#include <stdio.h>
#include <stdbool.h>
#include <stddef.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <memory.h>
#include <netdb.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>

#define UNUSED(x) __attribute__((unused)) x

#define min(a, b) \
  ({ __typeof__ (a) _a = (a); \
      __typeof__ (b) _b = (b); \
    _a < _b ? _a : _b; })

typedef struct {
  size_t sz;
  char* data;
} buffer;

void*
noop_init() {
  return NULL;
}

void
echo_step(UNUSED(void* state), buffer input, buffer* output) {
  memcpy(output->data, input.data, min(input.sz, output->sz));
}

void
palindrome_step(UNUSED(void* state), buffer input, buffer* output) {
  size_t maxpos = min(input.sz, output->sz);
  for (size_t pos = 0; pos < maxpos; pos++) {
    output->data[pos] = input.data[input.sz - pos - 1];
  }
}

typedef struct {
  uint32_t key;
  uint32_t value;
} kv;

typedef struct {
  uint64_t size;
  uint64_t capacity;
  kv data[];
} kvstore;

#define MEM_SIZE 4096
char mem[MEM_SIZE];

void* kvstore_init() {
  explicit_bzero(mem, sizeof(mem));
  kvstore* store = (kvstore*)mem;
  store->size = 0;
  store->capacity = (sizeof(mem)
                     - sizeof(typeof(store->size))
                     - sizeof(typeof(store->capacity)))
    / sizeof(kv);
  return (void*)store;
}

/* bool */
/* starts_with(char* input, size_t input_sz, char* key) { */
/*   unsigned long len = strlen(key); */
/*   return (len <= input_sz) && (memcmp(input, key, len) == 0); */
/* } */

typedef char kvstore_pkt_op[3];

typedef struct {
  kvstore_pkt_op op;
  unsigned: 4;
  uint32_t key;
  unsigned: 4;
  uint32_t value;
} __attribute__((packed)) kvstore_put_pkt;

typedef struct {
  kvstore_pkt_op op;
  unsigned: 4;
  uint32_t key;
} __attribute__((packed)) kvstore_get_pkt;

typedef union {
  kvstore_pkt_op op;
  kvstore_get_pkt mget;
  kvstore_put_pkt mput;
} __attribute__((packed)) kvstore_pkt;

#define OK "OK "
#define ERR "ERR "
#define INPUT_TOO_SHORT "input too short"
#define UNRECOGNIZED_OPERATION "unrecognized operation"
#define NOT_FOUND "not found"
#define STORE_FULL "store full"
/* #define OUTPUT_TOO_LONG "output too long" */

void
writeout(buffer* output, const char* header,
         const char* data, size_t data_len) {
  size_t header_len = strlen(header);
  size_t len = data_len + header_len;
  if (output->sz >= len + 1) {
    memcpy(output->data, header, header_len);
    memcpy(output->data + header_len, data, data_len);
    output->data[len] = '\n';
    output->sz = len + 1;
  }
}

void
err(buffer* output, const char* msg) {
  writeout(output, ERR, msg, strlen(msg));
}

void
ok(buffer* output, const char* data, size_t data_len) {
  /* fprintf(stderr, "ok(_,%.*s, %lu)\n", (int)data_len, data, data_len); */
  writeout(output, OK, data, data_len);
}

#define OP_GET "GET"
#define OP_PUT "PUT"

void
kvstore_step(void* state, buffer input, buffer* output) {
    kvstore* store = (kvstore*)state;
    if (input.sz < sizeof(kvstore_pkt_op)) {
      err(output, INPUT_TOO_SHORT);
    } else {
      kvstore_pkt* pkt = (kvstore_pkt*)input.data;
      if (memcmp(pkt->op, OP_GET, sizeof(pkt->op)) == 0) {
        if (input.sz < sizeof(kvstore_get_pkt)) {
          err(output, INPUT_TOO_SHORT);
        } else {
          kvstore_get_pkt* msg = &pkt->mget;
          size_t pos = 0;
          for (; pos < store->size; pos++) {
            size_t off = store->size - pos - 1;
            if (store->data[off].key == msg->key) {
              ok(output,
                 (const char*)&store->data[off].value,
                 sizeof(typeof(store->data[off].value)));
              pos = store->size;
            }
          }
          if (pos == store->size) {
            err(output, NOT_FOUND);
          }
        }
      } else if (memcmp(pkt->op, OP_PUT, sizeof(pkt->op)) == 0) {
        if (input.sz < sizeof(kvstore_put_pkt)) {
          err(output, INPUT_TOO_SHORT);
        } else {
          kvstore_put_pkt* msg = &pkt->mput;
          if (store->size < store->capacity) {
            store->data[store->size].key = msg->key;
            store->data[store->size].value = msg->value;
            store->size++;
            uint32_t out = 0;
            ok(output, (const char*)&out, sizeof(uint32_t));
          } else {
            err(output, STORE_FULL);
          }
        }
      } else {
        err(output, UNRECOGNIZED_OPERATION);
      }
    }
}

typedef void (*step_fn)(void* state, buffer input, buffer* output);
typedef void* (*init_fn)();

typedef struct {
  init_fn init;
  step_fn step;
} driver;

driver echo_driver = { .init = &noop_init, .step = &echo_step };
driver palindrome_driver = { .init = &noop_init, .step = &palindrome_step };
driver kvstore_driver = { .init = &kvstore_init, .step = &kvstore_step };

void
fail(char* msg) {
  perror(msg);
  exit(1);
}

#define DRIVER kvstore_driver

int
main(int argc, char** argv) {
  if (argc != 2) {
    fprintf(stderr, "Usage: %s <port>\n", argv[0]);
    exit(1);
  }

  uint16_t listen_port = atoi(argv[1]);

  int listen_fd = socket(AF_INET, SOCK_STREAM, 0);
  if (listen_fd < 0)
    fail("socket() failed");

  int optval = 1; // Allow immediate rebinding
  setsockopt(listen_fd, SOL_SOCKET, SO_REUSEADDR,
             (const void *)&optval, sizeof(typeof(optval)));

  struct sockaddr_in listen_addr; /* server's addr */
  bzero((char*) &listen_addr, sizeof(listen_addr));

  listen_addr.sin_family = AF_INET;
  listen_addr.sin_addr.s_addr = htonl(INADDR_ANY);
  listen_addr.sin_port = htons(listen_port);

  if (bind(listen_fd, (struct sockaddr *) &listen_addr,
           sizeof(listen_addr)) < 0)
    fail("bind() failed");

  const int queue_size = 10;
  if (listen(listen_fd, queue_size) < 0)
    fail("listen() failed");

  void* state = DRIVER.init();

  while (true) {
    struct sockaddr_in client_addr;
    socklen_t client_len = sizeof(client_addr);
    int client_fd = accept(listen_fd, (struct sockaddr *)&client_addr,
                           &client_len);
    if (client_fd < 0)
      fail("accept() failed");

    char* client_addr_str = inet_ntoa(client_addr.sin_addr);
    if (client_addr_str == NULL)
      fail("inet_ntoa() failed");
    fprintf(stderr, "Connected to %s\n", client_addr_str);

#define BUFFER_SIZE 2048
    char input[BUFFER_SIZE];
    char output[BUFFER_SIZE];

    int nr = read(client_fd, input, BUFFER_SIZE);
    if (nr < 0)
      fail("read() failed");
    fprintf(stderr, "<< %.*s", nr, input);

    buffer bin = { .sz = nr, .data = input };
    buffer bout = { .sz = BUFFER_SIZE, .data = output };
    DRIVER.step(state, bin, &bout);

    /* fprintf(stderr, ">> %.*s", (int)bout.sz, bout.data); */
    int nw = write(client_fd, bout.data, bout.sz);
    if (nw < 0)
      fail("write() failed");

    close(client_fd);
  }
}
