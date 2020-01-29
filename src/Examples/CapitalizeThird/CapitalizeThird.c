#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <string.h>

// Model code

struct String {
  int length;
  char* chars;
};

int capitalize_String (struct String *s) {
  int i;
  char x;

  // make a new string in which each character is capitalized
  // bad if the length of s.chars does not match s.length
  for (i = 0; i < s->length; i++) {
    x = toupper(s->chars[i]);
    s->chars[i] = x;
  }

  return 1;
}

int capitalize_3rd (struct String** in) {
  return capitalize_String(in[2]); // bad if input length < 3
}


// Test code

void print_String(struct String *s) {
  int i;
  
  for (i = 0; i < s->length; i++) {
    printf("%c", s->chars[i]);
  }
}

int main() {
  static const int N = 5;
  static char* names[5] = {"apple", "orange", "pear", "blueberry", "kiwi"};
  struct String *fruits[N];
  struct String *s;
  char *c;
  int len;
  int i;
  int j;

  for (i = 0; i < N; i++) {
    fruits[i] = (struct String *) malloc(sizeof(struct String));
    len = strlen(names[i]);
    fruits[i]->length = len;
    c = malloc(len * sizeof(char));
    for (j = 0; j < len; j++) {
      c[j] = names[i][j];
    } 
    fruits[i]->chars = c;
  }
  
  // print input
  for (i = 0; i < N; i++) {
    print_String(fruits[i]);
    printf("\n");
  }

  // capitalize
  capitalize_3rd(fruits);
  printf("---\n");

  // print output
  for (i = 0; i < N; i++) {
    print_String(fruits[i]);
    printf("\n");
  }

  // free
  for (i = 0; i < N; i++) {
    free(fruits[i]->chars);
    free(fruits[i]);
  }

  return 0;
}
