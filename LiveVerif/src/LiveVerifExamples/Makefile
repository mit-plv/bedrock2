default_target: test

.PHONY: test clean

C_TESTS := $(wildcard *_test.c)
TEST_EXES := $(patsubst %.c,%.exe,$(C_TESTS))
TEST_OUTS := $(patsubst %.c,%.out,$(C_TESTS))

# do not rm these intermediate files in a chain
.PRECIOUS: %_exported.h %_test.exe

%_exported.h: prelude.h.snippet %.v
	cat prelude.h.snippet $*.v > $@

%_test.exe: %_test.c %_exported.h
	$(CC) -O2 $< -o $@

%_test.out: %_test.exe
	$(abspath $<) > $@

test: $(TEST_OUTS)

clean:
	rm -f *_exported.h *_test.exe *_test.out

critbit_exported.h: onesize_malloc_exported.h

tree_set_exported.h: onesize_malloc_exported.h
