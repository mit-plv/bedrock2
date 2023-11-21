default_target: test

.PHONY: test clean

C_TESTS := $(wildcard test32/*_test.c test64/*_test.c)
TEST_EXES := $(patsubst %.c,%.exe,$(C_TESTS))
TEST_OUTS := $(patsubst %.c,%.out,$(C_TESTS))

# do not rm these intermediate files in a chain
.PRECIOUS: %_exported.h %_test.exe

test32/%_exported.h test64/%_exported.h: prelude.h.snippet %.v
	cat prelude.h.snippet $*.v > $@

# not passing -m32 flag because we don't want to depend on multilib
test32/%_test.exe: test32/%_test.c test32/%_exported.h
	$(CC) -O2 -fsyntax-only $< > $@

test64/%_test.exe: test64/%_test.c test64/%_exported.h
	$(CC) -O2 $< -o $@

test32/%_test.out: test32/%_test.exe
	echo "Not currently running 32-bit programs" > $@

test64/%_test.out: test64/%_test.exe
	$(abspath $<) > $@

test: $(TEST_OUTS)

clean:
	rm -f test32/*_exported.h test32/*_test.exe test32/*_test.out
	rm -f test64/*_exported.h test64/*_test.exe test64/*_test.out

test32/critbit_exported.h: test32/onesize_malloc_exported.h

test32/tree_set_exported.h: test32/onesize_malloc_exported.h
