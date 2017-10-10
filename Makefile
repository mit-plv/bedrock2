
# default_target: all

COQFLAGS= -Q ../bbv bbv  -Q ./src compiler  -Q ./lib lib

DEPFLAGS:=$(COQFLAGS)

COQC=$(COQBIN)coqc
COQTOP=$(COQBIN)coqtop
COQDEP=$(COQBIN)coqdep $(DEPFLAGS)
COQDOC=$(COQBIN)coqdoc

%.vo: %.v
	$(COQC) $(COQFLAGS) $*.v 

# all: Word.vo

clean:
	find . -type f \( -name '*.glob' -o -name '*.vo' -o -name '*.aux' \) -delete

