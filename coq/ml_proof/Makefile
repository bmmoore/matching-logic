all :
distclean : clean
	rm coq_makefile.mk

.PHONY : all distclean

coq_makefile.mk :
	coq_makefile -f _CoqProject -o $@

include coq_makefile.mk
