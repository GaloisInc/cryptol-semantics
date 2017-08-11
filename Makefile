COQPROJECT_EXISTS=$(wildcard _CoqProject)

ifeq "$(COQPROJECT_EXISTS)" ""
$(error "Run ./configure before running make")
endif

default: Makefile.coq
	$(MAKE) -f Makefile.coq

test : Makefile.coq.test
	$(MAKE) -f Makefile.coq.test

verif : test

HMAC : test

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	$(MAKE) -f Makefile.coq.test clean
	rm Makefile.coq
	rm Makefile.coq.test

.PHONY: default clean
