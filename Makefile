COQ_MAKEFILE := $(shell command -v coq_makefile 2>/dev/null || echo "rocq makefile")

MISSING	 =									\
	find . \( \( -name foo \) -prune \)					\
	    -o \( -name '*.v'							\
		  -print \)						|	\
		xargs egrep -i -Hn '(admit|undefined|jww)'		|	\
		      egrep -v 'Definition undefined'			|	\
		      egrep -v '(old|new|research)/'

all: coq-cds4ltl
	-@$(MISSING) || exit 0

coq-cds4ltl: Makefile.coq $(wildcard *.v)
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	$(COQ_MAKEFILE) -f $< -o $@

clean: _CoqProject Makefile.coq
	$(MAKE) -f Makefile.coq clean

install: _CoqProject Makefile.coq
	$(MAKE) -f Makefile.coq install

fullclean: clean
	rm -f Makefile.coq Makefile.coq.conf .Makefile.d
