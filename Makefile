COQ_MAKEFILE := rocq makefile

MISSING	 =									\
	find . \( \( -name foo \) -prune \)					\
	    -o \( -name '*.v'							\
		  -print \)						|	\
		xargs egrep -i -Hn '(admit|undefined|jww)'		|	\
		      egrep -v 'Definition undefined'			|	\
		      egrep -v '(old|new|research)/'

all: coq-cds4ltl
	-@$(MISSING) || exit 0

coq-cds4ltl: Makefile.coq $(wildcard src/*.v)
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	$(COQ_MAKEFILE) -f $< -o $@

clean: _CoqProject Makefile.coq
	$(MAKE) -f Makefile.coq clean

install: _CoqProject Makefile.coq
	$(MAKE) -f Makefile.coq install

fullclean: clean
	rm -f Makefile.coq Makefile.coq.conf .Makefile.d

# === Development Checks ===

lint:
	@echo "=== Checking for Admitted proofs (baseline: 0) ==="
	@ADMITTED=$$(grep -c 'Admitted\.' src/*.v 2>/dev/null \
		| awk -F: '{sum+=$$2} END{print sum}'); \
	echo "  Found: $$ADMITTED"; \
	if [ "$$ADMITTED" -gt 0 ]; then \
		echo "  ERROR: Admitted proofs found"; \
		exit 1; \
	fi
	@echo "=== Checking for admit/undefined/jww ==="
	-@$(MISSING) || exit 0

format-check:
	@FAIL=0; \
	echo "=== Checking for trailing whitespace ==="; \
	if grep -rn ' \+$$' src/*.v; then \
		echo "  ERROR: Trailing whitespace found"; \
		FAIL=1; \
	fi; \
	echo "=== Checking for tab characters ==="; \
	TAB=$$(printf '\t'); \
	if grep -rn "$$TAB" src/*.v; then \
		echo "  ERROR: Tab characters found (use spaces)"; \
		FAIL=1; \
	fi; \
	if [ "$$FAIL" -ne 0 ]; then exit 1; fi; \
	echo "  Passed."

format:
	@echo "=== Fixing whitespace ==="
	@perl -pi -e 's/[ \t]+$$//' src/*.v
	@echo "  Done."

timing: Makefile.coq
	$(MAKE) -f Makefile.coq TIMING=1

coqchk: all
	@echo "=== Running kernel verification ==="
	rocq check -R src CDS4LTL \
		CDS4LTL.MinBool CDS4LTL.Bool CDS4LTL.MinLTL CDS4LTL.LTL \
		CDS4LTL.Same_set CDS4LTL.Model CDS4LTL.Denote CDS4LTL.Step \
		CDS4LTL.EquationalReasoning CDS4LTL.Working

.PHONY: all clean install fullclean lint format-check format timing coqchk
