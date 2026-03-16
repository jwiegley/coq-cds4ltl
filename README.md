# A Calculational Deductive System for Linear Temporal Logic

I've been interested in temporal logic for a while now -- specifically,
whether you can formalize an entire textbook treatment of LTL using nothing
but equational reasoning. This project is the result: a complete Rocq
(formerly Coq) formalization of the axiom system from Warford, Vega, and
Staley's paper ["A Calculational Deductive System for Linear Temporal
Logic"](https://dl.acm.org/doi/10.1145/3387109) (ACM Computing Surveys,
Vol. 53, No. 3, June 2020).

The idea is straightforward: start from Huntington's three axioms for
Boolean algebra, add 10 temporal axioms for Next (&#x25EF;) and Until (U), and
derive everything else -- Eventually (&#x25C7;), Always (&#x25A1;), Wait (W), Release
(R), Strong Release (M) -- purely through equational rewriting. No induction
in the axiomatic layer. Over 240 theorems proven this way.

With many thanks to Professor Stan Warford and Dr. Scott Staley for
answering my questions and offering their support and encouragement.

## Building

You'll need Rocq 9.1. The easiest way to get set up:

```bash
nix develop    # drops you into a shell with all dependencies
make -j4       # builds everything
```

Or with OPAM:

```bash
opam install rocq-prover.9.1.0
make
```

## Project Structure

The source lives in `src/` and follows a strict module hierarchy -- each
layer builds only on the one above it:

```
MinBool.v    Huntington's 3 axioms (Boolean foundation)
    |
Bool.v       Adds conjunction as a derived operator
    |
MinLTL.v     10 temporal axioms (Next and Until)
    |
LTL.v        240+ derived theorems
```

Three semantic models validate the axioms:

- **Model.v** -- Soundness proofs over infinite streams
- **Denote.v** -- Homomorphic abstraction framework for proof reuse
- **Step.v** -- Computational model using Positive Normal Form reduction

Supporting files: `Same_set.v` (set theory utilities),
`EquationalReasoning.v` and `Working.v` (experimental equational reasoning).

## The Axioms

The temporal logic rests on 10 axioms plus 2 monotonicity declarations. I
spent some time verifying these are independent -- two axioms that were
originally in the basis (`next_not` and `until_left_and`) turned out to be
derivable from the others, so they got promoted to theorems. See
[README-axioms.md](README-axioms.md) for the full story.

The cool thing about this axiom set is that it's strong enough for purely
equational proofs of all 240+ theorems. No induction needed in the axiomatic
layer -- the one exception is theorem 170 in `Model.v`, where induction over
the semantic model establishes soundness.

## Current Status

All 240+ theorems are fully proven -- no `Admitted` proofs remain.

## Development

```bash
nix flake check       # run all checks (build, lint, whitespace)
make lint             # check for Admitted count regressions
make format-check     # whitespace hygiene (trailing spaces, tabs)
make format           # auto-fix whitespace issues
make timing           # build with per-sentence timing data
make coqchk           # kernel-level verification of compiled output
```

Pre-commit hooks via [Lefthook](https://github.com/evilmartians/lefthook)
run the build and all checks in parallel:

```bash
lefthook install      # set up hooks (one-time, from the dev shell)
```

## License

BSD-3-Clause. See [LICENSE.md](LICENSE.md).

## References

- Warford, Vega, and Staley. "A Calculational Deductive System for Linear
  Temporal Logic." *ACM Computing Surveys*, Vol. 53, No. 3, Article 59,
  June 2020.
- [README-axioms.md](README-axioms.md) -- documentation of the axiom set
  and independence analysis
