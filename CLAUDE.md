# CLAUDE.md — AI Assistant Context for coq-cds4ltl

## Project Overview

**Project:** coq-cds4ltl - A Calculational Deductive System for Linear Temporal Logic
**Language:** Rocq 9.1
**Domain:** Formal verification of Linear Temporal Logic (LTL)
**Paper:** "A Calculational Deductive System for Linear Temporal Logic" - Warford, Vega, Staley (ACM Computing Surveys, Vol. 53, No. 3, June 2020)
**Repository:** https://github.com/jwiegley/coq-cds4ltl
**License:** BSD-3-Clause

### Project Goal
Formalize the axiomatization of Linear Temporal Logic using a small axiom set (Huntington's Boolean axioms + 10 temporal axioms; 8 from the CDS4LTL paper plus 2 project-specific axioms `looped` and `until_and_until`) and prove 240+ theorems. The project provides three semantic models: axiomatic (abstract), denotational (infinite streams via `Ensemble nat`), and computational (Positive Normal Form reduction).

All 240+ theorems are currently proven — there are zero `Admitted`, zero `Abort`, and zero `admit` in the codebase. This invariant is enforced by `make lint` and the Nix flake's `lint` check.

## Tech Stack & Dependencies

### Core Requirements
- **Rocq:** 9.1
- **OCaml:** Required for Coq compilation
- **Build System:** `rocq makefile` + GNU Make
- **Package Manager:** OPAM or Nix flakes

### Environment Setup

#### Using Nix (Recommended)
```bash
nix develop                  # Enter development shell with Rocq 9.1
nix build                    # Build the project
nix flake check             # Run all checks
```

#### Using OPAM
```bash
opam switch create coq-cds4ltl 4.14.1
opam install rocq-prover.9.1.0
make
```

### Rocq Standard Library Modules Used
```coq
Stdlib.Unicode.Utf8          (* Unicode notation *)
Stdlib.Program.Program       (* Program tactics *)
Stdlib.Classes.Morphisms     (* Proper instances *)
Stdlib.Setoids.Setoid       (* Setoid rewriting *)
Stdlib.Sets.Ensembles       (* Classical set theory — Model.v, Same_set.v *)
Stdlib.Sets.Classical_sets  (* Classical set operations — Model.v *)
Stdlib.Sets.Powerset_facts  (* Powerset operations — Model.v *)
Stdlib.Logic.Classical      (* Law of excluded middle — Model.v only *)
Stdlib.micromega.Lia        (* Linear arithmetic — Model.v, Step.v *)
Stdlib.Lists.List           (* List operations — Step.v *)
```

Classical reasoning is confined to `Model.v` (semantic soundness over `Ensemble nat` requires LEM). The axiomatic layer (`MinBool` → `Bool` → `MinLTL` → `LTL`) does not import `Classical`.

### No External Dependencies
The project is self-contained, using only Coq's standard library.

## Project Structure

```
src/
├── MinBool.v        # Minimal Boolean logic (348 lines, Huntington's 3 axioms + 3 supplementary)
├── Bool.v           # Extended Boolean logic (505 lines, adds AND with single axiom; defines `boolean` tactic)
├── MinLTL.v         # Minimal LTL (516 lines, Next + Until + 10 temporal axioms)
├── LTL.v            # Full LTL (2,858 lines, 240+ theorems with ◇, □, W, R, M)
├── Model.v          # Semantic soundness proofs (870 lines, predicates over `Ensemble nat`)
├── Same_set.v       # Set theory utilities (204 lines)
├── Denote.v         # Homomorphic abstraction framework (279 lines, 13 module-type axioms)
└── Step.v           # Computational model (708 lines, PNF reduction)

old/                  # Deprecated modules (Bases, Working, EquationalReasoning, Syntax, CoSyntax, Machine, CoStep, Ext)
_CoqProject           # Build configuration
README.org            # Main documentation
README.md             # GitHub-flavored project README
README-axioms.md      # In-depth rationale for the axiom set
Makefile              # Build automation; `make lint` enforces zero Admitted
flake.nix             # Nix reproducible builds with build/lint/whitespace/coqchk checks
lefthook.yml          # Pre-commit hooks
```

## Mathematical Foundation

### Module Hierarchy
```
MinimalBooleanLogic (3 Huntington axioms + 3 supplementary)
    ↓
BooleanLogic (+1 axiom: and_def)
    ↓
MinimalLinearTemporalLogic (+10 temporal axioms; 2 Proper monotonicity instances)
    ↓
LinearTemporalLogicW (+3 definitions: ◇, □, W as module-type axioms)
    ↓
LinearTemporalLogic (+2 definitions: R, M as module-type axioms)
```

The "+ N temporal axioms" includes the 8 paper axioms (`next_impl`, `next_until`, `until_expand`, `until_false`, `until_left_or`, `until_left_or_order`, `until_right_and_order`, `not_until`) plus 2 project-specific axioms (`looped`, `until_and_until`). Two former axioms (`next_not` = paper Axiom 1, `until_left_and` = paper Axiom 14) are now derived theorems. See `README-axioms.md` for the full rationale.

### Core Operators
- **Boolean:** ¬ (not), ∨ (or), ∧ (and), ⇒ (implies), ≈ (equivalent), ⟹ (entails)
- **Temporal:** ◯ (next), U (until), ◇ (eventually), □ (always), W (wait), R (release), M (strong release)

### Key Axioms
1. **Huntington's Boolean axioms** (MinBool.v):
   - `or_comm`: p ∨ q ≈ q ∨ p
   - `or_assoc`: (p ∨ q) ∨ r ≈ p ∨ (q ∨ r)
   - `huntington`: ¬(¬p ∨ q) ∨ ¬(¬p ∨ ¬q) ≈ p

2. **10 temporal axioms** (MinLTL.v) — 8 from the paper + 2 project-specific:
   - Axiom 2:   `next_impl`             - ◯ (p ⇒ q) ≈ ◯ p ⇒ ◯ q
   - Axiom 9:   `next_until`            - ◯ (p U q) ≈ ◯ p U ◯ q
   - Axiom 10:  `until_expand`          - p U q ≈ q ∨ (p ∧ ◯ (p U q))
   - Axiom 11:  `until_false`           - p U ⊥ ⟹ ⊥
   - Axiom 12:  `until_left_or`         - p U (q ∨ r) ≈ p U q ∨ p U r
   - Axiom 17:  `until_left_or_order`   - p U (q U r) ⟹ (p ∨ q) U r
   - Axiom 18:  `until_right_and_order` - p U (q ∧ r) ⟹ (p U q) U r
   - Axiom 170: `not_until`             - ⊤ U ¬p ∧ ¬(p U q) ≈ ¬q U (¬p ∧ ¬q)
   - NEW:       `looped`                - ◯ ¬p U p ⟹ p   (well-foundedness; load-bearing for `law_75_strong`)
   - NEW:       `until_and_until`       - (p U q) ∧ (r U s) ⟹ (p ∧ r) U ((q ∧ r) ∨ (p ∧ s) ∨ (q ∧ s))
   - Plus 2 monotonicity Proper instances: `next_respects_implies`, `until_respects_implies`

   Derived (formerly axioms): `next_not` (Axiom 1), `until_left_and` (Axiom 14).

3. **Boolean extension** (Bool.v):
   - `and_def`: p ∧ q ≈ ¬(¬p ∨ ¬q)

## Proof Strategies & Tactics

### Primary Proof Style: Equational Reasoning
```coq
(* Forward/backward chains of equivalences *)
Definition proof_example p : result :=
  backward
    expression1
  ≡⟨⟨ justification1 ⟩⟩
    expression2
  ≡⟨⟨ justification2 ⟩⟩
    expression3
  ∎ equivalent.
```

### Custom Tactics

#### `boolean` (Bool.v:238)
Automatic simplification of Boolean expressions. Applies 30+ normalization rules.
```coq
Proof. boolean. Qed.  (* Solves many simple Boolean proofs *)
```

#### `one_arg` / `two_arg` (MinBool.v:136)
Automatically prove Proper instances for morphisms.

#### Model.v tactics
- `matches`: Extract existential witnesses
- `as_if`: Solve arithmetic with lia
- `reduce`: Unfold set operations
- `just_math`: Combine extensionality with lia
- `inv`: Combined inversion and reduction
- `equality`: Combine intuition with congruence

#### `defer` (Denote.v:97)
Transfer proof obligations via homomorphisms.

### Common Proof Patterns
1. **Boolean normalization:** `boolean. reflexivity.`
2. **Rewrite chains:** Sequential `rewrite` applications
3. **Contrapositive:** For proving implications
4. **Structured proofs:** Using `assert` for complex theorems

## Key Files & Their Purposes

### MinBool.v (348 lines)
- Huntington's 3 axioms for Boolean logic + 3 supplementary axioms
- Derives basic Boolean theorems
- Foundation for entire system
- Defines `one_arg`/`two_arg` tactics for Proper-instance discharge

### Bool.v (510 lines)
- Adds AND operator with a single axiom (`p ∧ q ≈ ¬(¬p ∨ ¬q)`)
- Proves De Morgan's laws, distributivity, including `mccune` (the McCune-style single Boolean axiom — proven, not aborted)
- Defines the `boolean` tactic for automated normalization

### MinLTL.v (516 lines)
- 10 temporal axioms (8 from paper + `looped` + `until_and_until`)
- 2 monotonicity Proper instances (`next_respects_implies`, `until_respects_implies`)
- Minimal temporal logic with Next and Until
- Derives `next_not` (paper Axiom 1) and `until_left_and` (paper Axiom 14) as theorems

### LTL.v (2,859 lines) — LARGEST FILE
- 240+ theorems numbered positionally to match the CDS4LTL paper's equation list (`law_n` ≈ n-th paper equation)
- Derived operators (◇, □, W, R, M) introduced via module-type axioms (`evn_def`, `always_def`, `wait_def`, `release_def`, `strong_release_def`)
- Section structure:
  - 3.1 Next ◯, 3.2 Until U  (inherited from MinLTL Facts)
  - 3.3 Eventually ◇ (laws 38-53)
  - 3.4-3.6 Always □ (laws 54-90)
  - 3.7 Wait W (laws 169-254)
  - **Release R (laws 256-265): Coq-specific extension** — the paper at line 842 deliberately excludes R; defined in Coq via `release_def: p R q ≈ ¬(¬p U ¬q)` (Ben-Ari)
  - **Strong Release M (laws 266-269): Coq-specific extension** — M is never mentioned in the paper
  - OLD section (laws 270-273): 270/271/272 documented as removed with semantic counterexamples; 273 proven
- All proofs `Qed`. No induction (forbidden outside Model.v). No classical logic.

### Model.v (870 lines)
- Semantic soundness: instantiates every module type up through `LinearTemporalLogic`
- Predicates encoded as `Ensemble nat` (i.e. `nat -> Prop`); a "trace" is the indicator set of where a predicate holds
- Only file using induction — `not_until` (Axiom 170) is the sole axiom whose semantic proof needs induction
- Imports `Stdlib.Logic.Classical`; `Excluded_Middle`, `NNPP`, `not_and_or` are required for the soundness proofs

### Denote.v (279 lines)
- Homomorphic abstraction framework: connects an abstract `LinearTemporalLogic` module type to a concrete `Formula` data type
- Defines the `defer` tactic for transferring proof obligations
- Contains 13 module-type axioms describing the homomorphism

### Step.v (~705 lines)
- Computational model intended for OCaml extraction
- Self-contained: does not depend on `Model.v` or any other module
- Inductive `Formula` with 12 constructors: Top, Bottom, Examine, And, Or, Next, Until, Wait, Always, Eventually, Release, StrongRelease
- `step` reduces a Formula one trace position at a time; `run` consumes a finite list
- Failure constructors: HitBottom plus tree-wrappers (BothFailed/LeftFailed/RightFailed)
- Soundness vs. Model.v is currently NOT proven (open issue: connect `passes (run φ s)` to `ModelLTL` semantics)

## AI Assistant Guidelines

### When Working with Proofs

1. **Start simple:** Use `boolean` tactic first for Boolean proofs
2. **Check existing lemmas:** 240+ theorems available - search before proving
3. **Follow naming convention:** Theorems numbered to match paper (e.g., `(* 42 *) law_42`)
4. **Use setoid rewriting:** The project uses `≈` and `⟹` relations extensively
5. **Avoid induction:** Keep axiomatic proofs equational; use induction only in Model.v

### When Extending the Project

1. **Add to appropriate Facts module:** Each logic level has a corresponding Facts module
2. **Prove Proper instances:** Required for new operators to work with rewriting
3. **Follow module hierarchy:** Don't break abstraction barriers
4. **Document axiom numbers:** Reference the CDS4LTL paper
5. **Test in Model.v:** Ensure new theorems are sound in semantic model

### Common Tasks

#### Adding a New Theorem
```coq
Module LinearTemporalLogicFacts.
  (* Add after related theorems *)
  Theorem my_new_theorem p q : formula.
  Proof.
    (* Try: boolean. *)
    (* Or: rewrite existing_theorem. boolean. *)
    (* Or: apply contrapositive. ... *)
  Qed.
End LinearTemporalLogicFacts.
```

#### Proving Soundness
Add corresponding proof in Model.v using the infinite stream model.

#### Extracting to OCaml
```coq
Extraction Language OCaml.
Extraction "ltl.ml" step compile.
```

### Build Commands
```bash
make                      # Build all (generates Makefile.coq if needed)
make clean               # Clean build artifacts (.vo, .vok, .glob files)
make install             # Install to Coq library
make fullclean           # Remove Makefile.coq as well
make -j4                 # Parallel build with 4 cores
make lint                # Enforce zero Admitted/admit/undefined/jww
make format-check        # Verify no trailing whitespace or tabs
make coqchk              # Run kernel verification on all compiled modules

# Development helpers
coqc src/MinBool.v        # Compile single file
rocq check CDS4LTL.MinBool # Verify compiled module in the kernel
grep -r "Abort"           # Should return zero results
grep -r "Admitted"        # Should return zero results
```

### Testing & Validation
- **Type checking:** All proofs verified by Coq's kernel
- **Admitted detection:** Makefile + flake `lint` check enforce zero `Admitted`/`admit` usage
- **Completeness:** 100% proven (zero Admitted/Abort across all source files)
- **CI:** GitHub Actions runs `nix flake check` on Rocq 9.1; lefthook adds local pre-commit checks

## Performance & Optimization

### Proof Performance
- Use `boolean` tactic for fast Boolean simplification
- Avoid long rewrite chains when possible
- Leverage `now` combinator for immediate closure

### Build Performance
- Parallel builds supported (`-j` flag)
- Incremental compilation via `.vo` files
- Use Nix for reproducible builds

## Current Status & Future Work

### Completed
- ✓ Minimal axiomatization (10 temporal axioms; reduced from original 12 by deriving `next_not` and `until_left_and`)
- ✓ 240+ theorems proven (zero `Admitted`)
- ✓ Semantic soundness (all axioms verified in `Ensemble nat` model)
- ✓ Computational model (Formula data type with `step`/`run`/`compile`; OCaml extraction-ready)
- ✓ `mccune` theorem proven (formerly an open challenge)
- ✓ `EquationalReasoning.v` notation library (`≡⟨⟩` chains)
- ✓ CI with Nix flake checks (build, lint, whitespace, coqchk)

### Future Directions
1. **Connect `Step.v` to `Model.v` soundness.** Currently `passes (run φ s)` is verified internally but not against the stream semantics in `Model.v`. Add a `Module Step <: LinearTemporalLogic` instantiation or a denotation function with a soundness lemma.
2. **Constructive foundation.** Remove `Classical` dependency from `Model.v` (likely requires a different model — decidable predicates over a fixed alphabet).
3. **Extract verified decision procedure** to OCaml using `Extraction Language OCaml` and `Extraction "ltl.ml" step compile`.
4. Schneider axiomatization equivalence (`Bases.v`): prove a functor `SchneiderAxioms <-> LinearTemporalLogicW`.
5. Bi-directional temporal flows (past-time operators `P`, `S`).
6. Integration with SPOT or other LTL tooling.
7. Generate proof certificates.

## Common Pitfalls & Solutions

### Pitfall: Rewriting fails with setoid relations
**Solution:** Ensure Proper instances are defined for all operators involved.

### Pitfall: Boolean normalization doesn't terminate
**Solution:** The `boolean` tactic applies many rewrite rules in `repeat match` and may loop on adversarial inputs. Fall back to manual rewrites if it hangs.

### Pitfall: Proof script breaks after Coq upgrade
**Solution:** Check deprecation warnings. The project moved from `Coq.*` to `Stdlib.*` paths in Rocq 9.x.

### Pitfall: Can't find the right theorem
**Solution:** Theorems are numbered to match the CDS4LTL paper. Search for `(* N *)` comments in `LTL.v` and `MinLTL.v`. The paper's section 3 is the primary reference for theorem numbers.

### Pitfall: A proof relies on auto-generated `H`/`H0` hypothesis names
**Solution:** This is fragile. Use `pose proof X as Hname` and `assert (Hname : ...)` with explicit names. Several long proofs in `LTL.v` (`law_140-144`, `law_165`) and `Model.v` (`not_until`, `until_and_until`) still use auto-naming and are scheduled for hardening.

### Pitfall: An `assert` body is indented but unbraced
**Solution:** Wrap with `{ ... }`. A misplaced indent silently re-attaches the tactic to the outer goal.

## Instructions for AI Assistants

### DO:
- Use the `boolean` tactic liberally for Boolean simplifications
- Reference theorem numbers from the CDS4LTL paper
- Maintain the equational proof style when possible
- Test new theorems in Model.v for soundness
- Follow the module hierarchy strictly
- Use Unicode operators consistently (◯, ◇, □, ∧, ∨, ⟹, ≈)
- Check for existing theorems before proving new ones
- Add proper documentation with theorem numbers

### DON'T:
- Don't use induction in axiomatic proofs (only in Model.v)
- Don't break module abstraction barriers
- Don't add external dependencies without strong justification
- Don't modify axioms without understanding the full impact
- Don't ignore incomplete proofs - they need completion
- Don't use classical logic where constructive proofs are possible

### Quick Reference

#### Most Used Theorems
- `not_not`: Double negation elimination
- `or_comm`, `or_assoc`: Commutativity and associativity
- `until_expand`: Expansion of Until
- `evn_def`, `always_def`: Definitions of ◇ and □
- `law_88_strong`: Bridge between □ and U

#### Most Used Tactics
1. `boolean` - Boolean simplification
2. `rewrite` / `rewrite <-` - Directed rewriting
3. `reflexivity` - Trivial equivalence
4. `now` - Immediate solution
5. `apply` - Direct application

#### File Dependencies
```
MinBool → Bool → MinLTL → LTL
                    ↓
        Model ← Same_set
           ↓
         Step
```

## Common Development Workflows

### Proving a New Theorem
1. Identify the appropriate Facts module based on operators used
2. Check if a similar theorem exists using `grep` or searching LTL.v
3. Add theorem with paper reference number if applicable
4. Try `boolean` first for Boolean properties
5. Use setoid rewriting for equivalences
6. Test soundness in Model.v if modifying core logic

### Debugging Failed Proofs
```coq
(* Show current proof state *)
Show.

(* Try automatic tactics in order — for the axiomatic layer (MinBool/Bool/MinLTL/LTL): *)
Proof. boolean. Qed.            (* Boolean simplification *)
Proof. now rewrite law_XX. Qed. (* Direct rewriting *)

(* `intuition` and `firstorder` are NOT used in the axiomatic layer — they are reserved for Model.v. *)

(* For Model.v proofs *)
Proof. matches. as_if. reduce. just_math. Qed.
```

### Adding a New Operator
1. Define in appropriate module type (MinLTL or LTL)
2. Add Proper instance for setoid rewriting
3. Define semantic interpretation in Model.v
4. Add computational reduction in Step.v
5. Prove key properties in Facts module

## Contact & Resources

- **Repository:** https://github.com/jwiegley/coq-cds4ltl
- **Paper:** ACM Computing Surveys, Vol. 53, No. 3, Article 59 (June 2020)
- **Maintainer:** John Wiegley
- **Related Work:** Büchi Automata formalization (see PDF in repo)

## Version History

- **Current:** Active development (20+ recent commits)
- **Rocq Support:** 9.1
- **Last Major Update:** See git log for recent changes

---

*This CLAUDE.md was generated through deep analysis of the coq-cds4ltl project using Coq expertise and LTL formalization best practices. It serves as a comprehensive guide for AI assistants to understand and contribute to this formal verification project.*