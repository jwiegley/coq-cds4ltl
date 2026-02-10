# CLAUDE.md — AI Assistant Context for coq-cds4ltl

## Project Overview

**Project:** coq-cds4ltl - A Calculational Deductive System for Linear Temporal Logic
**Language:** Coq 8.14-8.19
**Domain:** Formal verification of Linear Temporal Logic (LTL)
**Paper:** "A Calculational Deductive System for Linear Temporal Logic" - Warford, Vega, Staley (ACM Computing Surveys, Vol. 53, No. 3, June 2020)
**Repository:** https://github.com/jwiegley/coq-cds4ltl
**License:** BSD-3-Clause

### Project Goal
Formalize the axiomatization of Linear Temporal Logic using minimal axioms (Huntington's Boolean axioms + 9 temporal axioms) and prove 240+ theorems. The project provides three semantic models: axiomatic (abstract), denotational (infinite streams), and computational (Positive Normal Form reduction).

## Tech Stack & Dependencies

### Core Requirements
- **Coq:** 8.14-8.19 (default: 8.19)
- **OCaml:** Required for Coq compilation
- **Build System:** `coq_makefile` + GNU Make
- **Package Manager:** OPAM or Nix flakes

### Environment Setup

#### Using Nix (Recommended)
```bash
nix develop                  # Enter development shell with Coq 8.19
nix build                    # Build the project
nix flake check             # Run all checks
```

#### Using OPAM
```bash
opam switch create coq-cds4ltl 4.14.1
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.19.0
make
```

### Coq Standard Library Modules Used
```coq
Coq.Unicode.Utf8          (* Unicode notation *)
Coq.Program.Program       (* Program tactics *)
Coq.Classes.Morphisms     (* Proper instances *)
Coq.Setoids.Setoid       (* Setoid rewriting *)
Coq.Sets.Ensembles       (* Classical set theory *)
Coq.Sets.Classical_sets  (* Classical set operations *)
Coq.Sets.Powerset_facts  (* Powerset operations *)
Coq.Logic.Classical      (* Law of excluded middle *)
Coq.micromega.Lia        (* Linear arithmetic *)
Coq.Lists.List           (* List operations - used in Step.v *)
```

### No External Dependencies
The project is self-contained, using only Coq's standard library.

## Project Structure

```
src/
├── MinBool.v      # Minimal Boolean logic (348 lines, Huntington axioms)
├── Bool.v         # Extended Boolean logic (512 lines, adds AND operator)
├── MinLTL.v       # Minimal LTL (468 lines, Next + Until + 9 temporal axioms)
├── LTL.v          # Full LTL (2,803 lines, 240+ theorems with ◇, □, W, R, M)
├── Model.v        # Semantic soundness proofs (856 lines, infinite streams)
├── Same_set.v     # Set theory utilities (204 lines)
├── Denote.v       # Homomorphic abstraction framework (279 lines)
├── Step.v         # Computational model (651 lines, PNF reduction)
├── Bases.v        # Alternative Schneider axioms (54 lines, experimental)
└── Working.v      # Experimental equational reasoning (557 lines)

old/               # Deprecated modules (Syntax.v, CoSyntax.v, Machine.v)
_CoqProject        # Build configuration
README.org         # Main documentation
Makefile          # Build automation
flake.nix         # Nix reproducible builds
```

## Mathematical Foundation

### Module Hierarchy
```
MinimalBooleanLogic (3 axioms)
    ↓
BooleanLogic (+1 axiom: and_def)
    ↓
MinimalLinearTemporalLogic (+9 temporal axioms)
    ↓
LinearTemporalLogicW (+3 definitions: ◇, □, W)
    ↓
LinearTemporalLogic (+2 definitions: R, M)
```

### Core Operators
- **Boolean:** ¬ (not), ∨ (or), ∧ (and), ⇒ (implies), ≈ (equivalent), ⟹ (entails)
- **Temporal:** ◯ (next), U (until), ◇ (eventually), □ (always), W (wait), R (release), M (strong release)

### Key Axioms
1. **Huntington's Boolean axioms** (MinBool.v):
   - `or_comm`: p ∨ q ≈ q ∨ p
   - `or_assoc`: (p ∨ q) ∨ r ≈ p ∨ (q ∨ r)
   - `huntington`: ¬(¬p ∨ q) ∨ ¬(¬p ∨ ¬q) ≈ p

2. **9 temporal axioms** (MinLTL.v):
   - Axiom 1: `next_not` - ◯ ¬p ≈ ¬◯ p
   - Axiom 2: `next_impl` - ◯ (p ⇒ q) ≈ ◯ p ⇒ ◯ q
   - Axiom 9: `next_until` - ◯ (p U q) ≈ ◯ p U ◯ q
   - Axiom 10: `until_expand` - p U q ≈ q ∨ (p ∧ ◯ (p U q))
   - Axiom 11: `until_false` - p U ⊥ ⟹ ⊥
   - Axiom 12: `or_until_distr` - (p ∨ q) U r ⟹ (p U r) ∨ (q U r)
   - Axiom 14: `until_and_left` - (p ∧ q) U r ⟹ p U r
   - Axiom 17/18: Until distribution laws
   - Axiom 170: `not_until` - ¬(p U q) ≈ ¬q U (¬q ∧ ¬p)
   - Novel axiom: `looped` - ◯ ¬p U p ⟹ p (well-foundedness)

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
- Huntington's 3 axioms for Boolean logic
- Derives basic Boolean theorems
- Foundation for entire system

### Bool.v (512 lines)
- Adds AND operator with single axiom
- Proves De Morgan's laws, distributivity
- Defines `boolean` tactic

### MinLTL.v (468 lines)
- 9 temporal axioms
- Minimal temporal logic with Next and Until
- Core temporal theorems

### LTL.v (2,803 lines) - LARGEST FILE
- 240+ theorems organized by operator
- Derived operators (◇, □, W, R, M)
- Theorems 38-53: Eventually (◇) properties
- Theorems 54-90: Always (□) properties
- Theorems 91-130+: Wait (W) properties
- 14 Admitted proofs: R laws 260-265, M laws 266-269, OLD laws 270-273
- 1 Abort in Bool.v (`mccune` - documented research challenge)

### Model.v (856 lines)
- Semantic soundness proofs
- Infinite stream model
- Only file requiring induction (theorem 170)

### Denote.v (279 lines)
- Homomorphic abstraction
- Enables proof reuse across models
- Uses `defer` tactic

### Step.v (651 lines)
- Computational model
- Single-step reduction
- Positive Normal Form (PNF) encoding
- 12 Formula constructors: Top, Bottom, Examine, And, Or, Next, Until, Wait, Always, Eventually, Release, StrongRelease
- Error types: HitBottom, EndOfTrace, Rejected, Unsupported
- Enables model checking via `step` function

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
make fullclean          # Remove Makefile.coq as well
make -j4                 # Parallel build with 4 cores

# Development helpers
coqc src/MinBool.v      # Compile single file
coqchk CDS4LTL.MinBool  # Verify compiled module
grep -r "Abort"         # Find incomplete proofs (1 expected: mccune in Bool.v)
grep -r "Admitted"      # Find admitted proofs (14 expected in LTL.v)
```

### Testing & Validation
- **Type checking:** All proofs verified by Coq
- **Admitted detection:** Makefile checks for `admit`, `undefined`, `jww`
- **Completeness:** ~94% proven (14 Admitted out of 240+, concentrated in R/M/OLD sections)
- **CI Matrix:** Tests on Coq 8.14-8.19 plus dev version

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
- ✓ Minimal axiomatization
- ✓ 240+ theorems proven
- ✓ Semantic soundness
- ✓ Computational model

### In Progress
- 14 Admitted proofs in LTL.v:
  - Release (R) section: laws 260-265 (6 proofs)
  - Strong Release (M) section: laws 266-269 (4 proofs)
  - OLD section: laws 270-273 (4 proofs)
- 1 Abort in Bool.v (`mccune` - documented research challenge)
- Equational reasoning library integration (Working.v)
- Alternative Schneider axiomatization (Bases.v)

### Future Directions
1. Complete Release/StrongRelease proofs
2. Constructive foundation (remove Classical dependency)
3. Extract verified decision procedure
4. Bi-directional temporal flows
5. Integration with SPOT tool
6. Generate proof certificates

## Common Pitfalls & Solutions

### Pitfall: Rewriting fails with setoid relations
**Solution:** Ensure Proper instances are defined for all operators involved.

### Pitfall: Boolean normalization doesn't terminate
**Solution:** The `boolean` tactic may loop on certain expressions. Use manual rewrites.

### Pitfall: Proof script breaks after Coq upgrade
**Solution:** Check deprecation warnings, especially for `omega` → `lia` migration.

### Pitfall: Can't find the right theorem
**Solution:** Theorems are numbered. Check LTL.v comments for paper references.

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

(* Try automatic tactics in order *)
Proof. boolean. Qed.           (* Boolean simplification *)
Proof. now rewrite law_XX. Qed. (* Direct rewriting *)
Proof. intuition. Qed.          (* Intuitionistic reasoning *)

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
- **Coq Support:** 8.14-8.19
- **Last Major Update:** See git log for recent changes

---

*This CLAUDE.md was generated through deep analysis of the coq-cds4ltl project using Coq expertise and LTL formalization best practices. It serves as a comprehensive guide for AI assistants to understand and contribute to this formal verification project.*