# On the Axioms of MinimalLinearTemporalLogic

When I first set out to formalize the CDS4LTL paper in Coq, I wanted an axiom
set that was small enough to trust but expressive enough to prove 240+ theorems
without ever reaching for induction over the naturals. The standard approach to
LTL -- expansion plus an induction rule -- doesn't lend itself to equational
reasoning. So the axiom set here takes a different path: it trades the
induction rule for a handful of consequences that, together, recover enough of
its power for purely equational proofs.

What follows is a description of each axiom, why it's there, and what would
break if you took it away.

## The Boolean Foundation

Before the temporal axioms, the system rests on Huntington's three axioms for
Boolean algebra (commutativity, associativity, and the Huntington axiom), plus
a single axiom defining conjunction: `p ∧ q ≈ ¬(¬p ∨ ¬q)`. All of classical
propositional logic follows from these four. This is well-trodden ground and
I won't dwell on it here -- see `MinBool.v` and `Bool.v` for the development.

The temporal axioms build on this Boolean base. They introduce two new
operators -- Next (`◯`) and Until (`U`) -- and ten axioms that govern their
behavior.

## The Proper Instances

Two declarations aren't axioms in the traditional sense, but they carry real
axiomatic content:

**Monotonicity of Next.** `next_respects_implies` says that if `p ⟹ q`, then
`◯ p ⟹ ◯ q`. Next preserves entailment. This is the modal-logic principle
that Next is a *normal* operator -- it doesn't invert the logical order.
Without it, you can't rewrite under `◯` at all, and virtually every proof in
the development breaks.

**Monotonicity of Until.** `until_respects_implies` says that `U` is monotone
in both arguments: stronger hypotheses give stronger conclusions. This is
what lets you weaken sub-expressions inside `U` terms during equational
reasoning. It also turns out to be strong enough on its own to derive what was
previously Axiom 14 (the left distributivity of `U` over `∧`), since
projecting each conjunct is just monotonicity applied to `and_proj`.

## The Next Axioms

There are two axioms governing `◯`:

### Axiom 2: `next_impl` -- `◯ (p ⇒ q) ≈ ◯ p ⇒ ◯ q`

Next distributes over implication. Since `p ⇒ q` is just notation for `¬p ∨
q`, this really says that `◯` distributes over `∨` in a specific way.
Combined with monotonicity, it gives you distribution of `◯` over every
Boolean connective. In fact, it's strong enough to derive what was originally
Axiom 1 (the self-duality of Next, `◯ ¬p ≈ ¬◯ p`): instantiate `q` with `⊥`,
use the Until axioms to show `◯ ⊥ ≈ ⊥`, and simplify.

This axiom makes `◯` a *homomorphism* on the Boolean algebra. Without it, you
can't push `◯` through any propositional structure, and the connection between
"what's true now" and "what's true next" becomes opaque.

### Axiom 9: `next_until` -- `◯ (p U q) ≈ ◯ p U ◯ q`

Next distributes over Until. This is genuinely independent of Axiom 2 -- it
can't be derived from distributing `◯` over the Boolean connectives alone.
The expansion axiom (below) characterizes `p U q` as a fixpoint involving `◯`,
but it doesn't determine how `◯` interacts with `U` as a *whole*. You can
construct models where `◯` distributes over `∧` and `∨` perfectly well but
fails to commute with `U`.

What this axiom really says is that `◯` is a *temporal* homomorphism, not just
a Boolean one. It respects the structure of waiting.

## The Until Axioms

The remaining eight axioms define the behavior of `U`. They split naturally
into three groups: the fixpoint characterization, the distributive laws, and
the composition laws.

### The Fixpoint Group

These three axioms characterize what `U` *means*:

**Axiom 10: `until_expand` -- `p U q ≈ q ∨ (p ∧ ◯ (p U q))`**

This is the expansion law, and it's the most-used axiom in the entire
development. It says: "p until q" means either `q` holds right now, or `p`
holds right now and "p until q" holds starting from the next moment. This is
the defining equation of Until -- it characterizes `p U q` as a fixpoint of
`f(X) = q ∨ (p ∧ ◯ X)`.

But a fixpoint equation alone is dangerously weak. The equation `X = q ∨ (p ∧
◯ X)` has many solutions. In particular, the constant `⊤` satisfies it
whenever `□ p` holds. The expansion axiom tells you `p U q` is *a* fixpoint;
it doesn't tell you it's the *least* one. That's what the next axiom is for.

**Axiom 11: `until_false` -- `p U ⊥ ⟹ ⊥`**

Nothing can hold until falsehood. This looks almost trivially obvious, but
it carries surprising weight. From the expansion axiom alone, `p U ⊥ ≈ p ∧
◯ (p U ⊥)` -- the formula just says "p holds now and the same thing holds at
the next step," which is perfectly consistent with `p U ⊥` being `□ p` (or
even `⊤`). Axiom 11 rules this out. It forces `p U q` to be the *least*
fixpoint of the expansion equation, which is the essential semantic property
of Until: the eventuality `q` must actually *arrive*.

Together with expansion and Axiom 2, these two axioms are enough to derive
`◯ ⊥ ≈ ⊥` and from that the self-duality of Next (`◯ ¬p ≈ ¬◯ p`), which was
originally its own axiom.

**Axiom `looped` -- `◯ ¬p U p ⟹ p`**

This one isn't from the CDS4LTL paper. It says: if `¬p` holds at the next
step until `p` arrives, then `p` must already hold now. Think of it
contrapositively: if `p` doesn't hold now, then `¬p` holds at step 1, and the
formula `◯ ¬p U p` is asking for `p` to eventually arrive -- but the only way
it can arrive is if it held all along, contradicting our assumption.

Why do we need this? It's a *well-foundedness* principle. Where `until_false`
prevents waiting forever for something that never comes, `looped` prevents a
more subtle pathology: a circular temporal structure where time loops back on
itself. In the infinite-stream model this can't happen (time marches forward),
but the equational axioms don't know about streams. Without `looped`, you
can't prove `law_75_strong` (the characterization of "the last moment before
a change"), which drives the crucial always-induction principle (`law_55`).

It's used in only two proofs in the entire development, but those two proofs
are load-bearing walls.

### The Distributive Group

**Axiom 12: `until_left_or` -- `p U (q ∨ r) ≈ (p U q) ∨ (p U r)`**

Until distributes over disjunction in its right argument (the "eventuality"
argument). The reverse direction -- `(p U q) ∨ (p U r) ⟹ p U (q ∨ r)` -- is
trivially derivable from monotonicity (if `q ⟹ q ∨ r` then `p U q ⟹ p U (q
∨ r)`). But the forward direction is genuinely new: it says that waiting for
"q or r" is the same as waiting for q *or* waiting for r. This can't be
derived without it -- the expansion axiom only unfolds one step at a time and
can't distinguish which disjunct will eventually be satisfied.

**Axiom `until_and_until` -- `(p U q) ∧ (r U s) ⟹ (p ∧ r) U ((q ∧ r) ∨ (p ∧ s) ∨ (q ∧ s))`**

This is the other axiom not from the paper. When two Until formulas hold
simultaneously, you can combine them: before either eventuality arrives, both
invariants `p` and `r` hold; when one or both eventualities arrive, the
disjunction on the right captures the three possible cases (q arrives first,
s arrives first, or both arrive together).

Semantically, this is about *comparing two witness times*. If `p U q` is
witnessed at time `m` and `r U s` at time `n`, then the combined formula holds
with witness `min(m, n)`. This kind of inter-temporal reasoning simply isn't
available from the other axioms, which all deal with a single Until expression
at a time.

This axiom is what makes `always_and_until` (law 83: `□ p ∧ q U r ⟹ (p ∧ q)
U (p ∧ r)`) provable, which in turn is the engine behind the frame laws --
the ability to carry an invariant through a temporal argument.

### The Composition Group

**Axiom 17: `until_left_or_order` -- `p U (q U r) ⟹ (p ∨ q) U r`**

If you're waiting for "q until r" to happen, and you hold `p` in the
meantime, then throughout the entire period either `p` or `q` holds, and
eventually `r` arrives. This flattens a nested Until into a single one. In
the standard LTL axiomatization with induction, this is a theorem; without
induction, it must be assumed. The proof would require reasoning about two
different witness times (the outer and inner Until), which is exactly the kind
of thing equational reasoning can't synthesize on its own.

**Axiom 18: `until_right_and_order` -- `p U (q ∧ r) ⟹ (p U q) U r`**

If you're waiting for `q ∧ r`, then in particular you're waiting for `q`
(that gives `p U q` at the witness time), and `r` also holds at that time, so
`(p U q) U r` holds. Like Axiom 17, this is about the compositional structure
of nested waiting, and in the standard system it follows from induction.

These two axioms are used sparingly -- five times total across the whole
development -- but they're the only way to manipulate nested Until expressions,
which arise naturally when reasoning about Eventually (`◇`) and Always (`□`).

### The Negation Axiom

**Axiom 170: `not_until` -- `⊤ U ¬p ∧ ¬(p U q) ≈ ¬q U (¬p ∧ ¬q)`**

This is the most complex axiom, and the only one whose semantic proof in
`Model.v` requires induction over the naturals (all other axiom proofs are
purely structural). It characterizes the negation of an Until formula: `p U
q` fails to hold precisely when `¬q` persists until a point where both `¬p`
and `¬q` hold.

This axiom is what connects the "positive" temporal operators (Until,
Eventually) with their "negative" counterparts. Without it, you can't prove
`law_88_strong` (the bridge between Always and Until: `□ p ∧ ◇ q ⟹ p U (p ∧
q)`), which is arguably the most important single theorem in the development
-- it's what makes Always useful for reasoning about Until expressions, and
vice versa.

## What Was Removed

Two statements that were originally axioms turned out to be derivable:

**Former Axiom 1 (`next_not`): `◯ ¬p ≈ ¬◯ p`.** Derivable from Axiom 2
(`next_impl`) together with Axioms 10 and 11 (`until_expand` and
`until_false`). The trick is to first derive `◯ ⊥ ≈ ⊥` from the Until
axioms, then instantiate Axiom 2 with `q := ⊥` and simplify.

**Former Axiom 14 (`until_left_and`): `p U (q ∧ r) ⟹ (p U q) ∧ (p U r)`.**
Derivable from the monotonicity of Until (`until_respects_implies`) plus
Boolean logic. Since `q ∧ r ⟹ q` and `q ∧ r ⟹ r`, monotonicity gives
`p U (q ∧ r) ⟹ p U q` and `p U (q ∧ r) ⟹ p U r` independently, and
combining them via `and_idem` yields the conjunction.

Both remain available as theorems in `MinimalLinearTemporalLogicFacts` under
their original names, so no downstream code needed to change.

## What Remains Irreducible

The ten remaining axioms (plus two Proper instances) appear to be genuinely
independent. Here's the intuition for why each one can't be derived from the
others:

| Axiom | Why it's independent |
|-------|---------------------|
| `next_respects_implies` | Required to bootstrap `next_not` derivation; can't be derived without circular dependency |
| `until_respects_implies` | First-argument monotonicity of `U` requires reasoning about Until's internal structure that no other axiom provides |
| `next_impl` (2) | Sole source of `◯` distribution over propositional connectives |
| `next_until` (9) | Links `◯` to `U`; expansion is circular without it |
| `until_expand` (10) | The defining fixpoint equation; everything else builds on it |
| `until_false` (11) | Forces least-fixpoint semantics; independent from expansion |
| `looped` | Well-foundedness; a different kind of grounding than `until_false` |
| `until_left_or` (12) | Forward direction not derivable from monotonicity |
| `until_and_until` | Inter-temporal comparison of two witness times |
| `until_left_or_order` (17) | Nested Until flattening; requires witness-time reasoning |
| `until_right_and_order` (18) | Nested Until composition; same |
| `not_until` (170) | Negation of Until; the only axiom needing induction in its semantic proof |

I haven't proven formal independence results (that would require constructing
separating models for each axiom), but the semantic proofs in `Model.v`
suggest these are genuinely distinct: each axiom's proof uses a different
structural argument about infinite streams and witness times. The fact that
`not_until` is the *only* axiom requiring induction in its semantic proof is
particularly telling -- it carries fundamentally different information than
the rest.

## The Design Choice

A standard LTL axiomatization needs only three or four axioms: expansion,
induction, and the Next distribution laws. This system has ten. That's a
deliberate trade: by including more axioms (all of them semantically valid),
we avoid the induction rule entirely and can reason about temporal logic in a
purely equational style. The proofs read like algebraic calculations rather
than case analyses over trace positions.

The cost is a larger trusted base. The benefit is that 240+ theorems about
Eventually, Always, Wait, Release, and Strong Release can all be proved by
rewriting chains -- the same style of reasoning used in the CDS4LTL paper
itself.
