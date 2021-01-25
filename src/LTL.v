Require Import
  Coq.Classes.Morphisms
  MinLTL.

Module Type LinearTemporalLogic.

Declare Module MinLTL : MinimalLinearTemporalLogic.
Include MinLTL.

Parameter eventually : t -> t.
Parameter always : t -> t.
Parameter wait : t -> t -> t.
Parameter release : t -> t -> t.
Parameter strong_release : t -> t -> t.

Declare Instance eventually_respects_impl :
  Proper (impl ==> impl) eventually.
Declare Instance always_respects_impl :
  Proper (impl ==> impl) always.
Declare Instance wait_respects_impl :
  Proper (impl ==> impl ==> impl) wait.
Declare Instance release_respects_impl :
  Proper (impl ==> impl ==> impl) release.

Notation "◇ p"     := (eventually p) (at level 0, right associativity).
Notation "□ p"     := (always p)     (at level 0, right associativity).
Notation "p 'W' q" := (wait p q)     (at level 44, right associativity).

(*** 3.3 Eventually *)

Hypothesis (* 38 *) eventually_def : forall (φ : t), ◇ φ ≈ ⊤ U φ.

Set Nested Proofs Allowed.

Lemma (* 39 *) law (φ ψ : t) : (φ U ψ) ∧ ◇ ψ ≈ φ U ψ.
Lemma (* 40 *) law (φ ψ : t) : (φ U ψ) ∨ ◇ ψ ≈ ◇ ψ.
Lemma (* 41 *) law (φ ψ : t) : φ U ◇ ψ ≈ ◇ ψ.
Lemma (* 42 *) law (φ ψ : t) : φ U ψ ⟹ ◇ ψ.
Lemma (* 43 *) law : ◇ ⊤ ≈ ⊤.
Lemma (* 44 *) law : ◇ ⊥ ≈ ⊥.
Lemma (* 45 *) law (φ : t) : ◇ φ ≈ φ ∨ ◯◇ φ.
Lemma (* 46 *) law (φ : t) : φ ⟹ ◇ φ.
Lemma (* 47 *) law (φ : t) : ◯ φ ⟹ ◇ φ.
Lemma (* 48 *) law (φ : t) : φ ∨ ◇ φ ≈ ◇ φ.
Lemma (* 49 *) law (φ : t) : ◇ φ ∧ φ ≈ φ.
Lemma (* 50 *) law (φ : t) : ◇◇ φ ≈ ◇ φ.
Lemma (* 51 *) law (φ : t) : ◯◇ φ ≈ ◇◯ φ.
Lemma (* 52 *) law (φ ψ : t) : ◇ (φ ∨ ψ) ⟹ ◇ φ ∨ ◇ ψ.
Lemma (* 53 *) law (φ ψ : t) : ◇ (φ ∧ ψ) ⟹ ◇ φ ∧ ◇ ψ.

(*** 3.4 Always *)

Hypothesis (* 54 *) always_def : forall (φ : t), □ φ ≈ ¬◇¬ φ.
Hypothesis (* 55 *) always_until_and_ind : forall (φ ψ χ : t),
  □ (φ → (◯ φ ∧ ψ) ∨ χ) ⟹ φ → □ ψ ∨ (ψ U χ).
Hypothesis (* 56 *) always_until_or_ind : forall (φ ψ : t),
  □ (φ → ◯ (φ ∨ ψ)) ⟹ φ → □ φ ∨ (φ U ψ).

Lemma (* 57 *) law (φ : t) : □ (φ → ◯ φ) ⟹ φ → □ φ.
Lemma (* 58 *) law (φ : t) : □ (◯ φ → φ) ⟹ ◇ φ → φ.
Lemma (* 59 *) law (φ : t) : ◇ φ ≈ ¬□¬ φ.
Lemma (* 60 *) law (φ : t) : ¬□ φ ≈ ◇¬ φ.
Lemma (* 61 *) law (φ : t) : ¬◇ φ ≈ □¬ φ.
Lemma (* 62 *) law (φ : t) : ¬◇□ φ ≈ □◇¬ φ.
Lemma (* 63 *) law (φ : t) : ¬□◇ φ ≈ ◇□¬ φ.
Lemma (* 64 *) law : □ ⊤ ≈ ⊤.
Lemma (* 65 *) law : □ ⊥ ≈ ⊥.
Lemma (* 66 *) law (φ : t) : □ φ ≈ φ ∧ ◯□ φ.
Lemma (* 67 *) law (φ : t) : □ φ ≈ φ ∧ ◯ φ ∧ ◯□ φ.
Lemma (* 68 *) law (φ : t) : φ ∧ □ φ ≈ □ φ.
Lemma (* 69 *) law (φ : t) : □ φ ∨ φ ≈ φ.
Lemma (* 70 *) law (φ : t) : ◇ φ ∧ □ φ ≈ □ φ.
Lemma (* 71 *) law (φ : t) : □ φ ∨ ◇ φ ≈ ◇ φ.
Lemma (* 72 *) law (φ : t) : □□ φ ≈ □ φ.
Lemma (* 73 *) law (φ : t) : ◯□ φ ≈ □◯ φ.
Lemma (* 74 *) law (φ : t) : φ → □ φ ⟹ φ → ◯□ φ.
Lemma (* 75 *) law (φ : t) : φ ∧ ◇¬ φ ⟹ ◇ (φ ∧ ◯¬ φ).
Lemma (* 76 *) law (φ : t) : □ φ ⟹ φ.
Lemma (* 77 *) law (φ : t) : □ φ ⟹ ◇ φ.
Lemma (* 78 *) law (φ : t) : □ φ ⟹ ◯ φ.
Lemma (* 79 *) law (φ : t) : □ φ ⟹ ◯□ φ.
Lemma (* 80 *) law (φ : t) : □ φ ⟹ □◯ φ.
Lemma (* 81 *) law (φ ψ : t) : □ φ ⟹ ¬ (ψ U ¬ φ).

(*** 3.5 Temporal Deduction *)

Lemma (* 82 *) temporal_deduction (φ ψ : t) : (φ ≈ ⊤ -> ψ ≈ ⊤) -> □ φ ⟹ ψ.
Proof.
Admitted.

(*** 3.6 Always, Continued *)

Lemma (* 83 *) law (φ ψ χ : t) : □ φ ∧ (ψ U χ) ⟹ (φ ∧ ψ) U (φ ∧ χ).
Proof.
  apply and_impl_iff.
  apply temporal_deduction; intros.
  rewrite H.
  rewrite !true_and.
  rewrite or_comm.
  now apply true_def.
Qed.

(* Lemmas 84-135 (52) *)

(*** 3.7 Proof Metatheorems *)

(*
Lemma (* 136 *) metatheorem (ϕ : t) : ϕ is a theorem <-> □ ϕ is a theorem.
*)

Lemma (* 137 *) next_metatheorem (φ ψ : t) : φ ⟹ ψ -> ◯ φ ⟹ ◯ ψ.
Proof. now apply next_respects_impl. Qed.

Lemma (* 138 *) eventually_metatheorem (φ ψ : t) : φ ⟹ ψ -> ◇ φ ⟹ ◇ ψ.
Proof. now apply eventually_respects_impl. Qed.

Lemma (* 139 *) always_metatheorem (φ ψ : t) : φ ⟹ ψ -> □ φ ⟹ □ ψ.
Proof. now apply always_respects_impl. Qed.

(*** 3.8 Always, Continued *)

(* Lemmas 140-168 (28) *)

(*** 3.9 Wait *)

Hypothesis (* 169 *) wait_def : forall (φ ψ : t), φ W ψ ≈ □ φ ∨ (φ U ψ).
Hypothesis (* 170 *) wait_distr_not : forall (φ ψ : t), ¬(φ W ψ) ≈ ¬ ψ U (¬ φ ∧ ¬ ψ).

(* Lemmas 171-254 (84) *)

Lemma law_182 (φ : t) : φ W φ ≈ φ.
Lemma law_183 (φ ψ : t) : φ W ψ ≈ (φ U ψ) ∨ □ φ.
Lemma law_184 (φ ψ : t) : ¬(φ W ψ) ≈ ¬ ψ U (¬ φ ∧ ¬ ψ).
Lemma law_185 (φ ψ : t) : ¬(φ W ψ) ≈ (φ ∧ ¬ ψ) U (¬ φ ∧ ¬ ψ).
Lemma law_186 (φ ψ : t) : ¬(φ U ψ) ≈ ¬ ψ W (¬ φ ∧ ¬ ψ).
Lemma law_187 (φ ψ : t) : ¬(φ U ψ) ≈ (φ ∧ ¬ ψ) W (¬ φ ∧ ¬ ψ).
Lemma law_188 (φ ψ : t) : ¬(¬ φ U ¬ ψ) ≈ ψ W (φ ∧ ψ).
Lemma law_189 (φ ψ : t) : ¬(¬ φ U ¬ ψ) ≈ (¬ φ ∧ ψ) W (φ ∧ ψ).
Lemma law_190 (φ ψ : t) : ¬(¬ φ W ¬ ψ) ≈ ψ U (φ ∧ ψ).
Lemma law_191 (φ ψ : t) : ¬(¬ φ W ¬ ψ) ≈ (¬ φ ∧ ψ) U (φ ∧ ψ).
Lemma law_192 (φ ψ : t) : φ W ψ ≈ φ U (ψ ∨ □ φ).
Lemma law_193 (φ ψ : t) : φ W ψ ≈ (φ ∨ ψ) W ψ.
Lemma law_194 (φ ψ : t) : φ W ψ ≈ □ (φ ∧ ¬ ψ) ∨ (φ U ψ).
Lemma law_195 (φ ψ : t) : φ U ψ ≈ (φ W ψ) ∧ ◇ ψ.
Lemma law_196 (φ ψ : t) : φ U ψ ≈ (φ W ψ) ∧ ¬□¬ ψ.
Lemma law_197 (φ ψ : t) : φ U ψ ≈ ◇ ψ ∧ (φ W ψ).
Lemma law_198 (φ ψ : t) : φ W ψ ≈ ψ ∨ (φ ∧ ◯ (φ W ψ)).
Lemma law_199 (φ ψ : t) : φ W ψ ≈ (φ ∧ ¬ ψ) W ψ.
Lemma law_200 (φ ψ : t) : φ W (φ W ψ) ≈ φ W ψ.
Lemma law_201 (φ ψ : t) : (φ W ψ) W ψ ≈ φ W ψ.
Lemma law_202 (φ ψ : t) : φ W (φ U ψ) ≈ φ W ψ.
Lemma law_203 (φ ψ : t) : (φ U ψ) W ψ ≈ φ U ψ.
Lemma law_204 (φ ψ : t) : φ U (φ W ψ) ≈ φ W ψ.
Lemma law_205 (φ ψ : t) : (φ W ψ) U ψ ≈ φ U ψ.
Lemma law_206 (φ ψ : t) : ◯ (φ W ψ) ≈ ◯ φ W ◯ ψ.
Lemma law_207 (φ ψ : t) : φ W ◇ ψ ≈ □ φ ∨ ◇ ψ.
Lemma law_208 (φ : t) : ◇ φ W φ ≈ ◇ φ.
Lemma law_209 (φ ψ : t) : □ φ ∧ (φ W ψ) ≈ □ φ.
Lemma law_210 (φ ψ : t) : □ φ ∨ (φ W ψ) ≈ φ W ψ.
Lemma law_211 (φ : t) : φ W □ φ ≈ □ φ.
Lemma law_212 (φ : t) : □ φ ≈ φ W ⊥.
Lemma law_213 (φ : t) : ◇ φ ≈ ¬(¬ φ W ⊥).
Lemma law_214 (φ : t) : ⊤ W φ ≈ ⊤.
Lemma law_215 (φ : t) : φ W (⊤) ≈ ⊤.
Lemma law_216 (φ : t) : ⊥ W φ ≈ φ.
Lemma law_217 (φ ψ χ : t) : φ W (ψ ∨ χ) ≈ (φ W ψ) ∨ (φ W χ).
Lemma law_218 (φ ψ χ : t) : (φ ∧ ψ) W χ ≈ (φ W χ) ∧ (ψ W χ).
Lemma law_219 (φ ψ : t) : φ ∨ (φ W ψ) ≈ φ ∨ ψ.
Lemma law_220 (φ ψ : t) : (φ W ψ) ∨ ψ ≈ φ W ψ.
Lemma law_221 (φ ψ : t) : (φ W ψ) ∧ ψ ≈ ψ.
Lemma law_222 (φ ψ : t) : (φ W ψ) ∧ (φ ∨ ψ) ≈ φ W ψ.
Lemma law_223 (φ ψ : t) : (φ W ψ) ∨ (φ ∧ ψ) ≈ φ W ψ.
Lemma law_224 (φ ψ : t) : ((¬ φ U ψ) ∨ (¬ ψ U φ)) ≈ ◇ (φ ∨ ψ).
Lemma law_225 (φ ψ : t) : ψ ⟹ φ W ψ.
Lemma law_226 (φ ψ : t) : φ W φ ⟹ φ ∨ ψ.
Lemma law_227 (φ ψ : t) : φ W φ ⟹ □ φ ∨ ◇ ψ.
Lemma law_228 (φ : t) : ¬ φ W φ ≈ ⊤.
Lemma law_229 (φ ψ : t) : (φ → ψ) W φ ≈ ⊤.
Lemma law_230 (φ ψ : t) : (φ W ψ) ∨ (φ W ¬ ψ) ≈ ⊤.
Lemma law_231 (φ ψ χ : t) : (φ W (ψ ∧ χ)) ⟹ ((φ W ψ) ∧ (φ W χ)).
Lemma law_232 (φ ψ χ : t) : (φ W χ) ∨ (ψ W χ) ⟹ ((φ ∨ ψ) W χ).
Lemma law_233 (φ ψ : t) : φ U ψ ⟹ φ W ψ.
Lemma law_234 (φ ψ : t) : φ W □ ψ ⟹ □ (φ W ψ).
Lemma law_235 (φ ψ : t) : ¬ (φ U ψ) ⟹ ((φ ∧ ¬ ψ) W (¬ φ ∧ ¬ ψ)).
Lemma law_236 (φ ψ : t) : ¬ (φ W ψ) ⟹ ((φ ∧ ¬ ψ) U (¬ φ ∧ ¬ ψ)).
Lemma law_237 (φ ψ χ : t) : (φ → ψ) W χ ⟹ ((φ W χ) → (ψ W χ)).
Lemma law_238 (φ ψ : t) : □ φ ⟹ φ W ψ.
Lemma law_239 (φ ψ : t) : □ φ ⟹ (◯ ψ → ◯ (φ W ψ)).
Lemma law_240 (φ ψ : t) : □ φ ⟹ (◇ ψ → ◇ (φ W ψ)).
Lemma law_241 (φ ψ : t) : □ φ ⟹ (□ ψ → □ (φ W ψ)).
Lemma law_242 (φ ψ : t) : □ (φ ∨ ψ) ⟹ φ W ψ.
Lemma law_243 (φ ψ : t) : □ (¬ ψ → φ) ⟹ φ W ψ.
Lemma law_244 (φ ψ χ : t) : □ (φ → (◯ φ ∧ ψ) ∨ χ) ⟹ φ → ψ W χ.
Lemma law_245 (φ ψ : t) : □ (φ → ◯ (φ ∨ ψ)) ⟹ φ → φ W ψ.
Lemma law_246 (φ ψ : t) : □ (φ → ◯ φ) ⟹ φ → φ W ψ.
Lemma law_247 (φ ψ : t) : □ (φ → ψ ∧ ◯ φ) ⟹ φ → φ W ψ.
Lemma law_248 (φ ψ χ : t) : □ φ ∧ (ψ W χ) ⟹ ((φ ∧ ψ) W (φ ∧ χ)).
Lemma law_249 (φ ψ : t) : (φ W ψ) ∧ □¬ ψ ⟹ □ φ.
Lemma law_250 (φ ψ : t) : □ φ ⟹ ((φ U ψ) ∨ □¬ ψ).
Lemma law_251 (φ ψ : t) : ¬□ φ ∧ (φ W ψ) ⟹ ◇ ψ.
Lemma law_252 (φ ψ : t) : ◇ ψ ⟹ (¬□ φ ∨ (φ U ψ)).
Lemma law_253 (φ ψ χ : t) : □ (φ → ψ) ⟹ φ W χ → ψ W χ.
Lemma law_254 (φ ψ χ : t) : □ (φ → ψ) ⟹ χ W φ → χ W ψ.
Lemma law_255 (φ ψ χ ρ : t) : □ ((φ → χ) ∧ (ψ → ρ)) ⟹ ((φ W ψ) → (χ W ρ)).
Lemma law_256 (φ ψ χ ρ : t) : □ ((φ → ψ W χ) ∧ (χ → ψ W ρ)) ⟹ φ → ψ W ρ.
Lemma law_257 (φ ψ χ : t) : (φ U ψ) W χ ⟹ ((φ W ψ) W χ).
Lemma law_258 (φ ψ χ : t) : φ W (ψ U χ) ⟹ (φ W (ψ W χ)).
Lemma law_259 (φ ψ χ : t) : φ U (ψ U χ) ⟹ (φ U (ψ W χ)).
Lemma law_260 (φ ψ χ : t) : (φ U ψ) U χ ⟹ ((φ W ψ) U χ).
Lemma law_261 (φ ψ χ : t) : (φ U ψ) U χ ⟹ ((φ ∨ ψ) U χ).
Lemma law_262 (φ ψ χ : t) : (φ W ψ) W χ ⟹ ((φ ∨ ψ) W χ).
Lemma law_263 (φ ψ χ : t) : φ W (ψ W χ) ⟹ (φ W (ψ ∨ χ)).
Lemma law_264 (φ ψ χ : t) : φ W (ψ W χ) ⟹ ((φ ∨ ψ) W χ).
Lemma law_265 (φ ψ χ : t) : φ W (ψ ∧ χ) ⟹ ((φ W ψ) W χ).
Lemma law_266 (φ ψ : t) : (¬ φ W ψ) ∨ (¬ ψ W φ) ≈ ⊤.
Lemma law_267 (φ ψ χ : t) : (φ W ψ) ∧ (¬ ψ W χ) ⟹ φ W χ.
Lemma weakUntil_until_or (φ ψ : t) : φ W ψ ≈ φ U (ψ ∨ □ φ).
Lemma until_eventually_weakUntil (φ ψ : t) : φ U ψ ≈ ◇ ψ ∧ (φ W ψ).
Lemma expand_weakUntil  (φ ψ : t) : φ W ψ ≈ ψ ∨ (φ ∧ ◯ (φ W ψ)).

(*** Release *)

Notation "p 'R' q" := (release p q) (at level 45, right associativity).

Hypothesis release_def : forall (φ ψ : t), φ R ψ ≈ ¬ (¬ φ U ¬ ψ).

Lemma law_268 (φ ψ : t) : φ R ψ ≈ ¬(¬ φ U ¬ ψ).
Lemma law_269 (φ ψ : t) : φ U ψ ≈ ¬(¬ φ R ¬ ψ).
Lemma law_270 (φ ψ : t) : φ W ψ ≈ ψ R (ψ ∨ φ).
Lemma law_271 (φ ψ : t) : φ R ψ ≈ ψ W (ψ ∧ φ).
Lemma law_272 (φ ψ : t) : φ R ψ ≈ ψ ∧ (φ ∨ ◯ (φ R ψ)).
Lemma law_273 (φ ψ χ : t) : φ R (ψ ∨ χ) ≈ (φ R ψ) ∨ (φ R χ). (* ??? *)
Lemma law_274 (φ ψ χ : t) : (φ ∧ ψ) R χ ≈ (φ R χ) ∧ (ψ R χ). (* ??? *)
Lemma law_275 (φ ψ : t) : ◯ (φ R ψ) ≈ (◯ φ) R (◯ ψ).
Lemma law_276 (φ ψ : t) : □ ψ ≈ ⊥ R ψ.
Lemma not_until (φ ψ : t) : ¬ (φ U ψ) ≈ ¬φ R ¬ψ.
Lemma not_release (φ ψ : t) : ¬ (φ R ψ) ≈ (¬φ U ¬ψ).
Lemma always_release (ψ : t) : □ ψ ≈ ⊥ R ψ.
Lemma release_until (φ ψ : t) : φ R ψ ≈ ¬(¬φ U ¬ψ).
Lemma weakUntil_release_or (φ ψ : t) : φ W ψ ≈ ψ R (ψ ∨ φ).
Lemma release_weakUntil_and (φ ψ : t) : φ R ψ ≈ ψ W (ψ ∧ φ).
Lemma next_release (φ ψ : t) : ◯ (φ R ψ) ≈ (◯ φ) R (◯ ψ).
Lemma release_or (ρ φ ψ : t) : ρ R (φ ∨ ψ) ≈ (ρ R φ) ∨ (ρ R ψ).
Lemma and_release (ρ φ ψ : t) : (φ ∧ ψ) R ρ ≈ (φ R ρ) ∧ (ψ R ρ).
Lemma expand_release (φ ψ : t) : φ R ψ ≈ ψ ∧ (φ ∨ ◯ (φ R ψ)).

(*** Strong Release *)

Notation "p 'M' q" := (strong_release p q) (at level 45, right associativity).

Hypothesis strong_release_def : forall (φ ψ : t), φ M ψ ≈ (φ R ψ) ∧ ◇ φ.

Lemma law_277 (φ ψ : t) : φ M ψ ≈ (φ R ψ) ∧ ◇ φ.
Lemma law_278 (φ ψ : t) : φ M ψ ≈ φ R (ψ ∧ ◇ φ).
Lemma law_279 (φ ψ : t) : ¬(φ W ψ) ≈ (¬ φ M ¬ ψ).
Lemma law_280 (φ ψ : t) : ¬(φ M ψ) ≈ (¬ φ W ¬ ψ).
Lemma not_weakUntil (φ ψ : t) : ¬ (φ W ψ) ≈ (¬φ M ¬ψ).
Lemma not_strongRelease (φ ψ : t) : ¬ (φ M ψ) ≈ (¬φ W ¬ψ).
Lemma strongRelease_not_weakUntil (φ ψ : t) : φ M ψ ≈ ¬(¬φ W ¬ψ).
Lemma strongRelease_and_release (φ ψ : t) : φ M ψ ≈ (φ R ψ) ∧ ◇ φ.
Lemma strongRelease_release_and (φ ψ : t) : φ M ψ ≈ φ R (ψ ∧ ◇ φ).

(*** OLD *)

Notation "p ≉ q" := (~ (p ≈ q)) (at level 90, no associativity).

Lemma law_34 (φ : t) : ◇□ φ ⟹ □◇ φ.
Lemma law_35 (φ : t) : □¬ φ ⟹ ¬□ φ.
Lemma law_43 (φ : t) : ◇□◇ φ ≈ □◇ φ.
Lemma law_44 (φ : t) : □◇□ φ ≈ ◇□ φ.
Lemma law_45 (φ : t) : □◇□◇ φ ≈ □◇ φ.
Lemma law_46 (φ : t) : ◇□◇□ φ ≈ ◇□ φ.
Lemma law_47 (φ : t) : ◯□◇ φ ≈ □◇ φ.
Lemma law_48 (φ : t) : ◯◇□ φ ≈ ◇□ φ.
Lemma law_53 (φ ψ : t) : □ (φ ∧ ψ) ≈ □ φ ∧ □ ψ.
Lemma law_54 (φ ψ : t) : □ (φ ∨ ψ) ≉ □ φ ∨ □ ψ.
Lemma law_57 (φ ψ : t) : ◇ (φ ∧ ψ) ≉ ◇ φ ∧ ◇ ψ.
Lemma law_58 (φ ψ : t) : ◇ (φ ∨ ψ) ≈ ◇ φ ∨ ◇ ψ.
Lemma law_63 (φ ψ : t) : ◇□ (φ ∧ ψ) ≈ ◇□ φ ∧ ◇□ ψ.
Lemma law_64 (φ ψ : t) : □◇ (φ ∨ ψ) ≈ □◇ φ ∨ □◇ ψ.
Lemma law_65 (φ ψ : t) : ◇□ (φ → □ ψ) ≈ ◇□¬ φ ∧ ◇□ ψ.
Lemma law_66 (φ ψ : t) : □ (□◇ φ → ◇ ψ) ≈ ◇□¬ φ ∧ □◇ ψ.
Lemma law_67 (φ ψ : t) : □ ((φ ∨ □ ψ) ∧ (□ φ ∨ ψ)) ≈ □ φ ∨ □ ψ.
Lemma law_70 (φ : t) : ◇ φ ∧ □¬ φ ≈ ⊥.
Lemma law_71 (φ : t) : □ φ ∧ ◇¬ φ ≈ ⊥.
Lemma law_72 (φ : t) : □ φ ∧ □¬ φ ≈ ⊥.
Lemma law_73 (φ : t) : □◇ φ ∧ ◇□¬ φ ≈ ⊥.
Lemma law_74 (φ : t) : ◇□ φ ∧ □◇¬ φ ≈ ⊥.
Lemma law_75 (φ : t) : ◇□ φ ∧ ◇□¬ φ ≈ ⊥.
Lemma law_76 (φ : t) : ◇ φ ∨ □¬ φ ≈ ⊤.
Lemma law_77 (φ : t) : □ φ ∨ ◇¬ φ ≈ ⊤.
Lemma law_78 (φ : t) : ◇ φ ∨ ◇¬ φ ≈ ⊤.
Lemma law_79 (φ : t) : □◇ φ ∨ ◇□¬ φ ≈ ⊤.
Lemma law_80 (φ : t) : □◇ φ ∨ □◇¬ φ ≈ ⊤.
Lemma law_81 (φ : t) : ◇□ φ ∨ □◇¬ φ ≈ ⊤.
Lemma law_82 (φ ψ : t) : ◇ (φ → ψ) ⟹ □ φ → ◇ ψ.
Lemma law_85 (φ ψ : t) : □ (φ → ψ) ⟹ □ φ → □ ψ.
Lemma law_86 (φ ψ : t) : □ φ ∨ □ ψ ⟹ □ (φ ∨ ψ).
Lemma law_87 (φ ψ : t) : □ φ ∧ ◇ ψ ⟹ ◇ (φ ∧ ψ).
Lemma law_88 (φ ψ : t) : ◇ φ → ◇ ψ ⟹ ◇ (φ → ψ).
Lemma law_90 (φ ψ : t) : □◇ (φ ∧ ψ) ⟹ □◇ φ ∧ □◇ ψ.
Lemma law_91 (φ ψ : t) : □◇ (φ ∨ ψ) ⟹ □◇ φ ∨ □◇ ψ.
Lemma law_92 (φ ψ : t) : ◇□ (φ ∧ ψ) ⟹ ◇□ φ ∧ ◇□ ψ.
Lemma law_93 (φ ψ : t) : ◇□ φ ∨ ◇□ ψ ⟹ ◇□ (φ ∨ ψ).
Lemma law_94 (φ ψ : t) : ◇□ φ ∧ □◇ ψ ⟹ □◇ (φ ∧ ψ).
Lemma law_95 (φ ψ : t) : ◇□ φ ∧ □ (□ φ → ◇ ψ) ⟹ ◇ ψ.
Lemma law_96 (φ ψ : t) : □ (φ → ψ) ⟹ ◯ φ → ◯ ψ.
Lemma law_97 (φ ψ : t) : □ (φ → ψ) ⟹ ◇ φ → ◇ ψ.
Lemma law_98 (φ ψ : t) : □ (φ → ψ) ⟹ □◇ φ → □◇ ψ.
Lemma law_99 (φ ψ : t) : □ (φ → ψ) ⟹ ◇□ φ → ◇□ ψ.
Lemma law_100 (φ ψ : t) : □ φ ⟹ ◯ ψ → ◯ (φ ∧ ψ).
Lemma law_101 (φ ψ : t) : □ φ ⟹ ◇ ψ → ◇ (φ ∧ ψ).
Lemma law_102 (φ ψ : t) : □ φ ⟹ □ ψ → □ (φ ∧ ψ).
Lemma law_103 (φ ψ : t) : □ φ ⟹ ◯ ψ → ◯ (φ ∨ ψ).
Lemma law_104 (φ ψ : t) : □ φ ⟹ ◇ ψ → ◇ (φ ∨ ψ).
Lemma law_105 (φ ψ : t) : □ φ ⟹ □ ψ → □ (φ ∨ ψ).
Lemma law_106 (φ ψ : t) : □ φ ⟹ ◯ ψ → ◯ (φ → ψ).
Lemma law_107 (φ ψ : t) : □ φ ⟹ ◇ ψ → ◇ (φ → ψ).
Lemma law_108 (φ ψ : t) : □ φ ⟹ □ ψ → □ (φ → ψ).
Lemma law_109 (φ ψ : t) : □ (□ φ → ψ) ⟹ □ φ → □ ψ.
Lemma law_110 (φ ψ : t) : □ (φ → ◇ψ) ⟹ ◇ φ → ◇ ψ.
Lemma law_112 (φ ψ : t) : □ (φ → ◯ ψ) ⟹ φ → ◇ ψ.
Lemma law_113 (φ : t) : □ (φ → ◯¬ φ) ⟹ φ → ¬□ φ.
Lemma law_115 (φ ψ : t) : □ (φ ∨ ◯ ψ → ψ) ⟹ ◇ φ → ψ.
Lemma law_116 (φ ψ : t) : □ (φ → ◯ φ ∧ ψ) ⟹ φ → □ ψ.
Lemma law_117 (φ ψ χ : t) : □ (φ → (◯ φ ∧ ψ) ∨ χ) ⟹ φ → □ ψ ∨ (ψ U χ).
Lemma law_118 (φ ψ : t) : □ (φ → ◯ (φ ∨ ψ)) ⟹ φ → □ φ ∨ (φ U ψ).
Lemma law_119 (φ ψ χ ρ : t) : □ ((φ → ψ) ∧ (ψ → ◯ χ) ∧ (χ → ρ)) ⟹ φ → ◯ ρ.
Lemma law_120 (φ ψ χ ρ : t) : □ ((φ → ψ) ∧ (ψ → ◇ χ) ∧ (χ → ρ)) ⟹ φ → ◇ ρ.
Lemma law_121 (φ ψ χ ρ : t) : □ ((φ → ψ) ∧ (ψ → □ χ) ∧ (χ → ρ)) ⟹ φ → □ ρ.
Lemma law_122 (φ ψ χ : t) : □ ((φ → ◇ ψ) ∧ (ψ → ◇ χ)) ⟹ φ → ◇ χ.
Lemma law_123 (φ ψ χ : t) : □ ((φ → □ ψ) ∧ (ψ → □ χ)) ⟹ φ → □ χ.
Lemma law_124 (φ ψ χ : t) : (□ (□ φ → ◇ ψ) ∧ (ψ → ◯ χ)) ⟹ □ φ → ◯□◇ χ.
Lemma law_125 (φ ψ : t) : □ (φ ∨ ψ) ≈ ⊤ -> exists u, □ ((φ ∧ u) ∨ (ψ ∧ ¬ u)) ≈ ⊤.
Lemma law_126 (φ ψ χ ρ : t) : □ ((φ → ◇ (ψ ∨ χ)) ∧ (ψ → ◇ ρ) ∧ (χ → ◇ ρ)) ⟹ φ → ◇ ρ.
Lemma law_127 (φ ψ : t) : □ (□ φ → ψ) ∨ □ (□ ψ → φ) ≈ ⊤.
Lemma law_128 (φ : t) : φ U ⊥ ≈ ⊥.
Lemma law_132 (φ : t) : ¬ φ U φ ≈ ◇ φ.
Lemma law_136 (φ ψ : t) : (φ U ψ) ∨ (φ U ¬ ψ) ≈ ⊤.
Lemma law_145 (φ ψ : t) : φ U ψ ≈ (φ ∨ ψ) U ψ.
Lemma law_146 (φ ψ : t) : φ U ψ ≈ (φ ∧ ¬ ψ) U ψ.
Lemma law_148 (φ ψ χ : t) : (φ U χ) ∨ (ψ U χ) ⟹ (φ ∨ ψ) U χ.
Lemma law_150 (φ ψ χ : t) : φ U (ψ ∧ χ) ⟹ (φ U ψ) ∧ (φ U χ).
Lemma law_151 (φ ψ χ : t) : φ U (ψ ∧ χ) ⟹ φ U (ψ U χ).
Lemma law_152 (φ ψ χ : t) : (φ ∧ ψ) U χ ⟹ (φ U ψ) U χ.
Lemma law_153 (φ ψ χ : t) : (φ ∧ ψ) U χ ⟹ φ U (ψ U χ).
Lemma law_155 (φ ψ : t) : ◇ (φ U ψ) ≉ (◇ φ) U (◇ ψ).
Lemma law_160 (φ : t) : φ U □ φ ≈ □ φ.
Lemma law_161 (φ ψ : t) : φ U □ ψ ≈ □ (φ U ψ).
Lemma law_162 (φ ψ : t) : ◇ φ ⟹ ((φ → ψ) U φ).
Lemma law_170 (φ ψ : t) : □ φ ⟹ ◯ ψ → ◯ (φ U ψ).
Lemma law_171 (φ ψ : t) : □ φ ⟹ ◇ ψ → ◇ (φ U ψ).
Lemma law_172 (φ ψ : t) : □ φ ⟹ □ ψ → □ (φ U ψ).
Lemma law_174 (φ ψ : t) : □ φ ⟹ ◇ ψ → φ U ψ.
Lemma law_176 (φ ψ χ : t) : □ (φ → ψ) ⟹ (χ U φ) → (χ U ψ).
Lemma law_177 (φ ψ χ : t) : □ (φ → ψ) ⟹ (φ U χ) → (ψ U χ).
Lemma law_179 (φ ψ χ ρ : t) : □ ((φ → ψ U χ) ∧ (χ → ψ U ρ)) ⟹ φ → □ χ.
Lemma law_180 (φ ψ χ ρ : t) : □ ((φ → χ) ∧ (ψ → ρ)) ⟹ φ U ψ → χ U ρ.
Lemma law_181 (φ ψ χ : t) : □ (φ → ¬ ψ ∧ ◯ χ) ⟹ φ → ¬ (ψ U χ).
Lemma eventually_always_until (φ ψ : t) : ◇ ψ ⟹ □ φ → φ U ψ.

(* Definition examine {a : Type} (P : a -> t) : t := fun s => P (head s) s. *)

End LinearTemporalLogic.
