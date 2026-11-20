/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CTadSign
public import QED.Frozen.Graded.RegulatedAmplitude

/-!
# (X₁) piece C: the amplitude of a tadpole changes sign under the reflection

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C4. For a tadpole side `T` (`TadSide`) and line momenta that
vanish on the lines crossing the boundary of `T`, reflecting the momenta of the lines ending in
`T` changes the sign of the amplitude (G₃) (`contractionAmplitude_reflMom`) and of the regulated
amplitude (G₄) (`regulatedAmplitude_reflMom`); see `QED/GradedProof/X1CTadSign.lean` for the
`γ⁵` argument.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X1C

open QED.Graded
open QED.WickModel (Params Contraction Line FermionLine PhotonLine)
open QED.TwoLoop.FurryIntegrable (sgn)
open QED.GradedProof.X0 (ZLine prod_sgn_closed prod_split_loopT isLoopT isLoopT_iff sgn_sq
  prod_ite_one_eq_subtype)

/-- The scalar algebra of the sign argument. -/
theorem sign_algebra {ind a a' b b' F F' Q Q' W E : ℂ} (hW : a' * W = -a) (hWE : W * E = 1)
    (hE : E * E = 1) (hF : F' = E * F) (hb : b' = b) (hQ : Q' = Q) :
    ind * (a' * b' * F' * Q') = -(ind * (a * b * F * Q)) := by
  have ha : a' = -a * E := by
    calc a' = a' * (W * E) := by rw [hWE, mul_one]
      _ = (a' * W) * E := by ring
      _ = -a * E := by rw [hW]
  rw [ha, hF, hb, hQ]
  linear_combination (-(ind * a * b * F * Q)) * hE

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction 1 nA κ}
  {T : Fin N → Prop} [DecidablePred T]

theorem prod_gl_sign (hT : TadSide C T) :
    ∏ s : {s : Wick.FermionVertex κ // T s.1},
      (if κ s.1.1 = .gauge ∨ κ s.1.1 = .gaugeCt then (-1 : ℂ) else 1) = -1 := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  exact hT.odd.neg_one_pow

open scoped Classical in
/-- **The amplitude of a tadpole changes sign** under the reflection of the momenta of the lines
ending in the tadpole side, when the lines crossing its boundary carry momentum `0`. -/
theorem contractionAmplitude_reflMom (hT : TadSide C T) {k : Line C → Fin 4 → ℝ}
    (hcross : ∀ l : Line C, ¬ (T l.ends.1 ↔ T l.ends.2) → k l = 0) (P : Params) {F : Type}
    (Φ : Lepton.Flavors F) (D : Counterterms F) (φ : Flavoring F κ) (g : Grading κ)
    (pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin nA → Fin 4) :
    contractionAmplitude P Φ D C φ g pIn kIn (reflMom T k) αOut βIn μ =
      -contractionAmplitude P Φ D C φ g pIn kIn k αOut βIn μ := by
  unfold contractionAmplitude
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun lor _ => ?_
  conv_lhs => rw [prod_split_loopT (Z := fun s : Wick.FermionVertex κ => T s.1)]
  conv_rhs => rw [prod_split_loopT (Z := fun s : Wick.FermionVertex κ => T s.1)]
  refine sign_algebra (W := ∏ s : {s : Wick.FermionVertex κ // T s.1}, sgn (α s.1) * sgn (β s.1))
    (E := ∏ f : ZLine C (fun s => T s.1), sgn (β f.1.1) * sgn (α f.1.tail)) ?_
    (prod_sgn_closed hT.closed α β) ?_ ?_ ?_ ?_
  · rw [← Finset.prod_mul_distrib, neg_eq_neg_one_mul, ← prod_gl_sign hT,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    by_cases hgl : κ s.1.1 = .gauge ∨ κ s.1.1 = .gaugeCt
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hgl), neg_one_mul]
      exact vertexFactor_gl_mul_sgn _ _ _ _ _ _ α β lor _ _ _ _ hgl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hgl), one_mul]
      have hf : κ s.1.1 = .fermionCt := by
        have h2 := s.1.2
        rcases hk : κ s.1.1 <;> simp_all
      exact vertexFactor_fct_mul_sgn _ _ _ _ _ _ α β lor _ _ _ _ hf
        (psiMomentum₂_reflMom_of_T hT pIn k s.2)
  · rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun f _ => ?_
    linear_combination (sgn (α f.1.tail) * sgn (α f.1.tail)) * sgn_sq (β f.1.1) +
      sgn_sq (α f.1.tail)
  · rw [← prod_ite_one_eq_subtype (fun f : FermionLine C => T f.1.1)
      (fun f => sgn (β f.1) * sgn (α f.tail)), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun f _ => ?_
    by_cases hf : T f.1.1
    · have hr : reflMom T k (.inl f) = -k (.inl f) := by simp [reflMom, Line.ends, hf]
      simp only [hr, electronPropagator_neg_apply, hf, ↓reduceIte]
      ring
    · have hr : reflMom T k (.inl f) = k (.inl f) := by simp [reflMom, Line.ends, hf]
      simp only [hr, hf, ↓reduceIte, one_mul]
  · refine Finset.prod_congr rfl fun t _ => ?_
    by_cases h : isLoopT (fun s : Wick.FermionVertex κ => T s.1) t = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h)]
      refine vertexFactor_congr_mom _ _ _ _ _ _ _ _ _ _ _ _ _ t (fun s hs => ?_) (fun a ha => ?_)
      · have hsT : ¬ T s.1 := fun hsT => h ((isLoopT_iff t).2 ⟨hs ▸ s.2, by subst hs; exact hsT⟩)
        exact psiMomentum₂_reflMom_of_not pIn k hsT
      · rw [photonMomentum₂_reflMom hT kIn k hcross a]
        split_ifs
        · exact .inr rfl
        · exact .inl rfl
  · refine Finset.prod_congr rfl fun g' _ => ?_
    rcases reflMom_eq_or_neg (T := T) k (.inr g') with h | h <;> rw [h]
    rw [photonPropagator_neg]

open scoped Classical in
/-- **The regulated amplitude of a tadpole changes sign** under the reflection. -/
theorem regulatedAmplitude_reflMom (hT : TadSide C T) {k : Line C → Fin 4 → ℝ}
    (hcross : ∀ l : Line C, ¬ (T l.ends.1 ↔ T l.ends.2) → k l = 0) (P : Params) {F : Type}
    [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (g : Grading κ)
    (pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin nA → Fin 4) :
    regulatedAmplitude P Φ D C g pIn kIn (reflMom T k) αOut βIn μ =
      -regulatedAmplitude P Φ D C g pIn kIn k αOut βIn μ := by
  unfold regulatedAmplitude
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [contractionAmplitude_reflMom hT hcross, mul_neg]

end QED.GradedProof.X1C

end
