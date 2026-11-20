/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2SEClass
public import QED.GradedProof.SE2Decomp
public import QED.GradedProof.GEx2SE
public import QED.GradedProof.GEx2Affine
public import QED.GradedProof.V5ZeroSplit
public import QED.TwoLoop.LimitMirror

/-!
# The order-`e⁴` self-energy through the vertex's T1 parameter sets

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57), step
A8 (the flavour split). With `Q = vParams P Φ E f` (the level-`0` data of flavour `f`) and the
parameter sets and weights of the order-`5` vertex (`QED/GradedProof/V5ZeroSplit.lean`), at
every `ε > 0`, `selfEnergyPart_two_add_tree_eq_split`:

`Σ⁽⁴⁾ + seTree = (1/i) (seClassSum (zParams Q X) + ∑_g w_g seClassSum (gParams Q X g))`.

Per contraction (`contractionValue_zero_split`): without a closed loop the value does not read
the loop parameters and `∑_g w_g = 0`; with a closed loop the value is the weighted sum over
`auxT1 X g = gParams Q X g` (`QED/GradedProof/SE2Decomp.lean`), and `zParams` gives `0`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.WI2

open QED.Graded QED.GradedProof.SE2 QED.GradedProof.V5Zero.Split QED.Lepton.Proof.HM
open QED.WickModel (Params Contraction IsOnePI fermionSign loopCount lineMomentum₂)

section Fields

variable (P : Params) {F : Type} (Φ : Lepton.Flavors F) (E : Counterterms F) (f : F)

theorem auxT1_eq_gParams (X : ℝ) (g : F) :
    auxT1 P Φ E f X g = gParams (GEx2.vParams P Φ E f) { Φ with openLine := f } X g := rfl

theorem auxW_eq_weight (X : ℝ) (g : F) :
    auxW Φ f X g = weight (GEx2.vParams P Φ E f) { Φ with openLine := f } X g := rfl

end Fields

/-- With a closed loop, T1's value at `zParams` vanishes (its loop measure is `δ_m - δ_m`). -/
theorem contractionValue₂_zParams_of_hasLoop (Q : Params) (X : ℝ) {N : ℕ}
    {κ : Fin N → Wick.VertexKind} {C : Contraction 1 0 κ} (hS : IsSimple C) (hL : HasLoop C)
    (p : Fin 4 → ℝ) (α β : Fin 4) :
    QED.WickModel.contractionValue₂ (zParams Q X) C ![p] ![p] ![] ![α] ![β] ![] = 0 := by
  have h : ∀ ℓ : Fin (loopCount C) → Fin 4 → ℝ,
      QED.WickModel.regulatedAmplitude₂ (zParams Q X) C ![p] ![] (lineMomentum₂ C ![p] ![p] ![] ℓ)
        ![α] ![β] ![] = 0 * 0 := by
    intro ℓ
    rw [← regulatedAmplitude₂_t1F, regulatedAmplitude₂_of_hasLoop _ _ hS hL, Fin.sum_univ_three]
    simp [t1F, QED.WickModel.Params.loopCoeff, QED.WickModel.Params.mass, zParams]
  unfold QED.WickModel.contractionValue₂
  simp only [h, mul_zero]
  simpa using QED.TwoLoop.LimitMirror.jointEnergyFirstIntegral_const_mul (loopCount C) 0
    (fun _ => 0)

/-- Without a closed loop, T1's value does not read the loop parameters. -/
theorem contractionValue₂_eq_of_not_hasLoop {Q Q' : Params} (he : Q.e = Q'.e)
    (h₁ : Q.δ₁ = Q'.δ₁) (h₂ : Q.δ₂ = Q'.δ₂) (hm : Q.δm = Q'.δm) (h₃ : Q.δ₃ = Q'.δ₃)
    (hmm : Q.m = Q'.m) (hγ : Q.mγ = Q'.mγ) (hΛ : Q.Λ = Q'.Λ) (hε : Q.ε = Q'.ε) {N : ℕ}
    {κ : Fin N → Wick.VertexKind} {C : Contraction 1 0 κ} (hS : IsSimple C) (hL : ¬ HasLoop C)
    (p : Fin 4 → ℝ) (α β : Fin 4) :
    QED.WickModel.contractionValue₂ Q C ![p] ![p] ![] ![α] ![β] ![] =
      QED.WickModel.contractionValue₂ Q' C ![p] ![p] ![] ![α] ![β] ![] := by
  have h : ∀ ℓ : Fin (loopCount C) → Fin 4 → ℝ, QED.WickModel.regulatedAmplitude₂ Q C ![p] ![]
      (lineMomentum₂ C ![p] ![p] ![] ℓ) ![α] ![β] ![] =
      QED.WickModel.regulatedAmplitude₂ Q' C ![p] ![]
      (lineMomentum₂ C ![p] ![p] ![] ℓ) ![α] ![β] ![] := by
    intro ℓ
    rw [← regulatedAmplitude₂_t1F, ← regulatedAmplitude₂_t1F,
      regulatedAmplitude₂_of_not_hasLoop _ _ hS hL, regulatedAmplitude₂_of_not_hasLoop _ _ hS hL]
    obtain ⟨⟩ := Q
    obtain ⟨⟩ := Q'
    dsimp only at he h₁ h₂ hm h₃ hmm hγ hΛ hε
    subst he h₁ h₂ hm h₃ hmm hγ hΛ hε
    rfl
  unfold QED.WickModel.contractionValue₂
  simp only [h]

section Split

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (E : Counterterms F) (f : F)

/-- **The zero-grading value of an order-`4` 1PI contraction through `zParams`, `gParams`.** -/
theorem contractionValue_zero_split (hε : 0 < P.ε) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hpos : ∀ g, 0 < Φ.mass g) (hPV₁ : ∑ g, Φ.coeff g = 0)
    (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) {X : ℝ} (hlt : ∀ g, Φ.mass g < X) {N : ℕ}
    {κ : Fin N → Wick.VertexKind} (h4 : ∑ t, (κ t).order = 4) (C : Contraction 1 0 κ)
    (hC : IsOnePI C) (p : Fin 4 → ℝ) (α β : Fin 4) :
    contractionValue P { Φ with openLine := f } E C 0 ![p] ![p] ![] ![α] ![β] ![] =
      QED.WickModel.contractionValue₂ (zParams (GEx2.vParams P Φ E f) X) C ![p] ![p] ![] ![α]
          ![β] ![] +
        ∑ g, (weight (GEx2.vParams P Φ E f) { Φ with openLine := f } X g : ℂ) *
          QED.WickModel.contractionValue₂
            (gParams (GEx2.vParams P Φ E f) { Φ with openLine := f } X g) C ![p] ![p] ![] ![α]
            ![β] ![] := by
  have hS := isSimple_of_order_four h4 C hC
  have hCt := ctReaches_of_order_four h4 C hC
  have hCI := classInt_of_order_four classInt_repR classInt_repX classInt_repV classInt_repF
    classInt_repP0 classInt_repP1 classInt_repC1 classInt_repC2 h4 C hC
  by_cases hL : HasLoop C
  · rw [contractionValue₂_zParams_of_hasLoop _ _ hS hL, zero_add]
    unfold contractionValue
    rw [funext (integrand_loop_eq P Φ E f hPV₁ hPV₂ hS hCt hL hlt hpos p α β),
      jointEnergyFirstIntegral_sum Finset.univ _ _ fun g _ => hCI _
        (adm_auxT1 P Φ E f hε hmγ hΛ (hpos f) g (hpos g) (hlt g)) p α β]
    rfl
  · have hz : contractionValue P { Φ with openLine := f } E C 0 ![p] ![p] ![] ![α] ![β] ![] =
        QED.WickModel.contractionValue₂ (refT1 P Φ E f) C ![p] ![p] ![] ![α] ![β] ![] := by
      unfold contractionValue QED.WickModel.contractionValue₂
      congr 1
      funext ℓ
      have hz := regulatedAmplitude_zero_eq P (seParams₂ P Φ E f) { Φ with openLine := f } E C
        hCt rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => ⟨rfl, rfl, rfl⟩) (fun _ _ => rfl) ![p]
        ![] (lineMomentum₂ C ![p] ![p] ![] ℓ) ![α] ![β] ![]
      rw [hz, regulatedAmplitude₂_of_not_hasLoop _ _ hS hL]
      exact congrArg _ (regulatedAmplitude₂_refT1 P Φ E f hS _ _ _ _ _ _ hL).symm
    have hr : ∀ Q' : Params, Q'.e = P.e → Q'.δ₁ = P.e ^ 2 * E.d₁ f 0 →
        Q'.δ₂ = P.e ^ 2 * E.d₂ f 0 → Q'.δm = P.e ^ 2 * E.dm f 0 → Q'.δ₃ = P.e ^ 2 * E.d₃ 0 →
        Q'.m = Φ.mass f → Q'.mγ = P.mγ → Q'.Λ = P.Λ → Q'.ε = P.ε →
        QED.WickModel.contractionValue₂ Q' C ![p] ![p] ![] ![α] ![β] ![] =
          QED.WickModel.contractionValue₂ (refT1 P Φ E f) C ![p] ![p] ![] ![α] ![β] ![] :=
      fun Q' h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
        contractionValue₂_eq_of_not_hasLoop (Q' := refT1 P Φ E f) h1 h2 h3 h4 h5 h6 h7 h8 h9 hS hL
          p α β
    rw [hz, hr (zParams (GEx2.vParams P Φ E f) X) rfl rfl rfl rfl rfl rfl rfl rfl rfl]
    rw [Finset.sum_congr rfl fun g _ => by
      rw [hr (gParams (GEx2.vParams P Φ E f) { Φ with openLine := f } X g) rfl rfl rfl rfl rfl rfl
        rfl rfl rfl]]
    rw [← Finset.sum_mul, ← Complex.ofReal_sum,
      sum_weight (Φ := { Φ with openLine := f }) hPV₁ hPV₂]
    simp

/-- **The order-`4` self-energy through the vertex's T1 parameter sets** (`ε > 0`). -/
theorem selfEnergyPart_two_add_tree_eq_split (hε : 0 < P.ε) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hpos : ∀ g, 0 < Φ.mass g) (hPV₁ : ∑ g, Φ.coeff g = 0)
    (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) {X : ℝ} (hlt : ∀ g, Φ.mass g < X)
    (p : Fin 4 → ℝ) (α β : Fin 4) :
    selfEnergyPart P Φ E f 2 p α β + GEx2.seTree P Φ E f p α β =
      (1 / I) * (seClassSum (zParams (GEx2.vParams P Φ E f) X) p α β +
        ∑ g, (weight (GEx2.vParams P Φ E f) { Φ with openLine := f } X g : ℂ) *
          seClassSum (gParams (GEx2.vParams P Φ E f) { Φ with openLine := f } X g) p α β) := by
  classical
  have key : selfEnergyPart P Φ E f 2 p α β + GEx2.seTree P Φ E f p α β =
      (1 / I) * ∑ N ∈ Finset.range (4 + 1), (N.factorial : ℂ)⁻¹ *
        ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
            (fun κ => ∑ t, (κ t).order = 4),
          ∑ C ∈ (Finset.univ : Finset (Contraction 1 0 κ)).filter (fun C => IsOnePI C),
            ((fermionSign C : ℤ) : ℂ) *
              contractionValue P { Φ with openLine := f } E C 0 ![p] ![p] ![] ![α] ![β] ![] := by
    simp only [selfEnergyPart, Matrix.of_apply, onePIPart]
    rw [show 2 * 2 = 4 from rfl,
      QED.GradedProof.VP2.selectedPart_split P _ E 1 0 (fun C => IsOnePI C) 4,
      GEx2.seTreeSum_eq P Φ E f p α β, one_div, mul_add, ← mul_assoc,
      show (I⁻¹ * -I : ℂ) = -1 by rw [mul_neg, inv_mul_cancel₀ I_ne_zero]]
    ring
  have hT : ∀ S : Params, ∑ N ∈ Finset.range (4 + 1), (N.factorial : ℂ)⁻¹ *
        ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
            (fun κ => ∑ t, (κ t).order = 4),
          ∑ C ∈ (Finset.univ : Finset (Contraction 1 0 κ)).filter (fun C => IsOnePI C),
            ((fermionSign C : ℤ) : ℂ) *
              QED.WickModel.contractionValue₂ S C ![p] ![p] ![] ![α] ![β] ![] =
        seClassSum S p α β := fun S => sum_order_four_eq_seClassSum S p α β
  rw [key]
  simp only [← hT]
  congr 1
  rw [Finset.sum_congr rfl fun N _ => congrArg _ (Finset.sum_congr rfl fun κ hκ =>
    Finset.sum_congr rfl fun C hC => by
      rw [contractionValue_zero_split P Φ E f hε hmγ hΛ hpos hPV₁ hPV₂ hlt
        (Finset.mem_filter.1 hκ).2 C (Finset.mem_filter.1 hC).2])]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun g _ => ?_
  ring

end Split

end QED.GradedProof.WI2

end
