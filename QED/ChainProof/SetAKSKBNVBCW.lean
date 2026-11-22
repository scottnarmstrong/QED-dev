/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKBNCW

/-!
# Set (a), stage B3: hierarchical Cheng–Wu variables for a one-loop vertex insertion

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage B3 (the nested
form). For a function `F` on `ℝ⁵` homogeneous of degree `-5`, with an outer pair of lines
(positions `0, 3`) and an inner triple (positions `1, 2, 4`, the inner vertex), the Cheng–Wu
theorem with the inner triple on the simplex reads
`∫_{Δ₄} F = ∫_{Δ₂} Ψ`, `Ψ(q) = ∫_{(0,∞)²} F(v₀, q₀, q₁, v₁, q₂) dv`. It follows from the Cheng–Wu
theorem for `F` (coordinates `1, 4` on the simplex), Fubini, and the Cheng–Wu theorem backwards
for `Ψ`, which is homogeneous of degree `-3`. If at a normalized inner point the integrand is
`w(q) G_q(v, τ(q))` with `G_q` homogeneous of degree `-3`, the outer orthant integral is the
outer simplex integral with the weight `τ⁻¹` (`ksN_integral_pos_snoc`,
`ksN_integral_pos_snoc_one`); the identification holds almost everywhere in the Cheng–Wu
variables, and is moved to the simplex through the Cheng–Wu theorem for the homogeneous
difference:

* `ksN_ksNIns_scale`: `Ψ(t q) = t⁻³ Ψ(q)` (and the sections are integrable together);
* `ksN_nest3_point`: `Ψ(q) = σ⁻³ R(q/σ)` at every point with an integrable section, `σ = Σq`;
* **`ksN_nest3`**: `∫_{Δ₄} F = ∫_{Δ₂} (w/τ)(q) ∫_{Δ₂} G_q dq`, the outer function integrable.
-/

@[expose] public section

open MeasureTheory Set

namespace QED.ChainProof.SetAKS

open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet)
open QED.Integration.ChengWu
open QED.Integration.TwoLoop (sum_simplexPoint)

/-- The five-line point with the outer pair `v` on the lines `0, 3` and the inner triple `q` on
the lines `1, 2, 4`. -/
def ksNIns (q : Fin 3 → ℝ) (v : Fin 2 → ℝ) : Fin 5 → ℝ := ![v 0, q 0, q 1, v 1, q 2]

theorem ksN_ksNIns_smul {t : ℝ} (ht : t ≠ 0) (q : Fin 3 → ℝ) (v : Fin 2 → ℝ) :
    ksNIns (t • q) v = t • ksNIns q (t⁻¹ • v) := by
  funext i
  fin_cases i <;> simp [ksNIns, mul_inv_cancel_left₀ ht]

theorem ksN_ksNIns_pos {q : Fin 3 → ℝ} (hq : ∀ i, 0 < q i) {v : Fin 2 → ℝ} (hv : v ∈ ksNPos 2) :
    ∀ i, 0 < ksNIns q v i := fun i => by
  fin_cases i
  · exact hv 0
  · exact hq 0
  · exact hq 1
  · exact hv 1
  · exact hq 2

/-! ### The coordinates `(inner pair, outer pair)` -/

/-- The relabelling `(inner pair, outer pair) ↦ (v₀, p₀, p₁, v₁)` of four coordinates. -/
def ksNSig : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim ![1, 2] ![0, 3]
  invFun := ![Sum.inr 0, Sum.inl 0, Sum.inl 1, Sum.inr 1]
  left_inv := by intro x; rcases x with i | i <;> fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- The measurable equivalence `(p, v) ↦ (v₀, p₀, p₁, v₁)`. -/
noncomputable def ksNSplitEquiv : (Fin 2 → ℝ) × (Fin 2 → ℝ) ≃ᵐ (Fin 4 → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi fun _ : Fin 2 ⊕ Fin 2 => ℝ).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ) ksNSig)

theorem ksN_splitEquiv_apply (p v : Fin 2 → ℝ) : ksNSplitEquiv (p, v) = ![v 0, p 0, p 1, v 1] := by
  funext i
  fin_cases i <;>
    simp [ksNSplitEquiv, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast,
      ksNSig, MeasurableEquiv.sumPiEquivProdPi]

theorem ksN_splitEquiv_mp : MeasurePreserving ksNSplitEquiv (volume.prod volume) volume :=
  (volume_measurePreserving_sumPiEquivProdPi_symm _).trans
    (volume_measurePreserving_piCongrLeft _ _)

theorem ksN_preimage_splitEquiv :
    ksNSplitEquiv ⁻¹' chengWuSet (1 : Fin 4) = chengWuSet (0 : Fin 2) ×ˢ ksNPos 2 := by
  ext ⟨p, v⟩
  simp only [mem_preimage, ksN_splitEquiv_apply, mem_chengWuSet, mem_prod, ksNPos,
    mem_ofPred_eq, Fin.forall_fin_succ, IsEmpty.forall_iff]
  simp
  tauto

theorem ksN_snoc_splitEquiv (pv : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    (Fin.snoc (ksNSplitEquiv pv) (1 - ksNSplitEquiv pv 1) : Fin 5 → ℝ) =
      ksNIns (Fin.snoc pv.1 (1 - pv.1 0)) pv.2 := by
  obtain ⟨p, v⟩ := pv
  rw [ksN_splitEquiv_apply]
  funext i
  fin_cases i <;> rfl

/-! ### The outer orthant integral as a function of the inner point -/

section Scale

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : (Fin 5 → ℝ) → E}
  (hF : ∀ z : Fin 5 → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t → F (t • z) = (t ^ 5)⁻¹ • F z)
include hF

/-- **The outer orthant integral is homogeneous of degree `-3` in the inner point.** -/
theorem ksN_ksNIns_scale {q : Fin 3 → ℝ} (hq : ∀ i, 0 < q i) {t : ℝ} (ht : 0 < t) :
    (IntegrableOn (fun v => F (ksNIns (t • q) v)) (ksNPos 2) ↔
      IntegrableOn (fun v => F (ksNIns q v)) (ksNPos 2)) ∧
    ∫ v in ksNPos 2, F (ksNIns (t • q) v) = (t ^ 3)⁻¹ • ∫ v in ksNPos 2, F (ksNIns q v) := by
  set G : (Fin 2 → ℝ) → E := (ksNPos 2).indicator fun v => F (ksNIns q v)
  have hpt : ∀ v, (ksNPos 2).indicator (fun v => F (ksNIns (t • q) v)) v =
      (t ^ 5)⁻¹ • G (t⁻¹ • v) := fun v => by
    simp only [G]
    by_cases hv : v ∈ ksNPos 2
    · have hv' := (ksN_smul_mem_ksNPos (inv_pos.2 ht) v).2 hv
      rw [indicator_of_mem hv, indicator_of_mem hv', ksN_ksNIns_smul ht.ne',
        hF _ (ksN_ksNIns_pos hq hv') t ht]
    · rw [indicator_of_notMem hv, indicator_of_notMem
        (mt (ksN_smul_mem_ksNPos (inv_pos.2 ht) v).1 hv), smul_zero]
  have hfun : (ksNPos 2).indicator (fun v => F (ksNIns (t • q) v)) =
      fun v => (t ^ 5)⁻¹ • G (t⁻¹ • v) := funext hpt
  have hc : (t ^ 5)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ ht.ne')
  refine ⟨?_, ?_⟩
  · rw [← integrable_indicator_iff (measurableSet_ksNPos 2),
      ← integrable_indicator_iff (measurableSet_ksNPos 2), hfun]
    change Integrable ((t ^ 5)⁻¹ • fun v => G (t⁻¹ • v)) volume ↔ Integrable G volume
    rw [integrable_smul_iff hc]
    exact integrable_comp_smul_iff volume G (inv_ne_zero ht.ne')
  · rw [← integral_indicator (measurableSet_ksNPos 2), ← integral_indicator
      (measurableSet_ksNPos 2), hfun, integral_smul, Measure.integral_comp_smul,
      Module.finrank_fin_fun, inv_pow, inv_inv, abs_of_pos (by positivity), smul_smul]
    congr 1
    field_simp

end Scale

/-! ### The nested form -/

section Nest

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : (Fin 5 → ℝ) → E}
  (hF : ∀ z : Fin 5 → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t → F (t • z) = (t ^ 5)⁻¹ • F z)
  (w τ : (Fin 3 → ℝ) → ℝ) (G : (Fin 3 → ℝ) → (Fin 3 → ℝ) → E)
  (hτ : ∀ q : Fin 3 → ℝ, (∀ i, 0 < q i) → ∑ i, q i = 1 → 0 < τ q)
  (hG : ∀ q : Fin 3 → ℝ, (∀ i, 0 < q i) → ∑ i, q i = 1 → ∀ z : Fin 3 → ℝ, (∀ i, 0 < z i) →
    ∀ t : ℝ, 0 < t → G q (t • z) = (t ^ 3)⁻¹ • G q z)
  (hslice : ∀ q : Fin 3 → ℝ, (∀ i, 0 < q i) → ∑ i, q i = 1 → ∀ v ∈ ksNPos 2,
    F (ksNIns q v) = w q • G q (Fin.snoc v (τ q)))

/-- The nested outer integral at a normalized inner point: `(w/τ)(q) ∫_{Δ₂} G_q`. -/
noncomputable def ksNNestR (q : Fin 3 → ℝ) : E :=
  (w q * (τ q)⁻¹) • ∫ y in simplexSet 2, G q (simplexPoint y)

include hF hτ hG hslice

/-- **The outer orthant integral at an inner point with an integrable section** is
`σ⁻³ R(q/σ)`, `σ = Σq`. -/
theorem ksN_nest3_point {q : Fin 3 → ℝ} (hq : ∀ i, 0 < q i)
    (hsec : IntegrableOn (fun v => F (ksNIns q v)) (ksNPos 2)) :
    ∫ v in ksNPos 2, F (ksNIns q v) =
      ((∑ i, q i) ^ 3)⁻¹ • ksNNestR w τ G ((∑ i, q i)⁻¹ • q) := by
  set σ := ∑ i, q i with hσdef
  have hσ : 0 < σ := Finset.sum_pos (fun i _ => hq i) Finset.univ_nonempty
  set p := σ⁻¹ • q with hpdef
  have hp : ∀ i, 0 < p i := fun i => by
    simp only [hpdef, Pi.smul_apply, smul_eq_mul]
    exact mul_pos (inv_pos.2 hσ) (hq i)
  have hp1 : ∑ i, p i = 1 := by
    simp only [hpdef, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ← hσdef]
    exact inv_mul_cancel₀ hσ.ne'
  have hqp : σ • p = q := by
    rw [hpdef, smul_smul, mul_inv_cancel₀ hσ.ne', one_smul]
  obtain ⟨hiff, heq⟩ := ksN_ksNIns_scale hF hp hσ
  rw [hqp] at hiff heq
  rw [heq]
  congr 1
  have hsec' := hiff.1 hsec
  have hτp := hτ p hp hp1
  have hcg : EqOn (fun v => F (ksNIns p v)) (fun v => w p • G p (Fin.snoc v (τ p)))
      (ksNPos 2) := fun v hv => hslice p hp hp1 v hv
  rw [setIntegral_congr_fun (measurableSet_ksNPos 2) hcg, integral_smul, ksNNestR]
  by_cases hw : w p = 0
  · simp [hw]
  have hint : IntegrableOn (fun v => G p (Fin.snoc v (τ p))) (ksNPos 2) := by
    have h2 : IntegrableOn (fun v => (w p)⁻¹ • (w p • G p (Fin.snoc v (τ p)))) (ksNPos 2) :=
      (hsec'.congr_fun hcg (measurableSet_ksNPos 2)).smul (w p)⁻¹
    simpa only [smul_smul, inv_mul_cancel₀ hw, one_smul] using h2
  obtain ⟨hsc1, hsc2⟩ := ksN_integral_pos_snoc (hG p hp hp1) hτp
  obtain ⟨-, hb⟩ := ksN_integral_pos_snoc_one (hG p hp hp1) (hsc1.1 hint)
  rw [hsc2, hb, smul_smul]

/-- **Hierarchical Cheng–Wu variables for a vertex insertion.** For `F` on `ℝ⁵` homogeneous of
degree `-5` and integrable on `Δ₄`, whose value at a normalized inner point `q` (lines `1, 2, 4`)
is `w(q) G_q(v, τ(q))` with `G_q` homogeneous of degree `-3`:
`∫_{Δ₄} F = ∫_{Δ₂} (w/τ)(q) ∫_{Δ₂} G_q dq`, the outer function integrable on `Δ₂`. -/
theorem ksN_nest3 (hI : IntegrableOn (fun y => F (simplexPoint y)) (simplexSet 4)) :
    IntegrableOn (fun y => ksNNestR w τ G (simplexPoint y)) (simplexSet 2) ∧
    ∫ y in simplexSet 4, F (simplexPoint y) =
      ∫ y in simplexSet 2, ksNNestR w τ G (simplexPoint y) := by
  set Ψ : (Fin 3 → ℝ) → E := fun q => ∫ v in ksNPos 2, F (ksNIns q v) with hΨdef
  have hΨ : ∀ z : Fin 3 → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t → Ψ (t • z) = (t ^ 3)⁻¹ • Ψ z :=
    fun z hz t ht => (ksN_ksNIns_scale hF hz ht).2
  -- the Cheng–Wu theorem for `F`, inner coordinates `1, 4` on the simplex
  have hCW := integral_simplex_chengWu (1 : Fin 4) F hF
  have hIw := (integrableOn_simplex_chengWu_iff (1 : Fin 4) F hF).1 hI
  have he := ksN_splitEquiv_mp
  set g : (Fin 2 → ℝ) × (Fin 2 → ℝ) → E := fun pv => F (ksNIns (Fin.snoc pv.1 (1 - pv.1 0)) pv.2)
  have hg : (fun pv => F (Fin.snoc (ksNSplitEquiv pv) (1 - ksNSplitEquiv pv 1))) = g := by
    funext pv
    rw [ksN_snoc_splitEquiv]
  have hprod : IntegrableOn g (chengWuSet (0 : Fin 2) ×ˢ ksNPos 2) (volume.prod volume) := by
    rw [← he.integrableOn_comp_preimage ksNSplitEquiv.measurableEmbedding,
      ksN_preimage_splitEquiv] at hIw
    rw [← hg]
    exact hIw
  have hE1 : ∫ w in chengWuSet (1 : Fin 4), F (Fin.snoc w (1 - w 1)) =
      ∫ pv in chengWuSet (0 : Fin 2) ×ˢ ksNPos 2, g pv ∂(volume.prod volume) := by
    rw [← he.setIntegral_preimage_emb ksNSplitEquiv.measurableEmbedding,
      ksN_preimage_splitEquiv, ← hg]
  have hprod' : Integrable g ((volume.restrict (chengWuSet (0 : Fin 2))).prod
      (volume.restrict (ksNPos 2))) := by
    rw [Measure.prod_restrict]
    exact hprod
  have hFub : ∫ pv in chengWuSet (0 : Fin 2) ×ˢ ksNPos 2, g pv ∂(volume.prod volume) =
      ∫ p in chengWuSet (0 : Fin 2), Ψ (Fin.snoc p (1 - p 0)) :=
    setIntegral_prod g hprod
  have hΨint : IntegrableOn (fun p => Ψ (Fin.snoc p (1 - p 0))) (chengWuSet (0 : Fin 2)) :=
    hprod'.integral_prod_left
  -- the Cheng–Wu theorem backwards for `Ψ`
  have hCWΨ := integral_simplex_chengWu (0 : Fin 2) Ψ hΨ
  have hIΨ := (integrableOn_simplex_chengWu_iff (0 : Fin 2) Ψ hΨ).2 hΨint
  -- the homogeneous difference `B = Ψ - Ψ'` vanishes almost everywhere
  set Ψ' : (Fin 3 → ℝ) → E := fun q => ((∑ i, q i) ^ 3)⁻¹ • ksNNestR w τ G ((∑ i, q i)⁻¹ • q)
    with hΨ'def
  set B : (Fin 3 → ℝ) → E := fun q => Ψ q - Ψ' q with hBdef
  have hBhom : ∀ z : Fin 3 → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t → B (t • z) = (t ^ 3)⁻¹ • B z := by
    intro z hz t ht
    have hs : 0 < ∑ i, z i := Finset.sum_pos (fun i _ => hz i) Finset.univ_nonempty
    have hst : ∑ i, (t • z) i = t * ∑ i, z i := by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    have hpt : (∑ i, (t • z) i)⁻¹ • (t • z) = (∑ i, z i)⁻¹ • z := by
      rw [hst, smul_smul]
      congr 1
      field_simp
    simp only [hBdef, hΨ'def]
    rw [hΨ z hz t ht, hpt, hst, smul_sub, smul_smul, mul_pow, mul_inv]
  have hae : ∀ᵐ p ∂(volume.restrict (chengWuSet (0 : Fin 2))), B (Fin.snoc p (1 - p 0)) = 0 := by
    filter_upwards [ae_restrict_mem (measurableSet_chengWuSet (0 : Fin 2)),
      hprod'.prod_right_ae] with p hp hsec
    have hq : ∀ i, 0 < (Fin.snoc p (1 - p 0) : Fin 3 → ℝ) i := fun i => by
      induction i using Fin.lastCases with
      | last => simp only [Fin.snoc_last]; linarith [(mem_chengWuSet.1 hp).2]
      | cast i => simp only [Fin.snoc_castSucc]; exact (mem_chengWuSet.1 hp).1 i
    simp only [hBdef, hΨ'def, hΨdef]
    rw [ksN_nest3_point hF w τ G hτ hG hslice hq hsec, sub_self]
  have hBint : IntegrableOn (fun p => B (Fin.snoc p (1 - p 0))) (chengWuSet (0 : Fin 2)) :=
    (integrable_zero _ _ _).congr (hae.mono fun _ h => h.symm)
  have hB0 : ∫ p in chengWuSet (0 : Fin 2), B (Fin.snoc p (1 - p 0)) = 0 :=
    integral_eq_zero_of_ae hae
  have hIB := (integrableOn_simplex_chengWu_iff (0 : Fin 2) B hBhom).2 hBint
  have hCWB := integral_simplex_chengWu (0 : Fin 2) B hBhom
  have hRB : (fun y => ksNNestR w τ G (simplexPoint y)) =
      fun y => Ψ (simplexPoint y) - B (simplexPoint y) := by
    funext y
    simp only [hBdef, hΨ'def, sum_simplexPoint, one_pow, inv_one, one_smul, sub_sub_cancel]
  rw [hRB]
  refine ⟨hIΨ.sub hIB, ?_⟩
  rw [integral_sub hIΨ hIB, hCWB, hB0, sub_zero, hCWΨ, ← hFub, ← hE1, ← hCW]

end Nest

end QED.ChainProof.SetAKS

end
