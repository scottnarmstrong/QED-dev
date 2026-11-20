/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2F
public import QED.GradedProof.WI2VtxP

/-!
# A7 for the `δ₂` vertex classes: insertions on `F`

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A7. At zero photon momentum (`p' = p`, on shell), the `δ₂` vertex class on the incoming
(outgoing) internal electron line contracted with `r` is `e κ / auxLimit` times the parametric
value of the two-slot numerator of `F` with the insertion `(m - k̸) r̸ (m - k̸)` in slot `0`
(slot `1`), over the data `dF` with that line doubled (`sum_lower_ctLimitV_d2In`,
`sum_lower_ctLimitV_d2Out`): the insertion terms of `hasDerivAt_dF_wt`.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.WI2

open QED.GradedProof.SE2 QED.Integration.TwoLoop QED.WickModel QED.TwoLoop.ClassLimit
open QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance QED.TwoLoop.CountertermLimit
open QED.TwoLoop.Relabel QED.TwoLoop.ReflCovariance QED.TwoLoop.Insertion

theorem good_twV_dF (Q : Params) (p r : Fin 4 → ℝ) (j : Fin 2) (α β : Fin 4) :
    ∃ QV : LoopQuartic, ((dF Q).dup (eF j)).Good QV ∧
      QV.eval = fun ℓ => (dF Q).twV eF Q.m aSlotF bSlotF (cSlotF Q) (gF Q) p r ℓ j α β := by
  obtain ⟨QV, hQV⟩ := IsLoopPoly.exists_loopQuartic
    ((dF Q).isLoopPoly_twV eF Q.m aSlotF bSlotF (cSlotF Q) (gF Q) (isLoopPolyMat_gF Q) p r j α β)
  refine ⟨QV, ⟨Or.inl (by change 7 ≤ 6 + 1; norm_num), ?_⟩, hQV⟩
  rw [hQV]
  exact (dF Q).refinedBound_twV eF Q.m aSlotF bSlotF (cSlotF Q) (gF Q) (e₂ := (2 : Fin 7))
    eF_ne two_ne_eF_zero two_ne_eF_one eF_mem two_mem_EF (refinedBoundMat_gF Q) p r j α β

theorem vpos_dF_onShell (Q : Params) (hm : 0 < Q.m) (hmγ : 0 < Q.mγ) (hΛ : 0 < Q.Λ)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -Q.m ^ 2) : (dF Q).VPos ((dF Q).mom p) := by
  have hν : 0 < min Q.mγ Q.Λ := lt_min hmγ hΛ
  exact vpos_dF Q hm hν le_rfl (by rw [hp]; nlinarith)

theorem mom_dF_eF (Q : Params) (r : Fin 4 → ℝ) (j : Fin 2) : (dF Q).mom r (eF j) = r := by
  fin_cases j <;> simp [SEData.mom, dF, kindsF, eF]

theorem twE_dF (Q : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (j : Fin 2) :
    (dF Q).twE eF Q.m p ℓ j = electronNumerator Q.m (p + ℓ 0) := by
  have h := lineMomentum_dF Q p (eF j) ℓ
  fin_cases j <;> simp_all [SEData.twE, kindsF, eF, LineKind.lineMom]

/-- **The contracted `δ₂ in` vertex numerator at `p' = p`** is `e κ` times the slot-`0`
insertion numerator of `F`. -/
theorem sum_lower_numD2In (P : Params) (p r : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (α β : Fin 4) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * numD2In P p p μ (ℓ 0) α β =
      P.e * kappaSE P.e * (dF P).twV eF P.m aSlotF bSlotF (cSlotF P) (gF P) p r ℓ 0 α β := by
  have h := congrFun (congrFun (sum_lower_smul_vertexChain P.e (electronNumerator P.m (p + ℓ 0))
    (-(electronNumerator P.m (p + ℓ 0) *
      fermionCtMatrix P.δ₂ P.δm P.m (p + ℓ 0) * electronNumerator P.m (p + ℓ 0)))
    (pvPhotonNum P.mγ P.Λ) r) α) β
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h
  simp only [numD2In, h, vertexCoeff_eq, SEData.twV, SEData.tw, twE_dF, mom_dF_eF,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type, aSlotF, bSlotF,
    cSlotF, gF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ => ?_
  simp [Function.update, twE_dF, Matrix.mul_assoc]

/-- **The contracted `δ₂ out` vertex numerator at `p' = p`** is `e κ` times the slot-`1`
insertion numerator of `F`. -/
theorem sum_lower_numD2Out (P : Params) (p r : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ)
    (α β : Fin 4) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * numD2Out P p p μ (ℓ 0) α β =
      P.e * kappaSE P.e * (dF P).twV eF P.m aSlotF bSlotF (cSlotF P) (gF P) p r ℓ 1 α β := by
  have h := congrFun (congrFun (sum_lower_smul_vertexChain P.e (-(electronNumerator P.m (p + ℓ 0) *
      fermionCtMatrix P.δ₂ P.δm P.m (p + ℓ 0) * electronNumerator P.m (p + ℓ 0)))
    (electronNumerator P.m (p + ℓ 0)) (pvPhotonNum P.mγ P.Λ) r) α) β
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h
  simp only [numD2Out, h, vertexCoeff_eq, SEData.twV, SEData.tw, twE_dF, mom_dF_eF,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type, aSlotF, bSlotF,
    cSlotF, gF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ => ?_
  simp [Function.update, twE_dF, Matrix.mul_assoc]

theorem prod_lineDenom_d2_dup (κ : Fin 8 → LineKind) (hκ : κ = kindsD2In ∨ κ = kindsD2Out)
    (P : Params) (p : Fin 4 → ℝ) (j : Fin 2) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∏ i, (lineDenom (castLoopMatrix fun i => (κ i).dir) (fun i => (κ i).mom p p)
      (massesD2In P) ε i ℓ)⁻¹ =
      ∏ i, (lineDenom ((dF P).dup (eF j)).α (dbl (eF j) ((dF P).mom p)) ((dF P).dup (eF j)).M
        ε i ℓ)⁻¹ := by
  rw [prod_lineDenom_kinds]
  refine Eq.trans ?_ (prod_lineDenom_dbl (dF P).α ((dF P).mom p) (dF P).M ε (eF j) ℓ).symm
  have h : lineDenom (dF P).α ((dF P).mom p) (dF P).M ε (eF j) ℓ =
      propDenom (massesF P (eF j)) ε ((kindsF (eF j)).lineMom p p ℓ) :=
    congrArg (propDenom (massesF P (eF j)) ε) (lineMomentum_dF P p (eF j) ℓ)
  rw [prod_lineDenom_dF]
  erw [h]
  have hM : massesF P (eF j) = P.m := by fin_cases j <;> rfl
  have hk : (kindsF (eF j)).lineMom p p ℓ = p + ℓ 0 := by fin_cases j <;> rfl
  rw [hM, hk]
  rcases hκ with rfl | rfl <;>
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsD2In, kindsD2Out, massesD2In, kindsF,
    massesF, LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
  ring

/-- **A7 for `δ₂ in`**: the contracted class at `p' = p` is `e κ / auxLimit` times the
parametric value of the slot-`0` insertion numerator of `F` on the doubled data. -/
theorem sum_lower_ctLimitV_d2In (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (r : Fin 4 → ℝ) (α β : Fin 4) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * ctLimitV .d2In P p p μ α β =
      P.e * kappaSE P.e * (auxLimit P.m)⁻¹ * ((dF P).dup (eF 0)).pvF
        (fun ℓ => (dF P).twV eF P.m aSlotF bSlotF (cSlotF P) (gF P) p r ℓ 0 α β)
        (dbl (eF 0) ((dF P).mom p)) := by
  have hq : 0 ≤ Minkowski.dot (p - p) (p - p) := by simp [Minkowski.dot]
  choose v hv hct using fun μ => ctLimitV_d2In_entry P hm hmγ hΛ hp hp hq μ α β
  have hs := IsParamValue.sum Finset.univ (fun μ => ((Minkowski.lower r μ : ℝ) : ℂ))
    (fun μ _ => hv μ)
  have key := isParamValue_eq_const_mul hs (good_twV_dF P p r 0 α β)
    ((vpos_dF_onShell P hm hmγ hΛ hp).dup (eF 0)) (P.e * kappaSE P.e) fun ε _ ℓ => by
      rw [sum_lower_numD2In]
      change _ * ∏ i, (lineDenom (castLoopMatrix fun i => (kindsD2In i).dir)
        (fun i => (kindsD2In i).mom p p) (massesD2In P) ε i ℓ)⁻¹ = _
      rw [prod_lineDenom_d2_dup _ (Or.inl rfl) P p 0]
      ring
  simp only [hct, div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
  rw [key]
  ring

/-- **A7 for `δ₂ out`**: the contracted class at `p' = p` is `e κ / auxLimit` times the
parametric value of the slot-`1` insertion numerator of `F` on the doubled data. -/
theorem sum_lower_ctLimitV_d2Out (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (r : Fin 4 → ℝ) (α β : Fin 4) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * ctLimitV .d2Out P p p μ α β =
      P.e * kappaSE P.e * (auxLimit P.m)⁻¹ * ((dF P).dup (eF 1)).pvF
        (fun ℓ => (dF P).twV eF P.m aSlotF bSlotF (cSlotF P) (gF P) p r ℓ 1 α β)
        (dbl (eF 1) ((dF P).mom p)) := by
  have hq : 0 ≤ Minkowski.dot (p - p) (p - p) := by simp [Minkowski.dot]
  choose v hv hct using fun μ =>
    QED.TwoLoop.PauliZero.ctLimitV_d2Out_entry P hm hmγ hΛ hp hp hq μ α β
  have hs := IsParamValue.sum Finset.univ (fun μ => ((Minkowski.lower r μ : ℝ) : ℂ))
    (fun μ _ => hv μ)
  have key := isParamValue_eq_const_mul hs (good_twV_dF P p r 1 α β)
    ((vpos_dF_onShell P hm hmγ hΛ hp).dup (eF 1)) (P.e * kappaSE P.e) fun ε _ ℓ => by
      rw [sum_lower_numD2Out]
      change _ * ∏ i, (lineDenom (castLoopMatrix fun i => (kindsD2Out i).dir)
        (fun i => (kindsD2Out i).mom p p) (massesD2In P) ε i ℓ)⁻¹ = _
      rw [prod_lineDenom_d2_dup _ (Or.inr rfl) P p 1]
      ring
  simp only [hct, div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
  rw [key]
  ring

end QED.GradedProof.WI2

end
