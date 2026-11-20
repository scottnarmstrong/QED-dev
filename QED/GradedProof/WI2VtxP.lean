/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2P
public import QED.GradedProof.WI2VtxOpen
public import QED.TwoLoop.ReflCovarianceCounterterm
public import QED.TwoLoop.PauliZeroCovariance

/-!
# A7 for the `δ₃` vertex classes: insertions on `P0`, `P1`

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A7. At zero photon momentum (`p' = p`, on shell), the `δ₃` vertex classes contracted with
`r` are `e κ / auxLimit` times the parametric value of the one-slot numerator of `P0`, `P1` with
the insertion `(m - k̸) r̸ (m - k̸)` on the open line, over the data `dP` with that line doubled
(`sum_lower_ctLimitV_d3Slot0`, `sum_lower_ctLimitV_d3Slot1`), the term of the Ward–Takahashi
derivative `hasDerivAt_dP_wt`.

* `isParamValue_eq_const_mul`: a parametric value of product data (`ParamData`) is `κ` times
  that of `SEData` when the joint integrands are proportional at every `ε > 0`.
* `sum_lower_numD3`: `∑_μ r_μ numD3^μ = e κ slotV` (the vertex chain at `p' = p` is
  `(ie)³ (1/i)³ (2π)⁻⁴ ∑ D_{νρ} γ^ρ E γ^μ E γ^ν`, `κ = (ie)² (1/i)² (2π)⁻⁴`).
* `prod_lineDenom_d3_dup`: the nine denominators of the `δ₃` product data at `p' = p` are those
  of `dP` with line `0` doubled.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.WI2

open QED.GradedProof.SE2 QED.Integration.TwoLoop QED.WickModel QED.TwoLoop.ClassLimit
open QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance QED.TwoLoop.CountertermLimit
open QED.TwoLoop.Relabel QED.TwoLoop.ReflCovariance QED.TwoLoop.Insertion

/-- **A parametric value of product data as a multiple of one of `SEData`.** -/
theorem isParamValue_eq_const_mul {D : ParamData} {F₁ : (Fin 2 → Fin 4 → ℝ) → ℂ} {v : ℂ}
    (hv : IsParamValue D F₁ v) {D₂ : SEData} {F₂ : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (h₂ : ∃ Q : LoopQuartic, D₂.Good Q ∧ Q.eval = F₂) {q₂ : Fin (D₂.m + 1) → Fin 4 → ℝ}
    (hV₂ : D₂.VPos q₂) (κ : ℂ)
    (h : ∀ ε, 0 < ε → ∀ ℓ, F₁ ℓ * ∏ i, (lineDenom D.α D.p D.M ε i ℓ)⁻¹ =
      κ * (F₂ ℓ * ∏ i, (lineDenom D₂.α q₂ D₂.M ε i ℓ)⁻¹)) :
    v = κ * D₂.pvF F₂ q₂ := by
  obtain ⟨Q₂, hg₂, he₂⟩ := h₂
  rw [SEData.pvF_eq hg₂ he₂ hV₂]
  refine tendsto_nhds_unique hv.tendsto (((SEData.tendsto_pv hg₂ hV₂).const_mul κ).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [← QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul]
  congr 1
  funext ℓ
  rw [he₂]
  exact (h ε hε ℓ).symm

theorem good_slotV_dP (Q : Params) (p r : Fin 4 → ℝ) (α β : Fin 4) :
    ∃ QV : LoopQuartic, ((dP Q).dup 0).Good QV ∧
      QV.eval = fun ℓ => (dP Q).slotV 0 Q.m aSlotP bSlotP (cSlotP Q) p r ℓ α β := by
  obtain ⟨QV, hQV⟩ := IsLoopPoly.exists_loopQuartic
    ((dP Q).isLoopPoly_slotV 0 Q.m (A := aSlotP) (B := bSlotP) (isLoopPoly_cP Q) p r α β)
  refine ⟨QV, ⟨Or.inl (by change 7 ≤ 7 + 1; norm_num), ?_⟩, hQV⟩
  rw [hQV]
  exact (dP Q).refinedBound_slotV 0 Q.m (A := aSlotP) (B := bSlotP) zero_notMem_S_dP
    insert_subset_E_dP (refinedBound_cP Q) p r α β

theorem vpos_dP_onShell (Q : Params) (hm : 0 < Q.m) (hmγ : 0 < Q.mγ) (hΛ : 0 < Q.Λ)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -Q.m ^ 2) : (dP Q).VPos ((dP Q).mom p) := by
  have hν : 0 < min Q.mγ Q.Λ := lt_min hmγ hΛ
  exact vpos_dP Q hm hν le_rfl (by rw [hp]; nlinarith)

theorem mom_dP_zero (Q : Params) (r : Fin 4 → ℝ) : (dP Q).mom r 0 = r := by
  simp [SEData.mom, dP, SE2.kindsData, kindsSEP]

/-- Contracting the vertex chain with `r`. -/
theorem sum_lower_smul_vertexChain (e : ℝ) (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (D : Fin 4 → Fin 4 → ℂ) (r : Fin 4 → ℝ) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) • vertexChain e μ A B D =
      ((I * e) ^ 3 * (1 / I) ^ 3 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹) •
        ∑ ν, ∑ ρ, D ν ρ • (Dirac.gamma ρ * (A * Dirac.slash r * B) * Dirac.gamma ν) := by
  simp only [vertexChain, Dirac.slash, Finset.smul_sum, Matrix.mul_sum, Matrix.sum_mul,
    smul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  ring

theorem vertexCoeff_eq (e : ℝ) :
    (I * e) ^ 3 * (1 / I) ^ 3 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ = e * kappaSE e := by
  unfold kappaSE
  field_simp

/-- **The contracted `δ₃` vertex numerator at `p' = p`** is `e κ` times the one-slot insertion
numerator of `P0`, `P1`. -/
theorem sum_lower_numD3 (P : Params) (p r : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (α β : Fin 4) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * numD3 P p p μ (ℓ 0) α β =
      P.e * kappaSE P.e * (dP P).slotV 0 P.m aSlotP bSlotP (cSlotP P) p r ℓ α β := by
  have h := congrFun (congrFun (sum_lower_smul_vertexChain P.e (electronNumerator P.m (p + ℓ 0))
    (electronNumerator P.m (p + ℓ 0)) (photonNum P.δ₃ P.mγ P.Λ (ℓ 0)) r) α) β
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h
  simp only [numD3, h, vertexCoeff_eq, SEData.slotV, SEData.slotE, lineMomentum_dP_zero,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type, aSlotP, bSlotP,
    cSlotP, Finset.mul_sum, mom_dP_zero]

/-- The nine denominators of the `δ₃` product data at `p' = p` are those of `dP` with the open
line doubled. -/
theorem prod_lineDenom_d3_dup (P : Params) (p : Fin 4 → ℝ) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∏ i, (lineDenom (castLoopMatrix fun i => (kindsD3 i).dir) (fun i => (kindsD3 i).mom p p)
      (massesD3 P) ε i ℓ)⁻¹ =
      ∏ i, (lineDenom ((dP P).dup 0).α (dbl 0 ((dP P).mom p)) ((dP P).dup 0).M ε i ℓ)⁻¹ := by
  rw [prod_lineDenom_kinds]
  change _ = ∏ i, (lineDenom (dbl 0 (dP P).α) (dbl 0 ((dP P).mom p)) (dbl 0 (dP P).M) ε i ℓ)⁻¹
  rw [prod_lineDenom_dbl, prod_lineDenom_dP, lineDenom_eq_propDenom, lineMomentum_dP_zero]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsD3, massesD3, kindsSEP, massesSEP,
    LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [show (dP P).M 0 = P.m from rfl]
  ring

/-- **A7 for `δ₃` (slot `0`)**: the contracted `δ₃` vertex class at `p' = p` is `e κ / auxLimit`
times the parametric value of the insertion numerator of `P0`, `P1` on the doubled data. -/
theorem sum_lower_ctLimitV_d3Slot0 (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (r : Fin 4 → ℝ) (α β : Fin 4) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * ctLimitV .d3Slot0 P p p μ α β =
      P.e * kappaSE P.e * (auxLimit P.m)⁻¹ * ((dP P).dup 0).pvF
        (fun ℓ => (dP P).slotV 0 P.m aSlotP bSlotP (cSlotP P) p r ℓ α β)
        (dbl 0 ((dP P).mom p)) := by
  have hq : 0 ≤ Minkowski.dot (p - p) (p - p) := by simp [Minkowski.dot]
  choose v hv hct using fun μ => ctLimitV_d3Slot0_entry P hm hmγ hΛ hp hp hq μ α β
  have hs := IsParamValue.sum Finset.univ (fun μ => ((Minkowski.lower r μ : ℝ) : ℂ))
    (fun μ _ => hv μ)
  have key := isParamValue_eq_const_mul hs (good_slotV_dP P p r α β)
    ((vpos_dP_onShell P hm hmγ hΛ hp).dup 0) (P.e * kappaSE P.e) fun ε _ ℓ => by
      rw [sum_lower_numD3]
      change _ * ∏ i, (lineDenom (castLoopMatrix fun i => (kindsD3 i).dir)
        (fun i => (kindsD3 i).mom p p) (massesD3 P) ε i ℓ)⁻¹ = _
      rw [prod_lineDenom_d3_dup]
      ring
  simp only [hct, div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
  rw [key]
  ring

/-- **A7 for `δ₃` (slot `1`)**, the same value (`ctLimitV_d3Slot1_eq`). -/
theorem sum_lower_ctLimitV_d3Slot1 (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (r : Fin 4 → ℝ) (α β : Fin 4) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * ctLimitV .d3Slot1 P p p μ α β =
      P.e * kappaSE P.e * (auxLimit P.m)⁻¹ * ((dP P).dup 0).pvF
        (fun ℓ => (dP P).slotV 0 P.m aSlotP bSlotP (cSlotP P) p r ℓ α β)
        (dbl 0 ((dP P).mom p)) := by
  rw [QED.TwoLoop.PauliZero.ctLimitV_d3Slot1_eq]
  exact sum_lower_ctLimitV_d3Slot0 P hm hmγ hΛ hp r α β

end QED.GradedProof.WI2

end
