/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2Dbl
public import QED.TwoLoop.ClassLimitVP

/-!
# Cancelling a doubled denominator

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A5 (the `ε`-transfer). If the numerator over the data with line `i` doubled is
`(kᵢ·kᵢ + Mᵢ²) Q₂`, its parametric value is that of `Q₂` over the undoubled data
(`SEData.pv_dup_of_eval_eq`).

## Proof

At `ε > 0` the factor is `Dᵢ + iε` with `Dᵢ ≠ 0` the denominator of line `i`, so pointwise
`Q ∏_{N+1} D⁻¹ - iε Q₂ ∏_{N+1} D⁻¹ = Q₂ ∏_N D⁻¹`. Both terms on the left are jointly integrable
(the doubled data have at least eight lines), so the joint integrals satisfy the same relation;
as `ε → 0⁺` they converge to the parametric values (`SEData.tendsto_pv`), and `iε` times a
convergent family tends to `0`.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory

namespace QED.GradedProof.WI2

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit

variable {m : ℕ}

theorem lineMomentum_dbl (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (i : Fin (m + 1)) (j : Fin (m + 2)) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum (dbl i α) (dbl i p) j ℓ = lineMomentum α p (dblIdx i j) ℓ := by
  funext μ
  simp only [lineMomentum, dbl_apply]

theorem lineDenom_dbl (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (M : Fin (m + 1) → ℝ) (ε : ℝ) (i : Fin (m + 1)) (j : Fin (m + 2)) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineDenom (dbl i α) (dbl i p) (dbl i M) ε j ℓ = lineDenom α p M ε (dblIdx i j) ℓ := by
  simp only [lineDenom, lineMomentum_dbl, dbl_apply]

theorem prod_lineDenom_dbl (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (M : Fin (m + 1) → ℝ) (ε : ℝ) (i : Fin (m + 1)) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∏ j, (lineDenom (dbl i α) (dbl i p) (dbl i M) ε j ℓ)⁻¹ =
      (∏ j, (lineDenom α p M ε j ℓ)⁻¹) * (lineDenom α p M ε i ℓ)⁻¹ := by
  rw [Fin.prod_univ_castSucc]
  simp only [lineDenom_dbl, dblIdx_castSucc, dblIdx_last]

theorem lineDenom_ne_zero (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (M : Fin (m + 1) → ℝ) {ε : ℝ} (hε : 0 < ε) (i : Fin (m + 1)) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineDenom α p M ε i ℓ ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [lineDenom, sub_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero, mul_one,
    zero_sub, zero_im, neg_eq_zero, add_zero] at this
  exact hε.ne' this

end QED.GradedProof.WI2

namespace QED.GradedProof.SE2.SEData

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.GradedProof.WI2

theorem good_dup_of_good (D : SEData) (i : Fin (D.m + 1)) {Q : LoopQuartic} (hQ : D.Good Q) :
    (D.dup i).Good Q :=
  ⟨Or.inl (by change 7 ≤ D.m + 1; have := D.hm; omega),
    (refinedBound_dbl_map hQ.2 i).mono (Finset.subset_insert _ _) le_rfl⟩

/-- **Cancelling a doubled denominator**: a numerator `(kᵢ·kᵢ + Mᵢ²) Q₂` over the data with line
`i` doubled has the value of `Q₂` over the data. -/
theorem pv_dup_of_eval_eq (D : SEData) (i : Fin (D.m + 1)) {Q Q₂ : LoopQuartic}
    (hQ : (D.dup i).Good Q) (hQ₂ : D.Good Q₂) {q : Fin (D.m + 1) → Fin 4 → ℝ}
    (he : ∀ ℓ, Q.eval ℓ = ((Minkowski.dot (lineMomentum D.α q i ℓ) (lineMomentum D.α q i ℓ) +
      D.M i ^ 2 : ℝ) : ℂ) * Q₂.eval ℓ) (hV : D.VPos q) :
    (D.dup i).pv Q (dbl i q) = D.pv Q₂ q := by
  have hQ₂' := good_dup_of_good D i hQ₂
  have hV' := hV.dup i
  have h7 : 7 ≤ (D.dup i).m := by change 7 ≤ D.m + 1; have := D.hm; omega
  -- the relation of the joint integrals at `ε > 0`
  have hrel : ∀ ε : ℝ, 0 < ε →
      QED.TwoLoop.jointEnergyFirstIntegral 2
          (fun ℓ => Q₂.eval ℓ * ∏ j, (lineDenom D.α q D.M ε j ℓ)⁻¹) =
        QED.TwoLoop.jointEnergyFirstIntegral 2
            (fun ℓ => Q.eval ℓ * ∏ j, (lineDenom (D.dup i).α (dbl i q) (D.dup i).M ε j ℓ)⁻¹) +
          -((ε : ℂ) * I) * QED.TwoLoop.jointEnergyFirstIntegral 2
            (fun ℓ => Q₂.eval ℓ *
              ∏ j, (lineDenom (D.dup i).α (dbl i q) (D.dup i).M ε j ℓ)⁻¹) := fun ε hε => by
    have hI1 := jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined Q
      (D.dup i).α (dbl i q) (D.dup i).M h7 hε (D.dup i).hcrit hQ.2
    have hI2 := QED.TwoLoop.ClassLimit.jointEnergyFirstIntegrable_const_mul (-((ε : ℂ) * I))
      (jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined Q₂
        (D.dup i).α (dbl i q) (D.dup i).M h7 hε (D.dup i).hcrit hQ₂'.2)
    rw [← QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul,
      ← QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add hI1 hI2]
    congr 1
    funext ℓ
    change _ = Q.eval ℓ * ∏ j, (lineDenom (dbl i D.α) (dbl i q) (dbl i D.M) ε j ℓ)⁻¹ +
      -((ε : ℂ) * I) * (Q₂.eval ℓ * ∏ j, (lineDenom (dbl i D.α) (dbl i q) (dbl i D.M) ε j ℓ)⁻¹)
    rw [prod_lineDenom_dbl, he ℓ]
    have hne := lineDenom_ne_zero D.α q D.M hε i ℓ
    have hD : ((Minkowski.dot (lineMomentum D.α q i ℓ) (lineMomentum D.α q i ℓ) +
        D.M i ^ 2 : ℝ) : ℂ) = lineDenom D.α q D.M ε i ℓ + (ε : ℂ) * I := by
      simp only [lineDenom]
      ring
    rw [hD]
    field_simp
    ring
  -- the limits
  have h1 := tendsto_pv hQ₂ hV
  have h2 := (tendsto_pv hQ hV').add
    (((continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds).mul_const I |>.neg
      |>.mul (tendsto_pv hQ₂' hV'))
  rw [ofReal_zero, zero_mul, neg_zero, zero_mul, add_zero] at h2
  have h3 : Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
      (fun ℓ => Q₂.eval ℓ * ∏ j, (lineDenom D.α q D.M ε j ℓ)⁻¹)) (𝓝[>] 0)
      (𝓝 ((D.dup i).pv Q (dbl i q))) := by
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hrel ε hε).symm
  exact tendsto_nhds_unique h3 h1

end QED.GradedProof.SE2.SEData

end
