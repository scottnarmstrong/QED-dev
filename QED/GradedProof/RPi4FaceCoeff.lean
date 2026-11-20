/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4LoopDeg
public import QED.GradedProof.RPi4CollapseSwap

/-!
# (R-Π₄) step L6d1: the coefficients of the parametric integrand on a face

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d1. For a theta graph
with chain sums `Z₁` (row `(1, 0)`), `Z₂` (row `(0, 1)`), `Z₃` (row `(1, -1)`) the inverse
Symanzik matrix is `adj A / U` with `adj A = [[Z₂ + Z₃, Z₃], [Z₃, Z₁ + Z₃]]`. On the face where
`Z₂ + Z₃` is small, all its entries but `(1, 1)` stay below `1 / Z₁`; on the face where
`Z₁ + Z₃` is small, all but `(0, 0)` stay below `1 / Z₂`:

* `symanzikMatrix_inv_chain`, `abs_inv_le_chain_one`, `abs_inv_le_chain_two`, `abs_inv_le_chain`;
* `norm_cOneAt_le`, `norm_cTwoAt_le`, `norm_cTwoAt_le_deg`, `norm_cThreeAt_le`,
  `norm_cThreeAt_le_deg_one`, `norm_cThreeAt_le_deg_two`: the three coefficients of the
  parametric integrand at a point, bounded by `U⁻²` times the contraction bounds of
  `QED.GradedProof.RPi4.norm_contractTwo_le` and its sharp forms in `RPi4LoopDeg`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop

variable {m : ℕ}

/-! ### The inverse Symanzik matrix of a theta graph -/

section Inverse

variable (α : Fin (m + 1) → Fin 2 → ℝ) (z : Fin (m + 1) → ℝ)
  (hα : ∀ i, α i = ![1, 0] ∨ α i = ![0, 1] ∨ α i = ![1, -1])

include hα

/-- **The inverse Symanzik matrix of a theta graph** in its chain sums. -/
theorem symanzikMatrix_inv_chain :
    (symanzikMatrix α z)⁻¹ 0 0 = (chainZ α z ![0, 1] + chainZ α z ![1, -1]) / symanzikU α z ∧
      (symanzikMatrix α z)⁻¹ 1 1 =
        (chainZ α z ![1, 0] + chainZ α z ![1, -1]) / symanzikU α z ∧
      (symanzikMatrix α z)⁻¹ 0 1 = chainZ α z ![1, -1] / symanzikU α z ∧
      (symanzikMatrix α z)⁻¹ 1 0 = chainZ α z ![1, -1] / symanzikU α z := by
  obtain ⟨h00, h11, h01, h10⟩ := symanzikMatrix_chain α z hα
  have hU : symanzikU α z = (symanzikMatrix α z).det := rfl
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two, Matrix.smul_apply,
    smul_eq_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, h00, h11, h01, h10, ← hU]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

variable {z} (hz : ∀ i, 0 ≤ z i) (hU : symanzikU α z ≠ 0)

include hz hU

theorem symanzikU_pos_chain : 0 < symanzikU α z := by
  rw [symanzikU_chain α z hα] at hU ⊢
  have := chainZ_nonneg α hz ![1, 0]
  have := chainZ_nonneg α hz ![0, 1]
  have := chainZ_nonneg α hz ![1, -1]
  exact lt_of_le_of_ne (by positivity) (Ne.symm hU)

/-- **Off the entry `(1, 1)`**: `|(A⁻¹)ᵣₜ| ≤ 1 / Z₁`. -/
theorem abs_inv_le_chain_one (hZ : 0 < chainZ α z ![1, 0]) (r t : Fin 2) (hrt : (r, t) ≠ (1, 1)) :
    |(symanzikMatrix α z)⁻¹ r t| ≤ 1 / chainZ α z ![1, 0] := by
  have hUp := symanzikU_pos_chain α hα hz hU
  obtain ⟨h00, -, h01, h10⟩ := symanzikMatrix_inv_chain α z hα
  have h1 := chainZ_nonneg α hz ![0, 1]
  have h3 := chainZ_nonneg α hz ![1, -1]
  have hUc := symanzikU_chain α z hα
  have key : (chainZ α z ![0, 1] + chainZ α z ![1, -1]) / symanzikU α z ≤
      1 / chainZ α z ![1, 0] := by
    rw [div_le_div_iff₀ hUp hZ]; nlinarith
  have key' : chainZ α z ![1, -1] / symanzikU α z ≤ 1 / chainZ α z ![1, 0] :=
    (div_le_div_of_nonneg_right (by linarith) hUp.le).trans key
  fin_cases r <;> fin_cases t <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] at hrt ⊢
  · rw [h00, abs_of_nonneg (by positivity)]; exact key
  · rw [h01, abs_of_nonneg (by positivity)]; exact key'
  · rw [h10, abs_of_nonneg (by positivity)]; exact key'
  · exact absurd rfl hrt

/-- **Off the entry `(0, 0)`**: `|(A⁻¹)ᵣₜ| ≤ 1 / Z₂`. -/
theorem abs_inv_le_chain_two (hZ : 0 < chainZ α z ![0, 1]) (r t : Fin 2) (hrt : (r, t) ≠ (0, 0)) :
    |(symanzikMatrix α z)⁻¹ r t| ≤ 1 / chainZ α z ![0, 1] := by
  have hUp := symanzikU_pos_chain α hα hz hU
  obtain ⟨-, h11, h01, h10⟩ := symanzikMatrix_inv_chain α z hα
  have h1 := chainZ_nonneg α hz ![1, 0]
  have h3 := chainZ_nonneg α hz ![1, -1]
  have hUc := symanzikU_chain α z hα
  have key : (chainZ α z ![1, 0] + chainZ α z ![1, -1]) / symanzikU α z ≤
      1 / chainZ α z ![0, 1] := by
    rw [div_le_div_iff₀ hUp hZ]; nlinarith
  have key' : chainZ α z ![1, -1] / symanzikU α z ≤ 1 / chainZ α z ![0, 1] :=
    (div_le_div_of_nonneg_right (by linarith) hUp.le).trans key
  fin_cases r <;> fin_cases t <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] at hrt ⊢
  · exact absurd rfl hrt
  · rw [h01, abs_of_nonneg (by positivity)]; exact key'
  · rw [h10, abs_of_nonneg (by positivity)]; exact key'
  · rw [h11, abs_of_nonneg (by positivity)]; exact key

/-- **Every entry**: `|(A⁻¹)ᵣₜ| ≤ (Z₁ + Z₂ + Z₃) / U`. -/
theorem abs_inv_le_chain (r t : Fin 2) :
    |(symanzikMatrix α z)⁻¹ r t| ≤
      (chainZ α z ![1, 0] + chainZ α z ![0, 1] + chainZ α z ![1, -1]) / symanzikU α z := by
  have hUp := symanzikU_pos_chain α hα hz hU
  obtain ⟨h00, h11, h01, h10⟩ := symanzikMatrix_inv_chain α z hα
  have h1 := chainZ_nonneg α hz ![1, 0]
  have h2 := chainZ_nonneg α hz ![0, 1]
  have h3 := chainZ_nonneg α hz ![1, -1]
  fin_cases r <;> fin_cases t <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, h00, h11, h01, h10] <;>
    rw [abs_of_nonneg (by positivity)] <;>
    exact div_le_div_of_nonneg_right (by linarith) hUp.le

end Inverse

/-! ### The coefficients at a point -/

section Coefficients

variable (n : ℕ) {Q : LoopQuartic} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (z : Fin (m + 1) → ℝ)

theorem norm_invU_mul_le {U : ℝ} (hU : 0 < U) {w : ℂ} {B : ℝ} (hw : ‖w‖ ≤ B) :
    ‖((U ^ 2 : ℝ) : ℂ)⁻¹ * w‖ ≤ B / U ^ 2 := by
  rw [norm_mul, norm_inv, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
    inv_mul_eq_div]
  exact div_le_div_of_nonneg_right hw (by positivity)

variable {K : ℝ} (hK : 0 ≤ K) (hX : ∀ a, ‖loopComp (-loopShift α p z) a‖ ≤ K)
  (hU : 0 < symanzikU α z)

include hK hX hU

theorem norm_cOneAt_le :
    ‖cOneAt n Q α p z‖ ≤ (n - 4).factorial * (lqNorm Q * (1 + K) ^ 4) / symanzikU α z ^ 2 := by
  refine norm_invU_mul_le hU ?_
  rw [norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_evalC_le_lqNorm Q _ hK hX) (by positivity)

theorem norm_cTwoAt_le {g : ℝ} (hg : ∀ r t, |(symanzikMatrix α z)⁻¹ r t| ≤ g) :
    ‖cTwoAt n Q α p z‖ ≤
      (n - 5).factorial / 2 * (lqHess Q * (1 + (K + K ^ 2)) * g) / symanzikU α z ^ 2 := by
  refine norm_invU_mul_le hU ?_
  rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_ofNat]
  exact mul_le_mul_of_nonneg_left (norm_contractTwo_le Q _ _ hK hX hg) (by positivity)

/-- **Degree at most one along loop `s`**: the coefficient of `v^{4-n}` sees only `g₀`. -/
theorem norm_cTwoAt_le_deg {s : Fin 2} (hQ : LoopDegLe s 1 Q) {g₀ : ℝ} (hg₀ : 0 ≤ g₀)
    (hg : ∀ r t, (r, t) ≠ (s, s) → |(symanzikMatrix α z)⁻¹ r t| ≤ g₀) :
    ‖cTwoAt n Q α p z‖ ≤
      (n - 5).factorial / 2 * (lqHess Q * (1 + (K + K ^ 2)) * g₀) / symanzikU α z ^ 2 := by
  refine norm_invU_mul_le hU ?_
  rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_ofNat]
  exact mul_le_mul_of_nonneg_left (norm_contractTwo_le_deg hQ _ _ hK hX hg₀ hg) (by positivity)

omit hK hX in
theorem norm_cThreeAt_le {g : ℝ} (hg : ∀ r t, |(symanzikMatrix α z)⁻¹ r t| ≤ g) :
    ‖cThreeAt n Q α z‖ ≤ (n - 6).factorial / 4 * (lqQuart Q * (3 * g ^ 2)) / symanzikU α z ^ 2 := by
  refine norm_invU_mul_le hU ?_
  rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_ofNat]
  exact mul_le_mul_of_nonneg_left (norm_contractFour_le Q _ hg) (by positivity)

omit hK hX in
/-- **Degree at most one along loop `s`**: the coefficient of `v^{5-n}` sees only `g₀`. -/
theorem norm_cThreeAt_le_deg_one {s : Fin 2} (hQ : LoopDegLe s 1 Q) {g₀ : ℝ} (hg₀ : 0 ≤ g₀)
    (hg : ∀ r t, (r, t) ≠ (s, s) → |(symanzikMatrix α z)⁻¹ r t| ≤ g₀) :
    ‖cThreeAt n Q α z‖ ≤
      (n - 6).factorial / 4 * (lqQuart Q * (3 * g₀ ^ 2)) / symanzikU α z ^ 2 := by
  refine norm_invU_mul_le hU ?_
  rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_ofNat]
  exact mul_le_mul_of_nonneg_left (norm_contractFour_le_deg_one hQ _ hg₀ hg) (by positivity)

omit hK hX in
/-- **Degree at most two along loop `s`**: the coefficient of `v^{5-n}` sees `g` at most once. -/
theorem norm_cThreeAt_le_deg_two {s : Fin 2} (hQ : LoopDegLe s 2 Q) {g₀ g : ℝ} (hg₀ : 0 ≤ g₀)
    (hgg : ∀ r t, |(symanzikMatrix α z)⁻¹ r t| ≤ g)
    (hg : ∀ r t, (r, t) ≠ (s, s) → |(symanzikMatrix α z)⁻¹ r t| ≤ g₀) :
    ‖cThreeAt n Q α z‖ ≤
      (n - 6).factorial / 4 * (lqQuart Q * (3 * (g₀ * g))) / symanzikU α z ^ 2 := by
  refine norm_invU_mul_le hU ?_
  rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_ofNat]
  exact mul_le_mul_of_nonneg_left (norm_contractFour_le_deg_two hQ _ hg₀ hgg hg) (by positivity)

end Coefficients

end QED.GradedProof.RPi4

end
