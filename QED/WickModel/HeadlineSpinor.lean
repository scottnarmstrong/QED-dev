/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.Spinor
import QED.Algebra.Contraction
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The on-shell spinors span the Dirac solution spaces

For `m > 0` and on-shell `p` with `p⁰ > 0`, the spinors `u_s(p)` of `QED.Dirac.spinor` satisfy
the completeness relation `Σ_s u_s(p) ū_s(p) = m - p̸`. Since `(m - p̸) u = 2m u` for every
column `u` with `(p̸ + m) u = 0`, and `w (m - p̸) = 2m w` for every row `w` with
`w (p̸ + m) = 0`, it follows that these solution spaces are spanned by the `u_s(p)` and the
`ū_s(p)`, with coefficients `ū_s(p) u / 2m` and `w u_s(p) / 2m` ((38.1), (38.16)). So a
sandwich `w X u` vanishes for all solutions as soon as it vanishes on the spinor bases.

## Main statements

* `QED.WickModel.Headline.sum_vecMulVec_spinor`: `Σ_s u_s(p) ū_s(p) = m - p̸`.
* `QED.WickModel.Headline.eq_sum_spinor`: a column solution is `Σ_s (ū_s(p) u / 2m) u_s(p)`.
* `QED.WickModel.Headline.eq_sum_bar_spinor`: a row solution is `Σ_s (w u_s(p) / 2m) ū_s(p)`.
* `QED.WickModel.Headline.sandwich_eq_zero_of_spinor`: a sandwich that vanishes on the spinor
  bases vanishes on all solutions.

## Proof outline

With `M = m - p̸` and `c = 1/√(2m(m + p⁰))`, `u_s(p) = c M u_s(0)` and `ū_s(p) = c ū_s(0) M`,
so `Σ_s u_s(p) ū_s(p) = c² M (Σ_s u_s(0) ū_s(0)) M = c² m M (1 + β) M`, by the explicit rest
spinors. On shell `M² = 2m M`, and `M β M = 2p⁰ M` from `{γ⁰, p̸} = -2p⁰` and `p̸² = m²`.

The declarations here are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Matrix Complex QED.Dirac

namespace QED.WickModel

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- **Rest-spinor completeness**: `Σ_s u_s(0) ū_s(0) = m (1 + β)` for `m ≥ 0`. -/
theorem Headline.sum_vecMulVec_restSpinor {m : ℝ} (hm : 0 ≤ m) :
    ∑ s, vecMulVec (restSpinor m s) (bar (restSpinor m s)) = (m : ℂ) • (𝟙 + beta) := by
  have hsq : (Real.sqrt m : ℂ) * (Real.sqrt m : ℂ) = (m : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_two, vecMulVec, bar, restSpinor, beta, vecMul, dotProduct,
      Fin.sum_univ_four, hsq]

/-- On shell, `(m - p̸) β (m - p̸) = 2p⁰ (m - p̸)`. -/
theorem Headline.mass_sub_slash_mul_beta_mul (m : ℝ) (p : Fin 4 → ℝ)
    (hp : Minkowski.dot p p = -m ^ 2) :
    ((m : ℂ) • 𝟙 - slash p) * beta * ((m : ℂ) • 𝟙 - slash p) =
      ((2 * p 0 : ℝ) : ℂ) • ((m : ℂ) • 𝟙 - slash p) := by
  set S := slash p with hS
  have hanti : beta * S + S * beta = ((-2 * p 0 : ℝ) : ℂ) • 𝟙 := by
    rw [beta_eq_gamma_zero, hS]
    exact gamma_slash_anticomm 0 p
  have hSB : S * beta = ((-2 * p 0 : ℝ) : ℂ) • 𝟙 - beta * S := by
    rw [← hanti]; abel
  have hSS : S * S = ((m : ℂ) * m) • 𝟙 := by
    rw [hS, slash_mul_slash, hp]
    push_cast
    ring_nf
  have hzero : ((m : ℂ) • 𝟙 + S) * ((m : ℂ) • 𝟙 - S) = 0 := by
    rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, hSS]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
    abel
  calc ((m : ℂ) • 𝟙 - S) * beta * ((m : ℂ) • 𝟙 - S)
      = ((m : ℂ) • beta - S * beta) * ((m : ℂ) • 𝟙 - S) := by
        rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
    _ = beta * (((m : ℂ) • 𝟙 + S) * ((m : ℂ) • 𝟙 - S))
          - ((-2 * p 0 : ℝ) : ℂ) • ((m : ℂ) • 𝟙 - S) := by
        rw [hSB, ← Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one,
          show ((-2 * p 0 : ℝ) : ℂ) • ((m : ℂ) • 𝟙 - S)
            = (((-2 * p 0 : ℝ) : ℂ) • 𝟙) * ((m : ℂ) • 𝟙 - S) by
              rw [Matrix.smul_mul, Matrix.one_mul],
          ← Matrix.sub_mul]
        congr 1
        abel
    _ = ((2 * p 0 : ℝ) : ℂ) • ((m : ℂ) • 𝟙 - S) := by
        rw [hzero, Matrix.mul_zero, zero_sub, ← neg_smul]
        congr 1
        push_cast
        ring

/-- **Completeness of the on-shell spinors** ((38.1), (38.17)): `Σ_s u_s(p) ū_s(p) = m - p̸`
for `m > 0` and on-shell `p` with `p⁰ > 0`. -/
theorem Headline.sum_vecMulVec_spinor {m : ℝ} (hm : 0 < m) {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -m ^ 2) (hp0 : 0 < p 0) :
    ∑ s, vecMulVec (spinor m p s) (bar (spinor m p s)) = (m : ℂ) • 𝟙 - slash p := by
  set c : ℝ := (Real.sqrt (2 * m * (m + p 0)))⁻¹ with hc
  set M : Matrix (Fin 4) (Fin 4) ℂ := (m : ℂ) • 𝟙 - slash p with hM
  have hX : 0 < 2 * m * (m + p 0) := by positivity
  have hc2 : c * c * (2 * m * (m + p 0)) = 1 := by
    rw [hc, ← mul_inv, Real.mul_self_sqrt hX.le, inv_mul_cancel₀ hX.ne']
  have hbar : ∀ s, bar (spinor m p s) = (c : ℂ) • (bar (restSpinor m s) ᵥ* M) := by
    intro s
    simp only [spinor, ← hc, ← hM]
    rw [bar_smul, bar_mulVec, hM, beta_mul_conjTranspose_mass_sub_slash_mul_beta]
  have hu : ∀ s, spinor m p s = (c : ℂ) • (M *ᵥ restSpinor m s) := fun s => rfl
  have hMM : M * M = (2 * m : ℂ) • M := mass_sub_slash_sq m p hp
  have hMBM : M * beta * M = ((2 * p 0 : ℝ) : ℂ) • M := Headline.mass_sub_slash_mul_beta_mul m p hp
  calc ∑ s, vecMulVec (spinor m p s) (bar (spinor m p s))
      = ∑ s, ((c : ℂ) * c) • (M * vecMulVec (restSpinor m s) (bar (restSpinor m s)) * M) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [hbar, hu, smul_vecMulVec, vecMulVec_smul, smul_smul, mul_vecMulVec, vecMulVec_mul]
    _ = ((c : ℂ) * c) • (M * ((m : ℂ) • (𝟙 + beta)) * M) := by
        rw [← Finset.smul_sum, ← Finset.sum_mul, ← Finset.mul_sum,
          Headline.sum_vecMulVec_restSpinor hm.le]
    _ = ((c : ℂ) * c * m * (2 * m + 2 * p 0)) • M := by
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul,
          hMM, hMBM, ← add_smul, smul_smul, smul_smul]
        congr 1
        push_cast
        ring
    _ = M := by
        have h1 : ((c * c * (2 * m * (m + p 0)) : ℝ) : ℂ) = 1 := by rw [hc2]; simp
        have h2 : (c : ℂ) * c * m * (2 * m + 2 * p 0) = 1 := by
          push_cast at h1
          linear_combination h1
        rw [h2, one_smul]

/-- **Column solutions are spanned by the `u_s(p)`** (38.1): if `(p̸ + m) u = 0`, then
`u = Σ_s (ū_s(p) u / 2m) u_s(p)`. -/
theorem Headline.eq_sum_spinor {m : ℝ} (hm : 0 < m) {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -m ^ 2) (hp0 : 0 < p 0) {u : Fin 4 → ℂ}
    (hu : slash p *ᵥ u = -((m : ℂ) • u)) :
    u = ∑ s, ((2 * m : ℂ)⁻¹ * (bar (spinor m p s) ⬝ᵥ u)) • spinor m p s := by
  have hm' : (2 * m : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 2 * m := by positivity
    exact_mod_cast this.ne'
  have h1 : ((m : ℂ) • 𝟙 - slash p) *ᵥ u = (2 * m : ℂ) • u := by
    rw [sub_mulVec, smul_mulVec, one_mulVec, hu]
    module
  have h2 : ((m : ℂ) • 𝟙 - slash p) *ᵥ u = ∑ s, (bar (spinor m p s) ⬝ᵥ u) • spinor m p s := by
    rw [← Headline.sum_vecMulVec_spinor hm hp hp0, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [vecMulVec_mulVec, op_smul_eq_smul]
  calc u = (2 * m : ℂ)⁻¹ • ((2 * m : ℂ) • u) := by rw [smul_smul, inv_mul_cancel₀ hm', one_smul]
    _ = _ := by
        rw [← h1, h2, Finset.smul_sum]
        simp only [smul_smul]

/-- **Row solutions are spanned by the `ū_s(p)`** (38.16): if `w (p̸ + m) = 0`, then
`w = Σ_s (w u_s(p) / 2m) ū_s(p)`. -/
theorem Headline.eq_sum_bar_spinor {m : ℝ} (hm : 0 < m) {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -m ^ 2) (hp0 : 0 < p 0) {w : Fin 4 → ℂ}
    (hw : w ᵥ* slash p = -((m : ℂ) • w)) :
    w = ∑ s, ((2 * m : ℂ)⁻¹ * (w ⬝ᵥ spinor m p s)) • bar (spinor m p s) := by
  have hm' : (2 * m : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 2 * m := by positivity
    exact_mod_cast this.ne'
  have h1 : w ᵥ* ((m : ℂ) • 𝟙 - slash p) = (2 * m : ℂ) • w := by
    rw [vecMul_sub, vecMul_smul, vecMul_one, hw]
    module
  have h2 : w ᵥ* ((m : ℂ) • 𝟙 - slash p) = ∑ s, (w ⬝ᵥ spinor m p s) • bar (spinor m p s) := by
    rw [← Headline.sum_vecMulVec_spinor hm hp hp0, Matrix.vecMul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [vecMul_vecMulVec]
  calc w = (2 * m : ℂ)⁻¹ • ((2 * m : ℂ) • w) := by rw [smul_smul, inv_mul_cancel₀ hm', one_smul]
    _ = _ := by
        rw [← h1, h2, Finset.smul_sum]
        simp only [smul_smul]

/-- **A sandwich vanishing on the spinor bases vanishes on all solutions.** For on-shell
positive-energy `p'`, `p` and a matrix `X`: if `ū_{s'}(p') X u_s(p) = 0` for all spins, then
`w X u = 0` for every column `u` with `(p̸ + m) u = 0` and every row `w` with
`w (p̸' + m) = 0`. -/
theorem Headline.sandwich_eq_zero_of_spinor {m : ℝ} (hm : 0 < m) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) {X : Matrix (Fin 4) (Fin 4) ℂ}
    (h : ∀ s' s, bar (spinor m p' s') ⬝ᵥ (X *ᵥ spinor m p s) = 0) {u w : Fin 4 → ℂ}
    (hu : slash p *ᵥ u = -((m : ℂ) • u)) (hw : w ᵥ* slash p' = -((m : ℂ) • w)) :
    w ⬝ᵥ (X *ᵥ u) = 0 := by
  rw [Headline.eq_sum_spinor hm hp hp0 hu, Headline.eq_sum_bar_spinor hm hp' hp0' hw]
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, sum_dotProduct,
    dotProduct_smul, smul_dotProduct, h, smul_zero, Finset.sum_const_zero]

end QED.WickModel

end
