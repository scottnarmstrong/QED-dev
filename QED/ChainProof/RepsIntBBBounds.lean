/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.RepsIntBBComplex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lower bounds for the denominators at rotated loop energies

Helper for obligation O3-5 of `docs/HIGHER-LOOP-PLAN.md` (decision D-53). A denominator of the
bubble–bubble integrand at loop energies multiplied by `z` is `D = -(z t + a)² + Y - iε`, with `t`
a real combination of the loop energies, `a` a real external energy and `Y = |y|² + M² ≥ 0`.

* **On the rectangle** `1/2 ≤ Re z`, `0 ≤ Im z ≤ h` with `h a² ≤ ε/4`
  (`one_add_sq_le_rect`): `1 + t² ≤ K ‖D‖`, with `K` depending on `a`, `Y`, `ε` only. Then
  `Im D ≤ -3ε/4` (the rotation never crosses a pole) and `‖D‖ ≥ t²/8 - a² - Y - ε`.
* **At `z = 1 + s i`** with `s a² ≤ ε/4` (`one_add_sq_add_le_rot`): `1 + t² + Y ≤ K ‖D‖`, with
  `K` independent of `t` and `Y`. Then `-Im D ≥ s t² + 3ε/4` and `Re D ≥ Y - 2t² - 2a²`: the
  rotated denominator is elliptic in all momenta.

The numerator bound `norm_numC_le` and the matrix-norm facts use the `L^∞` operator norm.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.RepsIntBB

open QED.WickModel

/-! ### Scalar lower bounds -/

theorem den_re (X : ℂ) (Y ε : ℝ) :
    (-X ^ 2 + (Y : ℂ) - (ε : ℂ) * I).re = -(X.re ^ 2 - X.im ^ 2) + Y := by
  simp [sq]

theorem den_im (X : ℂ) (Y ε : ℝ) :
    (-X ^ 2 + (Y : ℂ) - (ε : ℂ) * I).im = -(2 * X.re * X.im) - ε := by
  simp [sq]
  ring

theorem neg_im_le_norm (w : ℂ) : -w.im ≤ ‖w‖ := (neg_le_abs _).trans (abs_im_le_norm _)

theorem re_le_norm (w : ℂ) : w.re ≤ ‖w‖ := (le_abs_self _).trans (abs_re_le_norm _)

theorem re_sq_sub_le_norm_den (X : ℂ) {Y ε : ℝ} (hY : 0 ≤ Y) (hε : 0 ≤ ε) :
    X.re ^ 2 - Y - ε ≤ ‖-X ^ 2 + (Y : ℂ) - (ε : ℂ) * I‖ := by
  have h1 : ‖-X ^ 2‖ - ‖-((Y : ℂ) - (ε : ℂ) * I)‖ ≤ ‖-X ^ 2 + (Y : ℂ) - (ε : ℂ) * I‖ := by
    have := norm_sub_norm_le (-X ^ 2) (-((Y : ℂ) - (ε : ℂ) * I))
    rwa [sub_neg_eq_add, ← add_sub_assoc] at this
  have h2 : ‖-((Y : ℂ) - (ε : ℂ) * I)‖ ≤ Y + ε := by
    rw [norm_neg]
    refine (norm_sub_le _ _).trans ?_
    simp [abs_of_nonneg hY, abs_of_nonneg hε]
  have h3 : X.re ^ 2 ≤ ‖-X ^ 2‖ := by
    rw [norm_neg, norm_pow, Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg X.im]
  linarith

/-- **The denominator on the rectangle** of rotations: `1 + t² ≤ K ‖-(z t + a)² + Y - iε‖`. -/
theorem one_add_sq_le_rect {z : ℂ} (hre : 1 / 2 ≤ z.re) (him : 0 ≤ z.im) {h a ε Y : ℝ}
    (hzh : z.im ≤ h) (hε : 0 < ε) (ha : h * a ^ 2 ≤ ε / 4) (hY : 0 ≤ Y) (t : ℝ) :
    1 + t ^ 2 ≤ (8 + 2 * (1 + 8 * (a ^ 2 + Y + ε)) / ε) *
      ‖-(z * t + a) ^ 2 + (Y : ℂ) - (ε : ℂ) * I‖ := by
  set X : ℂ := z * t + a
  set N := ‖-X ^ 2 + (Y : ℂ) - (ε : ℂ) * I‖
  have hXre : X.re = z.re * t + a := by simp [X]
  have hXim : X.im = z.im * t := by simp [X]
  have hI : 3 * ε / 4 ≤ N := by
    have h1 := neg_im_le_norm (-X ^ 2 + (Y : ℂ) - (ε : ℂ) * I)
    rw [den_im, hXre, hXim] at h1
    have h2 : z.re * t ^ 2 ≥ t ^ 2 / 2 := by nlinarith [sq_nonneg t]
    have h3 : z.im * a ^ 2 ≤ h * a ^ 2 := mul_le_mul_of_nonneg_right hzh (sq_nonneg a)
    have h4 : 0 ≤ z.im * (t + a) ^ 2 := mul_nonneg him (sq_nonneg _)
    have h5 : 0 ≤ z.im * (z.re * t ^ 2 - t ^ 2 / 2) := mul_nonneg him (by linarith)
    nlinarith
  have hR : t ^ 2 / 8 - a ^ 2 - Y - ε ≤ N := by
    have h1 := re_sq_sub_le_norm_den X hY hε.le
    rw [hXre] at h1
    have h2 : (z.re * t) ^ 2 ≥ t ^ 2 / 4 := by
      have hz : 1 / 4 ≤ z.re ^ 2 := by nlinarith
      rw [mul_pow]
      nlinarith [mul_le_mul_of_nonneg_right hz (sq_nonneg t)]
    have h3 : (z.re * t + a) ^ 2 ≥ (z.re * t) ^ 2 / 2 - a ^ 2 := by
      nlinarith [sq_nonneg (z.re * t + 2 * a)]
    linarith
  set K := a ^ 2 + Y + ε
  have hK : 0 ≤ K := by positivity
  have h2N : 1 ≤ 2 * N / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have : (1 + 8 * K) ≤ (1 + 8 * K) * (2 * N / ε) := le_mul_of_one_le_right (by linarith) h2N
  calc 1 + t ^ 2 ≤ 8 * N + (1 + 8 * K) := by linarith
    _ ≤ 8 * N + (1 + 8 * K) * (2 * N / ε) := by linarith
    _ = _ := by ring

/-- **The denominator at the rotation `1 + s i`**: `1 + t² + Y ≤ K ‖-((1 + s i) t + a)² + Y - iε‖`,
with `K` independent of `t` and `Y`. -/
theorem one_add_sq_add_le_rot {s a ε Y : ℝ} (hs : 0 < s) (hε : 0 < ε) (ha : s * a ^ 2 ≤ ε / 4)
    (t : ℝ) :
    1 + t ^ 2 + Y ≤ (1 + 3 / s + 2 * (1 + 2 * a ^ 2) / ε) *
      ‖-((1 + s * I) * t + a) ^ 2 + (Y : ℂ) - (ε : ℂ) * I‖ := by
  set X : ℂ := (1 + s * I) * t + a
  set N := ‖-X ^ 2 + (Y : ℂ) - (ε : ℂ) * I‖
  have hXre : X.re = t + a := by simp [X]
  have hXim : X.im = s * t := by simp [X]
  have hI : s * t ^ 2 + 3 * ε / 4 ≤ N := by
    have h1 := neg_im_le_norm (-X ^ 2 + (Y : ℂ) - (ε : ℂ) * I)
    rw [den_im, hXre, hXim] at h1
    have h4 : 0 ≤ s * (t + a) ^ 2 := mul_nonneg hs.le (sq_nonneg _)
    nlinarith
  have hR : Y - 2 * t ^ 2 - 2 * a ^ 2 ≤ N := by
    have h1 := re_le_norm (-X ^ 2 + (Y : ℂ) - (ε : ℂ) * I)
    rw [den_re, hXre, hXim] at h1
    nlinarith [sq_nonneg (s * t), sq_nonneg (t - a)]
  have h2N : 1 ≤ 2 * N / ε := by
    rw [le_div_iff₀ hε]
    nlinarith [mul_nonneg hs.le (sq_nonneg t)]
  have ht : t ^ 2 ≤ N / s := by
    rw [le_div_iff₀ hs]
    nlinarith [mul_nonneg hs.le (sq_nonneg t)]
  have : (1 + 2 * a ^ 2) ≤ (1 + 2 * a ^ 2) * (2 * N / ε) :=
    le_mul_of_one_le_right (by positivity) h2N
  calc 1 + t ^ 2 + Y ≤ N + 3 * (N / s) + (1 + 2 * a ^ 2) := by linarith
    _ ≤ N + 3 * (N / s) + (1 + 2 * a ^ 2) * (2 * N / ε) := by linarith
    _ = _ := by ring

/-! ### The spatial square -/

theorem norm_le_sqrt_sq3 (y : Fin 3 → ℝ) : ‖y‖ ≤ Real.sqrt (sq3 y) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  exact Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

theorem norm_sq_le_sq3 (y : Fin 3 → ℝ) : ‖y‖ ^ 2 ≤ sq3 y := by
  have h := norm_le_sqrt_sq3 y
  calc ‖y‖ ^ 2 ≤ Real.sqrt (sq3 y) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = sq3 y := Real.sq_sqrt (sq3_nonneg y)

/-! ### Matrix norms -/

section MatrixNorm

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem norm_entry_le (A : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) : ‖A i j‖ ≤ ‖A‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h1 : ‖A i j‖ ≤ ∑ k, ‖A i k‖ :=
    Finset.single_le_sum (f := fun k => ‖A i k‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  have h2 : (∑ k, ‖A i k‖₊) ≤ Finset.univ.sup fun i => ∑ k, ‖A i k‖₊ :=
    Finset.le_sup (f := fun i => ∑ k, ‖A i k‖₊) (Finset.mem_univ i)
  refine h1.trans ?_
  have h3 : ((∑ k, ‖A i k‖₊ : NNReal) : ℝ) ≤ ((Finset.univ.sup fun i => ∑ k, ‖A i k‖₊ : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr h2
  simpa using h3

theorem norm_trace_le (A : Matrix (Fin 4) (Fin 4) ℂ) : ‖A.trace‖ ≤ 4 * ‖A‖ := by
  unfold Matrix.trace Matrix.diag
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖A i i‖ ≤ ∑ _i : Fin 4, ‖A‖ := Finset.sum_le_sum fun i _ => norm_entry_le A i i
    _ = 4 * ‖A‖ := by simp

/-- `‖γ^μ‖ ≤ G`. -/
noncomputable def gammaBound : ℝ := ∑ μ, ‖Dirac.gamma μ‖

theorem norm_gamma_le (μ : Fin 4) : ‖Dirac.gamma μ‖ ≤ gammaBound :=
  Finset.single_le_sum (f := fun μ => ‖Dirac.gamma μ‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ μ)

theorem gammaBound_nonneg : 0 ≤ gammaBound := Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_slashC_le {q : Fin 4 → ℂ} {Q : ℝ} (hq : ∀ ν, ‖q ν‖ ≤ Q) :
    ‖slashC q‖ ≤ 4 * gammaBound * (4 * Q) := by
  have hQ : 0 ≤ Q := (norm_nonneg _).trans (hq 0)
  unfold slashC
  refine (norm_sum_le _ _).trans ?_
  have hc : ∀ μ, ‖∑ ν, (Minkowski.metric μ ν : ℂ) * q ν‖ ≤ 4 * Q := by
    intro μ
    refine (norm_sum_le _ _).trans ?_
    calc ∑ ν, ‖(Minkowski.metric μ ν : ℂ) * q ν‖ ≤ ∑ _ν : Fin 4, Q := by
          refine Finset.sum_le_sum fun ν _ => ?_
          rw [norm_mul]
          have hm : ‖(Minkowski.metric μ ν : ℂ)‖ ≤ 1 := by
            unfold Minkowski.metric
            split_ifs <;> simp
          calc ‖(Minkowski.metric μ ν : ℂ)‖ * ‖q ν‖ ≤ 1 * Q :=
                mul_le_mul hm (hq ν) (norm_nonneg _) zero_le_one
            _ = Q := one_mul Q
      _ = 4 * Q := by simp
  calc ∑ μ, ‖(∑ ν, (Minkowski.metric μ ν : ℂ) * q ν) • Dirac.gamma μ‖
      ≤ ∑ _μ : Fin 4, (4 * Q) * gammaBound := by
        refine Finset.sum_le_sum fun μ _ => ?_
        rw [norm_smul]
        exact mul_le_mul (hc μ) (norm_gamma_le μ) (norm_nonneg _) (by positivity)
    _ = 4 * gammaBound * (4 * Q) := by simp; ring

/-- The numerator bound `‖M - q̸‖ ≤ |M| ‖1‖ + 16 G Q`. -/
theorem norm_numC_le (M : ℝ) {q : Fin 4 → ℂ} {Q : ℝ} (hq : ∀ ν, ‖q ν‖ ≤ Q) :
    ‖numC M q‖ ≤ |M| * ‖(1 : Matrix (Fin 4) (Fin 4) ℂ)‖ + 4 * gammaBound * (4 * Q) := by
  unfold numC
  refine (norm_sub_le _ _).trans (add_le_add ?_ (norm_slashC_le hq))
  rw [norm_smul]
  simp

theorem norm_mk_le (X : ℂ) (y : Fin 3 → ℝ) (ν : Fin 4) : ‖mk X y ν‖ ≤ ‖X‖ + ‖y‖ := by
  refine Fin.cases ?_ (fun i => ?_) ν
  · simp only [mk, Fin.cons_zero]
    linarith [norm_nonneg y]
  · simp only [mk, Fin.cons_succ, norm_real]
    linarith [norm_le_pi_norm y i, norm_nonneg X]

theorem norm_epC_le (M ε : ℝ) (q : Fin 4 → ℂ) :
    ‖epC M ε q‖ ≤ ‖(denC M ε q)⁻¹‖ * ‖numC M q‖ := by
  unfold epC
  exact norm_smul_le _ _

end MatrixNorm

end QED.ChainProof.RepsIntBB

end
