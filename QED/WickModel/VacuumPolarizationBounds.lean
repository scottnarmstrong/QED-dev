/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.ShiftedEnergyIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pauli–Villars cancellations of principal powers

The energy integral of the vacuum polarization loop produces, for each flavor `f`, principal
powers `(-W_f + iε)^{-s}` of the Feynman mass terms `W_f`. A single flavor does not decay fast
enough in the spatial loop momentum to be integrable; the Pauli–Villars sums do. This module
proves the two cancellation bounds, uniformly in `ε > 0`:

* first order (`norm_sum_mul_cpow_le_one`): if `∑ c_f b_f = 0`, then
  `‖∑ c_f b_f (-W_f + iε)^{-s}‖ ≤ s (∑ |c_f b_f| (W_f - W_0)) λ^{-(s+1)}`;
* second order (`norm_sum_cpow_le_two`): if `∑ c_f = 0` and `∑ c_f W_f = 0`, then
  `‖∑ c_f (-W_f + iε)^{-s}‖ ≤ s (s + 1) (∑ |c_f| (W_f - W_0)²) λ^{-(s+2)}`,

where `W_0 ≤ W_f` for every `f` and `λ = max ε W_0`. They follow from the mean value
inequality, applied once to `x ↦ (-x + iε)^{-s}` and once to its first-order Taylor remainder.
The lower bound `λ` uses `‖-x + iε‖ ≥ max ε x`, so the bounds hold whatever the sign of `W_0`.
-/

@[expose] public section

open Complex Set

namespace QED.WickModel

namespace VacuumPolarizationLimit

/-- On `[a, ∞)`, `max ε a ≤ ‖-x + iε‖`. -/
theorem max_le_norm_neg_add_mul_I {ε a x : ℝ} (hε : 0 ≤ ε) (hx : a ≤ x) :
    max ε a ≤ ‖-(x : ℂ) + ε * I‖ := by
  refine max_le ?_ ?_
  · have h := Complex.abs_im_le_norm (-(x : ℂ) + ε * I)
    simp only [add_im, neg_im, ofReal_im, neg_zero, mul_im, ofReal_re, I_im, mul_one, I_re,
      mul_zero, add_zero, zero_add] at h
    rw [abs_of_nonneg hε] at h
    exact h
  · have h := Complex.abs_re_le_norm (-(x : ℂ) + ε * I)
    simp only [add_re, neg_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one,
      sub_self, add_zero] at h
    linarith [neg_abs_le (-x)]

/-- `‖(-x + iε)^{-s}‖ ≤ λ^{-s}` when `0 < λ ≤ ‖-x + iε‖` and `s ≥ 0`. -/
theorem norm_cpow_neg_le {ε x lam s : ℝ} (hlam : 0 < lam) (hle : lam ≤ ‖-(x : ℂ) + ε * I‖)
    (hs : 0 ≤ s) : ‖(-(x : ℂ) + ε * I) ^ (-(s : ℂ))‖ ≤ lam ^ (-s) := by
  rw [show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring, norm_cpow_real]
  exact Real.rpow_le_rpow_of_nonpos hlam hle (by linarith)

/-- For `ε > 0`, `d/dx (-x + iε)^{-s} = s (-x + iε)^{-(s+1)}`. -/
theorem hasDerivAt_cpow_neg {ε : ℝ} (hε : 0 < ε) (s x : ℝ) :
    HasDerivAt (fun x : ℝ => (-(x : ℂ) + ε * I) ^ (-(s : ℂ)))
      ((s : ℂ) * (-(x : ℂ) + ε * I) ^ (-((s + 1 : ℝ) : ℂ))) x := by
  have hmem : -(x : ℂ) + ε * I ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    right
    simp [hε.ne']
  have hφ : HasDerivAt (fun y : ℂ => -y + ε * I) (-1) (x : ℂ) :=
    ((hasDerivAt_id (x : ℂ)).neg).add_const (ε * I)
  have h := ((Complex.hasStrictDerivAt_cpow_const (c := -(s : ℂ)) hmem).hasDerivAt.comp (x : ℂ)
    hφ).comp_ofReal
  refine h.congr_deriv ?_
  rw [show -((s + 1 : ℝ) : ℂ) = -(s : ℂ) - 1 by push_cast; ring]
  ring

/-- **First-order bound.** For `ε > 0`, `a ≤ b` and `s ≥ 0`,
`‖(-b + iε)^{-s} - (-a + iε)^{-s}‖ ≤ s (b - a) (max ε a)^{-(s+1)}`. -/
theorem norm_cpow_sub_cpow_le_of_le {ε a b s : ℝ} (hε : 0 < ε) (hab : a ≤ b) (hs : 0 ≤ s) :
    ‖(-(b : ℂ) + ε * I) ^ (-(s : ℂ)) - (-(a : ℂ) + ε * I) ^ (-(s : ℂ))‖
      ≤ s * (b - a) * (max ε a) ^ (-(s + 1)) := by
  have hlam : 0 < max ε a := lt_max_of_lt_left hε
  have hbound : ∀ x ∈ Icc a b,
      ‖(s : ℂ) * (-(x : ℂ) + ε * I) ^ (-((s + 1 : ℝ) : ℂ))‖ ≤ s * (max ε a) ^ (-(s + 1)) := by
    intro x hx
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
    gcongr
    exact norm_cpow_neg_le hlam (max_le_norm_neg_add_mul_I hε.le hx.1) (by linarith)
  have key := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hasDerivAt_cpow_neg hε s x).hasDerivWithinAt) hbound (left_mem_Icc.2 hab)
    (right_mem_Icc.2 hab)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)] at key
  calc _ ≤ s * (max ε a) ^ (-(s + 1)) * (b - a) := key
    _ = _ := by ring

/-- **Second-order bound.** For `ε > 0`, `a ≤ b` and `s ≥ 0`, the first-order Taylor remainder
of `x ↦ (-x + iε)^{-s}` at `a` is bounded by `s (s + 1) (b - a)² (max ε a)^{-(s+2)}`. -/
theorem norm_cpow_sub_cpow_sub_le {ε a b s : ℝ} (hε : 0 < ε) (hab : a ≤ b) (hs : 0 ≤ s) :
    ‖(-(b : ℂ) + ε * I) ^ (-(s : ℂ)) - (-(a : ℂ) + ε * I) ^ (-(s : ℂ))
        - (s : ℂ) * (-(a : ℂ) + ε * I) ^ (-((s + 1 : ℝ) : ℂ)) * ((b - a : ℝ) : ℂ)‖
      ≤ s * (s + 1) * (b - a) ^ 2 * (max ε a) ^ (-(s + 2)) := by
  set g' : ℂ := (s : ℂ) * (-(a : ℂ) + ε * I) ^ (-((s + 1 : ℝ) : ℂ)) with hg'
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (-(x : ℂ) + ε * I) ^ (-(s : ℂ)) - g' * x)
      ((s : ℂ) * (-(x : ℂ) + ε * I) ^ (-((s + 1 : ℝ) : ℂ)) - g') x := by
    intro x
    have h2 : HasDerivAt (fun x : ℝ => g' * (x : ℂ)) g' x := by
      have := ((hasDerivAt_id x).ofReal_comp).const_mul g'
      simpa using this
    exact (hasDerivAt_cpow_neg hε s x).sub h2
  have hbound : ∀ x ∈ Icc a b,
      ‖(s : ℂ) * (-(x : ℂ) + ε * I) ^ (-((s + 1 : ℝ) : ℂ)) - g'‖
        ≤ s * (s + 1) * (b - a) * (max ε a) ^ (-(s + 2)) := by
    intro x hx
    have h1 := norm_cpow_sub_cpow_le_of_le hε hx.1 (by linarith : 0 ≤ s + 1)
    rw [show -(s + 1 + 1) = -(s + 2) by ring] at h1
    have hsplit : (s : ℂ) * (-(x : ℂ) + ε * I) ^ (-((s + 1 : ℝ) : ℂ)) - g'
        = (s : ℂ) * ((-(x : ℂ) + ε * I) ^ (-((s + 1 : ℝ) : ℂ))
          - (-(a : ℂ) + ε * I) ^ (-((s + 1 : ℝ) : ℂ))) := by
      rw [hg']
      ring
    have hlam : 0 < max ε a := lt_max_of_lt_left hε
    rw [hsplit, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
    calc s * ‖(-(x : ℂ) + ε * I) ^ (-((s + 1 : ℝ) : ℂ))
          - (-(a : ℂ) + ε * I) ^ (-((s + 1 : ℝ) : ℂ))‖
        ≤ s * ((s + 1) * (x - a) * (max ε a) ^ (-(s + 2))) := by gcongr
      _ ≤ s * ((s + 1) * (b - a) * (max ε a) ^ (-(s + 2))) := by
          gcongr
          exact hx.2
      _ = _ := by ring
  have key := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hderiv x).hasDerivWithinAt) hbound (left_mem_Icc.2 hab) (right_mem_Icc.2 hab)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)] at key
  have hrw : (-(b : ℂ) + ε * I) ^ (-(s : ℂ)) - (-(a : ℂ) + ε * I) ^ (-(s : ℂ))
        - g' * ((b - a : ℝ) : ℂ)
      = ((-(b : ℂ) + ε * I) ^ (-(s : ℂ)) - g' * b)
        - ((-(a : ℂ) + ε * I) ^ (-(s : ℂ)) - g' * a) := by
    push_cast
    ring
  rw [hrw]
  calc _ ≤ s * (s + 1) * (b - a) * (max ε a) ^ (-(s + 2)) * (b - a) := key
    _ = _ := by ring

/-- **First-order Pauli–Villars cancellation.** If `∑ c_f b_f = 0` and `W_0 ≤ W_f`, then
`‖∑ c_f b_f (-W_f + iε)^{-s}‖ ≤ s (∑ |c_f b_f| (W_f - W_0)) (max ε W_0)^{-(s+1)}`. -/
theorem norm_sum_mul_cpow_le_one {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) {c b W : Fin 3 → ℝ}
    (hcb : ∑ f, c f * b f = 0) (hW : ∀ f, W 0 ≤ W f) :
    ‖∑ f, ((c f * b f : ℝ) : ℂ) * (-(W f : ℂ) + ε * I) ^ (-(s : ℂ))‖
      ≤ s * (∑ f, |c f * b f| * (W f - W 0)) * (max ε (W 0)) ^ (-(s + 1)) := by
  set Z : Fin 3 → ℂ := fun f => (-(W f : ℂ) + ε * I) ^ (-(s : ℂ)) with hZ
  have hcb' : ((c 0 * b 0 : ℝ) : ℂ) + ((c 1 * b 1 : ℝ) : ℂ) + ((c 2 * b 2 : ℝ) : ℂ) = 0 := by
    rw [Fin.sum_univ_three] at hcb
    exact_mod_cast hcb
  have hrw : ∑ f, ((c f * b f : ℝ) : ℂ) * Z f = ∑ f, ((c f * b f : ℝ) : ℂ) * (Z f - Z 0) := by
    simp only [Fin.sum_univ_three]
    linear_combination Z 0 * hcb'
  change ‖∑ f, ((c f * b f : ℝ) : ℂ) * Z f‖ ≤ _
  rw [hrw, Finset.mul_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun f _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |c f * b f| * ‖Z f - Z 0‖
      ≤ |c f * b f| * (s * (W f - W 0) * (max ε (W 0)) ^ (-(s + 1))) := by
        gcongr
        exact norm_cpow_sub_cpow_le_of_le hε (hW f) hs
    _ = _ := by ring

/-- **Second-order Pauli–Villars cancellation.** If `∑ c_f = 0`, `∑ c_f W_f = 0` and
`W_0 ≤ W_f`, then
`‖∑ c_f (-W_f + iε)^{-s}‖ ≤ s (s + 1) (∑ |c_f| (W_f - W_0)²) (max ε W_0)^{-(s+2)}`. -/
theorem norm_sum_cpow_le_two {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) {c W : Fin 3 → ℝ}
    (hc : ∑ f, c f = 0) (hcW : ∑ f, c f * W f = 0) (hW : ∀ f, W 0 ≤ W f) :
    ‖∑ f, (c f : ℂ) * (-(W f : ℂ) + ε * I) ^ (-(s : ℂ))‖
      ≤ s * (s + 1) * (∑ f, |c f| * (W f - W 0) ^ 2) * (max ε (W 0)) ^ (-(s + 2)) := by
  set Z : Fin 3 → ℂ := fun f => (-(W f : ℂ) + ε * I) ^ (-(s : ℂ)) with hZ
  set g' : ℂ := (s : ℂ) * (-(W 0 : ℂ) + ε * I) ^ (-((s + 1 : ℝ) : ℂ)) with hg'
  have hc' : (c 0 : ℂ) + c 1 + c 2 = 0 := by
    rw [Fin.sum_univ_three] at hc
    exact_mod_cast hc
  have hcW' : (c 0 : ℂ) * W 0 + c 1 * W 1 + c 2 * W 2 = 0 := by
    rw [Fin.sum_univ_three] at hcW
    exact_mod_cast hcW
  have hrw : ∑ f, (c f : ℂ) * Z f
      = ∑ f, (c f : ℂ) * (Z f - Z 0 - g' * ((W f - W 0 : ℝ) : ℂ)) := by
    simp only [Fin.sum_univ_three]
    push_cast
    linear_combination (Z 0 - g' * W 0) * hc' + g' * hcW'
  change ‖∑ f, (c f : ℂ) * Z f‖ ≤ _
  rw [hrw, Finset.mul_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun f _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |c f| * ‖Z f - Z 0 - g' * ((W f - W 0 : ℝ) : ℂ)‖
      ≤ |c f| * (s * (s + 1) * (W f - W 0) ^ 2 * (max ε (W 0)) ^ (-(s + 2))) := by
        gcongr
        exact norm_cpow_sub_cpow_sub_le hε (hW f) hs
    _ = _ := by ring

end VacuumPolarizationLimit

end QED.WickModel

end
