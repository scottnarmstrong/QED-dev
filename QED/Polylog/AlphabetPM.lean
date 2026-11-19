/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The arguments of the alphabet `{u, 1 - u, 1 + u}`

For `0 < u < 1`, the data the polylogarithmic chain rule needs at each argument `f` built from
the letters `u, 1 - u, 1 + u, 2` (`QED.Polylog.hasDerivAt_Li_four_sub_of` and its companions):
the derivative `f'`, the bound `0 < |f| < 1`, the logarithmic derivative `f'/f` as a combination
of `1/u, 1/(1-u), 1/(1+u)`, and `log f`, `log (1 - f)` as combinations of
`log u, log (1 - u), log (1 + u), log 2`.

The arguments are `u, -u, 1 - u, 1/(1+u), u/(1+u), t, -t, (1+u)/2, (1-u)/2, 2u/(1+u), u², 1 - u²,
t²`, where `t = (1 - u)/(1 + u)`; names are in `QED.Polylog.PM`.
-/

public section

open Real

namespace QED.Polylog.PM

variable {u : ℝ}

/-- The data of the argument `x`. -/
theorem data_id (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt (fun x : ℝ => x) (1) u ∧
      |u| < 1 ∧ u ≠ 0 ∧
      (1) / (u) = 1 / u ∧
      log (u) = log u ∧
      log (1 - (u)) = log (1 - u) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hasDerivAt_id' u
  · exact abs_lt.2 ⟨by linarith, h1⟩
  · exact h0.ne'
  · rw [one_div]
  · exact rfl
  · exact rfl

/-- The data of the argument `-x`. -/
theorem data_neg (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt (fun x : ℝ => -x) (-1) u ∧
      |-u| < 1 ∧ -u ≠ 0 ∧
      (-1) / (-u) = 1 / u ∧
      log (-u) = log u ∧
      log (1 - (-u)) = log (1 + u) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hasDerivAt_id' u).neg
  · exact abs_lt.2 ⟨by linarith, by linarith⟩
  · exact (neg_neg_of_pos h0).ne
  · field_simp
  · exact Real.log_neg_eq_log u
  · rw [sub_neg_eq_add]

/-- The data of the argument `1 - x`. -/
theorem data_oneSub (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt (fun x : ℝ => 1 - x) (-1) u ∧
      |1 - u| < 1 ∧ 1 - u ≠ 0 ∧
      (-1) / (1 - u) = -(1 / (1 - u)) ∧
      log (1 - u) = log (1 - u) ∧
      log (1 - (1 - u)) = log u := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using (hasDerivAt_id' u).const_sub 1
  · exact abs_lt.2 ⟨by linarith, by linarith⟩
  · linarith
  · rw [neg_div, one_div]
  · exact rfl
  · rw [sub_sub_cancel]

/-- The data of the argument `1 / (1 + x)`. -/
theorem data_invOneAdd (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt (fun x : ℝ => 1 / (1 + x)) (-1 / (1 + u) ^ 2) u ∧
      |1 / (1 + u)| < 1 ∧ 1 / (1 + u) ≠ 0 ∧
      (-1 / (1 + u) ^ 2) / (1 / (1 + u)) = -(1 / (1 + u)) ∧
      log (1 / (1 + u)) = -log (1 + u) ∧
      log (1 - (1 / (1 + u))) = log u - log (1 + u) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := (hasDerivAt_const u (1 : ℝ)).div ((hasDerivAt_id' u).const_add 1) (by linarith)
    refine this.congr_deriv ?_
    field_simp
    ring
  · rw [abs_lt]; constructor
    · have : 0 < 1 / (1 + u) := by positivity
      linarith
    · rw [div_lt_one (by linarith)]; linarith
  · positivity
  · field_simp
  · rw [one_div, Real.log_inv]
  · rw [show 1 - 1 / (1 + u) = u / (1 + u) by field_simp; ring, log_div h0.ne' (by linarith)]

/-- The data of the argument `x / (1 + x)`. -/
theorem data_divOneAdd (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt (fun x : ℝ => x / (1 + x)) (1 / (1 + u) ^ 2) u ∧
      |u / (1 + u)| < 1 ∧ u / (1 + u) ≠ 0 ∧
      (1 / (1 + u) ^ 2) / (u / (1 + u)) = 1 / u - 1 / (1 + u) ∧
      log (u / (1 + u)) = log u - log (1 + u) ∧
      log (1 - (u / (1 + u))) = -log (1 + u) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := (hasDerivAt_id' u).div ((hasDerivAt_id' u).const_add 1) (by linarith)
    refine this.congr_deriv ?_
    field_simp
    ring
  · rw [abs_lt]; constructor
    · have : 0 < u / (1 + u) := by positivity
      linarith
    · rw [div_lt_one (by linarith)]; linarith
  · positivity
  · field_simp; ring
  · exact log_div h0.ne' (by linarith)
  · rw [show 1 - u / (1 + u) = (1 + u)⁻¹ by field_simp; ring, Real.log_inv]

/-- The data of the argument `(1 - x) / (1 + x)`. -/
theorem data_ksT (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt (fun x : ℝ => (1 - x) / (1 + x)) (-2 / (1 + u) ^ 2) u ∧
      |(1 - u) / (1 + u)| < 1 ∧ (1 - u) / (1 + u) ≠ 0 ∧
      (-2 / (1 + u) ^ 2) / ((1 - u) / (1 + u)) = -(1 / (1 - u)) - 1 / (1 + u) ∧
      log ((1 - u) / (1 + u)) = log (1 - u) - log (1 + u) ∧
      log (1 - ((1 - u) / (1 + u))) = log 2 + log u - log (1 + u) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := ((hasDerivAt_id' u).const_sub 1).div ((hasDerivAt_id' u).const_add 1)
      (by linarith)
    refine this.congr_deriv ?_
    field_simp
    ring
  · rw [abs_lt]; constructor
    · have : 0 < (1 - u) / (1 + u) := div_pos (by linarith) (by linarith)
      linarith
    · rw [div_lt_one (by linarith)]; linarith
  · exact (div_pos (by linarith) (by linarith)).ne'
  · have : 1 - u ≠ 0 := by linarith
    field_simp
    ring
  · exact log_div (by linarith) (by linarith)
  · rw [show 1 - (1 - u) / (1 + u) = 2 * u / (1 + u) by field_simp; ring,
      log_div (by positivity) (by linarith), log_mul (by norm_num) h0.ne']

/-- The data of the argument `-((1 - x) / (1 + x))`. -/
theorem data_negKsT (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt (fun x : ℝ => -((1 - x) / (1 + x))) (2 / (1 + u) ^ 2) u ∧
      |-((1 - u) / (1 + u))| < 1 ∧ -((1 - u) / (1 + u)) ≠ 0 ∧
      (2 / (1 + u) ^ 2) / (-((1 - u) / (1 + u))) = -(1 / (1 - u)) - 1 / (1 + u) ∧
      log (-((1 - u) / (1 + u))) = log (1 - u) - log (1 + u) ∧
      log (1 - (-((1 - u) / (1 + u)))) = log 2 - log (1 + u) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := (((hasDerivAt_id' u).const_sub 1).div ((hasDerivAt_id' u).const_add 1)
      (by linarith)).neg
    refine this.congr_deriv ?_
    field_simp
    ring
  · rw [abs_neg, abs_lt]; constructor
    · have : 0 < (1 - u) / (1 + u) := div_pos (by linarith) (by linarith)
      linarith
    · rw [div_lt_one (by linarith)]; linarith
  · exact (neg_neg_of_pos (div_pos (by linarith) (by linarith))).ne
  · have : 1 - u ≠ 0 := by linarith
    field_simp
    ring
  · rw [Real.log_neg_eq_log, log_div (by linarith) (by linarith)]
  · rw [show 1 - -((1 - u) / (1 + u)) = 2 / (1 + u) by field_simp; ring,
      log_div (by norm_num) (by linarith)]

/-- The data of the argument `(1 + x) / 2`. -/
theorem data_halfOneAdd (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt (fun x : ℝ => (1 + x) / 2) (1 / 2) u ∧
      |(1 + u) / 2| < 1 ∧ (1 + u) / 2 ≠ 0 ∧
      (1 / 2) / ((1 + u) / 2) = 1 / (1 + u) ∧
      log ((1 + u) / 2) = log (1 + u) - log 2 ∧
      log (1 - ((1 + u) / 2)) = log (1 - u) - log 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using ((hasDerivAt_id' u).const_add 1).div_const 2
  · exact abs_lt.2 ⟨by linarith, by linarith⟩
  · positivity
  · field_simp
  · exact log_div (by linarith) (by norm_num)
  · rw [show 1 - (1 + u) / 2 = (1 - u) / 2 by ring, log_div (by linarith) (by norm_num)]

/-- The data of the argument `(1 - x) / 2`. -/
theorem data_halfOneSub (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt (fun x : ℝ => (1 - x) / 2) (-1 / 2) u ∧
      |(1 - u) / 2| < 1 ∧ (1 - u) / 2 ≠ 0 ∧
      (-1 / 2) / ((1 - u) / 2) = -(1 / (1 - u)) ∧
      log ((1 - u) / 2) = log (1 - u) - log 2 ∧
      log (1 - ((1 - u) / 2)) = log (1 + u) - log 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using ((hasDerivAt_id' u).const_sub 1).div_const 2
  · exact abs_lt.2 ⟨by linarith, by linarith⟩
  · exact (div_pos (by linarith) (by norm_num)).ne'
  · have : 1 - u ≠ 0 := by linarith
    field_simp
  · exact log_div (by linarith) (by norm_num)
  · rw [show 1 - (1 - u) / 2 = (1 + u) / 2 by ring, log_div (by linarith) (by norm_num)]

/-- The data of the argument `2 * x / (1 + x)`. -/
theorem data_twoMulDiv (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt (fun x : ℝ => 2 * x / (1 + x)) (2 / (1 + u) ^ 2) u ∧
      |2 * u / (1 + u)| < 1 ∧ 2 * u / (1 + u) ≠ 0 ∧
      (2 / (1 + u) ^ 2) / (2 * u / (1 + u)) = 1 / u - 1 / (1 + u) ∧
      log (2 * u / (1 + u)) = log 2 + log u - log (1 + u) ∧
      log (1 - (2 * u / (1 + u))) = log (1 - u) - log (1 + u) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := ((hasDerivAt_id' u).const_mul 2).div ((hasDerivAt_id' u).const_add 1)
      (by linarith)
    refine this.congr_deriv ?_
    field_simp
    ring
  · rw [abs_lt]; constructor
    · have : 0 < 2 * u / (1 + u) := by positivity
      linarith
    · rw [div_lt_one (by linarith)]; linarith
  · positivity
  · field_simp; ring
  · rw [log_div (by positivity) (by linarith), log_mul (by norm_num) h0.ne']
  · rw [show 1 - 2 * u / (1 + u) = (1 - u) / (1 + u) by field_simp; ring,
      log_div (by linarith) (by linarith)]

/-- The data of the argument `x ^ 2`. -/
theorem data_sq (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u ∧
      |u ^ 2| < 1 ∧ u ^ 2 ≠ 0 ∧
      (2 * u) / (u ^ 2) = 2 * (1 / u) ∧
      log (u ^ 2) = 2 * log u ∧
      log (1 - (u ^ 2)) = log (1 - u) + log (1 + u) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hasDerivAt_pow 2 u
  · rw [abs_of_pos (by positivity)]; nlinarith
  · positivity
  · field_simp
  · rw [log_pow]; push_cast; ring
  · rw [show 1 - u ^ 2 = (1 - u) * (1 + u) by ring, log_mul (by linarith) (by linarith)]


/-- The data of the argument `1 - x ^ 2`. -/
theorem data_oneSubSq (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * u)) u ∧
      |1 - u ^ 2| < 1 ∧ 1 - u ^ 2 ≠ 0 ∧
      (-(2 * u)) / (1 - u ^ 2) = -(1 / (1 - u)) + 1 / (1 + u) ∧
      log (1 - u ^ 2) = log (1 - u) + log (1 + u) ∧
      log (1 - (1 - u ^ 2)) = 2 * log u := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using (hasDerivAt_pow 2 u).const_sub 1
  · rw [abs_of_pos (by nlinarith)]; nlinarith
  · nlinarith
  · have : 1 - u ^ 2 ≠ 0 := by nlinarith
    have : 1 - u ≠ 0 := by linarith
    have : 1 + u ≠ 0 := by linarith
    field_simp
    ring
  · rw [show 1 - u ^ 2 = (1 - u) * (1 + u) by ring, log_mul (by linarith) (by linarith)]

  · rw [sub_sub_cancel, log_pow]; push_cast; ring

/-- The data of the argument `((1 - x) / (1 + x)) ^ 2`. -/
theorem data_ksTSq (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt (fun x : ℝ => ((1 - x) / (1 + x)) ^ 2)
        (2 * ((1 - u) / (1 + u)) * (-2 / (1 + u) ^ 2)) u ∧
      |((1 - u) / (1 + u)) ^ 2| < 1 ∧ ((1 - u) / (1 + u)) ^ 2 ≠ 0 ∧
      (2 * ((1 - u) / (1 + u)) * (-2 / (1 + u) ^ 2)) / (((1 - u) / (1 + u)) ^ 2) =
        -2 * (1 / (1 - u)) - 2 * (1 / (1 + u)) ∧
      log (((1 - u) / (1 + u)) ^ 2) = 2 * (log (1 - u) - log (1 + u)) ∧
      log (1 - (((1 - u) / (1 + u)) ^ 2)) = 2 * log 2 + log u - 2 * log (1 + u) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := (data_ksT h0 h1).1.pow 2
    refine this.congr_deriv ?_
    push_cast
    ring
  · have h2 : 0 < (1 - u) / (1 + u) := div_pos (by linarith) (by linarith)
    have h3 : (1 - u) / (1 + u) < 1 := by rw [div_lt_one (by linarith)]; linarith
    rw [abs_of_pos (by positivity)]; nlinarith
  · exact pow_ne_zero 2 (div_pos (by linarith) (by linarith)).ne'
  · have : 1 - u ≠ 0 := by linarith
    field_simp
    ring
  · rw [log_pow, log_div (by linarith) (by linarith)]; push_cast; ring
  · rw [show 1 - ((1 - u) / (1 + u)) ^ 2 = 2 ^ 2 * u / (1 + u) ^ 2 by field_simp; ring,
      log_div (by positivity) (by positivity), log_mul (by positivity) h0.ne', log_pow,
      log_pow]
    push_cast
    ring

end QED.Polylog.PM
