/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.SetAW1
import QED.Polylog.AlphabetPM
import QED.Polylog.ExtraIntegrals
import QED.Polylog.LiCalculus
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Set (a): endpoint limits of the rational-coefficient part

Helper analysis for the sixth-order set (a) of `docs/HIGHER-LOOP-PLAN.md`. It is **not** frozen.

The coefficients of `QED.Chain.setAG1` have poles of order two at `u = 0`. Writing
`log (1 - u) = -u - u²/2 + u³ R₁`, `log (1 + u) = u - u²/2 + u³ R₂`, `Li 2 u = u R₃` and
`Li 2 (-u) = -u R₄` with `|Rᵢ| ≤ 3` on `(0, 1/2)`, every pole cancels: `G₁` is a constant-term
coefficient continuous at `0` plus terms `d(u) · u logʲ u · (product of the Rᵢ)` with `d`
continuous at `0` and `j ≤ 2`. At `u = 1` every coefficient of a monomial containing `log (1 - u)`
vanishes, so those terms carry the factor `(1 - u) log (1 - u)`.

## Main statements

* `QED.Chain.tendsto_setAG1_zero`: `G₁(0⁺) = -4619/432`.
* `QED.Chain.tendsto_setAG1_one`: `G₁(1⁻) = -41π²/81 - 1927/432 + π² log 2/3`.
-/

@[expose] public section

open Real Set Filter Topology QED.Polylog

namespace QED.Chain

namespace SetAW1

private theorem tlim {l : Filter ℝ} {x₀ : ℝ} (hl : l ≤ 𝓝 x₀) {g : ℝ → ℝ} {a : ℝ}
    (hg : ContinuousAt g x₀) (h : g x₀ = a) : Tendsto g l (𝓝 a) :=
  h ▸ hg.tendsto.mono_left hl

private theorem tendsto_mul_bdd {f g : ℝ → ℝ} {l : Filter ℝ} {C : ℝ} (hf : Tendsto f l (𝓝 0))
    (hg : ∀ᶠ x in l, |g x| ≤ C) : Tendsto (fun x => f x * g x) l (𝓝 0) :=
  hf.zero_mul_isBoundedUnder_le
    (isBoundedUnder_of_eventually_le (a := C) (hg.mono fun x h => by simpa using h))

private theorem tendsto_mul_zero_of_tendsto {f g : ℝ → ℝ} {l : Filter ℝ} {a : ℝ}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => f x * g x) l (𝓝 0) := by
  simpa using hf.mul hg

private theorem abs_mul_le_three {a b C : ℝ} (ha : |a| ≤ C) (hb : |b| ≤ 3) :
    |a * b| ≤ C * 3 := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

/-- `R₁(x) = (log (1 - x) + x + x²/2)/x³`. -/
noncomputable def remL1 (x : ℝ) : ℝ := (log (1 - x) + x + x ^ 2 / 2) / x ^ 3

/-- `R₂(x) = (log (1 + x) - x + x²/2)/x³`. -/
noncomputable def remLm (x : ℝ) : ℝ := (log (1 + x) - x + x ^ 2 / 2) / x ^ 3

/-- `R₃(x) = Li 2 x / x`. -/
noncomputable def remP (x : ℝ) : ℝ := Li 2 x / x

/-- `R₄(x) = -Li 2 (-x) / x`. -/
noncomputable def remM (x : ℝ) : ℝ := -Li 2 (-x) / x

private theorem cube_div_le {x : ℝ} (h0 : 0 < x) (h1 : x < 1 / 2) :
    x ^ 3 / (1 - x) ≤ 3 * x ^ 3 := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith [pow_pos h0 3]

theorem abs_remL1_le {x : ℝ} (h0 : 0 < x) (h1 : x < 1 / 2) : |remL1 x| ≤ 3 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |x| < 1 by rw [abs_of_pos h0]; linarith) 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_of_pos h0] at h
  norm_num at h
  have hx3 : 0 < x ^ 3 := pow_pos h0 3
  rw [remL1, abs_div, abs_of_pos hx3, div_le_iff₀ hx3,
    show log (1 - x) + x + x ^ 2 / 2 = x + x ^ 2 / 2 + log (1 - x) by ring]
  linarith [cube_div_le h0 h1]

theorem abs_remLm_le {x : ℝ} (h0 : 0 < x) (h1 : x < 1 / 2) : |remLm x| ≤ 3 := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |-x| < 1 by rw [abs_neg, abs_of_pos h0]; linarith) 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, abs_of_pos h0] at h
  norm_num at h
  have hx3 : 0 < x ^ 3 := pow_pos h0 3
  rw [remLm, abs_div, abs_of_pos hx3, div_le_iff₀ hx3,
    show log (1 + x) - x + x ^ 2 / 2 = -x + x ^ 2 / 2 + log (1 + x) by ring]
  linarith [cube_div_le h0 h1]

private theorem pi_sq_div_six_le : π ^ 2 / 6 ≤ 3 := by
  have := Real.pi_le_four
  have := Real.pi_pos
  nlinarith

theorem abs_remP_le {x : ℝ} (h0 : 0 < x) (h1 : x < 1 / 2) : |remP x| ≤ 3 := by
  have h := abs_Li_le (k := 2) le_rfl (y := x) (by rw [abs_of_pos h0]; linarith)
  rw [remP, abs_div, abs_of_pos h0, div_le_iff₀ h0]
  rw [abs_of_pos h0] at h
  nlinarith [pi_sq_div_six_le]

theorem abs_remM_le {x : ℝ} (h0 : 0 < x) (h1 : x < 1 / 2) : |remM x| ≤ 3 := by
  have h := abs_Li_le (k := 2) le_rfl (y := -x) (by rw [abs_neg, abs_of_pos h0]; linarith)
  rw [remM, abs_div, abs_neg, abs_of_pos h0, div_le_iff₀ h0]
  rw [abs_neg, abs_of_pos h0] at h
  nlinarith [pi_sq_div_six_le]

/-- `h21000 / (1 - x)`. -/
noncomputable def q21000 (x : ℝ) : ℝ :=
  (-38 - 104 * x - 92 * x ^ 2 - 24 * x ^ 3 - 6 * x ^ 4) / (9 * (1 + x) ^ 3)

/-- `h11100 / (1 - x)`. -/
noncomputable def q11100 (x : ℝ) : ℝ :=
  (-2 - 6 * x - 12 * x ^ 2 + 12 * x ^ 3 + 6 * x ^ 4 + 2 * x ^ 5) / (3 * x ^ 2 * (1 + x) ^ 2)

/-- `h11000 / (1 - x)`. -/
noncomputable def q11000 (x : ℝ) : ℝ :=
  (8 - 43 * x - 159 * x ^ 2 - 213 * x ^ 3 - 153 * x ^ 4 - 68 * x ^ 5 - 12 * x ^ 6) / (12 * x * (1
      + x) ^ 4)

/-- `h01100 / (1 - x)`. -/
noncomputable def q01100 (x : ℝ) : ℝ :=
  (3 + 6 * x + 22 * x ^ 2 + 6 * x ^ 3 + 3 * x ^ 4) / (3 * x ^ 2 * (1 + x))

/-- `h01000 / (1 - x)`. -/
noncomputable def q01000 (x : ℝ) : ℝ :=
  (-9 - x + 10 * x ^ 2 - x ^ 3 - 9 * x ^ 4) / (9 * x * (1 + x) ^ 3)


/-- Coefficient `21000` of `G₁` near `0`, divided by `x`. -/
noncomputable def d21000 (x : ℝ) : ℝ :=
  (-(38 * x ^ 2) - 66 * x ^ 3 + 12 * x ^ 4 + 68 * x ^ 5 + 18 * x ^ 6 + 6 * x ^ 7) / (9 * (1
      + x) ^ 3)

/-- Coefficient `20100` of `G₁` near `0`, divided by `x`. -/
noncomputable def d20100 (x : ℝ) : ℝ :=
  (-(44 * x ^ 2) - 108 * x ^ 3 - 69 * x ^ 4 + 9 * x ^ 5 + 9 * x ^ 6 + 3 * x ^ 7) / (9 * (1 + x) ^ 3)

/-- Coefficient `20000` of `G₁` near `0`, divided by `x`. -/
noncomputable def d20000 (x : ℝ) : ℝ :=
  (-24 - 132 * x - 272 * x ^ 2 - 408 * x ^ 3 - 366 * x ^ 4 - 99 * x ^ 5 - 27 * x ^ 6) / (54 * (1
      + x) ^ 3)

/-- Coefficient `11100` of `G₁` near `0`, divided by `x`. -/
noncomputable def d11100 (x : ℝ) : ℝ :=
  (-(2 * x ^ 3) - 4 * x ^ 4 - 6 * x ^ 5 + 24 * x ^ 6 - 6 * x ^ 7 - 4 * x ^ 8 - 2 * x ^ 9) / (3 *
      (1 + x) ^ 2)

/-- Coefficient `11000` of `G₁` near `0`, divided by `x`. -/
noncomputable def d11000 (x : ℝ) : ℝ :=
  (-(79 * x ^ 2) - 164 * x ^ 3 + 10 * x ^ 4 + 188 * x ^ 5 + 45 * x ^ 6 - 24 * x ^ 7 + 12 * x ^ 8
      + 8 * x ^ 9 + 4 * x ^ 10) / (12 * (1 + x) ^ 4)

/-- Coefficient `10200` of `G₁` near `0`, divided by `x`. -/
noncomputable def d10200 (x : ℝ) : ℝ :=
  (-(x ^ 3) - 2 * x ^ 4 - x ^ 5 + 16 * x ^ 6 - x ^ 7 - 2 * x ^ 8 - x ^ 9) / (3 * (1 + x) ^ 2)

/-- Coefficient `10100` of `G₁` near `0`, divided by `x`. -/
noncomputable def d10100 (x : ℝ) : ℝ :=
  (-(55 * x ^ 2) + 1292 * x ^ 3 + 4350 * x ^ 4 + 4316 * x ^ 5 + 1169 * x ^ 6 + 432 * x ^ 7 + 720
      * x ^ 8 + 288 * x ^ 9 + 72 * x ^ 10) / (108 * (1 + x) ^ 4)

/-- Coefficient `10010` of `G₁` near `0`, divided by `x`. -/
noncomputable def d10010 (x : ℝ) : ℝ :=
  (-176 - 432 * x - 276 * x ^ 2 + 36 * x ^ 3 + 36 * x ^ 4 + 12 * x ^ 5) / (9 * (1 + x) ^ 3)

/-- Coefficient `10001` of `G₁` near `0`, divided by `x`. -/
noncomputable def d10001 (x : ℝ) : ℝ :=
  (88 + 216 * x + 138 * x ^ 2 - 18 * x ^ 3 - 18 * x ^ 4 - 6 * x ^ 5) / (9 * (1 + x) ^ 3)

/-- Coefficient `10000` of `G₁` near `0`, divided by `x`. -/
noncomputable def d10000 (x : ℝ) : ℝ :=
  (1200 + 4431 * x + 5172 * x ^ 2 - 146 * x ^ 3 - 3796 * x ^ 4 - 1349 * x ^ 5 - 72 * x ^ 6 - 360
      * x ^ 7 - 144 * x ^ 8 - 54 * x ^ 9) / (216 * (1 + x) ^ 4)

/-- Coefficient `01100` of `G₁` near `0`, divided by `x`. -/
noncomputable def d01100 (x : ℝ) : ℝ :=
  (3 * x ^ 3 + 3 * x ^ 4 + 16 * x ^ 5 - 16 * x ^ 6 - 3 * x ^ 7 - 3 * x ^ 8) / (3 * (1 + x))

/-- Coefficient `01000` of `G₁` near `0`, divided by `x`. -/
noncomputable def d01000 (x : ℝ) : ℝ :=
  (61 * x ^ 2 + 145 * x ^ 3 + 17 * x ^ 4 - 187 * x ^ 5 - 75 * x ^ 6 + 21 * x ^ 7 + 9 * x ^ 8 + 9
      * x ^ 9) / (18 * (1 + x) ^ 3)

/-- Coefficient `00200` of `G₁` near `0`, divided by `x`. -/
noncomputable def d00200 (x : ℝ) : ℝ :=
  (3 * x ^ 3 + 3 * x ^ 4 + 16 * x ^ 5 - 16 * x ^ 6 - 3 * x ^ 7 - 3 * x ^ 8) / (6 * (1 + x))

/-- Coefficient `00110` of `G₁` near `0`, divided by `x`. -/
noncomputable def d00110 (x : ℝ) : ℝ :=
  (-(4 * x) - 8 * x ^ 2 - 4 * x ^ 3 + 64 * x ^ 4 - 4 * x ^ 5 - 8 * x ^ 6 - 4 * x ^ 7) / (3 * (1
      + x) ^ 2)

/-- Coefficient `00101` of `G₁` near `0`, divided by `x`. -/
noncomputable def d00101 (x : ℝ) : ℝ :=
  (2 * x + 4 * x ^ 2 + 2 * x ^ 3 - 32 * x ^ 4 + 2 * x ^ 5 + 4 * x ^ 6 + 2 * x ^ 7) / (3 * (1
      + x) ^ 2)

/-- Coefficient `00100` of `G₁` near `0`, divided by `x`. -/
noncomputable def d00100 (x : ℝ) : ℝ :=
  (-9 - 195 * x - 775 * x ^ 2 - 757 * x ^ 3 - 59 * x ^ 4 + 247 * x ^ 5 + 651 * x ^ 6 + 609
      * x ^ 7 + 216 * x ^ 8 + 72 * x ^ 9) / (72 * (1 + x) ^ 3)

/-- Coefficient `00010` of `G₁` near `0`, divided by `x`. -/
noncomputable def d00010 (x : ℝ) : ℝ :=
  (-237 - 196 * x + 850 * x ^ 2 + 1148 * x ^ 3 - 213 * x ^ 4 - 528 * x ^ 5 - 48 * x ^ 6 + 48
      * x ^ 7 + 24 * x ^ 8) / (36 * (1 + x) ^ 4)

/-- Coefficient `00001` of `G₁` near `0`, divided by `x`. -/
noncomputable def d00001 (x : ℝ) : ℝ :=
  (-323 - 2420 * x - 5346 * x ^ 2 - 4436 * x ^ 3 - 359 * x ^ 4 + 792 * x ^ 5 + 72 * x ^ 6 - 72
      * x ^ 7 - 36 * x ^ 8) / (108 * (1 + x) ^ 4)

/-- The constant-monomial coefficient of `G₁` near `0`. -/
noncomputable def c0fun (x : ℝ) : ℝ :=
  (-4619 - 12067 * x - 8303 * x ^ 2 + 2289 * x ^ 3 + 4539 * x ^ 4 + 3015 * x ^ 5 + 675 * x ^ 6
      - 513 * x ^ 7 - 270 * x ^ 8 - 162 * x ^ 9) / (432 * (1 + x) ^ 3)


theorem setAG1_eq_near_zero {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    setAG1 x = c0fun x +
      d21000 x * (x * log x ^ 2) * (remL1 x) +
      d20100 x * (x * log x ^ 2) * (remLm x) +
      d20000 x * (x * log x ^ 2) +
      d11100 x * (x * log x) * (remL1 x * remLm x) +
      d11000 x * (x * log x) * (remL1 x) +
      d10200 x * (x * log x) * (remLm x * remLm x) +
      d10100 x * (x * log x) * (remLm x) +
      d10010 x * (x * log x) * (remP x) +
      d10001 x * (x * log x) * (remM x) +
      d10000 x * (x * log x) +
      d01100 x * x * (remL1 x * remLm x) +
      d01000 x * x * (remL1 x) +
      d00200 x * x * (remLm x * remLm x) +
      d00110 x * x * (remLm x * remP x) +
      d00101 x * x * (remLm x * remM x) +
      d00100 x * x * (remLm x) +
      d00010 x * x * (remP x) +
      d00001 x * x * (remM x) := by
  obtain ⟨h0, h1⟩ := hx
  have hz : x ≠ 0 := h0.ne'
  have hp : 1 + x ≠ 0 := by linarith
  have hL1 : log (1 - x) = -x - x ^ 2 / 2 + x ^ 3 * remL1 x := by
    unfold remL1; field_simp; ring
  have hLm : log (1 + x) = x - x ^ 2 / 2 + x ^ 3 * remLm x := by
    unfold remLm; field_simp; ring
  have hP : Li 2 x = x * remP x := by unfold remP; field_simp
  have hM : Li 2 (-x) = -x * remM x := by unfold remM; field_simp
  have e0 : h21000 x * x ^ 3 = x * d21000 x := by
    simp only [h21000, d21000]
    field_simp
  have e1 : h20100 x * x ^ 3 = x * d20100 x := by
    simp only [h20100, d20100]
    field_simp
  have e2 : h20000 x + h20100 x * x - h21000 x * x - (1/2) * h20100 x * x ^ 2 - (1/2) * h21000 x
      * x ^ 2 = x * d20000 x := by
    simp only [h20000, h20100, h21000, d20000]
    field_simp
    ring
  have e3 : h11100 x * x ^ 6 = x * d11100 x := by
    simp only [h11100, d11100]
    field_simp
  have e4 : h11000 x * x ^ 3 + h11100 x * x ^ 4 - (1/2) * h11100 x * x ^ 5 = x * d11000 x := by
    simp only [h11000, h11100, d11000]
    field_simp
    ring
  have e5 : h10200 x * x ^ 6 = x * d10200 x := by
    simp only [h10200, d10200]
    field_simp
  have e6 : h10100 x * x ^ 3 - h10200 x * x ^ 5 - h11100 x * x ^ 4 + 2 * h10200 x * x ^ 4 - (1/2)
      * h11100 x * x ^ 5 = x * d10100 x := by
    simp only [h10100, h10200, h11100, d10100]
    field_simp
    ring
  have e7 : h10010 x * x = x * d10010 x := by
    simp only [h10010, d10010]
    field_simp
  have e8 : -(h10001 x * x) = x * d10001 x := by
    simp only [h10001, d10001]
    field_simp
    ring
  have e9 : h10000 x + h10100 x * x + h10200 x * x ^ 2 - h10200 x * x ^ 3 - h11000 x * x
      - h11100 x * x ^ 2 - (1/2) * h10100 x * x ^ 2 - (1/2) * h11000 x * x ^ 2 + (1/4) * h10200 x
      * x ^ 4 + (1/4) * h11100 x * x ^ 4 = x * d10000 x := by
    simp only [h10000, h10100, h10200, h11000, h11100, d10000]
    field_simp
    ring
  have e10 : h01100 x * x ^ 6 = x * d01100 x := by
    simp only [h01100, d01100]
    field_simp
  have e11 : h01000 x * x ^ 3 + h01100 x * x ^ 4 - (1/2) * h01100 x * x ^ 5 = x * d01000 x := by
    simp only [h01000, h01100, d01000]
    field_simp
    ring
  have e12 : h00200 x * x ^ 6 = x * d00200 x := by
    simp only [h00200, d00200]
    field_simp
  have e13 : h00110 x * x ^ 4 = x * d00110 x := by
    simp only [h00110, d00110]
    field_simp
  have e14 : -(h00101 x * x ^ 4) = x * d00101 x := by
    simp only [h00101, d00101]
    field_simp
    ring
  have e15 : h00100 x * x ^ 3 - h00200 x * x ^ 5 - h01100 x * x ^ 4 + 2 * h00200 x * x ^ 4 -
      (1/2) * h01100 x * x ^ 5 = x * d00100 x := by
    simp only [h00100, h00200, h01100, d00100]
    field_simp
    ring
  have e16 : h00010 x * x + h00110 x * x ^ 2 - (1/2) * h00110 x * x ^ 3 = x * d00010 x := by
    simp only [h00010, h00110, d00010]
    field_simp
    ring
  have e17 : (1/2) * h00101 x * x ^ 3 - h00001 x * x - h00101 x * x ^ 2 = x * d00001 x := by
    simp only [h00001, h00101, d00001]
    field_simp
    ring
  have e18 : h00000 x + h00100 x * x + h00200 x * x ^ 2 - h00200 x * x ^ 3 - h01000 x * x
      - h01100 x * x ^ 2 - (1/2) * h00100 x * x ^ 2 - (1/2) * h01000 x * x ^ 2 + (1/4) * h00200 x
      * x ^ 4 + (1/4) * h01100 x * x ^ 4 = c0fun x := by
    simp only [h00000, h00100, h00200, h01000, h01100, c0fun]
    field_simp
    ring

  unfold setAG1
  rw [hL1, hLm, hP, hM]

  linear_combination log x ^ 2 * remL1 x * e0 + log x ^ 2 * remLm x * e1 + log x ^ 2 * e2 + log x
      * remL1 x * remLm x * e3 + log x * remL1 x * e4 + log x * remLm x * remLm x * e5 + log x
      * remLm x * e6 + log x * remP x * e7 + log x * remM x * e8 + log x * e9 + remL1 x * remLm x
      * e10 + remL1 x * e11 + remLm x * remLm x * e12 + remLm x * remP x * e13 + remLm x * remM x
      * e14 + remLm x * e15 + remP x * e16 + remM x * e17 + e18

end SetAW1

open SetAW1

/-- `G₁(0⁺) = -4619/432`. -/
theorem tendsto_setAG1_zero : Tendsto setAG1 (𝓝[>] 0) (𝓝 (-(4619 / 432))) := by
  have ev : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) (1 / 2) := Ioo_mem_nhdsGT (by norm_num)
  have hl : 𝓝[>] (0 : ℝ) ≤ 𝓝 0 := nhdsWithin_le_nhds
  have b1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), |remL1 x| ≤ 3 := ev.mono fun x hx => abs_remL1_le hx.1 hx.2
  have bm : ∀ᶠ x in 𝓝[>] (0 : ℝ), |remLm x| ≤ 3 := ev.mono fun x hx => abs_remLm_le hx.1 hx.2
  have bP : ∀ᶠ x in 𝓝[>] (0 : ℝ), |remP x| ≤ 3 := ev.mono fun x hx => abs_remP_le hx.1 hx.2
  have bM : ∀ᶠ x in 𝓝[>] (0 : ℝ), |remM x| ≤ 3 := ev.mono fun x hx => abs_remM_le hx.1 hx.2
  have x0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := tlim hl (by fun_prop) rfl
  have x1 : Tendsto (fun x : ℝ => x * log x) (𝓝[>] 0) (𝓝 0) := tendsto_mul_log_zero
  have x2 : Tendsto (fun x : ℝ => x * log x ^ 2) (𝓝[>] 0) (𝓝 0) := tendsto_mul_log_sq_zero
  have cc := tlim hl (g := c0fun) (by unfold c0fun; fun_prop (disch := norm_num)) rfl
  have l21000 := tendsto_mul_zero_of_tendsto (tlim hl (g := d21000)
    (by unfold d21000; fun_prop (disch := norm_num)) rfl) x2
  have t21000 := tendsto_mul_bdd l21000 b1
  have l20100 := tendsto_mul_zero_of_tendsto (tlim hl (g := d20100)
    (by unfold d20100; fun_prop (disch := norm_num)) rfl) x2
  have t20100 := tendsto_mul_bdd l20100 bm
  have l20000 := tendsto_mul_zero_of_tendsto (tlim hl (g := d20000)
    (by unfold d20000; fun_prop (disch := norm_num)) rfl) x2
  have t20000 := l20000
  have l11100 := tendsto_mul_zero_of_tendsto (tlim hl (g := d11100)
    (by unfold d11100; fun_prop (disch := norm_num)) rfl) x1
  have t11100 := tendsto_mul_bdd l11100 ((b1.and bm).mono fun _ h => abs_mul_le_three h.1 h.2)
  have l11000 := tendsto_mul_zero_of_tendsto (tlim hl (g := d11000)
    (by unfold d11000; fun_prop (disch := norm_num)) rfl) x1
  have t11000 := tendsto_mul_bdd l11000 b1
  have l10200 := tendsto_mul_zero_of_tendsto (tlim hl (g := d10200)
    (by unfold d10200; fun_prop (disch := norm_num)) rfl) x1
  have t10200 := tendsto_mul_bdd l10200 ((bm.and bm).mono fun _ h => abs_mul_le_three h.1 h.2)
  have l10100 := tendsto_mul_zero_of_tendsto (tlim hl (g := d10100)
    (by unfold d10100; fun_prop (disch := norm_num)) rfl) x1
  have t10100 := tendsto_mul_bdd l10100 bm
  have l10010 := tendsto_mul_zero_of_tendsto (tlim hl (g := d10010)
    (by unfold d10010; fun_prop (disch := norm_num)) rfl) x1
  have t10010 := tendsto_mul_bdd l10010 bP
  have l10001 := tendsto_mul_zero_of_tendsto (tlim hl (g := d10001)
    (by unfold d10001; fun_prop (disch := norm_num)) rfl) x1
  have t10001 := tendsto_mul_bdd l10001 bM
  have l10000 := tendsto_mul_zero_of_tendsto (tlim hl (g := d10000)
    (by unfold d10000; fun_prop (disch := norm_num)) rfl) x1
  have t10000 := l10000
  have l01100 := tendsto_mul_zero_of_tendsto (tlim hl (g := d01100)
    (by unfold d01100; fun_prop (disch := norm_num)) rfl) x0
  have t01100 := tendsto_mul_bdd l01100 ((b1.and bm).mono fun _ h => abs_mul_le_three h.1 h.2)
  have l01000 := tendsto_mul_zero_of_tendsto (tlim hl (g := d01000)
    (by unfold d01000; fun_prop (disch := norm_num)) rfl) x0
  have t01000 := tendsto_mul_bdd l01000 b1
  have l00200 := tendsto_mul_zero_of_tendsto (tlim hl (g := d00200)
    (by unfold d00200; fun_prop (disch := norm_num)) rfl) x0
  have t00200 := tendsto_mul_bdd l00200 ((bm.and bm).mono fun _ h => abs_mul_le_three h.1 h.2)
  have l00110 := tendsto_mul_zero_of_tendsto (tlim hl (g := d00110)
    (by unfold d00110; fun_prop (disch := norm_num)) rfl) x0
  have t00110 := tendsto_mul_bdd l00110 ((bm.and bP).mono fun _ h => abs_mul_le_three h.1 h.2)
  have l00101 := tendsto_mul_zero_of_tendsto (tlim hl (g := d00101)
    (by unfold d00101; fun_prop (disch := norm_num)) rfl) x0
  have t00101 := tendsto_mul_bdd l00101 ((bm.and bM).mono fun _ h => abs_mul_le_three h.1 h.2)
  have l00100 := tendsto_mul_zero_of_tendsto (tlim hl (g := d00100)
    (by unfold d00100; fun_prop (disch := norm_num)) rfl) x0
  have t00100 := tendsto_mul_bdd l00100 bm
  have l00010 := tendsto_mul_zero_of_tendsto (tlim hl (g := d00010)
    (by unfold d00010; fun_prop (disch := norm_num)) rfl) x0
  have t00010 := tendsto_mul_bdd l00010 bP
  have l00001 := tendsto_mul_zero_of_tendsto (tlim hl (g := d00001)
    (by unfold d00001; fun_prop (disch := norm_num)) rfl) x0
  have t00001 := tendsto_mul_bdd l00001 bM
  have H :=
      ((((((((((((((((((cc.add t21000).add t20100).add t20000).add t11100).add t11000).add
      t10200).add t10100).add t10010).add t10001).add t10000).add t01100).add t01000).add
      t00200).add t00110).add t00101).add t00100).add t00010).add t00001)
  have ev' : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  have H2 : Tendsto setAG1 (𝓝[>] 0) (𝓝 _) := H.congr' <| by
    filter_upwards [ev'] with x hx
    rw [setAG1_eq_near_zero hx]
  convert H2 using 2
  simp only [c0fun]
  norm_num

theorem setAG1_eq_near_one {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    setAG1 x = q21000 x * (log x ^ 2) * ((1 - x) * log (1 - x)) +
      h20100 x * (log x ^ 2 * log (1 + x)) +
      h20000 x * (log x ^ 2) +
      q11100 x * (log x * log (1 + x)) * ((1 - x) * log (1 - x)) +
      q11000 x * (log x) * ((1 - x) * log (1 - x)) +
      h10200 x * (log x * log (1 + x) ^ 2) +
      h10100 x * (log x * log (1 + x)) +
      h10010 x * (log x * Li 2 x) +
      h10001 x * (log x * Li 2 (-x)) +
      h10000 x * (log x) +
      q01100 x * (log (1 + x)) * ((1 - x) * log (1 - x)) +
      q01000 x * ((1 - x) * log (1 - x)) +
      h00200 x * (log (1 + x) ^ 2) +
      h00110 x * (log (1 + x) * Li 2 x) +
      h00101 x * (log (1 + x) * Li 2 (-x)) +
      h00100 x * (log (1 + x)) +
      h00010 x * (Li 2 x) +
      h00001 x * (Li 2 (-x)) +
      h00000 x := by
  obtain ⟨h0, h1⟩ := hx
  have hz : x ≠ 0 := h0.ne'
  have hp : 1 + x ≠ 0 := by linarith
  have e21000 : h21000 x = (1 - x) * q21000 x := by
    simp only [h21000, q21000]
    field_simp
    ring
  have e11100 : h11100 x = (1 - x) * q11100 x := by
    simp only [h11100, q11100]
    field_simp
    ring
  have e11000 : h11000 x = (1 - x) * q11000 x := by
    simp only [h11000, q11000]
    field_simp
    ring
  have e01100 : h01100 x = (1 - x) * q01100 x := by
    simp only [h01100, q01100]
    field_simp
    ring
  have e01000 : h01000 x = (1 - x) * q01000 x := by
    simp only [h01000, q01000]
    field_simp
    ring
  unfold setAG1
  rw [e21000, e11100, e11000, e01100, e01000]
  ring

/-- `G₁(1⁻) = -41π²/81 - 1927/432 + π² log 2/3`. -/
theorem tendsto_setAG1_one :
    Tendsto setAG1 (𝓝[<] 1) (𝓝 (-(41 / 81) * π ^ 2 - 1927 / 432 + π ^ 2 * log 2 / 3)) := by
  have ev : ∀ᶠ x in 𝓝[<] (1 : ℝ), x ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT one_pos
  have hl : 𝓝[<] (1 : ℝ) ≤ 𝓝 1 := nhdsWithin_le_nhds
  have m1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have mm : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have sI := ev.mono fun u hu => mem_Icc.2 (abs_le.1 (PM.data_id hu.1 hu.2).2.1.le)
  have sA := ev.mono fun u hu => mem_Icc.2 (abs_le.1 (PM.data_neg hu.1 hu.2).2.1.le)
  have e0 : Tendsto (fun x : ℝ => log x) _ (𝓝 0) :=
    tlim hl (continuousAt_log one_ne_zero) (by norm_num)
  have em : Tendsto (fun x : ℝ => log (1 + x)) _ (𝓝 (log 2)) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have qP := tendsto_Li_comp (k := 2) (by norm_num) m1
    (tlim hl (g := fun x : ℝ => x) (by fun_prop) rfl) sI
  have qM := tendsto_Li_comp (k := 2) (by norm_num) mm
    (tlim hl (g := fun x : ℝ => -x) (by fun_prop) (by norm_num)) sA
  have z : Tendsto (fun x : ℝ => (1 - x) * log (1 - x)) (𝓝[<] 1) (𝓝 0) :=
    tendsto_mul_log_zero.comp tendsto_one_sub_nhdsLT_one
  have T0 := ((tlim hl (g := q21000) (by unfold q21000; fun_prop (disch := norm_num)) rfl).mul
      (e0.pow 2)).mul z
  have T1 := (tlim hl (g := h20100) (by unfold h20100; fun_prop (disch := norm_num)) rfl).mul
      ((e0.pow 2).mul em)
  have T2 := (tlim hl (g := h20000) (by unfold h20000; fun_prop (disch := norm_num)) rfl).mul
      (e0.pow 2)
  have T3 := ((tlim hl (g := q11100) (by unfold q11100; fun_prop (disch := norm_num)) rfl).mul
      (e0.mul em)).mul z
  have T4 := ((tlim hl (g := q11000) (by unfold q11000; fun_prop
      (disch := norm_num)) rfl).mul e0).mul z
  have T5 := (tlim hl (g := h10200) (by unfold h10200; fun_prop (disch := norm_num)) rfl).mul
      (e0.mul (em.pow 2))
  have T6 := (tlim hl (g := h10100) (by unfold h10100; fun_prop (disch := norm_num)) rfl).mul
      (e0.mul em)
  have T7 := (tlim hl (g := h10010) (by unfold h10010; fun_prop (disch := norm_num)) rfl).mul
      (e0.mul qP)
  have T8 := (tlim hl (g := h10001) (by unfold h10001; fun_prop (disch := norm_num)) rfl).mul
      (e0.mul qM)
  have T9 := (tlim hl (g := h10000) (by unfold h10000; fun_prop (disch := norm_num)) rfl).mul e0
  have T10 := ((tlim hl (g := q01100) (by unfold q01100; fun_prop
      (disch := norm_num)) rfl).mul em).mul z
  have T11 := ((tlim hl (g := q01000) (by unfold q01000; fun_prop (disch := norm_num)) rfl)).mul z
  have T12 := (tlim hl (g := h00200) (by unfold h00200; fun_prop (disch := norm_num)) rfl).mul
      (em.pow 2)
  have T13 := (tlim hl (g := h00110) (by unfold h00110; fun_prop (disch := norm_num)) rfl).mul
      (em.mul qP)
  have T14 := (tlim hl (g := h00101) (by unfold h00101; fun_prop (disch := norm_num)) rfl).mul
      (em.mul qM)
  have T15 := (tlim hl (g := h00100) (by unfold h00100; fun_prop (disch := norm_num)) rfl).mul em
  have T16 := (tlim hl (g := h00010) (by unfold h00010; fun_prop (disch := norm_num)) rfl).mul qP
  have T17 := (tlim hl (g := h00001) (by unfold h00001; fun_prop (disch := norm_num)) rfl).mul qM
  have T18 := (tlim hl (g := h00000) (by unfold h00000; fun_prop (disch := norm_num)) rfl)
  have H :=
      ((((((((((((((((((T0.add T1).add T2).add T3).add T4).add T5).add T6).add T7).add T8).add
      T9).add T10).add T11).add T12).add T13).add T14).add T15).add T16).add T17).add T18)
  have H2 : Tendsto setAG1 (𝓝[<] 1) (𝓝 _) := H.congr' <| by
    filter_upwards [ev] with x hx
    rw [setAG1_eq_near_one hx]
  convert H2 using 2
  simp only [h20100, h20000, h10200, h10100, h10010, h10001, h10000, h00200, h00110, h00101,
      h00100, h00010, h00001, h00000, mul_zero, zero_mul,
    show Li 2 1 = π ^ 2 / 6 from Li₂_one, show Li 2 (-1) = -π ^ 2 / 12 from Li₂_neg_one]
  norm_num
  ring

end QED.Chain
