/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RPrim
import QED.Polylog.Deriv
import QED.Polylog.ExtraIntegrals
import QED.Polylog.LiCalculus
import QED.Polylog.Integral

/-!
# Set (d), master `I₁₂`: the logarithmic face function of `T''` and its antiderivative

The second `ε`-derivatives of the face terms `T_A`, `T_B` at `ε = 0` are integrals of
`(4/θ) (h(r) + m g(r))`, where `g` is `QED.ThreeLoopD.i12Rg`, `m` is a logarithm and

  `h(r) = (9/2) ((1 + r)² log² (1 + r) - r² log² r) / r + 2 log r · g(r)`
  (`QED.ThreeLoopD.i12Th`).

With `l = log r`, `L = log (1 + r)`, `w = r / (1 + r)`, `v = 1 / (1 + r)` (both in `(0, 1)`),

  `Hh(r) = 2L³ - 3L²l + (9/2)(r + 1 - 1/r) L² + 12 L Li₂ w - 6 L Li₂ v - 6 r L l + 6 L l / r
    - 3 r L + 3 L + 6 L / r - 12 l Li₂ w + 9 Li₂ w + 12 Li₃ w - 6 Li₃ v + (3/2) r l² + 3 r l
    - 6 l - 6 + 6 ζ(3)`   (`QED.ThreeLoopD.i12ThPrim`)

is an antiderivative of `h(r) / r` on `(0, ∞)` with `Hh(0⁺) = 0`: as `r → 0⁺`, `6 L / r → 6`,
`Li₃ v → ζ(3)` and all other terms vanish (`6 l (L / r - 1) = O(r l)`).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i12ThPrim`.
* `QED.ThreeLoopD.tendsto_i12ThPrim_zero`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- `h(r) = (9/2) ((1 + r)² log² (1 + r) - r² log² r) / r + 2 log r · g(r)`. -/
noncomputable def i12Th (r : ℝ) : ℝ :=
  9 / 2 * ((1 + r) ^ 2 * log (1 + r) ^ 2 - r ^ 2 * log r ^ 2) / r + 2 * log r * i12Rg r

/-- An antiderivative of `h(r) / r` on `(0, ∞)`, vanishing at `0⁺`. -/
noncomputable def i12ThPrim (r : ℝ) : ℝ :=
  2 * log (1 + r) ^ 3 - 3 * log (1 + r) ^ 2 * log r +
    9 / 2 * (r + 1 - r⁻¹) * log (1 + r) ^ 2 + 12 * log (1 + r) * Li₂ (r / (1 + r)) -
    6 * log (1 + r) * Li₂ (1 / (1 + r)) - 6 * r * log (1 + r) * log r +
    6 * r⁻¹ * log (1 + r) * log r - 3 * r * log (1 + r) + 3 * log (1 + r) +
    6 * r⁻¹ * log (1 + r) - 12 * log r * Li₂ (r / (1 + r)) + 9 * Li₂ (r / (1 + r)) +
    12 * Li₃ (r / (1 + r)) - 6 * Li₃ (1 / (1 + r)) + 3 / 2 * r * log r ^ 2 + 3 * r * log r -
    6 * log r - 6 + 6 * zeta3

theorem i12_one_div_one_add_mem {r : ℝ} (hr : 0 < r) : 0 < 1 / (1 + r) ∧ 1 / (1 + r) < 1 :=
  ⟨by positivity, (div_lt_one (by linarith)).2 (by linarith)⟩

theorem hasDerivAt_i12ThPrim {r : ℝ} (hr0 : 0 < r) :
    HasDerivAt i12ThPrim (i12Th r / r) r := by
  have h1 : (1 + r) ≠ 0 := by positivity
  have hw := i12_div_one_add_mem hr0
  have hv := i12_one_div_one_add_mem hr0
  have hr : HasDerivAt (fun x : ℝ => x) 1 r := hasDerivAt_id' r
  have hri : HasDerivAt (fun x : ℝ => x⁻¹) (-(r ^ 2)⁻¹) r := hasDerivAt_inv hr0.ne'
  have hl : HasDerivAt (fun x : ℝ => log x) r⁻¹ r := hasDerivAt_log hr0.ne'
  have hL : HasDerivAt (fun x : ℝ => log (1 + x)) (1 / (1 + r)) r := by
    have := ((hasDerivAt_id' r).const_add 1).log h1
    simpa [one_div] using this
  have hq : HasDerivAt (fun x : ℝ => x / (1 + x)) (1 / (1 + r) ^ 2) r := by
    have := (hasDerivAt_id' r).div ((hasDerivAt_id' r).const_add 1) h1
    refine this.congr_deriv ?_
    field_simp
    ring
  have hp : HasDerivAt (fun x : ℝ => 1 / (1 + x)) (-1 / (1 + r) ^ 2) r := by
    have := ((hasDerivAt_id' r).const_add 1).inv h1
    simp only [one_div]
    refine this.congr_deriv ?_
    field_simp
  have hw1 : |r / (1 + r)| < 1 := by rw [abs_of_pos hw.1]; exact hw.2
  have hv1 : |1 / (1 + r)| < 1 := by rw [abs_of_pos hv.1]; exact hv.2
  have hdw : 1 / (1 + r) ^ 2 / (r / (1 + r)) = 1 / (r * (1 + r)) := by
    field_simp
  have hdv : -1 / (1 + r) ^ 2 / (1 / (1 + r)) = -1 / (1 + r) := by
    field_simp
  have hlw : log (1 - r / (1 + r)) = -log (1 + r) := by
    rw [show 1 - r / (1 + r) = (1 + r)⁻¹ by field_simp; ring]
    exact log_inv _
  have hlv : log (1 - 1 / (1 + r)) = log r - log (1 + r) := by
    rw [show 1 - 1 / (1 + r) = r / (1 + r) by field_simp; ring]
    exact log_div hr0.ne' h1
  have hP2 := hasDerivAt_Li_two_of hq hw1 hw.1.ne' hdw hlw
  have hQ2 := hasDerivAt_Li_two_of hp hv1 hv.1.ne' hdv hlv
  have hP3 := hasDerivAt_Li_three_of hq hw1 hw.1.ne' hdw rfl
  have hQ3 := hasDerivAt_Li_three_of hp hv1 hv.1.ne' hdv rfl
  simp only [Li_two, Li_three] at hP2 hQ2 hP3 hQ3
  have h := ((((((((((((((((((((((hr.mul hl).mul hl).const_mul (3/2)).add
    (((hr.mul hl).mul hL).const_mul (-6))).add
    ((hr.mul hl).const_mul (3))).add
    (((hr.mul hL).mul hL).const_mul (9/2))).add
    ((hr.mul hL).const_mul (-3))).add
    (((hri.mul hl).mul hL).const_mul (6))).add
    (((hri.mul hL).mul hL).const_mul (-9/2))).add
    ((hri.mul hL).const_mul (6))).add
    (((hl.mul hL).mul hL).const_mul (-3))).add
    ((hl.mul hP2).const_mul (-12))).add
    (hl.const_mul (-6))).add
    (((hL.mul hL).mul hL).const_mul (2))).add
    ((hL.mul hL).const_mul (9/2))).add
    ((hL.mul hP2).const_mul (12))).add
    ((hL.mul hQ2).const_mul (-6))).add
    (hL.const_mul (3))).add
    (hP2.const_mul (9))).add
    (hP3.const_mul (12))).add
    (hQ3.const_mul (-6))).add_const (6*zeta3 - 6))
  convert h using 1
  · funext x
    simp only [i12ThPrim, Pi.mul_apply, Pi.add_apply]
    ring
  simp only [i12Th, i12Rg, Pi.mul_apply]
  generalize log r = l
  generalize log (1 + r) = L
  generalize Li₂ (r / (1 + r)) = P2
  generalize Li₂ (1 / (1 + r)) = Q2
  field_simp
  ring

/-- `|log (1 + r) - r| ≤ 2 r²` for `0 < r < 1/2`. -/
theorem i12_abs_log_one_add_sub_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1 / 2) :
    |log (1 + r) - r| ≤ 2 * r ^ 2 := by
  have hx : |-r| < 1 := by rw [abs_neg, abs_of_pos hr0]; linarith
  have h := abs_log_sub_add_sum_range_le hx 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero,
    div_one, sub_neg_eq_add, abs_neg, abs_of_pos hr0] at h
  rw [show -r + log (1 + r) = log (1 + r) - r by ring] at h
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith), show (1 : ℕ) + 1 = 2 from rfl]
  nlinarith [mul_pos hr0 hr0]

theorem tendsto_i12ThPrim_zero : Tendsto i12ThPrim (𝓝[>] 0) (𝓝 0) := by
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo (0 : ℝ) (1 / 2) := Ioo_mem_nhdsGT (by norm_num)
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
    (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hL : Tendsto (fun r : ℝ => log (1 + r)) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => log (1 + r)) (𝓝 0) (𝓝 (log (1 + 0))) :=
      ((continuous_const.add continuous_id).tendsto 0).log (by norm_num)
    simpa using h.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hLr := tendsto_log_one_add_div_zero
  have hrl := tendsto_mul_log_zero
  have hrl2 := tendsto_mul_log_sq_zero
  have hLl : Tendsto (fun r : ℝ => log (1 + r) * log r) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using hrl.abs)
    filter_upwards [hev] with r hr'
    have h0 : 0 ≤ log (1 + r) := log_nonneg (by linarith [hr'.1])
    have h1 : log (1 + r) ≤ r := by
      have := log_le_sub_one_of_pos (by linarith [hr'.1] : 0 < 1 + r)
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, abs_of_pos hr'.1]
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have hR : Tendsto (fun r : ℝ => log r * (log (1 + r) / r - 1)) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using hrl.abs.const_mul 2)
    filter_upwards [hev] with r hr'
    obtain ⟨hr0, hr1⟩ := hr'
    have hb := i12_abs_log_one_add_sub_le hr0 hr1
    have e : log (1 + r) / r - 1 = (log (1 + r) - r) / r := by field_simp
    rw [e, Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hr0]
    calc |log r| * (|log (1 + r) - r| / r) ≤ |log r| * (2 * r ^ 2 / r) := by gcongr
      _ = 2 * (r * |log r|) := by field_simp
  have hw : Tendsto (fun r : ℝ => r / (1 + r)) (𝓝[>] 0) (𝓝 0) := by
    convert hr.div (tendsto_const_nhds.add hr) (by norm_num : (1 : ℝ) + 0 ≠ 0) using 2
    norm_num
  have hv : Tendsto (fun r : ℝ => 1 / (1 + r)) (𝓝[>] 0) (𝓝 1) := by
    convert (tendsto_const_nhds (x := (1 : ℝ))).div (tendsto_const_nhds.add hr)
      (by norm_num : (1 : ℝ) + 0 ≠ 0) using 2
    norm_num
  have hwI : ∀ᶠ r in 𝓝[>] (0 : ℝ), r / (1 + r) ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [hev] with r hr'
    have := i12_div_one_add_mem hr'.1
    exact ⟨by linarith, this.2.le⟩
  have hvI : ∀ᶠ r in 𝓝[>] (0 : ℝ), 1 / (1 + r) ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [hev] with r hr'
    have := i12_one_div_one_add_mem hr'.1
    exact ⟨by linarith, this.2.le⟩
  have hP2 := tendsto_Li₂_comp (by norm_num) hw hwI
  have hQ2 := tendsto_Li₂_comp (by norm_num) hv hvI
  have hP3 := tendsto_Li₃_comp (by norm_num) hw hwI
  have hQ3 := tendsto_Li₃_comp (by norm_num) hv hvI
  have hlP2 : Tendsto (fun r : ℝ => log r * Li₂ (r / (1 + r))) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using hrl.abs.const_mul (π ^ 2 / 6))
    filter_upwards [hev] with r hr'
    have hw' := i12_div_one_add_mem hr'.1
    have hwr : r / (1 + r) ≤ r := div_le_self hr'.1.le (by linarith [hr'.1])
    have hLi := abs_Li₂_le (y := r / (1 + r)) (by rw [abs_of_pos hw'.1]; exact hw'.2.le)
    rw [abs_of_pos hw'.1] at hLi
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hr'.1]
    calc |log r| * |Li₂ (r / (1 + r))| ≤ |log r| * (π ^ 2 / 6 * r) := by
          gcongr
          exact hLi.trans (by gcongr)
      _ = π ^ 2 / 6 * (r * |log r|) := by ring
  have h := (((((((((((((((((((hL.pow 3).const_mul 2).sub ((hL.mul hLl).const_mul 3)).add
    ((hr.mul (hL.pow 2)).const_mul (9 / 2))).add ((hL.pow 2).const_mul (9 / 2))).sub
    ((hLr.mul hL).const_mul (9 / 2))).add ((hL.mul hP2).const_mul 12)).sub
    ((hL.mul hQ2).const_mul 6)).sub ((hr.mul hLl).const_mul 6)).add (hR.const_mul 6)).sub
    ((hr.mul hL).const_mul 3)).add (hL.const_mul 3)).add (hLr.const_mul 6)).sub
    (hlP2.const_mul 12)).add (hP2.const_mul 9)).add (hP3.const_mul 12)).sub
    (hQ3.const_mul 6)).add (hrl2.const_mul (3 / 2))).add (hrl.const_mul 3)).add_const
    (-6 + 6 * zeta3)
  have e : i12ThPrim =ᶠ[𝓝[>] 0] fun r => 2 * log (1 + r) ^ 3 -
      3 * (log (1 + r) * (log (1 + r) * log r)) + 9 / 2 * (r * log (1 + r) ^ 2) +
      9 / 2 * log (1 + r) ^ 2 - 9 / 2 * (log (1 + r) / r * log (1 + r)) +
      12 * (log (1 + r) * Li₂ (r / (1 + r))) - 6 * (log (1 + r) * Li₂ (1 / (1 + r))) -
      6 * (r * (log (1 + r) * log r)) + 6 * (log r * (log (1 + r) / r - 1)) -
      3 * (r * log (1 + r)) + 3 * log (1 + r) + 6 * (log (1 + r) / r) -
      12 * (log r * Li₂ (r / (1 + r))) + 9 * Li₂ (r / (1 + r)) + 12 * Li₃ (r / (1 + r)) -
      6 * Li₃ (1 / (1 + r)) + 3 / 2 * (r * log r ^ 2) + 3 * (r * log r) + (-6 + 6 * zeta3) := by
    filter_upwards [hev] with r hr'
    have := hr'.1.ne'
    simp only [i12ThPrim]
    field_simp
    ring
  refine Tendsto.congr' e.symm ?_
  convert h using 2
  simp only [Li₂_zero, Li₃_zero, Li₃_one]
  ring

end QED.ThreeLoopD
