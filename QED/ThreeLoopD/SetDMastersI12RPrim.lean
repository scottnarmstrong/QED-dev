/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import QED.Polylog.Deriv
import QED.Polylog.Reflection
import QED.Polylog.ExtraIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Set (d), master `I₁₂`: the one-dimensional integrals of the coefficient `r₁`

The first Taylor coefficient of the remainder `QED.ThreeLoopD.i12Rest` involves the
`ε`-derivative of the bracket `Φ₀(X, Y) - (2 - 3ε) Y ^ (-3ε)` at `ε = 0`. With `r = X / Y` it
is

  `g(r) = 3 - 3 ((1 + r)² log (1 + r) - r² log r) / r`   (`QED.ThreeLoopD.i12Rg`).

On `(0, ∞)` the function `g(r) / r` has the antiderivative

  `Φ(r) = 3 log (1 + r) / r - 3 r log (1 + r) + 3 r log r - 6 Li₂ (r / (1 + r))
    - 3 log² (1 + r) - 3`   (`QED.ThreeLoopD.i12RPhi`),

with `Φ(0⁺) = 0`; the argument `r / (1 + r)` stays in `(0, 1)`. Euler's reflection formula
collapses the pair `Φ(k) + Φ(1 / k)` to `-6 - π² - 3 log² k`: all rational terms cancel and
the two dilogarithms sum to `π² / 6 - log (k / (1 + k)) log (1 / (1 + k))`. Hence, for `k > 0`,

  `∫₀¹ (g(kθ) + g(θ/k)) / θ dθ = -6 - π² - 3 log² k`.

The two remaining one-dimensional integrals are

  `∫₀¹ log² (2u / (1 - u)) du = log² 2 + π² / 3`,
  `∫₀¹ -4 log (1 - ρ / 2) / ρ dρ = 4 Li₂ (1 / 2)`.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i12RPhi`, `QED.ThreeLoopD.tendsto_i12RPhi_zero`.
* `QED.ThreeLoopD.i12RPhi_add_i12RPhi_inv`: `Φ(k) + Φ(1/k) = -6 - π² - 3 log² k`.
* `QED.ThreeLoopD.integral_i12Rg_pair`.
* `QED.ThreeLoopD.intervalIntegrable_and_integral_i12_log_sq`.
* `QED.ThreeLoopD.intervalIntegrable_and_integral_i12_log_half`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- `g(r) = 3 - 3 ((1 + r)² log (1 + r) - r² log r) / r`. -/
noncomputable def i12Rg (r : ℝ) : ℝ :=
  3 - 3 * ((1 + r) ^ 2 * log (1 + r) - r ^ 2 * log r) / r

/-- The antiderivative `Φ` of `g(r) / r` on `(0, ∞)`. -/
noncomputable def i12RPhi (r : ℝ) : ℝ :=
  3 * log (1 + r) / r - 3 * r * log (1 + r) + 3 * r * log r - 6 * Li₂ (r / (1 + r)) -
    3 * log (1 + r) ^ 2 - 3

theorem i12_div_one_add_mem {r : ℝ} (hr : 0 < r) : 0 < r / (1 + r) ∧ r / (1 + r) < 1 :=
  ⟨div_pos hr (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩

theorem hasDerivAt_i12RPhi {r : ℝ} (hr : 0 < r) : HasDerivAt i12RPhi (i12Rg r / r) r := by
  have h1 : (1 + r) ≠ 0 := by positivity
  have hw := i12_div_one_add_mem hr
  have hL : HasDerivAt (fun x : ℝ => log (1 + x)) (1 / (1 + r)) r := by
    have := ((hasDerivAt_id' r).const_add 1).log h1
    simpa [one_div] using this
  have hl : HasDerivAt (fun x : ℝ => log x) (1 / r) r := by
    simpa [one_div] using hasDerivAt_log hr.ne'
  have hq : HasDerivAt (fun x : ℝ => x / (1 + x)) (1 / (1 + r) ^ 2) r := by
    have := (hasDerivAt_id' r).div ((hasDerivAt_id' r).const_add 1) h1
    refine this.congr_deriv ?_
    field_simp
    ring
  have hLi := (hasDerivAt_Li₂ (by rw [abs_of_pos hw.1]; exact hw.2) hw.1.ne').comp r hq
  have hlog1 : log (1 - r / (1 + r)) = -log (1 + r) := by
    rw [show 1 - r / (1 + r) = (1 + r)⁻¹ by field_simp; ring]
    exact log_inv _
  have hA := (hL.const_mul 3).div (hasDerivAt_id' r) hr.ne'
  have hB := ((hasDerivAt_id' r).const_mul 3).mul hL
  have hC := ((hasDerivAt_id' r).const_mul 3).mul hl
  have h := ((((hA.sub hB).add hC).sub (hLi.const_mul 6)).sub ((hL.pow 2).const_mul 3)).sub_const 3
  convert h using 1
  · funext x
    simp only [i12RPhi, Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.div_apply, Pi.pow_apply]
  · rw [hlog1]
    simp only [i12Rg, Nat.cast_ofNat]
    field_simp
    ring

theorem tendsto_i12RPhi_zero : Tendsto i12RPhi (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun r : ℝ => 3 * (log (1 + r) / r)) (𝓝[>] 0) (𝓝 (3 * 1)) :=
    tendsto_log_one_add_div_zero.const_mul 3
  have hc : ContinuousAt (fun r : ℝ => 3 * r * log (1 + r)) 0 :=
    (continuousAt_const.mul continuousAt_id).mul
      ((continuousAt_const.add continuousAt_id).log (by norm_num))
  have h2 : Tendsto (fun r : ℝ => 3 * r * log (1 + r)) (𝓝[>] 0) (𝓝 0) := by
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have h3 : Tendsto (fun r : ℝ => 3 * (r * log r)) (𝓝[>] 0) (𝓝 (3 * 0)) :=
    tendsto_mul_log_zero.const_mul 3
  have hq : Tendsto (fun r : ℝ => r / (1 + r)) (𝓝[>] 0) (𝓝 0) := by
    have hc' : ContinuousAt (fun r : ℝ => r / (1 + r)) 0 :=
      continuousAt_id.div (continuousAt_const.add continuousAt_id) (by norm_num)
    have := hc'.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have h4 : Tendsto (fun r : ℝ => Li₂ (r / (1 + r))) (𝓝[>] 0) (𝓝 (Li₂ 0)) := by
    refine tendsto_Li₂_comp (by norm_num) hq ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    have := i12_div_one_add_mem hr
    exact ⟨by linarith, this.2.le⟩
  have hc5 : ContinuousAt (fun r : ℝ => 3 * log (1 + r) ^ 2) 0 :=
    continuousAt_const.mul (((continuousAt_const.add continuousAt_id).log (by norm_num)).pow 2)
  have h5 : Tendsto (fun r : ℝ => 3 * log (1 + r) ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have := hc5.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have h := ((((h1.sub h2).add h3).sub (h4.const_mul 6)).sub h5).sub_const 3
  rw [Li₂_zero] at h
  convert h using 2
  · simp only [i12RPhi]; ring
  · norm_num

/-- **The reflection pair**: `Φ(k) + Φ(1/k) = -6 - π² - 3 log² k`. -/
theorem i12RPhi_add_i12RPhi_inv {k : ℝ} (hk : 0 < k) :
    i12RPhi k + i12RPhi (1 / k) = -6 - π ^ 2 - 3 * log k ^ 2 := by
  have hk1 : (1 + k) ≠ 0 := by positivity
  have hw := i12_div_one_add_mem hk
  have hrefl := Li₂_add_Li₂_one_sub hw.1.le hw.2.le
  have harg : 1 / k / (1 + 1 / k) = 1 - k / (1 + k) := by field_simp; ring
  have hl1 : log (1 + 1 / k) = log (1 + k) - log k := by
    rw [show 1 + 1 / k = (1 + k) / k by field_simp; ring]
    exact log_div hk1 hk.ne'
  have hl2 : log (1 / k) = -log k := by rw [one_div, log_inv]
  have hl3 : log (k / (1 + k)) = log k - log (1 + k) := log_div hk.ne' hk1
  have hl4 : log (1 - k / (1 + k)) = -log (1 + k) := by
    rw [show 1 - k / (1 + k) = (1 + k)⁻¹ by field_simp; ring]
    exact log_inv _
  rw [hl3, hl4] at hrefl
  simp only [i12RPhi]
  rw [harg, hl1, hl2]
  have e : Li₂ (1 - k / (1 + k)) = π ^ 2 / 6 - (log k - log (1 + k)) * -log (1 + k) -
      Li₂ (k / (1 + k)) := by linarith
  rw [e]
  field_simp
  ring

/-- **The `θ`-integral of the pair** `(g(kθ) + g(θ/k)) / θ`. -/
theorem integral_i12Rg_pair {k : ℝ} (hk : 0 < k)
    (hint : IntervalIntegrable (fun θ => (i12Rg (k * θ) + i12Rg (θ / k)) / θ) volume 0 1) :
    ∫ θ in (0 : ℝ)..1, (i12Rg (k * θ) + i12Rg (θ / k)) / θ = -6 - π ^ 2 - 3 * log k ^ 2 := by
  set F : ℝ → ℝ := fun θ => i12RPhi (k * θ) + i12RPhi (θ / k) with hF
  have hd : ∀ θ : ℝ, 0 < θ → HasDerivAt F ((i12Rg (k * θ) + i12Rg (θ / k)) / θ) θ := by
    intro θ hθ
    have ha := (hasDerivAt_i12RPhi (mul_pos hk hθ)).comp θ ((hasDerivAt_id' θ).const_mul k)
    have hb := (hasDerivAt_i12RPhi (div_pos hθ hk)).comp θ ((hasDerivAt_id' θ).div_const k)
    refine (ha.add hb).congr_deriv ?_
    field_simp
  have hmapA : Tendsto (fun θ : ℝ => k * θ) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_const_mul k).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with θ (hθ : 0 < θ)
      exact mul_pos hk hθ
  have hmapB : Tendsto (fun θ : ℝ => θ / k) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_id.div_const k).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with θ (hθ : 0 < θ)
      exact div_pos hθ hk
  have h0 : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    have := (tendsto_i12RPhi_zero.comp hmapA).add (tendsto_i12RPhi_zero.comp hmapB)
    simpa using this
  have h1 : Tendsto F (𝓝[<] 1) (𝓝 (F 1)) :=
    (hd 1 one_pos).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun θ hθ => hd θ hθ.1) hint h0 h1, hF]
  simp only [mul_one, sub_zero]
  exact i12RPhi_add_i12RPhi_inv hk

/-- The antiderivative of `log² (2u / (1 - u))` on `(0, 1)`. -/
noncomputable def i12RLogSqPrim (u : ℝ) : ℝ :=
  log 2 ^ 2 * u + 2 * log 2 * (u * log u + (1 - u) * log (1 - u)) + u * log u ^ 2 +
    2 * (1 - u) * (log u * log (1 - u)) - (1 - u) * log (1 - u) ^ 2 + 2 * Li₂ u

theorem hasDerivAt_i12RLogSqPrim {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i12RLogSqPrim (log (2 * u / (1 - u)) ^ 2) u := by
  obtain ⟨h0, h1⟩ := hu
  have h1' : 1 - u ≠ 0 := by linarith
  have hl : HasDerivAt (fun x : ℝ => log x) (1 / u) u := by
    simpa [one_div] using hasDerivAt_log h0.ne'
  have hm : HasDerivAt (fun x : ℝ => log (1 - x)) (-1 / (1 - u)) u := by
    have := ((hasDerivAt_id' u).const_sub 1).log h1'
    simpa [neg_div] using this
  have hLi := hasDerivAt_Li₂' ⟨h0, h1⟩
  have hid := hasDerivAt_id' u
  have hs : HasDerivAt (fun x : ℝ => 1 - x) (-1) u := by simpa using hid.const_sub 1
  have h := ((((((hid.const_mul (log 2 ^ 2)).add (((hid.mul hl).add (hs.mul hm)).const_mul
    (2 * log 2))).add (hid.mul (hl.pow 2))).add ((hs.const_mul 2).mul (hl.mul hm))).sub
    (hs.mul (hm.pow 2))).add (hLi.const_mul 2))
  convert h using 1
  · funext x
    simp only [i12RLogSqPrim, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
  · rw [log_div (by positivity) h1', log_mul (by norm_num) h0.ne']
    simp only [Nat.cast_ofNat, Pi.mul_apply, Pi.pow_apply]
    field_simp
    ring

/-- `(1 - x) log x log (1 - x)`-type limits are assembled from `ExtraIntegrals`. -/
theorem tendsto_i12RLogSqPrim_zero : Tendsto i12RLogSqPrim (𝓝[>] 0) (𝓝 0) := by
  have hc1 : ContinuousAt (fun u : ℝ => 1 - u) 0 := continuousAt_const.sub continuousAt_id
  have hc2 : ContinuousAt (fun u : ℝ => log (1 - u)) 0 := hc1.log (by norm_num)
  have t1 : Tendsto (fun u : ℝ => 1 - u) (𝓝[>] 0) (𝓝 1) := by
    simpa using hc1.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have t2 : Tendsto (fun u : ℝ => log (1 - u)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hc2.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have tid : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h := (((((tid.const_mul (log 2 ^ 2)).add ((tendsto_mul_log_zero.add (t1.mul t2)).const_mul
    (2 * log 2))).add tendsto_mul_log_sq_zero).add ((t1.const_mul 2).mul
    tendsto_log_mul_log_one_sub_zero)).sub (t1.mul (t2.pow 2))).add
    (tendsto_Li₂_zero_right.const_mul 2)
  convert h using 2
  · simp only [i12RLogSqPrim]
  · norm_num

theorem tendsto_i12RLogSqPrim_one :
    Tendsto i12RLogSqPrim (𝓝[<] 1) (𝓝 (log 2 ^ 2 + π ^ 2 / 3)) := by
  have tid : Tendsto (fun u : ℝ => u) (𝓝[<] 1) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hcl : ContinuousAt (fun u : ℝ => log u) 1 := continuousAt_log (by norm_num)
  have tl : Tendsto (fun u : ℝ => log u) (𝓝[<] 1) (𝓝 0) := by
    simpa using hcl.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
  have t1 : Tendsto (fun u : ℝ => 1 - u) (𝓝[<] 1) (𝓝 0) := by
    have := ((continuous_sub_left (1 : ℝ)).tendsto (1 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
    simpa using this
  have tA : Tendsto (fun u : ℝ => (1 - u) * log (1 - u)) (𝓝[<] 1) (𝓝 0) :=
    tendsto_mul_log_zero.comp tendsto_one_sub_nhdsLT_one
  have tB : Tendsto (fun u : ℝ => (1 - u) * log (1 - u) ^ 2) (𝓝[<] 1) (𝓝 0) :=
    tendsto_mul_log_sq_zero.comp tendsto_one_sub_nhdsLT_one
  have h := (((((tid.const_mul (log 2 ^ 2)).add (((tid.mul tl).add tA).const_mul
    (2 * log 2))).add (tid.mul (tl.pow 2))).add ((t1.const_mul 2).mul
    tendsto_log_mul_log_one_sub_one)).sub tB).add (tendsto_Li₂_one_left.const_mul 2)
  convert h using 2
  · simp only [i12RLogSqPrim]
  · ring

/-- **`∫₀¹ log² (2u / (1 - u)) du = log² 2 + π² / 3`.** -/
theorem intervalIntegrable_and_integral_i12_log_sq :
    IntervalIntegrable (fun u : ℝ => log (2 * u / (1 - u)) ^ 2) volume 0 1 ∧
      ∫ u in (0 : ℝ)..1, log (2 * u / (1 - u)) ^ 2 = log 2 ^ 2 + π ^ 2 / 3 := by
  have h := intervalIntegrable_and_integral_eq_of_nonneg (fun u hu => hasDerivAt_i12RLogSqPrim hu)
    (fun u _ => sq_nonneg _) tendsto_i12RLogSqPrim_zero tendsto_i12RLogSqPrim_one
  rw [sub_zero] at h
  exact h

/-- **`∫₀¹ -4 log (1 - ρ/2) / ρ dρ = 4 Li₂ (1/2)`.** -/
theorem intervalIntegrable_and_integral_i12_log_half :
    IntervalIntegrable (fun ρ : ℝ => -4 * log (1 - ρ / 2) / ρ) volume 0 1 ∧
      ∫ ρ in (0 : ℝ)..1, -4 * log (1 - ρ / 2) / ρ = 4 * Li₂ (1 / 2) := by
  have hd : ∀ ρ ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun x => 4 * Li₂ (x / 2)) (-4 * log (1 - ρ / 2) / ρ) ρ := by
    intro ρ hρ
    have hw : |ρ / 2| < 1 := by rw [abs_of_pos (by linarith [hρ.1])]; linarith [hρ.2]
    have h := ((hasDerivAt_Li₂ hw (by linarith [hρ.1])).comp ρ
      ((hasDerivAt_id' ρ).div_const 2)).const_mul 4
    refine h.congr_deriv ?_
    have := hρ.1.ne'
    field_simp
  have hnn : ∀ ρ ∈ Ioo (0 : ℝ) 1, 0 ≤ -4 * log (1 - ρ / 2) / ρ := by
    intro ρ hρ
    have : log (1 - ρ / 2) ≤ 0 := log_nonpos (by linarith [hρ.2]) (by linarith [hρ.1])
    exact div_nonneg (by nlinarith) hρ.1.le
  have hc : Continuous fun x : ℝ => x / 2 := continuous_id.div_const 2
  have h0 : Tendsto (fun x : ℝ => 4 * Li₂ (x / 2)) (𝓝[>] 0) (𝓝 (4 * Li₂ 0)) := by
    refine (tendsto_Li₂_comp (by norm_num) ?_ ?_).const_mul 4
    · simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h1 : Tendsto (fun x : ℝ => 4 * Li₂ (x / 2)) (𝓝[<] 1) (𝓝 (4 * Li₂ (1 / 2))) := by
    refine (tendsto_Li₂_comp (by norm_num) ?_ ?_).const_mul 4
    · simpa using (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h := intervalIntegrable_and_integral_eq_of_nonneg hd hnn h0 h1
  rw [Li₂_zero, mul_zero, sub_zero] at h
  exact h

end QED.ThreeLoopD
