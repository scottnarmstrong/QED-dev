/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.LiN
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import QED.Polylog.AlphabetPM
import QED.Polylog.DilogPM
import QED.Polylog.Landen
import QED.Polylog.LiCalculus
import QED.Polylog.Reflection
import QED.Polylog.ExtraIntegrals
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The weight-four integral `∫₀¹ log y log² (1 - y) / y = -π⁴/180`

The integrand has no polylogarithmic antiderivative whose arguments stay in `[-1, 1]` on all of
`(0, 1)`: Nielsen's `S₂,₂` needs `Li 4 (y/(y-1))`. On `(0, 1/2)` it is available. Splitting at
`1/2` and reflecting the right half (`y ↦ 1 - y`),
`∫₀¹ log y log² (1 - y) / y = ∫₀^{1/2} (log y log² (1 - y) / y + log (1 - y) log² y / (1 - y))`,
and the integrand on the right has the antiderivative
`G = -4 P(y) + 4 P(1 - y) - 4 P(y/(y-1)) - 4 Li 2 y log y log (1 - y) - ½ log² y log² (1 - y)
  - 2 log y log³ (1 - y) + ½ log⁴ (1 - y) + (π²/3) log² (1 - y)`,
with `P(f) = Li 4 f - log f Li 3 f`, `G(0⁺) = 4 ζ(4)` and `G(1/2) = -4 Li 4 (-1) = 7π⁴/180`.

## Main results

* `QED.Polylog.intervalIntegrable_and_integral_log_mul_log_one_sub_sq_div`:
  `∫₀¹ log y log² (1 - y) / y = -π⁴/180`, with interval integrability.
* `QED.Polylog.intervalIntegrable_and_integral_log_mul_log_one_sub_sq_sq_div`:
  `∫₀¹ log u log² (1 - u²) / u = -π⁴/720` (substitute `y = u²`).
-/

public section

open Real Set Filter Topology MeasureTheory
open scoped Interval

namespace QED.Polylog

/-! ### The argument `y/(y-1)` on `(0, 1/2)` -/

private theorem data_landen {y : ℝ} (h0 : 0 < y) (h1 : y < 1 / 2) :
    HasDerivAt (fun x : ℝ => x / (x - 1)) (-1 / (y - 1) ^ 2) y ∧
      |y / (y - 1)| < 1 ∧ y / (y - 1) ≠ 0 ∧
      (-1 / (y - 1) ^ 2) / (y / (y - 1)) = 1 / y + 1 / (1 - y) ∧
      log (y / (y - 1)) = log y - log (1 - y) ∧
      Li 2 (y / (y - 1)) = -Li 2 y - log (1 - y) ^ 2 / 2 := by
  have hm : y - 1 ≠ 0 := by linarith
  have hm' : 1 - y ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := (hasDerivAt_id' y).div ((hasDerivAt_id' y).sub_const 1) hm
    refine this.congr_deriv ?_
    field_simp
    ring
  · rw [abs_lt]; constructor
    · rw [lt_div_iff_of_neg (by linarith)]; linarith
    · rw [div_lt_one_of_neg (by linarith)]; linarith
  · exact div_ne_zero h0.ne' hm
  · field_simp
    ring
  · rw [log_div h0.ne' hm, show y - 1 = -(1 - y) by ring, Real.log_neg_eq_log]
  · have h := Li₂_one_sub_inv_add_Li₂_one_sub (x := 1 - y) (by linarith) (by linarith)
    rw [show 1 - (1 - y)⁻¹ = y / (y - 1) by field_simp; ring, sub_sub_cancel] at h
    rw [Li_two]
    linarith

/-! ### The antiderivative on `(0, 1/2)` -/

/-- The antiderivative of `log y log² (1 - y) / y + log (1 - y) log² y / (1 - y)` on
`(0, 1/2)`. -/
private noncomputable def sPrim (y : ℝ) : ℝ :=
  -4 * (Li 4 y - log y * Li 3 y) + 4 * (Li 4 (1 - y) - log (1 - y) * Li 3 (1 - y)) -
    4 * (Li 4 (y / (y - 1)) - log (y / (y - 1)) * Li 3 (y / (y - 1))) -
    4 * Li 2 y * log y * log (1 - y) - log y ^ 2 * log (1 - y) ^ 2 / 2 -
    2 * log y * log (1 - y) ^ 3 + log (1 - y) ^ 4 / 2 + π ^ 2 / 3 * log (1 - y) ^ 2

private theorem hasDerivAt_sPrim {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) (1 / 2)) :
    HasDerivAt sPrim
      (log y * log (1 - y) ^ 2 / y + log (1 - y) * log y ^ 2 / (1 - y)) y := by
  obtain ⟨h0, h1⟩ := hy
  have h1' : y < 1 := by linarith
  obtain ⟨di, ai, ni, li, gi, gi1⟩ := PM.data_id h0 h1'
  obtain ⟨d1, a1, n1, l1, g1, g11⟩ := PM.data_oneSub h0 h1'
  obtain ⟨dL, aL, nL, lL, gL, LL⟩ := data_landen h0 h1
  have p1 := hasDerivAt_Li_four_sub_of di ai ni li gi rfl
  have p2 := hasDerivAt_Li_four_sub_of d1 a1 n1 l1 g1 (Li_two_one_sub' ⟨h0, h1'⟩)
  have p3 := hasDerivAt_Li_four_sub_of dL aL nL lL gL LL
  have q := hasDerivAt_Li_two_of di ai ni li gi1
  have e0 := hasDerivAt_log_of di ni li
  have e1 := hasDerivAt_log_of d1 n1 l1
  have h := (((((((p1.const_mul (-4)).add (p2.const_mul 4)).sub (p3.const_mul 4)).sub
    (((q.const_mul 4).mul e0).mul e1)).sub (((e0.pow 2).mul (e1.pow 2)).div_const 2)).sub
    (((e0.const_mul 2).mul (e1.pow 3)))).add ((e1.pow 4).div_const 2)).add
    ((e1.pow 2).const_mul (π ^ 2 / 3))
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.mul_apply]
  field_simp
  ring

private theorem tendsto_sPrim_zero : Tendsto sPrim (𝓝[>] 0) (𝓝 (2 * π ^ 4 / 45)) := by
  have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), y ∈ Ioo (0 : ℝ) (1 / 2) := Ioo_mem_nhdsGT (by norm_num)
  have hc : ∀ {g : ℝ → ℝ}, ContinuousAt g 0 → Tendsto g (𝓝[>] 0) (𝓝 (g 0)) :=
    fun hg => hg.tendsto.mono_left nhdsWithin_le_nhds
  have gy : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝 0) := hc continuousAt_id
  have g1 : Tendsto (fun y : ℝ => 1 - y) (𝓝[>] 0) (𝓝 1) := by
    simpa using hc (g := fun y : ℝ => 1 - y) (by fun_prop)
  have gL : Tendsto (fun y : ℝ => y / (y - 1)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hc (g := fun y : ℝ => y / (y - 1))
      (continuousAt_id.div (continuousAt_id.sub continuousAt_const) (by norm_num))
  have sy : ∀ᶠ y in 𝓝[>] (0 : ℝ), y ∈ Icc (-1 : ℝ) 1 :=
    hev.mono fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have s1 : ∀ᶠ y in 𝓝[>] (0 : ℝ), 1 - y ∈ Icc (-1 : ℝ) 1 :=
    hev.mono fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have sL : ∀ᶠ y in 𝓝[>] (0 : ℝ), |y / (y - 1)| ≤ 1 :=
    hev.mono fun y hy => (data_landen hy.1 hy.2).2.1.le
  have sL' : ∀ᶠ y in 𝓝[>] (0 : ℝ), y / (y - 1) ∈ Icc (-1 : ℝ) 1 :=
    sL.mono fun y hy => abs_le.1 hy
  have a1 := tendsto_Li_comp (k := 4) (by norm_num) (by norm_num) gy sy
  have a2 := tendsto_log_mul_Li_comp (k := 3) (by norm_num) gy
    (sy.mono fun y hy => abs_le.2 hy)
  have a3 := tendsto_Li_comp (k := 4) (by norm_num) (by norm_num) g1 s1
  have a4 := ((hc (g := fun y : ℝ => log (1 - y)) (by fun_prop (disch := norm_num))).mul
    (tendsto_Li_comp (k := 3) (by norm_num) (by norm_num) g1 s1))
  have a5 := tendsto_Li_comp (k := 4) (by norm_num) (by norm_num) gL sL'
  have a6 := tendsto_log_mul_Li_comp (k := 3) (by norm_num) gL sL
  have a7 := tendsto_Li_comp (k := 2) (by norm_num) (by norm_num) gy sy
  have ll := tendsto_log_mul_log_one_sub_zero
  have l1 : Tendsto (fun y : ℝ => log (1 - y)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hc (g := fun y : ℝ => log (1 - y)) (by fun_prop (disch := norm_num))
  have P1 := (a1.sub a2).const_mul (-4)
  have P2 := (a3.sub a4).const_mul 4
  have P3 := (a5.sub a6).const_mul 4
  have Q1 := (a7.mul ll).const_mul 4
  have Q2 := (ll.pow 2).div_const 2
  have Q3 := (ll.mul (l1.pow 2)).const_mul 2
  have Q4 := (l1.pow 4).div_const 2
  have Q5 := (l1.pow 2).const_mul (π ^ 2 / 3)
  have H := ((((((P1.add P2).sub P3).sub Q1).sub Q2).sub Q3).add Q4).add Q5
  have H2 : Tendsto sPrim (𝓝[>] 0) (𝓝 _) := H.congr fun y => by unfold sPrim; ring
  convert H2 using 2
  simp only [Li_four_one, Li_zero, sub_zero, log_one, zero_mul]
  ring

private theorem tendsto_sPrim_half : Tendsto sPrim (𝓝[<] (1 / 2)) (𝓝 (7 * π ^ 4 / 180)) := by
  have hev : ∀ᶠ y in 𝓝[<] (1 / 2 : ℝ), y ∈ Ioo (0 : ℝ) (1 / 2) := Ioo_mem_nhdsLT (by norm_num)
  have hc : ∀ {g : ℝ → ℝ}, ContinuousAt g (1 / 2) → Tendsto g (𝓝[<] (1 / 2)) (𝓝 (g (1 / 2))) :=
    fun hg => hg.tendsto.mono_left nhdsWithin_le_nhds
  have gy : Tendsto (fun y : ℝ => y) (𝓝[<] (1 / 2)) (𝓝 (1 / 2)) := hc continuousAt_id
  have g1 : Tendsto (fun y : ℝ => 1 - y) (𝓝[<] (1 / 2)) (𝓝 (1 / 2)) := by
    have := hc (g := fun y : ℝ => 1 - y) (by fun_prop)
    norm_num at this ⊢
    exact this
  have gL : Tendsto (fun y : ℝ => y / (y - 1)) (𝓝[<] (1 / 2)) (𝓝 (-1)) := by
    have := hc (g := fun y : ℝ => y / (y - 1))
      (continuousAt_id.div (continuousAt_id.sub continuousAt_const) (by norm_num))
    norm_num at this ⊢
    exact this
  have sy : ∀ᶠ y in 𝓝[<] (1 / 2 : ℝ), y ∈ Icc (-1 : ℝ) 1 :=
    hev.mono fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have s1 : ∀ᶠ y in 𝓝[<] (1 / 2 : ℝ), 1 - y ∈ Icc (-1 : ℝ) 1 :=
    hev.mono fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have sL : ∀ᶠ y in 𝓝[<] (1 / 2 : ℝ), y / (y - 1) ∈ Icc (-1 : ℝ) 1 :=
    hev.mono fun y hy => abs_le.1 (data_landen hy.1 hy.2).2.1.le
  have hm : (1 / 2 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hm' : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have ly : Tendsto (fun y : ℝ => log y) (𝓝[<] (1 / 2)) (𝓝 (log (1 / 2))) :=
    hc (continuousAt_log (by norm_num))
  have l1 : Tendsto (fun y : ℝ => log (1 - y)) (𝓝[<] (1 / 2)) (𝓝 (log (1 / 2))) := by
    have := hc (g := fun y : ℝ => log (1 - y)) (by fun_prop (disch := norm_num))
    norm_num at this ⊢
    exact this
  have lL : Tendsto (fun y : ℝ => log (y / (y - 1))) (𝓝[<] (1 / 2)) (𝓝 0) := by
    have := ((continuousAt_log (by norm_num : (-1 : ℝ) ≠ 0)).tendsto).comp gL
    rw [Real.log_neg_eq_log, log_one] at this
    exact this
  have P1 := ((tendsto_Li_comp (k := 4) (by norm_num) hm gy sy).sub
    (ly.mul (tendsto_Li_comp (k := 3) (by norm_num) hm gy sy))).const_mul (-4)
  have P2 := ((tendsto_Li_comp (k := 4) (by norm_num) hm g1 s1).sub
    (l1.mul (tendsto_Li_comp (k := 3) (by norm_num) hm g1 s1))).const_mul 4
  have P3 := ((tendsto_Li_comp (k := 4) (by norm_num) hm' gL sL).sub
    (lL.mul (tendsto_Li_comp (k := 3) (by norm_num) hm' gL sL))).const_mul 4
  have Q1 := (((tendsto_Li_comp (k := 2) (by norm_num) hm gy sy).const_mul 4).mul ly).mul l1
  have Q2 := ((ly.pow 2).mul (l1.pow 2)).div_const 2
  have Q3 := (ly.const_mul 2).mul (l1.pow 3)
  have Q4 := (l1.pow 4).div_const 2
  have Q5 := (l1.pow 2).const_mul (π ^ 2 / 3)
  have H := ((((((P1.add P2).sub P3).sub Q1).sub Q2).sub Q3).add Q4).add Q5
  have H2 : Tendsto sPrim (𝓝[<] (1 / 2)) (𝓝 _) := H.congr fun y => by unfold sPrim; ring
  convert H2 using 2
  rw [Li_four_neg_one, show Li 2 (1 / 2) = π ^ 2 / 12 - log 2 ^ 2 / 2 from Li₂_one_half,
    one_div, Real.log_inv]
  ring

/-- The split integral `∫₀^{1/2} (log y log² (1 - y)/y + log (1 - y) log² y/(1 - y)) = -π⁴/180`. -/
private theorem intervalIntegrable_and_integral_sHalf :
    IntervalIntegrable (fun y => log y * log (1 - y) ^ 2 / y + log (1 - y) * log y ^ 2 / (1 - y))
        volume 0 (1 / 2) ∧
      ∫ y in (0 : ℝ)..(1 / 2), (log y * log (1 - y) ^ 2 / y + log (1 - y) * log y ^ 2 / (1 - y)) =
        -(π ^ 4 / 180) := by
  have h := intervalIntegrable_and_integral_eq_of_nonpos' (by norm_num)
    (fun y hy => hasDerivAt_sPrim hy) (fun y hy => ?_) tendsto_sPrim_zero tendsto_sPrim_half
  · refine ⟨h.1, ?_⟩
    rw [h.2]
    ring
  · obtain ⟨h0, h1⟩ := hy
    have a : log y < 0 := log_neg h0 (by linarith)
    have b : log (1 - y) < 0 := log_neg (by linarith) (by linarith)
    have c : 0 < 1 - y := by linarith
    have e1 : log y * log (1 - y) ^ 2 / y ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg a.le (sq_nonneg _)) h0.le
    have e2 : log (1 - y) * log y ^ 2 / (1 - y) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg b.le (sq_nonneg _)) c.le
    linarith

private theorem measurable_A :
    Measurable fun y : ℝ => log y * log (1 - y) ^ 2 / y := by fun_prop

private theorem measurable_B :
    Measurable fun y : ℝ => log (1 - y) * log y ^ 2 / (1 - y) := by fun_prop

private theorem sign_A {y : ℝ} (hy : y ∈ Ι (0 : ℝ) (1 / 2)) :
    log y * log (1 - y) ^ 2 / y ≤ 0 ∧ log (1 - y) * log y ^ 2 / (1 - y) ≤ 0 := by
  rw [uIoc_of_le (by norm_num)] at hy
  obtain ⟨h0, h1⟩ := hy
  have a : log y ≤ 0 := log_nonpos h0.le (by linarith)
  have b : log (1 - y) ≤ 0 := log_nonpos (by linarith) (by linarith)
  exact ⟨div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg a (sq_nonneg _)) h0.le,
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg b (sq_nonneg _))
      (by linarith)⟩

/-- `log y log² (1 - y) / y` is interval integrable on `[0, 1]`, with integral `-π⁴/180`. -/
theorem intervalIntegrable_and_integral_log_mul_log_one_sub_sq_div :
    IntervalIntegrable (fun y => log y * log (1 - y) ^ 2 / y) volume 0 1 ∧
      ∫ y in (0 : ℝ)..1, log y * log (1 - y) ^ 2 / y = -(π ^ 4 / 180) := by
  obtain ⟨hs, hv⟩ := intervalIntegrable_and_integral_sHalf
  have hae : ∀ᵐ y ∂(volume.restrict (Ι (0 : ℝ) (1 / 2))), y ∈ Ι (0 : ℝ) (1 / 2) :=
    (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun _ h => h)
  have hA : IntervalIntegrable (fun y => log y * log (1 - y) ^ 2 / y) volume 0 (1 / 2) := by
    refine hs.mono_fun measurable_A.aestronglyMeasurable (hae.mono fun y hy => ?_)
    obtain ⟨a, b⟩ := sign_A hy
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonpos a, abs_of_nonpos (by linarith)]
    linarith
  have hB : IntervalIntegrable (fun y => log (1 - y) * log y ^ 2 / (1 - y)) volume 0 (1 / 2) := by
    refine hs.mono_fun measurable_B.aestronglyMeasurable (hae.mono fun y hy => ?_)
    obtain ⟨a, b⟩ := sign_A hy
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonpos b, abs_of_nonpos (by linarith)]
    linarith
  have hA' : IntervalIntegrable (fun y => log y * log (1 - y) ^ 2 / y) volume (1 / 2) 1 := by
    have := (hB.comp_sub_left 1).symm
    norm_num at this
    convert this using 1
  have hI : ∫ y in (1 / 2 : ℝ)..1, log y * log (1 - y) ^ 2 / y =
      ∫ y in (0 : ℝ)..(1 / 2), log (1 - y) * log y ^ 2 / (1 - y) := by
    have := intervalIntegral.integral_comp_sub_left
      (fun y => log y * log (1 - y) ^ 2 / y) (a := 0) (b := 1 / 2) 1
    norm_num at this
    rw [← this]
  refine ⟨hA.trans hA', ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hA hA', hI,
    ← intervalIntegral.integral_add hA hB, hv]

/-- `∫₀¹ log u log² (1 - u²) / u = -π⁴/720`, by the substitution `y = u²`. -/
theorem intervalIntegrable_and_integral_log_mul_log_one_sub_sq_sq_div :
    IntervalIntegrable (fun u => log u * (log (1 - u) + log (1 + u)) ^ 2 / u) volume 0 1 ∧
      ∫ u in (0 : ℝ)..1, log u * (log (1 - u) + log (1 + u)) ^ 2 / u = -(π ^ 4 / 720) := by
  obtain ⟨hi, hv⟩ := intervalIntegrable_and_integral_log_mul_log_one_sub_sq_div
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt (fun u : ℝ => u ^ 2) (2 * x) (Ioo 0 1) x :=
    fun x _ => by simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => u ^ 2) (Ioo 0 1) := fun a ha b hb h =>
    (pow_left_inj₀ ha.1.le hb.1.le two_ne_zero).1 h
  have himg : (fun u : ℝ => u ^ 2) '' Ioo 0 1 = Ioo 0 1 := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨by have := hu.1; positivity, by nlinarith [hu.1, hu.2]⟩
    · intro hy
      refine ⟨Real.sqrt y, ⟨Real.sqrt_pos.2 hy.1, ?_⟩, Real.sq_sqrt hy.1.le⟩
      rw [Real.sqrt_lt' one_pos]
      simpa using hy.2
  have hpt : ∀ u ∈ Ioo (0 : ℝ) 1, |2 * u| • (log (u ^ 2) * log (1 - u ^ 2) ^ 2 / u ^ 2) =
      4 * (log u * (log (1 - u) + log (1 + u)) ^ 2 / u) := by
    intro u hu
    obtain ⟨h0, h1⟩ := hu
    rw [smul_eq_mul, abs_of_pos (by positivity), log_pow,
      show 1 - u ^ 2 = (1 - u) * (1 + u) by ring, log_mul (by linarith) (by linarith)]
    field_simp
    push_cast
    ring
  have hiA : IntegrableOn (fun y => log y * log (1 - y) ^ 2 / y) (Ioo 0 1) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hi
    exact hi.mono_set Ioo_subset_Ioc_self
  have hi2 := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hd hinj
    (fun y => log y * log (1 - y) ^ 2 / y)).1 (by rwa [himg])
  have hi3 : IntegrableOn (fun u => log u * (log (1 - u) + log (1 + u)) ^ 2 / u) (Ioo 0 1) := by
    have : IntegrableOn (fun u : ℝ => |2 * u| • (log (u ^ 2) * log (1 - u ^ 2) ^ 2 / u ^ 2) / 4)
        (Ioo 0 1) := hi2.div_const 4
    refine this.congr_fun (fun u hu => ?_) measurableSet_Ioo
    simp only
    rw [hpt u hu]
    ring
  have hv2 := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hinj
    (fun y => log y * log (1 - y) ^ 2 / y)
  rw [himg, setIntegral_congr_fun measurableSet_Ioo hpt, integral_const_mul] at hv2
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one, IntegrableOn,
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact hi3
  · rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at hv
    rw [hv] at hv2
    linarith

end QED.Polylog
