/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.ExtraIntegrals
public import QED.Polylog.LogLiDiv
public import QED.Polylog.LogLogSq
public import QED.Polylog.LiCalculus
import QED.Polylog.Reflection
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Set (d), master `I₂`: two weight-four integrals for the `U`-part of `P'(0)`

After the substitutions of `QED.ThreeLoopD.SetDMastersI2P1USub`, the dilogarithmic part of the
`y₄`-primitive `Θ` of `QED.ThreeLoopD.SetDMastersI2P1ULines` reduces to the one-dimensional
integrals

* `∫₀¹ (Li₂ z + 7/2 log² (1 - z)) (-log z) / (z (1 - z)) dz = 7 π⁴ / 60`,
* `∫₀¹ (-log (1 - z)) K(z) / (z (1 - z)) dz = 13 π⁴ / 120`,
  `K(z) = log² z / 2 + 2 (π² / 6 - Li₂ z) = ∫_z^1 (-log s - 2 log (1 - s)) / s ds`.

Both split by `1 / (z (1 - z)) = 1 / z + 1 / (1 - z)`, the reflection `z ↦ 1 - z` and the
dilogarithm reflection formula into the known integrals of `QED.Polylog.LogLiDiv` and
`QED.Polylog.LogLogSq`, plus `∫₀¹ log (1 - z) Li₂ z / z = -π⁴ / 72` (`-(Li₂ z)² / 2` is a
primitive).

## Main results

* `QED.ThreeLoopD.i2P1UZ_log_one_sub_mul_Li₂_div`.
* `QED.ThreeLoopD.i2P1UZ_plus`, `QED.ThreeLoopD.i2P1UZ_minus`.
* `QED.ThreeLoopD.i2P1UZ_lint_inv`, `QED.ThreeLoopD.i2P1UZ_lint_h`: the inner integrals
  `∫_z^1 ds / s = -log z` and `∫_z^1 (-log s - 2 log (1 - s)) / s ds = K(z)`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology QED.Polylog

namespace QED.ThreeLoopD

/-- Changing an integrand on `(0, 1)` only. -/
theorem i2P1UZ_congr {f g : ℝ → ℝ} (h : ∀ z ∈ Ioo (0 : ℝ) 1, f z = g z)
    (hg : IntervalIntegrable g volume 0 1) :
    IntervalIntegrable f volume 0 1 ∧ ∫ z in (0 : ℝ)..1, f z = ∫ z in (0 : ℝ)..1, g z := by
  have hg' : IntegrableOn g (Ioo (0 : ℝ) 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hg).mono_set
      Ioo_subset_Ioc_self
  have hf' : IntegrableOn f (Ioo (0 : ℝ) 1) :=
    hg'.congr_fun (fun z hz => (h z hz).symm) measurableSet_Ioo
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
    ((integrableOn_Ioc_iff_integrableOn_Ioo (f := f)).2 hf'), ?_⟩
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

/-- The reflection `z ↦ 1 - z` on `(0, 1)`. -/
theorem i2P1UZ_reflect {f : ℝ → ℝ} {c : ℝ}
    (h : IntervalIntegrable f volume 0 1 ∧ ∫ z in (0 : ℝ)..1, f z = c) :
    IntervalIntegrable (fun z => f (1 - z)) volume 0 1 ∧
      ∫ z in (0 : ℝ)..1, f (1 - z) = c := by
  refine ⟨?_, ?_⟩
  · have := h.1.comp_sub_left 1
    rw [sub_zero, sub_self] at this
    exact this.symm
  · rw [intervalIntegral.integral_comp_sub_left (fun z => f z) 1, sub_self, sub_zero, h.2]

/-- `∫₀¹ log (1 - z) Li₂ z / z = -π⁴ / 72`: `-(Li₂ z)² / 2` is a primitive. -/
theorem i2P1UZ_log_one_sub_mul_Li₂_div :
    IntervalIntegrable (fun z => log (1 - z) * Li₂ z / z) volume 0 1 ∧
      ∫ z in (0 : ℝ)..1, log (1 - z) * Li₂ z / z = -(π ^ 4 / 72) := by
  have h := intervalIntegrable_and_integral_eq_of_nonpos (F := fun z => -(Li₂ z ^ 2 / 2))
    (f := fun z => log (1 - z) * Li₂ z / z)
    (fun z hz => by
      have := ((hasDerivAt_Li₂' hz).pow 2).div_const 2 |>.neg
      refine this.congr_deriv ?_
      have := hz.1.ne'
      field_simp
      ring)
    (fun z hz => div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
      (log_nonpos (by linarith [hz.2]) (by linarith [hz.1])) (Li₂_nonneg hz.1.le)) hz.1.le)
    ((tendsto_Li₂_zero_right.pow 2).div_const 2).neg ((tendsto_Li₂_one_left.pow 2).div_const 2).neg
  refine ⟨h.1, ?_⟩
  rw [h.2]
  ring

theorem i2P1UZ_log_mul_Li₂_div :
    IntervalIntegrable (fun z => log z * Li₂ z / z) volume 0 1 ∧
      ∫ z in (0 : ℝ)..1, log z * Li₂ z / z = -(π ^ 4 / 90) :=
  intervalIntegrable_and_integral_log_mul_Li_two_div

/-- `∫₀¹ log z Li₂ z / (1 - z) = -π⁴ / 120`, by `z ↦ 1 - z` and the reflection formula. -/
theorem i2P1UZ_log_mul_Li₂_div_one_sub :
    IntervalIntegrable (fun z => log z * Li₂ z / (1 - z)) volume 0 1 ∧
      ∫ z in (0 : ℝ)..1, log z * Li₂ z / (1 - z) = -(π ^ 4 / 120) := by
  have h1 := intervalIntegrable_and_integral_log_one_sub_div
  have h2 := intervalIntegrable_and_integral_log_mul_log_one_sub_sq_div
  have h3 := i2P1UZ_log_one_sub_mul_Li₂_div
  have hi := ((h1.1.const_mul (π ^ 2 / 6)).sub h2.1).sub h3.1
  have hc := i2P1UZ_congr (f := fun z => log (1 - z) * Li₂ (1 - z) / z) (fun z hz => by
    have hr := Li₂_add_Li₂_one_sub hz.1.le hz.2.le
    rw [show Li₂ (1 - z) = π ^ 2 / 6 - log z * log (1 - z) - Li₂ z by linarith]
    have := hz.1.ne'
    field_simp) hi
  have hv : ∫ z in (0 : ℝ)..1, log (1 - z) * Li₂ (1 - z) / z = -(π ^ 4 / 120) := by
    rw [hc.2, intervalIntegral.integral_sub ((h1.1.const_mul _).sub h2.1) h3.1,
      intervalIntegral.integral_sub (h1.1.const_mul _) h2.1, intervalIntegral.integral_const_mul,
      h1.2, h2.2, h3.2]
    ring
  have := i2P1UZ_reflect ⟨hc.1, hv⟩
  simp only [sub_sub_cancel] at this
  exact this

/-- `∫₀¹ log z log² (1 - z) / (1 - z) = -π⁴ / 45`. -/
theorem i2P1UZ_log_mul_log_one_sub_sq_div_one_sub :
    IntervalIntegrable (fun z => log z * log (1 - z) ^ 2 / (1 - z)) volume 0 1 ∧
      ∫ z in (0 : ℝ)..1, log z * log (1 - z) ^ 2 / (1 - z) = -(π ^ 4 / 45) := by
  have h := i2P1UZ_reflect intervalIntegrable_and_integral_log_sq_mul_log_one_sub_div
  simp only [sub_sub_cancel] at h
  have hc := i2P1UZ_congr (f := fun z => log z * log (1 - z) ^ 2 / (1 - z))
    (fun z _ => by ring) h.1
  exact ⟨hc.1, hc.2.trans h.2⟩

/-- `∫₀¹ log (1 - z) log² z / (1 - z) = -π⁴ / 180`. -/
theorem i2P1UZ_log_one_sub_mul_log_sq_div_one_sub :
    IntervalIntegrable (fun z => log (1 - z) * log z ^ 2 / (1 - z)) volume 0 1 ∧
      ∫ z in (0 : ℝ)..1, log (1 - z) * log z ^ 2 / (1 - z) = -(π ^ 4 / 180) := by
  have h := i2P1UZ_reflect intervalIntegrable_and_integral_log_mul_log_one_sub_sq_div
  simp only [sub_sub_cancel] at h
  exact h

/-- **The `+` integral**: `∫₀¹ (Li₂ z + 7/2 log² (1 - z)) (-log z) / (z (1 - z)) = 7 π⁴ / 60`. -/
theorem i2P1UZ_plus :
    IntervalIntegrable (fun z => (Li₂ z + 7 / 2 * log (1 - z) ^ 2) * (-log z) / (z * (1 - z)))
        volume 0 1 ∧
      ∫ z in (0 : ℝ)..1, (Li₂ z + 7 / 2 * log (1 - z) ^ 2) * (-log z) / (z * (1 - z)) =
        7 * π ^ 4 / 60 := by
  have ha := i2P1UZ_log_mul_Li₂_div
  have hb := i2P1UZ_log_mul_Li₂_div_one_sub
  have hc := intervalIntegrable_and_integral_log_mul_log_one_sub_sq_div
  have hd := i2P1UZ_log_mul_log_one_sub_sq_div_one_sub
  have hi := (((ha.1.const_mul (-1)).sub hb.1).sub (hc.1.const_mul (7 / 2))).sub
    (hd.1.const_mul (7 / 2))
  have hk := i2P1UZ_congr
    (f := fun z => (Li₂ z + 7 / 2 * log (1 - z) ^ 2) * (-log z) / (z * (1 - z))) (fun z hz => by
      have := hz.1.ne'
      have : 1 - z ≠ 0 := by linarith [hz.2]
      field_simp
      ring) hi
  refine ⟨hk.1, ?_⟩
  rw [hk.2, intervalIntegral.integral_sub (((ha.1.const_mul _).sub hb.1).sub
      (hc.1.const_mul _)) (hd.1.const_mul _), intervalIntegral.integral_sub
      ((ha.1.const_mul _).sub hb.1) (hc.1.const_mul _),
    intervalIntegral.integral_sub (ha.1.const_mul _) hb.1, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, ha.2, hb.2, hc.2,
    hd.2]
  ring

/-- `K(z) = log² z / 2 + 2 (π² / 6 - Li₂ z) = ∫_z^1 (-log s - 2 log (1 - s)) / s ds`. -/
noncomputable def i2P1UZK (z : ℝ) : ℝ := log z ^ 2 / 2 + 2 * (π ^ 2 / 6 - Li₂ z)

/-- **The `-` integral**: `∫₀¹ (-log (1 - z)) K(z) / (z (1 - z)) = 13 π⁴ / 120`. -/
theorem i2P1UZ_minus :
    IntervalIntegrable (fun z => -log (1 - z) * i2P1UZK z / (z * (1 - z))) volume 0 1 ∧
      ∫ z in (0 : ℝ)..1, -log (1 - z) * i2P1UZK z / (z * (1 - z)) = 13 * π ^ 4 / 120 := by
  have h1 := intervalIntegrable_and_integral_log_sq_mul_log_one_sub_div
  have h2 := i2P1UZ_log_one_sub_mul_log_sq_div_one_sub
  have hL := intervalIntegrable_and_integral_log_one_sub_div
  have hM := i2P1UZ_log_one_sub_mul_Li₂_div
  have ha := intervalIntegrable_and_integral_log_mul_Li_two_div
  -- `f₃ = log (1 - z) (π² / 6 - Li₂ z) / z`
  have h3 := i2P1UZ_congr (f := fun z => log (1 - z) * (π ^ 2 / 6 - Li₂ z) / z)
    (fun z hz => by
      have := hz.1.ne'
      field_simp) ((hL.1.const_mul (π ^ 2 / 6)).sub hM.1)
  have h3v : ∫ z in (0 : ℝ)..1, log (1 - z) * (π ^ 2 / 6 - Li₂ z) / z = -(π ^ 4 / 72) := by
    rw [h3.2, intervalIntegral.integral_sub (hL.1.const_mul _) hM.1,
      intervalIntegral.integral_const_mul, hL.2, hM.2]
    ring
  -- `f₄ = log (1 - z) (π² / 6 - Li₂ z) / (1 - z)`, reflected
  have h4 := i2P1UZ_congr (f := fun z => log z * (π ^ 2 / 6 - Li₂ (1 - z)) / z)
    (fun z hz => by
      have hr := Li₂_add_Li₂_one_sub hz.1.le hz.2.le
      rw [show π ^ 2 / 6 - Li₂ (1 - z) = log z * log (1 - z) + Li₂ z by linarith]
      have := hz.1.ne'
      field_simp
      rw [Li_two]) (h1.1.add ha.1)
  have h4v : ∫ z in (0 : ℝ)..1, log z * (π ^ 2 / 6 - Li₂ (1 - z)) / z = -(π ^ 4 / 30) := by
    rw [h4.2, intervalIntegral.integral_add h1.1 ha.1, h1.2, ha.2]
    ring
  have h4r := i2P1UZ_reflect ⟨h4.1, h4v⟩
  simp only [sub_sub_cancel] at h4r
  have hi := ((((h1.1.const_mul (1 / 2)).add (h2.1.const_mul (1 / 2))).add
    (h3.1.const_mul 2)).add (h4r.1.const_mul 2)).const_mul (-1)
  have hk := i2P1UZ_congr (f := fun z => -log (1 - z) * i2P1UZK z / (z * (1 - z)))
    (fun z hz => by
      have := hz.1.ne'
      have : 1 - z ≠ 0 := by linarith [hz.2]
      simp only [i2P1UZK]
      field_simp
      ring) hi
  refine ⟨hk.1, ?_⟩
  rw [hk.2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (((h1.1.const_mul _).add (h2.1.const_mul _)).add
      (h3.1.const_mul _)) (h4r.1.const_mul _), intervalIntegral.integral_add
      ((h1.1.const_mul _).add (h2.1.const_mul _)) (h3.1.const_mul _),
    intervalIntegral.integral_add (h1.1.const_mul _) (h2.1.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, h1.2, h2.2, h3v,
    h4r.2]
  ring

/-- Lower integral of a nonnegative interval integrand on `(a, b)`. -/
theorem i2P1UZ_lint_of {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hnn : ∀ x ∈ Ioo a b, 0 ≤ f x)
    (hv : ∫ x in a..b, f x = c) :
    ∫⁻ x in Ioo a b, ENNReal.ofReal (f x) = ENNReal.ofReal c := by
  have hIo : IntegrableOn f (Ioo a b) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hf).mono_set Ioo_subset_Ioc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hIo
    (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx using hnn x hx),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab, hv]

/-- `∫_z^1 ds / s = -log z`. -/
theorem i2P1UZ_lint_inv {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ∫⁻ s in Ioo z 1, ENNReal.ofReal (1 / s) = ENNReal.ofReal (-log z) := by
  have hd : ∀ s ∈ Ioo z 1, HasDerivAt log (1 / s) s := fun s hs => by
    simpa [one_div] using hasDerivAt_log (by linarith [hs.1] : s ≠ 0)
  have h0 : Tendsto log (𝓝[>] z) (𝓝 (log z)) :=
    ((continuousAt_log hz.ne').tendsto).mono_left nhdsWithin_le_nhds
  have h1 : Tendsto log (𝓝[<] 1) (𝓝 (log 1)) :=
    ((continuousAt_log one_ne_zero).tendsto).mono_left nhdsWithin_le_nhds
  have h := intervalIntegrable_and_integral_eq_of_nonneg' hz1 hd
    (fun s hs => div_nonneg zero_le_one (by linarith [hs.1])) h0 h1
  refine i2P1UZ_lint_of hz1.le h.1 (fun s hs => div_nonneg zero_le_one (by linarith [hs.1])) ?_
  rw [h.2, log_one, zero_sub]

/-- `∫_z^1 (-log s - 2 log (1 - s)) / s ds = K(z)`. -/
theorem i2P1UZ_lint_h {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ∫⁻ s in Ioo z 1, ENNReal.ofReal ((-log s - 2 * log (1 - s)) / s) =
      ENNReal.ofReal (i2P1UZK z) := by
  have hnn : ∀ s ∈ Ioo z 1, 0 ≤ (-log s - 2 * log (1 - s)) / s := fun s hs => by
    have h0 : 0 < s := by linarith [hs.1]
    have := log_nonpos h0.le hs.2.le
    have := log_nonpos (by linarith [hs.2]) (by linarith : 1 - s ≤ 1)
    exact div_nonneg (by linarith) h0.le
  have hd : ∀ s ∈ Ioo z 1, HasDerivAt (fun s => -(log s ^ 2 / 2) + 2 * Li₂ s)
      ((-log s - 2 * log (1 - s)) / s) s := fun s hs => by
    have h0 : 0 < s := by linarith [hs.1]
    have := (((hasDerivAt_log h0.ne').pow 2).div_const 2).neg.add
      ((hasDerivAt_Li₂' ⟨h0, hs.2⟩).const_mul 2)
    refine this.congr_deriv ?_
    field_simp
    ring
  have hc : ContinuousAt (fun s => -(log s ^ 2 / 2) + 2 * Li₂ s) z :=
    ((((continuousAt_log hz.ne').pow 2).div_const 2).neg).add
      ((continuousOn_Li₂.continuousAt (Icc_mem_nhds (by linarith) hz1)).const_mul 2)
  have h1 : Tendsto (fun s => -(log s ^ 2 / 2) + 2 * Li₂ s) (𝓝[<] 1)
      (𝓝 (-(log 1 ^ 2 / 2) + 2 * (π ^ 2 / 6))) := by
    have hl : Tendsto log (𝓝[<] 1) (𝓝 (log 1)) :=
      ((continuousAt_log one_ne_zero).tendsto).mono_left nhdsWithin_le_nhds
    exact ((hl.pow 2).div_const 2).neg.add (tendsto_Li₂_one_left.const_mul 2)
  have h := intervalIntegrable_and_integral_eq_of_nonneg' hz1 hd hnn
    (hc.tendsto.mono_left nhdsWithin_le_nhds) h1
  refine i2P1UZ_lint_of hz1.le h.1 hnn ?_
  rw [h.2, i2P1UZK, log_one]
  ring

end QED.ThreeLoopD
