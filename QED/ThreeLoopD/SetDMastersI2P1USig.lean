/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI2P0Val
public import QED.ThreeLoopD.SetDMastersI2P1UVal
import QED.Polylog.Reflection
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Set (d), master `I₂`: `∫∫ (1 - w) (-log σ) Ψ dx dw = 2 π⁴ / 5`

With `σ = A B + (A + B) C = α₁ α₂ α₃` (`α₁ = (1 - w) x`, `α₂ = w`, `α₃ = (1 - w)(1 - x)`),
`-log σ = Σᵢ (-log αᵢ)`. The function `Ψ(A, B, C)` of `QED.ThreeLoopD.SetDMastersI2P0Lines` is
symmetric, so the three terms are exchanged by the maps of
`QED.ThreeLoopD.SetDMastersI2P1USub` and each equals the `α₂ = w` term. That one is
`∫₀¹ (-log w) 2 φ(1) dw` with `2 φ(1) = 2 Li₂ w / w + 2 log w log (1 - w) / w + log² w / (1 - w)`
from `QED.ThreeLoopD.SetDMastersI2P0Val`, i.e. `π⁴/45 + 2π⁴/45 + π⁴/15 = 2π⁴/15`, using
`∫₀¹ log³ w / (1 - w) = -π⁴ / 15` (`QED.ThreeLoopD.i2P1USig_log_cube`, by parts from
`∫₀¹ log² w log (1 - w) / w = -π⁴ / 45`).

This makes `(1 - w) log σ / 𝒰²` integrable over the domain of `I₂`.

## Main results

* `QED.ThreeLoopD.i2P1USig_log_cube`.
* `QED.ThreeLoopD.i2P0Psi_swap₁₂`, `QED.ThreeLoopD.i2P0Psi_swap₂₃`.
* `QED.ThreeLoopD.i2P1USig_lint`: the lower integral of `(1 - w) (-log σ) Ψ` is `2 π⁴ / 5`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology QED.Polylog Function
open scoped ENNReal

namespace QED.ThreeLoopD

theorem i2P1USig_tendsto_zero :
    Tendsto (fun u : ℝ => log (1 - u) * log u ^ 3) (𝓝[>] 0) (𝓝 0) := by
  have h1 := tendsto_log_one_sub_div_zero'
  have h2 := (tendsto_log_mul_rpow_nhdsGT_zero (r := 1 / 3) (by norm_num)).pow 3
  rw [zero_pow (by norm_num)] at h2
  have := h1.mul h2
  rw [mul_zero] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
  have hc : (u ^ (1 / 3 : ℝ)) ^ 3 = u := by
    rw [← rpow_natCast, ← rpow_mul hu.le]
    norm_num
  rw [mul_pow, hc]
  field_simp

theorem i2P1USig_tendsto_one :
    Tendsto (fun u : ℝ => log (1 - u) * log u ^ 3) (𝓝[<] 1) (𝓝 0) := by
  have hl : Tendsto (fun u : ℝ => log u) (𝓝[<] 1) (𝓝 0) := by
    have := ((continuousAt_log one_ne_zero).tendsto).mono_left (nhdsWithin_le_nhds (s := Iio 1))
    rwa [log_one] at this
  have := tendsto_log_mul_log_one_sub_one.mul (hl.pow 2)
  rw [zero_mul] at this
  refine this.congr' (Eventually.of_forall fun u => ?_)
  ring

/-- **`∫₀¹ log³ u / (1 - u) = -π⁴ / 15`**: `log³ u / (1 - u)` is the derivative of
`-log (1 - u) log³ u + 3 ∫₀ᵘ log (1 - x) log² x / x dx`. -/
theorem i2P1USig_log_cube :
    IntervalIntegrable (fun u => log u ^ 3 / (1 - u)) volume 0 1 ∧
      ∫ u in (0 : ℝ)..1, log u ^ 3 / (1 - u) = -(π ^ 4 / 15) := by
  obtain ⟨hi, hv⟩ := intervalIntegrable_and_integral_log_sq_mul_log_one_sub_div
  set p : ℝ → ℝ := fun x => log x ^ 2 * log (1 - x) / x with hp
  have hpc : ContinuousOn p (Ioo 0 1) := by
    refine ContinuousOn.div ?_ continuousOn_id fun x hx => hx.1.ne'
    exact ((continuousOn_log.mono fun x hx => hx.1.ne').pow 2).mul
      (continuousOn_log.comp (by fun_prop) fun x hx => by
        simp only [mem_compl_iff, mem_singleton_iff]; linarith [hx.2])
  set G : ℝ → ℝ := fun u => ∫ x in (0 : ℝ)..u, p x with hG
  have hGc : ContinuousOn G (Icc 0 1) := by
    have := intervalIntegral.continuousOn_primitive_interval' hi
      (left_mem_uIcc (a := (0 : ℝ)) (b := 1))
    rwa [uIcc_of_le zero_le_one] at this
  have hGd : ∀ u ∈ Ioo (0 : ℝ) 1, HasDerivAt G (p u) u := fun u hu =>
    intervalIntegral.integral_hasDerivAt_right (hi.mono_set (by
      rw [uIcc_of_le zero_le_one, uIcc_of_le hu.1.le]
      exact Icc_subset_Icc le_rfl hu.2.le))
      ((hpc.mono le_rfl).stronglyMeasurableAtFilter isOpen_Ioo u hu)
      (hpc.continuousAt (isOpen_Ioo.mem_nhds hu))
  have h := intervalIntegrable_and_integral_eq_of_nonpos
    (F := fun u => -(log (1 - u) * log u ^ 3) + 3 * G u) (f := fun u => log u ^ 3 / (1 - u))
    (A := -0 + 3 * G 0) (B := -0 + 3 * G 1)
    (fun u hu => by
      have h1 : 0 < 1 - u := by linarith [hu.2]
      have hd := ((((hasDerivAt_id u).const_sub 1).log h1.ne').mul
        ((hasDerivAt_log hu.1.ne').pow 3)).neg.add ((hGd u hu).const_mul 3)
      refine hd.congr_deriv ?_
      simp only [hp, id, Pi.pow_apply]
      field_simp
      ring)
    (fun u hu => div_nonpos_of_nonpos_of_nonneg
      (Odd.pow_nonpos (by decide) (log_nonpos hu.1.le hu.2.le)) (by linarith [hu.2]))
    (i2P1USig_tendsto_zero.neg.add (((hGc 0 ⟨le_rfl, zero_le_one⟩).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Iio 1, isOpen_Iio, by norm_num, fun y hy =>
        ⟨le_of_lt hy.2, le_of_lt hy.1⟩⟩)).tendsto.const_mul 3))
    (i2P1USig_tendsto_one.neg.add (((hGc 1 ⟨zero_le_one, le_rfl⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLT one_pos)).tendsto.const_mul 3))
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [hG, intervalIntegral.integral_same, hv]
  ring

/-- `∫₀¹ (-log w) 2 φ(1) dw = 2 π⁴ / 15`. -/
theorem i2P1USig_w :
    ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (-log w * (2 * i2P0Phi w 1)) =
      ENNReal.ofReal (2 * π ^ 4 / 15) := by
  have heq : ∀ w ∈ Ioo (0 : ℝ) 1, 2 * i2P0Phi w 1 =
      2 * (Li₂ w / w) + 2 * (log w * log (1 - w) / w) + log w ^ 2 / (1 - w) := fun w hw => by
    have hr := Li₂_add_Li₂_one_sub hw.1.le hw.2.le
    have h0 := hw.1.ne'
    have h1 : 1 - w ≠ 0 := by linarith [hw.2]
    rw [i2P0Phi_one, show Li₂ (1 - w) = π ^ 2 / 6 - log w * log (1 - w) - Li₂ w by linarith]
    field_simp
    ring
  have hg : ∀ w ∈ Ioo (0 : ℝ) 1, 0 ≤ 2 * (Li₂ w / w) + 2 * (log w * log (1 - w) / w) +
      log w ^ 2 / (1 - w) := fun w hw => by
    have h1 : 0 < 1 - w := by linarith [hw.2]
    have hl1 := log_nonpos hw.1.le hw.2.le
    have hl2 := log_nonpos h1.le (by linarith [hw.1])
    have := Li₂_nonneg hw.1.le
    have := mul_nonneg_of_nonpos_of_nonpos hl1 hl2
    have := hw.1
    positivity
  have ha := i2P1UZ_log_mul_Li₂_div
  have hb := intervalIntegrable_and_integral_log_sq_mul_log_one_sub_div
  have hc := i2P1USig_log_cube
  have hk := i2P1UZ_congr (f := fun w => -log w * (2 * i2P0Phi w 1)) (fun w hw => by
      rw [heq w hw]
      have := hw.1.ne'
      have : 1 - w ≠ 0 := by linarith [hw.2]
      field_simp
      ring) (((ha.1.const_mul (-2)).sub (hb.1.const_mul 2)).sub hc.1)
  refine i2P1UZ_lint_of zero_le_one hk.1 (fun w hw => by
    rw [heq w hw]
    exact mul_nonneg (by linarith [log_nonpos hw.1.le hw.2.le]) (hg w hw)) ?_
  rw [hk.2, intervalIntegral.integral_sub ((ha.1.const_mul _).sub (hb.1.const_mul _)) hc.1,
    intervalIntegral.integral_sub (ha.1.const_mul _) (hb.1.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, ha.2, hb.2, hc.2]
  ring

theorem i2P0Psi_swap₁₂ (A B C : ℝ) : i2P0Psi B A C = i2P0Psi A B C := by
  unfold i2P0Psi
  rw [show B * A + (B + A) * C = A * B + (A + B) * C by ring, show B + A = A + B by ring,
    show B * A = A * B by ring]
  ring

theorem i2P0Psi_swap₂₃ {A B C : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    i2P0Psi A C B = i2P0Psi A B C := by
  unfold i2P0Psi
  rw [show A * C + (A + C) * B = A * B + (A + B) * C by ring, show C + B = B + C by ring]
  field_simp
  ring

theorem measurable_i2P0Q' : Measurable (uncurry i2P0Q) := by
  unfold i2P0Q i2P0Psi
  fun_prop

/-- The `α₂ = w` term. -/
theorem i2P1USig_J₂ :
    ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (-log w * i2P0Q x w) =
      ENNReal.ofReal (2 * π ^ 4 / 15) := by
  rw [i2P1US_swap (f := fun x w => ENNReal.ofReal (-log w * i2P0Q x w))
    (ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable fun p : ℝ × ℝ => -log p.2).mul
      measurable_i2P0Q'))]
  rw [← i2P1USig_w]
  refine setLIntegral_congr_fun measurableSet_Ioo fun w hw => ?_
  have hl : 0 ≤ -log w := by linarith [log_nonpos hw.1.le hw.2.le]
  simp_rw [ENNReal.ofReal_mul hl]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, i2P0_lint_x hw]

/-- The `α₁ = (1 - w) x` term equals the `α₂ = w` term. -/
theorem i2P1USig_J₁ :
    ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (-log ((1 - w) * x) * i2P0Q x w) =
      ENNReal.ofReal (2 * π ^ 4 / 15) := by
  set g : ℝ → ℝ → ℝ≥0∞ := fun u v =>
    ENNReal.ofReal (-log u * i2P0Psi (u * v) (v * (1 - u - v)) (u * (1 - u - v))) with hg
  have hgm : Measurable (uncurry g) := by
    rw [hg]
    unfold i2P0Psi
    fun_prop
  have e1 := i2P1US_xw_A hgm
  have e2 := i2P1US_xw_A' hgm
  rw [← i2P1USig_J₂]
  refine Eq.trans ?_ ((e1.trans e2.symm).trans ?_)
  · refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    refine setLIntegral_congr_fun measurableSet_Ioo fun w hw => ?_
    have hv : 0 ≤ 1 - w := by linarith [hw.2]
    rw [hg]
    simp only
    rw [← ENNReal.ofReal_mul hv, i2P0Q, show (1 - w) * x * w = w * (1 - w) * x by ring,
      show w * (1 - (1 - w) * x - w) = w * (1 - w) * (1 - x) by ring,
      show (1 - w) * x * (1 - (1 - w) * x - w) = (1 - w) ^ 2 * x * (1 - x) by ring]
    congr 1
    ring
  · refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    refine setLIntegral_congr_fun measurableSet_Ioo fun w hw => ?_
    have hv : 0 < 1 - w := by linarith [hw.2]
    rw [hg]
    simp only
    rw [← ENNReal.ofReal_mul hv.le, i2P0Q, show w * ((1 - w) * x) = w * (1 - w) * x by ring,
      show (1 - w) * x * (1 - w - (1 - w) * x) = (1 - w) ^ 2 * x * (1 - x) by ring,
      show w * (1 - w - (1 - w) * x) = w * (1 - w) * (1 - x) by ring,
      i2P0Psi_swap₂₃ (mul_pos (mul_pos hw.1 hv) hx.1).ne'
        (mul_pos (mul_pos hw.1 hv) (by linarith [hx.2] : (0 : ℝ) < 1 - x)).ne'
        (mul_pos (mul_pos (pow_pos hv 2) hx.1) (by linarith [hx.2] : (0 : ℝ) < 1 - x)).ne']
    congr 1
    ring

/-- The `α₃ = (1 - w)(1 - x)` term equals the `α₁` term, by `x ↦ 1 - x`. -/
theorem i2P1USig_J₃ :
    ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (-log ((1 - w) * (1 - x)) * i2P0Q x w) = ENNReal.ofReal (2 * π ^ 4 / 15) := by
  rw [← i2P1USig_J₁, ← i2P1US_reflect 1 (fun x => ∫⁻ w in Ioo (0 : ℝ) 1,
    ENNReal.ofReal (-log ((1 - w) * x) * i2P0Q x w))]
  refine setLIntegral_congr_fun measurableSet_Ioo fun x _ => lintegral_congr fun w => ?_
  rw [i2P0Q, i2P0Q, show w * (1 - w) * (1 - (1 - x)) = w * (1 - w) * x by ring,
    show (1 - w) ^ 2 * (1 - x) * (1 - (1 - x)) = (1 - w) ^ 2 * x * (1 - x) by ring,
    i2P0Psi_swap₁₂]

/-- Splitting a lower double integral of a sum of three nonnegative terms. -/
theorem i2P1U_lint_add3 {f₁ f₂ f₃ : ℝ → ℝ → ℝ} (m₁ : Measurable (uncurry f₁))
    (m₂ : Measurable (uncurry f₂))
    (h₁ : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ w ∈ Ioo (0 : ℝ) 1, 0 ≤ f₁ x w)
    (h₂ : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ w ∈ Ioo (0 : ℝ) 1, 0 ≤ f₂ x w)
    (h₃ : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ w ∈ Ioo (0 : ℝ) 1, 0 ≤ f₃ x w) :
    ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (f₁ x w + f₂ x w + f₃ x w) =
      (∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (f₁ x w)) +
      (∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (f₂ x w)) +
      ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (f₃ x w) := by
  have n₁ : Measurable (uncurry fun x w => ENNReal.ofReal (f₁ x w)) :=
    ENNReal.measurable_ofReal.comp m₁
  have n₂ : Measurable (uncurry fun x w => ENNReal.ofReal (f₂ x w)) :=
    ENNReal.measurable_ofReal.comp m₂
  have e : ∀ x ∈ Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (f₁ x w + f₂ x w + f₃ x w) =
      ((∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (f₁ x w)) +
        ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (f₂ x w)) +
        ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (f₃ x w) := by
    intro x hx
    have k₁ : Measurable fun w => ENNReal.ofReal (f₁ x w) := n₁.comp measurable_prodMk_left
    have k₂ : Measurable fun w => ENNReal.ofReal (f₂ x w) := n₂.comp measurable_prodMk_left
    rw [← lintegral_add_left (f := fun w => ENNReal.ofReal (f₁ x w)) k₁,
      ← lintegral_add_left (f := fun w => ENNReal.ofReal (f₁ x w) + ENNReal.ofReal (f₂ x w))
        (k₁.add k₂)]
    refine setLIntegral_congr_fun measurableSet_Ioo fun w hw => ?_
    rw [ENNReal.ofReal_add (add_nonneg (h₁ x hx w hw) (h₂ x hx w hw)) (h₃ x hx w hw),
      ENNReal.ofReal_add (h₁ x hx w hw) (h₂ x hx w hw)]
  have l₁ : Measurable fun x => ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (f₁ x w) :=
    n₁.lintegral_prod_right'
  have l₂ : Measurable fun x => ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (f₂ x w) :=
    n₂.lintegral_prod_right'
  rw [setLIntegral_congr_fun measurableSet_Ioo e, lintegral_add_left
    (f := fun x => (∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (f₁ x w)) +
      ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (f₂ x w)) (l₁.add l₂),
    lintegral_add_left (f := fun x => ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (f₁ x w)) l₁]

theorem i2P1USig_lt_one {a b : ℝ} (ha0 : 0 ≤ a) (ha : a < 1) (hb : b ≤ 1) : a * b < 1 := by
  nlinarith [mul_le_mul_of_nonneg_left hb ha0]

theorem i2P1USig_nn {a q : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hq : 0 ≤ q) : 0 ≤ -log a * q :=
  mul_nonneg (by linarith [log_nonpos ha.1.le ha.2.le]) hq

/-- **`∫∫ (1 - w) (-log σ) Ψ = 2 π⁴ / 5`**, `σ = A B + (A + B) C`. -/
theorem i2P1USig_lint :
    ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (-log (w * (1 - w) * x * (w * (1 - w) * (1 - x)) +
        (w * (1 - w) * x + w * (1 - w) * (1 - x)) * ((1 - w) ^ 2 * x * (1 - x))) * i2P0Q x w) =
      ENNReal.ofReal (2 * π ^ 4 / 5) := by
  have hQ : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ w ∈ Ioo (0 : ℝ) 1, 0 ≤ i2P0Q x w := fun x hx w hw => by
    obtain ⟨hA, -, hB, -, hC, -⟩ := QED.ThreeLoopD.i2_lines_pos hx hw
    exact mul_nonneg (by linarith [hw.2]) (i2P0Psi_nonneg hA hB hC)
  have e : ∀ x ∈ Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (-log (w * (1 - w) * x * (w * (1 - w) * (1 - x)) +
        (w * (1 - w) * x + w * (1 - w) * (1 - x)) * ((1 - w) ^ 2 * x * (1 - x))) * i2P0Q x w) =
      ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (-log w * i2P0Q x w +
        -log ((1 - w) * x) * i2P0Q x w + -log ((1 - w) * (1 - x)) * i2P0Q x w) := by
    intro x hx
    refine setLIntegral_congr_fun measurableSet_Ioo fun w hw => ?_
    have h1 : 0 < (1 - w) * x := mul_pos (by linarith [hw.2]) hx.1
    have h3 : 0 < (1 - w) * (1 - x) := mul_pos (by linarith [hw.2]) (by linarith [hx.2])
    rw [show w * (1 - w) * x * (w * (1 - w) * (1 - x)) +
      (w * (1 - w) * x + w * (1 - w) * (1 - x)) * ((1 - w) ^ 2 * x * (1 - x)) =
      w * ((1 - w) * x) * ((1 - w) * (1 - x)) by ring, log_mul (mul_pos hw.1 h1).ne' h3.ne',
      log_mul hw.1.ne' h1.ne']
    congr 1
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioo e, i2P1U_lint_add3
    (f₁ := fun x w => -log w * i2P0Q x w) (f₂ := fun x w => -log ((1 - w) * x) * i2P0Q x w)
    (f₃ := fun x w => -log ((1 - w) * (1 - x)) * i2P0Q x w)
    ((by fun_prop : Measurable fun p : ℝ × ℝ => -log p.2).mul measurable_i2P0Q')
    ((by fun_prop : Measurable fun p : ℝ × ℝ => -log ((1 - p.2) * p.1)).mul measurable_i2P0Q')
    (fun x hx w hw => i2P1USig_nn hw (hQ x hx w hw))
    (fun x hx w hw => i2P1USig_nn ⟨mul_pos (by linarith [hw.2]) hx.1,
      i2P1USig_lt_one (by linarith [hw.2]) (by linarith [hw.1]) hx.2.le⟩
      (hQ x hx w hw))
    (fun x hx w hw => i2P1USig_nn ⟨mul_pos (by linarith [hw.2]) (by linarith [hx.2]),
      i2P1USig_lt_one (by linarith [hw.2]) (by linarith [hw.1])
        (by linarith [hx.1])⟩ (hQ x hx w hw)),
    i2P1USig_J₂, i2P1USig_J₁, i2P1USig_J₃, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end QED.ThreeLoopD
