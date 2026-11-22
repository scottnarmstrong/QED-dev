/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI2P1FXi
public import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Set (d), master `I₂`: the substitutions of the `ℱ`-part after the simplex

After the photon lines, the electron line and the simplex, the `ℱ`-part has the form

  `∫_{ρ > 0} H(ρ) ∫₀¹ dξ M_t(ρ k) / (ρ k)`, `k = ξ (1 - ξ)`,
  `M_t(q) = ∫_{t > 0} log (1 + q t² / (1 + t)) / (1 + t)² dt`,

with `H` a weight in `ρ`. We prove, for every measurable `H ≥ 0`,

  `= ∫₀¹ ds 8 (1 + s²) / (s (1 - s²)) log² s ∫₀¹ dz 2 z H(r(s, z)²)`,
  `r(s, z) = (1 - s²) z / (s (1 - z²))`.

The `ξ`-integral is `QED.ThreeLoopD.i2P1FXi_lint` at `λ = ρ t² / (1 + t)`; then
`ρ = λ (1 + t) / t²` at fixed `t`, `t = (1 - z²) / z²` and `λ = (1 - s²)² / s²` (so that
`λ = p² / (1 - p)` with `p = 1 - s²`).

## Main definitions

* `QED.ThreeLoopD.i2P1FMt`: `M_t`.

## Main results

* `QED.ThreeLoopD.i2P1FSub_main`.
-/

@[expose] public section

open Real Set MeasureTheory Filter
open scoped ENNReal

namespace QED.ThreeLoopD

/-- `M_t(q) = ∫_{t > 0} log (1 + q t² / (1 + t)) / (1 + t)² dt` (so that the `y₄`-integral of
the `ℱ`-part at fixed `q` is `M_t(q) / q`). -/
noncomputable def i2P1FMt (q : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (log (1 + q * t ^ 2 / (1 + t)) / (1 + t) ^ 2)

/-- The `ξ`-integral `∫₀¹ log (1 + λ k) / k dξ` as a lower integral. -/
noncomputable def i2P1FSubD (μ : ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ in Ioo (0 : ℝ) 1, ENNReal.ofReal (log (1 + μ * (ξ * (1 - ξ))) / (ξ * (1 - ξ)))

theorem measurable_i2P1FSubD : Measurable i2P1FSubD := by
  have : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (log (1 + p.1 * (p.2 * (1 - p.2))) / (p.2 * (1 - p.2))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  exact this.lintegral_prod_right'

/-- Scaling on `(0, ∞)`: `∫_{x > 0} f(x) = ∫_{y > 0} f(y / c) / c`. -/
theorem i2P1FSub_scale {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ≥0∞) :
    ∫⁻ x in Ioi (0 : ℝ), f x = ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (1 / c) * f (y / c) := by
  have himg : (fun y : ℝ => y / c) '' Ioi 0 = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨y, (hy : 0 < y), rfl⟩
      exact div_pos hy hc
    · intro (hx : 0 < x)
      exact ⟨x * c, mul_pos hx hc, by field_simp⟩
  conv_lhs => rw [← himg]
  rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun y _ => ((hasDerivAt_id' y).div_const c).hasDerivWithinAt)
    (fun a _ b _ h => by simpa [hc.ne'] using h) f]
  refine setLIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  rw [abs_of_pos (by simpa using hc)]

/-- `t = (1 - z²) / z²`: `∫_{t > 0} G(t) / (1 + t)² = ∫₀¹ 2 z G((1 - z²) / z²)`. -/
theorem i2P1FSub_t (G : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (1 / (1 + t) ^ 2) * G t =
      ∫⁻ z in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * z) * G ((1 - z ^ 2) / z ^ 2) := by
  have himg : (fun z : ℝ => (1 - z ^ 2) / z ^ 2) '' Ioo 0 1 = Ioi 0 := by
    ext t
    constructor
    · rintro ⟨z, ⟨h0, h1⟩, rfl⟩
      have : 0 < 1 - z ^ 2 := by nlinarith
      exact div_pos this (by positivity)
    · intro (ht : 0 < t)
      have h1t : 0 < 1 + t := by linarith
      refine ⟨Real.sqrt (1 / (1 + t)), ⟨Real.sqrt_pos.2 (by positivity), ?_⟩, ?_⟩
      · rw [Real.sqrt_lt' one_pos, one_pow, div_lt_one h1t]
        linarith
      · simp only
        rw [Real.sq_sqrt (by positivity)]
        field_simp
        ring
  have hd : ∀ z ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt (fun z : ℝ => (1 - z ^ 2) / z ^ 2)
      (-(2 / z ^ 3)) (Ioo 0 1) z := fun z hz => by
    have h0 : z ≠ 0 := hz.1.ne'
    have := ((((hasDerivAt_id z).pow 2).const_sub 1).div ((hasDerivAt_id z).pow 2)
      (pow_ne_zero 2 h0))
    refine (this.congr_deriv ?_).hasDerivWithinAt
    simp only [id, Pi.pow_apply]
    field_simp
    ring
  have hinj : InjOn (fun z : ℝ => (1 - z ^ 2) / z ^ 2) (Ioo 0 1) := fun a ha b hb h => by
    have ha0 : a ≠ 0 := ha.1.ne'
    have hb0 : b ≠ 0 := hb.1.ne'
    simp only at h
    have h' : 1 / a ^ 2 = 1 / b ^ 2 := by
      have e1 : (1 - a ^ 2) / a ^ 2 = 1 / a ^ 2 - 1 := by field_simp
      have e2 : (1 - b ^ 2) / b ^ 2 = 1 / b ^ 2 - 1 := by field_simp
      linarith
    rw [one_div, one_div, inv_inj] at h'
    exact (sq_eq_sq₀ ha.1.le hb.1.le).1 h'
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hd hinj]
  refine setLIntegral_congr_fun measurableSet_Ioo fun z hz => ?_
  have h0 : 0 < z := hz.1
  rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), abs_neg, abs_of_pos (by positivity)]
  congr 2
  field_simp
  ring

/-- `λ = (1 - s²)² / s²`: `∫_{λ > 0} G(λ) / λ = ∫₀¹ 2 (1 + s²) / (s (1 - s²)) G((1 - s²)² / s²)`. -/
theorem i2P1FSub_s (G : ℝ → ℝ≥0∞) :
    ∫⁻ μ in Ioi (0 : ℝ), ENNReal.ofReal (1 / μ) * G μ =
      ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * (1 + s ^ 2) / (s * (1 - s ^ 2))) *
        G ((1 - s ^ 2) ^ 2 / s ^ 2) := by
  have himg : (fun s : ℝ => (1 - s ^ 2) ^ 2 / s ^ 2) '' Ioo 0 1 = Ioi 0 := by
    ext μ
    constructor
    · rintro ⟨s, ⟨h0, h1⟩, rfl⟩
      have : 0 < 1 - s ^ 2 := by nlinarith
      exact div_pos (by positivity) (by positivity)
    · intro (hμ : 0 < μ)
      set a := Real.sqrt μ with ha
      set b := Real.sqrt (μ + 4) with hb
      have ha0 : 0 < a := Real.sqrt_pos.2 hμ
      have ha2 : a ^ 2 = μ := Real.sq_sqrt hμ.le
      have hb2 : b ^ 2 = μ + 4 := Real.sq_sqrt (by linarith)
      have hb0 : 0 ≤ b := Real.sqrt_nonneg _
      have hab : a < b := by nlinarith
      have hb2' : b < a + 2 := by nlinarith
      refine ⟨(b - a) / 2, ⟨by linarith, by linarith⟩, ?_⟩
      simp only
      have hs0 : (b - a) / 2 ≠ 0 := by
        have : 0 < b - a := by linarith
        positivity
      field_simp
      nlinarith [ha2, hb2]
  have hd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt (fun s : ℝ => (1 - s ^ 2) ^ 2 / s ^ 2)
      (-(2 * (1 - s ^ 2) * (1 + s ^ 2) / s ^ 3)) (Ioo 0 1) s := fun s hs => by
    have h0 : s ≠ 0 := hs.1.ne'
    have := (((((hasDerivAt_id s).pow 2).const_sub 1).pow 2).div ((hasDerivAt_id s).pow 2)
      (pow_ne_zero 2 h0))
    refine (this.congr_deriv ?_).hasDerivWithinAt
    simp only [id, Pi.pow_apply]
    field_simp
    ring
  have hinj : InjOn (fun s : ℝ => (1 - s ^ 2) ^ 2 / s ^ 2) (Ioo 0 1) := fun a ha b hb h => by
    have ha0 : 0 < a := ha.1
    have hb0 : 0 < b := hb.1
    have ha1 : 0 < 1 - a ^ 2 := by nlinarith [ha.2]
    have hb1 : 0 < 1 - b ^ 2 := by nlinarith [hb.2]
    simp only at h
    rw [show (1 - a ^ 2) ^ 2 / a ^ 2 = ((1 - a ^ 2) / a) ^ 2 by ring,
      show (1 - b ^ 2) ^ 2 / b ^ 2 = ((1 - b ^ 2) / b) ^ 2 by ring] at h
    have h' := (sq_eq_sq₀ (by positivity) (by positivity)).1 h
    rw [div_eq_div_iff ha0.ne' hb0.ne'] at h'
    nlinarith [mul_pos ha0 hb0]
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hd hinj]
  refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  have h0 : 0 < s := hs.1
  have h1 : 0 < 1 - s ^ 2 := by nlinarith [hs.2]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), abs_neg, abs_of_pos (by positivity)]
  congr 2
  field_simp

/-- **The `ξ`-integral first**:
`∫₀¹ M_t(ρ k) / (ρ k) dξ = ∫_{t > 0} D(ρ t² / (1 + t)) / (ρ (1 + t)²)`
with `D(λ) = ∫₀¹ log (1 + λ k) / k`. -/
theorem i2P1FSub_xi {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ ξ in Ioo (0 : ℝ) 1, ENNReal.ofReal (1 / (ρ * (ξ * (1 - ξ)))) *
        i2P1FMt (ρ * (ξ * (1 - ξ))) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (1 / ρ) * ENNReal.ofReal (1 / (1 + t) ^ 2) *
        i2P1FSubD (ρ * (t ^ 2 / (1 + t))) := by
  have hm : Measurable (Function.uncurry fun ξ t : ℝ =>
      ENNReal.ofReal (1 / (ρ * (ξ * (1 - ξ)))) *
        ENNReal.ofReal (log (1 + ρ * (ξ * (1 - ξ)) * t ^ 2 / (1 + t)) / (1 + t) ^ 2)) :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).mul
      (ENNReal.measurable_ofReal.comp (by fun_prop))
  calc ∫⁻ ξ in Ioo (0 : ℝ) 1, ENNReal.ofReal (1 / (ρ * (ξ * (1 - ξ)))) *
        i2P1FMt (ρ * (ξ * (1 - ξ)))
      = ∫⁻ ξ in Ioo (0 : ℝ) 1, ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (1 / (ρ * (ξ * (1 - ξ)))) *
          ENNReal.ofReal (log (1 + ρ * (ξ * (1 - ξ)) * t ^ 2 / (1 + t)) / (1 + t) ^ 2) := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun ξ _ => ?_
        rw [i2P1FMt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ξ in Ioo (0 : ℝ) 1, ENNReal.ofReal (1 / (ρ * (ξ * (1 - ξ)))) *
          ENNReal.ofReal (log (1 + ρ * (ξ * (1 - ξ)) * t ^ 2 / (1 + t)) / (1 + t) ^ 2) :=
        lintegral_lintegral_swap hm.aemeasurable
    _ = _ := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
        rw [i2P1FSubD, ← lintegral_const_mul' _ _ (by
          rw [← ENNReal.ofReal_mul (by positivity)]; exact ENNReal.ofReal_ne_top)]
        refine setLIntegral_congr_fun measurableSet_Ioo fun ξ hξ => ?_
        have hk : 0 < ξ * (1 - ξ) := mul_pos hξ.1 (by linarith [hξ.2])
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity),
          show ρ * (ξ * (1 - ξ)) * t ^ 2 / (1 + t) = ρ * (t ^ 2 / (1 + t)) * (ξ * (1 - ξ)) by
            ring]
        congr 1
        field_simp

/-- **The substitutions of the `ℱ`-part**: for measurable `H ≥ 0`,
`∫_{ρ > 0} H(ρ) ∫₀¹ M_t(ρ k) / (ρ k) dξ
= ∫₀¹ ds 8 (1 + s²) / (s (1 - s²)) log² s ∫₀¹ dz 2 z H(r(s, z)²)`. -/
theorem i2P1FSub_main {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ρ in Ioi (0 : ℝ), H ρ * ∫⁻ ξ in Ioo (0 : ℝ) 1,
        ENNReal.ofReal (1 / (ρ * (ξ * (1 - ξ)))) * i2P1FMt (ρ * (ξ * (1 - ξ))) =
      ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (8 * (1 + s ^ 2) / (s * (1 - s ^ 2)) * log s ^ 2) *
        ∫⁻ z in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * z) *
          H (((1 - s ^ 2) * z / (s * (1 - z ^ 2))) ^ 2) := by
  have hD := measurable_i2P1FSubD
  have m1 : Measurable (Function.uncurry fun ρ t : ℝ => H ρ * (ENNReal.ofReal (1 / ρ) *
      ENNReal.ofReal (1 / (1 + t) ^ 2) * i2P1FSubD (ρ * (t ^ 2 / (1 + t))))) :=
    (hH.comp measurable_fst).mul (((ENNReal.measurable_ofReal.comp (by fun_prop)).mul
      (ENNReal.measurable_ofReal.comp (by fun_prop))).mul (hD.comp (by fun_prop)))
  have m2 : Measurable (Function.uncurry fun t μ : ℝ => ENNReal.ofReal (1 / (1 + t) ^ 2) *
      (ENNReal.ofReal (1 / μ) * i2P1FSubD μ * H (μ * (1 + t) / t ^ 2))) :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).mul (((ENNReal.measurable_ofReal.comp
      (by fun_prop)).mul (hD.comp measurable_snd)).mul (hH.comp (by fun_prop)))
  calc ∫⁻ ρ in Ioi (0 : ℝ), H ρ * ∫⁻ ξ in Ioo (0 : ℝ) 1,
        ENNReal.ofReal (1 / (ρ * (ξ * (1 - ξ)))) * i2P1FMt (ρ * (ξ * (1 - ξ)))
      = ∫⁻ ρ in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ), H ρ * (ENNReal.ofReal (1 / ρ) *
          ENNReal.ofReal (1 / (1 + t) ^ 2) * i2P1FSubD (ρ * (t ^ 2 / (1 + t)))) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun ρ (hρ : 0 < ρ) => ?_
        rw [i2P1FSub_xi hρ, ← lintegral_const_mul _ (show Measurable fun t : ℝ =>
          ENNReal.ofReal (1 / ρ) * ENNReal.ofReal (1 / (1 + t) ^ 2) *
            i2P1FSubD (ρ * (t ^ 2 / (1 + t))) from ((ENNReal.measurable_ofReal.comp
              (by fun_prop)).mul (ENNReal.measurable_ofReal.comp (by fun_prop))).mul
                (hD.comp (by fun_prop)))]
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ρ in Ioi (0 : ℝ), H ρ * (ENNReal.ofReal (1 / ρ) *
          ENNReal.ofReal (1 / (1 + t) ^ 2) * i2P1FSubD (ρ * (t ^ 2 / (1 + t)))) :=
        lintegral_lintegral_swap m1.aemeasurable
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ μ in Ioi (0 : ℝ), ENNReal.ofReal (1 / (1 + t) ^ 2) *
          (ENNReal.ofReal (1 / μ) * i2P1FSubD μ * H (μ * (1 + t) / t ^ 2)) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
        have hc : 0 < t ^ 2 / (1 + t) := by positivity
        rw [i2P1FSub_scale hc]
        refine setLIntegral_congr_fun measurableSet_Ioi fun μ (hμ : 0 < μ) => ?_
        rw [show μ / (t ^ 2 / (1 + t)) * (t ^ 2 / (1 + t)) = μ by field_simp,
          show μ / (t ^ 2 / (1 + t)) = μ * (1 + t) / t ^ 2 by field_simp]
        have e : ENNReal.ofReal (1 / (t ^ 2 / (1 + t))) *
            ENNReal.ofReal (1 / (μ * (1 + t) / t ^ 2)) *
            ENNReal.ofReal (1 / (1 + t) ^ 2) = ENNReal.ofReal (1 / (1 + t) ^ 2) *
              ENNReal.ofReal (1 / μ) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
        calc ENNReal.ofReal (1 / (t ^ 2 / (1 + t))) * (H (μ * (1 + t) / t ^ 2) *
              (ENNReal.ofReal (1 / (μ * (1 + t) / t ^ 2)) * ENNReal.ofReal (1 / (1 + t) ^ 2) *
                i2P1FSubD μ))
            = (ENNReal.ofReal (1 / (t ^ 2 / (1 + t))) *
                ENNReal.ofReal (1 / (μ * (1 + t) / t ^ 2)) * ENNReal.ofReal (1 / (1 + t) ^ 2)) *
                (i2P1FSubD μ * H (μ * (1 + t) / t ^ 2)) := by ring
          _ = _ := by rw [e]; ring
    _ = ∫⁻ μ in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (1 / (1 + t) ^ 2) *
          (ENNReal.ofReal (1 / μ) * i2P1FSubD μ * H (μ * (1 + t) / t ^ 2)) :=
        lintegral_lintegral_swap m2.aemeasurable
    _ = ∫⁻ μ in Ioi (0 : ℝ), ENNReal.ofReal (1 / μ) * (i2P1FSubD μ *
          ∫⁻ z in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * z) * H (μ * z ^ 2 / (1 - z ^ 2) ^ 2)) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun μ (hμ : 0 < μ) => ?_
        have e : ∀ t, ENNReal.ofReal (1 / (1 + t) ^ 2) *
            (ENNReal.ofReal (1 / μ) * i2P1FSubD μ * H (μ * (1 + t) / t ^ 2)) =
            ENNReal.ofReal (1 / μ) * i2P1FSubD μ *
              (ENNReal.ofReal (1 / (1 + t) ^ 2) * H (μ * (1 + t) / t ^ 2)) := fun t => by ring
        simp_rw [e]
        rw [lintegral_const_mul _ (show Measurable fun t : ℝ =>
          ENNReal.ofReal (1 / (1 + t) ^ 2) * H (μ * (1 + t) / t ^ 2) from
            (ENNReal.measurable_ofReal.comp (by fun_prop)).mul (hH.comp (by fun_prop))),
          i2P1FSub_t, mul_assoc]
        congr 2
        refine setLIntegral_congr_fun measurableSet_Ioo fun z hz => ?_
        have h0 : z ≠ 0 := hz.1.ne'
        have h1 : 1 - z ^ 2 ≠ 0 := by nlinarith [hz.1, hz.2]
        congr 2
        field_simp
        ring
    _ = ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * (1 + s ^ 2) / (s * (1 - s ^ 2))) *
          (i2P1FSubD ((1 - s ^ 2) ^ 2 / s ^ 2) * ∫⁻ z in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * z) *
            H ((1 - s ^ 2) ^ 2 / s ^ 2 * z ^ 2 / (1 - z ^ 2) ^ 2)) := i2P1FSub_s _
    _ = _ := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
        have h0 : 0 < s := hs.1
        have h1 : 0 < 1 - s ^ 2 := by nlinarith [hs.2]
        have hp : 1 - s ^ 2 ∈ Ico (0 : ℝ) 1 := ⟨h1.le, by nlinarith⟩
        have hD' := i2P1FXi_lint hp
        rw [show (1 - s ^ 2) ^ 2 / (1 - (1 - s ^ 2)) = (1 - s ^ 2) ^ 2 / s ^ 2 by ring,
          show 1 - (1 - s ^ 2) = s ^ 2 by ring] at hD'
        rw [i2P1FSubD, hD', ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        · congr 1
          rw [log_pow]
          push_cast
          ring
        · refine setLIntegral_congr_fun measurableSet_Ioo fun z hz => ?_
          have hz1 : 1 - z ^ 2 ≠ 0 := by nlinarith [hz.1, hz.2]
          congr 2
          field_simp

end QED.ThreeLoopD
