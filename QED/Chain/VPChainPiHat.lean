/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VacuumPolarizationUnit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The renormalized one-loop vacuum-polarization function on the photon variable

Helper analysis for the vacuum-polarization (VP) chains of `docs/HIGHER-LOOP-PLAN.md`
(section 3 (b), obligation O3-13). It is **not** frozen.

## Objects (electron mass `m = 1`)

* `piHat s = 2 ∫₀¹ t(1-t) log(1 + t(1-t)s) dt`: the renormalized one-loop VP function
  `Π̂(s)` of the plan (Srednicki (62.25) divided by `r = α/π`, Euclidean `s = k²/m²`).
* `piHatX x`: its closed form on the photon variable `s = x²/(1-x)` of the one-loop vertex,
  `-5/9 - 4/(3x) + 4/(3x²) + (x³ - 6x + 4)/(3x³) · log(1-x)` for `0 < x < 1`. This is the plan's
  Landau form `⅓[-5/3 + a + (1 - a/2) β log((β+1)²/a)]` with `a = 4/s`, since on this curve
  `β = √(1+a) = (2-x)/x` and `(β+1)²/a = 1/(1-x)`.

## Main statements

* `piHat_photonVar`: `Π̂(x²/(1-x)) = piHatX x` for `0 < x < 1`. Proof: on this curve
  `1 + t(1-t)s = (1-tx)(1-x+tx)/(1-x)`, and the `t`-integral is elementary.
* `piHat_eq_spectral`: `Π̂(s) = ∫₀¹ ρ(v) s/(s + 4/(1-v²)) dv` for `s > -4`, the spectral form of
  the two-loop VP unit (`QED.TwoLoop.VPUnit.integral_mul_log_eq_spectral` at `M = 1`).
* `one_sub_mul_piHat_photonVar`: for `0 < x < 1`, `(1-x) Π̂(x²/(1-x))` is the `v`-integral
  `∫₀¹ ρ(v) x²(1-x)/(x² + (1-x)·4/(1-v²)) dv` of the integrand of
  `QED.TwoLoop.VPUnit.integral_vpUnit`; so the one-bubble chain `∫₀¹ (1-x) Π̂(x²/(1-x)) dx` is the
  VP unit (its value `119/36 - π²/3` is reproved in `QED/Chain/VPChainSetB.lean`).
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.Chain

/-- The renormalized one-loop vacuum-polarization function
`Π̂(s) = 2 ∫₀¹ t(1-t) log(1 + t(1-t)s) dt` (electron loop, `m = 1`, Euclidean `s = k²/m²`). -/
noncomputable def piHat (s : ℝ) : ℝ :=
  2 * ∫ t in (0 : ℝ)..1, t * (1 - t) * log (1 + t * (1 - t) * s)

/-- The closed form of `Π̂(x²/(1-x))` on `0 < x < 1`. -/
noncomputable def piHatX (x : ℝ) : ℝ :=
  -5 / 9 - 4 / (3 * x) + 4 / (3 * x ^ 2) + (x ^ 3 - 6 * x + 4) / (3 * x ^ 3) * log (1 - x)

/-- A `t`-antiderivative of `t(1-t) (log(1-tx) + log(1-x+tx) - log(1-x))`. -/
noncomputable def tPrim (x t : ℝ) : ℝ :=
  t ^ 3 * (log (1 - x) / 3 + 2 / 9) + t ^ 2 * (-(log (1 - x)) / 2 - 1 / 3) +
    t * (-1 / 6 - 2 / (3 * x) + 2 / (3 * x ^ 2)) +
    (-t ^ 3 / 3 + t ^ 2 / 2 - 1 / (2 * x ^ 2) + 1 / (3 * x ^ 3)) * log (1 - t * x) +
    (-t ^ 3 / 3 + t ^ 2 / 2 - 1 / 6 + 1 / (2 * x ^ 2) - 1 / (3 * x ^ 3)) * log (1 - x + t * x)

theorem hasDerivAt_tPrim {x t : ℝ} (hx0 : 0 < x) (ha : 0 < 1 - t * x) (hb : 0 < 1 - x + t * x) :
    HasDerivAt (tPrim x)
      (t * (1 - t) * (log (1 - t * x) + log (1 - x + t * x) - log (1 - x))) t := by
  have h1 : HasDerivAt (fun t => 1 - t * x) (-x) t := by
    simpa using ((hasDerivAt_id' t).mul_const x).const_sub 1
  have h2 : HasDerivAt (fun t => 1 - x + t * x) x t := by
    simpa using ((hasDerivAt_id' t).mul_const x).const_add (1 - x)
  have hw : HasDerivAt (fun t : ℝ => -1 / 3 * t ^ 3 + 1 / 2 * t ^ 2)
      (-1 / 3 * (↑3 * t ^ (3 - 1)) + 1 / 2 * (↑2 * t ^ (2 - 1))) t :=
    ((hasDerivAt_pow 3 t).const_mul (-1 / 3)).add ((hasDerivAt_pow 2 t).const_mul (1 / 2))
  have h := (((((hasDerivAt_pow 3 t).mul_const (log (1 - x) / 3 + 2 / 9)).add
    ((hasDerivAt_pow 2 t).mul_const (-(log (1 - x)) / 2 - 1 / 3))).add
    ((hasDerivAt_id' t).mul_const (-1 / 6 - 2 / (3 * x) + 2 / (3 * x ^ 2)))).add
    (((hw.sub_const (1 / (2 * x ^ 2))).add_const (1 / (3 * x ^ 3))).mul (h1.log ha.ne'))).add
    ((((hw.sub_const (1 / 6)).add_const (1 / (2 * x ^ 2))).sub_const
      (1 / (3 * x ^ 3))).mul (h2.log hb.ne'))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  · have hx : x ≠ 0 := hx0.ne'
    have ha' : 1 - x * t ≠ 0 := by rw [mul_comm]; exact ha.ne'
    have hb' : 1 - x + x * t ≠ 0 := by rw [mul_comm]; exact hb.ne'
    field_simp
    push_cast
    ring
  · simp only [tPrim, Pi.add_apply, Pi.mul_apply]
    ring

/-- On the photon curve, `1 + t(1-t)·x²/(1-x) = (1-tx)(1-x+tx)/(1-x)`. -/
theorem one_add_photonVar_eq {x t : ℝ} (hx : x < 1) :
    1 + t * (1 - t) * (x ^ 2 / (1 - x)) = (1 - t * x) * (1 - x + t * x) / (1 - x) := by
  have : (1 : ℝ) - x ≠ 0 := by linarith
  field_simp
  ring

/-- **The closed form on the photon curve.** `Π̂(x²/(1-x)) = piHatX x` for `0 < x < 1`. -/
theorem piHat_photonVar {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    piHat (x ^ 2 / (1 - x)) = piHatX x := by
  obtain ⟨hx0, hx1⟩ := hx
  have hs : 0 < 1 - x := by linarith
  have hab : ∀ t ∈ uIcc (0 : ℝ) 1, 0 < 1 - t * x ∧ 0 < 1 - x + t * x := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    obtain ⟨ht0, ht1⟩ := ht
    constructor <;> nlinarith
  have hcongr : ∀ t ∈ uIcc (0 : ℝ) 1,
      t * (1 - t) * log (1 + t * (1 - t) * (x ^ 2 / (1 - x))) =
        t * (1 - t) * (log (1 - t * x) + log (1 - x + t * x) - log (1 - x)) := by
    intro t ht
    obtain ⟨ha, hb⟩ := hab t ht
    rw [one_add_photonVar_eq hx1, log_div (mul_pos ha hb).ne' hs.ne', log_mul ha.ne' hb.ne']
  have hcont : ContinuousOn
      (fun t => t * (1 - t) * (log (1 - t * x) + log (1 - x + t * x) - log (1 - x)))
      (uIcc 0 1) := by
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.sub (ContinuousOn.add ?_ ?_)
      continuousOn_const)
    · exact ContinuousOn.log (by fun_prop) fun t ht => (hab t ht).1.ne'
    · exact ContinuousOn.log (by fun_prop) fun t ht => (hab t ht).2.ne'
  unfold piHat
  rw [intervalIntegral.integral_congr hcongr,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_tPrim hx0 (hab t ht).1 (hab t ht).2) hcont.intervalIntegrable]
  simp only [tPrim, piHatX]
  have hx : x ≠ 0 := hx0.ne'
  simp only [one_mul, zero_mul, sub_zero, add_zero, log_one, mul_zero, one_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
  rw [show 1 - x + x = (1 : ℝ) by ring]
  simp only [log_one, mul_zero, add_zero]
  field_simp
  ring

/-- **The spectral form.** `Π̂(s) = ∫₀¹ ρ(v) s/(s + 4/(1-v²)) dv` for `s > -4`, with
`ρ(v) = v²(1 - v²/3)/(1 - v²)`. -/
theorem piHat_eq_spectral {s : ℝ} (hs : -4 < s) :
    piHat s = ∫ v in (0 : ℝ)..1,
      v ^ 2 * (1 - v ^ 2 / 3) / (1 - v ^ 2) * (s / (s + 4 / (1 - v ^ 2))) := by
  have h := QED.TwoLoop.VPUnit.integral_mul_log_eq_spectral (M := 1) (K := s) one_ne_zero
    (by norm_num; linarith)
  simp only [one_pow, div_one, mul_one] at h
  unfold piHat
  rw [h]
  ring

/-- On the photon curve the spectral integrand times `1 - x` is the one-loop `F₂` kernel:
`(1-x) s/(s + c) = x²(1-x)/(x² + (1-x)c)` for `s = x²/(1-x)`, `0 < x < 1`, `c ≥ 0`. -/
theorem one_sub_mul_photonVar_div {x c : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hc : 0 ≤ c) :
    (1 - x) * (x ^ 2 / (1 - x) / (x ^ 2 / (1 - x) + c)) =
      x ^ 2 * (1 - x) / (x ^ 2 + (1 - x) * c) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hs : 0 < 1 - x := by linarith
  have hd : 0 < x ^ 2 + (1 - x) * c := by positivity
  have hd' : 0 < x ^ 2 / (1 - x) + c := by positivity
  rw [show x ^ 2 / (1 - x) + c = (x ^ 2 + (1 - x) * c) / (1 - x) by field_simp]
  field_simp

/-- **Link to the VP unit.** For `0 < x < 1`, `(1-x) Π̂(x²/(1-x))` is the `v`-integral of the
integrand of `QED.TwoLoop.VPUnit.integral_vpUnit`:
`∫₀¹ ρ(v) x²(1-x)/(x² + (1-x)·4/(1-v²)) dv`. -/
theorem one_sub_mul_piHat_photonVar {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (1 - x) * piHat (x ^ 2 / (1 - x)) = ∫ v in (0 : ℝ)..1,
      v ^ 2 * (1 - v ^ 2 / 3) / (1 - v ^ 2) *
        (x ^ 2 * (1 - x) / (x ^ 2 + (1 - x) * (4 / (1 - v ^ 2)))) := by
  have hs : -4 < x ^ 2 / (1 - x) := by
    have : 0 ≤ x ^ 2 / (1 - x) := div_nonneg (sq_nonneg x) (by linarith [hx.2])
    linarith
  rw [piHat_eq_spectral hs, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun v hv => ?_
  rw [uIcc_of_le zero_le_one] at hv
  have hc : 0 ≤ 4 / (1 - v ^ 2) := div_nonneg (by norm_num) (by nlinarith [hv.1, hv.2])
  rw [← one_sub_mul_photonVar_div hx hc]
  ring

end QED.Chain
