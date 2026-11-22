/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9MThreeMono
import QED.ThreeLoopD.SetDMastersI9KValB

/-!
# Set (d), master `I₉`: the `x`-integral of the half-integrand of `M₃`

At fixed `w ∈ (0, 1)` (notation of `QED.ThreeLoopD.SetDMastersI9MThreeMono`, `λ = log w`), the
integrand of `M₃` is `(1 - w²)/w · (s₃(x) + s₃(1 - x))` with

  `s₃ = -9a³/2 - 27a²b/2 + 9a²p + 9a²q + 18abp - 6ap² - 12apq - 6aq²
      + λ (9a² + 9ab - 12ap - 12aq + 3p² + 3pq) + λ² (6p - 6a) + 3p³/2 + 9p²q/2`.

By the monomial reductions, `∫₀¹ s₃` is an explicit combination of weight-two integrals and the
nine pure integrals `P₁, P₃, P₅, P₆, P₇, P₈, P₉, R₁, R₃`, which here enter as hypotheses.

## Main results

* `QED.ThreeLoopD.i9M3S_integral`: integrability of `s₃` and `∫₀¹ s₃ = i9M3Sig w …`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- The half-integrand `s₃` of `M₃` at fixed `w` (see the module docstring). -/
noncomputable def i9M3S (w x : ℝ) : ℝ :=
  -(9 / 2) * (Real.log (w + (1 - w) * x) * Real.log (w + (1 - w) * x) * Real.log (w + (1 - w) *
      x)) -
    27 / 2 * (Real.log (w + (1 - w) * x) * Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) *
        x)) +
    9 * (Real.log (w + (1 - w) * x) * Real.log (w + (1 - w) * x) * Real.log x) + 9 * (Real.log (w
        + (1 - w) * x) * Real.log (w + (1 - w) * x) * Real.log (1 - x)) +
    18 * (Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) * Real.log x) - 6 * (Real.log (w
        + (1 - w) * x) * Real.log x * Real.log x) -
    12 * (Real.log (w + (1 - w) * x) * Real.log x * Real.log (1 - x)) - 6 * (Real.log (w + (1 - w)
        * x) * Real.log (1 - x) * Real.log (1 - x)) +
    Real.log w * (9 * Real.log (w + (1 - w) * x) ^ 2 + 9 * (Real.log (w + (1 - w) * x) * Real.log
        (1 - (1 - w) * x)) -
      12 * (Real.log x * Real.log (w + (1 - w) * x)) - 12 * (Real.log (1 - x) * Real.log (w + (1 -
          w) * x)) + 3 * (Real.log x * Real.log x) +
      3 * (Real.log x * Real.log (1 - x))) +
    Real.log w ^ 2 * (6 * Real.log x - 6 * Real.log (w + (1 - w) * x)) +
    3 / 2 * (Real.log x * Real.log x * Real.log x) + 9 / 2 * (Real.log x * Real.log x * Real.log
        (1 - x))

/-- `∫₀¹ log² A`. -/
noncomputable def i9M3VAA (w : ℝ) : ℝ := 2 + (2 * w * Real.log w - w * Real.log w ^ 2) / (1 - w)

/-- `∫₀¹ log x log A`. -/
noncomputable def i9M3VAP (w : ℝ) : ℝ :=
  2 + w * Real.log w / (1 - w) - w * (Li₂ (1 - w) + Real.log w ^ 2 / 2) / (1 - w)

/-- `∫₀¹ log (1 - x) log A = ∫₀¹ log x log B`. -/
noncomputable def i9M3VAQ (w : ℝ) : ℝ := 2 + w * Real.log w / (1 - w) - Li₂ (1 - w) / (1 - w)

/-- The value of `∫₀¹ s₃`, in terms of the pure integrals. -/
noncomputable def i9M3Sig (w P1 P3 P5 P6 P7 P8 P9 R1 R3 : ℝ) : ℝ :=
  -(9 / 2) * (-(w / (1 - w) * Real.log w ^ 3) - 3 * i9M3VAA w) -
    27 / 2 * (-2 * i9M2JAB w - i9M3VAA w + (1 + w) / (1 - w) * P1) +
    9 * (-i9M3VAA w - 2 * i9M3VAP w + 2 * w / (1 - w) * R1) +
    9 * (-2 * i9M3VAQ w - i9M3VAA w + P3 / (1 - w)) +
    18 * (-i9M3VAQ w - i9M3VAP w - i9M2JAB w + (1 + w) / (1 - w) * P8 - w / (1 - w) * P9) -
    6 * (-2 - 2 * i9M3VAP w + w / (1 - w) * R3) -
    12 * (-(2 - π ^ 2 / 6) - i9M3VAQ w - i9M3VAP w - w / (1 - w) * P6 + P7 / (1 - w)) -
    6 * (-2 - 2 * i9M3VAQ w + 2 / (1 - w) * P5) +
    Real.log w * (9 * i9M3VAA w + 9 * i9M2JAB w - 12 * i9M3VAP w - 12 * i9M3VAQ w + 3 * 2 +
      3 * (2 - π ^ 2 / 6)) +
    Real.log w ^ 2 * (6 * (-1) - 6 * (-1 - w * Real.log w / (1 - w))) +
    3 / 2 * (-6) + 9 / 2 * (2 * zeta3 - 6 + π ^ 2 / 3)

/-- **`∫₀¹ s₃`** in terms of the nine pure integrals. -/
theorem i9M3S_integral {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) {P1 P3 P5 P6 P7 P8 P9 R1 R3 : ℝ}
    (hP1 : IntervalIntegrable (fun x => (1 - w) * Real.log (w + (1 - w) * x) ^ 2 / (1 - (1 - w) *
        x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (1 - w) * Real.log (w + (1 - w) * x) ^ 2 / (1 - (1 - w) * x) = P1)
    (hP3 : IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) ^ 2 / (1 - x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) ^ 2 / (1 - x) = P3)
    (hP5 : IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log (1 - x) / (1 - x))
        volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log (1 - x) / (1 - x) = P5)
    (hP6 : IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log (1 - x) / x) volume
        0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log (1 - x) / x = P6)
    (hP7 : IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log x / (1 - x)) volume
        0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log x / (1 - x) = P7)
    (hP8 : IntervalIntegrable (fun x => (1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) / (1 -
        (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) / (1 - (1 - w) * x) =
          P8)
    (hP9 : IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) /
        x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) / x = P9)
    (hR1 : IntervalIntegrable (fun x => (1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) / (w +
        (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) / (w + (1 - w) * x) =
          R1)
    (hR3 : IntervalIntegrable (fun x => (1 - w) * Real.log x ^ 2 / (w + (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (1 - w) * Real.log x ^ 2 / (w + (1 - w) * x) = R3) :
    IntervalIntegrable (i9M3S w) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, i9M3S w x = i9M3Sig w P1 P3 P5 P6 P7 P8 P9 R1 R3 := by
  have haa := i9M2_logA_sq hw
  have hab := i9M2_logA_logB hw
  have hap := i9M2_logX_logA hw
  have hbp := i9M2_logX_logB hw
  have haq := i9M3_logQ_logA hw
  have hpp := i9M3_logX_sq
  have hqq := i9M3_logQ_sq
  have hpq := i9M3_logX_logQ
  have h := i9M2_step (i9M2_step (i9M2_step (i9M2_step (i9M2_step (i9M2_step (i9M2_step
    (i9M2_step (i9M2_step (i9M2_step (i9M2_step (i9M2_step (i9M2_step (i9M2_step (i9M2_step
    (i9M2_step (i9M2_step (i9M2_step i9M3_zero_step
    (i9M3_aaa hw) (-(9 / 2))) (i9M3_aab hw hab haa hP1) (-(27 / 2)))
    (i9M3_aap hw hap haa hR1) 9) (i9M3_aaq hw haq haa hP3) 9)
    (i9M3_abp hw hbp hap hab hP8 hP9) 18) (i9M3_app hw hpp hap hR3) (-6))
    (i9M3_apq hw hpq haq hap hP6 hP7) (-12)) (i9M3_aqq hw hqq haq hP5) (-6))
    haa (9 * Real.log w)) hab (9 * Real.log w)) hap (-(12 * Real.log w)))
    haq (-(12 * Real.log w))) hpp (3 * Real.log w)) hpq (3 * Real.log w))
    i9M2_log (6 * Real.log w ^ 2)) (i9M2_logA hw) (-(6 * Real.log w ^ 2)))
    i9_integral_log_cube (3 / 2)) i9_integral_log_sq_mul_log_one_sub (9 / 2)
  have e : i9M3S w = fun x => 0 + -(9 / 2) * (Real.log (w + (1 - w) * x) * Real.log (w + (1 - w) *
      x) * Real.log (w + (1 - w) * x)) +
      -(27 / 2) * (Real.log (w + (1 - w) * x) * Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w)
          * x)) + 9 * (Real.log (w + (1 - w) * x) * Real.log (w + (1 - w) * x) * Real.log x) +
      9 * (Real.log (w + (1 - w) * x) * Real.log (w + (1 - w) * x) * Real.log (1 - x)) + 18 *
          (Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) * Real.log x) +
      -6 * (Real.log (w + (1 - w) * x) * Real.log x * Real.log x) + -12 * (Real.log (w + (1 - w) *
          x) * Real.log x * Real.log (1 - x)) +
      -6 * (Real.log (w + (1 - w) * x) * Real.log (1 - x) * Real.log (1 - x)) + 9 * Real.log w *
          Real.log (w + (1 - w) * x) ^ 2 +
      9 * Real.log w * (Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x)) + -(12 * Real.log
          w) * (Real.log x * Real.log (w + (1 - w) * x)) +
      -(12 * Real.log w) * (Real.log (1 - x) * Real.log (w + (1 - w) * x)) + 3 * Real.log w *
          (Real.log x * Real.log x) +
      3 * Real.log w * (Real.log x * Real.log (1 - x)) + 6 * Real.log w ^ 2 * Real.log x +
      -(6 * Real.log w ^ 2) * Real.log (w + (1 - w) * x) + 3 / 2 * (Real.log x * Real.log x *
          Real.log x) +
      9 / 2 * (Real.log x * Real.log x * Real.log (1 - x)) := by
    funext x
    unfold i9M3S
    ring
  rw [e]
  refine ⟨h.1, h.2.trans ?_⟩
  unfold i9M3Sig i9M3VAA i9M3VAP i9M3VAQ
  ring

end QED.ThreeLoopD
