/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.VPChainPiHat
public import QED.Polylog.ExtraIntegralsX
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The exact value of the sixth-order VP chain, set (b) (O3-13)

Helper-level spike for obligation O3-13 of `docs/HIGHER-LOOP-PLAN.md` (task T2). It is **not**
frozen, and the target constant `QED.Chain.aSetB` is a plain definition awaiting a ruling.

With `Π̂ = QED.Chain.piHat` (the renormalized one-loop VP function, electron mass `1`),
`∫₀¹ (1-x) Π̂(x²/(1-x))² dx = (8/3) ζ(3) - (4/135) π² - 943/324`, and the integrand is interval
integrable on `[0,1]`. The one-bubble analogue `∫₀¹ (1-x) Π̂(x²/(1-x)) dx = 119/36 - π²/3` (the
value of `QED.TwoLoop.VPUnit.integral_vpUnit`) is proved the same way, as a check of the
normalization.

## Route

On `0 < x < 1`, `Π̂(x²/(1-x)) = A + B L` with `L = log(1-x)` (`QED.Chain.piHat_photonVar`). The
integrand `(1-x)(A + BL)²` has the antiderivative (generated and checked in exact arithmetic by
`scripts/numerics/chain/set_b_antiderivative.py`)
`F = N₀/x³ + N₁/x⁴ · (1-x)L + N₂/x⁵ · (1-x)L² - (8/45) Li₂(x) + (4/3) S(x)`,
with polynomials `N₀, N₁, N₂` and `S = QED.Polylog.logOneSubSqPrim` (`S' = L²/x`).

* At `x → 1⁻` the coefficients are regular, `(1-x)L → 0`, `(1-x)L² → 0`, `Li₂ → π²/6`, `S → 0`.
* At `x → 0⁺` the poles cancel: with `L = x T₁ + x⁴ ρ`, `T₁ = -1 - x/2 - x²/3 - x³/4` and
  `ρ = logRem x / x⁴ → 0` (`QED.Polylog.abs_logRem_le`), `F = Poly + U₁ρ + U₂ρ(2T₁ + ρx³) -
  (8/45)Li₂ + (4/3)S` with polynomials `Poly, U₁, U₂`, `Poly(0) = 2/9`; and `S → -2ζ(3)`.
* The integrand is nonnegative, so integrability and the value follow from
  `QED.Polylog.intervalIntegrable_and_integral_eq_of_nonneg`.

## Main statements

* `QED.Chain.aSetB`: `(8/3) ζ(3) - (4/135) π² - 943/324` (not frozen).
* `QED.Chain.intervalIntegrable_setB`, `QED.Chain.integral_setB`: integrability and
  `∫₀¹ (1-x) Π̂(x²/(1-x))² dx = aSetB`.
* `QED.Chain.intervalIntegrable_oneBubble`, `QED.Chain.integral_oneBubble`: the same for one
  bubble, `= 119/36 - π²/3`; `QED.Chain.integral_oneBubble_eq_vpUnit`: it equals the VP-unit
  double integral of `QED.TwoLoop.VPUnit.integral_vpUnit`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology QED.Polylog

namespace QED.Chain

/-- The sixth-order set (b) constant `(8/3) ζ(3) - (4/135) π² - 943/324` (not frozen). -/
noncomputable def aSetB : ℝ := 8 / 3 * zeta3 - 4 / 135 * π ^ 2 - 943 / 324

/-! ### A polynomial derivative -/

/-- The derivative of a polynomial of degree at most `7`. -/
theorem hasDerivAt_poly7 (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ x : ℝ) :
    HasDerivAt (fun y => a₀ + a₁ * y + a₂ * y ^ 2 + a₃ * y ^ 3 + a₄ * y ^ 4 + a₅ * y ^ 5 +
      a₆ * y ^ 6 + a₇ * y ^ 7)
      (a₁ + 2 * a₂ * x + 3 * a₃ * x ^ 2 + 4 * a₄ * x ^ 3 + 5 * a₅ * x ^ 4 + 6 * a₆ * x ^ 5 +
        7 * a₇ * x ^ 6) x := by
  have h := ((((((((hasDerivAt_const x a₀).add ((hasDerivAt_id' x).const_mul a₁)).add
    ((hasDerivAt_pow 2 x).const_mul a₂)).add ((hasDerivAt_pow 3 x).const_mul a₃)).add
    ((hasDerivAt_pow 4 x).const_mul a₄)).add ((hasDerivAt_pow 5 x).const_mul a₅)).add
    ((hasDerivAt_pow 6 x).const_mul a₆)).add ((hasDerivAt_pow 7 x).const_mul a₇))
  convert h using 1
  push_cast
  ring

/-! ### The antiderivative -/

/-- `N₀`, the numerator of the rational part `N₀/x³` of the antiderivative. -/
noncomputable def sbN0 (x : ℝ) : ℝ :=
  -16 / 45 + 64 * x / 45 - 224 * x ^ 2 / 135 - 295 * x ^ 4 / 162 - 89 * x ^ 5 / 324

/-- `N₁`, the numerator of the coefficient `N₁/x⁴` of `(1-x) log(1-x)`. -/
noncomputable def sbN1 (x : ℝ) : ℝ :=
  -32 / 45 + 112 * x / 45 - 296 * x ^ 2 / 135 - 32 * x ^ 3 / 27 - 35 * x ^ 4 / 54 -
    13 * x ^ 5 / 54

/-- `N₂`, the numerator of the coefficient `N₂/x⁵` of `(1-x) log(1-x)²`. -/
noncomputable def sbN2 (x : ℝ) : ℝ :=
  -16 / 45 + 64 * x / 45 - 76 * x ^ 2 / 45 - 2 * x ^ 3 / 15 + 94 * x ^ 4 / 45 - x ^ 5 / 18 +
    x ^ 6 / 18

theorem hasDerivAt_sbN0 (x : ℝ) :
    HasDerivAt sbN0 (64 / 45 - 448 * x / 135 - 590 * x ^ 3 / 81 - 445 * x ^ 4 / 324) x := by
  refine ((hasDerivAt_poly7 (-16 / 45) (64 / 45) (-224 / 135) 0 (-295 / 162) (-89 / 324) 0 0
    x).congr_deriv (by ring)).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  simp only [sbN0]
  ring

theorem hasDerivAt_sbN1 (x : ℝ) :
    HasDerivAt sbN1
      (112 / 45 - 592 * x / 135 - 32 * x ^ 2 / 9 - 70 * x ^ 3 / 27 - 65 * x ^ 4 / 54) x := by
  refine ((hasDerivAt_poly7 (-32 / 45) (112 / 45) (-296 / 135) (-32 / 27) (-35 / 54)
    (-13 / 54) 0 0 x).congr_deriv (by ring)).congr_of_eventuallyEq
    (Eventually.of_forall fun y => ?_)
  simp only [sbN1]
  ring

theorem hasDerivAt_sbN2 (x : ℝ) :
    HasDerivAt sbN2
      (64 / 45 - 152 * x / 45 - 2 * x ^ 2 / 5 + 376 * x ^ 3 / 45 - 5 * x ^ 4 / 18 + x ^ 5 / 3)
      x := by
  refine ((hasDerivAt_poly7 (-16 / 45) (64 / 45) (-76 / 45) (-2 / 15) (94 / 45) (-1 / 18)
    (1 / 18) 0 x).congr_deriv (by ring)).congr_of_eventuallyEq
    (Eventually.of_forall fun y => ?_)
  simp only [sbN2]
  ring

/-- The antiderivative of the set (b) integrand on `(0,1)`. -/
noncomputable def setBPrim (x : ℝ) : ℝ :=
  sbN0 x / x ^ 3 + sbN1 x / x ^ 4 * ((1 - x) * log (1 - x)) +
    sbN2 x / x ^ 5 * ((1 - x) * log (1 - x) ^ 2) - 8 / 45 * Li₂ x + 4 / 3 * logOneSubSqPrim x

theorem hasDerivAt_one_sub_mul_log {x : ℝ} (hx : x < 1) :
    HasDerivAt (fun y => (1 - y) * log (1 - y)) (-log (1 - x) - 1) x := by
  have hs : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id' x).const_sub 1
  have h := hs.mul (hs.log (by linarith))
  refine h.congr_deriv ?_
  have : (1 : ℝ) - x ≠ 0 := by linarith
  field_simp
  ring

theorem hasDerivAt_one_sub_mul_log_sq {x : ℝ} (hx : x < 1) :
    HasDerivAt (fun y => (1 - y) * log (1 - y) ^ 2) (-log (1 - x) ^ 2 - 2 * log (1 - x)) x := by
  have hs : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id' x).const_sub 1
  have h := hs.mul ((hs.log (by linarith)).pow 2)
  refine h.congr_deriv ?_
  have : (1 : ℝ) - x ≠ 0 := by linarith
  simp only [Pi.pow_apply]
  field_simp
  push_cast
  ring

theorem hasDerivAt_setBPrim {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt setBPrim ((1 - x) * piHatX x ^ 2) x := by
  obtain ⟨hx0, hx1⟩ := hx
  have hx' : x ≠ 0 := hx0.ne'
  have h := (((((hasDerivAt_sbN0 x).div (hasDerivAt_pow 3 x) (pow_ne_zero 3 hx')).add
    (((hasDerivAt_sbN1 x).div (hasDerivAt_pow 4 x) (pow_ne_zero 4 hx')).mul
      (hasDerivAt_one_sub_mul_log hx1))).add
    (((hasDerivAt_sbN2 x).div (hasDerivAt_pow 5 x) (pow_ne_zero 5 hx')).mul
      (hasDerivAt_one_sub_mul_log_sq hx1))).sub
    ((hasDerivAt_Li₂' ⟨hx0, hx1⟩).const_mul (8 / 45))).add
    ((hasDerivAt_logOneSubSqPrim ⟨hx0, hx1⟩).const_mul (4 / 3))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  · simp only [Pi.div_apply, sbN0, sbN1, sbN2, piHatX]
    field_simp
    push_cast
    ring
  · simp only [setBPrim, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]

/-! ### The endpoint `x → 0⁺` -/

/-- `T₁ = -1 - x/2 - x²/3 - x³/4`, so that `log(1-x) = x T₁ + logRem x`. -/
noncomputable def logT1 (x : ℝ) : ℝ := -1 - x / 2 - x ^ 2 / 3 - x ^ 3 / 4

/-- The regular part of the antiderivative at `0`. -/
noncomputable def sbPoly (x : ℝ) : ℝ :=
  2 / 9 + 8 * x / 45 - 28 * x ^ 2 / 45 - 172 * x ^ 3 / 405 - 53 * x ^ 4 / 180 - 19 * x ^ 5 / 18 -
    527 * x ^ 6 / 1620 - 91 * x ^ 7 / 405 - 1757 * x ^ 8 / 12960 - x ^ 9 / 432 - x ^ 10 / 288

/-- `U₁ = x⁴ · (1-x) N₁/x⁴`. -/
noncomputable def sbU1 (x : ℝ) : ℝ :=
  -32 / 45 + 16 * x / 5 - 632 * x ^ 2 / 135 + 136 * x ^ 3 / 135 + 29 * x ^ 4 / 54 +
    11 * x ^ 5 / 27 + 13 * x ^ 6 / 54

/-- `U₂ = x⁵ · (1-x) N₂/x⁵`. -/
noncomputable def sbU2 (x : ℝ) : ℝ :=
  -16 / 45 + 16 * x / 9 - 28 * x ^ 2 / 9 + 14 * x ^ 3 / 9 + 20 * x ^ 4 / 9 - 193 * x ^ 5 / 90 +
    x ^ 6 / 9 - x ^ 7 / 18

theorem log_one_sub_eq_logT1 (x : ℝ) : log (1 - x) = x * logT1 x + logRem x := by
  unfold logT1 logRem
  ring

theorem setBPrim_eq_zero_form {x : ℝ} (hx : x ≠ 0) :
    setBPrim x = sbPoly x + sbU1 x * (logRem x / x ^ 4) +
      sbU2 x * (logRem x / x ^ 4) * (2 * logT1 x + logRem x / x ^ 4 * x ^ 3) -
      8 / 45 * Li₂ x + 4 / 3 * logOneSubSqPrim x := by
  unfold setBPrim
  rw [log_one_sub_eq_logT1]
  generalize logRem x = r
  simp only [sbN0, sbN1, sbN2, sbPoly, sbU1, sbU2, logT1]
  field_simp
  ring

/-- `logRem x / x⁴ → 0` as `x → 0⁺`. -/
theorem tendsto_logRem_div_zero : Tendsto (fun x => logRem x / x ^ 4) (𝓝[>] 0) (𝓝 0) :=
  (tendsto_div_pow_four_of_abs_le (c := 1 / 2) (M := 2) (by norm_num)
    fun x hx => abs_logRem_le hx.1.le hx.2.le).1

theorem tendsto_setBPrim_zero :
    Tendsto setBPrim (𝓝[>] 0) (𝓝 (2 / 9 - 8 / 3 * zeta3)) := by
  have hc : ∀ {f : ℝ → ℝ}, Continuous f → Tendsto f (𝓝[>] 0) (𝓝 (f 0)) := fun hf =>
    (hf.tendsto 0).mono_left nhdsWithin_le_nhds
  have hP := hc (f := sbPoly) (by unfold sbPoly; fun_prop)
  have hU1 := hc (f := sbU1) (by unfold sbU1; fun_prop)
  have hU2 := hc (f := sbU2) (by unfold sbU2; fun_prop)
  have hT := hc (f := logT1) (by unfold logT1; fun_prop)
  have hx3 := hc (f := fun x : ℝ => x ^ 3) (by fun_prop)
  have hρ := tendsto_logRem_div_zero
  have h := ((((hP.add (hU1.mul hρ)).add ((hU2.mul hρ).mul ((hT.const_mul 2).add
    (hρ.mul hx3)))).sub (tendsto_Li₂_zero_right.const_mul (8 / 45))).add
    (tendsto_logOneSubSqPrim_zero.const_mul (4 / 3)))
  have hv : sbPoly 0 + sbU1 0 * 0 + sbU2 0 * 0 * (2 * logT1 0 + 0 * (fun x : ℝ => x ^ 3) 0) -
      8 / 45 * 0 + 4 / 3 * (-2 * zeta3) = 2 / 9 - 8 / 3 * zeta3 := by
    simp only [sbPoly]
    ring
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  rw [setBPrim_eq_zero_form hx.ne']

/-! ### The endpoint `x → 1⁻` -/

theorem tendsto_one_sub_mul_log_one : Tendsto (fun x : ℝ => (1 - x) * log (1 - x)) (𝓝[<] 1)
    (𝓝 0) :=
  tendsto_mul_log_zero.comp tendsto_one_sub_nhdsLT_one

theorem tendsto_one_sub_mul_log_sq_one :
    Tendsto (fun x : ℝ => (1 - x) * log (1 - x) ^ 2) (𝓝[<] 1) (𝓝 0) :=
  tendsto_mul_log_sq_zero.comp tendsto_one_sub_nhdsLT_one

theorem tendsto_setBPrim_one :
    Tendsto setBPrim (𝓝[<] 1) (𝓝 (-871 / 324 - 4 / 135 * π ^ 2)) := by
  have hc : ∀ {f : ℝ → ℝ}, ContinuousAt f 1 → Tendsto f (𝓝[<] 1) (𝓝 (f 1)) := fun hf =>
    hf.tendsto.mono_left nhdsWithin_le_nhds
  have h0 := hc (f := fun x => sbN0 x / x ^ 3) (by unfold sbN0; fun_prop (disch := norm_num))
  have h1 := hc (f := fun x => sbN1 x / x ^ 4) (by unfold sbN1; fun_prop (disch := norm_num))
  have h2 := hc (f := fun x => sbN2 x / x ^ 5) (by unfold sbN2; fun_prop (disch := norm_num))
  have h := (((h0.add (h1.mul tendsto_one_sub_mul_log_one)).add
    (h2.mul tendsto_one_sub_mul_log_sq_one)).sub (tendsto_Li₂_one_left.const_mul (8 / 45))).add
    (tendsto_logOneSubSqPrim_one.const_mul (4 / 3))
  have hv : sbN0 1 / 1 ^ 3 + sbN1 1 / 1 ^ 4 * 0 + sbN2 1 / 1 ^ 5 * 0 - 8 / 45 * (π ^ 2 / 6) +
      4 / 3 * 0 = -871 / 324 - 4 / 135 * π ^ 2 := by
    simp only [sbN0]
    ring
  rw [hv] at h
  exact h

/-! ### The set (b) value -/

theorem intervalIntegrable_and_integral_setB_closed :
    IntervalIntegrable (fun x => (1 - x) * piHatX x ^ 2) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (1 - x) * piHatX x ^ 2 = aSetB := by
  have h := intervalIntegrable_and_integral_eq_of_nonneg (fun x hx => hasDerivAt_setBPrim hx)
    (fun x hx => mul_nonneg (by linarith [hx.2]) (sq_nonneg _)) tendsto_setBPrim_zero
    tendsto_setBPrim_one
  refine ⟨h.1, ?_⟩
  rw [h.2, aSetB]
  ring

/-- The set (b) integrand agrees with its closed form almost everywhere on `(0,1]`. -/
theorem setB_integrand_ae :
    (fun x => (1 - x) * piHat (x ^ 2 / (1 - x)) ^ 2) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      fun x => (1 - x) * piHatX x ^ 2 := by
  filter_upwards [QED.TwoLoop.VPUnit.ae_mem_Ioo] with x hx
  rw [piHat_photonVar hx]

/-- The set (b) integrand `(1-x) Π̂(x²/(1-x))²` is interval integrable on `[0,1]`. -/
theorem intervalIntegrable_setB :
    IntervalIntegrable (fun x => (1 - x) * piHat (x ^ 2 / (1 - x)) ^ 2) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
    intervalIntegrable_and_integral_setB_closed.1).congr setB_integrand_ae.symm

/-- **Set (b) (O3-13).** `∫₀¹ (1-x) Π̂(x²/(1-x))² dx = (8/3) ζ(3) - (4/135) π² - 943/324`. -/
theorem integral_setB :
    ∫ x in (0 : ℝ)..1, (1 - x) * piHat (x ^ 2 / (1 - x)) ^ 2 = aSetB := by
  rw [← intervalIntegrable_and_integral_setB_closed.2, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one]
  exact integral_congr_ae setB_integrand_ae

/-! ### One bubble: the normalization check -/

/-- `Π̂(s) ≥ 0` for `s ≥ 0`. -/
theorem piHat_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ piHat s := by
  unfold piHat
  refine mul_nonneg zero_le_two (intervalIntegral.integral_nonneg zero_le_one fun t ht => ?_)
  have h0 : 0 ≤ t * (1 - t) := mul_nonneg ht.1 (by linarith [ht.2])
  exact mul_nonneg h0 (log_nonneg (by nlinarith [mul_nonneg h0 hs]))

/-- The antiderivative of the one-bubble integrand `(1-x) Π̂(x²/(1-x))` on `(0,1)`. -/
noncomputable def oneBubblePrim (x : ℝ) : ℝ :=
  (13 * x ^ 2 + 22 * x) / 36 - 2 / (3 * x) +
    (x ^ 3 - x ^ 2 + 16 * x - 4) / (6 * x ^ 2) * ((1 - x) * log (1 - x)) - 2 * Li₂ x

theorem hasDerivAt_oneBubblePrim {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt oneBubblePrim ((1 - x) * piHatX x) x := by
  obtain ⟨hx0, hx1⟩ := hx
  have hx' : x ≠ 0 := hx0.ne'
  have hA := (hasDerivAt_poly7 0 (22 / 36) (13 / 36) 0 0 0 0 0 x)
  have hB := (hasDerivAt_const x (2 : ℝ)).div ((hasDerivAt_id' x).const_mul 3) (by positivity)
  have hC := (hasDerivAt_poly7 (-4) 16 (-1) 1 0 0 0 0 x).div
    ((hasDerivAt_pow 2 x).const_mul 6) (by positivity)
  have h := ((hA.sub hB).add (hC.mul (hasDerivAt_one_sub_mul_log hx1))).sub
    ((hasDerivAt_Li₂' ⟨hx0, hx1⟩).const_mul 2)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  · simp only [Pi.div_apply, piHatX]
    field_simp
    ring
  · simp only [oneBubblePrim, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]
    ring

/-- The regular part of `oneBubblePrim` at `0`. -/
noncomputable def obPoly (x : ℝ) : ℝ :=
  -3 + 2 * x + x ^ 2 / 2 + x ^ 3 / 9 + 49 * x ^ 4 / 72 - x ^ 5 / 36 + x ^ 6 / 24

/-- The coefficient of `logRem x / x⁴` in `oneBubblePrim` at `0`. -/
noncomputable def obU (x : ℝ) : ℝ :=
  -2 * x ^ 2 / 3 + 10 * x ^ 3 / 3 - 17 * x ^ 4 / 6 + x ^ 5 / 3 - x ^ 6 / 6

theorem oneBubblePrim_eq_zero_form {x : ℝ} (hx : x ≠ 0) :
    oneBubblePrim x = obPoly x + obU x * (logRem x / x ^ 4) - 2 * Li₂ x := by
  unfold oneBubblePrim
  rw [log_one_sub_eq_logT1]
  generalize logRem x = r
  simp only [obPoly, obU, logT1]
  field_simp
  ring

theorem tendsto_oneBubblePrim_zero : Tendsto oneBubblePrim (𝓝[>] 0) (𝓝 (-3)) := by
  have hc : ∀ {f : ℝ → ℝ}, Continuous f → Tendsto f (𝓝[>] 0) (𝓝 (f 0)) := fun hf =>
    (hf.tendsto 0).mono_left nhdsWithin_le_nhds
  have hP := hc (f := obPoly) (by unfold obPoly; fun_prop)
  have hU := hc (f := obU) (by unfold obU; fun_prop)
  have h := (hP.add (hU.mul tendsto_logRem_div_zero)).sub (tendsto_Li₂_zero_right.const_mul 2)
  have hv : obPoly 0 + obU 0 * 0 - 2 * 0 = -3 := by
    simp only [obPoly]
    ring
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  rw [oneBubblePrim_eq_zero_form hx.ne']

theorem tendsto_oneBubblePrim_one :
    Tendsto oneBubblePrim (𝓝[<] 1) (𝓝 (11 / 36 - π ^ 2 / 3)) := by
  have hc : ∀ {f : ℝ → ℝ}, ContinuousAt f 1 → Tendsto f (𝓝[<] 1) (𝓝 (f 1)) := fun hf =>
    hf.tendsto.mono_left nhdsWithin_le_nhds
  have h0 := hc (f := fun x : ℝ => (13 * x ^ 2 + 22 * x) / 36 - 2 / (3 * x))
    (by fun_prop (disch := norm_num))
  have h1 := hc (f := fun x : ℝ => (x ^ 3 - x ^ 2 + 16 * x - 4) / (6 * x ^ 2))
    (by fun_prop (disch := norm_num))
  have h := (h0.add (h1.mul tendsto_one_sub_mul_log_one)).sub
    (tendsto_Li₂_one_left.const_mul 2)
  have hv : (13 * 1 ^ 2 + 22 * 1) / 36 - 2 / (3 * 1) +
      (1 ^ 3 - 1 ^ 2 + 16 * 1 - 4) / (6 * 1 ^ 2) * 0 - 2 * (π ^ 2 / 6) =
      (11 / 36 - π ^ 2 / 3 : ℝ) := by ring
  rw [hv] at h
  exact h

theorem intervalIntegrable_and_integral_oneBubble_closed :
    IntervalIntegrable (fun x => (1 - x) * piHatX x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (1 - x) * piHatX x = 119 / 36 - π ^ 2 / 3 := by
  have h := intervalIntegrable_and_integral_eq_of_nonneg
    (fun x hx => hasDerivAt_oneBubblePrim hx) (fun x hx => ?_) tendsto_oneBubblePrim_zero
    tendsto_oneBubblePrim_one
  · refine ⟨h.1, ?_⟩
    rw [h.2]
    ring
  · rw [← piHat_photonVar hx]
    exact mul_nonneg (by linarith [hx.2])
      (piHat_nonneg (div_nonneg (sq_nonneg x) (by linarith [hx.2])))

/-- The one-bubble integrand agrees with its closed form almost everywhere on `(0,1]`. -/
theorem oneBubble_integrand_ae :
    (fun x => (1 - x) * piHat (x ^ 2 / (1 - x))) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      fun x => (1 - x) * piHatX x := by
  filter_upwards [QED.TwoLoop.VPUnit.ae_mem_Ioo] with x hx
  rw [piHat_photonVar hx]

/-- The one-bubble integrand `(1-x) Π̂(x²/(1-x))` is interval integrable on `[0,1]`. -/
theorem intervalIntegrable_oneBubble :
    IntervalIntegrable (fun x => (1 - x) * piHat (x ^ 2 / (1 - x))) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
    intervalIntegrable_and_integral_oneBubble_closed.1).congr oneBubble_integrand_ae.symm

/-- **One bubble.** `∫₀¹ (1-x) Π̂(x²/(1-x)) dx = 119/36 - π²/3`. -/
theorem integral_oneBubble :
    ∫ x in (0 : ℝ)..1, (1 - x) * piHat (x ^ 2 / (1 - x)) = 119 / 36 - π ^ 2 / 3 := by
  rw [← intervalIntegrable_and_integral_oneBubble_closed.2,
    intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  exact integral_congr_ae oneBubble_integrand_ae

/-- The one-bubble chain is the two-loop VP unit: its integral equals the double integral of
`QED.TwoLoop.VPUnit.integral_vpUnit`. -/
theorem integral_oneBubble_eq_vpUnit :
    ∫ x in (0 : ℝ)..1, (1 - x) * piHat (x ^ 2 / (1 - x)) =
      ∫ v in (0 : ℝ)..1, v ^ 2 * (1 - v ^ 2 / 3) / (1 - v ^ 2) *
        ∫ x in (0 : ℝ)..1, x ^ 2 * (1 - x) / (x ^ 2 + (1 - x) * (4 / (1 - v ^ 2))) := by
  rw [integral_oneBubble, QED.TwoLoop.VPUnit.integral_vpUnit]

end QED.Chain
