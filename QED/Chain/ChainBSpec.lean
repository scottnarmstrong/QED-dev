/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.HeavyVPOuter
public import QED.Chain.VPChainSetB
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The flavour-summed subtracted bubble: spectral bounds and the regulator part `Δ_M` (O3-12)

Helper-level analysis for obligations O3-10 to O3-12 of `docs/HIGHER-LOOP-PLAN.md` (set (b),
the two-bubble chain). It is **not** frozen and does not depend on any three-loop model.

The open line and the electron loop have mass `1`; the regulator fermions have masses `M₁, M₂`
with the coefficients `c₁ = pvC1 M₁ M₂`, `c₂ = pvC2 M₁ M₂` of the two Pauli–Villars conditions.
The subtracted one-flavour bubble is the spectral integral
`QED.TwoLoop.UnitVPLink.specJ M s = ∫₀¹ ρ(v) s/(s + 4M²/(1-v²)) dv` (so that
`Π_loop(s) - Π_loop(0) = (e²/(4π²)) ∑_f c_f specJ(M_f, s)`, `QED.Chain.HeavyVP.flavourPi_sub_zero`).

## Objects

* `deltaM M₁ M₂ s = c₁ specJ(M₁, s) + c₂ specJ(M₂, s)`: the regulator part `Δ_M` of the
  flavour-summed subtracted bubble.
* `jSum M₁ M₂ s = specJ(1, s) + deltaM M₁ M₂ s`: the flavour-summed subtracted bubble divided by
  `r = e²/(4π²)`; by `jSum_eq_piHat_add` it is `Π̂(s) + Δ_M(s)` with `Π̂ = QED.Chain.piHat`.

## Main statements

* `specJ_le_div`: `0 ≤ specJ M s ≤ s/(15M²)` for `M ≠ 0`, `s ≥ 0` (the constant is the leading
  small-`s` coefficient).
* `specJ_anti`: `specJ M s ≤ specJ M' s` when `M'² ≤ M²`; with `specJ_one_eq_piHat`,
  `specJ M s ≤ Π̂(s)` for `M ≥ 1`.
* `deltaM_bounds` (**the divided-difference bound for the bubble itself**): for `M₁, M₂ ≥ 1` and
  `s ≥ 0`, with no constraint on `M₂/M₁`, `-(specJ(M₁,s) + specJ(M₂,s)) ≤ Δ_M(s) ≤ 0`. The
  pointwise step is `QED.TwoLoop.VPUnit.pv_pointwise` at `N = P = s`, `Q = 4/(1-v²)`, `μ_f = M_f²`.
* `abs_deltaM_le`: `|Δ_M(s)| ≤ (s/15)(1/M₁² + 1/M₂²)`; `neg_two_piHat_le_deltaM`:
  `-2Π̂(s) ≤ Δ_M(s)`; `abs_jSum_le`: `|jSum| ≤ 3Π̂(s)`.
* `measurable_specJ`, `measurable_jSum`: measurability in `s`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.Chain.ChainB

open QED.TwoLoop.VPUnit QED.TwoLoop.UnitVPLink

/-! ### The one-flavour spectral integral -/

/-- The integrand of `specJ` lies between `0` and `v²(1 - v²/3) s/(4M²)` on `[0,1]`. -/
theorem specJ_integrand_bound {M s v : ℝ} (hM : M ≠ 0) (hs : 0 ≤ s) (hv : v ∈ Icc (0 : ℝ) 1) :
    0 ≤ rho v * (s / (s + 4 * M ^ 2 / (1 - v ^ 2))) ∧
      rho v * (s / (s + 4 * M ^ 2 / (1 - v ^ 2))) ≤ v ^ 2 * (1 - v ^ 2 / 3) * s / (4 * M ^ 2) := by
  have hM2 : 0 < M ^ 2 := by positivity
  rcases hv.2.lt_or_eq with hv1 | rfl
  · have h1 : 0 < 1 - v ^ 2 := by nlinarith [hv.1]
    have hc := specMass_pos (M := M) hM hv.1 hv1
    have hr : 0 ≤ rho v := div_nonneg (mul_nonneg (sq_nonneg v) (by nlinarith [hv.1])) h1.le
    have hq : 0 ≤ s / (s + 4 * M ^ 2 / (1 - v ^ 2)) := div_nonneg hs (by positivity)
    refine ⟨mul_nonneg hr hq, ?_⟩
    have hle : s / (s + 4 * M ^ 2 / (1 - v ^ 2)) ≤ s / (4 * M ^ 2 / (1 - v ^ 2)) :=
      div_le_div_of_nonneg_left hs hc (by linarith)
    calc rho v * (s / (s + 4 * M ^ 2 / (1 - v ^ 2)))
        ≤ rho v * (s / (4 * M ^ 2 / (1 - v ^ 2))) := mul_le_mul_of_nonneg_left hle hr
      _ = v ^ 2 * (1 - v ^ 2 / 3) * s / (4 * M ^ 2) := by
          unfold rho
          field_simp
  · have h0 : rho 1 = 0 := by simp [rho]
    rw [h0, zero_mul]
    exact ⟨le_rfl, div_nonneg (mul_nonneg (by norm_num) hs) (by positivity)⟩

theorem measurable_specJ_integrand (M : ℝ) :
    Measurable (Function.uncurry fun (s v : ℝ) => rho v * (s / (s + 4 * M ^ 2 / (1 - v ^ 2)))) := by
  change Measurable fun q : ℝ × ℝ => rho q.2 * (q.1 / (q.1 + 4 * M ^ 2 / (1 - q.2 ^ 2)))
  unfold rho
  fun_prop

/-- `specJ M` is measurable. -/
theorem measurable_specJ (M : ℝ) : Measurable (specJ M) :=
  (stronglyMeasurable_intervalIntegral (measurable_specJ_integrand M)).measurable

theorem intervalIntegrable_specJ_integrand {M s : ℝ} (hM : M ≠ 0) (hs : 0 ≤ s) :
    IntervalIntegrable (fun v => rho v * (s / (s + 4 * M ^ 2 / (1 - v ^ 2)))) volume 0 1 := by
  have hm : Measurable fun v => rho v * (s / (s + 4 * M ^ 2 / (1 - v ^ 2))) := by
    unfold rho
    fun_prop
  refine ((by fun_prop : Continuous fun v : ℝ => v ^ 2 * (1 - v ^ 2 / 3) * s / (4 * M ^ 2)
    ).intervalIntegrable 0 1).mono_fun hm.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun v hv => ?_)
  rw [uIoc_of_le zero_le_one] at hv
  obtain ⟨b0, b1⟩ := specJ_integrand_bound hM hs (Ioc_subset_Icc_self hv)
  dsimp only
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg b0, abs_of_nonneg (b0.trans b1)]
  exact b1

theorem integral_specJ_bound (M s : ℝ) :
    ∫ v in (0 : ℝ)..1, v ^ 2 * (1 - v ^ 2 / 3) * s / (4 * M ^ 2) = s / (15 * M ^ 2) := by
  have e : (fun v : ℝ => v ^ 2 * (1 - v ^ 2 / 3) * s / (4 * M ^ 2)) =
      fun v => (v ^ 2 - v ^ 4 / 3) * (s / (4 * M ^ 2)) := by
    funext v
    ring
  rw [e, intervalIntegral.integral_mul_const, intervalIntegral.integral_sub
    ((continuous_pow 2).intervalIntegrable 0 1)
    (((continuous_pow 4).div_const 3).intervalIntegrable 0 1),
    intervalIntegral.integral_div, integral_pow, integral_pow]
  rcases eq_or_ne M 0 with rfl | hM
  · simp
  · field_simp
    ring

theorem specJ_nonneg {M s : ℝ} (hM : M ≠ 0) (hs : 0 ≤ s) : 0 ≤ specJ M s :=
  intervalIntegral.integral_nonneg zero_le_one fun _ hv => (specJ_integrand_bound hM hs hv).1

/-- **Small-`s` decay of one flavour**: `specJ M s ≤ s/(15M²)` for `M ≠ 0`, `s ≥ 0`. -/
theorem specJ_le_div {M s : ℝ} (hM : M ≠ 0) (hs : 0 ≤ s) : specJ M s ≤ s / (15 * M ^ 2) := by
  rw [← integral_specJ_bound M s]
  exact intervalIntegral.integral_mono_on zero_le_one (intervalIntegrable_specJ_integrand hM hs)
    ((by fun_prop : Continuous fun v : ℝ => v ^ 2 * (1 - v ^ 2 / 3) * s / (4 * M ^ 2)
      ).intervalIntegrable 0 1) fun _ hv => (specJ_integrand_bound hM hs hv).2

/-- **Monotonicity in the mass**: `specJ M s ≤ specJ M' s` for `M' ≠ 0`, `M'² ≤ M²`, `s ≥ 0`. -/
theorem specJ_anti {M M' s : ℝ} (hM' : M' ≠ 0) (hMM : M' ^ 2 ≤ M ^ 2) (hs : 0 ≤ s) :
    specJ M s ≤ specJ M' s := by
  have hM : M ≠ 0 := by
    rintro rfl
    have : 0 < M' ^ 2 := by positivity
    have h0 : M' ^ 2 ≤ 0 := by simpa using hMM
    linarith
  refine intervalIntegral.integral_mono_on zero_le_one (intervalIntegrable_specJ_integrand hM hs)
    (intervalIntegrable_specJ_integrand hM' hs) fun v hv => ?_
  rcases hv.2.lt_or_eq with hv1 | rfl
  · have h1 : 0 < 1 - v ^ 2 := by nlinarith [hv.1]
    have hc' := specMass_pos (M := M') hM' hv.1 hv1
    have hr : 0 ≤ rho v := div_nonneg (mul_nonneg (sq_nonneg v) (by nlinarith [hv.1])) h1.le
    refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hs (by positivity) ?_) hr
    have : 4 * M' ^ 2 / (1 - v ^ 2) ≤ 4 * M ^ 2 / (1 - v ^ 2) :=
      div_le_div_of_nonneg_right (by linarith) h1.le
    linarith
  · simp [rho]

/-- At unit mass the spectral integral is the renormalized bubble `Π̂`. -/
theorem specJ_one_eq_piHat {s : ℝ} (hs : -4 < s) : specJ 1 s = QED.Chain.piHat s := by
  rw [QED.Chain.piHat_eq_spectral hs]
  unfold specJ rho
  simp only [one_pow, mul_one]

/-- `specJ M s ≤ Π̂(s)` for `M ≥ 1`, `s ≥ 0`. -/
theorem specJ_le_piHat {M s : ℝ} (hM : 1 ≤ M) (hs : 0 ≤ s) : specJ M s ≤ QED.Chain.piHat s := by
  rw [← specJ_one_eq_piHat (by linarith)]
  exact specJ_anti one_ne_zero (by nlinarith) hs

/-! ### The regulator part of the flavour-summed bubble -/

/-- **The regulator part** `Δ_M(s) = c₁ specJ(M₁, s) + c₂ specJ(M₂, s)` of the flavour-summed
subtracted bubble (electron loop mass `1`). -/
noncomputable def deltaM (M₁ M₂ s : ℝ) : ℝ :=
  pvC1 M₁ M₂ * specJ M₁ s + pvC2 M₁ M₂ * specJ M₂ s

/-- **The flavour-summed subtracted bubble** (divided by `e²/(4π²)`):
`specJ(1, s) + c₁ specJ(M₁, s) + c₂ specJ(M₂, s)`. -/
noncomputable def jSum (M₁ M₂ s : ℝ) : ℝ := specJ 1 s + deltaM M₁ M₂ s

theorem jSum_eq_piHat_add {M₁ M₂ s : ℝ} (hs : 0 ≤ s) :
    jSum M₁ M₂ s = QED.Chain.piHat s + deltaM M₁ M₂ s := by
  rw [jSum, specJ_one_eq_piHat (by linarith)]

theorem measurable_deltaM (M₁ M₂ : ℝ) : Measurable (deltaM M₁ M₂) :=
  ((measurable_specJ M₁).const_mul _).add ((measurable_specJ M₂).const_mul _)

theorem measurable_jSum (M₁ M₂ : ℝ) : Measurable (jSum M₁ M₂) :=
  (measurable_specJ 1).add (measurable_deltaM M₁ M₂)

/-- **The divided-difference bound for the bubble.** For `M₁, M₂ ≥ 1` and `s ≥ 0`, with no
constraint on `M₂/M₁`: `-(specJ(M₁,s) + specJ(M₂,s)) ≤ Δ_M(s) ≤ 0`. (When `M₁² = M₂²` the
coefficients are `0` by Lean's division convention.) -/
theorem deltaM_bounds {M₁ M₂ s : ℝ} (h1 : 1 ≤ M₁) (h2 : 1 ≤ M₂) (hs : 0 ≤ s) :
    -(specJ M₁ s + specJ M₂ s) ≤ deltaM M₁ M₂ s ∧ deltaM M₁ M₂ s ≤ 0 := by
  have hM₁ : M₁ ≠ 0 := by positivity
  have hM₂ : M₂ ≠ 0 := by positivity
  have n1 := specJ_nonneg hM₁ hs
  have n2 := specJ_nonneg hM₂ hs
  by_cases h : M₁ ^ 2 = M₂ ^ 2
  · simp only [deltaM, pvC1, pvC2, h, sub_self, div_zero, zero_mul, add_zero]
    constructor <;> linarith
  have hμ₁ : 1 ≤ M₁ ^ 2 := one_le_pow₀ h1
  have hμ₂ : 1 ≤ M₂ ^ 2 := one_le_pow₀ h2
  have I1 := intervalIntegrable_specJ_integrand hM₁ hs
  have I2 := intervalIntegrable_specJ_integrand hM₂ hs
  have hpt : ∀ v ∈ Icc (0 : ℝ) 1,
      -(rho v * (s / (s + 4 * M₁ ^ 2 / (1 - v ^ 2))) +
          rho v * (s / (s + 4 * M₂ ^ 2 / (1 - v ^ 2)))) ≤
        pvC1 M₁ M₂ * (rho v * (s / (s + 4 * M₁ ^ 2 / (1 - v ^ 2)))) +
          pvC2 M₁ M₂ * (rho v * (s / (s + 4 * M₂ ^ 2 / (1 - v ^ 2)))) ∧
      pvC1 M₁ M₂ * (rho v * (s / (s + 4 * M₁ ^ 2 / (1 - v ^ 2)))) +
          pvC2 M₁ M₂ * (rho v * (s / (s + 4 * M₂ ^ 2 / (1 - v ^ 2)))) ≤ 0 := by
    intro v hv
    rcases hv.2.lt_or_eq with hv1 | rfl
    · have h1v : 0 < 1 - v ^ 2 := by nlinarith [hv.1]
      have hq : 0 < 4 / (1 - v ^ 2) := by positivity
      have hr : 0 ≤ rho v := div_nonneg (mul_nonneg (sq_nonneg v) (by nlinarith [hv.1])) h1v.le
      have e1 : 4 * M₁ ^ 2 / (1 - v ^ 2) = 4 / (1 - v ^ 2) * M₁ ^ 2 := by ring
      have e2 : 4 * M₂ ^ 2 / (1 - v ^ 2) = 4 / (1 - v ^ 2) * M₂ ^ 2 := by ring
      obtain ⟨b1, b2⟩ := pv_pointwise (N := s) (P := s) (Q := 4 / (1 - v ^ 2)) hs hq.le
        (by linarith) hμ₁ hμ₂ h
      have m1 := mul_le_mul_of_nonneg_left b1 hr
      have m2 := mul_le_mul_of_nonneg_left b2 hr
      simp only [pvC1, pvC2]
      rw [e1, e2]
      constructor <;> nlinarith
    · simp [rho]
  have hsum : deltaM M₁ M₂ s =
      ∫ v in (0 : ℝ)..1, (pvC1 M₁ M₂ * (rho v * (s / (s + 4 * M₁ ^ 2 / (1 - v ^ 2)))) +
        pvC2 M₁ M₂ * (rho v * (s / (s + 4 * M₂ ^ 2 / (1 - v ^ 2))))) := by
    rw [intervalIntegral.integral_add (I1.const_mul _) (I2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rfl
  have hneg : -(specJ M₁ s + specJ M₂ s) =
      ∫ v in (0 : ℝ)..1, -(rho v * (s / (s + 4 * M₁ ^ 2 / (1 - v ^ 2))) +
        rho v * (s / (s + 4 * M₂ ^ 2 / (1 - v ^ 2)))) := by
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_add I1 I2]
    rfl
  rw [hsum, hneg]
  constructor
  · exact intervalIntegral.integral_mono_on zero_le_one (I1.add I2).neg
      ((I1.const_mul _).add (I2.const_mul _)) fun v hv => (hpt v hv).1
  · have := intervalIntegral.integral_mono_on zero_le_one
      ((I1.const_mul _).add (I2.const_mul _)) (intervalIntegrable_const (c := (0 : ℝ)))
      fun v hv => (hpt v hv).2
    simpa using this

/-- **Small-`s` decay of `Δ_M`, uniform in `M₂/M₁`**: for `M₁, M₂ ≥ 1`, `s ≥ 0`,
`|Δ_M(s)| ≤ (s/15)(1/M₁² + 1/M₂²)`. -/
theorem abs_deltaM_le {M₁ M₂ s : ℝ} (h1 : 1 ≤ M₁) (h2 : 1 ≤ M₂) (hs : 0 ≤ s) :
    |deltaM M₁ M₂ s| ≤ s / 15 * (1 / M₁ ^ 2 + 1 / M₂ ^ 2) := by
  obtain ⟨b1, b2⟩ := deltaM_bounds h1 h2 hs
  have l1 := specJ_le_div (M := M₁) (by positivity) hs
  have l2 := specJ_le_div (M := M₂) (by positivity) hs
  have e : s / 15 * (1 / M₁ ^ 2 + 1 / M₂ ^ 2) = s / (15 * M₁ ^ 2) + s / (15 * M₂ ^ 2) := by
    have : M₁ ≠ 0 := by positivity
    have : M₂ ≠ 0 := by positivity
    field_simp
  rw [abs_of_nonpos b2, e]
  linarith

/-- `-2Π̂(s) ≤ Δ_M(s)` for `M₁, M₂ ≥ 1`, `s ≥ 0`. -/
theorem neg_two_piHat_le_deltaM {M₁ M₂ s : ℝ} (h1 : 1 ≤ M₁) (h2 : 1 ≤ M₂) (hs : 0 ≤ s) :
    -(2 * QED.Chain.piHat s) ≤ deltaM M₁ M₂ s := by
  have b := (deltaM_bounds h1 h2 hs).1
  have l1 := specJ_le_piHat h1 hs
  have l2 := specJ_le_piHat h2 hs
  linarith

/-- `|jSum M₁ M₂ s| ≤ 3Π̂(s)` for `M₁, M₂ ≥ 1`, `s ≥ 0`. -/
theorem abs_jSum_le {M₁ M₂ s : ℝ} (h1 : 1 ≤ M₁) (h2 : 1 ≤ M₂) (hs : 0 ≤ s) :
    |jSum M₁ M₂ s| ≤ 3 * QED.Chain.piHat s := by
  have b := neg_two_piHat_le_deltaM h1 h2 hs
  have b2 := (deltaM_bounds h1 h2 hs).2
  have p := QED.Chain.piHat_nonneg hs
  rw [jSum_eq_piHat_add hs, abs_le]
  constructor <;> linarith

end QED.Chain.ChainB
