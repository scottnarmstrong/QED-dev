/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.VacuumPolarizationRadial
public import QED.WickModel.VacuumPolarizationBounds
public import QED.WickModel.VacuumPolarizationEnergyFirst
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import QED.Integration.LoopBounds
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pauli–Villars-summed spatial integrals with complex masses, at fixed `ε > 0`

The `ε > 0` analogue of `QED.WickModel.VacuumPolarizationRadial`. After the loop-energy integral,
the translation of the spatial momentum and the symmetrization `w⃗ ↦ -w⃗`, the energy-first
vacuum polarization at fixed Feynman parameter and fixed `ε > 0` reduces to two Pauli–Villars
sums over `w⃗ ∈ ℝ³` of powers of `z_f = -(|w⃗|² + D_f) + iε`, with real `D_f` of any sign:

* `integral_cRadialSum`: `∫ ∑_f c_f z_f^{-3/2} d³w = -2π i ∑_f c_f log(D_f - iε)` when
  `∑ c_f = 0`;
* `integral_cRadialPiece_eq_zero`: `∫ ∑_f c_f z_f^{-3/2} (ŵ^μ ŵ^ν + h^{μν} z_f) d³w = 0` when
  `∑ c_f = 0` and `∑ c_f D_f = 0`.

The logarithmic integral uses the antiderivative `log(r + √u) - r/√u` of `r² u^{-3/2}`,
`u = r² + D - iε` (`hasDerivAt_logAnti`), and `z^{-3/2} = i u^{-3/2}` (`neg_cpow_neg_three_halves`).
The covariance integral uses the antiderivative `r³ ∑_f c_f z_f^{-1/2}`, whose limit at infinity
vanishes by the second-order Pauli–Villars bound of packet 6b.

The declarations here are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.TwoLoop.VPHalfAt

open QED.WickModel QED.WickModel.VacuumPolarizationLimit QED.Integration

/-! ### Branches -/

theorem mem_slitPlane_of_im_neg {u : ℂ} (hu : u.im < 0) : u ∈ slitPlane :=
  mem_slitPlane_iff.2 (Or.inr hu.ne)

theorem ne_zero_of_im_neg {u : ℂ} (hu : u.im < 0) : u ≠ 0 := by
  rintro rfl
  simp at hu

/-- In the lower half-plane the principal square root stays in the lower half-plane. -/
theorem im_cpow_half_neg {u : ℂ} (hu : u.im < 0) : (u ^ (1 / 2 : ℂ)).im < 0 := by
  rw [cpow_def_of_ne_zero (ne_zero_of_im_neg hu), exp_im]
  have harg : (log u * (1 / 2 : ℂ)).im = arg u / 2 := by
    simp [log_im]
    ring
  rw [harg]
  have h1 : arg u < 0 := arg_neg_iff.2 hu
  have h2 := neg_pi_lt_arg u
  exact mul_neg_of_pos_of_neg (Real.exp_pos _)
    (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith))

/-- `exp(-3πi/2) = i`. -/
theorem exp_neg_three_halves_pi_I : exp (↑π * I * (-(3 / 2) : ℂ)) = I := by
  have e : (↑π * I * (-(3 / 2) : ℂ)) = ((π / 2 : ℝ) : ℂ) * I - 2 * π * I := by
    push_cast
    ring
  rw [e, exp_sub, exp_two_pi_mul_I, div_one, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- **The branch relation**: for `u` in the lower half-plane, `(-u)^{-3/2} = i u^{-3/2}`. -/
theorem neg_cpow_neg_three_halves {u : ℂ} (hu : u.im < 0) :
    (-u) ^ (-(3 / 2) : ℂ) = I * u ^ (-(3 / 2) : ℂ) := by
  have hu0 := ne_zero_of_im_neg hu
  have hnu : -u ≠ 0 := neg_ne_zero.2 hu0
  have hlog : log (-u) = log u + π * I := by
    apply Complex.ext
    · simp [log_re]
    · simp [log_im, arg_neg_eq_arg_add_pi_of_im_neg hu]
  rw [cpow_def_of_ne_zero hnu, cpow_def_of_ne_zero hu0, hlog, add_mul, exp_add,
    exp_neg_three_halves_pi_I]
  ring

/-- `((a : ℂ) y)^c = a^c y^c` for real `a > 0`. -/
theorem ofReal_mul_cpow {a : ℝ} (ha : 0 < a) {y : ℂ} (hy : y ≠ 0) (c : ℂ) :
    ((a : ℂ) * y) ^ c = (a : ℂ) ^ c * y ^ c := by
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.2 ha.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero ha' hy), cpow_def_of_ne_zero ha', cpow_def_of_ne_zero hy,
    log_ofReal_mul ha hy, ← ofReal_log ha.le, add_mul, exp_add]

/-- `((r²) : ℂ)^{1/2} = r` for `r ≥ 0`. -/
theorem sq_cpow_half {r : ℝ} (hr : 0 ≤ r) : ((r : ℂ) ^ 2) ^ (1 / 2 : ℂ) = r := by
  have e : ((r : ℂ) ^ 2) = ((r ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e, e2, ← ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hr]

/-! ### The logarithmic antiderivative -/

/-- `log(r + √u) - r/√u` with `u = r² + Δ`. -/
noncomputable def logAnti (Δ : ℂ) (r : ℝ) : ℂ :=
  log ((r : ℂ) + ((r : ℂ) ^ 2 + Δ) ^ (1 / 2 : ℂ)) - (r : ℂ) * ((r : ℂ) ^ 2 + Δ) ^ (-(1 / 2) : ℂ)

theorem im_sq_add {Δ : ℂ} (r : ℝ) : ((r : ℂ) ^ 2 + Δ).im = Δ.im := by
  simp [sq]

/-- **The antiderivative**: `d/dr (log(r + √u) - r/√u) = r² u^{-3/2}`, `u = r² + Δ`, `Im Δ < 0`. -/
theorem hasDerivAt_logAnti {Δ : ℂ} (hΔ : Δ.im < 0) (r : ℝ) :
    HasDerivAt (logAnti Δ) ((r : ℂ) ^ 2 * ((r : ℂ) ^ 2 + Δ) ^ (-(3 / 2) : ℂ)) r := by
  set u := (r : ℂ) ^ 2 + Δ with hu_def
  have hu : u.im < 0 := by rw [hu_def, im_sq_add]; exact hΔ
  have hu0 := ne_zero_of_im_neg hu
  have hsl := mem_slitPlane_of_im_neg hu
  set S := u ^ (1 / 2 : ℂ) with hS_def
  have hSi : S.im < 0 := im_cpow_half_neg hu
  have hS0 : S ≠ 0 := ne_zero_of_im_neg hSi
  have hrS : ((r : ℂ) + S).im < 0 := by simpa using hSi
  have hrS0 := ne_zero_of_im_neg hrS
  -- the complex-variable derivatives
  have hp : HasDerivAt (fun ζ : ℂ => ζ ^ 2 + Δ) (2 * (r : ℂ)) (r : ℂ) := by
    simpa using (hasDerivAt_pow 2 (r : ℂ)).add_const Δ
  have h1 := (hp.cpow_const (c := (1 / 2 : ℂ)) hsl).comp_ofReal
  have h2 := (hp.cpow_const (c := (-(1 / 2) : ℂ)) hsl).comp_ofReal
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 r := by
    simpa using (hasDerivAt_id r).ofReal_comp
  have hlog := (hid.add h1).clog_real (by
    show (r : ℂ) + ((r : ℂ) ^ 2 + Δ) ^ (1 / 2 : ℂ) ∈ slitPlane
    exact mem_slitPlane_of_im_neg hrS)
  have hprod := hid.mul h2
  have h := hlog.sub hprod
  unfold logAnti
  refine h.congr_deriv ?_
  -- the algebra
  have e1 : u ^ ((1 / 2 : ℂ) - 1) = S⁻¹ := by
    rw [show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num, cpow_neg]
  have e2 : u ^ ((-(1 / 2) : ℂ) - 1) = S⁻¹ * u⁻¹ := by
    rw [cpow_sub _ _ hu0, cpow_one, cpow_neg, div_eq_mul_inv]
  have e3 : u ^ (-(3 / 2) : ℂ) = S⁻¹ * u⁻¹ := by
    rw [← e2]
    norm_num
  have e4 : u ^ (-(1 / 2) : ℂ) = S⁻¹ := by rw [cpow_neg]
  simp only [Pi.add_apply, ← hu_def, ← hS_def, e1, e2, e3, e4]
  field_simp
  ring

/-- `log(√Δ) = log Δ / 2`. -/
theorem logAnti_zero {Δ : ℂ} (hΔ : Δ.im < 0) : logAnti Δ 0 = log Δ / 2 := by
  have hΔ0 := ne_zero_of_im_neg hΔ
  simp only [logAnti, ofReal_zero, zero_add, zero_mul, sub_zero]
  rw [show ((0 : ℂ) ^ 2 + Δ) = Δ by ring, cpow_def_of_ne_zero hΔ0]
  have him : (log Δ * (1 / 2 : ℂ)).im = arg Δ / 2 := by
    simp [log_im]
    ring
  rw [log_exp (by rw [him]; linarith [neg_pi_lt_arg Δ, arg_le_pi Δ])
    (by rw [him]; linarith [neg_pi_lt_arg Δ, arg_le_pi Δ, Real.pi_pos])]
  ring

/-- The profile `φ(s) = log(1 + √(1+s)) - 1/√(1+s)`, continuous at `0`. -/
noncomputable def phiLog (s : ℂ) : ℂ :=
  log (1 + (1 + s) ^ (1 / 2 : ℂ)) - ((1 + s) ^ (1 / 2 : ℂ))⁻¹

theorem continuousAt_phiLog : ContinuousAt phiLog 0 := by
  have hc : ContinuousAt (fun s : ℂ => (1 + s) ^ (1 / 2 : ℂ)) 0 := by
    have h := continuousAt_cpow_const (b := (1 / 2 : ℂ)) (a := 1 + 0) (by simp)
    exact h.comp (continuous_const.add continuous_id).continuousAt
  have h1 : (fun s : ℂ => (1 + s) ^ (1 / 2 : ℂ)) 0 = 1 := by simp
  have hlog : ContinuousAt (fun s : ℂ => log (1 + (1 + s) ^ (1 / 2 : ℂ))) 0 := by
    refine (continuousAt_clog ?_).comp (continuousAt_const.add hc)
    simp only [add_zero, one_cpow]
    norm_num
  have hinv : ContinuousAt (fun s : ℂ => ((1 + s) ^ (1 / 2 : ℂ))⁻¹) 0 :=
    hc.inv₀ (by simp)
  exact hlog.sub hinv

theorem phiLog_zero : phiLog 0 = log 2 - 1 := by
  simp only [phiLog, add_zero, one_cpow, inv_one]
  norm_num

/-- For `r > 0`, `log(r + √u) - r/√u = log r + φ(Δ/r²)`. -/
theorem logAnti_eq {Δ : ℂ} (hΔ : Δ.im < 0) {r : ℝ} (hr : 0 < r) :
    logAnti Δ r = (Real.log r : ℂ) + phiLog (Δ / (r : ℂ) ^ 2) := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  set y := 1 + Δ / (r : ℂ) ^ 2 with hy
  have hyi : y.im < 0 := by
    have e : y = 1 + Δ / ((r ^ 2 : ℝ) : ℂ) := by rw [hy]; push_cast; ring
    rw [e, add_im, one_im, zero_add, div_ofReal_im]
    exact div_neg_of_neg_of_pos hΔ hr2
  have hy0 := ne_zero_of_im_neg hyi
  have hu : (r : ℂ) ^ 2 + Δ = ((r ^ 2 : ℝ) : ℂ) * y := by
    rw [hy]
    push_cast
    field_simp
  have hT : ((r : ℂ) ^ 2 + Δ) ^ (1 / 2 : ℂ) = (r : ℂ) * y ^ (1 / 2 : ℂ) := by
    rw [hu, ofReal_mul_cpow hr2 hy0]
    push_cast
    rw [sq_cpow_half hr.le]
  have hTi : (y ^ (1 / 2 : ℂ)).im < 0 := im_cpow_half_neg hyi
  have hT0 := ne_zero_of_im_neg hTi
  have h1T : (1 + y ^ (1 / 2 : ℂ)).im < 0 := by simpa using hTi
  have h1T0 := ne_zero_of_im_neg h1T
  unfold logAnti phiLog
  rw [← hy, hT, cpow_neg, hT]
  rw [show (r : ℂ) + (r : ℂ) * y ^ (1 / 2 : ℂ) = (r : ℂ) * (1 + y ^ (1 / 2 : ℂ)) by ring,
    log_ofReal_mul hr h1T0]
  field_simp
  ring

/-- **The boundary term at infinity vanishes** for a Pauli–Villars sum with `∑ c_f = 0`. -/
theorem tendsto_sum_logAnti {c : Fin 3 → ℝ} {Δ : Fin 3 → ℂ} (hΔ : ∀ f, (Δ f).im < 0)
    (hc : ∑ f, c f = 0) :
    Tendsto (fun r : ℝ => ∑ f, (c f : ℂ) * logAnti (Δ f) r) atTop (𝓝 0) := by
  have hlim : ∀ f, Tendsto (fun r : ℝ => phiLog (Δ f / (r : ℂ) ^ 2)) atTop (𝓝 (phiLog 0)) := by
    intro f
    have h0 : Tendsto (fun r : ℝ => Δ f / (r : ℂ) ^ 2) atTop (𝓝 0) := by
      have hr : Tendsto (fun r : ℝ => ((r ^ 2)⁻¹ : ℝ)) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero)
      have hc' := ((continuous_ofReal.tendsto _).comp hr).const_mul (Δ f)
      simp only [ofReal_zero, mul_zero] at hc'
      refine hc'.congr fun r => ?_
      simp [div_eq_mul_inv]
    exact continuousAt_phiLog.tendsto.comp h0
  have hsum := tendsto_finsetSum Finset.univ fun f _ => (hlim f).const_mul (c f : ℂ)
  have hval : ∑ f, (c f : ℂ) * phiLog 0 = 0 := by
    rw [← Finset.sum_mul]
    have : ∑ f, (c f : ℂ) = 0 := by exact_mod_cast hc
    rw [this, zero_mul]
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  simp only [logAnti_eq (hΔ _) hr, mul_add, Finset.sum_add_distrib]
  have : ∑ f, (c f : ℂ) * (Real.log r : ℂ) = 0 := by
    rw [← Finset.sum_mul]
    have : ∑ f, (c f : ℂ) = 0 := by exact_mod_cast hc
    rw [this, zero_mul]
  rw [this, zero_add]

/-- **The radial logarithmic integral**: `∫₀^∞ r² ∑_f c_f (r² + Δ_f)^{-3/2} dr
= -(1/2) ∑_f c_f log Δ_f`, for `Im Δ_f < 0`, `∑ c_f = 0` and an integrable integrand. -/
theorem integral_Ioi_sum_logAnti {c : Fin 3 → ℝ} {Δ : Fin 3 → ℂ} (hΔ : ∀ f, (Δ f).im < 0)
    (hc : ∑ f, c f = 0)
    (hint : IntegrableOn (fun r : ℝ => ∑ f, (c f : ℂ) *
      ((r : ℂ) ^ 2 * ((r : ℂ) ^ 2 + Δ f) ^ (-(3 / 2) : ℂ))) (Ioi 0)) :
    ∫ r in Ioi (0 : ℝ), ∑ f, (c f : ℂ) * ((r : ℂ) ^ 2 * ((r : ℂ) ^ 2 + Δ f) ^ (-(3 / 2) : ℂ)) =
      -(∑ f, (c f : ℂ) * log (Δ f)) / 2 := by
  have hderiv : ∀ r ∈ Ici (0 : ℝ), HasDerivAt (fun r : ℝ => ∑ f, (c f : ℂ) * logAnti (Δ f) r)
      (∑ f, (c f : ℂ) * ((r : ℂ) ^ 2 * ((r : ℂ) ^ 2 + Δ f) ^ (-(3 / 2) : ℂ))) r := fun r _ =>
    HasDerivAt.fun_sum fun f _ => (hasDerivAt_logAnti (hΔ f) r).const_mul _
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint (tendsto_sum_logAnti hΔ hc)]
  simp only [logAnti_zero (hΔ _)]
  rw [zero_sub, neg_div, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

/-! ### The variable `z = -(ρ + D) + iε` -/

/-- `z = -(ρ + D) + iε`. -/
noncomputable def zε (ε D ρ : ℝ) : ℂ := -(((ρ + D : ℝ)) : ℂ) + (ε : ℂ) * I

theorem zε_eq (ε D : ℝ) (r : ℝ) :
    zε ε D (r ^ 2) = -((r : ℂ) ^ 2 + ((D : ℂ) - (ε : ℂ) * I)) := by
  simp only [zε]
  push_cast
  ring

theorem im_mass_sub {ε : ℝ} (hε : 0 < ε) (D : ℝ) : ((D : ℂ) - (ε : ℂ) * I).im < 0 := by
  simp [hε]

theorem zε_mem_slitPlane {ε : ℝ} (hε : 0 < ε) (D ρ : ℝ) : zε ε D ρ ∈ slitPlane :=
  mem_slitPlane_iff.2 (Or.inr (by simp [zε, hε.ne']))

/-- The radial profile `∑_f c_f z_f^{-3/2}`. -/
noncomputable def hSum (c D : Fin 3 → ℝ) (ε ρ : ℝ) : ℂ :=
  ∑ f, (c f : ℂ) * zε ε (D f) ρ ^ (-(3 / 2) : ℂ)

/-- The Pauli–Villars sum `∑_f c_f z_f^{-3/2}` on `ℝ³`, `z_f = -(|w|² + D_f) + iε`. -/
noncomputable def cRadialSum (c D : Fin 3 → ℝ) (ε : ℝ) (w : Fin 3 → ℝ) : ℂ :=
  hSum c D ε (∑ i, w i ^ 2)

theorem continuous_zε_cpow {ε : ℝ} (hε : 0 < ε) (D : ℝ) (s : ℂ) :
    Continuous fun ρ : ℝ => zε ε D ρ ^ s := by
  have hz : Continuous fun ρ : ℝ => zε ε D ρ := by unfold zε; fun_prop
  exact hz.cpow continuous_const fun ρ => zε_mem_slitPlane hε D ρ

theorem continuous_hSum {ε : ℝ} (hε : 0 < ε) (c D : Fin 3 → ℝ) : Continuous (hSum c D ε) := by
  unfold hSum
  exact continuous_finsetSum _ fun f _ => continuous_const.mul (continuous_zε_cpow hε _ _)

/-- `max ε (|w|² + D₀) ≥ c (1 + ‖w‖)²`. -/
theorem exists_mul_le_max_sum_sq {ε : ℝ} (hε : 0 < ε) (D₀ : ℝ) :
    ∃ c > 0, ∀ w : Fin 3 → ℝ, c * (1 + ‖w‖) ^ 2 ≤ max ε (∑ i, w i ^ 2 + D₀) := by
  obtain ⟨c₀, hc₀, hcoer⟩ := exists_mul_one_add_norm_sq_le (n := 3) 0 one_pos
  have hA : 0 < 1 + |D₀| := by positivity
  refine ⟨min (c₀ / 2) (ε * c₀ / (2 * (1 + |D₀|))), by positivity, fun w => ?_⟩
  have h1 := hcoer w 0 1 (by simp) le_rfl
  simp only [Pi.zero_apply, add_zero] at h1
  have hW : c₀ * (1 + ‖w‖) ^ 2 - (1 + |D₀|) ≤ ∑ i, w i ^ 2 + D₀ := by
    linarith [neg_abs_le D₀]
  rcases le_or_gt (2 * (1 + |D₀|)) (c₀ * (1 + ‖w‖) ^ 2) with h | h
  · calc min (c₀ / 2) (ε * c₀ / (2 * (1 + |D₀|))) * (1 + ‖w‖) ^ 2
        ≤ c₀ / 2 * (1 + ‖w‖) ^ 2 := by gcongr; exact min_le_left _ _
      _ ≤ ∑ i, w i ^ 2 + D₀ := by linarith
      _ ≤ _ := le_max_right _ _
  · calc min (c₀ / 2) (ε * c₀ / (2 * (1 + |D₀|))) * (1 + ‖w‖) ^ 2
        ≤ ε * c₀ / (2 * (1 + |D₀|)) * (1 + ‖w‖) ^ 2 := by
          gcongr
          exact min_le_right _ _
      _ = ε * (c₀ * (1 + ‖w‖) ^ 2 / (2 * (1 + |D₀|))) := by ring
      _ ≤ ε * 1 := by
          gcongr
          rw [div_le_one (by positivity)]
          exact h.le
      _ = ε := mul_one ε
      _ ≤ _ := le_max_left _ _

theorem e32 : (-(((3 / 2 : ℝ)) : ℂ)) = -(3 / 2 : ℂ) := by push_cast; ring

theorem e12 : (-(((1 / 2 : ℝ)) : ℂ)) = -(1 / 2 : ℂ) := by push_cast; ring

/-- **Integrability**: `∑_f c_f z_f^{-3/2}` is integrable on `ℝ³` when `∑ c_f = 0` and
`D_0 ≤ D_f`. -/
theorem integrable_cRadialSum {c D : Fin 3 → ℝ} {ε : ℝ} (hε : 0 < ε) (hc : ∑ f, c f = 0)
    (hD : ∀ f, D 0 ≤ D f) : Integrable (cRadialSum c D ε) := by
  obtain ⟨c₁, hc₁, hlow⟩ := exists_mul_le_max_sum_sq hε (D 0)
  set K := 3 / 2 * (∑ f, |c f * 1| * (D f - D 0)) * c₁ ^ (-(3 / 2 + 1 : ℝ))
  have hbnd := (integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5)
    (by simp; norm_num)).const_mul K
  refine hbnd.mono' ((continuous_hSum hε c D).comp (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun w => ?_)
  have hcb : ∑ f, c f * 1 = 0 := by simpa using hc
  have b1 := norm_sum_mul_cpow_le_one hε (by norm_num : (0 : ℝ) ≤ 3 / 2) hcb
    (W := fun f => ∑ i, w i ^ 2 + D f) (fun f => by
      show ∑ i, w i ^ 2 + D 0 ≤ ∑ i, w i ^ 2 + D f
      linarith [hD f])
  simp only [mul_one, e32] at b1
  have hr := rpow_neg_le_of_mul_sq_le hc₁ (by positivity : 0 < 1 + ‖w‖) (hlow w)
    (r := 3 / 2 + 1) (by norm_num)
  have hS : 0 ≤ ∑ f, |c f| * (D f - D 0) := Finset.sum_nonneg fun f _ =>
    mul_nonneg (abs_nonneg _) (by linarith [hD f])
  have e : ∀ f, ∑ i, w i ^ 2 + D f - (∑ i, w i ^ 2 + D 0) = D f - D 0 := fun f => by ring
  simp only [e] at b1
  unfold cRadialSum hSum zε
  refine b1.trans ?_
  have hu5 : (1 + ‖w‖) ^ (-(2 * (3 / 2 + 1 : ℝ))) = (1 + ‖w‖) ^ (-(5 : ℝ)) := by norm_num
  simp only [K, mul_one]
  calc 3 / 2 * (∑ f, |c f| * (D f - D 0)) * max ε (∑ i, w i ^ 2 + D 0) ^ (-(3 / 2 + 1 : ℝ))
      ≤ 3 / 2 * (∑ f, |c f| * (D f - D 0)) *
          (c₁ ^ (-(3 / 2 + 1 : ℝ)) * (1 + ‖w‖) ^ (-(2 * (3 / 2 + 1 : ℝ)))) := by gcongr
    _ = _ := by rw [hu5]; ring

/-- **The logarithmic integral with complex masses**: for `ε > 0`, `∑ c_f = 0` and `D_0 ≤ D_f`,
`∫ ∑_f c_f z_f^{-3/2} d³w = -2π i ∑_f c_f log(D_f - iε)`. -/
theorem integral_cRadialSum {c D : Fin 3 → ℝ} {ε : ℝ} (hε : 0 < ε) (hc : ∑ f, c f = 0)
    (hD : ∀ f, D 0 ≤ D f) :
    ∫ w, cRadialSum c D ε w =
      -(2 * π * I * ∑ f, (c f : ℂ) * log ((D f : ℂ) - (ε : ℂ) * I)) := by
  have hint := integrable_cRadialSum hε hc hD
  have hrad := (integrable_comp_sum_sq_iff (hSum c D ε)).1 hint
  have hpt : ∀ r : ℝ, r ^ 2 • hSum c D ε (r ^ 2) = I * ∑ f, (c f : ℂ) *
      ((r : ℂ) ^ 2 * ((r : ℂ) ^ 2 + ((D f : ℂ) - (ε : ℂ) * I)) ^ (-(3 / 2) : ℂ)) := fun r => by
    have hz : ∀ f, zε ε (D f) (r ^ 2) ^ (-(3 / 2) : ℂ) =
        I * ((r : ℂ) ^ 2 + ((D f : ℂ) - (ε : ℂ) * I)) ^ (-(3 / 2) : ℂ) := fun f => by
      rw [zε_eq]
      exact neg_cpow_neg_three_halves (by rw [im_sq_add]; exact im_mass_sub hε _)
    simp only [hSum, hz, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Complex.real_smul]
    push_cast
    ring
  have hint' : IntegrableOn (fun r : ℝ => ∑ f, (c f : ℂ) *
      ((r : ℂ) ^ 2 * ((r : ℂ) ^ 2 + ((D f : ℂ) - (ε : ℂ) * I)) ^ (-(3 / 2) : ℂ))) (Ioi 0) := by
    have hr' : IntegrableOn (fun r : ℝ => -I * (r ^ 2 • hSum c D ε (r ^ 2))) (Ioi 0) :=
      hrad.const_mul (-I)
    refine hr'.congr_fun (fun r _ => ?_) measurableSet_Ioi
    dsimp only
    rw [hpt, ← mul_assoc, show -I * I = 1 by rw [neg_mul, I_mul_I, neg_neg], one_mul]
  have hI := integral_Ioi_sum_logAnti (fun f => im_mass_sub hε (D f)) hc hint'
  unfold cRadialSum
  rw [integral_comp_sum_sq]
  simp_rw [hpt]
  rw [integral_const_mul, hI, Complex.real_smul]
  push_cast
  ring

/-! ### The covariance integral -/

/-- The Pauli–Villars sum `∑_f c_f z_f^{-3/2} (ŵ^μ ŵ^ν + h^{μν} z_f)`. -/
noncomputable def cRadialPiece (c D : Fin 3 → ℝ) (ε : ℝ) (μ ν : Fin 4) (w : Fin 3 → ℝ) : ℂ :=
  ∑ f, (c f : ℂ) * (zε ε (D f) (∑ i, w i ^ 2) ^ (-(3 / 2) : ℂ) *
    ((((Fin.cons 0 w : Fin 4 → ℝ) μ * (Fin.cons 0 w : Fin 4 → ℝ) ν : ℝ) : ℂ)
      + (hproj μ ν : ℂ) * zε ε (D f) (∑ i, w i ^ 2)))

theorem cRadialPiece_succ_succ (c D : Fin 3 → ℝ) (ε : ℝ) (i : Fin 3) (w : Fin 3 → ℝ) :
    cRadialPiece c D ε i.succ i.succ w = ∑ f, (c f : ℂ) *
      (zε ε (D f) (∑ l, w l ^ 2) ^ (-(3 / 2) : ℂ) * (((w i ^ 2 : ℝ) : ℂ)
        + zε ε (D f) (∑ l, w l ^ 2))) := by
  have hh : hproj i.succ i.succ = 1 := by
    simp [hproj, e0, Minkowski.metric, Fin.succ_ne_zero]
  simp only [cRadialPiece, Fin.cons_succ, hh, ofReal_one, one_mul, sq]

theorem cRadialPiece_succ_succ_of_ne (c D : Fin 3 → ℝ) (ε : ℝ) {i j : Fin 3} (hij : i ≠ j)
    (w : Fin 3 → ℝ) :
    cRadialPiece c D ε i.succ j.succ w = (w i * w j) • hSum c D ε (∑ l, w l ^ 2) := by
  have hh : hproj i.succ j.succ = 0 := by
    simp [hproj, e0, Minkowski.metric, Fin.succ_inj, hij]
  simp only [cRadialPiece, Fin.cons_succ, hh, ofReal_zero, zero_mul, add_zero, hSum,
    Finset.smul_sum, Complex.real_smul]
  refine Finset.sum_congr rfl fun f _ => ?_
  push_cast
  ring

theorem cRadialPiece_zero_left (c D : Fin 3 → ℝ) (ε : ℝ) (ν : Fin 4) (w : Fin 3 → ℝ) :
    cRadialPiece c D ε 0 ν w = 0 := by
  have hh : hproj 0 ν = 0 := by
    refine Fin.cases ?_ (fun j => ?_) ν
    · simp [hproj, e0, Minkowski.metric]
    · simp [hproj, e0, Minkowski.metric, (Fin.succ_ne_zero j).symm]
  simp [cRadialPiece, hh]

theorem cRadialPiece_zero_right (c D : Fin 3 → ℝ) (ε : ℝ) (μ : Fin 4) (w : Fin 3 → ℝ) :
    cRadialPiece c D ε μ 0 w = 0 := by
  have hh : hproj μ 0 = 0 := by
    refine Fin.cases ?_ (fun j => ?_) μ
    · simp [hproj, e0, Minkowski.metric]
    · simp [hproj, e0, Minkowski.metric, Fin.succ_ne_zero j]
  simp [cRadialPiece, hh]

/-- The radial profile of the trace: `Ψ(ρ) = ∑_f c_f z_f^{-3/2} (ρ + 3 z_f)`. -/
noncomputable def cPsi (c D : Fin 3 → ℝ) (ε ρ : ℝ) : ℂ :=
  ∑ f, (c f : ℂ) * (zε ε (D f) ρ ^ (-(3 / 2) : ℂ) * ((ρ : ℂ) + 3 * zε ε (D f) ρ))

/-- `z^{-1/2} = z^{-3/2} z`. -/
theorem cpow_neg_half_eq {z : ℂ} (hz : z ≠ 0) :
    z ^ (-(1 / 2) : ℂ) = z ^ (-(3 / 2) : ℂ) * z := by
  rw [show (-(1 / 2) : ℂ) = -(3 / 2) + 1 by norm_num, cpow_add _ _ hz, cpow_one]

theorem zε_ne_zero {ε : ℝ} (hε : 0 < ε) (D ρ : ℝ) : zε ε D ρ ≠ 0 :=
  slitPlane_ne_zero (zε_mem_slitPlane hε D ρ)

/-- The antiderivative `r³ ∑_f c_f z_f^{-1/2}` of `r² Ψ(r²)`. -/
theorem hasDerivAt_cPsi {c D : Fin 3 → ℝ} {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    HasDerivAt (fun r : ℝ => (r : ℂ) ^ 3 * ∑ f, (c f : ℂ) * zε ε (D f) (r ^ 2) ^ (-(1 / 2) : ℂ))
      ((r : ℂ) ^ 2 * cPsi c D ε (r ^ 2)) r := by
  have hz : ∀ f, HasDerivAt (fun r : ℝ => zε ε (D f) (r ^ 2) ^ (-(1 / 2) : ℂ))
      ((2 * r) • ((((1 / 2 : ℝ)) : ℂ) * zε ε (D f) (r ^ 2) ^ (-(3 / 2) : ℂ))) r := fun f => by
    have h1 := hasDerivAt_cpow_neg hε (1 / 2) (r ^ 2 + D f)
    have h2 : HasDerivAt (fun r : ℝ => r ^ 2 + D f) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r).add_const (D f)
    have h3 := h1.scomp r h2
    simp only [e12, show ((1 / 2 : ℝ) + 1 : ℝ) = 3 / 2 by norm_num, e32] at h3
    exact h3
  have hsum : HasDerivAt (fun r : ℝ => ∑ f, (c f : ℂ) * zε ε (D f) (r ^ 2) ^ (-(1 / 2) : ℂ))
      (∑ f, (c f : ℂ) * ((2 * r) • ((((1 / 2 : ℝ)) : ℂ) *
        zε ε (D f) (r ^ 2) ^ (-(3 / 2) : ℂ)))) r :=
    HasDerivAt.fun_sum fun f _ => (hz f).const_mul _
  have hr3 : HasDerivAt (fun r : ℝ => (r : ℂ) ^ 3) (3 * (r : ℂ) ^ 2) r := by
    have := (hasDerivAt_pow 3 (r : ℂ)).comp_ofReal
    simpa using this
  refine (hr3.mul hsum).congr_deriv ?_
  simp only [cPsi, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [cpow_neg_half_eq (zε_ne_zero hε _ _), Complex.real_smul]
  push_cast
  ring

/-- The antiderivative vanishes at infinity, by the second-order Pauli–Villars bound. -/
theorem tendsto_cPsi_antideriv {c D : Fin 3 → ℝ} {ε : ℝ} (hε : 0 < ε) (hc : ∑ f, c f = 0)
    (hcD : ∑ f, c f * D f = 0) (hD : ∀ f, D 0 ≤ D f) :
    Tendsto (fun r : ℝ => (r : ℂ) ^ 3 * ∑ f, (c f : ℂ) * zε ε (D f) (r ^ 2) ^ (-(1 / 2) : ℂ))
      atTop (𝓝 0) := by
  set S₂ := ∑ f, |c f| * (D f - D 0) ^ 2
  set C := 1 / 2 * (1 / 2 + 1) * S₂ * (1 / 2 : ℝ) ^ (-(1 / 2 + 2 : ℝ))
  have hlim : Tendsto (fun r : ℝ => C * r ^ (-(2 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).const_mul C
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop (Real.sqrt (2 * |D 0|))] with r hr hr'
  have hcW : ∑ f, c f * (r ^ 2 + D f) = 0 := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hc, zero_mul, zero_add, hcD]
  have b2 := norm_sum_cpow_le_two hε (by norm_num : (0 : ℝ) ≤ 1 / 2) hc hcW
    (W := fun f => r ^ 2 + D f) (fun f => by
      show r ^ 2 + D 0 ≤ r ^ 2 + D f
      linarith [hD f])
  simp only [e12] at b2
  have e : ∀ f, r ^ 2 + D f - (r ^ 2 + D 0) = D f - D 0 := fun f => by ring
  simp only [e] at b2
  -- `max ε (r² + D₀) ≥ r²/2`
  have hr2 : 2 * |D 0| ≤ r ^ 2 := by
    have h0 : 0 ≤ Real.sqrt (2 * |D 0|) := Real.sqrt_nonneg _
    have := pow_le_pow_left₀ h0 hr' 2
    rwa [Real.sq_sqrt (by positivity)] at this
  have hlow : 1 / 2 * r ^ 2 ≤ max ε (r ^ 2 + D 0) :=
    le_trans (by linarith [neg_abs_le (D 0)]) (le_max_right _ _)
  have hrp := rpow_neg_le_of_mul_sq_le (by norm_num : (0 : ℝ) < 1 / 2) hr hlow
    (r := 1 / 2 + 2) (by norm_num)
  have hS₂ : 0 ≤ S₂ := Finset.sum_nonneg fun f _ => by positivity
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le]
  unfold zε
  calc r ^ 3 * ‖∑ f, (c f : ℂ) * (-((r ^ 2 + D f : ℝ) : ℂ) + (ε : ℂ) * I) ^ (-(1 / 2) : ℂ)‖
      ≤ r ^ 3 * (1 / 2 * (1 / 2 + 1) * S₂ * max ε (r ^ 2 + D 0) ^ (-(1 / 2 + 2 : ℝ))) := by
        gcongr
    _ ≤ r ^ 3 * (1 / 2 * (1 / 2 + 1) * S₂ *
          ((1 / 2 : ℝ) ^ (-(1 / 2 + 2 : ℝ)) * r ^ (-(2 * (1 / 2 + 2) : ℝ)))) := by gcongr
    _ = C * (r ^ (3 : ℝ) * r ^ (-(5 : ℝ))) := by
        rw [show (-(2 * (1 / 2 + 2)) : ℝ) = -5 by norm_num, ← Real.rpow_natCast r 3]
        simp only [C]
        push_cast
        ring
    _ = C * r ^ (-(2 : ℝ)) := by
        rw [← Real.rpow_add hr]
        norm_num

/-- **The covariance integral vanishes**: for `ε > 0`, `∑ c_f = 0`, `∑ c_f D_f = 0`, `D_0 ≤ D_f`,
and integrable diagonal components, `∫ ∑_f c_f z_f^{-3/2} (ŵ^μ ŵ^ν + h^{μν} z_f) d³w = 0`. -/
theorem integral_cRadialPiece_eq_zero {c D : Fin 3 → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hc : ∑ f, c f = 0) (hcD : ∑ f, c f * D f = 0) (hD : ∀ f, D 0 ≤ D f)
    (hdiag : ∀ i : Fin 3, Integrable (cRadialPiece c D ε i.succ i.succ)) (μ ν : Fin 4) :
    ∫ w, cRadialPiece c D ε μ ν w = 0 := by
  refine Fin.cases ?_ (fun i => ?_) μ
  · simp [cRadialPiece_zero_left]
  refine Fin.cases ?_ (fun j => ?_) ν
  · simp [cRadialPiece_zero_right]
  by_cases hij : i = j
  swap
  · simp_rw [cRadialPiece_succ_succ_of_ne c D ε hij]
    exact integral_coord_mul_coord_smul_radial (hSum c D ε) hij
  subst hij
  have hsame : ∀ a b : Fin 3,
      ∫ w, cRadialPiece c D ε a.succ a.succ w = ∫ w, cRadialPiece c D ε b.succ b.succ w := by
    intro a b
    rw [← integral_comp_swap (fun w => cRadialPiece c D ε a.succ a.succ w) a b]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [cRadialPiece_succ_succ, Equiv.swap_apply_left]
    have hs : ∑ l, w (Equiv.swap a b l) ^ 2 = ∑ l, w l ^ 2 :=
      Equiv.sum_comp (Equiv.swap a b) (fun l => w l ^ 2)
    rw [hs]
  have hsum : ∀ w, cRadialPiece c D ε (0 : Fin 3).succ (0 : Fin 3).succ w
      + cRadialPiece c D ε (1 : Fin 3).succ (1 : Fin 3).succ w
      + cRadialPiece c D ε (2 : Fin 3).succ (2 : Fin 3).succ w = cPsi c D ε (∑ l, w l ^ 2) := by
    intro w
    simp only [cRadialPiece_succ_succ, cPsi, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [Fin.sum_univ_three]
    push_cast
    ring
  have hint : Integrable fun w : Fin 3 → ℝ => cPsi c D ε (∑ l, w l ^ 2) :=
    (((hdiag 0).add (hdiag 1)).add (hdiag 2)).congr (Eventually.of_forall hsum)
  have hrad : ∫ w : Fin 3 → ℝ, cPsi c D ε (∑ l, w l ^ 2) = 0 := by
    rw [integral_comp_sum_sq]
    have hI := (integrable_comp_sum_sq_iff (cPsi c D ε)).1 hint
    have hI' : IntegrableOn (fun r : ℝ => (r : ℂ) ^ 2 * cPsi c D ε (r ^ 2)) (Ioi 0) := by
      refine hI.congr_fun (fun r _ => ?_) measurableSet_Ioi
      dsimp only
      rw [Complex.real_smul]
      push_cast
      ring
    have hval : ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ 2 * cPsi c D ε (r ^ 2) = 0 := by
      rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun r _ => hasDerivAt_cPsi hε r) hI'
        (tendsto_cPsi_antideriv hε hc hcD hD)]
      simp
    have e : ∫ r in Ioi (0 : ℝ), r ^ 2 • cPsi c D ε (r ^ 2) =
        ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ 2 * cPsi c D ε (r ^ 2) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
      rw [Complex.real_smul]
      push_cast
      ring
    rw [e, hval, smul_zero]
  have e := integral_congr_ae (μ := volume)
    (f := fun w => cRadialPiece c D ε (0 : Fin 3).succ (0 : Fin 3).succ w
      + cRadialPiece c D ε (1 : Fin 3).succ (1 : Fin 3).succ w
      + cRadialPiece c D ε (2 : Fin 3).succ (2 : Fin 3).succ w)
    (g := fun w : Fin 3 → ℝ => cPsi c D ε (∑ l, w l ^ 2)) (Eventually.of_forall hsum)
  have h3 : ∫ w : Fin 3 → ℝ, cPsi c D ε (∑ l, w l ^ 2)
      = 3 * ∫ w, cRadialPiece c D ε i.succ i.succ w := by
    rw [← e, integral_add (f := fun w => cRadialPiece c D ε (0 : Fin 3).succ (0 : Fin 3).succ w
      + cRadialPiece c D ε (1 : Fin 3).succ (1 : Fin 3).succ w) ((hdiag 0).add (hdiag 1))
      (hdiag 2), integral_add (hdiag 0) (hdiag 1), hsame 0 i, hsame 1 i, hsame 2 i]
    ring
  rw [hrad] at h3
  have h3' : (3 : ℂ) * ∫ w, cRadialPiece c D ε i.succ i.succ w = 0 := h3.symm
  exact (mul_eq_zero.1 h3').resolve_left (by norm_num)

end QED.TwoLoop.VPHalfAt

end
