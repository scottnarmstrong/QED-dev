/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.OneLoopBridgeWick
public import QED.DimReg.OneLoopReduction
public import QED.OneLoop.PauliLimit
public import QED.Frozen.OneLoop.PauliFormFactorLimit
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# Pilot P1: the one-loop Pauli form factor, dimensional regularization against the model

The one-loop anomaly is proved in the regulated four-dimensional model (photon mass `m_γ`,
Pauli–Villars mass `Λ`, momentum transfer `q² > 0`, all removed in a joint limit):
`F₂ / (α/π) = ½ ∫ dF pauliIntegrand → ½` (`QED.OneLoop.VertexLimit.tendsto_integral_pauliIntegrand`,
`QED.OneLoop.VertexLimit.formFactorB_eq`). This module links that limit to the dimensionally
regularized (DR) one-loop vertex, built from the values `QED.DimReg.OneLoopSchwinger.val` of the
on-shell family `D₀ = k²`, `D₁ = (k + p)² - 1` (`m = 1`), through one common
Feynman-parametric integrand.

**The DR integrand.** Projected onto the Pauli structure at `q = 0`, the one-loop vertex in
`d` dimensions, after Feynman parametrization (`w` the total weight of the two electron lines,
photon weight `1 - w`, shift of the loop momentum, `Δ = w²`), is

  `F₂ / (α/π) = ½ (4π)^{2-d/2} ∫₀¹ dw · w · N_d(w) · Γ(3) I_E(w²; 3, d)`,

with `I_E(Δ; 3, d) = Γ(3 - d/2)/Γ(3) Δ^{d/2-3}` the Euclidean ℓ-integral of the DR side
(`QED.DimReg.tadpole`) and `N_d(w) = 2w(1 - w) + (4 - d) w²` the Pauli numerator: the
`d`-dimensional contractions `γ^ν a̸ γ^μ b̸ γ_ν = -2 b̸ γ^μ a̸ + (4 - d) a̸ γ^μ b̸` and their
analogues add `(4 - d)(a̸ - m) γ^μ (b̸ - m)` to the four-dimensional numerator, whose Pauli part
is `(4 - d) m² w²` after the Gordon identity. As in plan step G3, the `d`-dimensional numerator
is a definition (`pauliNum`), checked at `d = 4` against the model's four-dimensional trace
(`pauliNum_four`). The factor `(4π)^{2-d/2}` converts the Feynman-rule measure
`dᵈℓ/(2π)^d` and the coupling `α/π = e²/(4π²)` to the DR measure `dᵈℓ/π^{d/2}`
(`normalization_eq`).

**Steps.**
1. *Family form and IBP.* For `re d > 3`, `d ≠ 4`, the parametric integral equals
   `½ (4π)^{2-d/2} (4 - d)(5 - d)/2 · I(1, 1)` (`pauliDR_eq_family`), and, by the certified
   reduction `QED.DimReg.OneLoopSchwinger.val_reduction₁₁`,
   `½ (4π)^{2-d/2} (4 - d)(5 - d)(d - 2)/(4(d - 3)) · I(0, 1)` (`pauliDRFamily_eq_tadpole`):
   the projected vertex reduced to the bubble and to the tadpole master.
2. *Continuation to `d = 4`.* The parametric integral converges on all of `re d > 3`,
   including `d = 4`, where the family form has the indeterminate `(4 - d) Γ(2 - d/2)`. So the
   `d → 4` limit of the family (and of the reduced) form is the value at `d = 4` of the
   parametric integral (`tendsto_pauliDRFamily`, `tendsto_pauliDRTadpole`).
3. *The common integrand.* At `d = 4` the DR integrand is `2(1 - w)` (`pauliIntegrandDR_four`),
   which is exactly the pointwise regulator limit of the model's `pauliIntegrand`
   (`tendsto_pauliIntegrand_eq_dr`). Both are the four-dimensional numerator times the same
   scalar kernel: the model integrand is `num · Γ(3)(I_E(D_{m_γ}; 3, 4) - I_E(D_Λ; 3, 4))`
   (`pauliIntegrand_eq_tadpole`), the DR integrand is `num · Γ(3) I_E(w²; 3, 4)`, and
   `i π² I_E(Δ; 3, 4)` is the `ε → 0⁺` limit of the model's own energy-first integral of
   `(ℓ·ℓ + Δ - iε)⁻³` (`QED.DimReg.OneLoopBridge.tendsto_energyFirstIntegral_wickKernel`).
   So no Wick-rotation convention is used: both integrands are obtained from the model's
   Minkowski prescription by theorems (`tendsto_pauliIntegrandDR_four_wick`,
   `tendsto_pauliIntegrand_wick`).

## Main statements

* `QED.DimReg.OneLoopBridge.pauli_dimreg_eq`: the DR limit (family and reduced forms), the
  model's regulator limit and `½ ∫₀¹ pauliIntegrandDR 4` coincide and equal `1/2`, and the
  model integrand tends pointwise to the DR integrand at `d = 4`.
* `QED.DimReg.OneLoopBridge.pauli_dimreg_frozen`: the same against the sealed headline
  `QED.OneLoop.isFormFactorPair_vertexOneLoop_pauli_limit`: every form-factor pair near the
  joint limit has `(4π²/e²) F₂` within `η` of the DR limit.
* `QED.DimReg.OneLoopBridge.pauliDR_eq_family`, `pauliDRFamily_eq_tadpole`: step 1.
* `QED.DimReg.OneLoopBridge.normalization_eq`, `normalizedPauli_eq`: the normalization ledger.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology
open QED.OneLoop.VertexLimit QED.Integration
open QED.DimReg.OneLoopSchwinger (val phi val_reduction₁₁)
open scoped Real

namespace QED.DimReg.OneLoopBridge

/-! ### The DR integrand -/

/-- The `d`-dimensional Pauli numerator of the one-loop vertex at `q = 0`, as a function of the
total electron weight `w` (`m = 1`): `2w(1 - w) + (4 - d) w²`. -/
noncomputable def pauliNum (d : ℂ) (w : ℝ) : ℂ := 2 * w * (1 - w) + (4 - d) * (w : ℂ) ^ 2

/-- The Feynman-parametric integrand of the projected DR vertex: the Jacobian `w`, the Pauli
numerator, and `Γ(3) I_E(w²; 3, d)`, the Euclidean loop integral at `Δ = w²`. -/
noncomputable def pauliIntegrandDR (d : ℂ) (w : ℝ) : ℂ :=
  w * pauliNum d w * (2 * tadpole (w ^ 2) 3 d)

/-- The projected DR one-loop vertex in units of `α/π`, as a Feynman-parametric integral. -/
noncomputable def pauliDR (d : ℂ) : ℂ :=
  1 / 2 * (4 * π : ℂ) ^ (2 - d / 2) * ∫ w in (0 : ℝ)..1, pauliIntegrandDR d w

/-- The projected DR one-loop vertex in units of `α/π`, written with the family value
`I(1, 1)` of `QED.DimReg.OneLoopSchwinger.val`. -/
noncomputable def pauliDRFamily (d : ℂ) : ℂ :=
  1 / 2 * (4 * π : ℂ) ^ (2 - d / 2) * ((4 - d) * (5 - d) / 2) * val ![1, 1] d

/-- The same, IBP-reduced to the tadpole master `I(0, 1)`. -/
noncomputable def pauliDRTadpole (d : ℂ) : ℂ :=
  1 / 2 * (4 * π : ℂ) ^ (2 - d / 2) * ((4 - d) * (5 - d) * (d - 2) / (4 * (d - 3))) *
    val ![0, 1] d

/-- The common value: `½ ∫₀¹` of the DR integrand at `d = 4`. -/
noncomputable def pauliLimit : ℂ := 1 / 2 * ∫ w in (0 : ℝ)..1, pauliIntegrandDR 4 w

/-! ### Closed forms -/

theorem Gamma_three : Gamma (3 : ℂ) = 2 := by
  rw [show (3 : ℂ) = (2 : ℕ) + 1 by norm_num, Gamma_nat_eq_factorial]; norm_num

theorem sq_cpow {w : ℝ} (hw : 0 < w) (d : ℂ) :
    ((w ^ 2 : ℝ) : ℂ) ^ (d / 2 - 3) = (w : ℂ) ^ (d - 6) := by
  have hw' : (w : ℂ) ≠ 0 := ofReal_ne_zero.mpr hw.ne'
  have hw2 : ((w ^ 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  rw [cpow_def_of_ne_zero hw2, cpow_def_of_ne_zero hw', ← ofReal_log (by positivity),
    ← ofReal_log hw.le, Real.log_pow]
  push_cast
  ring_nf

theorem tadpole_sq {w : ℝ} (hw : 0 < w) (d : ℂ) :
    tadpole (w ^ 2) 3 d = Gamma (3 - d / 2) / 2 * (w : ℂ) ^ (d - 6) := by
  rw [tadpole, Gamma_three, sq_cpow hw]

theorem cpow_sub_six_add {w : ℝ} (hw : 0 < w) (d : ℂ) (k : ℕ) :
    (w : ℂ) ^ (d - 6 + k) = (w : ℂ) ^ (d - 6) * (w : ℂ) ^ k := by
  rw [cpow_add _ _ (ofReal_ne_zero.mpr hw.ne'), cpow_natCast]

theorem pauliIntegrandDR_eq {w : ℝ} (hw : 0 < w) (d : ℂ) :
    pauliIntegrandDR d w =
      Gamma (3 - d / 2) * (2 * (w : ℂ) ^ (d - 4) + (2 - d) * (w : ℂ) ^ (d - 3)) := by
  have h4 := cpow_sub_six_add hw d 2
  have h3 := cpow_sub_six_add hw d 3
  push_cast at h4 h3
  rw [show d - 6 + 2 = d - 4 by ring] at h4
  rw [show d - 6 + 3 = d - 3 by ring] at h3
  rw [pauliIntegrandDR, pauliNum, tadpole_sq hw, h4, h3]
  ring

theorem integral_cpow_zero_one {r : ℂ} (hr : -1 < r.re) :
    ∫ w in (0 : ℝ)..1, (w : ℂ) ^ r = 1 / (r + 1) := by
  have hr1 : r + 1 ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  rw [integral_cpow (Or.inl hr)]
  simp [zero_cpow hr1]

/-- **The parametric integral in closed form**: for `re d > 3`,
`∫₀¹ pauliIntegrandDR d = Γ(3 - d/2) (5 - d)/(d - 3)`. -/
theorem integral_pauliIntegrandDR {d : ℂ} (hd : 3 < d.re) :
    ∫ w in (0 : ℝ)..1, pauliIntegrandDR d w = Gamma (3 - d / 2) * ((5 - d) / (d - 3)) := by
  have h4 : -1 < (d - 4).re := by simp; linarith
  have h3 : -1 < (d - 3).re := by simp; linarith
  have e : ∫ w in (0 : ℝ)..1, pauliIntegrandDR d w = ∫ w in (0 : ℝ)..1,
      Gamma (3 - d / 2) * (2 * (w : ℂ) ^ (d - 4) + (2 - d) * (w : ℂ) ^ (d - 3)) := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun w hw => ?_)
    rw [uIoc_of_le zero_le_one] at hw
    exact pauliIntegrandDR_eq hw.1 d
  rw [e, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((intervalIntegral.intervalIntegrable_cpow' h4).const_mul _)
      ((intervalIntegral.intervalIntegrable_cpow' h3).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_cpow_zero_one h4, integral_cpow_zero_one h3]
  have hd3 : d - 3 ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  have hd2 : d - 2 ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  rw [show d - 4 + 1 = d - 3 by ring, show d - 3 + 1 = d - 2 by ring]
  field_simp
  ring

theorem pauliDR_eq_closed {d : ℂ} (hd : 3 < d.re) :
    pauliDR d = 1 / 2 * (4 * π : ℂ) ^ (2 - d / 2) * (Gamma (3 - d / 2) * ((5 - d) / (d - 3))) := by
  rw [pauliDR, integral_pauliIntegrandDR hd]

/-! ### Step 1: the family form and the IBP reduction -/

theorem val_one_one (d : ℂ) :
    val ![1, 1] d = Gamma (2 - d / 2) * Gamma (d - 3) * (Gamma (d - 2))⁻¹ := by
  simp only [val, phi, Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  rw [show (1 : ℂ) + 1 - d / 2 = 2 - d / 2 by ring, show d - 2 * 1 - 1 = d - 3 by ring,
    show d - 1 - 1 = d - 2 by ring, Gamma_one, inv_one, mul_one]
  norm_num

/-- **Step 1a.** For `re d > 3` and `d ≠ 4`, the parametric DR vertex is
`½ (4π)^{2-d/2} (4 - d)(5 - d)/2 · I(1, 1)`. -/
theorem pauliDR_eq_family {d : ℂ} (hd : 3 < d.re) (h4 : d ≠ 4) : pauliDR d = pauliDRFamily d := by
  have hd3 : d - 3 ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  have hg3 : Gamma (d - 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have h2 : 2 - d / 2 ≠ 0 := fun h => h4 (by linear_combination -2 * h)
  have eΓ : Gamma (3 - d / 2) = (2 - d / 2) * Gamma (2 - d / 2) := by
    rw [show 3 - d / 2 = (2 - d / 2) + 1 by ring, Gamma_add_one _ h2]
  have eΓ' : Gamma (d - 2) = (d - 3) * Gamma (d - 3) := by
    rw [show d - 2 = (d - 3) + 1 by ring, Gamma_add_one _ hd3]
  rw [pauliDR_eq_closed hd, pauliDRFamily, val_one_one, eΓ, eΓ']
  field_simp
  ring

/-- **Step 1b (IBP).** For `d ∉ ℤ` the family form reduces to the tadpole master `I(0, 1)`. -/
theorem pauliDRFamily_eq_tadpole {d : ℂ} (hd : ∀ n : ℤ, d ≠ n) :
    pauliDRFamily d = pauliDRTadpole d := by
  have hd3 : d - 3 ≠ 0 := fun h => hd 3 (by push_cast; linear_combination h)
  rw [pauliDRFamily, pauliDRTadpole, val_reduction₁₁ hd]
  field_simp
  ring

/-- The tadpole master is `I(0, 1) = -Γ(1 - d/2)` for `d ∉ ℤ`. -/
theorem val_zero_one {d : ℂ} (hd : ∀ n : ℤ, d ≠ n) : val ![0, 1] d = -Gamma (1 - d / 2) := by
  have hg : Gamma (d - 1) ≠ 0 :=
    Gamma_ne_zero fun m hm => hd (1 - m) (by push_cast; linear_combination hm)
  simp only [val, phi, Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  rw [show (0 : ℂ) + 1 - d / 2 = 1 - d / 2 by ring, show d - 2 * 0 - 1 = d - 1 by ring,
    show d - 0 - 1 = d - 1 by ring, Gamma_one, inv_one, mul_one]
  field_simp

/-! ### Step 2: the limit `d → 4` -/

theorem continuousAt_closed :
    ContinuousAt (fun d : ℂ =>
      1 / 2 * (4 * π : ℂ) ^ (2 - d / 2) * (Gamma (3 - d / 2) * ((5 - d) / (d - 3)))) 4 := by
  have hpi : (4 * π : ℂ) ≠ 0 := by
    rw [show (4 * π : ℂ) = ((4 * π : ℝ) : ℂ) by push_cast; ring]
    exact ofReal_ne_zero.mpr (by positivity)
  have hc : ContinuousAt (fun d : ℂ => (4 * π : ℂ) ^ (2 - d / 2)) 4 :=
    ContinuousAt.const_cpow (by fun_prop) (Or.inl hpi)
  have hg : ContinuousAt (fun d : ℂ => Gamma (3 - d / 2)) 4 := by
    have h1 : (3 : ℂ) - 4 / 2 = 1 := by norm_num
    have hd := (differentiableAt_Gamma (3 - (4 : ℂ) / 2) (by
      rw [h1]; intro m hm
      have := congrArg re hm; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])).continuousAt
    exact hd.comp (f := fun d : ℂ => 3 - d / 2) (by fun_prop)
  have hq : ContinuousAt (fun d : ℂ => (5 - d) / (d - 3)) 4 :=
    ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
  exact (continuousAt_const.mul hc).mul (hg.mul hq)

theorem closed_four :
    1 / 2 * (4 * π : ℂ) ^ (2 - (4 : ℂ) / 2) * (Gamma (3 - (4 : ℂ) / 2) * ((5 - 4) / (4 - 3)))
      = 1 / 2 := by
  rw [show (2 : ℂ) - 4 / 2 = 0 by norm_num, show (3 : ℂ) - 4 / 2 = 1 by norm_num, cpow_zero,
    Gamma_one]
  norm_num

theorem re_gt_three_mem_nhds : {d : ℂ | 3 < d.re} ∈ 𝓝 (4 : ℂ) :=
  (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)

/-- The parametric DR vertex is continuous at `d = 4`, with value `1/2`. -/
theorem tendsto_pauliDR : Tendsto pauliDR (𝓝 4) (𝓝 (1 / 2)) := by
  have h := continuousAt_closed.tendsto
  rw [closed_four] at h
  refine h.congr' ?_
  filter_upwards [re_gt_three_mem_nhds] with d hd
  exact (pauliDR_eq_closed hd).symm

theorem pauliDR_four : pauliDR 4 = 1 / 2 := by
  rw [pauliDR_eq_closed (by norm_num), closed_four]

theorem integral_pauliIntegrandDR_four : ∫ w in (0 : ℝ)..1, pauliIntegrandDR 4 w = 1 := by
  rw [integral_pauliIntegrandDR (by norm_num), show (3 : ℂ) - 4 / 2 = 1 by norm_num, Gamma_one]
  norm_num

theorem pauliLimit_eq : pauliLimit = 1 / 2 := by
  rw [pauliLimit, integral_pauliIntegrandDR_four, mul_one]

theorem not_int_near_four : ∀ᶠ d : ℂ in 𝓝[≠] (4 : ℂ), ∀ n : ℤ, d ≠ (n : ℂ) := by
  have hb : Metric.ball (4 : ℂ) (1 / 2) ∈ 𝓝[≠] (4 : ℂ) :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ (by norm_num))
  filter_upwards [hb, self_mem_nhdsWithin] with d hd hne n hn
  subst hn
  rw [Metric.mem_ball, dist_eq] at hd
  have h1 : |(n : ℝ) - 4| < 1 / 2 := by
    have : ((n : ℂ) - 4) = (((n : ℝ) - 4 : ℝ) : ℂ) := by push_cast; ring
    rw [this, norm_real, Real.norm_eq_abs] at hd
    exact hd
  have h2 : n = 4 := by
    rw [abs_lt] at h1
    have a : (3 : ℝ) < n := by linarith
    have b : (n : ℝ) < 5 := by linarith
    have a' : (3 : ℤ) < n := by exact_mod_cast a
    have b' : n < (5 : ℤ) := by exact_mod_cast b
    omega
  exact hne (by rw [h2]; norm_num)

/-- **Step 2.** The `d → 4` limit of the projected DR vertex in family form is `pauliLimit`. -/
theorem tendsto_pauliDRFamily : Tendsto pauliDRFamily (𝓝[≠] 4) (𝓝 pauliLimit) := by
  rw [pauliLimit_eq]
  refine (tendsto_pauliDR.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [mem_nhdsWithin_of_mem_nhds re_gt_three_mem_nhds, self_mem_nhdsWithin]
    with d hd h4
  exact pauliDR_eq_family hd h4

/-- **Step 2, reduced form.** The same limit for the IBP-reduced form in the tadpole master. -/
theorem tendsto_pauliDRTadpole : Tendsto pauliDRTadpole (𝓝[≠] 4) (𝓝 pauliLimit) := by
  refine tendsto_pauliDRFamily.congr' ?_
  filter_upwards [not_int_near_four] with d hd
  exact pauliDRFamily_eq_tadpole hd

/-! ### Step 3: the common integrand and the model -/

/-- At `d = 4` the DR integrand is `2(1 - w)`. -/
theorem pauliIntegrandDR_four {w : ℝ} (hw : 0 < w) :
    pauliIntegrandDR 4 w = ((2 * (1 - w) : ℝ) : ℂ) := by
  rw [pauliIntegrandDR_eq hw, show (3 : ℂ) - 4 / 2 = 1 by norm_num, Gamma_one,
    show (4 : ℂ) - 4 = 0 by norm_num, show (4 : ℂ) - 3 = 1 by norm_num, cpow_zero, cpow_one]
  push_cast
  ring

/-- **The G3 check at `d = 4`**: the DR Pauli numerator, times the Jacobian and `m²`, is the
numerator of the model's `pauliIntegrand`, obtained from the four-dimensional trace. -/
theorem pauliNum_four (w m : ℝ) :
    (w : ℂ) * pauliNum 4 w * (m : ℂ) ^ 2 = ((2 * w * ((1 - w) - (1 - w) ^ 2) * m ^ 2 : ℝ) : ℂ) := by
  rw [pauliNum]
  push_cast
  ring

/-- The model integrand tends pointwise, as the regulators are removed, to the DR integrand at
`d = 4`. -/
theorem tendsto_pauliIntegrand_eq_dr {m : ℝ} (hm : 0 < m) {z : ℝ × ℝ}
    (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) :
    Tendsto (fun r => (pauliIntegrand m r z : ℂ)) regulatorFilter
      (𝓝 (pauliIntegrandDR 4 z.2)) := by
  rw [pauliIntegrandDR_four hz.2.1]
  exact (continuous_ofReal.tendsto _).comp (tendsto_pauliIntegrand hm hz)

/-- The model's Feynman mass `D_M = (1 - y) M² + y² (m² + x(1 - x) s)`. -/
noncomputable def feynDen (m M s : ℝ) (z : ℝ × ℝ) : ℝ :=
  (1 - z.2) * M ^ 2 + z.2 ^ 2 * (m ^ 2 + z.1 * (1 - z.1) * s)

theorem feynDen_pos {m : ℝ} (hm : 0 < m) (M : ℝ) {s : ℝ} (hs : 0 ≤ s) {z : ℝ × ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) : 0 < feynDen m M s z := by
  obtain ⟨⟨hx0, hx1⟩, hy0, hy1⟩ := hz
  have h1 : 0 ≤ (1 - z.2) * M ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : 0 ≤ z.1 * (1 - z.1) * s := mul_nonneg (mul_nonneg hx0 (by linarith)) hs
  unfold feynDen
  have : 0 < z.2 ^ 2 * (m ^ 2 + z.1 * (1 - z.1) * s) := by positivity
  linarith

/-- **The model integrand through the DR kernel**: `pauliIntegrand` is the four-dimensional
numerator times `Γ(3)(I_E(D_{m_γ}; 3, 4) - I_E(D_Λ; 3, 4))`. -/
theorem pauliIntegrand_eq_tadpole {m : ℝ} (hm : 0 < m) (r : ℝ × ℝ × ℝ) (hs : 0 ≤ r.2.2)
    {z : ℝ × ℝ} (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) :
    (pauliIntegrand m r z : ℂ) = ((2 * z.2 * ((1 - z.2) - (1 - z.2) ^ 2) * m ^ 2 : ℝ) : ℂ) *
      (2 * (tadpole (feynDen m r.1 r.2.2 z) 3 4 - tadpole (feynDen m r.2.1 r.2.2 z) 3 4)) := by
  have h1 := feynDen_pos hm r.1 hs hz
  have h2 := feynDen_pos hm r.2.1 hs hz
  rw [tadpole_three_four h1, tadpole_three_four h2, pauliIntegrand]
  simp only [feynDen] at h1 h2 ⊢
  push_cast
  field_simp

/-- **The DR integrand at `d = 4` from the model's Minkowski prescription.** The energy-first
integral of `(ℓ·ℓ + w² - iε)⁻³`, divided by `i π²` and multiplied by the numerator, tends to
`pauliIntegrandDR 4 w` as `ε → 0⁺`. -/
theorem tendsto_pauliIntegrandDR_four_wick {w : ℝ} (hw : 0 < w) :
    Tendsto (fun ε => w * pauliNum 4 w *
        (2 * (QED.OneLoop.energyFirstIntegral (wickKernel (w ^ 2) ε) / (I * (π : ℂ) ^ 2))))
      (𝓝[>] 0) (𝓝 (pauliIntegrandDR 4 w)) := by
  have hc : I * (π : ℂ) ^ 2 ≠ 0 := mul_ne_zero I_ne_zero (pow_ne_zero _ (ofReal_ne_zero.mpr
    Real.pi_ne_zero))
  have h := ((tendsto_energyFirstIntegral_wickKernel (Δ := w ^ 2) (by positivity)).div_const
    (I * (π : ℂ) ^ 2)).const_mul 2 |>.const_mul ((w : ℂ) * pauliNum 4 w)
  rw [mul_div_cancel_left₀ _ hc] at h
  exact h

/-- **The model integrand from the same Minkowski prescription**: `pauliIntegrand` is the
`ε → 0⁺` limit of the numerator times the Pauli–Villars difference of the energy-first
integrals of `(ℓ·ℓ + D_M - iε)⁻³`, divided by `i π²`. -/
theorem tendsto_pauliIntegrand_wick {m : ℝ} (hm : 0 < m) (r : ℝ × ℝ × ℝ) (hs : 0 ≤ r.2.2)
    {z : ℝ × ℝ} (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) :
    Tendsto (fun ε => ((2 * z.2 * ((1 - z.2) - (1 - z.2) ^ 2) * m ^ 2 : ℝ) : ℂ) *
        (2 * ((QED.OneLoop.energyFirstIntegral (wickKernel (feynDen m r.1 r.2.2 z) ε)
          - QED.OneLoop.energyFirstIntegral (wickKernel (feynDen m r.2.1 r.2.2 z) ε))
            / (I * (π : ℂ) ^ 2))))
      (𝓝[>] 0) (𝓝 (pauliIntegrand m r z : ℂ)) := by
  have hc : I * (π : ℂ) ^ 2 ≠ 0 := mul_ne_zero I_ne_zero (pow_ne_zero _ (ofReal_ne_zero.mpr
    Real.pi_ne_zero))
  have h := (((tendsto_energyFirstIntegral_wickKernel (feynDen_pos hm r.1 hs hz)).sub
    (tendsto_energyFirstIntegral_wickKernel (feynDen_pos hm r.2.1 hs hz))).div_const
    (I * (π : ℂ) ^ 2)).const_mul 2 |>.const_mul
    ((2 * z.2 * ((1 - z.2) - (1 - z.2) ^ 2) * m ^ 2 : ℝ) : ℂ)
  rw [← mul_sub, mul_div_cancel_left₀ _ hc, ← pauliIntegrand_eq_tadpole hm r hs hz] at h
  exact h

/-! ### Normalization ledger -/

/-- The measure conversion behind the factor `(4π)^{2-d/2}`: the Feynman-rule measure
`dᵈℓ/(2π)^d` is `(4π)^{-d/2}` times the DR measure `dᵈℓ/π^{d/2}`, and with the vertex prefactor
`2e²` and `α/π = e²/(4π²)` the projected vertex in units of `α/π` carries
`4π² · 2 · (4π)^{-d/2} = ½ (4π)^{2-d/2}`. -/
theorem normalization_eq (d : ℂ) :
    (π : ℂ) ^ (d / 2) * ((2 * π : ℂ) ^ d)⁻¹ = (4 * π : ℂ) ^ (-(d / 2)) ∧
      4 * (π : ℂ) ^ 2 * 2 * (4 * π : ℂ) ^ (-(d / 2)) = 1 / 2 * (4 * π : ℂ) ^ (2 - d / 2) := by
  have hpi : (0 : ℝ) ≤ π := Real.pi_pos.le
  have hpi' : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have e4 : (4 * π : ℂ) = ((4 : ℝ) : ℂ) * ((π : ℝ) : ℂ) := by push_cast; ring
  have e2 : (2 * π : ℂ) = ((2 : ℝ) : ℂ) * ((π : ℝ) : ℂ) := by push_cast; ring
  have h4 : ((4 : ℝ) : ℂ) ^ (d / 2) = ((2 : ℝ) : ℂ) ^ d := by
    rw [cpow_def_of_ne_zero (by norm_num), cpow_def_of_ne_zero (by norm_num),
      ← ofReal_log (by norm_num), ← ofReal_log (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]
    push_cast
    ring_nf
  have hpd : ((π : ℝ) : ℂ) ^ d = ((π : ℝ) : ℂ) ^ (d / 2) * ((π : ℝ) : ℂ) ^ (d / 2) := by
    rw [← cpow_add _ _ hpi']; ring_nf
  have h2ne : ((2 : ℝ) : ℂ) ^ d ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; simp
  have hpne : ((π : ℝ) : ℂ) ^ (d / 2) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; simp [Real.pi_ne_zero]
  refine ⟨?_, ?_⟩
  · rw [e4, e2, cpow_neg, mul_cpow_ofReal_nonneg (by norm_num) hpi,
      mul_cpow_ofReal_nonneg (by norm_num) hpi, h4, hpd]
    field_simp
  · rw [show (2 : ℂ) - d / 2 = 2 + -(d / 2) by ring, cpow_add _ _ (by rw [e4]; simp [hpi'])]
    rw [show (4 * π : ℂ) ^ (2 : ℂ) = (4 * π : ℂ) ^ (2 : ℕ) by norm_cast]
    ring

/-- **The model's normalized Pauli form factor.** On shell with `q² > 0`, every form-factor
pair of the frozen one-loop vertex has `F₂ / (α/π) = (4π²/e²) F₂ = ½ ∫ dF pauliIntegrand`. -/
theorem normalizedPauli_eq {e m mγ Λ : ℝ} {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (he : e ≠ 0) :
    4 * π ^ 2 / e ^ 2 * formFactorB e m mγ Λ p' p =
      1 / 2 * ∫ z, pauliIntegrand m (mγ, Λ, Minkowski.dot (p' - p) (p' - p)) z
        ∂feynmanMeasure := by
  rw [formFactorB_eq hp' hp]
  field_simp
  ring

/-! ### The pilot theorem -/

/-- **Pilot P1: the one-loop bridge.** The `d → 4` limit of the projected DR one-loop vertex,
in family form `½ (4π)^{2-d/2} (4 - d)(5 - d)/2 · I(1, 1)` and IBP-reduced to the tadpole
master, equals `½ ∫₀¹` of the DR Feynman-parametric integrand at `d = 4`, which is `1/2`; the
regulator limit of the model's normalized Pauli coefficient `½ ∫ dF pauliIntegrand` is the same
number; and the model integrand tends pointwise to the same DR integrand. -/
theorem pauli_dimreg_eq {m : ℝ} (hm : 0 < m) :
    pauliLimit = 1 / 2 ∧
      Tendsto pauliDRFamily (𝓝[≠] 4) (𝓝 pauliLimit) ∧
      Tendsto pauliDRTadpole (𝓝[≠] 4) (𝓝 pauliLimit) ∧
      Tendsto (fun r => ((1 / 2 * ∫ z, pauliIntegrand m r z ∂feynmanMeasure : ℝ) : ℂ))
        regulatorFilter (𝓝 pauliLimit) ∧
      ∀ z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1,
        Tendsto (fun r => (pauliIntegrand m r z : ℂ)) regulatorFilter
          (𝓝 (pauliIntegrandDR 4 z.2)) := by
  refine ⟨pauliLimit_eq, tendsto_pauliDRFamily, tendsto_pauliDRTadpole, ?_,
    fun z hz => tendsto_pauliIntegrand_eq_dr hm hz⟩
  have h := (continuous_ofReal.tendsto _).comp
    ((tendsto_integral_pauliIntegrand hm).const_mul (1 / 2 : ℝ))
  have e : (((1 / 2 : ℝ) * 1 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  rw [pauliLimit_eq, ← e]
  exact h

/-- **Pilot P1 against the sealed headline.** Near the joint limit, every form-factor pair of
the frozen one-loop vertex has normalized Pauli component `(4π²/e²) F₂` within `η` of the DR
limit `pauliLimit` (from `QED.OneLoop.isFormFactorPair_vertexOneLoop_pauli_limit`). -/
theorem pauli_dimreg_frozen {e m : ℝ} (he : e ≠ 0) (hm : 0 < m) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ R : ℝ, ∀ (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ) (p' p : Fin 4 → ℝ)
      (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
      (hp0' : 0 < p' 0) (hp0 : 0 < p 0),
      0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < δ →
      mγ < δ → R < Λ →
      ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair e m p' p
        (QED.OneLoop.vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0) F →
        ‖((4 * π ^ 2 / e ^ 2 : ℝ) : ℂ) * F.2 - pauliLimit‖ < η := by
  have he2 : 0 < e ^ 2 := by positivity
  have hc : 0 < 4 * π ^ 2 / e ^ 2 := by positivity
  obtain ⟨δ, hδ, R, hR⟩ := QED.OneLoop.isFormFactorPair_vertexOneLoop_pauli_limit e m he hm
    (e ^ 2 / (4 * π ^ 2) * η) (by positivity)
  refine ⟨δ, hδ, R, fun mγ Λ hmγ hΛ p' p hp' hp hp0' hp0 hq0 hqδ hmγδ hRΛ F hF => ?_⟩
  have h := (hR mγ Λ hmγ hΛ p' p hp' hp hp0' hp0 hq0 hqδ hmγδ hRΛ).2 F hF
  have e1 : ((4 * π ^ 2 / e ^ 2 : ℝ) : ℂ) * F.2 - pauliLimit
      = ((4 * π ^ 2 / e ^ 2 : ℝ) : ℂ) * (F.2 - ((e ^ 2 / (8 * π ^ 2) : ℝ) : ℂ)) := by
    have he' : (e : ℂ) ≠ 0 := ofReal_ne_zero.mpr he
    have hpi' : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [pauliLimit_eq]
    push_cast
    field_simp
    ring
  rw [e1, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hc]
  calc 4 * π ^ 2 / e ^ 2 * ‖F.2 - ((e ^ 2 / (8 * π ^ 2) : ℝ) : ℂ)‖
      < 4 * π ^ 2 / e ^ 2 * (e ^ 2 / (4 * π ^ 2) * η) := by gcongr
    _ = η := by field_simp

end QED.DimReg.OneLoopBridge

end
