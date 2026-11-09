/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.TwoPoint
public import QED.OneLoop.VertexAlgebra
public import QED.Algebra.Contraction
public import QED.Integration.EnergyIntegral
import QED.Algebra.FormFactorIndependence
import QED.WickModel.SelfEnergyEnergyFirst
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The one-loop vacuum polarization: algebra

Algebraic preparation for the energy-first integral of `QED.WickModel.vacuumPolarizationIntegrand`,
the integrand of the loop term of `i Π^{μν}(k)` in the primary source's (62.12), with the
Pauli–Villars flavors of decision D-22.

* The Dirac trace `Tr[(M - a̸) γ^μ (M - b̸) γ^ν] = 4 [a^μ b^ν + a^ν b^μ - (a·b + M²) g^{μν}]`
  (`QED.Dirac.trace_numerator`), from the trace of four slashes.
* The integrand factors as `κ ∑_f c_f N_f(ℓ) / (D_f(ℓ + k) D_f(ℓ))`, with the real numerator
  `N_f = numer M_f k ℓ μ ν` (`vacuumPolarizationIntegrand_eq`).
* The numerator is quadratic in the loop energy, with leading coefficient `alpha μ ν`
  (`numer_cons_eq`).
* The energy integral of a quadratic numerator against the square of a shifted denominator,
  `∫ (γ + β s + α s²) (-s² + w)⁻² dt = (π/2) (-w)^{-3/2} (α (-w) + γ)` with `s = t + a`
  (`integral_quadratic_shifted_two`).

The declarations here are internal helpers of packet 6b, not source-facing definitions.
-/

@[expose] public section

open Matrix Complex MeasureTheory Filter
open scoped Real

namespace QED.Dirac

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- The slash of the `μ`-th row of the metric is `γ^μ`. -/
theorem slash_metric (μ : Fin 4) : slash (fun ν => Minkowski.metric μ ν) = gamma μ := by
  fin_cases μ <;> simp [slash, Minkowski.lower_eq, Minkowski.metric, Fin.sum_univ_four]

/-- The product with the `μ`-th row of the metric is the component `a^μ`. -/
theorem dot_metric_right (a : Fin 4 → ℝ) (μ : Fin 4) :
    Minkowski.dot a (fun ν => Minkowski.metric μ ν) = a μ := by
  fin_cases μ <;> simp [Minkowski.dot_eq, Minkowski.metric]

/-- The product with the `μ`-th row of the metric is the component `a^μ`. -/
theorem dot_metric_left (a : Fin 4 → ℝ) (μ : Fin 4) :
    Minkowski.dot (fun ν => Minkowski.metric μ ν) a = a μ := by
  rw [Minkowski.dot_comm, dot_metric_right]

/-- `tr(a̸ b̸ c̸ d̸) = 4 [(a·b)(c·d) - (a·c)(b·d) + (a·d)(b·c)]`. -/
theorem trace_slash_mul_slash_mul_slash_mul_slash (a b c d : Fin 4 → ℝ) :
    trace (slash a * slash b * slash c * slash d) =
      4 * ((Minkowski.dot a b * Minkowski.dot c d - Minkowski.dot a c * Minkowski.dot b d
        + Minkowski.dot a d * Minkowski.dot b c : ℝ) : ℂ) := by
  have anti : ∀ x y : Fin 4 → ℝ,
      slash x * slash y = ((-2 * Minkowski.dot x y : ℝ) : ℂ) • 𝟙 - slash y * slash x := by
    intro x y
    rw [← slash_anticomm]
    abel
  have e1 : trace (slash a * slash b * slash c * slash d) =
      ((-2 * Minkowski.dot a b : ℝ) : ℂ) * trace (slash c * slash d)
        - trace (slash b * slash a * slash c * slash d) := by
    rw [anti a b, Matrix.sub_mul, Matrix.sub_mul, trace_sub, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.one_mul, trace_smul, smul_eq_mul]
  have e2 : trace (slash b * slash a * slash c * slash d) =
      ((-2 * Minkowski.dot a c : ℝ) : ℂ) * trace (slash b * slash d)
        - trace (slash b * slash c * slash a * slash d) := by
    rw [Matrix.mul_assoc (slash b) (slash a) (slash c), anti a c, Matrix.mul_sub,
      Matrix.sub_mul, trace_sub, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, trace_smul,
      smul_eq_mul, ← Matrix.mul_assoc]
  have e3 : trace (slash b * slash c * slash a * slash d) =
      ((-2 * Minkowski.dot a d : ℝ) : ℂ) * trace (slash b * slash c)
        - trace (slash b * slash c * slash d * slash a) := by
    rw [Matrix.mul_assoc (slash b * slash c) (slash a) (slash d), anti a d, Matrix.mul_sub,
      trace_sub, Matrix.mul_smul, Matrix.mul_one, trace_smul, smul_eq_mul, ← Matrix.mul_assoc]
  have e4 : trace (slash b * slash c * slash d * slash a) =
      trace (slash a * slash b * slash c * slash d) := by
    rw [trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [trace_slash_mul_slash] at e1 e2 e3
  push_cast at e1 e2 e3 ⊢
  linear_combination (e1 - e2 + e3 - e4) / 2

/-- **The Dirac trace of the vacuum polarization loop**:
`Tr[(M - a̸) γ^μ (M - b̸) γ^ν] = 4 [a^μ b^ν + a^ν b^μ - (a·b + M²) g^{μν}]`. -/
theorem trace_numerator (M : ℝ) (a b : Fin 4 → ℝ) (μ ν : Fin 4) :
    trace (((M : ℂ) • 𝟙 - slash a) * gamma μ * ((M : ℂ) • 𝟙 - slash b) * gamma ν) =
      ((4 * (a μ * b ν + a ν * b μ - (Minkowski.dot a b + M ^ 2) * Minkowski.metric μ ν) : ℝ)
        : ℂ) := by
  rw [← slash_metric μ, ← slash_metric ν]
  set c : Fin 4 → ℝ := fun ρ => Minkowski.metric μ ρ with hc
  set d : Fin 4 → ℝ := fun ρ => Minkowski.metric ν ρ with hd
  have hexp : ((M : ℂ) • 𝟙 - slash a) * slash c * ((M : ℂ) • 𝟙 - slash b) * slash d =
      ((M : ℂ) * M) • (slash c * slash d) - (M : ℂ) • (slash c * slash b * slash d)
        - (M : ℂ) • (slash a * slash c * slash d) + slash a * slash c * slash b * slash d := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_assoc]
    module
  rw [hexp, trace_add, trace_sub, trace_sub, trace_smul, trace_smul, trace_smul,
    trace_slash_mul_slash, trace_slash_mul_slash_mul_slash, trace_slash_mul_slash_mul_slash,
    trace_slash_mul_slash_mul_slash_mul_slash]
  simp only [smul_eq_mul]
  have h1 : Minkowski.dot c d = Minkowski.metric μ ν := dot_metric_right c ν
  have h2 : Minkowski.dot a c = a μ := dot_metric_right a μ
  have h3 : Minkowski.dot b d = b ν := dot_metric_right b ν
  have h4 : Minkowski.dot a d = a ν := dot_metric_right a ν
  have h5 : Minkowski.dot c b = b μ := dot_metric_left b μ
  rw [h1, h2, h3, h4, h5]
  push_cast
  ring

end QED.Dirac

namespace QED.WickModel

namespace VacuumPolarizationLimit

open QED.OneLoop

/-! ### The numerator and the factorization of the integrand -/

/-- The overall constant `(-1) (ie)² (1/i)² (2π)⁻⁴` of the (62.12) integrand. -/
noncomputable def kappa (e : ℝ) : ℂ :=
  (-1) * (I * e) ^ 2 * (1 / I) ^ 2 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹

/-- The overall constant is `-e² / (16 π⁴)`. -/
theorem kappa_eq (e : ℝ) : kappa e = ((-(e ^ 2 / (16 * π ^ 4)) : ℝ) : ℂ) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [kappa]
  push_cast
  field_simp
  ring_nf

/-- The numerator of the flavor-`M` loop, `Tr[(M - (ℓ̸ + k̸)) γ^μ (M - ℓ̸) γ^ν]
= 4 [(ℓ + k)^μ ℓ^ν + (ℓ + k)^ν ℓ^μ - ((ℓ + k)·ℓ + M²) g^{μν}]`. It is real. -/
noncomputable def numer (M : ℝ) (k ℓ : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  4 * ((ℓ + k) μ * ℓ ν + (ℓ + k) ν * ℓ μ
    - (Minkowski.dot (ℓ + k) ℓ + M ^ 2) * Minkowski.metric μ ν)

/-- **Factorization of the integrand**:
`κ ∑_f c_f N_f(ℓ) / (D_f(ℓ + k) D_f(ℓ))`. -/
theorem vacuumPolarizationIntegrand_eq (P : Params) (ε : ℝ) (k ℓ : Fin 4 → ℝ) (μ ν : Fin 4) :
    vacuumPolarizationIntegrand P ε k ℓ μ ν = kappa P.e * ∑ f, (P.loopCoeff f : ℂ) *
      ((numer (P.mass f) k ℓ μ ν : ℂ) *
        (denom (P.mass f) ε (ℓ + k) * denom (P.mass f) ε ℓ)⁻¹) := by
  unfold vacuumPolarizationIntegrand kappa
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  congr 1
  simp only [electronPropagator, Matrix.smul_mul, Matrix.mul_smul, trace_smul, smul_eq_mul,
    Dirac.trace_numerator]
  simp only [denom, numer, mul_inv]
  ring

/-- The unit vector of the loop energy. -/
noncomputable def e0 : Fin 4 → ℝ := Fin.cons 1 0

/-- The coefficient of the first power of `s` in `numer M k (ℓ + s • e)`. -/
noncomputable def linCoeff (k ℓ e : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  4 * ((ℓ + k) μ * e ν + e μ * ℓ ν + (ℓ + k) ν * e μ + e ν * ℓ μ
    - (Minkowski.dot (ℓ + k) e + Minkowski.dot e ℓ) * Minkowski.metric μ ν)

/-- The leading coefficient of the numerator in the loop energy,
`4 (2 δ^μ_0 δ^ν_0 + g^{μν})`. -/
noncomputable def alpha (μ ν : Fin 4) : ℝ :=
  4 * (2 * e0 μ * e0 ν + Minkowski.metric μ ν)

/-- The numerator along a line: `N(ℓ + s e) = N(ℓ) + s L + s² (4 (2 e^μ e^ν - (e·e) g^{μν}))`. -/
theorem numer_add_smul (M : ℝ) (k ℓ e : Fin 4 → ℝ) (s : ℝ) (μ ν : Fin 4) :
    numer M k (ℓ + s • e) μ ν = numer M k ℓ μ ν + s * linCoeff k ℓ e μ ν
      + s ^ 2 * (4 * (2 * e μ * e ν - Minkowski.dot e e * Minkowski.metric μ ν)) := by
  simp only [numer, linCoeff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Minkowski.dot_eq]
  ring

/-- `e₀ · e₀ = -1`. -/
theorem dot_e0 : Minkowski.dot e0 e0 = -1 := by
  have h0 : e0 0 = 1 := rfl
  have h1 : e0 1 = 0 := rfl
  have h2 : e0 2 = 0 := rfl
  have h3 : e0 3 = 0 := rfl
  rw [Minkowski.dot_eq, h0, h1, h2, h3]
  norm_num

/-- `(t, v⃗) = (-a, v⃗) + (t + a) e₀`. -/
theorem cons_eq_add_smul (t a : ℝ) (v : Fin 3 → ℝ) :
    (Fin.cons t v : Fin 4 → ℝ) = Fin.cons (-a) v + (t + a) • e0 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [e0]

/-- **The numerator is quadratic in the loop energy**, expanded around `t = -a`. -/
theorem numer_cons_eq (M : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) (t a : ℝ) (v : Fin 3 → ℝ) :
    numer M k (Fin.cons t v) μ ν = numer M k (Fin.cons (-a) v) μ ν
      + (t + a) * linCoeff k (Fin.cons (-a) v) e0 μ ν + (t + a) ^ 2 * alpha μ ν := by
  rw [cons_eq_add_smul t a v, numer_add_smul, dot_e0, alpha]
  ring

/-! ### The energy integral of a quadratic numerator -/

/-- `∫ (t² + z)⁻¹ dt = π z^{-1/2}` on the slit plane. -/
theorem integral_sq_add_zpow_one {z : ℂ} (hz : z ∈ slitPlane) :
    ∫ t : ℝ, ((t : ℂ) ^ 2 + z) ^ (-1 : ℤ) = π * z ^ (-(1 / 2 : ℂ)) := by
  have hK : ∫ s : ℝ, ((1 + s ^ 2) ^ 1)⁻¹ = π := by
    simp only [pow_one]
    exact integral_univ_inv_one_add_sq
  have h := QED.Integration.integral_sq_add_zpow_of_real 1 le_rfl ((π : ℝ) : ℂ)
    (fun a ha => QED.Integration.integral_sq_add_zpow_ofReal 1 ha hK) hz
  have e1 : (-((1 : ℕ) : ℤ)) = (-1 : ℤ) := by norm_num
  have e2 : ((1 / 2 : ℂ) - ((1 : ℕ) : ℂ)) = -(1 / 2 : ℂ) := by norm_num
  rw [e1, e2] at h
  exact h

/-- `z^{-1/2} = z z^{-3/2}` for `z ≠ 0`. -/
theorem cpow_neg_half_eq {z : ℂ} (hz : z ≠ 0) :
    z ^ (-(1 / 2 : ℂ)) = z * z ^ (-(3 / 2 : ℂ)) := by
  rw [show -(1 / 2 : ℂ) = 1 + (-(3 / 2)) by norm_num, Complex.cpow_add _ _ hz, Complex.cpow_one]

/-- The second moment `t² (t² + z)⁻²` is integrable on the slit plane. -/
theorem integrable_sq_mul_sq_add_zpow_two {z : ℂ} (hz : z ∈ slitPlane) :
    Integrable fun t : ℝ => (t : ℂ) ^ 2 * ((t : ℂ) ^ 2 + z) ^ (-2 : ℤ) := by
  obtain ⟨δ, hδ, c, hc, hbd⟩ := QED.Integration.exists_lower_bound_add_of_mem_slitPlane hz
  have hne := QED.Integration.sq_add_ne_zero_of_lower_bound hc (hbd z (Metric.mem_ball_self hδ))
  have i1 : Integrable fun t : ℝ => ((t : ℂ) ^ 2 + z) ^ (-1 : ℤ) := by
    simpa using QED.Integration.integrable_sq_add_zpow hz 1 le_rfl
  have i2 : Integrable fun t : ℝ => ((t : ℂ) ^ 2 + z) ^ (-2 : ℤ) := by
    simpa using QED.Integration.integrable_sq_add_zpow hz 2 (by norm_num)
  refine (i1.sub (i2.const_mul z)).congr (Eventually.of_forall fun t => ?_)
  have h := hne t
  simp only [Pi.sub_apply]
  rw [show (-1 : ℤ) = 1 + (-2) by norm_num, zpow_add₀ h, zpow_one]
  ring

/-- `∫ t² (t² + z)⁻² dt = (π/2) z z^{-3/2}` on the slit plane. -/
theorem integral_sq_mul_sq_add_zpow_two {z : ℂ} (hz : z ∈ slitPlane) :
    ∫ t : ℝ, (t : ℂ) ^ 2 * ((t : ℂ) ^ 2 + z) ^ (-2 : ℤ)
      = (π / 2 : ℂ) * (z * z ^ (-(3 / 2 : ℂ))) := by
  obtain ⟨δ, hδ, c, hc, hbd⟩ := QED.Integration.exists_lower_bound_add_of_mem_slitPlane hz
  have hne := QED.Integration.sq_add_ne_zero_of_lower_bound hc (hbd z (Metric.mem_ball_self hδ))
  have i1 : Integrable fun t : ℝ => ((t : ℂ) ^ 2 + z) ^ (-1 : ℤ) := by
    simpa using QED.Integration.integrable_sq_add_zpow hz 1 le_rfl
  have i2 : Integrable fun t : ℝ => ((t : ℂ) ^ 2 + z) ^ (-2 : ℤ) := by
    simpa using QED.Integration.integrable_sq_add_zpow hz 2 (by norm_num)
  have hpt : ∀ t : ℝ, (t : ℂ) ^ 2 * ((t : ℂ) ^ 2 + z) ^ (-2 : ℤ)
      = ((t : ℂ) ^ 2 + z) ^ (-1 : ℤ) - z * ((t : ℂ) ^ 2 + z) ^ (-2 : ℤ) := by
    intro t
    rw [show (-1 : ℤ) = 1 + (-2) by norm_num, zpow_add₀ (hne t), zpow_one]
    ring
  simp_rw [hpt]
  rw [integral_sub i1 (i2.const_mul z), integral_const_mul, integral_sq_add_zpow_one hz,
    QED.Integration.integral_sq_add_zpow_two hz, cpow_neg_half_eq (slitPlane_ne_zero hz)]
  ring

/-- A quadratic numerator against the square of a shifted denominator is integrable. -/
theorem integrable_quadratic_shifted_two {w : ℂ} (hw : -w ∈ slitPlane) (a : ℝ) (α β γ : ℂ) :
    Integrable fun t : ℝ =>
      (γ + ((t : ℂ) + a) * β + ((t : ℂ) + a) ^ 2 * α) * (-((t : ℂ) + a) ^ 2 + w) ^ (-2 : ℤ) := by
  have i0 : Integrable fun s : ℝ => ((s : ℂ) ^ 2 + -w) ^ (-2 : ℤ) := by
    simpa using QED.Integration.integrable_sq_add_zpow hw 2 (by norm_num)
  have i1 := SelfEnergyLimit.integrable_mul_sq_add_zpow_two hw
  have i2 := integrable_sq_mul_sq_add_zpow_two hw
  refine ((((i0.const_mul γ).add (i1.const_mul β)).add (i2.const_mul α)).comp_add_right a).congr
    (Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply, ofReal_add, SelfEnergyLimit.neg_sq_add_zpow_two]
  ring

/-- **The energy integral of a quadratic numerator against a squared shifted denominator.**
For `-w` in the slit plane,
`∫ (γ + (t + a) β + (t + a)² α) (-(t + a)² + w)⁻² dt = (π/2) (-w)^{-3/2} (α (-w) + γ)`. -/
theorem integral_quadratic_shifted_two {w : ℂ} (hw : -w ∈ slitPlane) (a : ℝ) (α β γ : ℂ) :
    ∫ t : ℝ, (γ + ((t : ℂ) + a) * β + ((t : ℂ) + a) ^ 2 * α) * (-((t : ℂ) + a) ^ 2 + w) ^ (-2 : ℤ)
      = (π / 2 : ℂ) * (-w) ^ (-(3 / 2 : ℂ)) * (α * (-w) + γ) := by
  have i0 : Integrable fun s : ℝ => ((s : ℂ) ^ 2 + -w) ^ (-2 : ℤ) := by
    simpa using QED.Integration.integrable_sq_add_zpow hw 2 (by norm_num)
  have i1 := SelfEnergyLimit.integrable_mul_sq_add_zpow_two hw
  have i2 := integrable_sq_mul_sq_add_zpow_two hw
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℂ,
      G = (fun s : ℝ => γ * ((s : ℂ) ^ 2 + -w) ^ (-2 : ℤ))
        + (fun s : ℝ => β * ((s : ℂ) * ((s : ℂ) ^ 2 + -w) ^ (-2 : ℤ)))
        + (fun s : ℝ => α * ((s : ℂ) ^ 2 * ((s : ℂ) ^ 2 + -w) ^ (-2 : ℤ))) := ⟨_, rfl⟩
  have hpt : ∀ t : ℝ,
      (γ + ((t : ℂ) + a) * β + ((t : ℂ) + a) ^ 2 * α) * (-((t : ℂ) + a) ^ 2 + w) ^ (-2 : ℤ)
        = G (t + a) := fun t => by
    simp only [hG, Pi.add_apply, ofReal_add, SelfEnergyLimit.neg_sq_add_zpow_two]
    ring
  simp_rw [hpt]
  rw [integral_add_right_eq_self G a, hG, integral_add' ((i0.const_mul _).add (i1.const_mul _))
    (i2.const_mul _), integral_add' (i0.const_mul _) (i1.const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul, QED.Integration.integral_sq_add_zpow_two hw,
    SelfEnergyLimit.integral_mul_sq_add_zpow_two, integral_sq_mul_sq_add_zpow_two hw]
  ring

end VacuumPolarizationLimit

end QED.WickModel

end
