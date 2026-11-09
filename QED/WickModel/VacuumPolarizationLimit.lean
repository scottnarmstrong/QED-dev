/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.VacuumPolarizationEnergyFirst
public import QED.WickModel.VacuumPolarizationRadial
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import QED.WickModel.SelfEnergyLimit
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The one-loop vacuum polarization: limit and transverse form

The loop term of the one-loop vacuum polarization is the energy-first integral (prescription
M1, decision D-5) of `QED.WickModel.vacuumPolarizationIntegrand`, the integrand of
`i Π^{μν}(k)` in the primary source's (62.12), with the Pauli–Villars flavors of decision
D-22. This module proves that its limit `ε → 0⁺` exists below the pair threshold `k² > -4m²`
and has the transverse form `i Π_loop(k²) (k² g^{μν} - k^μ k^ν)`, with
`Π_loop(s) = (e² / 2π²) ∫₀¹ x (1 - x) ∑_f c_f log (M_f² + x (1 - x) s) dx`, where
`c_0 = 1`, `M_0 = m` is the electron and `f = 1, 2` are the regulator fermions. The two
Pauli–Villars conditions `∑ c_f = 0` and `∑ c_f M_f² = 0` make the loop finite and transverse.

## Main definitions

* `QED.WickModel.vacuumPolarizationFeynmanMass`: `M² + x (1 - x) s`.
* `QED.WickModel.vacuumPolarizationLoop`: the coefficient `Π_loop(s)`.

## Main statements

* `QED.WickModel.tendsto_energyFirstIntegral_vacuumPolarizationIntegrand`: below threshold,
  the energy-first integral converges as `ε → 0⁺` to `i Π_loop(k²) (k² g^{μν} - k^μ k^ν)`.

## Proof

The limit is `∫ v, spatialG 0 v`
(`QED.WickModel.VacuumPolarizationLimit.tendsto_energyFirstIntegral_spatialG`). At `ε = 0` the
spatial integral is swapped with the Feynman-parameter integral (`integral_spatialG_zero_eq`).
At fixed `x`, translating the spatial momentum by `x k⃗` and symmetrizing under `w⃗ ↦ -w⃗`
(`timeSum_zero_shift_add`) leaves the two Pauli–Villars-summed integrals of
`QED.WickModel.VacuumPolarizationRadial`: the covariance integral, which vanishes, and the
logarithmic integral. The terms in `D_f log D_f` that are not transverse cancel between them
pointwise in `x`, so no integration by parts in `x` is needed.

Transversality holds only in the limit: at fixed `ε > 0` the energy-first integral is not
transverse.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory Set
open QED.OneLoop QED.Integration
open scoped Real

namespace QED.WickModel

/-- The Feynman mass of the vacuum polarization loop of mass `M`, `M² + x (1 - x) s`, with `x`
the Feynman parameter and `s = k²`. -/
noncomputable def vacuumPolarizationFeynmanMass (M s x : ℝ) : ℝ :=
  M ^ 2 + x * (1 - x) * s

/-- The loop coefficient of the one-loop vacuum polarization `Π^{μν}(k) = Π(k²)
(k² g^{μν} - k^μ k^ν)`, with the Pauli–Villars flavors:
`Π_loop(s) = (e² / 2π²) ∫₀¹ x (1 - x) ∑_f c_f log (M_f² + x (1 - x) s) dx`. -/
noncomputable def vacuumPolarizationLoop (P : Params) (s : ℝ) : ℝ :=
  P.e ^ 2 / (2 * π ^ 2) * ∫ x in (0 : ℝ)..1, x * (1 - x) *
    ∑ f, P.loopCoeff f * Real.log (vacuumPolarizationFeynmanMass (P.mass f) s x)

namespace VacuumPolarizationLimit

/-! ### Feynman masses -/

/-- The self-energy Feynman mass with equal masses is the vacuum polarization one. -/
theorem selfEnergyFeynmanMass_eq (M s x : ℝ) :
    selfEnergyFeynmanMass M M s x = vacuumPolarizationFeynmanMass M s x := by
  unfold selfEnergyFeynmanMass vacuumPolarizationFeynmanMass
  ring

/-- The flavor masses are positive. -/
theorem mass_pos {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (f : Fin 3) : 0 < P.mass f := by
  fin_cases f
  · exact hm
  · exact hm.trans hM₁
  · exact hm.trans hM₂

/-- Below the pair threshold the Feynman masses are positive on `[0, 1]`. -/
theorem selfEnergyFeynmanMass_mass_pos {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) {s : ℝ} (hs : -(4 * P.m ^ 2) < s) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (f : Fin 3) : 0 < selfEnergyFeynmanMass (P.mass f) (P.mass f) s x := by
  have hMf := mass_pos hm hM₁ hM₂ f
  have hle := mass_sq_le hm hM₁ hM₂ f
  have h0 : P.mass 0 = P.m := rfl
  refine selfEnergyFeynmanMass_pos hMf hMf ?_ hx
  rw [h0] at hle
  nlinarith

/-- Under the Pauli–Villars conditions, `∑_f c_f D_f = 0`. -/
theorem sum_loopCoeff_mul_feynmanMass {P : Params} (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (s x : ℝ) :
    ∑ f, P.loopCoeff f * selfEnergyFeynmanMass (P.mass f) (P.mass f) s x = 0 := by
  have h1 := sum_loopCoeff hPV₁
  have h2 := sum_loopCoeff_mul_mass_sq hPV₂
  simp only [selfEnergyFeynmanMass_eq, vacuumPolarizationFeynmanMass, mul_add,
    Finset.sum_add_distrib, h2, zero_add]
  have : ∑ f, P.loopCoeff f * (x * (1 - x) * s) = (∑ f, P.loopCoeff f) * (x * (1 - x) * s) :=
    (Finset.sum_mul _ _ _).symm
  rw [this, h1, zero_mul]

/-! ### The closed forms at `ε = 0` -/

/-- The closed-form energy integral is jointly measurable in `(v⃗, x)`. -/
theorem measurable_timeT (M ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    Measurable fun q : (Fin 3 → ℝ) × ℝ => timeT M ε k μ ν q.2 q.1 := by
  have hW : Continuous fun q : (Fin 3 → ℝ) × ℝ => SelfEnergyLimit.massW M M k q.2 q.1 := by
    simp only [SelfEnergyLimit.massW, selfEnergyFeynmanMass, Fin.sum_univ_three]
    fun_prop
  have hX : Measurable fun q : (Fin 3 → ℝ) × ℝ =>
      (-(SelfEnergyLimit.massW M M k q.2 q.1 : ℂ) + ε * I) :=
    (Complex.measurable_ofReal.comp hW.measurable).neg.add_const _
  have hN := continuous_ofReal.comp (continuous_numer_cons M k μ ν
    (f := fun q : (Fin 3 → ℝ) × ℝ => -(q.2 * k 0)) (g := fun q => q.1) (by fun_prop)
    continuous_fst)
  simp only [Function.comp_def] at hN
  unfold timeT
  exact (measurable_const.mul (hX.pow_const _)).mul
    ((measurable_const.mul hX).add hN.measurable)

/-- The Pauli–Villars sum of the closed forms is jointly measurable in `(v⃗, x)`. -/
theorem measurable_timeSum (P : Params) (ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    Measurable fun q : (Fin 3 → ℝ) × ℝ => timeSum P ε k μ ν q.2 q.1 := by
  unfold timeSum
  exact Finset.measurable_sum _ fun f _ => measurable_const.mul (measurable_timeT _ ε k μ ν)

/-- At `ε = 0`, after translating the spatial momentum by `x k⃗`. -/
theorem timeT_zero_shift {M : ℝ} {k : Fin 4 → ℝ} (μ ν : Fin 4) {x : ℝ}
    (hD : 0 < selfEnergyFeynmanMass M M (Minkowski.dot k k) x) (w : Fin 3 → ℝ) :
    timeT M 0 k μ ν x (w - fun i => x * k i.succ) =
      I * (π / 2 : ℂ) * ((((∑ i, w i ^ 2 + selfEnergyFeynmanMass M M (Minkowski.dot k k) x)
          ^ (-(3 / 2 : ℝ)) * (-(alpha μ ν) *
            (∑ i, w i ^ 2 + selfEnergyFeynmanMass M M (Minkowski.dot k k) x)
            + numer M k (Fin.cons 0 w - x • k) μ ν)) : ℝ) : ℂ) := by
  have hS : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hW : 0 < SelfEnergyLimit.massW M M k x (w - fun i => x * k i.succ) := by
    rw [SelfEnergyLimit.massW_sub]
    linarith
  simp only [timeT, ofReal_zero, zero_mul, add_zero]
  rw [VertexLimit.neg_ofReal_cpow_neg_three_halves hW, SelfEnergyLimit.massW_sub,
    SelfEnergyLimit.cons_neg_sub_eq]
  push_cast
  ring

/-- **The symmetrization identity**: the brackets at `±w⃗` add up to twice
`8 (ŵ^μ ŵ^ν - h^{μν} W) + 8 x (1 - x) (k² g^{μν} - k^μ k^ν)`. -/
theorem bracket_shift_add (M x : ℝ) (k : Fin 4 → ℝ) (w : Fin 3 → ℝ) (μ ν : Fin 4) :
    (-(alpha μ ν) * (∑ i, w i ^ 2 + selfEnergyFeynmanMass M M (Minkowski.dot k k) x)
        + numer M k (Fin.cons 0 w - x • k) μ ν)
      + (-(alpha μ ν) * (∑ i, w i ^ 2 + selfEnergyFeynmanMass M M (Minkowski.dot k k) x)
        + numer M k (-(Fin.cons 0 w) - x • k) μ ν)
      = 2 * (8 * ((Fin.cons 0 w : Fin 4 → ℝ) μ * (Fin.cons 0 w : Fin 4 → ℝ) ν
          - hproj μ ν * (∑ i, w i ^ 2 + selfEnergyFeynmanMass M M (Minkowski.dot k k) x))
        + 8 * (x * (1 - x)) * (Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν)) := by
  have c0 : (Fin.cons 0 w : Fin 4 → ℝ) 0 = 0 := rfl
  have c1 : (Fin.cons 0 w : Fin 4 → ℝ) 1 = w 0 := rfl
  have c2 : (Fin.cons 0 w : Fin 4 → ℝ) 2 = w 1 := rfl
  have c3 : (Fin.cons 0 w : Fin 4 → ℝ) 3 = w 2 := rfl
  simp only [numer, alpha, hproj, selfEnergyFeynmanMass, Pi.add_apply, Pi.sub_apply,
    Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Minkowski.dot_eq, Fin.sum_univ_three, c0, c1, c2,
    c3]
  ring

/-- **The symmetrized Pauli–Villars sum at `ε = 0`**, at fixed Feynman parameter. -/
theorem timeSum_zero_shift_add {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) {k : Fin 4 → ℝ} (hk : -(4 * P.m ^ 2) < Minkowski.dot k k) (μ ν : Fin 4)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (w : Fin 3 → ℝ) :
    timeSum P 0 k μ ν x (w - fun i => x * k i.succ)
        + timeSum P 0 k μ ν x (-w - fun i => x * k i.succ)
      = I * π * 8 * ((radialPiece P.loopCoeff
          (fun f => selfEnergyFeynmanMass (P.mass f) (P.mass f) (Minkowski.dot k k) x) μ ν w : ℝ)
            : ℂ)
        + I * π * (8 * (x * (1 - x) * (Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν)))
          * ((radialSum P.loopCoeff
            (fun f => selfEnergyFeynmanMass (P.mass f) (P.mass f) (Minkowski.dot k k) x) w : ℝ)
              : ℂ) := by
  have hneg : (Fin.cons 0 (-w) : Fin 4 → ℝ) = -(Fin.cons 0 w) := by
    funext q
    refine Fin.cases ?_ (fun j => ?_) q <;> simp
  have hsq : ∑ i, (-w) i ^ 2 = ∑ i, w i ^ 2 := by simp
  have hD := fun f => selfEnergyFeynmanMass_mass_pos hm hM₁ hM₂ hk hx f
  simp only [timeSum, radialPiece, radialSum, ofReal_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [timeT_zero_shift μ ν (hD f) w, timeT_zero_shift μ ν (hD f) (-w), hsq, hneg]
  have key := congrArg (fun r : ℝ => (r : ℂ)) (bracket_shift_add (P.mass f) x k w μ ν)
  push_cast at key ⊢
  linear_combination ((P.loopCoeff f : ℂ) * I * (π / 2 : ℂ) *
    (((∑ i, w i ^ 2 + selfEnergyFeynmanMass (P.mass f) (P.mass f) (Minkowski.dot k k) x)
      ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) * key

/-- Below threshold, the Pauli–Villars sum at `ε = 0` is integrable in the spatial momentum. -/
theorem integrable_timeSum_zero {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {k : Fin 4 → ℝ}
    (hk : -(4 * P.m ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Integrable fun v : Fin 3 → ℝ => timeSum P 0 k μ ν x v := by
  obtain ⟨K, -, hK⟩ := norm_timeSum_zero_le hm hM₁ hM₂ hPV₁ hPV₂ hk μ ν
  refine ((integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5)
    (by simp; norm_num)).const_mul K).mono'
    ((measurable_timeSum P 0 k μ ν).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    (Eventually.of_forall fun v => hK x hx v)

/-- The symmetrized integrand is integrable. -/
theorem integrable_timeSum_zero_shift_add {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {k : Fin 4 → ℝ}
    (hk : -(4 * P.m ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Integrable fun w : Fin 3 → ℝ => timeSum P 0 k μ ν x (w - fun i => x * k i.succ)
        + timeSum P 0 k μ ν x (-w - fun i => x * k i.succ) := by
  have hf := integrable_timeSum_zero hm hM₁ hM₂ hPV₁ hPV₂ hk μ ν hx
  exact (hf.comp_sub_right _).add (hf.comp_sub_right _).comp_neg

/-- Below threshold, each component of the covariance integrand is integrable. -/
theorem integrable_radialPiece {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {k : Fin 4 → ℝ}
    (hk : -(4 * P.m ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Integrable (radialPiece P.loopCoeff
      (fun f => selfEnergyFeynmanMass (P.mass f) (P.mass f) (Minkowski.dot k k) x) μ ν) := by
  have hD : ∀ f, 0 < selfEnergyFeynmanMass (P.mass f) (P.mass f) (Minkowski.dot k k) x :=
    fun f => selfEnergyFeynmanMass_mass_pos hm hM₁ hM₂ hk hx f
  have hS : Integrable fun w => ((radialSum P.loopCoeff
      (fun f => selfEnergyFeynmanMass (P.mass f) (P.mass f) (Minkowski.dot k k) x) w : ℝ) : ℂ) :=
    (integrable_radialSum hD (sum_loopCoeff hPV₁)).ofReal
  have hh := integrable_timeSum_zero_shift_add hm hM₁ hM₂ hPV₁ hPV₂ hk μ ν hx
  have hc : (I * π * 8 : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    simp [I_ne_zero, this]
  have hC : Integrable fun w => ((radialPiece P.loopCoeff
      (fun f => selfEnergyFeynmanMass (P.mass f) (P.mass f) (Minkowski.dot k k) x) μ ν w : ℝ)
        : ℂ) := by
    refine ((hh.sub (hS.const_mul (I * π * (8 * (x * (1 - x) *
      (Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν)))))).const_mul
      (I * π * 8)⁻¹).congr (Eventually.of_forall fun w => ?_)
    simp only [Pi.sub_apply]
    rw [timeSum_zero_shift_add hm hM₁ hM₂ hk μ ν hx w]
    field_simp
    ring
  simpa using hC.re

/-! ### The integral at fixed Feynman parameter -/

/-- **The spatial integral at fixed Feynman parameter** at `ε = 0`:
`∫ d³v ∑_f c_f T_f = -8 i π² x (1 - x) (∑_f c_f log D_f) (k² g^{μν} - k^μ k^ν)`. -/
theorem integral_timeSum_zero {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {k : Fin 4 → ℝ}
    (hk : -(4 * P.m ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∫ v, timeSum P 0 k μ ν x v = -(8 * I * π ^ 2) * ((x * (1 - x) *
      (∑ f, P.loopCoeff f * Real.log (vacuumPolarizationFeynmanMass (P.mass f)
        (Minkowski.dot k k) x)) * (Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν) : ℝ)
          : ℂ) := by
  set D : Fin 3 → ℝ := fun f => selfEnergyFeynmanMass (P.mass f) (P.mass f) (Minkowski.dot k k) x
    with hDdef
  have hD : ∀ f, 0 < D f := fun f => selfEnergyFeynmanMass_mass_pos hm hM₁ hM₂ hk hx f
  have hc := sum_loopCoeff hPV₁
  have hcD : ∑ f, P.loopCoeff f * D f = 0 := sum_loopCoeff_mul_feynmanMass hPV₁ hPV₂ _ x
  have hf := integrable_timeSum_zero hm hM₁ hM₂ hPV₁ hPV₂ hk μ ν hx
  have hS := integrable_radialSum hD hc
  have hP := integrable_radialPiece hm hM₁ hM₂ hPV₁ hPV₂ hk μ ν hx
  have hP0 : ∫ w, radialPiece P.loopCoeff D μ ν w = 0 :=
    integral_radialPiece_eq_zero hD hc hcD
      (fun i => integrable_radialPiece hm hM₁ hM₂ hPV₁ hPV₂ hk i.succ i.succ hx) μ ν
  have hS0 := integral_radialSum hD hc
  rw [SelfEnergyLimit.integral_eq_half_integral_of_add_neg hf (fun i => x * k i.succ)
    (timeSum_zero_shift_add hm hM₁ hM₂ hk μ ν hx), integral_add (hP.ofReal.const_mul _)
    (hS.ofReal.const_mul _), integral_const_mul, integral_const_mul, integral_complex_ofReal,
    integral_complex_ofReal, hP0, hS0]
  have hlog : ∀ f, Real.log (D f) = Real.log (vacuumPolarizationFeynmanMass (P.mass f)
      (Minkowski.dot k k) x) := fun f => by
    simp only [hDdef, selfEnergyFeynmanMass_eq]
  simp only [hlog]
  push_cast
  ring

/-! ### Assembly -/

/-- At `ε = 0`, the spatial integral and the Feynman-parameter integral can be swapped. -/
theorem integral_spatialG_zero_eq {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {k : Fin 4 → ℝ}
    (hk : -(4 * P.m ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    ∫ v, spatialG P 0 k μ ν v = ∫ x in Ioc (0 : ℝ) 1, kappa P.e * ∫ v, timeSum P 0 k μ ν x v := by
  obtain ⟨K, hK0, hK⟩ := norm_timeSum_zero_le hm hM₁ hM₂ hPV₁ hPV₂ hk μ ν
  set F : (Fin 3 → ℝ) → ℝ → ℂ := fun v x => kappa P.e * timeSum P 0 k μ ν x v with hF
  have hint : Integrable (Function.uncurry F)
      ((volume : Measure (Fin 3 → ℝ)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    have hg := ((integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5)
      (by simp; norm_num)).const_mul (‖kappa P.e‖ * K)).mul_prod
        (integrable_const (μ := volume.restrict (Ioc (0 : ℝ) 1)) (1 : ℝ))
    refine Integrable.mono' hg ?_ ((SelfEnergyLimit.ae_prod_restrict_Ioc _).mono fun q hq => ?_)
    · exact (measurable_const.mul (measurable_timeSum P 0 k μ ν)).aestronglyMeasurable
    · obtain ⟨v, x⟩ := q
      simp only [Function.uncurry_apply_pair, hF, mul_one] at hq ⊢
      rw [norm_mul]
      calc ‖kappa P.e‖ * ‖timeSum P 0 k μ ν x v‖
          ≤ ‖kappa P.e‖ * (K * (1 + ‖v‖) ^ (-(5 : ℝ))) := by
            gcongr
            exact hK x (Ioc_subset_Icc_self hq) v
        _ = ‖kappa P.e‖ * K * (1 + ‖v‖) ^ (-(5 : ℝ)) := by ring
  have hG : ∀ v, spatialG P 0 k μ ν v = ∫ x in Ioc (0 : ℝ) 1, F v x := fun v => rfl
  simp_rw [hG]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hF]
  rw [integral_const_mul]

/-- **The limit in closed form**: `∫ v, spatialG 0 v = i Π_loop(k²) (k² g^{μν} - k^μ k^ν)`. -/
theorem integral_spatialG_zero {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {k : Fin 4 → ℝ}
    (hk : -(4 * P.m ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    ∫ v, spatialG P 0 k μ ν v = I * (vacuumPolarizationLoop P (Minkowski.dot k k) : ℂ)
      * ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ) := by
  rw [integral_spatialG_zero_eq hm hM₁ hM₂ hPV₁ hPV₂ hk μ ν,
    setIntegral_congr_fun measurableSet_Ioc (fun x hx => by
      rw [integral_timeSum_zero hm hM₁ hM₂ hPV₁ hPV₂ hk μ ν (Ioc_subset_Icc_self hx)]),
    integral_const_mul, integral_const_mul, integral_complex_ofReal, integral_mul_const,
    vacuumPolarizationLoop, intervalIntegral.integral_of_le zero_le_one, kappa_eq]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring

end VacuumPolarizationLimit

/-! ### The main statement -/

/-- **The one-loop vacuum polarization below threshold.** For `m > 0`, regulator fermions
heavier than the electron and the Pauli–Villars conditions `1 + c₁ + c₂ = 0`,
`m² + c₁ M₁² + c₂ M₂² = 0`, and `k² > -4m²`, the energy-first integral of the integrand of
`i Π^{μν}(k)` in (62.12) converges, as `ε → 0⁺`, to
`i Π_loop(k²) (k² g^{μν} - k^μ k^ν)`, with `Π_loop = vacuumPolarizationLoop`. -/
theorem tendsto_energyFirstIntegral_vacuumPolarizationIntegrand {P : Params} (hm : 0 < P.m)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {k : Fin 4 → ℝ}
    (hk : -(4 * P.m ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => energyFirstIntegral fun ℓ => vacuumPolarizationIntegrand P ε k ℓ μ ν)
      (𝓝[>] 0) (𝓝 (I * (vacuumPolarizationLoop P (Minkowski.dot k k) : ℂ)
        * ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ))) := by
  rw [← VacuumPolarizationLimit.integral_spatialG_zero hm hM₁ hM₂ hPV₁ hPV₂ hk μ ν]
  exact VacuumPolarizationLimit.tendsto_energyFirstIntegral_spatialG hm hM₁ hM₂ hPV₁ hPV₂ hk μ ν

end QED.WickModel

end
