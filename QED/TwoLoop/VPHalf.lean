/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPUnitNested
public import QED.TwoLoop.VPHalfOneLoop
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The bubble half of the VP unit: subtraction at `k² = 0` and the spectral components

The bubble half `QED.TwoLoop.VPUnitNested.VPHalf P` of the nested form of the VP unit asks
`(1/(64 m⁵)) (1/i) (-vpZero P) = e³ outerF2 (Π_loop(s) s D(s)²)`. This file reduces it, at
`m = 1` and admissible regulators, to the **subtracted** bubble, and writes the subtracted right
side as a superposition of spectral components, each of which is the `q → 0` value of a one-loop
vertex with five photon masses (`QED/TwoLoop/VPHalfKernel.lean`,
`QED/TwoLoop/VPHalfOneLoop.lean`).

* **The constant `Π_loop(0)`** (`vpHalf_iff_vpHalfSub`). The photon function `Π_loop(0) s D(s)²`
  is the `δ₃` photon function with `δ₃ = -Π_loop(0)`, so its part of `VPHalf` is accounted for by
  `QED.TwoLoop.VPUnitNested.unit_d3Zero` at `subtractedParams P = {P with δ₃ := -Π_loop(0)}`.
  The rest is the spectral form `Π_loop(s) - Π_loop(0) = (e²/(4π²)) ∑_f c_f ∫₀¹ ρ(v)
  s/(s + 4M_f²/(1-v²)) dv` (`QED.TwoLoop.UnitVPLink.vacuumPolarizationLoop_sub_zero`) inside the
  outer functional, which is `e⁵/(16π⁴) ∑_f c_f vpFlavour M_f m_γ Λ`
  (`QED.TwoLoop.UnitVPLink.vpFlavour_eq_outer`). So `VPHalf P ↔ VPHalfSub P`, with
  `VPHalfSub P : (1/(64 m⁵)) (1/i) (-vpZero P - 2 d3Zero (subtractedParams P)) =
    e⁵/(16π⁴) ∑_f c_f vpFlavour M_f m_γ Λ`.
* **The spectral components** (`vpFlavour_eq_perV`): `vpFlavour M m_γ Λ =
  ∫₀¹ ρ(v) · (Λ² - m_γ²)² (∫ kernVP 1 m_γ Λ μ_v 0)/2 dv`, `μ_v² = 4M²/(1-v²)`. The kernel
  `kernVP m m_γ Λ μ = kern5 m m_γ Λ m_γ Λ μ` is, for distinct masses, the Feynman-parameter
  kernel of the `ε → 0⁺` limit of the one-loop integrand `perVIntegrand`
  (`QED.TwoLoop.VPHalf.tendsto_efi_perVIntegrand`), and the repeated masses are reached by
  continuity of the kernel integral (`QED.TwoLoop.VPHalf.tendsto_integral_kern5`).

## What remains for `VPHalf`

`VPHalfSub P` itself: that the VP class minus the `δ₃` class at `δ₃ = -Π_loop(0)` is, at
`q → 0`, the `ρ`-superposition over the flavours of the spectral components. This is the
exchange of the spectral integral with the `ε → 0⁺` and `q → 0` limits of the nested form (O2-8
at the `ε → 0` level); see `docs/TWO-LOOP-DERIVATION.md`, section 5.4.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.TwoLoop.VPHalf

open QED.WickModel QED.TwoLoop.UnitVPLink QED.TwoLoop.VPUnitNested QED.TwoLoop.VPUnit
open QED.Integration (feynmanMeasure)

/-! ### The outer functional of the loop function, split at `k² = 0` -/

/-- **The outer functional of `Π_loop s D²`, split at `k² = 0`**: at `m = 1` with admissible
regulators, `outerF2 (Π_loop s D²) = outerF2 (Π_loop(0) s D²) +
e²/(16π⁴) ∑_f c_f vpFlavour M_f m_γ Λ`. -/
theorem outerF2_loop_eq (P : Params) (hm : P.m = 1) (hM₁ : 1 < P.M₁) (hM₂ : 1 < P.M₂)
    (hmγ : 0 < P.mγ) (hmΛ : P.mγ < P.Λ) (hm2 : P.mγ < 2) :
    outerF2 (fun s => vacuumPolarizationLoop P s * s * photonD P.mγ P.Λ s ^ 2) =
      outerF2 (fun s => vacuumPolarizationLoop P 0 * s * photonD P.mγ P.Λ s ^ 2) +
        P.e ^ 2 / (16 * π ^ 4) * ∑ f, P.loopCoeff f * vpFlavour (P.mass f) P.mγ P.Λ := by
  have hmass := mass_ne_zero_of hm hM₁ hM₂
  have hΛ : 0 < P.Λ := hmγ.trans hmΛ
  have hsq : P.mγ ^ 2 < 4 := by nlinarith
  have F0 := vpFlavour_eq_outer (M := 1) one_ne_zero hmγ hmΛ (by norm_num; exact hsq)
  have F1 := vpFlavour_eq_outer (M := P.M₁) (by linarith : P.M₁ ≠ 0).symm.symm hmγ hmΛ
    (by nlinarith)
  have F2 := vpFlavour_eq_outer (M := P.M₂) (by linarith : P.M₂ ≠ 0).symm.symm hmγ hmΛ
    (by nlinarith)
  have hpt : ∀ x ∈ uIcc (0 : ℝ) 1,
      x ^ 2 * (vacuumPolarizationLoop P (photonVar x) * photonVar x *
        photonD P.mγ P.Λ (photonVar x) ^ 2) =
      x ^ 2 * (vacuumPolarizationLoop P 0 * photonVar x * photonD P.mγ P.Λ (photonVar x) ^ 2) +
        P.e ^ 2 / (4 * π ^ 2) * (flavOuter 1 P.mγ P.Λ x + P.c₁ * flavOuter P.M₁ P.mγ P.Λ x +
          P.c₂ * flavOuter P.M₂ P.mγ P.Λ x) := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    have hsub := vacuumPolarizationLoop_sub_zero P hmass (photonVar_nonneg hx)
    rw [Fin.sum_univ_three] at hsub
    simp only [Params.loopCoeff, Params.mass, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hm] at hsub
    have hPi : vacuumPolarizationLoop P (photonVar x) = vacuumPolarizationLoop P 0 +
        P.e ^ 2 / (4 * π ^ 2) * (1 * specJ 1 (photonVar x) + P.c₁ * specJ P.M₁ (photonVar x) +
          P.c₂ * specJ P.M₂ (photonVar x)) := by linarith
    simp only [flavOuter]
    rw [hPi]
    ring
  unfold outerF2
  beta_reduce
  rw [intervalIntegral.integral_congr hpt,
    intervalIntegral.integral_add (intervalIntegrable_outer_sD2 hmγ hΛ _)
      (((F0.1.add (F1.1.const_mul _)).add (F2.1.const_mul _)).const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (F0.1.add (F1.1.const_mul _)) (F2.1.const_mul _),
    intervalIntegral.integral_add F0.1 (F1.1.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, ← F0.2, ← F1.2, ← F2.2, Fin.sum_univ_three]
  simp only [Params.loopCoeff, Params.mass, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hm]
  generalize (∫ x in (0 : ℝ)..1,
    x ^ 2 * (vacuumPolarizationLoop P 0 * photonVar x * photonD P.mγ P.Λ (photonVar x) ^ 2)) = I0
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-! ### The subtracted bubble -/

/-- The parameters with `δ₃` replaced by `-Π_loop(0)`: the `δ₃` classes at these parameters carry
the constant part `Π_loop(0) s D(s)²` of the inserted photon function. -/
noncomputable def subtractedParams (P : Params) : Params :=
  { P with δ₃ := -vacuumPolarizationLoop P 0 }

/-- **The subtracted bubble half** (open): the bubble class minus the two `δ₃` classes at
`δ₃ = -Π_loop(0)` is the spectral superposition
`(1/(64 m⁵)) (1/i) (-vpZero P - 2 d3Zero (subtractedParams P)) =
  e⁵/(16π⁴) ∑_f c_f vpFlavour M_f m_γ Λ`. -/
def VPHalfSub (P : Params) : Prop :=
  1 / (64 * (P.m : ℂ) ^ 5) * ((1 / I) * (-QED.TwoLoop.PauliZeroExplicit.vpZero P -
      2 * QED.TwoLoop.PauliZeroExplicit.d3Zero (subtractedParams P))) =
    ((P.e ^ 5 / (16 * π ^ 4) * ∑ f, P.loopCoeff f * vpFlavour (P.mass f) P.mγ P.Λ : ℝ) : ℂ)

/-- **The bubble half is equivalent to the subtracted bubble half**, at `m = 1`, for regulator
masses `M₁, M₂ > 1`, `0 < m_γ < Λ`, `m_γ < 2` and every charge: the constant `Π_loop(0)` of the
inserted loop function is accounted for by the `δ₃` classes (`unit_d3Zero`). -/
theorem vpHalf_iff_vpHalfSub (P : Params) (hm : P.m = 1) (hM₁ : 1 < P.M₁) (hM₂ : 1 < P.M₂)
    (hmγ : 0 < P.mγ) (hmΛ : P.mγ < P.Λ) (hm2 : P.mγ < 2) : VPHalf P ↔ VPHalfSub P := by
  have hΛ : 0 < P.Λ := hmγ.trans hmΛ
  have hd3 := unit_d3Zero (subtractedParams P) hm hmγ hΛ
  have hfun : (fun s => -(subtractedParams P).δ₃ * s *
      photonD (subtractedParams P).mγ (subtractedParams P).Λ s ^ 2) =
      fun s => vacuumPolarizationLoop P 0 * s * photonD P.mγ P.Λ s ^ 2 := by
    funext s
    simp [subtractedParams]
  rw [hfun] at hd3
  change 1 / (64 * (P.m : ℂ) ^ 5) *
      ((1 / I) * (2 * QED.TwoLoop.PauliZeroExplicit.d3Zero (subtractedParams P))) =
    ((P.e ^ 3 * outerF2 (fun s => vacuumPolarizationLoop P 0 * s * photonD P.mγ P.Λ s ^ 2) :
      ℝ) : ℂ) at hd3
  unfold VPHalf VPHalfSub
  rw [outerF2_loop_eq P hm hM₁ hM₂ hmγ hmΛ hm2]
  push_cast at hd3 ⊢
  constructor
  · intro h
    linear_combination h - hd3
  · intro h
    linear_combination h + hd3

/-! ### The spectral components -/

/-- **One flavour as a superposition of spectral components**: for `M ≠ 0`, `0 < m_γ < Λ`,
`m_γ² < 4M²`, `vpFlavour M m_γ Λ = ∫₀¹ ρ(v) · (Λ² - m_γ²)² (∫ kernVP 1 m_γ Λ μ_v 0)/2 dv` with
`μ_v = √(4M²/(1-v²))`. The inner value is the `q² = 0`, `m = 1` kernel integral of the one-loop
vertex with photon factor `(Λ² - m_γ²)² k⁴/((k² + m_γ²)² (k² + Λ²)² (k² + μ_v²))`. -/
theorem vpFlavour_eq_perV {M mγ Λ : ℝ} (hM : M ≠ 0) (hmγ : 0 < mγ) (hmΛ : mγ < Λ)
    (hm2 : mγ ^ 2 < 4 * M ^ 2) :
    vpFlavour M mγ Λ = ∫ v in (0 : ℝ)..1, rho v *
      ((Λ ^ 2 - mγ ^ 2) ^ 2 *
        (∫ z, kernVP 1 mγ Λ (Real.sqrt (4 * M ^ 2 / (1 - v ^ 2))) 0 z ∂feynmanMeasure) / 2) := by
  have hΛ : 0 < Λ := hmγ.trans hmΛ
  have ha : 0 < mγ ^ 2 := pow_pos hmγ 2
  have hab : mγ ^ 2 < Λ ^ 2 := by nlinarith
  have h := vpFlavour_eq hM ha hab hm2
  rw [Real.sqrt_sq hmγ.le, Real.sqrt_sq hΛ.le] at h
  rw [h]
  refine intervalIntegral.integral_congr fun v hv => ?_
  rw [uIcc_of_le zero_le_one] at hv
  have h0 : 0 ≤ 4 * M ^ 2 / (1 - v ^ 2) := by
    have : 0 ≤ 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
    positivity
  rw [integral_kernVP_one_zero_mul, Real.sq_sqrt h0]
  ring

end QED.TwoLoop.VPHalf

end
