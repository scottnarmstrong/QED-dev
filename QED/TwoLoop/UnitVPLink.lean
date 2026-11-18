/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitsRegulated
public import QED.TwoLoop.VacuumPolarizationUnitLimit
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The VP unit: the explicit value is the outer one-loop `F₂` of the model's renormalized `Π`

Part of obligation O2-18 at model level (`docs/TWO-LOOP-DERIVATION.md`, section 5.3). The explicit
finite-regulator VP value `vpUnitReg m_γ Λ M₁ M₂` of `QED/TwoLoop/VacuumPolarizationUnitLimit.lean`
(electron mass `m = 1`) is identified with the one-loop Pauli functional applied to the photon
function `Π(k²) k² D(k²)²`, where `Π = -δ₃ + Π_loop` is the vacuum polarization of the model
(`QED.WickModel.vacuumPolarizationLoop`, flavour-summed with the Pauli–Villars coefficients of
`P`) and `δ₃` is fixed by the photon on-shell condition (Z₈).

## Objects

* `photonVar x = x²/(1-x)`: the Euclidean photon `k²/m²` as a function of the Feynman parameter of
  the one-loop vertex (`m = 1`).
* `photonD m_γ Λ s = 1/(s + m_γ²) - 1/(s + Λ²)`: the Pauli–Villars photon function.
* `outerF2 R = (1/(4π²)) ∫₀¹ x² R(x²/(1-x)) dx`: the one-loop `F₂(0)` at unit charge for the
  photon function `R`. For `R = photonD` it is the model's one-loop Pauli coefficient
  (`outerF2_photonD_eq_oneLoopPauliZero`), and it carries the normalization of the units: the `δ₁`
  class value gives `unitF2`-normalized `δ₁ e³ outerF2 (photonD m_γ Λ)` (`unit_d1Zero`).
* `vpOuterF2 P = outerF2 (s ↦ (Π_loop(s) - δ₃) s D(s)²)`.

## Main statements

* `vacuumPolarizationLoop_sub_zero`: the spectral form of the model's subtracted loop function,
  `Π_loop(s) - Π_loop(0) = (e²/(4π²)) ∑_f c_f ∫₀¹ ρ(v) s/(s + 4M_f²/(1-v²)) dv` for `s ≥ 0`.
* `vpFlavour_eq_outer`: one flavour of `vpUnitReg` is the outer functional of the one-flavour
  spectral insertion (Fubini on `[0,1]²`).
* `vpUnitReg_eq_vpOuterF2`: **with (Z₈) at `m = 1`, `16π⁴ vpOuterF2 P = e² vpUnitReg m_γ Λ M₁ M₂`.**
* `unitF2_VP_eq_vpUnitReg`, `unitF2_VP_iterated_limit`: the model's VP unit
  `unitF2 .VP (atUnitCharge P d₁ d₂ d_m d₃)` equals `vpUnitReg / (16π⁴)` and has the D-37.4
  iterated limit `119/36 - π²/3`, **given** the nested-form identity `VPUnitNested` at that point.

## What is not proved here

`VPUnitNested P : unitF2 .VP P = vpOuterF2 P`, the statement that the explicit parametric values
`-vpZero P + 2 d3Zero P` (nine resp. eight Feynman parameters,
`QED/TwoLoop/PauliZeroExplicit*.lean`) equal the outer one-loop functional of the inserted
photon function. It is the nested structure of the VP class at `q → 0` (obligations O2-8, O2-10,
O2-13), and it is a hypothesis of the last two theorems. The normalization `16π⁴` and the sign are
those of the units (`unit_d1Zero`); the identity itself is checked numerically only on its proved
side (`vpUnitReg` against the double integral of `Π_loop`), not on `vpZero`, `d3Zero`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.TwoLoop.UnitVPLink

open QED.WickModel QED.TwoLoop.VPUnit QED.TwoLoop.UnitsRegulated

/-! ### The one-loop Pauli functional -/

/-- The photon variable `k²/m² = x²/(1-x)` of the one-loop vertex at `q = 0` (`m = 1`). -/
noncomputable def photonVar (x : ℝ) : ℝ := x ^ 2 / (1 - x)

/-- The Pauli–Villars photon function `1/(s + m_γ²) - 1/(s + Λ²)`. -/
noncomputable def photonD (mγ Λ s : ℝ) : ℝ := 1 / (s + mγ ^ 2) - 1 / (s + Λ ^ 2)

/-- **The one-loop `F₂(0)` at unit charge for a photon function `R`**:
`(1/(4π²)) ∫₀¹ x² R(x²/(1-x)) dx`. -/
noncomputable def outerF2 (R : ℝ → ℝ) : ℝ :=
  1 / (4 * π ^ 2) * ∫ x in (0 : ℝ)..1, x ^ 2 * R (photonVar x)

/-- **The outer functional of the VP-inserted photon function**:
`outerF2 (s ↦ (Π_loop(s) - δ₃) s D(s)²)`, with `Π_loop` the model's flavour-summed loop function
(charge `P.e`) and `δ₃ = P.δ₃`. -/
noncomputable def vpOuterF2 (P : Params) : ℝ :=
  outerF2 fun s => (vacuumPolarizationLoop P s - P.δ₃) * s * photonD P.mγ P.Λ s ^ 2

theorem photonVar_nonneg {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ photonVar x :=
  div_nonneg (sq_nonneg x) (by linarith [hx.2])

theorem den_eq {x c : ℝ} (hx : x ≠ 1) : x ^ 2 + (1 - x) * c = (1 - x) * (photonVar x + c) := by
  have h : 1 - x ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  unfold photonVar
  field_simp

theorem sq_div_den {x c : ℝ} (hx : x ≠ 1) :
    x ^ 2 / (x ^ 2 + (1 - x) * c) = photonVar x / (photonVar x + c) := by
  have h : 1 - x ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have hx2 : x ^ 2 = (1 - x) * photonVar x := by
    unfold photonVar
    field_simp
  rw [den_eq hx, hx2, mul_div_mul_left _ _ h]

theorem f2Kernel_eq {c x : ℝ} (hx : x ≠ 1) : f2Kernel c x = x ^ 2 * (1 / (photonVar x + c)) := by
  have h : 1 - x ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  unfold f2Kernel
  rw [den_eq hx]
  rcases eq_or_ne (photonVar x + c) 0 with hs | hs
  · simp [hs]
  · field_simp

/-- **The kernel of `vpInsert` as the outer integrand of the inserted photon function**:
for `x ≠ 1`, `regKernel c a b x = x² s (1/(s+a) - 1/(s+b))² · s/(s+c)`, `s = x²/(1-x)`. -/
theorem regKernel_eq_photon {c a b x : ℝ} (hx : x ≠ 1) :
    regKernel c a b x =
      x ^ 2 * (photonVar x * (1 / (photonVar x + a) - 1 / (photonVar x + b)) ^ 2) *
        (photonVar x / (photonVar x + c)) := by
  unfold regKernel
  rw [f2Kernel_eq hx, sq_div_den hx, sq_div_den hx]
  ring

theorem ae_ne_one : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
  simp [ae_iff, measure_singleton]

/-- `outerF2` of the Pauli–Villars photon is the difference of the massive-photon `f2`. -/
theorem outerF2_photonD {mγ Λ : ℝ} (hmγ : 0 < mγ) (hΛ : 0 < Λ) :
    outerF2 (photonD mγ Λ) = (f2 (mγ ^ 2) - f2 (Λ ^ 2)) / (4 * π ^ 2) := by
  unfold outerF2 f2
  rw [← intervalIntegral.integral_sub (intervalIntegrable_f2Kernel (pow_pos hmγ 2))
    (intervalIntegrable_f2Kernel (pow_pos hΛ 2))]
  have h : ∫ x in (0 : ℝ)..1, x ^ 2 * photonD mγ Λ (photonVar x) =
      ∫ x in (0 : ℝ)..1, f2Kernel (mγ ^ 2) x - f2Kernel (Λ ^ 2) x := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne_one] with x hx _
    rw [f2Kernel_eq hx, f2Kernel_eq hx, photonD]
    ring
  rw [h]
  ring

/-! ### The normalization: the model's one-loop Pauli coefficient and the `δ₁` class -/

/-- At `m = 1`, `q² = 0` the one-loop Pauli integrand is `2(f2Kernel m_γ² - f2Kernel Λ²)` in the
second Feynman variable. -/
theorem pauliIntegrand_one_zero (mγ Λ : ℝ) (z : ℝ × ℝ) :
    QED.OneLoop.VertexLimit.pauliIntegrand 1 (mγ, Λ, 0) z =
      2 * (f2Kernel (mγ ^ 2) z.2 - f2Kernel (Λ ^ 2) z.2) := by
  unfold QED.OneLoop.VertexLimit.pauliIntegrand f2Kernel
  simp only [one_pow, mul_zero, add_zero, mul_one]
  ring

/-- **The model's one-loop Pauli coefficient at `m = 1`, `q² = 0`**:
`∫ pauliIntegrand 1 (m_γ, Λ, 0) = 2 (f2(m_γ²) - f2(Λ²))`. -/
theorem integral_pauliIntegrand_one_zero {mγ Λ : ℝ} (hmγ : 0 < mγ) (hΛ : 0 < Λ) :
    ∫ z, QED.OneLoop.VertexLimit.pauliIntegrand 1 (mγ, Λ, 0) z ∂QED.Integration.feynmanMeasure =
      2 * (f2 (mγ ^ 2) - f2 (Λ ^ 2)) := by
  simp_rw [pauliIntegrand_one_zero]
  unfold QED.Integration.feynmanMeasure
  rw [integral_fun_snd (f := fun y => 2 * (f2Kernel (mγ ^ 2) y - f2Kernel (Λ ^ 2) y))]
  have h1 : (volume.restrict (Ioc (0 : ℝ) 1)).real univ = 1 := by
    simp [Measure.real]
  rw [h1, one_smul, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (intervalIntegrable_f2Kernel (pow_pos hmγ 2))
      (intervalIntegrable_f2Kernel (pow_pos hΛ 2))]
  rfl

/-- `outerF2 (photonD m_γ Λ)` is the model's one-loop Pauli coefficient over `8π²` (at `m = 1`). -/
theorem outerF2_photonD_eq_oneLoopPauliZero (P : Params) (hm : P.m = 1) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) :
    outerF2 (photonD P.mγ P.Λ) =
      QED.TwoLoop.PauliZeroExplicit.oneLoopPauliZero P / (8 * π ^ 2) := by
  rw [outerF2_photonD hmγ hΛ]
  unfold QED.TwoLoop.PauliZeroExplicit.oneLoopPauliZero
  rw [hm, integral_pauliIntegrand_one_zero hmγ hΛ]
  ring

/-- **The normalization of the units**: the `unitF2`-normalized value of a `δ₁` class is
`δ₁ e³ outerF2 (photonD m_γ Λ)` (at `m = 1`). So `outerF2` is the one-loop `F₂(0)` functional in
the normalization of `QED.TwoLoop.UnitsRegulated.unitF2`. -/
theorem unit_d1Zero (P : Params) (hm : P.m = 1) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    1 / (64 * (P.m : ℂ) ^ 5) * ((1 / Complex.I) * QED.TwoLoop.PauliZeroExplicit.d1Zero P) =
      ((P.δ₁ * P.e ^ 3 * outerF2 (photonD P.mγ P.Λ) : ℝ) : ℂ) := by
  rw [outerF2_photonD_eq_oneLoopPauliZero P hm hmγ hΛ]
  unfold QED.TwoLoop.PauliZeroExplicit.d1Zero
  rw [hm]
  push_cast
  field_simp
  ring

/-! ### The spectral form of the model's subtracted loop function -/

/-- The one-flavour spectral integral `∫₀¹ ρ(v) s/(s + 4M²/(1-v²)) dv`. -/
noncomputable def specJ (M s : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1, rho v * (s / (s + 4 * M ^ 2 / (1 - v ^ 2)))

theorem feynmanMass_pos {M s x : ℝ} (hM : M ≠ 0) (hs : 0 ≤ s) (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < vacuumPolarizationFeynmanMass M s x := by
  unfold vacuumPolarizationFeynmanMass
  have : 0 ≤ x * (1 - x) * s := mul_nonneg (mul_nonneg hx.1 (by linarith [hx.2])) hs
  have : 0 < M ^ 2 := by positivity
  linarith

theorem intervalIntegrable_loop (P : Params) (hmass : ∀ f, P.mass f ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    IntervalIntegrable (fun x => x * (1 - x) *
      ∑ f, P.loopCoeff f * Real.log (vacuumPolarizationFeynmanMass (P.mass f) s x)) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one ?_
  refine (by fun_prop : Continuous fun x : ℝ => x * (1 - x)).continuousOn.mul ?_
  refine continuousOn_finsetSum _ fun f _ => continuousOn_const.mul ?_
  refine ContinuousOn.log ?_ fun x hx => (feynmanMass_pos (hmass f) hs hx).ne'
  unfold vacuumPolarizationFeynmanMass
  fun_prop

theorem intervalIntegrable_log_ratio {M s : ℝ} (hM : M ≠ 0) (hs : 0 ≤ s) :
    IntervalIntegrable (fun x => x * (1 - x) * Real.log ((M ^ 2 + x * (1 - x) * s) / M ^ 2))
      volume 0 1 := by
  refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one ?_
  refine (by fun_prop : Continuous fun x : ℝ => x * (1 - x)).continuousOn.mul ?_
  refine ContinuousOn.log (by fun_prop) fun x hx => ?_
  have := feynmanMass_pos hM hs hx
  unfold vacuumPolarizationFeynmanMass at this
  exact (div_pos this (by positivity)).ne'

/-- **The spectral form of the model's subtracted loop function (O2-18)**: for flavour masses
`M_f ≠ 0` and `s ≥ 0`,
`Π_loop(s) - Π_loop(0) = (e²/(4π²)) ∑_f c_f ∫₀¹ ρ(v) s/(s + 4M_f²/(1-v²)) dv`. -/
theorem vacuumPolarizationLoop_sub_zero (P : Params) (hmass : ∀ f, P.mass f ≠ 0) {s : ℝ}
    (hs : 0 ≤ s) :
    vacuumPolarizationLoop P s - vacuumPolarizationLoop P 0 =
      P.e ^ 2 / (4 * π ^ 2) * ∑ f, P.loopCoeff f * specJ (P.mass f) s := by
  unfold vacuumPolarizationLoop
  rw [← mul_sub, ← intervalIntegral.integral_sub (intervalIntegrable_loop P hmass hs)
    (intervalIntegrable_loop P hmass le_rfl)]
  have hpt : ∀ x ∈ uIcc (0 : ℝ) 1,
      x * (1 - x) * ∑ f, P.loopCoeff f * Real.log (vacuumPolarizationFeynmanMass (P.mass f) s x) -
        x * (1 - x) * ∑ f, P.loopCoeff f *
          Real.log (vacuumPolarizationFeynmanMass (P.mass f) 0 x) =
      ∑ f, P.loopCoeff f *
        (x * (1 - x) * Real.log ((P.mass f ^ 2 + x * (1 - x) * s) / P.mass f ^ 2)) := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    have h1 := feynmanMass_pos (hmass f) hs hx
    have h2 : (0 : ℝ) < P.mass f ^ 2 := by have := hmass f; positivity
    unfold vacuumPolarizationFeynmanMass at h1 ⊢
    rw [Real.log_div h1.ne' h2.ne', mul_zero, add_zero]
    ring
  rw [intervalIntegral.integral_congr hpt,
    intervalIntegral.integral_finsetSum fun f _ =>
      (intervalIntegrable_log_ratio (hmass f) hs).const_mul _]
  have hspec : ∀ f, ∫ x in (0 : ℝ)..1, P.loopCoeff f *
      (x * (1 - x) * Real.log ((P.mass f ^ 2 + x * (1 - x) * s) / P.mass f ^ 2)) =
      P.loopCoeff f * (1 / 2 * specJ (P.mass f) s) := fun f => by
    have hK : -(4 * P.mass f ^ 2) < s := by
      have := hmass f
      have : 0 < P.mass f ^ 2 := by positivity
      linarith
    rw [intervalIntegral.integral_const_mul, integral_mul_log_eq_spectral (hmass f) hK]
    rfl
  simp only [hspec]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

/-! ### One flavour: Fubini on `[0, 1]²` -/

/-- The integrand of `vpFlavour` before the `x`-integration. -/
noncomputable def flavKernel (M a b : ℝ) (q : ℝ × ℝ) : ℝ :=
  rho q.1 * regKernel (4 * M ^ 2 / (1 - q.1 ^ 2)) a b q.2

theorem measurable_flavKernel (M a b : ℝ) : Measurable (flavKernel M a b) := by
  have hr : Measurable rho := by unfold rho; fun_prop
  have hk := (measurable_regKernel a b).comp
    ((by fun_prop : Measurable fun v : ℝ => 4 * M ^ 2 / (1 - v ^ 2)).prodMap measurable_id)
  exact (hr.comp measurable_fst).mul hk

theorem flavKernel_bound {M a b : ℝ} (hM : M ≠ 0) (ha : 0 ≤ a) (hab : a ≤ b) {q : ℝ × ℝ}
    (hq : q ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) : ‖flavKernel M a b q‖ ≤ 1 / (4 * M ^ 2) := by
  obtain ⟨⟨hv0, hv1⟩, ⟨hx0, hx1⟩⟩ := hq
  have hx : q.2 ∈ Icc (0 : ℝ) 1 := ⟨hx0.le, hx1⟩
  have hM2 : 0 < M ^ 2 := by positivity
  rcases hv1.lt_or_eq with hv1 | hv1
  · have hs : 0 < 1 - q.1 ^ 2 := by nlinarith
    have hc : 0 < 4 * M ^ 2 / (1 - q.1 ^ 2) := by positivity
    have hr : 0 ≤ rho q.1 := div_nonneg (mul_nonneg (sq_nonneg _) (by nlinarith)) hs.le
    have k0 := regKernel_nonneg (a := a) (b := b) hc hx
    have k1 := (regKernel_le hc ha hab hx).trans (f2Kernel_le hc hx)
    have k2 : q.2 ^ 2 / (4 * M ^ 2 / (1 - q.1 ^ 2)) ≤ 1 / (4 * M ^ 2 / (1 - q.1 ^ 2)) :=
      div_le_div_of_nonneg_right (by nlinarith) hc.le
    unfold flavKernel
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr k0)]
    calc rho q.1 * regKernel (4 * M ^ 2 / (1 - q.1 ^ 2)) a b q.2
        ≤ rho q.1 * (1 / (4 * M ^ 2 / (1 - q.1 ^ 2))) :=
          mul_le_mul_of_nonneg_left (k1.trans k2) hr
      _ = q.1 ^ 2 * (1 - q.1 ^ 2 / 3) / (4 * M ^ 2) := by
          unfold rho
          field_simp
      _ ≤ 1 / (4 * M ^ 2) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith
  · have : rho q.1 = 0 := by simp [rho, hv1]
    simp only [flavKernel, this, zero_mul, norm_zero]
    positivity

theorem integrable_flavKernel {M a b : ℝ} (hM : M ≠ 0) (ha : 0 ≤ a) (hab : a ≤ b) :
    Integrable (flavKernel M a b) QED.Integration.feynmanMeasure := by
  refine Integrable.mono' (integrable_const (1 / (4 * M ^ 2)))
    (measurable_flavKernel M a b).aestronglyMeasurable ?_
  unfold QED.Integration.feynmanMeasure
  rw [Measure.prod_restrict]
  exact (ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioc)).2
    (Eventually.of_forall fun q hq => flavKernel_bound hM ha hab hq)

/-- The outer integrand of one flavour: `x² s D(s)² J(M, s)`, `s = x²/(1-x)`. -/
noncomputable def flavOuter (M mγ Λ x : ℝ) : ℝ :=
  x ^ 2 * (photonVar x * photonD mγ Λ (photonVar x) ^ 2 * specJ M (photonVar x))

theorem integral_flavKernel_v {M mγ Λ x : ℝ} (hx : x ≠ 1) :
    ∫ v in Ioc (0 : ℝ) 1, flavKernel M (mγ ^ 2) (Λ ^ 2) (v, x) = flavOuter M mγ Λ x := by
  simp only [flavKernel, regKernel_eq_photon hx]
  have e : ∀ v, rho v * (x ^ 2 * (photonVar x * (1 / (photonVar x + mγ ^ 2) -
      1 / (photonVar x + Λ ^ 2)) ^ 2) * (photonVar x / (photonVar x + 4 * M ^ 2 / (1 - v ^ 2)))) =
      x ^ 2 * (photonVar x * photonD mγ Λ (photonVar x) ^ 2) *
        (rho v * (photonVar x / (photonVar x + 4 * M ^ 2 / (1 - v ^ 2)))) := fun v => by
    unfold photonD
    ring
  simp only [e]
  rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one]
  unfold flavOuter specJ
  ring

/-- **One flavour as the outer functional of its spectral insertion**: for `M ≠ 0`,
`0 < m_γ < Λ`, `m_γ² < 4M²`, `vpFlavour M m_γ Λ = ∫₀¹ x² s D(s)² J(M, s) dx` with
`s = x²/(1-x)`, and the outer integrand is integrable. -/
theorem vpFlavour_eq_outer {M mγ Λ : ℝ} (hM : M ≠ 0) (hmγ : 0 < mγ) (hmΛ : mγ < Λ)
    (hm2 : mγ ^ 2 < 4 * M ^ 2) :
    IntervalIntegrable (flavOuter M mγ Λ) volume 0 1 ∧
      vpFlavour M mγ Λ = ∫ x in (0 : ℝ)..1, flavOuter M mγ Λ x := by
  have hΛ : 0 < Λ := hmγ.trans hmΛ
  have ha : 0 < mγ ^ 2 := pow_pos hmγ 2
  have hab : mγ ^ 2 < Λ ^ 2 := by nlinarith
  have hI := integrable_flavKernel (M := M) hM ha.le hab.le
  have hae : (fun x => ∫ v, flavKernel M (mγ ^ 2) (Λ ^ 2) (v, x)
      ∂(volume.restrict (Ioc (0 : ℝ) 1))) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      flavOuter M mγ Λ := by
    filter_upwards [ae_restrict_of_ae ae_ne_one] with x hx
    exact integral_flavKernel_v hx
  refine ⟨?_, ?_⟩
  · have h := hI.integral_prod_right
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 (h.congr hae)
  · have h := vpFlavour_eq hM ha hab hm2
    rw [sqrt_sq hmγ.le, sqrt_sq hΛ.le] at h
    rw [h, intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
      ← integral_congr_ae hae]
    have hswap := integral_integral_swap (μ := volume.restrict (Ioc (0 : ℝ) 1))
      (ν := volume.restrict (Ioc (0 : ℝ) 1))
      (f := fun v x => flavKernel M (mγ ^ 2) (Λ ^ 2) (v, x)) hI
    rw [← hswap]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [flavKernel]
    rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one]

/-! ### The main identity -/

theorem mass_ne_zero_of {P : Params} (hm : P.m = 1) (hM₁ : 1 < P.M₁) (hM₂ : 1 < P.M₂) :
    ∀ f, P.mass f ≠ 0 := by
  intro f
  fin_cases f
  · simp [Params.mass, hm]
  · simp only [Params.mass]
    exact (by linarith : (0 : ℝ) < P.M₁).ne'
  · simp only [Params.mass]
    exact (by linarith : (0 : ℝ) < P.M₂).ne'

/-- **The explicit VP value is the outer functional of the model's renormalized `Π`.** At `m = 1`,
with regulator masses `M₁, M₂ > 1` satisfying the Pauli–Villars conditions, `0 < m_γ < Λ`,
`m_γ < 2`, and `δ₃ = Π_loop(0)` (the photon on-shell condition (Z₈), `isPhotonOnShell_iff`):
`16π⁴ vpOuterF2 P = e² vpUnitReg m_γ Λ M₁ M₂`. -/
theorem vpUnitReg_eq_vpOuterF2 (P : Params) (hm : P.m = 1) (hM₁ : 1 < P.M₁) (hM₂ : 1 < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hmγ : 0 < P.mγ) (hmΛ : P.mγ < P.Λ) (hm2 : P.mγ < 2)
    (hδ₃ : P.δ₃ = vacuumPolarizationLoop P 0) :
    16 * π ^ 4 * vpOuterF2 P = P.e ^ 2 * vpUnitReg P.mγ P.Λ P.M₁ P.M₂ := by
  have hmass := mass_ne_zero_of hm hM₁ hM₂
  -- the Pauli–Villars coefficients
  have hPV₂' : 1 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0 := by rw [hm] at hPV₂; simpa using hPV₂
  have hne : P.M₁ ^ 2 ≠ P.M₂ ^ 2 := by
    intro h
    rw [h] at hPV₂'
    have : P.c₁ + P.c₂ = -1 := by linarith
    have h1 : 1 - P.M₂ ^ 2 = 0 := by linear_combination hPV₂' - P.M₂ ^ 2 * hPV₁
    nlinarith
  obtain ⟨hc₁, hc₂⟩ := pv_unique hne hPV₁ hPV₂'
  -- the three flavours
  have hsq : P.mγ ^ 2 < 4 := by nlinarith
  have F0 := vpFlavour_eq_outer (M := 1) one_ne_zero hmγ hmΛ (by norm_num; exact hsq)
  have F1 := vpFlavour_eq_outer (M := P.M₁) (by linarith : P.M₁ ≠ 0).symm.symm hmγ hmΛ
    (by nlinarith)
  have F2 := vpFlavour_eq_outer (M := P.M₂) (by linarith : P.M₂ ≠ 0).symm.symm hmγ hmΛ
    (by nlinarith)
  -- the outer integrand
  have hpt : ∀ x ∈ uIcc (0 : ℝ) 1,
      x ^ 2 * ((vacuumPolarizationLoop P (photonVar x) - P.δ₃) * photonVar x *
        photonD P.mγ P.Λ (photonVar x) ^ 2) =
      P.e ^ 2 / (4 * π ^ 2) * (flavOuter 1 P.mγ P.Λ x + P.c₁ * flavOuter P.M₁ P.mγ P.Λ x +
        P.c₂ * flavOuter P.M₂ P.mγ P.Λ x) := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    rw [hδ₃, vacuumPolarizationLoop_sub_zero P hmass (photonVar_nonneg hx), Fin.sum_univ_three]
    simp only [Params.loopCoeff, Params.mass, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hm, flavOuter]
    ring
  unfold vpOuterF2 outerF2
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (F0.1.add (F1.1.const_mul _)) (F2.1.const_mul _),
    intervalIntegral.integral_add F0.1 (F1.1.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, ← F0.2, ← F1.2, ← F2.2]
  unfold vpUnitReg
  rw [← hc₁, ← hc₂]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-! ### The VP unit of the model, given the nested form -/

/-- **The nested-form identity of the VP unit at `q = 0` (not proved here)**: the model's VP unit
at charge `1` is the outer one-loop functional of the inserted photon function `Π k² D²`,
`unitF2 .VP P = vpOuterF2 P`. Its proof is the nested structure of the VP class (O2-8, O2-10,
O2-13) applied to the explicit parametric values `-vpZero P + 2 d3Zero P`. -/
def VPUnitNested (P : Params) : Prop :=
  unitF2 .VP P = ((vpOuterF2 P : ℝ) : ℂ)

/-- **The model's VP unit equals the explicit value, given the nested form.** At `m = 1`, with
the Pauli–Villars conditions, `0 < m_γ < Λ`, `m_γ < 2`, and `d₃` fixed by (Z₈) at charge `1`:
`16π⁴ unitF2 .VP (atUnitCharge P d₁ d₂ d_m d₃) = vpUnitReg m_γ Λ M₁ M₂`. -/
theorem unitF2_VP_eq_vpUnitReg (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hm1 : P.m = 1) (hmγ : 0 < P.mγ)
    (hmΛ : P.mγ < P.Λ) (hm2 : P.mγ < 2) {d₁ d₂ dm d₃ : ℝ}
    (hph : IsPhotonOnShell (atUnitCharge P d₁ d₂ dm d₃) hm hM₁ hM₂ hPV₁ hPV₂)
    (hN : VPUnitNested (atUnitCharge P d₁ d₂ dm d₃)) :
    (16 * (π : ℂ) ^ 4) * unitF2 .VP (atUnitCharge P d₁ d₂ dm d₃) =
      ((vpUnitReg P.mγ P.Λ P.M₁ P.M₂ : ℝ) : ℂ) := by
  have hδ := (QED.TwoLoop.Scaling.isPhotonOnShell_iff (atUnitCharge P d₁ d₂ dm d₃) hm hM₁ hM₂
    hPV₁ hPV₂).1 hph
  have key := vpUnitReg_eq_vpOuterF2 (atUnitCharge P d₁ d₂ dm d₃) hm1 (hm1 ▸ hM₁) (hm1 ▸ hM₂)
    hPV₁ hPV₂ hmγ hmΛ hm2 hδ
  have he : (atUnitCharge P d₁ d₂ dm d₃).e = 1 := rfl
  rw [he, one_pow, one_mul] at key
  have key' : 16 * π ^ 4 * vpOuterF2 (atUnitCharge P d₁ d₂ dm d₃) =
      vpUnitReg P.mγ P.Λ P.M₁ P.M₂ := key
  rw [hN, ← key']
  push_cast
  ring

/-- **The D-37.4 iterated limit of the model's VP unit, given the nested form.** For every
`η > 0` there is `R` such that for all `M₁, M₂ > R` there are `δ > 0` and `Λ₀` such that for every
parameter set with `m = 1`, regulator masses `M₁, M₂`, Pauli–Villars coefficients,
`m_γ ∈ (0, δ)`, `Λ > Λ₀`, and every `d₃` fixed by (Z₈) at charge `1` for which the nested form
holds, `|16π⁴ unitF2 .VP (atUnitCharge P d₁ d₂ d_m d₃) - (119/36 - π²/3)| < η`. -/
theorem unitF2_VP_iterated_limit :
    ∀ η > 0, ∃ R : ℝ, ∀ M₁ M₂ : ℝ, R < M₁ → R < M₂ → ∃ δ > 0, ∃ Λ₀ : ℝ,
      ∀ (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
        (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0),
        P.m = 1 → P.M₁ = M₁ → P.M₂ = M₂ → 0 < P.mγ → P.mγ < δ → Λ₀ < P.Λ →
        ∀ d₁ d₂ dm d₃ : ℝ, IsPhotonOnShell (atUnitCharge P d₁ d₂ dm d₃) hm hM₁ hM₂ hPV₁ hPV₂ →
          VPUnitNested (atUnitCharge P d₁ d₂ dm d₃) →
          ‖(16 * (π : ℂ) ^ 4) * unitF2 .VP (atUnitCharge P d₁ d₂ dm d₃) -
            ((119 / 36 - π ^ 2 / 3 : ℝ) : ℂ)‖ < η := by
  intro η hη
  obtain ⟨R, hR⟩ := vpUnitReg_iterated_limit η hη
  refine ⟨R, fun M₁ M₂ h1 h2 => ?_⟩
  obtain ⟨δ, hδ, Λ₀, hΛ₀⟩ := hR M₁ M₂ h1 h2
  refine ⟨min δ 1, lt_min hδ one_pos, max Λ₀ 2, ?_⟩
  intro P hm hM₁ hM₂ hPV₁ hPV₂ hm1 e1 e2 hmγ hmδ hΛ d₁ d₂ dm d₃ hph hN
  have hmδ1 : P.mγ < 1 := hmδ.trans_le (min_le_right _ _)
  have hmΛ : P.mγ < P.Λ := by linarith [le_max_right Λ₀ 2]
  rw [unitF2_VP_eq_vpUnitReg P hm hM₁ hM₂ hPV₁ hPV₂ hm1 hmγ hmΛ (by linarith) hph hN, e1, e2,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact hΛ₀ P.mγ P.Λ hmγ (hmδ.trans_le (min_le_left _ _)) (lt_of_le_of_lt (le_max_left _ _) hΛ)

end QED.TwoLoop.UnitVPLink

end
