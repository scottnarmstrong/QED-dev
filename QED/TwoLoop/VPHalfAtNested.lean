/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalfAtInner
public import QED.TwoLoop.NestedVPFubiniBound
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The vacuum-polarization class at fixed `ε` with the inner loop in closed form

Steps 1 and 2 of the nested route to `QED.TwoLoop.VPHalf.VPHalfSubAt` (obligation O2-8),
combined, and the first manipulation of step 3.

* `contractionValue₂_VP_eq_closedForm`: for `ε > 0`, the mass and Pauli–Villars conditions and
  momentum conservation, the value (T₁₀) of the class `VP` is the energy-first integral over the
  photon momentum `k` of `∑ ρ σ, vpOuter … k ρ σ · (i Π̂_ε(k²) (k² g^{ρσ} - k^ρ k^σ)
  + ε S_ε(k²) g^{ρσ})`, with no hypothesis left
  (`QED.TwoLoop.NestedVPFubiniBound.contractionValue₂_VP_eq_nested` and
  `QED.TwoLoop.VPHalfAt.energyFirstIntegral_vacuumPolarizationIntegrand_eq`).
* `vpLoopEps_eq_spectral`, `vpExtraEps_eq_spectral`: the integration by parts in the Feynman
  parameter, which turns the logarithms into rational functions of `k²`:
  `Π̂_ε(s) = (e²/2π²) ((1/6) ∑_f c_f log(M_f² - iε)
    - s ∫₀¹ (x²/2 - x³/3)(1 - 2x) ∑_f c_f / (M_f² + x(1-x)s - iε) dx)`,
  `S_ε(s) = (e²/4π²) (∑_f c_f log(M_f² - iε) - s ∫₀¹ x(1 - 2x) ∑_f c_f / (M_f² + x(1-x)s - iε) dx)`.
  Each denominator is `x(1-x) (s + μ² - iε/(x(1-x)))` with `μ² = M_f²/(x(1-x))`: a propagator of
  mass `μ` with the prescription `ε/(x(1-x))`.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.TwoLoop.VPHalfAt

open QED.WickModel QED.WickModel.VacuumPolarizationLimit QED.OneLoop QED.TwoLoop.Enumeration

/-- **The class `VP` at fixed `ε > 0`, with the inner vacuum polarization in closed form**: no
integrability hypothesis remains. -/
theorem contractionValue₂_VP_eq_closedForm (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4)
    (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hε : 0 < P.ε) :
    contractionValue₂ P Class5.VP.rep pOut pIn kIn αOut βIn μ =
      energyFirstIntegral fun k =>
        ∑ ρ : Fin 4, ∑ σ : Fin 4, NestedVP.vpOuter P (pIn 0) (kIn 0) k (αOut 0) (βIn 0) (μ 0) ρ σ *
          (I * vpLoopEps P P.ε (Minkowski.dot k k) *
              ((Minkowski.dot k k * Minkowski.metric ρ σ - k ρ * k σ : ℝ) : ℂ)
            + (P.ε : ℂ) * vpExtraEps P P.ε (Minkowski.dot k k) * (Minkowski.metric ρ σ : ℂ)) := by
  rw [NestedVPFubiniBound.contractionValue₂_VP_eq_nested P hmom αOut βIn μ hm hM₁ hM₂ hPV₁ hPV₂ hε]
  simp only [energyFirstIntegral_vacuumPolarizationIntegrand_eq hm hM₁ hM₂ hPV₁ hPV₂ hε]

/-! ### Integration by parts in the Feynman parameter -/

/-- `∑_f c_f / (M_f² + x(1-x)s - iε)`, weighted by `1 - 2x`. -/
noncomputable def vpRatSum (P : Params) (ε s x : ℝ) : ℂ :=
  ∑ f, (P.loopCoeff f : ℂ) * (((1 - 2 * x) * s : ℝ) : ℂ) /
    ((vacuumPolarizationFeynmanMass (P.mass f) s x : ℂ) - ε * I)

theorem feynmanMass_sub_mem_slitPlane (M s x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ((vacuumPolarizationFeynmanMass M s x : ℂ) - ε * I) ∈ slitPlane :=
  mem_slitPlane_of_im_neg (by simp [hε])

/-- `d/dx ∑_f c_f log(M_f² + x(1-x)s - iε) = ∑_f c_f (1 - 2x) s / (M_f² + x(1-x)s - iε)`. -/
theorem hasDerivAt_vpLogSum (P : Params) {ε : ℝ} (hε : 0 < ε) (s x : ℝ) :
    HasDerivAt (vpLogSum P ε s) (vpRatSum P ε s x) x := by
  unfold vpLogSum vpRatSum
  refine HasDerivAt.fun_sum fun f _ => ?_
  have hD : HasDerivAt (fun x : ℝ => vacuumPolarizationFeynmanMass (P.mass f) s x)
      ((1 - 2 * x) * s) x := by
    unfold vacuumPolarizationFeynmanMass
    have := ((((hasDerivAt_id x).mul ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))).mul
      (hasDerivAt_const x s)).const_add (P.mass f ^ 2))
    refine this.congr_deriv ?_
    simp only [id, Pi.sub_apply]
    ring
  have h := (hD.ofReal_comp.sub_const ((ε : ℂ) * I)).clog_real
    (feynmanMass_sub_mem_slitPlane _ s x hε)
  have h2 := h.const_mul (P.loopCoeff f : ℂ)
  refine h2.congr_deriv ?_
  ring

theorem continuous_vpRatSum (P : Params) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    Continuous (vpRatSum P ε s) := by
  unfold vpRatSum
  refine continuous_finsetSum _ fun f _ => Continuous.div (by fun_prop)
    (by unfold vacuumPolarizationFeynmanMass; fun_prop) fun x => ?_
  exact slitPlane_ne_zero (feynmanMass_sub_mem_slitPlane _ s x hε)

theorem vpLogSum_one (P : Params) (ε s : ℝ) :
    vpLogSum P ε s 1 = ∑ f, (P.loopCoeff f : ℂ) * log (((P.mass f ^ 2 : ℝ) : ℂ) - ε * I) := by
  simp [vpLogSum, vacuumPolarizationFeynmanMass]

/-- **The transverse coefficient after integration by parts in `x`**. -/
theorem vpLoopEps_eq_spectral (P : Params) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    vpLoopEps P ε s = ((P.e ^ 2 / (2 * π ^ 2) : ℝ) : ℂ) *
      ((1 / 6 : ℂ) * ∑ f, (P.loopCoeff f : ℂ) * log (((P.mass f ^ 2 : ℝ) : ℂ) - ε * I)
        - ∫ x in (0 : ℝ)..1, vpRatSum P ε s x * ((x ^ 2 / 2 - x ^ 3 / 3 : ℝ) : ℂ)) := by
  have hv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => ((x ^ 2 / 2 - x ^ 3 / 3 : ℝ) : ℂ))
      ((x * (1 - x) : ℝ) : ℂ) x := fun x => by
    have := (((hasDerivAt_pow 2 x).div_const 2).sub ((hasDerivAt_pow 3 x).div_const 3)).ofReal_comp
    refine this.congr_deriv ?_
    push_cast
    ring
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => hasDerivAt_vpLogSum P hε s x) (fun x _ => hv x)
    ((continuous_vpRatSum P hε s).intervalIntegrable 0 1)
    ((by fun_prop : Continuous fun x : ℝ => ((x * (1 - x) : ℝ) : ℂ)).intervalIntegrable 0 1)
  unfold vpLoopEps
  congr 1
  have e : ∫ x in (0 : ℝ)..1, ((x * (1 - x) : ℝ) : ℂ) * vpLogSum P ε s x =
      ∫ x in (0 : ℝ)..1, vpLogSum P ε s x * ((x * (1 - x) : ℝ) : ℂ) := by
    congr 1
    funext x
    ring
  rw [e, hibp, vpLogSum_one]
  push_cast
  ring

/-- **The coefficient of the extra term after integration by parts in `x`**. -/
theorem vpExtraEps_eq_spectral (P : Params) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    vpExtraEps P ε s = ((P.e ^ 2 / (4 * π ^ 2) : ℝ) : ℂ) *
      (∑ f, (P.loopCoeff f : ℂ) * log (((P.mass f ^ 2 : ℝ) : ℂ) - ε * I)
        - ∫ x in (0 : ℝ)..1, vpRatSum P ε s x * (x : ℂ)) := by
  have hv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (x : ℂ)) ((1 : ℝ) : ℂ) x := fun x =>
    (hasDerivAt_id x).ofReal_comp
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => hasDerivAt_vpLogSum P hε s x) (fun x _ => hv x)
    ((continuous_vpRatSum P hε s).intervalIntegrable 0 1)
    (intervalIntegrable_const (c := ((1 : ℝ) : ℂ)))
  unfold vpExtraEps
  congr 1
  have e : ∫ x in (0 : ℝ)..1, vpLogSum P ε s x =
      ∫ x in (0 : ℝ)..1, vpLogSum P ε s x * ((1 : ℝ) : ℂ) := by
    congr 1
    funext x
    simp
  rw [e, hibp, vpLogSum_one]
  push_cast
  ring

end QED.TwoLoop.VPHalfAt

end
