/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalfAtRadial
public import QED.WickModel.VacuumPolarizationLimit
import QED.WickModel.SelfEnergyLimit
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The one-loop vacuum polarization at fixed `ε > 0` in closed form

The inner identity of the nested route to `QED.TwoLoop.VPHalf.VPHalfSubAt` (obligation O2-8 at
the `ε → 0` level, step 2 of the plan in `docs/TWO-LOOP-DERIVATION.md`). For `ε > 0`, every photon
momentum `k` (no threshold condition), the mass and the Pauli–Villars conditions, the
energy-first integral of the one-loop vacuum polarization integrand of (62.12) is

`Π^{μν}_ε(k) = i Π̂_ε(k²) (k² g^{μν} - k^μ k^ν) + ε S_ε(k²) g^{μν}`,

`Π̂_ε(s) = (e²/2π²) ∫₀¹ x(1-x) ∑_f c_f log(M_f² + x(1-x)s - iε) dx` (`vpLoopEps`),
`S_ε(s) = (e²/4π²) ∫₀¹ ∑_f c_f log(M_f² + x(1-x)s - iε) dx` (`vpExtraEps`),

with the principal logarithm (`energyFirstIntegral_vacuumPolarizationIntegrand_eq`). This is the
structure found numerically in `scripts/numerics/vp_half/`, now with the extra term explicit: it
is `ε` times a function of `k²` only.

## Proof

As for packet 6b at `ε = 0` (`QED.WickModel.VacuumPolarizationLimit.integral_spatialG_zero`):
the spatial integral is exchanged with the Feynman-parameter integral (`integral_spatialG_eq`,
with the uniform packet-6b bound); at fixed `x` the spatial momentum is translated by `x k⃗` and
symmetrized (`timeSum_shift_add`); the two resulting Pauli–Villars sums are those of
`QED.TwoLoop.VPHalfAt` with complex masses `D_f - iε`: the covariance integral vanishes and the
logarithmic one gives `-2π i ∑_f c_f log(D_f - iε)`. The extra term comes from
`α^{μν} = 8 h^{μν} - 4 g^{μν}`: the numerator's leading coefficient differs from the spatial
projector part, and the difference multiplies `z + W = iε`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped Real

namespace QED.TwoLoop.VPHalfAt

open QED.WickModel QED.WickModel.VacuumPolarizationLimit QED.OneLoop

/-! ### The closed-form functions -/

/-- `∑_f c_f log(M_f² + x(1-x)s - iε)`. -/
noncomputable def vpLogSum (P : Params) (ε s x : ℝ) : ℂ :=
  ∑ f, (P.loopCoeff f : ℂ) * log ((vacuumPolarizationFeynmanMass (P.mass f) s x : ℂ) - ε * I)

/-- **The transverse coefficient at fixed `ε`**:
`Π̂_ε(s) = (e²/2π²) ∫₀¹ x(1-x) ∑_f c_f log(M_f² + x(1-x)s - iε) dx`. -/
noncomputable def vpLoopEps (P : Params) (ε s : ℝ) : ℂ :=
  ((P.e ^ 2 / (2 * π ^ 2) : ℝ) : ℂ) * ∫ x in (0 : ℝ)..1, ((x * (1 - x) : ℝ) : ℂ) * vpLogSum P ε s x

/-- **The coefficient of the extra term at fixed `ε`**:
`S_ε(s) = (e²/4π²) ∫₀¹ ∑_f c_f log(M_f² + x(1-x)s - iε) dx`. -/
noncomputable def vpExtraEps (P : Params) (ε s : ℝ) : ℂ :=
  ((P.e ^ 2 / (4 * π ^ 2) : ℝ) : ℂ) * ∫ x in (0 : ℝ)..1, vpLogSum P ε s x

theorem continuous_vpLogSum (P : Params) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    Continuous (vpLogSum P ε s) := by
  unfold vpLogSum
  refine continuous_finsetSum _ fun f _ => continuous_const.mul ?_
  refine Continuous.clog (by unfold vacuumPolarizationFeynmanMass; fun_prop) fun x => ?_
  exact mem_slitPlane_of_im_neg (by simp [hε])

/-! ### The symmetrization at fixed `ε` -/

theorem alpha_eq (μ ν : Fin 4) : alpha μ ν = 8 * hproj μ ν - 4 * Minkowski.metric μ ν := by
  unfold alpha hproj
  ring

/-- The flavour-`M` closed form after the translation by `x k⃗`, symmetrized. -/
theorem timeT_shift_add (M ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) (x : ℝ) (w : Fin 3 → ℝ) :
    timeT M ε k μ ν x (w - fun i => x * k i.succ) + timeT M ε k μ ν x (-w - fun i => x * k i.succ)
      = (π / 2 : ℂ) * (zε ε (selfEnergyFeynmanMass M M (Minkowski.dot k k) x) (∑ i, w i ^ 2)
          ^ (-(3 / 2) : ℂ) *
        (16 * ((((Fin.cons 0 w : Fin 4 → ℝ) μ * (Fin.cons 0 w : Fin 4 → ℝ) ν : ℝ) : ℂ)
            + (hproj μ ν : ℂ) * zε ε (selfEnergyFeynmanMass M M (Minkowski.dot k k) x)
              (∑ i, w i ^ 2))
          + (16 * (x * (1 - x) * (Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν) : ℝ)
            - 8 * I * ε * Minkowski.metric μ ν))) := by
  have hneg : (Fin.cons 0 (-w) : Fin 4 → ℝ) = -(Fin.cons 0 w) := by
    funext q
    refine Fin.cases ?_ (fun j => ?_) q <;> simp
  have hsq : ∑ i, (-w) i ^ 2 = ∑ i, w i ^ 2 := by simp
  have e1 := SelfEnergyLimit.cons_neg_sub_eq k x w
  have e2 := SelfEnergyLimit.cons_neg_sub_eq k x (-w)
  rw [hneg] at e2
  simp only [timeT, SelfEnergyLimit.massW_sub, hsq, e1, e2]
  have key := congrArg (fun r : ℝ => (r : ℂ)) (bracket_shift_add M x k w μ ν)
  have ha := congrArg (fun r : ℝ => (r : ℂ)) (alpha_eq μ ν)
  simp only [zε]
  push_cast at key ha ⊢
  set Z := (-((∑ i, (w i : ℂ) ^ 2) + (selfEnergyFeynmanMass M M (Minkowski.dot k k) x : ℂ))
    + (ε : ℂ) * I) ^ (-(3 / 2) : ℂ)
  linear_combination (π / 2 : ℂ) * Z * key + (π / 2 : ℂ) * Z * (2 * ε * I) * ha

/-- **The symmetrized Pauli–Villars sum at fixed `ε > 0`**. -/
theorem timeSum_shift_add (P : Params) (ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) (x : ℝ)
    (w : Fin 3 → ℝ) :
    timeSum P ε k μ ν x (w - fun i => x * k i.succ)
        + timeSum P ε k μ ν x (-w - fun i => x * k i.succ)
      = 8 * π * cRadialPiece P.loopCoeff
          (fun f => selfEnergyFeynmanMass (P.mass f) (P.mass f) (Minkowski.dot k k) x) ε μ ν w
        + π * ((8 * (x * (1 - x) * (Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν)) : ℝ)
            - 4 * I * ε * Minkowski.metric μ ν) *
          cRadialSum P.loopCoeff
            (fun f => selfEnergyFeynmanMass (P.mass f) (P.mass f) (Minkowski.dot k k) x) ε w := by
  simp only [timeSum, cRadialPiece, cRadialSum, hSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← mul_add, timeT_shift_add]
  push_cast
  ring

/-! ### The spatial integral at fixed Feynman parameter -/

theorem mass_le_feynmanMass {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (s x : ℝ) (f : Fin 3) :
    selfEnergyFeynmanMass (P.mass 0) (P.mass 0) s x ≤
      selfEnergyFeynmanMass (P.mass f) (P.mass f) s x := by
  have := mass_sq_le hm hM₁ hM₂ f
  unfold selfEnergyFeynmanMass
  linarith

/-- For `ε > 0` the Pauli–Villars sum of closed forms is integrable in the spatial momentum, at
every `k` and `x ∈ [0, 1]`. -/
theorem integrable_timeSum {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) (μ ν : Fin 4) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Integrable fun v : Fin 3 → ℝ => timeSum P ε k μ ν x v := by
  obtain ⟨c, hc, hlow⟩ := exists_mul_le_max_massW P hε k
  refine ((integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5)
    (by simp; norm_num)).const_mul (constK P k μ ν c * (1 + ε))).mono'
    ((measurable_timeSum P ε k μ ν).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  exact (norm_timeSum_le hm hM₁ hM₂ hPV₁ hPV₂ k μ ν hc hε hx v (hlow x hx v)).trans (le_of_eq
    (by ring))

/-- **The spatial integral at fixed Feynman parameter and fixed `ε > 0`**:
`∫ d³v ∑_f c_f T_f = -8π² i x(1-x) L (k² g^{μν} - k^μ k^ν) - 4π² ε L g^{μν}`, with
`L = ∑_f c_f log(D_f - iε)`. -/
theorem integral_timeSum {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) (μ ν : Fin 4) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∫ v, timeSum P ε k μ ν x v =
      -(8 * π ^ 2 * I) * ((x * (1 - x) * (Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν) : ℝ)
          : ℂ) * vpLogSum P ε (Minkowski.dot k k) x
        - 4 * π ^ 2 * ε * (Minkowski.metric μ ν : ℂ) * vpLogSum P ε (Minkowski.dot k k) x := by
  set D : Fin 3 → ℝ := fun f => selfEnergyFeynmanMass (P.mass f) (P.mass f) (Minkowski.dot k k) x
    with hDdef
  have hc := sum_loopCoeff hPV₁
  have hcD : ∑ f, P.loopCoeff f * D f = 0 := sum_loopCoeff_mul_feynmanMass hPV₁ hPV₂ _ x
  have hD : ∀ f, D 0 ≤ D f := fun f => mass_le_feynmanMass hm hM₁ hM₂ _ x f
  have hf := integrable_timeSum hm hM₁ hM₂ hPV₁ hPV₂ hε k μ ν hx
  have hS := integrable_cRadialSum hε hc hD
  have hsym : Integrable fun w : Fin 3 → ℝ => timeSum P ε k μ ν x (w - fun i => x * k i.succ)
      + timeSum P ε k μ ν x (-w - fun i => x * k i.succ) :=
    (hf.comp_sub_right _).add (hf.comp_sub_right _).comp_neg
  have hπ : (8 * π : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    simp [this]
  have hP : ∀ μ' ν' : Fin 4, Integrable (cRadialPiece P.loopCoeff D ε μ' ν') := fun μ' ν' => by
    have hsym' : Integrable fun w : Fin 3 → ℝ =>
        timeSum P ε k μ' ν' x (w - fun i => x * k i.succ)
          + timeSum P ε k μ' ν' x (-w - fun i => x * k i.succ) :=
      ((integrable_timeSum hm hM₁ hM₂ hPV₁ hPV₂ hε k μ' ν' hx).comp_sub_right _).add
        ((integrable_timeSum hm hM₁ hM₂ hPV₁ hPV₂ hε k μ' ν' hx).comp_sub_right _).comp_neg
    refine ((hsym'.sub (hS.const_mul (π * ((8 * (x * (1 - x) * (Minkowski.dot k k *
      Minkowski.metric μ' ν' - k μ' * k ν')) : ℝ) - 4 * I * ε * Minkowski.metric μ' ν')))).const_mul
      (8 * π : ℂ)⁻¹).congr (Eventually.of_forall fun w => ?_)
    simp only [Pi.sub_apply]
    rw [timeSum_shift_add P ε k μ' ν' x w]
    field_simp
    ring
  have hP0 : ∫ w, cRadialPiece P.loopCoeff D ε μ ν w = 0 :=
    integral_cRadialPiece_eq_zero hε hc hcD hD (fun i => hP i.succ i.succ) μ ν
  have hS0 := integral_cRadialSum hε hc hD
  rw [SelfEnergyLimit.integral_eq_half_integral_of_add_neg hf (fun i => x * k i.succ)
    (timeSum_shift_add P ε k μ ν x), integral_add ((hP μ ν).const_mul _) (hS.const_mul _),
    integral_const_mul, integral_const_mul, hP0, hS0]
  have hlog : ∑ f, (P.loopCoeff f : ℂ) * log ((D f : ℂ) - (ε : ℂ) * I) =
      vpLogSum P ε (Minkowski.dot k k) x := by
    simp only [vpLogSum, hDdef, VacuumPolarizationLimit.selfEnergyFeynmanMass_eq]
  rw [hlog]
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-! ### Assembly -/

/-- For `ε > 0`, the spatial integral and the Feynman-parameter integral can be swapped. -/
theorem integral_spatialG_eq {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    ∫ v, spatialG P ε k μ ν v = ∫ x in Ioc (0 : ℝ) 1, kappa P.e * ∫ v, timeSum P ε k μ ν x v := by
  obtain ⟨c, hc, hlow⟩ := exists_mul_le_max_massW P hε k
  set K := constK P k μ ν c * (1 + ε)
  set F : (Fin 3 → ℝ) → ℝ → ℂ := fun v x => kappa P.e * timeSum P ε k μ ν x v with hF
  have hint : Integrable (Function.uncurry F)
      ((volume : Measure (Fin 3 → ℝ)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    have hg := ((integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5)
      (by simp; norm_num)).const_mul (‖kappa P.e‖ * K)).mul_prod
        (integrable_const (μ := volume.restrict (Ioc (0 : ℝ) 1)) (1 : ℝ))
    refine Integrable.mono' hg ?_ ((SelfEnergyLimit.ae_prod_restrict_Ioc _).mono fun q hq => ?_)
    · exact (measurable_const.mul (measurable_timeSum P ε k μ ν)).aestronglyMeasurable
    · obtain ⟨v, x⟩ := q
      simp only [Function.uncurry_apply_pair, hF, mul_one] at hq ⊢
      rw [norm_mul]
      calc ‖kappa P.e‖ * ‖timeSum P ε k μ ν x v‖
          ≤ ‖kappa P.e‖ * (K * (1 + ‖v‖) ^ (-(5 : ℝ))) := by
            gcongr
            exact (norm_timeSum_le hm hM₁ hM₂ hPV₁ hPV₂ k μ ν hc hε (Ioc_subset_Icc_self hq) v
              (hlow x (Ioc_subset_Icc_self hq) v)).trans (le_of_eq (by ring))
        _ = ‖kappa P.e‖ * K * (1 + ‖v‖) ^ (-(5 : ℝ)) := by ring
  have hG : ∀ v, spatialG P ε k μ ν v = ∫ x in Ioc (0 : ℝ) 1, F v x := fun v => rfl
  simp_rw [hG]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hF]
  rw [integral_const_mul]

/-- **The one-loop vacuum polarization at fixed `ε > 0`, in closed form** (O2-8, step 2). For
`m > 0`, regulator fermions heavier than the electron, the Pauli–Villars conditions, `ε > 0` and
every photon momentum `k`, the energy-first integral of the integrand of `i Π^{μν}(k)` in (62.12)
is `i Π̂_ε(k²) (k² g^{μν} - k^μ k^ν) + ε S_ε(k²) g^{μν}`. -/
theorem energyFirstIntegral_vacuumPolarizationIntegrand_eq {P : Params} (hm : 0 < P.m)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {ε : ℝ} (hε : 0 < ε)
    (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    energyFirstIntegral (fun ℓ => vacuumPolarizationIntegrand P ε k ℓ μ ν) =
      I * vpLoopEps P ε (Minkowski.dot k k) *
          ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ)
        + (ε : ℂ) * vpExtraEps P ε (Minkowski.dot k k) * (Minkowski.metric μ ν : ℂ) := by
  have h1 : energyFirstIntegral (fun ℓ => vacuumPolarizationIntegrand P ε k ℓ μ ν) =
      ∫ v, spatialG P ε k μ ν v := by
    simp only [energyFirstIntegral]
    exact integral_congr_ae (Eventually.of_forall fun v =>
      integral_vacuumPolarizationIntegrand_time hε P k μ ν v)
  set s := Minkowski.dot k k
  set T : ℝ := s * Minkowski.metric μ ν - k μ * k ν
  have hL := continuous_vpLogSum P hε s
  have iL : IntegrableOn (vpLogSum P ε s) (Ioc (0 : ℝ) 1) :=
    (hL.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have iL2 : IntegrableOn (fun x : ℝ => ((x * (1 - x) : ℝ) : ℂ) * vpLogSum P ε s x)
      (Ioc (0 : ℝ) 1) :=
    (((by fun_prop : Continuous fun x : ℝ => ((x * (1 - x) : ℝ) : ℂ)).mul
      hL).continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hpt : ∀ x ∈ Ioc (0 : ℝ) 1, kappa P.e * ∫ v, timeSum P ε k μ ν x v =
      (kappa P.e * (-(8 * π ^ 2 * I)) * (T : ℂ)) * (((x * (1 - x) : ℝ) : ℂ) * vpLogSum P ε s x)
        + (kappa P.e * (-(4 * π ^ 2 * ε * (Minkowski.metric μ ν : ℂ)))) * vpLogSum P ε s x := by
    intro x hx
    rw [integral_timeSum hm hM₁ hM₂ hPV₁ hPV₂ hε k μ ν (Ioc_subset_Icc_self hx)]
    simp only [T]
    push_cast
    ring
  rw [h1, integral_spatialG_eq hm hM₁ hM₂ hPV₁ hPV₂ hε k μ ν,
    setIntegral_congr_fun measurableSet_Ioc hpt, integral_add (iL2.const_mul _) (iL.const_mul _),
    integral_const_mul, integral_const_mul]
  simp only [vpLoopEps, vpExtraEps, intervalIntegral.integral_of_le zero_le_one, kappa_eq]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring

end QED.TwoLoop.VPHalfAt

end
