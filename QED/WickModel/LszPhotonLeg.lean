/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.Spinor
public import QED.Frozen.OneLoop.PhotonPropagator
public import QED.Frozen.WickModel.OnePIFunction
public import QED.Frozen.WickModel.VacuumPolarizationSpec
public import QED.WickModel.VacuumPolarizationLimit
public import Mathlib.Topology.Instances.Matrix
import QED.Algebra.OnShell
import QED.Integration.ParametricSmooth
import QED.WickModel.LszLegs
import QED.WickModel.PhotonOnShell
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The photon leg of the LSZ amplitude

The photon of the order-`e³` connected function is a background-field leg (decision D-29): its
line is amputated by the free photon propagator and keeps the vacuum-polarization insertion. The
photon-leg term of the function with incoming photon momentum `q` is
`∑_{νρ} [i e γ^ν]_{αβ} (1/i) Δ̃_{νρ}(q) [i Π^{μρ}_ε(q)]`, where `i Π^{μρ}_ε(q)` is the
one-particle-irreducible two-photon function (counterterm included). This module proves:

* for `q² > -4m²` off the photon poles `q² = -m_γ²`, `q² = -Λ²`, the limit `ε → 0⁺` of this
  term exists and is the same expression at `ε = 0` with `i Π(q²) (q² g^{μρ} - q^μ q^ρ)` from the
  characterization (Z₇′);
* with `Π(s) = -δ₃ + Π_loop(s)` this limit, `QED.WickModel.photonLegLimit`, is defined for all
  `q`; between the electron spinors and as a function of `(r', r)`, `q = r' - r`, it is
  continuous at an on-shell pair `(p', p)` of positive energy, with value
  `e q₀² [1/(q₀² + m_γ²) - 1/(q₀² + Λ²)] Π(q₀²) ū' γ^μ u`, `q₀ = p' - p`, because
  `ū(p') (p̸' - p̸) u(p) = 0`.

## Main definitions

* `QED.WickModel.photonLegLimit`: the limit `ε → 0⁺` of the photon-leg term.

## Main statements

* `QED.WickModel.continuousOn_vacuumPolarizationLoop`: `Π_loop` is continuous below the pair
  threshold.
* `QED.WickModel.vacuumPolarization_eq_loop`: (Z₇) in closed form, `Π = -δ₃ + Π_loop`.
* `QED.WickModel.tendsto_photonLeg`: the limit `ε → 0⁺`, with the sealed `Π` (Z₇).
* `QED.WickModel.tendsto_photonLeg_photonLegLimit`: the same limit, as `photonLegLimit`.
* `QED.WickModel.tendsto_photonLeg_sandwich`: the limit between two spinors.
* `QED.WickModel.eventually_photonLeg_domain`: near an on-shell pair of positive energy,
  `q = r' - r` satisfies the hypotheses of the limit.
* `QED.WickModel.tendsto_photonLegLimit_sandwich`: continuity at the on-shell pair, with the
  value above.
-/

@[expose] public section

open Matrix Complex Filter Topology Set MeasureTheory
open scoped ContDiff

namespace QED.WickModel

/-! ### The vacuum polarization function -/

/-- **Continuity of `Π_loop`.** For `m > 0` and regulator fermions heavier than the electron,
`vacuumPolarizationLoop P` is continuous on `s > -4m²`. -/
theorem continuousOn_vacuumPolarizationLoop {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) : ContinuousOn (vacuumPolarizationLoop P) (Ioi (-(4 * P.m ^ 2))) := by
  have hD : ∀ f, ContDiff ℝ ∞ (fun q : ℝ × ℝ =>
      vacuumPolarizationFeynmanMass (P.mass f) q.1 q.2) := fun f => by
    unfold vacuumPolarizationFeynmanMass
    fun_prop
  set W := ⋂ f : Fin 3, {q : ℝ × ℝ | 0 < vacuumPolarizationFeynmanMass (P.mass f) q.1 q.2}
  have hW : IsOpen W :=
    isOpen_iInter_of_finite fun f => isOpen_lt continuous_const (hD f).continuous
  have hUW : Ioi (-(4 * P.m ^ 2)) ×ˢ Icc (0 : ℝ) 1 ⊆ W := fun q hq => mem_iInter.mpr fun f => by
    change 0 < vacuumPolarizationFeynmanMass (P.mass f) q.1 q.2
    rw [← VacuumPolarizationLimit.selfEnergyFeynmanMass_eq]
    exact VacuumPolarizationLimit.selfEnergyFeynmanMass_mass_pos hm hM₁ hM₂ hq.1 hq.2 f
  have hw : ContDiff ℝ ∞ (fun q : ℝ × ℝ => q.2 * (1 - q.2)) := by fun_prop
  have hg : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => q.2 * (1 - q.2) *
      ∑ f, P.loopCoeff f * Real.log (vacuumPolarizationFeynmanMass (P.mass f) q.1 q.2)) W :=
    hw.contDiffOn.mul (ContDiffOn.sum fun f _ => contDiffOn_const.mul
      ((hD f).contDiffOn.log fun q hq => (mem_iInter.mp hq f).ne'))
  have h := QED.Integration.contDiffOn_integral_of_contDiffOn_prod
    (μ := volume.restrict (Ioc (0 : ℝ) 1)) isCompact_Icc
    ((ae_restrict_mem measurableSet_Ioc).mono fun x hx => Ioc_subset_Icc_self hx)
    isOpen_Ioi hW hUW hg
  refine ((continuousOn_const (c := P.e ^ 2 / (2 * Real.pi ^ 2))).mul h.continuousOn).congr
    fun s _ => ?_
  simp only [vacuumPolarizationLoop, intervalIntegral.integral_of_le zero_le_one, Pi.mul_apply]

/-- **(Z₇) in closed form.** The sealed vacuum polarization function is `-δ₃ + Π_loop`. -/
theorem vacuumPolarization_eq_loop (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (s : {s : ℝ // -(4 * P.m ^ 2) < s}) :
    vacuumPolarization P hm hM₁ hM₂ hPV₁ hPV₂ s =
      -(P.δ₃ : ℂ) + (vacuumPolarizationLoop P s.1 : ℂ) :=
  congrFun (eq_vacuumPolarizationLoop_of_tendsto P hm hM₁ hM₂ hPV₁ hPV₂
    (vacuumPolarization_spec P hm hM₁ hM₂ hPV₁ hPV₂).1) s

/-! ### The limit `ε → 0⁺` -/

/-- Off the poles `q² = -m_γ²`, `q² = -Λ²`, the photon propagator is continuous in `ε` at
`0`. -/
theorem tendsto_photonPropagator_zero {mγ Λ : ℝ} {q : Fin 4 → ℝ}
    (hqγ : Minkowski.dot q q ≠ -mγ ^ 2) (hqΛ : Minkowski.dot q q ≠ -Λ ^ 2) (ν ρ : Fin 4) :
    Tendsto (fun ε : ℝ => QED.OneLoop.photonPropagator mγ Λ ε q ν ρ) (𝓝[>] 0)
      (𝓝 (QED.OneLoop.photonPropagator mγ Λ 0 q ν ρ)) := by
  have h : ∀ M : ℝ, Minkowski.dot q q ≠ -M ^ 2 → ContinuousAt (fun ε : ℝ =>
      (((Minkowski.dot q q + M ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹) 0 := fun M hM => by
    have hne : ((Minkowski.dot q q + M ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I ≠ 0 := by
      rw [ofReal_zero, zero_mul, sub_zero]
      exact ofReal_ne_zero.mpr fun h => hM (by linarith)
    exact (continuous_const.sub (continuous_ofReal.mul continuous_const)).continuousAt.inv₀ hne
  unfold QED.OneLoop.photonPropagator
  exact (continuousAt_const.mul ((h mγ hqγ).sub (h Λ hqΛ))).tendsto.mono_left nhdsWithin_le_nhds

/-- **The photon leg as `ε → 0⁺`.** For `m > 0`, regulator fermions as in (Z₂), and `q` below
the pair threshold and off the photon poles, the photon-leg term
`∑_{νρ} [i e γ^ν]_{αβ} (1/i) Δ̃_{νρ}(q) [i Π^{μρ}_ε(q)]` tends to the same expression at `ε = 0`
with `i Π^{μρ}(q) = i Π(q²) (q² g^{μρ} - q^μ q^ρ)`, `Π` the sealed vacuum polarization (Z₇). -/
theorem tendsto_photonLeg (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {q : Fin 4 → ℝ} (hq : -(4 * P.m ^ 2) < Minkowski.dot q q)
    (hqγ : Minkowski.dot q q ≠ -P.mγ ^ 2) (hqΛ : Minkowski.dot q q ≠ -P.Λ ^ 2)
    (μ α β : Fin 4) :
    Tendsto (fun ε : ℝ => ∑ ν, ∑ ρ, (I * P.e) * Dirac.gamma ν α β *
        ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ ε q ν ρ) *
        onePIFunction { P with ε := ε } 0 2 2 ![] ![] ![q, -q] ![] ![] ![μ, ρ])
      (𝓝[>] 0)
      (𝓝 (∑ ν, ∑ ρ, (I * P.e) * Dirac.gamma ν α β *
        ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ 0 q ν ρ) *
        (I * (vacuumPolarization P hm hM₁ hM₂ hPV₁ hPV₂ ⟨_, hq⟩ *
          ((Minkowski.dot q q * Minkowski.metric μ ρ - q μ * q ρ : ℝ) : ℂ))))) := by
  refine tendsto_finsetSum _ fun ν _ => tendsto_finsetSum _ fun ρ _ => ?_
  have hPi := ((vacuumPolarization_spec P hm hM₁ hM₂ hPV₁ hPV₂).1 q hq μ ρ).const_mul I
  have h2 : Tendsto (fun ε : ℝ =>
      onePIFunction { P with ε := ε } 0 2 2 ![] ![] ![q, -q] ![] ![] ![μ, ρ]) (𝓝[>] 0)
      (𝓝 (I * (vacuumPolarization P hm hM₁ hM₂ hPV₁ hPV₂ ⟨_, hq⟩ *
          ((Minkowski.dot q q * Minkowski.metric μ ρ - q μ * q ρ : ℝ) : ℂ)))) :=
    hPi.congr fun ε => by rw [← mul_assoc, mul_one_div_cancel I_ne_zero, one_mul]
  exact (((tendsto_photonPropagator_zero hqγ hqΛ ν ρ).const_mul (1 / I)).const_mul
    ((I * P.e) * Dirac.gamma ν α β)).mul h2

/-- **The limit of the photon leg**, `∑_{νρ} [i e γ^ν]_{αβ} (1/i) Δ̃_{νρ}(q)|_{ε=0}
i Π(q²) (q² g^{μρ} - q^μ q^ρ)` with `Π(s) = -δ₃ + Π_loop(s)`, the sealed vacuum polarization
in closed form (`QED.WickModel.vacuumPolarization_eq_loop`), so that it is defined for all `q`.
It is the limit of the photon-leg term below the pair threshold and off the photon poles
(`QED.WickModel.tendsto_photonLeg_photonLegLimit`). -/
noncomputable def photonLegLimit (P : Params) (q : Fin 4 → ℝ) (μ α β : Fin 4) : ℂ :=
  ∑ ν, ∑ ρ, (I * P.e) * Dirac.gamma ν α β *
    ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ 0 q ν ρ) *
    (I * ((-(P.δ₃ : ℂ) + (vacuumPolarizationLoop P (Minkowski.dot q q) : ℂ)) *
      ((Minkowski.dot q q * Minkowski.metric μ ρ - q μ * q ρ : ℝ) : ℂ)))

/-- Below the pair threshold, `photonLegLimit` is the limit expression with the sealed `Π`. -/
theorem photonLegLimit_eq (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {q : Fin 4 → ℝ} (hq : -(4 * P.m ^ 2) < Minkowski.dot q q) (μ α β : Fin 4) :
    photonLegLimit P q μ α β =
      ∑ ν, ∑ ρ, (I * P.e) * Dirac.gamma ν α β *
        ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ 0 q ν ρ) *
        (I * (vacuumPolarization P hm hM₁ hM₂ hPV₁ hPV₂ ⟨_, hq⟩ *
          ((Minkowski.dot q q * Minkowski.metric μ ρ - q μ * q ρ : ℝ) : ℂ))) := by
  rw [vacuumPolarization_eq_loop]
  rfl

/-- **The photon leg as `ε → 0⁺`**, with limit `photonLegLimit`. -/
theorem tendsto_photonLeg_photonLegLimit (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {q : Fin 4 → ℝ} (hq : -(4 * P.m ^ 2) < Minkowski.dot q q)
    (hqγ : Minkowski.dot q q ≠ -P.mγ ^ 2) (hqΛ : Minkowski.dot q q ≠ -P.Λ ^ 2)
    (μ α β : Fin 4) :
    Tendsto (fun ε : ℝ => ∑ ν, ∑ ρ, (I * P.e) * Dirac.gamma ν α β *
        ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ ε q ν ρ) *
        onePIFunction { P with ε := ε } 0 2 2 ![] ![] ![q, -q] ![] ![] ![μ, ρ])
      (𝓝[>] 0) (𝓝 (photonLegLimit P q μ α β)) := by
  rw [photonLegLimit_eq P hm hM₁ hM₂ hPV₁ hPV₂ hq]
  exact tendsto_photonLeg P hm hM₁ hM₂ hPV₁ hPV₂ hq hqγ hqΛ μ α β

/-- Entrywise limits pass to the sandwich `(1/i) w M u`. -/
theorem tendsto_sandwich {ι : Type*} {l : Filter ι} {F : ι → Fin 4 → Fin 4 → ℂ}
    {G : Fin 4 → Fin 4 → ℂ} (h : ∀ α β, Tendsto (fun i => F i α β) l (𝓝 (G α β)))
    (w u : Fin 4 → ℂ) :
    Tendsto (fun i => (1 / I) * (w ⬝ᵥ (Matrix.of (F i) *ᵥ u))) l
      (𝓝 ((1 / I) * (w ⬝ᵥ (Matrix.of G *ᵥ u)))) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
  exact (tendsto_finsetSum _ fun α _ => (tendsto_finsetSum _ fun β _ =>
    (h α β).mul_const (u β)).const_mul (w α)).const_mul _

/-- **The photon leg between two spinors as `ε → 0⁺`.** Under the hypotheses of
`QED.WickModel.tendsto_photonLeg`, `(1/i) w [photon-leg term] u` tends to
`(1/i) w [photonLegLimit] u`, for any row vector `w` and column vector `u`. -/
theorem tendsto_photonLeg_sandwich (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {q : Fin 4 → ℝ} (hq : -(4 * P.m ^ 2) < Minkowski.dot q q)
    (hqγ : Minkowski.dot q q ≠ -P.mγ ^ 2) (hqΛ : Minkowski.dot q q ≠ -P.Λ ^ 2)
    (μ : Fin 4) (w u : Fin 4 → ℂ) :
    Tendsto (fun ε : ℝ => (1 / I) * (w ⬝ᵥ (Matrix.of (fun α β => ∑ ν, ∑ ρ,
        (I * P.e) * Dirac.gamma ν α β *
        ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ ε q ν ρ) *
        onePIFunction { P with ε := ε } 0 2 2 ![] ![] ![q, -q] ![] ![] ![μ, ρ]) *ᵥ u)))
      (𝓝[>] 0) (𝓝 ((1 / I) * (w ⬝ᵥ (Matrix.of (photonLegLimit P q μ) *ᵥ u)))) :=
  tendsto_sandwich (fun α β =>
    tendsto_photonLeg_photonLegLimit P hm hM₁ hM₂ hPV₁ hPV₂ hq hqγ hqΛ μ α β) w u

/-! ### The limit in closed form -/

/-- The difference of the two photon poles at `ε = 0`,
`D(q) = 1/(q² + m_γ²) - 1/(q² + Λ²)`. -/
noncomputable abbrev LszPhotonLeg.poles (mγ Λ : ℝ) (q : Fin 4 → ℝ) : ℂ :=
  (((Minkowski.dot q q + mγ ^ 2 : ℝ) : ℂ))⁻¹ - (((Minkowski.dot q q + Λ ^ 2 : ℝ) : ℂ))⁻¹

/-- The photon propagator at `ε = 0` is `g_{νρ} D(q)`. -/
theorem LszPhotonLeg.photonPropagator_zero (mγ Λ : ℝ) (q : Fin 4 → ℝ) (ν ρ : Fin 4) :
    QED.OneLoop.photonPropagator mγ Λ 0 q ν ρ =
      ((Minkowski.metric ν ρ : ℝ) : ℂ) * LszPhotonLeg.poles mγ Λ q := by
  simp only [QED.OneLoop.photonPropagator, ofReal_zero, zero_mul, sub_zero]

/-- `g_{νρ} (q² g^{μρ} - q^μ q^ρ)` summed over `ρ` is `q² δ_ν^μ - q^μ q_ν`. -/
theorem LszPhotonLeg.sum_metric_mul (q : Fin 4 → ℝ) (μ ν : Fin 4) :
    ∑ ρ, Minkowski.metric ν ρ * (Minkowski.dot q q * Minkowski.metric μ ρ - q μ * q ρ) =
      Minkowski.dot q q * (if ν = μ then 1 else 0) - q μ * Minkowski.lower q ν := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  · rw [← Minkowski.metric_mul_metric, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Minkowski.metric_symm μ ρ]
    ring
  · rw [Minkowski.lower, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    ring

/-- **The limit of the photon leg in closed form**:
`photonLegLimit = i e D(q) Π(q²) (q² γ^μ - q^μ q̸)`, with `Π(s) = -δ₃ + Π_loop(s)`. -/
theorem photonLegLimit_eq_smul (P : Params) (q : Fin 4 → ℝ) (μ : Fin 4) :
    Matrix.of (photonLegLimit P q μ) =
      (I * P.e * LszPhotonLeg.poles P.mγ P.Λ q *
          (-(P.δ₃ : ℂ) + (vacuumPolarizationLoop P (Minkowski.dot q q) : ℂ))) •
        (((Minkowski.dot q q : ℝ) : ℂ) • Dirac.gamma μ - ((q μ : ℝ) : ℂ) • Dirac.slash q) := by
  ext α β
  set c := I * P.e * LszPhotonLeg.poles P.mγ P.Λ q *
    (-(P.δ₃ : ℂ) + (vacuumPolarizationLoop P (Minkowski.dot q q) : ℂ))
  have hterm : ∀ ν ρ, (I * P.e) * Dirac.gamma ν α β *
      ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ 0 q ν ρ) *
      (I * ((-(P.δ₃ : ℂ) + (vacuumPolarizationLoop P (Minkowski.dot q q) : ℂ)) *
        ((Minkowski.dot q q * Minkowski.metric μ ρ - q μ * q ρ : ℝ) : ℂ))) =
      c * (Dirac.gamma ν α β * ((Minkowski.metric ν ρ *
        (Minkowski.dot q q * Minkowski.metric μ ρ - q μ * q ρ) : ℝ) : ℂ)) := fun ν ρ => by
    rw [LszPhotonLeg.photonPropagator_zero]
    simp only [c]
    push_cast
    field_simp
  have hsum : ∀ ν, ∑ ρ, Dirac.gamma ν α β * ((Minkowski.metric ν ρ *
      (Minkowski.dot q q * Minkowski.metric μ ρ - q μ * q ρ) : ℝ) : ℂ) =
      Dirac.gamma ν α β * ((Minkowski.dot q q * (if ν = μ then 1 else 0) -
        q μ * Minkowski.lower q ν : ℝ) : ℂ) := fun ν => by
    rw [← LszPhotonLeg.sum_metric_mul, ← Finset.mul_sum, ofReal_sum]
  simp only [Matrix.of_apply, photonLegLimit, hterm, ← Finset.mul_sum, hsum, Matrix.smul_apply,
    Matrix.sub_apply, smul_eq_mul, Dirac.slash, Matrix.sum_apply]
  congr 1
  push_cast
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  · rw [Finset.sum_eq_single μ (fun ν _ hν => by simp [hν]) (fun h => absurd (Finset.mem_univ μ) h)]
    simp only [ite_true, ofReal_one, mul_one]
    ring
  · refine Finset.sum_congr rfl fun ν _ => ?_
    ring

/-- **The sandwiched limit in closed form.** For any row vector `w` and column vector `u`,
`(1/i) w [photonLegLimit] u = e D(q) Π(q²) (q² w γ^μ u - q^μ w q̸ u)`. -/
theorem sandwich_photonLegLimit (P : Params) (q : Fin 4 → ℝ) (μ : Fin 4) (w u : Fin 4 → ℂ) :
    (1 / I) * (w ⬝ᵥ (Matrix.of (photonLegLimit P q μ) *ᵥ u)) =
      P.e * LszPhotonLeg.poles P.mγ P.Λ q *
        (-(P.δ₃ : ℂ) + (vacuumPolarizationLoop P (Minkowski.dot q q) : ℂ)) *
        (((Minkowski.dot q q : ℝ) : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)) -
          ((q μ : ℝ) : ℂ) * (w ⬝ᵥ (Dirac.slash q *ᵥ u))) := by
  rw [photonLegLimit_eq_smul, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, dotProduct_smul, dotProduct_sub, dotProduct_smul, dotProduct_smul]
  simp only [smul_eq_mul]
  field_simp

/-! ### Continuity at the mass shell -/

/-- `ū(p') (p̸' - p̸) u(p) = 0` for spinors with `ū(p') (p̸' + m) = 0` and `(p̸ + m) u(p) = 0`. -/
theorem LszPhotonLeg.dotProduct_slash_sub_mulVec {m : ℝ} {p' p : Fin 4 → ℝ} {w u : Fin 4 → ℂ}
    (hw : w ᵥ* Dirac.slash p' = -((m : ℂ) • w)) (hu : Dirac.slash p *ᵥ u = -((m : ℂ) • u)) :
    w ⬝ᵥ (Dirac.slash (p' - p) *ᵥ u) = 0 := by
  have hs : Dirac.slash (p' - p) = Dirac.slash p' - Dirac.slash p := by
    rw [sub_eq_add_neg, Dirac.slash_add, ← neg_one_smul ℝ p, Dirac.slash_smul, ofReal_neg,
      ofReal_one, neg_one_smul, ← sub_eq_add_neg]
  rw [hs, Matrix.sub_mulVec, dotProduct_sub, Matrix.dotProduct_mulVec, hw, hu, neg_dotProduct,
    dotProduct_neg, smul_dotProduct, dotProduct_smul, sub_neg_eq_add, neg_add_cancel]

/-- Below threshold: an on-shell pair of positive energy has `(p' - p)² > -4m²`. -/
theorem LszPhotonLeg.neg_four_mul_sq_lt {m : ℝ} (hm : 0 < m) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) : -(4 * m ^ 2) < Minkowski.dot (p' - p) (p' - p) := by
  have h := Minkowski.dot_sub_self_nonneg_of_onShell hp' hp hp0' hp0
  have : 0 < m ^ 2 := by positivity
  linarith

/-- `x ↦ (x.1 - x.2)²` is continuous. -/
theorem LszPhotonLeg.continuous_dot_sub :
    Continuous fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) => Minkowski.dot (x.1 - x.2) (x.1 - x.2) :=
  LszLegs.continuous_dot_self.comp (continuous_fst.sub continuous_snd)

/-- **The photon-leg hypotheses hold near the mass shell.** For `m, m_γ, Λ > 0` and an on-shell
pair `(p', p)` of positive energy, `q = r' - r` lies below the pair threshold and off the photon
poles for all `(r', r)` near `(p', p)`. -/
theorem eventually_photonLeg_domain {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) :
    ∀ᶠ x : (Fin 4 → ℝ) × (Fin 4 → ℝ) in 𝓝 (p', p),
      -(4 * m ^ 2) < Minkowski.dot (x.1 - x.2) (x.1 - x.2) ∧
        Minkowski.dot (x.1 - x.2) (x.1 - x.2) ≠ -mγ ^ 2 ∧
        Minkowski.dot (x.1 - x.2) (x.1 - x.2) ≠ -Λ ^ 2 := by
  have h0 := Minkowski.dot_sub_self_nonneg_of_onShell hp' hp hp0' hp0
  have hc := LszPhotonLeg.continuous_dot_sub.tendsto (p', p)
  have h1 : -(4 * m ^ 2) < Minkowski.dot (p' - p) (p' - p) :=
    LszPhotonLeg.neg_four_mul_sq_lt hm hp' hp hp0' hp0
  have h2 : -mγ ^ 2 < Minkowski.dot (p' - p) (p' - p) := by
    have : 0 < mγ ^ 2 := by positivity
    linarith
  have h3 : -Λ ^ 2 < Minkowski.dot (p' - p) (p' - p) := by
    have : 0 < Λ ^ 2 := by positivity
    linarith
  filter_upwards [hc.eventually (lt_mem_nhds h1), hc.eventually (lt_mem_nhds h2),
    hc.eventually (lt_mem_nhds h3)] with x hx1 hx2 hx3
  exact ⟨hx1, hx2.ne', hx3.ne'⟩

/-- Continuity of the closed form at an on-shell `q₀` of nonnegative square. -/
theorem LszPhotonLeg.continuousAt_closedForm (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) {q₀ : Fin 4 → ℝ}
    (hq₀ : 0 ≤ Minkowski.dot q₀ q₀) (μ : Fin 4) (w u : Fin 4 → ℂ) :
    ContinuousAt (fun q : Fin 4 → ℝ => P.e * LszPhotonLeg.poles P.mγ P.Λ q *
        (-(P.δ₃ : ℂ) + (vacuumPolarizationLoop P (Minkowski.dot q q) : ℂ)) *
        (((Minkowski.dot q q : ℝ) : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)) -
          ((q μ : ℝ) : ℂ) * (w ⬝ᵥ (Dirac.slash q *ᵥ u)))) q₀ := by
  have hd : Continuous fun q : Fin 4 → ℝ => ((Minkowski.dot q q : ℝ) : ℂ) :=
    continuous_ofReal.comp LszLegs.continuous_dot_self
  have hpole : ∀ M : ℝ, 0 < M → ContinuousAt (fun q : Fin 4 → ℝ =>
      (((Minkowski.dot q q + M ^ 2 : ℝ) : ℂ))⁻¹) q₀ := fun M hM => by
    have hM2 : 0 < M ^ 2 := by positivity
    have hne : ((Minkowski.dot q₀ q₀ + M ^ 2 : ℝ) : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (ne_of_gt (by linarith))
    exact (continuous_ofReal.comp
      (LszLegs.continuous_dot_self.add continuous_const)).continuousAt.inv₀ hne
  have hPi : ContinuousAt (fun q : Fin 4 → ℝ =>
      ((vacuumPolarizationLoop P (Minkowski.dot q q) : ℝ) : ℂ)) q₀ := by
    have h4 : -(4 * P.m ^ 2) < Minkowski.dot q₀ q₀ := by
      have : 0 < P.m ^ 2 := by positivity
      linarith
    have h5 : ContinuousAt (fun q : Fin 4 → ℝ => vacuumPolarizationLoop P (Minkowski.dot q q))
        q₀ :=
      ContinuousAt.comp (g := vacuumPolarizationLoop P)
        (f := fun q : Fin 4 → ℝ => Minkowski.dot q q)
        ((continuousOn_vacuumPolarizationLoop hm hM₁ hM₂).continuousAt (Ioi_mem_nhds h4))
        LszLegs.continuous_dot_self.continuousAt
    exact continuous_ofReal.continuousAt.comp h5
  have hslash : Continuous fun q : Fin 4 → ℝ => w ⬝ᵥ (Dirac.slash q *ᵥ u) :=
    continuous_const.dotProduct (LszLegs.continuous_slash.matrix_mulVec continuous_const)
  have hqμ : Continuous fun q : Fin 4 → ℝ => ((q μ : ℝ) : ℂ) :=
    continuous_ofReal.comp (continuous_apply μ)
  exact ((continuousAt_const.mul ((hpole P.mγ hmγ).sub (hpole P.Λ hΛ))).mul
    (continuousAt_const.add hPi)).mul
    ((hd.mul continuous_const).sub (hqμ.mul hslash)).continuousAt

/-- **The photon leg at the mass shell.** For `m, m_γ, Λ > 0`, regulator fermions as in (Z₂),
an on-shell pair `(p', p)` of positive energy, a row vector `w` with `w (p̸' + m) = 0` and a
column vector `u` with `(p̸ + m) u = 0`, the sandwiched limit `(1/i) w [photonLegLimit] u` at
`q = r' - r` tends, as `(r', r) → (p', p)`, to
`e q₀² [1/(q₀² + m_γ²) - 1/(q₀² + Λ²)] Π(q₀²) w γ^μ u` with `q₀ = p' - p` and `Π` the sealed
vacuum polarization (Z₇). -/
theorem tendsto_photonLegLimit_sandwich_of_dirac (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ : Fin 4) {w u : Fin 4 → ℂ}
    (hw : w ᵥ* Dirac.slash p' = -((P.m : ℂ) • w)) (hu : Dirac.slash p *ᵥ u = -((P.m : ℂ) • u)) :
    Tendsto (fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
        (1 / I) * (w ⬝ᵥ (Matrix.of (photonLegLimit P (x.1 - x.2) μ) *ᵥ u)))
      (𝓝 (p', p))
      (𝓝 (P.e * ((Minkowski.dot (p' - p) (p' - p) : ℝ) : ℂ) *
        ((((Minkowski.dot (p' - p) (p' - p) + P.mγ ^ 2 : ℝ) : ℂ))⁻¹ -
          (((Minkowski.dot (p' - p) (p' - p) + P.Λ ^ 2 : ℝ) : ℂ))⁻¹) *
        vacuumPolarization P hm hM₁ hM₂ hPV₁ hPV₂
          ⟨_, LszPhotonLeg.neg_four_mul_sq_lt hm hp' hp hp0' hp0⟩ *
        (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)))) := by
  have h0 := Minkowski.dot_sub_self_nonneg_of_onShell hp' hp hp0' hp0
  set F : (Fin 4 → ℝ) → ℂ := fun q => P.e * LszPhotonLeg.poles P.mγ P.Λ q *
    (-(P.δ₃ : ℂ) + (vacuumPolarizationLoop P (Minkowski.dot q q) : ℂ)) *
    (((Minkowski.dot q q : ℝ) : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)) -
      ((q μ : ℝ) : ℂ) * (w ⬝ᵥ (Dirac.slash q *ᵥ u))) with hF
  have hc : ContinuousAt F (p' - p) :=
    LszPhotonLeg.continuousAt_closedForm P hm hmγ hΛ hM₁ hM₂ h0 μ w u
  have hlim : Tendsto (fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) => F (x.1 - x.2)) (𝓝 (p', p))
      (𝓝 (F (p' - p))) :=
    hc.tendsto.comp ((continuous_fst.sub continuous_snd).tendsto (p', p))
  have hfun : (fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      (1 / I) * (w ⬝ᵥ (Matrix.of (photonLegLimit P (x.1 - x.2) μ) *ᵥ u))) =
      fun x => F (x.1 - x.2) :=
    funext fun x => sandwich_photonLegLimit P (x.1 - x.2) μ w u
  have hval : F (p' - p) = P.e * ((Minkowski.dot (p' - p) (p' - p) : ℝ) : ℂ) *
      ((((Minkowski.dot (p' - p) (p' - p) + P.mγ ^ 2 : ℝ) : ℂ))⁻¹ -
        (((Minkowski.dot (p' - p) (p' - p) + P.Λ ^ 2 : ℝ) : ℂ))⁻¹) *
      vacuumPolarization P hm hM₁ hM₂ hPV₁ hPV₂
        ⟨_, LszPhotonLeg.neg_four_mul_sq_lt hm hp' hp hp0' hp0⟩ *
      (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)) := by
    rw [hF, vacuumPolarization_eq_loop]
    simp only [LszPhotonLeg.dotProduct_slash_sub_mulVec hw hu, mul_zero, sub_zero]
    ring
  rw [hfun, ← hval]
  exact hlim

/-- **The photon leg at the mass shell, on the spinors (38.7), (38.12).** The case
`w = ū_{s'}(p')`, `u = u_s(p)` of
`QED.WickModel.tendsto_photonLegLimit_sandwich_of_dirac`. -/
theorem tendsto_photonLegLimit_sandwich (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (s' s : Fin 2) (μ : Fin 4) :
    Tendsto (fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
        (1 / I) * (Dirac.bar (Dirac.spinor P.m p' s') ⬝ᵥ
          (Matrix.of (photonLegLimit P (x.1 - x.2) μ) *ᵥ Dirac.spinor P.m p s)))
      (𝓝 (p', p))
      (𝓝 (P.e * ((Minkowski.dot (p' - p) (p' - p) : ℝ) : ℂ) *
        ((((Minkowski.dot (p' - p) (p' - p) + P.mγ ^ 2 : ℝ) : ℂ))⁻¹ -
          (((Minkowski.dot (p' - p) (p' - p) + P.Λ ^ 2 : ℝ) : ℂ))⁻¹) *
        vacuumPolarization P hm hM₁ hM₂ hPV₁ hPV₂
          ⟨_, LszPhotonLeg.neg_four_mul_sq_lt hm hp' hp hp0' hp0⟩ *
        (Dirac.bar (Dirac.spinor P.m p' s') ⬝ᵥ (Dirac.gamma μ *ᵥ Dirac.spinor P.m p s)))) :=
  tendsto_photonLegLimit_sandwich_of_dirac P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hp' hp hp0' hp0 μ
    (Dirac.bar_vecMul_slash P.m p' _ (Dirac.slash_mulVec_spinor P.m p' hp' s'))
    (Dirac.slash_mulVec_spinor P.m p hp s)

end QED.WickModel

end
