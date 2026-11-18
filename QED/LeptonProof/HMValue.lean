/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.LeptonProof.HMPhoton
public import QED.Chain.HeavyVPOuter
public import QED.TwoLoop.UnitsRegulated
public import QED.TwoLoop.MassScalingUnits
public import QED.TwoLoop.UnitVPClose
import QED.TwoLoop.VPUnitNested
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The heavy-lepton part of the regulated coefficient at finite regulators

Helper level, Phase 5 Stage 0 (decision D-50). The order-`e⁵` vertex of the multi-lepton model is
T1's vertex at the shifted photon counterterm plus a finite combination of T1 vertices
(`QED/LeptonProof/HMVertex.lean`, `QED/LeptonProof/HMPhoton.lean`):

`V_L(P) = V_T1(P') + [V_T1(P) - V_T1(P') + ∑_ℓ ∑_j w_{ℓ j} V_T1(Q_{ℓ j})]`,

with `P' = {P with δ₃ := δ₃ - ∑_ℓ π_ℓ}` and `Q_{ℓ j} = auxParams P (H ℓ) (X ℓ) j`. This file
computes the `q² → 0` value of the bracket from T1's units (decisions D-41, D-43):

* `pauliZeroLimit_div_eq_units`: for every admissible T1 parameter set, `pauliZeroLimit X e / e⁴`
  is the sum of the five units at unit charge and unit mass;
* the S, C, L and X units do not see the regulator fermions or `δ₃`, so they cancel in the
  bracket (the weights sum to `0`);
* the VP unit is the outer functional of the subtracted `Π` (T1's nested form, proved), and the
  bracket's VP units combine into each heavy lepton's own subtracted `Π`;

so (`heavyBracket_eq`)

`16π⁴ [pauliZeroLimit P e - pauliZeroLimit P' e + ∑ w pauliZeroLimit Q e] / e⁴
  = ∑_ℓ heavyUnitReg (m_ℓ/m) (m_γ/m) (Λ/m) (M_{ℓ,1}/m) (M_{ℓ,2}/m)`,

the explicit heavy VP unit of `QED/Chain/HeavyVPUnit.lean`, whose regulator limit is `a2Heavy`.
-/

@[expose] public section

open Complex Finset
open scoped Real
open QED.WickModel (Params vacuumPolarizationLoop)
open QED.TwoLoop.UnitsRegulated QED.TwoLoop.MassScaling QED.TwoLoop.UnitVPLink
open QED.TwoLoop.PauliZeroLimit QED.Chain.HeavyVP QED.TwoLoop.VPUnit

namespace QED.Lepton.Proof.HM

/-! ### Admissible T1 parameter sets at unit charge and unit mass -/

/-- The conditions on a T1 parameter set used at fixed regulators. -/
structure T1Adm (X : Params) : Prop where
  hm : 0 < X.m
  hmγ : 0 < X.mγ
  hmΛ : X.mγ < X.Λ
  hm2 : X.mγ < 2 * X.m
  hM₁ : X.m < X.M₁
  hM₂ : X.m < X.M₂
  pv₁ : 1 + X.c₁ + X.c₂ = 0
  pv₂ : X.m ^ 2 + X.c₁ * X.M₁ ^ 2 + X.c₂ * X.M₂ ^ 2 = 0

/-- The parameters of `X` at unit charge and unit mass, with counterterms `δᵢ/e²`. -/
noncomputable def unitY (X : Params) : Params :=
  atUnitCharge (unitMass X) (X.δ₁ / X.e ^ 2) (X.δ₂ / X.e ^ 2) (X.δm / X.e ^ 2) (X.δ₃ / X.e ^ 2)

section Unit

variable {X : Params} (hX : T1Adm X)
include hX

theorem unitMass_m_eq : (unitMass X).m = 1 := unitMass_m hX.hm.ne'

theorem unitMass_lt_M₁ : 1 < (unitMass X).M₁ := by
  rw [unitMass_M₁, lt_div_iff₀ hX.hm, one_mul]
  exact hX.hM₁

theorem unitMass_lt_M₂ : 1 < (unitMass X).M₂ := by
  rw [unitMass_M₂, lt_div_iff₀ hX.hm, one_mul]
  exact hX.hM₂

theorem unitMass_mγ_pos : 0 < (unitMass X).mγ := by
  rw [unitMass_mγ]
  exact div_pos hX.hmγ hX.hm

theorem unitMass_mγ_lt_Λ : (unitMass X).mγ < (unitMass X).Λ := by
  rw [unitMass_mγ, unitMass_Λ]
  exact div_lt_div_of_pos_right hX.hmΛ hX.hm

theorem unitMass_mγ_lt_two : (unitMass X).mγ < 2 := by
  rw [unitMass_mγ, div_lt_iff₀ hX.hm]
  exact hX.hm2

theorem unitMass_pv₂ :
    (unitMass X).m ^ 2 + (unitMass X).c₁ * (unitMass X).M₁ ^ 2 +
      (unitMass X).c₂ * (unitMass X).M₂ ^ 2 = 0 := by
  simp only [unitMass, massScale_m, massScale_c₁, massScale_c₂, massScale_M₁, massScale_M₂]
  linear_combination X.m⁻¹ ^ 2 * hX.pv₂

/-- **`pauliZeroLimit / e⁴` as the sum of the units at unit charge and unit mass.** -/
theorem pauliZeroLimit_div_eq_units (he : X.e ≠ 0) :
    pauliZeroLimit X X.e / (X.e : ℂ) ^ 4 = ∑ U, unitF2 U (unitY X) := by
  have hd : ∀ δ : ℝ, δ = X.e ^ 2 * (δ / X.e ^ 2) := fun δ => by
    have : X.e ^ 2 ≠ 0 := pow_ne_zero 2 he
    field_simp
  rw [pauliZeroLimit_div_pow_four X (hd X.δ₁) (hd X.δ₂) (hd X.δm) (hd X.δ₃) hX.hm hX.hmγ
      (hX.hmγ.trans hX.hmΛ) hX.hM₁.le hX.hM₂.le hX.pv₁ hX.pv₂ he,
    pauliZeroFour_eq_unitMass X hX.hm hX.hmγ (hX.hmγ.trans hX.hmΛ) hX.hM₁.le hX.hM₂.le hX.pv₁
      hX.pv₂]
  have hm1 := unitMass_m_eq hX
  rw [pauliZeroFour_eq_sum_units (unitMass X) (by rw [hm1]; exact one_pos) (unitMass_mγ_pos hX)
    ((unitMass_mγ_pos hX).trans (unitMass_mγ_lt_Λ hX)) (by rw [hm1]; exact (unitMass_lt_M₁ hX).le)
    (by rw [hm1]; exact (unitMass_lt_M₂ hX).le) hX.pv₁ (unitMass_pv₂ hX)]
  rfl

/-- **The VP unit is the outer functional** (T1's nested form). -/
theorem unitF2_VP_unitY : unitF2 .VP (unitY X) = ((vpOuterF2 (unitY X) : ℝ) : ℂ) :=
  QED.TwoLoop.UnitVPClose.vpUnitNested_atUnitCharge (unitMass X) (unitMass_m_eq hX)
    (unitMass_lt_M₁ hX) (unitMass_lt_M₂ hX) (unitMass_mγ_pos hX) (unitMass_mγ_lt_Λ hX)
    (unitMass_mγ_lt_two hX) hX.pv₁ (unitMass_pv₂ hX) _ _ _ _

/-- The outer integrand of `Π_loop s D²` at unit mass is integrable. -/
theorem intervalIntegrable_outer_loop_unitY :
    IntervalIntegrable (fun x => x ^ 2 * (vacuumPolarizationLoop (unitY X) (photonVar x) *
      photonVar x * photonD (unitY X).mγ (unitY X).Λ (photonVar x) ^ 2))
      MeasureTheory.volume 0 1 :=
  QED.TwoLoop.VPUnitNested.intervalIntegrable_outer_loop (unitY X) (unitMass_m_eq hX)
    (unitMass_lt_M₁ hX) (unitMass_lt_M₂ hX) (unitMass_mγ_pos hX) (unitMass_mγ_lt_Λ hX)
    (unitMass_mγ_lt_two hX)

end Unit

/-! ### Linearity of the outer functional -/

theorem outerF2_add {f g : ℝ → ℝ}
    (hf : IntervalIntegrable (fun x => x ^ 2 * f (photonVar x)) MeasureTheory.volume 0 1)
    (hg : IntervalIntegrable (fun x => x ^ 2 * g (photonVar x)) MeasureTheory.volume 0 1) :
    outerF2 (fun s => f s + g s) = outerF2 f + outerF2 g := by
  unfold outerF2
  rw [← mul_add, ← intervalIntegral.integral_add hf hg]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only
  ring

theorem outerF2_const_mul (c : ℝ) (f : ℝ → ℝ) :
    outerF2 (fun s => c * f s) = c * outerF2 f := by
  unfold outerF2
  have : (fun x => x ^ 2 * (c * f (photonVar x))) = fun x => c * (x ^ 2 * f (photonVar x)) := by
    funext x
    ring
  rw [this, intervalIntegral.integral_const_mul]
  ring

theorem outerF2_congr {f g : ℝ → ℝ} (h : ∀ s, f s = g s) : outerF2 f = outerF2 g := by
  rw [funext h]

/-! ### The decomposition of `vpOuterF2` -/

/-- The outer functional of `Π_loop s D²`. -/
noncomputable def outerA (Y : Params) : ℝ :=
  outerF2 fun s => vacuumPolarizationLoop Y s * s * photonD Y.mγ Y.Λ s ^ 2

/-- The outer functional of `s D²`. -/
noncomputable def outerB (Y : Params) : ℝ :=
  outerF2 fun s => s * photonD Y.mγ Y.Λ s ^ 2

theorem intervalIntegrable_outer_sD2' {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (c : ℝ) :
    IntervalIntegrable (fun x => x ^ 2 * (c * (photonVar x * photonD a b (photonVar x) ^ 2)))
      MeasureTheory.volume 0 1 := by
  refine (QED.TwoLoop.VPUnitNested.intervalIntegrable_outer_sD2 ha hb c).congr fun x _ => ?_
  ring

theorem vpOuterF2_unitY_eq {X : Params} (hX : T1Adm X) :
    vpOuterF2 (unitY X) = outerA (unitY X) - (unitY X).δ₃ * outerB (unitY X) := by
  have hγ : 0 < (unitY X).mγ := unitMass_mγ_pos hX
  have hΛ : 0 < (unitY X).Λ := hγ.trans (unitMass_mγ_lt_Λ hX)
  unfold vpOuterF2 outerA outerB
  rw [outerF2_congr fun s => show (vacuumPolarizationLoop (unitY X) s - (unitY X).δ₃) * s *
      photonD (unitY X).mγ (unitY X).Λ s ^ 2 = vacuumPolarizationLoop (unitY X) s * s *
        photonD (unitY X).mγ (unitY X).Λ s ^ 2 + (-(unitY X).δ₃) * (s *
          photonD (unitY X).mγ (unitY X).Λ s ^ 2) by ring,
    outerF2_add (intervalIntegrable_outer_loop_unitY hX)
      (intervalIntegrable_outer_sD2' hγ hΛ _), outerF2_const_mul]
  ring

/-- The subtracted outer functional `outerF2 ((Π(s) - Π(0)) s D²)`. -/
noncomputable def outerSub (Y : Params) : ℝ :=
  outerF2 fun s => (vacuumPolarizationLoop Y s - vacuumPolarizationLoop Y 0) * s *
    photonD Y.mγ Y.Λ s ^ 2

theorem outerA_unitY_eq {X : Params} (hX : T1Adm X) :
    outerA (unitY X) =
      outerSub (unitY X) + vacuumPolarizationLoop (unitY X) 0 * outerB (unitY X) := by
  have hγ : 0 < (unitY X).mγ := unitMass_mγ_pos hX
  have hΛ : 0 < (unitY X).Λ := hγ.trans (unitMass_mγ_lt_Λ hX)
  have h1 := intervalIntegrable_outer_loop_unitY hX
  have h2 := intervalIntegrable_outer_sD2' hγ hΛ (vacuumPolarizationLoop (unitY X) 0)
  have h3 : IntervalIntegrable (fun x => x ^ 2 * ((vacuumPolarizationLoop (unitY X) (photonVar x)
      - vacuumPolarizationLoop (unitY X) 0) * photonVar x *
        photonD (unitY X).mγ (unitY X).Λ (photonVar x) ^ 2)) MeasureTheory.volume 0 1 := by
    refine (h1.sub h2).congr fun x _ => ?_
    ring
  unfold outerA outerSub outerB
  rw [outerF2_congr fun s => show vacuumPolarizationLoop (unitY X) s * s *
      photonD (unitY X).mγ (unitY X).Λ s ^ 2 = (vacuumPolarizationLoop (unitY X) s -
        vacuumPolarizationLoop (unitY X) 0) * s * photonD (unitY X).mγ (unitY X).Λ s ^ 2 +
          vacuumPolarizationLoop (unitY X) 0 * (s * photonD (unitY X).mγ (unitY X).Λ s ^ 2) by
      ring, outerF2_add h3 h2, outerF2_const_mul]

/-- The masses at unit mass are the masses divided by `m`. -/
theorem unitY_mass (X : Params) (f : Fin 3) : (unitY X).mass f = X.m⁻¹ * X.mass f := by
  fin_cases f <;> rfl

theorem unitY_loopCoeff (X : Params) : (unitY X).loopCoeff = X.loopCoeff := rfl

theorem mass_pos_of_adm {X : Params} (hX : T1Adm X) (f : Fin 3) : 0 < X.mass f := by
  fin_cases f
  · exact hX.hm
  · exact hX.hm.trans hX.hM₁
  · exact hX.hm.trans hX.hM₂

theorem one_le_unitY_mass {X : Params} (hX : T1Adm X) (f : Fin 3) : 1 ≤ (unitY X).mass f := by
  rw [unitY_mass, ← div_eq_inv_mul, le_div_iff₀ hX.hm, one_mul]
  fin_cases f
  · exact le_rfl
  · exact hX.hM₁.le
  · exact hX.hM₂.le

/-- **The subtracted outer functional at unit mass** is the flavour sum of `vpFlavour`. -/
theorem outerSub_unitY {X : Params} (hX : T1Adm X) :
    16 * π ^ 4 * outerSub (unitY X) =
      ∑ i, X.loopCoeff i * vpFlavour (X.m⁻¹ * X.mass i) (unitY X).mγ (unitY X).Λ := by
  have hγ := unitMass_mγ_pos hX
  have hmΛ := unitMass_mγ_lt_Λ hX
  have h2 := unitMass_mγ_lt_two hX
  have hmass : ∀ f, (unitY X).mass f ≠ 0 := fun f =>
    (zero_lt_one.trans_le (one_le_unitY_mass hX f)).ne'
  have hm2 : ∀ f, (unitY X).mγ ^ 2 < 4 * (unitY X).mass f ^ 2 := fun f => by
    have h1 := one_le_unitY_mass hX f
    have h2' : (unitY X).mγ < 2 := h2
    have hγ' : 0 < (unitY X).mγ := hγ
    nlinarith
  have key := outerF2_flavourPi_sub (e := 1) (coeff := (unitY X).loopCoeff) hmass hγ hmΛ hm2
  rw [one_pow, one_mul] at key
  simp only [unitY_mass, unitY_loopCoeff] at key
  exact key

/-- **`Π(0)` at unit charge and unit mass** is `Π(0)/e²` (the masses rescale by a common factor
and `∑ c_f = 0`). -/
theorem vacuumPolarizationLoop_unitY_zero {X : Params} (hX : T1Adm X) (he : X.e ≠ 0) :
    vacuumPolarizationLoop (unitY X) 0 = vacuumPolarizationLoop X 0 / X.e ^ 2 := by
  have hpos := mass_pos_of_adm hX
  have hm := hX.hm
  have hsum : ∑ f, X.loopCoeff f = 0 := by
    simp [Fin.sum_univ_three, QED.WickModel.Params.loopCoeff, ← hX.pv₁, add_assoc]
  have hlog : ∀ x : ℝ, ∑ f, (unitY X).loopCoeff f *
      Real.log (QED.WickModel.vacuumPolarizationFeynmanMass ((unitY X).mass f) 0 x) =
      ∑ f, X.loopCoeff f *
        Real.log (QED.WickModel.vacuumPolarizationFeynmanMass (X.mass f) 0 x) := by
    intro x
    simp only [QED.WickModel.vacuumPolarizationFeynmanMass, mul_zero, add_zero, unitY_mass,
      unitY_loopCoeff, mul_pow]
    have e1 : ∀ f, Real.log (X.m⁻¹ ^ 2 * X.mass f ^ 2) =
        Real.log (X.m⁻¹ ^ 2) + Real.log (X.mass f ^ 2) := fun f =>
      Real.log_mul (by positivity) (pow_ne_zero 2 (hpos f).ne')
    simp only [e1, mul_add, sum_add_distrib, ← sum_mul, hsum, zero_mul, zero_add]
  unfold vacuumPolarizationLoop
  simp only [hlog]
  have he1 : (unitY X).e = 1 := rfl
  rw [he1]
  have : X.e ^ 2 ≠ 0 := pow_ne_zero 2 he
  field_simp

end QED.Lepton.Proof.HM

end
