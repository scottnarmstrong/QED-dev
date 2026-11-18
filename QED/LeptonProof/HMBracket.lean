/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.LeptonProof.HMValue

/-!
# The heavy-lepton bracket at finite regulators

Helper level, Phase 5 Stage 0 (decision D-50). With `P' = shiftP P H X` (photon counterterm
`δ₃ - ∑_ℓ π_ℓ`) and the auxiliary sets `Q_{ℓ j}`:

* `bracket_div_eq`: `[pauliZeroLimit P e - pauliZeroLimit P' e + ∑ w pauliZeroLimit Q e] / e⁴` is
  the same combination of the outer functionals `vpOuterF2` of the unit-charge, unit-mass
  parameters (the S, C, L, X units cancel);
* `bracket_outer_eq`: `16π⁴` times that combination is
  `∑_ℓ heavyUnitReg (m_ℓ/m) (m_γ/m) (Λ/m) (M_{ℓ,1}/m) (M_{ℓ,2}/m)`;
* `heavyBracket_eq`: the two together.
-/

@[expose] public section

open Complex Finset
open scoped Real
open QED.WickModel (Params vacuumPolarizationLoop)
open QED.TwoLoop.UnitsRegulated QED.TwoLoop.MassScaling QED.TwoLoop.UnitVPLink
open QED.TwoLoop.PauliZeroLimit QED.Chain.HeavyVP QED.TwoLoop.VPUnit

namespace QED.Lepton.Proof.HM

variable {n : ℕ} {H : Fin n → HeavyLepton} {X : Fin n → ℝ}

/-- **The shifted parameters**: the photon counterterm minus the heavy leptons' `Π(0)`. -/
noncomputable def shiftP (P : Params) (H : Fin n → HeavyLepton) (X : Fin n → ℝ) : Params :=
  { P with δ₃ := P.δ₃ - ∑ ℓ, heavyPi0 P (H ℓ) (X ℓ) }

theorem T1Adm.shift {P : Params} (hP : T1Adm P) (z : ℝ) : T1Adm { P with δ₃ := z } :=
  ⟨hP.hm, hP.hmγ, hP.hmΛ, hP.hm2, hP.hM₁, hP.hM₂, hP.pv₁, hP.pv₂⟩

theorem T1Adm.aux {P : Params} (hP : T1Adm P) (hok : AuxOK H X P.m) (hgt : AuxGt H X P.m)
    (ℓ : Fin n) (j : Fin 3) : T1Adm (auxParams P (H ℓ) (X ℓ) j) :=
  ⟨hP.hm, hP.hmγ, hP.hmΛ, hP.hm2, hgt.lt_mass ℓ j, hgt.lt_X ℓ, auxParams_PV₁ P (H ℓ) (X ℓ) j,
    auxParams_PV₂ P (H ℓ) j (hok.hX ℓ j)⟩

/-- The S, C, L and X units. -/
noncomputable def restUnits (Y : Params) : ℂ :=
  unitF2 .S Y + unitF2 .C Y + unitF2 .L Y + unitF2 .X Y

theorem sum_unitF2_eq (Y : Params) : ∑ U, unitF2 U Y = unitF2 .VP Y + restUnits Y := by
  have h : (Finset.univ : Finset TwoLoopUnit) = {.VP, .S, .C, .L, .X} := rfl
  rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [restUnits]
  ring

theorem restUnits_shift (P : Params) (z : ℝ) :
    restUnits (unitY { P with δ₃ := z }) = restUnits (unitY P) := rfl

theorem restUnits_shiftP (P : Params) (H : Fin n → HeavyLepton) (X : Fin n → ℝ) :
    restUnits (unitY (shiftP P H X)) = restUnits (unitY P) := rfl

theorem T1Adm.shiftP {P : Params} (hP : T1Adm P) (H : Fin n → HeavyLepton) (X : Fin n → ℝ) :
    T1Adm (shiftP P H X) := hP.shift _

theorem restUnits_aux (P : Params) (h : HeavyLepton) (Xa : ℝ) (j : Fin 3) :
    restUnits (unitY (auxParams P h Xa j)) = restUnits (unitY P) := rfl

theorem pauliZeroLimit_eq_units' {P X' : Params} (hX : T1Adm X') (he : P.e ≠ 0)
    (hXe : X'.e = P.e) :
    pauliZeroLimit X' P.e = (P.e : ℂ) ^ 4 * ∑ U, unitF2 U (unitY X') := by
  have h := pauliZeroLimit_div_eq_units hX (hXe ▸ he)
  rw [hXe] at h
  have he' : (P.e : ℂ) ^ 4 ≠ 0 := pow_ne_zero 4 (ofReal_ne_zero.mpr he)
  rw [(div_eq_iff he').mp h, mul_comm]

/-- **The bracket over `e⁴` is the combination of the outer functionals.** -/
theorem bracket_div_eq (P : Params) (hP : T1Adm P) (he : P.e ≠ 0) (hok : AuxOK H X P.m)
    (hgt : AuxGt H X P.m) :
    (pauliZeroLimit P P.e - pauliZeroLimit (shiftP P H X) P.e +
        ∑ ℓ, ∑ j, (auxWeight P (H ℓ) (X ℓ) j : ℂ) *
          pauliZeroLimit (auxParams P (H ℓ) (X ℓ) j) P.e) / (P.e : ℂ) ^ 4 =
      ((vpOuterF2 (unitY P) - vpOuterF2 (unitY (shiftP P H X)) +
        ∑ ℓ, ∑ j, auxWeight P (H ℓ) (X ℓ) j *
          vpOuterF2 (unitY (auxParams P (H ℓ) (X ℓ) j)) : ℝ) : ℂ) := by
  have he' : (P.e : ℂ) ^ 4 ≠ 0 := pow_ne_zero 4 (ofReal_ne_zero.mpr he)
  have hw : ∀ ℓ, ∑ j, (auxWeight P (H ℓ) (X ℓ) j : ℂ) = 0 := fun ℓ => by
    exact_mod_cast sum_auxWeight P (X ℓ) (hok.pv₁ ℓ) (hok.pv₂ ℓ)
  rw [pauliZeroLimit_eq_units' hP he rfl, pauliZeroLimit_eq_units' (hP.shiftP H X) he rfl]
  simp only [fun ℓ j => pauliZeroLimit_eq_units' (hP.aux hok hgt ℓ j) he rfl]
  simp only [sum_unitF2_eq, restUnits_shiftP, restUnits_aux, unitF2_VP_unitY hP,
    unitF2_VP_unitY (hP.shiftP H X), fun ℓ j => unitF2_VP_unitY (hP.aux hok hgt ℓ j)]
  have e1 : ∀ ℓ, ∑ j, (auxWeight P (H ℓ) (X ℓ) j : ℂ) * ((P.e : ℂ) ^ 4 *
      (((vpOuterF2 (unitY (auxParams P (H ℓ) (X ℓ) j)) : ℝ) : ℂ) + restUnits (unitY P))) =
      (P.e : ℂ) ^ 4 * ∑ j, (auxWeight P (H ℓ) (X ℓ) j : ℂ) *
        ((vpOuterF2 (unitY (auxParams P (H ℓ) (X ℓ) j)) : ℝ) : ℂ) := fun ℓ => by
    rw [mul_sum]
    have : ∀ j, (auxWeight P (H ℓ) (X ℓ) j : ℂ) * ((P.e : ℂ) ^ 4 *
        (((vpOuterF2 (unitY (auxParams P (H ℓ) (X ℓ) j)) : ℝ) : ℂ) + restUnits (unitY P))) =
        (P.e : ℂ) ^ 4 * ((auxWeight P (H ℓ) (X ℓ) j : ℂ) *
          ((vpOuterF2 (unitY (auxParams P (H ℓ) (X ℓ) j)) : ℝ) : ℂ)) +
          ((P.e : ℂ) ^ 4 * restUnits (unitY P)) * (auxWeight P (H ℓ) (X ℓ) j : ℂ) :=
      fun j => by ring
    rw [sum_congr rfl fun j _ => this j, sum_add_distrib, ← mul_sum, ← mul_sum, hw, mul_zero,
      add_zero]
  simp only [e1, ← mul_sum]
  push_cast
  have he1 : (P.e : ℂ) ≠ 0 := ofReal_ne_zero.mpr he
  field_simp
  ring

/-! ### The heavy unit -/

/-- **The heavy lepton's measure applied to `vpFlavour`** is the heavy VP unit `heavyUnitReg`
(the coefficients are the Pauli–Villars ones of the lepton's mass). -/
theorem sum_hCoeff_vpFlavour {h : HeavyLepton} (hpos : 0 < h.m) (h2 : h.m < h.M₂)
    (pv₁ : 1 + h.c₁ + h.c₂ = 0) (pv₂ : h.m ^ 2 + h.c₁ * h.M₁ ^ 2 + h.c₂ * h.M₂ ^ 2 = 0)
    {t : ℝ} (ht : 0 < t) (mγ Λ : ℝ) :
    ∑ j, hCoeff h j * vpFlavour (t * hMass h j) mγ Λ =
      heavyUnitReg (t * h.m) mγ Λ (t * h.M₁) (t * h.M₂) := by
  have pv₂' : (t * h.m) ^ 2 + h.c₁ * (t * h.M₁) ^ 2 + h.c₂ * (t * h.M₂) ^ 2 = 0 := by
    linear_combination t ^ 2 * pv₂
  have hne := sq_ne_sq_of_pvL (mul_pos ht hpos) (mul_lt_mul_of_pos_left h2 ht) pv₁ pv₂'
  obtain ⟨e1, e2⟩ := pvL_unique hne pv₁ pv₂'
  simp only [Fin.sum_univ_three, hCoeff, hMass, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_mul, heavyUnitReg, ← e1, ← e2]

/-- **The outer combination is the sum of the heavy VP units.** -/
theorem bracket_outer_eq (P : Params) (hP : T1Adm P) (he : P.e ≠ 0) (hok : AuxOK H X P.m)
    (hgt : AuxGt H X P.m) (hH₂ : ∀ ℓ, (H ℓ).m < (H ℓ).M₂) :
    16 * π ^ 4 * (vpOuterF2 (unitY P) - vpOuterF2 (unitY (shiftP P H X)) +
        ∑ ℓ, ∑ j, auxWeight P (H ℓ) (X ℓ) j * vpOuterF2 (unitY (auxParams P (H ℓ) (X ℓ) j))) =
      ∑ ℓ, heavyUnitReg (P.m⁻¹ * (H ℓ).m) (unitY P).mγ (unitY P).Λ (P.m⁻¹ * (H ℓ).M₁)
        (P.m⁻¹ * (H ℓ).M₂) := by
  set B := outerB (unitY P) with hB
  set S : Fin n → Fin 3 → ℝ := fun ℓ j => outerSub (unitY (auxParams P (H ℓ) (X ℓ) j)) with hS
  have hw : ∀ ℓ, ∑ j, auxWeight P (H ℓ) (X ℓ) j = 0 := fun ℓ =>
    sum_auxWeight P (X ℓ) (hok.pv₁ ℓ) (hok.pv₂ ℓ)
  have hQ : ∀ ℓ j, auxWeight P (H ℓ) (X ℓ) j * vpOuterF2 (unitY (auxParams P (H ℓ) (X ℓ) j)) =
      auxWeight P (H ℓ) (X ℓ) j * S ℓ j +
        (auxWeight P (H ℓ) (X ℓ) j * vacuumPolarizationLoop (auxParams P (H ℓ) (X ℓ) j) 0) *
          (B / P.e ^ 2) - (P.δ₃ / P.e ^ 2 * B) * auxWeight P (H ℓ) (X ℓ) j := by
    intro ℓ j
    have hQa := hP.aux hok hgt ℓ j
    rw [vpOuterF2_unitY_eq hQa, outerA_unitY_eq hQa, vacuumPolarizationLoop_unitY_zero hQa he]
    have e1 : (unitY (auxParams P (H ℓ) (X ℓ) j)).δ₃ = P.δ₃ / P.e ^ 2 := rfl
    have e2 : outerB (unitY (auxParams P (H ℓ) (X ℓ) j)) = B := rfl
    have e3 : (auxParams P (H ℓ) (X ℓ) j).e = P.e := rfl
    rw [e1, e2, e3]
    ring
  have hP0 : vpOuterF2 (unitY P) = outerA (unitY P) - P.δ₃ / P.e ^ 2 * B :=
    vpOuterF2_unitY_eq hP
  have hP1 : vpOuterF2 (unitY (shiftP P H X)) = outerA (unitY P) -
      (P.δ₃ - ∑ ℓ, heavyPi0 P (H ℓ) (X ℓ)) / P.e ^ 2 * B :=
    vpOuterF2_unitY_eq (hP.shiftP H X)
  have hsum : ∑ ℓ, ∑ j, auxWeight P (H ℓ) (X ℓ) j * vpOuterF2 (unitY (auxParams P (H ℓ) (X ℓ) j))
      = ∑ ℓ, ∑ j, auxWeight P (H ℓ) (X ℓ) j * S ℓ j +
        (∑ ℓ, heavyPi0 P (H ℓ) (X ℓ)) * (B / P.e ^ 2) := by
    simp only [hQ, sum_add_distrib, sum_sub_distrib, ← mul_sum, hw, mul_zero, sub_zero, ← sum_mul,
      heavyPi0]
  have hS16 : ∀ ℓ j, 16 * π ^ 4 * S ℓ j = ∑ i, (auxParams P (H ℓ) (X ℓ) j).loopCoeff i *
      vpFlavour (P.m⁻¹ * (auxParams P (H ℓ) (X ℓ) j).mass i) (unitY P).mγ (unitY P).Λ :=
    fun ℓ j => outerSub_unitY (hP.aux hok hgt ℓ j)
  rw [hsum, hP0, hP1]
  have e4 : 16 * π ^ 4 * (outerA (unitY P) - P.δ₃ / P.e ^ 2 * B -
      (outerA (unitY P) - (P.δ₃ - ∑ ℓ, heavyPi0 P (H ℓ) (X ℓ)) / P.e ^ 2 * B) +
        (∑ ℓ, ∑ j, auxWeight P (H ℓ) (X ℓ) j * S ℓ j +
          (∑ ℓ, heavyPi0 P (H ℓ) (X ℓ)) * (B / P.e ^ 2))) =
      ∑ ℓ, ∑ j, auxWeight P (H ℓ) (X ℓ) j * (16 * π ^ 4 * S ℓ j) := by
    have hR : ∑ ℓ, ∑ j, auxWeight P (H ℓ) (X ℓ) j * (16 * π ^ 4 * S ℓ j) =
        16 * π ^ 4 * ∑ ℓ, ∑ j, auxWeight P (H ℓ) (X ℓ) j * S ℓ j := by
      rw [mul_sum]
      refine sum_congr rfl fun ℓ _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      ring
    rw [hR]
    have hpe : P.e ^ 2 ≠ 0 := pow_ne_zero 2 he
    field_simp
    ring
  rw [e4]
  refine sum_congr rfl fun ℓ _ => ?_
  simp only [hS16]
  have key := sum_auxWeight_loop (M := ℝ) P (hok.pv₁ ℓ) (hok.pv₂ ℓ) (hok.hXm ℓ) (hok.hX ℓ)
    (fun b => vpFlavour (P.m⁻¹ * b) (unitY P).mγ (unitY P).Λ)
  simp only [smul_eq_mul] at key
  rw [key, ← sum_hCoeff_vpFlavour (hP.hm.trans (hgt.lt_mass ℓ 0)) (hH₂ ℓ) (hok.pv₁ ℓ)
    (hok.pv₂ ℓ) (inv_pos.mpr hP.hm)]

/-- **The heavy-lepton bracket at finite regulators.** -/
theorem heavyBracket_eq (P : Params) (hP : T1Adm P) (he : P.e ≠ 0) (hok : AuxOK H X P.m)
    (hgt : AuxGt H X P.m) (hH₂ : ∀ ℓ, (H ℓ).m < (H ℓ).M₂) :
    16 * (π : ℂ) ^ 4 * ((pauliZeroLimit P P.e - pauliZeroLimit (shiftP P H X) P.e +
        ∑ ℓ, ∑ j, (auxWeight P (H ℓ) (X ℓ) j : ℂ) *
          pauliZeroLimit (auxParams P (H ℓ) (X ℓ) j) P.e) / (P.e : ℂ) ^ 4) =
      ((∑ ℓ, heavyUnitReg ((H ℓ).m / P.m) (P.mγ / P.m) (P.Λ / P.m) ((H ℓ).M₁ / P.m)
        ((H ℓ).M₂ / P.m) : ℝ) : ℂ) := by
  rw [bracket_div_eq P hP he hok hgt]
  have h := bracket_outer_eq P hP he hok hgt hH₂
  have e1 : (unitY P).mγ = P.mγ / P.m := unitMass_mγ P
  have e2 : (unitY P).Λ = P.Λ / P.m := unitMass_Λ P
  simp only [e1, e2, ← div_eq_inv_mul] at h
  rw [← h]
  push_cast
  ring

end QED.Lepton.Proof.HM

end
