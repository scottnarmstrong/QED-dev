/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispMain
public import QED.TwoLoop.UnitSCCtAssembly
public import QED.TwoLoop.MassScalingUnits
import QED.TwoLoop.UnitSCCtJet
import QED.TwoLoop.UnitSCCtJetOut
import QED.TwoLoop.MassScalingCt

/-!
# Set (c): the explicit values of the five VP-share classes, linear in the share

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS` of
`QED.ChainProof.SetCRegDisp.setCRegLimitDisp_of_pieces`. The value of the VP-share class `Sₖ` is
`ctZero (sCls k) Q / (64 e m⁵)` at `Q = sParams …`, the one-loop parameters whose fermion
counterterms are `δᵢ = e⁴ sᵢ` (the share `s`). This file evaluates the three counterterm-class
values in closed form, for every charge `e`, mass `m > 0` and `0 < m_γ < Λ`:

* `d2InZero_eq`, `d2OutZero_eq`: `d2InZero Q = d2OutZero Q =
  16 i e³ m⁵ (δ₂ ΔV_k + δ_m ΔV_m)/π²`, with `ΔV_k = V_k(m_γ/m) - V_k(Λ/m)`,
  `ΔV_m = V_m(m_γ/m) - V_m(Λ/m)` (`QED.TwoLoop.UnitSCClose.selfVk`, `selfVm`). The charge is
  absorbed into the counterterms (`chargeOne`: the numerator is cubic in `e` and linear in
  `δ₂, δ_m`), the mass is scaled to `1` (`QED.TwoLoop.MassScaling.unitMass`), and the unit value
  is `QED.TwoLoop.UnitSCCt.d2InZero_eq_of_pointwise` with `d2Pointwise_In`, `d2Pointwise_Out`;
* `d1Zero` is `i δ₁ e (4m²)³ (e²/(8π²)) B(0)/m` by definition.

Hence the class values are linear in the share (`ctPauliAll_S_line`, `ctPauliAll_S_vtx`):
`Sₖ = i e²/(4π²) (ΔV_k e⁴s₂ + ΔV_m e⁴s_m)` for `k = 0, 1` (`δ₂, δ_m` on a line, `sCoefLine`) and
`Sₖ = i e² B(0)/(8π²) e⁴s₁` for `k = 2, 3, 4` (`δ₁` at a vertex, `sCoefVtx`, `B(0) = sPauliB0`).
-/

@[expose] public section

open Complex Real Set
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCPauli
open QED.ChainProof.SetAPauli (regParams regFlavors)
open QED.TwoLoop.PauliZeroExplicit (d2InZero d2OutZero d1Zero ctZero oneLoopPauliZero)
open QED.TwoLoop.CountertermLimit (numD2In numD2Out)
open QED.TwoLoop.Insertion (vertexChain fermionCtMatrix)
open QED.TwoLoop.MassScaling (unitMass massScale)
open QED.TwoLoop.UnitSCClose (selfVk selfVm)

/-! ### The charge absorbed into the counterterms -/

/-- The parameters at charge `1` with the fermion counterterms multiplied by `e³`. -/
def chargeOne (P : Params) : Params :=
  { P with e := 1, δ₂ := P.e ^ 3 * P.δ₂, δm := P.e ^ 3 * P.δm }

theorem fermionCtMatrix_mul (c δ₂ δm m : ℝ) (k : Fin 4 → ℝ) :
    fermionCtMatrix (c * δ₂) (c * δm) m k = (c : ℂ) • fermionCtMatrix δ₂ δm m k := by
  ext i j
  simp only [fermionCtMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem vertexChain_charge_in (e : ℝ) (μ : Fin 4) (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (D : Fin 4 → Fin 4 → ℂ) : vertexChain e μ A B D = vertexChain 1 μ A ((e : ℂ) ^ 3 • B) D := by
  simp only [vertexChain, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, smul_smul]
  congr 1
  funext ν
  congr 1
  funext ρ
  congr 1
  push_cast
  ring

theorem vertexChain_charge_out (e : ℝ) (μ : Fin 4) (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (D : Fin 4 → Fin 4 → ℂ) : vertexChain e μ A B D = vertexChain 1 μ ((e : ℂ) ^ 3 • A) B D := by
  simp only [vertexChain, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, smul_smul]
  congr 1
  funext ν
  congr 1
  funext ρ
  congr 1
  push_cast
  ring

theorem numD2In_chargeOne (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) (k : Fin 4 → ℝ) :
    numD2In P p' p μ k = numD2In (chargeOne P) p' p μ k := by
  simp only [numD2In, chargeOne]
  rw [vertexChain_charge_in, fermionCtMatrix_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]
  push_cast
  rfl

theorem numD2Out_chargeOne (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) (k : Fin 4 → ℝ) :
    numD2Out P p' p μ k = numD2Out (chargeOne P) p' p μ k := by
  simp only [numD2Out, chargeOne]
  rw [vertexChain_charge_out, fermionCtMatrix_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]
  push_cast
  rfl

theorem d2InZero_chargeOne (P : Params) : d2InZero P = d2InZero (chargeOne P) := by
  have e : (fun p' μ k => numD2In P p' (QED.TwoLoop.PauliZero.restMomentum P.m) μ k) =
      fun p' μ k => numD2In (chargeOne P) p' (QED.TwoLoop.PauliZero.restMomentum P.m) μ k := by
    funext p' μ k
    exact numD2In_chargeOne P _ _ μ k
  unfold d2InZero
  rw [e]
  rfl

theorem d2OutZero_chargeOne (P : Params) : d2OutZero P = d2OutZero (chargeOne P) := by
  have e : (fun p' μ k => numD2Out P p' (QED.TwoLoop.PauliZero.restMomentum P.m) μ k) =
      fun p' μ k => numD2Out (chargeOne P) p' (QED.TwoLoop.PauliZero.restMomentum P.m) μ k := by
    funext p' μ k
    exact numD2Out_chargeOne P _ _ μ k
  unfold d2OutZero
  rw [e]
  rfl

/-! ### The mass scaled to `1` -/

theorem massScale_unitMass {P : Params} (hm : P.m ≠ 0) : massScale P.m (unitMass P) = P := by
  have h : ∀ x : ℝ, P.m * (P.m⁻¹ * x) = x := fun x => by field_simp
  simp only [unitMass, massScale, h]

/-- The Pauli–Villars difference of the `δ₂` insertion, `V_k(m_γ/m) - V_k(Λ/m)`. -/
noncomputable def dVk (m mγ Λ : ℝ) : ℝ := selfVk (mγ / m) - selfVk (Λ / m)

/-- The Pauli–Villars difference of the `δ_m` insertion, `V_m(m_γ/m) - V_m(Λ/m)`. -/
noncomputable def dVm (m mγ Λ : ℝ) : ℝ := selfVm (mγ / m) - selfVm (Λ / m)

/-- **The `δ₂, δ_m` class on the incoming line in closed form**:
`d2InZero P = 16 i e³ m⁵ (δ₂ ΔV_k + δ_m ΔV_m)/π²`. -/
theorem d2InZero_eq (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) :
    d2InZero P = 16 * I * (P.e : ℂ) ^ 3 * (P.m : ℂ) ^ 5 *
      ((P.δ₂ * dVk P.m P.mγ P.Λ + P.δm * dVm P.m P.mγ P.Λ : ℝ) : ℂ) / (π : ℂ) ^ 2 := by
  rw [d2InZero_chargeOne]
  set Q := chargeOne P with hQdef
  have hQm : Q.m = P.m := rfl
  have hm1 : (unitMass Q).m = 1 := QED.TwoLoop.MassScaling.unitMass_m (hQm ▸ hm.ne')
  have hmγ' : 0 < (unitMass Q).mγ := by
    rw [QED.TwoLoop.MassScaling.unitMass_mγ]
    exact div_pos hmγ hm
  have hΛ' : (unitMass Q).mγ < (unitMass Q).Λ := by
    rw [QED.TwoLoop.MassScaling.unitMass_mγ, QED.TwoLoop.MassScaling.unitMass_Λ]
    exact div_lt_div_of_pos_right hΛ hm
  have h1 : d2InZero Q = (Q.m : ℂ) ^ 5 * d2InZero (unitMass Q) := by
    have hQ0 : Q.m ≠ 0 := by rw [hQm]; exact hm.ne'
    conv_lhs => rw [← massScale_unitMass hQ0]
    exact QED.TwoLoop.MassScaling.d2InZero_massScale (unitMass Q) (hm1 ▸ one_pos) hmγ'
      (hmγ'.trans hΛ') (hQm ▸ hm)
  have he1 : (unitMass Q).e = 1 := rfl
  have h2 := QED.TwoLoop.UnitSCCt.d2InZero_eq_of_pointwise (unitMass Q) hm1 hmγ' hΛ'
    (QED.TwoLoop.UnitSCCt.d2Pointwise_In hm1 he1)
  rw [h1, h2, QED.TwoLoop.UnitSCCt.auxLimit_eq one_pos]
  have hd : QED.TwoLoop.UnitSCCt.ctDelta (unitMass Q) =
      P.e ^ 3 * (P.δ₂ * dVk P.m P.mγ P.Λ + P.δm * dVm P.m P.mγ P.Λ) := by
    simp only [QED.TwoLoop.UnitSCCt.ctDelta, QED.TwoLoop.MassScaling.unitMass_mγ,
      QED.TwoLoop.MassScaling.unitMass_Λ, dVk, dVm]
    simp only [unitMass, QED.TwoLoop.MassScaling.massScale_δ₂,
      QED.TwoLoop.MassScaling.massScale_δm, hQdef, chargeOne]
    ring
  rw [hd, hQm]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  rw [show (I : ℂ) ^ 2 = -1 from Complex.I_sq]
  ring

/-- **The `δ₂, δ_m` class on the outgoing line in closed form**, the same value. -/
theorem d2OutZero_eq (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) :
    d2OutZero P = 16 * I * (P.e : ℂ) ^ 3 * (P.m : ℂ) ^ 5 *
      ((P.δ₂ * dVk P.m P.mγ P.Λ + P.δm * dVm P.m P.mγ P.Λ : ℝ) : ℂ) / (π : ℂ) ^ 2 := by
  rw [d2OutZero_chargeOne]
  set Q := chargeOne P with hQdef
  have hQm : Q.m = P.m := rfl
  have hm1 : (unitMass Q).m = 1 := QED.TwoLoop.MassScaling.unitMass_m (hQm ▸ hm.ne')
  have hmγ' : 0 < (unitMass Q).mγ := by
    rw [QED.TwoLoop.MassScaling.unitMass_mγ]
    exact div_pos hmγ hm
  have hΛ' : (unitMass Q).mγ < (unitMass Q).Λ := by
    rw [QED.TwoLoop.MassScaling.unitMass_mγ, QED.TwoLoop.MassScaling.unitMass_Λ]
    exact div_lt_div_of_pos_right hΛ hm
  have h1 : d2OutZero Q = (Q.m : ℂ) ^ 5 * d2OutZero (unitMass Q) := by
    have hQ0 : Q.m ≠ 0 := by rw [hQm]; exact hm.ne'
    conv_lhs => rw [← massScale_unitMass hQ0]
    exact QED.TwoLoop.MassScaling.d2OutZero_massScale (unitMass Q) (hm1 ▸ one_pos) hmγ'
      (hmγ'.trans hΛ') (hQm ▸ hm)
  have he1 : (unitMass Q).e = 1 := rfl
  have h2 := QED.TwoLoop.UnitSCCt.d2OutZero_eq_of_pointwise (unitMass Q) hm1 hmγ' hΛ'
    (QED.TwoLoop.UnitSCCt.d2Pointwise_Out hm1 he1)
  rw [h1, h2, QED.TwoLoop.UnitSCCt.auxLimit_eq one_pos]
  have hd : QED.TwoLoop.UnitSCCt.ctDelta (unitMass Q) =
      P.e ^ 3 * (P.δ₂ * dVk P.m P.mγ P.Λ + P.δm * dVm P.m P.mγ P.Λ) := by
    simp only [QED.TwoLoop.UnitSCCt.ctDelta, QED.TwoLoop.MassScaling.unitMass_mγ,
      QED.TwoLoop.MassScaling.unitMass_Λ, dVk, dVm]
    simp only [unitMass, QED.TwoLoop.MassScaling.massScale_δ₂,
      QED.TwoLoop.MassScaling.massScale_δm, hQdef, chargeOne]
    ring
  rw [hd, hQm]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  rw [show (I : ℂ) ^ 2 = -1 from Complex.I_sq]
  ring

/-! ### The five VP-share classes -/

/-- The one-loop Pauli integral `B(0)` at mass `m` and photon masses `m_γ, Λ`. -/
noncomputable def sPauliB0 (P₀ : Params) (mγ Λ : ℝ) : ℝ :=
  oneLoopPauliZero { P₀ with mγ := mγ, Λ := Λ }

/-- The coefficient of a line class (`δ₂, δ_m`): `i e²/(4π²)`. -/
noncomputable def sCoefLine (P₀ : Params) : ℂ := I * (P₀.e : ℂ) ^ 2 / (4 * (π : ℂ) ^ 2)

/-- The coefficient of a vertex class (`δ₁`): `i e² B(0)/(8π²)`. -/
noncomputable def sCoefVtx (P₀ : Params) (mγ Λ : ℝ) : ℂ :=
  I * (P₀.e : ℂ) ^ 2 * (sPauliB0 P₀ mγ Λ : ℂ) / (8 * (π : ℂ) ^ 2)

variable {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}

theorem sParams_δ₁ : (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s).δ₁ = P₀.e ^ 4 * s.1 := by
  have h := (SetCLink.withLevel_one_entries D s (D.d₃ 1)).2.2.2.2.1
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ).openLine
  simp only [sParams, SetCLink.ctParamsLevel, shareCt, h]

theorem sParams_δ₂ : (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s).δ₂ = P₀.e ^ 4 * s.2.1 := by
  have h := (SetCLink.withLevel_one_entries D s (D.d₃ 1)).2.2.2.2.2.1
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ).openLine
  simp only [sParams, SetCLink.ctParamsLevel, shareCt, h]

theorem sParams_δm : (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s).δm = P₀.e ^ 4 * s.2.2 := by
  have h := (SetCLink.withLevel_one_entries D s (D.d₃ 1)).2.2.2.2.2.2.1
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ).openLine
  simp only [sParams, SetCLink.ctParamsLevel, shareCt, h]

/-- **The line classes `S0`, `S1`** (`δ₂, δ_m` on the outgoing, incoming line):
`i e²/(4π²) (ΔV_k e⁴s₂ + ΔV_m e⁴s_m)`. -/
theorem ctPauliAll_S_line (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmγ : 0 < mγ) (hΛ : mγ < Λ)
    (k : Fin 5) (hk : (k : ℕ) < 2) :
    ctPauliAll P₀ (.inr (.inr k)) M₁ M₂ c₁ c₂ mγ Λ D s = sCoefLine P₀ *
      ((dVk P₀.m mγ Λ : ℂ) * ((P₀.e ^ 4 * s.2.1 : ℝ) : ℂ) +
        (dVm P₀.m mγ Λ : ℂ) * ((P₀.e ^ 4 * s.2.2 : ℝ) : ℂ)) := by
  have hv : ctZero (sCls k) (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) =
      16 * I * (P₀.e : ℂ) ^ 3 * (P₀.m : ℂ) ^ 5 *
        (((sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s).δ₂ * dVk P₀.m mγ Λ +
          (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s).δm * dVm P₀.m mγ Λ : ℝ) : ℂ) / (π : ℂ) ^ 2 := by
    fin_cases k
    · exact d2OutZero_eq _ hm hmγ hΛ
    · exact d2InZero_eq _ hm hmγ hΛ
    all_goals simp at hk
  change ctZero (sCls k) (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) /
    (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5) = _
  rw [hv, sParams_δ₂, sParams_δm, sCoefLine]
  have he' : (P₀.e : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr he
  have hm' : (P₀.m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-- **The vertex classes `S2`, `S3`, `S4`** (`δ₁` at a vertex): `i e² B(0)/(8π²) · e⁴s₁`. -/
theorem ctPauliAll_S_vtx (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (k : Fin 5) (hk : 2 ≤ (k : ℕ)) :
    ctPauliAll P₀ (.inr (.inr k)) M₁ M₂ c₁ c₂ mγ Λ D s =
      sCoefVtx P₀ mγ Λ * ((P₀.e ^ 4 * s.1 : ℝ) : ℂ) := by
  have hv : ctZero (sCls k) (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) =
      d1Zero (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) := by
    fin_cases k
    all_goals first | rfl | simp at hk
  change ctZero (sCls k) (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) /
    (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5) = _
  rw [hv, d1Zero, sParams_δ₁, sCoefVtx]
  have he' : (P₀.e : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr he
  have hm' : (P₀.m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hB : oneLoopPauliZero (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) = sPauliB0 P₀ mγ Λ := rfl
  rw [hB]
  have hsm : (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s).m = P₀.m := rfl
  have hse : (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s).e = P₀.e := rfl
  rw [hsm, hse]
  push_cast
  field_simp
  ring

end QED.ChainProof.SetCRegDisp

end
