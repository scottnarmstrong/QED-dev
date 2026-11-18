/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCGraphSpData
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The pointwise second-order coefficients of the `S₊` numerator

Section 8 of `docs/TWO-LOOP-UNITS.md`, stage 1 of the `S + C` link, graph half, the analogue of
`QED/TwoLoop/UnitLGraphTraceMain.lean` for the self-energy class `S₊`. With the projected
numerator `N = T₁ + T₂ V + T₃ V²` (`QED.TwoLoop.UnitSCGraph.openNum_eq_T_of_chain`) and, at a
point `z` of the eight line parameters,
`z_o = z₀ + z₁ + z₃` (the three outer electron lines, all with the loop momentum of the outer
photon), `Y = z₂` (the inner electron of the self-energy subgraph), `z_a = z₄ + z₆`,
`z_b = z₅ + z₇` (the outer and inner photon, each a Pauli–Villars pair), `s = Y + z_b`,
`c = Y z_b`, `a = s z_o + c`, `U = a + s z_a`, at `m = 1`, `e = 1`:

* `secondCoeff_spT1`: `c₂[T₁] = (Λ² - m_γ²)² (6/K) · (-z_a s a² (2U + z_a z_b)/(2U⁶))`;
* `secondCoeff_spT2`: `c₂[T₂] = (Λ² - m_γ²)² (2/K) · z_a s (3 Y U + 2 s z_a z_b)/U⁵`;
* `secondCoeff_spT3`: `c₂[T₃] = 0`,

with `K = 16π⁴/(64 i)`, for every `z` with `U ≠ 0` and every splitting of the outer electron
lines and of the photon pairs. Hence (`openZero_Sp_eq`)
`openZero .Sp P = ∫_{Δ₇} (c₂[T₁] + c₂[T₂] V)/V⁴`.

These are the formulas checked numerically by `scripts/numerics/sc_graph/` (against a
finite-difference model of `openNum .Sp` and, after merging the splits and the Pauli–Villars
pairs, against the engine integrand of `scripts/numerics/two_loop_units.py`, graph `S+`).
-/

@[expose] public section

open Complex Matrix
open scoped Real

namespace QED.TwoLoop.UnitSCGraph

open Filter Topology
open QED.WickModel QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.TwoLoop.ParamNumEval QED.TwoLoop.UnitLGraph QED.TwoLoop.UnitLGraphTrace
open QED.TwoLoop.Bridge QED.TwoLoop.Enumeration QED.TwoLoop.LimitCovariance
open QED.Integration.Feynman (simplexPoint)
open QED.Integration.TwoLoop (castLoopMatrix class5LoopMatrixPV symanzikU symanzikV symanzikVector
  symanzikMatrix)

/-! ### The parameters -/

section Params

variable (z : Fin 8 → ℝ)

/-- The three outer electron lines `z_o = z₀ + z₁ + z₃`. -/
def spzo : ℝ := z 0 + z 1 + z 3
/-- The inner electron `Y = z₂`. -/
def spY : ℝ := z 2
/-- The outer photon `z_a = z₄ + z₆`. -/
def spza : ℝ := z 4 + z 6
/-- The inner photon `z_b = z₅ + z₇`. -/
def spzb : ℝ := z 5 + z 7
/-- `s = Y + z_b`. -/
def spS : ℝ := spY z + spzb z
/-- `c = Y z_b`. -/
def spc : ℝ := spY z * spzb z
/-- `a = s z_o + c`. -/
def spa : ℝ := spS z * spzo z + spc z
/-- `U = a + s z_a`. -/
def spU : ℝ := spa z + spS z * spza z

theorem symanzikMatrix_Sp :
    symanzikMatrix (classAlpha .Sp) z =
      !![spzo z + spza z + spY z, spzo z + spza z; spzo z + spza z, spzo z + spza z + spzb z] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symanzikMatrix, Fin.sum_univ_succ, castLoopMatrix, class5LoopMatrixPV,
      QED.Integration.TwoLoop.class5LoopMatrix, spzo, spY, spza, spzb] <;> ring

theorem symanzikU_Sp : symanzikU (classAlpha .Sp) z = spU z := by
  rw [symanzikU, symanzikMatrix_Sp, Matrix.det_fin_two_of]
  simp only [spU, spa, spc, spS]
  ring

theorem inv_symanzikMatrix_Sp (s t : Fin 2) :
    (symanzikMatrix (classAlpha .Sp) z)⁻¹ s t =
      (spU z)⁻¹ * !![spzo z + spza z + spzb z, -(spzo z + spza z);
        -(spzo z + spza z), spzo z + spza z + spY z] s t := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', ← symanzikU, symanzikU_Sp, symanzikMatrix_Sp,
    Matrix.adjugate_fin_two_of, Matrix.smul_apply, smul_eq_mul]

/-- `X = σ₀ + τ₀`. -/
noncomputable def spX : ℝ := spSigP z 0 + spSigQ z 0
/-- `W = σ₀ + σ₁ + τ₀ + τ₁`. -/
noncomputable def spW : ℝ := spSigP z 0 + spSigP z 1 + spSigQ z 0 + spSigQ z 1
/-- `T = τ₀ + τ₁`. -/
noncomputable def spT : ℝ := spSigQ z 0 + spSigQ z 1
/-- `T₀ = τ₀`. -/
noncomputable def spT0 : ℝ := spSigQ z 0

theorem spX_eq : spX z = (spU z)⁻¹ *
    ((spzo z + spza z + spzb z) * (z 0 + z 1 + z 2 + z 3) - (spzo z + spza z) * (z 0 + z 1 + z 3)) := by
  simp only [spX, spSigP, spSigQ, inv_symanzikMatrix_Sp]
  simp
  ring

theorem spW_eq : spW z = (spU z)⁻¹ *
    (spzb z * (z 0 + z 1 + z 2 + z 3) + spY z * (z 0 + z 1 + z 3)) := by
  simp only [spW, spSigP, spSigQ, inv_symanzikMatrix_Sp]
  simp [spzo]
  ring

theorem spT_eq : spT z = (spU z)⁻¹ * (spzb z * (z 1 + z 2 + z 3) + spY z * (z 1 + z 3)) := by
  simp only [spT, spSigQ, inv_symanzikMatrix_Sp]
  simp [spzo]
  ring

theorem spT0_eq : spT0 z = (spU z)⁻¹ *
    ((spzo z + spza z + spzb z) * (z 1 + z 2 + z 3) - (spzo z + spza z) * (z 1 + z 3)) := by
  simp only [spT0, spSigQ, inv_symanzikMatrix_Sp]
  simp
  ring

end Params

/-! ### The rational identities -/

theorem spU_eq (z : Fin 8 → ℝ) :
    spU z = (spzo z + spza z + spY z) * (spzo z + spza z + spzb z) - (spzo z + spza z) ^ 2 := by
  simp only [spU, spa, spc, spS]; ring

/-- The rational identity of `c₂[T₁]` of `S₊`. -/
theorem spPsi1_identity {z : Fin 8 → ℝ} (hU : spU z ≠ 0) :
    spT z * spW z ^ 2 * spX z - spT z * spW z ^ 2 - 2 * spT z * spW z * spX z +
        2 * spT z * spW z - spT0 z * spW z ^ 3 + 3 * spT0 z * spW z ^ 2 - 2 * spT0 z * spW z +
        spW z ^ 3 * spX z - 2 * spW z ^ 3 - 2 * spW z ^ 2 * spX z + spW z ^ 2 + 2 * spW z * spX z =
      spza z * spS z * spa z ^ 2 * (2 * spU z + spza z * spzb z) / spU z ^ 4 := by
  rw [spX_eq, spW_eq, spT_eq, spT0_eq]
  have h : (spzo z + spza z + spY z) * (spzo z + spza z + spzb z) - (spzo z + spza z) ^ 2 ≠ 0 := by
    rwa [← spU_eq]
  simp only [spa, spc, spS]
  rw [spU_eq]
  simp only [spzo, spza, spzb, spY] at h ⊢
  field_simp
  ring

/-- The rational identity of `c₂[T₂]` of `S₊`, with `c₀₁ = z_b/U`, `c₀₂ = s/U` the contraction
coefficients. -/
theorem spPsi2_identity {z : Fin 8 → ℝ} (hU : spU z ≠ 0) :
    3072 * spT z * spX z * (spS z / spU z) - 3072 * spT z * (spS z / spU z) -
        3072 * spT0 z * spW z * (spS z / spU z) + 3072 * spT0 z * (spS z / spU z) +
        5120 * spW z ^ 2 * (spzb z / spU z) - 1024 * spW z * spX z * (spS z / spU z) -
        5120 * spW z * (spzb z / spU z) - 2048 * spW z * (spS z / spU z) -
        1024 * spX z * (spS z / spU z) + 4096 * (spS z / spU z) =
      2048 * (spza z * spS z * (3 * spY z * spU z + 2 * spS z * spza z * spzb z) / spU z ^ 3) := by
  rw [spX_eq, spW_eq, spT_eq, spT0_eq]
  have h : (spzo z + spza z + spY z) * (spzo z + spza z + spzb z) - (spzo z + spza z) ^ 2 ≠ 0 := by
    rwa [← spU_eq]
  simp only [spS]
  rw [spU_eq]
  simp only [spzo, spza, spzb, spY] at h ⊢
  field_simp
  ring

/-! ### The second-order coefficients -/

/-- The jet of the slot numerator `k` of `S₊`. -/
noncomputable def spSlotJ (z : Fin 8 → ℝ) (k : Fin 4) : PJ :=
  eJ ((spSlotA z k : ℂ) + (spSlotB z k : ℂ)) (spSlotB z k : ℂ)

theorem pwJ_spSlot_T1 (z : Fin 8 → ℝ) :
    pwJ qJ0.gam qJ1.gam rJ.gamT (((spSlotJ z 0).mul (spSlotJ z 1).gam).mul (spSlotJ z 2))
      (spSlotJ z 3) =
      -512 * ((spT z * spW z ^ 2 * spX z - spT z * spW z ^ 2 - 2 * spT z * spW z * spX z +
        2 * spT z * spW z - spT0 z * spW z ^ 3 + 3 * spT0 z * spW z ^ 2 - 2 * spT0 z * spW z +
        spW z ^ 3 * spX z - 2 * spW z ^ 3 - 2 * spW z ^ 2 * spX z + spW z ^ 2 +
        2 * spW z * spX z : ℝ) : ℂ) := by
  simp only [spSlotJ, pwJ_Sp_T1, spSlotA, spSlotB, spX, spW, spT, spT0, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons]
  push_cast
  ring

/-- **The jet of `T₁` of `S₊`**. -/
theorem hasJet2_spT1 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : spU z ≠ 0) :
    HasJet2 (classT1 .Sp permSp P z) 0 0 (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
      ((-(spza z * spS z * spa z ^ 2 * (2 * spU z + spza z * spzb z)) / (2 * spU z ^ 6) : ℝ) :
        ℂ)) := by
  have h := hasJet2_pwPl (q₀ := qJ0.gam) (q₁ := qJ1.gam) (r := rJ.gamT)
    (w := ((spSlotJ z 0).mul (spSlotJ z 1).gam).mul (spSlotJ z 2)) (z := spSlotJ z 3)
    (jet_lQ0 hm).gam (jet_lQ1 hm).gam (jet_lR hm).gamT
    (((jet_spE hm z 0).mul (jet_spE hm z 1).gam).mul (jet_spE hm z 2)) (jet_spE hm z 3)
  have h' := (h.const_mul 6).const_mul
    (ladderK P * ((symanzikU (classAlpha .Sp) z ^ 2 : ℝ) : ℂ)⁻¹)
  refine (h'.congr fun u => classT1_Sp_planar P z u).of_eq (fun _ => rfl) ?_ ?_ ?_
  · simp [spSlotJ]
  · simp [spSlotJ]
  rw [pwJ_spSlot_T1, spPsi1_identity hU, ladderK_eq he, symanzikU_Sp, kConst]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hU' : (spU z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU
  push_cast
  field_simp
  ring

/-- **The second-order coefficient of `T₁` of `S₊`**. -/
theorem secondCoeff_spT1 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : spU z ≠ 0) :
    secondCoeff (classT1 .Sp permSp P z) = ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
      ((-(spza z * spS z * spa z ^ 2 * (2 * spU z + spza z * spzb z)) / (2 * spU z ^ 6) : ℝ) :
        ℂ) :=
  (hasJet2_spT1 hm he hU).secondCoeff_eq

theorem classC_Sp_val (z : Fin 8 → ℝ) :
    classC .Sp (symanzikMatrix (classAlpha .Sp) z) 0 1 = ((spzb z / spU z : ℝ) : ℂ) ∧
    classC .Sp (symanzikMatrix (classAlpha .Sp) z) 0 2 = ((spS z / spU z : ℝ) : ℂ) ∧
    classC .Sp (symanzikMatrix (classAlpha .Sp) z) 0 3 = ((spS z / spU z : ℝ) : ℂ) ∧
    classC .Sp (symanzikMatrix (classAlpha .Sp) z) 1 2 = ((spzb z / spU z : ℝ) : ℂ) ∧
    classC .Sp (symanzikMatrix (classAlpha .Sp) z) 1 3 = ((spzb z / spU z : ℝ) : ℂ) ∧
    classC .Sp (symanzikMatrix (classAlpha .Sp) z) 2 3 = ((spS z / spU z : ℝ) : ℂ) := by
  simp only [classC, contrC, Fin.sum_univ_two, inv_symanzikMatrix_Sp]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [castLoopMatrix, class5LoopMatrixPV, QED.Integration.TwoLoop.class5LoopMatrix, ladderLines,
      spS] <;> ring

theorem spT2_combination (z : Fin 8 → ℝ) :
    classC .Sp (symanzikMatrix (classAlpha .Sp) z) 0 1 *
        (-8 * pwJ qJ0.gam qJ1.gam rJ.gamT (spSlotJ z 2) (spSlotJ z 3)) +
      classC .Sp (symanzikMatrix (classAlpha .Sp) z) 0 2 *
        pwJ qJ0.gam qJ1.gam rJ.gamT (spSlotJ z 1).gam.gam (spSlotJ z 3) +
      classC .Sp (symanzikMatrix (classAlpha .Sp) z) 0 3 *
        pwJ qJ0.gam.gam qJ1.gam.gam rJ.gamT.gamT ((spSlotJ z 1).gam.mul (spSlotJ z 2)) (PJ.c 1) +
      classC .Sp (symanzikMatrix (classAlpha .Sp) z) 1 2 *
        (-8 * pwJ qJ0.gam qJ1.gam rJ.gamT (spSlotJ z 0) (spSlotJ z 3)) +
      classC .Sp (symanzikMatrix (classAlpha .Sp) z) 1 3 *
        (2 * pwJ ((qJ0.gam.mul (spSlotJ z 0)).gam) ((qJ1.gam.mul (spSlotJ z 0)).gam)
          ((rJ.gamT.mul (spSlotJ z 0).bar).gamT) (spSlotJ z 2) (PJ.c 1)) +
      classC .Sp (symanzikMatrix (classAlpha .Sp) z) 2 3 *
        (2 * pwJ qJ0.gam qJ1.gam rJ.gamT ((spSlotJ z 0).mul (spSlotJ z 1).gam) (PJ.c 1)) =
    ((3072 * spT z * spX z * (spS z / spU z) - 3072 * spT z * (spS z / spU z) -
        3072 * spT0 z * spW z * (spS z / spU z) + 3072 * spT0 z * (spS z / spU z) +
        5120 * spW z ^ 2 * (spzb z / spU z) - 1024 * spW z * spX z * (spS z / spU z) -
        5120 * spW z * (spzb z / spU z) - 2048 * spW z * (spS z / spU z) -
        1024 * spX z * (spS z / spU z) + 4096 * (spS z / spU z) : ℝ) : ℂ) := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := classC_Sp_val z
  rw [h01, h02, h03, h12, h13, h23]
  simp only [spSlotJ, pwJ_Sp_23, pwJ_Sp_02, pwJ_Sp_03, pwJ_Sp_13, pwJ_Sp_23', spSlotA, spSlotB,
    spX, spW, spT, spT0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  ring

/-- **The jet of `T₂` of `S₊`**. -/
theorem hasJet2_spT2 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : spU z ≠ 0) :
    HasJet2 (classT2 .Sp permSp P z) 0 0 (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
      ((spza z * spS z * (3 * spY z * spU z + 2 * spS z * spza z * spzb z) / spU z ^ 5 : ℝ) :
        ℂ)) := by
  have hq0 := HasPJ.gam (x := qJ0) (jet_lQ0 hm)
  have hq1 := HasPJ.gam (x := qJ1) (jet_lQ1 hm)
  have hr := HasPJ.gamT (x := rJ) (jet_lR hm)
  have h₁ := hasJet2_pwPl hq0 hq1 hr (jet_spE hm z 2) (jet_spE hm z 3)
  have h₂ := hasJet2_pwPl hq0 hq1 hr (jet_spE hm z 1).gam.gam (jet_spE hm z 3)
  have h₃ := hasJet2_pwPl hq0.gam hq1.gam hr.gamT ((jet_spE hm z 1).gam.mul (jet_spE hm z 2))
    (HasPJ.const 1)
  have h₄ := hasJet2_pwPl hq0 hq1 hr (jet_spE hm z 0) (jet_spE hm z 3)
  have h₅ := hasJet2_pwPl (hq0.mul (jet_spE hm z 0)).gam (hq1.mul (jet_spE hm z 0)).gam
    (hr.mul (jet_spE hm z 0).bar).gamT (jet_spE hm z 2) (HasPJ.const 1)
  have h₆ := hasJet2_pwPl hq0 hq1 hr ((jet_spE hm z 0).mul (jet_spE hm z 1).gam) (HasPJ.const 1)
  have h := (((((((h₁.const_mul (-8)).const_mul
      (classC .Sp (symanzikMatrix (classAlpha .Sp) z) 0 1)).add
    (h₂.const_mul (classC .Sp (symanzikMatrix (classAlpha .Sp) z) 0 2))).add
    (h₃.const_mul (classC .Sp (symanzikMatrix (classAlpha .Sp) z) 0 3))).add
    ((h₄.const_mul (-8)).const_mul (classC .Sp (symanzikMatrix (classAlpha .Sp) z) 1 2))).add
    ((h₅.const_mul 2).const_mul (classC .Sp (symanzikMatrix (classAlpha .Sp) z) 1 3))).add
    ((h₆.const_mul 2).const_mul (classC .Sp (symanzikMatrix (classAlpha .Sp) z) 2 3))).const_mul
    (ladderK P * ((symanzikU (classAlpha .Sp) z ^ 2 : ℝ) : ℂ)⁻¹)
  refine (h.congr fun u => classT2_Sp_planar P z u).of_eq (fun _ => rfl) ?_ ?_ ?_
  · simp
  · simp
  have hc := spT2_combination z
  simp only [spSlotJ] at hc
  rw [hc, spPsi2_identity hU, ladderK_eq he, symanzikU_Sp, kConst]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hU' : (spU z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU
  push_cast
  field_simp
  ring

/-- **The second-order coefficient of `T₂` of `S₊`**. -/
theorem secondCoeff_spT2 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : spU z ≠ 0) :
    secondCoeff (classT2 .Sp permSp P z) = ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
      ((spza z * spS z * (3 * spY z * spU z + 2 * spS z * spza z * spzb z) / spU z ^ 5 : ℝ) :
        ℂ) :=
  (hasJet2_spT2 hm he hU).secondCoeff_eq

/-- **The jet of `T₃` of `S₊` vanishes**. -/
theorem hasJet2_spT3 {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) :
    HasJet2 (classT3 .Sp permSp P z) 0 0 0 := by
  have h₁ := hasJet2_pwPl (HasPJ.gam (x := qJ0) (jet_lQ0 hm)) (HasPJ.gam (x := qJ1) (jet_lQ1 hm))
    (HasPJ.gamT (x := rJ) (jet_lR hm)) (HasPJ.const 1) (HasPJ.const 1)
  set C := fun k l => classC .Sp (symanzikMatrix (classAlpha .Sp) z) k l
  have h := (((((h₁.const_mul (-16)).const_mul (C 0 1 * C 2 3)).add
    ((h₁.const_mul 8).const_mul (C 0 2 * C 1 3))).add
    ((h₁.const_mul (-16)).const_mul (C 0 3 * C 1 2))).const_mul (1 / 4)).const_mul
    (ladderK P * ((symanzikU (classAlpha .Sp) z ^ 2 : ℝ) : ℂ)⁻¹)
  refine (h.congr fun u => classT3_Sp_planar P z u).of_eq (fun _ => rfl) ?_ ?_ ?_ <;>
    simp [pwJ_Sp_T3]

/-- **The second-order coefficient of `T₃` of `S₊` vanishes.** -/
theorem secondCoeff_spT3 {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) :
    secondCoeff (classT3 .Sp permSp P z) = 0 :=
  (hasJet2_spT3 hm z).secondCoeff_eq

/-! ### The second-order coefficient of the projected numerator -/

@[fun_prop] theorem continuous_pvMomentaE_Sp (r : Fin 4 → ℝ) (i : Fin 8) (μ : Fin 4) :
    Continuous fun p' : Fin 4 → ℝ => pvMomentaE .Sp r p' i μ := by
  fin_cases i <;>
    simp [pvMomentaE, extMomenta, QED.Integration.TwoLoop.classCpSpMomenta,
      QED.Integration.TwoLoop.pvLines] <;> fun_prop

theorem continuous_spV (r : Fin 4 → ℝ) (M z : Fin 8 → ℝ) :
    Continuous fun p' : Fin 4 → ℝ => symanzikV (classAlpha .Sp) (pvMomentaE .Sp r p') M z := by
  unfold symanzikV symanzikVector QED.Minkowski.dot
  fun_prop

/-- The second Symanzik function of `S₊` along the curve tends to its value at `q = 0`. -/
theorem tendsto_spV (P : Params) (x : Fin 7 → ℝ) :
    Tendsto (fun u => ((symanzikV (classAlpha .Sp) (classMom .Sp P u) (pvMasses P)
        (simplexPoint x) : ℝ) : ℂ))
      (𝓝 0) (𝓝 ((openV .Sp P x : ℝ) : ℂ)) := by
  have h := ((continuous_spV (restMomentum P.m) (pvMasses P) (simplexPoint x)).tendsto
    (restMomentum P.m)).comp (tendsto_curveMomentum P.m)
  exact (Complex.continuous_ofReal.tendsto _).comp h

theorem Sp_mem_openClasses : Class5.Sp ∈ QED.TwoLoop.ClassIntegrable.openClasses := by decide

/-- **The jet of the projected `S₊` numerator**: `N(x, u) = c₂ u² + o(u²)` with
`c₂ = c₂[T₁] + c₂[T₂] V(x)`. -/
theorem hasJet2_openNum_Sp {P : Params} (hm : P.m = 1) (he : P.e = 1) (x : Fin 7 → ℝ)
    (hU : spU (simplexPoint x) ≠ 0) :
    HasJet2 (openNum .Sp P x) 0 0
      (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
          ((-(spza (simplexPoint x) * spS (simplexPoint x) * spa (simplexPoint x) ^ 2 *
              (2 * spU (simplexPoint x) + spza (simplexPoint x) * spzb (simplexPoint x))) /
            (2 * spU (simplexPoint x) ^ 6) : ℝ) : ℂ) +
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
          ((spza (simplexPoint x) * spS (simplexPoint x) *
              (3 * spY (simplexPoint x) * spU (simplexPoint x) +
                2 * spS (simplexPoint x) * spza (simplexPoint x) * spzb (simplexPoint x)) /
            spU (simplexPoint x) ^ 5 : ℝ) : ℂ) * ((openV .Sp P x : ℝ) : ℂ)) := by
  have hV := tendsto_spV P x
  have h := ((hasJet2_spT1 hm he hU).add (hasJet2_mul_tendsto (hasJet2_spT2 hm he hU) hV)).add
    (hasJet2_mul_tendsto (hasJet2_spT3 hm (simplexPoint x)) (hV.pow 2))
  exact h.of_eq (fun u => openNum_eq_T_of_chain isChainForm_Sp classMomE_Sp_eq Sp_mem_openClasses
    P x u) (by ring) (by ring) (by ring)

/-- **The second-order coefficient of the projected `S₊` numerator.** -/
theorem secondCoeff_openNum_Sp {P : Params} (hm : P.m = 1) (he : P.e = 1) (x : Fin 7 → ℝ)
    (hU : spU (simplexPoint x) ≠ 0) :
    secondCoeff (openNum .Sp P x) =
      ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
          ((-(spza (simplexPoint x) * spS (simplexPoint x) * spa (simplexPoint x) ^ 2 *
              (2 * spU (simplexPoint x) + spza (simplexPoint x) * spzb (simplexPoint x))) /
            (2 * spU (simplexPoint x) ^ 6) : ℝ) : ℂ) +
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
          ((spza (simplexPoint x) * spS (simplexPoint x) *
              (3 * spY (simplexPoint x) * spU (simplexPoint x) +
                2 * spS (simplexPoint x) * spza (simplexPoint x) * spzb (simplexPoint x)) /
            spU (simplexPoint x) ^ 5 : ℝ) : ℂ) * ((openV .Sp P x : ℝ) : ℂ) :=
  (hasJet2_openNum_Sp hm he x hU).secondCoeff_eq

/-- Almost every point of the simplex has `U ≠ 0` (for `S₊`). -/
theorem ae_spU_ne_zero : ∀ᵐ x ∂(MeasureTheory.volume.restrict
    (QED.Integration.Feynman.simplexSet 7)),
    spU (simplexPoint x) ≠ 0 := by
  have hspan : ∃ i j, classAlpha .Sp i 0 * classAlpha .Sp j 1 -
      classAlpha .Sp i 1 * classAlpha .Sp j 0 ≠ 0 :=
    ⟨0, 2, by simp [castLoopMatrix, class5LoopMatrixPV, QED.Integration.TwoLoop.class5LoopMatrix]⟩
  filter_upwards [QED.Integration.TwoLoop.ae_posDef (classAlpha .Sp) (by norm_num) hspan] with x hx
  rw [← symanzikU_Sp]
  exact hx.2.det_pos.ne'

/-- **The `S₊` class value with the explicit integrand**: at `m = 1`, `e = 1`,
`openZero .Sp P = ∫_{Δ₇} (c₂[T₁] + c₂[T₂] V)/V⁴` with
`c₂[T₁] = (Λ² - m_γ²)² (6/K) (-z_a s a² (2U + z_a z_b)/(2U⁶))` and
`c₂[T₂] = (Λ² - m_γ²)² (2/K) z_a s (3 Y U + 2 s z_a z_b)/U⁵`. -/
theorem openZero_Sp_eq {P : Params} (hm : P.m = 1) (he : P.e = 1) :
    openZero .Sp P = ∫ x in QED.Integration.Feynman.simplexSet 7,
      (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
          ((-(spza (simplexPoint x) * spS (simplexPoint x) * spa (simplexPoint x) ^ 2 *
              (2 * spU (simplexPoint x) + spza (simplexPoint x) * spzb (simplexPoint x))) /
            (2 * spU (simplexPoint x) ^ 6) : ℝ) : ℂ) +
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
          ((spza (simplexPoint x) * spS (simplexPoint x) *
              (3 * spY (simplexPoint x) * spU (simplexPoint x) +
                2 * spS (simplexPoint x) * spza (simplexPoint x) * spzb (simplexPoint x)) /
            spU (simplexPoint x) ^ 5 : ℝ) : ℂ) * ((openV .Sp P x : ℝ) : ℂ)) /
        ((openV .Sp P x : ℝ) : ℂ) ^ 4 := by
  unfold openZero
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [ae_spU_ne_zero] with x hx
  rw [secondCoeff_openNum_Sp hm he x hx]

end QED.TwoLoop.UnitSCGraph

end
