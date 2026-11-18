/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCGraphSmData
public import QED.TwoLoop.UnitSCGraphSpMain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The pointwise second-order coefficients of the `S₋` numerator

Section 8 of `docs/TWO-LOOP-UNITS.md`, stage 1 of the `S + C` link, graph half, the analogue of
`QED/TwoLoop/UnitSCGraphSpMain.lean` for the self-energy class `S₋`. With the projected
numerator `N = T₁ + T₂ V + T₃ V²` (`QED.TwoLoop.UnitSCGraph.openNum_eq_T_of_chain`) and, at a
point `z` of the eight line parameters,
`z_o = z₀ + z₂ + z₃` (the three outer electron lines), `Y = z₁` (the inner electron of the
self-energy subgraph), `z_a = z₄ + z₆`, `z_b = z₅ + z₇` (the outer and inner photon, each a
Pauli–Villars pair), `s = Y + z_b`, `c = Y z_b`, `a = s z_o + c`, `U = a + s z_a`, at `m = 1`,
`e = 1`:

* `secondCoeff_smT1`: `c₂[T₁] = (Λ² - m_γ²)² (6/K) · (-z_a s a² (2U + z_a z_b)/(2U⁶))`;
* `secondCoeff_smT2`: `c₂[T₂] = (Λ² - m_γ²)² (2/K) · z_a s (3 Y U + 2 s z_a z_b)/U⁵`;
* `secondCoeff_smT3`: `c₂[T₃] = 0`,

with `K = 16π⁴/(64 i)`: the same functions of the group variables as for `S₊`
(`QED/TwoLoop/UnitSCGraphSpMain.lean`), as the mirror symmetry predicts. Hence
(`openZero_Sm_eq`) `openZero .Sm P = ∫_{Δ₇} (c₂[T₁] + c₂[T₂] V)/V⁴`.

These formulas were checked numerically by `scripts/numerics/sc_graph/` (exact 4×4 traces in
`symbolic_c2.py`, the finite-difference model `model_check.py`, and the engine of
`scripts/numerics/two_loop_units.py`, graph `S-`, in `engine_check.py`).
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

/-- The three outer electron lines `z_o = z₀ + z₂ + z₃` of `S₋`. -/
def smzo : ℝ := z 0 + z 2 + z 3
/-- The inner electron `Y = z₁` of `S₋`. -/
def smY : ℝ := z 1
/-- `s = Y + z_b`. -/
def smS : ℝ := smY z + spzb z
/-- `c = Y z_b`. -/
def smc : ℝ := smY z * spzb z
/-- `a = s z_o + c`. -/
def sma : ℝ := smS z * smzo z + smc z
/-- `U = a + s z_a`. -/
def smU : ℝ := sma z + smS z * spza z

theorem symanzikMatrix_Sm :
    symanzikMatrix (classAlpha .Sm) z =
      !![smzo z + spza z + smY z, -smY z; -smY z, smY z + spzb z] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symanzikMatrix, Fin.sum_univ_succ, castLoopMatrix, class5LoopMatrixPV,
      QED.Integration.TwoLoop.class5LoopMatrix, smzo, smY, spza, spzb]
  all_goals ring

theorem smU_eq : smU z = (smzo z + spza z + smY z) * (smY z + spzb z) - smY z ^ 2 := by
  simp only [smU, sma, smc, smS]; ring

theorem symanzikU_Sm : symanzikU (classAlpha .Sm) z = smU z := by
  rw [symanzikU, symanzikMatrix_Sm, Matrix.det_fin_two_of, smU_eq]
  ring

theorem inv_symanzikMatrix_Sm (s t : Fin 2) :
    (symanzikMatrix (classAlpha .Sm) z)⁻¹ s t =
      (smU z)⁻¹ * !![smY z + spzb z, smY z; smY z, smzo z + spza z + smY z] s t := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', ← symanzikU, symanzikU_Sm, symanzikMatrix_Sm,
    Matrix.adjugate_fin_two_of, Matrix.smul_apply, smul_eq_mul]
  fin_cases s <;> fin_cases t <;> simp

/-- `X = σ₀ + τ₀`. -/
noncomputable def smX : ℝ := smSigP z 0 + smSigQ z 0
/-- `V = σ₀ - σ₁ + τ₀ - τ₁`. -/
noncomputable def smV : ℝ := smSigP z 0 - smSigP z 1 + smSigQ z 0 - smSigQ z 1
/-- `T₀ = τ₀`. -/
noncomputable def smT0 : ℝ := smSigQ z 0
/-- `T = τ₀ - τ₁`. -/
noncomputable def smT : ℝ := smSigQ z 0 - smSigQ z 1

theorem smX_eq : smX z = (smU z)⁻¹ *
    ((smY z + spzb z) * (z 0 + z 1 + z 2 + z 3) - smY z * z 1) := by
  simp only [smX, smSigP, smSigQ, inv_symanzikMatrix_Sm]
  simp
  ring

theorem smV_eq : smV z = (smU z)⁻¹ *
    (spzb z * (z 0 + z 1 + z 2 + z 3) + (smzo z + spza z) * z 1) := by
  simp only [smV, smSigP, smSigQ, inv_symanzikMatrix_Sm]
  simp [smY]
  ring

theorem smT0_eq : smT0 z = (smU z)⁻¹ * ((smY z + spzb z) * z 3) := by
  simp only [smT0, smSigQ, inv_symanzikMatrix_Sm]
  simp
  ring

theorem smT_eq : smT z = (smU z)⁻¹ * (spzb z * z 3) := by
  simp only [smT, smSigQ, inv_symanzikMatrix_Sm]
  simp
  ring

end Params

/-! ### The rational identities -/

/-- The rational identity of `c₂[T₁]` of `S₋`. -/
theorem smPsi1_identity {z : Fin 8 → ℝ} (hU : smU z ≠ 0) :
    smT z * smX z ^ 3 - 3 * smT z * smX z ^ 2 + 2 * smT z * smX z -
        smT0 z * smV z * smX z ^ 2 + 2 * smT0 z * smV z * smX z + smT0 z * smX z ^ 2 -
        2 * smT0 z * smX z + smV z * smX z ^ 3 - smV z * smX z ^ 2 - 3 * smX z ^ 3 +
        3 * smX z ^ 2 =
      spza z * smS z * sma z ^ 2 * (2 * smU z + spza z * spzb z) / smU z ^ 4 := by
  rw [smX_eq, smV_eq, smT_eq, smT0_eq]
  have h : (smzo z + spza z + smY z) * (smY z + spzb z) - smY z ^ 2 ≠ 0 := by
    rwa [← smU_eq]
  simp only [sma, smc, smS]
  rw [smU_eq]
  simp only [smzo, spza, spzb, smY] at h ⊢
  field_simp
  ring

/-- The rational identity of `c₂[T₂]` of `S₋`, with `c₀₁ = s/U`, `c₀₂ = z_b/U` the contraction
coefficients. -/
theorem smPsi2_identity {z : Fin 8 → ℝ} (hU : smU z ≠ 0) :
    3072 * smT z * smX z * (smS z / smU z) - 3072 * smT z * (smS z / smU z) -
        3072 * smT0 z * smV z * (smS z / smU z) + 3072 * smT0 z * (smS z / smU z) -
        1024 * smV z * smX z * (smS z / smU z) + 2048 * smV z * (smS z / smU z) +
        5120 * smX z ^ 2 * (spzb z / smU z) - 5120 * smX z * (spzb z / smU z) -
        5120 * smX z * (smS z / smU z) + 4096 * (smS z / smU z) =
      2048 * (spza z * smS z * (3 * smY z * smU z + 2 * smS z * spza z * spzb z) / smU z ^ 3) := by
  rw [smX_eq, smV_eq, smT_eq, smT0_eq]
  have h : (smzo z + spza z + smY z) * (smY z + spzb z) - smY z ^ 2 ≠ 0 := by
    rwa [← smU_eq]
  simp only [smS]
  rw [smU_eq]
  simp only [smzo, spza, spzb, smY] at h ⊢
  field_simp
  ring

/-! ### The second-order coefficients -/

/-- The jet of the slot numerator `k` of `S₋`. -/
noncomputable def smSlotJ (z : Fin 8 → ℝ) (k : Fin 4) : PJ :=
  eJ ((smSlotA z k : ℂ) + (smSlotB z k : ℂ)) (smSlotB z k : ℂ)

theorem pwJ_smSlot_T1 (z : Fin 8 → ℝ) :
    pwJ qJ0.gam qJ1.gam rJ.gamT (smSlotJ z 0)
      (((smSlotJ z 1).mul (smSlotJ z 2).gam).mul (smSlotJ z 3)) =
      -512 * ((smT z * smX z ^ 3 - 3 * smT z * smX z ^ 2 + 2 * smT z * smX z -
        smT0 z * smV z * smX z ^ 2 + 2 * smT0 z * smV z * smX z + smT0 z * smX z ^ 2 -
        2 * smT0 z * smX z + smV z * smX z ^ 3 - smV z * smX z ^ 2 - 3 * smX z ^ 3 +
        3 * smX z ^ 2 : ℝ) : ℂ) := by
  simp only [smSlotJ, pwJ_Sm_T1, smSlotA, smSlotB, smX, smV, smT, smT0, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons]
  push_cast
  ring

/-- **The jet of `T₁` of `S₋`**. -/
theorem hasJet2_smT1 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : smU z ≠ 0) :
    HasJet2 (classT1 .Sm permSm P z) 0 0 (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
      ((-(spza z * smS z * sma z ^ 2 * (2 * smU z + spza z * spzb z)) / (2 * smU z ^ 6) : ℝ) :
        ℂ)) := by
  have h := hasJet2_pwPl (q₀ := qJ0.gam) (q₁ := qJ1.gam) (r := rJ.gamT)
    (w := smSlotJ z 0) (z := ((smSlotJ z 1).mul (smSlotJ z 2).gam).mul (smSlotJ z 3))
    (jet_lQ0 hm).gam (jet_lQ1 hm).gam (jet_lR hm).gamT (jet_smE hm z 0)
    (((jet_smE hm z 1).mul (jet_smE hm z 2).gam).mul (jet_smE hm z 3))
  have h' := (h.const_mul 6).const_mul
    (ladderK P * ((symanzikU (classAlpha .Sm) z ^ 2 : ℝ) : ℂ)⁻¹)
  refine (h'.congr fun u => classT1_Sm_planar P z u).of_eq (fun _ => rfl) ?_ ?_ ?_
  · simp [smSlotJ]
  · simp [smSlotJ]
  rw [pwJ_smSlot_T1, smPsi1_identity hU, ladderK_eq he, symanzikU_Sm, kConst]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hU' : (smU z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU
  push_cast
  field_simp
  ring

/-- **The second-order coefficient of `T₁` of `S₋`**. -/
theorem secondCoeff_smT1 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : smU z ≠ 0) :
    secondCoeff (classT1 .Sm permSm P z) = ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
      ((-(spza z * smS z * sma z ^ 2 * (2 * smU z + spza z * spzb z)) / (2 * smU z ^ 6) : ℝ) :
        ℂ) :=
  (hasJet2_smT1 hm he hU).secondCoeff_eq

theorem classC_Sm_val (z : Fin 8 → ℝ) :
    classC .Sm (symanzikMatrix (classAlpha .Sm) z) 0 1 = ((smS z / smU z : ℝ) : ℂ) ∧
    classC .Sm (symanzikMatrix (classAlpha .Sm) z) 0 2 = ((spzb z / smU z : ℝ) : ℂ) ∧
    classC .Sm (symanzikMatrix (classAlpha .Sm) z) 0 3 = ((smS z / smU z : ℝ) : ℂ) ∧
    classC .Sm (symanzikMatrix (classAlpha .Sm) z) 1 2 = ((spzb z / smU z : ℝ) : ℂ) ∧
    classC .Sm (symanzikMatrix (classAlpha .Sm) z) 1 3 = ((smS z / smU z : ℝ) : ℂ) ∧
    classC .Sm (symanzikMatrix (classAlpha .Sm) z) 2 3 = ((spzb z / smU z : ℝ) : ℂ) := by
  simp only [classC, contrC, Fin.sum_univ_two, inv_symanzikMatrix_Sm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [castLoopMatrix, class5LoopMatrixPV, QED.Integration.TwoLoop.class5LoopMatrix, ladderLines,
      smS] <;> ring

theorem smT2_combination (z : Fin 8 → ℝ) :
    classC .Sm (symanzikMatrix (classAlpha .Sm) z) 0 1 *
        (2 * pwJ qJ0.gam qJ1.gam rJ.gamT (PJ.c 1) ((smSlotJ z 2).gam.mul (smSlotJ z 3))) +
      classC .Sm (symanzikMatrix (classAlpha .Sm) z) 0 2 *
        (2 * pwJ (((smSlotJ z 3).mul qJ0.gam).gam) (((smSlotJ z 3).mul qJ1.gam).gam)
          (((smSlotJ z 3).mul rJ.gamT).gamT) (PJ.c 1) (smSlotJ z 1)) +
      classC .Sm (symanzikMatrix (classAlpha .Sm) z) 0 3 *
        pwJ qJ0.gam.gam qJ1.gam.gam rJ.gamT.gamT (PJ.c 1) ((smSlotJ z 1).mul (smSlotJ z 2).gam) +
      classC .Sm (symanzikMatrix (classAlpha .Sm) z) 1 2 *
        (-8 * pwJ qJ0.gam qJ1.gam rJ.gamT (smSlotJ z 0) (smSlotJ z 3)) +
      classC .Sm (symanzikMatrix (classAlpha .Sm) z) 1 3 *
        pwJ qJ0.gam qJ1.gam rJ.gamT (smSlotJ z 0) (smSlotJ z 2).gam.gam +
      classC .Sm (symanzikMatrix (classAlpha .Sm) z) 2 3 *
        (-8 * pwJ qJ0.gam qJ1.gam rJ.gamT (smSlotJ z 0) (smSlotJ z 1)) =
    ((3072 * smT z * smX z * (smS z / smU z) - 3072 * smT z * (smS z / smU z) -
        3072 * smT0 z * smV z * (smS z / smU z) + 3072 * smT0 z * (smS z / smU z) -
        1024 * smV z * smX z * (smS z / smU z) + 2048 * smV z * (smS z / smU z) +
        5120 * smX z ^ 2 * (spzb z / smU z) - 5120 * smX z * (spzb z / smU z) -
        5120 * smX z * (smS z / smU z) + 4096 * (smS z / smU z) : ℝ) : ℂ) := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := classC_Sm_val z
  rw [h01, h02, h03, h12, h13, h23]
  simp only [smSlotJ, pwJ_Sm_01, pwJ_Sm_02, pwJ_Sm_03, pwJ_Sp_23, pwJ_Sm_13, smSlotA, smSlotB,
    smX, smV, smT, smT0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  ring

/-- **The jet of `T₂` of `S₋`**. -/
theorem hasJet2_smT2 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : smU z ≠ 0) :
    HasJet2 (classT2 .Sm permSm P z) 0 0 (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
      ((spza z * smS z * (3 * smY z * smU z + 2 * smS z * spza z * spzb z) / smU z ^ 5 : ℝ) :
        ℂ)) := by
  have hq0 := HasPJ.gam (x := qJ0) (jet_lQ0 hm)
  have hq1 := HasPJ.gam (x := qJ1) (jet_lQ1 hm)
  have hr := HasPJ.gamT (x := rJ) (jet_lR hm)
  have h₁ := hasJet2_pwPl hq0 hq1 hr (HasPJ.const 1) ((jet_smE hm z 2).gam.mul (jet_smE hm z 3))
  have h₂ := hasJet2_pwPl ((jet_smE hm z 3).mul hq0).gam ((jet_smE hm z 3).mul hq1).gam
    ((jet_smE hm z 3).mul hr).gamT (HasPJ.const 1) (jet_smE hm z 1)
  have h₃ := hasJet2_pwPl hq0.gam hq1.gam hr.gamT (HasPJ.const 1)
    ((jet_smE hm z 1).mul (jet_smE hm z 2).gam)
  have h₄ := hasJet2_pwPl hq0 hq1 hr (jet_smE hm z 0) (jet_smE hm z 3)
  have h₅ := hasJet2_pwPl hq0 hq1 hr (jet_smE hm z 0) (jet_smE hm z 2).gam.gam
  have h₆ := hasJet2_pwPl hq0 hq1 hr (jet_smE hm z 0) (jet_smE hm z 1)
  have h := (((((((h₁.const_mul 2).const_mul
      (classC .Sm (symanzikMatrix (classAlpha .Sm) z) 0 1)).add
    ((h₂.const_mul 2).const_mul (classC .Sm (symanzikMatrix (classAlpha .Sm) z) 0 2))).add
    (h₃.const_mul (classC .Sm (symanzikMatrix (classAlpha .Sm) z) 0 3))).add
    ((h₄.const_mul (-8)).const_mul (classC .Sm (symanzikMatrix (classAlpha .Sm) z) 1 2))).add
    (h₅.const_mul (classC .Sm (symanzikMatrix (classAlpha .Sm) z) 1 3))).add
    ((h₆.const_mul (-8)).const_mul (classC .Sm (symanzikMatrix (classAlpha .Sm) z) 2 3))).const_mul
    (ladderK P * ((symanzikU (classAlpha .Sm) z ^ 2 : ℝ) : ℂ)⁻¹)
  refine (h.congr fun u => classT2_Sm_planar P z u).of_eq (fun _ => rfl) ?_ ?_ ?_
  · simp
  · simp
  have hc := smT2_combination z
  simp only [smSlotJ] at hc
  rw [hc, smPsi2_identity hU, ladderK_eq he, symanzikU_Sm, kConst]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hU' : (smU z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU
  push_cast
  field_simp
  ring

/-- **The second-order coefficient of `T₂` of `S₋`**. -/
theorem secondCoeff_smT2 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : smU z ≠ 0) :
    secondCoeff (classT2 .Sm permSm P z) = ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
      ((spza z * smS z * (3 * smY z * smU z + 2 * smS z * spza z * spzb z) / smU z ^ 5 : ℝ) :
        ℂ) :=
  (hasJet2_smT2 hm he hU).secondCoeff_eq

/-- **The jet of `T₃` of `S₋` vanishes**. -/
theorem hasJet2_smT3 {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) :
    HasJet2 (classT3 .Sm permSm P z) 0 0 0 := by
  have h₁ := hasJet2_pwPl (HasPJ.gam (x := qJ0) (jet_lQ0 hm)) (HasPJ.gam (x := qJ1) (jet_lQ1 hm))
    (HasPJ.gamT (x := rJ) (jet_lR hm)) (HasPJ.const 1) (HasPJ.const 1)
  set C := fun k l => classC .Sm (symanzikMatrix (classAlpha .Sm) z) k l
  have h := (((((h₁.const_mul (-16)).const_mul (C 0 1 * C 2 3)).add
    ((h₁.const_mul 8).const_mul (C 0 2 * C 1 3))).add
    ((h₁.const_mul (-16)).const_mul (C 0 3 * C 1 2))).const_mul (1 / 4)).const_mul
    (ladderK P * ((symanzikU (classAlpha .Sm) z ^ 2 : ℝ) : ℂ)⁻¹)
  refine (h.congr fun u => classT3_Sm_planar P z u).of_eq (fun _ => rfl) ?_ ?_ ?_ <;>
    simp [pwJ_Sp_T3]

/-- **The second-order coefficient of `T₃` of `S₋` vanishes.** -/
theorem secondCoeff_smT3 {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) :
    secondCoeff (classT3 .Sm permSm P z) = 0 :=
  (hasJet2_smT3 hm z).secondCoeff_eq

/-! ### The second-order coefficient of the projected numerator -/

@[fun_prop] theorem continuous_pvMomentaE_Sm (r : Fin 4 → ℝ) (i : Fin 8) (μ : Fin 4) :
    Continuous fun p' : Fin 4 → ℝ => pvMomentaE .Sm r p' i μ := by
  fin_cases i <;>
    simp [pvMomentaE, extMomenta, QED.Integration.TwoLoop.classCmSmMomenta,
      QED.Integration.TwoLoop.pvLines] <;> fun_prop

theorem continuous_smV (r : Fin 4 → ℝ) (M z : Fin 8 → ℝ) :
    Continuous fun p' : Fin 4 → ℝ => symanzikV (classAlpha .Sm) (pvMomentaE .Sm r p') M z := by
  unfold symanzikV symanzikVector QED.Minkowski.dot
  fun_prop

/-- The second Symanzik function of `S₋` along the curve tends to its value at `q = 0`. -/
theorem tendsto_smV (P : Params) (x : Fin 7 → ℝ) :
    Tendsto (fun u => ((symanzikV (classAlpha .Sm) (classMom .Sm P u) (pvMasses P)
        (simplexPoint x) : ℝ) : ℂ))
      (𝓝 0) (𝓝 ((openV .Sm P x : ℝ) : ℂ)) := by
  have h := ((continuous_smV (restMomentum P.m) (pvMasses P) (simplexPoint x)).tendsto
    (restMomentum P.m)).comp (tendsto_curveMomentum P.m)
  exact (Complex.continuous_ofReal.tendsto _).comp h

theorem Sm_mem_openClasses : Class5.Sm ∈ QED.TwoLoop.ClassIntegrable.openClasses := by decide

/-- **The jet of the projected `S₋` numerator**: `N(x, u) = c₂ u² + o(u²)` with
`c₂ = c₂[T₁] + c₂[T₂] V(x)`. -/
theorem hasJet2_openNum_Sm {P : Params} (hm : P.m = 1) (he : P.e = 1) (x : Fin 7 → ℝ)
    (hU : smU (simplexPoint x) ≠ 0) :
    HasJet2 (openNum .Sm P x) 0 0
      (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
          ((-(spza (simplexPoint x) * smS (simplexPoint x) * sma (simplexPoint x) ^ 2 *
              (2 * smU (simplexPoint x) + spza (simplexPoint x) * spzb (simplexPoint x))) /
            (2 * smU (simplexPoint x) ^ 6) : ℝ) : ℂ) +
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
          ((spza (simplexPoint x) * smS (simplexPoint x) *
              (3 * smY (simplexPoint x) * smU (simplexPoint x) +
                2 * smS (simplexPoint x) * spza (simplexPoint x) * spzb (simplexPoint x)) /
            smU (simplexPoint x) ^ 5 : ℝ) : ℂ) * ((openV .Sm P x : ℝ) : ℂ)) := by
  have hV := tendsto_smV P x
  have h := ((hasJet2_smT1 hm he hU).add (hasJet2_mul_tendsto (hasJet2_smT2 hm he hU) hV)).add
    (hasJet2_mul_tendsto (hasJet2_smT3 hm (simplexPoint x)) (hV.pow 2))
  exact h.of_eq (fun u => openNum_eq_T_of_chain isChainForm_Sm classMomE_Sm_eq Sm_mem_openClasses
    P x u) (by ring) (by ring) (by ring)

/-- **The second-order coefficient of the projected `S₋` numerator.** -/
theorem secondCoeff_openNum_Sm {P : Params} (hm : P.m = 1) (he : P.e = 1) (x : Fin 7 → ℝ)
    (hU : smU (simplexPoint x) ≠ 0) :
    secondCoeff (openNum .Sm P x) =
      ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
          ((-(spza (simplexPoint x) * smS (simplexPoint x) * sma (simplexPoint x) ^ 2 *
              (2 * smU (simplexPoint x) + spza (simplexPoint x) * spzb (simplexPoint x))) /
            (2 * smU (simplexPoint x) ^ 6) : ℝ) : ℂ) +
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
          ((spza (simplexPoint x) * smS (simplexPoint x) *
              (3 * smY (simplexPoint x) * smU (simplexPoint x) +
                2 * smS (simplexPoint x) * spza (simplexPoint x) * spzb (simplexPoint x)) /
            smU (simplexPoint x) ^ 5 : ℝ) : ℂ) * ((openV .Sm P x : ℝ) : ℂ) :=
  (hasJet2_openNum_Sm hm he x hU).secondCoeff_eq

/-- Almost every point of the simplex has `U ≠ 0` (for `S₋`). -/
theorem ae_smU_ne_zero : ∀ᵐ x ∂(MeasureTheory.volume.restrict
    (QED.Integration.Feynman.simplexSet 7)),
    smU (simplexPoint x) ≠ 0 := by
  have hsman : ∃ i j, classAlpha .Sm i 0 * classAlpha .Sm j 1 -
      classAlpha .Sm i 1 * classAlpha .Sm j 0 ≠ 0 :=
    ⟨0, 1, by simp [castLoopMatrix, class5LoopMatrixPV, QED.Integration.TwoLoop.class5LoopMatrix]⟩
  filter_upwards [QED.Integration.TwoLoop.ae_posDef (classAlpha .Sm) (by norm_num) hsman] with x hx
  rw [← symanzikU_Sm]
  exact hx.2.det_pos.ne'

/-- **The `S₋` class value with the explicit integrand**: at `m = 1`, `e = 1`,
`openZero .Sm P = ∫_{Δ₇} (c₂[T₁] + c₂[T₂] V)/V⁴` with
`c₂[T₁] = (Λ² - m_γ²)² (6/K) (-z_a s a² (2U + z_a z_b)/(2U⁶))` and
`c₂[T₂] = (Λ² - m_γ²)² (2/K) z_a s (3 Y U + 2 s z_a z_b)/U⁵`. -/
theorem openZero_Sm_eq {P : Params} (hm : P.m = 1) (he : P.e = 1) :
    openZero .Sm P = ∫ x in QED.Integration.Feynman.simplexSet 7,
      (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
          ((-(spza (simplexPoint x) * smS (simplexPoint x) * sma (simplexPoint x) ^ 2 *
              (2 * smU (simplexPoint x) + spza (simplexPoint x) * spzb (simplexPoint x))) /
            (2 * smU (simplexPoint x) ^ 6) : ℝ) : ℂ) +
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
          ((spza (simplexPoint x) * smS (simplexPoint x) *
              (3 * smY (simplexPoint x) * smU (simplexPoint x) +
                2 * smS (simplexPoint x) * spza (simplexPoint x) * spzb (simplexPoint x)) /
            smU (simplexPoint x) ^ 5 : ℝ) : ℂ) * ((openV .Sm P x : ℝ) : ℂ)) /
        ((openV .Sm P x : ℝ) : ℂ) ^ 4 := by
  unfold openZero
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [ae_smU_ne_zero] with x hx
  rw [secondCoeff_openNum_Sm hm he x hx]

end QED.TwoLoop.UnitSCGraph

end
