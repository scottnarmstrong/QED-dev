/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCGraphCpTrace
public import QED.TwoLoop.UnitSCGraphSpData
import Mathlib.Tactic.Ring

/-!
# The planar data of the corner class `C₊`

Section 8 of `docs/TWO-LOOP-UNITS.md`, stage 1 of the `S + C` link, graph half. The momenta of
`C₊` at the shifted loop point lie in the plane of `p = (m, 0, 0, 0)` and `p'`:

* the loop shift is `S_s = σ_s p + τ_s p'` with `σ_s = ((A⁻¹)_{s0} + (A⁻¹)_{s1}) z₀`,
  `τ_s = (A⁻¹)_{s0} (z₁ + z₂) + (A⁻¹)_{s1} (z₁ - z₃)` (`loopShift_Cp`; line `0` carries `p`,
  lines `1, 2, 3` carry `p'`), so the momentum of chain slot `k` is `qₖ = aₖ p + bₖ p'`
  (`cpQ_apply`);
* the families of `QED/TwoLoop/UnitSCGraphCpTrace.lean` are planar (`planarPauli_hfam`, …), so
  the three coefficients `T₁, T₂, T₃` are planar expressions `ppPl`, `pwPl`
  (`classT1_Cp_planar`, `classT2_Cp_planar`, `classT3_Cp_planar`);
* their second-order jets along the curve (at `m = 1`) are explicit polynomials in
  `αₖ = aₖ + bₖ`, `βₖ = bₖ` (`ppJ_Cp_T1`, …, `pwJ_Cp_T3`; the polynomials were generated and
  checked against exact Dirac traces by `scripts/numerics/sc_graph/cp_planar.py`).
-/

@[expose] public section

open Complex Matrix
open scoped Real

namespace QED.TwoLoop.UnitSCGraph

open QED.Dirac QED.WickModel QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero
open QED.TwoLoop.Bridge QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.TwoLoop.ParamNumEval QED.TwoLoop.UnitLGraph QED.TwoLoop.UnitLGraphTrace
open QED.TwoLoop.Enumeration
open QED.Integration.TwoLoop (castLoopMatrix class5LoopMatrixPV symanzikV symanzikU symanzikMatrix
  lineMomentum loopShift)
open Pl

/-- The identity matrix. -/
local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-! ### The loop shift and the slot momenta -/

/-- The coefficient of `p` in the loop shift `S_s` of `C₊`. -/
noncomputable def cpSigP (z : Fin 8 → ℝ) (s : Fin 2) : ℝ :=
  (symanzikMatrix (classAlpha .Cp) z)⁻¹ s 0 * z 0 + (symanzikMatrix (classAlpha .Cp) z)⁻¹ s 1 * z 0

/-- The coefficient of `p'` in the loop shift `S_s` of `C₊`. -/
noncomputable def cpSigQ (z : Fin 8 → ℝ) (s : Fin 2) : ℝ :=
  (symanzikMatrix (classAlpha .Cp) z)⁻¹ s 0 * (z 1 + z 2) +
    (symanzikMatrix (classAlpha .Cp) z)⁻¹ s 1 * (z 1 - z 3)

/-- **The loop shift of `C₊`**: `S_s = σ_s p + τ_s p'`. -/
theorem loopShift_Cp (p p' : Fin 4 → ℝ) (z : Fin 8 → ℝ) (s : Fin 2) (μ : Fin 4) :
    loopShift (classAlpha .Cp) (pvMomentaE .Cp p p') z s μ = cpSigP z s * p μ + cpSigQ z s * p' μ := by
  rw [QED.TwoLoop.LimitCovariance.loopShift_apply]
  simp [Fin.sum_univ_succ, castLoopMatrix, class5LoopMatrixPV,
    QED.Integration.TwoLoop.class5LoopMatrix, pvMomentaE, extMomenta,
    QED.Integration.TwoLoop.classCpSpMomenta, QED.Integration.TwoLoop.pvLines, cpSigP, cpSigQ]
  ring

/-- The coefficient of `p` in the slot momentum `qₖ` of `C₊`. -/
noncomputable def cpSlotA (z : Fin 8 → ℝ) : Fin 4 → ℝ :=
  ![cpSigP z 1, -cpSigP z 0, -(cpSigP z 0 + cpSigP z 1), 1 - (cpSigP z 0 + cpSigP z 1)]

/-- The coefficient of `p'` in the slot momentum `qₖ` of `C₊`. -/
noncomputable def cpSlotB (z : Fin 8 → ℝ) : Fin 4 → ℝ :=
  ![1 + cpSigQ z 1, 1 - cpSigQ z 0, 1 - (cpSigQ z 0 + cpSigQ z 1), -(cpSigQ z 0 + cpSigQ z 1)]

/-- **The slot momenta of `C₊`**: `qₖ = aₖ p + bₖ p'`. -/
theorem cpQ_apply (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) (μ : Fin 4) :
    classQ .Cp P z u k μ =
      cpSlotA z k * restMomentum P.m μ + cpSlotB z k * curveMomentum P.m u μ := by
  simp only [classQ, QED.Integration.TwoLoop.lineMomentum, Pi.neg_apply, loopShift_Cp]
  fin_cases k <;>
    simp [Fin.sum_univ_two, castLoopMatrix, class5LoopMatrixPV,
      QED.Integration.TwoLoop.class5LoopMatrix, ladderLines, pvMomentaE, extMomenta,
      QED.Integration.TwoLoop.classCpSpMomenta, QED.Integration.TwoLoop.pvLines, cpSlotA,
      cpSlotB] <;>
    ring

theorem cpQ_two (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) : classQ .Cp P z u k 2 = 0 := by
  rw [cpQ_apply, restMomentum_two, curveMomentum_two]; ring

theorem cpQ_three (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) : classQ .Cp P z u k 3 = 0 := by
  rw [cpQ_apply, restMomentum_three, curveMomentum_three]; ring

theorem cpE_planar (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) :
    classE .Cp P z u k = toMat (ePl P.m (classQ .Cp P z u k)) :=
  electronNumerator_ePl P.m (cpQ_two P z u k) (cpQ_three P z u k)

/-! ### The planar families -/

/-- The family `K(Y₁)` split into closure operations. -/
theorem pp_kfam (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₁ W Z : Matrix (Fin 4) (Fin 4) ℂ) :
    pp P (kfam Y₁) W Z = -pp P (contractP (contractP (mulRightP gammaLower Y₁))) W Z +
      8 * pp P (mulRightP gammaLower Y₁) W Z := by
  have h : kfam Y₁ = fun ν => -contractP (contractP (mulRightP gammaLower Y₁)) ν +
      (8 : ℂ) • mulRightP gammaLower Y₁ ν := rfl
  rw [h, pp_add, pp_neg, pp_smul]

section PlanarPP

variable {P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {Q₀ Q₁ R : Pl} (hP : PlanarPauli P Q₀ Q₁ R)
include hP

theorem pp_hfam_planar (y₀ y₁ w z : Pl) :
    pp P (hfam (toMat y₀) (toMat y₁)) (toMat w) (toMat z) =
      ppPl Q₀ Q₁ R (gam (y₀ * g0L * y₁)) (gam (y₀ * g1 * y₁)) (gamT (y₀ * 1 * bar y₁)) w z :=
  pp_planar hP (planarPauli_hfam y₀ y₁) w z

theorem pp_gammaLower_planar (w z : Pl) :
    pp P gammaLower (toMat w) (toMat z) = ppPl Q₀ Q₁ R g0L g1 1 w z :=
  pp_planar hP planarPauli_gammaLower w z

theorem pp_gl_planar (y w z : Pl) :
    pp P (mulRightP gammaLower (toMat y)) (toMat w) (toMat z) =
      ppPl Q₀ Q₁ R (g0L * y) (g1 * y) (1 * bar y) w z :=
  pp_planar hP (planarPauli_mulRightP planarPauli_gammaLower y) w z

theorem pp_glcc_planar (y w z : Pl) :
    pp P (contractP (contractP (mulRightP gammaLower (toMat y)))) (toMat w) (toMat z) =
      ppPl Q₀ Q₁ R (gam (gam (g0L * y))) (gam (gam (g1 * y))) (gamT (gamT (1 * bar y))) w z :=
  pp_planar hP (planarPauli_contractP (planarPauli_contractP
    (planarPauli_mulRightP planarPauli_gammaLower y))) w z

end PlanarPP

/-! ### The three coefficients as planar expressions -/

section PlanarT

variable (P : Params) (z : Fin 8 → ℝ) (u : ℝ)

/-- The planar electron numerators of the chain slots of `C₊`. -/
noncomputable abbrev cpE (k : Fin 4) : Pl := ePl P.m (classQ .Cp P z u k)

/-- **`T₁` of `C₊` as a planar expression.** -/
theorem classT1_Cp_planar : classT1 .Cp permCp P z u =
    ladderK P * ((symanzikU (classAlpha .Cp) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (6 * ppPl (lQ0 P u) (lQ1 P u) (lR P u) (gam (cpE P z u 0 * g0L * cpE P z u 1))
        (gam (cpE P z u 0 * g1 * cpE P z u 1)) (gamT (cpE P z u 0 * 1 * bar (cpE P z u 1)))
        (cpE P z u 2) (cpE P z u 3)) := by
  rw [classT1_Cp_eq]
  simp only [cpE_planar]
  rw [pp_hfam_planar (planarPauli_ladder P u)]

/-- **`T₂` of `C₊` as a planar expression.** -/
theorem classT2_Cp_planar : classT2 .Cp permCp P z u =
    ladderK P * ((symanzikU (classAlpha .Cp) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (classC .Cp (symanzikMatrix (classAlpha .Cp) z) 0 1 *
          (4 * ppPl (lQ0 P u) (lQ1 P u) (lR P u) g0L g1 1 (cpE P z u 2) (cpE P z u 3)) +
        classC .Cp (symanzikMatrix (classAlpha .Cp) z) 0 2 *
          (-ppPl (lQ0 P u) (lQ1 P u) (lR P u) (gam (gam (g0L * cpE P z u 1)))
              (gam (gam (g1 * cpE P z u 1))) (gamT (gamT (1 * bar (cpE P z u 1)))) 1 (cpE P z u 3) +
            8 * ppPl (lQ0 P u) (lQ1 P u) (lR P u) (g0L * cpE P z u 1) (g1 * cpE P z u 1)
              (1 * bar (cpE P z u 1)) 1 (cpE P z u 3)) +
        classC .Cp (symanzikMatrix (classAlpha .Cp) z) 0 3 *
          (ppPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) (gam (1 * g0L * cpE P z u 1))
              (gam (1 * g1 * cpE P z u 1)) (gamT (1 * 1 * bar (cpE P z u 1))) (cpE P z u 2) 1 +
            4 * pwPl (lQ0 P u) (lQ1 P u) (lR P u) (gam (cpE P z u 1) * cpE P z u 2) 1 +
            2 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u))
              (cpE P z u 1 * gam (cpE P z u 2)) 1 +
            4 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) (cpE P z u 1) (cpE P z u 2)) +
        classC .Cp (symanzikMatrix (classAlpha .Cp) z) 1 2 *
          (2 * ppPl (lQ0 P u) (lQ1 P u) (lR P u) (gam (cpE P z u 0 * g0L * 1))
            (gam (cpE P z u 0 * g1 * 1)) (gamT (cpE P z u 0 * 1 * bar 1)) 1 (cpE P z u 3)) +
        classC .Cp (symanzikMatrix (classAlpha .Cp) z) 1 3 *
          (ppPl (lQ0 P u) (lQ1 P u) (lR P u) (gam (cpE P z u 0 * g0L * 1))
              (gam (cpE P z u 0 * g1 * 1)) (gamT (cpE P z u 0 * 1 * bar 1)) (gam (cpE P z u 2)) 1 +
            2 * ppPl (lQ0 P u) (lQ1 P u) (lR P u) (gam (cpE P z u 0 * g0L * 1))
              (gam (cpE P z u 0 * g1 * 1)) (gamT (cpE P z u 0 * 1 * bar 1)) 1 (cpE P z u 2) +
            2 * ppPl (lQ0 P u) (lQ1 P u) (lR P u) (gam (cpE P z u 0 * g0L * cpE P z u 2))
              (gam (cpE P z u 0 * g1 * cpE P z u 2)) (gamT (cpE P z u 0 * 1 * bar (cpE P z u 2)))
              1 1 +
            4 * pwPl (lQ0 P u) (lQ1 P u) (lR P u) 1 (cpE P z u 0 * gam (cpE P z u 2))) +
        classC .Cp (symanzikMatrix (classAlpha .Cp) z) 2 3 *
          (2 * ppPl (lQ0 P u) (lQ1 P u) (lR P u) (gam (cpE P z u 0 * g0L * cpE P z u 1))
            (gam (cpE P z u 0 * g1 * cpE P z u 1)) (gamT (cpE P z u 0 * 1 * bar (cpE P z u 1)))
            1 1)) := by
  have hP := planarPauli_ladder P u
  have hPS := planarPauli_contractP hP
  rw [classT2_Cp_eq, pp_kfam]
  simp only [cpE_planar, gamM_toMat, toMat_mul]
  rw [← toMat_one]
  simp only [pp_hfam_planar hP, pp_hfam_planar hPS, pp_gammaLower_planar hP, pp_gl_planar hP,
    pp_glcc_planar hP, pw_planar hP, pw_planar hPS]

/-- **`T₃` of `C₊` as a planar expression.** -/
theorem classT3_Cp_planar : classT3 .Cp permCp P z u =
    ladderK P * ((symanzikU (classAlpha .Cp) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (1 / 4 * (classC .Cp (symanzikMatrix (classAlpha .Cp) z) 0 1 *
          classC .Cp (symanzikMatrix (classAlpha .Cp) z) 2 3 *
            (16 * pwPl (lQ0 P u) (lQ1 P u) (lR P u) 1 1) +
        classC .Cp (symanzikMatrix (classAlpha .Cp) z) 0 2 *
          classC .Cp (symanzikMatrix (classAlpha .Cp) z) 1 3 *
            (-32 * pwPl (lQ0 P u) (lQ1 P u) (lR P u) 1 1) +
        classC .Cp (symanzikMatrix (classAlpha .Cp) z) 0 3 *
          classC .Cp (symanzikMatrix (classAlpha .Cp) z) 1 2 *
            (-32 * pwPl (lQ0 P u) (lQ1 P u) (lR P u) 1 1))) := by
  rw [classT3_Cp_eq, ← toMat_one, pw_planar (planarPauli_ladder P u)]

end PlanarT

/-! ### The jets of the slot numerators -/

/-- **The jet of a slot numerator of `C₊`**: `cpE k = (1, aₖ + bₖ p'⁰, -bₖ p'¹, 0)`. -/
theorem jet_cpE {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) (k : Fin 4) :
    HasPJ (fun u => cpE P z u k) (eJ ((cpSlotA z k : ℂ) + (cpSlotB z k : ℂ)) (cpSlotB z k : ℂ)) :=
  (HasPlJet.mk (HasJet2.const 1) ((HasJet2.const (cpSlotA z k : ℂ)).add
    (jet_P0.const_mul (cpSlotB z k : ℂ))) (jet_P1.const_mul (cpSlotB z k : ℂ)).neg
    (HasJet2.const 0)).of_eq
    (fun u => by
      ext <;> simp [cpE, ePl, cpQ_apply, hm, restMomentum])
    (by ext <;> simp [eJ]) (by ext <;> simp [eJ, mul_comm]) (by ext <;> simp [eJ, mul_comm])

/-! ### The second-order coefficients of the patterns -/

section Values

variable (α₀ α₁ α₂ α₃ β₀ β₁ β₂ β₃ : ℂ)

theorem ppJ_Cp_T1 : ppJ qJ0 qJ1 rJ (((eJ α₀ β₀).mul (PJ.c g0L)).mul (eJ α₁ β₁)).gam (((eJ α₀ β₀).mul (PJ.c g1)).mul (eJ α₁ β₁)).gam (((eJ α₀ β₀).mul (PJ.c 1)).mul (eJ α₁ β₁).bar).gamT (eJ α₂ β₂) (eJ α₃ β₃) =
    512*α₀*α₁*α₂*α₃ - 512*α₀*α₁*α₂ - 512*α₀*α₁*β₂ + 512*α₀*α₁*β₃ + 512*α₀*α₁ - 512*α₀*α₂*α₃ + 512*α₀*α₂*β₁ - 512*α₀*α₂*β₃ - 512*α₀*α₂ - 512*α₀*α₃*β₁ + 512*α₀*α₃*β₂ + 512*α₀*β₂ - 512*α₀*β₃ - 512*α₁*α₂*α₃ + 512*α₁*α₂*β₀ - 512*α₁*α₂*β₃ - 512*α₁*α₂ - 512*α₁*α₃*β₀ + 512*α₁*α₃*β₂ + 512*α₁*β₂ - 512*α₁*β₃ + 512*α₂*α₃*β₀ + 512*α₂*α₃*β₁ - 512*α₂*α₃ - 512*α₂*β₀ - 512*α₂*β₁ + 512*α₂*β₃ + 512*α₂ + 512*α₃*β₀ + 512*α₃*β₁ - 512*α₃*β₂ + 512*α₃ - 512*β₀ - 512*β₁ := by
  simp [ppJ, ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, g0L]
  ring

theorem ppJ_Cp_01 : ppJ qJ0 qJ1 rJ (PJ.c g0L) (PJ.c g1) (PJ.c 1) (eJ α₂ β₂) (eJ α₃ β₃) =
    -256*α₂*α₃ + 256*α₂*β₃ + 256*α₂ - 256*α₃*β₂ + 256*α₃ := by
  simp [ppJ, ppJk, PJ.mul, PJ.bar, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, g0L]
  ring

theorem ppJ_Cp_02a : ppJ qJ0 qJ1 rJ ((PJ.c g0L).mul (eJ α₁ β₁)).gam.gam ((PJ.c g1).mul (eJ α₁ β₁)).gam.gam ((PJ.c 1).mul (eJ α₁ β₁).bar).gamT.gamT (PJ.c 1) (eJ α₃ β₃) =
    2048*α₁*β₃ - 2048*α₃*β₁ + 1024*α₃ + 2048*β₁ := by
  simp [ppJ, ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, g0L]
  ring

theorem ppJ_Cp_02b : ppJ qJ0 qJ1 rJ ((PJ.c g0L).mul (eJ α₁ β₁)) ((PJ.c g1).mul (eJ α₁ β₁)) ((PJ.c 1).mul (eJ α₁ β₁).bar) (PJ.c 1) (eJ α₃ β₃) =
    -256*α₁*α₃ + 256*α₁*β₃ + 256*α₁ - 256*α₃*β₁ + 256*α₃ := by
  simp [ppJ, ppJk, PJ.mul, PJ.bar, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, g0L]
  ring

theorem ppJ_Cp_03a : ppJ qJ0.gam qJ1.gam rJ.gamT (((PJ.c 1).mul (PJ.c g0L)).mul (eJ α₁ β₁)).gam (((PJ.c 1).mul (PJ.c g1)).mul (eJ α₁ β₁)).gam (((PJ.c 1).mul (PJ.c 1)).mul (eJ α₁ β₁).bar).gamT (eJ α₂ β₂) (PJ.c 1) =
    -1024*α₁*α₂ - 1024*α₁*β₂ + 1024*α₁ + 1024*α₂*β₁ - 2048*α₂ := by
  simp [ppJ, ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, g0L]
  ring

theorem pwJ_Cp_03b : pwJ qJ0 qJ1 rJ ((eJ α₁ β₁).gam.mul (eJ α₂ β₂)) (PJ.c 1) =
    256*α₁*β₂ - 256*α₁ - 256*α₂*β₁ + 512*α₂ + 256*β₁ - 512*β₂ := by
  simp [pwJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1]
  ring

theorem pwJ_Cp_03c : pwJ qJ0.gam qJ1.gam rJ.gamT ((eJ α₁ β₁).mul (eJ α₂ β₂).gam) (PJ.c 1) =
    -512*α₁*β₂ - 1024*α₁ + 512*α₂*β₁ + 512*α₂ := by
  simp [pwJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1]
  ring

theorem pwJ_Cp_03d : pwJ qJ0.gam qJ1.gam rJ.gamT (eJ α₁ β₁) (eJ α₂ β₂) =
    -256*α₁*α₂ + 256*α₁*β₂ + 256*α₁ - 256*α₂*β₁ + 256*α₂ := by
  simp [pwJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1]
  ring

theorem ppJ_Cp_12 : ppJ qJ0 qJ1 rJ (((eJ α₀ β₀).mul (PJ.c g0L)).mul (PJ.c 1)).gam (((eJ α₀ β₀).mul (PJ.c g1)).mul (PJ.c 1)).gam (((eJ α₀ β₀).mul (PJ.c 1)).mul (PJ.c 1).bar).gamT (PJ.c 1) (eJ α₃ β₃) =
    -512*α₀*β₃ + 512*α₃*β₀ + 512*α₃ - 512*β₀ := by
  simp [ppJ, ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, g0L]
  ring

theorem ppJ_Cp_13a : ppJ qJ0 qJ1 rJ (((eJ α₀ β₀).mul (PJ.c g0L)).mul (PJ.c 1)).gam (((eJ α₀ β₀).mul (PJ.c g1)).mul (PJ.c 1)).gam (((eJ α₀ β₀).mul (PJ.c 1)).mul (PJ.c 1).bar).gamT (eJ α₂ β₂).gam (PJ.c 1) =
    -1024*α₀*α₂ + 1024*α₀*β₂ - 1024*α₂*β₀ + 1024*α₂ + 2048*β₀ := by
  simp [ppJ, ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, g0L]
  ring

theorem ppJ_Cp_13b : ppJ qJ0 qJ1 rJ (((eJ α₀ β₀).mul (PJ.c g0L)).mul (PJ.c 1)).gam (((eJ α₀ β₀).mul (PJ.c g1)).mul (PJ.c 1)).gam (((eJ α₀ β₀).mul (PJ.c 1)).mul (PJ.c 1).bar).gamT (PJ.c 1) (eJ α₂ β₂) =
    -512*α₀*β₂ + 512*α₂*β₀ + 512*α₂ - 512*β₀ := by
  simp [ppJ, ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, g0L]
  ring

theorem ppJ_Cp_13c : ppJ qJ0 qJ1 rJ (((eJ α₀ β₀).mul (PJ.c g0L)).mul (eJ α₂ β₂)).gam (((eJ α₀ β₀).mul (PJ.c g1)).mul (eJ α₂ β₂)).gam (((eJ α₀ β₀).mul (PJ.c 1)).mul (eJ α₂ β₂).bar).gamT (PJ.c 1) (PJ.c 1) =
    512*α₀*α₂ - 512*β₀ - 512*β₂ := by
  simp [ppJ, ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, g0L]
  ring

theorem pwJ_Cp_13d : pwJ qJ0 qJ1 rJ (PJ.c 1) ((eJ α₀ β₀).mul (eJ α₂ β₂).gam) =
    256*α₀*β₂ - 256*α₂*β₀ + 512*β₀ - 256*β₂ := by
  simp [pwJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1]
  ring

theorem ppJ_Cp_23 : ppJ qJ0 qJ1 rJ (((eJ α₀ β₀).mul (PJ.c g0L)).mul (eJ α₁ β₁)).gam (((eJ α₀ β₀).mul (PJ.c g1)).mul (eJ α₁ β₁)).gam (((eJ α₀ β₀).mul (PJ.c 1)).mul (eJ α₁ β₁).bar).gamT (PJ.c 1) (PJ.c 1) =
    512*α₀*α₁ - 512*β₀ - 512*β₁ := by
  simp [ppJ, ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, g0L]
  ring

theorem pwJ_Cp_T3 : pwJ qJ0 qJ1 rJ (PJ.c 1) (PJ.c 1) = 0 := by
  simp [pwJ, pwJk, PJ.mul, PJ.bar, PJ.c, PJ.s2, qJ0, qJ1, rJ, g0, g1]
  norm_num

/-! The values and first-order coefficients of the patterns vanish. -/

@[simp] theorem ppJk_Cp_T1_s0 : ppJk PJ.s0 qJ0 qJ1 rJ (((eJ α₀ β₀).mul (PJ.c g0L)).mul (eJ α₁ β₁)).gam (((eJ α₀ β₀).mul (PJ.c g1)).mul (eJ α₁ β₁)).gam (((eJ α₀ β₀).mul (PJ.c 1)).mul (eJ α₁ β₁).bar).gamT (eJ α₂ β₂) (eJ α₃ β₃) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1, g0L]

@[simp] theorem ppJk_Cp_T1_s1 : ppJk PJ.s1 qJ0 qJ1 rJ (((eJ α₀ β₀).mul (PJ.c g0L)).mul (eJ α₁ β₁)).gam (((eJ α₀ β₀).mul (PJ.c g1)).mul (eJ α₁ β₁)).gam (((eJ α₀ β₀).mul (PJ.c 1)).mul (eJ α₁ β₁).bar).gamT (eJ α₂ β₂) (eJ α₃ β₃) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1, g0L]

@[simp] theorem ppJk_Cp_01_s0 : ppJk PJ.s0 qJ0 qJ1 rJ (PJ.c g0L) (PJ.c g1) (PJ.c 1) (eJ α₂ β₂) (eJ α₃ β₃) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1, g0L]

@[simp] theorem ppJk_Cp_01_s1 : ppJk PJ.s1 qJ0 qJ1 rJ (PJ.c g0L) (PJ.c g1) (PJ.c 1) (eJ α₂ β₂) (eJ α₃ β₃) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1, g0L]

@[simp] theorem ppJk_Cp_02a_s0 : ppJk PJ.s0 qJ0 qJ1 rJ ((PJ.c g0L).mul (eJ α₁ β₁)).gam.gam ((PJ.c g1).mul (eJ α₁ β₁)).gam.gam ((PJ.c 1).mul (eJ α₁ β₁).bar).gamT.gamT (PJ.c 1) (eJ α₃ β₃) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1, g0L]

@[simp] theorem ppJk_Cp_02a_s1 : ppJk PJ.s1 qJ0 qJ1 rJ ((PJ.c g0L).mul (eJ α₁ β₁)).gam.gam ((PJ.c g1).mul (eJ α₁ β₁)).gam.gam ((PJ.c 1).mul (eJ α₁ β₁).bar).gamT.gamT (PJ.c 1) (eJ α₃ β₃) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1, g0L]

@[simp] theorem ppJk_Cp_02b_s0 : ppJk PJ.s0 qJ0 qJ1 rJ ((PJ.c g0L).mul (eJ α₁ β₁)) ((PJ.c g1).mul (eJ α₁ β₁)) ((PJ.c 1).mul (eJ α₁ β₁).bar) (PJ.c 1) (eJ α₃ β₃) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1, g0L]

@[simp] theorem ppJk_Cp_02b_s1 : ppJk PJ.s1 qJ0 qJ1 rJ ((PJ.c g0L).mul (eJ α₁ β₁)) ((PJ.c g1).mul (eJ α₁ β₁)) ((PJ.c 1).mul (eJ α₁ β₁).bar) (PJ.c 1) (eJ α₃ β₃) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1, g0L]

@[simp] theorem ppJk_Cp_03a_s0 : ppJk PJ.s0 qJ0.gam qJ1.gam rJ.gamT (((PJ.c 1).mul (PJ.c g0L)).mul (eJ α₁ β₁)).gam (((PJ.c 1).mul (PJ.c g1)).mul (eJ α₁ β₁)).gam (((PJ.c 1).mul (PJ.c 1)).mul (eJ α₁ β₁).bar).gamT (eJ α₂ β₂) (PJ.c 1) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1, g0L]

@[simp] theorem ppJk_Cp_03a_s1 : ppJk PJ.s1 qJ0.gam qJ1.gam rJ.gamT (((PJ.c 1).mul (PJ.c g0L)).mul (eJ α₁ β₁)).gam (((PJ.c 1).mul (PJ.c g1)).mul (eJ α₁ β₁)).gam (((PJ.c 1).mul (PJ.c 1)).mul (eJ α₁ β₁).bar).gamT (eJ α₂ β₂) (PJ.c 1) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1, g0L]

@[simp] theorem pwJk_Cp_03b_s0 : pwJk PJ.s0 qJ0 qJ1 rJ ((eJ α₁ β₁).gam.mul (eJ α₂ β₂)) (PJ.c 1) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Cp_03b_s1 : pwJk PJ.s1 qJ0 qJ1 rJ ((eJ α₁ β₁).gam.mul (eJ α₂ β₂)) (PJ.c 1) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Cp_03c_s0 : pwJk PJ.s0 qJ0.gam qJ1.gam rJ.gamT ((eJ α₁ β₁).mul (eJ α₂ β₂).gam) (PJ.c 1) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Cp_03c_s1 : pwJk PJ.s1 qJ0.gam qJ1.gam rJ.gamT ((eJ α₁ β₁).mul (eJ α₂ β₂).gam) (PJ.c 1) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Cp_03d_s0 : pwJk PJ.s0 qJ0.gam qJ1.gam rJ.gamT (eJ α₁ β₁) (eJ α₂ β₂) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Cp_03d_s1 : pwJk PJ.s1 qJ0.gam qJ1.gam rJ.gamT (eJ α₁ β₁) (eJ α₂ β₂) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem ppJk_Cp_12_s0 : ppJk PJ.s0 qJ0 qJ1 rJ (((eJ α₀ β₀).mul (PJ.c g0L)).mul (PJ.c 1)).gam (((eJ α₀ β₀).mul (PJ.c g1)).mul (PJ.c 1)).gam (((eJ α₀ β₀).mul (PJ.c 1)).mul (PJ.c 1).bar).gamT (PJ.c 1) (eJ α₃ β₃) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1, g0L]

@[simp] theorem ppJk_Cp_12_s1 : ppJk PJ.s1 qJ0 qJ1 rJ (((eJ α₀ β₀).mul (PJ.c g0L)).mul (PJ.c 1)).gam (((eJ α₀ β₀).mul (PJ.c g1)).mul (PJ.c 1)).gam (((eJ α₀ β₀).mul (PJ.c 1)).mul (PJ.c 1).bar).gamT (PJ.c 1) (eJ α₃ β₃) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1, g0L]

@[simp] theorem ppJk_Cp_13a_s0 : ppJk PJ.s0 qJ0 qJ1 rJ (((eJ α₀ β₀).mul (PJ.c g0L)).mul (PJ.c 1)).gam (((eJ α₀ β₀).mul (PJ.c g1)).mul (PJ.c 1)).gam (((eJ α₀ β₀).mul (PJ.c 1)).mul (PJ.c 1).bar).gamT (eJ α₂ β₂).gam (PJ.c 1) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1, g0L]

@[simp] theorem ppJk_Cp_13a_s1 : ppJk PJ.s1 qJ0 qJ1 rJ (((eJ α₀ β₀).mul (PJ.c g0L)).mul (PJ.c 1)).gam (((eJ α₀ β₀).mul (PJ.c g1)).mul (PJ.c 1)).gam (((eJ α₀ β₀).mul (PJ.c 1)).mul (PJ.c 1).bar).gamT (eJ α₂ β₂).gam (PJ.c 1) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1, g0L]

@[simp] theorem ppJk_Cp_13c_s0 : ppJk PJ.s0 qJ0 qJ1 rJ (((eJ α₀ β₀).mul (PJ.c g0L)).mul (eJ α₂ β₂)).gam (((eJ α₀ β₀).mul (PJ.c g1)).mul (eJ α₂ β₂)).gam (((eJ α₀ β₀).mul (PJ.c 1)).mul (eJ α₂ β₂).bar).gamT (PJ.c 1) (PJ.c 1) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1, g0L]

@[simp] theorem ppJk_Cp_13c_s1 : ppJk PJ.s1 qJ0 qJ1 rJ (((eJ α₀ β₀).mul (PJ.c g0L)).mul (eJ α₂ β₂)).gam (((eJ α₀ β₀).mul (PJ.c g1)).mul (eJ α₂ β₂)).gam (((eJ α₀ β₀).mul (PJ.c 1)).mul (eJ α₂ β₂).bar).gamT (PJ.c 1) (PJ.c 1) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1, g0L]

@[simp] theorem pwJk_Cp_13d_s0 : pwJk PJ.s0 qJ0 qJ1 rJ (PJ.c 1) ((eJ α₀ β₀).mul (eJ α₂ β₂).gam) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Cp_13d_s1 : pwJk PJ.s1 qJ0 qJ1 rJ (PJ.c 1) ((eJ α₀ β₀).mul (eJ α₂ β₂).gam) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Cp_T3_s0 : pwJk PJ.s0 qJ0 qJ1 rJ (PJ.c 1) (PJ.c 1) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.c, PJ.s0, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Cp_T3_s1 : pwJk PJ.s1 qJ0 qJ1 rJ (PJ.c 1) (PJ.c 1) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.c, PJ.s1, qJ0, qJ1, rJ, g0, g1]

end Values

end QED.TwoLoop.UnitSCGraph

end
