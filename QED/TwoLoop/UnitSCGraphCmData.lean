/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCGraphCmTrace
public import QED.TwoLoop.UnitSCGraphCpData
import Mathlib.Tactic.Ring

/-!
# The planar data of the corner class `C₋`

Section 8 of `docs/TWO-LOOP-UNITS.md`, stage 1 of the `S + C` link, graph half. The momenta of
`C₋` at the shifted loop point lie in the plane of `p = (m, 0, 0, 0)` and `p'`:

* the loop shift is `S_s = σ_s p + τ_s p'` with `σ_s = (A⁻¹)_{s0} (z₀ + z₁) + (A⁻¹)_{s1} (z₂ - z₀)`,
  `τ_s = (A⁻¹)_{s1} z₃` (`loopShift_Cm`; lines `0, 1, 2` carry `p`, line `3` carries `p'`), so the
  momentum of chain slot `k` is `qₖ = aₖ p + bₖ p'` (`cmQ_apply`);
* through the reversal of `QED/TwoLoop/UnitSCGraphCmTrace.lean`, the three coefficients
  `T₁, T₂, T₃` are planar expressions `ppPl`, `pwPl` in the reversed planar data `e^R`, `P^R`
  (`classT1_Cm_planar`, `classT2_Cm_planar`, `classT3_Cm_planar`);
* their second-order jets along the curve (at `m = 1`) are explicit polynomials in
  `αₖ = aₖ + bₖ`, `βₖ = bₖ` (`ppJ_Cm_T1`, …; generated and checked against exact Dirac traces by
  `scripts/numerics/sc_graph/cm_planar.py`).
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

/-- The coefficient of `p` in the loop shift `S_s` of `C₋`. -/
noncomputable def cmSigP (z : Fin 8 → ℝ) (s : Fin 2) : ℝ :=
  (symanzikMatrix (classAlpha .Cm) z)⁻¹ s 0 * (z 0 + z 1) +
    (symanzikMatrix (classAlpha .Cm) z)⁻¹ s 1 * (z 2 - z 0)

/-- The coefficient of `p'` in the loop shift `S_s` of `C₋`. -/
noncomputable def cmSigQ (z : Fin 8 → ℝ) (s : Fin 2) : ℝ :=
  (symanzikMatrix (classAlpha .Cm) z)⁻¹ s 1 * z 3

/-- **The loop shift of `C₋`**: `S_s = σ_s p + τ_s p'`. -/
theorem loopShift_Cm (p p' : Fin 4 → ℝ) (z : Fin 8 → ℝ) (s : Fin 2) (μ : Fin 4) :
    loopShift (classAlpha .Cm) (pvMomentaE .Cm p p') z s μ = cmSigP z s * p μ + cmSigQ z s * p' μ := by
  rw [QED.TwoLoop.LimitCovariance.loopShift_apply]
  simp [Fin.sum_univ_succ, castLoopMatrix, class5LoopMatrixPV,
    QED.Integration.TwoLoop.class5LoopMatrix, pvMomentaE, extMomenta,
    QED.Integration.TwoLoop.classCmSmMomenta, QED.Integration.TwoLoop.pvLines, cmSigP, cmSigQ]
  ring

/-- The coefficient of `p` in the slot momentum `qₖ` of `C₋`. -/
noncomputable def cmSlotA (z : Fin 8 → ℝ) : Fin 4 → ℝ :=
  ![-cmSigP z 1, 1 - cmSigP z 1, 1 - cmSigP z 0, 1 - cmSigP z 0 + cmSigP z 1]

/-- The coefficient of `p'` in the slot momentum `qₖ` of `C₋`. -/
noncomputable def cmSlotB (z : Fin 8 → ℝ) : Fin 4 → ℝ :=
  ![1 - cmSigQ z 1, -cmSigQ z 1, -cmSigQ z 0, -cmSigQ z 0 + cmSigQ z 1]

/-- **The slot momenta of `C₋`**: `qₖ = aₖ p + bₖ p'`. -/
theorem cmQ_apply (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) (μ : Fin 4) :
    classQ .Cm P z u k μ =
      cmSlotA z k * restMomentum P.m μ + cmSlotB z k * curveMomentum P.m u μ := by
  simp only [classQ, QED.Integration.TwoLoop.lineMomentum, Pi.neg_apply, loopShift_Cm]
  fin_cases k <;>
    simp [Fin.sum_univ_two, castLoopMatrix, class5LoopMatrixPV,
      QED.Integration.TwoLoop.class5LoopMatrix, ladderLines, pvMomentaE, extMomenta,
      QED.Integration.TwoLoop.classCmSmMomenta, QED.Integration.TwoLoop.pvLines, cmSlotA,
      cmSlotB] <;>
    ring

theorem cmQ_two (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) : classQ .Cm P z u k 2 = 0 := by
  rw [cmQ_apply, restMomentum_two, curveMomentum_two]; ring

theorem cmQ_three (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) : classQ .Cm P z u k 3 = 0 := by
  rw [cmQ_apply, restMomentum_three, curveMomentum_three]; ring

/-- The planar electron numerators of the chain slots of `C₋`. -/
noncomputable abbrev cmE (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) : Pl :=
  ePl P.m (classQ .Cm P z u k)

/-- The reversed slot numerators are planar. -/
theorem revM_cmE (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) :
    revM (classE .Cm P z u k) = toMat (revPl (cmE P z u k)) := by
  rw [classE_apply, electronNumerator_ePl P.m (cmQ_two P z u k) (cmQ_three P z u k), revM_toMat]

/-! ### The three coefficients as planar expressions -/

section PlanarT

variable (P : Params) (z : Fin 8 → ℝ) (u : ℝ)

theorem planarPauli_revF_ladder :
    PlanarPauli (revF (ladderPauli P u)) (revPl (lQ0 P u)) (revPl (lQ1 P u)) (revR (lR P u)) :=
  planarPauli_revM (planarPauli_ladder P u)

/-- **`T₁` of `C₋` as a planar expression.** -/
theorem classT1_Cm_planar : classT1 .Cm permCm P z u =
    ladderK P * ((symanzikU (classAlpha .Cm) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (6 * -ppPl (revPl (lQ0 P u)) (revPl (lQ1 P u)) (revR (lR P u)) (gam ((revPl (cmE P z u 3)) * g0L * (revPl (cmE P z u 2)))) (gam ((revPl (cmE P z u 3)) * g1 * (revPl (cmE P z u 2)))) (gamT ((revPl (cmE P z u 3)) * 1 * bar (revPl (cmE P z u 2)))) (revPl (cmE P z u 1)) (revPl (cmE P z u 0))) := by
  rw [classT1_Cm_eq]
  simp only [revM_cmE]
  rw [pp_hfam_planar (planarPauli_revF_ladder P u)]

/-- **`T₂` of `C₋` as a planar expression.** -/
theorem classT2_Cm_planar : classT2 .Cm permCm P z u =
    ladderK P * ((symanzikU (classAlpha .Cm) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 1 *
          -(2 * ppPl (revPl (lQ0 P u)) (revPl (lQ1 P u)) (revR (lR P u)) (gam ((revPl (cmE P z u 3)) * g0L * (revPl (cmE P z u 2)))) (gam ((revPl (cmE P z u 3)) * g1 * (revPl (cmE P z u 2)))) (gamT ((revPl (cmE P z u 3)) * 1 * bar (revPl (cmE P z u 2)))) 1 1) +
        classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 2 *
          -(ppPl (revPl (lQ0 P u)) (revPl (lQ1 P u)) (revR (lR P u)) (gam ((revPl (cmE P z u 3)) * g0L * 1)) (gam ((revPl (cmE P z u 3)) * g1 * 1)) (gamT ((revPl (cmE P z u 3)) * 1 * bar 1)) (gam (revPl (cmE P z u 1))) 1 +
            2 * ppPl (revPl (lQ0 P u)) (revPl (lQ1 P u)) (revR (lR P u)) (gam ((revPl (cmE P z u 3)) * g0L * 1)) (gam ((revPl (cmE P z u 3)) * g1 * 1)) (gamT ((revPl (cmE P z u 3)) * 1 * bar 1)) 1 (revPl (cmE P z u 1)) +
            2 * ppPl (revPl (lQ0 P u)) (revPl (lQ1 P u)) (revR (lR P u)) (gam ((revPl (cmE P z u 3)) * g0L * (revPl (cmE P z u 1)))) (gam ((revPl (cmE P z u 3)) * g1 * (revPl (cmE P z u 1)))) (gamT ((revPl (cmE P z u 3)) * 1 * bar (revPl (cmE P z u 1)))) 1 1 +
            4 * pwPl (revPl (lQ0 P u)) (revPl (lQ1 P u)) (revR (lR P u)) 1 ((revPl (cmE P z u 3)) * gam (revPl (cmE P z u 1)))) +
        classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 3 *
          -(ppPl (gam (revPl (lQ0 P u))) (gam (revPl (lQ1 P u))) (gamT (revR (lR P u))) (gam (1 * g0L * (revPl (cmE P z u 2)))) (gam (1 * g1 * (revPl (cmE P z u 2)))) (gamT (1 * 1 * bar (revPl (cmE P z u 2)))) (revPl (cmE P z u 1)) 1 +
            4 * pwPl (revPl (lQ0 P u)) (revPl (lQ1 P u)) (revR (lR P u)) (gam (revPl (cmE P z u 2)) * (revPl (cmE P z u 1))) 1 +
            2 * pwPl (gam (revPl (lQ0 P u))) (gam (revPl (lQ1 P u))) (gamT (revR (lR P u))) ((revPl (cmE P z u 2)) * gam (revPl (cmE P z u 1))) 1 +
            4 * pwPl (gam (revPl (lQ0 P u))) (gam (revPl (lQ1 P u))) (gamT (revR (lR P u))) (revPl (cmE P z u 2)) (revPl (cmE P z u 1))) +
        classC .Cm (symanzikMatrix (classAlpha .Cm) z) 1 2 *
          -(2 * ppPl (revPl (lQ0 P u)) (revPl (lQ1 P u)) (revR (lR P u)) (gam ((revPl (cmE P z u 3)) * g0L * 1)) (gam ((revPl (cmE P z u 3)) * g1 * 1)) (gamT ((revPl (cmE P z u 3)) * 1 * bar 1)) 1 (revPl (cmE P z u 0))) +
        classC .Cm (symanzikMatrix (classAlpha .Cm) z) 1 3 *
          -(-ppPl (revPl (lQ0 P u)) (revPl (lQ1 P u)) (revR (lR P u)) (gam (gam (g0L * (revPl (cmE P z u 2))))) (gam (gam (g1 * (revPl (cmE P z u 2))))) (gamT (gamT (1 * bar (revPl (cmE P z u 2))))) 1 (revPl (cmE P z u 0)) +
            8 * ppPl (revPl (lQ0 P u)) (revPl (lQ1 P u)) (revR (lR P u)) (g0L * (revPl (cmE P z u 2))) (g1 * (revPl (cmE P z u 2))) (1 * bar (revPl (cmE P z u 2))) 1 (revPl (cmE P z u 0))) +
        classC .Cm (symanzikMatrix (classAlpha .Cm) z) 2 3 *
          -(4 * ppPl (revPl (lQ0 P u)) (revPl (lQ1 P u)) (revR (lR P u)) g0L g1 1 (revPl (cmE P z u 1)) (revPl (cmE P z u 0)))) := by
  have hP := planarPauli_revF_ladder P u
  have hPS := planarPauli_contractP hP
  rw [classT2_Cm_eq, pp_kfam]
  simp only [revM_cmE, gamM_toMat, toMat_mul]
  rw [← toMat_one]
  simp only [pp_hfam_planar hP, pp_hfam_planar hPS, pp_gammaLower_planar hP, pp_gl_planar hP,
    pp_glcc_planar hP, pw_planar hP, pw_planar hPS]

/-- **`T₃` of `C₋` as a planar expression.** -/
theorem classT3_Cm_planar : classT3 .Cm permCm P z u =
    ladderK P * ((symanzikU (classAlpha .Cm) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (1 / 4 * (classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 1 *
          classC .Cm (symanzikMatrix (classAlpha .Cm) z) 2 3 *
            -(16 * pwPl (revPl (lQ0 P u)) (revPl (lQ1 P u)) (revR (lR P u)) 1 1) +
        classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 2 *
          classC .Cm (symanzikMatrix (classAlpha .Cm) z) 1 3 *
            (32 * pwPl (revPl (lQ0 P u)) (revPl (lQ1 P u)) (revR (lR P u)) 1 1) +
        classC .Cm (symanzikMatrix (classAlpha .Cm) z) 0 3 *
          classC .Cm (symanzikMatrix (classAlpha .Cm) z) 1 2 *
            (32 * pwPl (revPl (lQ0 P u)) (revPl (lQ1 P u)) (revR (lR P u)) 1 1))) := by
  rw [classT3_Cm_eq, ← toMat_one, pw_planar (planarPauli_revF_ladder P u)]

end PlanarT

/-! ### The jets of the slot numerators -/

/-- **The jet of a slot numerator of `C₋`**: `cmE k = (1, aₖ + bₖ p'⁰, -bₖ p'¹, 0)`. -/
theorem jet_cmE {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) (k : Fin 4) :
    HasPJ (fun u => cmE P z u k) (eJ ((cmSlotA z k : ℂ) + (cmSlotB z k : ℂ)) (cmSlotB z k : ℂ)) :=
  (HasPlJet.mk (HasJet2.const 1) ((HasJet2.const (cmSlotA z k : ℂ)).add
    (jet_P0.const_mul (cmSlotB z k : ℂ))) (jet_P1.const_mul (cmSlotB z k : ℂ)).neg
    (HasJet2.const 0)).of_eq
    (fun u => by
      ext <;> simp [cmE, ePl, cmQ_apply, hm, restMomentum])
    (by ext <;> simp [eJ]) (by ext <;> simp [eJ, mul_comm]) (by ext <;> simp [eJ, mul_comm])

/-! ### The second-order coefficients of the patterns -/

section Values

variable (α₀ α₁ α₂ α₃ β₀ β₁ β₂ β₃ : ℂ)

theorem ppJ_Cm_T1 : ppJ (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (eJ α₃ β₃)).mul (PJ.c g0L)).mul (pjRev (eJ α₂ β₂))).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c g1)).mul (pjRev (eJ α₂ β₂))).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c 1)).mul (pjRev (eJ α₂ β₂)).bar).gamT (pjRev (eJ α₁ β₁)) (pjRev (eJ α₀ β₀)) =
    -512*α₀*α₁*α₂*α₃ + 512*α₀*α₁*β₂ + 512*α₀*α₁*β₃ + 512*α₀*α₁ + 512*α₀*α₂*α₃ + 512*α₀*α₂*β₁ - 512*α₀*α₂*β₃ + 512*α₀*α₃*β₁ - 512*α₀*α₃*β₂ - 512*α₀*β₁ + 512*α₀*β₂ + 512*α₀*β₃ - 512*α₀ - 512*α₁*α₂*β₀ + 512*α₁*α₂*β₃ + 512*α₁*α₂ - 512*α₁*α₃*β₀ + 512*α₁*α₃*β₂ + 512*α₁*α₃ + 512*α₁*β₀ - 512*α₁*β₂ - 512*α₁*β₃ - 512*α₁ + 512*α₂*α₃*β₀ - 512*α₂*α₃*β₁ - 512*α₂*α₃ - 512*α₂*β₀ + 512*α₂*β₁ + 512*α₂ - 512*α₃*β₀ + 512*α₃*β₁ + 512*α₃ - 512*β₂ - 512*β₃ := by
  simp [ppJ, ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]
  ring

theorem ppJ_Cm_01 : ppJ (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (eJ α₃ β₃)).mul (PJ.c g0L)).mul (pjRev (eJ α₂ β₂))).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c g1)).mul (pjRev (eJ α₂ β₂))).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c 1)).mul (pjRev (eJ α₂ β₂)).bar).gamT (PJ.c 1) (PJ.c 1) =
    -512*α₂*α₃ + 512*α₂ + 512*α₃ - 512*β₂ - 512*β₃ := by
  simp [ppJ, ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]
  ring

theorem ppJ_Cm_02a : ppJ (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (eJ α₃ β₃)).mul (PJ.c g0L)).mul (PJ.c 1)).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c g1)).mul (PJ.c 1)).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c 1)).mul (PJ.c 1).bar).gamT (pjRev (eJ α₁ β₁)).gam (PJ.c 1) =
    1024*α₁*α₃ - 1024*α₁*β₃ - 1024*α₁ + 1024*α₃*β₁ - 2048*α₃ + 2048*β₃ := by
  simp [ppJ, ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]
  ring

theorem ppJ_Cm_02b : ppJ (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (eJ α₃ β₃)).mul (PJ.c g0L)).mul (PJ.c 1)).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c g1)).mul (PJ.c 1)).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c 1)).mul (PJ.c 1).bar).gamT (PJ.c 1) (pjRev (eJ α₁ β₁)) =
    512*α₁*β₃ - 512*α₁ - 512*α₃*β₁ + 512*α₃ - 512*β₃ := by
  simp [ppJ, ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]
  ring

theorem ppJ_Cm_02c : ppJ (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (eJ α₃ β₃)).mul (PJ.c g0L)).mul (pjRev (eJ α₁ β₁))).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c g1)).mul (pjRev (eJ α₁ β₁))).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c 1)).mul (pjRev (eJ α₁ β₁)).bar).gamT (PJ.c 1) (PJ.c 1) =
    -512*α₁*α₃ + 512*α₁ + 512*α₃ - 512*β₁ - 512*β₃ := by
  simp [ppJ, ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]
  ring

theorem pwJ_Cm_02d : pwJ (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (PJ.c 1) ((pjRev (eJ α₃ β₃)).mul (pjRev (eJ α₁ β₁)).gam) =
    -256*α₁*β₃ + 256*α₁ + 256*α₃*β₁ - 512*α₃ - 256*β₁ + 512*β₃ := by
  simp [pwJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, pjRev, pjRevR, revPl, revR]
  ring

theorem ppJ_Cm_03a : ppJ (pjRev qJ0).gam (pjRev qJ1).gam (pjRevR rJ).gamT (((PJ.c 1).mul (PJ.c g0L)).mul (pjRev (eJ α₂ β₂))).gam (((PJ.c 1).mul (PJ.c g1)).mul (pjRev (eJ α₂ β₂))).gam (((PJ.c 1).mul (PJ.c 1)).mul (pjRev (eJ α₂ β₂)).bar).gamT (pjRev (eJ α₁ β₁)) (PJ.c 1) =
    1024*α₁*α₂ + 1024*α₁*β₂ + 2048*α₁ - 1024*α₂*β₁ - 1024*α₂ := by
  simp [ppJ, ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]
  ring

theorem pwJ_Cm_03b : pwJ (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) ((pjRev (eJ α₂ β₂)).gam.mul (pjRev (eJ α₁ β₁))) (PJ.c 1) =
    -256*α₁*β₂ + 256*α₂*β₁ - 512*β₁ + 256*β₂ := by
  simp [pwJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, pjRev, pjRevR, revPl, revR]
  ring

theorem pwJ_Cm_03c : pwJ (pjRev qJ0).gam (pjRev qJ1).gam (pjRevR rJ).gamT ((pjRev (eJ α₂ β₂)).mul (pjRev (eJ α₁ β₁)).gam) (PJ.c 1) =
    512*α₁*β₂ - 512*α₁ - 512*α₂*β₁ + 1024*α₂ := by
  simp [pwJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, pjRev, pjRevR, revPl, revR]
  ring

theorem pwJ_Cm_03d : pwJ (pjRev qJ0).gam (pjRev qJ1).gam (pjRevR rJ).gamT (pjRev (eJ α₂ β₂)) (pjRev (eJ α₁ β₁)) =
    256*α₁*α₂ - 256*α₁*β₂ - 256*α₁ + 256*α₂*β₁ - 256*α₂ := by
  simp [pwJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, pjRev, pjRevR, revPl, revR]
  ring

theorem ppJ_Cm_12 : ppJ (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (eJ α₃ β₃)).mul (PJ.c g0L)).mul (PJ.c 1)).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c g1)).mul (PJ.c 1)).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c 1)).mul (PJ.c 1).bar).gamT (PJ.c 1) (pjRev (eJ α₀ β₀)) =
    512*α₀*β₃ - 512*α₀ - 512*α₃*β₀ + 512*α₃ - 512*β₃ := by
  simp [ppJ, ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]
  ring

theorem ppJ_Cm_13a : ppJ (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) ((PJ.c g0L).mul (pjRev (eJ α₂ β₂))).gam.gam ((PJ.c g1).mul (pjRev (eJ α₂ β₂))).gam.gam ((PJ.c 1).mul (pjRev (eJ α₂ β₂)).bar).gamT.gamT (PJ.c 1) (pjRev (eJ α₀ β₀)) =
    -2048*α₀*β₂ - 1024*α₀ + 2048*α₂*β₀ - 2048*α₂ + 2048*β₂ := by
  simp [ppJ, ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]
  ring

theorem ppJ_Cm_13b : ppJ (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) ((PJ.c g0L).mul (pjRev (eJ α₂ β₂))) ((PJ.c g1).mul (pjRev (eJ α₂ β₂))) ((PJ.c 1).mul (pjRev (eJ α₂ β₂)).bar) (PJ.c 1) (pjRev (eJ α₀ β₀)) =
    256*α₀*α₂ - 256*α₀*β₂ - 256*α₀ + 256*α₂*β₀ - 256*α₂ := by
  simp [ppJ, ppJk, PJ.mul, PJ.bar, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]
  ring

theorem ppJ_Cm_23 : ppJ (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (PJ.c g0L) (PJ.c g1) (PJ.c 1) (pjRev (eJ α₁ β₁)) (pjRev (eJ α₀ β₀)) =
    256*α₀*α₁ - 256*α₀*β₁ - 256*α₀ + 256*α₁*β₀ - 256*α₁ := by
  simp [ppJ, ppJk, PJ.mul, PJ.bar, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]
  ring

theorem pwJ_Cm_T3 : pwJ (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (PJ.c 1) (PJ.c 1) = 0 := by
  simp [pwJ, pwJk, PJ.mul, PJ.bar, PJ.c, PJ.s2, qJ0, qJ1, rJ, g0, g1, pjRev, pjRevR, revPl, revR]
  norm_num

/-! The values and first-order coefficients of the patterns vanish. -/

@[simp] theorem ppJk_Cm_T1_s0 : ppJk PJ.s0 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (eJ α₃ β₃)).mul (PJ.c g0L)).mul (pjRev (eJ α₂ β₂))).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c g1)).mul (pjRev (eJ α₂ β₂))).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c 1)).mul (pjRev (eJ α₂ β₂)).bar).gamT (pjRev (eJ α₁ β₁)) (pjRev (eJ α₀ β₀)) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]

@[simp] theorem ppJk_Cm_T1_s1 : ppJk PJ.s1 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (eJ α₃ β₃)).mul (PJ.c g0L)).mul (pjRev (eJ α₂ β₂))).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c g1)).mul (pjRev (eJ α₂ β₂))).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c 1)).mul (pjRev (eJ α₂ β₂)).bar).gamT (pjRev (eJ α₁ β₁)) (pjRev (eJ α₀ β₀)) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]

@[simp] theorem ppJk_Cm_01_s0 : ppJk PJ.s0 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (eJ α₃ β₃)).mul (PJ.c g0L)).mul (pjRev (eJ α₂ β₂))).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c g1)).mul (pjRev (eJ α₂ β₂))).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c 1)).mul (pjRev (eJ α₂ β₂)).bar).gamT (PJ.c 1) (PJ.c 1) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]

@[simp] theorem ppJk_Cm_01_s1 : ppJk PJ.s1 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (eJ α₃ β₃)).mul (PJ.c g0L)).mul (pjRev (eJ α₂ β₂))).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c g1)).mul (pjRev (eJ α₂ β₂))).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c 1)).mul (pjRev (eJ α₂ β₂)).bar).gamT (PJ.c 1) (PJ.c 1) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]

@[simp] theorem ppJk_Cm_02a_s0 : ppJk PJ.s0 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (eJ α₃ β₃)).mul (PJ.c g0L)).mul (PJ.c 1)).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c g1)).mul (PJ.c 1)).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c 1)).mul (PJ.c 1).bar).gamT (pjRev (eJ α₁ β₁)).gam (PJ.c 1) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]

@[simp] theorem ppJk_Cm_02a_s1 : ppJk PJ.s1 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (eJ α₃ β₃)).mul (PJ.c g0L)).mul (PJ.c 1)).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c g1)).mul (PJ.c 1)).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c 1)).mul (PJ.c 1).bar).gamT (pjRev (eJ α₁ β₁)).gam (PJ.c 1) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]

@[simp] theorem ppJk_Cm_02b_s0 : ppJk PJ.s0 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (eJ α₃ β₃)).mul (PJ.c g0L)).mul (PJ.c 1)).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c g1)).mul (PJ.c 1)).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c 1)).mul (PJ.c 1).bar).gamT (PJ.c 1) (pjRev (eJ α₁ β₁)) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]

@[simp] theorem ppJk_Cm_02b_s1 : ppJk PJ.s1 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (eJ α₃ β₃)).mul (PJ.c g0L)).mul (PJ.c 1)).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c g1)).mul (PJ.c 1)).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c 1)).mul (PJ.c 1).bar).gamT (PJ.c 1) (pjRev (eJ α₁ β₁)) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]

@[simp] theorem ppJk_Cm_02c_s0 : ppJk PJ.s0 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (eJ α₃ β₃)).mul (PJ.c g0L)).mul (pjRev (eJ α₁ β₁))).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c g1)).mul (pjRev (eJ α₁ β₁))).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c 1)).mul (pjRev (eJ α₁ β₁)).bar).gamT (PJ.c 1) (PJ.c 1) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]

@[simp] theorem ppJk_Cm_02c_s1 : ppJk PJ.s1 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (eJ α₃ β₃)).mul (PJ.c g0L)).mul (pjRev (eJ α₁ β₁))).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c g1)).mul (pjRev (eJ α₁ β₁))).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c 1)).mul (pjRev (eJ α₁ β₁)).bar).gamT (PJ.c 1) (PJ.c 1) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]

@[simp] theorem pwJk_Cm_02d_s0 : pwJk PJ.s0 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (PJ.c 1) ((pjRev (eJ α₃ β₃)).mul (pjRev (eJ α₁ β₁)).gam) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1, pjRev, pjRevR, revPl, revR]

@[simp] theorem pwJk_Cm_02d_s1 : pwJk PJ.s1 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (PJ.c 1) ((pjRev (eJ α₃ β₃)).mul (pjRev (eJ α₁ β₁)).gam) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1, pjRev, pjRevR, revPl, revR]

@[simp] theorem ppJk_Cm_03a_s0 : ppJk PJ.s0 (pjRev qJ0).gam (pjRev qJ1).gam (pjRevR rJ).gamT (((PJ.c 1).mul (PJ.c g0L)).mul (pjRev (eJ α₂ β₂))).gam (((PJ.c 1).mul (PJ.c g1)).mul (pjRev (eJ α₂ β₂))).gam (((PJ.c 1).mul (PJ.c 1)).mul (pjRev (eJ α₂ β₂)).bar).gamT (pjRev (eJ α₁ β₁)) (PJ.c 1) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]

@[simp] theorem ppJk_Cm_03a_s1 : ppJk PJ.s1 (pjRev qJ0).gam (pjRev qJ1).gam (pjRevR rJ).gamT (((PJ.c 1).mul (PJ.c g0L)).mul (pjRev (eJ α₂ β₂))).gam (((PJ.c 1).mul (PJ.c g1)).mul (pjRev (eJ α₂ β₂))).gam (((PJ.c 1).mul (PJ.c 1)).mul (pjRev (eJ α₂ β₂)).bar).gamT (pjRev (eJ α₁ β₁)) (PJ.c 1) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]

@[simp] theorem pwJk_Cm_03b_s0 : pwJk PJ.s0 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) ((pjRev (eJ α₂ β₂)).gam.mul (pjRev (eJ α₁ β₁))) (PJ.c 1) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1, pjRev, pjRevR, revPl, revR]

@[simp] theorem pwJk_Cm_03b_s1 : pwJk PJ.s1 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) ((pjRev (eJ α₂ β₂)).gam.mul (pjRev (eJ α₁ β₁))) (PJ.c 1) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1, pjRev, pjRevR, revPl, revR]

@[simp] theorem pwJk_Cm_03c_s0 : pwJk PJ.s0 (pjRev qJ0).gam (pjRev qJ1).gam (pjRevR rJ).gamT ((pjRev (eJ α₂ β₂)).mul (pjRev (eJ α₁ β₁)).gam) (PJ.c 1) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1, pjRev, pjRevR, revPl, revR]

@[simp] theorem pwJk_Cm_03c_s1 : pwJk PJ.s1 (pjRev qJ0).gam (pjRev qJ1).gam (pjRevR rJ).gamT ((pjRev (eJ α₂ β₂)).mul (pjRev (eJ α₁ β₁)).gam) (PJ.c 1) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1, pjRev, pjRevR, revPl, revR]

@[simp] theorem pwJk_Cm_03d_s0 : pwJk PJ.s0 (pjRev qJ0).gam (pjRev qJ1).gam (pjRevR rJ).gamT (pjRev (eJ α₂ β₂)) (pjRev (eJ α₁ β₁)) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1, pjRev, pjRevR, revPl, revR]

@[simp] theorem pwJk_Cm_03d_s1 : pwJk PJ.s1 (pjRev qJ0).gam (pjRev qJ1).gam (pjRevR rJ).gamT (pjRev (eJ α₂ β₂)) (pjRev (eJ α₁ β₁)) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1, pjRev, pjRevR, revPl, revR]

@[simp] theorem ppJk_Cm_12_s0 : ppJk PJ.s0 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (eJ α₃ β₃)).mul (PJ.c g0L)).mul (PJ.c 1)).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c g1)).mul (PJ.c 1)).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c 1)).mul (PJ.c 1).bar).gamT (PJ.c 1) (pjRev (eJ α₀ β₀)) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]

@[simp] theorem ppJk_Cm_12_s1 : ppJk PJ.s1 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (((pjRev (eJ α₃ β₃)).mul (PJ.c g0L)).mul (PJ.c 1)).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c g1)).mul (PJ.c 1)).gam (((pjRev (eJ α₃ β₃)).mul (PJ.c 1)).mul (PJ.c 1).bar).gamT (PJ.c 1) (pjRev (eJ α₀ β₀)) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]

@[simp] theorem ppJk_Cm_13a_s0 : ppJk PJ.s0 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) ((PJ.c g0L).mul (pjRev (eJ α₂ β₂))).gam.gam ((PJ.c g1).mul (pjRev (eJ α₂ β₂))).gam.gam ((PJ.c 1).mul (pjRev (eJ α₂ β₂)).bar).gamT.gamT (PJ.c 1) (pjRev (eJ α₀ β₀)) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]

@[simp] theorem ppJk_Cm_13a_s1 : ppJk PJ.s1 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) ((PJ.c g0L).mul (pjRev (eJ α₂ β₂))).gam.gam ((PJ.c g1).mul (pjRev (eJ α₂ β₂))).gam.gam ((PJ.c 1).mul (pjRev (eJ α₂ β₂)).bar).gamT.gamT (PJ.c 1) (pjRev (eJ α₀ β₀)) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]

@[simp] theorem ppJk_Cm_13b_s0 : ppJk PJ.s0 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) ((PJ.c g0L).mul (pjRev (eJ α₂ β₂))) ((PJ.c g1).mul (pjRev (eJ α₂ β₂))) ((PJ.c 1).mul (pjRev (eJ α₂ β₂)).bar) (PJ.c 1) (pjRev (eJ α₀ β₀)) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]

@[simp] theorem ppJk_Cm_13b_s1 : ppJk PJ.s1 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) ((PJ.c g0L).mul (pjRev (eJ α₂ β₂))) ((PJ.c g1).mul (pjRev (eJ α₂ β₂))) ((PJ.c 1).mul (pjRev (eJ α₂ β₂)).bar) (PJ.c 1) (pjRev (eJ α₀ β₀)) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]

@[simp] theorem ppJk_Cm_23_s0 : ppJk PJ.s0 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (PJ.c g0L) (PJ.c g1) (PJ.c 1) (pjRev (eJ α₁ β₁)) (pjRev (eJ α₀ β₀)) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]

@[simp] theorem ppJk_Cm_23_s1 : ppJk PJ.s1 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (PJ.c g0L) (PJ.c g1) (PJ.c 1) (pjRev (eJ α₁ β₁)) (pjRev (eJ α₀ β₀)) = 0 := by
  simp [ppJk, PJ.mul, PJ.bar, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1, g0L, pjRev, pjRevR, revPl, revR]

@[simp] theorem pwJk_Cm_T3_s0 : pwJk PJ.s0 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (PJ.c 1) (PJ.c 1) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.c, PJ.s0, qJ0, qJ1, rJ, g0, g1, pjRev, pjRevR, revPl, revR]

@[simp] theorem pwJk_Cm_T3_s1 : pwJk PJ.s1 (pjRev qJ0) (pjRev qJ1) (pjRevR rJ) (PJ.c 1) (PJ.c 1) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.c, PJ.s1, qJ0, qJ1, rJ, g0, g1, pjRev, pjRevR, revPl, revR]

end Values

end QED.TwoLoop.UnitSCGraph

end
