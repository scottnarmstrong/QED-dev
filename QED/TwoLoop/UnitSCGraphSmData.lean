/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCGraphSmTrace
public import QED.TwoLoop.UnitSCGraphSpData
import Mathlib.Tactic.Ring

/-!
# The planar data of the self-energy class `S₋`

Section 8 of `docs/TWO-LOOP-UNITS.md`, stage 1 of the `S + C` link, graph half, the analogue of
`QED/TwoLoop/UnitSCGraphSpData.lean` for `S₋`. The momenta of `S₋` at the shifted loop point lie
in the plane of `p = (m, 0, 0, 0)` and `p'`:

* the loop shift is `S_s = σ_s p + τ_s p'` with
  `σ_s = (A⁻¹)_{s0} (z₀ + z₁ + z₂) - (A⁻¹)_{s1} z₁`, `τ_s = (A⁻¹)_{s0} z₃` (`loopShift_Sm`; lines
  `0, 1, 2` carry `p`, line `3` carries `p'`), so the momentum of chain slot `k` is
  `qₖ = aₖ p + bₖ p'` (`smQ_apply`);
* hence the three coefficients `T₁, T₂, T₃` of `QED/TwoLoop/UnitSCGraphSmTrace.lean` are planar
  base patterns `pwPl` (`classT1_Sm_planar`, `classT2_Sm_planar`, `classT3_Sm_planar`);
* their second-order jets along the curve (at `m = 1`) are explicit polynomials in
  `αₖ = aₖ + bₖ`, `βₖ = bₖ` (`pwJ_Sm_T1`, …), and the values and first-order coefficients
  vanish.
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

/-- The coefficient of `p` in the loop shift `S_s` of `S₋`. -/
noncomputable def smSigP (z : Fin 8 → ℝ) (s : Fin 2) : ℝ :=
  (symanzikMatrix (classAlpha .Sm) z)⁻¹ s 0 * (z 0 + z 1 + z 2) -
    (symanzikMatrix (classAlpha .Sm) z)⁻¹ s 1 * z 1

/-- The coefficient of `p'` in the loop shift `S_s` of `S₋`. -/
noncomputable def smSigQ (z : Fin 8 → ℝ) (s : Fin 2) : ℝ :=
  (symanzikMatrix (classAlpha .Sm) z)⁻¹ s 0 * z 3

/-- **The loop shift of `S₋`**: `S_s = σ_s p + τ_s p'`. -/
theorem loopShift_Sm (p p' : Fin 4 → ℝ) (z : Fin 8 → ℝ) (s : Fin 2) (μ : Fin 4) :
    loopShift (classAlpha .Sm) (pvMomentaE .Sm p p') z s μ = smSigP z s * p μ + smSigQ z s * p' μ := by
  rw [QED.TwoLoop.LimitCovariance.loopShift_apply]
  simp [Fin.sum_univ_succ, castLoopMatrix, class5LoopMatrixPV,
    QED.Integration.TwoLoop.class5LoopMatrix, pvMomentaE, extMomenta,
    QED.Integration.TwoLoop.classCmSmMomenta, QED.Integration.TwoLoop.pvLines, smSigP, smSigQ]
  ring

/-- The coefficient of `p` in the slot momentum `qₖ` of `S₋`. -/
noncomputable def smSlotA (z : Fin 8 → ℝ) : Fin 4 → ℝ :=
  ![-smSigP z 0, 1 - smSigP z 0, 1 - smSigP z 0 + smSigP z 1, 1 - smSigP z 0]

/-- The coefficient of `p'` in the slot momentum `qₖ` of `S₋`. -/
noncomputable def smSlotB (z : Fin 8 → ℝ) : Fin 4 → ℝ :=
  ![1 - smSigQ z 0, -smSigQ z 0, -smSigQ z 0 + smSigQ z 1, -smSigQ z 0]

/-- **The slot momenta of `S₋`**: `qₖ = aₖ p + bₖ p'`. -/
theorem smQ_apply (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) (μ : Fin 4) :
    classQ .Sm P z u k μ =
      smSlotA z k * restMomentum P.m μ + smSlotB z k * curveMomentum P.m u μ := by
  simp only [classQ, QED.Integration.TwoLoop.lineMomentum, Pi.neg_apply, loopShift_Sm]
  fin_cases k <;>
    simp [Fin.sum_univ_two, castLoopMatrix, class5LoopMatrixPV,
      QED.Integration.TwoLoop.class5LoopMatrix, ladderLines, pvMomentaE, extMomenta,
      QED.Integration.TwoLoop.classCmSmMomenta, QED.Integration.TwoLoop.pvLines, smSlotA,
      smSlotB] <;>
    ring

theorem smQ_two (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) : classQ .Sm P z u k 2 = 0 := by
  rw [smQ_apply, restMomentum_two, curveMomentum_two]; ring

theorem smQ_three (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) : classQ .Sm P z u k 3 = 0 := by
  rw [smQ_apply, restMomentum_three, curveMomentum_three]; ring

theorem smE_planar (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) :
    classE .Sm P z u k = toMat (ePl P.m (classQ .Sm P z u k)) :=
  electronNumerator_ePl P.m (smQ_two P z u k) (smQ_three P z u k)

/-! ### The three coefficients as planar expressions -/

section PlanarT

variable (P : Params) (z : Fin 8 → ℝ) (u : ℝ)

/-- The planar electron numerators of the chain slots of `S₋`. -/
noncomputable abbrev smE (k : Fin 4) : Pl := ePl P.m (classQ .Sm P z u k)

/-- **`T₁` of `S₋` as a planar expression.** -/
theorem classT1_Sm_planar : classT1 .Sm permSm P z u =
    ladderK P * ((symanzikU (classAlpha .Sm) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (6 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) (smE P z u 0)
        (smE P z u 1 * gam (smE P z u 2) * smE P z u 3)) := by
  rw [classT1_Sm_eq]
  simp only [smE_planar, gamM_toMat, toMat_mul]
  rw [pw_planar (planarPauli_contractP (planarPauli_ladder P u))]

/-- **`T₂` of `S₋` as a planar expression.** -/
theorem classT2_Sm_planar : classT2 .Sm permSm P z u =
    ladderK P * ((symanzikU (classAlpha .Sm) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (classC .Sm (symanzikMatrix (classAlpha .Sm) z) 0 1 *
          (2 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) 1
            (gam (smE P z u 2) * smE P z u 3)) +
        classC .Sm (symanzikMatrix (classAlpha .Sm) z) 0 2 *
          (2 * pwPl (gam (smE P z u 3 * gam (lQ0 P u))) (gam (smE P z u 3 * gam (lQ1 P u)))
            (gamT (smE P z u 3 * gamT (lR P u))) 1 (smE P z u 1)) +
        classC .Sm (symanzikMatrix (classAlpha .Sm) z) 0 3 *
          pwPl (gam (gam (lQ0 P u))) (gam (gam (lQ1 P u))) (gamT (gamT (lR P u))) 1
            (smE P z u 1 * gam (smE P z u 2)) +
        classC .Sm (symanzikMatrix (classAlpha .Sm) z) 1 2 *
          (-8 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) (smE P z u 0)
            (smE P z u 3)) +
        classC .Sm (symanzikMatrix (classAlpha .Sm) z) 1 3 *
          pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) (smE P z u 0)
            (gam (gam (smE P z u 2))) +
        classC .Sm (symanzikMatrix (classAlpha .Sm) z) 2 3 *
          (-8 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) (smE P z u 0)
            (smE P z u 1))) := by
  have hP1 := planarPauli_contractP (planarPauli_ladder P u)
  have hP2 := planarPauli_contractP hP1
  have hP3 := planarPauli_contractP (planarPauli_mulLeftP hP1 (smE P z u 3))
  rw [classT2_Sm_eq]
  simp only [smE_planar, gamM_toMat, toMat_mul]
  rw [← toMat_one]
  simp only [pw_planar hP1, pw_planar hP2, pw_planar hP3]

/-- **`T₃` of `S₋` as a planar expression.** -/
theorem classT3_Sm_planar : classT3 .Sm permSm P z u =
    ladderK P * ((symanzikU (classAlpha .Sm) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (1 / 4 * (classC .Sm (symanzikMatrix (classAlpha .Sm) z) 0 1 *
          classC .Sm (symanzikMatrix (classAlpha .Sm) z) 2 3 *
            (-16 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) 1 1) +
        classC .Sm (symanzikMatrix (classAlpha .Sm) z) 0 2 *
          classC .Sm (symanzikMatrix (classAlpha .Sm) z) 1 3 *
            (8 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) 1 1) +
        classC .Sm (symanzikMatrix (classAlpha .Sm) z) 0 3 *
          classC .Sm (symanzikMatrix (classAlpha .Sm) z) 1 2 *
            (-16 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) 1 1))) := by
  have hP1 := planarPauli_contractP (planarPauli_ladder P u)
  rw [classT3_Sm_eq, ← toMat_one, pw_planar hP1]

end PlanarT

/-! ### The jets of the slot numerators -/

/-- **The jet of a slot numerator of `S₋`**: `smE k = (1, aₖ + bₖ p'⁰, -bₖ p'¹, 0)`. -/
theorem jet_smE {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) (k : Fin 4) :
    HasPJ (fun u => smE P z u k) (eJ ((smSlotA z k : ℂ) + (smSlotB z k : ℂ)) (smSlotB z k : ℂ)) :=
  (HasPlJet.mk (HasJet2.const 1) ((HasJet2.const (smSlotA z k : ℂ)).add
    (jet_P0.const_mul (smSlotB z k : ℂ))) (jet_P1.const_mul (smSlotB z k : ℂ)).neg
    (HasJet2.const 0)).of_eq
    (fun u => by
      ext <;> simp [smE, ePl, smQ_apply, hm, restMomentum])
    (by ext <;> simp [eJ]) (by ext <;> simp [eJ, mul_comm]) (by ext <;> simp [eJ, mul_comm])

/-! ### The second-order coefficients of the patterns -/

section Values

variable (α₀ α₁ α₂ α₃ β₀ β₁ β₂ β₃ : ℂ)

theorem pwJ_Sm_T1 : pwJ qJ0.gam qJ1.gam rJ.gamT (eJ α₀ β₀)
    (((eJ α₁ β₁).mul (eJ α₂ β₂).gam).mul (eJ α₃ β₃)) =
    -512 * (α₀ * α₁ * α₂ * α₃ - α₀ * α₁ * α₂ * β₃ - α₀ * α₁ * α₂ + α₀ * α₁ * α₃ * β₂ +
      2 * α₀ * α₁ * α₃ - 2 * α₀ * α₁ - α₀ * α₂ * α₃ * β₁ - α₀ * α₂ * α₃ + α₀ * α₂ -
      2 * α₀ * α₃ + 2 * α₀ * β₁ - α₀ * β₂ + 2 * α₀ * β₃ + 2 * α₀ + α₁ * α₂ * α₃ * β₀ -
      α₁ * α₂ * α₃ - 2 * α₁ * β₀ + α₁ * β₂ - 2 * α₁ * β₃ + 2 * α₁ + α₂ * β₀ - α₂ * β₁ +
      α₂ * β₃ - α₂ - 2 * α₃ * β₀ + 2 * α₃ * β₁ - α₃ * β₂ + 2 * α₃) := by
  simp [pwJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1]
  ring

theorem pwJ_Sm_01 : pwJ qJ0.gam qJ1.gam rJ.gamT (PJ.c 1) ((eJ α₂ β₂).gam.mul (eJ α₃ β₃)) =
    -512 * (α₂ * β₃ - α₂ - α₃ * β₂ + 2 * α₃) := by
  simp [pwJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1]
  ring

theorem pwJ_Sm_02 : pwJ (((eJ α₃ β₃).mul qJ0.gam).gam) (((eJ α₃ β₃).mul qJ1.gam).gam)
    (((eJ α₃ β₃).mul rJ.gamT).gamT) (PJ.c 1) (eJ α₁ β₁) =
    512 * (α₁ * α₃ - 2 * α₁ + α₃) := by
  simp [pwJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1]
  ring

theorem pwJ_Sm_03 : pwJ qJ0.gam.gam qJ1.gam.gam rJ.gamT.gamT (PJ.c 1)
    ((eJ α₁ β₁).mul (eJ α₂ β₂).gam) = 1024 * (α₁ * β₂ + 4 * α₁ - α₂ * β₁ - 2 * α₂) := by
  simp [pwJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1]
  ring

theorem pwJ_Sm_13 : pwJ qJ0.gam qJ1.gam rJ.gamT (eJ α₀ β₀) (eJ α₂ β₂).gam.gam =
    -1024 * (α₀ * α₂ - α₀ * β₂ - 4 * α₀ + α₂ * β₀ - α₂) := by
  simp [pwJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1]
  ring

/-! The values and first-order coefficients of all the patterns vanish. -/

@[simp] theorem pwJk_Sm_T1_s0 : pwJk PJ.s0 qJ0.gam qJ1.gam rJ.gamT (eJ α₀ β₀)
    (((eJ α₁ β₁).mul (eJ α₂ β₂).gam).mul (eJ α₃ β₃)) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Sm_T1_s1 : pwJk PJ.s1 qJ0.gam qJ1.gam rJ.gamT (eJ α₀ β₀)
    (((eJ α₁ β₁).mul (eJ α₂ β₂).gam).mul (eJ α₃ β₃)) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Sm_01_s0 :
    pwJk PJ.s0 qJ0.gam qJ1.gam rJ.gamT (PJ.c 1) ((eJ α₂ β₂).gam.mul (eJ α₃ β₃)) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Sm_01_s1 :
    pwJk PJ.s1 qJ0.gam qJ1.gam rJ.gamT (PJ.c 1) ((eJ α₂ β₂).gam.mul (eJ α₃ β₃)) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Sm_02_s0 : pwJk PJ.s0 (((eJ α₃ β₃).mul qJ0.gam).gam)
    (((eJ α₃ β₃).mul qJ1.gam).gam) (((eJ α₃ β₃).mul rJ.gamT).gamT) (PJ.c 1) (eJ α₁ β₁) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Sm_02_s1 : pwJk PJ.s1 (((eJ α₃ β₃).mul qJ0.gam).gam)
    (((eJ α₃ β₃).mul qJ1.gam).gam) (((eJ α₃ β₃).mul rJ.gamT).gamT) (PJ.c 1) (eJ α₁ β₁) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Sm_03_s0 : pwJk PJ.s0 qJ0.gam.gam qJ1.gam.gam rJ.gamT.gamT (PJ.c 1)
    ((eJ α₁ β₁).mul (eJ α₂ β₂).gam) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Sm_03_s1 : pwJk PJ.s1 qJ0.gam.gam qJ1.gam.gam rJ.gamT.gamT (PJ.c 1)
    ((eJ α₁ β₁).mul (eJ α₂ β₂).gam) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Sm_13_s0 :
    pwJk PJ.s0 qJ0.gam qJ1.gam rJ.gamT (eJ α₀ β₀) (eJ α₂ β₂).gam.gam = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Sm_13_s1 :
    pwJk PJ.s1 qJ0.gam qJ1.gam rJ.gamT (eJ α₀ β₀) (eJ α₂ β₂).gam.gam = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1]

end Values

end QED.TwoLoop.UnitSCGraph

end
