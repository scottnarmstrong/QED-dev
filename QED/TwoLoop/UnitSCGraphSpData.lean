/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCGraphSpTrace
import Mathlib.Tactic.Ring

/-!
# The planar data of the self-energy class `S₊`

Section 8 of `docs/TWO-LOOP-UNITS.md`, stage 1 of the `S + C` link, graph half. The momenta of
`S₊` at the shifted loop point lie in the plane of `p = (m, 0, 0, 0)` and `p'`:

* the loop shift is `S_s = σ_s p + τ_s p'` with `σ_s = ((A⁻¹)_{s0} + (A⁻¹)_{s1}) z₀`,
  `τ_s = (A⁻¹)_{s0} (z₁ + z₂ + z₃) + (A⁻¹)_{s1} (z₁ + z₃)` (`loopShift_Sp`; line `0` carries `p`,
  lines `1, 2, 3` carry `p'`), so the momentum of chain slot `k` is `qₖ = aₖ p + bₖ p'`
  (`spQ_apply`);
* hence the three coefficients `T₁, T₂, T₃` of `QED/TwoLoop/UnitSCGraphSpTrace.lean` are planar
  base patterns `pwPl` in the planar Pauli data of the ladder and the slot numerators
  (`classT1_Sp_planar`, `classT2_Sp_planar`, `classT3_Sp_planar`);
* their second-order jets along the curve (at `m = 1`) are explicit polynomials in
  `αₖ = aₖ + bₖ`, `βₖ = bₖ`, and the values and first-order coefficients vanish
  (`pwJ_Sp_T1`, …).
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

/-- The momentum of the chain slot `k` of the class `c` at the shifted loop momenta. -/
noncomputable abbrev classQ (c : Class5) (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) :
    Fin 4 → ℝ :=
  lineMomentum (classAlpha c) (classMom c P u) (ladderLines k)
    (-loopShift (classAlpha c) (classMom c P u) z)

theorem classE_apply (c : Class5) (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) :
    classE c P z u k = electronNumerator P.m (classQ c P z u k) := rfl

/-- The coefficient of `p` in the loop shift `S_s` of `S₊`. -/
noncomputable def spSigP (z : Fin 8 → ℝ) (s : Fin 2) : ℝ :=
  (symanzikMatrix (classAlpha .Sp) z)⁻¹ s 0 * z 0 + (symanzikMatrix (classAlpha .Sp) z)⁻¹ s 1 * z 0

/-- The coefficient of `p'` in the loop shift `S_s` of `S₊`. -/
noncomputable def spSigQ (z : Fin 8 → ℝ) (s : Fin 2) : ℝ :=
  (symanzikMatrix (classAlpha .Sp) z)⁻¹ s 0 * (z 1 + z 2 + z 3) +
    (symanzikMatrix (classAlpha .Sp) z)⁻¹ s 1 * (z 1 + z 3)

/-- **The loop shift of `S₊`**: `S_s = σ_s p + τ_s p'`. -/
theorem loopShift_Sp (p p' : Fin 4 → ℝ) (z : Fin 8 → ℝ) (s : Fin 2) (μ : Fin 4) :
    loopShift (classAlpha .Sp) (pvMomentaE .Sp p p') z s μ = spSigP z s * p μ + spSigQ z s * p' μ := by
  rw [QED.TwoLoop.LimitCovariance.loopShift_apply]
  simp [Fin.sum_univ_succ, castLoopMatrix, class5LoopMatrixPV,
    QED.Integration.TwoLoop.class5LoopMatrix, pvMomentaE, extMomenta,
    QED.Integration.TwoLoop.classCpSpMomenta, QED.Integration.TwoLoop.pvLines, spSigP, spSigQ]
  ring

/-- The coefficient of `p` in the slot momentum `qₖ` of `S₊`. -/
noncomputable def spSlotA (z : Fin 8 → ℝ) : Fin 4 → ℝ :=
  ![-(spSigP z 0 + spSigP z 1), -spSigP z 0, -(spSigP z 0 + spSigP z 1),
    1 - (spSigP z 0 + spSigP z 1)]

/-- The coefficient of `p'` in the slot momentum `qₖ` of `S₊`. -/
noncomputable def spSlotB (z : Fin 8 → ℝ) : Fin 4 → ℝ :=
  ![1 - (spSigQ z 0 + spSigQ z 1), 1 - spSigQ z 0, 1 - (spSigQ z 0 + spSigQ z 1),
    -(spSigQ z 0 + spSigQ z 1)]

/-- **The slot momenta of `S₊`**: `qₖ = aₖ p + bₖ p'`. -/
theorem spQ_apply (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) (μ : Fin 4) :
    classQ .Sp P z u k μ =
      spSlotA z k * restMomentum P.m μ + spSlotB z k * curveMomentum P.m u μ := by
  simp only [classQ, QED.Integration.TwoLoop.lineMomentum, Pi.neg_apply, loopShift_Sp]
  fin_cases k <;>
    simp [Fin.sum_univ_two, castLoopMatrix, class5LoopMatrixPV,
      QED.Integration.TwoLoop.class5LoopMatrix, ladderLines, pvMomentaE, extMomenta,
      QED.Integration.TwoLoop.classCpSpMomenta, QED.Integration.TwoLoop.pvLines, spSlotA,
      spSlotB] <;>
    ring

theorem spQ_two (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) : classQ .Sp P z u k 2 = 0 := by
  rw [spQ_apply, restMomentum_two, curveMomentum_two]; ring

theorem spQ_three (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) : classQ .Sp P z u k 3 = 0 := by
  rw [spQ_apply, restMomentum_three, curveMomentum_three]; ring

theorem spE_planar (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) :
    classE .Sp P z u k = toMat (ePl P.m (classQ .Sp P z u k)) :=
  electronNumerator_ePl P.m (spQ_two P z u k) (spQ_three P z u k)

theorem gamM_toMat (y : Pl) : gamM (toMat y) = toMat (gam y) := sum_gamma_toMat y

/-! ### The three coefficients as planar expressions -/

section PlanarT

variable (P : Params) (z : Fin 8 → ℝ) (u : ℝ)

/-- The planar electron numerators of the chain slots of `S₊`. -/
noncomputable abbrev spE (k : Fin 4) : Pl := ePl P.m (classQ .Sp P z u k)

/-- **`T₁` of `S₊` as a planar expression.** -/
theorem classT1_Sp_planar : classT1 .Sp permSp P z u =
    ladderK P * ((symanzikU (classAlpha .Sp) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (6 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u))
        (spE P z u 0 * gam (spE P z u 1) * spE P z u 2) (spE P z u 3)) := by
  rw [classT1_Sp_eq]
  simp only [spE_planar, gamM_toMat, toMat_mul]
  rw [pw_planar (planarPauli_contractP (planarPauli_ladder P u))]

/-- **`T₂` of `S₊` as a planar expression.** -/
theorem classT2_Sp_planar : classT2 .Sp permSp P z u =
    ladderK P * ((symanzikU (classAlpha .Sp) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (classC .Sp (symanzikMatrix (classAlpha .Sp) z) 0 1 *
          (-8 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) (spE P z u 2)
            (spE P z u 3)) +
        classC .Sp (symanzikMatrix (classAlpha .Sp) z) 0 2 *
          pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) (gam (gam (spE P z u 1)))
            (spE P z u 3) +
        classC .Sp (symanzikMatrix (classAlpha .Sp) z) 0 3 *
          pwPl (gam (gam (lQ0 P u))) (gam (gam (lQ1 P u))) (gamT (gamT (lR P u)))
            (gam (spE P z u 1) * spE P z u 2) 1 +
        classC .Sp (symanzikMatrix (classAlpha .Sp) z) 1 2 *
          (-8 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) (spE P z u 0)
            (spE P z u 3)) +
        classC .Sp (symanzikMatrix (classAlpha .Sp) z) 1 3 *
          (2 * pwPl (gam (gam (lQ0 P u) * spE P z u 0)) (gam (gam (lQ1 P u) * spE P z u 0))
            (gamT (gamT (lR P u) * bar (spE P z u 0))) (spE P z u 2) 1) +
        classC .Sp (symanzikMatrix (classAlpha .Sp) z) 2 3 *
          (2 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u))
            (spE P z u 0 * gam (spE P z u 1)) 1)) := by
  have hP1 := planarPauli_contractP (planarPauli_ladder P u)
  have hP2 := planarPauli_contractP hP1
  have hP3 := planarPauli_contractP (planarPauli_mulRightP hP1 (spE P z u 0))
  rw [classT2_Sp_eq]
  simp only [spE_planar, gamM_toMat, toMat_mul]
  rw [← toMat_one]
  simp only [pw_planar hP1, pw_planar hP2, pw_planar hP3]

/-- **`T₃` of `S₊` as a planar expression.** -/
theorem classT3_Sp_planar : classT3 .Sp permSp P z u =
    ladderK P * ((symanzikU (classAlpha .Sp) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (1 / 4 * (classC .Sp (symanzikMatrix (classAlpha .Sp) z) 0 1 *
          classC .Sp (symanzikMatrix (classAlpha .Sp) z) 2 3 *
            (-16 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) 1 1) +
        classC .Sp (symanzikMatrix (classAlpha .Sp) z) 0 2 *
          classC .Sp (symanzikMatrix (classAlpha .Sp) z) 1 3 *
            (8 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) 1 1) +
        classC .Sp (symanzikMatrix (classAlpha .Sp) z) 0 3 *
          classC .Sp (symanzikMatrix (classAlpha .Sp) z) 1 2 *
            (-16 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) 1 1))) := by
  have hP1 := planarPauli_contractP (planarPauli_ladder P u)
  rw [classT3_Sp_eq, ← toMat_one, pw_planar hP1]

end PlanarT

/-! ### The jets of the slot numerators -/

/-- **The jet of a slot numerator of `S₊`**: `spE k = (1, aₖ + bₖ p'⁰, -bₖ p'¹, 0)`. -/
theorem jet_spE {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) (k : Fin 4) :
    HasPJ (fun u => spE P z u k) (eJ ((spSlotA z k : ℂ) + (spSlotB z k : ℂ)) (spSlotB z k : ℂ)) :=
  (HasPlJet.mk (HasJet2.const 1) ((HasJet2.const (spSlotA z k : ℂ)).add
    (jet_P0.const_mul (spSlotB z k : ℂ))) (jet_P1.const_mul (spSlotB z k : ℂ)).neg
    (HasJet2.const 0)).of_eq
    (fun u => by
      ext <;> simp [spE, ePl, spQ_apply, hm, restMomentum])
    (by ext <;> simp [eJ]) (by ext <;> simp [eJ, mul_comm]) (by ext <;> simp [eJ, mul_comm])

/-! ### The second-order coefficients of the patterns -/

section Values

variable (α₀ α₁ α₂ α₃ β₀ β₁ β₂ β₃ : ℂ)

theorem pwJ_Sp_T1 : pwJ qJ0.gam qJ1.gam rJ.gamT (((eJ α₀ β₀).mul (eJ α₁ β₁).gam).mul (eJ α₂ β₂))
    (eJ α₃ β₃) =
    -512 * (α₀ * α₁ * α₂ * α₃ - α₀ * α₁ * α₂ * β₃ - α₀ * α₁ * α₂ + α₀ * α₁ * α₃ * β₂ -
      α₀ * α₁ * α₃ - α₀ * α₂ * α₃ * β₁ + 2 * α₀ * α₂ * α₃ - 2 * α₀ * α₃ + α₀ * β₁ - 2 * α₀ * β₂ +
      2 * α₀ * β₃ + 2 * α₀ + α₁ * α₂ * α₃ * β₀ - α₁ * α₂ * α₃ + α₁ * α₃ - α₁ * β₀ + α₁ * β₂ -
      α₁ * β₃ - α₁ - 2 * α₂ * α₃ + 2 * α₂ * β₀ - α₂ * β₁ + 2 * α₂ * β₃ + 2 * α₂ - 2 * α₃ * β₀ +
      α₃ * β₁ - 2 * α₃ * β₂ + 2 * α₃) := by
  simp [pwJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1]
  ring

theorem pwJ_Sp_23 : pwJ qJ0.gam qJ1.gam rJ.gamT (eJ α₂ β₂) (eJ α₃ β₃) =
    -256 * (α₂ * α₃ - α₂ * β₃ - α₂ + α₃ * β₂ - α₃) := by
  simp [pwJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1]
  ring

theorem pwJ_Sp_02 : pwJ qJ0.gam qJ1.gam rJ.gamT (eJ α₁ β₁).gam.gam (eJ α₃ β₃) =
    -1024 * (α₁ * α₃ - α₁ * β₃ - α₁ + α₃ * β₁ - 4 * α₃) := by
  simp [pwJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1]
  ring

theorem pwJ_Sp_03 : pwJ qJ0.gam.gam qJ1.gam.gam rJ.gamT.gamT ((eJ α₁ β₁).gam.mul (eJ α₂ β₂))
    (PJ.c 1) = 1024 * (α₁ * β₂ - 2 * α₁ - α₂ * β₁ + 4 * α₂) := by
  simp [pwJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1]
  ring

theorem pwJ_Sp_13 : pwJ ((qJ0.gam.mul (eJ α₀ β₀)).gam) ((qJ1.gam.mul (eJ α₀ β₀)).gam)
    ((rJ.gamT.mul (eJ α₀ β₀).bar).gamT) (eJ α₂ β₂) (PJ.c 1) =
    512 * (α₀ * α₂ + α₀ - 2 * α₂) := by
  simp [pwJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1]
  ring

theorem pwJ_Sp_23' : pwJ qJ0.gam qJ1.gam rJ.gamT ((eJ α₀ β₀).mul (eJ α₁ β₁).gam) (PJ.c 1) =
    -512 * (α₀ * β₁ + 2 * α₀ - α₁ * β₀ - α₁) := by
  simp [pwJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1]
  ring

theorem pwJ_Sp_T3 : pwJ qJ0.gam qJ1.gam rJ.gamT (PJ.c 1) (PJ.c 1) = 0 := by
  simp [pwJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, qJ0, qJ1, rJ, g0, g1]
  norm_num

/-! The values and first-order coefficients of all the patterns vanish. -/

@[simp] theorem pwJk_Sp_T1_s0 : pwJk PJ.s0 qJ0.gam qJ1.gam rJ.gamT
    (((eJ α₀ β₀).mul (eJ α₁ β₁).gam).mul (eJ α₂ β₂)) (eJ α₃ β₃) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Sp_T1_s1 : pwJk PJ.s1 qJ0.gam qJ1.gam rJ.gamT
    (((eJ α₀ β₀).mul (eJ α₁ β₁).gam).mul (eJ α₂ β₂)) (eJ α₃ β₃) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Sp_23_s0 : pwJk PJ.s0 qJ0.gam qJ1.gam rJ.gamT (eJ α₂ β₂) (eJ α₃ β₃) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Sp_23_s1 : pwJk PJ.s1 qJ0.gam qJ1.gam rJ.gamT (eJ α₂ β₂) (eJ α₃ β₃) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Sp_02_s0 :
    pwJk PJ.s0 qJ0.gam qJ1.gam rJ.gamT (eJ α₁ β₁).gam.gam (eJ α₃ β₃) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Sp_02_s1 :
    pwJk PJ.s1 qJ0.gam qJ1.gam rJ.gamT (eJ α₁ β₁).gam.gam (eJ α₃ β₃) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Sp_03_s0 : pwJk PJ.s0 qJ0.gam.gam qJ1.gam.gam rJ.gamT.gamT
    ((eJ α₁ β₁).gam.mul (eJ α₂ β₂)) (PJ.c 1) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Sp_03_s1 : pwJk PJ.s1 qJ0.gam.gam qJ1.gam.gam rJ.gamT.gamT
    ((eJ α₁ β₁).gam.mul (eJ α₂ β₂)) (PJ.c 1) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Sp_13_s0 : pwJk PJ.s0 ((qJ0.gam.mul (eJ α₀ β₀)).gam)
    ((qJ1.gam.mul (eJ α₀ β₀)).gam) ((rJ.gamT.mul (eJ α₀ β₀).bar).gamT) (eJ α₂ β₂) (PJ.c 1) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Sp_13_s1 : pwJk PJ.s1 ((qJ0.gam.mul (eJ α₀ β₀)).gam)
    ((qJ1.gam.mul (eJ α₀ β₀)).gam) ((rJ.gamT.mul (eJ α₀ β₀).bar).gamT) (eJ α₂ β₂) (PJ.c 1) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Sp_23'_s0 :
    pwJk PJ.s0 qJ0.gam qJ1.gam rJ.gamT ((eJ α₀ β₀).mul (eJ α₁ β₁).gam) (PJ.c 1) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Sp_23'_s1 :
    pwJk PJ.s1 qJ0.gam qJ1.gam rJ.gamT ((eJ α₀ β₀).mul (eJ α₁ β₁).gam) (PJ.c 1) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Sp_T3_s0 : pwJk PJ.s0 qJ0.gam qJ1.gam rJ.gamT (PJ.c 1) (PJ.c 1) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, qJ0, qJ1, rJ, g0, g1]

@[simp] theorem pwJk_Sp_T3_s1 : pwJk PJ.s1 qJ0.gam qJ1.gam rJ.gamT (PJ.c 1) (PJ.c 1) = 0 := by
  simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, qJ0, qJ1, rJ, g0, g1]

end Values

end QED.TwoLoop.UnitSCGraph

end
