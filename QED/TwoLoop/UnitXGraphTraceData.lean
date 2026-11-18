/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXGraphTracePlanar
public import QED.TwoLoop.UnitLGraphTraceData
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The planar data of the crossed ladder

Section 8 of `docs/TWO-LOOP-UNITS.md`, the graph half of the X unit. The momenta of the crossed
ladder at the shifted loop point lie in the plane of `p = (m, 0, 0, 0)` and `p'`:

* the loop shift is `S_s = σ_s p + τ_s p'` with `σ_s = (A⁻¹)_{s0} (z₀ + z₁) - (A⁻¹)_{s1} z₀`,
  `τ_s = (A⁻¹)_{s0} z₂ + (A⁻¹)_{s1} z₃` (`loopShift_crossed`), so the momentum of chain slot `k`
  is `qₖ = aₖ p + bₖ p'` (`crossedQ_apply`);
* the Pauli matrices are those of the ladder (`QED.TwoLoop.UnitLGraphTrace.planarPauli_ladder`).

With the reductions of `QED/TwoLoop/UnitXGraphTraceReduce.lean` and
`QED/TwoLoop/UnitXGraphTraceWick.lean`, the three coefficients `T₁, T₂, T₃` are planar
expressions in these data (`crossedT1_planar`, `crossedT2_planar`, `crossedT3_planar`), with
`eₖ = (m, qₖ⁰, -qₖ¹, 0)` the planar electron numerators, `ēₖ` their grade involutes (the planar
form of `m + q̸ₖ`) and `sₖ = (0, -qₖ⁰, qₖ¹, 0)` the planar form of `q̸ₖ`.
-/

@[expose] public section

open Complex Matrix
open scoped Real

namespace QED.TwoLoop.UnitXGraph

open QED.Dirac QED.WickModel QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero
open QED.TwoLoop.Bridge QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.TwoLoop.ParamNumEval QED.TwoLoop.UnitLGraph QED.TwoLoop.UnitLGraphTrace
open QED.Integration.TwoLoop (castLoopMatrix class5LoopMatrixPV symanzikV symanzikU symanzikMatrix
  lineMomentum loopShift)
open Pl

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-! ### The loop shift and the slot momenta -/

/-- The coefficient of `p` in the loop shift `S_s`. -/
noncomputable def xsigP (z : Fin 8 → ℝ) (s : Fin 2) : ℝ :=
  (symanzikMatrix crossedAlpha z)⁻¹ s 0 * (z 0 + z 1) - (symanzikMatrix crossedAlpha z)⁻¹ s 1 * z 0

/-- The coefficient of `p'` in the loop shift `S_s`. -/
noncomputable def xsigQ (z : Fin 8 → ℝ) (s : Fin 2) : ℝ :=
  (symanzikMatrix crossedAlpha z)⁻¹ s 0 * z 2 + (symanzikMatrix crossedAlpha z)⁻¹ s 1 * z 3

/-- **The loop shift of the crossed ladder**: `S_s = σ_s p + τ_s p'`. -/
theorem loopShift_crossed (p p' : Fin 4 → ℝ) (z : Fin 8 → ℝ) (s : Fin 2) (μ : Fin 4) :
    loopShift crossedAlpha (pvMomentaE .X p p') z s μ = xsigP z s * p μ + xsigQ z s * p' μ := by
  rw [loopShift_apply]
  simp [Fin.sum_univ_succ, castLoopMatrix, class5LoopMatrixPV,
    QED.Integration.TwoLoop.class5LoopMatrix, pvMomentaE, extMomenta,
    QED.Integration.TwoLoop.classLXMomenta, QED.Integration.TwoLoop.pvLines, xsigP, xsigQ]
  ring

/-- The coefficient of `p` in the slot momentum `qₖ`. -/
noncomputable def xslotA (z : Fin 8 → ℝ) : Fin 4 → ℝ :=
  ![-xsigP z 1, -xsigP z 0, 1 - xsigP z 0, 1 - xsigP z 0 + xsigP z 1]

/-- The coefficient of `p'` in the slot momentum `qₖ`. -/
noncomputable def xslotB (z : Fin 8 → ℝ) : Fin 4 → ℝ :=
  ![1 - xsigQ z 1, 1 - xsigQ z 0, -xsigQ z 0, -xsigQ z 0 + xsigQ z 1]

/-- **The slot momenta**: `qₖ = aₖ p + bₖ p'`. -/
theorem crossedQ_apply (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) (μ : Fin 4) :
    crossedQ P z u k μ = xslotA z k * restMomentum P.m μ + xslotB z k * curveMomentum P.m u μ := by
  simp only [crossedQ, QED.Integration.TwoLoop.lineMomentum, Pi.neg_apply, loopShift_crossed]
  fin_cases k <;>
    simp [Fin.sum_univ_two, castLoopMatrix, class5LoopMatrixPV,
      QED.Integration.TwoLoop.class5LoopMatrix, crossedLines, pvMomentaE, extMomenta,
      QED.Integration.TwoLoop.classLXMomenta, QED.Integration.TwoLoop.pvLines, xslotA, xslotB] <;>
    ring

theorem crossedQ_two (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) :
    crossedQ P z u k 2 = 0 := by
  rw [crossedQ_apply, restMomentum_two, curveMomentum_two]; ring

theorem crossedQ_three (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) :
    crossedQ P z u k 3 = 0 := by
  rw [crossedQ_apply, restMomentum_three, curveMomentum_three]; ring

/-! ### The planar forms of the slot matrices -/

/-- The planar coordinates `(0, -k⁰, k¹, 0)` of `k̸`. -/
def sPl (q : Fin 4 → ℝ) : Pl := ⟨0, -(q 0 : ℂ), (q 1 : ℂ), 0⟩

section Slots

variable (P : Params) (z : Fin 8 → ℝ) (u : ℝ)

/-- The planar electron numerator of the chain slot `k`. -/
noncomputable abbrev xE (k : Fin 4) : Pl := ePl P.m (crossedQ P z u k)

/-- The planar form of the slash of the slot momentum `k`. -/
noncomputable abbrev xS (k : Fin 4) : Pl := sPl (crossedQ P z u k)

theorem crossedE_planar (k : Fin 4) : crossedE P z u k = toMat (xE P z u k) :=
  electronNumerator_ePl P.m (crossedQ_two P z u k) (crossedQ_three P z u k)

theorem slash_crossedQ (k : Fin 4) : slash (crossedQ P z u k) = toMat (xS P z u k) :=
  slash_planar (crossedQ_two P z u k) (crossedQ_three P z u k)

theorem crossedE_eq_sub (k : Fin 4) :
    crossedE P z u k = (P.m : ℂ) • 𝟙 - slash (crossedQ P z u k) := rfl

theorem elecBar_planar (k : Fin 4) :
    (P.m : ℂ) • 𝟙 + slash (crossedQ P z u k) = toMat (bar (xE P z u k)) := by
  rw [slash_crossedQ, ← toMat_one, ← toMat_smul, ← toMat_add]
  congr 1
  ext <;> simp [sPl, ePl, bar]

end Slots

theorem slash_zero' : slash (0 : Fin 4 → ℝ) = 0 := by
  have h := slash_smul 0 (0 : Fin 4 → ℝ)
  simpa using h

/-- The crossed contraction with a constant first slot. -/
theorem xw_const (P' : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (c : ℂ)
    (Y₁ Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ) :
    xw P' (c • 𝟙) Y₁ Y₂ Y₃ = -lw P' 𝟙 (c • Y₁) Y₂ Y₃ - 2 * bs P' (c • Y₁) Y₂ Y₃ := by
  have h := xw_elec P' c 0 Y₁ Y₂ Y₃
  rw [slash_zero', sub_zero, add_zero, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_zero] at h
  rw [h]
  have : hg P' Y₁ Y₂ 0 = 0 := by simp [hg]
  rw [this]
  ring

/-! ### The three coefficients as planar expressions -/

section PlanarT

variable (P : Params) (z : Fin 8 → ℝ) (u : ℝ)

/-- The planar constant `2`. -/
abbrev two₂ : Pl := ⟨2, 0, 0, 0⟩

/-- **`T₁` as a planar expression**: `T₁ = K U⁻² · 6 xw(P; e)` with
`xw(P; e) = -lw(P; 1, ē₀ e₁, e₂, e₃) - 2 bs(P; ē₀ e₁, e₂, e₃) + 2 hg(P; e₁, e₂, e₃ s₀)`. -/
theorem crossedT1_planar : crossedT1 P z u =
    ladderK P * ((symanzikU crossedAlpha z ^ 2 : ℝ) : ℂ)⁻¹ *
      (6 * (-lwPl (lQ0 P u) (lQ1 P u) (lR P u) 1 (bar (xE P z u 0) * xE P z u 1) (xE P z u 2)
          (xE P z u 3) -
        2 * bsPl (lQ0 P u) (lQ1 P u) (lR P u) (bar (xE P z u 0) * xE P z u 1) (xE P z u 2)
          (xE P z u 3) +
        2 * hgPl (lQ0 P u) (lQ1 P u) (lR P u) (xE P z u 1) (xE P z u 2)
          (xE P z u 3 * xS P z u 0))) := by
  have hP := planarPauli_ladder P u
  rw [crossedT1_eq, crossedE_eq_sub P z u 0, xw_elec, elecBar_planar, slash_crossedQ,
    crossedE_planar, crossedE_planar, crossedE_planar, toMat_mul, toMat_mul, ← toMat_one,
    lw_planar hP, bs_planar hP, hg_planar hP]

/-- **`T₂` as a planar expression**: the six single contractions. -/
theorem crossedT2_planar : crossedT2 P z u =
    ladderK P * ((symanzikU crossedAlpha z ^ 2 : ℝ) : ℂ)⁻¹ *
      (crossedC (symanzikMatrix crossedAlpha z) 0 1 *
          (-lwPl (lQ0 P u) (lQ1 P u) (lR P u) 1 two₂ (xE P z u 2) (xE P z u 3) -
            2 * bsPl (lQ0 P u) (lQ1 P u) (lR P u) two₂ (xE P z u 2) (xE P z u 3)) +
        crossedC (symanzikMatrix crossedAlpha z) 0 2 *
          (-16 * (P.m : ℂ) * om0Pl (lQ0 P u) (lQ1 P u) (lR P u) (xE P z u 3) 1 -
            4 * omGPl (lQ0 P u) (lQ1 P u) (lR P u) (xS P z u 1) (xE P z u 3)) +
        crossedC (symanzikMatrix crossedAlpha z) 0 3 *
          (4 * hgPl (lQ0 P u) (lQ1 P u) (lR P u) (xE P z u 1) (xE P z u 2) 1 +
            16 * omGPl (lQ0 P u) (lQ1 P u) (lR P u) (xE P z u 1) (xE P z u 2) -
            f3Pl (lQ0 P u) (lQ1 P u) (lR P u) (xE P z u 1) (xE P z u 2)) +
        crossedC (symanzikMatrix crossedAlpha z) 1 2 *
          (-lwPl (lQ0 P u) (lQ1 P u) (lR P u) 1 (bar (xE P z u 0) * two₂) 1 (xE P z u 3) -
            2 * bsPl (lQ0 P u) (lQ1 P u) (lR P u) (bar (xE P z u 0) * two₂) 1 (xE P z u 3) +
            2 * hgPl (lQ0 P u) (lQ1 P u) (lR P u) two₂ 1 (xE P z u 3 * xS P z u 0)) +
        crossedC (symanzikMatrix crossedAlpha z) 1 3 *
          (-16 * (P.m : ℂ) * om0Pl (lQ0 P u) (lQ1 P u) (lR P u) 1 (xE P z u 0) -
            4 * (P.m : ℂ) * omGPl (lQ0 P u) (lQ1 P u) (lR P u) (xS P z u 2) 1 +
            8 * om0Pl (lQ0 P u) (lQ1 P u) (lR P u) (xS P z u 2) (xS P z u 0)) +
        crossedC (symanzikMatrix crossedAlpha z) 2 3 *
          (-lwPl (lQ0 P u) (lQ1 P u) (lR P u) 1 (bar (xE P z u 0) * xE P z u 1) two₂ 1 -
            2 * bsPl (lQ0 P u) (lQ1 P u) (lR P u) (bar (xE P z u 0) * xE P z u 1) two₂ 1 +
            2 * hgPl (lQ0 P u) (lQ1 P u) (lR P u) (xE P z u 1) two₂ (xS P z u 0))) := by
  have hP := planarPauli_ladder P u
  rw [crossedT2_eq, sum_xw_01, sum_xw_12, sum_xw_23, crossedE_eq_sub P z u 1, sum_xw_02,
    crossedE_eq_sub P z u 0, crossedE_eq_sub P z u 2, sum_xw_13, sum_xw_03, xw_const,
    xw_elec, xw_elec]
  simp only [elecBar_planar]
  simp only [← crossedE_eq_sub]
  simp only [crossedE_planar, slash_crossedQ, two_planar, Matrix.one_mul]
  simp only [toMat_mul]
  simp only [← toMat_one]
  simp only [lw_planar hP, bs_planar hP, hg_planar hP, omG_planar hP, om0_planar hP,
    f3_planar hP]

/-- **`T₃` as a planar expression**: the three double contractions. -/
theorem crossedT3_planar : crossedT3 P z u =
    ladderK P * ((symanzikU crossedAlpha z ^ 2 : ℝ) : ℂ)⁻¹ *
      (1 / 4 * (crossedC (symanzikMatrix crossedAlpha z) 0 1 *
          crossedC (symanzikMatrix crossedAlpha z) 2 3 *
          (-lwPl (lQ0 P u) (lQ1 P u) (lR P u) 1 two₂ two₂ 1 -
            2 * bsPl (lQ0 P u) (lQ1 P u) (lR P u) two₂ two₂ 1) +
        crossedC (symanzikMatrix crossedAlpha z) 0 2 *
          crossedC (symanzikMatrix crossedAlpha z) 1 3 *
          (8 * omGPl (lQ0 P u) (lQ1 P u) (lR P u) 1 1) +
        crossedC (symanzikMatrix crossedAlpha z) 0 3 *
          crossedC (symanzikMatrix crossedAlpha z) 1 2 *
          (4 * hgPl (lQ0 P u) (lQ1 P u) (lR P u) two₂ 1 1 +
            16 * omGPl (lQ0 P u) (lQ1 P u) (lR P u) two₂ 1 -
            f3Pl (lQ0 P u) (lQ1 P u) (lR P u) two₂ 1))) := by
  have hP := planarPauli_ladder P u
  rw [crossedT3_eq, sum_xw_0123, sum_xw_0213, sum_xw_0312, xw_const]
  simp only [two_planar]
  simp only [← toMat_one]
  simp only [lw_planar hP, bs_planar hP, hg_planar hP, omG_planar hP, f3_planar hP]

end PlanarT

end QED.TwoLoop.UnitXGraph

end
