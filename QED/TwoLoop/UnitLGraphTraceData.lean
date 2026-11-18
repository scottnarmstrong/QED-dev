/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLGraphTraceSum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The planar data of the ladder

Section 8 of `docs/TWO-LOOP-UNITS.md`, stage 1 of the L link, graph half. The momenta of the
ladder at the shifted loop point lie in the plane of `p = (m, 0, 0, 0)` and `p'`:

* the loop shift is `S_s = σ_s p + τ_s p'` with `σ_s = (A⁻¹)_{s0} z₁ + (A⁻¹)_{s1} z₀`,
  `τ_s = (A⁻¹)_{s0} z₂ + (A⁻¹)_{s1} z₃` (`loopShift_ladder`), so the momentum of chain slot `k`
  is `qₖ = aₖ p + bₖ p'` (`ladderQ_apply`);
* the Pauli matrices are planar for `μ = 0, 1` and `R γ^μ` for `μ = 2, 3`
  (`planarPauli_pauliMat`).

Hence the three coefficients `T₁, T₂, T₃` are the planar expressions of
`QED/TwoLoop/UnitLGraphTraceContract.lean` in these data (`ladderT1_planar`, `ladderT2_planar`,
`ladderT3_planar`).
-/

@[expose] public section

open Complex Matrix
open scoped Real

namespace QED.TwoLoop.UnitLGraphTrace

open QED.Dirac QED.WickModel QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero
open QED.TwoLoop.Bridge QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.TwoLoop.ParamNumEval QED.TwoLoop.UnitLGraph
open QED.Integration.TwoLoop (castLoopMatrix class5LoopMatrixPV symanzikV symanzikU symanzikMatrix
  lineMomentum loopShift)
open Pl

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-! ### The loop shift and the slot momenta -/

/-- The coefficient of `p` in the loop shift `S_s`. -/
noncomputable def sigP (z : Fin 8 → ℝ) (s : Fin 2) : ℝ :=
  (symanzikMatrix ladderAlpha z)⁻¹ s 0 * z 1 + (symanzikMatrix ladderAlpha z)⁻¹ s 1 * z 0

/-- The coefficient of `p'` in the loop shift `S_s`. -/
noncomputable def sigQ (z : Fin 8 → ℝ) (s : Fin 2) : ℝ :=
  (symanzikMatrix ladderAlpha z)⁻¹ s 0 * z 2 + (symanzikMatrix ladderAlpha z)⁻¹ s 1 * z 3

/-- **The loop shift of the ladder**: `S_s = σ_s p + τ_s p'`. -/
theorem loopShift_ladder (p p' : Fin 4 → ℝ) (z : Fin 8 → ℝ) (s : Fin 2) (μ : Fin 4) :
    loopShift ladderAlpha (pvMomentaE .L p p') z s μ = sigP z s * p μ + sigQ z s * p' μ := by
  rw [loopShift_apply]
  simp [Fin.sum_univ_succ, castLoopMatrix, class5LoopMatrixPV,
    QED.Integration.TwoLoop.class5LoopMatrix, pvMomentaE, extMomenta,
    QED.Integration.TwoLoop.classLXMomenta, QED.Integration.TwoLoop.pvLines, sigP, sigQ]
  ring

/-- The coefficient of `p` in the slot momentum `qₖ`. -/
noncomputable def slotA (z : Fin 8 → ℝ) : Fin 4 → ℝ :=
  ![-sigP z 1, -sigP z 0, 1 - sigP z 0, 1 - sigP z 1]

/-- The coefficient of `p'` in the slot momentum `qₖ`. -/
noncomputable def slotB (z : Fin 8 → ℝ) : Fin 4 → ℝ :=
  ![1 - sigQ z 1, 1 - sigQ z 0, -sigQ z 0, -sigQ z 1]

/-- **The slot momenta**: `qₖ = aₖ p + bₖ p'`. -/
theorem ladderQ_apply (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) (μ : Fin 4) :
    ladderQ P z u k μ = slotA z k * restMomentum P.m μ + slotB z k * curveMomentum P.m u μ := by
  simp only [ladderQ, QED.Integration.TwoLoop.lineMomentum, Pi.neg_apply, loopShift_ladder]
  fin_cases k <;>
    simp [Fin.sum_univ_two, castLoopMatrix, class5LoopMatrixPV,
      QED.Integration.TwoLoop.class5LoopMatrix, ladderLines, pvMomentaE, extMomenta,
      QED.Integration.TwoLoop.classLXMomenta, QED.Integration.TwoLoop.pvLines, slotA, slotB] <;>
    ring

/-! ### The planar Pauli matrices and electron numerators -/

/-- The planar coordinates `(m, k⁰, -k¹, 0)` of the electron numerator `m - k̸`. -/
def ePl (m : ℝ) (q : Fin 4 → ℝ) : Pl := ⟨(m : ℂ), (q 0 : ℂ), -(q 1 : ℂ), 0⟩

/-- The first Pauli coefficient `m(4m² + q²)`. -/
noncomputable def pauliC1 (m : ℝ) (p' p : Fin 4 → ℝ) : ℂ :=
  (m : ℂ) * (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ))

/-- The second Pauli coefficient `q² - 2m²`. -/
noncomputable def pauliC2 (m : ℝ) (p' p : Fin 4 → ℝ) : ℂ :=
  (Minkowski.dot (p' - p) (p' - p) : ℂ) - 2 * (m : ℂ) ^ 2

/-- The planar Pauli matrix `P_μ`, `μ = 0, 1` (`g` the planar `γ_μ`). -/
noncomputable def pauliQ (m : ℝ) (p' p : Fin 4 → ℝ) (g : Pl) (s : ℂ) : Pl :=
  pauliC1 m p' p • (ePl m p * g * ePl m p') + (pauliC2 m p' p * s) • (ePl m p * ePl m p')

/-- The planar factor `R` of `P_μ = R γ^μ`, `μ = 2, 3`. -/
noncomputable def pauliR (m : ℝ) (p' p : Fin 4 → ℝ) : Pl :=
  pauliC1 m p' p • (ePl m p * bar (ePl m p'))

theorem electronNumerator_ePl (m : ℝ) {q : Fin 4 → ℝ} (h2 : q 2 = 0) (h3 : q 3 = 0) :
    electronNumerator m q = toMat (ePl m q) :=
  electronNumerator_planar m h2 h3

/-- **The Pauli matrices of planar momenta are planar.** -/
theorem planarPauli_pauliMat (m : ℝ) {p' p : Fin 4 → ℝ} (h2' : p' 2 = 0) (h3' : p' 3 = 0)
    (h2 : p 2 = 0) (h3 : p 3 = 0) :
    PlanarPauli (pauliMat m p' p)
      (pauliQ m p' p g0L ((Minkowski.lower (p' + p) 0 : ℝ) : ℂ))
      (pauliQ m p' p g1 ((Minkowski.lower (p' + p) 1 : ℝ) : ℂ)) (pauliR m p' p) := by
  have hl2 : Minkowski.lower (p' + p) 2 = 0 := by simp [Minkowski.lower_eq, h2, h2']
  have hl3 : Minkowski.lower (p' + p) 3 = 0 := by simp [Minkowski.lower_eq, h3, h3']
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [pauliMat, electronNumerator_ePl m h2 h3, electronNumerator_ePl m h2' h3',
      gammaLower_zero, gammaLower_one, gammaLower_two, gammaLower_three, toMat_mul,
      toMat_mul_gamma_two_mul, toMat_mul_gamma_three_mul, hl2, hl3, pauliQ, pauliR, toMat_add,
      toMat_smul, pauliC1, pauliC2, Complex.ofReal_zero, mul_zero, zero_smul, add_zero,
      Matrix.smul_mul]

theorem restMomentum_two (m : ℝ) : restMomentum m 2 = 0 := rfl
theorem restMomentum_three (m : ℝ) : restMomentum m 3 = 0 := rfl
theorem curveMomentum_two (m u : ℝ) : curveMomentum m u 2 = 0 := rfl
theorem curveMomentum_three (m u : ℝ) : curveMomentum m u 3 = 0 := rfl

theorem ladderQ_two (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) : ladderQ P z u k 2 = 0 := by
  rw [ladderQ_apply, restMomentum_two, curveMomentum_two]; ring

theorem ladderQ_three (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) :
    ladderQ P z u k 3 = 0 := by
  rw [ladderQ_apply, restMomentum_three, curveMomentum_three]; ring

theorem ladderE_planar (P : Params) (z : Fin 8 → ℝ) (u : ℝ) (k : Fin 4) :
    ladderE P z u k = toMat (ePl P.m (ladderQ P z u k)) :=
  electronNumerator_ePl P.m (ladderQ_two P z u k) (ladderQ_three P z u k)

/-- The planar coordinates of `4m + 8 q̸`. -/
def wPl (m : ℝ) (q : Fin 4 → ℝ) : Pl := ⟨4 * (m : ℂ), -8 * (q 0 : ℂ), 8 * (q 1 : ℂ), 0⟩

theorem w_planar (m : ℝ) {q : Fin 4 → ℝ} (h2 : q 2 = 0) (h3 : q 3 = 0) :
    (4 * (m : ℂ)) • 𝟙 + (8 : ℂ) • slash q = toMat (wPl m q) := by
  rw [slash_planar h2 h3, ← toMat_one, ← toMat_smul, ← toMat_smul, ← toMat_add]
  congr 1
  ext <;> simp [wPl]

theorem two_planar : (2 : ℂ) • 𝟙 = toMat ⟨2, 0, 0, 0⟩ := by
  rw [← toMat_one, ← toMat_smul]
  congr 1
  ext <;> simp

/-! ### The three coefficients as planar expressions -/

section PlanarT

variable (P : Params) (z : Fin 8 → ℝ) (u : ℝ)

/-- The planar Pauli data along the curve. -/
noncomputable abbrev lQ0 : Pl :=
  pauliQ P.m (curveMomentum P.m u) (restMomentum P.m) g0L
    ((Minkowski.lower (curveMomentum P.m u + restMomentum P.m) 0 : ℝ) : ℂ)
/-- The planar Pauli data along the curve. -/
noncomputable abbrev lQ1 : Pl :=
  pauliQ P.m (curveMomentum P.m u) (restMomentum P.m) g1
    ((Minkowski.lower (curveMomentum P.m u + restMomentum P.m) 1 : ℝ) : ℂ)
/-- The planar Pauli data along the curve. -/
noncomputable abbrev lR : Pl := pauliR P.m (curveMomentum P.m u) (restMomentum P.m)

/-- The planar electron numerators of the chain slots. -/
noncomputable abbrev lE (k : Fin 4) : Pl := ePl P.m (ladderQ P z u k)

theorem planarPauli_ladder : PlanarPauli (ladderPauli P u) (lQ0 P u) (lQ1 P u) (lR P u) :=
  planarPauli_pauliMat P.m (curveMomentum_two _ _) (curveMomentum_three _ _)
    (restMomentum_two _) (restMomentum_three _)

/-- **`T₁` as a planar expression.** -/
theorem ladderT1_planar : ladderT1 P z u = ladderK P * ((symanzikU ladderAlpha z ^ 2 : ℝ) : ℂ)⁻¹ *
    (6 * lwPl (lQ0 P u) (lQ1 P u) (lR P u) (lE P z u 0) (lE P z u 1) (lE P z u 2) (lE P z u 3)) :=
        by
  rw [ladderT1_eq, ladderE_planar, ladderE_planar, ladderE_planar, ladderE_planar,
    lw_planar (planarPauli_ladder P u)]

/-- **`T₂` as a planar expression.** -/
theorem ladderT2_planar : ladderT2 P z u = ladderK P * ((symanzikU ladderAlpha z ^ 2 : ℝ) : ℂ)⁻¹ *
    (ladderC (symanzikMatrix ladderAlpha z) 0 1 *
        lwPl (lQ0 P u) (lQ1 P u) (lR P u) ⟨2, 0, 0, 0⟩ 1 (lE P z u 2) (lE P z u 3) +
      ladderC (symanzikMatrix ladderAlpha z) 0 2 *
        omLPl (lQ0 P u) (lQ1 P u) (lR P u) (wPl P.m (ladderQ P z u 1) * lE P z u 3) +
      ladderC (symanzikMatrix ladderAlpha z) 0 3 *
        f3Pl (lQ0 P u) (lQ1 P u) (lR P u) (lE P z u 1) (lE P z u 2) +
      ladderC (symanzikMatrix ladderAlpha z) 1 2 *
        lwPl (lQ0 P u) (lQ1 P u) (lR P u) (lE P z u 0) ⟨2, 0, 0, 0⟩ 1 (lE P z u 3) +
      ladderC (symanzikMatrix ladderAlpha z) 1 3 *
        omRPl (lQ0 P u) (lQ1 P u) (lR P u) (lE P z u 0 * wPl P.m (ladderQ P z u 2)) +
      ladderC (symanzikMatrix ladderAlpha z) 2 3 *
        lwPl (lQ0 P u) (lQ1 P u) (lR P u) (lE P z u 0) (lE P z u 1) ⟨2, 0, 0, 0⟩ 1) := by
  have hP := planarPauli_ladder P u
  rw [ladderT2_eq, ladderE_planar, ladderE_planar, ladderE_planar, ladderE_planar,
    w_planar P.m (ladderQ_two P z u 1) (ladderQ_three P z u 1),
    w_planar P.m (ladderQ_two P z u 2) (ladderQ_three P z u 2), two_planar, ← toMat_one,
    toMat_mul, toMat_mul, lw_planar hP, lw_planar hP, lw_planar hP, omL_planar hP, omR_planar hP,
    f3_planar hP]

/-- **`T₃` as a planar expression.** -/
theorem ladderT3_planar : ladderT3 P z u = ladderK P * ((symanzikU ladderAlpha z ^ 2 : ℝ) : ℂ)⁻¹ *
    (1 / 4 * (ladderC (symanzikMatrix ladderAlpha z) 0 1 * ladderC
        (symanzikMatrix ladderAlpha z) 2 3 *
        lwPl (lQ0 P u) (lQ1 P u) (lR P u) ⟨2, 0, 0, 0⟩ 1 ⟨2, 0, 0, 0⟩ 1 +
      ladderC (symanzikMatrix ladderAlpha z) 0 2 * ladderC (symanzikMatrix ladderAlpha z) 1 3 *
        (32 * omLPl (lQ0 P u) (lQ1 P u) (lR P u) 1) +
      ladderC (symanzikMatrix ladderAlpha z) 0 3 * ladderC (symanzikMatrix ladderAlpha z) 1 2 *
        f3Pl (lQ0 P u) (lQ1 P u) (lR P u) ⟨2, 0, 0, 0⟩ 1)) := by
  have hP := planarPauli_ladder P u
  rw [ladderT3_eq, two_planar, ← toMat_one, lw_planar hP, omL_planar hP, f3_planar hP]

end PlanarT

end QED.TwoLoop.UnitLGraphTrace

end
