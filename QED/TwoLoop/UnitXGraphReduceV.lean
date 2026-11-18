/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXGraphTraceMain
public import QED.TwoLoop.UnitsRegulated
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The crossed-ladder unit as a real simplex integral with the explicit `V`

Section 8 of `docs/TWO-LOOP-UNITS.md`, the graph half of the X unit, item (ii), first step (the
analogue of `QED/TwoLoop/UnitLGraphReduceV.lean`). At a point `z` of the eight Feynman parameters
of the Pauli–Villars form of the crossed ladder, with the group sums `z_A = z₀`, `z_M = z₁ + z₂`,
`z_c = z₃`, `z_a = z₄ + z₆`, `z_b = z₅ + z₇` (lines `4, 5` carry `m_γ`, lines `6, 7` carry `Λ`):

* `openV_X_eq`: **the second Symanzik function at `q = 0`** (`m = 1`) is
  `V = E + m_γ² (z₄ + z₅) + Λ² (z₆ + z₇)` with `E = Ẽ/U` (`gXE`),
  `Ẽ = z_A² (z_M + z_b + z_c) + z_A z_M² + 2 z_A z_M (z_b + z_c) + z_A z_c² + z_M² (z_a + z_b + z_c)
  + 2 z_M z_a z_c + z_M z_c² + z_a z_c²` (`gXEn`). In the frame `z_M + z_c + z_b = 1` of
  section 2.2 of the document, `E = Y² + b²/U` with `Y = z_M + z_c` and `b = z_A + z_M z_b`;
* `sixteen_pi_pow_four_mul_unitF2_X`: **the crossed-ladder unit** (at `m = e = 1`), normalized to
  the coefficient of `(α/π)²`, is the real integral
  `16π⁴ · unitF2 X P = (Λ² - m_γ²)² ∫_{Δ₇} [3 Ψ₁/(U⁶ V⁴) - Ψ₂/(U⁵ V³)]` (`crossedG`), with the
  polynomials `Ψ₁, Ψ₂` of `QED/TwoLoop/UnitXGraphTraceMain.lean`.

The integrand depends on the photon splits through `z_a, z_b` and `V`, and on the split `t = z₁`
of the electron pair through `Ψ₁, Ψ₂`, which are affine in `t`.
-/

@[expose] public section

open Complex MeasureTheory
open scoped Real

namespace QED.TwoLoop.UnitXGraph

open QED.WickModel QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.UnitLGraph
open QED.TwoLoop.UnitLGraphTrace QED.TwoLoop.Bridge QED.TwoLoop.UnitsRegulated
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.TwoLoop (castLoopMatrix class5LoopMatrixPV symanzikV symanzikVector
  symanzikMatrix)

/-! ### The second Symanzik function at `q = 0` -/

/-- The numerator `Ẽ = U E` of the massless part of `V`, in the group sums. -/
def gXEn (A M c a b : ℝ) : ℝ :=
  A ^ 2 * (M + b + c) + A * M ^ 2 + 2 * A * M * (b + c) + A * c ^ 2 +
    M ^ 2 * (a + b + c) + 2 * M * a * c + M * c ^ 2 + a * c ^ 2

/-- The massless part `E = Ẽ/U` of `V`. -/
noncomputable def gXE (A M c a b : ℝ) : ℝ := gXEn A M c a b / gXU A M c a b

/-- `V = E + m_γ² (z₄ + z₅) + Λ² (z₆ + z₇)` at a point of the eight parameters. -/
noncomputable def crossedV (P : Params) (z : Fin 8 → ℝ) : ℝ :=
  gXE (xA z) (xM z) (xc z) (xa z) (xb z) + P.mγ ^ 2 * (z 4 + z 5) + P.Λ ^ 2 * (z 6 + z 7)

theorem symanzikVector_crossed (P : Params) (hm : P.m = 1) (z : Fin 8 → ℝ) (s : Fin 2) :
    symanzikVector crossedAlpha (pvMomentaE .X (restMomentum P.m) (restMomentum P.m)) z s =
      ![![z 0 + z 1 + z 2, 0, 0, 0], ![z 3 - z 0, 0, 0, 0]] s := by
  funext μ
  fin_cases s <;> fin_cases μ <;>
    simp [symanzikVector, Fin.sum_univ_succ, pvMomentaE, extMomenta,
      QED.Integration.TwoLoop.classLXMomenta, QED.Integration.TwoLoop.pvLines, castLoopMatrix,
      class5LoopMatrixPV, QED.Integration.TwoLoop.class5LoopMatrix, restMomentum, hm] <;> ring

/-- **The second Symanzik function of the crossed ladder at `q = 0`**, at `m = 1` (for `U = 0`
both sides are evaluated with `x / 0 = 0`). -/
theorem symanzikV_crossed (P : Params) (hm : P.m = 1) (z : Fin 8 → ℝ) :
    symanzikV crossedAlpha (pvMomentaE .X (restMomentum P.m) (restMomentum P.m)) (pvMasses P) z =
      crossedV P z := by
  unfold symanzikV
  simp only [symanzikVector_crossed P hm, inv_symanzikMatrix_crossed, Fin.sum_univ_two]
  simp [Fin.sum_univ_succ, pvMomentaE, extMomenta, QED.Integration.TwoLoop.classLXMomenta,
    QED.Integration.TwoLoop.pvLines, pvMasses, QED.Integration.TwoLoop.classPVMasses,
    restMomentum, hm, QED.Minkowski.dot_eq, crossedV, gXE]
  simp only [xU, gXU, gXEn, xA, xM, xc, xa, xb]
  field_simp
  ring

/-- **`openV .X` with the explicit `V`** (at `m = 1`). -/
theorem openV_X_eq {P : Params} (hm : P.m = 1) (x : Fin 7 → ℝ) :
    openV .X P x = crossedV P (simplexPoint x) :=
  symanzikV_crossed P hm _

/-! ### The real integrand -/

/-- **The real integrand of the crossed-ladder unit on `Δ₇`**: `3 Ψ₁/(U⁶ V⁴) - Ψ₂/(U⁵ V³)`. -/
noncomputable def crossedG (P : Params) (z : Fin 8 → ℝ) : ℝ :=
  3 * xPsi1 z / (xU z ^ 6 * crossedV P z ^ 4) - xPsi2 z / (xU z ^ 5 * crossedV P z ^ 3)

theorem crossed_integrand_eq_aux (c K : ℂ) (P1 P2 U V : ℝ) (hU : U ≠ 0) :
    (c ^ 2 * (3 / K) * ((P1 / U ^ 6 : ℝ) : ℂ) + -(c ^ 2 * (1 / K) * ((P2 / U ^ 5 : ℝ) : ℂ)) *
        (V : ℂ)) / (V : ℂ) ^ 4 =
      c ^ 2 / K * ((3 * P1 / (U ^ 6 * V ^ 4) - P2 / (U ^ 5 * V ^ 3) : ℝ) : ℂ) := by
  rcases eq_or_ne V 0 with hV | hV
  · simp [hV]
  have hV' : (V : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV
  have hU' : (U : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU
  push_cast
  field_simp
  ring

theorem crossed_integrand_eq {P : Params} (hm : P.m = 1) (x : Fin 7 → ℝ)
    (hU : xU (simplexPoint x) ≠ 0) :
    (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (3 / kConst) *
          ((xPsi1 (simplexPoint x) / xU (simplexPoint x) ^ 6 : ℝ) : ℂ) +
        -(((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (1 / kConst) *
          ((xPsi2 (simplexPoint x) / xU (simplexPoint x) ^ 5 : ℝ) : ℂ)) *
          ((openV .X P x : ℝ) : ℂ)) /
        ((openV .X P x : ℝ) : ℂ) ^ 4 =
      ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 / kConst * ((crossedG P (simplexPoint x) : ℝ) : ℂ) := by
  rw [openV_X_eq hm x, crossed_integrand_eq_aux _ _ _ _ _ _ hU]
  rfl

/-- **The crossed-ladder unit as a real simplex integral** (`m = e = 1`), normalized to the
coefficient of `(α/π)²`: `16π⁴ · unitF2 X P = (Λ² - m_γ²)² ∫_{Δ₇} crossedG`. -/
theorem sixteen_pi_pow_four_mul_unitF2_X {P : Params} (hm : P.m = 1) (he : P.e = 1) :
    16 * (π : ℂ) ^ 4 * unitF2 .X P =
      (((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * ∫ x in simplexSet 7, crossedG P (simplexPoint x) : ℝ) : ℂ) := by
  have h : openZero .X P = ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 / kConst *
      ∫ x in simplexSet 7, ((crossedG P (simplexPoint x) : ℝ) : ℂ) := by
    rw [openZero_X_eq hm he, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_xU_ne_zero] with x hx
    exact crossed_integrand_eq hm x hx
  rw [unitF2, unitZero, h, integral_complex_ofReal, hm]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [kConst]
  push_cast
  field_simp

end QED.TwoLoop.UnitXGraph

end
