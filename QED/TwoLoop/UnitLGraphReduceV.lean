/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLGraphTraceMain
public import QED.TwoLoop.UnitLLinkCt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The ladder graph half as a real simplex integral with the explicit `V`

Section 8 of `docs/TWO-LOOP-UNITS.md`, stage 1 of the L link, graph half, item (ii), first step.
At a point `z` of the eight Feynman parameters of the Pauli–Villars form of the ladder, with the
group sums `z_A = z₀ + z₃`, `z_B = z₁ + z₂` (outer, inner electron pair), `z_a = z₄ + z₆`,
`z_b = z₅ + z₇` (outer, inner photon; lines `4, 5` carry `m_γ`, lines `6, 7` carry `Λ`), and
`s = z_B + z_b`, `c = z_B z_b`, `a = s z_A + c`, `U = a + s z_a`:

* `openV_L_eq`: **the second Symanzik function at `q = 0`** (`m = 1`) is
  `V = E + m_γ² (z₄ + z₅) + Λ² (z₆ + z₇)`, `E = (a (z_A + z_B) + z_B² z_a)/U`
  (in the frame `s = 1`, `E = Y² + a²/U`, the `Y² + a²/U` of eq. (2.1) of the document);
* `sixteen_pi_pow_four_mul_graphHalf`: **the ladder graph half** (at `m = e = 1`), normalized to
  the coefficient of `(α/π)²`, is the real integral
  `16π⁴ · graphHalf P = (Λ² - m_γ²)² ∫_{Δ₇} [3 z_a Q/(U⁵ V⁴) + z_a (9c + a)/(U⁴ V³)]`
  (`ladderG`), with `Q` of `QED/TwoLoop/UnitLGraphTraceMain.lean`.

The integrand depends on the electron splits only through `z_A, z_B`, and on the photon splits
through `z_a, z_b` and `V`.
-/

@[expose] public section

open Complex MeasureTheory
open scoped Real

namespace QED.TwoLoop.UnitLGraphReduce

open QED.WickModel QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.UnitLGraph
open QED.TwoLoop.UnitLGraphTrace QED.TwoLoop.Bridge
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.TwoLoop (castLoopMatrix class5LoopMatrixPV symanzikV symanzikVector
  symanzikMatrix)

/-! ### Functions of the group sums -/

/-- `s = z_B + z_b`. -/
def gS (B b : ℝ) : ℝ := B + b
/-- `c = z_B z_b`. -/
def gc (B b : ℝ) : ℝ := B * b
/-- `a = s z_A + c`. -/
def ga (A B b : ℝ) : ℝ := gS B b * A + gc B b
/-- `U = a + s z_a`. -/
def gU (A B a b : ℝ) : ℝ := ga A B b + gS B b * a
/-- `Q = (3z_B - 2s) a² + (4 z_B s - z_B² - 2s²) a z_a - 2 s c z_a²`. -/
def gQ (A B a b : ℝ) : ℝ :=
  (3 * B - 2 * gS B b) * ga A B b ^ 2 + (4 * B * gS B b - B ^ 2 - 2 * gS B b ^ 2) * ga A B b * a -
    2 * gS B b * gc B b * a ^ 2
/-- The massless part `E = (a (z_A + z_B) + z_B² z_a)/U` of `V`. -/
noncomputable def gE (A B a b : ℝ) : ℝ := (ga A B b * (A + B) + B ^ 2 * a) / gU A B a b

theorem lU_eq (z : Fin 8 → ℝ) : lU z = gU (lzA z) (lzB z) (lza z) (lzb z) := rfl
theorem la_eq (z : Fin 8 → ℝ) : la z = ga (lzA z) (lzB z) (lzb z) := rfl
theorem lc_eq (z : Fin 8 → ℝ) : lc z = gc (lzB z) (lzb z) := rfl
theorem lQ_eq (z : Fin 8 → ℝ) : lQ z = gQ (lzA z) (lzB z) (lza z) (lzb z) := rfl

/-! ### The second Symanzik function at `q = 0` -/

/-- `V = E + m_γ² (z₄ + z₅) + Λ² (z₆ + z₇)` at a point of the eight parameters. -/
noncomputable def ladderV (P : Params) (z : Fin 8 → ℝ) : ℝ :=
  gE (lzA z) (lzB z) (lza z) (lzb z) + P.mγ ^ 2 * (z 4 + z 5) + P.Λ ^ 2 * (z 6 + z 7)

theorem symanzikVector_ladder (P : Params) (hm : P.m = 1) (z : Fin 8 → ℝ) (s : Fin 2) :
    symanzikVector ladderAlpha (pvMomentaE .L (restMomentum P.m) (restMomentum P.m)) z s =
      ![![lzB z, 0, 0, 0], ![lzA z, 0, 0, 0]] s := by
  funext μ
  fin_cases s <;> fin_cases μ <;>
    simp [symanzikVector, Fin.sum_univ_succ, pvMomentaE, extMomenta,
      QED.Integration.TwoLoop.classLXMomenta, QED.Integration.TwoLoop.pvLines, castLoopMatrix,
      class5LoopMatrixPV, QED.Integration.TwoLoop.class5LoopMatrix, restMomentum, hm, lzA, lzB]

/-- **The second Symanzik function of the ladder at `q = 0`**, at `m = 1`, for `U ≠ 0`. -/
theorem symanzikV_ladder (P : Params) (hm : P.m = 1) {z : Fin 8 → ℝ} (hU : lU z ≠ 0) :
    symanzikV ladderAlpha (pvMomentaE .L (restMomentum P.m) (restMomentum P.m)) (pvMasses P) z =
      ladderV P z := by
  unfold symanzikV
  simp only [symanzikVector_ladder P hm, inv_symanzikMatrix_ladder, Fin.sum_univ_two]
  simp [Fin.sum_univ_succ, pvMomentaE, extMomenta, QED.Integration.TwoLoop.classLXMomenta,
    QED.Integration.TwoLoop.pvLines, pvMasses, QED.Integration.TwoLoop.classPVMasses,
    restMomentum, hm, QED.Minkowski.dot_eq, ladderV, gE]
  simp only [lU, la, lc, lS, lzA, lzB, lza, lzb, gU, ga, gS, gc] at hU ⊢
  field_simp
  ring

/-- **`openV .L` with the explicit `V`** (at `m = 1`, `U ≠ 0`). -/
theorem openV_L_eq {P : Params} (hm : P.m = 1) (x : Fin 7 → ℝ)
    (hU : lU (simplexPoint x) ≠ 0) : openV .L P x = ladderV P (simplexPoint x) :=
  symanzikV_ladder P hm hU

/-! ### The real integrand -/

/-- **The real integrand of the ladder graph half on `Δ₇`**:
`3 z_a Q/(U⁵ V⁴) + z_a (9c + a)/(U⁴ V³)`. -/
noncomputable def ladderG (P : Params) (z : Fin 8 → ℝ) : ℝ :=
  3 * lza z * gQ (lzA z) (lzB z) (lza z) (lzb z) /
      (gU (lzA z) (lzB z) (lza z) (lzb z) ^ 5 * ladderV P z ^ 4) +
    lza z * (9 * gc (lzB z) (lzb z) + ga (lzA z) (lzB z) (lzb z)) /
      (gU (lzA z) (lzB z) (lza z) (lzb z) ^ 4 * ladderV P z ^ 3)

theorem integrand_eq_aux (c K : ℂ) (za Q U V cc aa : ℝ) (hU : U ≠ 0) :
    (c ^ 2 * (6 / K) * ((za * Q / (2 * U ^ 5) : ℝ) : ℂ) +
        c ^ 2 * (2 / K) * ((za * (9 * cc + aa) / (2 * U ^ 4) : ℝ) : ℂ) * (V : ℂ)) / (V : ℂ) ^ 4 =
      c ^ 2 / K * ((3 * za * Q / (U ^ 5 * V ^ 4) + za * (9 * cc + aa) / (U ^ 4 * V ^ 3) : ℝ) : ℂ) := by
  rcases eq_or_ne V 0 with hV | hV
  · simp [hV]
  have hV' : (V : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV
  have hU' : (U : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU
  push_cast
  field_simp
  ring

theorem integrand_eq {P : Params} (hm : P.m = 1) (x : Fin 7 → ℝ)
    (hU : lU (simplexPoint x) ≠ 0) :
    (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
          ((lza (simplexPoint x) * lQ (simplexPoint x) / (2 * lU (simplexPoint x) ^ 5) : ℝ) : ℂ) +
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
          ((lza (simplexPoint x) * (9 * lc (simplexPoint x) + la (simplexPoint x)) /
            (2 * lU (simplexPoint x) ^ 4) : ℝ) : ℂ) * ((openV .L P x : ℝ) : ℂ)) /
        ((openV .L P x : ℝ) : ℂ) ^ 4 =
      ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 / kConst * ((ladderG P (simplexPoint x) : ℝ) : ℂ) := by
  rw [openV_L_eq hm x hU, integrand_eq_aux _ _ _ _ _ _ _ _ hU]
  rfl

/-- **The ladder graph half as a real simplex integral** (`m = e = 1`), normalized to the
coefficient of `(α/π)²`: `16π⁴ · graphHalf P = (Λ² - m_γ²)² ∫_{Δ₇} ladderG`. -/
theorem sixteen_pi_pow_four_mul_graphHalf {P : Params} (hm : P.m = 1) (he : P.e = 1) :
    16 * (π : ℂ) ^ 4 * QED.TwoLoop.UnitLLink.graphHalf P =
      (((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * ∫ x in simplexSet 7, ladderG P (simplexPoint x) : ℝ) : ℂ) := by
  have h : openZero .L P = ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 / kConst *
      ∫ x in simplexSet 7, ((ladderG P (simplexPoint x) : ℝ) : ℂ) := by
    rw [openZero_L_eq hm he, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_lU_ne_zero] with x hx
    exact integrand_eq hm x hx
  rw [QED.TwoLoop.UnitLLink.graphHalf, h, integral_complex_ofReal, hm]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [kConst]
  push_cast
  field_simp

end QED.TwoLoop.UnitLGraphReduce

end
