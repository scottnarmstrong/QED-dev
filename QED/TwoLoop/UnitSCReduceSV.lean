/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCGraphSpMain
public import QED.TwoLoop.UnitSCGraphSmMain
public import QED.TwoLoop.UnitLGraphReduceV
public import QED.Integration.SimplexMerge
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The self-energy pair `S₊ + S₋` as a real simplex integral with the explicit `V`

Section 8 of `docs/TWO-LOOP-UNITS.md`, the `S + C` link, stage 2 (reductions) for the self-energy
classes, first step (the analogue of `QED/TwoLoop/UnitLGraphReduceV.lean`). At a point `z` of the
eight Feynman parameters of the Pauli–Villars form of `S₊`, with the group sums
`z_o = z₀ + z₁ + z₃` (the three outer electron lines), `Y = z₂` (the inner electron),
`z_a = z₄ + z₆`, `z_b = z₅ + z₇` (outer, inner photon; lines `4, 5` carry `m_γ`, lines `6, 7`
carry `Λ`), `s = Y + z_b`, `c = Y z_b`, `a = s z_o + c`, `U = a + s z_a`: these are the
functions `gS, gc, ga, gU` of the ladder at `(z_A, z_B) = (z_o, Y)`
(`QED.TwoLoop.UnitLGraphReduce`), and

* `symanzikV_Sp`: **the second Symanzik function at `q = 0`** (`m = 1`) is
  `V = E + m_γ² (z₄ + z₅) + Λ² (z₆ + z₇)` with the ladder's `E = (a (z_o + Y) + Y² z_a)/U`
  (`gE`); in the frame `s = 1` of section 2.2 of the document, `E = Y² + a²/U`;
* `symanzikV_Sm`: the same for `S₋`, with `z_o = z₀ + z₂ + z₃`, `Y = z₁`;
* `sixteen_pi_pow_four_mul_openZero_Sp`: **the class `S₊`** (at `m = e = 1`), normalized to the
  coefficient of `(α/π)²`, is the real integral
  `16π⁴ (1/(64 m⁵)) (1/i) openZero S₊ = (Λ² - m_γ²)² ∫_{Δ₇} selfG`, with
  `selfG = -3 z_a s a² (2U + z_a z_b)/(U⁶ V⁴) + 2 z_a s (3 Y U + 2 s z_a z_b)/(U⁵ V³)`;
* `openZero_Sm_eq_Sp`: **the mirror identity** `openZero S₋ = openZero S₊` (at `m = e = 1`): the
  `S₋` integrand is the `S₊` integrand composed with the transposition of the coordinates `1, 2`
  of the simplex, which preserves the simplex integral.

The integrand depends on the electron splits only through `z_o, Y`, and on the photon splits
through `z_a, z_b` and `V`.
-/

@[expose] public section

open Complex MeasureTheory
open scoped Real

namespace QED.TwoLoop.UnitSCReduce

open QED.WickModel QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.UnitSCGraph
open QED.TwoLoop.UnitLGraph QED.TwoLoop.UnitLGraphTrace QED.TwoLoop.UnitLGraphReduce
open QED.TwoLoop.Bridge QED.TwoLoop.Enumeration QED.TwoLoop.ParamNumEval
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.TwoLoop (castLoopMatrix class5LoopMatrixPV symanzikU symanzikV symanzikVector
  symanzikMatrix)

/-! ### The second Symanzik function at `q = 0` -/

/-- `V = E + m_γ² (z₄ + z₅) + Λ² (z₆ + z₇)` with the massless part `E` of the group sums. -/
noncomputable def selfV (P : Params) (A B a b : ℝ) (z : Fin 8 → ℝ) : ℝ :=
  gE A B a b + P.mγ ^ 2 * (z 4 + z 5) + P.Λ ^ 2 * (z 6 + z 7)

theorem symanzikVector_Sp (P : Params) (hm : P.m = 1) (z : Fin 8 → ℝ) (s : Fin 2) :
    symanzikVector (classAlpha .Sp) (pvMomentaE .Sp (restMomentum P.m) (restMomentum P.m)) z s =
      ![![spzo z + spY z, 0, 0, 0], ![spzo z, 0, 0, 0]] s := by
  funext μ
  fin_cases s <;> fin_cases μ <;>
    simp [symanzikVector, Fin.sum_univ_succ, pvMomentaE, extMomenta,
      QED.Integration.TwoLoop.classCpSpMomenta, QED.Integration.TwoLoop.pvLines, castLoopMatrix,
      class5LoopMatrixPV, QED.Integration.TwoLoop.class5LoopMatrix, restMomentum, hm, spzo, spY] <;>
    ring

theorem symanzikVector_Sm (P : Params) (hm : P.m = 1) (z : Fin 8 → ℝ) (s : Fin 2) :
    symanzikVector (classAlpha .Sm) (pvMomentaE .Sm (restMomentum P.m) (restMomentum P.m)) z s =
      ![![smzo z + smY z, 0, 0, 0], ![-smY z, 0, 0, 0]] s := by
  funext μ
  fin_cases s <;> fin_cases μ <;>
    simp [symanzikVector, Fin.sum_univ_succ, pvMomentaE, extMomenta,
      QED.Integration.TwoLoop.classCmSmMomenta, QED.Integration.TwoLoop.pvLines, castLoopMatrix,
      class5LoopMatrixPV, QED.Integration.TwoLoop.class5LoopMatrix, restMomentum, hm, smzo, smY]
  ring

theorem symanzikV_Sm (P : Params) (hm : P.m = 1) {z : Fin 8 → ℝ} (hU : smU z ≠ 0) :
    symanzikV (classAlpha .Sm) (pvMomentaE .Sm (restMomentum P.m) (restMomentum P.m))
      (pvMasses P) z = selfV P (smzo z) (smY z) (spza z) (spzb z) z := by
  unfold symanzikV
  simp only [symanzikVector_Sm P hm, inv_symanzikMatrix_Sm, Fin.sum_univ_two]
  simp [Fin.sum_univ_succ, pvMomentaE, extMomenta, QED.Integration.TwoLoop.classCmSmMomenta,
    QED.Integration.TwoLoop.pvLines, pvMasses, QED.Integration.TwoLoop.classPVMasses,
    restMomentum, hm, QED.Minkowski.dot_eq, selfV, gE]
  simp only [smU, sma, smc, smS, smzo, smY, spza, spzb, gU, ga, gS, gc] at hU ⊢
  field_simp
  ring

theorem symanzikV_Sp (P : Params) (hm : P.m = 1) {z : Fin 8 → ℝ} (hU : spU z ≠ 0) :
    symanzikV (classAlpha .Sp) (pvMomentaE .Sp (restMomentum P.m) (restMomentum P.m))
      (pvMasses P) z = selfV P (spzo z) (spY z) (spza z) (spzb z) z := by
  unfold symanzikV
  simp only [symanzikVector_Sp P hm, inv_symanzikMatrix_Sp, Fin.sum_univ_two]
  simp [Fin.sum_univ_succ, pvMomentaE, extMomenta, QED.Integration.TwoLoop.classCpSpMomenta,
    QED.Integration.TwoLoop.pvLines, pvMasses, QED.Integration.TwoLoop.classPVMasses,
    restMomentum, hm, QED.Minkowski.dot_eq, selfV, gE]
  simp only [spU, spa, spc, spS, spzo, spY, spza, spzb, gU, ga, gS, gc] at hU ⊢
  field_simp
  ring

/-! ### The real integrand -/

/-- The numerator of the `V⁻⁴` term: `-3 z_a s a² (2U + z_a z_b)`. -/
def selfN1 (A B a b : ℝ) : ℝ := -(3 * a * gS B b * ga A B b ^ 2 * (2 * gU A B a b + a * b))

/-- The numerator of the `V⁻³` term: `2 z_a s (3 Y U + 2 s z_a z_b)`. -/
def selfN2 (A B a b : ℝ) : ℝ := 2 * a * gS B b * (3 * B * gU A B a b + 2 * gS B b * a * b)

/-- The integrand in the group sums and `V`: `N₁/(U⁶ V⁴) + N₂/(U⁵ V³)`. -/
noncomputable def selfGz (A B a b V : ℝ) : ℝ :=
  selfN1 A B a b / (gU A B a b ^ 6 * V ^ 4) + selfN2 A B a b / (gU A B a b ^ 5 * V ^ 3)

/-- **The real integrand of `S₊` on `Δ₇`.** -/
noncomputable def selfG (P : Params) (z : Fin 8 → ℝ) : ℝ :=
  selfGz (spzo z) (spY z) (spza z) (spzb z) (selfV P (spzo z) (spY z) (spza z) (spzb z) z)

/-- The real integrand of `S₋` on `Δ₇`. -/
noncomputable def selfGm (P : Params) (z : Fin 8 → ℝ) : ℝ :=
  selfGz (smzo z) (smY z) (spza z) (spzb z) (selfV P (smzo z) (smY z) (spza z) (spzb z) z)

theorem self_integrand_eq_aux (c K : ℂ) (za S a U zb Y V : ℝ) (hU : U ≠ 0) :
    (c ^ 2 * (6 / K) * ((-(za * S * a ^ 2 * (2 * U + za * zb)) / (2 * U ^ 6) : ℝ) : ℂ) +
        c ^ 2 * (2 / K) * ((za * S * (3 * Y * U + 2 * S * za * zb) / U ^ 5 : ℝ) : ℂ) * (V : ℂ)) /
        (V : ℂ) ^ 4 =
      c ^ 2 / K * ((-(3 * za * S * a ^ 2 * (2 * U + za * zb)) / (U ^ 6 * V ^ 4) +
        2 * za * S * (3 * Y * U + 2 * S * za * zb) / (U ^ 5 * V ^ 3) : ℝ) : ℂ) := by
  rcases eq_or_ne V 0 with hV | hV
  · simp [hV]
  have hV' : (V : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV
  have hU' : (U : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU
  push_cast
  field_simp
  ring

theorem self_integrand_eq_Sp {P : Params} (hm : P.m = 1) (x : Fin 7 → ℝ)
    (hU : spU (simplexPoint x) ≠ 0) :
    (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
          ((-(spza (simplexPoint x) * spS (simplexPoint x) * spa (simplexPoint x) ^ 2 *
              (2 * spU (simplexPoint x) + spza (simplexPoint x) * spzb (simplexPoint x))) /
            (2 * spU (simplexPoint x) ^ 6) : ℝ) : ℂ) +
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
          ((spza (simplexPoint x) * spS (simplexPoint x) *
              (3 * spY (simplexPoint x) * spU (simplexPoint x) +
                2 * spS (simplexPoint x) * spza (simplexPoint x) * spzb (simplexPoint x)) /
            spU (simplexPoint x) ^ 5 : ℝ) : ℂ) * ((openV .Sp P x : ℝ) : ℂ)) /
        ((openV .Sp P x : ℝ) : ℂ) ^ 4 =
      ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 / kConst * ((selfG P (simplexPoint x) : ℝ) : ℂ) := by
  have hV : openV .Sp P x = selfV P (spzo (simplexPoint x)) (spY (simplexPoint x))
      (spza (simplexPoint x)) (spzb (simplexPoint x)) (simplexPoint x) := symanzikV_Sp P hm hU
  rw [hV, self_integrand_eq_aux _ _ _ _ _ _ _ _ _ hU]
  rfl

theorem self_integrand_eq_Sm {P : Params} (hm : P.m = 1) (x : Fin 7 → ℝ)
    (hU : smU (simplexPoint x) ≠ 0) :
    (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
          ((-(spza (simplexPoint x) * smS (simplexPoint x) * sma (simplexPoint x) ^ 2 *
              (2 * smU (simplexPoint x) + spza (simplexPoint x) * spzb (simplexPoint x))) /
            (2 * smU (simplexPoint x) ^ 6) : ℝ) : ℂ) +
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
          ((spza (simplexPoint x) * smS (simplexPoint x) *
              (3 * smY (simplexPoint x) * smU (simplexPoint x) +
                2 * smS (simplexPoint x) * spza (simplexPoint x) * spzb (simplexPoint x)) /
            smU (simplexPoint x) ^ 5 : ℝ) : ℂ) * ((openV .Sm P x : ℝ) : ℂ)) /
        ((openV .Sm P x : ℝ) : ℂ) ^ 4 =
      ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 / kConst * ((selfGm P (simplexPoint x) : ℝ) : ℂ) := by
  have hV : openV .Sm P x = selfV P (smzo (simplexPoint x)) (smY (simplexPoint x))
      (spza (simplexPoint x)) (spzb (simplexPoint x)) (simplexPoint x) := symanzikV_Sm P hm hU
  rw [hV, self_integrand_eq_aux _ _ _ _ _ _ _ _ _ hU]
  rfl

/-! ### The classes as real integrals -/

theorem openZero_Sp_eq_real {P : Params} (hm : P.m = 1) (he : P.e = 1) :
    openZero .Sp P = ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 / kConst *
      ((∫ x in simplexSet 7, selfG P (simplexPoint x) : ℝ) : ℂ) := by
  rw [openZero_Sp_eq hm he, ← integral_complex_ofReal, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_spU_ne_zero] with x hx
  exact self_integrand_eq_Sp hm x hx

theorem openZero_Sm_eq_real {P : Params} (hm : P.m = 1) (he : P.e = 1) :
    openZero .Sm P = ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 / kConst *
      ((∫ x in simplexSet 7, selfGm P (simplexPoint x) : ℝ) : ℂ) := by
  rw [openZero_Sm_eq hm he, ← integral_complex_ofReal, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_smU_ne_zero] with x hx
  exact self_integrand_eq_Sm hm x hx

/-- The transposition of the coordinates `1, 2`, which exchanges the line labels of `S₊` and
`S₋`. -/
def selfSwap : Equiv.Perm (Fin 8) := Equiv.swap 1 2

theorem selfGm_eq (P : Params) (z : Fin 8 → ℝ) : selfGm P z = selfG P (z ∘ selfSwap) := by
  have h0 : (z ∘ selfSwap) 0 = z 0 := rfl
  have h1 : (z ∘ selfSwap) 1 = z 2 := rfl
  have h2 : (z ∘ selfSwap) 2 = z 1 := rfl
  have h3 : (z ∘ selfSwap) 3 = z 3 := rfl
  have h4 : (z ∘ selfSwap) 4 = z 4 := rfl
  have h5 : (z ∘ selfSwap) 5 = z 5 := rfl
  have h6 : (z ∘ selfSwap) 6 = z 6 := rfl
  have h7 : (z ∘ selfSwap) 7 = z 7 := rfl
  simp only [selfGm, selfG, selfV, spzo, spY, spza, spzb, smzo, smY, h0, h1, h2, h3, h4, h5, h6, h7]

/-- **The mirror identity** `∫ selfG(S₋) = ∫ selfG(S₊)`. -/
theorem integral_selfGm (P : Params) :
    ∫ x in simplexSet 7, selfGm P (simplexPoint x) = ∫ x in simplexSet 7, selfG P (simplexPoint x) := by
  simp only [selfGm_eq]
  exact QED.Integration.SimplexMerge.integral_simplex_comp_perm selfSwap (selfG P)

/-- **The mirror identity `openZero S₋ = openZero S₊`** at `m = e = 1`. -/
theorem openZero_Sm_eq_Sp {P : Params} (hm : P.m = 1) (he : P.e = 1) :
    openZero .Sm P = openZero .Sp P := by
  rw [openZero_Sm_eq_real hm he, openZero_Sp_eq_real hm he, integral_selfGm]

/-- **The class `S₊` as a real simplex integral** (`m = e = 1`), normalized to the coefficient of
`(α/π)²`: `16π⁴ (1/(64 m⁵)) (1/i) openZero S₊ = (Λ² - m_γ²)² ∫_{Δ₇} selfG`. -/
theorem sixteen_pi_pow_four_mul_openZero_Sp {P : Params} (hm : P.m = 1) (he : P.e = 1) :
    16 * (π : ℂ) ^ 4 * (1 / (64 * (P.m : ℂ) ^ 5) * ((1 / I) * openZero .Sp P)) =
      (((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * ∫ x in simplexSet 7, selfG P (simplexPoint x) : ℝ) : ℂ) := by
  rw [openZero_Sp_eq_real hm he, hm]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [kConst]
  push_cast
  field_simp

end QED.TwoLoop.UnitSCReduce

end
