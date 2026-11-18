/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCGraphCpMain
public import QED.TwoLoop.UnitSCGraphCmMain
public import QED.TwoLoop.UnitSCReduceSV
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The corner pair `C₊ + C₋` as a real simplex integral with the explicit `V`

Section 8 of `docs/TWO-LOOP-UNITS.md`, the `S + C` link, reductions for the corner classes, first
step (the analogue of `QED/TwoLoop/UnitSCReduceSV.lean`). At a point `z` of the eight Feynman
parameters of the Pauli–Villars form of `C₊`, with the group sums `z_o = z₀ + z₁` (the outer
electron pair), `y₃ = z₂`, `y₄ = z₃` (the electrons of the inner vertex subgraph),
`z_a = z₄ + z₆`, `z_b = z₅ + z₇` (outer, inner photon; lines `4, 5` carry `m_γ`, lines `6, 7`
carry `Λ`), and `U = (z_o + y₃ + z_a)(z_o + y₄ + z_a + z_b) - (z_o + z_a)²` (`gCU`):

* `symanzikV_Cp`: **the second Symanzik function at `q = 0`** (`m = 1`) is
  `V = E + m_γ² (z₄ + z₅) + Λ² (z₆ + z₇)` with `E = Ẽ/U` (`gCE`),
  `Ẽ = y₃²(y₄ + z_a + z_b + z_o) + y₃ y₄² + 2y₃y₄(z_a + z_o) + 2y₃ z_b z_o + y₃ z_o² + y₄²(z_a + z_o)
  + y₄ z_o² + z_b z_o²` (`gCEn`); in the frame `y₃ + y₄ + z_b = 1` of section 2.2 of the
  document, `E = Y² + b²/U` with `Y = y₃ + y₄`, `b = z_o + y₃ z_b`;
* `symanzikV_Cm`: the same for `C₋`, with `z_o = z₂ + z₃`, `y₃ = z₁`, `y₄ = z₀`,
  `z_a = z₅ + z₇`, `z_b = z₄ + z₆`;
* `sixteen_pi_pow_four_mul_openZero_Cp`: **the class `C₊`** (at `m = e = 1`), normalized to the
  coefficient of `(α/π)²`, is the real integral
  `16π⁴ (1/(64 m⁵)) (1/i) openZero C₊ = (Λ² - m_γ²)² ∫_{Δ₇} cornerG`, with
  `cornerG = 3 W M₁/(U⁶ V⁴) - M₂/(U⁵ V³)` (`W`, `M₁`, `M₂` of
  `QED/TwoLoop/UnitSCGraphCpMain.lean`);
* `openZero_Cm_eq_Cp`: **the mirror identity** `openZero C₋ = openZero C₊` (at `m = e = 1`): the
  `C₋` integrand is the `C₊` integrand composed with the permutation
  `(0 3)(1 2)(4 5)(6 7)` of the coordinates of the simplex (`cmσ`; `cmU`, `cmW`, `cmM₁`, `cmM₂`
  are `cpU`, `cpW`, `cpM₁`, `cpM₂` composed with it), which preserves the simplex integral.
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

/-! ### The group functions -/

/-- `U = (z_o + y₃ + z_a)(z_o + y₄ + z_a + z_b) - (z_o + z_a)²`. -/
def gCU (o y3 y4 a b : ℝ) : ℝ := (o + y3 + a) * (o + y4 + a + b) - (o + a) ^ 2

/-- The numerator `Ẽ = U E` of the massless part of `V`. -/
def gCEn (o y3 y4 a b : ℝ) : ℝ :=
  y3 ^ 2 * y4 + y3 ^ 2 * a + y3 ^ 2 * b + y3 ^ 2 * o + y3 * y4 ^ 2 + 2 * y3 * y4 * a +
    2 * y3 * y4 * o + 2 * y3 * b * o + y3 * o ^ 2 + y4 ^ 2 * a + y4 ^ 2 * o + y4 * o ^ 2 +
    b * o ^ 2

/-- The massless part `E = Ẽ/U` of `V`. -/
noncomputable def gCE (o y3 y4 a b : ℝ) : ℝ := gCEn o y3 y4 a b / gCU o y3 y4 a b

/-- `V = E + m_γ² (z₄ + z₅) + Λ² (z₆ + z₇)`. -/
noncomputable def cornerV (P : Params) (o y3 y4 a b : ℝ) (z : Fin 8 → ℝ) : ℝ :=
  gCE o y3 y4 a b + P.mγ ^ 2 * (z 4 + z 5) + P.Λ ^ 2 * (z 6 + z 7)

theorem cpU_eq_gCU (z : Fin 8 → ℝ) : cpU z = gCU (z 0 + z 1) (z 2) (z 3) (spza z) (spzb z) := by
  unfold cpU gCU; ring

theorem cmU_eq_gCU (z : Fin 8 → ℝ) : cmU z = gCU (z 2 + z 3) (z 1) (z 0) (cmza z) (cmzb z) := by
  unfold cmU gCU; ring

/-! ### The second Symanzik function at `q = 0` -/

theorem symanzikVector_Cp (P : Params) (hm : P.m = 1) (z : Fin 8 → ℝ) (s : Fin 2) :
    symanzikVector (classAlpha .Cp) (pvMomentaE .Cp (restMomentum P.m) (restMomentum P.m)) z s =
      ![![z 0 + z 1 + z 2, 0, 0, 0], ![z 0 + z 1 - z 3, 0, 0, 0]] s := by
  funext μ
  fin_cases s <;> fin_cases μ <;>
    simp [symanzikVector, Fin.sum_univ_succ, pvMomentaE, extMomenta,
      QED.Integration.TwoLoop.classCpSpMomenta, QED.Integration.TwoLoop.pvLines, castLoopMatrix,
      class5LoopMatrixPV, QED.Integration.TwoLoop.class5LoopMatrix, restMomentum, hm]
  all_goals ring

theorem symanzikVector_Cm (P : Params) (hm : P.m = 1) (z : Fin 8 → ℝ) (s : Fin 2) :
    symanzikVector (classAlpha .Cm) (pvMomentaE .Cm (restMomentum P.m) (restMomentum P.m)) z s =
      ![![z 0 + z 1, 0, 0, 0], ![z 2 + z 3 - z 0, 0, 0, 0]] s := by
  funext μ
  fin_cases s <;> fin_cases μ <;>
    simp [symanzikVector, Fin.sum_univ_succ, pvMomentaE, extMomenta,
      QED.Integration.TwoLoop.classCmSmMomenta, QED.Integration.TwoLoop.pvLines, castLoopMatrix,
      class5LoopMatrixPV, QED.Integration.TwoLoop.class5LoopMatrix, restMomentum, hm]
  ring

/-- **The second Symanzik function of `C₊` at `q = 0`**, at `m = 1`, for `U ≠ 0`. -/
theorem symanzikV_Cp (P : Params) (hm : P.m = 1) {z : Fin 8 → ℝ} (hU : cpU z ≠ 0) :
    symanzikV (classAlpha .Cp) (pvMomentaE .Cp (restMomentum P.m) (restMomentum P.m))
      (pvMasses P) z = cornerV P (z 0 + z 1) (z 2) (z 3) (spza z) (spzb z) z := by
  unfold symanzikV
  simp only [symanzikVector_Cp P hm, inv_symanzikMatrix_Cp, Fin.sum_univ_two]
  simp [Fin.sum_univ_succ, pvMomentaE, extMomenta, QED.Integration.TwoLoop.classCpSpMomenta,
    QED.Integration.TwoLoop.pvLines, pvMasses, QED.Integration.TwoLoop.classPVMasses,
    restMomentum, hm, QED.Minkowski.dot_eq, cornerV, gCE]
  rw [cpU_eq_gCU] at hU ⊢
  simp only [gCU, gCEn, spza, spzb] at hU ⊢
  field_simp
  ring

/-- **The second Symanzik function of `C₋` at `q = 0`**, at `m = 1`, for `U ≠ 0`. -/
theorem symanzikV_Cm (P : Params) (hm : P.m = 1) {z : Fin 8 → ℝ} (hU : cmU z ≠ 0) :
    symanzikV (classAlpha .Cm) (pvMomentaE .Cm (restMomentum P.m) (restMomentum P.m))
      (pvMasses P) z = cornerV P (z 2 + z 3) (z 1) (z 0) (cmza z) (cmzb z) z := by
  unfold symanzikV
  simp only [symanzikVector_Cm P hm, inv_symanzikMatrix_Cm, Fin.sum_univ_two]
  simp [Fin.sum_univ_succ, pvMomentaE, extMomenta, QED.Integration.TwoLoop.classCmSmMomenta,
    QED.Integration.TwoLoop.pvLines, pvMasses, QED.Integration.TwoLoop.classPVMasses,
    restMomentum, hm, QED.Minkowski.dot_eq]
  rw [cmU_eq_gCU] at hU ⊢
  unfold cornerV gCE
  simp only [gCU, gCEn, cmza, cmzb] at hU ⊢
  field_simp
  ring

/-! ### The real integrand -/

/-- The integrand from `W`, `M₁`, `M₂`, `U`, `V`: `3 W M₁/(U⁶ V⁴) - M₂/(U⁵ V³)`. -/
noncomputable def cornerGz (W M1 M2 U V : ℝ) : ℝ := 3 * W * M1 / (U ^ 6 * V ^ 4) - M2 / (U ^ 5 * V ^ 3)

/-- **The real integrand of `C₊` on `Δ₇`.** -/
noncomputable def cornerG (P : Params) (z : Fin 8 → ℝ) : ℝ :=
  cornerGz (cpW z) (cpM1 z) (cpM2 z) (cpU z) (cornerV P (z 0 + z 1) (z 2) (z 3) (spza z) (spzb z) z)

/-- The real integrand of `C₋` on `Δ₇`. -/
noncomputable def cornerGm (P : Params) (z : Fin 8 → ℝ) : ℝ :=
  cornerGz (cmW z) (cmM1 z) (cmM2 z) (cmU z) (cornerV P (z 2 + z 3) (z 1) (z 0) (cmza z) (cmzb z) z)

theorem corner_integrand_eq_aux (c K : ℂ) (W M1 M2 U V : ℝ) (hU : U ≠ 0) :
    (c ^ 2 * (6 / K) * ((W * M1 / (2 * U ^ 6) : ℝ) : ℂ) +
        c ^ 2 * (2 / K) * ((-M2 / (2 * U ^ 5) : ℝ) : ℂ) * (V : ℂ)) / (V : ℂ) ^ 4 =
      c ^ 2 / K * ((cornerGz W M1 M2 U V : ℝ) : ℂ) := by
  unfold cornerGz
  rcases eq_or_ne V 0 with hV | hV
  · simp [hV]
  have hV' : (V : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV
  have hU' : (U : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU
  push_cast
  field_simp
  ring

theorem corner_integrand_eq_Cp {P : Params} (hm : P.m = 1) (x : Fin 7 → ℝ)
    (hU : cpU (simplexPoint x) ≠ 0) :
    (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
          ((cpW (simplexPoint x) * cpM1 (simplexPoint x) / (2 * cpU (simplexPoint x) ^ 6) : ℝ) :
            ℂ) +
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
          ((-cpM2 (simplexPoint x) / (2 * cpU (simplexPoint x) ^ 5) : ℝ) : ℂ) *
            ((openV .Cp P x : ℝ) : ℂ)) /
        ((openV .Cp P x : ℝ) : ℂ) ^ 4 =
      ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 / kConst * ((cornerG P (simplexPoint x) : ℝ) : ℂ) := by
  have hV : openV .Cp P x = cornerV P (simplexPoint x 0 + simplexPoint x 1) (simplexPoint x 2)
      (simplexPoint x 3) (spza (simplexPoint x)) (spzb (simplexPoint x)) (simplexPoint x) :=
    symanzikV_Cp P hm hU
  rw [hV, corner_integrand_eq_aux _ _ _ _ _ _ _ hU]
  rfl

theorem corner_integrand_eq_Cm {P : Params} (hm : P.m = 1) (x : Fin 7 → ℝ)
    (hU : cmU (simplexPoint x) ≠ 0) :
    (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
          ((cmW (simplexPoint x) * cmM1 (simplexPoint x) / (2 * cmU (simplexPoint x) ^ 6) : ℝ) :
            ℂ) +
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
          ((-cmM2 (simplexPoint x) / (2 * cmU (simplexPoint x) ^ 5) : ℝ) : ℂ) *
            ((openV .Cm P x : ℝ) : ℂ)) /
        ((openV .Cm P x : ℝ) : ℂ) ^ 4 =
      ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 / kConst * ((cornerGm P (simplexPoint x) : ℝ) : ℂ) := by
  have hV : openV .Cm P x = cornerV P (simplexPoint x 2 + simplexPoint x 3) (simplexPoint x 1)
      (simplexPoint x 0) (cmza (simplexPoint x)) (cmzb (simplexPoint x)) (simplexPoint x) :=
    symanzikV_Cm P hm hU
  rw [hV, corner_integrand_eq_aux _ _ _ _ _ _ _ hU]
  rfl

/-! ### The classes as real integrals -/

theorem openZero_Cp_eq_real {P : Params} (hm : P.m = 1) (he : P.e = 1) :
    openZero .Cp P = ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 / kConst *
      ((∫ x in simplexSet 7, cornerG P (simplexPoint x) : ℝ) : ℂ) := by
  rw [openZero_Cp_eq hm he, ← integral_complex_ofReal, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_cpU_ne_zero] with x hx
  exact corner_integrand_eq_Cp hm x hx

theorem openZero_Cm_eq_real {P : Params} (hm : P.m = 1) (he : P.e = 1) :
    openZero .Cm P = ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 / kConst *
      ((∫ x in simplexSet 7, cornerGm P (simplexPoint x) : ℝ) : ℂ) := by
  rw [openZero_Cm_eq hm he, ← integral_complex_ofReal, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_cmU_ne_zero] with x hx
  exact corner_integrand_eq_Cm hm x hx

/-- The permutation `(0 3)(1 2)(4 5)(6 7)` of the coordinates, which exchanges the line labels
of `C₊` and `C₋`. -/
def cmσ : Equiv.Perm (Fin 8) where
  toFun := ![3, 2, 1, 0, 5, 4, 7, 6]
  invFun := ![3, 2, 1, 0, 5, 4, 7, 6]
  left_inv := by decide
  right_inv := by decide

theorem comp_cmσ (z : Fin 8 → ℝ) :
    (z ∘ cmσ) 0 = z 3 ∧ (z ∘ cmσ) 1 = z 2 ∧ (z ∘ cmσ) 2 = z 1 ∧ (z ∘ cmσ) 3 = z 0 ∧
    (z ∘ cmσ) 4 = z 5 ∧ (z ∘ cmσ) 5 = z 4 ∧ (z ∘ cmσ) 6 = z 7 ∧ (z ∘ cmσ) 7 = z 6 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem cmM2_eq (z : Fin 8 → ℝ) : cmM2 z = cpM2 (z ∘ cmσ) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := comp_cmσ z
  simp only [cmM2, cpM2, cmza, cmzb, spza, spzb, cmM2pa, cmM2pb, cmM2pc, cmM2pd, cpM2pa, cpM2pb,
    cpM2pc, cpM2pd, h0, h1, h2, h3, h4, h5, h6, h7]
  ring

theorem cmM1_eq (z : Fin 8 → ℝ) : cmM1 z = cpM1 (z ∘ cmσ) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := comp_cmσ z
  simp only [cmM1, cpM1, cmza, cmzb, spza, spzb, cmM1pa, cmM1pb, cmM1pc, cmM1pd, cpM1pa, cpM1pb,
    cpM1pc, cpM1pd, h0, h1, h2, h3, h4, h5, h6, h7]
  ring

theorem cornerGm_eq (P : Params) (z : Fin 8 → ℝ) : cornerGm P z = cornerG P (z ∘ cmσ) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := comp_cmσ z
  have eW : cmW z = cpW (z ∘ cmσ) := by
    simp only [cmW, cpW, cmzb, spzb, h0, h1, h2, h3, h5, h7]; ring
  have eU : cmU z = cpU (z ∘ cmσ) := by
    simp only [cmU, cpU, cmza, cmzb, spza, spzb, h0, h1, h2, h3, h4, h5, h6, h7]; ring
  have eV : cornerV P (z 2 + z 3) (z 1) (z 0) (cmza z) (cmzb z) z =
      cornerV P ((z ∘ cmσ) 0 + (z ∘ cmσ) 1) ((z ∘ cmσ) 2) ((z ∘ cmσ) 3) (spza (z ∘ cmσ))
        (spzb (z ∘ cmσ)) (z ∘ cmσ) := by
    simp only [cornerV, cmza, cmzb, spza, spzb, h0, h1, h2, h3, h4, h5, h6, h7]
    ring_nf
  unfold cornerGm cornerG
  rw [eW, eU, eV, cmM1_eq, cmM2_eq]

/-- **The mirror identity** `∫ cornerG(C₋) = ∫ cornerG(C₊)`. -/
theorem integral_cornerGm (P : Params) :
    ∫ x in simplexSet 7, cornerGm P (simplexPoint x) =
      ∫ x in simplexSet 7, cornerG P (simplexPoint x) := by
  simp only [cornerGm_eq]
  exact QED.Integration.SimplexMerge.integral_simplex_comp_perm cmσ (cornerG P)

/-- **The mirror identity `openZero C₋ = openZero C₊`** at `m = e = 1`. -/
theorem openZero_Cm_eq_Cp {P : Params} (hm : P.m = 1) (he : P.e = 1) :
    openZero .Cm P = openZero .Cp P := by
  rw [openZero_Cm_eq_real hm he, openZero_Cp_eq_real hm he, integral_cornerGm]

/-- **The class `C₊` as a real simplex integral** (`m = e = 1`), normalized to the coefficient of
`(α/π)²`: `16π⁴ (1/(64 m⁵)) (1/i) openZero C₊ = (Λ² - m_γ²)² ∫_{Δ₇} cornerG`. -/
theorem sixteen_pi_pow_four_mul_openZero_Cp {P : Params} (hm : P.m = 1) (he : P.e = 1) :
    16 * (π : ℂ) ^ 4 * (1 / (64 * (P.m : ℂ) ^ 5) * ((1 / I) * openZero .Cp P)) =
      (((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * ∫ x in simplexSet 7, cornerG P (simplexPoint x) : ℝ) : ℂ) := by
  rw [openZero_Cp_eq_real hm he, hm]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [kConst]
  push_cast
  field_simp

end QED.TwoLoop.UnitSCReduce

end
