/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLGraphTraceJet
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The pointwise second-order coefficients of the ladder numerator

Section 8 of `docs/TWO-LOOP-UNITS.md`, stage 1 of the L link, graph half, item (i). With the
projected ladder numerator `N = T₁ + T₂ V + T₃ V²` (`QED.TwoLoop.UnitLGraphTrace.openNum_L_eq_T`)
and, at a point `z` of the eight line parameters, `z_A = z₀ + z₃`, `z_B = z₁ + z₂` (the outer and
inner electron pairs), `z_a = z₄ + z₆`, `z_b = z₅ + z₇` (the outer and inner photon, each a
Pauli–Villars pair), `s = z_B + z_b`, `c = z_B z_b`, `a = s z_A + c`, `U = a + s z_a` and
`Q = (3z_B - 2s) a² + (4 z_B s - z_B² - 2s²) a z_a - 2 s c z_a²`, at `m = 1`, `e = 1`:

* `secondCoeff_ladderT1`: `c₂[T₁] = (Λ² - m_γ²)² (6/K) z_a Q/(2U⁵)`;
* `secondCoeff_ladderT2`: `c₂[T₂] = (Λ² - m_γ²)² (2/K) z_a (9c + a)/(2U⁴)`;
* `secondCoeff_ladderT3`: `c₂[T₃] = 0`,

with `K = 16π⁴/(64 i)` (`kConst`), for every `z` with `U ≠ 0` and every splitting of the pairs.
More precisely `T₁, T₂, T₃` vanish to first order at `u = 0` (`hasJet2_ladderT1`, …), so the
second-order coefficient of the projected numerator is `c₂[N(x, ·)] = c₂[T₁] + c₂[T₂] V(x)` with
`V(x)` the second Symanzik function at `q = 0` (`secondCoeff_openNum_L`), and
`openZero .L P = ∫_{Δ₇} (c₂[T₁] + c₂[T₂] V)/V⁴` (`openZero_L_eq`). In the frame
`s = z_B + z_b = 1` (`Y = z_B`) these are the formulas of the module docstring of
`QED/TwoLoop/UnitLGraph.lean` (`secondCoeff_ladderT1_frame`, `secondCoeff_ladderT2_frame`); the
general case is the homogeneous form of degree `-4` and `-5`.

The proof: `T₁, T₂, T₃` are planar expressions (`QED/TwoLoop/UnitLGraphTraceData.lean`) whose
second-order jets are computed by the planar jet rules (`QED/TwoLoop/UnitLGraphTraceJet.lean`);
the slot momenta enter only through `X = σ₀ + τ₀` and `W = σ₁ + τ₁`, and the remaining identity is
one of rational functions of `z_A, z_B, z_a, z_b`.
-/

@[expose] public section

open Complex Matrix
open scoped Real

namespace QED.TwoLoop.UnitLGraphTrace

open Filter Topology
open QED.WickModel QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.TwoLoop.ParamNumEval QED.TwoLoop.UnitLGraph QED.TwoLoop.Bridge
open QED.Integration.Feynman (simplexPoint)
open QED.Integration.TwoLoop (castLoopMatrix class5LoopMatrixPV symanzikU symanzikV symanzikVector
  symanzikMatrix)

/-! ### The parameters -/

section Params

variable (z : Fin 8 → ℝ)

/-- The outer electron pair `z_A = z₀ + z₃`. -/
def lzA : ℝ := z 0 + z 3
/-- The inner electron pair `z_B = z₁ + z₂`. -/
def lzB : ℝ := z 1 + z 2
/-- The outer photon pair `z_a = z₄ + z₆`. -/
def lza : ℝ := z 4 + z 6
/-- The inner photon pair `z_b = z₅ + z₇`. -/
def lzb : ℝ := z 5 + z 7
/-- `s = z_B + z_b`. -/
def lS : ℝ := lzB z + lzb z
/-- `c = z_B z_b`. -/
def lc : ℝ := lzB z * lzb z
/-- `a = s z_A + c`. -/
def la : ℝ := lS z * lzA z + lc z
/-- `U = a + s z_a`. -/
def lU : ℝ := la z + lS z * lza z
/-- `Q = (3z_B - 2s) a² + (4 z_B s - z_B² - 2s²) a z_a - 2 s c z_a²`. -/
def lQ : ℝ := (3 * lzB z - 2 * lS z) * la z ^ 2 +
  (4 * lzB z * lS z - lzB z ^ 2 - 2 * lS z ^ 2) * la z * lza z - 2 * lS z * lc z * lza z ^ 2

theorem symanzikMatrix_ladder :
    symanzikMatrix ladderAlpha z = !![lzB z + lzb z, -lzb z; -lzb z, lzA z + lza z + lzb z] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symanzikMatrix, Fin.sum_univ_succ, castLoopMatrix, class5LoopMatrixPV,
      QED.Integration.TwoLoop.class5LoopMatrix, lzA, lzB, lza, lzb] <;> ring

theorem symanzikU_ladder : symanzikU ladderAlpha z = lU z := by
  rw [symanzikU, symanzikMatrix_ladder, Matrix.det_fin_two_of]
  simp only [lU, la, lc, lS]
  ring

theorem inv_symanzikMatrix_ladder (s t : Fin 2) :
    (symanzikMatrix ladderAlpha z)⁻¹ s t =
      (lU z)⁻¹ * !![lzA z + lza z + lzb z, lzb z; lzb z, lzB z + lzb z] s t := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', ← symanzikU, symanzikU_ladder, symanzikMatrix_ladder,
    Matrix.adjugate_fin_two_of, Matrix.smul_apply, smul_eq_mul]
  fin_cases s <;> fin_cases t <;> simp

/-- `X = σ₀ + τ₀`. -/
noncomputable def lX : ℝ := sigP z 0 + sigQ z 0
/-- `W = σ₁ + τ₁`. -/
noncomputable def lW : ℝ := sigP z 1 + sigQ z 1

theorem lX_eq : lX z = (lU z)⁻¹ * ((lzA z + lza z + lzb z) * lzB z + lzb z * lzA z) := by
  simp only [lX, sigP, sigQ, inv_symanzikMatrix_ladder]
  simp [lzA, lzB]
  ring

theorem lW_eq : lW z = (lU z)⁻¹ * (lzb z * lzB z + (lzB z + lzb z) * lzA z) := by
  simp only [lW, sigP, sigQ, inv_symanzikMatrix_ladder]
  simp [lzA, lzB]
  ring

end Params

/-! ### The rational identities -/

theorem lU_ne_zero_aux {z : Fin 8 → ℝ} (hU : lU z ≠ 0) :
    (lzB z + lzb z) * (lzA z + lza z + lzb z) - lzb z ^ 2 ≠ 0 := by
  convert hU using 1
  simp only [lU, la, lc, lS]
  ring

/-- The rational identity of `c₂[T₁]`. -/
theorem psi1_identity {z : Fin 8 → ℝ} (hU : lU z ≠ 0) :
    3 * lW z ^ 2 * lX z - 4 * lW z ^ 2 - 3 * lW z * lX z ^ 2 + 4 * lW z * lX z + 2 * lX z ^ 2 -
      2 * lX z = lza z * lQ z / lU z ^ 3 := by
  rw [lX_eq, lW_eq]
  have hU' : lU z = (lzB z + lzb z) * (lzA z + lza z + lzb z) - lzb z ^ 2 := by
    simp only [lU, la, lc, lS]; ring
  simp only [lQ, la, lc, lS]
  rw [hU']
  have h := lU_ne_zero_aux hU
  field_simp
  ring

/-- The rational identity of `c₂[T₂]`, with `c₀₀, c₀₁, c₁₁` the entries of `A⁻¹`. -/
theorem psi2_identity {z : Fin 8 → ℝ} (hU : lU z ≠ 0) (c₀₀ c₀₁ c₁₁ : ℝ)
    (h₀₀ : c₀₀ = (lU z)⁻¹ * (lzA z + lza z + lzb z)) (h₀₁ : c₀₁ = (lU z)⁻¹ * lzb z)
    (h₁₁ : c₁₁ = (lU z)⁻¹ * (lzB z + lzb z)) :
    -1024 * lW z ^ 2 * c₀₀ + 2048 * lW z * lX z * c₀₁ + 1024 * lW z * c₀₀ - 4096 * lW z * c₀₁ -
      1024 * lX z ^ 2 * c₁₁ + 8192 * lX z * c₀₁ - 5120 * lX z * c₁₁ - 6144 * c₀₁ + 6144 * c₁₁ =
      1024 * (lza z * (9 * lc z + la z) / lU z ^ 2) := by
  subst h₀₀ h₀₁ h₁₁
  rw [lX_eq, lW_eq]
  have hU' : lU z = (lzB z + lzb z) * (lzA z + lza z + lzb z) - lzb z ^ 2 := by
    simp only [lU, la, lc, lS]; ring
  simp only [la, lc, lS]
  rw [hU']
  have h := lU_ne_zero_aux hU
  field_simp
  ring

/-! ### The constants -/

/-- `-π⁴ κ η² = i (Λ² - m_γ²)² / (256 π⁴)` at `e = 1`. -/
theorem ladderK_eq {P : Params} (he : P.e = 1) :
    ladderK P = I * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 / (256 * (π : ℂ) ^ 4) := by
  have h5 : (I * ((1 : ℝ) : ℂ)) ^ 5 = I := by
    rw [Complex.ofReal_one, mul_one, pow_succ, I_pow_four, one_mul]
  have h4 : (1 / I) ^ 4 = 1 := by
    rw [one_div, inv_I, neg_pow, I_pow_four]; norm_num
  have h2 : ∀ D : ℂ, (1 / I * D) ^ 2 = -D ^ 2 := fun D => by
    rw [mul_pow, one_div, inv_I, neg_sq, I_sq]; ring
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [ladderK, ladderConst, pvConst, QED.TwoLoop.ClassLimit.twoLoopNorm, he, h5, h4, h2]
  push_cast
  field_simp
  ring

/-- `K = 16π⁴/(64 i)`. -/
noncomputable def kConst : ℂ := 16 * (π : ℂ) ^ 4 / (64 * I)

theorem ladderC_eq (z : Fin 8 → ℝ) (k l : Fin 4) :
    ladderC (symanzikMatrix ladderAlpha z) k l =
      ((∑ s, ∑ r, ladderAlpha (ladderLines k) s * (symanzikMatrix ladderAlpha z)⁻¹ s r *
        ladderAlpha (ladderLines l) r : ℝ) : ℂ) := rfl

/-! ### The second-order coefficients -/

/-- The jet of the slot numerator `k`. -/
noncomputable def slotJ (z : Fin 8 → ℝ) (k : Fin 4) : PJ :=
  eJ ((slotA z k : ℂ) + (slotB z k : ℂ)) (slotB z k : ℂ)

/-- The jet of `4 + 8 q̸ₖ`. -/
noncomputable def slotW (z : Fin 8 → ℝ) (k : Fin 4) : PJ :=
  wJ ((slotA z k : ℂ) + (slotB z k : ℂ)) (slotB z k : ℂ)

theorem lwJ_slot_T1 (z : Fin 8 → ℝ) :
    lwJ qJ0 qJ1 rJ (slotJ z 0) (slotJ z 1) (slotJ z 2) (slotJ z 3) =
      512 * ((3 * lW z ^ 2 * lX z - 4 * lW z ^ 2 - 3 * lW z * lX z ^ 2 + 4 * lW z * lX z +
        2 * lX z ^ 2 - 2 * lX z : ℝ) : ℂ) := by
  simp only [slotJ, lwJ_T1, slotA, slotB, lX, lW, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  ring

/-- **The jet of `T₁`**: `T₁(u) = c₂[T₁] u² + o(u²)`, `c₂[T₁] = (Λ² - m_γ²)² (6/K) z_a Q/(2U⁵)`. -/
theorem hasJet2_ladderT1 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : lU z ≠ 0) :
    HasJet2 (ladderT1 P z) 0 0 (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
      ((lza z * lQ z / (2 * lU z ^ 5) : ℝ) : ℂ)) := by
  have h := hasJet2_lwPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) (y₀ := slotJ z 0)
    (y₁ := slotJ z 1) (y₂ := slotJ z 2) (y₃ := slotJ z 3) (jet_lQ0 hm) (jet_lQ1 hm) (jet_lR hm)
    (jet_lE hm z 0) (jet_lE hm z 1) (jet_lE hm z 2) (jet_lE hm z 3)
  have h' := (h.const_mul 6).const_mul (ladderK P * ((symanzikU ladderAlpha z ^ 2 : ℝ) : ℂ)⁻¹)
  refine (h'.congr fun u => ladderT1_planar P z u).of_eq (fun _ => rfl) ?_ ?_ ?_
  · simp [slotJ]
  · simp [slotJ]
  rw [lwJ_slot_T1, psi1_identity hU, ladderK_eq he, symanzikU_ladder, kConst]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hU' : (lU z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU
  push_cast
  field_simp
  ring

/-- **The second-order coefficient of `T₁`**: `c₂[T₁] = (Λ² - m_γ²)² (6/K) z_a Q/(2U⁵)`. -/
theorem secondCoeff_ladderT1 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : lU z ≠ 0) :
    secondCoeff (ladderT1 P z) = ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
      ((lza z * lQ z / (2 * lU z ^ 5) : ℝ) : ℂ) :=
  (hasJet2_ladderT1 hm he hU).secondCoeff_eq

theorem ladderC_val (z : Fin 8 → ℝ) :
    ladderC (symanzikMatrix ladderAlpha z) 0 1 = (((lU z)⁻¹ * lzb z : ℝ) : ℂ) ∧
    ladderC (symanzikMatrix ladderAlpha z) 0 2 = (((lU z)⁻¹ * lzb z : ℝ) : ℂ) ∧
    ladderC (symanzikMatrix ladderAlpha z) 0 3 = (((lU z)⁻¹ * (lzB z + lzb z) : ℝ) : ℂ) ∧
    ladderC (symanzikMatrix ladderAlpha z) 1 2 =
      (((lU z)⁻¹ * (lzA z + lza z + lzb z) : ℝ) : ℂ) ∧
    ladderC (symanzikMatrix ladderAlpha z) 1 3 = (((lU z)⁻¹ * lzb z : ℝ) : ℂ) ∧
    ladderC (symanzikMatrix ladderAlpha z) 2 3 = (((lU z)⁻¹ * lzb z : ℝ) : ℂ) := by
  simp only [ladderC, contrC, Fin.sum_univ_two, inv_symanzikMatrix_ladder]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [castLoopMatrix, class5LoopMatrixPV, QED.Integration.TwoLoop.class5LoopMatrix, ladderLines]

theorem t2_combination (z : Fin 8 → ℝ) :
    ladderC (symanzikMatrix ladderAlpha z) 0 1 *
        lwJ qJ0 qJ1 rJ (PJ.c ⟨2, 0, 0, 0⟩) (PJ.c 1) (slotJ z 2) (slotJ z 3) +
      ladderC (symanzikMatrix ladderAlpha z) 0 2 * omLJ qJ0 qJ1 rJ ((slotW z 1).mul (slotJ z 3)) +
      ladderC (symanzikMatrix ladderAlpha z) 0 3 * f3J qJ0 qJ1 rJ (slotJ z 1) (slotJ z 2) +
      ladderC (symanzikMatrix ladderAlpha z) 1 2 *
        lwJ qJ0 qJ1 rJ (slotJ z 0) (PJ.c ⟨2, 0, 0, 0⟩) (PJ.c 1) (slotJ z 3) +
      ladderC (symanzikMatrix ladderAlpha z) 1 3 * omRJ qJ0 qJ1 rJ ((slotJ z 0).mul (slotW z 2)) +
      ladderC (symanzikMatrix ladderAlpha z) 2 3 *
        lwJ qJ0 qJ1 rJ (slotJ z 0) (slotJ z 1) (PJ.c ⟨2, 0, 0, 0⟩) (PJ.c 1) =
    ((-1024 * lW z ^ 2 * ((lU z)⁻¹ * (lzA z + lza z + lzb z)) +
      2048 * lW z * lX z * ((lU z)⁻¹ * lzb z) +
      1024 * lW z * ((lU z)⁻¹ * (lzA z + lza z + lzb z)) - 4096 * lW z * ((lU z)⁻¹ * lzb z) -
      1024 * lX z ^ 2 * ((lU z)⁻¹ * (lzB z + lzb z)) + 8192 * lX z * ((lU z)⁻¹ * lzb z) -
      5120 * lX z * ((lU z)⁻¹ * (lzB z + lzb z)) - 6144 * ((lU z)⁻¹ * lzb z) +
      6144 * ((lU z)⁻¹ * (lzB z + lzb z)) : ℝ) : ℂ) := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := ladderC_val z
  rw [h01, h02, h03, h12, h13, h23]
  simp only [slotJ, slotW, lwJ_01, omLJ_02, f3J_03, lwJ_12, omRJ_13, lwJ_23, slotA, slotB, lX, lW,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  push_cast
  ring

/-- **The jet of `T₂`**: `T₂(u) = c₂[T₂] u² + o(u²)`, `c₂[T₂] = (Λ² - m_γ²)² (2/K) z_a (9c +
a)/(2U⁴)`. -/
theorem hasJet2_ladderT2 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : lU z ≠ 0) :
    HasJet2 (ladderT2 P z) 0 0 (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
      ((lza z * (9 * lc z + la z) / (2 * lU z ^ 4) : ℝ) : ℂ)) := by
  have h₁ := hasJet2_lwPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) (y₀ := PJ.c ⟨2, 0, 0, 0⟩)
    (y₁ := PJ.c 1) (y₂ := slotJ z 2) (y₃ := slotJ z 3) (jet_lQ0 hm) (jet_lQ1 hm) (jet_lR hm)
    (HasPJ.const _) (HasPJ.const _) (jet_lE hm z 2) (jet_lE hm z 3)
  have h₂ := hasJet2_omLPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ)
    (z := (slotW z 1).mul (slotJ z 3)) (jet_lQ0 hm) (jet_lQ1 hm) (jet_lR hm)
    (HasPJ.mul (x := slotW z 1) (y := slotJ z 3) (jet_wPl hm z 1) (jet_lE hm z 3))
  have h₃ := hasJet2_f3Pl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) (y₁ := slotJ z 1)
    (y₂ := slotJ z 2) (jet_lQ0 hm) (jet_lQ1 hm) (jet_lR hm) (jet_lE hm z 1) (jet_lE hm z 2)
  have h₄ := hasJet2_lwPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) (y₀ := slotJ z 0)
    (y₁ := PJ.c ⟨2, 0, 0, 0⟩) (y₂ := PJ.c 1) (y₃ := slotJ z 3) (jet_lQ0 hm) (jet_lQ1 hm)
    (jet_lR hm) (jet_lE hm z 0) (HasPJ.const _) (HasPJ.const _) (jet_lE hm z 3)
  have h₅ := hasJet2_omRPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ)
    (z := (slotJ z 0).mul (slotW z 2)) (jet_lQ0 hm) (jet_lQ1 hm) (jet_lR hm)
    (HasPJ.mul (x := slotJ z 0) (y := slotW z 2) (jet_lE hm z 0) (jet_wPl hm z 2))
  have h₆ := hasJet2_lwPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) (y₀ := slotJ z 0)
    (y₁ := slotJ z 1) (y₂ := PJ.c ⟨2, 0, 0, 0⟩) (y₃ := PJ.c 1) (jet_lQ0 hm) (jet_lQ1 hm)
    (jet_lR hm) (jet_lE hm z 0) (jet_lE hm z 1) (HasPJ.const _) (HasPJ.const _)
  have h := ((((((h₁.const_mul (ladderC (symanzikMatrix ladderAlpha z) 0 1)).add
    (h₂.const_mul (ladderC (symanzikMatrix ladderAlpha z) 0 2))).add
    (h₃.const_mul (ladderC (symanzikMatrix ladderAlpha z) 0 3))).add
    (h₄.const_mul (ladderC (symanzikMatrix ladderAlpha z) 1 2))).add
    (h₅.const_mul (ladderC (symanzikMatrix ladderAlpha z) 1 3))).add
    (h₆.const_mul (ladderC (symanzikMatrix ladderAlpha z) 2 3))).const_mul
    (ladderK P * ((symanzikU ladderAlpha z ^ 2 : ℝ) : ℂ)⁻¹)
  refine (h.congr fun u => ladderT2_planar P z u).of_eq (fun _ => rfl) ?_ ?_ ?_
  · simp [slotJ, slotW]
  · simp [slotJ, slotW]
  rw [t2_combination, psi2_identity hU _ _ _ rfl rfl rfl, ladderK_eq he, symanzikU_ladder, kConst]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hU' : (lU z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU
  push_cast
  field_simp
  ring

/-- **The second-order coefficient of `T₂`**: `c₂[T₂] = (Λ² - m_γ²)² (2/K) z_a (9c + a)/(2U⁴)`. -/
theorem secondCoeff_ladderT2 {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hU : lU z ≠ 0) :
    secondCoeff (ladderT2 P z) = ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
      ((lza z * (9 * lc z + la z) / (2 * lU z ^ 4) : ℝ) : ℂ) :=
  (hasJet2_ladderT2 hm he hU).secondCoeff_eq

/-- **The jet of `T₃` vanishes**: `T₃(u) = o(u²)`. -/
theorem hasJet2_ladderT3 {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) :
    HasJet2 (ladderT3 P z) 0 0 0 := by
  have h₁ := hasJet2_lwPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) (y₀ := PJ.c ⟨2, 0, 0, 0⟩)
    (y₁ := PJ.c 1) (y₂ := PJ.c ⟨2, 0, 0, 0⟩) (y₃ := PJ.c 1) (jet_lQ0 hm) (jet_lQ1 hm) (jet_lR hm)
    (HasPJ.const _) (HasPJ.const _) (HasPJ.const _) (HasPJ.const _)
  have h₂ := hasJet2_omLPl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) (z := PJ.c 1)
    (jet_lQ0 hm) (jet_lQ1 hm) (jet_lR hm) (HasPJ.const _)
  have h₃ := hasJet2_f3Pl (q₀ := qJ0) (q₁ := qJ1) (r := rJ) (y₁ := PJ.c ⟨2, 0, 0, 0⟩)
    (y₂ := PJ.c 1) (jet_lQ0 hm) (jet_lQ1 hm) (jet_lR hm) (HasPJ.const _) (HasPJ.const _)
  have h := ((((h₁.const_mul (ladderC (symanzikMatrix ladderAlpha z) 0 1 *
      ladderC (symanzikMatrix ladderAlpha z) 2 3)).add
    ((h₂.const_mul 32).const_mul (ladderC (symanzikMatrix ladderAlpha z) 0 2 *
      ladderC (symanzikMatrix ladderAlpha z) 1 3))).add
    (h₃.const_mul (ladderC (symanzikMatrix ladderAlpha z) 0 3 *
      ladderC (symanzikMatrix ladderAlpha z) 1 2))).const_mul (1 / 4)).const_mul
    (ladderK P * ((symanzikU ladderAlpha z ^ 2 : ℝ) : ℂ)⁻¹)
  refine (h.congr fun u => ladderT3_planar P z u).of_eq (fun _ => rfl) ?_ ?_ ?_ <;>
    simp [lwJ_T3, omLJ_T3, f3J_T3]

/-- **The second-order coefficient of `T₃` vanishes.** -/
theorem secondCoeff_ladderT3 {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) :
    secondCoeff (ladderT3 P z) = 0 :=
  (hasJet2_ladderT3 hm z).secondCoeff_eq

/-! ### The frame `z_B + z_b = 1` -/

/-- **`c₂[T₁]` in the frame `z_B + z_b = 1`**: with `Y = z_B`, `c = Y(1-Y)`, `a = z_A + c`,
`U = a + z_a`, `Q₀ = (3Y-2)a² + (4Y-Y²-2) a z_a - 2c z_a²`,
`c₂[T₁] = (Λ² - m_γ²)² (6/K) z_a Q₀/(2U⁵)`. -/
theorem secondCoeff_ladderT1_frame {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hs : lzB z + lzb z = 1) (hU : lzA z + lzB z * (1 - lzB z) + lza z ≠ 0) :
    secondCoeff (ladderT1 P z) = ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
      ((lza z * ((3 * lzB z - 2) * (lzA z + lzB z * (1 - lzB z)) ^ 2 +
          (4 * lzB z - lzB z ^ 2 - 2) * (lzA z + lzB z * (1 - lzB z)) * lza z -
          2 * (lzB z * (1 - lzB z)) * lza z ^ 2) /
        (2 * (lzA z + lzB z * (1 - lzB z) + lza z) ^ 5) : ℝ) : ℂ) := by
  have hb : lzb z = 1 - lzB z := by linarith
  have hU' : lU z = lzA z + lzB z * (1 - lzB z) + lza z := by
    simp only [lU, la, lc, lS, hb]; ring
  rw [secondCoeff_ladderT1 hm he (hU' ▸ hU), hU']
  congr 3
  simp only [lQ, la, lc, lS, hb]
  ring

/-- **`c₂[T₂]` in the frame `z_B + z_b = 1`**: `c₂[T₂] = (Λ² - m_γ²)² (2/K) z_a (9c + a)/(2U⁴)`. -/
theorem secondCoeff_ladderT2_frame {P : Params} (hm : P.m = 1) (he : P.e = 1) {z : Fin 8 → ℝ}
    (hs : lzB z + lzb z = 1) (hU : lzA z + lzB z * (1 - lzB z) + lza z ≠ 0) :
    secondCoeff (ladderT2 P z) = ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
      ((lza z * (9 * (lzB z * (1 - lzB z)) + (lzA z + lzB z * (1 - lzB z))) /
        (2 * (lzA z + lzB z * (1 - lzB z) + lza z) ^ 4) : ℝ) : ℂ) := by
  have hb : lzb z = 1 - lzB z := by linarith
  have hU' : lU z = lzA z + lzB z * (1 - lzB z) + lza z := by
    simp only [lU, la, lc, lS, hb]; ring
  rw [secondCoeff_ladderT2 hm he (hU' ▸ hU), hU']
  congr 3
  simp only [la, lc, lS, hb]
  ring

/-! ### The second-order coefficient of the projected numerator -/

theorem hasJet2_tendsto {g : ℝ → ℂ} {a b c : ℂ} (h : HasJet2 g a b c) :
    Tendsto g (𝓝 0) (𝓝 a) := by
  obtain ⟨ε, hε, he⟩ := h
  have hu := tendsto_ofReal_zero
  have hlim : Tendsto (fun u : ℝ => a + b * u + c * (u : ℂ) ^ 2 + (u : ℂ) ^ 2 * ε u) (𝓝 0)
      (𝓝 a) := by
    simpa using ((tendsto_const_nhds.add (hu.const_mul b)).add ((hu.pow 2).const_mul c)).add
      ((hu.pow 2).mul hε)
  exact hlim.congr fun u => (he u).symm

/-- A jet `c u² + o(u²)` times a function continuous at `0`. -/
theorem hasJet2_mul_tendsto {T V : ℝ → ℂ} {c V₀ : ℂ} (hT : HasJet2 T 0 0 c)
    (hV : Tendsto V (𝓝 0) (𝓝 V₀)) : HasJet2 (fun u => T u * V u) 0 0 (c * V₀) := by
  obtain ⟨ε, hε, he⟩ := hT
  refine ⟨fun u => ε u * V u + c * (V u - V₀), ?_, fun u => ?_⟩
  · have h1 : Tendsto (fun u => ε u * V u) (𝓝 0) (𝓝 0) := by simpa using hε.mul hV
    have h2 : Tendsto (fun u => c * (V u - V₀)) (𝓝 0) (𝓝 0) := by
      simpa using (hV.sub_const V₀).const_mul c
    simpa using h1.add h2
  · simp only
    rw [he u]
    ring

theorem tendsto_curveMomentum (m : ℝ) :
    Tendsto (curveMomentum m) (𝓝 0) (𝓝 (restMomentum m)) := by
  refine tendsto_pi_nhds.2 fun ν => ?_
  have h := (Complex.continuous_re.tendsto _).comp (hasJet2_tendsto (hasJet2_curveMomentum m ν))
  simpa [Function.comp_def] using h

@[fun_prop] theorem continuous_pvMomentaE_L (r : Fin 4 → ℝ) (i : Fin 8) (μ : Fin 4) :
    Continuous fun p' : Fin 4 → ℝ => pvMomentaE .L r p' i μ := by
  fin_cases i <;>
    simp [pvMomentaE, extMomenta, QED.Integration.TwoLoop.classLXMomenta,
      QED.Integration.TwoLoop.pvLines] <;> fun_prop

theorem continuous_ladderV (r : Fin 4 → ℝ) (M z : Fin 8 → ℝ) :
    Continuous fun p' : Fin 4 → ℝ => symanzikV ladderAlpha (pvMomentaE .L r p') M z := by
  unfold symanzikV symanzikVector QED.Minkowski.dot
  fun_prop

/-- The second Symanzik function along the curve tends to its value at `q = 0`. -/
theorem tendsto_ladderV (P : Params) (x : Fin 7 → ℝ) :
    Tendsto (fun u => ((symanzikV ladderAlpha (ladderMom P u) (pvMasses P) (simplexPoint x) : ℝ) :
        ℂ))
      (𝓝 0) (𝓝 ((openV .L P x : ℝ) : ℂ)) := by
  have h := ((continuous_ladderV (restMomentum P.m) (pvMasses P) (simplexPoint x)).tendsto
    (restMomentum P.m)).comp (tendsto_curveMomentum P.m)
  exact (Complex.continuous_ofReal.tendsto _).comp h

/-- **The jet of the projected ladder numerator**: `N(x, u) = c₂ u² + o(u²)` with
`c₂ = c₂[T₁] + c₂[T₂] V(x)`, `V(x)` the second Symanzik function at `q = 0`. -/
theorem hasJet2_openNum_L {P : Params} (hm : P.m = 1) (he : P.e = 1) (x : Fin 7 → ℝ)
    (hU : lU (simplexPoint x) ≠ 0) :
    HasJet2 (openNum .L P x) 0 0
      (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
          ((lza (simplexPoint x) * lQ (simplexPoint x) / (2 * lU (simplexPoint x) ^ 5) : ℝ) : ℂ) +
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
          ((lza (simplexPoint x) * (9 * lc (simplexPoint x) + la (simplexPoint x)) /
            (2 * lU (simplexPoint x) ^ 4) : ℝ) : ℂ) * ((openV .L P x : ℝ) : ℂ)) := by
  have hV := tendsto_ladderV P x
  have h := ((hasJet2_ladderT1 hm he hU).add (hasJet2_mul_tendsto
      (hasJet2_ladderT2 hm he hU) hV)).add
    (hasJet2_mul_tendsto (hasJet2_ladderT3 hm (simplexPoint x)) (hV.pow 2))
  exact h.of_eq (fun u => openNum_L_eq_T P x u) (by ring) (by ring) (by ring)

/-- **The second-order coefficient of the projected ladder numerator**: the integrand of
`openZero .L` is `c₂[N(x, ·)]/V⁴ = c₂[T₁]/V⁴ + c₂[T₂]/V³`, with
`c₂[N(x, ·)] = (Λ² - m_γ²)² ((6/K) z_a Q/(2U⁵) + (2/K) z_a (9c + a)/(2U⁴) · V)`. -/
theorem secondCoeff_openNum_L {P : Params} (hm : P.m = 1) (he : P.e = 1) (x : Fin 7 → ℝ)
    (hU : lU (simplexPoint x) ≠ 0) :
    secondCoeff (openNum .L P x) =
      ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
          ((lza (simplexPoint x) * lQ (simplexPoint x) / (2 * lU (simplexPoint x) ^ 5) : ℝ) : ℂ) +
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
          ((lza (simplexPoint x) * (9 * lc (simplexPoint x) + la (simplexPoint x)) /
            (2 * lU (simplexPoint x) ^ 4) : ℝ) : ℂ) * ((openV .L P x : ℝ) : ℂ) :=
  (hasJet2_openNum_L hm he x hU).secondCoeff_eq

/-- Almost every point of the simplex has `U ≠ 0`. -/
theorem ae_lU_ne_zero : ∀ᵐ x ∂(MeasureTheory.volume.restrict
    (QED.Integration.Feynman.simplexSet 7)),
    lU (simplexPoint x) ≠ 0 := by
  have hspan : ∃ i j, ladderAlpha i 0 * ladderAlpha j 1 - ladderAlpha i 1 * ladderAlpha j 0 ≠ 0 :=
    ⟨0, 1, by simp [castLoopMatrix, class5LoopMatrixPV, QED.Integration.TwoLoop.class5LoopMatrix]⟩
  filter_upwards [QED.Integration.TwoLoop.ae_posDef ladderAlpha (by norm_num) hspan] with x hx
  rw [← symanzikU_ladder]
  exact hx.2.det_pos.ne'

/-- **The ladder class value with the explicit integrand**: at `m = 1`, `e = 1`,
`openZero .L P = ∫_{Δ₇} (c₂[T₁] + c₂[T₂] V)/V⁴`. -/
theorem openZero_L_eq {P : Params} (hm : P.m = 1) (he : P.e = 1) :
    openZero .L P = ∫ x in QED.Integration.Feynman.simplexSet 7,
      (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) *
          ((lza (simplexPoint x) * lQ (simplexPoint x) / (2 * lU (simplexPoint x) ^ 5) : ℝ) : ℂ) +
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) *
          ((lza (simplexPoint x) * (9 * lc (simplexPoint x) + la (simplexPoint x)) /
            (2 * lU (simplexPoint x) ^ 4) : ℝ) : ℂ) * ((openV .L P x : ℝ) : ℂ)) /
        ((openV .L P x : ℝ) : ℂ) ^ 4 := by
  unfold openZero
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [ae_lU_ne_zero] with x hx
  rw [secondCoeff_openNum_L hm he x hx]

end QED.TwoLoop.UnitLGraphTrace

end
