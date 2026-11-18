/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.Contraction
public import QED.TwoLoop.ParametricBridge
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The planar Clifford subalgebra

Infrastructure for the Dirac traces of the ladder graph (section 8 of `docs/TWO-LOOP-UNITS.md`,
stage 1 of the L link). All momenta of the ladder at the shifted loop point lie in the plane of
`p = (m, 0, 0, 0)` and `p'`, spanned by `e₀, e₁`, so the electron numerators lie in the
subalgebra spanned by `1, γ⁰, γ¹, γ⁰γ¹`. This file represents that subalgebra by coordinates:

* `Pl`: the coordinates `(s, a, b, c)` of `s + a γ⁰ + b γ¹ + c γ⁰γ¹`, with the product of the
  Clifford relations `(γ⁰)² = 1`, `(γ¹)² = -1`, `γ¹γ⁰ = -γ⁰γ¹` (`Pl.toMat_mul`);
* `Pl.toMat`: the matrix, with `tr = 4 s` (`Pl.trace_toMat`);
* the transverse gammas `γ², γ³` anticommute with `γ⁰, γ¹`: `γⁱ X = X̄ γⁱ` with `X̄` the grade
  involution `Pl.bar` (`Pl.gamma_mul_toMat`), `(γⁱ)² = -1`, and `tr(X γⁱ) = 0`;
* the contractions: `γ^ν X γ_ν = Γ(X)` with `Γ(s, a, b, c) = (-4s, 2a, 2b, 0)`
  (`Pl.sum_gamma_toMat`), and `γ^ν X γⁱ γ_ν = Γ_T(X) γⁱ` with `Γ_T(s, a, b, c) = (2s, 0, 0, -2c)`
  for `i = 2, 3` (`Pl.sum_gamma_toMat_gamma`);
* the electron numerator of a planar momentum: `m - k̸ = (m, k⁰, -k¹, 0)`
  (`Pl.electronNumerator_planar`).
-/

@[expose] public section

open Complex Matrix

namespace QED.TwoLoop.UnitLGraphTrace

open QED.Dirac
open QED.TwoLoop.Bridge (electronNumerator)

/-- The coordinates `(s, a, b, c)` of the planar Clifford element `s + a γ⁰ + b γ¹ + c γ⁰γ¹`. -/
@[ext] structure Pl where
  /-- The scalar part. -/
  s : ℂ
  /-- The coefficient of `γ⁰`. -/
  a : ℂ
  /-- The coefficient of `γ¹`. -/
  b : ℂ
  /-- The coefficient of `γ⁰γ¹`. -/
  c : ℂ

namespace Pl

instance : Add Pl := ⟨fun x y => ⟨x.s + y.s, x.a + y.a, x.b + y.b, x.c + y.c⟩⟩
instance : Neg Pl := ⟨fun x => ⟨-x.s, -x.a, -x.b, -x.c⟩⟩
instance : Sub Pl := ⟨fun x y => ⟨x.s - y.s, x.a - y.a, x.b - y.b, x.c - y.c⟩⟩
instance : Zero Pl := ⟨⟨0, 0, 0, 0⟩⟩
instance : One Pl := ⟨⟨1, 0, 0, 0⟩⟩
instance : SMul ℂ Pl := ⟨fun k x => ⟨k * x.s, k * x.a, k * x.b, k * x.c⟩⟩

/-- The product of the planar Clifford algebra. -/
instance : Mul Pl := ⟨fun x y => ⟨x.s * y.s + x.a * y.a - x.b * y.b + x.c * y.c,
  x.s * y.a + x.a * y.s + x.b * y.c - x.c * y.b,
  x.s * y.b + x.b * y.s + x.a * y.c - x.c * y.a,
  x.s * y.c + x.c * y.s + x.a * y.b - x.b * y.a⟩⟩

variable (x y : Pl) (k : ℂ)

@[simp] theorem add_s : (x + y).s = x.s + y.s := rfl
@[simp] theorem add_a : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b : (x + y).b = x.b + y.b := rfl
@[simp] theorem add_c : (x + y).c = x.c + y.c := rfl
@[simp] theorem neg_s : (-x).s = -x.s := rfl
@[simp] theorem neg_a : (-x).a = -x.a := rfl
@[simp] theorem neg_b : (-x).b = -x.b := rfl
@[simp] theorem neg_c : (-x).c = -x.c := rfl
@[simp] theorem sub_s : (x - y).s = x.s - y.s := rfl
@[simp] theorem sub_a : (x - y).a = x.a - y.a := rfl
@[simp] theorem sub_b : (x - y).b = x.b - y.b := rfl
@[simp] theorem sub_c : (x - y).c = x.c - y.c := rfl
@[simp] theorem zero_s : (0 : Pl).s = 0 := rfl
@[simp] theorem zero_a : (0 : Pl).a = 0 := rfl
@[simp] theorem zero_b : (0 : Pl).b = 0 := rfl
@[simp] theorem zero_c : (0 : Pl).c = 0 := rfl
@[simp] theorem one_s : (1 : Pl).s = 1 := rfl
@[simp] theorem one_a : (1 : Pl).a = 0 := rfl
@[simp] theorem one_b : (1 : Pl).b = 0 := rfl
@[simp] theorem one_c : (1 : Pl).c = 0 := rfl
@[simp] theorem smul_s : (k • x).s = k * x.s := rfl
@[simp] theorem smul_a : (k • x).a = k * x.a := rfl
@[simp] theorem smul_b : (k • x).b = k * x.b := rfl
@[simp] theorem smul_c : (k • x).c = k * x.c := rfl
@[simp] theorem mul_s : (x * y).s = x.s * y.s + x.a * y.a - x.b * y.b + x.c * y.c := rfl
@[simp] theorem mul_a : (x * y).a = x.s * y.a + x.a * y.s + x.b * y.c - x.c * y.b := rfl
@[simp] theorem mul_b : (x * y).b = x.s * y.b + x.b * y.s + x.a * y.c - x.c * y.a := rfl
@[simp] theorem mul_c : (x * y).c = x.s * y.c + x.c * y.s + x.a * y.b - x.b * y.a := rfl

/-- The grade involution `s + a γ⁰ + b γ¹ + c γ⁰γ¹ ↦ s - a γ⁰ - b γ¹ + c γ⁰γ¹`. -/
def bar : Pl := ⟨x.s, -x.a, -x.b, x.c⟩

/-- The contraction `X ↦ γ^ν X γ_ν` on the planar subalgebra. -/
def gam : Pl := ⟨-4 * x.s, 2 * x.a, 2 * x.b, 0⟩

/-- The contraction around a transverse gamma: `γ^ν X γⁱ γ_ν = Γ_T(X) γⁱ` for `i = 2, 3`. -/
def gamT : Pl := ⟨2 * x.s, 0, 0, -2 * x.c⟩

@[simp] theorem bar_s : (bar x).s = x.s := rfl
@[simp] theorem bar_a : (bar x).a = -x.a := rfl
@[simp] theorem bar_b : (bar x).b = -x.b := rfl
@[simp] theorem bar_c : (bar x).c = x.c := rfl
@[simp] theorem gam_s : (gam x).s = -4 * x.s := rfl
@[simp] theorem gam_a : (gam x).a = 2 * x.a := rfl
@[simp] theorem gam_b : (gam x).b = 2 * x.b := rfl
@[simp] theorem gam_c : (gam x).c = 0 := rfl
@[simp] theorem gamT_s : (gamT x).s = 2 * x.s := rfl
@[simp] theorem gamT_a : (gamT x).a = 0 := rfl
@[simp] theorem gamT_b : (gamT x).b = 0 := rfl
@[simp] theorem gamT_c : (gamT x).c = -2 * x.c := rfl

/-- `γ⁰`. -/
def g0 : Pl := ⟨0, 1, 0, 0⟩
/-- `γ¹ = γ_1`. -/
def g1 : Pl := ⟨0, 0, 1, 0⟩
/-- `γ_0 = -γ⁰`. -/
def g0L : Pl := ⟨0, -1, 0, 0⟩

/-- The matrix `s + a γ⁰ + b γ¹ + c γ⁰γ¹` (Weyl representation). -/
def toMat : Matrix (Fin 4) (Fin 4) ℂ :=
  !![x.s, -x.c, x.a, x.b; -x.c, x.s, x.b, x.a; x.a, -x.b, x.s, x.c; -x.b, x.a, x.c, x.s]

theorem toMat_add : toMat (x + y) = toMat x + toMat y := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toMat] <;> ring

theorem toMat_sub : toMat (x - y) = toMat x - toMat y := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toMat] <;> ring

theorem toMat_neg : toMat (-x) = -toMat x := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toMat]

theorem toMat_smul : toMat (k • x) = k • toMat x := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toMat]

theorem toMat_zero : toMat 0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toMat]

theorem toMat_one : toMat 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toMat]

/-- **The product of the planar subalgebra.** -/
theorem toMat_mul : toMat x * toMat y = toMat (x * y) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toMat, Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring

/-- **The trace** `tr(s + a γ⁰ + b γ¹ + c γ⁰γ¹) = 4 s`. -/
theorem trace_toMat : trace (toMat x) = 4 * x.s := by
  simp [toMat, Matrix.trace, Fin.sum_univ_four]
  ring

theorem gamma_zero : gamma 0 = toMat g0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma, toMat, g0]

theorem gamma_one : gamma 1 = toMat g1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma, toMat, g1]

theorem gammaLower_zero : gammaLower 0 = toMat g0L := by
  rw [gammaLower_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma, toMat, g0L]

theorem gammaLower_one : gammaLower 1 = toMat g1 := by
  rw [gammaLower_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma, toMat, g1]

theorem gammaLower_two : gammaLower 2 = gamma 2 := by
  rw [gammaLower_eq]; rfl

theorem gammaLower_three : gammaLower 3 = gamma 3 := by
  rw [gammaLower_eq]; rfl

theorem gamma_two_mul_toMat : gamma 2 * toMat x = toMat (bar x) * gamma 2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [gamma, toMat, bar, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem gamma_three_mul_toMat : gamma 3 * toMat x = toMat (bar x) * gamma 3 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [gamma, toMat, bar, Matrix.mul_apply, Fin.sum_univ_four]

theorem gamma_two_mul_self : gamma 2 * gamma 2 = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma, Matrix.mul_apply, Fin.sum_univ_four]

theorem gamma_three_mul_self : gamma 3 * gamma 3 = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma, Matrix.mul_apply, Fin.sum_univ_four]

theorem trace_toMat_mul_gamma_two : trace (toMat x * gamma 2) = 0 := by
  simp [gamma, toMat, Matrix.trace, Fin.sum_univ_four]

theorem trace_toMat_mul_gamma_three : trace (toMat x * gamma 3) = 0 := by
  simp [gamma, toMat, Matrix.trace, Fin.sum_univ_four]

theorem gamma_two_sandwich : gamma 2 * toMat x * gamma 2 = toMat (-bar x) := by
  rw [gamma_two_mul_toMat, Matrix.mul_assoc, gamma_two_mul_self, Matrix.mul_neg, Matrix.mul_one,
    toMat_neg]

theorem gamma_three_sandwich : gamma 3 * toMat x * gamma 3 = toMat (-bar x) := by
  rw [gamma_three_mul_toMat, Matrix.mul_assoc, gamma_three_mul_self, Matrix.mul_neg,
    Matrix.mul_one, toMat_neg]

theorem gamma_three_two_three : gamma 3 * gamma 2 * gamma 3 = gamma 2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma, Matrix.mul_apply, Fin.sum_univ_four]

theorem gamma_two_three_two : gamma 2 * gamma 3 * gamma 2 = gamma 3 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma, Matrix.mul_apply, Fin.sum_univ_four]

theorem toMat_mul_gamma_two_mul (h : Pl) :
    toMat x * gamma 2 * toMat h = toMat (x * bar h) * gamma 2 := by
  rw [Matrix.mul_assoc, gamma_two_mul_toMat, ← Matrix.mul_assoc, toMat_mul]

theorem toMat_mul_gamma_three_mul (h : Pl) :
    toMat x * gamma 3 * toMat h = toMat (x * bar h) * gamma 3 := by
  rw [Matrix.mul_assoc, gamma_three_mul_toMat, ← Matrix.mul_assoc, toMat_mul]

theorem toMat_gamma_two_sq : toMat x * gamma 2 * gamma 2 = toMat (-x) := by
  rw [Matrix.mul_assoc, gamma_two_mul_self, Matrix.mul_neg, Matrix.mul_one, toMat_neg]

theorem toMat_gamma_three_sq : toMat x * gamma 3 * gamma 3 = toMat (-x) := by
  rw [Matrix.mul_assoc, gamma_three_mul_self, Matrix.mul_neg, Matrix.mul_one, toMat_neg]

theorem toMat_gamma_two_mul_toMat_gamma_two :
    toMat x * gamma 2 * (toMat y * gamma 2) = toMat (-(x * bar y)) := by
  rw [← Matrix.mul_assoc, toMat_mul_gamma_two_mul, toMat_gamma_two_sq]

theorem toMat_gamma_three_mul_toMat_gamma_three :
    toMat x * gamma 3 * (toMat y * gamma 3) = toMat (-(x * bar y)) := by
  rw [← Matrix.mul_assoc, toMat_mul_gamma_three_mul, toMat_gamma_three_sq]

theorem toMat_mul_toMat_gamma (M : Matrix (Fin 4) (Fin 4) ℂ) :
    toMat x * (toMat y * M) = toMat (x * y) * M := by
  rw [← Matrix.mul_assoc, toMat_mul]

theorem neg_mul' : (-x) * y = -(x * y) := by
  ext <;> simp <;> ring

theorem mul_neg' : x * (-y) = -(x * y) := by
  ext <;> simp <;> ring

/-- **The planar contraction** `γ^ν X γ_ν = Γ(X)`. -/
theorem sum_gamma_toMat : ∑ ν, gamma ν * toMat x * gammaLower ν = toMat (gam x) := by
  rw [Fin.sum_univ_four, gammaLower_zero, gammaLower_one, gammaLower_two, gammaLower_three,
    gamma_zero, gamma_one, gamma_two_sandwich, gamma_three_sandwich, toMat_mul, toMat_mul,
    toMat_mul, toMat_mul, ← toMat_add, ← toMat_add, ← toMat_add]
  congr 1
  ext <;> simp [g0, g1, g0L, gam, bar] <;> ring

/-- **The contraction around a transverse gamma** `γ^ν X γ² γ_ν = Γ_T(X) γ²`. -/
theorem sum_gamma_toMat_gamma_two :
    ∑ ν, gamma ν * (toMat x * gamma 2) * gammaLower ν = toMat (gamT x) * gamma 2 := by
  rw [Fin.sum_univ_four, gammaLower_zero, gammaLower_one, gammaLower_two, gammaLower_three,
    gamma_zero, gamma_one]
  have e0 : toMat g0 * (toMat x * gamma 2) * toMat g0L = toMat (g0 * x * bar g0L) * gamma 2 := by
    rw [← Matrix.mul_assoc, toMat_mul, toMat_mul_gamma_two_mul]
  have e1 : toMat g1 * (toMat x * gamma 2) * toMat g1 = toMat (g1 * x * bar g1) * gamma 2 := by
    rw [← Matrix.mul_assoc, toMat_mul, toMat_mul_gamma_two_mul]
  have e2 : gamma 2 * (toMat x * gamma 2) * gamma 2 = toMat (-bar x) * gamma 2 := by
    rw [← Matrix.mul_assoc, gamma_two_sandwich]
  have e3 : gamma 3 * (toMat x * gamma 2) * gamma 3 = toMat (bar x) * gamma 2 := by
    rw [← Matrix.mul_assoc, gamma_three_mul_toMat, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc (gamma 3), gamma_three_two_three]
  rw [e0, e1, e2, e3, ← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.add_mul, ← toMat_add,
    ← toMat_add, ← toMat_add]
  congr 2
  ext <;> simp [g0, g1, g0L, gamT, bar] <;> ring

/-- **The contraction around a transverse gamma** `γ^ν X γ³ γ_ν = Γ_T(X) γ³`. -/
theorem sum_gamma_toMat_gamma_three :
    ∑ ν, gamma ν * (toMat x * gamma 3) * gammaLower ν = toMat (gamT x) * gamma 3 := by
  rw [Fin.sum_univ_four, gammaLower_zero, gammaLower_one, gammaLower_two, gammaLower_three,
    gamma_zero, gamma_one]
  have e0 : toMat g0 * (toMat x * gamma 3) * toMat g0L = toMat (g0 * x * bar g0L) * gamma 3 := by
    rw [← Matrix.mul_assoc, toMat_mul, toMat_mul_gamma_three_mul]
  have e1 : toMat g1 * (toMat x * gamma 3) * toMat g1 = toMat (g1 * x * bar g1) * gamma 3 := by
    rw [← Matrix.mul_assoc, toMat_mul, toMat_mul_gamma_three_mul]
  have e2 : gamma 2 * (toMat x * gamma 3) * gamma 2 = toMat (bar x) * gamma 3 := by
    rw [← Matrix.mul_assoc, gamma_two_mul_toMat, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc (gamma 2), gamma_two_three_two]
  have e3 : gamma 3 * (toMat x * gamma 3) * gamma 3 = toMat (-bar x) * gamma 3 := by
    rw [← Matrix.mul_assoc, gamma_three_sandwich]
  rw [e0, e1, e2, e3, ← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.add_mul, ← toMat_add,
    ← toMat_add, ← toMat_add]
  congr 2
  ext <;> simp [g0, g1, g0L, gamT, bar] <;> ring

/-- The slash of a planar momentum: `k̸ = -k⁰ γ⁰ + k¹ γ¹`. -/
theorem slash_planar {q : Fin 4 → ℝ} (h2 : q 2 = 0) (h3 : q 3 = 0) :
    slash q = toMat ⟨0, -(q 0 : ℂ), (q 1 : ℂ), 0⟩ := by
  rw [slash, Fin.sum_univ_four, Minkowski.lower_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma, toMat, h2, h3]

/-- **The electron numerator of a planar momentum**: `m - k̸ = (m, k⁰, -k¹, 0)`. -/
theorem electronNumerator_planar (m : ℝ) {q : Fin 4 → ℝ} (h2 : q 2 = 0) (h3 : q 3 = 0) :
    electronNumerator m q = toMat ⟨(m : ℂ), (q 0 : ℂ), -(q 1 : ℂ), 0⟩ := by
  rw [electronNumerator, slash_planar h2 h3]
  ext i j; fin_cases i <;> fin_cases j <;> simp [toMat]

end Pl

end QED.TwoLoop.UnitLGraphTrace

end
