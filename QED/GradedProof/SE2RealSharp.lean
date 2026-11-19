/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.FormFactorIndependence

/-!
# An antilinear automorphism of the Dirac matrices fixing every `γ^μ`

Helper level for the Phase 5 Stage 2 goal (G-ex₂) `QED.Graded.existsUnique_withLevel_one`
(decision D-57), the reality inputs `SEReal`, `VPReal` and the reality of the order-`e⁵` vertex
coefficient at `q = 0`.

In the Weyl representation `γ⁰, γ¹, γ³` are real and `γ²` is imaginary. The real matrix
`C = γ⁰γ¹γ³` commutes with `γ⁰, γ¹, γ³`, anticommutes with `γ²` and satisfies `C² = -1`, so

`X♯ = C X̄ C⁻¹ = -(C X̄ C)`

(`X̄` the entrywise complex conjugate) is an antilinear algebra automorphism of the `4 × 4`
complex matrices with `γ^μ♯ = γ^μ` (`sharp_gamma`), hence `p̸♯ = p̸` for real `p`
(`sharp_slash`). Every product of slashed real vectors, real scalars and `γ^μ` is `♯`-fixed, and a
`♯`-fixed matrix has real trace (`trace_sharp`). For the self-energy form,
`(a p̸ + b)♯ = ā p̸ + b̄` (`sharp_seMat`), so if `a p̸ + b` is `♯`-fixed and `p² ≠ 0`, then `a`
and `b` are real (`im_eq_zero_of_sharp_seMat`).
-/

@[expose] public section

open Complex Matrix

namespace QED.GradedProof.SE2Real

open QED.Dirac

/-- The real matrix `C = γ⁰γ¹γ³` of the Weyl representation. -/
def cMat : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, 1; 0, 0, -1, 0; 0, 1, 0, 0; -1, 0, 0, 0]

theorem cMat_mul_cMat : cMat * cMat = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cMat, Matrix.mul_apply, Fin.sum_univ_four]

/-- **The antilinear automorphism** `X♯ = -(C X̄ C)`. -/
noncomputable def sharp (X : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  -(cMat * X.map (starRingEnd ℂ) * cMat)

theorem map_conj_add (X Y : Matrix (Fin 4) (Fin 4) ℂ) :
    (X + Y).map (starRingEnd ℂ) = X.map (starRingEnd ℂ) + Y.map (starRingEnd ℂ) := by
  ext i j
  simp

theorem map_conj_neg (X : Matrix (Fin 4) (Fin 4) ℂ) :
    (-X).map (starRingEnd ℂ) = -X.map (starRingEnd ℂ) := by
  ext i j
  simp

theorem sharp_add (X Y : Matrix (Fin 4) (Fin 4) ℂ) : sharp (X + Y) = sharp X + sharp Y := by
  rw [sharp, sharp, sharp, map_conj_add, Matrix.mul_add, Matrix.add_mul, neg_add]

theorem sharp_neg (X : Matrix (Fin 4) (Fin 4) ℂ) : sharp (-X) = -sharp X := by
  rw [sharp, sharp, map_conj_neg, Matrix.mul_neg, Matrix.neg_mul]

theorem sharp_sub (X Y : Matrix (Fin 4) (Fin 4) ℂ) : sharp (X - Y) = sharp X - sharp Y := by
  rw [sub_eq_add_neg, sharp_add, sharp_neg, ← sub_eq_add_neg]

theorem sharp_zero : sharp 0 = 0 := by
  simp [sharp]

theorem sharp_smul (c : ℂ) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    sharp (c • X) = (starRingEnd ℂ c) • sharp X := by
  have h : (c • X).map (starRingEnd ℂ) = (starRingEnd ℂ c) • X.map (starRingEnd ℂ) := by
    ext i j
    simp
  simp only [sharp, h, Matrix.mul_smul, Matrix.smul_mul, smul_neg]

theorem sharp_mul (X Y : Matrix (Fin 4) (Fin 4) ℂ) : sharp (X * Y) = sharp X * sharp Y := by
  have h : (X * Y).map (starRingEnd ℂ) = X.map (starRingEnd ℂ) * Y.map (starRingEnd ℂ) :=
    Matrix.map_mul
  simp only [sharp, h, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  rw [show cMat * X.map (starRingEnd ℂ) * cMat * (cMat * Y.map (starRingEnd ℂ) * cMat) =
      cMat * X.map (starRingEnd ℂ) * (cMat * cMat) * Y.map (starRingEnd ℂ) * cMat by
    simp only [Matrix.mul_assoc], cMat_mul_cMat]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, Matrix.mul_assoc]

theorem sharp_one : sharp 1 = 1 := by
  simp [sharp, cMat_mul_cMat]

theorem sharp_sum {ι : Type*} (s : Finset ι) (X : ι → Matrix (Fin 4) (Fin 4) ℂ) :
    sharp (∑ i ∈ s, X i) = ∑ i ∈ s, sharp (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sharp_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, sharp_add, ih]

theorem sharp_sharp (X : Matrix (Fin 4) (Fin 4) ℂ) : sharp (sharp X) = X := by
  have hc : cMat.map (starRingEnd ℂ) = cMat := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cMat]
  have hX : (X.map (starRingEnd ℂ)).map (starRingEnd ℂ) = X := by
    ext i j
    simp
  have h : (sharp X).map (starRingEnd ℂ) = -(cMat * X * cMat) := by
    rw [sharp, map_conj_neg, Matrix.map_mul, Matrix.map_mul, hc, hX]
  rw [sharp, h]
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, cMat_mul_cMat]
  simp only [Matrix.mul_assoc, cMat_mul_cMat]
  simp

/-- **`γ^μ♯ = γ^μ`.** -/
theorem sharp_gamma (μ : Fin 4) : sharp (gamma μ) = gamma μ := by
  ext i j
  simp only [sharp, Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.map_apply]
  fin_cases μ <;> fin_cases i <;> fin_cases j <;> simp [cMat, gamma]

/-- **`p̸♯ = p̸`** for a real vector `p`. -/
theorem sharp_slash (p : Fin 4 → ℝ) : sharp (slash p) = slash p := by
  simp only [slash, sharp_sum, sharp_smul, sharp_gamma, Complex.conj_ofReal]

/-- The trace of `X♯` is the complex conjugate of the trace of `X`. -/
theorem trace_sharp (X : Matrix (Fin 4) (Fin 4) ℂ) :
    trace (sharp X) = starRingEnd ℂ (trace X) := by
  rw [sharp, trace_neg, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, cMat_mul_cMat]
  simp [trace, Fin.sum_univ_four]

/-! ### The self-energy form -/

/-- `(a p̸ + b)♯ = ā p̸ + b̄`. -/
theorem sharp_seForm (a b : ℂ) (p : Fin 4 → ℝ) :
    sharp (a • slash p + b • (1 : Matrix (Fin 4) (Fin 4) ℂ)) =
      (starRingEnd ℂ a) • slash p + (starRingEnd ℂ b) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [sharp_add, sharp_smul, sharp_smul, sharp_slash, sharp_one]

/-- The trace projections of `a p̸ + b`: `tr = 4b`, `tr(p̸ ·) = -4 p² a`. -/
theorem trace_seForm (a b : ℂ) (p : Fin 4 → ℝ) :
    trace (a • slash p + b • (1 : Matrix (Fin 4) (Fin 4) ℂ)) = 4 * b ∧
      trace (slash p * (a • slash p + b • (1 : Matrix (Fin 4) (Fin 4) ℂ))) =
        -4 * (Minkowski.dot p p : ℂ) * a := by
  constructor
  · rw [trace_add, trace_smul, trace_smul, trace_slash, trace_one, Fintype.card_fin]
    simp only [smul_eq_mul]
    push_cast
    ring
  · rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, trace_add, trace_smul,
      trace_smul, trace_slash_mul_slash, trace_slash, smul_eq_mul, smul_eq_mul]
    ring

/-- **A `♯`-fixed self-energy form has real coefficients** when `p² ≠ 0`. -/
theorem im_eq_zero_of_sharp_seForm {a b : ℂ} {p : Fin 4 → ℝ} (hp : Minkowski.dot p p ≠ 0)
    (h : sharp (a • slash p + b • (1 : Matrix (Fin 4) (Fin 4) ℂ)) =
      a • slash p + b • (1 : Matrix (Fin 4) (Fin 4) ℂ)) :
    a.im = 0 ∧ b.im = 0 := by
  rw [sharp_seForm] at h
  obtain ⟨t1, t2⟩ := trace_seForm a b p
  obtain ⟨s1, s2⟩ := trace_seForm (starRingEnd ℂ a) (starRingEnd ℂ b) p
  have hb : starRingEnd ℂ b = b := by
    have := congrArg trace h
    rw [s1, t1] at this
    exact mul_left_cancel₀ (by norm_num : (4 : ℂ) ≠ 0) this
  have ha : starRingEnd ℂ a = a := by
    have := congrArg (fun X => trace (slash p * X)) h
    rw [s2, t2] at this
    have hp' : (-4 * (Minkowski.dot p p : ℂ)) ≠ 0 := by
      have : (Minkowski.dot p p : ℂ) ≠ 0 := by exact_mod_cast hp
      exact mul_ne_zero (by norm_num) this
    exact mul_left_cancel₀ hp' this
  exact ⟨Complex.conj_eq_iff_im.1 ha, Complex.conj_eq_iff_im.1 hb⟩

end QED.GradedProof.SE2Real

end
