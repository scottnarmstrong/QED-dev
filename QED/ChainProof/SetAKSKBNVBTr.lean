/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKBNTr
public import QED.WickModel.VacuumPolarizationAlgebra

/-!
# Set (a), stage B3: the `(2, 3)` entry of the vertex class `VB` as a scalar

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage B3 (the nested
form). The vertex class `VB` has the numerator `K Tr[γ² S(P) Γ³(Q - k, Q) S(k + P)]`
(`ksB_vNum_VB`, `Γ = ksBVertexIns`), a trace of up to six slashes. With the odd traces zero
(`ksN_trace_five`) and the six-slash recursion `ksN_trace_six`
(`tr(a̸ b̸ c̸ d̸ e̸ f̸) = Σⱼ (-1)ʲ (a·xⱼ) tr(…x̂ⱼ…)`, from `{a̸, b̸} = -2a·b` and cyclicity):

* **`ksN_vNum_VB`**: `vNum(VB)₂₃(ℓ) = K · ksNTB m (ℓ 0) (ℓ 1) k`, with `A = Q - k`, `R = k + P`,
  `ksNTB = 8m²(P²R³ + R²P³) - 16m²(A³ + Q³)(P² + R²) + 8m²(Q²A³ + A²Q³) + 2 tr(γ²P̸Q̸γ³A̸R̸)`.

`K = faceIdKV e 0 1`. (Checked against the sympy fit of `vNum`, `setAKS4/fit23.py`.)
-/

@[expose] public section

open Complex Matrix

namespace QED.ChainProof.SetAKS

open QED.Integration.TwoLoop QED.TwoLoop.Bridge QED.GradedProof.VP2 QED.GradedProof.RPi4
open QED.Dirac

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-- The scalar `(2, 3)` entry of the class `VB` (photon factor `K` removed); `A = Q - k`,
`R = k + P`. -/
noncomputable def ksNTB (m : ℝ) (P Q k : Fin 4 → ℝ) : ℝ :=
  8 * m ^ 2 * (P 2 * (k + P) 3 + (k + P) 2 * P 3) -
    16 * m ^ 2 * ((Q - k) 3 + Q 3) * (P 2 + (k + P) 2) +
    8 * m ^ 2 * (Q 2 * (Q - k) 3 + (Q - k) 2 * Q 3) +
    8 * (-P 2 * (Q 3 * Minkowski.dot (Q - k) (k + P) - Minkowski.dot Q (Q - k) * (k + P) 3 +
          Minkowski.dot Q (k + P) * (Q - k) 3) +
      Q 2 * (P 3 * Minkowski.dot (Q - k) (k + P) - Minkowski.dot P (Q - k) * (k + P) 3 +
          Minkowski.dot P (k + P) * (Q - k) 3) +
      (Q - k) 2 * (Minkowski.dot P Q * (k + P) 3 - P 3 * Minkowski.dot Q (k + P) +
          Minkowski.dot P (k + P) * Q 3) -
      (k + P) 2 * (Minkowski.dot P Q * (Q - k) 3 - P 3 * Minkowski.dot Q (Q - k) +
          Minkowski.dot P (Q - k) * Q 3))

/-- The chirality matrix anticommutes with a product of five slashes. -/
theorem ksN_trace_five (a b c d f : Fin 4 → ℝ) :
    trace (slash a * slash b * slash c * slash d * slash f) = 0 := by
  refine trace_eq_zero_of_chirality_anticomm _ ?_
  simp only [Matrix.mul_assoc, chirality_mul_slash_mul, chirality_mul_slash, Matrix.mul_neg,
    neg_neg]

/-- Moving `a̸` past `y̸` inside a trace. -/
theorem ksN_trace_swap (L R : Mat) (a y : Fin 4 → ℝ) :
    trace (L * (slash a * (slash y * R))) =
      ((-2 * Minkowski.dot a y : ℝ) : ℂ) * trace (L * R) -
        trace (L * (slash y * (slash a * R))) := by
  have h : slash a * slash y =
      ((-2 * Minkowski.dot a y : ℝ) : ℂ) • (1 : Mat) - slash y * slash a := by
    rw [← slash_anticomm a y]
    abel
  rw [← Matrix.mul_assoc (slash a), h, Matrix.sub_mul, Matrix.mul_sub, trace_sub, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_smul, trace_smul, smul_eq_mul, Matrix.mul_assoc]

/-- **The six-slash trace** by moving `a̸` through the other five slashes. -/
theorem ksN_trace_six (a b c d f g : Fin 4 → ℝ) :
    trace (slash a * slash b * slash c * slash d * slash f * slash g) =
      -(Minkowski.dot a b : ℂ) * trace (slash c * slash d * slash f * slash g) +
        (Minkowski.dot a c : ℂ) * trace (slash b * slash d * slash f * slash g) -
        (Minkowski.dot a d : ℂ) * trace (slash b * slash c * slash f * slash g) +
        (Minkowski.dot a f : ℂ) * trace (slash b * slash c * slash d * slash g) -
        (Minkowski.dot a g : ℂ) * trace (slash b * slash c * slash d * slash f) := by
  have s1 := ksN_trace_swap 1 (slash c * (slash d * (slash f * slash g))) a b
  have s2 := ksN_trace_swap (slash b) (slash d * (slash f * slash g)) a c
  have s3 := ksN_trace_swap (slash b * slash c) (slash f * slash g) a d
  have s4 := ksN_trace_swap (slash b * slash c * slash d) (slash g) a f
  have s5 := ksN_trace_swap (slash b * slash c * slash d * slash f) 1 a g
  have hc := trace_mul_comm (slash b * slash c * slash d * slash f * slash g) (slash a)
  simp only [Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one] at s1 s2 s3 s4 s5 hc ⊢
  push_cast at s1 s2 s3 s4 s5 ⊢
  linear_combination (s1 - s2 + s3 - s4 + s5 - hc) / 2

/-- **The `(2, 3)` entry of the class `VB`.** -/
theorem ksN_trace_VB (m : ℝ) (P Q k : Fin 4 → ℝ) :
    (gamma 2 * electronNumerator m P * ksBVertexIns m (Q - k) Q 3 *
      electronNumerator m (k + P)).trace = (ksNTB m P Q k : ℂ) := by
  simp only [ksBVertexIns, electronNumerator, ksB_gamma_eq_slash]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, ← Matrix.mul_assoc, trace_add, trace_sub,
    trace_smul, trace_slash, trace_slash_mul_slash, trace_slash_mul_slash_mul_slash,
    ksN_trace_five, ksN_trace_six, trace_slash_mul_slash_mul_slash_mul_slash, ksB_single_dot,
    ksB_dot_single, smul_eq_mul]
  simp only [ksNTB, Minkowski.dot, Minkowski.metric, Fin.sum_univ_four, Pi.single_apply,
    Pi.add_apply, Pi.sub_apply]
  simp
  ring

/-- **The `(2, 3)` entry of the `VB` numerator as a scalar.** -/
theorem ksN_vNum_VB (e m : ℝ) (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    vNum e 0 1 aVB baseVB cVB m k ℓ 2 3 = faceIdKV e 0 1 * (ksNTB m (ℓ 0) (ℓ 1) k : ℂ) := by
  rw [ksB_vNum_VB, ksN_trace_VB]

end QED.ChainProof.SetAKS

end
