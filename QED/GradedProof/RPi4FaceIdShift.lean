/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdAvg

/-!
# (R-Π₄) step L6d3: shifted quartics

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. The averaged
self-energy face (`faceId_faceIdVal_se_avg`) needs a family of quartics `T W` with
`T W (ℓ₀, 0) = Q(ℓ₀, -b₁(W) - b(W) ℓ₀)` and integrable coefficients. The linear part of the
substitution is `lmap`; this file gives the constant part: the shifted quartic
`faceIdShift Q D` with `(faceIdShift Q D)(X) = Q(D + X)`, whose coefficients are polynomials in
`D` (continuous in a parameter when `D` is).

* `faceIdG2`, `faceIdG3`, `faceIdH3`, `faceIdG4`, `faceIdH4`, `faceIdJ4`: the coefficients of the
  expansions of the quadratic, cubic and quartic parts at `D + X`;
* `faceId_sum2_shift`, `faceId_sum3_shift`, `faceId_sum4_shift`: the expansions;
* **`faceIdShift`**, **`faceId_evalC_shift`**; `faceId_continuous_shift`,
  `faceId_continuous_lmap`: continuity of the coefficients;
* **`faceIdSET`**: the self-energy family, `faceId_eval_seT`, `faceId_coefInt_seT`, and
  **`faceId_faceIdVal_se_shift`**: the self-energy face as one reduced functional.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.TwoLoop.LimitCovariance (lmap)

section Expand

variable (D X : LoopIndex → ℂ)

/-- Moving a weighted outer sum inside one binder. -/
theorem faceId_sum_in1 (F : LoopIndex → LoopIndex → ℂ) :
    ∑ a, D a * ∑ b, F a b = ∑ b, (∑ a, D a * F a b) := by
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-- Moving a weighted outer sum inside two binders. -/
theorem faceId_sum_in2 (F : LoopIndex → LoopIndex → LoopIndex → ℂ) :
    ∑ a, D a * ∑ b, ∑ c, F a b c = ∑ b, ∑ c, (∑ a, D a * F a b c) := by
  rw [faceId_sum_in1]
  exact Finset.sum_congr rfl fun b _ => faceId_sum_in1 D (fun a c => F a b c)

/-- Moving a weighted outer sum inside three binders. -/
theorem faceId_sum_in3 (F : LoopIndex → LoopIndex → LoopIndex → LoopIndex → ℂ) :
    ∑ a, D a * ∑ b, ∑ c, ∑ d, F a b c d = ∑ b, ∑ c, ∑ d, (∑ a, D a * F a b c d) := by
  rw [faceId_sum_in1]
  exact Finset.sum_congr rfl fun b _ => faceId_sum_in2 D (fun a c d => F a b c d)

/-- The linear coefficient of a quadratic form at `D + X`. -/
def faceIdG2 (q : LoopIndex → LoopIndex → ℂ) (a : LoopIndex) : ℂ :=
  ∑ b, q a b * D b + ∑ b, D b * q b a

/-- Distributing a sum of products `(u + v)(A + B + C)`. -/
theorem faceId_sum_expand3 (u v A B C : LoopIndex → ℂ) :
    ∑ a, (u a + v a) * (A a + B a + C a) =
      ∑ a, u a * A a + ∑ a, u a * B a + ∑ a, u a * C a + ∑ a, v a * A a + ∑ a, v a * B a +
        ∑ a, v a * C a := by
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  ring

/-- Distributing a sum of products `(u + v)(A + B + C + E)`. -/
theorem faceId_sum_expand4 (u v A B C E : LoopIndex → ℂ) :
    ∑ a, (u a + v a) * (A a + B a + C a + E a) =
      ∑ a, u a * A a + ∑ a, u a * B a + ∑ a, u a * C a + ∑ a, u a * E a + ∑ a, v a * A a +
        ∑ a, v a * B a + ∑ a, v a * C a + ∑ a, v a * E a := by
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem faceId_sum2_shift (q : LoopIndex → LoopIndex → ℂ) :
    ∑ a, ∑ b, q a b * ((D + X) a * (D + X) b) =
      ∑ a, ∑ b, q a b * (D a * D b) + ∑ a, faceIdG2 D q a * X a +
        ∑ a, ∑ b, q a b * (X a * X b) := by
  have e : ∀ a, ∑ b, q a b * ((D + X) a * (D + X) b) =
      (D a + X a) * (∑ b, q a b * D b + ∑ b, q a b * X b) := by
    intro a
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have t1 : ∑ a, D a * ∑ b, q a b * D b = ∑ a, ∑ b, q a b * (D a * D b) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have t2 : ∑ a, D a * ∑ b, q a b * X b = ∑ a, (∑ b, D b * q b a) * X a := by
    rw [faceId_sum_in1]
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have t3 : ∑ a, X a * ∑ b, q a b * D b = ∑ a, (∑ b, q a b * D b) * X a :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have t4 : ∑ a, X a * ∑ b, q a b * X b = ∑ a, ∑ b, q a b * (X a * X b) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [Finset.sum_congr rfl fun a _ => e a]
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  rw [t1, t2, t3, t4]
  simp only [faceIdG2, add_mul, Finset.sum_add_distrib]
  ring

/-- The linear coefficient of a cubic form at `D + X`. -/
def faceIdG3 (k : LoopIndex → LoopIndex → LoopIndex → ℂ) (a : LoopIndex) : ℂ :=
  ∑ b, ∑ c, k a b c * (D b * D c) + ∑ a', D a' * faceIdG2 D (k a') a

/-- The quadratic coefficient of a cubic form at `D + X`. -/
def faceIdH3 (k : LoopIndex → LoopIndex → LoopIndex → ℂ) (a b : LoopIndex) : ℂ :=
  ∑ a', D a' * k a' a b + faceIdG2 D (k a) b

theorem faceId_sum3_shift (k : LoopIndex → LoopIndex → LoopIndex → ℂ) :
    ∑ a, ∑ b, ∑ c, k a b c * ((D + X) a * (D + X) b * (D + X) c) =
      ∑ a, ∑ b, ∑ c, k a b c * (D a * D b * D c) + ∑ a, faceIdG3 D k a * X a +
        ∑ a, ∑ b, faceIdH3 D k a b * (X a * X b) +
        ∑ a, ∑ b, ∑ c, k a b c * (X a * X b * X c) := by
  have e : ∀ a, ∑ b, ∑ c, k a b c * ((D + X) a * (D + X) b * (D + X) c) =
      (D a + X a) * (∑ b, ∑ c, k a b c * (D b * D c) + ∑ b, faceIdG2 D (k a) b * X b +
        ∑ b, ∑ c, k a b c * (X b * X c)) := by
    intro a
    rw [← faceId_sum2_shift]
    simp only [Finset.mul_sum, Pi.add_apply]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have t1 : ∑ a, D a * ∑ b, ∑ c, k a b c * (D b * D c) =
      ∑ a, ∑ b, ∑ c, k a b c * (D a * D b * D c) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have t2 : ∑ a, D a * ∑ b, faceIdG2 D (k a) b * X b =
      ∑ b, (∑ a, D a * faceIdG2 D (k a) b) * X b := by
    rw [faceId_sum_in1]
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have t3 : ∑ a, D a * ∑ b, ∑ c, k a b c * (X b * X c) =
      ∑ b, ∑ c, (∑ a, D a * k a b c) * (X b * X c) := by
    rw [faceId_sum_in2]
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have t4 : ∑ a, X a * ∑ b, ∑ c, k a b c * (D b * D c) =
      ∑ a, (∑ b, ∑ c, k a b c * (D b * D c)) * X a :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have t5 : ∑ a, X a * ∑ b, faceIdG2 D (k a) b * X b =
      ∑ a, ∑ b, faceIdG2 D (k a) b * (X a * X b) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have t6 : ∑ a, X a * ∑ b, ∑ c, k a b c * (X b * X c) =
      ∑ a, ∑ b, ∑ c, k a b c * (X a * X b * X c) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  rw [Finset.sum_congr rfl fun a _ => e a, faceId_sum_expand3, t1, t2, t3, t4, t5, t6]
  simp only [faceIdG3, faceIdH3, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  ring

/-- The linear coefficient of a quartic form at `D + X`. -/
def faceIdG4 (R : LoopIndex → LoopIndex → LoopIndex → LoopIndex → ℂ) (a : LoopIndex) : ℂ :=
  ∑ b, ∑ c, ∑ d, R a b c d * (D b * D c * D d) + ∑ a', D a' * faceIdG3 D (R a') a

/-- The quadratic coefficient of a quartic form at `D + X`. -/
def faceIdH4 (R : LoopIndex → LoopIndex → LoopIndex → LoopIndex → ℂ) (a b : LoopIndex) : ℂ :=
  ∑ a', D a' * faceIdH3 D (R a') a b + faceIdG3 D (R a) b

/-- The cubic coefficient of a quartic form at `D + X`. -/
def faceIdJ4 (R : LoopIndex → LoopIndex → LoopIndex → LoopIndex → ℂ) (a b c : LoopIndex) : ℂ :=
  ∑ a', D a' * R a' a b c + faceIdH3 D (R a) b c

theorem faceId_sum4_shift (R : LoopIndex → LoopIndex → LoopIndex → LoopIndex → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * ((D + X) a * (D + X) b * (D + X) c * (D + X) d) =
      ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * (D a * D b * D c * D d) + ∑ a, faceIdG4 D R a * X a +
        ∑ a, ∑ b, faceIdH4 D R a b * (X a * X b) +
        ∑ a, ∑ b, ∑ c, faceIdJ4 D R a b c * (X a * X b * X c) +
        ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * (X a * X b * X c * X d) := by
  have e : ∀ a, ∑ b, ∑ c, ∑ d, R a b c d * ((D + X) a * (D + X) b * (D + X) c * (D + X) d) =
      (D a + X a) * (∑ b, ∑ c, ∑ d, R a b c d * (D b * D c * D d) +
        ∑ b, faceIdG3 D (R a) b * X b + ∑ b, ∑ c, faceIdH3 D (R a) b c * (X b * X c) +
        ∑ b, ∑ c, ∑ d, R a b c d * (X b * X c * X d)) := by
    intro a
    rw [← faceId_sum3_shift]
    simp only [Finset.mul_sum, Pi.add_apply]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have t1 : ∑ a, D a * ∑ b, ∑ c, ∑ d, R a b c d * (D b * D c * D d) =
      ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * (D a * D b * D c * D d) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have t2 : ∑ a, D a * ∑ b, faceIdG3 D (R a) b * X b =
      ∑ b, (∑ a, D a * faceIdG3 D (R a) b) * X b := by
    rw [faceId_sum_in1]
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have t3 : ∑ a, D a * ∑ b, ∑ c, faceIdH3 D (R a) b c * (X b * X c) =
      ∑ b, ∑ c, (∑ a, D a * faceIdH3 D (R a) b c) * (X b * X c) := by
    rw [faceId_sum_in2]
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have t4 : ∑ a, D a * ∑ b, ∑ c, ∑ d, R a b c d * (X b * X c * X d) =
      ∑ b, ∑ c, ∑ d, (∑ a, D a * R a b c d) * (X b * X c * X d) := by
    rw [faceId_sum_in3]
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have t5 : ∑ a, X a * ∑ b, ∑ c, ∑ d, R a b c d * (D b * D c * D d) =
      ∑ a, (∑ b, ∑ c, ∑ d, R a b c d * (D b * D c * D d)) * X a :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have t6 : ∑ a, X a * ∑ b, faceIdG3 D (R a) b * X b =
      ∑ a, ∑ b, faceIdG3 D (R a) b * (X a * X b) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have t7 : ∑ a, X a * ∑ b, ∑ c, faceIdH3 D (R a) b c * (X b * X c) =
      ∑ a, ∑ b, ∑ c, faceIdH3 D (R a) b c * (X a * X b * X c) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have t8 : ∑ a, X a * ∑ b, ∑ c, ∑ d, R a b c d * (X b * X c * X d) =
      ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * (X a * X b * X c * X d) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [Finset.sum_congr rfl fun a _ => e a, faceId_sum_expand4, t1, t2, t3, t4, t5, t6, t7, t8]
  simp only [faceIdG4, faceIdH4, faceIdJ4, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  ring

end Expand

/-! ### The shifted quartic -/

/-- **The shifted quartic** `X ↦ Q(D + X)`. -/
def faceIdShift (Q : LoopQuartic) (D : LoopIndex → ℂ) : LoopQuartic where
  const := Q.evalC D
  lin a := Q.lin a + faceIdG2 D Q.quad a + faceIdG3 D Q.cub a + faceIdG4 D Q.quart a
  quad a b := Q.quad a b + faceIdH3 D Q.cub a b + faceIdH4 D Q.quart a b
  cub a b c := Q.cub a b c + faceIdJ4 D Q.quart a b c
  quart := Q.quart

/-- **The shifted quartic evaluates at `D + X`.** -/
theorem faceId_evalC_shift (Q : LoopQuartic) (D X : LoopIndex → ℂ) :
    (faceIdShift Q D).evalC X = Q.evalC (D + X) := by
  have l1 : ∑ a, Q.lin a * (D + X) a = ∑ a, Q.lin a * D a + ∑ a, Q.lin a * X a := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  simp only [LoopQuartic.evalC]
  rw [l1, faceId_sum2_shift, faceId_sum3_shift, faceId_sum4_shift]
  simp only [faceIdShift, LoopQuartic.evalC, add_mul, Finset.sum_add_distrib]
  ring

theorem faceId_quart_shift (Q : LoopQuartic) (D : LoopIndex → ℂ) :
    (faceIdShift Q D).quart = Q.quart := rfl

/-- **The coefficients of the shifted quartic are continuous** in a parameter, when those of the
quartic and the shift are. -/
theorem faceId_continuous_shift {α : Type*} [TopologicalSpace α] {Q : α → LoopQuartic}
    (h0 : Continuous fun w => (Q w).const) (h1 : ∀ a, Continuous fun w => (Q w).lin a)
    (h2 : ∀ a b, Continuous fun w => (Q w).quad a b)
    (h3 : ∀ a b c, Continuous fun w => (Q w).cub a b c)
    (h4 : ∀ a b c d, Continuous fun w => (Q w).quart a b c d)
    {D : α → LoopIndex → ℂ} (hD : ∀ a, Continuous fun w => D w a) :
    (Continuous fun w => (faceIdShift (Q w) (D w)).const) ∧
      (∀ a, Continuous fun w => (faceIdShift (Q w) (D w)).lin a) ∧
      (∀ a b, Continuous fun w => (faceIdShift (Q w) (D w)).quad a b) ∧
      (∀ a b c, Continuous fun w => (faceIdShift (Q w) (D w)).cub a b c) ∧
      (∀ a b c d, Continuous fun w => (faceIdShift (Q w) (D w)).quart a b c d) := by
  refine ⟨?_, fun a => ?_, fun a b => ?_, fun a b c => ?_, fun a b c d => h4 a b c d⟩
  · simp only [faceIdShift, LoopQuartic.evalC]
    fun_prop
  · simp only [faceIdShift, faceIdG2, faceIdG3, faceIdG4]
    fun_prop
  · simp only [faceIdShift, faceIdH3, faceIdH4, faceIdG2, faceIdG3]
    fun_prop
  · simp only [faceIdShift, faceIdJ4, faceIdH3, faceIdG2]
    fun_prop

/-- **The coefficients of `lmap` are continuous** in a continuous matrix. -/
theorem faceId_continuous_lmap {α : Type*} [TopologicalSpace α] (Q : LoopQuartic)
    {M : α → Matrix LoopIndex LoopIndex ℝ} (hM : ∀ a b, Continuous fun w => M w a b) :
    (Continuous fun w => (lmap (M w) Q).const) ∧
      (∀ a, Continuous fun w => (lmap (M w) Q).lin a) ∧
      (∀ a b, Continuous fun w => (lmap (M w) Q).quad a b) ∧
      (∀ a b c, Continuous fun w => (lmap (M w) Q).cub a b c) ∧
      (∀ a b c d, Continuous fun w => (lmap (M w) Q).quart a b c d) := by
  have hC : ∀ a b, Continuous fun w => ((M w a b : ℝ) : ℂ) := fun a b =>
    continuous_ofReal.comp (hM a b)
  refine ⟨continuous_const, fun b => ?_, fun b c => ?_, fun b c d => ?_, fun b c d e => ?_⟩
  · simp only [lmap]
    exact continuous_finsetSum _ fun a _ => continuous_const.mul (hC a b)
  · simp only [lmap]
    exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun a' _ =>
      continuous_const.mul ((hC a b).mul (hC a' c))
  · simp only [lmap]
    exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun a' _ =>
      continuous_finsetSum _ fun a'' _ =>
        continuous_const.mul (((hC a b).mul (hC a' c)).mul (hC a'' d))
  · simp only [lmap]
    exact continuous_finsetSum _ fun a₁ _ => continuous_finsetSum _ fun a₂ _ =>
      continuous_finsetSum _ fun a₃ _ => continuous_finsetSum _ fun a₄ _ =>
        continuous_const.mul ((((hC a₁ b).mul (hC a₂ c)).mul (hC a₃ d)).mul (hC a₄ e))

/-- The entries of `faceIdM (faceIdMb (f w))` are continuous for continuous `f`. -/
theorem faceId_continuous_faceIdMb {α : Type*} [TopologicalSpace α] {f : α → ℝ}
    (hf : Continuous f) (a b : LoopIndex) :
    Continuous fun w => faceIdM (faceIdMb (f w)) a b := by
  rcases a with ⟨i, μ⟩
  rcases b with ⟨j, ν⟩
  simp only [faceIdM]
  split_ifs
  · fin_cases i <;> fin_cases j <;> simp [faceIdMb] <;> fun_prop
  · exact continuous_const

/-! ### The self-energy family -/

open MeasureTheory
open QED.Integration.Feynman (simplexSet simplexPoint isCompact_simplexSet)

section SE

variable {q : ℕ} (S : FaceShape (0 + 1) q) (Q : LoopQuartic)

/-- **The self-energy family** `T W = Q(ℓ₀, ℓ₁ - b₁(W) - b(W) ℓ₀)`, a shifted `lmap`. -/
noncomputable def faceIdSET (W : Fin (0 + 1) → ℝ) : LoopQuartic :=
  faceIdShift (lmap (faceIdM (faceIdMb (S.b (simplexPoint W)))) Q)
    (loopComp ![0, -S.b₁ (simplexPoint W)])

theorem faceId_eval_seT (W : Fin (0 + 1) → ℝ) (ℓ₀ : Fin 4 → ℝ) :
    (faceIdSET S Q W).eval ![ℓ₀, 0] =
      Q.eval ![ℓ₀, -S.b₁ (simplexPoint W) - S.b (simplexPoint W) • ℓ₀] := by
  have e : loopComp ![0, -S.b₁ (simplexPoint W)] + loopComp ![ℓ₀, 0] =
      loopComp ![ℓ₀, -S.b₁ (simplexPoint W)] := by
    rw [← loopComp_add]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [faceIdSET, LoopQuartic.eval, faceId_evalC_shift, e, ← LoopQuartic.eval,
    faceId_eval_lmap_faceIdMb]

/-- The coefficients of the self-energy family are integrable on `Δ₁`. -/
theorem faceId_coefInt_seT :
    FaceIdCoefInt (volume.restrict (simplexSet (0 + 1))) (faceIdSET S Q) := by
  have hb : Continuous fun W : Fin (0 + 1) → ℝ => S.b (simplexPoint W) := by
    simp only [FaceShape.b]
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_simplexPoint i).mul continuous_const).mul continuous_const
  have hb₁ : ∀ μ, Continuous fun W : Fin (0 + 1) → ℝ => S.b₁ (simplexPoint W) μ := by
    intro μ
    simp only [FaceShape.b₁]
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_simplexPoint i).mul continuous_const).mul continuous_const
  obtain ⟨l0, l1, l2, l3, l4⟩ := faceId_continuous_lmap Q (faceId_continuous_faceIdMb hb)
  have hD : ∀ a, Continuous fun W : Fin (0 + 1) → ℝ =>
      loopComp ![0, -S.b₁ (simplexPoint W)] a := by
    rintro ⟨i, μ⟩
    simp only [loopComp]
    fin_cases i
    · simpa using continuous_const
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.neg_apply,
        ofReal_neg]
      exact (continuous_ofReal.comp (hb₁ μ)).neg
  obtain ⟨c0, c1, c2, c3, c4⟩ := faceId_continuous_shift l0 l1 l2 l3 l4 hD
  exact faceId_coefInt_of_continuous (isCompact_simplexSet _) c0 c1 c2 c3 c4

/-- **The self-energy face as one reduced functional** with the explicit family `faceIdSET`:
`faceIdVal n S Q = S.faceIdRedVal (n - 2) (∫_{Δ₁} T)` (only the integrability of the bracket on
`Δ₁ × Δ_q` remains as a hypothesis). -/
theorem faceId_faceIdVal_se_shift {n : ℕ} (hQ : LoopDegLe 1 1 Q)
    (hn : n = 7 ∨ (n = 6 ∧ Q.quart = 0))
    (hint : IntegrableOn (fun x : (Fin (0 + 1) → ℝ) × (Fin q → ℝ) =>
      faceIdRedBr (n - 2) (faceIdSET S Q x.1) (faceIdX0 (S.P0 (simplexPoint x.2)))
        (S.mR (simplexPoint x.2) -
          Minkowski.dot (S.P0 (simplexPoint x.2)) (S.P0 (simplexPoint x.2))))
      (simplexSet (0 + 1) ×ˢ simplexSet q)) :
    faceIdVal n S Q =
      S.faceIdRedVal (n - 2) (faceIdAvg (volume.restrict (simplexSet (0 + 1))) (faceIdSET S Q)) :=
  faceId_faceIdVal_se_avg S hQ hn (faceIdSET S Q) (faceId_eval_seT S Q) (faceId_coefInt_seT S Q)
    hint

end SE

end QED.GradedProof.RPi4

end
