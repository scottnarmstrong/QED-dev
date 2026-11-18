/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ClassLimitParametric
public import QED.TwoLoop.LimitCovarianceLorentz
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Linear combinations and linear substitutions of loop quartics

Part of obligation O2-20 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4). The parametric integrand
`QED.TwoLoop.ClassLimit.paramIntegrand Q α p M ε x` of a numerator `Q : LoopQuartic` is built
from the value `Q(-S)`, the contraction `∑ Hₐ_b(-S) Gₐ_b` and the contraction `∑ Rₐ_bcd Πₐ_bcd(G)`
with `G = loopMetricInv A`. This file proves:

* **linearity** (`paramIntegrand_qsum`): for the coefficientwise linear combination
  `qsum s c Q` of quartics, the integrand is the same linear combination;
* **substitution** (`evalC_lmap`, `contractTwo_lmap`, `contractFour_lmap`): for the quartic
  `lmap M Q` with `(lmap M Q)(X) = Q(M X)` (`M` a real matrix on the eight loop components), the
  contractions with `G` become contractions with `M G Mᵀ`. The quadratic contraction goes through
  the even part of the quartic (`LoopQuartic.evalC_add_add_evalC_sub`) and a polarization
  (`sum_mul_symm_eq_of_quadForm_eq`), so the cubic and quartic parts of the Hessian need not be
  transformed separately.
-/

@[expose] public section

open Complex

namespace QED.TwoLoop.LimitCovariance

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint)
open scoped Matrix

/-! ### Moving sums -/

section SumMove

variable {ι κ R : Type*} [Fintype ι] [AddCommMonoid R] (t : Finset κ)

theorem sum_out1 (G : ι → κ → R) : ∑ b, ∑ a ∈ t, G b a = ∑ a ∈ t, ∑ b, G b a :=
  Finset.sum_comm

theorem sum_out2 (G : ι → ι → κ → R) :
    ∑ b, ∑ c, ∑ a ∈ t, G b c a = ∑ a ∈ t, ∑ b, ∑ c, G b c a := by
  rw [Finset.sum_congr rfl fun b _ => sum_out1 t _]
  exact Finset.sum_comm

theorem sum_out3 (G : ι → ι → ι → κ → R) :
    ∑ b, ∑ c, ∑ d, ∑ a ∈ t, G b c d a = ∑ a ∈ t, ∑ b, ∑ c, ∑ d, G b c d a := by
  rw [Finset.sum_congr rfl fun b _ => sum_out2 t _]
  exact Finset.sum_comm

theorem sum_out4 (G : ι → ι → ι → ι → κ → R) :
    ∑ b, ∑ c, ∑ d, ∑ e, ∑ a ∈ t, G b c d e a = ∑ a ∈ t, ∑ b, ∑ c, ∑ d, ∑ e, G b c d e a := by
  rw [Finset.sum_congr rfl fun b _ => sum_out3 t _]
  exact Finset.sum_comm

end SumMove

/-! ### Linear combinations -/

/-- The coefficientwise linear combination `∑ₖ cₖ Qₖ` of quartics. -/
noncomputable def qsum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (Q : ι → LoopQuartic) :
    LoopQuartic where
  const := ∑ k ∈ s, c k * (Q k).const
  lin a := ∑ k ∈ s, c k * (Q k).lin a
  quad a b := ∑ k ∈ s, c k * (Q k).quad a b
  cub a b d := ∑ k ∈ s, c k * (Q k).cub a b d
  quart a b d e := ∑ k ∈ s, c k * (Q k).quart a b d e

section QSum

variable {ι : Type*} (s : Finset ι) (c : ι → ℂ) (Q : ι → LoopQuartic)

theorem evalC_qsum (X : LoopIndex → ℂ) :
    (qsum s c Q).evalC X = ∑ k ∈ s, c k * (Q k).evalC X := by
  simp only [LoopQuartic.evalC, qsum, Finset.sum_mul, mul_add, Finset.mul_sum,
    Finset.sum_add_distrib]
  rw [sum_out1, sum_out2, sum_out3, sum_out4]
  simp only [mul_assoc]

theorem eval_qsum (ℓ : Fin 2 → Fin 4 → ℝ) :
    (qsum s c Q).eval ℓ = ∑ k ∈ s, c k * (Q k).eval ℓ :=
  evalC_qsum s c Q _

theorem quartSym_qsum (a b d e : LoopIndex) :
    (qsum s c Q).quartSym a b d e = ∑ k ∈ s, c k * (Q k).quartSym a b d e := by
  simp only [LoopQuartic.quartSym, qsum, mul_add, Finset.sum_add_distrib]

theorem hess_qsum (X : LoopIndex → ℂ) (a b : LoopIndex) :
    (qsum s c Q).hess X a b = ∑ k ∈ s, c k * (Q k).hess X a b := by
  simp only [LoopQuartic.hess, quartSym_qsum]
  simp only [qsum, add_mul, Finset.sum_mul, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  rw [sum_out1, sum_out1, sum_out1, sum_out2]
  simp only [mul_assoc]

theorem contractTwo_qsum (A : Matrix (Fin 2) (Fin 2) ℝ) (X : LoopIndex → ℂ) :
    (qsum s c Q).contractTwo A X = ∑ k ∈ s, c k * (Q k).contractTwo A X := by
  simp only [LoopQuartic.contractTwo, hess_qsum, Finset.sum_mul, Finset.mul_sum]
  rw [sum_out2]
  simp only [mul_assoc]

theorem contractFour_qsum (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (qsum s c Q).contractFour A = ∑ k ∈ s, c k * (Q k).contractFour A := by
  simp only [LoopQuartic.contractFour, qsum, Finset.sum_mul, Finset.mul_sum]
  rw [sum_out4]
  simp only [mul_assoc]

theorem paramIntegrand_qsum {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (M : Fin (m + 1) → ℝ) (ε : ℝ) (x : Fin m → ℝ) :
    ClassLimit.paramIntegrand (qsum s c Q) α p M ε x =
      ∑ k ∈ s, c k * ClassLimit.paramIntegrand (Q k) α p M ε x := by
  simp only [ClassLimit.paramIntegrand, eval_qsum, contractTwo_qsum, contractFour_qsum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

end QSum


/-! ### Block swaps -/

section Block

variable {ι R : Type*} [Fintype ι] [AddCommMonoid R]

theorem sum_block2 (f : ι → ι → ι → ι → R) :
    ∑ b, ∑ c, ∑ a, ∑ a', f b c a a' = ∑ a, ∑ a', ∑ b, ∑ c, f b c a a' := by
  rw [sum_out2]
  exact Finset.sum_congr rfl fun a _ => sum_out2 _ _

theorem sum_block3 (f : ι → ι → ι → ι → ι → ι → R) :
    ∑ b, ∑ c, ∑ d, ∑ a, ∑ a', ∑ a'', f b c d a a' a'' =
      ∑ a, ∑ a', ∑ a'', ∑ b, ∑ c, ∑ d, f b c d a a' a'' := by
  rw [sum_out3]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_out3]
  exact Finset.sum_congr rfl fun a' _ => sum_out3 _ _

theorem sum_block4 (f : ι → ι → ι → ι → ι → ι → ι → ι → R) :
    ∑ b, ∑ c, ∑ d, ∑ e, ∑ a₁, ∑ a₂, ∑ a₃, ∑ a₄, f b c d e a₁ a₂ a₃ a₄ =
      ∑ a₁, ∑ a₂, ∑ a₃, ∑ a₄, ∑ b, ∑ c, ∑ d, ∑ e, f b c d e a₁ a₂ a₃ a₄ := by
  rw [sum_out4]
  refine Finset.sum_congr rfl fun a₁ _ => ?_
  rw [sum_out4]
  refine Finset.sum_congr rfl fun a₂ _ => ?_
  rw [sum_out4]
  exact Finset.sum_congr rfl fun a₃ _ => sum_out4 _ _

theorem sum4_rev (g : ι → ι → ι → ι → R) :
    ∑ a, ∑ b, ∑ c, ∑ d, g a b c d = ∑ d, ∑ c, ∑ b, ∑ a, g a b c d := by
  rw [sum_out3]
  exact Finset.sum_congr rfl fun d _ => sum3_rev _

end Block

/-! ### Linear substitution -/

section LMap

variable (M : Matrix LoopIndex LoopIndex ℝ)

/-- `M X` for complex `X`. -/
noncomputable def actC (X : LoopIndex → ℂ) : LoopIndex → ℂ := fun a => ∑ b, (M a b : ℂ) * X b

theorem actC_add (X D : LoopIndex → ℂ) : actC M (X + D) = actC M X + actC M D := by
  funext a
  simp only [actC, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem actC_sub (X D : LoopIndex → ℂ) : actC M (X - D) = actC M X - actC M D := by
  funext a
  simp only [actC, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem actC_smul (r : ℂ) (X : LoopIndex → ℂ) : actC M (r • X) = r • actC M X := by
  funext a
  simp only [actC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The quartic `X ↦ Q(M X)`. -/
noncomputable def lmap (Q : LoopQuartic) : LoopQuartic where
  const := Q.const
  lin b := ∑ a, Q.lin a * (M a b : ℂ)
  quad b c := ∑ a, ∑ a', Q.quad a a' * ((M a b : ℂ) * M a' c)
  cub b c d := ∑ a, ∑ a', ∑ a'', Q.cub a a' a'' * ((M a b : ℂ) * M a' c * M a'' d)
  quart b c d e := ∑ a₁, ∑ a₂, ∑ a₃, ∑ a₄,
    Q.quart a₁ a₂ a₃ a₄ * ((M a₁ b : ℂ) * M a₂ c * M a₃ d * M a₄ e)

variable (Q : LoopQuartic)

theorem lin_part_lmap (X : LoopIndex → ℂ) :
    ∑ b, (lmap M Q).lin b * X b = ∑ a, Q.lin a * actC M X a := by
  simp only [lmap, actC, Finset.sum_mul, Finset.mul_sum]
  rw [sum_out1]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem quad_part_lmap (X : LoopIndex → ℂ) :
    ∑ b, ∑ c, (lmap M Q).quad b c * (X b * X c) =
      ∑ a, ∑ a', Q.quad a a' * (actC M X a * actC M X a') := by
  simp only [lmap, actC, Finset.sum_mul, Finset.mul_sum]
  rw [sum_block2]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem cub_part_lmap (X : LoopIndex → ℂ) :
    ∑ b, ∑ c, ∑ d, (lmap M Q).cub b c d * (X b * X c * X d) =
      ∑ a, ∑ a', ∑ a'', Q.cub a a' a'' * (actC M X a * actC M X a' * actC M X a'') := by
  simp only [lmap, actC, Finset.sum_mul, Finset.mul_sum]
  rw [sum_block3]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  rw [sum3_rev]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem quartPart_lmap (X : LoopIndex → ℂ) :
    (lmap M Q).quartPart X = Q.quartPart (actC M X) := by
  simp only [LoopQuartic.quartPart, lmap, actC, Finset.sum_mul, Finset.mul_sum]
  rw [sum_block4]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [sum4_rev]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The substituted quartic evaluates at `M X`.** -/
theorem evalC_lmap (X : LoopIndex → ℂ) : (lmap M Q).evalC X = Q.evalC (actC M X) := by
  have h := quartPart_lmap M Q X
  simp only [LoopQuartic.quartPart] at h
  simp only [LoopQuartic.evalC, lin_part_lmap, quad_part_lmap, cub_part_lmap, h]
  rfl

end LMap


/-! ### The contractions under substitution -/

section Contract

/-- The Hessian quadratic form, through values of the quartic. -/
theorem hessForm_eq (P : LoopQuartic) (X D : LoopIndex → ℂ) :
    ∑ a, ∑ b, P.hess X a b * (D a * D b) =
      (16 * (P.evalC (X + D) + P.evalC (X - D)) -
        (P.evalC (X + (2 : ℂ) • D) + P.evalC (X - (2 : ℂ) • D))) / 24 - 5 / 4 * P.evalC X := by
  have h1 := P.evalC_add_add_evalC_sub X D
  have h2 := P.evalC_add_add_evalC_sub X ((2 : ℂ) • D)
  have e1 : ∑ a, ∑ b, P.hess X a b * (((2 : ℂ) • D) a * ((2 : ℂ) • D) b) =
      4 * ∑ a, ∑ b, P.hess X a b * (D a * D b) := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e2 : P.quartPart ((2 : ℂ) • D) = 16 * P.quartPart D := by
    simp only [LoopQuartic.quartPart, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, e2] at h2
  linear_combination (-16 * h1 + h2) / 24

theorem hessForm_lmap (M : Matrix LoopIndex LoopIndex ℝ) (P : LoopQuartic)
    (X D : LoopIndex → ℂ) :
    ∑ a, ∑ b, (lmap M P).hess X a b * (D a * D b) =
      ∑ a, ∑ b, P.hess (actC M X) a b * (actC M D a * actC M D b) := by
  rw [hessForm_eq, hessForm_eq]
  simp only [evalC_lmap, actC_add, actC_sub, actC_smul]

/-- **Polarization**: two coefficient matrices with the same quadratic form have the same
contraction with every symmetric matrix. -/
theorem sum_mul_symm_eq_of_quadForm_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H H' : ι → ι → ℂ)
    (h : ∀ D : ι → ℂ, ∑ a, ∑ b, H a b * (D a * D b) = ∑ a, ∑ b, H' a b * (D a * D b))
    (G : ι → ι → ℂ) (hG : ∀ a b, G a b = G b a) :
    ∑ a, ∑ b, H a b * G a b = ∑ a, ∑ b, H' a b * G a b := by
  -- the bilinear expansion of a quadratic form
  have hq : ∀ (K : ι → ι → ℂ) (u w : ι → ℂ), ∑ a, ∑ b, K a b * ((u + w) a * (u + w) b) =
      ∑ a, ∑ b, K a b * (u a * u b) + ∑ a, ∑ b, K a b * (w a * w b) +
        ∑ a, ∑ b, K a b * (u a * w b) + ∑ a, ∑ b, K a b * (w a * u b) := by
    intro K u w
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hδ : ∀ (K : ι → ι → ℂ) (a b : ι),
      ∑ c, ∑ d, K c d * ((fun x => if x = a then (1 : ℂ) else 0) c *
        (fun x => if x = b then (1 : ℂ) else 0) d) = K a b := by
    intro K a b
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hsym : ∀ a b, H a b + H b a = H' a b + H' b a := by
    intro a b
    have e := h ((fun x => if x = a then (1 : ℂ) else 0) + fun x => if x = b then (1 : ℂ) else 0)
    rw [hq, hq, hδ, hδ, hδ, hδ, hδ, hδ, hδ, hδ] at e
    have ea := h fun x => if x = a then (1 : ℂ) else 0
    have eb := h fun x => if x = b then (1 : ℂ) else 0
    rw [hδ, hδ] at ea eb
    linear_combination e - ea - eb
  have hsplit : ∀ K : ι → ι → ℂ,
      2 * ∑ a, ∑ b, K a b * G a b = ∑ a, ∑ b, (K a b + K b a) * G a b := by
    intro K
    have e : ∑ a, ∑ b, K b a * G a b = ∑ a, ∑ b, K a b * G a b := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hG]
    simp only [add_mul, Finset.sum_add_distrib, e]
    ring
  have h2 : 2 * ∑ a, ∑ b, H a b * G a b = 2 * ∑ a, ∑ b, H' a b * G a b := by
    rw [hsplit, hsplit]
    simp only [hsym]
  have h2' : (2 : ℂ) ≠ 0 := two_ne_zero
  exact mul_left_cancel₀ h2' h2

theorem conj_apply (M B : Matrix LoopIndex LoopIndex ℝ) (x y : LoopIndex) :
    (M * B * Mᵀ) x y = ∑ b, ∑ c, M x b * M y c * B b c := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem loopMetricInv_symm {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : Aᵀ = A) (a b : LoopIndex) :
    loopMetricInv A a b = loopMetricInv A b a := by
  have hinv : A⁻¹ᵀ = A⁻¹ := by rw [Matrix.transpose_nonsing_inv, hA]
  have e : A⁻¹ a.1 b.1 = A⁻¹ b.1 a.1 := by
    rw [← Matrix.transpose_apply A⁻¹ b.1 a.1, hinv]
  simp only [loopMetricInv, e, Minkowski.metric_symm a.2 b.2]

/-- **The quadratic contraction under substitution.** -/
theorem contractTwo_lmap (M : Matrix LoopIndex LoopIndex ℝ) (P : LoopQuartic)
    {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : Aᵀ = A) (X : LoopIndex → ℂ) :
    (lmap M P).contractTwo A X =
      ∑ a, ∑ b, P.hess (actC M X) a b * (((M * loopMetricInv A * Mᵀ) a b : ℝ) : ℂ) := by
  classical
  set H' : LoopIndex → LoopIndex → ℂ := fun b c =>
    ∑ a, ∑ a', ((M a b : ℂ) * M a' c) * P.hess (actC M X) a a' with hH'
  have hq : ∀ D : LoopIndex → ℂ, ∑ a, ∑ b, (lmap M P).hess X a b * (D a * D b) =
      ∑ a, ∑ b, H' a b * (D a * D b) := by
    intro D
    rw [hessForm_lmap]
    simp only [hH', actC, Finset.sum_mul, Finset.mul_sum]
    rw [sum_block2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hpol := sum_mul_symm_eq_of_quadForm_eq _ _ hq
    (fun a b => ((loopMetricInv A a b : ℝ) : ℂ)) fun a b => by rw [loopMetricInv_symm hA]
  unfold LoopQuartic.contractTwo
  rw [hpol]
  simp only [hH', conj_apply, Finset.sum_mul]
  push_cast
  rw [sum_block2]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem matPair_conj (M B : Matrix LoopIndex LoopIndex ℝ) (a₁ a₂ a₃ a₄ : LoopIndex) :
    ∑ b, ∑ c, ∑ d, ∑ e, M a₁ b * M a₂ c * M a₃ d * M a₄ e * matPair B b c d e =
      matPair (M * B * Mᵀ) a₁ a₂ a₃ a₄ := by
  simp only [matPair, conj_apply, Finset.sum_mul_sum, mul_add, Finset.sum_add_distrib]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The quartic contraction under substitution.** -/
theorem contractFour_lmap (M : Matrix LoopIndex LoopIndex ℝ) (P : LoopQuartic)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (lmap M P).contractFour A =
      ∑ a₁, ∑ a₂, ∑ a₃, ∑ a₄,
        P.quart a₁ a₂ a₃ a₄ * (matPair (M * loopMetricInv A * Mᵀ) a₁ a₂ a₃ a₄ : ℂ) := by
  unfold LoopQuartic.contractFour
  simp only [lmap, Finset.sum_mul]
  rw [sum_block4]
  refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ =>
    Finset.sum_congr rfl fun a₃ _ => Finset.sum_congr rfl fun a₄ _ => ?_
  rw [← matPair_conj]
  push_cast
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end Contract


/-! ### Lorentz maps on the two loop momenta -/

section Block

/-- `L` acting on each of the two loop momenta. -/
def blockL (L : Matrix (Fin 4) (Fin 4) ℝ) : Matrix LoopIndex LoopIndex ℝ :=
  fun a b => if a.1 = b.1 then L a.2 b.2 else 0

theorem actC_blockL_loopComp (L : Matrix (Fin 4) (Fin 4) ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    actC (blockL L) (loopComp ℓ) = loopComp (loopAct L ℓ) := by
  funext a
  obtain ⟨s, μ⟩ := a
  simp only [actC, blockL, loopComp, loopAct, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    ofReal_sum, ofReal_mul]
  rw [Finset.sum_eq_single s]
  · exact Finset.sum_congr rfl fun ν _ => by simp
  · intro r _ hr
    simp [Ne.symm hr]
  · simp

theorem eval_lmap_blockL (L : Matrix (Fin 4) (Fin 4) ℝ) (Q : LoopQuartic)
    (ℓ : Fin 2 → Fin 4 → ℝ) : (lmap (blockL L) Q).eval ℓ = Q.eval (loopAct L ℓ) := by
  simp only [LoopQuartic.eval, evalC_lmap, actC_blockL_loopComp]

theorem sum_blockL_mul (L : Matrix (Fin 4) (Fin 4) ℝ) (s : Fin 2) (μ : Fin 4)
    (f : LoopIndex → ℝ) : ∑ b, blockL L (s, μ) b * f b = ∑ ρ, L μ ρ * f (s, ρ) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
  · simp [blockL]
  · intro r _ hr
    simp [blockL, Ne.symm hr]
  · simp

theorem blockL_conj_loopMetricInv {L : Matrix (Fin 4) (Fin 4) ℝ}
    (hL : ∀ μ ν, ∑ a, ∑ b, L μ a * L ν b * Minkowski.metric a b = Minkowski.metric μ ν)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    blockL L * loopMetricInv A * (blockL L)ᵀ = loopMetricInv A := by
  ext x y
  obtain ⟨s, μ⟩ := x
  obtain ⟨r, ν⟩ := y
  rw [conj_apply]
  have e : ∀ b, ∑ c, blockL L (s, μ) b * blockL L (r, ν) c * loopMetricInv A b c =
      blockL L (s, μ) b * ∑ c, blockL L (r, ν) c * loopMetricInv A b c := fun b => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp only [e]
  simp only [sum_blockL_mul, loopMetricInv]
  rw [← hL μ ν, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring

theorem symanzikMatrix_transpose {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (z : Fin (m + 1) → ℝ) :
    (symanzikMatrix α z)ᵀ = symanzikMatrix α z := by
  ext s t
  simp only [Matrix.transpose_apply, symanzikMatrix, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem loopShift_apply {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (z : Fin (m + 1) → ℝ) (s : Fin 2) (μ : Fin 4) :
    loopShift α p z s μ =
      ∑ t, (symanzikMatrix α z)⁻¹ s t * ∑ i, z i * α i t * p i μ := by
  refine Fin.cases ?_ (fun c => ?_) μ <;> rfl

theorem loopAct_loopShift {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (z : Fin (m + 1) → ℝ) {L : Matrix (Fin 4) (Fin 4) ℝ} (hp : ∀ i, L *ᵥ p i = p i) :
    loopAct L (loopShift α p z) = loopShift α p z := by
  funext s μ
  simp only [loopAct, Matrix.mulVec, dotProduct, loopShift_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := congrFun (hp i) μ
  simp only [Matrix.mulVec, dotProduct] at h
  rw [← h, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ν _ => by ring

theorem loopAct_neg (L : Matrix (Fin 4) (Fin 4) ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    loopAct L (-ℓ) = -loopAct L ℓ := by
  funext s
  simp [loopAct, Matrix.mulVec_neg]

/-- **Invariance of the parametric integrand**: if `L` preserves the Minkowski form and fixes
every external line momentum, substituting `ℓ ↦ L ℓ` in the numerator does not change the
integrand. -/
theorem paramIntegrand_lmap_blockL {L : Matrix (Fin 4) (Fin 4) ℝ}
    (hL : ∀ μ ν, ∑ a, ∑ b, L μ a * L ν b * Minkowski.metric a b = Minkowski.metric μ ν)
    (Q : LoopQuartic) {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (hp : ∀ i, L *ᵥ p i = p i) (M : Fin (m + 1) → ℝ) (ε : ℝ) (x : Fin m → ℝ) :
    ClassLimit.paramIntegrand (lmap (blockL L) Q) α p M ε x =
      ClassLimit.paramIntegrand Q α p M ε x := by
  have hX : actC (blockL L) (loopComp (-loopShift α p (simplexPoint x))) =
      loopComp (-loopShift α p (simplexPoint x)) := by
    rw [actC_blockL_loopComp, loopAct_neg, loopAct_loopShift α p _ hp]
  have h1 : (lmap (blockL L) Q).eval (-loopShift α p (simplexPoint x)) =
      Q.eval (-loopShift α p (simplexPoint x)) := by
    rw [LoopQuartic.eval, evalC_lmap, hX]
    rfl
  have h2 : (lmap (blockL L) Q).contractTwo (symanzikMatrix α (simplexPoint x))
      (loopComp (-loopShift α p (simplexPoint x))) =
      Q.contractTwo (symanzikMatrix α (simplexPoint x))
        (loopComp (-loopShift α p (simplexPoint x))) := by
    rw [contractTwo_lmap _ _ (symanzikMatrix_transpose _ _), hX, blockL_conj_loopMetricInv hL]
    rfl
  have h3 : (lmap (blockL L) Q).contractFour (symanzikMatrix α (simplexPoint x)) =
      Q.contractFour (symanzikMatrix α (simplexPoint x)) := by
    rw [contractFour_lmap, blockL_conj_loopMetricInv hL]
    rfl
  simp only [ClassLimit.paramIntegrand, h1, h2, h3]

end Block

/-! ### Parametric values -/

open MeasureTheory Filter Topology
open scoped Real

/-- Two-loop parametric data satisfying the hypotheses of
`QED.TwoLoop.ClassLimit.tendsto_jointEnergyFirstIntegral_of_refined`, except the numerator
bound. -/
structure ParamData where
  /-- The number of lines minus one. -/
  m : ℕ
  /-- The loop matrix. -/
  α : Fin (m + 1) → Fin 2 → ℝ
  /-- The external line momenta. -/
  p : Fin (m + 1) → Fin 4 → ℝ
  /-- The masses. -/
  M : Fin (m + 1) → ℝ
  /-- The numerator lines. -/
  E : Finset (Fin (m + 1))
  hm : 7 ≤ m
  hcrit : NoSubdivergenceRefined 2 E α
  /-- A positive lower bound for `V`. -/
  c : ℝ
  hc : 0 < c
  hV : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → symanzikU α z ≠ 0 →
    c ≤ symanzikV α p M z

/-- `v` is the parametric value at `ε = 0` of the numerator `F`: `F` is the value of a quartic
`Q`, satisfies the refined bound, and `v = -π⁴ ∫_Δ paramIntegrand Q … 0`. -/
def IsParamValue (D : ParamData) (F : (Fin 2 → Fin 4 → ℝ) → ℂ) (v : ℂ) : Prop :=
  ∃ Q : LoopQuartic, Q.eval = F ∧ RefinedBound D.α D.E 4 F ∧
    v = -((π : ℂ) ^ 4) * ∫ x in simplexSet D.m, ClassLimit.paramIntegrand Q D.α D.p D.M 0 x

namespace IsParamValue

variable {D : ParamData}

theorem tendsto {F : (Fin 2 → Fin 4 → ℝ) → ℂ} {v : ℂ} (h : IsParamValue D F v) :
    Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => F ℓ * ∏ i, (lineDenom D.α D.p D.M ε i ℓ)⁻¹)) (𝓝[>] 0) (𝓝 v) := by
  obtain ⟨Q, rfl, hB, rfl⟩ := h
  exact ClassLimit.tendsto_jointEnergyFirstIntegral_of_refined Q D.α D.p D.M D.hm D.hcrit hB
    D.hc D.hV

/-- The parametric value depends only on the numerator. -/
theorem unique {F : (Fin 2 → Fin 4 → ℝ) → ℂ} {v w : ℂ} (hv : IsParamValue D F v)
    (hw : IsParamValue D F w) : v = w :=
  tendsto_nhds_unique hv.tendsto hw.tendsto

theorem integrableOn {Q : LoopQuartic} (hB : RefinedBound D.α D.E 4 Q.eval) :
    IntegrableOn (ClassLimit.paramIntegrand Q D.α D.p D.M 0) (simplexSet D.m) :=
  ClassLimit.integrableOn_paramIntegrand_zero Q D.α D.p D.M D.hm D.hcrit hB D.hc D.hV

/-- **Linearity.** -/
theorem sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) {F : ι → (Fin 2 → Fin 4 → ℝ) → ℂ}
    {v : ι → ℂ} (h : ∀ k ∈ s, IsParamValue D (F k) (v k)) :
    IsParamValue D (fun ℓ => ∑ k ∈ s, c k * F k ℓ) (∑ k ∈ s, c k * v k) := by
  classical
  have : Inhabited LoopQuartic := ⟨⟨0, 0, 0, 0, 0⟩⟩
  choose! Q hQ hB hv using h
  refine ⟨qsum s c Q, ?_, ?_, ?_⟩
  · funext ℓ
    rw [eval_qsum]
    exact Finset.sum_congr rfl fun k hk => by rw [hQ k hk]
  · exact RefinedBound.sum s fun k hk => (hB k hk).const_mul (c k)
  · have hI : ∀ k ∈ s, IntegrableOn (ClassLimit.paramIntegrand (Q k) D.α D.p D.M 0)
        (simplexSet D.m) := fun k hk => integrableOn (by rw [hQ k hk]; exact hB k hk)
    simp only [paramIntegrand_qsum]
    rw [integral_finsetSum _ fun k hk => (hI k hk).const_mul (c k), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hv k hk, integral_const_mul]
    ring

/-- **Invariance**: if `L` has a spinor lift and fixes every external line momentum, the
numerators `F` and `ℓ ↦ F(L ℓ)` have the same parametric value. -/
theorem eq_of_loopAct {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}
    (hL : IsSpinLift L S T) (hp : ∀ i, L *ᵥ D.p i = D.p i) {F G : (Fin 2 → Fin 4 → ℝ) → ℂ}
    {v w : ℂ} (hv : IsParamValue D F v) (hw : IsParamValue D G w)
    (hFG : ∀ ℓ, G ℓ = F (loopAct L ℓ)) : v = w := by
  obtain ⟨Q, hQ, -, rfl⟩ := hv
  obtain ⟨Q', hQ', hB', rfl⟩ := hw
  have h' : IsParamValue D G (-((π : ℂ) ^ 4) * ∫ x in simplexSet D.m,
      ClassLimit.paramIntegrand (lmap (blockL L) Q) D.α D.p D.M 0 x) :=
    ⟨lmap (blockL L) Q, funext fun ℓ => by rw [eval_lmap_blockL, hQ, hFG], hB', rfl⟩
  rw [unique ⟨Q', hQ', hB', rfl⟩ h']
  congr 2
  funext x
  exact (paramIntegrand_lmap_blockL hL.lorentz_left Q D.α D.p hp D.M 0 x).symm

end IsParamValue

end QED.TwoLoop.LimitCovariance

end
