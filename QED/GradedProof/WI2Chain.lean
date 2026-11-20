/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2Chain4
public import QED.GradedProof.WI2Line
public import QED.TwoLoop.ClassIntegrableVP

/-!
# The open two-loop chain as a function of its three electron slots

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A6 for the classes `R` and `X`. The numerators of both are the open chain
`chain4 w E₃ E₂ E₁` (`QED.GradedProof.SE2.chain4`); here it is read as a function `chainAt w E` of
the three slots `E : Fin 3 → Matrix`, slot `j` holding the electron numerator of the `j`-th
electron line.

* `chainAt_update_add`, `chainAt_update_smul`: the chain is linear in each slot.
* `hasDerivAt_chainAt`: the product rule, the derivative being the sum over the slots of the
  chain with that slot differentiated (via the operator norm on matrices, local instance).
* `refinedBoundMat_chainAt`, `isLoopPolyMat_chainAt`: the pointwise bound and the degree, from
  those of the slots (the slots' line sets disjoint).
* `chainAt_update_ins`: an insertion `(m - k̸) q̸ (m - k̸)` in slot `j` is
  `(k·k + m²)` times the chain with `q̸` in slot `j` plus `2 q·k` times the chain itself
  (`QED.GradedProof.WI2.numerator_slash_numerator`).
-/

@[expose] public section

open Complex Matrix

namespace QED.GradedProof.WI2

open QED.GradedProof.SE2 QED.TwoLoop.ClassIntegrable QED.TwoLoop.Bridge
open QED.Integration.TwoLoop (RefinedBound)

/-- The open chain `chain4 w (E 2) (E 1) (E 0)` as a function of its three slots. -/
noncomputable def chainAt (w : (Fin 4 → Fin 4) → ℂ) (E : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  chain4 w (E 2) (E 1) (E 0)

variable (w : (Fin 4 → Fin 4) → ℂ)

theorem chainAt_update_add (E : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ) (j : Fin 3)
    (X Y : Matrix (Fin 4) (Fin 4) ℂ) :
    chainAt w (Function.update E j (X + Y)) =
      chainAt w (Function.update E j X) + chainAt w (Function.update E j Y) := by
  simp only [chainAt, chain4, chainG, ← Finset.sum_add_distrib, ← smul_add]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  fin_cases j <;> simp [Function.update, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem chainAt_update_smul (E : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ) (j : Fin 3) (c : ℂ)
    (X : Matrix (Fin 4) (Fin 4) ℂ) :
    chainAt w (Function.update E j (c • X)) = c • chainAt w (Function.update E j X) := by
  simp only [chainAt, chain4, chainG, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm, ← smul_smul]
  congr 1
  fin_cases j <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, ne_eq,
    Function.update_self, Function.update_of_ne, Fin.reduceEq, not_false_eq_true,
    Matrix.mul_smul, Matrix.smul_mul]

theorem chainAt_update_self (E : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ) (j : Fin 3) :
    chainAt w (Function.update E j (E j)) = chainAt w E := by
  rw [Function.update_eq_self]

/-- **The insertion in slot `j`**: `(m - k̸) q̸ (m - k̸)` gives `(k·k + m²)` times the chain with
`q̸` in slot `j` plus `2 q·k` times the chain with `m - k̸` there. -/
theorem chainAt_update_ins (E : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ) (j : Fin 3) (mass : ℝ)
    (k q : Fin 4 → ℝ) :
    chainAt w (Function.update E j (QED.TwoLoop.Bridge.electronNumerator mass k *
        Dirac.slash q * QED.TwoLoop.Bridge.electronNumerator mass k)) =
      ((Minkowski.dot k k + mass ^ 2 : ℝ) : ℂ) • chainAt w (Function.update E j (Dirac.slash q)) +
        ((2 * Minkowski.dot q k : ℝ) : ℂ) •
          chainAt w (Function.update E j (QED.TwoLoop.Bridge.electronNumerator mass k)) := by
  simp only [QED.TwoLoop.Bridge.electronNumerator]
  rw [numerator_slash_numerator, chainAt_update_add, chainAt_update_smul, chainAt_update_smul]


section Deriv

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- **The derivative of the chain along a line** in the momenta of its three slots. -/
theorem hasDerivAt_chainAt_line (mass : ℝ) (k q : Fin 3 → Fin 4 → ℝ) (t₀ : ℝ) (a b : Fin 4) :
    HasDerivAt (fun t : ℝ => chainAt w
        (fun j => QED.TwoLoop.Bridge.electronNumerator mass (k j + t • q j)) a b)
      (-∑ j, chainAt w (Function.update
        (fun j => QED.TwoLoop.Bridge.electronNumerator mass (k j + t₀ • q j)) j
        (Dirac.slash (q j))) a b) t₀ := by
  set E : ℝ → Fin 3 → Matrix (Fin 4) (Fin 4) ℂ :=
    fun t j => QED.TwoLoop.Bridge.electronNumerator mass (k j + t • q j)
  have h : ∀ j, HasDerivAt (fun t => E t j) (-Dirac.slash (q j)) t₀ := fun j => by
    have e : (fun t => E t j) = fun t : ℝ =>
        QED.TwoLoop.Bridge.electronNumerator mass (k j) - t • Dirac.slash (q j) := by
      funext t
      simp only [E, QED.TwoLoop.Bridge.electronNumerator, Dirac.slash_add, Dirac.slash_smul]
      rw [Complex.coe_smul]
      abel
    have h1 := ((hasDerivAt_id t₀).smul_const (Dirac.slash (q j))).const_sub
      (QED.TwoLoop.Bridge.electronNumerator mass (k j))
    rw [e]
    simp only [one_smul] at h1
    exact h1
  have hc : ∀ M : Matrix (Fin 4) (Fin 4) ℂ, HasDerivAt (fun _ : ℝ => M) 0 t₀ :=
    fun M => hasDerivAt_const _ _
  have hS := HasDerivAt.fun_sum (u := Finset.univ) fun (l : Fin 4 → Fin 4) _ =>
    (((((((hc (Dirac.gamma (l 3))).mul (h 2)).mul (hc (Dirac.gamma (l 2)))).mul (h 1)).mul
      (hc (Dirac.gamma (l 1)))).mul (h 0)).mul (hc (Dirac.gamma (l 0)))).const_smul (w l)
  have hS' : HasDerivAt (fun t => chainAt w (E t))
      (-∑ j, chainAt w (Function.update (E t₀) j (Dirac.slash (q j)))) t₀ := by
    refine (hS.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    · simp only [Fin.sum_univ_three, chainAt, chain4, chainG, ← Finset.sum_add_distrib,
        ← Finset.sum_neg_distrib, ← smul_add, ← smul_neg]
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      simp only [Function.update_self, ne_eq, Function.update_of_ne, Fin.reduceEq,
        not_false_eq_true, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Pi.mul_apply]
      noncomm_ring
    · simp only [chainAt, chain4, chainG, Pi.smul_apply, Pi.mul_apply]
  have hE := (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).hasFDerivAt
    |>.comp_hasDerivAt t₀ hS'
  exact hE

end Deriv

/-! ### Bounds and degrees -/

section Bounds

variable {m : ℕ} {al : Fin (m + 1) → Fin 2 → ℝ}

theorem refinedBoundMat_chain4 {S₃ S₂ S₁ : Finset (Fin (m + 1))} {d₃ d₂ d₁ : ℕ}
    {E₃ E₂ E₁ : (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    (h₃ : RefinedBoundMat al S₃ d₃ E₃) (h₂ : RefinedBoundMat al S₂ d₂ E₂)
    (h₁ : RefinedBoundMat al S₁ d₁ E₁) (h32 : Disjoint S₃ S₂) (h31 : Disjoint S₃ S₁)
    (h21 : Disjoint S₂ S₁) :
    RefinedBoundMat al (S₃ ∪ S₂ ∪ S₁) (d₃ + d₂ + d₁)
      fun ℓ => chain4 w (E₃ ℓ) (E₂ ℓ) (E₁ ℓ) := by
  intro a b
  simp only [chain4, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine RefinedBound.sum _ fun l _ => RefinedBound.const_mul _ ?_
  have c := fun t : Fin 4 => RefinedBoundMat.const (al := al) (Dirac.gamma (l t))
  have h := ((((((c 3).mul h₃ (Finset.disjoint_empty_left _)).mul (c 2)
    (Finset.disjoint_empty_right _)).mul h₂ (by simpa using h32)).mul (c 1)
    (Finset.disjoint_empty_right _)).mul h₁ (by simpa [Finset.disjoint_union_left] using
      ⟨h31, h21⟩)).mul (c 0) (Finset.disjoint_empty_right _)
  simp only [Finset.empty_union, Finset.union_empty, zero_add, add_zero] at h
  exact h a b

theorem isLoopPolyMat_chain4 {L d₃ d₂ d₁ : ℕ}
    {E₃ E₂ E₁ : (Fin L → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    (h₃ : IsLoopPolyMat L d₃ E₃) (h₂ : IsLoopPolyMat L d₂ E₂) (h₁ : IsLoopPolyMat L d₁ E₁) :
    IsLoopPolyMat L (d₃ + d₂ + d₁) fun ℓ => chain4 w (E₃ ℓ) (E₂ ℓ) (E₁ ℓ) := by
  intro a b
  simp only [chain4, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine IsLoopPoly.sum _ fun l _ => IsLoopPoly.const_mul _ ?_
  have c := fun t : Fin 4 => IsLoopPolyMat.const (L := L) (Dirac.gamma (l t))
  have h := ((((((c 3).mul h₃).mul (c 2)).mul h₂).mul (c 1)).mul h₁).mul (c 0)
  simp only [zero_add, add_zero] at h
  exact h a b

theorem refinedBoundMat_chainAt {F : (Fin 2 → Fin 4 → ℝ) → Fin 3 → Matrix (Fin 4) (Fin 4) ℂ}
    {S : Fin 3 → Finset (Fin (m + 1))} {d : Fin 3 → ℕ}
    (h : ∀ j, RefinedBoundMat al (S j) (d j) fun ℓ => F ℓ j)
    (hd : ∀ j₁ j₂, j₁ ≠ j₂ → Disjoint (S j₁) (S j₂)) :
    RefinedBoundMat al (S 2 ∪ S 1 ∪ S 0) (d 2 + d 1 + d 0) fun ℓ => chainAt w (F ℓ) :=
  refinedBoundMat_chain4 w (h 2) (h 1) (h 0) (hd 2 1 (by decide)) (hd 2 0 (by decide))
    (hd 1 0 (by decide))

theorem isLoopPolyMat_chainAt {L : ℕ} {F : (Fin L → Fin 4 → ℝ) → Fin 3 → Matrix (Fin 4) (Fin 4) ℂ}
    {d : Fin 3 → ℕ} (h : ∀ j, IsLoopPolyMat L (d j) fun ℓ => F ℓ j) :
    IsLoopPolyMat L (d 2 + d 1 + d 0) fun ℓ => chainAt w (F ℓ) :=
  isLoopPolyMat_chain4 w (h 2) (h 1) (h 0)

end Bounds

end QED.GradedProof.WI2

end
