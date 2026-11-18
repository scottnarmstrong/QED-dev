/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ParametricBridge

/-!
# Polynomials in the loop momenta under affine substitutions

Part of obligations O2-7 and O2-10 (`docs/TWO-LOOP-DERIVATION.md`, sections 4.1–4.4). The bridge
(`QED/TwoLoop/ParametricBridge*.lean`) proves the numerator degree bounds in the class loop
momenta. The frozen routing (T₄) uses other loop momenta, related to the class ones by an integer
unimodular affine change `ℓ ↦ M ℓ + a` (`QED.TwoLoop.Bridge.chgL`, …). This file transports the
degree bounds.

* `QED.TwoLoop.Bridge.IsLoopPoly.pow`: powers.
* `QED.TwoLoop.Bridge.IsLoopPoly.comp`: **substitution**. If `F` is a polynomial of total degree
  at most `n` in the loop momenta and every coordinate of `g(ℓ')` is a polynomial of total degree
  at most one in other loop momenta `ℓ'`, then `F ∘ g` has total degree at most `n`.
* `QED.TwoLoop.Bridge.IsLoopPoly.comp_affine`: the case `g(ℓ')ₛ = ∑ᵣ Mₛᵣ ℓ'ᵣ + aₛ` with a real
  matrix `M`; `IsLoopPoly.comp_intAffine` for an integer matrix (the form of the routing changes
  and of `QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add`).
* `QED.TwoLoop.Bridge.isLoopPoly_comp_intAffine_iff`: for `M` integer unimodular the degree bound
  holds in one set of loop momenta if and only if it holds in the other.
-/

public section

open QED.TwoLoop.Bridge

namespace QED.TwoLoop.Bridge

namespace IsLoopPoly

variable {L L' n k : ℕ} {F : (Fin L → Fin 4 → ℝ) → ℂ}

theorem pow (hF : IsLoopPoly L k F) (e : ℕ) : IsLoopPoly L (k * e) fun ℓ => F ℓ ^ e := by
  induction e with
  | zero => simpa using const (L := L) (n := 0) 1
  | succ e ih =>
    simpa [pow_succ, Nat.mul_succ] using ih.mul hF

/-- **Substitution.** A polynomial of total degree at most `n` in the loop momenta, composed with
a map whose coordinates are polynomials of total degree at most one, has total degree at most
`n`. -/
theorem comp (hF : IsLoopPoly L n F) {g : (Fin L' → Fin 4 → ℝ) → Fin L → Fin 4 → ℝ}
    (hg : ∀ s ν, IsLoopPoly L' 1 fun ℓ' => ((g ℓ' s ν : ℝ) : ℂ)) :
    IsLoopPoly L' n fun ℓ' => F (g ℓ') := by
  classical
  obtain ⟨Q, hQ, hFQ⟩ := hF
  have h : (fun ℓ' => F (g ℓ')) = fun ℓ' => ∑ d ∈ Q.support, Q.coeff d *
      ∏ x ∈ d.support, ((g ℓ' x.1 x.2 : ℝ) : ℂ) ^ d x := by
    funext ℓ'
    rw [hFQ, MvPolynomial.eval_eq]
  rw [h]
  refine sum _ fun d hd => ?_
  refine const_mul _ (mono ?_ ((MvPolynomial.le_totalDegree hd).trans hQ))
  have hp := prod (L := L') d.support (fun x => 1 * d x)
    (F := fun x ℓ' => ((g ℓ' x.1 x.2 : ℝ) : ℂ) ^ d x) fun x _ => (hg x.1 x.2).pow (d x)
  simpa [Finsupp.sum] using hp

/-- Substitution of a real affine map of the loop momenta. -/
theorem comp_affine (hF : IsLoopPoly L n F) (M : Fin L → Fin L' → ℝ) (a : Fin L → Fin 4 → ℝ) :
    IsLoopPoly L' n fun ℓ' => F ((fun s => ∑ r, M s r • ℓ' r) + a) := by
  refine hF.comp fun s ν => ?_
  have h : (fun ℓ' : Fin L' → Fin 4 → ℝ => ((((fun s => ∑ r, M s r • ℓ' r) + a) s ν : ℝ) : ℂ)) =
      fun ℓ' => (∑ r ∈ Finset.univ, (M s r : ℂ) * ((ℓ' r ν : ℝ) : ℂ)) + (a s ν : ℂ) := by
    funext ℓ'
    simp [Finset.sum_apply]
  rw [h]
  exact (sum _ fun r _ => (coord r ν le_rfl).const_mul _).add (const _)

/-- **Substitution of an integer affine map** `ℓ' ↦ M ℓ' + a`, the form of the changes of loop
momenta between routings. -/
theorem comp_intAffine (hF : IsLoopPoly L n F) (M : Matrix (Fin L) (Fin L') ℤ)
    (a : Fin L → Fin 4 → ℝ) :
    IsLoopPoly L' n fun ℓ' => F ((fun s => ∑ r, M s r • ℓ' r) + a) := by
  have h := hF.comp_affine (fun s r => (M s r : ℝ)) a
  have e : ∀ ℓ' : Fin L' → Fin 4 → ℝ,
      ((fun s => ∑ r, M s r • ℓ' r) + a) = ((fun s => ∑ r, (M s r : ℝ) • ℓ' r) + a) := by
    intro ℓ'
    funext s
    simp [Int.cast_smul_eq_zsmul]
  simpa only [e] using h

end IsLoopPoly

/-- For an integer matrix `M` with `IsUnit M.det`, the degree bound holds in the loop momenta
`ℓ` if and only if it holds after the change `ℓ ↦ M ℓ + a`. -/
theorem isLoopPoly_comp_intAffine_iff {L n : ℕ} {F : (Fin L → Fin 4 → ℝ) → ℂ}
    (M : Matrix (Fin L) (Fin L) ℤ) (hM : IsUnit M.det) (a : Fin L → Fin 4 → ℝ) :
    IsLoopPoly L n (fun ℓ => F ((fun s => ∑ r, M s r • ℓ r) + a)) ↔ IsLoopPoly L n F := by
  refine ⟨fun h => ?_, fun h => h.comp_intAffine M a⟩
  -- the inverse change `ℓ ↦ M⁻¹ (ℓ - a)`, with `M⁻¹` integer
  set N : Matrix (Fin L) (Fin L) ℤ := M⁻¹
  have hMN : M * N = 1 := Matrix.mul_nonsing_inv M hM
  have hc : ∀ s t : Fin L, ∑ r, (M s r : ℝ) * (N r t : ℝ) = if s = t then 1 else 0 := fun s t => by
    have := congrArg (fun z : ℤ => (z : ℝ)) (congrFun (congrFun hMN s) t)
    simpa [Matrix.mul_apply, Matrix.one_apply, apply_ite (fun z : ℤ => (z : ℝ))] using this
  have key : ∀ v : Fin L → Fin 4 → ℝ,
      (fun s => ∑ r, M s r • (fun s => ∑ t, N s t • v t) r) = v := by
    intro v
    funext s μ
    simp only [Finset.sum_apply, Pi.smul_apply]
    simp only [zsmul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul, hc]
    simp
  have h' := h.comp_intAffine N (fun s => -∑ r, N s r • a r)
  refine (congrArg (IsLoopPoly L n) (funext fun ℓ => congrArg F ?_)).mp h'
  have lin : (fun s => ∑ r, N s r • ℓ r) + (fun s => -∑ r, N s r • a r) =
      fun s => ∑ t, N s t • (ℓ - a) t := by
    funext s
    simp only [Pi.add_apply, Pi.sub_apply, smul_add, smul_neg, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [lin, key, sub_add_cancel]

end QED.TwoLoop.Bridge

end
