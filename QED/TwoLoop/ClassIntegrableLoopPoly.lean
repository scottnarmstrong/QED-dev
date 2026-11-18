/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ParametricBridge
public import QED.Integration.TwoLoopNumeratorQuartic

/-!
# Polynomials of degree at most four in the loop momenta as `LoopQuartic`

Part of obligation O2-7 (`docs/TWO-LOOP-DERIVATION.md`, section 4.3). The bridge
(`QED/TwoLoop/ParametricBridge*.lean`) proves that the class numerators are polynomials of total
degree at most four in the loop momenta (`QED.TwoLoop.Bridge.IsLoopPoly 2 4`, via
`MvPolynomial`), while the parametric representation
(`QED/Integration/TwoLoopNumeratorQuarticFull.lean`) takes numerators as coefficient arrays
(`QED.Integration.TwoLoop.LoopQuartic`). This file converts the first into the second:
`QED.TwoLoop.Bridge.IsLoopPoly.exists_loopQuartic` gives, for every polynomial of total degree at
most four, a `LoopQuartic` with the same values.

The proof writes each monomial `∏ᵢ Xᵢ^{dᵢ}` of degree at most four as the product over the list
`d.toMultiset.toList` of its variables (`LoopQuartic.ofList`), and sums with the coefficients
(`LoopQuartic.add`, `LoopQuartic.smul`).
-/

@[expose] public section

open Complex

namespace QED.Integration.TwoLoop.LoopQuartic

/-- The sum of two numerators. -/
def add (P Q : LoopQuartic) : LoopQuartic :=
  ⟨P.const + Q.const, P.lin + Q.lin, P.quad + Q.quad, P.cub + Q.cub, P.quart + Q.quart⟩

/-- A constant multiple of a numerator. -/
def smul (c : ℂ) (P : LoopQuartic) : LoopQuartic :=
  ⟨c * P.const, fun a => c * P.lin a, fun a b => c * P.quad a b, fun a b d => c * P.cub a b d,
    fun a b d e => c * P.quart a b d e⟩

/-- The zero numerator. -/
def zero : LoopQuartic := ⟨0, 0, 0, 0, 0⟩

theorem evalC_add (P Q : LoopQuartic) (X : LoopIndex → ℂ) :
    (P.add Q).evalC X = P.evalC X + Q.evalC X := by
  simp only [evalC, add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem evalC_smul (c : ℂ) (P : LoopQuartic) (X : LoopIndex → ℂ) :
    (smul c P).evalC X = c * P.evalC X := by
  simp only [evalC, smul, mul_add, Finset.mul_sum, mul_assoc]

theorem evalC_zero (X : LoopIndex → ℂ) : zero.evalC X = 0 := by
  simp [evalC, zero]

/-- The monomial `∏_{a ∈ l} X_a` of a list of at most four variables. -/
def ofList : List LoopIndex → LoopQuartic
  | [] => ⟨1, 0, 0, 0, 0⟩
  | [a] => ⟨0, fun x => if x = a then 1 else 0, 0, 0, 0⟩
  | [a, b] => ⟨0, 0, fun x y => if x = a then (if y = b then 1 else 0) else 0, 0, 0⟩
  | [a, b, c] => ⟨0, 0, 0, fun x y z =>
      if x = a then (if y = b then (if z = c then 1 else 0) else 0) else 0, 0⟩
  | [a, b, c, d] => ⟨0, 0, 0, 0, fun x y z w =>
      if x = a then (if y = b then (if z = c then (if w = d then 1 else 0) else 0) else 0)
        else 0⟩
  | _ => zero

theorem evalC_ofList (l : List LoopIndex) (hl : l.length ≤ 4) (X : LoopIndex → ℂ) :
    (ofList l).evalC X = (l.map X).prod := by
  match l, hl with
  | [], _ => simp [ofList, evalC]
  | [a], _ => simp [ofList, evalC]
  | [a, b], _ => simp [ofList, evalC]
  | [a, b, c], _ => simp [ofList, evalC, mul_assoc]
  | [a, b, c, d], _ => simp [ofList, evalC, mul_assoc]

end QED.Integration.TwoLoop.LoopQuartic

namespace QED.TwoLoop.Bridge

open QED.Integration.TwoLoop

/-- The value of a monomial as a product over the list of its variables. -/
theorem prod_map_toList_toMultiset (d : LoopIndex →₀ ℕ) (X : LoopIndex → ℂ) :
    (d.toMultiset.toList.map X).prod = ∏ i ∈ d.support, X i ^ d i := by
  rw [Multiset.prod_map_toList, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  rfl

/-- **A polynomial of total degree at most four in the loop momenta is a `LoopQuartic`.** -/
theorem IsLoopPoly.exists_loopQuartic {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (h : IsLoopPoly 2 4 F) :
    ∃ P : LoopQuartic, P.eval = F := by
  classical
  obtain ⟨Q, hQ, hF⟩ := h
  have key : ∀ s : Finset (LoopIndex →₀ ℕ), s ⊆ Q.support → ∃ P : LoopQuartic, ∀ X,
      P.evalC X = ∑ d ∈ s, Q.coeff d * ∏ i ∈ d.support, X i ^ d i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨LoopQuartic.zero, fun X => by simp [LoopQuartic.evalC_zero]⟩
    | insert d s hd ih =>
      intro hs
      obtain ⟨P, hP⟩ := ih ((Finset.subset_insert d s).trans hs)
      have hdeg : d.toMultiset.toList.length ≤ 4 := by
        rw [Multiset.length_toList, Finsupp.card_toMultiset]
        exact (MvPolynomial.le_totalDegree (hs (Finset.mem_insert_self d s))).trans hQ
      refine ⟨(LoopQuartic.smul (Q.coeff d) (LoopQuartic.ofList d.toMultiset.toList)).add P,
        fun X => ?_⟩
      rw [LoopQuartic.evalC_add, LoopQuartic.evalC_smul, LoopQuartic.evalC_ofList _ hdeg,
        prod_map_toList_toMultiset, hP, Finset.sum_insert hd]
  obtain ⟨P, hP⟩ := key Q.support subset_rfl
  refine ⟨P, funext fun ℓ => ?_⟩
  rw [hF ℓ, MvPolynomial.eval_eq, LoopQuartic.eval, hP]
  rfl

end QED.TwoLoop.Bridge

end
