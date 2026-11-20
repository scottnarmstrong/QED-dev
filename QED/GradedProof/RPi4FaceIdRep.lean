/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4CubicDeg

/-!
# (R-Π₄) step L6d3: quadratic representatives

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. The vertex face of
a six-line piece (`faceId_faceIdVal_vtx_six`) asks for a representative of its numerator without
cubic and quartic part. The numerators of these pieces, `Num X - Num M`, have total degree at
most two; this file gives such representatives with the degree bound along a loop
(the quadratic analogue of `exists_loopQuartic_cubic_deg`).

* `faceId_cub_ofList`: monomials of at most two variables have no cubic part;
* **`faceId_exists_loopQuartic_quad_deg`**: a polynomial of total degree `≤ 2` and degree `≤ d`
  along loop `s` is a `LoopQuartic` with `cub = 0`, `quart = 0` and `LoopDegLe s d`.
-/

@[expose] public section

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.Bridge QED.GradedProof.VP2

/-- Monomials of at most two variables have no cubic part. -/
theorem faceId_cub_ofList (l : List LoopIndex) (hl : l.length ≤ 2) :
    (LoopQuartic.ofList l).cub = 0 := by
  match l, hl with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | _ :: _ :: _ :: _, h => simp at h

/-- **A polynomial of total degree `≤ 2` and degree `≤ d` along loop `s`** is a `LoopQuartic`
without cubic and quartic part whose coefficients with more than `d` indices in loop `s`
vanish. -/
theorem faceId_exists_loopQuartic_quad_deg {s : Fin 2} {d : ℕ}
    {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (h : IsLoopPolyDeg s d 2 F) :
    ∃ P : LoopQuartic, P.cub = 0 ∧ P.quart = 0 ∧ LoopDegLe s d P ∧ P.eval = F := by
  classical
  obtain ⟨Q, hQ, hsQ, hF⟩ := h
  have key : ∀ t : Finset (LoopIndex →₀ ℕ), t ⊆ Q.support → ∃ P : LoopQuartic,
      P.cub = 0 ∧ P.quart = 0 ∧ LoopDegLe s d P ∧
        ∀ X, P.evalC X = ∑ x ∈ t, Q.coeff x * ∏ i ∈ x.support, X i ^ x i := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      exact fun _ => ⟨LoopQuartic.zero, rfl, rfl, LoopDegLe.zero, fun X => by
        simp [LoopQuartic.evalC_zero]⟩
    | insert x t hx ih =>
      intro ht
      obtain ⟨P, hPc, hPq, hPd, hP⟩ := ih ((Finset.subset_insert x t).trans ht)
      have hxQ : x ∈ Q.support := ht (Finset.mem_insert_self x t)
      have hdeg : x.toMultiset.toList.length ≤ 2 := by
        rw [Multiset.length_toList, Finsupp.card_toMultiset]
        exact (MvPolynomial.le_totalDegree hxQ).trans hQ
      refine ⟨(LoopQuartic.smul (Q.coeff x) (LoopQuartic.ofList x.toMultiset.toList)).add P,
        ?_, ?_, ((LoopDegLe.ofList _ ?_).smul _).add hPd, fun X => ?_⟩
      · have h0 := faceId_cub_ofList _ hdeg
        simp only [LoopQuartic.add, LoopQuartic.smul, h0, hPc, Pi.zero_apply, mul_zero]
        funext a b c
        simp
      · have h0 := LoopQuartic.quart_ofList x.toMultiset.toList (by omega)
        simp only [LoopQuartic.add, LoopQuartic.smul, h0, hPq, Pi.zero_apply, mul_zero]
        funext a b c e
        simp
      · rw [sum_map_loopInd_toList]
        exact hsQ x hxQ
      rw [LoopQuartic.evalC_add, LoopQuartic.evalC_smul,
        LoopQuartic.evalC_ofList _ (by omega), prod_map_toList_toMultiset, hP,
        Finset.sum_insert hx]
  obtain ⟨P, hPc, hPq, hPd, hP⟩ := key Q.support subset_rfl
  refine ⟨P, hPc, hPq, hPd, funext fun ℓ => ?_⟩
  rw [hF ℓ, MvPolynomial.eval_eq, LoopQuartic.eval, hP]
  rfl

end QED.GradedProof.RPi4

end
