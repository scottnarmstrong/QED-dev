/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4CubicDeg
public import QED.GradedProof.RPi4FaceIdLapF

/-!
# (R-Π₄) step L6d3: the half Laplacian of a quadratic numerator is constant

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. The vertex
faces of the six-line pieces (`faceId_face1_vtx_three`, `faceId_face0_vtx_three`) need the half
Laplacian of the numerator on the slice to be a constant. The numerators of those pieces are
polynomials of total degree `≤ 2` in the loop momenta (`C (Num X - Num M)` is a multiple of
`E₂ + const`, the padded numerator a propagator denominator), and the half Laplacian of such a
polynomial along either loop is a constant.

* `faceId_exists_quadQ`: a polynomial of total degree `≤ 2` is a `LoopQuartic` without cubic
  and quartic parts;
* **`faceId_lapF_const`**: its half Laplacian along loop `s` is constant.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.Bridge QED.GradedProof.VP2

theorem faceId_cub_ofList_two (l : List LoopIndex) (hl : l.length ≤ 2) :
    (LoopQuartic.ofList l).cub = 0 := by
  match l, hl with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl

/-- **A polynomial of total degree `≤ 2`** is a `LoopQuartic` without cubic and quartic parts. -/
theorem faceId_exists_quadQ {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (h : IsLoopPoly 2 2 F) :
    ∃ P : LoopQuartic, P.cub = 0 ∧ P.quart = 0 ∧ P.eval = F := by
  classical
  obtain ⟨Q, hQ, hF⟩ := h
  have key : ∀ t : Finset (LoopIndex →₀ ℕ), t ⊆ Q.support → ∃ P : LoopQuartic,
      P.cub = 0 ∧ P.quart = 0 ∧
        ∀ X, P.evalC X = ∑ x ∈ t, Q.coeff x * ∏ i ∈ x.support, X i ^ x i := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      exact fun _ => ⟨LoopQuartic.zero, rfl, rfl, fun X => by
        simp [LoopQuartic.evalC_zero]⟩
    | insert x t hx ih =>
      intro ht
      obtain ⟨P, hPc, hPq, hP⟩ := ih ((Finset.subset_insert x t).trans ht)
      have hxQ : x ∈ Q.support := ht (Finset.mem_insert_self x t)
      have hdeg : x.toMultiset.toList.length ≤ 2 := by
        rw [Multiset.length_toList, Finsupp.card_toMultiset]
        exact (MvPolynomial.le_totalDegree hxQ).trans hQ
      refine ⟨(LoopQuartic.smul (Q.coeff x) (LoopQuartic.ofList x.toMultiset.toList)).add P,
        ?_, ?_, fun X => ?_⟩
      · have h0 := faceId_cub_ofList_two _ hdeg
        simp only [LoopQuartic.add, LoopQuartic.smul, h0, hPc, Pi.zero_apply, mul_zero]
        funext a b c
        simp
      · have h0 := LoopQuartic.quart_ofList x.toMultiset.toList (by omega)
        simp only [LoopQuartic.add, LoopQuartic.smul, h0, hPq, Pi.zero_apply, mul_zero]
        funext a b c e
        simp
      rw [LoopQuartic.evalC_add, LoopQuartic.evalC_smul,
        LoopQuartic.evalC_ofList _ (by omega), prod_map_toList_toMultiset, hP,
        Finset.sum_insert hx]
  obtain ⟨P, hPc, hPq, hP⟩ := key Q.support subset_rfl
  refine ⟨P, hPc, hPq, funext fun ℓ => ?_⟩
  rw [hF ℓ, MvPolynomial.eval_eq, LoopQuartic.eval, hP]
  rfl

theorem faceId_loopDegLe_quadQ {P : LoopQuartic} (hc : P.cub = 0) (hq : P.quart = 0)
    (s : Fin 2) : LoopDegLe s 2 P where
  lin a ha := absurd ha (by have := loopInd_le_one s a; omega)
  quad a b ha := absurd ha (by have := loopInd_le_one s a; have := loopInd_le_one s b; omega)
  cub a b c _ := by rw [hc]; rfl
  quart a b c d _ := by rw [hq]; rfl

theorem faceId_eval_faceIdLap_quad {P : LoopQuartic} (hc : P.cub = 0) (hq : P.quart = 0)
    (ℓ : Fin 2 → Fin 4 → ℝ) : (faceIdLap P).eval ℓ = (faceIdLap P).const := by
  simp [LoopQuartic.eval, LoopQuartic.evalC, faceIdLap, hc, hq, LoopQuartic.quartSym]

/-- **The half Laplacian of a polynomial of total degree `≤ 2` is constant** along either
loop. -/
theorem faceId_lapF_const {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (h : IsLoopPoly 2 2 F) (s : Fin 2) :
    ∃ C : ℂ, ∀ ℓ, faceIdLapF s F ℓ = C := by
  obtain ⟨P, hc, hq, rfl⟩ := faceId_exists_quadQ h
  fin_cases s
  · have hc' : (swapQ P).cub = 0 := by
      funext a b c; simp only [swapQ, hc]; rfl
    have hq' : (swapQ P).quart = 0 := by
      funext a b c d; simp only [swapQ, hq]; rfl
    refine ⟨(faceIdLap (swapQ P)).const, fun ℓ => ?_⟩
    have e := faceId_eval_faceIdLap_swapQ (faceId_loopDegLe_quadQ hc hq 0) (ℓ ∘ lsw)
    have hl : ℓ ∘ lsw ∘ lsw = ℓ := by
      funext i; fin_cases i <;> rfl
    rw [Function.comp_assoc, hl, faceId_eval_faceIdLap_quad hc' hq'] at e
    exact e.symm
  · refine ⟨(faceIdLap P).const, fun ℓ => ?_⟩
    change faceIdLapF 1 P.eval ℓ = _
    rw [← faceId_eval_faceIdLap (faceId_loopDegLe_quadQ hc hq 1),
      faceId_eval_faceIdLap_quad hc hq]
