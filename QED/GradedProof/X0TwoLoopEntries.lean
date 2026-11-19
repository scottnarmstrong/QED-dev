/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0TwoLoop
public import QED.Integration.SymanzikIntegrabilityRefinedClasses

/-!
# (X₀): (T₉′) at two loops for a product of affine entries over parametric lines

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), part B of
`TwoLoopClosedGoal`. Let `m + 1` parametric lines carry the momenta `k_i = a_i · ℓ + q_i`
(`a_i ∈ ℤ²`) and masses `M_i`, and let `E` be a set of lines, each with an entry affine in its
line momentum. If the integer criterion `IntNoSubdivergenceRefined 2 E a` holds and either
`m ≥ 7` and `|E| ≤ 4`, or `m ≥ 6` and `|E| ≤ 3`, then
`z ∏_{i ∈ E} g_i(k_i) ∏_i D_{M_i}(k_i)⁻¹` satisfies (T₉′) at two loops, for any masses and
`ε > 0` (`jointEnergyFirstIntegrable_twoLoopEntries`): the numerator is a polynomial of degree
`|E|` bounded by the line weights of `E`, and the refined (resp. cubic) two-loop theorem
applies.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0

open QED.Integration.TwoLoop (castLoopMatrix lineDenom lineMomentum RefinedBound LoopQuartic
  refinedBound_lineMomentum IntNoSubdivergenceRefined noSubdivergenceRefined_castLoopMatrix_iff
  jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined
  jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_cubic)
open QED.TwoLoop.Bridge (IsLoopPoly isLoopAffine_lineMomentum)

/-- An affine entry at a line momentum is a polynomial of degree `1`. -/
theorem isLoopPoly_affEntry {m : ℕ} (al : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (i : Fin (m + 1)) (u : ℂ) (w : Fin 4 → ℂ) :
    IsLoopPoly 2 1 fun ℓ => u + ∑ ν, w ν * ((lineMomentum al p i ℓ ν : ℝ) : ℂ) :=
  (IsLoopPoly.const u).add (IsLoopPoly.sum _ fun ν _ =>
    ((isLoopAffine_lineMomentum al p i).isLoopPoly_coord ν).const_mul (w ν))

/-- An affine entry at a line momentum is bounded by that line. -/
theorem refinedBound_affEntry {m : ℕ} (al : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (i : Fin (m + 1)) (u : ℂ) (w : Fin 4 → ℂ) :
    RefinedBound al {i} 1 fun ℓ => u + ∑ ν, w ν * ((lineMomentum al p i ℓ ν : ℝ) : ℂ) :=
  ((RefinedBound.const u).mono (Finset.empty_subset _) (Nat.zero_le _)).add
    (RefinedBound.sum _ fun ν _ => (refinedBound_lineMomentum al p i ν).const_mul (w ν))

/-- **(T₉′) at two loops for a product of affine entries.** -/
theorem jointEnergyFirstIntegrable_twoLoopEntries {m : ℕ} (a : Fin (m + 1) → Fin 2 → ℤ)
    (q : Fin (m + 1) → Fin 4 → ℝ) (Ms : Fin (m + 1) → ℝ) {ε : ℝ} (hε : 0 < ε)
    (E : Finset (Fin (m + 1))) (u : Fin (m + 1) → ℂ) (w : Fin (m + 1) → Fin 4 → ℂ)
    (hcrit : IntNoSubdivergenceRefined 2 E a)
    (hsize : (7 ≤ m ∧ E.card ≤ 4) ∨ (6 ≤ m ∧ E.card ≤ 3)) (z : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      z * (∏ i ∈ E, (u i + ∑ ν, w i ν *
        ((lineMomentum (castLoopMatrix a) q i ℓ ν : ℝ) : ℂ))) *
        ∏ i, (lineDenom (castLoopMatrix a) q Ms ε i ℓ)⁻¹ := by
  classical
  set N : (Fin 2 → Fin 4 → ℝ) → ℂ := fun ℓ => z * ∏ i ∈ E, (u i + ∑ ν, w i ν *
    ((lineMomentum (castLoopMatrix a) q i ℓ ν : ℝ) : ℂ)) with hN
  have hpoly : IsLoopPoly 2 E.card N := by
    have h := IsLoopPoly.prod (L := 2) E (fun _ => 1)
      (F := fun i ℓ => u i + ∑ ν, w i ν * ((lineMomentum (castLoopMatrix a) q i ℓ ν : ℝ) : ℂ))
      fun i _ => isLoopPoly_affEntry _ _ i (u i) (w i)
    have hc : (∑ _i ∈ E, 1) = E.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    rw [hc] at h
    exact h.const_mul z
  have hB : RefinedBound (castLoopMatrix a) E E.card N := by
    have h := RefinedBound.prod (α := castLoopMatrix a) E id (Set.injOn_id _)
      (g := fun i ℓ => u i + ∑ ν, w i ν * ((lineMomentum (castLoopMatrix a) q i ℓ ν : ℝ) : ℂ))
      fun i _ => refinedBound_affEntry _ _ i (u i) (w i)
    rw [Finset.image_id] at h
    exact h.const_mul z
  have hcr := (noSubdivergenceRefined_castLoopMatrix_iff 2 E a).mpr hcrit
  have hfun : (fun ℓ => z * (∏ i ∈ E, (u i + ∑ ν, w i ν *
      ((lineMomentum (castLoopMatrix a) q i ℓ ν : ℝ) : ℂ))) *
      ∏ i, (lineDenom (castLoopMatrix a) q Ms ε i ℓ)⁻¹) =
      fun ℓ => N ℓ * ∏ i, (lineDenom (castLoopMatrix a) q Ms ε i ℓ)⁻¹ := rfl
  rw [hfun]
  rcases hsize with ⟨hm, hd⟩ | ⟨hm, hd⟩
  · obtain ⟨Q, hQ⟩ := (hpoly.mono hd).exists_loopQuartic
    rw [← hQ] at hB
    have h := jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined
      Q _ q Ms hm hε hcr (hB.mono le_rfl hd)
    rw [hQ] at h
    exact h
  · obtain ⟨Q, hq, hQ⟩ := QED.GradedProof.SE2.IsLoopPoly.exists_loopQuartic_cubic (hpoly.mono hd)
    rw [← hQ] at hB
    have h := jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_cubic
      Q _ q Ms hq hm hε hcr (hB.mono le_rfl (by omega))
    rw [hQ] at h
    exact h

end QED.GradedProof.X0

end
