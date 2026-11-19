/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0OneLoop

/-!
# (X₀): (T₉′) at one loop for a product of propagator entries

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57). Let fermion lines
`f ∈ F` carry `c_f ℓ + p_f` and photon lines `g ∈ G` carry `c_g ℓ + p_g`, with nonzero `c`. If
`|F| ≤ 3` and `4 < |F| + 4|G|`, the product of the entries `(1/i) S̃_{a b}` and `(1/i) Δ̃_{μν}`
satisfies (T₉′) with one loop momentum, for `ε > 0` and any masses and photon regulators
(`jointEnergyFirstIntegrable_entries`): the electron numerator is affine in the momentum and the
Pauli–Villars photon has two denominators, so `jointEnergyFirstIntegrable_oneLoop` applies with
the parametric lines `F ⊕ G × Fin 2` and numerator lines `F`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0

open QED.TwoLoop.Bridge (propDenom electronNumerator electronNumerator_apply
  electronPropagator_apply photonPropagator_eq_mul)

/-- `jointEnergyFirstIntegrable_oneLoop` with the lines indexed by any finite type. -/
theorem jointEnergyFirstIntegrable_oneLoop' {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℝ) (hc : ∀ i, c i ≠ 0) (q : ι → Fin 4 → ℝ) (Ms : ι → ℝ) {ε : ℝ} (hε : 0 < ε)
    (E : Finset ι) (hE : E.card ≤ 3) (hcount : 4 + E.card < 2 * Fintype.card ι)
    (g : ι → (Fin 4 → ℝ) → ℂ)
    (hg : ∀ i ∈ E, ∃ u : ℂ, ∃ w : Fin 4 → ℂ, ∀ k, g i k = u + ∑ ν, w ν * (k ν : ℂ)) (z : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ =>
      z * (∏ i ∈ E, g i (c i • ℓ 0 + q i)) * ∏ i, (propDenom (Ms i) ε (c i • ℓ 0 + q i))⁻¹ := by
  set e := Fintype.equivFin ι
  have h := jointEnergyFirstIntegrable_oneLoop (fun i => c (e.symm i)) (fun i => hc _)
    (fun i => q (e.symm i)) (fun i => Ms (e.symm i)) hε (E.map e.toEmbedding)
    (by rwa [Finset.card_map]) (by rwa [Finset.card_map]) (fun i => g (e.symm i))
    (fun i hi => by
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      simpa using hg j hj) z
  have hfun : ∀ ℓ : Fin 1 → Fin 4 → ℝ,
      z * (∏ i ∈ E.map e.toEmbedding, g (e.symm i) (c (e.symm i) • ℓ 0 + q (e.symm i))) *
        ∏ i, (propDenom (Ms (e.symm i)) ε (c (e.symm i) • ℓ 0 + q (e.symm i)))⁻¹ =
      z * (∏ i ∈ E, g i (c i • ℓ 0 + q i)) * ∏ i, (propDenom (Ms i) ε (c i • ℓ 0 + q i))⁻¹ := by
    intro ℓ
    rw [Finset.prod_map, Equiv.prod_comp e.symm
      (fun i => (propDenom (Ms i) ε (c i • ℓ 0 + q i))⁻¹)]
    simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
  simp only [hfun] at h
  exact h

/-- An entry of `m - k̸` is affine in `k`. -/
theorem electronNumerator_affine (m : ℝ) (a b : Fin 4) :
    ∃ u : ℂ, ∃ w : Fin 4 → ℂ, ∀ k : Fin 4 → ℝ,
      electronNumerator m k a b = u + ∑ ν, w ν * (k ν : ℂ) := by
  refine ⟨if a = b then (m : ℂ) else 0,
    fun ν => -∑ μ, ((Minkowski.metric μ ν : ℝ) : ℂ) * Dirac.gamma μ a b, fun k => ?_⟩
  rw [electronNumerator_apply, Finset.sum_comm, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [neg_mul, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun μ _ => by ring

/-- **(T₉′) at one loop for a product of propagator entries.** -/
theorem jointEnergyFirstIntegrable_entries {F G : Type*} [Fintype F] [DecidableEq F]
    [Fintype G] [DecidableEq G] (cF : F → ℝ) (hcF : ∀ f, cF f ≠ 0) (pF : F → Fin 4 → ℝ)
    (MF : F → ℝ) (aF bF : F → Fin 4) (cG : G → ℝ) (hcG : ∀ g, cG g ≠ 0)
    (pG : G → Fin 4 → ℝ) (μG νG : G → Fin 4) (mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hF : Fintype.card F ≤ 3) (hcount : 4 < Fintype.card F + 4 * Fintype.card G) :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ =>
      (∏ f, (1 / I) * QED.OneLoop.electronPropagator (MF f) ε (cF f • ℓ 0 + pF f) (aF f) (bF f)) *
        ∏ g, (1 / I) * QED.OneLoop.photonPropagator mγ Λ ε (cG g • ℓ 0 + pG g) (μG g) (νG g) := by
  classical
  have h := jointEnergyFirstIntegrable_oneLoop' (ι := F ⊕ G × Fin 2)
    (Sum.elim cF fun x => cG x.1) (fun i => by rcases i with f | x <;> simp [hcF, hcG])
    (Sum.elim pF fun x => pG x.1) (Sum.elim MF fun x => if x.2 = 0 then mγ else Λ) hε
    (Finset.univ.map Function.Embedding.inl) (by simpa using hF)
    (by simp only [Finset.card_map, Finset.card_univ, Fintype.card_sum, Fintype.card_prod,
      Fintype.card_fin]; omega)
    (Sum.elim (fun f k => electronNumerator (MF f) k (aF f) (bF f)) fun _ _ => 1)
    (fun i hi => by
      obtain ⟨f, -, rfl⟩ := Finset.mem_map.mp hi
      exact electronNumerator_affine _ _ _)
    ((∏ _f : F, (1 / I)) *
      ∏ g, (1 / I) * ((Minkowski.metric (μG g) (νG g) * (Λ ^ 2 - mγ ^ 2) : ℝ) : ℂ))
  convert h using 2 with ℓ
  simp only [electronPropagator_apply, photonPropagator_eq_mul _ _ hε.ne', Finset.prod_map,
    Function.Embedding.inl_apply, Sum.elim_inl, Sum.elim_inr, Fintype.prod_sum_type,
    Fintype.prod_prod_type, Fin.prod_univ_two, Fin.isValue, ite_true, one_ne_zero, ite_false,
    Finset.prod_mul_distrib]
  ring

end QED.GradedProof.X0

end
