/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CAmpIn
public import QED.Frozen.TwoLoop.PhotonMomentum

/-!
# (X₁) piece C: the photon momenta of the pieces of a leg gluing

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C3 (value factorization).

For a contraction `C` whose photon pairing is the disjoint union of those of `C₁` (with the photon
externals) and `C₂` (none), and line momenta `k` that give the photon lines of the pieces the
momenta `k₁`, `k₂` of the pieces, the momentum (T₆) entering a photon field of a piece is that of
the piece (`photonMomentum₂_split_left`, `_right`). The statements take the photon pairing as a
hypothesis `hC`, so no `rfl` proof appears in a rewritten term; `photonMomentum₂_glueIn_left`,
`_right` specialize them to `glueIn` at the split assignment of `lineSplitIn`.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction Line PhotonLine photonMomentum₂)

variable {N N₁ N₂ nA nf₁ nf₂ nf : ℕ} {κ : Fin N → Wick.VertexKind}
  {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N} {C₁ : Contraction nf₁ nA (leftKinds κ e)}
  {C₂ : Contraction nf₂ 0 (rightKinds κ e)} {C : Contraction nf nA κ}
  (hC : C.1.2 = dsum (pL κ e nA) C₁.1.2 C₂.1.2) (he : IsShuffle e)
  {k : Line C → Fin 4 → ℝ} {k₁ : Line C₁ → Fin 4 → ℝ} {k₂ : Line C₂ → Fin 4 → ℝ}

include hC in
theorem photon_inl_eq (j : Fin nA) : C.1.2 (.inl j) = pL κ e nA (.inl (C₁.1.2 (.inl j))) := by
  rw [hC]
  exact dsum_apply_inl (pL κ e nA) C₁.1.2 C₂.1.2 (.inl j)

include hC in
theorem photon_inl_left_iff (j : Fin nA) (a : Wick.PhotonSlot (leftKinds κ e)) :
    C.1.2 (.inl j) = .inr (psSplit κ e (.inl a)) ↔ C₁.1.2 (.inl j) = .inr a := by
  rw [photon_inl_eq hC]
  constructor
  · intro h
    rcases h' : C₁.1.2 (.inl j) with i | b
    · rw [h'] at h
      exact absurd h (by simp)
    · rw [h', pL_inl_inr] at h
      rw [Sum.inl_injective ((psSplit κ e).injective (Sum.inr_injective h))]
  · intro h
    rw [h, pL_inl_inr]

include hC in
theorem photon_inl_ne_right (j : Fin nA) (a : Wick.PhotonSlot (rightKinds κ e)) :
    C.1.2 (.inl j) ≠ .inr (psSplit κ e (.inr a)) := by
  rw [photon_inl_eq hC]
  intro h
  rcases h' : C₁.1.2 (.inl j) with i | b
  · rw [h'] at h
    exact absurd h (by simp)
  · rw [h', pL_inl_inr] at h
    exact absurd ((psSplit κ e).injective (Sum.inr_injective h)) (by simp)

include hC he in
/-- **The photon momentum at a field of the left piece** is that of the left piece. -/
theorem photonMomentum₂_split_left (kIn : Fin nA → Fin 4 → ℝ)
    (hk₁ : ∀ g, k (.inr (photonLineMap hC he (.inl g))) = k₁ (.inr g))
    (a : Wick.PhotonSlot (leftKinds κ e)) :
    photonMomentum₂ C kIn k (psSplit κ e (.inl a)) = photonMomentum₂ C₁ kIn k₁ a := by
  unfold photonMomentum₂
  congr 1
  · refine Finset.sum_congr rfl fun j _ => if_congr ?_ rfl rfl
    exact photon_inl_left_iff hC j a
  · rw [← Fintype.sum_bijective _ (photonLineMap_bijective hC he) _ _ fun _ => rfl,
      Fintype.sum_sum_type]
    have h0 : ∀ g : PhotonLine C₂,
        ((if (photonLineMap hC he (.inr g)).head = psSplit κ e (.inl a) then
          k (.inr (photonLineMap hC he (.inr g))) else 0) -
        (if (photonLineMap hC he (.inr g)).1 = psSplit κ e (.inl a) then
          k (.inr (photonLineMap hC he (.inr g))) else 0)) = 0 := fun g => by
      obtain ⟨h1, h2⟩ := photonLineMap_right hC he g
      rw [h1, h2]
      simp
    rw [Finset.sum_eq_zero fun g _ => h0 g, add_zero]
    refine Finset.sum_congr rfl fun g _ => ?_
    obtain ⟨h1, h2⟩ := photonLineMap_left hC he g
    rw [h1, h2, hk₁]
    simp only [(psSplit κ e).injective.eq_iff, Sum.inl.injEq]

include hC he in
/-- **The photon momentum at a field of the right piece** is that of the right piece. -/
theorem photonMomentum₂_split_right (kIn : Fin nA → Fin 4 → ℝ)
    (hk₂ : ∀ g, k (.inr (photonLineMap hC he (.inr g))) = k₂ (.inr g))
    (a : Wick.PhotonSlot (rightKinds κ e)) :
    photonMomentum₂ C kIn k (psSplit κ e (.inr a)) = photonMomentum₂ C₂ ![] k₂ a := by
  unfold photonMomentum₂
  congr 1
  · rw [Finset.sum_eq_zero fun j _ => ?_]
    · simp
    · exact ite_eq_right_iff.2 fun h => absurd h (photon_inl_ne_right hC j a)
  · rw [← Fintype.sum_bijective _ (photonLineMap_bijective hC he) _ _ fun _ => rfl,
      Fintype.sum_sum_type]
    have h0 : ∀ g : PhotonLine C₁,
        ((if (photonLineMap hC he (.inl g)).head = psSplit κ e (.inr a) then
          k (.inr (photonLineMap hC he (.inl g))) else 0) -
        (if (photonLineMap hC he (.inl g)).1 = psSplit κ e (.inr a) then
          k (.inr (photonLineMap hC he (.inl g))) else 0)) = 0 := fun g => by
      obtain ⟨h1, h2⟩ := photonLineMap_left hC he g
      rw [h1, h2]
      simp
    rw [Finset.sum_eq_zero fun g _ => h0 g, zero_add]
    refine Finset.sum_congr rfl fun g _ => ?_
    obtain ⟨h1, h2⟩ := photonLineMap_right hC he g
    rw [h1, h2, hk₂]
    simp only [(psSplit κ e).injective.eq_iff, Sum.inr.injEq]

/-! ### The photon momenta of `glueIn` -/

section GlueIn

variable (C₁ : Contraction 1 nA (leftKinds κ e)) (C₂ : Contraction 1 0 (rightKinds κ e))
  {a : Wick.FermionVertex (leftKinds κ e)} {c : Wick.FermionVertex (rightKinds κ e)}
  (ha : C₁.1.1 (.inr a) = .inl 0) (hc : C₂.1.1 (.inl 0) = .inr c) (he : IsShuffle e)
  (k₁ : Line C₁ → Fin 4 → ℝ) (k₂ : Line C₂ → Fin 4 → ℝ) (r : Fin 4 → ℝ)

theorem photonMomentum₂_glueIn_left (kIn : Fin nA → Fin 4 → ℝ)
    (s : Wick.PhotonSlot (leftKinds κ e)) :
    photonMomentum₂ (glueIn e C₁ C₂) kIn ((lineSplitIn C₁ C₂ ha hc he).splitMom k₁ k₂ r)
        (psSplit κ e (.inl s)) = photonMomentum₂ C₁ kIn k₁ s :=
  photonMomentum₂_split_left rfl he kIn (fun g => by
    have h := LineSplit.splitMom_left (lineSplitIn C₁ C₂ ha hc he) k₁ k₂ r (.inr g)
    rwa [lineSplitIn_left_photon] at h) s

theorem photonMomentum₂_glueIn_right (kIn : Fin nA → Fin 4 → ℝ)
    (s : Wick.PhotonSlot (rightKinds κ e)) :
    photonMomentum₂ (glueIn e C₁ C₂) kIn ((lineSplitIn C₁ C₂ ha hc he).splitMom k₁ k₂ r)
        (psSplit κ e (.inr s)) = photonMomentum₂ C₂ ![] k₂ s :=
  photonMomentum₂_split_right rfl he kIn (fun g => by
    have h := LineSplit.splitMom_right (lineSplitIn C₁ C₂ ha hc he) k₁ k₂ r (.inr g)
    rwa [lineSplitIn_right_photon] at h) s

end GlueIn

end QED.GradedProof.X1C

end
