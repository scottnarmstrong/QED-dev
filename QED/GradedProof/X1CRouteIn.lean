/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CLinesIn
public import QED.GradedProof.X1CGlueP
public import QED.Frozen.WickModel.ExternalsAttached
public import QED.TwoLoop.RelabelInvariance

/-!
# (X₁) piece C: the routing of a self-energy glued onto the incoming leg

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C2. In `glueIn e C₁ C₂` with outgoing momentum `r'`, incoming `r`
and photon momentum `q`, the external momenta at the vertices of `C₁` corrected by the bridge
momentum `r` (flowing from `c` to `a`) are those of `C₁` at `(r', r, q)`, and at the vertices of
`C₂` those of `C₂` at `(r, r)` (`externalMomentum_glueIn_left`, `_right`). So
(`jointEnergyFirstIntegral_glueIn`) the joint energy-first integral of any function of the line
momenta of `glueIn e C₁ C₂` is the one at the canonical routings of `C₁` and `C₂` joined by the
bridge momentum `r`, when `r' = r + q` and all three are connected.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction Line loopCount lineMomentum₂ externalMomentum VerticesConnected
  ExternalsAttached)

variable {N N₁ N₂ : ℕ} {κ : Fin N → Wick.VertexKind} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}
  (C₁ : Contraction 1 1 (leftKinds κ e)) (C₂ : Contraction 1 0 (rightKinds κ e))
  {a x : Wick.FermionVertex (leftKinds κ e)} {c : Wick.FermionVertex (rightKinds κ e)}
  (ha : C₁.1.1 (.inr a) = .inl 0) (hx : C₁.1.1 (.inl 0) = .inr x)
  (hc : C₂.1.1 (.inl 0) = .inr c)

include ha hc in
theorem glueIn_ne_inl_left (t : Wick.FermionVertex (leftKinds κ e)) (i : Fin 1) :
    (glueIn e C₁ C₂).1.1 (.inr (fvSplit κ e (.inl t))) ≠ .inl i := by
  rcases h : C₁.1.1 (.inr t) with j | s
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    have : t = a := Sum.inr_injective (C₁.1.1.injective (h.trans ha.symm))
    subst this
    rw [glueIn_bridge C₁ C₂ ha hc]
    exact Sum.inr_ne_inl
  · rw [glueIn_left' C₁ C₂ h]
    exact Sum.inr_ne_inl

theorem glueIn_inr_iff (t : Wick.FermionVertex (rightKinds κ e)) (i : Fin 1) :
    (glueIn e C₁ C₂).1.1 (.inr (fvSplit κ e (.inr t))) = .inl i ↔ C₂.1.1 (.inr t) = .inl i := by
  rw [glueIn_right]
  rcases C₂.1.1 (.inr t) with j | s
  · rw [fR_inr_inl]
    simp only [Sum.inl.injEq]
  · rw [fR_inr_inr]
    exact ⟨fun h => absurd h Sum.inr_ne_inl, fun h => absurd h Sum.inr_ne_inl⟩

theorem glueIn_ext_out (hx : C₁.1.1 (.inl 0) = .inr x) :
    (glueIn e C₁ C₂).1.1 (.inl 0) = .inr (fvSplit κ e (.inl x)) := by
  have h := glueIn_left C₁ C₂ hx
  rwa [fL_inl_inl] at h

theorem glueIn_ext_photon :
    (glueIn e C₁ C₂).1.2 (.inl 0) = .inr (psSplit κ e (.inl (extSlot C₁))) := by
  have h := gluePhotons_left C₁ C₂ (e := e) (.inl 0)
  rw [extSlot_spec, pL_inl_inl, pL_inl_inr] at h
  exact h

include ha hx hc in
/-- The external momenta of `glueIn` at the vertices of `C₁`, corrected by the bridge. -/
theorem externalMomentum_glueIn_left (r' r q : Fin 4 → ℝ) (v : Fin N₁) :
    externalMomentum (glueIn e C₁ C₂) ![r'] ![r] ![q] (e (.inl v)) +
      ((if e (.inl a.1) = e (.inl v) then r else 0) -
        (if e (.inr c.1) = e (.inl v) then r else 0)) =
      externalMomentum C₁ ![r'] ![r] ![q] v := by
  have I1 : ∀ i : Fin 1, (∃ t : Wick.FermionVertex κ, t.1 = e (.inl v) ∧
      (glueIn e C₁ C₂).1.1 (.inr t) = .inl i) ↔ False := fun i => by
    refine iff_false_intro ?_
    rintro ⟨t, ht, h⟩
    obtain ⟨y, rfl⟩ := (fvSplit κ e).surjective t
    rcases y with t | t
    · exact glueIn_ne_inl_left C₁ C₂ ha hc t i h
    · simp at ht
  have I1' : ∀ i : Fin 1, (∃ t : Wick.FermionVertex (leftKinds κ e), t.1 = v ∧
      C₁.1.1 (.inr t) = .inl i) ↔ a.1 = v := fun i => by
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    constructor
    · rintro ⟨t, ht, h⟩
      rwa [← Sum.inr_injective (C₁.1.1.injective (h.trans ha.symm))]
    · exact fun h => ⟨a, h, ha⟩
  have I2 : ∀ j : Fin 1, (∃ s : Wick.PhotonSlot κ, s.1 = e (.inl v) ∧
      (glueIn e C₁ C₂).1.2 (.inl j) = .inr s) ↔ (∃ s : Wick.PhotonSlot (leftKinds κ e),
        s.1 = v ∧ C₁.1.2 (.inl j) = .inr s) := fun j => by
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    rw [glueIn_ext_photon, extSlot_spec]
    simp only [Sum.inr.injEq]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨_, Sum.inl_injective (e.injective hs), rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨_, by simp only [psSplit_inl, hs], rfl⟩
  have I3 : ∀ i : Fin 1, (∃ t : Wick.FermionVertex κ, t.1 = e (.inl v) ∧
      (glueIn e C₁ C₂).1.1 (.inl i) = .inr t) ↔ (∃ t : Wick.FermionVertex (leftKinds κ e),
        t.1 = v ∧ C₁.1.1 (.inl i) = .inr t) := fun i => by
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rw [glueIn_ext_out C₁ C₂ hx, hx]
    simp only [Sum.inr.injEq]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨_, Sum.inl_injective (e.injective ht), rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨_, by simp only [fvSplit_inl, ht], rfl⟩
  unfold externalMomentum
  simp only [I1, I1', I2, I3, ite_false, Fin.sum_univ_one, Matrix.cons_val_zero,
    EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, reduceCtorEq]
  by_cases h : a.1 = v
  · simp only [h, ite_true, sub_zero]
    abel
  · simp [h]

include hx hc in
/-- The external momenta of `glueIn` at the vertices of `C₂`, corrected by the bridge. -/
theorem externalMomentum_glueIn_right (r' r q : Fin 4 → ℝ) (v : Fin N₂) :
    externalMomentum (glueIn e C₁ C₂) ![r'] ![r] ![q] (e (.inr v)) +
      ((if e (.inl a.1) = e (.inr v) then r else 0) -
        (if e (.inr c.1) = e (.inr v) then r else 0)) =
      externalMomentum C₂ ![r] ![r] ![] v := by
  have J1 : ∀ i : Fin 1, (∃ t : Wick.FermionVertex κ, t.1 = e (.inr v) ∧
      (glueIn e C₁ C₂).1.1 (.inr t) = .inl i) ↔ (∃ t : Wick.FermionVertex (rightKinds κ e),
        t.1 = v ∧ C₂.1.1 (.inr t) = .inl i) := fun i => by
    constructor
    · rintro ⟨t, ht, h⟩
      obtain ⟨y, rfl⟩ := (fvSplit κ e).surjective t
      rcases y with t | t
      · simp at ht
      · exact ⟨t, Sum.inr_injective (e.injective ht), (glueIn_inr_iff C₁ C₂ t i).1 h⟩
    · rintro ⟨t, ht, h⟩
      exact ⟨fvSplit κ e (.inr t), by simp [ht], (glueIn_inr_iff C₁ C₂ t i).2 h⟩
  have J2 : ∀ j : Fin 1, (∃ s : Wick.PhotonSlot κ, s.1 = e (.inr v) ∧
      (glueIn e C₁ C₂).1.2 (.inl j) = .inr s) ↔ False := fun j => by
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    rw [glueIn_ext_photon]
    refine iff_false_intro ?_
    rintro ⟨s, hs, h⟩
    rw [← Sum.inr_injective h] at hs
    simp at hs
  have J3 : ∀ i : Fin 1, (∃ t : Wick.FermionVertex κ, t.1 = e (.inr v) ∧
      (glueIn e C₁ C₂).1.1 (.inl i) = .inr t) ↔ False := fun i => by
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rw [glueIn_ext_out C₁ C₂ hx]
    refine iff_false_intro ?_
    rintro ⟨t, ht, h⟩
    rw [← Sum.inr_injective h] at ht
    simp at ht
  have J3' : ∀ i : Fin 1, (∃ t : Wick.FermionVertex (rightKinds κ e), t.1 = v ∧
      C₂.1.1 (.inl i) = .inr t) ↔ c.1 = v := fun i => by
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rw [hc]
    constructor
    · rintro ⟨t, ht, h⟩
      rwa [Sum.inr_injective h]
    · exact fun h => ⟨c, h, rfl⟩
  unfold externalMomentum
  simp only [J1, J2, J3, J3', ite_false, Fin.sum_univ_one, Matrix.cons_val_zero,
    EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq, reduceCtorEq, Finset.univ_eq_empty,
    Finset.sum_empty]
  by_cases h : c.1 = v
  · simp only [h, ite_true]
    abel
  · simp [h]

include ha hx hc in
/-- **The routing of `glueIn`**: for `r' = r + q` and connected `glueIn e C₁ C₂`, `C₁`, `C₂` with
attached externals, the joint energy-first integral of any function of the line momenta at the
canonical routing is the one at the canonical routings of `C₁` (at `(r', r, q)`, loop momenta
first) and `C₂` (at `(r, r)`), joined by the bridge momentum `r`. -/
theorem jointEnergyFirstIntegral_glueIn (he : IsShuffle e)
    (hV : VerticesConnected (glueIn e C₁ C₂)) (hV₁ : VerticesConnected C₁)
    (hV₂ : VerticesConnected C₂) (hA₁ : ExternalsAttached C₁) (hA₂ : ExternalsAttached C₂)
    {r' r q : Fin 4 → ℝ} (hmom : r' = r + q)
    (F : (Line (glueIn e C₁ C₂) → Fin 4 → ℝ) → ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegral (loopCount C₁ + loopCount C₂)
        (fun ℓ => F (lineMomentum₂ (glueIn e C₁ C₂) ![r'] ![r] ![q] ℓ)) =
      QED.TwoLoop.jointEnergyFirstIntegral (loopCount C₁ + loopCount C₂) (fun ℓ =>
        F ((lineSplitIn C₁ C₂ ha hc he).splitMom
          (lineMomentum₂ C₁ ![r'] ![r] ![q] fun s => ℓ (Fin.castAdd _ s))
          (lineMomentum₂ C₂ ![r] ![r] ![] fun s => ℓ (Fin.natAdd _ s)) r)) := by
  have hs₁ : ∑ v, externalMomentum C₁ ![r'] ![r] ![q] v = 0 := by
    rw [QED.TwoLoop.Relabel.sum_externalMomentum hA₁]
    simp [hmom]
  have hs₂ : ∑ v, externalMomentum C₂ ![r] ![r] ![] v = 0 := by
    rw [QED.TwoLoop.Relabel.sum_externalMomentum hA₂]
    simp
  exact (lineSplitIn C₁ C₂ ha hc he).jointEnergyFirstIntegral_split hV₁ hV₂ hs₁ hs₂
    (externalMomentum_glueIn_left C₁ C₂ ha hx hc r' r q)
    (externalMomentum_glueIn_right C₁ C₂ hx hc r' r q)
    ((lineSplitIn C₁ C₂ ha hc he).loopCount_split hV hV₁ hV₂ (Fin.pos a.1) (Fin.pos c.1)) F

end QED.GradedProof.X1C

end
