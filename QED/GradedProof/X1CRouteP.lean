/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CLinesP
public import QED.GradedProof.X1CRouteIn

/-!
# (X₁) piece C: the routing of a vacuum polarization glued onto the photon leg

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C2. In `glueP e C₁ C₂` with outgoing momentum `r'`, incoming `r`
and photon momentum `q`, the photon momentum `q` enters `C₂` at the field `w₁` (contracted with
its first external photon), leaves it at `w₂`, and crosses the bridge to `extSlot C₁`. The bridge
`b` runs from its smaller-key field to the other, so its momentum is `P = -q` when it starts at
`extSlot C₁` and `P = q` when it starts at `w₂`. With that `P`, the external momenta of `glueP`
corrected by the bridge are those of `C₁` at `(r', r, q)` and those of `C₂` at `(q, -q)`
(`externalMomentum_glueP_left`, `_right`), and (`jointEnergyFirstIntegral_glueP`) the joint
energy-first integral of any function of the line momenta of `glueP e C₁ C₂` is the one at the
canonical routings of `C₁` and `C₂` joined by the bridge momentum `P`.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction Line PhotonLine loopCount lineMomentum₂ externalMomentum
  VerticesConnected ExternalsAttached)
open QED.TwoLoop.Enumeration (head_eq)

variable {N N₁ N₂ : ℕ} {κ : Fin N → Wick.VertexKind} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}
  (C₁ : Contraction 1 1 (leftKinds κ e)) (C₂ : Contraction 0 2 (rightKinds κ e))
  {w₁ w₂ : Wick.PhotonSlot (rightKinds κ e)} (hw₁ : C₂.1.2 (.inl 0) = .inr w₁)
  (hw : C₂.1.2 (.inl 1) = .inr w₂)

theorem glueP_inl_iff (t : Wick.FermionVertex (leftKinds κ e)) (i : Fin 1) :
    (glueP e C₁ C₂).1.1 (.inr (fvSplit κ e (.inl t))) = .inl i ↔ C₁.1.1 (.inr t) = .inl i := by
  rw [← fL_inl_inr, glueP_fermion_left]
  rcases C₁.1.1 (.inr t) with j | s
  · rw [fL_inl_inl]
    simp only [Sum.inl.injEq]
  · rw [fL_inl_inr]
    exact ⟨fun h => absurd h Sum.inr_ne_inl, fun h => absurd h Sum.inr_ne_inl⟩

theorem glueP_ext_fermion (i : Fin 1) :
    (glueP e C₁ C₂).1.1 (.inl i) = fL κ e 1 (.inl (C₁.1.1 (.inl i))) := by
  rw [← glueP_fermion_left, fL_inl_inl]

include hw₁ in
theorem glueP_ext_w₁ : (glueP e C₁ C₂).1.2 (.inl 0) = .inr (psSplit κ e (.inr w₁)) := by
  rw [glueP_photon_ext, hw₁]
  rfl

include hw in
/-- The bridge correction at the vertices of `C₁`. -/
theorem corr_left {b : PhotonLine (glueP e C₁ C₂)} {q P : Fin 4 → ℝ}
    (hP : (b.1 = psSplit κ e (.inl (extSlot C₁)) ∧ P = -q) ∨
      (b.1 = psSplit κ e (.inr w₂) ∧ P = q)) (v : Fin N₁) :
    ((if b.head.1 = e (.inl v) then P else 0) - (if b.1.1 = e (.inl v) then P else 0)) =
      if (extSlot C₁).1 = v then q else 0 := by
  rcases hP with ⟨hb, rfl⟩ | ⟨hb, rfl⟩
  · rw [head_eq b (hb ▸ glueP_ext_w₂ C₁ C₂ hw), hb]
    by_cases h : (extSlot C₁).1 = v <;> simp [h]
  · rw [head_eq b (hb ▸ glueP_w₂_ext C₁ C₂ hw), hb]
    by_cases h : (extSlot C₁).1 = v <;> simp [h]

include hw in
/-- The bridge correction at the vertices of `C₂`. -/
theorem corr_right {b : PhotonLine (glueP e C₁ C₂)} {q P : Fin 4 → ℝ}
    (hP : (b.1 = psSplit κ e (.inl (extSlot C₁)) ∧ P = -q) ∨
      (b.1 = psSplit κ e (.inr w₂) ∧ P = q)) (v : Fin N₂) :
    ((if b.head.1 = e (.inr v) then P else 0) - (if b.1.1 = e (.inr v) then P else 0)) =
      -(if w₂.1 = v then q else 0) := by
  rcases hP with ⟨hb, rfl⟩ | ⟨hb, rfl⟩
  · rw [head_eq b (hb ▸ glueP_ext_w₂ C₁ C₂ hw), hb]
    by_cases h : w₂.1 = v <;> simp [h]
  · rw [head_eq b (hb ▸ glueP_w₂_ext C₁ C₂ hw), hb]
    by_cases h : w₂.1 = v <;> simp [h]

include hw₁ in
/-- The external momenta of `glueP` at the vertices of `C₁`, corrected by the bridge. -/
theorem externalMomentum_glueP_left (r' r q : Fin 4 → ℝ) (v : Fin N₁) :
    externalMomentum (glueP e C₁ C₂) ![r'] ![r] ![q] (e (.inl v)) +
      (if (extSlot C₁).1 = v then q else 0) = externalMomentum C₁ ![r'] ![r] ![q] v := by
  have I1 : ∀ i : Fin 1, (∃ t : Wick.FermionVertex κ, t.1 = e (.inl v) ∧
      (glueP e C₁ C₂).1.1 (.inr t) = .inl i) ↔ (∃ t : Wick.FermionVertex (leftKinds κ e),
        t.1 = v ∧ C₁.1.1 (.inr t) = .inl i) := fun i => by
    constructor
    · rintro ⟨t, ht, h⟩
      obtain ⟨y, rfl⟩ := (fvSplit κ e).surjective t
      rcases y with t | t
      · exact ⟨t, Sum.inl_injective (e.injective ht), (glueP_inl_iff C₁ C₂ t i).1 h⟩
      · simp at ht
    · rintro ⟨t, ht, h⟩
      exact ⟨fvSplit κ e (.inl t), by simp [ht], (glueP_inl_iff C₁ C₂ t i).2 h⟩
  have I2 : ∀ j : Fin 1, (∃ s : Wick.PhotonSlot κ, s.1 = e (.inl v) ∧
      (glueP e C₁ C₂).1.2 (.inl j) = .inr s) ↔ False := fun j => by
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    rw [glueP_ext_w₁ C₁ C₂ hw₁]
    refine iff_false_intro ?_
    rintro ⟨s, hs, h⟩
    rw [← Sum.inr_injective h] at hs
    simp at hs
  have I2' : ∀ j : Fin 1, (∃ s : Wick.PhotonSlot (leftKinds κ e), s.1 = v ∧
      C₁.1.2 (.inl j) = .inr s) ↔ (extSlot C₁).1 = v := fun j => by
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    rw [extSlot_spec]
    constructor
    · rintro ⟨s, hs, h⟩
      rwa [Sum.inr_injective h]
    · exact fun h => ⟨_, h, rfl⟩
  have I3 : ∀ i : Fin 1, (∃ t : Wick.FermionVertex κ, t.1 = e (.inl v) ∧
      (glueP e C₁ C₂).1.1 (.inl i) = .inr t) ↔ (∃ t : Wick.FermionVertex (leftKinds κ e),
        t.1 = v ∧ C₁.1.1 (.inl i) = .inr t) := fun i => by
    rw [glueP_ext_fermion]
    rcases C₁.1.1 (.inl i) with j | a
    · rw [fL_inl_inl]
      exact ⟨fun ⟨_, _, h⟩ => absurd h Sum.inl_ne_inr, fun ⟨_, _, h⟩ => absurd h Sum.inl_ne_inr⟩
    · rw [fL_inl_inr]
      simp only [Sum.inr.injEq]
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨_, Sum.inl_injective (e.injective ht), rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨_, by simp only [fvSplit_inl, ht], rfl⟩
  unfold externalMomentum
  simp only [I1, I2, I2', I3, ite_false, Fin.sum_univ_one, Matrix.cons_val_zero]
  abel

include hw₁ hw in
/-- The external momenta of `glueP` at the vertices of `C₂`, corrected by the bridge. -/
theorem externalMomentum_glueP_right (r' r q : Fin 4 → ℝ) (v : Fin N₂) :
    externalMomentum (glueP e C₁ C₂) ![r'] ![r] ![q] (e (.inr v)) +
      -(if w₂.1 = v then q else 0) = externalMomentum C₂ ![] ![] ![q, -q] v := by
  have J1 : ∀ i : Fin 1, (∃ t : Wick.FermionVertex κ, t.1 = e (.inr v) ∧
      (glueP e C₁ C₂).1.1 (.inr t) = .inl i) ↔ False := fun i => by
    refine iff_false_intro ?_
    rintro ⟨t, ht, h⟩
    obtain ⟨y, rfl⟩ := (fvSplit κ e).surjective t
    rcases y with t | t
    · simp at ht
    · obtain ⟨s, hs⟩ := exists_right_pair C₂ t
      rw [glueP_right' C₁ C₂ hs] at h
      exact Sum.inr_ne_inl h
  have J2 : ∀ j : Fin 1, (∃ s : Wick.PhotonSlot κ, s.1 = e (.inr v) ∧
      (glueP e C₁ C₂).1.2 (.inl j) = .inr s) ↔ w₁.1 = v := fun j => by
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    rw [glueP_ext_w₁ C₁ C₂ hw₁]
    constructor
    · rintro ⟨s, hs, h⟩
      rw [← Sum.inr_injective h] at hs
      exact Sum.inr_injective (e.injective hs)
    · exact fun h => ⟨_, by simp [h], rfl⟩
  have J2' : ∀ j : Fin 2, (∃ s : Wick.PhotonSlot (rightKinds κ e), s.1 = v ∧
      C₂.1.2 (.inl j) = .inr s) ↔ (if j = 0 then w₁.1 = v else w₂.1 = v) := fun j => by
    fin_cases j
    · simp only [Fin.zero_eta, ite_true, hw₁, Sum.inr.injEq, exists_eq_right']
    · simp only [Fin.mk_one, one_ne_zero, ite_false, hw, Sum.inr.injEq, exists_eq_right']
  have J3 : ∀ i : Fin 1, (∃ t : Wick.FermionVertex κ, t.1 = e (.inr v) ∧
      (glueP e C₁ C₂).1.1 (.inl i) = .inr t) ↔ False := fun i => by
    rw [glueP_ext_fermion]
    refine iff_false_intro ?_
    rintro ⟨t, ht, h⟩
    rcases h2 : C₁.1.1 (.inl i) with j | a
    · rw [h2, fL_inl_inl] at h
      exact Sum.inl_ne_inr h
    · rw [h2, fL_inl_inr] at h
      rw [← Sum.inr_injective h] at ht
      simp at ht
  unfold externalMomentum
  simp only [J1, J2, J2', J3, ite_false, Fin.sum_univ_one, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Finset.univ_eq_empty, Finset.sum_empty, one_ne_zero, ite_true]
  by_cases h : w₂.1 = v <;> simp [h]

include hw₁ in
/-- **The routing of `glueP`**: for `r' = r + q` and connected `glueP e C₁ C₂`, `C₁`, `C₂` with
attached externals, and the bridge `b` with its momentum `P` (`-q` if it starts at `extSlot C₁`,
`q` if it starts at `w₂`), the joint energy-first integral of any function of the line momenta at
the canonical routing is the one at the canonical routings of `C₁` (at `(r', r, q)`, loop momenta
first) and `C₂` (at `(q, -q)`), joined by the bridge momentum `P`. -/
theorem jointEnergyFirstIntegral_glueP (he : IsShuffle e)
    (hV : VerticesConnected (glueP e C₁ C₂)) (hV₁ : VerticesConnected C₁)
    (hV₂ : VerticesConnected C₂) (hA₁ : ExternalsAttached C₁) (hA₂ : ExternalsAttached C₂)
    {r' r q P : Fin 4 → ℝ} (hmom : r' = r + q) {b : PhotonLine (glueP e C₁ C₂)}
    (hb : b.1 = psSplit κ e (.inl (extSlot C₁)) ∨ b.1 = psSplit κ e (.inr w₂))
    (hP : (b.1 = psSplit κ e (.inl (extSlot C₁)) ∧ P = -q) ∨
      (b.1 = psSplit κ e (.inr w₂) ∧ P = q))
    (F : (Line (glueP e C₁ C₂) → Fin 4 → ℝ) → ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegral (loopCount C₁ + loopCount C₂)
        (fun ℓ => F (lineMomentum₂ (glueP e C₁ C₂) ![r'] ![r] ![q] ℓ)) =
      QED.TwoLoop.jointEnergyFirstIntegral (loopCount C₁ + loopCount C₂) (fun ℓ =>
        F ((lineSplitP C₁ C₂ hw he hb).splitMom
          (lineMomentum₂ C₁ ![r'] ![r] ![q] fun s => ℓ (Fin.castAdd _ s))
          (lineMomentum₂ C₂ ![] ![] ![q, -q] fun s => ℓ (Fin.natAdd _ s)) P)) := by
  have hs₁ : ∑ v, externalMomentum C₁ ![r'] ![r] ![q] v = 0 := by
    rw [QED.TwoLoop.Relabel.sum_externalMomentum hA₁]
    simp [hmom]
  have hs₂ : ∑ v, externalMomentum C₂ ![] ![] ![q, -q] v = 0 := by
    rw [QED.TwoLoop.Relabel.sum_externalMomentum hA₂]
    simp
  exact (lineSplitP C₁ C₂ hw he hb).jointEnergyFirstIntegral_split hV₁ hV₂ hs₁ hs₂
    (fun v => by
      rw [corr_left C₁ C₂ hw hP v]
      exact externalMomentum_glueP_left C₁ C₂ hw₁ r' r q v)
    (fun v => by
      rw [corr_right C₁ C₂ hw hP v]
      exact externalMomentum_glueP_right C₁ C₂ hw₁ hw r' r q v)
    ((lineSplitP C₁ C₂ hw he hb).loopCount_split hV hV₁ hV₂ (Fin.pos (extSlot C₁).1)
      (Fin.pos w₂.1)) F

end QED.GradedProof.X1C

end
