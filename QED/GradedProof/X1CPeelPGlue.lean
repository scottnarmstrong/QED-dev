/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CPeelPDefs
public import QED.GradedProof.X1CLinesP
public import QED.GradedProof.X1CCountConn

/-!
# (X₁) piece C: sides of lines in the photon-leg glue

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (the graph theory of the photon-leg peel). For a split `L` with
bridge ends `e (inl a)`, `e (inr c)` (either orientation) and a connected right piece,
`LineSplit.peelP_reach_right_iff`: a vertex of the left piece reaches the right piece without a
set of lines of the left piece iff it reaches `a` in the left piece.

For `G = glueP e C₁ C₂` (`C₁` a vertex, `C₂` a vacuum polarization with `C₂.1.2 (inl 0) = w₁`,
`C₂.1.2 (inl 1) = w₂`, bridge `b` from `extSlot C₁` to `w₂`):

* the externals: the fermion externals of `G` are those of `C₁` (`peelP_fermAt_glue`), the photon
  external of `G` sits at `w₁` (`peelP_photonAt_glue`);
* `peelP_ends`: the ends of the bridge `b`;
* for a line `l₁` of `C₁`, its sides in `G` are its sides in `C₁`, plus the whole of `C₂` when
  they hold `extSlot C₁` (`peelP_side_left`, `peelP_side_right`); hence the side of `l₁` in `G`
  carries a fermion external, the photon external, an external iff its side in `C₁` does
  (`peelP_fermAt_side`, `peelP_noPhotonAt_side`, `peelP_extAt_side`).
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction Line FermionLine PhotonLine Joined IsBridge VerticesConnected
  ExternalsAttached IsOnePI)
open QED.TwoLoop.Enumeration (head_eq)
open Relation

/-! ### Paths into the right piece of a split -/

namespace LineSplit

variable {nf nA N N₁ N₂ : ℕ} {κ : Fin N → Wick.VertexKind} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}
  {nf₁ nA₁ nf₂ nA₂ : ℕ} {C : Contraction nf nA κ} {C₁ : Contraction nf₁ nA₁ (leftKinds κ e)}
  {C₂ : Contraction nf₂ nA₂ (rightKinds κ e)} {u w : Fin N} (L : LineSplit C C₁ C₂ u w)
  {a : Fin N₁} {c : Fin N₂}
  (hb : (u = e (.inl a) ∧ w = e (.inr c)) ∨ (u = e (.inr c) ∧ w = e (.inl a)))
include hb

theorem peelP_bridge_joined {S : Set (Line C)} (hS : L.peelBridge ∉ S) :
    Joined C S (e (.inl a)) (e (.inr c)) := by
  refine ⟨L.peelBridge, hS, ?_⟩
  have h : L.peelBridge.ends = (u, w) := L.ends_bridge
  rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .inl h
  · exact .inr h

theorem peelP_reach_left_iff {S : Set (Line C)} {s s' : Fin N₁} :
    ReflTransGen (Joined C S) (e (.inl s)) (e (.inl s')) ↔
      ReflTransGen (Joined C₁ (L.peelSet₁ S)) s s' :=
  ⟨L.peel_proj_left_left hb, L.peel_lift_left⟩

/-- **A vertex of the left piece reaches the right piece iff it reaches the left end of the
bridge.** -/
theorem peelP_reach_right_iff (hV₂ : VerticesConnected C₂) {S : Set (Line C)}
    (hS₂ : ∀ g, L.equiv (.inr (.inl g)) ∉ S) (hSb : L.peelBridge ∉ S) {s : Fin N₁}
    {r : Fin N₂} :
    ReflTransGen (Joined C S) (e (.inl s)) (e (.inr r)) ↔
      ReflTransGen (Joined C₁ (L.peelSet₁ S)) s a := by
  constructor
  · intro h
    have h' := L.peel_proj_left hb h
    simp only [Equiv.symm_apply_apply, Sum.elim_inr] at h'
    exact h'.2
  · intro h
    exact ((L.peel_lift_left h).tail (L.peelP_bridge_joined hb hSb)).trans
      (L.peel_lift_right' hS₂ (hV₂ c r))

end LineSplit

variable {N N₁ N₂ : ℕ} {κ : Fin N → Wick.VertexKind} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}

/-! ### The externals of the glue -/

theorem peelP_photonAt_one {M nf : ℕ} {κ' : Fin M → Wick.VertexKind} (C : Contraction nf 1 κ')
    (T : Fin M → Prop) :
    (∃ j a, C.1.2 (.inl j) = .inr a ∧ T a.1) ↔ T (extSlot C).1 := by
  constructor
  · rintro ⟨j, a, hj, hT⟩
    rw [Subsingleton.elim j 0, extSlot_spec] at hj
    cases Sum.inr_injective hj
    exact hT
  · intro hT
    exact ⟨0, _, extSlot_spec C, hT⟩

theorem peelP_noPhotonAt_iff {nf nA M : ℕ} {κ' : Fin M → Wick.VertexKind}
    (C : Contraction nf nA κ') (T : Fin M → Prop) :
    PeelNoPhotonAt C T ↔ ¬ ∃ j a, C.1.2 (.inl j) = .inr a ∧ T a.1 := by
  simp only [PeelNoPhotonAt, not_exists, not_and]

variable (C₁ : Contraction 1 1 (leftKinds κ e)) (C₂ : Contraction 0 2 (rightKinds κ e))

theorem peelP_glue_out {x : Wick.FermionVertex (leftKinds κ e)}
    (hx : C₁.1.1 (.inl 0) = .inr x) :
    (glueP e C₁ C₂).1.1 (.inl 0) = .inr (fvSplit κ e (.inl x)) := by
  have h := glueP_fermion_left e C₁ C₂ (.inl 0)
  rw [hx] at h
  exact h

theorem peelP_glue_in {y : Wick.FermionVertex (leftKinds κ e)}
    (hy : C₁.1.1 (.inr y) = .inl 0) :
    (glueP e C₁ C₂).1.1 (.inr (fvSplit κ e (.inl y))) = .inl 0 := by
  have h := glueP_fermion_left e C₁ C₂ (.inr y)
  rw [hy] at h
  exact h

theorem peelP_glue_out_inv {x : Wick.FermionVertex κ}
    (hx : (glueP e C₁ C₂).1.1 (.inl 0) = .inr x) :
    ∃ x₁, x = fvSplit κ e (.inl x₁) ∧ C₁.1.1 (.inl 0) = .inr x₁ := by
  rcases h : C₁.1.1 (.inl 0) with i | x₁
  · have h' := glueP_fermion_left e C₁ C₂ (.inl 0)
    rw [h] at h'
    have h'' : (glueP e C₁ C₂).1.1 (.inl 0) = .inl i := h'
    rw [h''] at hx
    exact absurd hx Sum.inl_ne_inr
  · rw [peelP_glue_out C₁ C₂ h] at hx
    exact ⟨x₁, (Sum.inr_injective hx).symm, rfl⟩

theorem peelP_glue_in_inv {y : Wick.FermionVertex κ}
    (hy : (glueP e C₁ C₂).1.1 (.inr y) = .inl 0) :
    ∃ y₁, y = fvSplit κ e (.inl y₁) ∧ C₁.1.1 (.inr y₁) = .inl 0 := by
  obtain ⟨z, rfl⟩ := (fvSplit κ e).surjective y
  rcases z with t | t
  · rcases h : C₁.1.1 (.inr t) with i | s
    · exact ⟨t, rfl, by rw [h, Subsingleton.elim i 0]⟩
    · rw [glueP_left' C₁ C₂ h] at hy
      exact absurd hy Sum.inr_ne_inl
  · obtain ⟨s, hs⟩ := exists_right_pair C₂ t
    rw [glueP_right' C₁ C₂ hs] at hy
    exact absurd hy Sum.inr_ne_inl

/-- **The fermion externals of the glue are those of the vertex piece.** -/
theorem peelP_fermAt_glue (T : Fin N → Prop) :
    PeelPFermAt (glueP e C₁ C₂) T ↔ PeelPFermAt C₁ fun s => T (e (.inl s)) := by
  constructor
  · rintro (⟨s, hs, hT⟩ | ⟨s, hs, hT⟩)
    · obtain ⟨x₁, rfl, hx₁⟩ := peelP_glue_out_inv C₁ C₂ hs
      exact .inl ⟨x₁, hx₁, hT⟩
    · obtain ⟨y₁, rfl, hy₁⟩ := peelP_glue_in_inv C₁ C₂ hs
      exact .inr ⟨y₁, hy₁, hT⟩
  · rintro (⟨s, hs, hT⟩ | ⟨s, hs, hT⟩)
    · exact .inl ⟨_, peelP_glue_out C₁ C₂ hs, hT⟩
    · exact .inr ⟨_, peelP_glue_in C₁ C₂ hs, hT⟩

variable {w₁ : Wick.PhotonSlot (rightKinds κ e)} (hw₁ : C₂.1.2 (.inl 0) = .inr w₁)
include hw₁

theorem peelP_glue_photon :
    (glueP e C₁ C₂).1.2 (.inl 0) = .inr (psSplit κ e (.inr w₁)) := by
  rw [glueP_photon_ext, hw₁]
  rfl

/-- **The photon external of the glue sits at `w₁`.** -/
theorem peelP_photonAt_glue (T : Fin N → Prop) :
    (∃ j a, (glueP e C₁ C₂).1.2 (.inl j) = .inr a ∧ T a.1) ↔ T (e (.inr w₁.1)) := by
  constructor
  · rintro ⟨j, a, hj, hT⟩
    rw [Subsingleton.elim j 0, peelP_glue_photon C₁ C₂ hw₁] at hj
    cases Sum.inr_injective hj
    exact hT
  · intro hT
    exact ⟨0, _, peelP_glue_photon C₁ C₂ hw₁, hT⟩

omit hw₁

/-- **The glue of an attached vertex is attached.** -/
theorem peelP_glue_attached (hA₁ : ExternalsAttached C₁) (hw₁ : C₂.1.2 (.inl 0) = .inr w₁) :
    ExternalsAttached (glueP e C₁ C₂) := by
  obtain ⟨x, hx⟩ := count_exists_out hA₁
  refine ⟨fun i j h => ?_, fun i j h => ?_⟩
  · rw [Subsingleton.elim i 0, peelP_glue_out C₁ C₂ hx] at h
    exact Sum.inr_ne_inl h
  · rw [Subsingleton.elim i 0, peelP_glue_photon C₁ C₂ hw₁] at h
    exact Sum.inr_ne_inl h

/-! ### The bridge and the sides of the lines of the vertex piece -/

variable {w₂ : Wick.PhotonSlot (rightKinds κ e)} (hw : C₂.1.2 (.inl 1) = .inr w₂)
  (he : IsShuffle e) {b : PhotonLine (glueP e C₁ C₂)}
  (hbl : b.1 = psSplit κ e (.inl (extSlot C₁)) ∨ b.1 = psSplit κ e (.inr w₂))

include hw hbl in
/-- The ends of the bridge. -/
theorem peelP_ends :
    (b.1.1 = e (.inl (extSlot C₁).1) ∧ b.head.1 = e (.inr w₂.1)) ∨
      (b.1.1 = e (.inr w₂.1) ∧ b.head.1 = e (.inl (extSlot C₁).1)) := by
  rcases hbl with h | h
  · have hh : b.head = psSplit κ e (.inr w₂) := head_eq b (by rw [h]; exact glueP_ext_w₂ C₁ C₂ hw)
    exact .inl ⟨by rw [h]; rfl, by rw [hh]; rfl⟩
  · have hh : b.head = psSplit κ e (.inl (extSlot C₁)) :=
      head_eq b (by rw [h]; exact glueP_w₂_ext C₁ C₂ hw)
    exact .inr ⟨by rw [h]; rfl, by rw [hh]; rfl⟩

theorem peelP_bridge_eq : (lineSplitP C₁ C₂ hw he hbl).peelBridge = .inr b := rfl

theorem peelP_left_fermion (f : FermionLine C₁) :
    ∃ F, (lineSplitP C₁ C₂ hw he hbl).equiv (.inl (.inl f)) = .inl F := ⟨_, rfl⟩

theorem peelP_left_photon (p : PhotonLine C₁) :
    ∃ g, (lineSplitP C₁ C₂ hw he hbl).equiv (.inl (.inr p)) = .inr g := ⟨_, rfl⟩

theorem peelP_right_fermion (f : FermionLine C₂) :
    ∃ F, (lineSplitP C₁ C₂ hw he hbl).equiv (.inr (.inl (.inl f))) = .inl F := ⟨_, rfl⟩

theorem peelP_right_photon (p : PhotonLine C₂) :
    ∃ g, (lineSplitP C₁ C₂ hw he hbl).equiv (.inr (.inl (.inr p))) = .inr g := ⟨_, rfl⟩

/-- The sides of a line of the vertex piece, in the vertex piece. -/
theorem peelP_side_left (l₁ : Line C₁) {s v : Fin N₁} :
    ReflTransGen (Joined (glueP e C₁ C₂) {(lineSplitP C₁ C₂ hw he hbl).equiv (.inl l₁)})
        (e (.inl s)) (e (.inl v)) ↔ ReflTransGen (Joined C₁ {l₁}) s v := by
  rw [(lineSplitP C₁ C₂ hw he hbl).peelP_reach_left_iff (peelP_ends C₁ C₂ hw hbl),
    LineSplit.peelSet₁_singleton]

/-- **The side of a line of the vertex piece holds the vacuum polarization iff it holds
`extSlot C₁`.** -/
theorem peelP_side_right (hV₂ : VerticesConnected C₂) (l₁ : Line C₁) {s : Fin N₁}
    {r : Fin N₂} :
    ReflTransGen (Joined (glueP e C₁ C₂) {(lineSplitP C₁ C₂ hw he hbl).equiv (.inl l₁)})
        (e (.inl s)) (e (.inr r)) ↔ ReflTransGen (Joined C₁ {l₁}) s (extSlot C₁).1 := by
  set L := lineSplitP C₁ C₂ hw he hbl
  rw [L.peelP_reach_right_iff (peelP_ends C₁ C₂ hw hbl) hV₂
    (fun g hg => Sum.inr_ne_inl (L.equiv.injective (Set.mem_singleton_iff.1 hg)))
    (fun hg => Sum.inr_ne_inl (L.equiv.injective (Set.mem_singleton_iff.1 hg))),
    LineSplit.peelSet₁_singleton]

theorem peelP_fermAt_side (l₁ : Line C₁) (s : Fin N₁) :
    PeelPFermAt (glueP e C₁ C₂)
        (ReflTransGen (Joined (glueP e C₁ C₂) {(lineSplitP C₁ C₂ hw he hbl).equiv (.inl l₁)})
          (e (.inl s))) ↔ PeelPFermAt C₁ (ReflTransGen (Joined C₁ {l₁}) s) := by
  rw [peelP_fermAt_glue]
  have h : (fun v => ReflTransGen (Joined (glueP e C₁ C₂)
      {(lineSplitP C₁ C₂ hw he hbl).equiv (.inl l₁)}) (e (.inl s)) (e (.inl v))) =
      ReflTransGen (Joined C₁ {l₁}) s :=
    funext fun _ => propext (peelP_side_left C₁ C₂ hw he hbl l₁)
  rw [h]

include hw₁ in
theorem peelP_photonAt_side (hV₂ : VerticesConnected C₂) (l₁ : Line C₁) (s : Fin N₁) :
    (∃ j a, (glueP e C₁ C₂).1.2 (.inl j) = .inr a ∧
        ReflTransGen (Joined (glueP e C₁ C₂) {(lineSplitP C₁ C₂ hw he hbl).equiv (.inl l₁)})
          (e (.inl s)) a.1) ↔
      ∃ j a, C₁.1.2 (.inl j) = .inr a ∧ ReflTransGen (Joined C₁ {l₁}) s a.1 := by
  rw [peelP_photonAt_glue C₁ C₂ hw₁, peelP_photonAt_one, peelP_side_right C₁ C₂ hw he hbl hV₂]

include hw₁ in
/-- **The side of a line of the vertex piece carries an external in the glue iff it does in the
vertex piece.** -/
theorem peelP_extAt_side (hV₂ : VerticesConnected C₂) (l₁ : Line C₁) (s : Fin N₁) :
    PeelExtAt (glueP e C₁ C₂)
        (ReflTransGen (Joined (glueP e C₁ C₂) {(lineSplitP C₁ C₂ hw he hbl).equiv (.inl l₁)})
          (e (.inl s))) ↔ PeelExtAt C₁ (ReflTransGen (Joined C₁ {l₁}) s) := by
  rw [peelP_extAt_iff, peelP_extAt_iff, peelP_fermAt_side C₁ C₂ hw he hbl,
    peelP_photonAt_side C₁ C₂ hw₁ hw he hbl hV₂]

include hw₁ in
theorem peelP_noPhotonAt_side (hV₂ : VerticesConnected C₂) (l₁ : Line C₁) (s : Fin N₁) :
    PeelNoPhotonAt (glueP e C₁ C₂)
        (ReflTransGen (Joined (glueP e C₁ C₂) {(lineSplitP C₁ C₂ hw he hbl).equiv (.inl l₁)})
          (e (.inl s))) ↔ PeelNoPhotonAt C₁ (ReflTransGen (Joined C₁ {l₁}) s) := by
  rw [peelP_noPhotonAt_iff, peelP_noPhotonAt_iff, peelP_photonAt_side C₁ C₂ hw₁ hw he hbl hV₂]

end QED.GradedProof.X1C

end
