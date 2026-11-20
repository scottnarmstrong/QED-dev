/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CSplit
public import QED.GradedProof.X1CRoute
public import QED.TwoLoop.LoopBoundTwoExact

/-!
# (X₁) piece C: the routing of a contraction split along a bridge

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C2. A `LineSplit C C₁ C₂ u w` says that the internal lines of `C`
(on `κ`) are those of `C₁` (on the left piece of a split `e`), those of `C₂` (on the right piece)
and one more line, the bridge, from `u` to `w`, with the ends moved by `e`. This is the shape of
the three gluings (`glueIn`, `glueOut`, `glueP`).

* `splitMom S k₁ k₂ P`: the momentum assignment of `C` that is `k₁` on the lines of `C₁`, `k₂` on
  those of `C₂` and `P` on the bridge.
* `isConserved_splitMom`: it is conserved when `k₁`, `k₂` are and the external momenta of `C`
  match those of the pieces, the bridge read as an external line of each.
* `loopCount_split`: `loopCount C = loopCount C₁ + loopCount C₂` for connected `C`, `C₁`, `C₂`.
* `jointEnergyFirstIntegral_split` (**the routing of a split contraction**): the joint
  energy-first integral of any function of the line momenta of `C` at its canonical routing is
  the one at the concatenated canonical routings of the pieces, with the loop momenta of `C₁`
  first.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction Line loopCount lineMomentum₂ externalMomentum VerticesConnected
  chordMomentum)
open QED.TwoLoop.Routing (IsConserved inflow isConserved_lineMomentum₂)
open QED.TwoLoop.Relabel (IsIntAffine chordValues chordEquiv chordValues_lineMomentum₂)

variable {N N₁ N₂ : ℕ} {κ : Fin N → Wick.VertexKind} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}
  {nf nA nf₁ nA₁ nf₂ nA₂ : ℕ}

/-- The internal lines of `C` are those of `C₁`, those of `C₂` and a bridge from `u` to `w`, the
ends moved by `e`. -/
structure LineSplit (C : Contraction nf nA κ) (C₁ : Contraction nf₁ nA₁ (leftKinds κ e))
    (C₂ : Contraction nf₂ nA₂ (rightKinds κ e)) (u w : Fin N) where
  /-- The correspondence of the lines. -/
  equiv : Line C₁ ⊕ Line C₂ ⊕ Unit ≃ Line C
  ends_left : ∀ f, (equiv (.inl f)).ends = (e (.inl f.ends.1), e (.inl f.ends.2))
  ends_right : ∀ f, (equiv (.inr (.inl f))).ends = (e (.inr f.ends.1), e (.inr f.ends.2))
  ends_bridge : (equiv (.inr (.inr ()))).ends = (u, w)

namespace LineSplit

variable {C : Contraction nf nA κ} {C₁ : Contraction nf₁ nA₁ (leftKinds κ e)}
  {C₂ : Contraction nf₂ nA₂ (rightKinds κ e)} {u w : Fin N} (S : LineSplit C C₁ C₂ u w)

/-- The momentum assignment of `C` from assignments of the pieces and a bridge momentum. -/
def splitMom (k₁ : Line C₁ → Fin 4 → ℝ) (k₂ : Line C₂ → Fin 4 → ℝ) (P : Fin 4 → ℝ) :
    Line C → Fin 4 → ℝ :=
  fun f => Sum.elim k₁ (Sum.elim k₂ fun _ => P) (S.equiv.symm f)

@[simp] theorem splitMom_left (k₁ : Line C₁ → Fin 4 → ℝ) (k₂ : Line C₂ → Fin 4 → ℝ)
    (P : Fin 4 → ℝ) (f : Line C₁) : S.splitMom k₁ k₂ P (S.equiv (.inl f)) = k₁ f := by
  simp [splitMom]

@[simp] theorem splitMom_right (k₁ : Line C₁ → Fin 4 → ℝ) (k₂ : Line C₂ → Fin 4 → ℝ)
    (P : Fin 4 → ℝ) (f : Line C₂) : S.splitMom k₁ k₂ P (S.equiv (.inr (.inl f))) = k₂ f := by
  simp [splitMom]

@[simp] theorem splitMom_bridge (k₁ : Line C₁ → Fin 4 → ℝ) (k₂ : Line C₂ → Fin 4 → ℝ)
    (P : Fin 4 → ℝ) : S.splitMom k₁ k₂ P (S.equiv (.inr (.inr ()))) = P := by
  simp [splitMom]

theorem inflow_splitMom_left (k₁ : Line C₁ → Fin 4 → ℝ) (k₂ : Line C₂ → Fin 4 → ℝ)
    (P : Fin 4 → ℝ) (v : Fin N₁) :
    inflow (S.splitMom k₁ k₂ P) (e (.inl v)) = inflow k₁ v +
      ((if w = e (.inl v) then P else 0) - (if u = e (.inl v) then P else 0)) := by
  unfold inflow
  rw [← S.equiv.sum_comp, Fintype.sum_sum_type (α₁ := Line C₁),
    Fintype.sum_sum_type (α₁ := Line C₂)]
  simp only [splitMom_left, splitMom_right, splitMom_bridge, S.ends_left, S.ends_right,
    S.ends_bridge, Fintype.univ_unit, Finset.sum_singleton, EmbeddingLike.apply_eq_iff_eq,
    Sum.inl.injEq, reduceCtorEq, ite_false, sub_self, Finset.sum_const_zero, zero_add]

theorem inflow_splitMom_right (k₁ : Line C₁ → Fin 4 → ℝ) (k₂ : Line C₂ → Fin 4 → ℝ)
    (P : Fin 4 → ℝ) (v : Fin N₂) :
    inflow (S.splitMom k₁ k₂ P) (e (.inr v)) = inflow k₂ v +
      ((if w = e (.inr v) then P else 0) - (if u = e (.inr v) then P else 0)) := by
  unfold inflow
  rw [← S.equiv.sum_comp, Fintype.sum_sum_type (α₁ := Line C₁),
    Fintype.sum_sum_type (α₁ := Line C₂)]
  simp only [splitMom_left, splitMom_right, splitMom_bridge, S.ends_left, S.ends_right,
    S.ends_bridge, Fintype.univ_unit, Finset.sum_singleton, EmbeddingLike.apply_eq_iff_eq,
    Sum.inr.injEq, reduceCtorEq, ite_false, sub_self, Finset.sum_const_zero, zero_add]

/-- **The split assignment is conserved** when the assignments of the pieces are and the external
momenta of `C` at the vertices of each piece, corrected by the bridge, are those of the piece. -/
theorem isConserved_splitMom {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ}
    {pOut₁ pIn₁ : Fin nf₁ → Fin 4 → ℝ} {kIn₁ : Fin nA₁ → Fin 4 → ℝ}
    {pOut₂ pIn₂ : Fin nf₂ → Fin 4 → ℝ} {kIn₂ : Fin nA₂ → Fin 4 → ℝ}
    {k₁ : Line C₁ → Fin 4 → ℝ} {k₂ : Line C₂ → Fin 4 → ℝ} {P : Fin 4 → ℝ}
    (h₁ : IsConserved C₁ pOut₁ pIn₁ kIn₁ k₁) (h₂ : IsConserved C₂ pOut₂ pIn₂ kIn₂ k₂)
    (hext₁ : ∀ v, externalMomentum C pOut pIn kIn (e (.inl v)) +
      ((if w = e (.inl v) then P else 0) - (if u = e (.inl v) then P else 0)) =
        externalMomentum C₁ pOut₁ pIn₁ kIn₁ v)
    (hext₂ : ∀ v, externalMomentum C pOut pIn kIn (e (.inr v)) +
      ((if w = e (.inr v) then P else 0) - (if u = e (.inr v) then P else 0)) =
        externalMomentum C₂ pOut₂ pIn₂ kIn₂ v) :
    IsConserved C pOut pIn kIn (S.splitMom k₁ k₂ P) := by
  intro v
  obtain ⟨x, rfl⟩ := e.surjective v
  rcases x with v | v
  · have h := h₁ v
    rw [← hext₁ v] at h
    rw [inflow_splitMom_left]
    convert h using 1
    abel
  · have h := h₂ v
    rw [← hext₂ v] at h
    rw [inflow_splitMom_right]
    convert h using 1
    abel

include S in
theorem card_line : Nat.card (Line C) = Nat.card (Line C₁) + Nat.card (Line C₂) + 1 := by
  simp only [Nat.card_eq_fintype_card]
  rw [← Fintype.card_congr S.equiv, Fintype.card_sum (α := Line C₁),
    Fintype.card_sum (α := Line C₂), Fintype.card_unit, add_assoc]

include S in
/-- **The loops of a split contraction** are those of the pieces. -/
theorem loopCount_split (hV : VerticesConnected C) (hV₁ : VerticesConnected C₁)
    (hV₂ : VerticesConnected C₂) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) :
    loopCount C = loopCount C₁ + loopCount C₂ := by
  have hN : N = N₁ + N₂ := by
    simpa using Fintype.card_congr e.symm
  have h := QED.TwoLoop.LoopBoundTwo.loopCount_add_eq hV (by omega)
  have h₁ := QED.TwoLoop.LoopBoundTwo.loopCount_add_eq hV₁ hN₁
  have h₂ := QED.TwoLoop.LoopBoundTwo.loopCount_add_eq hV₂ hN₂
  have hc := S.card_line
  omega

end LineSplit

/-! ### Integer affine functions of a block of the loop momenta -/

theorem isIntAffine_comp_castAdd {L₁ L₂ : ℕ} {F : (Fin L₁ → Fin 4 → ℝ) → Fin 4 → ℝ}
    (hF : IsIntAffine F) :
    IsIntAffine fun ℓ : Fin (L₁ + L₂) → Fin 4 → ℝ => F fun s => ℓ (Fin.castAdd L₂ s) := by
  obtain ⟨m, b, h⟩ := hF
  refine ⟨Fin.append m 0, b, fun ℓ => ?_⟩
  simp only
  rw [h, Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem isIntAffine_comp_natAdd {L₁ L₂ : ℕ} {F : (Fin L₂ → Fin 4 → ℝ) → Fin 4 → ℝ}
    (hF : IsIntAffine F) :
    IsIntAffine fun ℓ : Fin (L₁ + L₂) → Fin 4 → ℝ => F fun s => ℓ (Fin.natAdd L₁ s) := by
  obtain ⟨m, b, h⟩ := hF
  refine ⟨Fin.append 0 m, b, fun ℓ => ?_⟩
  simp only
  rw [h, Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- The canonical routing gives the chord of rank `r` the loop momentum `ℓ r`. -/
theorem exists_line_lineMomentum₂ {M nf' nA' : ℕ} {κ' : Fin M → Wick.VertexKind}
    (C : Contraction nf' nA' κ') (pOut pIn : Fin nf' → Fin 4 → ℝ) (kIn : Fin nA' → Fin 4 → ℝ)
    (r : Fin (loopCount C)) :
    ∃ f : Line C, ∀ ℓ, lineMomentum₂ C pOut pIn kIn ℓ f = ℓ r := by
  refine ⟨((chordEquiv (C := C)).symm (Fin.cast rfl r)).1, fun ℓ => ?_⟩
  exact congrFun (chordValues_lineMomentum₂ rfl pOut pIn kIn ℓ) r

namespace LineSplit

variable {C : Contraction nf nA κ} {C₁ : Contraction nf₁ nA₁ (leftKinds κ e)}
  {C₂ : Contraction nf₂ nA₂ (rightKinds κ e)} {u w : Fin N} (S : LineSplit C C₁ C₂ u w)

/-- **The routing of a split contraction.** Let the pieces be connected with external momenta
summing to zero, and let the external momenta of `C`, corrected by the bridge momentum `P`, be
those of the pieces vertex by vertex. Then for every function `F` of the line momenta of `C`,
the joint energy-first integral at the canonical routing of `C` is the one at the split
assignment of the canonical routings of the pieces, the loop momenta of `C₁` first. -/
theorem jointEnergyFirstIntegral_split {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ}
    {pOut₁ pIn₁ : Fin nf₁ → Fin 4 → ℝ} {kIn₁ : Fin nA₁ → Fin 4 → ℝ}
    {pOut₂ pIn₂ : Fin nf₂ → Fin 4 → ℝ} {kIn₂ : Fin nA₂ → Fin 4 → ℝ} {P : Fin 4 → ℝ}
    (hV₁ : VerticesConnected C₁) (hV₂ : VerticesConnected C₂)
    (hs₁ : ∑ v, externalMomentum C₁ pOut₁ pIn₁ kIn₁ v = 0)
    (hs₂ : ∑ v, externalMomentum C₂ pOut₂ pIn₂ kIn₂ v = 0)
    (hext₁ : ∀ v, externalMomentum C pOut pIn kIn (e (.inl v)) +
      ((if w = e (.inl v) then P else 0) - (if u = e (.inl v) then P else 0)) =
        externalMomentum C₁ pOut₁ pIn₁ kIn₁ v)
    (hext₂ : ∀ v, externalMomentum C pOut pIn kIn (e (.inr v)) +
      ((if w = e (.inr v) then P else 0) - (if u = e (.inr v) then P else 0)) =
        externalMomentum C₂ pOut₂ pIn₂ kIn₂ v)
    (hL : loopCount C = loopCount C₁ + loopCount C₂) (F : (Line C → Fin 4 → ℝ) → ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegral (loopCount C₁ + loopCount C₂)
        (fun ℓ => F (lineMomentum₂ C pOut pIn kIn ℓ)) =
      QED.TwoLoop.jointEnergyFirstIntegral (loopCount C₁ + loopCount C₂) (fun ℓ =>
        F (S.splitMom (lineMomentum₂ C₁ pOut₁ pIn₁ kIn₁ fun s => ℓ (Fin.castAdd _ s))
          (lineMomentum₂ C₂ pOut₂ pIn₂ kIn₂ fun s => ℓ (Fin.natAdd _ s)) P)) := by
  refine jointEnergyFirstIntegral_eq_of_isConserved hL _ (fun ℓ => ?_) (fun f => ?_)
    (fun r => ?_) F
  · exact S.isConserved_splitMom (isConserved_lineMomentum₂ hV₁ hs₁ _)
      (isConserved_lineMomentum₂ hV₂ hs₂ _) hext₁ hext₂
  · obtain ⟨x, rfl⟩ := S.equiv.surjective f
    rcases x with f | f | ⟨⟩
    · simpa using isIntAffine_comp_castAdd (IsIntAffine.lineMomentum₂ C₁ pOut₁ pIn₁ kIn₁ f)
    · simpa using isIntAffine_comp_natAdd (IsIntAffine.lineMomentum₂ C₂ pOut₂ pIn₂ kIn₂ f)
    · exact ⟨0, P, fun ℓ => by simp [splitMom]⟩
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
    · obtain ⟨f, hf⟩ := exists_line_lineMomentum₂ C₁ pOut₁ pIn₁ kIn₁ r
      exact ⟨S.equiv (.inl f), fun ℓ => by simp [hf]⟩
    · obtain ⟨f, hf⟩ := exists_line_lineMomentum₂ C₂ pOut₂ pIn₂ kIn₂ r
      exact ⟨S.equiv (.inr (.inl f)), fun ℓ => by simp [hf]⟩

end LineSplit

end QED.GradedProof.X1C

end
