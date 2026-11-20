/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CCountInj
public import QED.GradedProof.X1CValIn

/-!
# (X₁) piece C: the weight of `glueIn` for the counting

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (counting).

* `LineSplit.count_verticesConnected`: a contraction whose lines are those of two connected
  pieces and a bridge between them is connected.
* `count_exists_out`, `count_exists_in`: the vertices of the outgoing and incoming externals of
  an attached contraction with one fermion line.
* **`countW_glueIn`**: the weight (fermionic sign times value) of `glueIn e C₁ C₂` is the sum over
  the bridge indices `z = (γ, δ)` of the products of the weights of the pieces, the bridge
  propagator `(1/i) S̃_{γδ}(r)` attached to the left piece: the hypothesis `hW` of
  `countSum_glue` for the in-leg peel. Only the attachment and connectivity of the pieces and
  the integrability (T₉′) of the piece integrands (`hT₁`, `hT₂`, in the form of
  `contractionValue_glueIn`) are assumed.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Params Contraction Line Joined loopCount lineMomentum₂ VerticesConnected
  ExternalsAttached fermionSign)
open QED.Graded
open Complex

variable {N N₁ N₂ : ℕ} {κ : Fin N → Wick.VertexKind} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}
  {nf nA nf₁ nA₁ nf₂ nA₂ : ℕ}

namespace LineSplit

variable {C : Contraction nf nA κ} {C₁ : Contraction nf₁ nA₁ (leftKinds κ e)}
  {C₂ : Contraction nf₂ nA₂ (rightKinds κ e)} {u w : Fin N} (S : LineSplit C C₁ C₂ u w)

theorem count_joined_symm {a b : Fin N} (h : Joined C ∅ a b) : Joined C ∅ b a := by
  obtain ⟨f, hf, h | h⟩ := h
  · exact ⟨f, hf, .inr h⟩
  · exact ⟨f, hf, .inl h⟩

theorem count_reach_symm {a b : Fin N} (h : Relation.ReflTransGen (Joined C ∅) a b) :
    Relation.ReflTransGen (Joined C ∅) b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single (count_joined_symm hbc)).trans ih

include S in
theorem count_reach_left {s t : Fin N₁} (h : Relation.ReflTransGen (Joined C₁ ∅) s t) :
    Relation.ReflTransGen (Joined C ∅) (e (.inl s)) (e (.inl t)) := by
  refine Relation.ReflTransGen.lift (fun s => e (.inl s)) (fun a b hab => ?_) _ _ h
  obtain ⟨f, -, hf⟩ := hab
  refine ⟨S.equiv (.inl f), Set.notMem_empty _, ?_⟩
  rw [S.ends_left]
  rcases hf with hf | hf <;> rw [hf]
  · exact .inl rfl
  · exact .inr rfl

include S in
theorem count_reach_right {s t : Fin N₂} (h : Relation.ReflTransGen (Joined C₂ ∅) s t) :
    Relation.ReflTransGen (Joined C ∅) (e (.inr s)) (e (.inr t)) := by
  refine Relation.ReflTransGen.lift (fun s => e (.inr s)) (fun a b hab => ?_) _ _ h
  obtain ⟨f, -, hf⟩ := hab
  refine ⟨S.equiv (.inr (.inl f)), Set.notMem_empty _, ?_⟩
  rw [S.ends_right]
  rcases hf with hf | hf <;> rw [hf]
  · exact .inl rfl
  · exact .inr rfl

include S in
/-- **Gluing connected pieces by a bridge gives a connected contraction.** -/
theorem count_verticesConnected {a₀ : Fin N₁} {c₀ : Fin N₂} (hu : u = e (.inr c₀))
    (hw : w = e (.inl a₀)) (hV₁ : VerticesConnected C₁) (hV₂ : VerticesConnected C₂) :
    VerticesConnected C := by
  have hb : Joined C ∅ u w := ⟨S.equiv (.inr (.inr ())), Set.notMem_empty _, .inl S.ends_bridge⟩
  have key : ∀ v, Relation.ReflTransGen (Joined C ∅) v w := by
    intro v
    obtain ⟨x, rfl⟩ := e.surjective v
    rcases x with s | s
    · rw [hw]
      exact S.count_reach_left (hV₁ s a₀)
    · refine (S.count_reach_right (hV₂ s c₀)).tail ?_
      rw [← hu]
      exact hb
  intro v v'
  exact (key v).trans (count_reach_symm (key v'))

end LineSplit

/-! ### The external vertices of an attached contraction -/

theorem count_exists_out {nA : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction 1 nA κ}
    (hA : ExternalsAttached C) : ∃ x, C.1.1 (.inl 0) = .inr x := by
  rcases h : C.1.1 (.inl 0) with i | x
  · exact absurd h (hA.1 0 i)
  · exact ⟨x, rfl⟩

theorem count_exists_in {nA : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction 1 nA κ}
    (hA : ExternalsAttached C) : ∃ a, C.1.1 (.inr a) = .inl 0 := by
  obtain ⟨z, hz⟩ := C.1.1.surjective (.inl 0)
  rcases z with i | a
  · exact absurd hz (hA.1 i 0)
  · exact ⟨a, hz⟩

/-! ### The weight of `glueIn` -/

/-- **The weight of `glueIn` is bilinear in the weights of the pieces** (hypothesis `hW` of
`countSum_glue`), with the bridge indices `z = (γ, δ)`. -/
theorem countW_glueIn {F : Type} [Fintype F] [DecidableEq F] (P : Params)
    (Φ : Lepton.Flavors F) (D : Counterterms F) (C₁ : Contraction 1 1 (leftKinds κ e))
    (C₂ : Contraction 1 0 (rightKinds κ e)) (he : IsShuffle e)
    (hV₁ : VerticesConnected C₁) (hV₂ : VerticesConnected C₂) (hA₁ : ExternalsAttached C₁)
    (hA₂ : ExternalsAttached C₂) {r' r q : Fin 4 → ℝ} (hmom : r' = r + q) (g : Grading κ)
    (αOut βIn μ : Fin 1 → Fin 4)
    (hT₁ : ∀ γ, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₁) fun ℓ =>
      twoPiInv (loopCount C₁) * regulatedAmplitude P Φ D C₁ (gradL κ e g) ![r] ![q]
        (lineMomentum₂ C₁ ![r'] ![r] ![q] ℓ) αOut ![γ] μ)
    (hT₂ : ∀ δ, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₂) fun ℓ =>
      twoPiInv (loopCount C₂) * regulatedAmplitude P Φ D C₂ (gradR κ e g) ![r] ![]
        (lineMomentum₂ C₂ ![r] ![r] ![] ℓ) ![δ] βIn ![]) :
    ((fermionSign (glueIn e C₁ C₂) : ℤ) : ℂ) *
        contractionValue P Φ D (glueIn e C₁ C₂) g ![r'] ![r] ![q] αOut βIn μ =
      ∑ z : Fin 4 × Fin 4,
        (((fermionSign C₁ : ℤ) : ℂ) *
            contractionValue P Φ D C₁ (gradL κ e g) ![r'] ![r] ![q] αOut ![z.1] μ *
          ((1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε r z.1 z.2)) *
        (((fermionSign C₂ : ℤ) : ℂ) *
          contractionValue P Φ D C₂ (gradR κ e g) ![r] ![r] ![] ![z.2] βIn ![]) := by
  obtain ⟨x, hx⟩ := count_exists_out hA₁
  obtain ⟨a, ha⟩ := count_exists_in hA₁
  obtain ⟨c, hc⟩ := count_exists_out hA₂
  obtain ⟨y, hy⟩ := count_exists_in hA₂
  have hV : VerticesConnected (glueIn e C₁ C₂) :=
    LineSplit.count_verticesConnected (lineSplitIn C₁ C₂ ha hc he) rfl rfl hV₁ hV₂
  rw [contractionValue_glueIn P Φ D C₁ C₂ ha hc he hx hy hV hV₁ hV₂ hA₁ hA₂ hmom g αOut βIn μ
    hT₁ hT₂, fermionSign_glueIn, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun δ _ => ?_
  push_cast
  ring

end QED.GradedProof.X1C

end
