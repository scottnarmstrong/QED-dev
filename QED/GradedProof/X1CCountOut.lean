/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CCountPeelIn
public import QED.GradedProof.X1CValOut

/-!
# (X₁) piece C: the out-leg peel at fixed `ε`, given the bijection

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (counting); the mirror of `X1CCountConn`, `X1CCountPeelIn`
for `glueOut`.

* `LineSplit.countOut_verticesConnected`: pieces connected and a bridge from the left piece to
  the right one ⇒ connected (the bridge orientation of `lineSplitOut`).
* `countW_glueOut`: the weight (fermionic sign times value) of `glueOut e C₁ C₂` is the sum over
  the bridge indices `z = (γ, δ)` of products of the weights of the pieces, the bridge
  propagator `(1/i) S̃_{γδ}(r')` attached to the self-energy piece.
* `countGlueOut_pieces_eq`: for a fixed split, `glueOut e C₁ C₂` determines `C₁` and `C₂`;
  `countGlueOut_injOn`: the hypothesis `hinj` from a function `peel` recovering the vertices of
  the self-energy piece.
* **`selectedPart_peelOut`**: for a class `H` of attached connected `(1,1)` contractions and an
  "out-leg reducible" predicate `Red`, given the bijection (`hmem`, `hinj`, `hsurj`) and the
  integrability (T₉′) of the pieces (`hT₁`, `hT₂`, in the form of `contractionValue_glueOut`),

  `H_K(r', r; αOut, βIn) = (H ∧ ¬Red)_K + ∑_{K₁+K₂=K} ∑_{γ δ}
    onePIPart(1,0)_{K₂}(r', r'; αOut, γ) · (1/i) S̃_{γδ}(r') · H_{K₁}(r', r; δ, βIn)`.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open Finset
open QED.WickModel (Params Contraction Joined loopCount lineMomentum₂ VerticesConnected
  ExternalsAttached IsOnePI fermionSign)
open QED.Graded
open Complex

variable {N N₁ N₂ : ℕ} {κ : Fin N → Wick.VertexKind} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}
  {nf nA nf₁ nA₁ nf₂ nA₂ : ℕ}

namespace LineSplit

variable {C : Contraction nf nA κ} {C₁ : Contraction nf₁ nA₁ (leftKinds κ e)}
  {C₂ : Contraction nf₂ nA₂ (rightKinds κ e)} {u w : Fin N} (S : LineSplit C C₁ C₂ u w)

include S in
/-- **Gluing connected pieces by a bridge gives a connected contraction** (bridge from the left
piece to the right piece). -/
theorem countOut_verticesConnected {a₀ : Fin N₁} {c₀ : Fin N₂} (hu : u = e (.inl a₀))
    (hw : w = e (.inr c₀)) (hV₁ : VerticesConnected C₁) (hV₂ : VerticesConnected C₂) :
    VerticesConnected C := by
  have hb : Joined C ∅ w u :=
    count_joined_symm ⟨S.equiv (.inr (.inr ())), Set.notMem_empty _, .inl S.ends_bridge⟩
  have key : ∀ v, Relation.ReflTransGen (Joined C ∅) v u := by
    intro v
    obtain ⟨x, rfl⟩ := e.surjective v
    rcases x with s | s
    · rw [hu]
      exact S.count_reach_left (hV₁ s a₀)
    · refine (S.count_reach_right (hV₂ s c₀)).tail ?_
      rw [← hw]
      exact hb
  intro v v'
  exact (key v).trans (count_reach_symm (key v'))

end LineSplit

/-! ### The weight of `glueOut` -/

/-- **The weight of `glueOut` is bilinear in the weights of the pieces** (hypothesis `hW` of
`countSum_glue` for the out-leg peel), with the bridge indices `z = (γ, δ)`. -/
theorem countW_glueOut {F : Type} [Fintype F] [DecidableEq F] (P : Params)
    (Φ : Lepton.Flavors F) (D : Counterterms F) (C₁ : Contraction 1 1 (leftKinds κ e))
    (C₂ : Contraction 1 0 (rightKinds κ e)) (he : IsShuffle e)
    (hV₁ : VerticesConnected C₁) (hV₂ : VerticesConnected C₂) (hA₁ : ExternalsAttached C₁)
    (hA₂ : ExternalsAttached C₂) {r' r q : Fin 4 → ℝ} (hmom : r' = r + q) (g : Grading κ)
    (αOut βIn μ : Fin 1 → Fin 4)
    (hT₁ : ∀ δ, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₁) fun ℓ =>
      twoPiInv (loopCount C₁) * regulatedAmplitude P Φ D C₁ (gradL κ e g) ![r] ![q]
        (lineMomentum₂ C₁ ![r'] ![r] ![q] ℓ) ![δ] βIn μ)
    (hT₂ : ∀ γ, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₂) fun ℓ =>
      twoPiInv (loopCount C₂) * regulatedAmplitude P Φ D C₂ (gradR κ e g) ![r'] ![]
        (lineMomentum₂ C₂ ![r'] ![r'] ![] ℓ) αOut ![γ] ![]) :
    ((fermionSign (glueOut e C₁ C₂) : ℤ) : ℂ) *
        contractionValue P Φ D (glueOut e C₁ C₂) g ![r'] ![r] ![q] αOut βIn μ =
      ∑ z : Fin 4 × Fin 4,
        (((fermionSign C₁ : ℤ) : ℂ) *
            contractionValue P Φ D C₁ (gradL κ e g) ![r'] ![r] ![q] ![z.2] βIn μ) *
        (((fermionSign C₂ : ℤ) : ℂ) *
            contractionValue P Φ D C₂ (gradR κ e g) ![r'] ![r'] ![] αOut ![z.1] ![] *
          ((1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε r' z.1 z.2)) := by
  obtain ⟨a, ha⟩ := count_exists_out hA₁
  obtain ⟨y, hy⟩ := count_exists_in hA₁
  obtain ⟨x, hx⟩ := count_exists_out hA₂
  obtain ⟨c, hc⟩ := count_exists_in hA₂
  have hV : VerticesConnected (glueOut e C₁ C₂) :=
    (lineSplitOut C₁ C₂ ha hc he).countOut_verticesConnected rfl rfl hV₁ hV₂
  rw [contractionValue_glueOut P Φ D C₁ C₂ ha hc he hx hy hV hV₁ hV₂ hA₁ hA₂ hmom g αOut βIn μ
    hT₁ hT₂, fermionSign_glueOut, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun δ _ => ?_
  push_cast
  ring

/-! ### The pieces of `glueOut` -/

section Pieces

theorem count_fvSplit_inr_ne_fL (t : Wick.FermionVertex (rightKinds κ e))
    (y : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e)) :
    (Sum.inr (fvSplit κ e (.inr t)) : Fin 1 ⊕ Wick.FermionVertex κ) ≠ fL κ e 1 (.inl y) := by
  rcases y with i | s
  · exact Sum.inr_ne_inl
  · rw [fL_inl_inr]
    intro h
    exact Sum.inr_ne_inl ((fvSplit κ e).injective (Sum.inr_injective h))

/-- The value of the right pairing of `glueOut` on a right field, read off from the glue. -/
theorem count_glueOut_right_eq {nA : ℕ} {C₁ C₁' : Contraction 1 nA (leftKinds κ e)}
    {C₂ C₂' : Contraction 1 0 (rightKinds κ e)}
    (h : (glueOut e C₁ C₂).1.1 = (glueOut e C₁' C₂').1.1)
    (x : Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e)) : C₂.1.1 x = C₂'.1.1 x := by
  have hx := congrArg (fun σ => σ (fR κ e 1 (.inr x))) h
  rcases h₁ : C₂.1.1 x with i | t <;> rcases h₂ : C₂'.1.1 x with i' | t'
  · rw [Subsingleton.elim i i']
  · rw [glueOut_right_ext C₁ C₂ h₁, glueOut_right C₁' C₂' h₂] at hx
    exact absurd hx.symm (count_fvSplit_inr_ne_fL t' _)
  · rw [glueOut_right C₁ C₂ h₁, glueOut_right_ext C₁' C₂' h₂] at hx
    exact absurd hx (count_fvSplit_inr_ne_fL t _)
  · rw [glueOut_right C₁ C₂ h₁, glueOut_right C₁' C₂' h₂] at hx
    exact congrArg Sum.inr (Sum.inr_injective ((fvSplit κ e).injective (Sum.inr_injective hx)))

/-- **For a fixed split, `glueOut` determines its pieces.** -/
theorem countGlueOut_pieces_eq {nA : ℕ} {C₁ C₁' : Contraction 1 nA (leftKinds κ e)}
    {C₂ C₂' : Contraction 1 0 (rightKinds κ e)} (h : glueOut e C₁ C₂ = glueOut e C₁' C₂') :
    C₁ = C₁' ∧ C₂ = C₂' := by
  have hf : (glueOut e C₁ C₂).1.1 = (glueOut e C₁' C₂').1.1 := by rw [h]
  have hp : gluePhotons e C₁.1.2 C₂.1.2 = gluePhotons e C₁'.1.2 C₂'.1.2 :=
    congrArg (fun C : Contraction 1 nA κ => C.1.2) h
  obtain ⟨hp₁, hp₂⟩ := count_dsum_inj _ hp
  have h₂ : C₂.1.1 = C₂'.1.1 := Equiv.ext (count_glueOut_right_eq hf)
  have h₁ : C₁.1.1 = C₁'.1.1 := by
    refine Equiv.ext ?_
    rintro (i | t)
    · obtain ⟨x, hx⟩ := C₂.1.1.surjective (.inl i)
      have hx' : C₂'.1.1 x = .inl i := by rw [← h₂]; exact hx
      have := congrArg (fun σ => σ (fR κ e 1 (.inr x))) hf
      rw [glueOut_right_ext C₁ C₂ hx, glueOut_right_ext C₁' C₂' hx'] at this
      exact Sum.inl_injective ((fL κ e 1).injective this)
    · have := congrArg (fun σ => σ (.inr (fvSplit κ e (.inl t)))) hf
      rw [glueOut_left, glueOut_left] at this
      exact Sum.inl_injective ((fL κ e 1).injective this)
  exact ⟨Subtype.ext (Prod.ext h₁ hp₁), Subtype.ext (Prod.ext h₂ hp₂)⟩

end Pieces

/-- The glue map of the out-leg peel. -/
abbrev countGlueOutMap : ∀ {N N₁ N₂ : ℕ} {κ : Fin N → Wick.VertexKind}
    (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N), Contraction 1 1 (leftKinds κ e) →
      Contraction 1 0 (rightKinds κ e) → Contraction 1 1 κ :=
  fun e C₁ C₂ => glueOut e C₁ C₂

/-- **Injectivity of the out-leg glue from the peeled set** (mirror of `countGlueIn_injOn`). -/
theorem countGlueOut_injOn {κ : Fin N → Wick.VertexKind} (SelH : CountSel 1 1)
    (g : Grading κ) (peel : Contraction 1 1 κ → Finset (Fin N))
    (hpeel : ∀ x ∈ countIdxSet SelH (countOnePI (nf := 1) (nA := 0)) g,
      peel (glueOut x.2.1 x.2.2.1 x.2.2.2) = (countLeftImage x.2.1)ᶜ) :
    Set.InjOn (fun x : CountIdx 1 1 1 0 κ => glueOut x.2.1 x.2.2.1 x.2.2.2)
      (countIdxSet SelH (countOnePI (nf := 1) (nA := 0)) g) := by
  rintro ⟨p, e, C₁, C₂⟩ hx ⟨p', e', C₁', C₂'⟩ hy h
  have h' : glueOut e C₁ C₂ = glueOut e' C₁' C₂' := h
  have hx' := mem_countIdxSet.1 hx
  have hy' := mem_countIdxSet.1 hy
  have h₁ : peel (glueOut e C₁ C₂) = (countLeftImage e)ᶜ := hpeel ⟨p, e, C₁, C₂⟩ hx
  have h₂ : peel (glueOut e' C₁' C₂') = (countLeftImage e')ᶜ := hpeel ⟨p', e', C₁', C₂'⟩ hy
  have himg : countLeftImage e = countLeftImage e' := by
    rw [h', h₂] at h₁
    exact compl_injective h₁.symm
  have hp : p = p' := by
    have h₁ := card_countLeftImage e
    rw [himg, card_countLeftImage] at h₁
    exact Prod.ext h₁.symm (by simp only at hx' hy'; omega)
  subst hp
  have he : e = e' := countShuffle_ext hx'.1 hx'.2.1 hy'.2.1 himg
  subst he
  obtain ⟨rfl, rfl⟩ := countGlueOut_pieces_eq h'
  rfl

variable {F : Type} [Fintype F] [DecidableEq F] (P : Params) (Φ : Lepton.Flavors F)
  (D : Counterterms F)

/-- The weight of the vertex piece of the out-leg peel. -/
noncomputable def countWOut₁ (r' r q : Fin 4 → ℝ) (βIn μ : Fin 1 → Fin 4) (z : Fin 4 × Fin 4) :
    CountWt 1 1 := fun C₁ g₁ => ((fermionSign C₁ : ℤ) : ℂ) *
  contractionValue P Φ D C₁ g₁ ![r'] ![r] ![q] ![z.2] βIn μ

/-- The weight of the self-energy piece of the out-leg peel, with the bridge propagator. -/
noncomputable def countWOut₂ (r' : Fin 4 → ℝ) (αOut : Fin 1 → Fin 4) (z : Fin 4 × Fin 4) :
    CountWt 1 0 := fun C₂ g₂ => ((fermionSign C₂ : ℤ) : ℂ) *
  contractionValue P Φ D C₂ g₂ ![r'] ![r'] ![] αOut ![z.1] ![] *
    ((1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε r' z.1 z.2)

/-- **The out-leg peel** `H = J + Σ · (1/i) S̃ · H` at fixed `ε`, given the bijection. -/
theorem selectedPart_peelOut (SelH Red : CountSel 1 1)
    (hH : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) (g : Grading κ),
      SelH C g → ExternalsAttached C ∧ VerticesConnected C) (K : ℕ)
    (hmem : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = K →
      ∀ x ∈ countIdxSet SelH (countOnePI (nf := 1) (nA := 0)) g,
        SelH (glueOut x.2.1 x.2.2.1 x.2.2.2) g ∧ Red (glueOut x.2.1 x.2.2.1 x.2.2.2) g)
    (hinj : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = K →
      Set.InjOn (fun x : CountIdx 1 1 1 0 κ => glueOut x.2.1 x.2.2.1 x.2.2.2)
        (countIdxSet SelH (countOnePI (nf := 1) (nA := 0)) g))
    (hsurj : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = K →
      ∀ C : Contraction 1 1 κ, SelH C g → Red C g →
        ∃ x ∈ countIdxSet SelH (countOnePI (nf := 1) (nA := 0)) g,
          glueOut x.2.1 x.2.2.1 x.2.2.2 = C)
    {r' r q : Fin 4 → ℝ} (hmom : r' = r + q) (αOut βIn μ : Fin 1 → Fin 4)
    (hT₁ : ∀ {N₁ : ℕ} (κ₁ : Fin N₁ → Wick.VertexKind) (g₁ : Grading κ₁)
      (C₁ : Contraction 1 1 κ₁), SelH C₁ g₁ → gradedOrder κ₁ g₁ ≤ K →
      ∀ δ, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₁) fun ℓ =>
        twoPiInv (loopCount C₁) * regulatedAmplitude P Φ D C₁ g₁ ![r] ![q]
          (lineMomentum₂ C₁ ![r'] ![r] ![q] ℓ) ![δ] βIn μ)
    (hT₂ : ∀ {N₂ : ℕ} (κ₂ : Fin N₂ → Wick.VertexKind) (g₂ : Grading κ₂)
      (C₂ : Contraction 1 0 κ₂), IsOnePI C₂ → gradedOrder κ₂ g₂ ≤ K →
      ∀ γ, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₂) fun ℓ =>
        twoPiInv (loopCount C₂) * regulatedAmplitude P Φ D C₂ g₂ ![r'] ![]
          (lineMomentum₂ C₂ ![r'] ![r'] ![] ℓ) αOut ![γ] ![]) :
    selectedPart P Φ D 1 1 SelH K ![r'] ![r] ![q] αOut βIn μ =
      selectedPart P Φ D 1 1 (fun C g => SelH C g ∧ ¬ Red C g) K ![r'] ![r] ![q] αOut βIn μ +
      ∑ p ∈ antidiagonal K, ∑ γ, ∑ δ,
        onePIPart P Φ D 1 0 p.2 ![r'] ![r'] ![] αOut ![γ] ![] *
          ((1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε r' γ δ) *
          selectedPart P Φ D 1 1 SelH p.1 ![r'] ![r] ![q] ![δ] βIn μ := by
  simp only [selectedPart_eq_countSum, onePIPart]
  rw [countSum_split SelH Red]
  congr 1
  rw [countSum_glue (fun C g => SelH C g ∧ Red C g) SelH countOnePI _
    (countWOut₁ P Φ D r' r q βIn μ) (countWOut₂ P Φ D r' αOut) countGlueOutMap K
    (fun κ g hg f => count_sum_of_bij _ _ _ countGlueOutMap g (hmem κ g hg) (hinj κ g hg)
      (fun C hC => hsurj κ g hg C hC.1 hC.2) f) ?_]
  · refine sum_congr rfl fun p _ => ?_
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun γ _ => sum_congr rfl fun δ _ => ?_
    exact (mul_comm _ _).trans (congrArg (· * _) (countSum_mul_const countOnePI
      (fun C₂ g₂ => ((fermionSign C₂ : ℤ) : ℂ) *
        contractionValue P Φ D C₂ g₂ ![r'] ![r'] ![] αOut ![γ] ![]) _ p.2))
  · intro N N₁ N₂ κ e g C₁ C₂ he hg h₁ h₂
    have hle := gradedOrder_split κ e g
    obtain ⟨hA₁, hV₁⟩ := hH C₁ _ h₁
    exact countW_glueOut P Φ D C₁ C₂ he hV₁ h₂.2.1 hA₁ h₂.1 hmom g αOut βIn μ
      (hT₁ _ _ C₁ h₁ (by omega)) (hT₂ _ _ C₂ h₂ (by omega))

end QED.GradedProof.X1C

end
