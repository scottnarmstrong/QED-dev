/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CCountOut
public import QED.GradedProof.X1CValP

/-!
# (X₁) piece C: the photon-leg peel at fixed `ε`, given the bijection

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (counting); the mirror of `X1CCountConn`, `X1CCountPeelIn`
for `glueP`.

* `countP_verticesConnected`: `glueP` of connected pieces is connected (either orientation of
  the bridge photon line).
* `countW_glueP`: the weight (fermionic sign times value) of `glueP e C₁ C₂` is the sum over the
  bridge Lorentz indices `z = (ν, ρ)` of products of the weights of the pieces, the bridge
  propagator `(1/i) D̃_{νρ}(q)` attached to the vertex piece.
* `countGlueP_pieces_eq`: for a fixed split, `glueP e C₁ C₂` determines `C₁` and `C₂` (the
  field `extSlot C₁` is the only field of `C₁` not paired with a field of `C₁` in the glue);
  `countGlueP_injOn`: the hypothesis `hinj` from a function `peel` recovering the vertices of
  the vacuum-polarization piece.
* **`selectedPart_peelP`**: for a class `J` of attached connected `(1,1)` contractions and a
  "photon-leg reducible" predicate `Red`, given the bijection (`hmem`, `hinj`, `hsurj`) and the
  integrability (T₉′) of the pieces (`hT₁`, `hT₂`, in the form of `contractionValue_glueP`),

  `J_K(r', r, q; μ) = (J ∧ ¬Red)_K + ∑_{K₁+K₂=K} ∑_{ν ρ} J_{K₁}(r', r, q; ν) · (1/i) D̃_{νρ}(q) ·
    onePIPart(0,2)_{K₂}(q, -q; μ₀, ρ)`.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open Finset
open QED.WickModel (Params Contraction PhotonLine loopCount lineMomentum₂ VerticesConnected
  ExternalsAttached IsOnePI fermionSign)
open QED.TwoLoop.Enumeration (head_eq)
open QED.Graded
open Complex

variable {N N₁ N₂ : ℕ} {κ : Fin N → Wick.VertexKind} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}

/-- **`glueP` of connected pieces is connected.** -/
theorem countP_verticesConnected (C₁ : Contraction 1 1 (leftKinds κ e))
    (C₂ : Contraction 0 2 (rightKinds κ e)) {w₂ : Wick.PhotonSlot (rightKinds κ e)}
    (hw : C₂.1.2 (.inl 1) = .inr w₂) (he : IsShuffle e) (hV₁ : VerticesConnected C₁)
    (hV₂ : VerticesConnected C₂) : VerticesConnected (glueP e C₁ C₂) := by
  obtain ⟨b, hb⟩ := exists_bridgeP C₁ C₂ hw
  rcases hb with hb' | hb'
  · have hh : b.head = psSplit κ e (.inr w₂) :=
      head_eq b (by rw [hb']; exact glueP_ext_w₂ C₁ C₂ hw)
    exact (lineSplitP C₁ C₂ hw he (.inl hb')).countOut_verticesConnected
      (a₀ := (extSlot C₁).1) (c₀ := w₂.1) (by rw [hb']; rfl) (by rw [hh]; rfl) hV₁ hV₂
  · have hh : b.head = psSplit κ e (.inl (extSlot C₁)) :=
      head_eq b (by rw [hb']; exact glueP_w₂_ext C₁ C₂ hw)
    exact (lineSplitP C₁ C₂ hw he (.inr hb')).count_verticesConnected
      (a₀ := (extSlot C₁).1) (c₀ := w₂.1) (by rw [hb']; rfl) (by rw [hh]; rfl) hV₁ hV₂

theorem count_exists_photon {nf N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf 2 κ}
    (hA : ExternalsAttached C) (i : Fin 2) : ∃ w, C.1.2 (.inl i) = .inr w := by
  rcases h : C.1.2 (.inl i) with j | w
  · exact absurd h (hA.2 i j)
  · exact ⟨w, rfl⟩

/-! ### The weight of `glueP` -/

/-- **The weight of `glueP` is bilinear in the weights of the pieces** (hypothesis `hW` of
`countSum_glue` for the photon-leg peel), with the bridge indices `z = (ν, ρ)`. -/
theorem countW_glueP {F : Type} [Fintype F] [DecidableEq F] (P : Params)
    (Φ : Lepton.Flavors F) (D : Counterterms F) (C₁ : Contraction 1 1 (leftKinds κ e))
    (C₂ : Contraction 0 2 (rightKinds κ e)) (he : IsShuffle e)
    (hV₁ : VerticesConnected C₁) (hV₂ : VerticesConnected C₂) (hA₁ : ExternalsAttached C₁)
    (hA₂ : ExternalsAttached C₂) {r' r q : Fin 4 → ℝ} (hmom : r' = r + q) (g : Grading κ)
    (αOut βIn μ : Fin 1 → Fin 4)
    (hT₁ : ∀ ν, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₁) fun ℓ =>
      twoPiInv (loopCount C₁) * regulatedAmplitude P Φ D C₁ (gradL κ e g) ![r] ![q]
        (lineMomentum₂ C₁ ![r'] ![r] ![q] ℓ) αOut βIn ![ν])
    (hT₂ : ∀ ρ, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₂) fun ℓ =>
      twoPiInv (loopCount C₂) * regulatedAmplitude P Φ D C₂ (gradR κ e g) ![] ![q, -q]
        (lineMomentum₂ C₂ ![] ![] ![q, -q] ℓ) ![] ![] ![μ 0, ρ]) :
    ((fermionSign (glueP e C₁ C₂) : ℤ) : ℂ) *
        contractionValue P Φ D (glueP e C₁ C₂) g ![r'] ![r] ![q] αOut βIn μ =
      ∑ z : Fin 4 × Fin 4,
        (((fermionSign C₁ : ℤ) : ℂ) *
            contractionValue P Φ D C₁ (gradL κ e g) ![r'] ![r] ![q] αOut βIn ![z.1] *
          ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε q z.1 z.2)) *
        (((fermionSign C₂ : ℤ) : ℂ) *
          contractionValue P Φ D C₂ (gradR κ e g) ![] ![] ![q, -q] ![] ![] ![μ 0, z.2]) := by
  obtain ⟨x, hx⟩ := count_exists_out hA₁
  obtain ⟨y, hy⟩ := count_exists_in hA₁
  obtain ⟨w₁, hw₁⟩ := count_exists_photon hA₂ 0
  obtain ⟨w₂, hw⟩ := count_exists_photon hA₂ 1
  have hV : VerticesConnected (glueP e C₁ C₂) := countP_verticesConnected C₁ C₂ hw he hV₁ hV₂
  rw [contractionValue_glueP P Φ D C₁ C₂ hw₁ hw he hx hy hV hV₁ hV₂ hA₁ hA₂ hmom g αOut βIn μ
    hT₁ hT₂, fermionSign_glueP, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  push_cast
  ring

/-! ### The pieces of `glueP` -/

section Pieces

variable (e)

theorem count_photonModel_ext (C₁ : Contraction 1 1 (leftKinds κ e))
    (C₂ : Contraction 0 2 (rightKinds κ e)) (s' : Wick.PhotonSlot (leftKinds κ e)) :
    photonModel e C₁ C₂ (.inr (.inl (extSlot C₁))) ≠ .inr (.inl s') := by
  simp only [photonModel, ite_true]
  rcases h : C₂.1.2 (.inl 1) with i | s
  · fin_cases i
    · simp [liftR]
    · exact absurd h (C₂.2 _).2
  · simp [liftR]

theorem count_photonModel_left (C₁ : Contraction 1 1 (leftKinds κ e))
    (C₂ : Contraction 0 2 (rightKinds κ e)) {s : Wick.PhotonSlot (leftKinds κ e)}
    (hs : s ≠ extSlot C₁) :
    ∃ s', C₁.1.2 (.inr s) = .inr s' ∧ photonModel e C₁ C₂ (.inr (.inl s)) = .inr (.inl s') := by
  obtain ⟨s', h, -, -⟩ := photonPair_left e C₁ hs
  exact ⟨s', h, photonModel_left e C₁ C₂ hs h⟩

variable {e}

/-- **For a fixed split, `glueP` determines its pieces.** -/
theorem countGlueP_pieces_eq {C₁ C₁' : Contraction 1 1 (leftKinds κ e)}
    {C₂ C₂' : Contraction 0 2 (rightKinds κ e)} (h : glueP e C₁ C₂ = glueP e C₁' C₂') :
    C₁ = C₁' ∧ C₂ = C₂' := by
  have hf : dsum (fL κ e 1) C₁.1.1 C₂.1.1 = dsum (fL κ e 1) C₁'.1.1 C₂'.1.1 :=
    congrArg (fun C : Contraction 1 1 κ => C.1.1) h
  obtain ⟨hf₁, hf₂⟩ := count_dsum_inj _ hf
  have hm : ∀ x, photonModel e C₁ C₂ x = photonModel e C₁' C₂' x := fun x => by
    have h1 := gluePPhotons_apply e C₁ C₂ x
    rw [show gluePPhotons e C₁ C₂ = gluePPhotons e C₁' C₂' from
      congrArg (fun C : Contraction 1 1 κ => C.1.2) h, gluePPhotons_apply] at h1
    exact ((pModelEquiv e).injective h1).symm
  have hext : extSlot C₁ = extSlot C₁' := by
    by_contra hne
    obtain ⟨s', -, hs'⟩ := count_photonModel_left e C₁' C₂' hne
    exact count_photonModel_ext e C₁ C₂ s' ((hm _).trans hs')
  have hp₁ : C₁.1.2 = C₁'.1.2 := by
    refine Equiv.ext ?_
    rintro (i | s)
    · rw [Subsingleton.elim i 0, extSlot_spec, extSlot_spec, hext]
    · by_cases hs : s = extSlot C₁
      · rw [hs, extSlot_spec', hext, extSlot_spec']
      · have hs₂ : s ≠ extSlot C₁' := hext ▸ hs
        obtain ⟨s₁, h₁, hm₁⟩ := count_photonModel_left e C₁ C₂ hs
        obtain ⟨s₂, h₂, hm₂⟩ := count_photonModel_left e C₁' C₂' hs₂
        have := (hm₁.symm.trans (hm _)).trans hm₂
        rw [h₁, h₂, Sum.inl_injective (Sum.inr_injective this)]
  have hp₂ : C₂.1.2 = C₂'.1.2 := by
    refine Equiv.ext fun y => ?_
    have h1 := hm (liftR e (extSlot C₁) y)
    rw [photonModel_liftR, hext, photonModel_liftR] at h1
    exact liftR_injective e _ h1
  exact ⟨Subtype.ext (Prod.ext hf₁ hp₁), Subtype.ext (Prod.ext hf₂ hp₂)⟩

end Pieces

/-- The glue map of the photon-leg peel. -/
abbrev countGluePMap : ∀ {N N₁ N₂ : ℕ} {κ : Fin N → Wick.VertexKind}
    (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N), Contraction 1 1 (leftKinds κ e) →
      Contraction 0 2 (rightKinds κ e) → Contraction 1 1 κ :=
  fun e C₁ C₂ => glueP e C₁ C₂

/-- **Injectivity of the photon-leg glue from the peeled set** (mirror of
`countGlueIn_injOn`). -/
theorem countGlueP_injOn {κ : Fin N → Wick.VertexKind} (SelJ : CountSel 1 1)
    (g : Grading κ) (peel : Contraction 1 1 κ → Finset (Fin N))
    (hpeel : ∀ x ∈ countIdxSet SelJ (countOnePI (nf := 0) (nA := 2)) g,
      peel (glueP x.2.1 x.2.2.1 x.2.2.2) = (countLeftImage x.2.1)ᶜ) :
    Set.InjOn (fun x : CountIdx 1 1 0 2 κ => glueP x.2.1 x.2.2.1 x.2.2.2)
      (countIdxSet SelJ (countOnePI (nf := 0) (nA := 2)) g) := by
  rintro ⟨p, e, C₁, C₂⟩ hx ⟨p', e', C₁', C₂'⟩ hy h
  have h' : glueP e C₁ C₂ = glueP e' C₁' C₂' := h
  have hx' := mem_countIdxSet.1 hx
  have hy' := mem_countIdxSet.1 hy
  have h₁ : peel (glueP e C₁ C₂) = (countLeftImage e)ᶜ := hpeel ⟨p, e, C₁, C₂⟩ hx
  have h₂ : peel (glueP e' C₁' C₂') = (countLeftImage e')ᶜ := hpeel ⟨p', e', C₁', C₂'⟩ hy
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
  obtain ⟨rfl, rfl⟩ := countGlueP_pieces_eq h'
  rfl

variable {F : Type} [Fintype F] [DecidableEq F] (P : Params) (Φ : Lepton.Flavors F)
  (D : Counterterms F)

/-- The weight of the vertex piece of the photon-leg peel, with the bridge propagator. -/
noncomputable def countWP₁ (r' r q : Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) (z : Fin 4 × Fin 4) :
    CountWt 1 1 := fun C₁ g₁ => ((fermionSign C₁ : ℤ) : ℂ) *
  contractionValue P Φ D C₁ g₁ ![r'] ![r] ![q] αOut βIn ![z.1] *
    ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε q z.1 z.2)

/-- The weight of the vacuum-polarization piece of the photon-leg peel. -/
noncomputable def countWP₂ (q : Fin 4 → ℝ) (μ : Fin 1 → Fin 4) (z : Fin 4 × Fin 4) :
    CountWt 0 2 := fun C₂ g₂ => ((fermionSign C₂ : ℤ) : ℂ) *
  contractionValue P Φ D C₂ g₂ ![] ![] ![q, -q] ![] ![] ![μ 0, z.2]

/-- **The photon-leg peel** `J = V + J · (1/i) D̃ · Π` at fixed `ε`, given the bijection. -/
theorem selectedPart_peelP (SelJ Red : CountSel 1 1)
    (hJ : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) (g : Grading κ),
      SelJ C g → ExternalsAttached C ∧ VerticesConnected C) (K : ℕ)
    (hmem : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = K →
      ∀ x ∈ countIdxSet SelJ (countOnePI (nf := 0) (nA := 2)) g,
        SelJ (glueP x.2.1 x.2.2.1 x.2.2.2) g ∧ Red (glueP x.2.1 x.2.2.1 x.2.2.2) g)
    (hinj : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = K →
      Set.InjOn (fun x : CountIdx 1 1 0 2 κ => glueP x.2.1 x.2.2.1 x.2.2.2)
        (countIdxSet SelJ (countOnePI (nf := 0) (nA := 2)) g))
    (hsurj : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = K →
      ∀ C : Contraction 1 1 κ, SelJ C g → Red C g →
        ∃ x ∈ countIdxSet SelJ (countOnePI (nf := 0) (nA := 2)) g,
          glueP x.2.1 x.2.2.1 x.2.2.2 = C)
    {r' r q : Fin 4 → ℝ} (hmom : r' = r + q) (αOut βIn μ : Fin 1 → Fin 4)
    (hT₁ : ∀ {N₁ : ℕ} (κ₁ : Fin N₁ → Wick.VertexKind) (g₁ : Grading κ₁)
      (C₁ : Contraction 1 1 κ₁), SelJ C₁ g₁ → gradedOrder κ₁ g₁ ≤ K →
      ∀ ν, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₁) fun ℓ =>
        twoPiInv (loopCount C₁) * regulatedAmplitude P Φ D C₁ g₁ ![r] ![q]
          (lineMomentum₂ C₁ ![r'] ![r] ![q] ℓ) αOut βIn ![ν])
    (hT₂ : ∀ {N₂ : ℕ} (κ₂ : Fin N₂ → Wick.VertexKind) (g₂ : Grading κ₂)
      (C₂ : Contraction 0 2 κ₂), IsOnePI C₂ → gradedOrder κ₂ g₂ ≤ K →
      ∀ ρ, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₂) fun ℓ =>
        twoPiInv (loopCount C₂) * regulatedAmplitude P Φ D C₂ g₂ ![] ![q, -q]
          (lineMomentum₂ C₂ ![] ![] ![q, -q] ℓ) ![] ![] ![μ 0, ρ]) :
    selectedPart P Φ D 1 1 SelJ K ![r'] ![r] ![q] αOut βIn μ =
      selectedPart P Φ D 1 1 (fun C g => SelJ C g ∧ ¬ Red C g) K ![r'] ![r] ![q] αOut βIn μ +
      ∑ p ∈ antidiagonal K, ∑ ν, ∑ ρ,
        selectedPart P Φ D 1 1 SelJ p.1 ![r'] ![r] ![q] αOut βIn ![ν] *
          ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε q ν ρ) *
          onePIPart P Φ D 0 2 p.2 ![] ![] ![q, -q] ![] ![] ![μ 0, ρ] := by
  simp only [selectedPart_eq_countSum, onePIPart]
  rw [countSum_split SelJ Red]
  congr 1
  rw [countSum_glue (fun C g => SelJ C g ∧ Red C g) SelJ countOnePI _
    (countWP₁ P Φ D r' r q αOut βIn) (countWP₂ P Φ D q μ) countGluePMap K
    (fun κ g hg f => count_sum_of_bij _ _ _ countGluePMap g (hmem κ g hg) (hinj κ g hg)
      (fun C hC => hsurj κ g hg C hC.1 hC.2) f) ?_]
  · refine sum_congr rfl fun p _ => ?_
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun ν _ => sum_congr rfl fun ρ _ => ?_
    exact congrArg (· * _) (countSum_mul_const SelJ (fun C₁ g₁ => ((fermionSign C₁ : ℤ) : ℂ) *
      contractionValue P Φ D C₁ g₁ ![r'] ![r] ![q] αOut βIn ![ν]) _ p.1)
  · intro N N₁ N₂ κ e g C₁ C₂ he hg h₁ h₂
    have hle := gradedOrder_split κ e g
    obtain ⟨hA₁, hV₁⟩ := hJ C₁ _ h₁
    exact countW_glueP P Φ D C₁ C₂ he hV₁ h₂.2.1 hA₁ h₂.1 hmom g αOut βIn μ
      (hT₁ _ _ C₁ h₁ (by omega)) (hT₂ _ _ C₂ h₂ (by omega))

end QED.GradedProof.X1C

end
