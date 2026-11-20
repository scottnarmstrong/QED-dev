/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CCountConn
public import QED.Frozen.Graded.OnePIPart

/-!
# (X₁) piece C: the in-leg peel at fixed `ε`, given the bijection

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (counting). **`selectedPart_peelIn`**: for a class `G` of
attached connected `(1,1)` contractions and an "in-leg reducible" predicate `Red`, if the
contractions of `G ∧ Red` (order `K`) are bijectively the `glueIn e C₁ C₂` of `C₁ ∈ G`, `C₂` a
1PI `(1,0)` contraction, over the shuffles (`hmem`, `hinj`, `hsurj`, the graph-theoretic input),
then at the regulators of `P`

`G_K(r', r; βIn) = H_K(r', r; βIn) + ∑_{K₁+K₂=K} ∑_{γ δ} G_{K₁}(r', r; γ) · (1/i) S̃_{γδ}(r) ·
  onePIPart(1,0)_{K₂}(r, r; δ, βIn)`,

`H = G ∧ ¬Red`, with the fermionic signs and the multiplicities `1/(N₁! N₂!)` accounted for. The
integrability (T₉′) of the piece integrands enters as the hypotheses `hT₁` (pieces in `G`) and
`hT₂` (1PI self-energy pieces), in the form of `contractionValue_glueIn`.

`countGlueIn_injOn` reduces the hypothesis `hinj` to one graph-theoretic fact: a function
`peel` that recovers the vertex set of the self-energy piece from the glued contraction.
`countSum_split`, `countSum_mul_const`: bookkeeping for the graded sums.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open Finset
open QED.WickModel (Params Contraction loopCount lineMomentum₂ VerticesConnected
  ExternalsAttached IsOnePI fermionSign)
open QED.Graded
open Complex

/-- **Splitting a selection** by a predicate. -/
theorem countSum_split {nf nA : ℕ} (Sel Q : CountSel nf nA) (W : CountWt nf nA) (K : ℕ) :
    countSum Sel W K = countSum (fun C g => Sel C g ∧ ¬ Q C g) W K +
      countSum (fun C g => Sel C g ∧ Q C g) W K := by
  classical
  simp only [countSum, ← sum_add_distrib, ← mul_add]
  refine sum_congr rfl fun N _ => congrArg _ (sum_congr rfl fun κ _ => sum_congr rfl
    fun g _ => ?_)
  simp only [countSel, sum_filter, ← sum_add_distrib]
  refine sum_congr rfl fun C _ => ?_
  by_cases h₁ : Sel C g <;> by_cases h₂ : Q C g <;> simp [h₁, h₂]

theorem countSum_mul_const {nf nA : ℕ} (Sel : CountSel nf nA) (W : CountWt nf nA) (c : ℂ)
    (K : ℕ) : countSum Sel (fun C g => W C g * c) K = countSum Sel W K * c := by
  simp only [countSum, sum_mul, mul_assoc]

/-- The glue map of the in-leg peel. -/
abbrev countGlueInMap : ∀ {N N₁ N₂ : ℕ} {κ : Fin N → Wick.VertexKind}
    (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N), Contraction 1 1 (leftKinds κ e) →
      Contraction 1 0 (rightKinds κ e) → Contraction 1 1 κ :=
  fun e C₁ C₂ => glueIn e C₁ C₂

/-- The 1PI selection. -/
abbrev countOnePI {nf nA : ℕ} : CountSel nf nA := fun C _ => IsOnePI C

variable {F : Type} [Fintype F] [DecidableEq F] (P : Params) (Φ : Lepton.Flavors F)
  (D : Counterterms F)

/-- The weight of the left piece of the in-leg peel, with the bridge propagator. -/
noncomputable def countWIn₁ (r' r q : Fin 4 → ℝ) (αOut μ : Fin 1 → Fin 4) (z : Fin 4 × Fin 4) :
    CountWt 1 1 := fun C₁ g₁ => ((fermionSign C₁ : ℤ) : ℂ) *
  contractionValue P Φ D C₁ g₁ ![r'] ![r] ![q] αOut ![z.1] μ *
    ((1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε r z.1 z.2)

/-- The weight of the self-energy piece of the in-leg peel. -/
noncomputable def countWIn₂ (r : Fin 4 → ℝ) (βIn : Fin 1 → Fin 4) (z : Fin 4 × Fin 4) :
    CountWt 1 0 := fun C₂ g₂ => ((fermionSign C₂ : ℤ) : ℂ) *
  contractionValue P Φ D C₂ g₂ ![r] ![r] ![] ![z.2] βIn ![]

/-- **Injectivity of the in-leg glue from the peeled set**: if a function `peel` recovers, from
every glued contraction of the data, the vertices of the self-energy piece (the complement of the
image of the left piece), the glue map is injective on the data. -/
theorem countGlueIn_injOn {N : ℕ} {κ : Fin N → Wick.VertexKind} (SelG : CountSel 1 1)
    (g : Grading κ) (peel : Contraction 1 1 κ → Finset (Fin N))
    (hpeel : ∀ x ∈ countIdxSet SelG (countOnePI (nf := 1) (nA := 0)) g,
      peel (glueIn x.2.1 x.2.2.1 x.2.2.2) = (countLeftImage x.2.1)ᶜ) :
    Set.InjOn (fun x : CountIdx 1 1 1 0 κ => glueIn x.2.1 x.2.2.1 x.2.2.2)
      (countIdxSet SelG (countOnePI (nf := 1) (nA := 0)) g) := by
  rintro ⟨p, e, C₁, C₂⟩ hx ⟨p', e', C₁', C₂'⟩ hy h
  have h' : glueIn e C₁ C₂ = glueIn e' C₁' C₂' := h
  have hx' := mem_countIdxSet.1 hx
  have hy' := mem_countIdxSet.1 hy
  have h₁ : peel (glueIn e C₁ C₂) = (countLeftImage e)ᶜ := hpeel ⟨p, e, C₁, C₂⟩ hx
  have h₂ : peel (glueIn e' C₁' C₂') = (countLeftImage e')ᶜ := hpeel ⟨p', e', C₁', C₂'⟩ hy
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
  obtain ⟨rfl, rfl⟩ := countGlueIn_pieces_eq h'
  rfl

/-- **The in-leg peel** `G = H + G · (1/i) S̃ · Σ` at fixed `ε`, given the bijection. -/
theorem selectedPart_peelIn (SelG Red : CountSel 1 1)
    (hG : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) (g : Grading κ),
      SelG C g → ExternalsAttached C ∧ VerticesConnected C) (K : ℕ)
    (hmem : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = K →
      ∀ x ∈ countIdxSet SelG (countOnePI (nf := 1) (nA := 0)) g,
        SelG (glueIn x.2.1 x.2.2.1 x.2.2.2) g ∧ Red (glueIn x.2.1 x.2.2.1 x.2.2.2) g)
    (hinj : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = K →
      Set.InjOn (fun x : CountIdx 1 1 1 0 κ => glueIn x.2.1 x.2.2.1 x.2.2.2)
        (countIdxSet SelG (countOnePI (nf := 1) (nA := 0)) g))
    (hsurj : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = K →
      ∀ C : Contraction 1 1 κ, SelG C g → Red C g →
        ∃ x ∈ countIdxSet SelG (countOnePI (nf := 1) (nA := 0)) g,
          glueIn x.2.1 x.2.2.1 x.2.2.2 = C)
    {r' r q : Fin 4 → ℝ} (hmom : r' = r + q) (αOut βIn μ : Fin 1 → Fin 4)
    (hT₁ : ∀ {N₁ : ℕ} (κ₁ : Fin N₁ → Wick.VertexKind) (g₁ : Grading κ₁)
      (C₁ : Contraction 1 1 κ₁), SelG C₁ g₁ → gradedOrder κ₁ g₁ ≤ K →
      ∀ γ, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₁) fun ℓ =>
        twoPiInv (loopCount C₁) * regulatedAmplitude P Φ D C₁ g₁ ![r] ![q]
          (lineMomentum₂ C₁ ![r'] ![r] ![q] ℓ) αOut ![γ] μ)
    (hT₂ : ∀ {N₂ : ℕ} (κ₂ : Fin N₂ → Wick.VertexKind) (g₂ : Grading κ₂)
      (C₂ : Contraction 1 0 κ₂), IsOnePI C₂ → gradedOrder κ₂ g₂ ≤ K →
      ∀ δ, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₂) fun ℓ =>
        twoPiInv (loopCount C₂) * regulatedAmplitude P Φ D C₂ g₂ ![r] ![]
          (lineMomentum₂ C₂ ![r] ![r] ![] ℓ) ![δ] βIn ![]) :
    selectedPart P Φ D 1 1 SelG K ![r'] ![r] ![q] αOut βIn μ =
      selectedPart P Φ D 1 1 (fun C g => SelG C g ∧ ¬ Red C g) K ![r'] ![r] ![q] αOut βIn μ +
      ∑ p ∈ antidiagonal K, ∑ γ, ∑ δ,
        selectedPart P Φ D 1 1 SelG p.1 ![r'] ![r] ![q] αOut ![γ] μ *
          ((1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε r γ δ) *
          onePIPart P Φ D 1 0 p.2 ![r] ![r] ![] ![δ] βIn ![] := by
  simp only [selectedPart_eq_countSum, onePIPart]
  rw [countSum_split SelG Red]
  congr 1
  rw [countSum_glue (fun C g => SelG C g ∧ Red C g) SelG countOnePI _
    (countWIn₁ P Φ D r' r q αOut μ) (countWIn₂ P Φ D r βIn) countGlueInMap K
    (fun κ g hg f => count_sum_of_bij _ _ _ countGlueInMap g (hmem κ g hg) (hinj κ g hg)
      (fun C hC => hsurj κ g hg C hC.1 hC.2) f) ?_]
  · refine sum_congr rfl fun p _ => ?_
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun γ _ => sum_congr rfl fun δ _ => ?_
    exact congrArg (· * _) (countSum_mul_const SelG (fun C₁ g₁ => ((fermionSign C₁ : ℤ) : ℂ) *
      contractionValue P Φ D C₁ g₁ ![r'] ![r] ![q] αOut ![γ] μ) _ p.1)
  · intro N N₁ N₂ κ e g C₁ C₂ he hg h₁ h₂
    have hle := gradedOrder_split κ e g
    obtain ⟨hA₁, hV₁⟩ := hG C₁ _ h₁
    exact countW_glueIn P Φ D C₁ C₂ he hV₁ h₂.2.1 hA₁ h₂.1 hmom g αOut βIn μ
      (hT₁ _ _ C₁ h₁ (by omega)) (hT₂ _ _ C₂ h₂ (by omega))

end QED.GradedProof.X1C

end
