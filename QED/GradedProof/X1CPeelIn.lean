/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CPeelSurj
public import QED.GradedProof.X1CPeelT9

/-!
# (X₁) piece C: the in-leg peel with the graph theory discharged

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5. For the attached connected tadpole-free `(1,1)` contractions
`G = peelSelG` and the in-leg reducible ones `peelRedIn` (an in-leg self-energy cut exists), at the
regulators of `P`:

`G_K(r', r; βIn) = (G ∧ ¬peelRedIn)_K(r', r; βIn) + ∑_{K₁+K₂=K} ∑_{γ δ} G_{K₁}(r', r; γ) ·
  (1/i) S̃_{γδ}(r) · onePIPart(1,0)_{K₂}(r, r; δ, βIn)`.

* **`selectedPart_peelIn'`**: the hypotheses `hmem`, `hinj`, `hsurj` of `selectedPart_peelIn` are
  discharged (`peel_hmemIn`, `countGlueIn_injOn` with `peel_hpeelIn`, `peel_hsurjIn`); the
  (T₉′) hypotheses `hT₁`, `hT₂` remain.
* **`selectedPart_peelIn_five`**: for `K ≤ 5` the (T₉′) hypotheses too, from `T9Hyps`
  (`peel_hT₁`, `peel_hT₂`).
* `peel_hG`, `peel_hmemI`, `peel_hinjI`, `peel_hsurjI`: the hypotheses `hG`, `hmemI`, `hinjI`,
  `hsurjI` of `countDyson_dysonFive_t9` (with `SelG := peelSelG`, `RedIn := peelRedIn`), in
  exactly its form.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open Finset
open QED.WickModel (Params Contraction loopCount lineMomentum₂ IsOnePI)
open QED.Graded
open Complex

variable {F : Type} [Fintype F] [DecidableEq F] (P : Params) (Φ : Lepton.Flavors F)
  (D : Counterterms F)

/-- **The in-leg peel**, graph theory discharged. -/
theorem selectedPart_peelIn' (K : ℕ) {r' r q : Fin 4 → ℝ} (hmom : r' = r + q)
    (αOut βIn μ : Fin 1 → Fin 4)
    (hT₁ : ∀ {N₁ : ℕ} (κ₁ : Fin N₁ → Wick.VertexKind) (g₁ : Grading κ₁)
      (C₁ : Contraction 1 1 κ₁), peelSelG C₁ g₁ → gradedOrder κ₁ g₁ ≤ K →
      ∀ γ, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₁) fun ℓ =>
        twoPiInv (loopCount C₁) * regulatedAmplitude P Φ D C₁ g₁ ![r] ![q]
          (lineMomentum₂ C₁ ![r'] ![r] ![q] ℓ) αOut ![γ] μ)
    (hT₂ : ∀ {N₂ : ℕ} (κ₂ : Fin N₂ → Wick.VertexKind) (g₂ : Grading κ₂)
      (C₂ : Contraction 1 0 κ₂), IsOnePI C₂ → gradedOrder κ₂ g₂ ≤ K →
      ∀ δ, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₂) fun ℓ =>
        twoPiInv (loopCount C₂) * regulatedAmplitude P Φ D C₂ g₂ ![r] ![]
          (lineMomentum₂ C₂ ![r] ![r] ![] ℓ) ![δ] βIn ![]) :
    selectedPart P Φ D 1 1 peelSelG K ![r'] ![r] ![q] αOut βIn μ =
      selectedPart P Φ D 1 1 (fun C g => peelSelG C g ∧ ¬ peelRedIn C g) K ![r'] ![r] ![q]
        αOut βIn μ +
      ∑ p ∈ antidiagonal K, ∑ γ, ∑ δ,
        selectedPart P Φ D 1 1 peelSelG p.1 ![r'] ![r] ![q] αOut ![γ] μ *
          ((1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε r γ δ) *
          onePIPart P Φ D 1 0 p.2 ![r] ![r] ![] ![δ] βIn ![] :=
  selectedPart_peelIn P Φ D peelSelG peelRedIn (fun _ _ h => ⟨h.1, h.2.1⟩) K
    (fun _ g _ => peel_hmemIn g)
    (fun _ g _ => countGlueIn_injOn peelSelG g peelIn (peel_hpeelIn g))
    (fun _ g _ C hS hR => peel_hsurjIn g C hS hR) hmom αOut βIn μ hT₁ hT₂

/-- **The in-leg peel at graded order at most `5`**, all hypotheses discharged from `T9Hyps`. -/
theorem selectedPart_peelIn_five {rep : F → F} {m₀ : ℝ} (H : T9Hyps P Φ D rep m₀) (K : ℕ)
    (hK : K ≤ 5) {r' r q : Fin 4 → ℝ} (hmom : r' = r + q) (αOut βIn μ : Fin 1 → Fin 4) :
    selectedPart P Φ D 1 1 peelSelG K ![r'] ![r] ![q] αOut βIn μ =
      selectedPart P Φ D 1 1 (fun C g => peelSelG C g ∧ ¬ peelRedIn C g) K ![r'] ![r] ![q]
        αOut βIn μ +
      ∑ p ∈ antidiagonal K, ∑ γ, ∑ δ,
        selectedPart P Φ D 1 1 peelSelG p.1 ![r'] ![r] ![q] αOut ![γ] μ *
          ((1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε r γ δ) *
          onePIPart P Φ D 1 0 p.2 ![r] ![r] ![] ![δ] βIn ![] :=
  selectedPart_peelIn' P Φ D K hmom αOut βIn μ
    (fun _ g₁ C₁ h hg γ => peel_hT₁ H C₁ h.1 h.2.1 g₁ (hg.trans hK) hmom αOut ![γ] μ)
    (fun _ g₂ C₂ h hg δ => peel_hT₂ H C₂ h g₂ (hg.trans hK) r ![δ] βIn)

/-! ### The in-leg hypotheses of `countDyson_dysonFive_t9` -/

/-- `hG` of `countDyson_dysonFive_t9` for `peelSelG`. -/
theorem peel_hG {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) (g : Grading κ)
    (h : peelSelG C g) : QED.WickModel.ExternalsAttached C ∧ QED.WickModel.VerticesConnected C :=
  ⟨h.1, h.2.1⟩

/-- `hmemI` of `countDyson_dysonFive_t9` for `peelSelG`, `peelRedIn`. -/
theorem peel_hmemI {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ)
    (_ : gradedOrder κ g ≤ 5) :
    ∀ x ∈ countIdxSet peelSelG (countOnePI (nf := 1) (nA := 0)) g,
      peelSelG (glueIn x.2.1 x.2.2.1 x.2.2.2) g ∧ peelRedIn (glueIn x.2.1 x.2.2.1 x.2.2.2) g :=
  peel_hmemIn g

/-- `hinjI` of `countDyson_dysonFive_t9` for `peelSelG`. -/
theorem peel_hinjI {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ)
    (_ : gradedOrder κ g ≤ 5) :
    Set.InjOn (fun x : CountIdx 1 1 1 0 κ => glueIn x.2.1 x.2.2.1 x.2.2.2)
      (countIdxSet peelSelG (countOnePI (nf := 1) (nA := 0)) g) :=
  countGlueIn_injOn peelSelG g peelIn (peel_hpeelIn g)

/-- `hsurjI` of `countDyson_dysonFive_t9` for `peelSelG`, `peelRedIn`. -/
theorem peel_hsurjI {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ)
    (_ : gradedOrder κ g ≤ 5) :
    ∀ C : Contraction 1 1 κ, peelSelG C g → peelRedIn C g →
      ∃ x ∈ countIdxSet peelSelG (countOnePI (nf := 1) (nA := 0)) g,
        glueIn x.2.1 x.2.2.1 x.2.2.2 = C :=
  fun C hS hR => peel_hsurjIn g C hS hR

end QED.GradedProof.X1C

end
