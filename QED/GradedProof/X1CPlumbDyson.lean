/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CPlumbPeel
public import QED.GradedProof.X1CCountDyson

/-!
# (X₁) piece C: `DysonFive` with the (T₉′) inputs discharged

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C. **`countDyson_dysonFive_t9`**: `countDyson_dysonFive` with the three
peels supplied by `selectedPart_peelIn_t9`, `selectedPart_peelOut_t9`, `selectedPart_peelP_t9`
at `K ∈ {1, 3, 5}`, `q = r' - r`. The remaining hypotheses are `T9Hyps` (from (X₁) by
`T9Hyps.of_x1`), the class condition `hG` (the class `G` consists of attached connected
contractions), and the graph-theoretic inputs: tadpole removal `h0`, the bijection hypotheses of
the three peels at graded order `≤ 5`, and `hV` (`G ∧ ¬RedIn ∧ ¬RedOut ∧ ¬RedP` is 1PI).
-/

@[expose] public section

namespace QED.GradedProof.X1C

open Finset
open QED.WickModel (Params Contraction VerticesConnected ExternalsAttached IsOnePI)
open QED.Graded

variable {P : Params} {F : Type} [Fintype F] [DecidableEq F] {Φ : Lepton.Flavors F}
  {D : Counterterms F} {rep : F → F} {m₀ : ℝ}

/-- **The order-`e⁵` Dyson decomposition, (T₉′) discharged**: only graph hypotheses remain. -/
theorem countDyson_dysonFive_t9 (H : T9Hyps P Φ D rep m₀) (SelG RedIn RedOut RedP : CountSel 1 1)
    (hG : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) (g : Grading κ),
      SelG C g → ExternalsAttached C ∧ VerticesConnected C)
    (h0 : ∀ (r' r : Fin 4 → ℝ) (α β μ : Fin 4),
      connectedPart P Φ D 1 1 5 ![r'] ![r] ![r' - r] ![α] ![β] ![μ] =
        selectedPart P Φ D 1 1 SelG 5 ![r'] ![r] ![r' - r] ![α] ![β] ![μ])
    (hmemI : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g ≤ 5 →
      ∀ x ∈ countIdxSet SelG (countOnePI (nf := 1) (nA := 0)) g,
        SelG (glueIn x.2.1 x.2.2.1 x.2.2.2) g ∧ RedIn (glueIn x.2.1 x.2.2.1 x.2.2.2) g)
    (hinjI : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g ≤ 5 →
      Set.InjOn (fun x : CountIdx 1 1 1 0 κ => glueIn x.2.1 x.2.2.1 x.2.2.2)
        (countIdxSet SelG (countOnePI (nf := 1) (nA := 0)) g))
    (hsurjI : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g ≤ 5 →
      ∀ C : Contraction 1 1 κ, SelG C g → RedIn C g →
        ∃ x ∈ countIdxSet SelG (countOnePI (nf := 1) (nA := 0)) g,
          glueIn x.2.1 x.2.2.1 x.2.2.2 = C)
    (hmemO : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g ≤ 5 →
      ∀ x ∈ countIdxSet (fun C g => SelG C g ∧ ¬ RedIn C g)
          (countOnePI (nf := 1) (nA := 0)) g,
        (SelG (glueOut x.2.1 x.2.2.1 x.2.2.2) g ∧ ¬ RedIn (glueOut x.2.1 x.2.2.1 x.2.2.2) g) ∧
          RedOut (glueOut x.2.1 x.2.2.1 x.2.2.2) g)
    (hinjO : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g ≤ 5 →
      Set.InjOn (fun x : CountIdx 1 1 1 0 κ => glueOut x.2.1 x.2.2.1 x.2.2.2)
        (countIdxSet (fun C g => SelG C g ∧ ¬ RedIn C g) (countOnePI (nf := 1) (nA := 0)) g))
    (hsurjO : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g ≤ 5 →
      ∀ C : Contraction 1 1 κ, (SelG C g ∧ ¬ RedIn C g) → RedOut C g →
        ∃ x ∈ countIdxSet (fun C g => SelG C g ∧ ¬ RedIn C g)
            (countOnePI (nf := 1) (nA := 0)) g,
          glueOut x.2.1 x.2.2.1 x.2.2.2 = C)
    (hmemP : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g ≤ 5 →
      ∀ x ∈ countIdxSet (fun C g => (SelG C g ∧ ¬ RedIn C g) ∧ ¬ RedOut C g)
          (countOnePI (nf := 0) (nA := 2)) g,
        ((SelG (glueP x.2.1 x.2.2.1 x.2.2.2) g ∧ ¬ RedIn (glueP x.2.1 x.2.2.1 x.2.2.2) g) ∧
          ¬ RedOut (glueP x.2.1 x.2.2.1 x.2.2.2) g) ∧ RedP (glueP x.2.1 x.2.2.1 x.2.2.2) g)
    (hinjP : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g ≤ 5 →
      Set.InjOn (fun x : CountIdx 1 1 0 2 κ => glueP x.2.1 x.2.2.1 x.2.2.2)
        (countIdxSet (fun C g => (SelG C g ∧ ¬ RedIn C g) ∧ ¬ RedOut C g)
          (countOnePI (nf := 0) (nA := 2)) g))
    (hsurjP : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g ≤ 5 →
      ∀ C : Contraction 1 1 κ, ((SelG C g ∧ ¬ RedIn C g) ∧ ¬ RedOut C g) → RedP C g →
        ∃ x ∈ countIdxSet (fun C g => (SelG C g ∧ ¬ RedIn C g) ∧ ¬ RedOut C g)
            (countOnePI (nf := 0) (nA := 2)) g,
          glueP x.2.1 x.2.2.1 x.2.2.2 = C)
    (hV : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) (g : Grading κ),
      gradedOrder κ g ≤ 5 →
        ((((SelG C g ∧ ¬ RedIn C g) ∧ ¬ RedOut C g) ∧ ¬ RedP C g) ↔ IsOnePI C)) :
    DysonFive P Φ D := by
  have hK : ∀ K ∈ ({1, 3, 5} : Finset ℕ), K ≤ 5 := by
    intro K hK
    simp only [mem_insert, mem_singleton] at hK
    omega
  refine countDyson_dysonFive P Φ D SelG RedIn RedOut RedP h0 ?_ ?_ ?_ hV
  · intro K hK5 r' r αOut βIn μ
    exact selectedPart_peelIn_t9 H SelG RedIn hG K (hK K hK5)
      (fun κ g hg => hmemI κ g (hg ▸ hK K hK5)) (fun κ g hg => hinjI κ g (hg ▸ hK K hK5))
      (fun κ g hg => hsurjI κ g (hg ▸ hK K hK5)) (add_sub_cancel r r').symm αOut βIn μ
  · intro K hK5 r' r αOut βIn μ
    exact selectedPart_peelOut_t9 H (fun C g => SelG C g ∧ ¬ RedIn C g) RedOut
      (fun C g h => hG C g h.1) K (hK K hK5)
      (fun κ g hg => hmemO κ g (hg ▸ hK K hK5)) (fun κ g hg => hinjO κ g (hg ▸ hK K hK5))
      (fun κ g hg => hsurjO κ g (hg ▸ hK K hK5)) (add_sub_cancel r r').symm αOut βIn μ
  · intro K hK5 r' r αOut βIn μ
    exact selectedPart_peelP_t9 H (fun C g => (SelG C g ∧ ¬ RedIn C g) ∧ ¬ RedOut C g) RedP
      (fun C g h => hG C g h.1.1) K (hK K hK5)
      (fun κ g hg => hmemP κ g (hg ▸ hK K hK5)) (fun κ g hg => hinjP κ g (hg ▸ hK K hK5))
      (fun κ g hg => hsurjP κ g (hg ▸ hK K hK5)) (add_sub_cancel r r').symm αOut βIn μ

end QED.GradedProof.X1C

end
