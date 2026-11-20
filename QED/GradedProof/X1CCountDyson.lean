/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CCountDysonMat

/-!
# (X₁) piece C: `DysonFive` from the three peels

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (assembly).

**`countDyson_dysonFive`**: `DysonFive P Φ D` (the order-`e⁵` Dyson decomposition at the
regulators of `P`) holds, conditionally on

* `h0` (tadpole removal): the connected order-`5` function is the selected part of a class
  `G` (intended: attached, connected, tadpole-free);
* `hI`, `hO`, `hP`: the three value-level peels at the odd orders `K ∈ {1, 3, 5}` and
  `q = r' - r`, in exactly the form of the conclusions of `selectedPart_peelIn` (class `G`,
  predicate `RedIn`), `selectedPart_peelOut` (class `H = G ∧ ¬RedIn`, predicate `RedOut`) and
  `selectedPart_peelP` (class `J = H ∧ ¬RedOut`, predicate `RedP`);
* `hV`: at graded order `≤ 5`, `J ∧ ¬RedP` is exactly 1PI.

The proof writes the peels as matrix recursions (`countDyson_matIn/Out/P`), unwinds them with
`countDyson_unwind` (the insertions vanish at orders `0, 1, 3, 5` by
`countDyson_onePIPart_eq_zero`) and identifies the chains and the vertex parts with those of
`dysonFive` (`countDyson_inLeg`, `countDyson_outLeg`, `countDyson_photonLeg`,
`countDyson_vertexPart`; the factor `i` cancels the `1/i` of `vertexPart`).
-/

@[expose] public section

namespace QED.GradedProof.X1C

open Finset
open QED.WickModel (Params Contraction IsOnePI)
open QED.Graded
open Complex

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F)

/-- **The order-`e⁵` Dyson decomposition from the three peels.** -/
theorem countDyson_dysonFive (SelG RedIn RedOut RedP : CountSel 1 1)
    (h0 : ∀ (r' r : Fin 4 → ℝ) (α β μ : Fin 4),
      connectedPart P Φ D 1 1 5 ![r'] ![r] ![r' - r] ![α] ![β] ![μ] =
        selectedPart P Φ D 1 1 SelG 5 ![r'] ![r] ![r' - r] ![α] ![β] ![μ])
    (hI : ∀ K ∈ ({1, 3, 5} : Finset ℕ), ∀ (r' r : Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4),
      selectedPart P Φ D 1 1 SelG K ![r'] ![r] ![r' - r] αOut βIn μ =
        selectedPart P Φ D 1 1 (fun C g => SelG C g ∧ ¬ RedIn C g) K ![r'] ![r] ![r' - r]
          αOut βIn μ +
        ∑ p ∈ antidiagonal K, ∑ γ, ∑ δ,
          selectedPart P Φ D 1 1 SelG p.1 ![r'] ![r] ![r' - r] αOut ![γ] μ *
            ((1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε r γ δ) *
            onePIPart P Φ D 1 0 p.2 ![r] ![r] ![] ![δ] βIn ![])
    (hO : ∀ K ∈ ({1, 3, 5} : Finset ℕ), ∀ (r' r : Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4),
      selectedPart P Φ D 1 1 (fun C g => SelG C g ∧ ¬ RedIn C g) K ![r'] ![r] ![r' - r]
          αOut βIn μ =
        selectedPart P Φ D 1 1 (fun C g => (SelG C g ∧ ¬ RedIn C g) ∧ ¬ RedOut C g) K ![r']
          ![r] ![r' - r] αOut βIn μ +
        ∑ p ∈ antidiagonal K, ∑ γ, ∑ δ,
          onePIPart P Φ D 1 0 p.2 ![r'] ![r'] ![] αOut ![γ] ![] *
            ((1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε r' γ δ) *
            selectedPart P Φ D 1 1 (fun C g => SelG C g ∧ ¬ RedIn C g) p.1 ![r'] ![r]
              ![r' - r] ![δ] βIn μ)
    (hP : ∀ K ∈ ({1, 3, 5} : Finset ℕ), ∀ (r' r : Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4),
      selectedPart P Φ D 1 1 (fun C g => (SelG C g ∧ ¬ RedIn C g) ∧ ¬ RedOut C g) K ![r']
          ![r] ![r' - r] αOut βIn μ =
        selectedPart P Φ D 1 1
          (fun C g => ((SelG C g ∧ ¬ RedIn C g) ∧ ¬ RedOut C g) ∧ ¬ RedP C g) K ![r'] ![r]
          ![r' - r] αOut βIn μ +
        ∑ p ∈ antidiagonal K, ∑ ν, ∑ ρ,
          selectedPart P Φ D 1 1 (fun C g => (SelG C g ∧ ¬ RedIn C g) ∧ ¬ RedOut C g) p.1
              ![r'] ![r] ![r' - r] αOut βIn ![ν] *
            ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (r' - r) ν ρ) *
            onePIPart P Φ D 0 2 p.2 ![] ![] ![r' - r, -(r' - r)] ![] ![] ![μ 0, ρ])
    (hV : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) (g : Grading κ),
      gradedOrder κ g ≤ 5 →
        ((((SelG C g ∧ ¬ RedIn C g) ∧ ¬ RedOut C g) ∧ ¬ RedP C g) ↔ IsOnePI C)) :
    DysonFive P Φ D := by
  intro r' r μ
  have hV' : ∀ K ∈ ({1, 3, 5} : Finset ℕ), ∀ μ,
      countDysonSel P Φ D
          (fun C g => ((SelG C g ∧ ¬ RedIn C g) ∧ ¬ RedOut C g) ∧ ¬ RedP C g) r' r K μ =
        countDysonSel P Φ D (fun C _ => IsOnePI C) r' r K μ := by
    intro K hK μ
    have hK5 : K ≤ 5 := by simp only [mem_insert, mem_singleton] at hK; omega
    ext α β
    exact countDyson_selectedPart_congr P Φ D
      (fun C g => ((SelG C g ∧ ¬ RedIn C g) ∧ ¬ RedOut C g) ∧ ¬ RedP C g)
      (fun C _ => IsOnePI C) K (fun C g hg => hV C g (hg ▸ hK5)) _ _ _ _ _ _
  have hJ : ∀ K ∈ ({1, 3, 5} : Finset ℕ), ∀ μ,
      countDysonSel P Φ D (fun C g => (SelG C g ∧ ¬ RedIn C g) ∧ ¬ RedOut C g) r' r K μ =
        countDysonSel P Φ D (fun C _ => IsOnePI C) r' r K μ +
        ∑ p ∈ antidiagonal K, ∑ ν, countDysonQ P Φ D (r' - r) p.2 ν μ •
          countDysonSel P Φ D (fun C g => (SelG C g ∧ ¬ RedIn C g) ∧ ¬ RedOut C g) r' r p.1 ν := by
    intro K hK μ
    rw [← hV' K hK μ]
    exact countDyson_matP P Φ D (fun C g => (SelG C g ∧ ¬ RedIn C g) ∧ ¬ RedOut C g)
      (fun C g => ((SelG C g ∧ ¬ RedIn C g) ∧ ¬ RedOut C g) ∧ ¬ RedP C g) r' r K
      (hP K hK r' r) μ
  have hH : ∀ K ∈ ({1, 3, 5} : Finset ℕ), ∀ μ,
      countDysonSel P Φ D (fun C g => SelG C g ∧ ¬ RedIn C g) r' r K μ =
        countDysonSel P Φ D (fun C g => (SelG C g ∧ ¬ RedIn C g) ∧ ¬ RedOut C g) r' r K μ +
        ∑ p ∈ antidiagonal K, countDysonY P Φ D r' p.2 *
          countDysonSel P Φ D (fun C g => SelG C g ∧ ¬ RedIn C g) r' r p.1 μ :=
    fun K hK μ => countDyson_matOut P Φ D (fun C g => SelG C g ∧ ¬ RedIn C g)
      (fun C g => (SelG C g ∧ ¬ RedIn C g) ∧ ¬ RedOut C g) r' r K (hO K hK r' r) μ
  have hG : ∀ K ∈ ({1, 3, 5} : Finset ℕ), ∀ μ,
      countDysonSel P Φ D SelG r' r K μ =
        countDysonSel P Φ D (fun C g => SelG C g ∧ ¬ RedIn C g) r' r K μ +
        ∑ p ∈ antidiagonal K, countDysonSel P Φ D SelG r' r p.1 μ * countDysonX P Φ D r p.2 :=
    fun K hK μ => countDyson_matIn P Φ D SelG (fun C g => SelG C g ∧ ¬ RedIn C g) r' r K
      (hI K hK r' r) μ
  have hU := countDyson_unwind _ _ _ _ _ _ _
    (fun K hK h2 h4 => countDysonX_eq_zero P Φ D r hK h2 h4)
    (fun K hK h2 h4 => countDysonY_eq_zero P Φ D r' hK h2 h4)
    (fun K hK h2 h4 => countDysonQ_eq_zero P Φ D (r' - r) hK h2 h4) hG hH hJ μ
  have hL : connMatrix P Φ D r' r μ = countDysonSel P Φ D SelG r' r 5 μ := by
    ext α β
    exact h0 r' r α β μ
  rw [hL, hU, dysonFive]
  simp only [Finset.smul_sum, smul_ite, smul_zero]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ =>
    sum_congr rfl fun d _ => ?_
  split_ifs
  · refine sum_congr rfl fun ν _ => ?_
    rw [countDyson_photonLeg, countDyson_outLeg, countDyson_inLeg, countDyson_vertexPart,
      Matrix.mul_smul, Matrix.smul_mul, smul_comm I, smul_smul I, mul_one_div_cancel I_ne_zero,
      one_smul]
  · rfl

end QED.GradedProof.X1C

end
