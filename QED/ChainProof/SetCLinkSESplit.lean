/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkSEEnum
public import QED.ChainProof.SetCLinkVSplit
public import QED.GradedProof.WI2SESplit
public import QED.GradedProof.EmbedOrder

/-!
# Set (c), model link: the selected order-`e⁴` self-energy through T1 parameter sets

Helper for the input (I3) of (WI-s) `QED.ThreeLoop.isVPShareOnShell_d₁_eq_d₂` (decision D-58),
the analogue of `QED.GradedProof.WI2.selfEnergyPart_two_add_tree_eq_split` for the self-energy
selection `selSE` of (Sc₂).

* `selfEnergySelPart_eq_sum`: for data `D` with no level `≥ 1`, the selected order-`4`
  self-energy is `(1/i)` times the sum over the kind sequences of total order `4` of the graded
  values at the zero grading of the 1PI contractions with `SEFam` (the nonzero gradings give `0`).
* **`selfEnergySelPart_split`**: it is `(1/i)(seVPValue (zParams Q X) + ∑_g w_g seVPValue
  (gParams Q X g))`, with the T1 parameter sets and weights of the order-`5` vertex
  (`WI2.contractionValue_zero_split`, `sum_order_four_seSelVal`).
-/

@[expose] public section

open Complex Finset

namespace QED.ChainProof.SetCLink

open QED.Graded QED.GradedProof QED.GradedProof.V5Zero.Split
open QED.WickModel (Params Contraction IsOnePI fermionSign)

/-- Membership in a filter, for any decidability instance. -/
theorem prop_of_mem_filter_any {α : Type} {p : α → Prop} {inst : DecidablePred p}
    {s : Finset α} {a : α} (h : a ∈ @Finset.filter α p inst s) : p a := by
  let _ := inst
  exact (Finset.mem_filter.1 h).2

open scoped Classical in
/-- The graded value at the zero grading of a self-energy contraction of the
vacuum-polarization family. -/
noncomputable def seSelValG (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (p : Fin 4 → ℝ) (α β : Fin 4) {N : ℕ}
    {κ : Fin N → Wick.VertexKind} (C : Contraction 1 0 κ) : ℂ :=
  if SEFam C then contractionValue P Φ D C 0 ![p] ![p] ![] ![α] ![β] ![] else 0

open scoped Classical in
/-- **The selected self-energy of data without levels `≥ 1` at the zero grading.** -/
theorem selfEnergySelPart_eq_sum (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F)
    (hD : ∀ f k, 1 ≤ k → D.d₁ f k = 0 ∧ D.d₂ f k = 0 ∧ D.dm f k = 0)
    (hD₃ : ∀ k, 1 ≤ k → D.d₃ k = 0) (f : F) (p : Fin 4 → ℝ) (α β : Fin 4) :
    selfEnergySelPart P Φ D selSE f 2 p α β = (1 / I) * ∑ N ∈ Finset.range (4 + 1),
      (N.factorial : ℂ)⁻¹ * ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
          (fun κ => ∑ t, (κ t).order = 4),
        ∑ C ∈ (Finset.univ : Finset (Contraction 1 0 κ)).filter (fun C => IsOnePI C),
          ((fermionSign C : ℤ) : ℂ) * seSelValG P { Φ with openLine := f } D p α β C := by
  rw [selfEnergySelPart, Matrix.of_apply]
  refine congrArg (fun x => (1 / I) * x) ?_
  unfold selectedPart
  refine Finset.sum_congr rfl fun N _ => congrArg _ ?_
  rw [sum_filter_any]
  refine Finset.sum_congr rfl fun κ _ => ?_
  by_cases hκ : ∑ t, (κ t).order = 4
  · simp only [hκ, ↓reduceIte]
    have h0 : (0 : Grading κ) ∈ (Fintype.piFinset fun _ : CtVertex κ =>
        Finset.range (2 * 2 + 1)).filter (fun g => gradedOrder κ g = 2 * 2) := by
      refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun _ => by simp, ?_⟩
      rw [gradedOrder_zero]
      exact hκ
    rw [Finset.sum_eq_single_of_mem 0 h0 fun g _ hg => Finset.sum_eq_zero fun C _ => by
      rw [contractionValue_eq_zero_of_level P _ D hD hD₃ C g hg, mul_zero]]
    rw [sum_filter_any, sum_filter_any]
    refine Finset.sum_congr rfl fun C _ => ?_
    simp only [seSelValG, SEFam]
    by_cases h1 : IsOnePI C <;> by_cases h2 : (ThreeLoop.IsVPSelfEnergy C ∨ ∀ t, κ t ≠ .gauge) <;>
      simp [h1, h2]
  · simp only [hκ, ↓reduceIte]
    refine Finset.sum_eq_zero fun g hg => Finset.sum_eq_zero fun C _ => ?_
    have hg0 : g ≠ 0 := by
      rintro rfl
      exact hκ (by simpa [gradedOrder_zero] using (Finset.mem_filter.1 hg).2)
    rw [contractionValue_eq_zero_of_level P _ D hD hD₃ C g hg0, mul_zero]

/-- **The selected order-`4` self-energy through T1 parameter sets** (`ε > 0`), for data without
levels `≥ 1`. -/
theorem selfEnergySelPart_split (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (hε : 0 < P.ε) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hpos : ∀ g, 0 < Φ.mass g) (hPV₁ : ∑ g, Φ.coeff g = 0)
    (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) {X : ℝ} (hlt : ∀ g, Φ.mass g < X)
    (hD : ∀ f k, 1 ≤ k → D.d₁ f k = 0 ∧ D.d₂ f k = 0 ∧ D.dm f k = 0)
    (hD₃ : ∀ k, 1 ≤ k → D.d₃ k = 0) (p : Fin 4 → ℝ) (α β : Fin 4) :
    selfEnergySelPart P Φ D selSE f 2 p α β =
      (1 / I) * (seVPValue (zParams (GEx2.vParams P Φ D f) X) p α β +
        ∑ g, (weight (GEx2.vParams P Φ D f) { Φ with openLine := f } X g : ℂ) *
          seVPValue (gParams (GEx2.vParams P Φ D f) { Φ with openLine := f } X g) p α β) := by
  classical
  set Q := GEx2.vParams P Φ D f
  set Φ' : Lepton.Flavors F := { Φ with openLine := f }
  have hT : ∀ S : Params, ∑ N ∈ Finset.range (4 + 1), (N.factorial : ℂ)⁻¹ *
        ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
            (fun κ => ∑ t, (κ t).order = 4),
          ∑ C ∈ (Finset.univ : Finset (Contraction 1 0 κ)).filter (fun C => IsOnePI C),
            ((fermionSign C : ℤ) : ℂ) * seSelVal S p α β C =
        seVPValue S p α β := fun S => sum_order_four_seSelVal S p α β
  have hC : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, ∑ t, (κ t).order = 4 →
      ∀ C : Contraction 1 0 κ, IsOnePI C →
        seSelValG P Φ' D p α β C = seSelVal (zParams Q X) p α β C +
          ∑ g, (weight Q Φ' X g : ℂ) * seSelVal (gParams Q Φ' X g) p α β C := by
    intro N κ hκ C hC
    by_cases h : SEFam C
    · simp only [seSelValG, seSelVal, h, ↓reduceIte]
      exact WI2.contractionValue_zero_split P Φ D f hε hmγ hΛ hpos hPV₁ hPV₂ hlt hκ C hC p α β
    · simp [seSelValG, seSelVal, h]
  rw [selfEnergySelPart_eq_sum P Φ D hD hD₃ f p α β]
  refine congrArg (fun x => (1 / I) * x) ?_
  simp only [← hT]
  rw [Finset.sum_congr rfl fun N _ => congrArg _ (Finset.sum_congr rfl fun κ hκ =>
    Finset.sum_congr rfl fun C hC' => by
      rw [hC (prop_of_mem_filter_any (p := fun κ : Fin N → Wick.VertexKind => ∑ t, (κ t).order = 4)
        hκ) C (prop_of_mem_filter_any (p := fun C : Contraction 1 0 κ => IsOnePI C) hC')])]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun g _ => ?_
  ring

end QED.ChainProof.SetCLink

end
