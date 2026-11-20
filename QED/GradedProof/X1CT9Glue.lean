/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CT9One
public import QED.GradedProof.X1CT9Vertex
public import QED.Frozen.Graded.IsRenormalizedThrough
import QED.LeptonProof.EmbedOneZero
import QED.WickModel.TwoPointClassificationTree

/-!
# (X₁) piece C: the (T₉′) inputs of the three value lemmas

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C. Bundles the hypotheses of (X₁) used for integrability (`T9Hyps`,
`T9Hyps.of_x1`) and supplies, for a glue of graded order `5` of an attached connected vertex
piece `C₁` and a 1PI self-energy or vacuum-polarization piece `C₂`, both (T₉′) hypotheses `hT₁`,
`hT₂` of `contractionValue_glueIn`, `contractionValue_glueOut`, `contractionValue_glueP`
(`t9_glueIn`, `t9_glueOut`, `t9_glueP`).

A 1PI self-energy or vacuum-polarization piece has even graded order at least `2`
(`t9_two_le_gradedOrder`: its photon fields pair off, so the total order is even, and it has a
vertex), so the piece has graded order `2` or `4` and the vertex piece graded order at most `3`
(`t9_split_orders`). The piece lemmas: `t9_selfEnergy` (graded order `≤ 4`, from
`t9_selfEnergy_two` and `t9_selfEnergy_four`), `t9_vacuumPolarization` (likewise), and
`t9_vertex_le_three`.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Params Contraction loopCount lineMomentum₂ IsOnePI VerticesConnected
  ExternalsAttached)
open QED.Graded

/-! ### Parity of the graded order -/

section Parity

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- With an even number of external photons, the total order of a contracted kind sequence is
even. -/
theorem t9_two_dvd_sum_order (C : Contraction nf nA κ) (h : 2 ∣ nA) :
    2 ∣ ∑ t, (κ t).order := by
  by_contra hodd
  have hmod : (∑ t, (κ t).photonSlots) % 2 = (∑ t, (κ t).order) % 2 := by
    rw [Finset.sum_nat_mod, Finset.sum_nat_mod Finset.univ 2 (fun t => (κ t).order)]
    simp only [QED.Lepton.Proof.photonSlots_mod_two]
  have hE : IsEmpty (Contraction nf nA κ) := by
    apply QED.WickModel.isEmpty_contraction_of_not_two_dvd
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]
    simp only [Fintype.card_fin]
    omega
  exact hE.false C

/-- The graded order of a contraction with an even number of external photons and a vertex is
even and at least `2`. -/
theorem t9_two_le_gradedOrder (C : Contraction nf nA κ) (h : 2 ∣ nA) (hN : 0 < N)
    (g : Grading κ) : 2 ≤ gradedOrder κ g ∧ 2 ∣ gradedOrder κ g := by
  have hd := t9_two_dvd_sum_order C h
  have hle := QED.TwoLoop.Enumeration.le_sum_order κ
  have h2 : ∑ t : CtVertex κ, 2 * g t = 2 * ∑ t, g t := (Finset.mul_sum _ _ _).symm
  unfold gradedOrder
  rw [h2]
  omega

end Parity

/-! ### The hypotheses of (X₁) used for integrability -/

/-- The hypotheses of (X₁) (at a fixed `ε > 0`) that the (T₉′) sources use. -/
structure T9Hyps (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F) (m₀ : ℝ) : Prop where
  hε : 0 < P.ε
  hm₀ : 0 < m₀
  hmass : ∀ g, m₀ ≤ Φ.mass g
  hmγ : 0 < P.mγ
  hΛ : 0 < P.Λ
  hrep : ∀ f, rep (rep f) = rep f
  hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0
  hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0
  hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0

/-- **The hypotheses of (X₁)** give `T9Hyps` at every `ε > 0`. -/
theorem T9Hyps.of_x1 (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F) (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : IsRenormalizedThrough P Φ D rep 2) {ε : ℝ} (hε : 0 < ε) :
    T9Hyps { P with ε := ε } Φ D rep m₀ :=
  ⟨hε, hm₀, hmass, hmγ, hΛ, hrep, hPV₁, hPV₂, fun f => hD.1 f 0 (by norm_num)⟩

/-! ### The pieces at any admissible graded order -/

variable {P : Params} {F : Type} [Fintype F] [DecidableEq F] {Φ : Lepton.Flavors F}
  {D : Counterterms F} {rep : F → F} {m₀ : ℝ}

section Pieces

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

theorem t9_pos_of_isOnePI {nf nA : ℕ} (C : Contraction nf nA κ) (hC : IsOnePI C)
    (h : 0 < nf ∨ 0 < nA) : 0 < N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain ⟨n, rfl⟩ | ⟨n, rfl⟩ : (∃ n, nf = n + 1) ∨ ∃ n, nA = n + 1 := by
      rcases h with h | h
      · exact Or.inl ⟨nf - 1, by omega⟩
      · exact Or.inr ⟨nA - 1, by omega⟩
    · exact absurd hC (QED.WickModel.not_isOnePI_of_fin_zero_left C)
    · exact absurd hC (QED.WickModel.not_isOnePI_of_fin_zero_right C)
  · exact hN

/-- **(T₉′) of a 1PI self-energy piece of graded order at most `4`**. -/
theorem t9_selfEnergy (H : T9Hyps P Φ D rep m₀) (C : Contraction 1 0 κ) (hC : IsOnePI C)
    (g : Grading κ) (hg : gradedOrder κ g ≤ 4) (p : Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      twoPiInv (loopCount C) * regulatedAmplitude P Φ D C g ![p] ![]
        (lineMomentum₂ C ![p] ![p] ![] ℓ) αOut βIn ![] := by
  obtain ⟨h2, hd⟩ := t9_two_le_gradedOrder C (by norm_num)
    (t9_pos_of_isOnePI C hC (Or.inl one_pos)) g
  rcases (by omega : gradedOrder κ g = 2 ∨ gradedOrder κ g = 4) with h | h
  · exact t9_selfEnergy_two P Φ D H.hε m₀ H.hm₀ H.hmass H.hmγ H.hΛ C hC g h p αOut βIn
  · exact t9_selfEnergy_four P Φ D H.hε rep m₀ H.hm₀ H.hmass H.hmγ H.hΛ H.hrep H.hPV₁ H.hPV₂
      C hC g h p αOut βIn

/-- **(T₉′) of a 1PI vacuum-polarization piece of graded order at most `4`**. -/
theorem t9_vacuumPolarization (H : T9Hyps P Φ D rep m₀) (C : Contraction 0 2 κ)
    (hC : IsOnePI C) (g : Grading κ) (hg : gradedOrder κ g ≤ 4) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      twoPiInv (loopCount C) * regulatedAmplitude P Φ D C g ![] ![k, -k]
        (lineMomentum₂ C ![] ![] ![k, -k] ℓ) ![] ![] ![μ, ν] := by
  obtain ⟨h2, hd⟩ := t9_two_le_gradedOrder C (by norm_num)
    (t9_pos_of_isOnePI C hC (Or.inr two_pos)) g
  rcases (by omega : gradedOrder κ g = 2 ∨ gradedOrder κ g = 4) with h | h
  · exact t9_vacuumPolarization_two P Φ D H.hε rep m₀ H.hm₀ H.hmass H.hrep H.hPV₁ H.hPV₂ C hC g
      h k μ ν
  · exact t9_vacuumPolarization_four P Φ D H.hε rep m₀ H.hm₀ H.hmass H.hmγ H.hΛ H.hrep H.hPV₁
      H.hPV₂ H.hD C hC g h k μ ν

end Pieces

/-! ### The glues -/

variable {N N₁ N₂ : ℕ} {κ : Fin N → Wick.VertexKind} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}

/-- **The graded orders of the two pieces** of a glue of graded order `5` whose second piece is
1PI with an even number of external photons. -/
theorem t9_split_orders {nf nA : ℕ} (C₂ : Contraction nf nA (rightKinds κ e)) (hC₂ : IsOnePI C₂)
    (h : 2 ∣ nA) (hnf : 0 < nf ∨ 0 < nA) (g : Grading κ) (hg : gradedOrder κ g = 5) :
    gradedOrder (leftKinds κ e) (gradL κ e g) ≤ 3 ∧
      gradedOrder (rightKinds κ e) (gradR κ e g) ≤ 4 := by
  have hs := gradedOrder_split κ e g
  obtain ⟨h2, hd⟩ := t9_two_le_gradedOrder C₂ h (t9_pos_of_isOnePI C₂ hC₂ hnf) (gradR κ e g)
  omega

/-- **The (T₉′) inputs `hT₁`, `hT₂` of `contractionValue_glueIn`.** -/
theorem t9_glueIn (H : T9Hyps P Φ D rep m₀) (C₁ : Contraction 1 1 (leftKinds κ e))
    (C₂ : Contraction 1 0 (rightKinds κ e)) (hA₁ : ExternalsAttached C₁)
    (hV₁ : VerticesConnected C₁) (hC₂ : IsOnePI C₂) (g : Grading κ) (hg : gradedOrder κ g = 5)
    (r' r q : Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    (∀ γ, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₁) fun ℓ =>
      twoPiInv (loopCount C₁) * regulatedAmplitude P Φ D C₁ (gradL κ e g) ![r] ![q]
        (lineMomentum₂ C₁ ![r'] ![r] ![q] ℓ) αOut ![γ] μ) ∧
    (∀ δ, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₂) fun ℓ =>
      twoPiInv (loopCount C₂) * regulatedAmplitude P Φ D C₂ (gradR κ e g) ![r] ![]
        (lineMomentum₂ C₂ ![r] ![r] ![] ℓ) ![δ] βIn ![]) := by
  obtain ⟨hL, hR⟩ := t9_split_orders C₂ hC₂ (by norm_num) (Or.inl one_pos) g hg
  exact ⟨fun γ => t9_vertex_le_three P Φ D H.hε rep H.hrep H.hPV₁ H.hPV₂ H.hD C₁ hA₁ hV₁ _ hL
      r' r q αOut ![γ] μ,
    fun δ => t9_selfEnergy H C₂ hC₂ _ hR r ![δ] βIn⟩

/-- **The (T₉′) inputs `hT₁`, `hT₂` of `contractionValue_glueOut`.** -/
theorem t9_glueOut (H : T9Hyps P Φ D rep m₀) (C₁ : Contraction 1 1 (leftKinds κ e))
    (C₂ : Contraction 1 0 (rightKinds κ e)) (hA₁ : ExternalsAttached C₁)
    (hV₁ : VerticesConnected C₁) (hC₂ : IsOnePI C₂) (g : Grading κ) (hg : gradedOrder κ g = 5)
    (r' r q : Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    (∀ δ, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₁) fun ℓ =>
      twoPiInv (loopCount C₁) * regulatedAmplitude P Φ D C₁ (gradL κ e g) ![r] ![q]
        (lineMomentum₂ C₁ ![r'] ![r] ![q] ℓ) ![δ] βIn μ) ∧
    (∀ γ, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₂) fun ℓ =>
      twoPiInv (loopCount C₂) * regulatedAmplitude P Φ D C₂ (gradR κ e g) ![r'] ![]
        (lineMomentum₂ C₂ ![r'] ![r'] ![] ℓ) αOut ![γ] ![]) := by
  obtain ⟨hL, hR⟩ := t9_split_orders C₂ hC₂ (by norm_num) (Or.inl one_pos) g hg
  exact ⟨fun δ => t9_vertex_le_three P Φ D H.hε rep H.hrep H.hPV₁ H.hPV₂ H.hD C₁ hA₁ hV₁ _ hL
      r' r q ![δ] βIn μ,
    fun γ => t9_selfEnergy H C₂ hC₂ _ hR r' αOut ![γ]⟩

/-- **The (T₉′) inputs `hT₁`, `hT₂` of `contractionValue_glueP`.** -/
theorem t9_glueP (H : T9Hyps P Φ D rep m₀) (C₁ : Contraction 1 1 (leftKinds κ e))
    (C₂ : Contraction 0 2 (rightKinds κ e)) (hA₁ : ExternalsAttached C₁)
    (hV₁ : VerticesConnected C₁) (hC₂ : IsOnePI C₂) (g : Grading κ) (hg : gradedOrder κ g = 5)
    (r' r q : Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    (∀ ν, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₁) fun ℓ =>
      twoPiInv (loopCount C₁) * regulatedAmplitude P Φ D C₁ (gradL κ e g) ![r] ![q]
        (lineMomentum₂ C₁ ![r'] ![r] ![q] ℓ) αOut βIn ![ν]) ∧
    (∀ ρ, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C₂) fun ℓ =>
      twoPiInv (loopCount C₂) * regulatedAmplitude P Φ D C₂ (gradR κ e g) ![] ![q, -q]
        (lineMomentum₂ C₂ ![] ![] ![q, -q] ℓ) ![] ![] ![μ 0, ρ]) := by
  obtain ⟨hL, hR⟩ := t9_split_orders C₂ hC₂ (by norm_num) (Or.inr two_pos) g hg
  exact ⟨fun ν => t9_vertex_le_three P Φ D H.hε rep H.hrep H.hPV₁ H.hPV₂ H.hD C₁ hA₁ hV₁ _ hL
      r' r q αOut βIn ![ν],
    fun ρ => t9_vacuumPolarization H C₂ hC₂ _ hR q (μ 0) ρ⟩

end QED.GradedProof.X1C

end
