/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CT9Base
public import QED.GradedProof.X0ClosedEnum

/-!
# (X₁) piece C: (T₉′) of the vertex pieces of graded order at most `3`

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C. Peeling one 1PI self-energy or vacuum-polarization piece (graded
order `2` or `4`) off an order-`e⁵` vertex graph leaves a vertex contraction `C₁ : (1, 1)` of
graded order `3` or `1`, attached and connected (not necessarily 1PI). Its grading is `0`
(`t9_grading_eq_zero`) and `2 L + 3 = V₃ + 2` with `V₃ ≤ 3`, so `L ≤ 1`; at `L = 1` all three
vertices are `gauge` (`t9_eq_kggg`). The one-loop contractions of `ggg` pass the open-line test
`OneCrit` of (X₀) when every fermion field lies on the external cycle (the triangle, a
self-energy on a leg) and the closed-loop test `ClosedCrit` otherwise (a bubble on the photon
leg, a tadpole): kernel evaluation over the `24` fermion pairings and the `3` photon pairings
(`t9_oneCtCheck_ggg`, `t9_closedCheck_ggg`). Hence (`t9_vertex_le_three`) the integrand of `C₁`
satisfies (T₉′) under the block hypotheses of (X₀), in the form of `hT₁` of the value lemmas.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Params Contraction loopCount lineMomentum₂ VerticesConnected
  ExternalsAttached)
open QED.Graded
open QED.TwoLoop.Enumeration (photonPermK psK IsInvolK)

/-- The kind sequence `ggg`. -/
def t9_kggg : Fin 3 → Wick.VertexKind := ![.gauge, .gauge, .gauge]

/-- The photon pairings of `ggg` with one external photon. -/
def t9_invs_ggg : List (Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot t9_kggg)) :=
  [photonPermK t9_kggg (psK t9_kggg 0 0) [(psK t9_kggg 1 0, psK t9_kggg 2 0)],
    photonPermK t9_kggg (psK t9_kggg 1 0) [(psK t9_kggg 0 0, psK t9_kggg 2 0)],
    photonPermK t9_kggg (psK t9_kggg 2 0) [(psK t9_kggg 0 0, psK t9_kggg 1 0)]]

theorem t9_invs_ggg_invol : ∀ τ ∈ t9_invs_ggg, IsInvolK τ := by decide +kernel

theorem t9_invs_ggg_complete : ∀ τ : Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot t9_kggg),
    IsInvolK τ → τ ∈ t9_invs_ggg := by decide +kernel

theorem t9_oneCtCheck_ggg : X0.OneCtCheck t9_invs_ggg t9_invs_ggg_invol := by
  unfold X0.OneCtCheck
  decide +kernel

theorem t9_closedCheck_ggg : X0.ClosedCheck t9_invs_ggg t9_invs_ggg_invol := by
  unfold X0.ClosedCheck
  decide +kernel

/-- The only kind sequence of three vertices and total order at most `3`. -/
theorem t9_eq_kggg : ∀ κ : Fin 3 → Wick.VertexKind, ∑ t, (κ t).order ≤ 3 → κ = t9_kggg := by
  decide

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}
  (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F)

/-- **(T₉′) of an attached connected vertex piece of graded order at most `3`**, in the form of
`hT₁` of `contractionValue_glueIn`, `contractionValue_glueOut`, `contractionValue_glueP` (any
external momenta). -/
theorem t9_vertex_le_three (hε : 0 < P.ε) (rep : F → F) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0)
    (C : Contraction 1 1 κ) (hA : ExternalsAttached C) (hV : VerticesConnected C)
    (g : Grading κ) (hg : gradedOrder κ g ≤ 3) (r' r q : Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      twoPiInv (loopCount C) * regulatedAmplitude P Φ D C g ![r] ![q]
        (lineMomentum₂ C ![r'] ![r] ![q] ℓ) αOut βIn μ := by
  obtain rfl := t9_grading_eq_zero hg
  have h3 : ∑ t, (κ t).order ≤ 3 := by rw [← X0.gradedOrder_zero]; exact hg
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exfalso
    rcases h : C.1.1 (.inl 0) with i | t
    · exact hA.1 0 i h
    · exact t.1.elim0
  have heq := QED.TwoLoop.LoopBoundTwo.two_mul_loopCount_add_eq hA hV hN
  have hcard := Finset.card_le_univ (Finset.univ.filter fun t => κ t = .gauge ∨ κ t = .gaugeCt)
  have hNle := QED.TwoLoop.Enumeration.le_sum_order κ
  rw [Fintype.card_fin] at hcard
  have hL : loopCount C = 0 ∨ loopCount C = 1 := by omega
  rcases hL with h0 | h1
  · exact X0.jointEnergyFirstIntegrable_of_loopCount_eq_zero _ h0
  obtain rfl : N = 3 := by omega
  obtain rfl := t9_eq_kggg κ h3
  by_cases hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)
  · exact X0.jointEnergyFirstIntegrable_openCt P Φ D hε C hcyc h1
      (X0.oneCrit_of_check t9_invs_ggg_complete t9_oneCtCheck_ggg C hcyc hV) ![r'] ![r] ![q]
      αOut βIn μ
  obtain ⟨c1, c2, c3, c4, c5⟩ :=
    X0.closedCrit_of_check t9_invs_ggg_complete t9_closedCheck_ggg C hA hcyc hV
  have hC : X0.ClosedShape C (X0.zOf C) := ⟨X0.isZ_zOf_apply C, fun t ht => not_not.mp ht, c1⟩
  exact X0.jointEnergyFirstIntegrable_closedOne P Φ D rep hrep hPV₁ hPV₂ hD hε C hC h1 c2 c3 c4
    c5 ![r'] ![r] ![q] αOut βIn μ

end QED.GradedProof.X1C

end
