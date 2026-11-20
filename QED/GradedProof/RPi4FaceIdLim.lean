/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4Sectors

/-!
# (R-Π₄) step L6d3: the face limits as unique limits; vanishing faces

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3 (face
identification). The per-piece rate `piece_rate` returns its limit `L` existentially. A rate
`‖f u - L‖ ≤ C u^{-1/2}` for `u ≥ 1` determines `L` as the limit of `f` at infinity, so the
face limits can be named as `limUnder atTop (fun u => u • ∫ pieceF)` and summed over pieces and
flavours; the identification with the counterterm insertions is then a statement about this one
named limit.

* `faceId_tendsto_of_rate`, `faceId_eq_limUnder_of_rate`: a `u^{-1/2}` rate determines the limit.
* `faceId_rate_sum`: rates add over a finite family, with the sum of the limits.
* `faceId_piece_rate`: `piece_rate` with its limit named, `limUnder atTop (u • ∫ pieceF)`, when
  `pieceF u` is integrable for every `u ≥ 1`.
* `FaceShape.faceId_gJ_zero_eq_zero`, `FaceShape.faceId_face_limit_eq_zero`: a face whose block
  has more fermion lines than the degree of its bracket (`B.d < p`) has limit `0`: this covers the
  faces of the pieces with an auxiliary Pauli–Villars line inside the subgraph and the
  non-logarithmic faces.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint)

section Unique

/-- **A rate `C u^{-1/2}` gives convergence.** -/
theorem faceId_tendsto_of_rate {f : ℝ → ℂ} {L : ℂ} {C : ℝ}
    (h : ∀ u : ℝ, 1 ≤ u → ‖f u - L‖ ≤ C * u ^ (-(1 / 2) : ℝ)) :
    Tendsto f atTop (𝓝 L) := by
  have hr : Tendsto (fun u : ℝ => C * u ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C
  refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' ?_ ?_ hr)
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [eventually_ge_atTop 1] with u hu using h u hu

/-- **The limit in a `u^{-1/2}` rate is the limit of the function.** -/
theorem faceId_eq_limUnder_of_rate {f : ℝ → ℂ} {L : ℂ} {C : ℝ}
    (h : ∀ u : ℝ, 1 ≤ u → ‖f u - L‖ ≤ C * u ^ (-(1 / 2) : ℝ)) :
    limUnder atTop f = L :=
  (faceId_tendsto_of_rate h).limUnder_eq

/-- **The rate with the limit named.** -/
theorem faceId_rate_limUnder {f : ℝ → ℂ} {L : ℂ} {C : ℝ}
    (h : ∀ u : ℝ, 1 ≤ u → ‖f u - L‖ ≤ C * u ^ (-(1 / 2) : ℝ)) :
    ∀ u : ℝ, 1 ≤ u → ‖f u - limUnder atTop f‖ ≤ C * u ^ (-(1 / 2) : ℝ) := by
  rw [faceId_eq_limUnder_of_rate h]
  exact h

/-- **Rates add over a finite family.** -/
theorem faceId_rate_sum {κ : Type*} (t : Finset κ) {f : κ → ℝ → ℂ} {L : κ → ℂ} {C : κ → ℝ}
    (h : ∀ i ∈ t, ∀ u : ℝ, 1 ≤ u → ‖f i u - L i‖ ≤ C i * u ^ (-(1 / 2) : ℝ)) :
    ∀ u : ℝ, 1 ≤ u →
      ‖∑ i ∈ t, f i u - ∑ i ∈ t, L i‖ ≤ (∑ i ∈ t, C i) * u ^ (-(1 / 2) : ℝ) := by
  intro u hu
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => h i hi u hu)

/-- **The limit of a finite sum of functions with rates is the sum of their limits.** -/
theorem faceId_limUnder_sum {κ : Type*} (t : Finset κ) {f : κ → ℝ → ℂ} {L : κ → ℂ}
    {C : κ → ℝ} (h : ∀ i ∈ t, ∀ u : ℝ, 1 ≤ u → ‖f i u - L i‖ ≤ C i * u ^ (-(1 / 2) : ℝ)) :
    limUnder atTop (fun u => ∑ i ∈ t, f i u) = ∑ i ∈ t, limUnder atTop (f i) := by
  rw [faceId_eq_limUnder_of_rate (faceId_rate_sum t h)]
  exact Finset.sum_congr rfl fun i hi => (faceId_eq_limUnder_of_rate (h i hi)).symm

end Unique

section Piece

variable {m : ℕ}

/-- **`piece_rate` with its limit named**: for a collapsed piece whose integrand is integrable at
every `u ≥ 1`, `u • ∫ pieceF` converges, uniformly over the family at the rate `u^{-1/2}`, to
`limUnder atTop (fun u => u • ∫ pieceF)`. The hypotheses are those of `piece_rate`. -/
theorem faceId_piece_rate {ι : Type*} {n : ℕ} (hnm : n - 3 < m) (α : Fin (m + 1) → Fin 2 → ℝ)
    (γ₀ : Fin (m + 1)) (huniq : ∀ l, α l = ![1, -1] ↔ l = γ₀)
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (hA1 : 2 ≤ (Finset.univ.filter fun l => α l ≠ ![1, 0]).card) (hR1 : ∃ l, α l = ![1, 0])
    (hA0 : 2 ≤ (Finset.univ.filter fun l => α l ≠ ![0, 1]).card) (hR0 : ∃ l, α l = ![0, 1])
    (cs : Fin (m + 1) → ℝ) (k : ι → Fin 4 → ℝ) (M : ι → Fin (m + 1) → ℝ)
    (Q Q₁ Q₀ : ι → LoopQuartic) {BQ B₁ B₀ : ℝ} (hQ : LQBdd Q BQ) (hQ₁ : LQBdd Q₁ B₁)
    (hQ₀ : LQBdd Q₀ B₀) (he₁ : ∀ s, (Q₁ s).eval = (Q s).eval)
    (he₀ : ∀ s, (Q₀ s).eval = (Q s).eval)
    (hd1 : ∀ s, LoopDegLe 1 3 (Q₁ s))
    (hd11 : (Finset.univ.filter fun l => α l ≠ ![1, 0]).card = 2 → ∀ s, LoopDegLe 1 1 (Q₁ s))
    (hd0 : ∀ s, LoopDegLe 0 3 (Q₀ s))
    (hd01 : (Finset.univ.filter fun l => α l ≠ ![0, 1]).card = 2 → ∀ s, LoopDegLe 0 1 (Q₀ s))
    (hn : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0 ∧ (Q₁ s).quart = 0 ∧ (Q₀ s).quart = 0))
    {KP KM c₀ : ℝ} (hk : ∀ s, ‖k s‖ ≤ KP) (hM : ∀ s l, |M s l| ≤ KM) (hc₀ : 0 < c₀)
    (hV : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 → symanzikU α w ≠ 0 →
      c₀ * ferSum α w ≤ symanzikV α (fun i => cs i • k s) (M s) w)
    (hint : ∀ s, ∀ u : ℝ, 1 ≤ u →
      IntegrableOn (fun x => pieceF n (Q s) α (fun i => cs i • k s) (M s) γ₀ u (simplexPoint x))
        (simplexSet m)) :
    ∃ C : ℝ, ∀ s, ∀ u : ℝ, 1 ≤ u →
      ‖u • (∫ x in simplexSet m,
          pieceF n (Q s) α (fun i => cs i • k s) (M s) γ₀ u (simplexPoint x)) -
        limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet m,
          pieceF n (Q s) α (fun i => cs i • k s) (M s) γ₀ u (simplexPoint x))‖ ≤
        C * u ^ (-(1 / 2) : ℝ) := by
  obtain ⟨C, L, hC⟩ := piece_rate hnm α γ₀ huniq hrow hA1 hR1 hA0 hR0 cs k M Q Q₁ Q₀ hQ hQ₁
    hQ₀ he₁ he₀ hd1 hd11 hd0 hd01 hn hk hM hc₀ hV
  exact ⟨C, fun s => faceId_rate_limUnder fun u hu => hC s u hu (hint s u hu)⟩

end Piece

section Vanish

variable {p q r : ℕ} (S : FaceShape p q) (B : FaceBr r)

/-- **A face with more fermion lines than the order of its bracket vanishes at `ρ = 0`**: the
rescaled coefficients carry `ρ^{p - d}`. -/
theorem FaceShape.faceId_coefJ_zero_eq_zero (hd : B.d < p) (j : Fin r) (W : Fin (p + 1) → ℝ)
    (V : Fin (q + 1) → ℝ) : S.coefJ B j 0 W V = 0 := by
  have hpd : p - B.d ≠ 0 := by omega
  simp [FaceShape.coefJ, zero_pow hpd]

theorem FaceShape.faceId_gJ_zero_eq_zero (hd : B.d < p) (σ : ℝ) : S.gJ B 0 σ = 0 := by
  simp [FaceShape.gJ, FaceShape.hJ, S.faceId_coefJ_zero_eq_zero B hd]

/-- **The face limit of a vanishing face is `0`**: the face-sector rate of `face_sector_rate`
with the limit `∫₀^∞ gJ(0, σ) = 0`. -/
theorem FaceShape.faceId_face_limit_eq_zero {ι : Type*} {p : ℕ} {S : ι → FaceShape (p + 1) q}
    {B : ι → FaceBr r} {k : Fin r → ℕ} {ρ₀ c₁ K KM : ℝ} (h : FamHyp S B k ρ₀ c₁ K KM)
    (hγ : ∀ s, (S s).γ = Fin.last (p + 1)) {n : ℕ} {Q : ι → LoopQuartic}
    (hRep : ∀ s, (B s).Rep n (p + 1) (Q s) (S s).α (S s).pp) (hd : ∀ s, (B s).d < p + 1) :
    ∃ C : ℝ, ∀ s, ∀ u : ℝ, 0 < u →
      IntegrableOn (fun x => (S s).fU n (Q s) u (simplexPoint x)) (simplexSet (p + 1 + 1 + q)) →
      ‖u • (∫ x in simplexSet (p + 1 + 1 + q),
          {z | blockSum z ≤ ρ₀}.indicator ((S s).fU n (Q s) u) (simplexPoint x))‖ ≤
        C * u ^ (-(1 / 2) : ℝ) := by
  obtain ⟨C, hC⟩ := FaceShape.face_sector_rate h hγ hRep
  refine ⟨C, fun s u hu hf => ?_⟩
  have h0 : ∫ σ in Ioi 0, (S s).gJ (B s) 0 σ = 0 := by
    simp [(S s).faceId_gJ_zero_eq_zero (B s) (hd s)]
  simpa [h0] using hC s u hu hf

end Vanish

end QED.GradedProof.RPi4

end
