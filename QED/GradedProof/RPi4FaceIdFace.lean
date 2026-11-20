/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdRest

/-!
# (R-Π₄) step L6d3: the nonvanishing faces as one-loop limits

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. For a piece
with photon line `γ₀`, the face-sector limits `limUnder atTop (u ↦ u ∫_{face ≤ ρ₀} pieceF)` of
the nonvanishing faces are, up to `iπ²` (self-energy) or `2iπ²` (vertex), the `ε → 0⁺` limits
of one-loop Minkowski integrals `N(x) ∏_{rest} D_l(x)⁻¹`; the rest lines are those of row
`(1, 0)` (loop `1` faces) or `(0, 1)` (loop `0` faces), at `pp l + x`. No sort appears in the
statements (the sort of `faceId_exists_sort` is used internally only):

* **`faceId_face1_se_five`**, **`faceId_face1_se_four`**: self-energy faces at loop `1`
  (pieces with seven resp. six lines), `N` the numerator at the midpoint of the face;
* **`faceId_face1_vtx_four`**, **`faceId_face1_vtx_three`**: vertex faces at loop `1`, `N` the
  half loop-`1` Laplacian on the slice `ℓ₁ = 0` (a constant for three rest lines);
* **`faceId_face0_vtx_four`**, **`faceId_face0_vtx_three`**: vertex faces at loop `0`, `N` the
  half loop-`0` Laplacian on the slice `ℓ₀ = 0`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.Integration.Feynman (simplexSet simplexPoint)

variable {m₀ : ℝ} (hm₀ : 0 < m₀) {k : Fin 4 → ℝ} (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k)
  {Q : LoopQuartic} {BQ : ℝ} (hQB : LQBdd (fun _ : Unit => Q) BQ)
  {ρ₀ c₁ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (hc₁ : 0 < c₁)

/-! ### Loop-`1` self-energy faces -/

section SE

variable {N : (Fin 4 → ℝ) → ℂ} {P : LoopQuartic} (hP1 : LoopDegLe 1 1 P)
  (hPN : ∀ ℓ, P.eval ℓ = N (ℓ 0))

include hm₀ hk hQB hρ₀ hρ₁ hc₁ hP1 hPN

/-- **The loop-`1` self-energy face of a seven-line piece.** -/
theorem faceId_face1_se_five {α : Fin 7 → Fin 2 → ℝ} {γ₀ : Fin 7}
    (huniq : ∀ l, α l = ![1, -1] ↔ l = γ₀)
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (hcard : (Finset.univ.filter fun l => α l ≠ ![1, 0]).card = 2)
    (pp : Fin 7 → Fin 4 → ℝ) (M : Fin 7 → ℝ) (hQ : LoopDegLe 1 1 Q)
    (hV : ∀ w : Fin 7 → ℝ, (∀ l, 0 ≤ w l) → ∑ l, w l = 1 → symanzikU α w ≠ 0 →
      w γ₀ ≤ ρ₀ → c₁ ≤ symanzikV α pp M w)
    (hint : ∀ u : ℝ, 1 ≤ u →
      IntegrableOn (fun x => pieceF 7 Q α pp M γ₀ u (simplexPoint x)) (simplexSet 6))
    (hM : ∀ l, α l = ![1, 0] → m₀ ≤ M l) (hpp : ∀ l, α l = ![1, 0] → pp l = 0 ∨ pp l = k)
    (hP : ∀ f, α f = ![0, 1] → ∀ ℓ₀ : Fin 4 → ℝ,
      Q.eval ![ℓ₀, (1 / 2 : ℝ) • (ℓ₀ + pp γ₀ - pp f)] = N ℓ₀) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun x => N x *
        ∏ l ∈ Finset.univ.filter (fun l => α l = ![1, 0]), (propDenom (M l) ε (pp l + x))⁻¹)
      (𝓝[>] 0) (𝓝 (I * (π : ℂ) ^ 2 * limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet 6,
        {w | faceSum α w ≤ ρ₀}.indicator (pieceF 7 Q α pp M γ₀ u) (simplexPoint x)))) := by
  obtain ⟨e, hS, hγ⟩ := faceId_exists_sort (p := 0) (q := 4) α γ₀ ((huniq γ₀).2 rfl) hrow hcard
  subst hγ
  have h : limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet 6,
      {w | faceSum α w ≤ ρ₀}.indicator (pieceF 7 Q α pp M (FaceSort.gam (p := 0) (q := 4) e) u)
        (simplexPoint x)) =
      faceIdVal 7 (hS.shape pp M) Q :=
    faceId_face_limUnder_sort (p := 0) (q := 4) α hS hrow pp M 7 Q hQB (hQ.mono (by norm_num))
      (fun _ => hQ) (Or.inl rfl) hρ₀ hρ₁ hc₁ hV hint
  rw [h]
  exact faceId_tendsto_se_five hm₀ hk hP1 hPN hS pp M huniq hQ hM hpp hP

/-- **The loop-`1` self-energy face of a six-line piece** (numerators without quartic part). -/
theorem faceId_face1_se_four (hPq : P.quart = 0) {α : Fin 6 → Fin 2 → ℝ} {γ₀ : Fin 6}
    (huniq : ∀ l, α l = ![1, -1] ↔ l = γ₀)
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (hcard : (Finset.univ.filter fun l => α l ≠ ![1, 0]).card = 2)
    (pp : Fin 6 → Fin 4 → ℝ) (M : Fin 6 → ℝ) (hQ : LoopDegLe 1 1 Q) (hQq : Q.quart = 0)
    (hV : ∀ w : Fin 6 → ℝ, (∀ l, 0 ≤ w l) → ∑ l, w l = 1 → symanzikU α w ≠ 0 →
      w γ₀ ≤ ρ₀ → c₁ ≤ symanzikV α pp M w)
    (hint : ∀ u : ℝ, 1 ≤ u →
      IntegrableOn (fun x => pieceF 6 Q α pp M γ₀ u (simplexPoint x)) (simplexSet 5))
    (hM : ∀ l, α l = ![1, 0] → m₀ ≤ M l) (hpp : ∀ l, α l = ![1, 0] → pp l = 0 ∨ pp l = k)
    (hP : ∀ f, α f = ![0, 1] → ∀ ℓ₀ : Fin 4 → ℝ,
      Q.eval ![ℓ₀, (1 / 2 : ℝ) • (ℓ₀ + pp γ₀ - pp f)] = N ℓ₀) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun x => N x *
        ∏ l ∈ Finset.univ.filter (fun l => α l = ![1, 0]), (propDenom (M l) ε (pp l + x))⁻¹)
      (𝓝[>] 0) (𝓝 (I * (π : ℂ) ^ 2 * limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet 5,
        {w | faceSum α w ≤ ρ₀}.indicator (pieceF 6 Q α pp M γ₀ u) (simplexPoint x)))) := by
  obtain ⟨e, hS, hγ⟩ := faceId_exists_sort (p := 0) (q := 3) α γ₀ ((huniq γ₀).2 rfl) hrow hcard
  subst hγ
  have h : limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet 5,
      {w | faceSum α w ≤ ρ₀}.indicator (pieceF 6 Q α pp M (FaceSort.gam (p := 0) (q := 3) e) u)
        (simplexPoint x)) =
      faceIdVal 6 (hS.shape pp M) Q :=
    faceId_face_limUnder_sort (p := 0) (q := 3) α hS hrow pp M 6 Q hQB (hQ.mono (by norm_num))
      (fun _ => hQ) (Or.inr ⟨rfl, hQq⟩) hρ₀ hρ₁ hc₁ hV hint
  rw [h]
  exact faceId_tendsto_se_four hm₀ hk hP1 hPN hPq hS pp M huniq hQ hQq hM hpp hP

end SE

/-! ### Loop-`1` vertex faces -/

section Vtx1

include hm₀ hk hQB hρ₀ hρ₁ hc₁

/-- **The loop-`1` vertex face of a seven-line piece.** -/
theorem faceId_face1_vtx_four {N : (Fin 4 → ℝ) → ℂ} {P : LoopQuartic} (hPq : P.quart = 0)
    (hP1 : LoopDegLe 1 1 P) (hPN : ∀ ℓ, P.eval ℓ = N (ℓ 0)) {α : Fin 7 → Fin 2 → ℝ}
    {γ₀ : Fin 7} (huniq : ∀ l, α l = ![1, -1] ↔ l = γ₀)
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (hcard : (Finset.univ.filter fun l => α l ≠ ![1, 0]).card = 3)
    (pp : Fin 7 → Fin 4 → ℝ) (M : Fin 7 → ℝ) (hQ : LoopDegLe 1 2 Q)
    (hV : ∀ w : Fin 7 → ℝ, (∀ l, 0 ≤ w l) → ∑ l, w l = 1 → symanzikU α w ≠ 0 →
      w γ₀ ≤ ρ₀ → c₁ ≤ symanzikV α pp M w)
    (hint : ∀ u : ℝ, 1 ≤ u →
      IntegrableOn (fun x => pieceF 7 Q α pp M γ₀ u (simplexPoint x)) (simplexSet 6))
    (hM : ∀ l, α l = ![1, 0] → m₀ ≤ M l) (hpp : ∀ l, α l = ![1, 0] → pp l = 0 ∨ pp l = k)
    (hL : ∀ ℓ₀ : Fin 4 → ℝ, faceIdLapF 1 Q.eval ![ℓ₀, 0] = N ℓ₀) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun x => N x *
        ∏ l ∈ Finset.univ.filter (fun l => α l = ![1, 0]), (propDenom (M l) ε (pp l + x))⁻¹)
      (𝓝[>] 0) (𝓝 (2 * I * (π : ℂ) ^ 2 * limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet 6,
        {w | faceSum α w ≤ ρ₀}.indicator (pieceF 7 Q α pp M γ₀ u) (simplexPoint x)))) := by
  obtain ⟨e, hS, hγ⟩ := faceId_exists_sort (p := 1) (q := 3) α γ₀ ((huniq γ₀).2 rfl) hrow hcard
  subst hγ
  have h : limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet 6,
      {w | faceSum α w ≤ ρ₀}.indicator (pieceF 7 Q α pp M (FaceSort.gam (p := 1) (q := 3) e) u)
        (simplexPoint x)) =
      faceIdVal 7 (hS.shape pp M) Q :=
    faceId_face_limUnder_sort (p := 1) (q := 3) α hS hrow pp M 7 Q hQB (hQ.mono (by norm_num))
      (fun h => absurd h one_ne_zero) (Or.inl rfl) hρ₀ hρ₁ hc₁ hV hint
  rw [h]
  exact faceId_tendsto_vtx_four hm₀ hk hPq hP1 hPN hS pp M hQ hM hpp hL

/-- **The loop-`1` vertex face of a six-line piece**: the half Laplacian is a constant `C`. -/
theorem faceId_face1_vtx_three (C : ℂ) {α : Fin 6 → Fin 2 → ℝ} {γ₀ : Fin 6}
    (huniq : ∀ l, α l = ![1, -1] ↔ l = γ₀)
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (hcard : (Finset.univ.filter fun l => α l ≠ ![1, 0]).card = 3)
    (pp : Fin 6 → Fin 4 → ℝ) (M : Fin 6 → ℝ) (hQ : LoopDegLe 1 2 Q) (hQq : Q.quart = 0)
    (hV : ∀ w : Fin 6 → ℝ, (∀ l, 0 ≤ w l) → ∑ l, w l = 1 → symanzikU α w ≠ 0 →
      w γ₀ ≤ ρ₀ → c₁ ≤ symanzikV α pp M w)
    (hint : ∀ u : ℝ, 1 ≤ u →
      IntegrableOn (fun x => pieceF 6 Q α pp M γ₀ u (simplexPoint x)) (simplexSet 5))
    (hM : ∀ l, α l = ![1, 0] → m₀ ≤ M l) (hpp : ∀ l, α l = ![1, 0] → pp l = 0 ∨ pp l = k)
    (hL : ∀ ℓ₀ : Fin 4 → ℝ, faceIdLapF 1 Q.eval ![ℓ₀, 0] = C) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun x => C *
        ∏ l ∈ Finset.univ.filter (fun l => α l = ![1, 0]), (propDenom (M l) ε (pp l + x))⁻¹)
      (𝓝[>] 0) (𝓝 (2 * I * (π : ℂ) ^ 2 * limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet 5,
        {w | faceSum α w ≤ ρ₀}.indicator (pieceF 6 Q α pp M γ₀ u) (simplexPoint x)))) := by
  obtain ⟨e, hS, hγ⟩ := faceId_exists_sort (p := 1) (q := 2) α γ₀ ((huniq γ₀).2 rfl) hrow hcard
  subst hγ
  have h : limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet 5,
      {w | faceSum α w ≤ ρ₀}.indicator (pieceF 6 Q α pp M (FaceSort.gam (p := 1) (q := 2) e) u)
        (simplexPoint x)) =
      faceIdVal 6 (hS.shape pp M) Q :=
    faceId_face_limUnder_sort (p := 1) (q := 2) α hS hrow pp M 6 Q hQB (hQ.mono (by norm_num))
      (fun h => absurd h one_ne_zero) (Or.inr ⟨rfl, hQq⟩) hρ₀ hρ₁ hc₁ hV hint
  rw [h]
  exact faceId_tendsto_vtx_three hm₀ hk C hS pp M hQ hQq hM hpp hL

end Vtx1

/-! ### Loop-`0` vertex faces -/

section Vtx0

include hm₀ hk hQB hρ₀ hρ₁ hc₁

/-- **The loop-`0` vertex face of a seven-line piece**: rest lines of row `(0, 1)`, `N` the half
loop-`0` Laplacian on the slice `ℓ₀ = 0`. -/
theorem faceId_face0_vtx_four {N : (Fin 4 → ℝ) → ℂ} {P : LoopQuartic} (hPq : P.quart = 0)
    (hP1 : LoopDegLe 1 1 P) (hPN : ∀ ℓ, P.eval ℓ = N (ℓ 0)) {α : Fin 7 → Fin 2 → ℝ}
    {γ₀ : Fin 7} (huniq : ∀ l, α l = ![1, -1] ↔ l = γ₀)
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (hcard : (Finset.univ.filter fun l => α l ≠ ![0, 1]).card = 3)
    (pp : Fin 7 → Fin 4 → ℝ) (M : Fin 7 → ℝ) (hQ : LoopDegLe 0 2 Q)
    (hV : ∀ w : Fin 7 → ℝ, (∀ l, 0 ≤ w l) → ∑ l, w l = 1 → symanzikU α w ≠ 0 →
      w γ₀ ≤ ρ₀ → c₁ ≤ symanzikV α pp M w)
    (hint : ∀ u : ℝ, 1 ≤ u →
      IntegrableOn (fun x => pieceF 7 Q α pp M γ₀ u (simplexPoint x)) (simplexSet 6))
    (hM : ∀ l, α l = ![0, 1] → m₀ ≤ M l) (hpp : ∀ l, α l = ![0, 1] → pp l = 0 ∨ pp l = k)
    (hL : ∀ x : Fin 4 → ℝ, faceIdLapF 0 Q.eval ![0, x] = N x) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun x => N x *
        ∏ l ∈ Finset.univ.filter (fun l => α l = ![0, 1]), (propDenom (M l) ε (pp l + x))⁻¹)
      (𝓝[>] 0) (𝓝 (2 * I * (π : ℂ) ^ 2 * limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet 6,
        {w | faceSum0 α w ≤ ρ₀}.indicator (pieceF 7 Q α pp M γ₀ u) (simplexPoint x)))) := by
  have hγ' : swapFlip α γ₀ = ![1, -1] := swapFlip_row_1m1 ((huniq γ₀).2 rfl)
  obtain ⟨e, hS, hγ⟩ := faceId_exists_sort (p := 1) (q := 3) (swapFlip α) γ₀ hγ'
    (faceId_hrow_swapFlip hrow) (by rw [filter_swapFlip hrow]; exact hcard)
  subst hγ
  have h : limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet 6,
      {w | faceSum0 α w ≤ ρ₀}.indicator (pieceF 7 Q α pp M (FaceSort.gam (p := 1) (q := 3) e) u)
        (simplexPoint x)) =
      faceIdVal 7 (hS.shape (flipMom (photonSign α) pp) M) (swapQ Q) :=
    faceId_face_limUnder_sort0 (p := 1) (q := 3) α hS hrow pp M 7 Q hQB (hQ.mono (by norm_num))
      (fun h => absurd h one_ne_zero) (Or.inl rfl) hρ₀ hρ₁ hc₁ hV hint
  rw [h]
  have ht := faceId_tendsto_vtx_four hm₀ hk hPq hP1 hPN hS (flipMom (photonSign α) pp) M
    (loopDegLe_swapQ hQ) (fun l hl => hM l ((faceId_swapFlip_10_iff hrow l).1 hl))
    (fun l hl => by
      rw [faceId_flipMom_of_row01 pp ((faceId_swapFlip_10_iff hrow l).1 hl)]
      exact hpp l ((faceId_swapFlip_10_iff hrow l).1 hl))
    fun x => (faceId_lapF_swapQ Q x).trans (hL x)
  have hprod : ∀ (ε : ℝ) (x : Fin 4 → ℝ),
      ∏ l ∈ Finset.univ.filter (fun l => swapFlip α l = ![1, 0]),
        (propDenom (M l) ε (flipMom (photonSign α) pp l + x))⁻¹ =
      ∏ l ∈ Finset.univ.filter (fun l => α l = ![0, 1]), (propDenom (M l) ε (pp l + x))⁻¹ := by
    intro ε x
    rw [faceId_filter_swapFlip_10 hrow]
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [faceId_flipMom_of_row01 pp (Finset.mem_filter.1 hl).2]
  simp only [hprod] at ht
  exact ht

/-- **The loop-`0` vertex face of a six-line piece**: the half loop-`0` Laplacian is a
constant `C`. -/
theorem faceId_face0_vtx_three (C : ℂ) {α : Fin 6 → Fin 2 → ℝ} {γ₀ : Fin 6}
    (huniq : ∀ l, α l = ![1, -1] ↔ l = γ₀)
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (hcard : (Finset.univ.filter fun l => α l ≠ ![0, 1]).card = 3)
    (pp : Fin 6 → Fin 4 → ℝ) (M : Fin 6 → ℝ) (hQ : LoopDegLe 0 2 Q) (hQq : Q.quart = 0)
    (hV : ∀ w : Fin 6 → ℝ, (∀ l, 0 ≤ w l) → ∑ l, w l = 1 → symanzikU α w ≠ 0 →
      w γ₀ ≤ ρ₀ → c₁ ≤ symanzikV α pp M w)
    (hint : ∀ u : ℝ, 1 ≤ u →
      IntegrableOn (fun x => pieceF 6 Q α pp M γ₀ u (simplexPoint x)) (simplexSet 5))
    (hM : ∀ l, α l = ![0, 1] → m₀ ≤ M l) (hpp : ∀ l, α l = ![0, 1] → pp l = 0 ∨ pp l = k)
    (hL : ∀ x : Fin 4 → ℝ, faceIdLapF 0 Q.eval ![0, x] = C) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun x => C *
        ∏ l ∈ Finset.univ.filter (fun l => α l = ![0, 1]), (propDenom (M l) ε (pp l + x))⁻¹)
      (𝓝[>] 0) (𝓝 (2 * I * (π : ℂ) ^ 2 * limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet 5,
        {w | faceSum0 α w ≤ ρ₀}.indicator (pieceF 6 Q α pp M γ₀ u) (simplexPoint x)))) := by
  have hγ' : swapFlip α γ₀ = ![1, -1] := swapFlip_row_1m1 ((huniq γ₀).2 rfl)
  obtain ⟨e, hS, hγ⟩ := faceId_exists_sort (p := 1) (q := 2) (swapFlip α) γ₀ hγ'
    (faceId_hrow_swapFlip hrow) (by rw [filter_swapFlip hrow]; exact hcard)
  subst hγ
  have h : limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet 5,
      {w | faceSum0 α w ≤ ρ₀}.indicator (pieceF 6 Q α pp M (FaceSort.gam (p := 1) (q := 2) e) u)
        (simplexPoint x)) =
      faceIdVal 6 (hS.shape (flipMom (photonSign α) pp) M) (swapQ Q) :=
    faceId_face_limUnder_sort0 (p := 1) (q := 2) α hS hrow pp M 6 Q hQB (hQ.mono (by norm_num))
      (fun h => absurd h one_ne_zero) (Or.inr ⟨rfl, hQq⟩) hρ₀ hρ₁ hc₁ hV hint
  rw [h]
  have ht := faceId_tendsto_vtx_three hm₀ hk C hS (flipMom (photonSign α) pp) M
    (loopDegLe_swapQ hQ) (quart_swapQ hQq) (fun l hl => hM l ((faceId_swapFlip_10_iff hrow l).1 hl))
    (fun l hl => by
      rw [faceId_flipMom_of_row01 pp ((faceId_swapFlip_10_iff hrow l).1 hl)]
      exact hpp l ((faceId_swapFlip_10_iff hrow l).1 hl))
    fun x => (faceId_lapF_swapQ Q x).trans (hL x)
  have hprod : ∀ (ε : ℝ) (x : Fin 4 → ℝ),
      ∏ l ∈ Finset.univ.filter (fun l => swapFlip α l = ![1, 0]),
        (propDenom (M l) ε (flipMom (photonSign α) pp l + x))⁻¹ =
      ∏ l ∈ Finset.univ.filter (fun l => α l = ![0, 1]), (propDenom (M l) ε (pp l + x))⁻¹ := by
    intro ε x
    rw [faceId_filter_swapFlip_10 hrow]
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [faceId_flipMom_of_row01 pp (Finset.mem_filter.1 hl).2]
  simp only [hprod] at ht
  exact ht

end Vtx0

end QED.GradedProof.RPi4

end
