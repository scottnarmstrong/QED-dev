/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdLoop1

/-!
# (R-Π₄) step L6d3: the limit of a piece is the sum of its two face limits

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. Under the
hypotheses of `piece_rate`, the limit `lim_{u → ∞} u ∫ pieceF` of a collapsed piece is the sum
of the limits of its loop-`1` face sector (`faceSum ≤ 1/4`) and its loop-`0` face sector
(`faceSum0 ≤ 1/4`): the corner and bulk sectors contribute `0`. Each face limit is a face value
`faceIdVal` of a sorted shape (`faceId_face_limUnder_sort`; for loop `0` after exchanging the
loops and reversing the photon, `faceId_face_limUnder_sort0`).

* **`faceId_piece_limUnder`**: piece limit = loop-`1` face limit + loop-`0` face limit;
* **`faceId_face_limUnder_sort0`**: the loop-`0` face limit is the face value of the sorted
  shape of the exchanged piece (`swapFlip`, `flipMom`, `swapQ`).
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet
  simplexPoint_mem_stdSimplex)

variable {m : ℕ}

/-- **The limit of a collapsed piece is the sum of its two face limits** (hypotheses of
`piece_rate`, the integrand integrable at every `u ≥ 1`): the corner and bulk sectors vanish in
the limit. -/
theorem faceId_piece_limUnder {ι : Type*} {n : ℕ} (hnm : n - 3 < m) (α : Fin (m + 1) → Fin 2 → ℝ)
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
        (simplexSet m)) (s : ι) :
    limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet m,
        pieceF n (Q s) α (fun i => cs i • k s) (M s) γ₀ u (simplexPoint x)) =
      limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet m,
        {w | faceSum α w ≤ 1 / 4}.indicator
          (pieceF n (Q s) α (fun i => cs i • k s) (M s) γ₀ u) (simplexPoint x)) +
      limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet m,
        {w | faceSum0 α w ≤ 1 / 4}.indicator
          (pieceF n (Q s) α (fun i => cs i • k s) (M s) γ₀ u) (simplexPoint x)) := by
  have hγ : α γ₀ = ![1, -1] := (huniq γ₀).mpr rfl
  set ρ₀ : ℝ := 1 / 4 with hρ₀
  set c₁ : ℝ := c₀ / 4 with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  set pp : ι → Fin (m + 1) → Fin 4 → ℝ := fun s i => cs i • k s with hpp
  set KP' : ℝ := (∑ l, |cs l|) * KP
  have hP : ∀ s l, ‖pp s l‖ ≤ KP' := fun s l => by
    simp only [hpp, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (Finset.single_le_sum (f := fun l => |cs l|) (fun l _ => abs_nonneg _)
      (Finset.mem_univ l)) (hk s) (norm_nonneg _) (Finset.sum_nonneg fun l _ => abs_nonneg _)
  have hkμ : ∀ s μ, |k s μ| ≤ KP := fun s μ => (norm_le_pi_norm (k s) μ).trans (hk s)
  -- the lower bounds of `V₀` in the forms the four sectors ask for
  have hVface : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w γ₀ ≤ ρ₀ → c₁ ≤ symanzikV α (pp s) (M s) w := fun s w hw hw1 hU h => by
    have := hV s w hw hw1 hU
    rw [ferSum_eq_one_sub huniq hw1] at this
    have h' : w γ₀ ≤ 1 / 4 := h
    have : c₀ * (3 / 4) ≤ c₀ * (1 - w γ₀) := mul_le_mul_of_nonneg_left (by linarith) hc₀.le
    linarith
  have hVbulk : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      w ∈ bulkSet α ρ₀ → c₁ ≤ symanzikV α (pp s) (M s) w := fun s w hw hw1 hb => by
    have hU := symanzikU_ge_bulk hrow w (by norm_num) hw hw1 hb
    have := hV s w hw hw1 (by positivity)
    have : c₀ * (1 / 4) ≤ c₀ * ferSum α w := mul_le_mul_of_nonneg_left hb.2.2.le hc₀.le
    linarith
  have hVcorner : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      w ∈ cornerSet α ρ₀ → symanzikU α w ≠ 0 → 0 ≤ symanzikV α (pp s) (M s) w :=
    fun s w hw hw1 _ hU => by
      have := hV s w hw hw1 hU
      have : 0 ≤ c₀ * ferSum α w := mul_nonneg hc₀.le (Finset.sum_nonneg fun l _ => hw l)
      linarith
  have hm0 : 0 < m := by rcases hn with rfl | ⟨rfl, -⟩ <;> omega
  have hnQ : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0) := by
    rcases hn with h | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, fun s => (h' s).1⟩
  have hnQ₁ : n = 7 ∨ (n = 6 ∧ ∀ s, (Q₁ s).quart = 0) := by
    rcases hn with h | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, fun s => (h' s).2.1⟩
  have hnQ₀ : n = 7 ∨ (n = 6 ∧ ∀ s, (Q₀ s).quart = 0) := by
    rcases hn with h | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, fun s => (h' s).2.2⟩
  have hF : ∀ (P : ι → LoopQuartic), (∀ s, (P s).eval = (Q s).eval) →
      ∀ s, pieceF n (P s) α (pp s) (M s) γ₀ = pieceF n (Q s) α (pp s) (M s) γ₀ :=
    fun P hP s => by
      funext u z
      simp only [pieceF, paramAtV_congr (hP s)]
  obtain ⟨C₁, L₁, h₁⟩ := face_rate_loop1 α γ₀ hγ hrow hA1 hR1 pp M n Q₁ hQ₁ hd1 hd11 hnQ₁
    (by norm_num) (by norm_num) hc₁0 hP hM hVface
  obtain ⟨C₀, L₀, h₀⟩ := face_rate_loop0 α γ₀ hγ hrow hA0 hR0 pp M n Q₀ hQ₀ hd0 hd01 hnQ₀
    (by norm_num) (by norm_num) hc₁0 hP hM hVface
  simp only [hF Q₁ he₁] at h₁
  simp only [hF Q₀ he₀] at h₀
  obtain ⟨Cc, hc⟩ := corner_rate hnm α γ₀ huniq hrow cs k M Q hQ hnQ (by norm_num) (by norm_num)
    hkμ hVcorner
  obtain ⟨Cb, hb⟩ := bulk_rate hm0 α γ₀ hrow pp M n Q hQ hnQ (by norm_num) hc₁0 hP hVbulk
  have hinv : ∀ u : ℝ, 1 ≤ u → u⁻¹ ≤ u ^ (-(1 / 2) : ℝ) := fun u hu => by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hu (by norm_num)
  have l1 : limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet m,
      {w | faceSum α w ≤ ρ₀}.indicator (pieceF n (Q s) α (pp s) (M s) γ₀ u) (simplexPoint x)) =
      L₁ s := faceId_eq_limUnder_of_rate fun u hu => h₁ s u (one_pos.trans_le hu) (hint s u hu)
  have l0 : limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet m,
      {w | faceSum0 α w ≤ ρ₀}.indicator (pieceF n (Q s) α (pp s) (M s) γ₀ u) (simplexPoint x)) =
      L₀ s := faceId_eq_limUnder_of_rate fun u hu => h₀ s u (one_pos.trans_le hu) (hint s u hu)
  rw [l1, l0]
  refine faceId_eq_limUnder_of_rate (C := C₁ + C₀ + |Cc| + Cb) fun u hu => ?_
  have hI := hint s u hu
  have hu0 : 0 < u := one_pos.trans_le hu
  have hsplit := integral_sector_eq hrow (ρ₀ := ρ₀) (by norm_num) hI
  have e1 := h₁ s u hu0 hI
  have e0 := h₀ s u hu0 hI
  have ec := hc s u hu
  have eb := hb s u hu0
  have ec' : ‖u • ∫ x in simplexSet m, (cornerSet α ρ₀).indicator
      (pieceF n (Q s) α (pp s) (M s) γ₀ u) (simplexPoint x)‖ ≤ |Cc| * u ^ (-(1 / 2) : ℝ) :=
    ec.trans (mul_le_mul (le_abs_self _) (hinv u hu) (by positivity) (abs_nonneg _))
  rw [hsplit, smul_add, smul_add, smul_add]
  set a := u • ∫ x in simplexSet m, {w | faceSum α w ≤ ρ₀}.indicator
    (pieceF n (Q s) α (pp s) (M s) γ₀ u) (simplexPoint x)
  set b := u • ∫ x in simplexSet m, {w | faceSum0 α w ≤ ρ₀}.indicator
    (pieceF n (Q s) α (pp s) (M s) γ₀ u) (simplexPoint x)
  set c := u • ∫ x in simplexSet m, (cornerSet α ρ₀).indicator
    (pieceF n (Q s) α (pp s) (M s) γ₀ u) (simplexPoint x)
  set d := u • ∫ x in simplexSet m, (bulkSet α ρ₀).indicator
    (pieceF n (Q s) α (pp s) (M s) γ₀ u) (simplexPoint x)
  have e : a + b + c + d - (L₁ s + L₀ s) = (a - L₁ s) + (b - L₀ s) + c + d := by ring
  rw [e]
  calc ‖(a - L₁ s) + (b - L₀ s) + c + d‖ ≤ ‖a - L₁ s‖ + ‖b - L₀ s‖ + ‖c‖ + ‖d‖ :=
        norm_add₄_le
    _ ≤ C₁ * u ^ (-(1 / 2) : ℝ) + C₀ * u ^ (-(1 / 2) : ℝ) + |Cc| * u ^ (-(1 / 2) : ℝ) +
          Cb * u ^ (-(1 / 2) : ℝ) := by gcongr
    _ = _ := by ring

/-- **The loop-`0` face limit of a piece is a face value**: for a permutation `e` sorting the
exchanged piece (`swapFlip α`, photon `γ₀` last in the face block),
`limUnder atTop (u ↦ u ∫_{faceSum0 ≤ ρ₀} pieceF) = faceIdVal` of the sorted shape with the
reversed momenta `flipMom` and the exchanged numerator `swapQ Q`. -/
theorem faceId_face_limUnder_sort0 {p q : ℕ} (α : Fin (p + 1 + 1 + q + 1) → Fin 2 → ℝ)
    {e : Equiv.Perm (Fin (p + 1 + 1 + q + 1))} (hS : FaceSort p q (swapFlip α) e)
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (pp : Fin (p + 1 + 1 + q + 1) → Fin 4 → ℝ) (M : Fin (p + 1 + 1 + q + 1) → ℝ)
    (n : ℕ) (Q : LoopQuartic) {BQ : ℝ} (hQ : LQBdd (fun _ : Unit => Q) BQ)
    (hd : LoopDegLe 0 3 Q) (hd1 : p = 0 → LoopDegLe 0 1 Q) (hn : n = 7 ∨ (n = 6 ∧ Q.quart = 0))
    {ρ₀ c₁ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (hc₁ : 0 < c₁)
    (hV : ∀ w : Fin (p + 1 + 1 + q + 1) → ℝ, (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w (FaceSort.gam e) ≤ ρ₀ → c₁ ≤ symanzikV α pp M w)
    (hint : ∀ u : ℝ, 1 ≤ u →
      IntegrableOn (fun x => pieceF n Q α pp M (FaceSort.gam e) u (simplexPoint x))
        (simplexSet (p + 1 + 1 + q))) :
    limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet (p + 1 + 1 + q),
        {w | faceSum0 α w ≤ ρ₀}.indicator (pieceF n Q α pp M (FaceSort.gam e) u)
          (simplexPoint x)) = faceIdVal n (hS.shape (flipMom (photonSign α) pp) M) (swapQ Q) := by
  have hrow' : ∀ l, swapFlip α l = ![1, 0] ∨ swapFlip α l = ![0, 1] ∨
      swapFlip α l = ![1, -1] := fun l => by
    rcases hrow l with h | h | h
    · exact Or.inr (Or.inl (swapFlip_row_10 h))
    · exact Or.inl (swapFlip_row_01 h)
    · exact Or.inr (Or.inr (swapFlip_row_1m1 h))
  have e1 : ∀ u, pieceF n (swapQ Q) (swapFlip α) (flipMom (photonSign α) pp) M
      (FaceSort.gam e) u = pieceF n Q α pp M (FaceSort.gam e) u := fun u =>
    funext fun w => pieceF_swapFlip α pp M w n Q _ u
  have hfs : faceSum (swapFlip α) = faceSum0 α := funext fun w => faceSum_swapFlip w hrow
  have h := faceId_face_limUnder_sort (swapFlip α) hS hrow' (flipMom (photonSign α) pp) M n
    (swapQ Q) (lqBdd_swapQ hQ) (loopDegLe_swapQ hd) (fun hp => loopDegLe_swapQ (hd1 hp))
    (by rcases hn with h | ⟨h, h'⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, quart_swapQ h'⟩) hρ₀ hρ₁ hc₁
    (fun w hw hw1 hU hγw => by
      rw [symanzikV_swapFlip]
      exact hV w hw hw1 (by rwa [symanzikU_swapFlip] at hU) hγw)
    (fun u hu => by simpa only [e1] using hint u hu)
  simp only [e1, hfs] at h
  exact h

end QED.GradedProof.RPi4

end
