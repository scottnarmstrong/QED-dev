/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceLoop1
public import QED.GradedProof.RPi4LoopSwap

/-!
# (R-Π₄) steps L6d1–L6d2: the loop-`0` face of any collapsed piece

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), steps L6d1–L6d2. The face
of loop `0` of a collapsed piece (the vertex face `H₁` of `VB`, and the vanishing faces
`S₁ ∪ γ` of `VA`, `VC`) is the part of the simplex where the weight of the lines with row
`(1, 0)` or `(1, -1)` is at most `ρ₀`. Exchanging the loops (`swapRows`, `swapQ`) and reversing
the photon line (`flipRows`, `flipMom`) turns it into the loop-`1` face of another piece, so
`face_rate_loop1` applies:

* `photonSign`, `swapFlip` (rows `(1, 0) ↔ (0, 1)`, `(1, -1)` fixed), `swapFlip_row_*`;
* `pieceF_swapFlip`, `symanzikU_swapFlip`, `symanzikV_swapFlip`, `faceSum0`,
  `faceSum_swapFlip`, `lqBdd_swapQ`;
* **`face_rate_loop0`**: the loop-`0` face rate `u^{-1/2}`, uniformly over the family.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint)

variable {m : ℕ}

/-- The sign `-1` on the lines with row `(1, -1)` (the photon), `1` elsewhere. -/
noncomputable def photonSign (α : Fin (m + 1) → Fin 2 → ℝ) : Fin (m + 1) → ℝ :=
  fun l => if α l = ![1, -1] then -1 else 1

theorem photonSign_sq (α : Fin (m + 1) → Fin 2 → ℝ) (l : Fin (m + 1)) :
    photonSign α l * photonSign α l = 1 := by
  unfold photonSign; split_ifs <;> norm_num

/-- The rows with the loops exchanged and the photon reversed. -/
noncomputable def swapFlip (α : Fin (m + 1) → Fin 2 → ℝ) : Fin (m + 1) → Fin 2 → ℝ :=
  flipRows (photonSign α) (swapRows α)

theorem row10_ne_row1m1 : (![1, 0] : Fin 2 → ℝ) ≠ ![1, -1] := fun h => by
  have := congrFun h 1
  norm_num at this

theorem row01_ne_row1m1 : (![0, 1] : Fin 2 → ℝ) ≠ ![1, -1] := fun h => by
  have := congrFun h 0
  norm_num at this

variable {α : Fin (m + 1) → Fin 2 → ℝ} {l : Fin (m + 1)}

theorem swapFlip_row_10 (h : α l = ![1, 0]) : swapFlip α l = ![0, 1] := by
  have hs : photonSign α l = 1 := by simp [photonSign, h]
  funext s
  fin_cases s <;> simp [swapFlip, flipRows, swapRows, hs, h, lsw]

theorem swapFlip_row_01 (h : α l = ![0, 1]) : swapFlip α l = ![1, 0] := by
  have hs : photonSign α l = 1 := by simp [photonSign, h]
  funext s
  fin_cases s <;> simp [swapFlip, flipRows, swapRows, hs, h, lsw]

theorem swapFlip_row_1m1 (h : α l = ![1, -1]) : swapFlip α l = ![1, -1] := by
  have hs : photonSign α l = -1 := by simp [photonSign, h]
  funext s
  fin_cases s <;> simp [swapFlip, flipRows, swapRows, hs, h, lsw]

variable (α) (pp : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (z : Fin (m + 1) → ℝ)

theorem symanzikU_swapFlip : symanzikU (swapFlip α) z = symanzikU α z := by
  rw [swapFlip, symanzikU, symanzikMatrix_flip _ _ (photonSign_sq α), ← symanzikU,
    symanzikU_swap]

theorem symanzikV_swapFlip :
    symanzikV (swapFlip α) (flipMom (photonSign α) pp) M z = symanzikV α pp M z := by
  rw [swapFlip, symanzikV_flip _ _ _ (photonSign_sq α), symanzikV_swap]

theorem pieceF_swapFlip (n : ℕ) (Q : LoopQuartic) (γ : Fin (m + 1)) (u : ℝ) :
    pieceF n (swapQ Q) (swapFlip α) (flipMom (photonSign α) pp) M γ u z =
      pieceF n Q α pp M γ u z := by
  rw [pieceF, pieceF, symanzikV_swapFlip, swapFlip, paramAtV_flip (hε := photonSign_sq α),
    paramAtV_swap]

/-- **The face weight of loop `0`**: the weight of the lines whose row is not `(0, 1)`. -/
noncomputable def faceSum0 (α : Fin (m + 1) → Fin 2 → ℝ) (z : Fin (m + 1) → ℝ) : ℝ :=
  ∑ l ∈ Finset.univ.filter (fun l => α l ≠ ![0, 1]), z l

variable {α}

theorem filter_swapFlip (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1]) :
    Finset.univ.filter (fun l => swapFlip α l ≠ ![1, 0]) =
      Finset.univ.filter (fun l => α l ≠ ![0, 1]) := by
  refine Finset.filter_congr fun l _ => ?_
  rcases hrow l with h | h | h
  · rw [swapFlip_row_10 h, h]
    exact ⟨fun _ => fun h' => row01_ne (h'.symm), fun _ => row01_ne⟩
  · rw [swapFlip_row_01 h, h]
    simp
  · rw [swapFlip_row_1m1 h, h]
    exact ⟨fun _ => fun h' => row01_ne_row1m1 h'.symm, fun _ => row1m1_ne⟩

theorem faceSum_swapFlip (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1]) :
    faceSum (swapFlip α) z = faceSum0 α z := by
  rw [faceSum, faceSum0, filter_swapFlip hrow]

theorem lqBdd_swapQ {ι : Type*} {Q : ι → LoopQuartic} {B : ℝ} (h : LQBdd Q B) :
    LQBdd (fun s => swapQ (Q s)) B :=
  ⟨fun i => h.const i, fun i _ => h.lin i _, fun i _ _ => h.quad i _ _,
    fun i _ _ _ => h.cub i _ _ _, fun i _ _ _ _ => h.quart i _ _ _ _⟩

theorem quart_swapQ {Q : LoopQuartic} (h : Q.quart = 0) : (swapQ Q).quart = 0 := by
  funext a b c d
  simp [swapQ, h]

theorem norm_flipMom_le {K : ℝ} (hP : ∀ l, ‖pp l‖ ≤ K) (l : Fin (m + 1)) :
    ‖flipMom (photonSign α) pp l‖ ≤ K := by
  have e : flipMom (photonSign α) pp l = photonSign α l • pp l := rfl
  have hs : ‖photonSign α l‖ = 1 := by unfold photonSign; split_ifs <;> simp
  rw [e, norm_smul, hs, one_mul]
  exact hP l

/-- **The loop-`0` face of a family of collapsed pieces, with rate `u^{-1/2}` uniform over the
family**: the mirror of `face_rate_loop1`, cut by `faceSum0`. -/
theorem face_rate_loop0 {ι : Type*} (α : Fin (m + 1) → Fin 2 → ℝ) (γ₀ : Fin (m + 1))
    (hγ : α γ₀ = ![1, -1]) (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (hA : 2 ≤ (Finset.univ.filter fun l => α l ≠ ![0, 1]).card) (hR : ∃ l, α l = ![0, 1])
    (pp : ι → Fin (m + 1) → Fin 4 → ℝ) (M : ι → Fin (m + 1) → ℝ) (n : ℕ)
    (Q : ι → LoopQuartic) {BQ : ℝ} (hQ : LQBdd Q BQ) (hd : ∀ s, LoopDegLe 0 3 (Q s))
    (hd1 : (Finset.univ.filter fun l => α l ≠ ![0, 1]).card = 2 → ∀ s, LoopDegLe 0 1 (Q s))
    (hn : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0))
    {ρ₀ c₁ KP KM : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (hc₁ : 0 < c₁)
    (hP : ∀ s l, ‖pp s l‖ ≤ KP) (hM : ∀ s l, |M s l| ≤ KM)
    (hV : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w γ₀ ≤ ρ₀ → c₁ ≤ symanzikV α (pp s) (M s) w) :
    ∃ C : ℝ, ∃ L : ι → ℂ, ∀ s, ∀ u : ℝ, 0 < u →
      IntegrableOn (fun x => pieceF n (Q s) α (pp s) (M s) γ₀ u (simplexPoint x))
        (simplexSet m) →
      ‖u • (∫ x in simplexSet m,
          {w | faceSum0 α w ≤ ρ₀}.indicator (pieceF n (Q s) α (pp s) (M s) γ₀ u)
            (simplexPoint x)) - L s‖ ≤ C * u ^ (-(1 / 2) : ℝ) := by
  have hrow' : ∀ l, swapFlip α l = ![1, 0] ∨ swapFlip α l = ![0, 1] ∨
      swapFlip α l = ![1, -1] := fun l => by
    rcases hrow l with h | h | h
    · exact Or.inr (Or.inl (swapFlip_row_10 h))
    · exact Or.inl (swapFlip_row_01 h)
    · exact Or.inr (Or.inr (swapFlip_row_1m1 h))
  obtain ⟨l, hl⟩ := hR
  obtain ⟨C, L, hC⟩ := face_rate_loop1 (swapFlip α) γ₀ (swapFlip_row_1m1 hγ) hrow'
    (by rw [filter_swapFlip hrow]; exact hA) ⟨l, swapFlip_row_01 hl⟩
    (fun s => flipMom (photonSign α) (pp s)) M n (fun s => swapQ (Q s)) (lqBdd_swapQ hQ)
    (fun s => loopDegLe_swapQ (hd s))
    (fun h s => loopDegLe_swapQ (hd1 (by rw [← filter_swapFlip hrow]; exact h) s))
    (by rcases hn with h | ⟨h, h'⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, fun s => quart_swapQ (h' s)⟩)
    hρ₀ hρ₁ hc₁ (fun s => norm_flipMom_le (pp s) (hP s)) hM
    (fun s w hw hw1 hU hγw => by
      rw [symanzikV_swapFlip]
      exact hV s w hw hw1 (by rwa [symanzikU_swapFlip] at hU) hγw)
  refine ⟨C, L, fun s u hu hf => ?_⟩
  have e : ∀ w, pieceF n (swapQ (Q s)) (swapFlip α) (flipMom (photonSign α) (pp s)) (M s) γ₀ u w =
      pieceF n (Q s) α (pp s) (M s) γ₀ u w := fun w => pieceF_swapFlip α (pp s) (M s) w n _ γ₀ u
  have e' := funext e
  have hfs : faceSum (swapFlip α) = faceSum0 α := funext fun w => faceSum_swapFlip w hrow
  have h := hC s u hu (by simp only [e]; exact hf)
  rw [e', hfs] at h
  exact h

end QED.GradedProof.RPi4

end
