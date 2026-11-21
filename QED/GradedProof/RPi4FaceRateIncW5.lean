/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceRateIncW4

/-!
# (R-Π₄) step L10, B-inc: the rate of the derivative terms of one piece

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10, the rate (B) of
the face-rate increment. The two new terms of the `σ`-derivative of a collapsed piece,
`pieceFd n` (`z_γ v paramAtV (n + 1) v`) and `pieceFw (n + 1)` (`B(z) z_γ paramAtV (n + 1) v`),
have the rate of `faceIdRayB_piece_rate`: the two faces from `faceIdRayD_face_rate_loop1/0` and
`faceIdRayW_face_rate_loop1/0`, the corner and the bulk from `faceIdRayD_corner_rate` and
`faceIdRayD_bulk_rate` (domination by the absolute bracket, which needs `V(0) ≥ 0`):

* `faceIdRayD_piece_rate_of`: the four sectors give the rate `C (1 + c₀⁻¹)^N u^{-1/2}`;
* **`faceIdRayD_piece_rate`**: the rate of `pieceFd n` and of `pieceFw (n + 1)` of a family.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet
  simplexPoint_mem_stdSimplex)

/-- **The rate of a family from its four sectors** (the assembly of `faceIdRayB_piece_rate`):
faces and bulk with constants `C (1 + (c₀/4)⁻¹)^j`, the corner with `C u^{-1}`. -/
theorem faceIdRayD_piece_rate_of {ι : Type*} {m : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ}
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (F : ι → ℝ → (Fin (m + 1) → ℝ) → ℂ) (c₀ : ι → ℝ) (hc₀ : ∀ s, 0 < c₀ s)
    (h₁ : ∃ C : ℝ, ∃ N : ℕ, ∃ L : ι → ℂ, ∀ s, ∀ u : ℝ, 0 < u →
      IntegrableOn (fun x => F s u (simplexPoint x)) (simplexSet m) →
      ‖u • (∫ x in simplexSet m, {w | faceSum α w ≤ 1 / 4}.indicator (F s u)
        (simplexPoint x)) - L s‖ ≤ C * (1 + (c₀ s / 4)⁻¹) ^ N * u ^ (-(1 / 2) : ℝ))
    (h₀ : ∃ C : ℝ, ∃ N : ℕ, ∃ L : ι → ℂ, ∀ s, ∀ u : ℝ, 0 < u →
      IntegrableOn (fun x => F s u (simplexPoint x)) (simplexSet m) →
      ‖u • (∫ x in simplexSet m, {w | faceSum0 α w ≤ 1 / 4}.indicator (F s u)
        (simplexPoint x)) - L s‖ ≤ C * (1 + (c₀ s / 4)⁻¹) ^ N * u ^ (-(1 / 2) : ℝ))
    (hcor : ∃ C : ℝ, ∀ s, ∀ u : ℝ, 1 ≤ u →
      ‖u • ∫ x in simplexSet m, (cornerSet α (1 / 4)).indicator (F s u) (simplexPoint x)‖ ≤
        C * u⁻¹)
    (hbul : ∃ C : ℝ, ∀ s, ∀ u : ℝ, 0 < u →
      ‖u • ∫ x in simplexSet m, (bulkSet α (1 / 4)).indicator (F s u) (simplexPoint x)‖ ≤
        C * (1 + (c₀ s / 4)⁻¹) ^ 3 * u ^ (-(1 / 2) : ℝ)) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ L : ι → ℂ, ∀ s, ∀ u : ℝ, 1 ≤ u →
      IntegrableOn (fun x => F s u (simplexPoint x)) (simplexSet m) →
      ‖u • (∫ x in simplexSet m, F s u (simplexPoint x)) - L s‖ ≤
        C * (1 + (c₀ s)⁻¹) ^ N * u ^ (-(1 / 2) : ℝ) := by
  obtain ⟨C₁, N₁, L₁, e₁⟩ := h₁
  obtain ⟨C₀, N₀, L₀, e₀⟩ := h₀
  obtain ⟨Cc, ec⟩ := hcor
  obtain ⟨Cb, eb⟩ := hbul
  set N := N₁ + N₀ + 3
  refine ⟨(|C₁| + |C₀| + |Cc| + |Cb|) * 4 ^ N, N, fun s => L₁ s + L₀ s, fun s u hu hI => ?_⟩
  have hu0 : 0 < u := one_pos.trans_le hu
  have hsplit := integral_sector_eq hrow (ρ₀ := 1 / 4) (by norm_num) hI
  have f1 := e₁ s u hu0 hI
  have f0 := e₀ s u hu0 hI
  have fc := ec s u hu
  have fb := eb s u hu0
  have hinv : u⁻¹ ≤ u ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hu (by norm_num)
  have fc' : ‖u • ∫ x in simplexSet m, (cornerSet α (1 / 4)).indicator (F s u)
      (simplexPoint x)‖ ≤ |Cc| * u ^ (-(1 / 2) : ℝ) :=
    fc.trans (mul_le_mul (le_abs_self _) hinv (by positivity) (abs_nonneg _))
  rw [hsplit, smul_add, smul_add, smul_add]
  set a := u • ∫ x in simplexSet m, {w | faceSum α w ≤ 1 / 4}.indicator (F s u) (simplexPoint x)
  set b := u • ∫ x in simplexSet m, {w | faceSum0 α w ≤ 1 / 4}.indicator (F s u)
    (simplexPoint x)
  set c := u • ∫ x in simplexSet m, (cornerSet α (1 / 4)).indicator (F s u) (simplexPoint x)
  set d := u • ∫ x in simplexSet m, (bulkSet α (1 / 4)).indicator (F s u) (simplexPoint x)
  have e : a + b + c + d - (L₁ s + L₀ s) = (a - L₁ s) + (b - L₀ s) + c + d := by ring
  rw [e]
  have hW := faceIdRayB_quarter_le (hc₀ s) (N := N)
  have w1 := hW N₁ (by omega)
  have w0 := hW N₀ (by omega)
  have wb := hW 3 (by omega)
  have hWN : 1 ≤ 4 ^ N * (1 + (c₀ s)⁻¹) ^ N := by
    have h1 : 1 ≤ 1 + (c₀ s)⁻¹ := by have := inv_pos.2 (hc₀ s); linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ h1)
  have hr : 0 ≤ u ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hu0.le _
  have hW1 : 0 ≤ 1 + (c₀ s / 4)⁻¹ := by have := hc₀ s; positivity
  set X := 4 ^ N * (1 + (c₀ s)⁻¹) ^ N
  have g1 : C₁ * (1 + (c₀ s / 4)⁻¹) ^ N₁ * u ^ (-(1 / 2) : ℝ) ≤ |C₁| * X * u ^ (-(1 / 2) : ℝ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self _) w1 (pow_nonneg hW1 _) (abs_nonneg _)) hr
  have g0 : C₀ * (1 + (c₀ s / 4)⁻¹) ^ N₀ * u ^ (-(1 / 2) : ℝ) ≤ |C₀| * X * u ^ (-(1 / 2) : ℝ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self _) w0 (pow_nonneg hW1 _) (abs_nonneg _)) hr
  have gb : Cb * (1 + (c₀ s / 4)⁻¹) ^ 3 * u ^ (-(1 / 2) : ℝ) ≤ |Cb| * X * u ^ (-(1 / 2) : ℝ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self _) wb (pow_nonneg hW1 _) (abs_nonneg _)) hr
  have gc : |Cc| * u ^ (-(1 / 2) : ℝ) ≤ |Cc| * X * u ^ (-(1 / 2) : ℝ) :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (abs_nonneg _) hWN) hr
  calc ‖(a - L₁ s) + (b - L₀ s) + c + d‖ ≤ ‖a - L₁ s‖ + ‖b - L₀ s‖ + ‖c‖ + ‖d‖ :=
        norm_add₄_le
    _ ≤ C₁ * (1 + (c₀ s / 4)⁻¹) ^ N₁ * u ^ (-(1 / 2) : ℝ) +
          C₀ * (1 + (c₀ s / 4)⁻¹) ^ N₀ * u ^ (-(1 / 2) : ℝ) + |Cc| * u ^ (-(1 / 2) : ℝ) +
          Cb * (1 + (c₀ s / 4)⁻¹) ^ 3 * u ^ (-(1 / 2) : ℝ) := by gcongr
    _ ≤ |C₁| * X * u ^ (-(1 / 2) : ℝ) + |C₀| * X * u ^ (-(1 / 2) : ℝ) +
          |Cc| * X * u ^ (-(1 / 2) : ℝ) + |Cb| * X * u ^ (-(1 / 2) : ℝ) := by linarith
    _ = _ := by simp only [X]; ring

/-- **The rate of the two derivative terms of one collapsed piece**, with the lower bound of
`V₀` tracked: `pieceFd n` and `pieceFw (n + 1)` have the rate of `faceIdRayB_piece_rate`,
given `V(0) ≥ 0` (the second Symanzik function at masses `0`) on the simplex. -/
theorem faceIdRayD_piece_rate {ι : Type*} {m n : ℕ} (hnm : n - 3 < m)
    (α : Fin (m + 1) → Fin 2 → ℝ)
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
    {KP KM : ℝ} (hk : ∀ s, ‖k s‖ ≤ KP) (hM : ∀ s l, |M s l| ≤ KM) (c₀ : ι → ℝ)
    (hc₀ : ∀ s, 0 < c₀ s)
    (hV : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 → symanzikU α w ≠ 0 →
      c₀ s * ferSum α w ≤ symanzikV α (fun i => cs i • k s) (M s) w)
    (hB0 : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 → symanzikU α w ≠ 0 →
      0 ≤ symanzikV α (fun i => cs i • k s) 0 w) :
    (∃ C : ℝ, ∃ N : ℕ, ∃ L : ι → ℂ, ∀ s, ∀ u : ℝ, 1 ≤ u →
      IntegrableOn (fun x => pieceFd n (Q s) α (fun i => cs i • k s) (M s) γ₀ u
        (simplexPoint x)) (simplexSet m) →
      ‖u • (∫ x in simplexSet m,
          pieceFd n (Q s) α (fun i => cs i • k s) (M s) γ₀ u (simplexPoint x)) - L s‖ ≤
        C * (1 + (c₀ s)⁻¹) ^ N * u ^ (-(1 / 2) : ℝ)) ∧
    (∃ C : ℝ, ∃ N : ℕ, ∃ L : ι → ℂ, ∀ s, ∀ u : ℝ, 1 ≤ u →
      IntegrableOn (fun x => pieceFw (n + 1) (Q s) α (fun i => cs i • k s) (M s) γ₀ u
        (simplexPoint x)) (simplexSet m) →
      ‖u • (∫ x in simplexSet m,
          pieceFw (n + 1) (Q s) α (fun i => cs i • k s) (M s) γ₀ u (simplexPoint x)) - L s‖ ≤
        C * (1 + (c₀ s)⁻¹) ^ N * u ^ (-(1 / 2) : ℝ)) := by
  have hγ : α γ₀ = ![1, -1] := (huniq γ₀).mpr rfl
  set ρ₀ : ℝ := 1 / 4 with hρ₀
  set c₁ : ι → ℝ := fun s => c₀ s / 4 with hc₁
  have hc₁0 : ∀ s, 0 < c₁ s := fun s => by have := hc₀ s; simp only [hc₁]; positivity
  set pp : ι → Fin (m + 1) → Fin 4 → ℝ := fun s i => cs i • k s with hpp
  set KP' : ℝ := (∑ l, |cs l|) * KP
  have hP : ∀ s l, ‖pp s l‖ ≤ KP' := fun s l => by
    simp only [hpp, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (Finset.single_le_sum (f := fun l => |cs l|) (fun l _ => abs_nonneg _)
      (Finset.mem_univ l)) (hk s) (norm_nonneg _) (Finset.sum_nonneg fun l _ => abs_nonneg _)
  have hkμ : ∀ s μ, |k s μ| ≤ KP := fun s μ => (norm_le_pi_norm (k s) μ).trans (hk s)
  have hVface : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w γ₀ ≤ ρ₀ → c₁ s ≤ symanzikV α (pp s) (M s) w := fun s w hw hw1 hU h => by
    have := hV s w hw hw1 hU
    rw [ferSum_eq_one_sub huniq hw1] at this
    have h' : w γ₀ ≤ 1 / 4 := h
    have : c₀ s * (3 / 4) ≤ c₀ s * (1 - w γ₀) :=
      mul_le_mul_of_nonneg_left (by linarith) (hc₀ s).le
    have := hc₀ s
    show c₀ s / 4 ≤ _
    linarith
  have hVbulk : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      w ∈ bulkSet α ρ₀ → c₁ s ≤ symanzikV α (pp s) (M s) w := fun s w hw hw1 hb => by
    have hU := symanzikU_ge_bulk hrow w (by norm_num) hw hw1 hb
    have := hV s w hw hw1 (by positivity)
    have : c₀ s * (1 / 4) ≤ c₀ s * ferSum α w :=
      mul_le_mul_of_nonneg_left hb.2.2.le (hc₀ s).le
    show c₀ s / 4 ≤ _
    linarith
  have hVcorner : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      w ∈ cornerSet α ρ₀ → symanzikU α w ≠ 0 → 0 ≤ symanzikV α (pp s) (M s) w :=
    fun s w hw hw1 _ hU => by
      have := hV s w hw hw1 hU
      have : 0 ≤ c₀ s * ferSum α w := mul_nonneg (hc₀ s).le (Finset.sum_nonneg fun l _ => hw l)
      linarith
  have hm0 : 0 < m := by rcases hn with rfl | ⟨rfl, -⟩ <;> omega
  have hn6 : 6 ≤ n := by rcases hn with rfl | ⟨rfl, -⟩ <;> norm_num
  have hnQ : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0) := by
    rcases hn with h | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, fun s => (h' s).1⟩
  have hnQ₁ : 7 ≤ n ∨ (n = 6 ∧ ∀ s, (Q₁ s).quart = 0) := by
    rcases hn with h | ⟨h, h'⟩
    · exact Or.inl h.ge
    · exact Or.inr ⟨h, fun s => (h' s).2.1⟩
  have hnQ₀ : 7 ≤ n ∨ (n = 6 ∧ ∀ s, (Q₀ s).quart = 0) := by
    rcases hn with h | ⟨h, h'⟩
    · exact Or.inl h.ge
    · exact Or.inr ⟨h, fun s => (h' s).2.2⟩
  have hF : ∀ (P : ι → LoopQuartic), (∀ s, (P s).eval = (Q s).eval) → ∀ s,
      pieceFd n (P s) α (pp s) (M s) γ₀ = pieceFd n (Q s) α (pp s) (M s) γ₀ ∧
        pieceFw (n + 1) (P s) α (pp s) (M s) γ₀ = pieceFw (n + 1) (Q s) α (pp s) (M s) γ₀ :=
    fun P hP s => ⟨by funext u z; simp only [pieceFd, paramAtV_congr (hP s)],
      by funext u z; simp only [pieceFw, pieceF, paramAtV_congr (hP s)]⟩
  have hBs : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → 0 ≤ symanzikV α (pp s) 0 w := hB0
  -- the two faces of each term
  obtain ⟨C₁, N₁, L₁, f₁⟩ := faceIdRayD_face_rate_loop1 α γ₀ hγ hrow hA1 hR1 pp M n Q₁ hQ₁ hd1
    hd11 hnQ₁ (by norm_num) (by norm_num) c₁ hc₁0 hP hM hVface
  obtain ⟨C₀, N₀, L₀, f₀⟩ := faceIdRayD_face_rate_loop0 α γ₀ hγ hrow hA0 hR0 pp M n Q₀ hQ₀ hd0
    hd01 hnQ₀ (by norm_num) (by norm_num) c₁ hc₁0 hP hM hVface
  obtain ⟨C₁', N₁', L₁', f₁'⟩ := faceIdRayW_face_rate_loop1 α γ₀ hγ hrow hA1 hR1 pp M (n + 1) Q₁
    hQ₁ hd1 hd11 (Or.inl (by omega)) (by norm_num) (by norm_num) c₁ hc₁0 hP hM hVface
  obtain ⟨C₀', N₀', L₀', f₀'⟩ := faceIdRayW_face_rate_loop0 α γ₀ hγ hrow hA0 hR0 pp M (n + 1) Q₀
    hQ₀ hd0 hd01 (Or.inl (by omega)) (by norm_num) (by norm_num) c₁ hc₁0 hP hM hVface
  simp only [(hF Q₁ he₁ _).1, (hF Q₁ he₁ _).2] at f₁ f₁'
  simp only [(hF Q₀ he₀ _).1, (hF Q₀ he₀ _).2] at f₀ f₀'
  -- corner and bulk of each term
  have hK0 : (0 : ℝ) ≤ ((n - 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  obtain ⟨Cc, fc⟩ := faceIdRayD_corner_rate hnm α γ₀ huniq hrow cs k M Q hQ hnQ (by norm_num)
    (by norm_num) hkμ hVcorner (fun s u => pieceFd n (Q s) α (pp s) (M s) γ₀ u) hK0
    (fun s u w hw hw1 hu => faceIdRayD_norm_pieceFd_le hn6 (by linarith) hw (hBs s w hw hw1))
  obtain ⟨Cc', fc'⟩ := faceIdRayD_corner_rate hnm α γ₀ huniq hrow cs k M Q hQ hnQ (by norm_num)
    (by norm_num) hkμ hVcorner (fun s u => pieceFw (n + 1) (Q s) α (pp s) (M s) γ₀ u) hK0
    (fun s u w hw hw1 hu => faceIdRayD_norm_pieceFw_le hn6 (by linarith) hw (hBs s w hw hw1))
  obtain ⟨Cb, fb⟩ := faceIdRayD_bulk_rate hm0 α γ₀ hrow pp M n Q hQ hnQ (by norm_num) hP c₁ hc₁0
    hVbulk (fun s u => pieceFd n (Q s) α (pp s) (M s) γ₀ u) hK0
    (fun s u w hw hw1 hu => faceIdRayD_norm_pieceFd_le hn6 hu.le hw (hBs s w hw hw1))
  obtain ⟨Cb', fb'⟩ := faceIdRayD_bulk_rate hm0 α γ₀ hrow pp M n Q hQ hnQ (by norm_num) hP c₁
    hc₁0 hVbulk (fun s u => pieceFw (n + 1) (Q s) α (pp s) (M s) γ₀ u) hK0
    (fun s u w hw hw1 hu => faceIdRayD_norm_pieceFw_le hn6 hu.le hw (hBs s w hw hw1))
  exact ⟨faceIdRayD_piece_rate_of hrow (fun s u => pieceFd n (Q s) α (pp s) (M s) γ₀ u) c₀ hc₀
      ⟨C₁, N₁, L₁, f₁⟩ ⟨C₀, N₀, L₀, f₀⟩ ⟨Cc, fc⟩ ⟨Cb, fb⟩,
    faceIdRayD_piece_rate_of hrow (fun s u => pieceFw (n + 1) (Q s) α (pp s) (M s) γ₀ u) c₀ hc₀
      ⟨C₁', N₁', L₁', f₁'⟩ ⟨C₀', N₀', L₀', f₀'⟩ ⟨Cc', fc'⟩ ⟨Cb', fb'⟩⟩

end QED.GradedProof.RPi4

end
