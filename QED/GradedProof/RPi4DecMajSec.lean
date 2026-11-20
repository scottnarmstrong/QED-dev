/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecMajFace

/-!
# (R-Π₄) step L9: the photon-weighted majorant of a piece is `O(1/u)` for every `u > 0`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (second
differences in `s`, the class inputs `QED.GradedProof.RPi4.DecVTwo`). The absolute-term
majorant `QED.GradedProof.RPi4.decMajF` of a collapsed piece satisfies `u ∫ decMajF ≤ C` for
every photon mass `u > 0`, uniformly over a family (`dec_maj_rate`, the majorant analogue of
`QED.GradedProof.RPi4.piece_rate`; no rate and no limit are needed):

* `dec_face_maj_loop1`: the loop-`1` face (lines sorted internally, as in `face_rate_loop1`,
  from `FaceSort.dec_face_maj`);
* `dec_three_coeff_eq`, `decMajF_swapFlip`, `dec_face_maj_loop0`: the loop-`0` face by
  exchanging the loops and reversing the photon line;
* `dec_corner_maj`: the loop-UV corner, from `dec_majF_le_corner` and the integrability of
  `ferSum^{-(n-2)}` (`n - 2 < m`);
* `dec_bulk_maj`: the bulk, from `dec_majF_le_bulk` and `u z_γ (c₁ + z_γ u)^{-2} ≤ 1/c₁`;
* `dec_integral_sector_eq`: the sector partition of a real integral.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet
  simplexPoint_mem_stdSimplex)

/-! ### The loop-`1` face -/

/-- **The loop-`1` face of the majorant**: `u ∫_{faceSum ≤ ρ₀} decMajF ≤ C` for all `u > 0`,
uniformly over the family (hypotheses of `face_rate_loop1`). -/
theorem dec_face_maj_loop1 {ι : Type*} {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (γ₀ : Fin (m + 1))
    (hγ : α γ₀ = ![1, -1]) (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (hA : 2 ≤ (Finset.univ.filter fun l => α l ≠ ![1, 0]).card) (hR : ∃ l, α l = ![1, 0])
    (pp : ι → Fin (m + 1) → Fin 4 → ℝ) (M : ι → Fin (m + 1) → ℝ) (n : ℕ)
    (Q : ι → LoopQuartic) {BQ : ℝ} (hQ : LQBdd Q BQ) (hd : ∀ s, LoopDegLe 1 3 (Q s))
    (hd1 : (Finset.univ.filter fun l => α l ≠ ![1, 0]).card = 2 → ∀ s, LoopDegLe 1 1 (Q s))
    (hn : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0))
    {ρ₀ c₁ KP KM : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (hc₁ : 0 < c₁)
    (hP : ∀ s l, ‖pp s l‖ ≤ KP) (hM : ∀ s l, |M s l| ≤ KM)
    (hV : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w γ₀ ≤ ρ₀ → c₁ ≤ symanzikV α (pp s) (M s) w) :
    ∃ C : ℝ, ∀ s, ∀ u : ℝ, 0 < u →
      IntegrableOn (fun x => decMajF n (Q s) α (pp s) (M s) γ₀ u (simplexPoint x))
        (simplexSet m) →
      u * ∫ x in simplexSet m,
          {w | faceSum α w ≤ ρ₀}.indicator (decMajF n (Q s) α (pp s) (M s) γ₀ u)
            (simplexPoint x) ≤ C := by
  classical
  have hn5 : 5 ≤ n := by rcases hn with rfl | ⟨rfl, -⟩ <;> norm_num
  set A := Finset.univ.filter fun l => α l ≠ ![1, 0] with hAdef
  have hmemA : ∀ l, l ∈ A ↔ α l ≠ ![1, 0] := fun l => by simp [hAdef]
  obtain ⟨p, hp⟩ : ∃ p, A.card = p + 1 + 1 := ⟨A.card - 2, by omega⟩
  obtain ⟨q, hq⟩ : ∃ q, Aᶜ.card = q + 1 := by
    obtain ⟨l, hl⟩ := hR
    have : 0 < Aᶜ.card := Finset.card_pos.mpr ⟨l, by simp [hAdef, hl]⟩
    exact ⟨Aᶜ.card - 1, by omega⟩
  have hm : m = p + 1 + 1 + q := by
    have := Finset.card_add_card_compl A
    simp only [Fintype.card_fin] at this
    omega
  subst hm
  have hγA : γ₀ ∈ A := (hmemA γ₀).mpr (by rw [hγ]; exact row1m1_ne)
  -- the sorting permutation
  have cA : Fintype.card {l // l ∈ A} = p + 1 + 1 := by simp [hp]
  have cR : Fintype.card {l // ¬l ∈ A} = q + 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]
    have := Finset.card_add_card_compl A
    simp only [Fintype.card_fin] at this
    omega
  set e₀ : Equiv.Perm (Fin (p + 1 + 1 + q + 1)) :=
    (finSumFinEquiv (m := p + 1 + 1) (n := q + 1)).symm.trans
      (((Fintype.equivFinOfCardEq cA).symm.sumCongr (Fintype.equivFinOfCardEq cR).symm).trans
        (Equiv.sumCompl (· ∈ A))) with he₀
  have he₀F : ∀ i : Fin (p + 1 + 1), e₀ (Fin.castAdd (q + 1) i) ∈ A := fun i => by
    simp only [he₀, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact Subtype.prop _
  have he₀R : ∀ j : Fin (q + 1), e₀ (Fin.natAdd (p + 1 + 1) j) ∉ A := fun j => by
    simp only [he₀, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.sumCompl_apply_inr]
    exact ((Fintype.equivFinOfCardEq cR).symm j).2
  set l₁ := e₀ (Fin.castAdd (q + 1) (Fin.last (p + 1)))
  set e : Equiv.Perm (Fin (p + 1 + 1 + q + 1)) := e₀.trans (Equiv.swap l₁ γ₀) with he
  have hswA : ∀ x ∈ A, Equiv.swap l₁ γ₀ x ∈ A := fun x hx => by
    rw [Equiv.swap_apply_def]
    split_ifs
    · exact hγA
    · exact he₀F _
    · exact hx
  have hS : FaceSort p q α e := by
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have hx := (hmemA _).mp (hswA _ (he₀F i))
      rcases hrow (e (Fin.castAdd (q + 1) i)) with h1 | h1 | h1
      · exact absurd h1 hx
      · exact Or.inl h1
      · exact Or.inr h1
    · have hx := he₀R j
      have h1 : e₀ (Fin.natAdd (p + 1 + 1) j) ≠ l₁ := fun h => hx (h ▸ he₀F _)
      have h2 : e₀ (Fin.natAdd (p + 1 + 1) j) ≠ γ₀ := fun h => hx (h ▸ hγA)
      have : e (Fin.natAdd (p + 1 + 1) j) = e₀ (Fin.natAdd (p + 1 + 1) j) := by
        simp only [he, Equiv.trans_apply]
        exact Equiv.swap_apply_of_ne_of_ne h1 h2
      rw [this]
      by_contra hne
      exact hx ((hmemA _).mpr hne)
  have hgam : FaceSort.gam e = γ₀ := by
    simp only [FaceSort.gam, he, Equiv.trans_apply]
    exact Equiv.swap_apply_left _ _
  -- uniform bounds
  have hα : ∀ l s, |α l s| ≤ 1 := fun l s => by
    rcases hrow l with h1 | h1 | h1 <;> rw [h1] <;> fin_cases s <;> simp
  have hK := fun s => hS.kF_shape_le (M := M s) hα (hP s)
  have hKM := fun s => hS.kM_shape_le (pp := pp s) (hP s) (hM s)
  have hV' : ∀ s (w : Fin (p + 1 + 1 + q + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w (FaceSort.gam e) ≤ ρ₀ → c₁ ≤ symanzikV α (pp s) (M s) w := by
    rw [hgam]; exact hV
  -- the bracket
  have fin : ∀ {r : ℕ} (B : ι → FaceBr r) (k : Fin r → ℕ), (∀ s, (B s).k = k) →
      (∀ j, 2 ≤ k j) → (∀ s, (B s).Meas) →
      (∀ j, UnifLip ρ₀ fun (i : ι × FaceIdx (p + 1) q) ρ =>
        (hS.shape (pp i.1) (M i.1)).coefJ (B i.1) j ρ (FaceShape.Wi i.2) (FaceShape.Vi i.2)) →
      (∀ s, (B s).Rep n (p + 1) (Q s) (fun i => α (e i)) (fun i => pp s (e i))) →
      ∃ C : ℝ, ∀ s, ∀ u : ℝ, 0 < u →
        IntegrableOn (fun x => decMajF n (Q s) α (pp s) (M s) γ₀ u (simplexPoint x))
          (simplexSet (p + 1 + 1 + q)) →
        u * ∫ x in simplexSet (p + 1 + 1 + q),
            {w | faceSum α w ≤ ρ₀}.indicator (decMajF n (Q s) α (pp s) (M s) γ₀ u)
              (simplexPoint x) ≤ C := by
    intro r B k hkc hk hB hD hRep
    obtain ⟨C, hC⟩ := hS.dec_face_maj pp M n hn5 Q B k hρ₀ hρ₁ hc₁ hK hKM hkc hk hB hD hRep hV'
    refine ⟨C, fun s u hu hf => ?_⟩
    rw [← hgam] at hf ⊢
    exact hC s u hu hf
  set S : ι → FaceShape (p + 1) q := fun s => hS.shape (pp s) (M s)
  have hK' : ∀ s, (S s).kF ≤ 1 + 3 * (p + 1 + 1) + 4 * ((q + 1) + 2 * (p + 1 + 1)) * KP := hK
  rcases hn with rfl | ⟨rfl, hq0⟩
  · rcases Nat.eq_zero_or_pos p with rfl | hp1
    · exact fin (fun s => FaceBr.se 7 (Q s)) ![7 - 3, 7 - 4, 7 - 5] (fun _ => rfl)
        (fun j => by fin_cases j <;> simp)
        (fun _ => FaceBr.meas_se) (FaceShape.unifLip_coefJ_se S hK' hρ₁ 7 hQ)
        (fun s => FaceBr.rep_se (hd1 (by omega) s) le_rfl)
    · exact fin (fun s => FaceBr.vtx 7 (Q s)) ![7 - 3, 7 - 4, 7 - 5] (fun _ => rfl)
        (fun j => by fin_cases j <;> simp)
        (fun _ => FaceBr.meas_vtx) (FaceShape.unifLip_coefJ_vtx S hK' hρ₁ 7 hQ)
        (fun s => FaceBr.rep_vtx3 (hd s) (by omega))
  · rcases Nat.eq_zero_or_pos p with rfl | hp1
    · exact fin (fun s => FaceBr.se₂ 6 (Q s)) ![6 - 3, 6 - 4] (fun _ => rfl)
        (fun j => by fin_cases j <;> simp)
        (fun _ => FaceBr.meas_se₂) (FaceShape.unifLip_coefJ_se₂ S hK' hρ₁ 6 hQ)
        (fun s => FaceBr.rep_se₂ (hd1 (by omega) s) (hq0 s) le_rfl)
    · exact fin (fun s => FaceBr.vtx₂ 6 (Q s)) ![6 - 3, 6 - 4] (fun _ => rfl)
        (fun j => by fin_cases j <;> simp)
        (fun _ => FaceBr.meas_vtx₂) (FaceShape.unifLip_coefJ_vtx₂ S hK' hρ₁ 6 hQ)
        (fun s => FaceBr.rep_vtx₂3 (hd s) (hq0 s) (by omega))


/-! ### The loop-`0` face -/

/-- **Uniqueness of the three coefficients**: two three-term Laurent polynomials
`a w^{-(f+2)} + b w^{-(f+1)} + c w^{-f}` that agree at `w = 1, 2, 3` have the same
coefficients. -/
theorem dec_three_coeff_eq {f : ℕ} {a b c a' b' c' : ℂ}
    (h : ∀ w : ℝ, 0 < w → a * ((w : ℂ) ^ (f + 2))⁻¹ + b * ((w : ℂ) ^ (f + 1))⁻¹ +
      c * ((w : ℂ) ^ f)⁻¹ = a' * ((w : ℂ) ^ (f + 2))⁻¹ + b' * ((w : ℂ) ^ (f + 1))⁻¹ +
      c' * ((w : ℂ) ^ f)⁻¹) :
    a = a' ∧ b = b' ∧ c = c' := by
  have hy : ∀ l : ℝ, 0 < l → (a - a') + l * (b - b') + l ^ 2 * (c - c') = 0 := fun l hl => by
    have hl' : (l : ℂ) ≠ 0 := ofReal_ne_zero.mpr hl.ne'
    have e := h l hl
    have e2 : (l : ℂ) ^ (f + 2) * (a * ((l : ℂ) ^ (f + 2))⁻¹ + b * ((l : ℂ) ^ (f + 1))⁻¹ +
        c * ((l : ℂ) ^ f)⁻¹) = a + l * b + l ^ 2 * c := by
      field_simp
      ring
    have e3 : (l : ℂ) ^ (f + 2) * (a' * ((l : ℂ) ^ (f + 2))⁻¹ + b' * ((l : ℂ) ^ (f + 1))⁻¹ +
        c' * ((l : ℂ) ^ f)⁻¹) = a' + l * b' + l ^ 2 * c' := by
      field_simp
      ring
    rw [e] at e2
    linear_combination e3 - e2
  have y1 := hy 1 one_pos
  have y2 := hy 2 two_pos
  have y3 := hy 3 three_pos
  push_cast at y1 y2 y3
  refine ⟨?_, ?_, ?_⟩
  · linear_combination 3 * y1 - 3 * y2 + y3
  · linear_combination (-5 / 2) * y1 + 4 * y2 - (3 / 2) * y3
  · linear_combination (1 / 2) * y1 - y2 + (1 / 2) * y3

variable {m : ℕ}

/-- The majorant depends on the integrand only through its values. -/
theorem decMajP_eq_of_paramAtV {n : ℕ} (hn : 5 ≤ n) {Q Q' : LoopQuartic}
    {α α' : Fin (m + 1) → Fin 2 → ℝ} {p p' : Fin (m + 1) → Fin 4 → ℝ} {z : Fin (m + 1) → ℝ}
    (h : ∀ w : ℝ, paramAtV n Q α p z w = paramAtV n Q' α' p' z w) (v : ℝ) :
    decMajP n Q α p z v = decMajP n Q' α' p' z v := by
  obtain ⟨f, rfl⟩ : ∃ f, n = f + 5 := ⟨n - 5, by omega⟩
  have e3 : f + 5 - 3 = f + 2 := by omega
  have e4 : f + 5 - 4 = f + 1 := by omega
  have e5 : f + 5 - 5 = f := by omega
  obtain ⟨h1, h2, h3⟩ := dec_three_coeff_eq (f := f) (a := cOneAt (f + 5) Q α p z)
    (b := cTwoAt (f + 5) Q α p z) (c := cThreeAt (f + 5) Q α z)
    (a' := cOneAt (f + 5) Q' α' p' z) (b' := cTwoAt (f + 5) Q' α' p' z)
    (c' := cThreeAt (f + 5) Q' α' z) fun w _ => by
      have := h w
      rwa [paramAtV_eq, paramAtV_eq, e3, e4, e5] at this
  simp only [decMajP, h1, h2, h3]

theorem decMajF_swapFlip (α : Fin (m + 1) → Fin 2 → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ)
    (M : Fin (m + 1) → ℝ) (z : Fin (m + 1) → ℝ) {n : ℕ} (hn : 5 ≤ n) (Q : LoopQuartic)
    (γ : Fin (m + 1)) (u : ℝ) :
    decMajF n (swapQ Q) (swapFlip α) (flipMom (photonSign α) pp) M γ u z =
      decMajF n Q α pp M γ u z := by
  rw [decMajF, decMajF, symanzikV_swapFlip]
  congr 1
  exact decMajP_eq_of_paramAtV hn (fun w => by
    rw [swapFlip, paramAtV_flip (hε := photonSign_sq α), paramAtV_swap]) _

/-- **The loop-`0` face of the majorant** (hypotheses of `face_rate_loop0`). -/
theorem dec_face_maj_loop0 {ι : Type*} (α : Fin (m + 1) → Fin 2 → ℝ) (γ₀ : Fin (m + 1))
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
    ∃ C : ℝ, ∀ s, ∀ u : ℝ, 0 < u →
      IntegrableOn (fun x => decMajF n (Q s) α (pp s) (M s) γ₀ u (simplexPoint x))
        (simplexSet m) →
      u * ∫ x in simplexSet m,
          {w | faceSum0 α w ≤ ρ₀}.indicator (decMajF n (Q s) α (pp s) (M s) γ₀ u)
            (simplexPoint x) ≤ C := by
  have hn5 : 5 ≤ n := by rcases hn with rfl | ⟨rfl, -⟩ <;> norm_num
  have hrow' : ∀ l, swapFlip α l = ![1, 0] ∨ swapFlip α l = ![0, 1] ∨
      swapFlip α l = ![1, -1] := fun l => by
    rcases hrow l with h | h | h
    · exact Or.inr (Or.inl (swapFlip_row_10 h))
    · exact Or.inl (swapFlip_row_01 h)
    · exact Or.inr (Or.inr (swapFlip_row_1m1 h))
  obtain ⟨l, hl⟩ := hR
  obtain ⟨C, hC⟩ := dec_face_maj_loop1 (swapFlip α) γ₀ (swapFlip_row_1m1 hγ) hrow'
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
  refine ⟨C, fun s u hu hf => ?_⟩
  have e' : decMajF n (swapQ (Q s)) (swapFlip α) (flipMom (photonSign α) (pp s)) (M s) γ₀ u =
      decMajF n (Q s) α (pp s) (M s) γ₀ u :=
    funext fun w => decMajF_swapFlip α (pp s) (M s) w hn5 (Q s) γ₀ u
  have hfs : faceSum (swapFlip α) = faceSum0 α := funext fun w => faceSum_swapFlip w hrow
  have h := hC s u hu (by rw [e']; exact hf)
  rw [e', hfs] at h
  exact h

/-! ### The corner and the bulk -/

/-- **The corner of the majorant**: `u ∫_{corner} decMajF ≤ C` for all `u > 0` (`n - 2 < m`,
`V₀ ≥ c₀ ferSum` where `U ≠ 0`). -/
theorem dec_corner_maj {ι : Type*} {n : ℕ} (hm : n - 2 < m) (α : Fin (m + 1) → Fin 2 → ℝ)
    (γ₀ : Fin (m + 1)) (huniq : ∀ l, α l = ![1, -1] ↔ l = γ₀)
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (cs : Fin (m + 1) → ℝ) (k : ι → Fin 4 → ℝ) (M : ι → Fin (m + 1) → ℝ)
    (Q : ι → LoopQuartic) {BQ : ℝ} (hQ : LQBdd Q BQ)
    (hn : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0))
    {ρ₀ KP c₀ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (hc₀ : 0 < c₀) (hk : ∀ s μ, |k s μ| ≤ KP)
    (hV : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → c₀ * ferSum α w ≤ symanzikV α (fun i => cs i • k s) (M s) w) :
    ∃ C : ℝ, ∀ s, ∀ u : ℝ, 0 < u →
      u * ∫ x in simplexSet m, (cornerSet α ρ₀).indicator
          (decMajF n (Q s) α (fun i => cs i • k s) (M s) γ₀ u) (simplexPoint x) ≤ C := by
  obtain ⟨E, hE, hEb⟩ := dec_majF_le_corner α γ₀ huniq hrow cs k M n Q hQ hn hρ₀ hρ₁ hc₀ hk
  have hm0 : 0 < m := by omega
  have hI := integrableOn_one_sub_simplexPoint_rpow hm0 γ₀ (q := ((n - 2 : ℕ) : ℝ))
    (Nat.cast_nonneg _) (by exact_mod_cast hm)
  refine ⟨∫ x in simplexSet m, E * (1 - simplexPoint x γ₀) ^ (-((n - 2 : ℕ) : ℝ)),
    fun s u hu => ?_⟩
  have hg : ∀ x ∈ simplexSet m, ‖u * (cornerSet α ρ₀).indicator
      (decMajF n (Q s) α (fun i => cs i • k s) (M s) γ₀ u) (simplexPoint x)‖ ≤
      E * (1 - simplexPoint x γ₀) ^ (-((n - 2 : ℕ) : ℝ)) := by
    intro x hx
    obtain ⟨hz, hz1⟩ := simplexPoint_mem_stdSimplex hx
    have hy : ferSum α (simplexPoint x) = 1 - simplexPoint x γ₀ := ferSum_eq_one_sub huniq hz1
    have hy0 : 0 ≤ 1 - simplexPoint x γ₀ := by
      rw [← hy]; exact Finset.sum_nonneg fun l _ => hz l
    have hR : 0 ≤ E * (1 - simplexPoint x γ₀) ^ (-((n - 2 : ℕ) : ℝ)) := by positivity
    by_cases hb : simplexPoint x ∈ cornerSet α ρ₀
    · rw [indicator_of_mem hb, norm_mul, Real.norm_of_nonneg hu.le]
      have hV' := hV s _ hz hz1
      by_cases hU : symanzikU α (simplexPoint x) = 0
      · rw [decMajF_eq_zero_of_U n (Q s) α _ _ hU, norm_zero, mul_zero]
        exact hR
      have h0 : 0 ≤ decMajF n (Q s) α (fun i => cs i • k s) (M s) γ₀ u (simplexPoint x) := by
        refine decMajF_nonneg n (Q s) α _ _ (hz γ₀) ?_
        have := hV' hU
        have : 0 ≤ c₀ * ferSum α (simplexPoint x) := mul_nonneg hc₀.le (by rw [hy]; exact hy0)
        have := mul_nonneg (hz γ₀) hu.le
        linarith
      rw [Real.norm_of_nonneg h0]
      refine (mul_le_mul_of_nonneg_left (hEb s _ hz hz1 hb hV' u hu) hu.le).trans
        (le_of_eq ?_)
      rw [hy, Real.rpow_neg hy0, Real.rpow_natCast]
      field_simp
    · rw [indicator_of_notMem hb, mul_zero, norm_zero]
      exact hR
  rw [← integral_const_mul]
  exact (Real.le_norm_self _).trans ((norm_integral_le_of_norm_le (hI.const_mul E)
    (ae_restrict_of_forall_mem (measurableSet_simplexSet m) hg)))

/-- **The bulk of the majorant**: `u ∫_{bulk} decMajF ≤ C` for all `u > 0` (`V₀ ≥ c₁` on the
bulk). -/
theorem dec_bulk_maj {ι : Type*} (α : Fin (m + 1) → Fin 2 → ℝ) (γ₀ : Fin (m + 1))
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (pp : ι → Fin (m + 1) → Fin 4 → ℝ) (M : ι → Fin (m + 1) → ℝ) (n : ℕ)
    (Q : ι → LoopQuartic) {BQ : ℝ} (hQ : LQBdd Q BQ)
    (hn : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0))
    {ρ₀ c₁ KP : ℝ} (hρ₀ : 0 < ρ₀) (hc₁ : 0 < c₁) (hP : ∀ s l, ‖pp s l‖ ≤ KP)
    (hV : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 → w ∈ bulkSet α ρ₀ →
      c₁ ≤ symanzikV α (pp s) (M s) w) :
    ∃ C : ℝ, ∀ s, ∀ u : ℝ, 0 < u →
      u * ∫ x in simplexSet m,
          (bulkSet α ρ₀).indicator (decMajF n (Q s) α (pp s) (M s) γ₀ u) (simplexPoint x) ≤
        C := by
  obtain ⟨D, hD, hDb⟩ := dec_majF_le_bulk α γ₀ hrow pp M n Q hQ hn hρ₀ hc₁ hP
  have hI : IntegrableOn (fun _ : Fin m → ℝ => D * c₁⁻¹) (simplexSet m) :=
    integrableOn_const (QED.Integration.Feynman.isCompact_simplexSet m).measure_lt_top.ne
  refine ⟨∫ _ in simplexSet m, D * c₁⁻¹, fun s u hu => ?_⟩
  have hg : ∀ x ∈ simplexSet m, ‖u * (bulkSet α ρ₀).indicator
      (decMajF n (Q s) α (pp s) (M s) γ₀ u) (simplexPoint x)‖ ≤ D * c₁⁻¹ := by
    intro x hx
    obtain ⟨hz, hz1⟩ := simplexPoint_mem_stdSimplex hx
    have hR : 0 ≤ D * c₁⁻¹ := by positivity
    by_cases hb : simplexPoint x ∈ bulkSet α ρ₀
    · rw [indicator_of_mem hb, norm_mul, Real.norm_of_nonneg hu.le]
      have hV' := hV s _ hz hz1 hb
      set t := simplexPoint x γ₀
      have ht := hz γ₀
      have htu : 0 ≤ t * u := mul_nonneg ht hu.le
      have h0 : 0 ≤ decMajF n (Q s) α (pp s) (M s) γ₀ u (simplexPoint x) :=
        decMajF_nonneg n (Q s) α _ _ ht (by linarith)
      rw [Real.norm_of_nonneg h0]
      refine (mul_le_mul_of_nonneg_left (hDb s _ hz hz1 hb hV' u hu.le) hu.le).trans ?_
      have hpos : 0 < c₁ + t * u := by linarith
      have key : t * u * ((c₁ + t * u) ^ 2)⁻¹ ≤ c₁⁻¹ := by
        rw [← div_eq_mul_inv, div_le_iff₀ (by positivity), inv_mul_eq_div,
          le_div_iff₀ hc₁]
        nlinarith
      calc u * (t * (D * ((c₁ + t * u) ^ 2)⁻¹)) = D * (t * u * ((c₁ + t * u) ^ 2)⁻¹) := by
            ring
        _ ≤ D * c₁⁻¹ := mul_le_mul_of_nonneg_left key hD
    · rw [indicator_of_notMem hb, mul_zero, norm_zero]
      exact hR
  rw [← integral_const_mul]
  exact (Real.le_norm_self _).trans ((norm_integral_le_of_norm_le hI
    (ae_restrict_of_forall_mem (measurableSet_simplexSet m) hg)))

/-! ### The four sectors -/

theorem dec_integrableOn_indicator_comp {f : (Fin (m + 1) → ℝ) → ℝ}
    {S : Set (Fin (m + 1) → ℝ)} (hS : MeasurableSet S)
    (hf : IntegrableOn (fun x => f (simplexPoint x)) (simplexSet m)) :
    IntegrableOn (fun x => S.indicator f (simplexPoint x)) (simplexSet m) := by
  have e : (fun x => S.indicator f (simplexPoint x)) =
      (simplexPoint ⁻¹' S).indicator (fun x => f (simplexPoint x)) := by
    funext x
    by_cases h : simplexPoint x ∈ S
    · rw [indicator_of_mem h, indicator_of_mem (show x ∈ simplexPoint ⁻¹' S from h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (show x ∉ simplexPoint ⁻¹' S from h)]
  rw [e]
  exact hf.indicator (hS.preimage continuous_simplexPoint'.measurable)

/-- **The sector partition of a real integral over the simplex** (`ρ₀ < 1/2`). -/
theorem dec_integral_sector_eq {α : Fin (m + 1) → Fin 2 → ℝ}
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1]) {ρ₀ : ℝ} (hρ : ρ₀ < 1 / 2)
    {f : (Fin (m + 1) → ℝ) → ℝ} (hf : IntegrableOn (fun x => f (simplexPoint x)) (simplexSet m)) :
    ∫ x in simplexSet m, f (simplexPoint x) =
      (∫ x in simplexSet m, {w | faceSum α w ≤ ρ₀}.indicator f (simplexPoint x)) +
      (∫ x in simplexSet m, {w | faceSum0 α w ≤ ρ₀}.indicator f (simplexPoint x)) +
      (∫ x in simplexSet m, (cornerSet α ρ₀).indicator f (simplexPoint x)) +
      ∫ x in simplexSet m, (bulkSet α ρ₀).indicator f (simplexPoint x) := by
  have h1 := dec_integrableOn_indicator_comp (S := {w | faceSum α w ≤ ρ₀})
    (measurableSet_le (measurable_faceSum α) measurable_const) hf
  have h2 := dec_integrableOn_indicator_comp (S := {w | faceSum0 α w ≤ ρ₀})
    (measurableSet_le (measurable_faceSum0 α) measurable_const) hf
  have h3 := dec_integrableOn_indicator_comp (S := cornerSet α ρ₀) (measurableSet_le
    (measurable_ferSum α) measurable_const) hf
  have h4 := dec_integrableOn_indicator_comp (measurableSet_bulkSet α ρ₀) hf
  set A := fun x => {w | faceSum α w ≤ ρ₀}.indicator f (simplexPoint x)
  set B := fun x => {w | faceSum0 α w ≤ ρ₀}.indicator f (simplexPoint x)
  set C := fun x => (cornerSet α ρ₀).indicator f (simplexPoint x)
  set D := fun x => (bulkSet α ρ₀).indicator f (simplexPoint x)
  have e3 : ∫ x in simplexSet m, (A x + B x + C x + D x) =
      (∫ x in simplexSet m, (A x + B x + C x)) + ∫ x in simplexSet m, D x :=
    integral_add ((h1.add h2).add h3) h4
  have e2 : ∫ x in simplexSet m, (A x + B x + C x) =
      (∫ x in simplexSet m, (A x + B x)) + ∫ x in simplexSet m, C x :=
    integral_add (h1.add h2) h3
  have e1 : ∫ x in simplexSet m, (A x + B x) =
      (∫ x in simplexSet m, A x) + ∫ x in simplexSet m, B x := integral_add h1 h2
  rw [← e1, ← e2, ← e3]
  refine setIntegral_congr_fun (measurableSet_simplexSet m) fun x hx => ?_
  obtain ⟨hz, hz1⟩ := simplexPoint_mem_stdSimplex hx
  exact sector_indicator_eq hrow hz hz1 f hρ

/-- **The majorant of one collapsed piece is `O(1/u)` for every `u > 0`, uniformly over a
family**: under the hypotheses of `piece_rate` (with `n - 2 < m` in place of `n - 3 < m`),
`u ∫ decMajF ≤ C` for all `u > 0` wherever `decMajF` is integrable. -/
theorem dec_maj_rate {ι : Type*} {n : ℕ} (hnm : n - 2 < m) (α : Fin (m + 1) → Fin 2 → ℝ)
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
      c₀ * ferSum α w ≤ symanzikV α (fun i => cs i • k s) (M s) w) :
    ∃ C : ℝ, ∀ s, ∀ u : ℝ, 0 < u →
      IntegrableOn (fun x => decMajF n (Q s) α (fun i => cs i • k s) (M s) γ₀ u (simplexPoint x))
        (simplexSet m) →
      u * ∫ x in simplexSet m,
          decMajF n (Q s) α (fun i => cs i • k s) (M s) γ₀ u (simplexPoint x) ≤ C := by
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
      ∀ s, decMajF n (P s) α (pp s) (M s) γ₀ = decMajF n (Q s) α (pp s) (M s) γ₀ :=
    fun P hP s => by
      funext u z
      exact decMajF_congr n (P s) α (pp s) z (hP s) (M s) γ₀ u
  obtain ⟨C₁, h₁⟩ := dec_face_maj_loop1 α γ₀ hγ hrow hA1 hR1 pp M n Q₁ hQ₁ hd1 hd11 hnQ₁
    (by norm_num) (by norm_num) hc₁0 hP hM hVface
  obtain ⟨C₀, h₀⟩ := dec_face_maj_loop0 α γ₀ hγ hrow hA0 hR0 pp M n Q₀ hQ₀ hd0 hd01 hnQ₀
    (by norm_num) (by norm_num) hc₁0 hP hM hVface
  simp only [hF Q₁ he₁] at h₁
  simp only [hF Q₀ he₀] at h₀
  obtain ⟨Cc, hc⟩ := dec_corner_maj hnm α γ₀ huniq hrow cs k M Q hQ hnQ (ρ₀ := ρ₀)
    (by norm_num) (by norm_num) hc₀ hkμ hV
  obtain ⟨Cb, hb⟩ := dec_bulk_maj α γ₀ hrow pp M n Q hQ hnQ (by norm_num) hc₁0 hP hVbulk
  refine ⟨C₁ + C₀ + Cc + Cb, fun s u hu hI => ?_⟩
  rw [dec_integral_sector_eq hrow (ρ₀ := ρ₀) (by norm_num) hI]
  have e1 := h₁ s u hu hI
  have e0 := h₀ s u hu hI
  have ec := hc s u hu
  have eb := hb s u hu
  rw [mul_add, mul_add, mul_add]
  linarith

end QED.GradedProof.RPi4

end
