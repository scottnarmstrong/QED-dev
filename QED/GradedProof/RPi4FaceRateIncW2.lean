/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceRateIncW1

/-!
# (R-Π₄) step L10, B-inc: the weighted face of a collapsed piece

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10, the rate (B) of
the face-rate increment. The weight of the `σ`-derivative of a piece is the second Symanzik
function at masses `0`, `B(z) = symanzikV α pp 0 z`. In join coordinates of a sorted piece it is
the rescaled `vHat` of the massless shape (`FaceShape.symanzikV_join_eq`), which is uniformly
Lipschitz (`FaceShape.unifLip_vHat`), so the weighted face rate (`faceIdRayW_face_sector_rate`)
applies with the coefficients `coefJ · vHat₀`:

* `pieceFw`: the weighted collapsed integrand `B(z) pieceF`;
* `FaceSort.faceIdRayW_face_rate_piece`: a sorted family of pieces;
* **`faceIdRayW_face_rate_loop1`**, **`faceIdRayW_face_rate_loop0`**: a collapsed family in its
  own line order, for every `n ≥ 7` (and `n = 6` with cubic numerators), so in particular for the
  exponent `n + 1` of the derivative of the seven-line (`n = 7`) and six-line (`n = 6`) pieces.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet
  simplexPoint_mem_stdSimplex)
open QED.Integration.SimplexMerge (integral_simplex_comp_perm integrableOn_simplex_comp_perm_iff)

/-- **The weighted collapsed integrand** `B(z) pieceF`, `B(z) = symanzikV α pp 0 z` (the second
Symanzik function at masses `0`). -/
noncomputable def pieceFw {m : ℕ} (n : ℕ) (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (pp : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (γ : Fin (m + 1)) (u : ℝ)
    (z : Fin (m + 1) → ℝ) : ℂ :=
  (symanzikV α pp 0 z : ℂ) * pieceF n Q α pp M γ u z

/-! ### A sorted piece -/

namespace FaceSort

variable {ι : Type*} {p q r : ℕ} {α : Fin (p + 1 + 1 + q + 1) → Fin 2 → ℝ}
  {e : Equiv.Perm (Fin (p + 1 + 1 + q + 1))}

/-- The weight of a sorted piece in join coordinates is the `vHat` of the massless shape. -/
theorem faceIdRayW_weight_join (h : FaceSort p q α e) (pp : Fin (p + 1 + 1 + q + 1) → Fin 4 → ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) {w : Fin (p + 1) → ℝ} (hw : w ∈ simplexSet (p + 1))
    {v : Fin q → ℝ} (hv : v ∈ simplexSet q) :
    symanzikV α pp 0 (fun j => joinZ ρ (simplexPoint w) (simplexPoint v) (e.symm j)) =
      (h.shape pp 0).vHat ρ (simplexPoint w) (simplexPoint v) := by
  obtain ⟨hw0, hw1⟩ := simplexPoint_mem_stdSimplex hw
  obtain ⟨-, hv1⟩ := simplexPoint_mem_stdSimplex hv
  have hu : (h.shape pp 0).uJ ρ (simplexPoint w) (simplexPoint v) ≠ 0 := by
    have := (h.shape pp 0).uJ_ge ρ _ _ hw0 hw1 hv1 hρ.le
    exact ne_of_gt (by linarith)
  rw [← symanzikV_perm, ← h.shape_α pp 0, ← h.shape_pp pp 0, ← h.shape_M pp 0]
  exact (h.shape pp 0).symanzikV_join_eq ρ _ _ hρ.ne' hu

/-- **The weighted face sector of a family of pieces in their own line order, with rate
`C (1 + c₁⁻¹)^N u^{-1/2}`** (the weighted form of `faceIdRayB_face_rate_piece`). -/
theorem faceIdRayW_face_rate_piece (h : FaceSort p q α e)
    (pp : ι → Fin (p + 1 + 1 + q + 1) → Fin 4 → ℝ) (M : ι → Fin (p + 1 + 1 + q + 1) → ℝ)
    (n : ℕ) (Q : ι → LoopQuartic) (B : ι → FaceBr r) (k : Fin r → ℕ) {ρ₀ K KM KM₀ : ℝ}
    (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1)
    (hK : ∀ s, (h.shape (pp s) (M s)).kF ≤ K) (hKM : ∀ s, (h.shape (pp s) (M s)).kM ≤ KM)
    (hKM₀ : ∀ s, (h.shape (pp s) 0).kM ≤ KM₀)
    (hkc : ∀ s, (B s).k = k) (hk : ∀ j, 2 ≤ k j) (hB : ∀ s, (B s).Meas)
    (hD : ∀ j, UnifLip ρ₀ fun (i : ι × FaceIdx (p + 1) q) ρ =>
      (h.shape (pp i.1) (M i.1)).coefJ (B i.1) j ρ (FaceShape.Wi i.2) (FaceShape.Vi i.2))
    (hRep : ∀ s, (B s).Rep n (p + 1) (Q s) (fun i => α (e i)) (fun i => pp s (e i)))
    (c₁ : ι → ℝ) (hc₁ : ∀ s, 0 < c₁ s)
    (hV : ∀ s (w : Fin (p + 1 + 1 + q + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w (gam e) ≤ ρ₀ → c₁ s ≤ symanzikV α (pp s) (M s) w) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ s, ∀ u : ℝ, 0 < u →
      IntegrableOn (fun x => pieceFw n (Q s) α (pp s) (M s) (gam e) u (simplexPoint x))
        (simplexSet (p + 1 + 1 + q)) →
      ‖u • (∫ x in simplexSet (p + 1 + 1 + q),
          {w | faceSum α w ≤ ρ₀}.indicator (pieceFw n (Q s) α (pp s) (M s) (gam e) u)
            (simplexPoint x)) -
        ∫ σ in Ioi 0, (h.shape (pp s) (M s)).gJw (B s) (h.shape (pp s) 0).vHat 0 σ‖ ≤
        C * (1 + (c₁ s)⁻¹) ^ N * u ^ (-(1 / 2) : ℝ) := by
  set S : ι → FaceShape (p + 1) q := fun s => h.shape (pp s) (M s) with hS
  set S₀ : ι → FaceShape (p + 1) q := fun s => h.shape (pp s) 0 with hS₀
  have hVS : ∀ s ρ, 0 < ρ → ρ ≤ ρ₀ → ∀ x ∈ simplexSet (p + 1) ×ˢ simplexSet q,
      c₁ s ≤ symanzikV (S s).α (S s).pp (S s).M
        (joinZ ρ (simplexPoint x.1) (simplexPoint x.2)) := by
    intro s ρ hρ hρ' x hx
    obtain ⟨hW0, hW1⟩ := simplexPoint_mem_stdSimplex hx.1
    obtain ⟨hV0, hV1⟩ := simplexPoint_mem_stdSimplex hx.2
    set W := simplexPoint x.1
    set V := simplexPoint x.2
    set z := joinZ ρ W V with hz
    have hρ1 : ρ < 1 := hρ'.trans_lt hρ₁
    have hz0 : ∀ l, 0 ≤ z l := fun l => by
      refine Fin.addCases (m := p + 1 + 1) (n := q + 1) (fun i => ?_) (fun j => ?_) l
      · simp only [hz, joinZ, Fin.append_left, Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg hρ.le (hW0 i)
      · simp only [hz, joinZ, Fin.append_right, Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (by linarith) (hV0 j)
    have hz1 : ∑ l, z l = 1 := by
      rw [sum_join]
      simp only [hz, joinZ, Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul,
        ← Finset.mul_sum, hW1, hV1]
      ring
    have hU : symanzikU (S s).α z ≠ 0 := by
      rw [symanzikU, det_face ((S s).isFaceMat ρ W V)]
      have := (S s).uJ_ge ρ W V hW0 hW1 hV1 hρ.le
      exact mul_ne_zero hρ.ne' (by unfold FaceShape.uJ at this; linarith)
    have hzγ : z (S s).γJ ≤ ρ₀ := by
      rw [hz, (S s).joinZ_γJ]
      have hWγ : W (S s).γ ≤ 1 := by
        rw [← hW1]
        exact Finset.single_le_sum (fun i _ => hW0 i) (Finset.mem_univ _)
      nlinarith [hW0 (S s).γ]
    have := hV s (fun j => z (e.symm j)) (fun l => hz0 _)
      (by rw [← hz1]; exact e.symm.sum_comp z)
      (by rwa [← symanzikU_perm, ← h.shape_α (pp s) (M s)])
      (by simpa only [gam, Equiv.symm_apply_apply] using
        (show z (Fin.castAdd (q + 1) (Fin.last (p + 1))) ≤ ρ₀ from hzγ))
    rwa [← symanzikV_perm, ← h.shape_α (pp s) (M s), ← h.shape_pp (pp s) (M s),
      ← h.shape_M (pp s) (M s)] at this
  have hRep' : ∀ s, (B s).Rep n (p + 1) (Q s) (S s).α (S s).pp := fun s => by
    rw [hS]
    dsimp only
    rw [h.shape_α, h.shape_pp]
    exact hRep s
  have hK₀ : ∀ s, (S₀ s).kF ≤ K := hK
  have hD' := fun j => (hD j).mul (FaceShape.unifLip_vHat S₀ hK₀ hρ₁ hKM₀)
  obtain ⟨C, N, hC⟩ := faceIdRayW_face_sector_rate (S := S) (ωJ := fun s => (S₀ s).vHat)
    hρ₀ hρ₁ hK hKM hkc hk hB (fun s => FaceShape.measurable_vX (S := S₀ s)) hD' c₁ hc₁
    hVS (fun s => rfl) hRep' (ω := fun s z => symanzikV α (pp s) 0 fun j => z (e.symm j))
    (fun s ρ hρ hρ1 w hw v hv => h.faceIdRayW_weight_join (pp s) hρ hρ1 hw hv)
  refine ⟨C, N, fun s u hu hf => ?_⟩
  have hfU : ∀ z, (S s).fUw (fun z => symanzikV α (pp s) 0 fun j => z (e.symm j)) n (Q s) u z =
      pieceFw n (Q s) α (pp s) (M s) (gam e) u fun j => z (e.symm j) := fun z => by
    rw [FaceShape.fUw, h.fU_eq (pp s) (M s) n (Q s) u z]
    rfl
  have hf' : IntegrableOn (fun x => (S s).fUw (fun z => symanzikV α (pp s) 0
      fun j => z (e.symm j)) n (Q s) u (simplexPoint x)) (simplexSet (p + 1 + 1 + q)) := by
    simp only [hfU]
    exact (integrableOn_simplex_comp_perm_iff e.symm
      (pieceFw n (Q s) α (pp s) (M s) (gam e) u)).mpr hf
  have hint : ∫ x in simplexSet (p + 1 + 1 + q),
      {w | faceSum α w ≤ ρ₀}.indicator (pieceFw n (Q s) α (pp s) (M s) (gam e) u)
        (simplexPoint x) =
      ∫ x in simplexSet (p + 1 + 1 + q),
        {z | FaceShape.blockSum (p := p + 1) (q := q) z ≤ ρ₀}.indicator
          ((S s).fUw (fun z => symanzikV α (pp s) 0 fun j => z (e.symm j)) n (Q s) u)
          (simplexPoint x) := by
    rw [← integral_simplex_comp_perm e.symm]
    refine setIntegral_congr_fun (measurableSet_simplexSet _) fun x _ => ?_
    simp only [indicator, mem_ofPred_eq, h.blockSum_eq, hfU]
    rfl
  rw [hint]
  exact hC s u hu hf'

end FaceSort

/-! ### A collapsed piece in its own line order -/

/-- **The weighted loop-`1` face of a family of collapsed pieces, with rate
`C (1 + c₁⁻¹)^N u^{-1/2}`** (the weighted form of `faceIdRayB_face_rate_loop1`, for every
`n ≥ 7`, and `n = 6` with cubic numerators; the weight is `B(z) = symanzikV α pp 0 z`). -/
theorem faceIdRayW_face_rate_loop1 {ι : Type*} {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    (γ₀ : Fin (m + 1))
    (hγ : α γ₀ = ![1, -1]) (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (hA : 2 ≤ (Finset.univ.filter fun l => α l ≠ ![1, 0]).card) (hR : ∃ l, α l = ![1, 0])
    (pp : ι → Fin (m + 1) → Fin 4 → ℝ) (M : ι → Fin (m + 1) → ℝ) (n : ℕ)
    (Q : ι → LoopQuartic) {BQ : ℝ} (hQ : LQBdd Q BQ) (hd : ∀ s, LoopDegLe 1 3 (Q s))
    (hd1 : (Finset.univ.filter fun l => α l ≠ ![1, 0]).card = 2 → ∀ s, LoopDegLe 1 1 (Q s))
    (hn : 7 ≤ n ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0))
    {ρ₀ KP KM : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (c₁ : ι → ℝ) (hc₁ : ∀ s, 0 < c₁ s)
    (hP : ∀ s l, ‖pp s l‖ ≤ KP) (hM : ∀ s l, |M s l| ≤ KM)
    (hV : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w γ₀ ≤ ρ₀ → c₁ s ≤ symanzikV α (pp s) (M s) w) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ L : ι → ℂ, ∀ s, ∀ u : ℝ, 0 < u →
      IntegrableOn (fun x => pieceFw n (Q s) α (pp s) (M s) γ₀ u (simplexPoint x))
        (simplexSet m) →
      ‖u • (∫ x in simplexSet m,
          {w | faceSum α w ≤ ρ₀}.indicator (pieceFw n (Q s) α (pp s) (M s) γ₀ u)
            (simplexPoint x)) - L s‖ ≤ C * (1 + (c₁ s)⁻¹) ^ N * u ^ (-(1 / 2) : ℝ) := by
  classical
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
  have hKM₀ := fun s => hS.kM_shape_le (pp := pp s) (M := 0) (KM := 0) (hP s)
    (fun l => by simp)
  have hV' : ∀ s (w : Fin (p + 1 + 1 + q + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w (FaceSort.gam e) ≤ ρ₀ → c₁ s ≤ symanzikV α (pp s) (M s) w := by
    rw [hgam]; exact hV
  -- the bracket
  have fin : ∀ {r : ℕ} (B : ι → FaceBr r) (k : Fin r → ℕ), (∀ s, (B s).k = k) →
      (∀ j, 2 ≤ k j) → (∀ s, (B s).Meas) →
      (∀ j, UnifLip ρ₀ fun (i : ι × FaceIdx (p + 1) q) ρ =>
        (hS.shape (pp i.1) (M i.1)).coefJ (B i.1) j ρ (FaceShape.Wi i.2) (FaceShape.Vi i.2)) →
      (∀ s, (B s).Rep n (p + 1) (Q s) (fun i => α (e i)) (fun i => pp s (e i))) →
      ∃ C : ℝ, ∃ N : ℕ, ∃ L : ι → ℂ, ∀ s, ∀ u : ℝ, 0 < u →
        IntegrableOn (fun x => pieceFw n (Q s) α (pp s) (M s) γ₀ u (simplexPoint x))
          (simplexSet (p + 1 + 1 + q)) →
        ‖u • (∫ x in simplexSet (p + 1 + 1 + q),
            {w | faceSum α w ≤ ρ₀}.indicator (pieceFw n (Q s) α (pp s) (M s) γ₀ u)
              (simplexPoint x)) - L s‖ ≤ C * (1 + (c₁ s)⁻¹) ^ N * u ^ (-(1 / 2) : ℝ) := by
    intro r B k hkc hk hB hD hRep
    obtain ⟨C, N, hC⟩ := hS.faceIdRayW_face_rate_piece pp M n Q B k hρ₀ hρ₁ hK hKM hKM₀ hkc hk
      hB hD hRep c₁ hc₁ hV'
    refine ⟨C, N, fun s => ∫ σ in Ioi 0, (hS.shape (pp s) (M s)).gJw (B s)
      (hS.shape (pp s) 0).vHat 0 σ, fun s u hu hf => ?_⟩
    rw [← hgam] at hf ⊢
    exact hC s u hu hf
  set S : ι → FaceShape (p + 1) q := fun s => hS.shape (pp s) (M s)
  have hK' : ∀ s, (S s).kF ≤ 1 + 3 * (p + 1 + 1) + 4 * ((q + 1) + 2 * (p + 1 + 1)) * KP := hK
  rcases hn with hn7 | ⟨rfl, hq0⟩
  · rcases Nat.eq_zero_or_pos p with rfl | hp1
    · exact fin (fun s => FaceBr.se n (Q s)) ![n - 3, n - 4, n - 5] (fun _ => rfl)
        (fun j => by fin_cases j <;> simp <;> omega)
        (fun _ => FaceBr.meas_se) (FaceShape.unifLip_coefJ_se S hK' hρ₁ n hQ)
        (fun s => FaceBr.rep_se (hd1 (by omega) s) le_rfl)
    · exact fin (fun s => FaceBr.vtx n (Q s)) ![n - 3, n - 4, n - 5] (fun _ => rfl)
        (fun j => by fin_cases j <;> simp <;> omega)
        (fun _ => FaceBr.meas_vtx) (FaceShape.unifLip_coefJ_vtx S hK' hρ₁ n hQ)
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

/-- **The weighted loop-`0` face of a family of collapsed pieces, with rate
`C (1 + c₁⁻¹)^N u^{-1/2}`**: the mirror of `faceIdRayW_face_rate_loop1`, cut by `faceSum0`. -/
theorem faceIdRayW_face_rate_loop0 {ι : Type*} {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    (γ₀ : Fin (m + 1))
    (hγ : α γ₀ = ![1, -1]) (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (hA : 2 ≤ (Finset.univ.filter fun l => α l ≠ ![0, 1]).card) (hR : ∃ l, α l = ![0, 1])
    (pp : ι → Fin (m + 1) → Fin 4 → ℝ) (M : ι → Fin (m + 1) → ℝ) (n : ℕ)
    (Q : ι → LoopQuartic) {BQ : ℝ} (hQ : LQBdd Q BQ) (hd : ∀ s, LoopDegLe 0 3 (Q s))
    (hd1 : (Finset.univ.filter fun l => α l ≠ ![0, 1]).card = 2 → ∀ s, LoopDegLe 0 1 (Q s))
    (hn : 7 ≤ n ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0))
    {ρ₀ KP KM : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (c₁ : ι → ℝ) (hc₁ : ∀ s, 0 < c₁ s)
    (hP : ∀ s l, ‖pp s l‖ ≤ KP) (hM : ∀ s l, |M s l| ≤ KM)
    (hV : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w γ₀ ≤ ρ₀ → c₁ s ≤ symanzikV α (pp s) (M s) w) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ L : ι → ℂ, ∀ s, ∀ u : ℝ, 0 < u →
      IntegrableOn (fun x => pieceFw n (Q s) α (pp s) (M s) γ₀ u (simplexPoint x))
        (simplexSet m) →
      ‖u • (∫ x in simplexSet m,
          {w | faceSum0 α w ≤ ρ₀}.indicator (pieceFw n (Q s) α (pp s) (M s) γ₀ u)
            (simplexPoint x)) - L s‖ ≤ C * (1 + (c₁ s)⁻¹) ^ N * u ^ (-(1 / 2) : ℝ) := by
  have hrow' : ∀ l, swapFlip α l = ![1, 0] ∨ swapFlip α l = ![0, 1] ∨
      swapFlip α l = ![1, -1] := fun l => by
    rcases hrow l with h | h | h
    · exact Or.inr (Or.inl (swapFlip_row_10 h))
    · exact Or.inl (swapFlip_row_01 h)
    · exact Or.inr (Or.inr (swapFlip_row_1m1 h))
  obtain ⟨l, hl⟩ := hR
  obtain ⟨C, N, L, hC⟩ := faceIdRayW_face_rate_loop1 (swapFlip α) γ₀ (swapFlip_row_1m1 hγ) hrow'
    (by rw [filter_swapFlip hrow]; exact hA) ⟨l, swapFlip_row_01 hl⟩
    (fun s => flipMom (photonSign α) (pp s)) M n (fun s => swapQ (Q s)) (lqBdd_swapQ hQ)
    (fun s => loopDegLe_swapQ (hd s))
    (fun h s => loopDegLe_swapQ (hd1 (by rw [← filter_swapFlip hrow]; exact h) s))
    (by rcases hn with h | ⟨h, h'⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, fun s => quart_swapQ (h' s)⟩)
    hρ₀ hρ₁ c₁ hc₁ (fun s => norm_flipMom_le (pp s) (hP s)) hM
    (fun s w hw hw1 hU hγw => by
      rw [symanzikV_swapFlip]
      exact hV s w hw hw1 (by rwa [symanzikU_swapFlip] at hU) hγw)
  refine ⟨C, N, L, fun s u hu hf => ?_⟩
  have e : ∀ w, pieceFw n (swapQ (Q s)) (swapFlip α) (flipMom (photonSign α) (pp s)) (M s) γ₀ u
      w = pieceFw n (Q s) α (pp s) (M s) γ₀ u w := fun w => by
    rw [pieceFw, pieceFw, symanzikV_swapFlip, pieceF_swapFlip α (pp s) (M s) w n _ γ₀ u]
  have e' := funext e
  have hfs : faceSum (swapFlip α) = faceSum0 α := funext fun w => faceSum_swapFlip w hrow
  have h := hC s u hu (by simp only [e]; exact hf)
  rw [e', hfs] at h
  exact h

end QED.GradedProof.RPi4

end
