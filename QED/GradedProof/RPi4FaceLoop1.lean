/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FacePerm
public import QED.GradedProof.RPi4FaceFam

/-!
# (R-Π₄) steps L6d1–L6d2: the loop-`1` face of any collapsed piece, with rate `u^{-1/2}`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), steps L6d1–L6d2. For a
collapsed piece in its own line order (loop rows `(1, 0)`, `(0, 1)` or `(1, -1)`, the photon
with row `(1, -1)`), the face of loop `1` is the part of the simplex where the weight of the
lines with row `(0, 1)` or `(1, -1)` is at most `ρ₀`. This file sorts the lines (no permutation
has to be given) and chooses the face bracket, so the face rate holds under hypotheses that can
be read off the piece:

* `cFourG_eS_three`, `paramAtV_face_vtx3`, `FaceBr.rep_vtx3`, `FaceBr.rep_vtx₂3`: the vertex
  bracket also represents numerators of degree `3` along loop `1` (the faces `S ∪ γ` of a chain
  with three fermion lines, whose limit vanishes);
* `FaceSort.kF_shape_le`, `FaceSort.kM_shape_le`: the uniform bounds of the sorted shape;
* **`face_rate_loop1`**: `‖u ∫_{faceSum ≤ ρ₀} pieceF - L‖ ≤ C u^{-1/2}`, uniformly over a family
  of momenta, masses and numerators (bounded momenta and masses, `LQBdd` numerators of degree
  `≤ 3` along loop `1`, `≤ 1` if the face block has two lines, `V₀ ≥ c₁` near the face).
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint)

/-! ### The vertex bracket at degree three -/

theorem cFourG_eS_three {s : Fin 2} {Q : LoopQuartic} (hQ : LoopDegLe s 3 Q) :
    cFourG Q (eS s) = 0 := by
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
  by_cases hq : 3 < loopInd s a + loopInd s b + loopInd s c + loopInd s d
  · rw [hQ.quart a b c d hq, zero_mul]
  · have h1 := loopInd_le_one s a
    have h2 := loopInd_le_one s b
    have h3 := loopInd_le_one s c
    have h4 := loopInd_le_one s d
    have h := fun x y (hxy : loopInd s x + loopInd s y ≤ 1) => gMet_eS_eq_zero (s := s) hxy
    have key : matPair (gMet (eS s)) a b c d = 0 := by
      simp only [matPair]
      have e1 : gMet (eS s) a b * gMet (eS s) c d = 0 := by
        rcases Nat.lt_or_ge (loopInd s a + loopInd s b) 2 with hab | hab
        · rw [h a b (by omega), zero_mul]
        · rw [h c d (by omega), mul_zero]
      have e2 : gMet (eS s) a c * gMet (eS s) b d = 0 := by
        rcases Nat.lt_or_ge (loopInd s a + loopInd s c) 2 with hab | hab
        · rw [h a c (by omega), zero_mul]
        · rw [h b d (by omega), mul_zero]
      have e3 : gMet (eS s) a d * gMet (eS s) b c = 0 := by
        rcases Nat.lt_or_ge (loopInd s a + loopInd s d) 2 with hab | hab
        · rw [h a d (by omega), zero_mul]
        · rw [h b c (by omega), mul_zero]
      rw [e1, e2, e3]
      ring
    rw [key, ofReal_zero, mul_zero]

section Vtx3

variable {n p m : ℕ} {Q : LoopQuartic} {α : Fin (m + 1) → Fin 2 → ℝ} {pp : Fin (m + 1) → Fin 4 → ℝ}
  {z : Fin (m + 1) → ℝ} {ρ a b c : ℝ} {b₁ : Fin 4 → ℝ}

/-- `paramAtV_face_vtx` for numerators of degree `≤ 3` along loop `1`. -/
theorem paramAtV_face_vtx3 (hQ : LoopDegLe 1 3 Q) (hp : 2 ≤ p)
    (h : IsFaceMat (symanzikMatrix α z) ρ a b c) (hρ : ρ ≠ 0) (hu : uHat ρ a b c ≠ 0)
    (hβ : ∀ μ, symanzikVector α pp z 1 μ = ρ * b₁ μ) (v : ℝ) :
    (ρ : ℂ) ^ (p + 1) * paramAtV n Q α pp z v = ((uHat ρ a b c ^ 2 : ℝ) : ℂ)⁻¹ *
      ((ρ : ℂ) ^ (p - 2) * faceBrVtx n Q ρ a b c (symanzikVector α pp z 0) b₁ v) := by
  rw [paramAtV_face_aux h hρ hu hβ, cFourG_eS_three hQ]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  have hρc : (ρ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hρ
  have huc : (uHat ρ a b c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu
  simp only [faceBrVtx, Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

theorem FaceBr.rep_vtx3 (hQ : LoopDegLe 1 3 Q) (hp : 2 ≤ p) :
    (FaceBr.vtx n Q).Rep n p Q α pp :=
  fun _ _ _ _ _ _ h hρ hu hβ v => by
    rw [FaceBr.val_vtx]; exact paramAtV_face_vtx3 hQ hp h hρ hu hβ v

theorem FaceBr.rep_vtx₂3 (hQ : LoopDegLe 1 3 Q) (hq : Q.quart = 0) (hp : 2 ≤ p) :
    (FaceBr.vtx₂ n Q).Rep n p Q α pp :=
  fun z ρ a b c b₁ h hρ hu hβ v => by
    rw [FaceBr.val_vtx₂ hq]; exact FaceBr.rep_vtx3 hQ hp z ρ a b c b₁ h hρ hu hβ v

end Vtx3

/-! ### Uniform bounds of a sorted shape -/

theorem sum_abs_le_card {n : ℕ} {f : Fin n → ℝ} {B : ℝ} (h : ∀ i, |f i| ≤ B) :
    ∑ i, |f i| ≤ n * B :=
  (Finset.sum_le_sum fun i _ => h i).trans_eq (by simp)

theorem abs_dot_self_le {a : Fin 4 → ℝ} {K : ℝ} (h : ‖a‖ ≤ K) :
    |Minkowski.dot a a| ≤ 4 * K ^ 2 := by
  have hb : ∀ μ, a μ ^ 2 ≤ K ^ 2 := fun μ => by
    have h1 : |a μ| ≤ K := (norm_le_pi_norm a μ).trans h
    nlinarith [abs_nonneg (a μ), sq_abs (a μ)]
  rw [Minkowski.dot_eq, abs_le]
  constructor <;> nlinarith [sq_nonneg (a 0), sq_nonneg (a 1), sq_nonneg (a 2), sq_nonneg (a 3),
    hb 0, hb 1, hb 2, hb 3]

namespace FaceSort

variable {p q : ℕ} {α : Fin (p + 1 + 1 + q + 1) → Fin 2 → ℝ}
  {e : Equiv.Perm (Fin (p + 1 + 1 + q + 1))} (h : FaceSort p q α e)
  {pp : Fin (p + 1 + 1 + q + 1) → Fin 4 → ℝ} {M : Fin (p + 1 + 1 + q + 1) → ℝ} {KP KM : ℝ}

theorem kF_shape_le (hα : ∀ l s, |α l s| ≤ 1) (hP : ∀ l, ‖pp l‖ ≤ KP) :
    (h.shape pp M).kF ≤ 1 + 3 * (p + 1 + 1) + 4 * ((q + 1) + 2 * (p + 1 + 1)) * KP := by
  have hαα : ∀ l s t, |α l s * α l t| ≤ 1 := fun l s t => by
    rw [abs_mul]
    exact (mul_le_mul (hα l s) (hα l t) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hαp : ∀ l s μ, |α l s * pp l μ| ≤ KP := fun l s μ => by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hα l s)).trans
      ((norm_le_pi_norm (pp l) μ).trans (hP l))
  have hpμ : ∀ l μ, |pp l μ| ≤ KP := fun l μ => (norm_le_pi_norm (pp l) μ).trans (hP l)
  have hkP : (h.shape pp M).kP ≤ 4 * ((q + 1) + 2 * (p + 1 + 1)) * KP := by
    unfold FaceShape.kP
    refine (Finset.sum_le_sum fun μ _ => add_le_add (add_le_add
      (sum_abs_le_card fun j => hpμ _ μ) (sum_abs_le_card fun i => hαp _ 0 μ))
      (sum_abs_le_card fun i => hαp _ 1 μ)).trans_eq ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  unfold FaceShape.kF
  have e1 := sum_abs_le_card (n := p + 1 + 1) fun i => hαα (e (Fin.castAdd (q + 1) i)) 0 0
  have e2 := sum_abs_le_card (n := p + 1 + 1) fun i => hαα (e (Fin.castAdd (q + 1) i)) 0 1
  have e3 := sum_abs_le_card (n := p + 1 + 1) fun i => hαα (e (Fin.castAdd (q + 1) i)) 1 1
  simp only [shape] at e1 e2 e3 hkP ⊢
  push_cast at e1 e2 e3 ⊢
  linarith

theorem kM_shape_le (hP : ∀ l, ‖pp l‖ ≤ KP) (hM : ∀ l, |M l| ≤ KM) :
    (h.shape pp M).kM ≤ ((p + 1 + 1) + (q + 1)) * (KM ^ 2 + 4 * KP ^ 2) := by
  have hl : ∀ l, |M l ^ 2 + Minkowski.dot (pp l) (pp l)| ≤ KM ^ 2 + 4 * KP ^ 2 := fun l => by
    refine (abs_add_le _ _).trans (add_le_add ?_ (abs_dot_self_le (hP l)))
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hM l) 2
  unfold FaceShape.kM
  have e1 := sum_abs_le_card (n := p + 1 + 1) fun i => hl (e (Fin.castAdd (q + 1) i))
  have e2 := sum_abs_le_card (n := q + 1) fun j => hl (e (Fin.natAdd (p + 1 + 1) j))
  simp only [shape] at e1 e2 ⊢
  push_cast at e1 e2 ⊢
  linarith

end FaceSort

/-! ### The loop-`1` face of a piece -/

/-- **The loop-`1` face of a family of collapsed pieces, with rate `u^{-1/2}` uniform over the
family.** The lines are sorted internally; the face bracket is the self-energy bracket when the
face block has two lines and the vertex bracket otherwise (three terms for `n = 7`, two for
`n = 6` with cubic numerators). -/
theorem face_rate_loop1 {ι : Type*} {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (γ₀ : Fin (m + 1))
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
    ∃ C : ℝ, ∃ L : ι → ℂ, ∀ s, ∀ u : ℝ, 0 < u →
      IntegrableOn (fun x => pieceF n (Q s) α (pp s) (M s) γ₀ u (simplexPoint x))
        (simplexSet m) →
      ‖u • (∫ x in simplexSet m,
          {w | faceSum α w ≤ ρ₀}.indicator (pieceF n (Q s) α (pp s) (M s) γ₀ u)
            (simplexPoint x)) - L s‖ ≤ C * u ^ (-(1 / 2) : ℝ) := by
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
  have hV' : ∀ s (w : Fin (p + 1 + 1 + q + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w (FaceSort.gam e) ≤ ρ₀ → c₁ ≤ symanzikV α (pp s) (M s) w := by
    rw [hgam]; exact hV
  -- the bracket
  have fin : ∀ {r : ℕ} (B : ι → FaceBr r) (k : Fin r → ℕ), (∀ s, (B s).k = k) →
      (∀ j, 2 ≤ k j) → (∀ s, (B s).Meas) →
      (∀ j, UnifLip ρ₀ fun (i : ι × FaceIdx (p + 1) q) ρ =>
        (hS.shape (pp i.1) (M i.1)).coefJ (B i.1) j ρ (FaceShape.Wi i.2) (FaceShape.Vi i.2)) →
      (∀ s, (B s).Rep n (p + 1) (Q s) (fun i => α (e i)) (fun i => pp s (e i))) →
      ∃ C : ℝ, ∃ L : ι → ℂ, ∀ s, ∀ u : ℝ, 0 < u →
        IntegrableOn (fun x => pieceF n (Q s) α (pp s) (M s) γ₀ u (simplexPoint x))
          (simplexSet (p + 1 + 1 + q)) →
        ‖u • (∫ x in simplexSet (p + 1 + 1 + q),
            {w | faceSum α w ≤ ρ₀}.indicator (pieceF n (Q s) α (pp s) (M s) γ₀ u)
              (simplexPoint x)) - L s‖ ≤ C * u ^ (-(1 / 2) : ℝ) := by
    intro r B k hkc hk hB hD hRep
    obtain ⟨C, hC⟩ := hS.face_rate_piece pp M n Q B k hρ₀ hρ₁ hc₁ hK hKM hkc hk hB hD hRep hV'
    refine ⟨C, fun s => ∫ σ in Ioi 0, (hS.shape (pp s) (M s)).gJ (B s) 0 σ, fun s u hu hf => ?_⟩
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

end QED.GradedProof.RPi4

end
