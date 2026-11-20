/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceLoop1
public import QED.GradedProof.RPi4FaceIdSigma

/-!
# (R-Π₄) step L6d3: the loop-`1` face of a piece with its limit named

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3.
`face_rate_loop1` gives the loop-`1` face rate of a collapsed piece with an existential limit.
Here the limit is named: for any permutation `e` sorting the piece face block first with the
photon last (`FaceSort`; one exists, `faceId_exists_sort`), the face sector of the piece tends at
rate `u^{-1/2}` to `faceIdVal`, the face integral `faceIdInt` at `ρ = 0` of the sorted shape with
the bracket of `face_rate_loop1` (self-energy bracket when the face block has one fermion line,
vertex bracket otherwise; three terms for `n = 7`, two for `n = 6`). When the face block has more
than two fermion lines, `faceIdVal = 0`.

* `faceIdVal`, `faceId_faceIdVal_eq_zero`;
* `faceId_exists_sort`, `faceId_famHyp` (the hypotheses `FamHyp` of the sorted shapes);
* **`faceId_face_rate_sort`**: the face rate with the limit `faceIdVal`;
* **`faceId_face_limUnder_sort`**: the face limit (`limUnder atTop`) is `faceIdVal`.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint simplexPoint_mem_stdSimplex)

/-- **The face value of a sorted shape** with the bracket of `face_rate_loop1`: the face integral
at `ρ = 0` of the self-energy bracket (`p = 0`, one fermion line in the face block) or the vertex
bracket (`p ≥ 1`), with three terms for `n = 7` and two otherwise. -/
noncomputable def faceIdVal (n : ℕ) {p q : ℕ} (S : FaceShape (p + 1) q) (Q : LoopQuartic) : ℂ :=
  if n = 7 then
    (if p = 0 then S.faceIdInt (FaceBr.se 7 Q) else S.faceIdInt (FaceBr.vtx 7 Q))
  else
    (if p = 0 then S.faceIdInt (FaceBr.se₂ 6 Q) else S.faceIdInt (FaceBr.vtx₂ 6 Q))

/-- **A face block with more than two fermion lines has face value `0`.** -/
theorem faceId_faceIdVal_eq_zero (n : ℕ) {p q : ℕ} (S : FaceShape (p + 1) q) (Q : LoopQuartic)
    (hp : 2 ≤ p) : faceIdVal n S Q = 0 := by
  have h1 : ¬p = 0 := by omega
  have hv : (FaceBr.vtx 7 Q).d < p + 1 := by simp [FaceBr.vtx]; omega
  have hv₂ : (FaceBr.vtx₂ 6 Q).d < p + 1 := by simp [FaceBr.vtx₂]; omega
  unfold faceIdVal
  split_ifs
  · exact S.faceId_faceIdInt_eq_zero _ hv
  · exact S.faceId_faceIdInt_eq_zero _ hv₂

/-- **A sorting permutation exists**: face block (rows `(0, 1)`, `(1, -1)`) first, photon last
in it, rest (row `(1, 0)`) after. -/
theorem faceId_exists_sort {p q : ℕ} (α : Fin (p + 1 + 1 + q + 1) → Fin 2 → ℝ)
    (γ₀ : Fin (p + 1 + 1 + q + 1)) (hγ : α γ₀ = ![1, -1])
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (hp : (Finset.univ.filter fun l => α l ≠ ![1, 0]).card = p + 1 + 1) :
    ∃ e : Equiv.Perm (Fin (p + 1 + 1 + q + 1)), FaceSort p q α e ∧ FaceSort.gam e = γ₀ := by
  classical
  set A := Finset.univ.filter fun l => α l ≠ ![1, 0] with hAdef
  have hmemA : ∀ l, l ∈ A ↔ α l ≠ ![1, 0] := fun l => by simp [hAdef]
  have hγA : γ₀ ∈ A := (hmemA γ₀).mpr (by rw [hγ]; exact row1m1_ne)
  have cA : Fintype.card {l // l ∈ A} = p + 1 + 1 := by simp [hp]
  have cR : Fintype.card {l // ¬l ∈ A} = q + 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]
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
  refine ⟨e, ⟨fun i => ?_, fun j => ?_⟩, ?_⟩
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
  · simp only [FaceSort.gam, he, Equiv.trans_apply]
    exact Equiv.swap_apply_left _ _

/-- **The hypotheses `FamHyp` of a family of sorted shapes** from those of
`FaceSort.face_rate_piece` (the lower bound on `V₀` in the piece's own coordinates). -/
theorem faceId_famHyp {ι : Type*} {p q r : ℕ} {α : Fin (p + 1 + 1 + q + 1) → Fin 2 → ℝ}
    {e : Equiv.Perm (Fin (p + 1 + 1 + q + 1))} (h : FaceSort p q α e)
    (pp : ι → Fin (p + 1 + 1 + q + 1) → Fin 4 → ℝ)
    (M : ι → Fin (p + 1 + 1 + q + 1) → ℝ) (B : ι → FaceBr r)
    (k : Fin r → ℕ) {ρ₀ c₁ K KM : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (hc₁ : 0 < c₁)
    (hK : ∀ s, (h.shape (pp s) (M s)).kF ≤ K) (hKM : ∀ s, (h.shape (pp s) (M s)).kM ≤ KM)
    (hkc : ∀ s, (B s).k = k) (hk : ∀ j, 2 ≤ k j) (hB : ∀ s, (B s).Meas)
    (hD : ∀ j, UnifLip ρ₀ fun (i : ι × FaceIdx (p + 1) q) ρ =>
      (h.shape (pp i.1) (M i.1)).coefJ (B i.1) j ρ (FaceShape.Wi i.2) (FaceShape.Vi i.2))
    (hV : ∀ s (w : Fin (p + 1 + 1 + q + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w (FaceSort.gam e) ≤ ρ₀ → c₁ ≤ symanzikV α (pp s) (M s) w) :
    FaceShape.FamHyp (fun s => h.shape (pp s) (M s)) B k ρ₀ c₁ K KM := by
  set S : ι → FaceShape (p + 1) q := fun s => h.shape (pp s) (M s) with hS
  have hVS : ∀ s ρ, 0 < ρ → ρ ≤ ρ₀ → ∀ x ∈ simplexSet (p + 1) ×ˢ simplexSet q,
      c₁ ≤ symanzikV (S s).α (S s).pp (S s).M
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
      (by simpa only [FaceSort.gam, Equiv.symm_apply_apply] using
        (show z (Fin.castAdd (q + 1) (Fin.last (p + 1))) ≤ ρ₀ from hzγ))
    rwa [← symanzikV_perm, ← h.shape_α (pp s) (M s), ← h.shape_pp (pp s) (M s),
      ← h.shape_M (pp s) (M s)] at this
  exact ⟨hρ₀, hρ₁, hc₁, hK, hKM, hkc, hk, hB, hD, hVS⟩

/-- **The loop-`1` face of a family of sorted pieces, with its limit named**: for a permutation
`e` sorting the piece (photon `γ₀` last in the face block), the face sector tends to the face
value `faceIdVal` of the sorted shape at rate `u^{-1/2}`, uniformly over the family. The
hypotheses are those of `face_rate_loop1`. -/
theorem faceId_face_rate_sort {ι : Type*} {p q : ℕ} (α : Fin (p + 1 + 1 + q + 1) → Fin 2 → ℝ)
    {e : Equiv.Perm (Fin (p + 1 + 1 + q + 1))} (hS : FaceSort p q α e)
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (pp : ι → Fin (p + 1 + 1 + q + 1) → Fin 4 → ℝ) (M : ι → Fin (p + 1 + 1 + q + 1) → ℝ)
    (n : ℕ) (Q : ι → LoopQuartic) {BQ : ℝ} (hQ : LQBdd Q BQ) (hd : ∀ s, LoopDegLe 1 3 (Q s))
    (hd1 : p = 0 → ∀ s, LoopDegLe 1 1 (Q s))
    (hn : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0))
    {ρ₀ c₁ KP KM : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (hc₁ : 0 < c₁)
    (hP : ∀ s l, ‖pp s l‖ ≤ KP) (hM : ∀ s l, |M s l| ≤ KM)
    (hV : ∀ s (w : Fin (p + 1 + 1 + q + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w (FaceSort.gam e) ≤ ρ₀ → c₁ ≤ symanzikV α (pp s) (M s) w) :
    ∃ C : ℝ, ∀ s, ∀ u : ℝ, 0 < u →
      IntegrableOn (fun x => pieceF n (Q s) α (pp s) (M s) (FaceSort.gam e) u (simplexPoint x))
        (simplexSet (p + 1 + 1 + q)) →
      ‖u • (∫ x in simplexSet (p + 1 + 1 + q),
          {w | faceSum α w ≤ ρ₀}.indicator (pieceF n (Q s) α (pp s) (M s) (FaceSort.gam e) u)
            (simplexPoint x)) - faceIdVal n (hS.shape (pp s) (M s)) (Q s)‖ ≤
        C * u ^ (-(1 / 2) : ℝ) := by
  have hα : ∀ l s, |α l s| ≤ 1 := fun l s => by
    rcases hrow l with h1 | h1 | h1 <;> rw [h1] <;> fin_cases s <;> simp
  have hK := fun s => hS.kF_shape_le (M := M s) hα (hP s)
  have hKM := fun s => hS.kM_shape_le (pp := pp s) (hP s) (hM s)
  set S : ι → FaceShape (p + 1) q := fun s => hS.shape (pp s) (M s)
  have hK' : ∀ s, (S s).kF ≤ 1 + 3 * (p + 1 + 1) + 4 * ((q + 1) + 2 * (p + 1 + 1)) * KP := hK
  -- the rate to the face integral of a bracket family
  have fin : ∀ {r : ℕ} (B : ι → FaceBr r) (k : Fin r → ℕ), (∀ s, (B s).k = k) →
      (∀ j, 2 ≤ k j) → (∀ s, (B s).Meas) →
      (∀ j, UnifLip ρ₀ fun (i : ι × FaceIdx (p + 1) q) ρ =>
        (S i.1).coefJ (B i.1) j ρ (FaceShape.Wi i.2) (FaceShape.Vi i.2)) →
      (∀ s, (B s).Rep n (p + 1) (Q s) (fun i => α (e i)) (fun i => pp s (e i))) →
      ∃ C : ℝ, ∀ s, ∀ u : ℝ, 0 < u →
        IntegrableOn (fun x => pieceF n (Q s) α (pp s) (M s) (FaceSort.gam e) u
          (simplexPoint x)) (simplexSet (p + 1 + 1 + q)) →
        ‖u • (∫ x in simplexSet (p + 1 + 1 + q),
            {w | faceSum α w ≤ ρ₀}.indicator
              (pieceF n (Q s) α (pp s) (M s) (FaceSort.gam e) u) (simplexPoint x)) -
          (S s).faceIdInt (B s)‖ ≤ C * u ^ (-(1 / 2) : ℝ) := by
    intro r B k hkc hk hB hD hRep
    obtain ⟨C, hC⟩ := hS.face_rate_piece pp M n Q B k hρ₀ hρ₁ hc₁ hK hKM hkc hk hB hD hRep hV
    have hF : FaceShape.FamHyp S B k ρ₀ c₁ _ _ :=
      faceId_famHyp hS pp M B k hρ₀ hρ₁ hc₁ hK hKM hkc hk hB hD hV
    refine ⟨C, fun s u hu hf => ?_⟩
    rw [← FaceShape.faceId_integral_gJ_zero hF s]
    exact hC s u hu hf
  rcases hn with rfl | ⟨rfl, hq0⟩
  · rcases Nat.eq_zero_or_pos p with rfl | hp1
    · obtain ⟨C, hC⟩ := fin (fun s => FaceBr.se 7 (Q s)) ![7 - 3, 7 - 4, 7 - 5] (fun _ => rfl)
        (fun j => by fin_cases j <;> simp)
        (fun _ => FaceBr.meas_se) (FaceShape.unifLip_coefJ_se S hK' hρ₁ 7 hQ)
        (fun s => FaceBr.rep_se (hd1 rfl s) le_rfl)
      exact ⟨C, fun s u hu hf => by simpa [faceIdVal] using hC s u hu hf⟩
    · obtain ⟨C, hC⟩ := fin (fun s => FaceBr.vtx 7 (Q s)) ![7 - 3, 7 - 4, 7 - 5] (fun _ => rfl)
        (fun j => by fin_cases j <;> simp)
        (fun _ => FaceBr.meas_vtx) (FaceShape.unifLip_coefJ_vtx S hK' hρ₁ 7 hQ)
        (fun s => FaceBr.rep_vtx3 (hd s) (by omega))
      have hp0 : p ≠ 0 := by omega
      exact ⟨C, fun s u hu hf => by simpa [faceIdVal, hp0] using hC s u hu hf⟩
  · rcases Nat.eq_zero_or_pos p with rfl | hp1
    · obtain ⟨C, hC⟩ := fin (fun s => FaceBr.se₂ 6 (Q s)) ![6 - 3, 6 - 4] (fun _ => rfl)
        (fun j => by fin_cases j <;> simp)
        (fun _ => FaceBr.meas_se₂) (FaceShape.unifLip_coefJ_se₂ S hK' hρ₁ 6 hQ)
        (fun s => FaceBr.rep_se₂ (hd1 rfl s) (hq0 s) le_rfl)
      exact ⟨C, fun s u hu hf => by simpa [faceIdVal] using hC s u hu hf⟩
    · obtain ⟨C, hC⟩ := fin (fun s => FaceBr.vtx₂ 6 (Q s)) ![6 - 3, 6 - 4] (fun _ => rfl)
        (fun j => by fin_cases j <;> simp)
        (fun _ => FaceBr.meas_vtx₂) (FaceShape.unifLip_coefJ_vtx₂ S hK' hρ₁ 6 hQ)
        (fun s => FaceBr.rep_vtx₂3 (hd s) (hq0 s) (by omega))
      have hp0 : p ≠ 0 := by omega
      exact ⟨C, fun s u hu hf => by simpa [faceIdVal, hp0] using hC s u hu hf⟩

/-- **The loop-`1` face limit of a sorted piece is its face value**: under the hypotheses of
`faceId_face_rate_sort` at one momentum, with the integrand integrable at every `u ≥ 1`,
`limUnder atTop (u ↦ u ∫_{faceSum ≤ ρ₀} pieceF) = faceIdVal`. -/
theorem faceId_face_limUnder_sort {p q : ℕ} (α : Fin (p + 1 + 1 + q + 1) → Fin 2 → ℝ)
    {e : Equiv.Perm (Fin (p + 1 + 1 + q + 1))} (hS : FaceSort p q α e)
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (pp : Fin (p + 1 + 1 + q + 1) → Fin 4 → ℝ) (M : Fin (p + 1 + 1 + q + 1) → ℝ)
    (n : ℕ) (Q : LoopQuartic) {BQ : ℝ} (hQ : LQBdd (fun _ : Unit => Q) BQ)
    (hd : LoopDegLe 1 3 Q) (hd1 : p = 0 → LoopDegLe 1 1 Q) (hn : n = 7 ∨ (n = 6 ∧ Q.quart = 0))
    {ρ₀ c₁ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (hc₁ : 0 < c₁)
    (hV : ∀ w : Fin (p + 1 + 1 + q + 1) → ℝ, (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w (FaceSort.gam e) ≤ ρ₀ → c₁ ≤ symanzikV α pp M w)
    (hint : ∀ u : ℝ, 1 ≤ u →
      IntegrableOn (fun x => pieceF n Q α pp M (FaceSort.gam e) u (simplexPoint x))
        (simplexSet (p + 1 + 1 + q))) :
    limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet (p + 1 + 1 + q),
        {w | faceSum α w ≤ ρ₀}.indicator (pieceF n Q α pp M (FaceSort.gam e) u)
          (simplexPoint x)) = faceIdVal n (hS.shape pp M) Q := by
  obtain ⟨C, hC⟩ := faceId_face_rate_sort α hS hrow (fun _ : Unit => pp) (fun _ => M) n
    (fun _ => Q) hQ (fun _ => hd) (fun h _ => hd1 h)
    (by rcases hn with h | ⟨h, h'⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, fun _ => h'⟩) hρ₀ hρ₁ hc₁
    (fun _ l => Finset.single_le_sum (f := fun l => ‖pp l‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ l))
    (fun _ l => Finset.single_le_sum (f := fun l => |M l|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ l))
    (fun _ => hV)
  exact faceId_eq_limUnder_of_rate fun u hu =>
    hC () u (one_pos.trans_le hu) (hint u hu)

end QED.GradedProof.RPi4

end
