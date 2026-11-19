/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0NsTerm
public import QED.GradedProof.X0BlockGen

/-!
# (X₀): (T₉′) of a two-loop contraction whose closed loop shares lines with the other loop

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), part B of
`TwoLoopClosedGoal`. Let `C` be a contraction of `gauge` vertices with two loops and one
closed fermion loop `zOf C` passing `NsCrit C`. For each index term, `M_f^p W(ℓ)` times the
loop denominators (`prod_nsFac`, `p ∈ {0, 2, 4}`) is summed over the flavours by
`jointEnergyFirstIntegrable_blockSumGen`; its expansion terms are integrands of
`jointEnergyFirstIntegrable_lines_pad`, with the multiplicities checked by `PatOK`
(`jointEnergyFirstIntegrable_nsTerm`). Summing over the indices gives (X₀) for `C`
(`jointEnergyFirstIntegrable_nsClosed`), at any masses.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0

open QED.Graded
open QED.WickModel
open QED.TwoLoop.Bridge (propDenom)

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind} {F : Type} {C : Contraction 1 nA κ}

/-- **The expansion terms**: (T₉′) of `z W(ℓ) ∏_{loop} ∏_{M ∈ G x} D_M(k_x)⁻¹` when the
multiplicities pass `PadCrit`. -/
theorem jointEnergyFirstIntegrable_nsLines (P : Params) (Φ : Lepton.Flavors F) (hε : 0 < P.ε)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (G : ZL C → List ℝ)
    (g : Line C → ℕ) (hG : ∀ x, (G x).length = 1 + g x.1)
    (hg : ∀ l, isZL C l = false → g l = 0)
    (hcrit : PadCrit (rowOf C) (fun l => baseN C l + g l) (baseD C (nsE α β C))) (z : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      z * ((∏ l, (nsNum P Φ C α β lor l (lineMomentum₂ C pOut pIn kIn ℓ l) *
        dProd P.ε (nsMs P Φ C l) (lineMomentum₂ C pOut pIn kIn ℓ l))) *
        ∏ x : ZL C, dProd P.ε (G x) (lineMomentum₂ C pOut pIn kIn ℓ x.1)) := by
  classical
  rw [← length_nsMs_zExt P Φ G g hG hg] at hcrit
  have h := jointEnergyFirstIntegrable_lines_pad (rowOf C) (extPart C pOut pIn kIn)
    (fun l => nsMs P Φ C l ++ zExt G l) (baseD C (nsE α β C)) (nsNum P Φ C α β lor)
    (affPoly_nsNum P Φ α β lor) hcrit hε z
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  rw [← prod_nsNum_zExt P Φ α β lor G (fun l => lineMomentum₂ C pOut pIn kIn ℓ l)]
  simp only [lineMomentum₂_eq_rowMom]
  rfl

theorem dProd_cons (ε M : ℝ) (ms : List ℝ) (k : Fin 4 → ℝ) :
    dProd ε (M :: ms) k = (propDenom M ε k)⁻¹ * dProd ε ms k := by
  simp [dProd]

theorem dProd_nil (ε : ℝ) (k : Fin 4 → ℝ) : dProd ε [] k = 1 := by
  simp [dProd]

theorem prod_dProd_one (ε : ℝ) (k : ZL C → Fin 4 → ℝ) (l : ZL C) (ms : List ℝ) :
    ∏ x : ZL C, dProd ε (0 :: (if x = l then ms else [])) (k x) =
      (∏ x : ZL C, (propDenom 0 ε (k x))⁻¹) * dProd ε ms (k l) := by
  classical
  have h : ∀ x, dProd ε (0 :: (if x = l then ms else [])) (k x) =
      (propDenom 0 ε (k x))⁻¹ * (if x = l then dProd ε ms (k x) else 1) := fun x => by
    rw [dProd_cons]
    split_ifs <;> simp [dProd_nil]
  simp only [h, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem prod_dProd_set (ε M : ℝ) (k : ZL C → Fin 4 → ℝ) (S : Finset (ZL C)) :
    ∏ x : ZL C, dProd ε (0 :: (if x ∈ S then [M] else [])) (k x) =
      (∏ x : ZL C, (propDenom 0 ε (k x))⁻¹) * ∏ x ∈ S, (propDenom M ε (k x))⁻¹ := by
  classical
  have h : ∀ x, dProd ε (0 :: (if x ∈ S then [M] else [])) (k x) =
      (propDenom 0 ε (k x))⁻¹ * (if x ∈ S then (propDenom M ε (k x))⁻¹ else 1) := fun x => by
    rw [dProd_cons]
    split_ifs <;> simp [dProd_cons, dProd_nil]
  simp only [h, Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]

variable [Fintype F] [DecidableEq F]

/-- **One index term of a non-separated contraction**, summed over the flavours of the closed
loop. -/
theorem jointEnergyFirstIntegrable_nsTerm (P : Params) (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hε : 0 < P.ε) (hκ : ∀ t, κ t = .gauge) (hZ : ∀ x, isZ (zOf C) (C.1.1 x) = isZ (zOf C) x)
    (hr : (zSet C).card ≤ 4) (hpat : AllPatOK C) (pOut pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) (z : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      ∑ f, (Φ.coeff f : ℂ) * (z * ampTerm P Φ D C (closedFlavoring Φ (zOf C) f) pIn kIn
        (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ α β lor) := by
  classical
  simp only [ampTerm_ns P Φ D hκ]
  set K := nsConst P C αOut βIn μ α β lor with hK
  by_cases hΓ : ∏ t, Wick.vertexFactor P.e 0 0 0 0 0 α β lor 0 0 t = 0
  · have h0 : K = 0 := by rw [hK, nsConst, hΓ, mul_zero]
    simp only [h0, zero_mul, mul_zero, Finset.sum_const_zero]
    exact jointEnergyFirstIntegrable_zero_fun'
  have hd := not_blk_of_prod_ne_zero P.e hκ α β lor hΓ
  obtain ⟨j, hj⟩ := even_nsP α β hZ hd
  have hcard := card_zSet_eq (C := C) α β
  have hpE : (zSet C).card - (nsE α β C).card = nsP α β C := by omega
  have hpat' := hpat (nsE α β C) (Finset.mem_powerset.mpr (Finset.filter_subset _ _))
  unfold PatOK at hpat'
  rw [hpE] at hpat'
  obtain ⟨h4, h2, h0⟩ := hpat'
  have multi : ∀ i, (i = 0 ∨ i = 1) → j = i → MultiOK C (nsE α β C) := by
    rintro i (rfl | rfl) rfl
    · exact h0 (by omega)
    · exact (h2 (by omega)).2
  set k : ZL C → (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ :=
    fun x ℓ => lineMomentum₂ C pOut pIn kIn ℓ x.1 with hk
  set W : (Fin 2 → Fin 4 → ℝ) → ℂ := fun ℓ =>
    ∏ l, (nsNum P Φ C α β lor l (lineMomentum₂ C pOut pIn kIn ℓ l) *
      dProd P.ε (nsMs P Φ C l) (lineMomentum₂ C pOut pIn kIn ℓ l)) with hW
  set E : ℕ → F → (Fin 2 → Fin 4 → ℝ) → ℂ := fun i _ ℓ => if j = i then z * K * W ℓ else 0
    with hE
  have hL := fun G g hG hg hcrit z' =>
    jointEnergyFirstIntegrable_nsLines P Φ hε α β lor pOut pIn kIn (C := C) G g hG hg hcrit z'
  have hzero : ∀ i, ¬ j = i → ∀ X : (Fin 2 → Fin 4 → ℝ) → ℂ, ∀ b (z' : ℂ),
      QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ => z' * (E i b ℓ * X ℓ) := by
    intro i hi X b z'
    simp only [hE, hi, ↓reduceIte, zero_mul, mul_zero]
    exact jointEnergyFirstIntegrable_zero_fun'
  have hmemZ : ∀ x : ZL C, x.1 ∈ zSet C := fun x => by
    simp only [zSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact x.2
  have hgZ : ∀ (x : ZL C) (c : ℕ) (l : Line C), isZL C l = false →
      (if l = x.1 then c else 0) = 0 := fun x c l hl => by
    refine ite_eq_right_iff.mpr fun h => ?_
    rw [h, x.2] at hl
    exact Bool.noConfusion hl
  -- two extra lines on one loop line
  have key₀₁ : ∀ i, (j = i → MultiOK C (nsE α β C)) → ∀ b (M : ℝ) (z' : ℂ) (l : ZL C),
      QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
        z' * (E i b ℓ * ((∏ l', (propDenom 0 P.ε (k l' ℓ))⁻¹) * (propDenom 0 P.ε (k l ℓ))⁻¹ *
          (propDenom M P.ε (k l ℓ))⁻¹)) := by
    intro i hi b M z' l
    by_cases hji : j = i
    · have h := hL (fun x => 0 :: (if x = l then [0, M] else []))
        (fun l' => if l' = l.1 then 2 else 0)
        (fun x => by
          by_cases hx : x = l
          · subst hx
            simp
          · have hx' : x.1 ≠ l.1 := fun h => hx (Subtype.ext h)
            simp [hx, hx'])
        (hgZ l 2) ((hi hji).1 l.1 (hmemZ l)) (z' * (z * K))
      refine (congrArg _ (funext fun ℓ => ?_)).mp h
      rw [prod_dProd_one P.ε (fun x => k x ℓ) l [0, M]]
      simp only [hE, hji, ↓reduceIte, dProd_cons, dProd_nil, mul_one, hk]
      ring
    · exact hzero i hji _ b z'
  -- one extra line on each loop line of `S`
  have keyS : ∀ i, (j = i → MultiOK C (nsE α β C)) → ∀ b (M : ℝ) (z' : ℂ) (S : Finset (ZL C)),
      2 ≤ S.card → QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
        z' * (E i b ℓ * ((∏ l', (propDenom 0 P.ε (k l' ℓ))⁻¹) *
          ∏ l ∈ S, (propDenom M P.ε (k l ℓ))⁻¹)) := by
    intro i hi b M z' S hS
    by_cases hji : j = i
    · set S' := S.map (Function.Embedding.subtype fun l => isZL C l = true) with hS'
      have hmem : ∀ x : ZL C, x.1 ∈ S' ↔ x ∈ S := fun x =>
        Finset.mem_map' (Function.Embedding.subtype fun l => isZL C l = true)
      have h := hL (fun x => 0 :: (if x ∈ S then [M] else []))
        (fun l' => if l' ∈ S' then 1 else 0)
        (fun x => by by_cases hx : x ∈ S <;> simp [hx, hmem])
        (fun l' hl' => by
          refine ite_eq_right_iff.mpr fun hm => ?_
          obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hm
          simp only [Function.Embedding.coe_subtype, x.2, Bool.true_eq_false] at hl')
        ((hi hji).2 S' (Finset.mem_powerset.mpr fun l hl => by
            obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hl
            exact hmemZ x)
          (by rw [hS', Finset.card_map]; exact hS)) (z' * (z * K))
      refine (congrArg _ (funext fun ℓ => ?_)).mp h
      rw [prod_dProd_set P.ε M (fun x => k x ℓ) S]
      simp only [hE, hji, ↓reduceIte, hk]
      ring
    · exact hzero i hji _ b z'
  have h := jointEnergyFirstIntegrable_blockSumGen Φ rep hrep hPV₁ hPV₂ k hε (E 0) (E 1) (E 2)
    (fun b M z' => by
      by_cases hj2 : j = 2
      · have h := hL (fun _ => [M]) (fun _ => 0) (fun _ => rfl) (fun _ _ => rfl)
          (by simp only [add_zero]; exact h4 (by omega)) (z' * (z * K))
        refine (congrArg _ (funext fun ℓ => ?_)).mp h
        simp only [hE, hj2, ↓reduceIte, dProd_cons, dProd_nil, mul_one, hk]
        ring
      · exact hzero 2 hj2 _ b z')
    (fun b z' l => by
      by_cases hj1 : j = 1
      · have h := hL (fun x => 0 :: (if x = l then [0] else []))
          (fun l' => if l' = l.1 then 1 else 0)
          (fun x => by
            by_cases hx : x = l
            · subst hx
              simp
            · have hx' : x.1 ≠ l.1 := fun h => hx (Subtype.ext h)
              simp [hx, hx'])
          (hgZ l 1) ((h2 (by omega)).1 l.1 (hmemZ l)) (z' * (z * K))
        refine (congrArg _ (funext fun ℓ => ?_)).mp h
        rw [prod_dProd_one P.ε (fun x => k x ℓ) l [0]]
        simp only [hE, hj1, ↓reduceIte, dProd_cons, dProd_nil, mul_one, hk]
        ring
      · exact hzero 1 hj1 _ b z')
    (fun E' hE' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hE'
      rcases hE' with rfl | rfl
      · exact key₀₁ 0 (multi 0 (Or.inl rfl))
      · exact key₀₁ 1 (multi 1 (Or.inr rfl)))
    (fun E' hE' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hE'
      rcases hE' with rfl | rfl
      · exact keyS 0 (multi 0 (Or.inl rfl))
      · exact keyS 1 (multi 1 (Or.inr rfl)))
  have hj2 : j ≤ 2 := by omega
  refine (congrArg _ (funext fun ℓ => Finset.sum_congr rfl fun f _ => ?_)).mp h
  rw [prod_nsFac P Φ hε.ne' α β lor (Φ.mass f) (fun l => lineMomentum₂ C pOut pIn kIn ℓ l), hj]
  interval_cases j <;> simp +decide only [hE, hk, hW, ↓reduceIte] <;> ring

/-- **(X₀) for a two-loop contraction with one closed loop sharing lines with the other
loop**, at any masses. -/
theorem jointEnergyFirstIntegrable_nsClosed (P : Params) (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hε : 0 < P.ε) (hκ : ∀ t, κ t = .gauge) (C : Contraction 1 1 κ) (hL : loopCount C = 2)
    (hC : ClosedShape C (zOf C)) (hr : (zSet C).card ≤ 4) (hpat : AllPatOK C)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C)
      (integrand P Φ D C 0 pOut pIn kIn αOut βIn μ) := by
  unfold integrand
  rw [hL]
  simp only [regulatedAmplitude_eq_closed Φ P D hC, contractionAmplitude_zero_eq]
  have h := jointEnergyFirstIntegrable_sum' Finset.univ fun α _ =>
    jointEnergyFirstIntegrable_sum' Finset.univ fun β _ =>
      jointEnergyFirstIntegrable_sum' Finset.univ fun lor _ =>
        jointEnergyFirstIntegrable_nsTerm P Φ D rep hrep hPV₁ hPV₂ hε hκ hC.inv hr hpat pOut pIn
          kIn αOut βIn μ α β lor (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  rw [sum_comm_four, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => ?_
  ring

end QED.GradedProof.X0

end
