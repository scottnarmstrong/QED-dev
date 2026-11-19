/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0ClosedTerm
public import QED.GradedProof.X0OneCtCrit

/-!
# (X₀): (T₉′) of a one-loop contraction whose loop is a closed fermion loop

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57). Let `C` have one
loop, a closed fermion loop `Z` (`ClosedShape`), with the loop momentum on exactly the lines of
`Z` (`c_l ≠ 0` iff `l` is a fermion line of `Z`). Let `r` be the number of loop lines and
`d = r + ∑_{s ∈ Z} vDeg s` the numerator degree. If `d ≤ 4` and `d < 2 r`, the integrand of
(X₀) at the zero grading satisfies (T₉′), under the block hypotheses of (X₀), at any masses
(`jointEnergyFirstIntegrable_closedOne`).

## Proof
Flavour sum (`regulatedAmplitude_eq_closed`), then the index terms (`ampTerm`). In one index
term, the vertices and lines off the loop are constant and of the open-line flavour; the loop
entries are chirality-pure (`vertexFactor_pure`, `electronNumerator_eq_ite`) with sign product
`1` (`prod_sgn_closed`), and the counterterm data of flavour `f` equal those of `rep f`;
`jointEnergyFirstIntegrable_entrySum` applies.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0

open QED.Graded
open QED.WickModel
open QED.TwoLoop.Bridge (propDenom electronNumerator electronPropagator_apply)
open QED.TwoLoop.FurryIntegrable (sgn)

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind} {F : Type} [Fintype F] [DecidableEq F]
  {Z : Wick.FermionVertex κ → Prop} [DecidablePred Z] {C : Contraction 1 nA κ}

/-- A product split along a predicate. -/
theorem prod_split_pred {T : Type*} [Fintype T] (p : T → Prop) [DecidablePred p] (G : T → ℂ) :
    ∏ x, G x = (∏ x : {x // p x}, G x.1) * ∏ x, (if p x then 1 else G x) := by
  rw [← prod_ite_one_eq_subtype p G, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  split_ifs <;> simp

theorem psiCoeff_of_Z (hZ : ∀ x, isZ Z (C.1.1 x) = isZ Z x) (c : Line C → ℤ)
    {s : Wick.FermionVertex κ} (hs : Z s) :
    psiCoeff c s = c (.inl ⟨s, isRight_of_Z hZ hs⟩) := by
  unfold psiCoeff
  split
  next i h =>
    have := isRight_of_Z hZ hs
    rw [h] at this
    exact absurd this (by simp)
  next => rfl

theorem vDeg_eq_zero_of_not_loop (c : Line C → ℤ)
    (hcf : ∀ f : FermionLine C, c (.inl f) ≠ 0 ↔ Z f.1) (hcg : ∀ g : PhotonLine C, c (.inr g) = 0)
    {t : Fin N} (ht : ¬ isLoopT Z t = true) : vDeg c t = 0 := by
  unfold vDeg
  split_ifs with h1 h2 h3 h4
  · rfl
  · exfalso
    apply h2
    unfold psiCoeff
    split
    · rfl
    · by_contra hne
      exact ht ((isLoopT_iff t).2 ⟨by rw [h1]; decide, (hcf _).1 hne⟩)
  · rfl
  · exfalso
    apply h4
    simp [slotCoeff, hcg]
  · rfl

omit [Fintype F] [DecidableEq F] in
theorem flOf_closed_of_Z (Φ : Lepton.Flavors F) (f : F) (s : {s : Wick.FermionVertex κ // Z s}) :
    flOf Φ (closedFlavoring Φ Z f) s.1.1 = f := by
  simp [flOf, s.1.2, closedFlavoring, s.2]

omit [Fintype F] [DecidableEq F] in
theorem flOf_closed_of_not (Φ : Lepton.Flavors F) (f : F) {t : Fin N}
    (ht : ¬ isLoopT Z t = true) : flOf Φ (closedFlavoring Φ Z f) t = Φ.openLine := by
  unfold flOf closedFlavoring
  split_ifs with h1 h2
  · rfl
  · exact absurd ((isLoopT_iff t).2 ⟨h1, h2⟩) ht
  · rfl

/-- **One index term of a closed one-loop contraction, summed over the flavours.** -/
theorem jointEnergyFirstIntegrable_closedTerm (P : Params) (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0) (hε : 0 < P.ε)
    (hZ : ∀ x, isZ Z (C.1.1 x) = isZ Z x) (c : Line C → ℤ) (ext : Line C → Fin 4 → ℝ)
    (hcf : ∀ f : FermionLine C, c (.inl f) ≠ 0 ↔ Z f.1) (hcg : ∀ g : PhotonLine C, c (.inr g) = 0)
    (hd : Fintype.card (ZLine C Z) + ∑ s : {s // Z s}, vDeg c s.1.1 ≤ 4)
    (hr : Fintype.card (ZLine C Z) + ∑ s : {s // Z s}, vDeg c s.1.1 <
      2 * Fintype.card (ZLine C Z))
    (pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin nA → Fin 4) (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
    (z : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ =>
      ∑ f, (Φ.coeff f : ℂ) * (z * ampTerm P Φ D C (closedFlavoring Φ Z f) pIn kIn
        (oneMom c ext (ℓ 0)) αOut βIn μ α β lor) := by
  classical
  -- the entries
  set a : {s // Z s} ⊕ ZLine C Z → Fin 4 := Sum.elim (fun s => α s.1) fun l => β l.1.1
  set b : {s // Z s} ⊕ ZLine C Z → Fin 4 := Sum.elim (fun s => β s.1) fun l => α l.1.tail
  set w : {s // Z s} ⊕ ZLine C Z → ℕ := Sum.elim (fun s => vDeg c s.1.1) fun _ => 1
  set u : F → {s // Z s} ⊕ ZLine C Z → ℂ := fun x => Sum.elim
    (fun s => if κ s.1.1 = .fermionCt then
      -I * ((P.e ^ 2 * D.dm x 0 : ℝ) : ℂ) * (1 : Matrix (Fin 4) (Fin 4) ℂ) (α s.1) (β s.1)
      else 0)
    fun l => (1 / I) * (1 : Matrix (Fin 4) (Fin 4) ℂ) (β l.1.1) (α l.1.tail)
  set v : F → {s // Z s} ⊕ ZLine C Z → (Fin 4 → ℝ) → ℂ := fun x => Sum.elim
    (fun s k => Wick.vertexFactor P.e (P.e ^ 2 * D.d₁ x 0) (P.e ^ 2 * D.d₂ x 0) 0
      (P.e ^ 2 * D.d₃ 0) 0 α β lor (psiMomentum₂ C pIn (oneMom c ext k))
      (photonMomentum₂ C kIn (oneMom c ext k)) s.1.1)
    fun l k => (1 / I) * electronNumerator 0 ((c (.inl l.1) : ℝ) • k + ext (.inl l.1))
      (β l.1.1) (α l.1.tail)
  set ind : ℂ := if (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
      (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
      (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) then 1 else 0
  set K : (Fin 4 → ℝ) → ℂ := fun k => z * ind *
    (∏ t, if isLoopT Z t = true then 1 else vf0 P D Φ.openLine (Φ.mass Φ.openLine) α β lor
      (psiMomentum₂ C pIn (oneMom c ext k)) (photonMomentum₂ C kIn (oneMom c ext k)) t) *
    (∏ f : FermionLine C, if Z f.1 then 1 else (1 / I) * QED.OneLoop.electronPropagator
      (Φ.mass Φ.openLine) P.ε (oneMom c ext k (.inl f)) (β f.1) (α f.tail)) *
    ∏ g' : PhotonLine C, (1 / I) *
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (oneMom c ext k (.inr g')) (lor g'.1)
        (lor g'.head)
  -- hypotheses of `jointEnergyFirstIntegrable_entrySum`
  have hcL : ∀ l : ZLine C Z, ((c (.inl l.1) : ℝ)) ≠ 0 :=
    fun l => Int.cast_ne_zero.mpr ((hcf l.1).mpr l.2)
  have hpar : Even (Finset.univ.filter fun e => blk (a e) = blk (b e)).card := by
    refine even_card_blk a b ?_ ?_
    · rw [Fintype.prod_sum_type]
      exact prod_sgn_closed hZ α β
    · rw [Fintype.card_sum, card_zLine hZ]
      exact ⟨_, rfl⟩
  have hv : ∀ x e, AffPoly (w e) (v x e) := fun x e => by
    rcases e with s | l
    · exact affPoly_vertexFactor _ _ _ _ _ _ α β lor c ext pIn kIn s.1.1
    · exact (AffPoly.comp_affine (electronNumerator_affine 0 _ _) _ _).const_mul _
  have hu : ∀ x e, w e = 0 → u x e = 0 := fun x e he => by
    rcases e with s | l
    · simp only [w, Sum.elim_inl] at he
      simp only [u, Sum.elim_inl]
      split_ifs with hf
      · exfalso
        unfold vDeg at he
        simp only [hf, ↓reduceDIte] at he
        rw [psiCoeff_of_Z hZ c s.2] at he
        simp only [ite_eq_left_iff] at he
        exact (hcf _).2 s.2 (by simpa using he)
      · rfl
    · simp [w] at he
  have hK : AffPoly 0 K := by
    have h1 : AffPoly 0 fun k => ∏ t, if isLoopT Z t = true then 1 else vf0 P D Φ.openLine
        (Φ.mass Φ.openLine) α β lor (psiMomentum₂ C pIn (oneMom c ext k))
        (photonMomentum₂ C kIn (oneMom c ext k)) t := by
      have := AffPoly.prod Finset.univ (fun _ => 0) (N := fun t k => if isLoopT Z t = true then 1
        else vf0 P D Φ.openLine (Φ.mass Φ.openLine) α β lor
          (psiMomentum₂ C pIn (oneMom c ext k)) (photonMomentum₂ C kIn (oneMom c ext k)) t)
        fun t _ => by
          by_cases ht : isLoopT Z t = true
          · simp only [ht, ite_true]; exact AffPoly.const _
          · simp only [ht]
            have h := affPoly_vertexFactor (C := C) P.e (P.e ^ 2 * D.d₁ Φ.openLine 0)
              (P.e ^ 2 * D.d₂ Φ.openLine 0) (P.e ^ 2 * D.dm Φ.openLine 0) (P.e ^ 2 * D.d₃ 0)
              (Φ.mass Φ.openLine) α β lor c ext pIn kIn t
            rw [vDeg_eq_zero_of_not_loop c hcf hcg ht] at h
            exact h
      simpa using this
    have h2 : AffPoly 0 fun k => ∏ f : FermionLine C, if Z f.1 then 1 else (1 / I) *
        QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε (oneMom c ext k (.inl f))
          (β f.1) (α f.tail) := by
      have := AffPoly.prod Finset.univ (fun _ => 0) (N := fun f k => if Z f.1 then 1 else
        (1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε
          (oneMom c ext k (.inl f)) (β f.1) (α f.tail)) fun f _ => by
          by_cases hf : Z f.1
          · simp only [hf, ite_true]; exact AffPoly.const _
          · have h0 : c (.inl f) = 0 := by
              by_contra h; exact hf ((hcf f).1 h)
            simp only [hf, ite_false, oneMom, h0, Int.cast_zero, zero_smul, zero_add]
            exact AffPoly.const _
      simpa using this
    have h3 : AffPoly 0 fun k => ∏ g' : PhotonLine C, (1 / I) *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (oneMom c ext k (.inr g')) (lor g'.1)
          (lor g'.head) := by
      simp only [oneMom, hcg, Int.cast_zero, zero_smul, zero_add]
      exact AffPoly.const _
    have := ((AffPoly.const (z * ind)).mul h1).mul h2 |>.mul h3
    simpa [K] using this
  have hsum : ∑ e, w e = Fintype.card (ZLine C Z) + ∑ s : {s // Z s}, vDeg c s.1.1 := by
    simp only [w, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, mul_one]
    ring
  have hmain := jointEnergyFirstIntegrable_entrySum Φ rep hrep hPV₁ hPV₂
    (fun l : ZLine C Z => (c (.inl l.1) : ℝ)) hcL (fun l => ext (.inl l.1)) hε a b hpar w u v
    hv hu K hK (by rw [hsum]; exact hd) (by rw [hsum]; exact hr)
  refine (congrArg _ (funext fun ℓ => Finset.sum_congr rfl fun f _ => ?_)).mp hmain
  congr 1
  -- one flavour
  set M := Φ.mass f
  have hV : ∀ s : {s : Wick.FermionVertex κ // Z s},
      vf0 P D (flOf Φ (closedFlavoring Φ Z f) s.1.1)
        (Φ.mass (flOf Φ (closedFlavoring Φ Z f) s.1.1)) α β lor
        (psiMomentum₂ C pIn (oneMom c ext (ℓ 0))) (photonMomentum₂ C kIn (oneMom c ext (ℓ 0)))
        s.1.1 = if blk (a (.inl s)) = blk (b (.inl s)) then (M : ℂ) * u (rep f) (.inl s)
          else v (rep f) (.inl s) (ℓ 0) := fun s => by
    obtain ⟨h1, h2, h3⟩ := hD f
    rw [flOf_closed_of_Z]
    simp only [vf0, h1, h2, h3, a, b, u, v, Sum.elim_inl]
    exact vertexFactor_pure _ _ _ _ _ _ α β lor _ _ s.1
  have hVn : ∀ t, (if isLoopT Z t = true then 1 else
      vf0 P D (flOf Φ (closedFlavoring Φ Z f) t) (Φ.mass (flOf Φ (closedFlavoring Φ Z f) t))
        α β lor (psiMomentum₂ C pIn (oneMom c ext (ℓ 0)))
        (photonMomentum₂ C kIn (oneMom c ext (ℓ 0))) t) =
      (if isLoopT Z t = true then 1 else vf0 P D Φ.openLine (Φ.mass Φ.openLine) α β lor
        (psiMomentum₂ C pIn (oneMom c ext (ℓ 0)))
        (photonMomentum₂ C kIn (oneMom c ext (ℓ 0))) t) := fun t => by
    split_ifs with ht
    · rfl
    · rw [flOf_closed_of_not Φ f ht]
  have hL : ∀ l : ZLine C Z, (1 / I) * QED.OneLoop.electronPropagator
      (Φ.mass (closedFlavoring Φ Z f l.1.1)) P.ε (oneMom c ext (ℓ 0) (.inl l.1)) (β l.1.1)
        (α l.1.tail) =
      (if blk (a (.inr l)) = blk (b (.inr l)) then (M : ℂ) * u (rep f) (.inr l)
        else v (rep f) (.inr l) (ℓ 0)) *
      (propDenom M P.ε ((c (.inl l.1) : ℝ) • ℓ 0 + ext (.inl l.1)))⁻¹ := fun l => by
    simp only [closedFlavoring, l.2, ite_true, electronPropagator_apply, oneMom, a, b, u, v,
      Sum.elim_inr, M]
    rw [electronNumerator_eq_ite, electronNumerator_eq_ite]
    split_ifs <;> ring
  have hLn : ∀ fl : FermionLine C, (if Z fl.1 then 1 else (1 / I) *
      QED.OneLoop.electronPropagator (Φ.mass (closedFlavoring Φ Z f fl.1)) P.ε
        (oneMom c ext (ℓ 0) (.inl fl)) (β fl.1) (α fl.tail)) =
      (if Z fl.1 then 1 else (1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine)
        P.ε (oneMom c ext (ℓ 0) (.inl fl)) (β fl.1) (α fl.tail)) := fun fl => by
    split_ifs with h
    · rfl
    · simp only [closedFlavoring, h, ite_false]
  unfold ampTerm
  rw [prod_split_loopT (Z := Z), prod_split_pred (fun fl : FermionLine C => Z fl.1)]
  simp only [hV, hVn, hL, hLn, Finset.prod_mul_distrib, Fintype.prod_sum_type, K]
  ring

omit [DecidableEq F] in
/-- Moving the flavour sum inside three index sums. -/
theorem sum_comm_four {A B B' : Type*} [Fintype A] [Fintype B] [Fintype B']
    (X : F → A → B → B' → ℂ) :
    ∑ a, ∑ b, ∑ b', ∑ f, X f a b b' = ∑ f, ∑ a, ∑ b, ∑ b', X f a b b' := by
  have h1 : ∀ a b, ∑ b', ∑ f, X f a b b' = ∑ f, ∑ b', X f a b b' := fun _ _ => Finset.sum_comm
  have h2 : ∀ a, ∑ b, ∑ f, ∑ b', X f a b b' = ∑ f, ∑ b, ∑ b', X f a b b' :=
    fun _ => Finset.sum_comm
  simp only [h1, h2]
  exact Finset.sum_comm

/-- **(X₀) for a one-loop contraction whose loop is a closed fermion loop**, at the zero
grading, any masses. -/
theorem jointEnergyFirstIntegrable_closedOne (P : Params) (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0) (hε : 0 < P.ε) (C : Contraction 1 1 κ) (hC : ClosedShape C Z)
    (hL : loopCount C = 1)
    (hcf : ∀ f : FermionLine C, loopCoeff C (.inl f) 0 ≠ 0 ↔ Z f.1)
    (hcg : ∀ g : PhotonLine C, loopCoeff C (.inr g) 0 = 0)
    (hd : Fintype.card (ZLine C Z) + ∑ s : {s // Z s}, vDeg (fun l => loopCoeff C l 0) s.1.1 ≤ 4)
    (hr : Fintype.card (ZLine C Z) + ∑ s : {s // Z s}, vDeg (fun l => loopCoeff C l 0) s.1.1 <
      2 * Fintype.card (ZLine C Z))
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C)
      (integrand P Φ D C 0 pOut pIn kIn αOut βIn μ) := by
  unfold integrand
  rw [hL]
  simp only [regulatedAmplitude_eq_closed Φ P D hC, lineMomentum₂_eq_oneMom,
    contractionAmplitude_zero_eq]
  have h := jointEnergyFirstIntegrable_sum' Finset.univ fun α _ =>
    jointEnergyFirstIntegrable_sum' Finset.univ fun β _ =>
      jointEnergyFirstIntegrable_sum' Finset.univ fun lor _ =>
        jointEnergyFirstIntegrable_closedTerm P Φ D rep hrep hPV₁ hPV₂ hD hε hC.inv
          (fun l => loopCoeff C l 0) (extPart C pOut pIn kIn) hcf hcg hd hr pIn kIn αOut βIn μ
          α β lor (((2 * Real.pi) ^ (4 * 1) : ℝ) : ℂ)⁻¹
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  rw [sum_comm_four, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => ?_
  ring

end QED.GradedProof.X0

end
