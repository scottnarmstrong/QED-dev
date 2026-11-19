/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0Denom
public import QED.TwoLoop.ClassIntegrable

/-!
# (X₀): the numerator of a two-loop contraction of `gauge` vertices

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), step X0d.4. For a
contraction of `gauge` vertices in the frozen routing (T₄) with two loop momenta, the amplitude
numerator is a polynomial of total degree at most the number of fermion lines on a loop
(`isLoopPoly_amplitudeNumerator_loop`), bounded by the line weights of those lines
(`refinedBound_amplitudeNumerator_loop`): the vertex factors do not depend on the momenta, and the
electron numerators of the fermion lines off the loops are constant.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0

open QED.WickModel QED.TwoLoop.Bridge
open QED.TwoLoop.Enumeration (lineData)
open QED.Integration.TwoLoop (castLoopMatrix lineMomentum RefinedBound)

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}

/-- The factor of a `gauge` vertex does not depend on the momenta. -/
theorem vertexFactor_eq_of_gauge (e δ₁ δ₂ δm δ₃ m : ℝ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (kψ kψ' : Wick.FermionVertex κ → Fin 4 → ℝ)
    (kA kA' : Wick.PhotonSlot κ → Fin 4 → ℝ) (t : Fin N) (h : κ t = .gauge) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ' kA' t := by
  unfold Wick.vertexFactor
  split <;> rename_i h' <;> simp_all

/-- The fermion lines off the loops carry constant momenta. -/
theorem lineMomentum₂_offLoop (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ)
    (f : {f : FermionLine C // ¬ edgeLoop (lineData C) (edgeOf (.inl f : Line C)) = true}) :
    lineMomentum₂ C pOut pIn kIn ℓ (.inl f.1) = extPart C pOut pIn kIn (.inl f.1) :=
  lineMomentum₂_eq_extPart _ _ _ _ _ (by simpa using f.2)

/-- The fermion lines on the loops, numbered by `ι`. -/
theorem lineMomentum₂_loopFermion {m : ℕ} (ι : LoopLine C ≃ Fin (m + 1))
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ)
    (f : LoopFermion C) :
    lineMomentum₂ C pOut pIn kIn ℓ (.inl f.1) =
      lineMomentum (castLoopMatrix (pMat ι)) (pVec ι pOut pIn kIn) (ι f.toLoopLine) ℓ :=
  lineMomentum₂_eq_lineMomentum ι pOut pIn kIn ℓ f.toLoopLine

/-- The product of the fermion factors, split into the lines on and off the loops. -/
theorem prod_fermion_split (F : FermionLine C → ℂ) :
    ∏ f : FermionLine C, F f = (∏ f : LoopFermion C, F f.1) *
      ∏ f : {f : FermionLine C // ¬ edgeLoop (lineData C) (edgeOf (.inl f : Line C)) = true},
        F f.1 :=
  (Fintype.prod_subtype_mul_prod_subtype _ F).symm

/-- **The numerator is bounded by the line weights of the fermion lines on the loops.** -/
theorem refinedBound_amplitudeNumerator_loop (P : Params) (hκ : ∀ t, κ t = .gauge)
    (φ : Flavoring κ) {m : ℕ} (ι : LoopLine C ≃ Fin (m + 1)) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    RefinedBound (castLoopMatrix (pMat ι))
      (Finset.univ.image fun f : LoopFermion C => ι f.toLoopLine) (Fintype.card (LoopFermion C))
      fun ℓ => amplitudeNumerator P C φ pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ := by
  classical
  unfold amplitudeNumerator
  refine RefinedBound.sum _ fun α _ => RefinedBound.sum _ fun β _ =>
    RefinedBound.sum _ fun lor _ => ?_
  refine RefinedBound.const_mul _ ?_
  have hv : ∀ ℓ : Fin 2 → Fin 4 → ℝ, (∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
      (psiMomentum₂ C pIn (lineMomentum₂ C pOut pIn kIn ℓ))
      (photonMomentum₂ C kIn (lineMomentum₂ C pOut pIn kIn ℓ)) t) =
      ∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor 0 0 t := fun ℓ =>
    Finset.prod_congr rfl fun t _ => vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ _ _ t (hκ t)
  simp only [hv, prod_fermion_split, lineMomentum₂_offLoop, lineMomentum₂_loopFermion ι]
  have hprod := RefinedBound.prod (α := castLoopMatrix (pMat ι)) Finset.univ
    (fun f : LoopFermion C => ι f.toLoopLine)
    (fun a _ b _ hab => Subtype.ext (Sum.inl_injective
      (congrArg Subtype.val (ι.injective hab))))
    (g := fun f ℓ => (1 / I) * electronNumerator (P.mass (φ.1 f.1.1))
      (lineMomentum (castLoopMatrix (pMat ι)) (pVec ι pOut pIn kIn) (ι f.toLoopLine) ℓ)
      (β f.1.1) (α f.1.tail))
    fun f _ => (QED.TwoLoop.ClassIntegrable.refinedBound_electronNumerator _ _ _ _ _
      _).const_mul _
  rw [Finset.card_univ] at hprod
  have h := hprod.const_mul ((∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor 0 0 t) *
    (∏ f : {f : FermionLine C // ¬ edgeLoop (lineData C) (edgeOf (.inl f : Line C)) = true},
      (1 / I) * electronNumerator (P.mass (φ.1 f.1.1)) (extPart C pOut pIn kIn (.inl f.1))
        (β f.1.1) (α f.1.tail)) *
    ∏ g : PhotonLine C, (1 / I) *
      ((Minkowski.metric (lor g.1) (lor g.head) * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ))
  convert h using 2 with ℓ
  ring

/-- **The numerator is a polynomial of degree at most the number of fermion lines on the
loops.** -/
theorem isLoopPoly_amplitudeNumerator_loop (P : Params) (hκ : ∀ t, κ t = .gauge)
    (φ : Flavoring κ) {m : ℕ} (ι : LoopLine C ≃ Fin (m + 1)) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    IsLoopPoly 2 (Fintype.card (LoopFermion C))
      fun ℓ => amplitudeNumerator P C φ pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ := by
  classical
  unfold amplitudeNumerator
  refine IsLoopPoly.sum _ fun α _ => IsLoopPoly.sum _ fun β _ => IsLoopPoly.sum _ fun lor _ => ?_
  refine IsLoopPoly.const_mul _ ?_
  have hv : ∀ ℓ : Fin 2 → Fin 4 → ℝ, (∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
      (psiMomentum₂ C pIn (lineMomentum₂ C pOut pIn kIn ℓ))
      (photonMomentum₂ C kIn (lineMomentum₂ C pOut pIn kIn ℓ)) t) =
      ∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor 0 0 t := fun ℓ =>
    Finset.prod_congr rfl fun t _ => vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ _ _ t (hκ t)
  simp only [hv, prod_fermion_split, lineMomentum₂_offLoop, lineMomentum₂_loopFermion ι]
  have hfer := IsLoopPoly.prod (L := 2) (Finset.univ : Finset (LoopFermion C)) (fun _ => 1)
    (F := fun f ℓ => (1 / I) * electronNumerator (P.mass (φ.1 f.1.1))
      (lineMomentum (castLoopMatrix (pMat ι)) (pVec ι pOut pIn kIn) (ι f.toLoopLine) ℓ)
      (β f.1.1) (α f.1.tail))
    fun f _ => ((isLoopAffine_lineMomentum _ _ _).isLoopPoly_electronNumerator _ _ _).const_mul _
  have hcard : (∑ _f ∈ (Finset.univ : Finset (LoopFermion C)), 1) =
      Fintype.card (LoopFermion C) := by
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ]
  rw [hcard] at hfer
  have h := (((IsLoopPoly.const (L := 2) (n := 0) (∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃
    P.m α β lor 0 0 t)).mul hfer).mul (IsLoopPoly.const (L := 2) (n := 0)
      (∏ f : {f : FermionLine C // ¬ edgeLoop (lineData C) (edgeOf (.inl f : Line C)) = true},
        (1 / I) * electronNumerator (P.mass (φ.1 f.1.1)) (extPart C pOut pIn kIn (.inl f.1))
          (β f.1.1) (α f.1.tail)))).mul (IsLoopPoly.const (L := 2) (n := 0)
      (∏ g : PhotonLine C, (1 / I) *
        ((Minkowski.metric (lor g.1) (lor g.head) * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ)))
  simp only [add_zero, zero_add] at h
  convert h using 2 with ℓ
  ring

end QED.GradedProof.X0

end
