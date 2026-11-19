/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2ClassF
public import QED.TwoLoop.ClassIntegrable
public import QED.Integration.TwoLoopRefinedBoundCubic

/-!
# Two-loop self-energy graphs of four `gauge` vertices without a closed loop

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), step 2, for the classes `R` and `X`. For a one-fermion contraction of the four
`gauge` vertices `k_gggg` whose permutation is one cycle through the external slot, with two
loops and three electron lines, the class obligation reduces to explicit parametric data:

* an integer loop matrix `a` for seven lines (the three electron lines `0, 1, 2` and the two
  Pauli–Villars photon pairs `3, 4` and `5, 6`) satisfying the decidable criterion
  `IntNoSubdivergenceRefined 2 {0, 1, 2} a`;
* the frozen electron-line momenta (T₄) as line momenta of the data, and the amplitude
  denominators as the product of the seven line denominators.

The numerator is a polynomial of degree at most three (`isLoopPoly_amplitudeNumerator_gggg`)
bounded by the line weights of the electron lines (`refinedBound_amplitudeNumerator_gggg`), and
the cubic Fubini theorem
`QED.Integration.TwoLoop.jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_cubic`
(seven propagators) gives (T₉′): `jointEnergyFirstIntegrable_gggg`.
-/

@[expose] public section

open Complex

namespace QED.Integration.TwoLoop.LoopQuartic

theorem quart_ofList (l : List LoopIndex) (hl : l.length ≤ 3) : (ofList l).quart = 0 := by
  match l, hl with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl
  | _ :: _ :: _ :: _ :: _, h => simp at h; omega

end QED.Integration.TwoLoop.LoopQuartic

namespace QED.GradedProof.SE2

open QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.Insertion
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix RefinedBound LoopQuartic
  IntNoSubdivergenceRefined noSubdivergenceRefined_castLoopMatrix_iff LoopIndex)

/-- **A polynomial of total degree at most three is a `LoopQuartic` without quartic part.** -/
theorem IsLoopPoly.exists_loopQuartic_cubic {F : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (h : IsLoopPoly 2 3 F) : ∃ P : LoopQuartic, P.quart = 0 ∧ P.eval = F := by
  classical
  obtain ⟨Q, hQ, hF⟩ := h
  have key : ∀ s : Finset (LoopIndex →₀ ℕ), s ⊆ Q.support → ∃ P : LoopQuartic, P.quart = 0 ∧
      ∀ X, P.evalC X = ∑ d ∈ s, Q.coeff d * ∏ i ∈ d.support, X i ^ d i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      exact fun _ => ⟨LoopQuartic.zero, rfl, fun X => by simp [LoopQuartic.evalC_zero]⟩
    | insert d s hd ih =>
      intro hs
      obtain ⟨P, hPq, hP⟩ := ih ((Finset.subset_insert d s).trans hs)
      have hdeg : d.toMultiset.toList.length ≤ 3 := by
        rw [Multiset.length_toList, Finsupp.card_toMultiset]
        exact (MvPolynomial.le_totalDegree (hs (Finset.mem_insert_self d s))).trans hQ
      refine ⟨(LoopQuartic.smul (Q.coeff d) (LoopQuartic.ofList d.toMultiset.toList)).add P,
        ?_, fun X => ?_⟩
      · have h0 := LoopQuartic.quart_ofList _ hdeg
        simp only [LoopQuartic.add, LoopQuartic.smul, h0, hPq, Pi.zero_apply, mul_zero]
        funext a b c d
        simp
      rw [LoopQuartic.evalC_add, LoopQuartic.evalC_smul, LoopQuartic.evalC_ofList _ (by omega),
        prod_map_toList_toMultiset, hP, Finset.sum_insert hd]
  obtain ⟨P, hPq, hP⟩ := key Q.support subset_rfl
  refine ⟨P, hPq, funext fun ℓ => ?_⟩
  rw [hF ℓ, MvPolynomial.eval_eq, LoopQuartic.eval, hP]
  rfl

/-- The vertex factor of the four `gauge` vertices does not depend on the momenta. -/
theorem vertexFactor_gggg (e δ₁ δ₂ δm δ₃ m : ℝ) (α β : Wick.FermionVertex k_gggg → Fin 4)
    (lor : Wick.PhotonSlot k_gggg → Fin 4) (kψ kψ' : Wick.FermionVertex k_gggg → Fin 4 → ℝ)
    (kA kA' : Wick.PhotonSlot k_gggg → Fin 4 → ℝ) (t : Fin 4) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ' kA' t := by
  fin_cases t <;> rfl

/-- The pointwise bound for the amplitude numerator of a contraction of `k_gggg`. -/
theorem refinedBound_amplitudeNumerator_gggg (P : Params) {nf nA m : ℕ}
    (C : Contraction nf nA k_gggg) (φ : Flavoring k_gggg)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (al : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (k : (Fin 2 → Fin 4 → ℝ) → Line C → Fin 4 → ℝ) (e : FermionLine C → Fin (m + 1))
    (he : Function.Injective e) (hk : ∀ ℓ f, k ℓ (.inl f) = lineMomentum al p (e f) ℓ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    RefinedBound al (Finset.univ.image e) (Fintype.card (FermionLine C))
      fun ℓ => amplitudeNumerator P C φ pIn kIn (k ℓ) αOut βIn μ := by
  classical
  unfold amplitudeNumerator
  refine RefinedBound.sum _ fun α _ => RefinedBound.sum _ fun β _ =>
    RefinedBound.sum _ fun lor _ => ?_
  refine RefinedBound.const_mul _ ?_
  have hv : ∀ ℓ, (∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
      (psiMomentum₂ C pIn (k ℓ)) (photonMomentum₂ C kIn (k ℓ)) t) =
      ∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor 0 0 t := fun ℓ =>
    Finset.prod_congr rfl fun t _ => vertexFactor_gggg _ _ _ _ _ _ _ _ _ _ _ _ _ _
  simp only [hv, hk]
  have hprod := RefinedBound.prod (α := al) Finset.univ e he.injOn
    (g := fun f ℓ => (1 / I) *
      electronNumerator (P.mass (φ.1 f.1)) (lineMomentum al p (e f) ℓ) (β f.1) (α f.tail))
    fun f _ => (QED.TwoLoop.ClassIntegrable.refinedBound_electronNumerator al p (e f) _ _
      _).const_mul _
  rw [Finset.card_univ] at hprod
  have h := hprod.const_mul ((∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor 0 0 t) *
    ∏ g : PhotonLine C, (1 / I) *
      ((Minkowski.metric (lor g.1) (lor g.head) * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ))
  convert h using 2 with ℓ
  ring

/-- The amplitude numerator of a contraction of `k_gggg` is a polynomial of total degree at most
the number of fermion lines. -/
theorem isLoopPoly_amplitudeNumerator_gggg (P : Params) {nf nA L : ℕ}
    (C : Contraction nf nA k_gggg) (φ : Flavoring k_gggg)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (k : (Fin L → Fin 4 → ℝ) → Line C → Fin 4 → ℝ)
    (hk : ∀ f : FermionLine C, IsLoopAffine fun ℓ => k ℓ (.inl f))
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    IsLoopPoly L (Fintype.card (FermionLine C))
      fun ℓ => amplitudeNumerator P C φ pIn kIn (k ℓ) αOut βIn μ := by
  classical
  unfold amplitudeNumerator
  refine IsLoopPoly.sum _ fun α _ => IsLoopPoly.sum _ fun β _ => IsLoopPoly.sum _ fun lor _ => ?_
  refine IsLoopPoly.const_mul _ ?_
  have hv : ∀ ℓ, (∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
      (psiMomentum₂ C pIn (k ℓ)) (photonMomentum₂ C kIn (k ℓ)) t) =
      ∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor 0 0 t := fun ℓ =>
    Finset.prod_congr rfl fun t _ => vertexFactor_gggg _ _ _ _ _ _ _ _ _ _ _ _ _ _
  simp only [hv]
  have hfer := IsLoopPoly.prod (L := L) (Finset.univ : Finset (FermionLine C)) (fun _ => 1)
    (F := fun f ℓ => (1 / I) *
      electronNumerator (P.mass (φ.1 f.1)) (k ℓ (.inl f)) (β f.1) (α f.tail))
    fun f _ => ((hk f).isLoopPoly_electronNumerator _ _ _).const_mul _
  have hcard : (∑ _f ∈ (Finset.univ : Finset (FermionLine C)), 1) =
      Fintype.card (FermionLine C) := by
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ]
  rw [hcard] at hfer
  have h := ((IsLoopPoly.const (L := L) (n := 0) (∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃
    P.m α β lor 0 0 t)).mul hfer).mul (IsLoopPoly.const (L := L) (n := 0)
      (∏ g : PhotonLine C, (1 / I) *
        ((Minkowski.metric (lor g.1) (lor g.head) * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ)))
  simpa using h

/-- The masses of the seven parametric lines: three electron lines and two Pauli–Villars photon
pairs. -/
def massesSE (Q : Params) : Fin 7 → ℝ := ![Q.m, Q.m, Q.m, Q.mγ, Q.Λ, Q.mγ, Q.Λ]

/-- **(T₉′) for a two-loop contraction of four `gauge` vertices from parametric data.** -/
theorem jointEnergyFirstIntegrable_gggg (C : Contraction 1 0 k_gggg)
    (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) (hL : loopCount C = 2)
    (hcard : Fintype.card (FermionLine C) = 3) (a : Fin 7 → Fin 2 → ℤ)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2} a) (Q : Params) (hε : 0 < Q.ε)
    (p : Fin 4 → ℝ) (pp : Fin 7 → Fin 4 → ℝ) (e : FermionLine C → Fin 7)
    (he : Function.Injective e) (hE : ∀ f, e f ∈ ({0, 1, 2} : Finset (Fin 7)))
    (hk : ∀ ℓ f, lineMomentum₂ C ![p] ![p] ![] ℓ (.inl f) =
      lineMomentum (castLoopMatrix a) pp (e f) ℓ)
    (hden : ∀ ℓ, amplitudeDenominator Q C (zeroFlavoring k_gggg)
      (lineMomentum₂ C ![p] ![p] ![] ℓ) =
        ∏ i, (lineDenom (castLoopMatrix a) pp (massesSE Q) Q.ε i ℓ)⁻¹) (α β : Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ Q C ![p] ![] (lineMomentum₂ C ![p] ![p] ![] ℓ) ![α] ![β] ![] := by
  rw [hL]
  set κ : ℂ := (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ with hκ
  have haff : ∀ f : FermionLine C, IsLoopAffine fun ℓ => lineMomentum₂ C ![p] ![p] ![] ℓ (.inl f) :=
    fun f => by
      rw [show (fun ℓ => lineMomentum₂ C ![p] ![p] ![] ℓ (.inl f)) =
        lineMomentum (castLoopMatrix a) pp (e f) from funext fun ℓ => hk ℓ f]
      exact isLoopAffine_lineMomentum _ _ _
  have hpoly := isLoopPoly_amplitudeNumerator_gggg Q C (zeroFlavoring k_gggg) ![p] ![]
    (fun ℓ => lineMomentum₂ C ![p] ![p] ![] ℓ) haff ![α] ![β] ![]
  rw [hcard] at hpoly
  obtain ⟨P, hq, hP⟩ := IsLoopPoly.exists_loopQuartic_cubic (hpoly.const_mul κ)
  have hB : RefinedBound (castLoopMatrix a) {0, 1, 2} 4 P.eval := by
    rw [hP]
    have h := (refinedBound_amplitudeNumerator_gggg Q C (zeroFlavoring k_gggg) ![p] ![]
      (castLoopMatrix a) pp (fun ℓ => lineMomentum₂ C ![p] ![p] ![] ℓ) e he hk ![α] ![β]
      ![]).const_mul κ
    rw [hcard] at h
    refine h.mono ?_ (by norm_num)
    intro i hi
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hi
    exact hE f
  have h :=
    QED.Integration.TwoLoop.jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_cubic
    P (castLoopMatrix a) pp (massesSE Q) hq (le_refl 6) hε
    ((noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit) hB
  have hfun : (fun ℓ => κ * regulatedAmplitude₂ Q C ![p] ![] (lineMomentum₂ C ![p] ![p] ![] ℓ)
      ![α] ![β] ![]) = fun ℓ => P.eval ℓ *
        ∏ i, (lineDenom (castLoopMatrix a) pp (massesSE Q) Q.ε i ℓ)⁻¹ := by
    funext ℓ
    rw [regulatedAmplitude₂_eq_zeroFlavoring Q hcyc, contractionAmplitude₂_eq Q hε.ne', hden,
      hP]
    ring
  rw [hfun]
  exact h

end QED.GradedProof.SE2

end
