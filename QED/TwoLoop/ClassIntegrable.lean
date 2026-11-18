/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ParametricBridgeS
public import QED.TwoLoop.ClassIntegrableLoopPoly
public import QED.TwoLoop.NestedVP
public import QED.Integration.TwoLoopRefinedBoundFubini
public import QED.Integration.SymanzikIntegrabilityRefinedClasses

/-!
# Integrability of both joint stages for the open-line classes at fixed `ε`

Obligation O2-7 (`docs/TWO-LOOP-DERIVATION.md`, section 4.3), its fixed-`ε` part, for the six
classes of five gauge vertices with an open electron line through both loops: `L`, `X`, `C₊`,
`C₋`, `S₊`, `S₋`. For every `ε > 0` (any masses, cutoffs and external momenta, under momentum
conservation), the integrand of the value (T₁₀) in the frozen routing (T₄) is integrable in the
energies at every spatial momentum, and its energy integral is integrable in the spatial momenta:
`QED.TwoLoop.jointEnergyFirstIntegrable` (T₉′) holds
(`QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_open`).

## Proof

* The bridge (`QED/TwoLoop/ParametricBridge*.lean`) writes the integrand in the class routing as
  the class numerator times the eight Pauli–Villars line denominators of
  `class5LoopMatrixPV c`, and the frozen routing as the class routing after an integer
  unimodular affine change of loop momenta.
* The numerator is a sum of constants times products, over the four fermion lines, of entries of
  `m - k̸_f`, each affine in the line momentum `k_f` (`amplitudeNumerator`). Every such entry
  satisfies `RefinedBound α {f} 1` (`refinedBound_electronNumerator`, from
  `refinedBound_lineMomentum`), so the numerator satisfies `RefinedBound α {0, 1, 2, 3} 4`
  (`refinedBound_amplitudeNumerator`, `refinedBound_classNumeratorE`): the pointwise bound by the
  line weights of the fermion lines.
* The numerator is a polynomial of degree at most four (`isLoopPoly_amplitudeNumerator`), hence
  a `LoopQuartic` (`IsLoopPoly.exists_loopQuartic`). With the criterion
  `NoSubdivergenceRefined 2 {0, 1, 2, 3}` for `class5LoopMatrixPV c`
  (`noSubdivergenceRefined_two_loopMatrixPV_iff`), the representation under the refined bound
  (`jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined`) gives both stages
  in the class routing (`jointEnergyFirstIntegrable_classRouting`).
* Integrability of both stages is invariant under integer unimodular affine changes
  (`QED.TwoLoop.NestedVP.jointEnergyFirstIntegrable_comp_matrix_add`), which transports it to
  the frozen routing.

The class `VP` is not covered here: its regulator-flavour sum is a sum of four bubble shapes
(`QED/TwoLoop/ParametricBridgeVPFlavour.lean`) and its numerator includes the closed-loop trace.
-/

@[expose] public section

open Complex

namespace QED.TwoLoop.ClassIntegrable

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix class5LoopMatrix
  class5LoopMatrixPV pvLines RefinedBound LoopQuartic refinedBound_lineMomentum
  NoSubdivergenceRefined)

/-! ### The pointwise bound for the amplitude numerator -/

/-- An entry of `m - k̸` at a line momentum is bounded by that line. -/
theorem refinedBound_electronNumerator {m : ℕ} (al : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (e : Fin (m + 1)) (mass : ℝ) (a b : Fin 4) :
    RefinedBound al {e} 1 fun ℓ => electronNumerator mass (lineMomentum al p e ℓ) a b := by
  have h : (fun ℓ => electronNumerator mass (lineMomentum al p e ℓ) a b) = fun ℓ =>
      (if a = b then (mass : ℂ) else 0) - ∑ μ, ∑ ν,
        (((Minkowski.metric μ ν : ℝ) : ℂ) * Dirac.gamma μ a b) *
          ((lineMomentum al p e ℓ ν : ℝ) : ℂ) := by
    funext ℓ
    rw [electronNumerator_apply]
    congr 1
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring
  rw [h]
  exact ((RefinedBound.const _).mono (Finset.empty_subset _) (Nat.zero_le _)).sub
    (RefinedBound.sum _ fun μ _ => RefinedBound.sum _ fun ν _ =>
      (refinedBound_lineMomentum al p e ν).const_mul _)

/-- **The pointwise bound for the amplitude numerator.** For a contraction of gauge vertices
whose fermion-line momenta are line momenta `k_f = α_{e(f)}·ℓ + p_{e(f)}` of the parametric data,
with `e` injective, the numerator of the amplitude satisfies the pointwise bound by the line
weights of the lines `e(f)`, with exponent the number of fermion lines. -/
theorem refinedBound_amplitudeNumerator (P : Params) {nf nA N m : ℕ}
    (C : Contraction nf nA (Enumeration.gauges N)) (φ : Flavoring (Enumeration.gauges N))
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
    Finset.prod_congr rfl fun t _ => vertexFactor_gauges _ _ _ _ _ _ _ _ _ _ _ _ _ _
  simp only [hv, hk]
  have hprod := RefinedBound.prod (α := al) Finset.univ e he.injOn
    (g := fun f ℓ => (1 / I) *
      electronNumerator (P.mass (φ.1 f.1)) (lineMomentum al p (e f) ℓ) (β f.1) (α f.tail))
    fun f _ => (refinedBound_electronNumerator al p (e f) _ _ _).const_mul _
  rw [Finset.card_univ] at hprod
  have h := hprod.const_mul ((∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor 0 0 t) *
    ∏ g : PhotonLine C, (1 / I) *
      ((Minkowski.metric (lor g.1) (lor g.head) * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ))
  convert h using 2 with ℓ
  ring

/-! ### The open-line classes -/

/-- The six classes of five gauge vertices with an open electron line through both loops. -/
abbrev openClasses : Finset Class5 := {.L, .X, .Cp, .Cm, .Sp, .Sm}

/-- The lines `0, …, 5` of a class inside the eight lines of its Pauli–Villars form. -/
def pvIdx (j : Fin 6) : Fin 8 := Fin.castLE (by norm_num) j

theorem pvLines_pvIdx : ∀ j : Fin 6, pvLines (pvIdx j) = j := by decide

theorem pvIdx_mem_of_lt : ∀ j : Fin 6, (j : ℕ) < 4 → pvIdx j ∈ ({0, 1, 2, 3} : Finset (Fin 8)) := by
  decide

/-- The fermion-line momenta of the class routing are line momenta of the Pauli–Villars data. -/
theorem classMomE_inl (c : Class5) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ)
    (f : FermionLine c.rep) :
    classMomE c p p' ℓ (.inl f) = lineMomentum (castLoopMatrix (class5LoopMatrixPV c))
      (pvMomentaE c p p') (pvIdx (lineIdx (.inl f : Line c.rep))) ℓ := by
  simp only [classMomE, QED.Integration.TwoLoop.castLoopMatrix_class5LoopMatrixPV]
  funext μ
  unfold QED.Integration.TwoLoop.lineMomentum pvMomentaE
  simp only [pvLines_pvIdx]

/-- The fermion lines of an open-line class are the lines `0, 1, 2, 3`, each once. -/
theorem fermionLine_facts {c : Class5} (hc : c ∈ openClasses) :
    Function.Injective (fun f : FermionLine c.rep => lineIdx (.inl f : Line c.rep)) ∧
      (∀ f : FermionLine c.rep, (lineIdx (.inl f : Line c.rep) : ℕ) < 4) ∧
      Fintype.card (FermionLine c.rep) = 4 := by
  simp only [openClasses, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide +kernel, by decide +kernel, card_fermionLine_L⟩
  · exact ⟨by decide +kernel, by decide +kernel, card_fermionLine_X⟩
  · exact ⟨by decide +kernel, by decide +kernel, card_fermionLine_Cp⟩
  · exact ⟨by decide +kernel, by decide +kernel, card_fermionLine_Cm⟩
  · exact ⟨by decide +kernel, by decide +kernel, card_fermionLine_Sp⟩
  · exact ⟨by decide +kernel, by decide +kernel, card_fermionLine_Sm⟩

/-- **The pointwise bound for the class numerators**: by the line weights of the four fermion
lines `0, 1, 2, 3` of the Pauli–Villars data, with exponent `4`. -/
theorem refinedBound_classNumeratorE {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    RefinedBound (castLoopMatrix (class5LoopMatrixPV c)) {0, 1, 2, 3} 4
      (classNumeratorE c P pOut pIn kIn αOut βIn μ) := by
  obtain ⟨hinj, hlt, hcard⟩ := fermionLine_facts hc
  have h := refinedBound_amplitudeNumerator P c.rep zeroFlavoring pIn kIn
    (castLoopMatrix (class5LoopMatrixPV c)) (pvMomentaE c (pIn 0) (pOut 0))
    (classMomE c (pIn 0) (pOut 0)) (fun f => pvIdx (lineIdx (.inl f : Line c.rep)))
    ((Fin.castLE_injective _).comp hinj) (fun ℓ f => classMomE_inl c _ _ ℓ f) αOut βIn μ
  refine h.mono ?_ hcard.le
  intro i hi
  obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hi
  exact pvIdx_mem_of_lt _ (hlt f)

/-- The class numerators are polynomials of degree at most four in the loop momenta. -/
theorem isLoopPoly_classNumeratorE {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    IsLoopPoly 2 4 (classNumeratorE c P pOut pIn kIn αOut βIn μ) :=
  (isLoopPoly_amplitudeNumerator P c.rep zeroFlavoring pIn kIn (classMomE c (pIn 0) (pOut 0))
    (fun _ => isLoopAffine_lineMomentum _ _ _) αOut βIn μ).mono (fermionLine_facts hc).2.2.le

/-- **Both joint stages are integrable in the class routing**, for every `ε > 0`. -/
theorem jointEnergyFirstIntegrable_classRouting {c : Class5} (hc : c ∈ openClasses)
    (P : Params) (hε : 0 < P.ε) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (fun ℓ =>
      (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        (classNumeratorE c P pOut pIn kIn αOut βIn μ ℓ *
          ∏ i : Fin 8, (pvDenomE c P (pIn 0) (pOut 0) i ℓ)⁻¹)) := by
  set κ : ℂ := (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ with hκ
  obtain ⟨Q, hQ⟩ := ((isLoopPoly_classNumeratorE hc P pOut pIn kIn αOut βIn μ).const_mul
    κ).exists_loopQuartic
  have hB : RefinedBound (castLoopMatrix (class5LoopMatrixPV c)) {0, 1, 2, 3} 4 Q.eval := by
    rw [hQ]
    exact (refinedBound_classNumeratorE hc P pOut pIn kIn αOut βIn μ).const_mul κ
  have hcrit : NoSubdivergenceRefined 2 {0, 1, 2, 3} (castLoopMatrix (class5LoopMatrixPV c)) :=
    (QED.Integration.TwoLoop.noSubdivergenceRefined_two_loopMatrixPV_iff c).mpr hc
  have h := QED.Integration.TwoLoop.jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined
    Q (castLoopMatrix (class5LoopMatrixPV c)) (pvMomentaE c (pIn 0) (pOut 0)) (pvMasses P)
    (by norm_num : 7 ≤ 7) hε hcrit hB
  have hfun : (fun ℓ => κ * (classNumeratorE c P pOut pIn kIn αOut βIn μ ℓ *
      ∏ i : Fin 8, (pvDenomE c P (pIn 0) (pOut 0) i ℓ)⁻¹)) =
      fun ℓ => Q.eval ℓ * ∏ i : Fin 8, (lineDenom (castLoopMatrix (class5LoopMatrixPV c))
        (pvMomentaE c (pIn 0) (pOut 0)) (pvMasses P) P.ε i ℓ)⁻¹ := by
    funext ℓ
    rw [hQ]
    simp only [pvDenomE]
    ring
  rw [hfun]
  exact h

/-- Transport of (T₉′) along an integer unimodular affine change of loop momenta. -/
theorem jointEnergyFirstIntegrable_of_comp {G H : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : IsUnit M.det) (a : Fin 2 → Fin 4 → ℝ)
    (hG : QED.TwoLoop.jointEnergyFirstIntegrable 2 G)
    (hH : ∀ ℓ, H ℓ = G ((fun s => ∑ r, M s r • ℓ r) + a)) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 H := by
  have h := NestedVP.jointEnergyFirstIntegrable_comp_matrix_add 2 G M hM a hG
  rwa [show H = fun ℓ => G ((fun s => ∑ r, M s r • ℓ r) + a) from funext hH]

/-- **O2-7 at fixed `ε` for the open-line classes.** For `c ∈ {L, X, C₊, C₋, S₊, S₋}`, every
`ε > 0` and momentum conservation `p' = p + k`, the integrand `(2π)⁻⁸ A(ℓ)` of the value (T₁₀)
in the frozen routing (T₄) has both stages of the joint energy-first integral integrable (T₉′):
it is integrable in the loop energies at every spatial momentum, and the energy integral is
integrable in the spatial momenta. No condition on the masses, the cutoff or the external
momenta beyond conservation is needed at fixed `ε > 0`. -/
theorem jointEnergyFirstIntegrable_open {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hε : 0 < P.ε) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (fun ℓ =>
      (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P c.rep pIn kIn (lineMomentum₂ c.rep pOut pIn kIn ℓ) αOut βIn μ) := by
  have hG := jointEnergyFirstIntegrable_classRouting hc P hε pOut pIn kIn αOut βIn μ
  have hε' : P.ε ≠ 0 := hε.ne'
  simp only [openClasses, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact jointEnergyFirstIntegrable_of_comp matL isUnit_det_matL ![-(pIn 0), -(pIn 0)] hG
      fun ℓ => by rw [regulatedAmplitude₂_lineMomentum₂_L P hε' hmom]; rfl
  · exact jointEnergyFirstIntegrable_of_comp matX isUnit_det_matX ![-(pIn 0), 0] hG
      fun ℓ => by rw [regulatedAmplitude₂_lineMomentum₂_X P hε' hmom]; rfl
  · exact jointEnergyFirstIntegrable_of_comp matCp isUnit_det_matCp ![-(pOut 0), pOut 0 - pIn 0]
      hG fun ℓ => by rw [regulatedAmplitude₂_lineMomentum₂_Cp P hε' hmom]; rfl
  · exact jointEnergyFirstIntegrable_of_comp matCm isUnit_det_matCm ![-(pIn 0), 0] hG
      fun ℓ => by rw [regulatedAmplitude₂_lineMomentum₂_Cm P hε' hmom]; rfl
  · exact jointEnergyFirstIntegrable_of_comp matSp isUnit_det_matSp ![-(pOut 0), pOut 0 - pIn 0]
      hG fun ℓ => by rw [regulatedAmplitude₂_lineMomentum₂_Sp P hε' hmom]; rfl
  · exact jointEnergyFirstIntegrable_of_comp matSm isUnit_det_matSm ![-(pIn 0), 0] hG
      fun ℓ => by rw [regulatedAmplitude₂_lineMomentum₂_Sm P hε' hmom]; rfl

/-- **The value of an open-line class is a genuine joint integral.** Under the hypotheses of
`jointEnergyFirstIntegrable_open`, the value (T₁₀) is the joint energy-first integral (T₉) of an
integrand whose two stages are integrable. -/
theorem contractionValue₂_open_eq_of_integrable {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hε : 0 < P.ε) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P c.rep pOut pIn kIn αOut βIn μ =
        QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ =>
          (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
            regulatedAmplitude₂ P c.rep pIn kIn (lineMomentum₂ c.rep pOut pIn kIn ℓ) αOut βIn μ) ∧
      QED.TwoLoop.jointEnergyFirstIntegrable 2 (fun ℓ =>
        (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
          regulatedAmplitude₂ P c.rep pIn kIn (lineMomentum₂ c.rep pOut pIn kIn ℓ) αOut βIn μ) :=
  ⟨Relabel.contractionValue₂_eq_of_loopCount P (loopCount_rep c) pOut pIn kIn αOut βIn μ,
    jointEnergyFirstIntegrable_open hc P hε hmom αOut βIn μ⟩

end QED.TwoLoop.ClassIntegrable

end
