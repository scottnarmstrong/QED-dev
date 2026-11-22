/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCCovInv
public import QED.Frozen.Graded.FamilyVertex

/-!
# Inversion of all momenta in the graded model, at fixed `ε`

Helper level, generic in the selection; the graded analogue of `QED/ChainProof/HCCovInv.lean`.
The value (G₅) of **every** graded contraction whose external fermion fields are attached to
vertices satisfies, at every parameter set (so at every `ε`), every grading and for all external
data,

`V_C(-p_out, -p_in, -k)_{αβ…} = (-1)^{n_A} ∏ᵢ s(αᵢ) s(βᵢ) · V_C(p_out, p_in, k)_{αβ…}`

with `s = (-1, -1, 1, 1)` the diagonal of the chirality matrix `Γ`
(`QED.ChainProof.GradedMirror.contractionValue_neg`). The grading and the flavouring change only
the scalar coefficients and masses of the vertex factors, and the vertex identity
`QED.ChainProof.Inv.vertexFactor_neg` holds for all coefficients, counterterm vertices
(`gaugeCt`, `fermionCt`, `photonCt`) included. Summed over any selection that attaches the
externals (`selectedPart_neg`), the family vertex (Gf₁) satisfies
`V_ε(-p', -p)_{ij} = -s(i) s(j) V_ε(p', p)_{ij}` (`familyVertex_neg`), that is,
`V(-p', -p) = -Γ V(p', p) Γ`.
-/

@[expose] public section

open Complex Matrix
open QED.WickModel (Params Contraction Line FermionLine PhotonLine psiMomentum₂ photonMomentum₂
  lineMomentum₂ ExternalsAttached)

namespace QED.ChainProof.GradedMirror

open QED.ChainProof.Inv

/-- The vertex signs under inversion, for vertex-dependent coefficients. -/
theorem prod_vertexFactor_neg {N : ℕ} {κ : Fin N → Wick.VertexKind} (e : ℝ)
    (a b c d m : Fin N → ℝ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (kψ : Wick.FermionVertex κ → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) :
    ∏ t, Wick.vertexFactor e (a t) (b t) (c t) (d t) (m t) α β lor (-kψ) (-kA) t =
      (∏ t, vsgn α β sg t) *
        ∏ t, Wick.vertexFactor e (a t) (b t) (c t) (d t) (m t) α β lor kψ kA t := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun t _ => vertexFactor_neg _ _ _ _ _ _ _ _ _ _ _ t

section Value

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : QED.Lepton.Flavors F)
  (D : Graded.Counterterms F) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

omit [Fintype F] [DecidableEq F] in
/-- **Inversion of the graded amplitude** (G₃). -/
theorem contractionAmplitude_neg (C : Contraction nf nA κ)
    (hatt : ∀ i j : Fin nf, C.1.1 (.inl i) ≠ .inl j) (φ : Graded.Flavoring F κ)
    (g : Graded.Grading κ) (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (k : Line C → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    Graded.contractionAmplitude P Φ D C φ g (-pIn) (-kIn) (-k) αOut βIn μ =
      ((-1) ^ nA * ∏ i, sg (αOut i) * sg (βIn i)) *
        Graded.contractionAmplitude P Φ D C φ g pIn kIn k αOut βIn μ := by
  unfold Graded.contractionAmplitude
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => ?_
  split_ifs with hc
  · have hp := prod_sign_pairing C hatt sg sg_mul_self α β αOut βIn hc.1 hc.2.1
    have hF : ∏ f : FermionLine C, (1 / I) *
        QED.OneLoop.electronPropagator (Φ.mass (φ f.1)) P.ε ((-k) (.inl f)) (β f.1) (α f.tail) =
        (∏ f : FermionLine C, sg (β f.1) * sg (α f.tail)) * ∏ f : FermionLine C, (1 / I) *
        QED.OneLoop.electronPropagator (Φ.mass (φ f.1)) P.ε (k (.inl f)) (β f.1) (α f.tail) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun f _ => ?_
      rw [Pi.neg_apply, electronPropagator_neg]
      ring
    have hG : ∏ g' : PhotonLine C, (1 / I) *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε ((-k) (.inr g')) (lor g'.1) (lor g'.head) =
        ∏ g' : PhotonLine C, (1 / I) *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr g')) (lor g'.1) (lor g'.head) :=
      Finset.prod_congr rfl fun g' _ => by rw [Pi.neg_apply, photonPropagator_neg]
    rw [psiMomentum₂_neg, photonMomentum₂_neg, prod_vertexFactor_neg, hF, hG, prod_vsgn,
      neg_one_pow_card_photonSlot C, ← hp]
    ring
  · simp

open scoped Classical in
/-- **Inversion of the graded regulated amplitude** (G₄). -/
theorem regulatedAmplitude_neg (C : Contraction nf nA κ)
    (hatt : ∀ i j : Fin nf, C.1.1 (.inl i) ≠ .inl j) (g : Graded.Grading κ)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    Graded.regulatedAmplitude P Φ D C g (-pIn) (-kIn) (-k) αOut βIn μ =
      ((-1) ^ nA * ∏ i, sg (αOut i) * sg (βIn i)) *
        Graded.regulatedAmplitude P Φ D C g pIn kIn k αOut βIn μ := by
  unfold Graded.regulatedAmplitude
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [contractionAmplitude_neg P Φ D C hatt]
  ring

/-- **Inversion of all momenta in the graded value** (G₅), at every parameter set, every grading
and for all external data, for a contraction whose external fermion fields are attached. -/
theorem contractionValue_neg (C : Contraction nf nA κ)
    (hatt : ∀ i j : Fin nf, C.1.1 (.inl i) ≠ .inl j) (g : Graded.Grading κ)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    Graded.contractionValue P Φ D C g (-pOut) (-pIn) (-kIn) αOut βIn μ =
      ((-1) ^ nA * ∏ i, sg (αOut i) * sg (βIn i)) *
        Graded.contractionValue P Φ D C g pOut pIn kIn αOut βIn μ := by
  unfold Graded.contractionValue
  rw [← QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_neg]
  have e : ∀ ℓ : Fin (QED.WickModel.loopCount C) → Fin 4 → ℝ,
      lineMomentum₂ C (-pOut) (-pIn) (-kIn) (-ℓ) = -lineMomentum₂ C pOut pIn kIn ℓ :=
    fun ℓ => lineMomentum₂_neg C pOut pIn kIn ℓ
  simp only [e, regulatedAmplitude_neg P Φ D C hatt]
  rw [← jointEnergyFirstIntegral_const_mul]
  congr 1
  funext ℓ
  ring

open scoped Classical in
/-- **Inversion of all momenta in a selected graded part** (G₆), for a selection whose
contractions have attached external fermion fields. -/
theorem selectedPart_neg (nf nA : ℕ)
    (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction nf nA κ → Graded.Grading κ → Prop)
    (hSel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ)
      (g : Graded.Grading κ), Sel C g → ∀ i j : Fin nf, C.1.1 (.inl i) ≠ .inl j)
    (K : ℕ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    Graded.selectedPart P Φ D nf nA Sel K (-pOut) (-pIn) (-kIn) αOut βIn μ =
      ((-1) ^ nA * ∏ i, sg (αOut i) * sg (βIn i)) *
        Graded.selectedPart P Φ D nf nA Sel K pOut pIn kIn αOut βIn μ := by
  unfold Graded.selectedPart
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun N _ => Finset.sum_congr rfl fun κ _ =>
    Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun C hC => ?_
  rw [contractionValue_neg P Φ D C (hSel C g (Finset.mem_filter.mp hC).2)]
  ring

/-- **Inversion of all momenta in the family vertex** (Gf₁) at fixed `ε`, for a selection whose
contractions have attached external fermion fields:
`V_ε(-p', -p)_{ij} = -s(i) s(j) V_ε(p', p)_{ij}`, i.e. `V(-p', -p) = -Γ V(p', p) Γ`. -/
theorem familyVertex_neg
    (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction 1 1 κ → Graded.Grading κ → Prop)
    (hSel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
      (g : Graded.Grading κ), Sel C g → ∀ i j : Fin 1, C.1.1 (.inl i) ≠ .inl j)
    (K : ℕ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (i j : Fin 4) :
    Graded.familyVertex P Φ D Sel K (-p') (-p) μ i j =
      -(sg i * sg j) * Graded.familyVertex P Φ D Sel K p' p μ i j := by
  simp only [Graded.familyVertex, Matrix.of_apply]
  have e1 : (fun _ : Fin 1 => -p') = -fun _ : Fin 1 => p' := rfl
  have e2 : (fun _ : Fin 1 => -p) = -fun _ : Fin 1 => p := rfl
  have e3 : (fun _ : Fin 1 => -p' - -p) = -fun _ : Fin 1 => p' - p := by
    funext _
    simp only [Pi.neg_apply]
    abel
  rw [e1, e2, e3, selectedPart_neg P Φ D 1 1 Sel hSel]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton, pow_one]
  ring

end Value

end QED.ChainProof.GradedMirror

end
