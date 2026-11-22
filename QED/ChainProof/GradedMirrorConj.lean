/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.GradedMirrorGraph

/-!
# Charge conjugation in the graded model at fixed `ε`, and the mirror identity of a family vertex

Helper level, generic in the selection; the graded analogue of `QED/ChainProof/HCCovConj.lean`,
now with the `fermionCt` (`δ₂`, `δ_m`) vertices. For a contraction `C`, the charge-conjugate
contraction `QED.ChainProof.Conj.ccC C` reverses every fermion line; it has the same vertex kinds,
so every grading `g` of `C` is one of `ccC C`, with the same levels.

* `vertexFactor_ccG`: under `(α, β) ↦ (p ∘ β, p ∘ α)`, every vertex factor (V₁₉) gets the sign
  `(-1)^{#photon fields} c(α) c(β)`, for all coefficients and masses; for a `fermionCt` vertex
  this needs its momentum reversed, `C (δ₂ k̸ + δ_m m)ᵀ C = δ₂ (-k)̸ + δ_m m`.
* `contractionAmplitude_ccC`, `regulatedAmplitude_ccC`: the graded amplitudes (G₃), (G₄) of
  `ccC C` at line momenta `k'` whose pull-back to `C` is conserved (so that the momentum of every
  `fermionCt` vertex reverses, `QED.ChainProof.GradedMirror.psiMomentum₂_ccC_of_fermionCt`).
* `contractionValue_ccC`: **charge conjugation of the graded value** (G₅), at every parameter set
  and grading, for attached externals, connected vertices and momentum conservation: the value of
  `ccC C` at `(-p_in, -p_out, k)` and indices `(p(β), p(α))` is `(-1)^{n_A} ∏ᵢ c(αᵢ) c(βᵢ)` times
  that of `C`. The loop momenta change by an integer unimodular affine map.
* `selectedPart_ccC`, `familyVertex_cc`: for a selection that implies one-particle
  irreducibility and is closed under `ccC` (with the same grading), reindexing the sum along the
  involution `ccC` gives `C V(p', p)ᵀ C = -V(-p, -p')` at every `ε`.
* **`chargeConj_familyVertex`**: with the inversion of all momenta
  (`QED.ChainProof.GradedMirror.familyVertex_neg`), the **fixed-`ε` mirror identity**
  `C V_ε(p', p)^μᵀ C = Γ V_ε(p, p')^μ Γ` of the family vertex (Gf₁), for all momenta.
-/

@[expose] public section

open Complex Matrix
open QED.WickModel (Params Contraction Line FermionLine PhotonLine psiMomentum₂ photonMomentum₂
  lineMomentum₂ externalMomentum IsOnePI VerticesConnected loopCount fermionSign)

namespace QED.ChainProof.GradedMirror

open QED.ChainProof.Inv QED.ChainProof.Conj QED.Dirac QED.TwoLoop.Routing

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### Vertex factors -/

theorem one_ccIdx (a b : Fin 4) :
    (1 : Matrix (Fin 4) (Fin 4) ℂ) (ccIdx b) (ccIdx a) =
      ccSign a * ccSign b * (1 : Matrix (Fin 4) (Fin 4) ℂ) a b := by
  fin_cases a <;> fin_cases b <;> simp [ccIdx, ccSign, Matrix.one_apply]

section VertexFactor

variable (e δ₁ δ₂ δm δ₃ m : ℝ) (α β : Wick.FermionVertex κ → Fin 4)
  (lor : Wick.PhotonSlot κ → Fin 4)
  (kψ kψ' : Wick.FermionVertex κ → Fin 4 → ℝ) (kA : Wick.PhotonSlot κ → Fin 4 → ℝ)

/-- **Charge conjugation of a vertex factor**, every vertex kind; a `fermionCt` vertex needs its
momentum reversed. -/
theorem vertexFactor_ccG (t : Fin N)
    (hψ : ∀ h : κ t ≠ .photonCt, κ t = .fermionCt → kψ' ⟨t, h⟩ = -kψ ⟨t, h⟩) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m (fun x => ccIdx (β x)) (fun x => ccIdx (α x)) lor kψ' kA t =
      vsgn α β ccSign t * Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t := by
  by_cases hk : κ t = .fermionCt
  · have hne : κ t ≠ .photonCt := by rw [hk]; decide
    have hs : (κ t).photonSlots = 0 := by rw [hk]; rfl
    unfold vsgn
    rw [dite_eq_left hne, hs, pow_zero, one_mul, vf_fermionCt _ _ _ _ _ _ _ _ _ _ _ hk,
      vf_fermionCt _ _ _ _ _ _ _ _ _ _ _ hk, hψ hne hk]
    simp only [QED.Dirac.slash_neg, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply,
      smul_eq_mul]
    rw [slash_ccIdx, one_ccIdx]
    ring
  · exact vertexFactor_cc e δ₁ δ₂ δm δ₃ m α β lor kψ kψ' kA t hk

/-- The vertex signs under charge conjugation, for vertex-dependent coefficients. -/
theorem prod_vertexFactor_cc (a b c d m : Fin N → ℝ)
    (hψ : ∀ t : Wick.FermionVertex κ, κ t.1 = .fermionCt → kψ' t = -kψ t) :
    ∏ t, Wick.vertexFactor e (a t) (b t) (c t) (d t) (m t) (fun x => ccIdx (β x))
        (fun x => ccIdx (α x)) lor kψ' kA t =
      (∏ t, vsgn α β ccSign t) *
        ∏ t, Wick.vertexFactor e (a t) (b t) (c t) (d t) (m t) α β lor kψ kA t := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun t _ =>
    vertexFactor_ccG _ _ _ _ _ _ _ _ _ _ _ _ t fun h hk => hψ ⟨t, h⟩ hk

end VertexFactor

/-! ### Amplitude and value -/

section Value

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : QED.Lepton.Flavors F)
  (D : Graded.Counterterms F)

omit [Fintype F] [DecidableEq F] in
open scoped Classical in
/-- **Charge conjugation of the graded amplitude** (G₃): the amplitude of `ccC C` at line
momenta `k'`, whose pull-back to `C` is conserved, with external `Ψ̄` momenta `-p_out` and indices
`(p(β), p(α))`, is `(-1)^{n_A} ∏ c(α) c(β)` times the amplitude of `C` at the pulled-back momenta
and indices `(α, β)`. -/
theorem contractionAmplitude_ccC (C : Contraction nf nA κ)
    (hatt : ∀ i j : Fin nf, C.1.1 (.inl i) ≠ .inl j) (φ : Graded.Flavoring F κ)
    (hφ : Graded.Preserves Φ C φ) (g : Graded.Grading κ) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (k' : Line (ccC C) → Fin 4 → ℝ)
    (hk : IsConserved C pOut pIn kIn ((corrCC C).pull k'))
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    Graded.contractionAmplitude P Φ D (ccC C) φ g (-pOut) kIn k' (fun i => ccIdx (βIn i))
        (fun i => ccIdx (αOut i)) μ =
      ((-1) ^ nA * ∏ i, ccSign (αOut i) * ccSign (βIn i)) *
        Graded.contractionAmplitude P Φ D C φ g pIn kIn ((corrCC C).pull k') αOut βIn μ := by
  unfold Graded.contractionAmplitude
  refine (sum_ccIdx _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun lor _ => ?_
  have hiff : ((∀ i t, (ccC C).1.1 (.inl i) = .inr t → ccIdx (β t) = ccIdx (βIn i)) ∧
      (∀ t i, (ccC C).1.1 (.inr t) = .inl i → ccIdx (α t) = ccIdx (αOut i)) ∧
      (∀ j a, (ccC C).1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      ((∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
      (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
      (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j)) := by
    simp only [ccC_apply_eq_iff, ccC_snd, (Function.LeftInverse.injective ccIdx_ccIdx).eq_iff]
    exact ⟨fun h => ⟨fun i t hit => h.2.1 t i hit, fun t i hti => h.1 i t hti, h.2.2⟩,
      fun h => ⟨fun i t hit => h.2.1 t i hit, fun t i hti => h.1 i t hti, h.2.2⟩⟩
  by_cases hc : (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
      (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
      (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j)
  · rw [ite_eq_left (hiff.mpr hc), ite_eq_left hc, one_mul, one_mul]
    have hp := prod_sign_pairing C hatt ccSign ccSign_mul_self α β αOut βIn hc.1 hc.2.1
    have hψ : ∀ t : Wick.FermionVertex κ, κ t.1 = .fermionCt →
        psiMomentum₂ (ccC C) (-pOut) k' t = -psiMomentum₂ C pIn ((corrCC C).pull k') t :=
      fun t ht => psiMomentum₂_ccC_of_fermionCt C pOut pIn kIn k' hk t ht
    have hF : ∏ f : FermionLine (ccC C), (1 / I) *
        QED.OneLoop.electronPropagator (Φ.mass (φ f.1)) P.ε (k' (.inl f)) (ccIdx (α f.1))
          (ccIdx (β f.tail)) =
        (∏ f : FermionLine C, ccSign (β f.1) * ccSign (α f.tail)) * ∏ f : FermionLine C,
          (1 / I) * QED.OneLoop.electronPropagator (Φ.mass (φ f.1)) P.ε
            ((corrCC C).pull k' (.inl f)) (β f.1) (α f.tail) := by
      rw [← Equiv.prod_comp (fermEquiv C), ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun f _ => ?_
      have hfl : φ f.tail = φ f.1 := by
        have := hφ (.inr f.1)
        rwa [fermionLine_spec f] at this
      change (1 / I) * QED.OneLoop.electronPropagator (Φ.mass (φ (lineCC f).1)) P.ε
          (k' (.inl (lineCC f))) (ccIdx (α (lineCC f).1)) (ccIdx (β (lineCC f).tail)) = _
      rw [lineCC_val, lineCC_tail, hfl, QED.OneLoop.electronPropagator_ccIdx, pull_inl]
      ring
    have hG : ∏ g' : PhotonLine (ccC C), (1 / I) *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k' (.inr g')) (lor g'.1) (lor g'.head) =
        ∏ g' : PhotonLine C, (1 / I) *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε ((corrCC C).pull k' (.inr g')) (lor g'.1)
          (lor g'.head) := rfl
    rw [photonMomentum₂_ccC, prod_vertexFactor_cc (hψ := hψ), hF, hG,
      prod_vsgn, neg_one_pow_card_photonSlot C, ← hp]
    ring
  · rw [ite_eq_right (fun h => hc (hiff.mp h)), ite_eq_right hc]
    simp

open scoped Classical in
/-- **Charge conjugation of the graded regulated amplitude** (G₄). -/
theorem regulatedAmplitude_ccC (C : Contraction nf nA κ)
    (hatt : ∀ i j : Fin nf, C.1.1 (.inl i) ≠ .inl j) (g : Graded.Grading κ)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k' : Line (ccC C) → Fin 4 → ℝ)
    (hk : IsConserved C pOut pIn kIn ((corrCC C).pull k'))
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    Graded.regulatedAmplitude P Φ D (ccC C) g (-pOut) kIn k' (fun i => ccIdx (βIn i))
        (fun i => ccIdx (αOut i)) μ =
      ((-1) ^ nA * ∏ i, ccSign (αOut i) * ccSign (βIn i)) *
        Graded.regulatedAmplitude P Φ D C g pIn kIn ((corrCC C).pull k') αOut βIn μ := by
  unfold Graded.regulatedAmplitude
  rw [Finset.mul_sum]
  have hfil : (Finset.univ : Finset (Graded.Flavoring F κ)).filter
      (Graded.Preserves Φ (ccC C)) =
      (Finset.univ : Finset (Graded.Flavoring F κ)).filter (Graded.Preserves Φ C) :=
    Finset.filter_congr fun φ _ => preserves_ccC_iff Φ C φ
  rw [hfil]
  refine Finset.sum_congr rfl fun φ hφ => ?_
  have hφ' := (Finset.mem_filter.mp hφ).2
  rw [loopWeight_ccC Φ C hφ', contractionAmplitude_ccC P Φ D C hatt φ hφ' g pOut pIn kIn k' hk]
  ring

theorem contractionValue_eq_of_loopCount {C : Contraction nf nA κ} {L : ℕ}
    (hL : loopCount C = L) (g : Graded.Grading κ) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    Graded.contractionValue P Φ D C g pOut pIn kIn αOut βIn μ =
      QED.TwoLoop.jointEnergyFirstIntegral L fun ℓ => (((2 * Real.pi) ^ (4 * L) : ℝ) : ℂ)⁻¹ *
        Graded.regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn
          μ := by
  subst hL
  rfl

/-- **Charge conjugation of the graded value** (G₅), at every parameter set (so every `ε`) and
every grading, for attached external fermion fields, connected vertices and momentum
conservation. -/
theorem contractionValue_ccC (C : Contraction nf nA κ)
    (hatt : ∀ i j : Fin nf, C.1.1 (.inl i) ≠ .inl j) (hV : VerticesConnected C)
    (g : Graded.Grading κ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (hsum : ∑ v, externalMomentum C pOut pIn kIn v = 0)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    Graded.contractionValue P Φ D (ccC C) g (-pIn) (-pOut) kIn (fun i => ccIdx (βIn i))
        (fun i => ccIdx (αOut i)) μ =
      ((-1) ^ nA * ∏ i, ccSign (αOut i) * ccSign (βIn i)) *
        Graded.contractionValue P Φ D C g pOut pIn kIn αOut βIn μ := by
  have hV' := verticesConnected_ccC hV
  have hL := loopCount_ccC hV
  obtain ⟨M, hMdet, a, h⟩ := QED.TwoLoop.LimitMirror.exists_routing_change_of_ext (corrCC C) hV
    hV' (fun v => externalMomentum_ccC C pOut pIn kIn v) hsum rfl hL
  rw [contractionValue_eq_of_loopCount P Φ D hL, contractionValue_eq_of_loopCount P Φ D rfl]
  have e : (fun ℓ : Fin (loopCount C) → Fin 4 → ℝ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        Graded.regulatedAmplitude P Φ D (ccC C) g (-pOut) kIn
          (lineMomentum₂ (ccC C) (-pIn) (-pOut) kIn ℓ) (fun i => ccIdx (βIn i))
          (fun i => ccIdx (αOut i)) μ) =
      fun ℓ => ((-1) ^ nA * ∏ i, ccSign (αOut i) * ccSign (βIn i)) *
        ((fun ℓ' : Fin (loopCount C) → Fin 4 → ℝ =>
          (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
            Graded.regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ')
              αOut βIn μ)
          ((fun s => ∑ r, M s r • ℓ r) + a)) := by
    funext ℓ
    have hk : IsConserved C pOut pIn kIn
        ((corrCC C).pull (lineMomentum₂ (ccC C) (-pIn) (-pOut) kIn ℓ)) := by
      rw [h ℓ]
      exact isConserved_lineMomentum₂ hV hsum _
    rw [regulatedAmplitude_ccC P Φ D C hatt g pOut pIn kIn _ hk, h]
    exact mul_left_comm _ _ _
  rw [e, jointEnergyFirstIntegral_const_mul]
  exact congrArg _
    (QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add _
      (fun ℓ' : Fin (loopCount C) → Fin 4 → ℝ =>
        (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
          Graded.regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ') αOut
            βIn μ)
      M hMdet a)

/-! ### Selected parts and family vertices -/

open scoped Classical in
/-- **Charge conjugation of a selected graded part** (G₆), for a selection that implies one-particle
irreducibility and is closed under `ccC` with the same grading, under momentum conservation. -/
theorem selectedPart_ccC (nf nA : ℕ)
    (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction nf nA κ → Graded.Grading κ → Prop)
    (hSel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ)
      (g : Graded.Grading κ), Sel C g → Sel (ccC C) g)
    (hOne : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ)
      (g : Graded.Grading κ), Sel C g → IsOnePI C)
    (K : ℕ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (hmom : ∑ i, pIn i + ∑ j, kIn j - ∑ i, pOut i = 0)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    Graded.selectedPart P Φ D nf nA Sel K (-pIn) (-pOut) kIn (fun i => ccIdx (βIn i))
        (fun i => ccIdx (αOut i)) μ =
      ((-1) ^ nA * ∏ i, ccSign (αOut i) * ccSign (βIn i)) *
        Graded.selectedPart P Φ D nf nA Sel K pOut pIn kIn αOut βIn μ := by
  unfold Graded.selectedPart
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun N _ => Finset.sum_congr rfl fun κ _ =>
    Finset.sum_congr rfl fun g _ => ?_
  refine Finset.sum_nbij' ccC ccC ?_ ?_ (fun C _ => ccC_ccC C) (fun C _ => ccC_ccC C) ?_
  · intro C hC
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC ⊢
    exact hSel C g hC
  · intro C hC
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC ⊢
    exact hSel C g hC
  · intro C hC
    have hC' := hSel C g (Finset.mem_filter.mp hC).2
    have h1 := hOne _ g hC'
    have hsign : fermionSign (ccC C) = fermionSign C := by
      simp only [fermionSign, ccC_fst, Equiv.Perm.sign_inv]
    have hsum : ∑ v, externalMomentum (ccC C) pOut pIn kIn v = 0 := by
      rw [QED.TwoLoop.Relabel.sum_externalMomentum h1.1, hmom]
    have hv := contractionValue_ccC P Φ D (ccC C) h1.1.1 h1.2.1 g pOut pIn kIn hsum αOut βIn μ
    rw [ccC_ccC] at hv
    rw [hsign, hv]
    ring

/-- **Charge conjugation of the family vertex** (Gf₁) at fixed `ε`, for all momenta, for a
selection that implies one-particle irreducibility and is closed under `ccC`:
`V(-p, -p')_{ab} = -c(a) c(b) V(p', p)_{p(b) p(a)}`, i.e. `C V(p', p)ᵀ C = -V(-p, -p')`. -/
theorem familyVertex_cc
    (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction 1 1 κ → Graded.Grading κ → Prop)
    (hSel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
      (g : Graded.Grading κ), Sel C g → Sel (ccC C) g)
    (hOne : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
      (g : Graded.Grading κ), Sel C g → IsOnePI C)
    (K : ℕ) (p' p : Fin 4 → ℝ) (μ a b : Fin 4) :
    Graded.familyVertex P Φ D Sel K (-p) (-p') μ a b =
      -(ccSign a * ccSign b) * Graded.familyVertex P Φ D Sel K p' p μ (ccIdx b) (ccIdx a) := by
  simp only [Graded.familyVertex, Matrix.of_apply]
  have hk : (fun _ : Fin 1 => -p - -p') = fun _ => p' - p := by
    funext _
    abel
  have hmom : ∑ i : Fin 1, (fun _ => p) i + ∑ j : Fin 1, (fun _ => p' - p) j -
      ∑ i : Fin 1, (fun _ => p') i = 0 := by
    simp
  have h := selectedPart_ccC P Φ D 1 1 Sel hSel hOne K (fun _ => p') (fun _ => p)
    (fun _ => p' - p) hmom (fun _ => ccIdx b) (fun _ => ccIdx a) (fun _ => μ)
  simp only [ccIdx_ccIdx, Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton,
    pow_one, ccSign_ccIdx] at h
  rw [hk, show (fun _ : Fin 1 => -p) = -fun _ : Fin 1 => p from rfl,
    show (fun _ : Fin 1 => -p') = -fun _ : Fin 1 => p' from rfl, h]
  ring

/-- **The fixed-`ε` mirror identity of a family vertex** (Gf₁), for all momenta, for a selection
that implies one-particle irreducibility and is closed under `ccC`:
`C V(p', p)^μᵀ C = Γ V(p, p')^μ Γ`. -/
theorem chargeConj_familyVertex
    (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction 1 1 κ → Graded.Grading κ → Prop)
    (hSel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
      (g : Graded.Grading κ), Sel C g → Sel (ccC C) g)
    (hOne : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
      (g : Graded.Grading κ), Sel C g → IsOnePI C)
    (K : ℕ) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    chargeConj * (Graded.familyVertex P Φ D Sel K p' p μ)ᵀ * chargeConj =
      chir * Graded.familyVertex P Φ D Sel K p p' μ * chir := by
  ext a b
  rw [QED.TwoLoop.LimitMirror.chargeConj_transpose_apply, chir_mul_mul_chir_apply]
  have h1 := familyVertex_cc P Φ D Sel hSel hOne K p' p μ a b
  have h2 := familyVertex_neg P Φ D Sel (fun C g h => (hOne C g h).1.1) K p p' μ a b
  rw [h1] at h2
  linear_combination -h2

end Value

end QED.ChainProof.GradedMirror

end
