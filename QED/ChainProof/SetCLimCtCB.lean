/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLimCtCD01
public import QED.ChainProof.SetCLinkIntCB
public import QED.GradedProof.Embed
public import QED.LeptonProof.EmbedRelabel
public import QED.TwoLoop.ClassLimitVP
public import QED.TwoLoop.ReflCovarianceClasses
public import QED.TwoLoop.RelabelCountertermClasses

/-!
# Set (c): limits and covariance of the three bubble classes `CB2`–`CB4`

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. The classes
`repCB2`, `repCB3`, `repCB4` are the one-loop vertex with a level-`0` `gaugeCt` vertex on its open
line and the bubble (a closed fermion loop) on its photon line. The graded value (G₅) is reduced
to T1's value (T₁₀) of the two-loop vacuum-polarization class without passing through T1's
flavourings (where a `gaugeCt` vertex must carry flavour `0`):

* `contractionValue_toG_const`: changing the `gaugeCt` vertices into `gauge` vertices
  (`QED.ChainProof.SetALink.toG`) multiplies the graded value at the zero grading by a constant
  `w`, when the `gaugeCt` factor `ctW` of every preserved flavouring is `w` and the loop weights
  agree (a pointwise identity of the integrands, `regulatedAmplitude_toG_const`, and a routing
  change);
* `contractionValue_gauges_regFlavors`: the graded value of a contraction of `gauge` vertices at
  the set (c) flavours is T1's value (`QED.GradedProof.contractionValue_zero_eq`, then the
  relabelling `Fin 3 ⊕ Fin 0 × Fin 3 ≃ Fin 3` of `QED.Lepton.Proof.contractionValue₂_relabel`);
* `toG_repCB2`, …: the changed contraction is a relabelling of `Class5.VP.rep` (kernel
  evaluation);
* `cbVal_apply`: the value of `CBₖ` (`k = 2, 3, 4`) is `e² d₁(e⁻, 0)` times T1's value of
  `Class5.VP.rep`.

Hence the limits exist and are `e² d₁(e⁻, 0)` times the class limit
`QED.TwoLoop.LimitCovariance.classLimitV .VP`, whose covariance is
`QED.TwoLoop.ReflCovariance.classLimitV_VP_map`.

* **`setCClassLim_CB`**, **`setCClassCov_CB`**: the limit and covariance links of the classes
  `.inl k` of `QED.ChainProof.SetCPauli.ctFam`, `2 ≤ k`;
* **`setCLimitLink_of_main_cb01`**, **`setCCovLink_of_main_cb01`**: the limit and covariance
  links of (HS₆) from the per-class links of the 36 two-loop-outer classes and the two classes
  `CB0`, `CB1` (open).
-/

@[expose] public section

open Complex Matrix Filter Topology
open QED.WickModel (Params IsOnePI Contraction contractionValue₂ loopCount lineMomentum₂
  ExternalsAttached VerticesConnected externalMomentum)

namespace QED.ChainProof.SetCPauli

open QED.TwoLoop.LimitCovariance QED.ChainProof.SetCLink QED.ChainProof.SetALink
open QED.TwoLoop.Relabel QED.TwoLoop.Enumeration
open QED.ChainProof.SetAPauli (regParams regFlavors)

/-! ### The kind change in the graded model, with a constant counterterm factor -/

section KindChange

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind} (hκ : ∀ t, κ t = .gauge ∨ κ t = .gaugeCt)
  {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (C : Contraction 1 nA κ)

/-- The graded value (G₅) as an integral over `L` loop momenta, for `loopCount C = L`. -/
theorem gradedValue_eq_of_loopCount (P : Params) (D : Graded.Counterterms F)
    (g : Graded.Grading κ) {C : Contraction 1 nA κ} {L : ℕ} (hL : loopCount C = L)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin nA → Fin 4) :
    Graded.contractionValue P Φ D C g pOut pIn kIn αOut βIn μ =
      QED.TwoLoop.jointEnergyFirstIntegral L fun ℓ => (((2 * Real.pi) ^ (4 * L) : ℝ) : ℂ)⁻¹ *
        Graded.regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn
          μ := by
  subst hL
  rfl

/-- **The regulated amplitude (G₄) under the kind change**, with a constant `gaugeCt` factor `w`
and equal loop weights on the preserved flavourings. -/
theorem regulatedAmplitude_toG_const (P : Params) (D : Graded.Counterterms F) (w : ℂ)
    (hw : ∀ φ, Graded.Preserves Φ C φ → ctW hκ P D φ = w ∧
      Graded.loopWeight Φ C φ = Graded.loopWeight Φ (toG hκ C) (flavG hκ φ))
    (pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (k' : QED.WickModel.Line (toG hκ C) → Fin 4 → ℝ)
    (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4) :
    Graded.regulatedAmplitude P Φ D C 0 pIn kIn ((corrG hκ C).pull k') αOut βIn μ =
      w * Graded.regulatedAmplitude P Φ D (toG hκ C) 0 pIn kIn k' αOut βIn μ := by
  classical
  unfold Graded.regulatedAmplitude
  rw [Finset.sum_filter, Finset.sum_filter, Finset.mul_sum]
  refine Fintype.sum_equiv (flavG hκ) _ _ fun φ => ?_
  by_cases hφ : Graded.Preserves Φ C φ
  · have hφ' : Graded.Preserves Φ (toG hκ C) (flavG hκ φ) :=
      (preserves_toG_iff hκ Φ C φ).mpr hφ
    simp only [hφ, hφ', ↓reduceIte, contractionAmplitude_toG, (hw φ hφ).1, (hw φ hφ).2]
    ring
  · have hφ' : ¬ Graded.Preserves Φ (toG hκ C) (flavG hκ φ) :=
      mt (preserves_toG_iff hκ Φ C φ).mp hφ
    simp only [hφ, hφ', ↓reduceIte, mul_zero]

/-- **The graded value (G₅) under the kind change**, with a constant `gaugeCt` factor `w` and
equal loop weights on the preserved flavourings, under momentum conservation, at every `ε`. -/
theorem contractionValue_toG_const (P : Params) (D : Graded.Counterterms F) (w : ℂ)
    (hw : ∀ φ, Graded.Preserves Φ C φ → ctW hκ P D φ = w ∧
      Graded.loopWeight Φ C φ = Graded.loopWeight Φ (toG hκ C) (flavG hκ φ))
    (hA : ExternalsAttached C) (hV : VerticesConnected C) (hV' : VerticesConnected (toG hκ C))
    (hL : loopCount (toG hκ C) = loopCount C) {pOut pIn : Fin 1 → Fin 4 → ℝ}
    {kIn : Fin nA → Fin 4 → ℝ} (hmom : ∑ i, pOut i = ∑ i, pIn i + ∑ j, kIn j)
    (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4) :
    Graded.contractionValue P Φ D C 0 pOut pIn kIn αOut βIn μ =
      w * Graded.contractionValue P Φ D (toG hκ C) 0 pOut pIn kIn αOut βIn μ := by
  have hsum : ∑ v, externalMomentum C pOut pIn kIn v = 0 := by
    rw [sum_externalMomentum hA, hmom, sub_self]
  obtain ⟨M, hM, a, h⟩ := (corrG hκ C).exists_routing_change hV hV'
    (fun v => externalMomentum_toG hκ C pOut pIn kIn v) hsum rfl hL
  rw [gradedValue_eq_of_loopCount Φ P D 0 (rfl : loopCount C = _),
    gradedValue_eq_of_loopCount Φ P D 0 hL]
  have hint : ∀ ℓ, w * ((((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
      Graded.regulatedAmplitude P Φ D (toG hκ C) 0 pIn kIn
        (lineMomentum₂ (toG hκ C) pOut pIn kIn ℓ) αOut βIn μ) =
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
      Graded.regulatedAmplitude P Φ D C 0 pIn kIn
        (lineMomentum₂ C pOut pIn kIn (matAct M ℓ + a)) αOut βIn μ :=
    fun ℓ => by
      rw [← h ℓ, regulatedAmplitude_toG_const hκ Φ C P D w hw]
      ring
  have hmul : ∀ (c : ℂ) (G : (Fin (loopCount C) → Fin 4 → ℝ) → ℂ),
      QED.TwoLoop.jointEnergyFirstIntegral (loopCount C) (fun ℓ => c * G ℓ) =
        c * QED.TwoLoop.jointEnergyFirstIntegral (loopCount C) G := fun c G => by
    unfold QED.TwoLoop.jointEnergyFirstIntegral
    simp only [MeasureTheory.integral_const_mul]
  rw [← hmul]
  simp only [hint]
  exact (QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add _
    (fun ℓ => (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
      Graded.regulatedAmplitude P Φ D C 0 pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ)
      M hM a).symm

end KindChange

/-! ### Contractions of `gauge` vertices at the set (c) flavours -/

/-- **The graded value of a contraction of `gauge` vertices at the set (c) flavours** (the
electron block, no heavy lepton) is T1's value, at every `ε`. -/
theorem contractionValue_gauges_regFlavors (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ ε : ℝ)
    (D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3)) {N nA : ℕ}
    (C : Contraction 1 nA (gauges N)) (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4) :
    Graded.contractionValue { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
        (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D C 0 pOut pIn kIn αOut βIn μ =
      contractionValue₂ { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } C pOut pIn kIn αOut βIn
        μ := by
  set P : Params := { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
  have hR : QED.GradedProof.CtReaches C := fun t ht => absurd rfl ht
  rw [QED.GradedProof.contractionValue_zero_eq P P _ D C hR rfl rfl rfl rfl
    (fun _ ht => Wick.VertexKind.noConfusion ht) (fun _ ht => Wick.VertexKind.noConfusion ht)
    (fun _ ht => Wick.VertexKind.noConfusion ht)]
  rw [QED.Lepton.Proof.contractionValue₂_relabel QED.Lepton.Proof.leptonFlavorsZeroEquiv
    (Ψ := QED.Lepton.Proof.HM.t1F P) rfl P ?_ ?_ C]
  · rfl
  · rintro (i | ⟨j, _⟩)
    · rfl
    · exact j.elim0
  · rintro (i | ⟨j, _⟩)
    · rfl
    · exact j.elim0

/-! ### The relabellings -/

/-- The relabelling of `Class5.VP.rep` onto the kind change of `CBₖ`: the ends `0`, `2` of the
open line and the two bubble vertices exchanged. -/
def permCB : Equiv.Perm (Fin 5) := permK ![2, 1, 0, 4, 3] ![2, 1, 0, 4, 3]

theorem toG_repCB2 :
    toG kCB2_kinds repCB2 = relabelK permCB (fun _ => rfl) Class5.VP.rep := by
  decide +kernel

theorem toG_repCB3 :
    toG kCB3_kinds repCB3 = relabelK permCB (fun _ => rfl) Class5.VP.rep := by
  decide +kernel

theorem toG_repCB4 :
    toG kCB4_kinds repCB4 = relabelK permCB (fun _ => rfl) Class5.VP.rep := by
  decide +kernel

/-! ### The values -/

open scoped Classical in
/-- **The counterterm factor and the loop weights** of a contraction with one `gaugeCt` vertex
`t₀`, on the cycle of the external field, and one closed fermion loop through `x₀`: on every
preserved flavouring, `ctW` is `e² d₁(e⁻, 0)` and the loop weights of `C` and `toG C` agree. -/
theorem ctW_loopWeight_of_one_ct {κ : Fin 5 → Wick.VertexKind}
    (hκ : ∀ t, κ t = .gauge ∨ κ t = .gaugeCt) {C : Contraction 1 1 κ} {t₀ : Fin 5}
    (ht₀ : ∀ t, κ t = .gaugeCt ↔ t = t₀)
    (hx : C.1.1.SameCycle (.inr (fvOfG hκ t₀)) (.inl 0)) {x₀ : Wick.FermionVertex κ}
    (h₀ : ∀ i, ¬ C.1.1.SameCycle (.inl i) (.inr x₀))
    (hall : ∀ x, (∃ i, C.1.1.SameCycle x (.inl i)) ∨ C.1.1.SameCycle x (.inr x₀))
    (h₀' : ∀ i, ¬ (toG hκ C).1.1.SameCycle (.inl i) (.inr (fvG hκ x₀)))
    (hall' : ∀ x, (∃ i, (toG hκ C).1.1.SameCycle x (.inl i)) ∨
      (toG hκ C).1.1.SameCycle x (.inr (fvG hκ x₀)))
    (P : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Graded.Counterterms F)
    (φ : Graded.Flavoring F κ) (hφ : Graded.Preserves Φ C φ) :
    ctW hκ P D φ = ((P.e ^ 2 * D.d₁ Φ.openLine 0 : ℝ) : ℂ) ∧
      Graded.loopWeight Φ C φ = Graded.loopWeight Φ (toG hκ C) (flavG hκ φ) := by
  have hφ' := (preserves_toG_iff hκ Φ C φ).mpr hφ
  have hf : φ (fvOfG hκ t₀) = Φ.openLine :=
    QED.GradedProof.VP2.fermionFlavor_eq_of_sameCycle Φ hφ hx
  refine ⟨?_, ?_⟩
  · rw [ctW, Fintype.prod_eq_single t₀ fun t ht => by
      simp only [show ¬ κ t = .gaugeCt from fun h => ht ((ht₀ t).mp h), ↓reduceIte]]
    simp only [(ht₀ t₀).mpr rfl, ↓reduceIte, hf]
  · rw [loopWeight_eq_of_one_loop Φ hφ x₀ h₀ hall,
      loopWeight_eq_of_one_loop Φ hφ' (fvG hκ x₀) h₀' hall', flavG_apply,
      Equiv.symm_apply_apply]

variable {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}

/-- The counterterm factor `e² d₁(e⁻, 0)` of the classes `CB2`–`CB4` at the set (c) data. -/
noncomputable def cbW (P₀ : Params) (D : RegCt) (s : ℝ × ℝ × ℝ) : ℂ :=
  ((P₀.e ^ 2 * (shareCt D s).d₁ (.inl 0) 0 : ℝ) : ℂ)

/-- The value of a class `CBₖ` from the data of its kind change. -/
theorem value_of_toG_eq {κ : Fin 5 → Wick.VertexKind}
    (hκ : ∀ t, κ t = .gauge ∨ κ t = .gaugeCt) {C : Contraction 1 1 κ} (hC : IsOnePI C)
    (hC' : IsOnePI (toG hκ C)) (hL : loopCount (toG hκ C) = loopCount C)
    (hG : toG hκ C = relabelK permCB (fun _ => rfl) Class5.VP.rep) {t₀ : Fin 5}
    (ht₀ : ∀ t, κ t = .gaugeCt ↔ t = t₀)
    (hx : C.1.1.SameCycle (.inr (fvOfG hκ t₀)) (.inl 0)) {x₀ : Wick.FermionVertex κ}
    (h₀ : ∀ i, ¬ C.1.1.SameCycle (.inl i) (.inr x₀))
    (hall : ∀ x, (∃ i, C.1.1.SameCycle x (.inl i)) ∨ C.1.1.SameCycle x (.inr x₀))
    (h₀' : ∀ i, ¬ (toG hκ C).1.1.SameCycle (.inl i) (.inr (fvG hκ x₀)))
    (hall' : ∀ x, (∃ i, (toG hκ C).1.1.SameCycle x (.inl i)) ∨
      (toG hκ C).1.1.SameCycle x (.inr (fvG hκ x₀))) (ε : ℝ) (p' p : Fin 4 → ℝ)
    (i j μ : Fin 4) :
    Graded.contractionValue { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
        (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) (shareCt D s) C 0 (fun _ => p') (fun _ => p)
        (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) =
      cbW P₀ D s * contractionValue₂ { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
        Class5.VP.rep (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j)
        (fun _ => μ) := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  rw [contractionValue_toG_const hκ _ C _ _ (cbW P₀ D s)
    (fun φ hφ => ctW_loopWeight_of_one_ct hκ ht₀ hx h₀ hall h₀' hall' _ _ _ φ hφ) hC.1 hC.2.1
    hC'.2.1 hL (by simp), contractionValue_gauges_regFlavors, hG,
    value_relabelK _ hmom (rep_isOnePI .VP)]

/-- **The values of the bubble classes `CB2`–`CB4`**: `e² d₁(e⁻, 0)` times T1's value of the
vacuum-polarization class, at the set (c) data and every `ε`. -/
theorem cbVal_apply (ε : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (k : Fin 5) (hk : 2 ≤ k)
    (i j : Fin 4) :
    cbVal { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (shareCt D s) p' p μ k i j =
      cbW P₀ D s * contractionValue₂ { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
        Class5.VP.rep (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j)
        (fun _ => μ) := by
  fin_cases k
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact value_of_toG_eq kCB2_kinds isOnePI_repCB2 isOnePI_toG_repCB2 loopCount_toG_repCB2
      toG_repCB2 kCB2_ct cb2_cycle cb2_open cb2_all cb2_open' cb2_all' ε p' p i j μ
  · exact value_of_toG_eq kCB3_kinds isOnePI_repCB3 isOnePI_toG_repCB3 loopCount_toG_repCB3
      toG_repCB3 kCB3_ct cb3_cycle cb3_open cb3_all cb3_open' cb3_all' ε p' p i j μ
  · exact value_of_toG_eq kCB4_kinds isOnePI_repCB4 isOnePI_toG_repCB4 loopCount_toG_repCB4
      toG_repCB4 kCB4_ct cb4_cycle cb4_open cb4_all cb4_open' cb4_all' ε p' p i j μ

/-! ### Limits and covariance -/

/-- The limit of the class `CBₖ` (`2 ≤ k`), with its sign in `ctFam`. -/
noncomputable def cbLim (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) (D : RegCt) (s : ℝ × ℝ × ℝ)
    (p' p : Fin 4 → ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  (-cbW P₀ D s) • classLimitV .VP (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) p p'

/-- The class values of `CBₖ` (`2 ≤ k`) along `ε`, with their sign in `ctFam`. -/
theorem ctFam_CB_eq (k : Fin 5) (hk : 2 ≤ k) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) (ε : ℝ) :
    ctFam { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (shareCt D s) p' p μ (.inl k) i j =
      -(cbW P₀ D s * contractionValue₂ { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
        Class5.VP.rep (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j)
        (fun _ => μ)) := by
  rw [← cbVal_apply ε p' p μ k hk i j]
  rfl

theorem cbLim_apply (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    cbLim P₀ M₁ M₂ c₁ c₂ mγ Λ D s p' p μ i j =
      -(cbW P₀ D s * classLimitV .VP (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) p p' μ i j) := by
  simp only [cbLim, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, neg_mul]

/-- At admissible data and an on-shell positive-energy pair, the class `CBₖ` (`2 ≤ k`)
converges to `-e² d₁(e⁻, 0)` times the limit of the vacuum-polarization class. -/
theorem isClassLimC_CB (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) (k : Fin 5) (hk : 2 ≤ k)
    {p' p : Fin 4 → ℝ} (hpq : IsPairQ P₀.m p' p) :
    IsClassLimC ctFam P₀ M₁ M₂ c₁ c₂ mγ Λ D s (.inl k) p' p
      (cbLim P₀ M₁ M₂ c₁ c₂ mγ Λ D s p' p) := by
  obtain ⟨hM₁, hM₂, hc₁, hc₂, hmγ, hΛ, -, hm2, -, -⟩ := hA
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  have hm : 0 < P₀.m := by linarith
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  intro μ i j
  have hT : Tendsto (fun ε => contractionValue₂ { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
      Class5.VP.rep (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j)
      (fun _ => μ)) (𝓝[>] 0) (𝓝 (classLimitV .VP (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) p p' μ i j)) :=
    tendsto_nhds_limUnder (QED.TwoLoop.ClassLimit.existsUnique_tendsto_contractionValue₂_VP
      (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) hm hmγ hΛ hM₁.le hM₂.le hc₁ hc₂ hmom hp hp' hq.le
      (fun _ => i) (fun _ => j) (fun _ => μ)).exists
  rw [cbLim_apply]
  exact ((hT.const_mul (cbW P₀ D s)).neg).congr fun ε => (ctFam_CB_eq k hk p' p μ i j ε).symm

/-- **The limit links of the three classes `CB2`–`CB4`.** -/
theorem setCClassLim_CB (k : Fin 5) (hk : 2 ≤ k) : SetCClassLim ctFam P₀ (.inl k) :=
  fun _ _ _ _ _ _ _ _ hA _ _ hpq => ⟨_, isClassLimC_CB hA k hk hpq⟩

/-- **The covariance links of the three classes `CB2`–`CB4`.** -/
theorem setCClassCov_CB (k : Fin 5) (hk : 2 ≤ k) : SetCClassCov ctFam P₀ (.inl k) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA L S T h p' p hpq h0 h1 Y Z hY hZ μ
  have hpq' := isPairQ_map h hpq h0 h1
  have eY : Y = cbLim P₀ M₁ M₂ c₁ c₂ mγ Λ D s p' p := by
    funext ν
    ext i j
    exact tendsto_nhds_unique (hY ν i j) (isClassLimC_CB hA k hk hpq ν i j)
  have eZ : Z = cbLim P₀ M₁ M₂ c₁ c₂ mγ Λ D s (L *ᵥ p') (L *ᵥ p) := by
    funext ν
    ext i j
    exact tendsto_nhds_unique (hZ ν i j) (isClassLimC_CB hA k hk hpq' ν i j)
  obtain ⟨hM₁, hM₂, hc₁, hc₂, hmγ, hΛ, -, hm2, -, -⟩ := hA
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  have hm : 0 < P₀.m := by linarith
  have hv : ∀ (c : ℂ) (Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ),
      QED.Dirac.vecAct L (c • Y) μ = c • QED.Dirac.vecAct L Y μ := fun c Y => by
    simp only [QED.Dirac.vecAct, Pi.smul_apply, Finset.smul_sum, smul_comm _ c]
  rw [eY, eZ, cbLim, cbLim, hv, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul,
    QED.TwoLoop.ReflCovariance.classLimitV_VP_map (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) hm hmγ hΛ
      hM₁.le hM₂.le hc₁ hc₂ h hp hp' hq.le μ]

/-! ### The links of (HS₆) with the classes `CB2`–`CB4` discharged -/

/-- The limit links of the five classes `CBₖ`, from those of `CB0`, `CB1`. -/
theorem setCClassLim_CB_all (hCB : ∀ k : Fin 5, k < 2 → SetCClassLim ctFam P₀ (.inl k)) :
    ∀ k, SetCClassLim ctFam P₀ (.inl k) := fun k =>
  if hk : 2 ≤ k then setCClassLim_CB k hk else hCB k (not_le.mp hk)

/-- The covariance links of the five classes `CBₖ`, from those of `CB0`, `CB1`. -/
theorem setCClassCov_CB_all (hCB : ∀ k : Fin 5, k < 2 → SetCClassCov ctFam P₀ (.inl k)) :
    ∀ k, SetCClassCov ctFam P₀ (.inl k) := fun k =>
  if hk : 2 ≤ k then setCClassCov_CB k hk else hCB k (not_le.mp hk)

/-- **The limit link of (HS₆)** from the limit links of the 36 two-loop-outer classes and of the
two classes `CB0`, `CB1`. -/
theorem setCLimitLink_of_main_cb01 (hM : ∀ r, SetCClassLim mainFam P₀ r)
    (hCB : ∀ k : Fin 5, k < 2 → SetCClassLim ctFam P₀ (.inl k)) : SetCLimitLink P₀ :=
  setCLimitLink_of_main_cb hM (setCClassLim_CB_all hCB)

/-- **The covariance link of (HS₆)** from the limit and covariance links of the 36
two-loop-outer classes and of the two classes `CB0`, `CB1`. -/
theorem setCCovLink_of_main_cb01 (hM : ∀ r, SetCClassLim mainFam P₀ r)
    (hCB : ∀ k : Fin 5, k < 2 → SetCClassLim ctFam P₀ (.inl k))
    (hMc : ∀ r, SetCClassCov mainFam P₀ r)
    (hCBc : ∀ k : Fin 5, k < 2 → SetCClassCov ctFam P₀ (.inl k)) : SetCCovLink P₀ :=
  setCCovLink_of_main_cb hM (setCClassLim_CB_all hCB) hMc (setCClassCov_CB_all hCBc)

end QED.ChainProof.SetCPauli

end
