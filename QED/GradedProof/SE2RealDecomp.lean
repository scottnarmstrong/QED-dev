/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2RealLim
public import QED.GradedProof.SE2Decomp

/-!
# `SEReal` from eight class obligations

Helper level for the Phase 5 Stage 2 goal (G-ex₂) `QED.Graded.existsUnique_withLevel_one`
(decision D-57), input `SEReal`. The reality counterpart of `QED/GradedProof/SE2Decomp.lean`.

The class obligation `ClassSharp C`: at every admissible T1 parameter set `Q` whose masses are at
least `m₀ > 0`, for `0 < ν ≤ min(m_γ, Λ)` and `ν ≤ 2 m₀`, the T1 value of `C` at the self-energy
kinematics has a limit `W` below `-(m + ν)²` with `W♯ = -W` (`HasSharpLim`, phase `-1`: the
value is `1/i` times a `♯`-fixed matrix). The proof of `SE2Decomp` goes through verbatim, since
every weight in `Σ^{(4)}_ε = (1/i) ∑ sign(C)/N! · value(C, g)` and in the zero-grading reduction
(`auxW`) is real, and the level-`1` tree `-i(e⁴ d₂ p̸ + e⁴ d_m M_f)` has phase `-1`. The factor
`1/i` turns the phase into `+1`, and `seReal_of_hasSharpLim` gives `SEReal`
(`seReal_of_classes`).
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params Contraction IsOnePI loopCount lineMomentum₂)

namespace QED.GradedProof.SE2Real

open QED.Graded QED.Lepton.Proof.HM QED.TwoLoop.Relabel QED.GradedProof.SE2

/-- **The reality class obligation.** -/
def ClassSharp {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 0 κ) : Prop :=
  ∀ Q : Params, Adm Q → ∀ m₀ ν : ℝ, 0 < m₀ → m₀ ≤ Q.m → m₀ ≤ Q.M₁ → m₀ ≤ Q.M₂ → 0 < ν →
    ν ≤ min Q.mγ Q.Λ → ν ≤ 2 * m₀ →
    HasSharpLim (Q.m + ν) (-1) fun ε p α β =>
      QED.WickModel.contractionValue₂ { Q with ε := ε } C ![p] ![p] ![] ![α] ![β] ![]

/-- The class obligation passes to relabellings of 1PI contractions. -/
theorem classSharp_relabelK {N : ℕ} {κ κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N))
    (hκ : ∀ t, κ' (π t) = κ t) (C : Contraction 1 0 κ) (hC : IsOnePI C) (h : ClassSharp C) :
    ClassSharp (relabelK π hκ C) := by
  intro Q hQ m₀ ν h0 h1 h2 h3 h4 h5 h6
  refine (h Q hQ m₀ ν h0 h1 h2 h3 h4 h5 h6).congr fun p _ α β => Eventually.of_forall fun ε => ?_
  exact (contractionValue₂_relabelK_of_isOnePI _ π hκ hC (by simp) _ _ _).symm

theorem classSharp_of_order_four (hR : ClassSharp repR) (hX : ClassSharp repX)
    (hV : ClassSharp repV) (hF : ClassSharp repF) (hP0 : ClassSharp repP0)
    (hP1 : ClassSharp repP1) (hC1 : ClassSharp repC1) (hC2 : ClassSharp repC2) {N : ℕ}
    {κ : Fin N → Wick.VertexKind} (h : ∑ t, (κ t).order = 4) (C : Contraction 1 0 κ)
    (hC : IsOnePI C) : ClassSharp C :=
  induction_of_order_four (fun C => ClassSharp C)
    (fun π hκ C hC h => classSharp_relabelK π hκ C hC h) hR hX hV hF hP0 hP1 hC1 hC2 h C hC

/-- The constant covariant matrix `-i(a p̸ + b)` with real `a, b` has phase `-1`. -/
theorem HasSharpLim.const_seMat {T : ℝ} (a b : ℝ) :
    HasSharpLim T (-1) fun _ p α β => seMat (-I * (a : ℂ)) (-I * (b : ℂ)) p α β := by
  refine ⟨fun p => seMat (-I * (a : ℂ)) (-I * (b : ℂ)) p, fun p _ =>
    ⟨fun _ _ => tendsto_const_nhds, ?_⟩⟩
  simp only [seMat]
  rw [sharp_seForm]
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, neg_neg, neg_smul, one_smul,
    smul_add, neg_mul]

/-- **The zero grading.** -/
theorem hasSharpLim_zero (hcls : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 0 κ),
      ∑ t, (κ t).order = 4 → IsOnePI C → ClassSharp C)
    (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (f : F) (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hPV₁ : ∑ g, Φ.coeff g = 0)
    (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (h4 : ∑ t, (κ t).order = 4) (C : Contraction 1 0 κ) (hC : IsOnePI C) :
    HasSharpLim (Φ.mass f + min (min P.mγ P.Λ) (2 * m₀)) (-1) fun ε p α β =>
      contractionValue { P with ε := ε } { Φ with openLine := f } D C 0 ![p] ![p] ![] ![α] ![β]
        ![] := by
  set ν := min (min P.mγ P.Λ) (2 * m₀) with hνdef
  have hν0 : 0 < ν := lt_min (lt_min hmγ hΛ) (by linarith)
  have hν : ν ≤ min P.mγ P.Λ := min_le_left _ _
  have hν2 : ν ≤ 2 * m₀ := min_le_right _ _
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  have hS := isSimple_of_order_four h4 C hC
  have hCt := ctReaches_of_order_four h4 C hC
  have hCI := classInt_of_order_four classInt_repR classInt_repX classInt_repV classInt_repF
    classInt_repP0 classInt_repP1 classInt_repC1 classInt_repC2 h4 C hC
  have hCF := hcls C h4 hC
  have hP1 : ∀ ε : ℝ, 0 < ({ P with ε := ε } : Params).mγ ∧ 0 < ({ P with ε := ε } : Params).Λ :=
    fun _ => ⟨hmγ, hΛ⟩
  by_cases hL : HasLoop C
  · obtain ⟨X, hlt⟩ : ∃ X : ℝ, ∀ g, Φ.mass g < X := ⟨1 + ∑ g, Φ.mass g, fun g => by
      have := Finset.single_le_sum (f := Φ.mass) (fun g _ => (hpos g).le) (Finset.mem_univ g)
      linarith⟩
    have hF : ∀ g, HasSharpLim (Φ.mass f + ν) (-1) fun ε p α β =>
        QED.WickModel.contractionValue₂ { auxT1 { P with ε := 1 } Φ D f X g with ε := ε } C
          ![p] ![p] ![] ![α] ![β] ![] := fun g =>
      hCF _ (adm_auxT1 { P with ε := 1 } Φ D f one_pos hmγ hΛ (hpos f) g (hpos g) (hlt g)) m₀ ν
        hm₀ (hmass f)
        (hmass g) ((hmass g).trans (hlt g).le) hν0 hν hν2
    refine (HasSharpLim.sum Finset.univ fun g _ => (hF g).const_mul_real (auxW Φ f X g)).congr
      fun p _ α β => ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    symm
    unfold contractionValue
    rw [funext (integrand_loop_eq { P with ε := ε } Φ D f hPV₁ hPV₂ hS hCt hL hlt hpos p α β)]
    exact SE2.jointEnergyFirstIntegral_sum Finset.univ _ _ fun g _ => hCI _
      (adm_auxT1 { P with ε := ε } Φ D f hε hmγ hΛ (hpos f) g (hpos g) (hlt g)) p α β
  · have hF : HasSharpLim (Φ.mass f + ν) (-1) fun ε p α β =>
        QED.WickModel.contractionValue₂ { refT1 { P with ε := 1 } Φ D f with ε := ε } C
          ![p] ![p] ![] ![α] ![β] ![] :=
      hCF _ (adm_refT1 { P with ε := 1 } Φ D f one_pos hmγ hΛ (hpos f)) m₀ ν hm₀ (hmass f)
        (by simp only [refT1]; linarith [hmass f, hpos f])
        (by simp only [refT1]; linarith [hmass f, hpos f]) hν0 hν hν2
    refine hF.congr fun p _ α β => Eventually.of_forall fun ε => ?_
    symm
    unfold contractionValue
    congr 1
    funext ℓ
    have hz := regulatedAmplitude_zero_eq { P with ε := ε } (seParams₂ { P with ε := ε } Φ D f)
      { Φ with openLine := f } D C hCt rfl rfl rfl rfl (fun _ _ => rfl)
      (fun _ _ => ⟨rfl, rfl, rfl⟩) (fun _ _ => rfl) ![p] ![] (lineMomentum₂ C ![p] ![p] ![] ℓ)
      ![α] ![β] ![]
    rw [hz, regulatedAmplitude₂_of_not_hasLoop _ _ hS hL]
    exact congrArg _ (regulatedAmplitude₂_refT1 { P with ε := ε } Φ D f hS _ _ _ _ _ _ hL).symm

/-- **A nonzero grading**: the `fermionCt` tree at level `1`, with an `ε`-independent covariant
value. -/
theorem hasSharpLim_tree (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (T : ℝ) {N : ℕ}
    {κ : Fin N → Wick.VertexKind} (g : Grading κ) (hg0 : g ≠ 0) (hg : gradedOrder κ g = 4)
    (C : Contraction 1 0 κ) (hC : IsOnePI C) :
    HasSharpLim T (-1) fun ε p α β =>
      contractionValue { P with ε := ε } { Φ with openLine := f } D C g ![p] ![p] ![] ![α] ![β]
        ![] := by
  obtain ⟨t, ht⟩ : ∃ t : CtVertex κ, 1 ≤ g t := by
    obtain ⟨t, ht⟩ := Function.ne_iff.1 hg0
    exact ⟨t, Nat.one_le_iff_ne_zero.2 ht⟩
  have h2 := Finset.single_le_sum (f := fun t : CtVertex κ => 2 * g t)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
  have h4 := hg
  unfold gradedOrder at h4
  have hle : ∑ s, (κ s).order ≤ 2 := by omega
  have hN := QED.ChainProof.Quick.le_sum_order κ
  obtain _ | _ | _ | N := N
  · exact t.1.elim0
  · obtain ⟨k, rfl⟩ : ∃ k, κ = QED.WickModel.oneVertex k :=
      ⟨κ 0, QED.WickModel.eq_oneVertex κ⟩
    have hk : k = .fermionCt := by
      by_contra hk
      exact QED.WickModel.not_isOnePI_oneVertex_selfEnergy hk C hC
    subst hk
    have hC' := hC
    rw [QED.WickModel.isOnePI_iff_eq_selfEnergyTree] at hC'
    subst hC'
    have hord : ∑ s, (QED.WickModel.oneVertex Wick.VertexKind.fermionCt s).order = 2 := by
      decide
    have : Subsingleton (CtVertex (QED.WickModel.oneVertex Wick.VertexKind.fermionCt)) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim (α := Fin 1) _ _)⟩
    have hsub : ∀ s : CtVertex (QED.WickModel.oneVertex Wick.VertexKind.fermionCt), s = t :=
      fun s => Subsingleton.elim _ _
    have hgt : ∀ s : CtVertex (QED.WickModel.oneVertex Wick.VertexKind.fermionCt), g s = 1 := by
      intro s
      rw [hsub s]
      rw [hord, Fintype.sum_subsingleton _ t] at h4
      omega
    have hR := QED.Lepton.Proof.reaches_of_one_zero (by rw [hord]; norm_num) _ hC
    refine (HasSharpLim.const_seMat (P.e ^ 4 * D.d₂ f 1) (P.e ^ 4 * D.dm f 1 * Φ.mass f)).congr
        fun p _ α β => Eventually.of_forall fun ε => ?_
    rw [contractionValue_eq_of_grading { P with ε := ε } (SE2.treeParams P Φ D f ε)
      { Φ with openLine := f } D _
      (ctReaches_of_reaches hR) g rfl rfl rfl rfl
      (fun _ h => absurd h (by simp [QED.WickModel.oneVertex]))
      (fun s _ => by refine ⟨?_, ?_, rfl⟩ <;> simp [SE2.treeParams, hgt s])
      (fun _ h => absurd h (by simp [QED.WickModel.oneVertex]))]
    rw [lepton_contractionValue₂_eq_of_reaches (SE2.treeParams P Φ D f ε)
      { Φ with openLine := f } rfl _ hR,
      QED.TwoLoop.contractionValue₂_eq_contractionValue_of_loopCount_le_one
        (SE2.treeParams P Φ D f ε) _
        (QED.TwoLoop.LoopBound.loopCount_le_one_of_order (K := 2) (by rw [hord])
          (by norm_num) _ hC),
      QED.WickModel.contractionValue_selfEnergyTree]
    simp only [seMat, SE2.treeParams, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero]
    push_cast
    ring
  · obtain rfl := QED.WickModel.eq_gauge2_of_sum_order_le hle
    exact (t.2 rfl).elim
  · omega

/-! ### The self-energy -/

/-- **The order-`e⁴` self-energy has a `♯`-fixed limit**, from the eight class obligations. -/
theorem hasSharpLim_selfEnergyPart (hcls : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}
      (C : Contraction 1 0 κ), ∑ t, (κ t).order = 4 → IsOnePI C → ClassSharp C)
    (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (f : F) (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hPV₁ : ∑ g, Φ.coeff g = 0)
    (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) :
    HasSharpLim (Φ.mass f + min (min P.mγ P.Λ) (2 * m₀)) 1 fun ε p α β =>
      selfEnergyPart { P with ε := ε } Φ D f 2 p α β := by
  classical
  have h : HasSharpLim (Φ.mass f + min (min P.mγ P.Λ) (2 * m₀)) (-(-1)) fun ε p α β =>
      (1 / I) * onePIPart { P with ε := ε } { Φ with openLine := f } D 1 0 (2 * 2) ![p] ![p] ![]
        ![α] ![β] ![] := by
    refine HasSharpLim.mul_inv_I ?_
    unfold onePIPart selectedPart
    refine HasSharpLim.sum _ fun N _ => HasSharpLim.const_mul_conj _ (by simp)
      (HasSharpLim.sum _ fun κ _ => HasSharpLim.sum _ fun g hg => HasSharpLim.sum _ fun C hC =>
        HasSharpLim.const_mul_conj _ (by simp) ?_)
    have hg4 := (Finset.mem_filter.1 hg).2
    have hC' := (Finset.mem_filter.1 hC).2
    by_cases hg0 : g = 0
    · subst hg0
      exact hasSharpLim_zero hcls P Φ D f m₀ hm₀ hmass hmγ hΛ hPV₁ hPV₂
        (by rwa [gradedOrder_zero] at hg4) C hC'
    · exact hasSharpLim_tree P Φ D f _ g hg0 hg4 C hC'
  rw [neg_neg] at h
  exact h.congr fun p _ α β => Eventually.of_forall fun ε => rfl

/-- **`SEReal` from the eight class obligations.** -/
theorem seReal_of_classes (hR : ClassSharp repR) (hX : ClassSharp repX)
    (hV : ClassSharp repV) (hF : ClassSharp repF) (hP0 : ClassSharp repP0)
    (hP1 : ClassSharp repP1) (hC1 : ClassSharp repC1) (hC2 : ClassSharp repC2) (P : Params)
    {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F)
    (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hPV₁ : ∑ g, Φ.coeff g = 0) (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) :
    GEx2.SEReal P Φ D f :=
  seReal_of_hasSharpLim P Φ D f (lt_min (lt_min hmγ hΛ) (by linarith))
    (hm₀.trans_le (hmass f))
    (hasSharpLim_selfEnergyPart (fun C h4 hC => classSharp_of_order_four hR hX hV hF hP0 hP1 hC1
      hC2 h4 C hC) P Φ D f m₀ hm₀ hmass hmγ hΛ hPV₁ hPV₂)

end QED.GradedProof.SE2Real

end
