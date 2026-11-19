/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2Decomp
public import QED.GradedProof.VP2Weights
public import QED.Frozen.Graded.CountertermsWithLevel

/-!
# The order-`e⁴` self-energy is affine in the level-`1` fermion counterterms

Helper level for the Phase 5 Stage 2 goal (G-ex₂) `QED.Graded.existsUnique_withLevel_one`
(decision D-57). The order-`4` self-energy (G₈ₛ) of flavour `f` is the zero-grading sum, which
reads only the level-`0` data (`QED.GradedProof.contractionValue_zero_congr`), minus the
level-`1` `fermionCt` tree `e⁴ d₂ f 1 p̸ + e⁴ d_m f 1 M_f`.

## Main statements

* `QED.GradedProof.GEx2.seTreeSum_eq`: the nonzero gradings give `-i` times the tree.
* `QED.GradedProof.GEx2.selfEnergyPart_two_add_tree`: for data agreeing at level `0`,
  `Σ⁽⁴⁾(D) + T(D) = Σ⁽⁴⁾(D') + T(D')`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.GEx2

open QED.Graded QED.GradedProof.SE2
open QED.WickModel (Params Contraction IsOnePI fermionSign)

/-- The level-`1` `fermionCt` tree of flavour `f`: `e⁴ d₂ f 1 p̸ + e⁴ d_m f 1 M_f`. -/
noncomputable def seTree (P : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Counterterms F)
    (f : F) (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((P.e ^ 4 * D.d₂ f 1 : ℝ) : ℂ) • Dirac.slash p +
    ((P.e ^ 4 * D.dm f 1 * Φ.mass f : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- A nonzero grading of graded order `4` with a 1PI one-fermion contraction has one vertex. -/
theorem eq_one_of_grading_ne_zero_se {N : ℕ} {κ : Fin N → Wick.VertexKind} {g : Grading κ}
    (hg0 : g ≠ 0) (hg : gradedOrder κ g = 4) : N = 1 := by
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
  · rfl
  · obtain rfl := QED.WickModel.eq_gauge2_of_sum_order_le hle
    exact (t.2 rfl).elim
  · omega

/-- The grading `1` of the single `fermionCt` vertex. -/
def gOneF : Grading (QED.WickModel.oneVertex .fermionCt) := fun _ => 1

theorem eq_gOneF {g : Grading (QED.WickModel.oneVertex .fermionCt)}
    (hg : gradedOrder (QED.WickModel.oneVertex .fermionCt) g = 4) : g = gOneF := by
  have hsub : ∀ s t : CtVertex (QED.WickModel.oneVertex .fermionCt), s = t :=
    fun s t => Subtype.ext (Subsingleton.elim (α := Fin 1) _ _)
  have hord : ∑ s, (QED.WickModel.oneVertex Wick.VertexKind.fermionCt s).order = 2 := by decide
  unfold gradedOrder at hg
  rw [hord] at hg
  funext t
  have : ∑ s : CtVertex (QED.WickModel.oneVertex .fermionCt), 2 * g s = 2 * g t := by
    rw [Fintype.sum_eq_single t fun s hs => absurd (hsub s t) hs]
  simp only [gOneF]
  omega

open scoped Classical in
/-- **The nonzero gradings of the order-`4` self-energy: the level-`1` `fermionCt` tree.** -/
theorem seTreeSum_eq (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (f : F) (p : Fin 4 → ℝ) (α β : Fin 4) :
    (∑ N ∈ Finset.range (4 + 1), (N.factorial : ℂ)⁻¹ *
      ∑ κ : Fin N → Wick.VertexKind,
        ∑ g ∈ (Fintype.piFinset fun _ : CtVertex κ => Finset.range (4 + 1)).filter
            (fun g => gradedOrder κ g = 4 ∧ g ≠ 0),
          ∑ C ∈ (Finset.univ : Finset (Contraction 1 0 κ)).filter (fun C => IsOnePI C),
            ((fermionSign C : ℤ) : ℂ) *
              contractionValue P { Φ with openLine := f } D C g ![p] ![p] ![] ![α] ![β] ![]) =
      -I * seTree P Φ D f p α β := by
  have hzero : ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind) (g : Grading κ),
      (g ∈ (Fintype.piFinset fun _ : CtVertex κ => Finset.range (4 + 1)).filter
        (fun g => gradedOrder κ g = 4 ∧ g ≠ 0)) →
      ∀ C ∈ (Finset.univ : Finset (Contraction 1 0 κ)).filter (fun C => IsOnePI C),
        N = 1 ∧ ∀ h : N = 1, κ = h ▸ QED.WickModel.oneVertex .fermionCt := by
    intro N κ g hg C hC
    obtain ⟨-, hg4, hg0⟩ := Finset.mem_filter.1 hg
    have hC' := (Finset.mem_filter.1 hC).2
    have h1 := eq_one_of_grading_ne_zero_se hg0 hg4
    refine ⟨h1, fun h => ?_⟩
    subst h
    obtain ⟨k0, rfl⟩ : ∃ k0, κ = QED.WickModel.oneVertex k0 :=
      ⟨κ 0, QED.WickModel.eq_oneVertex κ⟩
    by_contra hk
    exact QED.WickModel.not_isOnePI_oneVertex_selfEnergy (fun h => hk (by rw [h])) C hC'
  rw [Finset.sum_eq_single 1]
  · rw [Finset.sum_eq_single (QED.WickModel.oneVertex .fermionCt)]
    · rw [Finset.sum_eq_single gOneF]
      · simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_mul]
        have hord : ∑ s, (QED.WickModel.oneVertex Wick.VertexKind.fermionCt s).order = 2 := by
          decide
        have hv : ∀ C : Contraction 1 0 (QED.WickModel.oneVertex .fermionCt), IsOnePI C →
            contractionValue P { Φ with openLine := f } D C gOneF ![p] ![p] ![] ![α] ![β] ![] =
              QED.WickModel.contractionValue (treeParams P Φ D f P.ε) C ![p] ![p] ![] ![α] ![β]
                ![] := by
          intro C hC
          have hR := QED.Lepton.Proof.reaches_of_one_zero (by rw [hord]; norm_num) _ hC
          rw [contractionValue_eq_of_grading P (treeParams P Φ D f P.ε) { Φ with openLine := f }
            D C (ctReaches_of_reaches hR) gOneF rfl rfl rfl rfl
            (fun _ h => absurd h (by simp [QED.WickModel.oneVertex]))
            (fun s _ => by refine ⟨?_, ?_, rfl⟩ <;> simp [treeParams, gOneF])
            (fun _ h => absurd h (by simp [QED.WickModel.oneVertex]))]
          rw [lepton_contractionValue₂_eq_of_reaches (treeParams P Φ D f P.ε)
              { Φ with openLine := f } rfl _ hR,
            QED.TwoLoop.contractionValue₂_eq_contractionValue_of_loopCount_le_one
              (treeParams P Φ D f P.ε) _
              (QED.TwoLoop.LoopBound.loopCount_le_one_of_order (K := 2) (by rw [hord])
                (by norm_num) _ hC)]
        rw [Finset.sum_congr rfl fun C hC => by rw [hv C (Finset.mem_filter.1 hC).2]]
        rw [QED.WickModel.sum_isOnePI_selfEnergyTree (treeParams P Φ D f P.ε) ![p] ![p] ![]
          ![α] ![β] ![]]
        simp only [seTree, treeParams, Matrix.cons_val_zero]
      · intro g hg hne
        exact absurd (eq_gOneF (Finset.mem_filter.1 hg).2.1) hne
      · intro h
        refine absurd (Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun _ => by simp [gOneF],
          by decide, fun h0 => ?_⟩) h
        have := congrFun h0 ⟨0, by simp [QED.WickModel.oneVertex]⟩
        simp [gOneF] at this
    · intro κ _ hκ
      refine Finset.sum_eq_zero fun g hg => Finset.sum_eq_zero fun C hC => ?_
      exact absurd ((hzero 1 κ g hg C hC).2 rfl) hκ
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro N _ hN
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun κ _ => Finset.sum_eq_zero fun g hg =>
      Finset.sum_eq_zero fun C hC => ?_)
    exact absurd (hzero N κ g hg C hC).1 hN
  · intro h
    simp at h

/-- **The order-`4` self-energy plus the level-`1` tree reads only the level-`0` data.** -/
theorem selfEnergyPart_two_add_tree (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D D' : Counterterms F) (h₁ : ∀ f, D.d₁ f 0 = D'.d₁ f 0)
    (h₂ : ∀ f, D.d₂ f 0 = D'.d₂ f 0) (hm : ∀ f, D.dm f 0 = D'.dm f 0) (h₃ : D.d₃ 0 = D'.d₃ 0)
    (f : F) (p : Fin 4 → ℝ) (α β : Fin 4) :
    selfEnergyPart P Φ D f 2 p α β + seTree P Φ D f p α β =
      selfEnergyPart P Φ D' f 2 p α β + seTree P Φ D' f p α β := by
  classical
  have key : ∀ E : Counterterms F, selfEnergyPart P Φ E f 2 p α β + seTree P Φ E f p α β =
      (1 / I) * ∑ N ∈ Finset.range (4 + 1), (N.factorial : ℂ)⁻¹ *
        ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
            (fun κ => ∑ t, (κ t).order = 4),
          ∑ C ∈ (Finset.univ : Finset (Contraction 1 0 κ)).filter (fun C => IsOnePI C),
            ((fermionSign C : ℤ) : ℂ) *
              contractionValue P { Φ with openLine := f } E C 0 ![p] ![p] ![] ![α] ![β] ![] := by
    intro E
    simp only [selfEnergyPart, Matrix.of_apply, onePIPart]
    rw [show 2 * 2 = 4 from rfl,
      QED.GradedProof.VP2.selectedPart_split P _ E 1 0 (fun C => IsOnePI C) 4,
      seTreeSum_eq P Φ E f p α β, one_div, mul_add, ← mul_assoc,
      show (I⁻¹ * -I : ℂ) = -1 by rw [mul_neg, inv_mul_cancel₀ I_ne_zero]]
    ring
  rw [key D, key D']
  refine congrArg (fun z => (1 / I) * z) ?_
  refine Finset.sum_congr rfl fun N _ => congrArg _ (Finset.sum_congr rfl fun κ _ =>
    Finset.sum_congr rfl fun C _ => ?_)
  rw [contractionValue_zero_congr P _ D D' h₁ h₂ hm h₃]

end QED.GradedProof.GEx2

end
