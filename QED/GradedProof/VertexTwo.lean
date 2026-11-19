/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.VertexPart
public import QED.Frozen.Lepton.VertexOrderFive
public import QED.GradedProof.EmbedOrder
import QED.GradedProof.LevelOneCharge
import QED.WickModel.Compatibility
import QED.Wick.ClassificationSmall
import QED.Wick.Classification
import QED.ChainProof.QuickOrder
import QED.ChainProof.QuickMeaning
import QED.TwoLoop.OneLoopEmbedding
import QED.TwoLoop.LoopBound

/-!
# The graded order-`e⁵` vertex

Helper proof of the Phase 5 Stage 2 goal (E-G₃) `QED.Graded.vertexPart_two_eq` (decision D-57),
as `QED.GradedProof.vertexPart_two_eq'`.

* `levelZero D`: the data `D` with the levels `≥ 1` removed. By (E-G₁)
  (`onePIPart_eq_onePIFunction₂_sub'`) its order-`5` vertex part is (F₉).
* The difference of the two order-`5` parts is the sum of the terms with a nonzero grading
  (at the zero grading only level `0` is read, `contractionValue_zero_congr`; with a nonzero
  grading the terms of `levelZero D` vanish, `contractionValue_eq_zero_of_level`).
* A 1PI vertex contraction with a nonzero grading of graded order `5` has total order `≤ 3`, so it
  is the tree of one `gaugeCt` vertex of level `1` (`eq_one_of_level`, `eq_gaugeCt_of_level`,
  `grading_eq_one`), by packet 5's classification of the orders `≤ 3`.
* Its value is the tree `i e⁴ d₁ e γ^μ` (`sum_tree_level_one`), through the flavour model at a
  general grading (`contractionValue_eq_of_grading`), T1 and packet 5's `sum_isOnePI_gaugeCt`.
-/

@[expose] public section

open Complex
open QED.WickModel (Params Contraction IsOnePI fermionSign Line)
open QED.Graded

namespace QED.GradedProof

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### The value at a general grading -/

open scoped Classical in
/-- The graded amplitude (G₃) at the grading `g` of a flavouring of the flavour model is the
amplitude (F₅), when the parameters carry the open-line data of the levels present. -/
theorem contractionAmplitude_eq_of_grading (P P' : Params) {F : Type} (Φ : Lepton.Flavors F)
    (D : Counterterms F) (C : Contraction nf nA κ) (ψ : Lepton.Flavoring Φ κ) (g : Grading κ)
    (he : P'.e = P.e) (hmγ : P'.mγ = P.mγ) (hΛ : P'.Λ = P.Λ) (hε : P'.ε = P.ε)
    (hG : ∀ t : CtVertex κ, κ t.1 = .gaugeCt →
      P'.δ₁ = P.e ^ (2 * (g t + 1)) * D.d₁ Φ.openLine (g t))
    (hF : ∀ t : CtVertex κ, κ t.1 = .fermionCt →
      P'.δ₂ = P.e ^ (2 * (g t + 1)) * D.d₂ Φ.openLine (g t) ∧
      P'.δm = P.e ^ (2 * (g t + 1)) * D.dm Φ.openLine (g t) ∧ P'.m = Φ.mass Φ.openLine)
    (hP : ∀ t : CtVertex κ, κ t.1 = .photonCt →
      P'.δ₃ = P.e ^ (2 * (g t + 1)) * D.d₃ (g t))
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionAmplitude P Φ D C ψ.1 g pIn kIn k αOut βIn μ =
      Lepton.contractionAmplitude₂ P' Φ C ψ pIn kIn k αOut βIn μ := by
  unfold contractionAmplitude Lepton.contractionAmplitude₂
  rw [he, hmγ, hΛ, hε]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => ?_
  refine congrArg₂ _ rfl (congrArg₂ _ (congrArg₂ _ ?_ rfl) rfl)
  refine Finset.prod_congr rfl fun t _ => ?_
  by_cases hg : κ t = .gauge
  · exact vertexFactor_of_gauge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t hg
  dsimp only
  rw [dite_eq_right hg]
  by_cases hp : κ t = .photonCt
  · rw [dite_eq_left hp]
    exact vertexFactor_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t (fun h => by simp_all)
      (fun h => by simp_all) fun _ => (hP ⟨t, hg⟩ hp).symm
  · have hψ : ψ.1 ⟨t, hp⟩ = Φ.openLine := ψ.2 ⟨t, hp⟩ hg
    rw [dite_eq_right hp, hψ]
    refine vertexFactor_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t
      (fun h => (hG ⟨t, hg⟩ h).symm) (fun h => ?_) fun h => absurd h hp
    obtain ⟨h₂, hm, hM⟩ := hF ⟨t, hg⟩ h
    exact ⟨h₂.symm, hm.symm, hM.symm⟩

open scoped Classical in
/-- `regulatedAmplitude_zero_eq` at a general grading. -/
theorem regulatedAmplitude_eq_of_grading (P P' : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (C : Contraction nf nA κ) (hC : CtReaches C)
    (g : Grading κ) (he : P'.e = P.e) (hmγ : P'.mγ = P.mγ) (hΛ : P'.Λ = P.Λ) (hε : P'.ε = P.ε)
    (hG : ∀ t : CtVertex κ, κ t.1 = .gaugeCt →
      P'.δ₁ = P.e ^ (2 * (g t + 1)) * D.d₁ Φ.openLine (g t))
    (hF : ∀ t : CtVertex κ, κ t.1 = .fermionCt →
      P'.δ₂ = P.e ^ (2 * (g t + 1)) * D.d₂ Φ.openLine (g t) ∧
      P'.δm = P.e ^ (2 * (g t + 1)) * D.dm Φ.openLine (g t) ∧ P'.m = Φ.mass Φ.openLine)
    (hP : ∀ t : CtVertex κ, κ t.1 = .photonCt →
      P'.δ₃ = P.e ^ (2 * (g t + 1)) * D.d₃ (g t))
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    regulatedAmplitude P Φ D C g pIn kIn k αOut βIn μ =
      Lepton.regulatedAmplitude₂ P' Φ C pIn kIn k αOut βIn μ := by
  unfold regulatedAmplitude Lepton.regulatedAmplitude₂
  symm
  refine Finset.sum_bij (fun ψ _ => ψ.1) (fun ψ hψ => ?_) (fun ψ _ ψ' _ h => Subtype.ext h)
    (fun φ hφ => ?_) (fun ψ _ => ?_)
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
      (preserves_val_iff Φ C ψ).2 (Finset.mem_filter.1 hψ).2⟩
  · have hφ' := (Finset.mem_filter.1 hφ).2
    refine ⟨⟨φ, fun t ht => eq_openLine_of_ctReaches hC hφ' t ht⟩, ?_, rfl⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (preserves_val_iff Φ C _).1 hφ'⟩
  · rw [loopWeight_val, contractionAmplitude_eq_of_grading P P' Φ D C ψ g he hmγ hΛ hε hG hF hP]

open scoped Classical in
/-- `contractionValue_zero_eq` at a general grading. -/
theorem contractionValue_eq_of_grading (P P' : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (C : Contraction nf nA κ) (hC : CtReaches C)
    (g : Grading κ) (he : P'.e = P.e) (hmγ : P'.mγ = P.mγ) (hΛ : P'.Λ = P.Λ) (hε : P'.ε = P.ε)
    (hG : ∀ t : CtVertex κ, κ t.1 = .gaugeCt →
      P'.δ₁ = P.e ^ (2 * (g t + 1)) * D.d₁ Φ.openLine (g t))
    (hF : ∀ t : CtVertex κ, κ t.1 = .fermionCt →
      P'.δ₂ = P.e ^ (2 * (g t + 1)) * D.d₂ Φ.openLine (g t) ∧
      P'.δm = P.e ^ (2 * (g t + 1)) * D.dm Φ.openLine (g t) ∧ P'.m = Φ.mass Φ.openLine)
    (hP : ∀ t : CtVertex κ, κ t.1 = .photonCt →
      P'.δ₃ = P.e ^ (2 * (g t + 1)) * D.d₃ (g t))
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionValue P Φ D C g pOut pIn kIn αOut βIn μ =
      Lepton.contractionValue₂ P' Φ C pOut pIn kIn αOut βIn μ := by
  unfold contractionValue Lepton.contractionValue₂
  simp only [regulatedAmplitude_eq_of_grading P P' Φ D C hC g he hmγ hΛ hε hG hF hP]

/-- At the zero grading the value (G₅) reads only the level-`0` data. -/
theorem contractionValue_zero_congr (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D D' : Counterterms F) (h₁ : ∀ f, D.d₁ f 0 = D'.d₁ f 0)
    (h₂ : ∀ f, D.d₂ f 0 = D'.d₂ f 0) (hm : ∀ f, D.dm f 0 = D'.dm f 0) (h₃ : D.d₃ 0 = D'.d₃ 0)
    (C : Contraction nf nA κ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionValue P Φ D C 0 pOut pIn kIn αOut βIn μ =
      contractionValue P Φ D' C 0 pOut pIn kIn αOut βIn μ := by
  have ha : ∀ φ k, contractionAmplitude P Φ D C φ 0 pIn kIn k αOut βIn μ =
      contractionAmplitude P Φ D' C φ 0 pIn kIn k αOut βIn μ := by
    intro φ k
    unfold contractionAmplitude
    simp only [Pi.zero_apply, dite_eq_ite, ite_self, h₁, h₂, hm, h₃]
  have hr : ∀ k, regulatedAmplitude P Φ D C 0 pIn kIn k αOut βIn μ =
      regulatedAmplitude P Φ D' C 0 pIn kIn k αOut βIn μ := fun k =>
    Finset.sum_congr rfl fun φ _ => by rw [ha]
  unfold contractionValue
  simp only [hr]

/-! ### The data without the levels `≥ 1` -/

/-- The data `D` with the levels `≥ 1` removed. -/
def levelZero {F : Type} (D : Counterterms F) : Counterterms F where
  d₁ f k := if k = 0 then D.d₁ f 0 else 0
  d₂ f k := if k = 0 then D.d₂ f 0 else 0
  dm f k := if k = 0 then D.dm f 0 else 0
  d₃ k := if k = 0 then D.d₃ 0 else 0

/-! ### The 1PI vertex contractions with a nonzero grading of graded order `5` -/

theorem exists_level_of_ne_zero {g : Grading κ} (hg : g ≠ 0) : ∃ t : CtVertex κ, 1 ≤ g t := by
  obtain ⟨t, ht⟩ := Function.ne_iff.1 hg
  exact ⟨t, Nat.one_le_iff_ne_zero.2 ht⟩

theorem sum_order_le_three {g : Grading κ} (hg : g ≠ 0) (h5 : gradedOrder κ g = 5) :
    ∑ t, (κ t).order ≤ 3 := by
  obtain ⟨t, ht⟩ := exists_level_of_ne_zero hg
  have h := Finset.single_le_sum (f := fun t : CtVertex κ => 2 * g t) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ t)
  unfold gradedOrder at h5
  omega

/-- Such a contraction has one vertex. -/
theorem eq_one_of_level {g : Grading κ} (hg : g ≠ 0) (h5 : gradedOrder κ g = 5)
    (C : Contraction 1 1 κ) (hC : IsOnePI C) : N = 1 := by
  have h3 := sum_order_le_three hg h5
  obtain ⟨t, -⟩ := exists_level_of_ne_zero hg
  have hN := QED.ChainProof.Quick.le_sum_order κ
  obtain _ | _ | _ | _ | N := N
  · exact t.1.elim0
  · rfl
  · obtain ⟨C₀, rfl⟩ := (QED.WickModel.contractionEquiv κ).surjective C
    exact absurd (QED.WickModel.isOnePI_contractionEquiv_iff.1 hC)
      (Wick.not_isOnePI_of_fin_two κ h3 C₀)
  · obtain rfl := Wick.eq_gauge3_of_sum_order_le h3
    exact absurd rfl t.2
  · omega

/-- Such a contraction with one vertex is the `gaugeCt` vertex. -/
theorem eq_gaugeCt_of_level {κ : Fin 1 → Wick.VertexKind} {g : Grading κ} (hg : g ≠ 0)
    (h5 : gradedOrder κ g = 5) : κ = fun _ => .gaugeCt := by
  obtain ⟨t, -⟩ := exists_level_of_ne_zero hg
  have hκ : κ = fun _ => κ 0 := funext fun s => by rw [Subsingleton.elim s 0]
  have hk : κ 0 ≠ .gauge := by
    have := t.2
    rwa [Subsingleton.elim t.1 0] at this
  unfold gradedOrder at h5
  rw [Fin.sum_univ_one, ← Finset.mul_sum] at h5
  suffices h0 : κ 0 = .gaugeCt by rw [hκ, h0]
  rcases hk0 : κ 0 <;> rw [hk0] at h5 hk <;> simp [Wick.VertexKind.order] at h5 hk ⊢ <;> omega

theorem gradedOrder_gaugeCt_one :
    gradedOrder (fun _ : Fin 1 => Wick.VertexKind.gaugeCt) (fun _ => 1) = 5 := by
  have : Subsingleton (CtVertex fun _ : Fin 1 => Wick.VertexKind.gaugeCt) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  unfold gradedOrder
  rw [Fintype.sum_subsingleton _ ⟨0, by decide⟩]
  simp [Wick.VertexKind.order]

/-- Its grading is level `1`. -/
theorem grading_eq_one {g : Grading fun _ : Fin 1 => Wick.VertexKind.gaugeCt}
    (h5 : gradedOrder (fun _ : Fin 1 => Wick.VertexKind.gaugeCt) g = 5) : g = fun _ => 1 := by
  have : Subsingleton (CtVertex fun _ : Fin 1 => Wick.VertexKind.gaugeCt) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  unfold gradedOrder at h5
  rw [Fintype.sum_subsingleton _ (0 : Fin 1),
    Fintype.sum_subsingleton _ (⟨0, by decide⟩ : CtVertex fun _ : Fin 1 => .gaugeCt)] at h5
  change 3 + _ = 5 at h5
  funext t
  rw [Subsingleton.elim t ⟨0, by decide⟩]
  omega

/-! ### The level-`1` tree -/

open scoped Classical in
/-- **The level-`1` vertex counterterm tree** `i e⁴ d₁ e γ^μ`. -/
theorem sum_tree_level_one (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (hmass : Φ.mass Φ.openLine = P.m)
    (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    ∑ C ∈ (Finset.univ : Finset (Contraction 1 1 fun _ : Fin 1 => Wick.VertexKind.gaugeCt)).filter
        (fun C => IsOnePI C),
      ((fermionSign C : ℤ) : ℂ) * contractionValue P Φ D C (fun _ => 1) (fun _ => p')
        (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) =
      I * ((P.e ^ 4 * D.d₁ Φ.openLine 1 * P.e : ℝ) : ℂ) * Dirac.gamma μ i j := by
  set P' : Params := { P with δ₁ := P.e ^ 4 * D.d₁ Φ.openLine 1 } with hP'
  have hκ : ∑ t, ((fun _ : Fin 1 => Wick.VertexKind.gaugeCt) t).order ≤ 3 := by decide
  have hv : ∀ C ∈ (Finset.univ : Finset (Contraction 1 1
      fun _ : Fin 1 => Wick.VertexKind.gaugeCt)).filter (fun C => IsOnePI C),
      ((fermionSign C : ℤ) : ℂ) * contractionValue P Φ D C (fun _ => 1) (fun _ => p')
        (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) =
      ((fermionSign C : ℤ) : ℂ) * QED.WickModel.contractionValue P' C (fun _ => p')
        (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) := by
    intro C hC
    have hC' := (Finset.mem_filter.1 hC).2
    have hR := reaches_of_one_one hκ C hC'
    rw [contractionValue_eq_of_grading P P' Φ D C (ctReaches_of_reaches hR) _ rfl rfl rfl rfl
      (fun _ _ => by norm_num [hP']) (fun _ h => absurd h (by decide))
      (fun _ h => absurd h (by decide))]
    rw [← QED.TwoLoop.contractionValue₂_eq_contractionValue_of_loopCount_le_one P' C
      (QED.TwoLoop.LoopBound.loopCount_le_one_of_order hκ (by norm_num) C hC'),
      ← QED.ChainProof.contractionValue₂_params']
    unfold Lepton.contractionValue₂
    rw [QED.Lepton.Proof.regulatedAmplitude₂_eq_of_reaches P' Φ
      ⟨P'.mass, P'.loopCoeff, 0⟩ hmass hR]
  rw [Finset.sum_congr rfl hv,
    ← QED.WickModel.sum_isOnePI_contractionEquiv P' hκ p' p μ i j]
  have h := congrFun (congrFun (Wick.sum_isOnePI_gaugeCt P'.e P'.δ₁ P'.δ₂ P'.δm P'.δ₃ P'.m
    P'.mγ P'.Λ P'.ε p' p μ) i) j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h
  rw [h, hP']

/-! ### The theorem -/

open scoped Classical in
/-- The order-`5` vertex part minus that of `levelZero D` is the level-`1` tree. -/
theorem onePIPart_five_sub_levelZero (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (hmass : Φ.mass Φ.openLine = P.m)
    (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    onePIPart P Φ D 1 1 5 (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i)
        (fun _ => j) (fun _ => μ) -
      onePIPart P Φ (levelZero D) 1 1 5 (fun _ => p') (fun _ => p) (fun _ => p' - p)
        (fun _ => i) (fun _ => j) (fun _ => μ) =
      I * ((P.e ^ 4 * D.d₁ Φ.openLine 1 * P.e : ℝ) : ℂ) * Dirac.gamma μ i j := by
  have hD : ∀ f k, 1 ≤ k → (levelZero D).d₁ f k = 0 ∧ (levelZero D).d₂ f k = 0 ∧
      (levelZero D).dm f k = 0 := fun f k hk => by
    simp [levelZero, show k ≠ 0 by omega]
  have hD₃ : ∀ k, 1 ≤ k → (levelZero D).d₃ k = 0 := fun k hk => by
    simp [levelZero, show k ≠ 0 by omega]
  -- the term of `(N, κ, g, C)` in the difference
  have hzero : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (g : Grading κ) (C : Contraction 1 1 κ),
      g = 0 → contractionValue P Φ D C g (fun _ => p') (fun _ => p) (fun _ => p' - p)
          (fun _ => i) (fun _ => j) (fun _ => μ) -
        contractionValue P Φ (levelZero D) C g (fun _ => p') (fun _ => p) (fun _ => p' - p)
          (fun _ => i) (fun _ => j) (fun _ => μ) = 0 := by
    intro N κ g C hg
    subst hg
    rw [contractionValue_zero_congr P Φ D (levelZero D) (fun _ => by simp [levelZero])
      (fun _ => by simp [levelZero]) (fun _ => by simp [levelZero]) (by simp [levelZero]),
      sub_self]
  unfold onePIPart selectedPart
  rw [← Finset.sum_sub_distrib]
  simp only [← mul_sub, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single_of_mem 1 (by simp) fun N _ hN => ?_]
  · rw [Finset.sum_eq_single (fun _ => .gaugeCt) (fun κ _ hκ => ?_) (by simp)]
    · rw [Finset.sum_eq_single_of_mem (fun _ => 1) (Finset.mem_filter.2
        ⟨Fintype.mem_piFinset.2 fun _ => by simp, gradedOrder_gaugeCt_one⟩)
        fun g hg hne => ?_]
      · have h1 : (fun _ => 1 : Grading fun _ : Fin 1 => Wick.VertexKind.gaugeCt) ≠ 0 :=
          fun h => by simpa using congrFun h ⟨0, by decide⟩
        simp only [contractionValue_eq_zero_of_level P Φ (levelZero D) hD hD₃ _ _ h1]
        simp only [sub_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_mul]
        exact sum_tree_level_one P Φ D hmass p' p μ i j
      · refine Finset.sum_eq_zero fun C _ => ?_
        by_cases hg0 : g = 0
        · rw [hzero g C hg0, mul_zero]
        · exact absurd (grading_eq_one (Finset.mem_filter.1 hg).2) hne
    · refine Finset.sum_eq_zero fun g hg => Finset.sum_eq_zero fun C _ => ?_
      by_cases hg0 : g = 0
      · rw [hzero g C hg0, mul_zero]
      · exact absurd (eq_gaugeCt_of_level hg0 (Finset.mem_filter.1 hg).2) hκ
  · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun κ _ =>
      Finset.sum_eq_zero fun g hg => Finset.sum_eq_zero fun C hC => ?_)
    by_cases hg0 : g = 0
    · rw [hzero g C hg0, mul_zero]
    · exact absurd (eq_one_of_level hg0 (Finset.mem_filter.1 hg).2 C
        (Finset.mem_filter.1 hC).2) hN

/-- (E-G₃) **The graded order-`e⁵` vertex is (F₉) plus the level-`1` vertex counterterm tree.** -/
theorem vertexPart_two_eq' (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (hmass : Φ.mass Φ.openLine = P.m)
    (h₁ : P.δ₁ = P.e ^ 2 * D.d₁ Φ.openLine 0) (h₂ : P.δ₂ = P.e ^ 2 * D.d₂ Φ.openLine 0)
    (hm : P.δm = P.e ^ 2 * D.dm Φ.openLine 0) (h₃ : P.δ₃ = P.e ^ 2 * D.d₃ 0)
    (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    vertexPart P Φ D Φ.openLine 2 p' p μ =
      Lepton.vertexOrderFive P Φ p' p μ +
        ((P.e ^ 4 * D.d₁ Φ.openLine 1 * P.e : ℝ) : ℂ) • Dirac.gamma μ := by
  have hD : ∀ f k, 1 ≤ k → (levelZero D).d₁ f k = 0 ∧ (levelZero D).d₂ f k = 0 ∧
      (levelZero D).dm f k = 0 := fun f k hk => by
    simp [levelZero, show k ≠ 0 by omega]
  have hD₃ : ∀ k, 1 ≤ k → (levelZero D).d₃ k = 0 := fun k hk => by
    simp [levelZero, show k ≠ 0 by omega]
  ext i j
  have key : onePIPart P Φ (levelZero D) 1 1 5 (fun _ => p') (fun _ => p) (fun _ => p' - p)
      (fun _ => i) (fun _ => j) (fun _ => μ) =
      Lepton.onePIFunction₂ P Φ 1 1 5 (fun _ => p') (fun _ => p) (fun _ => p' - p)
        (fun _ => i) (fun _ => j) (fun _ => μ) -
      Lepton.onePIFunction₂ P Φ 1 1 4 (fun _ => p') (fun _ => p) (fun _ => p' - p)
        (fun _ => i) (fun _ => j) (fun _ => μ) :=
    onePIPart_eq_onePIFunction₂_sub' P Φ (levelZero D) hmass (by simpa [levelZero] using h₁)
      (by simpa [levelZero] using h₂) (by simpa [levelZero] using hm)
      (by simpa [levelZero] using h₃) hD hD₃ 1 1 4 le_rfl (by norm_num) _ _ _ _ _ _
  have hdiff := onePIPart_five_sub_levelZero P Φ D hmass p' p μ i j
  have hsplit : onePIPart P Φ D 1 1 5 (fun _ => p') (fun _ => p) (fun _ => p' - p)
      (fun _ => i) (fun _ => j) (fun _ => μ) =
      onePIPart P Φ (levelZero D) 1 1 5 (fun _ => p') (fun _ => p) (fun _ => p' - p)
        (fun _ => i) (fun _ => j) (fun _ => μ) +
      I * ((P.e ^ 4 * D.d₁ Φ.openLine 1 * P.e : ℝ) : ℂ) * Dirac.gamma μ i j := by
    rw [← hdiff]
    ring
  change (1 / I) * onePIPart P Φ D 1 1 (2 * 2 + 1) (fun _ => p') (fun _ => p) (fun _ => p' - p)
      (fun _ => i) (fun _ => j) (fun _ => μ) = _
  rw [show 2 * 2 + 1 = 5 from rfl, hsplit, key]
  simp only [Lepton.vertexOrderFive, Matrix.add_apply, Matrix.of_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [mul_add, one_div, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ I_ne_zero, one_mul]

end QED.GradedProof

end
