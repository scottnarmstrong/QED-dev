/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.IsChargeNormalizedAt
public import QED.Frozen.OneLoop.IsChargeNormalized
public import QED.Frozen.WickModel.OnePIFunction
public import QED.Frozen.Wick.WickVertex
public import QED.Frozen.TwoLoop.ContractionValue
public import QED.GradedProof.Embed
public import QED.LeptonProof.EmbedOneZero
import QED.Frozen.TwoLoop.OnePIFunctionEqOnePIFunction
import QED.Frozen.Wick.WickVertexLimit
import QED.WickModel.Compatibility
import QED.Wick.Classification
import QED.Wick.ClassificationSmall
import QED.Wick.ClassificationGauge3
import QED.ChainProof.QuickMeaning
import Mathlib.Topology.Instances.Matrix

/-!
# The order-`e³` charge condition of the graded model

Helper proof of the Phase 5 Stage 2 goal (E-G₂ₖ) `QED.Graded.isChargeNormalizedAt_one_iff`
(decision D-57), as `QED.GradedProof.isChargeNormalizedAt_one_iff'`.

* `reaches_of_one_one`: in a 1PI contraction with one fermion pair and one photon of order at
  most `3`, every fermion vertex lies on the open fermion line (packet 5's classification,
  transported along `QED.WickModel.contractionEquiv`).
* `onePIPart_three_vertex`: so the order-`3` part (G₆′) with one fermion pair and one photon is
  the difference of packet 6a's 1PI function (X₂₈) at orders `3` and `2`, with the open-line
  level-`0` data as counterterms and the open-line mass as `m`.
* `onePIFunction_one_one_two`: the order-`≤ 2` vertex (X₂₈) is the tree `i e γ^μ`.
* By (Y₁) and (W₂), `(1/i)` times the order-`3` part tends to the vertex function (J) minus the
  tree `e γ^μ`, which gives the theorem.
-/

@[expose] public section

open Complex Filter Topology Matrix
open QED.WickModel (Params Contraction IsOnePI fermionSign)
open QED.Graded

namespace QED.GradedProof

/-! ### The flavour collapse at order three -/

/-- **In a 1PI vertex contraction of order at most `3` every fermion vertex lies on the open
line.** -/
theorem reaches_of_one_one {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (hκ : ∑ t, (κ t).order ≤ 3) (C' : Contraction 1 1 κ) (hC' : IsOnePI C') :
    QED.Lepton.Proof.Reaches C' := by
  obtain ⟨C, rfl⟩ := (QED.WickModel.contractionEquiv κ).surjective C'
  have hC : Wick.IsOnePI C := QED.WickModel.isOnePI_contractionEquiv_iff.1 hC'
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hC.1
  have hstep : ∀ {x : Option (Wick.FermionVertex κ)} {y : Wick.FermionVertex κ},
      C.1.1 x = some y → (QED.WickModel.contractionEquiv κ C).1.1
        (QED.WickModel.optionEquivFinOneSum _ x) = .inr y := by
    intro x y h
    rw [QED.WickModel.contractionEquiv_fst, Equiv.permCongr_apply, Equiv.symm_apply_apply, h]
    rfl
  have h0 : ∀ {y : Wick.FermionVertex κ}, C.1.1 none = some y →
      (QED.WickModel.contractionEquiv κ C).1.1.SameCycle (.inl 0) (.inr y) := fun h =>
    QED.Lepton.Proof.sameCycle_of_apply_eq (hstep h)
  have h1 : ∀ {x y : Wick.FermionVertex κ}, C.1.1 (some x) = some y →
      (QED.WickModel.contractionEquiv κ C).1.1.SameCycle (.inr x) (.inr y) := fun h =>
    QED.Lepton.Proof.sameCycle_of_apply_eq (hstep h)
  intro t
  refine ⟨0, ?_⟩
  obtain rfl | rfl | rfl | rfl : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 := by
    have := QED.WickModel.le_three_of_sum_order_le hκ
    omega
  · exact t.1.elim0
  · rw [(Subtype.ext (Subsingleton.elim t.1 s.1) : t = s)]
    exact h0 hs
  · exact absurd hC (Wick.not_isOnePI_of_fin_two κ hκ C)
  · obtain rfl := Wick.eq_gauge3_of_sum_order_le hκ
    obtain ⟨a, b, c, hab, hbc, hac, ha, hb, hc, -, -, -⟩ := hC.exists_isChain
    have sa := h0 ha
    have sb := sa.trans (h1 hb)
    have sc := sb.trans (h1 hc)
    obtain ⟨t, ht⟩ := t
    rcases QED.WickModel.fin_three_eq_or_eq_or_eq hab hbc hac t with rfl | rfl | rfl
    · exact sa
    · exact sb
    · exact sc

/-- A contraction without closed fermion lines has its counterterm vertices on the open line. -/
theorem ctReaches_of_reaches {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    {C : Contraction nf nA κ} (h : QED.Lepton.Proof.Reaches C) : CtReaches C :=
  fun t _ => h t

/-! ### The order-three part -/

/-- The parameters with the open-line level-`0` data of `D` as counterterms and the open-line mass
as `m`. -/
def ctParams (Q : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Counterterms F) : Params :=
  { Q with
    δ₁ := Q.e ^ 2 * D.d₁ Φ.openLine 0
    δ₂ := Q.e ^ 2 * D.d₂ Φ.openLine 0
    δm := Q.e ^ 2 * D.dm Φ.openLine 0
    δ₃ := Q.e ^ 2 * D.d₃ 0
    m := Φ.mass Φ.openLine }

open scoped Classical in
/-- Without closed fermion lines, the graded value at the zero grading is the value (T₁₀) at the
parameters `ctParams`. -/
theorem contractionValue_zero_eq_of_reaches (Q : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (hC : QED.Lepton.Proof.Reaches C)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionValue Q Φ D C 0 pOut pIn kIn αOut βIn μ =
      QED.WickModel.contractionValue₂ (ctParams Q Φ D) C pOut pIn kIn αOut βIn μ := by
  rw [contractionValue_zero_eq Q (ctParams Q Φ D) Φ D C (ctReaches_of_reaches hC) rfl rfl rfl
    rfl (fun _ _ => rfl) (fun _ _ => ⟨rfl, rfl, rfl⟩) (fun _ _ => rfl)]
  rw [← QED.ChainProof.contractionValue₂_params']
  unfold Lepton.contractionValue₂
  rw [QED.Lepton.Proof.regulatedAmplitude₂_eq_of_reaches (ctParams Q Φ D) Φ
    ⟨(ctParams Q Φ D).mass, (ctParams Q Φ D).loopCoeff, 0⟩ rfl hC]

open scoped Classical in
/-- **The order-`3` vertex part is the order-`3` part of (X₂₈)** at the parameters `ctParams`. -/
theorem onePIPart_three_vertex (Q : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (pOut pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) (μ : Fin 1 → Fin 4) :
    onePIPart Q Φ D 1 1 3 pOut pIn kIn αOut βIn μ =
      QED.WickModel.onePIFunction (ctParams Q Φ D) 1 1 3 pOut pIn kIn αOut βIn μ -
        QED.WickModel.onePIFunction (ctParams Q Φ D) 1 1 2 pOut pIn kIn αOut βIn μ := by
  rw [← QED.WickModel.onePIFunction₂_eq_onePIFunction _ 1 1 3 (by norm_num),
    ← QED.WickModel.onePIFunction₂_eq_onePIFunction _ 1 1 2 (by norm_num)]
  have key := QED.ChainProof.Quick.sum_range_filter_order_sub (fun N => (N.factorial : ℂ)⁻¹)
    (fun N κ => ∑ C ∈ (Finset.univ : Finset (Contraction 1 1 κ)).filter IsOnePI,
      ((fermionSign C : ℤ) : ℂ) *
        QED.WickModel.contractionValue₂ (ctParams Q Φ D) C pOut pIn kIn αOut βIn μ) 2
  refine Eq.trans ?_ key.symm
  unfold onePIPart
  rw [selectedPart_eq_sum_order_of_le_three Q Φ D 1 1 (fun C => IsOnePI C) 3 (by norm_num)]
  refine Finset.sum_congr rfl fun N _ => congrArg _ (Finset.sum_congr rfl fun κ hκ => ?_)
  by_cases h3 : ∑ t, (κ t).order = 3
  · rw [ite_eq_left h3, ite_eq_left h3]
    refine Finset.sum_congr rfl fun C hC => ?_
    rw [contractionValue_zero_eq_of_reaches Q Φ D C
      (reaches_of_one_one h3.le C (Finset.mem_filter.1 hC).2)]
  · rw [ite_eq_right h3, ite_eq_right h3]

open scoped Classical in
/-- **The order-`≤ 2` vertex is the tree** `i e γ^μ`. -/
theorem onePIFunction_one_one_two (P : Params) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    QED.WickModel.onePIFunction P 1 1 2 (fun _ => p') (fun _ => p) (fun _ => p' - p)
        (fun _ => i) (fun _ => j) (fun _ => μ) =
      I * (P.e : ℂ) * Dirac.gamma μ i j := by
  unfold QED.WickModel.onePIFunction
  rw [Finset.sum_congr rfl fun N _ => congrArg _ (Finset.sum_congr rfl fun κ hκ =>
    (QED.WickModel.sum_isOnePI_contractionEquiv P
      ((Finset.mem_filter.1 hκ).2.trans (by norm_num)) p' p μ i j).symm)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [Finset.sum_eq_zero fun κ _ => Wick.sum_isOnePI_eq_zero Wick.not_isOnePI_of_fin_zero _,
    Finset.sum_eq_zero fun κ hκ => Wick.sum_isOnePI_eq_zero
      (Wick.not_isOnePI_of_fin_two κ ((Finset.mem_filter.1 hκ).2.trans (by norm_num))) _]
  rw [Finset.sum_eq_single_of_mem (fun _ => .gauge)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩) fun κ hκ hne => ?_]
  · have h := congrFun (congrFun (Wick.sum_isOnePI_gauge P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m P.mγ P.Λ
      P.ε p' p μ) i) j
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h
    rw [h]
    simp
  · obtain ⟨k, rfl⟩ : ∃ k, κ = fun _ => k :=
      ⟨κ 0, funext fun t => by rw [Subsingleton.elim t 0]⟩
    have hk := (Finset.mem_filter.1 hκ).2
    cases k
    · exact absurd rfl hne
    · simp [Wick.VertexKind.order] at hk
    · exact Wick.sum_isOnePI_eq_zero
        (fun C => (Wick.isEmpty_contraction_of_not_two_dvd (by decide)).elim C) _
    · exact Wick.sum_isOnePI_eq_zero
        (fun C => (Wick.isEmpty_contraction_of_not_two_dvd (by decide)).elim C) _

/-- The order-`3` graded vertex (G₈ᵥ) at `n = 1`, entrywise: `(1/i)` times packet 5's Wick vertex
(V₂₂) at the open-line level-`0` data and mass, minus the tree `e γ^μ`. -/
theorem vertexPart_one_apply (Q : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    vertexPart Q Φ D f 1 p' p μ i j =
      (1 / I) * Wick.wickVertex Q.e (Q.e ^ 2 * D.d₁ f 0) (Q.e ^ 2 * D.d₂ f 0)
          (Q.e ^ 2 * D.dm f 0) (Q.e ^ 2 * D.d₃ 0) (Φ.mass f) Q.mγ Q.Λ Q.ε p' p μ i j -
        (Q.e : ℂ) * Dirac.gamma μ i j := by
  simp only [vertexPart, Matrix.of_apply]
  rw [onePIPart_three_vertex Q { Φ with openLine := f } D,
    onePIFunction_one_one_two (ctParams Q { Φ with openLine := f } D) p' p μ i j,
    ← QED.WickModel.wickVertex_eq_onePIFunction']
  simp only [ctParams]
  field_simp

/-! ### The charge condition -/

/-- (E-G₂ₖ) **The order-`e³` charge condition is (K₀) at mass `M_f`** with
`Z₁ = 1 + e² d₁ f 0`. -/
theorem isChargeNormalizedAt_one_iff' (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (hf : 0 < Φ.mass f)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    IsChargeNormalizedAt P Φ D f 1 ↔
      QED.OneLoop.IsChargeNormalized P.e (1 + P.e ^ 2 * D.d₁ f 0) (Φ.mass f) P.mγ P.Λ hf hmγ
        hΛ := by
  unfold IsChargeNormalizedAt QED.OneLoop.IsChargeNormalized
  refine forall_congr' fun p => forall_congr' fun hp => forall_congr' fun hp0 =>
    forall_congr' fun μ => forall_congr' fun u => forall_congr' fun w =>
      forall_congr' fun _ => forall_congr' fun _ => ?_
  set VF := QED.OneLoop.vertexFunction P.e (1 + P.e ^ 2 * D.d₁ f 0) (Φ.mass f) P.mγ P.Λ hf hmγ
    hΛ p p hp hp hp0 hp0 μ with hVF
  have hent : ∀ i j, Tendsto (fun ε : ℝ => vertexPart { P with ε := ε } Φ D f 1 p p μ i j)
      (𝓝[>] 0) (𝓝 ((VF - (P.e : ℂ) • Dirac.gamma μ) i j)) := by
    intro i j
    simp only [vertexPart_one_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact (QED.Wick.tendsto_wickVertex P.e (P.e ^ 2 * D.d₁ f 0) (P.e ^ 2 * D.d₂ f 0)
      (P.e ^ 2 * D.dm f 0) (P.e ^ 2 * D.d₃ 0) (Φ.mass f) P.mγ P.Λ hf hmγ hΛ p p hp hp hp0 hp0
      μ i j).sub tendsto_const_nhds
  have hmat : Tendsto (fun ε : ℝ => vertexPart { P with ε := ε } Φ D f 1 p p μ) (𝓝[>] 0)
      (𝓝 (VF - (P.e : ℂ) • Dirac.gamma μ)) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hent i j
  have hcont : Continuous fun M : Matrix (Fin 4) (Fin 4) ℂ => w ⬝ᵥ (M *ᵥ u) :=
    continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
  have hlim := (hcont.tendsto _).comp hmat
  have hval : w ⬝ᵥ ((VF - (P.e : ℂ) • Dirac.gamma μ) *ᵥ u) =
      w ⬝ᵥ (VF *ᵥ u) - (P.e : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul]
  rw [hval] at hlim
  constructor
  · intro h
    exact sub_eq_zero.1 (tendsto_nhds_unique hlim h)
  · intro h
    rwa [h, sub_self] at hlim

end QED.GradedProof

end
