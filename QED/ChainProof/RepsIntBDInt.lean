/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.RepsIntBD
public import QED.ChainProof.IntegrableChainReduction

/-!
# Two-loop pieces on the rows of the `VP` class matrix

Helper for obligation O3-5 of `docs/HIGHER-LOOP-PLAN.md` (decision D-53). The integrands of the
bubble–`δ₃` and `δ₃`–bubble representatives split, after the flavour sum, into pieces
`N(λ) ∏ᵢ D_{σ(i)}(λ)⁻¹` whose lines are rows `σ(i)` of the class loop matrix of `VP`
(`class5LoopMatrix .VP`: open line `p + λ₁`, `p' + λ₁`, loop lines `λ₀ - λ₁`, `λ₀`, photon lines
`∓λ₁`). This file proves (T₉′) for such a piece from the numerator-aware criterion
(`jointEnergyFirstIntegrable_vpRows`), and the pointwise bounds and degree bounds of the
numerators that occur (`refinedBound_contract`, `isLoopPoly_contract`).
-/

@[expose] public section

open MeasureTheory Complex

namespace QED.ChainProof.RepsInt

open QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.Insertion QED.TwoLoop.CountertermLimit
  QED.ChainProof.Enum
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix class5LoopMatrix
  classVPMomenta RefinedBound IntNoSubdivergenceRefined noSubdivergenceRefined_castLoopMatrix_iff
  jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined refinedBound_lineMomentum)
open QED.TwoLoop.ClassIntegrable (RefinedBoundMat)

/-! ### Pieces on rows of the `VP` matrix -/

/-- **(T₉′) for a piece whose lines are rows of the `VP` class matrix**: with at least eight
lines, `ε > 0`, the refined criterion for the numerator lines `E`, a numerator of degree at most
four with the pointwise bound for `E`. -/
theorem jointEnergyFirstIntegrable_vpRows {m : ℕ} (hm : 7 ≤ m) (σ : Fin (m + 1) → Fin 6)
    (Ms : Fin (m + 1) → ℝ) {ε : ℝ} (hε : 0 < ε) (p p' : Fin 4 → ℝ) {E : Finset (Fin (m + 1))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun i => class5LoopMatrix .VP (σ i))
    {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (hpoly : IsLoopPoly 2 4 F)
    (hB : RefinedBound (castLoopMatrix fun i => class5LoopMatrix .VP (σ i)) E 4 F) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      F ℓ * ∏ i, (propDenom (Ms i) ε (classLineVP p p' (σ i) ℓ))⁻¹ := by
  obtain ⟨Q, rfl⟩ := hpoly.exists_loopQuartic
  exact jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined Q
    (castLoopMatrix fun i => class5LoopMatrix .VP (σ i)) (fun i => classVPMomenta p p' (σ i)) Ms
    hm hε ((noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr hcrit) hB

/-- The line momenta of the rows of the `VP` class matrix. -/
theorem classLineVP_rows (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    classLineVP p p' 0 ℓ = p - -ℓ 1 ∧ classLineVP p p' 1 ℓ = p' - -ℓ 1 ∧
      classLineVP p p' 2 ℓ = ℓ 0 + -ℓ 1 ∧ classLineVP p p' 3 ℓ = ℓ 0 ∧
      classLineVP p p' 4 ℓ = -ℓ 1 ∧ classLineVP p p' 5 ℓ = ℓ 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> funext μ <;>
    simp [classLineVP, QED.Integration.TwoLoop.lineMomentum, castLoopMatrix, class5LoopMatrix,
      classVPMomenta,
      Fin.sum_univ_two] <;> ring

theorem propDenom_neg (M ε : ℝ) (k : Fin 4 → ℝ) : propDenom M ε (-k) = propDenom M ε k := by
  simp [propDenom, Minkowski.dot]

/-! ### Numerator bounds -/

section Contract

variable {m : ℕ} (al : Fin (m + 1) → Fin 2 → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ)

/-- The component of a line momentum lowered by the metric. -/
theorem refinedBound_lower (e : Fin (m + 1)) (ν : Fin 4) :
    RefinedBound al {e} 1 fun ℓ => ((Minkowski.lower (lineMomentum al pp e ℓ) ν : ℝ) : ℂ) := by
  simp only [Minkowski.lower, ofReal_sum, ofReal_mul]
  exact RefinedBound.sum _ fun μ _ => (refinedBound_lineMomentum al pp e μ).const_mul _

/-- **The bound for the contracted numerators**: `∑ X^{l₀ l₂} g_{l₂ l₃} K_{l₀} V^{l₃}` with each
`X^{l₀ l₂}` bounded by the lines `E₀` with exponent two, `K` the momentum of line `eK`, `V` of
line `eV`, all lines distinct. -/
theorem refinedBound_contract {E₀ : Finset (Fin (m + 1))} {eK eV : Fin (m + 1)}
    (hK : eK ∉ E₀) (hV : eV ∉ E₀) (hKV : eK ≠ eV)
    (X : (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (hX : ∀ l0 l2, RefinedBound al E₀ 2 fun ℓ => X ℓ l0 l2) :
    RefinedBound al (E₀ ∪ {eK} ∪ {eV}) 4 fun ℓ =>
      ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l3 : Fin 4, X ℓ l0 l2 * ((Minkowski.metric l2 l3 : ℝ) : ℂ) *
        ((Minkowski.lower (lineMomentum al pp eK ℓ) l0 : ℝ) : ℂ) *
          ((lineMomentum al pp eV ℓ l3 : ℝ) : ℂ) := by
  refine RefinedBound.sum _ fun l0 _ => RefinedBound.sum _ fun l2 _ =>
    RefinedBound.sum _ fun l3 _ => ?_
  have h := ((((hX l0 l2).mul (RefinedBound.const ((Minkowski.metric l2 l3 : ℝ) : ℂ))
    (by simp)).mul (refinedBound_lower al pp eK l0) (by simpa using hK)).mul
      (refinedBound_lineMomentum al pp eV l3) (by simp [hV, Ne.symm hKV]))
  exact h.mono (by intro x hx; simpa using hx) (by norm_num)

end Contract

section Contract2

variable {m : ℕ} (al : Fin (m + 1) → Fin 2 → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ)

/-- `refinedBound_contract` for momenta given as functions equal to line momenta. -/
theorem refinedBound_contract' {E₀ : Finset (Fin (m + 1))} {eK eV : Fin (m + 1)}
    (hK : eK ∉ E₀) (hV : eV ∉ E₀) (hKV : eK ≠ eV)
    (K V : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ) (hKe : ∀ ℓ, K ℓ = lineMomentum al pp eK ℓ)
    (hVe : ∀ ℓ, V ℓ = lineMomentum al pp eV ℓ)
    (X : (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hX : ∀ l0 l2, RefinedBound al E₀ 2 fun ℓ => X ℓ l0 l2) :
    RefinedBound al (E₀ ∪ {eK} ∪ {eV}) 4 fun ℓ =>
      ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l3 : Fin 4, X ℓ l0 l2 * ((Minkowski.metric l2 l3 : ℝ) : ℂ) *
        ((Minkowski.lower (K ℓ) l0 : ℝ) : ℂ) * ((V ℓ l3 : ℝ) : ℂ) := by
  simp only [hKe, hVe]
  exact refinedBound_contract al pp hK hV hKV X hX

/-- The open-line numerator matrix `A₁ (m - P₁̸) A₂ (m - P₂̸) A₃` with `P₁`, `P₂` the momenta of
two distinct lines. -/
theorem refinedBound_openNum {e₁ e₂ : Fin (m + 1)} (h : e₁ ≠ e₂) (mass : ℝ)
    (P₁ P₂ : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ) (h₁ : ∀ ℓ, P₁ ℓ = lineMomentum al pp e₁ ℓ)
    (h₂ : ∀ ℓ, P₂ ℓ = lineMomentum al pp e₂ ℓ) (A₁ A₂ A₃ : Matrix (Fin 4) (Fin 4) ℂ)
    (a b : Fin 4) :
    RefinedBound al {e₁, e₂} 2 fun ℓ =>
      (A₁ * electronNumerator mass (P₁ ℓ) * A₂ * electronNumerator mass (P₂ ℓ) * A₃) a b := by
  simp only [h₁, h₂]
  have hm := ((((RefinedBoundMat.const A₁).mul (refinedBoundMat_electronNumerator' al pp e₁ mass)
    (by simp)).mul (RefinedBoundMat.const A₂) (by simp)).mul
      (refinedBoundMat_electronNumerator' al pp e₂ mass) (by simpa using h)).mul
        (RefinedBoundMat.const A₃) (by simp)
  exact (hm a b).mono (by intro x hx; simp only [Finset.mem_union, Finset.mem_singleton,
    Finset.notMem_empty, or_false, false_or] at hx; simp only [Finset.mem_insert,
    Finset.mem_singleton]; tauto) (by norm_num)

end Contract2

/-! ### Degree bounds -/

theorem isLoopAffine_neg_one : IsLoopAffine fun ℓ : Fin 2 → Fin 4 → ℝ => -ℓ 1 :=
  ⟨![0, -1], 0, fun ℓ => by funext ν; simp [Fin.sum_univ_two]⟩

theorem isLoopAffine_zero' : IsLoopAffine fun ℓ : Fin 2 → Fin 4 → ℝ => ℓ 0 :=
  ⟨![1, 0], 0, fun ℓ => by funext ν; simp [Fin.sum_univ_two]⟩

theorem IsLoopAffine.add' {F G : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ} (hF : IsLoopAffine F)
    (hG : IsLoopAffine G) : IsLoopAffine fun ℓ => F ℓ + G ℓ := by
  obtain ⟨a, b, hF⟩ := hF
  obtain ⟨a', b', hG⟩ := hG
  refine ⟨a + a', b + b', fun ℓ => ?_⟩
  simp only [hF, hG, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  abel

theorem IsLoopAffine.const_sub' {F : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ} (hF : IsLoopAffine F)
    (c : Fin 4 → ℝ) : IsLoopAffine fun ℓ => c - F ℓ := by
  obtain ⟨a, b, hF⟩ := hF
  refine ⟨-a, c - b, fun ℓ => ?_⟩
  simp only [hF, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
  abel

theorem isLoopPoly_lower {F : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ} (hF : IsLoopAffine F) (ν : Fin 4) :
    IsLoopPoly 2 1 fun ℓ => ((Minkowski.lower (F ℓ) ν : ℝ) : ℂ) := by
  simp only [Minkowski.lower, ofReal_sum, ofReal_mul]
  exact IsLoopPoly.sum _ fun μ _ => (hF.isLoopPoly_coord μ).const_mul _

/-- **The degree bound for the contracted numerators.** -/
theorem isLoopPoly_contract (mass : ℝ) {K V P₁ P₂ : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ}
    (hK : IsLoopAffine K) (hV : IsLoopAffine V) (h₁ : IsLoopAffine P₁) (h₂ : IsLoopAffine P₂)
    (A₁ A₂ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) (a b : Fin 4) :
    IsLoopPoly 2 4 fun ℓ =>
      ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l3 : Fin 4,
        (A₁ l2 * electronNumerator mass (P₁ ℓ) * A * electronNumerator mass (P₂ ℓ) * A₂ l0) a b *
          ((Minkowski.metric l2 l3 : ℝ) : ℂ) * ((Minkowski.lower (K ℓ) l0 : ℝ) : ℂ) *
            ((V ℓ l3 : ℝ) : ℂ) := by
  refine IsLoopPoly.sum _ fun l0 _ => IsLoopPoly.sum _ fun l2 _ => IsLoopPoly.sum _ fun l3 _ => ?_
  have hm : IsLoopPolyMat 2 (0 + 1 + 0 + 1 + 0) fun ℓ =>
      A₁ l2 * electronNumerator mass (P₁ ℓ) * A * electronNumerator mass (P₂ ℓ) * A₂ l0 :=
    ((((IsLoopPolyMat.const _).mul (h₁.isLoopPolyMat_electronNumerator mass)).mul
      (IsLoopPolyMat.const _)).mul (h₂.isLoopPolyMat_electronNumerator mass)).mul
        (IsLoopPolyMat.const _)
  exact (((hm a b).mul (IsLoopPoly.const (n := 0) _)).mul (isLoopPoly_lower hK l0)).mul
    (hV.isLoopPoly_coord l3)

/-! ### The `VP` shapes with extra photon lines -/

section VPExt

open QED.TwoLoop.ClassIntegrable

/-- The `VP` shapes with one extra photon line (row `4`). -/
def vpExt1Lines (t : Fin 4) (i : Fin 11) : Fin 6 :=
  if h : i.val < 10 then vpShapeLines t ⟨i.val, h⟩ else 4

/-- The masses of the `VP` shapes with one extra photon line of mass `M`. -/
def vpExt1Masses (P : Params) (t : Fin 4) (M : ℝ) (i : Fin 11) : ℝ :=
  if h : i.val < 10 then vpShapeMasses P t ⟨i.val, h⟩ else M

/-- The `VP` shapes with two extra photon lines (row `4`). -/
def vpExt2Lines (t : Fin 4) (i : Fin 12) : Fin 6 :=
  if h : i.val < 10 then vpShapeLines t ⟨i.val, h⟩ else 4

/-- The masses of the `VP` shapes with two extra photon lines of masses `M`, `M'`. -/
def vpExt2Masses (P : Params) (t : Fin 4) (M M' : ℝ) (i : Fin 12) : ℝ :=
  if h : i.val < 10 then vpShapeMasses P t ⟨i.val, h⟩ else if i.val = 10 then M else M'

theorem vpExt1_rows (t : Fin 4) (i : Fin 10) :
    castLoopMatrix (fun j => class5LoopMatrix .VP (vpExt1Lines t j)) (Fin.castSuccEmb i) =
      castLoopMatrix (vpShapeMatrix t) i := by
  funext r
  simp [castLoopMatrix, vpExt1Lines, vpShapeMatrix]

theorem vpExt2_rows (t : Fin 4) (i : Fin 10) :
    castLoopMatrix (fun j => class5LoopMatrix .VP (vpExt2Lines t j))
        (Fin.castLEEmb (by norm_num : 10 ≤ 12) i) =
      castLoopMatrix (vpShapeMatrix t) i := by
  funext r
  simp [castLoopMatrix, vpExt2Lines, vpShapeMatrix]

theorem prod_vpExt1 (P : Params) (t : Fin 4) (M : ℝ) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∏ i, (propDenom (vpExt1Masses P t M i) P.ε (classLineVP p p' (vpExt1Lines t i) ℓ))⁻¹ =
      (∏ i : Fin 10, (vpDenom P t p p' i ℓ)⁻¹) * (propDenom M P.ε (ℓ 1))⁻¹ := by
  have h1 : ∀ i : Fin 10, (propDenom (vpExt1Masses P t M (Fin.castSucc i)) P.ε
      (classLineVP p p' (vpExt1Lines t (Fin.castSucc i)) ℓ))⁻¹ = (vpDenom P t p p' i ℓ)⁻¹ :=
    fun i => by rw [vpDenom_eq]; simp [vpExt1Masses, vpExt1Lines]
  have h2 : (propDenom (vpExt1Masses P t M (Fin.last 10)) P.ε
      (classLineVP p p' (vpExt1Lines t (Fin.last 10)) ℓ))⁻¹ = (propDenom M P.ε (ℓ 1))⁻¹ := by
    simp [vpExt1Masses, vpExt1Lines, (classLineVP_rows p p' ℓ).2.2.2.2.1, propDenom_neg]
  rw [Fin.prod_univ_castSucc]
  simp only [h1, h2]

theorem prod_vpExt2 (P : Params) (t : Fin 4) (M M' : ℝ) (p p' : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∏ i, (propDenom (vpExt2Masses P t M M' i) P.ε (classLineVP p p' (vpExt2Lines t i) ℓ))⁻¹ =
      (∏ i : Fin 10, (vpDenom P t p p' i ℓ)⁻¹) *
        ((propDenom M P.ε (ℓ 1))⁻¹ * (propDenom M' P.ε (ℓ 1))⁻¹) := by
  have h1 : ∀ i : Fin 10, (propDenom (vpExt2Masses P t M M' (Fin.castSucc (Fin.castSucc i))) P.ε
      (classLineVP p p' (vpExt2Lines t (Fin.castSucc (Fin.castSucc i))) ℓ))⁻¹ =
        (vpDenom P t p p' i ℓ)⁻¹ :=
    fun i => by rw [vpDenom_eq]; simp [vpExt2Masses, vpExt2Lines]
  have h2 : (propDenom (vpExt2Masses P t M M' (Fin.castSucc (Fin.last 10))) P.ε
      (classLineVP p p' (vpExt2Lines t (Fin.castSucc (Fin.last 10))) ℓ))⁻¹ =
        (propDenom M P.ε (ℓ 1))⁻¹ := by
    simp [vpExt2Masses, vpExt2Lines, (classLineVP_rows p p' ℓ).2.2.2.2.1, propDenom_neg]
  have h3 : (propDenom (vpExt2Masses P t M M' (Fin.last 11)) P.ε
      (classLineVP p p' (vpExt2Lines t (Fin.last 11)) ℓ))⁻¹ = (propDenom M' P.ε (ℓ 1))⁻¹ := by
    simp [vpExt2Masses, vpExt2Lines, (classLineVP_rows p p' ℓ).2.2.2.2.1, propDenom_neg]
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  simp only [h1, h2, h3]
  ring

/-- **A `VP`-shape piece with one extra photon denominator.** -/
theorem jointEnergyFirstIntegrable_vpExt1 (P : Params) (hε : 0 < P.ε) (t : Fin 4) (M : ℝ)
    (p p' : Fin 4 → ℝ) {E : Finset (Fin 10)}
    (hcrit : IntNoSubdivergenceRefined 2 (E.map Fin.castSuccEmb)
      fun i => class5LoopMatrix .VP (vpExt1Lines t i))
    {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (hpoly : IsLoopPoly 2 4 F)
    (hB : RefinedBound (castLoopMatrix (vpShapeMatrix t)) E 4 F) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      F ℓ * ((∏ i : Fin 10, (vpDenom P t p p' i ℓ)⁻¹) * (propDenom M P.ε (ℓ 1))⁻¹) := by
  have h := jointEnergyFirstIntegrable_vpRows (by norm_num : 7 ≤ 10) (vpExt1Lines t)
    (vpExt1Masses P t M) hε p p' hcrit hpoly (RefinedBound.map_rows _ (vpExt1_rows t) hB)
  refine (congrArg (QED.TwoLoop.jointEnergyFirstIntegrable 2) (funext fun ℓ => ?_)).mp h
  rw [prod_vpExt1]

/-- **A `VP`-shape piece with two extra photon denominators.** -/
theorem jointEnergyFirstIntegrable_vpExt2 (P : Params) (hε : 0 < P.ε) (t : Fin 4) (M M' : ℝ)
    (p p' : Fin 4 → ℝ) {E : Finset (Fin 10)}
    (hcrit : IntNoSubdivergenceRefined 2 (E.map (Fin.castLEEmb (by norm_num : 10 ≤ 12)))
      fun i => class5LoopMatrix .VP (vpExt2Lines t i))
    {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (hpoly : IsLoopPoly 2 4 F)
    (hB : RefinedBound (castLoopMatrix (vpShapeMatrix t)) E 4 F) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      F ℓ * ((∏ i : Fin 10, (vpDenom P t p p' i ℓ)⁻¹) *
        ((propDenom M P.ε (ℓ 1))⁻¹ * (propDenom M' P.ε (ℓ 1))⁻¹)) := by
  have h := jointEnergyFirstIntegrable_vpRows (by norm_num : 7 ≤ 11) (vpExt2Lines t)
    (vpExt2Masses P t M M') hε p p' hcrit hpoly (RefinedBound.map_rows _ (vpExt2_rows t) hB)
  refine (congrArg (QED.TwoLoop.jointEnergyFirstIntegrable 2) (funext fun ℓ => ?_)).mp h
  rw [prod_vpExt2]

end VPExt

section VPExtSum

open QED.TwoLoop.ClassIntegrable

variable (P : Params) (hε : 0 < P.ε) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)

theorem crit_vpExt1 : ∀ t : Fin 4,
    IntNoSubdivergenceRefined 2 (({0, 1, 2, 3} : Finset (Fin 10)).map Fin.castSuccEmb)
      fun i => class5LoopMatrix .VP (vpExt1Lines t i) := by
  decide

theorem crit_vpExt1_three :
    IntNoSubdivergenceRefined 2 (({0, 1, 2, 8} : Finset (Fin 10)).map Fin.castSuccEmb)
      (fun i => class5LoopMatrix .VP (vpExt1Lines 3 i)) ∧
    IntNoSubdivergenceRefined 2 (({0, 1, 3, 9} : Finset (Fin 10)).map Fin.castSuccEmb)
      (fun i => class5LoopMatrix .VP (vpExt1Lines 3 i)) := by
  decide

theorem crit_vpExt2 : ∀ t : Fin 4,
    IntNoSubdivergenceRefined 2
      (({0, 1, 2, 3} : Finset (Fin 10)).map (Fin.castLEEmb (by norm_num : 10 ≤ 12)))
      fun i => class5LoopMatrix .VP (vpExt2Lines t i) := by
  decide

theorem crit_vpExt2_three :
    IntNoSubdivergenceRefined 2
      (({0, 1, 2, 8} : Finset (Fin 10)).map (Fin.castLEEmb (by norm_num : 10 ≤ 12)))
      (fun i => class5LoopMatrix .VP (vpExt2Lines 3 i)) ∧
    IntNoSubdivergenceRefined 2
      (({0, 1, 3, 9} : Finset (Fin 10)).map (Fin.castLEEmb (by norm_num : 10 ≤ 12)))
      (fun i => class5LoopMatrix .VP (vpExt2Lines 3 i)) := by
  decide

/-- The pieces of the `VP` shapes: the numerator bounds of `ClassIntegrableVP`. -/
theorem vpTerm_bounds (κ : ℂ) :
    (∀ t : Fin 4, IsLoopPoly 2 4 (fun ℓ => κ * (vpBubbleCoeff P * (vpE0 P pIn kIn αOut βIn μ ℓ +
        ((P.m ^ 2 : ℝ) : ℂ) * vpE2 P pIn kIn αOut βIn μ ℓ))) ∧
      RefinedBound (castLoopMatrix (vpShapeMatrix t)) {0, 1, 2, 3} 4
        (fun ℓ => κ * (vpBubbleCoeff P * (vpE0 P pIn kIn αOut βIn μ ℓ +
          ((P.m ^ 2 : ℝ) : ℂ) * vpE2 P pIn kIn αOut βIn μ ℓ)))) ∧
    (∀ i : Fin 10, IsLoopPoly 2 4
      (fun ℓ => κ * -(vpBubbleCoeff P * vpE2 P pIn kIn αOut βIn μ ℓ *
        vpDenom P 3 (pIn 0) (pOut 0) i ℓ))) ∧
    RefinedBound (castLoopMatrix (vpShapeMatrix 3)) {0, 1, 2, 8} 4
      (fun ℓ => κ * -(vpBubbleCoeff P * vpE2 P pIn kIn αOut βIn μ ℓ *
        vpDenom P 3 (pIn 0) (pOut 0) 8 ℓ)) ∧
    RefinedBound (castLoopMatrix (vpShapeMatrix 3)) {0, 1, 3, 9} 4
      (fun ℓ => κ * -(vpBubbleCoeff P * vpE2 P pIn kIn αOut βIn μ ℓ *
        vpDenom P 3 (pIn 0) (pOut 0) 3 ℓ)) := by
  have hp0 := isLoopPoly_vpE0 P pIn kIn αOut βIn μ
  have hp2 := isLoopPoly_vpE2 P pIn kIn αOut βIn μ
  refine ⟨fun t => ⟨((hp0.add ((hp2.mono (by norm_num)).const_mul _)).const_mul _).const_mul κ,
    (((refinedBound_vpE0 t P pIn kIn αOut βIn μ).add
      (((refinedBound_vpE2 t P pIn kIn αOut βIn μ).mono (by decide) (by norm_num)).const_mul
        _)).const_mul _).const_mul κ⟩, fun i => ?_, ?_, ?_⟩
  · have h : IsLoopPoly 2 4 (fun ℓ => -κ * (vpBubbleCoeff P * vpE2 P pIn kIn αOut βIn μ ℓ *
        vpDenom P 3 (pIn 0) (pOut 0) i ℓ)) :=
      (((hp2.const_mul _).mul (isLoopPoly_vpDenom P 3 (pIn 0) (pOut 0) i)).const_mul (-κ)).mono
        (by norm_num)
    refine (congrArg (IsLoopPoly 2 4) (funext fun ℓ => ?_)).mp h
    ring
  · have hD8 : RefinedBound (castLoopMatrix (vpShapeMatrix 3)) ({8} ∪ {2}) 2
        (vpDenom P 3 (pIn 0) (pOut 0) 8) :=
      refinedBound_lineDenom_of_eq (castLoopMatrix (vpShapeMatrix 3))
        (vpShapeMomenta 3 (pIn 0) (pOut 0)) (vpShapeMasses P 3) P.ε (by decide) fun ℓ => rfl
    exact (((((refinedBound_vpE2 3 P pIn kIn αOut βIn μ).const_mul _).mul hD8 (by decide)).mono
      (by decide) (by norm_num)).neg).const_mul κ
  · have hD3 : RefinedBound (castLoopMatrix (vpShapeMatrix 3)) ({3} ∪ {9}) 2
        (vpDenom P 3 (pIn 0) (pOut 0) 3) :=
      refinedBound_lineDenom_of_eq (castLoopMatrix (vpShapeMatrix 3))
        (vpShapeMomenta 3 (pIn 0) (pOut 0)) (vpShapeMasses P 3) P.ε (by decide) fun ℓ => rfl
    exact (((((refinedBound_vpE2 3 P pIn kIn αOut βIn μ).const_mul _).mul hD3 (by decide)).mono
      (by decide) (by norm_num)).neg).const_mul κ

include hε in
/-- **The `VP` shapes with one extra photon denominator**: (T₉′) of
`κ ∑ₜ Nₜ ∏ᵢ D_{t,i}⁻¹ · D_M(λ₁)⁻¹`. -/
theorem jointEnergyFirstIntegrable_vpSum_ext1 (κ : ℂ) (M : ℝ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      κ * ∑ t : Fin 4, vpTermNumer P pOut pIn kIn αOut βIn μ t ℓ *
        ((∏ i : Fin 10, (vpDenom P t (pIn 0) (pOut 0) i ℓ)⁻¹) * (propDenom M P.ε (ℓ 1))⁻¹) := by
  obtain ⟨hlow, hpoly3, hB8, hB3⟩ := vpTerm_bounds P pOut pIn kIn αOut βIn μ κ
  have hl : ∀ t : Fin 4, QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      (κ * (vpBubbleCoeff P * (vpE0 P pIn kIn αOut βIn μ ℓ +
        ((P.m ^ 2 : ℝ) : ℂ) * vpE2 P pIn kIn αOut βIn μ ℓ))) *
        ((∏ i : Fin 10, (vpDenom P t (pIn 0) (pOut 0) i ℓ)⁻¹) * (propDenom M P.ε (ℓ 1))⁻¹) :=
    fun t => jointEnergyFirstIntegrable_vpExt1 P hε t M _ _ (crit_vpExt1 t) (hlow t).1
      (hlow t).2
  have h3a := jointEnergyFirstIntegrable_vpExt1 P hε 3 M (pIn 0) (pOut 0)
    crit_vpExt1_three.1 (hpoly3 8) hB8
  have h3b := jointEnergyFirstIntegrable_vpExt1 P hε 3 M (pIn 0) (pOut 0)
    crit_vpExt1_three.2 (hpoly3 3) hB3
  have hsum := jointEnergyFirstIntegrable_add (jointEnergyFirstIntegrable_add
    (jointEnergyFirstIntegrable_add (jointEnergyFirstIntegrable_add (hl 0) (hl 1)) (hl 2)) h3a) h3b
  refine (congrArg (QED.TwoLoop.jointEnergyFirstIntegrable 2) (funext fun ℓ => ?_)).mp hsum
  simp only [Fin.sum_univ_four, vpTermNumer, Fin.reduceEq, ↓reduceIte]
  ring

include hε in
/-- **The `VP` shapes with two extra photon denominators.** -/
theorem jointEnergyFirstIntegrable_vpSum_ext2 (κ : ℂ) (M M' : ℝ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      κ * ∑ t : Fin 4, vpTermNumer P pOut pIn kIn αOut βIn μ t ℓ *
        ((∏ i : Fin 10, (vpDenom P t (pIn 0) (pOut 0) i ℓ)⁻¹) *
          ((propDenom M P.ε (ℓ 1))⁻¹ * (propDenom M' P.ε (ℓ 1))⁻¹)) := by
  obtain ⟨hlow, hpoly3, hB8, hB3⟩ := vpTerm_bounds P pOut pIn kIn αOut βIn μ κ
  have hl : ∀ t : Fin 4, QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      (κ * (vpBubbleCoeff P * (vpE0 P pIn kIn αOut βIn μ ℓ +
        ((P.m ^ 2 : ℝ) : ℂ) * vpE2 P pIn kIn αOut βIn μ ℓ))) *
        ((∏ i : Fin 10, (vpDenom P t (pIn 0) (pOut 0) i ℓ)⁻¹) *
          ((propDenom M P.ε (ℓ 1))⁻¹ * (propDenom M' P.ε (ℓ 1))⁻¹)) :=
    fun t => jointEnergyFirstIntegrable_vpExt2 P hε t M M' _ _ (crit_vpExt2 t) (hlow t).1
      (hlow t).2
  have h3a := jointEnergyFirstIntegrable_vpExt2 P hε 3 M M' (pIn 0) (pOut 0)
    crit_vpExt2_three.1 (hpoly3 8) hB8
  have h3b := jointEnergyFirstIntegrable_vpExt2 P hε 3 M M' (pIn 0) (pOut 0)
    crit_vpExt2_three.2 (hpoly3 3) hB3
  have hsum := jointEnergyFirstIntegrable_add (jointEnergyFirstIntegrable_add
    (jointEnergyFirstIntegrable_add (jointEnergyFirstIntegrable_add (hl 0) (hl 1)) (hl 2)) h3a) h3b
  refine (congrArg (QED.TwoLoop.jointEnergyFirstIntegrable 2) (funext fun ℓ => ?_)).mp hsum
  simp only [Fin.sum_univ_four, vpTermNumer, Fin.reduceEq, ↓reduceIte]
  ring

end VPExtSum

/-! ### The longitudinal pieces -/

section LPieces

/-- **A longitudinal piece of `repBD`**: `κ N_V(λ) ∏ᵢ D_{σ(i)}(λ)⁻¹` with the contracted
numerator `bdN` at `k = -λ₁` and `V` the momentum of line `eV`; lines `0, 1` are the open line
(rows `0, 1`) and line `2` a photon line of momentum `k` (row `4`). -/
theorem jointEnergyFirstIntegrable_bdPiece (P : Params) {m : ℕ} (hm : 7 ≤ m)
    (σ : Fin (m + 1) → Fin 6) (Ms : Fin (m + 1) → ℝ) (hε : 0 < P.ε) (p kext : Fin 4 → ℝ)
    (μ α β : Fin 4) (eV : Fin (m + 1)) {V : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ} (hV : IsLoopAffine V)
    (h0 : σ 0 = 0) (h1 : σ 1 = 1) (h2 : σ 2 = 4)
    (hVe : ∀ ℓ, V ℓ = classLineVP p (p + kext) (σ eV) ℓ) (h10 : (1 : Fin (m + 1)) ≠ 0)
    (h2E : (2 : Fin (m + 1)) ∉ ({1, 0} : Finset (Fin (m + 1))))
    (hVE : eV ∉ ({1, 0} : Finset (Fin (m + 1)))) (h2V : (2 : Fin (m + 1)) ≠ eV)
    (hcrit : IntNoSubdivergenceRefined 2 ({1, 0} ∪ {2} ∪ {eV}) fun i => class5LoopMatrix .VP (σ i))
    (κ : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      (κ * bdN P p kext μ α β (-ℓ 1) (V ℓ)) *
        ∏ i, (propDenom (Ms i) P.ε (classLineVP p (p + kext) (σ i) ℓ))⁻¹ := by
  set al := castLoopMatrix fun i => class5LoopMatrix .VP (σ i)
  set pp : Fin (m + 1) → Fin 4 → ℝ := fun i => classVPMomenta p (p + kext) (σ i)
  have hlm : ∀ e ℓ, lineMomentum al pp e ℓ = classLineVP p (p + kext) (σ e) ℓ := fun _ _ => rfl
  have r0 : ∀ ℓ, classLineVP p (p + kext) 0 ℓ = p - -ℓ 1 := fun ℓ => (classLineVP_rows _ _ ℓ).1
  have r1 : ∀ ℓ, classLineVP p (p + kext) 1 ℓ = p + kext - -ℓ 1 := fun ℓ =>
    (classLineVP_rows _ _ ℓ).2.1
  have r4 : ∀ ℓ, classLineVP p (p + kext) 4 ℓ = -ℓ 1 := fun ℓ =>
    (classLineVP_rows _ _ ℓ).2.2.2.2.1
  have hpoly : IsLoopPoly 2 4 fun ℓ => κ * bdN P p kext μ α β (-ℓ 1) (V ℓ) := by
    refine IsLoopPoly.const_mul κ ?_
    unfold bdN bdON
    exact isLoopPoly_contract P.m isLoopAffine_neg_one hV
      (IsLoopAffine.const_sub' isLoopAffine_neg_one (p + kext))
      (IsLoopAffine.const_sub' isLoopAffine_neg_one p)
      Dirac.gamma Dirac.gamma (Dirac.gamma μ) α β
  have hB : RefinedBound al ({1, 0} ∪ {2} ∪ {eV}) 4 fun ℓ =>
      κ * bdN P p kext μ α β (-ℓ 1) (V ℓ) := by
    refine RefinedBound.const_mul κ ?_
    unfold bdN bdON
    refine refinedBound_contract' al pp h2E hVE h2V (fun ℓ => -ℓ 1) V
      (fun ℓ => by rw [hlm, h2, r4]) (fun ℓ => by rw [hlm, hVe]) _ fun l0 l2 => ?_
    exact refinedBound_openNum al pp h10 P.m (fun ℓ => p + kext - -ℓ 1) (fun ℓ => p - -ℓ 1)
      (fun ℓ => by rw [hlm, h1, r1]) (fun ℓ => by rw [hlm, h0, r0]) _ _ _ α β
  exact jointEnergyFirstIntegrable_vpRows hm σ Ms hε p (p + kext) hcrit hpoly hB

/-- The lines of the piece with the loop `b₀ b₁ b₂` (momentum `q = λ₀`, row `3`). -/
def lineL1 : Fin 11 → Fin 6 := ![0, 1, 4, 4, 4, 4, 4, 4, 3, 3, 3]
/-- The lines of the piece with the loop `a₀ a₁ a₂` (momentum `q + k = λ₀ - λ₁`, row `2`). -/
def lineL2 : Fin 11 → Fin 6 := ![0, 1, 4, 4, 4, 4, 4, 4, 2, 2, 2]
/-- The lines of the piece `a₀ b₀ b₁ b₂`. -/
def lineL3a : Fin 12 → Fin 6 := ![0, 1, 4, 4, 4, 4, 4, 4, 2, 3, 3, 3]
/-- The lines of the piece `a₀ a₁ b₁ b₂`. -/
def lineL3b : Fin 12 → Fin 6 := ![0, 1, 4, 4, 4, 4, 4, 4, 2, 2, 3, 3]
/-- The lines of the piece `a₀ a₁ a₂ b₂`. -/
def lineL3c : Fin 12 → Fin 6 := ![0, 1, 4, 4, 4, 4, 4, 4, 2, 2, 2, 3]

/-- The masses of the pieces with three loop lines. -/
def massL1 (P : Params) : Fin 11 → ℝ := ![P.m, P.m, P.mγ, P.Λ, P.mγ, P.Λ, P.mγ, P.Λ, P.m, P.M₁, P.M₂]
/-- The masses of the piece `a₀ b₀ b₁ b₂`. -/
def massL3a (P : Params) : Fin 12 → ℝ :=
  ![P.m, P.m, P.mγ, P.Λ, P.mγ, P.Λ, P.mγ, P.Λ, P.m, P.m, P.M₁, P.M₂]
/-- The masses of the piece `a₀ a₁ b₁ b₂`. -/
def massL3b (P : Params) : Fin 12 → ℝ :=
  ![P.m, P.m, P.mγ, P.Λ, P.mγ, P.Λ, P.mγ, P.Λ, P.m, P.M₁, P.M₁, P.M₂]
/-- The masses of the piece `a₀ a₁ a₂ b₂`. -/
def massL3c (P : Params) : Fin 12 → ℝ :=
  ![P.m, P.m, P.mγ, P.Λ, P.mγ, P.Λ, P.mγ, P.Λ, P.m, P.M₁, P.M₂, P.M₂]

theorem crit_L : IntNoSubdivergenceRefined 2 ({1, 0} ∪ {2} ∪ {8}) (fun i => class5LoopMatrix .VP (lineL1 i)) ∧
    IntNoSubdivergenceRefined 2 ({1, 0} ∪ {2} ∪ {8}) (fun i => class5LoopMatrix .VP (lineL2 i)) ∧
    IntNoSubdivergenceRefined 2 ({1, 0} ∪ {2} ∪ {3}) (fun i => class5LoopMatrix .VP (lineL3a i)) ∧
    IntNoSubdivergenceRefined 2 ({1, 0} ∪ {2} ∪ {3}) (fun i => class5LoopMatrix .VP (lineL3b i)) ∧
    IntNoSubdivergenceRefined 2 ({1, 0} ∪ {2} ∪ {3}) (fun i => class5LoopMatrix .VP (lineL3c i)) := by
  decide

end LPieces

/-! ### `repBD`: the integrand as a sum of pieces, and (T₉′) -/

section BDAssembly

open QED.TwoLoop.ClassIntegrable

variable (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (αOut βIn μ : Fin 1 → Fin 4)

/-- The value integrand of `repBD s` in the nested routing, in the class variables
`q = λ₀`, `k = -λ₁`. -/
noncomputable def bdG (s : Fin 2) (pIn kIn : Fin 1 → Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
    regulatedAmplitude₂ P (repBD s) pIn kIn (bdMom s (pIn 0) (kIn 0) (ℓ 0) (-ℓ 1)) αOut βIn μ

theorem prod_lineL (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    (∏ i, (propDenom (massL1 P i) P.ε (classLineVP p p' (lineL1 i) ℓ))⁻¹) =
      (propDenom P.m P.ε (p - -ℓ 1))⁻¹ * (propDenom P.m P.ε (p' - -ℓ 1))⁻¹ *
        ((propDenom P.mγ P.ε (-ℓ 1))⁻¹ * (propDenom P.Λ P.ε (-ℓ 1))⁻¹) ^ 3 *
        ((propDenom P.m P.ε (ℓ 0))⁻¹ * (propDenom P.M₁ P.ε (ℓ 0))⁻¹ *
          (propDenom P.M₂ P.ε (ℓ 0))⁻¹) ∧
    (∏ i, (propDenom (massL1 P i) P.ε (classLineVP p p' (lineL2 i) ℓ))⁻¹) =
      (propDenom P.m P.ε (p - -ℓ 1))⁻¹ * (propDenom P.m P.ε (p' - -ℓ 1))⁻¹ *
        ((propDenom P.mγ P.ε (-ℓ 1))⁻¹ * (propDenom P.Λ P.ε (-ℓ 1))⁻¹) ^ 3 *
        ((propDenom P.m P.ε (ℓ 0 + -ℓ 1))⁻¹ * (propDenom P.M₁ P.ε (ℓ 0 + -ℓ 1))⁻¹ *
          (propDenom P.M₂ P.ε (ℓ 0 + -ℓ 1))⁻¹) ∧
    (∏ i, (propDenom (massL3a P i) P.ε (classLineVP p p' (lineL3a i) ℓ))⁻¹) =
      (propDenom P.m P.ε (p - -ℓ 1))⁻¹ * (propDenom P.m P.ε (p' - -ℓ 1))⁻¹ *
        ((propDenom P.mγ P.ε (-ℓ 1))⁻¹ * (propDenom P.Λ P.ε (-ℓ 1))⁻¹) ^ 3 *
        ((propDenom P.m P.ε (ℓ 0 + -ℓ 1))⁻¹ * (propDenom P.m P.ε (ℓ 0))⁻¹ *
          (propDenom P.M₁ P.ε (ℓ 0))⁻¹ * (propDenom P.M₂ P.ε (ℓ 0))⁻¹) ∧
    (∏ i, (propDenom (massL3b P i) P.ε (classLineVP p p' (lineL3b i) ℓ))⁻¹) =
      (propDenom P.m P.ε (p - -ℓ 1))⁻¹ * (propDenom P.m P.ε (p' - -ℓ 1))⁻¹ *
        ((propDenom P.mγ P.ε (-ℓ 1))⁻¹ * (propDenom P.Λ P.ε (-ℓ 1))⁻¹) ^ 3 *
        ((propDenom P.m P.ε (ℓ 0 + -ℓ 1))⁻¹ * (propDenom P.M₁ P.ε (ℓ 0 + -ℓ 1))⁻¹ *
          (propDenom P.M₁ P.ε (ℓ 0))⁻¹ * (propDenom P.M₂ P.ε (ℓ 0))⁻¹) ∧
    (∏ i, (propDenom (massL3c P i) P.ε (classLineVP p p' (lineL3c i) ℓ))⁻¹) =
      (propDenom P.m P.ε (p - -ℓ 1))⁻¹ * (propDenom P.m P.ε (p' - -ℓ 1))⁻¹ *
        ((propDenom P.mγ P.ε (-ℓ 1))⁻¹ * (propDenom P.Λ P.ε (-ℓ 1))⁻¹) ^ 3 *
        ((propDenom P.m P.ε (ℓ 0 + -ℓ 1))⁻¹ * (propDenom P.M₁ P.ε (ℓ 0 + -ℓ 1))⁻¹ *
          (propDenom P.M₂ P.ε (ℓ 0 + -ℓ 1))⁻¹ * (propDenom P.M₂ P.ε (ℓ 0))⁻¹) := by
  obtain ⟨r0, r1, r2, r3, r4, -⟩ := classLineVP_rows p p' ℓ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, lineL1, lineL2, lineL3a, lineL3b, lineL3c,
      massL1, massL3a, massL3b, massL3c, Matrix.cons_val_zero, Matrix.cons_val_succ, r0, r1, r2,
      r3, r4]
    ring

/-- The coefficient of the longitudinal pieces. -/
noncomputable def bdκL : ℂ :=
  (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * (P.δ₃ / 2 : ℂ) * ((I * P.e) ^ 5 * (1 / I) ^ 6 *
    (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)) ^ 3 * (4 * vpBubbleCoeff P))

/-- **The integrand of `repBD s` as a sum of pieces** (for `ε ≠ 0`, the Pauli–Villars conditions
and momentum conservation): two sums over the `VP` shapes with one, resp. two, extra photon
denominators, and the five longitudinal pieces. -/
theorem bdG_eq (s : Fin 2) (hε : P.ε ≠ 0) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    bdG P αOut βIn μ s pIn kIn ℓ =
      ((((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * (-(P.δ₃ / 2 : ℂ)) *
          ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)) *
        ∑ t : Fin 4, vpTermNumer P pOut pIn kIn αOut βIn μ t ℓ *
          ((∏ i : Fin 10, (vpDenom P t (pIn 0) (pOut 0) i ℓ)⁻¹) * (propDenom P.Λ P.ε (ℓ 1))⁻¹) +
      ((((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * (P.δ₃ / 2 : ℂ) *
          ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) * (((P.mγ ^ 2 : ℝ) : ℂ) - P.ε * I)) *
        ∑ t : Fin 4, vpTermNumer P pOut pIn kIn αOut βIn μ t ℓ *
          ((∏ i : Fin 10, (vpDenom P t (pIn 0) (pOut 0) i ℓ)⁻¹) *
            ((propDenom P.mγ P.ε (ℓ 1))⁻¹ * (propDenom P.Λ P.ε (ℓ 1))⁻¹)) +
      (bdκL P * bdN P (pIn 0) (kIn 0) (μ 0) (αOut 0) (βIn 0) (-ℓ 1) (ℓ 0)) *
        ∏ i, (propDenom (massL1 P i) P.ε (classLineVP (pIn 0) (pIn 0 + kIn 0) (lineL1 i) ℓ))⁻¹ +
      (-bdκL P * bdN P (pIn 0) (kIn 0) (μ 0) (αOut 0) (βIn 0) (-ℓ 1) (ℓ 0 + -ℓ 1)) *
        ∏ i, (propDenom (massL1 P i) P.ε (classLineVP (pIn 0) (pIn 0 + kIn 0) (lineL2 i) ℓ))⁻¹ +
      (-(bdκL P * ((P.ε : ℂ) * I)) * bdN P (pIn 0) (kIn 0) (μ 0) (αOut 0) (βIn 0) (-ℓ 1) (-ℓ 1)) *
        ∏ i, (propDenom (massL3a P i) P.ε
          (classLineVP (pIn 0) (pIn 0 + kIn 0) (lineL3a i) ℓ))⁻¹ +
      (-(bdκL P * ((P.ε : ℂ) * I)) * bdN P (pIn 0) (kIn 0) (μ 0) (αOut 0) (βIn 0) (-ℓ 1) (-ℓ 1)) *
        ∏ i, (propDenom (massL3b P i) P.ε
          (classLineVP (pIn 0) (pIn 0 + kIn 0) (lineL3b i) ℓ))⁻¹ +
      (-(bdκL P * ((P.ε : ℂ) * I)) * bdN P (pIn 0) (kIn 0) (μ 0) (αOut 0) (βIn 0) (-ℓ 1) (-ℓ 1)) *
        ∏ i, (propDenom (massL3c P i) P.ε
          (classLineVP (pIn 0) (pIn 0 + kIn 0) (lineL3c i) ℓ))⁻¹ := by
  obtain ⟨p1, p2, p3a, p3b, p3c⟩ := prod_lineL P (pIn 0) (pIn 0 + kIn 0) ℓ
  -- the vacuum-polarization part
  have hVP : ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
      contractionAmplitude₂ P QED.TwoLoop.NestedVP.cV (QED.TwoLoop.NestedVP.flavV f) pIn kIn
        (QED.TwoLoop.NestedVP.nestedMom (pIn 0) (kIn 0) (ℓ 0) (-ℓ 1)) αOut βIn μ =
      ∑ t : Fin 4, vpTermNumer P pOut pIn kIn αOut βIn μ t ℓ *
        ∏ i : Fin 10, (vpDenom P t (pIn 0) (pOut 0) i ℓ)⁻¹ := by
    rw [← QED.TwoLoop.NestedVP.regulatedAmplitude₂_nested,
      ← classMomVP_eq_nestedMom, ← hmom, regulatedAmplitude₂_classMomVP_shapes P hε hc₁ hc₂ hmom]
  -- the transverse coefficient
  have hDγ := propDenom_ne_zero (M := P.mγ) hε (ℓ 1)
  have hDΛ := propDenom_ne_zero (M := P.Λ) hε (ℓ 1)
  have hT : ((Minkowski.dot (-ℓ 1) (-ℓ 1) : ℝ) : ℂ) * photonScalar P.mγ P.Λ P.ε (-ℓ 1) =
      ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) * ((propDenom P.Λ P.ε (ℓ 1))⁻¹ -
        (((P.mγ ^ 2 : ℝ) : ℂ) - P.ε * I) *
          ((propDenom P.mγ P.ε (ℓ 1))⁻¹ * (propDenom P.Λ P.ε (ℓ 1))⁻¹)) := by
    have hs : photonScalar P.mγ P.Λ P.ε (-ℓ 1) =
        (propDenom P.mγ P.ε (ℓ 1))⁻¹ - (propDenom P.Λ P.ε (ℓ 1))⁻¹ := by
      rw [← propDenom_neg P.mγ P.ε (ℓ 1), ← propDenom_neg P.Λ P.ε (ℓ 1)]
      rfl
    have hdot : ((Minkowski.dot (-ℓ 1) (-ℓ 1) : ℝ) : ℂ) =
        propDenom P.mγ P.ε (ℓ 1) - (((P.mγ ^ 2 : ℝ) : ℂ) - P.ε * I) := by
      rw [← propDenom_neg P.mγ P.ε (ℓ 1)]
      simp only [propDenom]; push_cast; ring
    have hdiff : propDenom P.Λ P.ε (ℓ 1) - propDenom P.mγ P.ε (ℓ 1) =
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) := by
      simp only [propDenom]; push_cast; ring
    rw [hs, hdot, ← hdiff]
    field_simp
  -- the longitudinal part
  have hL := bdLong_sum P hε hc₁ hc₂ (pIn 0) (kIn 0) (ℓ 0) (-ℓ 1) (αOut 0) (βIn 0) (μ 0)
  unfold bdG
  rw [regulatedAmplitude₂_repBD]
  simp only [bd_amplitude_split, mul_add, Finset.sum_add_distrib]
  rw [show ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
      ((-(P.δ₃ / 2 : ℂ) * (((Minkowski.dot (-ℓ 1) (-ℓ 1) : ℝ) : ℂ) *
        photonScalar P.mγ P.Λ P.ε (-ℓ 1))) *
        contractionAmplitude₂ P QED.TwoLoop.NestedVP.cV (QED.TwoLoop.NestedVP.flavV f) pIn kIn
          (QED.TwoLoop.NestedVP.nestedMom (pIn 0) (kIn 0) (ℓ 0) (-ℓ 1)) αOut βIn μ) =
      (-(P.δ₃ / 2 : ℂ) * (((Minkowski.dot (-ℓ 1) (-ℓ 1) : ℝ) : ℂ) *
        photonScalar P.mγ P.Λ P.ε (-ℓ 1))) * ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
        contractionAmplitude₂ P QED.TwoLoop.NestedVP.cV (QED.TwoLoop.NestedVP.flavV f) pIn kIn
          (QED.TwoLoop.NestedVP.nestedMom (pIn 0) (kIn 0) (ℓ 0) (-ℓ 1)) αOut βIn μ by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring]
  rw [show ∑ f : Fin 3, (P.loopCoeff f : ℂ) * ((P.δ₃ / 2 : ℂ) *
      bdLong P f (pIn 0) (kIn 0) (ℓ 0) (-ℓ 1) (αOut 0) (βIn 0) (μ 0)) =
      (P.δ₃ / 2 : ℂ) * ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
        bdLong P f (pIn 0) (kIn 0) (ℓ 0) (-ℓ 1) (αOut 0) (βIn 0) (μ 0) by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring]
  rw [hVP, hT, hL, p1, p2, p3a, p3b, p3c]
  simp only [Fin.sum_univ_four, bdκL]
  ring

/-- **(T₉′) for the bubble–`δ₃` representatives**: at `ε > 0`, under the two Pauli–Villars
conditions and momentum conservation, the value integrand of `repBD s` satisfies both stages of
the joint energy-first integral, for all masses, cutoffs and counterterms. -/
theorem chainValueIntegrable_repBD (hε : 0 < P.ε) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hmom : pOut 0 = pIn 0 + kIn 0)
    (s : Fin 2) : ChainValueIntegrable P (repBD s) pOut pIn kIn αOut βIn μ := by
  have hG : QED.TwoLoop.jointEnergyFirstIntegrable 2 (bdG P αOut βIn μ s pIn kIn) := by
    have h1 := jointEnergyFirstIntegrable_vpSum_ext1 P hε pOut pIn kIn αOut βIn μ
      ((((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * (-(P.δ₃ / 2 : ℂ)) *
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)) P.Λ
    have h2 := jointEnergyFirstIntegrable_vpSum_ext2 P hε pOut pIn kIn αOut βIn μ
      ((((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * (P.δ₃ / 2 : ℂ) *
        ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) * (((P.mγ ^ 2 : ℝ) : ℂ) - P.ε * I)) P.mγ P.Λ
    obtain ⟨c1, c2, c3a, c3b, c3c⟩ := crit_L
    have hL1 := jointEnergyFirstIntegrable_bdPiece P (by norm_num) lineL1 (massL1 P) hε (pIn 0)
      (kIn 0) (μ 0) (αOut 0) (βIn 0) 8 isLoopAffine_zero' rfl rfl rfl
      (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.1.symm) (by decide) (by decide) (by decide)
      (by decide) c1 (bdκL P)
    have hL2 := jointEnergyFirstIntegrable_bdPiece P (by norm_num) lineL2 (massL1 P) hε (pIn 0)
      (kIn 0) (μ 0) (αOut 0) (βIn 0) 8 (IsLoopAffine.add' isLoopAffine_zero' isLoopAffine_neg_one)
      rfl rfl rfl (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.1.symm) (by decide) (by decide)
      (by decide) (by decide) c2 (-bdκL P)
    have hL3a := jointEnergyFirstIntegrable_bdPiece P (by norm_num) lineL3a (massL3a P) hε (pIn 0)
      (kIn 0) (μ 0) (αOut 0) (βIn 0) 3 isLoopAffine_neg_one rfl rfl rfl
      (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.2.1.symm) (by decide) (by decide) (by decide)
      (by decide) c3a (-(bdκL P * ((P.ε : ℂ) * I)))
    have hL3b := jointEnergyFirstIntegrable_bdPiece P (by norm_num) lineL3b (massL3b P) hε (pIn 0)
      (kIn 0) (μ 0) (αOut 0) (βIn 0) 3 isLoopAffine_neg_one rfl rfl rfl
      (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.2.1.symm) (by decide) (by decide) (by decide)
      (by decide) c3b (-(bdκL P * ((P.ε : ℂ) * I)))
    have hL3c := jointEnergyFirstIntegrable_bdPiece P (by norm_num) lineL3c (massL3c P) hε (pIn 0)
      (kIn 0) (μ 0) (αOut 0) (βIn 0) 3 isLoopAffine_neg_one rfl rfl rfl
      (fun ℓ => (classLineVP_rows _ _ ℓ).2.2.2.2.1.symm) (by decide) (by decide) (by decide)
      (by decide) c3c (-(bdκL P * ((P.ε : ℂ) * I)))
    have hsum := jointEnergyFirstIntegrable_add (jointEnergyFirstIntegrable_add
      (jointEnergyFirstIntegrable_add (jointEnergyFirstIntegrable_add
        (jointEnergyFirstIntegrable_add (jointEnergyFirstIntegrable_add h1 h2) hL1) hL2) hL3a)
          hL3b) hL3c
    refine (congrArg (QED.TwoLoop.jointEnergyFirstIntegrable 2) (funext fun ℓ => ?_)).mp hsum
    rw [bdG_eq P αOut βIn μ s hε.ne' hc₁ hc₂ hmom ℓ]
  unfold ChainValueIntegrable
  rw [loopCount_repBD]
  refine QED.TwoLoop.IntegrableOrderFive.jointEnergyFirstIntegrable_of_matAct !![1, 1; 1, 0]
    (by rw [Matrix.det_fin_two]; simp) ![-(pIn 0), -(pIn 0)] hG fun ℓ => ?_
  rw [lineMomentum₂_repBD s hmom, bdG]
  congr 3
  · funext ν
    simp [QED.TwoLoop.Relabel.matAct, Fin.sum_univ_two]
    ring
  · funext ν
    simp [QED.TwoLoop.Relabel.matAct, Fin.sum_univ_two]
    ring

end BDAssembly

end QED.ChainProof.RepsInt

end
