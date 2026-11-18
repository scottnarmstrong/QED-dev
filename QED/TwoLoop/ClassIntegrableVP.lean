/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ClassIntegrable
public import QED.TwoLoop.ParametricBridgeVPFlavour

/-!
# Integrability of both joint stages for the vacuum-polarization class at fixed `ε`

Obligation O2-7 (`docs/TWO-LOOP-DERIVATION.md`, section 4.3), its fixed-`ε` part, for the class
`VP`, and with it the hypothesis `hJ` of the nested-equals-joint theorem
`QED.TwoLoop.NestedVP.contractionValue₂_VP_eq_nested_energyFirst`.

For `ε > 0`, the two Pauli–Villars conditions and momentum conservation, the integrand of the
value (T₁₀) of `VP` in the frozen routing has both stages of the joint energy-first integral
integrable (`jointEnergyFirstIntegrable_VP`). Corollary: the nested-equals-joint theorem with
`hJ` discharged (`contractionValue₂_VP_eq_nested_energyFirst_of_hG`).

## Proof

The bridge (`QED/TwoLoop/ParametricBridgeVPFlavour.lean`, `regulatedAmplitude₂_classMomVP_shapes`)
writes the flavour-summed integrand in the class routing as `∑ₜ₌₀³ Nₜ ∏ᵢ₌₀⁹ D_{t,i}⁻¹`, with the
loop matrices `vpShapeMatrix t` (bubble shapes `(1,3)`, `(2,2)`, `(3,1)`, `(2,2)`). For
`t = 0, 1, 2`, `Nₜ = K (E₀ + m² E₂)`: `E₀` is the outer open-line factor times the loop trace,
a sum of products of entries of `m - k̸` over the open lines `0, 1` and of `-k̸` over the bubble
lines `2, 3`; `E₂` involves the open lines only. So `Nₜ` satisfies the pointwise bound
`RefinedBound α {0, 1, 2, 3} 4` (`refinedBound_vpE0`, `refinedBound_vpE2`, via the matrix form
`RefinedBoundMat`). For `t = 3`, `N₃ = -K E₂ (D_{3,8} + D_{3,3})`: each denominator is quadratic
in one bubble momentum, which is carried by two rows of the doubled-bubble matrix (`8` and `2`,
or `3` and `9`), so the two pieces satisfy `RefinedBound α {0, 1, 2, 8} 4` and
`RefinedBound α {0, 1, 3, 9} 4` (`refinedBound_lineDenom_of_eq`). The criterion
`NoSubdivergenceRefined 2` holds for each of the five (shape, line set) pairs (decided), so each
piece is integrable at both stages (`jointEnergyFirstIntegrable_vpPiece`); sums are integrable
(`jointEnergyFirstIntegrable_add`), and the unimodular change `chgVP` transports the result to
the frozen routing.
-/

@[expose] public section

open Complex

namespace QED.TwoLoop.ClassIntegrable

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix class5LoopMatrix
  RefinedBound LoopQuartic refinedBound_lineMomentum NoSubdivergenceRefined)

/-! ### Sums of integrable integrands -/

theorem jointEnergyFirstIntegrable_add {L : ℕ} {F G : (Fin L → Fin 4 → ℝ) → ℂ}
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable L F)
    (hG : QED.TwoLoop.jointEnergyFirstIntegrable L G) :
    QED.TwoLoop.jointEnergyFirstIntegrable L fun ℓ => F ℓ + G ℓ := by
  obtain ⟨hF1, hF2⟩ := hF
  obtain ⟨hG1, hG2⟩ := hG
  refine ⟨fun v => (hF1 v).add (hG1 v), ?_⟩
  have h : (fun v : Fin L → Fin 3 → ℝ => ∫ t : Fin L → ℝ,
      (F fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) +
        G fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) =
      fun v => (∫ t : Fin L → ℝ, F fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) +
        ∫ t : Fin L → ℝ, G fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ) :=
    funext fun v => MeasureTheory.integral_add (hF1 v) (hG1 v)
  rw [h]
  exact hF2.add hG2

/-! ### Matrix-valued numerators -/

/-- Every entry of a matrix-valued function satisfies the pointwise bound. -/
def RefinedBoundMat {m : ℕ} (al : Fin (m + 1) → Fin 2 → ℝ) (E : Finset (Fin (m + 1))) (k : ℕ)
    (A : (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ i j, RefinedBound al E k fun ℓ => A ℓ i j

namespace RefinedBoundMat

variable {m : ℕ} {al : Fin (m + 1) → Fin 2 → ℝ} {E E' : Finset (Fin (m + 1))} {k k' : ℕ}
  {A B : (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}

theorem const (C : Matrix (Fin 4) (Fin 4) ℂ) : RefinedBoundMat al ∅ 0 fun _ => C :=
  fun _ _ => RefinedBound.const _

theorem mul (hA : RefinedBoundMat al E k A) (hB : RefinedBoundMat al E' k' B) (hd : Disjoint E E') :
    RefinedBoundMat al (E ∪ E') (k + k') fun ℓ => A ℓ * B ℓ := fun i j => by
  simp only [Matrix.mul_apply]
  exact RefinedBound.sum _ fun l _ => (hA i l).mul (hB l j) hd

theorem trace (hA : RefinedBoundMat al E k A) : RefinedBound al E k fun ℓ => (A ℓ).trace := by
  simp only [Matrix.trace, Matrix.diag]
  exact RefinedBound.sum _ fun i _ => hA i i

end RefinedBoundMat

theorem lineMomentum_const_eq {m : ℕ} (al : Fin (m + 1) → Fin 2 → ℝ) (b : Fin 4 → ℝ)
    (e : Fin (m + 1)) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum al (fun _ => b) e ℓ = al e 0 • ℓ 0 + al e 1 • ℓ 1 + b := by
  funext μ
  simp [QED.Integration.TwoLoop.lineMomentum, Fin.sum_univ_two]

/-- `m - k̸` at a momentum affine in the loop momenta with the coefficients of line `e`. -/
theorem refinedBoundMat_electronNumerator {m : ℕ} (al : Fin (m + 1) → Fin 2 → ℝ)
    (e : Fin (m + 1)) (mass : ℝ) {F : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ} (b : Fin 4 → ℝ)
    (hF : ∀ ℓ, F ℓ = lineMomentum al (fun _ => b) e ℓ) :
    RefinedBoundMat al {e} 1 fun ℓ => electronNumerator mass (F ℓ) := fun i j => by
  simp only [hF]
  exact refinedBound_electronNumerator al (fun _ => b) e mass i j

/-- A line denominator whose momentum is repeated by a second line `j` is bounded by both
lines. -/
theorem refinedBound_lineDenom_of_eq {m : ℕ} (al : Fin (m + 1) → Fin 2 → ℝ)
    (pp : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (ε : ℝ) {i j : Fin (m + 1)}
    (hij : i ≠ j) (hmom : ∀ ℓ, lineMomentum al pp j ℓ = lineMomentum al pp i ℓ) :
    RefinedBound al ({i} ∪ {j}) 2 fun ℓ => lineDenom al pp M ε i ℓ := by
  have h : (fun ℓ => lineDenom al pp M ε i ℓ) = fun ℓ =>
      (∑ μ, ∑ ν, ((Minkowski.metric μ ν : ℝ) : ℂ) *
        (((lineMomentum al pp i ℓ μ : ℝ) : ℂ) * ((lineMomentum al pp j ℓ ν : ℝ) : ℂ))) +
      (((M i ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) := by
    funext ℓ
    simp only [hmom, lineDenom, Minkowski.dot]
    push_cast
    simp only [mul_assoc]
    ring
  rw [h]
  exact (RefinedBound.sum _ fun μ _ => RefinedBound.sum _ fun ν _ =>
    ((refinedBound_lineMomentum al pp i μ).mul (refinedBound_lineMomentum al pp j ν)
      (Finset.disjoint_singleton.mpr hij)).const_mul _).add
    ((RefinedBound.const _).mono (Finset.empty_subset _) (Nat.zero_le _))

/-! ### The numerators of the four shapes -/

theorem vpRows (t : Fin 4) :
    (castLoopMatrix (vpShapeMatrix t) 0 0 = 0 ∧ castLoopMatrix (vpShapeMatrix t) 0 1 = 1) ∧
      (castLoopMatrix (vpShapeMatrix t) 1 0 = 0 ∧ castLoopMatrix (vpShapeMatrix t) 1 1 = 1) ∧
      (castLoopMatrix (vpShapeMatrix t) 2 0 = 1 ∧ castLoopMatrix (vpShapeMatrix t) 2 1 = -1) ∧
      (castLoopMatrix (vpShapeMatrix t) 3 0 = 1 ∧ castLoopMatrix (vpShapeMatrix t) 3 1 = 0) := by
  fin_cases t <;> simp [castLoopMatrix, vpShapeMatrix, vpShapeLines, class5LoopMatrix]

/-- The outer open-line factor is bounded by the open lines `0, 1`. -/
theorem refinedBoundMat_outer (t : Fin 4) (P : Params) (p kext : Fin 4 → ℝ) (μ' ρ ν : Fin 4) :
    RefinedBoundMat (castLoopMatrix (vpShapeMatrix t)) (∅ ∪ {1} ∪ ∅ ∪ {0} ∪ ∅) (0 + 1 + 0 + 1 + 0)
      fun ℓ => Dirac.gamma ν * electronNumerator P.m (p + kext - -ℓ 1) * Dirac.gamma μ' *
        electronNumerator P.m (p - -ℓ 1) * Dirac.gamma ρ := by
  obtain ⟨⟨r00, r01⟩, ⟨r10, r11⟩, -, -⟩ := vpRows t
  have h1 : ∀ ℓ : Fin 2 → Fin 4 → ℝ, p + kext - -ℓ 1 =
      lineMomentum (castLoopMatrix (vpShapeMatrix t)) (fun _ => p + kext) 1 ℓ := fun ℓ => by
    rw [lineMomentum_const_eq, r10, r11]
    simp only [zero_smul, one_smul, zero_add, sub_neg_eq_add]
    abel
  have h0 : ∀ ℓ : Fin 2 → Fin 4 → ℝ, p - -ℓ 1 =
      lineMomentum (castLoopMatrix (vpShapeMatrix t)) (fun _ => p) 0 ℓ := fun ℓ => by
    rw [lineMomentum_const_eq, r00, r01]
    simp only [zero_smul, one_smul, zero_add, sub_neg_eq_add]
    abel
  exact ((((RefinedBoundMat.const (Dirac.gamma ν)).mul
    (refinedBoundMat_electronNumerator _ 1 P.m _ h1) (by decide)).mul
      (RefinedBoundMat.const (Dirac.gamma μ')) (by decide)).mul
        (refinedBoundMat_electronNumerator _ 0 P.m _ h0) (by decide)).mul
          (RefinedBoundMat.const (Dirac.gamma ρ)) (by decide)

/-- The loop factor `γ^σ (-q̸) γ^τ (-(q + k)̸)` is bounded by the bubble lines `3, 2`. -/
theorem refinedBoundMat_loop (t : Fin 4) (σ τ : Fin 4) :
    RefinedBoundMat (castLoopMatrix (vpShapeMatrix t)) (∅ ∪ {3} ∪ ∅ ∪ {2}) (0 + 1 + 0 + 1)
      fun ℓ => Dirac.gamma σ * electronNumerator 0 (ℓ 0) * Dirac.gamma τ *
        electronNumerator 0 (ℓ 0 + -ℓ 1) := by
  obtain ⟨-, -, ⟨r20, r21⟩, ⟨r30, r31⟩⟩ := vpRows t
  have h3 : ∀ ℓ : Fin 2 → Fin 4 → ℝ, ℓ 0 =
      lineMomentum (castLoopMatrix (vpShapeMatrix t)) (fun _ => 0) 3 ℓ := fun ℓ => by
    rw [lineMomentum_const_eq, r30, r31]
    simp
  have h2 : ∀ ℓ : Fin 2 → Fin 4 → ℝ, ℓ 0 + -ℓ 1 =
      lineMomentum (castLoopMatrix (vpShapeMatrix t)) (fun _ => 0) 2 ℓ := fun ℓ => by
    rw [lineMomentum_const_eq, r20, r21]
    simp only [one_smul, neg_smul, add_zero]
  exact (((RefinedBoundMat.const (Dirac.gamma σ)).mul
    (refinedBoundMat_electronNumerator _ 3 0 _ h3) (by decide)).mul
      (RefinedBoundMat.const (Dirac.gamma τ)) (by decide)).mul
        (refinedBoundMat_electronNumerator _ 2 0 _ h2) (by decide)

/-- **The pointwise bound for `E₀`**: by the open lines `0, 1` and the bubble lines `2, 3`. -/
theorem refinedBound_vpE0 (t : Fin 4) (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    RefinedBound (castLoopMatrix (vpShapeMatrix t)) {0, 1, 2, 3} 4
      (vpE0 P pIn kIn αOut βIn μ) := by
  unfold vpE0 vpNumerator vpNumer outerNum loopTrace
  refine RefinedBound.const_mul _ (RefinedBound.sum _ fun l0 _ => RefinedBound.sum _ fun l2 _ =>
    RefinedBound.sum _ fun l3 _ => RefinedBound.sum _ fun l4 _ => ?_)
  exact ((((refinedBoundMat_outer t P (pIn 0) (kIn 0) (μ 0) l0 l2 (αOut 0) (βIn 0)).mul
    (RefinedBound.const _) (by decide)).mul (RefinedBound.const _) (by decide)).mul
      (refinedBoundMat_loop t l3 l4).trace (by decide)).mono (by decide) (by norm_num)

/-- The pointwise bound for `E₂`: by the open lines `0, 1`. -/
theorem refinedBound_vpE2 (t : Fin 4) (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    RefinedBound (castLoopMatrix (vpShapeMatrix t)) {0, 1} 2 (vpE2 P pIn kIn αOut βIn μ) := by
  unfold vpE2 vpNumer2 outerNum
  refine RefinedBound.const_mul _ (RefinedBound.sum _ fun l0 _ => RefinedBound.sum _ fun l2 _ =>
    RefinedBound.sum _ fun l3 _ => RefinedBound.sum _ fun l4 _ => ?_)
  exact ((((refinedBoundMat_outer t P (pIn 0) (kIn 0) (μ 0) l0 l2 (αOut 0) (βIn 0)).mul
    (RefinedBound.const _) (by decide)).mul (RefinedBound.const _) (by decide)).mul
      (RefinedBound.const _) (by decide)).mono (by decide) (by norm_num)

/-! ### Integrability of the pieces -/

/-- A piece `F ∏ᵢ D_{t,i}⁻¹` with `F` a polynomial of degree at most four satisfying the pointwise
bound for a line set satisfying the criterion is integrable at both stages. -/
theorem jointEnergyFirstIntegrable_vpPiece (P : Params) (hε : 0 < P.ε) (t : Fin 4)
    (p p' : Fin 4 → ℝ) {E : Finset (Fin 10)}
    (hcrit : NoSubdivergenceRefined 2 E (castLoopMatrix (vpShapeMatrix t)))
    {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (hpoly : IsLoopPoly 2 4 F)
    (hB : RefinedBound (castLoopMatrix (vpShapeMatrix t)) E 4 F) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2
      (fun ℓ => F ℓ * ∏ i : Fin 10, (vpDenom P t p p' i ℓ)⁻¹) := by
  obtain ⟨Q, rfl⟩ := hpoly.exists_loopQuartic
  have h := QED.Integration.TwoLoop.jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined
    Q (castLoopMatrix (vpShapeMatrix t)) (vpShapeMomenta t p p') (vpShapeMasses P t)
    (by norm_num : 7 ≤ 9) hε hcrit hB
  exact h

theorem noSubdivergenceRefined_vpShape (t : Fin 4) :
    NoSubdivergenceRefined 2 {0, 1, 2, 3} (castLoopMatrix (vpShapeMatrix t)) :=
  (QED.Integration.TwoLoop.noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr (by
    revert t; decide)

theorem noSubdivergenceRefined_vpShape_three :
    NoSubdivergenceRefined 2 {0, 1, 2, 8} (castLoopMatrix (vpShapeMatrix 3)) ∧
      NoSubdivergenceRefined 2 {0, 1, 3, 9} (castLoopMatrix (vpShapeMatrix 3)) :=
  ⟨(QED.Integration.TwoLoop.noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr (by decide),
    (QED.Integration.TwoLoop.noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr (by decide)⟩

/-- **Both joint stages are integrable in the class routing of `VP`**, for every `ε > 0`. -/
theorem jointEnergyFirstIntegrable_VP_classRouting (P : Params) (hε : 0 < P.ε)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (fun ℓ =>
      (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        ∑ t : Fin 4, vpTermNumer P pOut pIn kIn αOut βIn μ t ℓ *
          ∏ i : Fin 10, (vpDenom P t (pIn 0) (pOut 0) i ℓ)⁻¹) := by
  set κ : ℂ := (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ with hκ
  set K := vpBubbleCoeff P with hK
  set E0 := vpE0 P pIn kIn αOut βIn μ with hE0
  set E2 := vpE2 P pIn kIn αOut βIn μ with hE2
  have hp0 := isLoopPoly_vpE0 P pIn kIn αOut βIn μ
  have hp2 := isLoopPoly_vpE2 P pIn kIn αOut βIn μ
  -- the terms `t = 0, 1, 2`
  have hlow : ∀ t : Fin 4, QED.TwoLoop.jointEnergyFirstIntegrable 2 (fun ℓ =>
      (κ * (K * (E0 ℓ + ((P.m ^ 2 : ℝ) : ℂ) * E2 ℓ))) *
        ∏ i : Fin 10, (vpDenom P t (pIn 0) (pOut 0) i ℓ)⁻¹) := fun t =>
    jointEnergyFirstIntegrable_vpPiece P hε t _ _ (noSubdivergenceRefined_vpShape t)
      (((hp0.add ((hp2.mono (by norm_num)).const_mul _)).const_mul K).const_mul κ)
      ((((refinedBound_vpE0 t P pIn kIn αOut βIn μ).add
        (((refinedBound_vpE2 t P pIn kIn αOut βIn μ).mono (by decide) (by norm_num)).const_mul
          _)).const_mul K).const_mul κ)
  -- the term `t = 3`, split along the two denominators
  have hpoly3 : ∀ i : Fin 10, IsLoopPoly 2 4
      (fun ℓ => κ * -(K * E2 ℓ * vpDenom P 3 (pIn 0) (pOut 0) i ℓ)) := fun i => by
    have h : IsLoopPoly 2 4 (fun ℓ => -κ * (K * E2 ℓ * vpDenom P 3 (pIn 0) (pOut 0) i ℓ)) :=
      (((hp2.const_mul K).mul (isLoopPoly_vpDenom P 3 (pIn 0) (pOut 0) i)).const_mul (-κ)).mono
        (by norm_num)
    refine (congrArg (IsLoopPoly 2 4) (funext fun ℓ => ?_)).mp h
    ring
  have hD8 : RefinedBound (castLoopMatrix (vpShapeMatrix 3)) ({8} ∪ {2}) 2
      (vpDenom P 3 (pIn 0) (pOut 0) 8) :=
    refinedBound_lineDenom_of_eq (castLoopMatrix (vpShapeMatrix 3))
      (vpShapeMomenta 3 (pIn 0) (pOut 0)) (vpShapeMasses P 3) P.ε (by decide) fun ℓ => rfl
  have hD3 : RefinedBound (castLoopMatrix (vpShapeMatrix 3)) ({3} ∪ {9}) 2
      (vpDenom P 3 (pIn 0) (pOut 0) 3) :=
    refinedBound_lineDenom_of_eq (castLoopMatrix (vpShapeMatrix 3))
      (vpShapeMomenta 3 (pIn 0) (pOut 0)) (vpShapeMasses P 3) P.ε (by decide) fun ℓ => rfl
  have h3a : QED.TwoLoop.jointEnergyFirstIntegrable 2 (fun ℓ =>
      (κ * -(K * E2 ℓ * vpDenom P 3 (pIn 0) (pOut 0) 8 ℓ)) *
        ∏ i : Fin 10, (vpDenom P 3 (pIn 0) (pOut 0) i ℓ)⁻¹) :=
    jointEnergyFirstIntegrable_vpPiece P hε 3 _ _ noSubdivergenceRefined_vpShape_three.1
      (hpoly3 8)
      ((((((refinedBound_vpE2 3 P pIn kIn αOut βIn μ).const_mul K).mul hD8 (by decide)).mono
        (by decide) (by norm_num)).neg).const_mul κ)
  have h3b : QED.TwoLoop.jointEnergyFirstIntegrable 2 (fun ℓ =>
      (κ * -(K * E2 ℓ * vpDenom P 3 (pIn 0) (pOut 0) 3 ℓ)) *
        ∏ i : Fin 10, (vpDenom P 3 (pIn 0) (pOut 0) i ℓ)⁻¹) :=
    jointEnergyFirstIntegrable_vpPiece P hε 3 _ _ noSubdivergenceRefined_vpShape_three.2
      (hpoly3 3)
      ((((((refinedBound_vpE2 3 P pIn kIn αOut βIn μ).const_mul K).mul hD3 (by decide)).mono
        (by decide) (by norm_num)).neg).const_mul κ)
  have hsum := jointEnergyFirstIntegrable_add (jointEnergyFirstIntegrable_add
    (jointEnergyFirstIntegrable_add (jointEnergyFirstIntegrable_add (hlow 0) (hlow 1)) (hlow 2))
      h3a) h3b
  convert hsum using 2 with ℓ
  simp only [Fin.sum_univ_four, vpTermNumer, Fin.reduceEq, ↓reduceIte]
  ring

/-- **O2-7 at fixed `ε` for `VP`**, the hypothesis `hJ` of the nested-equals-joint theorem: for
`ε > 0`, the two Pauli–Villars conditions and momentum conservation, the integrand of the value
(T₁₀) of `VP` in the frozen routing has both stages of the joint energy-first integral
integrable (T₉′). -/
theorem jointEnergyFirstIntegrable_VP (P : Params) (hε : 0 < P.ε) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2
      (NestedVP.frozenIntegrand P pOut pIn kIn αOut βIn μ) :=
  jointEnergyFirstIntegrable_of_comp matVP isUnit_det_matVP ![0, -(pIn 0)]
    (jointEnergyFirstIntegrable_VP_classRouting P hε pOut pIn kIn αOut βIn μ) fun ℓ => by
      rw [NestedVP.frozenIntegrand, lineMomentum₂_cV_class hmom,
        regulatedAmplitude₂_classMomVP_shapes P hε.ne' hc₁ hc₂ hmom]
      rfl

/-- **Nested equals joint for `VP` with the joint integrability proved**: the theorem
`QED.TwoLoop.NestedVP.contractionValue₂_VP_eq_nested_energyFirst` with its hypothesis `hJ`
discharged by `jointEnergyFirstIntegrable_VP`; the Fubini condition `hG` remains. -/
theorem contractionValue₂_VP_eq_nested_energyFirst_of_hG (P : Params)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4)
    (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hε : 0 < P.ε)
    (hG : ∀ᵐ w₂ : Fin 3 → ℝ, MeasureTheory.Integrable fun x : ℝ × (Fin 3 → ℝ) =>
      ∫ t₁ : ℝ, NestedVP.nestedIntegrand P (pIn 0) (kIn 0) (αOut 0) (βIn 0) (μ 0)
        ![Fin.cons t₁ x.2, Fin.cons x.1 w₂]) :
    contractionValue₂ P Class5.VP.rep pOut pIn kIn αOut βIn μ =
      QED.OneLoop.energyFirstIntegral fun k =>
        ∑ ρ : Fin 4, ∑ σ : Fin 4, NestedVP.vpOuter P (pIn 0) (kIn 0) k (αOut 0) (βIn 0) (μ 0) ρ σ *
          QED.OneLoop.energyFirstIntegral fun q =>
            QED.WickModel.vacuumPolarizationIntegrand P P.ε k q ρ σ :=
  NestedVP.contractionValue₂_VP_eq_nested_energyFirst P hmom αOut βIn μ hm hM₁ hM₂ hPV₁ hPV₂ hε
    (jointEnergyFirstIntegrable_VP P hε hPV₁ hPV₂ hmom αOut βIn μ) hG

end QED.TwoLoop.ClassIntegrable

end
