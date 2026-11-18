/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ClassIntegrableFurryFlavour
import Mathlib.Tactic.LinearCombination

/-!
# Integrability of both joint stages for the Furry classes at fixed `ε`

Obligation O2-7 (`docs/TWO-LOOP-DERIVATION.md`, section 4.3), its fixed-`ε` part, for the two
Furry classes `Fp` and `Fm` of five gauge vertices (the two orientations of the closed
three-vertex fermion loop). For `ε > 0`, the two Pauli–Villars conditions on the regulator
fermions and momentum conservation, the integrand of the value (T₁₀) in the frozen routing (T₄)
has both stages of the joint energy-first integral integrable (T₉′):
`QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_Fp`, `…_Fm`. With the open-line classes
(`QED/TwoLoop/ClassIntegrable.lean`) and `VP` (`QED/TwoLoop/ClassIntegrableVP.lean`) this covers
all nine classes: every class value is a genuine joint integral
(`contractionValue₂_Fp_eq_of_integrable`, `contractionValue₂_Fm_eq_of_integrable`).

The Pauli–Villars conditions are needed: for one loop flavour the triangle (three propagators,
numerator of degree three in its loop momentum) is linearly divergent, and the loop matrix of a
single flavour violates the numerator-aware criterion (`not_intNoSubdivergenceRefined_single`).

## Proof

* **Frozen routing and flavours** (`QED/TwoLoop/ClassIntegrableFurryRouting.lean`): the line
  momenta are `baseMom p k j ℓ` with the loop matrix `furryMatrix`; the regulated amplitude is
  `∑_f c_f N_f D_f`, with `D_f` the six line denominators of flavour `f`
  (`amplitudeDenominator_flavF`, photon pairs combined, `ε ≠ 0`).
* **Evenness** (`QED/TwoLoop/ClassIntegrableFurryEven.lean`): `N_f = E₀ + M_f² E₂` with
  `E₀ = N(0)`, `E₂ = N(1) - N(0)`.
* **Divided difference** (`QED/TwoLoop/ClassIntegrableFurryFlavour.lean`): the flavour sum is
  `K [(E₀ + m² E₂) ∑ₛ₌₀⁵ Tₛ - E₂ ∑ₛ₌₀² Uₛ]`, with `Tₛ` products of five and `Uₛ` products of four
  inverse loop denominators. So the integrand is a sum of nine pieces `(a N(0) + b N(1)) ∏ᵢ Dᵢ⁻¹`
  with loop matrices `furryMatrix ∘ selT s` (ten lines) and `furryMatrix ∘ selU s` (nine lines)
  (`integrand_eq_pieces`).
* **Each piece** (`jointEnergyFirstIntegrable_piece`): `N(M)` is a polynomial of degree at most
  four and satisfies the pointwise bound by the line weights of the four fermion lines
  (`refinedBound_amplitudeNumerator`, at the parameters `withLoopMass P M`), and the criterion
  `NoSubdivergenceRefined 2` holds for each of the nine shapes with one row of each fermion line
  (decided), so the representation under the refined bound
  (`jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined`) applies.
* **`Fm`**: the value integrand of `F₋` is minus that of `F₊` after an integer unimodular affine
  change of loop momenta (`QED.TwoLoop.Furry.regulatedAmplitude₂_Fm`,
  `QED.TwoLoop.Relabel.LineCorr.exists_routing_change`), under which (T₉′) is invariant.
-/

@[expose] public section

namespace QED.TwoLoop.FurryIntegrable

open Complex QED.WickModel QED.TwoLoop.Enumeration
open QED.TwoLoop.Furry (cP cM lineP lineP_bijective val_lineP prod_lineP furryCorr)
open QED.TwoLoop.Bridge (lineIdx amplitudeNumerator amplitudeDenominator propDenom
  contractionAmplitude₂_eq IsLoopPoly isLoopPoly_amplitudeNumerator isLoopAffine_lineMomentum)
open QED.TwoLoop.ClassIntegrable (refinedBound_amplitudeNumerator jointEnergyFirstIntegrable_add)
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix RefinedBound
  IntNoSubdivergenceRefined noSubdivergenceRefined_castLoopMatrix_iff
  jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined)

/-! ### The amplitude in the frozen routing -/

/-- The line momenta of the frozen routing of `F₊`. -/
def kP (p k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (g : Line cP) : Fin 4 → ℝ :=
  baseMom p k (lineIdx g) ℓ

/-- The denominators of the amplitude of flavour `f`: the open line, the three loop lines of
mass `M_f`, and the two photon pairs. -/
theorem amplitudeDenominator_flavF (P : Params) (f : Fin 3) (p k : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    amplitudeDenominator P cP (flavF f) (kP p k ℓ) =
      (propDenom P.m P.ε (baseMom p k 0 ℓ))⁻¹ * (propDenom (P.mass f) P.ε (baseMom p k 1 ℓ))⁻¹ *
          (propDenom (P.mass f) P.ε (baseMom p k 2 ℓ))⁻¹ *
          (propDenom (P.mass f) P.ε (baseMom p k 3 ℓ))⁻¹ *
        (((propDenom P.mγ P.ε (baseMom p k 4 ℓ))⁻¹ * (propDenom P.Λ P.ε (baseMom p k 4 ℓ))⁻¹) *
          ((propDenom P.mγ P.ε (baseMom p k 5 ℓ))⁻¹ *
            (propDenom P.Λ P.ε (baseMom p k 5 ℓ))⁻¹)) := by
  obtain ⟨i0, i1, i2, i3, i4, i5⟩ := lineIdx_P
  obtain ⟨v0, v1, v2, v3⟩ := val_lineP
  obtain ⟨f0, f1, f2, f3, f4⟩ := flavF_apply f
  unfold amplitudeDenominator
  rw [prod_lineP, prod_photonLine]
  simp only [kP, i0, i1, i2, i3, i4, i5, v0, v1, v2, v3, f1, f2, f3, f4]
  rfl

/-- The numerator `N(M)` of `F₊` at loop mass `M` in the frozen routing. -/
noncomputable def numP (P : Params) (M : ℝ) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  furryNum P M pIn kIn (kP (pIn 0) (kIn 0) ℓ) αOut βIn μ

open scoped Classical in
/-- **The regulated amplitude of `F₊` as a flavour sum**: for `ε ≠ 0`,
`∑_f c_f (E₀ + M_f² E₂) D_f`. -/
theorem regulatedAmplitude₂_kP (P : Params) (hε : P.ε ≠ 0) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    regulatedAmplitude₂ P cP pIn kIn (kP (pIn 0) (kIn 0) ℓ) αOut βIn μ =
      ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
        ((numP P 0 pIn kIn αOut βIn μ ℓ + ((P.mass f ^ 2 : ℝ) : ℂ) *
            (numP P 1 pIn kIn αOut βIn μ ℓ - numP P 0 pIn kIn αOut βIn μ ℓ)) *
          amplitudeDenominator P cP (flavF f) (kP (pIn 0) (kIn 0) ℓ)) := by
  rw [regulatedAmplitude₂, sum_preserves]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [loopWeight_flavF, contractionAmplitude₂_eq P hε, amplitudeNumerator_flavF, furryNum_eq]
  rfl

/-! ### The nine shapes -/

/-- The line maps of the six terms with five loop denominators (ten lines): the open line, the
photon pairs, and the loop lines `1, 2, 3` with multiplicities `(1,1,3)`, `(1,2,2)`, `(1,3,1)`,
`(2,1,2)`, `(2,2,1)`, `(3,1,1)`. -/
def selT : Fin 6 → Fin 10 → Fin 6
  | 0 => ![0, 4, 4, 5, 5, 1, 2, 3, 3, 3]
  | 1 => ![0, 4, 4, 5, 5, 1, 2, 2, 3, 3]
  | 2 => ![0, 4, 4, 5, 5, 1, 2, 2, 2, 3]
  | 3 => ![0, 4, 4, 5, 5, 1, 1, 2, 3, 3]
  | 4 => ![0, 4, 4, 5, 5, 1, 1, 2, 2, 3]
  | 5 => ![0, 4, 4, 5, 5, 1, 1, 1, 2, 3]

/-- The masses of the six terms with five loop denominators: `a₀b₀d₀d₁d₂`, `a₀b₀b₁d₁d₂`,
`a₀b₀b₁b₂d₂`, `a₀a₁b₁d₁d₂`, `a₀a₁b₁b₂d₂`, `a₀a₁a₂b₂d₂`. -/
def massT (P : Params) : Fin 6 → Fin 10 → ℝ
  | 0 => ![P.m, P.mγ, P.Λ, P.mγ, P.Λ, P.m, P.m, P.m, P.M₁, P.M₂]
  | 1 => ![P.m, P.mγ, P.Λ, P.mγ, P.Λ, P.m, P.m, P.M₁, P.M₁, P.M₂]
  | 2 => ![P.m, P.mγ, P.Λ, P.mγ, P.Λ, P.m, P.m, P.M₁, P.M₂, P.M₂]
  | 3 => ![P.m, P.mγ, P.Λ, P.mγ, P.Λ, P.m, P.M₁, P.M₁, P.M₁, P.M₂]
  | 4 => ![P.m, P.mγ, P.Λ, P.mγ, P.Λ, P.m, P.M₁, P.M₁, P.M₂, P.M₂]
  | 5 => ![P.m, P.mγ, P.Λ, P.mγ, P.Λ, P.m, P.M₁, P.M₂, P.M₂, P.M₂]

/-- The row of the first copy of each fermion line `0, 1, 2, 3` in the ten-line shapes. -/
def rowT : Fin 6 → Fin 6 → Fin 10
  | 0 => ![0, 5, 6, 7, 0, 0]
  | 1 => ![0, 5, 6, 8, 0, 0]
  | 2 => ![0, 5, 6, 9, 0, 0]
  | 3 => ![0, 5, 7, 8, 0, 0]
  | 4 => ![0, 5, 7, 9, 0, 0]
  | 5 => ![0, 5, 8, 9, 0, 0]

/-- The line maps of the three terms with four loop denominators (nine lines): multiplicities
`(1,1,2)`, `(1,2,1)`, `(2,1,1)`. -/
def selU : Fin 3 → Fin 9 → Fin 6
  | 0 => ![0, 4, 4, 5, 5, 1, 2, 3, 3]
  | 1 => ![0, 4, 4, 5, 5, 1, 2, 2, 3]
  | 2 => ![0, 4, 4, 5, 5, 1, 1, 2, 3]

/-- The masses of the three terms with four loop denominators: `a₁b₁d₁d₂`, `a₁b₁b₂d₂`,
`a₁a₂b₂d₂`. -/
def massU (P : Params) : Fin 3 → Fin 9 → ℝ
  | 0 => ![P.m, P.mγ, P.Λ, P.mγ, P.Λ, P.M₁, P.M₁, P.M₁, P.M₂]
  | 1 => ![P.m, P.mγ, P.Λ, P.mγ, P.Λ, P.M₁, P.M₁, P.M₂, P.M₂]
  | 2 => ![P.m, P.mγ, P.Λ, P.mγ, P.Λ, P.M₁, P.M₂, P.M₂, P.M₂]

/-- The row of the first copy of each fermion line `0, 1, 2, 3` in the nine-line shapes. -/
def rowU : Fin 3 → Fin 6 → Fin 9
  | 0 => ![0, 5, 6, 7, 0, 0]
  | 1 => ![0, 5, 6, 8, 0, 0]
  | 2 => ![0, 5, 7, 8, 0, 0]

theorem selT_rowT : ∀ s : Fin 6, ∀ j : Fin 6, (j : ℕ) < 4 → selT s (rowT s j) = j := by decide

theorem rowT_inj : ∀ s : Fin 6, ∀ i j : Fin 6, (i : ℕ) < 4 → (j : ℕ) < 4 →
    rowT s i = rowT s j → i = j := by decide

theorem selU_rowU : ∀ s : Fin 3, ∀ j : Fin 6, (j : ℕ) < 4 → selU s (rowU s j) = j := by decide

theorem rowU_inj : ∀ s : Fin 3, ∀ i j : Fin 6, (i : ℕ) < 4 → (j : ℕ) < 4 →
    rowU s i = rowU s j → i = j := by decide

/-- **The criterion for the ten-line shapes**, with one row of each fermion line. -/
theorem intNoSubdivergenceRefined_selT : ∀ s : Fin 6,
    IntNoSubdivergenceRefined 2 (Finset.univ.image fun j : Fin 4 => rowT s j.castSucc.castSucc)
      (fun i => furryMatrix (selT s i)) := by
  decide

/-- **The criterion for the nine-line shapes**, with one row of each fermion line. -/
theorem intNoSubdivergenceRefined_selU : ∀ s : Fin 3,
    IntNoSubdivergenceRefined 2 (Finset.univ.image fun j : Fin 4 => rowU s j.castSucc.castSucc)
      (fun i => furryMatrix (selU s i)) := by
  decide

/-- **A single loop flavour violates the criterion**: the six lines of `F₊` with the four fermion
lines as numerator lines (the triangle is linearly divergent). -/
theorem not_intNoSubdivergenceRefined_single :
    ¬ IntNoSubdivergenceRefined 2 {0, 1, 2, 3} furryMatrix := by
  decide

/-! ### One piece -/

theorem mem_image_row {n : ℕ} (row : Fin 6 → Fin (n + 1)) (j : Fin 6) (hj : (j : ℕ) < 4) :
    row j ∈ Finset.univ.image fun i : Fin 4 => row i.castSucc.castSucc :=
  Finset.mem_image.mpr ⟨⟨j, hj⟩, Finset.mem_univ _, by congr 1⟩

/-- **One piece is integrable at both stages**: `(a N(0) + b N(1)) ∏ᵢ Dᵢ⁻¹` along a line map
`sel` (with masses `Ms`) whose loop matrix satisfies the criterion with one row `row j` of each
fermion line `j`. -/
theorem jointEnergyFirstIntegrable_piece {n : ℕ} (hn : 7 ≤ n) (P : Params) (hε : 0 < P.ε)
    (pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) (sel : Fin (n + 1) → Fin 6)
    (Ms : Fin (n + 1) → ℝ) (row : Fin 6 → Fin (n + 1))
    (hcrit : IntNoSubdivergenceRefined 2
      (Finset.univ.image fun i : Fin 4 => row i.castSucc.castSucc) (fun i => furryMatrix (sel i)))
    (hsel : ∀ j : Fin 6, (j : ℕ) < 4 → sel (row j) = j)
    (hinj : ∀ i j : Fin 6, (i : ℕ) < 4 → (j : ℕ) < 4 → row i = row j → i = j) (a b : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (fun ℓ =>
      (a * numP P 0 pIn kIn αOut βIn μ ℓ + b * numP P 1 pIn kIn αOut βIn μ ℓ) *
        ∏ i, (propDenom (Ms i) P.ε (baseMom (pIn 0) (kIn 0) (sel i) ℓ))⁻¹) := by
  classical
  set E := Finset.univ.image fun i : Fin 4 => row i.castSucc.castSucc
  set al := castLoopMatrix fun i => furryMatrix (sel i)
  set pp : Fin (n + 1) → Fin 4 → ℝ := fun i => furryMomenta (pIn 0) (kIn 0) (sel i)
  have hk : ∀ (ℓ : Fin 2 → Fin 4 → ℝ) (f : FermionLine cP),
      kP (pIn 0) (kIn 0) ℓ (.inl f) = lineMomentum al pp (row (lineIdx (.inl f : Line cP))) ℓ := by
    intro ℓ f
    change baseMom _ _ _ ℓ = baseMom (pIn 0) (kIn 0) (sel (row (lineIdx (.inl f : Line cP)))) ℓ
    rw [hsel _ (lineIdx_fermion_lt f)]
  have he : Function.Injective fun f : FermionLine cP => row (lineIdx (.inl f : Line cP)) :=
    fun f g h => lineIdx_fermion_injective
      (hinj _ _ (lineIdx_fermion_lt f) (lineIdx_fermion_lt g) h)
  have hB : ∀ M : ℝ, RefinedBound al E 4 (numP P M pIn kIn αOut βIn μ) := by
    intro M
    have h := refinedBound_amplitudeNumerator (withLoopMass P M) cP (flavF 1) pIn kIn al pp
      (kP (pIn 0) (kIn 0)) _ he hk αOut βIn μ
    refine h.mono ?_ card_fermionLine.le
    intro i hi
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hi
    exact mem_image_row row _ (lineIdx_fermion_lt f)
  have hP : ∀ M : ℝ, IsLoopPoly 2 4 (numP P M pIn kIn αOut βIn μ) := fun M =>
    (isLoopPoly_amplitudeNumerator (withLoopMass P M) cP (flavF 1) pIn kIn (kP (pIn 0) (kIn 0))
      (fun _ => isLoopAffine_lineMomentum _ _ _) αOut βIn μ).mono card_fermionLine.le
  obtain ⟨Q, hQ⟩ := (((hP 0).const_mul a).add ((hP 1).const_mul b)).exists_loopQuartic
  have hBQ : RefinedBound al E 4 Q.eval := by
    rw [hQ]
    exact ((hB 0).const_mul a).add ((hB 1).const_mul b)
  have h := jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined Q al pp Ms hn
    hε ((noSubdivergenceRefined_castLoopMatrix_iff 2 E _).mpr hcrit) hBQ
  rw [hQ] at h
  exact h

/-! ### The integrand as a sum of pieces -/

theorem prod_univ_ten {M : Type*} [CommMonoid M] (f : Fin 10 → M) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 * f 8 * f 9 := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, Fin.prod_univ_eight]
  rfl

theorem prod_univ_nine {M : Type*} [CommMonoid M] (f : Fin 9 → M) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 * f 8 := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_eight]
  rfl

/-- `K = (M₁² - m²)(M₂² - m²)`, the coefficient of the second divided difference. -/
noncomputable def furryCoeff (P : Params) : ℂ :=
  (((P.M₁ ^ 2 - P.m ^ 2) * (P.M₂ ^ 2 - P.m ^ 2) : ℝ) : ℂ)

/-- The loop measure `(2π)⁻⁸`. -/
noncomputable def loopMeasure : ℂ := (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹

/-- The ten-line piece `s`: `κK (E₀ + m² E₂) ∏ᵢ D_{s,i}⁻¹`. -/
noncomputable def pieceT (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)
    (s : Fin 6) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  (loopMeasure * furryCoeff P * (1 - ((P.m ^ 2 : ℝ) : ℂ)) * numP P 0 pIn kIn αOut βIn μ ℓ +
      loopMeasure * furryCoeff P * ((P.m ^ 2 : ℝ) : ℂ) * numP P 1 pIn kIn αOut βIn μ ℓ) *
    ∏ i, (propDenom (massT P s i) P.ε (baseMom (pIn 0) (kIn 0) (selT s i) ℓ))⁻¹

/-- The nine-line piece `s`: `-κK E₂ ∏ᵢ D_{s,i}⁻¹`. -/
noncomputable def pieceU (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)
    (s : Fin 3) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  (loopMeasure * furryCoeff P * numP P 0 pIn kIn αOut βIn μ ℓ +
      -(loopMeasure * furryCoeff P) * numP P 1 pIn kIn αOut βIn μ ℓ) *
    ∏ i, (propDenom (massU P s i) P.ε (baseMom (pIn 0) (kIn 0) (selU s i) ℓ))⁻¹

/-- **The integrand of `F₊` as a sum of nine pieces.** For `ε ≠ 0` and the two Pauli–Villars
conditions, `(2π)⁻⁸` times the regulated amplitude (T₈) in the frozen routing is
`∑ₛ₌₀⁵ pieceT s + ∑ₛ₌₀² pieceU s`. -/
theorem integrand_eq_pieces (P : Params) (hε : P.ε ≠ 0) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    loopMeasure * regulatedAmplitude₂ P cP pIn kIn (kP (pIn 0) (kIn 0) ℓ) αOut βIn μ =
      ∑ s : Fin 6, pieceT P pIn kIn αOut βIn μ s ℓ +
        ∑ s : Fin 3, pieceU P pIn kIn αOut βIn μ s ℓ := by
  rw [regulatedAmplitude₂_kP P hε]
  simp only [amplitudeDenominator_flavF, Fin.sum_univ_three, Fin.sum_univ_six, pieceT, pieceU,
    prod_univ_ten, prod_univ_nine]
  simp only [Params.loopCoeff, Params.mass, selT, massT, selU, massU, Matrix.cons_val,
    Fin.isValue, Complex.ofReal_one, furryCoeff]
  set B : Fin 6 → Fin 4 → ℝ := fun j => baseMom (pIn 0) (kIn 0) j ℓ with hB
  set N0 := numP P 0 pIn kIn αOut βIn μ ℓ
  set N1 := numP P 1 pIn kIn αOut βIn μ ℓ
  have key := flavourSum_triangle_propDenom hε (B 1) (B 2) (B 3) hc₁ hc₂ N0 (N1 - N0)
  linear_combination
    (loopMeasure * (propDenom P.m P.ε (B 0))⁻¹ *
      ((propDenom P.mγ P.ε (B 4))⁻¹ * (propDenom P.Λ P.ε (B 4))⁻¹) *
      ((propDenom P.mγ P.ε (B 5))⁻¹ * (propDenom P.Λ P.ε (B 5))⁻¹)) * key

end QED.TwoLoop.FurryIntegrable

namespace QED.TwoLoop.ClassIntegrable

open Complex QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.FurryIntegrable
open QED.TwoLoop.Furry (cP cM furryCorr)

/-- (T₉′) for the negation of an integrand. -/
theorem jointEnergyFirstIntegrable_neg {L : ℕ} {F : (Fin L → Fin 4 → ℝ) → ℂ}
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable L F) :
    QED.TwoLoop.jointEnergyFirstIntegrable L fun ℓ => -F ℓ := by
  obtain ⟨h1, h2⟩ := hF
  refine ⟨fun v => (h1 v).neg, ?_⟩
  simp only [MeasureTheory.integral_neg]
  exact h2.neg

/-- **O2-7 at fixed `ε` for `F₊`.** For `ε > 0`, the two Pauli–Villars conditions and momentum
conservation, the integrand `(2π)⁻⁸ A(ℓ)` of the value (T₁₀) of the Furry class `Fp` in the
frozen routing (T₄) has both stages of the joint energy-first integral integrable (T₉′). -/
theorem jointEnergyFirstIntegrable_Fp (P : Params) (hε : 0 < P.ε) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (fun ℓ =>
      (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P Class5.Fp.rep pIn kIn (lineMomentum₂ Class5.Fp.rep pOut pIn kIn ℓ)
          αOut βIn μ) := by
  have hT : ∀ s : Fin 6, QED.TwoLoop.jointEnergyFirstIntegrable 2
      (pieceT P pIn kIn αOut βIn μ s) := fun s =>
    jointEnergyFirstIntegrable_piece (by norm_num) P hε pIn kIn αOut βIn μ (selT s) (massT P s)
      (rowT s) (intNoSubdivergenceRefined_selT s) (selT_rowT s) (rowT_inj s) _ _
  have hU : ∀ s : Fin 3, QED.TwoLoop.jointEnergyFirstIntegrable 2
      (pieceU P pIn kIn αOut βIn μ s) := fun s =>
    jointEnergyFirstIntegrable_piece (by norm_num) P hε pIn kIn αOut βIn μ (selU s) (massU P s)
      (rowU s) (intNoSubdivergenceRefined_selU s) (selU_rowU s) (rowU_inj s) _ _
  have hsum := jointEnergyFirstIntegrable_add
    (jointEnergyFirstIntegrable_add (jointEnergyFirstIntegrable_add
      (jointEnergyFirstIntegrable_add (jointEnergyFirstIntegrable_add
        (jointEnergyFirstIntegrable_add (hT 0) (hT 1)) (hT 2)) (hT 3)) (hT 4)) (hT 5))
    (jointEnergyFirstIntegrable_add (jointEnergyFirstIntegrable_add (hU 0) (hU 1)) (hU 2))
  convert hsum using 2 with ℓ
  have hk : lineMomentum₂ Class5.Fp.rep pOut pIn kIn ℓ = kP (pIn 0) (kIn 0) ℓ :=
    funext (lineMomentum₂_cP hmom ℓ)
  rw [hk]
  have h := integrand_eq_pieces P hε.ne' hc₁ hc₂ pIn kIn αOut βIn μ ℓ
  rw [loopMeasure] at h
  rw [h, Fin.sum_univ_six, Fin.sum_univ_three]

/-- **O2-7 at fixed `ε` for `F₋`.** Under the hypotheses of `jointEnergyFirstIntegrable_Fp`, the
same holds for the other orientation `Fm`: its integrand is minus that of `Fp` after an integer
unimodular affine change of loop momenta. -/
theorem jointEnergyFirstIntegrable_Fm (P : Params) (hε : 0 < P.ε) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (fun ℓ =>
      (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P Class5.Fm.rep pIn kIn (lineMomentum₂ Class5.Fm.rep pOut pIn kIn ℓ)
          αOut βIn μ) := by
  have hP := rep_isOnePI .Fp
  have hM := rep_isOnePI .Fm
  have hsum : ∑ v, externalMomentum cP pOut pIn kIn v = 0 := by
    rw [QED.TwoLoop.Relabel.sum_externalMomentum hP.1]
    simp only [Fin.sum_univ_one, hmom, sub_self]
  obtain ⟨M, hMdet, a, h⟩ := furryCorr.exists_routing_change hP.2.1 hM.2.1
    (QED.TwoLoop.Furry.externalMomentum_Fm pOut pIn kIn) hsum (loopCount_rep .Fp)
    (loopCount_rep .Fm)
  refine jointEnergyFirstIntegrable_of_comp M hMdet a
    (jointEnergyFirstIntegrable_neg (jointEnergyFirstIntegrable_Fp P hε hc₁ hc₂ hmom αOut βIn μ))
    fun ℓ => ?_
  rw [QED.TwoLoop.Furry.regulatedAmplitude₂_Fm, h, mul_neg]
  rfl

/-- **The value of `F₊` is a genuine joint integral.** Under the hypotheses of
`jointEnergyFirstIntegrable_Fp`, the value (T₁₀) is the joint energy-first integral (T₉) of an
integrand whose two stages are integrable. -/
theorem contractionValue₂_Fp_eq_of_integrable (P : Params) (hε : 0 < P.ε)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0) (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P Class5.Fp.rep pOut pIn kIn αOut βIn μ =
        QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ =>
          (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
            regulatedAmplitude₂ P Class5.Fp.rep pIn kIn
              (lineMomentum₂ Class5.Fp.rep pOut pIn kIn ℓ) αOut βIn μ) ∧
      QED.TwoLoop.jointEnergyFirstIntegrable 2 (fun ℓ =>
        (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
          regulatedAmplitude₂ P Class5.Fp.rep pIn kIn
            (lineMomentum₂ Class5.Fp.rep pOut pIn kIn ℓ) αOut βIn μ) :=
  ⟨QED.TwoLoop.Relabel.contractionValue₂_eq_of_loopCount P (loopCount_rep .Fp) pOut pIn kIn αOut
      βIn μ,
    jointEnergyFirstIntegrable_Fp P hε hc₁ hc₂ hmom αOut βIn μ⟩

/-- **The value of `F₋` is a genuine joint integral**, under the same hypotheses. -/
theorem contractionValue₂_Fm_eq_of_integrable (P : Params) (hε : 0 < P.ε)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0) (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P Class5.Fm.rep pOut pIn kIn αOut βIn μ =
        QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ =>
          (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
            regulatedAmplitude₂ P Class5.Fm.rep pIn kIn
              (lineMomentum₂ Class5.Fm.rep pOut pIn kIn ℓ) αOut βIn μ) ∧
      QED.TwoLoop.jointEnergyFirstIntegrable 2 (fun ℓ =>
        (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
          regulatedAmplitude₂ P Class5.Fm.rep pIn kIn
            (lineMomentum₂ Class5.Fm.rep pOut pIn kIn ℓ) αOut βIn μ) :=
  ⟨QED.TwoLoop.Relabel.contractionValue₂_eq_of_loopCount P (loopCount_rep .Fm) pOut pIn kIn αOut
      βIn μ,
    jointEnergyFirstIntegrable_Fm P hε hc₁ hc₂ hmom αOut βIn μ⟩

end QED.TwoLoop.ClassIntegrable

end
