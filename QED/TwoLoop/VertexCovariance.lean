/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.SandwichReductionMirror
public import QED.Frozen.TwoLoop.IsVertexOrderFiveLimit
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The form factors of the order-`e⁵` vertex, reduced to covariance and the mirror identity

The second conclusion clause of the headline (HV₃) of packet T3 (decision D-41), at fixed
regulators: for the parameters of `QED.TwoLoop.VertexLimit.exists_isVertexOrderFiveLimit_headline`,
`e ≠ 0` and an on-shell pair with `q² > 0`, every `ε → 0⁺` limit `V` of the order-`e⁵` vertex
(HV₂) has exactly one form-factor pair (G₀), **provided** `V` is

* little-group covariant at `(p', p)` (`QED.Dirac.IsLittleGroupCovariant`; obligation O2-20),
  and
* mirror symmetric (`QED.OneLoop.IsMirrorSymmetric`: charge conjugation combined with the
  reflection in `p + p'`; obligation O2-21).

Both hypotheses are linear conditions on `V`. This file also proves that they pass to finite
sums and to entrywise integrals of integrable families, the form in which the class limits
(`-π⁴ ∫_Δ paramIntegrand`, `QED/TwoLoop/ClassLimit*.lean`) will be shown to satisfy them.

## Main statements

* `QED.TwoLoop.VertexCovariance.existsUnique_isFormFactorPair_headline`: the clause, from the two
  hypotheses.
* `QED.TwoLoop.VertexCovariance.isLittleGroupCovariant_integral`,
  `QED.TwoLoop.VertexCovariance.isMirrorSymmetric_integral`: the hypotheses pass to integrals.
* `QED.TwoLoop.VertexCovariance.isLittleGroupCovariant_sum`,
  `QED.TwoLoop.VertexCovariance.isMirrorSymmetric_sum`: and to finite linear combinations.
-/

@[expose] public section

open Matrix Complex MeasureTheory

namespace QED.TwoLoop.VertexCovariance

open QED.Dirac QED.OneLoop QED.WickModel

/-! ### Linearity -/

theorem vecAct_finset_sum {ι : Type*} (s : Finset ι) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (c : ι → ℂ) (V : ι → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4) :
    vecAct L (fun ν => ∑ k ∈ s, c k • V k ν) μ = ∑ k ∈ s, c k • vecAct L (V k) μ := by
  simp only [vecAct, Finset.smul_sum, smul_comm _ (c _)]
  rw [Finset.sum_comm]

/-- Little-group covariance passes to finite linear combinations. -/
theorem isLittleGroupCovariant_sum {ι : Type*} (s : Finset ι) {p' p : Fin 4 → ℝ} (c : ι → ℂ)
    {V : ι → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hV : ∀ k ∈ s, IsLittleGroupCovariant p' p (V k)) :
    IsLittleGroupCovariant p' p (fun μ => ∑ k ∈ s, c k • V k μ) := by
  intro L S T hST hγ hLp hLp' μ
  rw [vecAct_finset_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, hV k hk L S T hST hγ hLp hLp' μ]

/-- The mirror identity passes to finite linear combinations with real coefficients. -/
theorem isMirrorSymmetric_sum {ι : Type*} (s : Finset ι) {p' p : Fin 4 → ℝ} (c : ι → ℝ)
    {V : ι → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hV : ∀ k ∈ s, IsMirrorSymmetric p' p (V k)) :
    IsMirrorSymmetric p' p (fun μ => ∑ k ∈ s, ((c k : ℝ) : ℂ) • V k μ) := by
  intro μ
  set S := reflSpin (p' + p)
  set T := (((Minkowski.dot (p' + p) (p' + p) : ℝ) : ℂ)⁻¹ • reflSpin (p' + p))
  have e : ∀ (x : ℂ) (Z : Matrix (Fin 4) (Fin 4) ℂ),
      S * (chargeConj * (x • Z)ᵀ * chargeConj) * T = x • (S * (chargeConj * Zᵀ * chargeConj) * T) :=
    fun x Z => by
      rw [Matrix.transpose_smul, Matrix.mul_smul chargeConj, Matrix.smul_mul, Matrix.mul_smul S,
        Matrix.smul_mul]
  calc S * (chargeConj * (∑ k ∈ s, ((c k : ℝ) : ℂ) • V k μ)ᵀ * chargeConj) * T
      = ∑ k ∈ s, S * (chargeConj * (((c k : ℝ) : ℂ) • V k μ)ᵀ * chargeConj) * T := by
        rw [Matrix.transpose_sum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
    _ = ∑ k ∈ s, ((c k : ℝ) : ℂ) • -vecAct (reflectMatrix (p' + p)) (V k) μ :=
        Finset.sum_congr rfl fun k hk => by rw [e, hV k hk μ]
    _ = _ := by
        rw [vecAct_finset_sum, ← Finset.sum_neg_distrib]
        simp only [smul_neg]

/-! ### Integrals -/

/-- The vertex with entries `∫ f(x)^μ_{ij} dν(x)`. -/
noncomputable def integralVertex {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (f : X → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => Matrix.of fun i j => ∫ x, f x μ i j ∂ν

theorem integralVertex_mul {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f : X → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hf : ∀ μ i j, Integrable (fun x => f x μ i j) ν)
    (A B : Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4) :
    A * integralVertex ν f μ * B = integralVertex ν (fun x μ => A * f x μ * B) μ := by
  ext i j
  simp only [integralVertex, Matrix.mul_apply, Matrix.of_apply]
  rw [integral_finsetSum _ fun k _ => (integrable_finsetSum _ fun l _ =>
    ((hf μ l k).const_mul (A i l))).mul_const (B k j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_mul_const, integral_finsetSum _ fun l _ => (hf μ l k).const_mul (A i l)]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul]

theorem integralVertex_vecAct {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f : X → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hf : ∀ μ i j, Integrable (fun x => f x μ i j) ν)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (μ : Fin 4) :
    vecAct L (integralVertex ν f) μ = integralVertex ν (fun x => vecAct L (f x)) μ := by
  ext i j
  simp only [vecAct, integralVertex, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply,
    smul_eq_mul]
  rw [integral_finsetSum _ fun ρ _ => (hf ρ i j).const_mul _]
  exact Finset.sum_congr rfl fun ρ _ => (integral_const_mul _ _).symm

/-- **Little-group covariance passes to integrals**: if `f(x)` is little-group covariant for
every `x` and its entries are integrable, then so is `∫ f dν`. -/
theorem isLittleGroupCovariant_integral {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {p' p : Fin 4 → ℝ} {f : X → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hf : ∀ μ i j, Integrable (fun x => f x μ i j) ν)
    (hcov : ∀ x, IsLittleGroupCovariant p' p (f x)) :
    IsLittleGroupCovariant p' p (integralVertex ν f) := by
  intro L S T hST hγ hLp hLp' μ
  rw [integralVertex_mul hf, integralVertex_vecAct hf]
  simp only [integralVertex]
  ext i j
  simp only [Matrix.of_apply]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [hcov x L S T hST hγ hLp hLp' μ])

/-- **The mirror identity passes to integrals.** -/
theorem isMirrorSymmetric_integral {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {p' p : Fin 4 → ℝ} {f : X → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hf : ∀ μ i j, Integrable (fun x => f x μ i j) ν)
    (hmir : ∀ x, IsMirrorSymmetric p' p (f x)) :
    IsMirrorSymmetric p' p (integralVertex ν f) := by
  intro μ
  have hT : (integralVertex ν f μ)ᵀ = integralVertex ν (fun x μ => (f x μ)ᵀ) μ := by
    ext i j
    simp [integralVertex]
  have hfT : ∀ μ i j, Integrable (fun x => (f x μ)ᵀ i j) ν := fun μ i j => hf μ j i
  have hfT' : ∀ μ i j, Integrable (fun x => (chargeConj * (f x μ)ᵀ * chargeConj) i j) ν :=
    fun μ i j => by
      simp only [Matrix.mul_apply]
      exact integrable_finsetSum _ fun k _ => (integrable_finsetSum _ fun l _ =>
        ((hfT μ l k).const_mul _)).mul_const _
  rw [hT, integralVertex_mul hfT, integralVertex_mul hfT', integralVertex_vecAct hf]
  have hneg : -integralVertex ν (fun x => vecAct (reflectMatrix (p' + p)) (f x)) μ =
      integralVertex ν (fun x => -vecAct (reflectMatrix (p' + p)) (f x)) μ := by
    ext i j
    simp [integralVertex, integral_neg]
  rw [hneg]
  simp only [integralVertex]
  ext i j
  simp only [Matrix.of_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have := hmir x μ
  simp only [Matrix.mul_assoc] at this ⊢
  rw [this]
  rfl

/-! ### The clause of (HV₃) -/

/-- **The form-factor clause of (HV₃), from covariance and the mirror identity.** For the
parameters of the headline (`M₁, M₂ > m`, the Pauli–Villars conditions, `m_γ, Λ > 0`, any
counterterms), `e ≠ 0`, `m > 0` and an on-shell pair with `q² > 0`: every `ε → 0⁺` limit `V`
of the order-`e⁵` vertex that is little-group covariant (O2-20) and mirror symmetric (O2-21) has
a form-factor pair (G₀), and the pair is unique. -/
theorem existsUnique_isFormFactorPair_headline (P₀ : Params) (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (M₁ M₂ c₁ c₂ mγ Λ d₁ d₂ dm d₃ : ℝ) (p' p : Fin 4 → ℝ)
    (hp' : Minkowski.dot p' p' = -P₀.m ^ 2) (hp : Minkowski.dot p p = -P₀.m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (_hV : IsVertexOrderFiveLimit
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
        δm := dm, δ₃ := d₃ } p' p V)
    (hcov : IsLittleGroupCovariant p' p V) (hmir : IsMirrorSymmetric p' p V) :
    (∃ F : ℂ × ℂ, IsFormFactorPair P₀.e P₀.m p' p V F) ∧
      ∀ F G : ℂ × ℂ, IsFormFactorPair P₀.e P₀.m p' p V F →
        IsFormFactorPair P₀.e P₀.m p' p V G → F = G := by
  obtain ⟨F, hF, huniq⟩ :=
    existsUnique_isFormFactorPair_of_mirror he hm.ne' hp' hp hq hcov hmir
  exact ⟨⟨F, hF⟩, fun G H hG hH => (huniq G hG).trans (huniq H hH).symm⟩

end QED.TwoLoop.VertexCovariance

end
