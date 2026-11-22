/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetASpecLimTerm
public import QED.Frozen.Graded.IsFamilyVertexLimit

/-!
# Set (a): the `ε → 0⁺` limit of the family vertex from an `ε`-uniform outer spectral form

Helper level for the set (a) headline (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`.
A *uniform spectral term* (`SALimTerm`) is the data of one term of the dressed outer vertex,
`EFI_ℓ ∫_Δ w_ε(x) specInt N m j Ms ε (√A(x))^{×r} (ξ(x))^{×r} ε`, with a weight `w_ε` that may
depend on `ε`; `SALimTerm.Hyp` collects the hypotheses of
`QED.ChainProof.SetASpec.saLim_tendsto_term` (the engine hypotheses on the numerator, `j ≤ k`,
measurable masses `√A ≥ M_lo` and parameters `ξ ∈ (0, 1)` a.e., weights with one integrable
majorant on `ε ∈ (0, 1]` converging almost everywhere).

* `SALimTerm.tendsto`: each term converges (`saLim_tendsto_term`).
* **`SetAOuterSpec`** (the named obligation that the set (a) nested form, the `ε`-uniform
  spectral form of `Π⁽⁴⁾_ε` and the outer numerator reduction together supply): for every entry
  `(μ, a, b)`, the family vertex at `ε ∈ (0, 1]` is a finite combination, with coefficients
  independent of `ε`, of uniform spectral terms satisfying `Hyp`.
* **`isFamilyVertexLimit_of_outerSpec`**: then the family vertex has an `ε → 0⁺` limit, the
  combination of the term limits `saLimTermLimit`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real
open QED.WickModel (Params Contraction)

namespace QED.ChainProof.SetASpec

open QED.OneLoop QED.Integration.Feynman QED.TwoLoop.VPUnitNested QED.TwoLoop.VPHalfAtGen

/-- **A uniform spectral term** of the dressed outer vertex over `k + 2` photon-type
denominators: numerator `N` with leading energy coefficient `α`, power `j` of `k²`, `r` spectral
factors of mass `√A` and parameter `ξ` on the simplex of dimension `n`, weight `w ε` and limit
weight `w₀`. -/
structure SALimTerm where
  /-- The outer numerator. -/
  N : (Fin 4 → ℝ) → ℂ
  /-- Its leading coefficient in the loop energy. -/
  α : ℂ
  /-- The power of `k²`. -/
  j : ℕ
  /-- The number of spectral factors. -/
  r : ℕ
  /-- The simplex dimension. -/
  n : ℕ
  /-- The mass square of the spectral factor. -/
  A : (Fin n → ℝ) → ℝ
  /-- The Feynman parameter of the spectral factor. -/
  ξ : (Fin n → ℝ) → ℝ
  /-- The weight at `ε`. -/
  w : ℝ → (Fin n → ℝ) → ℂ
  /-- The limit weight. -/
  w₀ : (Fin n → ℝ) → ℂ

namespace SALimTerm

/-- The hypotheses of `saLim_tendsto_term` on a term, at `k + 2` photon-type denominators. -/
def Hyp (k : ℕ) (Mlo : ℝ) (τ : SALimTerm) : Prop :=
  Continuous τ.N ∧
    (∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      τ.N (Fin.cons t v : Fin 4 → ℝ) = τ.α * (t : ℂ) ^ 2 + β * t + γ) ∧
    (∃ CN : ℝ, ∀ ℓ, ‖τ.N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) ∧ τ.j ≤ k ∧
    Measurable τ.A ∧ Measurable τ.ξ ∧ (∀ x, Mlo ^ 2 ≤ τ.A x) ∧
    (∀ᵐ x ∂(volume.restrict (simplexSet τ.n)), τ.ξ x ∈ Ioo (0 : ℝ) 1) ∧
    (∃ h : (Fin τ.n → ℝ) → ℝ, IntegrableOn h (simplexSet τ.n) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        AEStronglyMeasurable (τ.w ε) (volume.restrict (simplexSet τ.n)) ∧
        ∀ᵐ x ∂(volume.restrict (simplexSet τ.n)), ‖τ.w ε x‖ ≤ h x) ∧
    ∀ᵐ x ∂(volume.restrict (simplexSet τ.n)),
      Tendsto (fun ε => τ.w ε x) (𝓝[>] 0) (𝓝 (τ.w₀ x))

/-- The value of a term at `ε`: the energy-first integral of its outer integrand. -/
noncomputable def val (m : ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (p' p : Fin 4 → ℝ) (τ : SALimTerm)
    (ε : ℝ) : ℂ :=
  energyFirstIntegral (saLimTermInt τ.N m τ.j Ms τ.r τ.A τ.ξ (τ.w ε) ε p' p)

/-- The limit of a term. -/
noncomputable def lim (m : ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (p' p : Fin 4 → ℝ)
    (τ : SALimTerm) : ℂ :=
  saLimTermLimit τ.α τ.N m p' p τ.j Ms τ.r τ.A τ.ξ τ.w₀

/-- **Each uniform spectral term converges** as `ε → 0⁺`. -/
theorem tendsto {m M₀ Mlo : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀) (hMlo : M₀ ≤ Mlo)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {k : ℕ} {Ms : Fin (k + 2) → ℝ} (hMs : ∀ i, M₀ ≤ Ms i)
    {τ : SALimTerm} (hτ : τ.Hyp k Mlo) :
    Tendsto (τ.val m Ms p' p) (𝓝[>] 0) (𝓝 (τ.lim m Ms p' p)) := by
  obtain ⟨hNc, hNq, ⟨CN, hNb⟩, hjk, hA, hξ, hAlo, hξ01, ⟨h, hh, hw⟩, hwl⟩ := hτ
  exact (saLim_tendsto_term hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hMlo hjk Ms hMs τ.r hA hξ hAlo
    hξ01 τ.w τ.w₀ h hh (fun ε h0 h1 => (hw ε h0 h1).1) (fun ε h0 h1 => (hw ε h0 h1).2) hwl).2

/-- **A finite combination of uniform spectral terms converges.** -/
theorem tendsto_sum {m M₀ Mlo : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀) (hMlo : M₀ ≤ Mlo)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {k : ℕ} {Ms : Fin (k + 2) → ℝ} (hMs : ∀ i, M₀ ≤ Ms i)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (τ : ι → SALimTerm) (hτ : ∀ i ∈ s, (τ i).Hyp k Mlo) :
    Tendsto (fun ε => ∑ i ∈ s, c i * (τ i).val m Ms p' p ε) (𝓝[>] 0)
      (𝓝 (∑ i ∈ s, c i * (τ i).lim m Ms p' p)) :=
  tendsto_finsetSum s fun i hi =>
    (tendsto (hm := hm) hM₀ hMlo hp' hp hp0' hp0 hMs (hτ i hi)).const_mul (c i)

end SALimTerm

/-- **The `ε`-uniform outer spectral form of a family vertex** (open for set (a); it is what the
nested form at fixed `ε`, the `ε`-uniform spectral form of `Π⁽⁴⁾_ε` and the outer numerator
reduction supply together): photon-type masses `Ms ≥ M₀` over `k + 2` denominators, and for every
entry a finite combination, with `ε`-independent coefficients, of uniform spectral terms that
satisfy `Hyp k M_lo` and give the entry at every `ε ∈ (0, 1]`. -/
def SetAOuterSpec (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Graded.Counterterms F)
    (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction 1 1 κ → Graded.Grading κ → Prop)
    (K : ℕ) (p' p : Fin 4 → ℝ) : Prop :=
  ∃ (M₀ Mlo : ℝ) (k : ℕ) (Ms : Fin (k + 2) → ℝ), 0 < M₀ ∧ M₀ ≤ Mlo ∧ (∀ i, M₀ ≤ Ms i) ∧
    ∀ μ a b : Fin 4, ∃ (s : Finset ℕ) (c : ℕ → ℂ) (τ : ℕ → SALimTerm),
      (∀ i ∈ s, (τ i).Hyp k Mlo) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        Graded.familyVertex { P with ε := ε } Φ D Sel K p' p μ a b =
          ∑ i ∈ s, c i * (τ i).val P.m Ms p' p ε

/-- **The family vertex has an `ε → 0⁺` limit** when it has an `ε`-uniform outer spectral form,
at an on-shell positive-energy pair. -/
theorem isFamilyVertexLimit_of_outerSpec (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F)
    (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction 1 1 κ → Graded.Grading κ → Prop)
    (K : ℕ) {p' p : Fin 4 → ℝ} (hm : 0 < P.m) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
    (h : SetAOuterSpec P Φ D Sel K p' p) :
    ∃ V, Graded.IsFamilyVertexLimit P Φ D Sel K p' p V := by
  obtain ⟨M₀, Mlo, k, Ms, hM₀, hMlo, hMs, hent⟩ := h
  choose s c τ hτ he using hent
  refine ⟨fun μ => Matrix.of fun a b => ∑ i ∈ s μ a b, c μ a b i *
    (τ μ a b i).lim P.m Ms p' p, fun μ a b => ?_⟩
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 := by
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε using hε
  refine Tendsto.congr' ?_ (SALimTerm.tendsto_sum hm hM₀ hMlo hp' hp hp0' hp0 hMs (s μ a b)
    (c μ a b) (τ μ a b) (hτ μ a b))
  filter_upwards [hev] with ε hε
  exact (he μ a b ε hε.1 hε.2).symm

end QED.ChainProof.SetASpec

end
