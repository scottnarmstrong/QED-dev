/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ReflCovarianceClasses
public import QED.TwoLoop.ReflCovarianceCounterterm
public import QED.TwoLoop.CountertermMirrorPart
public import QED.TwoLoop.LimitCovariance

/-!
# The form-factor clause of the order-`e⁵` headline

Obligations O2-20 and O2-21 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4), closed at fixed
regulators. For the parameters of the headline (HV₃) (`m > 0`, `M₁, M₂ > m` with the two
Pauli–Villars conditions, `m_γ, Λ > 0`, any counterterms) and an on-shell positive-energy pair
`p, p'` with `q² > 0`:

* the limits of the seven classes `L, X, C₊, C₋, S₊, S₋, VP` and of the counterterm classes
  `δ₂ in`, `δ₃` (slot `0`) are covariant under the reflection `R_K` in `K = p + p'`
  (`QED.TwoLoop.LimitMirror.IsReflCovariantAt`). This is the case `L = R_K`, `S = K̸Γ`,
  `T = S/(K·K)` of their covariance under every real `L` with a spinor lift
  (`QED.TwoLoop.ReflCovariance.classLimitV_map`, `classLimitV_VP_map`, `ctLimitV_d2In_map`,
  `ctLimitV_d3Slot0_map`), since `R_K p' = -p`, `R_K p = -p'` and the limits at `(-p, -p')` exist;
* hence every `ε → 0⁺` limit `V` of the order-`e⁵` vertex (HV₂) is mirror symmetric
  (`isMirrorSymmetric_headline`), the hypotheses of
  `QED.TwoLoop.CountertermMirror.isMirrorSymmetric_headline_of_cov_ct` being discharged;
* with the little-group covariance of `V`
  (`QED.TwoLoop.LimitCovariance.isLittleGroupCovariant_headline`), **for `e ≠ 0` every such limit
  has exactly one form-factor pair** (G₀) (`existsUnique_isFormFactorPair_headline`), and a limit
  exists (`exists_isVertexOrderFiveLimit_and_existsUnique_isFormFactorPair_headline`).
-/

@[expose] public section

open Matrix Complex

namespace QED.TwoLoop.FormFactorClause

open QED.Dirac QED.OneLoop QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Relabel
  QED.TwoLoop.LimitCovariance QED.TwoLoop.LimitMirror QED.TwoLoop.ReflCovariance

section Refl

variable (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p' p : Fin 4 → ℝ}
  (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
  (hq : 0 < Minkowski.dot (p' - p) (p' - p))
include hm hmγ hΛ hp' hp hq

/-- **Reflection covariance of the open-line class limits.** -/
theorem isReflCovariantAt_classLimit_open {c : Class5}
    (hc : c ∈ ClassIntegrable.openClasses) : IsReflCovariantAt (classLimit c P) p' p := by
  intro μ
  rw [← reflectMatrix_mulVec, ← reflectMatrix_mulVec]
  exact classLimitV_map hc P hm hmγ hΛ (isSpinLift_reflect (dot_add_self_ne_zero hp' hp hq)) hp
    hp' hq.le μ

/-- **Reflection covariance of the limit of `VP`.** -/
theorem isReflCovariantAt_classLimit_VP (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0) (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) :
    IsReflCovariantAt (classLimit .VP P) p' p := by
  intro μ
  rw [← reflectMatrix_mulVec, ← reflectMatrix_mulVec]
  exact classLimitV_VP_map P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂
    (isSpinLift_reflect (dot_add_self_ne_zero hp' hp hq)) hp hp' hq.le μ

/-- **Reflection covariance of the seven class limits of five gauge vertices.** -/
theorem isReflCovariantAt_classLimit_of_mem_nonFurry (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0) (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {c : Class5} (hc : c ∈ Furry.nonFurry) : IsReflCovariantAt (classLimit c P) p' p := by
  by_cases hVP : c = .VP
  · subst hVP
    exact isReflCovariantAt_classLimit_VP P hm hmγ hΛ hp' hp hq hM₁ hM₂ hc₁ hc₂
  · exact isReflCovariantAt_classLimit_open P hm hmγ hΛ hp' hp hq
      (VertexLimit.mem_openClasses_of_mem_nonFurry c hc hVP)

/-- **Reflection covariance of the `δ₂ in` limit.** -/
theorem isReflCovariantAt_ctLimit_d2In : IsReflCovariantAt (ctLimit .d2In P) p' p := by
  intro μ
  rw [← reflectMatrix_mulVec, ← reflectMatrix_mulVec]
  exact ctLimitV_d2In_map P hm hmγ hΛ (isSpinLift_reflect (dot_add_self_ne_zero hp' hp hq)) hp
    hp' hq.le μ

/-- **Reflection covariance of the `δ₃` (slot `0`) limit.** -/
theorem isReflCovariantAt_ctLimit_d3Slot0 : IsReflCovariantAt (ctLimit .d3Slot0 P) p' p := by
  intro μ
  rw [← reflectMatrix_mulVec, ← reflectMatrix_mulVec]
  exact ctLimitV_d3Slot0_map P hm hmγ hΛ (isSpinLift_reflect (dot_add_self_ne_zero hp' hp hq))
    hp hp' hq.le μ

end Refl

/-- **The mirror identity of the order-`e⁵` limit (O2-21).** For the parameters of the headline
(HV₃) and an on-shell positive-energy pair with `q² > 0`, every `ε → 0⁺` limit `V` of the
order-`e⁵` vertex is mirror symmetric. -/
theorem isMirrorSymmetric_headline (P₀ : Params) (hm : 0 < P₀.m) (M₁ M₂ c₁ c₂ : ℝ)
    (hM₁ : P₀.m < M₁) (hM₂ : P₀.m < M₂) (hPV₁ : 1 + c₁ + c₂ = 0)
    (hPV₂ : P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (d₁ d₂ dm d₃ : ℝ) (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P₀.m ^ 2)
    (hp : Minkowski.dot p p = -P₀.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hV : IsVertexOrderFiveLimit
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
        δm := dm, δ₃ := d₃ } p' p V) :
    IsMirrorSymmetric p' p V :=
  CountertermMirror.isMirrorSymmetric_headline_of_cov_ct P₀ hm M₁ M₂ c₁ c₂ hM₁ hM₂ hPV₁ hPV₂ mγ Λ
    hmγ hΛ d₁ d₂ dm d₃ p' p hp' hp hp0' hp0 hq V hV
    (fun _ hc => isReflCovariantAt_classLimit_of_mem_nonFurry
      { P₀ with
          M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
          δm := dm, δ₃ := d₃ } hm hmγ hΛ hp' hp hq hM₁.le hM₂.le hPV₁ hPV₂ hc)
    (fun c hc => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact isReflCovariantAt_ctLimit_d2In
          { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hmγ hΛ hp' hp hq
      · exact isReflCovariantAt_ctLimit_d3Slot0
          { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hmγ hΛ hp' hp hq)

/-- **The form-factor clause of the headline (HV₃), at fixed regulators (O2-20, O2-21).** For
`e ≠ 0`, `m > 0`, regulator fermions `M₁, M₂ > m` with the Pauli–Villars conditions,
`m_γ, Λ > 0`, any counterterms, and an on-shell positive-energy pair `(p', p)` with `q² > 0`:
every `ε → 0⁺` limit `V` of the order-`e⁵` vertex (HV₂) has a form-factor pair (G₀), and any two
form-factor pairs of `V` are equal. -/
theorem existsUnique_isFormFactorPair_headline (P₀ : Params) (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (M₁ M₂ c₁ c₂ : ℝ) (hM₁ : P₀.m < M₁) (hM₂ : P₀.m < M₂) (hPV₁ : 1 + c₁ + c₂ = 0)
    (hPV₂ : P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (d₁ d₂ dm d₃ : ℝ) (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P₀.m ^ 2)
    (hp : Minkowski.dot p p = -P₀.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hV : IsVertexOrderFiveLimit
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
        δm := dm, δ₃ := d₃ } p' p V) :
    (∃ F : ℂ × ℂ, IsFormFactorPair P₀.e P₀.m p' p V F) ∧
      ∀ F G : ℂ × ℂ, IsFormFactorPair P₀.e P₀.m p' p V F →
        IsFormFactorPair P₀.e P₀.m p' p V G → F = G :=
  VertexCovariance.existsUnique_isFormFactorPair_headline P₀ he hm M₁ M₂ c₁ c₂ mγ Λ d₁ d₂ dm d₃
    p' p hp' hp hq V hV
    (isLittleGroupCovariant_headline P₀ hm M₁ M₂ c₁ c₂ hM₁ hM₂ hPV₁ hPV₂ mγ Λ hmγ hΛ d₁ d₂ dm d₃
      p' p hp' hp hp0' hp0 hq V hV)
    (isMirrorSymmetric_headline P₀ hm M₁ M₂ c₁ c₂ hM₁ hM₂ hPV₁ hPV₂ mγ Λ hmγ hΛ d₁ d₂ dm d₃ p' p
      hp' hp hp0' hp0 hq V hV)

/-- **The first two conclusions of the headline (HV₃) at fixed regulators**: the order-`e⁵`
vertex has an `ε → 0⁺` limit, and every such limit has exactly one form-factor pair. -/
theorem exists_isVertexOrderFiveLimit_and_existsUnique_isFormFactorPair_headline (P₀ : Params)
    (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (M₁ M₂ c₁ c₂ : ℝ) (hM₁ : P₀.m < M₁) (hM₂ : P₀.m < M₂)
    (hPV₁ : 1 + c₁ + c₂ = 0) (hPV₂ : P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) (mγ Λ : ℝ)
    (hmγ : 0 < mγ) (hΛ : 0 < Λ) (d₁ d₂ dm d₃ : ℝ) (p' p : Fin 4 → ℝ)
    (hp' : Minkowski.dot p' p' = -P₀.m ^ 2) (hp : Minkowski.dot p p = -P₀.m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p)) :
    (∃ V, IsVertexOrderFiveLimit
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
        δm := dm, δ₃ := d₃ } p' p V) ∧
    ∀ V, IsVertexOrderFiveLimit
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
        δm := dm, δ₃ := d₃ } p' p V →
      (∃ F : ℂ × ℂ, IsFormFactorPair P₀.e P₀.m p' p V F) ∧
        ∀ F G : ℂ × ℂ, IsFormFactorPair P₀.e P₀.m p' p V F →
          IsFormFactorPair P₀.e P₀.m p' p V G → F = G :=
  ⟨VertexLimit.exists_isVertexOrderFiveLimit_headline P₀ hm M₁ M₂ c₁ c₂ hM₁ hM₂ hPV₁ hPV₂ mγ Λ
      hmγ hΛ d₁ d₂ dm d₃ p' p hp' hp hp0' hp0 hq,
    fun V hV => existsUnique_isFormFactorPair_headline P₀ he hm M₁ M₂ c₁ c₂ hM₁ hM₂ hPV₁ hPV₂ mγ
      Λ hmγ hΛ d₁ d₂ dm d₃ p' p hp' hp hp0' hp0 hq V hV⟩

end QED.TwoLoop.FormFactorClause

end
