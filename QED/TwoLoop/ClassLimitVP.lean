/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ClassIntegrableVP
public import QED.TwoLoop.ClassLimit

/-!
# The `ε → 0⁺` limit of the vacuum-polarization class

Obligation O2-7 (`docs/TWO-LOOP-DERIVATION.md`, section 4.3), its limit part, for the class `VP`.
For `m, m_γ, Λ > 0`, regulator masses `M₁, M₂ ≥ m`, the two Pauli–Villars conditions
`1 + c₁ + c₂ = 0`, `m² + c₁M₁² + c₂M₂² = 0`, on-shell `p = pIn 0`, `p' = pOut 0` with
`(p' - p)² ≥ 0`, and momentum conservation, the value (T₁₀) of `VP` at prescription `ε`
converges as `ε → 0⁺`, for every choice of indices
(`QED.TwoLoop.ClassLimit.tendsto_contractionValue₂_VP`). The limit is a sum of five parametric
integrals at `ε = 0`, over the simplices of the bubble shapes `vpShapeMatrix t` (ten lines each),
with `ε`-independent numerators `vpPieceNumer j` (`j = 0, …, 4`, on the shapes
`vpPieceShape j = 0, 1, 2, 3, 3`).

## The `ε`-dependent numerator

By the bridge (`parametricForm_VP`) the value is the joint integral of
`(2π)⁻⁸ ∑ₜ₌₀³ Nₜ ∏ᵢ D_{t,i}⁻¹`. For `t = 0, 1, 2`, `Nₜ = K (E₀ + m² E₂)` does not depend on `ε`.
For `t = 3`, `N₃ = -K E₂ (D_{3,8} + D_{3,3})` contains two line denominators, each of which is
`D⁰ - iε` with `D⁰` its value at `ε = 0`. So (`integrand_VP_eq`)

`(2π)⁻⁸ N₃ = (2π)⁻⁸ (-K E₂ D⁰_{3,8}) + (2π)⁻⁸ (-K E₂ D⁰_{3,3}) + ε · 2i (2π)⁻⁸ K E₂`,

three `ε`-independent numerators, the last one multiplied by `ε`. Every piece satisfies the
pointwise bound and the refined criterion of `QED/TwoLoop/ClassIntegrableVP.lean` (line sets
`{0, 1, 2, 3}`, `{0, 1, 2, 8}`, `{0, 1, 3, 9}`), and `V ≥ (3/4) min(m², μ²) > 0`, `μ = min(m_γ, Λ)`,
for every shape (`symanzikV_vpShape_ge`). By
`QED.TwoLoop.ClassLimit.tendsto_jointEnergyFirstIntegral_of_refined` each piece converges; the
joint integral is additive on integrable pieces (`jointEnergyFirstIntegral_add`); and the last
piece is `ε` times a convergent quantity, so it tends to `0`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.TwoLoop.ClassLimit

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassIntegrable
open QED.Integration.TwoLoop (lineDenom castLoopMatrix RefinedBound LoopQuartic
  NoSubdivergenceRefined symanzikU symanzikV classVPMasses
  jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined)
open QED.Integration.Feynman (simplexSet)

/-! ### Linearity of the joint integral -/

/-- The joint integral (T₉) is additive on integrands whose two stages are integrable. -/
theorem jointEnergyFirstIntegral_add {L : ℕ} {F G : (Fin L → Fin 4 → ℝ) → ℂ}
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable L F)
    (hG : QED.TwoLoop.jointEnergyFirstIntegrable L G) :
    QED.TwoLoop.jointEnergyFirstIntegral L (fun ℓ => F ℓ + G ℓ) =
      QED.TwoLoop.jointEnergyFirstIntegral L F + QED.TwoLoop.jointEnergyFirstIntegral L G := by
  obtain ⟨hF1, hF2⟩ := hF
  obtain ⟨hG1, hG2⟩ := hG
  unfold QED.TwoLoop.jointEnergyFirstIntegral
  rw [← integral_add hF2 hG2]
  exact integral_congr_ae (Eventually.of_forall fun v => integral_add (hF1 v) (hG1 v))

/-- The joint integral (T₉) commutes with constant factors (no integrability needed). -/
theorem jointEnergyFirstIntegral_const_mul {L : ℕ} (c : ℂ) (F : (Fin L → Fin 4 → ℝ) → ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegral L (fun ℓ => c * F ℓ) =
      c * QED.TwoLoop.jointEnergyFirstIntegral L F := by
  unfold QED.TwoLoop.jointEnergyFirstIntegral
  simp only [integral_const_mul]

theorem jointEnergyFirstIntegrable_const_mul {L : ℕ} (c : ℂ) {F : (Fin L → Fin 4 → ℝ) → ℂ}
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable L F) :
    QED.TwoLoop.jointEnergyFirstIntegrable L (fun ℓ => c * F ℓ) := by
  obtain ⟨hF1, hF2⟩ := hF
  refine ⟨fun v => (hF1 v).const_mul c, ?_⟩
  simp only [integral_const_mul]
  exact hF2.const_mul c

/-! ### The five `ε`-independent pieces -/

/-- The shape of piece `j`: `0, 1, 2, 3, 3`. -/
def vpPieceShape : Fin 5 → Fin 4 := ![0, 1, 2, 3, 3]

/-- The `ε`-independent numerators of the five pieces: `(2π)⁻⁸ K (E₀ + m² E₂)` for the shapes
`0, 1, 2`, and `-(2π)⁻⁸ K E₂ D⁰_{3,8}`, `-(2π)⁻⁸ K E₂ D⁰_{3,3}` for shape `3`, with `D⁰` the line
denominators at `ε = 0`. -/
noncomputable def vpPieceNumer (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) (j : Fin 5) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  if j = 3 then
    twoLoopNorm * -(vpBubbleCoeff P * vpE2 P pIn kIn αOut βIn μ ℓ *
      lineDenom (castLoopMatrix (vpShapeMatrix 3)) (vpShapeMomenta 3 (pIn 0) (pOut 0))
        (vpShapeMasses P 3) 0 8 ℓ)
  else if j = 4 then
    twoLoopNorm * -(vpBubbleCoeff P * vpE2 P pIn kIn αOut βIn μ ℓ *
      lineDenom (castLoopMatrix (vpShapeMatrix 3)) (vpShapeMomenta 3 (pIn 0) (pOut 0))
        (vpShapeMasses P 3) 0 3 ℓ)
  else
    twoLoopNorm * (vpBubbleCoeff P * (vpE0 P pIn kIn αOut βIn μ ℓ +
      ((P.m ^ 2 : ℝ) : ℂ) * vpE2 P pIn kIn αOut βIn μ ℓ))

/-- The coefficient of `ε` in the numerator of shape `3`: `2i (2π)⁻⁸ K E₂`. -/
noncomputable def vpEpsNumer (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  2 * I * (twoLoopNorm * (vpBubbleCoeff P * vpE2 P pIn kIn αOut βIn μ ℓ))

/-- The product of the inverse line denominators of shape `t` at prescription `ε`. -/
noncomputable def vpDenomProd (P : Params) (t : Fin 4) (p p' : Fin 4 → ℝ) (ε : ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  ∏ i : Fin 10, (lineDenom (castLoopMatrix (vpShapeMatrix t)) (vpShapeMomenta t p p')
    (vpShapeMasses P t) ε i ℓ)⁻¹

theorem lineDenom_eps {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (M : Fin (m + 1) → ℝ) (ε : ℝ) (i : Fin (m + 1)) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineDenom α p M ε i ℓ = lineDenom α p M 0 i ℓ - (ε : ℂ) * I := by
  simp [lineDenom]

/-- **The integrand of `VP` at prescription `ε`, in `ε`-independent pieces.** -/
theorem integrand_VP_eq (P : Params) (ε : ℝ) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    twoLoopNorm * ∑ t : Fin 4, vpTermNumer { P with ε := ε } pOut pIn kIn αOut βIn μ t ℓ *
        ∏ i : Fin 10, (vpDenom { P with ε := ε } t (pIn 0) (pOut 0) i ℓ)⁻¹ =
      vpPieceNumer P pOut pIn kIn αOut βIn μ 0 ℓ * vpDenomProd P 0 (pIn 0) (pOut 0) ε ℓ +
        vpPieceNumer P pOut pIn kIn αOut βIn μ 1 ℓ * vpDenomProd P 1 (pIn 0) (pOut 0) ε ℓ +
        vpPieceNumer P pOut pIn kIn αOut βIn μ 2 ℓ * vpDenomProd P 2 (pIn 0) (pOut 0) ε ℓ +
        vpPieceNumer P pOut pIn kIn αOut βIn μ 3 ℓ * vpDenomProd P 3 (pIn 0) (pOut 0) ε ℓ +
        vpPieceNumer P pOut pIn kIn αOut βIn μ 4 ℓ * vpDenomProd P 3 (pIn 0) (pOut 0) ε ℓ +
        (ε : ℂ) * (vpEpsNumer P pIn kIn αOut βIn μ ℓ * vpDenomProd P 3 (pIn 0) (pOut 0) ε ℓ) := by
  have hD : ∀ (t : Fin 4) (i : Fin 10), vpDenom { P with ε := ε } t (pIn 0) (pOut 0) i ℓ =
      lineDenom (castLoopMatrix (vpShapeMatrix t)) (vpShapeMomenta t (pIn 0) (pOut 0))
        (vpShapeMasses P t) ε i ℓ := fun _ _ => rfl
  have hE0 : vpE0 { P with ε := ε } pIn kIn αOut βIn μ ℓ = vpE0 P pIn kIn αOut βIn μ ℓ := rfl
  have hE2 : vpE2 { P with ε := ε } pIn kIn αOut βIn μ ℓ = vpE2 P pIn kIn αOut βIn μ ℓ := rfl
  have hK : vpBubbleCoeff { P with ε := ε } = vpBubbleCoeff P := rfl
  simp only [Fin.sum_univ_four, vpTermNumer, Fin.reduceEq, ↓reduceIte, hD, hE0, hE2, hK,
    vpPieceNumer, vpEpsNumer, vpDenomProd]
  rw [lineDenom_eps _ _ _ ε 8, lineDenom_eps _ _ _ ε 3]
  ring

/-! ### Data of the pieces -/

theorem isLoopPoly_vpPieceNumer (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) (j : Fin 5) :
    IsLoopPoly 2 4 (vpPieceNumer P pOut pIn kIn αOut βIn μ j) := by
  have hp0 := isLoopPoly_vpE0 P pIn kIn αOut βIn μ
  have hp2 := isLoopPoly_vpE2 P pIn kIn αOut βIn μ
  have h3 : ∀ i : Fin 10, IsLoopPoly 2 4 fun ℓ => twoLoopNorm * -(vpBubbleCoeff P *
      vpE2 P pIn kIn αOut βIn μ ℓ * lineDenom (castLoopMatrix (vpShapeMatrix 3))
        (vpShapeMomenta 3 (pIn 0) (pOut 0)) (vpShapeMasses P 3) 0 i ℓ) := fun i => by
    have hD : IsLoopPoly 2 2 fun ℓ => lineDenom (castLoopMatrix (vpShapeMatrix 3))
        (vpShapeMomenta 3 (pIn 0) (pOut 0)) (vpShapeMasses P 3) 0 i ℓ :=
      isLoopPoly_vpDenom { P with ε := 0 } 3 (pIn 0) (pOut 0) i
    have h := (((hp2.const_mul (vpBubbleCoeff P)).mul hD).const_mul (-twoLoopNorm)).mono
      (by norm_num : 2 + 2 ≤ 4)
    refine (congrArg (IsLoopPoly 2 4) (funext fun ℓ => ?_)).mp h
    ring
  unfold vpPieceNumer
  split_ifs
  · exact h3 8
  · exact h3 3
  · exact (((hp0.add ((hp2.mono (by norm_num)).const_mul _)).const_mul _).const_mul _)

theorem isLoopPoly_vpEpsNumer (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) : IsLoopPoly 2 4 (vpEpsNumer P pIn kIn αOut βIn μ) :=
  ((((isLoopPoly_vpE2 P pIn kIn αOut βIn μ).mono (by norm_num)).const_mul _).const_mul
    _).const_mul _

/-- The line set of the pointwise bound of piece `j`. -/
def vpPieceLines : Fin 5 → Finset (Fin 10) :=
  ![{0, 1, 2, 3}, {0, 1, 2, 3}, {0, 1, 2, 3}, {0, 1, 2, 8}, {0, 1, 3, 9}]

theorem noSubdivergenceRefined_vpPiece (j : Fin 5) :
    NoSubdivergenceRefined 2 (vpPieceLines j)
      (castLoopMatrix (vpShapeMatrix (vpPieceShape j))) := by
  fin_cases j
  · exact noSubdivergenceRefined_vpShape 0
  · exact noSubdivergenceRefined_vpShape 1
  · exact noSubdivergenceRefined_vpShape 2
  · exact noSubdivergenceRefined_vpShape_three.1
  · exact noSubdivergenceRefined_vpShape_three.2

theorem refinedBound_vpPieceNumer (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) (j : Fin 5) :
    RefinedBound (castLoopMatrix (vpShapeMatrix (vpPieceShape j))) (vpPieceLines j) 4
      (vpPieceNumer P pOut pIn kIn αOut βIn μ j) := by
  have hlow : ∀ t : Fin 4, RefinedBound (castLoopMatrix (vpShapeMatrix t)) {0, 1, 2, 3} 4
      fun ℓ => twoLoopNorm * (vpBubbleCoeff P * (vpE0 P pIn kIn αOut βIn μ ℓ +
        ((P.m ^ 2 : ℝ) : ℂ) * vpE2 P pIn kIn αOut βIn μ ℓ)) := fun t =>
    (((refinedBound_vpE0 t P pIn kIn αOut βIn μ).add
      (((refinedBound_vpE2 t P pIn kIn αOut βIn μ).mono (by decide) (by norm_num)).const_mul
        _)).const_mul _).const_mul _
  have hD8 : RefinedBound (castLoopMatrix (vpShapeMatrix 3)) ({8} ∪ {2}) 2
      fun ℓ => lineDenom (castLoopMatrix (vpShapeMatrix 3)) (vpShapeMomenta 3 (pIn 0) (pOut 0))
        (vpShapeMasses P 3) 0 8 ℓ :=
    refinedBound_lineDenom_of_eq _ _ _ 0 (by decide) fun ℓ => rfl
  have hD3 : RefinedBound (castLoopMatrix (vpShapeMatrix 3)) ({3} ∪ {9}) 2
      fun ℓ => lineDenom (castLoopMatrix (vpShapeMatrix 3)) (vpShapeMomenta 3 (pIn 0) (pOut 0))
        (vpShapeMasses P 3) 0 3 ℓ :=
    refinedBound_lineDenom_of_eq _ _ _ 0 (by decide) fun ℓ => rfl
  fin_cases j
  · exact hlow 0
  · exact hlow 1
  · exact hlow 2
  · exact (((((refinedBound_vpE2 3 P pIn kIn αOut βIn μ).const_mul _).mul hD8 (by decide)).mono
      (by decide) (by norm_num)).neg).const_mul _
  · exact (((((refinedBound_vpE2 3 P pIn kIn αOut βIn μ).const_mul _).mul hD3 (by decide)).mono
      (by decide) (by norm_num)).neg).const_mul _

theorem refinedBound_vpEpsNumer (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    RefinedBound (castLoopMatrix (vpShapeMatrix 3)) {0, 1, 2, 3} 4
      (vpEpsNumer P pIn kIn αOut βIn μ) :=
  ((((refinedBound_vpE2 3 P pIn kIn αOut βIn μ).mono (by decide) (by norm_num)).const_mul
    _).const_mul _).const_mul _

/-- The mass condition of `symanzikV_vpShape_ge` with photon-mass lower bound `μ`. -/
theorem classVPMasses_vpShapeLines_le_of (P : Params) {μ : ℝ} (h₁ : P.m ^ 2 ≤ P.M₁ ^ 2)
    (h₂ : P.m ^ 2 ≤ P.M₂ ^ 2) (hγ : μ ^ 2 ≤ P.mγ ^ 2) (hΛ : μ ^ 2 ≤ P.Λ ^ 2) (t : Fin 4)
    (i : Fin 10) :
    classVPMasses P.m P.m μ μ (vpShapeLines t i) ^ 2 ≤ vpShapeMasses P t i ^ 2 := by
  fin_cases t <;> fin_cases i <;>
    simp [classVPMasses, vpShapeLines, vpShapeMasses, h₁, h₂, hγ, hΛ]

/-- **Positivity of `V` for the four shapes of `VP`**, with `μ = min(m_γ, Λ)`. -/
theorem symanzikV_vpShape_ge_min (P : Params) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (h₁ : P.m ^ 2 ≤ P.M₁ ^ 2) (h₂ : P.m ^ 2 ≤ P.M₂ ^ 2) (t : Fin 4) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {z : Fin 10 → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hz1 : ∑ i, z i = 1) (hU : symanzikU (castLoopMatrix (vpShapeMatrix t)) z ≠ 0) :
    3 / 4 * min (P.m ^ 2) (min P.mγ P.Λ ^ 2) ≤
      symanzikV (castLoopMatrix (vpShapeMatrix t)) (vpShapeMomenta t p p') (vpShapeMasses P t)
        z := by
  have hμ0 : 0 < min P.mγ P.Λ := lt_min hmγ hΛ
  exact symanzikV_vpShape_ge t (classVPMasses_vpShapeLines_le_of P h₁ h₂
    (pow_le_pow_left₀ hμ0.le (min_le_left _ _) 2) (pow_le_pow_left₀ hμ0.le (min_le_right _ _) 2) t)
    hp hp' hq hz hz1 hU

/-! ### The limit -/

/-- **O2-7's limit for `VP`, with the limit identified.** For `m, m_γ, Λ > 0`, `M₁, M₂ ≥ m`, the
two Pauli–Villars conditions, on-shell `p = pIn 0`, `p' = pOut 0` with `(p' - p)² ≥ 0`, and
momentum conservation: there are `LoopQuartic`s `Q j` with the values of the `ε`-independent
numerators `vpPieceNumer j` such that, for every choice of indices, the value (T₁₀) of `VP` at
prescription `ε` converges as `ε → 0⁺` to the sum over the five pieces of the parametric integrals
at `ε = 0` on their shapes. Each limit integrand is integrable. -/
theorem tendsto_contractionValue₂_VP (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (hp : Minkowski.dot (pIn 0) (pIn 0) = -P.m ^ 2)
    (hp' : Minkowski.dot (pOut 0) (pOut 0) = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (pOut 0 - pIn 0) (pOut 0 - pIn 0)) (αOut βIn μ : Fin 1 → Fin 4) :
    ∃ Q : Fin 5 → LoopQuartic, (∀ j, (Q j).eval = vpPieceNumer P pOut pIn kIn αOut βIn μ j) ∧
      (∀ j, IntegrableOn (paramIntegrand (Q j) (castLoopMatrix (vpShapeMatrix (vpPieceShape j)))
        (vpShapeMomenta (vpPieceShape j) (pIn 0) (pOut 0)) (vpShapeMasses P (vpPieceShape j)) 0)
        (simplexSet 9)) ∧
      Tendsto (fun ε => contractionValue₂ { P with ε := ε } Class5.VP.rep pOut pIn kIn αOut βIn μ)
        (𝓝[>] 0)
        (𝓝 (∑ j : Fin 5, -((π : ℂ) ^ 4) * ∫ x in simplexSet 9, paramIntegrand (Q j)
          (castLoopMatrix (vpShapeMatrix (vpPieceShape j)))
          (vpShapeMomenta (vpPieceShape j) (pIn 0) (pOut 0)) (vpShapeMasses P (vpPieceShape j)) 0
          x)) := by
  have h₁ : P.m ^ 2 ≤ P.M₁ ^ 2 := pow_le_pow_left₀ hm.le hM₁ 2
  have h₂ : P.m ^ 2 ≤ P.M₂ ^ 2 := pow_le_pow_left₀ hm.le hM₂ 2
  set c₀ := 3 / 4 * min (P.m ^ 2) (min P.mγ P.Λ ^ 2) with hc₀def
  have hc₀ : 0 < c₀ := mul_pos (by norm_num) (lt_min (by positivity) (pow_pos (lt_min hmγ hΛ) 2))
  have hV : ∀ t : Fin 4, ∀ z : Fin 10 → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU (castLoopMatrix (vpShapeMatrix t)) z ≠ 0 →
      c₀ ≤ symanzikV (castLoopMatrix (vpShapeMatrix t)) (vpShapeMomenta t (pIn 0) (pOut 0))
        (vpShapeMasses P t) z :=
    fun t _ hz hz1 hU => symanzikV_vpShape_ge_min P hmγ hΛ h₁ h₂ t hp hp' hq hz hz1 hU
  choose Q hQ using fun j =>
    (isLoopPoly_vpPieceNumer P pOut pIn kIn αOut βIn μ j).exists_loopQuartic
  obtain ⟨R, hR⟩ := (isLoopPoly_vpEpsNumer P pIn kIn αOut βIn μ).exists_loopQuartic
  have hB : ∀ j, RefinedBound (castLoopMatrix (vpShapeMatrix (vpPieceShape j))) (vpPieceLines j) 4
      (Q j).eval := fun j => by
    rw [hQ j]; exact refinedBound_vpPieceNumer P pOut pIn kIn αOut βIn μ j
  have hBR : RefinedBound (castLoopMatrix (vpShapeMatrix 3)) {0, 1, 2, 3} 4 R.eval := by
    rw [hR]; exact refinedBound_vpEpsNumer P pIn kIn αOut βIn μ
  -- the limits of the pieces
  have hT : ∀ j, Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ =>
      (Q j).eval ℓ * vpDenomProd P (vpPieceShape j) (pIn 0) (pOut 0) ε ℓ) (𝓝[>] 0)
      (𝓝 (-((π : ℂ) ^ 4) * ∫ x in simplexSet 9, paramIntegrand (Q j)
          (castLoopMatrix (vpShapeMatrix (vpPieceShape j)))
          (vpShapeMomenta (vpPieceShape j) (pIn 0) (pOut 0)) (vpShapeMasses P (vpPieceShape j)) 0
          x)) := fun j =>
    tendsto_jointEnergyFirstIntegral_of_refined (Q j) _ _ _ (by norm_num)
      (noSubdivergenceRefined_vpPiece j) (hB j) hc₀ (hV (vpPieceShape j))
  have hTR : Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ =>
      R.eval ℓ * vpDenomProd P 3 (pIn 0) (pOut 0) ε ℓ) (𝓝[>] 0)
      (𝓝 (-((π : ℂ) ^ 4) * ∫ x in simplexSet 9, paramIntegrand R
          (castLoopMatrix (vpShapeMatrix 3)) (vpShapeMomenta 3 (pIn 0) (pOut 0))
          (vpShapeMasses P 3) 0 x)) :=
    tendsto_jointEnergyFirstIntegral_of_refined R _ _ _ (by norm_num)
      (noSubdivergenceRefined_vpShape 3) hBR hc₀ (hV 3)
  have hI : ∀ j, ∀ ε : ℝ, 0 < ε → QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      (Q j).eval ℓ * vpDenomProd P (vpPieceShape j) (pIn 0) (pOut 0) ε ℓ := fun j ε hε =>
    QED.Integration.TwoLoop.jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined
      (Q j) _ _ _ (by norm_num) hε (noSubdivergenceRefined_vpPiece j) (hB j)
  have hIR : ∀ ε : ℝ, 0 < ε → QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      (ε : ℂ) * (R.eval ℓ * vpDenomProd P 3 (pIn 0) (pOut 0) ε ℓ) := fun ε hε =>
    jointEnergyFirstIntegrable_const_mul _
      (jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined
        R _ _ _ (by norm_num) hε (noSubdivergenceRefined_vpShape 3) hBR)
  refine ⟨Q, hQ, fun j => integrableOn_paramIntegrand_zero (Q j) _ _ _ (by norm_num)
    (noSubdivergenceRefined_vpPiece j) (hB j) hc₀ (hV (vpPieceShape j)), ?_⟩
  -- the `ε` piece tends to `0`
  have hε0 : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto' 0 0 Complex.ofReal_zero).mono_left nhdsWithin_le_nhds
  have hεR := hε0.mul hTR
  rw [zero_mul] at hεR
  have hsum := ((((((hT 0).add (hT 1)).add (hT 2)).add (hT 3)).add (hT 4)).add hεR)
  rw [add_zero] at hsum
  simp only [Fin.sum_univ_five]
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  simp only [← jointEnergyFirstIntegral_const_mul]
  rw [← jointEnergyFirstIntegral_add (hI 0 ε hε) (hI 1 ε hε),
    ← jointEnergyFirstIntegral_add (jointEnergyFirstIntegrable_add (hI 0 ε hε) (hI 1 ε hε))
      (hI 2 ε hε),
    ← jointEnergyFirstIntegral_add (jointEnergyFirstIntegrable_add (jointEnergyFirstIntegrable_add
      (hI 0 ε hε) (hI 1 ε hε)) (hI 2 ε hε)) (hI 3 ε hε),
    ← jointEnergyFirstIntegral_add (jointEnergyFirstIntegrable_add (jointEnergyFirstIntegrable_add
      (jointEnergyFirstIntegrable_add (hI 0 ε hε) (hI 1 ε hε)) (hI 2 ε hε)) (hI 3 ε hε))
      (hI 4 ε hε),
    ← jointEnergyFirstIntegral_add (jointEnergyFirstIntegrable_add (jointEnergyFirstIntegrable_add
      (jointEnergyFirstIntegrable_add (jointEnergyFirstIntegrable_add (hI 0 ε hε) (hI 1 ε hε))
        (hI 2 ε hε)) (hI 3 ε hε)) (hI 4 ε hε)) (hIR ε hε),
    (parametricForm_VP { P with ε := ε } hε.ne' hc₁ hc₂ hmom αOut βIn μ).1]
  congr 1
  funext ℓ
  rw [integrand_VP_eq]
  simp only [hQ, hR, vpPieceShape]
  rfl

/-- **The limit for `VP` exists and is unique**, under the hypotheses of
`tendsto_contractionValue₂_VP`. -/
theorem existsUnique_tendsto_contractionValue₂_VP (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (hp : Minkowski.dot (pIn 0) (pIn 0) = -P.m ^ 2)
    (hp' : Minkowski.dot (pOut 0) (pOut 0) = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (pOut 0 - pIn 0) (pOut 0 - pIn 0)) (αOut βIn μ : Fin 1 → Fin 4) :
    ∃! L : ℂ, Tendsto
      (fun ε => contractionValue₂ { P with ε := ε } Class5.VP.rep pOut pIn kIn αOut βIn μ)
      (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨Q, -, -, h⟩ :=
    tendsto_contractionValue₂_VP P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hmom hp hp' hq αOut βIn μ
  exact ⟨_, h, fun L hL => tendsto_nhds_unique hL h⟩

end QED.TwoLoop.ClassLimit

end
