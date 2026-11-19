/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ParametricBridgeVPFlavour
public import QED.Integration.SymanzikPositivityClasses

/-!
# A uniform lower bound for `V` of the vacuum-polarization shapes, for small regulator masses

Helper level for the relaxed order-`e⁵` vertex limit (V5Zero, part A). The bound
`QED.TwoLoop.ClassLimit.symanzikV_vpShape_ge_min` assumes that the loop masses are at least the
open-line mass `m`. Without that assumption the lower bound
`V ≥ m² (z₀ + z₁)² + M_f² (z₂ + z₃) + m_γ² (z₄ + z₅)` of
`QED.Integration.TwoLoop.le_symanzikV_classVP` still gives

`V ≥ (3/4) min(m², M_f², m_γ²)`  (`symanzikV_classVP_ge_min`),

for any loop mass `M_f`. Through repeated lines (`le_symanzikV_comp_of`) with reference masses
`(m, m₀, μ, μ)`, `μ = min(m_γ, Λ)`, the four shapes of `VP` satisfy `V ≥ vpLowerBound P m₀ > 0`
whenever `0 < m₀ ≤ m, M₁, M₂` (`symanzikV_vpShape_ge_relaxed`).
-/

@[expose] public section

namespace QED.GradedProof.V5Zero.Lim

open QED.WickModel QED.TwoLoop.Bridge
open QED.Integration.TwoLoop (castLoopMatrix symanzikU symanzikV classVPMasses classVPMomenta
  loopMatrixVP le_symanzikV_classVP three_quarters_le_of le_symanzikV_comp_of)

/-- **`V ≥ (3/4) min(m², M_f², m_γ²)` for the class `VP`**, for any loop mass `M_f`. -/
theorem symanzikV_classVP_ge_min {mass massF mγ lam₁ lam₂ : ℝ} {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2) (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU loopMatrixVP z ≠ 0) :
    3 / 4 * min (mass ^ 2) (min (massF ^ 2) (mγ ^ 2)) ≤
      symanzikV loopMatrixVP (classVPMomenta p p') (classVPMasses mass massF lam₁ lam₂) z := by
  refine le_trans ?_ (le_symanzikV_classVP hp hp' hq hlam₁ hlam₂ hz hz1 hU)
  have h1 : z 0 + z 1 + (z 2 + z 3 + z 4 + z 5) = 1 := by
    have := hz1; simp only [Fin.sum_univ_six] at this; linarith
  set c := min (mass ^ 2) (min (massF ^ 2) (mγ ^ 2))
  have hc0 : 0 ≤ c := le_min (sq_nonneg _) (le_min (sq_nonneg _) (sq_nonneg _))
  have h := three_quarters_le_of (k := mass ^ 2) (μ := c) (min_le_left _ _) le_rfl hc0 h1
    (by linarith [hz 2, hz 3, hz 4, hz 5])
  have h2 : c * (z 2 + z 3) ≤ massF ^ 2 * (z 2 + z 3) :=
    mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _))
      (by linarith [hz 2, hz 3])
  have h3 : c * (z 4 + z 5) ≤ mγ ^ 2 * (z 4 + z 5) :=
    mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _))
      (by linarith [hz 4, hz 5])
  nlinarith

/-- **`V ≥ (3/4) min(m², M_f², m_γ²)` for the four shapes of `VP`**, when every line has mass at
least that of its line of `VP` with masses `(m, M_f, m_γ, m_γ)`. -/
theorem symanzikV_vpShape_ge_min (t : Fin 4) {mass massF mγ : ℝ} {M' : Fin 10 → ℝ}
    (hM' : ∀ i, classVPMasses mass massF mγ mγ (vpShapeLines t i) ^ 2 ≤ M' i ^ 2)
    {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {z : Fin 10 → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hz1 : ∑ i, z i = 1) (hU : symanzikU (castLoopMatrix (vpShapeMatrix t)) z ≠ 0) :
    3 / 4 * min (mass ^ 2) (min (massF ^ 2) (mγ ^ 2)) ≤
      symanzikV (castLoopMatrix (vpShapeMatrix t)) (vpShapeMomenta t p p') M' z :=
  le_symanzikV_comp_of (σ := vpShapeLines t) (α := loopMatrixVP)
    (fun _ hw hw1 hU' => symanzikV_classVP_ge_min hp hp' hq le_rfl le_rfl hw hw1 hU')
    hM' hz hz1 hU

/-- The mass condition of `symanzikV_vpShape_ge_min` for the masses of the model, with loop
reference mass `m₀` and photon reference mass `μ`. -/
theorem classVPMasses_vpShapeLines_le (P : Params) {m₀ μ : ℝ} (h₀ : m₀ ^ 2 ≤ P.m ^ 2)
    (h₁ : m₀ ^ 2 ≤ P.M₁ ^ 2) (h₂ : m₀ ^ 2 ≤ P.M₂ ^ 2) (hγ : μ ^ 2 ≤ P.mγ ^ 2)
    (hΛ : μ ^ 2 ≤ P.Λ ^ 2) (t : Fin 4) (i : Fin 10) :
    classVPMasses P.m m₀ μ μ (vpShapeLines t i) ^ 2 ≤ vpShapeMasses P t i ^ 2 := by
  fin_cases t <;> fin_cases i <;>
    simp [classVPMasses, vpShapeLines, vpShapeMasses, h₀, h₁, h₂, hγ, hΛ]

/-- The uniform lower bound `(3/4) min(m², m₀², min(m_γ, Λ)²)` for `V` of the shapes of `VP`. -/
noncomputable def vpLowerBound (P : Params) (m₀ : ℝ) : ℝ :=
  3 / 4 * min (P.m ^ 2) (min (m₀ ^ 2) (min P.mγ P.Λ ^ 2))

theorem vpLowerBound_pos (P : Params) {m₀ : ℝ} (hm₀ : 0 < m₀) (hm : m₀ ≤ P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) : 0 < vpLowerBound P m₀ :=
  mul_pos (by norm_num) (lt_min (pow_pos (hm₀.trans_le hm) 2)
    (lt_min (pow_pos hm₀ 2) (pow_pos (lt_min hmγ hΛ) 2)))

/-- **Positivity of `V` for the four shapes of `VP`, for small regulator masses**: for
`0 < m₀ ≤ m, M₁, M₂` and `m_γ, Λ > 0`, `V ≥ vpLowerBound P m₀`. -/
theorem symanzikV_vpShape_ge_relaxed (P : Params) {m₀ : ℝ} (hm₀ : 0 < m₀) (hm : m₀ ≤ P.m)
    (hM₁ : m₀ ≤ P.M₁) (hM₂ : m₀ ≤ P.M₂) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (t : Fin 4)
    {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {z : Fin 10 → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hz1 : ∑ i, z i = 1) (hU : symanzikU (castLoopMatrix (vpShapeMatrix t)) z ≠ 0) :
    vpLowerBound P m₀ ≤
      symanzikV (castLoopMatrix (vpShapeMatrix t)) (vpShapeMomenta t p p') (vpShapeMasses P t)
        z := by
  have hμ0 : 0 < min P.mγ P.Λ := lt_min hmγ hΛ
  exact symanzikV_vpShape_ge_min t (classVPMasses_vpShapeLines_le P
    (pow_le_pow_left₀ hm₀.le hm 2) (pow_le_pow_left₀ hm₀.le hM₁ 2)
    (pow_le_pow_left₀ hm₀.le hM₂ 2) (pow_le_pow_left₀ hμ0.le (min_le_left _ _) 2)
    (pow_le_pow_left₀ hμ0.le (min_le_right _ _) 2) t) hp hp' hq hz hz1 hU

end QED.GradedProof.V5Zero.Lim

end
