/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.V5ZeroSharpOpen
public import QED.GradedProof.V5ZeroSharpCt
public import QED.GradedProof.V5ZeroSharpVP
public import QED.GradedProof.V5ZeroLimCov

/-!
# The order-`e⁵` vertex limit is `♯`-fixed

Helper level for the reality of the order-`e⁵` vertex limit (V5Zero, part D). For parameters with
`0 < m₀ ≤ m, M₁, M₂`, `m_γ, Λ > 0`, the Pauli–Villars conditions and any real counterterms, and
on-shell `p, p'` of positive energy with `q² ≥ 0`, the `ε → 0⁺` limit `V` of the order-`e⁵`
vertex satisfies `V^μ♯ = V^μ` for every `μ` (`sharp_vertexLimit`), with `♯` the antilinear
automorphism `QED.GradedProof.SE2Real.sharp` (`γ^μ♯ = γ^μ`).

The limit is `(1/i)` times a signed sum of class limits
(`QED.GradedProof.V5Zero.Lim.eq_classLimits_of_isVertexOrderFiveLimit`); every class limit `X`
satisfies `X♯ = -X` (open classes `sharp_classLimitV`, `VP` `sharp_classLimitV_VP`, counterterm
classes `sharp_ctLimitV`), and `conj (1/i) = -(1/i)`.
-/

@[expose] public section

open Complex Matrix

namespace QED.GradedProof.V5Zero.Sharp

open QED.GradedProof.SE2Real QED.TwoLoop QED.TwoLoop.LimitCovariance QED.TwoLoop.Relabel
open QED.TwoLoop.Enumeration QED.WickModel

/-- **The order-`e⁵` vertex limit is `♯`-fixed**: `V^μ♯ = V^μ`. -/
theorem sharp_vertexLimit (P : Params) {m₀ : ℝ} (hm₀ : 0 < m₀) (hm : m₀ ≤ P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : m₀ ≤ P.M₁) (hM₂ : m₀ ≤ P.M₂)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0) (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {p' p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp0 : 0 < p 0) (hp0' : 0 < p' 0) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hV : IsVertexOrderFiveLimit P p' p V) (μ : Fin 4) :
    sharp (V μ) = V μ := by
  have hm' : 0 < P.m := hm₀.trans_le hm
  rw [QED.GradedProof.V5Zero.Lim.eq_classLimits_of_isVertexOrderFiveLimit P hm₀ hm hmγ hΛ hM₁ hM₂
    hc₁ hc₂ hp hp' hp0 hp0' hq hV]
  dsimp only
  have hX : ∀ c ∈ Furry.nonFurry, sharp (classLimitV c P p p' μ) = -classLimitV c P p p' μ := by
    intro c hc
    by_cases hVP : c = .VP
    · subst hVP
      exact sharp_classLimitV_VP P hm₀ hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hp hp' hq μ
    · exact sharp_classLimitV (VertexLimit.mem_openClasses_of_mem_nonFurry c hc hVP) P hm' hmγ hΛ
        hp hp' hq μ
  have hconj : starRingEnd ℂ (1 / I) = -(1 / I) := by
    rw [map_div₀, map_one, Complex.conj_I, div_neg]
  rw [sharp_smul, hconj, sharp_add, sharp_sum, sharp_sum, neg_smul, ← smul_neg, neg_add,
    ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
  congr 2
  · refine Finset.sum_congr rfl fun c hc => ?_
    rw [sharp_smul, hX c hc, map_intCast, smul_neg, neg_neg]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [sharp_smul, sharp_ctLimitV c P hm' hmγ hΛ hp hp' hp0 hp0' hq μ, map_one, smul_neg, neg_neg]

end QED.GradedProof.V5Zero.Sharp

end
