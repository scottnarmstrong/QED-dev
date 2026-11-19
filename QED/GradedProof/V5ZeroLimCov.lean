/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZeroCovariance
public import QED.GradedProof.V5ZeroLimit
public import QED.GradedProof.V5ZeroLimCovVP

/-!
# Covariance of the order-`e⁵` vertex limit, for small regulator masses

Helper level for V5Zero, part A. This is `QED.TwoLoop.PauliZero.conj_vertexLimit_map` with the
hypothesis `M₁, M₂ ≥ m` replaced by `0 < m₀ ≤ m, M₁, M₂` for some `m₀`:

* `eq_classLimits_of_isVertexOrderFiveLimit`: the vertex limit is `1/i` times the signed sum of the
  class limits `classLimitV` plus the sum of the counterterm-class limits `ctLimitV`;
* `conj_vertexLimit_map`: `S W^μ T = L^μ_ν V^ν` for the limits `V` at `(p', p)` and `W` at
  `(L p', L p)`;
* `formFactorProj₂_vertexLimit_map`: the Pauli projector is invariant.

The open classes and the counterterm classes are reused unchanged; the class `VP` uses the relaxed
`QED.GradedProof.V5Zero.Lim.classLimitV_VP_map`.
-/

@[expose] public section

open Complex Matrix Filter Topology MeasureTheory
open scoped Real

namespace QED.GradedProof.V5Zero.Lim

open QED.Dirac QED.WickModel QED.TwoLoop QED.TwoLoop.Bridge QED.TwoLoop.Insertion
open QED.TwoLoop.CountertermLimit QED.TwoLoop.Relabel QED.TwoLoop.Enumeration
open QED.TwoLoop.LimitCovariance hiding vpData isLittleGroupCovariant_classLimitV_VP
open QED.TwoLoop.ReflCovariance hiding exists_quartic_classLimitV_VP classLimitV_VP_map
open QED.TwoLoop.PauliZero hiding eq_classLimits_of_isVertexOrderFiveLimit conj_vertexLimit_map
  formFactorProj₂_vertexLimit_map

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}

/-- **The vertex limit as the sum of the class limits**, for `0 < m₀ ≤ m, M₁, M₂`. -/
theorem eq_classLimits_of_isVertexOrderFiveLimit (P : Params) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hm : m₀ ≤ P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : m₀ ≤ P.M₁) (hM₂ : m₀ ≤ P.M₂)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p' p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0)
    (hp0' : 0 < p' 0) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hV : IsVertexOrderFiveLimit P p' p V) :
    V = fun μ => (1 / I) •
      ((∑ c ∈ Furry.nonFurry, (c.sign : ℂ) • classLimitV c P p p' μ) +
        ∑ c ∈ (Finset.univ : Finset CtClass), (1 : ℂ) • ctLimitV c P p p' μ) := by
  have hm₀' : 0 < P.m := hm₀.trans_le hm
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  funext μ
  ext i j
  have e : ∀ ε : ℝ, vertexOrderFive { P with ε := ε } p' p μ i j = (1 / I) *
      (∑ c ∈ Furry.nonFurry, (c.sign : ℂ) * contractionValue₂ { P with ε := ε } c.rep
          (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) +
        ∑ c : CtClass, contractionValue₂ { P with ε := ε } c.rep
          (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ)) :=
    fun ε => by
      rw [← onePIFunction₂_five_sub_four_eq_classes { P with ε := ε } hmom (fun _ => i)
        (fun _ => j) (fun _ => μ)]
      rfl
  have h₁ : ∀ c ∈ Furry.nonFurry, Tendsto (fun ε => (c.sign : ℂ) * contractionValue₂
      { P with ε := ε } c.rep (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i)
      (fun _ => j) (fun _ => μ)) (𝓝[>] 0) (𝓝 ((c.sign : ℂ) * classLimitV c P p p' μ i j)) :=
    fun c hc => (tendsto_nhds_limUnder (exists_tendsto_contractionValue₂_nonFurry hc
      P hm₀ hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ (pOut := fun _ => p') (pIn := fun _ => p)
      (kIn := fun _ => p' - p) hmom hp hp' hq (fun _ => i) (fun _ => j)
      (fun _ => μ))).const_mul _
  have h₂ : ∀ c ∈ (Finset.univ : Finset CtClass), Tendsto (fun ε => contractionValue₂
      { P with ε := ε } c.rep (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i)
      (fun _ => j) (fun _ => μ)) (𝓝[>] 0) (𝓝 (ctLimitV c P p p' μ i j)) :=
    fun c _ => tendsto_nhds_limUnder (CountertermLimit.exists_tendsto_contractionValue₂_ctClass c
      P hm₀' hmγ hΛ (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p) hmom hp hp'
      hp0 hp0' hq (fun _ => i) (fun _ => j) (fun _ => μ))
  have hT := ((tendsto_finsetSum _ h₁).add (tendsto_finsetSum _ h₂)).const_mul (1 / I)
  have hT' := hT.congr' (Eventually.of_forall fun ε => (e ε).symm)
  rw [tendsto_nhds_unique (hV μ i j) hT']
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sum_apply, smul_eq_mul, one_mul]

/-- **Covariance of the order-`e⁵` vertex limit under `L`, with the external momenta moved.**
For `m_γ, Λ > 0`, `0 < m₀ ≤ m, M₁, M₂` with the Pauli–Villars conditions, any counterterms,
on-shell `p, p'` with `q² ≥ 0`, `p, p', L p, L p'` of positive energy, and the limits `V` at
`(p', p)` and `W` at `(L p', L p)`: `S W^μ T = L^μ_ν V^ν`. -/
theorem conj_vertexLimit_map (P : Params) {m₀ : ℝ} (hm₀ : 0 < m₀) (hm : m₀ ≤ P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : m₀ ≤ P.M₁) (hM₂ : m₀ ≤ P.M₂)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (h : IsSpinLift L S T)
    {p' p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp0 : 0 < p 0) (hp0' : 0 < p' 0) (hLp0 : 0 < (L *ᵥ p) 0) (hLp0' : 0 < (L *ᵥ p') 0)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {V W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hV : IsVertexOrderFiveLimit P p' p V) (hW : IsVertexOrderFiveLimit P (L *ᵥ p') (L *ᵥ p) W)
    (μ : Fin 4) : S * W μ * T = vecAct L V μ := by
  have hm₀' : 0 < P.m := hm₀.trans_le hm
  have hpL : Minkowski.dot (L *ᵥ p) (L *ᵥ p) = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp
  have hpL' : Minkowski.dot (L *ᵥ p') (L *ᵥ p') = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp'
  have hqL : 0 ≤ Minkowski.dot (L *ᵥ p' - L *ᵥ p) (L *ᵥ p' - L *ᵥ p) := by
    rw [← Matrix.mulVec_sub, h.dot_mulVec]; exact hq
  rw [eq_classLimits_of_isVertexOrderFiveLimit P hm₀ hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hpL hpL' hLp0 hLp0'
    hqL hW, eq_classLimits_of_isVertexOrderFiveLimit P hm₀ hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hp hp' hp0 hp0'
    hq hV]
  dsimp only
  rw [Matrix.mul_smul, Matrix.smul_mul, vecAct_smul]
  congr 1
  rw [Matrix.mul_add, Matrix.add_mul, vecAct_add]
  congr 1
  · rw [Matrix.mul_sum, Matrix.sum_mul, VertexCovariance.vecAct_finset_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    by_cases hVP : c = .VP
    · subst hVP
      exact classLimitV_VP_map P hm₀ hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ h hp hp' hq μ
    · exact classLimitV_map (VertexLimit.mem_openClasses_of_mem_nonFurry c hc hVP) P hm₀' hmγ hΛ
        h hp hp' hq μ
  · rw [Matrix.mul_sum, Matrix.sum_mul, VertexCovariance.vecAct_finset_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    exact ctLimitV_map c P hm₀' hmγ hΛ h hp hp' hp0 hp0' hLp0 hLp0' hq μ

/-- **The Pauli projector of the vertex limit is invariant under `L`**, under the hypotheses of
`conj_vertexLimit_map`. -/
theorem formFactorProj₂_vertexLimit_map (P : Params) {m₀ : ℝ} (hm₀ : 0 < m₀) (hm : m₀ ≤ P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : m₀ ≤ P.M₁) (hM₂ : m₀ ≤ P.M₂)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (h : IsSpinLift L S T)
    {p' p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp0 : 0 < p 0) (hp0' : 0 < p' 0) (hLp0 : 0 < (L *ᵥ p) 0) (hLp0' : 0 < (L *ᵥ p') 0)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {V W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hV : IsVertexOrderFiveLimit P p' p V) (hW : IsVertexOrderFiveLimit P (L *ᵥ p') (L *ᵥ p) W)
    (e : ℝ) :
    QED.OneLoop.formFactorProj₂ e P.m (L *ᵥ p') (L *ᵥ p) W =
      QED.OneLoop.formFactorProj₂ e P.m p' p V :=
  formFactorProj₂_map h e P.m p' p fun μ =>
    conj_vertexLimit_map P hm₀ hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ h hp hp' hp0 hp0' hLp0 hLp0' hq hV hW μ

end QED.GradedProof.V5Zero.Lim

end
