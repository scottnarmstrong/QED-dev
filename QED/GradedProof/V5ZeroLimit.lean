/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VertexLimit
public import QED.GradedProof.V5ZeroLimVP

/-!
# The `ε → 0⁺` limit of the order-`e⁵` vertex, for small regulator masses

Helper level for V5Zero, part A. This is `QED.TwoLoop.VertexLimit.exists_isVertexOrderFiveLimit`
with the hypothesis `M₁, M₂ ≥ m` replaced by `0 < m₀ ≤ m, M₁, M₂` for some `m₀`. The open classes
and the counterterm classes did not use `M₁, M₂ ≥ m`; the class `VP` uses the relaxed
`QED.GradedProof.V5Zero.Lim.tendsto_contractionValue₂_VP`.

## Main statements

* `QED.GradedProof.V5Zero.Lim.exists_tendsto_vertexOrderFive`: each entry converges.
* `QED.GradedProof.V5Zero.Lim.exists_isVertexOrderFiveLimit`:
  `∃ V, IsVertexOrderFiveLimit P p' p V`.
* `QED.GradedProof.V5Zero.Lim.existsUnique_isVertexOrderFiveLimit`: the limit is unique.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.V5Zero.Lim

open QED.WickModel QED.TwoLoop QED.TwoLoop.Enumeration QED.TwoLoop.Relabel

/-- **Each class of five gauge vertices (Furry pair excluded) has an `ε → 0⁺` limit.** -/
theorem exists_tendsto_contractionValue₂_nonFurry {c : Class5} (hc : c ∈ Furry.nonFurry)
    (P : Params) {m₀ : ℝ} (hm₀ : 0 < m₀) (hm : m₀ ≤ P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : m₀ ≤ P.M₁) (hM₂ : m₀ ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (hp : Minkowski.dot (pIn 0) (pIn 0) = -P.m ^ 2)
    (hp' : Minkowski.dot (pOut 0) (pOut 0) = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (pOut 0 - pIn 0) (pOut 0 - pIn 0)) (αOut βIn μ : Fin 1 → Fin 4) :
    ∃ L : ℂ, Tendsto (fun ε => contractionValue₂ { P with ε := ε } c.rep pOut pIn kIn αOut βIn μ)
      (𝓝[>] 0) (𝓝 L) := by
  by_cases hVP : c = .VP
  · subst hVP
    obtain ⟨Q, -, -, h⟩ := tendsto_contractionValue₂_VP P hm₀ hm hmγ hΛ hM₁ hM₂ hc₁ hc₂
      hmom hp hp' hq αOut βIn μ
    exact ⟨_, h⟩
  · obtain ⟨Q, -, -, h⟩ := ClassLimit.tendsto_contractionValue₂_open
      (VertexLimit.mem_openClasses_of_mem_nonFurry c hc hVP) P (hm₀.trans_le hm) hmγ hΛ hmom hp hp'
      hq αOut βIn μ
    exact ⟨_, h⟩

/-- **Each entry of the order-`e⁵` vertex (HV₁) converges as `ε → 0⁺`**, for `m, m_γ, Λ > 0`,
`0 < m₀ ≤ m, M₁, M₂` with the Pauli–Villars conditions, on-shell positive-energy `p, p'` with
`(p' - p)² ≥ 0`, and every value of the counterterms. -/
theorem exists_tendsto_vertexOrderFive (P : Params) {m₀ : ℝ} (hm₀ : 0 < m₀) (hm : m₀ ≤ P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : m₀ ≤ P.M₁) (hM₂ : m₀ ≤ P.M₂)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p' p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0)
    (hp0' : 0 < p' 0) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (μ i j : Fin 4) :
    ∃ L : ℂ, Tendsto (fun ε => vertexOrderFive { P with ε := ε } p' p μ i j) (𝓝[>] 0) (𝓝 L) := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  have e : ∀ ε : ℝ, vertexOrderFive { P with ε := ε } p' p μ i j = (1 / I) *
      (∑ c ∈ Furry.nonFurry, (c.sign : ℂ) * contractionValue₂ { P with ε := ε } c.rep
          (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) +
        ∑ c : CtClass, contractionValue₂ { P with ε := ε } c.rep
          (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ)) :=
    fun ε => by
      rw [← onePIFunction₂_five_sub_four_eq_classes { P with ε := ε } hmom (fun _ => i)
        (fun _ => j) (fun _ => μ)]
      rfl
  obtain ⟨L₁, h₁⟩ := VertexLimit.exists_tendsto_finset_sum Furry.nonFurry
    (f := fun c ε => (c.sign : ℂ) * contractionValue₂ { P with ε := ε } c.rep
      (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ))
    (l := 𝓝[>] 0) fun c hc => by
      obtain ⟨L, hL⟩ := exists_tendsto_contractionValue₂_nonFurry hc P hm₀ hm hmγ hΛ hM₁ hM₂ hc₁ hc₂
        (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p) hmom hp hp' hq
        (fun _ => i) (fun _ => j) (fun _ => μ)
      exact ⟨_, hL.const_mul _⟩
  obtain ⟨L₂, h₂⟩ := VertexLimit.exists_tendsto_finset_sum (Finset.univ : Finset CtClass)
    (f := fun c ε => contractionValue₂ { P with ε := ε } c.rep
      (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ))
    (l := 𝓝[>] 0) fun c _ =>
      CountertermLimit.exists_tendsto_contractionValue₂_ctClass c P (hm₀.trans_le hm) hmγ hΛ
        (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p) hmom hp hp' hp0
        hp0' hq (fun _ => i) (fun _ => j) (fun _ => μ)
  exact ⟨_, ((h₁.add h₂).const_mul (1 / I)).congr' (Eventually.of_forall fun ε => (e ε).symm)⟩

/-- **The order-`e⁵` vertex has an `ε → 0⁺` limit** (HV₂), under the hypotheses of
`exists_tendsto_vertexOrderFive`: the first conclusion clause of (HV₃) at fixed regulators, for
every value of the counterterms. -/
theorem exists_isVertexOrderFiveLimit (P : Params) {m₀ : ℝ} (hm₀ : 0 < m₀) (hm : m₀ ≤ P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : m₀ ≤ P.M₁) (hM₂ : m₀ ≤ P.M₂)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p' p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0)
    (hp0' : 0 < p' 0) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) :
    ∃ V, IsVertexOrderFiveLimit P p' p V := by
  choose V hV using fun μ i j =>
    exists_tendsto_vertexOrderFive P hm₀ hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hp hp' hp0 hp0' hq μ i j
  exact ⟨fun μ => Matrix.of (V μ), hV⟩

/-- **The limit (HV₂) exists and is unique**, under the hypotheses of
`exists_tendsto_vertexOrderFive`. -/
theorem existsUnique_isVertexOrderFiveLimit (P : Params) {m₀ : ℝ} (hm₀ : 0 < m₀) (hm : m₀ ≤ P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : m₀ ≤ P.M₁) (hM₂ : m₀ ≤ P.M₂)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p' p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0)
    (hp0' : 0 < p' 0) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) :
    ∃! V, IsVertexOrderFiveLimit P p' p V := by
  obtain ⟨V, hV⟩ :=
    exists_isVertexOrderFiveLimit P hm₀ hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hp hp' hp0 hp0' hq
  exact ⟨V, hV, fun W hW => VertexLimit.isVertexOrderFiveLimit_unique hW hV⟩

end QED.GradedProof.V5Zero.Lim

end
