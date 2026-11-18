/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.CountertermLimit
public import QED.TwoLoop.ClassLimitVP
public import QED.Frozen.TwoLoop.IsVertexOrderFiveLimit

/-!
# The `ε → 0⁺` limit of the order-`e⁵` vertex exists and is unique

The first conclusion clause of the headline (HV₃) of packet T3 (decision D-41), at fixed
regulators: for `m, m_γ, Λ > 0`, regulator fermions `M₁, M₂ ≥ m` with the two Pauli–Villars
conditions, on-shell positive-energy `p, p'` with `q² = (p' - p)² ≥ 0`, and every value of the
counterterms `δ₁, δ₂, δ_m, δ₃`, the order-`e⁵` vertex (HV₁) `QED.TwoLoop.vertexOrderFive` has an
`ε → 0⁺` limit in the sense of (HV₂) `QED.TwoLoop.IsVertexOrderFiveLimit`, and the limit is
unique.

## Proof

Momentum conservation `p' = p + (p' - p)` holds, so by
`QED.TwoLoop.Relabel.onePIFunction₂_five_sub_four_eq_classes` every entry of (HV₁) is `1/i`
times the signed sum of the values of the seven classes of five gauge vertices `L, X, C±, S±, VP`
plus the sum of the values of the seven counterterm classes. Each term has a limit:

* `L, X, C±, S±`: `QED.TwoLoop.ClassLimit.tendsto_contractionValue₂_open`;
* `VP`: `QED.TwoLoop.ClassLimit.tendsto_contractionValue₂_VP` (this uses `M₁, M₂ ≥ m` and the
  Pauli–Villars conditions);
* the counterterm classes: `QED.TwoLoop.CountertermLimit.exists_tendsto_contractionValue₂_ctClass`
  (the `δ₁` classes use the positive energies).

Uniqueness holds because `𝓝[>] 0` is a nontrivial filter on `ℝ`.

## Main statements

* `QED.TwoLoop.VertexLimit.exists_tendsto_vertexOrderFive`: each entry converges.
* `QED.TwoLoop.VertexLimit.exists_isVertexOrderFiveLimit`: `∃ V, IsVertexOrderFiveLimit P p' p V`.
* `QED.TwoLoop.VertexLimit.isVertexOrderFiveLimit_unique`,
  `QED.TwoLoop.VertexLimit.existsUnique_isVertexOrderFiveLimit`: the limit is unique.
* `QED.TwoLoop.VertexLimit.exists_isVertexOrderFiveLimit_headline`: the existence clause in the
  shape of (HV₃).
-/

@[expose] public section

open Complex Filter Topology

namespace QED.TwoLoop.VertexLimit

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Relabel

/-- A finite sum of functions with limits has a limit. -/
theorem exists_tendsto_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ} {l : Filter ℝ}
    (h : ∀ i ∈ s, ∃ L, Tendsto (f i) l (𝓝 L)) :
    ∃ L, Tendsto (fun x => ∑ i ∈ s, f i x) l (𝓝 L) := by
  classical
  choose! a ha using h
  exact ⟨_, tendsto_finsetSum s ha⟩

theorem mem_openClasses_of_mem_nonFurry :
    ∀ c : Class5, c ∈ Furry.nonFurry → c ≠ .VP → c ∈ ClassIntegrable.openClasses := by
  decide

/-- **Each class of five gauge vertices (Furry pair excluded) has an `ε → 0⁺` limit.** -/
theorem exists_tendsto_contractionValue₂_nonFurry {c : Class5} (hc : c ∈ Furry.nonFurry)
    (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁)
    (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (hp : Minkowski.dot (pIn 0) (pIn 0) = -P.m ^ 2)
    (hp' : Minkowski.dot (pOut 0) (pOut 0) = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (pOut 0 - pIn 0) (pOut 0 - pIn 0)) (αOut βIn μ : Fin 1 → Fin 4) :
    ∃ L : ℂ, Tendsto (fun ε => contractionValue₂ { P with ε := ε } c.rep pOut pIn kIn αOut βIn μ)
      (𝓝[>] 0) (𝓝 L) := by
  by_cases hVP : c = .VP
  · subst hVP
    obtain ⟨Q, -, -, h⟩ := ClassLimit.tendsto_contractionValue₂_VP P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂
      hmom hp hp' hq αOut βIn μ
    exact ⟨_, h⟩
  · obtain ⟨Q, -, -, h⟩ := ClassLimit.tendsto_contractionValue₂_open
      (mem_openClasses_of_mem_nonFurry c hc hVP) P hm hmγ hΛ hmom hp hp' hq αOut βIn μ
    exact ⟨_, h⟩

/-- **Each entry of the order-`e⁵` vertex (HV₁) converges as `ε → 0⁺`**, for `m, m_γ, Λ > 0`,
`M₁, M₂ ≥ m` with the Pauli–Villars conditions, on-shell positive-energy `p, p'` with
`(p' - p)² ≥ 0`, and every value of the counterterms. -/
theorem exists_tendsto_vertexOrderFive (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
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
  obtain ⟨L₁, h₁⟩ := exists_tendsto_finset_sum Furry.nonFurry
    (f := fun c ε => (c.sign : ℂ) * contractionValue₂ { P with ε := ε } c.rep
      (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ))
    (l := 𝓝[>] 0) fun c hc => by
      obtain ⟨L, hL⟩ := exists_tendsto_contractionValue₂_nonFurry hc P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂
        (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p) hmom hp hp' hq
        (fun _ => i) (fun _ => j) (fun _ => μ)
      exact ⟨_, hL.const_mul _⟩
  obtain ⟨L₂, h₂⟩ := exists_tendsto_finset_sum (Finset.univ : Finset CtClass)
    (f := fun c ε => contractionValue₂ { P with ε := ε } c.rep
      (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ))
    (l := 𝓝[>] 0) fun c _ =>
      CountertermLimit.exists_tendsto_contractionValue₂_ctClass c P hm hmγ hΛ
        (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p) hmom hp hp' hp0
        hp0' hq (fun _ => i) (fun _ => j) (fun _ => μ)
  exact ⟨_, ((h₁.add h₂).const_mul (1 / I)).congr' (Eventually.of_forall fun ε => (e ε).symm)⟩

/-- **The order-`e⁵` vertex has an `ε → 0⁺` limit** (HV₂), under the hypotheses of
`exists_tendsto_vertexOrderFive`: the first conclusion clause of (HV₃) at fixed regulators, for
every value of the counterterms. -/
theorem exists_isVertexOrderFiveLimit (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p' p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0)
    (hp0' : 0 < p' 0) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) :
    ∃ V, IsVertexOrderFiveLimit P p' p V := by
  choose V hV using fun μ i j =>
    exists_tendsto_vertexOrderFive P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hp hp' hp0 hp0' hq μ i j
  exact ⟨fun μ => Matrix.of (V μ), hV⟩

/-- **The limit (HV₂) is unique**, for all parameters and momenta. -/
theorem isVertexOrderFiveLimit_unique {P : Params} {p' p : Fin 4 → ℝ}
    {V W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hV : IsVertexOrderFiveLimit P p' p V)
    (hW : IsVertexOrderFiveLimit P p' p W) : V = W :=
  funext fun μ => Matrix.ext fun i j => tendsto_nhds_unique (hV μ i j) (hW μ i j)

/-- **The limit (HV₂) exists and is unique**, under the hypotheses of
`exists_tendsto_vertexOrderFive`. -/
theorem existsUnique_isVertexOrderFiveLimit (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p' p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0)
    (hp0' : 0 < p' 0) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) :
    ∃! V, IsVertexOrderFiveLimit P p' p V := by
  obtain ⟨V, hV⟩ :=
    exists_isVertexOrderFiveLimit P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hp hp' hp0 hp0' hq
  exact ⟨V, hV, fun W hW => isVertexOrderFiveLimit_unique hW hV⟩

/-- **The existence clause of (HV₃), in its shape**: for the parameters
`{P₀ with M₁, M₂, c₁, c₂, m_γ, Λ, δ₁ := d₁, δ₂ := d₂, δ_m := dm, δ₃ := d₃}` of the headline, with
`M₁, M₂ > m`, the Pauli–Villars conditions, `m_γ, Λ > 0`, any counterterms, and an on-shell
positive-energy pair with `q² > 0`, the order-`e⁵` vertex has an `ε → 0⁺` limit. No smallness of
`m_γ`, `q²` or `1/Λ` and no condition on the counterterms is needed. -/
theorem exists_isVertexOrderFiveLimit_headline (P₀ : Params) (hm : 0 < P₀.m)
    (M₁ M₂ c₁ c₂ : ℝ) (hM₁ : P₀.m < M₁) (hM₂ : P₀.m < M₂) (hPV₁ : 1 + c₁ + c₂ = 0)
    (hPV₂ : P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (d₁ d₂ dm d₃ : ℝ) (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P₀.m ^ 2)
    (hp : Minkowski.dot p p = -P₀.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) :
    ∃ V, IsVertexOrderFiveLimit
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
        δm := dm, δ₃ := d₃ } p' p V :=
  exists_isVertexOrderFiveLimit
    { P₀ with
      M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
      δm := dm, δ₃ := d₃ } hm hmγ hΛ hM₁.le hM₂.le hPV₁ hPV₂ hp hp' hp0 hp0' hq.le

end QED.TwoLoop.VertexLimit

end
