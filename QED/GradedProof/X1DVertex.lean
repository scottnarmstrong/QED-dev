/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1DVP
public import QED.GradedProof.X1DCt
public import QED.GradedProof.V5ZeroLimit

/-!
# (X₁) piece D: the order-`e⁵` vertex (HV₁) off the mass shell

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece D, at the level of the two-loop model `QED.TwoLoop.vertexOrderFive`.
For `0 < m₀ ≤ m, M₁, M₂`, `m_γ, Λ > 0`, the two Pauli–Villars conditions and an on-shell
positive-energy pair `(p', p)` with `(p' - p)² ≥ 0`, the vertex at off-shell external momenta
`x = (r', r)` near `(p', p)` converges as `ε → 0⁺`, and the limit is continuous at `(p', p)`
(`exists_vertexOrderFive_offShell`).

The vertex is `(1/i)` times the signed sum of the seven non-Furry classes plus the seven
counterterm classes (`QED.TwoLoop.Relabel.onePIFunction₂_five_sub_four_eq_classes`, any
momenta); each class is an `OffLim` (`X1DOpen`, `X1DVP`, `X1DCt`).
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel QED.TwoLoop QED.TwoLoop.Enumeration QED.TwoLoop.Relabel

namespace QED.GradedProof.X1D

/-- **Matrix packaging of entrywise `OffLim`.** -/
theorem exists_matrix_of_offLim {Y : Type*} [TopologicalSpace Y] {y₀ : Y}
    {A : ℝ → Y → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (h : ∀ μ i j, OffLim (fun ε y => A ε y μ i j) y₀) :
    ∃ V : Y → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ,
      (∀ᶠ y in 𝓝 y₀, ∀ μ, Tendsto (fun ε => A ε y μ) (𝓝[>] 0) (𝓝 (V y μ))) ∧
        ContinuousAt V y₀ := by
  choose G hG hGc using h
  refine ⟨fun y μ => Matrix.of fun i j => G μ i j y, ?_, ?_⟩
  · filter_upwards [eventually_all.2 fun μ => eventually_all.2 fun i =>
      eventually_all.2 fun j => hG μ i j] with y hy μ
    exact tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hy μ i j
  · exact continuousAt_pi.2 fun μ => continuousAt_pi.2 fun i => continuousAt_pi.2 fun j =>
      hGc μ i j

section Vertex

variable (P : Params) {m₀ : ℝ} (hm₀ : 0 < m₀) (hm : m₀ ≤ P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
  (hM₁ : m₀ ≤ P.M₁) (hM₂ : m₀ ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
  (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p' p : Fin 4 → ℝ}
  (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0)
  (hp0' : 0 < p' 0) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
include hm₀ hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hp hp' hp0 hp0' hq

omit hp0 hp0' in
/-- **Each non-Furry class off the shell.** -/
theorem offLim_contractionValue₂_nonFurry {c : Class5} (hc : c ∈ Furry.nonFurry)
    (αOut βIn μ : Fin 1 → Fin 4) :
    OffLim (fun ε (y : Fin 2 → Fin 4 → ℝ) => contractionValue₂ { P with ε := ε } c.rep
      (fun _ => y 0) (fun _ => y 1) (fun _ => y 0 - y 1) αOut βIn μ) (pairY p' p) := by
  by_cases hVP : c = .VP
  · subst hVP
    exact offLim_contractionValue₂_VP P hm₀ hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hp hp' hq αOut βIn μ
  · exact offLim_contractionValue₂_open (VertexLimit.mem_openClasses_of_mem_nonFurry c hc hVP)
      P (hm₀.trans_le hm) hmγ hΛ hp hp' hq αOut βIn μ

/-- **Each entry of the vertex (HV₁) off the shell**, in `y = (r', r)`. -/
theorem offLim_vertexOrderFive (μ i j : Fin 4) :
    OffLim (fun ε (y : Fin 2 → Fin 4 → ℝ) => vertexOrderFive { P with ε := ε } (y 0) (y 1) μ i j)
      (pairY p' p) := by
  have h₁ := OffLim.sum Furry.nonFurry fun c hc =>
    (offLim_contractionValue₂_nonFurry P hm₀ hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hp hp' hq hc
      (fun _ => i) (fun _ => j) (fun _ => μ)).const_mul (c.sign : ℂ)
  have h₂ := OffLim.sum (Finset.univ : Finset CtClass) fun c _ =>
    offLim_contractionValue₂_ctClass c P (hm₀.trans_le hm) hmγ hΛ hp hp' hp0
      hp0' hq (fun _ => i) (fun _ => j) (fun _ => μ)
  refine ((h₁.add h₂).const_mul (1 / I)).congr fun y ε _ => ?_
  have hmom : (fun _ : Fin 1 => y 0) 0 = (fun _ : Fin 1 => y 1) 0 +
      (fun _ : Fin 1 => y 0 - y 1) 0 := by simp
  rw [← onePIFunction₂_five_sub_four_eq_classes { P with ε := ε } hmom (fun _ => i)
    (fun _ => j) (fun _ => μ)]
  rfl

/-- **(X₁) piece D, two-loop model: the order-`e⁵` vertex off the shell.** There is
`V : (r', r) ↦ (μ ↦ matrix)` such that, for `(r', r)` near `(p', p)`, the vertex (HV₁) at
`(r', r)` converges to `V (r', r)` as `ε → 0⁺`, and `V` is continuous at `(p', p)`. -/
theorem exists_vertexOrderFive_offShell :
    ∃ V : (Fin 4 → ℝ) × (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ,
      (∀ᶠ x in 𝓝 (p', p), ∀ μ, Tendsto (fun ε => vertexOrderFive { P with ε := ε } x.1 x.2 μ)
        (𝓝[>] 0) (𝓝 (V x μ))) ∧ ContinuousAt V (p', p) := by
  have hf : ContinuousAt (fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) => (![x.1, x.2] : Fin 2 → Fin 4 → ℝ))
      (p', p) := by
    refine continuous_pi (fun s => ?_) |>.continuousAt
    fin_cases s
    · exact continuous_fst
    · exact continuous_snd
  have key : ∀ μ i j, OffLim (fun ε (x : (Fin 4 → ℝ) × (Fin 4 → ℝ)) =>
      vertexOrderFive { P with ε := ε } x.1 x.2 μ i j) (p', p) := fun μ i j => by
    have h := OffLim.comp
      (F := fun ε (y : Fin 2 → Fin 4 → ℝ) => vertexOrderFive { P with ε := ε } (y 0) (y 1) μ i j)
      (f := fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) => (![x.1, x.2] : Fin 2 → Fin 4 → ℝ))
      (z₀ := (p', p))
      (offLim_vertexOrderFive P hm₀ hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hp hp' hp0 hp0' hq μ i j) hf
    exact h.congr fun x ε _ => by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact exists_matrix_of_offLim key

end Vertex

end QED.GradedProof.X1D

end
