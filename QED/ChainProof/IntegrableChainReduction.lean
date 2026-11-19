/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.EnumSum
public import QED.TwoLoop.IntegrableOrderFiveTransfer

/-!
# (HC₀) reduced to the nine representatives

Helper for obligation O3-5 of `docs/HIGHER-LOOP-PLAN.md` (decision D-53): the integrability
companion (HC₀) `QED.VPChain.jointEnergyFirstIntegrable_vertexChain_two` asserts (T₉′) for the
value integrand of every set (b) chain contraction. By the enumeration (obligation O3-4,
`QED.ChainProof.Enum.exists_rep`) every such contraction is a relabelling across kind sequences
of one of the nine representatives, each one-particle irreducible, and (T₉′) passes to
relabellings of 1PI contractions under momentum conservation, at any number of loops
(`QED.TwoLoop.IntegrableOrderFive.jointEnergyFirstIntegrable_relabelK`, through an integer
unimodular change of loop momenta). So (HC₀) holds as soon as (T₉′) holds for the nine
representatives (`jointEnergyFirstIntegrable_vertexChain_two_of_reps`, whose conclusion is that of
(HC₀) verbatim).

What remains for (HC₀) is exactly `RepsIntegrable`, at `ε > 0` under the Pauli–Villars
conditions and momentum conservation:
* `repBB` (three loops; two flavour-summed bubbles);
* `repBD s`, `repDB s` (two loops; one flavour-summed bubble and one `photonCt` vertex, whose
  factor is quadratic in the photon momentum, so the numerator has degree six);
* `repDD s₀ s₁` (one loop; two `photonCt` vertices, numerator of degree six).

The parametric criteria of `QED/Integration/` do not cover them as they stand: they are stated
for two loop momenta (`Fin 2`, the `2 × 2` Symanzik matrix and the Cauchy–Binet formula for
`2 × 2` minors) and numerators of degree at most four (`LoopQuartic`).
-/

@[expose] public section

namespace QED.ChainProof

open QED.WickModel QED.TwoLoop.Relabel QED.ChainProof.Enum

/-- (T₉′) for the integrand `(2π)^{-4L} A(ℓ)` of the value (T₁₀) of `C` in the frozen routing. -/
def ChainValueIntegrable (P : Params) {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction 1 1 κ) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    Prop :=
  QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
    (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ

/-- **The remaining analytic obligation of (HC₀)**: (T₉′) for the nine representatives. -/
def RepsIntegrable (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    Prop :=
  ChainValueIntegrable P repBB pOut pIn kIn αOut βIn μ ∧
    (∀ s, ChainValueIntegrable P (repBD s) pOut pIn kIn αOut βIn μ) ∧
    (∀ s, ChainValueIntegrable P (repDB s) pOut pIn kIn αOut βIn μ) ∧
    ∀ s₀ s₁, ChainValueIntegrable P (repDD s₀ s₁) pOut pIn kIn αOut βIn μ

theorem chainValueIntegrable_of_mem {P : Params} {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    {αOut βIn μ : Fin 1 → Fin 4} (h : RepsIntegrable P pOut pIn kIn αOut βIn μ) {N : ℕ} :
    ∀ R ∈ repsOf N, ChainValueIntegrable P R.rep pOut pIn kIn αOut βIn μ := by
  obtain ⟨hBB, hBD, hDB, hDD⟩ := h
  refine repsOf_cases (fun _ R => ChainValueIntegrable P R.rep pOut pIn kIn αOut βIn μ) ?_ ?_ ?_
  · simp only [reps5, List.mem_cons, List.not_mem_nil, or_false]
    rintro R (rfl | rfl | rfl | rfl) <;> exact hDD _ _
  · simp only [reps6, List.mem_cons, List.not_mem_nil, or_false]
    rintro R (rfl | rfl | rfl | rfl)
    exacts [hBD _, hBD _, hDB _, hDB _]
  · simp only [reps7, List.mem_cons, List.not_mem_nil, or_false]
    rintro R rfl
    exact hBB

/-- **(HC₀) from the nine representatives** (obligation O3-5, the transfer half). Under the
hypotheses of (HC₀), if the value integrands of the nine representatives satisfy (T₉′)
(`RepsIntegrable`), then the value integrand of every contraction `C` with `IsVPChain 2 C`
satisfies (T₉′). The conclusion is that of (HC₀) verbatim. The hypotheses `hε`, `hc₁`, `hc₂` are
not used by the transfer; they are those under which `RepsIntegrable` is to be proved. -/
theorem jointEnergyFirstIntegrable_vertexChain_two_of_reps (P : Params) (_hε : 0 < P.ε)
    (_hc₁ : 1 + P.c₁ + P.c₂ = 0) (_hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
    (hC : QED.VPChain.IsVPChain 2 C)
    {pOut pIn : Fin 1 → Fin 4 → ℝ} {kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) (hreps : RepsIntegrable P pOut pIn kIn αOut βIn μ) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ := by
  obtain ⟨R, hR, π, hκ, rfl⟩ := exists_rep hC
  exact QED.TwoLoop.IntegrableOrderFive.jointEnergyFirstIntegrable_relabelK P π hκ
    (repsOf_props R hR).1 (by simp only [Fin.sum_univ_one, hmom]) αOut βIn μ
    (chainValueIntegrable_of_mem hreps R hR)

end QED.ChainProof

end
