/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.RepsIntBBJoint
public import QED.ChainProof.HCBBWick
public import QED.ChainProof.HCBBRouting
public import QED.ChainProof.RepsIntFinal

/-!
# (HC₀): integrability of the bubble–bubble representative

Helper for obligation O3-5 of `docs/HIGHER-LOOP-PLAN.md` (decision D-53).

* `chainValueIntegrable_repBB`: (T₉′) for the three-loop representative `repBB` in the frozen
  routing, from `jointEnergyFirstIntegrable_bbIntegrand` (nested routing) by the integer
  unimodular change `ℓ ↦ (ℓ₂ + ℓ₀ - p, ℓ₁ + ℓ₀ - p, p - ℓ₀)`.
* **`QED.ChainProof.repsRemaining`**: `QED.ChainProof.RepsRemaining`.
* **`QED.ChainProof.jointEnergyFirstIntegrable_vertexChain_two'`**: (HC₀) with exactly the
  frozen statement and binders of `QED.VPChain.jointEnergyFirstIntegrable_vertexChain_two`.
-/

@[expose] public section

namespace QED.ChainProof.RepsIntBB

open QED.WickModel QED.ChainProof.Enum QED.ChainProof.HCLimit QED.ChainProof.HCBB

/-- The change of loop momenta `ℓ ↦ (ℓ₂ + ℓ₀, ℓ₁ + ℓ₀, -ℓ₀)`, integer unimodular. -/
def bbMat : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 1; 1, 1, 0; -1, 0, 0]

theorem isUnit_det_bbMat : IsUnit bbMat.det := by
  rw [Matrix.det_fin_three]
  simp [bbMat]

/-- **(T₉′) for the bubble–bubble representative** at `ε > 0` under the Pauli–Villars conditions
and momentum conservation, with no mass condition. -/
theorem chainValueIntegrable_repBB (P : Params) (hε : 0 < P.ε) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    QED.ChainProof.ChainValueIntegrable P repBB pOut pIn kIn αOut βIn μ := by
  have h := jointEnergyFirstIntegrable_bbIntegrand P hε hc₁ hc₂ (pIn 0) (kIn 0) (αOut 0) (βIn 0)
    (μ 0)
  have h' := QED.TwoLoop.NestedVP.jointEnergyFirstIntegrable_comp_matrix_add 3 _ bbMat
    isUnit_det_bbMat ![-pIn 0, -pIn 0, pIn 0] h
  have e : (fun ℓ : Fin 3 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 3) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P repBB pIn kIn (lineMomentum₂ repBB pOut pIn kIn ℓ) αOut βIn μ) =
      fun ℓ => bbIntegrand P (fun k => chainOuter P (pIn 0) (kIn 0) k (αOut 0) (βIn 0) (μ 0))
        ((fun s => ∑ r, bbMat s r • ℓ r) + ![-pIn 0, -pIn 0, pIn 0]) := by
    funext ℓ
    rw [lineMomentum₂_repBB hmom, integrand_eq]
    congr 1
    funext s
    fin_cases s <;> simp [Fin.sum_univ_three, bbMat] <;> abel
  unfold QED.ChainProof.ChainValueIntegrable
  rw [loopCount_repBB, e]
  exact h'

end QED.ChainProof.RepsIntBB

namespace QED.ChainProof

open QED.WickModel QED.ChainProof.Enum

/-- **What remained of (HC₀)**: (T₉′) for the bubble–bubble representative. -/
theorem repsRemaining : RepsRemaining :=
  fun P hε hc₁ hc₂ _ _ _ hmom αOut βIn μ =>
    RepsIntBB.chainValueIntegrable_repBB P hε hc₁ hc₂ hmom αOut βIn μ

/-- **(HC₀)**, with exactly the frozen statement and binders of
`QED.VPChain.jointEnergyFirstIntegrable_vertexChain_two`. -/
theorem jointEnergyFirstIntegrable_vertexChain_two' (P : Params) (hε : 0 < P.ε)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0) (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) (hC : QED.VPChain.IsVPChain 2 C)
    {pOut pIn : Fin 1 → Fin 4 → ℝ} {kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ :=
  jointEnergyFirstIntegrable_vertexChain_two'_of_remaining repsRemaining P hε hc₁ hc₂ C hC hmom
    αOut βIn μ

end QED.ChainProof

end
