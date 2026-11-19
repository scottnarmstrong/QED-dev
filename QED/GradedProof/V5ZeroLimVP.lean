/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ClassLimitVP
public import QED.GradedProof.V5ZeroLimBound

/-!
# The `ε → 0⁺` limit of the vacuum-polarization class, for small regulator masses

Helper level for the relaxed order-`e⁵` vertex limit (V5Zero, part A). This is
`QED.TwoLoop.ClassLimit.tendsto_contractionValue₂_VP` with the hypothesis `M₁, M₂ ≥ m` replaced by
`0 < m₀ ≤ m, M₁, M₂` for some `m₀`. The proof is the same; the only change is the lower bound for
`V` of the four shapes, now `QED.GradedProof.V5Zero.Lim.symanzikV_vpShape_ge_relaxed`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.GradedProof.V5Zero.Lim

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassIntegrable
open QED.TwoLoop.ClassLimit hiding tendsto_contractionValue₂_VP
  existsUnique_tendsto_contractionValue₂_VP
open QED.Integration.TwoLoop (castLoopMatrix RefinedBound LoopQuartic symanzikU symanzikV
  jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined)
open QED.Integration.Feynman (simplexSet)

/-- **The limit for `VP`, for small regulator masses.** As
`QED.TwoLoop.ClassLimit.tendsto_contractionValue₂_VP`, with `M₁, M₂ ≥ m` replaced by
`0 < m₀ ≤ m, M₁, M₂`. -/
theorem tendsto_contractionValue₂_VP (P : Params) {m₀ : ℝ} (hm₀ : 0 < m₀) (hm : m₀ ≤ P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : m₀ ≤ P.M₁) (hM₂ : m₀ ≤ P.M₂)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0)
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
  set c₀ := vpLowerBound P m₀
  have hc₀ : 0 < c₀ := vpLowerBound_pos P hm₀ hm hmγ hΛ
  have hV : ∀ t : Fin 4, ∀ z : Fin 10 → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU (castLoopMatrix (vpShapeMatrix t)) z ≠ 0 →
      c₀ ≤ symanzikV (castLoopMatrix (vpShapeMatrix t)) (vpShapeMomenta t (pIn 0) (pOut 0))
        (vpShapeMasses P t) z :=
    fun t _ hz hz1 hU => symanzikV_vpShape_ge_relaxed P hm₀ hm hM₁ hM₂ hmγ hΛ t hp hp' hq hz hz1 hU
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
theorem existsUnique_tendsto_contractionValue₂_VP (P : Params) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hm : m₀ ≤ P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : m₀ ≤ P.M₁) (hM₂ : m₀ ≤ P.M₂)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (hp : Minkowski.dot (pIn 0) (pIn 0) = -P.m ^ 2)
    (hp' : Minkowski.dot (pOut 0) (pOut 0) = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (pOut 0 - pIn 0) (pOut 0 - pIn 0)) (αOut βIn μ : Fin 1 → Fin 4) :
    ∃! L : ℂ, Tendsto
      (fun ε => contractionValue₂ { P with ε := ε } Class5.VP.rep pOut pIn kIn αOut βIn μ)
      (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨Q, -, -, h⟩ :=
    tendsto_contractionValue₂_VP P hm₀ hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hmom hp hp' hq αOut βIn μ
  exact ⟨_, h, fun L hL => tendsto_nhds_unique hL h⟩

end QED.GradedProof.V5Zero.Lim

end
