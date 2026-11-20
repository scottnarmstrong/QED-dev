/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1DOpen
public import QED.GradedProof.V5ZeroLimVP
public import QED.TwoLoop.PauliZeroLimitVP

/-!
# (X₁) piece D: the vacuum-polarization class off the mass shell

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece D. For the class `VP` of the order-`e⁵` vertex, at external momenta
`y = (r', r)` near an on-shell pair `(p', p)` with `(p' - p)² ≥ 0`, for `0 < m₀ ≤ m, M₁, M₂` and
the two Pauli–Villars conditions, the class value converges as `ε → 0⁺`, to a limit continuous
at `(p', p)` (`offLim_contractionValue₂_VP`).

As in `QED.TwoLoop.ClassLimit.tendsto_contractionValue₂_VP`, the value at `ε > 0` is the sum of
five `ε`-independent pieces on the bubble shapes and `ε` times a sixth
(`contractionValue₂_VP_eq_pieces`, any momenta). Each piece is a parametric family in `y`
(numerators polynomial in `y`: `isLoopPoly_vpPieceNumer_ext`, `isLoopPoly_vpEpsNumer_ext`), with
`V ≥ c/2` near the shell from `QED.GradedProof.V5Zero.Lim.symanzikV_vpShape_ge_relaxed`.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Integration.TwoLoop
open QED.TwoLoop.Enumeration (Class5)
open QED.TwoLoop.Bridge (IsLoopPoly IsLoopAffine IsLoopPolyMat outerNum vpE0 vpE2 vpNumerator
  vpNumer vpNumer2 vpShapeMomenta vpShapeMasses vpShapeMatrix vpBubbleCoeff electronNumerator
  propDenom)
open QED.TwoLoop.ClassLimit (twoLoopNorm vpPieceNumer vpEpsNumer vpDenomProd vpPieceShape
  vpPieceLines jointEnergyFirstIntegral_add jointEnergyFirstIntegral_const_mul
  jointEnergyFirstIntegrable_const_mul integrand_VP_eq refinedBound_vpPieceNumer
  refinedBound_vpEpsNumer isLoopPoly_vpPieceNumer isLoopPoly_vpEpsNumer
  noSubdivergenceRefined_vpPiece)
open QED.TwoLoop.ClassIntegrable (jointEnergyFirstIntegrable_add)

namespace QED.GradedProof.X1D

/-! ### The numerators as polynomials in `(r', r)` -/

theorem isLoopAffine_y_sub (j : Fin 2) (k : Fin 4 → ℝ) :
    IsLoopAffine fun y : Fin 2 → Fin 4 → ℝ => y j - k := by
  fin_cases j
  · exact ⟨![1, 0], -k, fun y => by funext σ; simp [Fin.sum_univ_two, sub_eq_add_neg]⟩
  · exact ⟨![0, 1], -k, fun y => by funext σ; simp [Fin.sum_univ_two, sub_eq_add_neg]⟩

theorem isLoopPoly_outerNum_ext (P : Params) (k : Fin 4 → ℝ) (μ ρ ν a b : Fin 4) :
    IsLoopPoly 2 2 fun y : Fin 2 → Fin 4 → ℝ => outerNum P (y 1) (y 0 - y 1) k μ ρ ν a b := by
  have e : ∀ y : Fin 2 → Fin 4 → ℝ, y 1 + (y 0 - y 1) - k = y 0 - k := fun y => by abel
  simp only [outerNum, e]
  have h := ((((IsLoopPolyMat.const (L := 2) (Dirac.gamma ν)).mul
    ((isLoopAffine_y_sub 0 k).isLoopPolyMat_electronNumerator P.m)).mul
      (IsLoopPolyMat.const (Dirac.gamma μ))).mul
        ((isLoopAffine_y_sub 1 k).isLoopPolyMat_electronNumerator P.m)).mul
          (IsLoopPolyMat.const (Dirac.gamma ρ))
  exact h a b

theorem isLoopPoly_vpE0_ext (P : Params) (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsLoopPoly 2 2 fun y : Fin 2 → Fin 4 → ℝ =>
      vpE0 P (fun _ => y 1) (fun _ => y 0 - y 1) αOut βIn μ ℓ := by
  unfold vpE0 vpNumerator vpNumer
  refine IsLoopPoly.const_mul _ (IsLoopPoly.sum _ fun l0 _ => IsLoopPoly.sum _ fun l2 _ =>
    IsLoopPoly.sum _ fun l3 _ => IsLoopPoly.sum _ fun l4 _ => ?_)
  exact (((isLoopPoly_outerNum_ext P _ _ _ _ _ _).mul (IsLoopPoly.const (n := 0) _)).mul
    (IsLoopPoly.const (n := 0) _)).mul (IsLoopPoly.const (n := 0) _)

theorem isLoopPoly_vpE2_ext (P : Params) (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsLoopPoly 2 2 fun y : Fin 2 → Fin 4 → ℝ =>
      vpE2 P (fun _ => y 1) (fun _ => y 0 - y 1) αOut βIn μ ℓ := by
  unfold vpE2 vpNumer2
  refine IsLoopPoly.const_mul _ (IsLoopPoly.sum _ fun l0 _ => IsLoopPoly.sum _ fun l2 _ =>
    IsLoopPoly.sum _ fun l3 _ => IsLoopPoly.sum _ fun l4 _ => ?_)
  exact (((isLoopPoly_outerNum_ext P _ _ _ _ _ _).mul (IsLoopPoly.const (n := 0) _)).mul
    (IsLoopPoly.const (n := 0) _)).mul (IsLoopPoly.const (n := 0) _)

theorem vpShapeMomenta_cases₂ (t : Fin 4) (i : Fin 10) :
    (∀ p p', vpShapeMomenta t p p' i = p) ∨ (∀ p p', vpShapeMomenta t p p' i = p') ∨
      (∀ p p', vpShapeMomenta t p p' i = 0) :=
  extMomenta_cases₂ .VP _

theorem isLoopPoly_vpShapeMomenta (t : Fin 4) (i : Fin 10) (ν : Fin 4) :
    IsLoopPoly 2 1 fun y : Fin 2 → Fin 4 → ℝ => ((vpShapeMomenta t (y 1) (y 0) i ν : ℝ) : ℂ) := by
  rcases vpShapeMomenta_cases₂ t i with h | h | h <;> simp only [h]
  · exact IsLoopPoly.coord 1 ν le_rfl
  · exact IsLoopPoly.coord 0 ν le_rfl
  · simpa using IsLoopPoly.const (L := 2) (n := 1) (0 : ℂ)

theorem continuous_vpShapeMomenta (t : Fin 4) :
    Continuous fun y : Fin 2 → Fin 4 → ℝ => vpShapeMomenta t (y 1) (y 0) := by
  refine continuous_pi fun i => ?_
  rcases vpShapeMomenta_cases₂ t i with h | h | h <;> simp only [h]
  · exact continuous_apply 1
  · exact continuous_apply 0
  · exact continuous_const

theorem isLoopPoly_vpLineDenom_ext (P : Params) (t : Fin 4) (i : Fin 10)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsLoopPoly 2 2 fun y : Fin 2 → Fin 4 → ℝ => lineDenom (castLoopMatrix (vpShapeMatrix t))
      (vpShapeMomenta t (y 1) (y 0)) (vpShapeMasses P t) 0 i ℓ := by
  have hA : IsLoopAffine fun y : Fin 2 → Fin 4 → ℝ =>
      lineMomentum (castLoopMatrix (vpShapeMatrix t)) (vpShapeMomenta t (y 1) (y 0)) i ℓ := by
    rcases vpShapeMomenta_cases₂ t i with h | h | h
    · exact ⟨![0, 1], fun ν => ∑ s, castLoopMatrix (vpShapeMatrix t) i s * ℓ s ν, fun y => by
        funext ν; simp [lineMomentum, h, Fin.sum_univ_two, add_comm]⟩
    · exact ⟨![1, 0], fun ν => ∑ s, castLoopMatrix (vpShapeMatrix t) i s * ℓ s ν, fun y => by
        funext ν; simp [lineMomentum, h, Fin.sum_univ_two, add_comm]⟩
    · exact ⟨0, fun ν => ∑ s, castLoopMatrix (vpShapeMatrix t) i s * ℓ s ν, fun y => by
        funext ν; simp [lineMomentum, h]⟩
  simp only [QED.TwoLoop.Bridge.lineDenom_eq_propDenom]
  exact hA.isLoopPoly_propDenom _ _

theorem isLoopPoly_vpPieceNumer_ext (P : Params) (αOut βIn μ : Fin 1 → Fin 4) (k : Fin 5)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsLoopPoly 2 4 fun y : Fin 2 → Fin 4 → ℝ => vpPieceNumer P (fun _ => y 0) (fun _ => y 1)
      (fun _ => y 0 - y 1) αOut βIn μ k ℓ := by
  have hE0 := isLoopPoly_vpE0_ext P αOut βIn μ ℓ
  have hE2 := isLoopPoly_vpE2_ext P αOut βIn μ ℓ
  have h3 : ∀ i : Fin 10, IsLoopPoly 2 4 fun y : Fin 2 → Fin 4 → ℝ => twoLoopNorm *
      -(vpBubbleCoeff P * vpE2 P (fun _ => y 1) (fun _ => y 0 - y 1) αOut βIn μ ℓ *
        lineDenom (castLoopMatrix (vpShapeMatrix 3)) (vpShapeMomenta 3 (y 1) (y 0))
          (vpShapeMasses P 3) 0 i ℓ) := fun i => by
    have h := (((hE2.const_mul (vpBubbleCoeff P)).mul
      (isLoopPoly_vpLineDenom_ext P 3 i ℓ)).const_mul (-twoLoopNorm))
    refine (congrArg (IsLoopPoly 2 4) (funext fun y => ?_)).mp h
    ring
  unfold vpPieceNumer
  split_ifs
  · exact h3 8
  · exact h3 3
  · exact ((((hE0.add (hE2.const_mul _)).const_mul _).const_mul _).mono (by norm_num))

theorem isLoopPoly_vpEpsNumer_ext (P : Params) (αOut βIn μ : Fin 1 → Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsLoopPoly 2 2 fun y : Fin 2 → Fin 4 → ℝ =>
      vpEpsNumer P (fun _ => y 1) (fun _ => y 0 - y 1) αOut βIn μ ℓ :=
  (((isLoopPoly_vpE2_ext P αOut βIn μ ℓ).const_mul _).const_mul _).const_mul _

/-! ### The value in pieces -/

/-- **The value of `VP` at `ε > 0` in pieces**, at any momenta with momentum conservation. -/
theorem contractionValue₂_VP_eq_pieces (P : Params) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {ε : ℝ} (hε : 0 < ε)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    QED.WickModel.contractionValue₂ { P with ε := ε } Class5.VP.rep pOut pIn kIn αOut βIn μ =
      ∑ j : Fin 5, QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ =>
          vpPieceNumer P pOut pIn kIn αOut βIn μ j ℓ *
            vpDenomProd P (vpPieceShape j) (pIn 0) (pOut 0) ε ℓ) +
        (ε : ℂ) * QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ =>
          vpEpsNumer P pIn kIn αOut βIn μ ℓ * vpDenomProd P 3 (pIn 0) (pOut 0) ε ℓ) := by
  choose Q hQ using fun j =>
    (isLoopPoly_vpPieceNumer P pOut pIn kIn αOut βIn μ j).exists_loopQuartic
  obtain ⟨R, hR⟩ := (isLoopPoly_vpEpsNumer P pIn kIn αOut βIn μ).exists_loopQuartic
  have hB : ∀ j, RefinedBound (castLoopMatrix (vpShapeMatrix (vpPieceShape j))) (vpPieceLines j) 4
      (Q j).eval := fun j => by
    rw [hQ j]; exact refinedBound_vpPieceNumer P pOut pIn kIn αOut βIn μ j
  have hBR : RefinedBound (castLoopMatrix (vpShapeMatrix 3)) {0, 1, 2, 3} 4 R.eval := by
    rw [hR]; exact refinedBound_vpEpsNumer P pIn kIn αOut βIn μ
  have hI : ∀ j, QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      (Q j).eval ℓ * vpDenomProd P (vpPieceShape j) (pIn 0) (pOut 0) ε ℓ := fun j =>
    jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined
      (Q j) _ _ _ (by norm_num) hε (noSubdivergenceRefined_vpPiece j) (hB j)
  have hIR : QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      (ε : ℂ) * (R.eval ℓ * vpDenomProd P 3 (pIn 0) (pOut 0) ε ℓ) :=
    jointEnergyFirstIntegrable_const_mul _
      (jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined
        R _ _ _ (by norm_num) hε (QED.TwoLoop.ClassIntegrable.noSubdivergenceRefined_vpShape 3)
        hBR)
  simp only [Fin.sum_univ_five, ← hQ, ← hR]
  rw [← jointEnergyFirstIntegral_const_mul,
    ← jointEnergyFirstIntegral_add (hI 0) (hI 1),
    ← jointEnergyFirstIntegral_add (jointEnergyFirstIntegrable_add (hI 0) (hI 1)) (hI 2),
    ← jointEnergyFirstIntegral_add (jointEnergyFirstIntegrable_add
      (jointEnergyFirstIntegrable_add (hI 0) (hI 1)) (hI 2)) (hI 3),
    ← jointEnergyFirstIntegral_add (jointEnergyFirstIntegrable_add
      (jointEnergyFirstIntegrable_add (jointEnergyFirstIntegrable_add (hI 0) (hI 1)) (hI 2))
        (hI 3)) (hI 4),
    ← jointEnergyFirstIntegral_add (jointEnergyFirstIntegrable_add
      (jointEnergyFirstIntegrable_add (jointEnergyFirstIntegrable_add
        (jointEnergyFirstIntegrable_add (hI 0) (hI 1)) (hI 2)) (hI 3)) (hI 4)) hIR,
    (QED.TwoLoop.Bridge.parametricForm_VP { P with ε := ε } hε.ne' hc₁ hc₂ hmom αOut βIn μ).1]
  congr 1
  funext ℓ
  rw [integrand_VP_eq]
  simp only [hQ, hR, vpPieceShape]
  rfl

/-! ### The limit off the shell -/

/-- **The class `VP` off the shell.** For `0 < m₀ ≤ m, M₁, M₂`, `m_γ, Λ > 0`, the two
Pauli–Villars conditions and an on-shell pair `(p', p)` with `(p' - p)² ≥ 0`, the value of `VP` at
the external momenta `y = (r', r)` converges as `ε → 0⁺` for `y` near `(p', p)`, to a limit
continuous at `(p', p)`. -/
theorem offLim_contractionValue₂_VP (P : Params) {m₀ : ℝ} (hm₀ : 0 < m₀) (hm : m₀ ≤ P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : m₀ ≤ P.M₁) (hM₂ : m₀ ≤ P.M₂)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0) (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {p' p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (αOut βIn μ : Fin 1 → Fin 4) :
    OffLim (fun ε (y : Fin 2 → Fin 4 → ℝ) => QED.WickModel.contractionValue₂ { P with ε := ε }
      Class5.VP.rep (fun _ => y 0) (fun _ => y 1) (fun _ => y 0 - y 1) αOut βIn μ)
      (pairY p' p) := by
  set c₀ := QED.GradedProof.V5Zero.Lim.vpLowerBound P m₀
  have hc₀ : 0 < c₀ := QED.GradedProof.V5Zero.Lim.vpLowerBound_pos P hm₀ hm hmγ hΛ
  have hV : ∀ t : Fin 4, ∀ᶠ y in 𝓝 (pairY p' p), ∀ z : Fin 10 → ℝ, (∀ i, 0 ≤ z i) →
      ∑ i, z i = 1 → symanzikU (castLoopMatrix (vpShapeMatrix t)) z ≠ 0 →
      c₀ / 2 ≤ symanzikV (castLoopMatrix (vpShapeMatrix t)) (vpShapeMomenta t (y 1) (y 0))
        (vpShapeMasses P t) z := fun t =>
    eventually_symanzikV_ge (α := castLoopMatrix (vpShapeMatrix t))
      (mom := fun y : Fin 2 → Fin 4 → ℝ => vpShapeMomenta t (y 1) (y 0))
      (continuous_vpShapeMomenta t).continuousAt (vpShapeMasses P t) hc₀
      fun z hz hz1 hU => QED.GradedProof.V5Zero.Lim.symanzikV_vpShape_ge_relaxed P hm₀ hm hM₁ hM₂
        hmγ hΛ t hp hp' hq hz hz1 hU
  have hpiece : ∀ j : Fin 5, OffLim (fun ε (y : Fin 2 → Fin 4 → ℝ) =>
      QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ =>
        vpPieceNumer P (fun _ => y 0) (fun _ => y 1) (fun _ => y 0 - y 1) αOut βIn μ j ℓ *
          vpDenomProd P (vpPieceShape j) (y 1) (y 0) ε ℓ)) (pairY p' p) := fun j =>
    exists_tendsto_cont (castLoopMatrix (vpShapeMatrix (vpPieceShape j)))
      (vpShapeMasses P (vpPieceShape j)) (by norm_num : 7 ≤ 9)
      (QED.TwoLoop.ClassLimit.noSubdivergenceRefined_vpPiece j)
      (mom := fun y => vpShapeMomenta (vpPieceShape j) (y 1) (y 0))
      (fun i ν => isLoopPoly_vpShapeMomenta _ i ν)
      (N := fun y ℓ => vpPieceNumer P (fun _ => y 0) (fun _ => y 1) (fun _ => y 0 - y 1) αOut
        βIn μ j ℓ) (fun ℓ => isLoopPoly_vpPieceNumer_ext P αOut βIn μ j ℓ)
      (fun y => QED.TwoLoop.ClassLimit.isLoopPoly_vpPieceNumer P _ _ _ αOut βIn μ j)
      (fun y => QED.TwoLoop.ClassLimit.refinedBound_vpPieceNumer P _ _ _ αOut βIn μ j)
      (half_pos hc₀) (hV (vpPieceShape j))
  have heps : OffLim (fun ε (y : Fin 2 → Fin 4 → ℝ) => (ε : ℂ) *
      QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ =>
        vpEpsNumer P (fun _ => y 1) (fun _ => y 0 - y 1) αOut βIn μ ℓ *
          vpDenomProd P 3 (y 1) (y 0) ε ℓ)) (pairY p' p) := by
    have h := exists_tendsto_cont (castLoopMatrix (vpShapeMatrix 3)) (vpShapeMasses P 3)
      (by norm_num : 7 ≤ 9) (QED.TwoLoop.ClassIntegrable.noSubdivergenceRefined_vpShape 3)
      (mom := fun y => vpShapeMomenta 3 (y 1) (y 0)) (fun i ν => isLoopPoly_vpShapeMomenta _ i ν)
      (N := fun y ℓ => vpEpsNumer P (fun _ => y 1) (fun _ => y 0 - y 1) αOut βIn μ ℓ)
      (fun ℓ => isLoopPoly_vpEpsNumer_ext P αOut βIn μ ℓ)
      (fun y => QED.TwoLoop.ClassLimit.isLoopPoly_vpEpsNumer P _ _ αOut βIn μ)
      (fun y => QED.TwoLoop.ClassLimit.refinedBound_vpEpsNumer P _ _ αOut βIn μ)
      (half_pos hc₀) (hV 3)
    have hε0 : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) :=
      (Complex.continuous_ofReal.tendsto' 0 0 Complex.ofReal_zero).mono_left nhdsWithin_le_nhds
    exact OffLim.mul_left hε0 h
  refine ((OffLim.sum Finset.univ fun j _ => hpiece j).add heps).congr fun y ε hε => ?_
  rw [contractionValue₂_VP_eq_pieces P hc₁ hc₂ hε (pOut := fun _ => y 0) (pIn := fun _ => y 1)
    (kIn := fun _ => y 0 - y 1) (by simp)]

end QED.GradedProof.X1D

end
