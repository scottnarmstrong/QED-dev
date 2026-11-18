/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZeroLimitOpen

/-!
# The second-order limit for the vacuum-polarization class

Part of obligation O2-22 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4). The limit of the class `VP`
is a sum of five parametric values on ten-line data
(`QED.TwoLoop.ReflCovariance.exists_quartic_classLimitV_VP`). For each piece the numerators are,
at fixed loop momenta, polynomials of degree at most `4` in `p'` (`isLoopPoly_vpPieceNumer_out`),
the lower bound `V ≥ 3/4 min(m², min(m_γ, Λ)²)` is uniform in `q² ≥ 0`
(`QED.TwoLoop.ClassLimit.symanzikV_vpShape_ge_min`), and `V` is even along the curve; so
`QED.TwoLoop.PauliZeroLimit.tendsto_piece` applies to each piece (`tendsto_VP`).
-/

@[expose] public section

open Complex Matrix Filter Topology Set
open scoped Real

namespace QED.TwoLoop.PauliZeroLimit

open QED.Dirac QED.WickModel QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero
open QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassLimit
open QED.Integration.TwoLoop (LoopQuartic RefinedBound castLoopMatrix symanzikV symanzikU
  lineDenom)

/-! ### The piece numerators as polynomials in `p'` -/

theorem isLoopPoly_outerNum_out (P : Params) (p : Fin 4 → ℝ) (k : Fin 4 → ℝ) (μ ρ ν a b : Fin 4) :
    IsLoopPoly 1 1 fun y => outerNum P p (y 0 - p) k μ ρ ν a b := by
  have hA : IsLoopAffine fun y : Fin 1 → Fin 4 → ℝ => p + (y 0 - p) - k :=
    ⟨![1], -k, fun y => by funext σ; simp; ring⟩
  have h := ((((IsLoopPolyMat.const (L := 1) (Dirac.gamma ν)).mul
    (hA.isLoopPolyMat_electronNumerator P.m)).mul (IsLoopPolyMat.const (Dirac.gamma μ))).mul
      (IsLoopPolyMat.const (electronNumerator P.m (p - k)))).mul
        (IsLoopPolyMat.const (Dirac.gamma ρ))
  exact h a b

theorem isLoopPoly_vpE0_out (P : Params) (p : Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsLoopPoly 1 1 fun y => vpE0 P (fun _ => p) (fun _ => y 0 - p) αOut βIn μ ℓ := by
  unfold vpE0 vpNumerator vpNumer
  refine IsLoopPoly.const_mul _ (IsLoopPoly.sum _ fun l0 _ => IsLoopPoly.sum _ fun l2 _ =>
    IsLoopPoly.sum _ fun l3 _ => IsLoopPoly.sum _ fun l4 _ => ?_)
  exact (((isLoopPoly_outerNum_out P p _ _ _ _ _ _).mul (IsLoopPoly.const (n := 0) _)).mul
    (IsLoopPoly.const (n := 0) _)).mul (IsLoopPoly.const (n := 0) _)

theorem isLoopPoly_vpE2_out (P : Params) (p : Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsLoopPoly 1 1 fun y => vpE2 P (fun _ => p) (fun _ => y 0 - p) αOut βIn μ ℓ := by
  unfold vpE2 vpNumer2
  refine IsLoopPoly.const_mul _ (IsLoopPoly.sum _ fun l0 _ => IsLoopPoly.sum _ fun l2 _ =>
    IsLoopPoly.sum _ fun l3 _ => IsLoopPoly.sum _ fun l4 _ => ?_)
  exact (((isLoopPoly_outerNum_out P p _ _ _ _ _ _).mul (IsLoopPoly.const (n := 0) _)).mul
    (IsLoopPoly.const (n := 0) _)).mul (IsLoopPoly.const (n := 0) _)

theorem vpShapeMomenta_cases (t : Fin 4) (p : Fin 4 → ℝ) (i : Fin 10) :
    (∀ p', vpShapeMomenta t p p' i = p) ∨ (∀ p', vpShapeMomenta t p p' i = p') ∨
      (∀ p', vpShapeMomenta t p p' i = 0) :=
  extMomenta_cases .VP p (vpShapeLines t i)

theorem isLoopPoly_vpLineDenom_out (P : Params) (t : Fin 4) (p : Fin 4 → ℝ) (i : Fin 10)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsLoopPoly 1 2 fun y => lineDenom (castLoopMatrix (vpShapeMatrix t))
      (vpShapeMomenta t p (y 0)) (vpShapeMasses P t) 0 i ℓ := by
  have hA := isLoopAffine_lineMomentum_ext (castLoopMatrix (vpShapeMatrix t))
    (fun p' => vpShapeMomenta t p p') i ℓ (by
      rcases vpShapeMomenta_cases t p i with h | h | h
      · exact Or.inl ⟨p, h⟩
      · exact Or.inr h
      · exact Or.inl ⟨0, h⟩)
  exact hA.isLoopPoly_propDenom _ _

/-- **The `VP` piece numerators are polynomials of degree at most `4` in `p'`**, at fixed loop
momenta. -/
theorem isLoopPoly_vpPieceNumer_out (P : Params) (p : Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)
    (k : Fin 5) (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsLoopPoly 1 4 fun y => vpPieceNumer P (fun _ => y 0) (fun _ => p) (fun _ => y 0 - p)
      αOut βIn μ k ℓ := by
  have hE0 := isLoopPoly_vpE0_out P p αOut βIn μ ℓ
  have hE2 := isLoopPoly_vpE2_out P p αOut βIn μ ℓ
  have h3 : ∀ i : Fin 10, IsLoopPoly 1 4 fun y : Fin 1 → Fin 4 → ℝ => twoLoopNorm *
      -(vpBubbleCoeff P * vpE2 P (fun _ => p) (fun _ => y 0 - p) αOut βIn μ ℓ *
        lineDenom (castLoopMatrix (vpShapeMatrix 3)) (vpShapeMomenta 3 p (y 0))
          (vpShapeMasses P 3) 0 i ℓ) := fun i => by
    have h := (((hE2.const_mul (vpBubbleCoeff P)).mul
      (isLoopPoly_vpLineDenom_out P 3 p i ℓ)).const_mul (-twoLoopNorm)).mono
        (by norm_num : 1 + 2 ≤ 4)
    refine (congrArg (IsLoopPoly 1 4) (funext fun y => ?_)).mp h
    ring
  unfold vpPieceNumer
  split_ifs
  · exact h3 8
  · exact h3 3
  · exact ((((hE0.add (hE2.const_mul _)).const_mul _).const_mul _).mono (by norm_num))

/-! ### The parametric data of the pieces along the curve -/

/-- The parametric data of the `k`-th piece of `VP` along the curve. -/
noncomputable def vpCurve (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (k : Fin 5) : CurveData where
  m := 9
  α := castLoopMatrix (vpShapeMatrix (vpPieceShape k))
  mom u := vpShapeMomenta (vpPieceShape k) (restMomentum P.m) (curveMomentum P.m u)
  M := vpShapeMasses P (vpPieceShape k)
  E := vpPieceLines k
  hm := by norm_num
  hcrit := noSubdivergenceRefined_vpPiece k
  c := 3 / 4 * min (P.m ^ 2) (min P.mγ P.Λ ^ 2)
  hc := mul_pos (by norm_num) (lt_min (by positivity) (pow_pos (lt_min hmγ hΛ) 2))
  hV := fun u hu _ hz hz1 hU => symanzikV_vpShape_ge_min P hmγ hΛ
    (pow_le_pow_left₀ hm.le hM₁ 2) (pow_le_pow_left₀ hm.le hM₂ 2) _
    (dot_restMomentum (m := P.m)) (dot_curveMomentum P.m hu)
    ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu) hz hz1 hU
  hmom := fun i μ => isUPoly_ext_curve P.m
    (fun p' => vpShapeMomenta (vpPieceShape k) (restMomentum P.m) p' i)
    (vpShapeMomenta_cases (vpPieceShape k) (restMomentum P.m) i) μ
  hVeven := fun u z => by
    have h := QED.TwoLoop.ReflCovariance.isSpinLift_reflect (K := axisOne)
      (by rw [dot_axisOne]; exact one_ne_zero)
    have e := QED.TwoLoop.ReflCovariance.symanzikV_map h
      (castLoopMatrix (vpShapeMatrix (vpPieceShape k)))
      (vpShapeMomenta (vpPieceShape k) (restMomentum P.m) (curveMomentum P.m u))
      (vpShapeMasses P (vpPieceShape k)) z
    rw [← QED.TwoLoop.ReflCovariance.vpShapeMomenta_map, reflectMatrix_restMomentum,
      reflectMatrix_curveMomentum] at e
    exact e

/-! ### The limit -/

/-- **The second-order limit for `VP`.** -/
theorem tendsto_VP (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) :
    ∃ L, Tendsto (fun u : ℝ =>
      (pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
          (classLimitV .VP P (restMomentum P.m) (curveMomentum P.m u)) +
        pauliNum P.m (curveMomentum P.m (-u)) (restMomentum P.m)
          (classLimitV .VP P (restMomentum P.m) (curveMomentum P.m (-u)))) / (2 * (u : ℂ) ^ 2))
      (𝓝[≠] 0) (𝓝 L) := by
  -- the piece quartics, chosen along the curve
  have hex : ∀ u : ℝ, ∃ Q : Fin 4 → Fin 4 → Fin 4 → Fin 5 → LoopQuartic, u ∈ Ioo (-1 : ℝ) 1 →
      (∀ μ i j k, (Q μ i j k).eval =
        fun ℓ => vpPieceM P (restMomentum P.m) (curveMomentum P.m u) k μ ℓ i j) ∧
      classLimitV .VP P (restMomentum P.m) (curveMomentum P.m u) = fun μ =>
        ∑ k ∈ Finset.univ, (1 : ℂ) • Matrix.of fun i j =>
          -((π : ℂ) ^ 4) * ∫ x in QED.Integration.Feynman.simplexSet 9, paramIntegrand (Q μ i j k)
            (castLoopMatrix (vpShapeMatrix (vpPieceShape k)))
            (vpShapeMomenta (vpPieceShape k) (restMomentum P.m) (curveMomentum P.m u))
            (vpShapeMasses P (vpPieceShape k)) 0 x := fun u => by
    by_cases hu : u ∈ Ioo (-1 : ℝ) 1
    · obtain ⟨Q, hQ, -, hW⟩ := QED.TwoLoop.ReflCovariance.exists_quartic_classLimitV_VP P hm hmγ
        hΛ hM₁ hM₂ hc₁ hc₂ (dot_restMomentum (m := P.m)) (dot_curveMomentum P.m hu)
        ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu)
      exact ⟨Q, fun _ => ⟨hQ, hW⟩⟩
    · exact ⟨fun _ _ _ _ => ⟨0, 0, 0, 0, 0⟩, fun h => absurd h hu⟩
  choose Qf hQf using hex
  set v : Fin 5 → ℝ → Idx → ℂ := fun k u j => -((π : ℂ) ^ 4) *
    ∫ x in QED.Integration.Feynman.simplexSet 9, paramIntegrand (Qf u j.1 j.2.1 j.2.2 k)
      (castLoopMatrix (vpShapeMatrix (vpPieceShape k)))
      (vpShapeMomenta (vpPieceShape k) (restMomentum P.m) (curveMomentum P.m u))
      (vpShapeMasses P (vpPieceShape k)) 0 x with hv_def
  have hF : ∀ (p' : Fin 4 → ℝ) (k : Fin 5) (j : Idx),
      (fun ℓ => vpPieceM P (restMomentum P.m) p' k j.1 ℓ j.2.1 j.2.2) =
        vpPieceNumer P (fun _ => p') (fun _ => restMomentum P.m)
          (fun _ => p' - restMomentum P.m) (fun _ => j.2.1) (fun _ => j.2.2) (fun _ => j.1) k :=
    fun p' k j => funext fun ℓ => by simp only [vpPieceM, Matrix.of_apply]
  have hB : ∀ (p' : Fin 4 → ℝ) (k : Fin 5) (j : Idx),
      RefinedBound (castLoopMatrix (vpShapeMatrix (vpPieceShape k))) (vpPieceLines k) 4
        (fun ℓ => vpPieceM P (restMomentum P.m) p' k j.1 ℓ j.2.1 j.2.2) := fun p' k j => by
    rw [hF]
    exact refinedBound_vpPieceNumer P _ _ _ _ _ _ k
  have hpiece : ∀ k : Fin 5, ∃ L, Tendsto (fun u : ℝ =>
      ((∑ j : Idx, pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2 *
          v k u j) +
        ∑ j : Idx, pauliWt P.m (curveMomentum P.m (-u)) (restMomentum P.m) j.1 j.2.1 j.2.2 *
          v k (-u) j) / (2 * (u : ℂ) ^ 2)) (𝓝[≠] 0) (𝓝 L) := fun k =>
    tendsto_piece (vpCurve P hm hmγ hΛ hM₁ hM₂ k) (J := Idx) (D := 8) (n := 4) (r := 4)
      (Dω := 8)
      (fun u j ℓ => vpPieceM P (restMomentum P.m) (curveMomentum P.m u) k j.1 ℓ j.2.1 j.2.2)
      (fun j => by
        have h := isUPoly_eval_of_isLoopPoly' (ι := Fin 2 → Fin 4 → ℝ) (n := 4)
          (G := fun ℓ y => vpPieceNumer P (fun _ => y 0) (fun _ => restMomentum P.m)
            (fun _ => y 0 - restMomentum P.m) (fun _ => j.2.1) (fun _ => j.2.2) (fun _ => j.1)
            k ℓ)
          (fun ℓ => isLoopPoly_vpPieceNumer_out P _ _ _ _ k ℓ)
          (ℓ := fun _ u => fun _ => curveMomentum P.m u) fun _ ν => isUPoly_curveMomentum P.m ν
        refine h.congr fun ℓ u _ => ?_
        simp only [vpPieceM, Matrix.of_apply])
      (fun u _ j => by
        rw [hF]
        exact (isLoopPoly_vpPieceNumer P _ _ _ _ _ _ k).exists_loopQuartic)
      (fun u _ j => hB _ k j) (v k)
      (fun u hu j => ⟨Qf u j.1 j.2.1 j.2.2 k, ((hQf u hu).1 j.1 j.2.1 j.2.2 k), hB _ k j, rfl⟩)
      (fun u j => pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2)
      (fun j => isUPoly_pauliWt P.m j) (sum_pauliWt_zero P.m)
  choose L hL using hpiece
  refine ⟨∑ k, L k, (tendsto_finsetSum Finset.univ fun k _ => hL k).congr' ?_⟩
  have h1 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [h1] with u hu
  have hu' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hS : ∀ w ∈ Ioo (-1 : ℝ) 1,
      pauliNum P.m (curveMomentum P.m w) (restMomentum P.m)
        (classLimitV .VP P (restMomentum P.m) (curveMomentum P.m w)) =
      ∑ k, ∑ j : Idx, pauliWt P.m (curveMomentum P.m w) (restMomentum P.m) j.1 j.2.1 j.2.2 *
        v k w j := fun w hw => by
    rw [pauliNum_eq_sum_idx, (hQf w hw).2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.sum_apply, Matrix.of_apply, one_smul, Finset.mul_sum, hv_def]
  rw [hS u hu, hS (-u) hu', ← Finset.sum_add_distrib, Finset.sum_div]

end QED.TwoLoop.PauliZeroLimit

end
