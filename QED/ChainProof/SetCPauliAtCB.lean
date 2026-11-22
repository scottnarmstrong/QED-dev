/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCPauliAtCt
public import QED.ChainProof.SetCLimCtCB01Link
public import QED.TwoLoop.PauliZeroExplicitOpen

/-!
# Set (c): the canonical Pauli limits of the classes `CB0`, `CB1`

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`.

**A class with a limit and a covariance link.** For a class `r` of a family `V` with the limit
link `SetCClassLim` and the covariance link `SetCClassCov`, let `clsLimAt` be its `ε → 0⁺` limit
(entrywise `limUnder`). Its Pauli numerator along the curve `p'(u)`, `p = (m, 0, 0, 0)` is even
in `u` (the covariance link with the reflection `x¹ ↦ -x¹`, `clsNum_neg`), so if the even
quotient `(S(u) + S(-u))/(2u²)` converges, the class has the canonical Pauli limit
`clsPauliLim` (`setCClassPauli_of_evenQuot`, through
`QED.ChainProof.SetCUnit.tendsto_formFactorProj₂_of`).

**`CB0`, `CB1`.** The limit of `CBₖ` (`k < 2`) at a pair is `∑ⱼ vAⱼ + c ∑ⱼ vBⱼ`, `vA` the
parametric values of the pieces of the once-merged pair on the ten-line `VP` shapes (`vpData`),
`vB` those of the bare pair on the eleven-line doubled shapes (`cbData`), `c = mergeC`
(`QED.ChainProof.SetCPauli.CB01.tendsto_cbIntegrand`). Along the curve the data are `vpCurve` and
`cbCurve`, the pieces are polynomial in `p'` of degree four, and Phase 4's explicit second-order
limit (`QED.TwoLoop.PauliZeroExplicit.tendsto_piece_explicit`) applies piece by piece.

## Main statements

* `clsLimAt`, `clsPauliLim`; `clsNum_neg`; **`setCClassPauli_of_evenQuot`**;
* `cbCurve`: the doubled-shape data along the curve;
* **`tendsto_evenQuot_cb01`**: the even quotient of the Pauli numerator of the limit of `CBₖ`
  (`k < 2`) along the curve tends to `∑ⱼ Z(vpCurve j, F_A) + c ∑ⱼ Z(cbCurve d j, F_B)`, with
  `Z = pauliCurveZero` the Phase 4 Feynman-parameter value;
* **`setCClassPauli_CB01`**: the per-class Pauli limits of `CB0`, `CB1`, with the values
  `clsPauliLim ctFam P₀ (.inl k)`.
-/

@[expose] public section

open Complex Matrix Filter Topology Set MeasureTheory
open scoped Real
open QED.WickModel (Params)

namespace QED.ChainProof.SetCPauli

open QED.Dirac QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.TwoLoop.LimitCovariance (IsParamValue vpData)
open QED.ChainProof.SetAPauli (regParams regFlavors)

/-! ### A class with a limit and a covariance link -/

section Generic

variable {ι : Type} (V : ClsFam ι) (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) (D : RegCt)
  (s : ℝ × ℝ × ℝ) (r : ι)

/-- The `ε → 0⁺` limit of the class value `V · r`, entrywise. -/
noncomputable def clsLimAt (p' p : Fin 4 → ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => Matrix.of fun i j => limUnder (𝓝[>] (0 : ℝ)) fun ε =>
    V { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
      (shareCt D s) p' p μ r i j

variable {V P₀ M₁ M₂ c₁ c₂ mγ Λ D s r}

theorem clsLimAt_eq {p' p : Fin 4 → ℝ} {Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hY : IsClassLimC V P₀ M₁ M₂ c₁ c₂ mγ Λ D s r p' p Y) :
    clsLimAt V P₀ M₁ M₂ c₁ c₂ mγ Λ D s r p' p = Y := by
  funext μ
  ext i j
  exact (hY μ i j).limUnder_eq

/-- The curve pair `(p'(u), p)` is admissible for `u ≠ 0`. -/
theorem isPairQ_curve {m : ℝ} (hm : 0 < m) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) (hu0 : u ≠ 0) :
    IsPairQ m (curveMomentum m u) (restMomentum m) := by
  refine ⟨dot_curveMomentum m hu, dot_restMomentum (m := m), curveMomentum_pos hm hu,
    restMomentum_pos hm, ?_⟩
  rw [dot_curveMomentum_sub m hu]
  have h1 := one_sub_sq_pos hu
  have h2 : 0 < u ^ 2 := lt_of_le_of_ne (sq_nonneg u) (Ne.symm (pow_ne_zero 2 hu0))
  unfold curveQ
  positivity

/-- **The Pauli numerator of a covariant class limit is even along the curve.** -/
theorem clsNum_neg (hL : SetCClassLim V P₀ r) (hC : SetCClassCov V P₀ r)
    (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) (hm : 0 < P₀.m) {u : ℝ}
    (hu : u ∈ Ioo (-1 : ℝ) 1) :
    pauliNum P₀.m (curveMomentum P₀.m (-u)) (restMomentum P₀.m)
        (clsLimAt V P₀ M₁ M₂ c₁ c₂ mγ Λ D s r (curveMomentum P₀.m (-u)) (restMomentum P₀.m)) =
      pauliNum P₀.m (curveMomentum P₀.m u) (restMomentum P₀.m)
        (clsLimAt V P₀ M₁ M₂ c₁ c₂ mγ Λ D s r (curveMomentum P₀.m u) (restMomentum P₀.m)) := by
  by_cases hu0 : u = 0
  · subst hu0
    rw [neg_zero]
  have h := QED.TwoLoop.ReflCovariance.isSpinLift_reflect (K := axisOne)
    (by rw [dot_axisOne]; exact one_ne_zero)
  have hp := isPairQ_curve hm hu hu0
  have hp' := isPairQ_curve hm (neg_mem_Ioo_one hu) (neg_ne_zero.mpr hu0)
  obtain ⟨Y, hY⟩ := hL M₁ M₂ c₁ c₂ mγ Λ D s hA _ _ hp
  obtain ⟨Z, hZ⟩ := hL M₁ M₂ c₁ c₂ mγ Λ D s hA _ _ hp'
  have hZ' : IsClassLimC V P₀ M₁ M₂ c₁ c₂ mγ Λ D s r
      (reflectMatrix axisOne *ᵥ curveMomentum P₀.m u)
      (reflectMatrix axisOne *ᵥ restMomentum P₀.m) Z := by
    rw [reflectMatrix_curveMomentum, reflectMatrix_restMomentum]
    exact hZ
  have hcov := hC M₁ M₂ c₁ c₂ mγ Λ D s hA _ _ _ h _ _ hp
    (by rw [reflectMatrix_curveMomentum]; exact curveMomentum_pos hm (neg_mem_Ioo_one hu))
    (by rw [reflectMatrix_restMomentum]; exact restMomentum_pos hm) Y Z hY hZ'
  have e := pauliNum_map h P₀.m (curveMomentum P₀.m u) (restMomentum P₀.m) hcov
  rw [reflectMatrix_curveMomentum, reflectMatrix_restMomentum] at e
  rw [clsLimAt_eq hY, clsLimAt_eq hZ]
  exact e

variable (V P₀ r) in
/-- The canonical Pauli value of a class: the limit of the even quotient of its Pauli numerator
along the curve, divided by `64 e m⁵`. -/
noncomputable def clsPauliLim : ClsPauliVal := fun M₁ M₂ c₁ c₂ mγ Λ D s =>
  limUnder (𝓝[≠] (0 : ℝ)) (evenQuot fun u => pauliNum P₀.m (curveMomentum P₀.m u)
    (restMomentum P₀.m) (clsLimAt V P₀ M₁ M₂ c₁ c₂ mγ Λ D s r (curveMomentum P₀.m u)
      (restMomentum P₀.m))) / (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5)

/-- **The canonical Pauli limit of a class with a limit and a covariance link**, if the even
quotient of its Pauli numerator along the curve converges. -/
theorem setCClassPauli_of_evenQuot (hL : SetCClassLim V P₀ r) (hC : SetCClassCov V P₀ r)
    (hT : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∃ L,
      Tendsto (evenQuot fun u => pauliNum P₀.m (curveMomentum P₀.m u) (restMomentum P₀.m)
        (clsLimAt V P₀ M₁ M₂ c₁ c₂ mγ Λ D s r (curveMomentum P₀.m u) (restMomentum P₀.m)))
        (𝓝[≠] 0) (𝓝 L)) :
    SetCClassPauli V P₀ r (clsPauliLim V P₀ r) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA η hη
  have hm : 0 < P₀.m := by obtain ⟨-, -, -, -, hmγ, -, -, hm2, -⟩ := hA; linarith
  obtain ⟨L, hT⟩ := hT M₁ M₂ c₁ c₂ mγ Λ D s hA
  have h := QED.ChainProof.SetCUnit.tendsto_formFactorProj₂_of hm P₀.e
    (fun p' => clsLimAt V P₀ M₁ M₂ c₁ c₂ mγ Λ D s r p' (restMomentum P₀.m))
    (tendsto_div_of_evenQuot (fun _ hu => clsNum_neg hL hC hA hm hu) hT)
  have e : clsPauliLim V P₀ r M₁ M₂ c₁ c₂ mγ Λ D s = L / (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5) := by
    rw [clsPauliLim, hT.limUnder_eq]
  filter_upwards [Metric.tendsto_nhds.1 h η hη, self_mem_nhdsWithin] with Q hQ (hQ0 : 0 < Q)
  intro Y hY
  rw [← clsLimAt_eq hY, e, ← dist_eq_norm]
  exact hQ

end Generic

/-! ### The pieces of `CB0`, `CB1` as polynomials in `p'` -/

section CBPoly

open QED.ChainProof.SetCPauli.CB01 QED.TwoLoop.Bridge QED.TwoLoop.ClassLimit
open QED.TwoLoop.CountertermLimit (isLoopPolyMat_add isLoopPolyMat_smul isLoopPolyMat_mono)
open QED.Integration.TwoLoop (lineDenom castLoopMatrix)

theorem isLoopAffine_cbMom_out (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (i : Fin 2) :
    IsLoopAffine fun y : Fin 1 → Fin 4 → ℝ => cbMom (y 0) p ℓ i := by
  fin_cases i
  · exact ⟨![0], p + ℓ 1, fun y => by funext ν; simp [cbMom]⟩
  · exact ⟨![1], ℓ 1, fun y => by funext ν; simp [cbMom]⟩

theorem isLoopPolyMat_cbXa_out (P : Params) (d : Fin 2) (p : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) (i : Fin 2) :
    IsLoopPolyMat 1 1 fun y : Fin 1 → Fin 4 → ℝ => cbXa P d (y 0) p ℓ i := by
  have hN := (isLoopAffine_cbMom_out p ℓ i).isLoopPolyMat_electronNumerator P.m
  by_cases h : i = d
  · have e : (fun y : Fin 1 → Fin 4 → ℝ => cbXa P d (y 0) p ℓ i) =
        fun y => mergeY P.m P.δ₂ P.δm (cbMom (y 0) p ℓ i) := funext fun y => by
      simp [cbXa, h]
    rw [e]
    unfold mergeY
    exact isLoopPolyMat_add (isLoopPolyMat_smul _ hN)
      (isLoopPolyMat_mono (isLoopPolyMat_smul _ (IsLoopPolyMat.const _)) (by norm_num))
  · have e : (fun y : Fin 1 → Fin 4 → ℝ => cbXa P d (y 0) p ℓ i) =
        fun y => electronNumerator P.m (cbMom (y 0) p ℓ i) := funext fun y => by
      simp [cbXa, h]
    rw [e]
    exact hN

theorem isLoopPoly_cbNum_out (P : Params) (M : ℝ)
    {X1 X0 : (Fin 1 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ} (hX1 : IsLoopPolyMat 1 1 X1)
    (hX0 : IsLoopPolyMat 1 1 X0) (α β μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsLoopPoly 1 2 fun y => cbNum P M (X1 y) (X0 y) α β μ ℓ := by
  unfold cbNum
  refine IsLoopPoly.const_mul _ (IsLoopPoly.sum _ fun l0 _ => IsLoopPoly.sum _ fun l3 _ =>
    IsLoopPoly.sum _ fun l4 _ => IsLoopPoly.sum _ fun l5 _ => ?_)
  have hO := (((((IsLoopPolyMat.const (L := 1) (Dirac.gamma l0)).mul hX1).mul
    (IsLoopPolyMat.const (Dirac.gamma μ))).mul hX0).mul (IsLoopPolyMat.const (Dirac.gamma l3))) α β
  exact (((hO.mul (IsLoopPoly.const (n := 0) _)).mul (IsLoopPoly.const (n := 0) _)).mul
    (IsLoopPoly.const (n := 0) _)).mono (by norm_num)

theorem isLoopPoly_cbNum2_out (P : Params)
    {X1 X0 : (Fin 1 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ} (hX1 : IsLoopPolyMat 1 1 X1)
    (hX0 : IsLoopPolyMat 1 1 X0) (α β μ : Fin 4) :
    IsLoopPoly 1 2 fun y => cbNum2 P (X1 y) (X0 y) α β μ := by
  unfold cbNum2
  refine IsLoopPoly.const_mul _ (IsLoopPoly.sum _ fun l0 _ => IsLoopPoly.sum _ fun l3 _ =>
    IsLoopPoly.sum _ fun l4 _ => IsLoopPoly.sum _ fun l5 _ => ?_)
  have hO := (((((IsLoopPolyMat.const (L := 1) (Dirac.gamma l0)).mul hX1).mul
    (IsLoopPolyMat.const (Dirac.gamma μ))).mul hX0).mul (IsLoopPolyMat.const (Dirac.gamma l3))) α β
  exact (((hO.mul (IsLoopPoly.const (n := 0) _)).mul (IsLoopPoly.const (n := 0) _)).mul
    (IsLoopPoly.const (n := 0) _)).mono (by norm_num)

/-- **A piece is a polynomial of degree four in `p'`** when the pair is of degree two. -/
theorem isLoopPoly_cbPiece_out (P : Params) (p : Fin 4 → ℝ)
    {E0 E2 : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ}
    (h0 : ∀ ℓ, IsLoopPoly 1 2 fun y => E0 (y 0) ℓ) (h2 : ∀ ℓ, IsLoopPoly 1 2 fun y => E2 (y 0) ℓ)
    (j : Fin 5) (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsLoopPoly 1 4 fun y => cbPiece P p (y 0) (E0 (y 0)) (E2 (y 0)) j ℓ := by
  have h3 : ∀ i : Fin 10, IsLoopPoly 1 4 fun y : Fin 1 → Fin 4 → ℝ => twoLoopNorm *
      -(vpBubbleCoeff P * E2 (y 0) ℓ * lineDenom (castLoopMatrix (vpShapeMatrix 3))
        (vpShapeMomenta 3 p (y 0)) (vpShapeMasses P 3) 0 i ℓ) := fun i => by
    have h := ((((h2 ℓ).const_mul (vpBubbleCoeff P)).mul
      (isLoopPoly_vpLineDenom_out P 3 p i ℓ)).const_mul (-twoLoopNorm)).mono
        (by norm_num : 2 + 2 ≤ 4)
    refine (congrArg (IsLoopPoly 1 4) (funext fun y => ?_)).mp h
    ring
  unfold cbPiece
  split_ifs
  · exact h3 8
  · exact h3 3
  · exact ((((h0 ℓ).add ((h2 ℓ).const_mul _)).const_mul _).const_mul _).mono (by norm_num)

/-! ### The pieces along the curve -/

/-- The piece `j` of the once-merged pair along the curve, at the entry `(μ, α, β)`. -/
noncomputable def cbFA (P : Params) (d : Fin 2) (j : Fin 5) (u : ℝ) (x : Idx)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  cbPiece P (restMomentum P.m) (curveMomentum P.m u)
    (cbEa0 P d (curveMomentum P.m u) (restMomentum P.m) x.2.1 x.2.2 x.1)
    (cbEa2 P d (curveMomentum P.m u) (restMomentum P.m) x.2.1 x.2.2 x.1) j ℓ

/-- The piece `j` of the bare pair along the curve, at the entry `(μ, α, β)`. -/
noncomputable def cbFB (P : Params) (j : Fin 5) (u : ℝ) (x : Idx) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ℂ :=
  cbPiece P (restMomentum P.m) (curveMomentum P.m u)
    (cbEv0 P (curveMomentum P.m u) (restMomentum P.m) x.2.1 x.2.2 x.1)
    (cbEv2 P (curveMomentum P.m u) (restMomentum P.m) x.2.1 x.2.2 x.1) j ℓ

theorem isUPoly_cbFA (P : Params) (d : Fin 2) (j : Fin 5) (x : Idx) :
    IsUPoly 8 fun ℓ u => wt u ^ 4 * cbFA P d j u x ℓ :=
  isUPoly_eval_of_isLoopPoly' (ι := Fin 2 → Fin 4 → ℝ) (n := 4)
    (G := fun ℓ y => cbPiece P (restMomentum P.m) (y 0)
      (cbEa0 P d (y 0) (restMomentum P.m) x.2.1 x.2.2 x.1)
      (cbEa2 P d (y 0) (restMomentum P.m) x.2.1 x.2.2 x.1) j ℓ)
    (fun ℓ => isLoopPoly_cbPiece_out P (restMomentum P.m)
      (E0 := fun p' => cbEa0 P d p' (restMomentum P.m) x.2.1 x.2.2 x.1)
      (E2 := fun p' => cbEa2 P d p' (restMomentum P.m) x.2.1 x.2.2 x.1)
      (fun ℓ => isLoopPoly_cbNum_out P 0 (isLoopPolyMat_cbXa_out P d _ ℓ 1)
        (isLoopPolyMat_cbXa_out P d _ ℓ 0) _ _ _ ℓ)
      (fun ℓ => isLoopPoly_cbNum2_out P (isLoopPolyMat_cbXa_out P d _ ℓ 1)
        (isLoopPolyMat_cbXa_out P d _ ℓ 0) _ _ _) j ℓ)
    (ℓ := fun _ u => fun _ => curveMomentum P.m u) fun _ ν => isUPoly_curveMomentum P.m ν

theorem isUPoly_cbFB (P : Params) (j : Fin 5) (x : Idx) :
    IsUPoly 8 fun ℓ u => wt u ^ 4 * cbFB P j u x ℓ :=
  isUPoly_eval_of_isLoopPoly' (ι := Fin 2 → Fin 4 → ℝ) (n := 4)
    (G := fun ℓ y => cbPiece P (restMomentum P.m) (y 0)
      (cbEv0 P (y 0) (restMomentum P.m) x.2.1 x.2.2 x.1)
      (cbEv2 P (y 0) (restMomentum P.m) x.2.1 x.2.2 x.1) j ℓ)
    (fun ℓ => isLoopPoly_cbPiece_out P (restMomentum P.m)
      (E0 := fun p' => cbEv0 P p' (restMomentum P.m) x.2.1 x.2.2 x.1)
      (E2 := fun p' => cbEv2 P p' (restMomentum P.m) x.2.1 x.2.2 x.1)
      (fun ℓ => isLoopPoly_cbNum_out P 0
        ((isLoopAffine_cbMom_out _ ℓ 1).isLoopPolyMat_electronNumerator P.m)
        ((isLoopAffine_cbMom_out _ ℓ 0).isLoopPolyMat_electronNumerator P.m) _ _ _ ℓ)
      (fun ℓ => isLoopPoly_cbNum2_out P
        ((isLoopAffine_cbMom_out _ ℓ 1).isLoopPolyMat_electronNumerator P.m)
        ((isLoopAffine_cbMom_out _ ℓ 0).isLoopPolyMat_electronNumerator P.m) _ _ _) j ℓ)
    (ℓ := fun _ u => fun _ => curveMomentum P.m u) fun _ ν => isUPoly_curveMomentum P.m ν

/-- The parametric data of the `j`-th piece on the doubled shape `(d, sⱼ)` along the curve. -/
noncomputable def cbCurve (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (d : Fin 2) (j : Fin 5) : CurveData where
  m := 10
  α := castLoopMatrix (cbShapeMatrix d (vpPieceShape j))
  mom u := cbShapeMomenta d (vpPieceShape j) (restMomentum P.m) (curveMomentum P.m u)
  M := cbShapeMasses P (vpPieceShape j)
  E := (vpPieceLines j).map Fin.castSuccEmb
  hm := by norm_num
  hcrit := noSubdivergenceRefined_cbPiece d j
  c := 3 / 4 * min (P.m ^ 2) (min P.mγ P.Λ ^ 2)
  hc := mul_pos (by norm_num) (lt_min (by positivity) (pow_pos (lt_min hmγ hΛ) 2))
  hV := fun u hu _ hz hz1 hU => symanzikV_cbShape_ge_min P hmγ hΛ
    (pow_le_pow_left₀ hm.le hM₁ 2) (pow_le_pow_left₀ hm.le hM₂ 2) d _
    (dot_restMomentum (m := P.m)) (dot_curveMomentum P.m hu)
    ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu) hz hz1 hU
  hmom := fun i μ => isUPoly_ext_curve P.m
    (fun p' => cbShapeMomenta d (vpPieceShape j) (restMomentum P.m) p' i)
    (extMomenta_cases .VP (restMomentum P.m) (cbShapeLines d (vpPieceShape j) i)) μ
  hVeven := fun u z => by
    have h := QED.TwoLoop.ReflCovariance.isSpinLift_reflect (K := axisOne)
      (by rw [dot_axisOne]; exact one_ne_zero)
    have e := QED.TwoLoop.ReflCovariance.symanzikV_map h
      (castLoopMatrix (cbShapeMatrix d (vpPieceShape j)))
      (cbShapeMomenta d (vpPieceShape j) (restMomentum P.m) (curveMomentum P.m u))
      (cbShapeMasses P (vpPieceShape j)) z
    rw [← cbShapeMomenta_map, reflectMatrix_restMomentum, reflectMatrix_curveMomentum] at e
    exact e

end CBPoly

/-- **The Phase 4 value of a projected piece**:
`∫_Δ c₂[N(x, ·)] / V(x, 0)^{m-3} dx` with `N` the Pauli-projected parametric numerator of `F`
along the curve. -/
noncomputable def pauliCurveZero (C : CurveData) (m : ℝ)
    (F : ℝ → Idx → (Fin 2 → Fin 4 → ℝ) → ℂ) : ℂ :=
  ∫ x in QED.Integration.Feynman.simplexSet C.m, secondCoeff (projNum C F
    (fun u (j : Idx) => pauliWt m (curveMomentum m u) (restMomentum m) j.1 j.2.1 j.2.2) x) /
      ((C.vfun x 0 : ℝ) : ℂ) ^ (C.m - 3)

/-- `tendsto_piece_explicit` with the Pauli weights. -/
theorem tendsto_piece_pauli (C : CurveData) (m : ℝ) (F : ℝ → Idx → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (hFpoly : ∀ j, IsUPoly 8 fun ℓ u => wt u ^ 4 * F u j ℓ)
    (hFq : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j,
      ∃ Q : QED.Integration.TwoLoop.LoopQuartic, Q.eval = F u j)
    (hFB : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j,
      QED.Integration.TwoLoop.RefinedBound C.α C.E 4 (F u j))
    (v : ℝ → Idx → ℂ)
    (hv : ∀ u (hu : u ∈ Ioo (-1 : ℝ) 1) j, IsParamValue (C.toParamData hu) (F u j) (v u j)) :
    Tendsto (fun u =>
      ((∑ j : Idx, pauliWt m (curveMomentum m u) (restMomentum m) j.1 j.2.1 j.2.2 * v u j) +
        ∑ j : Idx, pauliWt m (curveMomentum m (-u)) (restMomentum m) j.1 j.2.1 j.2.2 *
          v (-u) j) / (2 * (u : ℂ) ^ 2)) (𝓝[≠] 0) (𝓝 (pauliCurveZero C m F)) :=
  tendsto_piece_explicit C (J := Idx) (D := 8) (n := 4) (r := 4) (Dω := 8) F hFpoly hFq hFB v hv
    (fun u j => pauliWt m (curveMomentum m u) (restMomentum m) j.1 j.2.1 j.2.2)
    (fun j => isUPoly_pauliWt m j) (sum_pauliWt_zero m)

/-! ### The classes `CB0`, `CB1` -/

section CB

open QED.ChainProof.SetCPauli.CB01

variable {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}

/-- **The even quotient of the Pauli numerator of `CB0`, `CB1` along the curve converges** to
the Phase 4 values of the pieces: `∑ⱼ Z(vpCurve j, F_A) + c ∑ⱼ Z(cbCurve d j, F_B)`. -/
theorem tendsto_evenQuot_cb01 (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) (k : Fin 5) (hk : k < 2) :
    ∃ (hm : 0 < P₀.m) (hmγ : 0 < mγ) (hΛ : 0 < Λ),
      Tendsto (evenQuot fun u => pauliNum P₀.m (curveMomentum P₀.m u) (restMomentum P₀.m)
        (clsLimAt ctFam P₀ M₁ M₂ c₁ c₂ mγ Λ D s (.inl k) (curveMomentum P₀.m u)
          (restMomentum P₀.m))) (𝓝[≠] 0)
        (𝓝 (∑ j, pauliCurveZero (vpCurve (cbParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s 0) hm hmγ hΛ
              (le_of_lt hA.1) (le_of_lt hA.2.1) j) P₀.m
            (cbFA (cbParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s 0) (if k = 0 then 1 else 0) j) +
          mergeC P₀.m (cbParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s 0).δ₂
              (cbParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s 0).δm *
            ∑ j, pauliCurveZero (cbCurve (cbParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s 0) hm hmγ hΛ
              (le_of_lt hA.1) (le_of_lt hA.2.1) (if k = 0 then 1 else 0) j) P₀.m
              (cbFB (cbParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s 0) j))) := by
  have hA' := hA
  obtain ⟨hM₁, hM₂, -, -, hmγ, hΛ, -, hm2, -, -⟩ := hA'
  have hm : 0 < P₀.m := by linarith
  refine ⟨hm, hmγ, hΛ, ?_⟩
  set Pc := cbParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s 0 with hPc
  set d : Fin 2 := if k = 0 then 1 else 0 with hd
  set c := mergeC P₀.m Pc.δ₂ Pc.δm with hc
  have h₁ : Pc.m ^ 2 ≤ Pc.M₁ ^ 2 := pow_le_pow_left₀ hm.le hM₁.le 2
  have h₂ : Pc.m ^ 2 ≤ Pc.M₂ ^ 2 := pow_le_pow_left₀ hm.le hM₂.le 2
  set w : ℝ → Idx → ℂ := fun u x =>
    pauliWt P₀.m (curveMomentum P₀.m u) (restMomentum P₀.m) x.1 x.2.1 x.2.2 with hw
  -- the representation along the curve
  have hex : ∀ u (x : Idx), ∃ vA vB : Fin 5 → ℂ, ∀ hu : u ∈ Ioo (-1 : ℝ) 1,
      (∀ j, IsParamValue ((vpCurve Pc hm hmγ hΛ hM₁.le hM₂.le j).toParamData hu)
        (cbFA Pc d j u x) (vA j)) ∧
      (∀ j, IsParamValue ((cbCurve Pc hm hmγ hΛ hM₁.le hM₂.le d j).toParamData hu)
        (cbFB Pc j u x) (vB j)) ∧
      clsLimAt ctFam P₀ M₁ M₂ c₁ c₂ mγ Λ D s (.inl k) (curveMomentum P₀.m u)
          (restMomentum P₀.m) x.1 x.2.1 x.2.2 = ∑ j, vA j + c * ∑ j, vB j := fun u x => by
    by_cases hu : u ∈ Ioo (-1 : ℝ) 1
    · obtain ⟨vA, vB, hvA, hvB, hT⟩ := tendsto_cbIntegrand Pc hmγ hΛ hm h₁ h₂
        (dot_restMomentum (m := P₀.m)) (dot_curveMomentum P₀.m hu)
        ((dot_curveMomentum_sub P₀.m hu).symm ▸ curveQ_nonneg P₀.m hu) d x.2.1 x.2.2 x.1
      refine ⟨vA, vB, fun _ => ⟨hvA, hvB, ?_⟩⟩
      have h := hT.2.neg
      rw [neg_neg] at h
      refine Tendsto.limUnder_eq (h.congr' ?_)
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      exact (ctFam_cb01_eq hA k hk _ _ x.1 x.2.1 x.2.2 ε hε).symm
    · exact ⟨0, 0, fun h => absurd h hu⟩
  choose vA vB hv using hex
  -- the pieces
  have hLA : ∀ j, Tendsto (fun u => ((∑ x : Idx, w u x * vA u x j) +
      ∑ x : Idx, w (-u) x * vA (-u) x j) / (2 * (u : ℂ) ^ 2)) (𝓝[≠] 0)
      (𝓝 (pauliCurveZero (vpCurve Pc hm hmγ hΛ hM₁.le hM₂.le j) P₀.m (cbFA Pc d j))) :=
    fun j => tendsto_piece_pauli _ P₀.m (cbFA Pc d j) (fun x => isUPoly_cbFA Pc d j x)
      (fun u _ x => (isLoopPoly_cbPiece Pc _ _ (isLoopPoly_cbEa Pc d _ _ _ _ _).1
        (isLoopPoly_cbEa Pc d _ _ _ _ _).2 j).exists_loopQuartic)
      (fun u _ x => refinedBound_cbPiece Pc _ _ (fun t => refinedBound_cbEa0 t Pc d _ _ _ _ _)
        (fun t => refinedBound_cbEa2 t Pc d _ _ _ _ _) j)
      (fun u x => vA u x j) fun u hu x => (hv u x hu).1 j
  have hLB : ∀ j, Tendsto (fun u => ((∑ x : Idx, w u x * vB u x j) +
      ∑ x : Idx, w (-u) x * vB (-u) x j) / (2 * (u : ℂ) ^ 2)) (𝓝[≠] 0)
      (𝓝 (pauliCurveZero (cbCurve Pc hm hmγ hΛ hM₁.le hM₂.le d j) P₀.m (cbFB Pc j))) :=
    fun j => tendsto_piece_pauli _ P₀.m (cbFB Pc j) (fun x => isUPoly_cbFB Pc j x)
      (fun u _ x => (isLoopPoly_cbPiece Pc _ _ (isLoopPoly_cbEv Pc _ _ _ _ _).1
        (isLoopPoly_cbEv Pc _ _ _ _ _).2 j).exists_loopQuartic)
      (fun u _ x => refinedBound_cbShape d _ (refinedBound_cbPiece Pc _ _
        (fun t => refinedBound_cbEv0 t Pc _ _ _ _ _) (fun t => refinedBound_cbEv2 t Pc _ _ _ _ _)
          j))
      (fun u x => vB u x j) fun u hu x => (hv u x hu).2.1 j
  refine ((tendsto_finsetSum Finset.univ fun j _ => hLA j).add
    ((tendsto_finsetSum Finset.univ fun j _ => hLB j).const_mul c)).congr' ?_
  have h1 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [h1] with u hu
  have hS : ∀ v ∈ Ioo (-1 : ℝ) 1,
      pauliNum P₀.m (curveMomentum P₀.m v) (restMomentum P₀.m)
        (clsLimAt ctFam P₀ M₁ M₂ c₁ c₂ mγ Λ D s (.inl k) (curveMomentum P₀.m v)
          (restMomentum P₀.m)) =
        ∑ j, ∑ x : Idx, w v x * vA v x j + c * ∑ j, ∑ x : Idx, w v x * vB v x j := by
    intro v hv'
    rw [pauliNum_eq_sum_idx]
    have e : ∀ x : Idx, w v x * clsLimAt ctFam P₀ M₁ M₂ c₁ c₂ mγ Λ D s (.inl k)
        (curveMomentum P₀.m v) (restMomentum P₀.m) x.1 x.2.1 x.2.2 =
        ∑ j, w v x * vA v x j + c * ∑ j, w v x * vB v x j := fun x => by
      rw [(hv v x hv').2.2, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_add_distrib, Finset.sum_comm,
      ← Finset.mul_sum, Finset.sum_comm (γ := Idx)]
  simp only [evenQuot]
  rw [hS u hu, hS (-u) (neg_mem_Ioo_one hu), ← Finset.sum_div, ← Finset.sum_div,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- **The canonical Pauli limits of the two classes `CB0`, `CB1`.** -/
theorem setCClassPauli_CB01 (k : Fin 5) (hk : k < 2) :
    SetCClassPauli ctFam P₀ (.inl k) (clsPauliLim ctFam P₀ (.inl k)) :=
  setCClassPauli_of_evenQuot (setCClassLim_CB01 k hk) (setCClassCov_CB01 k hk)
    fun _ _ _ _ _ _ _ _ hA => by
      obtain ⟨_, _, _, h⟩ := tendsto_evenQuot_cb01 hA k hk
      exact ⟨_, h⟩

end CB

end QED.ChainProof.SetCPauli

end
