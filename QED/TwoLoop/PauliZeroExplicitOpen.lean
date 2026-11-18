/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZeroExplicitPiece
public import QED.TwoLoop.PauliZeroLimitVP

/-!
# The explicit second-order limits of the seven classes of five gauge vertices

Part of the explicit form of the `q² → 0⁺` limit of obligation O2-22
(`docs/TWO-LOOP-DERIVATION.md`, section 5.4). Along the curve
`p'(u) = m((1+u²)/(1-u²), 2u/(1-u²), 0, 0)`, `p = (m, 0, 0, 0)`, let `S_c(u)` be the Pauli
numerator of the `ε → 0⁺` limit of the class `c`. This file identifies the limit of
`(S_c(u) + S_c(-u)) / (2u²)` as `u → 0`, `u ≠ 0`:

* **open-line classes** `c ∈ {L, X, C₊, C₋, S₊, S₋}` (`tendsto_open_explicit`):
  `openZero c P = ∫_{Δ₇} c₂[N_c(x, ·)] / V_c(x)⁴ dx`, where
  `N_c(x, u) = ∑_{(μ,i,j)} w_{μij}(u) (-π⁴) T_c^{μij}(x, u)` is the Pauli projection of the
  parametric numerator `T = T₁ + T₂ V + T₃ V²` of the Pauli–Villars form (eight lines, seven
  Feynman parameters) of the class numerator at `p'(u)` (`openNum`), `w` the Pauli weights
  (`QED.TwoLoop.PauliZeroLimit.pauliWt`), `V_c(x)` the second Symanzik function at `q = 0`
  (`openV`) and `c₂ = secondCoeff` the second-order coefficient at `u = 0`;
* **vacuum polarization** (`tendsto_VP_explicit`): the sum over the five pieces of its parametric
  representation (ten lines, nine Feynman parameters),
  `vpZero P = ∑ₖ ∫_{Δ₉} c₂[N_{VP,k}(x, ·)] / V_{VP,k}(x)⁶ dx`.

The power of `V` is `N - 4` for `N` lines: the parametric integrand at `ε = 0` is
`T / V^{N-4}` (`QED.TwoLoop.PauliZeroLimit.paramIntegrand_zero_eq`).
-/

@[expose] public section

open Complex Matrix Filter Topology Set MeasureTheory
open scoped Real

namespace QED.TwoLoop.PauliZeroExplicit

open QED.Dirac QED.WickModel QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero
open QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassLimit
open QED.TwoLoop.PauliZeroLimit
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.TwoLoop (LoopQuartic RefinedBound castLoopMatrix class5LoopMatrixPV
  class5LoopMatrix symanzikV symanzikU pvLines lineDenom)

/-! ### The open-line classes -/

/-- The numerator function of the entry `(μ, i, j)` of an open-line class at outgoing momentum
`p'`, incoming momentum `p = (m, 0, 0, 0)`. -/
noncomputable def openF (c : Class5) (P : Params) (p' : Fin 4 → ℝ) (j : Idx) :
    (Fin 2 → Fin 4 → ℝ) → ℂ :=
  fun ℓ => (twoLoopNorm • classNumM c P (restMomentum P.m) p' j.1 ℓ) j.2.1 j.2.2

/-- **The Pauli-projected parametric numerator of an open-line class along the curve**:
`N_c(x, u) = ∑_{(μ,i,j)} w_{μij}(u) (-π⁴) T_c^{μij}(x, u)`. -/
noncomputable def openNum (c : Class5) (P : Params) (x : Fin 7 → ℝ) (u : ℝ) : ℂ :=
  ∑ j : Idx, pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2 *
    (-((π : ℂ) ^ 4) * paramNumOf (openF c P (curveMomentum P.m u) j)
      (castLoopMatrix (class5LoopMatrixPV c))
      (pvMomentaE c (restMomentum P.m) (curveMomentum P.m u)) (pvMasses P) x)

/-- The second Symanzik function of the Pauli–Villars form of an open-line class at `q = 0`. -/
noncomputable def openV (c : Class5) (P : Params) (x : Fin 7 → ℝ) : ℝ :=
  symanzikV (castLoopMatrix (class5LoopMatrixPV c))
    (pvMomentaE c (restMomentum P.m) (restMomentum P.m)) (pvMasses P) (simplexPoint x)

/-- **The `q → 0` value of an open-line class**: `∫_{Δ₇} c₂[N_c(x, ·)] / V_c(x)⁴ dx`. -/
noncomputable def openZero (c : Class5) (P : Params) : ℂ :=
  ∫ x in simplexSet 7, secondCoeff (openNum c P x) / ((openV c P x : ℝ) : ℂ) ^ 4

/-- **The explicit second-order limit for an open-line class.** -/
theorem tendsto_open_explicit {c : Class5} (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses)
    (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    Tendsto (fun u : ℝ =>
      (pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
          (classLimitV c P (restMomentum P.m) (curveMomentum P.m u)) +
        pauliNum P.m (curveMomentum P.m (-u)) (restMomentum P.m)
          (classLimitV c P (restMomentum P.m) (curveMomentum P.m (-u)))) / (2 * (u : ℂ) ^ 2))
      (𝓝[≠] 0) (𝓝 (openZero c P)) := by
  have hF : ∀ (p' : Fin 4 → ℝ) (j : Idx),
      (fun ℓ => (twoLoopNorm • classNumM c P (restMomentum P.m) p' j.1 ℓ) j.2.1 j.2.2) =
        fun ℓ => twoLoopNorm * classNumeratorE c P (fun _ => p') (fun _ => restMomentum P.m)
          (fun _ => p' - restMomentum P.m) (fun _ => j.2.1) (fun _ => j.2.2) (fun _ => j.1) ℓ :=
    fun p' j => funext fun ℓ => by simp only [Matrix.smul_apply, classNumM, Matrix.of_apply,
      smul_eq_mul]
  have hB : ∀ (p' : Fin 4 → ℝ) (j : Idx), RefinedBound (castLoopMatrix (class5LoopMatrixPV c))
      {0, 1, 2, 3} 4
      (fun ℓ => (twoLoopNorm • classNumM c P (restMomentum P.m) p' j.1 ℓ) j.2.1 j.2.2) :=
    fun p' j => by
      rw [hF]
      exact (QED.TwoLoop.ClassIntegrable.refinedBound_classNumeratorE hc P _ _ _ _ _ _).const_mul _
  have hL := tendsto_piece_explicit (openCurve hc P hm hmγ hΛ) (J := Idx) (D := 8) (n := 4)
    (r := 4) (Dω := 8)
    (fun u j ℓ => (twoLoopNorm • classNumM c P (restMomentum P.m) (curveMomentum P.m u) j.1 ℓ)
      j.2.1 j.2.2)
    (fun j => by
      have h := isUPoly_eval_of_isLoopPoly' (ι := Fin 2 → Fin 4 → ℝ) (n := 4)
        (G := fun ℓ y => twoLoopNorm * classNumeratorE c P (fun _ => y 0)
          (fun _ => restMomentum P.m) (fun _ => y 0 - restMomentum P.m) (fun _ => j.2.1)
          (fun _ => j.2.2) (fun _ => j.1) ℓ)
        (fun ℓ => (isLoopPoly_classNumeratorE_out hc P _ _ _ _ ℓ).const_mul _)
        (ℓ := fun _ u => fun _ => curveMomentum P.m u) fun _ ν => isUPoly_curveMomentum P.m ν
      refine h.congr fun ℓ u _ => ?_
      simp only [Matrix.smul_apply, classNumM, Matrix.of_apply, smul_eq_mul])
    (fun u _ j => by
      rw [hF]
      exact ((QED.TwoLoop.ClassIntegrable.isLoopPoly_classNumeratorE hc P _ _ _ _ _ _).const_mul
        _).exists_loopQuartic)
    (fun u _ j => hB _ j)
    (fun u j => classLimitV c P (restMomentum P.m) (curveMomentum P.m u) j.1 j.2.1 j.2.2)
    (fun u hu j => by
      obtain ⟨Q, hQ, -, hv⟩ := QED.TwoLoop.ReflCovariance.exists_quartic_classLimitV hc P hm hmγ
        hΛ (dot_restMomentum (m := P.m)) (dot_curveMomentum P.m hu)
        ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu) j.1 j.2.1 j.2.2
      exact ⟨Q, hQ, hB _ j, hv⟩)
    (fun u j => pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2)
    (fun j => isUPoly_pauliWt P.m j) (sum_pauliWt_zero P.m)
  have hval : (∫ x in simplexSet (openCurve hc P hm hmγ hΛ).m,
      secondCoeff (projNum (openCurve hc P hm hmγ hΛ)
        (fun u (j : Idx) ℓ => (twoLoopNorm • classNumM c P (restMomentum P.m)
          (curveMomentum P.m u) j.1 ℓ) j.2.1 j.2.2)
        (fun u (j : Idx) => pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2)
        x) /
        (((openCurve hc P hm hmγ hΛ).vfun x 0 : ℝ) : ℂ) ^ ((openCurve hc P hm hmγ hΛ).m - 3)) =
      openZero c P := by
    simp only [openZero, openV, CurveData.vfun, openCurve, curveMomentum_zero]
    rfl
  rw [hval] at hL
  exact hL.congr fun u => by simp only [pauliNum_eq_sum_idx]

/-! ### Vacuum polarization -/

/-- The numerator function of the entry `(μ, i, j)` of the `k`-th piece of `VP` at outgoing
momentum `p'`, incoming momentum `p = (m, 0, 0, 0)`. -/
noncomputable def vpF (P : Params) (p' : Fin 4 → ℝ) (k : Fin 5) (j : Idx) :
    (Fin 2 → Fin 4 → ℝ) → ℂ :=
  fun ℓ => vpPieceM P (restMomentum P.m) p' k j.1 ℓ j.2.1 j.2.2

/-- **The Pauli-projected parametric numerator of the `k`-th piece of `VP` along the curve.** -/
noncomputable def vpNum (P : Params) (k : Fin 5) (x : Fin 9 → ℝ) (u : ℝ) : ℂ :=
  ∑ j : Idx, pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2 *
    (-((π : ℂ) ^ 4) * paramNumOf (vpF P (curveMomentum P.m u) k j)
      (castLoopMatrix (vpShapeMatrix (vpPieceShape k)))
      (vpShapeMomenta (vpPieceShape k) (restMomentum P.m) (curveMomentum P.m u))
      (vpShapeMasses P (vpPieceShape k)) x)

/-- The second Symanzik function of the `k`-th piece of `VP` at `q = 0`. -/
noncomputable def vpV (P : Params) (k : Fin 5) (x : Fin 9 → ℝ) : ℝ :=
  symanzikV (castLoopMatrix (vpShapeMatrix (vpPieceShape k)))
    (vpShapeMomenta (vpPieceShape k) (restMomentum P.m) (restMomentum P.m))
    (vpShapeMasses P (vpPieceShape k)) (simplexPoint x)

/-- **The `q → 0` value of `VP`**: `∑ₖ ∫_{Δ₉} c₂[N_{VP,k}(x, ·)] / V_{VP,k}(x)⁶ dx`. -/
noncomputable def vpZero (P : Params) : ℂ :=
  ∑ k : Fin 5, ∫ x in simplexSet 9, secondCoeff (vpNum P k x) / ((vpV P k x : ℝ) : ℂ) ^ 6

/-- **The explicit second-order limit for `VP`.** -/
theorem tendsto_VP_explicit (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) :
    Tendsto (fun u : ℝ =>
      (pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
          (classLimitV .VP P (restMomentum P.m) (curveMomentum P.m u)) +
        pauliNum P.m (curveMomentum P.m (-u)) (restMomentum P.m)
          (classLimitV .VP P (restMomentum P.m) (curveMomentum P.m (-u)))) / (2 * (u : ℂ) ^ 2))
      (𝓝[≠] 0) (𝓝 (vpZero P)) := by
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
  have hpiece : ∀ k : Fin 5, Tendsto (fun u : ℝ =>
      ((∑ j : Idx, pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2 *
          v k u j) +
        ∑ j : Idx, pauliWt P.m (curveMomentum P.m (-u)) (restMomentum P.m) j.1 j.2.1 j.2.2 *
          v k (-u) j) / (2 * (u : ℂ) ^ 2)) (𝓝[≠] 0)
      (𝓝 (∫ x in simplexSet 9, secondCoeff (vpNum P k x) / ((vpV P k x : ℝ) : ℂ) ^ 6)) :=
    fun k => by
    have h := tendsto_piece_explicit (vpCurve P hm hmγ hΛ hM₁ hM₂ k) (J := Idx) (D := 8) (n := 4)
      (r := 4) (Dω := 8)
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
    have hval : (∫ x in simplexSet (vpCurve P hm hmγ hΛ hM₁ hM₂ k).m,
        secondCoeff (projNum (vpCurve P hm hmγ hΛ hM₁ hM₂ k)
          (fun u (j : Idx) ℓ => vpPieceM P (restMomentum P.m) (curveMomentum P.m u) k j.1 ℓ
            j.2.1 j.2.2)
          (fun u (j : Idx) => pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1
            j.2.2) x) /
          (((vpCurve P hm hmγ hΛ hM₁ hM₂ k).vfun x 0 : ℝ) : ℂ) ^
            ((vpCurve P hm hmγ hΛ hM₁ hM₂ k).m - 3)) =
        ∫ x in simplexSet 9, secondCoeff (vpNum P k x) / ((vpV P k x : ℝ) : ℂ) ^ 6 := by
      simp only [vpV, CurveData.vfun, vpCurve, curveMomentum_zero]
      rfl
    rw [hval] at h
    exact h
  refine (tendsto_finsetSum Finset.univ fun k _ => hpiece k).congr' ?_
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

end QED.TwoLoop.PauliZeroExplicit

end
