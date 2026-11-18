/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.LimitCovarianceQuartic
public import QED.TwoLoop.LimitCovarianceOpen
public import QED.TwoLoop.VertexCovariance
public import QED.TwoLoop.ClassLimit
import Mathlib.Tactic.Ring

/-!
# Covariance of the `ε → 0⁺` limits of the open-line classes

Part of obligation O2-20 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4).

* `isLittleGroupCovariant_of_paramValue`: if every entry `W^μ_{ij}` is the parametric value
  (`IsParamValue`) of the numerator entry `N^μ_{ij}` for fixed parametric data whose external
  line momenta are fixed by the Lorentz maps fixing `p, p'`, and the numerator matrices are
  covariant (`S N^μ(L ℓ) T = L^μ_ν N^ν(ℓ)`), then `W` is little-group covariant. The proof
  combines the linearity of parametric values (`IsParamValue.sum`) with their invariance under
  `ℓ ↦ L ℓ` (`IsParamValue.eq_of_loopAct`).
* `classLimitV c P p p'`: the vertex of `ε → 0⁺` limits of class `c`, and
  `isLittleGroupCovariant_classLimitV`: for the six open-line classes it is little-group
  covariant.
-/

@[expose] public section

open Complex Matrix Filter Topology
open scoped Real

namespace QED.TwoLoop.LimitCovariance

open QED.Dirac QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge
open QED.Integration.TwoLoop (LoopQuartic RefinedBound castLoopMatrix class5LoopMatrixPV)

/-! ### Covariance from parametric values -/

/-- **Covariance of a vertex of parametric values.** -/
theorem isLittleGroupCovariant_of_paramValue {p' p : Fin 4 → ℝ} (D : ParamData)
    (hD : ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ), IsSpinLift L S T →
      L *ᵥ p = p → L *ᵥ p' = p' → ∀ i, L *ᵥ D.p i = D.p i)
    (N : Fin 4 → (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (hN : ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ), IsSpinLift L S T →
      L *ᵥ p = p → L *ᵥ p' = p' → ∀ μ ℓ,
        S * N μ (loopAct L ℓ) * T = vecAct L (fun ν => N ν ℓ) μ)
    (W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hW : ∀ μ i j, IsParamValue D (fun ℓ => N μ ℓ i j) (W μ i j)) :
    IsLittleGroupCovariant p' p W := by
  intro L S T hST hγ hLp hLp' μ
  have h : IsSpinLift L S T := ⟨hST, hγ⟩
  ext i j
  -- the left side as a parametric value
  have hl : IsParamValue D (fun ℓ => ∑ k, T k j * ∑ l, S i l * N μ ℓ l k)
      (∑ k, T k j * ∑ l, S i l * W μ l k) :=
    IsParamValue.sum _ _ fun k _ => IsParamValue.sum _ _ fun l _ => hW μ l k
  have hr : IsParamValue D (fun ℓ => ∑ ν, ((L μ ν : ℝ) : ℂ) * N ν ℓ i j)
      (∑ ν, ((L μ ν : ℝ) : ℂ) * W ν i j) :=
    IsParamValue.sum _ _ fun ν _ => hW ν i j
  have heq := IsParamValue.eq_of_loopAct h (hD L S T h hLp hLp') hl hr fun ℓ => by
    have := congrFun (congrFun (hN L S T h hLp hLp' μ ℓ) i) j
    simp only [Matrix.mul_apply, vecAct, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [Matrix.mul_apply, vecAct, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← heq]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-! ### The class limits -/

/-- The vertex of `ε → 0⁺` limits of the value of class `c` at the on-shell pair `(p', p)` with
photon momentum `p' - p`. -/
noncomputable def classLimitV (c : Class5) (P : Params) (p p' : Fin 4 → ℝ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => Matrix.of fun i j => limUnder (𝓝[>] (0 : ℝ)) fun ε =>
    contractionValue₂ { P with ε := ε } c.rep (fun _ => p') (fun _ => p) (fun _ => p' - p)
      (fun _ => i) (fun _ => j) (fun _ => μ)

/-- The parametric data of an open-line class. -/
noncomputable def openData {c : Class5} (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses)
    (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) : ParamData where
  m := 7
  α := castLoopMatrix (class5LoopMatrixPV c)
  p := pvMomentaE c p p'
  M := pvMasses P
  E := {0, 1, 2, 3}
  hm := by norm_num
  hcrit := (QED.Integration.TwoLoop.noSubdivergenceRefined_two_loopMatrixPV_iff c).mpr hc
  c := 3 / 4 * min (P.m ^ 2 / 4) (min P.mγ P.Λ ^ 2)
  hc := mul_pos (by norm_num) (lt_min (by positivity) (pow_pos (lt_min hmγ hΛ) 2))
  hV := fun _ hz hz1 hU => ClassLimit.symanzikV_open_ge hc P hmγ hΛ hp hp' hq hz hz1 hU

/-- **Covariance of the limits of the open-line classes.** -/
theorem isLittleGroupCovariant_classLimitV {c : Class5}
    (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses) (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) :
    IsLittleGroupCovariant p' p (classLimitV c P p p') := by
  refine isLittleGroupCovariant_of_paramValue (openData hc P hm hmγ hΛ hp hp' hq)
    (fun L S T _ hLp hLp' i => mulVec_extMomenta hLp hLp' c _)
    (fun μ ℓ => ClassLimit.twoLoopNorm • classNumM c P p p' μ ℓ)
    (fun L S T h hLp hLp' μ ℓ => ?_) _ fun μ i j => ?_
  · rw [Matrix.mul_smul, Matrix.smul_mul, classNumM_cov hc h hLp hLp', vecAct_smul]
  · have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 :=
      by simp
    obtain ⟨Q, hQ, -, hT⟩ := ClassLimit.tendsto_contractionValue₂_open hc P hm hmγ hΛ
      (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p) hmom hp hp' hq
      (fun _ => i) (fun _ => j) (fun _ => μ)
    have hF : (fun ℓ => (ClassLimit.twoLoopNorm • classNumM c P p p' μ ℓ) i j) =
        fun ℓ => ClassLimit.twoLoopNorm * classNumeratorE c P (fun _ => p') (fun _ => p)
          (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) ℓ := by
      funext ℓ
      simp only [Matrix.smul_apply, classNumM, Matrix.of_apply, smul_eq_mul]
    rw [hF]
    refine ⟨Q, hQ, ?_, hT.limUnder_eq⟩
    exact (QED.TwoLoop.ClassIntegrable.refinedBound_classNumeratorE hc P (fun _ => p')
      (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ)).const_mul _

end QED.TwoLoop.LimitCovariance

end
