/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZeroLimitPiece
public import QED.TwoLoop.PauliZeroLimitCurve

/-!
# The second-order limit for the six open-line classes

Part of obligation O2-22 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4). For an open-line class
`c ∈ {L, X, C₊, C₋, S₊, S₋}` and `S_c(u)` the Pauli numerator of the class limit
`classLimitV c P p (p'(u))` along the curve, `(S_c(u) + S_c(-u)) / (2u²)` has a limit as `u → 0`
(`tendsto_open`).

* The class numerators, at fixed loop momenta, are polynomials of degree at most `4` in the
  outgoing momentum `p'` (`isLoopPoly_classNumeratorE_out`): the gauge vertex factors do not see
  the momenta (`amplitudeNumerator_gauges`), and each line momentum is affine in `p'`
  (`isLoopAffine_classMomE`).
* `openCurve`: the parametric data of the Pauli–Villars form along the curve, with the uniform
  lower bound `V ≥ 3/4 min(m²/4, min(m_γ, Λ)²)` (`QED.TwoLoop.ClassLimit.symanzikV_open_ge`) and
  `V` even in `u` by the reflection.
-/

@[expose] public section

open Complex Matrix Filter Topology Set
open scoped Real

namespace QED.TwoLoop.PauliZeroLimit

open QED.Dirac QED.WickModel QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero
open QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassLimit
open QED.Integration.TwoLoop (LoopQuartic RefinedBound castLoopMatrix class5LoopMatrixPV
  class5LoopMatrix symanzikV symanzikU pvLines)

/-! ### The numerators as polynomials in `p'` -/

/-- The numerator of a contraction of gauge vertices does not depend on the external momentum
arguments. -/
theorem amplitudeNumerator_gauges (P : Params) {nf nA N : ℕ}
    (C : Contraction nf nA (Enumeration.gauges N)) (φ : Flavoring (Enumeration.gauges N))
    (pIn pIn' : Fin nf → Fin 4 → ℝ) (kIn kIn' : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    amplitudeNumerator P C φ pIn kIn k αOut βIn μ =
      amplitudeNumerator P C φ pIn' kIn' k αOut βIn μ := by
  unfold amplitudeNumerator
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => ?_
  rw [Finset.prod_congr rfl fun t _ => vertexFactor_gauges P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
    (psiMomentum₂ C pIn k) (psiMomentum₂ C pIn' k) (photonMomentum₂ C kIn k)
    (photonMomentum₂ C kIn' k) t]

/-- Each external line momentum of a class is `p`, `p'` or `0`, independently of `p'`. -/
theorem extMomenta_cases (c : Class5) (p : Fin 4 → ℝ) (i : Fin 6) :
    (∀ p', extMomenta c p p' i = p) ∨ (∀ p', extMomenta c p p' i = p') ∨
      (∀ p', extMomenta c p p' i = 0) := by
  cases c <;> fin_cases i <;>
    simp [extMomenta, QED.Integration.TwoLoop.classLXMomenta,
      QED.Integration.TwoLoop.classCpSpMomenta, QED.Integration.TwoLoop.classCmSmMomenta,
      QED.Integration.TwoLoop.classVPMomenta]

theorem isLoopAffine_lineMomentum_ext {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    (q : (Fin 4 → ℝ) → Fin (m + 1) → Fin 4 → ℝ) (i : Fin (m + 1)) (ℓ : Fin 2 → Fin 4 → ℝ)
    (hq : (∃ b, ∀ p', q p' i = b) ∨ (∀ p', q p' i = p')) :
    IsLoopAffine fun y : Fin 1 → Fin 4 → ℝ =>
      QED.Integration.TwoLoop.lineMomentum α (q (y 0)) i ℓ := by
  rcases hq with ⟨b, hb⟩ | hb
  · refine ⟨0, QED.Integration.TwoLoop.lineMomentum α (fun _ => b) i ℓ, fun y => ?_⟩
    funext μ
    simp [QED.Integration.TwoLoop.lineMomentum, hb]
  · refine ⟨![1], fun μ => ∑ s, α i s * ℓ s μ, fun y => ?_⟩
    funext μ
    simp [QED.Integration.TwoLoop.lineMomentum, hb, add_comm]

theorem isLoopAffine_classMomE (c : Class5) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ)
    (f : Line c.rep) :
    IsLoopAffine fun y : Fin 1 → Fin 4 → ℝ => classMomE c p (y 0) ℓ f := by
  unfold classMomE
  refine isLoopAffine_lineMomentum_ext _ (fun p' => extMomenta c p p') _ ℓ ?_
  rcases extMomenta_cases c p (lineIdx f) with h | h | h
  · exact Or.inl ⟨p, h⟩
  · exact Or.inr h
  · exact Or.inl ⟨0, h⟩

/-- **The open-class numerators are polynomials of degree at most `4` in `p'`**, at fixed loop
momenta. -/
theorem isLoopPoly_classNumeratorE_out {c : Class5}
    (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses) (P : Params) (p : Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsLoopPoly 1 4 fun y => classNumeratorE c P (fun _ => y 0) (fun _ => p) (fun _ => y 0 - p)
      αOut βIn μ ℓ := by
  have e : ∀ y : Fin 1 → Fin 4 → ℝ, classNumeratorE c P (fun _ => y 0) (fun _ => p)
      (fun _ => y 0 - p) αOut βIn μ ℓ = amplitudeNumerator P c.rep zeroFlavoring (fun _ => p)
        (fun _ => 0) (classMomE c p (y 0) ℓ) αOut βIn μ := fun y =>
    amplitudeNumerator_gauges P c.rep zeroFlavoring _ _ _ _ _ αOut βIn μ
  simp only [e]
  exact (isLoopPoly_amplitudeNumerator P c.rep zeroFlavoring (fun _ => p) (fun _ => 0)
    (fun y => classMomE c p (y 0) ℓ) (fun f => isLoopAffine_classMomE c p ℓ (.inl f))
    αOut βIn μ).mono (QED.TwoLoop.ClassIntegrable.fermionLine_facts hc).2.2.le

/-! ### The parametric data along the curve -/

theorem isUPoly_ext_curve {ι : Type*} (m : ℝ) (q : (Fin 4 → ℝ) → Fin 4 → ℝ)
    (hq : (∀ p', q p' = restMomentum m) ∨ (∀ p', q p' = p') ∨ (∀ p', q p' = 0)) (μ : Fin 4) :
    IsUPoly (ι := ι) 2 fun _ u => wt u * ((q (curveMomentum m u) μ : ℝ) : ℂ) := by
  rcases hq with h | h | h
  · simp only [h]
    exact isUPoly_wt.mul_const _
  · simp only [h]
    exact isUPoly_curveMomentum m μ
  · simp only [h, Pi.zero_apply, ofReal_zero, mul_zero]
    exact IsUPoly.const fun _ => 0

/-- The parametric data of the Pauli–Villars form of an open-line class along the curve. -/
noncomputable def openCurve {c : Class5} (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses)
    (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) : CurveData where
  m := 7
  α := castLoopMatrix (class5LoopMatrixPV c)
  mom u := pvMomentaE c (restMomentum P.m) (curveMomentum P.m u)
  M := pvMasses P
  E := {0, 1, 2, 3}
  hm := by norm_num
  hcrit := (QED.Integration.TwoLoop.noSubdivergenceRefined_two_loopMatrixPV_iff c).mpr hc
  c := 3 / 4 * min (P.m ^ 2 / 4) (min P.mγ P.Λ ^ 2)
  hc := mul_pos (by norm_num) (lt_min (by positivity) (pow_pos (lt_min hmγ hΛ) 2))
  hV := fun u hu _ hz hz1 hU => symanzikV_open_ge hc P hmγ hΛ (dot_restMomentum (m := P.m))
    (dot_curveMomentum P.m hu) ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu) hz
    hz1 hU
  hmom := fun i μ => isUPoly_ext_curve P.m (fun p' => extMomenta c (restMomentum P.m) p' (pvLines i))
    (by
      rcases extMomenta_cases c (restMomentum P.m) (pvLines i) with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)) μ
  hVeven := fun u z => by
    have h := QED.TwoLoop.ReflCovariance.isSpinLift_reflect (K := axisOne)
      (by rw [dot_axisOne]; exact one_ne_zero)
    have e := QED.TwoLoop.ReflCovariance.symanzikV_map h (castLoopMatrix (class5LoopMatrixPV c))
      (pvMomentaE c (restMomentum P.m) (curveMomentum P.m u)) (pvMasses P) z
    rw [← QED.TwoLoop.ReflCovariance.pvMomentaE_map, reflectMatrix_restMomentum,
      reflectMatrix_curveMomentum] at e
    exact e

/-! ### The Pauli weights along the curve -/

/-- `isUPoly_eval_of_isLoopPoly` for polynomials depending on the parameter. -/
theorem isUPoly_eval_of_isLoopPoly' {ι : Type*} {L n : ℕ} {G : ι → (Fin L → Fin 4 → ℝ) → ℂ}
    (hG : ∀ x, IsLoopPoly L n (G x)) {ℓ : ι → ℝ → Fin L → Fin 4 → ℝ}
    (hℓ : ∀ s ν, IsUPoly 2 fun x u => wt u * ((ℓ x u s ν : ℝ) : ℂ)) :
    IsUPoly (2 * n) fun x u => wt u ^ n * G x (ℓ x u) := fun x =>
  isUPoly_eval_of_isLoopPoly (hG x) hℓ x

/-- The index `(μ, i, j)` of the entries of a vertex. -/
abbrev Idx := Fin 4 × Fin 4 × Fin 4

theorem pauliNum_eq_sum_idx (m : ℝ) (p' p : Fin 4 → ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    pauliNum m p' p V = ∑ j : Idx, pauliWt m p' p j.1 j.2.1 j.2.2 * V j.1 j.2.1 j.2.2 := by
  rw [pauliNum_eq_sum, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]

theorem isUPoly_pauliWt {ι : Type*} (m : ℝ) (j : Idx) :
    IsUPoly (ι := ι) 8 fun _ u =>
      wt u ^ 4 * pauliWt m (curveMomentum m u) (restMomentum m) j.1 j.2.1 j.2.2 :=
  isUPoly_eval_of_isLoopPoly (isLoopPoly_pauliWt m (restMomentum m) j.1 j.2.1 j.2.2)
    (ℓ := fun _ u => fun _ => curveMomentum m u) fun _ ν => isUPoly_curveMomentum m ν

theorem sum_pauliWt_zero (m : ℝ) (Y : Idx → ℂ) :
    ∑ j : Idx, pauliWt m (curveMomentum m 0) (restMomentum m) j.1 j.2.1 j.2.2 * Y j = 0 := by
  have h := pauliNum_self m (restMomentum m) (dot_restMomentum (m := m))
    (fun μ => Matrix.of fun i j => Y (μ, i, j))
  rw [pauliNum_eq_sum_idx] at h
  rw [curveMomentum_zero]
  simpa using h

/-! ### The open classes -/

/-- **The second-order limit for an open-line class.** -/
theorem tendsto_open {c : Class5} (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses)
    (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    ∃ L, Tendsto (fun u : ℝ =>
      (pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
          (classLimitV c P (restMomentum P.m) (curveMomentum P.m u)) +
        pauliNum P.m (curveMomentum P.m (-u)) (restMomentum P.m)
          (classLimitV c P (restMomentum P.m) (curveMomentum P.m (-u)))) / (2 * (u : ℂ) ^ 2))
      (𝓝[≠] 0) (𝓝 L) := by
  set C := openCurve hc P hm hmγ hΛ
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
  obtain ⟨L, hL⟩ := tendsto_piece C (J := Idx) (D := 8) (n := 4) (r := 4) (Dω := 8)
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
  refine ⟨L, hL.congr fun u => ?_⟩
  simp only [pauliNum_eq_sum_idx]

end QED.TwoLoop.PauliZeroLimit

end
