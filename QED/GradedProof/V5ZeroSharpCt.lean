/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.V5ZeroSharpAlg
public import QED.TwoLoop.PauliZeroCovariance
public import QED.TwoLoop.UnitSCCtAssembly

/-!
# `♯` of the limits of the counterterm classes

Helper level for the reality of the order-`e⁵` vertex limit (V5Zero, part D). Every
counterterm-class limit `W` satisfies `W♯ = -W` (`sharp_ctLimitV`), for `m, m_γ, Λ > 0`,
on-shell `p, p'` of positive energy with `q² ≥ 0`, and any real counterterms:

* `δ₂ in`, `δ₂ out`, `δ₃`: the entries are parametric values of `♯`-fixed numerators divided by
  `auxLimit m = i π²/(2m²)`, which is imaginary (`sharp_ctLimitV_of_entry`);
* `δ₁`: the limit is `δ₁ · i e³/(16π²)` times the integral of the `♯`-fixed closed form of the
  one-loop vertex (`sharp_closedFormMatrix`, `sharp_ctLimitV_d1`).
-/

@[expose] public section

open Complex Matrix MeasureTheory
open scoped Real

namespace QED.GradedProof.V5Zero.Sharp

open QED.Dirac QED.GradedProof.SE2Real QED.TwoLoop.LimitCovariance QED.TwoLoop.Bridge
open QED.TwoLoop.CountertermLimit QED.WickModel QED.TwoLoop.ReflCovariance QED.TwoLoop.Relabel
open QED.TwoLoop.VertexCovariance (integralVertex)


theorem conj_auxLimit {M : ℝ} (hM : 0 < M) : starRingEnd ℂ (auxLimit M) = -auxLimit M := by
  rw [QED.TwoLoop.UnitSCCt.auxLimit_eq hM]
  simp only [map_div₀, map_mul, Complex.conj_I, map_pow, Complex.conj_ofReal, map_ofNat]
  ring

/-- **A counterterm vertex of parametric values divided by `auxLimit m`**, with `♯`-fixed
numerators, satisfies `V♯ = -V`. -/
theorem sharp_ctLimitV_of_entry {M : ℝ} (hM : 0 < M) (D : ParamData)
    (N : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ) (hN : ∀ μ k, sharp (N μ k) = N μ k)
    (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hV : ∀ μ i j, ∃ v, IsParamValue D (fun ℓ => N μ (ℓ 0) i j) v ∧ V μ i j = v / auxLimit M)
    (μ : Fin 4) : sharp (V μ) = -V μ := by
  choose v hv hVv using hV
  have hW := sharp_eq_smul_of_isParamValue_vertex (fun μ ℓ => N μ (ℓ 0))
    (fun μ => Matrix.of (v μ)) 1 (fun μ ℓ => by rw [one_smul]; exact hN μ (ℓ 0))
    (fun μ i j => hv μ i j) μ
  have eV : V μ = (auxLimit M)⁻¹ • Matrix.of (v μ) := by
    ext i j
    simp only [hVv, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [eV, sharp_smul, hW, one_smul, map_inv₀, conj_auxLimit hM, inv_neg, neg_smul]

section Entries

variable (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p p' : Fin 4 → ℝ}
  (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
include hm hmγ hΛ hp hp' hq

theorem sharp_ctLimitV_d2In (μ : Fin 4) :
    sharp (ctLimitV .d2In P p p' μ) = -ctLimitV .d2In P p p' μ :=
  sharp_ctLimitV_of_entry hm _ (fun μ k => numD2In P p' p μ k)
    (fun μ k => sharp_numD2In P p' p μ k) _
    (fun μ i j => ctLimitV_d2In_entry P hm hmγ hΛ hp hp' hq μ i j) μ

theorem sharp_ctLimitV_d2Out (μ : Fin 4) :
    sharp (ctLimitV .d2Out P p p' μ) = -ctLimitV .d2Out P p p' μ :=
  sharp_ctLimitV_of_entry hm _ (fun μ k => numD2Out P p' p μ k)
    (fun μ k => sharp_numD2Out P p' p μ k) _
    (fun μ i j => QED.TwoLoop.PauliZero.ctLimitV_d2Out_entry P hm hmγ hΛ hp hp' hq μ i j) μ

theorem sharp_ctLimitV_d3Slot0 (μ : Fin 4) :
    sharp (ctLimitV .d3Slot0 P p p' μ) = -ctLimitV .d3Slot0 P p p' μ :=
  sharp_ctLimitV_of_entry hm _ (fun μ k => numD3 P p' p μ k)
    (fun μ k => sharp_numD3 P p' p μ k) _
    (fun μ i j => ctLimitV_d3Slot0_entry P hm hmγ hΛ hp hp' hq μ i j) μ

end Entries

/-! ### The `δ₁` classes -/

theorem sharp_vertexNumeratorMatrix (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (k : Fin 4 → ℝ) :
    sharp (QED.OneLoop.vertexNumeratorMatrix m p' p μ k) =
      QED.OneLoop.vertexNumeratorMatrix m p' p μ k := by
  simp only [QED.OneLoop.vertexNumeratorMatrix, sharp_sum, sharp_smul, sharp_mul, sharp_gamma,
    sharp_sub, sharp_one, sharp_slash, Complex.conj_ofReal]

theorem sharp_closedFormMatrix (m mγ Λ : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (z : ℝ × ℝ) :
    sharp (QED.OneLoop.VertexLimit.closedFormMatrix m mγ Λ p' p μ z) =
      QED.OneLoop.VertexLimit.closedFormMatrix m mγ Λ p' p μ z := by
  simp only [QED.OneLoop.VertexLimit.closedFormMatrix, sharp_smul, sharp_add, sharp_gamma,
    sharp_vertexNumeratorMatrix, map_mul, map_ofNat, Complex.conj_ofReal]

theorem sharp_integralVertex {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (f : X → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (hf : ∀ x μ, sharp (f x μ) = f x μ) (μ : Fin 4) :
    sharp (integralVertex ν f μ) = integralVertex ν f μ := by
  ext i j
  simp only [integralVertex, sharp_apply, Matrix.of_apply]
  rw [← integral_conj, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have := congrFun (congrFun (hf x μ) i) j
  rw [sharp_apply] at this
  exact this

theorem sharp_ctLimitV_d1 (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp0 : 0 < p 0) (hp0' : 0 < p' 0) {c : CtClass}
    (hc : c = .d1At1 ∨ c = .d1At2 ∨ c = .d1At3) (μ : Fin 4) :
    sharp (ctLimitV c P p p' μ) = -ctLimitV c P p p' μ := by
  rw [QED.TwoLoop.PauliZero.ctLimitV_d1_eq P hm hmγ hΛ hp hp' hp0 hp0' hc]
  dsimp only
  rw [sharp_smul, sharp_integralVertex _ _ (fun z μ => sharp_closedFormMatrix _ _ _ _ _ _ _),
    ← neg_smul]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- **`W♯ = -W` for every counterterm-class limit.** -/
theorem sharp_ctLimitV (c : CtClass) (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0) (hp0' : 0 < p' 0)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (μ : Fin 4) :
    sharp (ctLimitV c P p p' μ) = -ctLimitV c P p p' μ := by
  cases c
  · exact sharp_ctLimitV_d2In P hm hmγ hΛ hp hp' hq μ
  · exact sharp_ctLimitV_d2Out P hm hmγ hΛ hp hp' hq μ
  · exact sharp_ctLimitV_d3Slot0 P hm hmγ hΛ hp hp' hq μ
  · rw [QED.TwoLoop.PauliZero.ctLimitV_d3Slot1_eq]
    exact sharp_ctLimitV_d3Slot0 P hm hmγ hΛ hp hp' hq μ
  · exact sharp_ctLimitV_d1 P hm hmγ hΛ hp hp' hp0 hp0' (Or.inl rfl) μ
  · exact sharp_ctLimitV_d1 P hm hmγ hΛ hp hp' hp0 hp0' (Or.inr (Or.inl rfl)) μ
  · exact sharp_ctLimitV_d1 P hm hmγ hΛ hp hp' hp0 hp0' (Or.inr (Or.inr rfl)) μ

end QED.GradedProof.V5Zero.Sharp

end
