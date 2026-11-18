/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZeroLimitOpen
public import QED.OneLoop.FormFactorPair
public import QED.OneLoop.FormFactorSmooth
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The second-order limit for the counterterm classes

Part of obligation O2-22 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4).

* **`δ₂ in`, `δ₂ out`, `δ₃`.** Their limits are parametric values of product data (line kinds,
  with an auxiliary loop) divided by `auxLimit m`
  (`QED.TwoLoop.ReflCovariance.ctLimitV_d2In_entry`, …). The numerators are polynomials of degree
  at most `4` in `p'` at fixed loop momenta, and the lower bound `V ≥ 3/4 min(m², min(m_γ, Λ)²)` is
  uniform in `q² ≥ 0` (`QED.TwoLoop.CountertermLimit.symanzikV_kinds_ge`); `tendsto_kinds` applies
  `QED.TwoLoop.PauliZeroLimit.tendsto_piece` to any such class.
* **`δ₁`.** Each limit is `i δ₁` times the one-loop vertex (`ctLimitV_d1_eq_vertexOneLoop`), whose
  Pauli numerator is `e q² D² B(q²) / m` with `B` the one-loop Pauli coefficient
  (`pauliNum_vertexOneLoop`); `B` is continuous in `q²` at `0`
  (`QED.OneLoop.VertexLimit.contDiffOn_integral_pauliIntegrand`), so
  `S(u)/u² → i δ₁ e (4m²)³ B(0) / m` (`tendsto_d1`).
-/

@[expose] public section

open Complex Matrix Filter Topology Set MeasureTheory
open scoped Real

namespace QED.TwoLoop.PauliZeroLimit

open QED.Dirac QED.WickModel QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero
open QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassLimit
open QED.TwoLoop.CountertermLimit QED.TwoLoop.Insertion QED.TwoLoop.Relabel
open QED.Integration.TwoLoop (LoopQuartic RefinedBound castLoopMatrix symanzikV symanzikU
  IntNoSubdivergenceRefined noSubdivergenceRefined_castLoopMatrix_iff)

/-! ### Product data along the curve -/

/-- The parametric data of product data given by line kinds, along the curve. -/
noncomputable def kindsCurve {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind)
    (Ms : Fin (m + 1) → ℝ) (P : Params) (hm : 0 < P.m) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hMe : ∀ i, κ i ≠ .pho → Ms i ^ 2 = P.m ^ 2) (hMp : ∀ i, κ i = .pho → μ₀ ^ 2 ≤ Ms i ^ 2)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (κ i).dir) : CurveData where
  m := m
  α := castLoopMatrix fun i => (κ i).dir
  mom u := fun i => (κ i).mom (restMomentum P.m) (curveMomentum P.m u)
  M := Ms
  E := {0, 1, 2, 3}
  hm := hm7
  hcrit := (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit
  c := 3 / 4 * min (P.m ^ 2) (μ₀ ^ 2)
  hc := by positivity
  hV := fun u hu _ hz hz1 hU => symanzikV_kinds_ge κ Ms (dot_restMomentum (m := P.m))
    (dot_curveMomentum P.m hu) ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu)
    hMe hMp hz hz1 hU
  hmom := fun i μ => isUPoly_ext_curve P.m (fun p' => (κ i).mom (restMomentum P.m) p')
    (by rcases κ i with _ | _ | _ | _ <;> simp [LineKind.mom]) μ
  hVeven := fun u z => by
    have h := QED.TwoLoop.ReflCovariance.isSpinLift_reflect (K := axisOne)
      (by rw [dot_axisOne]; exact one_ne_zero)
    have e := QED.TwoLoop.ReflCovariance.symanzikV_map h (castLoopMatrix fun i => (κ i).dir)
      (fun i => (κ i).mom (restMomentum P.m) (curveMomentum P.m u)) Ms z
    simp only [← QED.TwoLoop.ReflCovariance.lineKind_mom_map, reflectMatrix_restMomentum,
      reflectMatrix_curveMomentum] at e
    exact e

/-- **The second-order limit for a class of product data.** -/
theorem tendsto_kinds {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind)
    (Ms : Fin (m + 1) → ℝ) (P : Params) (hm : 0 < P.m) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hMe : ∀ i, κ i ≠ .pho → Ms i ^ 2 = P.m ^ 2) (hMp : ∀ i, κ i = .pho → μ₀ ^ 2 ≤ Ms i ^ 2)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (κ i).dir)
    (num : (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (hnum : ∀ μ i j k, IsLoopPoly 1 4 fun y => num (y 0) μ k i j)
    (W : (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hW : ∀ u (hu : u ∈ Ioo (-1 : ℝ) 1) μ i j, ∃ v,
      IsParamValue ((kindsCurve hm7 κ Ms P hm hμ₀ hMe hMp hcrit).toParamData hu)
        (fun ℓ => num (curveMomentum P.m u) μ (ℓ 0) i j) v ∧
      W (curveMomentum P.m u) μ i j = v / auxLimit P.m) :
    ∃ L, Tendsto (fun u : ℝ =>
      (pauliNum P.m (curveMomentum P.m u) (restMomentum P.m) (W (curveMomentum P.m u)) +
        pauliNum P.m (curveMomentum P.m (-u)) (restMomentum P.m) (W (curveMomentum P.m (-u)))) /
          (2 * (u : ℂ) ^ 2)) (𝓝[≠] 0) (𝓝 L) := by
  set C := kindsCurve hm7 κ Ms P hm hμ₀ hMe hMp hcrit
  have hex : ∀ u (j : Idx), ∃ v : ℂ, ∀ hu : u ∈ Ioo (-1 : ℝ) 1,
      IsParamValue (C.toParamData hu)
        (fun ℓ => num (curveMomentum P.m u) j.1 (ℓ 0) j.2.1 j.2.2) v ∧
      W (curveMomentum P.m u) j.1 j.2.1 j.2.2 = v / auxLimit P.m := fun u j => by
    by_cases hu : u ∈ Ioo (-1 : ℝ) 1
    · obtain ⟨v, hv⟩ := hW u hu j.1 j.2.1 j.2.2
      exact ⟨v, fun _ => hv⟩
    · exact ⟨0, fun h => absurd h hu⟩
  choose v hv using hex
  obtain ⟨L, hL⟩ := tendsto_piece C (J := Idx) (D := 8) (n := 4) (r := 4) (Dω := 8)
    (fun u j ℓ => num (curveMomentum P.m u) j.1 (ℓ 0) j.2.1 j.2.2)
    (fun j => isUPoly_eval_of_isLoopPoly' (ι := Fin 2 → Fin 4 → ℝ) (n := 4)
      (G := fun ℓ y => num (y 0) j.1 (ℓ 0) j.2.1 j.2.2)
      (fun ℓ => hnum j.1 j.2.1 j.2.2 (ℓ 0))
      (ℓ := fun _ u => fun _ => curveMomentum P.m u) fun _ ν => isUPoly_curveMomentum P.m ν)
    (fun u hu j => by
      obtain ⟨Q, hQ, -, -⟩ := (hv u j hu).1
      exact ⟨Q, hQ⟩)
    (fun u hu j => by
      obtain ⟨Q, -, hB, -⟩ := (hv u j hu).1
      exact hB)
    v (fun u hu j => (hv u j hu).1)
    (fun u j => pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2)
    (fun j => isUPoly_pauliWt P.m j) (sum_pauliWt_zero P.m)
  refine ⟨L / auxLimit P.m, (hL.div_const (auxLimit P.m)).congr' ?_⟩
  have h1 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [h1] with u hu
  have hu' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hS : ∀ w (hw : w ∈ Ioo (-1 : ℝ) 1),
      pauliNum P.m (curveMomentum P.m w) (restMomentum P.m) (W (curveMomentum P.m w)) =
        (∑ j : Idx, pauliWt P.m (curveMomentum P.m w) (restMomentum P.m) j.1 j.2.1 j.2.2 *
          v w j) / auxLimit P.m := fun w hw => by
    rw [pauliNum_eq_sum_idx, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(hv w j hw).2, mul_div_assoc]
  rw [hS u hu, hS (-u) hu']
  ring

/-! ### The numerators of `δ₂ in`, `δ₂ out`, `δ₃` as polynomials in `p'` -/

theorem isLoopAffine_out_add (k : Fin 4 → ℝ) :
    IsLoopAffine fun y : Fin 1 → Fin 4 → ℝ => y 0 + k :=
  ⟨![1], k, fun y => by funext ν; simp⟩

theorem isLoopPolyMat_insertion_out (m δ₂ δm : ℝ) (k : Fin 4 → ℝ) :
    IsLoopPolyMat 1 3 fun y => -(electronNumerator m (y 0 + k) *
      fermionCtMatrix δ₂ δm m (y 0 + k) * electronNumerator m (y 0 + k)) := by
  have hA := isLoopAffine_out_add k
  have hC : IsLoopPolyMat 1 1 fun y => fermionCtMatrix δ₂ δm m (y 0 + k) := by
    simp only [fermionCtMatrix_eq]
    exact isLoopPolyMat_add (isLoopPolyMat_smul _ (hA.isLoopPolyMat_electronNumerator 0))
      (isLoopPolyMat_mono (isLoopPolyMat_smul _
        (IsLoopPolyMat.const (1 : Matrix (Fin 4) (Fin 4) ℂ))) (Nat.zero_le _))
  exact isLoopPolyMat_neg (((hA.isLoopPolyMat_electronNumerator m).mul hC).mul
    (hA.isLoopPolyMat_electronNumerator m))

theorem isLoopPoly_numD2In_out (P : Params) (p : Fin 4 → ℝ) (μ i j : Fin 4) (k : Fin 4 → ℝ) :
    IsLoopPoly 1 4 fun y => numD2In P (y 0) p μ k i j := by
  have h := isLoopPolyMat_vertexChain (L := 1) (a := 1) (b := 0) (d := 0) P.e μ
    (A := fun y => electronNumerator P.m (y 0 + k))
    (B := fun _ => -(electronNumerator P.m (p + k) * fermionCtMatrix P.δ₂ P.δm P.m (p + k) *
      electronNumerator P.m (p + k)))
    (D := fun _ => pvPhotonNum P.mγ P.Λ)
    ((isLoopAffine_out_add k).isLoopPolyMat_electronNumerator P.m) (IsLoopPolyMat.const _)
    (fun _ _ => IsLoopPoly.const _)
  exact (h i j).mono (by norm_num)

theorem isLoopPoly_numD2Out_out (P : Params) (p : Fin 4 → ℝ) (μ i j : Fin 4) (k : Fin 4 → ℝ) :
    IsLoopPoly 1 4 fun y => numD2Out P (y 0) p μ k i j := by
  have h := isLoopPolyMat_vertexChain (L := 1) (a := 3) (b := 0) (d := 0) P.e μ
    (A := fun y => -(electronNumerator P.m (y 0 + k) *
      fermionCtMatrix P.δ₂ P.δm P.m (y 0 + k) * electronNumerator P.m (y 0 + k)))
    (B := fun _ => electronNumerator P.m (p + k))
    (D := fun _ => pvPhotonNum P.mγ P.Λ)
    (isLoopPolyMat_insertion_out P.m P.δ₂ P.δm k) (IsLoopPolyMat.const _)
    (fun _ _ => IsLoopPoly.const _)
  exact (h i j).mono (by norm_num)

theorem isLoopPoly_numD3_out (P : Params) (p : Fin 4 → ℝ) (μ i j : Fin 4) (k : Fin 4 → ℝ) :
    IsLoopPoly 1 4 fun y => numD3 P (y 0) p μ k i j := by
  have h := isLoopPolyMat_vertexChain (L := 1) (a := 1) (b := 0) (d := 0) P.e μ
    (A := fun y => electronNumerator P.m (y 0 + k))
    (B := fun _ => electronNumerator P.m (p + k))
    (D := fun _ => photonNum P.δ₃ P.mγ P.Λ k)
    ((isLoopAffine_out_add k).isLoopPolyMat_electronNumerator P.m) (IsLoopPolyMat.const _)
    (fun _ _ => IsLoopPoly.const _)
  exact (h i j).mono (by norm_num)

/-! ### `δ₂ in`, `δ₂ out`, `δ₃` -/

section Kinds

variable (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
include hm hmγ hΛ

theorem tendsto_d2In :
    ∃ L, Tendsto (fun u : ℝ =>
      (pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
          (ctLimitV .d2In P (restMomentum P.m) (curveMomentum P.m u)) +
        pauliNum P.m (curveMomentum P.m (-u)) (restMomentum P.m)
          (ctLimitV .d2In P (restMomentum P.m) (curveMomentum P.m (-u)))) / (2 * (u : ℂ) ^ 2))
      (𝓝[≠] 0) (𝓝 L) :=
  tendsto_kinds (by norm_num) kindsD2In (massesD2In P) P hm (lt_min hmγ hΛ)
    (QED.TwoLoop.ReflCovariance.massesD2In_sq_of_ne_pho P)
    (QED.TwoLoop.ReflCovariance.min_sq_le_massesD2In_sq P hmγ hΛ)
    QED.TwoLoop.ReflCovariance.intNoSubdivergenceRefined_kindsD2In
    (fun p' μ k => numD2In P p' (restMomentum P.m) μ k)
    (fun μ i j k => isLoopPoly_numD2In_out P _ μ i j k)
    (fun p' => ctLimitV .d2In P (restMomentum P.m) p')
    (fun u hu μ i j => QED.TwoLoop.ReflCovariance.ctLimitV_d2In_entry P hm hmγ hΛ
      (dot_restMomentum (m := P.m)) (dot_curveMomentum P.m hu)
      ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu) μ i j)

theorem tendsto_d2Out :
    ∃ L, Tendsto (fun u : ℝ =>
      (pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
          (ctLimitV .d2Out P (restMomentum P.m) (curveMomentum P.m u)) +
        pauliNum P.m (curveMomentum P.m (-u)) (restMomentum P.m)
          (ctLimitV .d2Out P (restMomentum P.m) (curveMomentum P.m (-u)))) / (2 * (u : ℂ) ^ 2))
      (𝓝[≠] 0) (𝓝 L) :=
  tendsto_kinds (by norm_num) kindsD2Out (massesD2In P) P hm (lt_min hmγ hΛ)
    (massesD2In_sq_of_ne_pho_out P) (min_sq_le_massesD2In_sq_out P hmγ hΛ)
    intNoSubdivergenceRefined_kindsD2Out
    (fun p' μ k => numD2Out P p' (restMomentum P.m) μ k)
    (fun μ i j k => isLoopPoly_numD2Out_out P _ μ i j k)
    (fun p' => ctLimitV .d2Out P (restMomentum P.m) p')
    (fun u hu μ i j => ctLimitV_d2Out_entry P hm hmγ hΛ
      (dot_restMomentum (m := P.m)) (dot_curveMomentum P.m hu)
      ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu) μ i j)

theorem tendsto_d3Slot0 :
    ∃ L, Tendsto (fun u : ℝ =>
      (pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
          (ctLimitV .d3Slot0 P (restMomentum P.m) (curveMomentum P.m u)) +
        pauliNum P.m (curveMomentum P.m (-u)) (restMomentum P.m)
          (ctLimitV .d3Slot0 P (restMomentum P.m) (curveMomentum P.m (-u)))) /
            (2 * (u : ℂ) ^ 2))
      (𝓝[≠] 0) (𝓝 L) :=
  tendsto_kinds (by norm_num) kindsD3 (massesD3 P) P hm (lt_min hmγ hΛ)
    (QED.TwoLoop.ReflCovariance.massesD3_sq_of_ne_pho P)
    (QED.TwoLoop.ReflCovariance.min_sq_le_massesD3_sq P hmγ hΛ)
    QED.TwoLoop.ReflCovariance.intNoSubdivergenceRefined_kindsD3
    (fun p' μ k => numD3 P p' (restMomentum P.m) μ k)
    (fun μ i j k => isLoopPoly_numD3_out P _ μ i j k)
    (fun p' => ctLimitV .d3Slot0 P (restMomentum P.m) p')
    (fun u hu μ i j => QED.TwoLoop.ReflCovariance.ctLimitV_d3Slot0_entry P hm hmγ hΛ
      (dot_restMomentum (m := P.m)) (dot_curveMomentum P.m hu)
      ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu) μ i j)

end Kinds

/-! ### `δ₁` -/

theorem pauliNum_smul (m : ℝ) (p' p : Fin 4 → ℝ) (a : ℂ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    pauliNum m p' p (fun μ => a • V μ) = a * pauliNum m p' p V := by
  simp only [pauliNum_eq_sum, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

/-- The `δ₁` limits as `i δ₁` times the one-loop vertex. -/
theorem ctLimitV_d1_eq_vertexOneLoop {c : CtClass} (hc : c = .d1At1 ∨ c = .d1At2 ∨ c = .d1At3)
    (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0)
    (hp0' : 0 < p' 0) :
    ctLimitV c P p p' = fun μ => ((P.δ₁ : ℂ) * I) •
      QED.OneLoop.vertexOneLoop P.e P.m P.mγ P.Λ hm hmγ hΛ p' p hp' hp hp0' hp0 μ := by
  rw [ctLimitV_d1_eq P hm hmγ hΛ hp hp' hp0 hp0' hc]
  funext μ
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, VertexCovariance.integralVertex, Matrix.of_apply]
  rw [QED.OneLoop.VertexLimit.vertexOneLoop_eq_limit hm hmγ hΛ hp' hp hp0' hp0 μ,
    Matrix.of_apply, QED.OneLoop.VertexLimit.vertexLimit_entry_eq hm hmγ hΛ hp' hp hp0' hp0 μ i j]
  ring

/-- **The Pauli numerator of the one-loop vertex**: `e q² D² B / m`, for `q² > 0`. -/
theorem pauliNum_vertexOneLoop (e : ℝ) {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p)) :
    pauliNum m p' p (QED.OneLoop.vertexOneLoop e m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0) =
      (e : ℂ) * (Minkowski.dot (p' - p) (p' - p) : ℂ) *
        (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2 *
          (QED.OneLoop.VertexLimit.formFactorB e m mγ Λ p' p : ℂ) / m := by
  by_cases he : e = 0
  · subst he
    have h0 : QED.OneLoop.vertexOneLoop 0 m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0 =
        fun μ => (0 : ℂ) • QED.OneLoop.vertexOneLoop 0 m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0 μ := by
      funext μ
      ext i j
      rw [QED.OneLoop.VertexLimit.vertexOneLoop_eq_limit hm hmγ hΛ hp' hp hp0' hp0 μ,
        Matrix.of_apply, QED.OneLoop.VertexLimit.vertexLimit_entry_eq hm hmγ hΛ hp' hp hp0' hp0]
      simp
    rw [h0, pauliNum_smul]
    simp
  · have hF := QED.OneLoop.eq_formFactorProj_of_isFormFactorPair he hm.ne' hp' hp hq
      (QED.OneLoop.VertexLimit.isFormFactorPair_vertexOneLoop (e := e) hm hmγ hΛ hp' hp hp0' hp0)
    have hB := congrArg Prod.snd hF
    simp only at hB
    rw [hB, formFactorProj₂_eq_pauliNum]
    have he' : (e : ℂ) ≠ 0 := by exact_mod_cast he
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    have hq' : (Minkowski.dot (p' - p) (p' - p) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have hD : 4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < 4 * m ^ 2 + Minkowski.dot (p' - p) (p' - p) := by positivity
      exact_mod_cast this.ne'
    field_simp

/-- **The second-order limit for a `δ₁` class.** -/
theorem tendsto_d1 {c : CtClass} (hc : c = .d1At1 ∨ c = .d1At2 ∨ c = .d1At3) (P : Params)
    (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    ∃ L, Tendsto (fun u : ℝ =>
      (pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
          (ctLimitV c P (restMomentum P.m) (curveMomentum P.m u)) +
        pauliNum P.m (curveMomentum P.m (-u)) (restMomentum P.m)
          (ctLimitV c P (restMomentum P.m) (curveMomentum P.m (-u)))) / (2 * (u : ℂ) ^ 2))
      (𝓝[≠] 0) (𝓝 L) := by
  set g : ℝ → ℝ := fun s => ∫ z, QED.OneLoop.VertexLimit.pauliIntegrand P.m (P.mγ, P.Λ, s) z
    ∂QED.Integration.feynmanMeasure with hg_def
  have hg : ContinuousAt g 0 :=
    (QED.OneLoop.VertexLimit.contDiffOn_integral_pauliIntegrand hm hmγ hΛ).continuousOn.continuousAt
      (Ioi_mem_nhds (by nlinarith [hm]))
  -- the explicit function
  set Φ : ℝ → ℂ := fun u => ((P.δ₁ : ℂ) * I) * ((P.e : ℂ) *
    ((4 * P.m ^ 2 / (1 - u ^ 2) : ℝ) : ℂ) * (4 * (P.m : ℂ) ^ 2 + (curveQ P.m u : ℂ)) ^ 2 *
      ((P.e ^ 2 / (8 * π ^ 2) * g (curveQ P.m u) : ℝ) : ℂ) / P.m) with hΦ
  have hcq : ContinuousAt (curveQ P.m) 0 := by
    unfold curveQ
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
  have hgq : ContinuousAt (fun u => g (curveQ P.m u)) 0 := by
    have h0 : curveQ P.m 0 = 0 := by simp [curveQ]
    have hg' : ContinuousAt g (curveQ P.m 0) := by rw [h0]; exact hg
    exact hg'.comp hcq
  have hden : ContinuousAt (fun u : ℝ => 4 * P.m ^ 2 / (1 - u ^ 2)) 0 :=
    ContinuousAt.div continuousAt_const (by fun_prop) (by norm_num)
  have hΦc : ContinuousAt Φ 0 := by
    have c1 := Complex.continuous_ofReal.continuousAt.comp hden
    have c2 := Complex.continuous_ofReal.continuousAt.comp hcq
    have c3 := Complex.continuous_ofReal.continuousAt.comp
      ((continuousAt_const (y := P.e ^ 2 / (8 * π ^ 2))).mul hgq)
    exact continuousAt_const.mul ((((continuousAt_const.mul c1).mul
      ((continuousAt_const.add c2).pow 2)).mul c3).div_const _)
  refine ⟨Φ 0, (hΦc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_⟩
  have h0 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  have h1 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 ∧ u ≠ 0 :=
    h0.and self_mem_nhdsWithin
  filter_upwards [h1] with u ⟨hu, hu0⟩
  have hu' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hS : ∀ w (hw : w ∈ Ioo (-1 : ℝ) 1), w ≠ 0 →
      pauliNum P.m (curveMomentum P.m w) (restMomentum P.m)
        (ctLimitV c P (restMomentum P.m) (curveMomentum P.m w)) = (w : ℂ) ^ 2 * Φ w := by
    intro w hw hw0
    have hqpos : 0 < curveQ P.m w := by
      have := one_sub_sq_pos hw
      unfold curveQ
      have : 0 < w ^ 2 := by positivity
      positivity
    rw [ctLimitV_d1_eq_vertexOneLoop hc P hm hmγ hΛ (dot_restMomentum (m := P.m))
      (dot_curveMomentum P.m hw) (restMomentum_pos hm) (curveMomentum_pos hm hw),
      pauliNum_smul, pauliNum_vertexOneLoop P.e hm hmγ hΛ _ _ _ _
        ((dot_curveMomentum_sub P.m hw).symm ▸ hqpos),
      QED.OneLoop.VertexLimit.formFactorB_eq (dot_curveMomentum P.m hw)
        (dot_restMomentum (m := P.m)), dot_curveMomentum_sub P.m hw]
    have hw1 := (one_sub_sq_pos hw).ne'
    have hQw : ((curveQ P.m w : ℝ) : ℂ) = (w : ℂ) ^ 2 * ((4 * P.m ^ 2 / (1 - w ^ 2) : ℝ) : ℂ) := by
      rw [← ofReal_pow, ← ofReal_mul]
      congr 1
      unfold curveQ
      field_simp
    simp only [hΦ, hg_def]
    generalize (∫ z, QED.OneLoop.VertexLimit.pauliIntegrand P.m (P.mγ, P.Λ, curveQ P.m w) z
      ∂QED.Integration.feynmanMeasure) = G
    rw [hQw]
    ring
  rw [hS u hu hu0, hS (-u) hu' (neg_ne_zero.mpr hu0)]
  have hΦn : Φ (-u) = Φ u := by simp only [hΦ, curveQ_neg, neg_sq]
  rw [hΦn]
  have hu0' : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu0
  push_cast
  field_simp
  ring

end QED.TwoLoop.PauliZeroLimit

end
