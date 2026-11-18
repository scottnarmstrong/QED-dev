/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZeroExplicitPiece
public import QED.TwoLoop.PauliZeroLimitCt

/-!
# The explicit second-order limits of the seven counterterm classes

Part of the explicit form of the `q² → 0⁺` limit of obligation O2-22
(`docs/TWO-LOOP-DERIVATION.md`, section 5.4). Along the curve
`p'(u) = m((1+u²)/(1-u²), 2u/(1-u²), 0, 0)`, `p = (m, 0, 0, 0)`, let `S_c(u)` be the Pauli
numerator of the `ε → 0⁺` limit of the counterterm class `c`. This file identifies the limit of
`(S_c(u) + S_c(-u)) / (2u²)` as `u → 0`, `u ≠ 0`:

* **`δ₂ in`, `δ₂ out`, `δ₃`** (`tendsto_kinds_explicit`): the class limit is the parametric value
  of product data (the one-loop graph with the counterterm insertion and an auxiliary loop of
  three lines of mass `m`, decoupled from the external momenta) divided by the value
  `auxLimit m` of the auxiliary loop. The `q → 0` value is
  `kindsZero = (∫_{Δ} c₂[N(x, ·)] / V(x)^{N-4} dx) / auxLimit m` with `N(x, u)` the
  Pauli-projected parametric numerator along the curve (`kindsNum`) and `V(x)` the second
  Symanzik function at `q = 0` (`kindsV`). `N = 8` lines for `δ₂` (`d2InZero`, `d2OutZero`),
  `N = 9` for `δ₃` (`d3Zero`; both `δ₃` slots have the same limit).
* **`δ₁`** at any of its three vertices (`tendsto_d1_explicit`): the class limit is `i δ₁` times
  the one-loop vertex, and the value is
  `d1Zero P = i δ₁ e (4m²)³ (e²/(8π²)) B(0) / m` with
  `B(0) = ∫ pauliIntegrand m (m_γ, Λ, 0)` the one-loop Pauli integral at `q² = 0`.
-/

@[expose] public section

open Complex Matrix Filter Topology Set MeasureTheory
open scoped Real

namespace QED.TwoLoop.PauliZeroExplicit

open QED.Dirac QED.WickModel QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero
open QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassLimit
open QED.TwoLoop.CountertermLimit QED.TwoLoop.Insertion QED.TwoLoop.Relabel
open QED.TwoLoop.PauliZeroLimit
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.TwoLoop (LoopQuartic RefinedBound castLoopMatrix symanzikV symanzikU
  IntNoSubdivergenceRefined noSubdivergenceRefined_castLoopMatrix_iff)

/-! ### Product data -/

/-- **The Pauli-projected parametric numerator of product data along the curve.** -/
noncomputable def kindsNum {m : ℕ} (κ : Fin (m + 1) → LineKind) (Ms : Fin (m + 1) → ℝ)
    (P : Params) (num : (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (x : Fin m → ℝ) (u : ℝ) : ℂ :=
  ∑ j : Idx, pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2 *
    (-((π : ℂ) ^ 4) * paramNumOf (fun ℓ => num (curveMomentum P.m u) j.1 (ℓ 0) j.2.1 j.2.2)
      (castLoopMatrix fun i => (κ i).dir)
      (fun i => (κ i).mom (restMomentum P.m) (curveMomentum P.m u)) Ms x)

/-- The second Symanzik function of product data at `q = 0`. -/
noncomputable def kindsV {m : ℕ} (κ : Fin (m + 1) → LineKind) (Ms : Fin (m + 1) → ℝ)
    (P : Params) (x : Fin m → ℝ) : ℝ :=
  symanzikV (castLoopMatrix fun i => (κ i).dir)
    (fun i => (κ i).mom (restMomentum P.m) (restMomentum P.m)) Ms (simplexPoint x)

/-- **The `q → 0` value of product data**:
`(∫_{Δ} c₂[N(x, ·)] / V(x)^{m-3} dx) / auxLimit m`. -/
noncomputable def kindsZero {m : ℕ} (κ : Fin (m + 1) → LineKind) (Ms : Fin (m + 1) → ℝ)
    (P : Params) (num : (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ) : ℂ :=
  (∫ x in simplexSet m, secondCoeff (kindsNum κ Ms P num x) /
    ((kindsV κ Ms P x : ℝ) : ℂ) ^ (m - 3)) / auxLimit P.m

/-- **The explicit second-order limit for a class of product data.** -/
theorem tendsto_kinds_explicit {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind)
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
    Tendsto (fun u : ℝ =>
      (pauliNum P.m (curveMomentum P.m u) (restMomentum P.m) (W (curveMomentum P.m u)) +
        pauliNum P.m (curveMomentum P.m (-u)) (restMomentum P.m) (W (curveMomentum P.m (-u)))) /
          (2 * (u : ℂ) ^ 2)) (𝓝[≠] 0) (𝓝 (kindsZero κ Ms P num)) := by
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
  have hL := tendsto_piece_explicit C (J := Idx) (D := 8) (n := 4) (r := 4) (Dω := 8)
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
  have hval : (∫ x in simplexSet C.m,
      secondCoeff (projNum C (fun u (j : Idx) ℓ => num (curveMomentum P.m u) j.1 (ℓ 0) j.2.1 j.2.2)
        (fun u (j : Idx) => pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2)
        x) / ((C.vfun x 0 : ℝ) : ℂ) ^ (C.m - 3)) / auxLimit P.m = kindsZero κ Ms P num := by
    simp only [C, kindsZero, kindsV, CurveData.vfun, kindsCurve, curveMomentum_zero]
    rfl
  rw [← hval]
  refine (hL.div_const (auxLimit P.m)).congr' ?_
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

/-! ### `δ₂ in`, `δ₂ out`, `δ₃` -/

/-- **The `q → 0` value of the `δ₂`, `δ_m` class on the incoming internal electron line.** -/
noncomputable def d2InZero (P : Params) : ℂ :=
  kindsZero kindsD2In (massesD2In P) P fun p' μ k => numD2In P p' (restMomentum P.m) μ k

/-- **The `q → 0` value of the `δ₂`, `δ_m` class on the outgoing internal electron line.** -/
noncomputable def d2OutZero (P : Params) : ℂ :=
  kindsZero kindsD2Out (massesD2In P) P fun p' μ k => numD2Out P p' (restMomentum P.m) μ k

/-- **The `q → 0` value of a `δ₃` class** (either slot). -/
noncomputable def d3Zero (P : Params) : ℂ :=
  kindsZero kindsD3 (massesD3 P) P fun p' μ k => numD3 P p' (restMomentum P.m) μ k

section Kinds

variable (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
include hm hmγ hΛ

theorem tendsto_d2In_explicit :
    Tendsto (fun u : ℝ =>
      (pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
          (ctLimitV .d2In P (restMomentum P.m) (curveMomentum P.m u)) +
        pauliNum P.m (curveMomentum P.m (-u)) (restMomentum P.m)
          (ctLimitV .d2In P (restMomentum P.m) (curveMomentum P.m (-u)))) / (2 * (u : ℂ) ^ 2))
      (𝓝[≠] 0) (𝓝 (d2InZero P)) :=
  tendsto_kinds_explicit (by norm_num) kindsD2In (massesD2In P) P hm (lt_min hmγ hΛ)
    (QED.TwoLoop.ReflCovariance.massesD2In_sq_of_ne_pho P)
    (QED.TwoLoop.ReflCovariance.min_sq_le_massesD2In_sq P hmγ hΛ)
    QED.TwoLoop.ReflCovariance.intNoSubdivergenceRefined_kindsD2In
    (fun p' μ k => numD2In P p' (restMomentum P.m) μ k)
    (fun μ i j k => isLoopPoly_numD2In_out P _ μ i j k)
    (fun p' => ctLimitV .d2In P (restMomentum P.m) p')
    (fun u hu μ i j => QED.TwoLoop.ReflCovariance.ctLimitV_d2In_entry P hm hmγ hΛ
      (dot_restMomentum (m := P.m)) (dot_curveMomentum P.m hu)
      ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu) μ i j)

theorem tendsto_d2Out_explicit :
    Tendsto (fun u : ℝ =>
      (pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
          (ctLimitV .d2Out P (restMomentum P.m) (curveMomentum P.m u)) +
        pauliNum P.m (curveMomentum P.m (-u)) (restMomentum P.m)
          (ctLimitV .d2Out P (restMomentum P.m) (curveMomentum P.m (-u)))) / (2 * (u : ℂ) ^ 2))
      (𝓝[≠] 0) (𝓝 (d2OutZero P)) :=
  tendsto_kinds_explicit (by norm_num) kindsD2Out (massesD2In P) P hm (lt_min hmγ hΛ)
    (massesD2In_sq_of_ne_pho_out P) (min_sq_le_massesD2In_sq_out P hmγ hΛ)
    intNoSubdivergenceRefined_kindsD2Out
    (fun p' μ k => numD2Out P p' (restMomentum P.m) μ k)
    (fun μ i j k => isLoopPoly_numD2Out_out P _ μ i j k)
    (fun p' => ctLimitV .d2Out P (restMomentum P.m) p')
    (fun u hu μ i j => ctLimitV_d2Out_entry P hm hmγ hΛ
      (dot_restMomentum (m := P.m)) (dot_curveMomentum P.m hu)
      ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu) μ i j)

theorem tendsto_d3Slot0_explicit :
    Tendsto (fun u : ℝ =>
      (pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
          (ctLimitV .d3Slot0 P (restMomentum P.m) (curveMomentum P.m u)) +
        pauliNum P.m (curveMomentum P.m (-u)) (restMomentum P.m)
          (ctLimitV .d3Slot0 P (restMomentum P.m) (curveMomentum P.m (-u)))) /
            (2 * (u : ℂ) ^ 2))
      (𝓝[≠] 0) (𝓝 (d3Zero P)) :=
  tendsto_kinds_explicit (by norm_num) kindsD3 (massesD3 P) P hm (lt_min hmγ hΛ)
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

/-- The one-loop Pauli integral `B(0) = ∫ pauliIntegrand m (m_γ, Λ, 0)` at `q² = 0`. -/
noncomputable def oneLoopPauliZero (P : Params) : ℝ :=
  ∫ z, QED.OneLoop.VertexLimit.pauliIntegrand P.m (P.mγ, P.Λ, 0) z ∂QED.Integration.feynmanMeasure

/-- **The `q → 0` value of a `δ₁` class**: `i δ₁ e (4m²)³ (e²/(8π²)) B(0) / m`. -/
noncomputable def d1Zero (P : Params) : ℂ :=
  (P.δ₁ : ℂ) * I * ((P.e : ℂ) * (4 * (P.m : ℂ) ^ 2) ^ 3 *
    ((P.e ^ 2 / (8 * π ^ 2) * oneLoopPauliZero P : ℝ) : ℂ) / P.m)

/-- **The explicit second-order limit for a `δ₁` class.** -/
theorem tendsto_d1_explicit {c : CtClass} (hc : c = .d1At1 ∨ c = .d1At2 ∨ c = .d1At3)
    (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    Tendsto (fun u : ℝ =>
      (pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
          (ctLimitV c P (restMomentum P.m) (curveMomentum P.m u)) +
        pauliNum P.m (curveMomentum P.m (-u)) (restMomentum P.m)
          (ctLimitV c P (restMomentum P.m) (curveMomentum P.m (-u)))) / (2 * (u : ℂ) ^ 2))
      (𝓝[≠] 0) (𝓝 (d1Zero P)) := by
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
  have hΦ0 : Φ 0 = d1Zero P := by
    have h00 : (0 : ℝ) ^ 2 = 0 := by norm_num
    simp only [hΦ, d1Zero, oneLoopPauliZero, hg_def, curveQ, h00, mul_zero, sub_zero,
      div_one]
    push_cast
    ring
  rw [← hΦ0]
  refine (hΦc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
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

end QED.TwoLoop.PauliZeroExplicit

end
