/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellQBnd
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c): shell value and slope of the covariant self-energy with one dressed photon

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step b4. For the dressed photon
`R = R_T`, `U = T m²`, `a = seArg m s y` and `T₁ = quadTailVP m_γ² Λ² U`, the covariant
self-energy has the coefficients (up to a common constant)

`A(s) = -∫₀¹ ((4y - 2) Tail(a) + (y m² + y s - 3y² s) T₁(a)) dy`, `B(s) = 3 ∫₀¹ Tail(a) dy`.

* `hasDerivAt_covAU`, `hasDerivAt_covBU`: derivatives in `s` near the shell `s = -m²`, with
  integrands bounded by `covDerMax/(T m²)` (`abs_covADer_le`), `covDerMax` independent of `T`;
* `covAU_shell_value`: `covAU(-m²) + 3 covBU(-m²) = 2 seShellVal`;
* `covAU_shell_slope`: `-covAU(-m²) + 2m² covAU'(-m²) + 6m² covBU'(-m²) =
  -2 seShellSlope - Tail(0)`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCRegDisp

open QED.TwoLoop.UnitVPLink (photonVar)

/-- The integrand of `-A`: `(4y - 2) Tail(a) + (y m² + y s - 3y² s) T₁(a)`. -/
noncomputable def covAInt (m mγ Λ T s y : ℝ) : ℝ :=
  (4 * y - 2) * photonTail (vpPhotonT m mγ Λ T) (seArg m s y) +
    (y * m ^ 2 + y * s - 3 * y ^ 2 * s) * quadTailVP (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) (seArg m s y)

/-- The `s`-derivative of `covAInt`. -/
noncomputable def covADer (m mγ Λ T s y : ℝ) : ℝ :=
  (4 * y - 2) * (-vpPhotonT m mγ Λ T (seArg m s y) * y) +
    ((y - 3 * y ^ 2) * quadTailVP (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) (seArg m s y) +
      (y * m ^ 2 + y * s - 3 * y ^ 2 * s) *
        (-bubQ (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) (seArg m s y) * y))

/-- `-A` up to a constant. -/
noncomputable def covAU (m mγ Λ T s : ℝ) : ℝ := ∫ y in (0 : ℝ)..1, covAInt m mγ Λ T s y

/-- The derivative of `covAU`. -/
noncomputable def covAU' (m mγ Λ T s : ℝ) : ℝ := ∫ y in (0 : ℝ)..1, covADer m mγ Λ T s y

/-- `B/3` up to a constant. -/
noncomputable def covBU (m mγ Λ T s : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1, photonTail (vpPhotonT m mγ Λ T) (seArg m s y)

/-- The derivative of `covBU`. -/
noncomputable def covBU' (m mγ Λ T s : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1, -vpPhotonT m mγ Λ T (seArg m s y) * y

/-- The bound of the derivative integrand, independent of `T`. -/
noncomputable def covDerMax (m A B δ : ℝ) : ℝ :=
  2 * rMax A B + 2 * tMax A B + (m ^ 2 + 4 * (m ^ 2 + δ)) * qMax A B

/-- A measurable function bounded on `(0, 1)` is interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_unit_of_bound_Ioo {g : ℝ → ℝ} (hg : Measurable g) (C : ℝ)
    (hb : ∀ y ∈ Ioo (0 : ℝ) 1, ‖g y‖ ≤ C) : IntervalIntegrable g volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  exact Measure.integrableOn_of_bounded (M := C) (by simp) hg.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall hb))

theorem measurable_bubQ (A B U : ℝ) : Measurable (bubQ A B U) := by
  unfold bubQ
  fun_prop

theorem measurable_tail_seArg (m mγ Λ T s : ℝ) :
    Measurable fun y => photonTail (vpPhotonT m mγ Λ T) (seArg m s y) :=
  (measurable_photonTail_vp m mγ Λ).comp (measurable_const.prodMk (measurable_seArg m s))

theorem measurable_vp_seArg (m mγ Λ T s : ℝ) :
    Measurable fun y => vpPhotonT m mγ Λ T (seArg m s y) :=
  (measurable_vpPhotonT m mγ Λ).comp (measurable_const.prodMk (measurable_seArg m s))

theorem measurable_covAInt (m mγ Λ T s : ℝ) : Measurable (covAInt m mγ Λ T s) := by
  have h1 := measurable_tail_seArg m mγ Λ T s
  have h2 := (measurable_quadTailVP (mγ ^ 2) (Λ ^ 2) (T * m ^ 2)).comp (measurable_seArg m s)
  exact ((measurable_const.mul measurable_id).sub measurable_const).mul h1 |>.add
    ((((measurable_id.mul measurable_const).add (measurable_id.mul measurable_const)).sub
      ((measurable_const.mul (measurable_id.pow_const 2)).mul measurable_const)).mul h2)

theorem measurable_covADer (m mγ Λ T s : ℝ) : Measurable (covADer m mγ Λ T s) := by
  have h1 := measurable_vp_seArg m mγ Λ T s
  have h2 := (measurable_quadTailVP (mγ ^ 2) (Λ ^ 2) (T * m ^ 2)).comp (measurable_seArg m s)
  have h3 := (measurable_bubQ (mγ ^ 2) (Λ ^ 2) (T * m ^ 2)).comp (measurable_seArg m s)
  unfold covADer
  fun_prop

section Deriv

variable {m mγ Λ T δ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) (hδ : 0 < δ)
  (hδA : 2 * δ ≤ mγ ^ 2) (hδB : 2 * δ ≤ Λ ^ 2) (hδU : 2 * δ ≤ T * m ^ 2)
  (hab : mγ ^ 2 ≠ Λ ^ 2) (hac : mγ ^ 2 ≠ T * m ^ 2) (hbc : Λ ^ 2 ≠ T * m ^ 2)

include hm hmγ hΛ hT hδ hδA hδB hδU in
theorem hasDerivAt_tail_seArg {s y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (hs : -m ^ 2 - δ < s) :
    HasDerivAt (fun s => photonTail (vpPhotonT m mγ Λ T) (seArg m s y))
      (-vpPhotonT m mγ Λ T (seArg m s y) * y) s := by
  have hw := seArg_gt hδ hy hs
  have hle := le_vpMargin (m := m) (mγ := mγ) (Λ := Λ) (T := T) hδA hδB hδU
  exact (hasDerivAt_photonTail_vp hmγ hΛ hT hm (by linarith)).comp s
    (hasDerivAt_seArg m hy.2.ne s)

include hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc in
theorem hasDerivAt_covAInt {s y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (hs : -m ^ 2 - δ < s) :
    HasDerivAt (fun s => covAInt m mγ Λ T s y) (covADer m mγ Λ T s y) s := by
  have hw := seArg_gt hδ hy hs
  have ht := hasDerivAt_tail_seArg hm hmγ hΛ hT hδ hδA hδB hδU hy hs
  have hQ := (hasDerivAt_quadTailVP hab hac hbc (by linarith) (by linarith)
    (by linarith)).comp s (hasDerivAt_seArg m hy.2.ne s)
  have hc : HasDerivAt (fun s => y * m ^ 2 + y * s - 3 * y ^ 2 * s) (y - 3 * y ^ 2) s := by
    have h := (((hasDerivAt_id s).const_mul y).const_add (y * m ^ 2)).sub
      ((hasDerivAt_id s).const_mul (3 * y ^ 2))
    convert h using 1
    · funext v
      simp only [Pi.sub_apply, id]
    · ring
  have h := (ht.const_mul (4 * y - 2)).add (hc.mul hQ)
  convert h using 1
  · funext v
    simp only [covAInt, Pi.add_apply, Pi.mul_apply, Function.comp]
  · simp only [covADer, Function.comp]

include hm hδ hδA hδB hδU hab hac hbc in
/-- **The derivative integrand is bounded independently of `T`.** -/
theorem abs_covADer_le {s y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (hs1 : -m ^ 2 - δ < s)
    (hs2 : s < -m ^ 2 + δ) :
    |covADer m mγ Λ T s y| ≤ covDerMax m (mγ ^ 2) (Λ ^ 2) δ / (T * m ^ 2) := by
  have hw := (seArg_gt hδ hy hs1).le
  set w := seArg m s y
  have bR : |vpPhotonT m mγ Λ T w| ≤ (rMax (mγ ^ 2) (Λ ^ 2) / (T * m ^ 2)) := by
    rw [vpPhotonT_eq_mul_bubQ]
    exact abs_mul_bubQ_le_rMax hδ hδA hδB hδU hw
  have bT := abs_quadTailVP_le_tMax hδ hδA hδB hδU hab hac hbc hw
  have bQ := abs_bubQ_le_qMax hδ hδA hδB hδU hw
  obtain ⟨hy0, hy1⟩ := hy
  have a1 : |4 * y - 2| ≤ 2 := abs_le.2 ⟨by linarith, by linarith⟩
  have a2 : |y| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have a3 : |y - 3 * y ^ 2| ≤ 2 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have hsa : |s| ≤ m ^ 2 + δ := abs_le.2 ⟨by linarith, by nlinarith [sq_nonneg m]⟩
  have a4 : |y * m ^ 2 + y * s - 3 * y ^ 2 * s| ≤ m ^ 2 + 4 * (m ^ 2 + δ) := by
    have e : y * m ^ 2 + y * s - 3 * y ^ 2 * s = y * m ^ 2 + (y - 3 * y ^ 2) * s := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg m)]
    have h1 : |y| * m ^ 2 ≤ 1 * m ^ 2 := mul_le_mul_of_nonneg_right a2 (sq_nonneg m)
    have h2 : |y - 3 * y ^ 2| * |s| ≤ 2 * (m ^ 2 + δ) :=
      mul_le_mul a3 hsa (abs_nonneg _) (by norm_num)
    nlinarith
  have hr0 : 0 ≤ (rMax (mγ ^ 2) (Λ ^ 2) / (T * m ^ 2)) := (abs_nonneg _).trans bR
  have hq0 : 0 ≤ (qMax (mγ ^ 2) (Λ ^ 2) / (T * m ^ 2)) := (abs_nonneg _).trans bQ
  unfold covADer covDerMax
  refine (abs_add_le _ _).trans ?_
  have e1 : |(4 * y - 2) * (-vpPhotonT m mγ Λ T w * y)| ≤
      2 * (rMax (mγ ^ 2) (Λ ^ 2) / (T * m ^ 2)) := by
    rw [abs_mul, abs_mul, abs_neg]
    calc |4 * y - 2| * (|vpPhotonT m mγ Λ T w| * |y|) ≤
        2 * ((rMax (mγ ^ 2) (Λ ^ 2) / (T * m ^ 2)) * 1) :=
          mul_le_mul a1 (mul_le_mul bR a2 (abs_nonneg _) hr0) (by positivity) (by norm_num)
      _ = _ := by ring
  have e2 : |(y - 3 * y ^ 2) * quadTailVP (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) w| ≤
      2 * (tMax (mγ ^ 2) (Λ ^ 2) / (T * m ^ 2)) := by
    rw [abs_mul]
    exact mul_le_mul a3 bT (abs_nonneg _) (by norm_num)
  have e3 : |(y * m ^ 2 + y * s - 3 * y ^ 2 * s) *
      (-bubQ (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) w * y)| ≤
      (m ^ 2 + 4 * (m ^ 2 + δ)) * (qMax (mγ ^ 2) (Λ ^ 2) / (T * m ^ 2)) := by
    rw [abs_mul, abs_mul, abs_neg]
    calc |y * m ^ 2 + y * s - 3 * y ^ 2 * s| * (|bubQ (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) w| * |y|)
        ≤ (m ^ 2 + 4 * (m ^ 2 + δ)) * ((qMax (mγ ^ 2) (Λ ^ 2) / (T * m ^ 2)) * 1) :=
          mul_le_mul a4 (mul_le_mul bQ a2 (abs_nonneg _) hq0) (by positivity) (by positivity)
      _ = _ := by ring
  have e23 := (abs_add_le _ _).trans (add_le_add e2 e3)
  have ediv : (2 * rMax (mγ ^ 2) (Λ ^ 2) + 2 * tMax (mγ ^ 2) (Λ ^ 2) +
      (m ^ 2 + 4 * (m ^ 2 + δ)) * qMax (mγ ^ 2) (Λ ^ 2)) / (T * m ^ 2) =
      2 * (rMax (mγ ^ 2) (Λ ^ 2) / (T * m ^ 2)) + 2 * (tMax (mγ ^ 2) (Λ ^ 2) / (T * m ^ 2)) +
      (m ^ 2 + 4 * (m ^ 2 + δ)) * (qMax (mγ ^ 2) (Λ ^ 2) / (T * m ^ 2)) := by ring
  rw [ediv]
  linarith

include hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc in
theorem abs_covAInt_le {s y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (hs1 : -m ^ 2 - δ < s)
    (hs2 : s < -m ^ 2 + δ) : |covAInt m mγ Λ T s y| ≤
      2 * (bubKQ (mγ ^ 2) (Λ ^ 2) / (T * m ^ 2)) +
        (m ^ 2 + 4 * (m ^ 2 + δ)) * (tMax (mγ ^ 2) (Λ ^ 2) / (T * m ^ 2)) := by
  have hw := (seArg_gt hδ hy hs1).le
  set w := seArg m s y
  obtain ⟨t0, t1⟩ := photonTail_vp_mem_Icc hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc hw
  have bT := abs_quadTailVP_le_tMax hδ hδA hδB hδU hab hac hbc hw
  obtain ⟨hy0, hy1⟩ := hy
  have a1 : |4 * y - 2| ≤ 2 := abs_le.2 ⟨by linarith, by linarith⟩
  have a2 : |y| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have a3 : |y - 3 * y ^ 2| ≤ 2 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have hsa : |s| ≤ m ^ 2 + δ := abs_le.2 ⟨by linarith, by nlinarith [sq_nonneg m]⟩
  have a4 : |y * m ^ 2 + y * s - 3 * y ^ 2 * s| ≤ m ^ 2 + 4 * (m ^ 2 + δ) := by
    have e : y * m ^ 2 + y * s - 3 * y ^ 2 * s = y * m ^ 2 + (y - 3 * y ^ 2) * s := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg m)]
    have h1 : |y| * m ^ 2 ≤ 1 * m ^ 2 := mul_le_mul_of_nonneg_right a2 (sq_nonneg m)
    have h2 : |y - 3 * y ^ 2| * |s| ≤ 2 * (m ^ 2 + δ) :=
      mul_le_mul a3 hsa (abs_nonneg _) (by norm_num)
    nlinarith
  unfold covAInt
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg t0]
    exact mul_le_mul a1 t1 t0 (by norm_num)
  · rw [abs_mul]
    exact mul_le_mul a4 bT (abs_nonneg _) (by positivity)

include hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc in
theorem intervalIntegrable_covAInt {s : ℝ} (hs1 : -m ^ 2 - δ < s) (hs2 : s < -m ^ 2 + δ) :
    IntervalIntegrable (covAInt m mγ Λ T s) volume 0 1 :=
  intervalIntegrable_unit_of_bound_Ioo (measurable_covAInt m mγ Λ T s) _ fun _ hy =>
    (Real.norm_eq_abs _).trans_le
      (abs_covAInt_le hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc hy hs1 hs2)

include hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc in
theorem intervalIntegrable_tail_seArg {s : ℝ} (hs1 : -m ^ 2 - δ < s) :
    IntervalIntegrable (fun y => photonTail (vpPhotonT m mγ Λ T) (seArg m s y)) volume 0 1 :=
  intervalIntegrable_unit_of_bound_Ioo (measurable_tail_seArg m mγ Λ T s) _ fun y hy => by
    obtain ⟨t0, t1⟩ := photonTail_vp_mem_Icc hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc
      (seArg_gt hδ hy hs1).le
    rw [Real.norm_of_nonneg t0]
    exact t1

include hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc in
/-- **Differentiation of `covAU` under `∫₀¹ dy`** near the shell. -/
theorem hasDerivAt_covAU {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (-m ^ 2 - δ) (-m ^ 2 + δ)) :
    IntervalIntegrable (covADer m mγ Λ T s₀) volume 0 1 ∧
      HasDerivAt (covAU m mγ Λ T) (covAU' m mγ Λ T s₀) s₀ := by
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (bound := fun _ => covDerMax m (mγ ^ 2) (Λ ^ 2) δ / (T * m ^ 2))
    (F := fun s y => covAInt m mγ Λ T s y) (F' := fun s y => covADer m mγ Λ T s y)
    (x₀ := s₀) (s := Ioo (-m ^ 2 - δ) (-m ^ 2 + δ)) (isOpen_Ioo.mem_nhds hs₀)
    (Eventually.of_forall fun s => (measurable_covAInt m mγ Λ T s).aestronglyMeasurable)
    (intervalIntegrable_covAInt hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc hs₀.1 hs₀.2)
    (measurable_covADer m mγ Λ T s₀).aestronglyMeasurable
    (by
      filter_upwards [Measure.ae_ne volume (1 : ℝ)] with y hy1 hy s hs
      rw [uIoc_of_le zero_le_one] at hy
      exact (Real.norm_eq_abs _).trans_le (abs_covADer_le hm hδ hδA hδB hδU hab hac hbc
        ⟨hy.1, lt_of_le_of_ne hy.2 hy1⟩ hs.1 hs.2))
    intervalIntegrable_const
    (by
      filter_upwards [Measure.ae_ne volume (1 : ℝ)] with y hy1 hy s hs
      rw [uIoc_of_le zero_le_one] at hy
      exact hasDerivAt_covAInt hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc
        ⟨hy.1, lt_of_le_of_ne hy.2 hy1⟩ hs.1)
  exact key

include hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc in
/-- **Differentiation of `covBU` under `∫₀¹ dy`** near the shell. -/
theorem hasDerivAt_covBU {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (-m ^ 2 - δ) (-m ^ 2 + δ)) :
    IntervalIntegrable (fun y => -vpPhotonT m mγ Λ T (seArg m s₀ y) * y) volume 0 1 ∧
      HasDerivAt (covBU m mγ Λ T) (covBU' m mγ Λ T s₀) s₀ := by
  have bR : ∀ s y, y ∈ Ioo (0 : ℝ) 1 → -m ^ 2 - δ < s →
      ‖-vpPhotonT m mγ Λ T (seArg m s y) * y‖ ≤ (rMax (mγ ^ 2) (Λ ^ 2) / (T * m ^ 2)) := by
    intro s y hy hs
    have hw := (seArg_gt hδ hy hs).le
    have h := abs_mul_bubQ_le_rMax hδ hδA hδB hδU hw (U := T * m ^ 2)
    rw [← vpPhotonT_eq_mul_bubQ] at h
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hy.1]
    exact (mul_le_of_le_one_right (abs_nonneg _) hy.2.le).trans h
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 1) (bound := fun _ => (rMax (mγ ^ 2) (Λ ^ 2) / (T * m ^ 2)))
    (F := fun s y => photonTail (vpPhotonT m mγ Λ T) (seArg m s y))
    (F' := fun s y => -vpPhotonT m mγ Λ T (seArg m s y) * y)
    (x₀ := s₀) (s := Ioo (-m ^ 2 - δ) (-m ^ 2 + δ)) (isOpen_Ioo.mem_nhds hs₀)
    (Eventually.of_forall fun s => (measurable_tail_seArg m mγ Λ T s).aestronglyMeasurable)
    (intervalIntegrable_tail_seArg hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc hs₀.1)
    ((measurable_vp_seArg m mγ Λ T s₀).neg.mul measurable_id).aestronglyMeasurable
    (by
      filter_upwards [Measure.ae_ne volume (1 : ℝ)] with y hy1 hy s hs
      rw [uIoc_of_le zero_le_one] at hy
      exact bR s y ⟨hy.1, lt_of_le_of_ne hy.2 hy1⟩ hs.1)
    intervalIntegrable_const
    (by
      filter_upwards [Measure.ae_ne volume (1 : ℝ)] with y hy1 hy s hs
      rw [uIoc_of_le zero_le_one] at hy
      exact hasDerivAt_tail_seArg hm hmγ hΛ hT hδ hδA hδB hδU
        ⟨hy.1, lt_of_le_of_ne hy.2 hy1⟩ hs.1)
  exact key

/-! ### The shell value and slope -/

include hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc in
/-- **The shell value**: `covAU(-m²) + 3 covBU(-m²) = 2 ∫₀¹ (1 + y) Tail(a₀) dy`. -/
theorem covAU_shell_value :
    covAU m mγ Λ T (-m ^ 2) + 3 * covBU m mγ Λ T (-m ^ 2) =
      2 * seShellVal (vpPhotonT m mγ Λ T) m := by
  have hs1 : -m ^ 2 - δ < -m ^ 2 := by linarith
  have hs2 : -m ^ 2 < -m ^ 2 + δ := by linarith
  have hA := intervalIntegrable_covAInt hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc hs1 hs2
  have hB := intervalIntegrable_tail_seArg hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc hs1
  have hV := intervalIntegrable_tail_shellArg hm hmγ hΛ hT (c := fun y => 1 + y)
    (by fun_prop) two_pos fun y hy => by
      rw [Real.norm_of_nonneg (by linarith [hy.1])]
      linarith [hy.2]
  have hY0t := intervalIntegrable_tail_shellArg hm hmγ hΛ hT (c := fun y => 2 * y - 1)
    (by fun_prop) one_pos fun y hy => by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hy.1, hy.2]
  have hY0q := intervalIntegrable_quad_shellArg hm hmγ hΛ hT hab hac hbc
    (c := fun y => 3 * m ^ 2 * y ^ 2) (by fun_prop) (K := 3 * m ^ 2) fun y hy => by
      rw [Real.norm_of_nonneg (by positivity)]
      have : y ^ 2 ≤ 1 := pow_le_one₀ hy.1.le hy.2
      nlinarith [sq_nonneg m]
  have h0 := shell_yId₀ hm hmγ hΛ hT hab hac hbc
  rw [intervalIntegral.integral_add hY0t hY0q] at h0
  unfold covAU covBU seShellVal
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add hA (hB.const_mul 3)]
  have e : ∫ y in (0 : ℝ)..1, (covAInt m mγ Λ T (-m ^ 2) y +
      3 * photonTail (vpPhotonT m mγ Λ T) (seArg m (-m ^ 2) y)) =
      ∫ y in (0 : ℝ)..1, ((2 * y - 1) * photonTail (vpPhotonT m mγ Λ T) (shellArg m y) +
        3 * m ^ 2 * y ^ 2 * quadTailVP (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) (shellArg m y) +
        2 * ((1 + y) * photonTail (vpPhotonT m mγ Λ T) (shellArg m y))) := by
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [covAInt, seArg_shell]
    ring
  rw [e, intervalIntegral.integral_add (hY0t.add hY0q) (hV.const_mul 2),
    intervalIntegral.integral_add hY0t hY0q, h0, zero_add]

include hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc in
/-- **The shell slope**: `-covAU(-m²) + 2m² covAU'(-m²) + 6m² covBU'(-m²) =
-2 seShellSlope - Tail(0)`. -/
theorem covAU_shell_slope :
    -covAU m mγ Λ T (-m ^ 2) + 2 * m ^ 2 * covAU' m mγ Λ T (-m ^ 2) +
      6 * m ^ 2 * covBU' m mγ Λ T (-m ^ 2) =
      -2 * seShellSlope (vpPhotonT m mγ Λ T) m - photonTail (vpPhotonT m mγ Λ T) 0 := by
  have hs1 : -m ^ 2 - δ < -m ^ 2 := by linarith
  have hs2 : -m ^ 2 < -m ^ 2 + δ := by linarith
  have ha := intervalIntegrable_covAInt hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc hs1 hs2
  have hb := (hasDerivAt_covAU hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc ⟨hs1, hs2⟩).1
  have hc := (hasDerivAt_covBU hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc ⟨hs1, hs2⟩).1
  have hd1 := intervalIntegrable_vp_shellArg hm hmγ hΛ hT
    (c := fun x => 2 * m ^ 2 * x * (1 + x)) (by fun_prop) (K := 4 * m ^ 2) fun y hy => by
      rw [Real.norm_of_nonneg (by have := hy.1; positivity)]
      have : y * (1 + y) ≤ 2 := by nlinarith [hy.1, hy.2]
      nlinarith [sq_nonneg m]
  have hd2 := intervalIntegrable_tail_shellArg hm hmγ hΛ hT (c := fun x => 1 - x)
    (by fun_prop) one_pos fun y hy => by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hy.1, hy.2]
  have hd := hd1.sub hd2
  have he1 := intervalIntegrable_tail_shellArg hm hmγ hΛ hT (c := fun _ => 1)
    measurable_const one_pos fun y hy => by simp
  have he2 := intervalIntegrable_vp_shellArg hm hmγ hΛ hT
    (c := fun y => m ^ 2 * (4 * y - 2 * y ^ 2)) (by fun_prop) (K := 4 * m ^ 2) fun y hy => by
      have e1 : 0 ≤ 4 * y - 2 * y ^ 2 := by nlinarith [hy.1, hy.2]
      have e2 : 4 * y - 2 * y ^ 2 ≤ 4 := by nlinarith [hy.1, hy.2]
      have f1 := mul_le_mul_of_nonneg_left e2 (sq_nonneg m)
      have f0 := mul_nonneg (sq_nonneg m) e1
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith
  have he3 := intervalIntegrable_quad_shellArg hm hmγ hΛ hT hab hac hbc
    (c := fun y => 2 * m ^ 2 * (3 * y ^ 2 - y)) (by fun_prop) (K := 4 * m ^ 2) fun y hy => by
      have e1 : -1 ≤ 3 * y ^ 2 - y := by nlinarith [hy.1, hy.2]
      have e2 : 3 * y ^ 2 - y ≤ 2 := by nlinarith [hy.1, hy.2]
      have f1 := mul_le_mul_of_nonneg_left e2 (sq_nonneg m)
      have f2 := mul_le_mul_of_nonneg_left e1 (sq_nonneg m)
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith
  have he : IntervalIntegrable (fun y => photonTail (vpPhotonT m mγ Λ T) (shellArg m y) +
      m ^ 2 * (4 * y - 2 * y ^ 2) * vpPhotonT m mγ Λ T (shellArg m y) +
      2 * m ^ 2 * (3 * y ^ 2 - y) * quadTailVP (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) (shellArg m y))
      volume 0 1 := ((he1.add he2).add he3).congr fun y _ => by simp
  have hf0 := intervalIntegrable_tail_shellArg hm hmγ hΛ hT (c := fun y => 2 * y - 1)
    (by fun_prop) one_pos fun y hy => by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hy.1, hy.2]
  have hf1 := intervalIntegrable_quad_shellArg hm hmγ hΛ hT hab hac hbc
    (c := fun y => 3 * m ^ 2 * y ^ 2) (by fun_prop) (K := 3 * m ^ 2) fun y hy => by
      rw [Real.norm_of_nonneg (by positivity)]
      have : y ^ 2 ≤ 1 := pow_le_one₀ hy.1.le hy.2
      nlinarith [sq_nonneg m]
  have hf := hf0.add hf1
  have Ie := shell_yId₁ hm hmγ hΛ hT hab hac hbc
  have If := shell_yId₀ hm hmγ hΛ hT hab hac hbc
  set a := covAInt m mγ Λ T (-m ^ 2) with hadef
  set b := covADer m mγ Λ T (-m ^ 2) with hbdef
  set c : ℝ → ℝ := fun y => -vpPhotonT m mγ Λ T (seArg m (-m ^ 2) y) * y with hcdef
  set d : ℝ → ℝ := fun x => 2 * m ^ 2 * x * (1 + x) * vpPhotonT m mγ Λ T (shellArg m x) -
    (1 - x) * photonTail (vpPhotonT m mγ Λ T) (shellArg m x) with hddef
  set e : ℝ → ℝ := fun y => photonTail (vpPhotonT m mγ Λ T) (shellArg m y) +
      m ^ 2 * (4 * y - 2 * y ^ 2) * vpPhotonT m mγ Λ T (shellArg m y) +
      2 * m ^ 2 * (3 * y ^ 2 - y) * quadTailVP (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) (shellArg m y)
    with hedef
  set f : ℝ → ℝ := fun y => (2 * y - 1) * photonTail (vpPhotonT m mγ Λ T) (shellArg m y) +
      3 * m ^ 2 * y ^ 2 * quadTailVP (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) (shellArg m y) with hfdef
  have p1 : IntervalIntegrable (fun y => -a y + 2 * m ^ 2 * b y) volume 0 1 :=
    ha.neg.add (hb.const_mul _)
  have p2 : IntervalIntegrable (fun y => -a y + 2 * m ^ 2 * b y + 6 * m ^ 2 * c y)
    volume 0 1 := p1.add (hc.const_mul _)
  have p3 : IntervalIntegrable (fun y => -a y + 2 * m ^ 2 * b y + 6 * m ^ 2 * c y + 2 * d y)
    volume 0 1 := p2.add (hd.const_mul _)
  have p4 : IntervalIntegrable
    (fun y => -a y + 2 * m ^ 2 * b y + 6 * m ^ 2 * c y + 2 * d y + e y) volume 0 1 :=
    p3.add he
  have lin : ∫ y in (0 : ℝ)..1,
      (-a y + 2 * m ^ 2 * b y + 6 * m ^ 2 * c y + 2 * d y + e y + f y) =
      -(∫ y in (0 : ℝ)..1, a y) + 2 * m ^ 2 * (∫ y in (0 : ℝ)..1, b y) +
        6 * m ^ 2 * (∫ y in (0 : ℝ)..1, c y) + 2 * (∫ y in (0 : ℝ)..1, d y) +
        (∫ y in (0 : ℝ)..1, e y) + ∫ y in (0 : ℝ)..1, f y := by
    rw [intervalIntegral.integral_add p4 hf, intervalIntegral.integral_add p3 he,
      intervalIntegral.integral_add p2 (hd.const_mul _),
      intervalIntegral.integral_add p1 (hc.const_mul _),
      intervalIntegral.integral_add (f := fun y => -a y) ha.neg (hb.const_mul _),
      intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have zero : ∫ y in (0 : ℝ)..1,
      (-a y + 2 * m ^ 2 * b y + 6 * m ^ 2 * c y + 2 * d y + e y + f y) = 0 := by
    refine (intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_).trans
      intervalIntegral.integral_zero
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with y hy1 _
    have h1 : (1 : ℝ) - y ≠ 0 := sub_ne_zero.2 (Ne.symm hy1)
    simp only [hadef, hbdef, hcdef, hddef, hedef, hfdef, covAInt, covADer, seArg_shell,
      vpPhotonT_eq_mul_bubQ]
    generalize photonTail (vpPhotonT m mγ Λ T) (shellArg m y) = t
    generalize quadTailVP (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) (shellArg m y) = u
    generalize bubQ (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) (shellArg m y) = q
    simp only [shellArg, photonVar]
    field_simp
    ring
  rw [lin] at zero
  unfold covAU covAU' covBU' seShellSlope
  change -(∫ y in (0 : ℝ)..1, a y) + 2 * m ^ 2 * (∫ y in (0 : ℝ)..1, b y) +
      6 * m ^ 2 * (∫ y in (0 : ℝ)..1, c y) = -2 * (∫ y in (0 : ℝ)..1, d y) -
      photonTail (vpPhotonT m mγ Λ T) 0
  have Ie' : ∫ y in (0 : ℝ)..1, e y = photonTail (vpPhotonT m mγ Λ T) 0 := Ie
  have If' : ∫ y in (0 : ℝ)..1, f y = 0 := If
  linarith

end Deriv

end QED.ChainProof.SetCRegDisp

end
