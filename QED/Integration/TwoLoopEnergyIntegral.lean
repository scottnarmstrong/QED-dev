/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The signed two-loop energy integral

After Feynman parametrization at two loops, the inner integral over the two loop energies
`t = (t₁, t₂)` at fixed spatial momenta has the form `∫_{ℝ²} (-tᵀ A t + w)^{-n} dt`, with `A`
the positive definite matrix `(U_{st})` of Feynman parameters and `Im w < 0`
(`docs/TWO-LOOP-DERIVATION.md`, section 4.3; obligation O2-10). The integral is elementary, with
integer powers and no branch choice:
`∫_{ℝ²} (-tᵀ A t + w)^{-n} dt = -(π/(n-1)) (det A)^{-1/2} w^{1-n}` for `n ≥ 2`.

The proof passes to polar coordinates for `A = 1`, where the radial integral has the
antiderivative `(w - r²)^{1-n} / (2(n-1))` (`w - r² ≠ 0` because `Im w < 0`), and reduces a
general `A` to `A = 1` by the linear change of variables `s = M t`, with `M` the explicit
upper-triangular Cholesky factor of `A`, of determinant `√(det A)`.

The integrals are Bochner integrals for Lebesgue measure (`volume`) on `Fin 2 → ℝ`, the measure
the joint energy-first integral (T₉) `QED.TwoLoop.jointEnergyFirstIntegral` uses for `L = 2`, and
the integrand is absolutely integrable there.

## Main statements

* `QED.Integration.TwoLoop.integral_Ioi_mul_inv_neg_sq_add_pow`: the radial integral
  `∫₀^∞ r (w - r²)^{-n} dr = -w^{1-n} / (2(n-1))`.
* `QED.Integration.TwoLoop.integral_inv_neg_sumSq_add_pow`: the case `A = 1` on `Fin 2 → ℝ`.
* `QED.Integration.TwoLoop.integrable_inv_neg_quadratic_add_pow` and
  `QED.Integration.TwoLoop.integral_inv_neg_quadratic_add_pow`: integrability and the formula
  for a positive definite `A`.
-/

public section

open Complex MeasureTheory Filter Topology Set Matrix
open scoped Real

namespace QED.Integration.TwoLoop

variable {w : ℂ}

/-! ### The lower bound `‖w - s‖ ≥ c (1 + s)` -/

/-- If `Im w < 0`, then `‖w - s‖ ≥ c (1 + s)` uniformly for real `s ≥ 0`. -/
theorem exists_lower_bound_neg_add (hw : w.im < 0) :
    ∃ c > 0, ∀ s : ℝ, 0 ≤ s → c * (1 + s) ≤ ‖-(s : ℂ) + w‖ := by
  set η := -w.im with hη
  have hηpos : 0 < η := by linarith
  set R := |w.re| with hR
  have hRnn : 0 ≤ R := abs_nonneg _
  refine ⟨η / (1 + R + η), by positivity, fun s hs => ?_⟩
  set N := ‖-(s : ℂ) + w‖ with hN
  have hA : η ≤ N := by
    have := abs_im_le_norm (-(s : ℂ) + w)
    simp only [add_im, neg_im, ofReal_im, neg_zero, zero_add] at this
    rw [abs_of_neg hw] at this
    linarith
  have hB : s - R ≤ N := by
    have h1 := abs_re_le_norm (-(s : ℂ) + w)
    simp only [add_re, neg_re, ofReal_re] at h1
    have h2 := neg_abs_le (-s + w.re)
    have h3 := le_abs_self w.re
    linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hA) (by linarith : (0 : ℝ) ≤ 1 + R),
    mul_nonneg hηpos.le (sub_nonneg.mpr hB)]

/-- `-s + w ≠ 0` for real `s` when `Im w < 0`. -/
theorem neg_ofReal_add_ne_zero (hw : w.im < 0) (s : ℝ) : -(s : ℂ) + w ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [add_im, neg_im, ofReal_im, neg_zero, zero_add, zero_im] at this
  linarith

/-- The bound `‖(-s + w)^{-n}‖ ≤ c^{-n} (1 + s)^{-n}` for `s ≥ 0`. -/
theorem norm_inv_neg_add_pow_le {c : ℝ} (hc : 0 < c)
    (h : ∀ s : ℝ, 0 ≤ s → c * (1 + s) ≤ ‖-(s : ℂ) + w‖) (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ‖((-(s : ℂ) + w) ^ n)⁻¹‖ ≤ (c ^ n)⁻¹ * ((1 + s) ^ n)⁻¹ := by
  rw [norm_inv, norm_pow, ← mul_inv, ← mul_pow]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (h s hs) n)

/-! ### The radial integral -/

/-- The radial integrand `r (w - r²)^{-n}` is integrable on `ℝ` for `n ≥ 2`. -/
theorem integrable_mul_inv_neg_sq_add_pow (hw : w.im < 0) {n : ℕ} (hn : 2 ≤ n) :
    Integrable fun r : ℝ => (r : ℂ) * ((-((r ^ 2 : ℝ) : ℂ) + w) ^ n)⁻¹ := by
  obtain ⟨c, hc, hbd⟩ := exists_lower_bound_neg_add hw
  refine (integrable_inv_one_add_sq.const_mul (c ^ n)⁻¹).mono' ?_ (Eventually.of_forall ?_)
  · refine Continuous.aestronglyMeasurable ?_
    refine continuous_ofReal.mul (Continuous.inv₀ (by fun_prop) fun r => ?_)
    exact pow_ne_zero _ (neg_ofReal_add_ne_zero hw _)
  · intro r
    have h0 : 0 ≤ r ^ 2 := sq_nonneg r
    have h1 : 1 ≤ 1 + r ^ 2 := by linarith
    have hr : |r| ≤ 1 + r ^ 2 := by nlinarith [sq_abs r, abs_nonneg r]
    rw [norm_mul, norm_real, Real.norm_eq_abs]
    calc |r| * ‖((-((r ^ 2 : ℝ) : ℂ) + w) ^ n)⁻¹‖
        ≤ (1 + r ^ 2) * ((c ^ n)⁻¹ * ((1 + r ^ 2) ^ n)⁻¹) :=
          mul_le_mul hr (norm_inv_neg_add_pow_le hc hbd n h0) (norm_nonneg _) (by positivity)
      _ = (c ^ n)⁻¹ * ((1 + r ^ 2) ^ (n - 1))⁻¹ := by
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          rw [Nat.add_sub_cancel]
          field_simp
          ring
      _ ≤ (c ^ n)⁻¹ * (1 + r ^ 2)⁻¹ := by
          gcongr
          exact le_self_pow₀ h1 (by omega)

/-- **The radial integral.** For `Im w < 0` and `n ≥ 2`,
`∫₀^∞ r (w - r²)^{-n} dr = -w^{1-n} / (2(n-1))`. -/
theorem integral_Ioi_mul_inv_neg_sq_add_pow (hw : w.im < 0) {n : ℕ} (hn : 2 ≤ n) :
    ∫ r in Ioi (0 : ℝ), (r : ℂ) * ((-((r ^ 2 : ℝ) : ℂ) + w) ^ n)⁻¹ =
      -(1 / (2 * ((n : ℂ) - 1))) * (w ^ (n - 1))⁻¹ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hsub : m + 2 - 1 = m + 1 := by omega
  rw [hsub]
  set D : ℝ → ℂ := fun r => -((r ^ 2 : ℝ) : ℂ) + w with hD
  have hDne : ∀ r, D r ≠ 0 := fun r => neg_ofReal_add_ne_zero hw _
  have hk : (2 * (((m + 2 : ℕ) : ℂ) - 1)) ≠ 0 := by
    push_cast
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  set G : ℝ → ℂ := fun r => (D r ^ (m + 1))⁻¹ / (2 * (((m + 2 : ℕ) : ℂ) - 1)) with hG
  have hderiv : ∀ r ∈ Ici (0 : ℝ), HasDerivAt G ((r : ℂ) * (D r ^ (m + 2))⁻¹) r := by
    intro r _
    have h1 : HasDerivAt D (-(((2 : ℕ) * r ^ (2 - 1) : ℝ) : ℂ)) r :=
      ((hasDerivAt_pow 2 r).ofReal_comp).neg.add_const w
    have h2 := ((h1.fun_pow (m + 1)).fun_inv (pow_ne_zero _ (hDne r))).div_const
      (2 * (((m + 2 : ℕ) : ℂ) - 1))
    convert h2 using 1
    have hr := hDne r
    have hm1 : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    have hm2 : ((m + 2 : ℕ) : ℂ) - 1 = (m : ℂ) + 1 := by push_cast; ring
    simp only [Nat.add_sub_cancel, hm2]
    push_cast
    field_simp
    ring
  have hlim : Tendsto G atTop (𝓝 0) := by
    obtain ⟨c, hc, hbd⟩ := exists_lower_bound_neg_add hw
    have hnorm : Tendsto (fun r => ‖D r‖) atTop atTop := by
      refine tendsto_atTop_mono' _ ?_ ((tendsto_pow_atTop (two_ne_zero)).const_mul_atTop hc)
      filter_upwards with r
      have := hbd (r ^ 2) (sq_nonneg r)
      nlinarith
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := ((tendsto_pow_atTop (Nat.succ_ne_zero m)).comp hnorm).inv_tendsto_atTop.div_const
      ‖2 * (((m + 2 : ℕ) : ℂ) - 1)‖
    rw [zero_div] at this
    refine this.congr fun r => ?_
    simp only [hG, Function.comp_apply, Pi.inv_apply, norm_div, norm_inv, norm_pow]
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (integrable_mul_inv_neg_sq_add_pow hw (by omega)).integrableOn hlim]
  simp only [hG, hD, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ofReal_zero,
    neg_zero, zero_add]
  ring

/-! ### The case `A = 1` -/

/-- The integrand `(w - x² - y²)^{-n}` is integrable on `ℝ × ℝ` for `n ≥ 2`. -/
theorem integrable_prod_inv_neg_sumSq_add_pow (hw : w.im < 0) {n : ℕ} (hn : 2 ≤ n) :
    Integrable fun p : ℝ × ℝ => ((-((p.1 ^ 2 + p.2 ^ 2 : ℝ) : ℂ) + w) ^ n)⁻¹ := by
  obtain ⟨c, hc, hbd⟩ := exists_lower_bound_neg_add hw
  refine (((integrable_inv_one_add_sq.mul_prod integrable_inv_one_add_sq)).const_mul
    (c ^ n)⁻¹).mono' ?_ (Eventually.of_forall ?_)
  · refine Continuous.aestronglyMeasurable (Continuous.inv₀ (by fun_prop) fun p => ?_)
    exact pow_ne_zero _ (neg_ofReal_add_ne_zero hw _)
  · intro p
    have h1 : 0 ≤ p.1 ^ 2 := sq_nonneg _
    have h2 : 0 ≤ p.2 ^ 2 := sq_nonneg _
    refine (norm_inv_neg_add_pow_le hc hbd n (by positivity)).trans ?_
    gcongr
    calc ((1 + (p.1 ^ 2 + p.2 ^ 2)) ^ n)⁻¹ ≤ ((1 + (p.1 ^ 2 + p.2 ^ 2)) ^ 2)⁻¹ := by
          gcongr
          · linarith
      _ ≤ (1 + p.1 ^ 2)⁻¹ * (1 + p.2 ^ 2)⁻¹ := by
          rw [← mul_inv]
          gcongr
          nlinarith [mul_nonneg h1 h2]

/-- **The case `A = 1` on `ℝ × ℝ`.** For `Im w < 0` and `n ≥ 2`,
`∫_{ℝ²} (w - x² - y²)^{-n} = -(π/(n-1)) w^{1-n}`. -/
theorem integral_prod_inv_neg_sumSq_add_pow (hw : w.im < 0) {n : ℕ} (hn : 2 ≤ n) :
    ∫ p : ℝ × ℝ, ((-((p.1 ^ 2 + p.2 ^ 2 : ℝ) : ℂ) + w) ^ n)⁻¹ =
      -(π / ((n : ℂ) - 1)) * (w ^ (n - 1))⁻¹ := by
  rw [← integral_comp_polarCoord_symm]
  have hpt : ∀ p : ℝ × ℝ,
      p.1 • ((-((((polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2 : ℝ)) : ℂ) + w) ^ n)⁻¹ =
        (p.1 : ℂ) * ((-((p.1 ^ 2 : ℝ) : ℂ) + w) ^ n)⁻¹ * (fun _ : ℝ => (1 : ℂ)) p.2 := by
    intro p
    rw [polarCoord_symm_apply]
    have : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
      linear_combination p.1 ^ 2 * Real.cos_sq_add_sin_sq p.2
    rw [this, real_smul, mul_one]
  simp_rw [hpt]
  rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
    integral_prod_mul (fun r : ℝ => (r : ℂ) * ((-((r ^ 2 : ℝ) : ℂ) + w) ^ n)⁻¹)
      (fun _ : ℝ => (1 : ℂ)),
    integral_Ioi_mul_inv_neg_sq_add_pow hw hn, setIntegral_const, measureReal_def,
    Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), real_smul, mul_one]
  have hk : ((n : ℂ) - 1) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  push_cast
  field_simp
  ring

/-- The integrand `(w - t₀² - t₁²)^{-n}` is integrable on `Fin 2 → ℝ` for `n ≥ 2`. -/
theorem integrable_inv_neg_sumSq_add_pow (hw : w.im < 0) {n : ℕ} (hn : 2 ≤ n) :
    Integrable fun t : Fin 2 → ℝ => ((-((t 0 ^ 2 + t 1 ^ 2 : ℝ) : ℂ) + w) ^ n)⁻¹ := by
  have h := (volume_preserving_finTwoArrow ℝ).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)
    (g := fun p : ℝ × ℝ => ((-((p.1 ^ 2 + p.2 ^ 2 : ℝ) : ℂ) + w) ^ n)⁻¹)
  exact h.mpr (integrable_prod_inv_neg_sumSq_add_pow hw hn)

/-- **The case `A = 1` on `Fin 2 → ℝ`.** For `Im w < 0` and `n ≥ 2`,
`∫ (w - t₀² - t₁²)^{-n} dt = -(π/(n-1)) w^{1-n}`. -/
theorem integral_inv_neg_sumSq_add_pow (hw : w.im < 0) {n : ℕ} (hn : 2 ≤ n) :
    ∫ t : Fin 2 → ℝ, ((-((t 0 ^ 2 + t 1 ^ 2 : ℝ) : ℂ) + w) ^ n)⁻¹ =
      -(π / ((n : ℂ) - 1)) * (w ^ (n - 1))⁻¹ := by
  rw [← integral_prod_inv_neg_sumSq_add_pow hw hn]
  exact (volume_preserving_finTwoArrow ℝ).integral_comp'
    (g := fun p : ℝ × ℝ => ((-((p.1 ^ 2 + p.2 ^ 2 : ℝ) : ℂ) + w) ^ n)⁻¹)

/-! ### A positive definite `A` -/

/-- The upper-triangular Cholesky factor `!![√a, b/√a; 0, √(det A / a)]` of a `2 × 2` matrix
`A = !![a, b; b, c]`. -/
noncomputable def cholesky (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.sqrt (A 0 0), A 0 1 / Real.sqrt (A 0 0); 0, Real.sqrt (A.det / A 0 0)]

theorem det_cholesky {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) :
    (cholesky A).det = Real.sqrt A.det := by
  have ha : 0 < A 0 0 := hA.diag_pos
  rw [cholesky, det_fin_two_of, mul_zero, sub_zero, ← Real.sqrt_mul ha.le,
    mul_div_cancel₀ _ ha.ne']

/-- The quadratic form of `A` is the squared Euclidean norm of `cholesky A *ᵥ t`. -/
theorem dotProduct_mulVec_eq_cholesky {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    (t : Fin 2 → ℝ) :
    t ⬝ᵥ A *ᵥ t = (cholesky A *ᵥ t) 0 ^ 2 + (cholesky A *ᵥ t) 1 ^ 2 := by
  have ha : 0 < A 0 0 := hA.diag_pos
  have hd : 0 < A.det := hA.det_pos
  have hsym : A 1 0 = A 0 1 := by simpa using hA.isHermitian.apply 0 1
  have hsa : Real.sqrt (A 0 0) ^ 2 = A 0 0 := Real.sq_sqrt ha.le
  have hsa0 : Real.sqrt (A 0 0) ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hsd : Real.sqrt (A.det / A 0 0) ^ 2 = A.det / A 0 0 := Real.sq_sqrt (by positivity)
  simp only [cholesky, dotProduct, mulVec, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one, zero_mul, zero_add]
  rw [mul_pow, hsd, det_fin_two, hsym]
  set sa := Real.sqrt (A 0 0)
  rw [← hsa]
  field_simp
  ring

/-- **Integrability.** For a positive definite real `2 × 2` matrix `A`, `Im w < 0` and `n ≥ 2`,
the integrand `(-tᵀ A t + w)^{-n}` is integrable on `Fin 2 → ℝ`. -/
theorem integrable_inv_neg_quadratic_add_pow {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    (hw : w.im < 0) {n : ℕ} (hn : 2 ≤ n) :
    Integrable fun t : Fin 2 → ℝ => ((-((t ⬝ᵥ A *ᵥ t : ℝ) : ℂ) + w) ^ n)⁻¹ := by
  set M := cholesky A
  have h0 : LinearMap.det (toLin' M) ≠ 0 := by
    rw [LinearMap.det_toLin', det_cholesky hA]
    exact (Real.sqrt_pos.mpr hA.det_pos).ne'
  let e : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) := ((toLin' M).equivOfDetNeZero h0).toContinuousLinearEquiv
  have he : (e : (Fin 2 → ℝ) → (Fin 2 → ℝ)) = toLin' M := rfl
  set g : (Fin 2 → ℝ) → ℂ := fun s => ((-((s 0 ^ 2 + s 1 ^ 2 : ℝ) : ℂ) + w) ^ n)⁻¹
  have hfun : (fun t : Fin 2 → ℝ => ((-((t ⬝ᵥ A *ᵥ t : ℝ) : ℂ) + w) ^ n)⁻¹) = g ∘ e := by
    funext t
    simp only [Function.comp_apply, he, toLin'_apply, g, dotProduct_mulVec_eq_cholesky hA t, M]
  have hemb : MeasurableEmbedding (e : (Fin 2 → ℝ) → (Fin 2 → ℝ)) :=
    e.toHomeomorph.measurableEmbedding
  rw [hfun, ← hemb.integrable_map_iff]
  have hmap : Measure.map e volume = ENNReal.ofReal |(LinearMap.det (toLin' M))⁻¹| • volume := by
    rw [he]
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume h0
  rw [hmap]
  exact (integrable_inv_neg_sumSq_add_pow hw hn).smul_measure ENNReal.ofReal_ne_top

/-- **The signed two-loop energy integral** (`docs/TWO-LOOP-DERIVATION.md`, section 4.3;
obligation O2-10). For a positive definite real `2 × 2` matrix `A`, `Im w < 0` and `n ≥ 2`,
`∫_{ℝ²} (-tᵀ A t + w)^{-n} dt = -(π/(n-1)) (det A)^{-1/2} w^{1-n}`. -/
theorem integral_inv_neg_quadratic_add_pow {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    (hw : w.im < 0) {n : ℕ} (hn : 2 ≤ n) :
    ∫ t : Fin 2 → ℝ, ((-((t ⬝ᵥ A *ᵥ t : ℝ) : ℂ) + w) ^ n)⁻¹ =
      -(π / ((n : ℂ) - 1)) * ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ * (w ^ (n - 1))⁻¹ := by
  set M := cholesky A
  have hdpos : 0 < Real.sqrt A.det := Real.sqrt_pos.mpr hA.det_pos
  have h0 : LinearMap.det (toLin' M) ≠ 0 := by
    rw [LinearMap.det_toLin', det_cholesky hA]
    exact hdpos.ne'
  let e : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) := ((toLin' M).equivOfDetNeZero h0).toContinuousLinearEquiv
  have he : (e : (Fin 2 → ℝ) → (Fin 2 → ℝ)) = toLin' M := rfl
  set g : (Fin 2 → ℝ) → ℂ := fun s => ((-((s 0 ^ 2 + s 1 ^ 2 : ℝ) : ℂ) + w) ^ n)⁻¹
  have hfun : (fun t : Fin 2 → ℝ => ((-((t ⬝ᵥ A *ᵥ t : ℝ) : ℂ) + w) ^ n)⁻¹) =
      fun t => g (e t) := by
    funext t
    simp only [he, toLin'_apply, g, dotProduct_mulVec_eq_cholesky hA t, M]
  have hemb : MeasurableEmbedding (e : (Fin 2 → ℝ) → (Fin 2 → ℝ)) :=
    e.toHomeomorph.measurableEmbedding
  rw [hfun, ← hemb.integral_map]
  have hmap : Measure.map e volume = ENNReal.ofReal |(LinearMap.det (toLin' M))⁻¹| • volume := by
    rw [he]
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume h0
  rw [hmap,
    integral_smul_measure, integral_inv_neg_sumSq_add_pow hw hn,
    ENNReal.toReal_ofReal (by positivity), LinearMap.det_toLin', det_cholesky hA,
    abs_inv, abs_of_pos hdpos, real_smul]
  push_cast
  ring

end QED.Integration.TwoLoop

end
