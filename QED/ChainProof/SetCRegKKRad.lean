/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.CountertermLimitProduct

/-!
# Set (c): the one-loop scalar integrals `(k² + A - iδ)⁻⁴` and `(k² + A - iδ)⁻⁵`

Helper level for `QED.ChainProof.SetCRegDisp.IsKKSclLim` (`QED/ChainProof/SetCRegKKVal.lean`).
After Feynman parameters the scalar tadpole of the longitudinal cancellation is an integral of
the fourth and fifth inverse powers of `k² + A - iδ`. This file evaluates their energy-first
integrals, as `QED/TwoLoop/CountertermLimitProduct.lean` does for the third power:

* `integral_inv_one_add_sq_pow_four`, `…_five`: `∫ (1 + t²)⁻⁴ = 5π/16`, `∫ (1 + t²)⁻⁵ = 35π/128`;
* `kkDs`: the denominator `k² + A - iδ`; `kkSp4`, `kkSp5`: the energy integrals at spatial
  momentum `v`, `(5π/16) (-w)^{-7/2}` and `-(35π/128) (-w)^{-9/2}`, `w = |v|² + A - iδ`
  (`integral_kkDs_pow_four`, `integral_kkDs_pow_five`);
* `norm_kkSp4_le`, `norm_kkSp5_le`: bounds by `K (|v|² + A)^{1/2 - n}`, uniform in `δ`;
* `tendsto_kkSp4`, `tendsto_kkSp5`: continuity at `δ = 0` from above;
* `integral_sum_sq_add_rpow_neg_seven_halves`, `…_nine_halves`:
  `∫_{ℝ³} (|v|² + D)^{-7/2} = 8π/(15 D²)`, `∫_{ℝ³} (|v|² + D)^{-9/2} = 32π/(105 D³)`;
* **`integral_kkSp4_zero`**, **`integral_kkSp5_zero`**: at `δ = 0` the spatial integrals are
  `i π²/(6 A²)` and `i π²/(12 A³)`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.ChainProof.SetCRegDisp

open QED.Integration

/-! ### The energy constants -/

/-- `∫ (1 + t²)⁻⁴ dt = 5π/16`. -/
theorem integral_inv_one_add_sq_pow_four : ∫ t : ℝ, ((1 + t ^ 2) ^ 4)⁻¹ = 5 * π / 16 := by
  set F : ℝ → ℝ := fun t => t / (6 * (1 + t ^ 2) ^ 3) + 5 * t / (24 * (1 + t ^ 2) ^ 2) +
    5 * t / (16 * (1 + t ^ 2)) + 5 / 16 * Real.arctan t with hF
  have hderiv : ∀ t : ℝ, HasDerivAt F (((1 + t ^ 2) ^ 4)⁻¹) t := by
    intro t
    have h1 : 0 < 1 + t ^ 2 := by positivity
    have hu : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t).const_add 1
    have hu3 : HasDerivAt (fun t : ℝ => 6 * (1 + t ^ 2) ^ 3)
        (6 * (3 * (1 + t ^ 2) ^ 2 * (2 * t))) t := by simpa using (hu.pow 3).const_mul 6
    have hu2 : HasDerivAt (fun t : ℝ => 24 * (1 + t ^ 2) ^ 2)
        (24 * (2 * (1 + t ^ 2) * (2 * t))) t := by simpa using (hu.pow 2).const_mul 24
    have hu1 : HasDerivAt (fun t : ℝ => 16 * (1 + t ^ 2)) (16 * (2 * t)) t := hu.const_mul 16
    have h5 : HasDerivAt (fun t : ℝ => 5 * t) 5 t := by simpa using (hasDerivAt_id' t).const_mul 5
    have hq1 := (hasDerivAt_id' t).div hu3 (by positivity)
    have hq2 := h5.div hu2 (by positivity)
    have hq3 := h5.div hu1 (by positivity)
    refine (((hq1.add hq2).add hq3).add ((Real.hasDerivAt_arctan t).const_mul (5 / 16)))
      |>.congr_deriv ?_
    field_simp
    ring
  have hlim : ∀ {l : Filter ℝ} {L : ℝ}, Tendsto (fun t : ℝ => t / (1 + t ^ 2)) l (𝓝 0) →
      Tendsto (fun t : ℝ => (1 + t ^ 2)⁻¹) l (𝓝 0) → Tendsto Real.arctan l (𝓝 L) →
      Tendsto F l (𝓝 (5 / 16 * L)) := by
    intro l L h1 h2 h3
    have e : F = fun t => (t / (1 + t ^ 2)) * ((1 + t ^ 2)⁻¹ ^ 2 / 6 +
        5 * (1 + t ^ 2)⁻¹ / 24 + 5 / 16) + 5 / 16 * Real.arctan t := by
      funext t
      have : (1 + t ^ 2) ≠ 0 := by positivity
      simp only [hF]
      field_simp
    rw [e]
    have := (h1.mul (((h2.pow 2).div_const 6).add ((h2.const_mul 5).div_const 24)
      |>.add_const (5 / 16))).add (h3.const_mul (5 / 16))
    simpa using this
  have hbot := hlim tendsto_div_one_add_sq_atBot tendsto_inv_one_add_sq_atBot
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot)
  have htop := hlim tendsto_div_one_add_sq_atTop tendsto_inv_one_add_sq_atTop
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop)
  rw [integral_of_hasDerivAt_of_tendsto hderiv (integrable_inv_one_add_sq_pow 4 (by norm_num))
    hbot htop]
  ring

/-- `∫ (1 + t²)⁻⁵ dt = 35π/128`. -/
theorem integral_inv_one_add_sq_pow_five : ∫ t : ℝ, ((1 + t ^ 2) ^ 5)⁻¹ = 35 * π / 128 := by
  set F : ℝ → ℝ := fun t => t / (8 * (1 + t ^ 2) ^ 4) + 7 * t / (48 * (1 + t ^ 2) ^ 3) +
    35 * t / (192 * (1 + t ^ 2) ^ 2) + 35 * t / (128 * (1 + t ^ 2)) +
    35 / 128 * Real.arctan t with hF
  have hderiv : ∀ t : ℝ, HasDerivAt F (((1 + t ^ 2) ^ 5)⁻¹) t := by
    intro t
    have h1 : 0 < 1 + t ^ 2 := by positivity
    have hu : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t).const_add 1
    have hu4 : HasDerivAt (fun t : ℝ => 8 * (1 + t ^ 2) ^ 4)
        (8 * (4 * (1 + t ^ 2) ^ 3 * (2 * t))) t := by simpa using (hu.pow 4).const_mul 8
    have hu3 : HasDerivAt (fun t : ℝ => 48 * (1 + t ^ 2) ^ 3)
        (48 * (3 * (1 + t ^ 2) ^ 2 * (2 * t))) t := by simpa using (hu.pow 3).const_mul 48
    have hu2 : HasDerivAt (fun t : ℝ => 192 * (1 + t ^ 2) ^ 2)
        (192 * (2 * (1 + t ^ 2) * (2 * t))) t := by simpa using (hu.pow 2).const_mul 192
    have hu1 : HasDerivAt (fun t : ℝ => 128 * (1 + t ^ 2)) (128 * (2 * t)) t := hu.const_mul 128
    have h7 : HasDerivAt (fun t : ℝ => 7 * t) 7 t := by simpa using (hasDerivAt_id' t).const_mul 7
    have h35 : HasDerivAt (fun t : ℝ => 35 * t) 35 t := by
      simpa using (hasDerivAt_id' t).const_mul 35
    have hq1 := (hasDerivAt_id' t).div hu4 (by positivity)
    have hq2 := h7.div hu3 (by positivity)
    have hq3 := h35.div hu2 (by positivity)
    have hq4 := h35.div hu1 (by positivity)
    refine ((((hq1.add hq2).add hq3).add hq4).add
      ((Real.hasDerivAt_arctan t).const_mul (35 / 128))) |>.congr_deriv ?_
    field_simp
    ring
  have hlim : ∀ {l : Filter ℝ} {L : ℝ}, Tendsto (fun t : ℝ => t / (1 + t ^ 2)) l (𝓝 0) →
      Tendsto (fun t : ℝ => (1 + t ^ 2)⁻¹) l (𝓝 0) → Tendsto Real.arctan l (𝓝 L) →
      Tendsto F l (𝓝 (35 / 128 * L)) := by
    intro l L h1 h2 h3
    have e : F = fun t => (t / (1 + t ^ 2)) * ((1 + t ^ 2)⁻¹ ^ 3 / 8 +
        7 * (1 + t ^ 2)⁻¹ ^ 2 / 48 + 35 * (1 + t ^ 2)⁻¹ / 192 + 35 / 128) +
        35 / 128 * Real.arctan t := by
      funext t
      have : (1 + t ^ 2) ≠ 0 := by positivity
      simp only [hF]
      field_simp
    rw [e]
    have := (h1.mul (((((h2.pow 3).div_const 8).add ((h2.pow 2).const_mul 7 |>.div_const 48))
      |>.add ((h2.const_mul 35).div_const 192)) |>.add_const (35 / 128))).add
      (h3.const_mul (35 / 128))
    simpa using this
  have hbot := hlim tendsto_div_one_add_sq_atBot tendsto_inv_one_add_sq_atBot
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot)
  have htop := hlim tendsto_div_one_add_sq_atTop tendsto_inv_one_add_sq_atTop
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop)
  rw [integral_of_hasDerivAt_of_tendsto hderiv (integrable_inv_one_add_sq_pow 5 (by norm_num))
    hbot htop]
  ring

/-! ### The energy integrals -/

/-- The denominator `k² + A - iδ`. -/
noncomputable def kkDs (A δ : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  ((Minkowski.dot k k + A : ℝ) : ℂ) - (δ : ℂ) * I

/-- `-w`, `w = |v|² + A - iδ`, the argument of the energy integrals. -/
noncomputable def kkW (A δ : ℝ) (v : Fin 3 → ℝ) : ℂ :=
  -((((∑ k, v k ^ 2 + A : ℝ)) : ℂ) - (δ : ℂ) * I)

/-- The energy integral of `(k² + A - iδ)⁻⁴` at spatial momentum `v`. -/
noncomputable def kkSp4 (A δ : ℝ) (v : Fin 3 → ℝ) : ℂ :=
  (5 * π / 16 : ℂ) * kkW A δ v ^ (-(7 / 2 : ℂ))

/-- The energy integral of `(k² + A - iδ)⁻⁵` at spatial momentum `v`. -/
noncomputable def kkSp5 (A δ : ℝ) (v : Fin 3 → ℝ) : ℂ :=
  -((35 * π / 128 : ℂ) * kkW A δ v ^ (-(9 / 2 : ℂ)))

theorem kkW_mem_slitPlane {A δ : ℝ} (hδ : 0 < δ) (v : Fin 3 → ℝ) : kkW A δ v ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  right
  rw [kkW, QED.TwoLoop.CountertermLimit.im_neg_aux]
  exact hδ.ne'

theorem kkDs_cons (A δ t : ℝ) (v : Fin 3 → ℝ) :
    kkDs A δ (Fin.cons t v) = -((t : ℂ) ^ 2 + kkW A δ v) := by
  rw [kkDs, kkW, QED.TwoLoop.CountertermLimit.dot_cons_self]
  push_cast
  ring

/-- **The energy integral of `(k² + A - iδ)⁻⁴`.** -/
theorem integral_kkDs_pow_four {A δ : ℝ} (hδ : 0 < δ) (v : Fin 3 → ℝ) :
    ∫ t : ℝ, ((kkDs A δ (Fin.cons t v)) ^ 4)⁻¹ = kkSp4 A δ v := by
  have h := integral_sq_add_zpow_of_real 4 (by norm_num) ((5 * π / 16 : ℝ) : ℂ)
    (fun a ha => integral_sq_add_zpow_ofReal 4 ha integral_inv_one_add_sq_pow_four)
    (kkW_mem_slitPlane (A := A) hδ v)
  have hpt : ∀ t : ℝ, ((kkDs A δ (Fin.cons t v)) ^ 4)⁻¹ =
      ((t : ℂ) ^ 2 + kkW A δ v) ^ (-((4 : ℕ) : ℤ)) := fun t => by
    rw [kkDs_cons, zpow_neg, zpow_natCast, neg_pow, show (-1 : ℂ) ^ 4 = 1 by norm_num, one_mul]
  simp_rw [hpt]
  rw [h, kkSp4]
  push_cast
  norm_num

/-- **The energy integral of `(k² + A - iδ)⁻⁵`.** -/
theorem integral_kkDs_pow_five {A δ : ℝ} (hδ : 0 < δ) (v : Fin 3 → ℝ) :
    ∫ t : ℝ, ((kkDs A δ (Fin.cons t v)) ^ 5)⁻¹ = kkSp5 A δ v := by
  have h := integral_sq_add_zpow_of_real 5 (by norm_num) ((35 * π / 128 : ℝ) : ℂ)
    (fun a ha => integral_sq_add_zpow_ofReal 5 ha integral_inv_one_add_sq_pow_five)
    (kkW_mem_slitPlane (A := A) hδ v)
  have hpt : ∀ t : ℝ, ((kkDs A δ (Fin.cons t v)) ^ 5)⁻¹ =
      -(((t : ℂ) ^ 2 + kkW A δ v) ^ (-((5 : ℕ) : ℤ))) := fun t => by
    rw [kkDs_cons, zpow_neg, zpow_natCast, neg_pow, show (-1 : ℂ) ^ 5 = -1 by norm_num,
      neg_one_mul, inv_neg]
  simp_rw [hpt]
  rw [integral_neg, h, kkSp5]
  push_cast
  norm_num

/-! ### Bounds and continuity in `δ` -/

theorem kkW_ne_zero {A : ℝ} (hA : 0 < A) (δ : ℝ) (v : Fin 3 → ℝ) : kkW A δ v ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [kkW, QED.TwoLoop.CountertermLimit.re_neg_aux, zero_re] at this
  have h0 : 0 ≤ ∑ k, v k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  linarith

theorem sum_sq_add_pos {A : ℝ} (hA : 0 < A) (v : Fin 3 → ℝ) : 0 < ∑ k, v k ^ 2 + A := by
  have h0 : 0 ≤ ∑ k, v k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  linarith

/-- `‖(-w)^{-p}‖ ≤ (|v|² + A)^{-p}` for `p ≥ 0`, uniformly in `δ`. -/
theorem norm_kkW_cpow_le {A : ℝ} (hA : 0 < A) (δ : ℝ) (v : Fin 3 → ℝ) {p : ℝ} (hp : 0 ≤ p) :
    ‖kkW A δ v ^ (((-p : ℝ)) : ℂ)‖ ≤ (∑ k, v k ^ 2 + A) ^ (-p) := by
  have ha := sum_sq_add_pos hA v
  rw [norm_cpow_of_ne_zero (kkW_ne_zero hA δ v), ofReal_re, ofReal_im, mul_zero, Real.exp_zero,
    div_one]
  have hre : (∑ k, v k ^ 2 + A) ≤ ‖kkW A δ v‖ := by
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [kkW, QED.TwoLoop.CountertermLimit.re_neg_aux, abs_neg, abs_of_pos ha]
  exact Real.rpow_le_rpow_of_nonpos ha hre (by linarith)

theorem norm_kkSp4_le {A : ℝ} (hA : 0 < A) (δ : ℝ) (v : Fin 3 → ℝ) :
    ‖kkSp4 A δ v‖ ≤ 5 * π / 16 * (∑ k, v k ^ 2 + A) ^ (-(7 / 2 : ℝ)) := by
  have h := norm_kkW_cpow_le hA δ v (p := 7 / 2) (by norm_num)
  rw [kkSp4, norm_mul, show (-(7 / 2 : ℂ)) = (((-(7 / 2) : ℝ)) : ℂ) by push_cast; ring]
  have h1 : ‖(5 * π / 16 : ℂ)‖ = 5 * π / 16 := by
    rw [show (5 * π / 16 : ℂ) = ((5 * π / 16 : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [h1]
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem norm_kkSp5_le {A : ℝ} (hA : 0 < A) (δ : ℝ) (v : Fin 3 → ℝ) :
    ‖kkSp5 A δ v‖ ≤ 35 * π / 128 * (∑ k, v k ^ 2 + A) ^ (-(9 / 2 : ℝ)) := by
  have h := norm_kkW_cpow_le hA δ v (p := 9 / 2) (by norm_num)
  rw [kkSp5, norm_neg, norm_mul, show (-(9 / 2 : ℂ)) = (((-(9 / 2) : ℝ)) : ℂ) by push_cast; ring]
  have h1 : ‖(35 * π / 128 : ℂ)‖ = 35 * π / 128 := by
    rw [show (35 * π / 128 : ℂ) = ((35 * π / 128 : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [h1]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- `(-w)^s` is continuous in `δ ≥ 0` at `δ = 0`. -/
theorem tendsto_kkW_cpow {A : ℝ} (hA : 0 < A) (v : Fin 3 → ℝ) (s : ℂ) :
    Tendsto (fun δ => kkW A δ v ^ s) (𝓝[≥] 0) (𝓝 (kkW A 0 v ^ s)) := by
  set a : ℝ := ∑ k, v k ^ 2 + A
  have ha : 0 < a := sum_sq_add_pos hA v
  set z : ℝ → ℂ := fun δ => kkW A δ v with hz_def
  have hz0 : z 0 = ((-a : ℝ) : ℂ) := by simp [z, kkW, a]
  have hzc : Continuous z := by simp only [z, kkW]; fun_prop
  have hzS : Tendsto z (𝓝[≥] 0) (𝓝[{w : ℂ | 0 ≤ w.im}] (z 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨(hzc.tendsto 0).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 ≤ δ)
    show 0 ≤ (kkW A δ v).im
    rw [kkW, QED.TwoLoop.CountertermLimit.im_neg_aux]
    exact hδ
  have hlog := (continuousWithinAt_log_of_re_neg_of_im_zero (z := z 0) (by simp [hz0, ha])
    (by simp [hz0])).tendsto.comp hzS
  have hexp := (continuous_exp.tendsto _).comp (hlog.mul_const s)
  have hne : ∀ δ, z δ ≠ 0 := fun δ => kkW_ne_zero hA δ v
  have key : ∀ δ, kkW A δ v ^ s = exp (log (z δ) * s) := fun δ => by
    rw [← cpow_def_of_ne_zero (hne δ)]
  simp only [key]
  exact hexp

theorem tendsto_kkSp4 {A : ℝ} (hA : 0 < A) (v : Fin 3 → ℝ) :
    Tendsto (fun δ => kkSp4 A δ v) (𝓝[≥] 0) (𝓝 (kkSp4 A 0 v)) :=
  (tendsto_kkW_cpow hA v _).const_mul _

theorem tendsto_kkSp5 {A : ℝ} (hA : 0 < A) (v : Fin 3 → ℝ) :
    Tendsto (fun δ => kkSp5 A δ v) (𝓝[≥] 0) (𝓝 (kkSp5 A 0 v)) :=
  ((tendsto_kkW_cpow hA v _).const_mul _).neg

/-! ### The spatial integrals at `δ = 0` -/

theorem rpow_neg_seven_halves_eq {x : ℝ} (hx : 0 ≤ x) : x ^ (-(7 / 2 : ℝ)) = ((√x) ^ 7)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx, ← Real.rpow_neg hx]
  norm_num

theorem rpow_neg_nine_halves_eq {x : ℝ} (hx : 0 ≤ x) : x ^ (-(9 / 2 : ℝ)) = ((√x) ^ 9)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx, ← Real.rpow_neg hx]
  norm_num

/-- `∫₀^∞ r² (r² + D)^{-7/2} dr = 2/(15 D²)`. -/
theorem integral_Ioi_sq_mul_rpow_neg_seven_halves {D : ℝ} (hD : 0 < D) :
    ∫ r in Ioi (0 : ℝ), r ^ 2 * (r ^ 2 + D) ^ (-(7 / 2 : ℝ)) = 2 / (15 * D ^ 2) := by
  have hderiv : ∀ r ∈ Ici (0 : ℝ), HasDerivAt
      (fun r : ℝ => ((r / √(r ^ 2 + D)) ^ 3 / 3 - (r / √(r ^ 2 + D)) ^ 5 / 5) / D ^ 2)
      (r ^ 2 * (r ^ 2 + D) ^ (-(7 / 2 : ℝ))) r := by
    intro r _
    have hS : 0 < √(r ^ 2 + D) := Real.sqrt_pos.2 (by positivity)
    have hS2 : √(r ^ 2 + D) ^ 2 = r ^ 2 + D := Real.sq_sqrt (by positivity)
    have hu := (hasDerivAt_id r).div (hasDerivAt_sqrt_sq_add hD r) hS.ne'
    have h := (((hu.pow 3).div_const 3).sub ((hu.pow 5).div_const 5)).div_const (D ^ 2)
    refine h.congr_deriv ?_
    rw [rpow_neg_seven_halves_eq (by positivity)]
    simp only [Pi.div_apply, id, Nat.cast_ofNat]
    generalize √(r ^ 2 + D) = S at hS hS2 ⊢
    have hD' : D = S ^ 2 - r ^ 2 := by linarith
    subst hD'
    have hSne := hS.ne'
    norm_num only [div_pow]
    field_simp
  have hpos : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ r ^ 2 * (r ^ 2 + D) ^ (-(7 / 2 : ℝ)) := fun r _ => by
    positivity
  have hlim : Tendsto (fun r : ℝ => ((r / √(r ^ 2 + D)) ^ 3 / 3 - (r / √(r ^ 2 + D)) ^ 5 / 5) /
      D ^ 2) atTop (𝓝 ((1 ^ 3 / 3 - 1 ^ 5 / 5) / D ^ 2)) :=
    ((((tendsto_div_sqrt_sq_add_atTop hD.le).pow 3).div_const 3).sub
      (((tendsto_div_sqrt_sq_add_atTop hD.le).pow 5).div_const 5)).div_const _
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim]
  field_simp
  ring

/-- `∫₀^∞ r² (r² + D)^{-9/2} dr = 8/(105 D³)`. -/
theorem integral_Ioi_sq_mul_rpow_neg_nine_halves {D : ℝ} (hD : 0 < D) :
    ∫ r in Ioi (0 : ℝ), r ^ 2 * (r ^ 2 + D) ^ (-(9 / 2 : ℝ)) = 8 / (105 * D ^ 3) := by
  have hderiv : ∀ r ∈ Ici (0 : ℝ), HasDerivAt
      (fun r : ℝ => ((r / √(r ^ 2 + D)) ^ 3 / 3 - 2 * (r / √(r ^ 2 + D)) ^ 5 / 5 +
        (r / √(r ^ 2 + D)) ^ 7 / 7) / D ^ 3)
      (r ^ 2 * (r ^ 2 + D) ^ (-(9 / 2 : ℝ))) r := by
    intro r _
    have hS : 0 < √(r ^ 2 + D) := Real.sqrt_pos.2 (by positivity)
    have hS2 : √(r ^ 2 + D) ^ 2 = r ^ 2 + D := Real.sq_sqrt (by positivity)
    have hu := (hasDerivAt_id r).div (hasDerivAt_sqrt_sq_add hD r) hS.ne'
    have h := ((((hu.pow 3).div_const 3).sub (((hu.pow 5).const_mul 2).div_const 5)).add
      ((hu.pow 7).div_const 7)).div_const (D ^ 3)
    refine h.congr_deriv ?_
    rw [rpow_neg_nine_halves_eq (by positivity)]
    simp only [Pi.div_apply, id, Nat.cast_ofNat]
    generalize √(r ^ 2 + D) = S at hS hS2 ⊢
    have hD' : D = S ^ 2 - r ^ 2 := by linarith
    subst hD'
    have hSne := hS.ne'
    norm_num only [div_pow]
    field_simp
    ring
  have hpos : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ r ^ 2 * (r ^ 2 + D) ^ (-(9 / 2 : ℝ)) := fun r _ => by
    positivity
  have hlim : Tendsto (fun r : ℝ => ((r / √(r ^ 2 + D)) ^ 3 / 3 -
      2 * (r / √(r ^ 2 + D)) ^ 5 / 5 + (r / √(r ^ 2 + D)) ^ 7 / 7) / D ^ 3) atTop
      (𝓝 ((1 ^ 3 / 3 - 2 * 1 ^ 5 / 5 + 1 ^ 7 / 7) / D ^ 3)) :=
    (((((tendsto_div_sqrt_sq_add_atTop hD.le).pow 3).div_const 3).sub
      ((((tendsto_div_sqrt_sq_add_atTop hD.le).pow 5).const_mul 2).div_const 5)).add
      (((tendsto_div_sqrt_sq_add_atTop hD.le).pow 7).div_const 7)).div_const _
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim]
  field_simp
  ring

/-- `∫_{ℝ³} (|v|² + D)^{-7/2} d³v = 8π/(15 D²)`. -/
theorem integral_sum_sq_add_rpow_neg_seven_halves {D : ℝ} (hD : 0 < D) :
    ∫ v : Fin 3 → ℝ, (∑ k, v k ^ 2 + D) ^ (-(7 / 2 : ℝ)) = 8 * π / (15 * D ^ 2) := by
  have h := integral_comp_sum_sq (fun x : ℝ => (x + D) ^ (-(7 / 2 : ℝ)))
  simp only [smul_eq_mul] at h
  rw [h, integral_Ioi_sq_mul_rpow_neg_seven_halves hD]
  ring

/-- `∫_{ℝ³} (|v|² + D)^{-9/2} d³v = 32π/(105 D³)`. -/
theorem integral_sum_sq_add_rpow_neg_nine_halves {D : ℝ} (hD : 0 < D) :
    ∫ v : Fin 3 → ℝ, (∑ k, v k ^ 2 + D) ^ (-(9 / 2 : ℝ)) = 32 * π / (105 * D ^ 3) := by
  have h := integral_comp_sum_sq (fun x : ℝ => (x + D) ^ (-(9 / 2 : ℝ)))
  simp only [smul_eq_mul] at h
  rw [h, integral_Ioi_sq_mul_rpow_neg_nine_halves hD]
  ring

/-- `(-w)^s` at `δ = 0`: `(|v|² + A)^s e^{iπs}` for real `s`. -/
theorem kkW_zero_cpow {A : ℝ} (hA : 0 < A) (v : Fin 3 → ℝ) (s : ℝ) :
    kkW A 0 v ^ (s : ℂ) = (((∑ k, v k ^ 2 + A) ^ s : ℝ) : ℂ) * exp (π * I * s) := by
  have ha := sum_sq_add_pos hA v
  have h1 : kkW A 0 v = ((-(∑ k, v k ^ 2 + A) : ℝ) : ℂ) := by simp [kkW]
  rw [h1, ofReal_cpow_of_nonpos (by linarith), ofReal_neg, neg_neg, ofReal_cpow ha.le]

theorem exp_neg_seven_halves : exp (π * I * ((-(7 / 2) : ℝ) : ℂ)) = I := by
  have h : π * I * ((-(7 / 2) : ℝ) : ℂ) = π / 2 * I - 2 * (2 * π * I) := by push_cast; ring
  rw [h, exp_sub, show (2 : ℂ) * (2 * π * I) = ((2 : ℕ) : ℂ) * (2 * π * I) by norm_num,
    exp_nat_mul_two_pi_mul_I, div_one, exp_pi_div_two_mul_I]

theorem exp_neg_nine_halves : exp (π * I * ((-(9 / 2) : ℝ) : ℂ)) = -I := by
  have h : π * I * ((-(9 / 2) : ℝ) : ℂ) = -(π / 2 * I) - 2 * (2 * π * I) := by push_cast; ring
  rw [h, exp_sub, show (2 : ℂ) * (2 * π * I) = ((2 : ℕ) : ℂ) * (2 * π * I) by norm_num,
    exp_nat_mul_two_pi_mul_I, div_one, exp_neg, exp_pi_div_two_mul_I, inv_I]

theorem kkSp4_zero {A : ℝ} (hA : 0 < A) (v : Fin 3 → ℝ) :
    kkSp4 A 0 v = I * ((5 * π / 16 * (∑ k, v k ^ 2 + A) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ) := by
  rw [kkSp4, show (-(7 / 2 : ℂ)) = (((-(7 / 2) : ℝ)) : ℂ) by push_cast; ring,
    kkW_zero_cpow hA, exp_neg_seven_halves]
  push_cast
  ring

theorem kkSp5_zero {A : ℝ} (hA : 0 < A) (v : Fin 3 → ℝ) :
    kkSp5 A 0 v = I * ((35 * π / 128 * (∑ k, v k ^ 2 + A) ^ (-(9 / 2 : ℝ)) : ℝ) : ℂ) := by
  rw [kkSp5, show (-(9 / 2 : ℂ)) = (((-(9 / 2) : ℝ)) : ℂ) by push_cast; ring,
    kkW_zero_cpow hA, exp_neg_nine_halves]
  push_cast
  ring

/-- **The spatial integral of `(k² + A)⁻⁴` at `δ = 0`**: `i π²/(6 A²)`. -/
theorem integral_kkSp4_zero {A : ℝ} (hA : 0 < A) :
    ∫ v : Fin 3 → ℝ, kkSp4 A 0 v = I * ((π ^ 2 / (6 * A ^ 2) : ℝ) : ℂ) := by
  simp only [kkSp4_zero hA]
  rw [integral_const_mul, integral_complex_ofReal, integral_const_mul,
    integral_sum_sq_add_rpow_neg_seven_halves hA]
  congr 2
  field_simp
  ring

/-- **The spatial integral of `(k² + A)⁻⁵` at `δ = 0`**: `i π²/(12 A³)`. -/
theorem integral_kkSp5_zero {A : ℝ} (hA : 0 < A) :
    ∫ v : Fin 3 → ℝ, kkSp5 A 0 v = I * ((π ^ 2 / (12 * A ^ 3) : ℝ) : ℂ) := by
  simp only [kkSp5_zero hA]
  rw [integral_const_mul, integral_complex_ofReal, integral_const_mul,
    integral_sum_sq_add_rpow_neg_nine_halves hA]
  congr 2
  field_simp
  ring

end QED.ChainProof.SetCRegDisp

end
