/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI15KTaylor
public import QED.Polylog.Deriv
import QED.Polylog.LiLimits
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Set (d), master `I₁₅`: the first Taylor coefficient of `K`, `∫ F₁ = -33/4`

Write `v = 1 - u`. Then `P = (1 - v x)(u + v x)` and `c = x (1 - x)`, and the first Taylor
coefficient of `QED.ThreeLoopD.i15K` is

  `F₁ = (1 + v²)/u · log (c / P) + (2/x + 2/(1 - x) - (1 + v)) · g`,
  `g = log u - log (1 - v x) - log (u + v x)`.

For fixed `u` it has an explicit primitive in `x` (`QED.ThreeLoopD.i15Phi1`), built from
`t log t` and from

  `L(x) = Li₂ (v x) - Li₂ (v x / (u + v x)) - (log (u + v x) - log u)² / 2`,

whose derivative is `g / x` (`QED.ThreeLoopD.hasDerivAt_i15L1`); `g` is symmetric under
`x ↦ 1 - x`, so `-L(1 - x)` is a primitive of `g / (1 - x)`. Since `L(0) = 0` and
`L(1) = -log² u / 2`, the inner integral is elementary:

  `∫₀¹ F₁ dx = 4 (1 - u) log u - (2 - u)(log u + 2) - 2 log² u`

(`QED.ThreeLoopD.integral_i15F_one_inner`), and its integral over `u` is `-33/4`. Fubini
(`QED.ThreeLoopD.integrable_i15F_real`) joins the two.

## Main results

* `QED.ThreeLoopD.integral_i15F_one`: `∫∫ F₁ = -33/4`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology QED.Polylog

namespace QED.ThreeLoopD

/-! ### The primitive in `x` -/

/-- `(a + b x) log (a + b x)`. -/
noncomputable def i15MLin (a b x : ℝ) : ℝ := (a + b * x) * Real.log (a + b * x)

theorem hasDerivAt_i15MLin {a b x : ℝ} (h : a + b * x ≠ 0) :
    HasDerivAt (i15MLin a b) ((Real.log (a + b * x) + 1) * b) x := by
  have := (Real.hasDerivAt_mul_log h).comp x (((hasDerivAt_id x).const_mul b).const_add a)
  convert this using 1
  · funext y; simp [i15MLin]
  · ring

theorem continuous_i15MLin (a b : ℝ) : Continuous (i15MLin a b) :=
  Real.continuous_mul_log.comp (by fun_prop : Continuous fun x : ℝ => a + b * x)

/-- `L(x) = Li₂ (v x) - Li₂ (v x / (u + v x)) - (log (u + v x) - log u)² / 2`, `v = 1 - u`. -/
noncomputable def i15L1 (u x : ℝ) : ℝ :=
  Li₂ ((1 - u) * x) - Li₂ ((1 - u) * x / (u + (1 - u) * x)) -
    (Real.log (u + (1 - u) * x) - Real.log u) ^ 2 / 2

/-- `g(x) = log u - log (1 - v x) - log (u + v x)`. -/
noncomputable def i15g (u x : ℝ) : ℝ :=
  Real.log u - Real.log (1 + -(1 - u) * x) - Real.log (u + (1 - u) * x)

theorem i15g_one_sub (u x : ℝ) : i15g u (1 - x) = i15g u x := by
  unfold i15g
  rw [show 1 + -(1 - u) * (1 - x) = u + (1 - u) * x by ring,
    show u + (1 - u) * (1 - x) = 1 + -(1 - u) * x by ring]
  ring

theorem hasDerivAt_i15L1 {u x : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i15L1 u) (i15g u x / x) x := by
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨hx0, hx1⟩ := hx
  have hv : 0 < 1 - u := by linarith
  have hvx : 0 < (1 - u) * x := mul_pos hv hx0
  have hvx1 : (1 - u) * x < 1 := by nlinarith
  have hD : 0 < u + (1 - u) * x := by linarith
  have hw0 : 0 < (1 - u) * x / (u + (1 - u) * x) := div_pos hvx hD
  have hw1 : (1 - u) * x / (u + (1 - u) * x) < 1 := by
    rw [div_lt_one hD]; linarith
  have h1 := (hasDerivAt_Li₂ (by rw [abs_of_pos hvx]; exact hvx1) hvx.ne').comp x
    ((hasDerivAt_id x).const_mul (1 - u))
  have hwd : HasDerivAt (fun x => (1 - u) * x / (u + (1 - u) * x))
      (((1 - u) * 1 * (u + (1 - u) * x) - (1 - u) * x * ((1 - u) * 1)) /
        (u + (1 - u) * x) ^ 2) x :=
    ((hasDerivAt_id x).const_mul (1 - u)).div (((hasDerivAt_id x).const_mul (1 - u)).const_add u)
      hD.ne'
  have h2 := (hasDerivAt_Li₂ (by rw [abs_of_pos hw0]; exact hw1) hw0.ne').comp x hwd
  have h3 := (((((hasDerivAt_id x).const_mul (1 - u)).const_add u).log hD.ne').sub_const
    (Real.log u)).pow 2 |>.div_const 2
  have h := (h1.sub h2).sub h3
  convert h using 1
  · funext y; simp [i15L1]
  have e1 : 1 - (1 - u) * x / (u + (1 - u) * x) = u / (u + (1 - u) * x) := by
    field_simp; ring
  simp only [id, e1, Real.log_div hu0.ne' hD.ne']
  unfold i15g
  rw [show 1 + -(1 - u) * x = 1 - (1 - u) * x by ring]
  field_simp
  ring

/-- **The primitive in `x` of `F₁(·, u)`.** -/
noncomputable def i15Phi1 (u x : ℝ) : ℝ :=
  (1 + (1 - u) ^ 2) / u * (i15MLin 0 1 x - i15MLin 1 (-1) x +
      (i15MLin 1 (-(1 - u)) x - i15MLin u (1 - u) x) / (1 - u)) -
    (2 - u) * (x * Real.log u + (i15MLin 1 (-(1 - u)) x - i15MLin u (1 - u) x) / (1 - u) +
      2 * x) +
    2 * i15L1 u x - 2 * i15L1 u (1 - x)

theorem i15F_one_eq {x u : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    i15F 1 (x, u) = (1 + (1 - u) ^ 2) / u * (Real.log (0 + 1 * x) + Real.log (1 + -1 * x) -
        Real.log (1 + -(1 - u) * x) - Real.log (u + (1 - u) * x)) +
      (2 / x + 2 / (1 - x) - (2 - u)) * i15g u x := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hu0, hu1⟩ := hu
  have h1x : 0 < 1 - x := by linarith
  have hv : 0 < 1 - u := by linarith
  have hA : 0 < 1 + -(1 - u) * x := by nlinarith
  have hB : 0 < u + (1 - u) * x := by nlinarith
  have hP : i15P x u = (1 + -(1 - u) * x) * (u + (1 - u) * x) := by
    unfold i15P i9Poly; ring
  unfold i15F i15B1 i15B2 i15g
  rw [Real.log_mul hx0.ne' h1x.ne', hP, Real.log_mul hA.ne' hB.ne']
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, one_mul, zero_add,
    show 1 + -1 * x = 1 - x by ring]
  field_simp
  ring

theorem hasDerivAt_i15Phi1 {u x : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i15Phi1 u) (i15F 1 (x, u)) x := by
  have hx' := hx
  obtain ⟨hx0, hx1⟩ := hx'
  have hu' := hu
  obtain ⟨hu0, hu1⟩ := hu'
  have h1x : (1 - x) ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hv : 0 < 1 - u := by linarith
  have hA : 0 < 1 + -(1 - u) * x := by nlinarith
  have hB : 0 < u + (1 - u) * x := by nlinarith
  have m0 := hasDerivAt_i15MLin (a := 0) (b := 1) (x := x) (by linarith)
  have m1 := hasDerivAt_i15MLin (a := 1) (b := -1) (x := x) (by linarith)
  have m2 := hasDerivAt_i15MLin (a := 1) (b := -(1 - u)) (x := x) hA.ne'
  have m3 := hasDerivAt_i15MLin (a := u) (b := 1 - u) (x := x) hB.ne'
  have l0 := hasDerivAt_i15L1 hu hx
  have l1 := (hasDerivAt_i15L1 hu h1x).comp x ((hasDerivAt_id x).const_sub 1)
  have hlin : HasDerivAt (fun x => x * Real.log u + (i15MLin 1 (-(1 - u)) x -
      i15MLin u (1 - u) x) / (1 - u) + 2 * x)
      (1 * Real.log u + ((Real.log (1 + -(1 - u) * x) + 1) * -(1 - u) -
        (Real.log (u + (1 - u) * x) + 1) * (1 - u)) / (1 - u) + 2 * 1) x :=
    (((hasDerivAt_id x).mul_const (Real.log u)).add ((m2.sub m3).div_const (1 - u))).add
      ((hasDerivAt_id x).const_mul 2)
  have h := ((((m0.sub m1).add ((m2.sub m3).div_const (1 - u))).const_mul
    ((1 + (1 - u) ^ 2) / u)).sub (hlin.const_mul (2 - u))).add (l0.const_mul 2) |>.sub
    (l1.const_mul 2)
  convert h using 1
  · funext y
    simp only [i15Phi1, Function.comp_def, Pi.add_apply, Pi.sub_apply]
  · rw [i15F_one_eq hx hu]
    simp only [i15g_one_sub]
    unfold i15g
    field_simp
    ring

/-! ### The inner integral -/

theorem continuousOn_i15L1 {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : ContinuousOn (i15L1 u) (Icc 0 1) := by
  obtain ⟨hu0, hu1⟩ := hu
  have hv : 0 < 1 - u := by linarith
  have hD : ∀ x ∈ Icc (0 : ℝ) 1, 0 < u + (1 - u) * x := fun x hx => by nlinarith [hx.1]
  have hw : ContinuousOn (fun x => (1 - u) * x / (u + (1 - u) * x)) (Icc 0 1) :=
    (by fun_prop : Continuous fun x : ℝ => (1 - u) * x).continuousOn.div
      (by fun_prop : Continuous fun x : ℝ => u + (1 - u) * x).continuousOn
      fun x hx => (hD x hx).ne'
  have h1 : ContinuousOn (fun x => Li₂ ((1 - u) * x)) (Icc 0 1) :=
    continuousOn_Li₂.comp (by fun_prop : Continuous fun x : ℝ => (1 - u) * x).continuousOn
      fun x hx => ⟨by nlinarith [hx.1], by nlinarith [hx.2, hx.1]⟩
  have h2 : ContinuousOn (fun x => Li₂ ((1 - u) * x / (u + (1 - u) * x))) (Icc 0 1) :=
    continuousOn_Li₂.comp hw fun x hx => by
      have := hD x hx
      constructor
      · exact le_trans (by norm_num) (div_nonneg (by nlinarith [hx.1]) this.le)
      · rw [div_le_one this]; linarith
  have h3 : ContinuousOn (fun x => (Real.log (u + (1 - u) * x) - Real.log u) ^ 2 / 2)
      (Icc 0 1) :=
    ((((by fun_prop : Continuous fun x : ℝ => u + (1 - u) * x).continuousOn.log
      fun x hx => (hD x hx).ne').sub continuousOn_const).pow 2).div_const 2
  exact (h1.sub h2).sub h3

theorem continuousOn_i15Phi1 {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (i15Phi1 u) (Icc 0 1) := by
  have hm : ∀ a b : ℝ, ContinuousOn (i15MLin a b) (Icc 0 1) := fun a b =>
    (continuous_i15MLin a b).continuousOn
  have hL := continuousOn_i15L1 hu
  have hL' : ContinuousOn (fun x => i15L1 u (1 - x)) (Icc 0 1) :=
    hL.comp (by fun_prop : Continuous fun x : ℝ => 1 - x).continuousOn
      fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩
  unfold i15Phi1
  exact (((continuousOn_const.mul (((hm 0 1).sub (hm 1 (-1))).add
    (((hm _ _).sub (hm _ _)).div_const _))).sub (continuousOn_const.mul
    (((continuousOn_id.mul continuousOn_const).add (((hm _ _).sub (hm _ _)).div_const _)).add
      (continuousOn_const.mul continuousOn_id)))).add (continuousOn_const.mul hL)).sub
    (continuousOn_const.mul hL')

/-- The inner integral `4 (1 - u) log u - (2 - u)(log u + 2) - 2 log² u`. -/
noncomputable def i15h1 (u : ℝ) : ℝ :=
  4 * (1 - u) * Real.log u - (2 - u) * (Real.log u + 2) - 2 * Real.log u ^ 2

theorem i15Phi1_sub {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    i15Phi1 u 1 - i15Phi1 u 0 = i15h1 u := by
  obtain ⟨hu0, hu1⟩ := hu
  have hv : (1 - u) ≠ 0 := by linarith
  simp only [i15Phi1, i15L1, i15MLin, mul_one, mul_zero, add_zero, sub_self, sub_zero,
    zero_add, Real.log_one, zero_div, Li₂_zero, Real.log_zero, one_mul]
  simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  unfold i15h1
  field_simp
  ring_nf
  simp only [Real.log_one]
  ring

/-- **The inner integral of `F₁`.** -/
theorem integral_i15F_one_inner {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hint : IntegrableOn (fun x => i15F 1 (x, u)) (Ioo 0 1)) :
    ∫ x in Ioo (0 : ℝ) 1, i15F 1 (x, u) = i15h1 u := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one (continuousOn_i15Phi1 hu)
      (fun x hx => hasDerivAt_i15Phi1 hu hx)
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hint)]
  exact i15Phi1_sub hu

/-! ### The outer integral -/

/-- A primitive of `i15h1`. -/
noncomputable def i15Psi1 (u : ℝ) : ℝ :=
  6 * (u * Real.log u) - 10 * u - 3 / 2 * (u * (u * Real.log u)) + 7 / 4 * (u * u) -
    2 * (u * Real.log u ^ 2)

theorem integral_i15h1 (hI : IntervalIntegrable i15h1 volume 0 1) :
    ∫ u in (0 : ℝ)..1, i15h1 u = -33 / 4 := by
  have hd : ∀ u ∈ Ioo (0 : ℝ) 1, HasDerivAt i15Psi1 (i15h1 u) u := fun u hu => by
    have hl := Real.hasDerivAt_log hu.1.ne'
    have hul := (hasDerivAt_id u).mul hl
    have h := (((((hul.const_mul 6).sub ((hasDerivAt_id u).const_mul 10)).sub
      (((hasDerivAt_id u).mul hul).const_mul (3 / 2))).add
      (((hasDerivAt_id u).mul (hasDerivAt_id u)).const_mul (7 / 4))).sub
      (((hasDerivAt_id u).mul (hl.pow 2)).const_mul 2))
    convert h using 1
    · funext y; simp [i15Psi1]
    · have hu0 : u ≠ 0 := hu.1.ne'
      unfold i15h1
      simp only [id, Pi.mul_apply, Pi.pow_apply]
      field_simp
      ring
  have ha : Tendsto (fun u : ℝ => u * Real.log u) (𝓝[>] 0) (𝓝 0) := by
    have := Real.continuous_mul_log.tendsto 0
    simp only [zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hb : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hc : Tendsto (fun u : ℝ => u * Real.log u ^ 2) (𝓝[>] 0) (𝓝 0) :=
    tendsto_mul_log_sq_of_abs_le (C := 1) (eventually_mem_nhdsWithin.mono fun x hx => by
      rw [abs_of_pos (mem_Ioi.mp hx)]; linarith)
  have h0 : Tendsto i15Psi1 (𝓝[>] 0) (𝓝 0) := by
    have h := ((((ha.const_mul 6).sub (hb.const_mul 10)).sub ((hb.mul ha).const_mul (3 / 2))).add
      ((hb.mul hb).const_mul (7 / 4))).sub (hc.const_mul 2)
    simp only [mul_zero, sub_zero, add_zero] at h
    exact h
  have h1 : Tendsto i15Psi1 (𝓝[<] 1) (𝓝 (-33 / 4)) := by
    have hc1 : ContinuousAt i15Psi1 1 := by
      unfold i15Psi1
      have := Real.continuousAt_log (one_ne_zero (α := ℝ))
      fun_prop
    have := hc1.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
    convert this using 2
    simp [i15Psi1]
    norm_num
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one hd hI h0 h1]
  norm_num

/-! ### Fubini -/

/-- **`∫∫ F₁ = -33/4`.** -/
theorem integral_i15F_one : ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15F 1 z = -33 / 4 := by
  have hF := integrable_i15F_real (k := 1) (by norm_num)
  rw [volume_restrict_prod2] at hF ⊢
  rw [integral_prod_symm _ hF]
  have hae : (fun u => ∫ x, i15F 1 (x, u) ∂volume.restrict (Ioo (0 : ℝ) 1)) =ᵐ[volume.restrict
      (Ioo (0 : ℝ) 1)] i15h1 := by
    filter_upwards [hF.prod_left_ae, ae_restrict_mem measurableSet_Ioo] with u hu1 hu2
    exact integral_i15F_one_inner hu2 hu1
  rw [integral_congr_ae hae, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one]
  refine integral_i15h1 ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr ?_)
  exact hF.integral_prod_right.congr hae

/-- **The target expansion of `K` from `∫ F₂`, `∫ F₃`, `∫ F₄`** (`∫ F₀`, `∫ F₁` are proved). -/
theorem hasTruncLaurent_i15K_of_coeffs_two
    (h2 : ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15F 2 z =
      35 / 12 * Real.pi ^ 2 + 4 * QED.Polylog.zeta3 - 251 / 8)
    (h3 : ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15F 3 z =
      -16 * Real.pi ^ 2 * Real.log 2 + 107 / 8 * Real.pi ^ 2 + 61 * QED.Polylog.zeta3 - 1665 / 16)
    (h4 : ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15F 4 z =
      384 * QED.Polylog.Li 4 (1 / 2) + 16 * Real.log 2 ^ 4
        + 32 * Real.pi ^ 2 * Real.log 2 ^ 2 - 72 * Real.pi ^ 2 * Real.log 2
        - 253 / 80 * Real.pi ^ 4 - 2 / 3 * Real.pi ^ 2 * QED.Polylog.zeta3
        + 2267 / 48 * Real.pi ^ 2 + 503 / 2 * QED.Polylog.zeta3 + 12 * QED.Polylog.zeta5
        - 10403 / 32) :
    HasTruncLaurent i15K i15KLaurent 5 :=
  hasTruncLaurent_i15K_of_coeffs integral_i15F_one h2 h3 h4

end QED.ThreeLoopD
