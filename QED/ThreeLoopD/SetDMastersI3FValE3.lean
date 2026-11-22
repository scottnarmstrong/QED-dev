/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI3FValPhoton
public import QED.TwoLoop.UnitXCloseDilog

/-!
# Set (d), master `I₃`: the `e₃`-integral of `f₂` in closed form

Continuing `QED.ThreeLoopD.i3FInt_zero_eq_lintegral_f2`, the integral of
`f₂(c, e₁, e₃)` over `e₃ ∈ (0, ∞)` is evaluated in closed form, with `c = x (1 - x)`. Write
`y = 1 - x`, `q = c e₁ / (c + e₁)`, `p = c / e₁`, `A = c + e₁ + e₁²`. In `e₃ = t`, `f₂` has
poles only at `t = 0`, `t = -q` and the removable point `t = p`, and its logarithms are
`log (t + a)` for `a ∈ {c, x, y, 1 + e₁, q}` (`c + t + t² = (t + x)(t + y)`). Partial fractions
give

  `c e₁ f₂ = (q/e₁)(L_c - L_x - L_y)/(t + q) - (q/c) L_{1+e₁}/(t + q) - K/(t + q)`
  `        + (log (1 + t/x) + log (1 + t/y) - log (1 + t/c))/t`
  `        + Σ_a ± log ((t + a)/(p + a))/(t - p)`,

`L_a = log (t + a)`, `K = log (c + e₁) - log A`, the last sum over `a = 1 + e₁, q`
(sign `+`) and `a = x, y` (sign `-`). Each term has a dilogarithmic primitive, with the
dilogarithm `dilogI` on `(-∞, 1)` (`QED.TwoLoop.UnitXClose.dilogI`):

* `log (t + a)/(t + q)`: `log² (t + q)/2 + dilogI ((q - a)/(t + q))` (`i3EF`);
* `log (1 + t/a)/t`: `-dilogI (-t/a)` (`i3EZ`);
* `log ((t + a)/(p + a))/(t - p)`: `-dilogI ((p - t)/(p + a))` (`i3EW`), smooth across `t = p`.

Their sum `i3EP` has derivative `i3EH`, which equals `c e₁ f₂` off `t = p` (`i3EH_eq`) and is
continuous, hence nonnegative everywhere on `(0, ∞)`. The limit at `∞` (`tendsto_i3EP`) uses
the inversion formula `dilogI (-X) + dilogI (-1/X) = -π²/6 - log² X/2`
(`i3E_dilogI_inv`); the `log² t` and `log t` terms cancel by `q/e₁ + q/c = 1` and the residue
relation `(p + 1 + e₁)(p + q)(c + e₁) = (p + x)(p + y) A` (`i3E_log_res`), leaving

  `L = π²/6 - log x log y + (log² (p + 1 + e₁) + log² (p + q) - log² (p + x) - log² (p + y))/2`.

## Main results

* `QED.ThreeLoopD.i3V_lintegral_e3`:
  `∫₀^∞ f₂(x (1 - x), e₁, e₃) de₃ = g(x, e₁) = (L - P(0)) / (x (1 - x) e₁)` (`i3VG`).
* `QED.ThreeLoopD.i3FInt_zero_eq_lintegral_g`: `i3FInt 0 = ∫₀¹ dx ∫₀^∞ de₁ g(x, e₁)`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology
open scoped ENNReal
open QED.TwoLoop.UnitXClose

namespace QED.ThreeLoopD

theorem i3E_hasDerivAt_dilogI_comp {f : ℝ → ℝ} {f' t : ℝ} (hf : HasDerivAt f f' t)
    (h1 : f t < 1) : HasDerivAt (fun y => dilogI (f y)) (-dilogKer (f t) * f') t :=
  (hasDerivAt_dilogI h1).comp t hf

theorem i3E_dilogI_neg_one : dilogI (-1) = -π ^ 2 / 12 := by
  have h1 : Tendsto dilogI (𝓝[>] (-1)) (𝓝 (dilogI (-1))) :=
    ((hasDerivAt_dilogI (by norm_num)).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto QED.Polylog.Li₂ (𝓝[>] (-1)) (𝓝 (QED.Polylog.Li₂ (-1))) := by
    exact ((QED.Polylog.continuousOn_Li₂ (-1) (by norm_num)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGT (by norm_num))).tendsto
  have h3 : dilogI =ᶠ[𝓝[>] (-1)] QED.Polylog.Li₂ := by
    filter_upwards [Ioo_mem_nhdsGT (show (-1 : ℝ) < 1 by norm_num)] with y hy
    exact dilogI_eq_Li₂ hy
  rw [tendsto_nhds_unique (h1.congr' h3) h2, QED.Polylog.Li₂_neg_one]


/-- **Inversion**: `dilogI (-X) + dilogI (-1/X) = -π²/6 - log² X / 2` for `X > 0`. -/
theorem i3E_dilogI_inv {X : ℝ} (hX : 0 < X) :
    dilogI (-X) + dilogI (-(1 / X)) = -π ^ 2 / 6 - log X ^ 2 / 2 := by
  have hd : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt
      (fun y => dilogI (-y) + dilogI (-(1 / y)) + log y ^ 2 / 2) 0 y := by
    intro y (hy : 0 < y)
    have hf1 : HasDerivAt (fun z : ℝ => -z) (-1) y := (hasDerivAt_id y).neg
    have hf2 : HasDerivAt (fun z : ℝ => -(1 / z)) (1 / y ^ 2) y := by
      have := ((hasDerivAt_const y (1 : ℝ)).div (hasDerivAt_id y) hy.ne').neg
      refine this.congr_deriv ?_
      simp only [id]; field_simp; ring
    have h1 := i3E_hasDerivAt_dilogI_comp hf1 (by linarith)
    have h2 := i3E_hasDerivAt_dilogI_comp hf2
      (show -(1 / y) < 1 by have : 0 < 1 / y := by positivity
                            linarith)
    have h3 := ((hasDerivAt_log hy.ne').pow 2).div_const 2
    refine ((h1.add h2).add h3).congr_deriv ?_
    have hy1 : -y ≠ 0 := by simp [hy.ne']
    have hy2 : -(1 / y) ≠ 0 := by simp [hy.ne']
    simp only [dilogKer, hy1, hy2, ite_false]
    have e : 1 - -(1 / y) = (1 + y) / y := by field_simp; ring
    rw [e, log_div (by positivity) hy.ne', show 1 - -y = 1 + y by ring]
    field_simp
    ring
  have key := isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hd y hy).deriv) (show X ∈ Ioi (0 : ℝ) from hX)
    (show (1 : ℝ) ∈ Ioi (0 : ℝ) by norm_num)
  simp only [div_one, log_one, i3E_dilogI_neg_one] at key
  linarith

/-- Primitive of `log (t + a) / (t + q)`. -/
noncomputable def i3EF (q a t : ℝ) : ℝ := log (t + q) ^ 2 / 2 + dilogI ((q - a) / (t + q))

/-- Primitive of `log (1 + t / a) / t`. -/
noncomputable def i3EZ (a t : ℝ) : ℝ := -dilogI (-(t / a))

/-- Primitive of `log ((t + a) / (p + a)) / (t - p)`. -/
noncomputable def i3EW (p a t : ℝ) : ℝ := -dilogI ((p - t) / (p + a))

theorem hasDerivAt_i3EF {q a t : ℝ} (hq : 0 < q) (ha : 0 < a) (hqa : q ≠ a) (ht : 0 ≤ t) :
    HasDerivAt (i3EF q a) (log (t + a) / (t + q)) t := by
  have htq : 0 < t + q := by linarith
  have hu : HasDerivAt (fun y => (q - a) / (y + q)) (-(q - a) / (t + q) ^ 2) t := by
    have := (hasDerivAt_const t (q - a)).div ((hasDerivAt_id t).add_const q) htq.ne'
    refine this.congr_deriv ?_
    simp only [id]; ring
  have hu1 : (q - a) / (t + q) < 1 := by rw [div_lt_one htq]; linarith
  have h1 := i3E_hasDerivAt_dilogI_comp hu hu1
  have h2 := (((hasDerivAt_id t).add_const q).log htq.ne').pow 2 |>.div_const 2
  refine (h2.add h1).congr_deriv ?_
  have hne : (q - a) / (t + q) ≠ 0 := div_ne_zero (sub_ne_zero.2 hqa) htq.ne'
  have hta : 0 < t + a := by linarith
  have e : 1 - (q - a) / (t + q) = (t + a) / (t + q) := by field_simp; ring
  simp only [dilogKer, hne, ite_false, id, e]
  rw [log_div hta.ne' htq.ne']
  have : q - a ≠ 0 := sub_ne_zero.2 hqa
  field_simp
  ring

theorem hasDerivAt_i3EZ {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    HasDerivAt (i3EZ a) (-dilogKer (-(t / a)) / a) t := by
  have hu : HasDerivAt (fun y => -(y / a)) (-(1 / a)) t :=
    ((hasDerivAt_id t).div_const a).neg
  have h0 : 0 ≤ t / a := div_nonneg ht ha.le
  have hu1 : -(t / a) < 1 := by linarith
  refine (i3E_hasDerivAt_dilogI_comp hu hu1).neg.congr_deriv ?_
  ring

theorem hasDerivAt_i3EW {p a t : ℝ} (hpa : 0 < p + a) (ha : 0 < a) (ht : 0 ≤ t) :
    HasDerivAt (i3EW p a) (-dilogKer ((p - t) / (p + a)) / (p + a)) t := by
  have hu : HasDerivAt (fun y => (p - y) / (p + a)) (-(1 / (p + a))) t := by
    have := ((hasDerivAt_id t).const_sub p).div_const (p + a)
    refine this.congr_deriv ?_
    ring
  have hu1 : (p - t) / (p + a) < 1 := by
    rw [div_lt_one hpa]; linarith
  refine (i3E_hasDerivAt_dilogI_comp hu hu1).neg.congr_deriv ?_
  ring


/-- The `e₃`-primitive of `c e₁ f₂`, `c = x (1 - x)`, `q = c e₁/(c + e₁)`, `p = c/e₁`. -/
noncomputable def i3EP (x e1 t : ℝ) : ℝ :=
  x * (1 - x) * e1 / (x * (1 - x) + e1) / e1 * (i3EF (x * (1 - x) * e1 / (x * (1 - x) + e1))
      (x * (1 - x)) t - i3EF (x * (1 - x) * e1 / (x * (1 - x) + e1)) x t -
      i3EF (x * (1 - x) * e1 / (x * (1 - x) + e1)) (1 - x) t) -
    x * (1 - x) * e1 / (x * (1 - x) + e1) / (x * (1 - x)) *
      i3EF (x * (1 - x) * e1 / (x * (1 - x) + e1)) (1 + e1) t -
    (log (x * (1 - x) + e1) - log (x * (1 - x) + e1 + e1 ^ 2)) *
      log (t + x * (1 - x) * e1 / (x * (1 - x) + e1)) +
    (i3EZ x t + i3EZ (1 - x) t - i3EZ (x * (1 - x)) t) +
    (i3EW (x * (1 - x) / e1) (1 + e1) t +
      i3EW (x * (1 - x) / e1) (x * (1 - x) * e1 / (x * (1 - x) + e1)) t -
      i3EW (x * (1 - x) / e1) x t - i3EW (x * (1 - x) / e1) (1 - x) t)

/-- The derivative of `i3EP` in `t`: `c e₁ f₂`, extended continuously to `t = p`. -/
noncomputable def i3EH (x e1 t : ℝ) : ℝ :=
  x * (1 - x) * e1 / (x * (1 - x) + e1) / e1 *
      (log (t + x * (1 - x)) / (t + x * (1 - x) * e1 / (x * (1 - x) + e1)) -
        log (t + x) / (t + x * (1 - x) * e1 / (x * (1 - x) + e1)) -
        log (t + (1 - x)) / (t + x * (1 - x) * e1 / (x * (1 - x) + e1))) -
    x * (1 - x) * e1 / (x * (1 - x) + e1) / (x * (1 - x)) *
      (log (t + (1 + e1)) / (t + x * (1 - x) * e1 / (x * (1 - x) + e1))) -
    (log (x * (1 - x) + e1) - log (x * (1 - x) + e1 + e1 ^ 2)) *
      (1 / (t + x * (1 - x) * e1 / (x * (1 - x) + e1))) +
    (-dilogKer (-(t / x)) / x + -dilogKer (-(t / (1 - x))) / (1 - x) -
      -dilogKer (-(t / (x * (1 - x)))) / (x * (1 - x))) +
    (-dilogKer ((x * (1 - x) / e1 - t) / (x * (1 - x) / e1 + (1 + e1))) /
        (x * (1 - x) / e1 + (1 + e1)) +
      -dilogKer ((x * (1 - x) / e1 - t) / (x * (1 - x) / e1 +
        x * (1 - x) * e1 / (x * (1 - x) + e1))) /
        (x * (1 - x) / e1 + x * (1 - x) * e1 / (x * (1 - x) + e1)) -
      -dilogKer ((x * (1 - x) / e1 - t) / (x * (1 - x) / e1 + x)) / (x * (1 - x) / e1 + x) -
      -dilogKer ((x * (1 - x) / e1 - t) / (x * (1 - x) / e1 + (1 - x))) /
        (x * (1 - x) / e1 + (1 - x)))

theorem hasDerivAt_i3EP {x e1 t : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (he1 : 0 < e1) (ht : 0 ≤ t) :
    HasDerivAt (i3EP x e1) (i3EH x e1 t) t := by
  obtain ⟨hx0, hx1⟩ := hx
  have h1x : 0 < 1 - x := by linarith
  have hc : 0 < x * (1 - x) := mul_pos hx0 h1x
  have hq : 0 < x * (1 - x) * e1 / (x * (1 - x) + e1) := by positivity
  have hqlt : ∀ a, x * (1 - x) ≤ a → x * (1 - x) * e1 / (x * (1 - x) + e1) ≠ a := by
    intro a ha h
    have : x * (1 - x) * e1 / (x * (1 - x) + e1) < x * (1 - x) := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  have hxc : x * (1 - x) ≤ x := by nlinarith
  have hxc' : x * (1 - x) ≤ 1 - x := by nlinarith
  have hxc'' : x * (1 - x) ≤ 1 + e1 := by nlinarith
  have hp : 0 < x * (1 - x) / e1 := by positivity
  have hF := fun a (ha : 0 < a) (hca : x * (1 - x) ≤ a) => hasDerivAt_i3EF hq ha (hqlt a hca) ht
  have hlog : HasDerivAt (fun t => log (t + x * (1 - x) * e1 / (x * (1 - x) + e1)))
      (1 / (t + x * (1 - x) * e1 / (x * (1 - x) + e1))) t := by
    have := ((hasDerivAt_id t).add_const (x * (1 - x) * e1 / (x * (1 - x) + e1))).log
      (by simp only [id]; positivity)
    simpa using this
  have := (((((hF _ hc le_rfl).sub (hF _ hx0 hxc)).sub (hF _ h1x hxc')).const_mul
    (x * (1 - x) * e1 / (x * (1 - x) + e1) / e1)).sub
    ((hF _ (by positivity) hxc'').const_mul (x * (1 - x) * e1 / (x * (1 - x) + e1) /
      (x * (1 - x))))).sub (hlog.const_mul
        (log (x * (1 - x) + e1) - log (x * (1 - x) + e1 + e1 ^ 2))) |>.add
    (((hasDerivAt_i3EZ hx0 ht).add (hasDerivAt_i3EZ h1x ht)).sub (hasDerivAt_i3EZ hc ht)) |>.add
    ((((hasDerivAt_i3EW (p := x * (1 - x) / e1) (a := 1 + e1) (by positivity)
      (by positivity) ht).add
      (hasDerivAt_i3EW (p := x * (1 - x) / e1) (by positivity) hq ht)).sub
      (hasDerivAt_i3EW (p := x * (1 - x) / e1) (by positivity) hx0 ht)).sub
        (hasDerivAt_i3EW (p := x * (1 - x) / e1) (by positivity) h1x ht))
  convert this using 1
  · ext y; simp only [i3EP, Pi.add_apply, Pi.sub_apply]
  · simp only [i3EH]

theorem i3E_dilogKer_neg_div {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    -dilogKer (-(t / a)) / a = (log (t + a) - log a) / t := by
  have hne : -(t / a) ≠ 0 := by simp [ht.ne', ha.ne']
  simp only [dilogKer, hne, ite_false]
  rw [show 1 - -(t / a) = (t + a) / a by field_simp; ring, log_div (by positivity) ha.ne']
  field_simp

theorem i3E_dilogKer_sub_div {p a t : ℝ} (hpa : 0 < p + a) (hta : 0 < t + a) (hpt : p ≠ t) :
    -dilogKer ((p - t) / (p + a)) / (p + a) = (log (t + a) - log (p + a)) / (t - p) := by
  have hne : (p - t) / (p + a) ≠ 0 := div_ne_zero (sub_ne_zero.2 hpt) hpa.ne'
  simp only [dilogKer, hne, ite_false]
  rw [show 1 - (p - t) / (p + a) = (t + a) / (p + a) by field_simp; ring,
    log_div hta.ne' hpa.ne']
  have : t - p ≠ 0 := sub_ne_zero.2 hpt.symm
  have : p - t ≠ 0 := sub_ne_zero.2 hpt
  field_simp
  ring

theorem i3EH_eq {x e1 t : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (he1 : 0 < e1) (ht : 0 < t)
    (hm : x * (1 - x) ≠ e1 * t) :
    i3EH x e1 t = x * (1 - x) * e1 * i3VF2 (x * (1 - x)) e1 t := by
  obtain ⟨hx0, hx1⟩ := hx
  have hpt : x * (1 - x) / e1 ≠ t := by
    intro h; apply hm; rw [← h]; field_simp
  have hy0 : 0 < 1 - x := by linarith
  simp only [i3EH]
  rw [i3E_dilogKer_neg_div hx0 ht, i3E_dilogKer_neg_div hy0 ht,
    i3E_dilogKer_neg_div (mul_pos hx0 hy0) ht,
    i3E_dilogKer_sub_div (by positivity) (by positivity) hpt,
    i3E_dilogKer_sub_div (by positivity) (by positivity) hpt,
    i3E_dilogKer_sub_div (by positivity) (by positivity) hpt,
    i3E_dilogKer_sub_div (by positivity) (by positivity) hpt]
  simp only [i3VF2, i3VLI, i3VDel]
  set y := 1 - x with hy
  have hxy : x + y = 1 := by rw [hy]; ring
  set c := x * y with hc
  have hc0 : 0 < c := mul_pos hx0 hy0
  set D := c * (e1 + t) + e1 * t with hD
  have hD0 : 0 < D := by positivity
  have hq : t + c * e1 / (c + e1) = D / (c + e1) := by rw [hD]; field_simp; ring
  rw [hq]
  have hA : 0 < c + e1 + e1 ^ 2 := by positivity
  have hpe : c / e1 + (1 + e1) = (c + e1 + e1 ^ 2) / e1 := by
    field_simp; ring
  have hpq : c / e1 + c * e1 / (c + e1) = c * (c + e1 + e1 ^ 2) / (e1 * (c + e1)) := by
    field_simp
  have hpx : c / e1 + x = x * (y + e1) / e1 := by rw [hc]; field_simp
  have hpy : c / e1 + y = y * (x + e1) / e1 := by rw [hc]; field_simp
  have hAf : c + e1 + e1 ^ 2 = (x + e1) * (y + e1) := by rw [hc]; linear_combination e1 * hxy
  rw [show 1 * D - (c + t) * e1 = c * t by rw [hD]; ring,
    show (c + e1 + e1 ^ 2) * D - (1 + e1 + t) * D * e1 = (c - e1 * t) * D by rw [hD]; ring,
    show 1 * D - (c + t + t ^ 2) * e1 = t * (c - e1 * t) by rw [hD]; ring,
    show (c + e1) * D - D * e1 = c * D by ring,
    show c + t + t ^ 2 = (t + x) * (t + y) by rw [hc]; linear_combination (-t) * hxy,
    add_comm c t, show 1 + e1 + t = t + (1 + e1) by ring, hpe, hpq, hpx, hpy]
  have ht1 : (t + (1 + e1)) ≠ 0 := by positivity
  have htc : (t + c) ≠ 0 := by positivity
  have htx : (t + x) ≠ 0 := by positivity
  have hty : (t + y) ≠ 0 := by positivity
  have hce : (c + e1) ≠ 0 := by positivity
  have hxe : (x + e1) ≠ 0 := by positivity
  have hye : (y + e1) ≠ 0 := by positivity
  simp only [log_mul, log_div, ne_eq, mul_eq_zero, hD0.ne', he1.ne',
    hA.ne', ht1, htc, htx, hty, hce, hxe, hye, hx0.ne', hy0.ne', hc0.ne', not_false_eq_true,
    one_mul, or_self]
  have hlc : log c = log x + log y := by rw [hc, log_mul hx0.ne' hy0.ne']
  have hlA : log (c + e1 + e1 ^ 2) = log (x + e1) + log (y + e1) := by
    rw [hAf, log_mul hxe hye]
  rw [hlc, hlA]
  have hct : c - e1 * t ≠ 0 := sub_ne_zero.2 hm
  have htp : t - c / e1 ≠ 0 := sub_ne_zero.2 hpt.symm
  rw [show t - c / e1 = -(c - e1 * t) / e1 by field_simp; ring]
  generalize log (t + c) = L1 at *
  generalize log (t + x) = L2 at *
  generalize log (t + y) = L3 at *
  generalize log (t + (1 + e1)) = L4 at *
  generalize log D = L5 at *
  field_simp
  ring

/-- A combination of `i3VLI` with a nonnegative log-combination is nonnegative. -/
theorem i3E_LI4_nonneg {α₁ β₁ α₂ β₂ α₃ β₃ α₄ β₄ γ δ : ℝ} (hα₁ : 0 < α₁) (hβ₁ : 0 < β₁)
    (hα₂ : 0 < α₂) (hβ₂ : 0 < β₂) (hα₃ : 0 < α₃) (hβ₃ : 0 < β₃) (hα₄ : 0 < α₄) (hβ₄ : 0 < β₄)
    (hγ : 0 < γ) (hδ : 0 < δ) (hK₁ : α₁ * δ - β₁ * γ ≠ 0) (hK₂ : α₂ * δ - β₂ * γ ≠ 0)
    (hK₃ : α₃ * δ - β₃ * γ ≠ 0) (hK₄ : α₄ * δ - β₄ * γ ≠ 0)
    (hpos : ∀ x, 0 < x → 0 ≤ log (α₁ * x + β₁) + log (α₂ * x + β₂) - log (α₃ * x + β₃) -
      log (α₄ * x + β₄)) :
    0 ≤ i3VLI α₁ β₁ γ δ + i3VLI α₂ β₂ γ δ - i3VLI α₃ β₃ γ δ - i3VLI α₄ β₄ γ δ := by
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun x => i3VPrim α₁ β₁ γ δ x + i3VPrim α₂ β₂ γ δ x -
      i3VPrim α₃ β₃ γ δ x - i3VPrim α₄ β₄ γ δ x) ((log (α₁ * x + β₁) + log (α₂ * x + β₂) -
        log (α₃ * x + β₃) - log (α₄ * x + β₄)) / (γ * x + δ) ^ 2) x := by
    intro x hx
    refine ((((hasDerivAt_i3VPrim hα₁ hβ₁ hγ hδ hK₁ hx).add
      (hasDerivAt_i3VPrim hα₂ hβ₂ hγ hδ hK₂ hx)).sub
        (hasDerivAt_i3VPrim hα₃ hβ₃ hγ hδ hK₃ hx)).sub
          (hasDerivAt_i3VPrim hα₄ hβ₄ hγ hδ hK₄ hx)).congr_deriv ?_
    ring
  have hp : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ (log (α₁ * x + β₁) + log (α₂ * x + β₂) -
      log (α₃ * x + β₃) - log (α₄ * x + β₄)) / (γ * x + δ) ^ 2 :=
    fun x hx => div_nonneg (hpos x hx) (sq_nonneg _)
  have hl := (((tendsto_i3VPrim (β := β₁) (δ := δ) hα₁ hγ).add
    (tendsto_i3VPrim (β := β₂) (δ := δ) hα₂ hγ)).sub
      (tendsto_i3VPrim (β := β₃) (δ := δ) hα₃ hγ)).sub
        (tendsto_i3VPrim (β := β₄) (δ := δ) hα₄ hγ)
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' hd hp hl
  have h0 := setIntegral_nonneg (μ := volume) measurableSet_Ioi hp
  rw [h] at h0
  rw [← i3VLI_eq hα₁ hβ₁ hγ hδ, ← i3VLI_eq hα₂ hβ₂ hγ hδ, ← i3VLI_eq hα₃ hβ₃ hγ hδ,
    ← i3VLI_eq hα₄ hβ₄ hγ hδ]
  linarith

/-- `f₂ ≥ 0` off the null set `c = e₁ e₃`. -/
theorem i3E_F2_nonneg {c e1 e3 : ℝ} (hc : 0 < c) (he1 : 0 < e1) (he3 : 0 < e3)
    (hm : c ≠ e1 * e3) : 0 ≤ i3VF2 c e1 e3 := by
  have hδ : 0 < i3VDel c e1 e3 := by unfold i3VDel; positivity
  have hm' : c - e1 * e3 ≠ 0 := sub_ne_zero.2 hm
  have k1 : 1 * i3VDel c e1 e3 - (c + e3) * e1 ≠ 0 := by
    rw [show 1 * i3VDel c e1 e3 - (c + e3) * e1 = c * e3 by unfold i3VDel; ring]; positivity
  have k2 : (c + e1 + e1 ^ 2) * i3VDel c e1 e3 - (1 + e1 + e3) * i3VDel c e1 e3 * e1 ≠ 0 := by
    rw [show (c + e1 + e1 ^ 2) * i3VDel c e1 e3 - (1 + e1 + e3) * i3VDel c e1 e3 * e1 =
      (c - e1 * e3) * i3VDel c e1 e3 by ring]
    exact mul_ne_zero hm' hδ.ne'
  have k3 : 1 * i3VDel c e1 e3 - (c + e3 + e3 ^ 2) * e1 ≠ 0 := by
    rw [show 1 * i3VDel c e1 e3 - (c + e3 + e3 ^ 2) * e1 = e3 * (c - e1 * e3) by
      unfold i3VDel; ring]
    exact mul_ne_zero he3.ne' hm'
  have k4 : (c + e1) * i3VDel c e1 e3 - i3VDel c e1 e3 * e1 ≠ 0 := by
    rw [show (c + e1) * i3VDel c e1 e3 - i3VDel c e1 e3 * e1 = c * i3VDel c e1 e3 by ring]
    positivity
  exact i3E_LI4_nonneg one_pos (by positivity) (by positivity) (by positivity) one_pos
    (by positivity) (by positivity) hδ he1 hδ k1 k2 k3 k4
    fun x hx => i3V_log_comb_nonneg hc he1 hx he3

theorem i3E_continuousAt_dilogKer_comp {g : ℝ → ℝ} {t : ℝ} (hg : Continuous g) (h : g t < 1) :
    ContinuousAt (fun s => dilogKer (g s)) t :=
  (continuousOn_dilogKer.continuousAt (Iio_mem_nhds h)).comp hg.continuousAt

theorem continuousAt_i3EH {x e1 t : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (he1 : 0 < e1) (ht : 0 < t) :
    ContinuousAt (i3EH x e1) t := by
  obtain ⟨hx0, hx1⟩ := hx
  have hy0 : 0 < 1 - x := by linarith
  have hc : 0 < x * (1 - x) := mul_pos hx0 hy0
  have hq : 0 < x * (1 - x) * e1 / (x * (1 - x) + e1) := by positivity
  have hp : 0 < x * (1 - x) / e1 := by positivity
  have k1 := i3E_continuousAt_dilogKer_comp (g := fun s => -(s / x)) (t := t) (by fun_prop)
    (by have : 0 < t / x := by positivity
        linarith)
  have k2 := i3E_continuousAt_dilogKer_comp (g := fun s => -(s / (1 - x))) (t := t)
    (by fun_prop) (by have : 0 < t / (1 - x) := by positivity
                      linarith)
  have k3 := i3E_continuousAt_dilogKer_comp (g := fun s => -(s / (x * (1 - x)))) (t := t)
    (by fun_prop) (by have : 0 < t / (x * (1 - x)) := by positivity
                      linarith)
  have kw : ∀ a, 0 < a → ContinuousAt (fun s => dilogKer ((x * (1 - x) / e1 - s) /
      (x * (1 - x) / e1 + a))) t := fun a ha =>
    i3E_continuousAt_dilogKer_comp (by fun_prop) (by
      rw [div_lt_one (by positivity)]; linarith)
  have w1 := kw (1 + e1) (by positivity)
  have w2 := kw _ hq
  have w3 := kw x hx0
  have w4 := kw (1 - x) hy0
  have l1 : ContinuousAt (fun s => log (s + x * (1 - x))) t :=
    (continuousAt_id.add continuousAt_const).log (add_pos ht hc).ne'
  have l2 : ContinuousAt (fun s => log (s + x)) t :=
    (continuousAt_id.add continuousAt_const).log (add_pos ht hx0).ne'
  have l3 : ContinuousAt (fun s => log (s + (1 - x))) t :=
    (continuousAt_id.add continuousAt_const).log (add_pos ht hy0).ne'
  have l4 : ContinuousAt (fun s => log (s + (1 + e1))) t :=
    (continuousAt_id.add continuousAt_const).log (show t + (1 + e1) ≠ 0 by positivity)
  have hd : t + x * (1 - x) * e1 / (x * (1 - x) + e1) ≠ 0 := by positivity
  unfold i3EH
  fun_prop (disch := assumption)

/-- `i3EH ≥ 0` on `(0, ∞)`, including the removable point `t = c/e₁`. -/
theorem i3EH_nonneg {x e1 t : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (he1 : 0 < e1) (ht : 0 < t) :
    0 ≤ i3EH x e1 t := by
  have hc : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
  have key : ∀ s, 0 < s → x * (1 - x) ≠ e1 * s → 0 ≤ i3EH x e1 s := fun s hs hm => by
    rw [i3EH_eq hx he1 hs hm]
    exact mul_nonneg (by positivity) (i3E_F2_nonneg hc he1 hs hm)
  by_cases hm : x * (1 - x) = e1 * t
  · have hlim : Tendsto (i3EH x e1) (𝓝[≠] t) (𝓝 (i3EH x e1 t)) :=
      (continuousAt_i3EH hx he1 ht).tendsto.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hlim ?_
    have h1 : ∀ᶠ s in 𝓝[≠] t, 0 < s :=
      nhdsWithin_le_nhds (Ioi_mem_nhds ht)
    filter_upwards [h1, self_mem_nhdsWithin] with s hs (hst : s ≠ t)
    refine key s hs fun h => hst ?_
    have := he1.ne'
    rw [hm] at h
    exact (mul_left_cancel₀ this h).symm
  · exact key t ht hm

theorem i3E_tendsto_dilogI {g : ℝ → ℝ} (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun t => dilogI (g t)) atTop (𝓝 0) := by
  have := (hasDerivAt_dilogI (by norm_num : (0 : ℝ) < 1)).continuousAt.tendsto.comp hg
  rw [dilogI_zero] at this
  exact this

theorem i3E_tendsto_inv_div {p b : ℝ} (hb : 0 < b) :
    Tendsto (fun t => -(1 / ((t - p) / b))) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => (t - p) / b) atTop atTop :=
    (tendsto_atTop_add_const_right _ (-p) tendsto_id).atTop_div_const hb
  have := (tendsto_inv_atTop_zero.comp h).neg
  simpa [one_div, sub_eq_add_neg] using this

theorem i3E_tendsto_div_add {q a : ℝ} :
    Tendsto (fun t => (q - a) / (t + q)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ q tendsto_id)

theorem i3E_tendsto_log_sq_sub {q : ℝ} (hq : 0 < q) :
    Tendsto (fun t => (log t ^ 2 - log (t + q) ^ 2) / 2) atTop (𝓝 0) := by
  have hL : Tendsto (fun t => q * (log (1 * t + q) / (1 * t + 0))) atTop (𝓝 (q * 0)) :=
    (i3V_tendsto_log_div one_pos one_pos).const_mul q
  rw [mul_zero] at hL
  refine squeeze_zero_norm' ?_ hL
  filter_upwards [eventually_ge_atTop 1] with t ht
  have ht0 : 0 < t := by linarith
  have h1 : 0 ≤ log t := log_nonneg ht
  have h2 : log t ≤ log (t + q) := log_le_log ht0 (by linarith)
  have h3 : log (t + q) - log t ≤ q / t := by
    rw [← log_div (by linarith) ht0.ne']
    have := log_le_sub_one_of_pos (show 0 < (t + q) / t by positivity)
    have e : (t + q) / t - 1 = q / t := by field_simp; ring
    linarith
  rw [Real.norm_eq_abs, abs_le]
  simp only [one_mul, add_zero]
  have e : (log t ^ 2 - log (t + q) ^ 2) / 2 =
      -((log (t + q) - log t) * (log (t + q) + log t) / 2) := by ring
  rw [e]
  have h4 : (log (t + q) - log t) * (log (t + q) + log t) ≤ q / t * (2 * log (t + q)) :=
    mul_le_mul h3 (by linarith) (by linarith) (by positivity)
  have h5 : 0 ≤ (log (t + q) - log t) * (log (t + q) + log t) :=
    mul_nonneg (by linarith) (by linarith)
  have e2 : q / t * (2 * log (t + q)) = 2 * (q * (log (t + q) / t)) := by ring
  constructor <;> nlinarith

theorem i3E_tendsto_log_sub {p q : ℝ} :
    Tendsto (fun t => log (t - p) - log (t + q)) atTop (𝓝 0) := by
  have hr := i3V_tendsto_ratio (α := 1) (β := -p) (δ := q) one_pos
  rw [div_one] at hr
  have h := (continuousAt_log one_ne_zero).tendsto.comp hr
  rw [log_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (max p (-q))] with t ht
  have h1 : 0 < t - p := by linarith [le_max_left p (-q)]
  have h2 : 0 < t + q := by linarith [le_max_right p (-q)]
  simp only [Function.comp, one_mul, ← sub_eq_add_neg]
  rw [log_div h1.ne' h2.ne']

/-- The limit of `i3EP x e₁` at `∞`. -/
noncomputable def i3EL (x e1 : ℝ) : ℝ :=
  π ^ 2 / 6 - log x * log (1 - x) + (log (x * (1 - x) / e1 + (1 + e1)) ^ 2 +
    log (x * (1 - x) / e1 + x * (1 - x) * e1 / (x * (1 - x) + e1)) ^ 2 -
    log (x * (1 - x) / e1 + x) ^ 2 - log (x * (1 - x) / e1 + (1 - x)) ^ 2) / 2

theorem i3E_neg_dilogI_neg {X : ℝ} (hX : 0 < X) :
    -dilogI (-X) = π ^ 2 / 6 + log X ^ 2 / 2 + dilogI (-(1 / X)) := by
  have := i3E_dilogI_inv hX
  linarith

/-- The `p`-residue relation `(p + 1 + e₁)(p + q)(c + e₁) = (p + x)(p + 1 - x) A`, in logs. -/
theorem i3E_log_res {x e1 : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (he1 : 0 < e1) :
    log (x * (1 - x) / e1 + (1 + e1)) +
      log (x * (1 - x) / e1 + x * (1 - x) * e1 / (x * (1 - x) + e1)) -
      log (x * (1 - x) / e1 + x) - log (x * (1 - x) / e1 + (1 - x)) =
      log (x * (1 - x) + e1 + e1 ^ 2) - log (x * (1 - x) + e1) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hy0 : 0 < 1 - x := by linarith
  have hc : 0 < x * (1 - x) := mul_pos hx0 hy0
  rw [← log_mul (by positivity) (by positivity), ← log_div (by positivity) (by positivity),
    ← log_div (by positivity) (by positivity), ← log_div (by positivity) (by positivity)]
  congr 1
  field_simp
  ring

theorem tendsto_i3EP {x e1 : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (he1 : 0 < e1) :
    Tendsto (i3EP x e1) atTop (𝓝 (i3EL x e1)) := by
  have hR := i3E_log_res hx he1
  obtain ⟨hx0, hx1⟩ := hx
  have hy0 : 0 < 1 - x := by linarith
  have hc : 0 < x * (1 - x) := mul_pos hx0 hy0
  have hq : 0 < x * (1 - x) * e1 / (x * (1 - x) + e1) := by positivity
  have hp : 0 < x * (1 - x) / e1 := by positivity
  set y := 1 - x with hy
  set c := x * y with hcd
  set q := c * e1 / (c + e1) with hqd
  set p := c / e1 with hpd
  set K := log (c + e1) - log (c + e1 + e1 ^ 2) with hK
  have hqq : q / e1 + q / c = 1 := by rw [hqd]; field_simp
  have hlim := ((tendsto_const_nhds (x := i3EL x e1)).add ((i3E_tendsto_log_sq_sub hq).add
    ((i3E_tendsto_log_sub (p := p) (q := q)).const_mul K))).add
    ((((((i3E_tendsto_dilogI (i3E_tendsto_div_add (q := q) (a := c))).sub
      (i3E_tendsto_dilogI (i3E_tendsto_div_add (q := q) (a := x)))).sub
      (i3E_tendsto_dilogI (i3E_tendsto_div_add (q := q) (a := y)))).const_mul (q / e1)).sub
      ((i3E_tendsto_dilogI (i3E_tendsto_div_add (q := q) (a := 1 + e1))).const_mul (q / c))).add
    ((((i3E_tendsto_dilogI (i3E_tendsto_inv_div (p := 0) hx0)).add
      (i3E_tendsto_dilogI (i3E_tendsto_inv_div (p := 0) hy0))).sub
      (i3E_tendsto_dilogI (i3E_tendsto_inv_div (p := 0) hc))).add
    ((((i3E_tendsto_dilogI (i3E_tendsto_inv_div (p := p) (b := p + (1 + e1)) (by positivity))).add
      (i3E_tendsto_dilogI (i3E_tendsto_inv_div (p := p) (b := p + q) (by positivity)))).sub
      (i3E_tendsto_dilogI (i3E_tendsto_inv_div (p := p) (b := p + x) (by positivity)))).sub
      (i3E_tendsto_dilogI (i3E_tendsto_inv_div (p := p) (b := p + y) (by positivity))))))
  simp only [mul_zero, sub_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (max p 1)] with t ht
  have htp : p < t := lt_of_le_of_lt (le_max_left _ _) ht
  have ht0 : 0 < t := by linarith
  have hZ : ∀ a, 0 < a → i3EZ a t = π ^ 2 / 6 + (log t - log a) ^ 2 / 2 +
      dilogI (-(1 / ((t - 0) / a))) := fun a ha => by
    rw [i3EZ, i3E_neg_dilogI_neg (by positivity), sub_zero, log_div ht0.ne' ha.ne']
  have hW : ∀ a, 0 < p + a → i3EW p a t = π ^ 2 / 6 + (log (t - p) - log (p + a)) ^ 2 / 2 +
      dilogI (-(1 / ((t - p) / (p + a)))) := fun a ha => by
    rw [i3EW, show (p - t) / (p + a) = -((t - p) / (p + a)) by ring,
      i3E_neg_dilogI_neg (div_pos (by linarith) ha), log_div (by linarith) ha.ne']
  simp only [i3EP, i3EF, i3EL]
  rw [hZ x hx0, hZ y hy0, hZ c hc, hW _ (by positivity), hW _ (by positivity),
    hW _ (by positivity), hW _ (by positivity)]
  have hlc : log c = log x + log y := by rw [hcd, log_mul hx0.ne' hy0.ne']
  simp only [← hy, ← hcd, ← hqd, ← hpd, sub_zero]
  rw [hlc, hK]
  linear_combination (log (t + q) ^ 2 / 2) * hqq + log (t - p) * hR

/-- **The `e₃`-integral of `f₂`** in closed form: `g(x, e₁) = (L - P(0)) / (c e₁)`. -/
noncomputable def i3VG (x e1 : ℝ) : ℝ := (i3EL x e1 - i3EP x e1 0) / (x * (1 - x) * e1)

/-- **The `e₃`-integral**: `∫₀^∞ f₂(x (1 - x), e₁, e₃) de₃ = g(x, e₁)`. -/
theorem i3V_lintegral_e3 {x e1 : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (he1 : 0 < e1) :
    ∫⁻ e3 in Ioi (0 : ℝ), ENNReal.ofReal (i3VF2 (x * (1 - x)) e1 e3) =
      ENNReal.ofReal (i3VG x e1) := by
  have hc : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
  have hce : 0 < x * (1 - x) * e1 := mul_pos hc he1
  have hae : ∫⁻ e3 in Ioi (0 : ℝ), ENNReal.ofReal (i3VF2 (x * (1 - x)) e1 e3) =
      ∫⁻ e3 in Ioi (0 : ℝ), ENNReal.ofReal (i3EH x e1 e3 / (x * (1 - x) * e1)) := by
    refine setLIntegral_congr_fun_ae (measurableSet_Ioi (a := (0 : ℝ))) ?_
    have hne : ∀ᵐ e3 ∂(volume : Measure ℝ), e3 ≠ x * (1 - x) / e1 := by
      rw [ae_iff]; simp
    filter_upwards [hne] with e3 he3 (he3' : 0 < e3)
    rw [i3EH_eq hx he1 he3' fun h => he3 (by field_simp; linarith),
      mul_div_cancel_left₀ _ hce.ne']
  rw [hae, i3V_lintegral_Ioi_eq (g := fun t => i3EP x e1 t / (x * (1 - x) * e1))
    (fun t ht => (hasDerivAt_i3EP hx he1 ht).div_const _)
    (fun t ht => div_nonneg (i3EH_nonneg hx he1 ht) hce.le)
    ((tendsto_i3EP hx he1).div_const _), i3VG, sub_div]

/-- **`i3FInt 0` as a double integral of the closed form `g`.** -/
theorem i3FInt_zero_eq_lintegral_g :
    i3FInt 0 = (((∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ e1 in Ioi (0 : ℝ),
      ENNReal.ofReal (i3VG x e1)).toReal : ℝ) : ℂ) := by
  rw [i3FInt_zero_eq_lintegral_f2]
  congr 2
  exact setLIntegral_congr_fun measurableSet_Ioo fun x hx =>
    setLIntegral_congr_fun measurableSet_Ioi fun e1 (he1 : 0 < e1) => i3V_lintegral_e3 hx he1

end QED.ThreeLoopD
