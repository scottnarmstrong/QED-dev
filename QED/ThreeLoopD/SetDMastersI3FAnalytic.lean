/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI3F
public import QED.ThreeLoopD.SetDMastersI9Analytic
public import QED.DimReg.BetaPrime
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Set (d), master `I₃`: the dotted integral `F` is analytic near `ε = 0`

Write `c = x(1 - x)`, `σ = s(1 - s)` and `N = QED.ThreeLoopD.i3FPoly x s u v t`. On the domain
`x, s, u, v ∈ (0, 1)`, `t > 0` of `QED.ThreeLoopD.i3FInt`,

  `σ t (1 + t) ≤ N`, `c (1 + t) (u v)² ≤ N`, `N ≤ (1 + t)²`

(`w = s u + (1 - s) v ≥ u v`). Splitting `N ^ (-23/20) = N ^ (-69/80) N ^ (-23/80)` and bounding
the two factors by the two lower bounds, the integrand is dominated for `|re ε| ≤ 1/20` by

  `c ^ (-31/80) σ ^ (-77/80) u ^ (-23/40) v ^ (-23/40) t ^ (-73/80) (1 + t) ^ (-5/4)`

(`QED.ThreeLoopD.i3F_integrand_le`), an integrable product of one-variable powers (the `t`
factor is a Beta integral of the second kind). The integrand is holomorphic in `ε`, so `i3FInt`
is complex differentiable on `‖ε‖ < 1/40` (`QED.DimReg.differentiableAt_integral_of_holomorphic`),
and so is the Gamma prefactor of `QED.ThreeLoopD.setDI3F`.

## Main results

* `QED.ThreeLoopD.analyticOnNhd_i3FInt`, `QED.ThreeLoopD.analyticAt_setDI3F`.
* `QED.ThreeLoopD.setDI3F_zero_eq`: `F(0) = i3FInt 0 / 2`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric

namespace QED.ThreeLoopD

/-! ### Elementary bounds on the polynomial -/

theorem i3F_le_quarter {x : ℝ} : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]

/-- `σ t (1 + t) ≤ N`. -/
theorem i3FPoly_ge_left {x s u v t : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (ht : 0 < t) :
    s * (1 - s) * t * (1 + t) ≤ i3FPoly x s u v t := by
  have hc : 0 ≤ x * (1 - x) := (mul_pos hx.1 (by linarith [hx.2])).le
  have hσ : 0 ≤ s * (1 - s) := (mul_pos hs.1 (by linarith [hs.2])).le
  have h1 : 0 ≤ x * (1 - x) * ((1 + t) * (s * u + (1 - s) * v) ^ 2 + s * (1 - s) * (u - v) ^ 2) :=
    mul_nonneg hc (add_nonneg (mul_nonneg (by linarith) (sq_nonneg _))
      (mul_nonneg hσ (sq_nonneg _)))
  unfold i3FPoly
  linarith

theorem i3F_w_ge {s u v : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) : u * v ≤ s * u + (1 - s) * v := by
  have h1 : u * v ≤ u := by nlinarith [hu.1, hv.2]
  have h2 : u * v ≤ v := by nlinarith [hv.1, hu.2]
  nlinarith [hs.1, hs.2]

/-- `c (1 + t) (u v)² ≤ N`. -/
theorem i3FPoly_ge_right {x s u v t : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) (ht : 0 < t) :
    x * (1 - x) * (1 + t) * (u * v) ^ 2 ≤ i3FPoly x s u v t := by
  have hc : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
  have hσ : 0 < s * (1 - s) := mul_pos hs.1 (by linarith [hs.2])
  have hw := i3F_w_ge hs hu hv
  have huv : 0 ≤ u * v := (mul_pos hu.1 hv.1).le
  have hsq : (u * v) ^ 2 ≤ (s * u + (1 - s) * v) ^ 2 := pow_le_pow_left₀ huv hw 2
  have h1 : x * (1 - x) * (1 + t) * (u * v) ^ 2 ≤
      x * (1 - x) * ((1 + t) * (s * u + (1 - s) * v) ^ 2) := by
    rw [mul_assoc (x * (1 - x))]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (by linarith)) hc.le
  unfold i3FPoly
  nlinarith [mul_pos (mul_pos hσ ht) (by linarith : (0 : ℝ) < 1 + t),
    mul_nonneg (mul_nonneg hc.le hσ.le) (sq_nonneg (u - v))]

theorem i3FPoly_pos {x s u v t : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (ht : 0 < t) : 0 < i3FPoly x s u v t :=
  lt_of_lt_of_le (mul_pos (mul_pos (mul_pos hs.1 (by linarith [hs.2])) ht) (by linarith))
    (i3FPoly_ge_left hx hs ht)

/-- `N ≤ (1 + t)²`. -/
theorem i3FPoly_le {x s u v t : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) (ht : 0 < t) :
    i3FPoly x s u v t ≤ (1 + t) ^ 2 := by
  have hc : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
  have hσ : 0 < s * (1 - s) := mul_pos hs.1 (by linarith [hs.2])
  have hc4 : x * (1 - x) ≤ 1 / 4 := i3F_le_quarter
  have hσ4 : s * (1 - s) ≤ 1 / 4 := i3F_le_quarter
  have hw0 : 0 ≤ s * u + (1 - s) * v := by nlinarith [hs.1, hs.2, hu.1, hv.1]
  have hw1 : s * u + (1 - s) * v ≤ 1 := by nlinarith [hs.1, hs.2, hu.2, hv.2]
  have hw : (s * u + (1 - s) * v) ^ 2 ≤ 1 := by nlinarith
  have hd : (u - v) ^ 2 ≤ 1 := by nlinarith [hu.1, hu.2, hv.1, hv.2]
  have hB : (1 + t) * (s * u + (1 - s) * v) ^ 2 + s * (1 - s) * (u - v) ^ 2 ≤ 2 + t := by
    nlinarith [mul_le_mul_of_nonneg_left hw (by linarith : (0 : ℝ) ≤ 1 + t),
      mul_le_mul_of_nonneg_left hd hσ.le]
  have hB0 : 0 ≤ (1 + t) * (s * u + (1 - s) * v) ^ 2 + s * (1 - s) * (u - v) ^ 2 := by
    positivity
  unfold i3FPoly
  nlinarith [mul_le_mul hc4 hB hB0 (by norm_num : (0 : ℝ) ≤ 1 / 4),
    mul_le_mul_of_nonneg_right hσ4 (by positivity : (0 : ℝ) ≤ t * (1 + t))]

/-! ### The real dominating bound -/

/-- `t ^ r ≤ t ^ (-1/20) (1 + t) ^ (1/10)` for `|r| ≤ 1/20`. -/
theorem i3F_rpow_t_le {t r : ℝ} (ht : 0 < t) (hr1 : -(1 / 20) ≤ r) (hr2 : r ≤ 1 / 20) :
    t ^ r ≤ t ^ (-(1 / 20) : ℝ) * (1 + t) ^ (1 / 10 : ℝ) := by
  have e : t ^ r = t ^ (-(1 / 20) : ℝ) * t ^ (r + 1 / 20) := by
    rw [← Real.rpow_add ht]; congr 1; ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ht.le _)
  calc t ^ (r + 1 / 20) ≤ (1 + t) ^ (r + 1 / 20) :=
        Real.rpow_le_rpow ht.le (by linarith) (by linarith)
    _ ≤ (1 + t) ^ (1 / 10 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

/-- The product form of the majorant. -/
noncomputable def i3FMaj (z : ℝ × ℝ × ℝ × ℝ × ℝ) : ℝ :=
  (z.1 * (1 - z.1)) ^ (-(31 / 80) : ℝ) * ((z.2.1 * (1 - z.2.1)) ^ (-(77 / 80) : ℝ) *
    (z.2.2.1 ^ (-(23 / 40) : ℝ) * (z.2.2.2.1 ^ (-(23 / 40) : ℝ) *
      (z.2.2.2.2 ^ (-(73 / 80) : ℝ) * (1 + z.2.2.2.2) ^ (-(5 / 4) : ℝ)))))

/-- The bound in abstract form: `c, σ ≤ 1`, `σ t (1 + t) ≤ N`, `c (1 + t) (u v)² ≤ N`,
`N ≤ (1 + t)²`. -/
theorem i3F_bound_aux {c σ N u v t r : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hc1 : c ≤ 1) (hσ1 : σ ≤ 1)
    (hu : 0 < u) (hv : 0 < v) (ht : 0 < t) (hN : 0 < N) (hNl : σ * t * (1 + t) ≤ N)
    (hNr : c * (1 + t) * (u * v) ^ 2 ≤ N) (hNu : N ≤ (1 + t) ^ 2) (hr1 : -(1 / 20) ≤ r)
    (hr2 : r ≤ 1 / 20) :
    (c * σ) ^ (2 * r) * t ^ r * (1 + t) ^ (4 * r - 1) * N ^ (-1 - 3 * r) ≤
      c ^ (-(31 / 80) : ℝ) * (σ ^ (-(77 / 80) : ℝ) * (u ^ (-(23 / 40) : ℝ) *
        (v ^ (-(23 / 40) : ℝ) * (t ^ (-(73 / 80) : ℝ) * (1 + t) ^ (-(5 / 4) : ℝ))))) := by
  have hT : 1 ≤ 1 + t := by linarith
  have hT0 : 0 < 1 + t := by linarith
  have hcσ : 0 < c * σ := mul_pos hc hσ
  have huv : 0 < u * v := mul_pos hu hv
  have hX : 0 < σ * t * (1 + t) := by positivity
  have hY : 0 < c * (1 + t) * (u * v) ^ 2 := by positivity
  have h1 : (c * σ) ^ (2 * r) ≤ (c * σ) ^ (-(1 / 10) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hcσ (by nlinarith) (by linarith)
  have h2 := i3F_rpow_t_le ht hr1 hr2
  have h3 : (1 + t) ^ (4 * r - 1) ≤ (1 + t) ^ (-(4 / 5) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have h4 : N ^ (-1 - 3 * r) ≤ (σ * t * (1 + t)) ^ (-(69 / 80) : ℝ) *
      (c * (1 + t) * (u * v) ^ 2) ^ (-(23 / 80) : ℝ) * (1 + t) ^ (3 / 5 : ℝ) := by
    have e : N ^ (-1 - 3 * r) =
        N ^ (-(69 / 80) : ℝ) * N ^ (-(23 / 80) : ℝ) * N ^ (3 / 20 - 3 * r) := by
      rw [← Real.rpow_add hN, ← Real.rpow_add hN]; congr 1; ring
    rw [e]
    refine mul_le_mul (mul_le_mul (Real.rpow_le_rpow_of_nonpos hX hNl (by norm_num))
      (Real.rpow_le_rpow_of_nonpos hY hNr (by norm_num)) (Real.rpow_nonneg hN.le _)
      (Real.rpow_nonneg hX.le _)) ?_ (Real.rpow_nonneg hN.le _)
      (mul_nonneg (Real.rpow_nonneg hX.le _) (Real.rpow_nonneg hY.le _))
    calc N ^ (3 / 20 - 3 * r) ≤ ((1 + t) ^ (2 : ℝ)) ^ (3 / 20 - 3 * r) :=
          Real.rpow_le_rpow hN.le (by rw [Real.rpow_two]; exact hNu) (by linarith)
      _ = (1 + t) ^ (2 * (3 / 20 - 3 * r)) := by rw [← Real.rpow_mul hT0.le]
      _ ≤ (1 + t) ^ (3 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hq : ((u * v) ^ 2) ^ (-(23 / 80) : ℝ) = u ^ (-(23 / 40) : ℝ) * v ^ (-(23 / 40) : ℝ) := by
    rw [← Real.rpow_natCast_mul huv.le, Real.mul_rpow hu.le hv.le]; norm_num
  have hM : c ^ (-(31 / 80) : ℝ) * (σ ^ (-(77 / 80) : ℝ) * (u ^ (-(23 / 40) : ℝ) *
        (v ^ (-(23 / 40) : ℝ) * (t ^ (-(73 / 80) : ℝ) * (1 + t) ^ (-(5 / 4) : ℝ))))) =
      (c * σ) ^ (-(1 / 10) : ℝ) * (t ^ (-(1 / 20) : ℝ) * (1 + t) ^ (1 / 10 : ℝ)) *
        (1 + t) ^ (-(4 / 5) : ℝ) * ((σ * t * (1 + t)) ^ (-(69 / 80) : ℝ) *
          (c * (1 + t) * (u * v) ^ 2) ^ (-(23 / 80) : ℝ) * (1 + t) ^ (3 / 5 : ℝ)) := by
    rw [Real.mul_rpow hc.le hσ.le, Real.mul_rpow (by positivity) hT0.le,
      Real.mul_rpow hσ.le ht.le, Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow hc.le hT0.le, hq,
      ← rpow_mul_rpow_eq (a := -(1 / 10)) (b := -(23 / 80)) (c := -(31 / 80)) hc (by norm_num),
      ← rpow_mul_rpow_eq (a := -(1 / 10)) (b := -(69 / 80)) (c := -(77 / 80)) hσ (by norm_num),
      ← rpow_mul_rpow_eq (a := -(1 / 20)) (b := -(69 / 80)) (c := -(73 / 80)) ht (by norm_num),
      ← rpow_mul_rpow_eq (a := 1 / 10) (b := -(27 / 20)) (c := -(5 / 4)) hT0 (by norm_num),
      ← rpow_mul_rpow_eq (a := -(4 / 5)) (b := -(11 / 20)) (c := -(27 / 20)) hT0 (by norm_num),
      ← rpow_mul_rpow_eq (a := 3 / 5) (b := -(23 / 20)) (c := -(11 / 20)) hT0 (by norm_num),
      ← rpow_mul_rpow_eq (a := -(69 / 80)) (b := -(23 / 80)) (c := -(23 / 20)) hT0
        (by norm_num)]
    ring
  rw [hM]
  have hp1 := Real.rpow_nonneg hcσ.le (-(1 / 10) : ℝ)
  have hp2 := Real.rpow_nonneg ht.le r
  have hp3 := Real.rpow_nonneg hT0.le (4 * r - 1)
  have hp4 := mul_nonneg (Real.rpow_nonneg ht.le (-(1 / 20) : ℝ))
    (Real.rpow_nonneg hT0.le (1 / 10 : ℝ))
  exact mul_le_mul (mul_le_mul (mul_le_mul h1 h2 hp2 hp1) h3 hp3 (mul_nonneg hp1 hp4)) h4
    (Real.rpow_nonneg hN.le _)
    (mul_nonneg (mul_nonneg hp1 hp4) (Real.rpow_nonneg hT0.le _))

/-- **The dominating bound** (real form). -/
theorem i3F_integrand_le {x s u v t r : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) (ht : 0 < t) (hr1 : -(1 / 20) ≤ r)
    (hr2 : r ≤ 1 / 20) :
    (x * (1 - x) * (s * (1 - s))) ^ (2 * r) * t ^ r * (1 + t) ^ (4 * r - 1) *
        i3FPoly x s u v t ^ (-1 - 3 * r) ≤ i3FMaj (x, s, u, v, t) :=
  i3F_bound_aux (mul_pos hx.1 (by linarith [hx.2])) (mul_pos hs.1 (by linarith [hs.2]))
    (i3F_le_quarter.trans (by norm_num)) (i3F_le_quarter.trans (by norm_num)) hu.1 hv.1 ht
    (i3FPoly_pos hx hs ht) (i3FPoly_ge_left hx hs ht) (i3FPoly_ge_right hx hs hu hv ht)
    (i3FPoly_le hx hs hu hv ht) hr1 hr2

/-! ### Integrability of the majorant -/

theorem integrableOn_i3F_tpart :
    IntegrableOn (fun t : ℝ => t ^ (-(73 / 80) : ℝ) * (1 + t) ^ (-(5 / 4) : ℝ)) (Ioi 0) := by
  have h := QED.DimReg.integrableOn_betaPrime (a := ((7 / 80 : ℝ) : ℂ))
    (b := ((93 / 80 : ℝ) : ℂ)) (by norm_num) (by norm_num) one_pos
  refine IntegrableOn.congr_fun h.norm (fun t ht => ?_) measurableSet_Ioi
  have ht0 : (0 : ℝ) < t := ht
  have ht1 : (0 : ℝ) < 1 + 1 * t := by linarith
  rw [QED.DimReg.betaPrimeIntegrand, norm_mul, norm_cpow_eq_rpow_re_of_pos ht0,
    norm_cpow_eq_rpow_re_of_pos ht1, one_mul]
  congr 2 <;> simp <;> norm_num

theorem volume_restrict_prod5 (A B C D E : Set ℝ) :
    (volume.restrict (A ×ˢ (B ×ˢ (C ×ˢ (D ×ˢ E)))) : Measure (ℝ × ℝ × ℝ × ℝ × ℝ)) =
      (volume.restrict A).prod ((volume.restrict B).prod ((volume.restrict C).prod
        ((volume.restrict D).prod (volume.restrict E)))) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.volume_eq_prod,
    ← Measure.prod_restrict, Measure.volume_eq_prod, ← Measure.prod_restrict,
    Measure.volume_eq_prod, ← Measure.prod_restrict]

/-- The domain of `i3FInt`. -/
abbrev i3FDom : Set (ℝ × ℝ × ℝ × ℝ × ℝ) :=
  Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ))))

theorem integrable_i3FMaj : Integrable i3FMaj (volume.restrict i3FDom) := by
  rw [volume_restrict_prod5]
  exact (integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
    ((integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
      ((integrableOn_rpow_Ioo (by norm_num)).mul_prod
        ((integrableOn_rpow_Ioo (by norm_num)).mul_prod integrableOn_i3F_tpart)))

/-! ### The complex integrand -/

/-- The integrand of `i3FInt`. -/
noncomputable def i3FIntegrand (ε : ℂ) (z : ℝ × ℝ × ℝ × ℝ × ℝ) : ℂ :=
  ((z.1 * (1 - z.1) * (z.2.1 * (1 - z.2.1)) : ℝ) : ℂ) ^ (2 * ε) * (z.2.2.2.2 : ℂ) ^ ε *
    ((1 + z.2.2.2.2 : ℝ) : ℂ) ^ (4 * ε - 1) *
    ((i3FPoly z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 : ℝ) : ℂ) ^ (-1 - 3 * ε)

theorem i3FInt_eq (ε : ℂ) : i3FInt ε = ∫ z in i3FDom, i3FIntegrand ε z := rfl

theorem measurable_i3FIntegrand (ε : ℂ) : Measurable (i3FIntegrand ε) := by
  unfold i3FIntegrand i3FPoly; fun_prop

theorem norm_i3FIntegrand_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {z : ℝ × ℝ × ℝ × ℝ × ℝ}
    (hz : z ∈ i3FDom) : ‖i3FIntegrand ε z‖ ≤ i3FMaj z := by
  obtain ⟨hx, hs, hu, hv, ht⟩ := hz
  have ht0 : (0 : ℝ) < z.2.2.2.2 := ht
  have hr := abs_le.mp ((abs_re_le_norm ε).trans hε.le)
  have hc : 0 < z.1 * (1 - z.1) * (z.2.1 * (1 - z.2.1)) :=
    mul_pos (mul_pos hx.1 (by linarith [hx.2])) (mul_pos hs.1 (by linarith [hs.2]))
  have hT : (0 : ℝ) < 1 + z.2.2.2.2 := by linarith
  have hN := i3FPoly_pos (u := z.2.2.1) (v := z.2.2.2.1) hx hs ht0
  have hb := i3F_integrand_le hx hs hu hv ht0 (r := ε.re) (by linarith) (by linarith)
  rw [i3FIntegrand, norm_mul, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hc,
    norm_cpow_eq_rpow_re_of_pos ht0, norm_cpow_eq_rpow_re_of_pos hT,
    norm_cpow_eq_rpow_re_of_pos hN]
  convert hb using 3 <;> simp

theorem differentiableAt_i3FIntegrand {z : ℝ × ℝ × ℝ × ℝ × ℝ} (hz : z ∈ i3FDom) (ε : ℂ) :
    DifferentiableAt ℂ (fun ε => i3FIntegrand ε z) ε := by
  obtain ⟨hx, hs, hu, hv, ht⟩ := hz
  have ht0 : (0 : ℝ) < z.2.2.2.2 := ht
  have hc : 0 < z.1 * (1 - z.1) * (z.2.1 * (1 - z.2.1)) :=
    mul_pos (mul_pos hx.1 (by linarith [hx.2])) (mul_pos hs.1 (by linarith [hs.2]))
  have hT : (0 : ℝ) < 1 + z.2.2.2.2 := by linarith
  have hN := i3FPoly_pos (u := z.2.2.1) (v := z.2.2.2.1) hx hs ht0
  unfold i3FIntegrand
  refine (((?_ : DifferentiableAt ℂ _ ε).mul ?_).mul ?_).mul ?_
  · exact (by fun_prop : DifferentiableAt ℂ (fun ε : ℂ => 2 * ε) ε).const_cpow
      (Or.inl (ofReal_ne_zero.mpr hc.ne'))
  · exact differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.mpr ht0.ne'))
  · exact (by fun_prop : DifferentiableAt ℂ (fun ε : ℂ => 4 * ε - 1) ε).const_cpow
      (Or.inl (ofReal_ne_zero.mpr hT.ne'))
  · exact (by fun_prop : DifferentiableAt ℂ (fun ε : ℂ => -1 - 3 * ε) ε).const_cpow
      (Or.inl (ofReal_ne_zero.mpr hN.ne'))

/-! ### Analyticity -/

theorem differentiableAt_i3FInt {ε₀ : ℂ} (h0 : ‖ε₀‖ < 1 / 40) :
    DifferentiableAt ℂ i3FInt ε₀ := by
  have hball : ∀ ε ∈ ball ε₀ (1 / 40), ‖ε‖ < 1 / 20 := fun ε hε => by
    have := norm_sub_norm_le ε ε₀
    rw [mem_ball, dist_eq_norm] at hε
    linarith
  have hS : MeasurableSet i3FDom :=
    measurableSet_Ioo.prod (measurableSet_Ioo.prod (measurableSet_Ioo.prod
      (measurableSet_Ioo.prod measurableSet_Ioi)))
  have e : i3FInt = fun ε => ∫ z in i3FDom, i3FIntegrand ε z := funext i3FInt_eq
  rw [e]
  refine QED.DimReg.differentiableAt_integral_of_holomorphic (by norm_num : (0 : ℝ) < 1 / 40)
    integrable_i3FMaj (fun ε _ => (measurable_i3FIntegrand ε).aestronglyMeasurable) ?_ ?_
  · exact ae_restrict_of_forall_mem hS fun z hz ε hε => norm_i3FIntegrand_le (hball ε hε) hz
  · exact ae_restrict_of_forall_mem hS fun z hz ε _ =>
      (differentiableAt_i3FIntegrand hz ε).differentiableWithinAt

/-- **The parametric integral is analytic near `0`.** -/
theorem analyticOnNhd_i3FInt : AnalyticOnNhd ℂ i3FInt (ball 0 (1 / 40)) := fun ε hε =>
  DifferentiableOn.analyticAt (fun ε' hε' => (differentiableAt_i3FInt
    (by simpa using hε')).differentiableWithinAt) (isOpen_ball.mem_nhds hε)

theorem differentiableAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Gamma s :=
  differentiableAt_Gamma s fun m h => by
    have := congrArg re h
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

theorem differentiableAt_setDI3F {ε₀ : ℂ} (h0 : ‖ε₀‖ < 1 / 40) :
    DifferentiableAt ℂ setDI3F ε₀ := by
  have hr := abs_le.mp ((abs_re_le_norm ε₀).trans h0.le)
  have h1 : 0 < (1 + 3 * ε₀).re := by simp; linarith
  have h2 : 0 < (1 + ε₀).re := by simp; linarith
  have hG1 : DifferentiableAt ℂ (fun ε : ℂ => Gamma (1 + 3 * ε)) ε₀ :=
    (differentiableAt_Gamma_of_re_pos h1).comp ε₀ (by fun_prop)
  have hG2 : DifferentiableAt ℂ (fun ε : ℂ => Gamma (1 + ε)) ε₀ :=
    (differentiableAt_Gamma_of_re_pos h2).comp ε₀ (by fun_prop)
  have hne : 2 * Gamma (1 + ε₀) ^ 3 ≠ 0 :=
    mul_ne_zero two_ne_zero (pow_ne_zero _ (Gamma_ne_zero_of_re_pos h2))
  unfold setDI3F
  exact ((hG1.div ((hG2.pow 3).const_mul 2) hne).mul (differentiableAt_i3FInt h0))

/-- **`F` is analytic on `‖ε‖ < 1/40`.** -/
theorem analyticOnNhd_setDI3F : AnalyticOnNhd ℂ setDI3F (ball 0 (1 / 40)) := fun ε hε =>
  DifferentiableOn.analyticAt (fun ε' hε' => (differentiableAt_setDI3F
    (by simpa using hε')).differentiableWithinAt) (isOpen_ball.mem_nhds hε)

/-- **`F` is analytic at `0`.** -/
theorem analyticAt_setDI3F : AnalyticAt ℂ setDI3F 0 :=
  analyticOnNhd_setDI3F 0 (mem_ball_self (by norm_num))

/-! ### The value at `ε = 0` in terms of the parametric integral -/

/-- `F(0) = i3FInt 0 / 2`: the Gamma prefactor is `1/2` at `ε = 0`. -/
theorem setDI3F_zero_eq : setDI3F 0 = i3FInt 0 / 2 := by
  simp [setDI3F]
  ring

/-- `F(0) = π⁴/15` follows from `i3FInt 0 = 2π⁴/15`. -/
theorem setDI3F_zero_of_i3FInt (h : i3FInt 0 = 2 * (Real.pi : ℂ) ^ 4 / 15) :
    setDI3F 0 = (Real.pi : ℂ) ^ 4 / 15 := by
  rw [setDI3F_zero_eq, h]; ring

/-- **The `I₃` input with `F = setDI3F`**: analyticity is proved here, so only the value
`i3FInt 0 = 2π⁴/15` and the relation `QED.ThreeLoopD.SetDMasters.I3Rel` remain. -/
theorem hasTruncLaurent_I3_of_i3FInt {M : SetDMasters}
    (h0 : i3FInt 0 = 2 * (Real.pi : ℂ) ^ 4 / 15) (hrel : M.I3Rel setDI3F)
    (h12 : HasTruncLaurent M.I12 setDLaurentI12 3)
    (h13 : HasTruncLaurent M.I13 setDLaurentI13 3)
    (h14 : HasTruncLaurent M.I14 setDLaurentI14 3)
    (h18 : HasTruncLaurent M.I18 setDLaurentI18 3) :
    HasTruncLaurent M.I3 setDLaurentI3 1 :=
  hasTruncLaurent_I3_of_rel analyticAt_setDI3F (setDI3F_zero_of_i3FInt h0) hrel h12 h13 h14 h18

end QED.ThreeLoopD
