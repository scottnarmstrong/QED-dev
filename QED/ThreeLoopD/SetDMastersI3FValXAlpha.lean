/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI3FValE3
public import QED.ThreeLoopD.SetDMastersI3FValXPos

/-!
# Set (d), master `I₃`: the `α`-integral of the `c`-derivative

Fix `x ∈ (0, 1)`, `x ≠ 1/2`, and write `y = 1 - x`, `c = x y`, `d = x - y`. With `u = x α`,
`v = y α` and `Π = (1 + u)(1 + v) = 1 + α + c α²`, the numerator `N(u, v)` of
`QED.ThreeLoopD.SetDMastersI3FValXPos` satisfies

  `∫₀^∞ N(x α, y α) / (α Π) dα = J(x) = 2 (x Li₂(-y/x) - y Li₂(-x/y)) / (x - y)`.

The integrand is the derivative of the dilogarithmic primitive `Ψ` (`i3XPsi`), assembled from

* `∫ log (1 + b α)/α = -Li₂(-b α)`, `∫ log α/(1 + b α) = (log α log (1 + b α) + Li₂(-b α))/b`,
* `∫ log (1 + c α)/(1 + x α) = (log x log (1 + x α) - Li₂(-y (1 + x α)/x))/x`,
* `∫ log (1 + α)/(1 + x α) = (log (1 + α) log ((1 + x α)/y) + Li₂(-x (1 + α)/y))/x`,

with the dilogarithm `dilogI` on `(-∞, 1)`. Since `log 0 = 0` in Lean, `Ψ(0)` is also its limit
at `0⁺`, which is `-J(x)`; at `∞`, `Ψ → 0`: after the inversion formula every dilogarithm has a
vanishing argument and the logarithms combine into products of `δ_q = log (α + q) - log α → 0`
and `log α · δ_q → 0`.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i3XPsi`: `Ψ' = N(x α, y α)/(α Π)`.
* `QED.ThreeLoopD.i3X_lintegral_alpha`: `∫₀^∞ N(x α, y α)/(α Π) dα = J(x)` (lower integral).
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology
open scoped ENNReal
open QED.TwoLoop.UnitXClose

namespace QED.ThreeLoopD

/-- FTC on `(0, ∞)` for lower integrals of a nonnegative derivative, with continuity at `0`. -/
theorem i3X_lintegral_Ioi_eq {g g' : ℝ → ℝ} {l : ℝ} (hc : ContinuousWithinAt g (Ici 0) 0)
    (hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt g (g' x) x) (hpos : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ g' x)
    (hl : Tendsto g atTop (𝓝 l)) :
    ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (g' x) = ENNReal.ofReal (l - g 0) := by
  have hI := integrableOn_Ioi_deriv_of_nonneg hc hd hpos hl
  rw [← ofReal_integral_eq_lintegral_ofReal hI, integral_Ioi_of_hasDerivAt_of_nonneg hc hd hpos hl]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hpos x hx

/-- The chain rule for `dilogI ∘ f` with `log (1 - f)` supplied. -/
theorem i3X_hasDerivAt_dilogI {f : ℝ → ℝ} {f' a L : ℝ} (hf : HasDerivAt f f' a) (h1 : f a < 1)
    (h0 : f a ≠ 0) (hL : log (1 - f a) = L) :
    HasDerivAt (fun y => dilogI (f y)) (-(L / f a) * f') a := by
  have := i3E_hasDerivAt_dilogI_comp hf h1
  simp only [dilogKer, h0, ite_false, hL] at this
  exact this

/-- The `α`-primitive `Ψ` of `N(x α, y α) / (α Π)`. -/
noncomputable def i3XPsi (x a : ℝ) : ℝ :=
  dilogI (-(x * a)) + dilogI (-((1 - x) * a)) - dilogI (-a) +
    (x * (log a * log (1 + (1 - x) * a) + dilogI (-((1 - x) * a))) -
      (1 - x) * (log a * log (1 + x * a) + dilogI (-(x * a))) +
      x * (log x * log (1 + x * a) - dilogI (-((1 - x) * (1 + x * a) / x))) -
      (1 - x) * (log (1 - x) * log (1 + (1 - x) * a) -
        dilogI (-(x * (1 + (1 - x) * a) / (1 - x)))) +
      (1 - x) * (log (1 + a) * (log (1 + x * a) - log (1 - x)) +
        dilogI (-(x * (1 + a) / (1 - x)))) -
      x * (log (1 + a) * (log (1 + (1 - x) * a) - log x) +
        dilogI (-((1 - x) * (1 + a) / x))) -
      (x * log x + (1 - x) * log (1 - x)) * (log (1 + x * a) - log (1 + (1 - x) * a))) /
      (x - (1 - x))

/-- `J(x) = 2 (x Li₂(-y/x) - y Li₂(-x/y)) / (x - y)`. -/
noncomputable def i3XJ (x : ℝ) : ℝ :=
  2 * (x * dilogI (-((1 - x) / x)) - (1 - x) * dilogI (-(x / (1 - x)))) / (x - (1 - x))

/-- `N(x α, y α)` with its logarithms split into the letters. -/
theorem i3XN_xa {x a : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (ha : 0 < a) :
    i3XN (x * a) ((1 - x) * a) = (1 + a) * log (1 + a) +
      a * (1 + x * (1 - x) * a) * (log a + log (1 + x * (1 - x) * a)) -
      x * a * (log x + log a) - (1 - x) * a * (log (1 - x) + log a) -
      (1 + x * a) * (1 + (1 - x) * a) * (log (1 + x * a) + log (1 + (1 - x) * a)) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hy0 : 0 < 1 - x := by linarith
  have hc : 0 < 1 + x * (1 - x) * a := by positivity
  simp only [i3XN]
  rw [show 1 + x * a + (1 - x) * a = 1 + a by ring,
    show x * a + (1 - x) * a + x * a * ((1 - x) * a) = a * (1 + x * (1 - x) * a) by ring,
    show 1 + a + x * a * ((1 - x) * a) = (1 + x * a) * (1 + (1 - x) * a) by ring,
    log_mul ha.ne' hc.ne', log_mul hx0.ne' ha.ne', log_mul hy0.ne' ha.ne',
    log_mul (by positivity) (by positivity)]

theorem hasDerivAt_i3XPsi {x a : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hd : x ≠ 1 / 2) (ha : 0 < a) :
    HasDerivAt (i3XPsi x)
      (i3XN (x * a) ((1 - x) * a) / (a * ((1 + x * a) * (1 + (1 - x) * a)))) a := by
  obtain ⟨hx0, hx1⟩ := hx
  have hy0 : 0 < 1 - x := by linarith
  have hdd : x - (1 - x) ≠ 0 := fun h => hd (by linarith)
  have p1 : 0 < 1 + x * a := by positivity
  have p2 : 0 < 1 + (1 - x) * a := by positivity
  have p3 : 0 < 1 + a := by positivity
  have pc : 0 < 1 + x * (1 - x) * a := by positivity
  -- the linear inner functions
  have fx : HasDerivAt (fun a => -(x * a)) (-x) a := by
    exact ((hasDerivAt_id' a).const_mul x).neg.congr_deriv (by ring)
  have fy : HasDerivAt (fun a => -((1 - x) * a)) (-(1 - x)) a := by
    exact ((hasDerivAt_id' a).const_mul (1 - x)).neg.congr_deriv (by ring)
  have f1 : HasDerivAt (fun a => -a) (-1) a := (hasDerivAt_id' a).neg
  have f4 : HasDerivAt (fun a => -((1 - x) * (1 + x * a) / x)) (-(1 - x)) a := by
    have := ((((hasDerivAt_id' a).const_mul x).const_add 1).const_mul (1 - x)).div_const x |>.neg
    refine this.congr_deriv ?_
    field_simp
  have f5 : HasDerivAt (fun a => -(x * (1 + (1 - x) * a) / (1 - x))) (-x) a := by
    have := ((((hasDerivAt_id' a).const_mul (1 - x)).const_add 1).const_mul x).div_const
      (1 - x) |>.neg
    refine this.congr_deriv ?_
    field_simp
  have f6 : HasDerivAt (fun a => -(x * (1 + a) / (1 - x))) (-(x / (1 - x))) a := by
    have := (((hasDerivAt_id' a).const_add 1).const_mul x).div_const (1 - x) |>.neg
    refine this.congr_deriv ?_
    ring
  have f7 : HasDerivAt (fun a => -((1 - x) * (1 + a) / x)) (-((1 - x) / x)) a := by
    have := (((hasDerivAt_id' a).const_add 1).const_mul (1 - x)).div_const x |>.neg
    refine this.congr_deriv ?_
    ring
  -- the seven dilogarithms
  have dx := i3X_hasDerivAt_dilogI fx (by nlinarith) (neg_ne_zero.2 (by positivity))
    (show log (1 - -(x * a)) = log (1 + x * a) by ring_nf)
  have dy := i3X_hasDerivAt_dilogI fy (by nlinarith) (neg_ne_zero.2 (by positivity))
    (show log (1 - -((1 - x) * a)) = log (1 + (1 - x) * a) by ring_nf)
  have d1 := i3X_hasDerivAt_dilogI f1 (by linarith) (neg_ne_zero.2 (by positivity))
    (show log (1 - -a) = log (1 + a) by ring_nf)
  have d4 := i3X_hasDerivAt_dilogI f4 (by have : 0 < (1 - x) * (1 + x * a) / x := by positivity
                                          linarith)
    (by have : 0 < (1 - x) * (1 + x * a) / x := by positivity
        linarith)
    (show log (1 - -((1 - x) * (1 + x * a) / x)) = log (1 + x * (1 - x) * a) - log x by
      rw [← log_div pc.ne' hx0.ne']; congr 1; field_simp; ring)
  have d5 := i3X_hasDerivAt_dilogI f5
    (by have : 0 < x * (1 + (1 - x) * a) / (1 - x) := by positivity
        linarith)
    (by have : 0 < x * (1 + (1 - x) * a) / (1 - x) := by positivity
        linarith)
    (show log (1 - -(x * (1 + (1 - x) * a) / (1 - x))) =
        log (1 + x * (1 - x) * a) - log (1 - x) by
      rw [← log_div pc.ne' hy0.ne']; congr 1; field_simp; ring)
  have d6 := i3X_hasDerivAt_dilogI f6
    (by have : 0 < x * (1 + a) / (1 - x) := by positivity
        linarith)
    (by have : 0 < x * (1 + a) / (1 - x) := by positivity
        linarith)
    (show log (1 - -(x * (1 + a) / (1 - x))) = log (1 + x * a) - log (1 - x) by
      rw [← log_div p1.ne' hy0.ne']; congr 1; field_simp; ring)
  have d7 := i3X_hasDerivAt_dilogI f7
    (by have : 0 < (1 - x) * (1 + a) / x := by positivity
        linarith)
    (by have : 0 < (1 - x) * (1 + a) / x := by positivity
        linarith)
    (show log (1 - -((1 - x) * (1 + a) / x)) = log (1 + (1 - x) * a) - log x by
      rw [← log_div p2.ne' hx0.ne']; congr 1; field_simp; ring)
  -- the logarithms
  have lx : HasDerivAt (fun a => log (1 + x * a)) (x / (1 + x * a)) a := by
    have := (((hasDerivAt_id' a).const_mul x).const_add 1).log p1.ne'
    exact this.congr_deriv (by ring)
  have ly : HasDerivAt (fun a => log (1 + (1 - x) * a)) ((1 - x) / (1 + (1 - x) * a)) a := by
    have := (((hasDerivAt_id' a).const_mul (1 - x)).const_add 1).log p2.ne'
    exact this.congr_deriv (by ring)
  have l1 : HasDerivAt (fun a => log (1 + a)) (1 / (1 + a)) a := by
    have := ((hasDerivAt_id' a).const_add 1).log p3.ne'
    exact this.congr_deriv (by ring)
  have la : HasDerivAt (fun a => log a) (1 / a) a := by
    simpa [one_div] using hasDerivAt_log ha.ne'
  have b1 := ((la.mul ly).add dy).const_mul x
  have b2 := ((la.mul lx).add dx).const_mul (1 - x)
  have b3 := ((lx.const_mul (log x)).sub d4).const_mul x
  have b4 := ((ly.const_mul (log (1 - x))).sub d5).const_mul (1 - x)
  have b5 := ((l1.mul (lx.sub_const (log (1 - x)))).add d6).const_mul (1 - x)
  have b6 := ((l1.mul (ly.sub_const (log x))).add d7).const_mul x
  have b7 := (lx.sub ly).const_mul (x * log x + (1 - x) * log (1 - x))
  have hB := (((((b1.sub b2).add b3).sub b4).add b5).sub b6).sub b7
  have key := ((dx.add dy).sub d1).add (hB.div_const (x - (1 - x)))
  refine key.congr_deriv ?_
  rw [i3XN_xa ⟨hx0, hx1⟩ ha]
  field_simp
  ring

/-! ### Continuity at `0` -/

theorem i3X_cwa_log_mul {b : ℝ} (hb : 0 ≤ b) :
    ContinuousWithinAt (fun a => log a * log (1 + b * a)) (Ici 0) 0 := by
  rw [ContinuousWithinAt, show log 0 * log (1 + b * 0) = 0 by simp]
  have hm : Tendsto (fun a : ℝ => b * |a * log a|) (𝓝[Ici 0] 0) (𝓝 (b * |0 * log 0|)) :=
    ((continuous_mul_log.abs.const_mul b).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [show b * |(0 : ℝ) * log 0| = 0 by simp] at hm
  refine squeeze_zero_norm' ?_ hm
  filter_upwards [self_mem_nhdsWithin] with a (ha : 0 ≤ a)
  have h1 : 0 ≤ log (1 + b * a) := log_nonneg (by nlinarith)
  have h2 : log (1 + b * a) ≤ b * a := by
    have := log_le_sub_one_of_pos (show 0 < 1 + b * a by nlinarith)
    linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1, abs_mul, abs_of_nonneg ha]
  calc |log a| * log (1 + b * a) ≤ |log a| * (b * a) :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = b * (a * |log a|) := by ring

theorem i3X_ca_dilogI {f : ℝ → ℝ} (hf : Continuous f) (h : f 0 < 1) :
    ContinuousAt (fun a => dilogI (f a)) 0 :=
  (hasDerivAt_dilogI h).continuousAt.comp (f := f) hf.continuousAt

theorem i3X_ca_log {b : ℝ} : ContinuousAt (fun a => log (1 + b * a)) 0 :=
  ((continuous_const.add (continuous_const.mul continuous_id)).continuousAt).log (by simp)

theorem continuousWithinAt_i3XPsi {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContinuousWithinAt (i3XPsi x) (Ici 0) 0 := by
  obtain ⟨hx0, hx1⟩ := hx
  have hy0 : 0 < 1 - x := by linarith
  have cdx := (i3X_ca_dilogI (f := fun a => -(x * a)) (by fun_prop) (by simp)).continuousWithinAt
    (s := Ici 0)
  have cdy := (i3X_ca_dilogI (f := fun a => -((1 - x) * a)) (by fun_prop)
    (by simp)).continuousWithinAt (s := Ici 0)
  have cd1 := (i3X_ca_dilogI (f := fun a => -a) (by fun_prop) (by simp)).continuousWithinAt
    (s := Ici 0)
  have cd4 := (i3X_ca_dilogI (f := fun a => -((1 - x) * (1 + x * a) / x)) (by fun_prop)
    (by have : 0 < (1 - x) * (1 + x * 0) / x := by positivity
        linarith)).continuousWithinAt (s := Ici 0)
  have cd5 := (i3X_ca_dilogI (f := fun a => -(x * (1 + (1 - x) * a) / (1 - x))) (by fun_prop)
    (by have : 0 < x * (1 + (1 - x) * 0) / (1 - x) := by positivity
        linarith)).continuousWithinAt (s := Ici 0)
  have cd6 := (i3X_ca_dilogI (f := fun a => -(x * (1 + a) / (1 - x))) (by fun_prop)
    (by have : 0 < x * (1 + 0) / (1 - x) := by positivity
        linarith)).continuousWithinAt (s := Ici 0)
  have cd7 := (i3X_ca_dilogI (f := fun a => -((1 - x) * (1 + a) / x)) (by fun_prop)
    (by have : 0 < (1 - x) * (1 + 0) / x := by positivity
        linarith)).continuousWithinAt (s := Ici 0)
  have clx := (i3X_ca_log (b := x)).continuousWithinAt (s := Ici 0)
  have cly := (i3X_ca_log (b := 1 - x)).continuousWithinAt (s := Ici 0)
  have cl1 : ContinuousWithinAt (fun a => log (1 + a)) (Ici 0) 0 := by
    simpa using (i3X_ca_log (b := 1)).continuousWithinAt (s := Ici 0)
  have mx := i3X_cwa_log_mul hx0.le
  have my := i3X_cwa_log_mul hy0.le
  have K : ∀ c : ℝ, ContinuousWithinAt (fun _ : ℝ => c) (Ici 0) 0 := fun c =>
    continuousWithinAt_const
  have b1 := (K x).mul (my.add cdy)
  have b2 := (K (1 - x)).mul (mx.add cdx)
  have b3 := (K x).mul (((K (log x)).mul clx).sub cd4)
  have b4 := (K (1 - x)).mul (((K (log (1 - x))).mul cly).sub cd5)
  have b5 := (K (1 - x)).mul ((cl1.mul (clx.sub (K (log (1 - x))))).add cd6)
  have b6 := (K x).mul ((cl1.mul (cly.sub (K (log x)))).add cd7)
  have b7 := (K (x * log x + (1 - x) * log (1 - x))).mul (clx.sub cly)
  have hB := (((((b1.sub b2).add b3).sub b4).add b5).sub b6).sub b7
  exact ((cdx.add cdy).sub cd1).add (hB.div_const (x - (1 - x)))

/-! ### The limit at `∞` -/

theorem i3X_tendsto_dilogI_inv {f : ℝ → ℝ} {A B : ℝ} (hA : 0 < A) (hf : ∀ a, f a = A * a + B) :
    Tendsto (fun a => dilogI (-(1 / f a))) atTop (𝓝 0) := by
  refine i3E_tendsto_dilogI ?_
  have h : Tendsto f atTop atTop := by
    rw [show f = fun a => A * a + B from funext hf]
    exact tendsto_atTop_add_const_right _ B (tendsto_id.const_mul_atTop hA)
  simpa [one_div] using (tendsto_inv_atTop_zero.comp h).neg

theorem i3X_tendsto_D {q : ℝ} : Tendsto (fun a => log a - log (a + q)) atTop (𝓝 0) := by
  simpa using i3E_tendsto_log_sub (p := 0) (q := q)

theorem tendsto_i3XPsi {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hd : x ≠ 1 / 2) :
    Tendsto (i3XPsi x) atTop (𝓝 0) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hy0 : 0 < 1 - x := by linarith
  have hdd : x - (1 - x) ≠ 0 := fun h => hd (by linarith)
  have qx : 0 < 1 / x := by positivity
  have qy : 0 < 1 / (1 - x) := by positivity
  have s1 := i3X_tendsto_dilogI_inv (f := fun a => x * a) hx0 (B := 0) (fun a => by ring)
  have s2 := i3X_tendsto_dilogI_inv (f := fun a => (1 - x) * a) hy0 (B := 0) (fun a => by ring)
  have s3 := i3X_tendsto_dilogI_inv (f := fun a => a) one_pos (B := 0) (fun a => by ring)
  have s4 := i3X_tendsto_dilogI_inv (f := fun a => (1 - x) * (1 + x * a) / x) hy0
    (B := (1 - x) / x) (fun a => by field_simp; ring)
  have s5 := i3X_tendsto_dilogI_inv (f := fun a => x * (1 + (1 - x) * a) / (1 - x)) hx0
    (B := x / (1 - x)) (fun a => by field_simp; ring)
  have s6 := i3X_tendsto_dilogI_inv (f := fun a => x * (1 + a) / (1 - x)) (div_pos hx0 hy0)
    (B := x / (1 - x)) (fun a => by field_simp; ring)
  have s7 := i3X_tendsto_dilogI_inv (f := fun a => (1 - x) * (1 + a) / x) (div_pos hy0 hx0)
    (B := (1 - x) / x) (fun a => by field_simp; ring)
  have Dx := i3X_tendsto_D (q := 1 / x)
  have Dy := i3X_tendsto_D (q := 1 / (1 - x))
  have D1 := i3X_tendsto_D (q := 1)
  have Sx := i3E_tendsto_log_sq_sub qx
  have Sy := i3E_tendsto_log_sq_sub qy
  have t1 := (D1.mul D1).div_const 2
  have t2 := ((((D1.mul Dx).const_mul (1 - x)).sub ((D1.mul Dy).const_mul x)).sub
    (Sx.const_mul x)).add (Sy.const_mul (1 - x))
  have t3 := t2.div_const (x - (1 - x))
  have t4 := ((((((s1.const_mul (1 - (1 - x) / (x - (1 - x)))).add
    (s2.const_mul (1 + x / (x - (1 - x))))).sub s3).sub (s4.const_mul (x / (x - (1 - x))))).add
    (s5.const_mul ((1 - x) / (x - (1 - x))))).add (s6.const_mul ((1 - x) / (x - (1 - x))))).sub
    (s7.const_mul (x / (x - (1 - x))))
  have hlim := (((t1.add t3).sub (Dx.const_mul (log (1 - x)))).sub
    (Dy.const_mul (log x))).sub t4
  simp only [mul_zero, zero_div, add_zero, sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with a ha
  have inv : ∀ X : ℝ, 0 < X → ∀ L : ℝ, log X = L →
      dilogI (-X) = -π ^ 2 / 6 - L ^ 2 / 2 - dilogI (-(1 / X)) := fun X hX L hL => by
    have := i3E_dilogI_inv hX
    rw [hL] at this
    linarith
  have hLx : log (1 + x * a) = log x + log (a + 1 / x) := by
    rw [← log_mul hx0.ne' (by positivity)]; congr 1; field_simp; ring
  have hLy : log (1 + (1 - x) * a) = log (1 - x) + log (a + 1 / (1 - x)) := by
    rw [← log_mul hy0.ne' (by positivity)]; congr 1; field_simp; ring
  have hL1 : log (1 + a) = log (a + 1) := by rw [add_comm]
  have i1 := inv (x * a) (by positivity) _ (log_mul hx0.ne' ha.ne')
  have i2 := inv ((1 - x) * a) (by positivity) _ (log_mul hy0.ne' ha.ne')
  have i3 := inv a ha _ rfl
  have i4 := inv ((1 - x) * (1 + x * a) / x) (by positivity) (log (1 - x) + log (a + 1 / x))
    (by rw [log_div (by positivity) hx0.ne', log_mul hy0.ne' (by positivity), hLx]; ring)
  have i5 := inv (x * (1 + (1 - x) * a) / (1 - x)) (by positivity) (log x + log (a + 1 / (1 - x)))
    (by rw [log_div (by positivity) hy0.ne', log_mul hx0.ne' (by positivity), hLy]; ring)
  have i6 := inv (x * (1 + a) / (1 - x)) (by positivity) (log x + log (a + 1) - log (1 - x))
    (by rw [log_div (by positivity) hy0.ne', log_mul hx0.ne' (by positivity), hL1])
  have i7 := inv ((1 - x) * (1 + a) / x) (by positivity) (log (1 - x) + log (a + 1) - log x)
    (by rw [log_div (by positivity) hx0.ne', log_mul hy0.ne' (by positivity), hL1])
  simp only [i3XPsi]
  rw [i1, i2, i3, i4, i5, i6, i7, hLx, hLy, hL1]
  field_simp
  ring

/-! ### The `α`-integral -/

/-- **The `α`-integral**: `∫₀^∞ N(x α, y α)/(α Π) dα = J(x)` for `x ∈ (0, 1)`, `x ≠ 1/2`. -/
theorem i3X_lintegral_alpha {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hd : x ≠ 1 / 2) :
    ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal
      (i3XN (x * a) ((1 - x) * a) / (a * ((1 + x * a) * (1 + (1 - x) * a)))) =
      ENNReal.ofReal (i3XJ x) := by
  have hy0 : 0 < 1 - x := by linarith [hx.2]
  rw [i3X_lintegral_Ioi_eq (continuousWithinAt_i3XPsi hx)
    (fun a ha => hasDerivAt_i3XPsi hx hd ha)
    (fun a (ha : 0 < a) => div_nonneg (i3XN_nonneg (mul_pos hx.1 ha) (mul_pos hy0 ha).le)
      (mul_pos ha (mul_pos (by linarith [mul_pos hx.1 ha]) (by linarith [mul_pos hy0 ha]))).le)
    (tendsto_i3XPsi hx hd)]
  congr 1
  simp only [i3XPsi, i3XJ, mul_zero, neg_zero, dilogI_zero, log_zero, add_zero, log_one,
    zero_mul, mul_one, sub_zero, zero_add, zero_sub]
  ring

/-- `J(x) ≥ 0`: it is the integral of a nonnegative function. -/
theorem i3XJ_nonneg {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hd : x ≠ 1 / 2) : 0 ≤ i3XJ x := by
  have hy0 : 0 < 1 - x := by linarith [hx.2]
  have hpos : ∀ a ∈ Ioi (0 : ℝ), 0 ≤
      i3XN (x * a) ((1 - x) * a) / (a * ((1 + x * a) * (1 + (1 - x) * a))) :=
    fun a (ha : 0 < a) => div_nonneg (i3XN_nonneg (mul_pos hx.1 ha) (mul_pos hy0 ha).le)
      (mul_pos ha (mul_pos (by linarith [mul_pos hx.1 ha]) (by linarith [mul_pos hy0 ha]))).le
  have h := integral_Ioi_of_hasDerivAt_of_nonneg (continuousWithinAt_i3XPsi hx)
    (fun a ha => hasDerivAt_i3XPsi hx hd ha) hpos (tendsto_i3XPsi hx hd)
  have h0 : 0 - i3XPsi x 0 = i3XJ x := by
    simp only [i3XPsi, i3XJ, mul_zero, neg_zero, dilogI_zero, log_zero, add_zero, log_one,
      zero_mul, mul_one, sub_zero, zero_add, zero_sub]
    ring
  rw [← h0, ← h]
  exact setIntegral_nonneg measurableSet_Ioi hpos

end QED.ThreeLoopD
