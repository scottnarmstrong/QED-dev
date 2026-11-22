/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C1Ang
public import QED.ThreeLoopD.SetDMastersI5C1Ker
public import QED.ThreeLoopD.SetDMastersI5C0Sub

/-!
# Set (d), master `I₅`: the first coefficient of the kernel as a real double integral

**The angular denominators.** For `T > 0` let `x = 2t A(T)` (`QED.ThreeLoopD.i5xA`), so that
`t/x - x = T` and `0 < x < √t`. Then `V_x(z) = t/x - x - 2i√t z` (`QED.ThreeLoopD.i5V`) is
`(t/x) D_{x/√t}(z)`, and the angular integrals of `QED.ThreeLoopD.SetDMastersI5C1Ang` become

  `∫₋₁¹ √(1 - z²)/V_x = πx/(2t)`,
  `∫₋₁¹ √(1 - z²) log (1 - z²)/V_x = πx/(2t) · M(x)`,
  `∫₋₁¹ √(1 - z²) log V_{x'}/V_x = πx/(2t) · Λ(x, x')`,

with `M(x) = -2 log 2 + (t + x²)/x² · log (1 + x²/t)` (`QED.ThreeLoopD.i5Mx`) and
`Λ(x, x') = log (t/x') - x'/x + (t + x²)/x² · log (1 + x x'/t)` (`QED.ThreeLoopD.i5Lx`).

**Fubini.** The Cauchy estimate bounds the first Taylor coefficient of the triangle integrand by
`16 e^{π/8} i5TriDom t q`, and `|√(1 - z²) log (1 - z²)| ≤ 2`, so the integrand of
`QED.ThreeLoopD.i5KerIC t 1` (`QED.ThreeLoopD.i5H1`, a function of `(z, q)`) is integrable on the
product and the angular integral can be done first (`QED.ThreeLoopD.i5KerIC_one_eq`).

**The angular integral at fixed `q = (a, c)`.** With `U = 1 + a + c`, `X₁ = c² + a t`,
`w = V_y` (`y = 2t A(t)`) and `X = X₁ + c w = c V_x` (`x = 2t A(t + X₁/c)`,
`QED.ThreeLoopD.i5xq`), `1/(w X) = (1/X₁)(1/w - c/X)` and `log X = log c + log V_x`. The six
angular integrals above give (`QED.ThreeLoopD.i5_integral_i5H1`, `QED.ThreeLoopD.i5PhiQ1`)

  `∫₋₁¹ i5H1 t (z, q) dz = (1/(U X₁)) [(2 log U - log c)(πy/2t - πx/2t)`
    `- (πy/2t Λ(y, x) - πx/2t Λ(x, x)) - (πy/2t M(y) - πx/2t M(x))]`,

and hence (`QED.ThreeLoopD.i5KerC_one_eq_integral`)

  `K₁(t) = (1 - 2 log 2) ∫∫ i5Phi0 t + (2/π) ∫∫ i5PhiQ1 t`.

## Main results

* `QED.ThreeLoopD.i5_integral_V`, `QED.ThreeLoopD.i5_integral_VLogW`,
  `QED.ThreeLoopD.i5_integral_VLogV`.
* `QED.ThreeLoopD.integrable_i5H1`, `QED.ThreeLoopD.i5KerIC_one_eq`.
* `QED.ThreeLoopD.i5_integral_i5H1`, `QED.ThreeLoopD.i5KerC_one_eq_integral`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.ThreeLoopD

/-! ### The variable `x` of an angular denominator -/

/-- `x = 2t A(T)`, the root in `(0, √t)` of `t/x - x = T`. -/
noncomputable def i5xA (t T : ℝ) : ℝ := 2 * t * i5A t T

theorem i5xA_pos {t T : ℝ} (ht : 0 < t) (hT : 0 < T) : 0 < i5xA t T := by
  unfold i5xA i5A; positivity

theorem i5xA_inv {t T : ℝ} (ht : 0 < t) (hT : 0 < T) : t / i5xA t T - i5xA t T = T := by
  unfold i5xA i5A
  set S := √(T ^ 2 + 4 * t) with hS
  have hS2 : S ^ 2 = T ^ 2 + 4 * t := Real.sq_sqrt (by positivity)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have : 0 < T + S := by linarith
  field_simp
  linear_combination hS2

theorem i5xA_lt {t T : ℝ} (ht : 0 < t) (hT : 0 < T) : i5xA t T < √t := by
  have hx := i5xA_pos ht hT
  have h := i5xA_inv ht hT
  refine (Real.lt_sqrt hx.le).mpr ?_
  have : i5xA t T < t / i5xA t T := by linarith
  rw [lt_div_iff₀ hx] at this
  nlinarith

/-! ### The denominators `V_x` -/

/-- `V_x(z) = t/x - x - 2i√t z`. -/
noncomputable def i5V (t x z : ℝ) : ℂ := ((t / x - x : ℝ) : ℂ) - ((2 * √t * z : ℝ) : ℂ) * I

theorem i5V_eq {t x : ℝ} (ht : 0 < t) (hx : 0 < x) (z : ℝ) :
    i5V t x z = ((t / x : ℝ) : ℂ) * i5Dk (x / √t) z := by
  have hs : 0 < √t := Real.sqrt_pos.mpr ht
  have hs2 : √t ^ 2 = t := Real.sq_sqrt ht.le
  have e1 : t / x - x = t / x * (1 - (x / √t) ^ 2) := by
    rw [div_pow, hs2]; field_simp
  have e2 : 2 * √t * z = t / x * (2 * (x / √t) * z) := by
    rw [show t / x * (2 * (x / √t) * z) = 2 * (t / √t) * z by field_simp, Real.div_sqrt]
  unfold i5V i5Dk
  rw [e1, e2]
  push_cast
  ring

theorem i5V_k {t x : ℝ} (ht : 0 < t) (hx : 0 < x) (hxt : x < √t) :
    x / √t ∈ Ioo (0 : ℝ) 1 := by
  have hs : 0 < √t := Real.sqrt_pos.mpr ht
  exact ⟨by positivity, (div_lt_one hs).mpr hxt⟩

theorem i5V_ne_zero {t x : ℝ} (ht : 0 < t) (hx : 0 < x) (hxt : x < √t) (z : ℝ) :
    i5V t x z ≠ 0 := by
  have hk := i5V_k ht hx hxt
  rw [i5V_eq ht hx]
  exact mul_ne_zero (ofReal_ne_zero.mpr (by positivity))
    (i5Dk_ne_zero (by nlinarith [hk.1, hk.2]) z)

theorem re_i5V (t x z : ℝ) : (i5V t x z).re = t / x - x := by
  unfold i5V
  simp only [sub_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, zero_mul, sub_zero]

theorem i5_sq_div_sqrt {t x : ℝ} (ht : 0 < t) : (x / √t) ^ 2 = x ^ 2 / t := by
  rw [div_pow, Real.sq_sqrt ht.le]

theorem i5_mul_div_sqrt {t x x' : ℝ} (ht : 0 < t) : x / √t * (x' / √t) = x * x' / t := by
  rw [div_mul_div_comm, Real.mul_self_sqrt ht.le]

theorem i5_div_V {t x : ℝ} (ht : 0 < t) (hx : 0 < x) (z : ℝ) (f : ℂ) :
    f / i5V t x z = ((x / t : ℝ) : ℂ) * (f / i5Dk (x / √t) z) := by
  rw [i5V_eq ht hx]
  have : ((t / x : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  push_cast
  field_simp

/-- `∫₋₁¹ √(1 - z²)/V_x dz = πx/(2t)`. -/
theorem i5_integral_V {t x : ℝ} (ht : 0 < t) (hx : 0 < x) (hxt : x < √t) :
    ∫ z in Ioo (-1 : ℝ) 1, ((√(1 - z ^ 2) : ℝ) : ℂ) / i5V t x z =
      ((Real.pi * x / (2 * t) : ℝ) : ℂ) := by
  simp_rw [i5_div_V ht hx]
  rw [integral_const_mul, i5_integral_angD (i5V_k ht hx hxt)]
  push_cast
  field_simp

/-- `M(x) = -2 log 2 + (t + x²)/x² · log (1 + x²/t)`. -/
noncomputable def i5Mx (t x : ℝ) : ℝ :=
  -2 * Real.log 2 + (t + x ^ 2) / x ^ 2 * Real.log (1 + x ^ 2 / t)

/-- `Λ(x, x') = log (t/x') - x'/x + (t + x²)/x² · log (1 + x x'/t)`. -/
noncomputable def i5Lx (t x x' : ℝ) : ℝ :=
  Real.log (t / x') - x' / x + (t + x ^ 2) / x ^ 2 * Real.log (1 + x * x' / t)

/-- `∫₋₁¹ √(1 - z²) log (1 - z²)/V_x dz = πx/(2t) · M(x)`. -/
theorem i5_integral_VLogW {t x : ℝ} (ht : 0 < t) (hx : 0 < x) (hxt : x < √t) :
    ∫ z in Ioo (-1 : ℝ) 1, ((√(1 - z ^ 2) * Real.log (1 - z ^ 2) : ℝ) : ℂ) / i5V t x z =
      ((Real.pi * x / (2 * t) * i5Mx t x : ℝ) : ℂ) := by
  simp_rw [i5_div_V ht hx]
  rw [integral_const_mul, i5_integral_angLogW (i5V_k ht hx hxt), i5_sq_div_sqrt ht]
  unfold i5Mx
  push_cast
  have hx2 : (x : ℂ) ^ 2 ≠ 0 := by
    rw [← ofReal_pow]; exact ofReal_ne_zero.mpr (by positivity)
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  field_simp

theorem continuous_log_i5Dk {k : ℝ} (hk : k ^ 2 < 1) :
    Continuous fun z : ℝ => log (i5Dk k z) :=
  Continuous.clog (by unfold i5Dk; fun_prop) fun z =>
    mem_slitPlane_iff.mpr (Or.inl (by rw [re_i5Dk]; linarith))

/-- `∫₋₁¹ √(1 - z²) log V_{x'}/V_x dz = πx/(2t) · Λ(x, x')`. -/
theorem i5_integral_VLogV {t x x' : ℝ} (ht : 0 < t) (hx : 0 < x) (hxt : x < √t) (hx' : 0 < x')
    (hxt' : x' < √t) :
    ∫ z in Ioo (-1 : ℝ) 1, ((√(1 - z ^ 2) : ℝ) : ℂ) * log (i5V t x' z) / i5V t x z =
      ((Real.pi * x / (2 * t) * i5Lx t x x' : ℝ) : ℂ) := by
  have hk := i5V_k ht hx hxt
  have hk' := i5V_k ht hx' hxt'
  have hk2 : (x / √t) ^ 2 < 1 := by nlinarith [hk.1, hk.2]
  have hk2' : (x' / √t) ^ 2 < 1 := by nlinarith [hk'.1, hk'.2]
  have hpt : ∀ z : ℝ, ((√(1 - z ^ 2) : ℝ) : ℂ) * log (i5V t x' z) / i5V t x z =
      ((x / t : ℝ) : ℂ) * (((Real.log (t / x') : ℝ) : ℂ) *
        (((√(1 - z ^ 2) : ℝ) : ℂ) / i5Dk (x / √t) z) +
        ((√(1 - z ^ 2) : ℝ) : ℂ) * log (i5Dk (x' / √t) z) / i5Dk (x / √t) z) := fun z => by
    rw [i5_div_V ht hx, i5V_eq ht hx', log_ofReal_mul (by positivity) (i5Dk_ne_zero hk2' z)]
    ring
  have hc : Continuous fun z : ℝ =>
      ((√(1 - z ^ 2) : ℝ) : ℂ) * log (i5Dk (x' / √t) z) / i5Dk (x / √t) z :=
    Continuous.div ((by fun_prop : Continuous fun z : ℝ => ((√(1 - z ^ 2) : ℝ) : ℂ)).mul
      (continuous_log_i5Dk hk2'))
      (by unfold i5Dk; fun_prop) fun z => i5Dk_ne_zero hk2 z
  simp_rw [hpt]
  rw [integral_const_mul, integral_add ((i5_integrableOn_angD hk2).const_mul _)
    (hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self), integral_const_mul,
    i5_integral_angD hk, i5_integral_angLogDD hk hk', i5_sq_div_sqrt ht, i5_mul_div_sqrt ht]
  have hxx : x' / √t / (x / √t) = x' / x := by
    have : √t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
    field_simp
  rw [neg_div, hxx]
  unfold i5Lx
  push_cast
  have hx2 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  field_simp
  ring

/-! ### Fubini in `(z, q)` -/

/-- The integrand of `QED.ThreeLoopD.i5KerIC t 1`, as a function of `(z, q)`. -/
noncomputable def i5H1 (t : ℝ) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  (i5W t p.1)⁻¹ * (((√(1 - p.1 ^ 2) : ℝ) : ℂ) * i5TriFC t (i5W t p.1) p.2 1 -
    ((√(1 - p.1 ^ 2) * Real.log (1 - p.1 ^ 2) : ℝ) : ℂ) * i5TriF 0 t (i5W t p.1) p.2)

theorem measurable_i5H1 (t : ℝ) : Measurable (i5H1 t) := by
  unfold i5H1 i5TriFC i5TriL i5TriF i5X i5W
  fun_prop

theorem norm_i5TriFC_one_le {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : w.re = t) {q : ℝ × ℝ}
    (hq : q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :
    ‖i5TriFC t w q 1‖ ≤ 16 * (Real.exp (Real.pi / 8) * i5TriDom t q) := by
  rw [← i5Dsl_TriF ht hw hq 1]
  have h := norm_i13Dsl_le (R := 1 / 4) (ρ := 1 / 8) (by norm_num) (by norm_num)
    (differentiableOn_i5TriF ht hw hq _)
    (fun ε hε => norm_i5TriF_le_dom (by rw [hε]; norm_num) ht hw hq) 1 0 (by simp)
  refine h.trans_eq ?_
  ring

theorem abs_i5SqLog_le {z : ℝ} (hz : z ∈ Ioo (-1 : ℝ) 1) :
    |√(1 - z ^ 2) * Real.log (1 - z ^ 2)| ≤ 2 := by
  rw [i5_sqrt_log_eq, abs_mul, abs_two]
  have hu : 0 < √(1 - z ^ 2) := Real.sqrt_pos.mpr (i5_one_sub_sq_pos hz)
  have hu1 : √(1 - z ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith)
  have := Real.abs_log_mul_self_lt _ hu hu1
  rw [mul_comm] at this
  linarith

theorem norm_i5H1_le {t : ℝ} (ht : 0 < t) {z : ℝ} (hz : z ∈ Ioo (-1 : ℝ) 1) {q : ℝ × ℝ}
    (hq : q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :
    ‖i5H1 t (z, q)‖ ≤ 1 * (18 / t * (Real.exp (Real.pi / 8) * i5TriDom t q)) := by
  have h1 : ‖((√(1 - z ^ 2) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.mpr (by nlinarith)
  have h2 := norm_i5TriFC_one_le ht (re_i5W t z) hq
  have h3 : ‖((√(1 - z ^ 2) * Real.log (1 - z ^ 2) : ℝ) : ℂ)‖ ≤ 2 := by
    rw [norm_real, Real.norm_eq_abs]; exact abs_i5SqLog_le hz
  have h4 : ‖i5TriF 0 t (i5W t z) q‖ ≤ Real.exp (Real.pi / 8) * i5TriDom t q :=
    norm_i5TriF_le_dom (by simp) ht (re_i5W t z) hq
  have hM := (norm_nonneg _).trans h4
  have hw : ‖(i5W t z)⁻¹‖ ≤ 1 / t := by
    rw [norm_inv, one_div]; exact inv_anti₀ ht (le_norm_i5W t z)
  simp only [i5H1]
  calc _ = ‖(i5W t z)⁻¹‖ * ‖((√(1 - z ^ 2) : ℝ) : ℂ) * i5TriFC t (i5W t z) q 1 -
        ((√(1 - z ^ 2) * Real.log (1 - z ^ 2) : ℝ) : ℂ) * i5TriF 0 t (i5W t z) q‖ := norm_mul _ _
    _ ≤ 1 / t * (1 * (16 * (Real.exp (Real.pi / 8) * i5TriDom t q)) +
        2 * (Real.exp (Real.pi / 8) * i5TriDom t q)) :=
      mul_le_mul hw (norm_sub_le_of_le (norm_mul_le_of_le h1 h2) (norm_mul_le_of_le h3 h4))
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem integrable_i5H1 {t : ℝ} (ht : 0 < t) :
    Integrable (i5H1 t) ((volume.restrict (Ioo (-1 : ℝ) 1)).prod
      (volume.restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))) := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod
    (((integrableOn_i5TriDom ht).const_mul (Real.exp (Real.pi / 8))).const_mul (18 / t)))
    (measurable_i5H1 t).aestronglyMeasurable ?_
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod
    (measurableSet_Ioi.prod measurableSet_Ioi))] with p hp
  exact norm_i5H1_le ht hp.1 hp.2

theorem i5KerFC_one_eq_integral {t : ℝ} (ht : 0 < t) (z : ℝ) :
    i5KerFC t z 1 = ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5H1 t (z, q) := by
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  have i1 : IntegrableOn (fun q => i5TriFC t (i5W t z) q 1) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    Integrable.mono' (((integrableOn_i5TriDom ht).const_mul (Real.exp (Real.pi / 8))).const_mul 16)
      (show Measurable fun q => i5TriFC t (i5W t z) q 1 by
        unfold i5TriFC i5TriL i5X; fun_prop).aestronglyMeasurable
      (ae_restrict_of_forall_mem hS fun q hq => norm_i5TriFC_one_le ht (re_i5W t z) hq)
  have i0 : IntegrableOn (fun q => i5TriF 0 t (i5W t z) q) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    Integrable.mono' ((integrableOn_i5TriDom ht).const_mul (Real.exp (Real.pi / 8)))
      (measurable_i5TriF 0 t _).aestronglyMeasurable
      (ae_restrict_of_forall_mem hS fun q hq => norm_i5TriF_le_dom (by simp) ht (re_i5W t z) hq)
  rw [i5KerFC_one, i5TriC, i5Tri_eq]
  simp only [i5H1]
  rw [integral_const_mul, integral_sub (i1.const_mul _) (i0.const_mul _), integral_const_mul,
    integral_const_mul]
  push_cast
  ring

/-- `i5KerIC t 1` as an iterated integral, angular integral inside. -/
theorem i5KerIC_one_eq {t : ℝ} (ht : 0 < t) :
    i5KerIC t 1 = ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), ∫ z in Ioo (-1 : ℝ) 1, i5H1 t (z, q) := by
  unfold i5KerIC
  simp_rw [i5KerFC_one_eq_integral ht]
  exact integral_integral_swap (f := fun z q => i5H1 t (z, q)) (integrable_i5H1 ht)

/-! ### The angular integral at fixed `q` -/

/-- `x(q) = 2t A(t + X₁/c)`, `X₁ = c² + a t`: the variable of `X/c = V_{x(q)}`. -/
noncomputable def i5xq (t : ℝ) (q : ℝ × ℝ) : ℝ := i5xA t (t + (q.2 ^ 2 + q.1 * t) / q.2)

/-- The angular integral of `QED.ThreeLoopD.i5H1` at fixed `q = (a, c)`, with `y = 2t A(t)`,
`x = x(q)`: `(1/(U X₁)) [(2 log U - log c) (πy/2t - πx/2t) - (πy/2t Λ(y, x) - πx/2t Λ(x, x))`
`- (πy/2t M(y) - πx/2t M(x))]`. -/
noncomputable def i5PhiQ1 (t : ℝ) (q : ℝ × ℝ) : ℝ :=
  1 / ((1 + q.1 + q.2) * (q.2 ^ 2 + q.1 * t)) *
    ((2 * Real.log (1 + q.1 + q.2) - Real.log q.2) *
        (Real.pi * i5xA t t / (2 * t) - Real.pi * i5xq t q / (2 * t)) -
      (Real.pi * i5xA t t / (2 * t) * i5Lx t (i5xA t t) (i5xq t q) -
        Real.pi * i5xq t q / (2 * t) * i5Lx t (i5xq t q) (i5xq t q)) -
      (Real.pi * i5xA t t / (2 * t) * i5Mx t (i5xA t t) -
        Real.pi * i5xq t q / (2 * t) * i5Mx t (i5xq t q)))

theorem continuous_div_i5V {t x : ℝ} (ht : 0 < t) (hx : 0 < x) (hxt : x < √t) {f : ℝ → ℂ}
    (hf : Continuous f) : Continuous fun z => f z / i5V t x z :=
  Continuous.div hf (by unfold i5V; fun_prop) (i5V_ne_zero ht hx hxt)

theorem continuous_log_i5V {t x : ℝ} (hx : 0 < x) (hxt : x < √t) :
    Continuous fun z => log (i5V t x z) :=
  Continuous.clog (by unfold i5V; fun_prop) fun z => mem_slitPlane_iff.mpr (Or.inl (by
    rw [re_i5V]
    have h0 : 0 ≤ t := (Real.sqrt_pos.mp (hx.trans hxt)).le
    have : x ^ 2 < t := by
      have := (Real.lt_sqrt hx.le).mp hxt
      linarith
    rw [sub_pos, lt_div_iff₀ hx]
    nlinarith))

/-- The pointwise algebra behind `QED.ThreeLoopD.i5_integral_i5H1`. -/
theorem i5_H1_alg {w μ c U X₁ s L C l lc : ℂ} (hw : w ≠ 0) (hwμ : w + μ ≠ 0) (hc : c ≠ 0)
    (hU : U ≠ 0) (hX : X₁ ≠ 0) (hμ : c * μ = X₁) :
    w⁻¹ * (s * (U⁻¹ * (c * (w + μ))⁻¹ * (2 * C - (lc + L))) - l * (U⁻¹ * (c * (w + μ))⁻¹)) =
      1 / (U * X₁) * ((2 * C - lc) * (s / w - s / (w + μ)) - (s * L / w - s * L / (w + μ)) -
        (l / w - l / (w + μ))) := by
  rw [← hμ]
  have hμ0 : μ ≠ 0 := by rintro rfl; exact hX (by rw [← hμ, mul_zero])
  field_simp
  ring

theorem i5_integral_lin6 {s : Set ℝ} {f₁ f₂ f₃ f₄ f₅ f₆ : ℝ → ℂ} (C : ℂ)
    (h₁ : IntegrableOn f₁ s) (h₂ : IntegrableOn f₂ s) (h₃ : IntegrableOn f₃ s)
    (h₄ : IntegrableOn f₄ s) (h₅ : IntegrableOn f₅ s) (h₆ : IntegrableOn f₆ s) :
    ∫ z in s, (C * (f₁ z - f₂ z) - (f₃ z - f₄ z) - (f₅ z - f₆ z)) =
      C * ((∫ z in s, f₁ z) - ∫ z in s, f₂ z) - ((∫ z in s, f₃ z) - ∫ z in s, f₄ z) -
        ((∫ z in s, f₅ z) - ∫ z in s, f₆ z) := by
  have a₁ : IntegrableOn (fun z => C * (f₁ z - f₂ z) - (f₃ z - f₄ z)) s :=
    ((h₁.sub h₂).const_mul C).sub (h₃.sub h₄)
  have a₂ : IntegrableOn (fun z => f₅ z - f₆ z) s := h₅.sub h₆
  have a₃ : IntegrableOn (fun z => C * (f₁ z - f₂ z)) s := (h₁.sub h₂).const_mul C
  have a₄ : IntegrableOn (fun z => f₃ z - f₄ z) s := h₃.sub h₄
  rw [integral_sub a₁ a₂, integral_sub a₃ a₄, integral_const_mul, integral_sub h₁ h₂,
    integral_sub h₃ h₄, integral_sub h₅ h₆]

/-- **The angular integral at fixed `q`**: `∫₋₁¹ i5H1 t (z, q) dz = i5PhiQ1 t q`. -/
theorem i5_integral_i5H1 {t : ℝ} (ht : 0 < t) {q : ℝ × ℝ}
    (hq : q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :
    ∫ z in Ioo (-1 : ℝ) 1, i5H1 t (z, q) = (i5PhiQ1 t q : ℂ) := by
  obtain ⟨a, c⟩ := q
  have ha : 0 < a := hq.1
  have hc : 0 < c := hq.2
  set X₁ := c ^ 2 + a * t with hX₁
  have hX₁0 : 0 < X₁ := by positivity
  have hU : 0 < 1 + a + c := by linarith
  have hT : 0 < t + X₁ / c := by positivity
  set y := i5xA t t with hy
  set x := i5xq t (a, c) with hx
  have hy0 : 0 < y := i5xA_pos ht ht
  have hyt : y < √t := i5xA_lt ht ht
  have hyi : t / y - y = t := i5xA_inv ht ht
  have hx0 : 0 < x := i5xA_pos ht hT
  have hxt : x < √t := i5xA_lt ht hT
  have hxi : t / x - x = t + X₁ / c := i5xA_inv ht hT
  have hW : ∀ z : ℝ, i5W t z = i5V t y z := fun z => by
    unfold i5W i5V; rw [hyi]; push_cast; ring
  have hXV : ∀ z : ℝ, i5X t (i5W t z) (a, c) = (c : ℂ) * i5V t x z := fun z => by
    unfold i5X i5W i5V
    rw [hxi, hX₁]
    have : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
    push_cast
    field_simp
    ring
  have hVV : ∀ z : ℝ, i5V t x z = i5V t y z + ((X₁ / c : ℝ) : ℂ) := fun z => by
    unfold i5V; rw [hxi, hyi]; push_cast; ring
  set C := 2 * Real.log (1 + a + c) - Real.log c with hC
  have hpt : ∀ z ∈ Ioo (-1 : ℝ) 1, i5H1 t (z, (a, c)) =
      ((1 / ((1 + a + c) * X₁) : ℝ) : ℂ) * ((C : ℂ) *
          (((√(1 - z ^ 2) : ℝ) : ℂ) / i5V t y z - ((√(1 - z ^ 2) : ℝ) : ℂ) / i5V t x z) -
        (((√(1 - z ^ 2) : ℝ) : ℂ) * log (i5V t x z) / i5V t y z -
          ((√(1 - z ^ 2) : ℝ) : ℂ) * log (i5V t x z) / i5V t x z) -
        (((√(1 - z ^ 2) * Real.log (1 - z ^ 2) : ℝ) : ℂ) / i5V t y z -
          ((√(1 - z ^ 2) * Real.log (1 - z ^ 2) : ℝ) : ℂ) / i5V t x z)) := fun z _ => by
    have hVx := i5V_ne_zero ht hx0 hxt z
    have hlog : log (i5X t (i5W t z) (a, c)) = ((Real.log c : ℝ) : ℂ) + log (i5V t x z) := by
      rw [hXV, log_ofReal_mul hc hVx]
    simp only [i5H1]
    rw [i5TriFC_one, i5TriF_zero, i5TriL, hlog, hXV, hW]
    generalize log (i5V t x z) = L
    rw [hVV]
    have h := i5_H1_alg (w := i5V t y z) (μ := ((X₁ / c : ℝ) : ℂ)) (c := (c : ℂ))
      (U := ((1 + a + c : ℝ) : ℂ)) (X₁ := (X₁ : ℂ)) (s := ((√(1 - z ^ 2) : ℝ) : ℂ))
      (L := L) (C := ((Real.log (1 + a + c) : ℝ) : ℂ))
      (l := ((√(1 - z ^ 2) * Real.log (1 - z ^ 2) : ℝ) : ℂ)) (lc := ((Real.log c : ℝ) : ℂ))
      (i5V_ne_zero ht hy0 hyt z) (by rw [← hVV]; exact hVx) (ofReal_ne_zero.mpr hc.ne')
      (ofReal_ne_zero.mpr hU.ne') (ofReal_ne_zero.mpr hX₁0.ne')
      (by have : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
          push_cast; field_simp)
    rw [h, hC]
    push_cast
    ring
  have hI : ∀ f : ℝ → ℂ, Continuous f → IntegrableOn f (Ioo (-1 : ℝ) 1) := fun f hf =>
    hf.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have cs : Continuous fun z : ℝ => ((√(1 - z ^ 2) : ℝ) : ℂ) := by fun_prop
  have csl : Continuous fun z : ℝ => ((√(1 - z ^ 2) * Real.log (1 - z ^ 2) : ℝ) : ℂ) :=
    continuous_ofReal.comp continuous_i5SqLog
  have csL : Continuous fun z : ℝ => ((√(1 - z ^ 2) : ℝ) : ℂ) * log (i5V t x z) :=
    cs.mul (continuous_log_i5V hx0 hxt)
  have c1 := continuous_div_i5V ht hy0 hyt cs
  have c2 := continuous_div_i5V ht hx0 hxt cs
  have c3 := continuous_div_i5V ht hy0 hyt csL
  have c4 := continuous_div_i5V ht hx0 hxt csL
  have c5 := continuous_div_i5V ht hy0 hyt csl
  have c6 := continuous_div_i5V ht hx0 hxt csl
  have hlin := i5_integral_lin6 (C : ℂ) (hI _ c1) (hI _ c2) (hI _ c3) (hI _ c4) (hI _ c5)
    (hI _ c6)
  beta_reduce at hlin
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_const_mul, hlin,
    i5_integral_V ht hy0 hyt, i5_integral_V ht hx0 hxt,
    i5_integral_VLogV ht hy0 hyt hx0 hxt, i5_integral_VLogV ht hx0 hxt hx0 hxt,
    i5_integral_VLogW ht hy0 hyt, i5_integral_VLogW ht hx0 hxt]
  unfold i5PhiQ1
  simp only
  rw [← hX₁, ← hy, ← hx, ← hC]
  push_cast
  ring

/-! ### Assembly -/

/-- **The first coefficient of the kernel as real double integrals over `q = (a, c)`**:
`K₁(t) = (1 - 2 log 2) ∫∫ i5Phi0 + (2/π) ∫∫ i5PhiQ1`. -/
theorem i5KerC_one_eq_integral {t : ℝ} (ht : 0 < t) :
    i5KerC t 1 = (((1 - 2 * Real.log 2) * ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5Phi0 t q) +
      2 / Real.pi * ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5PhiQ1 t q : ℝ) := by
  rw [i5KerC_one_eq ht, i5Ker_zero ht, i5KerIC_one_eq ht,
    setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioi)
      fun q hq => i5_integral_i5H1 ht hq, integral_complex_ofReal]
  push_cast
  ring

end QED.ThreeLoopD
