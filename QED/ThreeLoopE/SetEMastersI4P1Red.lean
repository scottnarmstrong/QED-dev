/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI4Gauge
public import QED.ThreeLoopD.SetDMastersI2P1UTot

/-!
# Set (e), master I₄: `P'(0)` reduced to the `F`-part in the gauge of I₂

`P'(0) = ∫ L / U²` over the simplex chart, `L = 4 log U - 3 log F`
(`QED.ThreeLoopE.iteratedDeriv_i4PInt`). We prove:

* `L / U²` is integrable on `QED.ThreeLoopE.i4Dom`. On the domain, the integrand of `P` at a
  real regulator `t` has norm `exp(t L) / U²`, and `|L| ≤ (exp(δ L) + exp(-δ L)) / δ`, so the
  integrability at `t = ±1/200` (`QED.ThreeLoopE.integrableOn_i4Integrand`) dominates `L / U²`.
* `L / U²` is homogeneous of degree `-6`, so the shared Cheng–Wu gauge
  (`QED.ThreeLoopE.i4Gauge_integral`) moves `P'(0)` to the domain of I₂ with weight `1 - w`.
  There `U` is exactly `QED.ThreeLoopD.i2U`, and `F` becomes `QED.ThreeLoopE.i4CWF`.
* With `L = log U - 3 log (F / U)` and the `U`-part of set (d),
  `∫ (1 - w) log U / U² = -3 π⁴ / 10 + 18 ζ(3)` (`QED.ThreeLoopD.i2P1U_value`),

  `P'(0) = -3 π⁴ / 10 + 18 ζ(3) - 3 ∫ (1 - w) log (F / U) / U²`.

So `P'(0) = i4P1 = -7 π⁴ / 30 + 6 ζ(3) + π²` is equivalent to the value
`∫ (1 - w) log (F / U) / U² = -π⁴ / 45 + 4 ζ(3) - π² / 3` of the `F`-part alone.

In the gauge, with `A = y₇ + α₁ α₂`, `B = y₈ + α₂ α₃`, `C = y₄ + α₁ α₃` as for I₂
(`α₁ = (1 - w) x`, `α₂ = w`, `α₃ = (1 - w)(1 - x)`), one has `U = A B + B C + C A` and
`F / U = α₁ + α₂ + y₈ - y₄ R / (y₄ + R)`, `R = A B / (A + B) + α₁ α₃`; this is the form used for
the evaluation of the `F`-part.

## Main definitions

* `QED.ThreeLoopE.i4CWF`: the second Symanzik polynomial of I₄ in the gauge of I₂.

## Main results

* `QED.ThreeLoopE.integrableOn_i4P1L`.
* `QED.ThreeLoopE.i4P1_gauge`: `P'(0)` as an integral over the domain of I₂.
* `QED.ThreeLoopE.i4P1_reduction`, `QED.ThreeLoopE.iteratedDeriv_i4PInt_one_of_F`.
-/

@[expose] public section

open MeasureTheory Set Complex QED.ThreeLoopD

namespace QED.ThreeLoopE

/-- The second Symanzik polynomial of I₄ in the Cheng–Wu gauge of I₂,
`(a, b, c, l, m, n) = ((1 - w) x, w, y₈, (1 - w)(1 - x), y₄, y₇)`. -/
def i4CWF (x w y₄ y₇ y₈ : ℝ) : ℝ :=
  i4F ((1 - w) * x) w y₈ ((1 - w) * (1 - x)) y₄ y₇

/-- The first Symanzik polynomial of I₄ in the gauge is that of I₂. -/
theorem i4U_gauge (x w y₄ y₇ y₈ : ℝ) :
    i4U ((1 - w) * x) w y₈ ((1 - w) * (1 - x)) y₄ y₇ = i2U x w y₄ y₇ y₈ := by
  unfold i4U i2U i2LineA i2LineB i2LineC
  ring

theorem i4U_pos {a b c l m n : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hl : 0 < l)
    (hm : 0 < m) (hn : 0 < n) : 0 < i4U a b c l m n := by
  unfold i4U
  positivity

theorem i4F_pos {a b c l m n : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hl : 0 < l)
    (hm : 0 < m) (hn : 0 < n) : 0 < i4F a b c l m n := by
  unfold i4F
  positivity

/-- The log-weighted period density `(4 log U - 3 log F) / U²` in the six parameters. -/
noncomputable def i4LogForm (a b c l m n : ℝ) : ℝ :=
  (4 * Real.log (i4U a b c l m n) - 3 * Real.log (i4F a b c l m n)) / i4U a b c l m n ^ 2

theorem i4LogForm_smul (a b c l m n t : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hl : 0 < l) (hm : 0 < m) (hn : 0 < n) (ht : 0 < t) :
    i4LogForm (t * a) (t * b) (t * c) (t * l) (t * m) (t * n) =
      (t ^ 6)⁻¹ * i4LogForm a b c l m n := by
  have hU := i4U_pos ha hb hc hl hm hn
  have hF := i4F_pos ha hb hc hl hm hn
  have eU : i4U (t * a) (t * b) (t * c) (t * l) (t * m) (t * n) = t ^ 3 * i4U a b c l m n := by
    unfold i4U; ring
  have eF : i4F (t * a) (t * b) (t * c) (t * l) (t * m) (t * n) = t ^ 4 * i4F a b c l m n := by
    unfold i4F; ring
  unfold i4LogForm
  rw [eU, eF, Real.log_mul (by positivity) hU.ne', Real.log_mul (by positivity) hF.ne',
    Real.log_pow, Real.log_pow]
  field_simp
  push_cast
  ring

theorem i4SimplexIntegrand_logForm (x : I4Coords) :
    i4SimplexIntegrand i4LogForm x = i4LogWeight x ^ 1 / i4SimplexU x ^ 2 := by
  rw [pow_one]
  rfl

private theorem i4Dom_pos {x : I4Coords} (hx : x ∈ i4Dom) :
    0 < i4SimplexU x ∧ 0 < i4SimplexF x := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hx
  have hl : 0 < i4Last x := by unfold i4Last; linarith
  exact ⟨i4U_pos h1 h2 h3 h4 h5 hl, i4F_pos h1 h2 h3 h4 h5 hl⟩

private theorem norm_i4Integrand_real {U F : ℝ} (hU : 0 < U) (hF : 0 < F) (t : ℝ) :
    ‖(U : ℂ) ^ (-2 + 4 * (t : ℂ)) * (F : ℂ) ^ (-3 * (t : ℂ))‖ =
      Real.exp (t * (4 * Real.log U - 3 * Real.log F)) / U ^ 2 := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hU, Complex.norm_cpow_eq_rpow_re_of_pos hF,
    Real.rpow_def_of_pos hU, Real.rpow_def_of_pos hF, ← Real.exp_add,
    show U ^ 2 = Real.exp (Real.log U * 2) by
      rw [← Real.rpow_def_of_pos hU]; norm_cast, ← Real.exp_sub]
  congr 1
  simp only [add_re, mul_re, neg_re, ofReal_re, ofReal_im, re_ofNat, im_ofNat]
  ring

private theorem abs_le_exp_add_exp (u δ : ℝ) (hδ : 0 < δ) :
    |u| ≤ (Real.exp (δ * u) + Real.exp (-δ * u)) / δ := by
  rw [le_div_iff₀ hδ]
  have h1 := Real.add_one_le_exp (δ * |u|)
  have h2 := Real.exp_pos (δ * u)
  have h3 := Real.exp_pos (-δ * u)
  rcases abs_cases u with ⟨hu, -⟩ | ⟨hu, -⟩
  · rw [hu] at h1; nlinarith
  · rw [hu, mul_neg, ← neg_mul] at h1; nlinarith

/-- **`L / U²` is integrable** on the simplex chart. -/
theorem integrableOn_i4P1L :
    IntegrableOn (fun x => i4LogWeight x ^ 1 / i4SimplexU x ^ 2) i4Dom := by
  have hS : MeasurableSet i4Dom := by
    unfold i4Dom
    simp only [Set.ofPred_and]
    exact (measurableSet_lt measurable_const (by fun_prop)).inter
      ((measurableSet_lt measurable_const (by fun_prop)).inter
        ((measurableSet_lt measurable_const (by fun_prop)).inter
          ((measurableSet_lt measurable_const (by fun_prop)).inter
            ((measurableSet_lt measurable_const (by fun_prop)).inter
              (measurableSet_lt (by fun_prop) measurable_const)))))
  set δ : ℝ := 1 / 200
  have hδ : (0 : ℝ) < δ := by norm_num
  have hp := integrableOn_i4Integrand (ε := ((δ : ℝ) : ℂ)) (by
    rw [Complex.norm_real, Real.norm_eq_abs]; norm_num [δ])
  have hn := integrableOn_i4Integrand (ε := ((-δ : ℝ) : ℂ)) (by
    rw [Complex.norm_real, Real.norm_eq_abs]; norm_num [δ])
  refine Integrable.mono' ((hp.norm.add hn.norm).div_const δ) ?_
    (ae_restrict_of_forall_mem hS fun x hx => ?_)
  · have hm : Measurable fun x => i4LogWeight x ^ 1 / i4SimplexU x ^ 2 := by
      unfold i4LogWeight i4SimplexU i4SimplexF i4Last i4U i4F
      fun_prop
    exact hm.aestronglyMeasurable
  · obtain ⟨hU, hF⟩ := i4Dom_pos hx
    simp only [Pi.add_apply, norm_i4Integrand_real hU hF, Real.norm_eq_abs, pow_one]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < i4SimplexU x ^ 2)]
    have h := abs_le_exp_add_exp (i4LogWeight x) δ hδ
    unfold i4LogWeight at h ⊢
    calc _ ≤ (Real.exp (δ * (4 * Real.log (i4SimplexU x) - 3 * Real.log (i4SimplexF x))) +
          Real.exp (-δ * (4 * Real.log (i4SimplexU x) - 3 * Real.log (i4SimplexF x)))) / δ /
          i4SimplexU x ^ 2 := by gcongr
      _ = _ := by ring

/-- The log-weighted density in the gauge of I₂. -/
theorem i4GaugeIntegrand_logForm (z : I4Coords) :
    i4GaugeIntegrand i4LogForm z = (1 - z.2.1) *
      (4 * Real.log (i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) -
        3 * Real.log (i4CWF z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2)) /
        i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2 := by
  simp only [i4GaugeIntegrand, i4LogForm, i4U_gauge, i4CWF]
  ring

private theorem i2Dom_measurable : MeasurableSet i2Dom :=
  measurableSet_Ioo.prod (measurableSet_Ioo.prod (measurableSet_Ioi.prod
    (measurableSet_Ioi.prod measurableSet_Ioi)))

theorem i4CWF_pos {z : I4Coords} (hz : z ∈ i2Dom) :
    0 < i4CWF z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 := by
  obtain ⟨⟨hx0, hx1⟩, ⟨hw0, hw1⟩, h4, h7, h8⟩ := hz
  simp only [mem_Ioi] at h4 h7 h8
  exact i4F_pos (mul_pos (sub_pos.mpr hw1) hx0) hw0 h8
    (mul_pos (sub_pos.mpr hw1) (sub_pos.mpr hx1)) h4 h7

/-- **`P'(0)` in the gauge of I₂**, with the integrand integrable there. -/
theorem i4P1_gauge :
    IntegrableOn (fun z : I4Coords => (1 - z.2.1) *
      (4 * Real.log (i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) -
        3 * Real.log (i4CWF z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2)) /
        i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2) i2Dom ∧
    iteratedDeriv 1 i4PInt 0 = ((∫ z in i2Dom, (1 - z.2.1) *
      (4 * Real.log (i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) -
        3 * Real.log (i4CWF z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2)) /
        i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2 : ℝ) : ℂ) := by
  have hg : ∀ a b c l m n t : ℝ, 0 < a → 0 < b → 0 < c → 0 < l → 0 < m → 0 < n → 0 < t →
      i4LogForm (t * a) (t * b) (t * c) (t * l) (t * m) (t * n) =
        (t ^ 6)⁻¹ * i4LogForm a b c l m n :=
    fun a b c l m n t ha hb hc hl hm hn ht => i4LogForm_smul a b c l m n t ha hb hc hl hm hn ht
  have eS : (fun x => i4LogWeight x ^ 1 / i4SimplexU x ^ 2) = i4SimplexIntegrand i4LogForm :=
    funext fun x => (i4SimplexIntegrand_logForm x).symm
  have eG : i4GaugeIntegrand i4LogForm = fun z : I4Coords => (1 - z.2.1) *
      (4 * Real.log (i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) -
        3 * Real.log (i4CWF z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2)) /
        i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2 :=
    funext i4GaugeIntegrand_logForm
  refine ⟨?_, ?_⟩
  · rw [← eG, ← i4Gauge_integrableOn_iff hg, ← eS]
    exact integrableOn_i4P1L
  · rw [iteratedDeriv_i4PInt (by norm_num), eS, i4Gauge_integral hg, eG]

/-- **`P'(0) = -3 π⁴ / 10 + 18 ζ(3) - 3 ∫ (1 - w) log (F / U) / U²`** over the domain of I₂,
with the `F`-part integrable. -/
theorem i4P1_reduction :
    IntegrableOn (fun z : I4Coords => (1 - z.2.1) *
        Real.log (i4CWF z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 /
          i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) /
          i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2) i2Dom ∧
      iteratedDeriv 1 i4PInt 0 = ((-(3 * Real.pi ^ 4 / 10) + 18 * QED.Polylog.zeta3 -
        3 * ∫ z in i2Dom, (1 - z.2.1) *
          Real.log (i4CWF z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 /
            i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) /
            i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2 : ℝ) : ℂ) := by
  obtain ⟨hU, vU⟩ := i2P1U_value
  obtain ⟨hL, vL⟩ := i4P1_gauge
  have eq : EqOn (fun z : I4Coords =>
      ((1 - z.2.1) * Real.log (i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) /
          i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2 -
        (1 - z.2.1) * (4 * Real.log (i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) -
          3 * Real.log (i4CWF z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2)) /
          i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2) / 3)
      (fun z : I4Coords => (1 - z.2.1) *
        Real.log (i4CWF z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 /
          i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) /
          i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2) i2Dom := fun z hz => by
    obtain ⟨hUp, -⟩ := i2UF_pos hz
    simp only
    rw [Real.log_div (i4CWF_pos hz).ne' hUp.ne']
    ring
  have hF := IntegrableOn.congr_fun ((hU.sub hL).div_const 3) eq i2Dom_measurable
  refine ⟨hF, ?_⟩
  rw [vL]
  congr 1
  have eq2 : EqOn (fun z : I4Coords => (1 - z.2.1) *
      (4 * Real.log (i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) -
        3 * Real.log (i4CWF z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2)) /
        i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2)
      (fun z : I4Coords => (1 - z.2.1) *
          Real.log (i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) /
          i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2 - 3 * ((1 - z.2.1) *
        Real.log (i4CWF z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 /
          i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) /
          i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2)) i2Dom := fun z hz => by
    obtain ⟨hUp, -⟩ := i2UF_pos hz
    simp only
    rw [Real.log_div (i4CWF_pos hz).ne' hUp.ne']
    ring
  rw [setIntegral_congr_fun i2Dom_measurable eq2, integral_sub hU (hF.const_mul 3),
    integral_const_mul, vU]

/-- **`P'(0) = i4P1` from the `F`-part**:
`∫ (1 - w) log (F / U) / U² = -π⁴ / 45 + 4 ζ(3) - π² / 3` gives the first coefficient. -/
theorem iteratedDeriv_i4PInt_one_of_F
    (h : ∫ z in i2Dom, (1 - z.2.1) * Real.log (i4CWF z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 /
      i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) / i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2 =
      -(Real.pi ^ 4 / 45) + 4 * QED.Polylog.zeta3 - Real.pi ^ 2 / 3) :
    iteratedDeriv 1 i4PInt 0 = i4P1 := by
  rw [i4P1_reduction.2, h, i4P1]
  push_cast
  ring

end QED.ThreeLoopE

end
