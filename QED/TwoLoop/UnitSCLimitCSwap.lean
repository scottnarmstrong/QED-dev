/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLCloseSubst
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The corner unit C: the substitution `w = b(1-x)/x` with the lower limit `β(x)`

Section 2.2 of `docs/TWO-LOOP-UNITS.md`, stage (1) of the `S + C` link for the corner pair. In the
hierarchical variables of the corner graph the outer electron and photon parameters are
`b = z_o + g` and `w = z_a + e` (`g, e > 0`). Put `w = b(1-x)/x` at fixed `b`: then `z_a > 0` is
`x(b + e) < b`, and exchanging the order of the integrations over `z_o` and `x` gives, for every
`x ∈ (0, 1)`, the range `b > β(x) = max(g, e x/(1-x))` (the two branches of section 2.2). This
file proves, for any `F` integrable on `(0, ∞)²`:

* `integral_Ioi_eq_substH`: for `z_o + g > 0`, the substitution
  `∫_{z_a > 0} F(z_o, z_a) = ∫_0^1 [x(b + e) < b] F(z_o, b(1-x)/x - e) b/x² dx` (`substH`);
* `integral_substB_swap`: **the exchange**
  `∫_{z_o > 0} ∫_{z_a > 0} F = ∫_0^1 dx ∫_{z > 0} F(b - g, b(1-x)/x - e) b/x² dz`, `b = z + β(x)`
  (`substB`, `betaG`), and the inner integrand is integrable for almost every `x`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology Function

namespace QED.TwoLoop.UnitSCLimit

/-! ### The substitution `z_a = b(1-x)/x - e` -/

section SubstE

variable {b e : ℝ}

theorem image_substE (hb : 0 < b) (he : 0 < e) :
    (fun x => b * (1 - x) / x - e) '' Ioo (0 : ℝ) (b / (b + e)) = Ioi 0 := by
  ext z
  simp only [mem_image, mem_Ioo, mem_Ioi]
  constructor
  · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
    rw [lt_div_iff₀ (by positivity)] at hx1
    rw [sub_pos, lt_div_iff₀ hx0]
    nlinarith
  · intro hz
    refine ⟨b / (b + e + z), ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    · have : b + e + z ≠ 0 := by positivity
      field_simp
      ring

theorem injOn_substE (hb : 0 < b) :
    InjOn (fun x => b * (1 - x) / x - e) (Ioo (0 : ℝ) (b / (b + e))) := by
  intro x hx y hy hxy
  simp only at hxy
  have e1 : ∀ t : ℝ, t ≠ 0 → b * (1 - t) / t - e = b * t⁻¹ - (b + e) := fun t ht => by
    field_simp
    ring
  rw [e1 x hx.1.ne', e1 y hy.1.ne'] at hxy
  have h2 : b * x⁻¹ = b * y⁻¹ := by linarith
  exact inv_inj.mp (mul_left_cancel₀ hb.ne' h2)

theorem hasDerivWithinAt_substE {x : ℝ} (hx : 0 < x) (s : Set ℝ) :
    HasDerivWithinAt (fun x => b * (1 - x) / x - e) (-(b / x ^ 2)) s x := by
  have hx0 := hx.ne'
  have : HasDerivAt (fun x => b * (1 - x) / x - e)
      (((b * (0 - 1)) * x - b * (1 - x) * 1) / x ^ 2) x :=
    ((((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).const_mul b).div (hasDerivAt_id x)
      hx0).sub_const e
  refine (this.congr_deriv ?_).hasDerivWithinAt
  field_simp
  ring

theorem abs_substE_deriv {x : ℝ} (hx : 0 < x) (hb : 0 < b) : |-(b / x ^ 2)| = b / x ^ 2 := by
  rw [abs_neg, abs_of_pos (by positivity)]

/-- **The substitution `z_a = b(1-x)/x - e`**:
`∫_{z_a > 0} f = ∫_0^{b/(b+e)} f(b(1-x)/x - e) b/x² dx`. -/
theorem integral_Ioi_eq_substE (hb : 0 < b) (he : 0 < e) (f : ℝ → ℝ) :
    ∫ z in Ioi (0 : ℝ), f z =
      ∫ x in Ioo (0 : ℝ) (b / (b + e)), f (b * (1 - x) / x - e) * (b / x ^ 2) := by
  rw [← image_substE hb he, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun x hx => hasDerivWithinAt_substE hx.1 _) (injOn_substE hb)]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  simp only [abs_substE_deriv hx.1 hb, smul_eq_mul]
  ring

theorem integrableOn_Ioi_iff_substE (hb : 0 < b) (he : 0 < e) (f : ℝ → ℝ) :
    IntegrableOn f (Ioi 0) ↔
      IntegrableOn (fun x => f (b * (1 - x) / x - e) * (b / x ^ 2))
        (Ioo (0 : ℝ) (b / (b + e))) := by
  rw [← image_substE hb he, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun x hx => hasDerivWithinAt_substE hx.1 _) (injOn_substE hb)]
  refine integrableOn_congr_fun (fun x hx => ?_) measurableSet_Ioo
  simp only [abs_substE_deriv hx.1 hb, smul_eq_mul]
  ring

theorem measurableSet_cut (b e : ℝ) : MeasurableSet {x : ℝ | x * (b + e) < b} :=
  measurableSet_lt (by fun_prop) measurable_const

theorem Ioo_inter_cut (hb : 0 < b) (he : 0 < e) :
    Ioo (0 : ℝ) 1 ∩ {x : ℝ | x * (b + e) < b} = Ioo 0 (b / (b + e)) := by
  ext x
  simp only [mem_inter_iff, mem_Ioo, mem_ofPred_eq]
  rw [lt_div_iff₀ (by positivity : 0 < b + e)]
  constructor
  · rintro ⟨⟨h0, -⟩, h⟩
    exact ⟨h0, h⟩
  · rintro ⟨h0, h⟩
    exact ⟨⟨h0, by nlinarith⟩, h⟩

end SubstE

/-! ### The cut integrand on `(0, ∞) × (0, 1)` -/

/-- The integrand after `z_a = (z_o + g)(1-x)/x - e`, with its Jacobian, cut to `z_a > 0`. -/
noncomputable def substH (F : ℝ → ℝ → ℝ) (g e zo x : ℝ) : ℝ :=
  if x * (zo + g + e) < zo + g then F zo ((zo + g) * (1 - x) / x - e) * ((zo + g) / x ^ 2)
  else 0

theorem substH_eq_indicator (F : ℝ → ℝ → ℝ) (g e zo x : ℝ) :
    substH F g e zo x = {x : ℝ | x * (zo + g + e) < zo + g}.indicator
      (fun x => F zo ((zo + g) * (1 - x) / x - e) * ((zo + g) / x ^ 2)) x := by
  simp only [substH, Set.indicator_apply, mem_ofPred_eq]

theorem integral_Ioi_eq_substH {F : ℝ → ℝ → ℝ} {g e zo : ℝ} (hb : 0 < zo + g) (he : 0 < e) :
    ∫ za in Ioi (0 : ℝ), F zo za = ∫ x in Ioo (0 : ℝ) 1, substH F g e zo x := by
  simp_rw [substH_eq_indicator]
  rw [integral_Ioi_eq_substE hb he, setIntegral_indicator (measurableSet_cut _ _),
    Ioo_inter_cut hb he]

theorem integrableOn_Ioi_iff_substH {F : ℝ → ℝ → ℝ} {g e zo : ℝ} (hb : 0 < zo + g)
    (he : 0 < e) :
    IntegrableOn (F zo) (Ioi 0) ↔ IntegrableOn (fun x => substH F g e zo x) (Ioo (0 : ℝ) 1) := by
  simp_rw [substH_eq_indicator]
  rw [integrableOn_Ioi_iff_substE hb he (F zo), IntegrableOn, IntegrableOn,
    integrable_indicator_iff (measurableSet_cut _ _), IntegrableOn,
    Measure.restrict_restrict (measurableSet_cut _ _), inter_comm, Ioo_inter_cut hb he]

theorem integral_norm_substH {F : ℝ → ℝ → ℝ} {g e zo : ℝ} (hb : 0 < zo + g) (he : 0 < e) :
    ∫ za in Ioi (0 : ℝ), ‖F zo za‖ = ∫ x in Ioo (0 : ℝ) 1, ‖substH F g e zo x‖ := by
  rw [integral_Ioi_eq_substH (F := fun zo za => ‖F zo za‖) hb he]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have := hx.1
  simp only [substH]
  split_ifs
  · rw [norm_mul, Real.norm_eq_abs ((zo + g) / x ^ 2), abs_of_pos (by positivity)]
  · simp

theorem measurable_substH {F : ℝ → ℝ → ℝ} (hF : Measurable (uncurry F)) (g e : ℝ) :
    Measurable (uncurry (substH F g e)) := by
  change Measurable fun p : ℝ × ℝ => substH F g e p.1 p.2
  unfold substH
  refine Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) ?_ measurable_const
  have h1 : Measurable fun p : ℝ × ℝ => (p.1 + g) * (1 - p.2) / p.2 - e := by fun_prop
  exact (hF.comp (measurable_fst.prodMk h1)).mul (by fun_prop)

/-- The cut integrand is integrable on `(0, ∞) × (0, 1)` when `F` is integrable on `(0, ∞)²`. -/
theorem integrable_substH {F : ℝ → ℝ → ℝ} {g e : ℝ} (hg : 0 < g) (he : 0 < e)
    (hF : Measurable (uncurry F))
    (hint : Integrable (uncurry F) ((volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ))))) :
    Integrable (uncurry (substH F g e)) ((volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hpos : ∀ zo ∈ Ioi (0 : ℝ), 0 < zo + g := fun zo hz => by
    simp only [mem_Ioi] at hz; linarith
  refine (integrable_prod_iff (measurable_substH hF g e).aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · filter_upwards [hint.prod_right_ae, ae_restrict_mem measurableSet_Ioi] with zo hzo hz
    exact (integrableOn_Ioi_iff_substH (hpos zo hz) he).mp hzo
  · refine hint.integral_norm_prod_left.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with zo hz
    change ∫ za in Ioi (0 : ℝ), ‖F zo za‖ = ∫ x in Ioo (0 : ℝ) 1, ‖substH F g e zo x‖
    exact integral_norm_substH (hpos zo hz) he

/-! ### The lower limit `β(x)` -/

/-- **The lower limit** `β(x) = max(g, e x/(1-x))` of the outer electron parameter. -/
noncomputable def betaG (g e x : ℝ) : ℝ := max g (e * x / (1 - x))

theorem le_betaG (g e x : ℝ) : g ≤ betaG g e x := le_max_left _ _

theorem betaG_pos {g e x : ℝ} (hg : 0 < g) : 0 < betaG g e x := hg.trans_le (le_betaG g e x)

theorem Ioi_inter_cut {g e x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Ioi (0 : ℝ) ∩ {zo : ℝ | x * (zo + g + e) < zo + g} = Ioi (betaG g e x - g) := by
  ext zo
  simp only [mem_inter_iff, mem_Ioi, mem_ofPred_eq, betaG]
  have h1x : 0 < 1 - x := by linarith [hx.2]
  rw [sub_lt_iff_lt_add, max_lt_iff, div_lt_iff₀ h1x]
  constructor
  · rintro ⟨h0, h⟩
    exact ⟨by linarith, by nlinarith⟩
  · rintro ⟨h0, h⟩
    exact ⟨by linarith, by nlinarith⟩

/-- **The integrand on `b > β(x)`**: `F(b - g, b(1-x)/x - e) b/x²` at `b = z + β(x)`. -/
noncomputable def substB (F : ℝ → ℝ → ℝ) (g e x z : ℝ) : ℝ :=
  F (z + (betaG g e x - g)) ((z + betaG g e x) * (1 - x) / x - e) * ((z + betaG g e x) / x ^ 2)

theorem substB_eq (F : ℝ → ℝ → ℝ) (g e x z : ℝ) :
    substB F g e x z = (fun zo => F zo ((zo + g) * (1 - x) / x - e) * ((zo + g) / x ^ 2))
      (z + (betaG g e x - g)) := by
  simp only [substB, show z + (betaG g e x - g) + g = z + betaG g e x by ring]

theorem integral_Ioi_shift (f : ℝ → ℝ) (c : ℝ) :
    ∫ z in Ioi c, f z = ∫ z in Ioi (0 : ℝ), f (z + c) := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ)) (f := fun z => z + c)
    (f' := fun _ => 1) measurableSet_Ioi
    (fun z _ => ((hasDerivAt_id' z).add_const c).hasDerivWithinAt) (add_left_injective c).injOn f
  rw [image_add_const_Ioi, zero_add] at h
  rw [h]
  simp

theorem integrableOn_Ioi_shift_iff (f : ℝ → ℝ) (c : ℝ) :
    IntegrableOn f (Ioi c) ↔ IntegrableOn (fun z => f (z + c)) (Ioi 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Ioi (0 : ℝ))
    (f := fun z => z + c) (f' := fun _ => 1) measurableSet_Ioi
    (fun z _ => ((hasDerivAt_id' z).add_const c).hasDerivWithinAt) (add_left_injective c).injOn f
  rw [image_add_const_Ioi, zero_add] at h
  rw [h]
  simp

theorem integral_substH_eq_substB {F : ℝ → ℝ → ℝ} {g e x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∫ zo in Ioi (0 : ℝ), substH F g e zo x = ∫ z in Ioi (0 : ℝ), substB F g e x z := by
  have hind : ∀ zo, substH F g e zo x = {zo : ℝ | x * (zo + g + e) < zo + g}.indicator
      (fun zo => F zo ((zo + g) * (1 - x) / x - e) * ((zo + g) / x ^ 2)) zo := fun zo => by
    simp only [substH, Set.indicator_apply, mem_ofPred_eq]
  simp_rw [hind]
  rw [setIntegral_indicator (measurableSet_lt (by fun_prop) (by fun_prop)), Ioi_inter_cut hx,
    integral_Ioi_shift]
  simp only [substB_eq]

theorem integrableOn_substH_iff_substB {F : ℝ → ℝ → ℝ} {g e x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun zo => substH F g e zo x) (Ioi 0) ↔ IntegrableOn (substB F g e x) (Ioi 0) := by
  have hind : (fun zo => substH F g e zo x) = {zo : ℝ | x * (zo + g + e) < zo + g}.indicator
      (fun zo => F zo ((zo + g) * (1 - x) / x - e) * ((zo + g) / x ^ 2)) := by
    funext zo
    simp only [substH, Set.indicator_apply, mem_ofPred_eq]
  have hB : substB F g e x = fun z =>
      (fun zo => F zo ((zo + g) * (1 - x) / x - e) * ((zo + g) / x ^ 2)) (z + (betaG g e x - g)) := by
    funext z
    exact substB_eq F g e x z
  rw [hind, IntegrableOn, integrable_indicator_iff (measurableSet_lt (by fun_prop) (by fun_prop)),
    IntegrableOn, Measure.restrict_restrict (measurableSet_lt (by fun_prop) (by fun_prop)),
    inter_comm, Ioi_inter_cut hx, hB]
  exact integrableOn_Ioi_shift_iff _ _

/-- **The exchange of the integrations with the lower limit `β(x)`**: for `g, e > 0` and `F`
integrable on `(0, ∞)²`,
`∫_{z_o > 0} ∫_{z_a > 0} F = ∫_0^1 dx ∫_{z > 0} F(b - g, b(1-x)/x - e) b/x² dz`,
`b = z + max(g, e x/(1-x))`, and the inner integrand is integrable for almost every `x`. -/
theorem integral_substB_swap {F : ℝ → ℝ → ℝ} {g e : ℝ} (hg : 0 < g) (he : 0 < e)
    (hF : Measurable (uncurry F))
    (hint : Integrable (uncurry F) ((volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ))))) :
    (∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), IntegrableOn (substB F g e x) (Ioi 0)) ∧
      ∫ zo in Ioi (0 : ℝ), ∫ za in Ioi (0 : ℝ), F zo za =
        ∫ x in Ioo (0 : ℝ) 1, ∫ z in Ioi (0 : ℝ), substB F g e x z := by
  have hT := integrable_substH hg he hF hint
  have hpos : ∀ zo ∈ Ioi (0 : ℝ), 0 < zo + g := fun zo hz => by
    simp only [mem_Ioi] at hz; linarith
  refine ⟨?_, ?_⟩
  · filter_upwards [hT.prod_left_ae, ae_restrict_mem measurableSet_Ioo] with x hx hxm
    exact (integrableOn_substH_iff_substB hxm).mp hx
  · calc ∫ zo in Ioi (0 : ℝ), ∫ za in Ioi (0 : ℝ), F zo za
        = ∫ zo in Ioi (0 : ℝ), ∫ x in Ioo (0 : ℝ) 1, substH F g e zo x :=
          setIntegral_congr_fun measurableSet_Ioi fun zo hz => integral_Ioi_eq_substH (hpos zo hz) he
      _ = ∫ x in Ioo (0 : ℝ) 1, ∫ zo in Ioi (0 : ℝ), substH F g e zo x := integral_integral_swap hT
      _ = ∫ x in Ioo (0 : ℝ) 1, ∫ z in Ioi (0 : ℝ), substB F g e x z :=
          setIntegral_congr_fun measurableSet_Ioo fun x hx => integral_substH_eq_substB hx

end QED.TwoLoop.UnitSCLimit

end
