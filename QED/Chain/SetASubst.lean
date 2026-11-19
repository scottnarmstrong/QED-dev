/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.SetAFubini
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Set (a): the vertex kernel in closed form and the conformal variable

Helper analysis for the sixth-order set (a) of `docs/HIGHER-LOOP-PLAN.md`. It is **not** frozen.

* The `x`-integral `K̃(δ) = ∫₀¹ x²(1-x)/(x² + (1-x)·4/(1-δ²)) dx` of Kaptari et al. 2025,
  eq. (26) at `r = 1`, in closed form: the denominator is `(x - 2/(1-δ))(x - 2/(1+δ))`, so
  `K̃(δ) = -1/2 - (3+δ²)/(1-δ²) + (1-δ)²/(δ(1+δ)²) ln((1-δ)/2) - (1+δ)²/(δ(1-δ)²) ln((1+δ)/2)`.
* The substitution `δ = (1-u)/(1+u)` (an involution of `(0,1)`, with `|dδ/du| = 2/(1+u)²`)
  turns every logarithm of eq. (20) and of `K̃` into a combination of `ln u`, `ln(1-u)`,
  `ln(1+u)`, and the dilogarithm arguments into `±u`.

## Main statements

* `integral_setAKer_eq`: the closed form of `K̃(δ)` for `0 < δ < 1`.
* `QED.Chain.setAJ`: the set (a) integrand in the variable `u`, written with the atoms
  `ln u, ln(1-u), ln(1+u), Li₂(u), Li₂(-u)`.
* `intervalIntegrable_setAJ`, `integral_setADispersive_eq_setAJ`: the dispersive integral of
  eq. (25) equals `∫₀¹ setAJ u du`.
* `integral_setA_eq_setAJ`: the set (a) integral equals `∫₀¹ setAJ u du`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology QED.Polylog

namespace QED.Chain

/-! ### The closed form of `K̃` -/

/-- The closed form of `K̃(δ)`. -/
noncomputable def setAKt (δ : ℝ) : ℝ :=
  -1 / 2 - (3 + δ ^ 2) / (1 - δ ^ 2) + (1 - δ) ^ 2 / (δ * (1 + δ) ^ 2) * log ((1 - δ) / 2) -
    (1 + δ) ^ 2 / (δ * (1 - δ) ^ 2) * log ((1 + δ) / 2)

/-- An `x`-antiderivative of the vertex kernel at photon mass² `4/(1-δ²)`. -/
noncomputable def setAKtPrim (δ x : ℝ) : ℝ :=
  -x ^ 2 / 2 - (3 + δ ^ 2) / (1 - δ ^ 2) * x +
    (1 - δ) ^ 2 / (δ * (1 + δ) ^ 2) * log (2 - (1 + δ) * x) -
    (1 + δ) ^ 2 / (δ * (1 - δ) ^ 2) * log (2 - (1 - δ) * x)

theorem hasDerivAt_setAKtPrim {δ x : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (setAKtPrim δ) (x ^ 2 * (1 - x) / (x ^ 2 + (1 - x) * (4 / (1 - δ ^ 2)))) x := by
  obtain ⟨h0, h1⟩ := hδ
  obtain ⟨hx0, hx1⟩ := hx
  have ha : 0 < 2 - (1 + δ) * x := by nlinarith
  have hb : 0 < 2 - (1 - δ) * x := by nlinarith
  have hA : HasDerivAt (fun y => 2 - (1 + δ) * y) (-(1 + δ)) x := by
    simpa using ((hasDerivAt_id x).const_mul (1 + δ)).const_sub 2
  have hB : HasDerivAt (fun y => 2 - (1 - δ) * y) (-(1 - δ)) x := by
    simpa using ((hasDerivAt_id x).const_mul (1 - δ)).const_sub 2
  have h := ((((hasDerivAt_pow 2 x).neg.div_const 2).sub
    ((hasDerivAt_id x).const_mul ((3 + δ ^ 2) / (1 - δ ^ 2)))).add
    ((hA.log ha.ne').const_mul ((1 - δ) ^ 2 / (δ * (1 + δ) ^ 2)))).sub
    ((hB.log hb.ne').const_mul ((1 + δ) ^ 2 / (δ * (1 - δ) ^ 2)))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  · have hq : 1 - δ ^ 2 ≠ 0 := by nlinarith
    have hm : 1 - δ ≠ 0 := by linarith
    have hp : 1 + δ ≠ 0 := by linarith
    have ha' := ha.ne'
    have hb' := hb.ne'
    have hd : x ^ 2 + (1 - x) * (4 / (1 - δ ^ 2)) ≠ 0 := by
      rw [show x ^ 2 + (1 - x) * (4 / (1 - δ ^ 2)) =
        (2 - (1 + δ) * x) * (2 - (1 - δ) * x) / (1 - δ ^ 2) by field_simp; ring]
      exact div_ne_zero (mul_pos ha hb).ne' hq
    have key : x ^ 2 * (1 - x) / (x ^ 2 + (1 - x) * (4 / (1 - δ ^ 2))) =
        x ^ 2 * (1 - x) * (1 - δ ^ 2) / ((2 - (1 + δ) * x) * (2 - (1 - δ) * x)) := by
      rw [div_eq_div_iff hd (mul_ne_zero ha' hb')]
      field_simp
      ring
    rw [key]
    field_simp
    ring
  · simp only [setAKtPrim, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id]

/-- **The closed form of `K̃`.** -/
theorem integral_setAKer_eq {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    ∫ x in (0 : ℝ)..1, x ^ 2 * (1 - x) / (x ^ 2 + (1 - x) * (4 / (1 - δ ^ 2))) = setAKt δ := by
  have hcont : ContinuousOn (fun x => x ^ 2 * (1 - x) / (x ^ 2 + (1 - x) * (4 / (1 - δ ^ 2))))
      (uIcc 0 1) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    have hq : 0 < 1 - δ ^ 2 := by nlinarith [hδ.1, hδ.2]
    rcases eq_or_lt_of_le hx.2 with h | h
    · subst h; norm_num
    · have : 0 < (1 - x) * (4 / (1 - δ ^ 2)) := mul_pos (by linarith) (by positivity)
      have := sq_nonneg x
      exact (by linarith : (0 : ℝ) < x ^ 2 + (1 - x) * (4 / (1 - δ ^ 2))).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hasDerivAt_setAKtPrim hδ
    (by rwa [uIcc_of_le zero_le_one] at hx)) hcont.intervalIntegrable]
  obtain ⟨h0, h1⟩ := hδ
  have hm : (0 : ℝ) < 1 - δ := by linarith
  simp only [setAKtPrim, setAKt]
  rw [show (2 : ℝ) - (1 + δ) * 1 = 2 * ((1 - δ) / 2) by ring,
    show (2 : ℝ) - (1 - δ) * 1 = 2 * ((1 + δ) / 2) by ring,
    log_mul (by norm_num) (by positivity), log_mul (by norm_num) (by positivity)]
  simp only [mul_zero, sub_zero]
  ring

/-! ### The conformal variable `u` -/

/-- `δ = (1-u)/(1+u)`. -/
noncomputable def ksDelta (u : ℝ) : ℝ := (1 - u) / (1 + u)

theorem ksDelta_mem {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : ksDelta u ∈ Ioo (0 : ℝ) 1 :=
  ksU_mem hu

theorem ksDelta_ksDelta {u : ℝ} (hu : -1 < u) : ksDelta (ksDelta u) = u := by
  have : 1 + u ≠ 0 := by linarith
  unfold ksDelta
  field_simp
  ring

theorem image_ksDelta : ksDelta '' Ioo 0 1 = Ioo 0 1 := by
  ext δ
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ksDelta_mem hu
  · intro hδ
    exact ⟨ksDelta δ, ksDelta_mem hδ, ksDelta_ksDelta (by linarith [hδ.1])⟩

theorem injOn_ksDelta : InjOn ksDelta (Ioo 0 1) := fun a ha b hb h => by
  rw [← ksDelta_ksDelta (u := a) (by linarith [ha.1]),
    ← ksDelta_ksDelta (u := b) (by linarith [hb.1]), h]

theorem hasDerivAt_ksDelta {u : ℝ} (hu : -1 < u) :
    HasDerivAt ksDelta (-2 / (1 + u) ^ 2) u := by
  have hp : 1 + u ≠ 0 := by linarith
  have h : HasDerivAt (fun x : ℝ => (1 - x) / (1 + x))
      ((-1 * (1 + u) - (1 - u) * 1) / (1 + u) ^ 2) u :=
    ((hasDerivAt_id' u).const_sub 1).div ((hasDerivAt_id' u).const_add 1) hp
  show HasDerivAt (fun x : ℝ => (1 - x) / (1 + x)) _ u
  convert h using 1
  field_simp
  ring

/-- The change of variables `δ = (1-u)/(1+u)` on `(0,1)`. -/
theorem integral_Ioo_comp_ksDelta (f : ℝ → ℝ) :
    ∫ δ in Ioo (0 : ℝ) 1, f δ = ∫ u in Ioo (0 : ℝ) 1, 2 / (1 + u) ^ 2 * f (ksDelta u) := by
  have h := integral_image_eq_integral_abs_deriv_smul (f := ksDelta)
    (f' := fun u => -2 / (1 + u) ^ 2) measurableSet_Ioo
    (fun u hu => (hasDerivAt_ksDelta (by linarith [hu.1])).hasDerivWithinAt) injOn_ksDelta f
  rw [image_ksDelta] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  have : 0 < (1 + u) ^ 2 := by have := hu.1; positivity
  simp only [smul_eq_mul]
  rw [abs_div, abs_neg, abs_of_pos this]
  norm_num

theorem integrableOn_Ioo_comp_ksDelta {f : ℝ → ℝ} (hf : IntegrableOn f (Ioo 0 1)) :
    IntegrableOn (fun u => 2 / (1 + u) ^ 2 * f (ksDelta u)) (Ioo 0 1) := by
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul (f := ksDelta)
    (f' := fun u => -2 / (1 + u) ^ 2) measurableSet_Ioo
    (fun u hu => (hasDerivAt_ksDelta (by linarith [hu.1])).hasDerivWithinAt) injOn_ksDelta f).1
    (by rwa [image_ksDelta])
  refine h.congr_fun (fun u hu => ?_) measurableSet_Ioo
  have : 0 < (1 + u) ^ 2 := by have := hu.1; positivity
  simp only [smul_eq_mul]
  rw [abs_div, abs_neg, abs_of_pos this]
  norm_num

/-! ### The integrand in `u` -/

/-- `ρ⁽⁴⁾((1-u)/(1+u))` in the atoms `ln u, ln(1-u), ln(1+u), Li₂(u), Li₂(-u)`. -/
noncomputable def ksRhoU (u : ℝ) : ℝ :=
  (11 / 16 + 11 / 24 * ksDelta u ^ 2 - 7 / 48 * ksDelta u ^ 4 +
      (1 / 2 + ksDelta u ^ 2 / 3 - ksDelta u ^ 4 / 6) * (-log (1 + u) - 2 * log (1 - u))) *
      (-log u) +
    ksDelta u * (5 / 8 - 3 / 8 * ksDelta u ^ 2 - (1 / 2 - ksDelta u ^ 2 / 6) *
      (4 * log (1 - u) + 2 * log (1 + u) - 3 * log u)) +
    2 * (1 / 2 + ksDelta u ^ 2 / 3 - ksDelta u ^ 4 / 6) * (2 * Li₂ u + Li₂ (-u))

/-- `K̃((1-u)/(1+u))` in the atoms. -/
noncomputable def setAKtU (u : ℝ) : ℝ :=
  -1 / 2 - (3 + ksDelta u ^ 2) / (1 - ksDelta u ^ 2) +
    (1 - ksDelta u) ^ 2 / (ksDelta u * (1 + ksDelta u) ^ 2) * (log u - log (1 + u)) -
    (1 + ksDelta u) ^ 2 / (ksDelta u * (1 - ksDelta u) ^ 2) * (-log (1 + u))

/-- **The set (a) integrand in the conformal variable `u`.** -/
noncomputable def setAJ (u : ℝ) : ℝ :=
  2 / (1 + u) ^ 2 * (2 * ksDelta u / (1 - ksDelta u ^ 2)) * ksRhoU u * setAKtU u

theorem ksRho_ksDelta {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : ksRho (ksDelta u) = ksRhoU u := by
  obtain ⟨h0, h1⟩ := hu
  have hm : 0 < 1 - u := by linarith
  have hp : 0 < 1 + u := by linarith
  have hu0 : u ≠ 0 := h0.ne'
  have hd : 1 - ksDelta u ≠ 0 := by
    have : ksDelta u < 1 := (ksDelta_mem ⟨h0, h1⟩).2
    linarith
  have e1 : (1 + ksDelta u) / (1 - ksDelta u) = u⁻¹ := by
    rw [div_eq_iff hd, inv_mul_eq_div, eq_div_iff hu0]
    unfold ksDelta; field_simp; ring
  have e2 : (1 + ksDelta u) ^ 3 / (8 * ksDelta u ^ 2) = ((1 + u) * (1 - u) ^ 2)⁻¹ := by
    unfold ksDelta; field_simp; ring
  have e3 : 64 * ksDelta u ^ 4 / (1 - ksDelta u ^ 2) ^ 3 = (1 - u) ^ 4 * (1 + u) ^ 2 / u ^ 3 := by
    have hq : (1 - ksDelta u ^ 2) ^ 3 ≠ 0 := by
      unfold ksDelta
      rw [show 1 - ((1 - u) / (1 + u)) ^ 2 = 4 * u / (1 + u) ^ 2 by field_simp; ring]
      positivity
    rw [div_eq_div_iff hq (by positivity)]
    unfold ksDelta; field_simp; ring
  have e4 : (1 - ksDelta u) / (1 + ksDelta u) = u := ksDelta_ksDelta (by linarith)
  have l2 : log ((1 + u) * (1 - u) ^ 2) = log (1 + u) + 2 * log (1 - u) := by
    rw [log_mul hp.ne' (by positivity), log_pow]; push_cast; ring
  have l3 : log ((1 - u) ^ 4 * (1 + u) ^ 2 / u ^ 3) =
      4 * log (1 - u) + 2 * log (1 + u) - 3 * log u := by
    rw [log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      log_pow, log_pow, log_pow]
    push_cast; ring
  unfold ksRho ksRhoU
  rw [e1, e2, e3, e4]
  simp only [log_inv]
  rw [l2, l3]
  ring

theorem setAKt_ksDelta {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : setAKt (ksDelta u) = setAKtU u := by
  obtain ⟨h0, h1⟩ := hu
  have hp : 0 < 1 + u := by linarith
  have e1 : (1 - ksDelta u) / 2 = u / (1 + u) := by unfold ksDelta; field_simp; ring
  have e2 : (1 + ksDelta u) / 2 = (1 + u)⁻¹ := by unfold ksDelta; field_simp; ring
  unfold setAKt setAKtU
  rw [e1, e2, log_div h0.ne' hp.ne', log_inv]

/-- The dispersive integrand of eq. (25), in closed form. -/
theorem setADispersive_eq {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    2 * δ / (1 - δ ^ 2) * ksRho δ * (∫ x in (0 : ℝ)..1,
      x ^ 2 * (1 - x) / (x ^ 2 + (1 - x) * (4 / (1 - δ ^ 2)))) =
      2 * δ / (1 - δ ^ 2) * ksRho δ * setAKt δ := by
  rw [integral_setAKer_eq hδ]

theorem setAJ_eq {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    2 / (1 + u) ^ 2 * (2 * ksDelta u / (1 - ksDelta u ^ 2) * ksRho (ksDelta u) *
      ∫ x in (0 : ℝ)..1, x ^ 2 * (1 - x) / (x ^ 2 + (1 - x) * (4 / (1 - ksDelta u ^ 2)))) =
      setAJ u := by
  rw [setADispersive_eq (ksDelta_mem hu), ksRho_ksDelta hu, setAKt_ksDelta hu, setAJ]
  ring

/-- `setAJ` is interval integrable on `[0,1]`. -/
theorem intervalIntegrable_setAJ : IntervalIntegrable setAJ volume 0 1 := by
  have h := intervalIntegrable_setADispersive
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one, IntegrableOn,
    ← Measure.restrict_congr_set Ioo_ae_eq_Ioc] at h ⊢
  refine (integrableOn_Ioo_comp_ksDelta h).congr_fun (fun u hu => setAJ_eq hu) measurableSet_Ioo

/-- **The dispersive integral in the conformal variable.** -/
theorem integral_setADispersive_eq_setAJ :
    ∫ δ in (0 : ℝ)..1, 2 * δ / (1 - δ ^ 2) * ksRho δ * (∫ x in (0 : ℝ)..1,
      x ^ 2 * (1 - x) / (x ^ 2 + (1 - x) * (4 / (1 - δ ^ 2)))) = ∫ u in (0 : ℝ)..1, setAJ u := by
  rw [interval_eq_Ioo, interval_eq_Ioo, integral_Ioo_comp_ksDelta]
  exact setIntegral_congr_fun measurableSet_Ioo fun u hu => setAJ_eq hu

/-- **Set (a) in the conformal variable**: `∫₀¹ (1-x) Π̂⁽⁴⁾(x²/(1-x)) dx = ∫₀¹ setAJ u du`. -/
theorem integral_setA_eq_setAJ :
    ∫ x in (0 : ℝ)..1, (1 - x) * piHat4 (x ^ 2 / (1 - x)) = ∫ u in (0 : ℝ)..1, setAJ u := by
  rw [integral_setA_eq_dispersive, integral_setADispersive_eq_setAJ]

end QED.Chain
