/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKCornInW
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G3: a `b`-integral without `(M + w)⁻¹` terms

Helper level (no frozen statement). The crossed unit's `x`-integrand is `cForm` with
`a₀ = c₀ = 0` (no large-`b` logarithm, no counterterm). Writing every `(M + w)⁻¹` as
`∫_w^∞ dv/(M + v)²` and exchanging the order (all terms of one sign each), the `b`-integral over
`b > β` with `w = b h` becomes (**`crossT_cForm_eq`**), for `M, β, h > 0` and `w₀ = β h`,

`cForm(0, a₁, a₂, 0, c₁, c₂, c₃, β, h, M, log(M + β h), log(1 + M/(β h)))
  = ∫₀^∞ T(v)/(M + v)² dv`,

`T(v) = (a₁ - c₂ h)/v + (a₂ h - c₃ h²/2)/v² + c₁ log(v/w₀) + c₂/β + c₃/(2β²)` for `v > w₀`,
`T(v) = 0` below (`crossTTg`). Unlike the `(M + w)⁻¹`-representation of `SetCKCornInW`, this
form needs no integration by parts and has no boundary term. Size (**`crossT_abs_integral_le`**):
`∫₀^∞ |T|/(M + v)² ≤ |a₁| L/M² + |a₂|/(β M²) + |c₁| L/M + (|c₂|/β + |c₃|/(2β²))/M`,
`L = log(1 + M/w₀)`.

The four `v`-integrals `∫_c^∞ vᵏ⁻… dv/(M + v)²` are `crossTIoi0`, `crossTIoi1`, `crossTIoi2`,
`crossTIoiL`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- **The `v`-weight of the crossed `b`-integral** against `(M + v)⁻²`. -/
noncomputable def crossTTg (a₁ a₂ c₁ c₂ c₃ β h v : ℝ) : ℝ :=
  if β * h < v then
    (a₁ - c₂ * h) / v + (a₂ * h - c₃ * h ^ 2 / 2) / v ^ 2 + c₁ * log (v / (β * h)) +
      (c₂ / β + c₃ / (2 * β ^ 2))
  else 0

section

variable {M c : ℝ}

theorem crossT_hasDerivAt_inv {v : ℝ} (hMv : 0 < M + v) :
    HasDerivAt (fun v => 1 / (M + v)) (-(1 / (M + v) ^ 2)) v := by
  have := ((hasDerivAt_id v).const_add M).inv hMv.ne'
  simp only [id] at this
  simp only [one_div]
  convert this using 1
  ring

theorem crossT_hasDerivAt_one_div {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun v : ℝ => 1 / v) (-(1 / v ^ 2)) v := by
  simpa using crossT_hasDerivAt_inv (M := 0) (v := v) (by simpa using hv)

theorem crossT_tendsto_inv_add (M : ℝ) : Tendsto (fun v : ℝ => 1 / (M + v)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ M tendsto_id)

/-- Four integrable summands. -/
theorem crossT_integral_add4 {s : Set ℝ} {f₁ f₂ f₃ f₄ : ℝ → ℝ} (h₁ : IntegrableOn f₁ s)
    (h₂ : IntegrableOn f₂ s) (h₃ : IntegrableOn f₃ s) (h₄ : IntegrableOn f₄ s) :
    IntegrableOn (fun x => f₁ x + f₂ x + f₃ x + f₄ x) s ∧
      ∫ x in s, (f₁ x + f₂ x + f₃ x + f₄ x) =
        (∫ x in s, f₁ x) + (∫ x in s, f₂ x) + (∫ x in s, f₃ x) + ∫ x in s, f₄ x := by
  have h12 : IntegrableOn (fun x => f₁ x + f₂ x) s := h₁.add h₂
  have h123 : IntegrableOn (fun x => f₁ x + f₂ x + f₃ x) s := h12.add h₃
  refine ⟨h123.add h₄, ?_⟩
  rw [integral_add h123 h₄, integral_add h12 h₃, integral_add h₁ h₂]

/-- `∫_c^∞ dv/(M + v)² = 1/(M + c)`. -/
theorem crossTIoi0 (hM : 0 < M) (hc : 0 < c) :
    IntegrableOn (fun v => 1 / (M + v) ^ 2) (Ioi c) ∧
      ∫ v in Ioi c, 1 / (M + v) ^ 2 = 1 / (M + c) := by
  have hd : ∀ v ∈ Ici c, HasDerivAt (fun v => -(1 / (M + v))) (1 / (M + v) ^ 2) v :=
    fun v hv => by
      have hMv : 0 < M + v := by linarith [mem_Ici.1 hv]
      exact (crossT_hasDerivAt_inv hMv).neg.congr_deriv (neg_neg _)
  have hf : ∀ v ∈ Ioi c, 0 ≤ 1 / (M + v) ^ 2 := fun v _ => by positivity
  have hl : Tendsto (fun v => -(1 / (M + v))) atTop (𝓝 0) := by
    simpa using (crossT_tendsto_inv_add M).neg
  obtain ⟨hi, hv⟩ := cornIn_ioi_of_deriv hd hf hl
  exact ⟨hi, by rw [hv]; ring⟩

/-- `∫_c^∞ dv/(v (M + v)²) = log(1 + M/c)/M² - 1/(M (M + c))`. -/
theorem crossTIoi1 (hM : 0 < M) (hc : 0 < c) :
    IntegrableOn (fun v => 1 / (v * (M + v) ^ 2)) (Ioi c) ∧
      ∫ v in Ioi c, 1 / (v * (M + v) ^ 2) = log (1 + M / c) / M ^ 2 - 1 / (M * (M + c)) := by
  have hd : ∀ v ∈ Ici c, HasDerivAt
      (fun v => (log v - log (M + v)) / M ^ 2 + 1 / M * (1 / (M + v)))
      (1 / (v * (M + v) ^ 2)) v := fun v hv => by
    have hv0 : 0 < v := lt_of_lt_of_le hc hv
    have hMv : 0 < M + v := by linarith
    refine (((cornIn_hasDerivAt_logw hM hv0).div_const (M ^ 2)).add
      ((crossT_hasDerivAt_inv hMv).const_mul (1 / M))).congr_deriv ?_
    field_simp
    ring
  have hf : ∀ v ∈ Ioi c, 0 ≤ 1 / (v * (M + v) ^ 2) := fun v hv => by
    have hv0 : 0 < v := hc.trans hv
    positivity
  have hl : Tendsto (fun v => (log v - log (M + v)) / M ^ 2 + 1 / M * (1 / (M + v))) atTop
      (𝓝 0) := by
    have h := ((cornIn_tendsto_logw M hM.le).div_const (M ^ 2)).add
      ((crossT_tendsto_inv_add M).const_mul (1 / M))
    simp only [zero_div, mul_zero, add_zero] at h
    exact h
  obtain ⟨hi, hv⟩ := cornIn_ioi_of_deriv hd hf hl
  refine ⟨hi, hv.trans ?_⟩
  have e : 1 + M / c = (M + c) / c := by field_simp; ring
  rw [e, log_div (by positivity) hc.ne']
  have : M + c ≠ 0 := by positivity
  field_simp
  ring

/-- `∫_c^∞ dv/(v² (M + v)²) = 1/(M² c) - 2 log(1 + M/c)/M³ + 1/(M² (M + c))`. -/
theorem crossTIoi2 (hM : 0 < M) (hc : 0 < c) :
    IntegrableOn (fun v => 1 / (v ^ 2 * (M + v) ^ 2)) (Ioi c) ∧
      ∫ v in Ioi c, 1 / (v ^ 2 * (M + v) ^ 2) =
        1 / (M ^ 2 * c) - 2 * log (1 + M / c) / M ^ 3 + 1 / (M ^ 2 * (M + c)) := by
  have hd : ∀ v ∈ Ici c, HasDerivAt
      (fun v => -(1 / M ^ 2 * (1 / v)) - 2 * (log v - log (M + v)) / M ^ 3 -
        1 / M ^ 2 * (1 / (M + v)))
      (1 / (v ^ 2 * (M + v) ^ 2)) v := fun v hv => by
    have hv0 : 0 < v := lt_of_lt_of_le hc hv
    have hMv : 0 < M + v := by linarith
    have h1 := crossT_hasDerivAt_one_div hv0
    refine (((h1.const_mul (1 / M ^ 2)).neg.sub
      (((cornIn_hasDerivAt_logw hM hv0).const_mul 2).div_const (M ^ 3))).sub
      ((crossT_hasDerivAt_inv hMv).const_mul (1 / M ^ 2))).congr_deriv ?_
    field_simp
    ring
  have hf : ∀ v ∈ Ioi c, 0 ≤ 1 / (v ^ 2 * (M + v) ^ 2) := fun v _ => by positivity
  have hl : Tendsto (fun v => -(1 / M ^ 2 * (1 / v)) - 2 * (log v - log (M + v)) / M ^ 3 -
      1 / M ^ 2 * (1 / (M + v))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun v : ℝ => 1 / v) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h := ((h0.const_mul (1 / M ^ 2)).neg.sub
      (((cornIn_tendsto_logw M hM.le).const_mul 2).div_const (M ^ 3))).sub
      ((crossT_tendsto_inv_add M).const_mul (1 / M ^ 2))
    simp only [zero_div, mul_zero, neg_zero, sub_zero] at h
    exact h
  obtain ⟨hi, hv⟩ := cornIn_ioi_of_deriv hd hf hl
  refine ⟨hi, hv.trans ?_⟩
  have e : 1 + M / c = (M + c) / c := by field_simp; ring
  rw [e, log_div (by positivity) hc.ne']
  field_simp
  ring

/-- `∫_c^∞ log(v/c) dv/(M + v)² = log(1 + M/c)/M`. -/
theorem crossTIoiL (hM : 0 < M) (hc : 0 < c) :
    IntegrableOn (fun v => log (v / c) / (M + v) ^ 2) (Ioi c) ∧
      ∫ v in Ioi c, log (v / c) / (M + v) ^ 2 = log (1 + M / c) / M := by
  have hd : ∀ v ∈ Ici c, HasDerivAt
      (fun v => -(log (v / c) * (1 / (M + v))) + (log v - log (M + v)) / M)
      (log (v / c) / (M + v) ^ 2) v := fun v hv => by
    have hv0 : 0 < v := lt_of_lt_of_le hc hv
    have hMv : 0 < M + v := by linarith
    have hl : HasDerivAt (fun v => log (v / c)) (1 / v) v := by
      have := ((hasDerivAt_id v).div_const c).log (div_pos hv0 hc).ne'
      refine this.congr_deriv ?_
      simp only [id]
      field_simp
    refine ((hl.mul (crossT_hasDerivAt_inv hMv)).neg.add
      ((cornIn_hasDerivAt_logw hM hv0).div_const M)).congr_deriv ?_
    field_simp
    ring
  have hf : ∀ v ∈ Ioi c, 0 ≤ log (v / c) / (M + v) ^ 2 := fun v hv => by
    have hv0 : 0 < v := hc.trans hv
    have : 1 ≤ v / c := (one_le_div hc).2 (le_of_lt hv)
    exact div_nonneg (log_nonneg this) (by positivity)
  have hl : Tendsto (fun v => -(log (v / c) * (1 / (M + v))) + (log v - log (M + v)) / M)
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun v : ℝ => log v ^ 1 / (1 * v + M)) atTop (𝓝 0) :=
      tendsto_pow_log_div_mul_add_atTop 1 M 1 one_ne_zero
    have h1 := crossT_tendsto_inv_add M
    have h2 : Tendsto (fun v : ℝ => log (v / c) * (1 / (M + v))) atTop (𝓝 0) := by
      have h3 := h0.sub (h1.const_mul (log c))
      simp only [mul_zero, sub_zero] at h3
      refine h3.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with v hv
      rw [log_div hv.ne' hc.ne']
      have : M + v ≠ 0 := by positivity
      field_simp
      ring
    have h := h2.neg.add ((cornIn_tendsto_logw M hM.le).div_const M)
    simp only [zero_div, neg_zero, add_zero] at h
    exact h
  obtain ⟨hi, hv⟩ := cornIn_ioi_of_deriv hd hf hl
  refine ⟨hi, hv.trans ?_⟩
  have e : 1 + M / c = (M + c) / c := by field_simp; ring
  rw [div_self hc.ne', log_one, e, log_div (by positivity) hc.ne']
  ring

end

section

variable {a₁ a₂ c₁ c₂ c₃ β h M : ℝ}

theorem crossTTg_of_lt {v : ℝ} (hv : β * h < v) :
    crossTTg a₁ a₂ c₁ c₂ c₃ β h v =
      (a₁ - c₂ * h) / v + (a₂ * h - c₃ * h ^ 2 / 2) / v ^ 2 + c₁ * log (v / (β * h)) +
        (c₂ / β + c₃ / (2 * β ^ 2)) := by
  simp only [crossTTg, hv, ↓reduceIte]

theorem crossTTg_of_le {v : ℝ} (hv : v ≤ β * h) : crossTTg a₁ a₂ c₁ c₂ c₃ β h v = 0 := by
  simp only [crossTTg, not_lt.2 hv, ↓reduceIte]

/-- The weight against `(M + v)⁻²` beyond the threshold, as a combination of the masters. -/
theorem crossTTg_div_eq {v : ℝ} (hv : β * h < v) (hv0 : 0 < v) (hMv : 0 < M + v) :
    crossTTg a₁ a₂ c₁ c₂ c₃ β h v / (M + v) ^ 2 =
      (a₁ - c₂ * h) * (1 / (v * (M + v) ^ 2)) +
        (a₂ * h - c₃ * h ^ 2 / 2) * (1 / (v ^ 2 * (M + v) ^ 2)) +
        c₁ * (log (v / (β * h)) / (M + v) ^ 2) +
        (c₂ / β + c₃ / (2 * β ^ 2)) * (1 / (M + v) ^ 2) := by
  rw [crossTTg_of_lt hv]
  have := hv0.ne'
  have := hMv.ne'
  field_simp

/-- The weight is integrable against `(M + v)⁻²` on `(0, ∞)`. -/
theorem integrableOn_crossTTg (hM : 0 < M) (hw₀ : 0 < β * h) :
    IntegrableOn (fun v => crossTTg a₁ a₂ c₁ c₂ c₃ β h v / (M + v) ^ 2) (Ioi 0) := by
  obtain ⟨i0, -⟩ := crossTIoi0 hM hw₀
  obtain ⟨i1, -⟩ := crossTIoi1 hM hw₀
  obtain ⟨i2, -⟩ := crossTIoi2 hM hw₀
  obtain ⟨iL, -⟩ := crossTIoiL hM hw₀
  rw [← Ioc_union_Ioi_eq_Ioi hw₀.le]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_zero).congr_fun (fun v hv => ?_) measurableSet_Ioc
    simp [crossTTg_of_le hv.2]
  · refine IntegrableOn.congr_fun ((((i1.const_mul (a₁ - c₂ * h)).add
      (i2.const_mul (a₂ * h - c₃ * h ^ 2 / 2))).add (iL.const_mul c₁)).add
      (i0.const_mul (c₂ / β + c₃ / (2 * β ^ 2)))) (fun v hv => ?_) measurableSet_Ioi
    have hv0 : 0 < v := hw₀.trans hv
    simp only [Pi.add_apply]
    rw [crossTTg_div_eq hv hv0 (by positivity)]

/-- **The `(M + v)⁻²`-representation of the crossed `b`-integral.** -/
theorem crossT_cForm_eq (hM : 0 < M) (hβ : 0 < β) (hh : 0 < h) :
    cForm 0 a₁ a₂ 0 c₁ c₂ c₃ β h M (log (M + β * h)) (log (1 + M / (β * h))) =
      ∫ v in Ioi 0, crossTTg a₁ a₂ c₁ c₂ c₃ β h v / (M + v) ^ 2 := by
  have hw₀ : 0 < β * h := mul_pos hβ hh
  obtain ⟨i0, v0⟩ := crossTIoi0 hM hw₀
  obtain ⟨i1, v1⟩ := crossTIoi1 hM hw₀
  obtain ⟨i2, v2⟩ := crossTIoi2 hM hw₀
  obtain ⟨iL, vL⟩ := crossTIoiL hM hw₀
  have hint := integrableOn_crossTTg (a₁ := a₁) (a₂ := a₂) (c₁ := c₁) (c₂ := c₂) (c₃ := c₃)
    hM hw₀
  rw [← Ioc_union_Ioi_eq_Ioi hw₀.le] at hint ⊢
  rw [setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set subset_union_left) (hint.mono_set subset_union_right)]
  have e0 : ∫ v in Ioc 0 (β * h), crossTTg a₁ a₂ c₁ c₂ c₃ β h v / (M + v) ^ 2 = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (0 : ℝ)) fun v hv => by
      simp [crossTTg_of_le hv.2]]
    simp
  have e1 : ∫ v in Ioi (β * h), crossTTg a₁ a₂ c₁ c₂ c₃ β h v / (M + v) ^ 2 =
      (a₁ - c₂ * h) * (log (1 + M / (β * h)) / M ^ 2 - 1 / (M * (M + β * h))) +
        (a₂ * h - c₃ * h ^ 2 / 2) * (1 / (M ^ 2 * (β * h)) -
          2 * log (1 + M / (β * h)) / M ^ 3 + 1 / (M ^ 2 * (M + β * h))) +
        c₁ * (log (1 + M / (β * h)) / M) + (c₂ / β + c₃ / (2 * β ^ 2)) * (1 / (M + β * h)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun v hv =>
      crossTTg_div_eq hv (hw₀.trans hv) (by linarith [hw₀.trans (mem_Ioi.1 hv)]),
      (crossT_integral_add4 (i1.const_mul (a₁ - c₂ * h)) (i2.const_mul (a₂ * h - c₃ * h ^ 2 / 2))
        (iL.const_mul c₁) (i0.const_mul (c₂ / β + c₃ / (2 * β ^ 2)))).2,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, v0, v1, v2,
      vL]
  rw [e0, e1, zero_add]
  unfold cForm
  have := hM.ne'
  have := hh.ne'
  have := hβ.ne'
  have : M + β * h ≠ 0 := by positivity
  field_simp
  ring

/-- **The size of the weight**: `∫₀^∞ |T|/(M + v)² ≤ |a₁| L/M² + |a₂|/(β M²) + |c₁| L/M
  + (|c₂|/β + |c₃|/(2β²))/M`, `L = log(1 + M/w₀)`. -/
theorem crossT_abs_integral_le (hM : 0 < M) (hβ : 0 < β) (hh : 0 < h) :
    ∫ v in Ioi 0, |crossTTg a₁ a₂ c₁ c₂ c₃ β h v / (M + v) ^ 2| ≤
      |a₁| * (log (1 + M / (β * h)) / M ^ 2) + |a₂| / (β * M ^ 2) +
        |c₁| * (log (1 + M / (β * h)) / M) + (|c₂| / β + |c₃| / (2 * β ^ 2)) / M := by
  have hw₀ : 0 < β * h := mul_pos hβ hh
  obtain ⟨i0, v0⟩ := crossTIoi0 hM hw₀
  obtain ⟨i1, v1⟩ := crossTIoi1 hM hw₀
  obtain ⟨i2, v2⟩ := crossTIoi2 hM hw₀
  obtain ⟨iL, vL⟩ := crossTIoiL hM hw₀
  have hI : IntegrableOn (fun v => |crossTTg a₁ a₂ c₁ c₂ c₃ β h v / (M + v) ^ 2|) (Ioi 0) :=
    (integrableOn_crossTTg hM hw₀).abs
  rw [← Ioc_union_Ioi_eq_Ioi hw₀.le] at hI ⊢
  rw [setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hI.mono_set subset_union_left) (hI.mono_set subset_union_right)]
  have e0 : ∫ v in Ioc 0 (β * h), |crossTTg a₁ a₂ c₁ c₂ c₃ β h v / (M + v) ^ 2| = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (0 : ℝ)) fun v hv => by
      simp [crossTTg_of_le hv.2]]
    simp
  -- the pointwise bound beyond the threshold
  obtain ⟨jS, vS⟩ := crossT_integral_add4 (i1.const_mul |a₁|) (i2.const_mul (|a₂| * h))
    (iL.const_mul |c₁|) (i0.const_mul (|c₂| / β + |c₃| / (2 * β ^ 2)))
  have hpt : ∀ v ∈ Ioi (β * h), |crossTTg a₁ a₂ c₁ c₂ c₃ β h v / (M + v) ^ 2| ≤
      |a₁| * (1 / (v * (M + v) ^ 2)) + |a₂| * h * (1 / (v ^ 2 * (M + v) ^ 2)) +
        |c₁| * (log (v / (β * h)) / (M + v) ^ 2) +
        (|c₂| / β + |c₃| / (2 * β ^ 2)) * (1 / (M + v) ^ 2) := by
    intro v hv
    have hv0 : 0 < v := hw₀.trans hv
    have hMv : 0 < M + v := by linarith
    have hq : 0 ≤ h / v := (div_pos hh hv0).le
    have hq1 : β * (h / v) ≤ 1 := by
      rw [mul_div_assoc', div_le_one hv0]; exact hv.le
    rw [crossTTg_of_lt hv]
    have e : (a₁ - c₂ * h) / v + (a₂ * h - c₃ * h ^ 2 / 2) / v ^ 2 + c₁ * log (v / (β * h)) +
        (c₂ / β + c₃ / (2 * β ^ 2)) =
        a₁ / v + a₂ * h / v ^ 2 + c₁ * log (v / (β * h)) + c₂ * ((1 - β * (h / v)) / β) +
          c₃ * ((1 - (β * (h / v)) ^ 2) / (2 * β ^ 2)) := by
      have := hv0.ne'
      have := hβ.ne'
      field_simp
      ring
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (M + v) ^ 2)]
    have hL : 0 ≤ log (v / (β * h)) := log_nonneg ((one_le_div hw₀).2 hv.le)
    have b2 : |(1 - β * (h / v)) / β| ≤ 1 / β := by
      rw [abs_div, abs_of_pos hβ, abs_of_nonneg (by linarith)]
      exact div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hβ.le hq]) hβ.le
    have b3 : |(1 - (β * (h / v)) ^ 2) / (2 * β ^ 2)| ≤ 1 / (2 * β ^ 2) := by
      have h0 : 0 ≤ β * (h / v) := mul_nonneg hβ.le hq
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * β ^ 2),
        abs_of_nonneg (by nlinarith)]
      exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    have key : |a₁ / v + a₂ * h / v ^ 2 + c₁ * log (v / (β * h)) +
        c₂ * ((1 - β * (h / v)) / β) + c₃ * ((1 - (β * (h / v)) ^ 2) / (2 * β ^ 2))| ≤
        |a₁| / v + |a₂| * h / v ^ 2 + |c₁| * log (v / (β * h)) + |c₂| / β +
          |c₃| / (2 * β ^ 2) := by
      have t1 : |a₁ / v| = |a₁| / v := by rw [abs_div, abs_of_pos hv0]
      have t2 : |a₂ * h / v ^ 2| = |a₂| * h / v ^ 2 := by
        rw [abs_div, abs_mul, abs_of_pos hh, abs_of_pos (by positivity : (0 : ℝ) < v ^ 2)]
      have t3 : |c₁ * log (v / (β * h))| = |c₁| * log (v / (β * h)) := by
        rw [abs_mul, abs_of_nonneg hL]
      have t4 : |c₂ * ((1 - β * (h / v)) / β)| ≤ |c₂| / β := by
        rw [abs_mul, div_eq_mul_one_div |c₂|]
        exact mul_le_mul_of_nonneg_left b2 (abs_nonneg _)
      have t5 : |c₃ * ((1 - (β * (h / v)) ^ 2) / (2 * β ^ 2))| ≤ |c₃| / (2 * β ^ 2) := by
        rw [abs_mul, div_eq_mul_one_div |c₃|]
        exact mul_le_mul_of_nonneg_left b3 (abs_nonneg _)
      calc _ ≤ |a₁ / v| + |a₂ * h / v ^ 2| + |c₁ * log (v / (β * h))| +
            |c₂ * ((1 - β * (h / v)) / β)| + |c₃ * ((1 - (β * (h / v)) ^ 2) / (2 * β ^ 2))| := by
            refine (abs_add_le _ _).trans ?_
            gcongr
            refine (abs_add_le _ _).trans ?_
            gcongr
            exact abs_add_three _ _ _
        _ ≤ _ := by rw [t1, t2, t3]; linarith
    calc _ ≤ (|a₁| / v + |a₂| * h / v ^ 2 + |c₁| * log (v / (β * h)) + |c₂| / β +
          |c₃| / (2 * β ^ 2)) / (M + v) ^ 2 :=
          div_le_div_of_nonneg_right key (by positivity)
      _ = _ := by
          have := hv0.ne'
          have := hMv.ne'
          field_simp
          ring
  have hb : ∫ v in Ioi (β * h), |crossTTg a₁ a₂ c₁ c₂ c₃ β h v / (M + v) ^ 2| ≤
      |a₁| * (log (1 + M / (β * h)) / M ^ 2 - 1 / (M * (M + β * h))) +
        |a₂| * h * (1 / (M ^ 2 * (β * h)) - 2 * log (1 + M / (β * h)) / M ^ 3 +
          1 / (M ^ 2 * (M + β * h))) + |c₁| * (log (1 + M / (β * h)) / M) +
        (|c₂| / β + |c₃| / (2 * β ^ 2)) * (1 / (M + β * h)) := by
    refine (setIntegral_mono_on (hI.mono_set subset_union_right) jS measurableSet_Ioi hpt).trans
      (le_of_eq ?_)
    rw [vS, integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, v0,
      v1, v2, vL]
  -- the masters are bounded by their leading terms
  have hL0 : 0 ≤ log (1 + M / (β * h)) := log_nonneg (by
    have : 0 ≤ M / (β * h) := by positivity
    linarith)
  have m1 : 0 ≤ 1 / (M * (M + β * h)) := by positivity
  have m2 : 1 / (M ^ 2 * (β * h)) - 2 * log (1 + M / (β * h)) / M ^ 3 +
      1 / (M ^ 2 * (M + β * h)) ≤ 1 / (M ^ 2 * (β * h)) := by
    -- `∫_c^∞ dv/(v²(M+v)²) ≤ ∫_c^∞ dv/(M² v²)`
    have hle : ∫ v in Ioi (β * h), 1 / (v ^ 2 * (M + v) ^ 2) ≤
        ∫ v in Ioi (β * h), (1 / M ^ 2) * (1 / v ^ 2) := by
      have hi : IntegrableOn (fun v : ℝ => 1 / v ^ 2) (Ioi (β * h)) := by
        have := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hw₀
        refine this.congr_fun (fun v hv => ?_) measurableSet_Ioi
        have hv0 : 0 < v := hw₀.trans hv
        change v ^ (-2 : ℝ) = 1 / v ^ 2
        rw [rpow_neg hv0.le, rpow_two, one_div]
      refine setIntegral_mono_on i2 (hi.const_mul _) measurableSet_Ioi fun v hv => ?_
      have hv0 : 0 < v := hw₀.trans hv
      rw [one_div_mul_one_div]
      refine one_div_le_one_div_of_le (by positivity) ?_
      have : M ^ 2 ≤ (M + v) ^ 2 := by nlinarith
      nlinarith [sq_nonneg v]
    have hv : ∫ v in Ioi (β * h), (1 / M ^ 2) * (1 / v ^ 2) = 1 / (M ^ 2 * (β * h)) := by
      rw [integral_const_mul]
      have := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hw₀
      have e : ∫ v in Ioi (β * h), 1 / v ^ 2 = ∫ v in Ioi (β * h), v ^ (-2 : ℝ) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
        have hv0 : 0 < v := hw₀.trans hv
        rw [rpow_neg hv0.le, rpow_two, one_div]
      rw [e, this, show (-2 : ℝ) + 1 = -1 by norm_num, rpow_neg_one]
      field_simp
    rw [← v2]
    linarith
  have hab : 0 ≤ |a₂| * h := mul_nonneg (abs_nonneg _) hh.le
  have m0 : 1 / (M + β * h) ≤ 1 / M := one_div_le_one_div_of_le hM (by linarith)
  have hc0 : 0 ≤ |c₂| / β + |c₃| / (2 * β ^ 2) := by positivity
  rw [e0, zero_add]
  refine hb.trans ?_
  have f1 : |a₁| * (log (1 + M / (β * h)) / M ^ 2 - 1 / (M * (M + β * h))) ≤
      |a₁| * (log (1 + M / (β * h)) / M ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have f2 : |a₂| * h * (1 / (M ^ 2 * (β * h)) - 2 * log (1 + M / (β * h)) / M ^ 3 +
      1 / (M ^ 2 * (M + β * h))) ≤ |a₂| / (β * M ^ 2) := by
    refine (mul_le_mul_of_nonneg_left m2 hab).trans (le_of_eq ?_)
    field_simp
  have f0 : (|c₂| / β + |c₃| / (2 * β ^ 2)) * (1 / (M + β * h)) ≤
      (|c₂| / β + |c₃| / (2 * β ^ 2)) / M := by
    rw [div_eq_mul_one_div _ M]
    exact mul_le_mul_of_nonneg_left m0 hc0
  linarith

end

end QED.ChainProof.SetCK

end
