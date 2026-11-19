/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCLimitCMasters
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G2: the corner `b`-integral as a Stieltjes transform in `M`

Helper level (no frozen statement). Group G2 of the set (c) kernel plan is the corner unit `C`
with the photon of mass² `t` inside the vertex subgraph, `C(t, 0)`. Its `x`-integrand is
`cornerGm 0 (√t) y₃ y₄ x = cForm(…, β, h, M, log(M + β h), log(1 + M/(β h)))`, the closed form
of a `b`-integral over `b > β` whose `M`-dependence is through `(M + b h)⁻¹` and `(M + b h)⁻²`
only. Substituting `w = b h` and integrating the `(M + w)⁻²` terms by parts in `w` gives, for
arbitrary coefficients and `M, β, h > 0`, with `w₀ = β h` (**`cForm_add_log_eq`**):

`cForm + (c₀/h) log M = ∫₀^∞ K(w)/(M + w) dw + δ(w₀)/(M + w₀)`,

* `K(w) = c₁/w + (c₂ h - a₁)/w² + (c₃ h² - 2 a₂ h)/w³` for `w > w₀` (`cornInOm`) and
  `K(w) = -c₀/h` for `w ≤ w₀` (`cornInK`);
* `δ(w₀) = a₀/h + a₁/w₀ + a₂ h/w₀²` (`cornInDelta`), the boundary term of the integration by parts.

The `log M` on the left is the counterterm's share (it cancels the large-`b` logarithm).
The three `w`-integrals `∫_c^∞ dw/(wᵏ(M + w))`, `k = 1, 2, 3`, are `cornInIoi1`–`cornInIoi3`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- A nonnegative function with an antiderivative tending to `0` at `∞` is integrable on
`(c, ∞)` with integral `-F(c)`. -/
theorem cornIn_ioi_of_deriv {F f : ℝ → ℝ} {c : ℝ} (hd : ∀ w ∈ Ici c, HasDerivAt F (f w) w)
    (hf : ∀ w ∈ Ioi c, 0 ≤ f w) (hl : Tendsto F atTop (𝓝 0)) :
    IntegrableOn f (Ioi c) ∧ ∫ w in Ioi c, f w = -F c := by
  have hi := integrableOn_Ioi_deriv_of_nonneg' hd hf hl
  refine ⟨hi, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd hi hl]
  ring

theorem cornIn_tendsto_logw (M : ℝ) (hM : 0 ≤ M) :
    Tendsto (fun w : ℝ => log w - log (M + w)) atTop (𝓝 0) := by
  have := tendsto_log_sub_log_atTop (M := M) (h := 1) hM one_pos
  simpa using this

theorem cornIn_tendsto_inv_pow (k : ℕ) (hk : k ≠ 0) :
    Tendsto (fun w : ℝ => 1 / w ^ k) atTop (𝓝 0) := by
  have : Tendsto (fun w : ℝ => w ^ k) atTop atTop := tendsto_pow_atTop hk
  exact tendsto_const_nhds.div_atTop this

theorem cornIn_hasDerivAt_logw {M w : ℝ} (hM : 0 < M) (hw : 0 < w) :
    HasDerivAt (fun w => log w - log (M + w)) (1 / w - 1 / (M + w)) w := by
  have h1 : HasDerivAt (fun w => M + w) 1 w := (hasDerivAt_id w).const_add M
  have := (Real.hasDerivAt_log hw.ne').sub (h1.log (by positivity : (0 : ℝ) < M + w).ne')
  exact this.congr_deriv (by simp [one_div])

/-- `∫_c^∞ dw/(w(M + w)) = log(1 + M/c)/M`. -/
theorem cornInIoi1 {M c : ℝ} (hM : 0 < M) (hc : 0 < c) :
    IntegrableOn (fun w => 1 / (w * (M + w))) (Ioi c) ∧
      ∫ w in Ioi c, 1 / (w * (M + w)) = log (1 + M / c) / M := by
  have hd : ∀ w ∈ Ici c, HasDerivAt (fun w => (log w - log (M + w)) / M)
      (1 / (w * (M + w))) w := fun w hw => by
    have hw0 : 0 < w := lt_of_lt_of_le hc hw
    refine ((cornIn_hasDerivAt_logw hM hw0).div_const M).congr_deriv ?_
    have : M + w ≠ 0 := by positivity
    field_simp
    ring
  have hf : ∀ w ∈ Ioi c, 0 ≤ 1 / (w * (M + w)) := fun w hw => by
    have hw0 : 0 < w := hc.trans hw
    positivity
  have hl : Tendsto (fun w => (log w - log (M + w)) / M) atTop (𝓝 0) := by
    simpa using (cornIn_tendsto_logw M hM.le).div_const M
  obtain ⟨hi, hv⟩ := cornIn_ioi_of_deriv hd hf hl
  refine ⟨hi, hv.trans ?_⟩
  have e : 1 + M / c = (M + c) / c := by field_simp; ring
  rw [e, log_div (by positivity) hc.ne']
  ring

/-- `∫_c^∞ dw/(w²(M + w)) = 1/(M c) - log(1 + M/c)/M²`. -/
theorem cornInIoi2 {M c : ℝ} (hM : 0 < M) (hc : 0 < c) :
    IntegrableOn (fun w => 1 / (w ^ 2 * (M + w))) (Ioi c) ∧
      ∫ w in Ioi c, 1 / (w ^ 2 * (M + w)) = 1 / (M * c) - log (1 + M / c) / M ^ 2 := by
  have hd : ∀ w ∈ Ici c, HasDerivAt (fun w => -(1 / (M * w)) - (log w - log (M + w)) / M ^ 2)
      (1 / (w ^ 2 * (M + w))) w := fun w hw => by
    have hw0 : 0 < w := lt_of_lt_of_le hc hw
    have h1 : HasDerivAt (fun w => 1 / (M * w)) (-(1 / (M * w ^ 2))) w := by
      have := ((hasDerivAt_id w).const_mul M).inv (mul_ne_zero hM.ne' hw0.ne')
      refine (this.congr_deriv ?_).congr_of_eventuallyEq
        (Eventually.of_forall fun w => by simp [one_div])
      simp only [id]
      field_simp
    refine (h1.neg.sub ((cornIn_hasDerivAt_logw hM hw0).div_const (M ^ 2))).congr_deriv ?_
    have : M + w ≠ 0 := by positivity
    field_simp
    ring
  have hf : ∀ w ∈ Ioi c, 0 ≤ 1 / (w ^ 2 * (M + w)) := fun w hw => by
    have hw0 : 0 < w := hc.trans hw
    positivity
  have hl : Tendsto (fun w => -(1 / (M * w)) - (log w - log (M + w)) / M ^ 2) atTop (𝓝 0) := by
    have h0 : Tendsto (fun w : ℝ => 1 / (M * w)) atTop (𝓝 0) := tendsto_one_div_mul_atTop hM
    simpa using h0.neg.sub ((cornIn_tendsto_logw M hM.le).div_const (M ^ 2))
  obtain ⟨hi, hv⟩ := cornIn_ioi_of_deriv hd hf hl
  refine ⟨hi, hv.trans ?_⟩
  have e : 1 + M / c = (M + c) / c := by field_simp; ring
  rw [e, log_div (by positivity) hc.ne']
  ring

/-- `∫_c^∞ dw/(w³(M + w)) = 1/(2 M c²) - 1/(M² c) + log(1 + M/c)/M³`. -/
theorem cornInIoi3 {M c : ℝ} (hM : 0 < M) (hc : 0 < c) :
    IntegrableOn (fun w => 1 / (w ^ 3 * (M + w))) (Ioi c) ∧
      ∫ w in Ioi c, 1 / (w ^ 3 * (M + w)) =
        1 / (2 * M * c ^ 2) - 1 / (M ^ 2 * c) + log (1 + M / c) / M ^ 3 := by
  have hd : ∀ w ∈ Ici c, HasDerivAt
      (fun w => -(1 / (2 * M * w ^ 2)) + 1 / (M ^ 2 * w) + (log w - log (M + w)) / M ^ 3)
      (1 / (w ^ 3 * (M + w))) w := fun w hw => by
    have hw0 : 0 < w := lt_of_lt_of_le hc hw
    have h1 : HasDerivAt (fun w => 1 / (2 * M * w ^ 2)) (-(1 / (M * w ^ 3))) w := by
      have := ((hasDerivAt_pow 2 w).const_mul (2 * M)).inv
        (mul_ne_zero (by positivity) (pow_ne_zero 2 hw0.ne'))
      refine (this.congr_deriv ?_).congr_of_eventuallyEq
        (Eventually.of_forall fun w => by simp [one_div])
      field_simp
      ring
    have h2 : HasDerivAt (fun w => 1 / (M ^ 2 * w)) (-(1 / (M ^ 2 * w ^ 2))) w := by
      have := ((hasDerivAt_id w).const_mul (M ^ 2)).inv
        (mul_ne_zero (pow_ne_zero 2 hM.ne') hw0.ne')
      refine (this.congr_deriv ?_).congr_of_eventuallyEq
        (Eventually.of_forall fun w => by simp [one_div])
      simp only [id]
      field_simp
    refine ((h1.neg.add h2).add ((cornIn_hasDerivAt_logw hM hw0).div_const (M ^ 3))).congr_deriv
      ?_
    have : M + w ≠ 0 := by positivity
    field_simp
    ring
  have hf : ∀ w ∈ Ioi c, 0 ≤ 1 / (w ^ 3 * (M + w)) := fun w hw => by
    have hw0 : 0 < w := hc.trans hw
    positivity
  have hl : Tendsto (fun w => -(1 / (2 * M * w ^ 2)) + 1 / (M ^ 2 * w) +
      (log w - log (M + w)) / M ^ 3) atTop (𝓝 0) := by
    have h0 : Tendsto (fun w : ℝ => 1 / (2 * M * w ^ 2)) atTop (𝓝 0) := by
      exact tendsto_const_nhds.div_atTop
        ((tendsto_pow_atTop two_ne_zero).const_mul_atTop (by positivity))
    have h1 : Tendsto (fun w : ℝ => 1 / (M ^ 2 * w)) atTop (𝓝 0) :=
      tendsto_one_div_mul_atTop (by positivity)
    simpa using (h0.neg.add h1).add ((cornIn_tendsto_logw M hM.le).div_const (M ^ 3))
  obtain ⟨hi, hv⟩ := cornIn_ioi_of_deriv hd hf hl
  refine ⟨hi, hv.trans ?_⟩
  have e : 1 + M / c = (M + c) / c := by field_simp; ring
  rw [e, log_div (by positivity) hc.ne']
  ring

/-- `K(w)` beyond the threshold: `c₁/w + (c₂ h - a₁)/w² + (c₃ h² - 2 a₂ h)/w³`. -/
noncomputable def cornInOm (a₁ a₂ c₁ c₂ c₃ h w : ℝ) : ℝ :=
  c₁ / w + (c₂ * h - a₁) / w ^ 2 + (c₃ * h ^ 2 - 2 * a₂ * h) / w ^ 3

/-- **The `w`-weight** of the corner `b`-integral: `cornInOm` for `w > w₀`, `-c₀/h` below. -/
noncomputable def cornInK (a₁ a₂ c₀ c₁ c₂ c₃ h w₀ w : ℝ) : ℝ :=
  if w₀ < w then cornInOm a₁ a₂ c₁ c₂ c₃ h w else -(c₀ / h)

/-- The boundary term `δ(w) = a₀/h + a₁/w + a₂ h/w²` of the integration by parts. -/
noncomputable def cornInDelta (a₀ a₁ a₂ h w : ℝ) : ℝ := a₀ / h + a₁ / w + a₂ * h / w ^ 2

theorem cornInOm_div_eq {a₁ a₂ c₁ c₂ c₃ h M w : ℝ} (hw : 0 < w) (hMw : 0 < M + w) :
    cornInOm a₁ a₂ c₁ c₂ c₃ h w / (M + w) = c₁ * (1 / (w * (M + w))) +
      (c₂ * h - a₁) * (1 / (w ^ 2 * (M + w))) + (c₃ * h ^ 2 - 2 * a₂ * h) * (1 / (w ^ 3 *
        (M + w))) := by
  unfold cornInOm
  have := hw.ne'
  have := hMw.ne'
  field_simp

/-- `∫_0^c dw/(M + w) = log(M + c) - log M`. -/
theorem cornIn_integral_Ioc {M c : ℝ} (hM : 0 < M) (hc : 0 < c) :
    IntegrableOn (fun w => 1 / (M + w)) (Ioc 0 c) ∧
      ∫ w in Ioc 0 c, 1 / (M + w) = log (M + c) - log M := by
  have hcont : ContinuousOn (fun w : ℝ => 1 / (M + w)) (Icc 0 c) := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun w hw => ?_
    have : 0 ≤ w := hw.1
    positivity
  refine ⟨(hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self, ?_⟩
  rw [← intervalIntegral.integral_of_le hc.le]
  have hd : ∀ w ∈ uIcc 0 c, HasDerivAt (fun w => log (M + w)) (1 / (M + w)) w := by
    intro w hw
    rw [uIcc_of_le hc.le] at hw
    have : 0 < M + w := by linarith [hw.1]
    simpa [one_div] using ((hasDerivAt_id w).const_add M).log this.ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((hcont.mono (by rw [uIcc_of_le hc.le])).intervalIntegrable)]
  simp

/-- **The `w`-representation of `cForm`**: integrability of the kernel on `(0, ∞)`. -/
theorem integrableOn_cornInK {a₁ a₂ c₀ c₁ c₂ c₃ h M w₀ : ℝ} (hM : 0 < M) (hw₀ : 0 < w₀) :
    IntegrableOn (fun w => cornInK a₁ a₂ c₀ c₁ c₂ c₃ h w₀ w / (M + w)) (Ioi 0) := by
  obtain ⟨i1, -⟩ := cornInIoi1 hM hw₀
  obtain ⟨i2, -⟩ := cornInIoi2 hM hw₀
  obtain ⟨i3, -⟩ := cornInIoi3 hM hw₀
  obtain ⟨i0, -⟩ := cornIn_integral_Ioc hM hw₀
  rw [← Ioc_union_Ioi_eq_Ioi hw₀.le]
  refine IntegrableOn.union ?_ ?_
  · refine IntegrableOn.congr_fun (i0.const_mul (-(c₀ / h))) (fun w hw => ?_) measurableSet_Ioc
    simp only [cornInK, show ¬w₀ < w from not_lt.2 hw.2, ↓reduceIte]
    ring
  · refine IntegrableOn.congr_fun (((i1.const_mul c₁).add (i2.const_mul (c₂ * h - a₁))).add
      (i3.const_mul (c₃ * h ^ 2 - 2 * a₂ * h))) (fun w hw => ?_) measurableSet_Ioi
    have hw' : 0 < w := hw₀.trans hw
    simp only [cornInK, show w₀ < w from hw, ↓reduceIte, Pi.add_apply]
    rw [cornInOm_div_eq hw' (by positivity)]

/-- **The `w`-representation of `cForm`** (integration by parts of the `(M + w)⁻²` terms). -/
theorem cForm_add_log_eq {a₀ a₁ a₂ c₀ c₁ c₂ c₃ β h M : ℝ} (hM : 0 < M) (hβ : 0 < β)
    (hh : 0 < h) :
    cForm a₀ a₁ a₂ c₀ c₁ c₂ c₃ β h M (log (M + β * h)) (log (1 + M / (β * h))) +
        c₀ / h * log M =
      (∫ w in Ioi 0, cornInK a₁ a₂ c₀ c₁ c₂ c₃ h (β * h) w / (M + w)) +
        cornInDelta a₀ a₁ a₂ h (β * h) / (M + β * h) := by
  have hw₀ : 0 < β * h := mul_pos hβ hh
  set w₀ := β * h with hw₀def
  obtain ⟨i1, v1⟩ := cornInIoi1 hM hw₀
  obtain ⟨i2, v2⟩ := cornInIoi2 hM hw₀
  obtain ⟨i3, v3⟩ := cornInIoi3 hM hw₀
  obtain ⟨i0, v0⟩ := cornIn_integral_Ioc hM hw₀
  have hint := integrableOn_cornInK (a₁ := a₁) (a₂ := a₂) (c₀ := c₀) (c₁ := c₁) (c₂ := c₂)
    (c₃ := c₃) (h := h) hM hw₀
  rw [← Ioc_union_Ioi_eq_Ioi hw₀.le] at hint ⊢
  rw [setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set subset_union_left) (hint.mono_set subset_union_right)]
  have e0 : ∫ w in Ioc 0 w₀, cornInK a₁ a₂ c₀ c₁ c₂ c₃ h w₀ w / (M + w) =
      -(c₀ / h) * (log (M + w₀) - log M) := by
    rw [← v0, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun w hw => ?_
    simp only [cornInK, show ¬w₀ < w from not_lt.2 hw.2, ↓reduceIte]
    ring
  have e1 : ∫ w in Ioi w₀, cornInK a₁ a₂ c₀ c₁ c₂ c₃ h w₀ w / (M + w) =
      c₁ * (log (1 + M / w₀) / M) + (c₂ * h - a₁) * (1 / (M * w₀) - log (1 + M / w₀) / M ^ 2) +
        (c₃ * h ^ 2 - 2 * a₂ * h) *
          (1 / (2 * M * w₀ ^ 2) - 1 / (M ^ 2 * w₀) + log (1 + M / w₀) / M ^ 3) := by
    have ec : ∫ w in Ioi w₀, cornInK a₁ a₂ c₀ c₁ c₂ c₃ h w₀ w / (M + w) =
        ∫ w in Ioi w₀, (c₁ * (1 / (w * (M + w))) + (c₂ * h - a₁) * (1 / (w ^ 2 * (M + w))) +
          (c₃ * h ^ 2 - 2 * a₂ * h) * (1 / (w ^ 3 * (M + w)))) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
      have hw' : 0 < w := hw₀.trans hw
      simp only [cornInK, show w₀ < w from hw, ↓reduceIte]
      rw [cornInOm_div_eq hw' (by positivity)]
    have j1 : IntegrableOn (fun w => c₁ * (1 / (w * (M + w)))) (Ioi w₀) := i1.const_mul _
    have j2 : IntegrableOn (fun w => (c₂ * h - a₁) * (1 / (w ^ 2 * (M + w)))) (Ioi w₀) :=
      i2.const_mul _
    have j3 : IntegrableOn (fun w => (c₃ * h ^ 2 - 2 * a₂ * h) * (1 / (w ^ 3 * (M + w))))
      (Ioi w₀) := i3.const_mul _
    have j12 : IntegrableOn (fun w => c₁ * (1 / (w * (M + w))) +
        (c₂ * h - a₁) * (1 / (w ^ 2 * (M + w)))) (Ioi w₀) := j1.add j2
    rw [ec, integral_add j12 j3, integral_add j1 j2, integral_const_mul, integral_const_mul,
      integral_const_mul, v1, v2, v3]
  rw [e0, e1]
  unfold cForm cornInDelta
  have := hM.ne'
  have := hh.ne'
  have := hβ.ne'
  have : M + w₀ ≠ 0 := by positivity
  rw [hw₀def]
  field_simp
  ring

end QED.ChainProof.SetCK

end
