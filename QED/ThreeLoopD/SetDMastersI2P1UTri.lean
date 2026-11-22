/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI2P1UZ
public import QED.ThreeLoopD.SetDMastersI2P1USub

/-!
# Set (d), master `I₂`: the dilogarithmic part of `Θ` on the Feynman-parameter triangle

Each of the three dilogarithmic terms of the `y₄`-primitive `Θ`
(`QED.ThreeLoopD.i2P1UTheta`) is, in two of the Feynman parameters `(u, v)`,
`T(u, v) = (((log (u (1 - u)) + log (v (1 - v)))² - log² (u v (1 - u - v))) / 2
  + Li₂ (u v / ((1 - u)(1 - v)))) / (u v)`.
With `r = u v / ((1 - u)(1 - v))`, `s = u / (1 - v)`, `t = v / (1 - u)` (all in `(0, 1)` on the
triangle) and `h(s) = -log s - 2 log (1 - s) ≥ 0`, `T = G₊ - G₋`, where

* `G₊ = (Li₂ r + 7/2 log² (1 - r)) / (u v) ≥ 0`,
* `G₋ = -log (1 - r) (h(s) + h(t)) / (u v) ≥ 0`.

Under `u = s (1 - t) / (1 - s t)`, `v = t (1 - s) / (1 - s t)` one has `r = s t`, and the
Jacobian turns `G₊`, `G₋` into functions of `z = s t` times `1` and `h(s) + h(t)`, so by
`QED.ThreeLoopD.i2P1US_sq_z` and `QED.ThreeLoopD.SetDMastersI2P1UZ`

* `∫_triangle G₊ = 7 π⁴ / 60`, `∫_triangle G₋ = 13 π⁴ / 60`.

The dilogarithm is clamped to `[0, 1]` in `G₊` (`QED.ThreeLoopD.i2P1ULi`) to make it measurable;
the clamp is the identity on the triangle.

## Main results

* `QED.ThreeLoopD.i2P1UT_eq`: `T = G₊ - G₋` on the triangle.
* `QED.ThreeLoopD.i2P1UTri_plus`, `QED.ThreeLoopD.i2P1UTri_minus`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology QED.Polylog Function
open scoped ENNReal

namespace QED.ThreeLoopD

/-- The dilogarithm clamped to `[0, 1]`. -/
noncomputable def i2P1ULi (x : ℝ) : ℝ := Li₂ (max 0 (min x 1))

theorem continuous_i2P1ULi : Continuous i2P1ULi :=
  continuousOn_Li₂.comp_continuous (by fun_prop) fun x =>
    ⟨by linarith [le_max_left 0 (min x 1)], max_le zero_le_one (min_le_right x 1)⟩

@[fun_prop]
theorem measurable_i2P1ULi : Measurable i2P1ULi := continuous_i2P1ULi.measurable

theorem i2P1ULi_eq {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : i2P1ULi x = Li₂ x := by
  rw [i2P1ULi, min_eq_left h1, max_eq_right h0]

/-- `r = u v / ((1 - u)(1 - v))`. -/
noncomputable def i2P1Ur (u v : ℝ) : ℝ := u * v / ((1 - u) * (1 - v))

/-- `s = u / (1 - v)`. -/
noncomputable def i2P1Us (u v : ℝ) : ℝ := u / (1 - v)

/-- `h(s) = -log s - 2 log (1 - s)`. -/
noncomputable def i2P1Uh (s : ℝ) : ℝ := -log s - 2 * log (1 - s)

/-- `T(u, v)`, one dilogarithmic term of `Θ`. -/
noncomputable def i2P1UT (u v : ℝ) : ℝ :=
  (((log (u * (1 - u)) + log (v * (1 - v))) ^ 2 - log (u * v * (1 - u - v)) ^ 2) / 2 +
    Li₂ (u * v / ((1 - u) * (1 - v)))) / (u * v)

/-- `G₊ = (Li₂ r + 7/2 log² (1 - r)) / (u v)`. -/
noncomputable def i2P1UGp (u v : ℝ) : ℝ :=
  (i2P1ULi (i2P1Ur u v) + 7 / 2 * log (1 - i2P1Ur u v) ^ 2) / (u * v)

/-- `G₋ = -log (1 - r) (h(s) + h(t)) / (u v)`. -/
noncomputable def i2P1UGm (u v : ℝ) : ℝ :=
  -log (1 - i2P1Ur u v) * (i2P1Uh (i2P1Us u v) + i2P1Uh (i2P1Us v u)) / (u * v)

/-- `(Li₂ z + 7/2 log² (1 - z)) / (z (1 - z))`. -/
noncomputable def i2P1UFp (z : ℝ) : ℝ :=
  (i2P1ULi z + 7 / 2 * log (1 - z) ^ 2) / (z * (1 - z))

/-- `-log (1 - z) / (z (1 - z))`. -/
noncomputable def i2P1UFm (z : ℝ) : ℝ := -log (1 - z) / (z * (1 - z))

theorem i2P1Ur_mem {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (huv : u + v < 1) :
    i2P1Ur u v ∈ Ioo (0 : ℝ) 1 := by
  have h1 : 0 < 1 - u := by linarith
  have h2 : 0 < 1 - v := by linarith
  refine ⟨by unfold i2P1Ur; positivity, ?_⟩
  unfold i2P1Ur
  rw [div_lt_one (by positivity)]
  nlinarith

theorem i2P1Us_mem {u v : ℝ} (hu : 0 < u) (huv : u + v < 1) : i2P1Us u v ∈ Ioo (0 : ℝ) 1 := by
  have h2 : 0 < 1 - v := by linarith
  exact ⟨div_pos hu h2, (div_lt_one h2).2 (by linarith)⟩

theorem i2P1Uh_nonneg {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) : 0 ≤ i2P1Uh s := by
  have := log_nonpos hs.1.le hs.2.le
  have := log_nonpos (by linarith [hs.2]) (by linarith [hs.1] : 1 - s ≤ 1)
  unfold i2P1Uh
  linarith

theorem i2P1UGp_nonneg {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (huv : u + v < 1) :
    0 ≤ i2P1UGp u v := by
  have hr := i2P1Ur_mem hu hv huv
  have := Li₂_nonneg (le_max_left 0 (min (i2P1Ur u v) 1))
  unfold i2P1UGp i2P1ULi
  positivity

theorem i2P1UGm_nonneg {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (huv : u + v < 1) :
    0 ≤ i2P1UGm u v := by
  have hr := i2P1Ur_mem hu hv huv
  have h1 := log_nonpos (by linarith [hr.2]) (by linarith [hr.1] : 1 - i2P1Ur u v ≤ 1)
  have h2 := i2P1Uh_nonneg (i2P1Us_mem hu huv)
  have h3 := i2P1Uh_nonneg (i2P1Us_mem hv (by linarith : v + u < 1))
  unfold i2P1UGm
  exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)

/-- **`T = G₊ - G₋`** on the triangle. -/
theorem i2P1UT_eq {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (huv : u + v < 1) :
    i2P1UT u v = i2P1UGp u v - i2P1UGm u v := by
  have hr := i2P1Ur_mem hu hv huv
  have h1 : 0 < 1 - u := by linarith
  have h2 : 0 < 1 - v := by linarith
  have h3 : 0 < 1 - u - v := by linarith
  have e1 : log (1 - i2P1Ur u v) = log (1 - u - v) - log (1 - u) - log (1 - v) := by
    rw [show 1 - i2P1Ur u v = (1 - u - v) / ((1 - u) * (1 - v)) by
      unfold i2P1Ur; field_simp; ring, log_div h3.ne' (by positivity), log_mul h1.ne' h2.ne']
    ring
  have e2 : log (i2P1Us u v) = log u - log (1 - v) := by
    rw [i2P1Us, log_div hu.ne' h2.ne']
  have e3 : log (1 - i2P1Us u v) = log (1 - u - v) - log (1 - v) := by
    rw [i2P1Us, show 1 - u / (1 - v) = (1 - u - v) / (1 - v) by field_simp; ring,
      log_div h3.ne' h2.ne']
  have e4 : log (i2P1Us v u) = log v - log (1 - u) := by
    rw [i2P1Us, log_div hv.ne' h1.ne']
  have e5 : log (1 - i2P1Us v u) = log (1 - u - v) - log (1 - u) := by
    rw [i2P1Us, show 1 - v / (1 - u) = (1 - u - v) / (1 - u) by field_simp,
      log_div h3.ne' h1.ne']
  have e6 : log (u * (1 - u)) = log u + log (1 - u) := log_mul hu.ne' h1.ne'
  have e7 : log (v * (1 - v)) = log v + log (1 - v) := log_mul hv.ne' h2.ne'
  have e8 : log (u * v * (1 - u - v)) = log u + log v + log (1 - u - v) := by
    rw [log_mul (by positivity) h3.ne', log_mul hu.ne' hv.ne']
  unfold i2P1UT i2P1UGp i2P1UGm i2P1Uh
  rw [i2P1ULi_eq hr.1.le hr.2.le, e1, e2, e3, e4, e5, e6, e7, e8]
  simp only [i2P1Ur]
  generalize Li₂ (u * v / ((1 - u) * (1 - v))) = L
  generalize log u = a
  generalize log v = b
  generalize log (1 - u) = c
  generalize log (1 - v) = d
  generalize log (1 - u - v) = e
  have : u * v ≠ 0 := by positivity
  field_simp
  ring

/-- The square-to-triangle map: `r`, `s`, `t` and the Jacobian over `u v`. -/
theorem i2P1U_sq_identities {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    i2P1Ur (s * (1 - t) / (1 - s * t)) (t * (1 - s) / (1 - s * t)) = t * s ∧
    i2P1Us (s * (1 - t) / (1 - s * t)) (t * (1 - s) / (1 - s * t)) = s ∧
    i2P1Us (t * (1 - s) / (1 - s * t)) (s * (1 - t) / (1 - s * t)) = t ∧
    (1 - s) * (1 - t) / (1 - s * t) ^ 3 /
      (s * (1 - t) / (1 - s * t) * (t * (1 - s) / (1 - s * t))) =
      1 / (t * s * (1 - t * s)) := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨ht0, ht1⟩ := ht
  have hD : 0 < 1 - s * t := by nlinarith
  have h1 : 0 < 1 - s := by linarith
  have h2 : 0 < 1 - t := by linarith
  have hD' : 1 - s * t ≠ 0 := hD.ne'
  have hD2 : 1 - t * s ≠ 0 := by rw [mul_comm]; exact hD'
  have ha : 1 - s * (1 - t) / (1 - s * t) = (1 - s) / (1 - s * t) := by field_simp; ring
  have hb : 1 - t * (1 - s) / (1 - s * t) = (1 - t) / (1 - s * t) := by field_simp; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [i2P1Ur, ha, hb]
    field_simp
  · rw [i2P1Us, hb]
    field_simp
  · rw [i2P1Us, ha]
    field_simp
  · field_simp

theorem measurable_i2P1UGp : Measurable (uncurry fun u v => ENNReal.ofReal (i2P1UGp u v)) := by
  unfold i2P1UGp i2P1Ur
  fun_prop

theorem measurable_i2P1UGm : Measurable (uncurry fun u v => ENNReal.ofReal (i2P1UGm u v)) := by
  unfold i2P1UGm i2P1Ur i2P1Uh i2P1Us
  fun_prop

theorem i2P1U_mul_div_of {J P N Q : ℝ} (h : J / P = 1 / Q) : J * (N / P) = N / Q := by
  rw [show J * (N / P) = N * (J / P) by ring, h]
  ring

/-- **`∫_triangle G₊ = 7 π⁴ / 60`**. -/
theorem i2P1UTri_plus :
    ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) (1 - u), ENNReal.ofReal (i2P1UGp u v) =
      ENNReal.ofReal (7 * π ^ 4 / 60) := by
  rw [i2P1US_tri_sq measurable_i2P1UGp]
  have e : ∀ t ∈ Ioo (0 : ℝ) 1, ∫⁻ s in Ioo (0 : ℝ) 1,
      ENNReal.ofReal ((1 - s) * (1 - t) / (1 - s * t) ^ 3) *
        ENNReal.ofReal (i2P1UGp (s * (1 - t) / (1 - s * t)) (t * (1 - s) / (1 - s * t))) =
      ∫⁻ s in Ioo (0 : ℝ) 1, (fun _ => (1 : ℝ≥0∞)) t * ENNReal.ofReal (i2P1UFp (t * s)) := by
    intro t ht
    refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    obtain ⟨hr, -, -, hJ⟩ := i2P1U_sq_identities hs ht
    have hD : 0 < 1 - s * t := by nlinarith [hs.1, hs.2, ht.1, ht.2]
    rw [one_mul, ← ENNReal.ofReal_mul (div_nonneg (mul_nonneg (by linarith [hs.2])
      (by linarith [ht.2])) (pow_pos hD 3).le)]
    congr 1
    rw [i2P1UGp, hr, i2P1U_mul_div_of hJ, i2P1UFp]
  rw [setLIntegral_congr_fun measurableSet_Ioo e]
  refine (i2P1US_sq_z (k := fun _ => 1) (F := fun z => ENNReal.ofReal (i2P1UFp z))
    (by unfold i2P1UFp; fun_prop) measurable_const).trans ?_
  have e2 : ∀ z ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (i2P1UFp z) *
      ∫⁻ s in Ioo z 1, (fun _ => (1 : ℝ≥0∞)) s * ENNReal.ofReal (1 / s) =
      ENNReal.ofReal ((Li₂ z + 7 / 2 * log (1 - z) ^ 2) * (-log z) / (z * (1 - z))) := by
    intro z hz
    simp only [one_mul]
    rw [i2P1UZ_lint_inv hz.1 hz.2, ← ENNReal.ofReal_mul (by
      have := Li₂_nonneg (le_max_left 0 (min z 1))
      unfold i2P1UFp i2P1ULi
      have := hz.1
      have : 0 < 1 - z := by linarith [hz.2]
      positivity), i2P1UFp, i2P1ULi_eq hz.1.le hz.2.le]
    congr 1
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioo e2]
  refine i2P1UZ_lint_of zero_le_one i2P1UZ_plus.1 (fun z hz => ?_) i2P1UZ_plus.2
  have := Li₂_nonneg hz.1.le
  have := log_nonpos hz.1.le hz.2.le
  have := hz.1
  have : 0 < 1 - z := by linarith [hz.2]
  have : 0 ≤ -log z := by linarith
  positivity

/-- The `z`-reduction of one half of `G₋`. -/
theorem i2P1UTri_minus_half :
    ∫⁻ a in Ioo (0 : ℝ) 1, ∫⁻ b in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (i2P1Uh a) * ENNReal.ofReal (i2P1UFm (a * b)) =
      ENNReal.ofReal (13 * π ^ 4 / 120) := by
  refine (i2P1US_sq_z (k := fun a => ENNReal.ofReal (i2P1Uh a))
    (F := fun z => ENNReal.ofReal (i2P1UFm z)) (by unfold i2P1UFm; fun_prop)
    (by unfold i2P1Uh; fun_prop)).trans ?_
  have e2 : ∀ z ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (i2P1UFm z) *
      ∫⁻ s in Ioo z 1, ENNReal.ofReal (i2P1Uh s) * ENNReal.ofReal (1 / s) =
      ENNReal.ofReal (-log (1 - z) * i2P1UZK z / (z * (1 - z))) := by
    intro z hz
    have e3 : ∫⁻ s in Ioo z 1, ENNReal.ofReal (i2P1Uh s) * ENNReal.ofReal (1 / s) =
        ∫⁻ s in Ioo z 1, ENNReal.ofReal ((-log s - 2 * log (1 - s)) / s) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
      rw [← ENNReal.ofReal_mul (i2P1Uh_nonneg ⟨by linarith [hs.1, hz.1], hs.2⟩), i2P1Uh]
      congr 1
      ring
    have := hz.1
    have h1 : 0 < 1 - z := by linarith [hz.2]
    have := log_nonpos h1.le (by linarith)
    rw [e3, i2P1UZ_lint_h hz.1 hz.2, ← ENNReal.ofReal_mul (by
      unfold i2P1UFm
      exact div_nonneg (by linarith) (by positivity)), i2P1UFm]
    congr 1
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioo e2]
  refine i2P1UZ_lint_of zero_le_one i2P1UZ_minus.1 (fun z hz => ?_) i2P1UZ_minus.2
  have hK : 0 ≤ i2P1UZK z := by
    have := Li₂_nonneg hz.1.le
    have hL : Li₂ z ≤ π ^ 2 / 6 := by
      rw [← Li₂_one]
      exact monotoneOn_Li₂ ⟨by linarith [hz.1], hz.2.le⟩ ⟨by norm_num, le_rfl⟩ hz.2.le
    unfold i2P1UZK
    nlinarith [sq_nonneg (log z)]
  have := hz.1
  have h1 : 0 < 1 - z := by linarith [hz.2]
  have := log_nonpos h1.le (by linarith)
  exact div_nonneg (mul_nonneg (by linarith) hK) (by positivity)

/-- **`∫_triangle G₋ = 13 π⁴ / 60`**. -/
theorem i2P1UTri_minus :
    ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) (1 - u), ENNReal.ofReal (i2P1UGm u v) =
      ENNReal.ofReal (13 * π ^ 4 / 60) := by
  rw [i2P1US_tri_sq measurable_i2P1UGm]
  have hm1 : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (i2P1Uh p.1) * ENNReal.ofReal (i2P1UFm (p.1 * p.2)) := by
    unfold i2P1Uh i2P1UFm; fun_prop
  have hm2 : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (i2P1Uh p.2) * ENNReal.ofReal (i2P1UFm (p.1 * p.2)) := by
    unfold i2P1Uh i2P1UFm; fun_prop
  have e : ∀ t ∈ Ioo (0 : ℝ) 1, ∫⁻ s in Ioo (0 : ℝ) 1,
      ENNReal.ofReal ((1 - s) * (1 - t) / (1 - s * t) ^ 3) *
        ENNReal.ofReal (i2P1UGm (s * (1 - t) / (1 - s * t)) (t * (1 - s) / (1 - s * t))) =
      (∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (i2P1Uh t) * ENNReal.ofReal (i2P1UFm (t * s))) +
        ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (i2P1Uh s) * ENNReal.ofReal (i2P1UFm (t * s)) := by
    intro t ht
    rw [← lintegral_add_left (f := fun s => ENNReal.ofReal (i2P1Uh t) *
      ENNReal.ofReal (i2P1UFm (t * s))) (by unfold i2P1Uh i2P1UFm; fun_prop)]
    refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    obtain ⟨hr, h1, h2, hJ⟩ := i2P1U_sq_identities hs ht
    have hD : 0 < 1 - s * t := by nlinarith [hs.1, hs.2, ht.1, ht.2]
    have hz : t * s ∈ Ioo (0 : ℝ) 1 := ⟨mul_pos ht.1 hs.1, by nlinarith [hs.1, hs.2, ht.1, ht.2]⟩
    have hF : 0 ≤ i2P1UFm (t * s) := by
      have := log_nonpos (by linarith [hz.2]) (by linarith [hz.1] : 1 - t * s ≤ 1)
      have : 0 < 1 - t * s := by linarith [hz.2]
      unfold i2P1UFm
      exact div_nonneg (by linarith) (by positivity [hz.1])
    rw [← ENNReal.ofReal_mul (div_nonneg (mul_nonneg (by linarith [hs.2])
      (by linarith [ht.2])) (pow_pos hD 3).le), ← ENNReal.ofReal_mul (i2P1Uh_nonneg ht),
      ← ENNReal.ofReal_mul (i2P1Uh_nonneg hs), ← ENNReal.ofReal_add
        (mul_nonneg (i2P1Uh_nonneg ht) hF) (mul_nonneg (i2P1Uh_nonneg hs) hF)]
    congr 1
    rw [i2P1UGm, hr, h1, h2, i2P1U_mul_div_of hJ, i2P1UFm]
    ring
  have hm1' : Measurable fun t => ∫⁻ s in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (i2P1Uh t) * ENNReal.ofReal (i2P1UFm (t * s)) := hm1.lintegral_prod_right'
  rw [setLIntegral_congr_fun measurableSet_Ioo e, lintegral_add_left hm1', i2P1UTri_minus_half]
  have hsw := i2P1US_swap (f := fun t s =>
    ENNReal.ofReal (i2P1Uh s) * ENNReal.ofReal (i2P1UFm (t * s))) hm2
  rw [hsw]
  have e4 : ∀ s ∈ Ioo (0 : ℝ) 1, ∫⁻ t in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (i2P1Uh s) * ENNReal.ofReal (i2P1UFm (t * s)) =
      ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (i2P1Uh s) * ENNReal.ofReal (i2P1UFm (s * t)) :=
    fun s _ => lintegral_congr fun t => by rw [mul_comm t s]
  rw [setLIntegral_congr_fun measurableSet_Ioo e4, i2P1UTri_minus_half,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end QED.ThreeLoopD
