/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormXS
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the crossed `x`-integral as a function of `m`

Helper level (no frozen statement). Step 1 of route D for `ρ_X` (scratch `stageK/STATUS.md`,
sessions 19+, 22+). At a node `0 < y₃ < Y < 1` the threshold switches branch at
`m* = g x*` (`formXMs`); above it the threshold is the root `formXThr2` of
`e s² + m s - m = 0`, with **`hasDerivAt_formXThr2`**: `s′ = (1 - s)/(2es + m)`. The
`x`-integral as a function of `m` is `formXFm` (the cubic `formXF1` up to `m*`,
`formXF2 = P₁(x*) + P₂(s) - P₂(x*)` above), and

* **`formXFm_eq`**: `formXFm Y y₃ m = formXF Y y₃ m (formXThr Y y₃ m)` for `m > 0`;
* **`continuous_formXFm`** (the branches agree at `m*`, **`formXF2_ms`**);
* **`hasDerivAt_formXFm`**: `F′(m) = S(s(m))` (`formXS`) for `m > 0`, `m ≠ m*`
  (above the switch **`hasDerivAt_formXF2`**, from the generic **`formX_hasDerivAt_sub`**, the
  vanishing logarithm **`formX_log_thr`** and `formX_S2_id`).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- The switch value `m* = g x*` of `m` between the two threshold branches. -/
noncomputable def formXMs (Y y3 : ℝ) : ℝ := cornerG y3 (Y - y3) * cornInXs Y y3

/-- The threshold above the switch: the positive root of `e s² + m s - m = 0`. -/
noncomputable def formXThr2 (Y y3 m : ℝ) : ℝ :=
  (√(m ^ 2 + 4 * (y3 * (Y - y3)) * m) - m) / (2 * (y3 * (Y - y3)))

/-- The `x`-integral above the switch, `P₁(x*) + P₂(s) - P₂(x*)` at `s = formXThr2`. -/
noncomputable def formXF2 (Y y3 m : ℝ) : ℝ :=
  formXP1 Y y3 m (cornInXs Y y3) + formXP2 Y y3 m (formXThr2 Y y3 m) -
    formXP2 Y y3 m (cornInXs Y y3)

/-- **The `x`-integral as a function of `m`**, the polynomial `formXF1` below the switch. -/
noncomputable def formXFm (Y y3 m : ℝ) : ℝ :=
  if m ≤ formXMs Y y3 then formXF1 Y y3 m else formXF2 Y y3 m

theorem formXThr_eq (Y y3 m : ℝ) : formXThr Y y3 m =
    if m ≤ formXMs Y y3 then m / cornerG y3 (Y - y3) else formXThr2 Y y3 m := rfl

/-- A generic `m`-derivative: `f = g + a (m⁻¹ - m₀⁻¹) + b (m⁻² - m₀⁻²) + k (log m - log m₀)`
near `m₀`. -/
theorem formX_hasDerivAt_sub {f g a b k : ℝ → ℝ} {m₀ q a' b' k' : ℝ}
    (hfg : ∀ᶠ m in 𝓝 m₀, f m = g m + a m * (m⁻¹ - m₀⁻¹) + b m * ((m ^ 2)⁻¹ - (m₀ ^ 2)⁻¹) +
      k m * (log m - log m₀))
    (hm₀ : m₀ ≠ 0) (hg : HasDerivAt g q m₀) (ha : HasDerivAt a a' m₀) (hb : HasDerivAt b b' m₀)
    (hk : HasDerivAt k k' m₀) :
    HasDerivAt f (q - a m₀ / m₀ ^ 2 - 2 * b m₀ / m₀ ^ 3 + k m₀ / m₀) m₀ := by
  have h2 : m₀ ^ 2 ≠ 0 := pow_ne_zero 2 hm₀
  have hi := hasDerivAt_inv hm₀
  have hi2 := (hasDerivAt_pow 2 m₀).inv h2
  have h := ((hg.add (ha.mul (hi.sub_const m₀⁻¹))).add (hb.mul (hi2.sub_const (m₀ ^ 2)⁻¹))).add
    (hk.mul ((hasDerivAt_log hm₀).sub_const (log m₀)))
  refine (h.congr_of_eventuallyEq hfg).congr_deriv ?_
  simp only [Pi.inv_apply, sub_self, mul_zero, zero_add]
  field_simp
  ring

section

variable {Y y3 m : ℝ}

/-- The threshold above the switch is the nonnegative root. -/
theorem formXThr2_eq_of {s : ℝ} (he : 0 < y3 * (Y - y3)) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (h : y3 * (Y - y3) * s ^ 2 = m * (1 - s)) : formXThr2 Y y3 m = s := by
  unfold formXThr2
  set e := y3 * (Y - y3)
  rw [show m ^ 2 + 4 * e * m = (2 * e * s + m) ^ 2 by linear_combination (-4 * e) * h,
    Real.sqrt_sq (by positivity)]
  field_simp
  ring

theorem formXThr2_spec (he : 0 < y3 * (Y - y3)) (hm : 0 < m) :
    formXThr2 Y y3 m ∈ Ioo (0 : ℝ) 1 ∧
      y3 * (Y - y3) * formXThr2 Y y3 m ^ 2 = m * (1 - formXThr2 Y y3 m) := by
  set e := y3 * (Y - y3)
  set D := m ^ 2 + 4 * e * m with hD
  have hD0 : 0 ≤ D := by positivity
  have hq := Real.sq_sqrt hD0
  have hr := Real.sqrt_nonneg D
  set r := √D
  have hr1 : m < r := by nlinarith
  have hr2 : r < 2 * e + m := by nlinarith
  unfold formXThr2
  refine ⟨⟨div_pos (by linarith) (by positivity), (div_lt_one (by positivity)).2 (by linarith)⟩,
    ?_⟩
  have key : e * ((r - m) / (2 * e)) ^ 2 - m * (1 - (r - m) / (2 * e)) =
      (r ^ 2 - (m ^ 2 + 4 * e * m)) / (4 * e) := by field_simp; ring
  rw [hq, sub_self, zero_div] at key
  linarith

/-- The derivative of the threshold above the switch: `s′ = (1 - s)/(2es + m)`. -/
theorem hasDerivAt_formXThr2 (he : 0 < y3 * (Y - y3)) (hm : 0 < m) :
    HasDerivAt (formXThr2 Y y3) ((1 - formXThr2 Y y3 m) /
      (2 * (y3 * (Y - y3)) * formXThr2 Y y3 m + m)) m := by
  unfold formXThr2
  set e := y3 * (Y - y3)
  have hD : 0 < m ^ 2 + 4 * e * m := by positivity
  have hr : 0 < √(m ^ 2 + 4 * e * m) := Real.sqrt_pos.2 hD
  have h1 : HasDerivAt (fun m => m ^ 2 + 4 * e * m) (2 * m + 4 * e) m := by
    refine ((hasDerivAt_pow 2 m).add ((hasDerivAt_id' m).const_mul (4 * e))).congr_deriv ?_
    push_cast
    ring
  have h := ((h1.sqrt hD.ne').sub (hasDerivAt_id' m)).div_const (2 * e)
  refine h.congr_deriv ?_
  rw [show 2 * e * ((√(m ^ 2 + 4 * e * m) - m) / (2 * e)) + m = √(m ^ 2 + 4 * e * m) by
    field_simp; ring]
  field_simp
  ring

/-- On the threshold the logarithm of the weight vanishes. -/
theorem formX_log_thr {s : ℝ} (h3 : 0 < y3) (h34 : y3 < Y) (hm : 0 < m) (hs : s ∈ Ioo (0 : ℝ) 1)
    (h : y3 * (Y - y3) * s ^ 2 = m * (1 - s)) :
    log m - log (y3 * (Y - y3)) - 2 * log s + log (1 - s) = 0 := by
  have he : 0 < y3 * (Y - y3) := mul_pos h3 (by linarith)
  have h1 : 0 < 1 - s := by linarith [hs.2]
  have := congrArg log h
  rw [Real.log_mul he.ne' (by have := hs.1; positivity), Real.log_pow,
    Real.log_mul hm.ne' h1.ne'] at this
  push_cast at this
  linarith

/-- **The derivative above the switch**: `F₂′(m) = S₂(s(m))`. -/
theorem hasDerivAt_formXF2 (h3 : 0 < y3) (h34 : y3 < Y) (hY : Y < 1) (hm : 0 < m) :
    HasDerivAt (formXF2 Y y3) (formXS2 Y y3 (formXThr2 Y y3 m)) m := by
  have he : 0 < y3 * (Y - y3) := mul_pos h3 (by linarith)
  obtain ⟨hs, hsm⟩ := formXThr2_spec he hm
  have hσ := hasDerivAt_formXThr2 he hm
  set σ := formXThr2 Y y3 with hσ_def
  set s := σ m with hs_def
  have hxs := cornInXs_mem h3 h34 hY
  set xs := cornInXs Y y3
  have hY' : -1 + Y ≠ 0 := by contrapose! hY; linarith
  have h4 : y3 - Y ≠ 0 := by contrapose! h34; linarith
  have h4' : Y - y3 ≠ 0 := by contrapose! h34; linarith
  have hne : ∀ᶠ m' in 𝓝 m, m' ≠ 0 := eventually_ne_nhds hm.ne'
  have d1 := formX_hasDerivAt_sub (f := fun m' => formXP1 Y y3 m' xs)
    (g := fun _ => formXP1 Y y3 m xs) (a := fun _ => formXUa Y y3 xs)
    (b := fun _ => formXUb Y y3 xs) (k := fun _ => formXK1 Y y3 xs * xs)
    (hne.mono fun m' hm' => by have := formXP1_sub (y3 := y3) hm' hm.ne' hY' xs; linarith) hm.ne'
    (hasDerivAt_const _ _) (hasDerivAt_const _ _) (hasDerivAt_const _ _) (hasDerivAt_const _ _)
  have d2 := formX_hasDerivAt_sub (f := fun m' => formXP2 Y y3 m' xs)
    (g := fun _ => formXP2 Y y3 m xs) (a := fun _ => formXUa Y y3 xs)
    (b := fun _ => formXUb Y y3 xs) (k := fun _ => formXK1 Y y3 xs * xs)
    (hne.mono fun m' hm' => by have := formXP2_sub hm' hm.ne' h4 xs; linarith) hm.ne'
    (hasDerivAt_const _ _) (hasDerivAt_const _ _) (hasDerivAt_const _ _) (hasDerivAt_const _ _)
  have hs0 : s ≠ 0 := hs.1.ne'
  have hs1 : 1 - s ≠ 0 := by linarith [hs.2]
  have g3 : HasDerivAt (fun m' => formXP2 Y y3 m (σ m'))
      (formXE2 Y y3 m s * ((1 - s) / (2 * (y3 * (Y - y3)) * s + m))) m :=
    HasDerivAt.comp m (h₂ := formXP2 Y y3 m) (hasDerivAt_formXP2 (Y := Y) (y3 := y3) (m := m)
      (x := s) hs0 hs1 hm.ne' h3.ne' h4') hσ
  have a3 : HasDerivAt (fun m' => formXUa Y y3 (σ m')) _ m :=
    (hasDerivAt_formXUa Y y3 s).comp m hσ
  have b3 : HasDerivAt (fun m' => formXUb Y y3 (σ m')) _ m :=
    (hasDerivAt_formXUb Y y3 s).comp m hσ
  have k3 : HasDerivAt (fun m' => formXK1 Y y3 (σ m') * σ m') _ m :=
    ((hasDerivAt_formXK1 (Y := Y) (y3 := y3) (x := s)).comp m hσ).mul hσ
  have d3 := formX_hasDerivAt_sub (f := fun m' => formXP2 Y y3 m' (σ m'))
    (hne.mono fun m' hm' => by have := formXP2_sub hm' hm.ne' h4 (σ m'); linarith) hm.ne'
    g3 a3 b3 k3
  refine ((d1.add d3).sub d2).congr_deriv ?_
  have hlog := formX_log_thr h3 h34 hm hs hsm
  have hm' : m = y3 * (Y - y3) * s ^ 2 / (1 - s) := by field_simp; linarith
  have hs2 : s - 2 ≠ 0 := by linarith [hs.2]
  rw [← formX_S2_id h3.ne' h4' hs0 hs1 hs2, ← hm']
  unfold formXE2 formXDm
  rw [hlog]
  ring

/-- The two branches agree at the switch. -/
theorem formXF2_ms (h3 : 0 < y3) (h34 : y3 < Y) (hY : Y < 1) :
    formXF2 Y y3 (formXMs Y y3) = formXF1 Y y3 (formXMs Y y3) := by
  have hg := cornerG_pos hY h3
  have hxs := cornInXs_mem h3 h34 hY
  have he : 0 < y3 * (Y - y3) := mul_pos h3 (by linarith)
  have hms : 0 < formXMs Y y3 := mul_pos hg hxs.1
  have hY' : -1 + Y ≠ 0 := by contrapose! hY; linarith
  have hthr : formXThr2 Y y3 (formXMs Y y3) = cornInXs Y y3 :=
    formXThr2_eq_of he hms.le hxs.1.le (by
      have := formX_g_xs h3 h34 hY
      unfold formXMs
      linarith)
  unfold formXF2
  rw [hthr, add_sub_cancel_right, ← formXP1_eq_formXF1 hms.ne' h3.ne' hY' hg.ne']
  unfold formXMs
  rw [mul_div_cancel_left₀ _ hg.ne']

/-- Above the switch the threshold lies strictly above `x*`. -/
theorem cornInXs_lt_formXThr2 (h3 : 0 < y3) (h34 : y3 < Y) (hY : Y < 1)
    (hm : formXMs Y y3 < m) : cornInXs Y y3 < formXThr2 Y y3 m := by
  have hg := cornerG_pos hY h3
  have hxs := cornInXs_mem h3 h34 hY
  have he : 0 < y3 * (Y - y3) := mul_pos h3 (by linarith)
  have hms : 0 < formXMs Y y3 := mul_pos hg hxs.1
  obtain ⟨hs, hsm⟩ := formXThr2_spec he (hms.trans hm)
  have hgx := formX_g_xs h3 h34 hY
  unfold formXMs at hm hms
  by_contra hle
  replace hle := not_lt.mp hle
  have h1 : y3 * (Y - y3) * formXThr2 Y y3 m ^ 2 ≤ y3 * (Y - y3) * cornInXs Y y3 ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.1.le hle 2) he.le
  have h2 : cornerG y3 (Y - y3) * cornInXs Y y3 * (1 - cornInXs Y y3) <
      m * (1 - cornInXs Y y3) := mul_lt_mul_of_pos_right hm (by linarith [hxs.2])
  nlinarith

/-- **`formXFm` is the `x`-integral**: `F(m) = formXF Y y₃ m s(m)` for `m > 0`. -/
theorem formXFm_eq (h3 : 0 < y3) (h34 : y3 < Y) (hY : Y < 1) (hm : 0 < m) :
    formXFm Y y3 m = formXF Y y3 m (formXThr Y y3 m) := by
  have hg := cornerG_pos hY h3
  have hY' : -1 + Y ≠ 0 := by contrapose! hY; linarith
  unfold formXFm
  rw [formXThr_eq]
  split_ifs with h
  · have hs : m / cornerG y3 (Y - y3) ≤ cornInXs Y y3 := by
      rw [div_le_iff₀ hg, mul_comm]
      exact h
    unfold formXF
    rw [min_eq_left hs, add_sub_cancel_right, formXP1_eq_formXF1 hm.ne' h3.ne' hY' hg.ne']
  · have hs := cornInXs_lt_formXThr2 h3 h34 hY (not_le.mp h)
    unfold formXF formXF2
    rw [min_eq_right hs.le]

theorem continuous_formXFm (h3 : 0 < y3) (h34 : y3 < Y) (hY : Y < 1) :
    Continuous (formXFm Y y3) := by
  have hms : 0 < formXMs Y y3 := mul_pos (cornerG_pos hY h3) (cornInXs_mem h3 h34 hY).1
  have h1 : Continuous (formXF1 Y y3) := by unfold formXF1; exact continuous_formOSP6 _ _ _ _ _ _ _
  exact continuous_if_le continuous_id continuous_const h1.continuousOn
    (fun m hm => (hasDerivAt_formXF2 h3 h34 hY
      (hms.trans_le hm)).continuousAt.continuousWithinAt)
    (fun m hm => by rw [show m = formXMs Y y3 from hm]; exact (formXF2_ms h3 h34 hY).symm)

/-- **`F′(m) = S(s(m))`** off the switch. -/
theorem hasDerivAt_formXFm (h3 : 0 < y3) (h34 : y3 < Y) (hY : Y < 1) (hm : 0 < m)
    (hne : m ≠ formXMs Y y3) :
    HasDerivAt (formXFm Y y3) (formXS Y y3 (formXThr Y y3 m)) m := by
  have hg := cornerG_pos hY h3
  have hY' : -1 + Y ≠ 0 := by contrapose! hY; linarith
  rw [formXThr_eq]
  rcases lt_or_gt_of_ne hne with h | h
  · have hs : m / cornerG y3 (Y - y3) ≤ cornInXs Y y3 := by
      rw [div_le_iff₀ hg, mul_comm]
      exact h.le
    rw [ite_eq_left h.le, formXS, ite_eq_left hs]
    refine (hasDerivAt_formXF1 h3.ne' hY').congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h] with m' hm'
    exact ite_eq_left (le_of_lt hm')
  · have hs := cornInXs_lt_formXThr2 h3 h34 hY h
    rw [ite_eq_right (not_le.mpr h), formXS, ite_eq_right (not_le.mpr hs)]
    refine (hasDerivAt_formXF2 h3 h34 hY hm).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds h] with m' hm'
    exact ite_eq_right (not_le.mpr hm')

end

end QED.ChainProof.SetCK

end
