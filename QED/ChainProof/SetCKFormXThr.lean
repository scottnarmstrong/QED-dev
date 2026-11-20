/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormXH

/-!
# Set (c), Stage K, closed forms: the threshold of the crossed weight

Helper level (no frozen statement). At a node `(Y, y₃)`, `0 < y₃ < Y < 1`, and `m > 0` the
threshold `s ∈ (0, 1)` with `w₀(s) = m` (`cornInW0`) is explicit (`formXThr`): with
`g = y₃(1 - Y)`, `e = y₃(Y - y₃)` and `x* = (1 - Y)/(1 - y₃)`,

`s = m/g` if `m ≤ g x*`, and otherwise `s` is the positive root of `e s² + m s - m = 0`,
`s = (√(m² + 4 e m) - m)/(2e)`, which lies in `[x*, 1)`.

**`formXThr_mem`**, **`cornInW0_formXThr`**; hence **`formXHin_eq_thr`**: for
`0 < y₃ < Y < X < 1`, `formXHin Y y₃ X = formXF(Y, y₃, m, s(m))/(1 - Y)` with
`m = w_Y(X)`. This is the form of the inner integrand as a function of `m` alone, the input of
the `m`-derivative `S = ∂_m F` of the density route (`stageK/STATUS.md`, session 19+).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- **The threshold** `s(m)` with `w₀(s) = m`. -/
noncomputable def formXThr (Y y3 m : ℝ) : ℝ :=
  if m ≤ cornerG y3 (Y - y3) * cornInXs Y y3 then m / cornerG y3 (Y - y3)
  else (√(m ^ 2 + 4 * (y3 * (Y - y3)) * m) - m) / (2 * (y3 * (Y - y3)))

section

variable {Y y3 m : ℝ}

/-- `g x* = e x*²/(1 - x*)`: the two branches of `w₀` agree at `x*`. -/
theorem formX_g_xs (h3 : 0 < y3) (h34 : y3 < Y) (hY : Y < 1) :
    cornerG y3 (Y - y3) * cornInXs Y y3 * (1 - cornInXs Y y3) =
      y3 * (Y - y3) * cornInXs Y y3 ^ 2 := by
  have h1 : 1 - y3 ≠ 0 := by linarith
  unfold cornerG cornInXs
  field_simp
  ring

theorem formXThr_spec (h3 : 0 < y3) (h34 : y3 < Y) (hY : Y < 1) (hm : 0 < m) :
    formXThr Y y3 m ∈ Ioo (0 : ℝ) 1 ∧ cornInW0 Y y3 (formXThr Y y3 m) = m := by
  have hg := cornerG_pos hY h3
  have hxs := cornInXs_mem h3 h34 hY
  have he : 0 < y3 * (Y - y3) := mul_pos h3 (by linarith)
  unfold formXThr
  split_ifs with hb
  · have hs1 : m / cornerG y3 (Y - y3) ≤ cornInXs Y y3 := by rwa [div_le_iff₀ hg, mul_comm]
    have hs0 : 0 < m / cornerG y3 (Y - y3) := div_pos hm hg
    refine ⟨⟨hs0, hs1.trans_lt hxs.2⟩, ?_⟩
    rw [cornInW0, betaG_of_branch1 h3 (hs1.trans_lt hxs.2) (cornIn_branch1_of_xs h3 h34 hY hs1)]
    field_simp
  · rw [not_le] at hb
    set e := y3 * (Y - y3) with he_def
    set D := m ^ 2 + 4 * e * m with hD
    have hD0 : 0 ≤ D := by positivity
    have hq := Real.sq_sqrt hD0
    have hr := Real.sqrt_nonneg D
    set r := √D
    have hgx := formX_g_xs h3 h34 hY
    set xs := cornInXs Y y3
    have hr1 : m < r := by nlinarith
    have hr2 : r < 2 * e + m := by nlinarith
    have hr3 : 2 * e * xs + m ≤ r := by
      have h1 : e * xs ^ 2 < m * (1 - xs) := by
        rw [← hgx]
        exact mul_lt_mul_of_pos_right hb (by linarith [hxs.2])
      nlinarith [hxs.1]
    have hs0 : 0 < (r - m) / (2 * e) := div_pos (by linarith) (by positivity)
    have hs1 : (r - m) / (2 * e) < 1 := by rw [div_lt_one (by positivity)]; linarith
    have hsx : xs ≤ (r - m) / (2 * e) := by rw [le_div_iff₀ (by positivity)]; linarith
    refine ⟨⟨hs0, hs1⟩, ?_⟩
    rw [cornInW0_of_branch2 h3 hs1 (cornIn_branch2_of_xs h3 h34 hY hsx)]
    have h1s : 1 - (r - m) / (2 * e) ≠ 0 := by linarith
    rw [div_eq_iff h1s]
    field_simp
    nlinarith

/-- **The inner integrand at the explicit threshold.** -/
theorem formXHin_eq_thr {X : ℝ} (h3 : 0 < y3) (h34 : y3 < Y) (hYX : Y < X) (hX : X < 1) :
    formXHin Y y3 X =
      formXF Y y3 (cornInWX Y X) (formXThr Y y3 (cornInWX Y X)) / (1 - Y) := by
  have hw : 0 < cornInWX Y X := cornInWX_pos ⟨h3.trans h34, hYX.trans hX⟩ ⟨hYX, hX⟩
  obtain ⟨hs, hm⟩ := formXThr_spec h3 h34 (hYX.trans hX) hw
  exact formXHin_eq h3 h34 hYX hX hs hm

end

end QED.ChainProof.SetCK

end
