/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormXSDer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the bound on `S = ∂F/∂m`

Helper level (no frozen statement). Step 2 of route D for `ρ_X` (scratch `stageK/STATUS.md`,
sessions 19+, 22+): the absolute integrability needed for the Fubini swap comes from

**`formXS_bound`**: for `X < 1` there is `C ≥ 0` with `|S(Y, y₃, s(m))| ≤ C/(y₃ + m)` whenever
`0 < y₃ < Y ≤ X` and `m > 0`.

Below the switch `S₁ = N₁/(12 y₃ (Y - 1)³)` and `m ≤ y₃`. Above it the numerator of `S₂`
vanishes to third order at `s = 1`, `y₃ = Y` (**`formXN2_eq`**: `N₂ = t (d² Nₐ + t d N_b +
t² N_c)`, `t = 1 - s`, `d = Y - y₃`), so on the threshold `S₂ = (d² Nₐ + t d N_b + t² N_c)/
(12 s (2 - s) d² m)` (**`formXS2_eq_of_thr`**), with `t (1 - X) ≤ d`, `s ≥ 1 - X` and
`m ≥ y₃ (1 - X)²`. The polynomial coefficients are bounded on the unit cube by compactness
(**`formX_exists_bound_cube`**). Numerics (scratch `stageK/fx/xs4.py`, `probe.py`):
`|S| (y₃ + m) ≤ 2.9·10³` on `2·10⁵` random points with `Y ≤ 0.9`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- A coefficient of the decomposition of `formXN2`. -/
noncomputable def formXNa (Y y3 : ℝ) : ℝ :=
  -4 * y3 - 2 * y3 ^ 2 + 6 * Y * y3

/-- A coefficient of the decomposition of `formXN2`. -/
noncomputable def formXNb (Y y3 : ℝ) : ℝ :=
  2 - y3 ^ 2 - 4 * Y - 3 * Y ^ 2 + 6 * y3 + 6 * Y ^ 3 + 14 * y3 ^ 3 - 18 * Y * y3 ^ 2 - 9 * Y * y3
      + 6 * y3 * Y ^ 2

/-- A coefficient of the decomposition of `formXN2`. -/
noncomputable def formXNc (Y y3 s : ℝ) : ℝ :=
  -19 * Y ^ 3 + 2 * y3 + 3 * y3 ^ 3 + 6 * Y ^ 4 + 6 * y3 ^ 2 + 11 * Y ^ 2 + 16 * y3 ^ 4 + s ^ 2
      * y3 ^ 3 - 42 * Y * y3 ^ 3 - 28 * Y ^ 2 * s ^ 2 - 20 * Y * y3 ^ 2 - 19 * s * Y ^ 3 - 19 * y3
      * Y ^ 3 - 18 * Y * y3 - 9 * s ^ 2 * y3 ^ 2 - 6 * Y * s ^ 3 - 6 * s ^ 3 * y3 ^ 2 - 5 * y3
      * s ^ 2 - 2 * s ^ 3 * y3 ^ 3 + 2 * s * y3 + 2 * s ^ 3 * y3 ^ 4 + 5 * Y * s ^ 2 + 6 * s * Y ^ 4
      + 6 * s * y3 ^ 2 + 6 * y3 * s ^ 3 + 6 * Y ^ 2 * s ^ 3 + 7 * s * y3 ^ 3 + 10 * s ^ 2 * y3 ^ 4
      + 11 * s * Y ^ 2 + 12 * Y ^ 3 * s ^ 2 + 18 * s * y3 ^ 4 + 34 * y3 * Y ^ 2 + 40 * Y ^ 2
      * y3 ^ 2 - 52 * Y * s * y3 ^ 3 - 28 * Y * s * y3 ^ 2 - 25 * s * y3 * Y ^ 3 - 19 * Y * s ^ 2
      * y3 ^ 3 - 18 * Y * s * y3 - 8 * y3 * Y ^ 2 * s ^ 3 - 7 * Y * s ^ 2 * y3 ^ 2 - 6 * y3 * Y ^ 2
      * s ^ 2 - 6 * y3 * Y ^ 3 * s ^ 2 - 4 * Y * s ^ 3 * y3 ^ 3 + 2 * Y ^ 2 * s ^ 3 * y3 ^ 2 + 10
      * Y * s ^ 3 * y3 ^ 2 + 15 * Y ^ 2 * s ^ 2 * y3 ^ 2 + 37 * Y * y3 * s ^ 2 + 38 * s * y3 * Y ^ 2
      + 54 * s * Y ^ 2 * y3 ^ 2

/-- A continuous function of three variables is bounded on the unit cube. -/
theorem formX_exists_bound_cube (f : ℝ → ℝ → ℝ → ℝ)
    (hf : Continuous fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) :
    ∃ K, ∀ a b c, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 → c ∈ Icc (0 : ℝ) 1 → |f a b c| ≤ K := by
  obtain ⟨K, hK⟩ :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).exists_bound_of_continuousOn
      hf.continuousOn
  exact ⟨K, fun a b c ha hb hc => hK (a, b, c) ⟨ha, hb, hc⟩⟩

/-- The numerator of `S₂` vanishes to third order at `s = 1`, `y₃ = Y`. -/
theorem formXN2_eq (Y y3 s : ℝ) :
    formXN2 Y y3 s = (1 - s) * ((Y - y3) ^ 2 * formXNa Y y3 +
      (1 - s) * (Y - y3) * formXNb Y y3 + (1 - s) ^ 2 * formXNc Y y3 s) := by
  unfold formXN2 formXNa formXNb formXNc
  ring

section

variable {Y y3 s m : ℝ}

/-- `S₂` on the threshold `e s² = m(1 - s)`, with the factor `1 - s` cancelled. -/
theorem formXS2_eq_of_thr (h3 : y3 ≠ 0) (h4 : Y - y3 ≠ 0) (hs : s ≠ 0) (hs2 : 2 - s ≠ 0)
    (hm : m ≠ 0) (h : y3 * (Y - y3) * s ^ 2 = m * (1 - s)) :
    formXS2 Y y3 s = ((Y - y3) ^ 2 * formXNa Y y3 + (1 - s) * (Y - y3) * formXNb Y y3 +
      (1 - s) ^ 2 * formXNc Y y3 s) / (12 * s * (2 - s) * (Y - y3) ^ 2 * m) := by
  have h43 : y3 - Y ≠ 0 := by contrapose! h4; linarith
  have hs2' : s - 2 ≠ 0 := by contrapose! hs2; linarith
  unfold formXS2
  rw [formXN2_eq, div_eq_div_iff (by positivity) (by positivity)]
  set Q := (Y - y3) ^ 2 * formXNa Y y3 + (1 - s) * (Y - y3) * formXNb Y y3 +
    (1 - s) ^ 2 * formXNc Y y3 s
  linear_combination (-(Q * 12 * s * (2 - s) * (Y - y3) ^ 2)) * h

/-- `|S₁| ≤ K/(12 y₃ (1 - Y)³)` for a bound `K` of the numerator. -/
theorem abs_formXS1_le {K : ℝ} (h3 : 0 < y3) (hY : Y < 1) (hK : |formXN1 Y y3 s| ≤ K) :
    |formXS1 Y y3 s| ≤ K / (12 * y3 * (1 - Y) ^ 3) := by
  have h1 : 0 < 1 - Y := by linarith
  unfold formXS1
  rw [abs_div, show |12 * y3 * (Y - 1) ^ 3| = 12 * y3 * (1 - Y) ^ 3 by
    rw [show (Y - 1) ^ 3 = -(1 - Y) ^ 3 by ring, mul_neg, abs_neg]
    exact abs_of_pos (by positivity)]
  exact div_le_div_of_nonneg_right hK (by positivity)

/-- The numerator bound above the switch: `|d² Nₐ + t d N_b + t² N_c| ≤ d² L` for
`t k ≤ d`. -/
theorem formX_abs_Q_le {d t k Ka Kb Kc : ℝ} (hd : 0 ≤ d) (ht : 0 ≤ t) (hk : 0 < k)
    (htd : t * k ≤ d) (ha : |formXNa Y y3| ≤ |Ka|) (hb : |formXNb Y y3| ≤ |Kb|)
    (hc : |formXNc Y y3 s| ≤ |Kc|) :
    |d ^ 2 * formXNa Y y3 + t * d * formXNb Y y3 + t ^ 2 * formXNc Y y3 s| ≤
      d ^ 2 * (|Ka| + |Kb| / k + |Kc| / k ^ 2) := by
  have ht' : t ≤ d / k := by rw [le_div_iff₀ hk]; exact htd
  calc _ ≤ |d ^ 2 * formXNa Y y3| + |t * d * formXNb Y y3| + |t ^ 2 * formXNc Y y3 s| :=
        abs_add_three _ _ _
    _ = d ^ 2 * |formXNa Y y3| + t * d * |formXNb Y y3| + t ^ 2 * |formXNc Y y3 s| := by
        simp only [abs_mul, abs_pow, abs_of_nonneg hd, abs_of_nonneg ht]
    _ ≤ d ^ 2 * |Ka| + d / k * d * |Kb| + (d / k) ^ 2 * |Kc| := by gcongr
    _ = d ^ 2 * (|Ka| + |Kb| / k + |Kc| / k ^ 2) := by ring

end

/-- **The bound on `S`**: for `Y ≤ X < 1`, `|S(Y, y₃, s(m))| ≤ C/(y₃ + m)`. -/
theorem formXS_bound {X : ℝ} (hX : X < 1) :
    ∃ C, 0 ≤ C ∧ ∀ Y y3 m, 0 < y3 → y3 < Y → Y ≤ X → 0 < m →
      |formXS Y y3 (formXThr Y y3 m)| ≤ C / (y3 + m) := by
  obtain ⟨K1, hK1⟩ := formX_exists_bound_cube (fun a b c => formXN1 a b c)
    (by unfold formXN1; fun_prop)
  obtain ⟨Ka, hKa⟩ := formX_exists_bound_cube (fun a b _ => formXNa a b)
    (by unfold formXNa; fun_prop)
  obtain ⟨Kb, hKb⟩ := formX_exists_bound_cube (fun a b _ => formXNb a b)
    (by unfold formXNb; fun_prop)
  obtain ⟨Kc, hKc⟩ := formX_exists_bound_cube (fun a b c => formXNc a b c)
    (by unfold formXNc; fun_prop)
  set k := 1 - X with hk_def
  have hk : 0 < k := by linarith
  set L := |Ka| + |Kb| / k + |Kc| / k ^ 2
  refine ⟨max (2 * |K1| / (12 * k ^ 3)) (L * (1 + 1 / k ^ 2) / (12 * k)),
    le_max_of_le_left (by positivity), fun Y y3 m h3 h34 hYX hm => ?_⟩
  have hY : Y < 1 := by linarith
  have hY1 : k ≤ 1 - Y := by linarith
  have hy1 : 0 < 1 - y3 := by linarith
  have hg := cornerG_pos hY h3
  have hxs := cornInXs_mem h3 h34 hY
  have hgE : cornerG y3 (Y - y3) = y3 * (1 - Y) := by unfold cornerG; ring
  have hxsE : cornInXs Y y3 = (1 - Y) / (1 - y3) := rfl
  have hI : ∀ a : ℝ, 0 < a → a < 1 → a ∈ Icc (0 : ℝ) 1 := fun a h0 h1 => ⟨h0.le, h1.le⟩
  have hYI := hI Y (h3.trans h34) hY
  have hyI := hI y3 h3 (h34.trans hY)
  rw [le_div_iff₀ (by positivity), formXThr_eq]
  split_ifs with hb
  · set s := m / cornerG y3 (Y - y3) with hs_def
    have hs0 : 0 < s := div_pos hm hg
    have hsx : s ≤ cornInXs Y y3 := by rw [hs_def, div_le_iff₀ hg, mul_comm]; exact hb
    rw [formXS, ite_eq_left hsx]
    have h1 := abs_formXS1_le (s := s) h3 hY
      ((hK1 Y y3 s hYI hyI (hI s hs0 (hsx.trans_lt hxs.2))).trans (le_abs_self K1))
    have hmy : m ≤ y3 := by
      have hms : m ≤ cornerG y3 (Y - y3) * cornInXs Y y3 := hb
      rw [hgE, hxsE] at hms
      have : y3 * (1 - Y) * ((1 - Y) / (1 - y3)) ≤ y3 := by
        rw [mul_div_assoc', div_le_iff₀ hy1]
        nlinarith
      linarith
    have hYp : 0 < 1 - Y := by linarith
    calc |formXS1 Y y3 s| * (y3 + m) ≤ |K1| / (12 * y3 * (1 - Y) ^ 3) * (2 * y3) :=
          mul_le_mul h1 (by linarith) (by positivity) (by positivity)
      _ = 2 * |K1| / (12 * (1 - Y) ^ 3) := by field_simp
      _ ≤ 2 * |K1| / (12 * k ^ 3) := by gcongr
      _ ≤ _ := le_max_left _ _
  · have hms : cornerG y3 (Y - y3) * cornInXs Y y3 < m := not_le.mp hb
    have he : 0 < y3 * (Y - y3) := mul_pos h3 (by linarith)
    obtain ⟨hs, hsm⟩ := formXThr2_spec he hm
    have hxl := cornInXs_lt_formXThr2 h3 h34 hY hms
    set s := formXThr2 Y y3 m
    rw [formXS, ite_eq_right (not_le.mpr hxl)]
    have hd : 0 < Y - y3 := by linarith
    have hs2 : 2 - s ≠ 0 := by linarith [hs.2]
    rw [formXS2_eq_of_thr h3.ne' hd.ne' hs.1.ne' hs2 hm.ne' hsm]
    set Q := (Y - y3) ^ 2 * formXNa Y y3 + (1 - s) * (Y - y3) * formXNb Y y3 +
      (1 - s) ^ 2 * formXNc Y y3 s
    have hxk : k ≤ cornInXs Y y3 := by
      rw [hxsE, le_div_iff₀ hy1]
      nlinarith
    have hks : k ≤ s := hxk.trans hxl.le
    have htd : (1 - s) * k ≤ Y - y3 := by
      have h1 : (1 - Y) / (1 - y3) < s := hxl
      rw [div_lt_iff₀ hy1] at h1
      nlinarith
    have hQ : |Q| ≤ (Y - y3) ^ 2 * L :=
      formX_abs_Q_le hd.le (by linarith [hs.2]) hk htd
        ((hKa Y y3 0 hYI hyI ⟨le_rfl, zero_le_one⟩).trans (le_abs_self _))
        ((hKb Y y3 0 hYI hyI ⟨le_rfl, zero_le_one⟩).trans (le_abs_self _))
        ((hKc Y y3 s hYI hyI (hI s hs.1 hs.2)).trans (le_abs_self _))
    have hym : y3 * k ^ 2 ≤ m := by
      have h1 : cornerG y3 (Y - y3) * cornInXs Y y3 = y3 * (1 - Y) ^ 2 / (1 - y3) := by
        rw [hgE, hxsE]; ring
      rw [h1, div_lt_iff₀ hy1] at hms
      have : y3 * k ^ 2 ≤ y3 * (1 - Y) ^ 2 := by gcongr
      nlinarith
    have hden : 0 < 12 * s * (2 - s) * (Y - y3) ^ 2 * m := by
      have : 0 < 2 - s := by linarith [hs.2]
      have := hs.1
      positivity
    have hden2 : 12 * k * (Y - y3) ^ 2 ≤ 12 * s * (2 - s) * (Y - y3) ^ 2 := by
      have : k ≤ s * (2 - s) := by nlinarith [hs.2]
      have : 0 ≤ (Y - y3) ^ 2 := sq_nonneg _
      nlinarith
    rw [abs_div, abs_of_pos hden]
    calc |Q| / (12 * s * (2 - s) * (Y - y3) ^ 2 * m) * (y3 + m) ≤
          |Q| / (12 * s * (2 - s) * (Y - y3) ^ 2 * m) * (m * (1 + 1 / k ^ 2)) := by
          gcongr
          rw [mul_add, mul_one, mul_one_div]
          have : y3 ≤ m / k ^ 2 := by rw [le_div_iff₀ (by positivity)]; exact hym
          linarith
      _ = |Q| * (1 + 1 / k ^ 2) / (12 * s * (2 - s) * (Y - y3) ^ 2) := by
          field_simp
      _ ≤ (Y - y3) ^ 2 * L * (1 + 1 / k ^ 2) / (12 * k * (Y - y3) ^ 2) := by
          gcongr
      _ = L * (1 + 1 / k ^ 2) / (12 * k) := by field_simp
      _ ≤ _ := le_max_right _ _

end QED.ChainProof.SetCK

end
