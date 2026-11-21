/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLLowWeight
import QED.Polylog.ExtraIntegrals
import QED.Polylog.LiCalculus
import QED.Polylog.LiHalf

/-!
# Harmonic polylogarithms at `1`, weight at most three

The values `H(w; 1)` of the harmonic polylogarithms whose first letter is not `1` (for these
`H(w; x) → H(w; 1)` as `x → 1⁻`, `QED.Polylog.HPL.tendsto_hpl_one`), for every such word of
weight at most three over `{0, 1}` or over `{0, -1}`, and for the mixed word `(-1, 1)`, as
explicit constants in `log 2`, `π²` and `ζ(3) = zeta3`. Each value is the limit at `1⁻` of the
closed form of `QED.Polylog.HPL` in `QED.Polylog.HPLLowWeight`
(`QED.Polylog.HPL.hpl_one_eq_of_tendsto`).

## Main results

| word | `H(w; 1)` | word | `H(w; 1)` |
|---|---|---|---|
| `0`, `00`, `000` | `0` | `-1` | `log 2` |
| `01` | `π²/6` | `0-1` | `π²/12` |
| `-10` | `-π²/12` | `-1-1` | `log² 2 / 2` |
| `-11` | `π²/12 - log² 2 / 2` | `001` | `ζ(3)` |
| `010` | `-2 ζ(3)` | `011` | `ζ(3)` |
| `00-1` | `3 ζ(3)/4` | `0-10` | `-3 ζ(3)/2` |
| `0-1-1` | `ζ(3)/8` | `-100` | `3 ζ(3)/4` |
| `-10-1` | `π² log 2 / 12 - ζ(3)/4` | `-1-10` | `ζ(3)/8 - π² log 2 / 12` |
| `-1-1-1` | `log³ 2 / 6` | | |
-/

public section

open Real Set Filter Topology

namespace QED.Polylog.HPL

open Letter

/-! ### Tools -/

/-- If the first letter is not `1` and `H(a · w) = F` on `(0, 1)` with `F → c` at `1⁻`, then
`H(a · w; 1) = c`. -/
theorem hpl_one_eq_of_tendsto {a : Letter} (ha : a ≠ one) {w : List Letter} {F : ℝ → ℝ}
    {c : ℝ} (hF : ∀ x ∈ Ioo (0 : ℝ) 1, hpl (a :: w) x = F x)
    (hlim : Tendsto F (𝓝[<] 1) (𝓝 c)) : hpl (a :: w) 1 = c :=
  tendsto_nhds_unique (tendsto_hpl_one ha w) (hlim.congr' (by
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with x hx using (hF x hx).symm))

/-- A function continuous at `1` tends to its value there at `1⁻`. -/
theorem tendsto_nhdsLT_of_continuousAt {F : ℝ → ℝ} {c : ℝ} (hF : ContinuousAt F 1)
    (h : F 1 = c) : Tendsto F (𝓝[<] 1) (𝓝 c) := by
  rw [← h]
  exact hF.tendsto.mono_left nhdsWithin_le_nhds

/-- `Li k (g x) → Li k (g 1)` at `1⁻` for `g` continuous at `1`, with values in `[-1, 1]`. -/
theorem tendsto_Li_comp_one {k : ℕ} (hk : 2 ≤ k) {g : ℝ → ℝ} (hg : ContinuousAt g 1)
    (hg1 : g 1 ∈ Icc (-1 : ℝ) 1) (hgs : ∀ x ∈ Ioo (0 : ℝ) 1, g x ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun x => Li k (g x)) (𝓝[<] 1) (𝓝 (Li k (g 1))) :=
  tendsto_Li_comp hk hg1 (hg.tendsto.mono_left nhdsWithin_le_nhds)
    (by filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with x hx using hgs x hx)

/-- `Li k x → Li k 1` as `x → 1⁻`, for `2 ≤ k`. -/
theorem tendsto_Li_one_left {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (Li k) (𝓝[<] 1) (𝓝 (Li k 1)) :=
  tendsto_Li_comp_one (g := id) hk continuousAt_id (by simp)
    fun x hx => ⟨by show (-1 : ℝ) ≤ x; linarith [hx.1], hx.2.le⟩

/-- `Li k (-x) → Li k (-1)` as `x → 1⁻`, for `2 ≤ k`. -/
theorem tendsto_Li_neg_one_left {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (fun x => Li k (-x)) (𝓝[<] 1) (𝓝 (Li k (-1))) :=
  tendsto_Li_comp_one (g := fun x => -x) hk continuousAt_neg (by norm_num)
    fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩

/-- `log (1 + x) → log 2` as `x → 1⁻`. -/
theorem tendsto_log_one_add_one :
    Tendsto (fun x => log (1 + x)) (𝓝[<] 1) (𝓝 (log 2)) :=
  tendsto_nhdsLT_of_continuousAt (by fun_prop (disch := norm_num)) (by norm_num)

/-- `log x → 0` as `x → 1⁻`. -/
theorem tendsto_log_one : Tendsto log (𝓝[<] 1) (𝓝 0) :=
  tendsto_nhdsLT_of_continuousAt (continuousAt_log one_ne_zero) log_one

/-! ### Weight one and two -/

/-- The value `H(0; 1)`. -/
theorem hpl_zero_at_one : hpl [zero] 1 = 0 := by simp [hpl_zero]

/-- The value `H(-1; 1)`. -/
theorem hpl_negOne_at_one : hpl [negOne] 1 = log 2 :=
  hpl_one_eq_of_tendsto (by decide) (fun x hx => hpl_negOne hx) tendsto_log_one_add_one

/-- The value `H(0, 0; 1)`. -/
theorem hpl_zero_zero_at_one : hpl [zero, zero] 1 = 0 := by simp [hpl_zero_zero]

/-- The value `H(0, 1; 1)`. -/
theorem hpl_zero_one_at_one : hpl [zero, one] 1 = π ^ 2 / 6 := by
  have h := hpl_one_eq_of_tendsto (by decide) (fun x hx => hpl_zero_one hx)
    (tendsto_Li_one_left le_rfl)
  rwa [Li_two, Li₂_one] at h

/-- The value `H(0, -1; 1)`. -/
theorem hpl_zero_negOne_at_one : hpl [zero, negOne] 1 = π ^ 2 / 12 := by
  have h := hpl_one_eq_of_tendsto (by decide) (fun x hx => hpl_zero_negOne hx)
    (tendsto_Li_neg_one_left le_rfl).neg
  rw [h, Li_two, Li₂_neg_one]
  ring

/-- The value `H(-1, 0; 1)`. -/
theorem hpl_negOne_zero_at_one : hpl [negOne, zero] 1 = -π ^ 2 / 12 := by
  have h := hpl_one_eq_of_tendsto (by decide) (fun x hx => hpl_negOne_zero hx)
    ((tendsto_log_one.mul tendsto_log_one_add_one).add (tendsto_Li_neg_one_left le_rfl))
  rw [h, Li_two, Li₂_neg_one]
  ring

/-- The value `H(-1, -1; 1)`. -/
theorem hpl_negOne_negOne_at_one : hpl [negOne, negOne] 1 = log 2 ^ 2 / 2 :=
  hpl_one_eq_of_tendsto (by decide) (fun x hx => hpl_negOne_negOne hx)
    ((tendsto_log_one_add_one.pow 2).div_const 2)

/-- The value `H(-1, 1; 1)`. -/
theorem hpl_negOne_one_at_one : hpl [negOne, one] 1 = π ^ 2 / 12 - log 2 ^ 2 / 2 := by
  have t := tendsto_Li_comp_one (k := 2) (g := fun x => (1 + x) / 2) le_rfl (by fun_prop)
    (by norm_num) fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h := hpl_one_eq_of_tendsto (by decide) (fun x hx => hpl_negOne_one hx)
    ((t.sub_const (Li 2 (1 / 2))).sub (tendsto_log_one_add_one.const_mul (log 2)))
  rw [h, show (1 + 1 : ℝ) / 2 = 1 by norm_num, Li_two_one_half, Li_two, Li₂_one]
  ring

/-! ### Weight three over `{0, 1}` -/

/-- The value `H(0, 0, 0; 1)`. -/
theorem hpl_zero_zero_zero_at_one : hpl [zero, zero, zero] 1 = 0 := by
  simp [hpl_zero_zero_zero]

/-- The value `H(0, 0, 1; 1)`. -/
theorem hpl_zero_zero_one_at_one : hpl [zero, zero, one] 1 = zeta3 := by
  have h := hpl_one_eq_of_tendsto (by decide) (fun x hx => hpl_zero_zero_one hx)
    (tendsto_Li_one_left (k := 3) (by norm_num))
  rwa [Li_three_one] at h

/-- The value `H(0, 1, 0; 1)`. -/
theorem hpl_zero_one_zero_at_one : hpl [zero, one, zero] 1 = -2 * zeta3 := by
  have h := hpl_one_eq_of_tendsto (by decide) (fun x hx => hpl_zero_one_zero hx)
    ((tendsto_log_one.mul (tendsto_Li_one_left le_rfl)).sub
      ((tendsto_Li_one_left (k := 3) (by norm_num)).const_mul 2))
  rw [h, Li_three_one]
  ring

/-- The value `H(0, 1, 1; 1)`. -/
theorem hpl_zero_one_one_at_one : hpl [zero, one, one] 1 = zeta3 := by
  have t3 : Tendsto (fun x => Li 3 (1 - x)) (𝓝[<] 1) (𝓝 0) := by
    simpa using tendsto_Li_comp_one (k := 3) (g := fun x => 1 - x) (by norm_num) (by fun_prop)
      (by norm_num) fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have h := hpl_one_eq_of_tendsto (by decide) (fun x hx => hpl_zero_one_one hx)
    ((((tendsto_const_nhds (x := zeta3)).sub t3).add
      tendsto_log_one_sub_mul_Li₂_one_sub_one).add
      (tendsto_log_mul_log_one_sub_sq_one.div_const 2))
  rw [h]
  ring

/-! ### Weight three over `{0, -1}` -/

/-- The value `H(0, 0, -1; 1)`. -/
theorem hpl_zero_zero_negOne_at_one : hpl [zero, zero, negOne] 1 = 3 / 4 * zeta3 := by
  have h := hpl_one_eq_of_tendsto (by decide) (fun x hx => hpl_zero_zero_negOne hx)
    (tendsto_Li_neg_one_left (k := 3) (by norm_num)).neg
  rw [h, Li_three, Li₃_neg_one]
  ring

/-- The value `H(0, -1, 0; 1)`. -/
theorem hpl_zero_negOne_zero_at_one : hpl [zero, negOne, zero] 1 = -3 / 2 * zeta3 := by
  have h := hpl_one_eq_of_tendsto (by decide) (fun x hx => hpl_zero_negOne_zero hx)
    (((tendsto_log_one.neg).mul (tendsto_Li_neg_one_left le_rfl)).add
      ((tendsto_Li_neg_one_left (k := 3) (by norm_num)).const_mul 2))
  rw [h, Li_three, Li₃_neg_one]
  ring

/-- The value `H(0, -1, -1; 1)`. -/
theorem hpl_zero_negOne_negOne_at_one : hpl [zero, negOne, negOne] 1 = zeta3 / 8 := by
  have hc : ContinuousAt (fun x : ℝ => 1 / (1 + x)) 1 := by fun_prop (disch := norm_num)
  have hmem : ∀ x ∈ Ioo (0 : ℝ) 1, 1 / (1 + x) ∈ Icc (-1 : ℝ) 1 := fun x hx =>
    ⟨by have : 0 < 1 / (1 + x) := by have := hx.1; positivity
        linarith,
      by rw [div_le_one (by linarith [hx.1])]; linarith [hx.1]⟩
  have t3 := tendsto_Li_comp_one (k := 3) (by norm_num) hc (by norm_num) hmem
  have t2 := tendsto_Li_comp_one (k := 2) le_rfl hc (by norm_num) hmem
  have h := hpl_one_eq_of_tendsto (by decide) (fun x hx => hpl_zero_negOne_negOne hx)
    (((((tendsto_const_nhds (x := zeta3)).sub t3).sub (tendsto_log_one_add_one.mul t2)).sub
      ((tendsto_log_one_add_one.pow 3).div_const 3)).add
      ((tendsto_log_one.mul (tendsto_log_one_add_one.pow 2)).div_const 2))
  rw [h, show (1 : ℝ) / (1 + 1) = 1 / 2 by norm_num, Li_three_one_half, Li_two_one_half]
  ring

/-- The value `H(-1, 0, 0; 1)`. -/
theorem hpl_negOne_zero_zero_at_one : hpl [negOne, zero, zero] 1 = 3 / 4 * zeta3 := by
  have h := hpl_one_eq_of_tendsto (by decide) (fun x hx => hpl_negOne_zero_zero hx)
    (((((tendsto_log_one.pow 2).mul tendsto_log_one_add_one).div_const 2).add
      (tendsto_log_one.mul (tendsto_Li_neg_one_left le_rfl))).sub
      (tendsto_Li_neg_one_left (k := 3) (by norm_num)))
  rw [h, Li_three, Li₃_neg_one]
  ring

/-- The value `H(-1, 0, -1; 1)`. -/
theorem hpl_negOne_zero_negOne_at_one :
    hpl [negOne, zero, negOne] 1 = π ^ 2 / 12 * log 2 - zeta3 / 4 := by
  have h := hpl_one_eq_of_tendsto (by decide) (fun x hx => hpl_negOne_zero_negOne hx)
    (((tendsto_log_one_add_one.neg).mul (tendsto_Li_neg_one_left le_rfl)).sub
      ((tendsto_hpl_one (by decide) [negOne, negOne]).const_mul 2))
  rw [h, Li_two, Li₂_neg_one, hpl_zero_negOne_negOne_at_one]
  ring

/-- The value `H(-1, -1, 0; 1)`. -/
theorem hpl_negOne_negOne_zero_at_one :
    hpl [negOne, negOne, zero] 1 = zeta3 / 8 - π ^ 2 / 12 * log 2 := by
  have h := hpl_one_eq_of_tendsto (by decide) (fun x hx => hpl_negOne_negOne_zero hx)
    ((((tendsto_log_one.mul (tendsto_log_one_add_one.pow 2)).div_const 2).add
      (tendsto_log_one_add_one.mul (tendsto_Li_neg_one_left le_rfl))).add
      (tendsto_hpl_one (by decide) [negOne, negOne]))
  rw [h, Li_two, Li₂_neg_one, hpl_zero_negOne_negOne_at_one]
  ring

/-- The value `H(-1, -1, -1; 1)`. -/
theorem hpl_negOne_negOne_negOne_at_one : hpl [negOne, negOne, negOne] 1 = log 2 ^ 3 / 6 :=
  hpl_one_eq_of_tendsto (by decide) (fun x hx => hpl_negOne_negOne_negOne hx)
    ((tendsto_log_one_add_one.pow 3).div_const 6)

end QED.Polylog.HPL
