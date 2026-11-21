/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLLyndon3
import QED.Polylog.ExtraIntegrals
import QED.Polylog.HPLValues
import QED.Polylog.LiCalculus
import QED.Polylog.LiHalf
import QED.Polylog.LiLimits

/-!
# Harmonic polylogarithms at `1`: the mixed words of weight three

The values `H(w; 1)` of the seven weight-3 words over `{0, 1, -1}` that contain both letters
`1` and `-1` and do not start with `1`, as explicit constants in `ζ(3) = zeta3`, `π² log 2` and
`log³ 2`. Together with `QED.Polylog.HPLValues` this completes the values at `1` of all
weight-3 words whose first letter is not `1`.

| word | `H(w; 1)` | word | `H(w; 1)` |
|---|---|---|---|
| `01-1` | `π² log 2 / 4 - ζ(3)` | `0-11` | `13 ζ(3)/8 - π² log 2 / 4` |
| `-101` | `π² log 2 / 6 - 5 ζ(3)/8` | `-110` | `π² log 2 / 12 - ζ(3)` |
| `-111` | `Li₃(1/2)` | `-11-1` | `π² log 2 / 12 - ζ(3)/4 - log³ 2 / 6` |
| `-1-11` | `ζ(3)/8 - log³ 2 / 6` | | |

Each value is the limit at `1⁻` of a closed form; the divergent pieces `log (1 - x) · g(x)` and
`log² (1 - x) · g(x)` are controlled by `|g(x)| ≤ C (1 - x)`.
-/

public section

open Real Set Filter Topology

namespace QED.Polylog.HPL

open Letter

/-! ### Limit tools -/

/-- `g log² (1 - x) → 0` at `1⁻` when `|g x| ≤ C (1 - x)` eventually. -/
theorem tendsto_mul_log_one_sub_sq_of_abs_le {g : ℝ → ℝ} {C : ℝ}
    (hb : ∀ᶠ x in 𝓝[<] (1 : ℝ), |g x| ≤ C * (1 - x)) :
    Tendsto (fun x => g x * log (1 - x) ^ 2) (𝓝[<] 1) (𝓝 0) := by
  have hb' : ∀ᶠ t in 𝓝[>] (0 : ℝ), |g (1 - t)| ≤ C * t :=
    (tendsto_one_sub_nhdsGT_zero.eventually hb).mono fun t ht => by
      simpa only [sub_sub_cancel] using ht
  have h := (tendsto_mul_log_sq_of_abs_le hb').comp tendsto_one_sub_nhdsLT_one
  refine h.congr' ?_
  filter_upwards with x
  simp only [Function.comp_apply, sub_sub_cancel]

/-- `|log ((1 + x)/2)| ≤ 1 - x` written with `log (1 + x) - log 2`. -/
theorem abs_log_one_add_sub_log_two_le {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    |log (1 + x) - log 2| ≤ 1 - x := by
  rw [← log_div (by linarith [hx.1]) (by norm_num)]
  exact abs_log_one_add_div_two_le hx.1.le hx.2.le

/-- `|log (1 + x)| ≤ 1` on `(0, 1)`. -/
theorem abs_log_one_add_le_one {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : |log (1 + x)| ≤ 1 := by
  rw [abs_of_nonneg (log_nonneg (by linarith [hx.1]))]
  have := Real.log_le_sub_one_of_pos (by linarith [hx.1] : (0 : ℝ) < 1 + x)
  linarith [hx.2]

/-- Eventually `x ∈ (0, 1)` at `1⁻`. -/
theorem eventually_mem_Ioo_zero_one_nhdsLT : ∀ᶠ x in 𝓝[<] (1 : ℝ), x ∈ Ioo (0 : ℝ) 1 :=
  Ioo_mem_nhdsLT zero_lt_one

/-! ### The Lyndon words -/

/-- The value `H(0, 1, -1; 1) = π² log 2 / 4 - ζ(3)`. -/
theorem hpl_zero_one_negOne_at_one : hpl [zero, one, negOne] 1 = π ^ 2 / 4 * log 2 - zeta3 := by
  have t1 := tendsto_Li_one_left (k := 3) (by norm_num)
  have t2 := tendsto_Li_neg_one_left (k := 3) (by norm_num)
  have t3 := tendsto_Li_comp_one (k := 3) (g := fun x => (1 + x) / 2) (by norm_num)
    (by fun_prop) (by norm_num) fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have t4 := tendsto_Li_comp_one (k := 3) (g := fun x => 1 / (1 + x)) (by norm_num)
    (by fun_prop (disch := norm_num)) (by norm_num) fun x hx =>
      ⟨by have : 0 < 1 / (1 + x) := by have := hx.1; positivity
          linarith, by rw [div_le_one (by linarith [hx.1])]; linarith [hx.1]⟩
  have t5 := tendsto_Li_comp_one (k := 3) (g := fun x => 2 * x / (1 + x)) (by norm_num)
    (by fun_prop (disch := norm_num)) (by norm_num) fun x hx =>
      ⟨by have : 0 < 2 * x / (1 + x) := by have := hx.1; have := hx.2; positivity
          linarith, by rw [div_le_one (by linarith [hx.1])]; linarith [hx.2]⟩
  have t6 := tendsto_Li_one_left (k := 2) le_rfl
  have tp := QED.Polylog.HPL.tendsto_log_one_add_one
  have tx := tendsto_log_one
  have h := (((((((((t1.neg.add t2).sub t3).add t4).add t5).add (tp.mul t6)).add
    ((tx.mul (tp.pow 2)).div_const 2)).sub ((tp.pow 3).div_const 3)).add
    ((tp.pow 2).const_mul (log 2 / 2))).add (tp.const_mul (Li 2 (1 / 2) + π ^ 2 / 6))).add_const
    (Li 3 (1 / 2) - zeta3)
  rw [hpl_one_eq_of_tendsto (by decide) (fun x hx => hpl_zero_one_negOne hx) h]
  norm_num [Li_three_one, Li_two, Li₂_one, Li_three, Li₃_neg_one]
  rw [← Li_three, Li_three_one_half, ← Li_two, Li_two_one_half]
  ring

/-- The value `H(0, -1, 1; 1) = 13 ζ(3)/8 - π² log 2 / 4`. -/
theorem hpl_zero_negOne_one_at_one :
    hpl [zero, negOne, one] 1 = 13 / 8 * zeta3 - π ^ 2 / 4 * log 2 := by
  have t1 := tendsto_Li_one_left (k := 3) (by norm_num)
  have t2 := tendsto_Li_neg_one_left (k := 3) (by norm_num)
  have t3 := tendsto_Li_comp_one (k := 3) (g := fun x => 1 - x) (by norm_num)
    (by fun_prop) (by norm_num) fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have t4 := tendsto_Li_comp_one (k := 3) (g := fun x => (1 - x) / 2) (by norm_num)
    (by fun_prop) (by norm_num) fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have t5 := tendsto_Li_comp_one (k := 3) (g := fun x => (1 - x) / (1 + x)) (by norm_num)
    (by fun_prop (disch := norm_num)) (by norm_num) fun x hx =>
      ⟨by have : 0 < (1 - x) / (1 + x) := div_pos (by linarith [hx.2]) (by linarith [hx.1])
          linarith, by rw [div_le_one (by linarith [hx.1])]; linarith [hx.1]⟩
  have t6 := tendsto_Li_comp_one (k := 3) (g := fun x => 2 * x / (1 + x)) (by norm_num)
    (by fun_prop (disch := norm_num)) (by norm_num) fun x hx =>
      ⟨by have : 0 < 2 * x / (1 + x) := by have := hx.1; have := hx.2; positivity
          linarith, by rw [div_le_one (by linarith [hx.1])]; linarith [hx.2]⟩
  have tp := QED.Polylog.HPL.tendsto_log_one_add_one
  have tx := tendsto_log_one
  have tA := tendsto_log_one_sub_mul_Li₂_neg_add_one
  have tB := tendsto_log_mul_log_one_sub_one
  have tC := tendsto_mul_log_one_sub_of_abs_le (g := fun x => (log (1 + x) - log 2) ^ 2)
    (C := 1) (by
      filter_upwards [eventually_mem_Ioo_zero_one_nhdsLT] with x hx
      have h1 := abs_log_one_add_sub_log_two_le hx
      have h2 : |log (1 + x) - log 2| ≤ 1 := h1.trans (by linarith [hx.1])
      rw [abs_pow, one_mul, sq]
      calc |log (1 + x) - log 2| * |log (1 + x) - log 2| ≤ (1 - x) * 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) (by linarith [hx.2])
        _ = 1 - x := mul_one _)
  have h := ((((((((((((t1.sub t2).add t3).sub t4).sub t5).sub t6).sub
    ((tx.mul (tp.pow 2)).div_const 2)).add ((tp.pow 3).div_const 3)).sub
    ((tp.pow 2).const_mul (log 2 / 2))).sub (tp.const_mul (π ^ 2 / 6))).add_const
    (Li 3 (1 / 2))).add tA).add (tB.mul tp)).sub (tC.div_const 2)
  have hF : ∀ x ∈ Ioo (0 : ℝ) 1, hpl [zero, negOne, one] x =
      Li 3 x - Li 3 (-x) + Li 3 (1 - x) - Li 3 ((1 - x) / 2) - Li 3 ((1 - x) / (1 + x)) -
        Li 3 (2 * x / (1 + x)) - log x * log (1 + x) ^ 2 / 2 + log (1 + x) ^ 3 / 3 -
        log 2 / 2 * log (1 + x) ^ 2 - π ^ 2 / 6 * log (1 + x) + Li 3 (1 / 2) +
        log (1 - x) * (Li₂ (-x) + π ^ 2 / 12) + log x * log (1 - x) * log (1 + x) -
        (log (1 + x) - log 2) ^ 2 * log (1 - x) / 2 := by
    intro x hx
    rw [hpl_zero_negOne_one hx, Li_two_one_half, ← Li_two]
    ring
  rw [hpl_one_eq_of_tendsto (by decide) hF h]
  norm_num [Li_three_one, Li_three, Li₃_neg_one]
  rw [← Li_three, Li_three_one_half]
  ring

/-! ### Shuffle consequences -/

/-- The value `H(-1, 0, 1; 1) = π² log 2 / 6 - 5 ζ(3)/8`. -/
theorem hpl_negOne_zero_one_at_one :
    hpl [negOne, zero, one] 1 = π ^ 2 / 6 * log 2 - 5 / 8 * zeta3 := by
  have h := ((QED.Polylog.HPL.tendsto_log_one_add_one.mul (tendsto_Li_one_left (k := 2) le_rfl)).sub
    (tendsto_hpl_one (a := zero) (by decide) [negOne, one])).sub
    (tendsto_hpl_one (a := zero) (by decide) [one, negOne])
  rw [hpl_one_eq_of_tendsto (by decide) (fun x hx => hpl_negOne_zero_one hx) h,
    hpl_zero_negOne_one_at_one, hpl_zero_one_negOne_at_one, Li_two, Li₂_one]
  ring

/-- The value `H(-1, 1, 0; 1) = π² log 2 / 12 - ζ(3)`. -/
theorem hpl_negOne_one_zero_at_one :
    hpl [negOne, one, zero] 1 = π ^ 2 / 12 * log 2 - zeta3 := by
  have h := ((tendsto_log_one.mul (tendsto_hpl_one (a := negOne) (by decide) [one])).sub
    (tendsto_hpl_one (a := zero) (by decide) [negOne, one])).sub
    (tendsto_hpl_one (a := negOne) (by decide) [zero, one])
  rw [hpl_one_eq_of_tendsto (by decide) (fun x hx => hpl_negOne_one_zero hx) h,
    hpl_zero_negOne_one_at_one, hpl_negOne_zero_one_at_one]
  ring

/-- The value `H(-1, 1, 1; 1) = Li₃(1/2)`. -/
theorem hpl_negOne_one_one_at_one : hpl [negOne, one, one] 1 = Li 3 (1 / 2) := by
  have t1 := tendsto_Li_comp_one (k := 3) (g := fun x => (1 - x) / 2) (by norm_num)
    (by fun_prop) (by norm_num) fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have tA := tendsto_mul_log_one_sub_sq_of_abs_le (g := fun x => (log (1 + x) - log 2) / 2)
    (C := 1) (by
      filter_upwards [eventually_mem_Ioo_zero_one_nhdsLT] with x hx
      rw [abs_div, abs_two, one_mul]
      linarith [abs_log_one_add_sub_log_two_le hx, abs_nonneg (log (1 + x) - log 2)])
  have tB := tendsto_mul_log_one_sub_of_abs_le (g := fun x => Li 2 ((1 - x) / 2))
    (C := π ^ 2 / 6) (by
      filter_upwards [eventually_mem_Ioo_zero_one_nhdsLT] with x hx
      have h := abs_Li_le (k := 2) le_rfl (y := (1 - x) / 2)
        (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2])
      rw [abs_of_pos (by linarith [hx.2] : (0 : ℝ) < (1 - x) / 2)] at h
      nlinarith [pi_pos, hx.2])
  have h := ((tA.add tB).add_const (Li 3 (1 / 2))).sub t1
  have hF : ∀ x ∈ Ioo (0 : ℝ) 1, hpl [negOne, one, one] x =
      (log (1 + x) - log 2) / 2 * log (1 - x) ^ 2 + Li 2 ((1 - x) / 2) * log (1 - x) +
        Li 3 (1 / 2) - Li 3 ((1 - x) / 2) := by
    intro x hx
    rw [hpl_negOne_one_one hx, hpl_one_negOne_one hx, hpl_one_one_negOne hx, hpl_one_negOne hx]
    ring
  rw [hpl_one_eq_of_tendsto (by decide) hF h]
  norm_num

/-- The value `H(-1, 1, -1; 1) = π² log 2 / 12 - ζ(3)/4 - log³ 2 / 6`. -/
theorem hpl_negOne_one_negOne_at_one :
    hpl [negOne, one, negOne] 1 = π ^ 2 / 12 * log 2 - zeta3 / 4 - log 2 ^ 3 / 6 := by
  have t1 := tendsto_Li_comp_one (k := 3) (g := fun x => (1 + x) / 2) (by norm_num)
    (by fun_prop) (by norm_num) fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have t2 := tendsto_Li_comp_one (k := 2) (g := fun x => (1 - x) / 2) le_rfl
    (by fun_prop) (by norm_num) fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have tp := QED.Polylog.HPL.tendsto_log_one_add_one
  have tA := tendsto_mul_log_one_sub_of_abs_le (g := fun x => log (1 + x) * (log 2 - log (1 + x)))
    (C := 1) (by
      filter_upwards [eventually_mem_Ioo_zero_one_nhdsLT] with x hx
      have h1 := abs_log_one_add_sub_log_two_le hx
      rw [abs_sub_comm] at h1
      rw [abs_mul, one_mul]
      calc |log (1 + x)| * |log 2 - log (1 + x)| ≤ 1 * (1 - x) :=
            mul_le_mul (abs_log_one_add_le_one hx) h1 (abs_nonneg _) zero_le_one
        _ = 1 - x := one_mul _)
  have h := ((((((tp.mul t2).neg.sub (tp.const_mul (Li 2 (1 / 2)))).sub
    (t1.const_mul 2)).add_const (2 * Li 3 (1 / 2))).add ((tp.pow 2).const_mul (log 2))).sub
    (tp.const_mul (2 * (log 2 ^ 2 - π ^ 2 / 6)))).add tA
  have hF : ∀ x ∈ Ioo (0 : ℝ) 1, hpl [negOne, one, negOne] x =
      -(log (1 + x) * Li 2 ((1 - x) / 2)) - Li 2 (1 / 2) * log (1 + x) -
        2 * Li 3 ((1 + x) / 2) + 2 * Li 3 (1 / 2) + log 2 * log (1 + x) ^ 2 -
        2 * (log 2 ^ 2 - π ^ 2 / 6) * log (1 + x) +
        log (1 + x) * (log 2 - log (1 + x)) * log (1 - x) := by
    intro x hx
    rw [hpl_negOne_one_negOne hx, hpl_one_negOne_negOne hx, hpl_one_negOne hx]
    ring
  rw [hpl_one_eq_of_tendsto (by decide) hF h]
  norm_num [Li_three_one, Li_three, Li_two]
  rw [← Li_three, Li_three_one_half, ← Li_two, Li_two_one_half]
  ring

/-- The value `H(-1, -1, 1; 1) = ζ(3)/8 - log³ 2 / 6`. -/
theorem hpl_negOne_negOne_one_at_one :
    hpl [negOne, negOne, one] 1 = zeta3 / 8 - log 2 ^ 3 / 6 := by
  have t1 := tendsto_Li_comp_one (k := 3) (g := fun x => (1 + x) / 2) (by norm_num)
    (by fun_prop) (by norm_num) fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have tp := QED.Polylog.HPL.tendsto_log_one_add_one
  have h := (((t1.sub_const (Li 3 (1 / 2))).add (tp.const_mul (Li 2 (1 / 2)))).sub
    ((tp.pow 2).const_mul (log 2 / 2))).add (tp.const_mul (log 2 ^ 2 - π ^ 2 / 6))
  have hF : ∀ x ∈ Ioo (0 : ℝ) 1, hpl [negOne, negOne, one] x =
      Li 3 ((1 + x) / 2) - Li 3 (1 / 2) + Li 2 (1 / 2) * log (1 + x) -
        log 2 / 2 * log (1 + x) ^ 2 + (log 2 ^ 2 - π ^ 2 / 6) * log (1 + x) := by
    intro x hx
    rw [hpl_negOne_negOne_one hx, hpl_negOne_one_negOne hx, hpl_one_negOne_negOne hx,
      hpl_one_negOne hx]
    ring
  rw [hpl_one_eq_of_tendsto (by decide) hF h]
  norm_num [Li_three_one, Li_three]
  rw [← Li_three, Li_three_one_half, Li_two_one_half]
  ring

end QED.Polylog.HPL
