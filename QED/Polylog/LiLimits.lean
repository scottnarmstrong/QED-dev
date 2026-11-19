/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.LiN
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Order.Basic
import QED.Polylog.ExtraIntegrals
import QED.Polylog.LiCalculus

/-!
# Endpoint limits for polylogarithmic antiderivatives

Limits at `0⁺` and `1⁻` of the building blocks of the antiderivatives of
`QED.Chain.setAJ`-type integrands.

## Main results

* `QED.Polylog.tendsto_Li_sub_log_mul_Li_comp`, `QED.Polylog.tendsto_Li_sub_log_mul_Li_comp_zero`:
  limits of `Li k f - log f · Li j f` along `f → a`, for `a ≠ 0` and for `a = 0`.
* `QED.Polylog.tendsto_mul_log_sq_of_abs_le`: `g log² x → 0` at `0⁺` when `|g| ≤ C x`.
* `QED.Polylog.tendsto_mul_log_one_sub_of_abs_le`: `g log (1 - x) → 0` at `1⁻` when
  `|g| ≤ C (1 - x)`.
* `QED.Polylog.abs_log_one_add_div_two_le`: `|log ((1 + x)/2)| ≤ 1 - x` on `[0, 1]`.
* `QED.Polylog.tendsto_log_one_sub_mul_log_sq`, `QED.Polylog.tendsto_log_one_add_mul_log_sq`:
  `log (1 ∓ x) log² x → 0` at `0⁺`.
-/

public section

open Real Set Filter Topology

namespace QED.Polylog

/-- `Li k f - log f · Li j f → Li k a - log a · Li j a` along `f → a ≠ 0`, `a ∈ [-1, 1]`. -/
theorem tendsto_Li_sub_log_mul_Li_comp {α : Type*} {l : Filter α} {k j : ℕ} (hk : 2 ≤ k)
    (hj : 2 ≤ j) {g : α → ℝ} {a : ℝ} (ha : a ∈ Icc (-1 : ℝ) 1) (ha0 : a ≠ 0)
    (hg : Tendsto g l (𝓝 a)) (hgs : ∀ᶠ x in l, g x ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun x => Li k (g x) - log (g x) * Li j (g x)) l
      (𝓝 (Li k a - log a * Li j a)) :=
  (tendsto_Li_comp hk ha hg hgs).sub
    ((((continuousAt_log ha0).tendsto).comp hg).mul (tendsto_Li_comp hj ha hg hgs))

/-- `Li k f - log f · Li j f → 0` along `f → 0` inside `[-1, 1]`. -/
theorem tendsto_Li_sub_log_mul_Li_comp_zero {α : Type*} {l : Filter α} {k j : ℕ} (hk : 2 ≤ k)
    (hj : 2 ≤ j) {g : α → ℝ} (hg : Tendsto g l (𝓝 0)) (hgs : ∀ᶠ x in l, g x ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun x => Li k (g x) - log (g x) * Li j (g x)) l (𝓝 0) := by
  have h := (tendsto_Li_comp hk (by norm_num) hg hgs).sub
    (tendsto_log_mul_Li_comp hj hg (hgs.mono fun x hx => abs_le.2 hx))
  simpa using h

/-- `g log² x → 0` at `0⁺` when `|g x| ≤ C x` eventually. -/
theorem tendsto_mul_log_sq_of_abs_le {g : ℝ → ℝ} {C : ℝ}
    (hb : ∀ᶠ x in 𝓝[>] (0 : ℝ), |g x| ≤ C * x) :
    Tendsto (fun x => g x * log x ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_mul_log_sq_zero.abs).const_mul |C|
  rw [abs_zero, mul_zero] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [hb, self_mem_nhdsWithin] with x hx (hx0 : 0 < x)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hx0]
  calc |g x| * |log x ^ 2| ≤ C * x * |log x ^ 2| :=
        mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    _ = C * (x * |log x ^ 2|) := by ring
    _ ≤ |C| * (x * |log x ^ 2|) := mul_le_mul_of_nonneg_right (le_abs_self _)
        (mul_nonneg hx0.le (abs_nonneg _))

/-- `g log (1 - x) → 0` at `1⁻` when `|g x| ≤ C (1 - x)` eventually. -/
theorem tendsto_mul_log_one_sub_of_abs_le {g : ℝ → ℝ} {C : ℝ}
    (hb : ∀ᶠ x in 𝓝[<] (1 : ℝ), |g x| ≤ C * (1 - x)) :
    Tendsto (fun x => g x * log (1 - x)) (𝓝[<] 1) (𝓝 0) := by
  have h0 : Tendsto (fun x : ℝ => (1 - x) * log (1 - x)) (𝓝[<] 1) (𝓝 0) :=
    tendsto_mul_log_zero.comp tendsto_one_sub_nhdsLT_one
  have h := (h0.abs).const_mul |C|
  rw [abs_zero, mul_zero] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [hb, self_mem_nhdsWithin] with x hx (h1 : x < 1)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 - x)]
  calc |g x| * |log (1 - x)| ≤ C * (1 - x) * |log (1 - x)| :=
        mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    _ = C * ((1 - x) * |log (1 - x)|) := by ring
    _ ≤ |C| * ((1 - x) * |log (1 - x)|) := mul_le_mul_of_nonneg_right (le_abs_self _)
        (mul_nonneg (by linarith) (abs_nonneg _))

/-- `|log ((1 + x)/2)| ≤ 1 - x` for `0 ≤ x ≤ 1`. -/
theorem abs_log_one_add_div_two_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    |log ((1 + x) / 2)| ≤ 1 - x := by
  have hp : 0 < (1 + x) / 2 := by linarith
  have hle : log ((1 + x) / 2) ≤ 0 := log_nonpos hp.le (by linarith)
  have hge := Real.one_sub_inv_le_log_of_pos hp
  rw [abs_of_nonpos hle]
  have : 1 - ((1 + x) / 2)⁻¹ = (x - 1) / (1 + x) := by field_simp; ring
  rw [this] at hge
  have : (x - 1) / (1 + x) ≥ x - 1 := by
    rw [ge_iff_le, le_div_iff₀ (by linarith)]
    nlinarith
  linarith

/-- `|log (1 - x)| ≤ 2x` for `0 ≤ x ≤ 1/2`. -/
theorem abs_log_one_sub_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : |log (1 - x)| ≤ 2 * x := by
  have hp : 0 < 1 - x := by linarith
  have hle : log (1 - x) ≤ 0 := log_nonpos hp.le (by linarith)
  have hge := Real.one_sub_inv_le_log_of_pos hp
  rw [abs_of_nonpos hle]
  have : 1 - (1 - x)⁻¹ = -(x / (1 - x)) := by field_simp; ring
  rw [this] at hge
  have : x / (1 - x) ≤ 2 * x := by
    rw [div_le_iff₀ hp]
    nlinarith
  linarith

/-- `|log (1 + x)| ≤ x` for `0 ≤ x`. -/
theorem abs_log_one_add_le {x : ℝ} (h0 : 0 ≤ x) : |log (1 + x)| ≤ x := by
  have hp : 0 < 1 + x := by linarith
  rw [abs_of_nonneg (log_nonneg (by linarith))]
  have := Real.log_le_sub_one_of_pos hp
  linarith

/-- `log (1 - x) log² x → 0` at `0⁺`. -/
theorem tendsto_log_one_sub_mul_log_sq :
    Tendsto (fun x : ℝ => log (1 - x) * log x ^ 2) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_mul_log_sq_of_abs_le (C := 2) ?_
  have : Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  filter_upwards [this] with x hx
  exact abs_log_one_sub_le hx.1.le hx.2.le

/-- `log (1 + x) log² x → 0` at `0⁺`. -/
theorem tendsto_log_one_add_mul_log_sq :
    Tendsto (fun x : ℝ => log (1 + x) * log x ^ 2) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_mul_log_sq_of_abs_le (C := 1) ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  rw [one_mul]
  exact abs_log_one_add_le hx.le

end QED.Polylog
