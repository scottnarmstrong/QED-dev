/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLValues
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import QED.Polylog.LiCalculus

/-!
# `Li_k(1/2)` as a harmonic polylogarithm at `1`

`H(-1, 1, …, 1; 1) = Li_{j+1}(1/2)` (with `j` ones), for every `j`. In particular
`H(-1, 1, 1, 1; 1) = Li₄(1/2)` and `H(-1, 1, 1, 1, 1; 1) = Li₅(1/2)`, the weight-4 and weight-5
constants of the closed forms of `A₁⁽⁶⁾`.

The proof is the closed form on `(0, 1)`, with `a = (1 - x)/2`,
`H(-1, 1ʲ; x) = Li_{j+1}(1/2) - ∑_{i=0}^{j} H(1^{j-i}; x) Li_{i+1}(a)`,
verified by differentiation: the sum `T(p, m) = ∑_{i=0}^{p} H(1^{p-i}; x) Li_{m+i+1}(a)`
satisfies `T(p, m)' = -H(1ᵖ; x) Li_m(a) / (1 - x)` (by induction on `p`), and
`Li₀(a) / (1 - x) = 1 / (1 + x)`.

## Main results

* `QED.Polylog.HPL.hpl_negOne_replicate_one_at_one`: `H(-1, 1ʲ; 1) = Li_{j+1}(1/2)`.
* `QED.Polylog.HPL.hpl_negOne_one_one_one_at_one`: `H(-1, 1, 1, 1; 1) = Li₄(1/2)`.
* `QED.Polylog.HPL.hpl_negOne_one_one_one_one_at_one`: `H(-1, 1, 1, 1, 1; 1) = Li₅(1/2)`.
-/

@[expose] public section

open Real Set Filter Topology

namespace QED.Polylog.HPL

open Letter

/-- `Li₀(y) = y / (1 - y)` for `0 ≤ y < 1`. -/
theorem Li_zero_eq_div {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) : Li 0 y = y / (1 - y) := by
  have h := (hasSum_geometric_of_lt_one h0 h1).mul_left y
  simp only [Li, pow_zero, div_one]
  rw [show (fun n : ℕ => y ^ (n + 1)) = fun n => y * y ^ n from funext fun n => pow_succ' y n,
    h.tsum_eq, div_eq_mul_inv]

/-- The pieces `T(p, m)(x) = ∑_{i=0}^{p} H(1^{p-i}; x) Li_{m+i+1}((1 - x)/2)`. -/
noncomputable def liHalfT : ℕ → ℕ → ℝ → ℝ
  | 0, m, x => Li (m + 1) ((1 - x) / 2)
  | p + 1, m, x => hpl (List.replicate (p + 1) one) x * Li (m + 1) ((1 - x) / 2) +
      liHalfT p (m + 1) x

theorem hasDerivAt_Li_half (m : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => Li (m + 1) ((1 - x) / 2)) (-(Li m ((1 - x) / 2) / (1 - x))) x := by
  have ha0 : (1 - x) / 2 ≠ 0 := by linarith [hx.2]
  have ha1 : |(1 - x) / 2| < 1 := by
    rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
  have h := (hasDerivAt_Li (k := m + 1) (by omega) ha1 ha0).comp x
    (((hasDerivAt_id x).const_sub 1).div_const 2)
  rw [Nat.add_sub_cancel] at h
  have e : (fun x => Li (m + 1) ((1 - x) / 2)) = Li (m + 1) ∘ fun x => (1 - id x) / 2 := rfl
  rw [e]
  refine h.congr_deriv ?_
  have : (1 - x) ≠ 0 := by linarith [hx.2]
  field_simp

theorem hasDerivAt_liHalfT : ∀ (p m : ℕ) {x : ℝ}, x ∈ Ioo (0 : ℝ) 1 →
    HasDerivAt (liHalfT p m)
      (-(hpl (List.replicate p one) x * Li m ((1 - x) / 2) / (1 - x))) x
  | 0, m, x, hx => by
    simpa [liHalfT] using hasDerivAt_Li_half m hx
  | p + 1, m, x, hx => by
    have h1 := hasDerivAt_hpl_cons one (List.replicate p one) hx
    rw [← List.replicate_succ] at h1
    have h := (h1.mul (hasDerivAt_Li_half m hx)).add (hasDerivAt_liHalfT p (m + 1) hx)
    have e : liHalfT (p + 1) m = fun x => hpl (List.replicate (p + 1) one) x *
        Li (m + 1) ((1 - x) / 2) + liHalfT p (m + 1) x := rfl
    rw [e]
    convert h using 1
    have : (1 - x) ≠ 0 := by linarith [hx.2]
    simp only [kernel_one]
    field_simp
    ring

theorem continuousAt_Li_half (k : ℕ) : ContinuousAt (fun x : ℝ => Li (k + 1) ((1 - x) / 2)) 0 := by
  have h := (hasDerivAt_Li (k := k + 1) (by omega) (x := 1 / 2) (by norm_num [abs_of_pos])
    (by norm_num)).continuousAt
  have hc : ContinuousAt (fun x : ℝ => (1 - x) / 2) 0 := by fun_prop
  have : (1 - (0 : ℝ)) / 2 = 1 / 2 := by norm_num
  exact ContinuousAt.comp (g := Li (k + 1)) (by rwa [this]) hc

theorem tendsto_liHalfT_zero : ∀ p m : ℕ,
    Tendsto (liHalfT p m) (𝓝[>] 0) (𝓝 (Li (m + p + 1) (1 / 2)))
  | 0, m => by
    have h := tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ))
      (continuousAt_Li_half m).tendsto
    simpa [liHalfT] using h
  | p + 1, m => by
    have h0 : ¬AllZero (List.replicate (p + 1) one) := fun h => by
      have := h one (List.mem_replicate.2 ⟨by omega, rfl⟩)
      exact absurd this (by decide)
    have h1 := ((tendsto_hpl_zero h0).mul
      (tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ))
        (continuousAt_Li_half m).tendsto)).add
      (tendsto_liHalfT_zero p (m + 1))
    rw [zero_mul, zero_add, show m + 1 + p + 1 = m + (p + 1) + 1 by omega] at h1
    exact h1

/-- `|Li_k((1 - x)/2)| ≤ 1 - x` for `0 ≤ x < 1`, `k ≥ 1`. -/
theorem abs_Li_half_le {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    |Li k ((1 - x) / 2)| ≤ 1 - x := by
  have h := abs_Li_sub_le hk (x := (1 - x) / 2) (y := 0)
    (by rw [abs_le]; constructor <;> linarith) (by norm_num)
  have e : |(1 - x) / 2| = (1 - x) / 2 := abs_of_nonneg (by linarith)
  rw [Li_zero, sub_zero, sub_zero, e] at h
  linarith

theorem tendsto_hpl_mul_Li_half_one (p m : ℕ) :
    Tendsto (fun x => hpl (List.replicate p one) x * Li (m + 1) ((1 - x) / 2)) (𝓝[<] 1)
      (𝓝 0) := by
  obtain ⟨C, hC, h⟩ := abs_hpl_le_one_sub_rpow (List.replicate p one) (ε := 1 / 2)
    (by norm_num)
  have hlim : Tendsto (fun x : ℝ => C * (1 - x) ^ (1 / 2 : ℝ)) (𝓝[<] 1) (𝓝 0) := by
    have : Tendsto (fun x : ℝ => C * (1 - x) ^ (1 / 2 : ℝ)) (𝓝 1) (𝓝 (C * (1 - 1) ^ (1 / 2 : ℝ)))
      := by
      refine tendsto_const_nhds.mul ?_
      exact ((tendsto_const_nhds.sub tendsto_id).rpow_const (Or.inr (by norm_num)))
    rw [sub_self, zero_rpow (by norm_num), mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Ico_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with x hx
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  rw [Real.norm_eq_abs, abs_mul]
  calc |hpl (List.replicate p one) x| * |Li (m + 1) ((1 - x) / 2)| ≤
        (C * (1 - x) ^ (-(1 / 2) : ℝ)) * (1 - x) :=
        mul_le_mul (h x hx) (abs_Li_half_le (by omega) (by linarith [hx.1]) hx.2)
          (abs_nonneg _) (mul_nonneg hC (rpow_nonneg hx1.le _))
    _ = C * ((1 - x) ^ (-(1 / 2) : ℝ) * (1 - x) ^ (1 : ℝ)) := by rw [rpow_one]; ring
    _ = C * (1 - x) ^ (1 / 2 : ℝ) := by rw [← rpow_add hx1]; norm_num

theorem tendsto_liHalfT_one : ∀ p m : ℕ, Tendsto (liHalfT p m) (𝓝[<] 1) (𝓝 0)
  | 0, m => by simpa [liHalfT] using tendsto_hpl_mul_Li_half_one 0 m
  | p + 1, m => by
    have h := (tendsto_hpl_mul_Li_half_one (p + 1) m).add (tendsto_liHalfT_one p (m + 1))
    rw [add_zero] at h
    exact h

/-- The closed form `H(-1, 1ʲ; x) = Li_{j+1}(1/2) - T(j, 0)(x)` on `(0, 1)`. -/
theorem hpl_negOne_replicate_one (j : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl (negOne :: List.replicate j one) x = Li (j + 1) (1 / 2) - liHalfT j 0 x := by
  refine eq_hpl_cons_of_hasDerivAt (F := fun x => Li (j + 1) (1 / 2) - liHalfT j 0 x)
    (fun h => absurd (h negOne List.mem_cons_self) (by decide)) (fun x hx => ?_) ?_ x hx
  · have h := (hasDerivAt_liHalfT j 0 hx).const_sub (Li (j + 1) (1 / 2))
    convert h using 1
    have hx1 : (1 - x) ≠ 0 := by linarith [hx.2]
    have hx2 : (1 + x) ≠ 0 := by linarith [hx.1]
    have key : (1 - x) / 2 / (1 - (1 - x) / 2) / (1 - x) = (1 + x)⁻¹ := by
      rw [show (1 : ℝ) - (1 - x) / 2 = (1 + x) / 2 by ring]
      field_simp
    rw [Li_zero_eq_div (by linarith [hx.2]) (by linarith [hx.1]), kernel_negOne, neg_neg,
      mul_div_assoc, key, mul_comm]
  · have h := (tendsto_liHalfT_zero j 0).const_sub (Li (j + 1) (1 / 2))
    rw [zero_add, sub_self] at h
    exact h

/-- **`H(-1, 1ʲ; 1) = Li_{j+1}(1/2)`.** -/
theorem hpl_negOne_replicate_one_at_one (j : ℕ) :
    hpl (negOne :: List.replicate j one) 1 = Li (j + 1) (1 / 2) := by
  have h := (tendsto_liHalfT_one j 0).const_sub (Li (j + 1) (1 / 2))
  rw [sub_zero] at h
  exact hpl_one_eq_of_tendsto (by decide) (fun x hx => hpl_negOne_replicate_one j hx) h

/-- `H(-1, 1, 1, 1; 1) = Li₄(1/2)`. -/
theorem hpl_negOne_one_one_one_at_one : hpl [negOne, one, one, one] 1 = Li 4 (1 / 2) :=
  hpl_negOne_replicate_one_at_one 3

/-- `H(-1, 1, 1, 1, 1; 1) = Li₅(1/2)`. -/
theorem hpl_negOne_one_one_one_one_at_one :
    hpl [negOne, one, one, one, one] 1 = Li 5 (1 / 2) :=
  hpl_negOne_replicate_one_at_one 4

end QED.Polylog.HPL
