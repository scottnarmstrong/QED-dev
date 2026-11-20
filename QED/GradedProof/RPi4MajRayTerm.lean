/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# (R-Π₄) step L10: the large-`s` tool for parametric terms along a ray

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10. Along the ray
`k = √s v` (`v·v = 1`) the second Symanzik remainder of the eight-line data is
`V = V₀ + s B` with `V₀ ≥ c > 0` (masses) and `B ≥ 0` (`QED.Integration.TwoLoop.remainder_nonneg`,
`QED.Integration.symanzikV_smul_add_smul`), and the parametric numerators are polynomials in `√s`
of degree at most `4`. This file bounds one monomial
`φⱼ(s) = (√s)ʲ / (V₀ + s B)ⁿ` and its integrals against a coefficient `π`, for `s ≥ 1`:
`O(s)` and increments `O(s - s')`, with the weight
`ω = 1 / cⁿ` (`j ≤ 2`), `1 / (c^{n-1} √(c B))` (`j = 3`), `1 / (c^{n-1} B)` (`j = 4`).
For `j ≥ 3` one power of `s` is absorbed by `B` (`V ≥ s B`, `V ≥ √(c s B)`), so the coefficient
must be integrable against `B^{-1/2}`, resp. `B^{-1}`: the numerator must vanish where `B = 0`.

* `maj_pow_sub_pow_le`: `xⁿ - yⁿ ≤ n x^{n-1} (x - y)` for `0 ≤ y ≤ x`;
* `maj_inv_pow_sub_le`: `1/V'ⁿ - 1/Vⁿ ≤ n (V - V') / (V V'ⁿ)` for `0 < V' ≤ V`;
* `maj_phi_le`, `maj_phi_sub_le`: the pointwise bounds, `j ≤ 4`;
* **`maj_integral_phi`**: `∫ π φⱼ(s)` is `O(s)` with increments `O(s - s')`, `s ≥ s' ≥ 1`.
-/

@[expose] public section

open MeasureTheory

namespace QED.GradedProof.RPi4

/-! ### Elementary inequalities -/

theorem maj_pow_sub_pow_le {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (n : ℕ) :
    x ^ (n + 1) - y ^ (n + 1) ≤ (n + 1) * x ^ n * (x - y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hx : 0 ≤ x := hy.trans hyx
    have e : x ^ (n + 2) - y ^ (n + 2) = x * (x ^ (n + 1) - y ^ (n + 1)) + (x - y) * y ^ (n + 1) :=
      by ring
    have h1 : x * (x ^ (n + 1) - y ^ (n + 1)) ≤ x * ((n + 1) * x ^ n * (x - y)) :=
      mul_le_mul_of_nonneg_left ih hx
    have h2 : (x - y) * y ^ (n + 1) ≤ (x - y) * x ^ (n + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hyx _) (by linarith)
    have h1' : x * ((n + 1) * x ^ n * (x - y)) = (n + 1) * x ^ (n + 1) * (x - y) := by ring
    rw [e]
    push_cast
    linarith

/-- `1/V'ⁿ - 1/Vⁿ ≤ n (V - V') / (V V'ⁿ)` for `0 < V' ≤ V`. -/
theorem maj_inv_pow_sub_le {V V' : ℝ} (hV' : 0 < V') (hVV : V' ≤ V) (n : ℕ) :
    1 / V' ^ n - 1 / V ^ n ≤ n * (V - V') / (V * V' ^ n) := by
  have hV : 0 < V := hV'.trans_le hVV
  rcases n with _ | n
  · simp
  have h := maj_pow_sub_pow_le hV'.le hVV n
  rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
    (by positivity)]
  have e : (1 * V ^ (n + 1) - V' ^ (n + 1) * 1) * (V * V' ^ (n + 1)) =
      (V ^ (n + 1) - V' ^ (n + 1)) * (V * V' ^ (n + 1)) := by ring
  rw [e]
  calc (V ^ (n + 1) - V' ^ (n + 1)) * (V * V' ^ (n + 1))
      ≤ ((n + 1) * V ^ n * (V - V')) * (V * V' ^ (n + 1)) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = ((n + 1 : ℕ) : ℝ) * (V - V') * (V' ^ (n + 1) * V ^ (n + 1)) := by
        push_cast
        ring

/-! ### The monomial along the ray -/

/-- The monomial `(√s)ʲ / (V₀ + s B)ⁿ`. -/
noncomputable def majPhi (j n : ℕ) (V₀ B s : ℝ) : ℝ := Real.sqrt s ^ j / (V₀ + s * B) ^ n

/-- The weight of the monomial: `1/cⁿ` (`j ≤ 2`), `1/(c^{n-1} √(c B))` (`j = 3`),
`1/(c^{n-1} B)` (`j ≥ 4`). -/
noncomputable def majOmega (j n : ℕ) (c B : ℝ) : ℝ :=
  if j ≤ 2 then 1 / c ^ n else if j = 3 then 1 / (c ^ (n - 1) * Real.sqrt (c * B))
  else 1 / (c ^ (n - 1) * B)

section Pointwise

variable {c V₀ B : ℝ} (hc : 0 < c) (hV₀ : c ≤ V₀) (hB : 0 ≤ B)
include hc hV₀ hB

theorem maj_V_pos {s : ℝ} (hs : 0 ≤ s) : 0 < V₀ + s * B := by
  have := mul_nonneg hs hB
  linarith

/-- `Vⁿ ≥ c^{n-1} V` for `n ≥ 1`. -/
theorem maj_V_pow_ge {s : ℝ} (hs : 0 ≤ s) {n : ℕ} (hn : 1 ≤ n) :
    c ^ (n - 1) * (V₀ + s * B) ≤ (V₀ + s * B) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hcV : c ≤ V₀ + s * B := by nlinarith [mul_nonneg hs hB]
  rw [show m + 1 - 1 = m by omega, pow_succ]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc.le hcV m) (maj_V_pos hc hV₀ hB hs).le

/-- `V ≥ √(c s B)`. -/
theorem maj_sqrt_le_V {s : ℝ} (hs : 0 ≤ s) : Real.sqrt (c * (s * B)) ≤ V₀ + s * B := by
  have hsB := mul_nonneg hs hB
  rw [Real.sqrt_le_left (maj_V_pos hc hV₀ hB hs).le]
  nlinarith

end Pointwise

theorem maj_phi_split {V V' : ℝ} (hV' : 0 < V') (hVV : V' ≤ V) (a : ℝ) {a' : ℝ} (ha' : 0 ≤ a')
    (n : ℕ) : |a / V ^ n - a' / V' ^ n| ≤ |a - a'| / V ^ n + a' * (1 / V' ^ n - 1 / V ^ n) := by
  have hV : 0 < V := hV'.trans_le hVV
  have hdb0 : 0 ≤ 1 / V' ^ n - 1 / V ^ n := by
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hV'.le hVV n)
  have e : a / V ^ n - a' / V' ^ n = (a - a') / V ^ n - a' * (1 / V' ^ n - 1 / V ^ n) := by
    field_simp
    ring
  rw [e]
  refine (abs_sub _ _).trans (add_le_add (le_of_eq ?_) (le_of_eq ?_))
  · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < V ^ n)]
  · exact abs_of_nonneg (mul_nonneg ha' hdb0)

/-- The second part of an increment: `a' (1/V'ⁿ - 1/Vⁿ) ≤ n (s - s') (a' B / V) / V'ⁿ`. -/
theorem maj_phi_second {V₀ B : ℝ} (hB : 0 ≤ B) {s s' a' : ℝ} (hV' : 0 < V₀ + s' * B)
    (hss : s' ≤ s) (ha' : 0 ≤ a') (n : ℕ) :
    a' * (1 / (V₀ + s' * B) ^ n - 1 / (V₀ + s * B) ^ n) ≤
      n * (s - s') * (B / (V₀ + s * B)) * a' / (V₀ + s' * B) ^ n := by
  have hVV : V₀ + s' * B ≤ V₀ + s * B := by nlinarith
  have hV : 0 < V₀ + s * B := hV'.trans_le hVV
  have h := mul_le_mul_of_nonneg_left (maj_inv_pow_sub_le hV' hVV n) ha'
  refine h.trans (le_of_eq ?_)
  field_simp
  ring

section Cases

variable {c V₀ B : ℝ} (hc : 0 < c) (hV₀ : c ≤ V₀) (hB : 0 ≤ B) {n : ℕ} (hn : 1 ≤ n)
  {s s' : ℝ} (hs' : 1 ≤ s') (hss : s' ≤ s)
include hc hV₀ hB hn hs' hss

theorem maj_phi_bounds_le2 {j : ℕ} (hj : j ≤ 2) :
    majPhi j n V₀ B s ≤ s * (1 / c ^ n) ∧
      |majPhi j n V₀ B s - majPhi j n V₀ B s'| ≤ (4 + n) * (1 / c ^ n) * (s - s') := by
  have hs : 1 ≤ s := hs'.trans hss
  have hs0 : 0 ≤ s := by linarith
  have hs0' : 0 ≤ s' := by linarith
  have hd : 0 ≤ s - s' := by linarith
  have hV'p : 0 < V₀ + s' * B := maj_V_pos hc hV₀ hB hs0'
  have hVp : 0 < V₀ + s * B := maj_V_pos hc hV₀ hB hs0
  have hVV : V₀ + s' * B ≤ V₀ + s * B := by nlinarith
  have hcn : c ^ n ≤ (V₀ + s * B) ^ n := pow_le_pow_left₀ hc.le (by nlinarith) n
  have hcn' : c ^ n ≤ (V₀ + s' * B) ^ n := pow_le_pow_left₀ hc.le (by nlinarith) n
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0
  have hsq' : Real.sqrt s' ^ 2 = s' := Real.sq_sqrt hs0'
  have hr1 : 1 ≤ Real.sqrt s' := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hs'
  have hrr : Real.sqrt s' ≤ Real.sqrt s := Real.sqrt_le_sqrt hss
  have hdr : Real.sqrt s - Real.sqrt s' ≤ s - s' := by
    have e : (Real.sqrt s - Real.sqrt s') * (Real.sqrt s + Real.sqrt s') = s - s' := by
      linear_combination hsq - hsq'
    nlinarith
  have ha : ∀ t : ℝ, 1 ≤ t → Real.sqrt t ^ j ≤ t := fun t ht => by
    have h1 : 1 ≤ Real.sqrt t := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt ht
    calc Real.sqrt t ^ j ≤ Real.sqrt t ^ 2 := pow_le_pow_right₀ h1 hj
      _ = t := Real.sq_sqrt (by linarith)
  have hda : |Real.sqrt s ^ j - Real.sqrt s' ^ j| ≤ s - s' := by
    interval_cases j
    · simpa using hd
    · rw [pow_one, pow_one, abs_of_nonneg (by linarith)]; exact hdr
    · rw [hsq, hsq', abs_of_nonneg hd]
  unfold majPhi
  refine ⟨?_, (maj_phi_split hV'p hVV _ (by positivity) n).trans ?_⟩
  · rw [div_le_iff₀ (pow_pos hVp n)]
    calc Real.sqrt s ^ j ≤ s := ha s hs
      _ = s * (1 / c ^ n) * c ^ n := by field_simp
      _ ≤ s * (1 / c ^ n) * (V₀ + s * B) ^ n := mul_le_mul_of_nonneg_left hcn (by positivity)
  have h1 : |Real.sqrt s ^ j - Real.sqrt s' ^ j| / (V₀ + s * B) ^ n ≤ (s - s') / c ^ n :=
    div_le_div₀ hd hda (by positivity) hcn
  have hBV : s' * B / (V₀ + s * B) ≤ 1 := by
    rw [div_le_one (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right hss hB]
  have h2 : Real.sqrt s' ^ j * (1 / (V₀ + s' * B) ^ n - 1 / (V₀ + s * B) ^ n) ≤
      n * (s - s') / c ^ n := by
    calc _ ≤ n * (s - s') * (B / (V₀ + s * B)) * Real.sqrt s' ^ j / (V₀ + s' * B) ^ n :=
          maj_phi_second hB hV'p hss (by positivity) n
      _ ≤ n * (s - s') * (B / (V₀ + s * B)) * s' / (V₀ + s' * B) ^ n := by
          refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (ha s' hs')
            (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hd) (div_nonneg hB hVp.le)))
            (pow_pos hV'p n).le
      _ = n * (s - s') * (s' * B / (V₀ + s * B)) / (V₀ + s' * B) ^ n := by ring
      _ ≤ n * (s - s') * 1 / c ^ n := by gcongr
      _ = n * (s - s') / c ^ n := by ring
  calc _ ≤ (s - s') / c ^ n + n * (s - s') / c ^ n := add_le_add h1 h2
    _ = (1 + n) * (1 / c ^ n) * (s - s') := by ring
    _ ≤ (4 + n) * (1 / c ^ n) * (s - s') := by gcongr; norm_num

theorem maj_phi_bounds_three (hBp : 0 < B) :
    majPhi 3 n V₀ B s ≤ s * (1 / (c ^ (n - 1) * Real.sqrt (c * B))) ∧
      |majPhi 3 n V₀ B s - majPhi 3 n V₀ B s'| ≤
        (4 + n) * (1 / (c ^ (n - 1) * Real.sqrt (c * B))) * (s - s') := by
  have hs : 1 ≤ s := hs'.trans hss
  have hs0 : 0 ≤ s := by linarith
  have hs0' : 0 ≤ s' := by linarith
  have hd : 0 ≤ s - s' := by linarith
  have hV'p : 0 < V₀ + s' * B := maj_V_pos hc hV₀ hB hs0'
  have hVp : 0 < V₀ + s * B := maj_V_pos hc hV₀ hB hs0
  have hVV : V₀ + s' * B ≤ V₀ + s * B := by nlinarith
  have hcn1 : 0 < c ^ (n - 1) := by positivity
  set q := Real.sqrt (c * B) with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr (by positivity)
  have hsqrt : ∀ t : ℝ, 0 ≤ t → Real.sqrt (c * (t * B)) = Real.sqrt t * q := fun t ht => by
    rw [hq, ← Real.sqrt_mul ht, show c * (t * B) = t * (c * B) by ring]
  have hden : c ^ (n - 1) * (Real.sqrt s * q) ≤ (V₀ + s * B) ^ n :=
    (mul_le_mul_of_nonneg_left ((hsqrt s hs0) ▸ maj_sqrt_le_V hc hV₀ hB hs0) hcn1.le).trans
      (maj_V_pow_ge hc hV₀ hB hs0 hn)
  have hden' : c ^ (n - 1) * (Real.sqrt s' * q) ≤ (V₀ + s' * B) ^ n :=
    (mul_le_mul_of_nonneg_left ((hsqrt s' hs0') ▸ maj_sqrt_le_V hc hV₀ hB hs0') hcn1.le).trans
      (maj_V_pow_ge hc hV₀ hB hs0' hn)
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0
  have hsq' : Real.sqrt s' ^ 2 = s' := Real.sq_sqrt hs0'
  have hr1 : 1 ≤ Real.sqrt s' := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hs'
  have hrr : Real.sqrt s' ≤ Real.sqrt s := Real.sqrt_le_sqrt hss
  have hr0 : 0 < Real.sqrt s := by linarith
  have hdr0 : 0 ≤ Real.sqrt s - Real.sqrt s' := by linarith
  have hc3 : Real.sqrt s ^ 3 = s * Real.sqrt s := by rw [pow_succ, hsq]
  have hc3' : Real.sqrt s' ^ 3 = s' * Real.sqrt s' := by rw [pow_succ, hsq']
  unfold majPhi
  refine ⟨?_, (maj_phi_split hV'p hVV _ (by positivity) n).trans ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    calc Real.sqrt s ^ 3 = s * (1 / (c ^ (n - 1) * q)) * (c ^ (n - 1) * (Real.sqrt s * q)) := by
          rw [hc3]; field_simp
      _ ≤ s * (1 / (c ^ (n - 1) * q)) * (V₀ + s * B) ^ n :=
          mul_le_mul_of_nonneg_left hden (by positivity)
  have hda : |Real.sqrt s ^ 3 - Real.sqrt s' ^ 3| ≤ 3 * Real.sqrt s * (s - s') := by
    have h3 : Real.sqrt s' ^ 3 ≤ Real.sqrt s ^ 3 := pow_le_pow_left₀ (by positivity) hrr 3
    rw [abs_of_nonneg (by linarith)]
    have e : Real.sqrt s ^ 3 - Real.sqrt s' ^ 3 = (Real.sqrt s - Real.sqrt s') *
        (Real.sqrt s ^ 2 + Real.sqrt s * Real.sqrt s' + Real.sqrt s' ^ 2) := by ring
    have hsum : Real.sqrt s ^ 2 + Real.sqrt s * Real.sqrt s' + Real.sqrt s' ^ 2 ≤
        3 * Real.sqrt s * (Real.sqrt s + Real.sqrt s') := by
      nlinarith [mul_le_mul_of_nonneg_left hrr (Real.sqrt_nonneg s),
        mul_le_mul_of_nonneg_left hrr (Real.sqrt_nonneg s')]
    have e2 : (Real.sqrt s - Real.sqrt s') * (Real.sqrt s + Real.sqrt s') = s - s' := by
      linear_combination hsq - hsq'
    rw [e]
    calc _ ≤ (Real.sqrt s - Real.sqrt s') * (3 * Real.sqrt s * (Real.sqrt s + Real.sqrt s')) :=
          mul_le_mul_of_nonneg_left hsum hdr0
      _ = 3 * Real.sqrt s * ((Real.sqrt s - Real.sqrt s') * (Real.sqrt s + Real.sqrt s')) := by
          ring
      _ = _ := by rw [e2]
  have h1 : |Real.sqrt s ^ 3 - Real.sqrt s' ^ 3| / (V₀ + s * B) ^ n ≤
      3 * (s - s') / (c ^ (n - 1) * q) := by
    calc _ ≤ 3 * Real.sqrt s * (s - s') / (c ^ (n - 1) * (Real.sqrt s * q)) :=
          div_le_div₀ (by positivity) hda (by positivity) hden
      _ = _ := by field_simp
  have hBV : s' * B / (V₀ + s * B) ≤ 1 := by
    rw [div_le_one hVp]
    nlinarith [mul_le_mul_of_nonneg_right hss hB]
  have h2 : Real.sqrt s' ^ 3 * (1 / (V₀ + s' * B) ^ n - 1 / (V₀ + s * B) ^ n) ≤
      n * (s - s') / (c ^ (n - 1) * q) := by
    calc _ ≤ n * (s - s') * (B / (V₀ + s * B)) * Real.sqrt s' ^ 3 / (V₀ + s' * B) ^ n :=
          maj_phi_second hB hV'p hss (by positivity) n
      _ = n * (s - s') * (s' * B / (V₀ + s * B)) * Real.sqrt s' / (V₀ + s' * B) ^ n := by
          rw [hc3']; ring
      _ ≤ n * (s - s') * 1 * Real.sqrt s' / (c ^ (n - 1) * (Real.sqrt s' * q)) := by
          gcongr
      _ = _ := by field_simp
  calc _ ≤ 3 * (s - s') / (c ^ (n - 1) * q) + n * (s - s') / (c ^ (n - 1) * q) :=
        add_le_add h1 h2
    _ = (3 + n) * (1 / (c ^ (n - 1) * q)) * (s - s') := by ring
    _ ≤ (4 + n) * (1 / (c ^ (n - 1) * q)) * (s - s') := by gcongr; norm_num

theorem maj_phi_bounds_four (hBp : 0 < B) :
    majPhi 4 n V₀ B s ≤ s * (1 / (c ^ (n - 1) * B)) ∧
      |majPhi 4 n V₀ B s - majPhi 4 n V₀ B s'| ≤ (4 + n) * (1 / (c ^ (n - 1) * B)) * (s - s') := by
  have hs : 1 ≤ s := hs'.trans hss
  have hs0 : 0 ≤ s := by linarith
  have hs0' : 0 ≤ s' := by linarith
  have hd : 0 ≤ s - s' := by linarith
  have hV'p : 0 < V₀ + s' * B := maj_V_pos hc hV₀ hB hs0'
  have hVp : 0 < V₀ + s * B := maj_V_pos hc hV₀ hB hs0
  have hVV : V₀ + s' * B ≤ V₀ + s * B := by nlinarith
  have hcn1 : 0 < c ^ (n - 1) := by positivity
  have hden : c ^ (n - 1) * (s * B) ≤ (V₀ + s * B) ^ n :=
    (mul_le_mul_of_nonneg_left (by linarith) hcn1.le).trans (maj_V_pow_ge hc hV₀ hB hs0 hn)
  have hden' : c ^ (n - 1) * (s' * B) ≤ (V₀ + s' * B) ^ n :=
    (mul_le_mul_of_nonneg_left (by linarith) hcn1.le).trans (maj_V_pow_ge hc hV₀ hB hs0' hn)
  have h4 : ∀ t : ℝ, 0 ≤ t → Real.sqrt t ^ 4 = t * t := fun t ht => by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt ht, sq]
  unfold majPhi
  rw [h4 s hs0, h4 s' hs0']
  refine ⟨?_, (maj_phi_split hV'p hVV _ (by positivity) n).trans ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    calc s * s = s * (1 / (c ^ (n - 1) * B)) * (c ^ (n - 1) * (s * B)) := by field_simp
      _ ≤ s * (1 / (c ^ (n - 1) * B)) * (V₀ + s * B) ^ n :=
          mul_le_mul_of_nonneg_left hden (by positivity)
  have h1 : |s * s - s' * s'| / (V₀ + s * B) ^ n ≤ 2 * (s - s') / (c ^ (n - 1) * B) := by
    rw [abs_of_nonneg (by nlinarith)]
    calc (s * s - s' * s') / (V₀ + s * B) ^ n ≤ 2 * s * (s - s') / (c ^ (n - 1) * (s * B)) :=
          div_le_div₀ (by positivity) (by nlinarith) (by positivity) hden
      _ = _ := by field_simp
  have hBV : s' * B / (V₀ + s * B) ≤ 1 := by
    rw [div_le_one hVp]
    nlinarith [mul_le_mul_of_nonneg_right hss hB]
  have h2 : s' * s' * (1 / (V₀ + s' * B) ^ n - 1 / (V₀ + s * B) ^ n) ≤
      n * (s - s') / (c ^ (n - 1) * B) := by
    calc _ ≤ n * (s - s') * (B / (V₀ + s * B)) * (s' * s') / (V₀ + s' * B) ^ n :=
          maj_phi_second hB hV'p hss (by positivity) n
      _ = n * (s - s') * (s' * B / (V₀ + s * B)) * s' / (V₀ + s' * B) ^ n := by ring
      _ ≤ n * (s - s') * 1 * s' / (c ^ (n - 1) * (s' * B)) := by gcongr
      _ = _ := by field_simp
  calc _ ≤ 2 * (s - s') / (c ^ (n - 1) * B) + n * (s - s') / (c ^ (n - 1) * B) :=
        add_le_add h1 h2
    _ = (2 + n) * (1 / (c ^ (n - 1) * B)) * (s - s') := by ring
    _ ≤ (4 + n) * (1 / (c ^ (n - 1) * B)) * (s - s') := by gcongr; norm_num

/-- **The pointwise bounds of the monomial**, `s ≥ s' ≥ 1`, `j ≤ 4`, `n ≥ 1`; for `j ≥ 3` also
`B > 0`. -/
theorem maj_phi_bounds {j : ℕ} (hj : j ≤ 4) (hBp : 3 ≤ j → 0 < B) :
    majPhi j n V₀ B s ≤ s * majOmega j n c B ∧
      |majPhi j n V₀ B s - majPhi j n V₀ B s'| ≤ (4 + n) * majOmega j n c B * (s - s') := by
  unfold majOmega
  split_ifs with h2 h3
  · exact maj_phi_bounds_le2 hc hV₀ hB hn hs' hss h2
  · subst h3
    exact maj_phi_bounds_three hc hV₀ hB hn hs' hss (hBp le_rfl)
  · obtain rfl : j = 4 := by omega
    exact maj_phi_bounds_four hc hV₀ hB hn hs' hss (hBp (by norm_num))

end Cases


/-! ### Integrals against a coefficient -/

section Integral

variable {ι : Type*} [MeasurableSpace ι] {μ : Measure ι}

/-- **The large-`s` tool for one monomial**: `∫ π φⱼ(s)` is `O(s)` with increments `O(s - s')`
for `s ≥ s' ≥ 1`, if `‖π‖ ω` is integrable (`ω = majOmega j n c B`). -/
theorem maj_integral_phi {c : ℝ} (hc : 0 < c) {V₀ B : ι → ℝ} {π : ι → ℂ} {j n : ℕ} (hj : j ≤ 4)
    (hn : 1 ≤ n) (hV₀ : ∀ᵐ x ∂μ, c ≤ V₀ x) (hB : ∀ᵐ x ∂μ, 0 ≤ B x)
    (hBp : 3 ≤ j → ∀ᵐ x ∂μ, 0 < B x)
    (hmeas : ∀ s : ℝ, AEStronglyMeasurable (fun x => π x * (majPhi j n (V₀ x) (B x) s : ℂ)) μ)
    (hint : Integrable (fun x => ‖π x‖ * majOmega j n c (B x)) μ) :
    ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s → ‖∫ x, π x * (majPhi j n (V₀ x) (B x) s : ℂ) ∂μ‖ ≤ C * s ∧
      ∀ s' : ℝ, 1 ≤ s' → s' ≤ s →
        ‖∫ x, π x * (majPhi j n (V₀ x) (B x) s : ℂ) ∂μ -
          ∫ x, π x * (majPhi j n (V₀ x) (B x) s' : ℂ) ∂μ‖ ≤ C * (s - s') := by
  set K : ℝ := (4 + n) * ∫ x, ‖π x‖ * majOmega j n c (B x) ∂μ with hK
  have hpt : ∀ᵐ x ∂μ, ∀ s s' : ℝ, 1 ≤ s' → s' ≤ s →
      majPhi j n (V₀ x) (B x) s ≤ s * majOmega j n c (B x) ∧
        |majPhi j n (V₀ x) (B x) s - majPhi j n (V₀ x) (B x) s'| ≤
          (4 + n) * majOmega j n c (B x) * (s - s') := by
    have hBp' : ∀ᵐ x ∂μ, 3 ≤ j → 0 < B x := by
      by_cases h3 : 3 ≤ j
      · filter_upwards [hBp h3] with x hx using fun _ => hx
      · exact Filter.Eventually.of_forall fun x h => absurd h h3
    filter_upwards [hV₀, hB, hBp'] with x h0 h1 h2
    exact fun s s' hs' hss => maj_phi_bounds hc h0 h1 hn hs' hss hj h2
  have hφ0 : ∀ᵐ x ∂μ, ∀ s : ℝ, 0 ≤ s → 0 ≤ majPhi j n (V₀ x) (B x) s := by
    filter_upwards [hV₀, hB] with x h0 h1
    intro s hs
    unfold majPhi
    exact div_nonneg (by positivity) (pow_nonneg (maj_V_pos hc h0 h1 hs).le n)
  have hω0 : ∀ᵐ x ∂μ, 0 ≤ majOmega j n c (B x) := by
    filter_upwards [hB] with x h1
    unfold majOmega
    split_ifs <;> positivity
  have hval : ∀ s : ℝ, 1 ≤ s → ∀ᵐ x ∂μ,
      ‖π x * (majPhi j n (V₀ x) (B x) s : ℂ)‖ ≤ s * (‖π x‖ * majOmega j n c (B x)) := by
    intro s hs
    filter_upwards [hpt, hφ0] with x hx hx0
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hx0 s (by linarith))]
    calc ‖π x‖ * majPhi j n (V₀ x) (B x) s ≤ ‖π x‖ * (s * majOmega j n c (B x)) :=
          mul_le_mul_of_nonneg_left (hx s s hs le_rfl).1 (norm_nonneg _)
      _ = _ := by ring
  have hI : ∀ s : ℝ, 1 ≤ s → Integrable (fun x => π x * (majPhi j n (V₀ x) (B x) s : ℂ)) μ :=
    fun s hs => (hint.const_mul s).mono' (hmeas s) (hval s hs)
  have hK0 : 0 ≤ ∫ x, ‖π x‖ * majOmega j n c (B x) ∂μ := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hω0] with x hx using mul_nonneg (norm_nonneg _) hx
  refine ⟨K, fun s hs => ⟨?_, fun s' hs' hss => ?_⟩⟩
  · refine (norm_integral_le_of_norm_le (hint.const_mul s) (hval s hs)).trans ?_
    rw [integral_const_mul, hK]
    have h4 : (1 : ℝ) ≤ 4 + n := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    nlinarith [mul_le_mul_of_nonneg_right h4 (mul_nonneg hK0 (by linarith : (0 : ℝ) ≤ s))]
  · rw [← integral_sub (hI s (hs'.trans hss)) (hI s' hs')]
    have hb : ∀ᵐ x ∂μ, ‖π x * (majPhi j n (V₀ x) (B x) s : ℂ) -
        π x * (majPhi j n (V₀ x) (B x) s' : ℂ)‖ ≤
          ((4 + n) * (s - s')) * (‖π x‖ * majOmega j n c (B x)) := by
      filter_upwards [hpt] with x hx
      rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      calc ‖π x‖ * |majPhi j n (V₀ x) (B x) s - majPhi j n (V₀ x) (B x) s'|
          ≤ ‖π x‖ * ((4 + n) * majOmega j n c (B x) * (s - s')) :=
            mul_le_mul_of_nonneg_left (hx s s' hs' hss).2 (norm_nonneg _)
        _ = _ := by ring
    refine (norm_integral_le_of_norm_le (hint.const_mul _) hb).trans (le_of_eq ?_)
    rw [integral_const_mul, hK]
    ring

end Integral

end QED.GradedProof.RPi4

end
