/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCLimitCMasters
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-!
# The corner unit C: a pointwise bound uniform in the photon mass

Section 6.4 of `docs/TWO-LOOP-UNITS.md`, the dominating function for stage 3 of the `S + C` link
(`QED.TwoLoop.UnitSCCorner.CornerMainLimit`; namespace `QED.TwoLoop.UnitSCCornerMain`). The
closed form `cornerGm λ λ` of the `b`-integral has large cancellations at small `Y = y₃ + y₄`, so
it is bounded through the master integrals it is made of (by definition of `cForm`):

`cornerGm = -c₀ log(M + β h)/h + a₀ I₄ + a₁ I₅ + a₂ I₆ + c₁ I₂ + c₂ I₃ + c₃ I₇`,

with `I_k = ∫_β^∞ K_k(b) db ≥ 0` (written out in `cForm`). From `M + b h ≥ √M √(b h)` each
kernel is at most a constant times `b^{-p}` (`p = 3/2, 5/2, 7/2`; `masterK4_le`, …), so `I_k` is
at most a constant times `β^{1-p}` (`hasIoiInt_le_rpow`, `master4_bounds`, …). With `M ≥ Y²/4`,
`h ≥ x`, `β ≥ g = y₃ (1 - Y)`, the coefficients bounded by `x`, `x g`, `x g²`, `1`, `g`, `g²` times
constants (continuous functions on the compact cube, `exists_bound_cube`) and
`|c₀ log(M + β h)/h| ≤ 7/(2Y)` (`abs_cForm_log_le`), this gives (`abs_cForm_le`,
`exists_abs_cornerGm_le`)

`|cornerGm λ λ y₃ y₄ x| ≤ C / ((y₃ + y₄) √x √(y₃ (1 - y₃ - y₄)))` (`cornerMaj`)

for all `λ² ≤ 1` (including `λ = 0`), on the open triangle and `0 < x < 1`. The dominating
function is integrable on the triangle times `(0, 1)` (in `(Y, ξ)` it is
`C / (Y √x √(Y ξ (1-Y)))`, against the area element `Y dY dξ`; see
`QED/TwoLoop/UnitSCCornerMain.lean`). The bound was checked numerically before the proof
(mpmath, 20 000 log-uniform points near every face of the cube, `λ ∈ [0, 1]`): the ratio
`|cornerGm λ λ| · (y₃ + y₄) √x √g` stayed below `0.16`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology

namespace QED.TwoLoop.UnitSCCornerMain

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink
open QED.TwoLoop.UnitSCReduce (cornerP1 cornerP2)

/-! ### Improper integrals bounded by powers -/

/-- `∫_{z > 0} C (z + β)^{-(q+1)} dz = C β^{-q}/q`. -/
theorem hasIoiInt_rpow_shift {β C q : ℝ} (hβ : 0 < β) (hq : 0 < q) :
    HasIoiInt (fun z => C * (z + β) ^ (-(q + 1))) (C * (β ^ (-q) / q)) := by
  have hd : ∀ a ∈ Ici β, HasDerivAt (fun a => -(C * (a ^ (-q) / q))) (C * a ^ (-(q + 1))) a :=
    fun a ha => by
      have ha' : 0 < a := lt_of_lt_of_le hβ ha
      have h1 := ((Real.hasDerivAt_rpow_const (p := -q) (Or.inl ha'.ne')).div_const q).const_mul
        C |>.neg
      refine h1.congr_deriv ?_
      have e : -q - 1 = -(q + 1) := by ring
      rw [e]
      field_simp
  have hk : (∀ a ∈ Ioi β, 0 ≤ C * a ^ (-(q + 1))) ∨ (∀ a ∈ Ioi β, C * a ^ (-(q + 1)) ≤ 0) := by
    rcases le_total 0 C with hC | hC
    · exact Or.inl fun a ha => mul_nonneg hC (rpow_nonneg (hβ.trans ha).le _)
    · exact Or.inr fun a ha => mul_nonpos_of_nonpos_of_nonneg hC (rpow_nonneg (hβ.trans ha).le _)
  have hl : Tendsto (fun a : ℝ => -(C * (a ^ (-q) / q))) atTop (𝓝 (-(C * (0 / q)))) :=
    (((tendsto_rpow_neg_atTop hq).div_const q).const_mul C).neg
  have := hasIoiInt_shift hd hk hl
  refine this.congr (fun z _ => rfl) ?_
  simp

/-- **An improper integral bounded by a power**: if `0 ≤ k(a) ≤ C a^{-(q+1)}` for `a > 0`, then
`0 ≤ ∫_{z > 0} k(z + β) dz ≤ C β^{-q}/q`. -/
theorem hasIoiInt_le_rpow {k : ℝ → ℝ} {β V C q : ℝ} (hV : HasIoiInt (fun z => k (z + β)) V)
    (hβ : 0 < β) (hq : 0 < q) (hk0 : ∀ a, 0 < a → 0 ≤ k a)
    (hk : ∀ a, 0 < a → k a ≤ C * a ^ (-(q + 1))) : 0 ≤ V ∧ V ≤ C * (β ^ (-q) / q) := by
  have hB := hasIoiInt_rpow_shift (C := C) hβ hq
  rw [← hV.2, ← hB.2]
  have hpos : ∀ z ∈ Ioi (0 : ℝ), 0 < z + β := fun z hz => by
    simp only [mem_Ioi] at hz; linarith
  refine ⟨setIntegral_nonneg measurableSet_Ioi fun z hz => hk0 _ (hpos z hz), ?_⟩
  exact setIntegral_mono_on hV.1 hB.1 measurableSet_Ioi fun z hz => hk _ (hpos z hz)

theorem rpow_neg_half_add_one {a : ℝ} (ha : 0 < a) :
    a ^ (-((1 / 2 : ℝ) + 1)) = (a * √a)⁻¹ := by
  rw [rpow_neg ha.le, rpow_add ha, rpow_one, sqrt_eq_rpow, mul_comm]

theorem rpow_neg_three_half_add_one {a : ℝ} (ha : 0 < a) :
    a ^ (-((3 / 2 : ℝ) + 1)) = (a ^ 2 * √a)⁻¹ := by
  rw [rpow_neg ha.le, show (3 / 2 : ℝ) + 1 = 1 / 2 + 2 by norm_num, rpow_add ha,
    sqrt_eq_rpow, mul_comm, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast]

theorem rpow_neg_five_half_add_one {a : ℝ} (ha : 0 < a) :
    a ^ (-((5 / 2 : ℝ) + 1)) = (a ^ 3 * √a)⁻¹ := by
  rw [rpow_neg ha.le, show (5 / 2 : ℝ) + 1 = 1 / 2 + 3 by norm_num, rpow_add ha,
    sqrt_eq_rpow, mul_comm, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, rpow_natCast]

theorem rpow_neg_half' {a : ℝ} (ha : 0 < a) : a ^ (-(1 / 2 : ℝ)) = (√a)⁻¹ := by
  rw [rpow_neg ha.le, sqrt_eq_rpow]

theorem rpow_neg_three_half' {a : ℝ} (ha : 0 < a) : a ^ (-(3 / 2 : ℝ)) = (a * √a)⁻¹ := by
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, rpow_neg_half_add_one ha]

theorem rpow_neg_five_half' {a : ℝ} (ha : 0 < a) : a ^ (-(5 / 2 : ℝ)) = (a ^ 2 * √a)⁻¹ := by
  rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, rpow_neg_three_half_add_one ha]

/-- `q = 1/2`: a kernel `≤ C/(a √a)` integrates to at most `2C/√β`. -/
theorem hasIoiInt_le_q1 {k : ℝ → ℝ} {β V C : ℝ} (hV : HasIoiInt (fun z => k (z + β)) V)
    (hβ : 0 < β) (hk0 : ∀ a, 0 < a → 0 ≤ k a) (hk : ∀ a, 0 < a → k a ≤ C * (a * √a)⁻¹) :
    0 ≤ V ∧ V ≤ C * (2 * (√β)⁻¹) := by
  have := hasIoiInt_le_rpow hV hβ (by norm_num : (0 : ℝ) < 1 / 2) hk0 fun a ha => by
    rw [rpow_neg_half_add_one ha]; exact hk a ha
  rw [rpow_neg_half' hβ] at this
  refine ⟨this.1, this.2.trans_eq ?_⟩
  ring

/-- `q = 3/2`: a kernel `≤ C/(a² √a)` integrates to at most `(2/3) C/(β √β)`. -/
theorem hasIoiInt_le_q3 {k : ℝ → ℝ} {β V C : ℝ} (hV : HasIoiInt (fun z => k (z + β)) V)
    (hβ : 0 < β) (hk0 : ∀ a, 0 < a → 0 ≤ k a) (hk : ∀ a, 0 < a → k a ≤ C * (a ^ 2 * √a)⁻¹) :
    0 ≤ V ∧ V ≤ C * (2 / 3 * (β * √β)⁻¹) := by
  have := hasIoiInt_le_rpow hV hβ (by norm_num : (0 : ℝ) < 3 / 2) hk0 fun a ha => by
    rw [rpow_neg_three_half_add_one ha]; exact hk a ha
  rw [rpow_neg_three_half' hβ] at this
  refine ⟨this.1, this.2.trans_eq ?_⟩
  ring

/-- `q = 5/2`: a kernel `≤ C/(a³ √a)` integrates to at most `(2/5) C/(β² √β)`. -/
theorem hasIoiInt_le_q5 {k : ℝ → ℝ} {β V C : ℝ} (hV : HasIoiInt (fun z => k (z + β)) V)
    (hβ : 0 < β) (hk0 : ∀ a, 0 < a → 0 ≤ k a) (hk : ∀ a, 0 < a → k a ≤ C * (a ^ 3 * √a)⁻¹) :
    0 ≤ V ∧ V ≤ C * (2 / 5 * (β ^ 2 * √β)⁻¹) := by
  have := hasIoiInt_le_rpow hV hβ (by norm_num : (0 : ℝ) < 5 / 2) hk0 fun a ha => by
    rw [rpow_neg_five_half_add_one ha]; exact hk a ha
  rw [rpow_neg_five_half' hβ] at this
  refine ⟨this.1, this.2.trans_eq ?_⟩
  ring

/-! ### The master kernels bounded by powers of `b` -/

section Kernels

variable {M h a : ℝ}

theorem sqrt_mul_sqrt_mul_sqrt_le (hM : 0 ≤ M) (hh : 0 ≤ h) (ha : 0 ≤ a) :
    √M * √h * √a ≤ M + a * h := by
  rw [← sqrt_mul hM, ← sqrt_mul (mul_nonneg hM hh), sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [mul_nonneg (mul_nonneg hM hh) ha, mul_nonneg ha hh, sq_nonneg M, sq_nonneg (a * h)]

theorem masterK4_le (hM : 0 < M) (hh : 0 < h) (ha : 0 < a) :
    masterK4 M h a ≤ (√M * (h * √h))⁻¹ * (a * √a)⁻¹ := by
  have h1 := sqrt_mul_sqrt_mul_sqrt_le hM.le hh.le ha.le
  have h2 : a * h ≤ M + a * h := by linarith
  rw [masterK4, ← mul_inv, one_div]
  refine inv_anti₀ (by positivity) ?_
  calc √M * (h * √h) * (a * √a) = (√M * √h * √a) * (a * h) := by ring
    _ ≤ (M + a * h) * (M + a * h) := mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = (M + a * h) ^ 2 := by ring

theorem masterK5_le (hM : 0 < M) (hh : 0 < h) (ha : 0 < a) :
    masterK5 M h a ≤ (√M * (h * √h))⁻¹ * (a ^ 2 * √a)⁻¹ := by
  have h1 := sqrt_mul_sqrt_mul_sqrt_le hM.le hh.le ha.le
  have h2 : a * h ≤ M + a * h := by linarith
  rw [masterK5, ← mul_inv, one_div]
  refine inv_anti₀ (by positivity) ?_
  calc √M * (h * √h) * (a ^ 2 * √a) = a * ((√M * √h * √a) * (a * h)) := by ring
    _ ≤ a * ((M + a * h) * (M + a * h)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (by positivity)) ha.le
    _ = a * (M + a * h) ^ 2 := by ring

theorem masterK6_le (hM : 0 < M) (hh : 0 < h) (ha : 0 < a) :
    masterK6 M h a ≤ (√M * (h * √h))⁻¹ * (a ^ 3 * √a)⁻¹ := by
  have h1 := sqrt_mul_sqrt_mul_sqrt_le hM.le hh.le ha.le
  have h2 : a * h ≤ M + a * h := by linarith
  rw [masterK6, ← mul_inv, one_div]
  refine inv_anti₀ (by positivity) ?_
  calc √M * (h * √h) * (a ^ 3 * √a) = a ^ 2 * ((√M * √h * √a) * (a * h)) := by ring
    _ ≤ a ^ 2 * ((M + a * h) * (M + a * h)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (by positivity)) (by positivity)
    _ = a ^ 2 * (M + a * h) ^ 2 := by ring

theorem masterK2_le (hM : 0 < M) (hh : 0 < h) (ha : 0 < a) :
    masterK2 M h a ≤ (√M * √h)⁻¹ * (a * √a)⁻¹ := by
  have h1 := sqrt_mul_sqrt_mul_sqrt_le hM.le hh.le ha.le
  rw [masterK2, ← mul_inv, one_div]
  refine inv_anti₀ (by positivity) ?_
  calc √M * √h * (a * √a) = a * (√M * √h * √a) := by ring
    _ ≤ a * (M + a * h) := mul_le_mul_of_nonneg_left h1 ha.le

theorem masterK3_le (hM : 0 < M) (hh : 0 < h) (ha : 0 < a) :
    masterK3 M h a ≤ (√M * √h)⁻¹ * (a ^ 2 * √a)⁻¹ := by
  have h1 := sqrt_mul_sqrt_mul_sqrt_le hM.le hh.le ha.le
  rw [masterK3, ← mul_inv, one_div]
  refine inv_anti₀ (by positivity) ?_
  calc √M * √h * (a ^ 2 * √a) = a ^ 2 * (√M * √h * √a) := by ring
    _ ≤ a ^ 2 * (M + a * h) := mul_le_mul_of_nonneg_left h1 (by positivity)

theorem masterK7_le (hM : 0 < M) (hh : 0 < h) (ha : 0 < a) :
    masterK7 M h a ≤ (√M * √h)⁻¹ * (a ^ 3 * √a)⁻¹ := by
  have h1 := sqrt_mul_sqrt_mul_sqrt_le hM.le hh.le ha.le
  rw [masterK7, ← mul_inv, one_div]
  refine inv_anti₀ (by positivity) ?_
  calc √M * √h * (a ^ 3 * √a) = a ^ 3 * (√M * √h * √a) := by ring
    _ ≤ a ^ 3 * (M + a * h) := mul_le_mul_of_nonneg_left h1 (by positivity)

end Kernels

/-! ### The six masters bounded by powers of `β` -/

section Masters

variable {M h β : ℝ}

theorem master4_bounds (hM : 0 < M) (hh : 0 < h) (hβ : 0 < β) :
    0 ≤ 1 / (h * (M + β * h)) ∧
      1 / (h * (M + β * h)) ≤ (√M * (h * √h))⁻¹ * (2 * (√β)⁻¹) :=
  hasIoiInt_le_q1 (hasIoiInt_master4 hM hh hβ) hβ
    (fun a ha => by unfold masterK4; positivity) fun a ha => masterK4_le hM hh ha

theorem master5_bounds (hM : 0 < M) (hh : 0 < h) (hβ : 0 < β) :
    0 ≤ log (1 + M / (β * h)) / M ^ 2 - 1 / (M * (M + β * h)) ∧
      log (1 + M / (β * h)) / M ^ 2 - 1 / (M * (M + β * h)) ≤
        (√M * (h * √h))⁻¹ * (2 / 3 * (β * √β)⁻¹) :=
  hasIoiInt_le_q3 (hasIoiInt_master5 hM hh hβ) hβ
    (fun a ha => by unfold masterK5; positivity) fun a ha => masterK5_le hM hh ha

theorem master6_bounds (hM : 0 < M) (hh : 0 < h) (hβ : 0 < β) :
    0 ≤ 1 / (M ^ 2 * β) - 2 * h * log (1 + M / (β * h)) / M ^ 3 + h / (M ^ 2 * (M + β * h)) ∧
      1 / (M ^ 2 * β) - 2 * h * log (1 + M / (β * h)) / M ^ 3 + h / (M ^ 2 * (M + β * h)) ≤
        (√M * (h * √h))⁻¹ * (2 / 5 * (β ^ 2 * √β)⁻¹) :=
  hasIoiInt_le_q5 (hasIoiInt_master6 hM hh hβ) hβ
    (fun a ha => by unfold masterK6; positivity) fun a ha => masterK6_le hM hh ha

theorem master2_bounds (hM : 0 < M) (hh : 0 < h) (hβ : 0 < β) :
    0 ≤ log (1 + M / (β * h)) / M ∧
      log (1 + M / (β * h)) / M ≤ (√M * √h)⁻¹ * (2 * (√β)⁻¹) :=
  hasIoiInt_le_q1 (hasIoiInt_master2 hM hh hβ) hβ
    (fun a ha => by unfold masterK2; positivity) fun a ha => masterK2_le hM hh ha

theorem master3_bounds (hM : 0 < M) (hh : 0 < h) (hβ : 0 < β) :
    0 ≤ 1 / (M * β) - h * log (1 + M / (β * h)) / M ^ 2 ∧
      1 / (M * β) - h * log (1 + M / (β * h)) / M ^ 2 ≤
        (√M * √h)⁻¹ * (2 / 3 * (β * √β)⁻¹) :=
  hasIoiInt_le_q3 (hasIoiInt_master3 hM hh hβ) hβ
    (fun a ha => by unfold masterK3; positivity) fun a ha => masterK3_le hM hh ha

theorem master7_bounds (hM : 0 < M) (hh : 0 < h) (hβ : 0 < β) :
    0 ≤ 1 / (2 * M * β ^ 2) - h / (M ^ 2 * β) + h ^ 2 * log (1 + M / (β * h)) / M ^ 3 ∧
      1 / (2 * M * β ^ 2) - h / (M ^ 2 * β) + h ^ 2 * log (1 + M / (β * h)) / M ^ 3 ≤
        (√M * √h)⁻¹ * (2 / 5 * (β ^ 2 * √β)⁻¹) :=
  hasIoiInt_le_q5 (hasIoiInt_master7 hM hh hβ) hβ
    (fun a ha => by unfold masterK7; positivity) fun a ha => masterK7_le hM hh ha

end Masters

/-! ### The bound on the closed form -/

theorem abs_mul_le_of_le {a V A B : ℝ} (h0 : 0 ≤ V) (hV : V ≤ B) (ha : |a| ≤ A) :
    |a * V| ≤ A * B := by
  rw [abs_mul, abs_of_nonneg h0]
  exact mul_le_mul ha hV h0 ((abs_nonneg a).trans ha)

/-- **The subtracted logarithm**: `|c₀ (-log(M + β h)/h)| ≤ 7/(2Y)` when `0 ≤ c₀ ≤ x/2`,
`c₀ β ≤ 1/2`, `x ≤ h`, `Y²/4 ≤ M ≤ 2`. -/
theorem abs_cForm_log_le {c₀ β h M Y x : ℝ} (hY : 0 < Y) (hY1 : Y ≤ 1) (hx : 0 < x)
    (hβ : 0 < β) (hxh : x ≤ h) (hM : Y ^ 2 / 4 ≤ M) (hM2 : M ≤ 2) (hc0 : 0 ≤ c₀)
    (hc0x : c₀ ≤ x / 2) (hc0β : c₀ * β ≤ 1 / 2) :
    |c₀ * (-log (M + β * h) / h)| ≤ 7 / 2 * Y⁻¹ := by
  have hh : 0 < h := hx.trans_le hxh
  have hY4 : 0 < Y ^ 2 / 4 := by positivity
  have hMp : 0 < M := hY4.trans_le hM
  set t := c₀ / h with ht
  have ht0 : 0 ≤ t := div_nonneg hc0 hh.le
  have ht1 : t ≤ 1 / 2 := by
    rw [ht, div_le_iff₀ hh]
    nlinarith
  have htβ : t * (β * h) = c₀ * β := by rw [ht]; field_simp
  set A := log (M + β * h) with hA
  have hAu : A ≤ M + β * h := by
    have := log_le_sub_one_of_pos (show 0 < M + β * h by positivity)
    linarith
  have hAl : -(4 / Y) ≤ A := by
    have h1 : log (Y ^ 2 / 4) ≤ A := log_le_log hY4 (by nlinarith [mul_pos hβ hh])
    have h2 : log (Y ^ 2 / 4) = 2 * log (Y / 2) := by
      rw [show Y ^ 2 / 4 = (Y / 2) ^ 2 by ring, log_pow]; push_cast; ring
    have h3 := one_sub_inv_le_log_of_pos (show 0 < Y / 2 by positivity)
    have h4 : (Y / 2)⁻¹ = 2 / Y := by field_simp
    rw [h4] at h3
    have h5 : 0 < 2 / Y := by positivity
    have h6 : 4 / Y = 2 * (2 / Y) := by ring
    rw [h6]
    linarith
  have e : c₀ * (-A / h) = -(t * A) := by rw [ht]; field_simp
  rw [e, abs_neg, abs_le]
  have hYi : 1 ≤ Y⁻¹ := one_le_inv₀ hY |>.mpr hY1
  have e4 : 4 / Y = 4 * Y⁻¹ := by rw [div_eq_mul_inv]
  rw [e4] at hAl
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hAl ht0, mul_nonneg ht0 (show 0 ≤ 4 * Y⁻¹ by positivity),
      mul_le_mul_of_nonneg_right ht1 (show 0 ≤ 4 * Y⁻¹ by positivity)]
  · have h1 : t * A ≤ t * (M + β * h) := mul_le_mul_of_nonneg_left hAu ht0
    have h2 : t * M ≤ 1 / 2 * 2 := mul_le_mul ht1 hM2 hMp.le (by norm_num)
    nlinarith

/-- **The bound on the closed form** `cForm` through the masters, for `M ≥ Y²/4`, `h ≥ x`,
`β ≥ g` and coefficients bounded by `x`, `x g`, `x g²`, `1`, `g`, `g²` times constants. -/
theorem abs_cForm_le {a₀ a₁ a₂ c₀ c₁ c₂ c₃ β h M Y x g K₀ K₁ K₂ K₃ K₄ K₅ : ℝ}
    (hY : 0 < Y) (hY1 : Y ≤ 1) (hx : 0 < x) (hx1 : x ≤ 1) (hg : 0 < g) (hg1 : g ≤ 1)
    (hgβ : g ≤ β) (hxh : x ≤ h) (hM : Y ^ 2 / 4 ≤ M) (hM2 : M ≤ 2) (hc0 : 0 ≤ c₀)
    (hc0x : c₀ ≤ x / 2) (hc0β : c₀ * β ≤ 1 / 2)
    (ha₀ : |a₀| ≤ x * K₀) (ha₁ : |a₁| ≤ x * g * K₁) (ha₂ : |a₂| ≤ x * g ^ 2 * K₂)
    (hc₁ : |c₁| ≤ K₃) (hc₂ : |c₂| ≤ g * K₄) (hc₃ : |c₃| ≤ g ^ 2 * K₅) :
    |cForm a₀ a₁ a₂ c₀ c₁ c₂ c₃ β h M (log (M + β * h)) (log (1 + M / (β * h)))| ≤
      (7 / 2 + 4 * K₀ + 4 / 3 * K₁ + 4 / 5 * K₂ + 4 * K₃ + 4 / 3 * K₄ + 4 / 5 * K₅) *
        (Y * √x * √g)⁻¹ := by
  have hβ : 0 < β := hg.trans_le hgβ
  have hh : 0 < h := hx.trans_le hxh
  have hY4 : 0 < Y ^ 2 / 4 := by positivity
  have hMp : 0 < M := hY4.trans_le hM
  have hsM : Y / 2 ≤ √M := by
    rw [show Y / 2 = √((Y / 2) ^ 2) from (sqrt_sq (by positivity)).symm]
    exact sqrt_le_sqrt (by linarith)
  have hsx : √x ≤ √h := sqrt_le_sqrt hxh
  have hsg : √g ≤ √β := sqrt_le_sqrt hgβ
  have hsx0 : 0 < √x := sqrt_pos.mpr hx
  have hsg0 : 0 < √g := sqrt_pos.mpr hg
  have hsx1 : √x ≤ 1 := sqrt_le_one.mpr hx1
  have hsg1 : √g ≤ 1 := sqrt_le_one.mpr hg1
  have hK₀ : 0 ≤ K₀ := nonneg_of_mul_nonneg_right ((abs_nonneg _).trans ha₀) hx
  have hK₁ : 0 ≤ K₁ := nonneg_of_mul_nonneg_right ((abs_nonneg _).trans ha₁) (by positivity)
  have hK₂ : 0 ≤ K₂ := nonneg_of_mul_nonneg_right ((abs_nonneg _).trans ha₂) (by positivity)
  have hK₃ : 0 ≤ K₃ := (abs_nonneg _).trans hc₁
  have hK₄ : 0 ≤ K₄ := nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hc₂) (by positivity)
  have hK₅ : 0 ≤ K₅ := nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hc₃) (by positivity)
  set W := (Y * √x * √g)⁻¹ with hW
  have hW0 : 0 ≤ W := by positivity
  have hYW : Y⁻¹ ≤ W := by
    rw [hW]
    refine inv_anti₀ (by positivity) ?_
    calc Y * √x * √g ≤ Y * 1 * 1 := by gcongr
      _ = Y := by ring
  obtain ⟨b4l, b4u⟩ := master4_bounds hMp hh hβ
  obtain ⟨b5l, b5u⟩ := master5_bounds hMp hh hβ
  obtain ⟨b6l, b6u⟩ := master6_bounds hMp hh hβ
  obtain ⟨b2l, b2u⟩ := master2_bounds hMp hh hβ
  obtain ⟨b3l, b3u⟩ := master3_bounds hMp hh hβ
  obtain ⟨b7l, b7u⟩ := master7_bounds hMp hh hβ
  have t0 := abs_cForm_log_le hY hY1 hx hβ hxh hM hM2 hc0 hc0x hc0β
  have t4 := abs_mul_le_of_le b4l b4u ha₀
  have t5 := abs_mul_le_of_le b5l b5u ha₁
  have t6 := abs_mul_le_of_le b6l b6u ha₂
  have t2 := abs_mul_le_of_le b2l b2u hc₁
  have t3 := abs_mul_le_of_le b3l b3u hc₂
  have t7 := abs_mul_le_of_le b7l b7u hc₃
  have s4 : x * K₀ * ((√M * (h * √h))⁻¹ * (2 * (√β)⁻¹)) ≤ 4 * K₀ * W := by
    calc x * K₀ * ((√M * (h * √h))⁻¹ * (2 * (√β)⁻¹)) ≤
        x * K₀ * ((Y / 2 * (x * √x))⁻¹ * (2 * (√g)⁻¹)) := by gcongr
      _ = 4 * K₀ * W := by rw [hW]; field_simp; ring
  have s5 : x * g * K₁ * ((√M * (h * √h))⁻¹ * (2 / 3 * (β * √β)⁻¹)) ≤ 4 / 3 * K₁ * W := by
    calc x * g * K₁ * ((√M * (h * √h))⁻¹ * (2 / 3 * (β * √β)⁻¹)) ≤
        x * g * K₁ * ((Y / 2 * (x * √x))⁻¹ * (2 / 3 * (g * √g)⁻¹)) := by gcongr
      _ = 4 / 3 * K₁ * W := by rw [hW]; field_simp; ring
  have s6 : x * g ^ 2 * K₂ * ((√M * (h * √h))⁻¹ * (2 / 5 * (β ^ 2 * √β)⁻¹)) ≤
      4 / 5 * K₂ * W := by
    calc x * g ^ 2 * K₂ * ((√M * (h * √h))⁻¹ * (2 / 5 * (β ^ 2 * √β)⁻¹)) ≤
        x * g ^ 2 * K₂ * ((Y / 2 * (x * √x))⁻¹ * (2 / 5 * (g ^ 2 * √g)⁻¹)) := by gcongr
      _ = 4 / 5 * K₂ * W := by rw [hW]; field_simp; ring
  have s2 : K₃ * ((√M * √h)⁻¹ * (2 * (√β)⁻¹)) ≤ 4 * K₃ * W := by
    calc K₃ * ((√M * √h)⁻¹ * (2 * (√β)⁻¹)) ≤ K₃ * ((Y / 2 * √x)⁻¹ * (2 * (√g)⁻¹)) := by gcongr
      _ = 4 * K₃ * W := by rw [hW]; field_simp; ring
  have s3 : g * K₄ * ((√M * √h)⁻¹ * (2 / 3 * (β * √β)⁻¹)) ≤ 4 / 3 * K₄ * W := by
    calc g * K₄ * ((√M * √h)⁻¹ * (2 / 3 * (β * √β)⁻¹)) ≤
        g * K₄ * ((Y / 2 * √x)⁻¹ * (2 / 3 * (g * √g)⁻¹)) := by gcongr
      _ = 4 / 3 * K₄ * W := by rw [hW]; field_simp; ring
  have s7 : g ^ 2 * K₅ * ((√M * √h)⁻¹ * (2 / 5 * (β ^ 2 * √β)⁻¹)) ≤ 4 / 5 * K₅ * W := by
    calc g ^ 2 * K₅ * ((√M * √h)⁻¹ * (2 / 5 * (β ^ 2 * √β)⁻¹)) ≤
        g ^ 2 * K₅ * ((Y / 2 * √x)⁻¹ * (2 / 5 * (g ^ 2 * √g)⁻¹)) := by gcongr
      _ = 4 / 5 * K₅ * W := by rw [hW]; field_simp; ring
  unfold cForm
  set A := log (M + β * h)
  set L := log (1 + M / (β * h))
  have e0 : c₀ * (-A / h) = c₀ * (-log (M + β * h) / h) := rfl
  calc _ ≤ |c₀ * (-A / h)| + |a₀ * (1 / (h * (M + β * h)))| +
        |a₁ * (L / M ^ 2 - 1 / (M * (M + β * h)))| +
        |a₂ * (1 / (M ^ 2 * β) - 2 * h * L / M ^ 3 + h / (M ^ 2 * (M + β * h)))| +
        |c₁ * (L / M)| + |c₂ * (1 / (M * β) - h * L / M ^ 2)| +
        |c₃ * (1 / (2 * M * β ^ 2) - h / (M ^ 2 * β) + h ^ 2 * L / M ^ 3)| := by
          refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
          refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
          refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
          refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
          refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
          exact abs_add_le _ _
    _ ≤ _ := by linarith

/-! ### The corner integrand -/

/-- A continuous function is bounded on the cube `[0, 1]³`. -/
theorem exists_bound_cube {f : ℝ → ℝ → ℝ → ℝ}
    (hf : Continuous fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) :
    ∃ K, ∀ x y z, x ∈ Icc (0 : ℝ) 1 → y ∈ Icc (0 : ℝ) 1 → z ∈ Icc (0 : ℝ) 1 → |f x y z| ≤ K := by
  have hs : IsCompact (Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨K, hK⟩ := hs.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨K, fun x y z hx hy hz => by simpa [Real.norm_eq_abs] using hK (x, y, z) ⟨hx, hy, hz⟩⟩

theorem abs_mul_le_mul_of_abs_le {u f K : ℝ} (hu : 0 ≤ u) (hf : |f| ≤ K) : |u * f| ≤ u * K := by
  rw [abs_mul, abs_of_nonneg hu]
  exact mul_le_mul_of_nonneg_left hf hu

/-- **The dominating function** `1/((y₃ + y₄) √x √g)`, `g = y₃ (1 - y₃ - y₄)`. -/
noncomputable def cornerMaj (y3 y4 x : ℝ) : ℝ := ((y3 + y4) * √x * √(cornerG y3 y4))⁻¹

/-- **The pointwise bound, uniform in the photon mass**: there is `C` with
`|cornerGm λ λ y₃ y₄ x| ≤ C/((y₃ + y₄) √x √(y₃ (1 - y₃ - y₄)))` for every `λ² ≤ 1` (including
`λ = 0`), `(y₃, y₄)` in the open triangle and `0 < x < 1`. -/
theorem exists_abs_cornerGm_le : ∃ C : ℝ, ∀ lam y3 y4 x : ℝ, lam ^ 2 ≤ 1 → 0 < y3 → 0 < y4 →
    y3 + y4 < 1 → 0 < x → x < 1 → |cornerGm lam lam y3 y4 x| ≤ C * cornerMaj y3 y4 x := by
  obtain ⟨K₀, hK₀⟩ := exists_bound_cube (f := fun x y3 y4 => cornerP1 x y3 y4 / 4)
    (by unfold cornerP1; fun_prop)
  obtain ⟨K₁, hK₁⟩ := exists_bound_cube
    (f := fun x y3 y4 => (cornerQ x y3 - cornerP1 x y3 y4) / 4)
    (by unfold cornerP1 cornerQ; fun_prop)
  obtain ⟨K₂, hK₂⟩ := exists_bound_cube (f := fun x y3 _ => -(cornerQ x y3 / 4))
    (by unfold cornerQ; fun_prop)
  obtain ⟨K₃, hK₃⟩ := exists_bound_cube (f := fun x y3 y4 => cornerC1 x y3 y4)
    (by unfold cornerC1 cornerP2 cornerG; fun_prop)
  obtain ⟨K₄, hK₄⟩ := exists_bound_cube
    (f := fun x y3 y4 => x * (cornerR x y3 + cornerP2 x y3 y4) / 4)
    (by unfold cornerR cornerP2; fun_prop)
  obtain ⟨K₅, hK₅⟩ := exists_bound_cube (f := fun x y3 _ => -(x * cornerR x y3 / 4))
    (by unfold cornerR; fun_prop)
  refine ⟨7 / 2 + 4 * K₀ + 4 / 3 * K₁ + 4 / 5 * K₂ + 4 * K₃ + 4 / 3 * K₄ + 4 / 5 * K₅,
    fun lam y3 y4 x hl h3 h4 hY hx0 hx1 => ?_⟩
  have mx : x ∈ Icc (0 : ℝ) 1 := ⟨hx0.le, hx1.le⟩
  have m3 : y3 ∈ Icc (0 : ℝ) 1 := ⟨h3.le, by linarith⟩
  have m4 : y4 ∈ Icc (0 : ℝ) 1 := ⟨h4.le, by linarith⟩
  have hg : 0 < cornerG y3 y4 := by
    unfold cornerG; have : 0 < 1 - y3 - y4 := by linarith
    positivity
  have hg1 : cornerG y3 y4 ≤ 1 := by
    unfold cornerG; nlinarith
  have h1x : 0 < 1 - x := by linarith
  have hl0 : 0 ≤ lam ^ 2 := sq_nonneg lam
  have hxh : x ≤ ladderInnerMass 1 lam x / x := by
    rw [le_div_iff₀ hx0]; unfold ladderInnerMass; nlinarith [mul_nonneg h1x.le hl0]
  have hM : (y3 + y4) ^ 2 / 4 ≤ cornerMass lam lam y3 y4 := by
    unfold cornerMass
    nlinarith [mul_le_mul_of_nonneg_right hl (mul_pos h3 h4).le, sq_nonneg (y3 - y4),
      mul_nonneg (show 0 ≤ 1 - (y3 + y4) by linarith) hl0]
  have hM2 : cornerMass lam lam y3 y4 ≤ 2 := by
    unfold cornerMass
    nlinarith [mul_le_mul_of_nonneg_left hl (show 0 ≤ 1 - (y3 + y4) by linarith),
      mul_nonneg hl0 (mul_pos h3 h4).le]
  have hc0 : 0 ≤ cornerC0 x := by unfold cornerC0; positivity
  have hc0x : cornerC0 x ≤ x / 2 := by unfold cornerC0; nlinarith
  have hc0β : cornerC0 x * betaG (cornerG y3 y4) (y3 * y4) x ≤ 1 / 2 := by
    unfold betaG
    rw [mul_max_of_nonneg _ _ hc0]
    refine max_le ?_ ?_
    · unfold cornerC0
      have : x * (1 - x) ≤ 1 := by nlinarith
      have := mul_le_mul this hg1 hg.le zero_le_one
      nlinarith
    · unfold cornerC0
      have e : x * (1 - x) / 2 * (y3 * y4 * x / (1 - x)) = x ^ 2 * (y3 * y4) / 2 := by
        field_simp
      rw [e]
      have : y3 * y4 ≤ 1 := by nlinarith
      have : x ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul this (by assumption : y3 * y4 ≤ 1) (mul_pos h3 h4).le zero_le_one]
  have ha₀ : |cornerA0 x y3 y4| ≤ x * K₀ := by
    have := abs_mul_le_mul_of_abs_le hx0.le (hK₀ x y3 y4 mx m3 m4)
    rwa [show x * (cornerP1 x y3 y4 / 4) = cornerA0 x y3 y4 by unfold cornerA0; ring] at this
  have ha₁ : |cornerA1 x y3 y4| ≤ x * cornerG y3 y4 * K₁ := by
    have := abs_mul_le_mul_of_abs_le (mul_pos hx0 hg).le (hK₁ x y3 y4 mx m3 m4)
    rwa [show x * cornerG y3 y4 * ((cornerQ x y3 - cornerP1 x y3 y4) / 4) = cornerA1 x y3 y4 by
      unfold cornerA1; ring] at this
  have ha₂ : |cornerA2 x y3 y4| ≤ x * cornerG y3 y4 ^ 2 * K₂ := by
    have := abs_mul_le_mul_of_abs_le (by positivity : (0 : ℝ) ≤ x * cornerG y3 y4 ^ 2)
      (hK₂ x y3 y4 mx m3 m4)
    rwa [show x * cornerG y3 y4 ^ 2 * -(cornerQ x y3 / 4) = cornerA2 x y3 y4 by
      unfold cornerA2; ring] at this
  have hc₁ : |cornerC1 x y3 y4| ≤ K₃ := hK₃ x y3 y4 mx m3 m4
  have hc₂ : |cornerC2 x y3 y4| ≤ cornerG y3 y4 * K₄ := by
    have := abs_mul_le_mul_of_abs_le hg.le (hK₄ x y3 y4 mx m3 m4)
    rwa [show cornerG y3 y4 * (x * (cornerR x y3 + cornerP2 x y3 y4) / 4) = cornerC2 x y3 y4 by
      unfold cornerC2; ring] at this
  have hc₃ : |cornerC3 x y3 y4| ≤ cornerG y3 y4 ^ 2 * K₅ := by
    have := abs_mul_le_mul_of_abs_le (by positivity : (0 : ℝ) ≤ cornerG y3 y4 ^ 2)
      (hK₅ x y3 y4 mx m3 m4)
    rwa [show cornerG y3 y4 ^ 2 * -(x * cornerR x y3 / 4) = cornerC3 x y3 y4 by
      unfold cornerC3; ring] at this
  exact abs_cForm_le (by positivity) hY.le hx0 hx1.le hg hg1 (le_betaG _ _ _) hxh hM hM2 hc0 hc0x
    hc0β ha₀ ha₁ ha₂ hc₁ hc₂ hc₃

end QED.TwoLoop.UnitSCCornerMain

end
