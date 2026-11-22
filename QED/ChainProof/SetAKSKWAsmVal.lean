/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWQDisp

/-!
# Set (a), stage D: bounds on the node atoms at `s = 1`

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. For the
integrability of the `VA` node density against the dispersive kernel, every kernel
`k_s(T) = s/(T(s+T))` (`s > -4`, `T ≥ 4`) is dominated by `c_s k₁(T)`, `c_s = 5|s|/min(4, s+4)`
(`ksW_abs_ker_le`). Against `k₁` the atoms `1`, `a`, `|2 log a|` and `1/a` (`a = (T - T₀)/T₀`)
are nonnegative, and their integrals over the two pieces `(T₀, T₁]`, `T > T₁`
(`T₁ = T₀(1 + B)`) are node values, bounded elementarily for `T₀ ≥ 4`:

* `∫_{(T₀,T₁]} k₁ ≤ min(B, 1/4)`, `∫_{T > T₁} k₁ ≤ 1/4`, `∫_{(T₀,T₁]} a k₁ ≤ B`;
* `∫_{T > T₁} |2 log a| k₁ ≤ 5`, `∫_{T > T₁} k₁/a ≤ 1 + |log B|`.

Main results: `ksW_abs_ker_le`, `ksW_val_low`, `ksW_val_high`, `ksW_val_lin`, `ksW_val_log`,
`ksW_val_inv`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.ChainProof.SetAKS

/-- The kernel constant `c_s = 5|s|/min(4, s + 4)`. -/
noncomputable def ksWcs (s : ℝ) : ℝ := 5 * |s| / min 4 (s + 4)

theorem ksW_ksWcs_nonneg {s : ℝ} (hs : -4 < s) : 0 ≤ ksWcs s := by
  have hm : 0 < min 4 (s + 4) := lt_min (by norm_num) (by linarith)
  unfold ksWcs
  positivity

/-- **The kernel comparison**: `|s/(T(s+T))| ≤ c_s/(T(1+T))` for `s > -4`, `T ≥ 4`. -/
theorem ksW_abs_ker_le {s T : ℝ} (hs : -4 < s) (hT : 4 ≤ T) :
    |s / (T * (s + T))| ≤ ksWcs s * (1 / (T * (1 + T))) := by
  have hm : 0 < min 4 (s + 4) := lt_min (by norm_num) (by linarith)
  have hT0 : 0 < T := by linarith
  have hsT : 0 < s + T := by linarith
  have key : min 4 (s + 4) * (1 + T) ≤ 5 * (s + T) := by
    rcases le_or_gt 0 s with h | h
    · have := mul_le_mul_of_nonneg_right (min_le_left 4 (s + 4)) (by linarith : (0 : ℝ) ≤ 1 + T)
      linarith
    · have := mul_le_mul_of_nonneg_right (min_le_right 4 (s + 4)) (by linarith : (0 : ℝ) ≤ 1 + T)
      nlinarith
  rw [abs_div, abs_of_pos (mul_pos hT0 hsT), ksWcs, div_mul_div_comm, mul_one,
    div_le_div_iff₀ (mul_pos hT0 hsT) (mul_pos hm (by positivity))]
  have h0 := mul_le_mul_of_nonneg_left key (mul_nonneg (abs_nonneg s) hT0.le)
  nlinarith

section Values

variable {t₀ B : ℝ} (ht₀ : 4 ≤ t₀) (hB : 0 < B)
include ht₀ hB

theorem ksW_val_split {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi t₀)) :
    ∫ T in Ioi t₀, f T = (∫ T in Ioc t₀ (t₀ * (1 + B)), f T) + ∫ T in Ioi (t₀ * (1 + B)), f T := by
  have hT₁ : t₀ ≤ t₀ * (1 + B) := by nlinarith
  rw [← Ioc_union_Ioi_eq_Ioi hT₁, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hf.mono_set (Ioc_union_Ioi_eq_Ioi hT₁ ▸ subset_union_left))
    (hf.mono_set (Ioc_union_Ioi_eq_Ioi hT₁ ▸ subset_union_right))]

/-- The low piece of the constant atom: `∫_{(T₀,T₁]} k₁ ≤ B` and `≤ 1/4`. -/
theorem ksW_val_low :
    ∫ T in Ioc t₀ (t₀ * (1 + B)), 1 / (T * (1 + T)) ≤ B ∧
      ∫ T in Ioc t₀ (t₀ * (1 + B)), 1 / (T * (1 + T)) ≤ 1 / 4 := by
  have h0 : 0 < t₀ := by linarith
  have hT₁ : 0 < t₀ * (1 + B) := by positivity
  have e0 := ksD_log_eq_integral (s := 1) h0 (by linarith)
  have e1 := ksD_log_eq_integral (s := 1) hT₁ (by linarith)
  have hk := ksD_integrableOn_logNodeKer (s := 1) h0 (by linarith)
  have hs := ksW_val_split ht₀ hB hk
  rw [← e0, ← e1] at hs
  have l1 : 0 ≤ log (1 + 1 / (t₀ * (1 + B))) := log_nonneg (by have := hT₁; simp; positivity)
  have l0 : log (1 + 1 / t₀) ≤ 1 / t₀ := by
    have := log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / t₀)
    linarith
  have hinv : 1 / t₀ ≤ 1 / 4 := by gcongr
  refine ⟨?_, by linarith⟩
  have hprod : (1 + B) * (1 + 1 / (t₀ * (1 + B))) = 1 + B + 1 / t₀ := by
    field_simp
  have hle : log (1 + 1 / t₀) ≤ log (1 + B) + log (1 + 1 / (t₀ * (1 + B))) := by
    rw [← log_mul (by positivity) (by positivity), hprod]
    exact log_le_log (by positivity) (by linarith)
  have hB' : log (1 + B) ≤ B := by
    have := log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + B)
    linarith
  linarith

/-- The high piece of the constant atom: `∫_{T > T₁} k₁ ≤ 1/4`. -/
theorem ksW_val_high : ∫ T in Ioi (t₀ * (1 + B)), 1 / (T * (1 + T)) ≤ 1 / 4 := by
  have hT₁ : 4 ≤ t₀ * (1 + B) := by nlinarith
  have hT₁' : 0 < t₀ * (1 + B) := by linarith
  rw [← ksD_log_eq_integral (s := 1) hT₁' (by linarith)]
  have := log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / (t₀ * (1 + B)))
  have hinv : 1 / (t₀ * (1 + B)) ≤ 1 / 4 := by gcongr
  linarith

/-- The linear atom on the low piece: `∫_{(T₀,T₁]} a k₁ ≤ B`. -/
theorem ksW_val_lin : ∫ T in Ioc t₀ (t₀ * (1 + B)), (T - t₀) / t₀ * (1 / (T * (1 + T))) ≤ B := by
  have h0 : 0 < t₀ := by linarith
  have hT₁ : t₀ ≤ t₀ * (1 + B) := by nlinarith
  have e := ksW_mulLog_node (s := 1) h0 (by linarith) hB.le
  rw [intervalIntegral.integral_of_le hT₁] at e
  rw [← e]
  have hu : 0 < 1 + 1 / t₀ := by positivity
  have h1 : log (1 + B / (1 + 1 / t₀)) ≤ B / (1 + 1 / t₀) := by
    have := log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + B / (1 + 1 / t₀))
    linarith
  have h2 : 0 ≤ log (1 + B) := log_nonneg (by linarith)
  have h3 : (1 + 1 / t₀) * log (1 + B / (1 + 1 / t₀)) ≤ B := by
    calc _ ≤ (1 + 1 / t₀) * (B / (1 + 1 / t₀)) := mul_le_mul_of_nonneg_left h1 hu.le
      _ = B := by field_simp
  linarith

/-- The logarithmic atom on the high piece: `∫_{T > T₁} |2 log a| k₁ ≤ 5`. -/
theorem ksW_val_log :
    ∫ T in Ioi (t₀ * (1 + B)), |2 * log ((T - t₀) / t₀)| * (1 / (T * (1 + T))) ≤ 5 := by
  have h0 : 0 < t₀ := by linarith
  set f : ℝ → ℝ := fun T => 2 * log ((T - t₀) / t₀) * (1 / (T * (1 + T))) with hf
  have hfi : IntegrableOn f (Ioi t₀) := ksW_integrableOn_logSq (s := 1) h0 (by linarith)
  have habs : ∀ T ∈ Ioi t₀, |2 * log ((T - t₀) / t₀)| * (1 / (T * (1 + T))) = |f T| := by
    intro T hT
    have : t₀ < T := hT
    have hT0 : 0 < T := by linarith
    rw [hf, abs_mul (2 * log _), abs_of_pos (by positivity : (0 : ℝ) < 1 / (T * (1 + T)))]
  have hT₁ : t₀ ≤ t₀ * (1 + B) := by nlinarith
  have hmono : ∫ T in Ioi (t₀ * (1 + B)), |2 * log ((T - t₀) / t₀)| * (1 / (T * (1 + T))) ≤
      ∫ T in Ioi t₀, |f T| := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun T hT => habs T (lt_of_le_of_lt hT₁ hT))]
    exact setIntegral_mono_set hfi.norm (Eventually.of_forall fun T => abs_nonneg _)
      (Ioi_subset_Ioi hT₁).eventuallyLE
  refine hmono.trans ?_
  -- split at `T = 2T₀`
  have hs := ksW_val_split ht₀ one_pos hfi.norm
  have hs' := ksW_val_split ht₀ one_pos hfi
  have hT₂ : t₀ < t₀ * (1 + 1) := by linarith
  have ilow : ∫ T in Ioc t₀ (t₀ * (1 + 1)), |f T| = -∫ T in Ioc t₀ (t₀ * (1 + 1)), f T := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun T hT => abs_of_nonpos ?_
    have h1 : t₀ < T := hT.1
    have hl : log ((T - t₀) / t₀) ≤ 0 :=
      log_nonpos (div_nonneg (by linarith) h0.le) (by rw [div_le_one h0]; linarith [hT.2])
    have hT0 : 0 < T := by linarith
    have : 0 < 1 / (T * (1 + T)) := by positivity
    simp only [hf]
    nlinarith
  have ihigh : ∫ T in Ioi (t₀ * (1 + 1)), |f T| = ∫ T in Ioi (t₀ * (1 + 1)), f T := by
    refine setIntegral_congr_fun measurableSet_Ioi fun T hT => abs_of_nonneg ?_
    have h1 : t₀ * (1 + 1) < T := hT
    have hl : 0 ≤ log ((T - t₀) / t₀) := log_nonneg (by rw [le_div_iff₀ h0]; linarith)
    have hT0 : 0 < T := by linarith
    have : 0 < 1 / (T * (1 + T)) := by positivity
    simp only [hf]
    positivity
  have eall : ∫ T in Ioi t₀, f T = log (1 + 1 / t₀) ^ 2 :=
    (ksW_logSq_eq_integral (s := 1) h0 (by linarith)).symm
  have eK := ksW_ksUK_node (s := 1) h0 (by linarith) one_pos
  rw [intervalIntegral.integral_of_le hT₂.le] at eK
  have eK' : ∫ T in Ioc t₀ (t₀ * (1 + 1)), f T =
      2 * (ksUK (1 / (1 + 1 / t₀)) - ksUK 1) := by
    rw [eK, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun T _ => ?_
    simp only [hf, log_one, sub_zero]
    ring
  have hK0 : 0 ≤ ksUK (1 / (1 + 1 / t₀)) := ksU_ksUK_nonneg (by positivity)
  have hK1 : ksUK 1 ≤ 1 := by simpa using ksU_ksUK_le zero_le_one
  have hu : 0 < 1 / t₀ := by positivity
  have hl0 : 0 ≤ log (1 + 1 / t₀) := log_nonneg (by linarith)
  have hl1 : log (1 + 1 / t₀) ≤ 1 / 4 := by
    have := log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / t₀)
    have hinv : 1 / t₀ ≤ 1 / 4 := by gcongr
    linarith
  simp only [Real.norm_eq_abs] at hs
  rw [hs, ilow, ihigh]
  have hsq : log (1 + 1 / t₀) ^ 2 ≤ 1 / 16 := by nlinarith
  have hh : ∫ T in Ioi (t₀ * (1 + 1)), f T = log (1 + 1 / t₀) ^ 2 -
      2 * (ksUK (1 / (1 + 1 / t₀)) - ksUK 1) := by
    rw [← eall, ← eK', hs']
    ring
  rw [hh, eK']
  linarith

/-- The inverse atom on the high piece: `∫_{T > T₁} k₁/a ≤ 1 + |log B|`. -/
theorem ksW_val_inv :
    ∫ T in Ioi (t₀ * (1 + B)), t₀ / (T - t₀) * (1 / (T * (1 + T))) ≤ 1 + |log B| := by
  have h0 : 0 < t₀ := by linarith
  have e := ksW_logRatio_node (s := 1) h0 (by linarith) hB
  have e' : ∫ T in Ioi (t₀ * (1 + B)), t₀ / (T - t₀) * (1 / (T * (1 + T))) =
      (log (1 + B) - log B) - (log (1 + 1 / t₀ + B) - log B) / (1 + 1 / t₀) := by
    rw [show (log (1 + B) - log B) - (log (1 + 1 / t₀ + B) - log B) / (1 + 1 / t₀) =
      -((log (1 + 1 / t₀ + B) - log B) / (1 + 1 / t₀) - (log (1 + B) - log B)) by ring, e,
      ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun T _ => ?_
    ring
  rw [e']
  have hq : 0 ≤ (log (1 + 1 / t₀ + B) - log B) / (1 + 1 / t₀) := by
    have hu : 0 < 1 / t₀ := by positivity
    have : log B ≤ log (1 + 1 / t₀ + B) := log_le_log hB (by linarith)
    have : 0 < 1 + 1 / t₀ := by positivity
    exact div_nonneg (by linarith) this.le
  have hmain : log (1 + B) - log B ≤ 1 + |log B| := by
    rcases le_or_gt B 1 with h | h
    · have := log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + B)
      have := neg_abs_le (log B)
      linarith
    · have h2 : log (1 + B) ≤ log 2 + log B := by
        rw [← log_mul (by norm_num) hB.ne']
        exact log_le_log (by positivity) (by linarith)
      have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      have := abs_nonneg (log B)
      linarith
  linarith

end Values

end QED.ChainProof.SetAKS

end
