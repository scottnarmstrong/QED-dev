/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWAsmBDisp
public import QED.ChainProof.SetAKSKWAsmVal

/-!
# Set (a), stage D: the absolute values of the `VB` node atoms

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. Bounds
on `∫ |atom| k₁`, `k₁(T) = 1/(T(1 + T))`, for the atoms of the `VB` node density:

* `ksWB_val_log`: `∫_{T > t₀} |2 log((T - t₀)/t₀)| k₁ ≤ 5` (`t₀ ≥ 4`);
* `ksWB_integral_abs_ind_sub`: an indicator difference in absolute value integrates over `Ι p q`;
* `ksWB_integral_abs_of_sign`: an integrand of one sign on `(p, q)` has `∫_Ι |f| = |∫_p^q f|`;
* `ksWB_abs_ksUK_sub_le`: `|K(a) - K(b)| ≤ log(1 + max a b) |log a - log b|`.
* **`ksWB_integral_norm_le`**: the node norm bound `∫_{T > 4} |n_B k_s| ≤ c_s ksWBw(ρ, β, w)`
  (off `w(1-w) = β(1-β)`).
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology
open scoped Interval

namespace QED.ChainProof.SetAKS

/-- The logarithmic atom on the whole half-line: `∫_{T > t₀} |2 log a| k₁ ≤ 5`. -/
theorem ksWB_val_log {t₀ : ℝ} (ht₀ : 4 ≤ t₀) :
    ∫ T in Ioi t₀, |2 * log ((T - t₀) / t₀)| * (1 / (T * (1 + T))) ≤ 5 := by
  have h0 : 0 < t₀ := by linarith
  set f : ℝ → ℝ := fun T => 2 * log ((T - t₀) / t₀) * (1 / (T * (1 + T))) with hf
  have hfi : IntegrableOn f (Ioi t₀) := ksW_integrableOn_logSq (s := 1) h0 (by linarith)
  have habs : ∀ T ∈ Ioi t₀, |2 * log ((T - t₀) / t₀)| * (1 / (T * (1 + T))) = |f T| := by
    intro T hT
    have : t₀ < T := hT
    have hT0 : 0 < T := by linarith
    rw [hf, abs_mul (2 * log _), abs_of_pos (by positivity : (0 : ℝ) < 1 / (T * (1 + T)))]
  rw [setIntegral_congr_fun measurableSet_Ioi habs]
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

theorem ksWB_abs_mul_ind_sub_eq (f : ℝ → ℝ) (p q t : ℝ) :
    |f t * ((if p < t then (1 : ℝ) else 0) - (if q < t then 1 else 0))| =
      (Ι p q).indicator (fun t => |f t|) t := by
  rcases le_total p q with h | h
  · rw [uIoc_of_le h]
    by_cases h1 : p < t <;> by_cases h2 : q < t
    · simp [h1, h2, indicator, not_le.2 h2]
    · simp [h1, h2, indicator, le_of_not_gt h2]
    · exact absurd (lt_of_le_of_lt h h2) h1
    · simp [h1, h2, indicator]
  · rw [uIoc_of_ge h]
    by_cases h1 : p < t <;> by_cases h2 : q < t
    · simp [h1, h2, indicator, not_le.2 h1]
    · exact absurd (lt_of_le_of_lt h h1) h2
    · simp [h1, h2, indicator, le_of_not_gt h1, abs_neg]
    · simp [h1, h2, indicator]

/-- **An indicator difference in absolute value integrates over `Ι p q`.** -/
theorem ksWB_integral_abs_ind_sub {f : ℝ → ℝ} {c p q : ℝ} (hp : c ≤ p) (hq : c ≤ q) :
    ∫ t in Ioi c, |f t * ((if p < t then 1 else 0) - (if q < t then 1 else 0))| =
      ∫ t in Ι p q, |f t| := by
  simp_rw [ksWB_abs_mul_ind_sub_eq f p q]
  rw [setIntegral_indicator measurableSet_uIoc, inter_eq_right.2]
  intro t ht
  exact lt_of_le_of_lt (le_min hp hq) ht.1

/-- **An integrand of one sign** between `p` and `q`: `∫_Ι |f| = |∫_p^q f|`. -/
theorem ksWB_integral_abs_of_sign {f : ℝ → ℝ} {p q : ℝ}
    (hf : (∀ t ∈ Ioo (min p q) (max p q), 0 ≤ f t) ∨
      (∀ t ∈ Ioo (min p q) (max p q), f t ≤ 0)) :
    ∫ t in Ι p q, |f t| = |∫ t in p..q, f t| := by
  rw [intervalIntegral.abs_integral_eq_abs_integral_uIoc, uIoc, integral_Ioc_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]
  rcases hf with hf | hf
  · rw [setIntegral_congr_fun measurableSet_Ioo fun t ht => abs_of_nonneg (hf t ht),
      abs_of_nonneg (setIntegral_nonneg measurableSet_Ioo hf)]
  · rw [setIntegral_congr_fun measurableSet_Ioo fun t ht => abs_of_nonpos (hf t ht),
      integral_neg, abs_of_nonpos (setIntegral_nonpos measurableSet_Ioo hf)]

/-- **A Lipschitz bound for `K`** in the logarithmic variable. -/
theorem ksWB_abs_ksUK_sub_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |ksUK a - ksUK b| ≤ log (1 + max a b) * |log a - log b| := by
  have hK : ∀ x y, 0 < x → x ≤ y → |ksUK y - ksUK x| ≤ log (1 + y) * (log y - log x) := by
    intro x y hx hxy
    have hsub : ksUK y - ksUK x = ∫ t in x..y, ksUKer t := by
      rw [ksUK, ksUK, intervalIntegral.integral_interval_sub_left
        (ksU_intervalIntegrable_ksUKer (hx.le.trans hxy)) (ksU_intervalIntegrable_ksUKer hx.le)]
    have hpos : ∀ t ∈ Icc x y, 0 < t := fun t ht => lt_of_lt_of_le hx ht.1
    have hint : IntervalIntegrable (fun t => log (1 + y) * t⁻¹) volume x y :=
      (continuousOn_const.mul (continuousOn_inv₀.mono fun t ht => (hpos t
        (by rwa [uIcc_of_le hxy] at ht)).ne')).intervalIntegrable
    rw [hsub, abs_of_nonneg (intervalIntegral.integral_nonneg hxy fun t ht =>
      ksU_ksUKer_nonneg (hpos t ht).le)]
    calc ∫ t in x..y, ksUKer t ≤ ∫ t in x..y, log (1 + y) * t⁻¹ := by
          refine intervalIntegral.integral_mono_on hxy
            ((ksU_intervalIntegrable_ksUKer hx.le).symm.trans
              (ksU_intervalIntegrable_ksUKer (hx.le.trans hxy))) hint fun t ht => ?_
          have ht0 := hpos t ht
          rw [ksUKer, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (log_le_log (by linarith) (by linarith [ht.2]))
            (inv_nonneg.2 ht0.le)
      _ = log (1 + y) * (log y - log x) := by
          rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hx (hx.trans_le hxy),
            log_div (hx.trans_le hxy).ne' hx.ne']
  rcases le_total b a with h | h
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.2 (log_le_log hb h))]
    exact hK b a hb h
  · rw [max_eq_right h, abs_sub_comm, abs_sub_comm (log a),
      abs_of_nonneg (sub_nonneg.2 (log_le_log ha h))]
    exact hK a b ha h

/-! ### The norm bound at a node -/

/-- The weight of the `VB` node in the norm bound of its dispersive integrand. -/
noncomputable def ksWBw (ρ β w : ℝ) : ℝ :=
  (|ksWBg0 ρ β w| + |ksWBg1 ρ β w|) / ρ * log (1 + ksWBl ρ β w * ksWBr β / ksWBq w) +
    ρ * |ksUcB w| * |ksUK (ksWBl ρ β w * (ksWBr β + 1) / (ksWBq w + 1)) -
      ksUK (ksWBl ρ β w * ksWBr β / ksWBq w)| +
    |ksUq ρ β w * ksDYmax β w / 2| * log (1 + 1 / ksWBp ρ β w) +
    |(1 - ρ)⁻¹ * ksUf0 β w| * |log (1 + 1 / ksWBr β) - log (1 + 1 / ksWBp ρ β w)| +
    |ρ * ksUcB w * log (ksDYmax β w / ρ)| * log (1 + 1 / ksWBq w) +
    |ρ * ksUcB w / 2| * 5 + |ksUf0 β w / 2| * 5

theorem ksWB_abs_ker_le_abs {s T u : ℝ} (hs : -4 < s) (hT : 4 ≤ T) :
    |u * (s / (T * (s + T)))| ≤ ksWcs s * |u * (1 / (T * (1 + T)))| := by
  have hk : 0 ≤ 1 / (T * (1 + T)) := by
    have : 0 < T := by linarith
    positivity
  rw [abs_mul, abs_mul, abs_of_nonneg hk, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (ksW_abs_ker_le hs hT) (abs_nonneg u)

section Norm

variable {ρ β w : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hβ : β ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1)
  (hab : w * (1 - w) ≠ β * (1 - β))
include hρ hβ hw hab

/-- **The norm bound at a node**: `∫_{T > 4} |n_B k_s| ≤ c_s w(ρ, β, w)`. -/
theorem ksWB_integral_norm_le {s : ℝ} (hs : -4 < s) :
    ∫ T in Ioi 4, ‖ksWnB ρ β w T * (s / (T * (s + T)))‖ ≤ ksWcs s * ksWBw ρ β w := by
  obtain ⟨hq0, hq4, hr0, hr4, hl0, hY, hY1, hD0⟩ := ksWB_basic hρ hβ hw
  have hqr := ksWB_q_ne_r hab
  have hp4 := ksWB_four_le_p hρ hβ hw hab
  have hp0 : 0 < ksWBp ρ β w := by linarith
  have hpdef : ksWBp ρ β w = (ksWBl ρ β w * ksWBr β + ksWBq w) / (1 + ksWBl ρ β w) := rfl
  have hρ0 := hρ.1
  have hs1q : -ksWBq w < 1 := by linarith
  have hs1r : -ksWBr β < 1 := by linarith
  have hs1p : -ksWBp ρ β w < 1 := by linarith
  have i1 := ksWB_intervalIntegrable_T1 hq0 hr0 hqr hl0 (ksWBg0 ρ β w / ρ) (ksWBg1 ρ β w / ρ)
    hs1q hs1r
  have i1' := ksWB_intervalIntegrable_T1 hq0 hr0 hqr hl0 1 (-1) hs1q hs1r
  have iK := ksWB_intervalIntegrable_K hq0 hr0 hqr hl0 hs1q hs1r
  have N1 := ksWB_T1_node hq0 hr0 hqr hl0 1 (-1) hs1q hs1r
  have NK := ksWB_K_node hq0 hr0 hqr hl0 hs1q hs1r
  rw [← hpdef] at i1 i1' iK N1 NK
  have ikp := ksD_integrableOn_logNodeKer hp0 hs1p
  have ikq := ksD_integrableOn_logNodeKer hq0 hs1q
  have ikr := ksD_integrableOn_logNodeKer hr0 hs1r
  have isq := ksW_integrableOn_logSq hq0 hs1q
  have isr := ksW_integrableOn_logSq hr0 hs1r
  have ikrp : IntervalIntegrable (fun T : ℝ => 1 / (T * (1 + T))) volume (ksWBr β)
      (ksWBp ρ β w) := by
    refine ContinuousOn.intervalIntegrable (continuousOn_const.div (by fun_prop) fun T hT => ?_)
    have : min (ksWBr β) (ksWBp ρ β w) ≤ T := hT.1
    have : 0 < T := by linarith [le_trans (le_min hr4 hp4) this]
    positivity
  -- the seven atoms (with `k₁`)
  set A1 : ℝ → ℝ := fun T => (ksWBg0 ρ β w / ρ - ksWBg1 ρ β w / ρ * T) *
      (ksWBr β / (ksWBr β - T)) * (1 / (T * (1 + T))) *
      ((if ksWBp ρ β w < T then 1 else 0) - (if ksWBq w < T then 1 else 0)) with hA1
  set A2 : ℝ → ℝ := fun T => ρ * ksUcB w *
      ((log (ksWBl ρ β w * (ksWBr β - T)) - log (T - ksWBq w)) * (1 / (T * (1 + T))) *
      ((if ksWBp ρ β w < T then 1 else 0) - (if ksWBq w < T then 1 else 0))) with hA2
  set A3 : ℝ → ℝ := fun T => ksUq ρ β w * ksDYmax β w / 2 *
      (1 / (T * (1 + T)) * (if ksWBp ρ β w < T then 1 else 0)) with hA3
  set A4 : ℝ → ℝ := fun T => (1 - ρ)⁻¹ * ksUf0 β w * (1 / (T * (1 + T)) *
      ((if ksWBr β < T then 1 else 0) - (if ksWBp ρ β w < T then 1 else 0))) with hA4
  set A5 : ℝ → ℝ := fun T => ρ * ksUcB w * log (ksDYmax β w / ρ) *
      (1 / (T * (1 + T)) * (if ksWBq w < T then 1 else 0)) with hA5
  set A6 : ℝ → ℝ := fun T => ρ * ksUcB w / 2 * (2 * log ((T - ksWBq w) / ksWBq w) *
      (1 / (T * (1 + T))) * (if ksWBq w < T then 1 else 0)) with hA6
  set A7 : ℝ → ℝ := fun T => ksUf0 β w / 2 * (2 * log ((T - ksWBr β) / ksWBr β) *
      (1 / (T * (1 + T))) * (if ksWBr β < T then 1 else 0)) with hA7
  have j1 : IntegrableOn A1 (Ioi 4) := ksWB_integrableOn_ind_sub i1
  have j2 : IntegrableOn A2 (Ioi 4) := (ksWB_integrableOn_ind_sub iK).const_mul _
  have j3 : IntegrableOn A3 (Ioi 4) := (ksWB_integrableOn_ind ikp).const_mul _
  have j4 : IntegrableOn A4 (Ioi 4) := (ksWB_integrableOn_ind_sub ikrp).const_mul _
  have j5 : IntegrableOn A5 (Ioi 4) := (ksWB_integrableOn_ind ikq).const_mul _
  have j6 : IntegrableOn A6 (Ioi 4) := (ksWB_integrableOn_ind isq).const_mul _
  have j7 : IntegrableOn A7 (Ioi 4) := (ksWB_integrableOn_ind isr).const_mul _
  have hk1 : ∀ T : ℝ, 4 < T → 0 < 1 / (T * (1 + T)) := fun T hT => by
    have : 0 < T := by linarith
    positivity
  -- the pointwise bound
  have hpt : ∀ᵐ T ∂(volume.restrict (Ioi (4 : ℝ))), ‖ksWnB ρ β w T * (s / (T * (s + T)))‖ ≤
      ksWcs s * (|A1 T| + |A2 T| + |A3 T| + |A4 T| + |A5 T| + |A6 T| + |A7 T|) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ksWB_ae_ne 4 (ksWBp ρ β w),
      ksWB_ae_ne 4 (ksWBq w), ksWB_ae_ne 4 (ksWBr β)] with T hT h1 h2 h3
    have hT4 : 4 < T := hT
    rw [Real.norm_eq_abs]
    refine (ksWB_abs_ker_le_abs hs hT4.le).trans
      (mul_le_mul_of_nonneg_left ?_ (ksW_ksWcs_nonneg hs))
    have e : ksWnB ρ β w T * (1 / (T * (1 + T))) =
        A1 T - A2 T - A3 T + A4 T - A5 T + A6 T + A7 T := by
      rw [ksWB_ksWnB_eq hρ hβ hw h1 h2 h3]
      simp only [hA1, hA2, hA3, hA4, hA5, hA6, hA7]
      ring
    rw [e]
    refine abs_le.2 ⟨?_, ?_⟩
    · linarith [neg_abs_le (A1 T), neg_abs_le (A2 T), neg_abs_le (A3 T), neg_abs_le (A4 T),
        neg_abs_le (A5 T), neg_abs_le (A6 T), neg_abs_le (A7 T), le_abs_self (A2 T),
        le_abs_self (A3 T), le_abs_self (A5 T)]
    · linarith [neg_abs_le (A2 T), neg_abs_le (A3 T), neg_abs_le (A5 T), le_abs_self (A1 T),
        le_abs_self (A2 T), le_abs_self (A3 T), le_abs_self (A4 T), le_abs_self (A5 T),
        le_abs_self (A6 T), le_abs_self (A7 T)]
  have hint := (ksWB_node_disp hρ hβ hw hab hs).1
  have g2 : IntegrableOn (fun T => |A1 T| + |A2 T|) (Ioi 4) := j1.abs.add j2.abs
  have g3 : IntegrableOn (fun T => |A1 T| + |A2 T| + |A3 T|) (Ioi 4) := g2.add j3.abs
  have g4 : IntegrableOn (fun T => |A1 T| + |A2 T| + |A3 T| + |A4 T|) (Ioi 4) := g3.add j4.abs
  have g5 : IntegrableOn (fun T => |A1 T| + |A2 T| + |A3 T| + |A4 T| + |A5 T|) (Ioi 4) :=
    g4.add j5.abs
  have g6 : IntegrableOn (fun T => |A1 T| + |A2 T| + |A3 T| + |A4 T| + |A5 T| + |A6 T|)
    (Ioi 4) := g5.add j6.abs
  have g7 : IntegrableOn (fun T => |A1 T| + |A2 T| + |A3 T| + |A4 T| + |A5 T| + |A6 T| +
    |A7 T|) (Ioi 4) := g6.add j7.abs
  refine (integral_mono_ae hint.norm (g7.const_mul _) hpt).trans ?_
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (ksW_ksWcs_nonneg hs)
  rw [integral_add g6 j7.abs, integral_add g5 j6.abs, integral_add g4 j5.abs,
    integral_add g3 j4.abs, integral_add g2 j3.abs, integral_add j1.abs j2.abs]
  -- the seven values
  have habs_ind : ∀ (f : ℝ → ℝ) (x : ℝ), 4 ≤ x →
      ∫ T in Ioi 4, |f T * (if x < T then 1 else 0)| = ∫ T in Ioi x, |f T| := by
    intro f x hx
    have e : ∀ T, |f T * (if x < T then (1 : ℝ) else 0)| =
        |f T| * (if x < T then 1 else 0) := fun T => by
      by_cases h : x < T <;> simp [h]
    simp_rw [e]
    exact ksWB_integral_ind hx
  have hk1v : ∀ x, 4 ≤ x → ∫ T in Ioi 4, |1 / (T * (1 + T)) * (if x < T then 1 else 0)| =
      log (1 + 1 / x) := by
    intro x hx
    rw [habs_ind _ x hx, ksD_log_eq_integral (s := 1) (by linarith) (by linarith)]
    refine setIntegral_congr_fun measurableSet_Ioi fun T hT => abs_of_pos (hk1 T ?_)
    exact lt_of_le_of_lt hx hT
  have hlogv : ∀ x, 4 ≤ x → ∫ T in Ioi 4,
      |2 * log ((T - x) / x) * (1 / (T * (1 + T))) * (if x < T then 1 else 0)| ≤ 5 := by
    intro x hx
    rw [habs_ind _ x hx]
    refine le_trans (le_of_eq ?_) (ksWB_val_log hx)
    refine setIntegral_congr_fun measurableSet_Ioi fun T hT => ?_
    rw [abs_mul, abs_of_pos (hk1 T (lt_of_le_of_lt hx hT))]
  have v1 : ∫ T in Ioi 4, |A1 T| ≤
      (|ksWBg0 ρ β w| + |ksWBg1 ρ β w|) / ρ * log (1 + ksWBl ρ β w * ksWBr β / ksWBq w) := by
    simp only [hA1]
    rw [ksWB_integral_abs_ind_sub hp4 hq4]
    have hsgn : ∀ T ∈ Ioo (min (ksWBp ρ β w) (ksWBq w)) (max (ksWBp ρ β w) (ksWBq w)),
        0 < (T - ksWBr β) * (ksWBq w - ksWBr β) ∧ 4 < T := fun T hT =>
      ⟨(ksWB_mem_uIcc hqr hl0 (Ioo_subset_Icc_self hT)).1,
        lt_of_le_of_lt (le_min hp4 hq4) hT.1⟩
    have hsgn' : ∀ T ∈ Ι (ksWBp ρ β w) (ksWBq w), 4 < T := fun T hT =>
      lt_of_le_of_lt (le_min hp4 hq4) hT.1
    calc ∫ T in Ι (ksWBp ρ β w) (ksWBq w), |(ksWBg0 ρ β w / ρ - ksWBg1 ρ β w / ρ * T) *
          (ksWBr β / (ksWBr β - T)) * (1 / (T * (1 + T)))|
        ≤ ∫ T in Ι (ksWBp ρ β w) (ksWBq w), (|ksWBg0 ρ β w| + |ksWBg1 ρ β w|) / ρ *
          |(1 - -1 * T) * (ksWBr β / (ksWBr β - T)) * (1 / (T * (1 + T)))| := by
          refine setIntegral_mono_on i1.def'.norm (i1'.def'.norm.const_mul _) measurableSet_uIoc
            fun T hT => ?_
          have hT4 := hsgn' T hT
          have hk := hk1 T hT4
          have e1 : |(ksWBg0 ρ β w / ρ - ksWBg1 ρ β w / ρ * T) * (ksWBr β / (ksWBr β - T)) *
              (1 / (T * (1 + T)))| = |ksWBg0 ρ β w - ksWBg1 ρ β w * T| / ρ *
                (|ksWBr β / (ksWBr β - T)| * (1 / (T * (1 + T)))) := by
            rw [abs_mul, abs_mul, abs_of_pos hk, show ksWBg0 ρ β w / ρ - ksWBg1 ρ β w / ρ * T =
              (ksWBg0 ρ β w - ksWBg1 ρ β w * T) / ρ by ring, abs_div, abs_of_pos hρ0]
            ring
          have e2 : (|ksWBg0 ρ β w| + |ksWBg1 ρ β w|) / ρ * |(1 - -1 * T) *
              (ksWBr β / (ksWBr β - T)) * (1 / (T * (1 + T)))| =
                (|ksWBg0 ρ β w| + |ksWBg1 ρ β w|) * (1 + T) / ρ *
                  (|ksWBr β / (ksWBr β - T)| * (1 / (T * (1 + T)))) := by
            rw [abs_mul, abs_mul, abs_of_pos hk, abs_of_pos (by linarith : (0 : ℝ) < 1 - -1 * T)]
            ring
          rw [e1, e2]
          have hg : |ksWBg0 ρ β w - ksWBg1 ρ β w * T| ≤
              (|ksWBg0 ρ β w| + |ksWBg1 ρ β w|) * (1 + T) := by
            have h1 := abs_sub (ksWBg0 ρ β w) (ksWBg1 ρ β w * T)
            rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < T)] at h1
            nlinarith [abs_nonneg (ksWBg0 ρ β w), abs_nonneg (ksWBg1 ρ β w)]
          gcongr
      _ = (|ksWBg0 ρ β w| + |ksWBg1 ρ β w|) / ρ *
          |∫ T in ksWBp ρ β w..ksWBq w, (1 - -1 * T) * (ksWBr β / (ksWBr β - T)) *
            (1 / (T * (1 + T)))| := by
          rw [integral_const_mul, ksWB_integral_abs_of_sign]
          rcases lt_or_gt_of_ne hqr with h | h
          · refine Or.inl fun T hT => ?_
            obtain ⟨h1, h2⟩ := hsgn T hT
            have : T < ksWBr β := by nlinarith
            have := hk1 T h2
            have : 0 < ksWBr β / (ksWBr β - T) := div_pos hr0 (by linarith)
            have : (0 : ℝ) < 1 - -1 * T := by linarith
            positivity
          · refine Or.inr fun T hT => ?_
            obtain ⟨h1, h2⟩ := hsgn T hT
            have : ksWBr β < T := by nlinarith
            have := hk1 T h2
            have : ksWBr β / (ksWBr β - T) < 0 := div_neg_of_pos_of_neg hr0 (by linarith)
            have : (0 : ℝ) < 1 - -1 * T := by linarith
            exact (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg this (by assumption))
              (by assumption)).le
      _ = (|ksWBg0 ρ β w| + |ksWBg1 ρ β w|) / ρ * log (1 + ksWBl ρ β w * ksWBr β / ksWBq w) := by
          rw [← N1]
          have : 0 ≤ log (1 + ksWBl ρ β w * ksWBr β / ksWBq w) :=
            log_nonneg (by have := div_pos (mul_pos hl0 hr0) hq0; linarith)
          simp [abs_of_nonneg this]
  have v2 : ∫ T in Ioi 4, |A2 T| = ρ * |ksUcB w| *
      |ksUK (ksWBl ρ β w * (ksWBr β + 1) / (ksWBq w + 1)) -
        ksUK (ksWBl ρ β w * ksWBr β / ksWBq w)| := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun T _ => (show |A2 T| = _ from abs_mul _ _)),
      integral_const_mul, abs_mul, abs_of_pos hρ0, ksWB_integral_abs_ind_sub hp4 hq4,
      ksWB_integral_abs_of_sign (Or.inl fun T hT => ?_), ← NK]
    have hpos := ksWB_K_density_pos hqr hl0 (t := T) hT
    have hT4 : 4 < T := lt_of_le_of_lt (le_min hp4 hq4) hT.1
    exact (mul_pos hpos (hk1 T hT4)).le
  have v3 : ∫ T in Ioi 4, |A3 T| = |ksUq ρ β w * ksDYmax β w / 2| *
      log (1 + 1 / ksWBp ρ β w) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun T _ => (show |A3 T| = _ from abs_mul _ _)),
      integral_const_mul, hk1v _ hp4]
  have v4 : ∫ T in Ioi 4, |A4 T| = |(1 - ρ)⁻¹ * ksUf0 β w| *
      |log (1 + 1 / ksWBr β) - log (1 + 1 / ksWBp ρ β w)| := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun T _ => (show |A4 T| = _ from abs_mul _ _)),
      integral_const_mul, ksWB_integral_abs_ind_sub hr4 hp4,
      ksWB_integral_abs_of_sign (Or.inl fun T hT => (hk1 T
        (lt_of_le_of_lt (le_min hr4 hp4) hT.1)).le), ← ksWB_integral_ind_sub hr4 hp4 ikrp]
    simp_rw [mul_sub]
    rw [integral_sub (ksWB_integrableOn_ind ikr) (ksWB_integrableOn_ind ikp),
      ksWB_integral_ind hr4, ksWB_integral_ind hp4,
      ← ksD_log_eq_integral (s := 1) hr0 hs1r, ← ksD_log_eq_integral (s := 1) hp0 hs1p]
  have v5 : ∫ T in Ioi 4, |A5 T| = |ρ * ksUcB w * log (ksDYmax β w / ρ)| *
      log (1 + 1 / ksWBq w) := by
    simp only [hA5]
    rw [show (fun T => |ρ * ksUcB w * log (ksDYmax β w / ρ) *
      (1 / (T * (1 + T)) * if ksWBq w < T then 1 else 0)|) = fun T =>
        |ρ * ksUcB w * log (ksDYmax β w / ρ)| *
          |1 / (T * (1 + T)) * if ksWBq w < T then 1 else 0| from funext fun T => abs_mul _ _,
      integral_const_mul, hk1v _ hq4]
  have v6 : ∫ T in Ioi 4, |A6 T| ≤ |ρ * ksUcB w / 2| * 5 := by
    simp only [hA6]
    rw [show (fun T => |ρ * ksUcB w / 2 * (2 * log ((T - ksWBq w) / ksWBq w) *
      (1 / (T * (1 + T))) * if ksWBq w < T then 1 else 0)|) = fun T => |ρ * ksUcB w / 2| *
        |2 * log ((T - ksWBq w) / ksWBq w) * (1 / (T * (1 + T))) *
          if ksWBq w < T then 1 else 0| from funext fun T => abs_mul _ _, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hlogv _ hq4) (abs_nonneg _)
  have v7 : ∫ T in Ioi 4, |A7 T| ≤ |ksUf0 β w / 2| * 5 := by
    simp only [hA7]
    rw [show (fun T => |ksUf0 β w / 2 * (2 * log ((T - ksWBr β) / ksWBr β) *
      (1 / (T * (1 + T))) * if ksWBr β < T then 1 else 0)|) = fun T => |ksUf0 β w / 2| *
        |2 * log ((T - ksWBr β) / ksWBr β) * (1 / (T * (1 + T))) *
          if ksWBr β < T then 1 else 0| from funext fun T => abs_mul _ _, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hlogv _ hr4) (abs_nonneg _)
  rw [v2, v3, v4, v5]
  unfold ksWBw
  linarith

end Norm

end QED.ChainProof.SetAKS

end
