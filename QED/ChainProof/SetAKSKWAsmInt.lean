/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWAsmVal

/-!
# Set (a), stage D: the joint integrability of the `VA` node density

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. The
node density `n_A(x, σ, T)` of `ksW_ksUQ_sub_eq` is, on the two pieces `(T₀, T₁]` and
`T > T₁`, a combination of the atoms `1`, `a`, `2 log a`, `1/a` with coefficients in `(x, σ)`.
With `|k_s| ≤ c_s k₁` and the atom values of `SetAKSKWAsmVal`,

  `∫_{T > T₀} |n_A k_s| dT ≤ c_s g(x, σ)`   (`ksW_integral_norm_ksWnA_le`),

with `g ≤ C ksUg(x) ksUg(σ)` integrable on the unit square. Hence the joint integrand
`[T₀(σ) < T] n_A k_s` is integrable on `(0,1)² × (4, ∞)` (`ksW_integrable_VA_joint`): the
hypothesis of the dispersive exchange `ksW_integral_dispersion_swap`.

Main results:

* `ksW_integral_norm_ksWnA_le`, `ksW_ksWgA_le`;
* **`ksW_integrable_VA_joint`**.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.ChainProof.SetAKS

/-- The `(x, σ)` weight dominating `∫ |n_A k_s| / c_s`. -/
noncomputable def ksWgA (x σ : ℝ) : ℝ :=
  |-2 * ksDa1 x σ * (1 - σ) * (-log x + log (1 - σ)) +
      2 * ksDa1 x σ * (1 - σ) * log (x / (1 - x) * (1 - σ))| / 4 +
    |ksWal x σ| * (1 - σ) + |2 * ksDa1 x σ - ksWbe x σ| * (1 - σ) +
    |-2 * ksDa1 x σ * (1 - σ) * (-log x + log (1 - σ)) - ksWbe x σ * (1 - σ) +
      2 * ksDa1 x σ * (1 - σ)| / 4 +
    5 * |ksDa1 x σ * (1 - σ)| + |ksWal x σ * (1 - σ)| * (1 + |log (x / (1 - x) * (1 - σ))|)

/-- **The norm integral of the node dispersion**: `∫_{T > T₀} |n_A k_s| ≤ c_s g(x, σ)`. -/
theorem ksW_integral_norm_ksWnA_le {x σ s : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hσ : σ ∈ Ioo (0 : ℝ) 1) (hs : -4 < s) :
    ∫ T in Ioi (σ * (1 - σ))⁻¹, ‖ksWnA x σ T * (s / (T * (s + T)))‖ ≤ ksWcs s * ksWgA x σ := by
  have hY : 0 < 1 - σ := by linarith [hσ.2]
  have hp : 0 < σ * (1 - σ) := mul_pos hσ.1 hY
  have hp4 : σ * (1 - σ) ≤ 1 / 4 := by nlinarith [sq_nonneg (σ - 1 / 2)]
  have hI := ksW_integrableOn_ksWnA hx hσ hs
  have hIn : IntegrableOn (fun T => ‖ksWnA x σ T * (s / (T * (s + T)))‖)
      (Ioi (σ * (1 - σ))⁻¹) := hI.norm
  set t₀ := (σ * (1 - σ))⁻¹ with ht₀def
  have ht₀ : 0 < t₀ := inv_pos.2 hp
  have h4 : 4 ≤ t₀ := by
    rw [ht₀def, le_inv_comm₀ (by norm_num) hp]
    linarith
  have hb : 0 < x / (1 - x) := div_pos hx.1 (by linarith [hx.2])
  have hB : 0 < x / (1 - x) * (1 - σ) := mul_pos hb hY
  set B := x / (1 - x) * (1 - σ) with hBdef
  set T₁ := t₀ * (1 + B) with hT₁def
  have hT₁ : t₀ < T₁ := by rw [hT₁def]; nlinarith
  have hc := ksW_ksWcs_nonneg hs
  have hk1 : IntegrableOn (fun T : ℝ => 1 / (T * (1 + T))) (Ioi t₀) :=
    ksD_integrableOn_logNodeKer (s := 1) ht₀ (by linarith)
  have hl1 : IntegrableOn (fun T => 2 * log ((T - t₀) / t₀) * (1 / (T * (1 + T)))) (Ioi t₀) :=
    ksW_integrableOn_logSq (s := 1) ht₀ (by linarith)
  have hr1 : IntegrableOn (fun T => -(t₀ / (T - t₀)) * (1 / (T * (1 + T)))) (Ioi T₁) :=
    ksW_integrableOn_logRatio (s := 1) ht₀ (by linarith) hT₁
  have ha1 : IntegrableOn (fun T => (T - t₀) / t₀ * (1 / (T * (1 + T)))) (Ioc t₀ T₁) := by
    have hc : ContinuousOn (fun T => (T - t₀) / t₀ * (1 / (T * (1 + T)))) (Icc t₀ T₁) := by
      refine ContinuousOn.mul (by fun_prop) (continuousOn_const.div (by fun_prop) fun T hT => ?_)
      exact (mul_pos (by linarith [hT.1]) (by linarith [hT.1])).ne'
    exact (hc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hsub₁ : Ioc t₀ T₁ ⊆ Ioi t₀ := Ioc_subset_Ioi_self
  have hsub₂ : Ioi T₁ ⊆ Ioi t₀ := Ioi_subset_Ioi hT₁.le
  -- the coefficients
  set α := ksWal x σ
  set β := ksWbe x σ
  set a₁ := ksDa1 x σ
  set b := x / (1 - x) with hbdef
  set P := -2 * a₁ * (1 - σ) * (-log x + log (1 - σ)) + 2 * a₁ * (1 - σ) * log B with hP
  set n₂ := (2 * a₁ - β) / b with hn₂
  set m₁ := -2 * a₁ * (1 - σ) * (-log x + log (1 - σ)) - β * (1 - σ) + 2 * a₁ * (1 - σ)
    with hm₁
  have hV := ksW_val_low h4 hB
  have hV2 := ksW_val_lin h4 hB
  have hV3 := ksW_val_high h4 hB
  have hV4 := ksW_val_log h4 hB
  have hV5 := ksW_val_inv h4 hB
  -- the low piece
  have hlow : ∫ T in Ioc t₀ T₁, ‖ksWnA x σ T * (s / (T * (s + T)))‖ ≤
      ksWcs s * ((|P| + |α| / b) * (∫ T in Ioc t₀ T₁, 1 / (T * (1 + T))) +
        |n₂| * ∫ T in Ioc t₀ T₁, (T - t₀) / t₀ * (1 / (T * (1 + T)))) := by
    have hint : IntegrableOn (fun T => ksWcs s * ((|P| + |α| / b) * (1 / (T * (1 + T))) +
        |n₂| * ((T - t₀) / t₀ * (1 / (T * (1 + T)))))) (Ioc t₀ T₁) :=
      (((hk1.mono_set hsub₁).const_mul _).add (ha1.const_mul _)).const_mul _
    refine (setIntegral_mono_on (hIn.mono_set hsub₁) hint measurableSet_Ioc
      fun T hT => ?_).trans_eq ?_
    · have hT0 : t₀ < T := hT.1
      have hTk := ksW_abs_ker_le hs (h4.trans hT0.le)
      have ha : 0 ≤ (T - t₀) / t₀ := div_nonneg (by linarith) ht₀.le
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, ksW_ksWnA_low hx hσ hT.1 hT.2]
      have hn : |-2 * a₁ * (1 - σ) * (-log x + log (1 - σ)) + α / b +
          2 * a₁ * (1 - σ) * log B + n₂ * ((T - t₀) / t₀)| ≤
          |P| + |α| / b + |n₂| * ((T - t₀) / t₀) := by
        have e : -2 * a₁ * (1 - σ) * (-log x + log (1 - σ)) + α / b + 2 * a₁ * (1 - σ) * log B +
            n₂ * ((T - t₀) / t₀) = P + α / b + n₂ * ((T - t₀) / t₀) := by rw [hP]; ring
        rw [e]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg ha, abs_div, abs_of_pos hb]
        have := abs_add_le P (α / b)
        rw [abs_div, abs_of_pos hb] at this
        linarith
      have hk0 : 0 ≤ 1 / (T * (1 + T)) := by
        have : 0 < T := by linarith
        positivity
      calc _ ≤ (|P| + |α| / b + |n₂| * ((T - t₀) / t₀)) * (ksWcs s * (1 / (T * (1 + T)))) :=
            mul_le_mul hn hTk (abs_nonneg _) (by positivity)
        _ = _ := by ring
    · rw [integral_const_mul, integral_add ((hk1.mono_set hsub₁).const_mul _) (ha1.const_mul _),
        integral_const_mul, integral_const_mul]
  -- the high piece
  have hhigh : ∫ T in Ioi T₁, ‖ksWnA x σ T * (s / (T * (s + T)))‖ ≤
      ksWcs s * (|m₁| * (∫ T in Ioi T₁, 1 / (T * (1 + T))) +
        |a₁ * (1 - σ)| * (∫ T in Ioi T₁, |2 * log ((T - t₀) / t₀)| * (1 / (T * (1 + T)))) +
        |α * (1 - σ)| * ∫ T in Ioi T₁, t₀ / (T - t₀) * (1 / (T * (1 + T)))) := by
    have hlabs : IntegrableOn (fun T => |2 * log ((T - t₀) / t₀)| * (1 / (T * (1 + T))))
        (Ioi T₁) := by
      refine IntegrableOn.congr_fun (hl1.mono_set hsub₂).norm (fun T hT => ?_) measurableSet_Ioi
      have : 0 < T := by have : T₁ < T := hT; linarith
      have hk : (0 : ℝ) < 1 / (T * (1 + T)) := by positivity
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos hk]
    have hrr : IntegrableOn (fun T => t₀ / (T - t₀) * (1 / (T * (1 + T)))) (Ioi T₁) :=
      hr1.neg.congr_fun (fun T _ => by simp only [Pi.neg_apply]; ring) measurableSet_Ioi
    have hint : IntegrableOn (fun T => ksWcs s * (|m₁| * (1 / (T * (1 + T))) +
        |a₁ * (1 - σ)| * (|2 * log ((T - t₀) / t₀)| * (1 / (T * (1 + T)))) +
        |α * (1 - σ)| * (t₀ / (T - t₀) * (1 / (T * (1 + T)))))) (Ioi T₁) :=
      ((((hk1.mono_set hsub₂).const_mul _).add (hlabs.const_mul _)).add
        (hrr.const_mul _)).const_mul _
    refine (setIntegral_mono_on (hIn.mono_set hsub₂) hint measurableSet_Ioi
      fun T hT => ?_).trans_eq ?_
    · have hT1 : T₁ < T := hT
      have hT0 : t₀ < T := hT₁.trans hT1
      have hTk := ksW_abs_ker_le hs (h4.trans hT0.le)
      have hr : 0 < t₀ / (T - t₀) := div_pos ht₀ (by linarith)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, ksW_ksWnA_high hx hσ hT]
      have hn : |m₁ + a₁ * (1 - σ) * (2 * log ((T - t₀) / t₀)) +
          -(α * (1 - σ)) * (-(t₀ / (T - t₀)))| ≤
          |m₁| + |a₁ * (1 - σ)| * |2 * log ((T - t₀) / t₀)| + |α * (1 - σ)| * (t₀ / (T - t₀)) := by
        refine (abs_add_le _ _).trans ?_
        refine add_le_add ((abs_add_le _ _).trans ?_) ?_
        · rw [abs_mul]
        · rw [abs_mul, abs_neg, abs_neg, abs_of_pos hr]
      have hk0 : 0 ≤ 1 / (T * (1 + T)) := by
        have : 0 < T := by linarith
        positivity
      calc _ ≤ (|m₁| + |a₁ * (1 - σ)| * |2 * log ((T - t₀) / t₀)| +
            |α * (1 - σ)| * (t₀ / (T - t₀))) * (ksWcs s * (1 / (T * (1 + T)))) :=
            mul_le_mul hn hTk (abs_nonneg _) (by positivity)
        _ = _ := by ring
    · have j1 : IntegrableOn (fun T => |m₁| * (1 / (T * (1 + T))) +
          |a₁ * (1 - σ)| * (|2 * log ((T - t₀) / t₀)| * (1 / (T * (1 + T))))) (Ioi T₁) :=
        ((hk1.mono_set hsub₂).const_mul _).add (hlabs.const_mul _)
      have j2 : IntegrableOn (fun T => |α * (1 - σ)| * (t₀ / (T - t₀) * (1 / (T * (1 + T)))))
          (Ioi T₁) := hrr.const_mul _
      rw [integral_const_mul, integral_add j1 j2, integral_add ((hk1.mono_set hsub₂).const_mul _)
        (hlabs.const_mul _), integral_const_mul, integral_const_mul, integral_const_mul]
  -- assemble
  rw [← Ioc_union_Ioi_eq_Ioi hT₁.le, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hIn.mono_set hsub₁) (hIn.mono_set hsub₂)]
  refine (add_le_add hlow hhigh).trans ?_
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ hc
  have e1 : |α| / b * B = |α| * (1 - σ) := by rw [hBdef]; field_simp
  have e2 : |n₂| * B = |2 * a₁ - β| * (1 - σ) := by
    rw [hn₂, hBdef, abs_div, abs_of_pos hb]; field_simp
  have i1 : (|P| + |α| / b) * (∫ T in Ioc t₀ T₁, 1 / (T * (1 + T))) ≤
      |P| / 4 + |α| / b * B := by
    have := abs_nonneg P
    have : 0 ≤ |α| / b := div_nonneg (abs_nonneg _) hb.le
    nlinarith [hV.1, hV.2]
  have i2 : |n₂| * (∫ T in Ioc t₀ T₁, (T - t₀) / t₀ * (1 / (T * (1 + T)))) ≤ |n₂| * B :=
    mul_le_mul_of_nonneg_left hV2 (abs_nonneg _)
  have i3 : |m₁| * (∫ T in Ioi T₁, 1 / (T * (1 + T))) ≤ |m₁| / 4 := by
    have := mul_le_mul_of_nonneg_left hV3 (abs_nonneg m₁); linarith
  have i4 := mul_le_mul_of_nonneg_left hV4 (abs_nonneg (a₁ * (1 - σ)))
  have i5 := mul_le_mul_of_nonneg_left hV5 (abs_nonneg (α * (1 - σ)))
  unfold ksWgA
  rw [← hP, ← hm₁]
  linarith

theorem ksW_abs_mul_le {c u K : ℝ} (h : |c| ≤ K) : |c * u| ≤ K * |u| := by
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right h (abs_nonneg u)

/-- **The weight is dominated by the unit-square weight**: `g ≤ 1000 ksUg(x) ksUg(σ)`. -/
theorem ksW_ksWgA_le {x σ : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    ksWgA x σ ≤ 1000 * (ksUg x * ksUg σ) := by
  obtain ⟨x0, x1⟩ := hx
  obtain ⟨σ0, σ1⟩ := hσ
  have hY : 0 < 1 - σ := by linarith
  have hx' : 0 < 1 - x := by linarith
  have ha : |ksDa1 x σ| ≤ 8 :=
    (ksU_abs_ksDa1_le' ⟨x0.le, x1.le⟩ ⟨σ0.le, σ1.le⟩).trans (by linarith)
  set c := ksDa1 x σ * (1 - σ) with hcdef
  have hc : |c| ≤ 8 := by
    rw [hcdef, abs_mul, abs_of_pos hY]
    nlinarith [abs_nonneg (ksDa1 x σ)]
  have hp : 0 ≤ σ * (1 - σ) * (3 + x) ∧ σ * (1 - σ) * (3 + x) ≤ 1 := by
    have h1 : 0 ≤ σ * (1 - σ) := by positivity
    have h2 : σ * (1 - σ) ≤ 1 / 4 := by nlinarith [sq_nonneg (σ - 1 / 2)]
    constructor
    · positivity
    · nlinarith
  have hq : 0 ≤ (1 - x) * σ ^ 2 ∧ (1 - x) * σ ^ 2 ≤ 1 := by
    constructor
    · positivity
    · have : σ ^ 2 ≤ 1 := by nlinarith
      nlinarith
  have hal : |ksWal x σ| ≤ 32 := by
    unfold ksWal
    rw [abs_le]
    constructor <;> nlinarith [hp.1, hp.2, hq.1, hq.2]
  have hbe : |ksWbe x σ| ≤ 16 := by
    unfold ksWbe
    rw [abs_le]
    constructor <;> nlinarith [hq.1, hq.2]
  have hαY : |ksWal x σ * (1 - σ)| ≤ 32 := by
    rw [abs_mul, abs_of_pos hY]
    nlinarith [abs_nonneg (ksWal x σ)]
  have hβY : |ksWbe x σ * (1 - σ)| ≤ 16 := by
    rw [abs_mul, abs_of_pos hY]
    nlinarith [abs_nonneg (ksWbe x σ)]
  -- logarithms
  have hgx : 1 ≤ ksUg x ∧ x ^ (-(1 / 2 : ℝ)) ≤ ksUg x - 1 ∧
      (1 - x) ^ (-(1 / 2 : ℝ)) ≤ ksUg x - 1 := by
    have := rpow_nonneg x0.le (-(1 / 2 : ℝ))
    have := rpow_nonneg hx'.le (-(1 / 2 : ℝ))
    unfold ksUg
    refine ⟨by linarith, by linarith, by linarith⟩
  have hgσ : 1 ≤ ksUg σ ∧ (1 - σ) ^ (-(1 / 2 : ℝ)) ≤ ksUg σ - 1 := by
    have := rpow_nonneg σ0.le (-(1 / 2 : ℝ))
    have := rpow_nonneg hY.le (-(1 / 2 : ℝ))
    unfold ksUg
    refine ⟨by linarith, by linarith⟩
  have lx := ksU_abs_log_le x0 x1.le
  have l1x := ksU_abs_log_le hx' (by linarith)
  have lY := ksU_abs_log_le hY (by linarith)
  have hlB : |log (x / (1 - x) * (1 - σ))| ≤ |log x| + |log (1 - x)| + |log (1 - σ)| := by
    rw [log_mul (div_pos x0 hx').ne' hY.ne', log_div x0.ne' hx'.ne']
    refine (abs_add_le _ _).trans ?_
    have := abs_sub (log x) (log (1 - x))
    linarith
  set lB := |log (x / (1 - x) * (1 - σ))|
  have hlxY : |-log x + log (1 - σ)| ≤ |log x| + |log (1 - σ)| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
  -- the six terms
  have t1 : |-2 * ksDa1 x σ * (1 - σ) * (-log x + log (1 - σ)) +
      2 * ksDa1 x σ * (1 - σ) * log (x / (1 - x) * (1 - σ))| ≤
      16 * (|log x| + |log (1 - σ)|) + 16 * lB := by
    rw [show -2 * ksDa1 x σ * (1 - σ) * (-log x + log (1 - σ)) +
      2 * ksDa1 x σ * (1 - σ) * log (x / (1 - x) * (1 - σ)) =
      (-2 * c) * (-log x + log (1 - σ)) + (2 * c) * log (x / (1 - x) * (1 - σ)) by ring]
    have h1 := ksW_abs_mul_le (u := -log x + log (1 - σ)) (K := 16)
      (by rw [abs_mul]; norm_num; linarith : |-2 * c| ≤ 16)
    have h2 := ksW_abs_mul_le (u := log (x / (1 - x) * (1 - σ))) (K := 16)
      (by rw [abs_mul]; norm_num; linarith : |2 * c| ≤ 16)
    have := abs_add_le ((-2 * c) * (-log x + log (1 - σ)))
      ((2 * c) * log (x / (1 - x) * (1 - σ)))
    linarith
  have t3 : |2 * ksDa1 x σ - ksWbe x σ| * (1 - σ) ≤ 32 := by
    have : |2 * ksDa1 x σ - ksWbe x σ| ≤ 32 := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul]
      norm_num
      linarith
    nlinarith [abs_nonneg (2 * ksDa1 x σ - ksWbe x σ)]
  have t2 : |ksWal x σ| * (1 - σ) ≤ 32 := by
    nlinarith [abs_nonneg (ksWal x σ)]
  have t4 : |-2 * ksDa1 x σ * (1 - σ) * (-log x + log (1 - σ)) - ksWbe x σ * (1 - σ) +
      2 * ksDa1 x σ * (1 - σ)| ≤ 16 * (|log x| + |log (1 - σ)|) + 32 := by
    rw [show -2 * ksDa1 x σ * (1 - σ) * (-log x + log (1 - σ)) - ksWbe x σ * (1 - σ) +
      2 * ksDa1 x σ * (1 - σ) = (-2 * c) * (-log x + log (1 - σ)) +
        (-(ksWbe x σ * (1 - σ)) + 2 * c) by ring]
    have h1 := ksW_abs_mul_le (u := -log x + log (1 - σ)) (K := 16)
      (by rw [abs_mul]; norm_num; linarith : |-2 * c| ≤ 16)
    have h2 : |-(ksWbe x σ * (1 - σ)) + 2 * c| ≤ 32 := by
      refine (abs_add_le _ _).trans ?_
      have : |2 * c| ≤ 16 := by rw [abs_mul]; norm_num; linarith
      rw [abs_neg]
      linarith
    have := abs_add_le ((-2 * c) * (-log x + log (1 - σ))) (-(ksWbe x σ * (1 - σ)) + 2 * c)
    linarith
  have t6 : |ksWal x σ * (1 - σ)| * (1 + lB) ≤ 32 * (1 + lB) :=
    mul_le_mul_of_nonneg_right hαY (by positivity)
  have hG1 : ksUg x ≤ ksUg x * ksUg σ := le_mul_of_one_le_right (by linarith) hgσ.1
  have hG2 : ksUg σ ≤ ksUg x * ksUg σ := le_mul_of_one_le_left (by linarith) hgx.1
  have hG0 : 1 ≤ ksUg x * ksUg σ := by nlinarith
  unfold ksWgA
  rw [← hcdef]
  have : 0 ≤ lB := abs_nonneg _
  linarith [hgx.2.1, hgx.2.2, hgσ.2]

theorem ksW_measurable_ksWnA : Measurable fun p : (ℝ × ℝ) × ℝ => ksWnA p.1.1 p.1.2 p.2 := by
  unfold ksWnA ksWnAa ksDa1 ksWal ksWbe
  refine Measurable.add (by fun_prop) (Measurable.ite ?_ (by fun_prop) (by fun_prop))
  exact measurableSet_lt (by fun_prop) (by fun_prop)

/-- The threshold of the node, `max 4 T₀(σ)`: equal to `T₀(σ)` on `(0, 1)`, and `≥ 4`. -/
noncomputable def ksWt0 (σ : ℝ) : ℝ := max 4 (σ * (1 - σ))⁻¹

theorem ksW_four_le_ksWt0 (σ : ℝ) : 4 ≤ ksWt0 σ := le_max_left _ _

theorem ksW_ksWt0_eq {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) : ksWt0 σ = (σ * (1 - σ))⁻¹ := by
  have hp : 0 < σ * (1 - σ) := mul_pos hσ.1 (by linarith [hσ.2])
  have hp4 : σ * (1 - σ) ≤ 1 / 4 := by nlinarith [sq_nonneg (σ - 1 / 2)]
  refine max_eq_right ?_
  rw [le_inv_comm₀ (by norm_num) hp]
  linarith

/-- The joint integrand of the `VA` dispersive exchange. -/
noncomputable def ksWjA (s : ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  {p : (ℝ × ℝ) × ℝ | ksWt0 p.1.2 < p.2}.indicator
    (fun p => ksWnA p.1.1 p.1.2 p.2 * (s / (p.2 * (s + p.2)))) p

theorem ksW_measurable_ksWjA (s : ℝ) : Measurable (ksWjA s) := by
  unfold ksWjA
  refine (ksW_measurable_ksWnA.mul (by fun_prop)).indicator ?_
  exact measurableSet_lt (by unfold ksWt0; fun_prop) measurable_snd

theorem ksW_ksWjA_slice (s : ℝ) (z : ℝ × ℝ) :
    (fun T => ksWjA s (z, T)) =
      (Ioi (ksWt0 z.2)).indicator (fun T => ksWnA z.1 z.2 T * (s / (T * (s + T)))) := by
  funext T
  simp only [ksWjA, indicator, mem_ofPred_eq, mem_Ioi]

theorem ksW_restrict_Ioi_ksWt0 {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    (volume.restrict (Ioi (4 : ℝ))).restrict (Ioi (ksWt0 σ)) =
      volume.restrict (Ioi (σ * (1 - σ))⁻¹) := by
  rw [Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi,
    sup_eq_left.2 (ksW_four_le_ksWt0 σ), ksW_ksWt0_eq hσ]

/-- **The joint integrability of the `VA` dispersive exchange**: `[T₀(σ) < T] n_A k_s` is
integrable on `(0,1)² × (4, ∞)`. -/
theorem ksW_integrable_VA_joint {s : ℝ} (hs : -4 < s) :
    Integrable (ksWjA s) (((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1))).prod (volume.restrict (Ioi 4))) := by
  have hmeas := ksW_measurable_ksWjA s
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  have hae : ∀ᵐ z ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))),
      z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
  have hnorm : ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
      ∫ T, ‖ksWjA s (z, T)‖ ∂(volume.restrict (Ioi 4)) =
        ∫ T in Ioi (z.2 * (1 - z.2))⁻¹, ‖ksWnA z.1 z.2 T * (s / (T * (s + T)))‖ := by
    intro z hz
    have e : ∀ T, ‖ksWjA s (z, T)‖ = (Ioi (ksWt0 z.2)).indicator
        (fun T => ‖ksWnA z.1 z.2 T * (s / (T * (s + T)))‖) T := fun T => by
      rw [show ksWjA s (z, T) = _ from congrFun (ksW_ksWjA_slice s z) T,
        norm_indicator_eq_indicator_norm]
    simp only [e]
    rw [integral_indicator measurableSet_Ioi, ksW_restrict_Ioi_ksWt0 hz.2]
  constructor
  · filter_upwards [hae] with z hz
    rw [ksW_ksWjA_slice, integrable_indicator_iff measurableSet_Ioi, IntegrableOn,
      ksW_restrict_Ioi_ksWt0 hz.2]
    exact ksW_integrableOn_ksWnA hz.1 hz.2 hs
  · refine Integrable.mono' (ksU_integrable_ksUg_mul.const_mul (ksWcs s * 1000))
      (hmeas.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable) ?_
    filter_upwards [hae] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), hnorm z hz]
    refine (ksW_integral_norm_ksWnA_le hz.1 hz.2 hs).trans ?_
    have := mul_le_mul_of_nonneg_left (ksW_ksWgA_le hz.1 hz.2) (ksW_ksWcs_nonneg hs)
    linarith

end QED.ChainProof.SetAKS

end
