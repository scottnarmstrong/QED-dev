/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWRhoA
public import QED.ChainProof.SetAKSKWAsmDef
public import QED.ChainProof.SetAKSKWAsmInt

/-!
# Set (a), stage D: integrability of the `VA` node density on the square, and `ρ_A`

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. At a
fixed spectral point `T = 4/(1-δ²)` the node density `ksWnA x σ T` is integrable on
`(0, 1) × (σ₋, σ₊)`: in `x` it is dominated piecewise by `-48 log x + R` below the second
threshold and by `-96 log x - 48(1-x) log(1-x) + E/x` above it, so

  `∫₀¹ |ksWnAa x σ a| dx ≤ 372 + 48|log(1-σ)| + (128 + 64a)(|log a| + |log(a + 1 - σ)|)`,

which is integrable in `σ` (`a = T(σ - σ₋)(σ₊ - σ)`). With Fubini this evaluates the density
`ksWRhoA` of the assembly in closed form.

Main results:

* `ksWR_integral_abs_le`: the bound on the `x`-integral of `|ksWnAa|`;
* `ksWR_integrable_square`: integrability on the square;
* **`ksWR_ksWRhoA_eq`**: `ksWRhoA δ = ksWRAv δ` on `(0, 1)`;
* **`ksWR_ksWRhoB_iff`**: `2ρ_A + ρ_B = 16ρ⁽⁴⁾ + 6ρ_D ↔ ρ_B = ksWRBv δ` for `ρ_B = ksWRhoB`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology intervalIntegral

namespace QED.ChainProof.SetAKS

open QED.Chain

section Pointwise

variable {x σ a : ℝ}

theorem ksWR_abs_a1 (hx : x ∈ Ioo (0 : ℝ) 1) (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    |2 * ksDa1 x σ * (1 - σ)| ≤ 48 := by
  obtain ⟨x0, x1⟩ := hx
  obtain ⟨s0, s1⟩ := hσ
  have hk : |ksWRk σ| ≤ 24 := by
    unfold ksWRk
    rw [abs_le]
    constructor <;> nlinarith
  have e : 2 * ksDa1 x σ * (1 - σ) = 2 * ksWRk σ * ((1 - x) * (1 - σ)) := by
    simp only [ksDa1, ksWRk]
    ring
  have h1 : 0 ≤ (1 - x) * (1 - σ) := by nlinarith
  have h2 : (1 - x) * (1 - σ) ≤ 1 := by nlinarith
  rw [e, abs_mul, abs_mul, abs_of_nonneg h1]
  have := abs_nonneg (ksWRk σ)
  norm_num
  nlinarith

theorem ksWR_abs_k (hσ : σ ∈ Ioo (0 : ℝ) 1) : |2 * ksWRk σ * (1 - σ)| ≤ 48 := by
  obtain ⟨s0, s1⟩ := hσ
  unfold ksWRk
  rw [abs_le]
  constructor <;> nlinarith [mul_pos s0 (by linarith : (0 : ℝ) < 1 - σ)]

theorem ksWR_abs_al (hx : x ∈ Ioo (0 : ℝ) 1) (hσ : σ ∈ Ioo (0 : ℝ) 1) : |ksWal x σ| ≤ 80 := by
  obtain ⟨x0, x1⟩ := hx
  obtain ⟨s0, s1⟩ := hσ
  have p0 : 0 ≤ σ * (1 - σ) * (3 + x) :=
    mul_nonneg (mul_nonneg s0.le (by linarith)) (by linarith)
  have p1 : σ * (1 - σ) * (3 + x) ≤ 4 := by nlinarith [mul_pos s0 (by linarith : (0:ℝ) < 1 - σ)]
  have q0 : 0 ≤ (1 - x) * σ ^ 2 := mul_nonneg (by linarith) (sq_nonneg σ)
  have q1 : (1 - x) * σ ^ 2 ≤ 1 := by nlinarith
  unfold ksWal
  rw [abs_le]
  constructor <;> nlinarith

theorem ksWR_abs_lin (hx : x ∈ Ioo (0 : ℝ) 1) (hσ : σ ∈ Ioo (0 : ℝ) 1) (ha : 0 < a) :
    |ksWal x σ + (2 * ksDa1 x σ - ksWbe x σ) * a| ≤ 80 + 64 * a := by
  obtain ⟨x0, x1⟩ := hx
  obtain ⟨s0, s1⟩ := hσ
  have hα := ksWR_abs_al ⟨x0, x1⟩ ⟨s0, s1⟩
  have hd : |2 * ksDa1 x σ - ksWbe x σ| ≤ 64 := by
    unfold ksDa1 ksWbe
    have : 0 < 1 - x := by linarith
    rw [abs_le]
    constructor <;> nlinarith [mul_pos this s0, mul_pos (mul_pos this s0) s0]
  have := abs_add_le (ksWal x σ) ((2 * ksDa1 x σ - ksWbe x σ) * a)
  rw [abs_mul (2 * ksDa1 x σ - ksWbe x σ), abs_of_pos ha] at this
  nlinarith

/-- The pointwise bound below the second threshold. -/
theorem ksWR_abs_high (hx : x ∈ Ioo (0 : ℝ) 1) (hσ : σ ∈ Ioo (0 : ℝ) 1) (ha : 0 < a)
    (hb : x / (1 - x) * (1 - σ) < a) :
    |ksWnAa x σ a| ≤ (-48 + 0 * x) * log x +
      ((48 * (|log (1 - σ)| + |log a|) + 80 * ((1 - σ) / a) + 64) + 0 * x) := by
  have hA := ksWR_abs_a1 hx hσ
  have hα := ksWR_abs_al hx hσ
  have hY : 0 < 1 - σ := by linarith [hσ.2]
  have hL : log x ≤ 0 := log_nonpos hx.1.le hx.2.le
  have hβ0 : 0 ≤ ksWbe x σ * (1 - σ) := by
    unfold ksWbe; have : 0 < 1 - x := by linarith [hx.2]
    positivity
  have hβ1 : ksWbe x σ * (1 - σ) ≤ 16 := by
    unfold ksWbe
    have q0 : 0 ≤ (1 - x) * σ ^ 2 := mul_nonneg (by linarith [hx.2]) (sq_nonneg σ)
    have q1 : (1 - x) * σ ^ 2 ≤ 1 := by nlinarith [hσ.1, hσ.2, hx.1, hx.2]
    have : (1 - x) * σ ^ 2 * (1 - σ) ≤ 1 := by nlinarith [hσ.1]
    nlinarith
  set A := 2 * ksDa1 x σ * (1 - σ)
  have e : ksWnAa x σ a = A * log x + -A * (log (1 - σ) - log a) +
      ksWal x σ * ((1 - σ) / a) + -(ksWbe x σ * (1 - σ)) + A := by
    simp only [ksWnAa, hb, ↓reduceIte, A]
    ring
  have hYa : 0 < (1 - σ) / a := div_pos hY ha
  have t1 : |A * log x| ≤ 48 * -log x := by
    rw [abs_mul, abs_of_nonpos hL]
    exact mul_le_mul_of_nonneg_right hA (by linarith)
  have t2 : |-A * (log (1 - σ) - log a)| ≤ 48 * (|log (1 - σ)| + |log a|) := by
    rw [abs_mul, abs_neg]
    have : |log (1 - σ) - log a| ≤ |log (1 - σ)| + |log a| := by
      rw [abs_le]; constructor <;> linarith [abs_nonneg (log (1 - σ)), le_abs_self (log (1 - σ)),
        neg_abs_le (log (1 - σ)), le_abs_self (log a), neg_abs_le (log a)]
    exact mul_le_mul hA this (abs_nonneg _) (by norm_num)
  have t3 : |ksWal x σ * ((1 - σ) / a)| ≤ 80 * ((1 - σ) / a) := by
    rw [abs_mul, abs_of_pos hYa]
    exact mul_le_mul_of_nonneg_right hα hYa.le
  rw [e, abs_le]
  constructor <;> linarith [le_abs_self (A * log x), neg_abs_le (A * log x),
    le_abs_self (-A * (log (1 - σ) - log a)), neg_abs_le (-A * (log (1 - σ) - log a)),
    le_abs_self (ksWal x σ * ((1 - σ) / a)), neg_abs_le (ksWal x σ * ((1 - σ) / a)),
    le_abs_self A, neg_abs_le A]

/-- The pointwise bound above the second threshold. -/
theorem ksWR_abs_low (hx : x ∈ Ioo (0 : ℝ) 1) (hσ : σ ∈ Ioo (0 : ℝ) 1) (ha : 0 < a)
    (hb : ¬(x / (1 - x) * (1 - σ) < a)) :
    |ksWnAa x σ a| ≤ (-96 + 0 * x) * log x + -48 * ((1 - x) * log (1 - x)) +
      (80 + 64 * a) / x + (0 + 0 * x) := by
  obtain ⟨x0, x1⟩ := hx
  have hx1 : 0 < 1 - x := by linarith
  have hY : 0 < 1 - σ := by linarith [hσ.2]
  have hL : log x ≤ 0 := log_nonpos x0.le x1.le
  have hM : (1 - x) * log (1 - x) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hx1.le (log_nonpos hx1.le (by linarith))
  have hlog : log (x / (1 - x) * (1 - σ) / a) = log x - log (1 - x) + log (1 - σ) - log a := by
    rw [log_div (mul_pos (div_pos x0 hx1) hY).ne' ha.ne',
      log_mul (div_pos x0 hx1).ne' hY.ne', log_div x0.ne' hx1.ne']
  have hA := ksWR_abs_a1 ⟨x0, x1⟩ hσ
  have hk := ksWR_abs_k hσ
  have hG := ksWR_abs_lin ⟨x0, x1⟩ hσ ha
  set A := 2 * ksDa1 x σ * (1 - σ)
  set G := ksWal x σ + (2 * ksDa1 x σ - ksWbe x σ) * a
  have e : ksWnAa x σ a = (2 * A) * log x + -(2 * ksWRk σ * (1 - σ)) *
      ((1 - x) * log (1 - x)) + G * (1 - x) / x := by
    simp only [ksWnAa, hb, ↓reduceIte, hlog, A, G]
    simp only [ksDa1, ksWRk]
    field_simp
    ring
  have t1 : |2 * A * log x| ≤ 96 * -log x := by
    rw [abs_mul, abs_of_nonpos hL, abs_mul]
    norm_num
    nlinarith [abs_nonneg A]
  have t2 : |-(2 * ksWRk σ * (1 - σ)) * ((1 - x) * log (1 - x))| ≤
      48 * -((1 - x) * log (1 - x)) := by
    rw [abs_mul, abs_neg, abs_of_nonpos hM]
    exact mul_le_mul_of_nonneg_right hk (by linarith)
  have t3 : |G * (1 - x) / x| ≤ (80 + 64 * a) / x := by
    rw [abs_div, abs_of_pos x0, abs_mul, abs_of_pos hx1]
    gcongr
    nlinarith [abs_nonneg G]
  rw [e, abs_le]
  constructor <;> linarith [le_abs_self (2 * A * log x), neg_abs_le (2 * A * log x),
    le_abs_self (-(2 * ksWRk σ * (1 - σ)) * ((1 - x) * log (1 - x))),
    neg_abs_le (-(2 * ksWRk σ * (1 - σ)) * ((1 - x) * log (1 - x))),
    le_abs_self (G * (1 - x) / x), neg_abs_le (G * (1 - x) / x)]

end Pointwise

theorem ksWR_neg_mulLog_le {c : ℝ} (hc : 0 < c) : -(c * log c) ≤ 1 := by
  have h := log_le_sub_one_of_pos (inv_pos.2 hc)
  rw [log_inv] at h
  have : c * (-log c) ≤ c * (c⁻¹ - 1) := mul_le_mul_of_nonneg_left h hc.le
  rw [mul_sub, mul_inv_cancel₀ hc.ne'] at this
  nlinarith

/-- **The bound on the `x`-integral of `|ksWnAa|`.** -/
theorem ksWR_integral_abs_le {σ a : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) (ha : 0 < a) :
    ∫ x in (0 : ℝ)..1, |ksWnAa x σ a| ≤
      372 + 48 * |log (1 - σ)| + (128 + 64 * a) * (|log a| + |log (a + (1 - σ))|) := by
  have hY : 0 < 1 - σ := by linarith [hσ.2]
  obtain ⟨iH, iL⟩ := ksWR_intervalIntegrable_ksWnAa hσ ha
  set c := a / (a + (1 - σ)) with hc
  have hc0 : 0 < c := div_pos ha (by linarith)
  have hc1 : c < 1 := (div_lt_one (by linarith)).2 (by linarith)
  -- the dominating functions
  have bH : IntervalIntegrable (fun x => (-48 + 0 * x) * log x +
      ((48 * (|log (1 - σ)| + |log a|) + 80 * ((1 - σ) / a) + 64) + 0 * x)) volume 0 c :=
    (ksWR_intervalIntegrable_linLog _ _ 0 c).add (Continuous.intervalIntegrable (by fun_prop) _ _)
  have bL : IntervalIntegrable (fun x => (-96 + 0 * x) * log x + -48 * ((1 - x) * log (1 - x)) +
      (80 + 64 * a) / x + (0 + 0 * x)) volume c 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hc1.le]
    have hl : ContinuousOn log (Icc c 1) :=
      continuousOn_log.mono fun x hx => (hc0.trans_le hx.1).ne'
    have hi : ContinuousOn (fun x : ℝ => (80 + 64 * a) / x) (Icc c 1) :=
      continuousOn_const.div continuousOn_id fun x hx => (hc0.trans_le hx.1).ne'
    have hm := ksWR_continuous_mulLog_one
    refine ContinuousOn.add (ContinuousOn.add (ContinuousOn.add ?_ ?_) hi) ?_
    · exact (Continuous.continuousOn (by fun_prop)).mul hl
    · exact Continuous.continuousOn (by fun_prop)
    · exact Continuous.continuousOn (by fun_prop)
  have mH : ∫ x in (0 : ℝ)..c, |ksWnAa x σ a| ≤ ∫ x in (0 : ℝ)..c, ((-48 + 0 * x) * log x +
      ((48 * (|log (1 - σ)| + |log a|) + 80 * ((1 - σ) / a) + 64) + 0 * x)) :=
    integral_mono_on_of_le_Ioo hc0.le iH.abs bH fun x hx =>
      ksWR_abs_high ⟨hx.1, hx.2.trans hc1⟩ hσ ha
        ((ksWR_branch_iff ⟨hx.1, hx.2.trans hc1⟩ hσ.2 ha).2 hx.2)
  have mL : ∫ x in c..1, |ksWnAa x σ a| ≤ ∫ x in c..1, ((-96 + 0 * x) * log x +
      -48 * ((1 - x) * log (1 - x)) + (80 + 64 * a) / x + (0 + 0 * x)) :=
    integral_mono_on_of_le_Ioo hc1.le iL.abs bL fun x hx =>
      ksWR_abs_low ⟨hc0.trans hx.1, hx.2⟩ hσ ha fun h =>
        (lt_asymm ((ksWR_branch_iff ⟨hc0.trans hx.1, hx.2⟩ hσ.2 ha).1 h)) hx.1
  rw [ksWR_integral_high hc0] at mH
  rw [ksWR_integral_low hc0 hc1] at mL
  rw [← integral_add_adjacent_intervals iH.abs iL.abs]
  -- elementary bounds on the values
  have k1 := ksWR_neg_mulLog_le hc0
  have hc1' : 0 < 1 - c := by linarith
  have k2 := ksWR_neg_mulLog_le hc1'
  have k3 : (1 - c) ^ 2 * log (1 - c) ≥ -1 := by
    have : (1 - c) * ((1 - c) * log (1 - c)) ≥ -1 := by
      have h0 : (1 - c) * log (1 - c) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hc1'.le (log_nonpos hc1'.le (by linarith))
      nlinarith
    nlinarith
  have k4 : c * log c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc0.le (log_nonpos hc0.le hc1.le)
  have hlc : log c = log a - log (a + (1 - σ)) := log_div ha.ne' (by linarith)
  have k5 : -log c ≤ |log a| + |log (a + (1 - σ))| := by
    rw [hlc]
    linarith [neg_abs_le (log a), le_abs_self (log (a + (1 - σ)))]
  have k6 : (1 - σ) / a * c ≤ 1 := by
    rw [hc, div_mul_div_comm, mul_comm (1 - σ) a, ← div_mul_div_comm, div_self ha.ne', one_mul,
      div_le_one (by linarith)]
    linarith
  have hB : 0 ≤ |log (1 - σ)| + |log a| := by positivity
  have k7 : (48 * (|log (1 - σ)| + |log a|) + 80 * ((1 - σ) / a) + 64) * c ≤
      48 * (|log (1 - σ)| + |log a|) + 80 + 64 := by
    have := mul_le_of_le_one_right hB hc1.le
    nlinarith
  have k8 : (80 + 64 * a) * -log c ≤ (80 + 64 * a) * (|log a| + |log (a + (1 - σ))|) :=
    mul_le_mul_of_nonneg_left k5 (by positivity)
  have hlaY : 0 ≤ |log a| + |log (a + (1 - σ))| := by positivity
  have k9 : (1 - c) ^ 2 ≤ 1 := by nlinarith
  have k10 : 0 ≤ 48 * (|log a| + |log (a + (1 - σ))|) - 48 * |log a| := by
    have := abs_nonneg (log (a + (1 - σ)))
    linarith
  simp only [ksWRH, ksWRL] at mH mL
  nlinarith [abs_nonneg (log (1 - σ)), abs_nonneg (log a), mul_nonneg ha.le hlaY]

section Square

variable {δ : ℝ}

theorem ksWR_a_eq (hδ : δ ∈ Ioo (0 : ℝ) 1) (σ : ℝ) :
    ksDT 1 δ * (σ * (1 - σ)) - 1 = ksDT 1 δ * ((σ - (1 - δ) / 2) * ((1 + δ) / 2 - σ)) := by
  have pD : 1 - δ ^ 2 ≠ 0 := by nlinarith [hδ.1, hδ.2]
  unfold ksDT
  field_simp
  ring

/-- The dominating function of the `x`-integral of `|ksWnA|`. -/
noncomputable def ksWRg (δ σ : ℝ) : ℝ :=
  372 + 48 * |log (1 - σ)| + (128 + 64 * ksDT 1 δ) * (|log (ksDT 1 δ * (σ * (1 - σ)) - 1)| +
    |log (ksDT 1 δ * (σ * (1 - σ)) - 1 + (1 - σ))|)

theorem ksWR_integrableOn_ksWRg (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (ksWRg δ) (Ioo ((1 - δ) / 2) ((1 + δ) / 2)) := by
  obtain ⟨h0, h1⟩ := hδ
  set sm := (1 - δ) / 2
  set sp := (1 + δ) / 2
  have hsp : sm ≤ sp := by simp only [sm, sp]; linarith
  have pD : 0 < 1 - δ ^ 2 := by nlinarith
  have hT : 0 < ksDT 1 δ := by unfold ksDT; positivity
  have hIcc : ∀ σ ∈ Icc sm sp, 0 < 1 - σ ∧ 0 ≤ ksDT 1 δ * (σ * (1 - σ)) - 1 := fun σ hσ => by
    obtain ⟨hσ1, hσ2⟩ := hσ
    simp only [sm, sp] at hσ1 hσ2
    refine ⟨by linarith, ?_⟩
    rw [ksWR_a_eq ⟨h0, h1⟩]
    exact mul_nonneg hT.le (mul_nonneg (by linarith) (by linarith))
  have hIcc2 : ∀ σ ∈ Icc sm sp, ksDT 1 δ * (σ * (1 - σ)) - 1 + (1 - σ) ≠ 0 := fun σ hσ => by
    have := hIcc σ hσ
    linarith
  -- the regular logarithms
  have c1 : ContinuousOn (fun σ : ℝ => |log (1 - σ)|) (Icc sm sp) :=
    (ContinuousOn.log (by fun_prop) fun σ hσ => (hIcc σ hσ).1.ne').abs
  have c2 : ContinuousOn (fun σ : ℝ => |log (ksDT 1 δ * (σ * (1 - σ)) - 1 + (1 - σ))|)
      (Icc sm sp) :=
    (ContinuousOn.log (by fun_prop) hIcc2).abs
  have i1 := (c1.integrableOn_Icc (μ := volume)).mono_set (Ioo_subset_Icc_self (a := sm) (b := sp))
  have i2 := (c2.integrableOn_Icc (μ := volume)).mono_set (Ioo_subset_Icc_self (a := sm) (b := sp))
  -- the logarithm of `a`
  have l1 : IntervalIntegrable (fun σ => log (σ - sm)) volume sm sp := by
    have := (intervalIntegrable_log' (a := sm - sm) (b := sp - sm)).comp_sub_right sm
    simpa only [sub_add_cancel] using this
  have l2 : IntervalIntegrable (fun σ => log (sp - σ)) volume sm sp := by
    have := (intervalIntegrable_log' (a := sp - sm) (b := sp - sp)).comp_sub_left sp
    simpa only [sub_sub_cancel, sub_self, sub_zero] using this
  have l3 : IntegrableOn (fun σ => log (ksDT 1 δ) + log (σ - sm) + log (sp - σ)) (Ioo sm sp) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hsp).1
      ((intervalIntegrable_const.add l1).add l2)
  have l4 : IntegrableOn (fun σ => log (ksDT 1 δ * (σ * (1 - σ)) - 1)) (Ioo sm sp) := by
    refine l3.congr_fun (fun σ hσ => ?_) measurableSet_Ioo
    have a1 : 0 < σ - sm := by linarith [hσ.1]
    have a2 : 0 < sp - σ := by linarith [hσ.2]
    simp only
    rw [ksWR_a_eq ⟨h0, h1⟩, log_mul hT.ne' (mul_pos a1 a2).ne', log_mul a1.ne' a2.ne']
    ring
  have i3 := l4.abs
  unfold ksWRg
  exact ((integrableOn_const (by simp) (by simp)).add (i1.const_mul 48)).add
    ((i3.add i2).const_mul _)

/-- **The node density is integrable on the square** `(0, 1) × (σ₋, σ₊)` at `T = 4/(1-δ²)`. -/
theorem ksWR_integrable_square (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    Integrable (Function.uncurry fun x σ => ksWnA x σ (ksDT 1 δ))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo ((1 - δ) / 2) ((1 + δ) / 2)))) := by
  have hmeas : Measurable (Function.uncurry fun x σ => ksWnA x σ (ksDT 1 δ)) := by
    have := ksW_measurable_ksWnA.comp
      (measurable_id.prodMk (measurable_const (a := ksDT 1 δ)) : Measurable fun p : ℝ × ℝ =>
        (p, ksDT 1 δ))
    exact this
  refine (integrable_prod_iff' (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (ν := volume.restrict (Ioo ((1 - δ) / 2) ((1 + δ) / 2)))
    hmeas.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · refine ae_restrict_of_forall_mem measurableSet_Ioo fun σ hσ => ?_
    obtain ⟨iH, iL⟩ := ksWR_intervalIntegrable_ksWnAa (ksWR_sigma_mem hδ hσ) (ksWR_a_pos hδ hσ)
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 (iH.trans iL)
  · refine Integrable.mono' (ksWR_integrableOn_ksWRg hδ)
      (hmeas.norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioo fun σ hσ => ?_
    have hσ' := ksWR_sigma_mem hδ hσ
    have ha := ksWR_a_pos hδ hσ
    have hle : ksDT 1 δ * (σ * (1 - σ)) - 1 ≤ ksDT 1 δ := by
      have hT : 0 < ksDT 1 δ := by
        unfold ksDT; have : 0 < 1 - δ ^ 2 := by nlinarith [hδ.1, hδ.2]
        positivity
      have h1 : σ * (1 - σ) ≤ 1 := by nlinarith [hσ'.1, hσ'.2]
      nlinarith [mul_le_mul_of_nonneg_left h1 hT.le]
    have e : ∫ x in Ioo (0 : ℝ) 1, ‖Function.uncurry (fun x σ => ksWnA x σ (ksDT 1 δ)) (x, σ)‖ =
        ∫ x in (0 : ℝ)..1, |ksWnAa x σ (ksDT 1 δ * (σ * (1 - σ)) - 1)| := by
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      rfl
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), e]
    refine (ksWR_integral_abs_le hσ' ha).trans ?_
    unfold ksWRg
    have : 0 ≤ |log (ksDT 1 δ * (σ * (1 - σ)) - 1)| +
        |log (ksDT 1 δ * (σ * (1 - σ)) - 1 + (1 - σ))| := by positivity
    nlinarith

/-- **The `VA` spectral density of the assembly in closed form**: `ksWRhoA δ = ksWRAv δ`. -/
theorem ksWR_ksWRhoA_eq (hδ : δ ∈ Ioo (0 : ℝ) 1) : ksWRhoA δ = ksWRAv δ :=
  ksWR_rhoA_eq hδ (ksWR_integrable_square hδ)

/-- **The density identity reduced to the value of `ρ_B`**: on `(0, 1)`,
`2 ksWRhoA + ρ_B = 16ρ⁽⁴⁾ + 6ρ_D ↔ ρ_B = ksWRBv δ` (any `ρ_B`). -/
theorem ksWR_identity_iff_rhoB (hδ : δ ∈ Ioo (0 : ℝ) 1) (ρB : ℝ) :
    2 * ksWRhoA δ + ρB = 16 * ksRho δ + 6 * ksRhoDm δ ↔ ρB = ksWRBv δ :=
  ksWR_identity_iff (ksWR_ksWRhoA_eq hδ)

/-- The density identity for `ksWRhoB`, reduced to `ksWRhoB δ = ksWRBv δ`. -/
theorem ksWR_ksWRhoB_iff (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    2 * ksWRhoA δ + ksWRhoB δ = 16 * ksRho δ + 6 * ksRhoDm δ ↔ ksWRhoB δ = ksWRBv δ :=
  ksWR_identity_iff_rhoB hδ _

end Square

end QED.ChainProof.SetAKS

end
