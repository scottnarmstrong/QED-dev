/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4PairF

/-!
# (R-Π₄) step L9, D3b: the photon limit of a change of the counterterm mass

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (decoupling),
part D3b. The on-shell mass insertion `ctPair e m a b` diverges as `a → 0`, `b → ∞`, but the
difference at two masses converges, by dominated convergence (the logarithms differ by at most
`|log(μ'²/μ²)|` pointwise):

* `dec_abs_log_ratio_le`: `|log((t μ'² + B)/(t μ² + B))| ≤ |log(μ'²/μ²)|`;
* `dec_tendsto_ctPair_sub`: **`ctPair e μ' Λ⁻¹ Λ - ctPair e μ Λ⁻¹ Λ → (3e²/16π²) log(μ'²/μ²)`**.
-/

@[expose] public section

open Filter Topology MeasureTheory Set
open scoped Interval

namespace QED.GradedProof.RPi4

/-- **The ratio of two shifted quadratic forms** lies between `1` and `μ'²/μ²`. -/
theorem dec_abs_log_ratio_le {μ μ' t B : ℝ} (hμ : 0 < μ) (hμ' : 0 < μ') (ht : 0 < t)
    (hB : 0 ≤ B) :
    |Real.log ((t * μ' ^ 2 + B) / (t * μ ^ 2 + B))| ≤ |Real.log (μ' ^ 2 / μ ^ 2)| := by
  have p : 0 < t * μ ^ 2 + B := by positivity
  have p' : 0 < t * μ' ^ 2 + B := by positivity
  have q : 0 < μ ^ 2 := by positivity
  have q' : 0 < μ' ^ 2 := by positivity
  rcases le_total (μ ^ 2) (μ' ^ 2) with h | h
  · have h1 : 1 ≤ (t * μ' ^ 2 + B) / (t * μ ^ 2 + B) := by
      rw [one_le_div p]; nlinarith
    have h2 : (t * μ' ^ 2 + B) / (t * μ ^ 2 + B) ≤ μ' ^ 2 / μ ^ 2 := by
      rw [div_le_div_iff₀ p q]; nlinarith
    have h3 : 1 ≤ μ' ^ 2 / μ ^ 2 := by rw [one_le_div q]; exact h
    rw [abs_of_nonneg (Real.log_nonneg h1), abs_of_nonneg (Real.log_nonneg h3)]
    exact Real.log_le_log (by linarith) h2
  · have h1 : (t * μ' ^ 2 + B) / (t * μ ^ 2 + B) ≤ 1 := by
      rw [div_le_one p]; nlinarith
    have h2 : μ' ^ 2 / μ ^ 2 ≤ (t * μ' ^ 2 + B) / (t * μ ^ 2 + B) := by
      rw [div_le_div_iff₀ q p]; nlinarith
    have h3 : μ' ^ 2 / μ ^ 2 ≤ 1 := by rw [div_le_one q]; exact h
    rw [abs_of_nonpos (Real.log_nonpos (by positivity) h1),
      abs_of_nonpos (Real.log_nonpos (by positivity) h3), neg_le_neg_iff]
    exact Real.log_le_log (by positivity) h2

/-- The difference of the on-shell logarithms is a difference of two log-ratios. -/
theorem dec_onShellL_sub {μ μ' a b x : ℝ} (hμ : μ ≠ 0) (hμ' : μ' ≠ 0) (ha : 0 < a) (hb : 0 < b)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    onShellL μ' a b x - onShellL μ a b x =
      Real.log ((x ^ 2 * μ' ^ 2 + (1 - x) * b ^ 2) / (x ^ 2 * μ ^ 2 + (1 - x) * b ^ 2)) -
        Real.log ((x ^ 2 * μ' ^ 2 + (1 - x) * a ^ 2) / (x ^ 2 * μ ^ 2 + (1 - x) * a ^ 2)) := by
  have pa := onShell_denom_pos hμ hx (pow_pos ha 2)
  have pb := onShell_denom_pos hμ hx (pow_pos hb 2)
  have pa' := onShell_denom_pos hμ' hx (pow_pos ha 2)
  have pb' := onShell_denom_pos hμ' hx (pow_pos hb 2)
  simp only [onShellL]
  rw [Real.log_div pb'.ne' pa'.ne', Real.log_div pb.ne' pa.ne', Real.log_div pb'.ne' pb.ne',
    Real.log_div pa'.ne' pa.ne']
  ring

/-- **The pointwise photon limit of the difference of the on-shell logarithms**: `-log(μ'²/μ²)`
for `0 < x < 1`. -/
theorem dec_tendsto_onShellL_sub {μ μ' x : ℝ} (hμ : 0 < μ) (hμ' : 0 < μ') (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun Λ : ℝ => onShellL μ' Λ⁻¹ Λ x - onShellL μ Λ⁻¹ Λ x) atTop
      (𝓝 (-Real.log (μ' ^ 2 / μ ^ 2))) := by
  have h1x : 0 < 1 - x := by linarith [hx.2]
  have hx2 : 0 < x ^ 2 := pow_pos hx.1 2
  -- the ratio at the light photon, as a function of `c = Λ⁻¹`
  have hA : Tendsto (fun c : ℝ => (x ^ 2 * μ' ^ 2 + (1 - x) * c ^ 2) /
      (x ^ 2 * μ ^ 2 + (1 - x) * c ^ 2)) (𝓝 0) (𝓝 (μ' ^ 2 / μ ^ 2)) := by
    have hc : ContinuousAt (fun c : ℝ => (x ^ 2 * μ' ^ 2 + (1 - x) * c ^ 2) /
        (x ^ 2 * μ ^ 2 + (1 - x) * c ^ 2)) 0 :=
      ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)
    have e : (x ^ 2 * μ' ^ 2 + (1 - x) * 0 ^ 2) / (x ^ 2 * μ ^ 2 + (1 - x) * 0 ^ 2) =
        μ' ^ 2 / μ ^ 2 := by
      field_simp
      ring
    have := hc.tendsto
    rwa [e] at this
  -- the ratio at the heavy photon, as a function of `c = Λ⁻¹`
  have hB : Tendsto (fun c : ℝ => (x ^ 2 * μ' ^ 2 * c ^ 2 + (1 - x)) /
      (x ^ 2 * μ ^ 2 * c ^ 2 + (1 - x))) (𝓝 0) (𝓝 1) := by
    have hc : ContinuousAt (fun c : ℝ => (x ^ 2 * μ' ^ 2 * c ^ 2 + (1 - x)) /
        (x ^ 2 * μ ^ 2 * c ^ 2 + (1 - x))) 0 :=
      ContinuousAt.div (by fun_prop) (by fun_prop) (by simp; linarith)
    have e : (x ^ 2 * μ' ^ 2 * 0 ^ 2 + (1 - x)) / (x ^ 2 * μ ^ 2 * 0 ^ 2 + (1 - x)) = 1 := by
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add]
      exact div_self h1x.ne'
    have := hc.tendsto
    rwa [e] at this
  have hinv : Tendsto (fun Λ : ℝ => Λ⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have lA := ((Real.continuousAt_log (by positivity)).tendsto.comp (hA.comp hinv))
  have lB := ((Real.continuousAt_log one_ne_zero).tendsto.comp (hB.comp hinv))
  rw [Real.log_one] at lB
  have := lB.sub lA
  rw [zero_sub] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with Λ hΛ
  rw [dec_onShellL_sub hμ.ne' hμ'.ne' (inv_pos.2 hΛ) hΛ (Ioo_subset_Icc_self hx)]
  simp only [Function.comp_apply]
  congr 2
  rw [inv_pow]
  field_simp

/-- **Dominated convergence for the weighted difference of the on-shell logarithms.** -/
theorem dec_tendsto_integral_onShellL_sub {μ μ' : ℝ} (hμ : 0 < μ) (hμ' : 0 < μ') {w : ℝ → ℝ}
    (hw : Continuous w) (hw1 : ∀ x ∈ Icc (0 : ℝ) 1, |w x| ≤ 1) :
    Tendsto (fun Λ : ℝ => ∫ x in (0 : ℝ)..1, w x * (onShellL μ' Λ⁻¹ Λ x - onShellL μ Λ⁻¹ Λ x))
      atTop (𝓝 (∫ x in (0 : ℝ)..1, w x * -Real.log (μ' ^ 2 / μ ^ 2))) := by
  set ℓ := Real.log (μ' ^ 2 / μ ^ 2)
  have hI : Ι (0 : ℝ) 1 = Ioc 0 1 := uIoc_of_le zero_le_one
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * |ℓ|)
    ?_ ?_ (by simp) ?_
  · filter_upwards [eventually_gt_atTop 0] with Λ hΛ
    have hc : ContinuousOn (fun x => w x * (onShellL μ' Λ⁻¹ Λ x - onShellL μ Λ⁻¹ Λ x))
        (uIcc 0 1) :=
      hw.continuousOn.mul ((continuousOn_onShellL hμ'.ne' (inv_pos.2 hΛ) hΛ).sub
        (continuousOn_onShellL hμ.ne' (inv_pos.2 hΛ) hΛ))
    rw [hI]
    refine (hc.mono ?_).aestronglyMeasurable measurableSet_Ioc
    rw [uIcc_of_le zero_le_one]
    exact Ioc_subset_Icc_self
  · filter_upwards [eventually_gt_atTop 0] with Λ hΛ
    refine Eventually.of_forall fun x hx => ?_
    rw [hI] at hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hx
    have hx0 : 0 < x ^ 2 := pow_pos hx.1 2
    have h1x : 0 ≤ 1 - x := by linarith [hx.2]
    rw [dec_onShellL_sub hμ.ne' hμ'.ne' (inv_pos.2 hΛ) hΛ hx', norm_mul, Real.norm_eq_abs,
      Real.norm_eq_abs]
    have b1 := dec_abs_log_ratio_le hμ hμ' hx0 (mul_nonneg h1x (sq_nonneg Λ))
    have b2 := dec_abs_log_ratio_le hμ hμ' hx0 (mul_nonneg h1x (sq_nonneg Λ⁻¹))
    calc |w x| * |_ - _| ≤ 1 * (|ℓ| + |ℓ|) :=
          mul_le_mul (hw1 x hx') ((abs_sub _ _).trans (add_le_add b1 b2)) (abs_nonneg _)
            zero_le_one
      _ = 2 * |ℓ| := by ring
  · have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({1} : Set ℝ) :=
      (countable_singleton 1).ae_notMem volume
    filter_upwards [hne] with x hx1 hx
    rw [hI] at hx
    have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
    exact (dec_tendsto_onShellL_sub hμ hμ' hx').const_mul (w x)

/-- **D3b: the photon limit of the change of the counterterm mass**:
`ctPair e μ' Λ⁻¹ Λ - ctPair e μ Λ⁻¹ Λ → (3e²/16π²) log(μ'²/μ²)`. -/
theorem dec_tendsto_ctPair_sub (e : ℝ) {μ μ' : ℝ} (hμ : 0 < μ) (hμ' : 0 < μ') :
    Tendsto (fun Λ : ℝ => ctPair e μ' Λ⁻¹ Λ - ctPair e μ Λ⁻¹ Λ) atTop
      (𝓝 (3 * e ^ 2 / (16 * Real.pi ^ 2) * Real.log (μ' ^ 2 / μ ^ 2))) := by
  set ℓ := Real.log (μ' ^ 2 / μ ^ 2)
  have t1 := dec_tendsto_integral_onShellL_sub hμ hμ' (w := fun _ => 1) continuous_const
    (fun _ _ => by simp)
  have t2 := dec_tendsto_integral_onShellL_sub hμ hμ' (w := fun x => 1 - x) (by fun_prop)
    (fun x hx => by rw [abs_of_nonneg (by linarith [hx.2])]; linarith [hx.1])
  have i1 : ∫ x in (0 : ℝ)..1, (1 : ℝ) * -ℓ = -ℓ := by simp
  have i2 : ∫ x in (0 : ℝ)..1, (1 - x) * -ℓ = -ℓ / 2 := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub
      intervalIntegrable_const intervalIntegral.intervalIntegrable_id, integral_id]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
    ring
  rw [i1] at t1
  rw [i2] at t2
  have := (t1.const_mul (-(e ^ 2 / (4 * Real.pi ^ 2)))).add
    (t2.const_mul (e ^ 2 / (8 * Real.pi ^ 2)))
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hval : 3 * e ^ 2 / (16 * Real.pi ^ 2) * ℓ =
      -(e ^ 2 / (4 * Real.pi ^ 2)) * -ℓ + e ^ 2 / (8 * Real.pi ^ 2) * (-ℓ / 2) := by
    field_simp
    ring
  rw [hval]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with Λ hΛ
  have hc : ∀ m : ℝ, 0 < m → ContinuousOn (onShellL m Λ⁻¹ Λ) (uIcc 0 1) :=
    fun m hm => continuousOn_onShellL hm.ne' (inv_pos.2 hΛ) hΛ
  have c1 := (hc μ' hμ').intervalIntegrable (μ := volume)
  have c2 := (hc μ hμ).intervalIntegrable (μ := volume)
  have hw : ContinuousOn (fun x : ℝ => 1 - x) (uIcc 0 1) := by fun_prop
  have d1 := (hw.mul (hc μ' hμ')).intervalIntegrable (μ := volume)
  have d2 := (hw.mul (hc μ hμ)).intervalIntegrable (μ := volume)
  simp only [ctPair, one_mul, mul_sub]
  rw [intervalIntegral.integral_sub c1 c2, intervalIntegral.integral_sub
    (f := fun x => (1 - x) * onShellL μ' Λ⁻¹ Λ x) (g := fun x => (1 - x) * onShellL μ Λ⁻¹ Λ x)
    d1 d2]
  ring

end QED.GradedProof.RPi4

end
