/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKUVA

/-!
# Set (a), stage D: bounds and the node interchange for the `VA` class

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification), step D3 (the photon-mass integral). At a fixed outer node `x`
the `VA` integrand `x⁻¹ ksDLin(A(σ), ksDb M u x, 1 - σ, α σ, β σ)` is bounded on
`(0, Λ] × (0, 1)` (its denominator is at least `A(σ) ≥ kA > 0`), so the photon-mass integral
and the `σ`-integral may be swapped, and the photon-mass integral is evaluated node by node by
the antiderivative `ksUPhi`. The node difference `ksUPhi(ksDb M Λ x) - ksUPhi(ksDb M 0 x)` is
bounded by `C (1 + x^{-1/2} + (1 - x)^{-1/2})`, integrable over the outer node.

Main results:

* `ksU_abs_ksDLin_le`, `ksU_ksDLin_one_one_le`: `|ksDLin a₀ a₁| ≤ (|a₀| + |a₁|) ksDLin 1 1`,
  `ksDLin 1 1 ≤ (1 + A⁻¹)²`;
* `ksU_kA_le_ksDA`: `A(σ) ≥ kA = min(M², M² + s/4) > 0` on `[0, 1]`;
* **`ksU_abs_ksUNodeD_le`**: the node bound of the photon-mass integral;
* **`ksU_node_swap`**: at a fixed `x`, the photon-mass and `σ` integrals commute, and the
  result is the `σ`-integral of the node difference.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral

namespace QED.ChainProof.SetAKS

/-! ### Elementary bounds -/

theorem ksU_ksDLin_one_one_le {A b Y : ℝ} (hA : 0 < A) (hb : 0 < b) (hY : 0 ≤ Y)
    (hY1 : Y ≤ 1) : ksDLin A b Y 1 1 ≤ (1 + A⁻¹) ^ 2 := by
  rw [← ksD_integral_lin 1 1 hA hb hY]
  have hle : ∫ r in (0 : ℝ)..Y, ksDLinI A b Y 1 1 r ≤
      ∫ r in (0 : ℝ)..Y, r * (A⁻¹ ^ 2 + 2 * A⁻¹) := by
    refine intervalIntegral.integral_mono_on hY ?_
      ((continuous_id.mul continuous_const).intervalIntegrable _ _) fun r hr => ?_
    · refine ContinuousOn.intervalIntegrable fun r hr => ?_
      rw [uIcc_of_le hY] at hr
      have hD := ksD_den_pos hA hb hr.2
      refine ContinuousAt.continuousWithinAt ?_
      unfold ksDLinI
      have : ContinuousAt (fun r => A + b * (Y - r)) r := by fun_prop
      exact continuousAt_id.mul ((continuousAt_const.div (this.pow 2)
        (pow_ne_zero 2 hD.ne')).add (continuousAt_const.div this hD.ne'))
    · have hD := ksD_den_pos hA hb hr.2
      have hAD : A ≤ A + b * (Y - r) := by nlinarith [hr.2]
      simp only [ksDLinI]
      refine mul_le_mul_of_nonneg_left ?_ hr.1
      have h1 : 1 / (A + b * (Y - r)) ^ 2 ≤ A⁻¹ ^ 2 := by
        rw [inv_pow, ← one_div]
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hA.le hAD 2)
      have h2 : 2 * 1 / (A + b * (Y - r)) ≤ 2 * A⁻¹ := by
        have := one_div_le_one_div_of_le hA hAD
        rw [one_div, one_div] at this
        calc 2 * 1 / (A + b * (Y - r)) = 2 * (A + b * (Y - r))⁻¹ := by ring
          _ ≤ 2 * A⁻¹ := by linarith
      linarith
  refine hle.trans ?_
  rw [intervalIntegral.integral_mul_const, integral_id]
  have hAi : 0 ≤ A⁻¹ := inv_nonneg.2 hA.le
  have hY2 : Y ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hY2 (by positivity : (0 : ℝ) ≤ A⁻¹ ^ 2 + 2 * A⁻¹)]

theorem ksU_abs_ksDLin_le {A b Y : ℝ} (a₀ a₁ : ℝ) (hA : 0 < A) (hb : 0 < b) (hY : 0 ≤ Y) :
    |ksDLin A b Y a₀ a₁| ≤ (|a₀| + |a₁|) * ksDLin A b Y 1 1 := by
  have h10 := ksU_ksDLin_nonneg hA hb hY zero_le_one le_rfl
  have h01 := ksU_ksDLin_nonneg hA hb hY le_rfl zero_le_one
  have h11 : ksDLin A b Y 1 1 = ksDLin A b Y 1 0 + ksDLin A b Y 0 1 := by
    rw [ksU_ksDLin_split A b Y 1 1]; ring
  rw [ksU_ksDLin_split, h11]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg h10, abs_of_nonneg h01]
  nlinarith [abs_nonneg a₀, abs_nonneg a₁, mul_nonneg (abs_nonneg a₀) h01,
    mul_nonneg (abs_nonneg a₁) h10]

/-- The lower bound `kA = min(M², M² + s/4)` of `A(σ) = M² + σ(1 - σ)s` on `[0, 1]`. -/
noncomputable def ksUkA (M s : ℝ) : ℝ := min (M ^ 2) (M ^ 2 + s / 4)

theorem ksU_ksUkA_pos {M s : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s) : 0 < ksUkA M s :=
  lt_min (by positivity) (by linarith)

theorem ksU_kA_le_ksDA {M s σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) : ksUkA M s ≤ ksDA M s σ := by
  obtain ⟨h0, h1⟩ := hσ
  have hq : 0 ≤ σ * (1 - σ) := mul_nonneg h0 (by linarith)
  have hq4 : σ * (1 - σ) ≤ 1 / 4 := by nlinarith [sq_nonneg (σ - 1 / 2)]
  simp only [ksDA, ksUkA]
  rcases le_or_gt 0 s with hs0 | hs0
  · exact (min_le_left _ _).trans (by nlinarith [mul_nonneg hq hs0])
  · exact (min_le_right _ _).trans
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 4 - σ * (1 - σ)) (by linarith :
        0 ≤ -s)])

theorem ksU_ksDA_le {M s σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) : ksDA M s σ ≤ M ^ 2 + |s| := by
  obtain ⟨h0, h1⟩ := hσ
  have hq : 0 ≤ σ * (1 - σ) := mul_nonneg h0 (by linarith)
  have hq1 : σ * (1 - σ) ≤ 1 := by nlinarith
  simp only [ksDA]
  nlinarith [mul_le_mul_of_nonneg_left (le_abs_self s) hq, abs_nonneg s,
    mul_le_mul_of_nonneg_right hq1 (abs_nonneg s)]

theorem ksU_abs_ksDa0_le {M x s σ : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hσ : σ ∈ Icc (0 : ℝ) 1) :
    |ksDa0 M x s σ| ≤ 16 * (4 * M ^ 2 + |s|) := by
  obtain ⟨x0, x1⟩ := hx
  obtain ⟨h0, h1⟩ := hσ
  have hq : 0 ≤ σ * (1 - σ) := mul_nonneg h0 (by linarith)
  have hq1 : σ * (1 - σ) ≤ 1 := by nlinarith
  have hM : 0 ≤ M ^ 2 := sq_nonneg M
  have hc : 0 ≤ (1 - x) * σ ^ 2 := mul_nonneg (by linarith) (sq_nonneg σ)
  have hc1 : (1 - x) * σ ^ 2 ≤ 1 := by nlinarith [sq_nonneg σ]
  have hQ : |4 * M ^ 2 - (1 - x) * M ^ 2 + (1 - x) * σ ^ 2 * s| ≤ 4 * M ^ 2 + |s| := by
    have h1' : |(1 - x) * σ ^ 2 * s| ≤ |s| := by
      rw [abs_mul, abs_of_nonneg hc]
      nlinarith [abs_nonneg s]
    rw [abs_le] at h1' ⊢
    constructor <;> nlinarith
  simp only [ksDa0]
  rw [show 16 * σ * (1 - σ) * (4 * M ^ 2 - (1 - x) * M ^ 2 + (1 - x) * σ ^ 2 * s) =
    16 * (σ * (1 - σ)) * (4 * M ^ 2 - (1 - x) * M ^ 2 + (1 - x) * σ ^ 2 * s) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 16 * (σ * (1 - σ)))]
  nlinarith [abs_nonneg (4 * M ^ 2 - (1 - x) * M ^ 2 + (1 - x) * σ ^ 2 * s)]

theorem ksU_abs_ksDa1_le {x σ : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hσ : σ ∈ Icc (0 : ℝ) 1) :
    |ksDa1 x σ| ≤ 8 := by
  obtain ⟨x0, x1⟩ := hx
  obtain ⟨h0, h1⟩ := hσ
  have hp : |σ * (4 * σ - 3)| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (σ - 3 / 8)]
  simp only [ksDa1]
  rw [show -8 * (1 - x) * σ * (4 * σ - 3) = -8 * (1 - x) * (σ * (4 * σ - 3)) by ring,
    abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - x),
    show |(-8 : ℝ)| = 8 by norm_num]
  nlinarith [abs_nonneg (σ * (4 * σ - 3))]

/-! ### The node bound -/

/-- The node difference of the antiderivative: the photon-mass integral over `(0, Λ]` of the
`VA` integrand at the node `(x, σ)` with moments `a₀, a₁`. -/
noncomputable def ksUNodeD (M s x a₀ a₁ Λ σ : ℝ) : ℝ :=
  ksUPhi (ksDA M s σ) (ksDb M Λ x) (1 - σ) a₀ a₁ - ksUPhi (ksDA M s σ) (ksDb M 0 x) (1 - σ) a₀ a₁

/-- The integrable node weight `1 + x^{-1/2} + (1 - x)^{-1/2}`. -/
noncomputable def ksUg (x : ℝ) : ℝ := 1 + x ^ (-(1 / 2 : ℝ)) + (1 - x) ^ (-(1 / 2 : ℝ))

theorem ksU_integrableOn_ksUg : IntegrableOn ksUg (Ioo (0 : ℝ) 1) := by
  have h1 : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h2 : IntervalIntegrable (fun x : ℝ => (1 - x) ^ (-(1 / 2 : ℝ))) volume 0 1 := by
    simpa using (h1.comp_sub_left 1).symm
  rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  exact (intervalIntegrable_const.add h1).add h2

theorem ksU_rpow_neg_half_sq {t : ℝ} (ht : 0 < t) : (t ^ (-(1 / 2 : ℝ))) ^ 2 = t⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  norm_num [Real.rpow_neg_one]

theorem ksU_sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

theorem ksU_sqrt_le_mul_rpow {c t : ℝ} (hc : 0 ≤ c) (ht : 0 < t) :
    Real.sqrt (c / t) ≤ Real.sqrt c * t ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_le_iff]
  refine ⟨mul_nonneg (Real.sqrt_nonneg c) (Real.rpow_nonneg ht.le _), ?_⟩
  rw [mul_pow, Real.sq_sqrt hc, ksU_rpow_neg_half_sq ht, div_eq_mul_inv]

/-- **The node bound of the photon-mass integral**: for `M > 0`, `s > -4M²`, `x, σ ∈ (0, 1)`,
`Λ ≥ 0`, the node difference is at most `C (|a₀| + |a₁|) (1 + x^{-1/2} + (1 - x)^{-1/2})`. -/
theorem ksU_abs_ksUNodeD_le {M s x σ Λ : ℝ} (a₀ a₁ : ℝ) (hM : 0 < M) (hs : -(4 * M ^ 2) < s)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hσ : σ ∈ Ioo (0 : ℝ) 1) (hΛ : 0 ≤ Λ) :
    |ksUNodeD M s x a₀ a₁ Λ σ| ≤ 160 * (|a₀| + |a₁|) * (2 + M ^ 2 + |s| + (ksUkA M s)⁻¹) ^ 2 *
      (2 + 2 * M + Real.sqrt Λ) * ksUg x := by
  have hσI : σ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hσ
  have hA := ksD_ksDA_pos hM hs hσI
  have hkA := ksU_ksUkA_pos hM hs
  have hY : 0 < 1 - σ := by linarith [hσ.2]
  have hY1 : 1 - σ ≤ 1 := by linarith [hσ.1]
  have hx0 := hx.1
  have h1x : 0 < 1 - x := by linarith [hx.2]
  have hB := ksU_ksDb_pos hM hx hΛ
  have hb0 := ksU_ksDb_pos hM hx le_rfl
  set A := ksDA M s σ
  set W := 2 + A + A⁻¹ with hW
  set Wb := 2 + M ^ 2 + |s| + (ksUkA M s)⁻¹ with hWb
  set K := |a₀| + |a₁| with hK
  have hK0 : 0 ≤ K := by positivity
  have hWle : W ^ 2 ≤ Wb ^ 2 := by
    have h1 : A ≤ M ^ 2 + |s| := ksU_ksDA_le hσI
    have h2 : A⁻¹ ≤ (ksUkA M s)⁻¹ := inv_anti₀ hkA (ksU_kA_le_ksDA hσI)
    exact pow_le_pow_left₀ (by positivity) (by rw [hW, hWb]; linarith) 2
  have hPhi : ∀ b, 0 < b → |ksUPhi A b (1 - σ) a₀ a₁| ≤ 160 * K * Wb ^ 2 * (1 + Real.sqrt b) :=
    fun b hb => by
      refine (ksU_abs_ksUPhi_le a₀ a₁ hA hb hY hY1).trans ?_
      have h1 := ksU_one_add_log_sq_le hb.le
      have h2 : 0 ≤ (1 + Real.log (1 + b)) ^ 2 := sq_nonneg _
      calc 10 * K * W ^ 2 * (1 + Real.log (1 + b)) ^ 2
          ≤ 10 * K * Wb ^ 2 * (16 * (1 + Real.sqrt b)) := by gcongr
        _ = 160 * K * Wb ^ 2 * (1 + Real.sqrt b) := by ring
  set p := (1 - x) ^ (-(1 / 2 : ℝ)) with hp
  set q := x ^ (-(1 / 2 : ℝ)) with hq
  have hp0 : 0 ≤ p := Real.rpow_nonneg h1x.le _
  have hq0 : 0 ≤ q := Real.rpow_nonneg hx0.le _
  have hsb0 : Real.sqrt (ksDb M 0 x) ≤ M * p := by
    rw [ksU_ksDb_zero hx]
    refine (Real.sqrt_le_sqrt (?_ : M ^ 2 * x / (1 - x) ≤ M ^ 2 / (1 - x))).trans ?_
    · gcongr; nlinarith [sq_nonneg M, hx.2]
    · refine (ksU_sqrt_le_mul_rpow (sq_nonneg M) h1x).trans_eq ?_
      rw [Real.sqrt_sq hM.le]
  have hsB : Real.sqrt (ksDb M Λ x) ≤ M * p + Real.sqrt Λ * q := by
    rw [ksU_ksDb_eq, add_comm]
    refine (ksU_sqrt_add_le hb0.le (div_nonneg hΛ hx0.le)).trans ?_
    linarith [ksU_sqrt_le_mul_rpow hΛ hx0]
  have hsq : 0 ≤ Real.sqrt Λ := Real.sqrt_nonneg Λ
  have hC : 0 ≤ 160 * K * Wb ^ 2 := by positivity
  unfold ksUNodeD
  refine (abs_sub _ _).trans ?_
  refine (add_le_add (hPhi _ hB) (hPhi _ hb0)).trans ?_
  have hlin : 1 + Real.sqrt (ksDb M Λ x) + (1 + Real.sqrt (ksDb M 0 x)) ≤
      (2 + 2 * M + Real.sqrt Λ) * ksUg x := by
    rw [ksUg, ← hp, ← hq]
    nlinarith [mul_nonneg hM.le hp0, mul_nonneg hM.le hq0, mul_nonneg hsq hp0]
  calc 160 * K * Wb ^ 2 * (1 + Real.sqrt (ksDb M Λ x)) +
        160 * K * Wb ^ 2 * (1 + Real.sqrt (ksDb M 0 x))
      = 160 * K * Wb ^ 2 * (1 + Real.sqrt (ksDb M Λ x) + (1 + Real.sqrt (ksDb M 0 x))) := by
        ring
    _ ≤ 160 * K * Wb ^ 2 * ((2 + 2 * M + Real.sqrt Λ) * ksUg x) := by gcongr
    _ = _ := by ring

/-! ### The interchange at a fixed outer node -/

theorem ksU_measurable_ksDLin {γ : Type*} [MeasurableSpace γ] {A b Y a₀ a₁ : γ → ℝ}
    (hA : Measurable A) (hb : Measurable b) (hY : Measurable Y) (ha₀ : Measurable a₀)
    (ha₁ : Measurable a₁) : Measurable fun z => ksDLin (A z) (b z) (Y z) (a₀ z) (a₁ z) := by
  unfold ksDLin
  fun_prop

/-- The photon-mass integral of one node with general moments (`ksU_integral_ksDYA` with
`A > 0`, `Y > 0`, `a₀`, `a₁` arbitrary). -/
theorem ksU_integral_node {M x A Y Λ : ℝ} (a₀ a₁ : ℝ) (hM : 0 < M) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hA : 0 < A) (hY : 0 < Y) (hΛ : 0 ≤ Λ) :
    ∫ u in (0 : ℝ)..Λ, x⁻¹ * ksDLin A (ksDb M u x) Y a₀ a₁ =
      ksUPhi A (ksDb M Λ x) Y a₀ a₁ - ksUPhi A (ksDb M 0 x) Y a₀ a₁ := by
  have hx0 := hx.1
  set d := ksDb M 0 x with hd
  have hsub : ∫ u in (0 : ℝ)..Λ, x⁻¹ * ksDLin A (ksDb M u x) Y a₀ a₁ =
      x⁻¹ * (x • ∫ b in 0 / x + d..Λ / x + d, ksDLin A b Y a₀ a₁) := by
    rw [intervalIntegral.integral_const_mul, ← intervalIntegral.integral_comp_div_add
      (f := fun b => ksDLin A b Y a₀ a₁) hx0.ne' d]
    simp only [← ksU_ksDb_eq, hd]
  rw [hsub, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hx0.ne', one_mul,
    ksU_integral_ksDLin _ _ hA (by rw [← ksU_ksDb_eq]; exact ksU_ksDb_pos hM hx le_rfl)
      (by gcongr) hY, ← ksU_ksDb_eq, ← ksU_ksDb_eq]

theorem ksU_ae_mem_prod {Λ : ℝ} :
    ∀ᵐ p ∂((volume.restrict (Ioc (0 : ℝ) Λ)).prod (volume.restrict (Ioo (0 : ℝ) 1))),
      p ∈ Ioc (0 : ℝ) Λ ×ˢ Ioo (0 : ℝ) 1 := by
  rw [Measure.prod_restrict]
  exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioo)

/-- The `VA` integrand at a fixed outer node `x` with moment functions `α`, `β`. -/
noncomputable def ksUNodeF (M s x : ℝ) (α β : ℝ → ℝ) (u σ : ℝ) : ℝ :=
  x⁻¹ * ksDLin (ksDA M s σ) (ksDb M u x) (1 - σ) (α σ) (β σ)

theorem ksU_integrable_ksUNodeF {M s x Λ K : ℝ} {α β : ℝ → ℝ} (hM : 0 < M)
    (hs : -(4 * M ^ 2) < s) (hx : x ∈ Ioo (0 : ℝ) 1) (hα : Measurable α) (hβ : Measurable β)
    (hK : ∀ σ ∈ Icc (0 : ℝ) 1, |α σ| + |β σ| ≤ K) :
    Integrable (Function.uncurry (ksUNodeF M s x α β))
      ((volume.restrict (Ioc (0 : ℝ) Λ)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hmeas : Measurable (Function.uncurry (ksUNodeF M s x α β)) := by
    have : Measurable fun p : ℝ × ℝ =>
        ksDLin (ksDA M s p.2) (ksDb M p.1 x) (1 - p.2) (α p.2) (β p.2) :=
      ksU_measurable_ksDLin (by unfold ksDA; fun_prop) (by unfold ksDb; fun_prop)
        (by fun_prop) (hα.comp measurable_snd) (hβ.comp measurable_snd)
    exact measurable_const.mul this
  refine Integrable.of_bound hmeas.aestronglyMeasurable
    (x⁻¹ * (K * (1 + (ksUkA M s)⁻¹) ^ 2)) ?_
  filter_upwards [ksU_ae_mem_prod] with p hp
  obtain ⟨⟨hu0, -⟩, hσ⟩ := hp
  have hσI : p.2 ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hσ
  have hA := ksD_ksDA_pos hM hs hσI
  have hb := ksU_ksDb_pos hM hx hu0.le
  have hY : 0 ≤ 1 - p.2 := by linarith [hσ.2]
  have hkA := ksU_ksUkA_pos hM hs
  have hAi : (ksDA M s p.2)⁻¹ ≤ (ksUkA M s)⁻¹ := inv_anti₀ hkA (ksU_kA_le_ksDA hσI)
  have h11 := ksU_ksDLin_one_one_le hA hb hY (by linarith [hσ.1])
  have h11' : (1 + (ksDA M s p.2)⁻¹) ^ 2 ≤ (1 + (ksUkA M s)⁻¹) ^ 2 :=
    pow_le_pow_left₀ (by have := inv_pos.2 hA; positivity) (by linarith) 2
  have hL := ksU_abs_ksDLin_le (α p.2) (β p.2) hA hb hY
  have hL0 := ksU_ksDLin_nonneg hA hb hY zero_le_one zero_le_one
  have hKp := hK p.2 hσI
  simp only [ksUNodeF, Function.uncurry, Real.norm_eq_abs, abs_mul,
    abs_of_pos (inv_pos.2 hx.1)]
  refine mul_le_mul_of_nonneg_left (hL.trans ?_) (inv_pos.2 hx.1).le
  calc (|α p.2| + |β p.2|) * ksDLin (ksDA M s p.2) (ksDb M p.1 x) (1 - p.2) 1 1
      ≤ K * (1 + (ksUkA M s)⁻¹) ^ 2 := by
        refine mul_le_mul hKp (h11.trans h11') hL0 ?_
        linarith [abs_nonneg (β p.2), abs_nonneg (α p.2)]

/-- **The interchange at a fixed outer node**: the photon-mass integral over `(0, Λ]` and the
`σ`-integral commute, and the photon-mass integral is the node difference `ksUNodeD`. -/
theorem ksU_node_swap {M s x Λ K : ℝ} {α β : ℝ → ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hΛ : 0 ≤ Λ) (hα : Measurable α) (hβ : Measurable β)
    (hK : ∀ σ ∈ Icc (0 : ℝ) 1, |α σ| + |β σ| ≤ K) :
    ∫ u in Ioc (0 : ℝ) Λ, ∫ σ in Ioo (0 : ℝ) 1, ksUNodeF M s x α β u σ =
      ∫ σ in Ioo (0 : ℝ) 1, ksUNodeD M s x (α σ) (β σ) Λ σ := by
  rw [integral_integral_swap (ksU_integrable_ksUNodeF hM hs hx hα hβ hK)]
  refine setIntegral_congr_fun measurableSet_Ioo fun σ hσ => ?_
  rw [← intervalIntegral.integral_of_le hΛ]
  exact ksU_integral_node _ _ hM hx (ksD_ksDA_pos hM hs (Ioo_subset_Icc_self hσ))
    (by linarith [hσ.2]) hΛ

theorem ksU_integrableOn_ksUNodeD {M s x Λ K : ℝ} {α β : ℝ → ℝ} (hM : 0 < M)
    (hs : -(4 * M ^ 2) < s) (hx : x ∈ Ioo (0 : ℝ) 1) (hΛ : 0 ≤ Λ) (hα : Measurable α)
    (hβ : Measurable β) (hK : ∀ σ ∈ Icc (0 : ℝ) 1, |α σ| + |β σ| ≤ K) :
    IntegrableOn (fun σ => ksUNodeD M s x (α σ) (β σ) Λ σ) (Ioo (0 : ℝ) 1) := by
  have h := (ksU_integrable_ksUNodeF (Λ := Λ) hM hs hx hα hβ hK).integral_prod_right
  refine IntegrableOn.congr_fun h (fun σ hσ => ?_) measurableSet_Ioo
  simp only [Function.uncurry_apply_pair]
  rw [← intervalIntegral.integral_of_le hΛ]
  exact ksU_integral_node _ _ hM hx (ksD_ksDA_pos hM hs (Ioo_subset_Icc_self hσ))
    (by linarith [hσ.2]) hΛ

end QED.ChainProof.SetAKS

end
