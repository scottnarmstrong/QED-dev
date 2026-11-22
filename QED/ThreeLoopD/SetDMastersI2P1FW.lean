/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Set (d), master `I₂`: the one-dimensional integrals of the simplex step of the `ℱ`-part

At fixed `q = s + α₁ α₃` the simplex integral of the slice length `len(q - α₁ α₃)` splits into
three terms of the form `min(1 / (q - C), 1 / A')`. Each is reduced to a one-dimensional integral
of a logarithm; here we compute the inner integrals:

* with `K = u (1 - u)` (`u = α₁`, `v = α₃`, `A = u (1 - u - v) = K - u v`),
  `∫₀^{1-u} 1[u v < q] min(1 / (q - u v), 1 / A) dv = g(q / K) / u`,
  `g(ρ) = -log (1 - ρ)` (`ρ < 1`), `g(ρ) = -log (1 - 1 / ρ)` (`ρ ≥ 1`);
* in the coordinates `α₁ = σ ξ`, `α₃ = σ (1 - ξ)`, `k = ξ (1 - ξ)`,
  `∫₀¹ σ 1[σ² k < q] min(1 / (q - σ² k), 1 / (σ k (1 - σ))) dσ = h(q / k) / k`,
  `h(ρ) = log (1 - ρ) / 2 - log (1 - √ρ)` (`ρ < 1`), `h(ρ) = -log (1 - 1 / ρ) / 2` (`ρ ≥ 1`).

## Main definitions

* `QED.ThreeLoopD.i2P1Fgr`, `QED.ThreeLoopD.i2P1Fhr`.

## Main results

* `QED.ThreeLoopD.i2P1FW_one`, `QED.ThreeLoopD.i2P1FW_three`.
-/

@[expose] public section

open Real Set MeasureTheory Filter
open scoped ENNReal

namespace QED.ThreeLoopD

/-- `g(ρ) = -log (1 - ρ)` for `ρ < 1`, `-log (1 - 1 / ρ)` for `ρ ≥ 1`. -/
noncomputable def i2P1Fgr (ρ : ℝ) : ℝ := if ρ < 1 then -log (1 - ρ) else -log (1 - 1 / ρ)

/-- `h(ρ) = log (1 - ρ) / 2 - log (1 - √ρ)` for `ρ < 1`, `-log (1 - 1 / ρ) / 2` for `ρ ≥ 1`. -/
noncomputable def i2P1Fhr (ρ : ℝ) : ℝ :=
  if ρ < 1 then log (1 - ρ) / 2 - log (1 - Real.sqrt ρ) else -log (1 - 1 / ρ) / 2

/-- The fundamental theorem of calculus for a lower integral over `(a, b)`. -/
theorem i2P1FW_ftc {f F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (f x) x) (hf : ContinuousOn f (Icc a b))
    (hnn : ∀ x ∈ Ioo a b, 0 ≤ f x) :
    ∫⁻ x in Ioo a b, ENNReal.ofReal (f x) = ENNReal.ofReal (F b - F a) := by
  have hi : IntegrableOn f (Icc a b) := hf.integrableOn_Icc
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hF x (by rwa [uIcc_of_le hab] at hx)) (hf.intervalIntegrable_of_Icc hab),
    intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    ofReal_integral_eq_lintegral_ofReal (hi.mono_set Ioo_subset_Icc_self)
      ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall hnn))]

theorem i2P1FW_disj (a b c : ℝ) : Disjoint (Ioo a b) (Ico b c) :=
  Set.disjoint_left.2 fun _ h1 h2 => absurd h2.1 (not_le.2 h1.2)

/-- `∫ₐᵇ dv / (c - u v) = (log (c - u a) - log (c - u b)) / u`. -/
theorem i2P1FW_lin {u c a b : ℝ} (hu : 0 < u) (hab : a ≤ b) (hc : 0 < c - u * b) :
    ∫⁻ v in Ioo a b, ENNReal.ofReal (1 / (c - u * v)) =
      ENNReal.ofReal ((log (c - u * a) - log (c - u * b)) / u) := by
  have hpos : ∀ v ∈ Icc a b, 0 < c - u * v := fun v hv => by nlinarith [hv.2]
  rw [i2P1FW_ftc (f := fun v => 1 / (c - u * v)) (F := fun v => -log (c - u * v) / u) hab
    (fun v hv => ?_)
    (continuousOn_const.div (by fun_prop) fun v hv => (hpos v hv).ne')
    (fun v hv => (one_div_pos.2 (hpos v (Ioo_subset_Icc_self hv))).le)]
  · congr 1
    ring
  · have h := ((((hasDerivAt_id v).const_mul u).const_sub c).log (hpos v hv).ne').neg.div_const u
    refine h.congr_deriv ?_
    simp only [id]
    field_simp [(hpos v hv).ne']

/-- **Terms one and two at fixed `α₁ = u`**: with `K = u (1 - u)`,
`∫₀^{1-u} 1[u v < q] min(1 / (q - u v), 1 / (u (1 - u - v))) dv = g(q / K) / u` (`q ≠ K`). -/
theorem i2P1FW_one {q u : ℝ} (hq : 0 < q) (hu : u ∈ Ioo (0 : ℝ) 1) (hne : q ≠ u * (1 - u)) :
    ∫⁻ v in Ioo (0 : ℝ) (1 - u), (if u * v < q then
        ENNReal.ofReal (min (1 / (q - u * v)) (1 / (u * (1 - u - v)))) else 0) =
      ENNReal.ofReal (i2P1Fgr (q / (u * (1 - u))) / u) := by
  obtain ⟨hu0, hu1⟩ := hu
  have hK : 0 < u * (1 - u) := mul_pos hu0 (by linarith)
  rcases lt_or_gt_of_ne hne with h | h
  · have hqu : q / u < 1 - u := by rw [div_lt_iff₀ hu0]; linarith
    have hq0 : 0 < q / u := div_pos hq hu0
    rw [← Ioo_union_Ico_eq_Ioo hq0 hqu.le, lintegral_union measurableSet_Ico (i2P1FW_disj _ _ _)]
    have e2 : ∫⁻ v in Ico (q / u) (1 - u), (if u * v < q then
        ENNReal.ofReal (min (1 / (q - u * v)) (1 / (u * (1 - u - v)))) else 0) = 0 := by
      rw [setLIntegral_congr_fun measurableSet_Ico (g := fun _ => 0) fun v hv => ?_]
      · simp
      · have := hv.1
        rw [div_le_iff₀ hu0] at this
        rw [ite_eq_right (by linarith)]
    have e1 : ∫⁻ v in Ioo 0 (q / u), (if u * v < q then
        ENNReal.ofReal (min (1 / (q - u * v)) (1 / (u * (1 - u - v)))) else 0) =
        ∫⁻ v in Ioo 0 (q / u), ENNReal.ofReal (1 / (u * (1 - u) - u * v)) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
      have huv : u * v < q := by have := hv.2; rw [lt_div_iff₀ hu0] at this; linarith
      rw [ite_eq_left huv, min_eq_right]
      · congr 2
        ring
      · exact one_div_le_one_div_of_le (by linarith) (by nlinarith)
    rw [e2, add_zero, e1, i2P1FW_lin hu0 hq0.le (by rw [mul_div_cancel₀ _ hu0.ne']; linarith),
      i2P1Fgr, ite_eq_left ((div_lt_one hK).2 h), mul_zero, sub_zero, mul_div_cancel₀ _ hu0.ne',
      show 1 - q / (u * (1 - u)) = (u * (1 - u) - q) / (u * (1 - u)) by field_simp,
      log_div (by linarith) hK.ne']
    congr 1
    ring
  · have e1 : ∫⁻ v in Ioo 0 (1 - u), (if u * v < q then
        ENNReal.ofReal (min (1 / (q - u * v)) (1 / (u * (1 - u - v)))) else 0) =
        ∫⁻ v in Ioo 0 (1 - u), ENNReal.ofReal (1 / (q - u * v)) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
      have huv : u * v < u * (1 - u) := mul_lt_mul_of_pos_left hv.2 hu0
      rw [ite_eq_left (by linarith), min_eq_left]
      exact one_div_le_one_div_of_le (mul_pos hu0 (by linarith [hv.2])) (by nlinarith)
    rw [e1, i2P1FW_lin hu0 (by linarith) (by linarith), i2P1Fgr,
      ite_eq_right (not_lt.2 ((one_le_div hK).2 h.le)), mul_zero, sub_zero, one_div_div,
      show 1 - u * (1 - u) / q = (q - u * (1 - u)) / q by field_simp,
      log_div (by linarith) hq.ne']
    congr 1
    ring

/-- `∫ₐᵇ σ dσ / (q - σ² k) = (log (q - a² k) - log (q - b² k)) / (2 k)`. -/
theorem i2P1FW_quad {q k a b : ℝ} (hk : 0 < k) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : 0 < q - b ^ 2 * k) :
    ∫⁻ σ in Ioo a b, ENNReal.ofReal (σ / (q - σ ^ 2 * k)) =
      ENNReal.ofReal ((log (q - a ^ 2 * k) - log (q - b ^ 2 * k)) / (2 * k)) := by
  have hpos : ∀ σ ∈ Icc a b, 0 < q - σ ^ 2 * k := fun σ hσ => by
    have : σ ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (ha.trans hσ.1) hσ.2 2
    nlinarith
  rw [i2P1FW_ftc (f := fun σ => σ / (q - σ ^ 2 * k)) (F := fun σ => -log (q - σ ^ 2 * k) / (2 * k))
    hab (fun σ hσ => ?_) (continuousOn_id.div (by fun_prop) fun σ hσ => (hpos σ hσ).ne')
    (fun σ hσ => div_nonneg (ha.trans hσ.1.le) (hpos σ (Ioo_subset_Icc_self hσ)).le)]
  · congr 1
    ring
  · have h := ((((hasDerivAt_id σ).pow 2).mul_const k).const_sub q |>.log
      (hpos σ hσ).ne').neg.div_const (2 * k)
    refine h.congr_deriv ?_
    simp only [id, Pi.pow_apply]
    field_simp [(hpos σ hσ).ne']
    ring

/-- **Term three at fixed `ξ`**: with `k = ξ (1 - ξ)`,
`∫₀¹ σ 1[σ² k < q] min(1 / (q - σ² k), 1 / (σ k (1 - σ))) dσ = h(q / k) / k` (`q ≠ k`). -/
theorem i2P1FW_three {q k : ℝ} (hq : 0 < q) (hk : 0 < k) (hne : q ≠ k) :
    ∫⁻ σ in Ioo (0 : ℝ) 1, (if σ ^ 2 * k < q then
        ENNReal.ofReal (σ * min (1 / (q - σ ^ 2 * k)) (1 / (σ * k * (1 - σ)))) else 0) =
      ENNReal.ofReal (i2P1Fhr (q / k) / k) := by
  obtain ⟨ρ, rfl⟩ : ∃ ρ, q = ρ * k := ⟨q / k, by field_simp⟩
  have hρ0 : 0 < ρ := pos_of_mul_pos_left hq hk.le
  rw [show ρ * k / k = ρ by field_simp]
  rcases lt_or_gt_of_ne hne with h | h
  · have hρ1 : ρ < 1 := by nlinarith
    set r := Real.sqrt ρ with hr
    have hr0 : 0 < r := Real.sqrt_pos.2 hρ0
    have hr2 : r ^ 2 = ρ := Real.sq_sqrt hρ0.le
    have hr1 : r < 1 := by nlinarith
    have hρr : ρ < r := by nlinarith
    rw [← Ioo_union_Ico_eq_Ioo hρ0 hρ1.le, lintegral_union measurableSet_Ico (i2P1FW_disj _ _ _),
      setLIntegral_congr (Ioo_ae_eq_Ico (a := ρ) (b := 1)).symm,
      ← Ioo_union_Ico_eq_Ioo hρr hr1.le, lintegral_union measurableSet_Ico (i2P1FW_disj _ _ _)]
    have e3 : ∫⁻ σ in Ico r 1, (if σ ^ 2 * k < ρ * k then
        ENNReal.ofReal (σ * min (1 / (ρ * k - σ ^ 2 * k)) (1 / (σ * k * (1 - σ)))) else 0) =
        0 := by
      rw [setLIntegral_congr_fun measurableSet_Ico (g := fun _ => 0) fun σ hσ => ?_]
      · simp
      · have : r ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ hr0.le hσ.1 2
        rw [ite_eq_right (by nlinarith)]
    have e1 : ∫⁻ σ in Ioo 0 ρ, (if σ ^ 2 * k < ρ * k then
        ENNReal.ofReal (σ * min (1 / (ρ * k - σ ^ 2 * k)) (1 / (σ * k * (1 - σ)))) else 0) =
        ∫⁻ σ in Ioo 0 ρ, ENNReal.ofReal (σ / (ρ * k - σ ^ 2 * k)) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun σ hσ => ?_
      obtain ⟨h0, h1⟩ := hσ
      have hs2 : σ ^ 2 < ρ := by nlinarith
      rw [ite_eq_left (by nlinarith), min_eq_left, mul_one_div]
      exact one_div_le_one_div_of_le (by have := mul_pos h0 hk; nlinarith) (by nlinarith)
    have e2 : ∫⁻ σ in Ioo ρ r, (if σ ^ 2 * k < ρ * k then
        ENNReal.ofReal (σ * min (1 / (ρ * k - σ ^ 2 * k)) (1 / (σ * k * (1 - σ)))) else 0) =
        ∫⁻ σ in Ioo ρ r, ENNReal.ofReal (1 / (k - k * σ)) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun σ hσ => ?_
      obtain ⟨h0, h1⟩ := hσ
      have hσ0 : 0 < σ := hρ0.trans h0
      have hs2 : σ ^ 2 < ρ := by nlinarith
      rw [ite_eq_left (by nlinarith), min_eq_right]
      · congr 1
        field_simp
      · exact one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
    rw [e3, add_zero, e1, e2, i2P1FW_quad hk le_rfl hρ0.le (by nlinarith),
      i2P1FW_lin hk hρr.le (by nlinarith), ← ENNReal.ofReal_add, i2P1Fhr, ite_eq_left hρ1]
    · congr 1
      rw [show ρ * k - ρ ^ 2 * k = ρ * k * (1 - ρ) by ring,
        show k - k * ρ = k * (1 - ρ) by ring, show k - k * r = k * (1 - r) by ring,
        log_mul (by positivity) (by linarith), log_mul hk.ne' (by linarith),
        log_mul hk.ne' (by linarith)]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, sub_zero]
      field_simp
      ring
    · refine div_nonneg (sub_nonneg.2 (log_le_log (by nlinarith) (by nlinarith))) (by positivity)
    · exact div_nonneg (sub_nonneg.2 (log_le_log (by nlinarith) (by nlinarith))) hk.le
  · have hρ1 : 1 < ρ := by nlinarith
    have e1 : ∫⁻ σ in Ioo 0 1, (if σ ^ 2 * k < ρ * k then
        ENNReal.ofReal (σ * min (1 / (ρ * k - σ ^ 2 * k)) (1 / (σ * k * (1 - σ)))) else 0) =
        ∫⁻ σ in Ioo 0 1, ENNReal.ofReal (σ / (ρ * k - σ ^ 2 * k)) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun σ hσ => ?_
      obtain ⟨h0, h1⟩ := hσ
      have hs2 : σ ^ 2 < 1 := by nlinarith
      rw [ite_eq_left (by nlinarith), min_eq_left, mul_one_div]
      exact one_div_le_one_div_of_le (by have := mul_pos h0 hk; nlinarith) (by nlinarith)
    rw [e1, i2P1FW_quad hk le_rfl zero_le_one (by nlinarith), i2P1Fhr,
      ite_eq_right (not_lt.2 hρ1.le)]
    congr 1
    rw [show 1 - 1 / ρ = (ρ - 1) / ρ by field_simp, log_div (by linarith) hρ0.ne',
      show ρ * k - 1 ^ 2 * k = k * (ρ - 1) by ring, log_mul hk.ne' (by linarith),
      show ρ * k - 0 ^ 2 * k = ρ * k by ring, log_mul hρ0.ne' hk.ne']
    field_simp
    ring

end QED.ThreeLoopD
