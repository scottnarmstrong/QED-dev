/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RHighSParK
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Set (d), master `I₁₂`: the coefficient `K₁` in closed form

The piece `Qreg` of the bad part of the bulk term of `I₁₂` contains the parametric integral
`K(z) = ∫₀¹ c^{-ε-1} (φ(z/c) - a (z/c)^{-3ε}) dρ`, `c = ρ(2 - ρ)/4`, `a = 2 - 3ε`,
`φ(r) = ((1 + r)^a - r^a - 1)/r`. Its order-0 coefficient vanishes and its order-1 coefficient is
`K₁(z) = ∫₀¹ ψ₁(z/c)/c dρ` (`i12HSQK1`). In `σ = 1 - ρ`, `t = 1 - σ² = 4c` and `q = 4z = ξ² - 1`
(`ξ = √(1 + 4z) = 1/x`), `K₁ = -(12/q) ∫₀¹ f` with
`f = log q - log t - q/t + (q + t)²/t² log ((q + t)/q)` (`i12HSQK1_eq_integral`). An integration
by parts in `σ` (`hasDerivAt_i12HSQKh`; the boundary term tends to `q/2` at `σ = 1`) reduces
`∫ f` to an elementary integral and the weight-2 integral `W(1/ξ)` of
`QED.ThreeLoopD.SetDMastersI12RHighSParK`, giving (`i12HSQK1_closed`)

  `K₁ = -(12/q) (log q - 2 log 2 + ξ(3 - ξ²)/2 log ((ξ + 1)/(ξ - 1))`
        `+ q(ξ² + 3) log² ((1 - x)/(1 + x))/8 + q/2)`.

In `y = (1 - x)/(1 + x) = w/(1 + w)` (`z = w(1 + w)`) only `log y` and `log (1 - y)` occur:
`K₁` has weight `≤ 2` with letters `{0, 1}`. (Check: `K₁(2) = -6 + 12 log 2 - 18 log² 2`.)

## Main definitions

* `QED.ThreeLoopD.i12HSQKpsi`, `QED.ThreeLoopD.i12HSQK1`.

## Main results

* `QED.ThreeLoopD.i12HSQK1_eq_integral`, `QED.ThreeLoopD.integral_i12HSQKf`,
  `QED.ThreeLoopD.i12HSQK1_closed`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ThreeLoopD

open QED.Polylog.ParamHPL

/-- `ψ₁(r) = [ε¹](φ(r) - a r^{-3ε}) = -3((1 + r)² log (1 + r) - r² log r)/r + 3 + 6 log r`. -/
noncomputable def i12HSQKpsi (r : ℝ) : ℝ :=
  -3 * ((1 + r) ^ 2 * log (1 + r) - r ^ 2 * log r) / r + 3 + 6 * log r

/-- The reduced integrand `log q - log t - q/t + (q + t)²/t² (log (q + t) - log q)`. -/
noncomputable def i12HSQKf (q t : ℝ) : ℝ :=
  log q - log t - q / t + (q + t) ^ 2 / t ^ 2 * (log (q + t) - log q)

theorem i12HSQKpsi_div {q t : ℝ} (hq : 0 < q) (ht : 0 < t) :
    i12HSQKpsi (q / t) / (t / 4) = -(12 / q) * i12HSQKf q t := by
  have e1 : 1 + q / t = (q + t) / t := by field_simp; ring
  unfold i12HSQKpsi i12HSQKf
  rw [e1, log_div (by positivity) ht.ne', log_div hq.ne' ht.ne']
  field_simp
  ring

/-- `1 ≤ (q + t)²/t² log ((q + t)/q) - q/t ≤ 2 + t/q` for `q, t > 0`. -/
theorem i12HSQK_B_lam_bounds {q t : ℝ} (hq : 0 < q) (ht : 0 < t) :
    1 ≤ (q + t) ^ 2 / t ^ 2 * (log (q + t) - log q) - q / t ∧
      (q + t) ^ 2 / t ^ 2 * (log (q + t) - log q) - q / t ≤ 2 + t / q := by
  have hqt : 0 < q + t := by linarith
  rw [← log_div hqt.ne' hq.ne']
  have hx : 0 < (q + t) / q := by positivity
  have up := log_le_sub_one_of_pos hx
  have lo := one_sub_inv_le_log_of_pos hx
  have e1 : (q + t) / q - 1 = t / q := by field_simp; ring
  have e2 : 1 - ((q + t) / q)⁻¹ = t / (q + t) := by field_simp; ring
  rw [e1] at up
  rw [e2] at lo
  have hB : 0 ≤ (q + t) ^ 2 / t ^ 2 := by positivity
  constructor
  · have := mul_le_mul_of_nonneg_left lo hB
    have e3 : (q + t) ^ 2 / t ^ 2 * (t / (q + t)) = q / t + 1 := by field_simp
    linarith
  · have := mul_le_mul_of_nonneg_left up hB
    have e3 : (q + t) ^ 2 / t ^ 2 * (t / q) = q / t + 2 + t / q := by field_simp; ring
    linarith

/-- The log-power bound for the reduced integrand. -/
theorem abs_i12HSQKf_le {q σ : ℝ} (hq : 0 < q) (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    |i12HSQKf q (1 - σ ^ 2)| ≤
      1 * (|log q| + log 2 + 2 + 1 / q + |log σ| + |log (1 - σ)|) ^ 1 := by
  have ht : 0 < 1 - σ ^ 2 := by nlinarith [hσ.1, hσ.2]
  have hb := i12HSQK_B_lam_bounds hq ht
  have e : log (1 - σ ^ 2) = log (1 - σ) + log (1 + σ) := by
    rw [← log_mul (by linarith [hσ.2]) (by linarith [hσ.1])]; ring_nf
  have l1 : 0 ≤ log (1 + σ) := log_nonneg (by linarith [hσ.1])
  have l2 : log (1 + σ) ≤ log 2 := log_le_log (by linarith [hσ.1]) (by linarith [hσ.2])
  have htq : (1 - σ ^ 2) / q ≤ 1 / q := div_le_div_of_nonneg_right (by nlinarith) hq.le
  have a1 := neg_abs_le (log q)
  have a2 := le_abs_self (log q)
  have a3 := neg_abs_le (log (1 - σ))
  have a4 := le_abs_self (log (1 - σ))
  have a5 := abs_nonneg (log σ)
  have a6 : 0 ≤ 1 / q := by positivity
  unfold i12HSQKf
  rw [one_mul, pow_one, abs_le, e]
  constructor <;> linarith [hb.1, hb.2]

/-- The elementary part `e(σ)` of the reduced integrand (`q = ξ² - 1`). -/
noncomputable def i12HSQKe (ξ σ : ℝ) : ℝ :=
  log (ξ ^ 2 - 1) - log (1 - σ ^ 2) - (ξ ^ 2 - 1) * ξ ^ 2 / (ξ ^ 2 - σ ^ 2) +
    2 * σ ^ 2 / (ξ ^ 2 - σ ^ 2)

/-- The boundary function `Q(σ) λ(σ)` of the integration by parts. -/
noncomputable def i12HSQKh (ξ σ : ℝ) : ℝ :=
  (σ + (ξ ^ 2 - 1) ^ 2 * σ / (2 * (1 - σ ^ 2)) +
      (2 * (ξ ^ 2 - 1) + (ξ ^ 2 - 1) ^ 2 / 2) * i12HSQKA σ) *
    (log (ξ ^ 2 - σ ^ 2) - log (ξ ^ 2 - 1))

/-- **The integration by parts identity:** `f = e + q(ξ² + 3) A(σ) σ/(ξ² - σ²) + ∂_σ(Q λ)`. -/
theorem hasDerivAt_i12HSQKh {ξ σ : ℝ} (hξ : 1 < ξ) (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i12HSQKh ξ) (i12HSQKf (ξ ^ 2 - 1) (1 - σ ^ 2) - i12HSQKe ξ σ -
      (ξ ^ 2 - 1) * (ξ ^ 2 + 3) * (i12HSQKA σ * (σ / (ξ ^ 2 - σ ^ 2)))) σ := by
  have ht : 0 < 1 - σ ^ 2 := by nlinarith [hσ.1, hσ.2]
  have hq : 0 < ξ ^ 2 - 1 := by nlinarith
  have hqt : 0 < ξ ^ 2 - σ ^ 2 := by nlinarith [hσ.1, hσ.2]
  have dt : HasDerivAt (fun σ => 1 - σ ^ 2) (-(2 * σ)) σ := by
    simpa using (hasDerivAt_pow 2 σ).const_sub 1
  have d1 : HasDerivAt (fun σ => (ξ ^ 2 - 1) ^ 2 * σ / (2 * (1 - σ ^ 2)))
      ((ξ ^ 2 - 1) ^ 2 * (1 + σ ^ 2) / (2 * (1 - σ ^ 2) ^ 2)) σ := by
    have := ((hasDerivAt_id' σ).const_mul ((ξ ^ 2 - 1) ^ 2)).div (dt.const_mul 2)
      (by positivity)
    refine this.congr_deriv ?_
    field_simp
    ring
  have dQ := ((hasDerivAt_id' σ).add d1).add
    ((hasDerivAt_i12HSQKA (by linarith [hσ.1]) hσ.2).const_mul
      (2 * (ξ ^ 2 - 1) + (ξ ^ 2 - 1) ^ 2 / 2))
  have dl : HasDerivAt (fun σ => log (ξ ^ 2 - σ ^ 2) - log (ξ ^ 2 - 1))
      (-(2 * σ) / (ξ ^ 2 - σ ^ 2)) σ := by
    have := (((hasDerivAt_pow 2 σ).const_sub (ξ ^ 2)).log hqt.ne').sub_const (log (ξ ^ 2 - 1))
    refine this.congr_deriv ?_
    simp
  have h := dQ.mul dl
  refine h.congr_deriv ?_
  have e1 : ξ ^ 2 - 1 + (1 - σ ^ 2) = ξ ^ 2 - σ ^ 2 := by ring
  simp only [Pi.add_apply]
  unfold i12HSQKf i12HSQKe
  rw [e1]
  field_simp
  ring

/-- The boundary value `Q λ → q/2` at `σ = 1`. -/
theorem tendsto_i12HSQKh_one {ξ : ℝ} (hξ : 1 < ξ) :
    Tendsto (i12HSQKh ξ) (𝓝[<] 1) (𝓝 ((ξ ^ 2 - 1) / 2)) := by
  set q := ξ ^ 2 - 1 with hqdef
  have hq : 0 < q := by rw [hqdef]; nlinarith
  set c₂ := 2 * q + q ^ 2 / 2
  set lam : ℝ → ℝ := fun σ => log (ξ ^ 2 - σ ^ 2) - log q with hlam
  have hlam1 : ContinuousAt lam 1 := by
    have : ξ ^ 2 - 1 ^ 2 ≠ 0 := by nlinarith
    rw [hlam]; fun_prop (disch := assumption)
  have hlam0 : lam 1 = 0 := by simp [hlam, hqdef]
  -- (a) `σ λ → 0`
  have ha : Tendsto (fun σ => σ * lam σ) (𝓝[<] 1) (𝓝 0) := by
    have hc : ContinuousAt (fun σ => σ * lam σ) 1 := continuousAt_id.mul hlam1
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
    rw [hlam0, mul_zero] at this
    exact this
  -- bounds on `λ` on `(0, 1)`
  have hlb : ∀ σ ∈ Ioo (0 : ℝ) 1, (1 - σ ^ 2) / (q + (1 - σ ^ 2)) ≤ lam σ ∧
      lam σ ≤ (1 - σ ^ 2) / q := by
    intro σ hσ
    have ht : 0 < 1 - σ ^ 2 := by nlinarith [hσ.1, hσ.2]
    have hqt : 0 < q + (1 - σ ^ 2) := by linarith
    have e : ξ ^ 2 - σ ^ 2 = q + (1 - σ ^ 2) := by rw [hqdef]; ring
    have hx : 0 < (q + (1 - σ ^ 2)) / q := by positivity
    have up := log_le_sub_one_of_pos hx
    have lo := one_sub_inv_le_log_of_pos hx
    rw [log_div hqt.ne' hq.ne'] at up lo
    have e1 : (q + (1 - σ ^ 2)) / q - 1 = (1 - σ ^ 2) / q := by field_simp; ring
    have e2 : 1 - ((q + (1 - σ ^ 2)) / q)⁻¹ = (1 - σ ^ 2) / (q + (1 - σ ^ 2)) := by
      field_simp; ring
    simp only [hlam, e]
    constructor <;> linarith
  -- (b) `A λ → 0`
  have hb : Tendsto (fun σ => i12HSQKA σ * lam σ) (𝓝[<] 1) (𝓝 0) := by
    have ht := tendsto_one_sub_mul_of_abs_le_logs (n := 1) i12HSQK_log_two_nonneg
      (by positivity : (0 : ℝ) ≤ 2 / q) (f := fun σ => i12HSQKA σ * (lam σ / (1 - σ)))
      fun σ hσ => by
        have h1 : 0 < 1 - σ := by linarith [hσ.2]
        have hl := hlb σ hσ
        have hl0 : 0 ≤ lam σ := le_trans (by
          have : 0 < 1 - σ ^ 2 := by nlinarith [hσ.1, hσ.2]
          positivity) hl.1
        rw [abs_mul, mul_comm]
        refine mul_le_mul ?_ (abs_i12HSQKA_le hσ) (abs_nonneg _) (by positivity)
        rw [abs_of_nonneg (by positivity), div_le_iff₀ h1]
        calc lam σ ≤ (1 - σ ^ 2) / q := hl.2
          _ = (1 + σ) / q * (1 - σ) := by field_simp; ring
          _ ≤ 2 / q * (1 - σ) := by
            gcongr; linarith [hσ.2]
    refine ht.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with σ hσ
    have h1 : 1 - σ ≠ 0 := by linarith [hσ.2]
    field_simp
  -- (c) `σ λ / t → 1/q`
  have hc : Tendsto (fun σ => σ * (lam σ / (1 - σ ^ 2))) (𝓝[<] 1) (𝓝 (1 / q)) := by
    have hlo : Tendsto (fun σ : ℝ => σ / (q + (1 - σ ^ 2))) (𝓝[<] 1) (𝓝 (1 / q)) := by
      have : ContinuousAt (fun σ : ℝ => σ / (q + (1 - σ ^ 2))) 1 := by
        have : q + (1 - 1 ^ 2) ≠ 0 := by simp; exact hq.ne'
        fun_prop (disch := assumption)
      simpa using this.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
    have hhi : Tendsto (fun σ : ℝ => σ / q) (𝓝[<] 1) (𝓝 (1 / q)) := by
      have : ContinuousAt (fun σ : ℝ => σ / q) 1 := by fun_prop
      simpa using this.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with σ hσ
      have ht : 0 < 1 - σ ^ 2 := by nlinarith [hσ.1, hσ.2]
      have hl := (hlb σ hσ).1
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < q + (1 - σ ^ 2))]
      have : 1 ≤ lam σ / (1 - σ ^ 2) * (q + (1 - σ ^ 2)) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ ht]
        rw [div_le_iff₀ (by positivity)] at hl; linarith
      nlinarith [hσ.1]
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with σ hσ
      have ht : 0 < 1 - σ ^ 2 := by nlinarith [hσ.1, hσ.2]
      have hl := (hlb σ hσ).2
      have : lam σ / (1 - σ ^ 2) ≤ 1 / q := by
        rw [div_le_iff₀ ht]; calc lam σ ≤ (1 - σ ^ 2) / q := hl
          _ = 1 / q * (1 - σ ^ 2) := by ring
      calc σ * (lam σ / (1 - σ ^ 2)) ≤ σ * (1 / q) := mul_le_mul_of_nonneg_left this hσ.1.le
        _ = σ / q := by ring
  have htot := (ha.add (hb.const_mul c₂)).add (hc.const_mul (q ^ 2 / 2))
  have hval : (0 : ℝ) + c₂ * 0 + q ^ 2 / 2 * (1 / q) = q / 2 := by field_simp; ring
  rw [hval] at htot
  refine htot.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with σ hσ
  have ht : 0 < 1 - σ ^ 2 := by nlinarith [hσ.1, hσ.2]
  simp only [i12HSQKh, hlam, ← hqdef]
  field_simp
  ring

/-- The primitive of `e`:
`σ log q - (1 + σ) log (1 + σ) + (1 - σ) log (1 - σ) + ξ(3 - ξ²)/2 (log (ξ + σ) - log (ξ - σ))`. -/
noncomputable def i12HSQKPe (ξ σ : ℝ) : ℝ :=
  σ * log (ξ ^ 2 - 1) - (1 + σ) * log (1 + σ) + (1 - σ) * log (1 - σ) +
    ξ * (3 - ξ ^ 2) / 2 * (log (ξ + σ) - log (ξ - σ))

theorem hasDerivAt_i12HSQKPe {ξ σ : ℝ} (hξ : 1 < ξ) (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i12HSQKPe ξ) (i12HSQKe ξ σ) σ := by
  have a : 0 < 1 + σ := by linarith [hσ.1]
  have b : 0 < 1 - σ := by linarith [hσ.2]
  have c : 0 < ξ + σ := by linarith [hσ.1]
  have d : 0 < ξ - σ := by linarith [hσ.2]
  have da : HasDerivAt (fun σ => 1 + σ) 1 σ := by simpa using (hasDerivAt_id σ).const_add 1
  have db : HasDerivAt (fun σ => 1 - σ) (-1) σ := by simpa using (hasDerivAt_id σ).const_sub 1
  have dc : HasDerivAt (fun σ => ξ + σ) 1 σ := by simpa using (hasDerivAt_id σ).const_add ξ
  have dd : HasDerivAt (fun σ => ξ - σ) (-1) σ := by simpa using (hasDerivAt_id σ).const_sub ξ
  have h := ((((hasDerivAt_id' σ).mul_const (log (ξ ^ 2 - 1))).sub (da.mul (da.log a.ne'))).add
    (db.mul (db.log b.ne'))).add (((dc.log c.ne').sub (dd.log d.ne')).const_mul
      (ξ * (3 - ξ ^ 2) / 2))
  refine h.congr_deriv ?_
  have e1 : log (1 - σ ^ 2) = log (1 - σ) + log (1 + σ) := by
    rw [← log_mul b.ne' a.ne']; ring_nf
  have e2 : ξ ^ 2 - σ ^ 2 = (ξ + σ) * (ξ - σ) := by ring
  unfold i12HSQKe
  rw [e1, e2]
  field_simp
  ring

theorem continuousOn_i12HSQKPe {ξ : ℝ} (hξ : 1 < ξ) : ContinuousOn (i12HSQKPe ξ) (Icc 0 1) := by
  intro σ hσ
  have c : ξ + σ ≠ 0 := by linarith [hσ.1]
  have d : ξ - σ ≠ 0 := by linarith [hσ.2]
  have a : 1 + σ ≠ 0 := by linarith [hσ.1]
  have hm : Continuous fun σ : ℝ => (1 - σ) * log (1 - σ) :=
    Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
  refine ContinuousAt.continuousWithinAt ?_
  unfold i12HSQKPe
  exact ((by fun_prop (disch := assumption) : ContinuousAt (fun σ : ℝ =>
    σ * log (ξ ^ 2 - 1) - (1 + σ) * log (1 + σ)) σ).add hm.continuousAt).add
    (by fun_prop (disch := assumption))

theorem i12HSQKe_abs_le {ξ σ : ℝ} (hξ : 1 < ξ) (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    |i12HSQKe ξ σ| ≤ 1 * (|log (ξ ^ 2 - 1)| + log 2 + ξ ^ 2 + 2 / (ξ ^ 2 - 1) + |log σ| +
      |log (1 - σ)|) ^ 1 := by
  have hq : 0 < ξ ^ 2 - 1 := by nlinarith
  have hqt : ξ ^ 2 - 1 ≤ ξ ^ 2 - σ ^ 2 := by nlinarith [hσ.1, hσ.2]
  have e : log (1 - σ ^ 2) = log (1 - σ) + log (1 + σ) := by
    rw [← log_mul (by linarith [hσ.2]) (by linarith [hσ.1])]; ring_nf
  have l1 : 0 ≤ log (1 + σ) := log_nonneg (by linarith [hσ.1])
  have l2 : log (1 + σ) ≤ log 2 := log_le_log (by linarith [hσ.1]) (by linarith [hσ.2])
  have t1 : 0 ≤ (ξ ^ 2 - 1) * ξ ^ 2 / (ξ ^ 2 - σ ^ 2) :=
    div_nonneg (by positivity) (by linarith)
  have t1' : (ξ ^ 2 - 1) * ξ ^ 2 / (ξ ^ 2 - σ ^ 2) ≤ ξ ^ 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have t2 : 0 ≤ 2 * σ ^ 2 / (ξ ^ 2 - σ ^ 2) := div_nonneg (by positivity) (by linarith)
  have t2' : 2 * σ ^ 2 / (ξ ^ 2 - σ ^ 2) ≤ 2 / (ξ ^ 2 - 1) := by
    rw [div_le_div_iff₀ (by linarith) hq]; nlinarith [hσ.1, hσ.2]
  have a1 := neg_abs_le (log (ξ ^ 2 - 1))
  have a2 := le_abs_self (log (ξ ^ 2 - 1))
  have a3 := neg_abs_le (log (1 - σ))
  have a4 := le_abs_self (log (1 - σ))
  have a5 := abs_nonneg (log σ)
  unfold i12HSQKe
  rw [one_mul, pow_one, abs_le, e]
  constructor <;> linarith

theorem integrableOn_i12HSQKe {ξ : ℝ} (hξ : 1 < ξ) : IntegrableOn (i12HSQKe ξ) (Ioo 0 1) := by
  refine integrableOn_Ioo_of_abs_le_logs (by
    have : 0 < ξ ^ 2 - 1 := by nlinarith
    have := i12HSQK_log_two_nonneg
    positivity) zero_le_one 1
    ((continuousOn_of_forall_continuousAt fun σ hσ => ?_).aestronglyMeasurable
      measurableSet_Ioo) fun σ hσ => i12HSQKe_abs_le hξ hσ
  have h1 : 1 - σ ^ 2 ≠ 0 := by nlinarith [hσ.1, hσ.2]
  have h2 : ξ ^ 2 - σ ^ 2 ≠ 0 := by nlinarith [hσ.1, hσ.2]
  have h3 : ξ ^ 2 - 1 ≠ 0 := by nlinarith
  unfold i12HSQKe
  fun_prop (disch := assumption)

/-- `∫₀¹ e = i12HSQKPe ξ 1 = log (q/4) + ξ(3 - ξ²)/2 log ((ξ + 1)/(ξ - 1))`. -/
theorem integral_i12HSQKe {ξ : ℝ} (hξ : 1 < ξ) :
    ∫ σ in Ioo (0 : ℝ) 1, i12HSQKe ξ σ = i12HSQKPe ξ 1 := by
  have hi := integrableOn_i12HSQKe hξ
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one (continuousOn_i12HSQKPe hξ)
      (fun σ hσ => hasDerivAt_i12HSQKPe hξ hσ)
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hi)]
  simp [i12HSQKPe]

theorem i12HSQKW_kernel_inv {ξ σ : ℝ} (hξ : 1 < ξ) (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    ξ⁻¹ ^ 2 * σ / (1 - ξ⁻¹ ^ 2 * σ ^ 2) = σ / (ξ ^ 2 - σ ^ 2) := by
  have h0 : ξ ≠ 0 := by linarith
  have h2 : ξ ^ 2 - σ ^ 2 ≠ 0 := by nlinarith [hσ.1, hσ.2]
  have e : 1 - ξ⁻¹ ^ 2 * σ ^ 2 = (ξ ^ 2 - σ ^ 2) / ξ ^ 2 := by
    rw [inv_pow]; field_simp
  rw [e, inv_pow]
  field_simp

/-- **The reduced integral of `K₁`:**
`∫₀¹ f = i12HSQKPe ξ 1 + (ξ² - 1)(ξ² + 3) W(1/ξ) + (ξ² - 1)/2`. -/
theorem integral_i12HSQKf {ξ : ℝ} (hξ : 1 < ξ) :
    ∫ σ in Ioo (0 : ℝ) 1, i12HSQKf (ξ ^ 2 - 1) (1 - σ ^ 2) =
      i12HSQKPe ξ 1 + (ξ ^ 2 - 1) * (ξ ^ 2 + 3) * i12HSQKW ξ⁻¹ + (ξ ^ 2 - 1) / 2 := by
  have hq : 0 < ξ ^ 2 - 1 := by nlinarith
  have hxi : ξ⁻¹ ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, inv_lt_one_of_one_lt₀ hξ⟩
  set c := (ξ ^ 2 - 1) * (ξ ^ 2 + 3)
  set Wk : ℝ → ℝ := fun σ => i12HSQKA σ * (σ / (ξ ^ 2 - σ ^ 2)) with hWk
  have hWeq : ∀ σ ∈ Ioo (0 : ℝ) 1,
      i12HSQKA σ * (ξ⁻¹ ^ 2 * σ / (1 - ξ⁻¹ ^ 2 * σ ^ 2)) = Wk σ := fun σ hσ => by
    rw [hWk, i12HSQKW_kernel_inv hξ hσ]
  have hWi : IntegrableOn Wk (Ioo 0 1) := by
    refine (integrableOn_Ioo_of_abs_le_logs i12HSQK_log_two_nonneg
      (by have : 0 < 1 - ξ⁻¹ ^ 2 := by nlinarith [hxi.1, hxi.2]
          positivity) 1
      ((continuousOn_of_forall_continuousAt fun σ hσ =>
        continuousAt_i12HSQKW_integrand hσ
        (i12HSQK_one_sub_sq_pos hxi (Ioo_subset_Icc_self hσ))).aestronglyMeasurable
        measurableSet_Ioo) fun σ hσ =>
        abs_i12HSQKW_integrand_le hxi.1.le le_rfl hxi.2 hσ).congr_fun hWeq measurableSet_Ioo
  have hWint : ∫ σ in Ioo (0 : ℝ) 1, Wk σ = i12HSQKW ξ⁻¹ :=
    (setIntegral_congr_fun measurableSet_Ioo hWeq).symm
  have hki : IntegrableOn (fun σ => i12HSQKe ξ σ + c * Wk σ) (Ioo 0 1) :=
    (integrableOn_i12HSQKe hξ).add (hWi.const_mul c)
  have hfi : IntegrableOn (fun σ => i12HSQKf (ξ ^ 2 - 1) (1 - σ ^ 2)) (Ioo 0 1) := by
    refine integrableOn_Ioo_of_abs_le_logs (by
      have := i12HSQK_log_two_nonneg; positivity) zero_le_one 1
      ((continuousOn_of_forall_continuousAt fun σ hσ => ?_).aestronglyMeasurable
        measurableSet_Ioo) fun σ hσ => abs_i12HSQKf_le hq hσ
    have h1 : 1 - σ ^ 2 ≠ 0 := by nlinarith [hσ.1, hσ.2]
    have h2 : ξ ^ 2 - 1 + (1 - σ ^ 2) ≠ 0 := by nlinarith [hσ.1, hσ.2]
    have h3 : ξ ^ 2 - 1 ≠ 0 := hq.ne'
    unfold i12HSQKf
    fun_prop (disch := first | assumption | exact pow_ne_zero 2 h1)
  have hla : Tendsto (i12HSQKh ξ) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (i12HSQKh ξ) 0 := by
      have h1 : (2 : ℝ) * (1 - 0 ^ 2) ≠ 0 := by norm_num
      have h2 : ξ ^ 2 - 0 ^ 2 ≠ 0 := by nlinarith
      have h3 : ξ ^ 2 - 1 ≠ 0 := hq.ne'
      have hA := continuousAt_i12HSQKA (σ := 0) (by norm_num) (by norm_num)
      unfold i12HSQKh
      fun_prop (disch := assumption)
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [i12HSQKh, i12HSQKA_zero] using this
  have key := setIntegral_Ioo_eq_add_of_eq_add_deriv
    (f := fun σ => i12HSQKf (ξ ^ 2 - 1) (1 - σ ^ 2)) (k := fun σ => i12HSQKe ξ σ + c * Wk σ)
    (h := i12HSQKh ξ) (h' := fun σ => i12HSQKf (ξ ^ 2 - 1) (1 - σ ^ 2) -
      (i12HSQKe ξ σ + c * Wk σ)) zero_lt_one (fun σ _ => by ring) hki
    (fun σ hσ => (hasDerivAt_i12HSQKh hξ hσ).congr_deriv (by rw [hWk]; ring))
    (hfi.sub hki) hla (tendsto_i12HSQKh_one hξ)
  rw [key, integral_add (integrableOn_i12HSQKe hξ) (hWi.const_mul c), integral_const_mul,
    hWint, integral_i12HSQKe hξ]
  ring

/-- `K₁(z) = ∫₀¹ ψ₁(z/c)/c dρ`, `c = ρ(2 - ρ)/4`: the order-1 coefficient of
`K(z) = ∫₀¹ c^{-ε-1} (φ(z/c) - a (z/c)^{-3ε}) dρ` (whose order-0 coefficient vanishes). -/
noncomputable def i12HSQK1 (z : ℝ) : ℝ :=
  ∫ ρ in Ioo (0 : ℝ) 1, i12HSQKpsi (z / (ρ * (2 - ρ) / 4)) / (ρ * (2 - ρ) / 4)

/-- `K₁` in the variable `σ = 1 - ρ`, through the reduced integral. -/
theorem i12HSQK1_eq_integral {ξ : ℝ} (hξ : 1 < ξ) :
    i12HSQK1 ((ξ ^ 2 - 1) / 4) =
      -(12 / (ξ ^ 2 - 1)) * ∫ σ in Ioo (0 : ℝ) 1, i12HSQKf (ξ ^ 2 - 1) (1 - σ ^ 2) := by
  have hq : 0 < ξ ^ 2 - 1 := by nlinarith
  set F : ℝ → ℝ := fun ρ =>
    i12HSQKpsi ((ξ ^ 2 - 1) / 4 / (ρ * (2 - ρ) / 4)) / (ρ * (2 - ρ) / 4) with hF
  have hcov : ∫ ρ in (0 : ℝ)..1, F ρ = ∫ σ in (0 : ℝ)..1, F (1 - σ) := by
    rw [intervalIntegral.integral_comp_sub_left]; norm_num
  unfold i12HSQK1
  rw [← hF, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, hcov,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun σ hσ => ?_
  have ht : 0 < 1 - σ ^ 2 := by nlinarith [hσ.1, hσ.2]
  have e : (1 - σ) * (2 - (1 - σ)) / 4 = (1 - σ ^ 2) / 4 := by ring
  have e2 : (ξ ^ 2 - 1) / 4 / ((1 - σ ^ 2) / 4) = (ξ ^ 2 - 1) / (1 - σ ^ 2) := by
    field_simp
  simp only [hF]
  rw [e, e2, i12HSQKpsi_div hq ht]

/-- **`K₁` in closed form** (`q = ξ² - 1 = 4z`, `ξ = √(1 + 4z) > 1`):
`K₁ = -(12/q) (Pe(ξ, 1) + q(ξ² + 3) log² ((1 - ξ⁻¹)/(1 + ξ⁻¹))/8 + q/2)`, with
`Pe(ξ, 1) = log q - 2 log 2 + ξ(3 - ξ²)/2 (log (ξ + 1) - log (ξ - 1))`. -/
theorem i12HSQK1_closed {ξ : ℝ} (hξ : 1 < ξ) :
    i12HSQK1 ((ξ ^ 2 - 1) / 4) = -(12 / (ξ ^ 2 - 1)) *
      (log (ξ ^ 2 - 1) - 2 * log 2 + ξ * (3 - ξ ^ 2) / 2 * (log (ξ + 1) - log (ξ - 1)) +
        (ξ ^ 2 - 1) * (ξ ^ 2 + 3) * ((log (1 - ξ⁻¹) - log (1 + ξ⁻¹)) ^ 2 / 8) +
        (ξ ^ 2 - 1) / 2) := by
  have hxi : ξ⁻¹ ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, inv_lt_one_of_one_lt₀ hξ⟩
  rw [i12HSQK1_eq_integral hξ, integral_i12HSQKf hξ, i12HSQKW_eq_log hxi]
  congr 2
  simp only [i12HSQKPe]
  norm_num

end QED.ThreeLoopD
