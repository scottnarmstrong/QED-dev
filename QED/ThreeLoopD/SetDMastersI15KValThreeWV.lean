/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI15KValThreeWu
public import QED.ThreeLoopD.SetDMastersI15KValThreeW
import QED.ThreeLoopD.SetDMastersI15KValThreeW0
import QED.Polylog.LiCalculus
import QED.ThreeLoopD.SetDMastersI15KValThreeK
import QED.Polylog.HPLLowWeight
import QED.Polylog.DilogPM
import QED.Polylog.Landen
import QED.Polylog.Reflection
import QED.Polylog.LiN

/-!
# Set (d), master `I₁₅`: the `u`-integral of `b₁³ - b₂³` is `W₃`

The primitive of `QED.ThreeLoopD.SetDMastersI15KValThreeWu` gives
`∫₀¹ (b₁³ - b₂³) du = Φ(1) - Φ(0⁺)`, a combination of `Li₃` and `Li₂` at `r`, `1 - r`,
`r/(1 + r)`, `1/(1 + r)`, `r²` and `1 - r²`. Rewriting these by reflection, duplication,
`Li₂ (r/(1 + r))`, `Li₂ (1/(1 + r))`, Landen's identity for `Li₃` and the mixed combination
`QED.ThreeLoopD.i15K_mixed`, and the harmonic polylogarithms of `QED.ThreeLoopD.i15W3` by their
closed forms, both sides become the same polynomial in `Li₃ (±r)`, `Li₃ (1 - r)`,
`Li₃ (1/(1 + r))`, `Li₂ (±r)`, logarithms, `π²`, `ζ(3)` and the words `H(1, -1, 0)`,
`H(-1, 1, 0)`.

## Main results

* `QED.ThreeLoopD.i15WuPhi_sub_eq`: `Φ(1) - Φ(0⁺) = W₃(r)`.
* `QED.ThreeLoopD.integral_i15WuF_eq`: `∫₀¹ (b₁³ - b₂³) du = W₃(r)`.
* `QED.ThreeLoopD.integral_i15W3`: `W₃ / r` is integrable on `[0, 1]` and
  `∫₀¹ W₃ / r = 3 (14 π² + 56 ζ(3) - 16 π² log 2 - 100)`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

theorem i15WuPhi_sub_eq {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    i15WuPhi r 1 - i15WuPhi0 r = i15W3 r := by
  obtain ⟨h0, h1⟩ := hr
  have hr' : r ∈ Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
  have hp : 0 < 1 + r := by linarith
  have hm : 0 < 1 - r := by linarith
  have v0 : i15WuX0 r 1 = r := by unfold i15WuX0; field_simp; ring
  have v1 : i15WuX1 r 1 = 1 - r := by unfold i15WuX1; field_simp; ring
  have v2 : i15WuX2 r 1 = r / (1 + r) := by unfold i15WuX2; ring_nf
  have v3 : i15WuX3 r 1 = 1 / (1 + r) := by unfold i15WuX3; ring_nf
  have v4 : i15WuX4 r 1 = 1 / (1 + r) := by unfold i15WuX4; ring_nf
  have v5 : i15WuX5 r 1 = r / (1 + r) := by unfold i15WuX5; ring_nf
  have v6 : i15WuX6 r 1 = 1 - r := by unfold i15WuX6; field_simp
  have v7 : i15WuX7 r 1 = r := by unfold i15WuX7; field_simp; ring
  have eA : i15WuA r 1 = log (1 + r) - log r := by
    unfold i15WuA; rw [← log_div hp.ne' h0.ne']; congr 1; field_simp; ring
  have eB : i15WuB r 1 = log (1 + r) := by unfold i15WuB; rw [mul_one]
  -- logarithms of the arguments
  have l1 : log (r / (1 + r)) = log r - log (1 + r) := log_div h0.ne' hp.ne'
  have l2 : log (1 / (1 + r)) = -log (1 + r) := by rw [one_div, log_inv]
  have l3 : log (r ^ 2) = 2 * log r := by rw [log_pow]; push_cast; ring
  have l4 : log ((1 - r) * (1 + r)) = log (1 - r) + log (1 + r) := log_mul hm.ne' hp.ne'
  -- dilogarithms
  have d1 : Li₂ (1 - r) = π ^ 2 / 6 - log r * log (1 - r) - Li₂ r := by
    have := Li₂_add_Li₂_one_sub h0.le h1.le; linarith
  have d2 : Li₂ (r / (1 + r)) = -Li₂ (-r) - log (1 + r) ^ 2 / 2 := Li_two_div_one_add hr'
  have d3 : Li₂ (1 / (1 + r)) =
      π ^ 2 / 6 + log r * log (1 + r) - log (1 + r) ^ 2 / 2 + Li₂ (-r) := Li_two_inv_one_add hr'
  have d4 : Li₂ (r ^ 2) = 2 * Li₂ r + 2 * Li₂ (-r) := by
    have := Li₂_add_Li₂_neg (x := r) (by rw [abs_of_pos h0]; exact h1.le); linarith
  have d5 : Li₂ ((1 - r) * (1 + r)) = π ^ 2 / 6 - 2 * log r * (log (1 - r) + log (1 + r)) -
      (2 * Li₂ r + 2 * Li₂ (-r)) := by
    have := Li₂_add_Li₂_one_sub (x := r ^ 2) (by positivity) (by nlinarith)
    rw [show (1 : ℝ) - r ^ 2 = (1 - r) * (1 + r) by ring, l3, l4, d4] at this
    linarith
  -- trilogarithms
  have t1 : Li₃ (r ^ 2) = 4 * Li₃ r + 4 * Li₃ (-r) := by
    have := Li₃_add_Li₃_neg (x := r) (by rw [abs_of_pos h0]; exact h1.le); linarith
  have t2 : Li₃ (r / (1 + r)) = zeta3 - log (1 + r) ^ 3 / 6 - π ^ 2 / 6 * log (1 + r) -
      log (1 + r) ^ 2 * (log r - log (1 + r)) / 2 - Li₃ (1 / (1 + r)) - Li₃ (-r) := by
    have h := Li₃_add_Li₃_one_sub_add_Li₃_one_sub_inv (x := 1 / (1 + r))
      (by rw [le_div_iff₀ hp]; linarith) (by rw [div_le_one hp]; linarith)
    rw [show (1 : ℝ) - 1 / (1 + r) = r / (1 + r) by field_simp; ring,
      show (1 : ℝ) - (1 / (1 + r))⁻¹ = -r by field_simp; ring, l2, l1] at h
    linarith
  have t3 : Li₃ ((1 - r) * (1 + r)) = -(2 / 3) * (2 * hpl [one, zero, negOne] r -
      hpl [one, negOne, zero] r - hpl [negOne, one, zero] r - (3 * Li₃ (1 - r) +
      3 * Li₃ (1 / (1 + r)) - 2 * log (1 + r) * Li₂ r - 2 * log r * log (1 - r) * log (1 + r) -
      log (1 + r) ^ 3 / 2 - π ^ 2 / 4 * log (1 - r) + 3 * π ^ 2 / 4 * log (1 + r) -
      9 / 2 * zeta3)) := by
    rw [i15K_mixed hr', show (1 - r) * (1 + r) = 1 - r ^ 2 by ring]
    unfold i15KR
    ring
  unfold i15WuPhi i15WuPhi0 i15W3 i15TG
  rw [i15WuX0_zero hr', i15WuX1_zero, i15WuX2_zero hr', i15WuX3_zero, i15WuX4_zero, i15WuX5_zero,
    i15WuX6_zero, i15WuX7_zero, v0, v1, v2, v3, v4, v5, v6, v7, eA, eB]
  simp only [i15WuP, i15TPoly, i15TMono, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, log_one, log_zero, Li₂_one, Li₃_one, Li₂_zero, Li₃_zero, l1, l2, l3, l4, d1, d2,
    d3, d4, d5, t1, t2, t3, hpl_one hr', hpl_negOne hr', hpl_zero, hpl_zero_zero,
    hpl_zero_negOne hr', hpl_one_zero hr', hpl_negOne_zero hr', hpl_negOne_negOne hr',
    hpl_zero_zero_zero, hpl_zero_zero_negOne hr', hpl_zero_one_zero hr', hpl_zero_negOne_zero hr',
    hpl_one_zero_zero hr', hpl_one_one_zero hr', hpl_zero_one_one hr', hpl_negOne_zero_zero hr',
    hpl_negOne_zero_negOne hr', hpl_negOne_negOne_zero hr', hpl_negOne_negOne_negOne hr',
    hpl_zero_negOne_negOne hr', Li_two, Li_three]
  ring

/-- **`∫₀¹ (b₁³ - b₂³) du = W₃(r)`**, with integrability. -/
theorem integral_i15WuF_eq {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (i15WuF r) volume 0 1 ∧ ∫ u in (0 : ℝ)..1, i15WuF r u = i15W3 r := by
  obtain ⟨hi, hv⟩ := integral_i15WuF hr
  exact ⟨hi, hv.trans (i15WuPhi_sub_eq hr)⟩

theorem i15W3_nonpos {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : i15W3 r ≤ 0 := by
  obtain ⟨-, hv⟩ := integral_i15WuF_eq hr
  rw [← hv, intervalIntegral.integral_of_le zero_le_one]
  exact setIntegral_nonpos measurableSet_Ioc fun u hu => i15WuF_nonpos hr hu.1

/-- **`∫₀¹ W₃ / r = 3 (14 π² + 56 ζ(3) - 16 π² log 2 - 100)`**, with integrability. -/
theorem integral_i15W3 :
    IntervalIntegrable (fun r => i15W3 r / r) volume 0 1 ∧
      ∫ r in (0 : ℝ)..1, i15W3 r / r =
        3 * (14 * π ^ 2 + 56 * zeta3 - 16 * π ^ 2 * log 2 - 100) := by
  have hI := (intervalIntegrable_and_integral_eq_of_nonpos' zero_lt_one
    (fun r hr => hasDerivAt_i15W3Phi hr)
    (fun r hr => div_nonpos_of_nonpos_of_nonneg (i15W3_nonpos hr) hr.1.le)
    tendsto_i15W3Phi_zero tendsto_i15W3Phi_one).1
  exact ⟨hI, integral_i15W3_of_tendsto hI tendsto_i15W3Phi_zero⟩

end QED.ThreeLoopD
