/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKVCore
public import QED.ChainProof.SetAKSKVLog

/-!
# Set (a), stage D4: the core identity reduced to unit mass

Helper level for `KsCore` (Set (a) of the three-loop coefficient). The mass scaling of the
finite parts (`ksW_ksUF_scale`, `ksW_ksUFB_scale`) writes both sides of `KsCore` at mass `M`
and `s = M² t` as the same sides at mass `1` and `t`, plus `log M²` times the difference
`2Δc₁(t) + Δc₁B(t)` of the `log Λ` coefficients; that difference is `12 D(t)`
(`ksW_log_coeff`), which is exactly the `log M²` part of the target. So `KsCore` follows from
its unit-mass case `KsCoreOne`, an identity between functions of one variable `t > -4`:

  `ksUKe 1 · (2 (F(1, t) - F(1, 0)) + F_B(1, t) - F_B(1, 0))`
  `  = Π̂⁽⁴⁾(t)/(16π⁴) + c_m(1) D(t)/(32π⁴)`.

Main results:

* `KsCoreOne`: the unit-mass identity;
* **`ksW_ksCore_of_one`**: `KsCoreOne → KsCore`.
-/

@[expose] public section

open Real

namespace QED.ChainProof.SetAKS

open QED.Chain QED.GradedProof.RPi4

/-- **The core identity at unit mass.** -/
def KsCoreOne : Prop := ∀ t : ℝ, -4 < t →
  ksUKe 1 * (2 * (ksUF 1 t - ksUF 1 0) + (ksUFB 1 t - ksUFB 1 0)) =
    piHat4 t / (16 * π ^ 4) + ksUcm 1 * ksDm t / (32 * π ^ 4)

theorem ksW_ksUKe_one : ksUKe 1 = 1 / (256 * π ^ 4) := by
  unfold ksUKe
  have : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **The reduction to unit mass**: `KsCoreOne → KsCore`. -/
theorem ksW_ksCore_of_one (h : KsCoreOne) : KsCore := by
  intro M s hM hs
  have hM2 : 0 < M ^ 2 := by positivity
  set t := s / M ^ 2 with htd
  have hst : s = M ^ 2 * t := by rw [htd]; field_simp
  have ht : -4 < t := by rw [htd, lt_div_iff₀ hM2]; linarith
  have h0 : (-4 : ℝ) < 0 := by norm_num
  have hL := ksW_log_coeff ht
  have hC := h t ht
  rw [show ksUF M 0 = ksUF M (M ^ 2 * 0) by rw [mul_zero],
    show ksUFB M 0 = ksUFB M (M ^ 2 * 0) by rw [mul_zero], hst, ksW_ksUF_scale hM ht,
    ksW_ksUF_scale hM h0, ksW_ksUFB_scale hM ht, ksW_ksUFB_scale hM h0]
  rw [ksW_ksUKe_one] at hC ⊢
  linear_combination hC - (Real.log (M ^ 2) / (256 * π ^ 4)) * hL

end QED.ChainProof.SetAKS

end
