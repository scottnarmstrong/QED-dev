/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitX
public import QED.Polylog.ExtraIntegralsX
import QED.Polylog.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The kernel of the crossed-ladder unit: definitions (helper level, O2-25)

Section 4.5 of `docs/TWO-LOOP-UNITS.md` reduces the crossed-ladder unit X to `X = ∫₀¹ K_X`
(eq. (4.7)), with an explicit kernel `K_X` (`crossedKernel`) in the functions `Li₂ Y`,
`D(Y) = Li₂ (1 - 2Y) - Li₂ (2Y - 1)` (`crossedD`), `log Y` and `log (1 - Y)`. Integration by
parts gives `K_X = G' + p + K_m` (eq. (4.8)) with a boundary function `G` (`crossedBoundary`), a
linear polynomial `p` (`crossedPoly`) and a combination `K_m` (`crossedMasterKernel`) of the
master integrals of `QED.TwoLoop.UnitX` (eq. (4.9)). This file states the four functions, as in
the tables of 4.5.2 and 4.5.3, together with the regular part `crossedKernelReg` of `K_X` (`K_X`
plus explicit multiples of `log² Y`, `log Y`, `log (1 - Y)` and the integrand of `M₈`, with no
factor `1/(2Y - 1)`), and proves an endpoint expansion of `D`:

* `QED.TwoLoop.Units.abs_crossedDRem_le`: on `[0, 1/4]`,
  `|D(s) + log s log (1 - 2s) - (π²/4 - 2s + (7/9) s³ + (5/3) s⁴)| ≤ 110 s⁵`.

The function `D(s) + log s log (1 - 2s)` is continuous at `0` and its derivative
`log (1 - 2s)/s - 2 log (1 - s)/(1 - 2s)` has no logarithmic singularity, so the bound follows
from the expansions of `log (1 - x)` in `QED.Polylog.ExtraIntegralsX` and the mean value theorem.
Near `Y = 1` the same function enters through `D(1 - s) = -D(s)`.

Here `ζ(2) = π²/6`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology QED.Polylog

namespace QED.TwoLoop.Units

/-! ### The kernel, the boundary function, the polynomial and the master combination -/

/-- `ϱ(Y) = 5/(6(Y-1)) - 3/(4(Y-1)²) - 8/(3(Y-1)³) - 1/(Y-1)⁴` (section 4.5.2). -/
noncomputable def crossedRho (Y : ℝ) : ℝ :=
  5 / (6 * (Y - 1)) - 3 / (4 * (Y - 1) ^ 2) - 8 / (3 * (Y - 1) ^ 3) - 1 / (Y - 1) ^ 4

/-- The crossed-ladder kernel `K_X` of eq. (4.7) of `docs/TWO-LOOP-UNITS.md`, with the
coefficients `k_L, k_D, k_aa, k_ab, k_a, k_b, k_z, k_1` of the table of 4.5.2. -/
noncomputable def crossedKernel (Y : ℝ) : ℝ :=
  (-(5 / 2) * Y - 5 / 4 + 2 * crossedRho Y + 5 / (6 * Y) - 7 / (12 * Y ^ 2)) * Li₂ Y +
    (-(7 / 6) * Y - 11 / 12 + crossedRho Y + 5 / (6 * Y) - 1 / (12 * Y ^ 2)) * crossedD Y +
    (Y / 12 - 7 / 24 + crossedRho Y / 2) * log Y ^ 2 +
    (-(4 / 3) * Y - 1 / 3 + 5 / (6 * Y) - 7 / (12 * Y ^ 2)) * (log Y * log (1 - Y)) +
    (-(11 / 12) * Y - 5 / 4 - 1 / (8 * (2 * Y - 1)) + 11 / (12 * (Y - 1)) - 2 / (3 * (Y - 1) ^ 2) -
        1 / (Y - 1) ^ 3 - 5 / (12 * Y)) * log Y +
    (11 / 12 * Y - 13 / 12 + 1 / (8 * (2 * Y - 1)) - 2 / (3 * (Y - 1)) - 1 / (Y - 1) ^ 2 +
        7 / (6 * Y) - 1 / (24 * Y ^ 2)) * log (1 - Y) +
    (23 / 12 * Y + 19 / 24 - crossedRho Y / 2 - 5 / (4 * Y) + 1 / (8 * Y ^ 2)) * (π ^ 2 / 6) +
    (-(17 / 12) * Y + 1 / 24 + 2 / (3 * (Y - 1)) + 1 / (Y - 1) ^ 2 + 3 / (8 * Y))

/-- The boundary function `G` of eq. (4.8). -/
noncomputable def crossedBoundary (Y : ℝ) : ℝ :=
  (-(5 / 4) * Y ^ 2 - 5 / 4 * Y + 3 / (2 * (Y - 1)) + 8 / (3 * (Y - 1) ^ 2) +
        2 / (3 * (Y - 1) ^ 3) + 7 / (12 * Y)) * Li₂ Y +
    (-(7 / 12) * Y ^ 2 - 11 / 12 * Y + 3 / (4 * (Y - 1)) + 4 / (3 * (Y - 1) ^ 2) +
        1 / (3 * (Y - 1) ^ 3) + 1 / (12 * Y)) * crossedD Y +
    (Y ^ 2 / 24 - 7 / 24 * Y + 3 / (8 * (Y - 1)) + 2 / (3 * (Y - 1) ^ 2) + 1 / (6 * (Y - 1) ^ 3) -
        1 / 8) * log Y ^ 2 +
    (-(2 / 3) * Y ^ 2 - 1 / 3 * Y + 7 / (12 * Y)) * (log Y * log (1 - Y)) +
    (-(11 / 24) * Y ^ 2 - 7 / 8 * Y + 1 / (3 * (Y - 1)) + 1 / (3 * (Y - 1) ^ 2) + 5 / 12) * log Y +
    (11 / 24 * Y ^ 2 - 19 / 24 * Y + 1 / (3 * (Y - 1)) + 1 / (24 * Y) + 23 / 24) * log (1 - Y) -
    π ^ 2 / 6 * (3 / (8 * (Y - 1)) + 2 / (3 * (Y - 1) ^ 2) + 1 / (6 * (Y - 1) ^ 3) + 1 / (8 * Y)) -
    1 / (3 * (Y - 1))

/-- The polynomial `p(Y) = (30 + 19 ζ(2) + (46 ζ(2) - 34) Y)/24` of eq. (4.8). -/
noncomputable def crossedPoly (Y : ℝ) : ℝ :=
  (30 + 19 * (π ^ 2 / 6) + (46 * (π ^ 2 / 6) - 34) * Y) / 24

/-- The combination `K_m` of master integrands of eq. (4.9). -/
noncomputable def crossedMasterKernel (Y : ℝ) : ℝ :=
  5 / 6 * (Li₂ Y / Y + log Y * log (1 - Y) / Y + (crossedD Y - π ^ 2 / 4) / Y +
      2 * ((Li₂ Y - π ^ 2 / 6) / (Y - 1)) + (crossedD Y + π ^ 2 / 4) / (Y - 1)) +
    5 / 12 * (log Y ^ 2 / (Y - 1)) + 5 / 12 * (log Y / (Y - 1)) + 11 / 6 * (log (1 - Y) / Y) +
    4 / 3 * ((log Y - log (1 - Y)) / (2 * Y - 1))

/-- The regular part of `K_X`: `K_X + (log Y - log (1 - Y))/(8(2Y - 1)) + log² Y/4 + (7/8) log Y +
log (1 - Y)/8`, written without the factor `1/(2Y - 1)`. It is continuous on `(0, 1)` and has
finite limits at both ends; `K_X` differs from it by multiples of `log² Y`, `log Y`,
`log (1 - Y)` and the integrand of `M₈`. -/
noncomputable def crossedKernelReg (Y : ℝ) : ℝ :=
  (-(5 / 2) * Y - 5 / 4 + 2 * crossedRho Y + 5 / (6 * Y) - 7 / (12 * Y ^ 2)) * Li₂ Y +
    (-(7 / 6) * Y - 11 / 12 + crossedRho Y + 5 / (6 * Y) - 1 / (12 * Y ^ 2)) * crossedD Y +
    (Y / 12 - 7 / 24 + crossedRho Y / 2 + 1 / 4) * log Y ^ 2 +
    (-(4 / 3) * Y - 1 / 3 + 5 / (6 * Y) - 7 / (12 * Y ^ 2)) * (log Y * log (1 - Y)) +
    (-(11 / 12) * Y - 5 / 4 + 11 / (12 * (Y - 1)) - 2 / (3 * (Y - 1) ^ 2) - 1 / (Y - 1) ^ 3 -
        5 / (12 * Y) + 7 / 8) * log Y +
    (11 / 12 * Y - 13 / 12 - 2 / (3 * (Y - 1)) - 1 / (Y - 1) ^ 2 + 7 / (6 * Y) -
        1 / (24 * Y ^ 2) + 1 / 8) * log (1 - Y) +
    (23 / 12 * Y + 19 / 24 - crossedRho Y / 2 - 5 / (4 * Y) + 1 / (8 * Y ^ 2)) * (π ^ 2 / 6) +
    (-(17 / 12) * Y + 1 / 24 + 2 / (3 * (Y - 1)) + 1 / (Y - 1) ^ 2 + 3 / (8 * Y))

/-! ### The expansion of `D` at `0` -/

/-- The remainder of `D(s) + log s log (1 - 2s)` after its expansion to order `s⁴`. -/
noncomputable def crossedDRem (s : ℝ) : ℝ :=
  crossedD s + log s * log (1 - 2 * s) - (π ^ 2 / 4 - 2 * s + 7 / 9 * s ^ 3 + 5 / 3 * s ^ 4)

/-- `log s log (1 - 2s) → 0` as `s → 0`. -/
theorem tendsto_log_mul_log_one_sub_two_mul :
    Tendsto (fun s : ℝ => log s * log (1 - 2 * s)) (𝓝 0) (𝓝 0) := by
  have hlim : Tendsto (fun s : ℝ => 4 * |s * log s|) (𝓝 0) (𝓝 0) := by
    have := ((continuous_mul_log.tendsto 0).abs).const_mul 4
    simpa using this
  refine squeeze_zero_norm' ?_ hlim
  have hev : ∀ᶠ s : ℝ in 𝓝 0, |s| < 1 / 4 := by
    have : Tendsto (fun s : ℝ => |s|) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ))
    exact this.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hev] with s hs
  have h2 : |2 * s| < 1 := by rw [abs_mul, abs_two]; linarith
  have hb := Real.abs_log_sub_add_sum_range_le h2 0
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_one] at hb
  have hpos : 0 < 1 - |2 * s| := by linarith
  have hb' : |log (1 - 2 * s)| ≤ 4 * |s| := by
    refine hb.trans ?_
    rw [div_le_iff₀ hpos, abs_mul, abs_two]
    nlinarith [abs_nonneg s]
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  calc |log s| * |log (1 - 2 * s)| ≤ |log s| * (4 * |s|) :=
        mul_le_mul_of_nonneg_left hb' (abs_nonneg _)
    _ = 4 * (|s| * |log s|) := by ring

theorem continuousOn_crossedDRem : ContinuousOn crossedDRem (Icc 0 (1 / 4)) := by
  have hD : ContinuousOn crossedD (Icc 0 (1 / 4)) :=
    continuousOn_crossedD.mono (Icc_subset_Icc le_rfl (by norm_num))
  have hl : ContinuousOn (fun s : ℝ => log s * log (1 - 2 * s)) (Icc 0 (1 / 4)) := by
    intro s hs
    rcases hs.1.eq_or_lt with rfl | hs0
    · refine ContinuousAt.continuousWithinAt ?_
      have := tendsto_log_mul_log_one_sub_two_mul
      simpa [ContinuousAt] using this
    · refine ContinuousAt.continuousWithinAt ?_
      have h1 : (1 : ℝ) - 2 * s ≠ 0 := by linarith [hs.2]
      exact (continuousAt_log hs0.ne').mul
        ((by fun_prop : ContinuousAt (fun y : ℝ => 1 - 2 * y) s).log h1)
  exact (hD.add hl).sub (by fun_prop)

theorem hasDerivAt_crossedDRem {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 4)) :
    HasDerivAt crossedDRem
      (logRem (2 * s) / s - 2 * logRem s / (1 - 2 * s) + 131 * s ^ 4 / (6 * (1 - 2 * s))) s := by
  obtain ⟨hs0, hs1⟩ := hs
  have h1 : (1 : ℝ) - 2 * s ≠ 0 := by linarith
  have h1' : (1 : ℝ) - s ≠ 0 := by linarith
  have hD := hasDerivAt_crossedD ⟨hs0, by linarith⟩ (by linarith : s ≠ 1 / 2)
  have d1 : HasDerivAt (fun y : ℝ => 1 - 2 * y) (-2) s := by
    simpa using ((hasDerivAt_id' s).const_mul 2).const_sub 1
  have hl := (hasDerivAt_log hs0.ne').mul (d1.log h1)
  have hp : HasDerivAt (fun y : ℝ => π ^ 2 / 4 - 2 * y + 7 / 9 * y ^ 3 + 5 / 3 * y ^ 4)
      (-2 + 7 / 3 * s ^ 2 + 20 / 3 * s ^ 3) s := by
    have := (((hasDerivAt_const s (π ^ 2 / 4)).sub ((hasDerivAt_id' s).const_mul 2)).add
      ((hasDerivAt_pow 3 s).const_mul (7 / 9))).add ((hasDerivAt_pow 4 s).const_mul (5 / 3))
    refine this.congr_deriv ?_
    push_cast
    ring
  have h := (hD.add hl).sub hp
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => rfl)
  unfold logRem
  field_simp
  ring

/-- **The expansion of `D` at `0`.** On `[0, 1/4]`,
`|D(s) + log s log (1 - 2s) - (π²/4 - 2s + (7/9) s³ + (5/3) s⁴)| ≤ 110 s⁵`. -/
theorem abs_crossedDRem_le {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (1 / 4)) :
    |crossedDRem s| ≤ 110 * s ^ 5 := by
  refine abs_le_mul_pow_of_abs_deriv_le (n := 4) continuousOn_crossedDRem
    (fun y hy => hasDerivAt_crossedDRem hy) (fun y hy => ?_) ?_ s hs
  · obtain ⟨hy0, hy1⟩ := hy
    have hq : 0 < 1 - 2 * y := by linarith
    have e1 : |logRem (2 * y) / y| ≤ 64 * y ^ 4 := by
      rw [abs_div, abs_of_pos hy0, div_le_iff₀ hy0]
      have := abs_logRem_le (x := 2 * y) (by linarith) (by linarith)
      nlinarith
    have e2 : |2 * logRem y / (1 - 2 * y)| ≤ 2 * y ^ 4 := by
      rw [abs_div, abs_of_pos hq, div_le_iff₀ hq, abs_mul, abs_two]
      have := abs_logRem_le (x := y) hy0.le (by linarith)
      have h4 : 0 ≤ y ^ 4 := by positivity
      nlinarith
    have e3 : |131 * y ^ 4 / (6 * (1 - 2 * y))| ≤ 44 * y ^ 4 := by
      have h4 : 0 ≤ y ^ 4 := by positivity
      rw [abs_div, abs_of_nonneg (by positivity), abs_of_pos (by positivity),
        div_le_iff₀ (by positivity)]
      nlinarith
    calc |logRem (2 * y) / y - 2 * logRem y / (1 - 2 * y) + 131 * y ^ 4 / (6 * (1 - 2 * y))|
        ≤ |logRem (2 * y) / y - 2 * logRem y / (1 - 2 * y)| +
            |131 * y ^ 4 / (6 * (1 - 2 * y))| := abs_add_le _ _
      _ ≤ |logRem (2 * y) / y| + |2 * logRem y / (1 - 2 * y)| +
            |131 * y ^ 4 / (6 * (1 - 2 * y))| := by gcongr; exact abs_sub _ _
      _ ≤ 110 * y ^ 4 := by linarith
  · simp [crossedDRem, crossedD_zero]

end QED.TwoLoop.Units
