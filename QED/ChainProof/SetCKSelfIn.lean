/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKSelfInX

/-!
# Set (c), Stage K, group G1: the self-energy unit with a massive inner photon

Helper level (no frozen statement). Group G1 of the set (c) kernel plan is the self-energy unit
`S` with the photon of mass² `t > 0` inside the self-energy subgraph and the outer photon
massless, `S(t, 0)`. It is infrared finite by itself. From eq. (5.3) of
`docs/TWO-LOOP-UNITS.md` at infinite Pauli–Villars mass, with `M = M_t(Y) = Y² + (1-Y) t`,
`c = Y(1-Y)` and the counterterm values `V_k(0) = -1`, `V_m(0) = 1/2` (`tendsto_selfVk`,
`tendsto_selfVm`),

`S(t, 0) = 2 ∫₀¹ dY [∫₀¹ (selfGm 0 (√t) Y x - D(Y, x)) dx - d̄₂ + (d̄₂ - σ)/2]`,

`d̄₂ = (1-Y) log M/2 + (1+Y) c/M`, `σ = -(1+Y) log M/2` (`selfIn`). Numerically
`selfIn 1 = -0.59998526940548301815` and `selfIn 4 = -0.28672402713348324136`, the values of the
regulated unit at outer photon mass² `10⁻⁴⁰, 10⁻⁵⁰` (scratch `setCkernel/run2d.out`).

* **`selfInIntegrand_eq`**: the `Y`-integrand is the **per-node function** `F(Y, u)` at
  `u = Q(Y) + t` (`selfInF`, from `integral_selfInG` and `M_t = (1-Y)(Q(Y) + t)`):
  `F = a log u - b log(u + Y) + c_Y log Y + r` with rational `a, b, c_Y, r`; `log(1-Y)` cancels.
* `IsSelfInDensity ρ`: the Stieltjes identity `selfIn t = ∫₀¹ ρ Q/(Q + t)` for all `t > 0`.
-/

@[expose] public section

open MeasureTheory Set Real

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitLLink QED.TwoLoop.UnitSCLimit

/-- `d̄₂(Y, M) = (1-Y) log M/2 + (1+Y) Y(1-Y)/M`, the `δ₂` insertion of the unit `S`. -/
noncomputable def selfInD2 (Y M : ℝ) : ℝ := (1 - Y) * log M / 2 + (1 + Y) * (Y * (1 - Y)) / M

/-- `σ(Y, M) = -(1+Y) log M/2`, the `δ_m` insertion of the unit `S`. -/
noncomputable def selfInSigma (Y M : ℝ) : ℝ := -((1 + Y) / 2 * log M)

/-- The `Y`-integrand of the inner-massive self-energy unit. -/
noncomputable def selfInIntegrand (t Y : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..1, (selfGm 0 (√t) Y x - selfInSub Y x)) - selfInD2 Y (massIn t Y) +
    (selfInD2 Y (massIn t Y) - selfInSigma Y (massIn t Y)) / 2

/-- **The inner-massive self-energy unit** `S(t, 0)`. -/
noncomputable def selfIn (t : ℝ) : ℝ := 2 * ∫ Y in (0 : ℝ)..1, selfInIntegrand t Y

/-- **The Stieltjes identity for G1** for a candidate density `ρ`. -/
def IsSelfInDensity (ρ : ℝ → ℝ) : Prop := ∀ t : ℝ, 0 < t → selfIn t = setCKStieltjes ρ t

/-- The coefficient `a(Y, u)` of `log u` in the per-node function. -/
noncomputable def selfInA (Y u : ℝ) : ℝ :=
  (6 * Y ^ 3 + 4 * Y ^ 2 * u + Y * u ^ 2 - 2 * Y * u - u ^ 2) / (12 * Y ^ 2)

/-- The coefficient `b(Y, u)` of `-log(u + Y)` in the per-node function. -/
noncomputable def selfInB (Y u : ℝ) : ℝ :=
  (Y + u) ^ 3 * (Y ^ 2 + Y * u + Y - u) / (12 * Y ^ 2 * u ^ 2)

/-- The coefficient of `log Y` in the per-node function. -/
noncomputable def selfInCY (Y u : ℝ) : ℝ := Y * (Y ^ 2 + 4 * Y * u + Y + 2 * u) / (12 * u ^ 2)

/-- The rational part of the per-node function. -/
noncomputable def selfInR (Y u : ℝ) : ℝ :=
  (-10 * Y ^ 3 + 7 * Y ^ 2 * u - 10 * Y ^ 2 + 2 * Y * u ^ 2 - 3 * Y * u - 2 * u ^ 2) / (24 * Y * u)

/-- **The per-node function** `F(Y, u)` of the inner-massive self-energy unit. -/
noncomputable def selfInF (Y u : ℝ) : ℝ :=
  selfInA Y u * log u - selfInB Y u * log (u + Y) + selfInCY Y u * log Y + selfInR Y u

/-- The closed form at `c = Y(1-Y)`, `M = (1-Y) u`, plus the counterterms, is `F(Y, u)`. -/
theorem selfInPhi_add_ct {Y u : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    selfInPhi Y (Y * (1 - Y)) ((1 - Y) * u) - selfInD2 Y ((1 - Y) * u) +
      (selfInD2 Y ((1 - Y) * u) - selfInSigma Y ((1 - Y) * u)) / 2 = selfInF Y u := by
  have hY0 := hY.1
  have hY1 : 0 < 1 - Y := by linarith [hY.2]
  have eM : log ((1 - Y) * u) = log (1 - Y) + log u := log_mul hY1.ne' hu.ne'
  have eMc : log ((1 - Y) * u + Y * (1 - Y)) = log (1 - Y) + log (u + Y) := by
    rw [show (1 - Y) * u + Y * (1 - Y) = (1 - Y) * (u + Y) by ring,
      log_mul hY1.ne' (by positivity)]
  have ec : log (Y * (1 - Y)) = log Y + log (1 - Y) := log_mul hY0.ne' hY1.ne'
  unfold selfInPhi selfInD2 selfInSigma selfInF selfInA selfInB selfInCY selfInR
  rw [eM, eMc, ec]
  have := hY0.ne'
  have := hY1.ne'
  have := hu.ne'
  have : 1 - Y ≠ 0 := hY1.ne'
  field_simp
  ring

/-- **The `Y`-integrand is the per-node function** at `u = Q(Y) + t`. -/
theorem selfInIntegrand_eq {t Y : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    selfInIntegrand t Y = selfInF Y (setCKQ Y + t) := by
  have hc : 0 < Y * (1 - Y) := mul_pos hY.1 (by linarith [hY.2])
  have hM := massIn_pos ht ⟨hY.1.le, hY.2.le⟩
  have hI : ∫ x in (0 : ℝ)..1, (selfGm 0 (√t) Y x - selfInSub Y x) =
      selfInPhi Y (Y * (1 - Y)) (massIn t Y) := by
    rw [← integral_selfInG hc hM]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
    rw [uIoc_of_le zero_le_one] at hx
    exact selfGm_zero_sub_eq_selfInG hx.1.ne'
  have hQ : 0 ≤ setCKQ Y := setCKQ_nonneg ⟨hY.1.le, hY.2.le⟩
  rw [selfInIntegrand, hI, massIn, ladderInnerMass_sqrt_eq ht.le hY.2]
  exact selfInPhi_add_ct hY (by linarith)

/-- **G1 as a node integral**: `selfIn t = 2 ∫₀¹ F(Y, Q(Y) + t) dY`. -/
theorem selfIn_eq {t : ℝ} (ht : 0 < t) :
    selfIn t = 2 * ∫ Y in (0 : ℝ)..1, selfInF Y (setCKQ Y + t) := by
  rw [selfIn]
  congr 1
  refine intervalIntegral.integral_congr_ae ((Measure.ae_ne volume 1).mono fun Y h1 hY => ?_)
  rw [uIoc_of_le zero_le_one] at hY
  exact selfInIntegrand_eq ht ⟨hY.1, lt_of_le_of_ne hY.2 h1⟩

end QED.ChainProof.SetCK

end
