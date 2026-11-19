/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKInnerX

/-!
# Set (c), Stage K: the L pair at one massive photon

Helper level (no frozen statement). The ladder unit with one photon of mass² `t > 0` has two
placements: the massive photon inside the vertex subgraph (**inner**) or outside it (**outer**).
Each placement is infrared divergent at a massless other photon of mass `λ`,
`L(t, λ²) = F₂(t) log λ + L_in(t) + o(1)` and `L(λ², t) = -F₂(t) log λ + L_out(t) + o(1)`, so the
**L pair** `L_in + L_out` is the infrared-finite object of the Stieltjes identity (S) restricted
to the ladder (Stage K pilot of the set (c) kernel plan). This file defines the two
`λ`-free placements from the representation (3.4) of `docs/TWO-LOOP-UNITS.md` (`ladderGm`,
`ladderCtBracket`, `oneLoopF2`) and reduces the inner one to a single integral.

* `lInner t = ∫₀¹ dY [∫₀¹ dx (G(M_t, h = x) - T₁) + (11/6) Y c/M_t - CT(M_t; Y)/2]`: the soft
  outer logarithm is removed by `T₁ = -Y c (1-x)³/(x M_t)` (section 3.4 at `λ = 0`), with the
  constant of `∫₀¹ x(1-x)³/(x² + (1-x)λ²) dx = -log λ - 11/6 + o(1)`, and the counterterm
  `δ₁ F₂⁽²⁾(λ) → CT/2`.
* `lOuter t = ∫₀¹∫₀¹ G(M = Y², h_t) - (3/2) F₂(t)`: the inner logarithm sits in `δ₁`, and
  `∫₀¹ CT(λ; Y) dY = log λ + 3/2 + o(1)`.
* `lPair t = lInner t + lOuter t`.
* **`lInner_eq`**: `lInner t = ∫₀¹ Ψ_in(Y, M_t(Y)) dY` with `Ψ_in = Φ_in + (11/6) Y c/M - CT/2`
  (`psiIn`), by the closed-form `x`-integration `integral_innerG`.
* `IsLPairDensity ρ`: the pilot statement **(S_L)**, `lPair t = ∫₀¹ ρ(x) Q/(Q+t) dx` for all
  `t > 0`. It is not proved here; the density is the fibre density of the scratch note
  (numerically, `ρ_L(1⁻) = 5/36`, `ρ_L(x) ~ -2 log x` at `x → 0`).

The `λ → 0` statements behind `lInner` and `lOuter` (the link to `L(μ, ν)` at two photon masses)
are not proved here; numerically `lPair 1 = 0.26258700006243295976` agrees with the regulated pair
at `λ² = 10⁻⁴⁰, 10⁻⁵⁰` to 19 digits.
-/

@[expose] public section

open MeasureTheory Set Real

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitLLink

/-- The inner-massive mass `M_t(Y) = Y² + (1-Y) t`. -/
noncomputable def massIn (t Y : ℝ) : ℝ := ladderInnerMass 1 (√t) Y

/-- The `Y`-integrand of the inner-massive placement. -/
noncomputable def lInnerIntegrand (t Y : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..1, (ladderGm 0 (√t) Y x +
      Y * (Y * (1 - Y)) * (1 - x) ^ 3 / (x * massIn t Y))) +
    11 / 6 * (Y * (Y * (1 - Y))) / massIn t Y - ladderCtBracket (√t) Y / 2

/-- **The inner-massive placement** of the ladder, infrared-subtracted. -/
noncomputable def lInner (t : ℝ) : ℝ := ∫ Y in (0 : ℝ)..1, lInnerIntegrand t Y

/-- **The outer-massive placement** of the ladder, infrared-subtracted. -/
noncomputable def lOuter (t : ℝ) : ℝ :=
  (∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderGm (√t) 0 Y x) - 3 / 2 * oneLoopF2 1 (√t)

/-- **The L pair** at photon mass² `t`. -/
noncomputable def lPair (t : ℝ) : ℝ := lInner t + lOuter t

/-- `Ψ_in(Y, c, M) = Φ_in + (11/6) Y c/M - CT(M; Y)/2`, `CT = Y(Y² + 2Y - 2)/(2M) - (Y/2) log M`. -/
noncomputable def psiIn (Y c M : ℝ) : ℝ :=
  phiIn Y c M + 11 / 6 * (Y * c) / M - (Y * (Y ^ 2 + 2 * Y - 2) / (2 * M) - Y / 2 * log M) / 2

/-- **The pilot statement (S_L)** for a candidate density `ρ`. -/
def IsLPairDensity (ρ : ℝ → ℝ) : Prop := ∀ t : ℝ, 0 < t → lPair t = setCKStieltjes ρ t

theorem massIn_pos {t Y : ℝ} (ht : 0 < t) (hY : Y ∈ Icc (0 : ℝ) 1) : 0 < massIn t Y :=
  ladderInnerMass_pos one_pos (sqrt_pos.2 ht) hY

theorem lInnerIntegrand_eq {t Y : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    lInnerIntegrand t Y = psiIn Y (Y * (1 - Y)) (massIn t Y) := by
  have hc : 0 < Y * (1 - Y) := mul_pos hY.1 (by linarith [hY.2])
  have hM := massIn_pos ht ⟨hY.1.le, hY.2.le⟩
  have hI : ∫ x in (0 : ℝ)..1, (ladderGm 0 (√t) Y x +
      Y * (Y * (1 - Y)) * (1 - x) ^ 3 / (x * massIn t Y)) =
      phiIn Y (Y * (1 - Y)) (massIn t Y) := by
    rw [← integral_innerG hc hM]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
    rw [uIoc_of_le zero_le_one] at hx
    exact ladderGm_zero_add_eq_innerG hx.1.ne'
  rw [lInnerIntegrand, hI, psiIn, ladderCtBracket]
  rfl

/-- **The inner placement as a single integral**: `lInner t = ∫₀¹ Ψ_in(Y, Y(1-Y), M_t(Y)) dY`. -/
theorem lInner_eq {t : ℝ} (ht : 0 < t) :
    lInner t = ∫ Y in (0 : ℝ)..1, psiIn Y (Y * (1 - Y)) (massIn t Y) := by
  refine intervalIntegral.integral_congr_ae ((Measure.ae_ne volume 1).mono fun Y h1 hY => ?_)
  rw [uIoc_of_le zero_le_one] at hY
  exact lInnerIntegrand_eq ht ⟨hY.1, lt_of_le_of_ne hY.2 h1⟩

end QED.ChainProof.SetCK

end
