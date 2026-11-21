/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.Tadpole
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The factorized three-loop vacuum integral and its Laurent expansion

Laporta–Remiddi (1996), eq. (14), give the factorized three-loop vacuum master as
`I₁₈ = C(ω) (-ω⁻³ - 3ω⁻² - 6ω⁻¹ - 10 - 15ω - 21ω² - 28ω³ + O(ω⁴))`, with `d = 4 - 2ω` and
`C(ω) = (π ^ ω Γ(1 + ω)) ³`. It is the cube of the one-loop tadpole with `ν = 1`, `m² = 1`; in
the normalization of `QED.DimReg.FeynmanFamily.integral` (measure `dᵈk / π ^ (d / 2)` per loop)
the tadpole at `d = 4 - 2ω` is `Γ(-1 + ω)` (`QED.DimReg.tadpole_one_one_four_sub`). The factor
`π ^ (3ω)` between the two normalizations (or its inverse, depending on the measure convention
of the source) is entire and nonvanishing; `QED.DimReg.mul_cube_vacuumProduct_laurent` carries
an arbitrary such factor.

The expansion is exact: `Γ(-1 + ω) = Γ(1 + ω) / (ω (ω - 1))`, so
`Γ(-1 + ω)³ = Γ(1 + ω)³ · (-1 / (ω³ (1 - ω)³))`, and
`-1 / (1 - ω)³ = -∑ₙ C(n + 2, 2) ωⁿ`. The coefficients `1, 3, 6, 10, 15, 21, 28` are the
triangular numbers.

## Form for later consumption

We give the expansion in three equivalent forms, all for the closed form of the
dimensionally continued integral (the continuation of `QED.DimReg.FeynmanFamily.integral`):
* `QED.DimReg.vacuumProduct_laurent`: an exact identity with explicit remainder,
  `T(ω)³ = Γ(1 + ω)³ (L(ω) + ω⁴ R(ω))` for `ω ≠ 0, 1`, with `L` the Laurent polynomial above
  and `R(ω) = -(36 - 63ω + 28ω²) / (1 - ω)³`, analytic on `‖ω‖ < 1` and bounded by `600`
  on `‖ω‖ ≤ 1 / 2` (`QED.DimReg.norm_vacuumRemainder_le`).
* `QED.DimReg.eventually_cube_mul_vacuumProduct`, `QED.DimReg.analyticAt_vacuumRegular`:
  near `0` (punctured), `ω³ T(ω)³ = Γ(1 + ω)³ g(ω)` with `g(ω) = -1 / (1 - ω)³` analytic
  at `0`.
* `QED.DimReg.hasSum_vacuumRegular`: all Taylor coefficients, `g(ω) = ∑ₙ -C(n + 2, 2) ωⁿ`
  for `‖ω‖ < 1`.

A bridge theorem that needs the coefficients of `ω⁻³, …, ω³` uses the first form: the
remainder term is `ω⁴` times a function bounded near `0`.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.DimReg

/-- The unit-mass tadpole with `ν = 1` at `d = 4 - 2ω` is `Γ(-1 + ω)`. -/
theorem tadpole_one_one_four_sub (ω : ℂ) : tadpole 1 1 (4 - 2 * ω) = Gamma (-1 + ω) := by
  rw [tadpole, ofReal_one, one_cpow, Gamma_one, div_one, mul_one]
  congr 1
  ring

/-- The factorized three-loop vacuum product: the cube of the unit-mass `ν = 1` tadpole at
`d = 4 - 2ω` (each factor the meromorphic continuation of its parametric integral). -/
noncomputable def vacuumProduct (ω : ℂ) : ℂ := tadpole 1 1 (4 - 2 * ω) ^ 3

/-- The Laurent polynomial `-ω⁻³ - 3ω⁻² - 6ω⁻¹ - 10 - 15ω - 21ω² - 28ω³` of LR96 eq. (14). -/
noncomputable def vacuumLaurentPoly (ω : ℂ) : ℂ :=
  -ω⁻¹ ^ 3 - 3 * ω⁻¹ ^ 2 - 6 * ω⁻¹ - 10 - 15 * ω - 21 * ω ^ 2 - 28 * ω ^ 3

/-- The remainder `R(ω) = -(36 - 63ω + 28ω²) / (1 - ω)³` of the expansion at order `ω⁴`. -/
noncomputable def vacuumRemainder (ω : ℂ) : ℂ := -(36 - 63 * ω + 28 * ω ^ 2) / (1 - ω) ^ 3

/-- The regular part `g(ω) = -1 / (1 - ω)³ = ω³ T(ω)³ / Γ(1 + ω)³`. -/
noncomputable def vacuumRegular (ω : ℂ) : ℂ := -1 / (1 - ω) ^ 3

/-- `Γ(-1 + ω) = Γ(1 + ω) / (ω (ω - 1))`, in multiplied-out form. -/
theorem Gamma_neg_one_add_mul {ω : ℂ} (h0 : ω ≠ 0) (h1 : ω ≠ 1) :
    ω * (ω - 1) * Gamma (-1 + ω) = Gamma (1 + ω) := by
  have e1 : Gamma (1 + ω) = ω * Gamma ω := by
    rw [add_comm, Gamma_add_one _ h0]
  have e2 : Gamma ω = (ω - 1) * Gamma (-1 + ω) := by
    have h := Gamma_add_one (ω - 1) (sub_ne_zero.mpr h1)
    rw [sub_add_cancel] at h
    rw [h, show -1 + ω = ω - 1 by ring]
  rw [e1, e2]; ring

/-- The exact closed form: `T(ω)³ = Γ(1 + ω)³ · (-1 / (ω³ (1 - ω)³))` for `ω ≠ 0, 1`. -/
theorem vacuumProduct_eq {ω : ℂ} (h0 : ω ≠ 0) (h1 : ω ≠ 1) :
    vacuumProduct ω = Gamma (1 + ω) ^ 3 * (vacuumRegular ω / ω ^ 3) := by
  rw [vacuumProduct, tadpole_one_one_four_sub, vacuumRegular, ← Gamma_neg_one_add_mul h0 h1]
  have h1' : (1 : ℂ) - ω ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  ring

/-- The algebraic Laurent identity `g(ω) / ω³ = L(ω) + ω⁴ R(ω)` for `ω ≠ 0, 1`. -/
theorem vacuumRegular_div_eq {ω : ℂ} (h0 : ω ≠ 0) (h1 : ω ≠ 1) :
    vacuumRegular ω / ω ^ 3 = vacuumLaurentPoly ω + ω ^ 4 * vacuumRemainder ω := by
  have h1' : (1 : ℂ) - ω ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [vacuumRegular, vacuumLaurentPoly, vacuumRemainder]
  field_simp
  ring

/-- **LR96 eq. (14), exact form.** For `ω ≠ 0, 1`,
`T(ω)³ = Γ(1 + ω)³ (-ω⁻³ - 3ω⁻² - 6ω⁻¹ - 10 - 15ω - 21ω² - 28ω³ + ω⁴ R(ω))`. -/
theorem vacuumProduct_laurent {ω : ℂ} (h0 : ω ≠ 0) (h1 : ω ≠ 1) :
    vacuumProduct ω =
      Gamma (1 + ω) ^ 3 * (vacuumLaurentPoly ω + ω ^ 4 * vacuumRemainder ω) := by
  rw [vacuumProduct_eq h0 h1, vacuumRegular_div_eq h0 h1]

/-- The same expansion with any normalization factor `c` per loop (e.g. `c = π ^ ω`, which
turns `Γ(1 + ω)³` into LR96's `C(ω) = (π ^ ω Γ(1 + ω))³`). -/
theorem mul_cube_vacuumProduct_laurent (c : ℂ) {ω : ℂ} (h0 : ω ≠ 0) (h1 : ω ≠ 1) :
    c ^ 3 * vacuumProduct ω =
      (c * Gamma (1 + ω)) ^ 3 * (vacuumLaurentPoly ω + ω ^ 4 * vacuumRemainder ω) := by
  rw [vacuumProduct_laurent h0 h1]; ring

/-- The remainder is analytic on the unit disc. -/
theorem analyticAt_vacuumRemainder {ω : ℂ} (hω : ‖ω‖ < 1) : AnalyticAt ℂ vacuumRemainder ω := by
  have h : (1 - ω) ^ 3 ≠ 0 := by
    refine pow_ne_zero 3 (sub_ne_zero.mpr fun h => ?_)
    rw [← h, norm_one] at hω
    exact lt_irrefl _ hω
  unfold vacuumRemainder
  exact (by fun_prop : AnalyticAt ℂ (fun ω : ℂ => -(36 - 63 * ω + 28 * ω ^ 2)) ω).div
    (by fun_prop) h

/-- An explicit bound on the remainder: `‖R(ω)‖ ≤ 600` for `‖ω‖ ≤ 1 / 2`. -/
theorem norm_vacuumRemainder_le {ω : ℂ} (hω : ‖ω‖ ≤ 1 / 2) : ‖vacuumRemainder ω‖ ≤ 600 := by
  have hnum : ‖-(36 - 63 * ω + 28 * ω ^ 2)‖ ≤ 75 := by
    rw [norm_neg]
    calc ‖36 - 63 * ω + 28 * ω ^ 2‖ ≤ ‖36 - 63 * ω‖ + ‖28 * ω ^ 2‖ := norm_add_le _ _
      _ ≤ ‖(36 : ℂ)‖ + ‖63 * ω‖ + ‖28 * ω ^ 2‖ := by gcongr; exact norm_sub_le _ _
      _ = 36 + 63 * ‖ω‖ + 28 * ‖ω‖ ^ 2 := by simp [norm_pow]
      _ ≤ 75 := by nlinarith [norm_nonneg ω]
  have hden : (1 / 2 : ℝ) ≤ ‖1 - ω‖ := by
    have := norm_sub_norm_le (1 : ℂ) ω
    rw [norm_one] at this
    linarith
  have hden3 : (1 / 8 : ℝ) ≤ ‖(1 - ω) ^ 3‖ := by
    rw [norm_pow]
    calc (1 / 8 : ℝ) = (1 / 2) ^ 3 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hden 3
  rw [vacuumRemainder, norm_div, div_le_iff₀ (by linarith)]
  nlinarith

/-- The regular part `g(ω) = -1 / (1 - ω)³` is analytic at `0`. -/
theorem analyticAt_vacuumRegular : AnalyticAt ℂ vacuumRegular 0 := by
  unfold vacuumRegular
  exact analyticAt_const.div (by fun_prop) (by norm_num)

/-- Near `0` (punctured), `ω³ T(ω)³ = Γ(1 + ω)³ g(ω)` with `g` analytic at `0`. -/
theorem eventually_cube_mul_vacuumProduct :
    ∀ᶠ ω in 𝓝[≠] (0 : ℂ), ω ^ 3 * vacuumProduct ω = Gamma (1 + ω) ^ 3 * vacuumRegular ω := by
  have h1 : ∀ᶠ ω in 𝓝[≠] (0 : ℂ), ω ≠ 1 :=
    nhdsWithin_le_nhds (isOpen_ne.mem_nhds (by norm_num : (0 : ℂ) ≠ 1))
  filter_upwards [self_mem_nhdsWithin, h1] with ω h0 h1
  have h0 : ω ≠ 0 := h0
  rw [vacuumProduct_eq h0 h1]
  have : ω ^ 3 ≠ 0 := pow_ne_zero 3 h0
  field_simp

/-- All Taylor coefficients of the regular part: `g(ω) = ∑ₙ -C(n + 2, 2) ωⁿ` for `‖ω‖ < 1`.
The first seven coefficients `-1, -3, -6, -10, -15, -21, -28` are those of LR96 eq. (14). -/
theorem hasSum_vacuumRegular {ω : ℂ} (hω : ‖ω‖ < 1) :
    HasSum (fun n : ℕ => -(((n + 2).choose 2 : ℕ) : ℂ) * ω ^ n) (vacuumRegular ω) := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one 2 hω).neg
  rw [vacuumRegular, neg_div]
  convert h using 2 with n
  ring

end QED.DimReg
