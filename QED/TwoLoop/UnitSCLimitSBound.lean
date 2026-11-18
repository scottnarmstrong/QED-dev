/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCLimitSOuter
public import QED.TwoLoop.UnitLCloseLimit
public import QED.TwoLoop.UnitSCCloseIR
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-!
# The self-energy unit S: pointwise bounds uniform in the regulators

Sections 2.3 and 5.4 of `docs/TWO-LOOP-UNITS.md`, stages (2) and (3) of the `S + C` link for the
self-energy pair (the analogue of `QED/TwoLoop/UnitLCloseBound.lean`). With `u = M/(c h)` and
`B = log(1 + u)`, the `x`-integrand of the `a`-integration is (`sForm_eq_phi`)

`selfGm = -ℓ log(M + c h) + (k₁/h) φ₁(u) + (k₂/h²) φ₂(u)`, `ℓ = k₁/h + k₂/h²`,

`φ₁(u) = 1/u - 2B/u - B/u² ∈ [-2, 0]`, `φ₂(u) + 1 = (B - u)/u² ∈ [-1/(1+u), 0]`
(`sPhi1_bounds`, `sPhi2_bounds`). The coefficient `ℓ` of the inner subdivergence `-ℓ log M_Λ` is
the integrand of the counterterm combination `(1-Y)/2 V_k + V_m` (`selfEll_eq`, the pointwise form
of the cancellation of section 2.3). With the weight `ℓ(Y, x) = log 2 - log Y - log(1-Y) - log x`
(`QED.TwoLoop.UnitLLink.ladderEll`), for `0 < Y, x < 1`:

* `abs_selfGm_outer_le`: the terms with the **outer** photon at mass `Λ ≥ 1` (any inner mass
  `0 < μ ≤ Λ`): `|G(Λ, μ)| ≤ (7 + 5 log Λ + 5 ℓ)/Λ²`;
* `abs_selfE1_le`: the term with the **inner** photon at mass `Λ ≥ 1`, with `-ℓ log M_Λ` and the
  large-`M` constant `-k₂/h²` removed (`selfE1`): `|e₁(λ, Λ)| ≤ (5 + 9 log Λ + 5 ℓ)/Λ²` for every
  `λ > 0`;
* `abs_selfR_le`: **the integrand of eq. (5.3)** `G_S(λ) = selfR λ` is bounded by `4 + 5 ℓ` for
  `λ² ≤ 1` (including `λ = 0`): the two-loop part of `S` is infrared finite, uniformly.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology

namespace QED.TwoLoop.UnitSCLimit

open QED.TwoLoop.UnitLLink QED.TwoLoop.UnitSCClose

/-! ### The functions `φ₁`, `φ₂` -/

/-- `φ₁(u) = 1/u - 2 log(1+u)/u - log(1+u)/u²`. -/
noncomputable def sPhi1 (u : ℝ) : ℝ := 1 / u - 2 * log (1 + u) / u - log (1 + u) / u ^ 2

/-- `φ₂(u) = -1 + (log(1+u) - u)/u²`. -/
noncomputable def sPhi2 (u : ℝ) : ℝ := -1 + (log (1 + u) - u) / u ^ 2

/-- **The identity behind the bounds**:
`sForm = -(k₁/h + k₂/h²) A + (k₁/h) φ₁(u) + (k₂/h²) φ₂(u)`, `u = M/(c h)`. -/
theorem sForm_eq_phi {k₁ k₂ c h M A : ℝ} (hM : 0 < M) (hh : 0 < h) (hc : 0 < c) :
    sForm k₁ k₂ c h M A (log (1 + M / (c * h))) =
      -(k₁ / h + k₂ / h ^ 2) * A + k₁ / h * sPhi1 (M / (c * h)) +
        k₂ / h ^ 2 * sPhi2 (M / (c * h)) := by
  unfold sForm sPhi1 sPhi2
  generalize log (1 + M / (c * h)) = B
  have := hM.ne'
  have := hh.ne'
  have := hc.ne'
  field_simp
  ring

theorem sPhi1_eq {u : ℝ} (hu : u ≠ 0) : sPhi1 u = (u - (2 * u + 1) * log (1 + u)) / u ^ 2 := by
  unfold sPhi1
  field_simp
  ring

theorem one_add_mul_log_ge {u : ℝ} (hu : 0 < u) : u ≤ (1 + u) * log (1 + u) := by
  have h := sub_log_one_add_le hu.le
  rw [le_div_iff₀ (by linarith)] at h
  nlinarith

theorem sPhi1_bounds {u : ℝ} (hu : 0 < u) : -2 ≤ sPhi1 u ∧ sPhi1 u ≤ 0 := by
  rw [sPhi1_eq hu.ne']
  have hB0 := log_one_add_nonneg hu.le
  have hBu := log_one_add_le_self hu.le
  have hBl := one_add_mul_log_ge hu
  have hu2 : 0 < u ^ 2 := by positivity
  constructor
  · rw [le_div_iff₀ hu2]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * u + 1) (by linarith : 0 ≤ u - log (1 + u))]
  · rw [div_le_iff₀ hu2]
    nlinarith [mul_nonneg hu.le hB0]

theorem abs_sPhi1_le {u : ℝ} (hu : 0 < u) : |sPhi1 u| ≤ 2 :=
  abs_le.mpr ⟨by linarith [(sPhi1_bounds hu).1], by linarith [(sPhi1_bounds hu).2]⟩

theorem abs_sPhi1_le_div {u : ℝ} (hu : 0 < u) : |sPhi1 u| ≤ (1 + 2 * log (1 + u)) / u := by
  rw [abs_of_nonpos (sPhi1_bounds hu).2, sPhi1_eq hu.ne']
  have hBu := log_one_add_le_self hu.le
  have hu2 : 0 < u ^ 2 := by positivity
  rw [show (1 + 2 * log (1 + u)) / u = (u + 2 * u * log (1 + u)) / u ^ 2 by
    field_simp, ← neg_div, div_le_div_iff_of_pos_right hu2]
  nlinarith

theorem sPhi2_bounds {u : ℝ} (hu : 0 < u) :
    -(1 / (1 + u)) ≤ sPhi2 u + 1 ∧ sPhi2 u + 1 ≤ 0 := by
  have e : sPhi2 u + 1 = (log (1 + u) - u) / u ^ 2 := by unfold sPhi2; ring
  rw [e]
  have h0 := sub_log_one_add_nonneg hu.le
  have h1 := sub_log_one_add_le hu.le
  have hu2 : 0 < u ^ 2 := by positivity
  constructor
  · rw [le_div_iff₀ hu2]
    have : u ^ 2 / (1 + u) = 1 / (1 + u) * u ^ 2 := by ring
    linarith
  · exact div_nonpos_of_nonpos_of_nonneg (by linarith) hu2.le

theorem abs_sPhi2_add_one_le {u : ℝ} (hu : 0 < u) : |sPhi2 u + 1| ≤ 1 / (1 + u) := by
  obtain ⟨h1, h2⟩ := sPhi2_bounds hu
  rw [abs_of_nonpos h2]
  linarith

theorem one_div_one_add_le {u : ℝ} (hu : 0 < u) : 1 / (1 + u) ≤ 1 ∧ 1 / (1 + u) ≤ 1 / u := by
  constructor
  · rw [div_le_one (by linarith)]; linarith
  · exact one_div_le_one_div_of_le hu (by linarith)

theorem abs_sPhi2_le {u : ℝ} (hu : 0 < u) : |sPhi2 u| ≤ 2 := by
  have h := abs_sPhi2_add_one_le hu
  have h1 := (one_div_one_add_le hu).1
  have : |sPhi2 u| ≤ |sPhi2 u + 1| + 1 := by
    calc |sPhi2 u| = |(sPhi2 u + 1) + (-1)| := by ring_nf
      _ ≤ |sPhi2 u + 1| + |(-1 : ℝ)| := abs_add_le _ _
      _ = |sPhi2 u + 1| + 1 := by norm_num
  linarith

/-! ### Abstract bounds -/

theorem abs_coeff_add_le {k₁ k₂ h : ℝ} (hh : 0 < h) :
    |k₁ / h + k₂ / h ^ 2| ≤ |k₁| / h + |k₂| / h ^ 2 := by
  calc |k₁ / h + k₂ / h ^ 2| ≤ |k₁ / h| + |k₂ / h ^ 2| := abs_add_le _ _
    _ = |k₁| / h + |k₂| / h ^ 2 := by
      rw [abs_div, abs_div, abs_of_pos hh, abs_of_pos (by positivity : 0 < h ^ 2)]

theorem abs_mul_div_le {k h t C : ℝ} (hh : 0 < h) (ht : |t| ≤ C) : |k / h * t| ≤ |k| / h * C := by
  rw [abs_mul, abs_div, abs_of_pos hh]
  exact mul_le_mul_of_nonneg_left ht (by positivity)

/-- **The generic bound**: `|sForm| ≤ (|k₁|/h + |k₂|/h²) |A| + 2|k₁|/h + 2|k₂|/h²`. -/
theorem abs_sForm_le {k₁ k₂ c h M A : ℝ} (hc : 0 < c) (hh : 0 < h) (hM : 0 < M) :
    |sForm k₁ k₂ c h M A (log (1 + M / (c * h)))| ≤
      (|k₁| / h + |k₂| / h ^ 2) * |A| + 2 * (|k₁| / h) + 2 * (|k₂| / h ^ 2) := by
  have hu : 0 < M / (c * h) := by positivity
  rw [sForm_eq_phi hM hh hc]
  have t1 : |-(k₁ / h + k₂ / h ^ 2) * A| ≤ (|k₁| / h + |k₂| / h ^ 2) * |A| := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right (abs_coeff_add_le hh) (abs_nonneg A)
  have t2 := abs_mul_div_le (k := k₁) hh (abs_sPhi1_le hu)
  have t3 := abs_mul_div_le (k := k₂) (by positivity : 0 < h ^ 2) (abs_sPhi2_le hu)
  have := abs_add_three (-(k₁ / h + k₂ / h ^ 2) * A) (k₁ / h * sPhi1 (M / (c * h)))
    (k₂ / h ^ 2 * sPhi2 (M / (c * h)))
  linarith

/-- **The bound with the large-`M` constant removed**:
`|sForm + k₂/h²| ≤ (|k₁|/h + |k₂|/h²) |A| + 2|k₁|/h + |k₂|/h²`. -/
theorem abs_sForm_add_le {k₁ k₂ c h M A : ℝ} (hc : 0 < c) (hh : 0 < h) (hM : 0 < M) :
    |sForm k₁ k₂ c h M A (log (1 + M / (c * h))) + k₂ / h ^ 2| ≤
      (|k₁| / h + |k₂| / h ^ 2) * |A| + 2 * (|k₁| / h) + |k₂| / h ^ 2 := by
  have hu : 0 < M / (c * h) := by positivity
  rw [sForm_eq_phi hM hh hc]
  have e : -(k₁ / h + k₂ / h ^ 2) * A + k₁ / h * sPhi1 (M / (c * h)) +
      k₂ / h ^ 2 * sPhi2 (M / (c * h)) + k₂ / h ^ 2 =
      -(k₁ / h + k₂ / h ^ 2) * A + k₁ / h * sPhi1 (M / (c * h)) +
        k₂ / h ^ 2 * (sPhi2 (M / (c * h)) + 1) := by ring
  rw [e]
  have t1 : |-(k₁ / h + k₂ / h ^ 2) * A| ≤ (|k₁| / h + |k₂| / h ^ 2) * |A| := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right (abs_coeff_add_le hh) (abs_nonneg A)
  have t2 := abs_mul_div_le (k := k₁) hh (abs_sPhi1_le hu)
  have t3 := abs_mul_div_le (k := k₂) (by positivity : 0 < h ^ 2)
    ((abs_sPhi2_add_one_le hu).trans (one_div_one_add_le hu).1)
  have := abs_add_three (-(k₁ / h + k₂ / h ^ 2) * A) (k₁ / h * sPhi1 (M / (c * h)))
    (k₂ / h ^ 2 * (sPhi2 (M / (c * h)) + 1))
  linarith

/-- **The bound at large `M`**: with `-ℓ log M` and `-k₂/h²` removed,
`|sForm + ℓ log M + k₂/h²| ≤ (|k₁| + |k₂|/h)(2 + 2 log(1 + u)) c/M`. -/
theorem abs_sForm_e1_le {k₁ k₂ c h M : ℝ} (hc : 0 < c) (hh : 0 < h) (hM : 0 < M) :
    |sForm k₁ k₂ c h M (log (M + c * h)) (log (1 + M / (c * h))) +
        (k₁ / h + k₂ / h ^ 2) * log M + k₂ / h ^ 2| ≤
      (|k₁| + |k₂| / h) * (2 + 2 * log (1 + M / (c * h))) * (c / M) := by
  have hu : 0 < M / (c * h) := by positivity
  have hv : 0 < c * h / M := by positivity
  have hlog : log (M + c * h) = log M + log (1 + c * h / M) := by
    rw [← log_mul hM.ne' (by positivity : (1 : ℝ) + c * h / M ≠ 0).symm.symm]
    congr 1
    field_simp
  rw [sForm_eq_phi hM hh hc, hlog]
  have e : -(k₁ / h + k₂ / h ^ 2) * (log M + log (1 + c * h / M)) + k₁ / h * sPhi1 (M / (c * h)) +
      k₂ / h ^ 2 * sPhi2 (M / (c * h)) + (k₁ / h + k₂ / h ^ 2) * log M + k₂ / h ^ 2 =
      -(k₁ / h + k₂ / h ^ 2) * log (1 + c * h / M) + k₁ / h * sPhi1 (M / (c * h)) +
        k₂ / h ^ 2 * (sPhi2 (M / (c * h)) + 1) := by ring
  rw [e]
  set B := log (1 + M / (c * h)) with hB
  have hB0 : 0 ≤ B := log_one_add_nonneg hu.le
  have hL0 := log_one_add_nonneg hv.le
  have hL1 := log_one_add_le_self hv.le
  have hiu : 1 / (M / (c * h)) = c * h / M := by field_simp
  -- the three terms
  have t1 : |-(k₁ / h + k₂ / h ^ 2) * log (1 + c * h / M)| ≤ (|k₁| + |k₂| / h) * (c / M) := by
    rw [abs_mul, abs_neg, abs_of_nonneg hL0]
    calc |k₁ / h + k₂ / h ^ 2| * log (1 + c * h / M)
        ≤ (|k₁| / h + |k₂| / h ^ 2) * (c * h / M) :=
          mul_le_mul (abs_coeff_add_le hh) hL1 hL0 (by positivity)
      _ = (|k₁| + |k₂| / h) * (c / M) := by field_simp
  have t2 : |k₁ / h * sPhi1 (M / (c * h))| ≤ |k₁| * (1 + 2 * B) * (c / M) := by
    calc |k₁ / h * sPhi1 (M / (c * h))| ≤ |k₁| / h * ((1 + 2 * B) / (M / (c * h))) :=
          abs_mul_div_le hh (abs_sPhi1_le_div hu)
      _ = |k₁| * (1 + 2 * B) * (c / M) := by field_simp
  have t3 : |k₂ / h ^ 2 * (sPhi2 (M / (c * h)) + 1)| ≤ |k₂| / h * (c / M) := by
    calc |k₂ / h ^ 2 * (sPhi2 (M / (c * h)) + 1)| ≤ |k₂| / h ^ 2 * (1 / (M / (c * h))) :=
          abs_mul_div_le (by positivity) ((abs_sPhi2_add_one_le hu).trans (one_div_one_add_le hu).2)
      _ = |k₂| / h * (c / M) := by field_simp
  have := abs_add_three (-(k₁ / h + k₂ / h ^ 2) * log (1 + c * h / M))
    (k₁ / h * sPhi1 (M / (c * h))) (k₂ / h ^ 2 * (sPhi2 (M / (c * h)) + 1))
  have hk1 : 0 ≤ |k₁| := abs_nonneg _
  have hk2 : 0 ≤ |k₂| / h := by positivity
  have hcM : 0 ≤ c / M := by positivity
  nlinarith [mul_nonneg (mul_nonneg hk2 hB0) hcM]

/-! ### The coefficients -/

theorem abs_selfK1_le {Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |selfK1 Y x| ≤ 3 / 2 * (x * (1 - x)) := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hx0, hx1⟩ := hx
  have e : selfK1 Y x = x * (1 - x) / 2 * (2 * Y * x + Y - 2 * x + 2) := by unfold selfK1; ring
  have t0 : 0 ≤ 2 * Y * x + Y - 2 * x + 2 := by nlinarith
  have t1 : 2 * Y * x + Y - 2 * x + 2 ≤ 3 := by nlinarith
  have hp : 0 ≤ x * (1 - x) := mul_nonneg hx0.le (by linarith)
  rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ x * (1 - x) / 2), abs_of_nonneg t0]
  nlinarith

theorem abs_selfK2_le {Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |selfK2 Y x| ≤ 3 / 4 * (x ^ 2 * (1 - x)) := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hx0, hx1⟩ := hx
  have e : selfK2 Y x = -(x ^ 2 * (1 - x) / 4 * (3 - x - Y * (1 - x))) := by unfold selfK2; ring
  have t0 : 0 ≤ 3 - x - Y * (1 - x) := by nlinarith
  have t1 : 3 - x - Y * (1 - x) ≤ 3 := by nlinarith
  have hp : 0 ≤ x ^ 2 * (1 - x) := mul_nonneg (by positivity) (by linarith)
  rw [e, abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ x ^ 2 * (1 - x) / 4),
    abs_of_nonneg t0]
  nlinarith

/-! ### The masses -/

theorem selfH_ge {μ x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : x ≤ ladderInnerMass 1 μ x / x := by
  rw [le_div_iff₀ hx.1]
  unfold ladderInnerMass
  have : 0 ≤ (1 - x) * μ ^ 2 := mul_nonneg (by linarith [hx.2]) (sq_nonneg _)
  nlinarith

theorem selfH_pos {μ x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < ladderInnerMass 1 μ x / x :=
  hx.1.trans_le (selfH_ge hx)

theorem selfM_ge {μ Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) : Y ^ 2 ≤ ladderInnerMass 1 μ Y := by
  unfold ladderInnerMass
  have : 0 ≤ (1 - Y) * μ ^ 2 := mul_nonneg (by linarith [hY.2]) (sq_nonneg _)
  nlinarith

theorem selfM_pos {μ Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) : 0 < ladderInnerMass 1 μ Y :=
  lt_of_lt_of_le (by have := hY.1; positivity) (selfM_ge hY)

theorem selfC_pos {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) : 0 < Y * (1 - Y) :=
  mul_pos hY.1 (by linarith [hY.2])

theorem ladderEll_ge {Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    log 2 - log x - 2 * log Y ≤ 2 * ladderEll Y x := by
  unfold ladderEll
  have h1 := log_nonpos_of_mem hY
  have h2 := log_nonpos_of_mem hx
  have h3 : log (1 - Y) ≤ 0 := log_nonpos (by linarith [hY.2]) (by linarith [hY.1])
  have h4 : 0 ≤ log 2 := log_nonneg (by norm_num)
  linarith

/-- `|log(M + c h)| ≤ log K - log x - 2 log Y` when `Y² ≤ M + c h ≤ K/x`, `K ≥ 1`. -/
theorem abs_log_le_of_bounds {Y x K z : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hK : 1 ≤ K) (hlo : Y ^ 2 ≤ z) (hhi : z ≤ K / x) : |log z| ≤ log K - log x - 2 * log Y := by
  have hY2 : 0 < Y ^ 2 := by have := hY.1; positivity
  have hz : 0 < z := hY2.trans_le hlo
  have hl : 2 * log Y ≤ log z := by
    have e : log (Y ^ 2) = 2 * log Y := by rw [log_pow]; norm_num
    rw [← e]; exact log_le_log hY2 hlo
  have hu : log z ≤ log K - log x := by
    rw [← log_div (by linarith) hx.1.ne']; exact log_le_log hz hhi
  have h1 := log_nonpos_of_mem hY
  have h2 := log_nonpos_of_mem hx
  have hK0 : 0 ≤ log K := log_nonneg hK
  rw [abs_le]
  constructor <;> linarith

/-! ### The outer terms -/

theorem selfK1_div_outer_le {Λ Y x : ℝ} (hΛ : 1 ≤ Λ) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) : |selfK1 Y x| / (ladderInnerMass 1 Λ x / x) ≤ 3 / 2 / Λ ^ 2 := by
  have hk := abs_selfK1_le hY hx
  obtain ⟨hx0, hx1⟩ := hx
  have hm : 0 < ladderInnerMass 1 Λ x := ladderInnerMass_pos one_pos (by linarith) ⟨hx0.le, hx1.le⟩
  have hΛ2 : 1 ≤ Λ ^ 2 := by nlinarith
  rw [div_div_eq_mul_div, div_le_div_iff₀ hm (by positivity)]
  have hmx : (1 - x) * Λ ^ 2 ≤ ladderInnerMass 1 Λ x := by
    unfold ladderInnerMass; nlinarith [sq_nonneg x]
  have : |selfK1 Y x| * x ≤ 3 / 2 * (x ^ 2 * (1 - x)) := by
    have := mul_le_mul_of_nonneg_right hk hx0.le; nlinarith
  have hx2 : x ^ 2 * (1 - x) ≤ 1 - x := by
    have : x ^ 2 ≤ 1 := by nlinarith
    nlinarith
  nlinarith

theorem selfK2_div_outer_le {Λ Y x : ℝ} (hΛ : 1 ≤ Λ) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) : |selfK2 Y x| / (ladderInnerMass 1 Λ x / x) ^ 2 ≤ 3 / 4 / Λ ^ 2 := by
  have hk := abs_selfK2_le hY hx
  obtain ⟨hx0, hx1⟩ := hx
  have hm : 0 < ladderInnerMass 1 Λ x := ladderInnerMass_pos one_pos (by linarith) ⟨hx0.le, hx1.le⟩
  have hΛ2 : 1 ≤ Λ ^ 2 := by nlinarith
  rw [div_pow, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hmx : (1 - x) * Λ ^ 2 ≤ ladderInnerMass 1 Λ x := by
    unfold ladderInnerMass; nlinarith [sq_nonneg x]
  have hmx2 : x ^ 2 ≤ ladderInnerMass 1 Λ x := by
    unfold ladderInnerMass; nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - x) (sq_nonneg Λ)]
  -- `x⁴ (1-x) Λ² ≤ m²`
  have hprod : x ^ 2 * ((1 - x) * Λ ^ 2) ≤ ladderInnerMass 1 Λ x ^ 2 := by
    calc x ^ 2 * ((1 - x) * Λ ^ 2) ≤ ladderInnerMass 1 Λ x * ladderInnerMass 1 Λ x :=
          mul_le_mul hmx2 hmx (by positivity) hm.le
      _ = ladderInnerMass 1 Λ x ^ 2 := (sq _).symm
  have : |selfK2 Y x| * x ^ 2 ≤ 3 / 4 * (x ^ 4 * (1 - x)) := by
    have := mul_le_mul_of_nonneg_right hk (sq_nonneg x); nlinarith
  have hx4 : x ^ 4 * (1 - x) ≤ x ^ 2 * (1 - x) := by
    have : x ^ 4 ≤ x ^ 2 := pow_le_pow_of_le_one hx0.le hx1.le (by norm_num)
    nlinarith
  nlinarith

/-- **The outer-`Λ` terms**: for `Λ ≥ 1`, `0 < μ ≤ Λ` and `0 < Y, x < 1`,
`|G(Λ, μ; Y, x)| ≤ (7 + 5 log Λ + 5 ℓ(Y, x))/Λ²`. -/
theorem abs_selfGm_outer_le {Λ μ Y x : ℝ} (hΛ : 1 ≤ Λ) (hμ : 0 < μ) (hμΛ : μ ≤ Λ)
    (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |selfGm Λ μ Y x| ≤ (7 + 5 * log Λ + 5 * ladderEll Y x) / Λ ^ 2 := by
  have hc := selfC_pos hY
  have hh := selfH_pos (μ := Λ) hx
  have hM := selfM_pos (μ := μ) hY
  have h0 := abs_sForm_le (k₁ := selfK1 Y x) (k₂ := selfK2 Y x)
    (A := log (ladderInnerMass 1 μ Y + Y * (1 - Y) * (ladderInnerMass 1 Λ x / x))) hc hh hM
  have b1 := selfK1_div_outer_le hΛ hY hx
  have b2 := selfK2_div_outer_le hΛ hY hx
  -- the logarithm
  have hΛ2 : 1 ≤ Λ ^ 2 := by nlinarith
  have hlogΛ : log (2 * Λ ^ 2) = log 2 + 2 * log Λ := by
    rw [log_mul (by norm_num) (by positivity), log_pow]; push_cast; ring
  have hA : |log (ladderInnerMass 1 μ Y + Y * (1 - Y) * (ladderInnerMass 1 Λ x / x))| ≤
      log (2 * Λ ^ 2) - log x - 2 * log Y := by
    refine abs_log_le_of_bounds hY hx (by nlinarith) ?_ ?_
    · have := selfM_ge (μ := μ) hY
      have : 0 ≤ Y * (1 - Y) * (ladderInnerMass 1 Λ x / x) := by positivity
      linarith
    · obtain ⟨hx0, hx1⟩ := hx
      obtain ⟨hY0, hY1⟩ := hY
      have hMle : ladderInnerMass 1 μ Y ≤ Λ ^ 2 := by
        unfold ladderInnerMass
        have : μ ^ 2 ≤ Λ ^ 2 := by nlinarith
        nlinarith
      have hmle : ladderInnerMass 1 Λ x ≤ Λ ^ 2 := by
        unfold ladderInnerMass; nlinarith
      have hc4 : Y * (1 - Y) ≤ 1 / 4 := c_le_quarter Y
      rw [le_div_iff₀ hx0, add_mul, mul_assoc, div_mul_cancel₀ _ hx0.ne']
      nlinarith
  have hell := ladderEll_ge hY hx
  have hlΛ : 0 ≤ log Λ := log_nonneg hΛ
  have hl2 : log 2 ≤ 1 := by
    have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hk1 : 0 ≤ |selfK1 Y x| / (ladderInnerMass 1 Λ x / x) := by positivity
  have hk2 : 0 ≤ |selfK2 Y x| / (ladderInnerMass 1 Λ x / x) ^ 2 := by positivity
  have hΛpos : 0 < Λ ^ 2 := by positivity
  unfold selfGm
  refine h0.trans ?_
  rw [hlogΛ] at hA
  have hAb : |log (ladderInnerMass 1 μ Y + Y * (1 - Y) * (ladderInnerMass 1 Λ x / x))| ≤
      1 + 2 * log Λ + 2 * ladderEll Y x := by linarith
  have hsum : |selfK1 Y x| / (ladderInnerMass 1 Λ x / x) +
      |selfK2 Y x| / (ladderInnerMass 1 Λ x / x) ^ 2 ≤ 9 / 4 / Λ ^ 2 := by
    have : 3 / 2 / Λ ^ 2 + 3 / 4 / Λ ^ 2 = 9 / 4 / Λ ^ 2 := by ring
    linarith
  have hprod := mul_le_mul hsum hAb (abs_nonneg _) (by positivity)
  have hell0 := ladderEll_nonneg hY hx
  have e : 9 / 4 / Λ ^ 2 * (1 + 2 * log Λ + 2 * ladderEll Y x) + 2 * (3 / 2 / Λ ^ 2) +
      2 * (3 / 4 / Λ ^ 2) = (27 / 4 + 9 / 2 * log Λ + 9 / 2 * ladderEll Y x) / Λ ^ 2 := by ring
  have hfin : (27 / 4 + 9 / 2 * log Λ + 9 / 2 * ladderEll Y x) / Λ ^ 2 ≤
      (7 + 5 * log Λ + 5 * ladderEll Y x) / Λ ^ 2 := by
    exact (div_le_div_iff_of_pos_right hΛpos).mpr (by linarith)
  linarith [hprod, b1, b2, e, hfin, hk1, hk2]

/-! ### The inner term at mass `Λ` -/

/-- **The coefficient of the inner subdivergence**: `ℓ = k₁/h + k₂/h²` (outer photon mass `lam`),
so that `selfGm lam Λ ≈ -ℓ log M_Λ - k₂/h²` for large `Λ`. -/
noncomputable def selfEll (lam Y x : ℝ) : ℝ :=
  selfK1 Y x / (ladderInnerMass 1 lam x / x) + selfK2 Y x / (ladderInnerMass 1 lam x / x) ^ 2

/-- **The inner term at mass `Λ` with its large logarithm and constant removed**:
`e₁ = G(λ, Λ) + ℓ log M_Λ + k₂/h²`. -/
noncomputable def selfE1 (lam Lam Y x : ℝ) : ℝ :=
  selfGm lam Lam Y x + selfEll lam Y x * log (ladderInnerMass 1 Lam Y) +
    selfK2 Y x / (ladderInnerMass 1 lam x / x) ^ 2

/-- **The pointwise form of the cancellation of section 2.3**: the coefficient `ℓ` of `-log M_Λ` is
the integrand of `(1-Y)/2 V_k + V_m`, the counterterm combination at the same inner parameter. -/
theorem selfEll_eq {lam Y x : ℝ} (hlam : 0 < lam) (hx : x ∈ Ioo (0 : ℝ) 1) :
    selfEll lam Y x = (1 - Y) / 2 * vkIntegrand lam x + vmIntegrand lam x := by
  have hm := ladderInnerMass_pos one_pos hlam ⟨hx.1.le, hx.2.le⟩
  have hx0 := hx.1.ne'
  unfold selfEll vkIntegrand vmIntegrand selfK1 selfK2
  have := hm.ne'
  field_simp
  unfold ladderInnerMass
  ring

theorem selfK_div_bounds {μ Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |selfK1 Y x| / (ladderInnerMass 1 μ x / x) ≤ 3 / 2 ∧
      |selfK2 Y x| / (ladderInnerMass 1 μ x / x) ^ 2 ≤ 3 / 4 ∧
      |selfK1 Y x| + |selfK2 Y x| / (ladderInnerMass 1 μ x / x) ≤ 9 / 4 := by
  have hk1 := abs_selfK1_le hY hx
  have hk2 := abs_selfK2_le hY hx
  have hh := selfH_ge (μ := μ) hx
  obtain ⟨hx0, hx1⟩ := hx
  have hp : x * (1 - x) ≤ 1 := by nlinarith
  have hp2 : x ^ 2 * (1 - x) ≤ x ^ 2 := by nlinarith [sq_nonneg x]
  have hpos : 0 < ladderInnerMass 1 μ x / x := hx0.trans_le hh
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ hpos]
    nlinarith [abs_nonneg (selfK1 Y x)]
  · rw [div_le_iff₀ (by positivity)]
    have : x ^ 2 ≤ (ladderInnerMass 1 μ x / x) ^ 2 := by gcongr
    nlinarith [abs_nonneg (selfK2 Y x)]
  · have : |selfK2 Y x| / (ladderInnerMass 1 μ x / x) ≤ 3 / 4 := by
      rw [div_le_iff₀ hpos]
      nlinarith [abs_nonneg (selfK2 Y x)]
    linarith

theorem log_two_le_one : log 2 ≤ 1 := by
  have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith

/-- **The inner term at mass `Λ`**: for `λ > 0`, `Λ ≥ 1` and `0 < Y, x < 1`,
`|e₁(λ, Λ; Y, x)| ≤ (5 + 9 log Λ + 5 ℓ(Y, x))/Λ²`. -/
theorem abs_selfE1_le {lam Lam Y x : ℝ} (hLam : 1 ≤ Lam) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    |selfE1 lam Lam Y x| ≤ (5 + 9 * log Lam + 5 * ladderEll Y x) / Lam ^ 2 := by
  have hc := selfC_pos hY
  have hh := selfH_pos (μ := lam) hx
  have hM := selfM_pos (μ := Lam) hY
  have h0 := abs_sForm_e1_le (k₁ := selfK1 Y x) (k₂ := selfK2 Y x) hc hh hM
  obtain ⟨-, -, hk⟩ := selfK_div_bounds (μ := lam) hY hx
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hx0, hx1⟩ := hx
  have hL2 : 1 ≤ Lam ^ 2 := by nlinarith
  have hLpos : 0 < Lam ^ 2 := by positivity
  -- `c/M ≤ 1/Λ²`
  have hcM : Y * (1 - Y) / ladderInnerMass 1 Lam Y ≤ 1 / Lam ^ 2 := by
    rw [div_le_div_iff₀ hM hLpos]
    unfold ladderInnerMass
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - Y)
      (by linarith : (0 : ℝ) ≤ 1 - Y)) hLpos.le, sq_nonneg Y]
  -- `log(1 + u) ≤ 2 log Λ + ℓ`
  have hMle : ladderInnerMass 1 Lam Y ≤ Lam ^ 2 := by
    unfold ladderInnerMass; nlinarith
  have hcx : 0 < Y * (1 - Y) * x := by positivity
  have hu : ladderInnerMass 1 Lam Y / (Y * (1 - Y) * (ladderInnerMass 1 lam x / x)) ≤
      Lam ^ 2 / (Y * (1 - Y) * x) := by
    have hhx := selfH_ge (μ := lam) ⟨hx0, hx1⟩
    rw [div_le_div_iff₀ (by positivity) hcx]
    have : Y * (1 - Y) * x ≤ Y * (1 - Y) * (ladderInnerMass 1 lam x / x) :=
      mul_le_mul_of_nonneg_left hhx hc.le
    nlinarith
  have hc4 : Y * (1 - Y) ≤ 1 / 4 := c_le_quarter Y
  have hge1 : 1 ≤ Lam ^ 2 / (Y * (1 - Y) * x) := by
    rw [one_le_div hcx]; nlinarith
  have hB : log (1 + ladderInnerMass 1 Lam Y / (Y * (1 - Y) * (ladderInnerMass 1 lam x / x))) ≤
      2 * log Lam + ladderEll Y x := by
    have hu0 : 0 ≤ ladderInnerMass 1 Lam Y / (Y * (1 - Y) * (ladderInnerMass 1 lam x / x)) := by
      positivity
    calc log (1 + ladderInnerMass 1 Lam Y / (Y * (1 - Y) * (ladderInnerMass 1 lam x / x)))
        ≤ log (2 * Lam ^ 2 / (Y * (1 - Y) * x)) := by
          refine log_le_log (by linarith) ?_
          rw [mul_div_assoc]; linarith
      _ = 2 * log Lam + ladderEll Y x := by
          unfold ladderEll
          rw [log_div (by positivity) hcx.ne', log_mul (by norm_num) (by positivity), log_pow,
            log_mul (by positivity) hx0.ne', log_mul hY0.ne' (by linarith)]
          push_cast
          ring
  have hB0 : 0 ≤ log (1 + ladderInnerMass 1 Lam Y /
      (Y * (1 - Y) * (ladderInnerMass 1 lam x / x))) := log_one_add_nonneg (by positivity)
  have hk0 : 0 ≤ |selfK1 Y x| + |selfK2 Y x| / (ladderInnerMass 1 lam x / x) := by positivity
  have hcM0 : 0 ≤ Y * (1 - Y) / ladderInnerMass 1 Lam Y := by positivity
  unfold selfE1 selfGm selfEll
  refine h0.trans ?_
  have hlL : 0 ≤ log Lam := log_nonneg hLam
  have hell := ladderEll_nonneg ⟨hY0, hY1⟩ ⟨hx0, hx1⟩
  calc (|selfK1 Y x| + |selfK2 Y x| / (ladderInnerMass 1 lam x / x)) *
        (2 + 2 * log (1 + ladderInnerMass 1 Lam Y /
          (Y * (1 - Y) * (ladderInnerMass 1 lam x / x)))) *
        (Y * (1 - Y) / ladderInnerMass 1 Lam Y)
      ≤ 9 / 4 * (2 + 2 * (2 * log Lam + ladderEll Y x)) * (1 / Lam ^ 2) := by
        gcongr
    _ ≤ (5 + 9 * log Lam + 5 * ladderEll Y x) / Lam ^ 2 := by
        rw [mul_one_div]
        exact (div_le_div_iff_of_pos_right hLpos).mpr (by nlinarith)

/-- **The integrand of eq. (5.3) is bounded uniformly in `λ² ≤ 1`**:
`|G_S(λ; Y, x)| ≤ 4 + 5 ℓ(Y, x)` for `0 < Y, x < 1`. -/
theorem abs_selfR_le {lam Y x : ℝ} (hlam : lam ^ 2 ≤ 1) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) : |selfR lam Y x| ≤ 4 + 5 * ladderEll Y x := by
  have hc := selfC_pos hY
  have hh := selfH_pos (μ := lam) hx
  have hM := selfM_pos (μ := lam) hY
  have h0 := abs_sForm_add_le (k₁ := selfK1 Y x) (k₂ := selfK2 Y x)
    (A := log (ladderInnerMass 1 lam Y + Y * (1 - Y) * (ladderInnerMass 1 lam x / x))) hc hh hM
  obtain ⟨b1, b2, -⟩ := selfK_div_bounds (μ := lam) hY hx
  have hA : |log (ladderInnerMass 1 lam Y + Y * (1 - Y) * (ladderInnerMass 1 lam x / x))| ≤
      log 2 - log x - 2 * log Y := by
    refine abs_log_le_of_bounds hY hx (by norm_num) ?_ ?_
    · have := selfM_ge (μ := lam) hY
      have : 0 ≤ Y * (1 - Y) * (ladderInnerMass 1 lam x / x) := by positivity
      linarith
    · obtain ⟨hx0, hx1⟩ := hx
      obtain ⟨hY0, hY1⟩ := hY
      have hMle : ladderInnerMass 1 lam Y ≤ 1 := by
        unfold ladderInnerMass; nlinarith
      have hmle : ladderInnerMass 1 lam x ≤ 1 := by
        unfold ladderInnerMass; nlinarith
      have hc4 : Y * (1 - Y) ≤ 1 / 4 := c_le_quarter Y
      rw [le_div_iff₀ hx0, add_mul, mul_assoc, div_mul_cancel₀ _ hx0.ne']
      nlinarith
  have hell := ladderEll_ge hY hx
  have hell0 := ladderEll_nonneg hY hx
  unfold selfR selfGm
  refine h0.trans ?_
  have hk1 : 0 ≤ |selfK1 Y x| / (ladderInnerMass 1 lam x / x) := by positivity
  have hk2 : 0 ≤ |selfK2 Y x| / (ladderInnerMass 1 lam x / x) ^ 2 := by positivity
  have hprod := mul_le_mul (add_le_add b1 b2) (hA.trans hell) (abs_nonneg _) (by norm_num)
  linarith

end QED.TwoLoop.UnitSCLimit

end
