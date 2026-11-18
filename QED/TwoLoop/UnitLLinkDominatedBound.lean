/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLLinkLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-!
# The ladder unit L: a bound on the remainder `R(λ; Y, x)` uniform in `λ`

Section 3.4 of `docs/TWO-LOOP-UNITS.md`. With `c = Y(1-Y)`, `M = Y² + (1-Y)λ²`,
`h = (x² + (1-x)λ²)/x` and `u = M/(c h)`, write `ψ(u) = u - log(1 + u) ∈ [0, min(u, u²)]`. The
first-order part `Q/M² · u` of `Q/M² · log(1 + u)` cancels the terms `x q₀/(M h) - 9c/M` of
`G`, and the `1/x` part of `-x q₀ = 2c(1-x)²/x + p` combines with `-T₁` into
`Y c² (1-x)³ log(1 + u)/M²`. This gives the decomposition (`ladderR_eq_decomp`)

`R = Y x(1-x)/2 · (8 - log(M + c h))/h + Y c²(1-x)³ log(1+u)/M²
    - Y x(1-x) c (8M + 9ch + p) ψ(u)/(2M²)`,

`p = -x(3Y-2) - (4Y-Y²-2)(1-x)`, in which every term is bounded by elementary means. The result
is, for `λ² ≤ 1` and `0 < Y, x < 1`,

* `abs_ladderR_le`: `|R(λ; Y, x)| ≤ 17 (1 - log x - log Y) / max(x, Y)`;
* `abs_ladderR_le_rpow`: `|R(λ; Y, x)| ≤ 153 Y^(-3/4) x^(-3/4)`, a product bound integrable
  on the square.

Numerically the ratio `|R| max(x, Y)/(1 - log x - log Y)` stays below `0.68` (logarithmic grid
of `(0,1)²` down to `10⁻¹²`, `λ ∈ [10⁻¹², 1]`).
-/

@[expose] public section

open Real Set

namespace QED.TwoLoop.UnitLLink

open QED.TwoLoop.Units

/-! ### The pieces of the decomposition -/

/-- `u = M/(c h)`, the argument of `log(1 + u)` in `G`. -/
noncomputable def ladderU (lam Y x : ℝ) : ℝ :=
  ladderInnerMass 1 lam Y / (Y * (1 - Y) * (ladderInnerMass 1 lam x / x))

/-- `ψ(u) = u - log(1 + u)`. -/
noncomputable def ladderPsi (lam Y x : ℝ) : ℝ := ladderU lam Y x - log (1 + ladderU lam Y x)

/-- The bounded polynomial `p = -x(3Y-2) - (4Y-Y²-2)(1-x)` (`-x q₀ = 2c(1-x)²/x + p`). -/
def ladderPolyP (Y x : ℝ) : ℝ := -x * (3 * Y - 2) - (4 * Y - Y ^ 2 - 2) * (1 - x)

/-- `E₁ = Y x(1-x)/2 · (8 - log(M + c h))/h`. -/
noncomputable def ladderRE1 (lam Y x : ℝ) : ℝ :=
  Y * x * (1 - x) / 2 *
    ((8 - log (ladderInnerMass 1 lam Y + Y * (1 - Y) * (ladderInnerMass 1 lam x / x))) /
      (ladderInnerMass 1 lam x / x))

/-- `E₂ = Y c² (1-x)³ log(1 + u)/M²`. -/
noncomputable def ladderRE2 (lam Y x : ℝ) : ℝ :=
  Y * (Y * (1 - Y)) ^ 2 * (1 - x) ^ 3 * log (1 + ladderU lam Y x) / ladderInnerMass 1 lam Y ^ 2

/-- `E₃ₐ = Y x(1-x) c · 8M · ψ/(2M²)`. -/
noncomputable def ladderRE3a (lam Y x : ℝ) : ℝ :=
  Y * x * (1 - x) * (Y * (1 - Y)) * (8 * ladderInnerMass 1 lam Y) * ladderPsi lam Y x /
    (2 * ladderInnerMass 1 lam Y ^ 2)

/-- `E₃ᵦ = Y x(1-x) c · 9ch · ψ/(2M²)`. -/
noncomputable def ladderRE3b (lam Y x : ℝ) : ℝ :=
  Y * x * (1 - x) * (Y * (1 - Y)) * (9 * (Y * (1 - Y)) * (ladderInnerMass 1 lam x / x)) *
    ladderPsi lam Y x / (2 * ladderInnerMass 1 lam Y ^ 2)

/-- `E₃꜀ = Y x(1-x) c · p · ψ/(2M²)`. -/
noncomputable def ladderRE3c (lam Y x : ℝ) : ℝ :=
  Y * x * (1 - x) * (Y * (1 - Y)) * ladderPolyP Y x * ladderPsi lam Y x /
    (2 * ladderInnerMass 1 lam Y ^ 2)

/-- **The decomposition of the remainder**: `R = E₁ + E₂ - (E₃ₐ + E₃ᵦ + E₃꜀)`. -/
theorem ladderR_eq_decomp (lam : ℝ) {Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ladderR lam Y x = ladderRE1 lam Y x + ladderRE2 lam Y x -
      (ladderRE3a lam Y x + ladderRE3b lam Y x + ladderRE3c lam Y x) := by
  have hY0 : Y ≠ 0 := hY.1.ne'
  have hY1 : 1 - Y ≠ 0 := by linarith [hY.2]
  have hx0 : x ≠ 0 := hx.1.ne'
  have hM : ladderInnerMass 1 lam Y ≠ 0 := by
    have := ladderInnerMass_one_ge (lam := lam) hY.2.le
    have : 0 < Y ^ 2 := by have := hY.1; positivity
    linarith
  have hm : ladderInnerMass 1 lam x ≠ 0 := by
    have := ladderInnerMass_one_ge (lam := lam) hx.2.le
    have : 0 < x ^ 2 := by have := hx.1; positivity
    linarith
  unfold ladderR ladderG ladderT1 ladderRE1 ladderRE2 ladderRE3a ladderRE3b ladderRE3c ladderPsi
    ladderU ladderPolyP
  generalize ladderInnerMass 1 lam Y = M at hM ⊢
  generalize ladderInnerMass 1 lam x = m at hm ⊢
  generalize log (M + Y * (1 - Y) * (m / x)) = L1
  generalize log (1 + M / (Y * (1 - Y) * (m / x))) = L2
  field_simp
  ring

/-! ### Elementary bounds -/

/-- `0 ≤ u - log(1 + u) ≤ u` and `u - log(1 + u) ≤ u²` for `u ≥ 0`. -/
theorem sub_log_one_add_bounds {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ u - log (1 + u) ∧ u - log (1 + u) ≤ u ∧ u - log (1 + u) ≤ u ^ 2 := by
  have h1 : 0 < 1 + u := by linarith
  have hle := Real.log_le_sub_one_of_pos h1
  have hge := Real.one_sub_inv_le_log_of_pos h1
  have hnn : 0 ≤ log (1 + u) := Real.log_nonneg (by linarith)
  refine ⟨by linarith, by linarith, ?_⟩
  have e : 1 - (1 + u)⁻¹ = u / (1 + u) := by field_simp; ring
  rw [e] at hge
  have : u - u / (1 + u) ≤ u ^ 2 := by
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ h1]
    nlinarith
  linarith

/-- `|p| ≤ 2` on the unit square. -/
theorem abs_ladderPolyP_le {Y x : ℝ} (hY : Y ∈ Icc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    |ladderPolyP Y x| ≤ 2 := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hx0, hx1⟩ := hx
  unfold ladderPolyP
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hx0 hY0, mul_nonneg (sub_nonneg.2 hx1) hY0,
    mul_nonneg (sub_nonneg.2 hx1) (mul_nonneg hY0 hY0), mul_nonneg hx0 (sub_nonneg.2 hY1),
    mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hY1)]

/-- The standing hypotheses on `M` and `m = x² + (1-x)λ²`. -/
structure LadderMassBounds (Y x M m : ℝ) : Prop where
  hY : Y ∈ Ioo (0 : ℝ) 1
  hx : x ∈ Ioo (0 : ℝ) 1
  hM1 : Y ^ 2 ≤ M
  hM2 : M ≤ 1
  hm1 : x ^ 2 ≤ m
  hm2 : m ≤ 1

namespace LadderMassBounds

variable {Y x M m : ℝ} (H : LadderMassBounds Y x M m)
include H

theorem Y_pos : 0 < Y := H.hY.1
theorem x_pos : 0 < x := H.hx.1
theorem one_sub_Y_pos : 0 < 1 - Y := by linarith [H.hY.2]
theorem one_sub_x_pos : 0 < 1 - x := by linarith [H.hx.2]
theorem M_pos : 0 < M := lt_of_lt_of_le (by have := H.Y_pos; positivity) H.hM1
theorem m_pos : 0 < m := lt_of_lt_of_le (by have := H.x_pos; positivity) H.hm1
theorem c_pos : 0 < Y * (1 - Y) := mul_pos H.Y_pos H.one_sub_Y_pos

/-- `Y (1-x) x²/m ∈ [0, 1]`. -/
theorem weight_le : Y * (1 - x) * x ^ 2 / m ≤ 1 := by
  have := H.Y_pos; have := H.x_pos; have := H.one_sub_x_pos; have := H.m_pos
  rw [div_le_one H.m_pos]
  have : Y * (1 - x) ≤ 1 := by nlinarith [H.hY.2, H.hx.2]
  nlinarith [H.hm1]

theorem weight_nonneg : 0 ≤ Y * (1 - x) * x ^ 2 / m := by
  have := H.Y_pos; have := H.x_pos; have := H.one_sub_x_pos; have := H.m_pos
  positivity

/-- `u = M/(c h) > 0`. -/
theorem u_pos : 0 < M / (Y * (1 - Y) * (m / x)) := by
  have := H.M_pos; have := H.c_pos; have := H.m_pos; have := H.x_pos
  positivity

/-- **`|E₁| ≤ (9 - log x - log Y)/2`**. -/
theorem abs_E1_le :
    |Y * x * (1 - x) / 2 * ((8 - log (M + Y * (1 - Y) * (m / x))) / (m / x))| ≤
      (9 - log x - log Y) / 2 := by
  have hx0 := H.x_pos; have hY0 := H.Y_pos; have hm0 := H.m_pos; have hM0 := H.M_pos
  have hc := H.c_pos
  set L := log (M + Y * (1 - Y) * (m / x)) with hL
  have hk : Y * x * (1 - x) / 2 * ((8 - L) / (m / x)) = Y * (1 - x) * x ^ 2 / m / 2 * (8 - L) := by
    field_simp
  have hhx : x ≤ m / x := by rw [le_div_iff₀ hx0]; nlinarith [H.hm1]
  have hh1 : m / x ≤ 1 / x := div_le_div_of_nonneg_right H.hm2 hx0.le
  have hlogx : log x ≤ 0 := Real.log_nonpos hx0.le H.hx.2.le
  have hlogY : log Y ≤ 0 := Real.log_nonpos hY0.le H.hY.2.le
  -- lower bound for `L`
  have hlow : log Y + log x ≤ L := by
    rw [← Real.log_mul hY0.ne' hx0.ne']
    apply Real.log_le_log (mul_pos hY0 hx0)
    have : Y * (1 - Y) * x ≤ Y * (1 - Y) * (m / x) := mul_le_mul_of_nonneg_left hhx hc.le
    nlinarith [H.hM1, H.hx.2, H.hY.2]
  -- upper bound for `L`
  have hup : L ≤ 1 - log x := by
    have hpos : 0 < M + Y * (1 - Y) * (m / x) := by positivity
    have h2 : M + Y * (1 - Y) * (m / x) ≤ 2 / x := by
      have hc1 : Y * (1 - Y) ≤ 1 := by nlinarith [H.hY.2]
      have : Y * (1 - Y) * (m / x) ≤ 1 / x :=
        (mul_le_of_le_one_left (by positivity) hc1).trans hh1
      have : 1 ≤ 1 / x := by rw [le_div_iff₀ hx0]; linarith [H.hx.2]
      have e : 2 / x = 1 / x + 1 / x := by ring
      linarith [H.hM2]
    have := Real.log_le_log hpos h2
    rw [Real.log_div two_ne_zero hx0.ne'] at this
    linarith [Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2)]
  rw [hk, abs_mul, abs_of_nonneg (by have := H.weight_nonneg; positivity)]
  have habs : |8 - L| ≤ 9 - log x - log Y := by
    rw [abs_le]; constructor <;> linarith
  have := H.weight_le
  have := H.weight_nonneg
  calc Y * (1 - x) * x ^ 2 / m / 2 * |8 - L| ≤ 1 / 2 * (9 - log x - log Y) := by
        apply mul_le_mul (by linarith) habs (abs_nonneg _) (by norm_num)
    _ = (9 - log x - log Y) / 2 := by ring

/-- **`0 ≤ E₂`**. -/
theorem E2_nonneg :
    0 ≤ Y * (Y * (1 - Y)) ^ 2 * (1 - x) ^ 3 * log (1 + M / (Y * (1 - Y) * (m / x))) / M ^ 2 := by
  have := H.Y_pos; have := H.one_sub_x_pos; have := H.c_pos; have := H.M_pos
  have := Real.log_nonneg (by linarith [H.u_pos] : (1 : ℝ) ≤ 1 + M / (Y * (1 - Y) * (m / x)))
  positivity

/-- **`E₂ ≤ 1/x`** (from `log(1 + u) ≤ u`). -/
theorem E2_le_inv_x :
    Y * (Y * (1 - Y)) ^ 2 * (1 - x) ^ 3 * log (1 + M / (Y * (1 - Y) * (m / x))) / M ^ 2 ≤
      1 / x := by
  have hY0 := H.Y_pos; have hx0 := H.x_pos; have hx1 := H.one_sub_x_pos; have hc := H.c_pos
  have hM0 := H.M_pos; have hm0 := H.m_pos; have hu := H.u_pos
  set u := M / (Y * (1 - Y) * (m / x)) with hu_def
  have hL := sub_log_one_add_bounds hu.le
  have hL0 : 0 ≤ log (1 + u) := Real.log_nonneg (by linarith)
  have h3 : (1 - x) ^ 3 ≤ 1 := pow_le_one₀ hx1.le (by linarith)
  have hk : (1 - x) ^ 3 * log (1 + u) ≤ u := by
    have := mul_le_of_le_one_left hL0 h3
    linarith [hL.2.1]
  calc Y * (Y * (1 - Y)) ^ 2 * (1 - x) ^ 3 * log (1 + u) / M ^ 2
      = Y * (Y * (1 - Y)) ^ 2 * ((1 - x) ^ 3 * log (1 + u)) / M ^ 2 := by ring
    _ ≤ Y * (Y * (1 - Y)) ^ 2 * u / M ^ 2 := by gcongr
    _ = Y * (Y * (1 - Y)) * x / (M * m) := by rw [hu_def]; field_simp
    _ ≤ 1 / x := by
      rw [div_le_div_iff₀ (by positivity) hx0]
      have h1 : Y * (Y * (1 - Y)) ≤ M := by nlinarith [H.hM1]
      have := mul_le_mul h1 H.hm1 (by positivity) hM0.le
      nlinarith

/-- **`E₂ ≤ (2 - log x - log Y)/Y`** (from `M ≥ Y²` and `u ≤ 1/(c x)`). -/
theorem E2_le_inv_Y :
    Y * (Y * (1 - Y)) ^ 2 * (1 - x) ^ 3 * log (1 + M / (Y * (1 - Y) * (m / x))) / M ^ 2 ≤
      (2 - log x - log Y) / Y := by
  have hY0 := H.Y_pos; have hx0 := H.x_pos; have hx1 := H.one_sub_x_pos; have hc := H.c_pos
  have hM0 := H.M_pos; have hm0 := H.m_pos; have hu := H.u_pos; have hY1 := H.one_sub_Y_pos
  set u := M / (Y * (1 - Y) * (m / x)) with hu_def
  have hL0 : 0 ≤ log (1 + u) := Real.log_nonneg (by linarith)
  have h3 : (1 - x) ^ 3 ≤ 1 := pow_le_one₀ hx1.le (by linarith)
  -- `log(1 + u) ≤ log 2 - log Y - log x - log(1 - Y)`
  have hcx : 0 < Y * (1 - Y) * x := by positivity
  have hcx1 : Y * (1 - Y) * x ≤ 1 := by
    have : Y * (1 - Y) ≤ 1 := by nlinarith [H.hY.2]
    nlinarith [H.hx.2]
  have hu1 : u ≤ 1 / (Y * (1 - Y) * x) := by
    rw [hu_def]
    have hhx : x ≤ m / x := by rw [le_div_iff₀ hx0]; nlinarith [H.hm1]
    have : Y * (1 - Y) * x ≤ Y * (1 - Y) * (m / x) := mul_le_mul_of_nonneg_left hhx hc.le
    calc M / (Y * (1 - Y) * (m / x)) ≤ 1 / (Y * (1 - Y) * (m / x)) :=
          div_le_div_of_nonneg_right H.hM2 (by positivity)
      _ ≤ 1 / (Y * (1 - Y) * x) := one_div_le_one_div_of_le hcx this
  have h2 : 1 + u ≤ 2 / (Y * (1 - Y) * x) := by
    have : 1 ≤ 1 / (Y * (1 - Y) * x) := by rw [le_div_iff₀ hcx]; linarith
    have e : 2 / (Y * (1 - Y) * x) = 1 / (Y * (1 - Y) * x) + 1 / (Y * (1 - Y) * x) := by ring
    linarith
  have hlogL : log (1 + u) ≤ log 2 - log Y - log (1 - Y) - log x := by
    have := Real.log_le_log (by linarith) h2
    rw [Real.log_div two_ne_zero hcx.ne', Real.log_mul (by positivity) hx0.ne',
      Real.log_mul hY0.ne' hY1.ne'] at this
    linarith
  have hlog2 : log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2)]
  have hlog2' : 0 ≤ log 2 := Real.log_nonneg (by norm_num)
  have hlogx : log x ≤ 0 := Real.log_nonpos hx0.le H.hx.2.le
  have hlogY : log Y ≤ 0 := Real.log_nonpos hY0.le H.hY.2.le
  have hent := neg_mul_log_le_one_sub hY1
  have hent0 : 0 ≤ -((1 - Y) * log (1 - Y)) := by
    have : log (1 - Y) ≤ 0 := Real.log_nonpos hY1.le (by linarith)
    nlinarith
  -- `(1 - Y)² log(1 + u) ≤ 2 - log x - log Y`
  have hkey : (1 - Y) ^ 2 * log (1 + u) ≤ 2 - log x - log Y := by
    have hA : 0 ≤ log 2 - log Y - log x := by linarith
    have hs1 : (1 - Y) ^ 2 ≤ 1 := pow_le_one₀ hY1.le (by linarith)
    have e1 : (1 - Y) ^ 2 * log (1 + u) ≤
        (1 - Y) ^ 2 * (log 2 - log Y - log x) + (1 - Y) * (-((1 - Y) * log (1 - Y))) := by
      have := mul_le_mul_of_nonneg_left hlogL (by positivity : (0 : ℝ) ≤ (1 - Y) ^ 2)
      nlinarith
    have e2 : (1 - Y) ^ 2 * (log 2 - log Y - log x) ≤ log 2 - log Y - log x :=
      mul_le_of_le_one_left hA hs1
    have e3 : (1 - Y) * (-((1 - Y) * log (1 - Y))) ≤ 1 := by
      have : -((1 - Y) * log (1 - Y)) ≤ 1 := by linarith
      nlinarith
    linarith
  calc Y * (Y * (1 - Y)) ^ 2 * (1 - x) ^ 3 * log (1 + u) / M ^ 2
      = Y * (Y * (1 - Y)) ^ 2 * ((1 - x) ^ 3 * log (1 + u)) / M ^ 2 := by ring
    _ ≤ Y * (Y * (1 - Y)) ^ 2 * log (1 + u) / M ^ 2 := by
        gcongr
        exact mul_le_of_le_one_left hL0 h3
    _ ≤ Y * (Y * (1 - Y)) ^ 2 * log (1 + u) / (Y ^ 2) ^ 2 := by
        gcongr
        exact H.hM1
    _ = (1 - Y) ^ 2 * log (1 + u) / Y := by field_simp
    _ ≤ (2 - log x - log Y) / Y := by gcongr

/-- **`0 ≤ E₃ₐ ≤ 4`** (from `ψ ≤ u`). -/
theorem E3a_bounds :
    0 ≤ Y * x * (1 - x) * (Y * (1 - Y)) * (8 * M) *
        (M / (Y * (1 - Y) * (m / x)) - log (1 + M / (Y * (1 - Y) * (m / x)))) / (2 * M ^ 2) ∧
    Y * x * (1 - x) * (Y * (1 - Y)) * (8 * M) *
        (M / (Y * (1 - Y) * (m / x)) - log (1 + M / (Y * (1 - Y) * (m / x)))) / (2 * M ^ 2) ≤
      4 := by
  have hY0 := H.Y_pos; have hx0 := H.x_pos; have hx1 := H.one_sub_x_pos; have hc := H.c_pos
  have hM0 := H.M_pos; have hm0 := H.m_pos; have hu := H.u_pos
  have hY1 := H.one_sub_Y_pos.ne'
  set u := M / (Y * (1 - Y) * (m / x)) with hu_def
  have hL := sub_log_one_add_bounds hu.le
  refine ⟨by have := hL.1; positivity, ?_⟩
  calc Y * x * (1 - x) * (Y * (1 - Y)) * (8 * M) * (u - log (1 + u)) / (2 * M ^ 2)
      ≤ Y * x * (1 - x) * (Y * (1 - Y)) * (8 * M) * u / (2 * M ^ 2) := by gcongr; exact hL.2.1
    _ = 4 * (Y * (1 - x) * x ^ 2 / m) := by rw [hu_def]; field_simp; norm_num
    _ ≤ 4 * 1 := by gcongr; exact H.weight_le
    _ = 4 := by ring

/-- **`0 ≤ E₃ᵦ ≤ 9/2`** (from `ψ ≤ u²`). -/
theorem E3b_bounds :
    0 ≤ Y * x * (1 - x) * (Y * (1 - Y)) * (9 * (Y * (1 - Y)) * (m / x)) *
        (M / (Y * (1 - Y) * (m / x)) - log (1 + M / (Y * (1 - Y) * (m / x)))) / (2 * M ^ 2) ∧
    Y * x * (1 - x) * (Y * (1 - Y)) * (9 * (Y * (1 - Y)) * (m / x)) *
        (M / (Y * (1 - Y) * (m / x)) - log (1 + M / (Y * (1 - Y) * (m / x)))) / (2 * M ^ 2) ≤
      9 / 2 := by
  have hY0 := H.Y_pos; have hx0 := H.x_pos; have hx1 := H.one_sub_x_pos; have hc := H.c_pos
  have hM0 := H.M_pos; have hm0 := H.m_pos; have hu := H.u_pos
  have hY1 := H.one_sub_Y_pos.ne'
  set u := M / (Y * (1 - Y) * (m / x)) with hu_def
  have hL := sub_log_one_add_bounds hu.le
  refine ⟨by have := hL.1; positivity, ?_⟩
  calc Y * x * (1 - x) * (Y * (1 - Y)) * (9 * (Y * (1 - Y)) * (m / x)) * (u - log (1 + u)) /
        (2 * M ^ 2)
      ≤ Y * x * (1 - x) * (Y * (1 - Y)) * (9 * (Y * (1 - Y)) * (m / x)) * u ^ 2 /
        (2 * M ^ 2) := by gcongr; exact hL.2.2
    _ = 9 / 2 * (Y * (1 - x) * x ^ 2 / m) := by rw [hu_def]; field_simp
    _ ≤ 9 / 2 * 1 := by gcongr; exact H.weight_le
    _ = 9 / 2 := by ring

/-- **`|E₃꜀| ≤ min(1/Y, 1/((1-Y)x))`** (from `ψ ≤ u`, `ψ ≤ u²`), for `|p| ≤ 2`. -/
theorem abs_E3c_le {p : ℝ} (hp : |p| ≤ 2) :
    |Y * x * (1 - x) * (Y * (1 - Y)) * p *
        (M / (Y * (1 - Y) * (m / x)) - log (1 + M / (Y * (1 - Y) * (m / x)))) / (2 * M ^ 2)| ≤
      1 / Y ∧
    |Y * x * (1 - x) * (Y * (1 - Y)) * p *
        (M / (Y * (1 - Y) * (m / x)) - log (1 + M / (Y * (1 - Y) * (m / x)))) / (2 * M ^ 2)| ≤
      1 / ((1 - Y) * x) := by
  have hY0 := H.Y_pos; have hx0 := H.x_pos; have hx1 := H.one_sub_x_pos; have hc := H.c_pos
  have hM0 := H.M_pos; have hm0 := H.m_pos; have hu := H.u_pos; have hY1 := H.one_sub_Y_pos
  set u := M / (Y * (1 - Y) * (m / x)) with hu_def
  have hL := sub_log_one_add_bounds hu.le
  have hbase : |Y * x * (1 - x) * (Y * (1 - Y)) * p * (u - log (1 + u)) / (2 * M ^ 2)| ≤
      Y * x * (Y * (1 - Y)) * (u - log (1 + u)) / M ^ 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg hL.1, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Y * x *
      (1 - x) * (Y * (1 - Y))), abs_of_pos (by positivity : 0 < 2 * M ^ 2)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : Y * x * (1 - x) * (Y * (1 - Y)) ≤ Y * x * (Y * (1 - Y)) := by
      have : 0 ≤ Y * x * (Y * (1 - Y)) := by positivity
      nlinarith
    have := mul_le_mul h1 hp (abs_nonneg _) (by positivity)
    have := mul_le_mul_of_nonneg_right this (mul_nonneg hL.1 (sq_nonneg M))
    nlinarith
  refine ⟨hbase.trans ?_, hbase.trans ?_⟩
  · calc Y * x * (Y * (1 - Y)) * (u - log (1 + u)) / M ^ 2
        ≤ Y * x * (Y * (1 - Y)) * u / M ^ 2 := by gcongr; exact hL.2.1
      _ = Y * x ^ 2 / (M * m) := by rw [hu_def]; field_simp
      _ ≤ 1 / Y := by
        rw [div_le_div_iff₀ (by positivity) hY0]
        have := mul_le_mul H.hM1 H.hm1 (by positivity) hM0.le
        nlinarith
  · calc Y * x * (Y * (1 - Y)) * (u - log (1 + u)) / M ^ 2
        ≤ Y * x * (Y * (1 - Y)) * u ^ 2 / M ^ 2 := by gcongr; exact hL.2.2
      _ = x ^ 3 / ((1 - Y) * m ^ 2) := by rw [hu_def]; field_simp
      _ ≤ 1 / ((1 - Y) * x) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : (x ^ 2) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (by positivity) H.hm1 2
        nlinarith

end LadderMassBounds

/-! ### The uniform bound -/

/-- **The uniform bound on the remainder**: for `|λ| ≤ 1` and `0 < Y, x < 1`,
`|R(λ; Y, x)| ≤ 17 (1 - log x - log Y)/max(x, Y)`. -/
theorem abs_ladderR_le {lam Y x : ℝ} (hlam : |lam| ≤ 1) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    |ladderR lam Y x| ≤ 17 * (1 - log x - log Y) / max x Y := by
  have hYI : Y ∈ Icc (0 : ℝ) 1 := ⟨hY.1.le, hY.2.le⟩
  have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have H : LadderMassBounds Y x (ladderInnerMass 1 lam Y) (ladderInnerMass 1 lam x) :=
    ⟨hY, hx, ladderInnerMass_one_ge hY.2.le, ladderInnerMass_one_le hYI hlam,
      ladderInnerMass_one_ge hx.2.le, ladderInnerMass_one_le hxI hlam⟩
  have hY0 := hY.1; have hx0 := hx.1
  have e1 : |ladderRE1 lam Y x| ≤ (9 - log x - log Y) / 2 := H.abs_E1_le
  have e2a : ladderRE2 lam Y x ≤ 1 / x := H.E2_le_inv_x
  have e2b : ladderRE2 lam Y x ≤ (2 - log x - log Y) / Y := H.E2_le_inv_Y
  have e2n : 0 ≤ ladderRE2 lam Y x := H.E2_nonneg
  have e3a : 0 ≤ ladderRE3a lam Y x ∧ ladderRE3a lam Y x ≤ 4 := H.E3a_bounds
  have e3b : 0 ≤ ladderRE3b lam Y x ∧ ladderRE3b lam Y x ≤ 9 / 2 := H.E3b_bounds
  have e3c : |ladderRE3c lam Y x| ≤ 1 / Y ∧ |ladderRE3c lam Y x| ≤ 1 / ((1 - Y) * x) :=
    H.abs_E3c_le (abs_ladderPolyP_le hYI hxI)
  set ℓ := 1 - log x - log Y with hℓ
  have hlogx : log x ≤ 0 := Real.log_nonpos hx0.le hx.2.le
  have hlogY : log Y ≤ 0 := Real.log_nonpos hY0.le hY.2.le
  have hℓ1 : 1 ≤ ℓ := by linarith
  set mx := max x Y with hmx
  have hmx0 : 0 < mx := lt_max_of_lt_left hx0
  have hmx1 : mx ≤ 1 := max_le hx.2.le hY.2.le
  -- `E₂ ≤ (ℓ + 1)/max(x, Y)`
  have e2 : ladderRE2 lam Y x ≤ (ℓ + 1) / mx := by
    rcases le_total x Y with h | h
    · rw [hmx, max_eq_right h]
      calc ladderRE2 lam Y x ≤ (2 - log x - log Y) / Y := e2b
        _ = (ℓ + 1) / Y := by rw [hℓ]; ring
    · rw [hmx, max_eq_left h]
      calc ladderRE2 lam Y x ≤ 1 / x := e2a
        _ ≤ (ℓ + 1) / x := by gcongr; linarith
  -- `|E₃꜀| ≤ 2/max(x, Y)`
  have e3 : |ladderRE3c lam Y x| ≤ 2 / mx := by
    rcases le_total x Y with h | h
    · rw [hmx, max_eq_right h]
      calc |ladderRE3c lam Y x| ≤ 1 / Y := e3c.1
        _ ≤ 2 / Y := by gcongr; norm_num
    · rw [hmx, max_eq_left h]
      rcases le_total (1 / 2) Y with hY2 | hY2
      · calc |ladderRE3c lam Y x| ≤ 1 / Y := e3c.1
          _ ≤ 2 := by rw [div_le_iff₀ hY0]; linarith
          _ ≤ 2 / x := by rw [le_div_iff₀ hx0]; nlinarith [hx.2]
      · calc |ladderRE3c lam Y x| ≤ 1 / ((1 - Y) * x) := e3c.2
          _ ≤ 2 / x := by
            rw [div_le_div_iff₀ (mul_pos (by linarith) hx0) hx0]
            nlinarith
  rw [ladderR_eq_decomp lam hY hx]
  have htri : |ladderRE1 lam Y x + ladderRE2 lam Y x -
      (ladderRE3a lam Y x + ladderRE3b lam Y x + ladderRE3c lam Y x)| ≤
      |ladderRE1 lam Y x| + ladderRE2 lam Y x + ladderRE3a lam Y x + ladderRE3b lam Y x +
        |ladderRE3c lam Y x| := by
    have h1 := abs_sub (ladderRE1 lam Y x + ladderRE2 lam Y x)
      (ladderRE3a lam Y x + ladderRE3b lam Y x + ladderRE3c lam Y x)
    have h2 := abs_add_le (ladderRE1 lam Y x) (ladderRE2 lam Y x)
    have h3 := abs_add_le (ladderRE3a lam Y x + ladderRE3b lam Y x) (ladderRE3c lam Y x)
    have h4 := abs_add_le (ladderRE3a lam Y x) (ladderRE3b lam Y x)
    rw [abs_of_nonneg e2n] at h2
    rw [abs_of_nonneg e3a.1] at h4
    rw [abs_of_nonneg e3b.1] at h4
    linarith
  have hsum : (9 - log x - log Y) / 2 + (ℓ + 1) / mx + 4 + 9 / 2 + 2 / mx =
      (((8 + ℓ) / 2 + 4 + 9 / 2) * mx + (ℓ + 1) + 2) / mx := by
    rw [hℓ]; field_simp; ring
  have key : ((8 + ℓ) / 2 + 4 + 9 / 2) * mx + (ℓ + 1) + 2 ≤ 17 * ℓ := by nlinarith
  calc _ ≤ _ := htri
    _ ≤ (9 - log x - log Y) / 2 + (ℓ + 1) / mx + 4 + 9 / 2 + 2 / mx := by
        linarith [e3a.2, e3b.2]
    _ = _ := hsum
    _ ≤ 17 * ℓ / mx := by gcongr

/-- `(1 - log x - log Y)/max(x, Y) ≤ 9 Y^(-3/4) x^(-3/4)` on `(0,1)²`. -/
theorem div_max_le_rpow {Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    (1 - log x - log Y) / max x Y ≤ 9 * (Y ^ (-(3 / 4) : ℝ) * x ^ (-(3 / 4) : ℝ)) := by
  have hY0 := hY.1; have hx0 := hx.1
  have hlx : -log x ≤ 4 * x ^ (-(1 / 4) : ℝ) := by
    have := Real.neg_rpow_div_le_log hx0.le (by norm_num : (0 : ℝ) < 1 / 4)
    have e : -x ^ (-(1 / 4) : ℝ) / (1 / 4) = -(4 * x ^ (-(1 / 4) : ℝ)) := by ring
    linarith
  have hlY : -log Y ≤ 4 * Y ^ (-(1 / 4) : ℝ) := by
    have := Real.neg_rpow_div_le_log hY0.le (by norm_num : (0 : ℝ) < 1 / 4)
    have e : -Y ^ (-(1 / 4) : ℝ) / (1 / 4) = -(4 * Y ^ (-(1 / 4) : ℝ)) := by ring
    linarith
  have hax : 1 ≤ x ^ (-(1 / 4) : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx0 hx.2.le (by norm_num)
  have haY : 1 ≤ Y ^ (-(1 / 4) : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hY0 hY.2.le (by norm_num)
  have hℓ : 1 - log x - log Y ≤ 9 * (Y ^ (-(1 / 4) : ℝ) * x ^ (-(1 / 4) : ℝ)) := by nlinarith
  have hmax : 1 / max x Y ≤ Y ^ (-(1 / 2) : ℝ) * x ^ (-(1 / 2) : ℝ) := by
    rcases le_total x Y with h | h
    · rw [max_eq_right h]
      have e : 1 / Y = Y ^ (-(1 / 2) : ℝ) * Y ^ (-(1 / 2) : ℝ) := by
        rw [← Real.rpow_add hY0]; norm_num [Real.rpow_neg_one]
      rw [e]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx0 h (by norm_num))
        (Real.rpow_nonneg hY0.le _)
    · rw [max_eq_left h]
      have e : 1 / x = Y ^ (-(1 / 2) : ℝ) * x ^ (-(1 / 2) : ℝ) * (x ^ (-(1 / 2) : ℝ) /
          Y ^ (-(1 / 2) : ℝ)) := by
        have : 0 < Y ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hY0 _
        rw [mul_comm (Y ^ _), mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ this.ne',
          ← Real.rpow_add hx0]
        norm_num [Real.rpow_neg_one]
      rw [e]
      have : x ^ (-(1 / 2) : ℝ) / Y ^ (-(1 / 2) : ℝ) ≤ 1 := by
        rw [div_le_one (Real.rpow_pos_of_pos hY0 _)]
        exact Real.rpow_le_rpow_of_nonpos hY0 h (by norm_num)
      have hp : 0 ≤ Y ^ (-(1 / 2) : ℝ) * x ^ (-(1 / 2) : ℝ) := by positivity
      exact mul_le_of_le_one_right hp this
  have hℓ0 : 0 ≤ 1 - log x - log Y := by
    have := Real.log_nonpos hx0.le hx.2.le
    have := Real.log_nonpos hY0.le hY.2.le
    linarith
  calc (1 - log x - log Y) / max x Y = (1 - log x - log Y) * (1 / max x Y) := by ring
    _ ≤ 9 * (Y ^ (-(1 / 4) : ℝ) * x ^ (-(1 / 4) : ℝ)) *
        (Y ^ (-(1 / 2) : ℝ) * x ^ (-(1 / 2) : ℝ)) := by
        apply mul_le_mul hℓ hmax (by positivity) (by positivity)
    _ = 9 * (Y ^ (-(3 / 4) : ℝ) * x ^ (-(3 / 4) : ℝ)) := by
        have e1 : Y ^ (-(1 / 4) : ℝ) * Y ^ (-(1 / 2) : ℝ) = Y ^ (-(3 / 4) : ℝ) := by
          rw [← Real.rpow_add hY0]; norm_num
        have e2 : x ^ (-(1 / 4) : ℝ) * x ^ (-(1 / 2) : ℝ) = x ^ (-(3 / 4) : ℝ) := by
          rw [← Real.rpow_add hx0]; norm_num
        rw [← e1, ← e2]; ring

/-- **The product bound**: for `|λ| ≤ 1` and `0 < Y, x < 1`,
`|R(λ; Y, x)| ≤ 153 Y^(-3/4) x^(-3/4)`. -/
theorem abs_ladderR_le_rpow {lam Y x : ℝ} (hlam : |lam| ≤ 1) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    |ladderR lam Y x| ≤ 153 * (Y ^ (-(3 / 4) : ℝ) * x ^ (-(3 / 4) : ℝ)) := by
  have h := abs_ladderR_le hlam hY hx
  have h2 := div_max_le_rpow hY hx
  calc |ladderR lam Y x| ≤ 17 * (1 - log x - log Y) / max x Y := h
    _ = 17 * ((1 - log x - log Y) / max x Y) := by ring
    _ ≤ 17 * (9 * (Y ^ (-(3 / 4) : ℝ) * x ^ (-(3 / 4) : ℝ))) := by gcongr
    _ = _ := by ring

end QED.TwoLoop.UnitLLink

end
