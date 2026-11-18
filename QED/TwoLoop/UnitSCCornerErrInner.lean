/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCornerErrCoeff
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The corner error terms: the inner photon at mass `Λ`

Section 2.3 of `docs/TWO-LOOP-UNITS.md` for the corner graph. The `x`-integrand with the inner
photon at mass `Λ`, `G(λ, Λ) = cornerGm λ Λ`, carries the inner subdivergence `-ℓ_C log M_Λ`,
`ℓ_C = c₀/h`, `M_Λ = Y² + (1-Y) Λ²`; the large-`M` constant of the corner is `0`. With the
logarithm put back (`cornerE`, `e = G(λ, Λ) + ℓ_C log M_Λ`) this file proves, for `0 < λ ≤ 1 ≤ Λ`,
`(y₃, y₄)` in the open triangle and `0 < x < 1` (`abs_cornerE_le`):

`|e(λ, Λ)| ≤ (10 + 2 log(1 + Λ²/g)) / N_Λ(Y)`, `N_Λ(Y) = 3Y²/4 + (1-Y) Λ²` (`cornerN`).

The bound is uniform in `λ` and in `x`; it is `O(log Λ/(Λ² (1-Y)))` but only `O(1)` near `Y = 1`.
The steps:

* `abs_cForm_add_le`: the closed form `cForm` of the `b`-integral without its logarithm
  `-c₀ log(M + β h)/h` is bounded by the six masters, each bounded through `L ≤ u` and
  `|L - u| ≤ u²` (`u = M/(β h)`, `L = log(1 + u)`);
* `log_massΛ_sub_le`: `0 ≤ log(M + β h) - log M_Λ ≤ β h/M_Λ`, since `β h ≥ λ² e`
  (`β ≥ e x/(1-x)`), so `|ℓ_C (log M_Λ - log(M + β h))| ≤ c₀ β/M_Λ ≤ 1/(8 M_Λ)`.
-/

@[expose] public section

open Real Set

namespace QED.TwoLoop.UnitSCCorner

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-! ### The closed form without its logarithm -/

theorem log_one_add_bounds {u : ℝ} (hu : 0 < u) :
    0 ≤ log (1 + u) ∧ log (1 + u) ≤ u ∧ |log (1 + u) - u| ≤ u ^ 2 := by
  refine ⟨log_nonneg (by linarith), ?_, ?_⟩
  · have := log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + u); linarith
  · have h := abs_sPhi2_add_one_le hu
    have e : sPhi2 u + 1 = (log (1 + u) - u) / u ^ 2 := by unfold sPhi2; ring
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < u ^ 2), div_le_iff₀ (by positivity)] at h
    have : 1 / (1 + u) * u ^ 2 ≤ u ^ 2 := by
      have : 1 / (1 + u) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      nlinarith [sq_nonneg u]
    linarith

theorem abs_mul_le_mul_of_abs_le {k t B : ℝ} (ht : |t| ≤ B) : |k * t| ≤ |k| * B := by
  rw [abs_mul]; exact mul_le_mul_of_nonneg_left ht (abs_nonneg k)

theorem abs_add_six_le (a b c d e f : ℝ) :
    |a + b + c + d + e + f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  have h1 := abs_add_le (a + b + c + d + e) f
  have h2 := abs_add_le (a + b + c + d) e
  have h3 := abs_add_le (a + b + c) d
  have h4 := abs_add_le (a + b) c
  have h5 := abs_add_le a b
  linarith

/-- **The closed form without its logarithm**, bounded by the six masters. -/
theorem abs_cForm_add_le {a₀ a₁ a₂ c₀ c₁ c₂ c₃ β h M A : ℝ} (hβ : 0 < β) (hh : 0 < h)
    (hM : 0 < M) :
    |cForm a₀ a₁ a₂ c₀ c₁ c₂ c₃ β h M A (log (1 + M / (β * h))) + c₀ * A / h| ≤
      |a₀| * (1 / (h * M)) + |a₁| * ((log (1 + M / (β * h)) + 1) / M ^ 2) +
        |a₂| * (4 / (M ^ 2 * β)) + |c₁| * (log (1 + M / (β * h)) / M) +
        |c₂| * (2 / (M * β)) + |c₃| * (3 / (2 * M * β ^ 2)) := by
  have hu : 0 < M / (β * h) := by positivity
  obtain ⟨hL0, hLu, hLu2⟩ := log_one_add_bounds hu
  generalize hLdef : log (1 + M / (β * h)) = L at hL0 hLu hLu2 ⊢
  have hhL : h * L ≤ M / β := by
    calc h * L ≤ h * (M / (β * h)) := mul_le_mul_of_nonneg_left hLu hh.le
      _ = M / β := by field_simp
  have e : cForm a₀ a₁ a₂ c₀ c₁ c₂ c₃ β h M A L + c₀ * A / h =
      a₀ * (1 / (h * (M + β * h))) + a₁ * (L / M ^ 2 - 1 / (M * (M + β * h))) +
      a₂ * (1 / (M ^ 2 * β) - 2 * (h * L) / M ^ 3 + h / (M ^ 2 * (M + β * h))) + c₁ * (L / M) +
      c₂ * (1 / (M * β) - (h * L) / M ^ 2) +
      c₃ * (1 / (2 * M * β ^ 2) + h ^ 2 / M ^ 3 * (L - M / (β * h))) := by
    unfold cForm
    field_simp
    ring
  rw [e]
  have hMβh : 0 < M + β * h := by positivity
  -- the masters
  have t4 : |1 / (h * (M + β * h))| ≤ 1 / (h * M) := by
    rw [abs_of_pos (by positivity)]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have t5 : |L / M ^ 2 - 1 / (M * (M + β * h))| ≤ (L + 1) / M ^ 2 := by
    have h1 : 1 / (M * (M + β * h)) ≤ 1 / M ^ 2 :=
      one_div_le_one_div_of_le (by positivity)
        (by rw [sq]; exact mul_le_mul_of_nonneg_left (by nlinarith [mul_pos hβ hh]) hM.le)
    have h2 : 0 ≤ 1 / (M * (M + β * h)) := by positivity
    have h3 : 0 ≤ L / M ^ 2 := by positivity
    have h4 : (0 : ℝ) ≤ 1 / M ^ 2 := by positivity
    have : (L + 1) / M ^ 2 = L / M ^ 2 + 1 / M ^ 2 := by ring
    rw [abs_le]; constructor <;> linarith
  have hk1 : h * L / M ^ 2 ≤ 1 / (M * β) := by
    calc h * L / M ^ 2 ≤ M / β / M ^ 2 := div_le_div_of_nonneg_right hhL (by positivity)
      _ = 1 / (M * β) := by field_simp
  have hk1' : 0 ≤ h * L / M ^ 2 := by positivity
  have t3 : |1 / (M * β) - (h * L) / M ^ 2| ≤ 2 / (M * β) := by
    have : (0 : ℝ) ≤ 1 / (M * β) := by positivity
    have : 2 / (M * β) = 2 * (1 / (M * β)) := by ring
    rw [abs_le]; constructor <;> linarith
  have t6 : |1 / (M ^ 2 * β) - 2 * (h * L) / M ^ 3 + h / (M ^ 2 * (M + β * h))| ≤
      4 / (M ^ 2 * β) := by
    have h1 : 2 * (h * L) / M ^ 3 ≤ 2 / (M ^ 2 * β) := by
      calc 2 * (h * L) / M ^ 3 ≤ 2 * (M / β) / M ^ 3 :=
            div_le_div_of_nonneg_right (by linarith) (by positivity)
        _ = 2 / (M ^ 2 * β) := by field_simp
    have h2 : h / (M ^ 2 * (M + β * h)) ≤ 1 / (M ^ 2 * β) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ M ^ 2 * h * M := by positivity
      nlinarith
    have h3 : 0 ≤ 2 * (h * L) / M ^ 3 := by positivity
    have h4 : 0 ≤ h / (M ^ 2 * (M + β * h)) := by positivity
    have h5 : (0 : ℝ) ≤ 1 / (M ^ 2 * β) := by positivity
    have : 4 / (M ^ 2 * β) = 4 * (1 / (M ^ 2 * β)) := by ring
    have : 2 / (M ^ 2 * β) = 2 * (1 / (M ^ 2 * β)) := by ring
    rw [abs_le]; constructor <;> linarith
  have t2 : |L / M| ≤ L / M := by rw [abs_of_nonneg (by positivity)]
  have t7 : |1 / (2 * M * β ^ 2) + h ^ 2 / M ^ 3 * (L - M / (β * h))| ≤ 3 / (2 * M * β ^ 2) := by
    have h1 : |h ^ 2 / M ^ 3 * (L - M / (β * h))| ≤ 1 / (M * β ^ 2) := by
      calc |h ^ 2 / M ^ 3 * (L - M / (β * h))| ≤ h ^ 2 / M ^ 3 * (M / (β * h)) ^ 2 := by
            rw [abs_mul, abs_of_pos (by positivity)]
            exact mul_le_mul_of_nonneg_left hLu2 (by positivity)
        _ = 1 / (M * β ^ 2) := by field_simp
    calc _ ≤ |1 / (2 * M * β ^ 2)| + |h ^ 2 / M ^ 3 * (L - M / (β * h))| := abs_add_le _ _
      _ ≤ 1 / (2 * M * β ^ 2) + 1 / (M * β ^ 2) := by
          rw [abs_of_pos (by positivity)]; linarith
      _ = 3 / (2 * M * β ^ 2) := by field_simp; ring
  refine (abs_add_six_le _ _ _ _ _ _).trans ?_
  have := abs_mul_le_mul_of_abs_le (k := a₀) t4
  have := abs_mul_le_mul_of_abs_le (k := a₁) t5
  have := abs_mul_le_mul_of_abs_le (k := a₂) t6
  have := abs_mul_le_mul_of_abs_le (k := c₁) t2
  have := abs_mul_le_mul_of_abs_le (k := c₂) t3
  have := abs_mul_le_mul_of_abs_le (k := c₃) t7
  linarith

/-! ### The masses -/

/-- `N_Λ(Y) = 3Y²/4 + (1-Y) Λ²`, a lower bound for both mass functions of the inner term. -/
noncomputable def cornerN (Lam Y : ℝ) : ℝ := 3 / 4 * Y ^ 2 + (1 - Y) * Lam ^ 2

theorem two_thirds_le_cornerN {Lam Y : ℝ} (hLam : 1 ≤ Lam) (hY1 : Y ≤ 1) :
    2 / 3 ≤ cornerN Lam Y := by
  unfold cornerN
  have : 1 - Y ≤ (1 - Y) * Lam ^ 2 := by
    have : 1 ≤ Lam ^ 2 := by nlinarith
    nlinarith
  nlinarith [sq_nonneg (Y - 2 / 3)]

theorem cornerN_pos {Lam Y : ℝ} (hLam : 1 ≤ Lam) (hY1 : Y ≤ 1) : 0 < cornerN Lam Y :=
  lt_of_lt_of_le (by norm_num) (two_thirds_le_cornerN hLam hY1)

/-- **The `x`-integrand of the inner term, with its logarithm put back**:
`e = G(λ, Λ) + ℓ_C log M_Λ`, `ℓ_C = c₀/h`. -/
noncomputable def cornerE (lam Lam y3 y4 x : ℝ) : ℝ :=
  cornerGm lam Lam y3 y4 x +
    cornerC0 x / (ladderInnerMass 1 lam x / x) * log (ladderInnerMass 1 Lam (y3 + y4))

section Bounds

variable {lam Lam x y3 y4 : ℝ}

theorem cornerN_le_cornerMass (hl : lam ^ 2 ≤ 1) (h3 : 0 < y3) (h4 : 0 < y4) :
    cornerN Lam (y3 + y4) ≤ cornerMass lam Lam y3 y4 := by
  unfold cornerN cornerMass
  have : lam ^ 2 * (y3 * y4) ≤ y3 * y4 := by
    have := mul_pos h3 h4; nlinarith
  nlinarith [sq_nonneg (y3 - y4)]

theorem cornerN_le_massΛ :
    cornerN Lam (y3 + y4) ≤ ladderInnerMass 1 Lam (y3 + y4) := by
  unfold cornerN ladderInnerMass
  nlinarith [sq_nonneg (y3 + y4)]

theorem cornerMass_le_sq (hLam : 1 ≤ Lam) (h3 : 0 < y3) (h4 : 0 < y4) (hY : y3 + y4 < 1) :
    cornerMass lam Lam y3 y4 ≤ Lam ^ 2 := by
  unfold cornerMass
  have hL : 1 ≤ Lam ^ 2 := by nlinarith
  have : 0 ≤ lam ^ 2 * (y3 * y4) := by have := mul_pos h3 h4; positivity
  nlinarith

theorem cornerG_le_cornerN (hLam : 1 ≤ Lam) (h3 : 0 < y3) (h4 : 0 < y4) (hY : y3 + y4 < 1) :
    cornerG y3 y4 ≤ cornerN Lam (y3 + y4) := by
  have hg := cornerG_le_one_sub hY h4
  unfold cornerN
  have hL : 1 ≤ Lam ^ 2 := by nlinarith
  nlinarith [sq_nonneg (y3 + y4)]

theorem betaG_mul_one_sub_ge {g e x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    e * x ≤ betaG g e x * (1 - x) := by
  have h1 : 0 < 1 - x := by linarith [hx.2]
  have := le_max_right g (e * x / (1 - x))
  rw [← div_le_iff₀ h1]
  exact this

theorem cornerC0_mul_betaG_le (hx : x ∈ Ioo (0 : ℝ) 1) (h3 : 0 < y3) (h4 : 0 < y4)
    (hY : y3 + y4 < 1) : cornerC0 x * betaG (cornerG y3 y4) (y3 * y4) x ≤ 1 / 8 := by
  obtain ⟨hx0, hx1⟩ := hx
  have hg := cornerG_pos h3 hY
  have hg4 := cornerG_le_quarter h3 h4
  have he4 : y3 * y4 ≤ 1 / 4 := by nlinarith [sq_nonneg (y3 - y4)]
  unfold cornerC0 betaG
  rcases le_total (cornerG y3 y4) (y3 * y4 * x / (1 - x)) with h | h
  · rw [max_eq_right h]
    have e : x * (1 - x) / 2 * (y3 * y4 * x / (1 - x)) = x ^ 2 * (y3 * y4) / 2 := by
      have : 1 - x ≠ 0 := by linarith
      field_simp
    rw [e]
    have : x ^ 2 ≤ 1 := by nlinarith
    have := mul_pos h3 h4
    nlinarith
  · rw [max_eq_left h]
    have : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
    have : 0 ≤ x * (1 - x) := by nlinarith
    nlinarith

/-- `β h ≥ λ² e`: the shift of the mass function by the outer photon is dominated by `β h`. -/
theorem lam_sq_mul_le_betaG_mul_h (hx : x ∈ Ioo (0 : ℝ) 1) (h3 : 0 < y3) (hY : y3 + y4 < 1) :
    lam ^ 2 * (y3 * y4) ≤
      betaG (cornerG y3 y4) (y3 * y4) x * (ladderInnerMass 1 lam x / x) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hb := betaG_mul_one_sub_ge (g := cornerG y3 y4) (e := y3 * y4) ⟨hx0, hx1⟩
  have hβ := betaG_pos (e := y3 * y4) (x := x) (cornerG_pos h3 hY)
  rw [mul_div_assoc', le_div_iff₀ hx0]
  unfold ladderInnerMass
  have : 0 ≤ betaG (cornerG y3 y4) (y3 * y4) x * x ^ 2 := by positivity
  have : lam ^ 2 * (y3 * y4 * x) ≤ lam ^ 2 * (betaG (cornerG y3 y4) (y3 * y4) x * (1 - x)) :=
    mul_le_mul_of_nonneg_left hb (sq_nonneg _)
  nlinarith

/-- **The logarithm of the inner subdivergence**:
`|ℓ_C (log M_Λ - log(M + β h))| ≤ 1/(8 M_Λ)`. -/
theorem abs_cornerEll_log_sub_le (hx : x ∈ Ioo (0 : ℝ) 1) (h3 : 0 < y3)
    (h4 : 0 < y4) (hY : y3 + y4 < 1) :
    |cornerC0 x / (ladderInnerMass 1 lam x / x) * (log (ladderInnerMass 1 Lam (y3 + y4)) -
        log (cornerMass lam Lam y3 y4 +
          betaG (cornerG y3 y4) (y3 * y4) x * (ladderInnerMass 1 lam x / x)))| ≤
      1 / 8 / ladderInnerMass 1 Lam (y3 + y4) := by
  set h := ladderInnerMass 1 lam x / x with hh
  set β := betaG (cornerG y3 y4) (y3 * y4) x with hβdef
  set MΛ := ladderInnerMass 1 Lam (y3 + y4) with hMΛ
  have hhpos : 0 < h := selfH_pos hx
  have hβ : 0 < β := betaG_pos (cornerG_pos h3 hY)
  have hMΛpos : 0 < MΛ := lt_of_lt_of_le (by positivity) (selfM_ge (μ := Lam)
    (Y := y3 + y4) ⟨by positivity, hY⟩)
  have hc0 := cornerC0_nonneg hx
  have hkey := lam_sq_mul_le_betaG_mul_h (lam := lam) hx h3 hY
  have hsum : cornerMass lam Lam y3 y4 + β * h = MΛ + (β * h - lam ^ 2 * (y3 * y4)) := by
    rw [hMΛ]; unfold cornerMass ladderInnerMass; ring
  have hd0 : 0 ≤ β * h - lam ^ 2 * (y3 * y4) := by linarith
  have hlog0 : log MΛ ≤ log (cornerMass lam Lam y3 y4 + β * h) := by
    rw [hsum]; exact log_le_log hMΛpos (by linarith)
  have hlog1 : log (cornerMass lam Lam y3 y4 + β * h) - log MΛ ≤ β * h / MΛ := by
    rw [hsum, ← log_div (by linarith) hMΛpos.ne']
    have := log_le_sub_one_of_pos (show 0 < (MΛ + (β * h - lam ^ 2 * (y3 * y4))) / MΛ by
      positivity)
    have e : (MΛ + (β * h - lam ^ 2 * (y3 * y4))) / MΛ - 1 =
        (β * h - lam ^ 2 * (y3 * y4)) / MΛ := by field_simp; ring
    have : (β * h - lam ^ 2 * (y3 * y4)) / MΛ ≤ β * h / MΛ :=
      div_le_div_of_nonneg_right (by nlinarith [mul_pos h3 h4, sq_nonneg lam]) hMΛpos.le
    linarith
  rw [abs_mul, abs_of_nonneg (by positivity), abs_sub_comm,
    abs_of_nonneg (by linarith)]
  calc cornerC0 x / h * (log (cornerMass lam Lam y3 y4 + β * h) - log MΛ)
      ≤ cornerC0 x / h * (β * h / MΛ) := mul_le_mul_of_nonneg_left hlog1 (by positivity)
    _ = cornerC0 x * β / MΛ := by field_simp
    _ ≤ 1 / 8 / MΛ := div_le_div_of_nonneg_right
        (cornerC0_mul_betaG_le hx h3 h4 hY) hMΛpos.le

/-- **The bound on the inner term**: for `0 < λ ≤ 1 ≤ Λ`, `(y₃, y₄)` in the open triangle and
`0 < x < 1`, `|e(λ, Λ)| ≤ (10 + 2 log(1 + Λ²/g)) / N_Λ(Y)`. -/
theorem abs_cornerE_le (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hLam : 1 ≤ Lam)
    (hx : x ∈ Ioo (0 : ℝ) 1) (h3 : 0 < y3) (h4 : 0 < y4) (hY : y3 + y4 < 1) :
    |cornerE lam Lam y3 y4 x| ≤
      (10 + 2 * log (1 + Lam ^ 2 / cornerG y3 y4)) / cornerN Lam (y3 + y4) := by
  set h := ladderInnerMass 1 lam x / x with hh
  set β := betaG (cornerG y3 y4) (y3 * y4) x with hβdef
  set M := cornerMass lam Lam y3 y4 with hMdef
  set g := cornerG y3 y4 with hgdef
  set N := cornerN Lam (y3 + y4) with hNdef
  have hhx : x ≤ h := selfH_ge hx
  have hhpos : 0 < h := selfH_pos hx
  have hg : 0 < g := cornerG_pos h3 hY
  have hβ : 0 < β := betaG_pos hg
  have hgβ : g ≤ β := le_betaG _ _ _
  have hN : 0 < N := cornerN_pos hLam (by linarith)
  have hNM : N ≤ M := cornerN_le_cornerMass (by nlinarith) h3 h4
  have hM : 0 < M := hN.trans_le hNM
  have hgM : g ≤ M := (cornerG_le_cornerN hLam h3 h4 hY).trans hNM
  have hMΛ : N ≤ ladderInnerMass 1 Lam (y3 + y4) := cornerN_le_massΛ
  obtain ⟨hx0, hx1⟩ := hx
  -- the split
  have e : cornerE lam Lam y3 y4 x =
      (cForm (cornerA0 x y3 y4) (cornerA1 x y3 y4) (cornerA2 x y3 y4) (cornerC0 x)
          (cornerC1 x y3 y4) (cornerC2 x y3 y4) (cornerC3 x y3 y4) β h M (log (M + β * h))
          (log (1 + M / (β * h))) + cornerC0 x * log (M + β * h) / h) +
        cornerC0 x / h * (log (ladderInnerMass 1 Lam (y3 + y4)) - log (M + β * h)) := by
    unfold cornerE cornerGm
    ring
  rw [e]
  have hA := abs_cForm_add_le (a₀ := cornerA0 x y3 y4) (a₁ := cornerA1 x y3 y4)
    (a₂ := cornerA2 x y3 y4) (c₀ := cornerC0 x) (c₁ := cornerC1 x y3 y4) (c₂ := cornerC2 x y3 y4)
    (c₃ := cornerC3 x y3 y4) (A := log (M + β * h)) hβ hhpos hM
  have hB := abs_cornerEll_log_sub_le (Lam := Lam) (lam := lam) ⟨hx0, hx1⟩ h3 h4 hY
  have ha0 := abs_cornerA0_le ⟨hx0, hx1⟩ h3 h4 hY
  have ha1 := abs_cornerA1_le ⟨hx0, hx1⟩ h3 h4 hY
  have ha2 := abs_cornerA2_le ⟨hx0, hx1⟩ h3 h4 hY
  have hc1 := abs_cornerC1_le ⟨hx0, hx1⟩ h3 h4 hY
  have hc2 := abs_cornerC2_le ⟨hx0, hx1⟩ h3 h4 hY
  have hc3 := abs_cornerC3_le ⟨hx0, hx1⟩ h3 h4 hY
  rw [← hgdef] at ha1 ha2 hc2 hc3
  generalize hLdef : log (1 + M / (β * h)) = L at hA
  have hL0 : 0 ≤ L := by
    rw [← hLdef]
    have : 0 ≤ M / (β * h) := by positivity
    exact log_nonneg (by linarith)
  -- the six terms
  have b1 : |cornerA0 x y3 y4| * (1 / (h * M)) ≤ 1 / 2 / M := by
    calc _ ≤ (x / 2) * (1 / (x * M)) :=
          mul_le_mul ha0 (one_div_le_one_div_of_le (by positivity)
            (mul_le_mul_of_nonneg_right hhx hM.le)) (by positivity) (by positivity)
      _ = 1 / 2 / M := by field_simp
  have b2 : |cornerA1 x y3 y4| * ((L + 1) / M ^ 2) ≤ 3 / 4 * x * (L + 1) / M := by
    calc _ ≤ (3 / 4 * x * g) * ((L + 1) / M ^ 2) := mul_le_mul_of_nonneg_right ha1 (by positivity)
      _ = 3 / 4 * x * (L + 1) / M * (g / M) := by field_simp
      _ ≤ 3 / 4 * x * (L + 1) / M * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one hM).2 hgM) (by positivity)
      _ = _ := mul_one _
  have b3 : |cornerA2 x y3 y4| * (4 / (M ^ 2 * β)) ≤ x / M := by
    calc _ ≤ (x * g ^ 2 / 4) * (4 / (M ^ 2 * β)) := mul_le_mul_of_nonneg_right ha2 (by positivity)
      _ = x / M * ((g / M) * (g / β)) := by field_simp
      _ ≤ x / M * (1 * 1) := mul_le_mul_of_nonneg_left (mul_le_mul ((div_le_one hM).2 hgM)
          ((div_le_one hβ).2 hgβ) (by positivity) zero_le_one) (by positivity)
      _ = _ := by ring
  have b4 : |cornerC1 x y3 y4| * (L / M) ≤ 9 / 8 * x * L / M := by
    calc _ ≤ (9 / 8 * x) * (L / M) := mul_le_mul_of_nonneg_right hc1 (by positivity)
      _ = _ := by ring
  have b5 : |cornerC2 x y3 y4| * (2 / (M * β)) ≤ 7 / 2 * x / M := by
    calc _ ≤ (7 / 4 * x * g) * (2 / (M * β)) := mul_le_mul_of_nonneg_right hc2 (by positivity)
      _ = 7 / 2 * x / M * (g / β) := by field_simp; ring
      _ ≤ 7 / 2 * x / M * 1 := mul_le_mul_of_nonneg_left ((div_le_one hβ).2 hgβ) (by positivity)
      _ = _ := mul_one _
  have b6 : |cornerC3 x y3 y4| * (3 / (2 * M * β ^ 2)) ≤ 9 / 8 * x / M := by
    calc _ ≤ (3 / 4 * x * g ^ 2) * (3 / (2 * M * β ^ 2)) :=
          mul_le_mul_of_nonneg_right hc3 (by positivity)
      _ = 9 / 8 * x / M * ((g / β) * (g / β)) := by field_simp; ring
      _ ≤ 9 / 8 * x / M * (1 * 1) := mul_le_mul_of_nonneg_left (mul_le_mul
          ((div_le_one hβ).2 hgβ) ((div_le_one hβ).2 hgβ) (by positivity) zero_le_one)
          (by positivity)
      _ = _ := by ring
  -- `x L ≤ 1 + log(1 + Λ²/g)`
  have hxL : x * L ≤ 1 + log (1 + Lam ^ 2 / g) := by
    have hu : M / (β * h) ≤ Lam ^ 2 / g / x := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : M ≤ Lam ^ 2 := cornerMass_le_sq hLam h3 h4 hY
      have h2 : g * x ≤ β * h := mul_le_mul hgβ hhx hx0.le hβ.le
      exact mul_le_mul h1 h2 (by positivity) (sq_nonneg _)
    have hL : L ≤ log (1 + Lam ^ 2 / g / x) := by
      rw [← hLdef]
      exact log_le_log (by positivity) (by linarith)
    calc x * L ≤ x * log (1 + Lam ^ 2 / g / x) := mul_le_mul_of_nonneg_left hL hx0.le
      _ ≤ 1 + log (1 + Lam ^ 2 / g) := mul_log_one_add_div_le hx0 hx1.le (by positivity)
  -- assembly
  have hsum : |cForm (cornerA0 x y3 y4) (cornerA1 x y3 y4) (cornerA2 x y3 y4) (cornerC0 x)
      (cornerC1 x y3 y4) (cornerC2 x y3 y4) (cornerC3 x y3 y4) β h M (log (M + β * h)) L +
      cornerC0 x * log (M + β * h) / h| ≤ (7 + 2 * (x * L)) / M := by
    refine hA.trans ?_
    have hle : 1 / 2 + 3 / 4 * x + x + 7 / 2 * x + 9 / 8 * x + 15 / 8 * (x * L) ≤
        7 + 2 * (x * L) := by linarith [mul_nonneg hx0.le hL0]
    calc _ ≤ 1 / 2 / M + 3 / 4 * x * (L + 1) / M + x / M + 9 / 8 * x * L / M + 7 / 2 * x / M +
          9 / 8 * x / M :=
          add_le_add (add_le_add (add_le_add (add_le_add (add_le_add b1 b2) b3) b4) b5) b6
      _ = (1 / 2 + 3 / 4 * x + x + 7 / 2 * x + 9 / 8 * x + 15 / 8 * (x * L)) / M := by ring
      _ ≤ (7 + 2 * (x * L)) / M := div_le_div_of_nonneg_right hle hM.le
  have hlogpos : 0 ≤ log (1 + Lam ^ 2 / g) := by
    have : 0 ≤ Lam ^ 2 / g := by positivity
    exact log_nonneg (by linarith)
  have hxL0 : 0 ≤ x * L := mul_nonneg hx0.le hL0
  calc _ ≤ |cForm (cornerA0 x y3 y4) (cornerA1 x y3 y4) (cornerA2 x y3 y4) (cornerC0 x)
        (cornerC1 x y3 y4) (cornerC2 x y3 y4) (cornerC3 x y3 y4) β h M (log (M + β * h)) L +
        cornerC0 x * log (M + β * h) / h| +
        |cornerC0 x / h * (log (ladderInnerMass 1 Lam (y3 + y4)) - log (M + β * h))| := by
          rw [← hLdef]; exact abs_add_le _ _
    _ ≤ (7 + 2 * (x * L)) / M + 1 / 8 / ladderInnerMass 1 Lam (y3 + y4) := add_le_add hsum hB
    _ ≤ (7 + 2 * (x * L)) / N + 1 / 8 / N := add_le_add
        (div_le_div_of_nonneg_left (by positivity) hN hNM)
        (div_le_div_of_nonneg_left (by positivity) hN hMΛ)
    _ ≤ (10 + 2 * log (1 + Lam ^ 2 / g)) / N := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right (by linarith) hN.le

end Bounds

end QED.TwoLoop.UnitSCCorner

end
