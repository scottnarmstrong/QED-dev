/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXCloseBoundData
public import QED.TwoLoop.UnitXCloseLimit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

/-!
# The domination of the crossed-ladder integrand, uniform in the regulators

The hypothesis `CrossedDom` of `QED/TwoLoop/UnitXCloseLimit.lean`, proved:

* `crossedDom`: for `z` in the open 4-simplex of the group sums and all `μ_a, μ_b ≥ 0`,
  `|T(μ_a, μ_b)(z)| ≤ C ∏ₖ zₖ^{-s}` with `s = domS / domN < 1`.

Proof. `V = E + μ_a z_a + μ_b z_b ≥ E = Ẽ/U > 0`, so
`|T| ≤ |M Ψ₁|/(2 U⁴ Ẽ²) + |M Ψ₂|/(2 U⁴ Ẽ)`. The polynomials `M Ψ₁(M/2)` and `M Ψ₂(M/2)` are the
term lists `domTerms₁`, `domTerms₂` (`mul_gPsi1_eq`, `mul_gPsi2_eq`); every term passes the
certificate check (`domTerms₁_ok`, `domTerms₂_ok`), and `listBound` bounds each quotient by
`5 (∑ |c|) ∏ₖ zₖ^{-s}`.

* `xUnitLimitOne_of_iterated`, `xUnitLimit_of_iterated`: **the X link (at `m = 1`, and at every
  mass) reduces to the value of the massless iterated integral**
  `∫_{triangle} ∫₀^∞ ∫₀^∞ T(0, 0) = 1/6 - 5 ζ(2) log 2 + (13/6) ζ(2) + (5/4) ζ(3)`.
-/

@[expose] public section

open MeasureTheory Set

namespace QED.TwoLoop.UnitXClose

open QED.TwoLoop.UnitXGraph

theorem gz_eq (z : Fin 5 → ℝ) : gz (z 0) (z 1) (z 2) (z 3) (z 4) = z := by
  funext k; fin_cases k <;> rfl

/-- `|T(μ_a, μ_b)| ≤ |M Ψ₁|/(2 U⁴ Ẽ²) + |M Ψ₂|/(2 U⁴ Ẽ)`. -/
theorem abs_crossedTerm_le {μa μb A M c a b : ℝ} (hμa : 0 ≤ μa) (hμb : 0 ≤ μb) (hA : 0 < A)
    (hM : 0 < M) (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) :
    |crossedTerm μa μb A M c a b| ≤
      |M * gPsi1 A (M / 2) M c a b| / (gXU A M c a b ^ 4 * gXEn A M c a b ^ 2) / 2 +
        |M * gPsi2 A (M / 2) M c a b| / (gXU A M c a b ^ 4 * gXEn A M c a b ^ 1) / 2 := by
  have hU := gXU_pos hA hM hc ha hb
  have hE := gXE_pos hA hM hc ha hb
  have hEn : 0 < gXEn A M c a b := by unfold gXEn; positivity
  have hEe : gXE A M c a b = gXEn A M c a b / gXU A M c a b := rfl
  set V := gXE A M c a b + μa * a + μb * b
  have hV : gXE A M c a b ≤ V := by
    have := mul_nonneg hμa ha.le; have := mul_nonneg hμb hb.le; simp only [V]; linarith
  have hV0 : 0 < V := hE.trans_le hV
  have e : crossedTerm μa μb A M c a b =
      M * gPsi1 A (M / 2) M c a b / (2 * gXU A M c a b ^ 6 * V ^ 2) -
        M * gPsi2 A (M / 2) M c a b / (2 * gXU A M c a b ^ 5 * V) := by
    unfold crossedTerm; ring
  rw [e]
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * gXU A M c a b ^ 6 * V ^ 2)]
    have h1 : gXU A M c a b ^ 4 * gXEn A M c a b ^ 2 ≤ gXU A M c a b ^ 6 * V ^ 2 := by
      have : gXEn A M c a b = gXU A M c a b * gXE A M c a b := by
        rw [hEe]; field_simp
      rw [this, mul_pow, ← mul_assoc, ← pow_add]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hE.le hV 2) (by positivity)
    rw [div_div]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by nlinarith)
  · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * gXU A M c a b ^ 5 * V)]
    have h1 : gXU A M c a b ^ 4 * gXEn A M c a b ^ 1 ≤ gXU A M c a b ^ 5 * V := by
      have : gXEn A M c a b = gXU A M c a b * gXE A M c a b := by
        rw [hEe]; field_simp
      rw [this, pow_one, ← mul_assoc, ← pow_succ]
      exact mul_le_mul_of_nonneg_left hV (by positivity)
    rw [div_div]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by nlinarith)

/-- **The domination**: `|T(μ_a, μ_b)(z)| ≤ C ∏ₖ zₖ^{-s}` on the open simplex, uniformly in
`μ_a, μ_b ≥ 0`, with `s = domS/domN`. -/
theorem crossedDom : CrossedDom := by
  refine ⟨5 * absSum domTerms₁ / 2 + 5 * absSum domTerms₂ / 2, (domS : ℝ) / domN,
    by positivity, by rw [div_lt_one (by norm_num [domN])]; norm_num [domS, domN],
    fun μa μb hμa hμb z hz hz1 => ?_⟩
  obtain ⟨A, M, c, a, b, rfl⟩ : ∃ A M c a b : ℝ, z = gz A M c a b :=
    ⟨z 0, z 1, z 2, z 3, z 4, (gz_eq z).symm⟩
  have e0 : gz A M c a b 0 = A := rfl
  have e1 : gz A M c a b 1 = M := rfl
  have e2 : gz A M c a b 2 = c := rfl
  have e3 : gz A M c a b 3 = a := rfl
  have e4 : gz A M c a b 4 = b := rfl
  rw [e0, e1, e2, e3, e4]
  have hA : 0 < A := e0 ▸ hz 0
  have hM : 0 < M := e1 ▸ hz 1
  have hc : 0 < c := e2 ▸ hz 2
  have ha : 0 < a := e3 ▸ hz 3
  have hb : 0 < b := e4 ▸ hz 4
  have hzle : ∀ k, gz A M c a b k ≤ 1 := fun k => by
    have : gz A M c a b k ≤ ∑ j, gz A M c a b j :=
      Finset.single_le_sum (fun j _ => (hz j).le) (Finset.mem_univ k)
    linarith
  have hN : 0 < domN := by norm_num [domN]
  have h1 := listBound hA hM hc ha hb hzle hz1 hN domTerms₁_ok
  have h2 := listBound hA hM hc ha hb hzle hz1 hN domTerms₂_ok
  have hz0 : ∀ k, 0 ≤ gz A M c a b k := fun k => (hz k).le
  have a1 := abs_evalTerms_le hz0 domTerms₁
  have a2 := abs_evalTerms_le hz0 domTerms₂
  rw [← mul_gPsi1_eq] at a1
  rw [← mul_gPsi2_eq] at a2
  have hU := gXU_pos hA hM hc ha hb
  have hEn : 0 < gXEn A M c a b := by unfold gXEn; positivity
  have b1 : |M * gPsi1 A (M / 2) M c a b| / (gXU A M c a b ^ 4 * gXEn A M c a b ^ 2) ≤
      evalAbs domTerms₁ (gz A M c a b) / (gXU A M c a b ^ 4 * gXEn A M c a b ^ 2) :=
    div_le_div_of_nonneg_right a1 (by positivity)
  have b2 : |M * gPsi2 A (M / 2) M c a b| / (gXU A M c a b ^ 4 * gXEn A M c a b ^ 1) ≤
      evalAbs domTerms₂ (gz A M c a b) / (gXU A M c a b ^ 4 * gXEn A M c a b ^ 1) :=
    div_le_div_of_nonneg_right a2 (by positivity)
  have hT := abs_crossedTerm_le hμa hμb hA hM hc ha hb
  have hm : mono (gz A M c a b) (fun _ => -((domS : ℝ) / domN)) =
      ∏ k, gz A M c a b k ^ (-((domS : ℝ) / domN)) := rfl
  rw [← hm]
  linarith

/-- **The X link at `m = 1` reduces to the value of the massless iterated integral.** -/
theorem xUnitLimitOne_of_iterated
    (hval : ∫ p in innerTriangle, ∫ zA in Ioi (0 : ℝ), ∫ za in Ioi (0 : ℝ),
        crossedTerm 0 0 zA p.1 p.2 za (1 - (p.1 + p.2)) = xValue) :
    QED.TwoLoop.HeadlineAssembly.XUnitLimitOne :=
  xUnitLimitOne_of_dom_iterated crossedDom hval

/-- **The X link at every mass reduces to the value of the massless iterated integral.** -/
theorem xUnitLimit_of_iterated
    (hval : ∫ p in innerTriangle, ∫ zA in Ioi (0 : ℝ), ∫ za in Ioi (0 : ℝ),
        crossedTerm 0 0 zA p.1 p.2 za (1 - (p.1 + p.2)) = xValue) :
    QED.TwoLoop.HeadlineAssembly.XUnitLimit :=
  QED.TwoLoop.HeadlineAssembly.XUnitLimit.of_one (xUnitLimitOne_of_iterated hval)

end QED.TwoLoop.UnitXClose

end
