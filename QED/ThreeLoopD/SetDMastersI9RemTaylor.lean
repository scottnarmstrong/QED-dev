/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9Analytic
public import QED.ThreeLoopD.SetDMastersLaurent
import Mathlib.Analysis.Complex.AbsMax

/-!
# Set (d), master `I₉`: the remainder `Rem` to order `ε²` as two real integrals

The integrand of `QED.ThreeLoopD.i9Rem` is, at each point of the open cube, a sum of five
exponentials in `ε`: with `c = x(1 - x)`, `D = c w y (1 - y)`,
`Λ = 2 log c + 2 log w + log y + log (1 - y)` and `P₀ = P|_{y=0}`, `P₁ = P|_{y=1}`,

  `c ^ (2ε - 1) w ^ (2ε - 1) y ^ (ε - 1) (1 - y) ^ (ε - 1) Ψ_sub = D⁻¹ Σⱼ βⱼ e ^ (ε λⱼ)`,

`λⱼ = Λ - 3 log Qⱼ`, over `(βⱼ, Qⱼ) = (P, P), (-w y, w y), (-(1 - y) P₀, P₀), (-y P₁, P₁),
(y w, w)` (the `c ^ s` terms cancel). Since `Σ βⱼ = 0`, the expansion
`e ^ t = 1 + t + t²/2 + t³ E₃(t)` (`QED.ThreeLoopD.exp_eq_i9E3`, `E₃` entire) writes the
integrand as `ε F₁ + ε² F₂ + ε³ G(ε)` with explicit real `F₁, F₂`
(`QED.ThreeLoopD.i9RemF1`, `QED.ThreeLoopD.i9RemF2`). The maximum modulus principle on the
circle `‖ε‖ = 1/25`, against the bound of `QED.ThreeLoopD.norm_i9Rem_integrand_le`, bounds
`F₁`, `F₂` and `G(ε)` on `‖ε‖ ≤ 1/25` by multiples of that same integrable function. Hence

  `Rem(ε) = ε ∫ F₁ + ε² ∫ F₂ + ε³ ∫ G(ε)`, with `ε ↦ ∫ G(ε)` analytic at `0`.

No differentiation under the integral sign is needed.

## Main results

* `QED.ThreeLoopD.i9Rem_eq_taylor`: the decomposition for `‖ε‖ < 1/25`.
* `QED.ThreeLoopD.hasTruncLaurent_i9Rem_integrals`:
  `HasTruncLaurent i9Rem (fun ε => ε ∫ F₁ + ε² ∫ F₂) 3`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric QED.DimReg Filter Topology

namespace QED.ThreeLoopD

/-! ### The entire function `E₃` -/

/-- `E₃(t) = ∫₀¹ (1 - s)²/2 e ^ (t s) ds`, so that `e ^ t = 1 + t + t²/2 + t³ E₃(t)`. -/
noncomputable def i9E3 (t : ℂ) : ℂ :=
  ∫ s in (0 : ℝ)..1, (((1 - s) ^ 2 / 2 : ℝ) : ℂ) * cexp (t * s)

theorem exp_eq_i9E3 (t : ℂ) : cexp t = 1 + t + t ^ 2 / 2 + t ^ 3 * i9E3 t := by
  have hG : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ =>
      (t ^ 2 * (((1 - s) ^ 2 / 2 : ℝ) : ℂ) + t * ((1 - s : ℝ) : ℂ) + 1) * cexp (t * s))
      (t ^ 3 * ((((1 - s) ^ 2 / 2 : ℝ) : ℂ) * cexp (t * s))) s := by
    intro s _
    have hq : HasDerivAt (fun s : ℝ => (((1 - s) ^ 2 / 2 : ℝ) : ℂ)) ((-(1 - s) : ℝ) : ℂ) s := by
      have := (((hasDerivAt_id s).const_sub 1).pow 2).div_const 2
      exact (this.congr_deriv (by simp; ring)).ofReal_comp
    have hl : HasDerivAt (fun s : ℝ => ((1 - s : ℝ) : ℂ)) ((-1 : ℝ) : ℂ) s :=
      (((hasDerivAt_id s).const_sub 1).congr_deriv (by simp)).ofReal_comp
    have hs : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) ((1 : ℝ) : ℂ) s :=
      (hasDerivAt_id s).ofReal_comp
    have he := (hs.const_mul t).cexp
    convert (((hq.const_mul (t ^ 2)).add (hl.const_mul t)).add_const 1).mul he using 1
    simp only [Pi.add_apply]
    push_cast
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hG
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [intervalIntegral.integral_const_mul] at hint
  unfold i9E3
  rw [hint]
  push_cast
  simp
  ring

theorem differentiable_i9E3 : Differentiable ℂ i9E3 := by
  intro t₁
  have e : i9E3 = fun t => ∫ s in Ioc (0 : ℝ) 1, (((1 - s) ^ 2 / 2 : ℝ) : ℂ) * cexp (t * s) := by
    funext t
    exact intervalIntegral.integral_of_le zero_le_one
  rw [e]
  refine differentiableAt_integral_of_holomorphic (z₁ := t₁) one_pos
    (b := fun _ => Real.exp (‖t₁‖ + 1)) (integrable_const _)
    (fun t _ => (by fun_prop : Continuous fun s : ℝ =>
      (((1 - s) ^ 2 / 2 : ℝ) : ℂ) * cexp (t * s)).aestronglyMeasurable) ?_
    (ae_of_all _ fun s => (by fun_prop : Differentiable ℂ fun t : ℂ =>
      (((1 - s) ^ 2 / 2 : ℝ) : ℂ) * cexp (t * s)).differentiableOn)
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs t ht => ?_
  rw [mem_ball, dist_eq_norm] at ht
  have ht' : ‖t‖ < ‖t₁‖ + 1 := by linarith [norm_sub_norm_le t t₁]
  have h1 : |(1 - s) ^ 2 / 2| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [hs.1, hs.2]
  have h2 : ‖cexp (t * s)‖ ≤ Real.exp (‖t₁‖ + 1) := by
    refine (norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hs.1]
    nlinarith [norm_nonneg t, hs.2]
  rw [norm_mul, norm_real, Real.norm_eq_abs]
  calc _ ≤ 1 * Real.exp (‖t₁‖ + 1) := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

attribute [fun_prop] differentiable_i9E3

@[fun_prop]
theorem measurable_i9E3 : Measurable i9E3 := differentiable_i9E3.continuous.measurable

/-! ### Maximum modulus on a disc -/

theorem i9_norm_le_of_sphere {h : ℂ → ℂ} (hh : Differentiable ℂ h) {ρ M : ℝ} (hρ : 0 < ρ)
    (hM : ∀ ε : ℂ, ‖ε‖ = ρ → ‖h ε‖ ≤ M) {ε : ℂ} (hε : ‖ε‖ ≤ ρ) : ‖h ε‖ ≤ M := by
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) ρ) isBounded_ball
    hh.diffContOnCl (fun z hz => ?_) ?_
  · rw [frontier_ball 0 hρ.ne'] at hz
    exact hM z (by simpa using hz)
  · rw [closure_ball 0 hρ.ne']
    simpa using hε

/-- Coefficient bounds for `ε F₁ + ε² F₂ + ε³ G(ε)` from a bound on a circle. -/
theorem i9_taylor3_bound {F₁ F₂ : ℂ} {G : ℂ → ℂ} (hG : Differentiable ℂ G) {ρ b : ℝ}
    (hρ : 0 < ρ) (hf : ∀ ε : ℂ, ‖ε‖ = ρ → ‖ε * F₁ + ε ^ 2 * F₂ + ε ^ 3 * G ε‖ ≤ b) :
    ‖F₁‖ ≤ b / ρ ∧ ‖F₂‖ ≤ 2 * b / ρ ^ 2 ∧ ∀ ε : ℂ, ‖ε‖ ≤ ρ → ‖G ε‖ ≤ 4 * b / ρ ^ 3 := by
  have h1 : ‖F₁‖ ≤ b / ρ := by
    have := i9_norm_le_of_sphere (h := fun ε => F₁ + ε * F₂ + ε ^ 2 * G ε) (by fun_prop) hρ
      (M := b / ρ) (fun ε hε => by
        rw [le_div_iff₀ hρ, ← hε, ← norm_mul]
        convert hf ε hε using 2
        ring) (ε := 0) (by simp; positivity)
    simpa using this
  have hb : 0 ≤ b := by
    by_contra hneg
    have : b / ρ < 0 := div_neg_of_neg_of_pos (not_le.mp hneg) hρ
    linarith [(norm_nonneg F₁).trans h1]
  have h2 : ‖F₂‖ ≤ 2 * b / ρ ^ 2 := by
    have := i9_norm_le_of_sphere (h := fun ε => F₂ + ε * G ε) (by fun_prop) hρ
      (M := 2 * b / ρ ^ 2) (fun ε hε => by
        rw [le_div_iff₀ (by positivity), ← hε, ← norm_pow, ← norm_mul]
        have e : (F₂ + ε * G ε) * ε ^ 2 = (ε * F₁ + ε ^ 2 * F₂ + ε ^ 3 * G ε) - ε * F₁ := by ring
        rw [e]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, hε]
        have := hf ε hε
        have : ρ * ‖F₁‖ ≤ b := by rw [le_div_iff₀ hρ] at h1; linarith
        linarith) (ε := 0) (by simp; positivity)
    simpa using this
  refine ⟨h1, h2, fun ε hε => i9_norm_le_of_sphere hG hρ (fun ε hε => ?_) hε⟩
  rw [le_div_iff₀ (by positivity), ← hε, ← norm_pow, ← norm_mul]
  have e : G ε * ε ^ 3 = (ε * F₁ + ε ^ 2 * F₂ + ε ^ 3 * G ε) - ε * F₁ - ε ^ 2 * F₂ := by ring
  rw [e]
  have hsub : ‖ε * F₁ + ε ^ 2 * F₂ + ε ^ 3 * G ε - ε * F₁ - ε ^ 2 * F₂‖ ≤
      ‖ε * F₁ + ε ^ 2 * F₂ + ε ^ 3 * G ε‖ + ‖ε * F₁‖ + ‖ε ^ 2 * F₂‖ :=
    (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
  refine hsub.trans ?_
  rw [norm_mul, norm_mul, norm_pow, hε]
  have := hf ε hε
  have h1' : ρ * ‖F₁‖ ≤ b := by rw [le_div_iff₀ hρ] at h1; linarith
  have h2' : ρ ^ 2 * ‖F₂‖ ≤ 2 * b := by rw [le_div_iff₀ (by positivity)] at h2; linarith
  linarith

/-! ### The pointwise Taylor coefficients -/

/-- `D = c w y (1 - y)`. -/
def i9RemD (x w y : ℝ) : ℝ := x * (1 - x) * w * (y * (1 - y))

/-- `Λ = 2 log c + 2 log w + log y + log (1 - y)`. -/
noncomputable def i9RemLam (x w y : ℝ) : ℝ :=
  2 * Real.log (x * (1 - x)) + 2 * Real.log w + Real.log y + Real.log (1 - y)

/-- `S_k = P logᵏ P - w y logᵏ (w y) - (1 - y) P₀ logᵏ P₀ - y P₁ logᵏ P₁ + y w logᵏ w`: the
`y`-subtraction of `P logᵏ P - w y logᵏ (w y)`. -/
noncomputable def i9RemS (k : ℕ) (x w y : ℝ) : ℝ :=
  i9Poly x w y * Real.log (i9Poly x w y) ^ k - w * y * Real.log (w * y) ^ k -
    (1 - y) * i9Poly x w 0 * Real.log (i9Poly x w 0) ^ k -
    y * i9Poly x w 1 * Real.log (i9Poly x w 1) ^ k + y * w * Real.log w ^ k

/-- **The first Taylor coefficient** `F₁ = -3 S₁ / D`. -/
noncomputable def i9RemF1 (z : ℝ × ℝ × ℝ) : ℝ :=
  -3 * i9RemS 1 z.1 z.2.1 z.2.2 / i9RemD z.1 z.2.1 z.2.2

/-- **The second Taylor coefficient** `F₂ = (Λ (-3 S₁) + 9/2 S₂) / D`. -/
noncomputable def i9RemF2 (z : ℝ × ℝ × ℝ) : ℝ :=
  (i9RemLam z.1 z.2.1 z.2.2 * (-3 * i9RemS 1 z.1 z.2.1 z.2.2) + 9 / 2 * i9RemS 2 z.1 z.2.1 z.2.2) /
    i9RemD z.1 z.2.1 z.2.2

/-- One term `β λ³ E₃(ε λ)` of the cubic remainder, `λ = Λ - 3 log Q`. -/
noncomputable def i9RemTerm (ε : ℂ) (x w y β Q : ℝ) : ℂ :=
  (β : ℂ) * ((i9RemLam x w y - 3 * Real.log Q : ℝ) : ℂ) ^ 3 *
    i9E3 (ε * ((i9RemLam x w y - 3 * Real.log Q : ℝ) : ℂ))

/-- **The cubic remainder** `G(ε) = D⁻¹ Σⱼ βⱼ λⱼ³ E₃(ε λⱼ)`. -/
noncomputable def i9RemG (ε : ℂ) (z : ℝ × ℝ × ℝ) : ℂ :=
  ((i9RemD z.1 z.2.1 z.2.2 : ℝ) : ℂ)⁻¹ *
    (i9RemTerm ε z.1 z.2.1 z.2.2 (i9Poly z.1 z.2.1 z.2.2) (i9Poly z.1 z.2.1 z.2.2) +
      i9RemTerm ε z.1 z.2.1 z.2.2 (-(z.2.1 * z.2.2)) (z.2.1 * z.2.2) +
      i9RemTerm ε z.1 z.2.1 z.2.2 (-((1 - z.2.2) * i9Poly z.1 z.2.1 0)) (i9Poly z.1 z.2.1 0) +
      i9RemTerm ε z.1 z.2.1 z.2.2 (-(z.2.2 * i9Poly z.1 z.2.1 1)) (i9Poly z.1 z.2.1 1) +
      i9RemTerm ε z.1 z.2.1 z.2.2 (z.2.2 * z.2.1) z.2.1)

theorem i9_cpow_two_mul_sub_one {r : ℝ} (hr : 0 < r) (ε : ℂ) :
    (r : ℂ) ^ (2 * ε - 1) = (r : ℂ)⁻¹ * cexp (ε * (2 * (Real.log r : ℂ))) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr.ne'), ← ofReal_log hr.le,
    show (Real.log r : ℂ) * (2 * ε - 1) = -(Real.log r : ℂ) + ε * (2 * (Real.log r : ℂ)) by ring,
    Complex.exp_add, Complex.exp_neg, ← ofReal_exp, Real.exp_log hr]

theorem i9_cpow_sub_one {r : ℝ} (hr : 0 < r) (ε : ℂ) :
    (r : ℂ) ^ (ε - 1) = (r : ℂ)⁻¹ * cexp (ε * (Real.log r : ℂ)) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr.ne'), ← ofReal_log hr.le,
    show (Real.log r : ℂ) * (ε - 1) = -(Real.log r : ℂ) + ε * (Real.log r : ℂ) by ring,
    Complex.exp_add, Complex.exp_neg, ← ofReal_exp, Real.exp_log hr]

theorem i9_cpow_one_sub_three_mul {r : ℝ} (hr : 0 < r) (ε : ℂ) :
    (r : ℂ) ^ (1 - 3 * ε) = (r : ℂ) * cexp (ε * (-3 * (Real.log r : ℂ))) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr.ne'), ← ofReal_log hr.le,
    show (Real.log r : ℂ) * (1 - 3 * ε) = (Real.log r : ℂ) + ε * (-3 * (Real.log r : ℂ)) by ring,
    Complex.exp_add, ← ofReal_exp, Real.exp_log hr]

theorem i9_exp_prod {ε : ℂ} (a b c d e : ℝ) :
    cexp (ε * (2 * (a : ℂ))) * cexp (ε * (2 * (b : ℂ))) * cexp (ε * (c : ℂ)) *
        cexp (ε * (d : ℂ)) * cexp (ε * (-3 * (e : ℂ))) =
      1 + ε * ((2 * a + 2 * b + c + d - 3 * e : ℝ) : ℂ) +
        (ε * ((2 * a + 2 * b + c + d - 3 * e : ℝ) : ℂ)) ^ 2 / 2 +
        (ε * ((2 * a + 2 * b + c + d - 3 * e : ℝ) : ℂ)) ^ 3 *
          i9E3 (ε * ((2 * a + 2 * b + c + d - 3 * e : ℝ) : ℂ)) := by
  rw [← exp_eq_i9E3]
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The pointwise expansion** of the remainder integrand. -/
theorem i9Rem_integrand_eq {x w y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) {ε : ℂ} (hs : 1 - 3 * ε ≠ 0) :
    i9Wt ε x w * i9WtY ε y * i9PsiSub ε x w y =
      ε * (i9RemF1 (x, w, y) : ℂ) + ε ^ 2 * (i9RemF2 (x, w, y) : ℂ) +
        ε ^ 3 * i9RemG ε (x, w, y) := by
  have hc : 0 < x * (1 - x) := i9_c_pos hx
  have hw0 : 0 < w := hw.1
  have hy0 : 0 < y := hy.1
  have hy1 : 0 < 1 - y := by linarith [hy.2]
  have hw1 : 0 < 1 - w := by linarith [hw.2]
  have hP : 0 < i9Poly x w y :=
    add_pos_of_nonneg_of_pos (mul_nonneg hc.le (sq_nonneg _)) (mul_pos hw0 hy0)
  have hP0 : 0 < i9Poly x w 0 := by
    unfold i9Poly; rw [mul_zero, add_zero]; exact mul_pos hc (pow_pos hw1 2)
  have hP1 : 0 < i9Poly x w 1 :=
    add_pos_of_nonneg_of_pos (mul_nonneg hc.le (sq_nonneg _)) (by simpa using hw0)
  have hwy : 0 < w * y := mul_pos hw0 hy0
  have e1 := i9_exp_prod (ε := ε) (Real.log (x * (1 - x))) (Real.log w) (Real.log y)
    (Real.log (1 - y)) (Real.log (i9Poly x w y))
  have e2 := i9_exp_prod (ε := ε) (Real.log (x * (1 - x))) (Real.log w) (Real.log y)
    (Real.log (1 - y)) (Real.log (w * y))
  have e3 := i9_exp_prod (ε := ε) (Real.log (x * (1 - x))) (Real.log w) (Real.log y)
    (Real.log (1 - y)) (Real.log (i9Poly x w 0))
  have e4 := i9_exp_prod (ε := ε) (Real.log (x * (1 - x))) (Real.log w) (Real.log y)
    (Real.log (1 - y)) (Real.log (i9Poly x w 1))
  have e5 := i9_exp_prod (ε := ε) (Real.log (x * (1 - x))) (Real.log w) (Real.log y)
    (Real.log (1 - y)) (Real.log w)
  unfold i9Wt i9WtY i9PsiSub i9Psi
  simp only [mul_one, mul_zero, ofReal_zero, zero_cpow hs]
  rw [i9_cpow_two_mul_sub_one hc, i9_cpow_two_mul_sub_one hw0, i9_cpow_sub_one hy0,
    i9_cpow_sub_one hy1, i9_cpow_one_sub_three_mul hP, i9_cpow_one_sub_three_mul hwy,
    i9_cpow_one_sub_three_mul hc, i9_cpow_one_sub_three_mul hP0,
    i9_cpow_one_sub_three_mul hP1, i9_cpow_one_sub_three_mul hw0]
  simp only [i9RemF1, i9RemF2, i9RemG, i9RemTerm, i9RemS, i9RemD, i9RemLam]
  have hP' : (i9Poly x w y : ℂ) = (i9Poly x w 0 : ℂ) + w * y := by
    unfold i9Poly; push_cast; ring
  have hP1' : (i9Poly x w 1 : ℂ) = (i9Poly x w 0 : ℂ) + w := by
    unfold i9Poly; push_cast; ring
  push_cast at e1 e2 e3 e4 e5 ⊢
  have hDi : ((x : ℂ) * (1 - x) * w * (y * (1 - y)))⁻¹ =
      ((x : ℂ) * (1 - x))⁻¹ * (w : ℂ)⁻¹ * (y : ℂ)⁻¹ * (1 - (y : ℂ))⁻¹ := by
    rw [show ((x : ℂ) * (1 - x) * w * (y * (1 - y))) = ((x : ℂ) * (1 - x)) * w * y * (1 - y) by
      ring, mul_inv, mul_inv, mul_inv]
  simp only [div_eq_mul_inv]
  rw [hDi]
  set Di : ℂ := ((x : ℂ) * (1 - x))⁻¹ * (w : ℂ)⁻¹ * (y : ℂ)⁻¹ * (1 - (y : ℂ))⁻¹ with hDi'
  set L : ℂ := 2 * (Real.log (x * (1 - x)) : ℂ) + 2 * (Real.log w : ℂ) + (Real.log y : ℂ) +
    (Real.log (1 - y) : ℂ) with hL
  linear_combination (Di * (i9Poly x w y : ℂ)) * e1 + (-(Di * (w * y))) * e2 +
    (-(Di * ((1 - y) * (i9Poly x w 0 : ℂ)))) * e3 + (-(Di * (y * (i9Poly x w 1 : ℂ)))) * e4 +
    (Di * (y * w)) * e5 + Di * (1 + ε * L + ε ^ 2 * L ^ 2 / 2) * hP' -
    y * Di * (1 + ε * L + ε ^ 2 * L ^ 2 / 2) * hP1'

theorem i9Rem_integrand_eq' {z : ℝ × ℝ × ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) {ε : ℂ} (hs : 1 - 3 * ε ≠ 0) :
    i9Wt ε z.1 z.2.1 * i9WtY ε z.2.2 * i9PsiSub ε z.1 z.2.1 z.2.2 =
      ε * (i9RemF1 z : ℂ) + ε ^ 2 * (i9RemF2 z : ℂ) + ε ^ 3 * i9RemG ε z := by
  obtain ⟨x, w, y⟩ := z
  exact i9Rem_integrand_eq hz.1 hz.2.1 hz.2.2 hs

/-! ### Bounds and integrability -/

/-- The dominating function of `QED.ThreeLoopD.norm_i9Rem_integrand_le`. -/
noncomputable def i9RemBound (z : ℝ × ℝ × ℝ) : ℝ :=
  51 * ((z.1 * (1 - z.1)) ^ (-(39 / 40) : ℝ) * (z.2.1 ^ (-(39 / 40) : ℝ) *
    (z.2.2 * (1 - z.2.2)) ^ (-(37 / 40) : ℝ)))

theorem integrable_i9RemBound :
    Integrable i9RemBound
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))) := by
  rw [volume_restrict_prod3]
  exact ((integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
    ((integrableOn_rpow_Ioo (by norm_num)).mul_prod
      (integrableOn_mul_one_sub_rpow_Ioo (by norm_num)))).const_mul 51

theorem differentiable_i9RemG (z : ℝ × ℝ × ℝ) : Differentiable ℂ fun ε => i9RemG ε z := by
  unfold i9RemG i9RemTerm
  fun_prop

theorem measurable_i9RemG (ε : ℂ) : Measurable fun z => i9RemG ε z := by
  unfold i9RemG i9RemTerm i9RemLam i9RemD i9Poly
  fun_prop

theorem measurable_i9RemF1 : Measurable i9RemF1 := by
  unfold i9RemF1 i9RemS i9RemD i9Poly
  fun_prop

theorem measurable_i9RemF2 : Measurable i9RemF2 := by
  unfold i9RemF2 i9RemS i9RemD i9RemLam i9Poly
  fun_prop

/-- **Coefficient bounds**: `|F₁| ≤ 25 b`, `|F₂| ≤ 1250 b`, `‖G(ε)‖ ≤ 62500 b` on `‖ε‖ ≤ 1/25`. -/
theorem i9Rem_coeff_bounds {z : ℝ × ℝ × ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :
    |i9RemF1 z| ≤ 25 * i9RemBound z ∧ |i9RemF2 z| ≤ 1250 * i9RemBound z ∧
      ∀ ε : ℂ, ‖ε‖ ≤ 1 / 25 → ‖i9RemG ε z‖ ≤ 62500 * i9RemBound z := by
  obtain ⟨h1, h2, h3⟩ := i9_taylor3_bound (F₁ := (i9RemF1 z : ℂ)) (F₂ := (i9RemF2 z : ℂ))
    (differentiable_i9RemG z) (ρ := 1 / 25) (b := i9RemBound z) (by norm_num) (fun ε hε => by
      have hε' : ‖ε‖ < 1 / 20 := by rw [hε]; norm_num
      rw [← i9Rem_integrand_eq' hz (i9_eps_facts hε').2.2.2.2]
      exact norm_i9Rem_integrand_le hε' hz.1 hz.2.1 hz.2.2)
  rw [norm_real, Real.norm_eq_abs] at h1 h2
  refine ⟨h1.trans (le_of_eq (by ring)), h2.trans (le_of_eq (by ring)),
    fun ε hε => (h3 ε hε).trans (le_of_eq (by ring))⟩

/-! ### The expansion -/

/-- **`Rem(ε) = ε ∫ F₁ + ε² ∫ F₂ + ε³ ∫ G(ε)`** for `‖ε‖ < 1/25`. -/
theorem i9Rem_eq_taylor {ε : ℂ} (hε : ‖ε‖ < 1 / 25) :
    i9Rem ε =
      ε * ((∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1), i9RemF1 z : ℝ) : ℂ) +
        ε ^ 2 * ((∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1), i9RemF2 z : ℝ) : ℂ) +
        ε ^ 3 * ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1), i9RemG ε z := by
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :=
    measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo)
  have hs := (i9_eps_facts (by linarith : ‖ε‖ < 1 / 20)).2.2.2.2
  have hb := integrable_i9RemBound
  have hF1 : Integrable (fun z => (i9RemF1 z : ℂ))
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))) :=
    Integrable.mono' (hb.const_mul 25) (measurable_i9RemF1.complex_ofReal.aestronglyMeasurable)
      (ae_restrict_of_forall_mem hS fun z hz => by
        rw [norm_real, Real.norm_eq_abs]; exact (i9Rem_coeff_bounds hz).1)
  have hF2 : Integrable (fun z => (i9RemF2 z : ℂ))
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))) :=
    Integrable.mono' (hb.const_mul 1250) (measurable_i9RemF2.complex_ofReal.aestronglyMeasurable)
      (ae_restrict_of_forall_mem hS fun z hz => by
        rw [norm_real, Real.norm_eq_abs]; exact (i9Rem_coeff_bounds hz).2.1)
  have hG : Integrable (fun z => i9RemG ε z)
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))) :=
    Integrable.mono' (hb.const_mul 62500) ((measurable_i9RemG ε).aestronglyMeasurable)
      (ae_restrict_of_forall_mem hS fun z hz => (i9Rem_coeff_bounds hz).2.2 ε hε.le)
  have hA : Integrable (fun z => ε * (i9RemF1 z : ℂ) + ε ^ 2 * (i9RemF2 z : ℂ))
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))) :=
    (hF1.const_mul ε).add (hF2.const_mul (ε ^ 2))
  unfold i9Rem
  rw [setIntegral_congr_fun hS (fun z hz => i9Rem_integrand_eq' hz hs),
    integral_add hA (hG.const_mul (ε ^ 3)),
    integral_add (hF1.const_mul ε) (hF2.const_mul (ε ^ 2)), integral_const_mul,
    integral_const_mul, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]

/-- `ε ↦ ∫ G(ε)` is analytic at `0`. -/
theorem analyticAt_i9RemR :
    AnalyticAt ℂ (fun ε => ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1), i9RemG ε z)
      0 := by
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :=
    measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo)
  have hd : ∀ ε₀ ∈ ball (0 : ℂ) (1 / 50), DifferentiableAt ℂ
      (fun ε => ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1), i9RemG ε z) ε₀ := by
    intro ε₀ h0
    have hball : ∀ ε ∈ ball ε₀ (1 / 50), ‖ε‖ ≤ 1 / 25 := fun ε hε => by
      have := norm_sub_norm_le ε ε₀
      rw [mem_ball, dist_eq_norm] at hε
      rw [mem_ball, dist_zero_right] at h0
      linarith
    refine differentiableAt_integral_of_holomorphic (by norm_num : (0 : ℝ) < 1 / 50)
      (b := fun z => 62500 * i9RemBound z) (integrable_i9RemBound.const_mul _)
      (fun ε _ => (measurable_i9RemG ε).aestronglyMeasurable) ?_
      (ae_of_all _ fun z => (differentiable_i9RemG z).differentiableOn)
    exact ae_restrict_of_forall_mem hS fun z hz ε hε => (i9Rem_coeff_bounds hz).2.2 ε (hball ε hε)
  exact DifferentiableOn.analyticAt (fun ε hε => (hd ε hε).differentiableWithinAt)
    (ball_mem_nhds 0 (by norm_num))

/-- **The remainder to order `ε²`**, with the coefficients as real integrals:
`Rem(ε) = ε ∫ F₁ + ε² ∫ F₂ + O(ε³)`. -/
theorem hasTruncLaurent_i9Rem_integrals :
    HasTruncLaurent i9Rem (fun ε =>
      ε * ((∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1), i9RemF1 z : ℝ) : ℂ) +
        ε ^ 2 * ((∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1), i9RemF2 z : ℝ) : ℂ))
      3 :=
  ⟨_, analyticAt_i9RemR, eventually_nhdsWithin_of_eventually_nhds
    (eventually_of_mem (ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 25)) fun ε hε =>
      i9Rem_eq_taylor (by simpa using hε))⟩

end QED.ThreeLoopD
