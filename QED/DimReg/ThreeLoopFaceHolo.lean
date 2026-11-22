/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopFaceThm
public import QED.DimReg.ThreeLoopTmplLP
public import QED.DimReg.Analytic

/-!
# Holomorphy of the face continuation `cont9` in `(s₇, s₈)`

The continuation `QED.DimReg.ThreeLoop.cont9 n d₀ λ s₇ s₈` of the normalized nine-variable
integral is an integral of `x₇^{s₇+k₇} x₈^{s₈+k₈}` against a fixed function, times entire
factors `1/Γ`. Inside the strips where the integral converges absolutely it is holomorphic in
each variable (`QED.DimReg.differentiableOn_integral_mul_exp`, with `x_b^s = exp(s log x_b)`):

* `differentiableOn_integral_wt9`: `s ↦ ∫ x^{ν-1}|_{ν_b = s} ∂^A G^{-d/2}` is holomorphic on
  `{a₁ < re s < a₂}` if the integrals at `re s = a₁` and `re s = a₂` converge;
* `eventually_differentiableOn_cont9_seven`, `eventually_differentiableOn_cont9_eight`: for
  `re λ` large, `cont9` is holomorphic in `s₇` on `{-k₇ - 1/2 < re s₇ < M}` for every `s₈` with
  `-k₈ - 1 < re s₈ ≤ M`, and symmetrically in `s₈`.

The normalization `QED.DimReg.ThreeLoop.normLP` of the nine-variable integral splits as
`pf9 · 1/(Γ(ν₇) Γ(ν₈))` (`normLP_nu9`), with `pf9` entire in `(ν₇, ν₈)` and equal to `norm9` at
`(ν₇, ν₈) = (-k₇, -k₈)` (`pf9_neg_ord`).
-/

@[expose] public section

open Complex Filter Topology Set MeasureTheory QED.DimReg QED.DimReg.Sector QED.DimReg.LineCont
open QED.DimReg.TwoLoopSESector (atRe eventually_re_gt eventually_list)

namespace QED.DimReg.ThreeLoop

/-! ### Parametric integrals in one exponent -/

theorem wt9_update_nu (ν : Fin 9 → ℂ) (b : Fin 9) (s : ℂ) (x : Fin 9 → ℝ) :
    wt9 (Function.update ν b s) x =
      (x b : ℂ) ^ (s - 1) * ∏ i ∈ Finset.univ.erase b, (x i : ℂ) ^ (ν i - 1) := by
  rw [wt9, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b), Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun i hi => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

theorem wt9_update_eq_exp (ν : Fin 9 → ℂ) (b : Fin 9) (s : ℂ) {x : Fin 9 → ℝ}
    (hx : x ∈ posOrthant 9) :
    wt9 (Function.update ν b s) x =
      wt9 (Function.update ν b 0) x * exp (s * (Real.log (x b) : ℂ)) := by
  have hxb := (mem_posOrthant.mp hx) b
  have hx0 : (x b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hxb.ne'
  rw [wt9_update_nu, wt9_update_nu, show s - 1 = (0 - 1) + s by ring, cpow_add _ _ hx0,
    cpow_def_of_ne_zero hx0 s, ← ofReal_log hxb.le]
  ring_nf

/-- **Holomorphy in one exponent.** -/
theorem differentiableOn_integral_wt9 (ν : Fin 9 → ℂ) (b : Fin 9) (A : List ZPoly) (d : ℂ)
    {a₁ a₂ : ℝ}
    (h1 : IntegrableOn (fun x => wt9 (Function.update ν b a₁) x * faceDeriv A d x) (posOrthant 9))
    (h2 : IntegrableOn (fun x => wt9 (Function.update ν b a₂) x * faceDeriv A d x)
      (posOrthant 9)) :
    DifferentiableOn ℂ
      (fun s => ∫ x in posOrthant 9, wt9 (Function.update ν b s) x * faceDeriv A d x)
      {s | a₁ < s.re ∧ s.re < a₂} := by
  set f : (Fin 9 → ℝ) → ℂ := fun x => wt9 (Function.update ν b 0) x * faceDeriv A d x
  set φ : (Fin 9 → ℝ) → ℝ := fun x => Real.log (x b)
  have hP := measurableSet_posOrthant 9
  have hφm : Measurable φ := Real.measurable_log.comp (measurable_pi_apply b)
  have heq : ∀ s : ℂ, ∀ x ∈ posOrthant 9,
      wt9 (Function.update ν b s) x * faceDeriv A d x = f x * exp (s * φ x) := by
    intro s x hx
    rw [wt9_update_eq_exp ν b s hx]
    ring
  have hnorm : ∀ a : ℝ, ∀ x ∈ posOrthant 9, ‖wt9 (Function.update ν b a) x * faceDeriv A d x‖ =
      ‖f x‖ * Real.exp (a * φ x) := by
    intro a x hx
    rw [heq a x hx, norm_mul, norm_exp]
    congr 2
    simp
  have hint : ∀ a : ℝ, IntegrableOn (fun x => wt9 (Function.update ν b a) x * faceDeriv A d x)
      (posOrthant 9) → Integrable (fun x => ‖f x‖ * Real.exp (a * φ x))
        (volume.restrict (posOrthant 9)) := fun a h =>
    (integrableOn_congr_fun (hnorm a) hP).mp h.norm
  have hfm : AEStronglyMeasurable f (volume.restrict (posOrthant 9)) := by
    have hm : AEStronglyMeasurable (fun x => wt9 (Function.update ν b a₁) x * faceDeriv A d x *
        exp (-(a₁ : ℂ) * φ x)) (volume.restrict (posOrthant 9)) :=
      h1.aestronglyMeasurable.mul (continuous_exp.comp_aestronglyMeasurable
        ((continuous_ofReal.comp_aestronglyMeasurable hφm.aestronglyMeasurable).const_mul _))
    refine hm.congr ((ae_restrict_mem hP).mono fun x hx => ?_)
    simp only
    rw [heq _ x hx, mul_assoc, ← exp_add]
    simp
  have hD := differentiableOn_integral_mul_exp hfm hφm.aestronglyMeasurable (hint a₁ h1)
    (hint a₂ h2)
  refine hD.congr fun s _ => ?_
  exact setIntegral_congr_fun hP fun x hx => heq s x hx

/-! ### Holomorphy of `cont9` -/

theorem update_nu9_seven_zero (ν : Fin 7 → ℂ) (a c : ℂ) :
    nu9 ν a c = Function.update (nu9 ν 0 c) 7 a := (update_nu9_seven ν 0 c a).symm

theorem update_nu9_eight_zero (ν : Fin 7 → ℂ) (a c : ℂ) :
    nu9 ν a c = Function.update (nu9 ν a 0) 8 c := (update_nu9_eight ν a 0 c).symm

theorem differentiable_inv_Gamma_add (k : ℕ) :
    Differentiable ℂ fun s : ℂ => (Gamma (s + ((k + 1 : ℕ) : ℂ)))⁻¹ :=
  differentiable_one_div_Gamma.comp (differentiable_id.add (differentiable_const _))

/-- **`cont9` is holomorphic in `s₇`** on `{-k₇ - 1/2 < re s₇ < M}`, for every `s₈` with
`-k₈ - 1 < re s₈ ≤ M`, for `re λ` large. -/
theorem eventually_differentiableOn_cont9_seven (n : Fin 9 → ℤ) (d₀ : ℂ) {M : ℝ} (hM0 : 0 ≤ M) :
    ∀ᶠ l in atRe, ∀ c : ℂ, -(ord8 n : ℝ) - 1 < c.re → c.re ≤ M →
      DifferentiableOn ℂ (fun a => cont9 n d₀ l a c)
        {a | -(ord7 n : ℝ) - 1 / 2 < a.re ∧ a.re < M} := by
  filter_upwards [eventually_integrableOn_faceDeriv (lbl3 n []) d₀ (bPolys (ord7 n) (ord8 n))
    (M + ord7 n + ord8 n + 1)] with l hl c hc1 hc2
  set k₇ := ord7 n
  set k₈ := ord8 n
  set ν' := lineNu w7 (lbl3 n []) l
  set c' := c + ((k₈ + 1 : ℕ) : ℂ)
  have hk7 : (0 : ℝ) ≤ k₇ := Nat.cast_nonneg _
  have hk8 : (0 : ℝ) ≤ k₈ := Nat.cast_nonneg _
  have hc'1 : 0 < c'.re := by simp only [c', add_re, natCast_re]; push_cast; linarith
  have hc'2 : c'.re ≤ M + k₇ + k₈ + 1 := by
    simp only [c', add_re, natCast_re]; push_cast; linarith
  have hM : -(k₇ : ℝ) - 1 / 2 < M := by linarith
  have hI := differentiableOn_integral_wt9 (nu9 ν' 0 c') 7 (bPolys k₇ k₈) (lineD h7 d₀ l)
    (a₁ := 1 / 2) (a₂ := M + k₇ + 1)
    (by rw [← update_nu9_seven_zero]
        exact hl _ _ (by rw [ofReal_re]; norm_num) (by rw [ofReal_re]; linarith) hc'1 hc'2)
    (by rw [← update_nu9_seven_zero]
        exact hl _ _ (by rw [ofReal_re]; linarith) (by rw [ofReal_re]; linarith) hc'1 hc'2)
  have hmaps : MapsTo (fun a : ℂ => a + ((k₇ + 1 : ℕ) : ℂ))
      {a | -(k₇ : ℝ) - 1 / 2 < a.re ∧ a.re < M} {s | 1 / 2 < s.re ∧ s.re < M + k₇ + 1} := by
    intro a ha
    simp only [mem_ofPred_eq, add_re, natCast_re] at ha ⊢
    push_cast
    constructor <;> linarith [ha.1, ha.2]
  have hcomp := hI.comp (differentiable_id.add (differentiable_const _)).differentiableOn hmaps
  unfold cont9
  refine DifferentiableOn.const_mul ?_ _
  refine (((differentiable_inv_Gamma_add k₇).differentiableOn).mul
    (differentiableOn_const _)).mul ?_
  refine hcomp.congr fun a _ => ?_
  simp only [Function.comp_apply]
  rw [← update_nu9_seven_zero]
  rfl

/-- **`cont9` is holomorphic in `s₈`** on `{-k₈ - 1/2 < re s₈ < M}`, for every `s₇` with
`-k₇ - 1 < re s₇ ≤ M`, for `re λ` large. -/
theorem eventually_differentiableOn_cont9_eight (n : Fin 9 → ℤ) (d₀ : ℂ) {M : ℝ} (hM0 : 0 ≤ M) :
    ∀ᶠ l in atRe, ∀ a : ℂ, -(ord7 n : ℝ) - 1 < a.re → a.re ≤ M →
      DifferentiableOn ℂ (fun c => cont9 n d₀ l a c)
        {c | -(ord8 n : ℝ) - 1 / 2 < c.re ∧ c.re < M} := by
  filter_upwards [eventually_integrableOn_faceDeriv (lbl3 n []) d₀ (bPolys (ord7 n) (ord8 n))
    (M + ord7 n + ord8 n + 1)] with l hl a ha1 ha2
  set k₇ := ord7 n
  set k₈ := ord8 n
  set ν' := lineNu w7 (lbl3 n []) l
  set a' := a + ((k₇ + 1 : ℕ) : ℂ)
  have hk7 : (0 : ℝ) ≤ k₇ := Nat.cast_nonneg _
  have hk8 : (0 : ℝ) ≤ k₈ := Nat.cast_nonneg _
  have ha'1 : 0 < a'.re := by simp only [a', add_re, natCast_re]; push_cast; linarith
  have ha'2 : a'.re ≤ M + k₇ + k₈ + 1 := by
    simp only [a', add_re, natCast_re]; push_cast; linarith
  have hM : -(k₈ : ℝ) - 1 / 2 < M := by linarith
  have hI := differentiableOn_integral_wt9 (nu9 ν' a' 0) 8 (bPolys k₇ k₈) (lineD h7 d₀ l)
    (a₁ := 1 / 2) (a₂ := M + k₈ + 1)
    (by rw [← update_nu9_eight_zero]
        exact hl _ _ ha'1 ha'2 (by rw [ofReal_re]; norm_num) (by rw [ofReal_re]; linarith))
    (by rw [← update_nu9_eight_zero]
        exact hl _ _ ha'1 ha'2 (by rw [ofReal_re]; linarith) (by rw [ofReal_re]; linarith))
  have hmaps : MapsTo (fun c : ℂ => c + ((k₈ + 1 : ℕ) : ℂ))
      {c | -(k₈ : ℝ) - 1 / 2 < c.re ∧ c.re < M} {s | 1 / 2 < s.re ∧ s.re < M + k₈ + 1} := by
    intro c hc
    simp only [mem_ofPred_eq, add_re, natCast_re] at hc ⊢
    push_cast
    constructor <;> linarith [hc.1, hc.2]
  have hcomp := hI.comp (differentiable_id.add (differentiable_const _)).differentiableOn hmaps
  unfold cont9
  refine DifferentiableOn.const_mul ?_ _
  refine ((differentiableOn_const _).mul
    ((differentiable_inv_Gamma_add k₈).differentiableOn)).mul ?_
  refine hcomp.congr fun c _ => ?_
  simp only [Function.comp_apply]
  rw [← update_nu9_eight_zero]
  rfl

/-! ### The normalization -/

/-- The normalization of the nine-variable integral at `(ν'(λ), a, c)` without the factor
`1/(Γ(a) Γ(c))`: `Γ(d/2) / (Γ(2d - |ν'| - a - c) ∏_{b < 7} Γ(ν'_b))`, along the line through
the seven-variable label `m`. -/
noncomputable def pf9 (m : Fin 7 → ℤ) (d₀ l a c : ℂ) : ℂ :=
  Gamma (lineD h7 d₀ l / 2) *
    (Gamma (2 * lineD h7 d₀ l - ∑ b : Fin 7, lineNu w7 m l b - a - c))⁻¹ *
    ∏ b : Fin 7, (Gamma (lineNu w7 m l b))⁻¹

theorem normLP_nu9 (m : Fin 7 → ℤ) (d₀ l a c : ℂ) :
    normLP (nu9 (lineNu w7 m l) a c) (lineD h7 d₀ l) =
      pf9 m d₀ l a c * (Gamma a)⁻¹ * (Gamma c)⁻¹ := by
  have e7 : nu9 (lineNu w7 m l) a c (Fin.castSucc (Fin.last 7)) = a := rfl
  have e8 : nu9 (lineNu w7 m l) a c (Fin.last 8) = c := rfl
  rw [normLP, pf9, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.prod_univ_castSucc,
    Fin.prod_univ_castSucc]
  simp only [nu9_castSucc, e7, e8]
  rw [show 2 * lineD h7 d₀ l - (∑ i : Fin 7, lineNu w7 m l i + a + c) =
    2 * lineD h7 d₀ l - ∑ b : Fin 7, lineNu w7 m l b - a - c by ring]
  ring

theorem pf9_neg_ord (n : Fin 9 → ℤ) (d₀ l : ℂ) :
    pf9 (lbl3 n []) d₀ l (-(ord7 n : ℂ)) (-(ord8 n : ℂ)) = norm9 n d₀ l := by
  simp only [pf9, norm9]
  congr 3
  ring_nf

theorem differentiable_pf9_seven (m : Fin 7 → ℤ) (d₀ l c : ℂ) :
    Differentiable ℂ fun a => pf9 m d₀ l a c := by
  unfold pf9
  exact ((differentiable_const _).mul (differentiable_one_div_Gamma.comp
    ((differentiable_const _).sub differentiable_id |>.sub (differentiable_const _)))).mul
    (differentiable_const _)

theorem differentiable_pf9_eight (m : Fin 7 → ℤ) (d₀ l a : ℂ) :
    Differentiable ℂ fun c => pf9 m d₀ l a c := by
  unfold pf9
  exact ((differentiable_const _).mul (differentiable_one_div_Gamma.comp
    ((differentiable_const _).sub differentiable_id))).mul (differentiable_const _)

end QED.DimReg.ThreeLoop
