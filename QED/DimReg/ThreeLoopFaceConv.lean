/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopFaceInt
public import QED.DimReg.BetaPrimeNested
public import QED.DimReg.OrthantFTC

/-!
# Convergence of the nine-variable integrals near the face `x₇ = x₈ = 0`

On the closed orthant `G ≥ G₇(x')` (`x' = (x₀, …, x₆)`; `G` has natural coefficients) and `G`
contains the monomials `x₅x₆x₇` and `x₄x₆x₈`, so `3G ≥ A + B + C` with `A = G₇(x')`,
`B = x₅x₆x₇`, `C = x₄x₆x₈`. For `σ ≥ μ₇ + μ₈ + 2`,
`G^{-σ} ≤ 3^σ A^{-σ} (1 + (B/A))^{-(μ₇+1)} (1 + (C/A))^{-(μ₈+1)}`, and integrating the two Beta
integrals of the second kind in `x₈` and `x₇` (`QED.DimReg.integrableOn_prod_betaPrime`) leaves
a Lee–Pomeransky integral of `G₇` at shifted exponents:

* `integrableOn_conv9`: `x^{μ-1} G^{-σ}` is integrable on `(0,∞)^9` if `μ₇, μ₈ > 0`,
  `μ₇ + μ₈ + 2 ≤ σ` and `x'^{μ''-1} G₇^{-(σ-μ₇-μ₈)}` is integrable on `(0,∞)^7`, where
  `μ'' = μ' - μ₇(e₅ + e₆) - μ₈(e₄ + e₆)`;
* `eventually_lpConvergent9`: along the lines of `QED.DimReg.ThreeLoop.F7`, for `re λ` large,
  the nine-variable integral converges at every `(ν, d)` with `ν'` and `d` within `R` of the
  line, and `0 < re ν₇, re ν₈ ≤ R` (the seven-variable integral of the bound is controlled by
  the sector data `QED.DimReg.ThreeLoop.S7`, at bounded distance from the line);
* `eventually_integrableOn_faceDeriv`: hence, for `re λ` large, `x^{ν-1} ∂^A G^{-d/2}` is
  integrable for every `ν = (ν'(λ), ν₇, ν₈)` with `0 < re ν₇, re ν₈ ≤ M`: these are the
  integrability hypotheses of `QED.DimReg.ThreeLoop.mellin_step`.
-/

@[expose] public section

open Complex Filter Topology Set MeasureTheory QED.DimReg QED.DimReg.Sector QED.DimReg.LineCont
open QED.DimReg.TwoLoopSESector (atRe eventually_re_gt eventually_list)

namespace QED.DimReg.ThreeLoop

/-! ### Splitting off the last coordinate -/

theorem piFinSuccAbove_last_symm {n : ℕ} (z : ℝ × (Fin n → ℝ)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm z =
      Fin.snoc z.2 z.1 := by
  show Fin.insertNth (α := fun _ => ℝ) (Fin.last n) z.1 z.2 = _
  rw [Fin.insertNth_last']

theorem integrableOn_posOrthant_snoc {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {f : (Fin (n + 1) → ℝ) → E} :
    IntegrableOn f (posOrthant (n + 1)) ↔
      IntegrableOn (fun z : ℝ × (Fin n → ℝ) => f (Fin.snoc z.2 z.1)) (Ioi 0 ×ˢ posOrthant n)
        ((volume : Measure ℝ).prod volume) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  have hp : MeasurePreserving e := volume_preserving_piFinSuccAbove (fun _ => ℝ) (Fin.last n)
  rw [← Measure.volume_eq_prod, ← (hp.integrableOn_comp_preimage e.measurableEmbedding),
    preimage_piFinSuccAbove_posOrthant]
  refine integrableOn_congr_fun (fun x _ => ?_) (measurableSet_posOrthant _)
  simp only [Function.comp_apply]
  rw [← piFinSuccAbove_last_symm, e.symm_apply_apply]

theorem setIntegral_posOrthant_snoc {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : (Fin (n + 1) → ℝ) → E) :
    ∫ x in posOrthant (n + 1), f x =
      ∫ z in Ioi 0 ×ˢ posOrthant n, f (Fin.snoc z.2 z.1) ∂((volume : Measure ℝ).prod volume) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  have hp : MeasurePreserving e := volume_preserving_piFinSuccAbove (fun _ => ℝ) (Fin.last n)
  rw [← Measure.volume_eq_prod, ← preimage_piFinSuccAbove_posOrthant (Fin.last n),
    ← hp.setIntegral_preimage_emb e.measurableEmbedding]
  refine setIntegral_congr_fun (by
    rw [preimage_piFinSuccAbove_posOrthant]; exact measurableSet_posOrthant _) fun x _ => ?_
  rw [← piFinSuccAbove_last_symm, e.symm_apply_apply]

theorem snoc_mem_posOrthant {n : ℕ} {w : Fin n → ℝ} (hw : w ∈ posOrthant n) {t : ℝ}
    (ht : 0 < t) : (Fin.snoc w t : Fin (n + 1) → ℝ) ∈ posOrthant (n + 1) := by
  rw [mem_posOrthant] at hw ⊢
  intro i
  induction i using Fin.lastCases with
  | last => simpa using ht
  | cast j => simpa using hw j

theorem init_mem_posOrthant {n : ℕ} {x : Fin (n + 1) → ℝ} (hx : x ∈ posOrthant (n + 1)) :
    Fin.init x ∈ posOrthant n :=
  mem_posOrthant.mpr fun _ => mem_posOrthant.mp hx _

/-! ### Polynomial facts -/

theorem continuous_npolyEval {N : ℕ} (P : NPoly) : Continuous fun y : Fin N → ℝ => P.eval y := by
  unfold NPoly.eval mono
  exact continuous_list_sum _ fun t _ => continuous_const.mul
    (continuous_finsetProd _ fun k _ => (continuous_apply k).pow _)

theorem mono_le_mono {N : ℕ} (α : List ℕ) {x y : Fin N → ℝ} (hy : ∀ k, 0 ≤ y k)
    (hxy : ∀ k, y k ≤ x k) : mono α y ≤ mono α x :=
  Finset.prod_le_prod₀ (fun k _ => pow_nonneg (hy k) _)
    (fun k _ => pow_le_pow_left₀ (hy k) (hxy k) _)

theorem npolyEval_mono {N : ℕ} (P : NPoly) {x y : Fin N → ℝ} (hy : ∀ k, 0 ≤ y k)
    (hxy : ∀ k, y k ≤ x k) : P.eval y ≤ P.eval x :=
  List.sum_le_sum fun t _ =>
    mul_le_mul_of_nonneg_left (mono_le_mono t.1 hy hxy) (Nat.cast_nonneg _)

theorem term_le_npolyEval {N : ℕ} {P : NPoly} {t : List ℕ × ℕ} (ht : t ∈ P) {x : Fin N → ℝ}
    (hx : ∀ k, 0 ≤ x k) : (t.2 : ℝ) * mono t.1 x ≤ P.eval x := by
  refine List.single_le_sum (fun z hz => ?_) _ (List.mem_map.mpr ⟨t, ht, rfl⟩)
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp hz
  exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun k _ => pow_nonneg (hx k) _)

/-- The first seven coordinates. -/
def res7 (x : Fin 9 → ℝ) : Fin 7 → ℝ := Fin.init (Fin.init x)

theorem ext7_le {x : Fin 9 → ℝ} (hx : ∀ k, 0 ≤ x k) (i : Fin 9) : ext7 (res7 x) i ≤ x i := by
  simp only [ext7, res7, Fin.init]
  split_ifs with h
  · exact le_of_eq (congrArg x (Fin.ext rfl))
  · exact hx i

theorem g7_le_G {x : Fin 9 → ℝ} (hx : ∀ k, 0 ≤ x k) : g7.eval (res7 x) ≤ lpPoly.eval x := by
  rw [← lpPoly_eval_ext7]
  refine npolyEval_mono _ (fun i => ?_) (ext7_le hx)
  simp only [ext7, res7, Fin.init]
  split_ifs
  · exact hx _
  · exact le_rfl

theorem g7_pos {x : Fin 7 → ℝ} (hx : x ∈ posOrthant 7) : 0 < g7.eval x := by
  have := F7.pos x hx
  rwa [show F7.S = S7 from rfl, S7_G] at this

theorem mem_lpPoly_x7 : ([0, 0, 0, 0, 0, 1, 1, 1, 0], 1) ∈ lpPoly := by
  rw [lpPoly_eq_lit]; decide +kernel

theorem mem_lpPoly_x8 : ([0, 0, 0, 0, 1, 0, 1, 0, 1], 1) ∈ lpPoly := by
  rw [lpPoly_eq_lit]; decide +kernel

/-- **The lower bound** `3G ≥ G₇(x') + x₅x₆x₇ + x₄x₆x₈` on the closed orthant. -/
theorem three_G_ge {x : Fin 9 → ℝ} (hx : ∀ k, 0 ≤ x k) :
    g7.eval (res7 x) + x 5 * x 6 * x 7 + x 4 * x 6 * x 8 ≤ 3 * lpPoly.eval x := by
  have h1 := g7_le_G hx
  have h2 := term_le_npolyEval mem_lpPoly_x7 hx
  have h3 := term_le_npolyEval mem_lpPoly_x8 hx
  simp only [mono, Fin.prod_univ_succ, Fin.prod_univ_zero] at h2 h3
  norm_num at h2 h3
  have e2 : x 5 * x 6 * x 7 = x (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))) *
      x (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0)))))) *
      x (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))))) := rfl
  have e3 : x 4 * x 6 * x 8 = x (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0)))) *
      x (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0)))))) *
      x (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ
        (Fin.succ 0)))))))) := rfl
  rw [e2, e3]
  linarith

/-! ### The bound by two Beta integrals of the second kind -/

/-- **The elementary inequality**: if `A + B + C ≤ 3G`, `A > 0`, `B, C ≥ 0` and
`0 ≤ p, q`, `p + q ≤ σ`, then `G^{-σ} ≤ 3^σ A^{-σ} (1 + B/A)^{-p} (1 + C/A)^{-q}`. -/
theorem rpow_neg_le_three {A B C G σ p q : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hG : A + B + C ≤ 3 * G) (hp : 0 ≤ p) (hq : 0 ≤ q) (hσ : p + q ≤ σ) :
    G ^ (-σ) ≤ 3 ^ σ * A ^ (-σ) * (1 + B / A) ^ (-p) * (1 + C / A) ^ (-q) := by
  have hS : 0 < A + B + C := by positivity
  have hG0 : 0 < G := by linarith
  have h3 : G ^ (-σ) = 3 ^ σ * (3 * G) ^ (-σ) := by
    rw [Real.mul_rpow (by norm_num) hG0.le, ← mul_assoc, ← Real.rpow_add (by norm_num)]
    simp
  have h1 : (3 * G) ^ (-σ) ≤ (A + B + C) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos hS hG (by linarith)
  have hsplit : (A + B + C) ^ (-σ) =
      (A + B + C) ^ (-(σ - p - q)) * (A + B + C) ^ (-p) * (A + B + C) ^ (-q) := by
    rw [← Real.rpow_add hS, ← Real.rpow_add hS]; ring_nf
  have i1 : (A + B + C) ^ (-(σ - p - q)) ≤ A ^ (-(σ - p - q)) :=
    Real.rpow_le_rpow_of_nonpos hA (by linarith) (by linarith)
  have i2 : (A + B + C) ^ (-p) ≤ (A + B) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have i3 : (A + B + C) ^ (-q) ≤ (A + C) ^ (-q) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have e1 : (1 + B / A) ^ (-p) = (A + B) ^ (-p) * A ^ p := by
    rw [show 1 + B / A = (A + B) / A by field_simp, Real.div_rpow (by positivity) hA.le,
      Real.rpow_neg hA.le, div_inv_eq_mul]
  have e2 : (1 + C / A) ^ (-q) = (A + C) ^ (-q) * A ^ q := by
    rw [show 1 + C / A = (A + C) / A by field_simp, Real.div_rpow (by positivity) hA.le,
      Real.rpow_neg hA.le, div_inv_eq_mul]
  have e3 : A ^ (-σ) * A ^ p * A ^ q = A ^ (-(σ - p - q)) := by
    rw [← Real.rpow_add hA, ← Real.rpow_add hA]; ring_nf
  rw [h3, e1, e2]
  calc 3 ^ σ * (3 * G) ^ (-σ) ≤ 3 ^ σ * ((A + B + C) ^ (-(σ - p - q)) * (A + B + C) ^ (-p) *
        (A + B + C) ^ (-q)) := by
        rw [← hsplit]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ 3 ^ σ * (A ^ (-(σ - p - q)) * (A + B) ^ (-p) * (A + C) ^ (-q)) := by
        gcongr
    _ = _ := by rw [← e3]; ring

/-- The weight `∏_b x_b^{μ_b - 1}` in seven variables, real. -/
noncomputable def wtR (μ : Fin 7 → ℝ) (x : Fin 7 → ℝ) : ℝ := ∏ b, x b ^ (μ b - 1)

/-- The slope `x₅x₆/G₇` of the bound in `x₇`. -/
noncomputable def c7 (x : Fin 7 → ℝ) : ℝ := x 5 * x 6 / g7.eval x

/-- The slope `x₄x₆/G₇` of the bound in `x₈`. -/
noncomputable def c8 (x : Fin 7 → ℝ) : ℝ := x 4 * x 6 / g7.eval x

/-- The shifted exponents `μ'' = μ' - μ₇(e₅ + e₆) - μ₈(e₄ + e₆)`. -/
def shift7 {R : Type*} [Ring R] (μ : Fin 7 → R) (μ₇ μ₈ : R) : Fin 7 → R := fun b =>
  μ b - (if b = 5 ∨ b = 6 then μ₇ else 0) - (if b = 4 ∨ b = 6 then μ₈ else 0)

/-- The majorant: `3^σ x'^{μ'-1} G₇^{-σ}` times two Beta integrands of the second kind. -/
noncomputable def maj9 (μ : Fin 7 → ℝ) (μ₇ μ₈ σ : ℝ) (x : Fin 9 → ℝ) : ℂ :=
  ((3 ^ σ * wtR μ (res7 x) * g7.eval (res7 x) ^ (-σ) : ℝ) : ℂ) *
    betaPrimeIntegrand μ₇ 1 (c7 (res7 x)) (Fin.init x (Fin.last 7)) *
    betaPrimeIntegrand μ₈ 1 (c8 (res7 x)) (x (Fin.last 8))

theorem measurable_maj9 (μ : Fin 7 → ℝ) (μ₇ μ₈ σ : ℝ) : Measurable (maj9 μ μ₇ μ₈ σ) := by
  have hg : Measurable fun x : Fin 7 → ℝ => g7.eval x := (continuous_npolyEval g7).measurable
  unfold maj9 betaPrimeIntegrand c7 c8 wtR res7 Fin.init
  fun_prop

theorem c7_pos {x : Fin 7 → ℝ} (hx : x ∈ posOrthant 7) : 0 < c7 x := by
  have h := mem_posOrthant.mp hx
  exact div_pos (mul_pos (h 5) (h 6)) (g7_pos hx)

theorem c8_pos {x : Fin 7 → ℝ} (hx : x ∈ posOrthant 7) : 0 < c8 x := by
  have h := mem_posOrthant.mp hx
  exact div_pos (mul_pos (h 4) (h 6)) (g7_pos hx)

theorem wtR_shift7 {μ : Fin 7 → ℝ} {μ₇ μ₈ : ℝ} {x : Fin 7 → ℝ} (hx : x ∈ posOrthant 7) :
    wtR (shift7 μ μ₇ μ₈) x =
      wtR μ x * ((x 5 * x 6) ^ (-μ₇) * (x 4 * x 6) ^ (-μ₈)) := by
  have h := mem_posOrthant.mp hx
  have hb : ∀ b, x b ^ (shift7 μ μ₇ μ₈ b - 1) = x b ^ (μ b - 1) *
      (x b ^ (-(if b = 5 ∨ b = 6 then μ₇ else 0)) *
        x b ^ (-(if b = 4 ∨ b = 6 then μ₈ else 0))) := by
    intro b
    rw [← Real.rpow_add (h b), ← Real.rpow_add (h b), shift7]
    ring_nf
  simp only [wtR, hb, Finset.prod_mul_distrib, Fin.prod_univ_seven]
  rw [Real.mul_rpow (h 5).le (h 6).le, Real.mul_rpow (h 4).le (h 6).le]
  simp

theorem norm_maj9 (μ : Fin 7 → ℝ) (μ₇ μ₈ σ : ℝ) {x : Fin 9 → ℝ} (hx : x ∈ posOrthant 9) :
    ‖maj9 μ μ₇ μ₈ σ x‖ = 3 ^ σ * wtR μ (res7 x) * g7.eval (res7 x) ^ (-σ) *
      (x 7 ^ (μ₇ - 1) * (1 + c7 (res7 x) * x 7) ^ (-(μ₇ + 1))) *
      (x 8 ^ (μ₈ - 1) * (1 + c8 (res7 x) * x 8) ^ (-(μ₈ + 1))) := by
  have h := mem_posOrthant.mp hx
  have hr : res7 x ∈ posOrthant 7 := init_mem_posOrthant (init_mem_posOrthant hx)
  have hw : 0 ≤ wtR μ (res7 x) := Finset.prod_nonneg fun b _ =>
    Real.rpow_nonneg (mem_posOrthant.mp hr b).le _
  have hA := g7_pos hr
  have h7 : 0 < Fin.init x (Fin.last 7) := h 7
  have h8 : 0 < x (Fin.last 8) := h 8
  rw [maj9, norm_mul, norm_mul, norm_betaPrimeIntegrand _ _ (c7_pos hr) h7,
    norm_betaPrimeIntegrand _ _ (c8_pos hr) h8, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  simp only [ofReal_re, one_re]
  rfl

theorem measurable_snoc_swap (n : ℕ) :
    Measurable fun z : ℝ × (Fin n → ℝ) => (Fin.snoc z.2 z.1 : Fin (n + 1) → ℝ) := by
  have := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm.measurable
  convert this using 1
  funext z
  rw [piFinSuccAbove_last_symm]

/-- **The majorant is integrable** if the seven-variable integral at the shifted exponents
converges. -/
theorem integrableOn_maj9 {μ : Fin 7 → ℝ} {μ₇ μ₈ σ : ℝ} (h7 : 0 < μ₇) (h8 : 0 < μ₈)
    (h : IntegrableOn (fun x => wtR (shift7 μ μ₇ μ₈) x * g7.eval x ^ (-(σ - μ₇ - μ₈)))
      (posOrthant 7)) :
    IntegrableOn (maj9 μ μ₇ μ₈ σ) (posOrthant 9) := by
  rw [integrableOn_posOrthant_snoc]
  refine integrableOn_prod_betaPrime (measurableSet_posOrthant 8) (a := (μ₈ : ℂ)) (b := 1)
    (by simpa using h8) (by simp)
    ((measurable_maj9 μ μ₇ μ₈ σ).comp (measurable_snoc_swap 8)).aestronglyMeasurable
    (A := fun w => ((3 ^ σ * wtR μ (Fin.init w) * g7.eval (Fin.init w) ^ (-σ) : ℝ) : ℂ) *
      betaPrimeIntegrand μ₇ 1 (c7 (Fin.init w)) (w (Fin.last 7)))
    (c := fun w => c8 (Fin.init w)) (fun w hw => c8_pos (init_mem_posOrthant hw))
    (fun t _ w _ => by simp only [maj9, res7, Fin.init_snoc, Fin.snoc_last]) ?_
  rw [integrableOn_posOrthant_snoc]
  have hm : Measurable fun w : Fin 8 → ℝ =>
      ((3 ^ σ * wtR μ (Fin.init w) * g7.eval (Fin.init w) ^ (-σ) : ℝ) : ℂ) *
        betaPrimeIntegrand μ₇ 1 (c7 (Fin.init w)) (w (Fin.last 7)) *
        ((c8 (Fin.init w) : ℝ) : ℂ) ^ (-(μ₈ : ℂ)) := by
    have hg : Measurable fun x : Fin 7 → ℝ => g7.eval x := (continuous_npolyEval g7).measurable
    unfold betaPrimeIntegrand c7 c8 wtR Fin.init
    fun_prop
  refine integrableOn_prod_betaPrime (measurableSet_posOrthant 7) (a := (μ₇ : ℂ)) (b := 1)
    (by simpa using h7) (by simp) (hm.comp (measurable_snoc_swap 7)).aestronglyMeasurable
    (A := fun x => ((3 ^ σ * wtR μ x * g7.eval x ^ (-σ) : ℝ) : ℂ) *
      ((c8 x : ℝ) : ℂ) ^ (-(μ₈ : ℂ)))
    (c := c7) (fun x hx => c7_pos hx)
    (fun t _ w _ => by simp only [Fin.init_snoc, Fin.snoc_last]; ring) ?_
  refine IntegrableOn.congr_fun ((h.const_mul (3 ^ σ)).ofReal) (fun x hx => ?_)
    (measurableSet_posOrthant 7)
  have hx' := mem_posOrthant.mp hx
  have hA := g7_pos hx
  have e7 : ((c7 x : ℝ) : ℂ) ^ (-(μ₇ : ℂ)) = ((c7 x ^ (-μ₇) : ℝ) : ℂ) := by
    rw [ofReal_cpow (c7_pos hx).le]; push_cast; rfl
  have e8 : ((c8 x : ℝ) : ℂ) ^ (-(μ₈ : ℂ)) = ((c8 x ^ (-μ₈) : ℝ) : ℂ) := by
    rw [ofReal_cpow (c8_pos hx).le]; push_cast; rfl
  rw [e7, e8, ← ofReal_mul, ← ofReal_mul]
  congr 1
  rw [wtR_shift7 hx, c7, c8, Real.div_rpow (mul_pos (hx' 5) (hx' 6)).le hA.le,
    Real.div_rpow (mul_pos (hx' 4) (hx' 6)).le hA.le]
  have e : g7.eval x ^ (-(σ - μ₇ - μ₈)) = g7.eval x ^ (-σ) * g7.eval x ^ μ₇ * g7.eval x ^ μ₈ := by
    rw [← Real.rpow_add hA, ← Real.rpow_add hA]; ring_nf
  rw [e, Real.rpow_neg hA.le μ₇, Real.rpow_neg hA.le μ₈]
  field_simp
  change _ = (_ : ℝ) * _
  ring

/-- **Convergence near the face, real form.** If `μ₇, μ₈ > 0`, `μ₇ + μ₈ + 2 ≤ σ` and
`x'^{μ''-1} G₇^{-(σ - μ₇ - μ₈)}` is integrable on `(0,∞)^7`, then `x^{μ-1} G^{-σ}` is
integrable on `(0,∞)^9`. -/
theorem integrableOn_conv9 {μ : Fin 9 → ℝ} {σ : ℝ} (h7 : 0 < μ 7) (h8 : 0 < μ 8)
    (hσ : μ 7 + μ 8 + 2 ≤ σ)
    (h : IntegrableOn (fun x => wtR (shift7 (fun b => μ (Fin.castSucc (Fin.castSucc b)))
      (μ 7) (μ 8)) x * g7.eval x ^ (-(σ - μ 7 - μ 8))) (posOrthant 7)) :
    IntegrableOn (fun x => (∏ i, x i ^ (μ i - 1)) * lpPoly.eval x ^ (-σ)) (posOrthant 9) := by
  set μ' : Fin 7 → ℝ := fun b => μ (Fin.castSucc (Fin.castSucc b))
  have hM := (integrableOn_maj9 h7 h8 h).norm
  refine hM.mono' ?_ (ae_restrict_of_forall_mem (measurableSet_posOrthant 9) fun x hx => ?_)
  · have hG : Measurable fun x : Fin 9 → ℝ => lpPoly.eval x :=
      (continuous_npolyEval lpPoly).measurable
    exact (by fun_prop : Measurable fun x : Fin 9 → ℝ =>
      (∏ i, x i ^ (μ i - 1)) * lpPoly.eval x ^ (-σ)).aestronglyMeasurable
  have h' := mem_posOrthant.mp hx
  have hr : res7 x ∈ posOrthant 7 := init_mem_posOrthant (init_mem_posOrthant hx)
  have hA := g7_pos hr
  have hG := G_pos hx
  have hw : 0 ≤ wtR μ' (res7 x) := Finset.prod_nonneg fun b _ =>
    Real.rpow_nonneg (mem_posOrthant.mp hr b).le _
  rw [norm_maj9 _ _ _ _ hx, Real.norm_eq_abs, abs_of_nonneg (by
    exact mul_nonneg (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (h' i).le _)
      (Real.rpow_nonneg hG.le _))]
  have hprod : ∏ i, x i ^ (μ i - 1) = wtR μ' (res7 x) * x 7 ^ (μ 7 - 1) * x 8 ^ (μ 8 - 1) := by
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    rfl
  have e4 : res7 x 4 = x 4 := rfl
  have e5 : res7 x 5 = x 5 := rfl
  have e6 : res7 x 6 = x 6 := rfl
  have hB : c7 (res7 x) * x 7 = x 5 * x 6 * x 7 / g7.eval (res7 x) := by
    rw [c7, e5, e6]; ring
  have hC : c8 (res7 x) * x 8 = x 4 * x 6 * x 8 / g7.eval (res7 x) := by
    rw [c8, e4, e6]; ring
  have key := rpow_neg_le_three hA (by have := h' 5; have := h' 6; have := h' 7; positivity)
    (by have := h' 4; have := h' 6; have := h' 8; positivity) (three_G_ge fun k => (h' k).le)
    (p := μ 7 + 1) (q := μ 8 + 1) (σ := σ) (by linarith) (by linarith) (by linarith)
  rw [hprod, hB, hC]
  have p7 : 0 ≤ x 7 ^ (μ 7 - 1) := Real.rpow_nonneg (h' 7).le _
  have p8 : 0 ≤ x 8 ^ (μ 8 - 1) := Real.rpow_nonneg (h' 8).le _
  calc wtR μ' (res7 x) * x 7 ^ (μ 7 - 1) * x 8 ^ (μ 8 - 1) * lpPoly.eval x ^ (-σ)
      ≤ wtR μ' (res7 x) * x 7 ^ (μ 7 - 1) * x 8 ^ (μ 8 - 1) *
        (3 ^ σ * g7.eval (res7 x) ^ (-σ) *
          (1 + x 5 * x 6 * x 7 / g7.eval (res7 x)) ^ (-(μ 7 + 1)) *
          (1 + x 4 * x 6 * x 8 / g7.eval (res7 x)) ^ (-(μ 8 + 1))) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by ring

/-! ### Along the lines: the seven-variable integral at bounded distance -/

/-- A perturbation of the argument moves an integer-affine form by at most
`(Σᵢ |aᵢ| + |c_d|) ρ`. -/
theorem abs_re_eval_sub_le {N : ℕ} (f : AffForm) {ν ν₀ : Fin N → ℂ} {d d₀ : ℂ} {ρ : ℝ}
    (hν : ∀ i, |(ν i).re - (ν₀ i).re| ≤ ρ) (hd : |d.re - d₀.re| ≤ ρ) :
    |(f.eval ν d).re - (f.eval ν₀ d₀).re| ≤
      (∑ i : Fin N, |(f.2.1.getD i 0 : ℝ)| + |(f.2.2 : ℝ)|) * ρ := by
  have e : (f.eval ν d).re - (f.eval ν₀ d₀).re =
      ∑ i : Fin N, (f.2.1.getD i 0 : ℝ) * ((ν i).re - (ν₀ i).re) +
        (f.2.2 : ℝ) * ((d.re - d₀.re) / 2) := by
    simp only [AffForm.eval, add_re, re_sum, mul_re, intCast_re, intCast_im, zero_mul, sub_zero,
      div_ofNat_re, mul_sub, Finset.sum_sub_distrib]
    ring
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans hd
  rw [e, add_mul, Finset.sum_mul]
  refine (abs_add_le _ _).trans (add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => ?_)) ?_)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hν i) (abs_nonneg _)
  · rw [abs_mul, abs_div, abs_two]
    have := abs_nonneg (f.2.2 : ℝ)
    nlinarith [abs_nonneg (d.re - d₀.re)]

/-- **Positivity of the leaf exponents near the line**: for `re λ` large, every point within
`ρ` of `(n + λw, d₀ + 2hλ)` (in real parts) has all leaf exponents with positive real part. -/
theorem eventually_reGt_near {N : ℕ} (F : LineFamily N) (n : Fin N → ℤ) (d₀ : ℂ) (ρ : ℝ) :
    ∀ᶠ l in atRe, ∀ (ν : Fin N → ℂ) (e : ℂ),
      (∀ i, |(ν i).re - (lineNu F.w n l i).re| ≤ ρ) → |e.re - (lineD F.h d₀ l).re| ≤ ρ →
      F.S.ReGt (fun _ => ν) (fun _ => e) 0 0 := by
  simp only [LPSectorData.ReGt]
  have hT : ∀ T : Finset (Fin N), ∀ᶠ l in atRe, ∀ ps ∈ (F.S.tree T).paths, ∀ k : Fin N,
      ∀ (ν : Fin N → ℂ) (e : ℂ), (∀ i, |(ν i).re - (lineNu F.w n l i).re| ≤ ρ) →
      |e.re - (lineD F.h d₀ l).re| ≤ ρ → 0 < (F.S.leafS T ps (fun _ => ν) (fun _ => e) 0 k).re := by
    intro T
    have hfin : {ps | ps ∈ (F.S.tree T).paths}.Finite := (F.S.tree T).paths.finite_toSet
    refine ((eventually_all_finite hfin).2 fun ps hps => eventually_all.2 fun k => ?_).mono
      fun l hl ps hps => hl ps hps
    have s1 : (1 : ℝ) ≤ slopeZ F.w F.h (leafForm F.S.D (flagsOf T) ps (F.S.leafMin T ps) k) := by
      exact_mod_cast F.slope_ge hps k
    set f := leafForm F.S.D (flagsOf T) ps (F.S.leafMin T ps) k
    set C : ℝ := ∑ i : Fin N, |(f.2.1.getD i 0 : ℝ)| + |(f.2.2 : ℝ)|
    have hC : 0 ≤ C := by positivity
    filter_upwards [eventually_re_gt (|baseRe f n d₀| + C * ρ + 1)] with l hl ν e hν he
    have hρ : 0 ≤ ρ := (abs_nonneg _).trans he
    rw [F.leafS_eq]
    have hpert := abs_re_eval_sub_le f hν he
    have hline := re_eval_line F.w F.h f n d₀ l
    have hb := neg_abs_le (baseRe f n d₀)
    have hCR : 0 ≤ C * ρ := by positivity
    have hl0 : 0 < l.re := by linarith [abs_nonneg (baseRe f n d₀)]
    have s1' : l.re ≤ (slopeZ F.w F.h f : ℝ) * l.re := by nlinarith
    rw [abs_le] at hpert
    linarith [hpert.1]
  exact (eventually_all.2 hT).mono fun l hl ν e hν he T ps hps k => hl T ps hps k ν e hν he

/-- The hypotheses of `eventually_lpConvergent9`: `ν'` and `d` within `R` of the line,
`0 < re ν₇, re ν₈ ≤ R`. -/
def Near9 (n : Fin 7 → ℤ) (d₀ : ℂ) (R : ℝ) (l : ℂ) (ν : Fin 9 → ℂ) (e : ℂ) : Prop :=
  (∀ b : Fin 7, |(ν (Fin.castSucc (Fin.castSucc b))).re - (lineNu w7 n l b).re| ≤ R) ∧
    0 < (ν 7).re ∧ (ν 7).re ≤ R ∧ 0 < (ν 8).re ∧ (ν 8).re ≤ R ∧
    |e.re - (lineD h7 d₀ l).re| ≤ R

theorem re_shift7 (μ : Fin 7 → ℂ) (a c : ℂ) (b : Fin 7) :
    (shift7 μ a c b).re = shift7 (fun b => (μ b).re) a.re c.re b := by
  simp only [shift7]
  split_ifs <;> simp

theorem Near9.shift {n : Fin 7 → ℤ} {d₀ : ℂ} {R : ℝ} {l : ℂ} {ν : Fin 9 → ℂ} {e : ℂ}
    (h : Near9 n d₀ R l ν e) :
    (∀ b, |(shift7 (fun b => ν (Fin.castSucc (Fin.castSucc b))) (ν 7) (ν 8) b).re -
      (lineNu w7 n l b).re| ≤ 5 * R) ∧
      |(e - 2 * ν 7 - 2 * ν 8).re - (lineD h7 d₀ l).re| ≤ 5 * R := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun b => ?_, ?_⟩
  · rw [re_shift7]
    have := h1 b
    simp only [shift7]
    rw [abs_le] at this ⊢
    constructor <;> split_ifs <;> linarith
  · simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    rw [abs_le] at h6 ⊢
    constructor <;> linarith

theorem measurable_lpPoly : Measurable fun x : Fin 9 → ℝ => lpPoly.eval x :=
  (continuous_npolyEval lpPoly).measurable

theorem measurable_g7 : Measurable fun x : Fin 7 → ℝ => g7.eval x :=
  (continuous_npolyEval g7).measurable

/-- **Convergence near the face along the lines.** For `re λ` large, the nine-variable
Lee–Pomeransky integral converges at every `(ν, d)` with `ν'`, `d` within `R` of the line
`(n + λw₇, d₀ + 6λ)` and `0 < re ν₇, re ν₈ ≤ R`. -/
theorem eventually_lpConvergent9 (n : Fin 7 → ℤ) (d₀ : ℂ) (R : ℝ) :
    ∀ᶠ l in atRe, ∀ (ν : Fin 9 → ℂ) (e : ℂ), Near9 n d₀ R l ν e →
      LPConvergent (fun x => lpPoly.eval x) ν e := by
  have hleaf : ∀ᶠ l in atRe, ∀ (ν : Fin 9 → ℂ) (e : ℂ), Near9 n d₀ R l ν e →
      F7.S.ReGt (fun _ => shift7 (fun b => ν (Fin.castSucc (Fin.castSucc b))) (ν 7) (ν 8))
        (fun _ => e - 2 * ν 7 - 2 * ν 8) 0 0 :=
    (eventually_reGt_near F7 n d₀ (5 * R)).mono fun l hl ν e hn =>
      hl _ _ hn.shift.1 hn.shift.2
  filter_upwards [hleaf, eventually_re_gt (|d₀.re| + R + 4)] with l hl hre ν e hn
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hn
  have hR : 0 ≤ R := h2.le.trans h3
  have hc7 := F7.S.lpConvergent_of_re (ν := fun _ => shift7 (fun b => ν (Fin.castSucc
    (Fin.castSucc b))) (ν 7) (ν 8)) (d := fun _ => e - 2 * ν 7 - 2 * ν 8)
    (differentiable_const _) (hl ν e ⟨h1, h2, h3, h4, h5, h6⟩)
  rw [F7_G, lpConvergent_iff_re measurable_g7 (fun x hx => g7_pos hx)] at hc7
  rw [lpConvergent_iff_re measurable_lpPoly (fun x hx => G_pos hx)]
  refine integrableOn_conv9 (μ := fun i => (ν i).re) (σ := e.re / 2) h2 h4 ?_ ?_
  · have : (lineD h7 d₀ l).re = d₀.re + 6 * l.re := by
      norm_num [lineD, ThreeLoop.h7]
    rw [abs_le, this] at h6
    have := neg_abs_le d₀.re
    have := abs_nonneg d₀.re
    linarith [h6.1]
  · refine hc7.congr_fun (fun x _ => ?_) (measurableSet_posOrthant 7)
    simp only [wtR, re_shift7]
    congr 2
    simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    ring

/-! ### The integrands `x^{ν-1} ∂^A G^{-d/2}` -/

/-- The nine exponents `(ν', ν₇, ν₈)`. -/
def nu9 (ν : Fin 7 → ℂ) (a c : ℂ) : Fin 9 → ℂ := Fin.snoc (Fin.snoc ν a) c

@[simp] theorem nu9_seven (ν : Fin 7 → ℂ) (a c : ℂ) : nu9 ν a c 7 = a := rfl

@[simp] theorem nu9_eight (ν : Fin 7 → ℂ) (a c : ℂ) : nu9 ν a c 8 = c := rfl

@[simp] theorem nu9_castSucc (ν : Fin 7 → ℂ) (a c : ℂ) (b : Fin 7) :
    nu9 ν a c (Fin.castSucc (Fin.castSucc b)) = ν b := by
  simp [nu9]

theorem integrableOn_list_sum {ι : Type*} (L : List ι) {g : ι → (Fin 9 → ℝ) → ℂ}
    {s : Set (Fin 9 → ℝ)} (h : ∀ t ∈ L, IntegrableOn (g t) s) :
    IntegrableOn (fun x => (L.map fun t => g t x).sum) s := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a List.mem_cons_self).add (ih fun t ht => h t (List.mem_cons_of_mem a ht))

theorem wt9_mul_eval (ν : Fin 9 → ℂ) (d : ℂ) (j : ℕ) (P : ZPoly) {x : Fin 9 → ℝ}
    (hx : x ∈ posOrthant 9) :
    wt9 ν x * ((lpPoly.eval x : ℝ) : ℂ) ^ (-(d / 2) - j) * (ZPoly.eval P x : ℂ) =
      (P.map fun t => (t.2 : ℂ) * lpIntegrand (fun x => lpPoly.eval x)
        (natShift ν fun k => t.1.getD k 0) (d + 2 * j) x).sum := by
  induction P with
  | nil => simp
  | cons t P ih =>
    rw [List.map_cons, List.sum_cons, ← ih, ZPoly.eval_cons, lpIntegrand_natShift _ _ _ _ hx]
    simp only [lpIntegrand, wt9, monoEval, mono]
    push_cast
    rw [show -((d + 2 * (j : ℂ)) / 2) = -(d / 2) - j by ring]
    ring

/-- `x^{ν-1} ∂^A G^{-d/2}` is integrable on `(0,∞)^9` if every Lee–Pomeransky integral
`(ν + α, d + 2j)` of its terms converges. -/
theorem integrableOn_faceDeriv_of (A : List ZPoly) (d : ℂ) (ν : Fin 9 → ℂ)
    (h : ∀ j < A.length, ∀ t ∈ A.getD j [], LPConvergent (fun x => lpPoly.eval x)
      (natShift ν fun k => t.1.getD k 0) (d + 2 * j)) :
    IntegrableOn (fun x => wt9 ν x * faceDeriv A d x) (posOrthant 9) := by
  have hI : IntegrableOn (fun x => ∑ j ∈ Finset.range A.length, fallC (-(d / 2)) j *
      ((A.getD j []).map fun t => (t.2 : ℂ) * lpIntegrand (fun x => lpPoly.eval x)
        (natShift ν fun k => t.1.getD k 0) (d + 2 * j) x).sum) (posOrthant 9) := by
    refine integrable_finsetSum _ fun j hj => (integrableOn_list_sum _ fun t ht => ?_).const_mul _
    exact (h j (Finset.mem_range.mp hj) t ht).const_mul _
  refine hI.congr_fun (fun x hx => ?_) (measurableSet_posOrthant 9)
  rw [faceDeriv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← wt9_mul_eval ν d j _ hx]
  ring

/-- A bound for all exponents occurring in `A`. -/
def degA (A : List ZPoly) : ℕ := (A.map fun P => (P.map fun t => t.1.sum).sum).sum

theorem getD_le_sum : ∀ (l : List ℕ) (k : ℕ), l.getD k 0 ≤ l.sum
  | [], k => by simp
  | a :: l, 0 => by simp
  | a :: l, k + 1 => by
    have := getD_le_sum l k
    simp only [List.getD_cons_succ, List.sum_cons]
    omega

theorem getD_le_degA {A : List ZPoly} {j : ℕ} (hj : j < A.length) {t : List ℕ × ℤ}
    (ht : t ∈ A.getD j []) (k : ℕ) : t.1.getD k 0 ≤ degA A := by
  have hA : A.getD j [] ∈ A := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    exact List.getElem_mem hj
  calc t.1.getD k 0 ≤ t.1.sum := getD_le_sum _ _
    _ ≤ ((A.getD j []).map fun t => t.1.sum).sum := List.le_sum_of_mem (List.mem_map_of_mem ht)
    _ ≤ degA A := List.le_sum_of_mem (List.mem_map_of_mem (f := fun P : ZPoly =>
          (P.map fun t => t.1.sum).sum) hA)

/-- **The integrability hypotheses of the Mellin steps.** For `re λ` large,
`x^{ν-1} ∂^A G^{-d/2}` is integrable on `(0,∞)^9` at `ν = (n' + λw₇, ν₇, ν₈)`,
`d = d₀ + 6λ`, for all `0 < re ν₇, re ν₈ ≤ M`. -/
theorem eventually_integrableOn_faceDeriv (n : Fin 7 → ℤ) (d₀ : ℂ) (A : List ZPoly) (M : ℝ) :
    ∀ᶠ l in atRe, ∀ a c : ℂ, 0 < a.re → a.re ≤ M → 0 < c.re → c.re ≤ M →
      IntegrableOn (fun x => wt9 (nu9 (lineNu w7 n l) a c) x * faceDeriv A (lineD h7 d₀ l) x)
        (posOrthant 9) := by
  filter_upwards [eventually_lpConvergent9 n d₀ (M + degA A + 2 * A.length)] with l hl a c
    ha hM hc hM'
  refine integrableOn_faceDeriv_of _ _ _ fun j hj t ht => hl _ _ ⟨fun b => ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals have hdeg := getD_le_degA hj ht
  all_goals simp only [natShift, nu9_seven, nu9_eight, nu9_castSucc, add_re, natCast_re]
  · have := hdeg b
    have h0 : (0 : ℝ) ≤ (t.1.getD b 0 : ℝ) := Nat.cast_nonneg _
    have h1 : (t.1.getD b 0 : ℝ) ≤ degA A := by exact_mod_cast this
    rw [show (t.1.getD (Fin.castSucc (Fin.castSucc b) : Fin 9) 0 : ℝ) = t.1.getD b 0 from rfl,
      add_sub_cancel_left, abs_of_nonneg h0]
    linarith [ha.le.trans hM]
  · positivity
  · have h1 : (t.1.getD 7 0 : ℝ) ≤ degA A := by exact_mod_cast hdeg 7
    have h2 : ((7 : Fin 9) : ℕ) = 7 := rfl
    rw [h2]; linarith
  · positivity
  · have h1 : (t.1.getD 8 0 : ℝ) ≤ degA A := by exact_mod_cast hdeg 8
    have h2 : ((8 : Fin 9) : ℕ) = 8 := rfl
    rw [h2]; linarith
  · have hj' : (j : ℝ) ≤ A.length := by exact_mod_cast hj.le
    simp only [mul_re, re_ofNat, im_ofNat, natCast_im, mul_zero, sub_zero, add_sub_cancel_left]
    rw [abs_le, natCast_re]
    have := Nat.cast_nonneg (α := ℝ) (degA A)
    have := Nat.cast_nonneg (α := ℝ) j
    constructor <;> linarith [ha.le.trans hM]

end QED.DimReg.ThreeLoop
