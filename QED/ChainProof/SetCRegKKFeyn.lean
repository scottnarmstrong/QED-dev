/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegKKRad
public import QED.ChainProof.SetCRegKKSplit
public import QED.Integration.FeynmanParameterGeneral
public import QED.Integration.TwoLoopParametricAlgebra

/-!
# Set (c): Feynman parameters for the scalar Källén–Lehmann integrand

The scalar integrand `kkScl` of `QED/ChainProof/SetCRegKKSplit.lean` is
`k² (k²/4 + τ² - iε)⁻¹ (k² + mγ² - iε)⁻² (k² + Λ² - iε)⁻²`. Writing it as
`4 k² ∏ᵢ aᵢ⁻¹` over five factors and applying the Feynman formula
`QED.Integration.Feynman.prod_inv_eq_factorial_mul_integral_simplex` gives

  `kkScl = 96 ∫_{Δ₄} k² (k² + M(x) - iε E(x))⁻⁵ dx`,

with `M(x) = x₀ c + (x₁ + x₂) a + (x₃ + x₄) b` (`c = 4τ²`, `a = mγ²`, `b = Λ²`) and
`E(x) = 1 + 3 x₀ ∈ [1, 4]`. At fixed spatial momentum the energy integral and the
simplex integral commute (the integrand is `O((1 + t²)⁻⁴)` uniformly on the simplex),
and the energy integrals are the closed forms `kkSp4`, `kkSp5` of
`QED/ChainProof/SetCRegKKRad.lean`.

## Main results

* `kkScl_eq_feyn`: the Feynman representation of `kkScl` at `ε > 0`.
* `integral_kkScl_cons`: `∫ dt kkScl(t, v) = 96 ∫_{Δ₄} kkPhi(x, v) dx`, where
  `kkPhi = kkSp4 (M, εE) - (M - iεE) kkSp5 (M, εE)`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real
open QED.WickModel (vacuumPolarizationFeynmanMass)

namespace QED.ChainProof.SetCRegDisp

open QED.Integration QED.Integration.Feynman
open QED.Integration.TwoLoop (simplexPoint_castSucc simplexPoint_last)

/-! ### The Feynman data -/

/-- The Feynman-averaged mass `x₀ c + (x₁ + x₂) a + (x₃ + x₄) b`, `x₄ = 1 - ∑ xᵢ`. -/
def kkM (c a b : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  x 0 * c + (x 1 + x 2) * a + (x 3 + (1 - ∑ i, x i)) * b

/-- The Feynman-averaged width `4 x₀ + x₁ + x₂ + x₃ + x₄ = 1 + 3 x₀`. -/
def kkE (x : Fin 4 → ℝ) : ℝ := 1 + 3 * x 0

/-- The five masses `c, a, a, b, b`. -/
def kkMass (c a b : ℝ) : Fin 5 → ℝ := ![c, a, a, b, b]

/-- The five widths `4, 1, 1, 1, 1` (in units of `ε`). -/
def kkWt : Fin 5 → ℝ := ![4, 1, 1, 1, 1]

/-- The five Feynman denominators `k² + Mᵢ - iε Eᵢ`. -/
noncomputable def kkA (c a b ε : ℝ) (k : Fin 4 → ℝ) (i : Fin 5) : ℂ :=
  ((Minkowski.dot k k + kkMass c a b i : ℝ) : ℂ) - ((ε * kkWt i : ℝ) : ℂ) * I

theorem kkA_im_neg {c a b ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) (i : Fin 5) :
    (kkA c a b ε k i).im < 0 := by
  fin_cases i <;> simp [kkA, kkWt] <;> linarith

theorem simplexComb_kkA (c a b ε : ℝ) (k : Fin 4 → ℝ) (x : Fin 4 → ℝ) :
    simplexComb (kkA c a b ε k) x = kkDs (kkM c a b x) (ε * kkE x) k := by
  have p0 : simplexPoint x 0 = x 0 := simplexPoint_castSucc x 0
  have p1 : simplexPoint x 1 = x 1 := simplexPoint_castSucc x 1
  have p2 : simplexPoint x 2 = x 2 := simplexPoint_castSucc x 2
  have p3 : simplexPoint x 3 = x 3 := simplexPoint_castSucc x 3
  have p4 : simplexPoint x 4 = 1 - ∑ i, x i := simplexPoint_last x
  rw [simplexComb_eq_sum_simplexPoint, Fin.sum_univ_five, p0, p1, p2, p3, p4]
  simp only [kkA, kkDs, kkM, kkE, kkMass, kkWt, Fin.sum_univ_four]
  simp
  ring

theorem kkScl_eq_prod (mγ Λ τ ε : ℝ) (k : Fin 4 → ℝ) :
    kkScl mγ Λ τ ε k =
      4 * (Minkowski.dot k k : ℂ) * ∏ i, (kkA (4 * τ ^ 2) (mγ ^ 2) (Λ ^ 2) ε k i)⁻¹ := by
  set A := kkA (4 * τ ^ 2) (mγ ^ 2) (Λ ^ 2) ε k
  have h0 : (((vacuumPolarizationFeynmanMass τ (Minkowski.dot k k) (1 / 2) : ℝ) : ℂ) -
      (ε : ℂ) * I) = A 0 / 4 := by
    simp [A, vacuumPolarizationFeynmanMass, kkA, kkMass, kkWt]
    ring
  have h1 : kkDn mγ ε k = A 1 := by simp [A, kkDn, kkA, kkMass, kkWt]
  have h2 : A 2 = A 1 := by simp [A, kkA, kkMass, kkWt]
  have h3 : kkDn Λ ε k = A 3 := by simp [A, kkDn, kkA, kkMass, kkWt]
  have h4 : A 4 = A 3 := by simp [A, kkA, kkMass, kkWt]
  rw [Fin.prod_univ_five, kkScl, h0, h1, h3, h2, h4, inv_div]
  ring

/-- **The Feynman representation of the scalar integrand.** -/
theorem kkScl_eq_feyn {mγ Λ τ ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) :
    kkScl mγ Λ τ ε k = 96 * ∫ x in simplexSet 4, (Minkowski.dot k k : ℂ) *
      (kkDs (kkM (4 * τ ^ 2) (mγ ^ 2) (Λ ^ 2) x) (ε * kkE x) k ^ 5)⁻¹ := by
  rw [kkScl_eq_prod, prod_inv_eq_factorial_mul_integral_simplex (kkA_im_neg hε k),
    integral_const_mul]
  simp only [simplexComb_kkA]
  norm_num [Nat.factorial]
  ring

/-! ### Bounds on the simplex -/

theorem simplexSet_facts {x : Fin 4 → ℝ} (hx : x ∈ simplexSet 4) :
    (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1 := by
  obtain ⟨h0, _⟩ := simplexPoint_mem_stdSimplex hx
  refine ⟨fun i => ?_, ?_⟩
  · simpa [simplexPoint_castSucc] using h0 i.castSucc
  · have := h0 (Fin.last 4)
    rw [simplexPoint_last] at this
    linarith

theorem kkM_bounds {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) {x : Fin 4 → ℝ}
    (hx : x ∈ simplexSet 4) :
    min c (min a b) ≤ kkM c a b x ∧ kkM c a b x ≤ c + a + b := by
  obtain ⟨h0, hs⟩ := simplexSet_facts hx
  rw [Fin.sum_univ_four] at hs
  have hy : 0 ≤ 1 - (x 0 + x 1 + x 2 + x 3) := by linarith
  set μ := min c (min a b)
  have hμc : μ ≤ c := min_le_left _ _
  have hμa : μ ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have hμb : μ ≤ b := (min_le_right _ _).trans (min_le_right _ _)
  have h00 := h0 0
  have h01 := h0 1
  have h02 := h0 2
  have h03 := h0 3
  unfold kkM
  rw [Fin.sum_univ_four]
  constructor
  · nlinarith [mul_nonneg h00 (sub_nonneg.2 hμc), mul_nonneg (add_nonneg h01 h02)
      (sub_nonneg.2 hμa), mul_nonneg (add_nonneg h03 hy) (sub_nonneg.2 hμb)]
  · nlinarith [mul_nonneg (show 0 ≤ 1 - x 0 by linarith) hc.le,
      mul_nonneg (show 0 ≤ 1 - (x 1 + x 2) by linarith) ha.le,
      mul_nonneg (show 0 ≤ 1 - (x 3 + (1 - (x 0 + x 1 + x 2 + x 3))) by linarith) hb.le]

theorem kkE_bounds {x : Fin 4 → ℝ} (hx : x ∈ simplexSet 4) : 1 ≤ kkE x ∧ kkE x ≤ 4 := by
  obtain ⟨h0, hs⟩ := simplexSet_facts hx
  rw [Fin.sum_univ_four] at hs
  have := h0 0
  have := h0 1
  have := h0 2
  have := h0 3
  constructor <;> unfold kkE <;> linarith

/-- The lower bound `‖k² + A - iδ‖ ≥ ε (1 + t²)/(1 + B₁ + ε)`, for `δ ≥ ε` and
`|v|² + A ≤ B₁`. -/
theorem norm_kkDs_cons_ge {A δ ε B₁ : ℝ} (hε : 0 < ε) (hδ : ε ≤ δ) (t : ℝ)
    (v : Fin 3 → ℝ) (hB : ∑ k, v k ^ 2 + A ≤ B₁) (hB₁ : 0 ≤ B₁) :
    ε * (1 + t ^ 2) ≤ (1 + B₁ + ε) * ‖kkDs A δ (Fin.cons t v)‖ := by
  have hre : (kkDs A δ (Fin.cons t v)).re = -t ^ 2 + (∑ k, v k ^ 2 + A) := by
    rw [kkDs, QED.TwoLoop.CountertermLimit.dot_cons_self]
    simp only [sub_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]
    ring
  have him : (kkDs A δ (Fin.cons t v)).im = -δ := by simp [kkDs]
  set C := kkDs A δ (Fin.cons t v)
  have h1 : ε ≤ ‖C‖ := by
    have := abs_im_le_norm C
    rw [him, abs_neg, abs_of_pos (hε.trans_le hδ)] at this
    linarith
  have h2 : t ^ 2 - B₁ ≤ ‖C‖ := by
    have := neg_abs_le C.re
    have := abs_re_le_norm C
    linarith
  by_cases ht : t ^ 2 ≤ B₁ + ε
  · nlinarith
  · push Not at ht
    nlinarith

/-! ### The energy integral at fixed spatial momentum -/

/-- The energy-integrated Feynman integrand: `kkSp4 (M, εE) - (M - iεE) kkSp5 (M, εE)`. -/
noncomputable def kkPhi (c a b ε : ℝ) (x : Fin 4 → ℝ) (v : Fin 3 → ℝ) : ℂ :=
  kkSp4 (kkM c a b x) (ε * kkE x) v -
    (((kkM c a b x : ℝ) : ℂ) - ((ε * kkE x : ℝ) : ℂ) * I) * kkSp5 (kkM c a b x) (ε * kkE x) v

theorem integrable_kkDs_pow {A δ : ℝ} (hδ : 0 < δ) (v : Fin 3 → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    Integrable fun t : ℝ => ((kkDs A δ (Fin.cons t v)) ^ n)⁻¹ := by
  have h := integrable_sq_add_zpow (kkW_mem_slitPlane (A := A) hδ v) n hn
  refine (h.const_mul ((-1 : ℂ) ^ n)).congr (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [kkDs_cons, neg_pow ((t : ℂ) ^ 2 + kkW A δ v) n, mul_inv, ← inv_pow, inv_neg_one, zpow_neg,
    zpow_natCast]

theorem kkDs_ne_zero {A δ : ℝ} (hδ : 0 < δ) (k : Fin 4 → ℝ) : kkDs A δ k ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp [kkDs] at this
  linarith

/-- At `x` in the simplex, the energy integral of `k² (k² + M - iεE)⁻⁵` is `kkPhi`. -/
theorem integral_feyn_energy {c a b ε : ℝ} (hε : 0 < ε) {x : Fin 4 → ℝ} (hx : x ∈ simplexSet 4)
    (v : Fin 3 → ℝ) :
    ∫ t : ℝ, (Minkowski.dot (Fin.cons t v : Fin 4 → ℝ) (Fin.cons t v) : ℂ) *
      (kkDs (kkM c a b x) (ε * kkE x) (Fin.cons t v) ^ 5)⁻¹ = kkPhi c a b ε x v := by
  have hδ : 0 < ε * kkE x := mul_pos hε (by linarith [(kkE_bounds hx).1])
  set A := kkM c a b x
  set δ := ε * kkE x
  have hpt : ∀ t : ℝ, (Minkowski.dot (Fin.cons t v : Fin 4 → ℝ) (Fin.cons t v) : ℂ) *
      (kkDs A δ (Fin.cons t v) ^ 5)⁻¹ = (kkDs A δ (Fin.cons t v) ^ 4)⁻¹ -
        ((A : ℂ) - (δ : ℂ) * I) * (kkDs A δ (Fin.cons t v) ^ 5)⁻¹ := fun t => by
    have hne := kkDs_ne_zero (A := A) hδ (Fin.cons t v)
    have hs : (Minkowski.dot (Fin.cons t v : Fin 4 → ℝ) (Fin.cons t v) : ℂ) =
        kkDs A δ (Fin.cons t v) - ((A : ℂ) - (δ : ℂ) * I) := by
      rw [kkDs]
      push_cast
      ring
    rw [hs]
    field_simp
  simp_rw [hpt]
  rw [integral_sub (integrable_kkDs_pow hδ v 4 (by norm_num))
    ((integrable_kkDs_pow hδ v 5 (by norm_num)).const_mul _), integral_const_mul,
    integral_kkDs_pow_four hδ, integral_kkDs_pow_five hδ, kkPhi]

theorem isFiniteMeasure_simplex : IsFiniteMeasure (volume.restrict (simplexSet 4)) :=
  isFiniteMeasure_restrict.2 (isCompact_simplexSet 4).measure_lt_top.ne

/-- The Feynman integrand at spatial momentum `v`, as a function of `(t, x)`. -/
noncomputable def kkG (c a b ε : ℝ) (v : Fin 3 → ℝ) (t : ℝ) (x : Fin 4 → ℝ) : ℂ :=
  (Minkowski.dot (Fin.cons t v : Fin 4 → ℝ) (Fin.cons t v) : ℂ) *
    (kkDs (kkM c a b x) (ε * kkE x) (Fin.cons t v) ^ 5)⁻¹

theorem measurable_kkG (c a b ε : ℝ) (v : Fin 3 → ℝ) :
    Measurable (Function.uncurry (kkG c a b ε v)) := by
  have he : Function.uncurry (kkG c a b ε v) = fun p : ℝ × (Fin 4 → ℝ) =>
      ((-p.1 ^ 2 + ∑ k, v k ^ 2 : ℝ) : ℂ) *
        (((((-p.1 ^ 2 + ∑ k, v k ^ 2 + kkM c a b p.2 : ℝ) : ℂ) -
          ((ε * kkE p.2 : ℝ) : ℂ) * I) ^ 5)⁻¹) := by
    funext p
    simp only [Function.uncurry, kkG, kkDs, QED.TwoLoop.CountertermLimit.dot_cons_self]
  have h1 : Continuous fun p : ℝ × (Fin 4 → ℝ) => ((-p.1 ^ 2 + ∑ k, v k ^ 2 : ℝ) : ℂ) := by
    fun_prop
  have h2 : Continuous fun p : ℝ × (Fin 4 → ℝ) =>
      ((-p.1 ^ 2 + ∑ k, v k ^ 2 + kkM c a b p.2 : ℝ) : ℂ) - ((ε * kkE p.2 : ℝ) : ℂ) * I := by
    unfold kkM kkE
    fun_prop
  rw [he]
  exact h1.measurable.mul (h2.pow 5).measurable.inv

/-- The uniform bound `|kkG| ≤ K (1 + t²)⁻⁴` on the simplex. -/
theorem norm_kkG_le {c a b ε : ℝ} (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε)
    (v : Fin 3 → ℝ) (t : ℝ) {x : Fin 4 → ℝ} (hx : x ∈ simplexSet 4) :
    ‖kkG c a b ε v t x‖ ≤ (1 + ∑ k, v k ^ 2) *
      (ε / (1 + (∑ k, v k ^ 2 + (c + a + b)) + ε)) ^ (-5 : ℤ) * ((1 + t ^ 2) ^ 4)⁻¹ := by
  set R := ∑ k, v k ^ 2
  have hR : 0 ≤ R := Finset.sum_nonneg fun k _ => sq_nonneg _
  set B₁ := R + (c + a + b)
  have hB₁ : 0 ≤ B₁ := by positivity
  obtain ⟨hM0, hM1⟩ := kkM_bounds hc ha hb hx
  have hE := (kkE_bounds hx).1
  set C := kkDs (kkM c a b x) (ε * kkE x) (Fin.cons t v)
  have hC := norm_kkDs_cons_ge (A := kkM c a b x) (δ := ε * kkE x) hε (by nlinarith) t v
    (show R + kkM c a b x ≤ B₁ by linarith) hB₁
  set κ := ε / (1 + B₁ + ε)
  have hκ : 0 < κ := by positivity
  have hCge : κ * (1 + t ^ 2) ≤ ‖C‖ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  have hpow : (κ * (1 + t ^ 2)) ^ 5 ≤ ‖C‖ ^ 5 := pow_le_pow_left₀ (by positivity) hCge 5
  have hs : ‖(Minkowski.dot (Fin.cons t v : Fin 4 → ℝ) (Fin.cons t v) : ℂ)‖ ≤
      (1 + R) * (1 + t ^ 2) := by
    rw [QED.TwoLoop.CountertermLimit.dot_cons_self, Complex.norm_real, Real.norm_eq_abs,
      abs_le]
    constructor <;> nlinarith [sq_nonneg t]
  have hpos : 0 < (κ * (1 + t ^ 2)) ^ 5 := by positivity
  calc ‖kkG c a b ε v t x‖ = ‖(Minkowski.dot (Fin.cons t v : Fin 4 → ℝ) (Fin.cons t v) : ℂ)‖ *
        (‖C‖ ^ 5)⁻¹ := by rw [kkG, norm_mul, norm_inv, norm_pow]
    _ ≤ (1 + R) * (1 + t ^ 2) * ((κ * (1 + t ^ 2)) ^ 5)⁻¹ :=
        mul_le_mul hs (inv_anti₀ hpos hpow) (by positivity) (by positivity)
    _ = (1 + R) * κ ^ (-5 : ℤ) * ((1 + t ^ 2) ^ 4)⁻¹ := by
        rw [zpow_neg, zpow_ofNat]
        field_simp

/-- **The energy integral of `kkScl` at fixed spatial momentum**, after Feynman
parametrization and the exchange of the energy and simplex integrals. -/
theorem integral_kkScl_cons {mγ Λ τ ε : ℝ} (hτ : 0 < τ) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (hε : 0 < ε) (v : Fin 3 → ℝ) :
    ∫ t : ℝ, kkScl mγ Λ τ ε (Fin.cons t v) =
      96 * ∫ x in simplexSet 4, kkPhi (4 * τ ^ 2) (mγ ^ 2) (Λ ^ 2) ε x v := by
  have hc : 0 < 4 * τ ^ 2 := by positivity
  have ha : 0 < mγ ^ 2 := by positivity
  have hb : 0 < Λ ^ 2 := by positivity
  have := isFiniteMeasure_simplex
  have hae : ∀ᵐ p ∂((volume : Measure ℝ).prod (volume.restrict (simplexSet 4))),
      p ∈ univ ×ˢ simplexSet 4 := by
    rw [← Measure.restrict_univ (μ := (volume : Measure ℝ)), Measure.prod_restrict]
    exact ae_restrict_mem (MeasurableSet.univ.prod (measurableSet_simplexSet 4))
  have hint : Integrable (Function.uncurry (kkG (4 * τ ^ 2) (mγ ^ 2) (Λ ^ 2) ε v))
      ((volume : Measure ℝ).prod (volume.restrict (simplexSet 4))) := by
    refine Integrable.mono' ((((integrable_inv_one_add_sq_pow 4 (by norm_num)).const_mul
      ((1 + ∑ k, v k ^ 2) * (ε / (1 + (∑ k, v k ^ 2 + (4 * τ ^ 2 + mγ ^ 2 + Λ ^ 2)) + ε)) ^
        (-5 : ℤ))).mul_prod (integrable_const (1 : ℝ))))
      (measurable_kkG _ _ _ _ v).aestronglyMeasurable ?_
    filter_upwards [hae] with p hp
    rw [mul_one]
    exact norm_kkG_le hc ha hb hε v p.1 hp.2
  simp_rw [kkScl_eq_feyn hε]
  rw [integral_const_mul]
  congr 1
  have hswap := integral_integral_swap hint
  simp only [kkG] at hswap
  rw [hswap]
  exact setIntegral_congr_fun (measurableSet_simplexSet 4) fun x hx => integral_feyn_energy hε hx v

end QED.ChainProof.SetCRegDisp
