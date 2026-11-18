/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCtMerge
public import QED.Integration.ChengWu
public import QED.Integration.SimplexMergePV
public import QED.Integration.SymanzikIntegrability
public import QED.Integration.TwoLoopParametric
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The parametric integral of the `δ₂, δ_m` counterterm classes

Section 5.2 of `docs/TWO-LOOP-UNITS.md`, the `δ₂, δ_m` half of the unit `S`, integration stage.
The second-order (`q² → 0`) coefficient of the product data of the `δ₂, δ_m` classes, divided by
`V⁴`, is (at `m = 1`, `docs` normalization, see `QED/TwoLoop/UnitSCCtAssembly.lean`) of the form

`ctG(z) = (f(ξ)/V⁴ + h(ξ)/(X₁ V³)) / (X₁² X₂²)`

on the eight Feynman parameters `z` (outgoing electron `z₀`, doubled incoming electron `z₁, z₂`,
photon pair `z₃` (squared mass `a`), `z₄` (squared mass `b`), auxiliary loop `z₅, z₆, z₇`), with
`X₁ = z₀ + ⋯ + z₄`, `X₂ = z₅ + z₆ + z₇` (`U = X₁ X₂`), `e = z₀ + z₁ + z₂`, `ξ = e/X₁` and
`V = a z₃ + b z₄ + X₂ + e²/X₁` (the second Symanzik function at `q = 0`). This file proves, for
continuous `f, h` and distinct `a, b > 0` (`integral_ctG`):

`∫_{Δ₇} ctG = ∫₀¹ x²/4 · (f(x) (M_b⁻² - M_a⁻²)/(6(a - b)) + h(x) (M_b⁻¹ - M_a⁻¹)/(2(a - b))) dx`,

`M_μ(x) = x² + (1 - x) μ`, and the integrand is integrable on `Δ₇`.

## Proof

* integrability: `V ≥ min(a, b, 1)/4` and `|ctG| ≤ C/(X₁³ X₂²) ≤ C ∏ zᵢ^{-3/4}`;
* merging (`QED/TwoLoop/UnitSCCtMerge.lean`) of the groups `e`, `T = X₂`, `r = z₃ + z₄`: the
  integrand depends on the splits only through the photon split `t`, with `V` affine in `t`, so
  the merged integrand is `(e²/2)(T²/2) ∫₀^r ctG dt`, the photon split giving the divided
  difference (`QED.Integration.SimplexMerge.integral_inv_pow_four_affine`) (`ctMerged_ctG`);
* the result `ctH` is homogeneous of degree `-3` on `ℝ³`; the Cheng–Wu theorem with the
  constraint `e + r = 1` gives `x = e ∈ (0, 1)`, `T ∈ (0, ∞)`, and `X₁ = 1`, `V = M_μ(x) + T`;
* the `T`-integrals `∫₀^∞ (M + T)^{-k-1} dT = 1/(k M^k)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace QED.TwoLoop.UnitSCCt

open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet)
open QED.Integration.ChengWu (chengWuSet openSimplex integral_simplex_chengWu
  integrableOn_simplex_chengWu_iff measurableSet_chengWuSet)
open QED.Integration.SimplexMerge

/-! ### The integrand -/

/-- The electron group `e = z₀ + z₁ + z₂`. -/
def ctE (z : Fin 8 → ℝ) : ℝ := z 0 + z 1 + z 2

/-- The first loop `X₁ = z₀ + ⋯ + z₄`. -/
def ctX1 (z : Fin 8 → ℝ) : ℝ := z 0 + z 1 + z 2 + z 3 + z 4

/-- The auxiliary loop `X₂ = z₅ + z₆ + z₇`. -/
def ctX2 (z : Fin 8 → ℝ) : ℝ := z 5 + z 6 + z 7

/-- The second Symanzik function at `q = 0`: `V = a z₃ + b z₄ + X₂ + e²/X₁`. -/
noncomputable def ctV (a b : ℝ) (z : Fin 8 → ℝ) : ℝ :=
  z 3 * a + z 4 * b + ctX2 z + ctE z ^ 2 / ctX1 z

/-- **The integrand** `(f(ξ)/V⁴ + h(ξ)/(X₁ V³)) / (X₁² X₂²)`, `ξ = e/X₁`. -/
noncomputable def ctG (f h : ℝ → ℝ) (a b : ℝ) (z : Fin 8 → ℝ) : ℝ :=
  (f (ctE z / ctX1 z) / ctV a b z ^ 4 + h (ctE z / ctX1 z) / (ctX1 z * ctV a b z ^ 3)) /
    (ctX1 z ^ 2 * ctX2 z ^ 2)

/-! ### Integrability -/

theorem simplexPoint_pos_of_mem_openSimplex' {m : ℕ} {x : Fin m → ℝ}
    (hx : x ∈ openSimplex m) : ∀ i, 0 < simplexPoint x i := by
  intro i
  induction i using Fin.lastCases with
  | last =>
    rw [QED.Integration.TwoLoop.simplexPoint_last]
    linarith [(QED.Integration.ChengWu.mem_openSimplex.mp hx).2]
  | cast j =>
    rw [QED.Integration.TwoLoop.simplexPoint_castSucc]
    exact (QED.Integration.ChengWu.mem_openSimplex.mp hx).1 j

theorem ae_mem_openSimplex' {m : ℕ} (hm : 0 < m) :
    ∀ᵐ x ∂(volume.restrict (simplexSet m)), x ∈ openSimplex m := by
  have h := QED.Integration.ChengWu.simplexSet_ae_eq_openSimplex (⟨0, hm⟩ : Fin m)
  filter_upwards [ae_restrict_mem (measurableSet_simplexSet m),
    ae_restrict_of_ae h] with x hx hx'
  exact (hx'.mp hx : _)

theorem sum_simplexPoint {m : ℕ} (x : Fin m → ℝ) : ∑ i, simplexPoint x i = 1 := by
  simp only [Fin.sum_univ_castSucc, QED.Integration.TwoLoop.simplexPoint_castSucc,
    QED.Integration.TwoLoop.simplexPoint_last]
  ring

theorem measurable_ctG {f h : ℝ → ℝ} (hf : Measurable f) (hh : Measurable h) (a b : ℝ) :
    Measurable (ctG f h a b) := by
  unfold ctG ctV ctE ctX1 ctX2
  fun_prop

/-- **The lower bound** `V ≥ μ₀/4`, `μ₀ = min(a, b, 1)`, on the simplex. -/
theorem le_ctV {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {z : Fin 8 → ℝ} (hz : ∀ i, 0 < z i)
    (hz1 : ∑ i, z i = 1) : min a (min b 1) / 4 ≤ ctV a b z := by
  set μ := min a (min b 1)
  have hμa : μ ≤ a := min_le_left _ _
  have hμb : μ ≤ b := le_trans (min_le_right _ _) (min_le_left _ _)
  have hμ1 : μ ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hμ0 : 0 < μ := lt_min ha (lt_min hb one_pos)
  rw [Fin.sum_univ_eight] at hz1
  have h0 := hz 0; have h1 := hz 1; have h2 := hz 2; have h3 := hz 3
  have h4 := hz 4; have h5 := hz 5; have h6 := hz 6; have h7 := hz 7
  have hX1 : 0 < ctX1 z := by unfold ctX1; positivity
  have hX1le : ctX1 z ≤ 1 := by unfold ctX1; linarith
  have he : ctE z ^ 2 ≤ ctE z ^ 2 / ctX1 z := by
    rw [le_div_iff₀ hX1]
    nlinarith [sq_nonneg (ctE z)]
  have e1 : z 3 * μ ≤ z 3 * a := mul_le_mul_of_nonneg_left hμa h3.le
  have e2 : z 4 * μ ≤ z 4 * b := mul_le_mul_of_nonneg_left hμb h4.le
  have e3 : ctX2 z * μ ≤ ctX2 z := by
    have : 0 ≤ ctX2 z := by unfold ctX2; positivity
    nlinarith
  have hsum : z 3 + z 4 + ctX2 z = 1 - ctE z := by unfold ctX2 ctE; linarith
  have key : μ / 4 ≤ μ * (1 - ctE z) + ctE z ^ 2 := by
    nlinarith [sq_nonneg (ctE z - μ / 2)]
  unfold ctV
  nlinarith

theorem prod_pow_three_le {z : Fin 8 → ℝ} (hz : ∀ i, 0 < z i) (hz1 : ∑ i, z i = 1) :
    (∏ i, z i) ^ 3 ≤ (ctX1 z ^ 3 * ctX2 z ^ 2) ^ 4 := by
  rw [Fin.sum_univ_eight] at hz1
  have h0 := hz 0; have h1 := hz 1; have h2 := hz 2; have h3 := hz 3
  have h4 := hz 4; have h5 := hz 5; have h6 := hz 6; have h7 := hz 7
  have hX1 : 0 < ctX1 z := by unfold ctX1; positivity
  have hX2 : 0 < ctX2 z := by unfold ctX2; positivity
  have hX11 : ctX1 z ≤ 1 := by unfold ctX1; linarith
  have hX21 : ctX2 z ≤ 1 := by unfold ctX2; linarith
  have l0 : z 0 ≤ ctX1 z := by unfold ctX1; linarith
  have l1 : z 1 ≤ ctX1 z := by unfold ctX1; linarith
  have l2 : z 2 ≤ ctX1 z := by unfold ctX1; linarith
  have l3 : z 3 ≤ ctX1 z := by unfold ctX1; linarith
  have l4 : z 4 ≤ ctX1 z := by unfold ctX1; linarith
  have l5 : z 5 ≤ ctX2 z := by unfold ctX2; linarith
  have l6 : z 6 ≤ ctX2 z := by unfold ctX2; linarith
  have l7 : z 7 ≤ ctX2 z := by unfold ctX2; linarith
  have hP : ∏ i, z i ≤ ctX1 z ^ 5 * ctX2 z ^ 3 := by
    rw [Fin.prod_univ_eight]
    calc z 0 * z 1 * z 2 * z 3 * z 4 * z 5 * z 6 * z 7
        ≤ ctX1 z * ctX1 z * ctX1 z * ctX1 z * ctX1 z * ctX2 z * ctX2 z * ctX2 z := by gcongr
      _ = ctX1 z ^ 5 * ctX2 z ^ 3 := by ring
  have hP0 : 0 ≤ ∏ i, z i := Finset.prod_nonneg fun i _ => (hz i).le
  have q1 : ctX1 z ^ 15 ≤ ctX1 z ^ 12 := pow_le_pow_of_le_one hX1.le hX11 (by norm_num)
  have q2 : ctX2 z ^ 9 ≤ ctX2 z ^ 8 := pow_le_pow_of_le_one hX2.le hX21 (by norm_num)
  calc (∏ i, z i) ^ 3 ≤ (ctX1 z ^ 5 * ctX2 z ^ 3) ^ 3 := by gcongr
    _ = ctX1 z ^ 15 * ctX2 z ^ 9 := by ring
    _ ≤ ctX1 z ^ 12 * ctX2 z ^ 8 := by gcongr
    _ = (ctX1 z ^ 3 * ctX2 z ^ 2) ^ 4 := by ring

/-- `1/(X₁³ X₂²) ≤ ∏ᵢ zᵢ^{-3/4}` on the open simplex. -/
theorem inv_le_prod_rpow {z : Fin 8 → ℝ} (hz : ∀ i, 0 < z i) (hz1 : ∑ i, z i = 1) :
    (ctX1 z ^ 3 * ctX2 z ^ 2)⁻¹ ≤ ∏ i, z i ^ (-(3 / 4 : ℝ)) := by
  have hz' : ∀ i, 0 ≤ z i := fun i => (hz i).le
  have hP : 0 < ∏ i, z i := Finset.prod_pos fun i _ => hz i
  have hX1 : 0 < ctX1 z := by
    unfold ctX1; have := hz 0; have := hz 1; have := hz 2; have := hz 3; have := hz 4
    positivity
  have hX2 : 0 < ctX2 z := by unfold ctX2; have := hz 5; have := hz 6; have := hz 7; positivity
  rw [Real.finsetProd_rpow _ _ (fun i _ => hz' i)]
  set p := ∏ i, z i
  have hq : 0 < p ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hP _
  have key : p ^ (3 / 4 : ℝ) ≤ ctX1 z ^ 3 * ctX2 z ^ 2 := by
    have h4 : (p ^ (3 / 4 : ℝ)) ^ 4 ≤ (ctX1 z ^ 3 * ctX2 z ^ 2) ^ 4 := by
      have e : (p ^ (3 / 4 : ℝ)) ^ 4 = p ^ 3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hP.le]
        norm_num
      rw [e]
      exact prod_pow_three_le hz hz1
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h4
  rw [Real.rpow_neg hP.le]
  exact inv_anti₀ hq key

/-- **The integrand is integrable on the simplex** (continuous `f, h`, `a, b > 0`). -/
theorem integrableOn_ctG {f h : ℝ → ℝ} (hf : Continuous f) (hh : Continuous h) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun x => ctG f h a b (simplexPoint x)) (simplexSet 7) := by
  obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.continuousOn : ContinuousOn f (Icc (0 : ℝ) 1))
  obtain ⟨Ch, hCh⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hh.continuousOn : ContinuousOn h (Icc (0 : ℝ) 1))
  set v₀ : ℝ := min a (min b 1) / 4
  have hv₀ : 0 < v₀ := by have := lt_min ha (lt_min hb one_pos); positivity
  set C : ℝ := |Cf| / v₀ ^ 4 + |Ch| / v₀ ^ 3
  have hint : IntegrableOn (fun x => C * ∏ i ∈ Finset.univ, simplexPoint x i ^ (-(3 / 4 : ℝ)))
      (simplexSet 7) :=
    (QED.Integration.TwoLoop.integrableOn_prod_simplexPoint_rpow Finset.univ (by norm_num)
      (by norm_num)).const_mul C
  refine hint.mono' ((measurable_ctG hf.measurable hh.measurable a b).comp
    QED.Integration.TwoLoop.continuous_simplexPoint'.measurable).aestronglyMeasurable ?_
  filter_upwards [ae_mem_openSimplex' (by norm_num : 0 < 7)] with x hx
  set z := simplexPoint x
  have hz := simplexPoint_pos_of_mem_openSimplex' hx
  have hz1 : ∑ i, z i = 1 := sum_simplexPoint x
  have hV := le_ctV ha hb hz hz1
  have hz1' := hz1
  rw [Fin.sum_univ_eight] at hz1'
  have h0 := hz 0; have h1 := hz 1; have h2 := hz 2; have h3 := hz 3
  have h4 := hz 4; have h5 := hz 5; have h6 := hz 6; have h7 := hz 7
  have hX1 : 0 < ctX1 z := by unfold ctX1; positivity
  have hX2 : 0 < ctX2 z := by unfold ctX2; positivity
  have hX11 : ctX1 z ≤ 1 := by unfold ctX1; linarith
  have hVp : 0 < ctV a b z := lt_of_lt_of_le hv₀ hV
  have hξ : ctE z / ctX1 z ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by unfold ctE; positivity, (div_le_one hX1).mpr ?_⟩
    unfold ctE ctX1; linarith
  have bf : |f (ctE z / ctX1 z)| ≤ |Cf| := (hCf _ hξ).trans (le_abs_self _)
  have bh : |h (ctE z / ctX1 z)| ≤ |Ch| := (hCh _ hξ).trans (le_abs_self _)
  have t1 : |f (ctE z / ctX1 z) / ctV a b z ^ 4| ≤ |Cf| / v₀ ^ 4 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < ctV a b z ^ 4)]
    exact div_le_div₀ (abs_nonneg _) bf (by positivity) (pow_le_pow_left₀ hv₀.le hV 4)
  have t2 : |h (ctE z / ctX1 z) / (ctX1 z * ctV a b z ^ 3)| ≤ |Ch| / v₀ ^ 3 / ctX1 z := by
    rw [abs_div, abs_of_pos (by positivity : 0 < ctX1 z * ctV a b z ^ 3), div_div,
      mul_comm (v₀ ^ 3)]
    exact div_le_div₀ (abs_nonneg _) bh (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv₀.le hV 3) hX1.le)
  have t3 : |Cf| / v₀ ^ 4 ≤ |Cf| / v₀ ^ 4 / ctX1 z := by
    rw [le_div_iff₀ hX1]
    exact mul_le_of_le_one_right (by positivity) hX11
  have hnum : |f (ctE z / ctX1 z) / ctV a b z ^ 4 + h (ctE z / ctX1 z) / (ctX1 z * ctV a b z ^ 3)|
      ≤ C / ctX1 z := by
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ |Cf| / v₀ ^ 4 / ctX1 z + |Ch| / v₀ ^ 3 / ctX1 z := add_le_add (t1.trans t3) t2
      _ = C / ctX1 z := by simp only [C]; ring
  rw [Real.norm_eq_abs]
  unfold ctG
  rw [abs_div, abs_of_pos (by positivity : 0 < ctX1 z ^ 2 * ctX2 z ^ 2)]
  calc _ ≤ C / ctX1 z / (ctX1 z ^ 2 * ctX2 z ^ 2) := div_le_div_of_nonneg_right hnum (by positivity)
    _ = C * (ctX1 z ^ 3 * ctX2 z ^ 2)⁻¹ := by field_simp
    _ ≤ C * ∏ i ∈ Finset.univ, z i ^ (-(3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (inv_le_prod_rpow hz hz1) (by positivity)

/-! ### The merged integrand -/

/-- **The integrand on `Δ₂` after the merges**, at `w = (e, T, r)`: with `X = e + r`,
`ξ = e/X`, `K_μ = r μ + T + e²/X`,
`(e²/(4X²)) (f(ξ) (K_b⁻³ - K_a⁻³)/(3(a - b)) + (h(ξ)/X) (K_b⁻² - K_a⁻²)/(2(a - b)))`. -/
noncomputable def ctH (f h : ℝ → ℝ) (a b : ℝ) (w : Fin 3 → ℝ) : ℝ :=
  w 0 ^ 2 / 4 / (w 0 + w 2) ^ 2 *
    (f (w 0 / (w 0 + w 2)) *
        (((w 2 * b + w 1 + w 0 ^ 2 / (w 0 + w 2)) ^ 3)⁻¹ -
          ((w 2 * a + w 1 + w 0 ^ 2 / (w 0 + w 2)) ^ 3)⁻¹) / (3 * (a - b)) +
      h (w 0 / (w 0 + w 2)) / (w 0 + w 2) *
        (((w 2 * b + w 1 + w 0 ^ 2 / (w 0 + w 2)) ^ 2)⁻¹ -
          ((w 2 * a + w 1 + w 0 ^ 2 / (w 0 + w 2)) ^ 2)⁻¹) / (2 * (a - b)))

/-- The integrand at the split point depends only on the photon split `t₄`. -/
theorem ctG_ctSplit (f h : ℝ → ℝ) (a b : ℝ) (w : Fin 3 → ℝ) (t₅ t₄ t₃ t₂ t₁ : ℝ) :
    ctG f h a b (ctSplit w t₅ t₄ t₃ t₂ t₁) =
      (f (w 0 / (w 0 + w 2)) *
          (((w 2 * b + w 1 + w 0 ^ 2 / (w 0 + w 2)) + (a - b) * t₄) ^ 4)⁻¹ +
        h (w 0 / (w 0 + w 2)) / (w 0 + w 2) *
          (((w 2 * b + w 1 + w 0 ^ 2 / (w 0 + w 2)) + (a - b) * t₄) ^ 3)⁻¹) /
        ((w 0 + w 2) ^ 2 * w 1 ^ 2) := by
  have hE : ctE (ctSplit w t₅ t₄ t₃ t₂ t₁) = w 0 := by simp [ctE, ctSplit]
  have hX1 : ctX1 (ctSplit w t₅ t₄ t₃ t₂ t₁) = w 0 + w 2 := by simp [ctX1, ctSplit]
  have hX2 : ctX2 (ctSplit w t₅ t₄ t₃ t₂ t₁) = w 1 := by simp [ctX2, ctSplit]
  have hV : ctV a b (ctSplit w t₅ t₄ t₃ t₂ t₁) =
      (w 2 * b + w 1 + w 0 ^ 2 / (w 0 + w 2)) + (a - b) * t₄ := by
    unfold ctV
    rw [hE, hX1, hX2]
    simp [ctSplit]
    ring
  unfold ctG
  rw [hE, hX1, hX2, hV]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem integral_sub_mul_const (c K : ℝ) : ∫ t in (0 : ℝ)..c, (c - t) * K = c ^ 2 / 2 * K := by
  rw [intervalIntegral.integral_mul_const]
  congr 1
  simp only [intervalIntegral.integral_sub intervalIntegrable_const
    intervalIntegral.intervalIntegrable_id, integral_id, intervalIntegral.integral_const,
    smul_eq_mul]
  ring

/-- The iterated integral of a function of `t₄` only. -/
theorem iterated_eval (G : ℝ → ℝ) (A B C : ℝ) :
    (∫ t₅ in (0 : ℝ)..A, ∫ t₄ in (0 : ℝ)..C, ∫ t₃ in (0 : ℝ)..B,
      ∫ _t₂ in (0 : ℝ)..(B - t₃), ∫ _t₁ in (0 : ℝ)..(A - t₅), G t₄) =
      A ^ 2 / 2 * (B ^ 2 / 2 * ∫ t₄ in (0 : ℝ)..C, G t₄) := by
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have h3 : ∀ t₅ t₄ : ℝ, ∫ t₃ in (0 : ℝ)..B, (B - t₃) * ((A - t₅) * G t₄) =
      (B ^ 2 / 2 * (A - t₅)) * G t₄ := fun t₅ t₄ => by
    rw [integral_sub_mul_const]; ring
  simp only [h3, intervalIntegral.integral_const_mul]
  have h5 : ∫ t₅ in (0 : ℝ)..A, B ^ 2 / 2 * (A - t₅) * ∫ t₄ in (0 : ℝ)..C, G t₄ =
      ∫ t₅ in (0 : ℝ)..A, (A - t₅) * (B ^ 2 / 2 * ∫ t₄ in (0 : ℝ)..C, G t₄) := by
    congr 1; funext t₅; ring
  rw [h5, integral_sub_mul_const]

/-- **The merged integrand** at a positive point of `ℝ³`. -/
theorem ctMerged_ctG {f h : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    {w : Fin 3 → ℝ} (hw0 : 0 < w 0) (hw1 : 0 < w 1) (hw2 : 0 < w 2) :
    ctMerged (ctG f h a b) w = ctH f h a b w := by
  set X := w 0 + w 2 with hX
  have hX0 : 0 < X := by positivity
  set K := w 2 * b + w 1 + w 0 ^ 2 / X with hK
  have hK0 : 0 < K := by positivity
  have hKw : 0 < K + (a - b) * w 2 := by
    have : K + (a - b) * w 2 = w 2 * a + w 1 + w 0 ^ 2 / X := by rw [hK]; ring
    rw [this]; positivity
  have hβ : a - b ≠ 0 := sub_ne_zero.mpr hab
  unfold ctMerged
  simp only [ctG_ctSplit]
  rw [iterated_eval]
  have i4 := intervalIntegrable_inv_pow_affine 4 hK0 hKw (β := a - b)
  have i3 := intervalIntegrable_inv_pow_affine 3 hK0 hKw (β := a - b)
  have hint : ∫ t₄ in (0 : ℝ)..w 2, (f (w 0 / X) * ((K + (a - b) * t₄) ^ 4)⁻¹ +
      h (w 0 / X) / X * ((K + (a - b) * t₄) ^ 3)⁻¹) / (X ^ 2 * w 1 ^ 2) =
      (f (w 0 / X) * (((K ^ 3)⁻¹ - ((K + (a - b) * w 2) ^ 3)⁻¹) / (3 * (a - b))) +
        h (w 0 / X) / X * (((K ^ 2)⁻¹ - ((K + (a - b) * w 2) ^ 2)⁻¹) / (2 * (a - b)))) /
        (X ^ 2 * w 1 ^ 2) := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add (i4.const_mul _)
      (i3.const_mul _), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_inv_pow_four_affine hβ hK0 hKw, integral_inv_pow_three_affine hβ hK0 hKw]
  rw [hint]
  have hK' : K + (a - b) * w 2 = w 2 * a + w 1 + w 0 ^ 2 / X := by rw [hK]; ring
  rw [hK']
  unfold ctH
  rw [← hX, ← hK]
  have := hw1.ne'
  field_simp
  ring

/-! ### Homogeneity and the Cheng–Wu frame -/

/-- **`ctH` is homogeneous of degree `-3`** on the positive orthant. -/
theorem ctH_smul (f h : ℝ → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    {w : Fin 3 → ℝ} (hw : ∀ i, 0 < w i) {t : ℝ} (ht : 0 < t) :
    ctH f h a b (t • w) = (t ^ 3)⁻¹ * ctH f h a b w := by
  have h0 := hw 0; have h1 := hw 1; have h2 := hw 2
  set X := w 0 + w 2 with hX
  have hX0 : 0 < X := by positivity
  set Kb := w 2 * b + w 1 + w 0 ^ 2 / X with hKb
  set Ka := w 2 * a + w 1 + w 0 ^ 2 / X with hKa
  have hKb0 : 0 < Kb := by positivity
  have hKa0 : 0 < Ka := by positivity
  have eX : t * w 0 + t * w 2 = t * X := by rw [hX]; ring
  have eξ : t * w 0 / (t * X) = w 0 / X := mul_div_mul_left _ _ ht.ne'
  have eb : t * w 2 * b + t * w 1 + (t * w 0) ^ 2 / (t * X) = t * Kb := by
    rw [hKb]; field_simp
  have ea : t * w 2 * a + t * w 1 + (t * w 0) ^ 2 / (t * X) = t * Ka := by
    rw [hKa]; field_simp
  unfold ctH
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [eX, eξ, eb, ea, ← hX, ← hKb, ← hKa]
  have hβ : a - b ≠ 0 := sub_ne_zero.mpr hab
  have := ht.ne'
  have := hX0.ne'
  have := hKb0.ne'
  have := hKa0.ne'
  field_simp

/-- In the Cheng–Wu frame `e + r = 1`, `X = 1`: `ctH` at `(x, T, 1 - x)`. -/
theorem ctH_frame (f h : ℝ → ℝ) (a b x T : ℝ) :
    ctH f h a b (Fin.snoc ![x, T] (1 - x)) =
      x ^ 2 / 4 * (f x * ((((x ^ 2 + (1 - x) * b) + T) ^ 3)⁻¹ -
          (((x ^ 2 + (1 - x) * a) + T) ^ 3)⁻¹) / (3 * (a - b)) +
        h x * ((((x ^ 2 + (1 - x) * b) + T) ^ 2)⁻¹ -
          (((x ^ 2 + (1 - x) * a) + T) ^ 2)⁻¹) / (2 * (a - b))) := by
  have s0 : (Fin.snoc ![x, T] (1 - x) : Fin 3 → ℝ) 0 = x := rfl
  have s1 : (Fin.snoc ![x, T] (1 - x) : Fin 3 → ℝ) 1 = T := rfl
  have s2 : (Fin.snoc ![x, T] (1 - x) : Fin 3 → ℝ) 2 = 1 - x := rfl
  have e1 : x + (1 - x) = 1 := by ring
  unfold ctH
  rw [s0, s1, s2, e1]
  simp only [div_one, one_pow]
  ring_nf

/-- **Fubini on the two-dimensional Cheng–Wu domain** `{0 < w₀ < 1, w₁ > 0}`. -/
theorem integral_chengWuSet_zero_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (Fin 2 → ℝ) → E} (hg : IntegrableOn g (chengWuSet (0 : Fin 2))) :
    ∫ w in chengWuSet (0 : Fin 2), g w = ∫ x in Ioo (0 : ℝ) 1, ∫ T in Ioi (0 : ℝ), g ![x, T] := by
  have hvol : (volume : Measure (Fin 2 → ℝ)) = Measure.pi fun _ => volume := rfl
  have he := (measurePreserving_finTwoArrow (volume : Measure ℝ)).symm
  have h1 := he.setIntegral_preimage_emb MeasurableEquiv.finTwoArrow.symm.measurableEmbedding g
    (chengWuSet 0)
  rw [hvol] at hg
  have hint := (he.integrableOn_comp_preimage
    MeasurableEquiv.finTwoArrow.symm.measurableEmbedding).mpr hg
  have hsymm : ∀ q : ℝ × ℝ, MeasurableEquiv.finTwoArrow.symm q = ![q.1, q.2] := fun q => by
    funext i; fin_cases i <;> rfl
  have hpre : MeasurableEquiv.finTwoArrow.symm ⁻¹' chengWuSet (0 : Fin 2) =
      Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ) := by
    ext q
    simp only [Set.mem_preimage, hsymm, QED.Integration.ChengWu.mem_chengWuSet, Fin.forall_fin_two,
      Set.mem_prod, Set.mem_Ioo, Set.mem_Ioi, Matrix.cons_val_zero, Matrix.cons_val_one]
    tauto
  rw [hpre] at h1 hint
  rw [hvol, ← h1, setIntegral_prod (fun q => g (MeasurableEquiv.finTwoArrow.symm q)) hint]
  simp only [hsymm]

/-! ### The `T`-integrals -/

theorem integral_Ioi_inv_pow_add {M : ℝ} (hM : 0 < M) (n : ℕ) :
    IntegrableOn (fun T => (((M + T) ^ (n + 2))⁻¹ : ℝ)) (Ioi 0) ∧
      ∫ T in Ioi (0 : ℝ), ((M + T) ^ (n + 2))⁻¹ = ((n + 1) * M ^ (n + 1))⁻¹ := by
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  set g : ℝ → ℝ := fun T => -((M + T) ^ (n + 1))⁻¹ / (n + 1)
  have hderiv : ∀ T ∈ Ici (0 : ℝ), HasDerivAt g (((M + T) ^ (n + 2))⁻¹) T := by
    intro T hT
    have hpos : 0 < M + T := by have := mem_Ici.mp hT; linarith
    have hlin : HasDerivAt (fun T => M + T) 1 T := by
      simpa using (hasDerivAt_id T).const_add M
    have hd := ((hlin.pow (n + 1)).inv (pow_ne_zero _ hpos.ne')).neg.div_const ((n : ℝ) + 1)
    refine hd.congr_deriv ?_
    have hp : M + T ≠ 0 := hpos.ne'
    simp only [Pi.pow_apply, Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  have hpos : ∀ T ∈ Ioi (0 : ℝ), 0 ≤ ((M + T) ^ (n + 2))⁻¹ := fun T hT => by
    have : 0 < M + T := by have := mem_Ioi.mp hT; linarith
    positivity
  have hlim : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => M + T) atTop atTop := tendsto_atTop_add_const_left _ M tendsto_id
    have h2 := (tendsto_pow_atTop (n := n + 1) (by omega)).comp h1
    have h3 := (tendsto_inv_atTop_zero.comp h2).neg.div_const ((n : ℝ) + 1)
    simpa [g, Function.comp_def] using h3
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim]
  simp only [g, add_zero]
  field_simp
  ring

/-- **The `T`-integral at fixed `x`.** -/
theorem integral_ctH_frame (f h : ℝ → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∫ T in Ioi (0 : ℝ), ctH f h a b (Fin.snoc ![x, T] (1 - x)) =
      x ^ 2 / 4 * (f x * (((x ^ 2 + (1 - x) * b) ^ 2)⁻¹ - ((x ^ 2 + (1 - x) * a) ^ 2)⁻¹) /
          (6 * (a - b)) +
        h x * ((x ^ 2 + (1 - x) * b)⁻¹ - (x ^ 2 + (1 - x) * a)⁻¹) / (2 * (a - b))) := by
  have h1x : 0 < 1 - x := by linarith [hx.2]
  have hMa : 0 < x ^ 2 + (1 - x) * a := by have := hx.1; positivity
  have hMb : 0 < x ^ 2 + (1 - x) * b := by have := hx.1; positivity
  obtain ⟨ia3, ea3⟩ := integral_Ioi_inv_pow_add hMa 1
  obtain ⟨ib3, eb3⟩ := integral_Ioi_inv_pow_add hMb 1
  obtain ⟨ia2, ea2⟩ := integral_Ioi_inv_pow_add hMa 0
  obtain ⟨ib2, eb2⟩ := integral_Ioi_inv_pow_add hMb 0
  norm_num at ea3 eb3 ea2 eb2 ia3 ib3 ia2 ib2
  simp only [ctH_frame]
  set c₁ := x ^ 2 / 4 * f x / (3 * (a - b))
  set c₂ := x ^ 2 / 4 * h x / (2 * (a - b))
  have e : ∀ T : ℝ, x ^ 2 / 4 * (f x * ((((x ^ 2 + (1 - x) * b) + T) ^ 3)⁻¹ -
      (((x ^ 2 + (1 - x) * a) + T) ^ 3)⁻¹) / (3 * (a - b)) +
      h x * ((((x ^ 2 + (1 - x) * b) + T) ^ 2)⁻¹ -
        (((x ^ 2 + (1 - x) * a) + T) ^ 2)⁻¹) / (2 * (a - b))) =
      (c₁ * (((x ^ 2 + (1 - x) * b) + T) ^ 3)⁻¹ - c₁ * (((x ^ 2 + (1 - x) * a) + T) ^ 3)⁻¹) +
        (c₂ * (((x ^ 2 + (1 - x) * b) + T) ^ 2)⁻¹ -
          c₂ * (((x ^ 2 + (1 - x) * a) + T) ^ 2)⁻¹) := fun T => by
    simp only [c₁, c₂]; ring
  simp only [e]
  have j1 : IntegrableOn (fun T => c₁ * (((x ^ 2 + (1 - x) * b) + T) ^ 3)⁻¹ -
      c₁ * (((x ^ 2 + (1 - x) * a) + T) ^ 3)⁻¹) (Ioi 0) :=
    (ib3.const_mul c₁).sub (ia3.const_mul c₁)
  have j2 : IntegrableOn (fun T => c₂ * (((x ^ 2 + (1 - x) * b) + T) ^ 2)⁻¹ -
      c₂ * (((x ^ 2 + (1 - x) * a) + T) ^ 2)⁻¹) (Ioi 0) :=
    (ib2.const_mul c₂).sub (ia2.const_mul c₂)
  rw [integral_add j1 j2, integral_sub (ib3.const_mul c₁) (ia3.const_mul c₁),
    integral_sub (ib2.const_mul c₂) (ia2.const_mul c₂),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, ea3, eb3, ea2,
    eb2]
  simp only [c₁, c₂, div_eq_mul_inv, mul_inv]
  ring

/-! ### The theorem -/

/-- The integrand of the final one-dimensional integral. -/
noncomputable def ctLine (f h : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  x ^ 2 / 4 * (f x * (((x ^ 2 + (1 - x) * b) ^ 2)⁻¹ - ((x ^ 2 + (1 - x) * a) ^ 2)⁻¹) /
      (6 * (a - b)) +
    h x * ((x ^ 2 + (1 - x) * b)⁻¹ - (x ^ 2 + (1 - x) * a)⁻¹) / (2 * (a - b)))

/-- **The parametric integral of the `δ₂, δ_m` classes**: for continuous `f, h` and distinct
squared photon masses `a, b > 0`, `ctG` is integrable on `Δ₇` and
`∫_{Δ₇} ctG = ∫₀¹ ctLine dx`. -/
theorem integral_ctG {f h : ℝ → ℝ} (hf : Continuous f) (hh : Continuous h) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    IntegrableOn (fun x => ctG f h a b (simplexPoint x)) (simplexSet 7) ∧
    ∫ x in simplexSet 7, ctG f h a b (simplexPoint x) = ∫ x in (0 : ℝ)..1, ctLine f h a b x := by
  have I₇ := integrableOn_ctG hf hh ha hb
  obtain ⟨I₂, e₂⟩ := integral_simplex_ctSplit I₇
  have hae : (fun y => ctMerged (ctG f h a b) (simplexPoint y)) =ᵐ[volume.restrict (simplexSet 2)]
      fun y => ctH f h a b (simplexPoint y) := by
    filter_upwards [ae_mem_openSimplex' (by norm_num : 0 < 2)] with y hy
    have hz := simplexPoint_pos_of_mem_openSimplex' hy
    exact ctMerged_ctG ha hb hab (hz 0) (hz 1) (hz 2)
  have I₂' : IntegrableOn (fun y => ctH f h a b (simplexPoint y)) (simplexSet 2) :=
    I₂.congr_fun_ae hae
  have hF : ∀ z : Fin 3 → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t →
      ctH f h a b (t • z) = (t ^ (2 + 1))⁻¹ • ctH f h a b z := fun z hz t ht => by
    rw [smul_eq_mul]; exact ctH_smul f h ha hb hab hz ht
  have hCW := integral_simplex_chengWu (0 : Fin 2) (ctH f h a b) hF
  have ICW := (integrableOn_simplex_chengWu_iff (0 : Fin 2) (ctH f h a b) hF).mp I₂'
  refine ⟨I₇, ?_⟩
  rw [e₂, integral_congr_ae hae, hCW, integral_chengWuSet_zero_two ICW,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  simp only [Matrix.cons_val_zero]
  rw [integral_ctH_frame f h ha hb hx]
  rfl

end QED.TwoLoop.UnitSCCt

end
