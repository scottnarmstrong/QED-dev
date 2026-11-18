/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXGraphReduceChengWu
public import QED.TwoLoop.HeadlineAssemblyUnits
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The crossed-ladder unit X: the joint regulator limit, given a domination

Section 8 of `docs/TWO-LOOP-UNITS.md`, item 11, for the X unit. On the 4-simplex of the merged
groups `z = (z_A, z_M, z_c, z_a, z_b)`, `16π⁴ · unitF2 X P = ∫_{Δ₄} crossedF4 P`
(`QED.TwoLoop.UnitXGraph.sixteen_pi_pow_four_mul_unitF2_X_eq_simplex`), with
`crossedF4 = T(m_γ², m_γ²) - T(m_γ², Λ²) - T(Λ², m_γ²) + T(Λ², Λ²)`, `T = crossedTerm`.
Pointwise on the open simplex, `T(m_γ², m_γ²) → T(0, 0)` as `m_γ → 0` and the three terms with
a `Λ²` tend to `0` as `Λ → ∞`, since `V ≥ Λ² z_b` or `V ≥ Λ² z_a` (`tendsto_crossedFour`).
Given a bound `|T(μ_a, μ_b)(z)| ≤ C ∏ₖ zₖ^{-s}` (`s < 1`) uniform in `μ_a, μ_b ≥ 0`
(`CrossedDom`), dominated convergence gives:

* `tendsto_integral_crossedFour`: `∫_{Δ₄} crossedF4 → ∫_{Δ₄} T(0, 0)` as
  `(m_γ, Λ) → (0⁺, ∞)` **jointly**, and `T(0, 0)` is integrable on `Δ₄`;
* `xUnitLimitOne_of_dom`: **the X link at `m = 1`** (`XUnitLimitOne`), given the domination and
  the value `∫_{Δ₄} T(0, 0) = 1/6 - 5 ζ(2) log 2 + (13/6) ζ(2) + (5/4) ζ(3)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace QED.TwoLoop.UnitXClose

open QED.WickModel QED.TwoLoop.UnitXGraph QED.TwoLoop.UnitsRegulated
open QED.Integration.Feynman (simplexSet simplexPoint)

/-- The merged integrand at photon mass `λ` and Pauli–Villars mass `Λ`
(`crossedF4 P = crossedFour P.mγ P.Λ`). -/
noncomputable def crossedFour (lam Lam : ℝ) (w : Fin 5 → ℝ) : ℝ :=
  crossedTerm (lam ^ 2) (lam ^ 2) (w 0) (w 1) (w 2) (w 3) (w 4) -
    crossedTerm (lam ^ 2) (Lam ^ 2) (w 0) (w 1) (w 2) (w 3) (w 4) -
    crossedTerm (Lam ^ 2) (lam ^ 2) (w 0) (w 1) (w 2) (w 3) (w 4) +
    crossedTerm (Lam ^ 2) (Lam ^ 2) (w 0) (w 1) (w 2) (w 3) (w 4)

theorem crossedF4_eq (P : Params) (w : Fin 5 → ℝ) : crossedF4 P w = crossedFour P.mγ P.Λ w := rfl

/-- The massless integrand `T(0, 0)`. -/
noncomputable def crossedZero (w : Fin 5 → ℝ) : ℝ :=
  crossedTerm 0 0 (w 0) (w 1) (w 2) (w 3) (w 4)

/-- **The domination hypothesis**: `|T(μ_a, μ_b)(z)| ≤ C ∏ₖ zₖ^{-s}` on the open simplex, for
some `0 ≤ s < 1`, uniformly in `μ_a, μ_b ≥ 0`. -/
def CrossedDom : Prop :=
  ∃ C s : ℝ, 0 ≤ s ∧ s < 1 ∧ ∀ μa μb : ℝ, 0 ≤ μa → 0 ≤ μb → ∀ z : Fin 5 → ℝ, (∀ k, 0 < z k) →
    ∑ k, z k = 1 → |crossedTerm μa μb (z 0) (z 1) (z 2) (z 3) (z 4)| ≤ C * ∏ k, z k ^ (-s)

/-! ### Pointwise limits -/

/-- `T = M (Ψ₁/(2U⁶) (V⁻¹)² - Ψ₂/(2U⁵) V⁻¹)`. -/
theorem crossedTerm_eq_inv (μa μb A M c a b : ℝ) :
    crossedTerm μa μb A M c a b =
      M * (gPsi1 A (M / 2) M c a b / (2 * gXU A M c a b ^ 6) *
          ((gXE A M c a b + μa * a + μb * b)⁻¹) ^ 2 -
        gPsi2 A (M / 2) M c a b / (2 * gXU A M c a b ^ 5) *
          (gXE A M c a b + μa * a + μb * b)⁻¹) := by
  unfold crossedTerm
  simp only [div_eq_mul_inv, mul_inv, inv_pow]
  ring

theorem tendsto_crossedTerm_zero_of_tendsto {ι : Type*} {l : Filter ι} {μa μb : ι → ℝ}
    {A M c a b : ℝ} (h : Tendsto (fun n => gXE A M c a b + μa n * a + μb n * b) l atTop) :
    Tendsto (fun n => crossedTerm (μa n) (μb n) A M c a b) l (𝓝 0) := by
  simp only [crossedTerm_eq_inv]
  have hi := h.inv_tendsto_atTop
  have := ((hi.pow 2).const_mul (gPsi1 A (M / 2) M c a b / (2 * gXU A M c a b ^ 6))).sub
    (hi.const_mul (gPsi2 A (M / 2) M c a b / (2 * gXU A M c a b ^ 5)))
  simpa using this.const_mul M

theorem continuous_crossedTerm_diag {A M c a b : ℝ} (hE : 0 < gXE A M c a b) :
    ContinuousWithinAt (fun lam : ℝ => crossedTerm (lam ^ 2) (lam ^ 2) A M c a b) (Ioi 0) 0 := by
  refine ContinuousAt.continuousWithinAt ?_
  simp only [crossedTerm_eq_inv]
  have hV : gXE A M c a b + (0 : ℝ) ^ 2 * a + (0 : ℝ) ^ 2 * b ≠ 0 := by simp [hE.ne']
  have hc : ContinuousAt (fun lam : ℝ => (gXE A M c a b + lam ^ 2 * a + lam ^ 2 * b)⁻¹) 0 :=
    ((by fun_prop : Continuous fun lam : ℝ =>
      gXE A M c a b + lam ^ 2 * a + lam ^ 2 * b).continuousAt).inv₀ hV
  exact continuousAt_const.mul (((continuousAt_const.mul (hc.pow 2))).sub
    (continuousAt_const.mul hc))

/-- **The pointwise joint limit**: on the open orthant, `crossedFour λ Λ z → T(0, 0)(z)` as
`(λ, Λ) → (0⁺, ∞)`. -/
theorem tendsto_crossedFour {z : Fin 5 → ℝ} (hz : ∀ k, 0 < z k) :
    Tendsto (fun p : ℝ × ℝ => crossedFour p.1 p.2 z) (𝓝[>] 0 ×ˢ atTop) (𝓝 (crossedZero z)) := by
  have hE := gXE_pos (hz 0) (hz 1) (hz 2) (hz 3) (hz 4)
  have h1 : Tendsto (fun p : ℝ × ℝ => crossedTerm (p.1 ^ 2) (p.1 ^ 2) (z 0) (z 1) (z 2) (z 3) (z 4))
      (𝓝[>] 0 ×ˢ atTop) (𝓝 (crossedZero z)) := by
    have := (continuous_crossedTerm_diag hE).tendsto
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
    exact this.comp tendsto_fst
  have hL : Tendsto (fun p : ℝ × ℝ => p.2 ^ 2) (𝓝[>] 0 ×ˢ atTop) atTop :=
    (tendsto_pow_atTop two_ne_zero).comp tendsto_snd
  have hsq : ∀ p : ℝ × ℝ, 0 ≤ p.1 ^ 2 := fun p => sq_nonneg _
  have hev : ∀ (μ : ℝ × ℝ → ℝ), (∀ p, 0 ≤ μ p) → ∀ {u v : ℝ}, 0 ≤ u → 0 < v →
      Tendsto (fun p : ℝ × ℝ => gXE (z 0) (z 1) (z 2) (z 3) (z 4) + μ p * u + p.2 ^ 2 * v)
        (𝓝[>] 0 ×ˢ atTop) atTop := by
    intro μ hμ u v hu hv
    refine tendsto_atTop_mono (fun p => ?_) ((hL.atTop_mul_const hv).atTop_add
      (tendsto_const_nhds (x := gXE (z 0) (z 1) (z 2) (z 3) (z 4))))
    have := mul_nonneg (hμ p) hu
    linarith
  have h2 : Tendsto (fun p : ℝ × ℝ => crossedTerm (p.1 ^ 2) (p.2 ^ 2) (z 0) (z 1) (z 2) (z 3) (z 4))
      (𝓝[>] 0 ×ˢ atTop) (𝓝 0) :=
    tendsto_crossedTerm_zero_of_tendsto (hev _ hsq (hz 3).le (hz 4))
  have h3 : Tendsto (fun p : ℝ × ℝ => crossedTerm (p.2 ^ 2) (p.1 ^ 2) (z 0) (z 1) (z 2) (z 3) (z 4))
      (𝓝[>] 0 ×ˢ atTop) (𝓝 0) := by
    refine tendsto_crossedTerm_zero_of_tendsto ?_
    have := hev _ hsq (hz 4).le (hz 3)
    refine this.congr fun p => ?_
    ring
  have h4 : Tendsto (fun p : ℝ × ℝ => crossedTerm (p.2 ^ 2) (p.2 ^ 2) (z 0) (z 1) (z 2) (z 3) (z 4))
      (𝓝[>] 0 ×ˢ atTop) (𝓝 0) :=
    tendsto_crossedTerm_zero_of_tendsto (hev (fun p => p.2 ^ 2) (fun p => sq_nonneg _)
      (hz 3).le (hz 4))
  have := ((h1.sub h2).sub h3).add h4
  simpa [crossedFour] using this

/-! ### Dominated convergence -/

theorem measurable_crossedTerm (μa μb : ℝ) :
    Measurable fun w : Fin 5 → ℝ => crossedTerm μa μb (w 0) (w 1) (w 2) (w 3) (w 4) := by
  unfold crossedTerm gPsi1 gPsi2 gXE gXEn psiT1h psiT2h gXan gXbn gXU
  fun_prop

theorem sum_simplexPoint (y : Fin 4 → ℝ) : ∑ k, simplexPoint y k = 1 := by
  simp only [Fin.sum_univ_castSucc, QED.Integration.TwoLoop.simplexPoint_castSucc,
    QED.Integration.TwoLoop.simplexPoint_last]
  ring

theorem simplexPoint_le_one {y : Fin 4 → ℝ} (hy : ∀ i, 0 < simplexPoint y i) (k : Fin 5) :
    simplexPoint y k ≤ 1 := by
  have h := sum_simplexPoint y
  have : simplexPoint y k ≤ ∑ j, simplexPoint y j :=
    Finset.single_le_sum (fun j _ => (hy j).le) (Finset.mem_univ k)
  linarith

/-- **The joint regulator limit on `Δ₄`, given the domination**: `T(0, 0)` is integrable on
`Δ₄` and `∫_{Δ₄} crossedFour λ Λ → ∫_{Δ₄} T(0, 0)` as `(λ, Λ) → (0⁺, ∞)`. -/
theorem tendsto_integral_crossedFour (hdom : CrossedDom) :
    IntegrableOn (fun y => crossedZero (simplexPoint y)) (simplexSet 4) ∧
    Tendsto (fun p : ℝ × ℝ => ∫ y in simplexSet 4, crossedFour p.1 p.2 (simplexPoint y))
      (𝓝[>] 0 ×ˢ atTop) (𝓝 (∫ y in simplexSet 4, crossedZero (simplexPoint y))) := by
  obtain ⟨C, s, hs0, hs1, hC⟩ := hdom
  have hint : IntegrableOn (fun y => 4 * C * ∏ k ∈ Finset.univ, simplexPoint y k ^ (-s))
      (simplexSet 4) :=
    (QED.Integration.TwoLoop.integrableOn_prod_simplexPoint_rpow Finset.univ hs0 hs1).const_mul _
  have hsp := QED.Integration.TwoLoop.continuous_simplexPoint' (m := 4)
  have hmeas : ∀ μa μb : ℝ, AEStronglyMeasurable
      (fun y : Fin 4 → ℝ => crossedTerm μa μb (simplexPoint y 0) (simplexPoint y 1)
        (simplexPoint y 2) (simplexPoint y 3) (simplexPoint y 4))
        (volume.restrict (simplexSet 4)) :=
    fun μa μb => ((measurable_crossedTerm μa μb).comp hsp.measurable).aestronglyMeasurable
  have hb : ∀ μa μb : ℝ, 0 ≤ μa → 0 ≤ μb → ∀ᵐ y ∂(volume.restrict (simplexSet 4)),
      |crossedTerm μa μb (simplexPoint y 0) (simplexPoint y 1) (simplexPoint y 2)
        (simplexPoint y 3) (simplexPoint y 4)| ≤ C * ∏ k, simplexPoint y k ^ (-s) := by
    intro μa μb ha hb
    filter_upwards [QED.TwoLoop.UnitLGraphReduce.ae_simplexPoint_pos (by norm_num : 0 < 4)]
      with y hy
    exact hC μa μb ha hb _ hy (sum_simplexPoint y)
  refine ⟨?_, ?_⟩
  · have hint1 : IntegrableOn (fun y => C * ∏ k ∈ Finset.univ, simplexPoint y k ^ (-s))
        (simplexSet 4) :=
      (QED.Integration.TwoLoop.integrableOn_prod_simplexPoint_rpow Finset.univ hs0 hs1).const_mul _
    refine hint1.mono' (hmeas 0 0) ?_
    filter_upwards [hb 0 0 le_rfl le_rfl] with y hy
    rw [Real.norm_eq_abs]
    exact hy
  · refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hint ?_
    · exact Eventually.of_forall fun p =>
        (((hmeas _ _).sub (hmeas _ _)).sub (hmeas _ _)).add (hmeas _ _)
    · refine Eventually.of_forall fun p => ?_
      filter_upwards [hb _ _ (sq_nonneg p.1) (sq_nonneg p.1),
        hb _ _ (sq_nonneg p.1) (sq_nonneg p.2),
        hb _ _ (sq_nonneg p.2) (sq_nonneg p.1), hb _ _ (sq_nonneg p.2) (sq_nonneg p.2)]
        with y h1 h2 h3 h4
      rw [Real.norm_eq_abs, crossedFour]
      have := abs_add_le (crossedTerm (p.1 ^ 2) (p.1 ^ 2) (simplexPoint y 0) (simplexPoint y 1)
        (simplexPoint y 2) (simplexPoint y 3) (simplexPoint y 4) -
        crossedTerm (p.1 ^ 2) (p.2 ^ 2) (simplexPoint y 0) (simplexPoint y 1) (simplexPoint y 2)
          (simplexPoint y 3) (simplexPoint y 4) -
        crossedTerm (p.2 ^ 2) (p.1 ^ 2) (simplexPoint y 0) (simplexPoint y 1) (simplexPoint y 2)
          (simplexPoint y 3) (simplexPoint y 4))
        (crossedTerm (p.2 ^ 2) (p.2 ^ 2) (simplexPoint y 0) (simplexPoint y 1) (simplexPoint y 2)
          (simplexPoint y 3) (simplexPoint y 4))
      have := abs_sub (crossedTerm (p.1 ^ 2) (p.1 ^ 2) (simplexPoint y 0) (simplexPoint y 1)
        (simplexPoint y 2) (simplexPoint y 3) (simplexPoint y 4) -
        crossedTerm (p.1 ^ 2) (p.2 ^ 2) (simplexPoint y 0) (simplexPoint y 1) (simplexPoint y 2)
          (simplexPoint y 3) (simplexPoint y 4))
        (crossedTerm (p.2 ^ 2) (p.1 ^ 2) (simplexPoint y 0) (simplexPoint y 1) (simplexPoint y 2)
          (simplexPoint y 3) (simplexPoint y 4))
      have := abs_sub (crossedTerm (p.1 ^ 2) (p.1 ^ 2) (simplexPoint y 0) (simplexPoint y 1)
        (simplexPoint y 2) (simplexPoint y 3) (simplexPoint y 4))
        (crossedTerm (p.1 ^ 2) (p.2 ^ 2) (simplexPoint y 0) (simplexPoint y 1) (simplexPoint y 2)
          (simplexPoint y 3) (simplexPoint y 4))
      linarith
    · filter_upwards [QED.TwoLoop.UnitLGraphReduce.ae_simplexPoint_pos (by norm_num : 0 < 4)]
        with y hy
      exact tendsto_crossedFour hy


/-! ### The massless integrand in the hierarchical Cheng–Wu variables -/

theorem crossedZero_smul {z : Fin 5 → ℝ} (hz : ∀ i, 0 < z i) {t : ℝ} (ht : 0 < t) :
    crossedZero (t • z) = (t ^ 5)⁻¹ • crossedZero z := by
  simp only [crossedZero, Pi.smul_apply, smul_eq_mul]
  exact crossedTerm_smul le_rfl le_rfl (hz 0) (hz 1) (hz 2) (hz 3) (hz 4) ht

/-- **The massless integral as an iterated integral** in the hierarchical variables, given that
`T(0, 0)` is integrable on `Δ₄`: `∫_{Δ₄} T(0, 0) = ∫_{(z₂, z₃) ∈ triangle} ∫₀^∞ dz_A ∫₀^∞ dz_a
T(0, 0)(z_A, z₂, z₃, z_a, 1 - z₂ - z₃)`. -/
theorem integral_crossedZero_eq_iterated
    (hI : IntegrableOn (fun y => crossedZero (simplexPoint y)) (simplexSet 4)) :
    ∫ y in simplexSet 4, crossedZero (simplexPoint y) =
      ∫ p in innerTriangle, ∫ zA in Ioi (0 : ℝ), ∫ za in Ioi (0 : ℝ),
        crossedTerm 0 0 zA p.1 p.2 za (1 - (p.1 + p.2)) := by
  have hF : ∀ z : Fin 5 → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t →
      crossedZero (t • z) = (t ^ 5)⁻¹ • crossedZero z := fun z hz t ht => crossedZero_smul hz ht
  have hCW := integral_simplex_chengWuSet (by norm_num) innerSet crossedZero hF
  have hCWi := (integrableOn_simplex_chengWuSet_iff (by norm_num) innerSet crossedZero hF).mp hI
  simp only [sum_innerSet] at hCW hCWi
  rw [hCW, integral_cwSet_innerSet hCWi]
  rfl

/-! ### The X link -/

/-- The value `1/6 - 5 ζ(2) log 2 + (13/6) ζ(2) + (5/4) ζ(3)` of the X unit. -/
noncomputable def xValue : ℝ :=
  1 / 6 - 5 * (π ^ 2 / 6) * Real.log 2 + 13 / 6 * (π ^ 2 / 6) + 5 / 4 * QED.Polylog.zeta3

/-- **The X link at `m = 1`**, given the domination and the value of the massless integral. -/
theorem xUnitLimitOne_of_dom (hdom : CrossedDom)
    (hval : ∫ y in simplexSet 4, crossedZero (simplexPoint y) = xValue) :
    QED.TwoLoop.HeadlineAssembly.XUnitLimitOne := by
  intro η hη
  have hT := Metric.tendsto_nhds.mp (tendsto_integral_crossedFour hdom).2 η hη
  rw [hval] at hT
  obtain ⟨pa, hpa, pb, hpb, hp⟩ := eventually_prod_iff.mp hT
  obtain ⟨ε, hε, hεa⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hpa)
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp hpb
  refine ⟨min ε 1, lt_min hε one_pos, max R₀ 1,
    fun P hm hmγ hΛ hm1 hδ hR d₁ d₂ dm d₃ _ _ => ?_⟩
  have hlt : P.mγ < P.Λ := by
    have := min_le_right ε 1
    have := le_max_right R₀ 1
    linarith
  obtain ⟨-, hEq⟩ := sixteen_pi_pow_four_mul_unitF2_X_eq_simplex
    (P := atUnitCharge P d₁ d₂ dm d₃) hm1 rfl hmγ hlt
  rw [hEq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← Real.dist_eq]
  have key := hp (hεa ?_ hmγ) (hR₀ _ ((le_max_left R₀ 1).trans hR.le))
  · simpa [crossedF4_eq, xValue, atUnitCharge] using key
  · rw [Real.dist_eq, sub_zero, abs_of_pos hmγ]
    exact lt_of_lt_of_le hδ (min_le_left ε 1)

/-- **The X link at `m = 1`**, given the domination and the value of the massless iterated
integral in the hierarchical variables. -/
theorem xUnitLimitOne_of_dom_iterated (hdom : CrossedDom)
    (hval : ∫ p in innerTriangle, ∫ zA in Ioi (0 : ℝ), ∫ za in Ioi (0 : ℝ),
        crossedTerm 0 0 zA p.1 p.2 za (1 - (p.1 + p.2)) = xValue) :
    QED.TwoLoop.HeadlineAssembly.XUnitLimitOne :=
  xUnitLimitOne_of_dom hdom <| by
    rw [integral_crossedZero_eq_iterated (tendsto_integral_crossedFour hdom).1, hval]

end QED.TwoLoop.UnitXClose

end
