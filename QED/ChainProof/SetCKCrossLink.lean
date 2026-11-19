/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKCrossSubst
public import QED.ChainProof.SetCKAssembly
public import QED.TwoLoop.UnitXCloseYXi

/-!
# Set (c), Stage K, group G3: the crossed pair from the parametric integrand

Helper level (no frozen statement). Links the closed-form crossed piece `crossT` of
`QED/ChainProof/SetCKCrossT.lean` to the crossed unit on the simplex, `crossUnit`
(`QED/ChainProof/SetCKCrossMirror.lean`), and removes the factor `2` of the assembly:

* `crossT_eq_crossUnit`: **`crossT t = crossUnit 0 t`** for `t > 0`. The Cheng–Wu form
  (`crossUnit_eq_iterated`), the exchange `(z_A, z_a) ↦ (x, b)` with `b > β(x)`
  (`QED.TwoLoop.UnitSCLimit.integral_substB_swap`), the `b`-integration (`hasIoiInt_crossAX`) and
  the substitution `(z₂, z₃) = (y₃, Y - y₃)` of the triangle
  (`QED.TwoLoop.UnitXClose.integral_triangle_eq_yxi` and `y₃ = Y ξ`).
* `crossT_eq_crossUnit_mirror`: `crossT t = crossUnit t 0` (with `crossUnit_mirror`).
* `setCKKernelSum_eq'`: **the Stieltjes representation with the actual crossed pair**
  `X(t, 0) + X(0, t) = crossUnit 0 t + crossUnit t 0` in place of `2 crossT t`
  (`setCKKernelPairSum`).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory Function

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitXGraph QED.TwoLoop.UnitXClose QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

theorem measurable_crossSlice (μa μb y3 y4 : ℝ) :
    Measurable (uncurry fun zA za => crossedTerm μa μb zA y3 y4 za (1 - (y3 + y4))) := by
  change Measurable fun p : ℝ × ℝ => crossedTerm μa μb p.1 y3 y4 p.2 (1 - (y3 + y4))
  unfold crossedTerm gPsi1 gPsi2 gXE gXEn psiT1h psiT2h gXan gXbn gXU
  fun_prop

/-- For almost every `(y₃, y₄)` in the triangle, the slice of the crossed integrand is integrable
on `(0, ∞)²`. -/
theorem ae_integrable_crossSlice {μa μb : ℝ} (hμa : 0 ≤ μa) (hμb : 0 ≤ μb) :
    ∀ᵐ p ∂(volume.restrict innerTriangle),
      Integrable (uncurry fun zA za => crossedTerm μa μb zA p.1 p.2 za (1 - (p.1 + p.2)))
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  filter_upwards [(integrable_crossedH hμa hμb).prod_right_ae] with p hp
  rw [← Measure.prod_restrict] at hp
  exact hp.congr (ae_of_all _ fun q => rfl)

theorem cornerMass_zero_sqrt_pos {t y3 y4 : ℝ} (h3 : 0 < y3) (h4 : 0 < y4)
    (hY : y3 + y4 < 1) : 0 < cornerMass 0 (√t) y3 y4 := by
  unfold cornerMass
  have h1 : 0 ≤ (1 - (y3 + y4)) * √t ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : 0 < (y3 + y4) ^ 2 := by positivity
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, sub_zero]
  linarith

/-- **The two outer integrations of the inner-massive crossed integrand** at a point of the
triangle: `∫₀^∞ ∫₀^∞ T(0, t) dz_a dz_A = ∫₀¹ crossTGm 0 √t y₃ y₄ x dx`. -/
theorem iterated_crossedTerm_eq {t : ℝ} (ht : 0 < t) {p : ℝ × ℝ} (hp : p ∈ innerTriangle)
    (hint : Integrable (uncurry fun zA za => crossedTerm 0 t zA p.1 p.2 za (1 - (p.1 + p.2)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) :
    ∫ zA in Ioi (0 : ℝ), ∫ za in Ioi (0 : ℝ), crossedTerm 0 t zA p.1 p.2 za (1 - (p.1 + p.2)) =
      ∫ x in Ioo (0 : ℝ) 1, crossTGm 0 (√t) p.1 p.2 x := by
  obtain ⟨h3, h4, hY⟩ := hp
  have hg : 0 < cornerG p.1 p.2 := by
    unfold cornerG; have : 0 < 1 - p.1 - p.2 := by linarith
    positivity
  obtain ⟨-, heq⟩ := integral_substB_swap hg (mul_pos h3 h4) (measurable_crossSlice 0 t p.1 p.2)
    hint
  rw [heq]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have hh : 0 < ladderInnerMass 1 0 x / x := by
    rw [ladderInnerMass_zero_div hx.1.ne']; exact hx.1
  have hI := hasIoiInt_crossAX (la := 0) (lb := √t) h3 hY hx hh
    (cornerMass_zero_sqrt_pos (t := t) h3 h4 hY)
  rw [← hI.2]
  refine setIntegral_congr_fun measurableSet_Ioi fun z _ => ?_
  have e1 : z + (betaG (cornerG p.1 p.2) (p.1 * p.2) x - cornerG p.1 p.2) =
      z + betaG (cornerG p.1 p.2) (p.1 * p.2) x - cornerG p.1 p.2 := by ring
  have e2 : (1 : ℝ) - (p.1 + p.2) = 1 - p.1 - p.2 := by ring
  simp only [substB, crossAX, e1, e2, sq_sqrt ht.le, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow]

/-- The `x`-integrand of the crossed piece at a point of the triangle. -/
noncomputable def crossTriF (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ x in Ioo (0 : ℝ) 1, crossTGm 0 (√t) p.1 p.2 x

theorem ae_iterated_eq_crossTriF {t : ℝ} (ht : 0 < t) :
    (fun p : ℝ × ℝ => ∫ zA in Ioi (0 : ℝ), ∫ za in Ioi (0 : ℝ),
        crossedTerm 0 t zA p.1 p.2 za (1 - (p.1 + p.2))) =ᵐ[volume.restrict innerTriangle]
      crossTriF t := by
  filter_upwards [ae_integrable_crossSlice le_rfl ht.le,
    ae_restrict_mem measurableSet_innerTriangle] with p hp hmem
  exact iterated_crossedTerm_eq ht hmem hp

theorem integrableOn_crossTriF {t : ℝ} (ht : 0 < t) : IntegrableOn (crossTriF t) innerTriangle := by
  have hH := integrable_crossedH le_rfl ht.le
  have hL := hH.integral_prod_left
  refine (hL.congr ?_).congr (ae_iterated_eq_crossTriF ht)
  filter_upwards [hH.prod_right_ae] with p hp
  rw [← Measure.prod_restrict] at hp
  rw [← Measure.prod_restrict, integral_prod _ hp]
  rfl

/-- The `ξ`-integral of the triangle substitution is the `y₃`-integral of `crossTIntegrand`. -/
theorem crossTIntegrand_eq_xi {t Y : ℝ} (hY : 0 < Y) :
    crossTIntegrand t Y = ∫ ξ in Ioo (0 : ℝ) 1, Y * crossTriF t (Y * ξ, Y * (1 - ξ)) := by
  set g : ℝ → ℝ := fun y3 => ∫ x in (0 : ℝ)..1, crossTGm 0 (√t) y3 (Y - y3) x with hg
  have hf : ∀ ξ, crossTriF t (Y * ξ, Y * (1 - ξ)) = g (Y * ξ) := fun ξ => by
    simp only [crossTriF, hg, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
    rw [show Y * (1 - ξ) = Y - Y * ξ by ring]
  simp only [hf]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left _ hY.ne',
    mul_zero, mul_one, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hY.ne', one_mul]
  rfl

/-- **The inner-massive crossed piece is the crossed unit on the simplex**:
`crossT t = crossUnit 0 t` (`X(t, 0)`). -/
theorem crossT_eq_crossUnit {t : ℝ} (ht : 0 < t) : crossT t = crossUnit 0 t := by
  rw [crossUnit_eq_iterated le_rfl ht.le, integral_congr_ae (ae_iterated_eq_crossTriF ht),
    integral_triangle_eq_yxi (integrableOn_crossTriF ht), crossT,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo fun Y hY => crossTIntegrand_eq_xi hY.1

/-- **The mirror placement**: `crossT t = crossUnit t 0` (`X(0, t)`). -/
theorem crossT_eq_crossUnit_mirror {t : ℝ} (ht : 0 < t) : crossT t = crossUnit t 0 := by
  rw [crossT_eq_crossUnit ht, crossUnit_mirror]

/-- **The set (c) kernel sum with the actual crossed pair** `X(t, 0) + X(0, t)`. -/
noncomputable def setCKKernelPairSum (t : ℝ) : ℝ :=
  lPair t + selfIn t + cornIn t + (crossUnit 0 t + crossUnit t 0) + scOutS t + scOutC t

theorem setCKKernelPairSum_eq_setCKKernelSum {t : ℝ} (ht : 0 < t) :
    setCKKernelPairSum t = setCKKernelSum t := by
  rw [setCKKernelPairSum, setCKKernelSum, ← crossT_eq_crossUnit ht,
    ← crossT_eq_crossUnit_mirror ht, two_mul]

/-- **The Stieltjes representation of the set (c) kernel sum with the actual crossed pair**
(`Q`-derivative form): the factor `2` of `setCKKernelSum_eq` is the mirror symmetry. -/
theorem setCKKernelSum_eq' {t : ℝ} (ht : 0 < t) :
    setCKKernelPairSum t =
      ∫ X in (0 : ℝ)..1, setCKHTot X * (setCKdQ X / (setCKQ X + t) ^ 2) := by
  rw [setCKKernelPairSum_eq_setCKKernelSum ht, setCKKernelSum_eq ht]

end QED.ChainProof.SetCK

end
