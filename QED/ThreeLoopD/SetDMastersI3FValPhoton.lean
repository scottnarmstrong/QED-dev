/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI3FValCoV

/-!
# Set (d), master `I₃`: the photon-parameter integrals of `i3FInt 0`

Starting from `QED.ThreeLoopD.i3FInt_zero_eq_lintegral`, both photon parameters integrate in
closed form.

**`d₁`.** `U = A₁ d₁ + B₁` and `F = A₂ d₁ + B₂` are linear in `d₁`, with
`A₁ B₂ - A₂ B₁ = L²`, `L = e₁ d₃ + δ`, `δ = c (e₁ + e₃) + e₁ e₃`. Hence
`∫₀^∞ dd₁ / (U F) = log (A₁ B₂ / (A₂ B₁)) / L²` (`QED.ThreeLoopD.i3V_lintegral_d1`).

**`d₃`.** As polynomials in `d₃`,

  `A₁ = d₃ + c + e₃`, `B₂ = (c + e₁ + e₁²) d₃ + (1 + e₁ + e₃) δ`,
  `A₂ = d₃ + c + e₃ + e₃²`, `B₁ = (c + e₁) d₃ + δ`,

and `∫₀^∞ log (α x + β) / (γ x + δ)² dx = log β / (γ δ) + α log (α δ / (β γ)) / (γ (α δ - β γ))`
(`QED.ThreeLoopD.i3VLI`, for `α δ ≠ β γ`). The four determinants are `c e₃`,
`(c - e₁ e₃) δ`, `e₃ (c - e₁ e₃)` and `c δ`, so away from the null set `e₁ e₃ = c` the double
integral is `f₂ = i3VLI(A₁) + i3VLI(B₂) - i3VLI(A₂) - i3VLI(B₁)` (`QED.ThreeLoopD.i3VF2`). The
four logarithms are integrated together with the nonnegative-derivative form of the
fundamental theorem of calculus on `(0, ∞)`, so no term needs to be integrable on its own.

## Main results

* `QED.ThreeLoopD.i3V_lintegral_photons`: `∫∫ dd₃ dd₁ / (U F) = f₂(c, e₁, e₃)`.
* `QED.ThreeLoopD.i3FInt_zero_eq_lintegral_f2`:
  `i3FInt 0 = ∫₀¹ dx ∫₀^∞ de₁ ∫₀^∞ de₃ f₂(x (1 - x), e₁, e₃)` (as a lower integral).
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology
open scoped ENNReal

namespace QED.ThreeLoopD

/-- FTC on `(0, ∞)` for lower integrals of a nonnegative derivative. -/
theorem i3V_lintegral_Ioi_eq {g g' : ℝ → ℝ} {l : ℝ}
    (hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt g (g' x) x) (hpos : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ g' x)
    (hl : Tendsto g atTop (𝓝 l)) :
    ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (g' x) = ENNReal.ofReal (l - g 0) := by
  have hI := integrableOn_Ioi_deriv_of_nonneg' hd hpos hl
  rw [← ofReal_integral_eq_lintegral_ofReal hI, integral_Ioi_of_hasDerivAt_of_nonneg' hd hpos hl]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hpos x hx

/-- `(α x + β) / (γ x + δ) → α / γ`. -/
theorem i3V_tendsto_ratio {α β γ δ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun x => (α * x + β) / (γ * x + δ)) atTop (𝓝 (α / γ)) := by
  have h : Tendsto (fun x : ℝ => (α + β * x⁻¹) / (γ + δ * x⁻¹)) atTop
      (𝓝 ((α + β * 0) / (γ + δ * 0))) :=
    ((tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul β)).div
      (tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul δ)) (by simp [hγ.ne']))
  simp only [mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  field_simp

/-- `log (α x + β) / (γ x + δ) → 0`. -/
theorem i3V_tendsto_log_div {α β γ δ : ℝ} (hα : 0 < α) (hγ : 0 < γ) :
    Tendsto (fun x => log (α * x + β) / (γ * x + δ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => α * x + β) atTop atTop :=
    tendsto_atTop_add_const_right _ β (tendsto_id.const_mul_atTop hα)
  have h2 := (tendsto_pow_log_div_mul_add_atTop (γ / α) (δ - γ * β / α) 1
    (div_pos hγ hα).ne').comp h1
  refine h2.congr fun x => ?_
  simp only [Function.comp, pow_one]
  congr 1
  field_simp
  ring

/-- The `d₁`-integral: `∫₀^∞ dd / ((A₁ d + B₁)(A₂ d + B₂)) = log (A₁ B₂ / (A₂ B₁)) / K`. -/
theorem i3V_lintegral_rat {A1 B1 A2 B2 : ℝ} (hA1 : 0 < A1) (hB1 : 0 < B1) (hA2 : 0 < A2)
    (hB2 : 0 < B2) (hK : 0 < A1 * B2 - A2 * B1) :
    ∫⁻ d in Ioi (0 : ℝ), ENNReal.ofReal (1 / ((A1 * d + B1) * (A2 * d + B2))) =
      ENNReal.ofReal ((log A1 + log B2 - log A2 - log B1) / (A1 * B2 - A2 * B1)) := by
  set K := A1 * B2 - A2 * B1 with hKd
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun d => (log (A1 * d + B1) - log (A2 * d + B2)) / K)
      (1 / ((A1 * x + B1) * (A2 * x + B2))) x := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx
    have p1 : 0 < A1 * x + B1 := by positivity
    have p2 : 0 < A2 * x + B2 := by positivity
    have h1 := (((hasDerivAt_id x).const_mul A1).add_const B1).log p1.ne'
    have h2 := (((hasDerivAt_id x).const_mul A2).add_const B2).log p2.ne'
    refine ((h1.sub h2).div_const K).congr_deriv ?_
    simp only [id, mul_one]
    field_simp
    rw [hKd]; ring
  have hpos : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ 1 / ((A1 * x + B1) * (A2 * x + B2)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    positivity
  have hl : Tendsto (fun d => (log (A1 * d + B1) - log (A2 * d + B2)) / K) atTop
      (𝓝 ((log A1 - log A2) / K)) := by
    have h := ((continuousAt_log (div_pos hA1 hA2).ne').tendsto.comp
      (i3V_tendsto_ratio (α := A1) (β := B1) (δ := B2) hA2)).div_const K
    rw [log_div hA1.ne' hA2.ne'] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with d hd
    have p1 : 0 < A1 * d + B1 := by positivity
    have p2 : 0 < A2 * d + B2 := by positivity
    simp only [Function.comp, log_div p1.ne' p2.ne']
  rw [i3V_lintegral_Ioi_eq hd hpos hl]
  congr 1
  simp only [mul_zero, zero_add]
  ring

/-- `∫₀^∞ log (α x + β) / (γ x + δ)² dx`, for `α δ ≠ β γ`. -/
noncomputable def i3VLI (α β γ δ : ℝ) : ℝ :=
  log β / (γ * δ) + α * log (α * δ / (β * γ)) / (γ * (α * δ - β * γ))

/-- An antiderivative of `log (α x + β) / (γ x + δ)²`. -/
noncomputable def i3VPrim (α β γ δ x : ℝ) : ℝ :=
  -(log (α * x + β) / (γ * (γ * x + δ))) +
    α / (γ * (α * δ - β * γ)) * log ((α * x + β) / (γ * x + δ))

/-- The derivative of `i3VPrim`. -/
theorem hasDerivAt_i3VPrim {α β γ δ x : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hδ : 0 < δ) (hK : α * δ - β * γ ≠ 0) (hx : 0 ≤ x) :
    HasDerivAt (i3VPrim α β γ δ) (log (α * x + β) / (γ * x + δ) ^ 2) x := by
  have p1 : 0 < α * x + β := by positivity
  have p2 : 0 < γ * x + δ := by positivity
  have hl := (((hasDerivAt_id x).const_mul α).add_const β).log p1.ne'
  have hq := ((((hasDerivAt_id x).const_mul α).add_const β).div
    (((hasDerivAt_id x).const_mul γ).add_const δ) p2.ne').log (div_pos p1 p2).ne'
  have hd := ((hl.div ((((hasDerivAt_id x).const_mul γ).add_const δ).const_mul γ)
    (mul_pos hγ p2).ne').neg).add (hq.const_mul (α / (γ * (α * δ - β * γ))))
  refine hd.congr_deriv ?_
  simp only [id, mul_one, Pi.div_apply]
  field_simp
  ring

/-- The limit of `i3VPrim` at `∞`. -/
theorem tendsto_i3VPrim {α β γ δ : ℝ} (hα : 0 < α) (hγ : 0 < γ) :
    Tendsto (i3VPrim α β γ δ) atTop
      (𝓝 (-(0 / γ) + α / (γ * (α * δ - β * γ)) * log (α / γ))) := by
  have h1 : Tendsto (fun x => log (α * x + β) / (γ * x + δ) / γ) atTop (𝓝 (0 / γ)) :=
    (i3V_tendsto_log_div hα hγ).div_const γ
  have h2 := ((continuousAt_log (div_pos hα hγ).ne').tendsto.comp
    (i3V_tendsto_ratio (α := α) (β := β) (δ := δ) hγ)).const_mul (α / (γ * (α * δ - β * γ)))
  refine (h1.neg.add h2).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [i3VPrim, Function.comp]
  congr 2
  rw [div_div, mul_comm (γ * x + δ) γ]

/-- `i3VLI` is the limit minus the value at `0`. -/
theorem i3VLI_eq {α β γ δ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ) :
    -(0 / γ) + α / (γ * (α * δ - β * γ)) * log (α / γ) - i3VPrim α β γ δ 0 = i3VLI α β γ δ := by
  simp only [i3VPrim, i3VLI, mul_zero, zero_add, zero_div, neg_zero]
  rw [log_div hα.ne' hγ.ne', log_div hβ.ne' hδ.ne',
    log_div (mul_pos hα hδ).ne' (mul_pos hβ hγ).ne', log_mul hα.ne' hδ.ne',
    log_mul hβ.ne' hγ.ne']
  ring

/-- **The `d₃`-integral** of a combination of four logarithms over `(γ x + δ)²`. -/
theorem i3V_lintegral_log4 {α₁ β₁ α₂ β₂ α₃ β₃ α₄ β₄ γ δ : ℝ} (hα₁ : 0 < α₁) (hβ₁ : 0 < β₁)
    (hα₂ : 0 < α₂) (hβ₂ : 0 < β₂) (hα₃ : 0 < α₃) (hβ₃ : 0 < β₃) (hα₄ : 0 < α₄) (hβ₄ : 0 < β₄)
    (hγ : 0 < γ) (hδ : 0 < δ) (hK₁ : α₁ * δ - β₁ * γ ≠ 0) (hK₂ : α₂ * δ - β₂ * γ ≠ 0)
    (hK₃ : α₃ * δ - β₃ * γ ≠ 0) (hK₄ : α₄ * δ - β₄ * γ ≠ 0)
    (hpos : ∀ x, 0 < x → 0 ≤ log (α₁ * x + β₁) + log (α₂ * x + β₂) - log (α₃ * x + β₃) -
      log (α₄ * x + β₄)) :
    ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((log (α₁ * x + β₁) + log (α₂ * x + β₂) -
        log (α₃ * x + β₃) - log (α₄ * x + β₄)) / (γ * x + δ) ^ 2) =
      ENNReal.ofReal (i3VLI α₁ β₁ γ δ + i3VLI α₂ β₂ γ δ - i3VLI α₃ β₃ γ δ - i3VLI α₄ β₄ γ δ) := by
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun x => i3VPrim α₁ β₁ γ δ x + i3VPrim α₂ β₂ γ δ x -
      i3VPrim α₃ β₃ γ δ x - i3VPrim α₄ β₄ γ δ x) ((log (α₁ * x + β₁) + log (α₂ * x + β₂) -
        log (α₃ * x + β₃) - log (α₄ * x + β₄)) / (γ * x + δ) ^ 2) x := by
    intro x hx
    refine ((((hasDerivAt_i3VPrim hα₁ hβ₁ hγ hδ hK₁ hx).add
      (hasDerivAt_i3VPrim hα₂ hβ₂ hγ hδ hK₂ hx)).sub
        (hasDerivAt_i3VPrim hα₃ hβ₃ hγ hδ hK₃ hx)).sub
          (hasDerivAt_i3VPrim hα₄ hβ₄ hγ hδ hK₄ hx)).congr_deriv ?_
    ring
  have hp : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ (log (α₁ * x + β₁) + log (α₂ * x + β₂) -
      log (α₃ * x + β₃) - log (α₄ * x + β₄)) / (γ * x + δ) ^ 2 :=
    fun x hx => div_nonneg (hpos x hx) (sq_nonneg _)
  have hl := (((tendsto_i3VPrim (β := β₁) (δ := δ) hα₁ hγ).add
    (tendsto_i3VPrim (β := β₂) (δ := δ) hα₂ hγ)).sub
      (tendsto_i3VPrim (β := β₃) (δ := δ) hα₃ hγ)).sub
        (tendsto_i3VPrim (β := β₄) (δ := δ) hα₄ hγ)
  rw [i3V_lintegral_Ioi_eq hd hp hl, ← i3VLI_eq hα₁ hβ₁ hγ hδ, ← i3VLI_eq hα₂ hβ₂ hγ hδ,
    ← i3VLI_eq hα₃ hβ₃ hγ hδ, ← i3VLI_eq hα₄ hβ₄ hγ hδ]
  congr 1
  ring

/-- `δ = c (e₁ + e₃) + e₁ e₃`. -/
def i3VDel (c e1 e3 : ℝ) : ℝ := c * (e1 + e3) + e1 * e3

/-- **The photon-integrated integrand** `f₂(c, e₁, e₃) = ∫∫ dd₁ dd₃ / (U F)` (for `c ≠ e₁ e₃`). -/
noncomputable def i3VF2 (c e1 e3 : ℝ) : ℝ :=
  i3VLI 1 (c + e3) e1 (i3VDel c e1 e3) +
    i3VLI (c + e1 + e1 ^ 2) ((1 + e1 + e3) * i3VDel c e1 e3) e1 (i3VDel c e1 e3) -
    i3VLI 1 (c + e3 + e3 ^ 2) e1 (i3VDel c e1 e3) - i3VLI (c + e1) (i3VDel c e1 e3) e1
      (i3VDel c e1 e3)

/-- The `d₁`-integral of `1 / (U F)`. -/
theorem i3V_lintegral_d1 {c e1 d3 e3 : ℝ} (hc : 0 < c) (he1 : 0 < e1) (hd3 : 0 < d3)
    (he3 : 0 < e3) :
    ∫⁻ d1 in Ioi (0 : ℝ), ENNReal.ofReal (i3VDens c d1 e1 d3 e3) =
      ENNReal.ofReal ((log (1 * d3 + (c + e3)) +
        log ((c + e1 + e1 ^ 2) * d3 + (1 + e1 + e3) * i3VDel c e1 e3) -
        log (1 * d3 + (c + e3 + e3 ^ 2)) - log ((c + e1) * d3 + i3VDel c e1 e3)) /
          (e1 * d3 + i3VDel c e1 e3) ^ 2) := by
  have hδ : 0 < i3VDel c e1 e3 := by unfold i3VDel; positivity
  have hK : 0 < (c + (d3 + e3)) * (c * (e1 + (d3 + e3)) + e1 * (d3 + e3) + c * (e1 + e3) ^ 2 +
      e1 ^ 2 * (d3 + e3) + e3 ^ 2 * e1) - (c + (d3 + e3) + e3 ^ 2) *
        (c * (e1 + (d3 + e3)) + e1 * (d3 + e3)) := by
    have e : (c + (d3 + e3)) * (c * (e1 + (d3 + e3)) + e1 * (d3 + e3) + c * (e1 + e3) ^ 2 +
      e1 ^ 2 * (d3 + e3) + e3 ^ 2 * e1) - (c + (d3 + e3) + e3 ^ 2) *
        (c * (e1 + (d3 + e3)) + e1 * (d3 + e3)) = (e1 * d3 + i3VDel c e1 e3) ^ 2 := by
      unfold i3VDel; ring
    rw [e]; positivity
  have h := i3V_lintegral_rat (A1 := c + (d3 + e3)) (B1 := c * (e1 + (d3 + e3)) + e1 * (d3 + e3))
    (A2 := c + (d3 + e3) + e3 ^ 2) (B2 := c * (e1 + (d3 + e3)) + e1 * (d3 + e3) +
      c * (e1 + e3) ^ 2 + e1 ^ 2 * (d3 + e3) + e3 ^ 2 * e1) (by positivity) (by positivity)
    (by positivity) (by positivity) hK
  have e : ∀ d1, i3VDens c d1 e1 d3 e3 = 1 / (((c + (d3 + e3)) * d1 +
      (c * (e1 + (d3 + e3)) + e1 * (d3 + e3))) * ((c + (d3 + e3) + e3 ^ 2) * d1 +
        (c * (e1 + (d3 + e3)) + e1 * (d3 + e3) + c * (e1 + e3) ^ 2 + e1 ^ 2 * (d3 + e3) +
          e3 ^ 2 * e1))) := fun d1 => by
    simp only [i3VDens, i3VF, i3VU]; ring
  simp_rw [e]
  rw [h]
  congr 1
  unfold i3VDel
  congr 1
  · congr 1; congr 1; congr 1
    · congr 1; ring
    · congr 1; ring
    · congr 1; ring
    · congr 1; ring
  · ring

/-- The `d₁`-integral is nonnegative: `A₁ B₂ - A₂ B₁ = L² ≥ 0`. -/
theorem i3V_log_comb_nonneg {c e1 d3 e3 : ℝ} (hc : 0 < c) (he1 : 0 < e1) (hd3 : 0 < d3)
    (he3 : 0 < e3) :
    0 ≤ log (1 * d3 + (c + e3)) + log ((c + e1 + e1 ^ 2) * d3 + (1 + e1 + e3) * i3VDel c e1 e3) -
      log (1 * d3 + (c + e3 + e3 ^ 2)) - log ((c + e1) * d3 + i3VDel c e1 e3) := by
  have hδ : 0 < i3VDel c e1 e3 := by unfold i3VDel; positivity
  have p1 : 0 < 1 * d3 + (c + e3) := by positivity
  have p2 : 0 < (c + e1 + e1 ^ 2) * d3 + (1 + e1 + e3) * i3VDel c e1 e3 := by positivity
  have p3 : 0 < 1 * d3 + (c + e3 + e3 ^ 2) := by positivity
  have p4 : 0 < (c + e1) * d3 + i3VDel c e1 e3 := by positivity
  have hle : (1 * d3 + (c + e3 + e3 ^ 2)) * ((c + e1) * d3 + i3VDel c e1 e3) ≤
      (1 * d3 + (c + e3)) * ((c + e1 + e1 ^ 2) * d3 + (1 + e1 + e3) * i3VDel c e1 e3) := by
    have e : (1 * d3 + (c + e3)) * ((c + e1 + e1 ^ 2) * d3 + (1 + e1 + e3) * i3VDel c e1 e3) -
        (1 * d3 + (c + e3 + e3 ^ 2)) * ((c + e1) * d3 + i3VDel c e1 e3) =
          (e1 * d3 + i3VDel c e1 e3) ^ 2 := by unfold i3VDel; ring
    nlinarith [sq_nonneg (e1 * d3 + i3VDel c e1 e3)]
  have := log_le_log (mul_pos p3 p4) hle
  rw [log_mul p3.ne' p4.ne', log_mul p1.ne' p2.ne'] at this
  linarith

/-- **The photon integrals**: `∫∫ dd₃ dd₁ / (U F) = f₂(c, e₁, e₃)` for `c ≠ e₁ e₃`. -/
theorem i3V_lintegral_photons {c e1 e3 : ℝ} (hc : 0 < c) (he1 : 0 < e1) (he3 : 0 < e3)
    (hm : c ≠ e1 * e3) :
    ∫⁻ d3 in Ioi (0 : ℝ), ∫⁻ d1 in Ioi (0 : ℝ), ENNReal.ofReal (i3VDens c d1 e1 d3 e3) =
      ENNReal.ofReal (i3VF2 c e1 e3) := by
  have hδ : 0 < i3VDel c e1 e3 := by unfold i3VDel; positivity
  rw [setLIntegral_congr_fun measurableSet_Ioi fun d3 (hd3 : 0 < d3) =>
    i3V_lintegral_d1 hc he1 hd3 he3]
  have hm' : c - e1 * e3 ≠ 0 := sub_ne_zero.2 hm
  have k1 : 1 * i3VDel c e1 e3 - (c + e3) * e1 ≠ 0 := by
    rw [show 1 * i3VDel c e1 e3 - (c + e3) * e1 = c * e3 by unfold i3VDel; ring]; positivity
  have k2 : (c + e1 + e1 ^ 2) * i3VDel c e1 e3 - (1 + e1 + e3) * i3VDel c e1 e3 * e1 ≠ 0 := by
    rw [show (c + e1 + e1 ^ 2) * i3VDel c e1 e3 - (1 + e1 + e3) * i3VDel c e1 e3 * e1 =
      (c - e1 * e3) * i3VDel c e1 e3 by ring]
    exact mul_ne_zero hm' hδ.ne'
  have k3 : 1 * i3VDel c e1 e3 - (c + e3 + e3 ^ 2) * e1 ≠ 0 := by
    rw [show 1 * i3VDel c e1 e3 - (c + e3 + e3 ^ 2) * e1 = e3 * (c - e1 * e3) by
      unfold i3VDel; ring]
    exact mul_ne_zero he3.ne' hm'
  have k4 : (c + e1) * i3VDel c e1 e3 - i3VDel c e1 e3 * e1 ≠ 0 := by
    rw [show (c + e1) * i3VDel c e1 e3 - i3VDel c e1 e3 * e1 = c * i3VDel c e1 e3 by ring]
    positivity
  rw [i3V_lintegral_log4 one_pos (by positivity) (by positivity) (by positivity) one_pos
    (by positivity) (by positivity) hδ he1 hδ k1 k2 k3 k4
    fun x hx => i3V_log_comb_nonneg hc he1 hx he3]
  rfl

/-- **`i3FInt 0` as a triple integral of `f₂`.** -/
theorem i3FInt_zero_eq_lintegral_f2 :
    i3FInt 0 = (((∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ e1 in Ioi (0 : ℝ), ∫⁻ e3 in Ioi (0 : ℝ),
      ENNReal.ofReal (i3VF2 (x * (1 - x)) e1 e3)).toReal : ℝ) : ℂ) := by
  rw [i3FInt_zero_eq_lintegral]
  congr 2
  refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have hc : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
  refine setLIntegral_congr_fun measurableSet_Ioi fun e1 (he1 : 0 < e1) => ?_
  refine setLIntegral_congr_fun_ae (measurableSet_Ioi (a := (0 : ℝ))) ?_
  have hne : ∀ᵐ e3 ∂(volume : Measure ℝ), e3 ≠ x * (1 - x) / e1 := by
    rw [ae_iff]; simp
  filter_upwards [hne] with e3 he3 (he3' : 0 < e3)
  refine i3V_lintegral_photons hc he1 he3' fun h => he3 ?_
  field_simp
  linarith

end QED.ThreeLoopD
