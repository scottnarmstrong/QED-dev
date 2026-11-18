/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCLimitCSwap
public import QED.TwoLoop.UnitSCReduce
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The corner unit C: the integration over the outer electron parameter

Section 6.3 of `docs/TWO-LOOP-UNITS.md`, stage (1) of the `S + C` link for the corner pair. After
`w = b(1-x)/x` the integrand of eq. (6.2) is `A₂/D² + A₁/D` (`cornerTerm_subst`),
`D = M + b h`, `M = Y² + (1-Y) μ_b - μ_a e`, `h = (x² + (1-x) μ_a)/x`, `b > β(x) = max(g, e x/(1-x))`
(`QED.TwoLoop.UnitSCLimit.integral_substB_swap`), with `Y = y₃ + y₄`, `g = y₃(1-Y)`, `e = y₃ y₄`.
In powers of `b`,

`A₂/D² + A₁/D = a₀/D² + a₁/(b D²) + a₂/(b² D²) + c₀/D + c₁/(b D) + c₂/(b² D) + c₃/(b³ D)`

(`cornerAX_eq`), with `c₀ = x(1-x)/2` (the coefficient `ℓ h` of the inner subdivergence of
section 2.3). Besides the five masters of the ladder this needs
`∫_β^∞ db/(b² D²)` (`hasIoiInt_master6`) and `∫_β^∞ db/(b³ D)` (`hasIoiInt_master7`). This file
proves:

* `hasIoiInt_cornerAX_sub`: for `(y₃, y₄)` in the open triangle, `0 < x < 1` and photon masses with
  `M₁, M₂ > 0`, the difference of the integrands at the two inner masses, at `b = z + β(x)`, is
  integrable on `z > 0` with integral `cornerGm la lb₁ - cornerGm la lb₂` (closed form, the
  large-`b` logarithm written as `-c₀ log(M + β h)/h`);
* `integral_cornerF4_eq_gsum`: for `m = e = 1`, `0 < m_γ < Λ`, `m_γ ≤ 1`,
  `∫_{y₃,y₄} ∫₀^∞ dz_o ∫₀^∞ dz_a cornerF4
    = ∫_{y₃,y₄} ∫₀¹ dx [G(m_γ, m_γ) - G(m_γ, Λ) - O(Λ; m_γ, Λ)]`,
  `G = cornerGm` in closed form (outer photon mass first) and `O` the `b`-integral of the
  Pauli–Villars pair with the outer photon at mass `Λ` (`cornerOut`, kept as an integral: its
  mass function `M = Y² + (1-Y) μ_b - Λ² e` can vanish, where the closed form has removable
  singularities);
* `sixteen_pi_pow_four_mul_unitF2_C_eq_gsum`: **the unit `C`** in this form, plus
  `2 δ₁ (F₂⁽²⁾(m_γ) - F₂⁽²⁾(Λ))`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology Function

namespace QED.TwoLoop.UnitSCLimit

open QED.TwoLoop.UnitLLink QED.TwoLoop.UnitSCReduce QED.WickModel QED.TwoLoop.UnitsRegulated
open QED.TwoLoop.UnitXGraph QED.TwoLoop.UnitSCGraph

/-! ### Two more masters -/

section Masters

variable {M h c : ℝ}

/-- `1/(a² (M + a h)²)`. -/
noncomputable def masterK6 (M h a : ℝ) : ℝ := 1 / (a ^ 2 * (M + a * h) ^ 2)
/-- `1/(a³ (M + a h))`. -/
noncomputable def masterK7 (M h a : ℝ) : ℝ := 1 / (a ^ 3 * (M + a * h))

theorem tendsto_one_div_mul_atTop (hM : 0 < M) :
    Tendsto (fun a : ℝ => 1 / (M * a)) atTop (𝓝 0) :=
  (tendsto_inv_atTop_zero.comp (tendsto_id.const_mul_atTop hM)).congr fun a => by simp [one_div]

/-- `∫_c^∞ da/(a² (M + a h)²) = 1/(M² c) - 2h log(1 + M/(c h))/M³ + h/(M² (M + c h))`. -/
theorem hasIoiInt_master6 (hM : 0 < M) (hh : 0 < h) (hc : 0 < c) :
    HasIoiInt (fun z => masterK6 M h (z + c))
      (1 / (M ^ 2 * c) - 2 * h * log (1 + M / (c * h)) / M ^ 3 + h / (M ^ 2 * (M + c * h))) := by
  have hd : ∀ a ∈ Ici c, HasDerivAt
      (fun a => -(1 / (M ^ 2 * a)) - 2 * h * (log a - log (M + a * h)) / M ^ 3 -
        h / (M ^ 2 * (M + a * h))) (masterK6 M h a) a := fun a ha => by
    have ha' : 0 < a := lt_of_lt_of_le hc ha
    have p1 : 0 < M + a * h := by positivity
    have h1 : HasDerivAt (fun a => 1 / (M ^ 2 * a)) (-(1 / (M ^ 2 * a ^ 2))) a := by
      have : HasDerivAt (fun a => (M ^ 2 * a)⁻¹) (-(M ^ 2 * 1) / (M ^ 2 * a) ^ 2) a :=
        ((hasDerivAt_id a).const_mul (M ^ 2)).inv (by simp only [id]; positivity)
      simp only [one_div]
      refine this.congr_deriv ?_
      field_simp
    have h2 : HasDerivAt (fun a => h / (M ^ 2 * (M + a * h)))
        (-(h * (M ^ 2 * h)) / (M ^ 2 * (M + a * h)) ^ 2) a := by
      have : HasDerivAt (fun a => (M ^ 2 * (M + a * h))⁻¹)
          (-(M ^ 2 * (1 * h)) / (M ^ 2 * (M + a * h)) ^ 2) a :=
        ((((hasDerivAt_id a).mul_const h).const_add M).const_mul (M ^ 2)).inv
          (by simp only [id]; positivity)
      have := this.const_mul h
      simp only [div_eq_mul_inv] at this ⊢
      refine this.congr_deriv ?_
      ring
    have : HasDerivAt (fun a => -(1 / (M ^ 2 * a)) - 2 * h * (log a - log (M + a * h)) / M ^ 3 -
        h / (M ^ 2 * (M + a * h)))
        (-(-(1 / (M ^ 2 * a ^ 2))) - 2 * h * (1 / a - h / (M + a * h)) / M ^ 3 -
          -(h * (M ^ 2 * h)) / (M ^ 2 * (M + a * h)) ^ 2) a :=
      ((h1.neg).sub ((((hasDerivAt_id a).log ha'.ne').sub
        (hasDerivAt_log_add p1)).const_mul (2 * h) |>.div_const (M ^ 3))).sub h2
    refine this.congr_deriv ?_
    simp only [masterK6]
    field_simp
    ring
  have hk : (∀ a ∈ Ioi c, 0 ≤ masterK6 M h a) ∨ (∀ a ∈ Ioi c, masterK6 M h a ≤ 0) :=
    Or.inl fun a ha => by
      have ha' : 0 < a := hc.trans ha
      unfold masterK6; positivity
  have hl : Tendsto (fun a => -(1 / (M ^ 2 * a)) - 2 * h * (log a - log (M + a * h)) / M ^ 3 -
      h / (M ^ 2 * (M + a * h))) atTop (𝓝 (-0 - 2 * h * -log h / M ^ 3 - h * 0 / M ^ 2)) := by
    have h3 : Tendsto (fun a => h * (1 / (M + a * h)) / M ^ 2) atTop (𝓝 (h * 0 / M ^ 2)) :=
      ((tendsto_inv_add_atTop (M := M) hh).const_mul h).div_const _
    refine ((tendsto_one_div_mul_atTop (M := M ^ 2) (by positivity)).neg.sub
      (((tendsto_log_sub_log_atTop hM.le hh).const_mul (2 * h)).div_const _)).sub h3 |>.congr
      fun a => ?_
    simp only [div_eq_mul_inv, mul_inv, one_mul]
    ring
  have := hasIoiInt_shift hd hk hl
  refine this.congr (fun z _ => rfl) ?_
  have hch : 0 < c * h := by positivity
  have e : 1 + M / (c * h) = (M + c * h) / (c * h) := by field_simp; ring
  rw [e, log_div (by positivity) hch.ne', log_mul hc.ne' hh.ne']
  field_simp
  ring

/-- `∫_c^∞ da/(a³ (M + a h)) = 1/(2 M c²) - h/(M² c) + h² log(1 + M/(c h))/M³`. -/
theorem hasIoiInt_master7 (hM : 0 < M) (hh : 0 < h) (hc : 0 < c) :
    HasIoiInt (fun z => masterK7 M h (z + c))
      (1 / (2 * M * c ^ 2) - h / (M ^ 2 * c) + h ^ 2 * log (1 + M / (c * h)) / M ^ 3) := by
  have hd : ∀ a ∈ Ici c, HasDerivAt
      (fun a => -(1 / (2 * M * (a * a))) + h * (1 / (M ^ 2 * a)) +
        h ^ 2 * (log a - log (M + a * h)) / M ^ 3) (masterK7 M h a) a := fun a ha => by
    have ha' : 0 < a := lt_of_lt_of_le hc ha
    have p1 : 0 < M + a * h := by positivity
    have h1 : HasDerivAt (fun a => 1 / (M ^ 2 * a)) (-(1 / (M ^ 2 * a ^ 2))) a := by
      have : HasDerivAt (fun a => (M ^ 2 * a)⁻¹) (-(M ^ 2 * 1) / (M ^ 2 * a) ^ 2) a :=
        ((hasDerivAt_id a).const_mul (M ^ 2)).inv (by simp only [id]; positivity)
      simp only [one_div]
      refine this.congr_deriv ?_
      field_simp
    have h0 : HasDerivAt (fun a => 1 / (2 * M * (a * a)))
        (-(2 * M * (1 * a + a * 1)) / (2 * M * (a * a)) ^ 2) a := by
      have : HasDerivAt (fun a => (2 * M * (a * a))⁻¹)
          (-(2 * M * (1 * a + a * 1)) / (2 * M * (a * a)) ^ 2) a :=
        (((hasDerivAt_id' a).mul (hasDerivAt_id' a)).const_mul (2 * M)).inv
          (mul_ne_zero (by positivity) (mul_ne_zero ha'.ne' ha'.ne'))
      simp only [one_div]
      exact this
    have : HasDerivAt (fun a => -(1 / (2 * M * (a * a))) + h * (1 / (M ^ 2 * a)) +
        h ^ 2 * (log a - log (M + a * h)) / M ^ 3)
        (-(-(2 * M * (1 * a + a * 1)) / (2 * M * (a * a)) ^ 2) + h * -(1 / (M ^ 2 * a ^ 2)) +
          h ^ 2 * (1 / a - h / (M + a * h)) / M ^ 3) a :=
      ((h0.neg).add (h1.const_mul h)).add ((((hasDerivAt_id a).log ha'.ne').sub
        (hasDerivAt_log_add p1)).const_mul (h ^ 2) |>.div_const (M ^ 3))
    refine this.congr_deriv ?_
    simp only [masterK7]
    field_simp
    ring
  have hk : (∀ a ∈ Ioi c, 0 ≤ masterK7 M h a) ∨ (∀ a ∈ Ioi c, masterK7 M h a ≤ 0) :=
    Or.inl fun a ha => by
      have ha' : 0 < a := hc.trans ha
      unfold masterK7; positivity
  have hl : Tendsto (fun a => -(1 / (2 * M * (a * a))) + h * (1 / (M ^ 2 * a)) +
      h ^ 2 * (log a - log (M + a * h)) / M ^ 3) atTop (𝓝 (-0 + h * 0 + h ^ 2 * -log h / M ^ 3)) := by
    have h0 : Tendsto (fun a : ℝ => 1 / (2 * M * (a * a))) atTop (𝓝 0) := by
      have : Tendsto (fun a : ℝ => 2 * M * (a * a)) atTop atTop :=
        (tendsto_id.atTop_mul_atTop₀ tendsto_id).const_mul_atTop (by positivity)
      exact (tendsto_inv_atTop_zero.comp this).congr fun a => by simp [one_div]
    exact (h0.neg.add ((tendsto_one_div_mul_atTop (M := M ^ 2) (by positivity)).const_mul h)).add
      (((tendsto_log_sub_log_atTop hM.le hh).const_mul (h ^ 2)).div_const _)
  have := hasIoiInt_shift hd hk hl
  refine this.congr (fun z _ => rfl) ?_
  have hch : 0 < c * h := by positivity
  have e : 1 + M / (c * h) = (M + c * h) / (c * h) := by field_simp; ring
  rw [e, log_div (by positivity) hch.ne', log_mul hc.ne' hh.ne']
  field_simp
  ring

end Masters

/-! ### The corner integrand in the variables `(b, x)` -/

/-- `g = y₃ (1 - y₃ - y₄)`, the minimum of the outer electron parameter. -/
noncomputable def cornerG (y3 y4 : ℝ) : ℝ := y3 * (1 - y3 - y4)

/-- **The mass function** `M = Y² + (1-Y) μ_b - μ_a e` of the corner (inner photon mass `lb`,
outer photon mass `la`, `Y = y₃ + y₄`, `e = y₃ y₄`). -/
noncomputable def cornerMass (la lb y3 y4 : ℝ) : ℝ :=
  (y3 + y4) ^ 2 + (1 - (y3 + y4)) * lb ^ 2 - la ^ 2 * (y3 * y4)

/-- `q = x(2-x)(1-2y₃)`. -/
noncomputable def cornerQ (x y3 : ℝ) : ℝ := x * (2 - x) * (1 - 2 * y3)
/-- `r = 3x(1-2y₃)`. -/
noncomputable def cornerR (x y3 : ℝ) : ℝ := 3 * x * (1 - 2 * y3)

/-- `a₀ = x p₁/4`. -/
noncomputable def cornerA0 (x y3 y4 : ℝ) : ℝ := x / 4 * cornerP1 x y3 y4
/-- `a₁ = x g (q - p₁)/4`. -/
noncomputable def cornerA1 (x y3 y4 : ℝ) : ℝ :=
  x / 4 * cornerG y3 y4 * (cornerQ x y3 - cornerP1 x y3 y4)
/-- `a₂ = -x q g²/4`. -/
noncomputable def cornerA2 (x y3 y4 : ℝ) : ℝ := -(x / 4 * cornerQ x y3 * cornerG y3 y4 ^ 2)
/-- `c₀ = x(1-x)/2`. -/
noncomputable def cornerC0 (x : ℝ) : ℝ := x * (1 - x) / 2
/-- `c₁ = -x (p₂ - 2(x-1) g)/4`. -/
noncomputable def cornerC1 (x y3 y4 : ℝ) : ℝ :=
  -(x / 4 * (cornerP2 x y3 y4 - 2 * (x - 1) * cornerG y3 y4))
/-- `c₂ = x g (r + p₂)/4`. -/
noncomputable def cornerC2 (x y3 y4 : ℝ) : ℝ :=
  x / 4 * cornerG y3 y4 * (cornerR x y3 + cornerP2 x y3 y4)
/-- `c₃ = -x r g²/4`. -/
noncomputable def cornerC3 (x y3 y4 : ℝ) : ℝ := -(x / 4 * cornerR x y3 * cornerG y3 y4 ^ 2)

/-- **The integrand of eq. (6.2) times the Jacobian** `b/x²` of `w = b(1-x)/x`, at outer photon
mass `la` and inner photon mass `lb`, in the frame `y₃ + y₄ + z_b = 1`. -/
noncomputable def cornerAX (la lb y3 y4 x b : ℝ) : ℝ :=
  cornerTerm (la ^ 2) (lb ^ 2) (b - cornerG y3 y4) y3 y4 (b * (1 - x) / x - y3 * y4)
    (1 - y3 - y4) * (b / x ^ 2)

/-- The `b`-integral in closed form, with `A = log(M + β h)` and `L = log(1 + M/(β h))`:
`-c₀ A/h + a₀/(h(M + βh)) + a₁ (L/M² - 1/(M(M + βh)))
  + a₂ (1/(M² β) - 2hL/M³ + h/(M²(M + βh))) + c₁ L/M + c₂ (1/(Mβ) - hL/M²)
  + c₃ (1/(2Mβ²) - h/(M²β) + h² L/M³)`. -/
noncomputable def cForm (a₀ a₁ a₂ c₀ c₁ c₂ c₃ β h M A L : ℝ) : ℝ :=
  c₀ * (-A / h) + a₀ * (1 / (h * (M + β * h))) + a₁ * (L / M ^ 2 - 1 / (M * (M + β * h))) +
    a₂ * (1 / (M ^ 2 * β) - 2 * h * L / M ^ 3 + h / (M ^ 2 * (M + β * h))) + c₁ * (L / M) +
    c₂ * (1 / (M * β) - h * L / M ^ 2) +
    c₃ * (1 / (2 * M * β ^ 2) - h / (M ^ 2 * β) + h ^ 2 * L / M ^ 3)

/-- **The `x`-integrand of eq. (6.3) at outer photon mass `la` and inner photon mass `lb`**:
the `b`-integral of eq. (6.2) over `b > β(x)`, in closed form (the large-`b` logarithm written as
`-c₀ log(M + β h)/h`). -/
noncomputable def cornerGm (la lb y3 y4 x : ℝ) : ℝ :=
  cForm (cornerA0 x y3 y4) (cornerA1 x y3 y4) (cornerA2 x y3 y4) (cornerC0 x) (cornerC1 x y3 y4)
    (cornerC2 x y3 y4) (cornerC3 x y3 y4) (betaG (cornerG y3 y4) (y3 * y4) x)
    (ladderInnerMass 1 la x / x) (cornerMass la lb y3 y4)
    (log (cornerMass la lb y3 y4 +
      betaG (cornerG y3 y4) (y3 * y4) x * (ladderInnerMass 1 la x / x)))
    (log (1 + cornerMass la lb y3 y4 /
      (betaG (cornerG y3 y4) (y3 * y4) x * (ladderInnerMass 1 la x / x))))

theorem cornerMass_pos {la lb y3 y4 : ℝ} (h3 : 0 < y3) (h4 : 0 < y4) (hY : y3 + y4 ≤ 1)
    (hla : la ^ 2 ≤ 1) : 0 < cornerMass la lb y3 y4 := by
  unfold cornerMass
  have h1 : 0 ≤ (1 - (y3 + y4)) * lb ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : la ^ 2 * (y3 * y4) ≤ y3 * y4 := by
    have := mul_pos h3 h4
    nlinarith
  nlinarith [mul_pos h3 h4, sq_nonneg y3, sq_nonneg y4]

/-- **The integrand in the variables `(b, x)`** as a combination of the masters. -/
theorem cornerAX_eq {la lb y3 y4 x b : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hla : 0 < la) (hb : 0 < b)
    (hD : 0 < cornerMass la lb y3 y4 + b * (ladderInnerMass 1 la x / x)) :
    cornerAX la lb y3 y4 x b =
      cornerC0 x * (1 / (cornerMass la lb y3 y4 + b * (ladderInnerMass 1 la x / x))) +
        cornerA0 x y3 y4 * masterK4 (cornerMass la lb y3 y4) (ladderInnerMass 1 la x / x) b +
        cornerA1 x y3 y4 * masterK5 (cornerMass la lb y3 y4) (ladderInnerMass 1 la x / x) b +
        cornerA2 x y3 y4 * masterK6 (cornerMass la lb y3 y4) (ladderInnerMass 1 la x / x) b +
        cornerC1 x y3 y4 * masterK2 (cornerMass la lb y3 y4) (ladderInnerMass 1 la x / x) b +
        cornerC2 x y3 y4 * masterK3 (cornerMass la lb y3 y4) (ladderInnerMass 1 la x / x) b +
        cornerC3 x y3 y4 * masterK7 (cornerMass la lb y3 y4) (ladderInnerMass 1 la x / x) b := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have eD : (y3 + y4) ^ 2 + (1 - (y3 + y4)) * lb ^ 2 - la ^ 2 * (y3 * y4) +
      b * ((x ^ 2 + (1 - x) * la ^ 2) / x) =
      cornerMass la lb y3 y4 + b * (ladderInnerMass 1 la x / x) := by
    unfold cornerMass ladderInnerMass; ring
  have hD' : 0 < (y3 + y4) ^ 2 + (1 - (y3 + y4)) * lb ^ 2 - la ^ 2 * (y3 * y4) +
      b * ((x ^ 2 + (1 - x) * la ^ 2) / x) := eD ▸ hD
  unfold cornerAX
  rw [show cornerG y3 y4 = y3 * (1 - y3 - y4) from rfl, cornerTerm_subst hb hx hD', eD]
  have hL0 : ladderInnerMass 1 la x ≠ 0 :=
    (ladderInnerMass_pos one_pos hla ⟨hx.1.le, hx.2.le⟩).ne'
  have hD0 := hD.ne'
  have hb0 := hb.ne'
  unfold masterK2 masterK3 masterK4 masterK5 masterK6 masterK7 cornerA0 cornerA1 cornerA2 cornerC0
    cornerC1 cornerC2 cornerC3 cornerQ cornerR cornerG
  field_simp
  ring

/-- **The `b`-integration** (section 6.3 of the document): for `(y₃, y₄)` in the open triangle,
`0 < x < 1`, an outer photon mass `la > 0` and inner photon masses with positive mass functions,
the difference of the integrands at the two inner masses, at `b = z + β(x)`, is integrable on
`z > 0` with integral `cornerGm la lb₁ - cornerGm la lb₂`. -/
theorem hasIoiInt_cornerAX_sub {la lb₁ lb₂ y3 y4 x : ℝ} (h3 : 0 < y3)
    (hY : y3 + y4 < 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hla : 0 < la)
    (hM₁ : 0 < cornerMass la lb₁ y3 y4) (hM₂ : 0 < cornerMass la lb₂ y3 y4) :
    HasIoiInt (fun z => cornerAX la lb₁ y3 y4 x (z + betaG (cornerG y3 y4) (y3 * y4) x) -
        cornerAX la lb₂ y3 y4 x (z + betaG (cornerG y3 y4) (y3 * y4) x))
      (cornerGm la lb₁ y3 y4 x - cornerGm la lb₂ y3 y4 x) := by
  have hg : 0 < cornerG y3 y4 := by unfold cornerG; have : 0 < 1 - y3 - y4 := by linarith
                                    positivity
  have hh := ladderH_pos hla hx
  have hβ := betaG_pos (e := y3 * y4) (x := x) hg
  set M₁ := cornerMass la lb₁ y3 y4 with hM₁def
  set M₂ := cornerMass la lb₂ y3 y4 with hM₂def
  set h := ladderInnerMass 1 la x / x with hhdef
  set β := betaG (cornerG y3 y4) (y3 * y4) x with hβdef
  have I1 := hasIoiInt_master1 hM₁ hM₂ hh hβ
  have I2 := (hasIoiInt_master2 hM₁ hh hβ).sub (hasIoiInt_master2 hM₂ hh hβ)
  have I3 := (hasIoiInt_master3 hM₁ hh hβ).sub (hasIoiInt_master3 hM₂ hh hβ)
  have I4 := (hasIoiInt_master4 hM₁ hh hβ).sub (hasIoiInt_master4 hM₂ hh hβ)
  have I5 := (hasIoiInt_master5 hM₁ hh hβ).sub (hasIoiInt_master5 hM₂ hh hβ)
  have I6 := (hasIoiInt_master6 hM₁ hh hβ).sub (hasIoiInt_master6 hM₂ hh hβ)
  have I7 := (hasIoiInt_master7 hM₁ hh hβ).sub (hasIoiInt_master7 hM₂ hh hβ)
  have I := ((((((I1.const_mul (cornerC0 x)).add (I4.const_mul (cornerA0 x y3 y4))).add
    (I5.const_mul (cornerA1 x y3 y4))).add (I6.const_mul (cornerA2 x y3 y4))).add
    (I2.const_mul (cornerC1 x y3 y4))).add (I3.const_mul (cornerC2 x y3 y4))).add
    (I7.const_mul (cornerC3 x y3 y4))
  refine I.congr (fun z hz => ?_) ?_
  · have hb : 0 < z + β := by simp only [mem_Ioi] at hz; linarith
    rw [cornerAX_eq hx hla hb (by positivity), cornerAX_eq hx hla hb (by positivity)]
    ring
  · simp only [cornerGm, cForm]
    rw [← hM₁def, ← hM₂def, ← hhdef, ← hβdef]
    have h1 : log (M₂ + β * h) - log (M₁ + β * h) = -log (M₁ + β * h) - -log (M₂ + β * h) := by
      ring
    rw [div_eq_mul_inv (log (M₂ + β * h) - log (M₁ + β * h)), h1]
    ring

/-! ### The graph half after the `b`-integration -/

/-- **The `b`-integral of the Pauli–Villars pair with the outer photon at mass `la`** (inner
masses `lb₁`, `lb₂`), kept as an integral. -/
noncomputable def cornerOut (la lb₁ lb₂ y3 y4 x : ℝ) : ℝ :=
  ∫ z in Ioi (0 : ℝ), (cornerAX la lb₁ y3 y4 x (z + betaG (cornerG y3 y4) (y3 * y4) x) -
    cornerAX la lb₂ y3 y4 x (z + betaG (cornerG y3 y4) (y3 * y4) x))

/-- **The `x`-integrand of the corner graph half**:
`G(m_γ, m_γ) - G(m_γ, Λ) - O(Λ; m_γ, Λ)` (outer mass first). -/
noncomputable def cornerGSum (mγ Λ y3 y4 x : ℝ) : ℝ :=
  cornerGm mγ mγ y3 y4 x - cornerGm mγ Λ y3 y4 x - cornerOut Λ mγ Λ y3 y4 x

theorem measurable_cornerSlice (P : Params) (y3 y4 : ℝ) :
    Measurable (uncurry fun zo za => cornerF4 P ![zo, y3, y4, za, 1 - (y3 + y4)]) := by
  change Measurable fun p : ℝ × ℝ => cornerF4 P ![p.1, y3, y4, p.2, 1 - (y3 + y4)]
  simp only [cornerF4, cornerTerm, gCW, gCM1, gCM2, gCU, gCE, gCEn, cpM1pa, cpM1pb, cpM1pc,
    cpM1pd, cpM2pa, cpM2pb, cpM2pc, cpM2pd, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons]
  fun_prop

theorem substB_cornerSlice (P : Params) (y3 y4 x z : ℝ) :
    substB (fun zo za => cornerF4 P ![zo, y3, y4, za, 1 - (y3 + y4)]) (cornerG y3 y4) (y3 * y4)
        x z =
      (cornerAX P.mγ P.mγ y3 y4 x (z + betaG (cornerG y3 y4) (y3 * y4) x) -
          cornerAX P.mγ P.Λ y3 y4 x (z + betaG (cornerG y3 y4) (y3 * y4) x)) -
        (cornerAX P.Λ P.mγ y3 y4 x (z + betaG (cornerG y3 y4) (y3 * y4) x) -
          cornerAX P.Λ P.Λ y3 y4 x (z + betaG (cornerG y3 y4) (y3 * y4) x)) := by
  have e1 : z + (betaG (cornerG y3 y4) (y3 * y4) x - cornerG y3 y4) =
      z + betaG (cornerG y3 y4) (y3 * y4) x - cornerG y3 y4 := by ring
  have e2 : (1 : ℝ) - (y3 + y4) = 1 - y3 - y4 := by ring
  simp only [substB, cornerF4, cornerAX, e1, e2, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- For almost every `(y₃, y₄)` in the triangle, the slice of the corner integrand is integrable
on `(0, ∞)²`. -/
theorem ae_integrable_cornerSlice {P : Params} (hm : P.m = 1) (he : P.e = 1) (hmγ : 0 < P.mγ)
    (hΛ : P.mγ < P.Λ) :
    ∀ᵐ p ∂(volume.restrict innerTriangle),
      Integrable (uncurry fun zo za => cornerF4 P ![zo, p.1, p.2, za, 1 - (p.1 + p.2)])
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  obtain ⟨hI, -⟩ := sixteen_pi_pow_four_mul_openZero_Cp_eq_chengWu hm he hmγ hΛ
  have he' := measurePreserving_splitInner.symm
  have hint := (he'.integrableOn_comp_preimage splitInner.symm.measurableEmbedding).mpr hI
  rw [preimage_splitInner_symm] at hint
  have hint' : Integrable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      cornerF4 P (Fin.snoc (splitInner.symm q) (1 - (splitInner.symm q 1 + splitInner.symm q 2))))
      ((volume.restrict innerTriangle).prod
        ((volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))) := by
    rw [Measure.prod_restrict]; exact hint
  filter_upwards [hint'.prod_right_ae] with p hp
  rw [← Measure.prod_restrict] at hp
  refine hp.congr (ae_of_all _ fun q => ?_)
  simp only [splitInner_symm_apply, uncurry]
  rfl

/-- **The corner graph half after the `b`-integration** (`m = e = 1`, `0 < m_γ < Λ`, `m_γ ≤ 1`):
`∫_{y₃,y₄} ∫₀^∞ ∫₀^∞ cornerF4 = ∫_{y₃,y₄} ∫₀¹ dx [G(m_γ, m_γ) - G(m_γ, Λ) - O(Λ; m_γ, Λ)]`. -/
theorem integral_cornerF4_eq_gsum {P : Params} (hm : P.m = 1) (he : P.e = 1) (hmγ : 0 < P.mγ)
    (hΛ : P.mγ < P.Λ) (hmγ1 : P.mγ ≤ 1) :
    ∫ p in innerTriangle, ∫ zo in Ioi (0 : ℝ), ∫ za in Ioi (0 : ℝ),
        cornerF4 P ![zo, p.1, p.2, za, 1 - (p.1 + p.2)] =
      ∫ p in innerTriangle, ∫ x in Ioo (0 : ℝ) 1, cornerGSum P.mγ P.Λ p.1 p.2 x := by
  have hm2 : P.mγ ^ 2 ≤ 1 := by nlinarith
  refine integral_congr_ae ?_
  filter_upwards [ae_integrable_cornerSlice hm he hmγ hΛ,
    ae_restrict_mem measurableSet_innerTriangle] with p hp hpm
  obtain ⟨h3, h4, hY⟩ := hpm
  have hg : 0 < cornerG p.1 p.2 := by
    unfold cornerG; have : 0 < 1 - p.1 - p.2 := by linarith
    positivity
  obtain ⟨hae, heq⟩ := integral_substB_swap hg (mul_pos h3 h4) (measurable_cornerSlice P p.1 p.2) hp
  rw [heq]
  refine integral_congr_ae ?_
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with x hx hxm
  have hin := hasIoiInt_cornerAX_sub h3 hY hxm hmγ (cornerMass_pos h3 h4 hY.le hm2)
    (cornerMass_pos h3 h4 hY.le hm2) (lb₁ := P.mγ) (lb₂ := P.Λ)
  have hout : IntegrableOn (fun z =>
      cornerAX P.Λ P.mγ p.1 p.2 x (z + betaG (cornerG p.1 p.2) (p.1 * p.2) x) -
        cornerAX P.Λ P.Λ p.1 p.2 x (z + betaG (cornerG p.1 p.2) (p.1 * p.2) x)) (Ioi 0) := by
    refine (hin.1.sub hx).congr_fun (fun z _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, substB_cornerSlice]
    ring
  have e : (fun z => substB (fun zo za => cornerF4 P ![zo, p.1, p.2, za, 1 - (p.1 + p.2)])
      (cornerG p.1 p.2) (p.1 * p.2) x z) = fun z =>
      (cornerAX P.mγ P.mγ p.1 p.2 x (z + betaG (cornerG p.1 p.2) (p.1 * p.2) x) -
          cornerAX P.mγ P.Λ p.1 p.2 x (z + betaG (cornerG p.1 p.2) (p.1 * p.2) x)) -
        (cornerAX P.Λ P.mγ p.1 p.2 x (z + betaG (cornerG p.1 p.2) (p.1 * p.2) x) -
          cornerAX P.Λ P.Λ p.1 p.2 x (z + betaG (cornerG p.1 p.2) (p.1 * p.2) x)) := by
    funext z
    exact substB_cornerSlice P p.1 p.2 x z
  rw [e, integral_sub hin.1 hout, hin.2, cornerGSum, cornerOut]

/-- **The unit `C` after the `b`-integration** (`m = 1`, `0 < m_γ < Λ`, `m_γ ≤ 1`, `d₁` fixed by
the frozen charge condition):
`16π⁴ unitF2 C P₁ = 2 ∫_{y₃,y₄} ∫₀¹ G_Σ + 2 δ₁ (F₂⁽²⁾(m_γ) - F₂⁽²⁾(Λ))`. -/
theorem sixteen_pi_pow_four_mul_unitF2_C_eq_gsum (P : Params) (hm : P.m = 1) (hm0 : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ0 : 0 < P.Λ) (hΛ : P.mγ < P.Λ) (hmγ1 : P.mγ ≤ 1) {d₁ d₂ dm d₃ : ℝ}
    (hch : QED.OneLoop.IsChargeNormalized 1 (1 + d₁) P.m P.mγ P.Λ hm0 hmγ hΛ0) :
    16 * (π : ℂ) ^ 4 * unitF2 .C (atUnitCharge P d₁ d₂ dm d₃) =
      ((2 * ∫ p in innerTriangle, ∫ x in Ioo (0 : ℝ) 1, cornerGSum P.mγ P.Λ p.1 p.2 x : ℝ) : ℂ) +
        ((2 * (ladderDeltaOne P.m P.mγ P.Λ * (oneLoopF2 P.m P.mγ - oneLoopF2 P.m P.Λ)) : ℝ) :
          ℂ) := by
  rw [sixteen_pi_pow_four_mul_unitF2_C P hm hm0 hmγ hΛ0 hΛ hch]
  congr 3
  exact integral_cornerF4_eq_gsum (P := atUnitCharge P d₁ d₂ dm d₃) hm rfl hmγ hΛ hmγ1

end QED.TwoLoop.UnitSCLimit

end
