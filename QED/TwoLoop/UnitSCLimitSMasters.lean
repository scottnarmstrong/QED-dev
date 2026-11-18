/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCReduce
public import QED.TwoLoop.UnitLCloseSubst
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The self-energy unit S: the integration over the outer electron parameter

Section 5.3 of `docs/TWO-LOOP-UNITS.md`, stage (1) of the `S + C` link for the self-energy pair
(the analogue of `QED/TwoLoop/UnitLCloseMasters.lean` and `QED/TwoLoop/UnitLCloseSubst.lean`).
After `z_a = a(1-x)/x` the integrand of eq. (5.1) is `A₂/D² + A₁/D`, `D = M + a h`, with
`M = Y² + (1-Y) μ_b` (inner photon mass `μ_b`), `h = (x² + (1-x) μ_a)/x` (outer photon mass `μ_a`),
`c = Y(1-Y)` and

`A₂ = k₂ (a - c)²/a`, `A₁ = k₁ (a - c)²/a²`,
`k₂ = x²(x-1)(Yx - Y - x + 3)/4`, `k₁ = -x(x-1)(2Yx + Y - 2x + 2)/2`.

With `a/D² = (1/D - M/D²)/h` this is a combination of the five masters of the ladder
(`selfAX_eq`): `(k₁ + k₂/h)/D + (-k₂ M/h - 2c k₂)/D² + k₂ c²/(a D²) - 2c k₁/(a D) + k₁ c²/(a² D)`.
The first term is not integrable at large `a`, but its coefficient does not depend on `M`, so the
large-`a` logarithm cancels between the two inner Pauli–Villars terms. This file proves:

* `hasIoiInt_selfAX_sub`: for `0 < Y, x < 1` and photon masses `la, lb₁, lb₂ > 0`, the difference
  of the integrands at the two inner photon masses, at `a = z + Y(1-Y)`, is integrable on `z > 0`
  with integral `selfGm la lb₁ Y x - selfGm la lb₂ Y x`, where `selfGm la lb` is the `x`-integrand
  `E_S` of eq. (5.3) of the document (with the large-`a` logarithm written as `-log(M + c h)`);
* `integral_selfDocSum_eq_gsum`: for `m = e = 1` and `0 < m_γ < Λ`,
  `∫₀¹ dY ∫₀^∞ dz_o ∫₀^∞ dz_a selfDocSum = ∫_{0<Y<1} ∫_{0<x<1} G_Σ(Y, x)`, with
  `G_Σ = G(m_γ, m_γ) - G(m_γ, Λ) - G(Λ, m_γ) + G(Λ, Λ)` (`selfGSum`, outer mass first);
* `sixteen_pi_pow_four_mul_unitF2_S_eq_gsum`: **the unit `S`**,
  `16π⁴ unitF2 S P₁ = 2 ∫∫ G_Σ + 16π⁴ sCtHalf P₁`, `P₁ = atUnitCharge P d₁ d₂ d_m d₃`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology Function

namespace QED.TwoLoop.UnitSCLimit

open QED.TwoLoop.UnitLLink QED.TwoLoop.UnitSCReduce QED.WickModel QED.TwoLoop.UnitsRegulated

/-! ### The integrand in the variables `(a, x)` -/

/-- The coefficient `k₂ = x²(x-1)(Yx - Y - x + 3)/4` of `A₂ = k₂ (a - c)²/a` in eq. (5.1). -/
noncomputable def selfK2 (Y x : ℝ) : ℝ := x ^ 2 * (x - 1) * (Y * x - Y - x + 3) / 4

/-- The coefficient `k₁ = -x(x-1)(2Yx + Y - 2x + 2)/2` of `A₁ = k₁ (a - c)²/a²` in eq. (5.1). -/
noncomputable def selfK1 (Y x : ℝ) : ℝ := -(x * (x - 1) * (2 * Y * x + Y - 2 * x + 2)) / 2

/-- **The integrand of eq. (5.1) times the Jacobian** `a/x²` of `z_a = a(1-x)/x`, at outer photon
mass `la` and inner photon mass `lb`. -/
noncomputable def selfAX (la lb Y x a : ℝ) : ℝ :=
  selfDocF Y a (a * (1 - x) / x) (la ^ 2) (lb ^ 2) * (a / x ^ 2)

/-- The shape of the `a`-integral: with `A = log(M + c h)` and `B = log(1 + M/(c h))`,
`-(k₁ + k₂/h) A/h + (-k₂ M/h - 2c k₂)/(h(M + ch)) + k₂ c² (B/M² - 1/(M(M + ch)))
  - 2c k₁ B/M + k₁ c² (1/(Mc) - h B/M²)`. -/
noncomputable def sForm (k₁ k₂ c h M A B : ℝ) : ℝ :=
  -(k₁ + k₂ / h) * A / h + (-(k₂ * M / h) - 2 * c * k₂) * (1 / (h * (M + c * h))) +
    k₂ * c ^ 2 * (B / M ^ 2 - 1 / (M * (M + c * h))) - 2 * c * k₁ * (B / M) +
    k₁ * c ^ 2 * (1 / (M * c) - h * B / M ^ 2)

/-- **The `x`-integrand of eq. (5.3) at outer photon mass `la` and inner photon mass `lb`**
(the `a`-integral of eq. (5.1) over `a > c`, with the large-`a` logarithm written as
`-log(M + c h)`). -/
noncomputable def selfGm (la lb Y x : ℝ) : ℝ :=
  sForm (selfK1 Y x) (selfK2 Y x) (Y * (1 - Y)) (ladderInnerMass 1 la x / x)
    (ladderInnerMass 1 lb Y)
    (log (ladderInnerMass 1 lb Y + Y * (1 - Y) * (ladderInnerMass 1 la x / x)))
    (log (1 + ladderInnerMass 1 lb Y / (Y * (1 - Y) * (ladderInnerMass 1 la x / x))))

/-- **The integrand in the variables `(a, x)`** as a combination of the masters. -/
theorem selfAX_eq {la lb Y x a : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hla : 0 < la) (hlb : 0 < lb) (ha : 0 < a) :
    selfAX la lb Y x a =
      (selfK1 Y x + selfK2 Y x / (ladderInnerMass 1 la x / x)) *
          (1 / (ladderInnerMass 1 lb Y + a * (ladderInnerMass 1 la x / x))) +
        (-(selfK2 Y x * ladderInnerMass 1 lb Y / (ladderInnerMass 1 la x / x)) -
            2 * (Y * (1 - Y)) * selfK2 Y x) *
          masterK4 (ladderInnerMass 1 lb Y) (ladderInnerMass 1 la x / x) a +
        selfK2 Y x * (Y * (1 - Y)) ^ 2 *
          masterK5 (ladderInnerMass 1 lb Y) (ladderInnerMass 1 la x / x) a -
        2 * (Y * (1 - Y)) * selfK1 Y x *
          masterK2 (ladderInnerMass 1 lb Y) (ladderInnerMass 1 la x / x) a +
        selfK1 Y x * (Y * (1 - Y)) ^ 2 *
          masterK3 (ladderInnerMass 1 lb Y) (ladderInnerMass 1 la x / x) a := by
  have hM := ladderInnerMass_pos one_pos hlb ⟨hY.1.le, hY.2.le⟩
  have hh := ladderH_pos hla hx
  have hx0 : x ≠ 0 := hx.1.ne'
  have hD : 0 < ladderInnerMass 1 lb Y + a * (ladderInnerMass 1 la x / x) := by positivity
  unfold selfAX
  rw [selfDocF_subst hY ha hx (sq_nonneg la) (sq_nonneg lb)]
  have eD : Y ^ 2 + (1 - Y) * lb ^ 2 + a * ((x ^ 2 + (1 - x) * la ^ 2) / x) =
      ladderInnerMass 1 lb Y + a * (ladderInnerMass 1 la x / x) := by
    unfold ladderInnerMass; ring
  rw [eD]
  have hh0 := hh.ne'
  have hD0 := hD.ne'
  have hM0 := hM.ne'
  have hL0 : ladderInnerMass 1 la x ≠ 0 :=
    (ladderInnerMass_pos one_pos hla ⟨hx.1.le, hx.2.le⟩).ne'
  have ha0 := ha.ne'
  unfold masterK2 masterK3 masterK4 masterK5 selfK1 selfK2
  field_simp
  ring

/-- `sForm` as the combination of the master values. -/
theorem sForm_eq_masters {k₁ k₂ c h M A B : ℝ} :
    sForm k₁ k₂ c h M A B =
      (k₁ + k₂ / h) * (-A / h) + (-(k₂ * M / h) - 2 * c * k₂) * (1 / (h * (M + c * h))) +
        k₂ * c ^ 2 * (B / M ^ 2 - 1 / (M * (M + c * h))) - 2 * c * k₁ * (B / M) +
        k₁ * c ^ 2 * (1 / (M * c) - h * B / M ^ 2) := by
  unfold sForm
  ring

/-- **The `a`-integration** (section 5.3 of the document): for `0 < Y, x < 1` and photon masses
`la, lb₁, lb₂ > 0`, the difference of the integrands at the two inner photon masses, at
`a = z + Y(1-Y)`, is integrable on `z > 0` with integral `selfGm la lb₁ - selfGm la lb₂`. -/
theorem hasIoiInt_selfAX_sub {la lb₁ lb₂ Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hla : 0 < la) (hlb₁ : 0 < lb₁) (hlb₂ : 0 < lb₂) :
    HasIoiInt (fun z => selfAX la lb₁ Y x (z + Y * (1 - Y)) - selfAX la lb₂ Y x (z + Y * (1 - Y)))
      (selfGm la lb₁ Y x - selfGm la lb₂ Y x) := by
  have hM₁ := ladderInnerMass_pos one_pos hlb₁ ⟨hY.1.le, hY.2.le⟩
  have hM₂ := ladderInnerMass_pos one_pos hlb₂ ⟨hY.1.le, hY.2.le⟩
  have hh := ladderH_pos hla hx
  have hc : 0 < Y * (1 - Y) := mul_pos hY.1 (by linarith [hY.2])
  set M₁ := ladderInnerMass 1 lb₁ Y with hM₁def
  set M₂ := ladderInnerMass 1 lb₂ Y with hM₂def
  set h := ladderInnerMass 1 la x / x with hhdef
  set c := Y * (1 - Y) with hcdef
  have I1 := hasIoiInt_master1 hM₁ hM₂ hh hc
  have I2 := (hasIoiInt_master2 hM₁ hh hc).sub (hasIoiInt_master2 hM₂ hh hc)
  have I3 := (hasIoiInt_master3 hM₁ hh hc).sub (hasIoiInt_master3 hM₂ hh hc)
  have I4 := (hasIoiInt_master4 hM₁ hh hc).sub (hasIoiInt_master4 hM₂ hh hc)
  have I5 := (hasIoiInt_master5 hM₁ hh hc).sub (hasIoiInt_master5 hM₂ hh hc)
  have I4a := (hasIoiInt_master4 hM₁ hh hc).const_mul
    (-(selfK2 Y x * M₁ / h) - 2 * c * selfK2 Y x)
  have I4b := (hasIoiInt_master4 hM₂ hh hc).const_mul
    (-(selfK2 Y x * M₂ / h) - 2 * c * selfK2 Y x)
  have I := ((((I1.const_mul (selfK1 Y x + selfK2 Y x / h)).add (I4a.sub I4b)).add
    (I5.const_mul (selfK2 Y x * c ^ 2))).sub (I2.const_mul (2 * c * selfK1 Y x))).add
    (I3.const_mul (selfK1 Y x * c ^ 2))
  refine I.congr (fun z hz => ?_) ?_
  · have ha : 0 < z + c := by simp only [mem_Ioi] at hz; linarith
    rw [selfAX_eq hY hx hla hlb₁ ha, selfAX_eq hY hx hla hlb₂ ha]
    ring
  · simp only [selfGm, sForm_eq_masters]
    rw [← hM₁def, ← hM₂def, ← hhdef, ← hcdef]
    have h1 : log (M₂ + c * h) - log (M₁ + c * h) = -log (M₁ + c * h) - -log (M₂ + c * h) := by
      ring
    rw [div_eq_mul_inv (log (M₂ + c * h) - log (M₁ + c * h)), h1]
    ring

/-! ### The graph half after the `a`-integration -/

/-- **The `x`-integrand after the `a`-integration, summed over the photon masses with the
Pauli–Villars signs**: `G(m_γ, m_γ) - G(m_γ, Λ) - G(Λ, m_γ) + G(Λ, Λ)` (outer mass first). -/
noncomputable def selfGSum (mγ Λ Y x : ℝ) : ℝ :=
  selfGm mγ mγ Y x - selfGm mγ Λ Y x - selfGm Λ mγ Y x + selfGm Λ Λ Y x

theorem measurable_selfDocSum (P : QED.WickModel.Params) (Y : ℝ) :
    Measurable (uncurry fun zo za => selfDocSum P Y zo za) := by
  change Measurable fun p : ℝ × ℝ => selfDocSum P Y p.1 p.2
  unfold selfDocSum selfDocF
  fun_prop

theorem substT_selfDocSum (P : QED.WickModel.Params) (Y x zo : ℝ) :
    substT (fun zo za => selfDocSum P Y zo za) (Y * (1 - Y)) zo x =
      (selfAX P.mγ P.mγ Y x (zo + Y * (1 - Y)) - selfAX P.mγ P.Λ Y x (zo + Y * (1 - Y))) -
        (selfAX P.Λ P.mγ Y x (zo + Y * (1 - Y)) - selfAX P.Λ P.Λ Y x (zo + Y * (1 - Y))) := by
  simp only [substT, selfDocSum, selfAX]
  ring

/-- The inner integral over `z_o` is `G_Σ(Y, x)`. -/
theorem integral_substT_selfDocSum (P : QED.WickModel.Params) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∫ zo in Ioi (0 : ℝ), substT (fun zo za => selfDocSum P Y zo za) (Y * (1 - Y)) zo x =
      selfGSum P.mγ P.Λ Y x := by
  have h := (hasIoiInt_selfAX_sub hY hx hmγ hmγ hΛ).sub (hasIoiInt_selfAX_sub hY hx hΛ hmγ hΛ)
  simp only [substT_selfDocSum]
  rw [h.2, selfGSum]
  ring

/-- For almost every `Y ∈ (0, 1)`, the slice of the integrand of eq. (5.1) is integrable on
`(0, ∞)²`. -/
theorem ae_integrable_selfDocSum_slice {P : QED.WickModel.Params} (hm : P.m = 1) (he : P.e = 1)
    (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) :
    ∀ᵐ Y ∂(volume.restrict (Ioo (0 : ℝ) 1)), Integrable (uncurry fun zo za => selfDocSum P Y zo za)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  obtain ⟨hI, -⟩ := sixteen_pi_pow_four_mul_openZero_Sp_eq_doc hm he hmγ hΛ
  have he' := QED.Integration.ChengWu.measurePreserving_splitOne.symm
  have hint := (he'.integrableOn_comp_preimage
    QED.Integration.ChengWu.splitOne.symm.measurableEmbedding).mpr hI
  rw [QED.Integration.ChengWu.preimage_splitOne_symm] at hint
  have hint' : Integrable (fun q : ℝ × (ℝ × ℝ) =>
      selfDocSum P (QED.Integration.ChengWu.splitOne.symm q 1)
        (QED.Integration.ChengWu.splitOne.symm q 0) (QED.Integration.ChengWu.splitOne.symm q 2))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]; exact hint
  filter_upwards [hint'.prod_right_ae] with Y hY
  refine hY.congr (ae_of_all _ fun p => ?_)
  simp [QED.Integration.ChengWu.splitOne_symm_apply, uncurry]

/-- **The self-energy graph half after the `a`-integration** (`m = e = 1`, `0 < m_γ < Λ`):
`∫₀¹ dY ∫₀^∞ dz_o ∫₀^∞ dz_a selfDocSum = ∫_{0<Y<1} ∫_{0<x<1} G_Σ(Y, x)`. -/
theorem integral_selfDocSum_eq_gsum {P : QED.WickModel.Params} (hm : P.m = 1) (he : P.e = 1)
    (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) :
    ∫ Y in Ioo (0 : ℝ) 1, ∫ zo in Ioi (0 : ℝ), ∫ za in Ioi (0 : ℝ), selfDocSum P Y zo za =
      ∫ Y in Ioo (0 : ℝ) 1, ∫ x in Ioo (0 : ℝ) 1, selfGSum P.mγ P.Λ Y x := by
  refine integral_congr_ae ?_
  filter_upwards [ae_integrable_selfDocSum_slice hm he hmγ hΛ,
    ae_restrict_mem measurableSet_Ioo] with Y hY hYm
  have hc : 0 < Y * (1 - Y) := mul_pos hYm.1 (by linarith [hYm.2])
  rw [(integral_subst_swap hc (measurable_selfDocSum P Y) hY).2]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  exact integral_substT_selfDocSum P hmγ (hmγ.trans hΛ) hYm hx

/-- **The unit `S` after the `a`-integration** (`m = 1`, `0 < m_γ < Λ`):
`16π⁴ unitF2 S P₁ = 2 ∫∫ G_Σ + 16π⁴ sCtHalf P₁`, `P₁ = atUnitCharge P d₁ d₂ d_m d₃`. -/
theorem sixteen_pi_pow_four_mul_unitF2_S_eq_gsum (P : QED.WickModel.Params) (hm : P.m = 1)
    (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) (d₁ d₂ dm d₃ : ℝ) :
    16 * (π : ℂ) ^ 4 * unitF2 .S (atUnitCharge P d₁ d₂ dm d₃) =
      ((2 * ∫ Y in Ioo (0 : ℝ) 1, ∫ x in Ioo (0 : ℝ) 1, selfGSum P.mγ P.Λ Y x : ℝ) : ℂ) +
        16 * (π : ℂ) ^ 4 * sCtHalf (atUnitCharge P d₁ d₂ dm d₃) := by
  rw [sixteen_pi_pow_four_mul_unitF2_S P hm hmγ hΛ d₁ d₂ dm d₃]
  congr 3
  exact integral_selfDocSum_eq_gsum (P := atUnitCharge P d₁ d₂ dm d₃) hm rfl hmγ hΛ

end QED.TwoLoop.UnitSCLimit

end
