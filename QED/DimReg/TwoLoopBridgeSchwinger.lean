/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.TwoLoopBridgeMoments
public import QED.DimReg.TwoLoopBridgeSchwingerProj
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Two-loop momentum integrals as `FeynmanFamily.integral`, in integer dimension

The dimensionally continued integral `QED.DimReg.FeynmanFamily.integral` is defined by its
Lee–Pomeransky formula; the link to loop momenta is, elsewhere in `QED/DimReg`, a documented
convention (Wick rotation, Schwinger parameters, Gaussian integration; see
`QED/DimReg/Symanzik.lean`). This file proves the Euclidean part of that convention at two
loops in every integer dimension `D ≥ 1`.

Two-loop Euclidean propagators are given by data `K : PropData D N`:
`Dₐ(ℓ) = pₐ |ℓ₁|² + 2 qₐ ℓ₁·ℓ₂ + rₐ |ℓ₂|² - 2 (β₁ₐ·ℓ₁ + β₂ₐ·ℓ₂) + cₐ` (`PropData.prop`).
With `A(x) = Σ xₐ [[pₐ, qₐ], [qₐ, rₐ]]`, `B(x) = Σ xₐ βₐ`, `C(x) = Σ xₐ cₐ`, the Symanzik
polynomials are `U = det A` and `F = U C - B·adj(A)B` (`PropData.symU`, `PropData.symF`).
If a family `P` has these Symanzik polynomials (`PropData.Represents`), then for positive real
labels `ν`
`∫ ∏ₐ Dₐ(ℓ)^(-νₐ) d^Dℓ₁ d^Dℓ₂ = π^D · P.integral ν D`
(`integral_prod_prop_rpow`), whenever the projective integral converges and the exponents
`a = |ν| - D`, `b = 3D/2 - |ν|` have positive real part. The proof: Schwinger parameters
`Dₐ^(-νₐ) = Γ(νₐ)⁻¹ ∫₀^∞ tₐ^(νₐ-1) e^(-tₐ Dₐ)`, Fubini (all integrands are positive), the
Gaussian integral `QED.DimReg.TwoLoopBridgeMoments.integral_affine_mul_affine_two`, the
Schwinger form in projective coordinates
`QED.DimReg.SchwingerProj.integral_schwIntegrand_eq_proj`, and
`QED.DimReg.LPChange.integral_eq_proj`.
-/

@[expose] public section

open MeasureTheory Set MvPolynomial
open scoped Real InnerProductSpace

namespace QED.DimReg.TwoLoopBridgeSchwinger

open QED.DimReg.TwoLoopBridgeGauss QED.DimReg.TwoLoopBridgeMoments
open QED.Integration.ChengWu (openSimplex)

variable {D N : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin D)

/-- Two-loop Euclidean propagator data:
`Dₐ(ℓ) = pₐ |ℓ₁|² + 2 qₐ ℓ₁·ℓ₂ + rₐ |ℓ₂|² - 2 (β₁ₐ·ℓ₁ + β₂ₐ·ℓ₂) + cₐ`. -/
structure PropData (D N : ℕ) where
  /-- The coefficient of `|ℓ₁|²`. -/
  p : Fin N → ℝ
  /-- Half the coefficient of `ℓ₁·ℓ₂`. -/
  q : Fin N → ℝ
  /-- The coefficient of `|ℓ₂|²`. -/
  r : Fin N → ℝ
  /-- Minus half the external vector coupled to `ℓ₁`. -/
  β₁ : Fin N → EuclideanSpace ℝ (Fin D)
  /-- Minus half the external vector coupled to `ℓ₂`. -/
  β₂ : Fin N → EuclideanSpace ℝ (Fin D)
  /-- The constant term. -/
  c : Fin N → ℝ

namespace PropData

variable (K : PropData D N)

/-- The propagator `Dₐ(ℓ)`. -/
noncomputable def prop (a : Fin N) (z : V × V) : ℝ :=
  quad (K.p a) (K.q a) (K.r a) z - 2 * lin (K.β₁ a) (K.β₂ a) z + K.c a

/-- `A₁₁(x) = Σ xₐ pₐ`. -/
noncomputable def sumP (x : Fin N → ℝ) : ℝ := ∑ a, x a * K.p a
/-- `A₁₂(x) = Σ xₐ qₐ`. -/
noncomputable def sumQ (x : Fin N → ℝ) : ℝ := ∑ a, x a * K.q a
/-- `A₂₂(x) = Σ xₐ rₐ`. -/
noncomputable def sumR (x : Fin N → ℝ) : ℝ := ∑ a, x a * K.r a
/-- `B₁(x) = Σ xₐ β₁ₐ`. -/
noncomputable def sumB₁ (x : Fin N → ℝ) : V := ∑ a, x a • K.β₁ a
/-- `B₂(x) = Σ xₐ β₂ₐ`. -/
noncomputable def sumB₂ (x : Fin N → ℝ) : V := ∑ a, x a • K.β₂ a
/-- `C(x) = Σ xₐ cₐ`. -/
noncomputable def sumC (x : Fin N → ℝ) : ℝ := ∑ a, x a * K.c a

/-- The first Symanzik polynomial `U = det A`. -/
noncomputable def symU (x : Fin N → ℝ) : ℝ := K.sumP x * K.sumR x - K.sumQ x ^ 2

/-- The second Symanzik polynomial `F = U C - B·adj(A)B`. -/
noncomputable def symF (x : Fin N → ℝ) : ℝ :=
  K.symU x * K.sumC x - (K.sumR x * ‖K.sumB₁ x‖ ^ 2 -
    2 * K.sumQ x * ⟪K.sumB₁ x, K.sumB₂ x⟫_ℝ + K.sumP x * ‖K.sumB₂ x‖ ^ 2)

/-- A two-loop family `P` has the Symanzik polynomials of the propagators `K`. -/
def Represents (P : FeynmanFamily N) : Prop :=
  P.loops = 2 ∧ (∀ x, eval x P.U = K.symU x) ∧ ∀ x, eval x P.F = K.symF x

theorem sum_mul_prop (x : Fin N → ℝ) (z : V × V) :
    ∑ a, x a * K.prop a z = quad (K.sumP x) (K.sumQ x) (K.sumR x) z -
      2 * lin (K.sumB₁ x) (K.sumB₂ x) z + K.sumC x := by
  simp only [prop, quad, lin, sumP, sumQ, sumR, sumB₁, sumB₂, sumC, sum_inner, inner_smul_left,
    RCLike.conj_to_real, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem continuous_prop (a : Fin N) : Continuous (K.prop a) := by
  unfold prop quad lin
  fun_prop

end PropData

open PropData

/-! ### Schwinger parameters -/

/-- `X^(-ν) = Γ(ν)⁻¹ ∫₀^∞ t^(ν-1) e^(-t X) dt` for `X > 0`, `ν > 0`. -/
theorem rpow_neg_eq_integral {X ν : ℝ} (hX : 0 < X) (hν : 0 < ν) :
    X ^ (-ν) = (Real.Gamma ν)⁻¹ * ∫ t in Ioi (0 : ℝ), t ^ (ν - 1) * Real.exp (-(t * X)) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hν hX
  simp_rw [mul_comm _ X]
  rw [h, one_div, Real.inv_rpow hX.le, ← Real.rpow_neg hX.le]
  field_simp [(Real.Gamma_pos_of_pos hν).ne']

/-- Products of Schwinger representations as one orthant integral. -/
theorem prod_rpow_neg_eq_integral {X ν : Fin N → ℝ} (hX : ∀ a, 0 < X a) (hν : ∀ a, 0 < ν a) :
    ∏ a, X a ^ (-ν a) = (∏ a, Real.Gamma (ν a))⁻¹ *
      ∫ t in posOrthant N, (∏ a, t a ^ (ν a - 1)) * Real.exp (-∑ a, t a * X a) := by
  have hpi : (volume : Measure (Fin N → ℝ)).restrict (posOrthant N) =
      Measure.pi fun _ => volume.restrict (Ioi 0) := by
    rw [posOrthant, volume_pi, Measure.restrict_pi_pi]
  have hint : ∫ t in posOrthant N, (∏ a, t a ^ (ν a - 1)) * Real.exp (-∑ a, t a * X a) =
      ∏ a, ∫ t in Ioi (0 : ℝ), t ^ (ν a - 1) * Real.exp (-(t * X a)) := by
    rw [hpi, ← integral_fintype_prod_eq_prod (fun a t => t ^ (ν a - 1) * Real.exp (-(t * X a)))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_neg_distrib]
  rw [hint, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun a _ => rpow_neg_eq_integral (hX a) (hν a)

/-! ### The Gaussian step -/

theorem integrable_gaussR {p q r : ℝ} (hp : 0 < p) (hdet : 0 < p * r - q ^ 2) (b₁ b₂ : V) :
    Integrable (gaussR p q r b₁ b₂) (volume.prod volume) := by
  have h := integrable_affine_mul_affine_gaussR hp hdet 0 0 1 0 0 0 0 b₁ b₂
  simpa [lin] using h

theorem integral_gaussR (hD : 0 < D) {p q r : ℝ} (hp : 0 < p) (hdet : 0 < p * r - q ^ 2)
    (b₁ b₂ : V) :
    ∫ z : V × V, gaussR p q r b₁ b₂ z ∂(volume.prod volume) =
      (π ^ 2 / (p * r - q ^ 2)) ^ ((D : ℝ) / 2) * Real.exp (invForm p q r b₁ b₂) := by
  have h := integral_affine_mul_affine_two hD hp hdet 0 0 1 0 0 0 0 b₁ b₂
  simpa [lin, bil] using h

/-- `(π² / U)^(D/2) = π^D U^(-D/2)`. -/
theorem pi_sq_div_rpow {u : ℝ} (hu : 0 < u) :
    (π ^ 2 / u) ^ ((D : ℝ) / 2) = π ^ D * u ^ (-((D : ℝ) / 2)) := by
  rw [Real.div_rpow (by positivity) hu.le, ← Real.rpow_natCast π 2, ← Real.rpow_mul
    Real.pi_pos.le, Real.rpow_neg hu.le, div_eq_mul_inv]
  congr 1
  rw [show ((2 : ℕ) : ℝ) * ((D : ℝ) / 2) = (D : ℕ) by push_cast; ring, Real.rpow_natCast]

/-- **The Gaussian step at a Schwinger point**: for `x` with `A₁₁(x) > 0`, `U(x) > 0`,
`∫ e^(-Σ xₐ Dₐ(ℓ)) d^Dℓ₁ d^Dℓ₂ = π^D U(x)^(-D/2) e^(-F(x)/U(x))`. -/
theorem integral_exp_neg_sum_mul_prop (hD : 0 < D) (K : PropData D N) {x : Fin N → ℝ}
    (hp : 0 < K.sumP x) (hU : 0 < K.symU x) :
    ∫ z : V × V, Real.exp (-∑ a, x a * K.prop a z) ∂(volume.prod volume) =
      π ^ D * K.symU x ^ (-((D : ℝ) / 2)) * Real.exp (-(K.symF x / K.symU x)) := by
  have hpt : ∀ z : V × V, Real.exp (-∑ a, x a * K.prop a z) =
      gaussR (K.sumP x) (K.sumQ x) (K.sumR x) (K.sumB₁ x) (K.sumB₂ x) z *
        Real.exp (-K.sumC x) := by
    intro z
    rw [sum_mul_prop, gaussR, ← Real.exp_add]
    congr 1
    ring
  simp_rw [hpt]
  have hU' : 0 < K.sumP x * K.sumR x - K.sumQ x ^ 2 := hU
  rw [integral_mul_const, integral_gaussR hD hp hU', pi_sq_div_rpow hU', mul_assoc,
    ← Real.exp_add]
  have key : invForm (K.sumP x) (K.sumQ x) (K.sumR x) (K.sumB₁ x) (K.sumB₂ x) + -K.sumC x =
      -(K.symF x / K.symU x) := by
    rw [invForm, symF, show K.sumP x * K.sumR x - K.sumQ x ^ 2 = K.symU x from rfl]
    have := hU.ne'
    field_simp
    ring
  rw [key]
  rfl

/-- The real Schwinger integrand `α^(ν-1) U^(-D/2) e^(-F/U)`. -/
noncomputable def schwR {m : ℕ} (P : FeynmanFamily (m + 1)) (ν : Fin (m + 1) → ℝ) (D : ℕ)
    (x : Fin (m + 1) → ℝ) : ℝ :=
  (∏ a, x a ^ (ν a - 1)) * eval x P.U ^ (-((D : ℝ) / 2)) *
    Real.exp (-(eval x P.F / eval x P.U))

theorem schwIntegrand_eq_schwR {m : ℕ} (P : FeynmanFamily (m + 1)) (ν : Fin (m + 1) → ℝ)
    {x : Fin (m + 1) → ℝ} (hx : ∀ i, 0 < x i) (hU : 0 < eval x P.U) :
    P.schwIntegrand (fun a => (ν a : ℂ)) D x = (schwR P ν D x : ℂ) := by
  simp only [FeynmanFamily.schwIntegrand, schwR, Complex.ofReal_mul, Complex.ofReal_prod,
    Complex.ofReal_cpow (hx _).le, Complex.ofReal_cpow hU.le, Complex.ofReal_exp,
    Complex.ofReal_neg]
  push_cast
  ring_nf

theorem schwR_nonneg {m : ℕ} (P : FeynmanFamily (m + 1)) (ν : Fin (m + 1) → ℝ)
    {x : Fin (m + 1) → ℝ} (hx : ∀ i, 0 < x i) (hU : 0 < eval x P.U) : 0 ≤ schwR P ν D x := by
  unfold schwR
  exact mul_nonneg (mul_nonneg (Finset.prod_nonneg fun a _ => Real.rpow_nonneg (hx a).le _)
    (Real.rpow_nonneg hU.le _)) (Real.exp_pos _).le

/-- **Two-loop momentum integrals in integer dimension.** Let the family `P` have the
Symanzik polynomials of the two-loop Euclidean propagators `K` (`PropData.Represents`), with
`U, F > 0` and `A₁₁ > 0` on the open orthant and positive propagators. For positive real labels
`ν` with `re a > 0`, `re b > 0` (`a = |ν| - D`, `b = 3D/2 - |ν|`) and a convergent projective
integral,
`∫ ∏ₐ Dₐ(ℓ)^(-νₐ) d^Dℓ₁ d^Dℓ₂ = π^D · P.integral ν D`. -/
theorem integral_prod_prop_rpow (hD : 0 < D) {m : ℕ} (K : PropData D (m + 1))
    (P : FeynmanFamily (m + 1)) (hK : K.Represents P) (hP : P.IsHomogeneous)
    (hprop : ∀ a z, 0 < K.prop a z) (hp : ∀ x : Fin (m + 1) → ℝ, (∀ i, 0 < x i) → 0 < K.sumP x)
    (hU : ∀ x : Fin (m + 1) → ℝ, (∀ i, 0 < x i) → 0 < eval x P.U)
    (hF : ∀ x : Fin (m + 1) → ℝ, (∀ i, 0 < x i) → 0 < eval x P.F)
    {ν : Fin (m + 1) → ℝ} (hν : ∀ a, 0 < ν a)
    (ha : 0 < (P.projA (fun a => (ν a : ℂ)) D).re) (hb : 0 < (P.projB (fun a => (ν a : ℂ)) D).re)
    (hint : IntegrableOn (P.projIntegrand (fun a => (ν a : ℂ)) D) (openSimplex m)) :
    ((∫ z : V × V, ∏ a, K.prop a z ^ (-ν a) ∂(volume.prod volume) : ℝ) : ℂ) =
      (π : ℂ) ^ D * P.integral (fun a => (ν a : ℂ)) D := by
  obtain ⟨-, hUe, hFe⟩ := hK
  set νc : Fin (m + 1) → ℂ := fun a => (ν a : ℂ)
  have hS : IntegrableOn (P.schwIntegrand νc D) (posOrthant (m + 1)) :=
    (SchwingerProj.integrableOn_schwIntegrand_iff P νc D hP hU hF ha).mpr hint
  have hRint : IntegrableOn (schwR P ν D) (posOrthant (m + 1)) := by
    refine (show IntegrableOn (fun x => ‖P.schwIntegrand νc D x‖) (posOrthant (m + 1)) volume
      from hS.norm).congr_fun (fun x hx => ?_) (measurableSet_posOrthant _)
    rw [mem_posOrthant] at hx
    show ‖P.schwIntegrand νc D x‖ = schwR P ν D x
    rw [show P.schwIntegrand νc D x = _ from schwIntegrand_eq_schwR P ν hx (hU x hx),
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (schwR_nonneg P ν hx (hU x hx))]
  set f : (Fin (m + 1) → ℝ) × (V × V) → ℝ := fun w =>
    (∏ a, w.1 a ^ (ν a - 1)) * Real.exp (-∑ a, w.1 a * K.prop a w.2)
  have hgx : ∀ x : Fin (m + 1) → ℝ, (∀ i, 0 < x i) →
      ∫ z : V × V, f (x, z) ∂(volume.prod volume) = π ^ D * schwR P ν D x := by
    intro x hx
    simp only [f]
    rw [integral_const_mul, integral_exp_neg_sum_mul_prop hD K (hp x hx)
      (by rw [← hUe]; exact hU x hx), schwR, ← hUe, ← hFe]
    ring
  have hfm : AEStronglyMeasurable f ((volume.restrict (posOrthant (m + 1))).prod
      (volume.prod volume)) := by
    refine Measurable.aestronglyMeasurable ?_
    refine (Finset.measurable_prod _ fun a _ => ((measurable_pi_apply a).comp
      measurable_fst).pow_const _).mul ?_
    refine Measurable.exp (Measurable.neg ?_)
    refine Finset.measurable_sum _ fun a _ => ?_
    exact ((measurable_pi_apply a).comp measurable_fst).mul
      ((K.continuous_prop a).measurable.comp measurable_snd)
  have hfint : Integrable f ((volume.restrict (posOrthant (m + 1))).prod (volume.prod volume)) := by
    rw [integrable_prod_iff hfm]
    constructor
    · refine ae_restrict_of_forall_mem (measurableSet_posOrthant _) fun x hx => ?_
      rw [mem_posOrthant] at hx
      have hUx : 0 < K.symU x := by rw [← hUe]; exact hU x hx
      have hG := (integrable_gaussR (hp x hx) hUx (K.sumB₁ x) (K.sumB₂ x)).mul_const
        (Real.exp (-K.sumC x))
      refine (hG.const_mul (∏ a, x a ^ (ν a - 1))).congr
        (Filter.Eventually.of_forall fun z => ?_)
      simp only [f]
      rw [sum_mul_prop, gaussR, ← Real.exp_add]
      congr 2
      ring
    · refine (hRint.const_mul (π ^ D)).congr ?_
      refine ae_restrict_of_forall_mem (measurableSet_posOrthant _) fun x hx => ?_
      rw [mem_posOrthant] at hx
      show π ^ D * schwR P ν D x = ∫ y, ‖f (x, y)‖ ∂(volume.prod volume)
      rw [← hgx x hx]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [f, Real.norm_eq_abs]
      exact (abs_of_nonneg (mul_nonneg (Finset.prod_nonneg fun a _ =>
        Real.rpow_nonneg (hx a).le _) (Real.exp_pos _).le)).symm
  have hswap := integral_integral_swap (f := fun x z => f (x, z)) hfint
  have hpt : ∀ z : V × V, ∏ a, K.prop a z ^ (-ν a) = (∏ a, Real.Gamma (ν a))⁻¹ *
      ∫ x in posOrthant (m + 1), f (x, z) := fun z =>
    prod_rpow_neg_eq_integral (fun a => hprop a z) hν
  simp_rw [hpt]
  rw [integral_const_mul, ← hswap,
    setIntegral_congr_fun (measurableSet_posOrthant _) fun x hx =>
      hgx x (mem_posOrthant.mp hx), integral_const_mul]
  have hval : ((∫ x in posOrthant (m + 1), schwR P ν D x : ℝ) : ℂ) =
      Complex.Gamma (P.projA νc D) * ∫ x in openSimplex m, P.projIntegrand νc D x := by
    rw [← integral_complex_ofReal, ← SchwingerProj.integral_schwIntegrand_eq_proj P νc D hP hU
      hF ha hS]
    refine setIntegral_congr_fun (measurableSet_posOrthant _) fun x hx => ?_
    rw [mem_posOrthant] at hx
    exact (show P.schwIntegrand νc D x = _ from schwIntegrand_eq_schwR P ν hx (hU x hx)).symm
  have hconv : LPConvergent P.lpPoly νc D :=
    (LPChange.lpConvergent_iff_proj P νc D hP hU hF ha hb).mpr hint
  rw [LPChange.integral_eq_proj P νc D hP hU hF ha hb hconv]
  push_cast
  rw [hval]
  simp only [νc, Complex.Gamma_ofReal]
  ring

end QED.DimReg.TwoLoopBridgeSchwinger
