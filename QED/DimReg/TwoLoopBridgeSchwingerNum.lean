/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.TwoLoopBridgeSchwinger
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Two-loop momentum integrals with a numerator, in projective form

`QED.DimReg.FeynmanFamily.integral` vanishes at labels with a non-positive index, because its
prefactor contains `Γ(νⱼ)⁻¹` and Lean's `Γ(0)⁻¹ = 0`. A numerator label therefore cannot be
read off from `FeynmanFamily.integral`; what replaces it is a **parametric formula**: a
combination of projective integrals with the factors `Γ(a)` and `Γ(a - 1)`. This file proves
that formula at two loops, in every integer dimension `D ≥ 1`, for a numerator that is one
quadratic propagator.

## The ray lemma with an insertion

If `h` is homogeneous of degree `-k` on the open orthant (`IsHomogNeg h k`), the cone
decomposition `α = s · y` of the Schwinger integrand times `h` gives the ray integral
`∫₀^∞ s^(a-k-1) e^(-s F/U) ds = Γ(a - k) (F/U)^(k-a)`, so
`∫_{(0,∞)^N} α^(ν-1) U^(-d/2) e^(-F/U) h(α) = Γ(a - k) ∫_Δ y^(ν-1) U^(-b) F^(-a) (F/U)^k h(y)`
(`integral_schwIntegrand_mul_eq`; the integrand on the right is
`QED.DimReg.FeynmanFamily.projInsert`), and the two sides converge together
(`integrableOn_schwIntegrand_mul_iff`). For `h = 1`, `k = 0` this is
`QED.DimReg.SchwingerProj.integral_schwIntegrand_eq_proj`.

## One propagator as numerator

For a numerator `Ñ(ℓ)` of the propagator shape of
`QED.DimReg.TwoLoopBridgeSchwinger.PropData.prop` (quadratic part `A' = [[p', q'], [q', r']]`),
the Gaussian moment of `QED.DimReg.TwoLoopBridgeMoments.integral_quad_mul_gaussR` gives, at a
Schwinger point `x`,
`∫ Ñ(ℓ) e^(-Σ xₐ Dₐ(ℓ)) = π^D U^(-D/2) e^(-F/U) (Ñ(s(x)) + D/2 · tr(A' adj A(x)) / U(x))`
with the shift `s = A⁻¹B` (`integral_prop_mul_exp_neg_sum_mul_prop`). The first insertion
(`numShift`) is homogeneous of degree `0`, the second (`numTrace`) of degree `-1`, and the ray
lemma turns the momentum integral into
`∫ Ñ ∏ₐ Dₐ^(-νₐ) = π^D / ∏ₐ Γ(νₐ) · (Γ(a) ∫_Δ y^(ν-1) U^(-b) F^(-a) Ñ(s(y))
  + D/2 · Γ(a - 1) ∫_Δ y^(ν-1) U^(-b) F^(-a) (F/U) tr(A' adj A)/U)`
(`integral_prop_mul_prod_prop_rpow`). The dimension enters polynomially, through `D/2`, and
through `a = |ν| - D`, `b = 3D/2 - |ν|`: the right side is the formula that defines the
numerator label in any complex dimension.
-/

@[expose] public section

open MeasureTheory Set Complex MvPolynomial

namespace QED.DimReg.FeynmanFamily

open QED.Integration.Feynman (simplexPoint)

/-- The projective integrand with an insertion `h` of degree `-k`:
`y^(ν-1) U(y)^(-b) F(y)^(-a) (F(y)/U(y))^k h(y)` at `y = simplexPoint x`. -/
noncomputable def projInsert {m : ℕ} (P : FeynmanFamily (m + 1)) (ν : Fin (m + 1) → ℂ) (d : ℂ)
    (k : ℕ) (h : (Fin (m + 1) → ℝ) → ℂ) (x : Fin m → ℝ) : ℂ :=
  P.projIntegrand ν d x *
    ((eval (simplexPoint x) P.F / eval (simplexPoint x) P.U : ℝ) : ℂ) ^ k * h (simplexPoint x)

end QED.DimReg.FeynmanFamily

namespace QED.DimReg.SchwingerNum

open QED.Integration.Feynman (simplexPoint)
open QED.Integration.ChengWu (openSimplex mem_openSimplex)
open QED.DimReg.LPChange QED.DimReg.SchwingerProj
open FeynmanFamily

variable {m : ℕ}

/-- `h` is homogeneous of degree `-k` on the open orthant. -/
def IsHomogNeg (h : (Fin (m + 1) → ℝ) → ℂ) (k : ℕ) : Prop :=
  ∀ y : Fin (m + 1) → ℝ, (∀ i, 0 < y i) → ∀ s : ℝ, 0 < s → h (s • y) = ((s : ℂ) ^ k)⁻¹ * h y

theorem cpow_sub_one_mul_inv_pow {s : ℝ} (hs : 0 < s) (a : ℂ) (k : ℕ) :
    (s : ℂ) ^ (a - 1) * ((s : ℂ) ^ k)⁻¹ = (s : ℂ) ^ (a - k - 1) := by
  have hs' : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  rw [show a - k - 1 = (a - 1) - k by ring, cpow_sub (a - 1) _ hs', cpow_natCast, div_eq_mul_inv]

variable (P : FeynmanFamily (m + 1)) (ν : Fin (m + 1) → ℂ) (d : ℂ)

/-- On the ray through a positive point `y`, the cone integrand of the Schwinger integrand
times an insertion of degree `-k` is the Γ integrand `s^(a-k-1) e^(-c s)`, `c = F(y)/U(y)`. -/
theorem cone_schwIntegrand_mul_eq (hP : P.IsHomogeneous) {h : (Fin (m + 1) → ℝ) → ℂ} {k : ℕ}
    (hh : IsHomogNeg h k) {y : Fin (m + 1) → ℝ} (hy : ∀ i, 0 < y i) (hU : 0 < eval y P.U)
    (hF : 0 < eval y P.F) {s : ℝ} (hs : 0 < s) :
    s ^ m • (P.schwIntegrand ν d (s • y) * h (s • y)) =
      ((∏ i, (y i : ℂ) ^ (ν i - 1)) * (eval y P.U : ℂ) ^ (-(d / 2)) * h y) *
        ((s : ℂ) ^ (P.projA ν d - k - 1) *
          exp (-((eval y P.F / eval y P.U * s : ℝ) : ℂ))) := by
  rw [hh y hy s hs, ← smul_mul_assoc, cone_schwIntegrand_eq P ν d hP hy hU hF hs,
    ← cpow_sub_one_mul_inv_pow hs]
  ring

/-- The projective integrand with an insertion as the ray prefactor times `c^(-(a-k))`. -/
theorem projInsert_eq {k : ℕ} (h : (Fin (m + 1) → ℝ) → ℂ) {x : Fin m → ℝ}
    (hU : 0 < eval (simplexPoint x) P.U) (hF : 0 < eval (simplexPoint x) P.F) :
    P.projInsert ν d k h x =
      ((∏ i, (simplexPoint x i : ℂ) ^ (ν i - 1)) *
          (eval (simplexPoint x) P.U : ℂ) ^ (-(d / 2)) * h (simplexPoint x)) *
        (((eval (simplexPoint x) P.F / eval (simplexPoint x) P.U : ℝ) : ℂ) ^
          (-(P.projA ν d - k))) := by
  have hc : ((eval (simplexPoint x) P.F / eval (simplexPoint x) P.U : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (div_pos hF hU).ne'
  rw [projInsert, projIntegrand_eq P ν d hU hF, show -(P.projA ν d - k) = -P.projA ν d + k by
    ring, cpow_add _ _ hc, cpow_natCast]
  ring

theorem measurable_coneIntegrand_schwIntegrand_mul {h : (Fin (m + 1) → ℝ) → ℂ}
    (hm : Measurable h) :
    Measurable (coneIntegrand fun x => P.schwIntegrand ν d x * h x) := by
  unfold coneIntegrand
  refine (measurable_fst.pow_const _).smul
    (((measurable_schwIntegrand P ν d).mul hm).comp ?_)
  exact (continuous_fst.smul (continuous_simplexPoint.comp continuous_snd)).measurable

/-- **The ray lemma with an insertion.** For a homogeneous family with `U, F > 0` on the open
orthant, an insertion `h` homogeneous of degree `-k`, `re (a - k) > 0` and absolute
convergence,
`∫_{(0,∞)^N} α^(ν-1) U^(-d/2) e^(-F/U) h(α) = Γ(a - k) ∫_Δ y^(ν-1) U^(-b) F^(-a) (F/U)^k h(y)`.
-/
theorem integral_schwIntegrand_mul_eq (hP : P.IsHomogeneous)
    (hU : ∀ y : Fin (m + 1) → ℝ, (∀ i, 0 < y i) → 0 < eval y P.U)
    (hF : ∀ y : Fin (m + 1) → ℝ, (∀ i, 0 < y i) → 0 < eval y P.F)
    {h : (Fin (m + 1) → ℝ) → ℂ} {k : ℕ} (hh : IsHomogNeg h k)
    (ha : 0 < (P.projA ν d - k).re)
    (hint : IntegrableOn (fun x => P.schwIntegrand ν d x * h x) (posOrthant (m + 1))) :
    ∫ x in posOrthant (m + 1), P.schwIntegrand ν d x * h x =
      Gamma (P.projA ν d - k) * ∫ x in openSimplex m, P.projInsert ν d k h x := by
  rw [integral_posOrthant_eq_cone _ hint, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_openSimplex fun x hx => ?_
  have hy := simplexPoint_pos hx
  have hUx := hU _ hy
  have hFx := hF _ hy
  have hray : ∀ s ∈ Ioi (0 : ℝ),
      s ^ m • (P.schwIntegrand ν d (s • simplexPoint x) * h (s • simplexPoint x)) =
        ((∏ i, (simplexPoint x i : ℂ) ^ (ν i - 1)) *
          (eval (simplexPoint x) P.U : ℂ) ^ (-(d / 2)) * h (simplexPoint x)) *
          ((s : ℂ) ^ (P.projA ν d - k - 1) * exp (-((eval (simplexPoint x) P.F /
            eval (simplexPoint x) P.U * s : ℝ) : ℂ))) := fun s hs =>
    cone_schwIntegrand_mul_eq P ν d hP hh hy hUx hFx hs
  rw [setIntegral_congr_fun measurableSet_Ioi hray, integral_const_mul,
    integral_ray ha (div_pos hFx hUx), projInsert_eq P ν d h hUx hFx]
  ring

/-- **Convergence with an insertion.** Under the hypotheses of `integral_schwIntegrand_mul_eq`
(and `h` measurable), the Schwinger integral with the insertion converges absolutely exactly
when the projective integral of `projInsert` does. -/
theorem integrableOn_schwIntegrand_mul_iff (hP : P.IsHomogeneous)
    (hU : ∀ y : Fin (m + 1) → ℝ, (∀ i, 0 < y i) → 0 < eval y P.U)
    (hF : ∀ y : Fin (m + 1) → ℝ, (∀ i, 0 < y i) → 0 < eval y P.F)
    {h : (Fin (m + 1) → ℝ) → ℂ} {k : ℕ} (hh : IsHomogNeg h k) (hm : Measurable h)
    (ha : 0 < (P.projA ν d - k).re) :
    IntegrableOn (fun x => P.schwIntegrand ν d x * h x) (posOrthant (m + 1)) ↔
      IntegrableOn (P.projInsert ν d k h) (openSimplex m) := by
  rw [integrableOn_posOrthant_iff, IntegrableOn, ← Measure.prod_restrict,
    integrable_prod_iff'
      (measurable_coneIntegrand_schwIntegrand_mul P ν d hm).aestronglyMeasurable]
  have hray : ∀ x ∈ openSimplex m, ∀ s ∈ Ioi (0 : ℝ),
      coneIntegrand (fun x => P.schwIntegrand ν d x * h x) (s, x) =
        ((∏ i, (simplexPoint x i : ℂ) ^ (ν i - 1)) *
          (eval (simplexPoint x) P.U : ℂ) ^ (-(d / 2)) * h (simplexPoint x)) *
          ((s : ℂ) ^ (P.projA ν d - k - 1) * exp (-((eval (simplexPoint x) P.F /
            eval (simplexPoint x) P.U * s : ℝ) : ℂ))) := fun x hx s hs =>
    cone_schwIntegrand_mul_eq P ν d hP hh (simplexPoint_pos hx) (hU _ (simplexPoint_pos hx))
      (hF _ (simplexPoint_pos hx)) hs
  have hray' : ∀ x ∈ openSimplex m, ∀ s ∈ Ioi (0 : ℝ),
      coneIntegrand (fun x => P.schwIntegrand ν d x * h x) (s, x) =
        ((∏ i, (simplexPoint x i : ℂ) ^ (ν i - 1)) *
          (eval (simplexPoint x) P.U : ℂ) ^ (-(d / 2)) * h (simplexPoint x)) *
          ((s : ℂ) ^ ((P.projA ν d - k) - 1) * exp (-((eval (simplexPoint x) P.F /
            eval (simplexPoint x) P.U * s : ℝ) : ℂ))) := hray
  have h1 : ∀ᵐ x ∂(volume.restrict (openSimplex m)),
      Integrable (fun s => coneIntegrand (fun x => P.schwIntegrand ν d x * h x) (s, x))
        (volume.restrict (Ioi 0)) := by
    refine ae_restrict_of_forall_mem measurableSet_openSimplex fun x hx => ?_
    have hc := div_pos (hF _ (simplexPoint_pos hx)) (hU _ (simplexPoint_pos hx))
    exact IntegrableOn.congr_fun ((integrableOn_ray ha hc).const_mul _)
      (fun s hs => (hray' x hx s hs).symm) measurableSet_Ioi
  rw [and_iff_right h1]
  have h2 : ∀ x ∈ openSimplex m,
      ∫ s in Ioi 0, ‖coneIntegrand (fun x => P.schwIntegrand ν d x * h x) (s, x)‖ =
        Real.Gamma (P.projA ν d - k).re * ‖P.projInsert ν d k h x‖ := by
    intro x hx
    have hUx := hU _ (simplexPoint_pos hx)
    have hFx := hF _ (simplexPoint_pos hx)
    rw [setIntegral_congr_fun measurableSet_Ioi fun s hs => by rw [hray' x hx s hs, norm_mul],
      integral_const_mul, integral_norm_ray ha (div_pos hFx hUx),
      projInsert_eq P ν d h hUx hFx, norm_mul (_ * _ * h (simplexPoint x)),
      norm_mul (_ * _) (h (simplexPoint x)),
      norm_cpow_eq_rpow_re_of_pos (div_pos hFx hUx), neg_re, one_div,
      Real.inv_rpow (div_pos hFx hUx).le, Real.rpow_neg (div_pos hFx hUx).le]
    ring
  have hmeas : Measurable (P.projInsert ν d k h) := by
    unfold projInsert
    have hU' : Measurable fun x : Fin m → ℝ => eval (simplexPoint x) P.U :=
      ((MvPolynomial.continuous_eval P.U).comp continuous_simplexPoint).measurable
    have hF' : Measurable fun x : Fin m → ℝ => eval (simplexPoint x) P.F :=
      ((MvPolynomial.continuous_eval P.F).comp continuous_simplexPoint).measurable
    exact ((measurable_projIntegrand P ν d).mul
      ((measurable_ofReal.comp (hF'.div hU')).pow_const _)).mul
      (hm.comp continuous_simplexPoint.measurable)
  rw [integrable_congr (ae_restrict_of_forall_mem measurableSet_openSimplex h2),
    integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (Real.Gamma_pos_of_pos ha).ne'),
    integrable_norm_iff hmeas.aestronglyMeasurable, IntegrableOn]

end QED.DimReg.SchwingerNum

namespace QED.DimReg.TwoLoopBridgeSchwingerNum

open scoped Real InnerProductSpace
open QED.Integration.ChengWu (openSimplex)
open QED.DimReg.TwoLoopBridgeGauss QED.DimReg.TwoLoopBridgeMoments
open QED.DimReg.TwoLoopBridgeSchwinger QED.DimReg.SchwingerNum
open PropData

variable {D N M m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin D)

/-! ### The Gaussian moment of a propagator numerator -/

/-- `c·A⁻¹b` is the linear form `c·s` evaluated at the shift `s = A⁻¹b`. -/
theorem bil_eq_lin_shift (p q r : ℝ) (c₁ c₂ b₁ b₂ : V) :
    bil p q r c₁ c₂ b₁ b₂ = lin c₁ c₂ (shift₁ p q r b₁ b₂, shift₂ p q r b₁ b₂) := by
  simp only [bil, lin, shift₁, shift₂, inner_smul_right, inner_sub_right]
  ring

theorem integrable_quad_mul_gaussR {p q r : ℝ} (hp : 0 < p) (hdet : 0 < p * r - q ^ 2)
    (p' q' r' : ℝ) (b₁ b₂ : V) :
    Integrable (fun z : V × V => quad p' q' r' z * gaussR p q r b₁ b₂ z)
      (volume.prod volume) := by
  set e : Fin D → V := fun k => EuclideanSpace.single k 1
  have hG := fun c₁ c₂ c₁' c₂' : V =>
    integrable_affine_mul_affine_gaussR hp hdet 0 0 0 c₁ c₂ c₁' c₂' b₁ b₂
  refine (integrable_finsetSum Finset.univ fun k _ =>
    (((hG (e k) 0 (e k) 0).const_mul p').add ((hG (e k) 0 0 (e k)).const_mul (2 * q'))).add
      ((hG 0 (e k) 0 (e k)).const_mul r')).congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply]
  rw [quad_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [e, zero_add, add_zero]
  ring

theorem integrable_prop_mul_gaussR {p q r : ℝ} (hp : 0 < p) (hdet : 0 < p * r - q ^ 2)
    (Kn : PropData D M) (j : Fin M) (b₁ b₂ : V) :
    Integrable (fun z : V × V => Kn.prop j z * gaussR p q r b₁ b₂ z) (volume.prod volume) := by
  refine ((integrable_quad_mul_gaussR hp hdet (Kn.p j) (Kn.q j) (Kn.r j) b₁ b₂).add
    (integrable_affine_mul_affine_gaussR hp hdet 0 1 (Kn.c j) ((-2 : ℝ) • Kn.β₁ j)
      ((-2 : ℝ) • Kn.β₂ j) 0 0 b₁ b₂)).congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply, prop, lin, inner_smul_left, inner_zero_left, RCLike.conj_to_real]
  ring

/-- **The Gaussian moment of a propagator numerator**: with the shift `s = A⁻¹b`,
`∫ Ñ(ℓ) e^(-(ℓ·Aℓ) + 2 b·ℓ) = (π² / det A)^(D/2) e^(b·A⁻¹b)
  (Ñ(s) + D (p' r - 2 q' q + r' p) / (2 det A))`. -/
theorem integral_prop_mul_gaussR (hD : 0 < D) {p q r : ℝ} (hp : 0 < p)
    (hdet : 0 < p * r - q ^ 2) (Kn : PropData D M) (j : Fin M) (b₁ b₂ : V) :
    ∫ z : V × V, Kn.prop j z * gaussR p q r b₁ b₂ z ∂(volume.prod volume) =
      (π ^ 2 / (p * r - q ^ 2)) ^ ((D : ℝ) / 2) * Real.exp (invForm p q r b₁ b₂) *
        (Kn.prop j (shift₁ p q r b₁ b₂, shift₂ p q r b₁ b₂) +
          D * (Kn.p j * r - 2 * Kn.q j * q + Kn.r j * p) / (2 * (p * r - q ^ 2))) := by
  have hpt : ∀ z : V × V, Kn.prop j z * gaussR p q r b₁ b₂ z =
      quad (Kn.p j) (Kn.q j) (Kn.r j) z * gaussR p q r b₁ b₂ z +
        ((0 + lin ((-2 : ℝ) • Kn.β₁ j) ((-2 : ℝ) • Kn.β₂ j) z) * (1 + lin 0 0 z) + Kn.c j) *
          gaussR p q r b₁ b₂ z := by
    intro z
    simp only [prop, lin, inner_smul_left, inner_zero_left, RCLike.conj_to_real]
    ring
  simp_rw [hpt]
  rw [integral_add (integrable_quad_mul_gaussR hp hdet _ _ _ b₁ b₂)
      (integrable_affine_mul_affine_gaussR hp hdet 0 1 (Kn.c j) _ _ 0 0 b₁ b₂),
    integral_quad_mul_gaussR hD hp hdet, integral_affine_mul_affine_two hD hp hdet,
    show bil p q r ((-2 : ℝ) • Kn.β₁ j) ((-2 : ℝ) • Kn.β₂ j) 0 0 = 0 by simp [bil],
    bil_eq_lin_shift, bil_eq_lin_shift]
  simp only [prop, lin, inner_smul_left, inner_zero_left, RCLike.conj_to_real]
  ring

/-! ### The insertions -/

/-- The shift `s(x) = A(x)⁻¹ B(x)` of the Gaussian at the Schwinger point `x`. -/
noncomputable def shiftAt (K : PropData D N) (x : Fin N → ℝ) : V × V :=
  (shift₁ (K.sumP x) (K.sumQ x) (K.sumR x) (K.sumB₁ x) (K.sumB₂ x),
    shift₂ (K.sumP x) (K.sumQ x) (K.sumR x) (K.sumB₁ x) (K.sumB₂ x))

/-- The degree-`0` insertion: the numerator `Ñ` at the shift, `Ñ(A(x)⁻¹ B(x))`. -/
noncomputable def numShift (K : PropData D N) (Kn : PropData D M) (j : Fin M)
    (x : Fin N → ℝ) : ℝ :=
  Kn.prop j (shiftAt K x)

/-- The degree-`-1` insertion: `tr(A' adj A(x)) / U(x)`, `A'` the quadratic part of `Ñ`. -/
noncomputable def numTrace (K : PropData D N) (Kn : PropData D M) (j : Fin M)
    (x : Fin N → ℝ) : ℝ :=
  (Kn.p j * K.sumR x - 2 * Kn.q j * K.sumQ x + Kn.r j * K.sumP x) / K.symU x

theorem sumP_smul (K : PropData D N) (s : ℝ) (x : Fin N → ℝ) :
    K.sumP (s • x) = s * K.sumP x := by
  simp only [sumP, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem sumQ_smul (K : PropData D N) (s : ℝ) (x : Fin N → ℝ) :
    K.sumQ (s • x) = s * K.sumQ x := by
  simp only [sumQ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem sumR_smul (K : PropData D N) (s : ℝ) (x : Fin N → ℝ) :
    K.sumR (s • x) = s * K.sumR x := by
  simp only [sumR, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem sumB₁_smul (K : PropData D N) (s : ℝ) (x : Fin N → ℝ) :
    K.sumB₁ (s • x) = s • K.sumB₁ x := by
  simp only [sumB₁, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]

theorem sumB₂_smul (K : PropData D N) (s : ℝ) (x : Fin N → ℝ) :
    K.sumB₂ (s • x) = s • K.sumB₂ x := by
  simp only [sumB₂, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]

theorem symU_smul (K : PropData D N) (s : ℝ) (x : Fin N → ℝ) :
    K.symU (s • x) = s ^ 2 * K.symU x := by
  simp only [symU, sumP_smul, sumQ_smul, sumR_smul]
  ring

theorem inv_mul_sq_mul {s : ℝ} (hs : s ≠ 0) (t : ℝ) : (s ^ 2 * t)⁻¹ * s ^ 2 = t⁻¹ := by
  rw [mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hs), one_mul]

theorem shift₁_smul {s : ℝ} (hs : s ≠ 0) (p q r : ℝ) (b₁ b₂ : V) :
    shift₁ (s * p) (s * q) (s * r) (s • b₁) (s • b₂) = shift₁ p q r b₁ b₂ := by
  unfold shift₁
  rw [show s * p * (s * r) - (s * q) ^ 2 = s ^ 2 * (p * r - q ^ 2) by ring,
    show (s * r) • (s • b₁) - (s * q) • (s • b₂) = s ^ 2 • (r • b₁ - q • b₂) by module,
    smul_smul, inv_mul_sq_mul hs]

theorem shift₂_smul {s : ℝ} (hs : s ≠ 0) (p q r : ℝ) (b₁ b₂ : V) :
    shift₂ (s * p) (s * q) (s * r) (s • b₁) (s • b₂) = shift₂ p q r b₁ b₂ := by
  unfold shift₂
  rw [show s * p * (s * r) - (s * q) ^ 2 = s ^ 2 * (p * r - q ^ 2) by ring,
    show (s * p) • (s • b₂) - (s * q) • (s • b₁) = s ^ 2 • (p • b₂ - q • b₁) by module,
    smul_smul, inv_mul_sq_mul hs]

theorem shiftAt_smul (K : PropData D N) {s : ℝ} (hs : s ≠ 0) (x : Fin N → ℝ) :
    shiftAt K (s • x) = shiftAt K x := by
  simp only [shiftAt, sumP_smul, sumQ_smul, sumR_smul, sumB₁_smul, sumB₂_smul, shift₁_smul hs,
    shift₂_smul hs]

theorem numTrace_smul (K : PropData D N) (Kn : PropData D M) (j : Fin M) {s : ℝ} (hs : s ≠ 0)
    (x : Fin N → ℝ) : numTrace K Kn j (s • x) = s⁻¹ * numTrace K Kn j x := by
  simp only [numTrace, sumP_smul, sumQ_smul, sumR_smul, symU_smul]
  by_cases hU : K.symU x = 0
  · simp [hU]
  · field_simp

theorem isHomogNeg_numShift (K : PropData D (m + 1)) (Kn : PropData D M) (j : Fin M) :
    IsHomogNeg (fun x => (numShift K Kn j x : ℂ)) 0 := by
  intro y _ s hs
  simp only [numShift, shiftAt_smul K hs.ne', pow_zero, inv_one, one_mul]

theorem isHomogNeg_numTrace (K : PropData D (m + 1)) (Kn : PropData D M) (j : Fin M) :
    IsHomogNeg (fun x => (numTrace K Kn j x : ℂ)) 1 := by
  intro y _ s hs
  simp only [numTrace_smul K Kn j hs.ne', pow_one]
  push_cast
  rfl

theorem measurable_shiftAt (K : PropData D N) : Measurable (shiftAt K) := by
  have hP : Measurable K.sumP := by unfold sumP; fun_prop
  have hQ : Measurable K.sumQ := by unfold sumQ; fun_prop
  have hR : Measurable K.sumR := by unfold sumR; fun_prop
  have hB₁ : Measurable K.sumB₁ := by unfold sumB₁; fun_prop
  have hB₂ : Measurable K.sumB₂ := by unfold sumB₂; fun_prop
  have hdet : Measurable fun x => (K.sumP x * K.sumR x - K.sumQ x ^ 2)⁻¹ :=
    ((hP.mul hR).sub (hQ.pow_const 2)).inv
  unfold shiftAt shift₁ shift₂
  exact (hdet.smul (((hR.smul hB₁).sub (hQ.smul hB₂)))).prodMk
    (hdet.smul ((hP.smul hB₂).sub (hQ.smul hB₁)))

theorem measurable_numShift (K : PropData D N) (Kn : PropData D M) (j : Fin M) :
    Measurable (numShift K Kn j) :=
  (Kn.continuous_prop j).measurable.comp (measurable_shiftAt K)

theorem measurable_numTrace (K : PropData D N) (Kn : PropData D M) (j : Fin M) :
    Measurable (numTrace K Kn j) := by
  have hP : Measurable K.sumP := by unfold sumP; fun_prop
  have hQ : Measurable K.sumQ := by unfold sumQ; fun_prop
  have hR : Measurable K.sumR := by unfold sumR; fun_prop
  unfold numTrace symU
  exact ((((hR.const_mul _).sub (hQ.const_mul _)).add (hP.const_mul _))).div
    ((hP.mul hR).sub (hQ.pow_const 2))

/-- **The Gaussian step with a numerator**: at a Schwinger point `x` with `A₁₁(x) > 0`,
`U(x) > 0`,
`∫ Ñ(ℓ) e^(-Σ xₐ Dₐ(ℓ)) = π^D U^(-D/2) e^(-F/U) (Ñ(s(x)) + D/2 · tr(A' adj A(x)) / U(x))`. -/
theorem integral_prop_mul_exp_neg_sum_mul_prop (hD : 0 < D) (K : PropData D N)
    (Kn : PropData D M) (j : Fin M) {x : Fin N → ℝ} (hp : 0 < K.sumP x) (hU : 0 < K.symU x) :
    ∫ z : V × V, Kn.prop j z * Real.exp (-∑ a, x a * K.prop a z) ∂(volume.prod volume) =
      π ^ D * K.symU x ^ (-((D : ℝ) / 2)) * Real.exp (-(K.symF x / K.symU x)) *
        (numShift K Kn j x + D / 2 * numTrace K Kn j x) := by
  have hpt : ∀ z : V × V, Kn.prop j z * Real.exp (-∑ a, x a * K.prop a z) =
      Kn.prop j z * gaussR (K.sumP x) (K.sumQ x) (K.sumR x) (K.sumB₁ x) (K.sumB₂ x) z *
        Real.exp (-K.sumC x) := by
    intro z
    rw [sum_mul_prop, gaussR, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [hpt]
  have hU' : 0 < K.sumP x * K.sumR x - K.sumQ x ^ 2 := hU
  rw [integral_mul_const, integral_prop_mul_gaussR hD hp hU', pi_sq_div_rpow hU']
  have key : invForm (K.sumP x) (K.sumQ x) (K.sumR x) (K.sumB₁ x) (K.sumB₂ x) + -K.sumC x =
      -(K.symF x / K.symU x) := by
    rw [invForm, symF, show K.sumP x * K.sumR x - K.sumQ x ^ 2 = K.symU x from rfl]
    have := hU.ne'
    field_simp
    ring
  rw [← key, Real.exp_add, numShift, numTrace, shiftAt,
    show K.sumP x * K.sumR x - K.sumQ x ^ 2 = K.symU x from rfl]
  ring

/-! ### The momentum integral with one numerator -/

/-- **Two-loop momentum integrals with one propagator as numerator.** Let `P` have the Symanzik
polynomials of the propagators `K` (`PropData.Represents`), with `U, F > 0` and `A₁₁ > 0` on the
open orthant and positive propagators, and let `Ñ = Kn.prop j` be a nonnegative quadratic of
propagator shape (quadratic part `A'`). For positive real labels `ν` with `re a > 1`
(`a = |ν| - D`) and convergent projective integrals of the two insertions,
`∫ Ñ ∏ₐ Dₐ^(-νₐ) d^Dℓ₁ d^Dℓ₂ = π^D / ∏ₐ Γ(νₐ) · (Γ(a) ∫_Δ y^(ν-1) U^(-b) F^(-a) Ñ(s(y))
  + D/2 · Γ(a - 1) ∫_Δ y^(ν-1) U^(-b) F^(-a) (F/U) tr(A' adj A)/U)`,
`s = A⁻¹B` the Gaussian shift (`numShift`, `numTrace`). -/
theorem integral_prop_mul_prod_prop_rpow (hD : 0 < D) {m : ℕ} (K : PropData D (m + 1))
    (Kn : PropData D M) (j : Fin M) (P : FeynmanFamily (m + 1)) (hK : K.Represents P)
    (hP : P.IsHomogeneous) (hprop : ∀ a z, 0 < K.prop a z) (hnum : ∀ z, 0 ≤ Kn.prop j z)
    (hp : ∀ x : Fin (m + 1) → ℝ, (∀ i, 0 < x i) → 0 < K.sumP x)
    (hU : ∀ x : Fin (m + 1) → ℝ, (∀ i, 0 < x i) → 0 < eval x P.U)
    (hF : ∀ x : Fin (m + 1) → ℝ, (∀ i, 0 < x i) → 0 < eval x P.F)
    {ν : Fin (m + 1) → ℝ} (hν : ∀ a, 0 < ν a)
    (ha : 1 < (P.projA (fun a => (ν a : ℂ)) D).re)
    (hint₀ : IntegrableOn (P.projInsert (fun a => (ν a : ℂ)) D 0
      (fun x => (numShift K Kn j x : ℂ))) (openSimplex m))
    (hint₁ : IntegrableOn (P.projInsert (fun a => (ν a : ℂ)) D 1
      (fun x => (numTrace K Kn j x : ℂ))) (openSimplex m)) :
    ((∫ z : V × V, Kn.prop j z * ∏ a, K.prop a z ^ (-ν a) ∂(volume.prod volume) : ℝ) : ℂ) =
      ((π ^ D / ∏ a, Real.Gamma (ν a) : ℝ) : ℂ) *
        (Gamma (P.projA (fun a => (ν a : ℂ)) D) * (∫ x in openSimplex m,
            P.projInsert (fun a => (ν a : ℂ)) D 0 (fun x => (numShift K Kn j x : ℂ)) x) +
          D / 2 * Gamma (P.projA (fun a => (ν a : ℂ)) D - 1) * ∫ x in openSimplex m,
            P.projInsert (fun a => (ν a : ℂ)) D 1 (fun x => (numTrace K Kn j x : ℂ)) x) := by
  obtain ⟨-, hUe, hFe⟩ := hK
  set νc : Fin (m + 1) → ℂ := fun a => (ν a : ℂ)
  set N₀ : (Fin (m + 1) → ℝ) → ℂ := fun x => (numShift K Kn j x : ℂ)
  set N₁ : (Fin (m + 1) → ℝ) → ℂ := fun x => (numTrace K Kn j x : ℂ)
  have ha₀ : 0 < (P.projA νc D - ((0 : ℕ) : ℂ)).re := by simp; linarith
  have ha₁ : 0 < (P.projA νc D - ((1 : ℕ) : ℂ)).re := by simp; linarith
  have hm₀ : Measurable N₀ := measurable_ofReal.comp (measurable_numShift K Kn j)
  have hm₁ : Measurable N₁ := measurable_ofReal.comp (measurable_numTrace K Kn j)
  have hS₀ : IntegrableOn (fun x => P.schwIntegrand νc D x * N₀ x) (posOrthant (m + 1)) :=
    (integrableOn_schwIntegrand_mul_iff P νc D hP hU hF (isHomogNeg_numShift K Kn j) hm₀
      ha₀).mpr hint₀
  have hS₁ : IntegrableOn (fun x => P.schwIntegrand νc D x * N₁ x) (posOrthant (m + 1)) :=
    (integrableOn_schwIntegrand_mul_iff P νc D hP hU hF (isHomogNeg_numTrace K Kn j) hm₁
      ha₁).mpr hint₁
  set g : (Fin (m + 1) → ℝ) → ℝ := fun x =>
    schwR P ν D x * (numShift K Kn j x + D / 2 * numTrace K Kn j x)
  have hg_eq : ∀ x ∈ posOrthant (m + 1), ((g x : ℝ) : ℂ) =
      P.schwIntegrand νc D x * N₀ x + (D / 2 : ℂ) * (P.schwIntegrand νc D x * N₁ x) := by
    intro x hx
    rw [mem_posOrthant] at hx
    rw [show P.schwIntegrand νc D x = _ from schwIntegrand_eq_schwR P ν hx (hU x hx)]
    simp only [g, N₀, N₁]
    push_cast
    ring
  have hgint : IntegrableOn g (posOrthant (m + 1)) := by
    have hc := (hS₀.add (hS₁.const_mul (D / 2 : ℂ))).re
    refine hc.congr_fun (fun x hx => ?_) (measurableSet_posOrthant _)
    simp only [Pi.add_apply]
    rw [← hg_eq x hx]
    exact RCLike.ofReal_re _
  set f : (Fin (m + 1) → ℝ) × (V × V) → ℝ := fun w =>
    (∏ a, w.1 a ^ (ν a - 1)) * (Kn.prop j w.2 * Real.exp (-∑ a, w.1 a * K.prop a w.2))
  have hf0 : ∀ x : Fin (m + 1) → ℝ, (∀ i, 0 < x i) → ∀ z, 0 ≤ f (x, z) := fun x hx z =>
    mul_nonneg (Finset.prod_nonneg fun a _ => Real.rpow_nonneg (hx a).le _)
      (mul_nonneg (hnum z) (Real.exp_pos _).le)
  have hgx : ∀ x : Fin (m + 1) → ℝ, (∀ i, 0 < x i) →
      ∫ z : V × V, f (x, z) ∂(volume.prod volume) = π ^ D * g x := by
    intro x hx
    simp only [f, g]
    rw [integral_const_mul, integral_prop_mul_exp_neg_sum_mul_prop hD K Kn j (hp x hx)
      (by rw [← hUe]; exact hU x hx), schwR, ← hUe, ← hFe]
    ring
  have hfm : AEStronglyMeasurable f ((volume.restrict (posOrthant (m + 1))).prod
      (volume.prod volume)) := by
    refine Measurable.aestronglyMeasurable ?_
    refine (Finset.measurable_prod _ fun a _ => ((measurable_pi_apply a).comp
      measurable_fst).pow_const _).mul
      (((Kn.continuous_prop j).measurable.comp measurable_snd).mul ?_)
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
      have hG := (integrable_prop_mul_gaussR (hp x hx) hUx Kn j (K.sumB₁ x)
        (K.sumB₂ x)).mul_const (Real.exp (-K.sumC x))
      refine (hG.const_mul (∏ a, x a ^ (ν a - 1))).congr
        (Filter.Eventually.of_forall fun z => ?_)
      simp only [f]
      rw [sum_mul_prop, gaussR, mul_assoc (Kn.prop j z), ← Real.exp_add]
      congr 3
      ring
    · refine (hgint.const_mul (π ^ D)).congr ?_
      refine ae_restrict_of_forall_mem (measurableSet_posOrthant _) fun x hx => ?_
      rw [mem_posOrthant] at hx
      show π ^ D * g x = ∫ y, ‖f (x, y)‖ ∂(volume.prod volume)
      rw [← hgx x hx]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [Real.norm_eq_abs]
      exact (abs_of_nonneg (hf0 x hx z)).symm
  have hswap := integral_integral_swap (f := fun x z => f (x, z)) hfint
  have hpt : ∀ z : V × V, Kn.prop j z * ∏ a, K.prop a z ^ (-ν a) =
      (∏ a, Real.Gamma (ν a))⁻¹ * ∫ x in posOrthant (m + 1), f (x, z) := by
    intro z
    rw [prod_rpow_neg_eq_integral (fun a => hprop a z) hν, ← integral_const_mul,
      ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [f]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, ← hswap,
    setIntegral_congr_fun (measurableSet_posOrthant _) fun x hx =>
      hgx x (mem_posOrthant.mp hx), integral_const_mul]
  have hval : ((∫ x in posOrthant (m + 1), g x : ℝ) : ℂ) =
      Gamma (P.projA νc D) * (∫ x in openSimplex m, P.projInsert νc D 0 N₀ x) +
        D / 2 * Gamma (P.projA νc D - 1) * ∫ x in openSimplex m, P.projInsert νc D 1 N₁ x := by
    rw [← integral_complex_ofReal, setIntegral_congr_fun (measurableSet_posOrthant _) hg_eq,
      integral_add hS₀ (hS₁.const_mul _), integral_const_mul,
      integral_schwIntegrand_mul_eq P νc D hP hU hF (isHomogNeg_numShift K Kn j) ha₀ hS₀,
      integral_schwIntegrand_mul_eq P νc D hP hU hF (isHomogNeg_numTrace K Kn j) ha₁ hS₁]
    simp only [Nat.cast_zero, Nat.cast_one, sub_zero]
    ring
  push_cast
  rw [hval]
  ring

end QED.DimReg.TwoLoopBridgeSchwingerNum
