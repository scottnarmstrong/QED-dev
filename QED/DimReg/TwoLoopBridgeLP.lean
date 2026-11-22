/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.TwoLoopBridgeLPChange
public import QED.DimReg.BetaPrime
public import QED.DimReg.Tadpole
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# The Lee–Pomeransky integral in projective form

For a family with homogeneous Symanzik polynomials (`U` of degree `L`, `F` of degree `L + 1`),
positive on the open orthant, the Lee–Pomeransky integral (`QED.DimReg.lpIntegral`) equals the
projective integral over the simplex:
`∫_{(0,∞)^N} x^(ν-1) (U + F)^(-d/2) = Γ(a) Γ(b) / Γ(d/2) · ∫_Δ y^(ν-1) U^(-b) F^(-a)`, with
`a = |ν| - L d / 2` and `b = (L + 1) d / 2 - |ν|` (so `a + b = d / 2`), wherever `re a > 0`,
`re b > 0` and the Lee–Pomeransky integral converges. With the Lee–Pomeransky Γ-prefactor this is
the standard projective representation
`I(d, ν) = Γ(a) / ∏ Γ(νᵢ) · ∫_Δ y^(ν-1) U^(|ν| - (L+1) d/2) F^(L d/2 - |ν|)`.

The proof writes the orthant as a cone over the open simplex,
`z = s · (x, 1 - ∑ x)` with Jacobian `s^(N-1)` (`QED.DimReg.LPChange.integral_posOrthant_eq_cone`),
uses homogeneity, `U(s y) + F(s y) = s^L U(y) (1 + s F(y) / U(y))`, to bring the ray integrand
to the Beta integrand of the second kind, and evaluates the ray integral with
`QED.DimReg.integral_betaPrime`.

## Main results

* `QED.DimReg.LPChange.eval_smul_of_isHomogeneous`: `φ(s • y) = s^n φ(y)`.
* `QED.DimReg.LPChange.lpIntegral_eq_proj`: the Lee–Pomeransky integral in projective form.
* `QED.DimReg.LPChange.integral_eq_proj`: the normalized integral in projective form.
* `QED.DimReg.LPChange.lpConvergent_iff_proj`: the Lee–Pomeransky integral converges absolutely
  exactly when the projective integral does.
* `QED.DimReg.LPChange.integral_tadpoleFamily_proj`: check, the one-loop tadpole by this route.
-/

@[expose] public section

open MeasureTheory Set Complex MvPolynomial

namespace QED.DimReg.LPChange

open QED.Integration.Feynman (simplexPoint)
open QED.Integration.ChengWu (openSimplex mem_openSimplex)
open QED.Integration.TwoLoop (simplexPoint_castSucc simplexPoint_last)

variable {m : ℕ}

theorem eval_smul_of_isHomogeneous {σ : Type*} [Fintype σ] {φ : MvPolynomial σ ℝ} {n : ℕ}
    (hφ : φ.IsHomogeneous n) (s : ℝ) (y : σ → ℝ) : eval (s • y) φ = s ^ n * eval y φ := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← hφ.degree_eq_sum_deg_support hk]
  ring

theorem simplexPoint_pos {x : Fin m → ℝ} (hx : x ∈ openSimplex m) (i : Fin (m + 1)) :
    0 < simplexPoint x i := by
  rw [mem_openSimplex] at hx
  induction i using Fin.lastCases with
  | last => rw [simplexPoint_last]; linarith [hx.2]
  | cast j => rw [simplexPoint_castSucc]; exact hx.1 j

/-- A principal power of a positive real as an exponential. -/
theorem cpow_ofReal_pos {r : ℝ} (hr : 0 < r) (c : ℂ) :
    (r : ℂ) ^ c = exp ((Real.log r : ℂ) * c) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr.ne'), ofReal_log hr.le]

end QED.DimReg.LPChange

/-! ### The exponents and the projective integrand -/

namespace QED.DimReg.FeynmanFamily

open QED.Integration.Feynman (simplexPoint)

variable {N : ℕ}

/-- The ray exponent `a = |ν| - L d / 2`. -/
noncomputable def projA (P : FeynmanFamily N) (ν : Fin N → ℂ) (d : ℂ) : ℂ :=
  ∑ i, ν i - P.loops * d / 2

/-- The complementary exponent `b = (L + 1) d / 2 - |ν|`. -/
noncomputable def projB (P : FeynmanFamily N) (ν : Fin N → ℂ) (d : ℂ) : ℂ :=
  (P.loops + 1) * d / 2 - ∑ i, ν i

theorem projA_add_projB (P : FeynmanFamily N) (ν : Fin N → ℂ) (d : ℂ) :
    P.projA ν d + P.projB ν d = d / 2 := by
  simp only [projA, projB]; ring

/-- The projective integrand `y^(ν-1) U(y)^(-b) F(y)^(-a)` at the simplex point
`y = simplexPoint x`. -/
noncomputable def projIntegrand {m : ℕ} (P : FeynmanFamily (m + 1)) (ν : Fin (m + 1) → ℂ)
    (d : ℂ) (x : Fin m → ℝ) : ℂ :=
  (∏ i, (simplexPoint x i : ℂ) ^ (ν i - 1)) * (eval (simplexPoint x) P.U : ℂ) ^ (-P.projB ν d) *
    (eval (simplexPoint x) P.F : ℂ) ^ (-P.projA ν d)

end QED.DimReg.FeynmanFamily

namespace QED.DimReg.LPChange

open QED.Integration.Feynman (simplexPoint)
open QED.Integration.ChengWu (openSimplex mem_openSimplex)
open QED.Integration.TwoLoop (simplexPoint_last)

variable {m : ℕ}

open FeynmanFamily

/-! ### The ray integrand -/

variable (P : FeynmanFamily (m + 1)) (ν : Fin (m + 1) → ℂ) (d : ℂ)

/-- On the ray through a positive point `y`, the cone integrand of the Lee–Pomeransky integrand
is the Beta integrand of the second kind with `c = F(y) / U(y)`. -/
theorem cone_lpIntegrand_eq (hP : P.IsHomogeneous) {y : Fin (m + 1) → ℝ} (hy : ∀ i, 0 < y i)
    (hU : 0 < eval y P.U) (hF : 0 < eval y P.F) {s : ℝ} (hs : 0 < s) :
    s ^ m • lpIntegrand P.lpPoly ν d (s • y) =
      ((∏ i, (y i : ℂ) ^ (ν i - 1)) * (eval y P.U : ℂ) ^ (-(d / 2))) *
        betaPrimeIntegrand (P.projA ν d) (P.projB ν d) (eval y P.F / eval y P.U) s := by
  set u := eval y P.U
  set f := eval y P.F
  have hw : 0 < 1 + f / u * s := by positivity
  have hG : P.lpPoly (s • y) = s ^ P.loops * u * (1 + f / u * s) := by
    rw [FeynmanFamily.lpPoly, eval_add, eval_smul_of_isHomogeneous hP.1,
      eval_smul_of_isHomogeneous hP.2]
    field_simp
    ring
  rw [lpIntegrand, betaPrimeIntegrand, hG, Complex.real_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [projA_add_projB]
  have hpos : ∀ i, 0 < s * y i := fun i => mul_pos hs (hy i)
  simp only [cpow_ofReal_pos (hpos _), cpow_ofReal_pos (hy _), cpow_ofReal_pos hU,
    cpow_ofReal_pos hs, cpow_ofReal_pos hw, cpow_ofReal_pos (by positivity :
      0 < s ^ P.loops * u * (1 + f / u * s)), ← Complex.exp_sum]
  rw [Real.log_mul (by positivity) hw.ne', Real.log_mul (by positivity) hU.ne', Real.log_pow]
  have hsm : ((s ^ m : ℝ) : ℂ) = exp ((Real.log s : ℂ) * m) := by
    rw [← cpow_ofReal_pos hs, ofReal_pow, cpow_natCast]
  rw [hsm]
  simp only [← Complex.exp_add]
  congr 1
  simp only [Real.log_mul hs.ne' (hy _).ne', ofReal_add, ofReal_mul, ofReal_natCast, add_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, mul_sub]
  simp only [projA]
  push_cast
  ring

/-- `U^(-d/2) (F / U)^(-a) = U^(-b) F^(-a)`. -/
theorem cpow_U_mul_ratio {u f : ℝ} (hu : 0 < u) (hf : 0 < f) :
    (u : ℂ) ^ (-(d / 2)) * ((f / u : ℝ) : ℂ) ^ (-P.projA ν d) =
      (u : ℂ) ^ (-P.projB ν d) * (f : ℂ) ^ (-P.projA ν d) := by
  rw [cpow_ofReal_pos hu, cpow_ofReal_pos (div_pos hf hu), cpow_ofReal_pos hu,
    cpow_ofReal_pos hf, ← Complex.exp_add, ← Complex.exp_add, Real.log_div hf.ne' hu.ne']
  congr 1
  have h := projA_add_projB P ν d
  rw [← h]
  push_cast
  ring

/-! ### The projective form -/

/-- **The Lee–Pomeransky integral in projective form.** For a homogeneous family with `U, F > 0`
on the open orthant, `re a > 0`, `re b > 0` and absolute convergence,
`∫_{(0,∞)^N} x^(ν-1) (U + F)^(-d/2) = Γ(a) Γ(b) / Γ(d/2) · ∫_Δ y^(ν-1) U^(-b) F^(-a)`. -/
theorem lpIntegral_eq_proj (hP : P.IsHomogeneous)
    (hU : ∀ y : Fin (m + 1) → ℝ, (∀ i, 0 < y i) → 0 < eval y P.U)
    (hF : ∀ y : Fin (m + 1) → ℝ, (∀ i, 0 < y i) → 0 < eval y P.F)
    (ha : 0 < (P.projA ν d).re) (hb : 0 < (P.projB ν d).re)
    (hconv : LPConvergent P.lpPoly ν d) :
    lpIntegral P.lpPoly ν d = Gamma (P.projA ν d) * Gamma (P.projB ν d) / Gamma (d / 2) *
      ∫ x in openSimplex m, P.projIntegrand ν d x := by
  rw [lpIntegral, integral_posOrthant_eq_cone _ hconv, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_openSimplex fun x hx => ?_
  have hy := simplexPoint_pos hx
  have hUx := hU _ hy
  have hFx := hF _ hy
  rw [setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) =>
      cone_lpIntegrand_eq P ν d hP hy hUx hFx hs,
    integral_const_mul, integral_betaPrime ha hb (div_pos hFx hUx), projA_add_projB,
    projIntegrand]
  rw [show ∀ A B C D : ℂ, A * B * (C * D) = (B * C) * (A * D) / 1 from fun _ _ _ _ => by ring,
    cpow_U_mul_ratio P ν d hUx hFx, div_one]
  ring

/-- **The normalized integral in projective form**:
`I(d, ν) = Γ(a) / ∏ Γ(νᵢ) · ∫_Δ y^(ν-1) U^(|ν| - (L+1) d/2) F^(L d/2 - |ν|)`. -/
theorem integral_eq_proj (hP : P.IsHomogeneous)
    (hU : ∀ y : Fin (m + 1) → ℝ, (∀ i, 0 < y i) → 0 < eval y P.U)
    (hF : ∀ y : Fin (m + 1) → ℝ, (∀ i, 0 < y i) → 0 < eval y P.F)
    (ha : 0 < (P.projA ν d).re) (hb : 0 < (P.projB ν d).re)
    (hconv : LPConvergent P.lpPoly ν d) :
    P.integral ν d = Gamma (P.projA ν d) / (∏ i, Gamma (ν i)) *
      ∫ x in openSimplex m, P.projIntegrand ν d x := by
  have hd : 0 < (d / 2).re := by rw [← projA_add_projB, add_re]; linarith
  have hΓd := Gamma_ne_zero_of_re_pos hd
  have hΓb := Gamma_ne_zero_of_re_pos hb
  rw [FeynmanFamily.integral, lpIntegral_eq_proj P ν d hP hU hF ha hb hconv,
    FeynmanFamily.prefactor]
  change Gamma (d / 2) / (Gamma (P.projB ν d) * _) * _ = _
  field_simp

/-! ### Convergence -/

theorem ofReal_norm_betaPrimeIntegrand (a b : ℂ) {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    ((‖betaPrimeIntegrand a b c s‖ : ℝ) : ℂ) = betaPrimeIntegrand a.re b.re c s := by
  have h1 : 0 < 1 + c * s := by positivity
  rw [betaPrimeIntegrand, betaPrimeIntegrand, norm_mul, norm_cpow_eq_rpow_re_of_pos hs,
    norm_cpow_eq_rpow_re_of_pos h1, ofReal_mul, ofReal_cpow hs.le, ofReal_cpow h1.le]
  push_cast
  simp

theorem ofReal_integral_norm_betaPrime {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {c : ℝ}
    (hc : 0 < c) :
    ((∫ s in Ioi 0, ‖betaPrimeIntegrand a b c s‖ : ℝ) : ℂ) =
      (c : ℂ) ^ (-(a.re : ℂ)) * (Gamma a.re * Gamma b.re / Gamma (a.re + b.re)) := by
  rw [← integral_complex_ofReal, ← integral_betaPrime (a := a.re) (b := b.re) (by simpa)
    (by simpa) hc]
  exact setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) =>
    ofReal_norm_betaPrimeIntegrand a b hc hs

/-- The ray integral of the norm scales as `c^(-re a)`. -/
theorem integral_norm_betaPrime {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {c : ℝ}
    (hc : 0 < c) :
    ∫ s in Ioi 0, ‖betaPrimeIntegrand a b c s‖ =
      c ^ (-a.re) * ∫ s in Ioi 0, ‖betaPrimeIntegrand a b 1 s‖ := by
  apply ofReal_injective
  rw [ofReal_mul, ofReal_integral_norm_betaPrime ha hb hc,
    ofReal_integral_norm_betaPrime ha hb one_pos, ofReal_cpow hc.le, ofReal_one, one_cpow,
    one_mul, ofReal_neg]

theorem integral_norm_betaPrime_one_ne_zero {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    ∫ s in Ioi 0, ‖betaPrimeIntegrand a b 1 s‖ ≠ 0 := by
  intro h
  have := ofReal_integral_norm_betaPrime ha hb one_pos
  rw [h, ofReal_zero, ofReal_one, one_cpow, one_mul] at this
  have hab : 0 < ((a.re : ℂ) + b.re).re := by simp; linarith
  exact div_ne_zero (mul_ne_zero (Gamma_ne_zero_of_re_pos (by simpa))
    (Gamma_ne_zero_of_re_pos (by simpa))) (Gamma_ne_zero_of_re_pos hab) this.symm

/-- The projective integrand as the ray prefactor times `c^(-a)`, `c = F / U`. -/
theorem projIntegrand_eq {x : Fin m → ℝ} (hU : 0 < eval (simplexPoint x) P.U)
    (hF : 0 < eval (simplexPoint x) P.F) :
    P.projIntegrand ν d x =
      ((∏ i, (simplexPoint x i : ℂ) ^ (ν i - 1)) * (eval (simplexPoint x) P.U : ℂ) ^ (-(d / 2)))
        * (((eval (simplexPoint x) P.F / eval (simplexPoint x) P.U : ℝ) : ℂ) ^ (-P.projA ν d)) := by
  rw [projIntegrand, mul_assoc, mul_assoc, cpow_U_mul_ratio P ν d hU hF]

theorem continuous_simplexPoint : Continuous (simplexPoint (m := m)) :=
  continuous_pi fun i => QED.Integration.TwoLoop.continuous_simplexPoint i

theorem measurable_projIntegrand : Measurable (P.projIntegrand ν d) := by
  unfold projIntegrand
  refine (Measurable.mul ?_ ?_).mul ?_
  · exact Finset.measurable_prod _ fun i _ =>
      (measurable_ofReal.comp (continuous_simplexPoint.measurable.eval)).pow_const _
  · exact (measurable_ofReal.comp
      ((MvPolynomial.continuous_eval P.U).comp continuous_simplexPoint).measurable).pow_const _
  · exact (measurable_ofReal.comp
      ((MvPolynomial.continuous_eval P.F).comp continuous_simplexPoint).measurable).pow_const _

theorem measurable_coneIntegrand_lpIntegrand :
    Measurable (coneIntegrand (lpIntegrand P.lpPoly ν d)) := by
  unfold coneIntegrand
  refine (measurable_fst.pow_const _).smul ((measurable_lpIntegrand
    P.continuous_lpPoly.measurable ν d).comp ?_)
  exact (continuous_fst.smul (continuous_simplexPoint.comp continuous_snd)).measurable

/-- **Convergence in projective form.** Under the hypotheses of `lpIntegral_eq_proj`, the
Lee–Pomeransky integral converges absolutely exactly when the projective integral does. -/
theorem lpConvergent_iff_proj (hP : P.IsHomogeneous)
    (hU : ∀ y : Fin (m + 1) → ℝ, (∀ i, 0 < y i) → 0 < eval y P.U)
    (hF : ∀ y : Fin (m + 1) → ℝ, (∀ i, 0 < y i) → 0 < eval y P.F)
    (ha : 0 < (P.projA ν d).re) (hb : 0 < (P.projB ν d).re) :
    LPConvergent P.lpPoly ν d ↔ IntegrableOn (P.projIntegrand ν d) (openSimplex m) := by
  rw [LPConvergent, integrableOn_posOrthant_iff, IntegrableOn, ← Measure.prod_restrict,
    integrable_prod_iff' (measurable_coneIntegrand_lpIntegrand P ν d).aestronglyMeasurable]
  have hray : ∀ x ∈ openSimplex m, ∀ s ∈ Ioi (0 : ℝ),
      coneIntegrand (lpIntegrand P.lpPoly ν d) (s, x) =
        ((∏ i, (simplexPoint x i : ℂ) ^ (ν i - 1)) *
          (eval (simplexPoint x) P.U : ℂ) ^ (-(d / 2))) *
          betaPrimeIntegrand (P.projA ν d) (P.projB ν d)
            (eval (simplexPoint x) P.F / eval (simplexPoint x) P.U) s := fun x hx s hs =>
    cone_lpIntegrand_eq P ν d hP (simplexPoint_pos hx) (hU _ (simplexPoint_pos hx))
      (hF _ (simplexPoint_pos hx)) hs
  have h1 : ∀ᵐ x ∂(volume.restrict (openSimplex m)),
      Integrable (fun s => coneIntegrand (lpIntegrand P.lpPoly ν d) (s, x))
        (volume.restrict (Ioi 0)) := by
    refine ae_restrict_of_forall_mem measurableSet_openSimplex fun x hx => ?_
    have hc := div_pos (hF _ (simplexPoint_pos hx)) (hU _ (simplexPoint_pos hx))
    exact IntegrableOn.congr_fun ((integrableOn_betaPrime ha hb hc).const_mul _)
      (fun s hs => (hray x hx s hs).symm) measurableSet_Ioi
  rw [and_iff_right h1]
  set J1 := ∫ s in Ioi 0, ‖betaPrimeIntegrand (P.projA ν d) (P.projB ν d) 1 s‖
  have h2 : ∀ x ∈ openSimplex m,
      ∫ s in Ioi 0, ‖coneIntegrand (lpIntegrand P.lpPoly ν d) (s, x)‖ =
        J1 * ‖P.projIntegrand ν d x‖ := by
    intro x hx
    have hUx := hU _ (simplexPoint_pos hx)
    have hFx := hF _ (simplexPoint_pos hx)
    rw [setIntegral_congr_fun measurableSet_Ioi fun s hs => by rw [hray x hx s hs, norm_mul],
      integral_const_mul, integral_norm_betaPrime ha hb (div_pos hFx hUx),
      projIntegrand_eq P ν d hUx hFx, norm_mul (_ * _),
      norm_cpow_eq_rpow_re_of_pos (div_pos hFx hUx), neg_re]
    ring
  rw [integrable_congr (ae_restrict_of_forall_mem measurableSet_openSimplex h2),
    integrable_const_mul_iff (isUnit_iff_ne_zero.mpr
      (integral_norm_betaPrime_one_ne_zero ha hb)),
    integrable_norm_iff (measurable_projIntegrand P ν d).aestronglyMeasurable, IntegrableOn]

/-! ### Check: the one-loop tadpole -/

theorem integral_fin_zero (g : (Fin 0 → ℝ) → ℂ) :
    ∫ x in openSimplex 0, g x = g Fin.elim0 := by
  have h : openSimplex 0 = univ := by ext x; simp [mem_openSimplex]
  rw [h, Measure.restrict_univ, volume_pi, Measure.pi_of_empty (x := Fin.elim0),
    integral_dirac]

/-- The projective route reproduces the tadpole closed form `QED.DimReg.tadpole`
(the case `N = 1`, where the simplex is a point), with convergence also obtained from the
projective side. -/
theorem integral_tadpoleFamily_proj {m2 : ℝ} (hm : 0 < m2) {ν d : ℂ}
    (h1 : 0 < (ν - d / 2).re) (h2 : 0 < (d - ν).re) :
    (tadpoleFamily m2).integral (fun _ => ν) d = tadpole m2 ν d := by
  set P := tadpoleFamily m2
  have hU : ∀ y : Fin 1 → ℝ, (∀ i, 0 < y i) → 0 < eval y P.U := fun y hy => by
    simpa [P, tadpoleFamily] using hy 0
  have hF : ∀ y : Fin 1 → ℝ, (∀ i, 0 < y i) → 0 < eval y P.F := fun y hy => by
    simpa [P, tadpoleFamily] using mul_pos hm (pow_pos (hy 0) 2)
  have hA : P.projA (fun _ => ν) d = ν - d / 2 := by
    simp [projA, P, tadpoleFamily]
  have hB : P.projB (fun _ => ν) d = d - ν := by
    simp [projB, P, tadpoleFamily]; ring
  have ha : 0 < (P.projA (fun _ => ν) d).re := hA ▸ h1
  have hb : 0 < (P.projB (fun _ => ν) d).re := hB ▸ h2
  have hpt : simplexPoint (Fin.elim0 : Fin 0 → ℝ) = fun _ => 1 := by
    funext i
    rw [Fin.fin_one_eq_zero i, show (0 : Fin 1) = Fin.last 0 from rfl, simplexPoint_last]
    simp
  have hconv : LPConvergent P.lpPoly (fun _ => ν) d := by
    rw [lpConvergent_iff_proj P _ d (tadpoleFamily_isHomogeneous m2) hU hF ha hb]
    have h : openSimplex 0 = univ := by ext x; simp [mem_openSimplex]
    rw [h, IntegrableOn, Measure.restrict_univ, volume_pi,
      Measure.pi_of_empty (x := Fin.elim0)]
    exact integrable_dirac enorm_lt_top
  rw [integral_eq_proj P _ d (tadpoleFamily_isHomogeneous m2) hU hF ha hb hconv,
    integral_fin_zero, projIntegrand, hpt, hA, tadpole]
  simp [P, tadpoleFamily]

end QED.DimReg.LPChange
