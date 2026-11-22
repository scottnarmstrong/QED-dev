/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI10G0An
public import QED.ThreeLoopD.SetDMastersI9Strip
public import QED.DimReg.FeynmanJoin
public import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Set (e), master `I₁₀`: `G₀` in closed form for `re ε > 0`

For `0 < re ε` (and `‖ε‖ < 1/20`) the two parts of the integrand of `(1 - ε) G₀`
(`QED.ThreeLoopE.i10G0_eq_prod`) converge separately: with `A(σ) = (1 - σ) ^ (-ε)`,

  `(1 - ε) G₀ = J - B(ε, 1 - ε) / (1 - ε)`,
  `J = ∫∫_{(0,1)²} (1 - σ) ^ (-ε) σ ^ (ε - 1) u ^ (-ε) (1 - (1 - u) σ) ^ (1 - 3ε)`.

The substitution `(p, t) ↦ (σ, u) = (p + (1 - p) t, (1 - p) t / (p + (1 - p) t))`
(`QED.ThreeLoopE.i10G0Map`, a bijection of `(0,1)²` with Jacobian `(1 - p) / σ`) has
`1 - σ = (1 - p)(1 - t)` and `1 - (1 - u) σ = 1 - p`, and turns the integrand of `J` into
`σ ^ (2ε - 2) (1 - p) ^ (2 - 5ε) t ^ (-ε) (1 - t) ^ (-ε)` (`QED.ThreeLoopE.i10G0HF`). The
`t`-integral is the Feynman join (`QED.DimReg.integral_feynmanJoin` with `a = b = 1 - ε`,
`A = 1`, `B = p`), `p ^ (ε - 1) B(1 - ε, 1 - ε)`, and the `p`-integral is `B(ε, 3 - 5ε)`. So

  `G₀ = (B(1 - ε, 1 - ε) B(ε, 3 - 5ε) - B(ε, 1 - ε) / (1 - ε)) / (1 - ε)`
  (`QED.ThreeLoopE.i10G0_eq_closed`).

## Main results

* `QED.ThreeLoopE.image_i10G0Map`, `QED.ThreeLoopE.abs_det_i10G0Deriv`.
* `QED.ThreeLoopE.integral_i10G0JF`, `QED.ThreeLoopE.i10G0_eq_closed`.
-/

@[expose] public section

open MeasureTheory Set Complex QED.DimReg QED.ThreeLoopD

namespace QED.ThreeLoopE

/-! ### The change of variables -/

/-- `σ = p + (1 - p) t`. -/
def i10G0Sig (q : ℝ × ℝ) : ℝ := q.1 + (1 - q.1) * q.2

/-- `(p, t) ↦ (σ, u) = (p + (1 - p) t, (1 - p) t / σ)`. -/
noncomputable def i10G0Map (q : ℝ × ℝ) : ℝ × ℝ := (i10G0Sig q, (1 - q.1) * q.2 / i10G0Sig q)

/-- The inverse `(σ, u) ↦ (σ (1 - u), σ u / (1 - σ (1 - u)))`. -/
noncomputable def i10G0Inv (q : ℝ × ℝ) : ℝ × ℝ :=
  (q.1 * (1 - q.2), q.1 * q.2 / (1 - q.1 * (1 - q.2)))

/-- The derivative of `i10G0Map`. -/
noncomputable def i10G0Deriv (q : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  ((1 - q.2) • ContinuousLinearMap.fst ℝ ℝ ℝ + (1 - q.1) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    ((-q.2 / i10G0Sig q ^ 2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ((1 - q.1) * q.1 / i10G0Sig q ^ 2) • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem i10G0Sig_pos {q : ℝ × ℝ} (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    0 < i10G0Sig q := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hq
  have : 0 < 1 - q.1 := by linarith
  unfold i10G0Sig; positivity

theorem one_sub_i10G0Sig (q : ℝ × ℝ) : 1 - i10G0Sig q = (1 - q.1) * (1 - q.2) := by
  unfold i10G0Sig; ring

theorem hasFDerivAt_i10G0Map {q : ℝ × ℝ} (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    HasFDerivAt i10G0Map (i10G0Deriv q) q := by
  have hS := i10G0Sig_pos hq
  have hx := hasFDerivAt_fst (𝕜 := ℝ) (p := q) (E := ℝ) (F := ℝ)
  have hw := hasFDerivAt_snd (𝕜 := ℝ) (p := q) (E := ℝ) (F := ℝ)
  have h1 := (hasFDerivAt_const (1 : ℝ) q).sub hx
  have hσ := hx.add (h1.mul hw)
  have hN := h1.mul hw
  have hσz : q.1 + (1 - q.1) * q.2 ≠ 0 := hS.ne'
  have hI := (hasDerivAt_inv hσz).comp_hasFDerivAt q hσ
  have h := hσ.prodMk (hN.mul hI)
  convert h using 1
  · funext t
    simp only [i10G0Map, i10G0Sig, div_eq_mul_inv]
    rfl
  · refine ContinuousLinearMap.ext fun v => ?_
    refine Prod.ext ?_ ?_
    · simp [i10G0Deriv]
      ring
    · simp [i10G0Deriv, i10G0Sig]
      field_simp
      ring

theorem det_i10G0Deriv (q : ℝ × ℝ) :
    (i10G0Deriv q).det = (1 - q.2) * ((1 - q.1) * q.1 / i10G0Sig q ^ 2) -
      (1 - q.1) * (-q.2 / i10G0Sig q ^ 2) := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ),
    Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, i10G0Deriv]

theorem abs_det_i10G0Deriv {q : ℝ × ℝ} (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    |(i10G0Deriv q).det| = (1 - q.1) / i10G0Sig q := by
  have hS := i10G0Sig_pos hq
  have h1 : 0 < 1 - q.1 := by linarith [hq.1.2]
  have e : (i10G0Deriv q).det = (1 - q.1) / i10G0Sig q := by
    rw [det_i10G0Deriv]
    field_simp
    unfold i10G0Sig
    ring
  rw [e, abs_of_pos (div_pos h1 hS)]

theorem i10G0Map_mem {q : ℝ × ℝ} (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    i10G0Map q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
  have hS := i10G0Sig_pos hq
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hq
  have h1' : 0 < 1 - q.1 := by linarith
  refine ⟨⟨hS, ?_⟩, ?_, ?_⟩
  · show q.1 + (1 - q.1) * q.2 < 1
    nlinarith
  · show 0 < (1 - q.1) * q.2 / i10G0Sig q
    positivity
  · show (1 - q.1) * q.2 / i10G0Sig q < 1
    rw [div_lt_one hS]
    unfold i10G0Sig
    linarith

theorem i10G0Inv_mem {q : ℝ × ℝ} (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    i10G0Inv q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hq
  have h4' : 0 < 1 - q.2 := by linarith
  have hD : 0 < 1 - q.1 * (1 - q.2) := by nlinarith
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · show 0 < q.1 * (1 - q.2)
    positivity
  · show q.1 * (1 - q.2) < 1
    nlinarith
  · show 0 < q.1 * q.2 / (1 - q.1 * (1 - q.2))
    positivity
  · show q.1 * q.2 / (1 - q.1 * (1 - q.2)) < 1
    rw [div_lt_one hD]
    nlinarith

theorem i10G0Inv_map {q : ℝ × ℝ} (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    i10G0Inv (i10G0Map q) = q := by
  have hS := i10G0Sig_pos hq
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hq
  obtain ⟨p, t⟩ := q
  simp only at h1 h2 h3 h4
  have hS' : p + (1 - p) * t ≠ 0 := hS.ne'
  have hp : 1 - p ≠ 0 := by linarith
  have e1 : (p + (1 - p) * t) * (1 - (1 - p) * t / (p + (1 - p) * t)) = p := by
    field_simp; ring
  have e2 : 1 - (p + (1 - p) * t) * (1 - (1 - p) * t / (p + (1 - p) * t)) = 1 - p := by
    rw [e1]
  simp only [i10G0Inv, i10G0Map, i10G0Sig]
  rw [e2, e1]
  refine Prod.ext rfl ?_
  simp only
  field_simp

theorem i10G0Map_inv {q : ℝ × ℝ} (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    i10G0Map (i10G0Inv q) = q := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hq
  obtain ⟨s, u⟩ := q
  simp only at h1 h2 h3 h4
  have hD : 1 - s * (1 - u) ≠ 0 := by nlinarith
  have hs : s ≠ 0 := h1.ne'
  have eS : s * (1 - u) + (1 - s * (1 - u)) * (s * u / (1 - s * (1 - u))) = s := by
    field_simp; ring
  simp only [i10G0Map, i10G0Inv, i10G0Sig]
  rw [eS]
  refine Prod.ext rfl ?_
  simp only
  field_simp

theorem injOn_i10G0Map : InjOn i10G0Map (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  intro z hz z' hz' h
  rw [← i10G0Inv_map hz, ← i10G0Inv_map hz', h]

theorem image_i10G0Map :
    i10G0Map '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) = Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact i10G0Map_mem hz
  · intro hq
    exact ⟨i10G0Inv q, i10G0Inv_mem hq, i10G0Map_inv hq⟩

/-! ### The two parts of the integrand -/

/-- The first part, `(1 - σ) ^ (-ε) σ ^ (ε - 1) u ^ (-ε) (1 - (1 - u) σ) ^ (1 - 3ε)`. -/
noncomputable def i10G0JF (ε : ℂ) (q : ℝ × ℝ) : ℂ :=
  ((1 - q.1 : ℝ) : ℂ) ^ (-ε) * (q.1 : ℂ) ^ (ε - 1) * (q.2 : ℂ) ^ (-ε) *
    ((1 - (1 - q.2) * q.1 : ℝ) : ℂ) ^ (1 - 3 * ε)

/-- The second part, `σ ^ (ε - 1) (1 - σ) ^ (-ε) u ^ (-ε)`, written as Beta integrands. -/
noncomputable def i10G0KF (ε : ℂ) (q : ℝ × ℝ) : ℂ :=
  (q.1 : ℂ) ^ (ε - 1) * ((1 - q.1 : ℝ) : ℂ) ^ ((1 - ε) - 1) * (q.2 : ℂ) ^ ((1 - ε) - 1)

/-- The first part after the substitution: `σ ^ (2ε - 2) (1 - p) ^ (2 - 5ε) t ^ (-ε)
(1 - t) ^ (-ε)`. -/
noncomputable def i10G0HF (ε : ℂ) (q : ℝ × ℝ) : ℂ :=
  ((1 - q.1 : ℝ) : ℂ) ^ (2 - 5 * ε) * feynmanJoin (1 - ε) (1 - ε) 1 q.1 q.2

theorem i10G0F_eq (ε : ℂ) (q : ℝ × ℝ) : i10G0F ε q = i10G0JF ε q - i10G0KF ε q := by
  simp only [i10G0F, i10A, i10PsiF, i10G0JF, i10G0KF, sub_sub_cancel_left]
  ring

theorem i10_cpow_eq_exp {t : ℝ} (ht : 0 < t) (z : ℂ) :
    ((t : ℝ) : ℂ) ^ z = cexp ((Real.log t : ℂ) * z) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr ht.ne'), ofReal_log ht.le]

theorem i10G0_subst_eq (ε : ℂ) {q : ℝ × ℝ} (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    |(i10G0Deriv q).det| • i10G0JF ε (i10G0Map q) = i10G0HF ε q := by
  have hS := i10G0Sig_pos hq
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hq
  have hp : 0 < 1 - q.1 := by linarith
  have ht : 0 < 1 - q.2 := by linarith
  rw [abs_det_i10G0Deriv ⟨⟨h1, h2⟩, h3, h4⟩]
  have eS : q.2 * 1 + (1 - q.2) * q.1 = i10G0Sig q := by unfold i10G0Sig; ring
  have eA : 1 - (i10G0Map q).1 = (1 - q.1) * (1 - q.2) := one_sub_i10G0Sig q
  have eU : 1 - (1 - (i10G0Map q).2) * (i10G0Map q).1 = 1 - q.1 := by
    simp only [i10G0Map]
    field_simp
    unfold i10G0Sig
    ring
  have eD : (((1 - q.1) / i10G0Sig q : ℝ) : ℂ) =
      cexp ((Real.log (1 - q.1) : ℂ) - (Real.log (i10G0Sig q) : ℂ)) := by
    rw [← ofReal_sub, ← ofReal_exp, Real.exp_sub, Real.exp_log hp, Real.exp_log hS]
  simp only [i10G0JF, i10G0HF, feynmanJoin, eA, eU, eS]
  simp only [i10G0Map]
  rw [real_smul, eD, i10_cpow_eq_exp (mul_pos hp ht), i10_cpow_eq_exp hS,
    i10_cpow_eq_exp (div_pos (mul_pos hp h3) hS), i10_cpow_eq_exp hp, i10_cpow_eq_exp hp,
    i10_cpow_eq_exp h3, i10_cpow_eq_exp ht, i10_cpow_eq_exp hS,
    Real.log_mul hp.ne' ht.ne', Real.log_div (mul_pos hp h3).ne' hS.ne',
    Real.log_mul hp.ne' h3.ne']
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ### Integrability and the integrals -/

theorem i10G0_eps {ε : ℂ} (hε : ‖ε‖ < 1 / 20) (hre : 0 < ε.re) :
    0 < (1 - ε).re ∧ 0 < (3 - 5 * ε).re := by
  have hr := i10_re_le hε
  constructor <;> simp <;> linarith

theorem integrableOn_i10G0KF {ε : ℂ} (hε : ‖ε‖ < 1 / 20) (hre : 0 < ε.re) :
    IntegrableOn (i10G0KF ε) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  obtain ⟨h1, -⟩ := i10G0_eps hε hre
  rw [IntegrableOn, volume_restrict_prod2]
  exact (i9_integrableOn_beta hre h1).mul_prod (i9_integrableOn_cpow h1)

theorem integral_i10G0KF {ε : ℂ} (hε : ‖ε‖ < 1 / 20) (hre : 0 < ε.re) :
    ∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i10G0KF ε q = i9Beta ε (1 - ε) * (1 / (1 - ε)) := by
  obtain ⟨h1, -⟩ := i10G0_eps hε hre
  rw [volume_restrict_prod2]
  refine (integral_prod_mul (fun x : ℝ => (x : ℂ) ^ (ε - 1) * ((1 - x : ℝ) : ℂ) ^ ((1 - ε) - 1))
    (fun y : ℝ => (y : ℂ) ^ ((1 - ε) - 1))).trans ?_
  rw [i9_integral_beta hre h1, i9_integral_cpow h1]

theorem integrableOn_i10G0JF {ε : ℂ} (hε : ‖ε‖ < 1 / 20) (hre : 0 < ε.re) :
    IntegrableOn (i10G0JF ε) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  refine ((integrableOn_i10G0F hε).add (integrableOn_i10G0KF hε hre)).congr_fun
    (fun q _ => ?_) (measurableSet_Ioo.prod measurableSet_Ioo)
  simp only [Pi.add_apply]
  rw [i10G0F_eq]; ring

theorem integral_i10G0HF_inner {ε : ℂ} (hε : ‖ε‖ < 1 / 20) (hre : 0 < ε.re) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∫ t in Ioo (0 : ℝ) 1, i10G0HF ε (p, t) =
      i9Beta (1 - ε) (1 - ε) * ((p : ℂ) ^ (ε - 1) * ((1 - p : ℝ) : ℂ) ^ ((3 - 5 * ε) - 1)) := by
  obtain ⟨h1, -⟩ := i10G0_eps hε hre
  simp only [i10G0HF]
  rw [integral_const_mul, integral_feynmanJoin h1 h1 one_pos hp.1, ofReal_one, one_cpow, i9Beta,
    show -(1 - ε) = ε - 1 by ring, show (3 - 5 * ε) - 1 = 2 - 5 * ε by ring]
  ring

theorem integral_i10G0JF {ε : ℂ} (hε : ‖ε‖ < 1 / 20) (hre : 0 < ε.re) :
    ∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i10G0JF ε q =
      i9Beta (1 - ε) (1 - ε) * i9Beta ε (3 - 5 * ε) := by
  obtain ⟨h1, h3⟩ := i10G0_eps hε hre
  have : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hd : ∀ q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
      HasFDerivWithinAt i10G0Map (i10G0Deriv q) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) q :=
    fun q hq => (hasFDerivAt_i10G0Map hq).hasFDerivWithinAt
  have hI : IntegrableOn (fun q => |(i10G0Deriv q).det| • i10G0JF ε (i10G0Map q))
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hS hd injOn_i10G0Map
      (i10G0JF ε)).1 (by rw [image_i10G0Map]; exact integrableOn_i10G0JF hε hre)
  have hH : IntegrableOn (i10G0HF ε) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    hI.congr_fun (fun q hq => i10G0_subst_eq ε hq) hS
  rw [IntegrableOn, Measure.volume_eq_prod] at hH
  calc _ = ∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
        |(i10G0Deriv q).det| • i10G0JF ε (i10G0Map q) := by
        rw [← integral_image_eq_integral_abs_det_fderiv_smul volume hS hd injOn_i10G0Map,
          image_i10G0Map]
    _ = ∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i10G0HF ε q :=
        setIntegral_congr_fun hS fun q hq => i10G0_subst_eq ε hq
    _ = ∫ p in Ioo (0 : ℝ) 1, ∫ t in Ioo (0 : ℝ) 1, i10G0HF ε (p, t) := by
        rw [Measure.volume_eq_prod, setIntegral_prod _ hH]
    _ = ∫ p in Ioo (0 : ℝ) 1, i9Beta (1 - ε) (1 - ε) *
        ((p : ℂ) ^ (ε - 1) * ((1 - p : ℝ) : ℂ) ^ ((3 - 5 * ε) - 1)) :=
        setIntegral_congr_fun measurableSet_Ioo fun p hp => integral_i10G0HF_inner hε hre hp
    _ = _ := by rw [integral_const_mul, i9_integral_beta hre h3]

/-- **`G₀` in closed form**: `(B(1 - ε, 1 - ε) B(ε, 3 - 5ε) - B(ε, 1 - ε) / (1 - ε)) / (1 - ε)`
(for `0 < re ε`; the right side continues `G₀`). -/
noncomputable def i10G0Cl (ε : ℂ) : ℂ :=
  (i9Beta (1 - ε) (1 - ε) * i9Beta ε (3 - 5 * ε) - i9Beta ε (1 - ε) / (1 - ε)) / (1 - ε)

theorem i10G0_eq_closed {ε : ℂ} (hε : ‖ε‖ < 1 / 20) (hre : 0 < ε.re) :
    i10G0 ε = i10G0Cl ε := by
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  rw [i10G0_eq_prod hε, setIntegral_congr_fun hS fun q _ => i10G0F_eq ε q,
    integral_sub (integrableOn_i10G0JF hε hre) (integrableOn_i10G0KF hε hre),
    integral_i10G0JF hε hre, integral_i10G0KF hε hre, i10G0Cl]
  ring

end QED.ThreeLoopE
