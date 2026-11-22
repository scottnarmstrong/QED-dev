/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellCovX
public import QED.TwoLoop.VPHalfAtAssemblyLimit
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Tactic.Ring

/-!
# Set (c): the `x`-integrals of `covAU`, `covBU` and their `s`-derivatives

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step b4. With
`w(x) = (1 - 2x)(x²/2 - x³/3)`, `T_f(x) = μ_f²/m²`, `μ_f = specMu M_f x`,

`covAX(s) = ∫₀¹ ∑_f c_f w(x) (x(1-x))⁻¹ covAU(T_f(x), s) dx`, and `covBX` with `covBU`.

The integrands are bounded uniformly near the shell because `|covAU'(T, s)| ≤ C/(T m²)` and
`T_f(x) m² x(1-x) = M_f²`. The coincident points `Λ = μ_f` are Lebesgue null.

* `hasDerivAt_covAX`, `hasDerivAt_covBX`: derivatives in `s` at `s₀` near `-m²`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetCRegDisp

open QED.WickModel
open QED.TwoLoop.VPHalfAtAssembly (specMu ae_specMu_ne mem_Ioo_mul_pos)

/-- The weight `w(x) = (1 - 2x)(x²/2 - x³/3)`. -/
noncomputable def covWt (x : ℝ) : ℝ := (1 - 2 * x) * (x ^ 2 / 2 - x ^ 3 / 3)

/-- The rescaled spectral mass `T_f(x) = μ_f²/m²`. -/
noncomputable def covT (P : Params) (f : Fin 3) (x : ℝ) : ℝ := specMu (P.mass f) x ^ 2 / P.m ^ 2

/-- A flavour-summed `x`-integrand. -/
noncomputable def covG (P : Params) (K : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (s x : ℝ) : ℝ :=
  ∑ f, P.loopCoeff f * covWt x * (x * (1 - x))⁻¹ * K P.m P.mγ P.Λ (covT P f x) s

/-- `covAX(s) = ∫₀¹ ∑_f c_f w(x) (x(1-x))⁻¹ covAU(T_f(x), s) dx`. -/
noncomputable def covAX (P : Params) (s : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, covG P covAU s x

/-- The derivative of `covAX`. -/
noncomputable def covAX' (P : Params) (s : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, covG P covAU' s x

/-- `covBX(s) = ∫₀¹ ∑_f c_f w(x) (x(1-x))⁻¹ covBU(T_f(x), s) dx`. -/
noncomputable def covBX (P : Params) (s : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, covG P covBU s x

/-- The derivative of `covBX`. -/
noncomputable def covBX' (P : Params) (s : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, covG P covBU' s x

theorem abs_covWt_le {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : |covWt x| ≤ 1 := by
  obtain ⟨h0, h1⟩ := hx
  unfold covWt
  rw [abs_mul]
  have a1 : |1 - 2 * x| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hx3 : x ^ 3 ≤ x ^ 2 := by nlinarith [sq_nonneg x]
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  have hx0 : 0 ≤ x ^ 3 := by positivity
  have a2 : |x ^ 2 / 2 - x ^ 3 / 3| ≤ 1 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
  calc |1 - 2 * x| * |x ^ 2 / 2 - x ^ 3 / 3| ≤ 1 * 1 :=
        mul_le_mul a1 a2 (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-! ### Measurability in `x` -/

theorem measurable_quadTailVP_uncurry (A B : ℝ) :
    Measurable fun q : ℝ × ℝ => quadTailVP A B q.1 q.2 := by
  unfold quadTailVP
  fun_prop

theorem measurable_quadTailVP_comp {α : Type*} [MeasurableSpace α] (A B : ℝ) {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun a => quadTailVP A B (f a) (g a) :=
  (measurable_quadTailVP_uncurry A B).comp (hf.prodMk hg)

theorem measurable_bubQ_uncurry (A B : ℝ) :
    Measurable fun q : ℝ × ℝ => bubQ A B q.1 q.2 := by
  unfold bubQ
  fun_prop

theorem measurable_bubQ_comp {α : Type*} [MeasurableSpace α] (A B : ℝ) {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun a => bubQ A B (f a) (g a) :=
  (measurable_bubQ_uncurry A B).comp (hf.prodMk hg)

theorem measurable_covAInt_uncurry (m mγ Λ s : ℝ) :
    Measurable fun r : ℝ × ℝ => covAInt m mγ Λ r.1 s r.2 := by
  have hw : Measurable fun r : ℝ × ℝ => seArg m s r.2 := (measurable_seArg m s).comp measurable_snd
  have h1 : Measurable fun r : ℝ × ℝ => photonTail (vpPhotonT m mγ Λ r.1) (seArg m s r.2) :=
    (measurable_photonTail_vp m mγ Λ).comp (measurable_fst.prodMk hw)
  have h2 : Measurable fun r : ℝ × ℝ =>
      quadTailVP (mγ ^ 2) (Λ ^ 2) (r.1 * m ^ 2) (seArg m s r.2) :=
    measurable_quadTailVP_comp _ _ (measurable_fst.mul_const _) hw
  unfold covAInt
  exact (((measurable_const.mul measurable_snd).sub measurable_const).mul h1).add
    ((((measurable_snd.mul_const _).add (measurable_snd.mul_const _)).sub
      ((measurable_const.mul (measurable_snd.pow_const 2)).mul_const _)).mul h2)

theorem measurable_covADer_uncurry (m mγ Λ s : ℝ) :
    Measurable fun r : ℝ × ℝ => covADer m mγ Λ r.1 s r.2 := by
  have hw : Measurable fun r : ℝ × ℝ => seArg m s r.2 := (measurable_seArg m s).comp measurable_snd
  have h1 : Measurable fun r : ℝ × ℝ => vpPhotonT m mγ Λ r.1 (seArg m s r.2) :=
    (measurable_vpPhotonT m mγ Λ).comp (measurable_fst.prodMk hw)
  have h2 : Measurable fun r : ℝ × ℝ =>
      quadTailVP (mγ ^ 2) (Λ ^ 2) (r.1 * m ^ 2) (seArg m s r.2) :=
    measurable_quadTailVP_comp _ _ (measurable_fst.mul_const _) hw
  have h3 : Measurable fun r : ℝ × ℝ => bubQ (mγ ^ 2) (Λ ^ 2) (r.1 * m ^ 2) (seArg m s r.2) :=
    measurable_bubQ_comp _ _ (measurable_fst.mul_const _) hw
  unfold covADer
  exact (((measurable_const.mul measurable_snd).sub measurable_const).mul
    (h1.neg.mul measurable_snd)).add
    (((measurable_snd.sub (measurable_const.mul (measurable_snd.pow_const 2))).mul h2).add
      ((((measurable_snd.mul_const _).add (measurable_snd.mul_const _)).sub
        ((measurable_const.mul (measurable_snd.pow_const 2)).mul_const _)).mul
          (h3.neg.mul measurable_snd)))

/-- An interval integral over `[0, 1]` of a jointly measurable integrand is measurable. -/
theorem measurable_intervalIntegral_unit {g : ℝ × ℝ → ℝ} (hg : Measurable g) :
    Measurable fun T => ∫ y in (0 : ℝ)..1, g (T, y) := by
  have h := (hg.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) 1))).measurable
  convert h using 1
  funext T
  simp only [intervalIntegral.integral_of_le zero_le_one]

theorem measurable_covAU (m mγ Λ s : ℝ) : Measurable fun T => covAU m mγ Λ T s :=
  measurable_intervalIntegral_unit (measurable_covAInt_uncurry m mγ Λ s)

theorem measurable_covAU' (m mγ Λ s : ℝ) : Measurable fun T => covAU' m mγ Λ T s :=
  measurable_intervalIntegral_unit (measurable_covADer_uncurry m mγ Λ s)

theorem measurable_covBU (m mγ Λ s : ℝ) : Measurable fun T => covBU m mγ Λ T s :=
  measurable_intervalIntegral_unit (g := fun r : ℝ × ℝ =>
    photonTail (vpPhotonT m mγ Λ r.1) (seArg m s r.2))
    ((measurable_photonTail_vp m mγ Λ).comp
      (measurable_fst.prodMk ((measurable_seArg m s).comp measurable_snd)))

theorem measurable_covBU' (m mγ Λ s : ℝ) : Measurable fun T => covBU' m mγ Λ T s :=
  measurable_intervalIntegral_unit (g := fun r : ℝ × ℝ =>
    -vpPhotonT m mγ Λ r.1 (seArg m s r.2) * r.2)
    (((measurable_vpPhotonT m mγ Λ).comp
      (measurable_fst.prodMk ((measurable_seArg m s).comp measurable_snd))).neg.mul
        measurable_snd)

theorem measurable_covT (P : Params) (f : Fin 3) : Measurable (covT P f) := by
  unfold covT specMu
  fun_prop

theorem measurable_covG (P : Params) {K : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ} (s : ℝ)
    (hK : Measurable fun T => K P.m P.mγ P.Λ T s) : Measurable (covG P K s) := by
  unfold covG covWt
  refine Finset.measurable_sum _ fun f _ => ?_
  exact (((measurable_const.mul (by fun_prop)).mul (by fun_prop)).mul
    (hK.comp (measurable_covT P f)))

/-! ### The facts at one `x` -/

section Facts

variable {P : Params} {δ : ℝ} (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hγΛ : P.mγ < P.Λ)
  (hγ2 : P.mγ < 2 * P.m) (hmass : ∀ f, P.m ≤ P.mass f) (hδ : 0 < δ)
  (hδA : 2 * δ ≤ P.mγ ^ 2) (hδm : δ ≤ P.m ^ 2)

include hm hmγ hγΛ hγ2 hmass hδ hδA hδm in
/-- The hypotheses of the `T`-level lemmas at `T = T_f(x)`. -/
theorem covT_facts {f : Fin 3} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hΛμ : P.Λ ^ 2 ≠ specMu (P.mass f) x ^ 2) :
    0 < covT P f x ∧ 2 * δ ≤ P.Λ ^ 2 ∧ 2 * δ ≤ covT P f x * P.m ^ 2 ∧
      P.mγ ^ 2 ≠ P.Λ ^ 2 ∧ P.mγ ^ 2 ≠ covT P f x * P.m ^ 2 ∧
      P.Λ ^ 2 ≠ covT P f x * P.m ^ 2 ∧
      x * (1 - x) * (covT P f x * P.m ^ 2) = P.mass f ^ 2 := by
  obtain ⟨hμ2, hμ4⟩ := specMu_sq_eq (M := P.mass f) hx
  have hm2 : P.m ^ 2 ≠ 0 := pow_ne_zero 2 hm.ne'
  have hTm : covT P f x * P.m ^ 2 = specMu (P.mass f) x ^ 2 := div_mul_cancel₀ _ hm2
  have hMf := hmass f
  have hm4 : 4 * P.m ^ 2 ≤ specMu (P.mass f) x ^ 2 := le_trans (by nlinarith) hμ4
  have hx1 := mem_Ioo_mul_pos hx
  refine ⟨div_pos (by nlinarith) (by positivity),
    le_trans hδA (pow_le_pow_left₀ hmγ.le hγΛ.le 2), by rw [hTm]; nlinarith,
    (pow_lt_pow_left₀ hγΛ hmγ.le two_ne_zero).ne, by rw [hTm]; nlinarith,
    by rw [hTm]; exact hΛμ, ?_⟩
  rw [hTm, hμ2]
  exact mul_div_cancel₀ _ hx1.ne'

include hm hmγ hγΛ hγ2 hmass hδ hδA hδm in
/-- **The bound of one flavour term of a derivative integrand.** -/
theorem abs_covWt_mul_le {f : Fin 3} {x s C : ℝ} {K : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hΛμ : P.Λ ^ 2 ≠ specMu (P.mass f) x ^ 2)
    (hK : |K P.m P.mγ P.Λ (covT P f x) s| ≤ C / (covT P f x * P.m ^ 2)) :
    |P.loopCoeff f * covWt x * (x * (1 - x))⁻¹ * K P.m P.mγ P.Λ (covT P f x) s| ≤
      |P.loopCoeff f| * (C / P.mass f ^ 2) := by
  obtain ⟨hT, -, -, -, -, -, hX⟩ := covT_facts hm hmγ hγΛ hγ2 hmass hδ hδA hδm hx hΛμ
  have hx1 := mem_Ioo_mul_pos hx
  have hU : 0 < covT P f x * P.m ^ 2 := by positivity
  have hw := abs_covWt_le hx
  rw [abs_mul, abs_mul, abs_mul, abs_inv, abs_of_pos hx1]
  have e : C / P.mass f ^ 2 = (x * (1 - x))⁻¹ * (C / (covT P f x * P.m ^ 2)) := by
    rw [← hX]
    field_simp
  rw [e]
  calc |P.loopCoeff f| * |covWt x| * (x * (1 - x))⁻¹ * |K P.m P.mγ P.Λ (covT P f x) s|
      ≤ |P.loopCoeff f| * 1 * (x * (1 - x))⁻¹ * (C / (covT P f x * P.m ^ 2)) := by
        gcongr
    _ = _ := by ring

end Facts

/-! ### Bounds at one `T` -/

/-- The bound `2 bubKQ + (m² + 4(m² + δ)) tMax` of `T m² |covAInt|`. -/
noncomputable def covIntMax (m A B δ : ℝ) : ℝ :=
  2 * bubKQ A B + (m ^ 2 + 4 * (m ^ 2 + δ)) * tMax A B

section TBound

variable {m mγ Λ T δ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) (hδ : 0 < δ)
  (hδA : 2 * δ ≤ mγ ^ 2) (hδB : 2 * δ ≤ Λ ^ 2) (hδU : 2 * δ ≤ T * m ^ 2)
  (hab : mγ ^ 2 ≠ Λ ^ 2) (hac : mγ ^ 2 ≠ T * m ^ 2) (hbc : Λ ^ 2 ≠ T * m ^ 2)

/-- An interval integral over `[0, 1]` of a function bounded on `(0, 1)`. -/
theorem abs_intervalIntegral_unit_le {g : ℝ → ℝ} {C : ℝ}
    (hb : ∀ y ∈ Ioo (0 : ℝ) 1, |g y| ≤ C) : |∫ y in (0 : ℝ)..1, g y| ≤ C := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := 0) (b := 1) (C := C)
    (f := g) (by
      filter_upwards [Measure.ae_ne volume (1 : ℝ)] with y hy1 hy
      rw [uIoc_of_le zero_le_one] at hy
      exact hb y ⟨hy.1, lt_of_le_of_ne hy.2 hy1⟩)
  simpa using h

include hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc in
theorem abs_covAU_le {s : ℝ} (hs1 : -m ^ 2 - δ < s) (hs2 : s < -m ^ 2 + δ) :
    |covAU m mγ Λ T s| ≤ covIntMax m (mγ ^ 2) (Λ ^ 2) δ / (T * m ^ 2) := by
  refine abs_intervalIntegral_unit_le fun y hy => ?_
  refine (abs_covAInt_le hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc hy hs1 hs2).trans_eq ?_
  unfold covIntMax
  ring

include hm hδ hδA hδB hδU hab hac hbc in
theorem abs_covAU'_le {s : ℝ} (hs1 : -m ^ 2 - δ < s) (hs2 : s < -m ^ 2 + δ) :
    |covAU' m mγ Λ T s| ≤ covDerMax m (mγ ^ 2) (Λ ^ 2) δ / (T * m ^ 2) :=
  abs_intervalIntegral_unit_le fun _ hy =>
    abs_covADer_le hm hδ hδA hδB hδU hab hac hbc hy hs1 hs2

include hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc in
theorem abs_covBU_le {s : ℝ} (hs1 : -m ^ 2 - δ < s) :
    |covBU m mγ Λ T s| ≤ bubKQ (mγ ^ 2) (Λ ^ 2) / (T * m ^ 2) :=
  abs_intervalIntegral_unit_le fun y hy => by
    obtain ⟨t0, t1⟩ := photonTail_vp_mem_Icc hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc
      (seArg_gt hδ hy hs1).le
    rw [abs_of_nonneg t0]
    exact t1

include hδ hδA hδB hδU in
theorem abs_covBU'_le {s : ℝ} (hs1 : -m ^ 2 - δ < s) :
    |covBU' m mγ Λ T s| ≤ rMax (mγ ^ 2) (Λ ^ 2) / (T * m ^ 2) :=
  abs_intervalIntegral_unit_le fun y hy => by
    have hw := (seArg_gt hδ hy hs1).le
    have h := abs_mul_bubQ_le_rMax hδ hδA hδB hδU hw (U := T * m ^ 2)
    rw [← vpPhotonT_eq_mul_bubQ] at h
    rw [abs_mul, abs_neg, abs_of_pos hy.1]
    exact (mul_le_of_le_one_right (abs_nonneg _) hy.2.le).trans h

end TBound

/-! ### The `x`-integrals -/

theorem ae_covT_ne {P : Params} (hΛ : 0 < P.Λ) :
    ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioo (0 : ℝ) 1 → ∀ f, P.Λ ^ 2 ≠ specMu (P.mass f) x ^ 2 := by
  have h := ae_all_iff.2 fun f : Fin 3 => ae_specMu_ne (M := P.mass f) hΛ
  filter_upwards [h] with x hx hxI f heq
  exact hx f hxI ((pow_left_inj₀ (Real.sqrt_nonneg _) hΛ.le two_ne_zero).1 heq.symm)

theorem intervalIntegrable_of_ae_bound {g : ℝ → ℝ} (hg : Measurable g) (C : ℝ)
    (hb : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioo (0 : ℝ) 1 → ‖g x‖ ≤ C) :
    IntervalIntegrable g volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  exact Measure.integrableOn_of_bounded (M := C) (by simp) hg.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioo).2 hb)

section XLevel

variable {P : Params} {δ : ℝ} (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hγΛ : P.mγ < P.Λ)
  (hγ2 : P.mγ < 2 * P.m) (hmass : ∀ f, P.m ≤ P.mass f) (hδ : 0 < δ)
  (hδA : 2 * δ ≤ P.mγ ^ 2) (hδm : δ ≤ P.m ^ 2)

/-- The flavour-summed bound `∑_f |c_f| C/M_f²`. -/
noncomputable def covSumBound (P : Params) (C : ℝ) : ℝ := ∑ f, |P.loopCoeff f| * (C / P.mass f ^ 2)

include hm hmγ hγΛ hγ2 hmass hδ hδA hδm in
/-- **The flavour-summed integrand is bounded off the coincident points.** -/
theorem abs_covG_le {K : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ} {C s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hΛμ : ∀ f, P.Λ ^ 2 ≠ specMu (P.mass f) x ^ 2)
    (hK : ∀ f, |K P.m P.mγ P.Λ (covT P f x) s| ≤ C / (covT P f x * P.m ^ 2)) :
    |covG P K s x| ≤ covSumBound P C := by
  unfold covG covSumBound
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun f _ => ?_)
  exact abs_covWt_mul_le hm hmγ hγΛ hγ2 hmass hδ hδA hδm hx (hΛμ f) (hK f)

include hm hmγ hγΛ hγ2 hmass hδ hδA hδm in
/-- **Differentiation of `covAX` under `∫₀¹ dx`** near the shell. -/
theorem hasDerivAt_covAX {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (-P.m ^ 2 - δ) (-P.m ^ 2 + δ)) :
    IntervalIntegrable (covG P covAU s₀) volume 0 1 ∧
      IntervalIntegrable (covG P covAU' s₀) volume 0 1 ∧
      HasDerivAt (covAX P) (covAX' P s₀) s₀ := by
  have hΛ : 0 < P.Λ := hmγ.trans hγΛ
  have hae := ae_covT_ne (P := P) hΛ
  have fct := fun f x (hx : x ∈ Ioo (0 : ℝ) 1) (h : P.Λ ^ 2 ≠ specMu (P.mass f) x ^ 2) =>
    covT_facts hm hmγ hγΛ hγ2 hmass hδ hδA hδm hx h
  have hF0 : IntervalIntegrable (covG P covAU s₀) volume 0 1 := by
    refine intervalIntegrable_of_ae_bound (measurable_covG P s₀ (measurable_covAU _ _ _ s₀))
      (covSumBound P (covIntMax P.m (P.mγ ^ 2) (P.Λ ^ 2) δ)) ?_
    filter_upwards [hae] with x hx hxI
    rw [Real.norm_eq_abs]
    refine abs_covG_le hm hmγ hγΛ hγ2 hmass hδ hδA hδm hxI (hx hxI) fun f => ?_
    obtain ⟨hT, hδB, hδU, hab, hac, hbc, -⟩ := fct f x hxI (hx hxI f)
    exact abs_covAU_le hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc hs₀.1 hs₀.2
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (bound := fun _ => covSumBound P (covDerMax P.m (P.mγ ^ 2) (P.Λ ^ 2) δ))
    (F := fun s x => covG P covAU s x) (F' := fun s x => covG P covAU' s x)
    (x₀ := s₀) (s := Ioo (-P.m ^ 2 - δ) (-P.m ^ 2 + δ)) (isOpen_Ioo.mem_nhds hs₀)
    (Eventually.of_forall fun s =>
      (measurable_covG P s (measurable_covAU _ _ _ s)).aestronglyMeasurable) hF0
    (measurable_covG P s₀ (measurable_covAU' _ _ _ s₀)).aestronglyMeasurable
    (by
      filter_upwards [hae, Measure.ae_ne volume (1 : ℝ)] with x hx hx1 hxI s hs
      rw [uIoc_of_le zero_le_one] at hxI
      have hxI' : x ∈ Ioo (0 : ℝ) 1 := ⟨hxI.1, lt_of_le_of_ne hxI.2 hx1⟩
      rw [Real.norm_eq_abs]
      refine abs_covG_le hm hmγ hγΛ hγ2 hmass hδ hδA hδm hxI' (hx hxI') fun f => ?_
      obtain ⟨hT, hδB, hδU, hab, hac, hbc, -⟩ := fct f x hxI' (hx hxI' f)
      exact abs_covAU'_le hm hδ hδA hδB hδU hab hac hbc hs.1 hs.2)
    intervalIntegrable_const
    (by
      filter_upwards [hae, Measure.ae_ne volume (1 : ℝ)] with x hx hx1 hxI s hs
      rw [uIoc_of_le zero_le_one] at hxI
      have hxI' : x ∈ Ioo (0 : ℝ) 1 := ⟨hxI.1, lt_of_le_of_ne hxI.2 hx1⟩
      have hd : ∀ f ∈ (Finset.univ : Finset (Fin 3)), HasDerivAt
          (fun s => P.loopCoeff f * covWt x * (x * (1 - x))⁻¹ * covAU P.m P.mγ P.Λ (covT P f x) s)
          (P.loopCoeff f * covWt x * (x * (1 - x))⁻¹ * covAU' P.m P.mγ P.Λ (covT P f x) s) s :=
        fun f _ => by
          obtain ⟨hT, hδB, hδU, hab, hac, hbc, -⟩ := fct f x hxI' (hx hxI' f)
          exact (hasDerivAt_covAU hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc hs).2.const_mul _
      unfold covG
      exact HasDerivAt.sum hd)
  exact ⟨hF0, key.1, key.2⟩

include hm hmγ hγΛ hγ2 hmass hδ hδA hδm in
/-- **Differentiation of `covBX` under `∫₀¹ dx`** near the shell. -/
theorem hasDerivAt_covBX {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (-P.m ^ 2 - δ) (-P.m ^ 2 + δ)) :
    IntervalIntegrable (covG P covBU s₀) volume 0 1 ∧
      IntervalIntegrable (covG P covBU' s₀) volume 0 1 ∧
      HasDerivAt (covBX P) (covBX' P s₀) s₀ := by
  have hΛ : 0 < P.Λ := hmγ.trans hγΛ
  have hae := ae_covT_ne (P := P) hΛ
  have fct := fun f x (hx : x ∈ Ioo (0 : ℝ) 1) (h : P.Λ ^ 2 ≠ specMu (P.mass f) x ^ 2) =>
    covT_facts hm hmγ hγΛ hγ2 hmass hδ hδA hδm hx h
  have hF0 : IntervalIntegrable (covG P covBU s₀) volume 0 1 := by
    refine intervalIntegrable_of_ae_bound (measurable_covG P s₀ (measurable_covBU _ _ _ s₀))
      (covSumBound P (bubKQ (P.mγ ^ 2) (P.Λ ^ 2))) ?_
    filter_upwards [hae] with x hx hxI
    rw [Real.norm_eq_abs]
    refine abs_covG_le hm hmγ hγΛ hγ2 hmass hδ hδA hδm hxI (hx hxI) fun f => ?_
    obtain ⟨hT, hδB, hδU, hab, hac, hbc, -⟩ := fct f x hxI (hx hxI f)
    exact abs_covBU_le hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc hs₀.1
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (bound := fun _ => covSumBound P (rMax (P.mγ ^ 2) (P.Λ ^ 2)))
    (F := fun s x => covG P covBU s x) (F' := fun s x => covG P covBU' s x)
    (x₀ := s₀) (s := Ioo (-P.m ^ 2 - δ) (-P.m ^ 2 + δ)) (isOpen_Ioo.mem_nhds hs₀)
    (Eventually.of_forall fun s =>
      (measurable_covG P s (measurable_covBU _ _ _ s)).aestronglyMeasurable) hF0
    (measurable_covG P s₀ (measurable_covBU' _ _ _ s₀)).aestronglyMeasurable
    (by
      filter_upwards [hae, Measure.ae_ne volume (1 : ℝ)] with x hx hx1 hxI s hs
      rw [uIoc_of_le zero_le_one] at hxI
      have hxI' : x ∈ Ioo (0 : ℝ) 1 := ⟨hxI.1, lt_of_le_of_ne hxI.2 hx1⟩
      rw [Real.norm_eq_abs]
      refine abs_covG_le hm hmγ hγΛ hγ2 hmass hδ hδA hδm hxI' (hx hxI') fun f => ?_
      obtain ⟨hT, hδB, hδU, hab, hac, hbc, -⟩ := fct f x hxI' (hx hxI' f)
      exact abs_covBU'_le hδ hδA hδB hδU hs.1)
    intervalIntegrable_const
    (by
      filter_upwards [hae, Measure.ae_ne volume (1 : ℝ)] with x hx hx1 hxI s hs
      rw [uIoc_of_le zero_le_one] at hxI
      have hxI' : x ∈ Ioo (0 : ℝ) 1 := ⟨hxI.1, lt_of_le_of_ne hxI.2 hx1⟩
      have hd : ∀ f ∈ (Finset.univ : Finset (Fin 3)), HasDerivAt
          (fun s => P.loopCoeff f * covWt x * (x * (1 - x))⁻¹ * covBU P.m P.mγ P.Λ (covT P f x) s)
          (P.loopCoeff f * covWt x * (x * (1 - x))⁻¹ * covBU' P.m P.mγ P.Λ (covT P f x) s) s :=
        fun f _ => by
          obtain ⟨hT, hδB, hδU, hab, hac, hbc, -⟩ := fct f x hxI' (hx hxI' f)
          exact (hasDerivAt_covBU hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc hs).2.const_mul _
      unfold covG
      exact HasDerivAt.sum hd)
  exact ⟨hF0, key.1, key.2⟩

end XLevel

end QED.ChainProof.SetCRegDisp

end
