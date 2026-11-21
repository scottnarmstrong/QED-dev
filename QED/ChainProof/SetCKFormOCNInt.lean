/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCNAnti

/-!
# Set (c), Stage K, closed forms: `N(a, X)` as an antiderivative difference

Helper level (no frozen statement). Item 3 of the `ρ_oC` route (Stage K notes, Session 30+).
**`formOCN`** `a X = ∫_{x ∈ (0, X)} (g_k + S_A)(a, x, v(x, X))`, `v = Q(X) - Q(x)`. On the
fibre `Y_c = a (X - x)(X + (1 - X) x)/((1 - X)(1 - a x)(x + a Q(X)))`
(**`formOCN_logYc`**), so the integrand is `formOCNIg a Q(X) X x` (**`formOCN_integrand_eq`**,
via `formOC_gk_add_SA`), and by the FTC with the antiderivative `formOCNF`, continuous on
`[0, X]` (the `X - x` letter enters as `(X - x) log(X - x)`):

**`formOC_N_eq`**: for `a ∈ (0, 1)`, `a ≠ 1/2`, `X ∈ (0, 1)`, the integrand is integrable on
`(0, X)` and `formOCN a X = formOCNF a Q(X) X X - formOCNF a Q(X) X 0`.
-/

@[expose] public section

open Real Set MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- **`N(a, X)`**, the `x`-integral of `g_k + S_A` on the fibre over `X`. -/
noncomputable def formOCN (a X : ℝ) : ℝ :=
  ∫ x in Ioo 0 X, (formOCgk x a (scOutVX x X) + formOCSA a x (scOutVX x X))

section

variable {a q X x : ℝ}

theorem formOCN_logYc (ha : a ∈ Ioo (0 : ℝ) 1) (hX : X < 1) (hx : x ∈ Ioo 0 X) :
    log (formOCYc a x (scOutVX x X)) = log a + log (X - x) + log (X + (1 - X) * x) -
      log (1 - X) - log (1 + -a * x) - log (a * setCKQ X + 1 * x) := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hx0, hxX⟩ := hx
  have h1X : 0 < 1 - X := by linarith
  have h1x : 0 < 1 - x := by linarith
  have hXx : 0 < X - x := by linarith
  have hl2 : 0 < X + (1 - X) * x := by nlinarith
  have hlL : 0 < 1 + -a * x := by nlinarith
  have hQ : 0 < setCKQ X := div_pos (pow_pos (by linarith) 2) h1X
  have hlE : 0 < a * setCKQ X + 1 * x := by nlinarith [mul_pos ha0 hQ]
  have eY : formOCYc a x (scOutVX x X) = a * (X - x) * (X + (1 - X) * x) /
      ((1 - X) * (1 + -a * x) * (a * setCKQ X + 1 * x)) := by
    have e : setCKQ x + scOutVX x X = setCKQ X := by unfold scOutVX; ring
    rw [formOCYc, e]
    unfold scOutVX setCKQ
    field_simp
    ring
  rw [eY, log_div (by positivity) (by positivity), log_mul (by positivity) hl2.ne',
    log_mul ha0.ne' hXx.ne', log_mul (by positivity) hlE.ne', log_mul h1X.ne' hlL.ne']
  ring

theorem formOCN_integrand_eq (ha : a ∈ Ioo (0 : ℝ) 1) (hX : X < 1) (hx : x ∈ Ioo 0 X) :
    formOCgk x a (scOutVX x X) + formOCSA a x (scOutVX x X) = formOCNIg a (setCKQ X) X x := by
  have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
  have hv : 0 < scOutVX x X := sub_pos.2 (setCKQ_lt hx.1.le hx.2 hX)
  have e : setCKQ x + scOutVX x X = setCKQ X := by unfold scOutVX; ring
  rw [formOC_gk_add_SA ha hx' hv, e, formOCN_logYc ha hX hx, formOCNIg]

theorem continuousOn_formOCNF (ha : a ∈ Ioo (0 : ℝ) 1) (hq : 0 < q) (hX : X ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (formOCNF a q X) (Icc 0 X) := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hX0, hX1⟩ := hX
  have hXl : Continuous fun z : ℝ => (X - z) * log (X - z) :=
    (continuous_const.sub continuous_id).mul_log
  have hlog : ∀ α β : ℝ, (∀ z ∈ Icc (0 : ℝ) X, 0 < α + β * z) →
      ContinuousOn (fun z => log (α + β * z)) (Icc 0 X) := fun α β h =>
    ContinuousOn.log (by fun_prop) fun z hz => (h z hz).ne'
  have h2 := hlog X (1 - X) fun z hz => by nlinarith [hz.1, hz.2]
  have hL := hlog 1 (-a) fun z hz => by nlinarith [hz.1, hz.2]
  have hE := hlog (a * q) 1 fun z hz => by nlinarith [hz.1, hz.2, mul_pos ha0 hq]
  have hM := hlog 1 (a - 1) fun z hz => by nlinarith [hz.1, hz.2]
  have hP := fun c : Fin 6 → ℝ => (continuous_formXPol c).continuousOn (s := Icc (0 : ℝ) X)
  have hPol := (continuous_formXPol (formOCNint (formOCNcd a q X))).continuousOn
    (s := Icc (0 : ℝ) X)
  have hQ := (continuous_formXPol (formOCNquo (formOCNcP a q) X)).continuousOn
    (s := Icc (0 : ℝ) X)
  have hr4 : ContinuousOn (fun z => formOCNr4 a q / (z + a * q)) (Icc 0 X) :=
    continuousOn_const.div (by fun_prop) fun z hz => by nlinarith [hz.1, mul_pos ha0 hq]
  unfold formOCNF
  exact ((((((hPol.add ((hP _).mul continuousOn_const)).sub (hQ.mul hXl.continuousOn)).add
    (((hP _).sub continuousOn_const).mul h2)).add
    (((continuousOn_const.sub (hP _)).sub continuousOn_const).mul hL)).add
    (((continuousOn_const.sub (hP _)).add continuousOn_const).mul hE)).add
    (continuousOn_const.mul hM)).sub hr4

/-- The continuous part of the `N`-integrand (all letters except `X - x`). -/
noncomputable def formOCNIc (a q X x : ℝ) : ℝ :=
  formXPol (formOCNcT a q) x + formOCNr1 a q / (1 - a * x) + formOCNr2 a q / (1 - x + a * x) +
    formOCNr3 a q / (x + a * q) + formOCNr4 a q / (x + a * q) ^ 2 +
    formXPol (formOCNcR a q) x * (log a + log (X + (1 - X) * x) - log (1 - X) -
      log (1 + -a * x) - log (a * q + 1 * x))

theorem formOCNIg_eq (ha : a ∈ Ioo (0 : ℝ) 1) (h2a : 2 * a - 1 ≠ 0) (hq : 0 < q)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    formOCNIg a q X x = formOCNIc a q X x + formXPol (formOCNcR a q) x * log (X - x) := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hx0, hx1⟩ := hx
  have hD : 1 + a * (1 - a) * q ≠ 0 := by nlinarith [mul_pos ha0 hq]
  have hT := formOCN_T_eq (x := x) hD (by nlinarith [mul_pos ha0 hq]) (by nlinarith)
    (by nlinarith) ha0.ne' (by linarith) h2a
  unfold formOCNIg formOCNIc
  rw [hT, formOCN_R_eq hD]
  ring

theorem formOCN_intervalIntegrable (ha : a ∈ Ioo (0 : ℝ) 1) (h2a : 2 * a - 1 ≠ 0) (hq : 0 < q)
    (hX : X ∈ Ioo (0 : ℝ) 1) : IntervalIntegrable (formOCNIg a q X) volume 0 X := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hX0, hX1⟩ := hX
  have hpos : ∀ z ∈ uIcc (0 : ℝ) X, 0 < 1 - a * z ∧ 0 < 1 - z + a * z ∧ 0 < z + a * q ∧
      0 < X + (1 - X) * z ∧ 0 < 1 + -a * z ∧ 0 < a * q + 1 * z := fun z hz => by
    rw [uIcc_of_le hX0.le] at hz
    obtain ⟨hz0, hz1⟩ := hz
    have := mul_pos ha0 hq
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith
  have hc : ContinuousOn (formOCNIc a q X) (uIcc 0 X) := by
    have hlog : ∀ f : ℝ → ℝ, Continuous f → (∀ z ∈ uIcc (0 : ℝ) X, 0 < f z) →
        ContinuousOn (fun z => log (f z)) (uIcc 0 X) := fun f hf h =>
      hf.continuousOn.log fun z hz => (h z hz).ne'
    have hdiv : ∀ (c : ℝ) (f : ℝ → ℝ), Continuous f → (∀ z ∈ uIcc (0 : ℝ) X, 0 < f z) →
        ContinuousOn (fun z => c / f z) (uIcc 0 X) := fun c f hf h =>
      continuousOn_const.div hf.continuousOn fun z hz => (h z hz).ne'
    unfold formOCNIc
    refine (((((continuous_formXPol _).continuousOn.add
      (hdiv _ _ (by fun_prop) fun z hz => (hpos z hz).1)).add
      (hdiv _ _ (by fun_prop) fun z hz => (hpos z hz).2.1)).add
      (hdiv _ _ (by fun_prop) fun z hz => (hpos z hz).2.2.1)).add
      (hdiv _ (fun z => (z + a * q) ^ 2) (by fun_prop)
        fun z hz => pow_pos (hpos z hz).2.2.1 2)).add
      ((continuous_formXPol _).continuousOn.mul ((((continuousOn_const.add
        (hlog _ (by fun_prop) fun z hz => (hpos z hz).2.2.2.1)).sub continuousOn_const).sub
        (hlog _ (by fun_prop) fun z hz => (hpos z hz).2.2.2.2.1)).sub
        (hlog _ (by fun_prop) fun z hz => (hpos z hz).2.2.2.2.2)))
  have hl : IntervalIntegrable (fun z => log (X - z)) volume 0 X := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := X)).comp_sub_left X
    simp only [sub_zero, sub_self] at h
    exact h.symm
  have hR := hl.continuousOn_mul (continuous_formXPol (formOCNcR a q)).continuousOn
  refine ((hc.intervalIntegrable).add hR).congr_uIoo fun z hz => ?_
  rw [uIoo_of_le hX0.le] at hz
  exact (formOCNIg_eq ⟨ha0, ha1⟩ h2a hq ⟨hz.1.le, by linarith [hz.2]⟩).symm

/-- **`N(a, X)` as an antiderivative difference.** -/
theorem formOC_N_eq (ha : a ∈ Ioo (0 : ℝ) 1) (h2a : 2 * a - 1 ≠ 0) (hX : X ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun x => formOCgk x a (scOutVX x X) + formOCSA a x (scOutVX x X)) (Ioo 0 X) ∧
      formOCN a X = formOCNF a (setCKQ X) X X - formOCNF a (setCKQ X) X 0 := by
  have hq : 0 < setCKQ X := div_pos (pow_pos hX.1 2) (by linarith [hX.2])
  have hI := formOCN_intervalIntegrable ha h2a hq hX
  have e : EqOn (fun x => formOCgk x a (scOutVX x X) + formOCSA a x (scOutVX x X))
      (formOCNIg a (setCKQ X) X) (Ioo 0 X) := fun x hx => formOCN_integrand_eq ha hX.2 hx
  have hIo : IntegrableOn (formOCNIg a (setCKQ X) X) (Ioo 0 X) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hX.1.le).1 hI).mono_set Ioo_subset_Ioc_self
  refine ⟨hIo.congr_fun e.symm measurableSet_Ioo, ?_⟩
  rw [formOCN, setIntegral_congr_fun measurableSet_Ioo e, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hX.1.le]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hX.1.le
    (continuousOn_formOCNF ha hq hX) (fun x hx => hasDerivAt_formOCNF ha h2a hq hX.2 hx) hI

end

end QED.ChainProof.SetCK

end
