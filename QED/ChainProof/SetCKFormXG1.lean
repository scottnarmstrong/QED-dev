/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormXG1H2
public import QED.Polylog.Basic
import QED.Polylog.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Set (c), Stage K, closed forms: the branch-1 `u`-integral of `I(X)`

Helper level (no frozen statement). Step 4 of route D for `ρ_X` (scratch `stageK/STATUS.md`,
session 26+). With the rational coefficients of `SetCKFormXG1D`, `M = coordM X u`,
`P = X² + (1 - X)u`, `κ = formXkap`, the function

`G₁ = formXG1h + F_a log(1 - u) + F̃_b (X - u) log(X - u) + F_c log(X + u - Xu) + F_d log P
  + (formXG1m - κ log K) log M + κ (Li₂(M/K) - Li₂(M) + Li₂((1 - X)²/M) - Li₂((1 - X)/M))`

(`formXG1`; all four dilogarithm arguments lie in `(0, 1]` for `u ∈ [0, X]`) is continuous on
`[0, X]` (**`continuousOn_formXG1`**), has derivative `formXJ1L` on `(0, X)`
(**`hasDerivAt_formXG1`**), and so

**`integral_formXJ1_eq`**: if `formXJ1 X` is integrable on `(0, X)`, then
`∫_{(0,X)} formXJ1 X = G₁(X) - G₁(0)`.
-/

@[expose] public section

open Real Set MeasureTheory QED.Polylog

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- **The branch-1 antiderivative** `G₁`. -/
noncomputable def formXG1 (X u : ℝ) : ℝ :=
  formXG1h X u + formXG1a X u * log (1 - u) + formXG1b X u * ((X - u) * log (X - u)) +
    formXG1c X u * log (X + u - X * u) + formXG1d X u * log (X ^ 2 + (1 - X) * u) +
    (formXG1m X - formXkap X * log (formXK X)) * log (coordM X u) +
    formXkap X * (Li₂ (coordM X u / formXK X) - Li₂ (coordM X u) +
      Li₂ ((1 - X) ^ 2 / coordM X u) - Li₂ ((1 - X) / coordM X u))

/-- The chain rule for `Li₂ ∘ f` with `f ∈ (0, 1)`. -/
theorem formX_hasDerivAt_li2_comp {f : ℝ → ℝ} {f' u : ℝ} (hf : HasDerivAt f f' u)
    (h0 : 0 < f u) (h1 : f u < 1) :
    HasDerivAt (fun z => Li₂ (f z)) (-log (1 - f u) / f u * f') u :=
  (hasDerivAt_Li₂ (by rw [abs_lt]; constructor <;> linarith) h0.ne').comp u hf

section

variable {X u : ℝ}

theorem formXG1_li2_derivs (hX : X ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo 0 X) :
    HasDerivAt (fun z => Li₂ (coordM X z / formXK X))
        (-(log (1 - X) + log (1 - u) - log (formXK X)) * (1 - X) / coordM X u) u ∧
      HasDerivAt (fun z => Li₂ (coordM X z))
        (-(log (1 - X) + log (X - u)) * (1 - X) / coordM X u) u ∧
      HasDerivAt (fun z => Li₂ ((1 - X) ^ 2 / coordM X z))
        ((log (X + u - X * u) - log (coordM X u)) * (1 - X) / coordM X u) u ∧
      HasDerivAt (fun z => Li₂ ((1 - X) / coordM X z))
        ((log (X ^ 2 + (1 - X) * u) - log (coordM X u)) * (1 - X) / coordM X u) u := by
  obtain ⟨hX0, hX1⟩ := hX
  obtain ⟨hu0, hu1⟩ := hu
  have hM := coordM_pos ⟨hX0, hX1⟩ hu0.le
  have hK := formXK_pos X
  have h1X : 0 < 1 - X := by linarith
  have h1u : 0 < 1 - u := by linarith
  have hXu : 0 < X - u := by linarith
  have hB : 0 < X + u - X * u := by nlinarith
  have hP : 0 < X ^ 2 + (1 - X) * u := by nlinarith
  have eKM : formXK X - coordM X u = (1 - X) * (1 - u) := by unfold formXK coordM; ring
  have e1M : 1 - coordM X u = (1 - X) * (X - u) := by unfold coordM; ring
  have eMB : coordM X u - (1 - X) ^ 2 = X + u - X * u := by unfold coordM; ring
  have eMP : coordM X u - (1 - X) = X ^ 2 + (1 - X) * u := by unfold coordM; ring
  have hc := hasDerivAt_coordM X u
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := formX_hasDerivAt_li2_comp (hc.div_const (formXK X)) (by positivity)
      (by rw [div_lt_one hK]; nlinarith)
    refine h.congr_deriv ?_
    have : 1 - coordM X u / formXK X = (1 - X) * (1 - u) / formXK X := by
      rw [← eKM]; field_simp
    rw [this, log_div (by positivity) hK.ne', log_mul h1X.ne' h1u.ne']
    field_simp
  · have h := formX_hasDerivAt_li2_comp hc hM (by nlinarith)
    refine h.congr_deriv ?_
    rw [e1M, log_mul h1X.ne' hXu.ne']
    field_simp
  · have hq : HasDerivAt (fun z => (1 - X) ^ 2 / coordM X z)
        (-((1 - X) ^ 2 * (1 - X)) / coordM X u ^ 2) u := by
      have := (hc.inv hM.ne').const_mul ((1 - X) ^ 2)
      refine (this.congr_deriv ?_).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun z => ?_)
      · ring
      · simp [div_eq_mul_inv]
    have h := formX_hasDerivAt_li2_comp hq (by positivity) (by rw [div_lt_one hM]; nlinarith)
    refine h.congr_deriv ?_
    have : 1 - (1 - X) ^ 2 / coordM X u = (X + u - X * u) / coordM X u := by
      rw [← eMB]; field_simp
    rw [this, log_div hB.ne' hM.ne']
    field_simp
  · have hq : HasDerivAt (fun z => (1 - X) / coordM X z)
        (-((1 - X) * (1 - X)) / coordM X u ^ 2) u := by
      have := (hc.inv hM.ne').const_mul (1 - X)
      refine (this.congr_deriv ?_).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun z => ?_)
      · ring
      · simp [div_eq_mul_inv]
    have h := formX_hasDerivAt_li2_comp hq (by positivity) (by rw [div_lt_one hM]; nlinarith)
    refine h.congr_deriv ?_
    have : 1 - (1 - X) / coordM X u = (X ^ 2 + (1 - X) * u) / coordM X u := by
      rw [← eMP]; field_simp
    rw [this, log_div hP.ne' hM.ne']
    field_simp

/-- **`G₁′ = J₁`** on `(0, X)`. -/
theorem hasDerivAt_formXG1 (hX : X ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo 0 X) :
    HasDerivAt (formXG1 X) (formXJ1L X u) u := by
  have hM := coordM_pos hX hu.1.le
  obtain ⟨d1, d2, d3, d4⟩ := formXG1_li2_derivs hX hu
  have p0 := hasDerivAt_formXG1h hX hu
  have pa := hasDerivAt_formXG1a_piece hX hu
  have pb := hasDerivAt_formXG1b_piece hX hu
  have pc := hasDerivAt_formXG1c_piece hX hu
  have pd := hasDerivAt_formXG1d_piece hX hu
  have pm := ((hasDerivAt_coordM X u).log hM.ne').const_mul
    (formXG1m X - formXkap X * log (formXK X))
  have pl := (((d1.sub d2).add d3).sub d4).const_mul (formXkap X)
  refine ((((((p0.add pa).add pb).add pc).add pd).add pm).add pl).congr_deriv ?_
  unfold formXJ1L
  field_simp
  ring

/-- `G₁` is continuous on `[0, X]`. -/
theorem continuousOn_formXG1 (hX : X ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (formXG1 X) (Icc 0 X) := by
  obtain ⟨hX0, hX1⟩ := hX
  have hK := formXK_pos X
  have hM : ∀ u ∈ Icc 0 X, 0 < coordM X u := fun u hu => coordM_pos ⟨hX0, hX1⟩ hu.1
  have hM1 : ∀ u ∈ Icc 0 X, coordM X u ≤ 1 := fun u hu => by
    unfold coordM; nlinarith [hu.2]
  have h1u : ∀ u ∈ Icc 0 X, 1 - u ≠ 0 := fun u hu => by linarith [hu.2]
  have hB : ∀ u ∈ Icc 0 X, X + u - X * u ≠ 0 := fun u hu => by nlinarith [hu.1]
  have hP : ∀ u ∈ Icc 0 X, X ^ 2 + (1 - X) * u ≠ 0 := fun u hu => by nlinarith [hu.1]
  have cM : ContinuousOn (coordM X) (Icc 0 X) := by unfold coordM; fun_prop
  have hpol : ∀ {n : ℕ} (c : Fin n → ℝ) (D : ℝ), D ≠ 0 →
      ContinuousOn (fun u => formXPol c u / (D * coordM X u ^ 2)) (Icc 0 X) := by
    intro n c D hD
    refine (continuous_formXPol c).continuousOn.div (continuousOn_const.mul (cM.pow 2))
      fun u hu => mul_ne_zero hD (pow_ne_zero _ (hM u hu).ne')
  have hX1' : X - 1 ≠ 0 := by linarith
  have ca := hpol (formXG1aN X) (formXG1aD X) (by unfold formXG1aD; simp [*, hK.ne'])
  have cb := hpol (formXG1bN X) (formXG1bD X) (by unfold formXG1bD; simp [*])
  have cc := hpol (formXG1cN X) (formXG1cD X) (by unfold formXG1cD; simp [*])
  have cd := hpol (formXG1dN X) (formXG1dD X) (by unfold formXG1dD; simp [*])
  have ch := hpol (formXG1hRN X) (formXG1hRD X) (by unfold formXG1hRD; simp [*, hK.ne'])
  have ch' : ContinuousOn (formXG1h X) (Icc 0 X) := by
    have q1 : ContinuousOn (fun u : ℝ => formXG1e1 X / (1 - u)) (Icc 0 X) :=
      continuousOn_const.div (by fun_prop) h1u
    have q2 : ContinuousOn (fun u : ℝ => formXG1e2 X / (X ^ 2 + (1 - X) * u)) (Icc 0 X) :=
      continuousOn_const.div (by fun_prop) hP
    exact ((ch.add q1).add q2).congr fun u _ => rfl
  have cl1 : ContinuousOn (fun u => log (1 - u)) (Icc 0 X) :=
    continuousOn_log.comp (by fun_prop) fun u hu => h1u u hu
  have cl2 : Continuous fun u : ℝ => (X - u) * log (X - u) :=
    continuous_mul_log.comp (continuous_const.sub continuous_id)
  have cl3 : ContinuousOn (fun u => log (X + u - X * u)) (Icc 0 X) :=
    continuousOn_log.comp (by fun_prop) fun u hu => hB u hu
  have cl4 : ContinuousOn (fun u => log (X ^ 2 + (1 - X) * u)) (Icc 0 X) :=
    continuousOn_log.comp (by fun_prop) fun u hu => hP u hu
  have cl5 : ContinuousOn (fun u => log (coordM X u)) (Icc 0 X) :=
    continuousOn_log.comp cM fun u hu => (hM u hu).ne'
  have cLi : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc 0 X) → (∀ u ∈ Icc 0 X, 0 ≤ f u ∧ f u ≤ 1) →
      ContinuousOn (fun u => Li₂ (f u)) (Icc 0 X) := fun hf hm =>
    continuousOn_Li₂.comp hf fun u hu => ⟨by linarith [(hm u hu).1], (hm u hu).2⟩
  have c1 := cLi (f := fun u => coordM X u / formXK X) (cM.div_const _) fun u hu =>
    ⟨(div_pos (hM u hu) hK).le, by rw [div_le_one hK]; unfold formXK; nlinarith [hM1 u hu]⟩
  have c2 := cLi (f := coordM X) cM fun u hu => ⟨(hM u hu).le, hM1 u hu⟩
  have c3 := cLi (f := fun u => (1 - X) ^ 2 / coordM X u)
    (continuousOn_const.div cM fun u hu => (hM u hu).ne') fun u hu =>
    ⟨by have := hM u hu; positivity, by
      rw [div_le_one (hM u hu)]; unfold coordM; nlinarith [hu.1]⟩
  have c4 := cLi (f := fun u => (1 - X) / coordM X u)
    (continuousOn_const.div cM fun u hu => (hM u hu).ne') fun u hu =>
    ⟨by have := hM u hu; have : 0 < 1 - X := by linarith
        positivity, by
      rw [div_le_one (hM u hu)]; unfold coordM; nlinarith [hu.1]⟩
  have cl2' := cl2.continuousOn (s := Icc 0 X)
  have e : formXG1 X = fun u => formXG1h X u +
      formXPol (formXG1aN X) u / (formXG1aD X * coordM X u ^ 2) * log (1 - u) +
      formXPol (formXG1bN X) u / (formXG1bD X * coordM X u ^ 2) * ((X - u) * log (X - u)) +
      formXPol (formXG1cN X) u / (formXG1cD X * coordM X u ^ 2) * log (X + u - X * u) +
      formXPol (formXG1dN X) u / (formXG1dD X * coordM X u ^ 2) *
        log (X ^ 2 + (1 - X) * u) +
      (formXG1m X - formXkap X * log (formXK X)) * log (coordM X u) +
      formXkap X * (Li₂ (coordM X u / formXK X) - Li₂ (coordM X u) +
        Li₂ ((1 - X) ^ 2 / coordM X u) - Li₂ ((1 - X) / coordM X u)) := rfl
  rw [e]
  exact (((((ch'.add (ca.mul cl1)).add (cb.mul cl2')).add (cc.mul cl3)).add (cd.mul cl4)).add
    (continuousOn_const.mul cl5)).add (continuousOn_const.mul (((c1.sub c2).add c3).sub c4))

end

/-- **The branch-1 integral** by the fundamental theorem of calculus. -/
theorem integral_formXJ1_eq {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1)
    (hint : IntegrableOn (formXJ1 X) (Ioo 0 X)) :
    ∫ u in Ioo 0 X, formXJ1 X u = formXG1 X X - formXG1 X 0 := by
  have hab : 0 ≤ X := hX.1.le
  have e : EqOn (formXJ1 X) (formXJ1L X) (Ioo 0 X) := fun u hu => formXJ1_eq_L hX hu
  have hint' : IntegrableOn (formXJ1L X) (Ioo 0 X) := hint.congr_fun e measurableSet_Ioo
  rw [setIntegral_congr_fun measurableSet_Ioo e, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hab]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (continuousOn_formXG1 hX)
    (fun u hu => hasDerivAt_formXG1 hX hu) ?_
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
  exact hint'

end QED.ChainProof.SetCK

end
