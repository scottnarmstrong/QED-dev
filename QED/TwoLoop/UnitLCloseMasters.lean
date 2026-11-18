/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLGraphReduceChengWu
public import QED.TwoLoop.UnitLLinkLimit
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The ladder unit L: the integration over the outer electron parameter

Section 3.3 of `docs/TWO-LOOP-UNITS.md`, stage (2) of the L link, step 1 (the `a`-integration).
In the variables of eq. (3.1) put `z_a = a(1-x)/x` (section 2.2): then `U = a/x`, the Jacobian is
`a/x²`, and the denominator is linear in `a`, `D = M + a h` with `M = Y² + (1-Y) μ_b` (inner photon
mass `μ_b`) and `h = (x² + (1-x) μ_a)/x` (outer photon mass `μ_a`). The integrand of eq. (3.1)
times the Jacobian (`ladderAX`) is

`P [1/(M + a h) + 8c/(a(M + a h)) - 9c²/(a²(M + a h)) + q/(M + a h)² - q c/(a (M + a h)²)]`,

`P = Y x (1-x)/2`, `c = Y(1-Y)`, `q = x q₀` (`ladderAX_eq`). The first term is not integrable at
large `a`, but its coefficient does not depend on `M`: in the difference of the two inner
Pauli–Villars terms the large-`a` logarithm cancels. This file proves, by the elementary masters
(improper integrals of nonnegative derivatives):

* `hasIoiInt_ladderAX_sub`: for `0 < Y, x < 1` and photon masses `la, lb₁, lb₂ > 0`, the
  difference `a ↦ ladderAX la lb₁ - ladderAX la lb₂` at `a = z + c` is integrable on `z > 0`
  and its integral is `ladderGm la lb₁ Y x - ladderGm la lb₂ Y x`;

with `ladderGm la lb` the `x`-integrand of eq. (3.4) at outer photon mass `la` and inner photon
mass `lb` (`ladderGm lam lam = ladderG lam`, `ladderGm_self`):

`ladderGm = P [x q₀/(M h) - 9c/M - log(M + c h)/h + Q/M² · log(1 + M/(c h))]`,
`Q = c (8M + 9c h - x q₀)`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology

namespace QED.TwoLoop.UnitLLink

open QED.TwoLoop.UnitLGraphReduce

/-! ### Integrals over `z > 0` -/

/-- `f` is integrable on `(0, ∞)` with integral `A`. -/
def HasIoiInt (f : ℝ → ℝ) (A : ℝ) : Prop :=
  IntegrableOn f (Ioi 0) ∧ ∫ z in Ioi (0 : ℝ), f z = A

theorem HasIoiInt.add {f g : ℝ → ℝ} {A B : ℝ} (hf : HasIoiInt f A) (hg : HasIoiInt g B) :
    HasIoiInt (fun z => f z + g z) (A + B) :=
  ⟨hf.1.add hg.1, by rw [integral_add hf.1 hg.1, hf.2, hg.2]⟩

theorem HasIoiInt.sub {f g : ℝ → ℝ} {A B : ℝ} (hf : HasIoiInt f A) (hg : HasIoiInt g B) :
    HasIoiInt (fun z => f z - g z) (A - B) :=
  ⟨hf.1.sub hg.1, by rw [integral_sub hf.1 hg.1, hf.2, hg.2]⟩

theorem HasIoiInt.const_mul {f : ℝ → ℝ} {A : ℝ} (hf : HasIoiInt f A) (r : ℝ) :
    HasIoiInt (fun z => r * f z) (r * A) :=
  ⟨hf.1.const_mul r, by rw [integral_const_mul, hf.2]⟩

theorem HasIoiInt.congr {f g : ℝ → ℝ} {A B : ℝ} (hf : HasIoiInt f A)
    (hfg : ∀ z ∈ Ioi (0 : ℝ), f z = g z) (hAB : A = B) : HasIoiInt g B := by
  refine ⟨hf.1.congr_fun hfg measurableSet_Ioi, ?_⟩
  rw [← hAB, ← hf.2]
  exact (setIntegral_congr_fun measurableSet_Ioi hfg).symm

/-- **An improper integral of a derivative of constant sign**, shifted by `c`:
`∫_{z > 0} k(z + c) dz = l - Φ(c)` when `Φ' = k` on `[c, ∞)`, `k` has a constant sign on `(c, ∞)`
and `Φ → l` at infinity. -/
theorem hasIoiInt_shift {Φ k : ℝ → ℝ} {c l : ℝ} (hd : ∀ a ∈ Ici c, HasDerivAt Φ (k a) a)
    (hk : (∀ a ∈ Ioi c, 0 ≤ k a) ∨ (∀ a ∈ Ioi c, k a ≤ 0)) (hl : Tendsto Φ atTop (𝓝 l)) :
    HasIoiInt (fun z => k (z + c)) (l - Φ c) := by
  have hderiv : ∀ z ∈ Ici (0 : ℝ), HasDerivAt (fun z => Φ (z + c)) (k (z + c)) z := fun z hz =>
    HasDerivAt.comp_add_const z c (hd (z + c) (by simp only [mem_Ici] at hz ⊢; linarith))
  have hg : Tendsto (fun z => Φ (z + c)) atTop (𝓝 l) :=
    hl.comp (tendsto_atTop_add_const_right _ c tendsto_id)
  have hint : IntegrableOn (fun z => k (z + c)) (Ioi 0) := by
    rcases hk with hk | hk
    · exact integrableOn_Ioi_deriv_of_nonneg' hderiv
        (fun z hz => hk (z + c) (by simp only [mem_Ioi] at hz ⊢; linarith)) hg
    · exact integrableOn_Ioi_deriv_of_nonpos' hderiv
        (fun z hz => hk (z + c) (by simp only [mem_Ioi] at hz ⊢; linarith)) hg
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hg, zero_add]

/-! ### The masters -/

section Masters

variable {M h c : ℝ}

/-- `1/(a (M + a h))`. -/
noncomputable def masterK2 (M h a : ℝ) : ℝ := 1 / (a * (M + a * h))
/-- `1/(a² (M + a h))`. -/
noncomputable def masterK3 (M h a : ℝ) : ℝ := 1 / (a ^ 2 * (M + a * h))
/-- `1/(M + a h)²`. -/
noncomputable def masterK4 (M h a : ℝ) : ℝ := 1 / (M + a * h) ^ 2
/-- `1/(a (M + a h)²)`. -/
noncomputable def masterK5 (M h a : ℝ) : ℝ := 1 / (a * (M + a * h) ^ 2)

theorem tendsto_log_sub_log_atTop (hM : 0 ≤ M) (hh : 0 < h) :
    Tendsto (fun a => log a - log (M + a * h)) atTop (𝓝 (-log h)) := by
  have h0 : Tendsto (fun a : ℝ => M / a) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := M)).div_atTop tendsto_id
  have h1 : Tendsto (fun a : ℝ => h + M / a) atTop (𝓝 h) := by
    simpa using (tendsto_const_nhds (x := h)).add h0
  have h2 := ((continuousAt_log hh.ne').tendsto.comp h1).neg
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with a ha
  have e : M + a * h = a * (h + M / a) := by field_simp; ring
  have hpos : 0 < h + M / a := by positivity
  simp only [Function.comp, e, log_mul ha.ne' hpos.ne']
  ring

theorem tendsto_log_sub_log_atTop' {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hh : 0 < h) :
    Tendsto (fun a => (log (M₁ + a * h) - log (M₂ + a * h)) / h) atTop (𝓝 0) := by
  have h1 := tendsto_log_sub_log_atTop hM₁ hh
  have h2 := tendsto_log_sub_log_atTop hM₂ hh
  have h3 := (h2.sub h1).div_const h
  simp only [sub_self, zero_div] at h3
  refine h3.congr fun a => ?_
  ring

theorem tendsto_inv_add_atTop (hh : 0 < h) :
    Tendsto (fun a => 1 / (M + a * h)) atTop (𝓝 0) := by
  have : Tendsto (fun a => M + a * h) atTop atTop :=
    tendsto_atTop_add_const_left _ M (tendsto_id.atTop_mul_const hh)
  exact (tendsto_inv_atTop_zero.comp this).congr fun a => by simp [one_div]

theorem hasDerivAt_log_add {a : ℝ} (hpos : 0 < M + a * h) :
    HasDerivAt (fun a => log (M + a * h)) (h / (M + a * h)) a := by
  have := (((hasDerivAt_id a).mul_const h).const_add M).log hpos.ne'
  simpa using this

/-- The master `∫_c^∞ (1/(M₁ + a h) - 1/(M₂ + a h)) da = (log(M₂ + c h) - log(M₁ + c h))/h`. -/
theorem hasIoiInt_master1 {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hh : 0 < h) (hc : 0 < c) :
    HasIoiInt (fun z => 1 / (M₁ + (z + c) * h) - 1 / (M₂ + (z + c) * h))
      ((log (M₂ + c * h) - log (M₁ + c * h)) / h) := by
  have hd : ∀ a ∈ Ici c, HasDerivAt (fun a => (log (M₁ + a * h) - log (M₂ + a * h)) / h)
      (1 / (M₁ + a * h) - 1 / (M₂ + a * h)) a := fun a ha => by
    have ha' : 0 < a := lt_of_lt_of_le hc ha
    have p1 : 0 < M₁ + a * h := by positivity
    have p2 : 0 < M₂ + a * h := by positivity
    have := ((hasDerivAt_log_add p1).sub (hasDerivAt_log_add p2)).div_const h
    refine this.congr_deriv ?_
    field_simp
  have hk : (∀ a ∈ Ioi c, 0 ≤ 1 / (M₁ + a * h) - 1 / (M₂ + a * h)) ∨
      (∀ a ∈ Ioi c, 1 / (M₁ + a * h) - 1 / (M₂ + a * h) ≤ 0) := by
    rcases le_total M₁ M₂ with hle | hle
    · left
      intro a ha
      have ha' : 0 < a := hc.trans ha
      have p1 : 0 < M₁ + a * h := by positivity
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le p1 (by linarith)
    · right
      intro a ha
      have ha' : 0 < a := hc.trans ha
      have p2 : 0 < M₂ + a * h := by positivity
      rw [sub_nonpos]
      exact one_div_le_one_div_of_le p2 (by linarith)
  have := hasIoiInt_shift hd hk (tendsto_log_sub_log_atTop' hM₁.le hM₂.le hh)
  refine this.congr (fun z _ => rfl) ?_
  ring

/-- `∫_c^∞ da/(a (M + a h)) = log(1 + M/(c h))/M`. -/
theorem hasIoiInt_master2 (hM : 0 < M) (hh : 0 < h) (hc : 0 < c) :
    HasIoiInt (fun z => masterK2 M h (z + c)) (log (1 + M / (c * h)) / M) := by
  have hd : ∀ a ∈ Ici c, HasDerivAt (fun a => (log a - log (M + a * h)) / M)
      (masterK2 M h a) a := fun a ha => by
    have ha' : 0 < a := lt_of_lt_of_le hc ha
    have p1 : 0 < M + a * h := by positivity
    have : HasDerivAt (fun a => (log a - log (M + a * h)) / M) ((1 / a - h / (M + a * h)) / M) a :=
      (((hasDerivAt_id a).log ha'.ne').sub (hasDerivAt_log_add p1)).div_const M
    refine this.congr_deriv ?_
    simp only [masterK2]
    field_simp
    ring
  have hk : (∀ a ∈ Ioi c, 0 ≤ masterK2 M h a) ∨ (∀ a ∈ Ioi c, masterK2 M h a ≤ 0) :=
    Or.inl fun a ha => by
      have ha' : 0 < a := hc.trans ha
      unfold masterK2; positivity
  have := hasIoiInt_shift hd hk ((tendsto_log_sub_log_atTop hM.le hh).div_const M)
  refine this.congr (fun z _ => rfl) ?_
  have hch : 0 < c * h := by positivity
  have e : 1 + M / (c * h) = (M + c * h) / (c * h) := by field_simp; ring
  rw [e, log_div (by positivity) hch.ne', log_mul hc.ne' hh.ne']
  ring

/-- `∫_c^∞ da/(a² (M + a h)) = 1/(M c) - h log(1 + M/(c h))/M²`. -/
theorem hasIoiInt_master3 (hM : 0 < M) (hh : 0 < h) (hc : 0 < c) :
    HasIoiInt (fun z => masterK3 M h (z + c))
      (1 / (M * c) - h * log (1 + M / (c * h)) / M ^ 2) := by
  have hd : ∀ a ∈ Ici c, HasDerivAt (fun a => -(1 / (M * a)) - h * (log a - log (M + a * h)) / M ^ 2)
      (masterK3 M h a) a := fun a ha => by
    have ha' : 0 < a := lt_of_lt_of_le hc ha
    have p1 : 0 < M + a * h := by positivity
    have h1 : HasDerivAt (fun a => 1 / (M * a)) (-(1 / (M * a ^ 2))) a := by
      have : HasDerivAt (fun a => (M * a)⁻¹) (-(M * 1) / (M * a) ^ 2) a :=
        ((hasDerivAt_id a).const_mul M).inv (by simp only [id]; positivity)
      simp only [one_div]
      refine this.congr_deriv ?_
      field_simp
    have : HasDerivAt (fun a => -(1 / (M * a)) - h * (log a - log (M + a * h)) / M ^ 2)
        (-(-(1 / (M * a ^ 2))) - h * (1 / a - h / (M + a * h)) / M ^ 2) a :=
      (h1.neg).sub ((((hasDerivAt_id a).log ha'.ne').sub
        (hasDerivAt_log_add p1)).const_mul h |>.div_const (M ^ 2))
    refine this.congr_deriv ?_
    simp only [masterK3]
    field_simp
    ring
  have hk : (∀ a ∈ Ioi c, 0 ≤ masterK3 M h a) ∨ (∀ a ∈ Ioi c, masterK3 M h a ≤ 0) :=
    Or.inl fun a ha => by
      have ha' : 0 < a := hc.trans ha
      unfold masterK3; positivity
  have hl : Tendsto (fun a => -(1 / (M * a)) - h * (log a - log (M + a * h)) / M ^ 2) atTop
      (𝓝 (-0 - h * -log h / M ^ 2)) := by
    have h0 : Tendsto (fun a : ℝ => 1 / (M * a)) atTop (𝓝 0) := by
      exact (tendsto_inv_atTop_zero.comp (tendsto_id.const_mul_atTop hM)).congr fun a => by
        simp [one_div]
    exact h0.neg.sub (((tendsto_log_sub_log_atTop hM.le hh).const_mul h).div_const _)
  have := hasIoiInt_shift hd hk hl
  refine this.congr (fun z _ => rfl) ?_
  have hch : 0 < c * h := by positivity
  have e : 1 + M / (c * h) = (M + c * h) / (c * h) := by field_simp; ring
  rw [e, log_div (by positivity) hch.ne', log_mul hc.ne' hh.ne']
  field_simp
  ring

/-- `∫_c^∞ da/(M + a h)² = 1/(h (M + c h))`. -/
theorem hasIoiInt_master4 (hM : 0 < M) (hh : 0 < h) (hc : 0 < c) :
    HasIoiInt (fun z => masterK4 M h (z + c)) (1 / (h * (M + c * h))) := by
  have hd : ∀ a ∈ Ici c, HasDerivAt (fun a => -(1 / (h * (M + a * h)))) (masterK4 M h a) a :=
    fun a ha => by
      have ha' : 0 < a := lt_of_lt_of_le hc ha
      have p1 : 0 < M + a * h := by positivity
      have : HasDerivAt (fun a => (h * (M + a * h))⁻¹) (-(h * (1 * h)) / (h * (M + a * h)) ^ 2) a :=
        ((((hasDerivAt_id a).mul_const h).const_add M).const_mul h).inv
          (by simp only [id]; positivity)
      simp only [one_div]
      refine this.neg.congr_deriv ?_
      simp only [masterK4]
      field_simp
  have hk : (∀ a ∈ Ioi c, 0 ≤ masterK4 M h a) ∨ (∀ a ∈ Ioi c, masterK4 M h a ≤ 0) :=
    Or.inl fun a _ => by unfold masterK4; positivity
  have hl : Tendsto (fun a => -(1 / (h * (M + a * h)))) atTop (𝓝 (-(0 / h))) := by
    refine ((tendsto_inv_add_atTop (M := M) hh).div_const h).neg.congr fun a => ?_
    field_simp
  have := hasIoiInt_shift hd hk hl
  refine this.congr (fun z _ => rfl) ?_
  ring

/-- `∫_c^∞ da/(a (M + a h)²) = log(1 + M/(c h))/M² - 1/(M (M + c h))`. -/
theorem hasIoiInt_master5 (hM : 0 < M) (hh : 0 < h) (hc : 0 < c) :
    HasIoiInt (fun z => masterK5 M h (z + c))
      (log (1 + M / (c * h)) / M ^ 2 - 1 / (M * (M + c * h))) := by
  have hd : ∀ a ∈ Ici c, HasDerivAt
      (fun a => ((log a - log (M + a * h)) / M + 1 / (M + a * h)) / M) (masterK5 M h a) a :=
    fun a ha => by
      have ha' : 0 < a := lt_of_lt_of_le hc ha
      have p1 : 0 < M + a * h := by positivity
      have h1 : HasDerivAt (fun a => 1 / (M + a * h)) (-(h / (M + a * h) ^ 2)) a := by
        have : HasDerivAt (fun a => (M + a * h)⁻¹) (-(1 * h) / (M + a * h) ^ 2) a :=
          (((hasDerivAt_id a).mul_const h).const_add M).inv p1.ne'
        simp only [one_div]
        refine this.congr_deriv ?_
        ring
      have : HasDerivAt (fun a => ((log a - log (M + a * h)) / M + 1 / (M + a * h)) / M)
          (((1 / a - h / (M + a * h)) / M + -(h / (M + a * h) ^ 2)) / M) a :=
        (((((hasDerivAt_id a).log ha'.ne').sub (hasDerivAt_log_add p1)).div_const M).add
          h1).div_const M
      refine this.congr_deriv ?_
      simp only [masterK5]
      field_simp
      ring
  have hk : (∀ a ∈ Ioi c, 0 ≤ masterK5 M h a) ∨ (∀ a ∈ Ioi c, masterK5 M h a ≤ 0) :=
    Or.inl fun a ha => by
      have ha' : 0 < a := hc.trans ha
      unfold masterK5; positivity
  have hl : Tendsto (fun a => ((log a - log (M + a * h)) / M + 1 / (M + a * h)) / M) atTop
      (𝓝 ((-log h / M + 0) / M)) :=
    (((tendsto_log_sub_log_atTop hM.le hh).div_const M).add
      (tendsto_inv_add_atTop (M := M) hh)).div_const M
  have := hasIoiInt_shift hd hk hl
  refine this.congr (fun z _ => rfl) ?_
  have hch : 0 < c * h := by positivity
  have e : 1 + M / (c * h) = (M + c * h) / (c * h) := by field_simp; ring
  rw [e, log_div (by positivity) hch.ne', log_mul hc.ne' hh.ne']
  field_simp
  ring

end Masters

/-! ### The ladder integrand in the variables `(a, x)` -/

/-- **The integrand of eq. (3.1) times the Jacobian** `a/x²` of `z_a = a(1-x)/x`, at outer photon
mass `la` and inner photon mass `lb`. -/
noncomputable def ladderAX (la lb Y x a : ℝ) : ℝ :=
  ladderDocF Y a (a * (1 - x) / x) (la ^ 2) (lb ^ 2) * (a / x ^ 2)

/-- **The `x`-integrand of eq. (3.4) at outer photon mass `la` and inner photon mass `lb`**:
`P [x q₀/(M h) - 9c/M - log(M + c h)/h + Q/M² · log(1 + M/(c h))]` with `h` built from `la` and
`M` from `lb`. -/
noncomputable def ladderGm (la lb Y x : ℝ) : ℝ :=
  Y * x * (1 - x) / 2 *
    (x * ((3 * Y - 2) + (4 * Y - Y ^ 2 - 2) * ((1 - x) / x) -
        2 * (Y * (1 - Y)) * ((1 - x) / x) ^ 2) /
        (ladderInnerMass 1 lb Y * (ladderInnerMass 1 la x / x)) -
      9 * (Y * (1 - Y)) / ladderInnerMass 1 lb Y -
      log (ladderInnerMass 1 lb Y + Y * (1 - Y) * (ladderInnerMass 1 la x / x)) /
        (ladderInnerMass 1 la x / x) +
      Y * (1 - Y) * (8 * ladderInnerMass 1 lb Y +
          9 * (Y * (1 - Y)) * (ladderInnerMass 1 la x / x) -
          x * ((3 * Y - 2) + (4 * Y - Y ^ 2 - 2) * ((1 - x) / x) -
            2 * (Y * (1 - Y)) * ((1 - x) / x) ^ 2)) / ladderInnerMass 1 lb Y ^ 2 *
        log (1 + ladderInnerMass 1 lb Y / (Y * (1 - Y) * (ladderInnerMass 1 la x / x))))

theorem ladderGm_self (lam : ℝ) : ladderGm lam lam = ladderG lam := rfl

theorem ladderH_pos {la x : ℝ} (hla : 0 < la) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < ladderInnerMass 1 la x / x :=
  div_pos (ladderInnerMass_pos one_pos hla ⟨hx.1.le, hx.2.le⟩) hx.1

/-- **The integrand in the variables `(a, x)`** is
`P [1/(M + a h) + 8c/(a(M + a h)) - 9c²/(a²(M + a h)) + q/(M + a h)² - q c/(a (M + a h)²)]`. -/
theorem ladderAX_eq {la lb Y x a : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hla : 0 < la) (hlb : 0 < lb) (ha : 0 < a) :
    ladderAX la lb Y x a = Y * x * (1 - x) / 2 *
      (1 / (ladderInnerMass 1 lb Y + a * (ladderInnerMass 1 la x / x)) +
        8 * (Y * (1 - Y)) * masterK2 (ladderInnerMass 1 lb Y) (ladderInnerMass 1 la x / x) a -
        9 * (Y * (1 - Y)) ^ 2 *
          masterK3 (ladderInnerMass 1 lb Y) (ladderInnerMass 1 la x / x) a +
        x * ((3 * Y - 2) + (4 * Y - Y ^ 2 - 2) * ((1 - x) / x) -
          2 * (Y * (1 - Y)) * ((1 - x) / x) ^ 2) *
          masterK4 (ladderInnerMass 1 lb Y) (ladderInnerMass 1 la x / x) a -
        x * ((3 * Y - 2) + (4 * Y - Y ^ 2 - 2) * ((1 - x) / x) -
          2 * (Y * (1 - Y)) * ((1 - x) / x) ^ 2) * (Y * (1 - Y)) *
          masterK5 (ladderInnerMass 1 lb Y) (ladderInnerMass 1 la x / x) a) := by
  have hM := ladderInnerMass_pos one_pos hlb ⟨hY.1.le, hY.2.le⟩
  have hh := ladderH_pos hla hx
  have hx0 : x ≠ 0 := hx.1.ne'
  have hD : 0 < ladderInnerMass 1 lb Y + a * (ladderInnerMass 1 la x / x) := by positivity
  have hU : a + a * (1 - x) / x = a / x := by field_simp; ring
  have eD : Y ^ 2 + (1 - Y) * lb ^ 2 + a ^ 2 / (a / x) + la ^ 2 * (a * (1 - x) / x) =
      ladderInnerMass 1 lb Y + a * (ladderInnerMass 1 la x / x) := by
    unfold ladderInnerMass
    field_simp
    ring
  unfold ladderAX ladderDocF
  rw [hU, eD]
  unfold masterK2 masterK3 masterK4 masterK5
  field_simp
  ring

/-- The shape of `ladderGm`: `P (q/(M h) - 9c/M - A/h + c (8M + 9c h - q)/M² · B)`. -/
noncomputable def gForm (P c q h M A B : ℝ) : ℝ :=
  P * (q / (M * h) - 9 * c / M - A / h + c * (8 * M + 9 * c * h - q) / M ^ 2 * B)

theorem ladderGm_eq_form (la lb Y x : ℝ) :
    ladderGm la lb Y x = gForm (Y * x * (1 - x) / 2) (Y * (1 - Y))
      (x * ((3 * Y - 2) + (4 * Y - Y ^ 2 - 2) * ((1 - x) / x) -
        2 * (Y * (1 - Y)) * ((1 - x) / x) ^ 2)) (ladderInnerMass 1 la x / x)
      (ladderInnerMass 1 lb Y)
      (log (ladderInnerMass 1 lb Y + Y * (1 - Y) * (ladderInnerMass 1 la x / x)))
      (log (1 + ladderInnerMass 1 lb Y / (Y * (1 - Y) * (ladderInnerMass 1 la x / x)))) := rfl

/-- `gForm` as the combination of the masters. -/
theorem gForm_eq_masters {P c q h M A B : ℝ} (hM : 0 < M) (hh : 0 < h) (hc : 0 < c)
    (hMc : 0 < M + c * h) :
    gForm P c q h M A B = P * (-A / h + 8 * c * (B / M) - 9 * c ^ 2 * (1 / (M * c) - h * B / M ^ 2) +
      q * (1 / (h * (M + c * h))) - q * c * (B / M ^ 2 - 1 / (M * (M + c * h)))) := by
  unfold gForm
  have := hM.ne'
  have := hh.ne'
  have := hc.ne'
  have := hMc.ne'
  field_simp
  ring

/-- **The `a`-integration** (section 3.3 of the document): for `0 < Y, x < 1` and photon masses
`la, lb₁, lb₂ > 0`, the difference of the integrands at the two inner photon masses, at
`a = z + Y(1-Y)`, is integrable on `z > 0` with integral `ladderGm la lb₁ - ladderGm la lb₂`. -/
theorem hasIoiInt_ladderAX_sub {la lb₁ lb₂ Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hla : 0 < la) (hlb₁ : 0 < lb₁) (hlb₂ : 0 < lb₂) :
    HasIoiInt (fun z => ladderAX la lb₁ Y x (z + Y * (1 - Y)) - ladderAX la lb₂ Y x (z + Y * (1 - Y)))
      (ladderGm la lb₁ Y x - ladderGm la lb₂ Y x) := by
  have hM₁ := ladderInnerMass_pos one_pos hlb₁ ⟨hY.1.le, hY.2.le⟩
  have hM₂ := ladderInnerMass_pos one_pos hlb₂ ⟨hY.1.le, hY.2.le⟩
  have hh := ladderH_pos hla hx
  have hc : 0 < Y * (1 - Y) := mul_pos hY.1 (by linarith [hY.2])
  have I1 := hasIoiInt_master1 hM₁ hM₂ hh hc
  have I2 := (hasIoiInt_master2 hM₁ hh hc).sub (hasIoiInt_master2 hM₂ hh hc)
  have I3 := (hasIoiInt_master3 hM₁ hh hc).sub (hasIoiInt_master3 hM₂ hh hc)
  have I4 := (hasIoiInt_master4 hM₁ hh hc).sub (hasIoiInt_master4 hM₂ hh hc)
  have I5 := (hasIoiInt_master5 hM₁ hh hc).sub (hasIoiInt_master5 hM₂ hh hc)
  set q := x * ((3 * Y - 2) + (4 * Y - Y ^ 2 - 2) * ((1 - x) / x) -
    2 * (Y * (1 - Y)) * ((1 - x) / x) ^ 2) with hq
  have I := (((((I1.add (I2.const_mul (8 * (Y * (1 - Y))))).sub
    (I3.const_mul (9 * (Y * (1 - Y)) ^ 2))).add (I4.const_mul q)).sub
    (I5.const_mul (q * (Y * (1 - Y))))).const_mul (Y * x * (1 - x) / 2))
  refine I.congr (fun z hz => ?_) ?_
  · have ha : 0 < z + Y * (1 - Y) := by simp only [mem_Ioi] at hz; linarith
    rw [ladderAX_eq hY hx hla hlb₁ ha, ladderAX_eq hY hx hla hlb₂ ha]
    ring
  · rw [ladderGm_eq_form, ladderGm_eq_form, ← hq,
      gForm_eq_masters hM₁ hh hc (by positivity), gForm_eq_masters hM₂ hh hc (by positivity)]
    ring

end QED.TwoLoop.UnitLLink

end
