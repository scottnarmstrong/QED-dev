/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecSegCont

/-!
# (R-Π₄) step L9: a Lipschitz bound for integrals of polynomial families

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (Lipschitz bounds
near `s = 0`). The Lipschitz counterpart of `QED.GradedProof.RPi4.exists_norm_integral_upoly_le`:
a polynomial family is Lipschitz on `[-1/2, 1/2]` with the constant `∑ⱼ j ‖cⱼ‖` of its
interpolation coefficients, and a quotient `A / ((1 - u²)ᵃ Vᴺ)` with `V ≥ c > 0` bounded and
Lipschitz in `u` (uniformly off a null set) is Lipschitz with an integrable constant.

* `dec_norm_pow_sub_pow_le`, `dec_norm_div_sub_div_le`, `dec_norm_wt_sub_le`: elementary bounds;
* `dec_norm_upoly_le`, `dec_norm_upoly_sub_le`: a polynomial family at one parameter;
* `decLagβ₀`, `decLagβ`, `dec_norm_upoly_le_of_nodes`, `dec_norm_upoly_sub_le_of_nodes`: the same
  from bounds at the nodes;
* `dec_lip_integral_upoly`: **the Lipschitz bound for `∫ A(·, u) / ((1 - u²)ᵃ V(u)ᴺ)`**.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set Polynomial
open scoped Real

namespace QED.GradedProof.RPi4

open QED.TwoLoop.PauliZeroLimit

/-! ### Elementary bounds -/

theorem dec_norm_pow_sub_pow_le {z w : ℂ} {B : ℝ} (hB : 1 ≤ B) (hz : ‖z‖ ≤ B) (hw : ‖w‖ ≤ B)
    (n : ℕ) : ‖z ^ n - w ^ n‖ ≤ n * B ^ n * ‖z - w‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : z ^ (n + 1) - w ^ (n + 1) = z * (z ^ n - w ^ n) + (z - w) * w ^ n := by ring
    have hB0 : 0 ≤ B := zero_le_one.trans hB
    have hwn : ‖w ^ n‖ ≤ B ^ n := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hw n
    have hBn : B ^ n ≤ B ^ (n + 1) := pow_le_pow_right₀ hB (Nat.le_succ n)
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖z‖ * ‖z ^ n - w ^ n‖ ≤ B * (n * B ^ n * ‖z - w‖) :=
      mul_le_mul hz ih (norm_nonneg _) hB0
    have h2 : ‖z - w‖ * ‖w ^ n‖ ≤ ‖z - w‖ * B ^ n := mul_le_mul_of_nonneg_left hwn (norm_nonneg _)
    have hzw := norm_nonneg (z - w)
    push_cast
    calc ‖z‖ * ‖z ^ n - w ^ n‖ + ‖z - w‖ * ‖w ^ n‖
        ≤ B * (n * B ^ n * ‖z - w‖) + ‖z - w‖ * B ^ n := add_le_add h1 h2
      _ = n * B ^ (n + 1) * ‖z - w‖ + B ^ n * ‖z - w‖ := by ring
      _ ≤ n * B ^ (n + 1) * ‖z - w‖ + B ^ (n + 1) * ‖z - w‖ :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right hBn hzw)
      _ = (n + 1) * B ^ (n + 1) * ‖z - w‖ := by ring

theorem dec_norm_div_sub_div_le {a a' b b' : ℂ} (hb : b ≠ 0) (hb' : b' ≠ 0) :
    ‖a / b - a' / b'‖ ≤ ‖a - a'‖ / ‖b‖ + ‖a'‖ * ‖b - b'‖ / (‖b‖ * ‖b'‖) := by
  have e : a / b - a' / b' = (a - a') / b + a' * (b' - b) / (b * b') := by
    field_simp
    ring
  rw [e]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_div, norm_div, norm_mul, norm_mul, norm_sub_rev b' b]

theorem dec_norm_wt_le_one {u : ℝ} (hu : |u| ≤ 1 / 2) : ‖wt u‖ ≤ 1 := by
  have e : wt u = ((1 - u ^ 2 : ℝ) : ℂ) := by simp [wt]
  have h2 : u ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs u, abs_nonneg u]
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [sq_nonneg u]

theorem dec_norm_wt_sub_le {u u' : ℝ} (hu : |u| ≤ 1 / 2) (hu' : |u'| ≤ 1 / 2) :
    ‖wt u - wt u'‖ ≤ |u - u'| := by
  have e : wt u - wt u' = ((u' - u) * (u' + u) : ℝ) := by simp [wt]; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_sub_comm]
  have : |u' + u| ≤ 1 := (abs_add_le _ _).trans (by linarith)
  nlinarith [abs_nonneg (u - u')]

/-! ### Polynomial families at one parameter -/

section UPoly

variable {ι : Type*} {D : ℕ} {f : ι → ℝ → ℂ}

theorem dec_norm_upoly_le (hf : IsUPoly D f) (x : ι) {u : ℝ} (hu : |u| ≤ 1 / 2) :
    ‖f x u‖ ≤ ∑ j ∈ Finset.range (D + 1), ‖(interp D f x).coeff j‖ := by
  have hu1 : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  rw [hf.eq_interp x u hu1, eval_interp_eq_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (abs_nonneg u) (hu.trans (by norm_num)))

theorem dec_norm_upoly_sub_le (hf : IsUPoly D f) (x : ι) {u u' : ℝ} (hu : |u| ≤ 1 / 2)
    (hu' : |u'| ≤ 1 / 2) :
    ‖f x u - f x u'‖ ≤ (∑ j ∈ Finset.range (D + 1), (j : ℝ) * ‖(interp D f x).coeff j‖) *
      |u - u'| := by
  have hu1 : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  have hu1' : u' ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [neg_abs_le u'], by linarith [le_abs_self u']⟩
  rw [hf.eq_interp x u hu1, hf.eq_interp x u' hu1', eval_interp_eq_sum, eval_interp_eq_sum,
    ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← mul_sub, norm_mul]
  have hp : ‖(u : ℂ) ^ j - (u' : ℂ) ^ j‖ ≤ j * |u - u'| := by
    rw [← ofReal_pow, ← ofReal_pow, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    refine (abs_pow_sub_pow_le u u' j).trans ?_
    have hm : max |u| |u'| ≤ 1 := max_le (hu.trans (by norm_num)) (hu'.trans (by norm_num))
    have : max |u| |u'| ^ (j - 1) ≤ 1 := pow_le_one₀ (le_max_of_le_left (abs_nonneg _)) hm
    have h0 : 0 ≤ |u - u'| * j := by positivity
    nlinarith
  calc ‖(interp D f x).coeff j‖ * ‖(u : ℂ) ^ j - (u' : ℂ) ^ j‖
      ≤ ‖(interp D f x).coeff j‖ * (j * |u - u'|) :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = (j : ℝ) * ‖(interp D f x).coeff j‖ * |u - u'| := by ring

/-- The sum of the norms of the coefficients of the Lagrange basis (degree `D`). -/
noncomputable def decLagβ₀ (D : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (D + 1), ∑ k : Fin (D + 1), ‖(lbasis D k).coeff j‖

/-- The weighted sum `∑ⱼ j ∑ₖ ‖(ℓₖ)ⱼ‖` of the Lagrange basis (degree `D`). -/
noncomputable def decLagβ (D : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (D + 1), (j : ℝ) * ∑ k : Fin (D + 1), ‖(lbasis D k).coeff j‖

theorem dec_norm_interp_coeff_le (x : ι) {B : ℝ} (hB : ∀ k, ‖f x (node D k)‖ ≤ B) (j : ℕ) :
    ‖(interp D f x).coeff j‖ ≤ B * ∑ k : Fin (D + 1), ‖(lbasis D k).coeff j‖ := by
  rw [interp_coeff, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hB k) (norm_nonneg _)

theorem dec_norm_upoly_le_of_nodes (hf : IsUPoly D f) (x : ι) {B : ℝ}
    (hB : ∀ k, ‖f x (node D k)‖ ≤ B) {u : ℝ} (hu : |u| ≤ 1 / 2) : ‖f x u‖ ≤ B * decLagβ₀ D := by
  refine (dec_norm_upoly_le hf x hu).trans ?_
  rw [decLagβ₀, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => dec_norm_interp_coeff_le x hB j

theorem dec_norm_upoly_sub_le_of_nodes (hf : IsUPoly D f) (x : ι) {B : ℝ}
    (hB : ∀ k, ‖f x (node D k)‖ ≤ B) {u u' : ℝ} (hu : |u| ≤ 1 / 2) (hu' : |u'| ≤ 1 / 2) :
    ‖f x u - f x u'‖ ≤ B * decLagβ D * |u - u'| := by
  refine (dec_norm_upoly_sub_le hf x hu hu').trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
  rw [decLagβ, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have := dec_norm_interp_coeff_le x hB j
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

end UPoly

/-! ### The Lipschitz bound for integrals of polynomial families -/

section Integral

variable {ι : Type*} [MeasurableSpace ι] {μ : Measure ι}

/-- **A Lipschitz bound for `∫ A(·, u) / ((1 - u²)ᵃ V(u)ᴺ)`** on `[-1/2, 1/2]`, for polynomial
families `A` with integrable values at the nodes and `c ≤ V ≤ B`, `V` Lipschitz in `u` with a
constant `L`, uniformly off a null set. -/
theorem dec_lip_integral_upoly {D a N : ℕ} {A : ι → ℝ → ℂ} (hA : IsUPoly D A)
    (hAi : ∀ k, Integrable (fun x => A x (node D k)) μ) {c B L : ℝ} (hc : 0 < c) (hB : 1 ≤ B)
    {V : ℝ → ι → ℝ} (hVm : ∀ u, AEStronglyMeasurable (V u) μ)
    (hV : ∀ᵐ x ∂μ, ∀ u u' : ℝ, |u| ≤ 1 / 2 → |u'| ≤ 1 / 2 →
      c ≤ V u x ∧ V u x ≤ B ∧ |V u x - V u' x| ≤ L * |u - u'|) :
    ∃ C : ℝ, ∀ u u' : ℝ, |u| ≤ 1 / 2 → |u'| ≤ 1 / 2 →
      ‖∫ x, A x u / (wt u ^ a * (V u x : ℂ) ^ N) ∂μ -
        ∫ x, A x u' / (wt u' ^ a * (V u' x : ℂ) ^ N) ∂μ‖ ≤ C * |u - u'| := by
  have hcf : ∀ j, Integrable (fun x => (interp D A x).coeff j) μ := integrable_interp_coeff hAi
  set K : ι → ℝ := fun x => ∑ j ∈ Finset.range (D + 1), ‖(interp D A x).coeff j‖ with hK
  set K₁ : ι → ℝ := fun x => ∑ j ∈ Finset.range (D + 1), (j : ℝ) * ‖(interp D A x).coeff j‖
    with hK₁
  have hKi : Integrable K μ := integrable_finsetSum _ fun j _ => (hcf j).norm
  have hK₁i : Integrable K₁ μ :=
    integrable_finsetSum _ fun j _ => (hcf j).norm.const_mul _
  have hK0 : ∀ x, 0 ≤ K x := fun x => Finset.sum_nonneg fun _ _ => norm_nonneg _
  set d₀ : ℝ := (3 / 4 : ℝ) ^ a * c ^ N with hd₀
  have hd₀p : 0 < d₀ := by positivity
  set LD : ℝ := (a + N * L) * B ^ N with hLD
  -- the denominator
  set Dn : ℝ → ι → ℂ := fun u x => wt u ^ a * (V u x : ℂ) ^ N with hDn
  have hDlow : ∀ x u, |u| ≤ 1 / 2 → c ≤ V u x → d₀ ≤ ‖Dn u x‖ := fun x u hu hVx => by
    simp only [hDn]
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hc.trans_le hVx)]
    exact mul_le_mul (pow_le_pow_left₀ (by norm_num) (norm_wt_ge hu) a)
      (pow_le_pow_left₀ hc.le hVx N) (by positivity) (by positivity)
  have hDsub : ∀ x u u', |u| ≤ 1 / 2 → |u'| ≤ 1 / 2 → c ≤ V u x → V u x ≤ B →
      c ≤ V u' x → V u' x ≤ B → |V u x - V u' x| ≤ L * |u - u'| →
      ‖Dn u x - Dn u' x‖ ≤ LD * |u - u'| := by
    intro x u u' hu hu' hc1 hB1 hc2 hB2 hL
    have hVn : ∀ v, c ≤ v → v ≤ B → ‖((v : ℝ) : ℂ)‖ ≤ B := fun v h1 h2 => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hc.trans_le h1)]
      exact h2
    have hw1 := dec_norm_pow_sub_pow_le le_rfl (dec_norm_wt_le_one hu) (dec_norm_wt_le_one hu') a
    have hw2 := dec_norm_wt_sub_le hu hu'
    have hv1 := dec_norm_pow_sub_pow_le hB (hVn _ hc1 hB1) (hVn _ hc2 hB2) N
    have hvv : ‖((V u x : ℝ) : ℂ) - ((V u' x : ℝ) : ℂ)‖ ≤ L * |u - u'| := by
      rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hL
    have hVN : ‖((V u x : ℝ) : ℂ) ^ N‖ ≤ B ^ N := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hVn _ hc1 hB1) N
    have hwa : ‖wt u' ^ a‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (dec_norm_wt_le_one hu')
    have e : Dn u x - Dn u' x = (wt u ^ a - wt u' ^ a) * ((V u x : ℝ) : ℂ) ^ N +
        wt u' ^ a * (((V u x : ℝ) : ℂ) ^ N - ((V u' x : ℝ) : ℂ) ^ N) := by
      simp only [hDn]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    simp only [one_pow, mul_one] at hw1
    have hB0 : 0 ≤ B := zero_le_one.trans hB
    have hL0 : 0 ≤ L * |u - u'| := (norm_nonneg _).trans hvv
    have t1 : ‖wt u ^ a - wt u' ^ a‖ * ‖((V u x : ℝ) : ℂ) ^ N‖ ≤ a * |u - u'| * B ^ N :=
      mul_le_mul (hw1.trans (mul_le_mul_of_nonneg_left hw2 (Nat.cast_nonneg a))) hVN
        (norm_nonneg _) (by positivity)
    have t2 : ‖wt u' ^ a‖ * ‖((V u x : ℝ) : ℂ) ^ N - ((V u' x : ℝ) : ℂ) ^ N‖ ≤
        1 * (N * B ^ N * (L * |u - u'|)) :=
      mul_le_mul hwa (hv1.trans (mul_le_mul_of_nonneg_left hvv (by positivity)))
        (norm_nonneg _) zero_le_one
    calc ‖wt u ^ a - wt u' ^ a‖ * ‖((V u x : ℝ) : ℂ) ^ N‖ +
          ‖wt u' ^ a‖ * ‖((V u x : ℝ) : ℂ) ^ N - ((V u' x : ℝ) : ℂ) ^ N‖
        ≤ a * |u - u'| * B ^ N + 1 * (N * B ^ N * (L * |u - u'|)) := add_le_add t1 t2
      _ = LD * |u - u'| := by simp only [hLD]; ring
  -- the integrand
  set G : ι → ℝ := fun x => K₁ x / d₀ + K x * |LD| / d₀ ^ 2 with hG
  have hGi : Integrable G μ := (hK₁i.div_const _).add ((hKi.mul_const _).div_const _)
  have hIoo : ∀ u : ℝ, |u| ≤ 1 / 2 → u ∈ Ioo (-1 : ℝ) 1 := fun u hu =>
    ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  have hFm : ∀ u : ℝ, |u| ≤ 1 / 2 →
      AEStronglyMeasurable (fun x => A x u / (wt u ^ a * (V u x : ℂ) ^ N)) μ := by
    intro u hu
    have e : (fun x => A x u) =
        fun x => ∑ j ∈ Finset.range (D + 1), (interp D A x).coeff j * (u : ℂ) ^ j :=
      funext fun x => by rw [hA.eq_interp x u (hIoo u hu), eval_interp_eq_sum]
    have hP : AEStronglyMeasurable (fun x => A x u) μ := by
      rw [e]
      exact Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
        (hcf j).aestronglyMeasurable.mul_const _
    have hVc : AEStronglyMeasurable (fun x => ((V u x : ℝ) : ℂ)) μ :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable (hVm u)
    exact hP.div₀ ((hVc.pow N).const_mul _)
  have hFi : ∀ u : ℝ, |u| ≤ 1 / 2 →
      Integrable (fun x => A x u / (wt u ^ a * (V u x : ℂ) ^ N)) μ := by
    intro u hu
    refine Integrable.mono' (hKi.div_const d₀) (hFm u hu) ?_
    filter_upwards [hV] with x hx
    have hVx := (hx u u hu hu).1
    rw [norm_div]
    exact div_le_div₀ (hK0 x) (dec_norm_upoly_le hA x hu) hd₀p (hDlow x u hu hVx)
  refine ⟨∫ x, G x ∂μ, fun u u' hu hu' => ?_⟩
  rw [← integral_sub (hFi u hu) (hFi u' hu'), ← integral_mul_const]
  refine norm_integral_le_of_norm_le (hGi.mul_const _) ?_
  filter_upwards [hV] with x hx
  obtain ⟨hc1, hB1, hL⟩ := hx u u' hu hu'
  obtain ⟨hc2, hB2, -⟩ := hx u' u hu' hu
  have hD1 := hDlow x u hu hc1
  have hD2 := hDlow x u' hu' hc2
  have hDs := hDsub x u u' hu hu' hc1 hB1 hc2 hB2 hL
  have hA1 := dec_norm_upoly_sub_le hA x hu hu'
  have hA2 := dec_norm_upoly_le hA x hu'
  have hn1 : Dn u x ≠ 0 := norm_pos_iff.mp (hd₀p.trans_le hD1)
  have hn2 : Dn u' x ≠ 0 := norm_pos_iff.mp (hd₀p.trans_le hD2)
  have h := dec_norm_div_sub_div_le (a := A x u) (a' := A x u') hn1 hn2
  simp only [hDn] at h hD1 hD2 hDs
  refine h.trans ?_
  have hd2 : d₀ ^ 2 ≤ ‖wt u ^ a * (V u x : ℂ) ^ N‖ * ‖wt u' ^ a * (V u' x : ℂ) ^ N‖ := by
    rw [sq]; exact mul_le_mul hD1 hD2 hd₀p.le (hd₀p.le.trans hD1)
  have hu0 := abs_nonneg (u - u')
  have e1 : ‖A x u - A x u'‖ / ‖wt u ^ a * (V u x : ℂ) ^ N‖ ≤ K₁ x * |u - u'| / d₀ :=
    div_le_div₀ (by positivity) hA1 hd₀p hD1
  have e2 : ‖A x u'‖ * ‖wt u ^ a * (V u x : ℂ) ^ N - wt u' ^ a * (V u' x : ℂ) ^ N‖ /
      (‖wt u ^ a * (V u x : ℂ) ^ N‖ * ‖wt u' ^ a * (V u' x : ℂ) ^ N‖) ≤
      K x * (|LD| * |u - u'|) / d₀ ^ 2 :=
    div_le_div₀ (by positivity) (mul_le_mul hA2 (hDs.trans (mul_le_mul_of_nonneg_right
      (le_abs_self _) hu0)) (norm_nonneg _) (hK0 x)) (by positivity) hd2
  calc _ ≤ K₁ x * |u - u'| / d₀ + K x * (|LD| * |u - u'|) / d₀ ^ 2 := add_le_add e1 e2
    _ = G x * |u - u'| := by simp only [hG]; ring

end Integral

end QED.GradedProof.RPi4

end
