/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ClassLimit
public import QED.Integration.EnergyIntegral
public import QED.Integration.SpatialIntegral

/-!
# One-loop `ε → 0⁺` limits through the two-loop parametric representation

A tool for obligations O2-7 and O2-13 (`docs/TWO-LOOP-DERIVATION.md`, sections 4.3 and 5.1): the
limit `ε → 0⁺` of the energy-first integral (D) of a one-loop integrand `F_ε(k) = N(k) ∏ᵢ Dᵢ(k)⁻¹`
with a polynomial numerator of degree at most four and at least five propagators, such as the
one-loop vertex with a counterterm inserted on an internal line.

The two-loop machinery (`QED/TwoLoop/ClassLimitParametric.lean`) already proves such limits for
two loop momenta. A one-loop integrand is brought into its scope by multiplying it with an
independent auxiliary loop `H_ε(k') = (k'² + M² - iε)⁻³`:

* the joint energy-first integral (T₉) of a product `F(ℓ₀) H(ℓ₁)` is the product of the two
  energy-first integrals (D), for all integrands (`jointEnergyFirstIntegral_two_mul`; Fubini for
  product functions needs no integrability);
* the auxiliary loop has an explicit limit `auxLimit M ≠ 0`
  (`tendsto_energyFirstIntegral_aux`, `auxLimit_ne_zero`), from the closed-form energy integral of
  `QED/Integration/EnergyIntegral.lean` and the radial integral `∫ (|v|² + M²)^{-5/2} = 4π/(3M²)`;
* the product is a two-loop integrand with lines of loop direction `(1, 0)` (those of `F`) and
  `(0, 1)` (the three auxiliary lines), so `tendsto_jointEnergyFirstIntegral_of_refined` applies
  once the refined criterion, the pointwise numerator bound and the positivity of `V` hold.

For numerators that depend only on `ℓ₀`, the pointwise bound is
`refinedBound_of_dependsOnZero`; for line data given by kinds (outgoing electron, incoming
electron, photon, auxiliary), the positivity is `symanzikV_kinds_ge`: the one-loop
`D ≥ (1 - x_γ)² m² + x_γ μ²` in the two-loop form.

## Main statements

* `jointEnergyFirstIntegral_two_mul`, `tendsto_energyFirstIntegral_aux`, `auxLimit_ne_zero`.
* `refinedBound_of_dependsOnZero`, `symanzikV_kinds_ge`.
* `exists_tendsto_energyFirstIntegral_of_product`: the one-loop limit exists.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.TwoLoop.CountertermLimit

open QED.Integration QED.Integration.TwoLoop QED.TwoLoop.Bridge

/-! ### Product integrands -/

/-- Fubini for a product function on `X²`, with no integrability hypothesis. -/
theorem integral_finTwo_mul {X : Type*} [MeasureSpace X] [SigmaFinite (volume : Measure X)]
    (f g : X → ℂ) : ∫ x : Fin 2 → X, f (x 0) * g (x 1) = (∫ x, f x) * ∫ x, g x :=
  ((measurePreserving_finTwoArrow (volume : Measure X)).integral_comp'
    (fun y : X × X => f y.1 * g y.2)).trans (integral_prod_mul f g)

/-- **The joint energy-first integral of a product** `F(ℓ₀) H(ℓ₁)` is the product of the
energy-first integrals, for all integrands. -/
theorem jointEnergyFirstIntegral_two_mul (F H : (Fin 4 → ℝ) → ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => F (ℓ 0) * H (ℓ 1)) =
      QED.OneLoop.energyFirstIntegral F * QED.OneLoop.energyFirstIntegral H := by
  unfold QED.TwoLoop.jointEnergyFirstIntegral QED.OneLoop.energyFirstIntegral
  have hin : ∀ v : Fin 2 → Fin 3 → ℝ,
      ∫ t : Fin 2 → ℝ, F (Fin.cons (t 0) (v 0)) * H (Fin.cons (t 1) (v 1)) =
        (∫ t : ℝ, F (Fin.cons t (v 0))) * ∫ t : ℝ, H (Fin.cons t (v 1)) := fun v =>
    integral_finTwo_mul (fun t => F (Fin.cons t (v 0))) (fun t => H (Fin.cons t (v 1)))
  simp only [hin]
  exact integral_finTwo_mul (fun v => ∫ t : ℝ, F (Fin.cons t v))
    (fun v => ∫ t : ℝ, H (Fin.cons t v))

/-! ### The auxiliary loop -/

theorem dot_cons_self (t : ℝ) (v : Fin 3 → ℝ) :
    Minkowski.dot (Fin.cons t v : Fin 4 → ℝ) (Fin.cons t v) = -t ^ 2 + ∑ k, v k ^ 2 := by
  have h0 : (Fin.cons t v : Fin 4 → ℝ) 0 = t := rfl
  have h1 : (Fin.cons t v : Fin 4 → ℝ) 1 = v 0 := rfl
  have h2 : (Fin.cons t v : Fin 4 → ℝ) 2 = v 1 := rfl
  have h3 : (Fin.cons t v : Fin 4 → ℝ) 3 = v 2 := rfl
  rw [Minkowski.dot_eq, h0, h1, h2, h3, Fin.sum_univ_three]
  ring

theorem re_neg_aux (a ε : ℝ) : (-((a : ℂ) - (ε : ℂ) * I)).re = -a := by
  simp only [neg_re, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
    sub_zero]

theorem im_neg_aux (a ε : ℝ) : (-((a : ℂ) - (ε : ℂ) * I)).im = ε := by
  simp only [neg_im, sub_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one,
    zero_sub, neg_neg, add_zero]

/-- The energy integral of the auxiliary loop at spatial momentum `v`, as a function of `ε`. -/
noncomputable def auxSpatial (M ε : ℝ) (v : Fin 3 → ℝ) : ℂ :=
  -((3 * π / 8 : ℂ) *
    (-((((∑ k, v k ^ 2 + M ^ 2 : ℝ)) : ℂ) - (ε : ℂ) * I)) ^ (-(5 / 2 : ℂ)))

/-- The limit of the auxiliary loop. -/
noncomputable def auxLimit (M : ℝ) : ℂ := ∫ v : Fin 3 → ℝ, auxSpatial M 0 v

theorem neg_aux_mem_slitPlane {M ε : ℝ} (hε : 0 < ε) (v : Fin 3 → ℝ) :
    -((((∑ k, v k ^ 2 + M ^ 2 : ℝ)) : ℂ) - (ε : ℂ) * I) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  right
  rw [im_neg_aux]
  exact hε.ne'

theorem integral_aux_time (M : ℝ) {ε : ℝ} (hε : 0 < ε) (v : Fin 3 → ℝ) :
    ∫ t : ℝ, ((propDenom M ε (Fin.cons t v))⁻¹) ^ 3 = auxSpatial M ε v := by
  rw [auxSpatial, ← integral_neg_sq_add_zpow_three (neg_aux_mem_slitPlane hε v)]
  congr 1
  funext t
  have hx : (((-t ^ 2 + ∑ k, v k ^ 2 + M ^ 2 : ℝ)) : ℂ) - (ε : ℂ) * I =
      -(t : ℂ) ^ 2 + ((((∑ k, v k ^ 2 + M ^ 2 : ℝ)) : ℂ) - (ε : ℂ) * I) := by
    push_cast
    ring
  rw [propDenom, dot_cons_self, hx,
    show (-3 : ℤ) = -((3 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast, inv_pow]

theorem aux_ne_zero {M : ℝ} (hM : 0 < M) (ε : ℝ) (v : Fin 3 → ℝ) :
    -((((∑ k, v k ^ 2 + M ^ 2 : ℝ)) : ℂ) - (ε : ℂ) * I) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [re_neg_aux, zero_re] at this
  have h0 : 0 ≤ ∑ k, v k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  nlinarith [sq_pos_of_pos hM]

theorem norm_auxSpatial_le {M : ℝ} (hM : 0 < M) (ε : ℝ) (v : Fin 3 → ℝ) :
    ‖auxSpatial M ε v‖ ≤ 3 * π / 8 * (∑ k, v k ^ 2 + M ^ 2) ^ (-(5 / 2 : ℝ)) := by
  have hz := aux_ne_zero hM ε v
  have ha : 0 < ∑ k, v k ^ 2 + M ^ 2 := by
    have h0 : 0 ≤ ∑ k, v k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
    positivity
  rw [auxSpatial, norm_neg, norm_mul, norm_cpow_of_ne_zero hz]
  have hre : (∑ k, v k ^ 2 + M ^ 2) ≤
      ‖-((((∑ k, v k ^ 2 + M ^ 2 : ℝ)) : ℂ) - (ε : ℂ) * I)‖ := by
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [re_neg_aux, abs_neg, abs_of_pos ha]
  have h83 : ‖(3 * π / 8 : ℂ)‖ = 3 * π / 8 := by
    rw [show (3 * π / 8 : ℂ) = ((3 * π / 8 : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [h83]
  have hre' : (-(5 / 2 : ℂ)).re = -(5 / 2 : ℝ) := by norm_num
  have him' : (-(5 / 2 : ℂ)).im = 0 := by norm_num
  rw [hre', him', mul_zero, Real.exp_zero, div_one]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha hre (by norm_num))
    (by positivity)

theorem continuous_auxSpatial (M : ℝ) {ε : ℝ} (hε : 0 < ε) : Continuous (auxSpatial M ε) := by
  unfold auxSpatial
  refine Continuous.neg (continuous_const.mul ?_)
  refine Continuous.cpow (by fun_prop) continuous_const fun v => neg_aux_mem_slitPlane hε v

theorem tendsto_auxSpatial {M : ℝ} (hM : 0 < M) (v : Fin 3 → ℝ) :
    Tendsto (fun ε => auxSpatial M ε v) (𝓝[>] 0) (𝓝 (auxSpatial M 0 v)) := by
  set a : ℝ := ∑ k, v k ^ 2 + M ^ 2 with ha_def
  have ha : 0 < a := by
    have h0 : 0 ≤ ∑ k, v k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
    positivity
  set z : ℝ → ℂ := fun ε => -(((a : ℝ) : ℂ) - (ε : ℂ) * I) with hz_def
  have hz0 : z 0 = ((-a : ℝ) : ℂ) := by simp [z]
  have hzc : Continuous z := by fun_prop
  have hzS : Tendsto z (𝓝[>] 0) (𝓝[{w : ℂ | 0 ≤ w.im}] (z 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨(hzc.tendsto 0).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    simp [z, hε.le]
  have hlog := (continuousWithinAt_log_of_re_neg_of_im_zero (z := z 0) (by simp [hz0, ha])
    (by simp [hz0])).tendsto.comp hzS
  have hexp := ((continuous_exp.tendsto _).comp (hlog.mul_const (-(5 / 2 : ℂ))))
  have hne : ∀ ε, z ε ≠ 0 := fun ε => aux_ne_zero hM ε v
  have key : ∀ ε, auxSpatial M ε v = -((3 * π / 8 : ℂ) * exp (log (z ε) * (-(5 / 2 : ℂ)))) :=
    fun ε => by rw [auxSpatial, ← cpow_def_of_ne_zero (hne ε)]
  simp only [key]
  exact (hexp.const_mul _).neg

/-- **The limit of the auxiliary loop** `(k² + M² - iε)⁻³`. -/
theorem tendsto_energyFirstIntegral_aux {M : ℝ} (hM : 0 < M) :
    Tendsto (fun ε : ℝ => QED.OneLoop.energyFirstIntegral fun k => ((propDenom M ε k)⁻¹) ^ 3)
      (𝓝[>] 0) (𝓝 (auxLimit M)) := by
  have hbnd : Integrable fun v : Fin 3 → ℝ =>
      3 * π / 8 * (∑ k, v k ^ 2 + M ^ 2) ^ (-(5 / 2 : ℝ)) :=
    (integrable_sum_sq_add_rpow (by positivity) (by norm_num)).const_mul _
  have hlim : Tendsto (fun ε : ℝ => ∫ v, auxSpatial M ε v) (𝓝[>] 0) (𝓝 (auxLimit M)) :=
    tendsto_integral_filter_of_dominated_convergence _
      (eventually_nhdsWithin_of_forall fun ε hε =>
        (continuous_auxSpatial M hε).aestronglyMeasurable)
      (Eventually.of_forall fun ε => Eventually.of_forall fun v => norm_auxSpatial_le hM ε v)
      hbnd (Eventually.of_forall fun v => tendsto_auxSpatial hM v)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  unfold QED.OneLoop.energyFirstIntegral
  exact integral_congr_ae (Eventually.of_forall fun v => (integral_aux_time M hε v).symm)

/-- **The limit of the auxiliary loop is not zero.** -/
theorem auxLimit_ne_zero {M : ℝ} (hM : 0 < M) : auxLimit M ≠ 0 := by
  have hpt : ∀ v : Fin 3 → ℝ, auxSpatial M 0 v =
      (-((3 * π / 8 : ℂ) * exp (π * I * (-(5 / 2 : ℂ))))) *
        (((∑ k, v k ^ 2 + M ^ 2) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) := by
    intro v
    have ha : 0 < ∑ k, v k ^ 2 + M ^ 2 := by
      have h0 : 0 ≤ ∑ k, v k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
      positivity
    have h1 : -((((∑ k, v k ^ 2 + M ^ 2 : ℝ)) : ℂ) - ((0 : ℝ) : ℂ) * I) =
        ((-(∑ k, v k ^ 2 + M ^ 2) : ℝ) : ℂ) := by push_cast; ring
    rw [auxSpatial, h1, ofReal_cpow_of_nonpos (by linarith), ofReal_neg, neg_neg,
      ofReal_cpow ha.le]
    push_cast
    ring
  rw [auxLimit]
  simp only [hpt]
  rw [integral_const_mul, integral_complex_ofReal,
    integral_sum_sq_add_rpow_neg_five_halves (by positivity)]
  refine mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero ?_ (exp_ne_zero _))) ?_
  · exact_mod_cast (by positivity : (3 * π / 8 : ℝ) ≠ 0)
  · exact_mod_cast (by positivity : (4 * π / (3 * M ^ 2) : ℝ) ≠ 0)

/-! ### The pointwise bound for numerators depending on the first loop momentum only -/

/-- A crude growth bound for a polynomial of degree at most four. -/
theorem exists_norm_evalC_le (Q : LoopQuartic) :
    ∃ C, 0 ≤ C ∧ ∀ X : LoopIndex → ℂ, ‖Q.evalC X‖ ≤ C * (1 + ‖X‖) ^ 4 := by
  refine ⟨‖Q.const‖ + ∑ a, ‖Q.lin a‖ + ∑ a, ∑ b, ‖Q.quad a b‖ +
    ∑ a, ∑ b, ∑ c, ‖Q.cub a b c‖ + ∑ a, ∑ b, ∑ c, ∑ d, ‖Q.quart a b c d‖, by positivity,
    fun X => ?_⟩
  set r := 1 + ‖X‖ with hr_def
  have hr : 1 ≤ r := le_add_of_nonneg_right (norm_nonneg _)
  have hr0 : 0 ≤ r := by linarith
  have hX : ∀ a, ‖X a‖ ≤ r := fun a => (norm_le_pi_norm X a).trans (by linarith)
  have hr1 : r ≤ r ^ 4 := le_self_pow₀ hr (by norm_num)
  have hr2 : r ^ 2 ≤ r ^ 4 := pow_le_pow_right₀ hr (by norm_num)
  have hr3 : r ^ 3 ≤ r ^ 4 := pow_le_pow_right₀ hr (by norm_num)
  have hr4 : 1 ≤ r ^ 4 := one_le_pow₀ hr
  have t0 : ‖Q.const‖ ≤ ‖Q.const‖ * r ^ 4 := le_mul_of_one_le_right (norm_nonneg _) hr4
  have t1 : ‖∑ a, Q.lin a * X a‖ ≤ (∑ a, ‖Q.lin a‖) * r ^ 4 := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((hX a).trans hr1) (norm_nonneg _)
  have t2 : ‖∑ a, ∑ b, Q.quad a b * (X a * X b)‖ ≤ (∑ a, ∑ b, ‖Q.quad a b‖) * r ^ 4 := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖X a‖ * ‖X b‖ ≤ r * r := mul_le_mul (hX a) (hX b) (norm_nonneg _) hr0
      _ = r ^ 2 := by ring
      _ ≤ r ^ 4 := hr2
  have t3 : ‖∑ a, ∑ b, ∑ c, Q.cub a b c * (X a * X b * X c)‖ ≤
      (∑ a, ∑ b, ∑ c, ‖Q.cub a b c‖) * r ^ 4 := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [norm_mul, norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖X a‖ * ‖X b‖ * ‖X c‖ ≤ r * r * r :=
          mul_le_mul (mul_le_mul (hX a) (hX b) (norm_nonneg _) hr0) (hX c) (norm_nonneg _)
            (by positivity)
      _ = r ^ 3 := by ring
      _ ≤ r ^ 4 := hr3
  have t4 : ‖∑ a, ∑ b, ∑ c, ∑ d, Q.quart a b c d * (X a * X b * X c * X d)‖ ≤
      (∑ a, ∑ b, ∑ c, ∑ d, ‖Q.quart a b c d‖) * r ^ 4 := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖X a‖ * ‖X b‖ * ‖X c‖ * ‖X d‖ ≤ r * r * r * r :=
          mul_le_mul (mul_le_mul (mul_le_mul (hX a) (hX b) (norm_nonneg _) hr0) (hX c)
            (norm_nonneg _) (by positivity)) (hX d) (norm_nonneg _) (by positivity)
      _ = r ^ 4 := by ring
  unfold LoopQuartic.evalC
  have e1 := norm_add_le (Q.const + ∑ a, Q.lin a * X a + ∑ a, ∑ b, Q.quad a b * (X a * X b) +
    ∑ a, ∑ b, ∑ c, Q.cub a b c * (X a * X b * X c))
    (∑ a, ∑ b, ∑ c, ∑ d, Q.quart a b c d * (X a * X b * X c * X d))
  have e2 := norm_add_le (Q.const + ∑ a, Q.lin a * X a + ∑ a, ∑ b, Q.quad a b * (X a * X b))
    (∑ a, ∑ b, ∑ c, Q.cub a b c * (X a * X b * X c))
  have e3 := norm_add_le (Q.const + ∑ a, Q.lin a * X a) (∑ a, ∑ b, Q.quad a b * (X a * X b))
  have e4 := norm_add_le Q.const (∑ a, Q.lin a * X a)
  nlinarith

/-- **The pointwise bound for a numerator depending only on `ℓ₀`**: if `Q(ℓ) = Q(ℓ₀, 0)` and
`E` consists of four lines of loop direction `(1, 0)`, then `Q` satisfies the refined bound of
exponent four for `E`. -/
theorem refinedBound_of_dependsOnZero {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    {E : Finset (Fin (m + 1))} (hE : E.card = 4) (hα : ∀ e ∈ E, α e = ![1, 0])
    (Q : LoopQuartic) (hQ : ∀ ℓ, Q.eval ℓ = Q.eval ![ℓ 0, 0]) : RefinedBound α E 4 Q.eval := by
  obtain ⟨e₀, he₀⟩ : E.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨C, hC, hQC⟩ := exists_norm_evalC_le Q
  have hν : ∀ ν : Fin 4, ∃ Cν : ℝ, 0 ≤ Cν ∧ ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A.PosDef →
      ∀ ℓ : Fin 2 → Fin 4 → ℝ,
        |ℓ 0 ν| ≤ Cν * lineWeight α {e₀} A * Real.sqrt (1 + loopNorm A ℓ) := by
    intro ν
    obtain ⟨Cν, hCν, h⟩ := refinedBound_lineMomentum α (fun _ => 0) e₀ ν
    refine ⟨Cν, hCν, fun A hA ℓ => ?_⟩
    have h1 := h A hA ℓ
    have hl : lineMomentum α (fun _ => 0) e₀ ℓ ν = ℓ 0 ν := by
      simp [lineMomentum, hα e₀ he₀, Fin.sum_univ_two]
    simp only at h1
    rwa [hl, norm_real, Real.norm_eq_abs, pow_one] at h1
  choose Cν hCν hbound using hν
  set K := 1 + ∑ ν, Cν ν with hK
  have hK0 : 0 ≤ ∑ ν, Cν ν := Finset.sum_nonneg fun ν _ => hCν ν
  refine ⟨C * K ^ 4, by positivity, fun A hA ℓ => ?_⟩
  set w := Real.sqrt (1 + α e₀ ⬝ᵥ Matrix.mulVec A⁻¹ (α e₀)) with hw
  have hw1 : 1 ≤ w := one_le_sqrt_lineFactor α hA e₀
  have hs1 := sqrt_one_add_loopNorm_one_le hA ℓ
  set s := Real.sqrt (1 + loopNorm A ℓ) with hs
  have hlw : lineWeight α {e₀} A = w := lineWeight_singleton α e₀ A
  have hLW : lineWeight α E A = w ^ 4 := by
    unfold lineWeight
    rw [Finset.prod_congr rfl (fun e he => by rw [hα e he, ← hα e₀ he₀]), Finset.prod_const, hE]
  have hX : ‖loopComp ![ℓ 0, 0]‖ ≤ (∑ ν, Cν ν) * w * s := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_
    obtain ⟨i, ν⟩ := a
    fin_cases i
    · simp only [loopComp, Fin.zero_eta, Matrix.cons_val_zero, norm_real, Real.norm_eq_abs]
      calc |ℓ 0 ν| ≤ Cν ν * w * s := by rw [← hlw]; exact hbound ν A hA ℓ
        _ ≤ (∑ ν, Cν ν) * w * s := by
          gcongr
          exact Finset.single_le_sum (f := Cν) (fun ν _ => hCν ν) (Finset.mem_univ ν)
    · simp only [loopComp, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Pi.zero_apply, ofReal_zero, norm_zero]
      positivity
  have hws : 1 ≤ w * s := one_le_mul_of_one_le_of_one_le hw1 hs1
  have h1X : 1 + ‖loopComp ![ℓ 0, 0]‖ ≤ K * (w * s) := by nlinarith
  rw [hQ ℓ, LoopQuartic.eval]
  calc ‖Q.evalC (loopComp ![ℓ 0, 0])‖ ≤ C * (1 + ‖loopComp ![ℓ 0, 0]‖) ^ 4 := hQC _
    _ ≤ C * (K * (w * s)) ^ 4 := by gcongr
    _ = C * K ^ 4 * lineWeight α E A * s ^ 4 := by rw [hLW]; ring

/-! ### Line data by kinds and the positivity of `V` -/

/-- The kind of a line of the product data: an electron line carrying the outgoing momentum
`p'`, one carrying the incoming momentum `p`, a photon line (no external momentum), or a line of
the auxiliary loop. -/
inductive LineKind
  | out
  | inn
  | pho
  | aux
  deriving DecidableEq

namespace LineKind

/-- The integer loop direction: `(0, 1)` for the auxiliary loop, `(1, 0)` otherwise. -/
def dir : LineKind → Fin 2 → ℤ
  | aux => ![0, 1]
  | _ => ![1, 0]

/-- The external momentum of the line. -/
def mom (p p' : Fin 4 → ℝ) : LineKind → Fin 4 → ℝ
  | out => p'
  | inn => p
  | _ => 0

/-- The momentum of the line at loop momenta `ℓ`. -/
def lineMom (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : LineKind → Fin 4 → ℝ
  | out => p' + ℓ 0
  | inn => p + ℓ 0
  | pho => ℓ 0
  | aux => ℓ 1

/-- The coefficient of `(p + p')/2` in the external momentum. -/
def ca : LineKind → ℝ
  | out => 1
  | inn => 1
  | _ => 0

/-- The coefficient of `(p' - p)/2` in the external momentum. -/
def cb : LineKind → ℝ
  | out => 1
  | inn => -1
  | _ => 0

end LineKind

/-- The line momentum of the product data is `LineKind.lineMom`. -/
theorem lineMomentum_kinds {m : ℕ} (κ : Fin (m + 1) → LineKind) (p p' : Fin 4 → ℝ)
    (i : Fin (m + 1)) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum (castLoopMatrix fun i => (κ i).dir) (fun i => (κ i).mom p p') i ℓ =
      (κ i).lineMom p p' ℓ := by
  funext ν
  rcases h : κ i with _ | _ | _ | _ <;>
    simp [lineMomentum, castLoopMatrix, LineKind.dir, LineKind.mom, LineKind.lineMom,
      Fin.sum_univ_two, add_comm, h]

/-- **Positivity of `V` for the product data** (the one-loop `D ≥ (1 - x_γ)² m² + x_γ μ²` in the
two-loop form): for on-shell `p, p'` with `q² ≥ 0`, electron and auxiliary lines of mass `m` and
photon lines of mass at least `μ`, `V ≥ (3/4) min(m², μ²)` wherever `U ≠ 0`. -/
theorem symanzikV_kinds_ge {m : ℕ} (κ : Fin (m + 1) → LineKind) (Ms : Fin (m + 1) → ℝ)
    {mass μ : ℝ} {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -mass ^ 2)
    (hp' : Minkowski.dot p' p' = -mass ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hMe : ∀ i, κ i ≠ .pho → Ms i ^ 2 = mass ^ 2) (hMp : ∀ i, κ i = .pho → μ ^ 2 ≤ Ms i ^ 2)
    {z : Fin (m + 1) → ℝ} (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1)
    (hU : symanzikU (castLoopMatrix fun i => (κ i).dir) z ≠ 0) :
    3 / 4 * min (mass ^ 2) (μ ^ 2) ≤
      symanzikV (castLoopMatrix fun i => (κ i).dir) (fun i => (κ i).mom p p') Ms z := by
  set α : Fin (m + 1) → Fin 2 → ℝ := castLoopMatrix fun i => (κ i).dir with hα
  set P : Fin 4 → ℝ := (1 / 2 : ℝ) • (p + p')
  set K : Fin 4 → ℝ := (1 / 2 : ℝ) • (p' - p)
  have hmom : (fun i => (κ i).mom p p') = fun i => (κ i).ca • P + (κ i).cb • K := by
    funext i ν
    rcases h : κ i with _ | _ | _ | _ <;>
      simp [LineKind.mom, LineKind.ca, LineKind.cb, P, K] <;> ring
  rw [hmom, symanzikV_smul_add_smul α Ms z _ _ (dot_half_add_half_sub hp hp'),
    dot_half_add_self hp hp']
  have hk := dot_half_sub_self_nonneg hq
  set k := Minkowski.dot K K
  set a : Fin (m + 1) → ℝ := fun i => (κ i).ca
  set b : Fin (m + 1) → ℝ := fun i => (κ i).cb
  set x : Fin (m + 1) → ℝ := fun i => if κ i = .inn then 1 else 0
  set y : Fin (m + 1) → ℝ := fun i => if κ i = .out then 1 else 0
  set g : Fin (m + 1) → ℝ := fun i => if κ i = .pho then 1 else 0
  set sa : Fin (m + 1) → ℝ := fun i => if κ i = .aux then 1 else 0
  have hα0 : ∀ i, α i 0 = 1 - sa i := fun i => by
    rcases h : κ i with _ | _ | _ | _ <;> simp [α, castLoopMatrix, sa, h, LineKind.dir]
  have hα1 : ∀ i, α i 1 = sa i := fun i => by
    rcases h : κ i with _ | _ | _ | _ <;> simp [α, castLoopMatrix, sa, h, LineKind.dir]
  -- `R(b) ≥ R(a)`
  have hb : (fun i => y i - x i) = b := by
    funext i; rcases h : κ i with _ | _ | _ | _ <;> simp [x, y, b, h, LineKind.cb]
  have ha : (fun i => x i + y i) = a := by
    funext i; rcases h : κ i with _ | _ | _ | _ <;> simp [x, y, a, h, LineKind.ca]
  have hRba : remainder α z a ≤ remainder α z b := by
    have h := remainder_sub_sub_remainder_add α z x y
    rw [hb, ha] at h
    have hxy : ∑ i, z i * x i * y i = 0 :=
      Finset.sum_eq_zero fun i _ => by
        rcases h : κ i with _ | _ | _ | _ <;> simp [x, y, h]
    have hcx1 : coefVec α z x 1 = 0 :=
      Finset.sum_eq_zero fun i _ => by
        rw [hα1]; rcases h : κ i with _ | _ | _ | _ <;> simp [x, sa, h]
    have hcy1 : coefVec α z y 1 = 0 :=
      Finset.sum_eq_zero fun i _ => by
        rw [hα1]; rcases h : κ i with _ | _ | _ | _ <;> simp [y, sa, h]
    have hA01 : symanzikMatrix α z 0 1 = 0 := by
      simp only [symanzikMatrix, Matrix.of_apply]
      exact Finset.sum_eq_zero fun i _ => by
        rw [hα0, hα1]; rcases h : κ i with _ | _ | _ | _ <;> simp [sa, h]
    have hA00 : 0 ≤ symanzikMatrix α z 0 0 := by
      simp only [symanzikMatrix, Matrix.of_apply]
      exact Finset.sum_nonneg fun i _ => by
        rw [mul_assoc]; exact mul_nonneg (hz i) (mul_self_nonneg _)
    have hA11 : 0 ≤ symanzikMatrix α z 1 1 := by
      simp only [symanzikMatrix, Matrix.of_apply]
      exact Finset.sum_nonneg fun i _ => by
        rw [mul_assoc]; exact mul_nonneg (hz i) (mul_self_nonneg _)
    have hU0 : 0 ≤ symanzikU α z := by
      rw [symanzikU, Matrix.det_fin_two, symanzikMatrix_one_zero, hA01]
      nlinarith
    have hcx0 : 0 ≤ coefVec α z x 0 :=
      Finset.sum_nonneg fun i _ => by
        rw [hα0]; rcases h : κ i with _ | _ | _ | _ <;> simp [x, sa, h, hz i]
    have hcy0 : 0 ≤ coefVec α z y 0 :=
      Finset.sum_nonneg fun i _ => by
        rw [hα0]; rcases h : κ i with _ | _ | _ | _ <;> simp [y, sa, h, hz i]
    rw [dotProduct_inv_symanzikMatrix_mulVec, hcx1, hcy1, hA01, hxy] at h
    have : 0 ≤ (symanzikU α z)⁻¹ *
        (symanzikMatrix α z 1 1 * coefVec α z x 0 * coefVec α z y 0) :=
      mul_nonneg (inv_nonneg.mpr hU0) (mul_nonneg (mul_nonneg hA11 hcx0) hcy0)
    nlinarith
  -- `R(a) ≤ E (1 - E)² + G E²`
  set E := ∑ i, z i * a i
  set G := ∑ i, z i * g i
  set S := ∑ i, z i * sa i
  have hRa : remainder α z a ≤ E * (1 - E) ^ 2 + G * E ^ 2 := by
    refine (remainder_le_sum_sq α hz hU a ![-E, 0]).trans (le_of_eq ?_)
    have hpt : ∀ i, z i * (∑ s, α i s * (![-E, 0] : Fin 2 → ℝ) s + a i) ^ 2 =
        z i * a i * (1 - E) ^ 2 + z i * g i * E ^ 2 := fun i => by
      rw [Fin.sum_univ_two, hα0, hα1]
      have e0 : (![-E, 0] : Fin 2 → ℝ) 0 = -E := rfl
      have e1 : (![-E, 0] : Fin 2 → ℝ) 1 = 0 := rfl
      rcases h : κ i with _ | _ | _ | _ <;>
        simp only [a, g, sa, h, LineKind.ca, reduceCtorEq, ite_true, ite_false, e0, e1] <;> ring
    simp only [hpt, Finset.sum_add_distrib, ← Finset.sum_mul]
    rfl
  have hM : mass ^ 2 * (E + S) + μ ^ 2 * G ≤ ∑ i, z i * Ms i ^ 2 := by
    have hpt : ∀ i, mass ^ 2 * (z i * a i + z i * sa i) + μ ^ 2 * (z i * g i) ≤
        z i * Ms i ^ 2 := fun i => by
      have hz0 := hz i
      rcases h : κ i with _ | _ | _ | _ <;>
        simp only [a, sa, g, h, LineKind.ca, reduceCtorEq, ite_true, ite_false]
      · rw [hMe i (by simp [h])]; exact le_of_eq (by ring)
      · rw [hMe i (by simp [h])]; exact le_of_eq (by ring)
      · nlinarith [mul_le_mul_of_nonneg_left (hMp i h) hz0]
      · rw [hMe i (by simp [h])]; exact le_of_eq (by ring)
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt i
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at this
    linarith
  have hsum : E + G + S = 1 := by
    have hpt : ∀ i, z i * a i + z i * g i + z i * sa i = z i := fun i => by
      rcases h : κ i with _ | _ | _ | _ <;> simp [a, g, sa, h, LineKind.ca]
    rw [← hz1, ← Finset.sum_congr rfl fun i _ => hpt i]
    simp only [Finset.sum_add_distrib]
    rfl
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun i _ => by
    rcases h : κ i with _ | _ | _ | _ <;> simp [a, h, LineKind.ca, hz i]
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun i _ => by
    rcases h : κ i with _ | _ | _ | _ <;> simp [g, h, hz i]
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => by
    rcases h : κ i with _ | _ | _ | _ <;> simp [sa, h, hz i]
  set c := min (mass ^ 2) (μ ^ 2)
  have hc1 : c ≤ mass ^ 2 := min_le_left _ _
  have hc2 : c ≤ μ ^ 2 := min_le_right _ _
  have hmR : mass ^ 2 * remainder α z a ≤ mass ^ 2 * (E * (1 - E) ^ 2 + G * E ^ 2) :=
    mul_le_mul_of_nonneg_left hRa (sq_nonneg _)
  have hkR : 0 ≤ k * (remainder α z b - remainder α z a) := mul_nonneg hk (by linarith)
  have hG : G = 1 - E - S := by linarith
  have key : mass ^ 2 * (E + S) + μ ^ 2 * G - mass ^ 2 * (E * (1 - E) ^ 2 + G * E ^ 2) =
      mass ^ 2 * (E ^ 2 * (1 + S) + S) + μ ^ 2 * G := by rw [hG]; ring
  have h1 : c * (E ^ 2 + S) ≤ mass ^ 2 * (E ^ 2 * (1 + S) + S) := by
    have : E ^ 2 + S ≤ E ^ 2 * (1 + S) + S := by nlinarith [sq_nonneg E]
    exact (mul_le_mul_of_nonneg_left this (le_trans (le_min (sq_nonneg _) (sq_nonneg _))
      le_rfl)).trans (mul_le_mul_of_nonneg_right hc1 (by positivity))
  have h2 : c * G ≤ μ ^ 2 * G := mul_le_mul_of_nonneg_right hc2 hG0
  have hc0 : 0 ≤ c := le_min (sq_nonneg _) (sq_nonneg _)
  have h3 : 3 / 4 * c ≤ c * (E ^ 2 + S + G) := by
    rw [show E ^ 2 + S + G = E ^ 2 - E + 1 by linarith]
    nlinarith [sq_nonneg (E - 1 / 2)]
  nlinarith

/-! ### The one-loop limit -/

/-- **The one-loop limit through the product with the auxiliary loop.** Let `F_ε` be one-loop
integrands such that, for every `ε > 0`, `Q(ℓ) ∏ᵢ Dᵢ(ℓ)⁻¹ = F_ε(ℓ₀) (ℓ₁² + M² - iε)⁻³` for
two-loop data `(α, p, M)` with at least eight lines satisfying the refined criterion, the refined
bound and a positive lower bound on `V`. Then the energy-first integral of `F_ε` converges as
`ε → 0⁺`. -/
theorem exists_tendsto_energyFirstIntegral_of_product {m : ℕ} (hm : 7 ≤ m)
    (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ)
    (Q : LoopQuartic) {E : Finset (Fin (m + 1))} (hcrit : NoSubdivergenceRefined 2 E α)
    (hB : RefinedBound α E 4 Q.eval) {c : ℝ} (hc : 0 < c)
    (hV : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → symanzikU α z ≠ 0 →
      c ≤ symanzikV α p M z) {mass : ℝ} (hmass : 0 < mass) (F : ℝ → (Fin 4 → ℝ) → ℂ)
    (hfac : ∀ ε : ℝ, 0 < ε → ∀ ℓ : Fin 2 → Fin 4 → ℝ,
      Q.eval ℓ * ∏ i, (lineDenom α p M ε i ℓ)⁻¹ =
        F ε (ℓ 0) * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3) :
    ∃ L : ℂ, Tendsto (fun ε => QED.OneLoop.energyFirstIntegral (F ε)) (𝓝[>] 0) (𝓝 L) := by
  have hT := QED.TwoLoop.ClassLimit.tendsto_jointEnergyFirstIntegral_of_refined Q α p M hm hcrit
    hB hc hV
  have hH := tendsto_energyFirstIntegral_aux hmass
  have hH0 := auxLimit_ne_zero hmass
  refine ⟨_, (hT.div hH hH0).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin, hH.eventually_ne hH0] with ε (hε : 0 < ε) hne
  rw [Pi.div_apply, show (fun ℓ => Q.eval ℓ * ∏ i, (lineDenom α p M ε i ℓ)⁻¹) =
      fun ℓ => F ε (ℓ 0) * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3 from funext (hfac ε hε),
    jointEnergyFirstIntegral_two_mul (F ε) (fun k => ((propDenom mass ε k)⁻¹) ^ 3)]
  exact mul_div_cancel_right₀ _ hne

end QED.TwoLoop.CountertermLimit

end
