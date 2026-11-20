/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceV
public import QED.GradedProof.RPi4Face
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# (R-Π₄) step L6d2: the `σ`-integration of a face, with a rate

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d2 (model-free).
A face function has the form `g(ρ, σ) = (1 - ρ)^q ∫ H(ρ, σ, x) dμ(x)` with
`H = θ ∑ⱼ Dⱼ(ρ) (v(ρ) + θ σ)^{-kⱼ}`, `0 ≤ θ ≤ 1`, coefficients `Dⱼ` bounded and Lipschitz at
`ρ = 0`, `v ≥ c₁ > 0` Lipschitz at `ρ = 0`, and exponents `kⱼ ≥ 2`. With the `θ`-marginal bound
`∫ θ (c₁ + θσ)^{-2} dμ ≤ A σ^{-3/2}` this gives the bounds `B(σ) = K₀ A σ^{-3/2}` and
`B₁(σ) = K₁ A σ^{-3/2}` of the face lemma, hence the face limit with rate `u^{-1/2}`:

* `inv_pow_le_face` (`w^{-k} ≤ c₁^{-(k-2)} c'^{-2}`), `norm_face_sub_le_pos` (the face lemma
  with its bounds needed only for `σ > 0`);
* `SigData` (the hypotheses), `sigH`, `sigG`, `norm_sigH_le`, `norm_sigH_sub_le`,
  `norm_sigG_le`, `norm_sigG_le_unif`, `norm_sigG_sub_le`, `measurable_sigG`;
* **`norm_sigma_face_le`**: `‖u ∫₀^{ρ₀} g(ρ, ρu) dρ - ∫₀^∞ g(0, σ) dσ‖ ≤ C u^{-1/2}`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.GradedProof.RPi4

/-! ### Elementary inequalities -/

/-- `w^{-k} ≤ c₁^{-(k-2)} c'^{-2}` for `0 < c₁ ≤ c' ≤ w`, `k ≥ 2`. -/
theorem inv_pow_le_face {c₁ c' w : ℝ} (hc : 0 < c₁) (h1 : c₁ ≤ c') (h2 : c' ≤ w) {k : ℕ}
    (hk : 2 ≤ k) : (w ^ k)⁻¹ ≤ (c₁ ^ (k - 2))⁻¹ * (c' ^ 2)⁻¹ := by
  have hc' : 0 < c' := hc.trans_le h1
  rw [← mul_inv, show w ^ k = w ^ (k - 2) * w ^ 2 by rw [← pow_add]; congr 1; omega]
  exact inv_anti₀ (by positivity) (mul_le_mul (pow_le_pow_left₀ hc.le (h1.trans h2) _)
    (pow_le_pow_left₀ hc'.le h2 _) (by positivity) (pow_nonneg (hc.le.trans (h1.trans h2)) _))

/-- **The face lemma, with its bounds needed only for `σ > 0`.** -/
theorem norm_face_sub_le_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → ℝ → E} {B B₁ : ℝ → ℝ} {ρ₀ u : ℝ} (hρ₀ : 0 < ρ₀) (hu : 0 < u)
    (hgi : IntervalIntegrable (fun σ => g (σ / u) σ) volume 0 (ρ₀ * u))
    (hg0 : IntegrableOn (g 0) (Ioi 0)) (hB : IntegrableOn B (Ioi (ρ₀ * u)))
    (hB₁ : IntervalIntegrable (fun σ => σ * B₁ σ) volume 0 (ρ₀ * u))
    (hbd : ∀ σ, 0 < σ → ‖g 0 σ‖ ≤ B σ)
    (hlip : ∀ ρ σ, 0 ≤ ρ → ρ ≤ ρ₀ → 0 < σ → ‖g ρ σ - g 0 σ‖ ≤ ρ * B₁ σ) :
    ‖u • (∫ ρ in (0 : ℝ)..ρ₀, g ρ (ρ * u)) - ∫ σ in Ioi 0, g 0 σ‖ ≤
      u⁻¹ * (∫ σ in (0 : ℝ)..ρ₀ * u, σ * B₁ σ) + ∫ σ in Ioi (ρ₀ * u), B σ := by
  have hR : 0 < ρ₀ * u := mul_pos hρ₀ hu
  have hg0R : IntegrableOn (g 0) (Ioi (ρ₀ * u)) := hg0.mono_set (Ioi_subset_Ioi hR.le)
  have hg0i : IntervalIntegrable (g 0) volume 0 (ρ₀ * u) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mpr (hg0.mono_set Ioc_subset_Ioi_self)
  rw [smul_integral_comp_face g hu, ← intervalIntegral.integral_interval_add_Ioi hg0 hg0R,
    ← sub_sub, ← intervalIntegral.integral_sub hgi hg0i]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · have hb : IntervalIntegrable (fun σ => u⁻¹ * (σ * B₁ σ)) volume 0 (ρ₀ * u) :=
      hB₁.const_mul _
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.norm_integral_le_of_norm_le hR.le (ae_of_all _ fun σ hσ => ?_) hb
    have hρ : 0 ≤ σ / u := div_nonneg hσ.1.le hu.le
    have hρ' : σ / u ≤ ρ₀ := (div_le_iff₀ hu).mpr hσ.2
    refine (hlip _ _ hρ hρ' hσ.1).trans (le_of_eq ?_)
    rw [div_eq_inv_mul, mul_assoc]
  · refine (norm_integral_le_integral_norm _).trans ?_
    refine setIntegral_mono_on hg0R.norm hB measurableSet_Ioi fun σ hσ => ?_
    exact hbd σ (hR.trans hσ)

/-! ### The abstract face function -/

variable {X : Type*} [MeasurableSpace X] {r : ℕ}

/-- The abstract face integrand `θ ∑ⱼ Dⱼ(ρ) (v(ρ) + θσ)^{-kⱼ}`. -/
noncomputable def sigH (θ : X → ℝ) (D : Fin r → ℝ → X → ℂ) (vh : ℝ → X → ℝ) (k : Fin r → ℕ)
    (ρ σ : ℝ) (x : X) : ℂ :=
  (θ x : ℂ) * ∑ j, D j ρ x * (((vh ρ x + θ x * σ : ℝ) : ℂ) ^ k j)⁻¹

/-- The abstract face function `(1 - ρ)^q ∫ H dμ`. -/
noncomputable def sigG (μ : Measure X) (q : ℕ) (θ : X → ℝ) (D : Fin r → ℝ → X → ℂ)
    (vh : ℝ → X → ℝ) (k : Fin r → ℕ) (ρ σ : ℝ) : ℂ :=
  (((1 - ρ) ^ q : ℝ) : ℂ) * ∫ x, sigH θ D vh k ρ σ x ∂μ

/-- The `θ`-majorant `θ (c₁ + θσ)^{-2}`. -/
noncomputable def sigM (θ : X → ℝ) (c₁ σ : ℝ) (x : X) : ℝ := θ x * ((c₁ + θ x * σ) ^ 2)⁻¹

/-- **The hypotheses of the `σ`-integration.** -/
structure SigData (μ : Measure X) (ρ₀ c₁ BD LD LV : ℝ) (θ : X → ℝ) (D : Fin r → ℝ → X → ℂ)
    (vh : ℝ → X → ℝ) (k : Fin r → ℕ) : Prop where
  c₁_pos : 0 < c₁
  ρ₀_pos : 0 < ρ₀
  ρ₀_le : ρ₀ ≤ 1
  hθ : ∀ᵐ x ∂μ, 0 ≤ θ x ∧ θ x ≤ 1
  hD : ∀ᵐ x ∂μ, ∀ j ρ, 0 ≤ ρ → ρ ≤ ρ₀ → ‖D j ρ x‖ ≤ BD ∧ ‖D j ρ x - D j 0 x‖ ≤ LD * ρ
  hv : ∀ᵐ x ∂μ, ∀ ρ, 0 ≤ ρ → ρ ≤ ρ₀ → c₁ ≤ vh ρ x ∧ |vh ρ x - vh 0 x| ≤ LV * ρ
  hk : ∀ j, 2 ≤ k j
  BD_nonneg : 0 ≤ BD
  LD_nonneg : 0 ≤ LD
  LV_nonneg : 0 ≤ LV
  hθm : Measurable θ
  hDm : ∀ j, Measurable fun y : ℝ × X => D j y.1 y.2
  hvm : Measurable fun y : ℝ × X => vh y.1 y.2

/-- The constant of the majorant. -/
noncomputable def sigK₀ (c₁ BD : ℝ) (k : Fin r → ℕ) : ℝ := ∑ j, BD * (c₁ ^ (k j - 2))⁻¹

/-- The constant of the Lipschitz bound. -/
noncomputable def sigK₁ (c₁ BD LD LV : ℝ) (k : Fin r → ℕ) : ℝ :=
  ∑ j, (LD * (c₁ ^ (k j - 2))⁻¹ + BD * k j * LV * (c₁ ^ (k j + 1 - 2))⁻¹)

variable {μ : Measure X} {ρ₀ c₁ BD LD LV : ℝ} {θ : X → ℝ} {D : Fin r → ℝ → X → ℂ}
  {vh : ℝ → X → ℝ} {k : Fin r → ℕ}

namespace SigData

variable (h : SigData μ ρ₀ c₁ BD LD LV θ D vh k)
include h

theorem sigM_nonneg (σ : ℝ) : ∀ᵐ x ∂μ, 0 ≤ sigM θ c₁ σ x := by
  filter_upwards [h.hθ] with x hx
  exact mul_nonneg hx.1 (inv_nonneg.mpr (sq_nonneg _))

theorem sigM_le {σ : ℝ} (hσ : 0 ≤ σ) : ∀ᵐ x ∂μ, sigM θ c₁ σ x ≤ (c₁ ^ 2)⁻¹ := by
  filter_upwards [h.hθ] with x hx
  have hc := h.c₁_pos
  have h1 : c₁ ≤ c₁ + θ x * σ := le_add_of_nonneg_right (mul_nonneg hx.1 hσ)
  calc θ x * ((c₁ + θ x * σ) ^ 2)⁻¹ ≤ 1 * (c₁ ^ 2)⁻¹ :=
        mul_le_mul hx.2 (inv_anti₀ (by positivity) (pow_le_pow_left₀ hc.le h1 2))
          (by positivity) zero_le_one
    _ = _ := one_mul _

theorem measurable_sigM (σ : ℝ) : Measurable (sigM θ c₁ σ) := by
  have := h.hθm
  unfold sigM
  fun_prop

theorem integrable_sigM [IsFiniteMeasure μ] {σ : ℝ} (hσ : 0 ≤ σ) :
    Integrable (sigM θ c₁ σ) μ :=
  Integrable.of_bound (h.measurable_sigM σ).aestronglyMeasurable _ (by
    filter_upwards [h.sigM_nonneg σ, h.sigM_le hσ] with x h0 h1
    rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)

/-- **The pointwise majorant.** -/
theorem norm_sigH_le : ∀ᵐ x ∂μ, ∀ ρ σ, 0 ≤ ρ → ρ ≤ ρ₀ → 0 ≤ σ →
    ‖sigH θ D vh k ρ σ x‖ ≤ sigK₀ c₁ BD k * sigM θ c₁ σ x := by
  filter_upwards [h.hθ, h.hD, h.hv] with x hθ hD hv
  intro ρ σ hρ hρ' hσ
  have hc := h.c₁_pos
  set c' := c₁ + θ x * σ
  have h1 : c₁ ≤ c' := le_add_of_nonneg_right (mul_nonneg hθ.1 hσ)
  have h2 : c' ≤ vh ρ x + θ x * σ := by linarith [(hv ρ hρ hρ').1]
  rw [sigH, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hθ.1, sigM, sigK₀]
  have hs : ‖∑ j, D j ρ x * (((vh ρ x + θ x * σ : ℝ) : ℂ) ^ k j)⁻¹‖ ≤
      ∑ j, BD * (c₁ ^ (k j - 2))⁻¹ * (c' ^ 2)⁻¹ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  · calc _ ≤ θ x * ∑ j, BD * (c₁ ^ (k j - 2))⁻¹ * (c' ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left hs hθ.1
      _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => by ring
  rw [norm_mul, norm_inv, norm_pow, norm_real, Real.norm_eq_abs,
    abs_of_pos (hc.trans_le (h1.trans h2)), mul_assoc]
  exact mul_le_mul (hD j ρ hρ hρ').1 (inv_pow_le_face hc h1 h2 (h.hk j))
    (inv_nonneg.mpr (pow_nonneg (hc.le.trans (h1.trans h2)) _))
    ((norm_nonneg _).trans (hD j ρ hρ hρ').1)

/-- **The pointwise Lipschitz bound.** -/
theorem norm_sigH_sub_le : ∀ᵐ x ∂μ, ∀ ρ σ, 0 ≤ ρ → ρ ≤ ρ₀ → 0 ≤ σ →
    ‖sigH θ D vh k ρ σ x - sigH θ D vh k 0 σ x‖ ≤ ρ * sigK₁ c₁ BD LD LV k * sigM θ c₁ σ x := by
  filter_upwards [h.hθ, h.hD, h.hv] with x hθ hD hv
  intro ρ σ hρ hρ' hσ
  have hc := h.c₁_pos
  set c' := c₁ + θ x * σ
  have h1 : c₁ ≤ c' := le_add_of_nonneg_right (mul_nonneg hθ.1 hσ)
  have hv1 : c' ≤ vh ρ x + θ x * σ := by linarith [(hv ρ hρ hρ').1]
  have hv0 : c' ≤ vh 0 x + θ x * σ := by linarith [(hv 0 le_rfl (h.ρ₀_pos.le)).1]
  rw [sigH, sigH, ← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg hθ.1, sigM, sigK₁]
  have hs : ‖∑ j, (D j ρ x * (((vh ρ x + θ x * σ : ℝ) : ℂ) ^ k j)⁻¹ -
      D j 0 x * (((vh 0 x + θ x * σ : ℝ) : ℂ) ^ k j)⁻¹)‖ ≤
      ∑ j, ρ * (LD * (c₁ ^ (k j - 2))⁻¹ + BD * k j * LV * (c₁ ^ (k j + 1 - 2))⁻¹) *
        (c' ^ 2)⁻¹ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  · calc _ ≤ θ x * ∑ j, ρ * (LD * (c₁ ^ (k j - 2))⁻¹ +
          BD * k j * LV * (c₁ ^ (k j + 1 - 2))⁻¹) * (c' ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left hs hθ.1
      _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => by ring
  have hd := norm_mul_inv_pow_sub_le (hc.trans_le h1) hv0 hv1 (hD j ρ hρ hρ').2
    (hD j 0 le_rfl h.ρ₀_pos.le).1 (by
      rw [show vh ρ x + θ x * σ - (vh 0 x + θ x * σ) = vh ρ x - vh 0 x by ring]
      exact (hv ρ hρ hρ').2) (k j)
  refine hd.trans ?_
  have hL := h.LD_nonneg
  have hB : 0 ≤ BD := (norm_nonneg _).trans (hD j 0 le_rfl h.ρ₀_pos.le).1
  have hLV := h.LV_nonneg
  have e1 := inv_pow_le_face hc h1 le_rfl (h.hk j)
  have e2 := inv_pow_le_face hc h1 le_rfl (show 2 ≤ k j + 1 by have := h.hk j; omega)
  have hk0 : (0 : ℝ) ≤ k j := Nat.cast_nonneg _
  calc ρ * (LD * (c' ^ k j)⁻¹ + BD * k j * LV * (c' ^ (k j + 1))⁻¹) ≤
      ρ * (LD * ((c₁ ^ (k j - 2))⁻¹ * (c' ^ 2)⁻¹) +
        BD * k j * LV * ((c₁ ^ (k j + 1 - 2))⁻¹ * (c' ^ 2)⁻¹)) := by
        gcongr
    _ = _ := by ring

theorem sigK₀_nonneg : 0 ≤ sigK₀ c₁ BD k :=
  Finset.sum_nonneg fun _ _ => mul_nonneg h.BD_nonneg (inv_nonneg.mpr (pow_nonneg h.c₁_pos.le _))

theorem sigK₁_nonneg : 0 ≤ sigK₁ c₁ BD LD LV k := by
  have hc := h.c₁_pos.le
  have := h.BD_nonneg
  have := h.LD_nonneg
  have := h.LV_nonneg
  exact Finset.sum_nonneg fun _ _ => by positivity

theorem measurable_sigH_uncurry :
    Measurable fun y : (ℝ × ℝ) × X => sigH θ D vh k y.1.1 y.1.2 y.2 := by
  have hθ : Measurable fun y : (ℝ × ℝ) × X => θ y.2 := h.hθm.comp measurable_snd
  have hD : ∀ j, Measurable fun y : (ℝ × ℝ) × X => D j y.1.1 y.2 := fun j =>
    (h.hDm j).comp (measurable_fst.fst.prodMk measurable_snd)
  have hv : Measurable fun y : (ℝ × ℝ) × X => vh y.1.1 y.2 :=
    h.hvm.comp (measurable_fst.fst.prodMk measurable_snd)
  unfold sigH
  refine (Complex.measurable_ofReal.comp hθ).mul
    (Finset.measurable_sum _ fun j _ => (hD j).mul ?_)
  exact ((Complex.measurable_ofReal.comp (hv.add (hθ.mul measurable_fst.snd))).pow_const _).inv

theorem measurable_sigH (ρ σ : ℝ) : Measurable (sigH θ D vh k ρ σ) :=
  h.measurable_sigH_uncurry.comp ((measurable_const (a := (ρ, σ))).prodMk measurable_id)

theorem integrable_sigH [IsFiniteMeasure μ] {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ ρ₀) (hσ : 0 ≤ σ) :
    Integrable (sigH θ D vh k ρ σ) μ :=
  Integrable.of_bound (h.measurable_sigH ρ σ).aestronglyMeasurable
    (sigK₀ c₁ BD k * (c₁ ^ 2)⁻¹) (by
      filter_upwards [h.norm_sigH_le, h.sigM_le hσ] with x h1 h2
      exact (h1 ρ σ hρ hρ' hσ).trans (mul_le_mul_of_nonneg_left h2 h.sigK₀_nonneg))

theorem integral_sigM_le_unif [IsFiniteMeasure μ] {σ : ℝ} (hσ : 0 ≤ σ) :
    ∫ x, sigM θ c₁ σ x ∂μ ≤ (c₁ ^ 2)⁻¹ * μ.real univ := by
  have := integral_mono_ae (h.integrable_sigM hσ) (integrable_const ((c₁ ^ 2)⁻¹))
    (h.sigM_le hσ)
  rwa [integral_const, smul_eq_mul, mul_comm] at this

theorem norm_integral_sigH_le [IsFiniteMeasure μ] {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ ρ₀)
    (hσ : 0 ≤ σ) :
    ‖∫ x, sigH θ D vh k ρ σ x ∂μ‖ ≤ sigK₀ c₁ BD k * ∫ x, sigM θ c₁ σ x ∂μ := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le ((h.integrable_sigM hσ).const_mul _) ?_
  filter_upwards [h.norm_sigH_le] with x hx using hx ρ σ hρ hρ' hσ

theorem norm_integral_sigH_sub_le [IsFiniteMeasure μ] {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ ρ₀)
    (hσ : 0 ≤ σ) :
    ‖∫ x, sigH θ D vh k ρ σ x ∂μ - ∫ x, sigH θ D vh k 0 σ x ∂μ‖ ≤
      ρ * sigK₁ c₁ BD LD LV k * ∫ x, sigM θ c₁ σ x ∂μ := by
  rw [← integral_sub (h.integrable_sigH hρ hρ' hσ) (h.integrable_sigH le_rfl h.ρ₀_pos.le hσ),
    ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((h.integrable_sigM hσ).const_mul _) ?_
  filter_upwards [h.norm_sigH_sub_le] with x hx using hx ρ σ hρ hρ' hσ

theorem norm_one_sub_pow_le {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ ρ₀) (q : ℕ) :
    ‖((((1 - ρ) ^ q : ℝ)) : ℂ)‖ ≤ 1 := by
  rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith [h.ρ₀_le]) _)]
  exact pow_le_one₀ (by linarith [h.ρ₀_le]) (by linarith)

theorem norm_sigG_le [IsFiniteMeasure μ] (q : ℕ) {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ ρ₀)
    (hσ : 0 ≤ σ) :
    ‖sigG μ q θ D vh k ρ σ‖ ≤ sigK₀ c₁ BD k * ∫ x, sigM θ c₁ σ x ∂μ := by
  rw [sigG, norm_mul]
  exact (mul_le_mul (h.norm_one_sub_pow_le hρ hρ' q) (h.norm_integral_sigH_le hρ hρ' hσ)
    (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul _))

theorem norm_sigG_le_unif [IsFiniteMeasure μ] (q : ℕ) {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ ρ₀)
    (hσ : 0 ≤ σ) :
    ‖sigG μ q θ D vh k ρ σ‖ ≤ sigK₀ c₁ BD k * ((c₁ ^ 2)⁻¹ * μ.real univ) :=
  (h.norm_sigG_le q hρ hρ' hσ).trans
    (mul_le_mul_of_nonneg_left (h.integral_sigM_le_unif hσ) h.sigK₀_nonneg)

theorem norm_sigG_sub_le [IsFiniteMeasure μ] (q : ℕ) {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ ρ₀)
    (hσ : 0 ≤ σ) :
    ‖sigG μ q θ D vh k ρ σ - sigG μ q θ D vh k 0 σ‖ ≤
      ρ * ((q * sigK₀ c₁ BD k + sigK₁ c₁ BD LD LV k) * ∫ x, sigM θ c₁ σ x ∂μ) := by
  set I₁ := ∫ x, sigH θ D vh k ρ σ x ∂μ
  set I₀ := ∫ x, sigH θ D vh k 0 σ x ∂μ
  have e : sigG μ q θ D vh k ρ σ - sigG μ q θ D vh k 0 σ =
      ((((1 - ρ) ^ q - 1 : ℝ)) : ℂ) * I₁ + (I₁ - I₀) := by
    simp only [sigG, sub_zero, one_pow, ofReal_one, one_mul, I₁, I₀]
    push_cast
    ring
  have hb : |(1 - ρ) ^ q - 1| ≤ q * ρ := by
    have h1 : (1 - ρ) ^ q ≤ 1 := pow_le_one₀ (by linarith [h.ρ₀_le]) (by linarith)
    have h2 := one_add_mul_le_pow (show -2 ≤ -ρ by linarith [h.ρ₀_le]) q
    rw [abs_of_nonpos (by linarith), ← sub_eq_add_neg] at *
    linarith
  have hI := h.integral_sigM_le_unif hσ
  have hM : 0 ≤ ∫ x, sigM θ c₁ σ x ∂μ := integral_nonneg_of_ae (h.sigM_nonneg σ)
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_real, Real.norm_eq_abs]
  have h1 := h.norm_integral_sigH_le hρ hρ' hσ
  have h2 := h.norm_integral_sigH_sub_le hρ hρ' hσ
  have hK₀ := h.sigK₀_nonneg
  calc |(1 - ρ) ^ q - 1| * ‖I₁‖ + ‖I₁ - I₀‖ ≤
      (q * ρ) * (sigK₀ c₁ BD k * ∫ x, sigM θ c₁ σ x ∂μ) +
        ρ * sigK₁ c₁ BD LD LV k * ∫ x, sigM θ c₁ σ x ∂μ :=
        add_le_add (mul_le_mul hb h1 (norm_nonneg _) (by positivity)) h2
    _ = _ := by ring

theorem measurable_sigG_uncurry (q : ℕ) [SFinite μ] :
    Measurable fun y : ℝ × ℝ => sigG μ q θ D vh k y.1 y.2 := by
  have hI : Measurable fun y : ℝ × ℝ => ∫ x, sigH θ D vh k y.1 y.2 x ∂μ :=
    (h.measurable_sigH_uncurry.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  unfold sigG
  exact (Complex.measurable_ofReal.comp ((measurable_const.sub measurable_fst).pow_const q)).mul hI

/-- **The face limit of the abstract face function, with rate `u^{-1/2}`.** -/
theorem norm_sigma_face_le [IsFiniteMeasure μ] (q : ℕ) {A : ℝ}
    (hA : ∀ σ, 0 < σ → ∫ x, sigM θ c₁ σ x ∂μ ≤ A * σ ^ (-(3 / 2) : ℝ)) {u : ℝ} (hu : 0 < u) :
    ‖u • (∫ ρ in (0 : ℝ)..ρ₀, sigG μ q θ D vh k ρ (ρ * u)) -
        ∫ σ in Ioi 0, sigG μ q θ D vh k 0 σ‖ ≤
      2 * A * ((q * sigK₀ c₁ BD k + sigK₁ c₁ BD LD LV k) * ρ₀ ^ (1 / 2 : ℝ) +
        sigK₀ c₁ BD k * ρ₀ ^ (-(1 / 2) : ℝ)) * u ^ (-(1 / 2) : ℝ) := by
  have hρ₀ := h.ρ₀_pos
  have hR : 0 < ρ₀ * u := mul_pos hρ₀ hu
  set K₀ := sigK₀ c₁ BD k
  set K₁ := q * K₀ + sigK₁ c₁ BD LD LV k
  have hK₀ : 0 ≤ K₀ := h.sigK₀_nonneg
  have hK₁ : 0 ≤ K₁ := add_nonneg (mul_nonneg (Nat.cast_nonneg _) hK₀) h.sigK₁_nonneg
  set Cu := K₀ * ((c₁ ^ 2)⁻¹ * μ.real univ)
  have hGm := h.measurable_sigG_uncurry q
  have hgi : IntervalIntegrable (fun σ => sigG μ q θ D vh k (σ / u) σ) volume 0 (ρ₀ * u) := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mpr
      (IntegrableOn.of_bound (by simp) ?_ Cu ?_)
    · exact (hGm.comp ((measurable_id.div_const u).prodMk measurable_id)).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun σ hσ => ?_
      exact h.norm_sigG_le_unif q (div_nonneg hσ.1.le hu.le) ((div_le_iff₀ hu).mpr hσ.2) hσ.1.le
  have hm0 : Measurable (sigG μ q θ D vh k 0) :=
    hGm.comp (measurable_const.prodMk measurable_id)
  have hg0 : IntegrableOn (sigG μ q θ D vh k 0) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    refine IntegrableOn.union (IntegrableOn.of_bound (by simp) hm0.aestronglyMeasurable Cu
      (ae_restrict_of_forall_mem measurableSet_Ioc fun σ hσ =>
        h.norm_sigG_le_unif q le_rfl hρ₀.le hσ.1.le)) ?_
    refine Integrable.mono' (((integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3 / 2) : ℝ) < -1)
      one_pos).const_mul A).const_mul K₀) hm0.aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun σ hσ => ?_
    exact (h.norm_sigG_le q le_rfl hρ₀.le (zero_le_one.trans hσ.le)).trans
      (mul_le_mul_of_nonneg_left (hA σ (one_pos.trans hσ)) hK₀)
  have hB : IntegrableOn (fun σ => K₀ * (A * σ ^ (-(3 / 2) : ℝ))) (Ioi (ρ₀ * u)) :=
    ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3 / 2) : ℝ) < -1) hR).const_mul A).const_mul K₀
  have hpow : ∀ σ : ℝ, 0 ≤ σ → σ * (K₁ * (A * σ ^ (-(3 / 2) : ℝ))) =
      K₁ * A * σ ^ (-(1 / 2) : ℝ) := by
    intro σ hσ
    rcases hσ.lt_or_eq with hσ | rfl
    · have := Real.rpow_add hσ 1 (-(3 / 2))
      rw [Real.rpow_one, show (1 : ℝ) + -(3 / 2) = -(1 / 2) by norm_num] at this
      rw [this]; ring
    · rw [Real.zero_rpow (by norm_num)]; ring
  have hB₁ : IntervalIntegrable (fun σ => σ * (K₁ * (A * σ ^ (-(3 / 2) : ℝ)))) volume 0 (ρ₀ * u) :=
    ((intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul
      (K₁ * A)).congr fun σ hσ => by
        rw [uIoc_of_le hR.le] at hσ
        exact (hpow σ hσ.1.le).symm
  refine (norm_face_sub_le_pos hρ₀ hu hgi hg0 hB hB₁ (fun σ hσ => ?_)
    (fun ρ σ hρ hρ' hσ => ?_)).trans (le_of_eq ?_)
  · exact (h.norm_sigG_le q le_rfl hρ₀.le hσ.le).trans
      (mul_le_mul_of_nonneg_left (hA σ hσ) hK₀)
  · refine (h.norm_sigG_sub_le q hρ hρ' hσ.le).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hA σ hσ) hK₁) hρ)
  · rw [intervalIntegral.integral_congr fun σ hσ => hpow σ (by
        rw [uIcc_of_le hR.le] at hσ; exact hσ.1), intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num)), integral_const_mul, integral_const_mul,
      integral_Ioi_rpow_neg_three_halves hR, Real.zero_rpow (by norm_num),
      Real.mul_rpow hρ₀.le hu.le, Real.mul_rpow hρ₀.le hu.le,
      Real.rpow_neg hu.le, Real.rpow_neg hρ₀.le]
    norm_num
    set w := u ^ (1 / 2 : ℝ) with hw
    have hw0 : w ≠ 0 := (Real.rpow_pos_of_pos hu _).ne'
    have hsq : u = w * w := by rw [hw, ← Real.rpow_add hu]; norm_num
    rw [hsq]
    field_simp

end SigData

end QED.GradedProof.RPi4

end
