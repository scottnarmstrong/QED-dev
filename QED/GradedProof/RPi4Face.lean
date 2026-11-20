/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# (R-Π₄) step L6d2: the face limit of a heavy-photon sector

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d2 (model-free).
In the sector `ρ ≤ ρ₀` of a logarithmic subgraph (`ρ` the weight of the subgraph block in the
join coordinates), the heavy-photon density times `u` is `u ∫₀^{ρ₀} g(ρ, ρ u) dρ`, where the
integrand depends on `u` only through `σ = ρ u`. Substituting `σ = ρ u` gives
`∫₀^{ρ₀ u} g(σ/u, σ) dσ`, which tends to the **face integral** `∫₀^∞ g(0, σ) dσ`:

* `smul_integral_comp_face`: `u ∫₀^{ρ₀} g(ρ, ρ u) dρ = ∫₀^{ρ₀ u} g(σ/u, σ) dσ`;
* `norm_face_sub_le`: with a majorant `‖g(0, σ)‖ ≤ B(σ)` and a Lipschitz bound
  `‖g(ρ, σ) - g(0, σ)‖ ≤ ρ B₁(σ)`,
  `‖u ∫₀^{ρ₀} g(ρ, ρ u) dρ - ∫₀^∞ g(0, σ) dσ‖ ≤ u⁻¹ ∫₀^{ρ₀ u} σ B₁(σ) dσ + ∫_{ρ₀ u}^∞ B`.
-/

@[expose] public section

open MeasureTheory Set

namespace QED.GradedProof.RPi4

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The substitution `σ = ρ u`** in a sector integral. -/
theorem smul_integral_comp_face (g : ℝ → ℝ → E) {ρ₀ u : ℝ} (hu : 0 < u) :
    u • ∫ ρ in (0 : ℝ)..ρ₀, g ρ (ρ * u) = ∫ σ in (0 : ℝ)..ρ₀ * u, g (σ / u) σ := by
  have h := intervalIntegral.integral_comp_mul_right (fun σ => g (σ / u) σ) (a := 0) (b := ρ₀)
    hu.ne'
  simp only [mul_div_cancel_right₀ _ hu.ne', zero_mul] at h
  rw [h, smul_smul, mul_inv_cancel₀ hu.ne', one_smul]

/-- **The face limit with a rate.** -/
theorem norm_face_sub_le {g : ℝ → ℝ → E} {B B₁ : ℝ → ℝ} {ρ₀ u : ℝ} (hρ₀ : 0 < ρ₀) (hu : 0 < u)
    (hgi : IntervalIntegrable (fun σ => g (σ / u) σ) volume 0 (ρ₀ * u))
    (hg0 : IntegrableOn (g 0) (Ioi 0)) (hB : IntegrableOn B (Ioi (ρ₀ * u)))
    (hB₁ : IntervalIntegrable (fun σ => σ * B₁ σ) volume 0 (ρ₀ * u))
    (hbd : ∀ σ, 0 ≤ σ → ‖g 0 σ‖ ≤ B σ)
    (hlip : ∀ ρ σ, 0 ≤ ρ → ρ ≤ ρ₀ → 0 ≤ σ → ‖g ρ σ - g 0 σ‖ ≤ ρ * B₁ σ) :
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
    refine (hlip _ _ hρ hρ' hσ.1.le).trans (le_of_eq ?_)
    rw [div_eq_inv_mul, mul_assoc]
  · refine (norm_integral_le_integral_norm _).trans ?_
    refine setIntegral_mono_on hg0R.norm hB measurableSet_Ioi fun σ hσ => ?_
    exact hbd σ (hR.le.trans (le_of_lt hσ))

end QED.GradedProof.RPi4

end
