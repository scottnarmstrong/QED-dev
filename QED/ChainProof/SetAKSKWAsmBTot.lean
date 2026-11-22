/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWAsmBInt
public import QED.ChainProof.SetAKSKWAsmTot
public import QED.ChainProof.SetAKSKVScale

/-!
# Set (a), stage D: the dispersive form of the `VB` class

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. The
subtracted `VB` finite part at unit mass has the spectral form

  `ksUFB 1 s - ksUFB 1 0 = ∫₀¹ ksSpecKer(s, δ) ρ_B(δ) dδ`   (`s > -4`),   `ρ_B = ksWRhoB`.

Proof: integrate the node dispersion `ksWB_node_disp` (valid off the null set
`w(1-w) = β(1-β)`) over the unit cube, exchange the cube and spectral integrals by the joint
integrability `ksWB_integrable_VB_joint`, reorder the cube integral at a.e. `T > 4` to the
iterated integral in `β, w, ρ` (`ksWB_integral_cube_reorder`), and pass to the velocity by
`ksD_dispersion_eq_delta`; the density in the spectral variable `ksWBR` satisfies
`ksWBR (ksDT 1 δ) = ksWRhoB δ` by definition.

Main results:

* `ksWB_integral_cube_reorder`, `ksWB_ae_slice`;
* **`ksWB_VB_dispersion`**, **`ksWB_intervalIntegrable_VB`**.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.ChainProof.SetAKS

local notation "ksWBμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- Reordering an integral over the unit cube in `((ρ, β), w)` to the iterated integral in the
order `β, w, ρ`. -/
theorem ksWB_integral_cube_reorder {f : (ℝ × ℝ) × ℝ → ℝ}
    (hf : Integrable f (((ksWBμ).prod ksWBμ).prod ksWBμ)) :
    ∫ z, f z ∂(((ksWBμ).prod ksWBμ).prod ksWBμ) =
      ∫ β in Ioo (0 : ℝ) 1, ∫ w in Ioo (0 : ℝ) 1, ∫ ρ in Ioo (0 : ℝ) 1, f ((ρ, β), w) := by
  set e : (ℝ × ℝ) × ℝ ≃ᵐ (ℝ × ℝ) × ℝ := MeasurableEquiv.prodAssoc.trans MeasurableEquiv.prodComm
    with he
  have hmp : MeasurePreserving e (((ksWBμ).prod ksWBμ).prod ksWBμ)
      (((ksWBμ).prod ksWBμ).prod ksWBμ) :=
    (Measure.measurePreserving_swap (μ := ksWBμ) (ν := (ksWBμ).prod ksWBμ)).comp
      (measurePreserving_prodAssoc ksWBμ ksWBμ ksWBμ)
  set g : (ℝ × ℝ) × ℝ → ℝ := fun p => f ((p.2, p.1.1), p.1.2) with hg
  have hge : g ∘ e = f := by
    funext z
    rfl
  have hgi : Integrable g (((ksWBμ).prod ksWBμ).prod ksWBμ) := by
    rw [← hmp.integrable_comp_emb e.measurableEmbedding, hge]
    exact hf
  have h1 : ∫ z, f z ∂(((ksWBμ).prod ksWBμ).prod ksWBμ) =
      ∫ p, g p ∂(((ksWBμ).prod ksWBμ).prod ksWBμ) := by
    rw [← hmp.integral_comp' g]
    rfl
  rw [h1, integral_prod g hgi, integral_prod _ hgi.integral_prod_left]

/-- The `VB` density as a function of the spectral variable: the iterated node integral. -/
noncomputable def ksWBR (T : ℝ) : ℝ :=
  ∫ β in Ioo (0 : ℝ) 1, ∫ w in Ioo (0 : ℝ) 1, ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ β w T

theorem ksWB_ksWBR_ksDT (δ : ℝ) : ksWBR (ksDT 1 δ) = ksWRhoB δ := rfl

/-- At a.e. `T > 4` the cube integral of the node density is `ksWBR T`, and the exchanged
integrand is `ksWBR T · k_s(T)`. -/
theorem ksWB_ae_slice {s : ℝ} (hs : -4 < s) :
    ∀ᵐ T ∂(volume.restrict (Ioi (4 : ℝ))),
      ∫ z, ksWjB s (z, T) ∂(((ksWBμ).prod ksWBμ).prod ksWBμ) =
        ksWBR T / T * (s / (s + T)) := by
  have hint₁ := (ksWB_integrable_VB_joint (s := 1) (by norm_num)).prod_left_ae
  filter_upwards [hint₁, ae_restrict_mem measurableSet_Ioi] with T hT hT4
  have hT4' : 4 < T := hT4
  have hT0 : 0 < T := by linarith
  have hk : 1 / (T * (1 + T)) ≠ 0 := by positivity
  have hi : Integrable (fun z : (ℝ × ℝ) × ℝ => ksWnB z.1.1 z.1.2 z.2 T)
      (((ksWBμ).prod ksWBμ).prod ksWBμ) := by
    refine (hT.mul_const (1 / (T * (1 + T)))⁻¹).congr (Eventually.of_forall fun z => ?_)
    simp only [ksWjB]
    field_simp
  have e : (fun z => ksWjB s (z, T)) = fun z : (ℝ × ℝ) × ℝ =>
      ksWnB z.1.1 z.1.2 z.2 T * (s / (T * (s + T))) := rfl
  rw [e, integral_mul_const, ksWB_integral_cube_reorder hi]
  have : s + T ≠ 0 := by linarith
  simp only [ksWBR]
  field_simp

/-- **The dispersive form of the `VB` class** (unit mass, `s > -4`):
`F_B(1, s) - F_B(1, 0) = ∫₀¹ ksSpecKer(s, δ) ρ_B(δ) dδ`, `ρ_B = ksWRhoB`. -/
theorem ksWB_VB_dispersion {s : ℝ} (hs : -4 < s) :
    ksUFB 1 s - ksUFB 1 0 = ∫ δ in (0 : ℝ)..1, ksSpecKer s δ * ksWRhoB δ := by
  set ν := ((ksWBμ).prod ksWBμ).prod ksWBμ with hν
  have hs' : -(4 * (1 : ℝ) ^ 2) < s := by norm_num; linarith
  have ib := ksW_integrable_ksUb0 one_pos hs'
  have ib0 := ksW_integrable_ksUb0 one_pos (by norm_num : -(4 * (1 : ℝ) ^ 2) < 0)
  have hint := ksWB_integrable_VB_joint hs
  have hF : ksUFB 1 s - ksUFB 1 0 =
      ∫ z, (ksUb0 1 s z.1.1 z.1.2 z.2 - ksUb0 1 0 z.1.1 z.1.2 z.2) ∂ν := by
    rw [ksUFB, ksUFB, integral_sub ib ib0]
  have hnode : ∀ᵐ z ∂ν, ksUb0 1 s z.1.1 z.1.2 z.2 - ksUb0 1 0 z.1.1 z.1.2 z.2 =
      ∫ T in Ioi 4, ksWjB s (z, T) := by
    filter_upwards [Filter.Eventually.and ksU_ae_mem_cube ksWB_ae_ne_cube] with z hz
    exact (ksWB_node_disp hz.1.1 hz.1.2.1 hz.1.2.2 hz.2 hs).2
  rw [hF, integral_congr_ae hnode, integral_integral_swap (f := fun z T => ksWjB s (z, T)) hint,
    integral_congr_ae (ksWB_ae_slice hs)]
  have hD := ksD_dispersion_eq_delta one_pos ksWBR s
  simp only [one_pow, mul_one, div_one] at hD
  rw [hD]
  rfl

/-- **The `VB` integrand in the velocity is integrable.** -/
theorem ksWB_intervalIntegrable_VB {s : ℝ} (hs : -4 < s) :
    IntervalIntegrable (fun δ => ksSpecKer s δ * ksWRhoB δ) volume 0 1 := by
  have hint := ksWB_integrable_VB_joint hs
  have hR : IntegrableOn (fun t => ksWBR t / t * (s / (s + t))) (Ioi (4 * 1 ^ 2)) := by
    rw [show (4 : ℝ) * 1 ^ 2 = 4 by norm_num]
    exact hint.integral_prod_right.congr (ksWB_ae_slice hs)
  rw [← ksD_image_ksDT one_pos, integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioo (fun δ hδ => (ksD_hasDerivAt_ksDT 1 hδ).hasDerivWithinAt)
    (ksD_injOn_ksDT one_pos)] at hR
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  refine hR.congr_fun (fun δ hδ => ?_) measurableSet_Ioo
  simp only [smul_eq_mul]
  rw [ksW_ksDT_jac hδ, ksWB_ksWBR_ksDT]

end QED.ChainProof.SetAKS

end
