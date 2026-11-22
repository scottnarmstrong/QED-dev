/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWRhoU
public import QED.ChainProof.SetAKSKSSpec

/-!
# Set (a), stage D: the `VA` spectral density in closed form

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. The
spectral density of the `VA` class in the velocity `δ ∈ (0, 1)` (`T = 4/(1-δ²)`),

  `ρ_A(δ) = ∫₀¹ dx ∫_{σ₋}^{σ₊} dσ ksWnA x σ T - (1-δ²)/(4δ) (C̄(σ₋) + C̄(σ₊))`,

`σ± = (1 ± δ)/2`, `C̄(σ) = ∫₀¹ ksWCA x σ dx`, is elementary:

  `ρ_A(δ) = ksWRAv δ = ksWRAn δ - 3(1-δ²)²/(2δ)`,

`ksWRAn δ = 8/3 δ(δ²-3) log(8δ²) + P₋(δ) log(1-δ) - P₊(δ) log(1+δ) + R(δ)` (no dilogarithms).
The node part is computed with the `σ`-integral outside (`ksWR_integral_sigma_x`); the order of
the assembly (`x` outside) follows by Fubini from the integrability of the node density on the
square (hypothesis `hint` of `ksWR_rhoA_eq`). Consequently the density identity
`2ρ_A + ρ_B = 16ρ⁽⁴⁾ + 6ρ_D` is equivalent to `ρ_B = ksWRBv δ`, an explicit function with the
dilogarithms of `ρ⁽⁴⁾` (`ksWR_identity_iff`).

Main results:

* **`ksWR_integral_sigma_x`**: `∫_{σ₋}^{σ₊} ∫₀¹ ksWnA x σ T dx dσ = ksWRAn δ`;
* **`ksWR_threshold_eq`**: `(1-δ²)/(4δ)(C̄(σ₋) + C̄(σ₊)) = 3(1-δ²)²/(2δ)`;
* **`ksWR_rhoA_eq`**: `ρ_A(δ) = ksWRAv δ` in the form of the assembly;
* `ksWR_identity_iff`: the density identity as a value of `ρ_B`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology intervalIntegral

namespace QED.ChainProof.SetAKS

open QED.Chain

/-- **The `VA` spectral density in closed form**, `ρ_A(δ)`. -/
noncomputable def ksWRAv (δ : ℝ) : ℝ := ksWRAn δ - 3 * (1 - δ ^ 2) ^ 2 / (2 * δ)

/-- **The value of `ρ_B` forced by the density identity**:
`ρ_B = 16ρ⁽⁴⁾ + 6ρ_D - 2ρ_A`. -/
noncomputable def ksWRBv (δ : ℝ) : ℝ := 16 * ksRho δ + 6 * ksRhoDm δ - 2 * ksWRAv δ

variable {δ : ℝ}

theorem ksWR_a_pos (hδ : δ ∈ Ioo (0 : ℝ) 1) {σ : ℝ} (hσ : σ ∈ Ioo ((1 - δ) / 2) ((1 + δ) / 2)) :
    0 < ksDT 1 δ * (σ * (1 - σ)) - 1 := by
  obtain ⟨h0, h1⟩ := hδ
  have pD : 0 < 1 - δ ^ 2 := by nlinarith
  unfold ksDT
  rw [sub_pos, one_pow, mul_one, div_mul_eq_mul_div, one_lt_div pD]
  nlinarith [hσ.1, hσ.2]

theorem ksWR_sigma_mem (hδ : δ ∈ Ioo (0 : ℝ) 1) {σ : ℝ}
    (hσ : σ ∈ Ioo ((1 - δ) / 2) ((1 + δ) / 2)) : σ ∈ Ioo (0 : ℝ) 1 :=
  ⟨by linarith [hσ.1, hδ.2], by linarith [hσ.2, hδ.2]⟩

/-- The inner `x`-integral at a node above threshold. -/
theorem ksWR_integral_x (hδ : δ ∈ Ioo (0 : ℝ) 1) {σ : ℝ}
    (hσ : σ ∈ Ioo ((1 - δ) / 2) ((1 + δ) / 2)) :
    ∫ x in Ioo (0 : ℝ) 1, ksWnA x σ (ksDT 1 δ) =
      ksWRMx σ (ksDT 1 δ * (σ * (1 - σ)) - 1) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  exact ksWR_integral_ksWnAa (ksWR_sigma_mem hδ hσ) (ksWR_a_pos hδ hσ)

/-- **The node part of `ρ_A`, `σ` outside**:
`∫_{σ₋}^{σ₊} ∫₀¹ ksWnA x σ T dx dσ = ksWRAn δ`. -/
theorem ksWR_integral_sigma_x (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    ∫ σ in Ioo ((1 - δ) / 2) ((1 + δ) / 2), ∫ x in Ioo (0 : ℝ) 1, ksWnA x σ (ksDT 1 δ) =
      ksWRAn δ := by
  rw [setIntegral_congr_fun measurableSet_Ioo fun σ hσ => ksWR_integral_x hδ hσ,
    ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [hδ.1] : (1 - δ) / 2 ≤ (1 + δ) / 2)]
  exact ksWR_integral_ksWRMx hδ

/-- **The threshold part of `ρ_A`**: `(1-δ²)/(4δ)(C̄(σ₋) + C̄(σ₊)) = 3(1-δ²)²/(2δ)`. -/
theorem ksWR_threshold_eq (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    (1 - δ ^ 2) / (4 * δ) * ((∫ x in Ioo (0 : ℝ) 1, ksWCA x ((1 - δ) / 2)) +
      ∫ x in Ioo (0 : ℝ) 1, ksWCA x ((1 + δ) / 2)) = 3 * (1 - δ ^ 2) ^ 2 / (2 * δ) := by
  simp only [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ksWR_integral_ksWCA]
  have : δ ≠ 0 := hδ.1.ne'
  field_simp
  ring

/-- **`ρ_A` in closed form**, in the form of the assembly (`x` outside): given the integrability
of the node density on the square, `ρ_A(δ) = ksWRAv δ`. -/
theorem ksWR_rhoA_eq (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hint : Integrable (Function.uncurry fun x σ => ksWnA x σ (ksDT 1 δ))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo ((1 - δ) / 2) ((1 + δ) / 2))))) :
    (∫ x in Ioo (0 : ℝ) 1, ∫ σ in Ioo ((1 - δ) / 2) ((1 + δ) / 2), ksWnA x σ (ksDT 1 δ)) -
        (1 - δ ^ 2) / (4 * δ) * ((∫ x in Ioo (0 : ℝ) 1, ksWCA x ((1 - δ) / 2)) +
          ∫ x in Ioo (0 : ℝ) 1, ksWCA x ((1 + δ) / 2)) = ksWRAv δ := by
  rw [integral_integral_swap hint, ksWR_integral_sigma_x hδ, ksWR_threshold_eq hδ]
  rfl

/-- **The density identity as a value of `ρ_B`**: with `ρ_A = ksWRAv δ`,
`2ρ_A + ρ_B = 16ρ⁽⁴⁾ + 6ρ_D ↔ ρ_B = ksWRBv δ`. -/
theorem ksWR_identity_iff {ρA ρB : ℝ} (hA : ρA = ksWRAv δ) :
    2 * ρA + ρB = 16 * ksRho δ + 6 * ksRhoDm δ ↔ ρB = ksWRBv δ := by
  subst hA
  unfold ksWRBv
  constructor <;> intro h <;> linarith

end QED.ChainProof.SetAKS

end
