/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKSSpec
public import QED.ChainProof.SetAKSKSRho

/-!
# R-KS, stage S: the target spectral density by derivatives

Helper level for the identification (R-KS) of the regulator limit of the frozen goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` with the Källén–Sabry function (the open
input `SetAKSFix e`). The target spectral density `ρ_L = ρ⁽⁴⁾ - (3/4) L ρ_D` (`ksSpecRho`) is
differentiable on `(0, 1)` with an explicit elementary derivative. Hence a candidate density
(the summed density of stage D) equals `ρ_L` on `(0, 1)` as soon as it has the same derivative
there and the same limit at `δ → 1⁻` (`t → ∞`).

Main results:

* `ksRhoDmDer`, `ksS_hasDerivAt_ksRhoDm`: `ρ_D' = (1-δ²)(1+3δ²)/(2δ²)`;
* `ksSpecRhoDer`, `ksS_hasDerivAt_ksSpecRho`: the derivative of `ρ_L`;
* `ksS_eqOn_ksSpecRho`: a density with derivative `ksSpecRhoDer L` on `(0, 1)` and the same
  limit at `1⁻` as `ρ_L` equals `ρ_L` on `(0, 1)`.
-/

@[expose] public section

open Real Filter Topology Set

namespace QED.ChainProof.SetAKS

/-- The derivative of `ρ_D`: `(1-δ²)(1+3δ²)/(2δ²)`. -/
noncomputable def ksRhoDmDer (δ : ℝ) : ℝ :=
  (1 - δ ^ 2) * (1 + 3 * δ ^ 2) / (2 * δ ^ 2)

theorem ksS_hasDerivAt_ksRhoDm {δ : ℝ} (hδ : δ ≠ 0) : HasDerivAt ksRhoDm (ksRhoDmDer δ) δ := by
  have hn : HasDerivAt (fun d : ℝ => (1 - d ^ 2) ^ 2) (-(4 * δ * (1 - δ ^ 2))) δ := by
    refine (((hasDerivAt_pow 2 δ).const_sub 1).fun_pow 2).congr_deriv ?_
    push_cast
    ring
  have hd : HasDerivAt (fun d : ℝ => 2 * d) 2 δ := by
    simpa using (hasDerivAt_id' δ).const_mul 2
  have h := (hn.fun_div hd (mul_ne_zero two_ne_zero hδ)).neg
  refine h.congr_deriv ?_
  simp only [ksRhoDmDer]
  field_simp
  ring

/-- The derivative of the target spectral density `ρ_L`. -/
noncomputable def ksSpecRhoDer (L δ : ℝ) : ℝ :=
  ksRhoDer δ - 3 / 4 * L * ksRhoDmDer δ

theorem ksS_hasDerivAt_ksSpecRho (L : ℝ) {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (ksSpecRho L) (ksSpecRhoDer L δ) δ :=
  (ksS_hasDerivAt_ksRho hδ).sub ((ksS_hasDerivAt_ksRhoDm hδ.1.ne').const_mul (3 / 4 * L))

/-- **Stage S by derivatives**: a density `ρ` with derivative `ksSpecRhoDer L` on `(0, 1)` and
`ρ - ρ_L → 0` at `1⁻` equals the target density `ρ_L` on `(0, 1)`. -/
theorem ksS_eqOn_ksSpecRho {ρ : ℝ → ℝ} {L : ℝ}
    (hρ : ∀ δ ∈ Ioo (0 : ℝ) 1, HasDerivAt ρ (ksSpecRhoDer L δ) δ)
    (hlim : Tendsto (fun δ => ρ δ - ksSpecRho L δ) (𝓝[<] 1) (𝓝 0)) :
    EqOn ρ (ksSpecRho L) (Ioo 0 1) :=
  ksS_eqOn_of_hasDerivAt hρ (fun _ hδ => ksS_hasDerivAt_ksSpecRho L hδ) hlim

end QED.ChainProof.SetAKS

end
