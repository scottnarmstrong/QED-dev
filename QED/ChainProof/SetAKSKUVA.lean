/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKUAsym
public import QED.ChainProof.SetAKSKUBnd

/-!
# Set (a), stage D: the photon-mass integral of one `VA` node

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification), step D3 (the photon-mass integral). At a node `(x, σ)` of the
`VA` class the photon mass² `u` enters `ksDYA M u x s σ` only through the slope
`ksDb M u x = b₀ + u/x`, `b₀ = ksDb M 0 x = M²x/(1 - x) > 0`, so the weight `x⁻¹` is the
Jacobian `db/du` and the cutoff integral is a difference of the antiderivative `ksUPhi`:

  `∫_a^Λ x⁻¹ ksDYA M u x s σ du = ksUPhi(ksDb M Λ x) - ksUPhi(ksDb M a x)`  (`0 ≤ a ≤ Λ`).

Main results:

* `ksU_ksDb_eq`, `ksU_ksDb_pos`: `ksDb M u x = u/x + ksDb M 0 x > 0` for `u ≥ 0`;
* **`ksU_integral_ksDYA`**: the cutoff photon-mass integral of one `VA` node.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral

namespace QED.ChainProof.SetAKS

theorem ksU_ksDb_eq (M u x : ℝ) : ksDb M u x = u / x + ksDb M 0 x := by
  simp only [ksDb]
  ring

theorem ksU_ksDb_zero {M x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : ksDb M 0 x = M ^ 2 * x / (1 - x) := by
  have h1x : 1 - x ≠ 0 := by linarith [hx.2]
  simp only [ksDb, zero_div, add_zero]
  field_simp
  ring

theorem ksU_ksDb_pos {M u x : ℝ} (hM : 0 < M) (hx : x ∈ Ioo (0 : ℝ) 1) (hu : 0 ≤ u) :
    0 < ksDb M u x := by
  rw [ksU_ksDb_eq, ksU_ksDb_zero hx]
  have h1x : 0 < 1 - x := by linarith [hx.2]
  have : 0 < M ^ 2 * x / (1 - x) := by have := hx.1; positivity
  have : 0 ≤ u / x := div_nonneg hu hx.1.le
  linarith

/-- **The cutoff photon-mass integral of one `VA` node**: for `M > 0`, `s > -4M²`,
`x ∈ (0, 1)`, `σ ∈ [0, 1)` and `0 ≤ a ≤ Λ`,
`∫_a^Λ x⁻¹ ksDYA M u x s σ du = ksUPhi(ksDb M Λ x) - ksUPhi(ksDb M a x)` (at the node's
`A = ksDA M s σ`, `Y = 1 - σ`, `a₀ = ksDa0 M x s σ`, `a₁ = ksDa1 x σ`). -/
theorem ksU_integral_ksDYA {M s x σ a Λ : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hσ : σ ∈ Ico (0 : ℝ) 1) (ha : 0 ≤ a) (haΛ : a ≤ Λ) :
    ∫ u in a..Λ, x⁻¹ * ksDYA M u x s σ =
      ksUPhi (ksDA M s σ) (ksDb M Λ x) (1 - σ) (ksDa0 M x s σ) (ksDa1 x σ) -
        ksUPhi (ksDA M s σ) (ksDb M a x) (1 - σ) (ksDa0 M x s σ) (ksDa1 x σ) := by
  have hx0 := hx.1
  have hA := ksD_ksDA_pos hM hs (Ico_subset_Icc_self hσ)
  have hY : 0 < 1 - σ := by linarith [hσ.2]
  set d := ksDb M 0 x with hd
  have hsub : ∫ u in a..Λ, x⁻¹ * ksDYA M u x s σ =
      x⁻¹ * (x • ∫ b in a / x + d..Λ / x + d,
        ksDLin (ksDA M s σ) b (1 - σ) (ksDa0 M x s σ) (ksDa1 x σ)) := by
    rw [intervalIntegral.integral_const_mul, ← intervalIntegral.integral_comp_div_add
      (f := fun b => ksDLin (ksDA M s σ) b (1 - σ) (ksDa0 M x s σ) (ksDa1 x σ)) hx0.ne' d]
    simp only [ksDYA, ← ksU_ksDb_eq, hd]
  rw [hsub, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hx0.ne', one_mul,
    ksU_integral_ksDLin _ _ hA (by rw [← ksU_ksDb_eq]; exact ksU_ksDb_pos hM hx ha)
      (by gcongr) hY, ← ksU_ksDb_eq, ← ksU_ksDb_eq]

end QED.ChainProof.SetAKS

end
