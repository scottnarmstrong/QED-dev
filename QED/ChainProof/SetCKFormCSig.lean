/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormCB2

/-!
# Set (c), Stage K, closed forms: `σ_C` after the branch-1 `s`-integral

Helper level (no frozen statement). Combines `cornInSig_ae_eq` with the closed forms of the two
branch integrands (`coordJ1_mul_formCS`, `coordJ2_mul_formCS`) and the branch-1 `s`-integral
(`integral_formCF1`, on `(s_lo(u), 1 - u]` with `0 < s_lo(u) ≤ 1 - u`, `coordSLo_le`):

**`cornInSig_ae_eq_br`**: for a.e. `X ∈ (0, 1)`, with `Y = Y(u)` (`coordY1`),
`σ_C(X) = ∫₀^X [A₁(Y, u, 1 - u) - A₁(Y, u, s_lo(u)) + ∫_{(1-u, 1)} F₂(X, u, s) ds] du`,
the `u`-integrand being integrable on `(0, X)`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

theorem coordSLo_pos {X u : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo 0 X) :
    0 < coordSLo X u := by
  have := hX.1
  have : 0 < X - u := by linarith [hu.2]
  have : 0 < X + u - X * u := by nlinarith [hu.1, hX.2]
  have : 0 < 1 - X := by linarith [hX.2]
  have : 0 < X ^ 2 + (1 - X) * u := by nlinarith [hu.1]
  unfold coordSLo
  positivity

theorem coordSLo_le {X u : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo 0 X) :
    coordSLo X u ≤ 1 - u := by
  have : 0 < X ^ 2 + (1 - X) * u := by nlinarith [hu.1, hX.1, hX.2]
  unfold coordSLo
  rw [div_le_iff₀ this]
  nlinarith [hu.1, hX.2]

/-- **`σ_C` after the branch-1 `s`-integral**, for almost every outer node. -/
theorem cornInSig_ae_eq_br :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      IntegrableOn (fun u => formCA1 (coordY1 X u) u (1 - u) -
          formCA1 (coordY1 X u) u (coordSLo X u) + ∫ s in Ioo (1 - u) 1, formCF2 X u s)
        (Ioo 0 X) ∧
      cornInSig X = ∫ u in Ioo 0 X, (formCA1 (coordY1 X u) u (1 - u) -
          formCA1 (coordY1 X u) u (coordSLo X u) + ∫ s in Ioo (1 - u) 1, formCF2 X u s) := by
  filter_upwards [cornInSig_ae_eq, ae_restrict_mem measurableSet_Ioo] with X hI hX
  obtain ⟨hi, he⟩ := hI
  have hfib : EqOn (fun u => (∫ s in Ioc (coordSLo X u) (1 - u),
        coordJ1 X u s * formCS (coordPsi1 X (u, s)).1 (coordPsi1 X (u, s)).2 X s) +
        ∫ s in Ioo (1 - u) 1,
          coordJ2 X u s * formCS (coordPsi2 X (u, s)).1 (coordPsi2 X (u, s)).2 X s)
      (fun u => formCA1 (coordY1 X u) u (1 - u) -
          formCA1 (coordY1 X u) u (coordSLo X u) + ∫ s in Ioo (1 - u) 1, formCF2 X u s)
      (Ioo 0 X) := by
    intro u hu
    simp only
    congr 1
    · rw [← integral_formCF1 _ _ (coordSLo_pos hX hu) (coordSLo_le hX hu)]
      exact setIntegral_congr_fun measurableSet_Ioc fun s hs =>
        coordJ1_mul_formCS hX (p := (u, s)) ⟨hu, hs⟩
    · exact setIntegral_congr_fun measurableSet_Ioo fun s hs =>
        coordJ2_mul_formCS hX (p := (u, s)) ⟨hu, hs⟩
  exact ⟨hi.congr_fun hfib measurableSet_Ioo,
    he.trans (setIntegral_congr_fun measurableSet_Ioo hfib)⟩

end QED.ChainProof.SetCK

end
