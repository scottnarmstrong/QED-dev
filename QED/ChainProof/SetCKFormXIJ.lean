/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormXB2K

/-!
# Set (c), Stage K, closed forms: `I(X)` after the two inner integrals

Helper level (no frozen statement). Step 4 of route D for `ρ_X` (scratch `stageK/STATUS.md`,
session 24+). Combining `formXI_ae_eq_br` with the inner integrals `integral_formXKin1`
(branch 1, `s` inside) and `integral_formXKin2` (branch 2, `u` inside):

**`formXI_ae_eq_J`**: for almost every `X ∈ (0, 1)`, `formXJ1 X` is integrable on `(0, X)`,
`formXJ2 X` on `(1 - X, 1)`, and `I(X) = ∫₀^X formXJ1 X u du + ∫_{1-X}^1 formXJ2 X s ds`, with
`formXJ1 X u = A₁(Y(u), u, 1 - u) - A₁(Y(u), u, s_lo(u))` and
`formXJ2 X s = A(X) - A(1 - s)`, `A = formXPFA (formXk2 X s) X s`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

/-- The branch-1 `u`-integrand of `I(X)`. -/
noncomputable def formXJ1 (X u : ℝ) : ℝ :=
  formXA1 (coordY1 X u) u (1 - u) - formXA1 (coordY1 X u) u (coordSLo X u)

/-- The branch-2 `s`-integrand of `I(X)`. -/
noncomputable def formXJ2 (X s : ℝ) : ℝ :=
  formXPFA (formXk2 X s) X s X - formXPFA (formXk2 X s) X s (1 - s)

/-- **`I(X)` after the inner integrals**, for almost every `X`. -/
theorem formXI_ae_eq_J :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      IntegrableOn (formXJ1 X) (Ioo 0 X) ∧ IntegrableOn (formXJ2 X) (Ioo (1 - X) 1) ∧
        formXI X = (∫ u in Ioo 0 X, formXJ1 X u) + ∫ s in Ioo (1 - X) 1, formXJ2 X s := by
  filter_upwards [formXI_ae_eq_br, ae_restrict_mem measurableSet_Ioo] with X h hX
  obtain ⟨i1, i2, he⟩ := h
  have e1 : EqOn (fun u => ∫ s in Ioc (coordSLo X u) (1 - u), formXKin1 X u s) (formXJ1 X)
      (Ioo 0 X) := fun u hu => integral_formXKin1 hX hu
  have e2 : EqOn (fun s => ∫ u in Ioo (1 - s) X, formXKin2 X u s) (formXJ2 X)
      (Ioo (1 - X) 1) := fun s hs => integral_formXKin2 hX hs
  refine ⟨i1.congr_fun e1 measurableSet_Ioo, i2.congr_fun e2 measurableSet_Ioo, ?_⟩
  rw [he, setIntegral_congr_fun measurableSet_Ioo e1, setIntegral_congr_fun measurableSet_Ioo e2]

end QED.ChainProof.SetCK

end
