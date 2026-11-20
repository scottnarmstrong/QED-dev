/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormXF
public import QED.ChainProof.SetCKCrossTFub

/-!
# Set (c), Stage K, closed forms: the crossed weight `H_X` as a double integral

Helper level (no frozen statement). The G3 weight `H_X = crossTH` is a triple integral over the
cube `(Y, y₃, x)`. At almost every node `X ∈ (0, 1)` its kernel section is integrable (Fubini
on the integrable kernel `crossTKerT 1`, **`ae_integrable_crossTKer`**), and integrating out
`x` first (after reassociating the cube) gives

**`crossTH_ae_eq`**: for almost every `X ∈ (0, 1)`, `(Y, y₃) ↦ formXHin Y y₃ X` is integrable
on the square and `H_X(X) = ∫∫ formXHin Y y₃ X dY dy₃`, where
`formXHin Y y₃ X = 1{y₃ < Y < X} (∫₀¹ T(Y, y₃, x, w_Y(X)) dx)/(1 - Y)`.

The inner `x`-integral has the closed form `formXF` at any threshold `s` with
`w₀(s) = w_Y(X)` (**`formXHin_eq`**, from `integral_crossTT_x`).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- The `(Y, y₃)`-integrand of `H_X`: the kernel integrated over `x`. -/
noncomputable def formXHin (Y y3 X : ℝ) : ℝ :=
  if y3 < Y ∧ Y < X then (∫ x in Ioo (0 : ℝ) 1, crossTT Y y3 x (cornInWX Y X)) / (1 - Y)
  else 0

/-- Almost every node has an integrable kernel section. -/
theorem ae_integrable_crossTKer :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      Integrable (fun p : ℝ × ℝ × ℝ => crossTKer p.1 p.2.1 p.2.2 X)
        ((volume.restrict (Ioo (0 : ℝ) 1)).prod
          ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) := by
  filter_upwards [(integrable_crossTKerT one_pos).prod_left_ae,
    ae_restrict_mem measurableSet_Ioo] with X hI hX
  have hw : 0 < setCKdQ X / (setCKQ X + 1) ^ 2 := by
    have := setCKdQ_pos hX
    have := setCKQ_nonneg ⟨hX.1.le, hX.2.le⟩
    positivity
  refine (hI.div_const (setCKdQ X / (setCKQ X + 1) ^ 2)).congr
    (Eventually.of_forall fun p => ?_)
  simp only [crossTKerT]
  exact mul_div_cancel_right₀ _ hw.ne'

/-- The `x`-integral of the kernel is `formXHin`. -/
theorem integral_crossTKer_x (Y y3 X : ℝ) :
    ∫ x in Ioo (0 : ℝ) 1, crossTKer Y y3 x X = formXHin Y y3 X := by
  unfold crossTKer formXHin
  split_ifs
  · exact integral_div _ _
  · exact integral_zero _ _

/-- **`H_X` as a double integral** at a node with an integrable kernel section. -/
theorem crossTH_eq_of_integrable {X : ℝ}
    (hI : Integrable (fun p : ℝ × ℝ × ℝ => crossTKer p.1 p.2.1 p.2.2 X)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))))) :
    Integrable (fun q : ℝ × ℝ => formXHin q.1 q.2 X)
        ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) ∧
      crossTH X = ∫ q, formXHin q.1 q.2 X
        ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1)
  set k : ℝ × ℝ × ℝ → ℝ := fun p => crossTKer p.1 p.2.1 p.2.2 X with hk
  have hP := measurePreserving_prodAssoc μ μ μ
  have hI' : Integrable (k ∘ MeasurableEquiv.prodAssoc) ((μ.prod μ).prod μ) :=
    (hP.integrable_comp_emb MeasurableEquiv.prodAssoc.measurableEmbedding).2 hI
  have hfib : ∀ q : ℝ × ℝ, ∫ x, (k ∘ MeasurableEquiv.prodAssoc) (q, x) ∂μ =
      formXHin q.1 q.2 X := fun q => integral_crossTKer_x q.1 q.2 X
  refine ⟨hI'.integral_prod_left.congr (Eventually.of_forall hfib), ?_⟩
  rw [crossTH, ← hP.integral_comp' (g := k)]
  exact (integral_prod _ hI').trans (integral_congr_ae (Eventually.of_forall hfib))

/-- **`H_X` is a double integral for almost every node.** -/
theorem crossTH_ae_eq :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      Integrable (fun q : ℝ × ℝ => formXHin q.1 q.2 X)
          ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) ∧
        crossTH X = ∫ q, formXHin q.1 q.2 X
          ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  filter_upwards [ae_integrable_crossTKer] with X hI
  exact crossTH_eq_of_integrable hI

/-- **The inner integrand in closed form**, at any threshold `s` of `m = w_Y(X)`. -/
theorem formXHin_eq {Y y3 X s : ℝ} (h3 : 0 < y3) (h34 : y3 < Y) (hYX : Y < X) (hX : X < 1)
    (hs : s ∈ Ioo (0 : ℝ) 1) (hm : cornInW0 Y y3 s = cornInWX Y X) :
    formXHin Y y3 X = formXF Y y3 (cornInWX Y X) s / (1 - Y) := by
  simp only [formXHin, h34, hYX, and_self, ↓reduceIte]
  rw [(integral_crossTT_x h3 h34 (hYX.trans hX) hs hm).2]

end QED.ChainProof.SetCK

end
