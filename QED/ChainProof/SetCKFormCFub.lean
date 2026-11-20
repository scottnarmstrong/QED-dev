/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKCornInFub
public import QED.ChainProof.SetCKFormCS
public import QED.ChainProof.SetCKCoordInt

/-!
# Set (c), Stage K, closed forms: the inner corner node integral in threshold coordinates

Helper level (no frozen statement). Second step of the closed form of `ρ_C` (`rhoCornIn`). For
almost every outer node `X ∈ (0, 1)` the cube section of the kernel `cornInKer` is integrable
(`ae_integrable_cornInKer`, from `integrable_cornInKerT`), so `σ_C(X)` (`cornInSig`) is the
integral over the triangle `T = {0 < y₃ < Y < X}` of the `x`-integral `formCHin` of the weight
(`cornInSig_eq_of_integrable`). In the threshold coordinates `(u, s)` of `SetCKCoordInt` and
with the `x`-integral in closed form at the threshold (`integral_cornInKt_x`):

**`cornInSig_ae_eq`**: for a.e. `X ∈ (0, 1)`,
`σ_C(X) = ∫₀^X [∫_{(s_lo(u), 1-u]} J₁ S(Ψ₁(u, s), s) ds + ∫_{(1-u, 1)} J₂ S(Ψ₂(u, s), s) ds] du`,

where `S(Y, y₃, s) = P(s) - (1 - s)²/4 + φ(max(s, x*))` (`formCS`), and the `u`-integrand is
integrable on `(0, X)`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- The `x`-integral of the inner corner weight at the node `(Y, y₃)` and outer node `X`. -/
noncomputable def formCHin (Y y3 X : ℝ) : ℝ :=
  ∫ x in Ioo (0 : ℝ) 1, cornInKt Y y3 x (cornInWX Y X)

/-- The closed form `S = P(s) - (1 - s)²/4 + φ(max(s, x*))` of the `x`-integral at threshold
`s` (`integral_cornInKt_x`). -/
noncomputable def formCS (Y y3 X s : ℝ) : ℝ :=
  formCPrim Y y3 (cornInWX Y X) s - (1 - s) ^ 2 / 4 + cornInPhi Y y3 (max s (cornInXs Y y3))

/-- Almost every node has an integrable cube section. -/
theorem ae_integrable_cornInKer :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      Integrable (fun p : ℝ × ℝ × ℝ => cornInKer p.1 p.2.1 p.2.2 X)
        ((volume.restrict (Ioo (0 : ℝ) 1)).prod
          ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) := by
  filter_upwards [(integrable_cornInKerT one_pos).prod_left_ae,
    ae_restrict_mem measurableSet_Ioo] with X hI hX
  have hw : 0 < setCKdQ X / (setCKQ X + 1) := by
    have := setCKdQ_pos hX
    have := setCKQ_nonneg ⟨hX.1.le, hX.2.le⟩
    positivity
  refine (hI.div_const (setCKdQ X / (setCKQ X + 1))).congr
    (Eventually.of_forall fun p => ?_)
  simp only [cornInKerT]
  exact mul_div_cancel_right₀ _ hw.ne'

theorem integral_cornInKer_x (Y y3 X : ℝ) :
    ∫ x in Ioo (0 : ℝ) 1, cornInKer Y y3 x X =
      if y3 < Y ∧ Y < X then formCHin Y y3 X else 0 := by
  unfold cornInKer formCHin
  split_ifs
  · rfl
  · exact integral_zero _ _

/-- **`σ_C` as a double integral** at a node with an integrable cube section. -/
theorem cornInSig_eq_of_integrable {X : ℝ}
    (hI : Integrable (fun p : ℝ × ℝ × ℝ => cornInKer p.1 p.2.1 p.2.2 X)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))))) :
    Integrable (fun q : ℝ × ℝ => if q.2 < q.1 ∧ q.1 < X then formCHin q.1 q.2 X else 0)
        ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) ∧
      cornInSig X = ∫ q, (if q.2 < q.1 ∧ q.1 < X then formCHin q.1 q.2 X else 0)
        ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1)
  set k : ℝ × ℝ × ℝ → ℝ := fun p => cornInKer p.1 p.2.1 p.2.2 X with hk
  have hP := measurePreserving_prodAssoc μ μ μ
  have hI' : Integrable (k ∘ MeasurableEquiv.prodAssoc) ((μ.prod μ).prod μ) :=
    (hP.integrable_comp_emb MeasurableEquiv.prodAssoc.measurableEmbedding).2 hI
  have hfib : ∀ q : ℝ × ℝ, ∫ x, (k ∘ MeasurableEquiv.prodAssoc) (q, x) ∂μ =
      if q.2 < q.1 ∧ q.1 < X then formCHin q.1 q.2 X else 0 :=
    fun q => integral_cornInKer_x q.1 q.2 X
  refine ⟨hI'.integral_prod_left.congr (Eventually.of_forall hfib), ?_⟩
  rw [cornInSig, ← hP.integral_comp' (g := k)]
  exact (integral_prod _ hI').trans (integral_congr_ae (Eventually.of_forall hfib))

/-- The `x`-integral at a point with threshold coordinates `p`. -/
theorem formCHin_eq {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) {q p : ℝ × ℝ} (h : CoordSpec X q p) :
    formCHin q.1 q.2 X = formCS q.1 q.2 X p.2 := by
  obtain ⟨⟨⟨-, hYX⟩, hz0, hzY⟩, hs, hw, -⟩ := h
  exact (integral_cornInKt_x hz0 hzY (hYX.trans hX.2) hs hw).2

/-- **`σ_C` in threshold coordinates**, for almost every outer node. -/
theorem cornInSig_ae_eq :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      IntegrableOn (fun u => (∫ s in Ioc (coordSLo X u) (1 - u),
          coordJ1 X u s * formCS (coordPsi1 X (u, s)).1 (coordPsi1 X (u, s)).2 X s) +
          ∫ s in Ioo (1 - u) 1,
            coordJ2 X u s * formCS (coordPsi2 X (u, s)).1 (coordPsi2 X (u, s)).2 X s)
        (Ioo 0 X) ∧
      cornInSig X = ∫ u in Ioo 0 X, ((∫ s in Ioc (coordSLo X u) (1 - u),
          coordJ1 X u s * formCS (coordPsi1 X (u, s)).1 (coordPsi1 X (u, s)).2 X s) +
          ∫ s in Ioo (1 - u) 1,
            coordJ2 X u s * formCS (coordPsi2 X (u, s)).1 (coordPsi2 X (u, s)).2 X s) := by
  filter_upwards [ae_integrable_cornInKer, ae_restrict_mem measurableSet_Ioo] with X hI hX
  obtain ⟨hi, he⟩ := cornInSig_eq_of_integrable hI
  obtain ⟨hsq, hsq'⟩ := coord_integral_square hX (fun q => formCHin q.1 q.2 X)
  obtain ⟨hu, hue⟩ := coord_integral_eq hX (hsq.1 hi)
  have hfib : EqOn (fun u => (∫ s in Ioc (coordSLo X u) (1 - u),
        coordJ1 X u s * formCHin (coordPsi1 X (u, s)).1 (coordPsi1 X (u, s)).2 X) +
        ∫ s in Ioo (1 - u) 1,
          coordJ2 X u s * formCHin (coordPsi2 X (u, s)).1 (coordPsi2 X (u, s)).2 X)
      (fun u => (∫ s in Ioc (coordSLo X u) (1 - u),
        coordJ1 X u s * formCS (coordPsi1 X (u, s)).1 (coordPsi1 X (u, s)).2 X s) +
        ∫ s in Ioo (1 - u) 1,
          coordJ2 X u s * formCS (coordPsi2 X (u, s)).1 (coordPsi2 X (u, s)).2 X s)
      (Ioo 0 X) := by
    intro u hu
    simp only
    congr 1
    · refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
      simp only [formCHin_eq hX (coordPsi1_spec hX (p := (u, s)) ⟨hu, hs⟩)]
    · refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
      simp only [formCHin_eq hX (coordPsi2_spec hX (p := (u, s)) ⟨hu, hs⟩)]
  refine ⟨hu.congr_fun hfib measurableSet_Ioo, ?_⟩
  rw [he, hsq', hue]
  exact setIntegral_congr_fun measurableSet_Ioo hfib

end QED.ChainProof.SetCK

end
