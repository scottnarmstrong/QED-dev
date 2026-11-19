/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKPairInt

/-!
# Set (c), Stage K, group G2: the node change of variables `w = (1-Y)(Q(X) - Q(Y))`

Helper level (no frozen statement). For a node `Y ∈ (0, 1)` the map
`w_Y(X) = (1-Y)(Q(X) - Q(Y))` (`cornInWX`) is a strictly increasing bijection of `(Y, 1)` onto
`(0, ∞)` with derivative `(1-Y) Q'(X)` (`cornInWX_image`). With `M = (1-Y)(Q(Y) + t)` one has
`M + w_Y(X) = (1-Y)(Q(X) + t)`, so a `w`-integral `∫₀^∞ k(w)/(M + w) dw` becomes the node integral
`∫_Y^1 k(w_Y(X)) Q'(X)/(Q(X) + t) dX` (**`cornIn_cv`**, integrability included).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

/-- The node map `w_Y(X) = (1-Y)(Q(X) - Q(Y))`. -/
noncomputable def cornInWX (Y X : ℝ) : ℝ := (1 - Y) * (setCKQ X - setCKQ Y)

section

variable {Y t : ℝ}

theorem cornInWX_pos (hY : Y ∈ Ioo (0 : ℝ) 1) {X : ℝ} (hX : X ∈ Ioo Y 1) :
    0 < cornInWX Y X :=
  mul_pos (by linarith [hY.2]) (sub_pos.2 (setCKQ_lt hY.1.le hX.1 hX.2))

theorem cornInWX_strictMonoOn (hY : Y ∈ Ioo (0 : ℝ) 1) : StrictMonoOn (cornInWX Y) (Ioo Y 1) :=
  fun a ha b hb hab => by
    have h1 : 0 < 1 - Y := by linarith [hY.2]
    have := setCKQ_lt (hY.1.le.trans ha.1.le) hab hb.2
    unfold cornInWX
    nlinarith

theorem hasDerivAt_cornInWX {X : ℝ} (hX : X < 1) :
    HasDerivAt (cornInWX Y) ((1 - Y) * setCKdQ X) X :=
  ((hasDerivAt_setCKQ hX).sub_const (setCKQ Y)).const_mul (1 - Y)

/-- `w_Y` maps `(Y, 1)` onto `(0, ∞)`. -/
theorem cornInWX_image (hY : Y ∈ Ioo (0 : ℝ) 1) : cornInWX Y '' Ioo Y 1 = Ioi 0 := by
  refine Subset.antisymm ?_ fun w hw => ?_
  · rintro _ ⟨X, hX, rfl⟩
    exact cornInWX_pos hY hX
  have h1 : 0 < 1 - Y := by linarith [hY.2]
  have hev : ∀ᶠ X in 𝓝[<] (1 : ℝ), Y < X ∧ w / (1 - Y) < setCKQ X - setCKQ Y :=
    Filter.Eventually.and (Ioo_mem_nhdsLT hY.2)
      ((tendsto_setCKQ_sub_atTop Y).eventually_gt_atTop _) |>.mono fun X h => ⟨h.1.1, h.2⟩
  obtain ⟨b, hYb, hb⟩ := hev.exists
  have hb1 : b < 1 := by
    by_contra h
    push Not at h
    have h0 : setCKQ b - setCKQ Y ≤ 0 := by
      have : 1 - b ≤ 0 := by linarith
      have : setCKQ b ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg b) this
      linarith [setCKQ_nonneg ⟨hY.1.le, hY.2.le⟩]
    have : 0 < w / (1 - Y) := div_pos hw h1
    linarith
  have hcont : ContinuousOn (cornInWX Y) (Icc Y b) := fun X hX =>
    (hasDerivAt_cornInWX (lt_of_le_of_lt hX.2 hb1)).continuousAt.continuousWithinAt
  have hwb : w < cornInWX Y b := by
    unfold cornInWX
    rw [div_lt_iff₀ h1] at hb
    linarith
  have hw0 : cornInWX Y Y = 0 := by simp [cornInWX]
  obtain ⟨X, hX, hXw⟩ := intermediate_value_Ioo hYb.le hcont ⟨by rw [hw0]; exact hw, hwb⟩
  exact ⟨X, ⟨hX.1, hX.2.trans hb1⟩, hXw⟩

/-- **The node change of variables** `w = w_Y(X)`, with integrability. -/
theorem cornIn_cv (hY : Y ∈ Ioo (0 : ℝ) 1) (f : ℝ → ℝ) :
    (IntegrableOn f (Ioi 0) ↔
      IntegrableOn (fun X => (1 - Y) * setCKdQ X * f (cornInWX Y X)) (Ioo Y 1)) ∧
      ∫ w in Ioi 0, f w = ∫ X in Ioo Y 1, (1 - Y) * setCKdQ X * f (cornInWX Y X) := by
  have hd : ∀ X ∈ Ioo Y 1, HasDerivWithinAt (cornInWX Y) ((1 - Y) * setCKdQ X) (Ioo Y 1) X :=
    fun X hX => (hasDerivAt_cornInWX hX.2).hasDerivWithinAt
  have hinj := (cornInWX_strictMonoOn hY).injOn
  have habs : ∀ X ∈ Ioo Y 1, |(1 - Y) * setCKdQ X| = (1 - Y) * setCKdQ X := fun X hX =>
    abs_of_pos (mul_pos (by linarith [hY.2]) (setCKdQ_pos ⟨hY.1.trans hX.1, hX.2⟩))
  have hI := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hd hinj f
  have hE := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hinj f
  rw [cornInWX_image hY] at hI hE
  refine ⟨hI.trans ⟨fun h => ?_, fun h => ?_⟩, hE.trans ?_⟩
  · refine h.congr_fun (fun X hX => ?_) measurableSet_Ioo
    simp only [smul_eq_mul, habs X hX]
  · refine h.congr_fun (fun X hX => ?_) measurableSet_Ioo
    simp only [smul_eq_mul, habs X hX]
  · refine setIntegral_congr_fun measurableSet_Ioo fun X hX => ?_
    simp only [smul_eq_mul, habs X hX]

/-- `M + w_Y(X) = (1-Y)(Q(X) + t)` with `M = (1-Y)(Q(Y) + t)`. -/
theorem cornInWX_add (Y t X : ℝ) :
    (1 - Y) * (setCKQ Y + t) + cornInWX Y X = (1 - Y) * (setCKQ X + t) := by
  unfold cornInWX
  ring

/-- The node form of a `w`-integrand: `(1-Y) Q'(X) k(w)/(M + w) = k(w) Q'(X)/(Q(X) + t)`. -/
theorem cornIn_cv_integrand (hY : Y < 1) (ht : 0 < t) {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1)
    (k : ℝ) :
    (1 - Y) * setCKdQ X * (k / ((1 - Y) * (setCKQ Y + t) + cornInWX Y X)) =
      k * (setCKdQ X / (setCKQ X + t)) := by
  rw [cornInWX_add]
  have h1 : 1 - Y ≠ 0 := by linarith
  have h2 : setCKQ X + t ≠ 0 := by
    have := setCKQ_nonneg ⟨hX.1.le, hX.2.le⟩
    linarith
  field_simp

end

end QED.ChainProof.SetCK

end
