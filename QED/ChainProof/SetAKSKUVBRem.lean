/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKUVBDom

/-!
# Set (a), stage D: the `VB` remainder, its pointwise limit and its domination

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification), step D3 (the photon-mass integral of the `VB` class). After the
boundary-layer model of `ksU_ksUDB_split` is integrated in `ρ` (giving `f₀ K(Λ/A(β))`), the
`VB` node integrand becomes `ksUQs = Q₁ + Q₂ + Q₃ + Q₄ + f₀ K(Λ/A(β))`. Its remainder

  `ksUDr = ksUQs - b₂ (log Λ)² - b₁ log Λ`

converges pointwise on the open cube to `b₀` as `Λ → ∞` (`ksU_tendsto_ksUDr`), and is bounded,
uniformly in `Λ ≥ 1`, by a multiple of `ksUg ρ · ksUg w`.
-/

@[expose] public section

open Filter Topology MeasureTheory Set

namespace QED.ChainProof.SetAKS

/-- `ℓ₃ = log(Y/(ρA))`. -/
noncomputable def ksUl3 (M s ρ β w : ℝ) : ℝ := Real.log (ksDYmax β w / (ρ * ksDA M s w))

/-- The `(log Λ)²` density of the `VB` class. -/
noncomputable def ksUb2 (ρ β w : ℝ) : ℝ := ρ * ksUcB w / 2 + ksUf0 β w / 2

/-- The `log Λ` density of the `VB` class. -/
noncomputable def ksUb1 (M s ρ β w : ℝ) : ℝ :=
  ksUq ρ β w * ksDYmax β w / 2 + ρ * ksUcB w * ksUl3 M s ρ β w +
    ksUf0 β w * Real.log (ksDA M s β)⁻¹

/-- The finite part density of the `VB` class. -/
noncomputable def ksUb0 (M s ρ β w : ℝ) : ℝ :=
  (1 - ρ)⁻¹ * ksUG0 M s ρ β w *
      ksDJ1 (ksDA M s w) (ksDbB M 0 (ksUPtB ρ β) s) (ksDYmax β w) 0 +
    ksUq ρ β w * ksDYmax β w / 2 * Real.log ((1 - ρ) * ksUR M s ρ β w) +
    (1 - ρ)⁻¹ * ksUf0 β w * Real.log ((1 - ρ) * ksUR M s ρ β w / ((1 - ρ) / ksDA M s β)) +
    ρ * ksUcB w * (ksUl3 M s ρ β w ^ 2 / 2 + 2 * ksUK 1 -
      ksUK (ksDbB M 0 (ksUPtB ρ β) s * ksDYmax β w / ksDA M s w)) +
    ksUf0 β w * (Real.log (ksDA M s β)⁻¹ ^ 2 / 2 + 2 * ksUK 1)

/-- The `VB` node integrand after the `ρ`-integral of the boundary-layer model. -/
noncomputable def ksUQs (M s Λ ρ β w : ℝ) : ℝ :=
  ksUQ1 M s Λ ρ β w + ksUQ2 M s Λ ρ β w + ksUQ3 M s Λ ρ β w + ksUQ4 M s Λ ρ β w +
    ksUf0 β w * ksUK (Λ / ksDA M s β)

/-- The remainder of the `VB` node integrand. -/
noncomputable def ksUDr (M s Λ ρ β w : ℝ) : ℝ :=
  ksUQs M s Λ ρ β w - ksUb2 ρ β w * Real.log Λ ^ 2 - ksUb1 M s ρ β w * Real.log Λ

section Node

variable {M s ρ β w : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s) (hρ : ρ ∈ Ioo (0 : ℝ) 1)
  (hβ : β ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1)
include hM hs hρ hβ hw

theorem ksU_ksUR_pos : 0 < ksUR M s ρ β w := by
  have := ksD_ksDA_pos hM hs (Ioo_subset_Icc_self hw)
  have := ksD_ksDA_pos hM hs (Ioo_subset_Icc_self hβ)
  have := ksU_ksDYmax_pos hβ hw
  have := hρ.1
  have : 0 < 1 - ρ := by linarith [hρ.2]
  unfold ksUR; positivity

omit hβ in
/-- The remainder in pieces. -/
theorem ksU_ksUDr_eq (Λ : ℝ) :
    ksUDr M s Λ ρ β w = ksUQ1 M s Λ ρ β w +
      ksUq ρ β w * ksDYmax β w / 2 *
        (Real.log (1 + Λ * ((1 - ρ) * ksUR M s ρ β w)) - Real.log Λ) +
      ksUQ3 M s Λ ρ β w +
      ρ * ksUcB w * ((ksUK ((ρ * ksDbB M 0 (ksUPtB ρ β) s + Λ) *
          (ksDYmax β w / (ρ * ksDA M s w))) - Real.log Λ ^ 2 / 2 -
          ksUl3 M s ρ β w * Real.log Λ) -
        ksUK (ksDbB M 0 (ksUPtB ρ β) s * ksDYmax β w / ksDA M s w)) +
      ksUf0 β w * (ksUK ((0 + Λ) * (ksDA M s β)⁻¹) - Real.log Λ ^ 2 / 2 -
        Real.log (ksDA M s β)⁻¹ * Real.log Λ) := by
  have hρ0 := hρ.1
  have hA := ksD_ksDA_pos hM hs (Ioo_subset_Icc_self hw)
  have hB : ksDbB M Λ (ksUPtB ρ β) s * ksDYmax β w / ksDA M s w =
      (ρ * ksDbB M 0 (ksUPtB ρ β) s + Λ) * (ksDYmax β w / (ρ * ksDA M s w)) := by
    rw [ksU_ksDbB_ptB hρ]; field_simp
  have hK : (0 + Λ) * (ksDA M s β)⁻¹ = Λ / ksDA M s β := by ring
  simp only [ksUDr, ksUQs, ksUQ2, ksUQ4, ksUb2, ksUb1, hB, hK, mul_assoc]
  ring

/-- **The pointwise limit of the remainder.** -/
theorem ksU_tendsto_ksUDr :
    Tendsto (fun Λ => ksUDr M s Λ ρ β w) atTop (𝓝 (ksUb0 M s ρ β w)) := by
  have hρ0 := hρ.1
  have h1 : 0 < 1 - ρ := by linarith [hρ.2]
  have hA := ksD_ksDA_pos hM hs (Ioo_subset_Icc_self hw)
  have hAb := ksD_ksDA_pos hM hs (Ioo_subset_Icc_self hβ)
  have hY := ksU_ksDYmax_pos hβ hw
  have hb₀ := ksU_ksDbB_zero_pos hM hs hρ hβ
  have hR := ksU_ksUR_pos hM hs hρ hβ hw
  -- the pieces
  have t1 : Tendsto (fun Λ => ksUQ1 M s Λ ρ β w) atTop
      (𝓝 ((1 - ρ)⁻¹ * ksUG0 M s ρ β w *
        (ksDJ1 (ksDA M s w) (ksDbB M 0 (ksUPtB ρ β) s) (ksDYmax β w) 0 - 0))) := by
    have h := (ksU_tendsto_J1_zero hA hY.le hb₀ hρ0).const_sub
      (ksDJ1 (ksDA M s w) (ksDbB M 0 (ksUPtB ρ β) s) (ksDYmax β w) 0)
    refine (h.const_mul ((1 - ρ)⁻¹ * ksUG0 M s ρ β w)).congr' (Eventually.of_forall fun Λ => ?_)
    simp only [ksUQ1]
    rw [ksU_ksDbB_ptB (u := Λ) hρ]
  have t2 := (ksU_tendsto_log_sub (mul_pos h1 hR)).const_mul (ksUq ρ β w * ksDYmax β w / 2)
  have t3 : Tendsto (fun Λ => ksUQ3 M s Λ ρ β w) atTop (𝓝 ((1 - ρ)⁻¹ * ksUf0 β w *
      Real.log ((1 - ρ) * ksUR M s ρ β w / ((1 - ρ) / ksDA M s β)))) := by
    refine ((ksU_tendsto_log_ratio (mul_pos h1 hR) (div_pos h1 hAb)).const_mul
      ((1 - ρ)⁻¹ * ksUf0 β w)).congr' (Eventually.of_forall fun Λ => ?_)
    unfold ksUQ3
    ring_nf
  have t4 := ((ksU_tendsto_K_sub (t := ρ * ksDbB M 0 (ksUPtB ρ β) s)
    (div_pos hY (mul_pos hρ0 hA)) (by positivity)).sub_const
      (ksUK (ksDbB M 0 (ksUPtB ρ β) s * ksDYmax β w / ksDA M s w))).const_mul (ρ * ksUcB w)
  have t5 := (ksU_tendsto_K_sub (t := 0) (inv_pos.2 hAb) le_rfl).const_mul (ksUf0 β w)
  have ht := (((t1.add t2).add t3).add t4).add t5
  have e : ksUb0 M s ρ β w = (1 - ρ)⁻¹ * ksUG0 M s ρ β w *
        (ksDJ1 (ksDA M s w) (ksDbB M 0 (ksUPtB ρ β) s) (ksDYmax β w) 0 - 0) +
      ksUq ρ β w * ksDYmax β w / 2 * Real.log ((1 - ρ) * ksUR M s ρ β w) +
      (1 - ρ)⁻¹ * ksUf0 β w *
        Real.log ((1 - ρ) * ksUR M s ρ β w / ((1 - ρ) / ksDA M s β)) +
      ρ * ksUcB w * (Real.log (ksDYmax β w / (ρ * ksDA M s w)) ^ 2 / 2 + 2 * ksUK 1 -
        ksUK (ksDbB M 0 (ksUPtB ρ β) s * ksDYmax β w / ksDA M s w)) +
      ksUf0 β w * (Real.log (ksDA M s β)⁻¹ ^ 2 / 2 + 2 * ksUK 1) := by
    simp only [ksUb0, ksUl3, sub_zero]
  rw [e]
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
  rw [ksU_ksUDr_eq hM hs hρ hw Λ, ksUl3]

end Node

end QED.ChainProof.SetAKS

end
