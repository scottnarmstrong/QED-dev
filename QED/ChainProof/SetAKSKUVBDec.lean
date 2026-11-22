/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKUVBFub

/-!
# Set (a), stage D: the `VB` node difference split for its large-cutoff expansion

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification), step D3 (the photon-mass integral of the `VB` class). In the
coordinates `(ρ, β, w)` the photon-line coordinate is constant (`c₁ = 0`), so only the moments
`J1₀`, `J1₁`, `J2₁` enter, and the logarithm coefficient is `H₀ Y`, with
`H₀ = -32β(1 - β) + (1 - ρ) q`. The node difference `ksUDB` is split as

  `ksUDB = M + Q₁ + Q₂ + Q₃ + Q₄`,

* `M = (1 - ρ)⁻¹ f₀ log(1 + Λ(1 - ρ)/A(β))`, `f₀ = -16β(1 - β)Y`: the boundary layer at
  `ρ → 1`, whose `ρ`-integral is `f₀ K(Λ/A(β))`;
* `Q₁ = (1 - ρ)⁻¹ G₀ (J1₀(b₀) - J1₀(B))`, `Q₂ = (qY/2) log(1 + Λ(1 - ρ)R)`,
  `Q₃ = (1 - ρ)⁻¹ f₀ log((1 + Λ(1 - ρ)R)/(1 + Λ(1 - ρ)/A(β)))`,
  `Q₄ = ρc (K(BY/A) - K(b₀Y/A))`, `R = Y/(ρ((1 - ρ)A + ρA(β)Y))`.

Main result: **`ksU_ksUDB_split`**.
-/

@[expose] public section

open MeasureTheory Set

namespace QED.ChainProof.SetAKS

/-- `f₀ = -16β(1 - β)Y`: the logarithm coefficient at `ρ = 1`. -/
noncomputable def ksUf0 (β w : ℝ) : ℝ := -16 * β * (1 - β) * ksDYmax β w

/-- The slope of `H₀` in `x₂ = 1 - ρ`: `H₀ = -32β(1 - β) + (1 - ρ) q`. -/
def ksUq (ρ β w : ℝ) : ℝ :=
  -32 * w + 32 * (1 - ρ) * w * (w - 1) + 32 * (2 * w - 1) * ((1 - β) + (1 - ρ) * (β - w)) -
    32 * (β - w) + 32 * (β - w) * (2 * (1 - β) + (1 - ρ) * (β - w))

/-- `R = Y/(ρ((1 - ρ)A + ρA(β)Y))`. -/
noncomputable def ksUR (M s ρ β w : ℝ) : ℝ :=
  ksDYmax β w / (ρ * ((1 - ρ) * ksDA M s w + ρ * ksDA M s β * ksDYmax β w))

/-- The boundary-layer model `M`. -/
noncomputable def ksUMd (M s Λ ρ β w : ℝ) : ℝ :=
  (1 - ρ)⁻¹ * ksUf0 β w * Real.log (1 + Λ * (1 - ρ) / ksDA M s β)

/-- `G₀ = E₀ - H₀ A/2`. -/
noncomputable def ksUG0 (M s ρ β w : ℝ) : ℝ :=
  ksUGc (ksDA M s w) (ksDEc M (ksUPtB ρ β) w) (ksDHc (ksUPtB ρ β) w) 0

/-- `Q₁`: the moment part. -/
noncomputable def ksUQ1 (M s Λ ρ β w : ℝ) : ℝ :=
  (1 - ρ)⁻¹ * ksUG0 M s ρ β w * (ksDJ1 (ksDA M s w) (ksDbB M 0 (ksUPtB ρ β) s) (ksDYmax β w) 0 -
    ksDJ1 (ksDA M s w) (ksDbB M Λ (ksUPtB ρ β) s) (ksDYmax β w) 0)

/-- `Q₂`: the regular logarithm part. -/
noncomputable def ksUQ2 (M s Λ ρ β w : ℝ) : ℝ :=
  ksUq ρ β w * ksDYmax β w / 2 * Real.log (1 + Λ * (1 - ρ) * ksUR M s ρ β w)

/-- `Q₃`: the correction of the boundary-layer model. -/
noncomputable def ksUQ3 (M s Λ ρ β w : ℝ) : ℝ :=
  (1 - ρ)⁻¹ * ksUf0 β w * Real.log ((1 + Λ * (1 - ρ) * ksUR M s ρ β w) /
    (1 + Λ * (1 - ρ) / ksDA M s β))

/-- `Q₄`: the dilogarithm part. -/
noncomputable def ksUQ4 (M s Λ ρ β w : ℝ) : ℝ :=
  ρ * ksUcB w * (ksUK (ksDbB M Λ (ksUPtB ρ β) s * ksDYmax β w / ksDA M s w) -
    ksUK (ksDbB M 0 (ksUPtB ρ β) s * ksDYmax β w / ksDA M s w))

theorem ksU_ksDEc_ptB_hi {M ρ β w : ℝ} (hρ : ρ ≠ 0) :
    ksDEc M (ksUPtB ρ β) w 1 = 0 ∧ ksDEc M (ksUPtB ρ β) w 2 = 0 := by
  simp [ksDEc, ksDcv, ksU_ksDc1_ptB hρ]

theorem ksU_ksDHc_ptB_hi {ρ β w : ℝ} (hρ : ρ ≠ 0) :
    ksDHc (ksUPtB ρ β) w 1 = 0 ∧ ksDHc (ksUPtB ρ β) w 2 = 0 := by
  simp [ksDHc, ksDcv, ksU_ksDc1_ptB hρ]

theorem ksU_ksDHc_ptB_zero (ρ β w : ℝ) :
    ksDHc (ksUPtB ρ β) w 0 = -32 * β * (1 - β) + (1 - ρ) * ksUq ρ β w := by
  simp only [ksDHc, ksDcv, ksDc0, ksUPtB, ksUq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem ksU_log_ratio {M s Λ ρ β w : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s)
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hβ : β ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) (hΛ : 0 ≤ Λ) :
    Real.log (ksDA M s w + ksDbB M Λ (ksUPtB ρ β) s * ksDYmax β w) -
      Real.log (ksDA M s w + ksDbB M 0 (ksUPtB ρ β) s * ksDYmax β w) =
      Real.log (1 + Λ * (1 - ρ) * ksUR M s ρ β w) := by
  have hA := ksD_ksDA_pos hM hs (Ioo_subset_Icc_self hw)
  have hAb := ksD_ksDA_pos hM hs (Ioo_subset_Icc_self hβ)
  have hY := ksU_ksDYmax_pos hβ hw
  have hb₀ := ksU_ksDbB_zero_pos hM hs hρ hβ
  have hB := ksU_ksDbB_ptB_pos hM hs hρ hβ hΛ
  have h1 : 0 < 1 - ρ := by linarith [hρ.2]
  have hρ0 := hρ.1
  rw [← Real.log_div (by positivity) (by positivity)]
  congr 1
  rw [ksU_ksDbB_ptB hρ, ksU_ksDbB_zero_ptB hρ, ksUR]
  have hD : 0 < (1 - ρ) * ksDA M s w + ρ * ksDA M s β * ksDYmax β w := by positivity
  field_simp
  ring

/-- **The split of the `VB` node difference.** -/
theorem ksU_ksUDB_split {M s Λ ρ β w : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s)
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hβ : β ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) (hΛ : 0 ≤ Λ) :
    ksUDB M s Λ ρ β w = ksUMd M s Λ ρ β w + ksUQ1 M s Λ ρ β w + ksUQ2 M s Λ ρ β w +
      ksUQ3 M s Λ ρ β w + ksUQ4 M s Λ ρ β w := by
  have hρ0 := hρ.1
  have h1 : 0 < 1 - ρ := by linarith [hρ.2]
  obtain ⟨e1, e2⟩ := ksU_ksDEc_ptB_hi (M := M) (β := β) (w := w) hρ0.ne'
  obtain ⟨g1, g2⟩ := ksU_ksDHc_ptB_hi (β := β) (w := w) hρ0.ne'
  have hlog := ksU_log_ratio hM hs hρ hβ hw hΛ
  have hAb := ksD_ksDA_pos hM hs (Ioo_subset_Icc_self hβ)
  have hR : 0 ≤ Λ * (1 - ρ) * ksUR M s ρ β w := by
    have := ksD_ksDA_pos hM hs (Ioo_subset_Icc_self hw)
    have := ksU_ksDYmax_pos hβ hw
    unfold ksUR; positivity
  have hm : 0 < 1 + Λ * (1 - ρ) / ksDA M s β := by positivity
  have hlq : Real.log ((1 + Λ * (1 - ρ) * ksUR M s ρ β w) / (1 + Λ * (1 - ρ) / ksDA M s β)) =
      Real.log (1 + Λ * (1 - ρ) * ksUR M s ρ β w) - Real.log (1 + Λ * (1 - ρ) / ksDA M s β) :=
    Real.log_div (by positivity) hm.ne'
  simp only [ksUDB, ksUDg, ksUMd, ksUQ1, ksUQ2, ksUQ3, ksUQ4, ksUG0]
  rw [ksU_ksUPsiB_sub, hlog, hlq]
  simp only [ksUGc, ksUPY, e1, e2, g1, g2, ksU_ksDHc_ptB_zero, ksU_ksUtB_eq, ksUf0]
  field_simp
  ring

end QED.ChainProof.SetAKS

end
