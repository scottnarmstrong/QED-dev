/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWRhoBV
public import QED.ChainProof.SetAKSKWRhoBE2
public import QED.ChainProof.SetAKSKWRhoInt

/-!
# Set (a), stage D: the value of `ρ_B` and the density identity

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. On each
of the three ranges `(0, σ₋)`, `(σ₋, σ₊)`, `(σ₊, 1)` of the `β`-integral of `ρ_B`
(`σ± = (1 ± δ)/2`) the integrand `ksWWE · δ` is a `ksWYe` combination (`ksWY1_eqOn`,
`ksWY2_eqOn`, `ksWY3_eqOn`), hence integrable with the primitive value `ksWYv` (`ksWY_piece`).
The three values add up to `ksWRBv δ` (`ksWYv_total`). Hence `ρ_B(δ) = ksWRBv δ`, which is the
density identity `2ρ_A + ρ_B = 16ρ⁽⁴⁾ + 6ρ_D` on `(0, 1)`.

Main results:

* `ksWY_integral_ksWWE_eq`: `∫₀¹ ksWWE β δ dβ = ksWRBv δ`;
* `ksWY_ksWRhoB_eq_ksWRBv`: `ρ_B(δ) = ksWRBv δ`;
* **`ksWY_density_identity`**: `2ρ_A(δ) + ρ_B(δ) = 16ρ⁽⁴⁾(δ) + 6ρ_D(δ)` for `δ ∈ (0, 1)`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology intervalIntegral

namespace QED.ChainProof.SetAKS

open QED.Chain

variable {d : ℝ}

theorem ksWY_ksWWE_I {b : ℝ} (hb : b < (1 - d) / 2) : ksWWE b d = ksWWEI b d := by
  simp only [ksWWE, hb, ↓reduceIte]

theorem ksWY_ksWWE_II {b : ℝ} (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d) / 2)) :
    ksWWE b d = ksWWEII b d := by
  simp only [ksWWE, not_lt.2 hb.1.le, hb.2, ↓reduceIte]

theorem ksWY_ksWWE_III (hd : 0 ≤ d) {b : ℝ} (hb : (1 + d) / 2 < b) :
    ksWWE b d = ksWWEIII b d := by
  simp only [ksWWE, show ¬ b < (1 - d) / 2 by linarith, not_lt.2 hb.le, ↓reduceIte]

/-- **Assembly of the `β`-integral** from the three ranges. -/
theorem ksWY_integral_ksWWE {V₁ V₂ V₃ : ℝ}
    (h₁ : IntervalIntegrable (fun b => ksWWE b d) volume 0 ((1 - d) / 2) ∧
      ∫ b in (0 : ℝ)..((1 - d) / 2), ksWWE b d = V₁)
    (h₂ : IntervalIntegrable (fun b => ksWWE b d) volume ((1 - d) / 2) ((1 + d) / 2) ∧
      ∫ b in ((1 - d) / 2)..((1 + d) / 2), ksWWE b d = V₂)
    (h₃ : IntervalIntegrable (fun b => ksWWE b d) volume ((1 + d) / 2) 1 ∧
      ∫ b in ((1 + d) / 2)..1, ksWWE b d = V₃) :
    ∫ b in Ioo (0 : ℝ) 1, ksWWE b d = V₁ + V₂ + V₃ := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← integral_add_adjacent_intervals h₁.1 (h₂.1.trans h₃.1),
    ← integral_add_adjacent_intervals h₂.1 h₃.1, h₁.2, h₂.2, h₃.2]
  ring

/-- The range `(0, σ₋)`. -/
theorem ksWY_piece_I (hd : d ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun b => ksWWE b d) volume 0 ((1 - d) / 2) ∧
      ∫ b in (0 : ℝ)..((1 - d) / 2), ksWWE b d =
        ksWYv (ksWY1L d) (ksWY1P d) (ksWY1D d) (ksWY1Q d) (ksWY1C d) (ksWY1R d) (ksWY1S d) 0
          ((1 - d) / 2) := by
  obtain ⟨h0, h1⟩ := hd
  have hlu : (0 : ℝ) ≤ (1 - d) / 2 := by linarith
  refine ksWY_piece _ _ _ _ _ _ _ hlu ?_ ?_ ?_ ?_ ?_
    (fun b hb => (ksWY1_eqOn ⟨h0, h1⟩ hb).trans (ksWY_ksWWE_I hb.2).symm) <;>
  simp only [ksWY1D, ksWY1Q, ksWY1C, ksWY1R, ksWY1S, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, uIcc_of_le hlu, mem_Icc, ne_eq] <;>
  and_intros <;> intro h <;> linarith

/-- The range `(σ₋, σ₊)`. -/
theorem ksWY_piece_II (hd : d ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun b => ksWWE b d) volume ((1 - d) / 2) ((1 + d) / 2) ∧
      ∫ b in ((1 - d) / 2)..((1 + d) / 2), ksWWE b d =
        ksWYv (ksWY2L d) (ksWY2P d) (ksWY2D d) (ksWY2Q d) (ksWY2C d) (ksWY2R d) (ksWY2S d)
          ((1 - d) / 2) ((1 + d) / 2) := by
  obtain ⟨h0, h1⟩ := hd
  have hlu : (1 - d) / 2 ≤ (1 + d) / 2 := by linarith
  refine ksWY_piece _ _ _ _ _ _ _ hlu ?_ ?_ ?_ ?_ ?_
    (fun b hb => (ksWY2_eqOn ⟨h0, h1⟩ hb).trans (ksWY_ksWWE_II hb).symm) <;>
  simp only [ksWY2D, ksWY2Q, ksWY2C, ksWY2R, ksWY2S, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, uIcc_of_le hlu, mem_Icc, ne_eq] <;>
  and_intros <;> intro h <;> linarith

/-- The range `(σ₊, 1)`. -/
theorem ksWY_piece_III (hd : d ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun b => ksWWE b d) volume ((1 + d) / 2) 1 ∧
      ∫ b in ((1 + d) / 2)..1, ksWWE b d =
        ksWYv (ksWY3L d) (ksWY3P d) (ksWY3D d) (ksWY3Q d) (ksWY3C d) (ksWY3R d) (ksWY3S d)
          ((1 + d) / 2) 1 := by
  obtain ⟨h0, h1⟩ := hd
  have hlu : (1 + d) / 2 ≤ 1 := by linarith
  refine ksWY_piece _ _ _ _ _ _ _ hlu ?_ ?_ ?_ ?_ ?_
    (fun b hb => (ksWY3_eqOn ⟨h0, h1⟩ hb).trans (ksWY_ksWWE_III h0.le hb.1).symm) <;>
  simp only [ksWY3D, ksWY3Q, ksWY3C, ksWY3R, ksWY3S, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, uIcc_of_le hlu, mem_Icc, ne_eq] <;>
  and_intros <;> intro h <;> linarith

/-- **The `β`-integral of `ρ_B`** in closed form. -/
theorem ksWY_integral_ksWWE_eq (hd : d ∈ Ioo (0 : ℝ) 1) :
    ∫ b in Ioo (0 : ℝ) 1, ksWWE b d = ksWRBv d := by
  rw [ksWY_integral_ksWWE (ksWY_piece_I hd) (ksWY_piece_II hd) (ksWY_piece_III hd),
    ksWYv_total hd]

/-- **The value of `ρ_B`**: `ksWRhoB δ = ksWRBv δ` on `(0, 1)`. -/
theorem ksWY_ksWRhoB_eq_ksWRBv (hd : d ∈ Ioo (0 : ℝ) 1) : ksWRhoB d = ksWRBv d := by
  rw [ksWW_ksWRhoB_eq hd, ksWY_integral_ksWWE_eq hd]

/-- **The density identity of Set (a)**: `2ρ_A(δ) + ρ_B(δ) = 16ρ⁽⁴⁾(δ) + 6ρ_D(δ)` on
`(0, 1)`. -/
theorem ksWY_density_identity (hd : d ∈ Ioo (0 : ℝ) 1) :
    2 * ksWRhoA d + ksWRhoB d = 16 * ksRho d + 6 * ksRhoDm d :=
  (ksWR_ksWRhoB_iff hd).2 (ksWY_ksWRhoB_eq_ksWRBv hd)

end QED.ChainProof.SetAKS

end
