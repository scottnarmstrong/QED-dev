/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKUSum
public import QED.ChainProof.SetAKSKAFix

/-!
# Set (a), stage D: the per-flavour limit as a flavour sum, and the reduction of stage D4

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification). By `ksU_decT₀_re_eq` the per-flavour limit is the finite part
`ksUFTot` of the sum of the classes. That finite part is a flavour sum
`∑_f c_f G(e, μ, M_f, s)` of one function `ksUGf` of a single mass, and for the configuration
`decCfg μ x` (masses `μ, √2 μ, √x`, coefficients `x/μ² - 2, 1 - x/μ², 1`) the first two
flavours are affine in `x`. Hence the output statement `KsSpecForm e ρ` of stage D follows from
a dispersive representation of the single function `G(e, μ, √x, s)` alone.

Main results:

* `ksU_ksUFTot_eq`: `ksUFTot e μ x s = ∑_f c_f G(e, μ, M_f, s)`;
* **`ksU_decT₀_eq`**: `decT₀ e μ x s = (∑_f c_f G(e, μ, M_f, s))/e⁴` (a real number);
* **`ksU_ksSpecForm_of_flavour`**: the reduction of `KsSpecForm e ρ` to `G(e, μ, √x, s)`.
-/

@[expose] public section

open Filter Topology MeasureTheory Set

namespace QED.ChainProof.SetAKS

open QED.GradedProof.RPi4

/-- **The single-flavour finite part** `G(e, μ, M, s)`: the `VA`, `VB` and mass classes of one
flavour of mass `M`, subtracted at `s = 0`, the mass insertion being on the lightest line
`μ`. -/
noncomputable def ksUGf (e μ M s : ℝ) : ℝ :=
  ksUKe e * (2 * (ksUF M s - ksUF M 0) + (ksUFB M s - ksUFB M 0)) +
    ksUme e * ksUcm μ * (e ^ 2 / (4 * Real.pi ^ 2)) * (ksDm (s / M ^ 2) - ksDm (0 / M ^ 2))

theorem ksU_ksUFTot_eq (e μ x s : ℝ) :
    ksUFTot e μ x s = ∑ f, (decCfg μ x).coeff f * ksUGf e μ ((decCfg μ x).mass f) s := by
  set Φ := decCfg μ x
  have e1 : ∀ f, Φ.coeff f * ksUGf e μ (Φ.mass f) s =
      ksUKe e * (2 * (Φ.coeff f * ksUF (Φ.mass f) s) - 2 * (Φ.coeff f * ksUF (Φ.mass f) 0) +
        (Φ.coeff f * ksUFB (Φ.mass f) s) - (Φ.coeff f * ksUFB (Φ.mass f) 0)) +
      ksUme e * ksUcm μ * (e ^ 2 / (4 * Real.pi ^ 2)) *
        (Φ.coeff f * ksDm (s / Φ.mass f ^ 2) - Φ.coeff f * ksDm (0 / Φ.mass f ^ 2)) := by
    intro f; unfold ksUGf; ring
  simp only [e1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ksUFTot,
    ksMassF]
  ring

section Eq

variable {e μ x s : ℝ} (he : e ≠ 0) (hμ : 0 < μ) (hx : μ ^ 2 ≤ x) (hs : -(4 * μ ^ 2) < s)
include he hμ hx hs

/-- **The per-flavour limit as a real flavour sum.** -/
theorem ksU_decT₀_eq : decT₀ e μ x s =
    (((∑ f, (decCfg μ x).coeff f * ksUGf e μ ((decCfg μ x).mass f) s) / e ^ 4 : ℝ) : ℂ) := by
  have hre := (ksU_decT₀_re_eq hμ hx hs he).2
  have him := ksD_im_decT₀ he hμ hx hs
  have h4 : ((e : ℂ) ^ 4) ≠ 0 := pow_ne_zero 4 (Complex.ofReal_ne_zero.2 he)
  have hz : (e : ℂ) ^ 4 * decT₀ e μ x s = ((ksUFTot e μ x s : ℝ) : ℂ) :=
    Complex.ext (by simpa using hre) (by simpa using him)
  rw [← ksU_ksUFTot_eq, Complex.ofReal_div, Complex.ofReal_pow, ← hz, mul_div_cancel_left₀ _ h4]

end Eq

/-- **The reduction of stage D to one flavour**: if the single-flavour finite part at the
heaviest flavour `M = √x` is, up to an affine function of `x`, the dispersive integral of a
density `ρ`, then the output statement `KsSpecForm e ρ` of stage D holds. -/
theorem ksU_ksSpecForm_of_flavour {e : ℝ} (he : e ≠ 0) {ρ : ℝ → ℝ → ℝ → ℝ}
    (h : ∃ α β : ℝ → ℝ → ℝ, ∀ μ x s : ℝ, 0 < μ → μ ^ 2 ≤ x → -(4 * μ ^ 2) < s →
      ksUGf e μ (Real.sqrt x) s / e ^ 4 =
        (∫ δ in (0 : ℝ)..1, ksSpecKer (s / x) δ * ρ μ x δ) / (16 * Real.pi ^ 4) +
          (α μ s + β μ s * x)) :
    KsSpecForm e ρ := by
  obtain ⟨α, β, hG⟩ := h
  refine ⟨fun μ s => (((-2 * ksUGf e μ μ s + ksUGf e μ (Real.sqrt 2 * μ) s) / e ^ 4 +
      α μ s : ℝ) : ℂ), fun μ s => (((ksUGf e μ μ s - ksUGf e μ (Real.sqrt 2 * μ) s) /
      μ ^ 2 / e ^ 4 + β μ s : ℝ) : ℂ), fun μ x s hμ hx hs => ?_⟩
  rw [ksU_decT₀_eq he hμ hx hs, Fin.sum_univ_three]
  have hG' := hG μ x s hμ hx hs
  have hμ2 : μ ^ 2 ≠ 0 := (pow_pos hμ 2).ne'
  have he4 : e ^ 4 ≠ 0 := pow_ne_zero 4 he
  simp only [decCfg, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  set G1 := ksUGf e μ μ s
  set G2 := ksUGf e μ (Real.sqrt 2 * μ) s
  set I := ∫ δ in (0 : ℝ)..1, ksSpecKer (s / x) δ * ρ μ x δ
  have h3 : 1 * ksUGf e μ (Real.sqrt x) s / e ^ 4 = I / (16 * Real.pi ^ 4) +
      (α μ s + β μ s * x) := by rw [one_mul]; exact hG'
  have key : ((x / μ ^ 2 - 2) * G1 + (1 - x / μ ^ 2) * G2 + 1 * ksUGf e μ (Real.sqrt x) s) /
      e ^ 4 = I / (16 * Real.pi ^ 4) + (((-2 * G1 + G2) / e ^ 4 + α μ s) +
        ((G1 - G2) / μ ^ 2 / e ^ 4 + β μ s) * x) := by
    calc ((x / μ ^ 2 - 2) * G1 + (1 - x / μ ^ 2) * G2 + 1 * ksUGf e μ (Real.sqrt x) s) / e ^ 4
        = ((x / μ ^ 2 - 2) * G1 + (1 - x / μ ^ 2) * G2) / e ^ 4 +
          1 * ksUGf e μ (Real.sqrt x) s / e ^ 4 := by ring
      _ = _ := by rw [h3]; field_simp; ring
  rw [key]
  push_cast
  ring

end QED.ChainProof.SetAKS

end
