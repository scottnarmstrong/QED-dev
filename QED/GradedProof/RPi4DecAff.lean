/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecRep
public import QED.GradedProof.RPi4DecScalForm

/-!
# (R-Π₄) step L9, D3: `DecScalAff` from scaling, the anomaly and regularity at `s = 0`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (decoupling),
part D3. The per-flavour function `decT₀` (two loops, fixed auxiliary pair, counterterms at
`μ`) and the one-loop functional `decD₀` (the `s`-subtracted projected mass-derivative block of
the same configuration, the coefficient of the counterterm mass) are related by:

* `DecScaleT₀ e` (from D3a): `decT₀ e μ x s = decT₀ e 1 (x/μ²) (s/μ²)`;
* `DecAnomT₀ e κ` (from D3a, D3b and D1): the values at `μ = 1` are dilation covariant up to
  `κ log Λ · decD₀`;
* `DecDil (decD₀ e 1)` (from D3c): the one-loop functional is exactly covariant;
* `DecLipD e` (D3c), `DecLipT e` (**D3d, the analytic core**): Lipschitz in `s` near `0` at
  fixed masses.

Then `dec_scalAff_of`: **`DecScalAff e`**. The values at `s = 0` vanish by definition
(`decT₀_zero`, `decD₀_zero`).
-/

@[expose] public section

open Complex Filter Topology
open QED.Graded

namespace QED.GradedProof.RPi4

/-- **The one-loop functional of the configuration `decCfg μ x`**: the `s`-subtracted projected
limit of the mass-derivative block with unit weight, `/ e²` (the counterterm-mass coefficient). -/
noncomputable def decD₀ (e μ x s : ℝ) : ℂ :=
  I * (projS (fLim (decCfg μ x) (fun _ => 0) e fun _ => 1) s -
    projS (fLim (decCfg μ x) (fun _ => 0) e fun _ => 1) 0) / (e : ℂ) ^ 2

theorem decT₀_zero (e μ x : ℝ) : decT₀ e μ x 0 = 0 := by
  simp only [decT₀, asmPolLim, sub_self, tendsto_const_nhds.limUnder_eq, zero_div]

theorem decD₀_zero (e μ x : ℝ) : decD₀ e μ x 0 = 0 := by
  simp [decD₀]

/-- **(D3a, special case) exact scaling of the per-flavour function.** -/
def DecScaleT₀ (e : ℝ) : Prop :=
  ∀ μ x s : ℝ, 0 < μ → μ ^ 2 ≤ x → -(4 * μ ^ 2) < s →
    decT₀ e μ x s = decT₀ e 1 (x / μ ^ 2) (s / μ ^ 2)

/-- **(D3a + D3b + D1) dilation covariance up to the counterterm-mass anomaly** at `μ = 1`. -/
def DecAnomT₀ (e : ℝ) (κ : ℂ) : Prop :=
  ∀ Λ x s : ℝ, 0 < Λ → 0 < x → -(4 * min 1 x) < s → -(4 * min 1 Λ) < Λ * s →
    decT₀ e 1 (Λ * x) (Λ * s) + ((x - 2 : ℝ) : ℂ) * decT₀ e 1 Λ (Λ * s) +
      ((1 - x : ℝ) : ℂ) * decT₀ e 1 (2 * Λ) (Λ * s) =
      decT₀ e 1 x s + κ * (Real.log Λ : ℂ) * decD₀ e 1 x s

/-- **(D3c) the one-loop functional is Lipschitz in `s` near `0`** at fixed masses. -/
def DecLipD (e : ℝ) : Prop := ∀ x : ℝ, 0 < x → DecLip0 (decD₀ e 1 x)

/-- **(D3d, the analytic core) the per-flavour function is Lipschitz in `s` near `0`** at fixed
masses. -/
def DecLipT (e : ℝ) : Prop := ∀ x : ℝ, 0 < x → DecLip0 (decT₀ e 1 x)

/-- **D3: `DecScalAff` from the scaling, the anomaly, the one-loop covariance and the two
Lipschitz bounds.** -/
theorem dec_scalAff_of {e : ℝ} (κ : ℂ) (hS : DecScaleT₀ e) (hA : DecAnomT₀ e κ)
    (hD : DecDil (decD₀ e 1)) (hDl : DecLipD e) (hTl : DecLipT e) : DecScalAff e := by
  obtain ⟨G, φ, δ, L, hδ, hL, hG0, hφ0, hG, hφ, hT⟩ := dec_exists_scal_anom κ hD
    (fun x _ => decD₀_zero e 1 x) hDl hA (fun x _ => decT₀_zero e 1 x) hTl
  refine ⟨G, φ, κ, δ, L,
    fun μ s => -2 * G (s / μ ^ 2) + G (s / μ ^ 2 / 2) +
      κ * (Real.log 2 : ℂ) * φ (s / μ ^ 2 / 2),
    fun μ s => (G (s / μ ^ 2) - G (s / μ ^ 2 / 2) - κ * (Real.log 2 : ℂ) * φ (s / μ ^ 2 / 2)) /
      ((μ ^ 2 : ℝ) : ℂ),
    hδ, hL, hG0, hφ0, hG, hφ, fun μ x s hμ hx hs => ?_⟩
  have hμ2 : 0 < μ ^ 2 := by positivity
  have hy : 1 ≤ x / μ ^ 2 := by rwa [le_div_iff₀ hμ2, one_mul]
  have ht : -(4 * min 1 (x / μ ^ 2)) < s / μ ^ 2 := by
    rw [min_eq_left hy, lt_div_iff₀ hμ2]
    linarith
  rw [hS μ x s hμ hx hs, hT _ _ (zero_lt_one.trans_le hy) ht]
  have hx0 : x ≠ 0 := (hμ2.trans_le hx).ne'
  have hμc : ((μ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hμ2.ne'
  simp only [decR, decLφ, decT]
  rw [show s / μ ^ 2 / (x / μ ^ 2) = s / x by field_simp]
  have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  push_cast
  field_simp
  ring

end QED.GradedProof.RPi4

end
