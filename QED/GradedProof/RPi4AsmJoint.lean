/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DensBound
public import QED.GradedProof.RPi4Light
public import QED.GradedProof.RPi4Tail

/-!
# (R-Π₄) step L8: the joint photon-regulator limit of the subtracted class sum

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L8. At fixed fermion
masses, the subtracted class sum `Q(a, b; s) - Q(a, b; 0)` (`QED.GradedProof.RPi4.qPair` at the
photon pair `(a, b) = (m_γ, Λ)`, which is `Π(s)` by `pol_eq_qPair_sub`) has a joint limit as
`m_γ → 0`, `Λ → ∞`, with the rate `C (√m_γ + Λ⁻¹)`, uniformly for `s` in a compact interval
below threshold. The heavy pair is `exists_norm_qPair_sub_heavy_le` (conditional on the
face-limit identity `FaceLimitId`, step L6d3), the light pair `exists_norm_qPair_sub_light_le`
(L7), the assembly `exists_pair_limit`.

* `asmPolLim`: the limit, named along the diagonal `m_γ = Λ⁻¹`, `Λ → ∞`;
* `asm_exists_norm_sub_polLim_le`: **the joint limit with its rate**, given `FaceLimitId` on the
  interval `[min S₀ 0, max S 0]` at the tilt scale `c = 1 + |max S 0|`.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.RPi4

open QED.WickModel (Params)

section L8

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

/-- **The photon-regulator limit of the subtracted class sum** (step L8), named along the
diagonal `m_γ = Λ⁻¹`, `Λ → ∞`; it is the joint limit by `asm_exists_norm_sub_polLim_le`. -/
noncomputable def asmPolLim (e s : ℝ) : ℂ :=
  limUnder atTop fun Λ : ℝ => qPair Φ rep e Λ⁻¹ Λ s - qPair Φ rep e Λ⁻¹ Λ 0

variable (P : Params) {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **L8: the joint photon-regulator limit, with its rate**, given the face-limit identity:
`‖Q(a, b; s) - Q(a, b; 0) - asmPolLim(s)‖ ≤ C (√a + b⁻¹)` for `0 < a ≤ 1 ≤ b`, uniformly for
`s ∈ [S₀, S]`, `S₀ > -4m₀²`. -/
theorem asm_exists_norm_sub_polLim_le (he : P.e ≠ 0) {S₀ S : ℝ} (hS₀ : -(4 * m₀ ^ 2) < S₀)
    (hId : ∀ s : ℝ, min S₀ 0 ≤ s → s ≤ max S 0 →
      FaceLimitId Φ rep P.e m₀ (1 + |max S 0|) s) :
    ∃ C : ℝ, ∀ s : ℝ, S₀ ≤ s → s ≤ S → ∀ a b : ℝ, 0 < a → a ≤ 1 → 1 ≤ b →
      ‖qPair Φ rep P.e a b s - qPair Φ rep P.e a b 0 - asmPolLim Φ rep P.e s‖ ≤
        C * (Real.sqrt a + b⁻¹) := by
  set c : ℝ := 1 + |max S 0| with hc_def
  have hc : 0 < c := by positivity
  have h00 : -(4 * m₀ ^ 2) < 0 := by nlinarith
  have hS₀' : -(4 * m₀ ^ 2) < min S₀ 0 := lt_min hS₀ h00
  have hS' : max S 0 < 2 * c ^ 2 := by
    have := le_abs_self (max S 0)
    nlinarith [abs_nonneg (max S 0)]
  have hS₀S' : min S₀ 0 ≤ max S 0 := (min_le_right _ _).trans (le_max_right _ _)
  obtain ⟨Ch, hCh⟩ := exists_norm_qPair_sub_heavy_le Φ rep P hm₀ hmass hrep hPV₁ hPV₂ he hc
    hS₀' (min_le_right _ _) (le_max_right _ _) hS' hId
  obtain ⟨Cl, hCl⟩ := exists_norm_qPair_sub_light_le P Φ rep hm₀ hmass hrep hPV₁ hPV₂ he hS₀'
    hS₀S'
  refine ⟨|Cl| + |Ch|, fun s h₀ h₁ a b ha ha1 hb => ?_⟩
  have h₀' : min S₀ 0 ≤ s := (min_le_left _ _).trans h₀
  have h₁' : s ≤ max S 0 := h₁.trans (le_max_left _ _)
  have hs : -(4 * m₀ ^ 2) < s := hS₀'.trans_le h₀'
  set Q : ℝ → ℝ → ℂ := fun a b => qPair Φ rep P.e a b s - qPair Φ rep P.e a b 0 with hQ
  have hadd : ∀ a b d, 0 < a → 0 < b → 0 < d → Q a d = Q a b + Q b d := fun a b d ha hb hd => by
    simp only [hQ, qPair_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he ha hb hd hs,
      qPair_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he ha hb hd h00]
    ring
  have hh : Tendsto (fun b : ℝ => |Ch| / b) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hsq0 : Tendsto Real.sqrt (𝓝 0) (𝓝 0) := by
    simpa using Real.continuous_sqrt.tendsto 0
  have hh₀ : Tendsto (fun b : ℝ => |Cl| * Real.sqrt b) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hsq0.mono_left nhdsWithin_le_nhds).const_mul |Cl|
  obtain ⟨L, hL⟩ := exists_pair_limit (Q := Q) one_pos le_rfl hadd hh hh₀
    (fun b d hb hbd => (hCh s h₀' h₁' b d hb hbd).trans
      (div_le_div_of_nonneg_right (le_abs_self _) (one_pos.trans_le hb).le))
    (fun a b ha hab hb1 => (hCl a b s ha hab hb1 h₀' h₁').trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)))
  have hlim : asmPolLim Φ rep P.e s = L := by
    refine Tendsto.limUnder_eq ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hr : Tendsto (fun Λ : ℝ => |Cl| * Real.sqrt Λ⁻¹ + |Ch| / Λ) atTop (𝓝 0) := by
      simpa using ((hsq0.comp tendsto_inv_atTop_zero).const_mul |Cl|).add hh
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hr
    filter_upwards [eventually_ge_atTop 1] with Λ hΛ
    have hΛ0 : 0 < Λ := one_pos.trans_le hΛ
    exact hL Λ⁻¹ Λ (inv_pos.2 hΛ0) (inv_le_one_of_one_le₀ hΛ) hΛ
  rw [hlim]
  have e := hL a b ha ha1 hb
  calc ‖Q a b - L‖ ≤ |Cl| * Real.sqrt a + |Ch| / b := e
    _ ≤ (|Cl| + |Ch|) * (Real.sqrt a + b⁻¹) := by
      have hb0 : 0 < b := one_pos.trans_le hb
      rw [div_eq_mul_inv]
      nlinarith [abs_nonneg Cl, abs_nonneg Ch, Real.sqrt_nonneg a, inv_pos.2 hb0]

end L8

end QED.GradedProof.RPi4

end
