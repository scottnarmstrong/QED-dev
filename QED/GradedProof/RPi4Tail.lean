/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# (R-Π₄) step L8: regulator limits of an additive function of the photon pair

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L8, in a form that
does not mention the model. The class sum `Q(a, b)` at the photon pair `(a, b)` is additive,
`Q(a, d) = Q(a, b) + Q(b, d)` (`QED.GradedProof.RPi4.qPair_add`). Then the joint limit
`m_γ → 0`, `Λ → ∞` of `Q(m_γ, Λ)` follows from two tail bounds: `‖Q(b, d)‖ ≤ h(b)` for a heavy
pair `R₀ ≤ b ≤ d`, and `‖Q(a, b)‖ ≤ h₀(b)` for a light pair `0 < a ≤ b ≤ r₀`, with `h → 0` at
infinity and `h₀ → 0` at `0⁺`.

* `exists_tendsto_of_incr`: a function on `ℝ` with increments `‖g d - g b‖ ≤ h b` (`b ≤ d`) and
  `h → 0` converges at infinity, with `‖g b - L‖ ≤ h b`.
* `exists_pair_limit`: **the joint limit with an explicit rate**:
  `‖Q(a, b) - L‖ ≤ h₀(a) + h(b)` for `0 < a ≤ r₀`, `R₀ ≤ b`. The rate is uniform in any parameter
  on which `h`, `h₀` do not depend (here: `s` on a compact interval).
-/

@[expose] public section

open Filter Topology

namespace QED.GradedProof.RPi4

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

/-- **Convergence at infinity from bounded increments**, with the rate. -/
theorem exists_tendsto_of_incr {g : ℝ → E} {h : ℝ → ℝ} {R₀ : ℝ}
    (hh : Tendsto h atTop (𝓝 0)) (hinc : ∀ b d, R₀ ≤ b → b ≤ d → ‖g d - g b‖ ≤ h b) :
    ∃ L : E, Tendsto g atTop (𝓝 L) ∧ ∀ b, R₀ ≤ b → ‖g b - L‖ ≤ h b := by
  have hc : Cauchy (map g atTop) := by
    refine Metric.cauchy_iff.2 ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨R₁, hR₁⟩ := (hh.eventually (gt_mem_nhds (half_pos hε))).exists_forall_of_atTop
    set R := max R₀ R₁
    refine ⟨g '' Set.Ici R, image_mem_map (Ici_mem_atTop R), ?_⟩
    rintro _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩
    have h1 := hinc R b (le_max_left _ _) hb
    have h2 := hinc R d (le_max_left _ _) hd
    have h3 := hR₁ R (le_max_right _ _)
    rw [dist_eq_norm]
    calc ‖g b - g d‖ = ‖(g b - g R) - (g d - g R)‖ := by congr 1; abel
      _ ≤ ‖g b - g R‖ + ‖g d - g R‖ := norm_sub_le _ _
      _ < ε := by linarith
  obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.1 hc
  refine ⟨L, hL, fun b hb => ?_⟩
  rw [norm_sub_rev]
  refine le_of_tendsto ((hL.sub_const (g b)).norm) ?_
  filter_upwards [eventually_ge_atTop b] with d hd
  exact hinc b d hb hd

variable {Q : ℝ → ℝ → E}

/-- **The joint regulator limit of an additive function of the photon pair**, with the rate
`h₀(a) + h(b)`. -/
theorem exists_pair_limit {r₀ R₀ : ℝ} (hr₀ : 0 < r₀) (hrR : r₀ ≤ R₀)
    (hadd : ∀ a b d, 0 < a → 0 < b → 0 < d → Q a d = Q a b + Q b d)
    {h h₀ : ℝ → ℝ} (hh : Tendsto h atTop (𝓝 0)) (hh₀ : Tendsto h₀ (𝓝[>] 0) (𝓝 0))
    (hheavy : ∀ b d, R₀ ≤ b → b ≤ d → ‖Q b d‖ ≤ h b)
    (hlight : ∀ a b, 0 < a → a ≤ b → b ≤ r₀ → ‖Q a b‖ ≤ h₀ b) :
    ∃ L : E, ∀ a b, 0 < a → a ≤ r₀ → R₀ ≤ b → ‖Q a b - L‖ ≤ h₀ a + h b := by
  -- heavy side: `g b = Q r₀ b`
  obtain ⟨L₁, -, hL₁⟩ := exists_tendsto_of_incr (g := fun b => Q r₀ b) hh fun b d hb hbd => by
    have hb0 : 0 < b := hr₀.trans_le (hrR.trans hb)
    rw [hadd r₀ b d hr₀ hb0 (hb0.trans_le hbd), add_sub_cancel_left]
    exact hheavy b d hb hbd
  -- light side: `g y = Q y⁻¹ r₀` as `y → ∞`
  have hh₀' : Tendsto (fun y : ℝ => h₀ y⁻¹) atTop (𝓝 0) :=
    hh₀.comp tendsto_inv_atTop_nhdsGT_zero
  obtain ⟨L₀, -, hL₀⟩ := exists_tendsto_of_incr (g := fun y => Q y⁻¹ r₀) (R₀ := r₀⁻¹) hh₀'
    fun y z hy hyz => by
      have hy0 : 0 < y := (inv_pos.2 hr₀).trans_le hy
      have hz0 : 0 < z := hy0.trans_le hyz
      have hzy : z⁻¹ ≤ y⁻¹ := inv_anti₀ hy0 hyz
      have hyr : y⁻¹ ≤ r₀ := by
        rw [inv_le_comm₀ hy0 hr₀]
        exact hy
      rw [hadd z⁻¹ y⁻¹ r₀ (inv_pos.2 hz0) (inv_pos.2 hy0) hr₀, add_sub_cancel_right]
      exact hlight _ _ (inv_pos.2 hz0) hzy hyr
  refine ⟨L₀ + L₁, fun a b ha har hb => ?_⟩
  have hb0 : 0 < b := hr₀.trans_le (hrR.trans hb)
  have e1 := hL₀ a⁻¹ (inv_anti₀ ha har)
  rw [inv_inv] at e1
  have e2 := hL₁ b hb
  rw [hadd a r₀ b ha hr₀ hb0]
  calc ‖Q a r₀ + Q r₀ b - (L₀ + L₁)‖ = ‖(Q a r₀ - L₀) + (Q r₀ b - L₁)‖ := by congr 1; abel
    _ ≤ ‖Q a r₀ - L₀‖ + ‖Q r₀ b - L₁‖ := norm_add_le _ _
    _ ≤ h₀ a + h b := add_le_add e1 e2

end QED.GradedProof.RPi4

end
