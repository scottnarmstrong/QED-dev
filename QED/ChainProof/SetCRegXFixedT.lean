/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegXIntegral

/-!
# The crossed partial fractions in physical regulator coordinates

The spectral squared mass is fixed in electron-mass units. The regulator
masses in the engine are in physical units, so they are divided by the
positive electron mass before applying the joint limit from
`QED/ChainProof/SetCRegXIntegral.lean`.
-/

public section

open Set Filter Topology

namespace QED.ChainProof.SetCK

private theorem tendsto_regulator_div_mass {m : ℝ} (hm : 0 < m) :
    Tendsto (fun p : ℝ × ℝ => (p.1 / m, p.2 / m)) (𝓝[>] 0 ×ˢ atTop) (𝓝[>] 0 ×ˢ atTop) := by
  have h₁ : Tendsto (fun x : ℝ => x / m) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa only [id_eq, zero_div] using
        (((continuous_id.div_const m).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with x hx
      exact div_pos hx hm
  have h₂ : Tendsto (fun x : ℝ => x / m) atTop atTop :=
    (tendsto_div_const_atTop_of_pos hm).2 tendsto_id
  exact (h₁.comp tendsto_fst).prodMk (h₂.comp tendsto_snd)

/-- The exact crossed kernel has its fixed-spectral-mass limit in the
physical regulator coordinates of the engine. -/
theorem tendsto_xExact_div_mass {m T : ℝ} (hm : 0 < m) (hT : 4 ≤ T) :
    Tendsto (fun p : ℝ × ℝ => xExact T (p.1 / m) (p.2 / m))
      (𝓝[>] 0 ×ˢ atTop) (𝓝 (crossUnit 0 T + crossUnit T 0)) := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) hT
  have h := (tendsto_xExact hTpos).comp (tendsto_regulator_div_mass hm)
  simpa only [Function.comp_def] using h

/-- At fixed spectral mass, the two squared regulator masses eventually
lie on opposite sides of the spectral mass with strict gaps. -/
theorem eventually_xExact_mass_separation {m T : ℝ} (hm : 0 < m) (hT : 4 ≤ T) :
    ∀ᶠ p : ℝ × ℝ in 𝓝[>] 0 ×ˢ atTop,
      0 < p.1 ∧ p.1 < p.2 ∧ (p.1 / m) ^ 2 < T / 2 ∧ 2 * T < (p.2 / m) ^ 2 := by
  have hp : Tendsto (fun p : ℝ × ℝ => p.1) (𝓝[>] 0 ×ˢ atTop) (𝓝[>] 0) := tendsto_fst
  have hq : Tendsto (fun p : ℝ × ℝ => p.2) (𝓝[>] 0 ×ˢ atTop) atTop := tendsto_snd
  have hpair := tendsto_regulator_div_mass hm
  have h₁ : Tendsto (fun p : ℝ × ℝ => (p.1 / m) ^ 2) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) := by
    have hpow : Tendsto (fun q : ℝ => q ^ 2) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((continuous_pow 2).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    exact hpow.comp (tendsto_fst.comp hpair)
  have h₂ : Tendsto (fun p : ℝ × ℝ => (p.2 / m) ^ 2) (𝓝[>] 0 ×ˢ atTop) atTop :=
    (tendsto_pow_atTop two_ne_zero).comp (tendsto_snd.comp hpair)
  filter_upwards [hp.eventually self_mem_nhdsWithin,
    (hp.mono_right nhdsWithin_le_nhds).eventually (Iio_mem_nhds (zero_lt_one' ℝ)),
    hq.eventually (eventually_gt_atTop 1),
    h₁.eventually (Iio_mem_nhds (show 0 < T / 2 by linarith)),
    h₂.eventually (eventually_gt_atTop (2 * T))] with p hpos hlight hheavy ha hb
  exact ⟨hpos, hlight.trans hheavy, ha, hb⟩

end QED.ChainProof.SetCK

end
