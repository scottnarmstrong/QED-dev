/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.A2Four
public import QED.Chain.HeavyLeptonBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The heavy-lepton coefficient `a2Four`: limit and enclosures

Helper-level proofs for the Phase 5 Stage 0 packet (decision D-50), goals (U₃′), (U₄), (U₅).

The frozen coefficient `QED.Lepton.a2Four` writes the three dilogarithms as explicit `∑'`
series; these are the series of `QED.Polylog.Li₂`, so `a2Four` is the helper-level closed form
`QED.Chain.HeavyLepton.a2Heavy` by definition (`a2Four_eq_a2Heavy`). The limit `y → 1⁻` and the
muon and tau enclosures then follow from `tendsto_a2Heavy_one` and the enclosures of
`QED/Chain/HeavyLeptonBounds.lean`, whose intervals are exactly the frozen AKN intervals
(`0.00483633159 = 483633159/10¹¹`, `0.00483633181 = 483633181/10¹¹`,
`0.000287566 = 287566/10⁹`, `0.000287604 = 287604/10⁹`) and whose conclusions are inside the
frozen ones.

## Main statements

* `a2Four_eq_a2Heavy`: `a2Four = a2Heavy` (definitional).
* `tendsto_a2Four_one'`: the frozen goal `QED.Lepton.tendsto_a2Four_one`.
* `a2Four_mem_muon'`, `a2Four_mem_tau'`: the frozen goals `QED.Lepton.a2Four_mem_muon` and
  `QED.Lepton.a2Four_mem_tau`.
-/

@[expose] public section

open Filter Topology QED.Chain.HeavyLepton

namespace QED.Lepton.Proof

/-- The frozen coefficient is the helper closed form: the `∑'` series are `QED.Polylog.Li₂`. -/
theorem a2Four_eq_a2Heavy : a2Four = a2Heavy := rfl

/-- (U₃′) The limit `y → 1⁻` of `a2Four` is `119/36 - π²/3`. -/
theorem tendsto_a2Four_one' :
    Tendsto a2Four (𝓝[<] 1) (𝓝 (119 / 36 - Real.pi ^ 2 / 3)) := by
  rw [a2Four_eq_a2Heavy]
  exact tendsto_a2Heavy_one

/-- (U₄) The muon enclosure. -/
theorem a2Four_mem_muon' (y : ℝ) (hy : y ∈ Set.Icc (0.00483633159 : ℝ) 0.00483633181) :
    a2Four y ∈ Set.Icc (5.197386e-7 : ℝ) 5.197388e-7 := by
  rw [a2Four_eq_a2Heavy]
  obtain ⟨h1, h2⟩ := hy
  have hlo := a2Heavy_mu_lo
  have hhi := a2Heavy_mu_hi
  have m1 : a2Heavy (483633159 / 10 ^ 11) ≤ a2Heavy y :=
    a2Heavy_mono (by norm_num) (by norm_num at h1 ⊢; linarith) (by norm_num at h2; linarith)
  have m2 : a2Heavy y ≤ a2Heavy (483633181 / 10 ^ 11) :=
    a2Heavy_mono (by norm_num at h1; linarith) (by norm_num at h2 ⊢; linarith) (by norm_num)
  have n1 : (5.197386e-7 : ℝ) ≤ 5197386525 / 10 ^ 16 := by norm_num
  have n2 : (5197386998 : ℝ) / 10 ^ 16 ≤ 5.197388e-7 := by norm_num
  exact ⟨by linarith, by linarith⟩

/-- (U₅) The tau enclosure. -/
theorem a2Four_mem_tau' (y : ℝ) (hy : y ∈ Set.Icc (0.000287566 : ℝ) 0.000287604) :
    a2Four y ∈ Set.Icc (1.8376e-9 : ℝ) 1.8382e-9 := by
  rw [a2Four_eq_a2Heavy]
  obtain ⟨h1, h2⟩ := hy
  have hlo := a2Heavy_tau_lo
  have hhi := a2Heavy_tau_hi
  have m1 : a2Heavy (287566 / 10 ^ 9) ≤ a2Heavy y :=
    a2Heavy_mono (by norm_num) (by norm_num at h1 ⊢; linarith) (by norm_num at h2; linarith)
  have m2 : a2Heavy y ≤ a2Heavy (287604 / 10 ^ 9) :=
    a2Heavy_mono (by norm_num at h1; linarith) (by norm_num at h2 ⊢; linarith) (by norm_num)
  have n1 : (1.8376e-9 : ℝ) ≤ 18376481 / 10 ^ 16 := by norm_num
  have n2 : (18381339 : ℝ) / 10 ^ 16 ≤ 1.8382e-9 := by norm_num
  exact ⟨by linarith, by linarith⟩

end QED.Lepton.Proof

end
