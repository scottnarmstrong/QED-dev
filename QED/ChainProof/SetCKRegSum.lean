/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKRegCOut
public import QED.ChainProof.SetCKRegLIn
public import QED.ChainProof.SetCKRegSIn
public import QED.ChainProof.SetCKRegX
public import QED.ChainProof.SetCKCrossLink

/-!
# Set (c), Stage K: the regulated kernel pair sum at infinite Pauli–Villars mass

Helper level (no frozen statement). The Stage K kernel pair sum
`setCKKernelPairSum t = L-pair + S(t,0) + C(t,0) + (X(t,0) + X(0,t)) + G4S + G4C` is the
`λ → 0⁺` limit of its two-mass parametric representations at `Λ = ∞` (layer R1 of the M5
plan), with the photon of mass `λ` on the massless line of each unit:

`regKernelPairR1 t λ = (lInRep + lOutRep) + selfInRep + cornInRep
  + (crossUnit λ² t + crossUnit t λ²) + (scOutSRep + scOutCRep)` (all at `(t, λ)`).

* **`tendsto_regKernelPairR1`**: `regKernelPairR1 t λ → setCKKernelPairSum t` as `λ → 0⁺`, for
  every `t > 0` (the per-group links `tendsto_lPairRep`, `tendsto_selfInRep`,
  `tendsto_cornInRep`, `tendsto_crossUnit`, `tendsto_scOutRep`);
* **`tendsto_regKernelPairMixed`**: the same with the crossed pair at finite `Λ`
  (`xReg t λ Λ`, the only group whose finite-`Λ` (R2) form is in Lean), jointly as
  `(λ, Λ) → (0⁺, ∞)`.

The finite-`Λ` forms of the other groups (layer R2) are not here; see the M5 status in the
scratch `STATUS.md`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology

namespace QED.ChainProof.SetCK

/-- **The regulated kernel pair sum at `Λ = ∞`** (layer R1), photon mass `λ` on the massless
line of each unit. -/
noncomputable def regKernelPairR1 (t lam : ℝ) : ℝ :=
  (lInRep t lam + lOutRep t lam) + selfInRep t lam + cornInRep t lam +
    (crossUnit (lam ^ 2) t + crossUnit t (lam ^ 2)) + scOutRep t lam

/-- The regulated kernel pair sum with the crossed pair at finite `Λ` (`xReg`). -/
noncomputable def regKernelPairMixed (t lam Lam : ℝ) : ℝ :=
  (lInRep t lam + lOutRep t lam) + selfInRep t lam + cornInRep t lam + xReg t lam Lam +
    scOutRep t lam

theorem setCKKernelPairSum_eq_groups (t : ℝ) :
    setCKKernelPairSum t = lPair t + selfIn t + cornIn t + (crossUnit 0 t + crossUnit t 0) +
      (scOutS t + scOutC t) := by
  unfold setCKKernelPairSum
  ring

theorem tendsto_crossUnit_pair {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun lam : ℝ => crossUnit (lam ^ 2) t + crossUnit t (lam ^ 2)) (𝓝[>] 0)
      (𝓝 (crossUnit 0 t + crossUnit t 0)) := by
  have h1 : Tendsto (fun lam : ℝ => lam ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun x : ℝ => x ^ 2) (𝓝 0) (𝓝 (0 ^ 2)) := (continuous_pow 2).tendsto 0
    rw [zero_pow two_ne_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hp : ∀ᶠ lam : ℝ in 𝓝[>] 0, 0 ≤ lam ^ 2 := Eventually.of_forall fun lam => sq_nonneg lam
  have ht' : ∀ᶠ _ : ℝ in 𝓝[>] 0, 0 ≤ t := Eventually.of_forall fun _ => ht
  exact (tendsto_crossUnit h1 tendsto_const_nhds le_rfl ht hp ht').add
    (tendsto_crossUnit tendsto_const_nhds h1 ht le_rfl ht' hp)

/-- **The regulator link of the kernel pair sum at `Λ = ∞`**: for `t > 0`,
`regKernelPairR1 t λ → setCKKernelPairSum t` as `λ → 0⁺`. -/
theorem tendsto_regKernelPairR1 {t : ℝ} (ht : 0 < t) :
    Tendsto (fun lam => regKernelPairR1 t lam) (𝓝[>] 0) (𝓝 (setCKKernelPairSum t)) := by
  rw [setCKKernelPairSum_eq_groups]
  exact ((((tendsto_lPairRep ht).add (tendsto_selfInRep ht)).add (tendsto_cornInRep ht)).add
    (tendsto_crossUnit_pair ht.le)).add (tendsto_scOutRep ht)

/-- **The joint link with the crossed pair at finite `Λ`**: for `t > 0`,
`regKernelPairMixed t λ Λ → setCKKernelPairSum t` as `(λ, Λ) → (0⁺, ∞)`. -/
theorem tendsto_regKernelPairMixed {t : ℝ} (ht : 0 < t) :
    Tendsto (fun p : ℝ × ℝ => regKernelPairMixed t p.1 p.2) (𝓝[>] 0 ×ˢ atTop)
      (𝓝 (setCKKernelPairSum t)) := by
  rw [setCKKernelPairSum_eq_groups]
  have hf : Tendsto (fun p : ℝ × ℝ => p.1) (𝓝[>] 0 ×ˢ atTop) (𝓝[>] 0) := tendsto_fst
  exact (((((tendsto_lPairRep ht).comp hf).add ((tendsto_selfInRep ht).comp hf)).add
    ((tendsto_cornInRep ht).comp hf)).add (tendsto_xReg ht.le)).add
    ((tendsto_scOutRep ht).comp hf)

end QED.ChainProof.SetCK
