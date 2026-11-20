/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKLamOutS
public import QED.ChainProof.SetCKLamOutCReg
public import QED.ChainProof.SetCKRegSum
public import QED.ChainProof.SetCKRegLOutR2

/-!
# Set (c), Stage K: the outer group at finite Pauli–Villars mass

Helper level (no frozen statement). The outer group `S(0, t) + C(0, t)` with the corner
counterterm (outer photon of mass² `t > 0`, the bubble line), with the Pauli–Villars pair
`(λ, Λ)` on its massless inner photon line and the counterterms `δ₂, δ_m, δ₁` as Pauli–Villars
differences, is (layer R2 of the M5 plan)

`scOutReg t λ Λ = scOutSReg t λ Λ + scOutCReg t λ Λ`.

* **`scOutReg_eq`**: `scOutReg t λ Λ = scOutRep t λ - scOutRep t Λ` for `0 < λ`, `λ² ≤ 1 ≤ Λ`:
  the finite-`Λ` unit is the `Λ = ∞` form at `λ` plus a remainder independent of `λ`;
* **`scOutRep_large_eq`**: at the large inner mass the inner subdivergences of the self-energy
  graph (against `δ₂, δ_m`, by `V_k + V_m + F₂ = 0`) and of the corner graph (against `δ₁`:
  `±F₂(√t) ∫₀¹ Y log M_Λ`) cancel, and
  `scOutRep t Λ = 2 ∬ e₁(√t, Λ) - 2 F₂(√t) ∫₀¹ Y²(2 - Y)/(2 M_Λ) + 2 ∫₀¹ lamOutCY t Λ`;
* **`tendsto_scOutRep_atTop`**: `scOutRep t Λ → 0` as `Λ → ∞` (decoupling of the heavy inner
  photon; only the sum `S + C` with all three counterterms decouples);
* **`tendsto_scOutReg`**: **the finite-`Λ` link of the outer group**,
  `scOutReg t λ Λ → scOutS t + scOutC t` jointly as `(λ, Λ) → (0⁺, ∞)`;
* **`tendsto_regKernelPairOut`**: the kernel pair sum with every unit that carries no inner
  bubble-line regulator at finite `Λ` (the crossed pair `xReg`, the ladder `L(0, t)` `lOutReg`,
  the outer group `scOutReg`; the inner-massive `L(t, 0)`, `S(t, 0)`, `C(t, 0)` at `Λ = ∞`)
  tends to `setCKKernelPairSum t` jointly.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology Function

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitLLink QED.TwoLoop.UnitSCLimit

/-- **The outer group at finite Pauli–Villars mass** (pair `(λ, Λ)` on the inner line). -/
noncomputable def scOutReg (t lam Lam : ℝ) : ℝ := scOutSReg t lam Lam + scOutCReg t lam Lam

/-- **The outer group at finite `Λ` is the `Λ = ∞` form plus a `λ`-independent remainder.** -/
theorem scOutReg_eq {t lam Lam : ℝ} (ht : 0 < t) (hl : lam ^ 2 ≤ 1) (hLam : 1 ≤ Lam) :
    scOutReg t lam Lam = scOutRep t lam - scOutRep t Lam := by
  unfold scOutReg scOutRep
  rw [scOutSReg_eq ht hl hLam, scOutCReg_eq ht hl (by linarith)]
  ring

/-- **The outer group at a large inner mass**, with the inner subdivergences cancelled. -/
theorem scOutRep_large_eq {t Lam : ℝ} (ht : 0 < t) (hLam : 1 ≤ Lam) :
    scOutRep t Lam = 2 * (∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, selfE1 (√t) Lam Y x) -
      2 * oneLoopF2 1 (√t) *
        (∫ Y in (0 : ℝ)..1, Y ^ 2 * (2 - Y) / (2 * ladderInnerMass 1 Lam Y)) +
      2 * ∫ Y in (0 : ℝ)..1, lamOutCY t Lam Y := by
  unfold scOutRep
  rw [lamOutS_scOutSRep_eq ht hLam, (lamOutC_scOutCRep_eq ht (by linarith)).2]
  ring

/-- **Decoupling**: the outer group with its inner photon at mass `Λ` vanishes as `Λ → ∞`. -/
theorem tendsto_scOutRep_atTop {t : ℝ} (ht : 0 < t) :
    Tendsto (scOutRep t) atTop (𝓝 0) := by
  have hE : Tendsto (fun Lam => ∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, selfE1 (√t) Lam Y x)
      atTop (𝓝 0) := by
    have hb : Tendsto (fun Lam : ℝ => (20 + 9 * log Lam + 5 * log 2) / Lam ^ 2) atTop (𝓝 0) := by
      have := (tendsto_const_div_sq (20 + 5 * log 2)).add (tendsto_log_div_sq.const_mul 9)
      rw [mul_zero, add_zero] at this
      refine this.congr fun Lam => ?_
      ring
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Lam hLam
    rw [Real.norm_eq_abs]
    exact (lamOutS_E1_bound hLam).2
  have h := ((hE.const_mul 2).sub (tendsto_lamOutS_rat.const_mul (2 * oneLoopF2 1 (√t)))).add
    ((tendsto_integral_lamOutCY ht).const_mul 2)
  simp only [mul_zero, sub_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Lam hLam
  exact (scOutRep_large_eq ht hLam).symm

/-- **The finite-`Λ` link of the outer group**: for `t > 0`,
`scOutReg t λ Λ → scOutS t + scOutC t` as `(λ, Λ) → (0⁺, ∞)` jointly. -/
theorem tendsto_scOutReg {t : ℝ} (ht : 0 < t) :
    Tendsto (fun p : ℝ × ℝ => scOutReg t p.1 p.2) (𝓝[>] 0 ×ˢ atTop)
      (𝓝 (scOutS t + scOutC t)) := by
  have h1 := (tendsto_scOutRep ht).comp
    (tendsto_fst : Tendsto (fun p : ℝ × ℝ => p.1) (𝓝[>] 0 ×ˢ atTop) (𝓝[>] 0))
  have h2 := (tendsto_scOutRep_atTop ht).comp
    (tendsto_snd : Tendsto (fun p : ℝ × ℝ => p.2) (𝓝[>] 0 ×ˢ atTop) atTop)
  have := h1.sub h2
  rw [sub_zero] at this
  refine this.congr' ?_
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝[>] 0 ×ˢ atTop, p.1 ∈ Ioo (0 : ℝ) 1 ∧ 1 ≤ p.2 :=
    ((show ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) 1 from
      Ioo_mem_nhdsGT (by norm_num)).prod_inl _).and
      ((eventually_ge_atTop (1 : ℝ)).prod_inr _)
  filter_upwards [hev] with p hp
  simp only [Function.comp]
  rw [scOutReg_eq ht (by nlinarith [hp.1.1, hp.1.2]) hp.2]

/-- The kernel pair sum with the crossed pair, the ladder `L(0, t)` and the outer group at
finite `Λ`, and the inner-massive placements at `Λ = ∞`. -/
noncomputable def regKernelPairOut (t lam Lam : ℝ) : ℝ :=
  (lInRep t lam + lOutReg t lam Lam) + selfInRep t lam + cornInRep t lam + xReg t lam Lam +
    scOutReg t lam Lam

/-- **The joint link with every outer-group and crossed unit at finite `Λ`**: for `t > 0`,
`regKernelPairOut t λ Λ → setCKKernelPairSum t` as `(λ, Λ) → (0⁺, ∞)`. -/
theorem tendsto_regKernelPairOut {t : ℝ} (ht : 0 < t) :
    Tendsto (fun p : ℝ × ℝ => regKernelPairOut t p.1 p.2) (𝓝[>] 0 ×ˢ atTop)
      (𝓝 (setCKKernelPairSum t)) := by
  rw [setCKKernelPairSum_eq_groups]
  have hf : Tendsto (fun p : ℝ × ℝ => p.1) (𝓝[>] 0 ×ˢ atTop) (𝓝[>] 0) := tendsto_fst
  have hL : Tendsto (fun p : ℝ × ℝ => lInRep t p.1 + lOutReg t p.1 p.2) (𝓝[>] 0 ×ˢ atTop)
      (𝓝 (lPair t)) := by
    have := ((tendsto_lInRep ht).comp hf).add (tendsto_lOutReg ht)
    rw [lPair]
    refine this.congr fun p => ?_
    simp only [Function.comp]
    ring
  exact ((((hL.add ((tendsto_selfInRep ht).comp hf)).add ((tendsto_cornInRep ht).comp hf)).add
    (tendsto_xReg ht.le)).add (tendsto_scOutReg ht))

end QED.ChainProof.SetCK
