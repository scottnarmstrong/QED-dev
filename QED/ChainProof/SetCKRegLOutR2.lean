/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKRegLOut
public import QED.TwoLoop.UnitLClose

/-!
# Set (c), Stage K: the ladder with a massive outer photon at finite Pauli–Villars mass

Helper level (no frozen statement). In the ladder placement `L(0, t)` (photon of mass² `t` outside
the vertex subgraph) the massless line is the inner photon. With the Pauli–Villars pair `(λ, Λ)`
on it and its own counterterm `δ₁(λ, Λ) = -∫CT(λ) + ∫CT(Λ)` (`ladderDeltaOne`) times
`F₂(√t)`, the unit is (layer R2 of the M5 plan)

`lOutReg t λ Λ = ∫₀¹ dY [∫₀¹ dx (G(√t, λ) - G(√t, Λ)) - F₂(√t) (CT(λ; Y) - CT(Λ; Y))]`.

With `e₁ = G(√t, Λ) + E(√t, Λ)` of Phase 4 (`ladderE1`, bounded by `6(1 + ℓ)/√M_Λ` at any outer
mass), `∫ E dx = (Y/2) log M_Λ F₂(√t) + (Y²(1-Y)/M_Λ) J(√t)` and `S(Λ) = ∫ ((Y/2) log M_Λ + CT(Λ))`:

* **`lOutReg_eq`**: `lOutReg t λ Λ = lOutRep t λ + lOutErr t Λ`,
  `lOutErr t Λ = -∬ e₁(√t, Λ) + F₂(√t) S(Λ) + F₂(Λ) J(√t)` (independent of `λ`);
* **`tendsto_lOutErr`**: `lOutErr t Λ → 0` as `Λ → ∞` (the inner `log M_Λ` cancels inside
  `S(Λ)`);
* **`tendsto_lOutReg`**: `lOutReg t λ Λ + F₂(√t) log λ → lOuter t` jointly as
  `(λ, Λ) → (0⁺, ∞)`;
* **`tendsto_regOuterBound`**: the Phase 4 bound on `∬ G(Λ, μ)`, valid for every inner mass
  `0 < μ ≤ Λ`, tends to `0`: units with the outer line at a Pauli–Villars mass `Λ` vanish
  uniformly in the inner mass (this covers outer-line partners at `Λ` with bounded coefficients).
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitLLink

/-- **The ladder `L(0, t)` at finite Pauli–Villars mass** (pair `(λ, Λ)` on the inner line). -/
noncomputable def lOutReg (t lam Lam : ℝ) : ℝ :=
  ∫ Y in (0 : ℝ)..1, ((∫ x in (0 : ℝ)..1, (ladderGm (√t) lam Y x - ladderGm (√t) Lam Y x)) -
    oneLoopF2 1 (√t) * (ladderCtBracket lam Y - ladderCtBracket Lam Y))

/-- The `Λ`-dependent remainder `-∬ e₁(√t, Λ) + F₂(√t) S(Λ) + F₂(Λ) J(√t)`. -/
noncomputable def lOutErr (t Lam : ℝ) : ℝ :=
  -(∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderE1 (√t) Lam Y x) +
    oneLoopF2 1 (√t) * ladderS1 Lam + oneLoopF2 1 Lam * outerSoftJ (√t)

theorem lOutReg_integrand_eq {t lam Lam Y : ℝ} (ht : 0 < t) (hlam1 : lam ^ 2 ≤ 1)
    (hLam : 1 ≤ Lam) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    (∫ x in (0 : ℝ)..1, (ladderGm (√t) lam Y x - ladderGm (√t) Lam Y x)) -
        oneLoopF2 1 (√t) * (ladderCtBracket lam Y - ladderCtBracket Lam Y) =
      ((∫ x in (0 : ℝ)..1, ladderGm (√t) lam Y x) - oneLoopF2 1 (√t) * ladderCtBracket lam Y) +
        (-(∫ x in (0 : ℝ)..1, ladderE1 (√t) Lam Y x) +
          oneLoopF2 1 (√t) * (Y / 2 * log (ladderInnerMass 1 Lam Y) + ladderCtBracket Lam Y) +
          Y ^ 2 * (1 - Y) * 1 ^ 2 / ladderInnerMass 1 Lam Y * outerSoftJ (√t)) := by
  have hs : 0 < √t := sqrt_pos.2 ht
  have hG : (fun x => ladderGm (√t) Lam Y x) =
      fun x => ladderE1 (√t) Lam Y x - ladderE1Explicit (√t) Lam Y x :=
    funext fun x => by unfold ladderE1; ring
  have iE1 := (e1_x_bound hs hLam hY).1
  obtain ⟨iE, hE⟩ := integral_ladderE1Explicit hs Lam Y
  have iGl := intervalIntegrable_ladderGm_outer ht hlam1 hY
  have iGL : IntervalIntegrable (fun x => ladderGm (√t) Lam Y x) volume 0 1 := by
    rw [hG]; exact iE1.sub iE
  rw [intervalIntegral.integral_sub iGl iGL, hG, intervalIntegral.integral_sub iE1 iE, hE]
  ring

/-- **`L(0, t)` at finite `Λ` is the `Λ = ∞` form plus a `λ`-independent remainder.** -/
theorem lOutReg_eq {t lam Lam : ℝ} (ht : 0 < t) (hlam : 0 < lam) (hlam1 : lam ^ 2 ≤ 1)
    (hLam : 1 ≤ Lam) : lOutReg t lam Lam = lOutRep t lam + lOutErr t Lam := by
  have hs : 0 < √t := sqrt_pos.2 ht
  have hLam0 : 0 < Lam := by linarith
  have i1 : IntervalIntegrable (fun Y => (∫ x in (0 : ℝ)..1, ladderGm (√t) lam Y x) -
      oneLoopF2 1 (√t) * ladderCtBracket lam Y) volume 0 1 :=
    (intervalIntegrable_integral_ladderGm_outer ht hlam1).sub
      ((intervalIntegrable_ladderCtBracket hlam).const_mul _)
  have iE1 := (e1_Y_bound hs hLam).1
  have ia := intervalIntegrable_half_log hLam0
  have iCL := intervalIntegrable_ladderCtBracket hLam0
  have ib : IntervalIntegrable (fun Y => Y ^ 2 * (1 - Y) * 1 ^ 2 / ladderInnerMass 1 Lam Y)
      volume 0 1 := (continuousOn_ladderInnerMass_Y hLam0 _ (by fun_prop)).intervalIntegrable
  have iE1n : IntervalIntegrable (fun Y => -(∫ x in (0 : ℝ)..1, ladderE1 (√t) Lam Y x))
      volume 0 1 := iE1.neg
  have iac : IntervalIntegrable (fun Y => oneLoopF2 1 (√t) *
      (Y / 2 * log (ladderInnerMass 1 Lam Y) + ladderCtBracket Lam Y)) volume 0 1 :=
    (ia.add iCL).const_mul _
  have ibJ : IntervalIntegrable (fun Y => Y ^ 2 * (1 - Y) * 1 ^ 2 / ladderInnerMass 1 Lam Y *
      outerSoftJ (√t)) volume 0 1 := ib.mul_const _
  have i2 := (iE1n.add iac).add ibJ
  have e : lOutReg t lam Lam = ∫ Y in (0 : ℝ)..1,
      (((∫ x in (0 : ℝ)..1, ladderGm (√t) lam Y x) - oneLoopF2 1 (√t) * ladderCtBracket lam Y) +
        (-(∫ x in (0 : ℝ)..1, ladderE1 (√t) Lam Y x) +
          oneLoopF2 1 (√t) * (Y / 2 * log (ladderInnerMass 1 Lam Y) + ladderCtBracket Lam Y) +
          Y ^ 2 * (1 - Y) * 1 ^ 2 / ladderInnerMass 1 Lam Y * outerSoftJ (√t))) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    exact lOutReg_integrand_eq ht hlam1 hLam ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩
  rw [e, intervalIntegral.integral_add i1 i2]
  have e2 : ∫ Y in (0 : ℝ)..1, (-(∫ x in (0 : ℝ)..1, ladderE1 (√t) Lam Y x) +
      oneLoopF2 1 (√t) * (Y / 2 * log (ladderInnerMass 1 Lam Y) + ladderCtBracket Lam Y) +
      Y ^ 2 * (1 - Y) * 1 ^ 2 / ladderInnerMass 1 Lam Y * outerSoftJ (√t)) = lOutErr t Lam := by
    rw [intervalIntegral.integral_add (iE1n.add iac) ibJ,
      intervalIntegral.integral_add iE1n iac, intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
    rfl
  rw [e2]
  rfl

/-- **The remainder vanishes as `Λ → ∞`.** -/
theorem tendsto_lOutErr {t : ℝ} (ht : 0 < t) : Tendsto (lOutErr t) atTop (𝓝 0) := by
  have hs : 0 < √t := sqrt_pos.2 ht
  have h1 : Tendsto (fun Lam => ∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderE1 (√t) Lam Y x)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ tendsto_integral_e1Dom
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Lam hLam
    rw [Real.norm_eq_abs]
    exact (e1_Y_bound hs hLam).2
  have h3 : Tendsto (fun Lam : ℝ => oneLoopF2 1 Lam) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ (tendsto_const_div_sq 1)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with Lam hLam
      exact (oneLoopF2_nonneg_le_one (by linarith)).1
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with Lam hLam
      exact oneLoopF2_le_inv_sq hLam
  have := (h1.neg.add (tendsto_ladderS1.const_mul (oneLoopF2 1 (√t)))).add
    (h3.mul_const (outerSoftJ (√t)))
  simp only [neg_zero, mul_zero, zero_mul, add_zero] at this
  exact this

/-- **The regulator link of `L(0, t)` at finite `Λ`**: for `t > 0`,
`lOutReg t λ Λ + F₂(√t) log λ → lOuter t` as `(λ, Λ) → (0⁺, ∞)` jointly. -/
theorem tendsto_lOutReg {t : ℝ} (ht : 0 < t) :
    Tendsto (fun p : ℝ × ℝ => lOutReg t p.1 p.2 + oneLoopF2 1 (√t) * log p.1)
      (𝓝[>] 0 ×ˢ atTop) (𝓝 (lOuter t)) := by
  have h1 := (tendsto_lOutRep ht).comp
    (tendsto_fst : Tendsto (fun p : ℝ × ℝ => p.1) (𝓝[>] 0 ×ˢ atTop) (𝓝[>] 0))
  have h2 := (tendsto_lOutErr ht).comp
    (tendsto_snd : Tendsto (fun p : ℝ × ℝ => p.2) (𝓝[>] 0 ×ˢ atTop) atTop)
  have := h1.add h2
  rw [add_zero] at this
  refine this.congr' ?_
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝[>] 0 ×ˢ atTop, p.1 ∈ Ioo (0 : ℝ) 1 ∧ 1 ≤ p.2 :=
    ((show ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) 1 from
      Ioo_mem_nhdsGT (by norm_num)).prod_inl _).and
      ((eventually_ge_atTop (1 : ℝ)).prod_inr _)
  filter_upwards [hev] with p hp
  simp only [Function.comp]
  rw [lOutReg_eq ht hp.1.1 (by nlinarith [hp.1.1, hp.1.2]) hp.2]
  ring

/-- **The outer line at a Pauli–Villars mass**: the Phase 4 bound
`|∬ G(Λ, μ)| ≤ ∫ (13 + log Λ + log 2 - log Y - log(1 - Y))/Λ²` (`outer_Y_bound`, every
`0 < μ ≤ Λ`) tends to `0`. -/
theorem tendsto_regOuterBound :
    Tendsto (fun Lam : ℝ => ∫ Y in (0 : ℝ)..1, (13 + log Lam + log 2 - log Y - log (1 - Y)) /
      Lam ^ 2) atTop (𝓝 0) := by
  set K := ∫ Y in (0 : ℝ)..1, (13 + log 2 - log Y - log (1 - Y))
  simp only [integral_outerDom_eq, add_div]
  simpa using tendsto_log_div_sq.add (tendsto_const_div_sq K)

end QED.ChainProof.SetCK
