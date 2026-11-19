/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKScOutW
public import QED.ChainProof.SetCKOuterL
public import QED.ChainProof.SetCKPairX
public import QED.TwoLoop.UnitSCCloseIR
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G4: the outer-massive self-energy unit with the corner counterterm

Helper level (no frozen statement). Group G4 of the set (c) kernel plan is
`S(0, t) + C(0, t)` with the corner counterterm, the photon of mass² `t > 0` outside the
subdivergent subgraph. It splits into two infrared-finite parts: the self-energy unit with the
corner counterterm (this file, `scOutS`) and the two-loop part of the corner (no counterterm).

**The infrared regrouping.** At inner photon mass `λ`, `M = Y² + (1-Y)λ²`, the counterterms of
`S(0, t)` are `2∫dY [d̄₂ V_k(t) + (d̄₂ - σ) V_m(t)]` (`d̄₂`, `σ` as in `SetCKSelfIn`) and the
corner counterterm is `-2F₂(t) ∫dY Y((Y² + 2Y - 2)/(2M) - log M/2)`. At `λ = 0` the `1/Y` parts
are `2(V_k + V_m + F₂)/Y = 0` (`selfVk_add_selfVm_add_oneLoopF2`); the remaining parts integrate
to `-(5/2) V_k(t) - 5 V_m(t) - 3 F₂(t)` (`scOutSCt`). The two-loop `x`-integrand at `λ = 0` is
`selfGm (√t) 0 Y x + k₂/h²` (`scOutSG`; `k₂/h²` is the inner Pauli–Villars remainder, the engine's
`E - e₀`, scratch `stageK/g4/dS2.py`); it has no `1/Y` singularity at fixed `x`. So

`scOutS t = 2 ∫₀¹ dY ∫₀¹ dx scOutSG t Y x + scOutSCt t`.

Numerically `scOutS 1 = -0.50454859731998391743`, `scOutS 4 = -0.26243446416883242306`
(scratch `stageK/g4/s3.py`), against the regulated values `-0.5045485973199926128` (level 12)
and `-0.26243446414769337995` (level 8) of `S(0, t) + C_ct(0, t)` at `λ² = 10⁻⁴⁰, 10⁻⁵⁰`.

**The `(u + v)⁻²`-form per point** (**`scOutSG_eq`**): with `u = Q(x) + t`, `ρ = x/(1-x)`,
`scOutSG t Y x = ∫₀^∞ T(Y, x, v)/(u + v)² dv - k₂ ρ² log(Y²)/u²` (`scOutST`, from
`scOut_sForm_eq`). The counterterm is a node integral `∫₀¹ (A(x)/u + B(x)/u²) dx` with
`A = x²(5x - 8)`, `B = 5x⁴(x - 3)/(4(x - 1))` (**`scOutSCt_eq`**).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink QED.TwoLoop.UnitSCClose

/-- `ρ(x) = x/(1-x)`, so that `h_t(x) = (Q(x) + t)/ρ(x)`. -/
noncomputable def scOutRho (x : ℝ) : ℝ := x / (1 - x)

/-- The two-loop `x`-integrand of the outer-massive self-energy unit at `λ = 0`. -/
noncomputable def scOutSG (t Y x : ℝ) : ℝ := selfGm (√t) 0 Y x + selfK2 Y x / hOut t x ^ 2

/-- The regular parts of the counterterms: `-(5/2) V_k(t) - 5 V_m(t) - 3 F₂(t)`. -/
noncomputable def scOutSCt (t : ℝ) : ℝ :=
  -(5 / 2 * selfVk (√t)) - 5 * selfVm (√t) - 3 * oneLoopF2 1 (√t)

/-- **The outer-massive self-energy unit with the corner counterterm** at `λ = 0`. -/
noncomputable def scOutS (t : ℝ) : ℝ :=
  2 * (∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, scOutSG t Y x) + scOutSCt t

/-- The `(u + v)⁻²`-weight of `scOutSG` at `(Y, x)`. -/
noncomputable def scOutST (Y x v : ℝ) : ℝ :=
  scOutTg (selfK1 Y x * scOutRho x) (selfK2 Y x * scOutRho x ^ 2)
    (Y ^ 2 * scOutRho x / (Y * (1 - Y))) (-(selfK1 Y x * scOutRho x * log (Y ^ 2))) v

/-- The coefficient of `1/u` of the counterterm node function. -/
noncomputable def scOutSA (x : ℝ) : ℝ := x ^ 2 * (5 * x - 8)

/-- The coefficient of `1/u²` of the counterterm node function. -/
noncomputable def scOutSB (x : ℝ) : ℝ := 5 * x ^ 4 * (x - 3) / (4 * (x - 1))

theorem hOut_eq_div_scOutRho {t x : ℝ} (ht : 0 ≤ t) (hx : x ∈ Ioo (0 : ℝ) 1) :
    hOut t x = (setCKQ x + t) / scOutRho x := by
  rw [hOut, ladderInnerMass_sqrt_div_eq ht hx, scOutRho]
  have : x ≠ 0 := hx.1.ne'
  have : 1 - x ≠ 0 := by linarith [hx.2]
  field_simp

theorem scOutRho_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < scOutRho x :=
  div_pos hx.1 (by linarith [hx.2])

/-- **The `(u + v)⁻²`-form of the two-loop integrand** at `(Y, x)`. -/
theorem scOutSG_eq {t Y x : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    scOutSG t Y x = (∫ v in Ioi 0, scOutST Y x v / (setCKQ x + t + v) ^ 2) -
      selfK2 Y x * scOutRho x ^ 2 * log (Y ^ 2) / (setCKQ x + t) ^ 2 := by
  have hu : 0 < setCKQ x + t := by
    have := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
    linarith
  have hc : 0 < Y * (1 - Y) := mul_pos hY.1 (by linarith [hY.2])
  have hM : 0 < Y ^ 2 := pow_pos hY.1 2
  have h0 : ladderInnerMass 1 0 Y = Y ^ 2 := by unfold ladderInnerMass; ring
  have e := scOut_sForm_eq (k₁ := selfK1 Y x) (k₂ := selfK2 Y x) hc hM (scOutRho_pos hx) hu
  unfold scOutSG selfGm scOutST
  rw [← hOut, h0, hOut_eq_div_scOutRho ht.le hx, e]

/-- The counterterm integrand at a node: `A/u + B/u²`. -/
theorem scOutSCt_integrand_eq {t x : ℝ} (ht : 0 < t) (hx : x ∈ Ioo (0 : ℝ) 1) :
    -(5 / 2 * vkIntegrand (√t) x) - 5 * vmIntegrand (√t) x -
        3 * (x ^ 2 * (1 - x) * 1 ^ 2 / ladderInnerMass 1 (√t) x) =
      scOutSA x / (setCKQ x + t) + scOutSB x / (setCKQ x + t) ^ 2 := by
  have hm : ladderInnerMass 1 (√t) x = (1 - x) * (setCKQ x + t) :=
    ladderInnerMass_sqrt_eq ht.le hx.2
  have hu : 0 < setCKQ x + t := by
    have := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
    linarith
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h1' : x - 1 ≠ 0 := by linarith [hx.2]
  have ht' : √t ^ 2 = t := sq_sqrt ht.le
  unfold vkIntegrand vmIntegrand scOutSA scOutSB
  rw [hm]
  have hq : t = (setCKQ x + t) - x ^ 2 / (1 - x) := by unfold setCKQ; ring
  set u := setCKQ x + t with hudef
  rw [ht', hq]
  have := hu.ne'
  field_simp
  ring

/-- **The counterterm as a node integral.** -/
theorem scOutSCt_eq {t : ℝ} (ht : 0 < t) :
    scOutSCt t = ∫ x in (0 : ℝ)..1,
      (scOutSA x / (setCKQ x + t) + scOutSB x / (setCKQ x + t) ^ 2) := by
  have hs : 0 < √t := sqrt_pos.2 ht
  have ik := intervalIntegrable_vkIntegrand hs
  have im := intervalIntegrable_vmIntegrand hs
  have i2 := intervalIntegrable_oneLoopF2_integrand one_pos hs
  rw [scOutSCt, selfVk, selfVm, oneLoopF2, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_neg]
  have j1 : IntervalIntegrable (fun x => -(5 / 2 * vkIntegrand (√t) x)) volume 0 1 :=
    (ik.const_mul _).neg
  have j2 : IntervalIntegrable (fun x => 5 * vmIntegrand (√t) x) volume 0 1 := im.const_mul _
  have j12 : IntervalIntegrable (fun x => -(5 / 2 * vkIntegrand (√t) x) -
      5 * vmIntegrand (√t) x) volume 0 1 := j1.sub j2
  have j3 : IntervalIntegrable (fun x => 3 * (x ^ 2 * (1 - x) * 1 ^ 2 /
      ladderInnerMass 1 (√t) x)) volume 0 1 := i2.const_mul _
  rw [← intervalIntegral.integral_sub j1 j2, ← intervalIntegral.integral_sub j12 j3]
  refine intervalIntegral.integral_congr_ae ((Measure.ae_ne volume 1).mono fun x h1 hx => ?_)
  rw [uIoc_of_le zero_le_one] at hx
  exact scOutSCt_integrand_eq ht ⟨hx.1, lt_of_le_of_ne hx.2 h1⟩

end QED.ChainProof.SetCK

end
