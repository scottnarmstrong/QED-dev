/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKPairF
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Set (c), Stage K: the per-node dispersion relation of the L pair

Helper level (no frozen statement). For a node `x ∈ (0, 1)` put `p = x/(1-x)`. The pair integrand
`F(x, u) = α log u + β log(u + x) + γ Li₂(1 - p/u) + δ` (`pairFe`) is, as a function of `u > 0`,

`F(x, u) = e₁(x)/u + ∫₀^∞ σ_x(v)/(v + u) dv`,

with the discontinuity `σ_x(v) = -(α(x, -v) + β(x, -v) [v > x] + γ(x, -v) log(1 + p/v))`
(`dispSig`) and the pole residue `e₁(x) = x² log(1-x) - x²(3x² - 18x + 14)/(4(x - 1))` (`dispE1`).
This file gives the closed-form antiderivative of `σ_x(v)/(v + u)` in `v`: `dispPsi1` on `v < x`
and `dispPsi1 + dispJump` on `v > x`, with derivatives (`hasDerivAt_dispPsi1`,
`hasDerivAt_dispJump`), the limit at `v = 0⁺` (`tendsto_dispPsi1_zero`), the limit at `v → ∞`
(`tendsto_dispPsi2_atTop`) and the evaluation (`disp_value`):

`Ψ₂(∞) - (Ψ₂(x) - Ψ₁(x)) - Ψ₁(0⁺) = F(x, u) - e₁(x)/u`.

The `dilog` part of the antiderivative is `D(v) = Li₂((u - p)/(v + u)) - Li₂(u/(v + u))` (`dispD`),
with `D' = log(1 + p/v)/(v + u)`. The point `u = p` (photon mass² `t = x`) is excluded: `α` has a
removable pole there.
-/

@[expose] public section

namespace QED.ChainProof.SetCK

open Real Set Filter Topology QED.TwoLoop.UnitXClose QED.TwoLoop.UnitXXi QED.Polylog

/-- The coefficient of `log (v + p)` in `Ψ₁`. -/
noncomputable def dispC2 (x u : ℝ) : ℝ :=
  -x*(-1 + x)*(-29*x ^ 2 - 18*u ^ 2 - 4*u + 6*x + 9*x ^ 3 - 48*u*x ^ 2 - 18*u ^ 2*x ^ 2 +
    6*u*x ^ 3 + 36*x*u ^ 2 + 46*u*x)/(4*(x - u + u*x) ^ 2)

/-- The coefficient of `log v` in the jump `Ψ₂ - Ψ₁`. -/
noncomputable def dispB2 (x u : ℝ) : ℝ :=
  x ^ 2*(-2 - 20*u - 4*x + 7*x ^ 2 + 20*u*x)/(12*u ^ 2*(-1 + x))

/-- The linear coefficient of the polynomial part. -/
noncomputable def dispK (x u : ℝ) : ℝ := -u*x + u + 4*x ^ 2 - 10*x + 4

/-- The residue of `Ψ₁` at `v = -p`. -/
noncomputable def dispR1 (x u : ℝ) : ℝ := -x ^ 2*(x - 1)*(3*x - 2)/(4*(x - u + u*x))

/-- The residue of the jump at `v = 0`. -/
noncomputable def dispB3 (x u : ℝ) : ℝ := x ^ 2*(7*x ^ 2 - 4*x - 2)/(12*u*(x - 1))

/-- The dilogarithm part `D(v) = Li₂((u - p)/(v + u)) - Li₂(u/(v + u))`. -/
noncomputable def dispD (x u v : ℝ) : ℝ :=
  dilogI ((u - x / (1 - x)) / (v + u)) - Li₂ (u / (v + u))

/-- The antiderivative `Ψ₁` of `σ_x(v)/(v + u)` on `0 < v < x`. -/
noncomputable def dispPsi1 (x u v : ℝ) : ℝ :=
  -pairAl x u * log (v + u) + dispC2 x u * log (v + x / (1 - x)) -
    9 * (x - 1) ^ 2 / 2 * (v * log (1 + x / (1 - x) / v)) - pairGa x u * dispD x u v -
    v ^ 2 / (24 * x) - v * dispK x u / (12 * x * (x - 1)) + dispR1 x u / (v + x / (1 - x))

/-- The jump `Ψ₂ - Ψ₁`, an antiderivative of the `β` part `-β(x, -v)/(v + u)`. -/
noncomputable def dispJump (x u v : ℝ) : ℝ :=
  -pairBe x u * log (v + u) + dispB2 x u * log v + v ^ 2 / (24 * x) +
    v * dispK x u / (12 * x * (x - 1)) + dispB3 x u / v

/-- The value `Ψ₁(0⁺)`. -/
noncomputable def dispPsi10 (x u : ℝ) : ℝ :=
  -pairAl x u * log u + dispC2 x u * log (x / (1 - x)) -
    pairGa x u * (dilogI ((u - x / (1 - x)) / u) - π ^ 2 / 6) + dispR1 x u / (x / (1 - x))

/-- The discontinuity `σ_x(v)` of the pair integrand across `u = -v`. -/
noncomputable def dispSig (x v : ℝ) : ℝ :=
  -(pairAl x (-v) + (if x < v then pairBe x (-v) else 0) +
    pairGa x (-v) * log (1 + x / (1 - x) / v))

/-- The residue `e₁(x)` of the pair integrand at `u = 0`. -/
noncomputable def dispE1 (x : ℝ) : ℝ :=
  x ^ 2 * log (1 - x) - x ^ 2 * (3*x ^ 2 - 18*x + 14)/(4*(x - 1))

section

variable {x u v : ℝ}

theorem disp_logs (hx : x ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) (hv : 0 < v) :
    log (1 + x / (1 - x) / v) = log (v + x / (1 - x)) - log v ∧
      log (1 - (u - x / (1 - x)) / (v + u)) = log (v + x / (1 - x)) - log (v + u) ∧
      log (1 - u / (v + u)) = log v - log (v + u) := by
  have hp : 0 < x / (1 - x) := div_pos hx.1 (by linarith [hx.2])
  have hvu : 0 < v + u := by linarith
  have hvp : 0 < v + x / (1 - x) := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [← log_div hvp.ne' hv.ne']; congr 1; field_simp
  · rw [← log_div hvp.ne' hvu.ne']; congr 1; field_simp; ring
  · rw [← log_div hv.ne' hvu.ne']; congr 1; field_simp; ring

theorem hasDerivAt_dispD (hx : x ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) (hup : u ≠ x / (1 - x))
    (hv : 0 < v) : HasDerivAt (dispD x u) (log (1 + x / (1 - x) / v) / (v + u)) v := by
  have hp : 0 < x / (1 - x) := div_pos hx.1 (by linarith [hx.2])
  have hvu : 0 < v + u := by linarith
  have hf : HasDerivAt (fun w => (u - x / (1 - x)) / (w + u))
      ((0 * (v + u) - (u - x / (1 - x)) * 1) / (v + u) ^ 2) v :=
    (hasDerivAt_const v _).div ((hasDerivAt_id' v).add_const u) hvu.ne'
  have hf1 : (u - x / (1 - x)) / (v + u) < 1 := by
    rw [div_lt_one hvu]; linarith
  have hf0 : (u - x / (1 - x)) / (v + u) ≠ 0 :=
    div_ne_zero (sub_ne_zero.2 hup) hvu.ne'
  have hg : HasDerivAt (fun w => u / (w + u)) ((0 * (v + u) - u * 1) / (v + u) ^ 2) v :=
    (hasDerivAt_const v _).div ((hasDerivAt_id' v).add_const u) hvu.ne'
  have hg0 : 0 < u / (v + u) := div_pos hu hvu
  have hg1 : |u / (v + u)| < 1 := by
    rw [abs_of_pos hg0, div_lt_one hvu]; linarith
  have H := (hasDerivAt_dilogI_comp hf hf1 hf0).sub ((hasDerivAt_Li₂ hg1 hg0.ne').comp v hg)
  convert H using 1
  · funext w
    simp [dispD]
  obtain ⟨e1, e2, e3⟩ := disp_logs hx hu hv
  rw [e1, e2, e3]
  have hvp : 0 < v + x / (1 - x) := by linarith
  have hsub : u - x / (1 - x) ≠ 0 := sub_ne_zero.2 hup
  field_simp
  ring

theorem disp_rat (hx : x ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) (hup : u ≠ x / (1 - x)) (hv : 0 < v) :
    -pairAl x u / (v + u) + dispC2 x u * (1 - x) / (v * (1 - x) + x) +
      9 * (x - 1) ^ 2 / 2 * (x / (v * (1 - x) + x)) - 2 * v / (24 * x) -
      dispK x u / (12 * x * (x - 1)) - dispR1 x u * (1 - x) ^ 2 / (v * (1 - x) + x) ^ 2 =
      -pairAl x (-v) / (v + u) := by
  have hx0 := hx.1.ne'
  have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
  have hxm : -1 + x ≠ 0 := fun h => hx1 (by linarith)
  have hxm' : x - 1 ≠ 0 := fun h => hx1 (by linarith)
  have hvu : v + u ≠ 0 := by linarith
  have hvp : v * (1 - x) + x ≠ 0 := by nlinarith [hx.1, hx.2]
  have hvx : x - -v + -v * x ≠ 0 := by nlinarith [hx.1, hx.2]
  have hup' : x - u + u * x ≠ 0 := by
    intro h; apply hup; field_simp; linarith
  have hup'' : u * x - u + x ≠ 0 := fun h => hup' (by linarith)
  have h1 : x - u + x * u ≠ 0 := fun h => hup' (by linarith)
  have h2 : u * (x - 1) + x ≠ 0 := fun h => hup' (by linarith)
  have h3 : x - -v + -(x * v) ≠ 0 := fun h => hvx (by linarith)
  unfold pairAl dispC2 dispK dispR1
  field_simp
  ring

theorem disp_gam (hu : 0 < u) (hv : 0 < v) :
    9 * (x - 1) ^ 2 / 2 + pairGa x u / (v + u) = pairGa x (-v) / (v + u) := by
  have hvu : v + u ≠ 0 := by linarith
  unfold pairGa
  field_simp
  ring

theorem hasDerivAt_dispPsi1 (hx : x ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) (hup : u ≠ x / (1 - x))
    (hv : 0 < v) :
    HasDerivAt (dispPsi1 x u)
      (-(pairAl x (-v) + pairGa x (-v) * log (1 + x / (1 - x) / v)) / (v + u)) v := by
  have hx0 := hx.1
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hp : 0 < x / (1 - x) := div_pos hx0 hx1
  have hvu : 0 < v + u := by linarith
  have hvp : 0 < v + x / (1 - x) := by linarith
  have dLu : HasDerivAt (fun w => log (w + u)) (1 / (v + u)) v := by
    simpa using ((hasDerivAt_id' v).add_const u).log hvu.ne'
  have dLp : HasDerivAt (fun w => log (w + x / (1 - x))) (1 / (v + x / (1 - x))) v := by
    simpa using ((hasDerivAt_id' v).add_const (x / (1 - x))).log hvp.ne'
  have dq : HasDerivAt (fun w => 1 + x / (1 - x) / w)
      ((0 * v - x / (1 - x) * 1) / v ^ 2) v :=
    ((hasDerivAt_const v (x / (1 - x))).div (hasDerivAt_id' v) hv.ne').const_add 1
  have hq : 0 < 1 + x / (1 - x) / v := by positivity
  have dR : HasDerivAt (fun w => w * log (1 + x / (1 - x) / w))
      (1 * log (1 + x / (1 - x) / v) +
        v * (((0 * v - x / (1 - x) * 1) / v ^ 2) / (1 + x / (1 - x) / v)))
      v := (hasDerivAt_id' v).mul (dq.log hq.ne')
  have dV2 : HasDerivAt (fun w : ℝ => w ^ 2 / (24 * x)) (2 * v / (24 * x)) v := by
    simpa using ((hasDerivAt_id' v).pow 2).div_const (24 * x)
  have dV1 : HasDerivAt (fun w => w * dispK x u / (12 * x * (x - 1)))
      (dispK x u / (12 * x * (x - 1))) v := by
    simpa using ((hasDerivAt_id' v).mul_const (dispK x u)).div_const (12 * x * (x - 1))
  have dP : HasDerivAt (fun w => dispR1 x u / (w + x / (1 - x)))
      ((0 * (v + x / (1 - x)) - dispR1 x u * 1) / (v + x / (1 - x)) ^ 2) v :=
    (hasDerivAt_const v _).div ((hasDerivAt_id' v).add_const _) hvp.ne'
  have dD := hasDerivAt_dispD hx hu hup hv
  have H := ((((((dLu.const_mul (-pairAl x u)).add (dLp.const_mul (dispC2 x u))).sub
    (dR.const_mul (9 * (x - 1) ^ 2 / 2))).sub (dD.const_mul (pairGa x u))).sub dV2).sub dV1).add dP
  convert H using 1
  · funext w
    simp only [dispPsi1, Pi.add_apply, Pi.sub_apply]
  have hvp' : v * (1 - x) + x ≠ 0 := by nlinarith
  have h1 : 1 / (v + x / (1 - x)) = (1 - x) / (v * (1 - x) + x) := by
    field_simp
  have h2 : v * ((0 * v - x / (1 - x) * 1) / v ^ 2 / (1 + x / (1 - x) / v)) =
      -(x / (v * (1 - x) + x)) := by
    field_simp
    ring
  have h3 : (0 * (v + x / (1 - x)) - dispR1 x u * 1) / (v + x / (1 - x)) ^ 2 =
      -(dispR1 x u * (1 - x) ^ 2 / (v * (1 - x) + x) ^ 2) := by
    field_simp
    ring
  rw [h1, h2, h3]
  have hr := disp_rat hx hu hup hv
  have hg := disp_gam (x := x) hu hv
  linear_combination -hr + log (1 + x / (1 - x) / v) * hg

theorem hasDerivAt_dispJump (hx : x ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) (hv : 0 < v) :
    HasDerivAt (dispJump x u) (-pairBe x (-v) / (v + u)) v := by
  have hx0 := hx.1
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hvu : 0 < v + u := by linarith
  have dLu : HasDerivAt (fun w => log (w + u)) (1 / (v + u)) v := by
    simpa using ((hasDerivAt_id' v).add_const u).log hvu.ne'
  have dLv : HasDerivAt log (1 / v) v := by simpa using hasDerivAt_log hv.ne'
  have dV2 : HasDerivAt (fun w : ℝ => w ^ 2 / (24 * x)) (2 * v / (24 * x)) v := by
    simpa using ((hasDerivAt_id' v).pow 2).div_const (24 * x)
  have dV1 : HasDerivAt (fun w => w * dispK x u / (12 * x * (x - 1)))
      (dispK x u / (12 * x * (x - 1))) v := by
    simpa using ((hasDerivAt_id' v).mul_const (dispK x u)).div_const (12 * x * (x - 1))
  have dP : HasDerivAt (fun w => dispB3 x u / w) ((0 * v - dispB3 x u * 1) / v ^ 2) v :=
    (hasDerivAt_const v _).div (hasDerivAt_id' v) hv.ne'
  have H := ((((dLu.const_mul (-pairBe x u)).add (dLv.const_mul (dispB2 x u))).add dV2).add
    dV1).add dP
  convert H using 1
  · funext w
    simp only [dispJump, Pi.add_apply]
  unfold pairBe dispB2 dispK dispB3
  have hx0' := hx0.ne'
  have hx1' := hx1.ne'
  have hxm : -1 + x ≠ 0 := fun h => hx1' (by linarith)
  have hxm' : x - 1 ≠ 0 := fun h => hx1' (by linarith)
  have hu' := hu.ne'
  have hv' := hv.ne'
  field_simp
  ring


theorem tendsto_dispPsi1_zero (hx : x ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    Tendsto (dispPsi1 x u) (𝓝[>] 0) (𝓝 (dispPsi10 x u)) := by
  have hp : 0 < x / (1 - x) := div_pos hx.1 (by linarith [hx.2])
  set p := x / (1 - x) with hpdef
  have hR : Tendsto (fun v => v * log (1 + p / v)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun v => v * log (v + p)) (𝓝[>] 0) (𝓝 (0 * log (0 + p))) :=
      ((continuousAt_id.mul ((continuousAt_id.add continuousAt_const).log
        (by show (0 : ℝ) + p ≠ 0; rw [zero_add]; exact hp.ne'))).tendsto).mono_left
          nhdsWithin_le_nhds
    have h2 : Tendsto (fun v => v * log v) (𝓝[>] 0) (𝓝 (0 * log 0)) :=
      (continuous_mul_log.tendsto 0).mono_left nhdsWithin_le_nhds
    have := h1.sub h2
    simp only [zero_mul, sub_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with v hv
    have hv' : 0 < v := hv
    have hvp : 0 < v + p := by linarith
    rw [show 1 + p / v = (v + p) / v by field_simp, log_div hvp.ne' hv'.ne']
    ring
  have hD : Tendsto (dispD x u) (𝓝[>] 0) (𝓝 (dilogI ((u - p) / u) - π ^ 2 / 6)) := by
    have hA : Tendsto (fun v => dilogI ((u - p) / (v + u))) (𝓝[>] 0)
        (𝓝 (dilogI ((u - p) / (0 + u)))) := by
      have hc : ContinuousAt (fun v : ℝ => (u - p) / (v + u)) 0 :=
        continuousAt_const.div (continuousAt_id.add continuousAt_const) (by simpa using hu.ne')
      have h0 : (u - p) / (0 + u) ∈ Iio (1 : ℝ) := by
        rw [zero_add, mem_Iio, div_lt_one hu]; linarith
      exact (ContinuousAt.comp (f := fun v : ℝ => (u - p) / (v + u)) (g := dilogI)
        (continuousOn_dilogI.continuousAt (isOpen_Iio.mem_nhds h0)) hc).tendsto.mono_left
          nhdsWithin_le_nhds
    have hB : Tendsto (fun v => Li₂ (u / (v + u))) (𝓝[>] 0) (𝓝 (π ^ 2 / 6)) := by
      have hc : Tendsto (fun v : ℝ => u / (v + u)) (𝓝[>] 0) (𝓝[Icc (-1) 1] 1) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have : ContinuousAt (fun v : ℝ => u / (v + u)) 0 :=
            continuousAt_const.div (continuousAt_id.add continuousAt_const)
              (by simpa using hu.ne')
          have h1 := this.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
          simpa [hu.ne'] using h1
        · filter_upwards [self_mem_nhdsWithin] with v hv
          have hv' : 0 < v := hv
          have hvu : 0 < v + u := by linarith
          refine ⟨?_, ?_⟩
          · have : 0 ≤ u / (v + u) := (div_pos hu hvu).le
            linarith
          · rw [div_le_one hvu]; linarith
      have := (continuousOn_Li₂ 1 ⟨by norm_num, le_rfl⟩).tendsto.comp hc
      rwa [Li₂_one] at this
    have := hA.sub hB
    rw [zero_add] at this
    exact this
  have hc : ContinuousAt (fun v => -pairAl x u * log (v + u) + dispC2 x u * log (v + p) -
      v ^ 2 / (24 * x) - v * dispK x u / (12 * x * (x - 1)) + dispR1 x u / (v + p)) 0 := by
    have h1 : (0 : ℝ) + u ≠ 0 := by simpa using hu.ne'
    have h2 : (0 : ℝ) + p ≠ 0 := by rw [zero_add]; exact hp.ne'
    exact ((((continuousAt_const.mul ((continuousAt_id.add continuousAt_const).log h1)).add
      (continuousAt_const.mul ((continuousAt_id.add continuousAt_const).log h2))).sub
      ((continuousAt_id.pow 2).div_const _)).sub ((continuousAt_id.mul continuousAt_const).div_const
        _)).add (continuousAt_const.div (continuousAt_id.add continuousAt_const) h2)
  have H := ((hc.tendsto.mono_left nhdsWithin_le_nhds).sub
    (hR.const_mul (9 * (x - 1) ^ 2 / 2))).sub (hD.const_mul (pairGa x u))
  have e : dispPsi10 x u = -pairAl x u * log (0 + u) + dispC2 x u * log (0 + p) -
      0 ^ 2 / (24 * x) - 0 * dispK x u / (12 * x * (x - 1)) + dispR1 x u / (0 + p) -
      9 * (x - 1) ^ 2 / 2 * 0 - pairGa x u * (dilogI ((u - p) / u) - π ^ 2 / 6) := by
    simp only [dispPsi10, zero_add, ← hpdef]
    ring
  rw [e]
  refine H.congr fun v => ?_
  simp only [dispPsi1, ← hpdef]
  ring

theorem tendsto_dispPsi2_atTop (hx : x ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) (hup : u ≠ x / (1 - x)) :
    Tendsto (fun v => dispPsi1 x u v + dispJump x u v) atTop
      (𝓝 (-9 * (x - 1) ^ 2 / 2 * (x / (1 - x)))) := by
  have hp : 0 < x / (1 - x) := div_pos hx.1 (by linarith [hx.2])
  set p := x / (1 - x) with hpdef
  have hsum : -pairAl x u - pairBe x u + dispC2 x u + dispB2 x u = 0 := by
    have hx0 := hx.1.ne'
    have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
    have hxm : -1 + x ≠ 0 := fun h => hx1 (by linarith)
    have hu' := hu.ne'
    have hup' : x - u + u * x ≠ 0 := by
      intro h; apply hup; rw [hpdef]; field_simp; linarith
    have h1 : x - u + x * u ≠ 0 := fun h => hup' (by linarith)
    have h2 : u * (x - 1) + x ≠ 0 := fun h => hup' (by linarith)
    unfold pairAl pairBe dispC2 dispB2
    field_simp
    ring
  have hL : ∀ c : ℝ, Tendsto (fun v : ℝ => log (1 + c / v)) atTop (𝓝 0) := fun c => by
    have h := ((tendsto_const_nhds (x := c)).div_atTop tendsto_id).const_add 1
    rw [add_zero] at h
    have := (continuousAt_log one_ne_zero).tendsto.comp h
    rw [log_one] at this
    exact this
  have hR := Real.tendsto_mul_log_one_add_div_atTop p
  have hD : Tendsto (dispD x u) atTop (𝓝 0) := by
    have h1 : Tendsto (fun v => (u - p) / (v + u)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_id)
    have h2 : Tendsto (fun v => u / (v + u)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_id)
    have c1 : ContinuousAt dilogI 0 :=
      continuousOn_dilogI.continuousAt (isOpen_Iio.mem_nhds (by norm_num))
    have c2 : ContinuousAt Li₂ 0 :=
      continuousOn_Li₂.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))
    have := (c1.tendsto.comp h1).sub (c2.tendsto.comp h2)
    simp only [dilogI_zero, Li₂_zero, sub_zero] at this
    refine this.congr fun v => ?_
    simp only [dispD, Function.comp, ← hpdef]
  have hr1 : Tendsto (fun v => dispR1 x u / (v + p)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_id)
  have hb3 : Tendsto (fun v => dispB3 x u / v) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have H := (((((hL u).const_mul (-pairAl x u - pairBe x u)).add
    ((hL p).const_mul (dispC2 x u))).sub (hR.const_mul (9 * (x - 1) ^ 2 / 2))).sub
      (hD.const_mul (pairGa x u))).add (hr1.add hb3)
  have e : -9 * (x - 1) ^ 2 / 2 * p = (-pairAl x u - pairBe x u) * 0 + dispC2 x u * 0 -
      9 * (x - 1) ^ 2 / 2 * p - pairGa x u * 0 + (0 + 0) := by ring
  rw [e]
  refine H.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with v hv
  have hvu : 0 < v + u := by linarith
  have hvp : 0 < v + p := by linarith
  have l1 : log (v + u) = log v + log (1 + u / v) := by
    rw [← log_mul hv.ne' (by positivity)]; congr 1; field_simp
  have l2 : log (v + p) = log v + log (1 + p / v) := by
    rw [← log_mul hv.ne' (by positivity)]; congr 1; field_simp
  simp only [dispPsi1, dispJump, ← hpdef, l1, l2]
  linear_combination -log v * hsum

/-- **The evaluation**: `Ψ₂(∞) - (Ψ₂ - Ψ₁)(x) - Ψ₁(0⁺) = F(x, u) - e₁(x)/u`. -/
theorem disp_value (hx : x ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) (hup : u ≠ x / (1 - x)) :
    -9 * (x - 1) ^ 2 / 2 * (x / (1 - x)) - dispJump x u x - dispPsi10 x u =
      pairFe x u - dispE1 x / u := by
  have hx0 := hx.1
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have e1 : log (x / (1 - x)) = log x - log (1 - x) := log_div hx0.ne' hx1.ne'
  have e2 : (u - x / (1 - x)) / u = 1 - x / ((1 - x) * u) := by
    field_simp
  have e3 : log (x + u) = log (u + x) := by rw [add_comm]
  unfold dispJump dispPsi10 pairFe dispE1
  rw [e1, e2, e3]
  have hx0' := hx0.ne'
  have hx1' := hx1.ne'
  have hxm : -1 + x ≠ 0 := fun h => hx1' (by linarith)
  have hxm' : x - 1 ≠ 0 := fun h => hx1' (by linarith)
  have hu' := hu.ne'
  have hup' : x - u + u * x ≠ 0 := by
    intro h; apply hup; field_simp; linarith
  have h1 : x - u + x * u ≠ 0 := fun h => hup' (by linarith)
  have h2 : u * (x - 1) + x ≠ 0 := fun h => hup' (by linarith)
  have h3 : u * x - u + x ≠ 0 := fun h => hup' (by linarith)
  have h4 : x + x * u - u ≠ 0 := fun h => hup' (by linarith)
  have hX : -dispB2 x u - dispC2 x u = pairDx x u := by
    unfold dispB2 dispC2 pairDx
    field_simp
    ring
  have hL1 : dispC2 x u = pairD1 x u - x ^ 2 / u := by
    unfold dispC2 pairD1
    field_simp
    ring
  have h0 : -9 * (x - 1) ^ 2 / 2 * (x / (1 - x)) -
      (x ^ 2 / (24 * x) + x * dispK x u / (12 * x * (x - 1)) + dispB3 x u / x) -
      pairGa x u * (π ^ 2 / 6) - dispR1 x u / (x / (1 - x)) =
      pairD0 x u + x ^ 2 * (3 * x ^ 2 - 18 * x + 14) / (4 * (x - 1)) / u := by
    unfold dispK dispB3 pairGa dispR1 pairD0
    field_simp
    ring
  linear_combination log x * hX + log (1 - x) * hL1 + h0

end

end QED.ChainProof.SetCK
