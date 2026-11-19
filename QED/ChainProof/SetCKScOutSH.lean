/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKScOutSAtom
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G4: the Stieltjes identity for the self-energy part

Helper level (no frozen statement). The self-energy part of G4 (`scOutS`, the outer-massive
self-energy unit with the corner counterterm, `S(0, t) + C_ct(0, t)` at `λ = 0`) satisfies the
`Q`-derivative form of the Stieltjes identity (**`scOutSH_isScOutSHDensity`**):

`scOutS t = ∫₀¹ H_S(X) Q'(X)/(Q(X) + t)² dX` for every `t > 0`,

with `H_S(X) = ∫_{(0,1)²} 1{x < X} (2T + A)(Y, x, Q(X) - Q(x)) d(Y, x) + X³(1 - X)/2`
(`scOutSH`, kernel part `scOutSHk` of `SetCKScOutSFub`, pole part from `SetCKScOutSAtom`).

**Proof.** At every `(Y, x)` of the square, by `scOutSW_integral` and the counterterm node
form `scOutSCt_eq`, `2 scOutSG + A/u + B/u² = ∫₀^∞ (2T + A)/(u + v)² dv + scOutSAt`. Both
terms are integrable on the square (`integral_scOutSKerT`, `integrable_scOutSAt`), so the
iterated integral defining `scOutS` is a square integral, and the two pieces are the node
integrals of `integral_scOutSKerT` and `integral_scOutSAt_square`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink QED.TwoLoop.UnitSCClose

/-- **The G4S weight** `H_S(X)`: the kernel part plus the pole part `X³(1 - X)/2`. -/
noncomputable def scOutSH (X : ℝ) : ℝ := scOutSHk X + X ^ 3 * (1 - X) / 2

/-- **The `Q`-derivative form of the Stieltjes identity for G4S**: for a candidate `H`,
`scOutS t = ∫₀¹ H(X) Q'(X)/(Q(X) + t)² dX` for every `t > 0`. -/
def IsScOutSHDensity (H : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → scOutS t = ∫ X in (0 : ℝ)..1, H X * (setCKdQ X / (setCKQ X + t) ^ 2)

section

variable {t : ℝ}

/-- The counterterm node function is integrable on `(0, 1)`. -/
theorem integrableOn_scOutSCt_integrand (ht : 0 < t) :
    IntegrableOn (fun x => scOutSA x / (setCKQ x + t) + scOutSB x / (setCKQ x + t) ^ 2)
      (Ioo (0 : ℝ) 1) := by
  have hs : 0 < √t := sqrt_pos.2 ht
  have ik := intervalIntegrable_vkIntegrand hs
  have im := intervalIntegrable_vmIntegrand hs
  have i2 := intervalIntegrable_oneLoopF2_integrand one_pos hs
  have j : IntervalIntegrable (fun x => -(5 / 2 * vkIntegrand (√t) x) -
      5 * vmIntegrand (√t) x - 3 * (x ^ 2 * (1 - x) * 1 ^ 2 / ladderInnerMass 1 (√t) x))
      volume 0 1 :=
    ((ik.const_mul _).neg.sub (im.const_mul _)).sub (i2.const_mul _)
  exact (j.1.mono_set Ioo_subset_Ioc_self).congr_fun
    (fun x hx => scOutSCt_integrand_eq ht hx) measurableSet_Ioo

theorem integrableOn_scOutSHk_mul (ht : 0 < t) :
    IntegrableOn (fun X => scOutSHk X * (setCKdQ X / (setCKQ X + t) ^ 2)) (Ioo (0 : ℝ) 1) := by
  refine (integrable_scOutSKerT ht).integral_prod_right.congr
    (Eventually.of_forall fun X => ?_)
  simp only [scOutSKerT, scOutSHk]
  exact integral_mul_const _ _

end

/-- **G4S (Stage K), `Q`-derivative form**: `scOutS t = ∫₀¹ H_S(X) Q'(X)/(Q(X) + t)² dX` for
every `t > 0`. -/
theorem scOutSH_isScOutSHDensity : IsScOutSHDensity scOutSH := fun t ht => by
  set μ := volume.restrict (Ioo (0 : ℝ) 1) with hμ
  set c : ℝ → ℝ := fun x => scOutSA x / (setCKQ x + t) + scOutSB x / (setCKQ x + t) ^ 2
    with hc_def
  have hc : Integrable c μ := integrableOn_scOutSCt_integrand ht
  obtain ⟨hGW, vGW⟩ := integral_scOutSKerT ht
  have hAt := integrable_scOutSAt ht
  obtain ⟨iAt, vAt⟩ := integral_scOutSAt_square ht
  have hpt : ∀ᵐ p ∂(μ.prod μ), 2 * scOutSG t p.1 p.2 + c p.2 =
      scOutSGW t p.1 p.2 + scOutSAt t p.1 p.2 := by
    filter_upwards [ae_mem_square_Ioo] with p hp
    have e := scOutSW_integral ht hp.1 hp.2
    unfold scOutSGW
    rw [e]
    simp only [hc_def, scOutSAt]
    ring
  have hcs : Integrable (fun p : ℝ × ℝ => c p.2) (μ.prod μ) := hc.comp_snd μ
  have hG : Integrable (fun p : ℝ × ℝ => scOutSG t p.1 p.2) (μ.prod μ) := by
    refine (((hGW.add hAt).sub hcs).div_const 2).congr (hpt.mono fun p h => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [← h]
    ring
  have e1 : ∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, scOutSG t Y x =
      ∫ p, scOutSG t p.1 p.2 ∂(μ.prod μ) := by
    rw [integral_prod _ hG, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun Y _ => ?_
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have e2 : scOutSCt t = ∫ p, c p.2 ∂(μ.prod μ) := by
    rw [scOutSCt_eq ht, integral_fun_snd, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
    simp [hμ, Measure.real, hc_def]
  have e3 : 2 * (∫ p, scOutSG t p.1 p.2 ∂(μ.prod μ)) + ∫ p, c p.2 ∂(μ.prod μ) =
      (∫ p, scOutSGW t p.1 p.2 ∂(μ.prod μ)) + ∫ p, scOutSAt t p.1 p.2 ∂(μ.prod μ) := by
    rw [← integral_const_mul, ← integral_add (hG.const_mul 2) hcs, ← integral_add hGW hAt]
    exact integral_congr_ae hpt
  rw [scOutS, e1, e2, e3, vGW, vAt, ← integral_add (integrableOn_scOutSHk_mul ht) iAt,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun X _ => ?_
  simp only [scOutSH]
  ring

end QED.ChainProof.SetCK

end
