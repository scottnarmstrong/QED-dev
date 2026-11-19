/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKCrossTW
public import QED.TwoLoop.UnitSCLimitSMasters
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G4: the self-energy `a`-integral as a `(u + v)⁻²`-transform

Helper level (no frozen statement). Group G4 is the outer-massive self-energy and corner pair.
In the self-energy unit with a massless inner photon (`M = Y²`) and outer photon mass² `t`, the
`a`-integrand of eq. (5.1) of `docs/TWO-LOOP-UNITS.md` is
`k₂(a - c)²/(a D²) + k₁(a - c)²/(a² D)`, `D = M + a h`, with `h = h_t(x) = u/ρ`,
`u = Q(x) + t`, `ρ = x/(1-x)`. Substituting `v = M ρ/a`, i.e. `D = (a/ρ)(u + v)`, the
`a`-integral over `a > c` becomes a `v`-integral over `0 < v < V`, `V = M ρ/c`, and the
large-`a` logarithm (written as `-(k₁ + k₂/h) log(M + c h)/h` in `sForm`) becomes a weight on
`v > V` plus a pole. With the subtraction `k₂/h²` of the unit (the inner Pauli–Villars
remainder), the result is (**`scOut_sForm_eq`**), for `c, M, ρ, u > 0`,

`sForm k₁ k₂ c h M (log(M + c h)) (log(1 + M/(c h))) + k₂/h²
  = ∫₀^∞ T(v)/(u + v)² dv - k₂ ρ² log M/u²`,

with `α = k₁ ρ`, `β = k₂ ρ²`, `p = -α log M` and (`scOutTg`)
`T(v) = α(v²/(2V²) - 2v/V) + β(v/V² - 2/V) + p` for `v ≤ V`,
`T(v) = -3α/2 - α log(v/V) - β/v + p` for `v > V` (continuous at `v = V`).
The weight does not depend on `u`: the outer photon mass enters only through `u`.
Checked numerically (scratch `stageK/g4/gen.py`, `tS.py`, 25 digits).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- **The `(u + v)⁻²`-weight of the outer-massive self-energy `a`-integral.** -/
noncomputable def scOutTg (α β V p v : ℝ) : ℝ :=
  if v ≤ V then α * (v ^ 2 / (2 * V ^ 2) - 2 * v / V) + β * (v / V ^ 2 - 2 / V) + p
  else -(3 / 2 * α) - α * log (v / V) - β / v + p

section

variable {u V : ℝ}

/-- `∫₀^V (a₀ + a₁ v + a₂ v²)/(u + v)² dv` in closed form. -/
theorem scOut_integral_quad (hu : 0 < u) (hV : 0 < V) (a₀ a₁ a₂ : ℝ) :
    IntegrableOn (fun v => (a₀ + a₁ * v + a₂ * v ^ 2) / (u + v) ^ 2) (Ioc 0 V) ∧
      ∫ v in Ioc 0 V, (a₀ + a₁ * v + a₂ * v ^ 2) / (u + v) ^ 2 =
        a₂ * V + (a₁ - 2 * a₂ * u) * (log (u + V) - log u) -
          (a₀ - a₁ * u + a₂ * u ^ 2) * (1 / (u + V) - 1 / u) := by
  have hc : ContinuousOn (fun v => (a₀ + a₁ * v + a₂ * v ^ 2) / (u + v) ^ 2) (Icc 0 V) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun v hv => by
      have : 0 < u + v := by linarith [hv.1]
      positivity
  have hi : IntegrableOn (fun v => (a₀ + a₁ * v + a₂ * v ^ 2) / (u + v) ^ 2) (Ioc 0 V) :=
    (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  refine ⟨hi, ?_⟩
  rw [← intervalIntegral.integral_of_le hV.le]
  have hd : ∀ v ∈ uIcc 0 V, HasDerivAt
      (fun v => a₂ * v + (a₁ - 2 * a₂ * u) * log (u + v) -
        (a₀ - a₁ * u + a₂ * u ^ 2) * (1 / (u + v)))
      ((a₀ + a₁ * v + a₂ * v ^ 2) / (u + v) ^ 2) v := fun v hv => by
    rw [uIcc_of_le hV.le] at hv
    have huv : 0 < u + v := by linarith [hv.1]
    have hl : HasDerivAt (fun v => log (u + v)) (1 / (u + v)) v := by
      have := ((hasDerivAt_id v).const_add u).log huv.ne'
      simpa [one_div] using this
    refine ((((hasDerivAt_id v).const_mul a₂).add (hl.const_mul (a₁ - 2 * a₂ * u))).sub
      ((crossT_hasDerivAt_inv (M := u) huv).const_mul (a₀ - a₁ * u + a₂ * u ^ 2))).congr_deriv ?_
    have := huv.ne'
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((hc.mono (uIcc_of_le hV.le).subset).intervalIntegrable)]
  simp only [add_zero, mul_zero, zero_add]
  ring

end

section

variable {α β V p u : ℝ}

theorem scOutTg_of_le {v : ℝ} (hv : v ≤ V) :
    scOutTg α β V p v =
      (p - 2 * β / V) + (β / V ^ 2 - 2 * α / V) * v + α / (2 * V ^ 2) * v ^ 2 := by
  simp only [scOutTg, hv, ↓reduceIte]
  ring

theorem scOutTg_of_lt {v : ℝ} (hv : V < v) :
    scOutTg α β V p v = -(3 / 2 * α) - α * log (v / V) - β / v + p := by
  simp only [scOutTg, not_le.2 hv, ↓reduceIte]

/-- The weight beyond `V` against `(u + v)⁻²`, as a combination of the masters. -/
theorem scOutTg_div_of_lt {v : ℝ} (hv : V < v) (hv0 : 0 < v) (huv : 0 < u + v) :
    scOutTg α β V p v / (u + v) ^ 2 =
      (p - 3 / 2 * α) * (1 / (u + v) ^ 2) + -α * (log (v / V) / (u + v) ^ 2) +
        -β * (1 / (v * (u + v) ^ 2)) := by
  rw [scOutTg_of_lt hv]
  have := hv0.ne'
  have := huv.ne'
  field_simp
  ring

/-- The weight is integrable against `(u + v)⁻²` beyond `V`, and its integral there. -/
theorem scOutTg_Ioi (hu : 0 < u) (hV : 0 < V) :
    IntegrableOn (fun v => scOutTg α β V p v / (u + v) ^ 2) (Ioi V) ∧
      ∫ v in Ioi V, scOutTg α β V p v / (u + v) ^ 2 =
        (p - 3 / 2 * α) * (1 / (u + V)) + -α * (log (1 + u / V) / u) +
          -β * (log (1 + u / V) / u ^ 2 - 1 / (u * (u + V))) := by
  obtain ⟨i0, v0⟩ := crossTIoi0 hu hV
  obtain ⟨i1, v1⟩ := crossTIoi1 hu hV
  obtain ⟨iL, vL⟩ := crossTIoiL hu hV
  have j0 := i0.const_mul (p - 3 / 2 * α)
  have jL := iL.const_mul (-α)
  have j1 := i1.const_mul (-β)
  have hcongr : EqOn (fun v => scOutTg α β V p v / (u + v) ^ 2)
      (fun v => (p - 3 / 2 * α) * (1 / (u + v) ^ 2) + -α * (log (v / V) / (u + v) ^ 2) +
        -β * (1 / (v * (u + v) ^ 2))) (Ioi V) := fun v hv =>
    scOutTg_div_of_lt hv (hV.trans hv) (by linarith [hV.trans (mem_Ioi.1 hv)])
  have j01 : IntegrableOn (fun v => (p - 3 / 2 * α) * (1 / (u + v) ^ 2) +
      -α * (log (v / V) / (u + v) ^ 2)) (Ioi V) := j0.add jL
  refine ⟨IntegrableOn.congr_fun (j01.add j1) hcongr.symm measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_add j01 j1,
    integral_add j0 jL, integral_const_mul, integral_const_mul, integral_const_mul, v0, v1, vL]

theorem scOutTg_Ioc (hu : 0 < u) (hV : 0 < V) :
    IntegrableOn (fun v => scOutTg α β V p v / (u + v) ^ 2) (Ioc 0 V) ∧
      ∫ v in Ioc 0 V, scOutTg α β V p v / (u + v) ^ 2 =
        α / (2 * V ^ 2) * V + ((β / V ^ 2 - 2 * α / V) - 2 * (α / (2 * V ^ 2)) * u) *
          (log (u + V) - log u) -
          ((p - 2 * β / V) - (β / V ^ 2 - 2 * α / V) * u + α / (2 * V ^ 2) * u ^ 2) *
            (1 / (u + V) - 1 / u) := by
  obtain ⟨hi, hv⟩ := scOut_integral_quad hu hV (p - 2 * β / V) (β / V ^ 2 - 2 * α / V)
    (α / (2 * V ^ 2))
  have hcongr : EqOn (fun v => scOutTg α β V p v / (u + v) ^ 2)
      (fun v => ((p - 2 * β / V) + (β / V ^ 2 - 2 * α / V) * v + α / (2 * V ^ 2) * v ^ 2) /
        (u + v) ^ 2) (Ioc 0 V) := fun v hv => by
    simp only [scOutTg_of_le hv.2]
  exact ⟨hi.congr_fun hcongr.symm measurableSet_Ioc,
    by rw [setIntegral_congr_fun measurableSet_Ioc hcongr, hv]⟩

/-- The weight is integrable against `(u + v)⁻²` on `(0, ∞)`. -/
theorem integrableOn_scOutTg (hu : 0 < u) (hV : 0 < V) :
    IntegrableOn (fun v => scOutTg α β V p v / (u + v) ^ 2) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi hV.le]
  exact (scOutTg_Ioc hu hV).1.union (scOutTg_Ioi hu hV).1

end

/-- **The `(u + v)⁻²`-representation of the outer-massive self-energy `a`-integral.** -/
theorem scOut_sForm_eq {k₁ k₂ c M ρ u : ℝ} (hc : 0 < c) (hM : 0 < M) (hρ : 0 < ρ)
    (hu : 0 < u) :
    sForm k₁ k₂ c (u / ρ) M (log (M + c * (u / ρ))) (log (1 + M / (c * (u / ρ)))) +
        k₂ / (u / ρ) ^ 2 =
      (∫ v in Ioi 0, scOutTg (k₁ * ρ) (k₂ * ρ ^ 2) (M * ρ / c) (-(k₁ * ρ * log M)) v /
        (u + v) ^ 2) - k₂ * ρ ^ 2 * log M / u ^ 2 := by
  set V := M * ρ / c with hVdef
  have hV : 0 < V := by positivity
  have hint := integrableOn_scOutTg (α := k₁ * ρ) (β := k₂ * ρ ^ 2) (p := -(k₁ * ρ * log M))
    hu hV
  rw [← Ioc_union_Ioi_eq_Ioi hV.le] at hint ⊢
  rw [setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set subset_union_left) (hint.mono_set subset_union_right),
    (scOutTg_Ioc hu hV).2, (scOutTg_Ioi hu hV).2]
  have huV : 0 < u + V := by positivity
  have e1 : M + c * (u / ρ) = c / ρ * (u + V) := by
    rw [hVdef]; field_simp; ring
  have e2 : 1 + M / (c * (u / ρ)) = (u + V) / u := by
    rw [hVdef]; field_simp
  have e3 : 1 + u / V = (u + V) / V := by field_simp; ring
  have lV : log V = log M + log ρ - log c := by
    rw [hVdef, log_div (by positivity) hc.ne', log_mul hM.ne' hρ.ne']
  rw [e1, e2, e3, log_mul (by positivity) huV.ne', log_div hc.ne' hρ.ne',
    log_div huV.ne' hu.ne', log_div huV.ne' hV.ne', lV]
  unfold sForm
  rw [hVdef]
  have := hc.ne'
  have := hM.ne'
  have := hρ.ne'
  have := hu.ne'
  have : u * c + M * ρ ≠ 0 := by positivity
  have : c * u + M * ρ ≠ 0 := by positivity
  field_simp
  ring

end QED.ChainProof.SetCK

end
