/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWRhoX

/-!
# Set (a), stage D: the `σ`-integral of the `VA` node density

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. At the
spectral point `T = 4/(1-δ²)` the nodes above threshold are `σ = (1 + δu)/2`, `u ∈ (-1, 1)`,
with `a = Tσ(1-σ) - 1 = δ²(1-u²)/(1-δ²)`. In `u` the `x`-integrated density `ksWRMx σ a` is
`ksWRfu δ u`: polynomial coefficients times the logarithms of `1 ± u`, `1 ± δu`,
`1 + δ² - 2δu` plus a rational part, with the explicit primitive `ksWRG δ`. Hence the node part
of the `VA` density is elementary:

  `∫_{(1-δ)/2}^{(1+δ)/2} ksWRMx σ (Tσ(1-σ) - 1) dσ = ksWRAn δ`.

Main results:

* `ksWR_hasDerivAt_ksWRG`: the primitive;
* `ksWR_integral_ksWRfu`: `∫_{-1}^1 ksWRfu δ u du = (2/δ) ksWRAn δ`;
* `ksWR_ksWRMx_eq`: the integrand in `u`;
* **`ksWR_integral_ksWRMx`**: the `σ`-integral.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology intervalIntegral

namespace QED.ChainProof.SetAKS

/-- A polynomial of degree at most five. -/
def ksWRpol (c₀ c₁ c₂ c₃ c₄ c₅ u : ℝ) : ℝ :=
  c₀ + c₁ * u + c₂ * u ^ 2 + c₃ * u ^ 3 + c₄ * u ^ 4 + c₅ * u ^ 5

theorem ksWR_hasDerivAt_pol (c₀ c₁ c₂ c₃ c₄ c₅ u : ℝ) :
    HasDerivAt (ksWRpol c₀ c₁ c₂ c₃ c₄ c₅)
      (c₁ + 2 * c₂ * u + 3 * c₃ * u ^ 2 + 4 * c₄ * u ^ 3 + 5 * c₅ * u ^ 4) u := by
  have h := ((((((hasDerivAt_const u c₀).add ((hasDerivAt_id u).const_mul c₁)).add
    ((hasDerivAt_pow 2 u).const_mul c₂)).add ((hasDerivAt_pow 3 u).const_mul c₃)).add
    ((hasDerivAt_pow 4 u).const_mul c₄)).add ((hasDerivAt_pow 5 u).const_mul c₅))
  refine h.congr_deriv ?_
  push_cast
  ring

theorem ksWR_hasDerivAt_compMulLog {l : ℝ → ℝ} {l' u : ℝ} (hl : HasDerivAt l l' u)
    (h : l u ≠ 0) : HasDerivAt (fun v => l v * log (l v)) (l' * (log (l u) + 1)) u :=
  ((ksWR_hasDerivAt_mulLog h).comp u hl).congr_deriv (by ring)

/-- The coefficient of `log a` in `u`. -/
noncomputable def ksWRA (δ u : ℝ) : ℝ :=
  4 * (δ * u + 1) ^ 2 * (5 * δ ^ 2 * u ^ 2 - δ ^ 2 - 6 * δ * u + 2) / ((δ - 1) * (δ + 1))

/-- The coefficient of `log (a + 1 - σ)` in `u`. -/
noncomputable def ksWRB (δ u : ℝ) : ℝ :=
  -2 * (δ * u + 1) * (-2 * δ ^ 4 * u ^ 2 + 10 * δ ^ 3 * u ^ 3 + δ ^ 3 * u - 3 * δ ^ 2 - 11 * δ * u
    + 5) / ((δ - 1) * (δ + 1))

/-- The coefficient of `log (1 - σ)` in `u`. -/
noncomputable def ksWRC (δ u : ℝ) : ℝ :=
  -2 * (δ * u - 1) * (δ * u + 1) * (2 * δ * u - 1)

/-- The polynomial part of the rational term in `u`. -/
noncomputable def ksWRRp (δ u : ℝ) : ℝ :=
  -δ ^ 6 / 8 - δ ^ 5 * u / 4 - δ ^ 4 * u ^ 2 / 2 + δ ^ 4 / 8 - 11 * δ ^ 3 * u ^ 3 + δ ^ 3 * u / 2 +
    9 * δ ^ 2 * u ^ 2 / 2 - 11 * δ ^ 2 / 8 + 43 * δ * u / 4 - 21 / 8

/-- The residue of the rational term at `1 + δ² - 2δu = 0`. -/
noncomputable def ksWRcR (δ : ℝ) : ℝ :=
  (δ - 1) ^ 2 * (δ + 1) ^ 2 * (δ ^ 4 + 2 * δ ^ 2 + 13) / 8

/-- **The `x`-integrated `VA` density in `u`** (`σ = (1 + δu)/2`). -/
noncomputable def ksWRfu (δ u : ℝ) : ℝ :=
  ksWRA δ u * (log (1 - u) + log (1 + u) + 2 * log δ - log (1 - δ ^ 2)) +
    ksWRB δ u * (log (1 + δ * u) + log (1 + δ ^ 2 - 2 * δ * u) - log 2 - log (1 - δ ^ 2)) +
    ksWRC δ u * (log (1 - δ * u) - log 2) + ksWRRp δ u + ksWRcR δ / (1 + δ ^ 2 - 2 * δ * u)

/-- The polynomial `q1` of the primitive `ksWRG`. -/
noncomputable def ksWRq1 (δ u : ℝ) : ℝ :=
  ksWRpol (-4 * (δ - 2) * (2 * δ ^ 3 + 4 * δ ^ 2 - 3) / (3 * (δ - 1) * (δ + 1))) (-4 * δ * (2 * δ
      ^ 2 - 2 * δ - 3) / (3 * (δ - 1))) (-4 * δ ^ 2 * (2 * δ + 5) / (3 * (δ + 1))) (-4 * δ ^ 3 / (δ
      - 1)) (-4 * δ ^ 4 / ((δ - 1) * (δ + 1))) (0) u

/-- The polynomial `q2` of the primitive `ksWRG`. -/
noncomputable def ksWRq2 (δ u : ℝ) : ℝ :=
  ksWRpol (4 * (δ + 2) * (2 * δ ^ 3 - 4 * δ ^ 2 + 3) / (3 * (δ - 1) * (δ + 1))) (-4 * δ * (2 * δ
      ^ 2 + 2 * δ - 3) / (3 * (δ + 1))) (4 * δ ^ 2 * (2 * δ - 5) / (3 * (δ - 1))) (-4 * δ ^ 3 / (δ
      + 1)) (4 * δ ^ 4 / ((δ - 1) * (δ + 1))) (0) u

/-- The polynomial `q3` of the primitive `ksWRG`. -/
noncomputable def ksWRq3 (δ u : ℝ) : ℝ :=
  ksWRpol (1 / (3 * δ)) (-5 / 3) (δ / 3) (δ ^ 2) (0) (0) u

/-- The polynomial `q4` of the primitive `ksWRG`. -/
noncomputable def ksWRq4 (δ u : ℝ) : ℝ :=
  ksWRpol ((11 * δ ^ 2 - 23) / (3 * δ * (δ - 1) * (δ + 1))) (7 / 3) (-δ * (δ - 5) * (δ + 5) / (3
      * (δ - 1) * (δ + 1))) (δ ^ 2) (-4 * δ ^ 3 / ((δ - 1) * (δ + 1))) (0) u

/-- The polynomial `q5` of the primitive `ksWRG`. -/
noncomputable def ksWRq5 (δ u : ℝ) : ℝ :=
  ksWRpol ((δ ^ 2 + 5) * (3 * δ ^ 6 + 11 * δ ^ 4 - 59 * δ ^ 2 + 29) / (48 * δ * (δ - 1) * (δ +
      1))) ((3 * δ ^ 2 + 5) * (δ ^ 4 + 6 * δ ^ 2 - 19) / (24 * (δ - 1) * (δ + 1))) (δ * (3 * δ ^ 2
      + 23) / 12) (δ ^ 2 * (δ ^ 2 + 7) / (2 * (δ - 1) * (δ + 1))) (2 * δ ^ 3 / ((δ - 1) * (δ + 1)))
      (0) u

/-- The polynomial `q6` of the primitive `ksWRG`. -/
noncomputable def ksWRq6 (δ u : ℝ) : ℝ :=
  ksWRpol (0) ((4 * δ ^ 6 - 21 * δ ^ 4 - 12 * δ ^ 2 * log 2 - 6 * δ ^ 2 * log (1 - δ ^ 2) - 24 *
      δ ^ 2 * log δ + 17 * δ ^ 2 + 24 * log 2 + 6 * log (1 - δ ^ 2) + 48 * log δ) / (3 * (δ - 1) *
      (δ + 1))) (2 * δ * (2 * δ ^ 4 - 6 * δ ^ 2 * log 2 + 3 * δ ^ 2 * log (1 - δ ^ 2) - 12 * δ ^ 2
      * log δ + 3 * δ ^ 2 - 6 * log 2 - 3 * log (1 - δ ^ 2) - 12 * log δ - 5) / (3 * (δ - 1) * (δ +
      1))) (-δ ^ 2 * (12 * δ ^ 2 * log 2 - 6 * δ ^ 2 * log (1 - δ ^ 2) + 24 * δ ^ 2 * log δ - 11 *
      δ ^ 2 + 60 * log 2 + 6 * log (1 - δ ^ 2) + 120 * log δ + 11) / (9 * (δ - 1) * (δ + 1))) (-δ ^
      3 * (2 * δ ^ 2 * log (1 - δ ^ 2) + 5 * δ ^ 2 - 8 * log 2 - 2 * log (1 - δ ^ 2) - 16 * log δ -
      5) / (2 * (δ - 1) * (δ + 1))) (4 * δ ^ 4 * (log 2 + 2 * log δ) / ((δ - 1) * (δ + 1))) u

/-- The primitive of `ksWRfu δ` in `u`. -/
noncomputable def ksWRG (δ u : ℝ) : ℝ :=
  ksWRq1 δ u * ((1 - u) * log (1 - u)) +
  ksWRq2 δ u * ((1 + u) * log (1 + u)) +
  ksWRq3 δ u * ((1 - δ * u) * log (1 - δ * u)) +
  ksWRq4 δ u * ((1 + δ * u) * log (1 + δ * u)) +
  ksWRq5 δ u * ((1 + δ ^ 2 - 2 * δ * u) * log (1 + δ ^ 2 - 2 * δ * u)) -
  ksWRcR δ / (2 * δ) * log (1 + δ ^ 2 - 2 * δ * u) + ksWRq6 δ u

/-- **The node part of the `VA` density** (closed form). -/
noncomputable def ksWRAn (δ : ℝ) : ℝ :=
  8 / 3 * δ * (δ ^ 2 - 3) * (3 * log 2 + 2 * log δ) +
    (4 * δ ^ 6 + 3 * δ ^ 4 - 24 * δ ^ 3 - 18 * δ ^ 2 + 72 * δ - 45) / 6 * log (1 - δ) -
    (4 * δ ^ 6 + 3 * δ ^ 4 + 24 * δ ^ 3 - 18 * δ ^ 2 - 72 * δ - 45) / 6 * log (1 + δ) +
    (24 * δ ^ 6 - 107 * δ ^ 4 + 54 * δ ^ 2 - 27) / (18 * δ) + 3 * (1 - δ ^ 2) ^ 2 / (2 * δ)

section Prim

variable {δ : ℝ}

theorem ksWR_arg5_pos (hδ : δ ∈ Ioo (0 : ℝ) 1) {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    0 < 1 + δ ^ 2 - 2 * δ * u := by
  nlinarith [hδ.1, hδ.2, hu.1, hu.2, sq_nonneg (1 - δ)]

theorem ksWR_hasDerivAt_ksWRG (hδ : δ ∈ Ioo (0 : ℝ) 1) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (ksWRG δ) (ksWRfu δ u) u := by
  obtain ⟨h0, h1⟩ := hδ
  have e1 : (1 : ℝ) - u ≠ 0 := by linarith [hu.2]
  have e2 : (1 : ℝ) + u ≠ 0 := by linarith [hu.1]
  have e3 : (1 : ℝ) - δ * u ≠ 0 := by nlinarith [hu.1, hu.2]
  have e4 : (1 : ℝ) + δ * u ≠ 0 := by nlinarith [hu.1, hu.2]
  have e5 : (1 : ℝ) + δ ^ 2 - 2 * δ * u ≠ 0 :=
    (ksWR_arg5_pos ⟨h0, h1⟩ ⟨hu.1.le, hu.2.le⟩).ne'
  have hδ0 : δ ≠ 0 := h0.ne'
  have hd1 : δ - 1 ≠ 0 := by linarith
  have hd2 : δ + 1 ≠ 0 := by linarith
  have l1 := ksWR_hasDerivAt_compMulLog ((hasDerivAt_id u).const_sub 1) e1
  have l2 := ksWR_hasDerivAt_compMulLog ((hasDerivAt_id u).const_add 1) e2
  have l3 := ksWR_hasDerivAt_compMulLog (((hasDerivAt_id u).const_mul δ).const_sub 1) e3
  have l4 := ksWR_hasDerivAt_compMulLog (((hasDerivAt_id u).const_mul δ).const_add 1) e4
  have a5 : HasDerivAt (fun v => 1 + δ ^ 2 - 2 * δ * v) (-(2 * δ)) u := by
    simpa using ((hasDerivAt_id u).const_mul (2 * δ)).const_sub (1 + δ ^ 2)
  have l5 := ksWR_hasDerivAt_compMulLog a5 e5
  have g5 := (a5.log e5).const_mul (ksWRcR δ / (2 * δ))
  have q1 := (show HasDerivAt (fun v => ksWRq1 δ v) _ u from ksWR_hasDerivAt_pol _ _ _ _ _ _ u)
  have q2 := (show HasDerivAt (fun v => ksWRq2 δ v) _ u from ksWR_hasDerivAt_pol _ _ _ _ _ _ u)
  have q3 := (show HasDerivAt (fun v => ksWRq3 δ v) _ u from ksWR_hasDerivAt_pol _ _ _ _ _ _ u)
  have q4 := (show HasDerivAt (fun v => ksWRq4 δ v) _ u from ksWR_hasDerivAt_pol _ _ _ _ _ _ u)
  have q5 := (show HasDerivAt (fun v => ksWRq5 δ v) _ u from ksWR_hasDerivAt_pol _ _ _ _ _ _ u)
  have q6 := (show HasDerivAt (fun v => ksWRq6 δ v) _ u from ksWR_hasDerivAt_pol _ _ _ _ _ _ u)
  have h := (((((((q1.mul l1).add (q2.mul l2)).add (q3.mul l3)).add (q4.mul l4)).add
    (q5.mul l5)).sub g5).add q6)
  refine h.congr_deriv ?_
  simp only [id, ksWRpol, ksWRq1, ksWRq2, ksWRq3, ksWRq4, ksWRq5, ksWRfu, ksWRA,
    ksWRB, ksWRC, ksWRRp, ksWRcR]
  field_simp
  ring

theorem ksWR_continuousOn_ksWRG (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (ksWRG δ) (Icc (-1) 1) := by
  have m1 : Continuous fun u : ℝ => (1 - u) * log (1 - u) :=
    continuous_mul_log.comp (by fun_prop)
  have m2 : Continuous fun u : ℝ => (1 + u) * log (1 + u) :=
    continuous_mul_log.comp (by fun_prop)
  have m3 : Continuous fun u : ℝ => (1 - δ * u) * log (1 - δ * u) :=
    continuous_mul_log.comp (by fun_prop)
  have m4 : Continuous fun u : ℝ => (1 + δ * u) * log (1 + δ * u) :=
    continuous_mul_log.comp (by fun_prop)
  have m5 : Continuous fun u : ℝ => (1 + δ ^ 2 - 2 * δ * u) * log (1 + δ ^ 2 - 2 * δ * u) :=
    continuous_mul_log.comp (by fun_prop)
  have c5 : ContinuousOn (fun u : ℝ => log (1 + δ ^ 2 - 2 * δ * u)) (Icc (-1) 1) :=
    ContinuousOn.log (by fun_prop) fun u hu => (ksWR_arg5_pos hδ hu).ne'
  have hc : Continuous fun u => ksWRq1 δ u * ((1 - u) * log (1 - u)) +
      ksWRq2 δ u * ((1 + u) * log (1 + u)) + ksWRq3 δ u * ((1 - δ * u) * log (1 - δ * u)) +
      ksWRq4 δ u * ((1 + δ * u) * log (1 + δ * u)) +
      ksWRq5 δ u * ((1 + δ ^ 2 - 2 * δ * u) * log (1 + δ ^ 2 - 2 * δ * u)) := by
    simp only [ksWRq1, ksWRq2, ksWRq3, ksWRq4, ksWRq5, ksWRpol]
    fun_prop
  have hq : Continuous fun u => ksWRq6 δ u := by
    simp only [ksWRq6, ksWRpol]
    fun_prop
  exact (hc.continuousOn.sub (c5.const_smul (ksWRcR δ / (2 * δ)))).add hq.continuousOn

theorem ksWR_intervalIntegrable_log_add (a b : ℝ) :
    IntervalIntegrable (fun x => log (1 + x)) volume a b := by
  have h := (intervalIntegrable_log' (a := 1 + a) (b := 1 + b)).comp_add_left 1
  simp only [add_sub_cancel_left] at h
  exact h

theorem ksWR_intervalIntegrable_ksWRfu (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (ksWRfu δ) volume (-1) 1 := by
  have e : ksWRfu δ = fun u => ksWRA δ u * log (1 - u) + ksWRA δ u * log (1 + u) +
      (ksWRA δ u * (2 * log δ - log (1 - δ ^ 2)) +
        ksWRB δ u * (log (1 + δ * u) + log (1 + δ ^ 2 - 2 * δ * u) - log 2 - log (1 - δ ^ 2)) +
        ksWRC δ u * (log (1 - δ * u) - log 2) + ksWRRp δ u +
        ksWRcR δ / (1 + δ ^ 2 - 2 * δ * u)) := by
    funext u
    unfold ksWRfu
    ring
  obtain ⟨h0, h1⟩ := hδ
  have cA : Continuous fun u => ksWRA δ u := by unfold ksWRA; fun_prop
  have p3 : ∀ u ∈ Icc (-1 : ℝ) 1, 0 < 1 - δ * u := fun u hu => by nlinarith [hu.1, hu.2]
  have p4 : ∀ u ∈ Icc (-1 : ℝ) 1, 0 < 1 + δ * u := fun u hu => by nlinarith [hu.1, hu.2]
  have p5 := fun u (hu : u ∈ Icc (-1 : ℝ) 1) => ksWR_arg5_pos ⟨h0, h1⟩ hu
  have hr : ContinuousOn (fun u => ksWRA δ u * (2 * log δ - log (1 - δ ^ 2)) +
        ksWRB δ u * (log (1 + δ * u) + log (1 + δ ^ 2 - 2 * δ * u) - log 2 - log (1 - δ ^ 2)) +
        ksWRC δ u * (log (1 - δ * u) - log 2) + ksWRRp δ u +
        ksWRcR δ / (1 + δ ^ 2 - 2 * δ * u)) (Icc (-1) 1) := by
    have l3 : ContinuousOn (fun u : ℝ => log (1 - δ * u)) (Icc (-1) 1) :=
      ContinuousOn.log (by fun_prop) fun u hu => (p3 u hu).ne'
    have l4 : ContinuousOn (fun u : ℝ => log (1 + δ * u)) (Icc (-1) 1) :=
      ContinuousOn.log (by fun_prop) fun u hu => (p4 u hu).ne'
    have l5 : ContinuousOn (fun u : ℝ => log (1 + δ ^ 2 - 2 * δ * u)) (Icc (-1) 1) :=
      ContinuousOn.log (by fun_prop) fun u hu => (p5 u hu).ne'
    have d5 : ContinuousOn (fun u : ℝ => ksWRcR δ / (1 + δ ^ 2 - 2 * δ * u)) (Icc (-1) 1) :=
      continuousOn_const.div (by fun_prop) fun u hu => (p5 u hu).ne'
    have cB : Continuous fun u => ksWRB δ u := by unfold ksWRB; fun_prop
    have cC : Continuous fun u => ksWRC δ u := by unfold ksWRC; fun_prop
    have cR : Continuous fun u => ksWRRp δ u := by unfold ksWRRp; fun_prop
    refine ((((cA.continuousOn.mul continuousOn_const).add (cB.continuousOn.mul
      (((l4.add l5).sub continuousOn_const).sub continuousOn_const))).add
      (cC.continuousOn.mul (l3.sub continuousOn_const))).add cR.continuousOn).add d5
  rw [e]
  refine ((ksWR_intervalIntegrable_log_one (-1) 1).continuousOn_mul cA.continuousOn).add
    ((ksWR_intervalIntegrable_log_add (-1) 1).continuousOn_mul cA.continuousOn) |>.add ?_
  exact hr.intervalIntegrable_of_Icc (by norm_num)

/-- **The `u`-integral**: `∫_-1^1 ksWRfu δ u du = (2/δ) ksWRAn δ`. -/
theorem ksWR_integral_ksWRfu (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    ∫ u in (-1 : ℝ)..1, ksWRfu δ u = 2 / δ * ksWRAn δ := by
  rw [integral_eq_sub_of_hasDerivAt_of_le (by norm_num) (ksWR_continuousOn_ksWRG hδ)
    (fun u hu => ksWR_hasDerivAt_ksWRG hδ hu) (ksWR_intervalIntegrable_ksWRfu hδ)]
  obtain ⟨h0, h1⟩ := hδ
  have hm : 0 < 1 - δ := by linarith
  have hp : 0 < 1 + δ := by linarith
  have r1 : (1 : ℝ) + δ ^ 2 - 2 * δ * 1 = (1 - δ) ^ 2 := by ring
  have r2 : (1 : ℝ) + δ ^ 2 - 2 * δ * (-1) = (1 + δ) ^ 2 := by ring
  have r3 : (1 : ℝ) - δ * (-1) = 1 + δ := by ring
  have r4 : (1 : ℝ) + δ * (-1) = 1 - δ := by ring
  have r5 : (1 : ℝ) - -1 = 2 := by norm_num
  have r6 : (1 : ℝ) + 1 = 2 := by norm_num
  have hD : log (1 - δ ^ 2) = log (1 - δ) + log (1 + δ) := by
    rw [← log_mul hm.ne' hp.ne']
    ring_nf
  simp only [ksWRG]
  rw [r1, r2, r3, r4, r5, r6]
  simp only [mul_one, sub_self, zero_mul, mul_zero, log_zero,
    add_neg_cancel, log_pow, ksWRq1, ksWRq2, ksWRq3, ksWRq4, ksWRq5, ksWRq6, ksWRpol, hD,
    ksWRAn, ksWRcR]
  have : δ ≠ 0 := h0.ne'
  have : δ - 1 ≠ 0 := by linarith
  have : δ + 1 ≠ 0 := by linarith
  field_simp
  ring

end Prim

section Sigma

variable {δ : ℝ}

/-- **The `x`-integrated density in `u`**: at `σ = (1 + δu)/2`, `T = 4/(1-δ²)`,
`ksWRMx σ (Tσ(1-σ) - 1) = ksWRfu δ u`. -/
theorem ksWR_ksWRMx_eq (hδ : δ ∈ Ioo (0 : ℝ) 1) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    ksWRMx (δ / 2 * u + 1 / 2) (ksDT 1 δ * ((δ / 2 * u + 1 / 2) * (1 - (δ / 2 * u + 1 / 2))) - 1) =
      ksWRfu δ u := by
  obtain ⟨h0, h1⟩ := hδ
  have p1 : 0 < 1 - u := by linarith [hu.2]
  have p2 : 0 < 1 + u := by linarith [hu.1]
  have p3 : 0 < 1 - δ * u := by nlinarith [hu.1, hu.2]
  have p4 : 0 < 1 + δ * u := by nlinarith [hu.1, hu.2]
  have p5 : 0 < 1 + δ ^ 2 - 2 * δ * u := ksWR_arg5_pos ⟨h0, h1⟩ ⟨hu.1.le, hu.2.le⟩
  have pD : 0 < 1 - δ ^ 2 := by nlinarith
  have ha : ksDT 1 δ * ((δ / 2 * u + 1 / 2) * (1 - (δ / 2 * u + 1 / 2))) - 1 =
      δ ^ 2 * ((1 - u) * (1 + u)) / (1 - δ ^ 2) := by
    unfold ksDT
    field_simp
    ring
  have hY : 1 - (δ / 2 * u + 1 / 2) = (1 - δ * u) / 2 := by ring
  set a := δ ^ 2 * ((1 - u) * (1 + u)) / (1 - δ ^ 2) with ha'
  have pa : 0 < a := by positivity
  have haY : a + (1 - δ * u) / 2 = (1 + δ * u) * (1 + δ ^ 2 - 2 * δ * u) / (2 * (1 - δ ^ 2)) := by
    rw [ha']
    field_simp
    ring
  have pY : 0 < a + (1 - δ * u) / 2 := by positivity
  have hlc : log (a / (a + (1 - δ * u) / 2)) = log a - log (a + (1 - δ * u) / 2) :=
    log_div pa.ne' pY.ne'
  have hl1c : log (1 - a / (a + (1 - δ * u) / 2)) =
      log ((1 - δ * u) / 2) - log (a + (1 - δ * u) / 2) := by
    rw [show 1 - a / (a + (1 - δ * u) / 2) = (1 - δ * u) / 2 / (a + (1 - δ * u) / 2) by
      field_simp; ring, log_div (by positivity) pY.ne']
  have hlaY : log (a + (1 - δ * u) / 2) =
      log (1 + δ * u) + log (1 + δ ^ 2 - 2 * δ * u) - log 2 - log (1 - δ ^ 2) := by
    rw [haY, log_div (by positivity) (by positivity), log_mul p4.ne' p5.ne',
      log_mul two_ne_zero pD.ne']
    ring
  have hla : log a = 2 * log δ + log (1 - u) + log (1 + u) - log (1 - δ ^ 2) := by
    rw [ha', log_div (by positivity) pD.ne', log_mul (by positivity) (by positivity),
      log_pow, log_mul p1.ne' p2.ne']
    push_cast
    ring
  have hlY : log ((1 - δ * u) / 2) = log (1 - δ * u) - log 2 := log_div p3.ne' two_ne_zero
  rw [ha]
  simp only [ksWRMx, ksWRH, ksWRL, ksWRg0, ksWRg1, ksWRk]
  rw [hY, hlc, hl1c, hlaY, hla, hlY]
  simp only [ksWRfu, ksWRA, ksWRB, ksWRC, ksWRRp, ksWRcR]
  have : δ - 1 ≠ 0 := by linarith
  have : δ + 1 ≠ 0 := by linarith
  have : a ≠ 0 := pa.ne'
  rw [ha']
  field_simp
  ring

/-- **The `σ`-integral of the `x`-integrated `VA` density**: for `δ ∈ (0, 1)`,
`∫_{(1-δ)/2}^{(1+δ)/2} ksWRMx σ (Tσ(1-σ) - 1) dσ = ksWRAn δ`, `T = 4/(1-δ²)`. -/
theorem ksWR_integral_ksWRMx (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    ∫ σ in (1 - δ) / 2..(1 + δ) / 2, ksWRMx σ (ksDT 1 δ * (σ * (1 - σ)) - 1) = ksWRAn δ := by
  have hc : δ / 2 ≠ 0 := by linarith [hδ.1]
  have h := intervalIntegral.integral_comp_mul_add
    (fun σ => ksWRMx σ (ksDT 1 δ * (σ * (1 - σ)) - 1)) (a := -1) (b := 1) hc (1 / 2)
  rw [show δ / 2 * (-1) + 1 / 2 = (1 - δ) / 2 by ring,
    show δ / 2 * 1 + 1 / 2 = (1 + δ) / 2 by ring] at h
  have e1 : ∫ u in (-1 : ℝ)..1, ksWRMx (δ / 2 * u + 1 / 2)
      (ksDT 1 δ * ((δ / 2 * u + 1 / 2) * (1 - (δ / 2 * u + 1 / 2))) - 1) =
      ∫ u in (-1 : ℝ)..1, ksWRfu δ u :=
    integral_congr_Ioo_of_le (by norm_num) fun u hu => ksWR_ksWRMx_eq hδ hu
  rw [e1, ksWR_integral_ksWRfu hδ, smul_eq_mul, inv_div] at h
  exact (mul_left_cancel₀ (div_ne_zero two_ne_zero hδ.1.ne') h).symm

end Sigma

end QED.ChainProof.SetAKS

end
