/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4Counterterm
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# (R-Π₄): the Pauli–Villars photon as an integral over the photon mass

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), lemma L5 of the plan. The
model's photon is the Pauli–Villars pair `D_{m_γ}⁻¹ D_Λ⁻¹` (up to the constant `Λ² - m_γ²`); the
mass counterterm is a log of a ratio at the same two masses. Both are integrals over the squared
photon mass `u = μ²` of a doubled photon line, so the `Λ`-dependence of the order-`e⁴` vacuum
polarization becomes the upper limit of a `u`-integral.

* `inv_mul_inv_eq_integral`: `(b - a) (w + a)⁻¹ (w + b)⁻¹ = ∫_a^b (w + u)⁻² du` whenever
  `w + u ≠ 0` on `[a, b]`.
* `propDenom_pair_eq_integral`: the photon pair of the model at `ε ≠ 0`,
  `(Λ² - m_γ²) D_{m_γ}(q)⁻¹ D_Λ(q)⁻¹ = ∫_{m_γ²}^{Λ²} (q² + u - iε)⁻² du`.
* `integral_comp_pair`: the Feynman-parameter form. Two lines with the same momentum, parameters
  `a`, `t - a` and squared masses `A`, `B` enter a parametric integrand only through `t` and
  `a A + (t - a) B`; integrating out `a` at fixed `t` gives `t/(B - A) ∫_A^B du` of the doubled
  line with parameter `t` and squared mass `u`.
* `log_sub_log_eq_integral`, `onShellL_eq_integral`: `L(x) = ∫_{m_γ²}^{Λ²} (1 - x) / D_u(x) du`.
* `onShellδm_sub_onShellδ₂_eq_integral_sigma`: the surviving mass insertion is
  `δ = ∫_{m_γ²}^{Λ²} σ(u) du` with `σ(u) = -(e²/8π²) ∫₀¹ (1 - x²) / (x² m² + (1 - x) u) dx`
  (`sigma`).
-/

@[expose] public section

open Complex MeasureTheory Set intervalIntegral
open QED.WickModel (Params)

namespace QED.GradedProof.RPi4

/-! ### The propagator pair -/

/-- **The propagator pair as an integral over the squared mass.** -/
theorem inv_mul_inv_eq_integral (w : ℂ) {a b : ℝ} (h : ∀ u ∈ uIcc a b, w + (u : ℂ) ≠ 0) :
    (((b - a : ℝ) : ℂ)) * ((w + a)⁻¹ * (w + b)⁻¹) = ∫ u in a..b, ((w + (u : ℂ)) ^ 2)⁻¹ := by
  have hd : ∀ u ∈ uIcc a b, HasDerivAt (fun u : ℝ => -(w + (u : ℂ))⁻¹)
      (((w + (u : ℂ)) ^ 2)⁻¹) u := by
    intro u hu
    have h1 : HasDerivAt (fun z : ℂ => w + z) 1 (u : ℂ) := (hasDerivAt_id _).const_add w
    have h2 := (h1.inv (h u hu)).neg.comp_ofReal
    convert h2 using 1
    ring
  have hc : ContinuousOn (fun u : ℝ => ((w + (u : ℂ)) ^ 2)⁻¹) (uIcc a b) := by
    refine ContinuousOn.inv₀ (by fun_prop) fun u hu => pow_ne_zero 2 (h u hu)
  rw [integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]
  have ha := h a left_mem_uIcc
  have hb := h b right_mem_uIcc
  field_simp
  push_cast
  ring

open QED.TwoLoop.Bridge (propDenom) in
/-- **The Pauli–Villars photon pair of the model** at `ε ≠ 0`:
`(Λ² - m_γ²) D_{m_γ}(q)⁻¹ D_Λ(q)⁻¹ = ∫_{m_γ²}^{Λ²} (q² + u - iε)⁻² du`. -/
theorem propDenom_pair_eq_integral (mγ Λ : ℝ) {ε : ℝ} (hε : ε ≠ 0) (q : Fin 4 → ℝ) :
    (((Λ ^ 2 - mγ ^ 2 : ℝ) : ℂ)) * ((propDenom mγ ε q)⁻¹ * (propDenom Λ ε q)⁻¹) =
      ∫ u in mγ ^ 2..Λ ^ 2, ((((Minkowski.dot q q + u : ℝ) : ℂ) - (ε : ℂ) * I) ^ 2)⁻¹ := by
  have hw : ∀ u : ℝ, (((Minkowski.dot q q : ℝ) : ℂ) - (ε : ℂ) * I) + (u : ℂ) =
      ((Minkowski.dot q q + u : ℝ) : ℂ) - (ε : ℂ) * I := fun u => by push_cast; ring
  have h := inv_mul_inv_eq_integral (((Minkowski.dot q q : ℝ) : ℂ) - (ε : ℂ) * I)
    (a := mγ ^ 2) (b := Λ ^ 2) fun u _ => by
      rw [hw]
      intro h0
      have := congrArg Complex.im h0
      simp at this
      exact hε this
  simp only [hw] at h
  simpa only [propDenom] using h

/-! ### The Feynman-parameter form -/

/-- **Collapsing a pair of lines with the same momentum.** For any `h`, squared masses `A ≠ B`
and total parameter `t`, `∫₀^t h(a A + (t - a) B) da = t/(B - A) ∫_A^B h(t u) du`. -/
theorem integral_comp_pair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : ℝ → E)
    {A B : ℝ} (hAB : A ≠ B) (t : ℝ) :
    ∫ a in (0 : ℝ)..t, h (a * A + (t - a) * B) = (t / (B - A)) • ∫ u in A..B, h (t * u) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  have hc : A - B ≠ 0 := sub_ne_zero.2 hAB
  have e1 : (fun a => h (a * A + (t - a) * B)) = fun a => h ((A - B) * a + t * B) := by
    funext a
    congr 1
    ring
  rw [e1, integral_comp_mul_add (fun a => h a) hc, integral_comp_mul_left (fun u => h u) ht,
    smul_smul, integral_symm]
  have e2 : (A - B) * 0 + t * B = t * B := by ring
  have e3 : (A - B) * t + t * B = t * A := by ring
  rw [e2, e3, smul_neg, ← neg_smul]
  congr 1
  have hc' : B - A ≠ 0 := sub_ne_zero.2 hAB.symm
  field_simp
  ring

/-! ### The logarithm and the mass counterterm -/

/-- **A logarithm of an affine function as an integral.** -/
theorem log_sub_log_eq_integral {c d A B : ℝ} (h : ∀ u ∈ uIcc A B, 0 < c + d * u) :
    Real.log (c + d * B) - Real.log (c + d * A) = ∫ u in A..B, d / (c + d * u) := by
  have hd : ∀ u ∈ uIcc A B, HasDerivAt (fun u => Real.log (c + d * u)) (d / (c + d * u)) u := by
    intro u hu
    have h1 : HasDerivAt (fun u => c + d * u) d u := by
      simpa using ((hasDerivAt_id u).const_mul d).const_add c
    exact h1.log (h u hu).ne'
  have hc : ContinuousOn (fun u => d / (c + d * u)) (uIcc A B) :=
    continuousOn_const.div (by fun_prop) fun u hu => (h u hu).ne'
  rw [integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]

theorem onShell_denom_pos {m x u : ℝ} (hm : m ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) (hu : 0 < u) :
    0 < x ^ 2 * m ^ 2 + (1 - x) * u := by
  rcases eq_or_lt_of_le hx.2 with rfl | hx1
  · simp only [one_pow, one_mul, sub_self, zero_mul, add_zero]
    positivity
  · have : 0 < (1 - x) * u := mul_pos (by linarith) hu
    nlinarith [sq_nonneg (x * m)]

/-- **The on-shell logarithm as an integral over the squared photon mass**:
`L(x) = ∫_{m_γ²}^{Λ²} (1 - x) / (x² m² + (1 - x) u) du` for `x ∈ [0, 1]`. -/
theorem onShellL_eq_integral {m mγ Λ x : ℝ} (hm : m ≠ 0) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    onShellL m mγ Λ x = ∫ u in mγ ^ 2..Λ ^ 2, (1 - x) / (x ^ 2 * m ^ 2 + (1 - x) * u) := by
  have hpos : ∀ u ∈ uIcc (mγ ^ 2) (Λ ^ 2), 0 < x ^ 2 * m ^ 2 + (1 - x) * u := fun u hu =>
    onShell_denom_pos hm hx (lt_of_lt_of_le (lt_min (by positivity) (by positivity)) hu.1)
  rw [onShellL, Real.log_div (hpos _ right_mem_uIcc).ne' (hpos _ left_mem_uIcc).ne']
  exact log_sub_log_eq_integral hpos

/-- The density of the mass insertion in the squared photon mass,
`σ(u) = -(e²/8π²) ∫₀¹ (1 - x²) / (x² m² + (1 - x) u) dx`. -/
noncomputable def sigma (e m u : ℝ) : ℝ :=
  -(e ^ 2 / (8 * Real.pi ^ 2)) * ∫ x in (0 : ℝ)..1, (1 - x ^ 2) / (x ^ 2 * m ^ 2 + (1 - x) * u)

open QED.WickModel (onShellδ₂ onShellδm) in
/-- **The mass insertion as an integral over the squared photon mass**:
`δ = (B - A)(-m²) = ∫_{m_γ²}^{Λ²} σ(u) du`. -/
theorem onShellδm_sub_onShellδ₂_eq_integral_sigma (P : Params) (hm : P.m ≠ 0) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) :
    onShellδm P - onShellδ₂ P = ∫ u in P.mγ ^ 2..P.Λ ^ 2, sigma P.e P.m u := by
  have hu0 : ∀ u ∈ uIcc (P.mγ ^ 2) (P.Λ ^ 2), 0 < u := fun u hu =>
    lt_of_lt_of_le (lt_min (by positivity) (by positivity)) hu.1
  set G : ℝ → ℝ → ℝ := fun x u => (1 - x ^ 2) / (x ^ 2 * P.m ^ 2 + (1 - x) * u) with hG
  have hGc : ContinuousOn (Function.uncurry G) (Icc (0 : ℝ) 1 ×ˢ uIcc (P.mγ ^ 2) (P.Λ ^ 2)) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => ?_
    exact (onShell_denom_pos hm hz.1 (hu0 _ hz.2)).ne'
  have hGi : IntegrableOn (Function.uncurry G)
      (uIoc (0 : ℝ) 1 ×ˢ uIoc (P.mγ ^ 2) (P.Λ ^ 2)) := by
    refine (hGc.integrableOn_compact (isCompact_Icc.prod isCompact_uIcc)).mono_set ?_
    rw [uIoc_of_le zero_le_one]
    exact prod_mono Ioc_subset_Icc_self uIoc_subset_uIcc
  have hL : ∀ x ∈ uIcc (0 : ℝ) 1,
      -(P.e ^ 2 / (4 * Real.pi ^ 2)) * onShellL P.m P.mγ P.Λ x +
          P.e ^ 2 / (8 * Real.pi ^ 2) * ((1 - x) * onShellL P.m P.mγ P.Λ x) =
        -(P.e ^ 2 / (8 * Real.pi ^ 2)) * ∫ u in P.mγ ^ 2..P.Λ ^ 2, G x u := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    rw [onShellL_eq_integral hm hmγ hΛ hx, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add]
    · refine integral_congr fun u hu => ?_
      have hd := (onShell_denom_pos hm hx (hu0 u hu)).ne'
      simp only [hG]
      field_simp
      ring
    all_goals
      have hD : ∀ u ∈ uIcc (P.mγ ^ 2) (P.Λ ^ 2), x ^ 2 * P.m ^ 2 + (1 - x) * u ≠ 0 :=
        fun u hu => (onShell_denom_pos hm hx (hu0 u hu)).ne'
      have hI : ContinuousOn (fun u => (x ^ 2 * P.m ^ 2 + (1 - x) * u)⁻¹)
          (uIcc (P.mγ ^ 2) (P.Λ ^ 2)) := ContinuousOn.inv₀ (by fun_prop) hD
      refine ContinuousOn.intervalIntegrable ?_
      simp only [div_eq_mul_inv]
      first
        | exact continuousOn_const.mul (continuousOn_const.mul hI)
        | exact continuousOn_const.mul (continuousOn_const.mul (continuousOn_const.mul hI))
  have hLc : ContinuousOn (onShellL P.m P.mγ P.Λ) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    refine ContinuousOn.log ?_ fun x hx => ?_
    · refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
      exact (onShell_denom_pos hm hx (by positivity)).ne'
    · exact (div_pos (onShell_denom_pos hm hx (by positivity))
        (onShell_denom_pos hm hx (by positivity))).ne'
  rw [onShellδm_sub_onShellδ₂_eq_integral, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add, integral_congr hL,
    intervalIntegral.integral_const_mul, intervalIntegral_intervalIntegral_swap hGi]
  rotate_left
  · exact hLc.intervalIntegrable.const_mul _
  · exact (ContinuousOn.mul (by fun_prop) hLc).intervalIntegrable.const_mul _
  simp only [sigma, hG]
  rw [← intervalIntegral.integral_const_mul]

end QED.GradedProof.RPi4

end
