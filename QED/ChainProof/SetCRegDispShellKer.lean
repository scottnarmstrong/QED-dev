/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShare
public import QED.TwoLoop.UnitVPLink

/-!
# Set (c): the shell kernels of the VP-inserted self-energy and their integrability

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS` of
`QED.ChainProof.SetCRegDisp.setCRegLimitDisp_of_pieces` through
`QED.ChainProof.SetCRegDisp.isDispPV_S_of_shell`. That theorem needs `ShellDisp P₀ w₀ w₁`: the
shell value `σ₀` and slope `σ₁` of the selected order-`4` self-energy are dispersion integrals
with kernels `w₀`, `w₁`. This file fixes the expected kernels and proves everything about
`ShellDisp` except the two value identities.

**The one-loop self-energy of a photon function.** Replacing the Pauli–Villars photon
`D(s) = 1/(s + m_γ²) - 1/(s + Λ²)` of the one-loop self-energy by a photon function `R`, the
frozen coefficients (`QED.WickModel.selfEnergyLoopA`, `QED.WickModel.selfEnergyLoopB`,
`log(D_Λ/D_{m_γ}) = ∫_a^∞ D`) become
`A_R(s) = -(e²/8π²) ∫₀¹ (1-x) ∫_a^∞ R`, `B_R(s) = -(e²/4π²) ∫₀¹ ∫_a^∞ R`,
`a = x(m² + (1-x)s)/(1-x)`. On the shell `a = m² x²/(1-x)` and `∂ₛ a = x`, so the shell value
`A(-m²)(-m) + B(-m²) m` and the slope of `GEx2.shellFun` at `-m` are
`-(e² m/8π²) ∫₀¹ (1+x) Tail(a₀)` and `(e²/8π²) ∫₀¹ (2m² x(1+x) R(a₀) - (1-x) Tail(a₀))`.

**The inserted photon.** As for the vertex (`QED.TwoLoop.UnitVPLink.vpOuterF2`, with
`δ₃ = Π_loop(0)` and `QED.TwoLoop.UnitVPLink.vacuumPolarizationLoop_sub_zero`), the VP-inserted
photon function is `(e²/4π²) ∑_f c_f ∫₀¹ ρ(v) s²/(s + T_f m²) D(s)² dv`, `T_f = (M_f²/m²) t_v`,
the flavour structure of `dispPVF`. Hence the kernels `shellKer₀`, `shellKer₁` below, with
`R_T(s) = s²/(s + T m²) D(s)²` (`vpPhotonT`). The value identities are not proved here.

## Main statements

* `vpPhotonT`, `photonTail`, `seShellVal`, `seShellSlope`, `shellKer₀`, `shellKer₁`;
* `vpPhotonT_nonneg`, `vpPhotonT_le`: `0 ≤ R_T(s) ≤ K/(T m²) (1 + s²)⁻¹` for `s ≥ 0`;
* `photonTail_nonneg`, `photonTail_le`: `0 ≤ ∫_a^∞ R_T ≤ π K/(T m²)` for `a ≥ 0`;
* **`norm_shellKer₀_le`**, **`norm_shellKer₁_le`**: `‖w(T)‖ ≤ C/T` for `T > 0`;
* `measurable_shellKer₀`, `measurable_shellKer₁`;
* **`integrableOn_dispPVF_of_le`**: any measurable kernel with `‖u(T)‖ ≤ C/T` has an integrable
  flavour-summed dispersion integrand on `(0, 1)`;
* **`shellDisp_of_values`**: `ShellDisp P₀ (shellKer₀ P₀) (shellKer₁ P₀)` from the two value
  identities `σ₀ = ∫ dispPVF (shellKer₀)`, `σ₁ = ∫ dispPVF (shellKer₁)` alone.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.TwoLoop.UnitVPLink (photonVar photonD photonVar_nonneg)
open QED.ChainProof.SetCK QED.ChainProof.SetCPauli

/-! ### The kernels -/

/-- **The VP-inserted photon function** at spectral mass² `T m²`, without its charge factor:
`R_T(s) = s²/(s + T m²) D(s)²`. -/
noncomputable def vpPhotonT (m mγ Λ T s : ℝ) : ℝ :=
  s ^ 2 / (s + T * m ^ 2) * photonD mγ Λ s ^ 2

/-- The tail `∫_a^∞ R = ∫_{u > 0} R(a + u)` of a photon function. -/
noncomputable def photonTail (R : ℝ → ℝ) (a : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), R (a + u)

/-- The shell argument `a₀ = m² x²/(1-x)` of the photon function. -/
noncomputable def shellArg (m x : ℝ) : ℝ := m ^ 2 * photonVar x

/-- The shell-value integral `∫₀¹ (1+x) Tail_R(a₀) dx`. -/
noncomputable def seShellVal (R : ℝ → ℝ) (m : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, (1 + x) * photonTail R (shellArg m x)

/-- The shell-slope integral `∫₀¹ (2m² x(1+x) R(a₀) - (1-x) Tail_R(a₀)) dx`. -/
noncomputable def seShellSlope (R : ℝ → ℝ) (m : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    (2 * m ^ 2 * x * (1 + x) * R (shellArg m x) - (1 - x) * photonTail R (shellArg m x))

/-- **The expected kernel of the shell value** `σ₀`:
`-(e⁴ m/(32π⁴)) ∫₀¹ (1+x) Tail_{R_T}(a₀) dx`. -/
noncomputable def shellKer₀ (P₀ : Params) (mγ Λ T : ℝ) : ℂ :=
  ((-(P₀.e ^ 4 * P₀.m) / (32 * Real.pi ^ 4) * seShellVal (vpPhotonT P₀.m mγ Λ T) P₀.m : ℝ) : ℂ)

/-- **The expected kernel of the shell slope** `σ₁`:
`(e⁴/(32π⁴)) ∫₀¹ (2m² x(1+x) R_T(a₀) - (1-x) Tail_{R_T}(a₀)) dx`. -/
noncomputable def shellKer₁ (P₀ : Params) (mγ Λ T : ℝ) : ℂ :=
  ((P₀.e ^ 4 / (32 * Real.pi ^ 4) * seShellSlope (vpPhotonT P₀.m mγ Λ T) P₀.m : ℝ) : ℂ)

/-! ### Bounds on the photon function and its tail -/

/-- The constant `K = (Λ² - m_γ²)²/min(1, Λ⁴)` of the photon bound. -/
noncomputable def photonK (mγ Λ : ℝ) : ℝ := (Λ ^ 2 - mγ ^ 2) ^ 2 / min 1 (Λ ^ 4)

section Bounds

variable {m mγ Λ T : ℝ}

theorem photonK_nonneg (mγ Λ : ℝ) : 0 ≤ photonK mγ Λ := by
  unfold photonK
  have : 0 ≤ min 1 (Λ ^ 4) := le_min zero_le_one (by positivity)
  positivity

theorem vpPhotonT_eq (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) (hm : 0 < m) {s : ℝ}
    (hs : 0 ≤ s) : vpPhotonT m mγ Λ T s =
      (s / (s + mγ ^ 2)) ^ 2 * ((Λ ^ 2 - mγ ^ 2) ^ 2 / ((s + T * m ^ 2) * (s + Λ ^ 2) ^ 2)) := by
  have h1 : s + mγ ^ 2 ≠ 0 := by positivity
  have h2 : s + Λ ^ 2 ≠ 0 := by positivity
  have h3 : s + T * m ^ 2 ≠ 0 := by positivity
  unfold vpPhotonT photonD
  field_simp
  ring

theorem vpPhotonT_nonneg (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) (hm : 0 < m) {s : ℝ}
    (hs : 0 ≤ s) : 0 ≤ vpPhotonT m mγ Λ T s := by
  rw [vpPhotonT_eq hmγ hΛ hT hm hs]
  positivity

/-- **The photon bound**: `R_T(s) ≤ K/(T m²) (1 + s²)⁻¹` for `s ≥ 0`. -/
theorem vpPhotonT_le (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) (hm : 0 < m) {s : ℝ}
    (hs : 0 ≤ s) : vpPhotonT m mγ Λ T s ≤ photonK mγ Λ / (T * m ^ 2) * (1 + s ^ 2)⁻¹ := by
  rw [vpPhotonT_eq hmγ hΛ hT hm hs]
  set μ := min 1 (Λ ^ 4) with hμ
  have hμ0 : 0 < μ := lt_min one_pos (by positivity)
  have hμ1 : μ ≤ 1 := min_le_left _ _
  have hμΛ : μ ≤ Λ ^ 4 := min_le_right _ _
  have hq : (s / (s + mγ ^ 2)) ^ 2 ≤ 1 :=
    pow_le_one₀ (by positivity) ((div_le_one (by positivity)).2 (by nlinarith))
  have hB : μ * (1 + s ^ 2) ≤ (s + Λ ^ 2) ^ 2 := by
    have : μ * s ^ 2 ≤ s ^ 2 := mul_le_of_le_one_left (sq_nonneg s) hμ1
    nlinarith [mul_nonneg hs (sq_nonneg Λ)]
  have hden : T * m ^ 2 * (μ * (1 + s ^ 2)) ≤ (s + T * m ^ 2) * (s + Λ ^ 2) ^ 2 :=
    mul_le_mul (by linarith) hB (by positivity) (by positivity)
  have hR : (Λ ^ 2 - mγ ^ 2) ^ 2 / ((s + T * m ^ 2) * (s + Λ ^ 2) ^ 2) ≤
      photonK mγ Λ / (T * m ^ 2) * (1 + s ^ 2)⁻¹ := by
    have e : photonK mγ Λ / (T * m ^ 2) * (1 + s ^ 2)⁻¹ =
        (Λ ^ 2 - mγ ^ 2) ^ 2 / (T * m ^ 2 * (μ * (1 + s ^ 2))) := by
      unfold photonK
      rw [← hμ]
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
  calc (s / (s + mγ ^ 2)) ^ 2 * ((Λ ^ 2 - mγ ^ 2) ^ 2 / ((s + T * m ^ 2) * (s + Λ ^ 2) ^ 2))
      ≤ 1 * ((Λ ^ 2 - mγ ^ 2) ^ 2 / ((s + T * m ^ 2) * (s + Λ ^ 2) ^ 2)) :=
        mul_le_mul_of_nonneg_right hq (by positivity)
    _ ≤ _ := by rw [one_mul]; exact hR

theorem measurable_vpPhotonT (m mγ Λ : ℝ) :
    Measurable fun q : ℝ × ℝ => vpPhotonT m mγ Λ q.1 q.2 := by
  unfold vpPhotonT photonD
  fun_prop

theorem integrableOn_vpPhotonT_shift (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) (hm : 0 < m)
    {a : ℝ} (ha : 0 ≤ a) : IntegrableOn (fun u => vpPhotonT m mγ Λ T (a + u)) (Ioi 0) := by
  refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul
    (photonK mγ Λ / (T * m ^ 2))).integrableOn) ?_ ?_
  · exact ((measurable_vpPhotonT m mγ Λ).comp (measurable_const.prodMk
      (measurable_const.add measurable_id))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have hu0 : 0 ≤ u := le_of_lt hu
    have hs : 0 ≤ a + u := by linarith
    rw [Real.norm_of_nonneg (vpPhotonT_nonneg hmγ hΛ hT hm hs)]
    refine (vpPhotonT_le hmγ hΛ hT hm hs).trans (mul_le_mul_of_nonneg_left ?_ ?_)
    · exact inv_anti₀ (by positivity) (by nlinarith)
    · exact div_nonneg (photonK_nonneg _ _) (by positivity)

theorem photonTail_nonneg (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) (hm : 0 < m) {a : ℝ}
    (ha : 0 ≤ a) : 0 ≤ photonTail (vpPhotonT m mγ Λ T) a :=
  setIntegral_nonneg measurableSet_Ioi fun u hu =>
    vpPhotonT_nonneg hmγ hΛ hT hm (by have : 0 < u := hu; linarith)

/-- **The tail bound**: `∫_a^∞ R_T ≤ π K/(T m²)` for `a ≥ 0`. -/
theorem photonTail_le (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) (hm : 0 < m) {a : ℝ}
    (ha : 0 ≤ a) : photonTail (vpPhotonT m mγ Λ T) a ≤ photonK mγ Λ / (T * m ^ 2) * Real.pi := by
  set c := photonK mγ Λ / (T * m ^ 2)
  have hc : 0 ≤ c := div_nonneg (photonK_nonneg _ _) (by positivity)
  have hg : Integrable (fun u : ℝ => c * (1 + u ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul c
  calc photonTail (vpPhotonT m mγ Λ T) a ≤ ∫ u in Ioi (0 : ℝ), c * (1 + u ^ 2)⁻¹ := by
        refine setIntegral_mono_on (integrableOn_vpPhotonT_shift hmγ hΛ hT hm ha)
          hg.integrableOn measurableSet_Ioi fun u hu => ?_
        have hu0 : 0 ≤ u := le_of_lt hu
        refine (vpPhotonT_le hmγ hΛ hT hm (by linarith)).trans
          (mul_le_mul_of_nonneg_left ?_ hc)
        exact inv_anti₀ (by positivity) (by nlinarith)
    _ ≤ ∫ u : ℝ, c * (1 + u ^ 2)⁻¹ :=
        setIntegral_le_integral hg (Eventually.of_forall fun u => by positivity)
    _ = c * Real.pi := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

theorem shellArg_nonneg (m : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ shellArg m x :=
  mul_nonneg (sq_nonneg m) (photonVar_nonneg hx)

theorem norm_seShellVal_le (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) (hm : 0 < m) :
    ‖seShellVal (vpPhotonT m mγ Λ T) m‖ ≤ 2 * (photonK mγ Λ / (T * m ^ 2) * Real.pi) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := 2 * (photonK mγ Λ / (T * m ^ 2) * Real.pi))
    (f := fun x => (1 + x) * photonTail (vpPhotonT m mγ Λ T) (shellArg m x)) ?_
  · simpa [seShellVal] using h
  intro x hx
  rw [uIoc_of_le zero_le_one] at hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hx
  have ha := shellArg_nonneg m hx'
  have h0 := photonTail_nonneg hmγ hΛ hT hm ha
  have h1 := photonTail_le hmγ hΛ hT hm ha
  rw [Real.norm_of_nonneg (mul_nonneg (by linarith [hx.1]) h0)]
  exact mul_le_mul (by linarith [hx.2]) h1 h0 zero_le_two

theorem norm_seShellSlope_le (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) (hm : 0 < m) :
    ‖seShellSlope (vpPhotonT m mγ Λ T) m‖ ≤
      (4 * m ^ 2 + Real.pi) * (photonK mγ Λ / (T * m ^ 2)) := by
  set c := photonK mγ Λ / (T * m ^ 2)
  have hc : 0 ≤ c := div_nonneg (photonK_nonneg _ _) (by positivity)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := (4 * m ^ 2 + Real.pi) * c)
    (f := fun x => 2 * m ^ 2 * x * (1 + x) * vpPhotonT m mγ Λ T (shellArg m x) -
      (1 - x) * photonTail (vpPhotonT m mγ Λ T) (shellArg m x)) ?_
  · simpa [seShellSlope] using h
  intro x hx
  rw [uIoc_of_le zero_le_one] at hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hx
  have ha := shellArg_nonneg m hx'
  have h0 := photonTail_nonneg hmγ hΛ hT hm ha
  have h1 := photonTail_le hmγ hΛ hT hm ha
  have r0 := vpPhotonT_nonneg hmγ hΛ hT hm ha
  have r1 : vpPhotonT m mγ Λ T (shellArg m x) ≤ c := by
    refine (vpPhotonT_le hmγ hΛ hT hm ha).trans ?_
    calc c * (1 + shellArg m x ^ 2)⁻¹ ≤ c * 1 :=
          mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ (by nlinarith)) hc
      _ = c := mul_one c
  have hx0 : 0 ≤ x := hx'.1
  have hx1 : x ≤ 1 := hx'.2
  have hA : 0 ≤ 2 * m ^ 2 * x * (1 + x) := by positivity
  have hA' : 2 * m ^ 2 * x * (1 + x) ≤ 4 * m ^ 2 := by
    have : x * (1 + x) ≤ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg m)]
  have hP1 : 2 * m ^ 2 * x * (1 + x) * vpPhotonT m mγ Λ T (shellArg m x) ≤ 4 * m ^ 2 * c :=
    mul_le_mul hA' r1 r0 (by positivity)
  have hP2 : (1 - x) * photonTail (vpPhotonT m mγ Λ T) (shellArg m x) ≤ Real.pi * c := by
    calc (1 - x) * photonTail (vpPhotonT m mγ Λ T) (shellArg m x) ≤ 1 * (c * Real.pi) :=
          mul_le_mul (by linarith) h1 h0 zero_le_one
      _ = Real.pi * c := by ring
  have hP1' : 0 ≤ 2 * m ^ 2 * x * (1 + x) * vpPhotonT m mγ Λ T (shellArg m x) :=
    mul_nonneg hA r0
  have hP2' : 0 ≤ (1 - x) * photonTail (vpPhotonT m mγ Λ T) (shellArg m x) :=
    mul_nonneg (by linarith) h0
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [Real.pi_pos]

end Bounds

/-! ### The kernel bounds and measurability -/

section Kernel

variable (P₀ : Params) {mγ Λ : ℝ}

/-- **The shell-value kernel decays like `1/T`.** -/
theorem norm_shellKer₀_le (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hm : 0 < P₀.m) {T : ℝ} (hT : 0 < T) :
    ‖shellKer₀ P₀ mγ Λ T‖ ≤
      |(-(P₀.e ^ 4 * P₀.m) / (32 * Real.pi ^ 4))| * (2 * (photonK mγ Λ / P₀.m ^ 2 * Real.pi)) /
        T := by
  unfold shellKer₀
  rw [Complex.norm_real, norm_mul, Real.norm_eq_abs, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (norm_seShellVal_le hmγ hΛ hT hm).trans (le_of_eq ?_)
  field_simp

/-- **The shell-slope kernel decays like `1/T`.** -/
theorem norm_shellKer₁_le (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hm : 0 < P₀.m) {T : ℝ} (hT : 0 < T) :
    ‖shellKer₁ P₀ mγ Λ T‖ ≤
      |P₀.e ^ 4 / (32 * Real.pi ^ 4)| * ((4 * P₀.m ^ 2 + Real.pi) * (photonK mγ Λ / P₀.m ^ 2)) /
        T := by
  unfold shellKer₁
  rw [Complex.norm_real, norm_mul, Real.norm_eq_abs, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (norm_seShellSlope_le hmγ hΛ hT hm).trans (le_of_eq ?_)
  field_simp

theorem measurable_photonTail_vp (m mγ Λ : ℝ) :
    Measurable fun q : ℝ × ℝ => photonTail (vpPhotonT m mγ Λ q.1) q.2 := by
  have hf : StronglyMeasurable fun r : (ℝ × ℝ) × ℝ => vpPhotonT m mγ Λ r.1.1 (r.1.2 + r.2) :=
    ((measurable_vpPhotonT m mγ Λ).comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).add measurable_snd))).stronglyMeasurable
  exact (hf.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))).measurable

theorem measurable_shellArg (m : ℝ) : Measurable (shellArg m) := by
  unfold shellArg photonVar
  fun_prop

theorem measurable_seShellVal (m mγ Λ : ℝ) :
    Measurable fun T => seShellVal (vpPhotonT m mγ Λ T) m := by
  have hf : StronglyMeasurable fun r : ℝ × ℝ =>
      (1 + r.2) * photonTail (vpPhotonT m mγ Λ r.1) (shellArg m r.2) :=
    ((measurable_const.add measurable_snd).mul ((measurable_photonTail_vp m mγ Λ).comp
      (measurable_fst.prodMk ((measurable_shellArg m).comp measurable_snd)))).stronglyMeasurable
  have h := (hf.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1))).measurable
  convert h using 1
  funext T
  simp only [seShellVal, intervalIntegral.integral_of_le zero_le_one]

theorem measurable_seShellSlope (m mγ Λ : ℝ) :
    Measurable fun T => seShellSlope (vpPhotonT m mγ Λ T) m := by
  have hP : Measurable fun r : ℝ × ℝ => vpPhotonT m mγ Λ r.1 (shellArg m r.2) :=
    (measurable_vpPhotonT m mγ Λ).comp
      (measurable_fst.prodMk ((measurable_shellArg m).comp measurable_snd))
  have hT : Measurable fun r : ℝ × ℝ => photonTail (vpPhotonT m mγ Λ r.1) (shellArg m r.2) :=
    (measurable_photonTail_vp m mγ Λ).comp
      (measurable_fst.prodMk ((measurable_shellArg m).comp measurable_snd))
  have hf : StronglyMeasurable fun r : ℝ × ℝ =>
      2 * m ^ 2 * r.2 * (1 + r.2) * vpPhotonT m mγ Λ r.1 (shellArg m r.2) -
        (1 - r.2) * photonTail (vpPhotonT m mγ Λ r.1) (shellArg m r.2) :=
    ((((measurable_const.mul measurable_snd).mul (measurable_const.add measurable_snd)).mul
      hP).sub ((measurable_const.sub measurable_snd).mul hT)).stronglyMeasurable
  have h := (hf.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1))).measurable
  convert h using 1
  funext T
  simp only [seShellSlope, intervalIntegral.integral_of_le zero_le_one]

theorem measurable_shellKer₀ (mγ Λ : ℝ) : Measurable (shellKer₀ P₀ mγ Λ) :=
  Complex.measurable_ofReal.comp (measurable_const.mul (measurable_seShellVal P₀.m mγ Λ))

theorem measurable_shellKer₁ (mγ Λ : ℝ) : Measurable (shellKer₁ P₀ mγ Λ) :=
  Complex.measurable_ofReal.comp (measurable_const.mul (measurable_seShellSlope P₀.m mγ Λ))

end Kernel

/-! ### Integrability of the dispersion integrand -/

theorem measurable_setCKSpecRho : Measurable setCKSpecRho := by
  unfold setCKSpecRho
  fun_prop

theorem measurable_setCKSpecMass : Measurable setCKSpecMass := by
  unfold setCKSpecMass
  fun_prop

/-- **A kernel decaying like `1/T` has an integrable dispersion integrand**: on `(0, 1)`,
`|ρ(v)| ≤ t_v/4` and `‖u(r t_v)‖ ≤ C/(r t_v)`, so the integrand is bounded. -/
theorem integrableOn_dispPVF_of_le {m M₁ M₂ c₁ c₂ : ℝ} (hm : m ≠ 0) (hM₁ : M₁ ≠ 0)
    (hM₂ : M₂ ≠ 0) {u : ℝ → ℂ} (hu : Measurable u) {C : ℝ}
    (hC : ∀ T, 0 < T → ‖u T‖ ≤ C / T) :
    IntegrableOn (dispPVF m M₁ M₂ c₁ c₂ u) (Ioo 0 1) := by
  have hs := measurable_setCKSpecMass
  have hmeas : Measurable (dispPVF m M₁ M₂ c₁ c₂ u) := by
    unfold dispPVF
    exact (Complex.measurable_ofReal.comp measurable_setCKSpecRho).mul
      (((hu.comp hs).add (measurable_const.mul (hu.comp (measurable_const.mul hs)))).add
        (measurable_const.mul (hu.comp (measurable_const.mul hs))))
  have hr₁ : 0 < M₁ ^ 2 / m ^ 2 := by positivity
  have hr₂ : 0 < M₂ ^ 2 / m ^ 2 := by positivity
  refine Measure.integrableOn_of_bounded
    (M := C / 4 * (1 + |c₁| / (M₁ ^ 2 / m ^ 2) + |c₂| / (M₂ ^ 2 / m ^ 2))) (by simp)
    hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun v hv => ?_)
  obtain ⟨hv0, hv1⟩ := hv
  have hw : 0 < 1 - v ^ 2 := by nlinarith
  have ht4 : setCKSpecMass v / 4 = 1 / (1 - v ^ 2) := by
    rw [setCKSpecMass]
    field_simp
  have htpos : 0 < setCKSpecMass v := by rw [setCKSpecMass]; positivity
  have hρ : ‖(setCKSpecRho v : ℂ)‖ ≤ setCKSpecMass v / 4 := by
    have h0 : 0 ≤ v ^ 2 * (1 - v ^ 2 / 3) := mul_nonneg (sq_nonneg v) (by nlinarith)
    rw [Complex.norm_real, Real.norm_eq_abs, setCKSpecRho, abs_div, abs_of_pos hw,
      abs_of_nonneg h0, ht4]
    exact div_le_div_of_nonneg_right (by nlinarith) hw.le
  set t := setCKSpecMass v
  have e1 := hC t htpos
  have e2 := hC (M₁ ^ 2 / m ^ 2 * t) (mul_pos hr₁ htpos)
  have e3 := hC (M₂ ^ 2 / m ^ 2 * t) (mul_pos hr₂ htpos)
  have hS : ‖u t + (c₁ : ℂ) * u (M₁ ^ 2 / m ^ 2 * t) + (c₂ : ℂ) * u (M₂ ^ 2 / m ^ 2 * t)‖ ≤
      C / t * (1 + |c₁| / (M₁ ^ 2 / m ^ 2) + |c₂| / (M₂ ^ 2 / m ^ 2)) := by
    refine norm_add₃_le.trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    have e : C / t * (1 + |c₁| / (M₁ ^ 2 / m ^ 2) + |c₂| / (M₂ ^ 2 / m ^ 2)) =
        C / t + |c₁| * (C / (M₁ ^ 2 / m ^ 2 * t)) + |c₂| * (C / (M₂ ^ 2 / m ^ 2 * t)) := by
      field_simp
    rw [e]
    exact add_le_add (add_le_add e1 (mul_le_mul_of_nonneg_left e2 (abs_nonneg _)))
      (mul_le_mul_of_nonneg_left e3 (abs_nonneg _))
  simp only [dispPVF]
  rw [norm_mul]
  calc _ ≤ t / 4 * (C / t * (1 + |c₁| / (M₁ ^ 2 / m ^ 2) + |c₂| / (M₂ ^ 2 / m ^ 2))) :=
        mul_le_mul hρ hS (norm_nonneg _) (by positivity)
    _ = _ := by field_simp

/-! ### The reduction of `ShellDisp` to the two value identities -/

open QED.ChainProof.SetAPauli (regParams regFlavors) in
/-- **`ShellDisp` from the value identities alone**: the integrability conjuncts of `IsDispPV`
hold for `shellKer₀`, `shellKer₁` at every admissible datum. -/
theorem shellDisp_of_values {P₀ : Params}
    (hval : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ r : ℝ, 0 < r →
      ∀ A B : ℝ → ℂ, SetCLink.SELimitSel (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) (SetCLink.dZero D) r A B → ∀ σ₀ σ₁ : ℝ,
      A (-P₀.m ^ 2) * ((-P₀.m : ℝ) : ℂ) + B (-P₀.m ^ 2) * P₀.m = σ₀ →
      HasDerivAt (QED.GradedProof.GEx2.shellFun A B P₀.m) σ₁ (-P₀.m) →
      (σ₀ : ℂ) = ∫ v in Ioo (0 : ℝ) 1, dispPVF P₀.m M₁ M₂ c₁ c₂ (shellKer₀ P₀ mγ Λ) v ∧
        (σ₁ : ℂ) = ∫ v in Ioo (0 : ℝ) 1, dispPVF P₀.m M₁ M₂ c₁ c₂ (shellKer₁ P₀ mγ Λ) v) :
    ShellDisp P₀ (shellKer₀ P₀) (shellKer₁ P₀) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA r hr A B hlim σ₀ σ₁ h₀ h₁
  obtain ⟨hM₁, hM₂, -, -, hmγ, hΛ, -, hm2, -, -⟩ := id hA
  have hm : 0 < P₀.m := by linarith
  obtain ⟨v₀, v₁⟩ := hval M₁ M₂ c₁ c₂ mγ Λ D s hA r hr A B hlim σ₀ σ₁ h₀ h₁
  exact ⟨⟨integrableOn_dispPVF_of_le hm.ne' (hm.trans hM₁).ne' (hm.trans hM₂).ne'
      (measurable_shellKer₀ P₀ mγ Λ) fun T hT => norm_shellKer₀_le P₀ hmγ hΛ hm hT, v₀⟩,
    ⟨integrableOn_dispPVF_of_le hm.ne' (hm.trans hM₁).ne' (hm.trans hM₂).ne'
      (measurable_shellKer₁ P₀ mγ Λ) fun T hT => norm_shellKer₁_le P₀ hmγ hΛ hm hT, v₁⟩⟩

end QED.ChainProof.SetCRegDisp

end
