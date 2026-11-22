/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegKKLim
public import QED.ChainProof.SetCRegKKVal

/-!
# Set (c): the scalar Källén–Lehmann limit, and the cancellation above threshold

`QED/ChainProof/SetCRegKKLim.lean` evaluates the `ε → 0⁺` limit of the scalar integral
as `8 i π² ∫_{Δ₄} M(x)⁻² dx`. The Euclidean match with the VP-inserted photon function
`vpPhotonT` of `QED/ChainProof/SetCRegDispShellKer.lean` is the real Feynman formula

  `((s + c)(s + a)²(s + b)²)⁻¹ = 24 ∫_{Δ₄} (s + M(x))⁻⁵ dx`  (`s ≥ 0`),

integrated against `s²` over `s > 0` with `∫₀^∞ s² (s + A)⁻⁵ ds = 1/(12 A²)`:

  `∫₀^∞ s² ((s + c)(s + a)²(s + b)²)⁻¹ ds = 2 ∫_{Δ₄} M(x)⁻² dx`.

Since `vpPhotonT(s) = (b - a)² s² ((s + c)(s + a)²(s + b)²)⁻¹` with `c = T m²`, the limit
is `4 i π² Tail/(Λ² - mγ²)²`, which is `IsKKSclLim m` of
`QED/ChainProof/SetCRegKKVal.lean`.

## Main results

* `integral_Ioi_kkProd`: the Euclidean match above.
* `isKKSclLim`: `IsKKSclLim m` for `0 < m`.
* `isKKSumGe`, `isKKCancelGe`: the Källén–Lehmann sum and the cancellation above
  threshold, for `0 < P₀.m` (and `P₀.e ≠ 0` for the cancellation).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.Integration QED.Integration.Feynman
open QED.Integration.TwoLoop (simplexPoint_castSucc simplexPoint_last)

/-! ### The real Feynman formula -/

theorem simplexComb_kkMass (c a b s : ℝ) (x : Fin 4 → ℝ) :
    simplexComb (fun i => -I * ((s + kkMass c a b i : ℝ) : ℂ)) x =
      -I * ((s + kkM c a b x : ℝ) : ℂ) := by
  have p0 : simplexPoint x 0 = x 0 := simplexPoint_castSucc x 0
  have p1 : simplexPoint x 1 = x 1 := simplexPoint_castSucc x 1
  have p2 : simplexPoint x 2 = x 2 := simplexPoint_castSucc x 2
  have p3 : simplexPoint x 3 = x 3 := simplexPoint_castSucc x 3
  have p4 : simplexPoint x 4 = 1 - ∑ i, x i := simplexPoint_last x
  rw [simplexComb_eq_sum_simplexPoint, Fin.sum_univ_five, p0, p1, p2, p3, p4]
  simp only [kkM, kkMass, Fin.sum_univ_four]
  simp
  ring

/-- **The real Feynman formula** for the five Euclidean denominators. -/
theorem kkFeynReal {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) {s : ℝ}
    (hs : 0 ≤ s) :
    ((s + c) * (s + a) ^ 2 * (s + b) ^ 2)⁻¹ =
      24 * ∫ x in simplexSet 4, ((s + kkM c a b x) ^ 5)⁻¹ := by
  have him : ∀ i, (-I * ((s + kkMass c a b i : ℝ) : ℂ)).im < 0 := by
    intro i
    fin_cases i <;> simp [kkMass] <;> linarith
  have h := prod_inv_eq_factorial_mul_integral_simplex him
  have hpt : ∀ x : Fin 4 → ℝ, (simplexComb (fun i => -I * ((s + kkMass c a b i : ℝ) : ℂ)) x ^
      (4 + 1))⁻¹ = (-I)⁻¹ ^ 5 * ((((s + kkM c a b x) ^ 5)⁻¹ : ℝ) : ℂ) := fun x => by
    rw [simplexComb_kkMass, show (4 + 1 : ℕ) = 5 from rfl, mul_pow, mul_inv, inv_pow, ofReal_inv,
      ofReal_pow]
  have k0 : kkMass c a b 0 = c := rfl
  have k1 : kkMass c a b 1 = a := rfl
  have k2 : kkMass c a b 2 = a := rfl
  have k3 : kkMass c a b 3 = b := rfl
  have k4 : kkMass c a b 4 = b := rfl
  rw [Fin.prod_univ_five, k0, k1, k2, k3, k4] at h
  simp only [hpt] at h
  rw [integral_const_mul, integral_complex_ofReal] at h
  have hne : ((-I)⁻¹ ^ 5 : ℂ) ≠ 0 := pow_ne_zero _ (inv_ne_zero (neg_ne_zero.2 I_ne_zero))
  have hl : (-I * ((s : ℂ) + c))⁻¹ * (-I * ((s : ℂ) + a))⁻¹ * (-I * ((s : ℂ) + a))⁻¹ *
      (-I * ((s : ℂ) + b))⁻¹ * (-I * ((s : ℂ) + b))⁻¹ =
      (-I)⁻¹ ^ 5 * (((s : ℂ) + c)⁻¹ * (((s : ℂ) + a)⁻¹) ^ 2 * (((s : ℂ) + b)⁻¹) ^ 2) := by
    simp only [mul_inv]
    ring
  have h2 : ((((s + c) * (s + a) ^ 2 * (s + b) ^ 2)⁻¹ : ℝ) : ℂ) =
      ((s : ℂ) + c)⁻¹ * (((s : ℂ) + a)⁻¹) ^ 2 * (((s : ℂ) + b)⁻¹) ^ 2 := by
    push_cast
    simp only [mul_inv, inv_pow]
  push_cast at h
  have h' : (-I)⁻¹ ^ 5 * ((((s + c) * (s + a) ^ 2 * (s + b) ^ 2)⁻¹ : ℝ) : ℂ) =
      (-I)⁻¹ ^ 5 * ((24 * ∫ x in simplexSet 4, ((s + kkM c a b x) ^ 5)⁻¹ : ℝ) : ℂ) := by
    rw [h2, ← hl, h]
    push_cast [Nat.factorial]
    ring
  exact_mod_cast mul_left_cancel₀ hne h'

/-! ### The radial integral `∫₀^∞ s² (s + A)⁻⁵ ds` -/

theorem hasDerivAt_kkRad {A : ℝ} (hA : 0 < A) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (fun s : ℝ => -((s + A) ^ 2)⁻¹ / 2 + 2 * A * ((s + A) ^ 3)⁻¹ / 3 -
      A ^ 2 * ((s + A) ^ 4)⁻¹ / 4) (s ^ 2 * ((s + A) ^ 5)⁻¹) s := by
  have hne : s + A ≠ 0 := by positivity
  have hu : HasDerivAt (fun s : ℝ => s + A) 1 s := (hasDerivAt_id s).add_const A
  have h := ((((hu.pow 2).inv (pow_ne_zero _ hne)).neg.div_const 2).add
    ((((hu.pow 3).inv (pow_ne_zero _ hne)).const_mul (2 * A)).div_const 3)).sub
    ((((hu.pow 4).inv (pow_ne_zero _ hne)).const_mul (A ^ 2)).div_const 4)
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply]
  norm_num only
  field_simp
  ring

theorem tendsto_kkRad {A : ℝ} :
    Tendsto (fun s : ℝ => -((s + A) ^ 2)⁻¹ / 2 + 2 * A * ((s + A) ^ 3)⁻¹ / 3 -
      A ^ 2 * ((s + A) ^ 4)⁻¹ / 4) atTop (𝓝 0) := by
  have hk : ∀ k : ℕ, k ≠ 0 → Tendsto (fun s : ℝ => ((s + A) ^ k)⁻¹) atTop (𝓝 0) :=
    fun k hk => tendsto_inv_atTop_zero.comp
      ((tendsto_pow_atTop hk).comp (tendsto_atTop_add_const_right _ A tendsto_id))
  have h := (((hk 2 (by norm_num)).neg.div_const 2).add
    (((hk 3 (by norm_num)).const_mul (2 * A)).div_const 3)).sub
    (((hk 4 (by norm_num)).const_mul (A ^ 2)).div_const 4)
  simpa using h

theorem kkRad_nonneg {A : ℝ} (hA : 0 < A) : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ s ^ 2 * ((s + A) ^ 5)⁻¹ :=
  fun s hs => by
    have : 0 < s := hs
    positivity

theorem integrableOn_kkRad {A : ℝ} (hA : 0 < A) :
    IntegrableOn (fun s : ℝ => s ^ 2 * ((s + A) ^ 5)⁻¹) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun _ hs => hasDerivAt_kkRad hA hs) (kkRad_nonneg hA)
    tendsto_kkRad

/-- `∫₀^∞ s² (s + A)⁻⁵ ds = 1/(12 A²)`. -/
theorem integral_Ioi_kkRad {A : ℝ} (hA : 0 < A) :
    ∫ s in Ioi (0 : ℝ), s ^ 2 * ((s + A) ^ 5)⁻¹ = (12 * A ^ 2)⁻¹ := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun _ hs => hasDerivAt_kkRad hA hs)
    (kkRad_nonneg hA) tendsto_kkRad]
  field_simp
  ring

/-! ### The Euclidean match -/

/-- **The Euclidean match**:
`∫₀^∞ s² ((s + c)(s + a)²(s + b)²)⁻¹ ds = 2 ∫_{Δ₄} M(x)⁻² dx`. -/
theorem integral_Ioi_kkProd {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) :
    ∫ s in Ioi (0 : ℝ), s ^ 2 * ((s + c) * (s + a) ^ 2 * (s + b) ^ 2)⁻¹ =
      2 * ∫ x in simplexSet 4, (kkM c a b x ^ 2)⁻¹ := by
  have := isFiniteMeasure_simplex
  have hμ : 0 < min c (min a b) := lt_min hc (lt_min ha hb)
  set g : ℝ → (Fin 4 → ℝ) → ℝ := fun s x => s ^ 2 * (24 * ((s + kkM c a b x) ^ 5)⁻¹)
  have hpt : ∀ s ∈ Ioi (0 : ℝ), s ^ 2 * ((s + c) * (s + a) ^ 2 * (s + b) ^ 2)⁻¹ =
      ∫ x in simplexSet 4, g s x := fun s hs => by
    rw [kkFeynReal hc ha hb (le_of_lt hs), ← integral_const_mul, ← integral_const_mul]
  have hae : ∀ᵐ p ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (simplexSet 4))),
      p ∈ Ioi 0 ×ˢ simplexSet 4 := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod (measurableSet_simplexSet 4))
  have hmeas : Measurable (Function.uncurry g) := by
    have h1 : Continuous fun p : ℝ × (Fin 4 → ℝ) => (p.1 + kkM c a b p.2) ^ 5 := by
      unfold kkM
      fun_prop
    exact (measurable_fst.pow_const 2).mul (measurable_const.mul h1.measurable.inv)
  have hint : Integrable (Function.uncurry g)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (simplexSet 4))) := by
    refine Integrable.mono' ((((integrableOn_kkRad hμ).const_mul 24)).mul_prod
      (integrable_const (1 : ℝ))) hmeas.aestronglyMeasurable ?_
    filter_upwards [hae] with p hp
    obtain ⟨hs, hx⟩ := hp
    have hs' : 0 < p.1 := hs
    have hM := (kkM_bounds hc ha hb hx).1
    have hA : 0 < kkM c a b p.2 := hμ.trans_le hM
    simp only [Function.uncurry, g]
    rw [Real.norm_of_nonneg (by positivity), mul_one, mul_left_comm]
    gcongr
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_integral_swap hint,
    setIntegral_congr_fun (measurableSet_simplexSet 4)
      (g := fun x => 2 * (kkM c a b x ^ 2)⁻¹), integral_const_mul]
  intro x hx
  have hA : 0 < kkM c a b x := hμ.trans_le (kkM_bounds hc ha hb hx).1
  simp only [g]
  simp_rw [mul_left_comm _ (24 : ℝ)]
  rw [integral_const_mul, integral_Ioi_kkRad hA]
  field_simp
  norm_num

/-- The tail of the VP-inserted photon function as a Euclidean integral. -/
theorem photonTail_vpPhotonT {m mγ Λ T : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (hT : 0 < T) :
    photonTail (vpPhotonT m mγ Λ T) 0 = (Λ ^ 2 - mγ ^ 2) ^ 2 *
      ∫ s in Ioi (0 : ℝ), s ^ 2 * ((s + T * m ^ 2) * (s + mγ ^ 2) ^ 2 * (s + Λ ^ 2) ^ 2)⁻¹ := by
  rw [photonTail, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs' : 0 < s := hs
  simp only [zero_add]
  rw [vpPhotonT_eq hmγ hΛ hT hm hs'.le]
  have h1 : s + mγ ^ 2 ≠ 0 := by positivity
  have h2 : s + Λ ^ 2 ≠ 0 := by positivity
  have h3 : s + T * m ^ 2 ≠ 0 := by positivity
  field_simp

/-! ### The scalar limit and the cancellation above threshold -/

/-- **The scalar Källén–Lehmann limit** for every positive mass. -/
theorem isKKSclLim {m : ℝ} (hm : 0 < m) : IsKKSclLim m := by
  intro mγ Λ T hmγ hlt hT
  have hΛ : 0 < Λ := hmγ.trans hlt
  have hT0 : 0 < T := by linarith
  have hmT : 0 ≤ m ^ 2 * T := by positivity
  have hτ : 0 < √(m ^ 2 * T) / 2 := by
    have : 0 < √(m ^ 2 * T) := Real.sqrt_pos.2 (by positivity)
    positivity
  have h4 : 4 * (√(m ^ 2 * T) / 2) ^ 2 = T * m ^ 2 := by
    rw [div_pow, Real.sq_sqrt hmT]
    ring
  have h := tendsto_energyFirstIntegral_kkScl hτ hmγ hΛ
  rw [h4] at h
  convert h using 4
  have hab : Λ ^ 2 - mγ ^ 2 ≠ 0 := by
    have : mγ ^ 2 < Λ ^ 2 := by gcongr
    linarith
  rw [photonTail_vpPhotonT hm hmγ hΛ hT0, integral_Ioi_kkProd (by positivity) (by positivity)
    (by positivity)]
  field_simp
  ring

/-- **The Källén–Lehmann sum above threshold** for every positive electron mass. -/
theorem isKKSumGe (P₀ : Params) (hm : 0 < P₀.m) : IsKKSumGe P₀ :=
  isKKSumGe_of_sclLim P₀ hm (isKKSclLim hm)

/-- **The cancellation above threshold** for every positive electron mass and nonzero
charge. -/
theorem isKKCancelGe (P₀ : Params) (he : P₀.e ≠ 0) (hm : 0 < P₀.m) : IsKKCancelGe P₀ :=
  isKKCancelGe_of_sclLim P₀ he hm (isKKSclLim hm)

end QED.ChainProof.SetCRegDisp
