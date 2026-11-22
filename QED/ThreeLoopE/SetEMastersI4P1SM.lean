/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI4P1SGauge
public import QED.ThreeLoopE.SetEMastersI4P1FY4
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Set (e), master I₄: the photon parameter `m` in the electron-line gauge

The photon line `D₇` (parameter `m`, from A to E) is parallel to the external momentum, so both
Symanzik polynomials are linear in `m`: `U = U₁ m + U₂` and `F = (S U₁ - U₂) m + S U₂`, where
`S = a + b + c`, `U₁ = U(G - m) = (a + b + l)(b + c + n) - b²` and
`U₂ = U(G / m) = b (a + n)(c + l) + a n (c + l) + c l (a + n)` (`QED.ThreeLoopE.i4U_eq_m`,
`QED.ThreeLoopE.i4F_eq_m`). In the gauge `S = 1` of `QED.ThreeLoopE.SetEMastersI4P1SGauge`,
with `R = U₂ / U₁ < 1` the effective resistance of `G - m`,

  `∫_{m > 0} (4 log U - 3 log F) / U² dm = (4 + log U₂) / (U₁ U₂) + 3 (1 - R) log (1 - R) / U₂²`

(`QED.ThreeLoopE.i4SM_integral`): the `log U` part is `(1 + log U₂) / (U₁ U₂)`, and the
`log (F / U)` part is `QED.ThreeLoopE.i4P1FY4_integral` at `S = 1`. Fubini then gives `P'(0)` as a
four-dimensional integral over `(a, b, l, n)` (`QED.ThreeLoopE.i4P1_SM`).

## Main definitions

* `QED.ThreeLoopE.i4SU1`, `QED.ThreeLoopE.i4SU2`, `QED.ThreeLoopE.i4SMVal`,
  `QED.ThreeLoopE.i4SDom4`.

## Main results

* `QED.ThreeLoopE.i4U_eq_m`, `QED.ThreeLoopE.i4F_eq_m`, `QED.ThreeLoopE.i4SU_pos`.
* `QED.ThreeLoopE.i4SM_integral`.
* `QED.ThreeLoopE.i4P1_SM`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real

namespace QED.ThreeLoopE

/-- `U₁ = U(G - m)`, the first Symanzik polynomial without the line `D₇`. -/
def i4SU1 (a b c l n : ℝ) : ℝ := (a + b + l) * (b + c + n) - b ^ 2

/-- `U₂ = U(G / m)`, the first Symanzik polynomial with the line `D₇` contracted. -/
def i4SU2 (a b c l n : ℝ) : ℝ := b * (a + n) * (c + l) + a * n * (c + l) + c * l * (a + n)

theorem i4U_eq_m (a b c l m n : ℝ) :
    i4U a b c l m n = i4SU1 a b c l n * m + i4SU2 a b c l n := by
  unfold i4U i4SU1 i4SU2
  ring

theorem i4F_eq_m (a b c l m n : ℝ) :
    i4F a b c l m n = ((a + b + c) * i4SU1 a b c l n - i4SU2 a b c l n) * m +
      (a + b + c) * i4SU2 a b c l n := by
  unfold i4F i4SU1 i4SU2
  ring

/-- For positive parameters, `0 < U₂ < S U₁`. -/
theorem i4SU_pos {a b c l n : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hl : 0 < l)
    (hn : 0 < n) :
    0 < i4SU1 a b c l n ∧ 0 < i4SU2 a b c l n ∧
      i4SU2 a b c l n < (a + b + c) * i4SU1 a b c l n := by
  have e1 : i4SU1 a b c l n = a * b + a * c + a * n + b * c + b * l + b * n + c * l + l * n := by
    unfold i4SU1; ring
  have e3 : (a + b + c) * i4SU1 a b c l n - i4SU2 a b c l n =
      a ^ 2 * b + a ^ 2 * c + a ^ 2 * n + a * b ^ 2 + 2 * a * b * c + 2 * a * b * n + a * c ^ 2 +
        b ^ 2 * c + b ^ 2 * l + b ^ 2 * n + b * c ^ 2 + 2 * b * c * l + c ^ 2 * l := by
    unfold i4SU1 i4SU2; ring
  refine ⟨by rw [e1]; positivity, by unfold i4SU2; positivity, ?_⟩
  have : 0 < a ^ 2 * b + a ^ 2 * c + a ^ 2 * n + a * b ^ 2 + 2 * a * b * c + 2 * a * b * n +
      a * c ^ 2 + b ^ 2 * c + b ^ 2 * l + b ^ 2 * n + b * c ^ 2 + 2 * b * c * l + c ^ 2 * l := by
    positivity
  linarith

/-- The value of the `m`-integral of the log-weighted density, `K = U₁`, `Q = U₂`. -/
noncomputable def i4SMVal (K Q : ℝ) : ℝ :=
  (4 + log Q) / (K * Q) + 3 * (1 - Q / K) * log (1 - Q / K) / Q ^ 2

private theorem i4SM_logD {K Q : ℝ} (hK : 0 < K) (hQ : 0 < Q) :
    IntegrableOn (fun y => log (K * y + Q) / (K * y + Q) ^ 2) (Ioi 0) ∧
      ∫ y in Ioi 0, log (K * y + Q) / (K * y + Q) ^ 2 = (1 + log Q) / (K * Q) := by
  have hD : Tendsto (fun y : ℝ => K * y + Q) atTop atTop :=
    tendsto_atTop_add_const_right _ Q (tendsto_id.const_mul_atTop hK)
  have hD' (y : ℝ) : HasDerivAt (fun y => K * y + Q) K y := by
    simpa using ((hasDerivAt_id y).const_mul K).add_const Q
  -- `(1 + log D) / D → 0`
  have hlim : Tendsto (fun y : ℝ => (1 + log (K * y + Q)) / (K * (K * y + Q))) atTop (𝓝 0) := by
    have h1 := (tendsto_pow_log_div_mul_add_atTop K 0 1 hK.ne').comp hD
    have h2 := (hD.const_mul_atTop hK).inv_tendsto_atTop
    have h := h2.add h1
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with y hy
    have : 0 < K * y + Q := by positivity
    simp only [Function.comp_apply, pow_one, add_zero, Pi.inv_apply]
    field_simp
  set c₀ : ℝ := |log Q|
  have hint2 : IntegrableOn (fun y : ℝ => 1 / (K * y + Q) ^ 2) (Ioi 0) := by
    refine integrableOn_Ioi_deriv_of_nonneg (g := fun y => -(1 / (K * (K * y + Q))))
      (l := 0) ?_ (fun y hy => ?_) (fun y _ => by positivity) ?_
    · exact (by fun_prop : Continuous fun y : ℝ => K * y + Q).continuousAt.continuousWithinAt
        |>.const_mul K |>.inv₀ (by positivity) |>.const_mul 1 |>.neg
    · have hy' : 0 < K * y + Q := by have : (0 : ℝ) < y := hy; positivity
      have h2 : HasDerivAt (fun y => K * (K * y + Q)) (K * K) y := by
        simpa using (hD' y).const_mul K
      convert ((h2.inv (by positivity)).const_mul 1).neg using 1
      · funext y; simp [one_div]
      · field_simp
    · simpa [one_div] using ((hD.const_mul_atTop hK).inv_tendsto_atTop).neg
  -- `(log D + c₀) / D² ≥ 0` has the primitive `-(1 + log D + c₀) / (K D)`
  have hP (c : ℝ) {y : ℝ} (hy : 0 ≤ y) : HasDerivAt
      (fun y => -((1 + log (K * y + Q) + c) / (K * (K * y + Q))))
      ((log (K * y + Q) + c) / (K * y + Q) ^ 2) y := by
    have hpos : 0 < K * y + Q := by positivity
    have h := ((((hD' y).log hpos.ne').const_add 1).add_const c).div ((hD' y).const_mul K)
      (by positivity)
    convert h.neg using 1
    field_simp
    ring
  have hint1 : IntegrableOn (fun y => (log (K * y + Q) + c₀) / (K * y + Q) ^ 2) (Ioi 0) := by
    refine integrableOn_Ioi_deriv_of_nonneg (l := 0)
      (hP c₀ le_rfl).continuousAt.continuousWithinAt (fun y hy => hP c₀ (le_of_lt hy))
      (fun y hy => ?_) ?_
    · have hy0 : (0 : ℝ) < y := hy
      have : log Q ≤ log (K * y + Q) := log_le_log hQ (by nlinarith)
      have : 0 ≤ log (K * y + Q) + c₀ := by linarith [neg_abs_le (log Q)]
      positivity
    · have h := (hlim.add ((hD.const_mul_atTop hK).inv_tendsto_atTop.const_mul c₀)).neg
      simp only [mul_zero, add_zero, neg_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop 0] with y hy
      have : 0 < K * y + Q := by positivity
      simp only [Pi.inv_apply]
      field_simp
  have hint : IntegrableOn (fun y => log (K * y + Q) / (K * y + Q) ^ 2) (Ioi 0) := by
    refine (hint1.sub (hint2.const_mul c₀)).congr_fun (fun y _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    ring
  refine ⟨hint, ?_⟩
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun y =>
      -((1 + log (K * y + Q) + 0) / (K * (K * y + Q)))) (m := 0)
    (hP 0 le_rfl).continuousAt.continuousWithinAt (fun y hy => hP 0 (le_of_lt hy))
    (by simpa using hint) (by simpa using hlim.neg)
  simp only [add_zero, mul_zero, zero_add] at h
  rw [h]
  ring

/-- **The `m`-integral.** For `0 < Q < K`,
`∫_{m > 0} (4 log (K m + Q) - 3 log ((K - Q) m + Q)) / (K m + Q)² = i4SMVal K Q`, with the
integrand integrable. -/
theorem i4SM_integral {K Q : ℝ} (hK : 0 < K) (hQ : 0 < Q) (hQK : Q < K) :
    IntegrableOn (fun m => (4 * log (K * m + Q) - 3 * log ((K - Q) * m + Q)) /
        (K * m + Q) ^ 2) (Ioi 0) ∧
      ∫ m in Ioi 0, (4 * log (K * m + Q) - 3 * log ((K - Q) * m + Q)) / (K * m + Q) ^ 2 =
        i4SMVal K Q := by
  obtain ⟨hD, vD⟩ := i4SM_logD hK hQ
  obtain ⟨hN, vN⟩ := i4P1FY4_integral (S := 1) hK hQ (by linarith)
  simp only [one_mul] at hN vN
  have eq : EqOn (fun m => log (K * m + Q) / (K * m + Q) ^ 2 -
      3 * (log (((K - Q) * m + Q) / (K * m + Q)) / (K * m + Q) ^ 2))
      (fun m => (4 * log (K * m + Q) - 3 * log ((K - Q) * m + Q)) / (K * m + Q) ^ 2)
      (Ioi 0) := fun m hm => by
    have hm0 : (0 : ℝ) < m := hm
    have h1 : 0 < K * m + Q := by positivity
    have h2 : 0 < (K - Q) * m + Q := by have : 0 < K - Q := by linarith
                                        positivity
    simp only
    rw [log_div h2.ne' h1.ne']
    ring
  have hI := (hD.sub (hN.const_mul 3)).congr_fun eq measurableSet_Ioi
  refine ⟨hI, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi eq, integral_sub hD (hN.const_mul 3),
    integral_const_mul, vD, vN, i4SMVal, i4P1FY4Val]
  simp only [log_one, mul_zero, zero_sub]
  field_simp
  ring

/-! ### Fubini over `m` -/

/-- The four-dimensional domain `(a, b, l, n)` of the electron-line gauge after `m`. -/
def i4SDom4 : Set (ℝ × ℝ × ℝ × ℝ) :=
  {y | 0 < y.1 ∧ 0 < y.2.1 ∧ y.1 + y.2.1 < 1 ∧ 0 < y.2.2.1 ∧ 0 < y.2.2.2}

/-- The `m`-integrated density on `i4SDom4`. -/
noncomputable def i4SMDens (y : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  i4SMVal (i4SU1 y.1 y.2.1 (1 - y.1 - y.2.1) y.2.2.1 y.2.2.2)
    (i4SU2 y.1 y.2.1 (1 - y.1 - y.2.1) y.2.2.1 y.2.2.2)

private def sEquiv : I4Coords ≃ᵐ (ℝ × ℝ × ℝ × ℝ) × ℝ :=
  ((MeasurableEquiv.refl ℝ).prodCongr ((MeasurableEquiv.refl ℝ).prodCongr
    MeasurableEquiv.prodAssoc.symm)).trans
    (((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.prodAssoc.symm).trans
      MeasurableEquiv.prodAssoc.symm)

private theorem sEquiv_apply (x : I4Coords) :
    sEquiv x = ((x.1, x.2.1, x.2.2.1, x.2.2.2.1), x.2.2.2.2) := rfl

private theorem measurePreserving_sEquiv : MeasurePreserving sEquiv := by
  unfold sEquiv
  exact ((MeasurePreserving.symm _ volume_preserving_prodAssoc).comp
    ((MeasurePreserving.id volume).prod
      (MeasurePreserving.symm _ volume_preserving_prodAssoc))).comp
    ((MeasurePreserving.id volume).prod ((MeasurePreserving.id volume).prod
      (MeasurePreserving.symm _ volume_preserving_prodAssoc)))

private theorem preimage_sEquiv : sEquiv ⁻¹' (i4SDom4 ×ˢ Ioi 0) = i4SDom := by
  ext x
  simp only [mem_preimage, sEquiv_apply, mem_prod, i4SDom4, i4SDom, mem_ofPred_eq, mem_Ioi]
  tauto

private theorem measurableSet_i4SDom4 : MeasurableSet i4SDom4 := by
  unfold i4SDom4
  simp only [Set.ofPred_and]
  exact (measurableSet_lt measurable_const (by fun_prop)).inter
    ((measurableSet_lt measurable_const (by fun_prop)).inter
      ((measurableSet_lt (by fun_prop) measurable_const).inter
        ((measurableSet_lt measurable_const (by fun_prop)).inter
          (measurableSet_lt measurable_const (by fun_prop)))))

/-- On the domain, the slice of the log-weighted density at fixed `(a, b, l, n)`. -/
private theorem slice_eq (y : ℝ × ℝ × ℝ × ℝ) (m : ℝ) :
    i4SIntegrand i4LogForm (y.1, y.2.1, y.2.2.1, y.2.2.2, m) =
      (4 * log (i4SU1 y.1 y.2.1 (1 - y.1 - y.2.1) y.2.2.1 y.2.2.2 * m +
          i4SU2 y.1 y.2.1 (1 - y.1 - y.2.1) y.2.2.1 y.2.2.2) -
        3 * log ((i4SU1 y.1 y.2.1 (1 - y.1 - y.2.1) y.2.2.1 y.2.2.2 -
          i4SU2 y.1 y.2.1 (1 - y.1 - y.2.1) y.2.2.1 y.2.2.2) * m +
          i4SU2 y.1 y.2.1 (1 - y.1 - y.2.1) y.2.2.1 y.2.2.2)) /
      (i4SU1 y.1 y.2.1 (1 - y.1 - y.2.1) y.2.2.1 y.2.2.2 * m +
        i4SU2 y.1 y.2.1 (1 - y.1 - y.2.1) y.2.2.1 y.2.2.2) ^ 2 := by
  simp only [i4SIntegrand, i4LogForm, i4U_eq_m, i4F_eq_m,
    show y.1 + y.2.1 + (1 - y.1 - y.2.1) = 1 by ring, one_mul]

private theorem slice_integral {y : ℝ × ℝ × ℝ × ℝ} (hy : y ∈ i4SDom4) :
    ∫ m in Ioi 0, i4SIntegrand i4LogForm (y.1, y.2.1, y.2.2.1, y.2.2.2, m) = i4SMDens y := by
  obtain ⟨ha, hb, hab, hl, hn⟩ := hy
  have hc : 0 < 1 - y.1 - y.2.1 := by linarith
  obtain ⟨h1, h2, h3⟩ := i4SU_pos ha hb hc hl hn
  rw [show y.1 + y.2.1 + (1 - y.1 - y.2.1) = 1 by ring, one_mul] at h3
  rw [setIntegral_congr_fun measurableSet_Ioi fun m _ => slice_eq y m]
  exact (i4SM_integral h1 h2 h3).2

/-- **`P'(0)` after the `m`-integral**: an integral of `i4SMDens` over `i4SDom4`, with the
density integrable there. -/
theorem i4P1_SM :
    IntegrableOn i4SMDens i4SDom4 ∧
      iteratedDeriv 1 i4PInt 0 = ((∫ y in i4SDom4, i4SMDens y : ℝ) : ℂ) := by
  have hg : ∀ a b c l m n t : ℝ, 0 < a → 0 < b → 0 < c → 0 < l → 0 < m → 0 < n → 0 < t →
      i4LogForm (t * a) (t * b) (t * c) (t * l) (t * m) (t * n) =
        (t ^ 6)⁻¹ * i4LogForm a b c l m n :=
    fun a b c l m n t ha hb hc hl hm hn ht => i4LogForm_smul a b c l m n t ha hb hc hl hm hn ht
  have eS : (fun x => i4LogWeight x ^ 1 / i4SimplexU x ^ 2) = i4SimplexIntegrand i4LogForm :=
    funext fun x => (i4SimplexIntegrand_logForm x).symm
  have hI : IntegrableOn (i4SIntegrand i4LogForm) i4SDom := by
    rw [← i4SGauge_integrableOn_iff hg, ← eS]
    exact integrableOn_i4P1L
  set G : (ℝ × ℝ × ℝ × ℝ) × ℝ → ℝ := fun z =>
    i4SIntegrand i4LogForm (z.1.1, z.1.2.1, z.1.2.2.1, z.1.2.2.2, z.2) with hG
  have hGI : IntegrableOn G (i4SDom4 ×ˢ Ioi 0) := by
    rw [← measurePreserving_sEquiv.integrableOn_comp_preimage sEquiv.measurableEmbedding,
      preimage_sEquiv]
    exact hI
  have hInt : ∫ x in i4SDom, i4SIntegrand i4LogForm x = ∫ z in i4SDom4 ×ˢ Ioi 0, G z := by
    rw [← measurePreserving_sEquiv.setIntegral_preimage_emb sEquiv.measurableEmbedding G,
      preimage_sEquiv]
    rfl
  have hslice : EqOn (fun y => ∫ m in Ioi 0, G (y, m)) i4SMDens i4SDom4 :=
    fun y hy => slice_integral hy
  refine ⟨?_, ?_⟩
  · have h := hGI
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h
    exact (show IntegrableOn (fun y => ∫ m in Ioi 0, G (y, m)) i4SDom4 volume from
      h.integral_prod_left).congr_fun hslice measurableSet_i4SDom4
  · rw [iteratedDeriv_i4PInt (by norm_num), eS, i4SGauge_integral hg, hInt,
      Measure.volume_eq_prod, setIntegral_prod G (by rwa [← Measure.volume_eq_prod]),
      setIntegral_congr_fun measurableSet_i4SDom4 hslice]

end QED.ThreeLoopE

end
