/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RHighSMel

/-!
# Set (d), master `I₁₂`: the good part of the bulk remainder in closed form

With the sectors merged (`QED.ThreeLoopD.SetDMastersI12RHighSCov`), the main term of the bulk
part `S` of the remainder of `I₁₂` at `(x, s, u)` is, by the homogeneity of `Φ₀`,
`x ^ (ε - 1) s ^ (2ε - 1) w(u) h ^ (-ε - 1) (1 - xs) ^ (-ε) φ(s k / h)`, with `h = h(x)`,
`k = u / (1 - u)`, `w(u) = u ^ ε (1 - u) ^ (-2ε)` and `φ = Φ₀(·, 1)`. The *good part*
(`QED.ThreeLoopD.i12HSGood`) drops the factor `(1 - xs) ^ (-ε)`, extends `s` to `(0, ∞)`,
subtracts the faces `s → 0`, `s → ∞` (`QED.ThreeLoopD.i12HSD`) and the face `x = 0`:

  `Good = x ^ (ε - 1) s ^ (2ε - 1) w(u) [h ^ (-ε - 1) D(s, k/h) - h₀ ^ (-ε - 1) D(s, k/h₀)]`.

For `0 < re ε < 1/3`, integrating `s` (the subtracted Mellin integral
`QED.ThreeLoopD.i12HS_psi`), then `u` (Beta integrals), then `x`:

  `∫ Good = M_φ P(ε - 1, ε) / (1 - ε) - a B_w / (2ε) P(-ε - 1, ε) - a B_w / ε P(2ε - 1, ε)`,

with `a = 2 - 3ε`, `M_φ` the Mellin transform of `φ` (`QED.ThreeLoopD.i12HSMphi`),
`B_w = Γ(1 + ε) Γ(1 - 2ε) / Γ(2 - ε)` and `P(α, ε) = ∫₀¹ x ^ (ε - 1) (h(x) ^ α - h(0) ^ α) dx`.
Here the absolute convergence of the triple integral is a hypothesis (it is the domination of the
good part, which also gives its analyticity near `ε = 0`).

## Main results

* `QED.ThreeLoopD.i12HSGood_fibre`: the `s`-integral at fixed `(x, u)`.
* `QED.ThreeLoopD.i12HS_integral_u`: the `u`-integral `∫₀¹ w(u) Ψ(ε, k/H) du`.
* `QED.ThreeLoopD.i12HSGood_slice`: the `(s, u)`-integral at fixed `x`.
* `QED.ThreeLoopD.i12HS_integral_good`: the closed form of `∫ Good`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.ThreeLoopD

/-- The ratio `k = u / (1 - u)`. -/
noncomputable def i12HSk (u : ℝ) : ℝ := u / (1 - u)

/-- The weight `w(u) = u ^ ε (1 - u) ^ (-2ε)`. -/
noncomputable def i12HSw (ε : ℂ) (u : ℝ) : ℂ := (u : ℂ) ^ ε * ((1 - u : ℝ) : ℂ) ^ (-2 * ε)

/-- **The good part of the bulk remainder** (`e`-exact integrand on
`(x, s, u) ∈ (0, 1) × (0, ∞) × (0, 1)`):
`x ^ (ε - 1) s ^ (2ε - 1) w(u) [h ^ (-ε - 1) D(s, k/h) - h₀ ^ (-ε - 1) D(s, k/h₀)]`,
`h = h(x)`, `h₀ = h(0)`, `D = QED.ThreeLoopD.i12HSD`. -/
noncomputable def i12HSGood (ε : ℂ) (x s u : ℝ) : ℂ :=
  (x : ℂ) ^ (ε - 1) * (s : ℂ) ^ (2 * ε - 1) * i12HSw ε u *
    (((i12H x : ℝ) : ℂ) ^ (-ε - 1) * i12HSD ε s (i12HSk u / i12H x) -
      ((i12H 0 : ℝ) : ℂ) ^ (-ε - 1) * i12HSD ε s (i12HSk u / i12H 0))

/-- `B_w = Γ(1 + ε) Γ(1 - 2ε) / Γ(2 - ε) = ∫₀¹ w`. -/
noncomputable def i12HSBw (ε : ℂ) : ℂ := Gamma (1 + ε) * Gamma (1 - 2 * ε) / Gamma (2 - ε)

/-- `P(α, ε) = ∫₀¹ x ^ (ε - 1) (h(x) ^ α - h(0) ^ α) dx`. -/
noncomputable def i12HSP (α ε : ℂ) : ℂ :=
  ∫ x in Ioo (0 : ℝ) 1, (x : ℂ) ^ (ε - 1) * (((i12H x : ℝ) : ℂ) ^ α - ((i12H 0 : ℝ) : ℂ) ^ α)

theorem i12HS_h_pos {x : ℝ} (hx : x < 2) : 0 < i12H x := by unfold i12H; linarith

/-- **The fibre in `s`**: for `x ∈ (0, 2)`, `u ∈ (0, 1)`, `0 < re ε < 1/3`,
`∫₀^∞ Good ds = x ^ (ε - 1) w(u) (h ^ (-ε - 1) Ψ(ε, k/h) - h₀ ^ (-ε - 1) Ψ(ε, k/h₀))`. -/
theorem i12HSGood_fibre {ε : ℂ} (h0 : 0 < ε.re) (h1 : ε.re < 1 / 3) {x u : ℝ} (hx : x < 2)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun s => i12HSGood ε x s u) (Ioi 0) ∧
      ∫ s in Ioi (0 : ℝ), i12HSGood ε x s u =
        (x : ℂ) ^ (ε - 1) * i12HSw ε u *
          (((i12H x : ℝ) : ℂ) ^ (-ε - 1) * i12HSPsi ε (i12HSk u / i12H x) -
            ((i12H 0 : ℝ) : ℂ) ^ (-ε - 1) * i12HSPsi ε (i12HSk u / i12H 0)) := by
  have hk : 0 < i12HSk u := div_pos hu.1 (by linarith [hu.2])
  obtain ⟨iA, vA⟩ := i12HS_psi h0 h1 (div_pos hk (i12HS_h_pos hx))
  obtain ⟨iB, vB⟩ := i12HS_psi h0 h1 (div_pos hk (i12HS_h_pos (x := 0) (by norm_num)))
  set cA := (x : ℂ) ^ (ε - 1) * i12HSw ε u * ((i12H x : ℝ) : ℂ) ^ (-ε - 1)
  set cB := (x : ℂ) ^ (ε - 1) * i12HSw ε u * ((i12H 0 : ℝ) : ℂ) ^ (-ε - 1)
  have e : (fun s => i12HSGood ε x s u) = fun s : ℝ =>
      cA * ((s : ℂ) ^ (2 * ε - 1) * i12HSD ε s (i12HSk u / i12H x)) -
        cB * ((s : ℂ) ^ (2 * ε - 1) * i12HSD ε s (i12HSk u / i12H 0)) := by
    funext s
    simp only [i12HSGood, cA, cB]
    ring
  rw [e]
  refine ⟨(iA.const_mul cA).sub (iB.const_mul cB), ?_⟩
  rw [integral_sub (iA.const_mul cA) (iB.const_mul cB), integral_const_mul, integral_const_mul,
    vA, vB]
  simp only [cA, cB]
  ring

/-- `∫₀¹ u ^ p (1 - u) ^ q du = Γ(p + 1) Γ(q + 1) / Γ(p + q + 2)` for `re p, re q > -1`. -/
theorem i12HS_beta_unit {p q : ℂ} (hp : -1 < p.re) (hq : -1 < q.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ p * ((1 - u : ℝ) : ℂ) ^ q) (Ioo 0 1) ∧
      ∫ u in Ioo (0 : ℝ) 1, (u : ℂ) ^ p * ((1 - u : ℝ) : ℂ) ^ q =
        Gamma (p + 1) * Gamma (q + 1) / Gamma (p + 1 + (q + 1)) := by
  have hp' : 0 < (p + 1).re := by simp; linarith
  have hq' : 0 < (q + 1).re := by simp; linarith
  have hB := betaIntegral_convergent hp' hq'
  simp only [add_sub_cancel_right] at hB
  have e : (fun u : ℝ => (u : ℂ) ^ p * ((1 - u : ℝ) : ℂ) ^ q) =
      fun u : ℝ => (u : ℂ) ^ p * (1 - (u : ℂ)) ^ q := by
    funext u; push_cast; rfl
  rw [e]
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hB
    |>.mono_set Ioo_subset_Ioc_self, ?_⟩
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← betaIntegral_eq_Gamma_mul_div _ _ hp' hq', betaIntegral]
  simp only [add_sub_cancel_right]

/-- `(k / H) ^ c = u ^ c (1 - u) ^ (-c) H ^ (-c)` for `u ∈ (0, 1)`, `H > 0`. -/
theorem i12HS_k_div_cpow {u H : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hH : 0 < H) (c : ℂ) :
    ((i12HSk u / H : ℝ) : ℂ) ^ c =
      (u : ℂ) ^ c * ((1 - u : ℝ) : ℂ) ^ (-c) * (H : ℂ) ^ (-c) := by
  have h1 : 0 < 1 - u := by linarith [hu.2]
  rw [show i12HSk u / H = u * ((1 - u) * H)⁻¹ by simp only [i12HSk]; field_simp,
    DimReg.ofReal_mul_inv_cpow hu.1.le (by positivity),
    DimReg.cpow_ofReal_mul h1.le hH.le]
  ring

/-- **The `u`-integral**: for `H > 0`, `0 < re ε < 1/3`,
`∫₀¹ w(u) Ψ(ε, k/H) du = H ^ (2ε) M_φ / (1 - ε) - a B_w / (2ε) - a H ^ (3ε) B_w / ε`. -/
theorem i12HS_integral_u {ε : ℂ} (h0 : 0 < ε.re) (h1 : ε.re < 1 / 3) {H : ℝ} (hH : 0 < H) :
    IntegrableOn (fun u => i12HSw ε u * i12HSPsi ε (i12HSk u / H)) (Ioo 0 1) ∧
      ∫ u in Ioo (0 : ℝ) 1, i12HSw ε u * i12HSPsi ε (i12HSk u / H) =
        (H : ℂ) ^ (2 * ε) * i12HSMphi ε / (1 - ε) - (2 - 3 * ε) * i12HSBw ε / (2 * ε) -
          (2 - 3 * ε) * (H : ℂ) ^ (3 * ε) * i12HSBw ε / ε := by
  set M := i12HSMphi ε
  set a := 2 - 3 * ε
  have hpt : ∀ u ∈ Ioo (0 : ℝ) 1, i12HSw ε u * i12HSPsi ε (i12HSk u / H) =
      (H : ℂ) ^ (2 * ε) * M * (u : ℂ) ^ (-ε) -
        a / (2 * ε) * ((u : ℂ) ^ ε * ((1 - u : ℝ) : ℂ) ^ (-2 * ε)) -
        a * (H : ℂ) ^ (3 * ε) / ε * ((u : ℂ) ^ (-2 * ε) * ((1 - u : ℝ) : ℂ) ^ ε) := by
    intro u hu
    have hU : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.1.ne'
    have hV : ((1 - u : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith [hu.2])
    set U := (u : ℂ)
    set V := ((1 - u : ℝ) : ℂ)
    simp only [i12HSw, i12HSPsi, i12HS_k_div_cpow hu hH]
    have e1 : U ^ ε * U ^ (-2 * ε) = U ^ (-ε) := by
      rw [← cpow_add _ _ hU]; ring_nf
    have e2 : V ^ (-2 * ε) * V ^ (2 * ε) = 1 := by
      rw [← cpow_add _ _ hV, show -2 * ε + 2 * ε = 0 by ring, cpow_zero]
    have e3 : U ^ ε * U ^ (-3 * ε) = U ^ (-2 * ε) := by
      rw [← cpow_add _ _ hU]; ring_nf
    have e4 : V ^ (-2 * ε) * V ^ (3 * ε) = V ^ ε := by
      rw [← cpow_add _ _ hV]; ring_nf
    rw [show -(-2 * ε) = 2 * ε by ring, show -(-3 * ε) = 3 * ε by ring]
    linear_combination ((H : ℂ) ^ (2 * ε) * M) *
        (V ^ (-2 * ε) * V ^ (2 * ε) * e1 + U ^ (-ε) * e2) -
      (a * (H : ℂ) ^ (3 * ε) / ε) * (V ^ (-2 * ε) * V ^ (3 * ε) * e3 + U ^ (-2 * ε) * e4)
  obtain ⟨i1, v1⟩ := i12HS_cpow_unit (r := -ε) (by simp; linarith)
  obtain ⟨i2, v2⟩ := i12HS_beta_unit (p := ε) (q := -2 * ε) (by linarith)
    (by simp; linarith)
  obtain ⟨i3, v3⟩ := i12HS_beta_unit (p := -2 * ε) (q := ε) (by simp; linarith)
    (by linarith)
  have j1 : IntegrableOn (fun u : ℝ => (H : ℂ) ^ (2 * ε) * M * (u : ℂ) ^ (-ε)) (Ioo 0 1) :=
    i1.const_mul _
  have j2 : IntegrableOn (fun u : ℝ =>
      a / (2 * ε) * ((u : ℂ) ^ ε * ((1 - u : ℝ) : ℂ) ^ (-2 * ε))) (Ioo 0 1) := i2.const_mul _
  have j3 : IntegrableOn (fun u : ℝ =>
      a * (H : ℂ) ^ (3 * ε) / ε * ((u : ℂ) ^ (-2 * ε) * ((1 - u : ℝ) : ℂ) ^ ε)) (Ioo 0 1) :=
    i3.const_mul _
  have j12 : IntegrableOn (fun u : ℝ => (H : ℂ) ^ (2 * ε) * M * (u : ℂ) ^ (-ε) -
      a / (2 * ε) * ((u : ℂ) ^ ε * ((1 - u : ℝ) : ℂ) ^ (-2 * ε))) (Ioo 0 1) := j1.sub j2
  have hI : IntegrableOn (fun u : ℝ => (H : ℂ) ^ (2 * ε) * M * (u : ℂ) ^ (-ε) -
      a / (2 * ε) * ((u : ℂ) ^ ε * ((1 - u : ℝ) : ℂ) ^ (-2 * ε)) -
      a * (H : ℂ) ^ (3 * ε) / ε * ((u : ℂ) ^ (-2 * ε) * ((1 - u : ℝ) : ℂ) ^ ε)) (Ioo 0 1) :=
    j12.sub j3
  refine ⟨hI.congr_fun (fun u hu => (hpt u hu).symm) measurableSet_Ioo, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_sub j12 j3, integral_sub j1 j2,
    integral_const_mul, integral_const_mul, integral_const_mul, v1, v2, v3, i12HSBw]
  have hε : ε ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have h1e : (1 - ε) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  rw [show -ε + 1 = 1 - ε by ring, show ε + 1 + (-2 * ε + 1) = 2 - ε by ring,
    show -2 * ε + 1 + (ε + 1) = 2 - ε by ring, show -2 * ε + 1 = 1 - 2 * ε by ring,
    add_comm ε 1]
  field_simp

/-- The integrand of `P(α, ε)` is integrable on `(0, 1)` for `re ε > 0`. -/
theorem i12HS_integrableOn_P (α : ℂ) {ε : ℂ} (h0 : 0 < ε.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (ε - 1) *
      (((i12H x : ℝ) : ℂ) ^ α - ((i12H 0 : ℝ) : ℂ) ^ α)) (Ioo 0 1) := by
  have hi := intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := 1) (r := ε - 1)
    (by simp; linarith)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one,
    ← integrableOn_Icc_iff_integrableOn_Ioc] at hi
  have he : (fun x : ℝ => ((i12H x : ℝ) : ℂ) ^ α) =
      fun x : ℝ => ((1 / 2 + (-1 / 4) * x : ℝ) : ℂ) ^ α := by
    funext x; congr 2; unfold i12H; ring
  have hc : ContinuousOn (fun x : ℝ => ((i12H x : ℝ) : ℂ) ^ α - ((i12H 0 : ℝ) : ℂ) ^ α)
      (Icc 0 1) := by
    refine ContinuousOn.sub ?_ continuousOn_const
    rw [he]
    exact fun x hx => (i12HS_hasDerivAt_cpow_affine (1 / 2) (-1 / 4) α
      (by linarith [hx.2])).continuousAt.continuousWithinAt
  exact (hi.mul_continuousOn hc isCompact_Icc).mono_set Ioo_subset_Icc_self

/-- **The `(s, u)`-slice of the good part**: for `x ∈ (0, 1)` with the slice integrable,
`∫ Good(x, ·, ·) = x ^ (ε - 1) [M_φ/(1 - ε) (h ^ (ε - 1) - h₀ ^ (ε - 1))
  - a B_w/(2ε) (h ^ (-ε - 1) - h₀ ^ (-ε - 1)) - a B_w/ε (h ^ (2ε - 1) - h₀ ^ (2ε - 1))]`. -/
theorem i12HSGood_slice {ε : ℂ} (h0 : 0 < ε.re) (h1 : ε.re < 1 / 3) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hI : IntegrableOn (fun y : ℝ × ℝ => i12HSGood ε x y.1 y.2) (Ioi 0 ×ˢ Ioo 0 1)) :
    ∫ y in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1, i12HSGood ε x y.1 y.2 =
      i12HSMphi ε / (1 - ε) * ((x : ℂ) ^ (ε - 1) *
          (((i12H x : ℝ) : ℂ) ^ (ε - 1) - ((i12H 0 : ℝ) : ℂ) ^ (ε - 1))) -
        (2 - 3 * ε) * i12HSBw ε / (2 * ε) * ((x : ℂ) ^ (ε - 1) *
          (((i12H x : ℝ) : ℂ) ^ (-ε - 1) - ((i12H 0 : ℝ) : ℂ) ^ (-ε - 1))) -
        (2 - 3 * ε) * i12HSBw ε / ε * ((x : ℂ) ^ (ε - 1) *
          (((i12H x : ℝ) : ℂ) ^ (2 * ε - 1) - ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1))) := by
  have hHx : 0 < i12H x := i12HS_h_pos (by linarith [hx.2])
  have hH0 : 0 < i12H 0 := i12HS_h_pos (by norm_num)
  unfold IntegrableOn at hI
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hI
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm _ hI]
  obtain ⟨iA, vA⟩ := i12HS_integral_u h0 h1 hHx
  obtain ⟨iB, vB⟩ := i12HS_integral_u h0 h1 hH0
  set X := (x : ℂ) ^ (ε - 1)
  set A := ((i12H x : ℝ) : ℂ)
  set B := ((i12H 0 : ℝ) : ℂ)
  have hfib : ∀ u ∈ Ioo (0 : ℝ) 1, ∫ s in Ioi (0 : ℝ), i12HSGood ε x s u =
      X * A ^ (-ε - 1) * (i12HSw ε u * i12HSPsi ε (i12HSk u / i12H x)) -
        X * B ^ (-ε - 1) * (i12HSw ε u * i12HSPsi ε (i12HSk u / i12H 0)) := by
    intro u hu
    rw [(i12HSGood_fibre h0 h1 (by linarith [hx.2]) hu).2]
    ring
  have jA : IntegrableOn (fun u => X * A ^ (-ε - 1) *
      (i12HSw ε u * i12HSPsi ε (i12HSk u / i12H x))) (Ioo 0 1) := iA.const_mul _
  have jB : IntegrableOn (fun u => X * B ^ (-ε - 1) *
      (i12HSw ε u * i12HSPsi ε (i12HSk u / i12H 0))) (Ioo 0 1) := iB.const_mul _
  rw [setIntegral_congr_fun measurableSet_Ioo hfib, integral_sub jA jB, integral_const_mul,
    integral_const_mul, vA, vB]
  have hA : A ≠ 0 := ofReal_ne_zero.mpr hHx.ne'
  have hB : B ≠ 0 := ofReal_ne_zero.mpr hH0.ne'
  have eA1 : A ^ (-ε - 1) * A ^ (2 * ε) = A ^ (ε - 1) := by rw [← cpow_add _ _ hA]; ring_nf
  have eA2 : A ^ (-ε - 1) * A ^ (3 * ε) = A ^ (2 * ε - 1) := by rw [← cpow_add _ _ hA]; ring_nf
  have eB1 : B ^ (-ε - 1) * B ^ (2 * ε) = B ^ (ε - 1) := by rw [← cpow_add _ _ hB]; ring_nf
  have eB2 : B ^ (-ε - 1) * B ^ (3 * ε) = B ^ (2 * ε - 1) := by rw [← cpow_add _ _ hB]; ring_nf
  linear_combination (X * i12HSMphi ε / (1 - ε)) * (eA1 - eB1) -
    (X * (2 - 3 * ε) * i12HSBw ε / ε) * (eA2 - eB2)

/-- **The good part in closed form** (`0 < re ε < 1/3`, given the absolute convergence of the
triple integral): `∫ Good = M_φ P(ε - 1, ε)/(1 - ε) - (a B_w/ε) [P(2ε - 1, ε) + P(-ε - 1, ε)/2]`
(written with `a B_w/(2ε)` and `a B_w/ε` separately). -/
theorem i12HS_integral_good {ε : ℂ} (h0 : 0 < ε.re) (h1 : ε.re < 1 / 3)
    (hG : IntegrableOn (fun z : ℝ × ℝ × ℝ => i12HSGood ε z.1 z.2.1 z.2.2)
      (Ioo 0 1 ×ˢ (Ioi 0 ×ˢ Ioo 0 1))) :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1), i12HSGood ε z.1 z.2.1 z.2.2 =
      i12HSMphi ε / (1 - ε) * i12HSP (ε - 1) ε -
        (2 - 3 * ε) * i12HSBw ε / (2 * ε) * i12HSP (-ε - 1) ε -
        (2 - 3 * ε) * i12HSBw ε / ε * i12HSP (2 * ε - 1) ε := by
  rw [Measure.volume_eq_prod] at hG ⊢
  rw [setIntegral_prod _ hG]
  have hG' := hG
  unfold IntegrableOn at hG'
  rw [← Measure.prod_restrict] at hG'
  have hae := hG'.prod_right_ae
  have j1 := (i12HS_integrableOn_P (ε - 1) h0).const_mul (i12HSMphi ε / (1 - ε))
  have j2 := (i12HS_integrableOn_P (-ε - 1) h0).const_mul
    ((2 - 3 * ε) * i12HSBw ε / (2 * ε))
  have j3 := (i12HS_integrableOn_P (2 * ε - 1) h0).const_mul
    ((2 - 3 * ε) * i12HSBw ε / ε)
  rw [integral_congr_ae (g := fun x : ℝ => i12HSMphi ε / (1 - ε) * ((x : ℂ) ^ (ε - 1) *
          (((i12H x : ℝ) : ℂ) ^ (ε - 1) - ((i12H 0 : ℝ) : ℂ) ^ (ε - 1))) -
        (2 - 3 * ε) * i12HSBw ε / (2 * ε) * ((x : ℂ) ^ (ε - 1) *
          (((i12H x : ℝ) : ℂ) ^ (-ε - 1) - ((i12H 0 : ℝ) : ℂ) ^ (-ε - 1))) -
        (2 - 3 * ε) * i12HSBw ε / ε * ((x : ℂ) ^ (ε - 1) *
          (((i12H x : ℝ) : ℂ) ^ (2 * ε - 1) - ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1))))]
  · have j12 : IntegrableOn (fun x : ℝ => i12HSMphi ε / (1 - ε) * ((x : ℂ) ^ (ε - 1) *
          (((i12H x : ℝ) : ℂ) ^ (ε - 1) - ((i12H 0 : ℝ) : ℂ) ^ (ε - 1))) -
        (2 - 3 * ε) * i12HSBw ε / (2 * ε) * ((x : ℂ) ^ (ε - 1) *
          (((i12H x : ℝ) : ℂ) ^ (-ε - 1) - ((i12H 0 : ℝ) : ℂ) ^ (-ε - 1)))) (Ioo 0 1) :=
      j1.sub j2
    rw [integral_sub j12 j3, integral_sub j1 j2, integral_const_mul, integral_const_mul,
      integral_const_mul, i12HSP, i12HSP, i12HSP]
  · filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with x hx hxm
    exact i12HSGood_slice h0 h1 hxm hx

end QED.ThreeLoopD
