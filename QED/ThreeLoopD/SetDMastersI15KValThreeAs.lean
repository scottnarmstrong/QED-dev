/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI15KValTwo
public import QED.ThreeLoopD.SetDMastersI15KValThreeA
public import QED.ThreeLoopD.SetDMastersI15KValThreeH
public import QED.ThreeLoopD.SetDMastersI15KValThreeWV
import QED.ThreeLoopD.SetDMastersI15KValThreeW0
import QED.Polylog.LiCalculus

/-!
# Set (d), master `I₁₅`: `∫∫ F₃` from its two halves

`F₃ = A₁,₃ + A₂₃,₃` (`QED.ThreeLoopD.i15F_eq_add`). For `0 < x < 1/2` and `r = x / (1 - x)`,
`A₁,₃(x, u) = (b₁³ - b₂³)(r, u) / (6 x (1 - x))` with `b₁, b₂` as in
`QED.ThreeLoopD.i15WuF`, so the `u`-slice of `A₁,₃` is `W₃(r) / (6 x (1 - x))`
(`QED.ThreeLoopD.integral_i15WuF_eq`). Its primitive in `x` is `Φ(x/(1 - x)) / 6`, with `Φ` the
primitive of `W₃ / r`. Since `A₁,₃ ≤ 0`, Tonelli gives its integrability and
`∫∫ A₁,₃ = (Φ(1) - Φ(0⁺)) / 3 = 14 π² + 56 ζ(3) - 16 π² log 2 - 100`, using the symmetry
`x ↦ 1 - x`. Then `A₂₃,₃` is integrable, and by Fubini `∫∫ A₂₃,₃ = ∫₀¹ h₃` once the `x`-slices
of `A₂₃,₃` are `h₃ = QED.ThreeLoopD.i15H3`; `∫₀¹ h₃ = 5 ζ(3) - 5π²/8 - 65/16`
(`QED.ThreeLoopD.integral_i15H3`).

## Main results

* `QED.ThreeLoopD.integral_i15A1k_three`: `∫∫ A₁,₃ = 14 π² + 56 ζ(3) - 16 π² log 2 - 100`.
* `QED.ThreeLoopD.integral_i15F_three_of_inner`: `∫∫ F₃` given the `x`-slices of `A₂₃,₃`.
* `QED.ThreeLoopD.hasTruncLaurent_i15K_of_inner_four`: the expansion of `K` given those slices
  and `∫∫ F₄`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

/-! ### The `u`-slices of `A₁,₃` -/

theorem i15A1k_three_eq {x u : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) (hu : u ∈ Ioo (0 : ℝ) 1) :
    i15A1k 3 (x, u) = i15WuF (x / (1 - x)) u / (6 * (x * (1 - x))) := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hu0, hu1⟩ := hu
  have hx1' : x ∈ Ioo (0 : ℝ) 1 := ⟨hx0, by linarith⟩
  have hm : 0 < 1 - x := by linarith
  set r := x / (1 - x) with hr
  have hr0 : 0 < r := div_pos hx0 hm
  have hpr : 1 + r = 1 / (1 - x) := by rw [hr]; field_simp; ring
  have lp : log (1 + r) = -log (1 - x) := by rw [hpr, one_div, log_inv]
  have lr : log r = log x - log (1 - x) := log_div hx0.ne' hm.ne'
  have hA : 0 < u + (1 - u) * x := by nlinarith
  have hB : 0 < 1 - (1 - u) * x := by nlinarith
  have la : i15WuA r u = log (u + (1 - u) * x) - log x := by
    unfold i15WuA
    rw [← log_div hA.ne' hx0.ne']
    congr 1
    rw [hr]; field_simp; ring
  have lb : i15WuB r u = log (1 - (1 - u) * x) - log (1 - x) := by
    unfold i15WuB
    rw [← log_div hB.ne' hm.ne']
    congr 1
    rw [hr]; field_simp; ring
  have e1 : i15B1 x u = -log r + log u + 2 * log (1 + r) - 2 * i15WuA r u - 2 * i15WuB r u := by
    rw [i15B1_eq hx1' ⟨hu0, hu1⟩, la, lb, lp, lr]; ring
  have e2 : i15B2 x u = log r - 2 * log (1 + r) - log u := by
    rw [i15B2_eq hx1', lp, lr]; ring
  unfold i15A1k i15WuF
  simp only [e1, e2, Nat.factorial]
  norm_num

theorem i15Q3_ratio_identity {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
    i15W3 (x / (1 - x)) / (6 * (x * (1 - x))) =
      i15W3 (x / (1 - x)) / (x / (1 - x)) / (6 * (1 - x) ^ 2) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  field_simp

/-- **The `u`-slice of `A₁,₃`** at `0 < x < 1/2`. -/
theorem integrableOn_and_integral_i15A1k_three_inner {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
    IntegrableOn (fun u => i15A1k 3 (x, u)) (Ioo 0 1) ∧
      ∫ u in Ioo (0 : ℝ) 1, i15A1k 3 (x, u) = i15W3 (x / (1 - x)) / (6 * (x * (1 - x))) := by
  obtain ⟨hI, hv⟩ := integral_i15WuF_eq (i15Q_ratio_mem hx)
  have hcongr : ∀ u ∈ Ioo (0 : ℝ) 1,
      i15A1k 3 (x, u) = i15WuF (x / (1 - x)) u / (6 * (x * (1 - x))) :=
    fun u hu => i15A1k_three_eq hx hu
  have hIo : IntegrableOn (i15WuF (x / (1 - x))) (Ioo 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hI
  refine ⟨IntegrableOn.congr_fun (hIo.div_const _) (fun u hu => (hcongr u hu).symm)
    measurableSet_Ioo, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioo hcongr, integral_div,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, hv]

/-! ### The primitive in `x` -/

/-- The `u`-slice of `A₁,₃` at `0 < x < 1/2`. -/
noncomputable def i15Q3G (x : ℝ) : ℝ := i15W3 (x / (1 - x)) / (6 * (x * (1 - x)))

/-- `Ψ₃(x) = Φ(x / (1 - x)) / 6`. -/
noncomputable def i15Q3Psi (x : ℝ) : ℝ := i15W3Phi (x / (1 - x)) / 6

theorem hasDerivAt_i15Q3Psi {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
    HasDerivAt i15Q3Psi (i15Q3G x) x := by
  have h1 : 0 < 1 - x := by linarith [hx.2]
  have hd : HasDerivAt (fun x => x / (1 - x)) ((1 * (1 - x) - x * (-1)) / (1 - x) ^ 2) x := by
    have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
      simpa using (hasDerivAt_id' x).const_sub 1
    exact (hasDerivAt_id' x).div h2 h1.ne'
  have h := ((hasDerivAt_i15W3Phi (i15Q_ratio_mem hx)).comp x hd).div_const 6
  convert h using 1
  · funext y; rfl
  unfold i15Q3G
  rw [i15Q3_ratio_identity hx]
  field_simp
  ring

theorem tendsto_i15Q3Psi_zero : Tendsto i15Q3Psi (𝓝[>] 0) (𝓝 50) := by
  have := (tendsto_i15W3Phi_zero.comp i15Q_tendsto_ratio_zero).div_const 6
  rw [show (300 : ℝ) / 6 = 50 by norm_num] at this
  exact this

theorem tendsto_i15Q3Psi_half : Tendsto i15Q3Psi (𝓝[<] (1 / 2))
    (𝓝 ((42 * π ^ 2 + 168 * zeta3 - 48 * π ^ 2 * log 2) / 6)) :=
  (tendsto_i15W3Phi_one.comp i15Q_tendsto_ratio_half).div_const 6

/-! ### The symmetry `x ↦ 1 - x` and the slices -/

theorem i15A1k_one_sub (k : ℕ) (x u : ℝ) : i15A1k k (1 - x, u) = i15A1k k (x, u) := by
  have hc : (1 - x) * (1 - (1 - x)) = x * (1 - x) := by ring
  have hP : i15P (1 - x) u = i15P x u := by unfold i15P i9Poly; ring
  unfold i15A1k i15B1 i15B2
  simp only [hc, hP]

/-- The slice integral `g₃(x) = ∫₀¹ A₁,₃(x, u) du`. -/
noncomputable def i15Q3g (x : ℝ) : ℝ := ∫ u in Ioo (0 : ℝ) 1, i15A1k 3 (x, u)

theorem i15Q3g_one_sub (x : ℝ) : i15Q3g (1 - x) = i15Q3g x := by
  unfold i15Q3g
  simp only [i15A1k_one_sub]

theorem i15Q3g_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) : i15Q3g x = i15Q3G x :=
  (integrableOn_and_integral_i15A1k_three_inner hx).2

theorem i15Q3G_nonpos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) : i15Q3G x ≤ 0 := by
  have hc : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
  unfold i15Q3G
  exact div_nonpos_of_nonpos_of_nonneg (i15W3_nonpos (i15Q_ratio_mem hx)) (by positivity)

theorem i15Q3g_left :
    IntervalIntegrable i15Q3g volume 0 (1 / 2) ∧
      ∫ x in (0 : ℝ)..(1 / 2), i15Q3g x =
        (42 * π ^ 2 + 168 * zeta3 - 48 * π ^ 2 * log 2) / 6 - 50 := by
  have h := intervalIntegrable_and_integral_eq_of_nonpos' (F := i15Q3Psi) (f := i15Q3g)
    (by norm_num) (fun x hx => by rw [i15Q3g_eq hx]; exact hasDerivAt_i15Q3Psi hx)
    (fun x hx => by rw [i15Q3g_eq hx]; exact i15Q3G_nonpos hx) tendsto_i15Q3Psi_zero
    tendsto_i15Q3Psi_half
  exact h

theorem i15Q3g_right :
    IntervalIntegrable i15Q3g volume (1 / 2) 1 ∧
      ∫ x in (1 / 2 : ℝ)..1, i15Q3g x =
        (42 * π ^ 2 + 168 * zeta3 - 48 * π ^ 2 * log 2) / 6 - 50 := by
  have hs : ∀ x ∈ Ioo (1 / 2 : ℝ) 1, 1 - x ∈ Ioo (0 : ℝ) (1 / 2) := fun x hx =>
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hd : ∀ x ∈ Ioo (1 / 2 : ℝ) 1, HasDerivAt (fun x => -i15Q3Psi (1 - x)) (i15Q3g x) x := by
    intro x hx
    have := ((hasDerivAt_i15Q3Psi (hs x hx)).comp x ((hasDerivAt_id' x).const_sub 1)).neg
    rw [← i15Q3g_one_sub, i15Q3g_eq (hs x hx)]
    convert this using 1
    · funext y; rfl
    · ring
  have h0 : Tendsto (fun x => -i15Q3Psi (1 - x)) (𝓝[>] (1 / 2))
      (𝓝 (-((42 * π ^ 2 + 168 * zeta3 - 48 * π ^ 2 * log 2) / 6))) := by
    refine (tendsto_i15Q3Psi_half.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)).neg
    · have := ((continuous_sub_left (1 : ℝ)).tendsto (1 / 2)).mono_left
        (nhdsWithin_le_nhds (s := Ioi (1 / 2)))
      convert this using 2; norm_num
    · filter_upwards [self_mem_nhdsWithin] with x (hx : 1 / 2 < x)
      show 1 - x < 1 / 2
      linarith
  have h1 : Tendsto (fun x => -i15Q3Psi (1 - x)) (𝓝[<] 1) (𝓝 (-50)) :=
    (tendsto_i15Q3Psi_zero.comp tendsto_one_sub_nhdsLT_one).neg
  have h := intervalIntegrable_and_integral_eq_of_nonpos' (F := fun x => -i15Q3Psi (1 - x))
    (f := i15Q3g) (by norm_num) hd
    (fun x hx => by rw [← i15Q3g_one_sub, i15Q3g_eq (hs x hx)]; exact i15Q3G_nonpos (hs x hx))
    h0 h1
  refine ⟨h.1, ?_⟩
  rw [h.2]
  ring

/-! ### Integrability and the value of `∫∫ A₁,₃` -/

theorem measurable_i15A1k (k : ℕ) : Measurable (i15A1k k) := by
  unfold i15A1k i15B1 i15B2 i15P i9Poly
  fun_prop

theorem integrableOn_i15A1k_three_slice {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hx2 : x ≠ 1 / 2) :
    IntegrableOn (fun u => i15A1k 3 (x, u)) (Ioo 0 1) := by
  rcases lt_or_gt_of_ne hx2 with h | h
  · exact (integrableOn_and_integral_i15A1k_three_inner ⟨hx.1, h⟩).1
  · have := (integrableOn_and_integral_i15A1k_three_inner (x := 1 - x)
      ⟨by linarith [hx.2], by linarith⟩).1
    simpa only [i15A1k_one_sub] using this

theorem integrable_i15A1k_three :
    IntegrableOn (i15A1k 3) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  rw [IntegrableOn, volume_restrict_prod2,
    integrable_prod_iff (measurable_i15A1k 3).aestronglyMeasurable]
  have hne : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), x ∈ ({1 / 2} : Set ℝ)ᶜ :=
    ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton _))
  have hgI : IntegrableOn i15Q3g (Ioo 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (i15Q3g_left.1.trans i15Q3g_right.1)
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioo, hne] with x hx hx2
    exact integrableOn_i15A1k_three_slice hx hx2
  · refine hgI.neg.congr_fun (fun x hx => ?_) measurableSet_Ioo
    unfold i15Q3g
    rw [Pi.neg_apply, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    rw [Real.norm_eq_abs, abs_of_nonpos (i15A1k_three_nonpos (z := (x, u)) ⟨hx, hu⟩)]

/-- **`∫∫ A₁,₃ = 14 π² + 56 ζ(3) - 16 π² log 2 - 100`.** -/
theorem integral_i15A1k_three :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15A1k 3 z =
      14 * π ^ 2 + 56 * zeta3 - 16 * π ^ 2 * log 2 - 100 := by
  have hF : Integrable (i15A1k 3) ((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1))) := by
    rw [← volume_restrict_prod2]; exact integrable_i15A1k_three
  rw [volume_restrict_prod2, integral_prod _ hF]
  change ∫ x in Ioo (0 : ℝ) 1, i15Q3g x = _
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_add_adjacent_intervals i15Q3g_left.1 i15Q3g_right.1,
    i15Q3g_left.2, i15Q3g_right.2]
  ring

/-! ### `∫∫ A₂₃,₃` and `∫∫ F₃` -/

/-- **`∫∫ A₂₃,₃ = ∫₀¹ h₃`**, given that the integrable `x`-slices of `A₂₃,₃` are `h₃`. -/
theorem integral_i15A23k_three_of_inner
    (hH : ∀ u ∈ Ioo (0 : ℝ) 1, IntegrableOn (fun x => i15A23k 3 (x, u)) (Ioo 0 1) →
      ∫ x in Ioo (0 : ℝ) 1, i15A23k 3 (x, u) = i15H3 u)
    (hA : IntegrableOn (i15A23k 3) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15A23k 3 z =
      5 * zeta3 - 5 * π ^ 2 / 8 - 65 / 16 := by
  have hF : Integrable (i15A23k 3) ((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1))) := by
    rw [← volume_restrict_prod2]; exact hA
  rw [volume_restrict_prod2, integral_prod_symm _ hF]
  have hae : (fun u => ∫ x, i15A23k 3 (x, u) ∂volume.restrict (Ioo (0 : ℝ) 1)) =ᵐ[volume.restrict
      (Ioo (0 : ℝ) 1)] i15H3 := by
    filter_upwards [hF.prod_left_ae, ae_restrict_mem measurableSet_Ioo] with u hu1 hu2
    exact hH u hu2 hu1
  rw [integral_congr_ae hae, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one]
  refine integral_i15H3 ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr ?_)
  exact hF.integral_prod_right.congr hae

/-- **`∫∫ F₃ = -16 π² log 2 + 107 π²/8 + 61 ζ(3) - 1665/16`**, given the `x`-slices of
`A₂₃,₃`. -/
theorem integral_i15F_three_of_inner
    (hH : ∀ u ∈ Ioo (0 : ℝ) 1, IntegrableOn (fun x => i15A23k 3 (x, u)) (Ioo 0 1) →
      ∫ x in Ioo (0 : ℝ) 1, i15A23k 3 (x, u) = i15H3 u) :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15F 3 z =
      -16 * π ^ 2 * log 2 + 107 / 8 * π ^ 2 + 61 * zeta3 - 1665 / 16 := by
  obtain ⟨h23, hsum⟩ := integral_i15F_eq_add (k := 3) (by norm_num) integrable_i15A1k_three
  rw [hsum, integral_i15A1k_three, integral_i15A23k_three_of_inner hH h23]
  ring

/-- **The target expansion of `K`** from the `x`-slices of `A₂₃,₃` and `∫∫ F₄`. -/
theorem hasTruncLaurent_i15K_of_inner_four
    (hH : ∀ u ∈ Ioo (0 : ℝ) 1, IntegrableOn (fun x => i15A23k 3 (x, u)) (Ioo 0 1) →
      ∫ x in Ioo (0 : ℝ) 1, i15A23k 3 (x, u) = i15H3 u)
    (h4 : ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15F 4 z =
      384 * QED.Polylog.Li 4 (1 / 2) + 16 * Real.log 2 ^ 4
        + 32 * Real.pi ^ 2 * Real.log 2 ^ 2 - 72 * Real.pi ^ 2 * Real.log 2
        - 253 / 80 * Real.pi ^ 4 - 2 / 3 * Real.pi ^ 2 * QED.Polylog.zeta3
        + 2267 / 48 * Real.pi ^ 2 + 503 / 2 * QED.Polylog.zeta3 + 12 * QED.Polylog.zeta5
        - 10403 / 32) :
    HasTruncLaurent i15K i15KLaurent 5 :=
  hasTruncLaurent_i15K_of_coeffs_three (integral_i15F_three_of_inner hH) h4

end QED.ThreeLoopD
