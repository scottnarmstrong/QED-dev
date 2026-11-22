/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI15KValFourH
public import QED.ThreeLoopD.SetDMastersI15KValFourW
public import QED.ThreeLoopD.SetDMastersI15KValThreeHxVal

/-!
# Set (d), master `I₁₅`: the fourth Taylor coefficient of `K`, from its inner integrals

With `F₄ = A₁,₄ + A₂₃,₄` (`QED.ThreeLoopD.i15F_eq_add`), this file reduces
`∫∫ F₄` (the hypothesis `h4` of `QED.ThreeLoopD.hasTruncLaurent_i15K_of_coeffs_three`) to the two
inner identities

* `∫₀¹ A₁,₄(x, u) du = W₄(r) / (24 x (1 - x))`, `r = x / (1 - x)`, for `0 < x < 1/2`, with the
  integrability of the slice (`W₄ = QED.ThreeLoopD.i15W4`);
* `∫₀¹ A₂₃,₄(x, u) dx = h₄(u)` for `0 < u < 1`, given the integrability of the slice
  (`h₄ = QED.ThreeLoopD.i15H4`),

which hold numerically to about `500` digits (`setDI15i/fit4.py`) but are not proved here. Granting
them, everything else is proved: `A₁,₄ ≥ 0` is integrable by Tonelli (the outer primitive
`Ψ(x) = Φ(x / (1 - x)) / 24` of `QED.ThreeLoopD.SetDMastersI15KValFourW` and the symmetry
`x ↦ 1 - x`), with `∫∫ A₁,₄ = 384 Li₄(1/2) + 16 log⁴ 2 + 32 π² log² 2 - 80 π² log 2
- 16 π⁴/5 + 272 ζ(3) + 164 π²/3 - 360`; then `A₂₃,₄ = F₄ - A₁,₄` is integrable and Fubini with
`QED.ThreeLoopD.integral_i15H4` gives
`∫∫ A₂₃,₄ = 12 ζ(5) - 2 π² ζ(3)/3 + 3 π⁴/80 + 8 π² log 2 - 119 π²/16 - 41 ζ(3)/2 + 1117/32`.

## Main results

* `QED.ThreeLoopD.integral_i15A1k_four`, `QED.ThreeLoopD.integral_i15A23k_four`.
* `QED.ThreeLoopD.integral_i15F_four`: the value of `∫∫ F₄`.
* `QED.ThreeLoopD.hasTruncLaurent_i15K_of_inner_F4`: the target expansion of `K` from the two
  inner identities.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

/-- The value of `∫∫ A₁,₄`. -/
noncomputable def i15A1FourVal : ℝ :=
  384 * Li 4 (1 / 2) + 16 * log 2 ^ 4 + 32 * π ^ 2 * log 2 ^ 2 - 80 * π ^ 2 * log 2 -
    16 * π ^ 4 / 5 + 272 * zeta3 + 164 * π ^ 2 / 3 - 360

/-- The inner integral `W₄(r) / (24 x (1 - x))` of `A₁,₄` over `u`, `r = x / (1 - x)`. -/
noncomputable def i15W4G (x : ℝ) : ℝ := i15W4 (x / (1 - x)) / (24 * (x * (1 - x)))

/-- `Ψ(x) = Φ(x / (1 - x)) / 24`, a primitive of `W₄(r) / (24 x (1 - x))`. -/
noncomputable def i15W4Psi (x : ℝ) : ℝ := i15W4Phi (x / (1 - x)) / 24

theorem hasDerivAt_i15W4Psi {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
    HasDerivAt i15W4Psi (i15W4G x) x := by
  have h1 : 0 < 1 - x := by linarith [hx.2]
  have hd : HasDerivAt (fun x => x / (1 - x)) ((1 * (1 - x) - x * (-1)) / (1 - x) ^ 2) x := by
    have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
      simpa using (hasDerivAt_id' x).const_sub 1
    exact (hasDerivAt_id' x).div h2 h1.ne'
  have h := ((hasDerivAt_i15W4Phi (i15Q_ratio_mem hx)).comp x hd).div_const 24
  convert h using 1
  · funext y; rfl
  unfold i15W4G
  have h0 : x ≠ 0 := hx.1.ne'
  field_simp
  ring

theorem tendsto_i15W4Psi_zero : Tendsto i15W4Psi (𝓝[>] 0) (𝓝 (i15W4K0 / 24)) :=
  (tendsto_i15W4Phi_zero.comp i15Q_tendsto_ratio_zero).div_const 24

theorem tendsto_i15W4Psi_half : Tendsto i15W4Psi (𝓝[<] (1 / 2)) (𝓝 (i15W4K1 / 24)) :=
  (tendsto_i15W4Phi_one.comp i15Q_tendsto_ratio_half).div_const 24

/-! ### `A₁,₄`: symmetry, Tonelli and the value -/

/-- The slice integral `∫₀¹ A₁,₄(x, u) du`. -/
noncomputable def i15A1g4 (x : ℝ) : ℝ := ∫ u in Ioo (0 : ℝ) 1, i15A1k 4 (x, u)

theorem i15A1g4_one_sub (x : ℝ) : i15A1g4 (1 - x) = i15A1g4 x := by
  unfold i15A1g4
  simp only [i15A1k_one_sub]

theorem i15A1g4_nonneg {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 ≤ i15A1g4 x :=
  setIntegral_nonneg measurableSet_Ioo fun u hu => i15A1k_four_nonneg (z := (x, u)) ⟨hx, hu⟩

section Inner

variable (hA1 : ∀ x ∈ Ioo (0 : ℝ) (1 / 2), IntegrableOn (fun u => i15A1k 4 (x, u)) (Ioo 0 1) ∧
  ∫ u in Ioo (0 : ℝ) 1, i15A1k 4 (x, u) = i15W4G x)

include hA1 in
theorem i15A1g4_left :
    IntervalIntegrable i15A1g4 volume 0 (1 / 2) ∧
      ∫ x in (0 : ℝ)..(1 / 2), i15A1g4 x = i15A1FourVal / 2 := by
  have hs : ∀ x ∈ Ioo (0 : ℝ) (1 / 2), x ∈ Ioo (0 : ℝ) 1 := fun x hx =>
    ⟨hx.1, by linarith [hx.2]⟩
  have h := i15Q_ftc_nonneg (F := i15W4Psi) (f := i15A1g4) (by norm_num)
    (fun x hx => by rw [show i15A1g4 x = i15W4G x from (hA1 x hx).2]; exact hasDerivAt_i15W4Psi hx)
    (fun x hx => i15A1g4_nonneg (hs x hx)) tendsto_i15W4Psi_zero tendsto_i15W4Psi_half
  refine ⟨h.1, ?_⟩
  rw [h.2, ← sub_div, i15W4K1_sub_K0]
  unfold i15A1FourVal
  ring

include hA1 in
theorem i15A1g4_right :
    IntervalIntegrable i15A1g4 volume (1 / 2) 1 ∧
      ∫ x in (1 / 2 : ℝ)..1, i15A1g4 x = i15A1FourVal / 2 := by
  have hs : ∀ x ∈ Ioo (1 / 2 : ℝ) 1, 1 - x ∈ Ioo (0 : ℝ) (1 / 2) := fun x hx =>
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hd : ∀ x ∈ Ioo (1 / 2 : ℝ) 1,
      HasDerivAt (fun x => -i15W4Psi (1 - x)) (i15A1g4 x) x := by
    intro x hx
    have := ((hasDerivAt_i15W4Psi (hs x hx)).comp x ((hasDerivAt_id' x).const_sub 1)).neg
    rw [← i15A1g4_one_sub, show i15A1g4 (1 - x) = i15W4G (1 - x) from (hA1 _ (hs x hx)).2]
    convert this using 1
    · funext y; rfl
    · ring
  have h0 : Tendsto (fun x => -i15W4Psi (1 - x)) (𝓝[>] (1 / 2)) (𝓝 (-(i15W4K1 / 24))) := by
    refine (tendsto_i15W4Psi_half.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)).neg
    · have := ((continuous_sub_left (1 : ℝ)).tendsto (1 / 2)).mono_left
        (nhdsWithin_le_nhds (s := Ioi (1 / 2)))
      convert this using 2; norm_num
    · filter_upwards [self_mem_nhdsWithin] with x (hx : 1 / 2 < x)
      show 1 - x < 1 / 2
      linarith
  have h1 : Tendsto (fun x => -i15W4Psi (1 - x)) (𝓝[<] 1) (𝓝 (-(i15W4K0 / 24))) :=
    (tendsto_i15W4Psi_zero.comp tendsto_one_sub_nhdsLT_one).neg
  have h := i15Q_ftc_nonneg (F := fun x => -i15W4Psi (1 - x)) (f := i15A1g4) (by norm_num) hd
    (fun x hx => i15A1g4_nonneg ⟨by linarith [hx.1], hx.2⟩) h0 h1
  refine ⟨h.1, ?_⟩
  rw [h.2, show -(i15W4K0 / 24) - -(i15W4K1 / 24) = (i15W4K1 - i15W4K0) / 24 by ring,
    i15W4K1_sub_K0]
  unfold i15A1FourVal
  ring

include hA1 in
theorem integrableOn_i15A1k_four_slice {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hx2 : x ≠ 1 / 2) :
    IntegrableOn (fun u => i15A1k 4 (x, u)) (Ioo 0 1) := by
  rcases lt_or_gt_of_ne hx2 with h | h
  · exact (hA1 x ⟨hx.1, h⟩).1
  · have := (hA1 (1 - x) ⟨by linarith [hx.2], by linarith⟩).1
    simpa only [i15A1k_one_sub] using this

include hA1 in
/-- **`A₁,₄` is integrable on the square** (Tonelli), given its inner integral. -/
theorem integrable_i15A1k_four : IntegrableOn (i15A1k 4) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  rw [IntegrableOn, volume_restrict_prod2,
    integrable_prod_iff (measurable_i15A1k 4).aestronglyMeasurable]
  have hne : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), x ∈ ({1 / 2} : Set ℝ)ᶜ :=
    ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton _))
  have hgI : IntegrableOn i15A1g4 (Ioo 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      ((i15A1g4_left hA1).1.trans (i15A1g4_right hA1).1)
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioo, hne] with x hx hx2
    exact integrableOn_i15A1k_four_slice hA1 hx hx2
  · refine hgI.congr_fun (fun x hx => ?_) measurableSet_Ioo
    unfold i15A1g4
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (i15A1k_four_nonneg (z := (x, u)) ⟨hx, hu⟩)]

include hA1 in
/-- **`∫∫ A₁,₄`**, given its inner integral. -/
theorem integral_i15A1k_four :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15A1k 4 z = i15A1FourVal := by
  have hF : Integrable (i15A1k 4) ((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1))) := by
    rw [← volume_restrict_prod2]; exact integrable_i15A1k_four hA1
  rw [volume_restrict_prod2, integral_prod _ hF]
  change ∫ x in Ioo (0 : ℝ) 1, i15A1g4 x = _
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_add_adjacent_intervals (i15A1g4_left hA1).1
      (i15A1g4_right hA1).1, (i15A1g4_left hA1).2, (i15A1g4_right hA1).2]
  ring

end Inner

/-! ### `A₂₃,₄` by Fubini -/

/-- **`∫∫ A₂₃,₄`**, given its integrability on the square and its inner integral. -/
theorem integral_i15A23k_four
    (hA23 : ∀ u ∈ Ioo (0 : ℝ) 1, IntegrableOn (fun x => i15A23k 4 (x, u)) (Ioo 0 1) →
      ∫ x in Ioo (0 : ℝ) 1, i15A23k 4 (x, u) = i15H4 u)
    (hA : IntegrableOn (i15A23k 4) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15A23k 4 z = i15H4Val := by
  have hF : Integrable (i15A23k 4) ((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1))) := by
    rw [← volume_restrict_prod2]; exact hA
  rw [volume_restrict_prod2, integral_prod_symm _ hF]
  have hae : (fun u => ∫ x, i15A23k 4 (x, u) ∂volume.restrict (Ioo (0 : ℝ) 1)) =ᵐ[volume.restrict
      (Ioo (0 : ℝ) 1)] i15H4 := by
    filter_upwards [hF.prod_left_ae, ae_restrict_mem measurableSet_Ioo] with u hu1 hu2
    exact hA23 u hu2 hu1
  rw [integral_congr_ae hae, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one]
  refine integral_i15H4 ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr ?_)
  exact hF.integral_prod_right.congr hae

/-! ### The fourth Taylor coefficient -/

/-- **`∫∫ F₄`**, given the inner integrals of `A₁,₄` and `A₂₃,₄`. -/
theorem integral_i15F_four
    (hA1 : ∀ x ∈ Ioo (0 : ℝ) (1 / 2), IntegrableOn (fun u => i15A1k 4 (x, u)) (Ioo 0 1) ∧
      ∫ u in Ioo (0 : ℝ) 1, i15A1k 4 (x, u) = i15W4G x)
    (hA23 : ∀ u ∈ Ioo (0 : ℝ) 1, IntegrableOn (fun x => i15A23k 4 (x, u)) (Ioo 0 1) →
      ∫ x in Ioo (0 : ℝ) 1, i15A23k 4 (x, u) = i15H4 u) :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15F 4 z =
      384 * QED.Polylog.Li 4 (1 / 2) + 16 * Real.log 2 ^ 4
        + 32 * Real.pi ^ 2 * Real.log 2 ^ 2 - 72 * Real.pi ^ 2 * Real.log 2
        - 253 / 80 * Real.pi ^ 4 - 2 / 3 * Real.pi ^ 2 * QED.Polylog.zeta3
        + 2267 / 48 * Real.pi ^ 2 + 503 / 2 * QED.Polylog.zeta3 + 12 * QED.Polylog.zeta5
        - 10403 / 32 := by
  obtain ⟨h23, hsplit⟩ := integral_i15F_eq_add (k := 4) (by norm_num) (integrable_i15A1k_four hA1)
  rw [hsplit, integral_i15A1k_four hA1, integral_i15A23k_four hA23 h23]
  unfold i15A1FourVal i15H4Val
  ring

/-- **The target expansion of `K`**, given the inner integrals of `F₄`. -/
theorem hasTruncLaurent_i15K_of_inner_F4
    (hA1 : ∀ x ∈ Ioo (0 : ℝ) (1 / 2), IntegrableOn (fun u => i15A1k 4 (x, u)) (Ioo 0 1) ∧
      ∫ u in Ioo (0 : ℝ) 1, i15A1k 4 (x, u) = i15W4G x)
    (hA23 : ∀ u ∈ Ioo (0 : ℝ) 1, IntegrableOn (fun x => i15A23k 4 (x, u)) (Ioo 0 1) →
      ∫ x in Ioo (0 : ℝ) 1, i15A23k 4 (x, u) = i15H4 u) :
    HasTruncLaurent i15K i15KLaurent 5 :=
  hasTruncLaurent_i15K_of_F4 (integral_i15F_four hA1 hA23)

end QED.ThreeLoopD
