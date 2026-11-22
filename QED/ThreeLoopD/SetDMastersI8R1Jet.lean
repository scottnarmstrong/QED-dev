/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R0
public import QED.ThreeLoopD.SetDMastersI13R1

/-!
# Set (d), master `I₈`: the Taylor coefficients of the angular average and of the integrands

With `w_ε(z) = (1 - z²) ^ (1/2 - ε) = √(1 - z²) exp (-ε log (1 - z²))`, the coefficients of
`J_ε(t) = ∫₀¹ w_ε(z)/(t + 4z²) dz` and of the moments `∫₀¹ w_ε`, `∫₀¹ z² w_ε` are the integrals of
`√(1 - z²) (-log (1 - z²))ᵏ / k!` against `1/(t + 4z²)`, `1`, `z²`
(`QED.ThreeLoopD.i8Jet_J`, `QED.ThreeLoopD.i8Jet_Mom0`, `QED.ThreeLoopD.i8Jet_Mom2`).

**The normalization.** Legendre's duplication formula `Γ(1 - ε) Γ(3/2 - ε) =
2 ^ (2ε - 1) √π Γ(2 - 2ε)` gives

  `N_ε = (4/π) 4 ^ (-ε) (1 - ε)/(1 - 2ε) G(ε)`, `G = Γ(1 - ε)²/Γ(1 - 2ε)`

(`QED.ThreeLoopD.i8Nrm_eq_G`), so `N₀ = 4/π`, `N₁ = N₀ (1 - 2 log 2)` and
`N₂ = N₀ (2 log² 2 - 2 log 2 + 2 - π²/6)` (`QED.ThreeLoopD.i8NC_one`, `QED.ThreeLoopD.i8NC_two`).

**The integrands.** The jets of `h₁ = t ^ (1 - ε) b_ε² N_ε J_ε` and of `Asym` are Cauchy products
(`QED.ThreeLoopD.i8Jet_remInt1`, `QED.ThreeLoopD.i8Jet_remInt2`); at first order, with
`λ = log t` and `β₁` the first bubble coefficient,

  `D¹ h₁(t) = (1 - ξ)(-λ + 2β₁ + 1 - 2 log 2) + t N₀ J₁(t)`,
  `D¹ Asym(t) = 4 - 3λ + (-17/2 - λ)/t`

(`QED.ThreeLoopD.i8R1C_one`, `QED.ThreeLoopD.i8AsymC_one`).

## Main results

* `QED.ThreeLoopD.i8Jet_integral`, `QED.ThreeLoopD.i8Jet_J`, `QED.ThreeLoopD.i8Jet_Nrm`.
* `QED.ThreeLoopD.i8Jet_remInt1`, `QED.ThreeLoopD.i8Jet_remInt2`.
* `QED.ThreeLoopD.i8R1C_one`, `QED.ThreeLoopD.i8AsymC_one`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Filter Topology QED.Polylog
open scoped Nat

namespace QED.ThreeLoopD

/-! ### Jets of parametric integrals -/

/-- **The jet of a parametric integral**: the coefficients are the integrals of the pointwise
coefficients. -/
theorem i8Jet_integral {s : Set ℝ} {g : ℝ → ℂ → ℂ} {c : ℝ → ℕ → ℂ} {R ρ : ℝ} {M : ℝ → ℝ}
    (hs : MeasurableSet s) (hρ : 0 < ρ) (hρR : ρ < R) (hMi : IntegrableOn M s)
    (hd : ∀ x ∈ s, DifferentiableOn ℂ (g x) (ball 0 R))
    (hm : ∀ ε ∈ ball (0 : ℂ) R, AEStronglyMeasurable (fun x => g x ε) (volume.restrict s))
    (hb : ∀ x ∈ s, ∀ ε : ℂ, ‖ε‖ = ρ → ‖g x ε‖ ≤ M x)
    (hc : ∀ x ∈ s, ∀ k, i13Dsl (g x) k 0 = c x k) :
    I13Jet (fun ε => ∫ x in s, g x ε) fun k => ∫ x in s, c x k := by
  have hd' : ∀ᵐ x ∂(volume.restrict s), DifferentiableOn ℂ (g x) (ball 0 R) :=
    ae_restrict_of_forall_mem hs hd
  have hb' : ∀ᵐ x ∂(volume.restrict s), ∀ ε : ℂ, ‖ε‖ = ρ → ‖g x ε‖ ≤ M x :=
    ae_restrict_of_forall_mem hs hb
  have hball : ∀ ε : ℂ, ‖ε‖ ≤ ρ → ε ∈ ball (0 : ℂ) R := fun ε hε => by
    rw [mem_ball, dist_zero_right]; linarith
  have hdiff : DifferentiableOn ℂ (fun ε => ∫ x in s, g x ε) (ball 0 (ρ / 2)) := by
    intro ε₀ h0
    have hsub : ∀ ε ∈ ball ε₀ (ρ / 2), ‖ε‖ ≤ ρ := fun ε hε => by
      rw [mem_ball, dist_eq_norm] at hε
      rw [mem_ball, dist_zero_right] at h0
      linarith [norm_sub_norm_le ε ε₀]
    refine (QED.DimReg.differentiableAt_integral_of_holomorphic (F := fun ε x => g x ε)
      (half_pos hρ) hMi (fun ε hε => hm ε (hball ε (hsub ε hε))) ?_ ?_).differentiableWithinAt
    · filter_upwards [hd', hb'] with x hx hxb ε hε
      simpa using norm_i13Dsl_le hρ hρR hx hxb 0 ε (hsub ε hε)
    · filter_upwards [hd'] with x hx
      exact hx.mono fun ε hε => hball ε (hsub ε hε)
  refine ⟨ρ / 2, half_pos hρ, hdiff, fun k => ?_⟩
  have H := hasTruncLaurent_integral_i13Dsl hρ hρR hMi hd' hm hb' (k + 1)
  rw [i13Dsl_zero_eq_of_hasTruncLaurent (half_pos hρ) hdiff H k (Nat.lt_succ_self k)]
  exact setIntegral_congr_fun hs fun x hx => hc x hx k

theorem I13Jet.dsl_eq {f : ℂ → ℂ} {a : ℕ → ℂ} (hf : I13Jet f a) (k : ℕ) : i13Dsl f k 0 = a k := by
  obtain ⟨-, -, -, h⟩ := hf
  exact h k

/-! ### The angular weight -/

/-- The Taylor coefficients `√(1 - z²) (-log (1 - z²))ᵏ / k!` of `ε ↦ w_ε(z)`. -/
noncomputable def i8WC (z : ℝ) (k : ℕ) : ℂ :=
  (√(1 - z ^ 2) : ℂ) * ((-Real.log (1 - z ^ 2) : ℝ) : ℂ) ^ k / (k ! : ℂ)

theorem i8Wt_eq_exp {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) (ε : ℂ) :
    i8Wt ε z = (√(1 - z ^ 2) : ℂ) * exp (((-Real.log (1 - z ^ 2) : ℝ) : ℂ) * ε) := by
  have hr := i8_one_sub_sq_pos hz
  have h0 : ((1 - z ^ 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  rw [← i13_cpow_neg_eq_exp hr, ← i8Wt_zero hz]
  unfold i8Wt
  rw [← cpow_add _ _ h0]
  congr 1
  ring

theorem i8Dsl_wt_mul {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) (q : ℂ) (k : ℕ) :
    i13Dsl (fun ε => i8Wt ε z * q) k 0 = i8WC z k * q := by
  rw [(((i13Jet_exp ((-Real.log (1 - z ^ 2) : ℝ) : ℂ)).const_mul
    ((√(1 - z ^ 2) : ℂ) * q))).congr (funext fun ε => by rw [i8Wt_eq_exp hz]; ring) |>.dsl_eq k]
  unfold i8WC
  ring

theorem i8Dsl_wt_div {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) (q : ℂ) (k : ℕ) :
    i13Dsl (fun ε => i8Wt ε z / q) k 0 = i8WC z k / q := by
  simp_rw [div_eq_mul_inv]
  exact i8Dsl_wt_mul hz _ k

theorem differentiable_i8Wt {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    Differentiable ℂ fun ε => i8Wt ε z := by
  unfold i8Wt
  exact Differentiable.const_cpow (by fun_prop)
    (Or.inl (ofReal_ne_zero.mpr (i8_one_sub_sq_pos hz).ne'))

theorem i8_re_le_of_norm {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 2) : ε.re ≤ 1 / 2 :=
  (re_le_norm ε).trans hε

/-! ### The jets of `J` and of the moments -/

/-- The coefficients `Jₖ(t) = ∫₀¹ √(1 - z²) (-log (1 - z²))ᵏ / k! / (t + 4z²) dz`. -/
noncomputable def i8JC (t : ℝ) (k : ℕ) : ℂ :=
  ∫ z in Ioo (0 : ℝ) 1, i8WC z k / ((t + 4 * z ^ 2 : ℝ) : ℂ)

theorem i8Jet_J {t : ℝ} (ht : 0 < t) : I13Jet (fun ε => i8J ε t) (i8JC t) := by
  refine i8Jet_integral (R := 1 / 2) (ρ := 1 / 4) (M := fun _ => t⁻¹) measurableSet_Ioo
    (by norm_num) (by norm_num) (integrable_const _)
    (fun z hz => ((differentiable_i8Wt hz).div_const _).differentiableOn)
    (fun ε hε => (integrableOn_i8J (i8_re_le_of_norm (by
      rw [mem_ball, dist_zero_right] at hε; linarith)) ht).aestronglyMeasurable)
    (fun z hz ε hε => ?_) (fun z hz k => i8Dsl_wt_div hz _ k)
  rw [div_eq_mul_inv, norm_mul]
  calc ‖i8Wt ε z‖ * ‖(((t + 4 * z ^ 2 : ℝ) : ℂ))⁻¹‖ ≤ 1 * t⁻¹ :=
        mul_le_mul (norm_i8Wt_le (i8_re_le_of_norm (by rw [hε]; norm_num)) hz)
          (norm_i8_inv_den_le ht z) (norm_nonneg _) zero_le_one
    _ = t⁻¹ := one_mul _

/-- The coefficients of `∫₀¹ w_ε`. -/
noncomputable def i8M0C (k : ℕ) : ℂ := ∫ z in Ioo (0 : ℝ) 1, i8WC z k

/-- The coefficients of `∫₀¹ z² w_ε`. -/
noncomputable def i8M2C (k : ℕ) : ℂ := ∫ z in Ioo (0 : ℝ) 1, i8WC z k * ((z ^ 2 : ℝ) : ℂ)

theorem i8_norm_sq_le {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) : ‖((z ^ 2 : ℝ) : ℂ)‖ ≤ 1 := by
  rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [hz.1, hz.2]

theorem i8Jet_Mom2 : I13Jet i8Mom2 i8M2C := by
  refine i8Jet_integral (R := 1 / 2) (ρ := 1 / 4) (M := fun _ => 1) measurableSet_Ioo
    (by norm_num) (by norm_num) (integrable_const _)
    (fun z hz => ((differentiable_i8Wt hz).mul_const _).differentiableOn)
    (fun ε _ => ((measurable_i8Wt ε).mul (by fun_prop)).aestronglyMeasurable)
    (fun z hz ε hε => ?_) (fun z hz k => i8Dsl_wt_mul hz _ k)
  rw [norm_mul]
  calc ‖i8Wt ε z‖ * ‖((z ^ 2 : ℝ) : ℂ)‖ ≤ 1 * 1 :=
        mul_le_mul (norm_i8Wt_le (i8_re_le_of_norm (by rw [hε]; norm_num)) hz)
          (i8_norm_sq_le hz) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

theorem i8Jet_Mom0 : I13Jet i8Mom0 i8M0C := by
  have h := i8Jet_integral (s := Ioo (0 : ℝ) 1) (g := fun z ε => i8Wt ε z * 1)
    (c := fun z k => i8WC z k * 1) (R := 1 / 2) (ρ := 1 / 4) (M := fun _ => 1)
    measurableSet_Ioo (by norm_num) (by norm_num) (integrable_const _)
    (fun z hz => ((differentiable_i8Wt hz).mul_const _).differentiableOn)
    (fun ε _ => ((measurable_i8Wt ε).mul_const _).aestronglyMeasurable)
    (fun z hz ε hε => by
      rw [mul_one]; exact norm_i8Wt_le (i8_re_le_of_norm (by rw [hε]; norm_num)) hz)
    (fun z hz k => i8Dsl_wt_mul hz _ k)
  simp only [mul_one] at h
  exact h

/-! ### The normalization -/

/-- **Duplication**: `N_ε = (4/π) 4 ^ (-ε) (1 - ε)/(1 - 2ε) G(ε)`. -/
theorem i8Nrm_eq_G {ε : ℂ} (hε : ‖ε‖ < 1 / 8) :
    i8Nrm ε = 4 / (Real.pi : ℂ) * exp (((-2 * Real.log 2 : ℝ) : ℂ) * ε) * (1 - ε) *
      (1 / (1 - 2 * ε)) * i13G ε := by
  have hre : ε.re < 1 / 8 := (re_le_norm ε).trans_lt hε
  have hpos : ∀ s : ℂ, 0 < s.re → Gamma s ≠ 0 := fun s hs => Gamma_ne_zero_of_re_pos hs
  have g1 : Gamma (1 - ε) ≠ 0 := hpos _ (by simp; linarith)
  have g12 : Gamma (1 - 2 * ε) ≠ 0 := hpos _ (by simp; linarith)
  have g3 : Gamma (3 / 2 - ε) ≠ 0 := hpos _ (by rw [sub_re]; norm_num; linarith)
  have h1 : (1 : ℂ) - ε ≠ 0 := fun h => by
    have := congr_arg re h; simp at this; linarith
  have h12 : (1 : ℂ) - 2 * ε ≠ 0 := fun h => by
    have := congr_arg re h; simp at this; linarith
  have hs : ((√Real.pi : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpi : (Real.pi : ℂ) = ((√Real.pi : ℝ) : ℂ) ^ 2 := by
    rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hdup := Complex.Gamma_mul_Gamma_add_half (1 - ε)
  rw [show 1 - ε + 1 / 2 = 3 / 2 - ε by ring, show (1 : ℂ) - 2 * (1 - ε) = 2 * ε - 1 by ring,
    show 2 * (1 - ε) = (1 - 2 * ε) + 1 by ring, Gamma_add_one _ h12] at hdup
  have hl : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [ofReal_log zero_le_two]; norm_num
  have h2 : exp ((Real.log 2 : ℝ) : ℂ) = 2 := by rw [← hl, exp_log two_ne_zero]
  have hE : exp (((-2 * Real.log 2 : ℝ) : ℂ) * ε) * (2 * (2 : ℂ) ^ (2 * ε - 1)) = 1 := by
    rw [cpow_def_of_ne_zero two_ne_zero, hl]
    have e : (2 : ℂ) * exp (((Real.log 2 : ℝ) : ℂ) * (2 * ε - 1)) =
        exp (((Real.log 2 : ℝ) : ℂ) * (2 * ε)) := by
      rw [show ((Real.log 2 : ℝ) : ℂ) * (2 * ε) =
        ((Real.log 2 : ℝ) : ℂ) + ((Real.log 2 : ℝ) : ℂ) * (2 * ε - 1) by ring, exp_add, h2]
    rw [e, ← exp_add, ← exp_zero]
    congr 1
    push_cast
    ring
  have hE0 : (2 : ℂ) ^ (2 * ε - 1) ≠ 0 := by
    intro h; rw [h, mul_zero, mul_zero] at hE; exact zero_ne_one hE
  have hX : exp (((-2 * Real.log 2 : ℝ) : ℂ) * ε) = 1 / (2 * (2 : ℂ) ^ (2 * ε - 1)) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero hE0)]; exact hE
  have hg3 : Gamma (3 / 2 - ε) =
      (1 - 2 * ε) * Gamma (1 - 2 * ε) * (2 : ℂ) ^ (2 * ε - 1) * ((√Real.pi : ℝ) : ℂ) /
        Gamma (1 - ε) := by
    rw [eq_div_iff g1, ← hdup]; ring
  unfold i8Nrm i13G
  rw [hX, hg3, i13_Gamma_half, show (2 : ℂ) - ε = (1 - ε) + 1 by ring, Gamma_add_one _ h1, hpi]
  field_simp
  ring

/-- The Taylor coefficients of `N_ε`. -/
noncomputable def i8NC (k : ℕ) : ℂ := i13Dsl i8Nrm k 0

theorem i8Jet_Nrm : I13Jet i8Nrm i8NC :=
  I13Jet.of_differentiableOn (R := 1 / 2) (by norm_num) fun ε hε =>
    (differentiableAt_i8Nrm (by rwa [mem_ball, dist_zero_right] at hε)).differentiableWithinAt

/-- The coefficients of the duplication form of `N_ε`. -/
noncomputable def i8NdC : ℕ → ℂ :=
  i13Cauchy (i13Cauchy (i13Cauchy (fun k => 4 / (Real.pi : ℂ) *
    (((-2 * Real.log 2 : ℝ) : ℂ) ^ k / (k ! : ℂ)))
    fun k => (if k = 0 then 1 else 0) - (if k = 1 then 1 else 0)) fun k => 2 ^ k) i13GC

theorem i8NC_eq (k : ℕ) : i8NC k = i8NdC k := by
  have J := (((((i13Jet_exp ((-2 * Real.log 2 : ℝ) : ℂ)).const_mul (4 / (Real.pi : ℂ))).mul'
    ((i13Jet_const 1).sub i13Jet_id)).mul' (i13Jet_geom 2)).mul' i13Jet_G).congr_ball
      (g := i8Nrm) (r := 1 / 8) (by norm_num) fun ε hε => by
        rw [mem_ball, dist_zero_right] at hε
        rw [i8Nrm_eq_G hε]
  exact J.dsl_eq k

theorem i8NC_zero : i8NC 0 = 4 / (Real.pi : ℂ) := by
  rw [i8NC_eq]
  simp [i8NdC, i13Cauchy, i13GC_zero]

theorem i8NC_one : i8NC 1 = 4 / (Real.pi : ℂ) * (1 - 2 * (Real.log 2 : ℂ)) := by
  rw [i8NC_eq]
  simp [i8NdC, i13Cauchy, Finset.sum_range_succ, i13GC_zero, i13GC_one]
  ring

theorem i8NC_two : i8NC 2 = 4 / (Real.pi : ℂ) *
    (2 * (Real.log 2 : ℂ) ^ 2 - 2 * (Real.log 2 : ℂ) + 2 - (Real.pi : ℂ) ^ 2 / 6) := by
  rw [i8NC_eq]
  simp [i8NdC, i13Cauchy, Finset.sum_range_succ, i13GC_zero, i13GC_one,
    i13GC_eq 2 (by norm_num), i13GpC]
  ring

/-! ### `κ` -/

theorem i8Jet_Kap : I13Jet i8Kap fun k => (1 / 2) ^ k :=
  (i13Jet_geom (1 / 2)).congr_ball (r := 1) one_pos fun ε hε => by
    rw [mem_ball, dist_zero_right] at hε
    have h : (2 : ℂ) - ε ≠ 0 := fun h => by
      have : ‖ε‖ = 2 := by rw [show ε = 2 by linear_combination -h]; simp
      linarith
    unfold i8Kap
    field_simp

/-! ### The jets of the integrands -/

/-- The coefficients of `Asym(·, t)`. -/
noncomputable def i8AsymC (t : ℝ) (k : ℕ) : ℂ :=
  i13Cauchy (i13Cauchy i13A0C i13A0C) (i13TpC t 0 (-3)) k +
    i13Cauchy (fun k => 2 * i13Cauchy i13A0C i13A1C k -
      i13Cauchy (fun k => (1 / 2) ^ k) (i13Cauchy i13A0C i13A0C) k) (i13TpC t (-1) (-3)) k +
    i13Cauchy (fun k => 2 * i13Cauchy i13A0C i13B0C k) (i13TpC t (-1) (-2)) k

theorem i8Jet_asym {t : ℝ} (ht : 0 < t) : I13Jet (fun ε => i8Asym ε t) (i8AsymC t) := by
  have J1 := (i13Jet_Al0.mul' i13Jet_Al0).mul' (i13Jet_tpow ht (fun ε => -3 * ε) 0 (-3)
    fun ε => by ring)
  have J2 := (((i13Jet_Al0.mul' i13Jet_Al1).const_mul 2).sub
    (i8Jet_Kap.mul' (i13Jet_Al0.mul' i13Jet_Al0))).mul'
    (i13Jet_tpow ht (fun ε => -1 - 3 * ε) (-1) (-3) fun ε => by ring)
  have J3 := ((i13Jet_Al0.mul' i13Jet_Be0).const_mul 2).mul'
    (i13Jet_tpow ht (fun ε => -1 - 2 * ε) (-1) (-2) fun ε => by ring)
  refine ((J1.add J2).add J3).congr (funext fun ε => ?_)
  unfold i8Asym
  ring

/-- The coefficients of `h₁(t, ·) = t ^ (1 - ε) b_ε(t)² N_ε J_ε(t)`. -/
noncomputable def i8R1C (t : ℝ) : ℕ → ℂ :=
  i13Cauchy (i13TpC t 1 (-1)) (i13Cauchy (i13Cauchy (i13BubC t) (i13BubC t))
    (i13Cauchy i8NC (i8JC t)))

theorem i8Jet_remInt1 {t : ℝ} (ht : 0 < t) : I13Jet (i8RemInt1 t) (i8R1C t) :=
  ((i13Jet_tpow ht (fun ε => 1 - ε) 1 (-1) fun ε => by ring).mul'
    (((i13Jet_bub ht.le).mul' (i13Jet_bub ht.le)).mul' (i8Jet_Nrm.mul' (i8Jet_J ht)))).congr
    (funext fun ε => by unfold i8RemInt1; rw [i8Ang_eq]; ring)

theorem i8Jet_remInt2 {t : ℝ} (ht : 0 < t) :
    I13Jet (i8RemInt2 t) fun k => i8R1C t k - i8AsymC t k :=
  ((i8Jet_remInt1 ht).sub (i8Jet_asym ht)).congr (funext fun ε => by
    unfold i8RemInt2 i8RemInt1; rfl)

/-! ### The first coefficients -/

/-- `J₁(t) = ∫₀¹ √(1 - z²) (-log (1 - z²)) / (t + 4z²) dz`. -/
noncomputable def i8J1r (t : ℝ) : ℝ :=
  ∫ z in Ioo (0 : ℝ) 1, √(1 - z ^ 2) * -Real.log (1 - z ^ 2) / (t + 4 * z ^ 2)

theorem i8JC_one (t : ℝ) : i8JC t 1 = (i8J1r t : ℂ) := by
  unfold i8JC i8J1r
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioo fun z _ => ?_
  unfold i8WC
  push_cast
  ring

theorem i8_t_NC_JC_zero {t : ℝ} (ht : 0 < t) :
    (t : ℂ) * (i8NC 0 * i8JC t 0) = ((1 - i13Xi t : ℝ) : ℂ) := by
  rw [← i8_t_mul_Ang_zero ht, i8Ang_eq, ← (i8Jet_J ht).dsl_eq 0]
  rfl

theorem i8R1C_one {t : ℝ} (ht : 0 < t) :
    i8R1C t 1 = (((1 - i13Xi t) * (-Real.log t + 2 * i13Be1r t + (1 - 2 * Real.log 2)) +
      t * (4 / Real.pi) * i8J1r t : ℝ) : ℂ) := by
  have h0 := i8_t_NC_JC_zero ht
  have hb := i13BubC_one ht
  simp only [i8R1C, i13Cauchy, i13TpC, Finset.sum_range_succ, Finset.sum_range_zero,
    i13BubC_zero, cpow_one, Nat.sub_self, Nat.sub_zero, zero_add] at h0 ⊢
  rw [i8NC_one, i8JC_one, hb, i8NC_zero]
  rw [i8NC_zero] at h0
  simp only [ofReal_sub, ofReal_add, ofReal_mul, ofReal_neg, ofReal_one, ofReal_ofNat,
    ofReal_div] at h0 ⊢
  linear_combination (-(Real.log t : ℂ) + 2 * (i13Be1r t : ℂ) + 1 - 2 * (Real.log 2 : ℂ)) * h0

theorem i8AsymC_one {t : ℝ} (ht : 0 < t) :
    i8AsymC t 1 = ((4 - 3 * Real.log t + (-17 / 2 - Real.log t) / t : ℝ) : ℂ) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  simp only [i8AsymC, i13A0C, i13A1C, i13B0C, i13Cauchy, i13TpC,
    Finset.sum_range_succ, Finset.sum_range_zero, i13GC_zero, i13GC_one, cpow_zero,
    cpow_neg_one]
  norm_num
  simp only [i13GC_zero, i13GC_one]
  field_simp
  ring

end QED.ThreeLoopD
