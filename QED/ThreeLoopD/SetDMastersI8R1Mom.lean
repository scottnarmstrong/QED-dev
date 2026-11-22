/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R1Jet

/-!
# Set (d), master `I₈`: logarithmic moments of the angular weight

With `w(z) = √(1 - z²)`, `L(z) = log (1 - z²)` and `l = log 2`,

  `∫₀¹ w L = (π/4)(1 - 2l)`, `∫₀¹ w L z² = (π/4)(1/8 - l/2)`,
  `∫₀¹ w L² z² = (π/2)(l²/2 - l/4 - 5/16 + π²/24)`,
  `∫₀¹ w L z² log z = π (l²/8 - l/16 + 3/64) - π³/192`.

The first three are the first coefficients of `N_ε ∫ w_ε = 1` and `4 N_ε ∫ z² w_ε = κ`
(`QED.ThreeLoopD.i8Nrm_mul_Mom0`, `QED.ThreeLoopD.i8Nrm_mul_Mom2`), given the coefficients of `N_ε`.
For the last, `x = z²` turns it into `Y/4`, `Y = ∫₀¹ √(x (1 - x)) log x log (1 - x) dx`; the
reflection formula gives `2 cos (πε) ∫₀¹ x ^ (1/2 + ε) (1 - x) ^ (1/2 - ε) dx = π (1/4 - ε²)`, whose
`ε²` coefficient, with the symmetry `x ↦ 1 - x`, determines `Y`.

## Main results

* `QED.ThreeLoopD.i8_integral_wL`, `QED.ThreeLoopD.i8_integral_wLz2`,
  `QED.ThreeLoopD.i8_integral_wL2z2`, `QED.ThreeLoopD.i8_integral_wLz2log`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Filter Topology
open scoped Nat

namespace QED.ThreeLoopD

/-! ### The moments of `w_ε` -/

theorem i8_cauchy_Mom0 (k : ℕ) : i13Cauchy i8NC i8M0C k = if k = 0 then 1 else 0 := by
  have J := (i8Jet_Nrm.mul' i8Jet_Mom0).congr_ball (g := fun _ => (1 : ℂ)) (r := 1 / 2)
    (by norm_num) fun ε hε => i8Nrm_mul_Mom0 (by rwa [mem_ball, dist_zero_right] at hε)
  rw [← J.dsl_eq k, (i13Jet_const 1).dsl_eq k]

theorem i8_cauchy_Mom2 (k : ℕ) : 4 * i13Cauchy i8NC i8M2C k = (1 / 2) ^ k := by
  have J := ((i8Jet_Nrm.mul' i8Jet_Mom2).const_mul 4).congr_ball (g := i8Kap) (r := 1 / 2)
    (by norm_num) fun ε hε => by
      rw [← i8Nrm_mul_Mom2 (by rwa [mem_ball, dist_zero_right] at hε)]; ring
  rw [← J.dsl_eq k, i8Jet_Kap.dsl_eq k]

theorem i8_pi_ne : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'

theorem i8M0C_one : i8M0C 1 = -((Real.pi : ℂ) / 4 * (1 - 2 * (Real.log 2 : ℂ))) := by
  have e0 := i8_cauchy_Mom0 0
  have e1 := i8_cauchy_Mom0 1
  simp only [i13Cauchy, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.sub_self, Nat.sub_zero, i8NC_zero, i8NC_one, ite_true, one_ne_zero, ite_false] at e0 e1
  have hpi := i8_pi_ne
  generalize ((Real.log 2 : ℝ) : ℂ) = L at e0 e1 ⊢
  generalize ((Real.pi : ℝ) : ℂ) = p at e0 e1 hpi ⊢
  have m0 : i8M0C 0 = p / 4 := by field_simp at e0; linear_combination e0 / 4
  rw [m0] at e1
  field_simp at e1
  linear_combination e1 / 4

theorem i8M2C_vals : i8M2C 1 = (Real.pi : ℂ) / 4 * (-1 / 8 + (Real.log 2 : ℂ) / 2) ∧
    i8M2C 2 = (Real.pi : ℂ) / 4 * ((Real.log 2 : ℂ) ^ 2 / 2 - (Real.log 2 : ℂ) / 4 - 5 / 16 +
      (Real.pi : ℂ) ^ 2 / 24) := by
  have e0 := i8_cauchy_Mom2 0
  have e1 := i8_cauchy_Mom2 1
  have e2 := i8_cauchy_Mom2 2
  simp only [i13Cauchy, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.sub_self, Nat.sub_zero, i8NC_zero, i8NC_one, i8NC_two] at e0 e1 e2
  have hpi := i8_pi_ne
  generalize ((Real.log 2 : ℝ) : ℂ) = L at e0 e1 e2 ⊢
  generalize ((Real.pi : ℝ) : ℂ) = p at e0 e1 e2 hpi ⊢
  have m0 : i8M2C 0 = p / 16 := by
    field_simp at e0; linear_combination e0 / 16
  rw [m0] at e1 e2
  have m1 : i8M2C 1 = p / 4 * (-1 / 8 + L / 2) := by
    field_simp at e1; linear_combination e1 / 512
  refine ⟨m1, ?_⟩
  rw [m1] at e2
  field_simp at e2
  linear_combination e2 / 49152

/-! ### Real forms -/

theorem i8_cast_integral {f : ℝ → ℝ} {g : ℝ → ℂ} (h : ∀ z ∈ Ioo (0 : ℝ) 1, g z = (f z : ℂ)) :
    ∫ z in Ioo (0 : ℝ) 1, g z = ((∫ z in Ioo (0 : ℝ) 1, f z : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  exact setIntegral_congr_fun measurableSet_Ioo h

/-- `∫₀¹ √(1 - z²) log (1 - z²) dz = (π/4)(1 - 2 log 2)`. -/
theorem i8_integral_wL :
    ∫ z in Ioo (0 : ℝ) 1, √(1 - z ^ 2) * Real.log (1 - z ^ 2) =
      Real.pi / 4 * (1 - 2 * Real.log 2) := by
  have h := i8M0C_one
  unfold i8M0C at h
  rw [i8_cast_integral (f := fun z => -(√(1 - z ^ 2) * Real.log (1 - z ^ 2))) fun z _ => by
    unfold i8WC; push_cast; ring] at h
  rw [integral_neg] at h
  exact_mod_cast neg_injective (by exact_mod_cast h)

/-- `∫₀¹ √(1 - z²) log (1 - z²) z² dz = (π/4)(1/8 - log 2 / 2)`. -/
theorem i8_integral_wLz2 :
    ∫ z in Ioo (0 : ℝ) 1, √(1 - z ^ 2) * Real.log (1 - z ^ 2) * z ^ 2 =
      Real.pi / 4 * (1 / 8 - Real.log 2 / 2) := by
  have h := i8M2C_vals.1
  unfold i8M2C at h
  rw [i8_cast_integral (f := fun z => -(√(1 - z ^ 2) * Real.log (1 - z ^ 2) * z ^ 2))
    fun z _ => by unfold i8WC; push_cast; ring, integral_neg] at h
  have h' : ((∫ z in Ioo (0 : ℝ) 1, √(1 - z ^ 2) * Real.log (1 - z ^ 2) * z ^ 2 : ℝ) : ℂ) =
      ((Real.pi / 4 * (1 / 8 - Real.log 2 / 2) : ℝ) : ℂ) := by
    push_cast at h ⊢; linear_combination -h
  exact_mod_cast h'

/-- `∫₀¹ √(1 - z²) log² (1 - z²) z² dz = (π/2)(l²/2 - l/4 - 5/16 + π²/24)`. -/
theorem i8_integral_wL2z2 :
    ∫ z in Ioo (0 : ℝ) 1, √(1 - z ^ 2) * Real.log (1 - z ^ 2) ^ 2 * z ^ 2 =
      Real.pi / 2 * (Real.log 2 ^ 2 / 2 - Real.log 2 / 4 - 5 / 16 + Real.pi ^ 2 / 24) := by
  have h := i8M2C_vals.2
  unfold i8M2C at h
  rw [i8_cast_integral (f := fun z => √(1 - z ^ 2) * Real.log (1 - z ^ 2) ^ 2 * z ^ 2 / 2)
    fun z _ => by unfold i8WC; push_cast; ring, integral_div] at h
  have h' : ((∫ z in Ioo (0 : ℝ) 1, √(1 - z ^ 2) * Real.log (1 - z ^ 2) ^ 2 * z ^ 2 : ℝ) : ℂ) =
      ((Real.pi / 2 * (Real.log 2 ^ 2 / 2 - Real.log 2 / 4 - 5 / 16 + Real.pi ^ 2 / 24) : ℝ) :
        ℂ) := by
    push_cast at h ⊢; linear_combination 2 * h
  exact_mod_cast h'

/-! ### The reflection family -/

theorem i8_cpow_half_add {r : ℝ} (hr : 0 < r) (a : ℂ) :
    (r : ℂ) ^ ((1 : ℂ) / 2 + a) = (√r : ℂ) * exp (((Real.log r : ℝ) : ℂ) * a) := by
  have h0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  rw [cpow_add _ _ h0, Real.sqrt_eq_rpow, ofReal_cpow hr.le, cpow_def_of_ne_zero h0 a,
    ofReal_log hr.le]
  push_cast
  ring_nf

/-- `F(ε) = ∫₀¹ x ^ (1/2 + ε) (1 - x) ^ (1/2 - ε) dx = B(3/2 + ε, 3/2 - ε)`. -/
noncomputable def i8Fm (ε : ℂ) : ℂ :=
  ∫ x in Ioo (0 : ℝ) 1, (x : ℂ) ^ ((3 / 2 + ε) - 1) * ((1 - x : ℝ) : ℂ) ^ ((3 / 2 - ε) - 1)

/-- The coefficients `√(x (1 - x)) (log x - log (1 - x))ᵏ / k!` of the reflection family. -/
noncomputable def i8FmC (x : ℝ) (k : ℕ) : ℂ :=
  (√x * √(1 - x) : ℝ) * ((Real.log x - Real.log (1 - x) : ℝ) : ℂ) ^ k / (k ! : ℂ)

theorem i8Fm_integrand_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (ε : ℂ) :
    (x : ℂ) ^ ((3 / 2 + ε) - 1) * ((1 - x : ℝ) : ℂ) ^ ((3 / 2 - ε) - 1) =
      (√x * √(1 - x) : ℝ) * exp (((Real.log x - Real.log (1 - x) : ℝ) : ℂ) * ε) := by
  rw [show (3 / 2 + ε) - 1 = (1 : ℂ) / 2 + ε by ring,
    show (3 / 2 - ε) - 1 = (1 : ℂ) / 2 + -ε by ring, i8_cpow_half_add hx.1,
    i8_cpow_half_add (by linarith [hx.2] : (0 : ℝ) < 1 - x)]
  push_cast
  rw [mul_mul_mul_comm, ← exp_add]
  congr 2
  ring

theorem i8_norm_cpow_le_one {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(x : ℂ) ^ s‖ ≤ 1 := by
  rw [norm_cpow_eq_rpow_re_of_pos h0]
  exact Real.rpow_le_one h0.le h1 hs

theorem i8Jet_Fm : I13Jet i8Fm fun k => ∫ x in Ioo (0 : ℝ) 1, i8FmC x k := by
  refine i8Jet_integral (R := 1 / 2) (ρ := 1 / 4) (M := fun _ => 1) measurableSet_Ioo
    (by norm_num) (by norm_num) (integrable_const _) (fun x hx => ?_) (fun ε hε => ?_)
    (fun x hx ε hε => ?_) (fun x hx k => ?_)
  · have h1 : ((1 - x : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith [hx.2])
    have h0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.1.ne'
    exact ((Differentiable.const_cpow (by fun_prop) (Or.inl h0)).mul
      (Differentiable.const_cpow (by fun_prop) (Or.inl h1))).differentiableOn
  · rw [mem_ball, dist_zero_right] at hε
    have hr := abs_re_le_norm ε
    exact (i9_integrableOn_beta (u := 3 / 2 + ε) (v := 3 / 2 - ε)
      (by rw [add_re]; norm_num; linarith [abs_le.mp (hr.trans hε.le)])
      (by rw [sub_re]; norm_num; linarith [abs_le.mp (hr.trans hε.le)])).aestronglyMeasurable
  · have hr := abs_le.mp ((abs_re_le_norm ε).trans_eq hε)
    rw [norm_mul]
    calc _ ≤ (1 : ℝ) * 1 := mul_le_mul
          (i8_norm_cpow_le_one hx.1 hx.2.le (by rw [sub_re, add_re]; norm_num; linarith))
          (i8_norm_cpow_le_one (by linarith [hx.2]) (by linarith [hx.1])
            (by rw [sub_re, sub_re]; norm_num; linarith)) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  · rw [(((i13Jet_exp ((Real.log x - Real.log (1 - x) : ℝ) : ℂ)).const_mul
      (((√x * √(1 - x) : ℝ) : ℂ))).congr
      (funext fun ε => (i8Fm_integrand_eq hx ε).symm)).dsl_eq k]
    unfold i8FmC
    ring

/-- **Reflection**: `2 cos (πε) F(ε) = π (1/4 - ε²)`. -/
theorem i8_cos_mul_Fm {ε : ℂ} (hε : ‖ε‖ < 1 / 2) :
    (exp ((Real.pi * I) * ε) + exp ((-(Real.pi * I)) * ε)) * i8Fm ε =
      Real.pi * (1 / 4 - ε ^ 2) := by
  have hr := abs_lt.mp ((abs_re_le_norm ε).trans_lt hε)
  have hp : 0 < (1 / 2 + ε).re := by rw [add_re]; norm_num; linarith
  have hm : 0 < (1 / 2 - ε).re := by rw [sub_re]; norm_num; linarith
  have hB := i9_integral_beta (u := 3 / 2 + ε) (v := 3 / 2 - ε)
    (by rw [add_re]; norm_num; linarith) (by rw [sub_re]; norm_num; linarith)
  have hR := Complex.Gamma_mul_Gamma_one_sub (1 / 2 + ε)
  rw [show (1 : ℂ) - (1 / 2 + ε) = 1 / 2 - ε by ring,
    show (Real.pi : ℂ) * (1 / 2 + ε) = Real.pi * ε + Real.pi / 2 by ring,
    Complex.sin_add_pi_div_two] at hR
  have g1 := Gamma_ne_zero_of_re_pos hp
  have g2 := Gamma_ne_zero_of_re_pos hm
  have hc : Complex.cos (Real.pi * ε) ≠ 0 := fun h => by
    rw [h, div_zero] at hR; exact mul_ne_zero g1 g2 hR
  have hcos : exp ((Real.pi * I) * ε) + exp ((-(Real.pi * I)) * ε) =
      2 * Complex.cos (Real.pi * ε) := by
    rw [Complex.two_cos]; ring_nf
  have g3 : Gamma (3 / 2 + ε + (3 / 2 - ε)) = 2 := by
    rw [show (3 : ℂ) / 2 + ε + (3 / 2 - ε) = 2 + 1 by ring, Gamma_add_one _ two_ne_zero,
      show (2 : ℂ) = 1 + 1 by norm_num, Gamma_add_one _ one_ne_zero, Gamma_one]
    norm_num
  rw [hcos, i8Fm, hB, i9Beta, g3, show (3 : ℂ) / 2 + ε = (1 / 2 + ε) + 1 by ring,
    show (3 : ℂ) / 2 - ε = (1 / 2 - ε) + 1 by ring,
    Gamma_add_one _ (fun h => by have := congr_arg re h; simp at this; linarith),
    Gamma_add_one _ (fun h => by have := congr_arg re h; simp at this; linarith)]
  rw [eq_div_iff hc] at hR
  linear_combination (1 / 4 - ε ^ 2) * hR

/-- `∫₀¹ √(x (1 - x)) (log x - log (1 - x))² / 2 dx = -π/2 + π³/16`. -/
theorem i8_integral_FmC_two :
    ∫ x in Ioo (0 : ℝ) 1, √x * √(1 - x) * (Real.log x - Real.log (1 - x)) ^ 2 / 2 =
      -Real.pi / 2 + Real.pi ^ 3 / 16 := by
  have J := (((i13Jet_exp (Real.pi * I)).add (i13Jet_exp (-(Real.pi * I)))).mul'
    i8Jet_Fm).congr_ball
    (g := fun ε => (Real.pi : ℂ) * (1 / 4 - ε ^ 2)) (r := 1 / 2) (by norm_num) fun ε hε =>
      i8_cos_mul_Fm (by rwa [mem_ball, dist_zero_right] at hε)
  have K := ((i13Jet_const ((Real.pi : ℂ) / 4)).sub
    ((i13Jet_id.mul' i13Jet_id).const_mul (Real.pi : ℂ))).congr (g := fun ε =>
      (Real.pi : ℂ) * (1 / 4 - ε ^ 2)) (funext fun ε => by ring)
  have e : ∀ k, i13Cauchy (fun k => (Real.pi * I) ^ k / (k ! : ℂ) +
      (-(Real.pi * I)) ^ k / (k ! : ℂ)) (fun k => ∫ x in Ioo (0 : ℝ) 1, i8FmC x k) k =
      (if k = 0 then (Real.pi : ℂ) / 4 else 0) - (Real.pi : ℂ) *
        i13Cauchy (fun k => if k = 1 then 1 else 0) (fun k => if k = 1 then 1 else 0) k :=
    fun k => (J.dsl_eq k).symm.trans (K.dsl_eq k)
  have e0 := e 0
  have e2 := e 2
  simp only [i13Cauchy, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.sub_self, Nat.sub_zero] at e0 e2
  norm_num at e0 e2
  have hI : I ^ 2 = -1 := I_sq
  have hF : ∀ k, ∫ x in Ioo (0 : ℝ) 1, i8FmC x k = ((∫ x in Ioo (0 : ℝ) 1,
      √x * √(1 - x) * (Real.log x - Real.log (1 - x)) ^ k / (k ! : ℝ) : ℝ) : ℂ) := fun k =>
    i8_cast_integral fun x _ => by unfold i8FmC; push_cast; ring
  rw [hF] at e0
  rw [hF, hF] at e2
  set A0 := ∫ x in Ioo (0 : ℝ) 1,
    √x * √(1 - x) * (Real.log x - Real.log (1 - x)) ^ 0 / ((0 ! : ℕ) : ℝ)
  set A2 := ∫ x in Ioo (0 : ℝ) 1,
    √x * √(1 - x) * (Real.log x - Real.log (1 - x)) ^ 2 / ((2 ! : ℕ) : ℝ)
  have h2 : (A2 : ℂ) = ((-Real.pi / 2 + Real.pi ^ 3 / 16 : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, hI] at e2
    linear_combination e2 / 2 + (Real.pi : ℂ) ^ 2 / 4 * e0
  have h2' : A2 = -Real.pi / 2 + Real.pi ^ 3 / 16 := by exact_mod_cast h2
  rw [← h2']
  simp [A2, Nat.factorial]

/-! ### The mixed moment -/

theorem i8_integral_sq_subst_real (G : ℝ → ℝ) :
    ∫ z in Ioo (0 : ℝ) 1, G (z ^ 2) = ∫ x in Ioo (0 : ℝ) 1, G x / (2 * √x) := by
  have h := i8_integral_sq_subst (fun x => (G x : ℂ))
  rw [i8_cast_integral (f := fun z => G (z ^ 2)) (fun z _ => rfl),
    i8_cast_integral (f := fun x => G x / (2 * √x)) (fun x _ => by push_cast; rfl)] at h
  exact_mod_cast h

theorem i8_integral_symm (f : ℝ → ℝ) :
    ∫ x in Ioo (0 : ℝ) 1, f x = ∫ x in Ioo (0 : ℝ) 1, f (1 - x) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_sub_left]
  norm_num

theorem i8_abs_sqrt_mul_log_le {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1) : |√x * Real.log x| ≤ 2 := by
  have h := Real.abs_log_mul_self_rpow_lt x (1 / 2) h0 h1 (by norm_num)
  rw [Real.sqrt_eq_rpow, mul_comm]
  norm_num at h ⊢
  exact h.le

theorem i8_abs_sqrt_mul_log_sq_le {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1) :
    |√x * Real.log x ^ 2| ≤ 16 := by
  have h := Real.abs_log_mul_self_rpow_lt x (1 / 4) h0 h1 (by norm_num)
  have e : √x * Real.log x ^ 2 = (Real.log x * x ^ ((1 : ℝ) / 4)) ^ 2 := by
    rw [mul_pow, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 4)), ← Real.rpow_mul h0.le,
      Real.sqrt_eq_rpow]
    norm_num
    ring
  rw [e, abs_pow, abs_mul]
  norm_num at h
  have ha := mul_nonneg (abs_nonneg (Real.log x)) (abs_nonneg (x ^ ((1 : ℝ) / 4)))
  nlinarith

theorem i8_integrableOn_bdd {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ x ∈ Ioo (0 : ℝ) 1, |f x| ≤ C) : IntegrableOn f (Ioo (0 : ℝ) 1) :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioo fun x hx => by
      rw [Real.norm_eq_abs]; exact hb x hx)

theorem i8_mem_one_sub {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < 1 - x ∧ 1 - x ≤ 1 :=
  ⟨by linarith [hx.2], by linarith [hx.1]⟩

theorem i8_sqrt_le_one {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : |√x| ≤ 1 := by
  rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_one]; exact hx.2.le

theorem i8_div_two_sqrt {x : ℝ} (hx : 0 < x) : x / (2 * √x) = √x / 2 := by
  have hs := Real.sqrt_pos.mpr hx
  rw [div_eq_div_iff (by positivity) two_ne_zero]
  linear_combination -2 * Real.mul_self_sqrt hx.le

/-- `Q = ∫₀¹ √(x (1 - x)) log² (1 - x) dx = π (l²/2 - l/4 - 5/16 + π²/24)`. -/
theorem i8_integral_Q1 :
    ∫ x in Ioo (0 : ℝ) 1, √x * √(1 - x) * Real.log (1 - x) ^ 2 =
      Real.pi * (Real.log 2 ^ 2 / 2 - Real.log 2 / 4 - 5 / 16 + Real.pi ^ 2 / 24) := by
  have h := i8_integral_wL2z2
  have e := i8_integral_sq_subst_real (fun x => √(1 - x) * Real.log (1 - x) ^ 2 * x)
  rw [e] at h
  rw [show (∫ x in Ioo (0 : ℝ) 1, √x * √(1 - x) * Real.log (1 - x) ^ 2) =
    2 * ∫ x in Ioo (0 : ℝ) 1, √(1 - x) * Real.log (1 - x) ^ 2 * x / (2 * √x) by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      rw [show √(1 - x) * Real.log (1 - x) ^ 2 * x / (2 * √x) =
        √(1 - x) * Real.log (1 - x) ^ 2 * (x / (2 * √x)) by ring, i8_div_two_sqrt hx.1]
      ring, h]
  ring

/-- `Y = ∫₀¹ √(x (1 - x)) log x log (1 - x) dx = π (l²/2 - l/4 + 3/16) - π³/48`. -/
theorem i8_integral_Y :
    ∫ x in Ioo (0 : ℝ) 1, √x * √(1 - x) * (Real.log x * Real.log (1 - x)) =
      Real.pi * (Real.log 2 ^ 2 / 2 - Real.log 2 / 4 + 3 / 16) - Real.pi ^ 3 / 48 := by
  have hm : ∀ f : ℝ → ℝ, Measurable f → Measurable fun x => √x * √(1 - x) * f x :=
    fun f hf => by fun_prop
  have i0 : IntegrableOn (fun x => √x * √(1 - x) * Real.log x ^ 2) (Ioo (0 : ℝ) 1) :=
    i8_integrableOn_bdd (hm _ (by fun_prop)) (C := 16 * 1) fun x hx => by
      rw [show √x * √(1 - x) * Real.log x ^ 2 = (√x * Real.log x ^ 2) * √(1 - x) by ring,
        abs_mul]
      exact mul_le_mul (i8_abs_sqrt_mul_log_sq_le hx.1 hx.2.le)
        (by rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_one]; linarith [hx.1])
        (abs_nonneg _) (by norm_num)
  have i1 : IntegrableOn (fun x => √x * √(1 - x) * Real.log (1 - x) ^ 2) (Ioo (0 : ℝ) 1) :=
    i8_integrableOn_bdd (hm _ (by fun_prop)) (C := 1 * 16) fun x hx => by
      rw [mul_assoc, abs_mul]
      exact mul_le_mul (i8_sqrt_le_one hx) (i8_abs_sqrt_mul_log_sq_le (i8_mem_one_sub hx).1
        (i8_mem_one_sub hx).2) (abs_nonneg _) zero_le_one
  have i01 : IntegrableOn (fun x => √x * √(1 - x) * (Real.log x * Real.log (1 - x)))
      (Ioo (0 : ℝ) 1) :=
    i8_integrableOn_bdd (hm _ (by fun_prop)) (C := 2 * 2) fun x hx => by
      rw [show √x * √(1 - x) * (Real.log x * Real.log (1 - x)) =
        (√x * Real.log x) * (√(1 - x) * Real.log (1 - x)) by ring, abs_mul]
      exact mul_le_mul (i8_abs_sqrt_mul_log_le hx.1 hx.2.le) (i8_abs_sqrt_mul_log_le
        (i8_mem_one_sub hx).1 (i8_mem_one_sub hx).2) (abs_nonneg _) (by norm_num)
  have hsym : ∫ x in Ioo (0 : ℝ) 1, √x * √(1 - x) * Real.log x ^ 2 =
      ∫ x in Ioo (0 : ℝ) 1, √x * √(1 - x) * Real.log (1 - x) ^ 2 := by
    rw [i8_integral_symm]
    refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
    simp only [sub_sub_cancel]
    ring
  have hF := i8_integral_FmC_two
  set A := fun x : ℝ => √x * √(1 - x) * Real.log x ^ 2
  set B := fun x : ℝ => √x * √(1 - x) * Real.log (1 - x) ^ 2
  set C := fun x : ℝ => √x * √(1 - x) * (Real.log x * Real.log (1 - x))
  have hs := integral_sub (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (f := fun x => A x / 2 + B x / 2) (g := C) (by exact (i0.div_const 2).add (i1.div_const 2))
    i01
  have ha := integral_add (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (f := fun x => A x / 2) (g := fun x => B x / 2) (i0.div_const 2) (i1.div_const 2)
  rw [setIntegral_congr_fun measurableSet_Ioo (g := fun x => A x / 2 + B x / 2 - C x)
    fun x _ => by simp only [A, B, C]; ring, hs, ha, integral_div, integral_div] at hF
  simp only [A, B, C] at hF
  rw [hsym, i8_integral_Q1] at hF
  linarith

/-- **The mixed moment**
`∫₀¹ √(1 - z²) log (1 - z²) z² log z dz = π (l²/8 - l/16 + 3/64) - π³/192`. -/
theorem i8_integral_wLz2log :
    ∫ z in Ioo (0 : ℝ) 1, √(1 - z ^ 2) * Real.log (1 - z ^ 2) * z ^ 2 * Real.log z =
      Real.pi * (Real.log 2 ^ 2 / 8 - Real.log 2 / 16 + 3 / 64) - Real.pi ^ 3 / 192 := by
  have e := i8_integral_sq_subst_real
    (fun x => √(1 - x) * Real.log (1 - x) * x * (Real.log x / 2))
  rw [setIntegral_congr_fun measurableSet_Ioo (g := fun z =>
      √(1 - z ^ 2) * Real.log (1 - z ^ 2) * z ^ 2 * (Real.log (z ^ 2) / 2)) fun z hz => by
      simp only [Real.log_pow]; push_cast; ring, e,
    setIntegral_congr_fun measurableSet_Ioo (g := fun x =>
      (√x * √(1 - x) * (Real.log x * Real.log (1 - x))) / 4) fun x hx => by
      rw [show √(1 - x) * Real.log (1 - x) * x * (Real.log x / 2) / (2 * √x) =
        √(1 - x) * Real.log (1 - x) * (Real.log x / 2) * (x / (2 * √x)) by ring,
        i8_div_two_sqrt hx.1]
      ring,
    integral_div, i8_integral_Y]
  ring

end QED.ThreeLoopD
