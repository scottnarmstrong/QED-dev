/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13RJet
public import QED.ThreeLoopD.SetDMastersI13RemCoeff

/-!
# Set (d), master `I₁₃`: the pointwise Taylor coefficients of the integrands of `Rem`

For `t > 0` the integrands `h₁(t, ·) = t ^ (1 - ε) b_ε(t)²` and `h₂(t, ·) = h₁(t, ·) - Asym(·, t)`
of `QED.ThreeLoopD.i13Rem` have jets (`QED.ThreeLoopD.I13Jet`) built from

* the bubble, `Dʲ b(t)(0) = βⱼ(t) = ∫₀¹ (-L)ʲ / j! dx`, `L = log (1 + x(1 - x) t)`
  (`QED.ThreeLoopD.i13Jet_bub`);
* the powers `t ^ (a + b ε) = t ^ a e ^ (b ε log t)` (`QED.ThreeLoopD.i13Jet_tpow`);
* `G = Γ(1 - ε)² / Γ(1 - 2ε)`, whose first six coefficients are those of
  `QED.ThreeLoopD.i13Gp` (`QED.ThreeLoopD.i13Dsl_G`), and the rational coefficients of the
  large-`t` expansion.

## Main results

* `QED.ThreeLoopD.i13Jet_remInt1`, `QED.ThreeLoopD.i13Jet_remInt2`.
* `QED.ThreeLoopD.i13Dsl_remInt1_one`, `QED.ThreeLoopD.i13Dsl_asym_one`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Filter Topology QED.Polylog
open scoped Nat

namespace QED.ThreeLoopD

/-- The Cauchy product of two coefficient sequences. -/
noncomputable def i13Cauchy (a b : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (k + 1), a i * b (k - i)

theorem I13Jet.mul' {f g : ℂ → ℂ} {a b : ℕ → ℂ} (hf : I13Jet f a) (hg : I13Jet g b) :
    I13Jet (fun ε => f ε * g ε) (i13Cauchy a b) :=
  hf.mul hg

theorem i13Jet_id : I13Jet (fun ε => ε) fun k => if k = 1 then 1 else 0 := by
  refine ⟨1, one_pos, differentiableOn_id, fun k => ?_⟩
  refine i13Dsl_zero_eq_of_expansion (f := fun ε : ℂ => ε)
    (a := fun k => if k = 1 then 1 else 0) (n := k + 2) (g := fun _ => 0) one_pos
    differentiableOn_id
    continuousAt_const (fun ε _ => ?_) k (by omega)
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp

/-! ### The bubble -/

/-- `βₖ(t) = ∫₀¹ (-log (1 + x(1 - x) t))ᵏ / k! dx`, the coefficients of the bubble. -/
noncomputable def i13BubC (t : ℝ) (k : ℕ) : ℂ :=
  ∫ x in Ioo (0 : ℝ) 1, ((-Real.log (1 + x * (1 - x) * t) : ℝ) : ℂ) ^ k / (k ! : ℂ)

theorem i13_cpow_neg_eq_exp {r : ℝ} (hr : 0 < r) (ε : ℂ) :
    ((r : ℝ) : ℂ) ^ (-ε) = exp (((-Real.log r : ℝ) : ℂ) * ε) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr.ne'), ← ofReal_log hr.le]
  congr 1
  push_cast
  ring

theorem i13Jet_bub {t : ℝ} (ht : 0 ≤ t) : I13Jet (fun ε => i13Bub ε t) (i13BubC t) := by
  refine ⟨1, one_pos, (differentiable_i13Bub ht).differentiableOn, fun k => ?_⟩
  have H := hasTruncLaurent_integral_i13Dsl (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (h := fun x ε => ((1 + x * (1 - x) * t : ℝ) : ℂ) ^ (-ε)) (R := 2) (ρ := 1)
    (M := fun _ => (1 + t / 4) ^ (1 : ℝ)) one_pos one_lt_two (integrable_const _)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun x hx =>
      (Differentiable.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.mpr
        (i13_base_pos (Ioo_subset_Icc_self hx) ht).ne'))).differentiableOn)
    (fun ε _ => (integrableOn_i13Bub_integrand ε ht).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun x hx ε hε => by
      have := norm_i13Bub_integrand_le ε (Ioo_subset_Icc_self hx) ht
      rwa [hε] at this) (k + 1)
  refine (i13Dsl_zero_eq_of_hasTruncLaurent one_pos (differentiable_i13Bub ht).differentiableOn
    H k (Nat.lt_succ_self k)).trans ?_
  unfold i13BubC
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have hr := i13_base_pos (Ioo_subset_Icc_self hx) ht
  obtain ⟨-, -, -, hv⟩ := (i13Jet_exp ((-Real.log (1 + x * (1 - x) * t) : ℝ) : ℂ)).congr
    (funext fun ε => (i13_cpow_neg_eq_exp hr ε).symm)
  exact hv k

theorem I13Jet.congr_ball {f g : ℂ → ℂ} {a : ℕ → ℂ} (hf : I13Jet f a) {r : ℝ} (hr : 0 < r)
    (h : ∀ ε ∈ ball (0 : ℂ) r, f ε = g ε) : I13Jet g a := by
  obtain ⟨R, hR, hRr, hd, hk⟩ := hf.restrict hr
  have hg : DifferentiableOn ℂ g (ball 0 R) := hd.congr fun ε hε =>
    (h ε (ball_subset_ball hRr hε)).symm
  have key : ∀ k, ∀ ε ∈ ball (0 : ℂ) R, i13Dsl f k ε = i13Dsl g k ε := by
    intro k
    induction k with
    | zero => exact fun ε hε => h ε (ball_subset_ball hRr hε)
    | succ k ih =>
      refine i13_eqOn_of_mul hR (differentiableOn_i13Dsl hR hd (k + 1)).continuousOn
        (differentiableOn_i13Dsl hR hg (k + 1)).continuousOn fun ε hε => ?_
      have e1 := i13Dsl_step f k ε
      have e2 := i13Dsl_step g k ε
      rw [ih ε hε, ih 0 (mem_ball_self hR)] at e1
      linear_combination e2 - e1
  exact ⟨R, hR, hg, fun k => (key k 0 (mem_ball_self hR)).symm.trans (hk k)⟩

/-! ### Powers of `t` -/

/-- The coefficients `t ^ a (b log t)ᵏ / k!` of `t ^ (a + b ε)`. -/
noncomputable def i13TpC (t : ℝ) (a b : ℂ) (k : ℕ) : ℂ :=
  (t : ℂ) ^ a * ((b * (Real.log t : ℂ)) ^ k / (k ! : ℂ))

theorem i13Jet_tpow {t : ℝ} (ht : 0 < t) (e : ℂ → ℂ) (a b : ℂ) (he : ∀ ε, e ε = a + b * ε) :
    I13Jet (fun ε => (t : ℂ) ^ e ε) (i13TpC t a b) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  refine ((i13Jet_exp (b * (Real.log t : ℂ))).const_mul ((t : ℂ) ^ a)).congr (funext fun ε => ?_)
  rw [he, cpow_add _ _ ht0, cpow_def_of_ne_zero ht0 (b * ε), ← ofReal_log ht.le]
  congr 2
  ring

/-! ### `G` and the coefficients of the large-`t` expansion -/

/-- The Taylor coefficients of `G` (those of `QED.ThreeLoopD.i13Gp` for `k < 6`). -/
noncomputable def i13GC (k : ℕ) : ℂ := i13Dsl i13G k 0

/-- The coefficients of `QED.ThreeLoopD.i13Gp`. -/
noncomputable def i13GpC : ℕ → ℂ
  | 0 => 1
  | 1 => 0
  | 2 => -1 / 6 * (Real.pi : ℂ) ^ 2
  | 3 => -2 * (zeta3 : ℂ)
  | 4 => -1 / 40 * (Real.pi : ℂ) ^ 4
  | 5 => 1 / 3 * (Real.pi : ℂ) ^ 2 * (zeta3 : ℂ) - 6 * (zeta5 : ℂ)
  | _ => 0

theorem differentiableOn_i13G : DifferentiableOn ℂ i13G (ball 0 (1 / 8)) := fun ε hε => by
  rw [mem_ball, dist_zero_right] at hε
  exact (differentiableAt_i13G (by linarith)).differentiableWithinAt

theorem analyticAt_i13dG : AnalyticAt ℂ i13dG 0 := by
  have hV : AnalyticAt ℂ i13V 0 := by
    have h1 := analyticAt_logGammaRem_mul (-1)
    have h2 := analyticAt_logGammaRem_mul (-2)
    unfold i13V
    fun_prop
  have hX : AnalyticAt ℂ i13X 0 := by unfold i13X; fun_prop
  have hEG : AnalyticAt ℂ (fun ε => QED.DimReg.expRem3 (ε ^ 2 * i13X ε)) 0 :=
    QED.DimReg.analyticAt_expRem3.comp_of_eq (by fun_prop) (by simp)
  unfold i13dG i13dGp
  fun_prop

theorem i13GC_eq : ∀ k < 6, i13GC k = i13GpC k := by
  refine i13Dsl_zero_eq_of_expansion (by norm_num) differentiableOn_i13G
    analyticAt_i13dG.continuousAt fun ε hε => ?_
  rw [mem_ball, dist_zero_right] at hε
  rw [i13G_eq hε, i13G_trunc]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, i13GpC, i13Gp]
  ring

theorem i13Jet_G : I13Jet i13G i13GC := I13Jet.of_differentiableOn (by norm_num)
  differentiableOn_i13G

/-- The coefficients of `α₀ = G / (1 - 2ε)`. -/
noncomputable def i13A0C : ℕ → ℂ := i13Cauchy i13GC fun k => 2 ^ k

/-- The coefficients of `α₁ = 2G`. -/
noncomputable def i13A1C (k : ℕ) : ℂ := 2 * i13GC k

/-- The coefficients of `α₂ = -2(1 + 2ε) G`. -/
noncomputable def i13A2C (k : ℕ) : ℂ :=
  -2 * i13GC k + -4 * i13Cauchy (fun k => if k = 1 then 1 else 0) i13GC k

/-- The coefficients of `β₀ = 2 / (ε - 1)`. -/
noncomputable def i13B0C (k : ℕ) : ℂ := -2 * 1 ^ k

/-- The coefficients of `β₁ = 4 / ((ε - 1)(ε - 2))`. -/
noncomputable def i13B1C (k : ℕ) : ℂ := 4 * 1 ^ k + -2 * (1 / 2) ^ k

theorem i13Jet_Al0 : I13Jet i13Al0 i13A0C :=
  (i13Jet_G.mul' (by simpa using i13Jet_geom 2)).congr (funext fun ε => by unfold i13Al0; ring)

theorem i13Jet_Al1 : I13Jet i13Al1 i13A1C :=
  (i13Jet_G.const_mul 2).congr (funext fun ε => by unfold i13Al1; ring)

theorem i13Jet_Al2 : I13Jet i13Al2 i13A2C :=
  (i13Jet_G.lin (i13Jet_id.mul' i13Jet_G) (-2) (-4)).congr
    (funext fun ε => by unfold i13Al2; ring)

theorem i13Jet_Be0 : I13Jet i13Be0 i13B0C :=
  ((i13Jet_geom 1).const_mul (-2)).congr (funext fun ε => by
    unfold i13Be0
    rw [show ε - 1 = -(1 - 1 * ε) by ring, div_neg]
    ring)

theorem i13Jet_Be1 : I13Jet i13Be1 i13B1C := by
  refine ((i13Jet_geom 1).lin (i13Jet_geom (1 / 2)) 4 (-2)).congr_ball (r := 1 / 2)
    (by norm_num) fun ε hε => ?_
  rw [mem_ball, dist_zero_right] at hε
  have h1 : ε - 1 ≠ 0 := fun h => by
    have : ‖ε‖ = 1 := by rw [show ε = 1 by linear_combination h]; simp
    linarith
  have h2 : ε - 2 ≠ 0 := fun h => by
    have : ‖ε‖ = 2 := by rw [show ε = 2 by linear_combination h]; simp
    linarith
  have h1' : 1 - 1 * ε ≠ 0 := fun h => h1 (by linear_combination -h)
  have h2' : 1 - 1 / 2 * ε ≠ 0 := fun h => h2 (by linear_combination -2 * h)
  have h3 : 1 - ε ≠ 0 := fun h => h1 (by linear_combination -h)
  have h4 : 2 - ε ≠ 0 := fun h => h2 (by linear_combination -h)
  unfold i13Be1
  field_simp
  ring

/-! ### The jets of the integrands -/

/-- The coefficients of `Asym(·, t)`. -/
noncomputable def i13AsymC (t : ℝ) (k : ℕ) : ℂ :=
  i13Cauchy (i13Cauchy i13A0C i13A0C) (i13TpC t 1 (-3)) k +
    i13Cauchy (fun k => 2 * i13Cauchy i13A0C i13A1C k) (i13TpC t 0 (-3)) k +
    i13Cauchy (fun k => 2 * i13Cauchy i13A0C i13B0C k) (i13TpC t 0 (-2)) k +
    i13Cauchy (fun k => i13Cauchy i13A1C i13A1C k + 2 * i13Cauchy i13A0C i13A2C k)
      (i13TpC t (-1) (-3)) k +
    i13Cauchy (fun k => 2 * (i13Cauchy i13A1C i13B0C k + i13Cauchy i13A0C i13B1C k))
      (i13TpC t (-1) (-2)) k +
    i13Cauchy (i13Cauchy i13B0C i13B0C) (i13TpC t (-1) (-1)) k

theorem i13Jet_asym {t : ℝ} (ht : 0 < t) : I13Jet (fun ε => i13Asym ε t) (i13AsymC t) := by
  have J1 := (i13Jet_Al0.mul' i13Jet_Al0).mul' (i13Jet_tpow ht (fun ε => 1 - 3 * ε) 1 (-3)
    fun ε => by ring)
  have J2 := ((i13Jet_Al0.mul' i13Jet_Al1).const_mul 2).mul'
    (i13Jet_tpow ht (fun ε => -3 * ε) 0 (-3) fun ε => by ring)
  have J3 := ((i13Jet_Al0.mul' i13Jet_Be0).const_mul 2).mul'
    (i13Jet_tpow ht (fun ε => -2 * ε) 0 (-2) fun ε => by ring)
  have J4 := ((i13Jet_Al1.mul' i13Jet_Al1).add ((i13Jet_Al0.mul' i13Jet_Al2).const_mul 2)).mul'
    (i13Jet_tpow ht (fun ε => -1 - 3 * ε) (-1) (-3) fun ε => by ring)
  have J5 := (((i13Jet_Al1.mul' i13Jet_Be0).add (i13Jet_Al0.mul' i13Jet_Be1)).const_mul 2).mul'
    (i13Jet_tpow ht (fun ε => -1 - 2 * ε) (-1) (-2) fun ε => by ring)
  have J6 := (i13Jet_Be0.mul' i13Jet_Be0).mul'
    (i13Jet_tpow ht (fun ε => -1 - ε) (-1) (-1) fun ε => by ring)
  refine ((((((J1.add J2).add J3).add J4).add J5).add J6).congr (funext fun ε => ?_))
  unfold i13Asym
  ring

/-- The coefficients of `h₁(t, ·) = t ^ (1 - ε) b_ε(t)²`. -/
noncomputable def i13R1C (t : ℝ) : ℕ → ℂ :=
  i13Cauchy (i13TpC t 1 (-1)) (i13Cauchy (i13BubC t) (i13BubC t))

theorem i13Jet_remInt1 {t : ℝ} (ht : 0 < t) : I13Jet (i13RemInt1 t) (i13R1C t) :=
  ((i13Jet_tpow ht (fun ε => 1 - ε) 1 (-1) fun ε => by ring).mul'
    ((i13Jet_bub ht.le).mul' (i13Jet_bub ht.le))).congr (funext fun ε => by
      unfold i13RemInt1; ring)

theorem i13Jet_remInt2 {t : ℝ} (ht : 0 < t) :
    I13Jet (i13RemInt2 t) fun k => i13R1C t k - i13AsymC t k :=
  ((i13Jet_remInt1 ht).sub (i13Jet_asym ht)).congr (funext fun ε => by
    unfold i13RemInt2 i13RemInt1; rfl)

theorem i13Dsl_remInt1 {t : ℝ} (ht : 0 < t) (k : ℕ) : i13Dsl (i13RemInt1 t) k 0 = i13R1C t k := by
  obtain ⟨-, -, -, h⟩ := i13Jet_remInt1 ht
  exact h k

theorem i13Dsl_remInt2 {t : ℝ} (ht : 0 < t) (k : ℕ) :
    i13Dsl (i13RemInt2 t) k 0 = i13R1C t k - i13AsymC t k := by
  obtain ⟨-, -, -, h⟩ := i13Jet_remInt2 ht
  exact h k

/-! ### The first coefficient -/

theorem i13BubC_zero (t : ℝ) : i13BubC t 0 = 1 := by
  unfold i13BubC
  simp [Real.volume_real_Ioo_of_le zero_le_one]

theorem i13GC_zero : i13GC 0 = 1 := i13GC_eq 0 (by norm_num)

theorem i13GC_one : i13GC 1 = 0 := i13GC_eq 1 (by norm_num)

theorem i13R1C_one (t : ℝ) :
    i13R1C t 1 = 2 * t * i13BubC t 1 - t * (Real.log t : ℂ) := by
  simp only [i13R1C, i13Cauchy, i13TpC, Finset.sum_range_succ, Finset.sum_range_zero,
    i13BubC_zero, cpow_one]
  norm_num [i13BubC_zero]
  ring

theorem i13AsymC_one {t : ℝ} (ht : 0 < t) :
    i13AsymC t 1 = t * (4 - 3 * (Real.log t : ℂ)) - 4 - 4 * (Real.log t : ℂ) +
      (-2 + 4 * (Real.log t : ℂ)) / t := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  simp only [i13AsymC, i13A0C, i13A1C, i13A2C, i13B0C, i13B1C, i13Cauchy, i13TpC,
    Finset.sum_range_succ, Finset.sum_range_zero, i13GC_zero, i13GC_one, cpow_one, cpow_zero,
    cpow_neg_one]
  norm_num [i13GC_zero, i13GC_one]
  field_simp
  ring

end QED.ThreeLoopD
