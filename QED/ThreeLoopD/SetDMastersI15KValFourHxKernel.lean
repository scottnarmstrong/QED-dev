/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI15KValThreeHxArg
public import QED.ThreeLoopD.SetDMastersI15KValThreeA
public import QED.Polylog.HPLCalculus
import QED.ThreeLoopD.SetDMastersI15KValTwoA
import QED.Polylog.ParamHPL
import QED.Polylog.ParamHPLLog
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Set (d), master `I₁₅`: the signed slice and its endpoints

The two moving kernels are written without the poles in their offset
parameters, so they extend to zero as the parameter approaches one.
The fixed kernels give the two logarithms at the ends of the slice.
Integration by parts and shuffle multiplication evaluate the signed
slice as a sum of convergent word endpoints.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog.HPL
open scoped Interval

namespace QED.ThreeLoopD

/-- The fixed poles at the ends of the signed slice and its two moving poles. -/
inductive I15Hx4Letter
  | zero | one | pos | neg
  deriving DecidableEq

/-- Signed offsets, with the poles at the negatives of the offsets. -/
noncomputable def i15Hx4Offset (u : ℝ) : I15Hx4Letter → ℝ
  | .zero => 0
  | .one => -1
  | .pos => u / (1 - u)
  | .neg => -(1 - u)⁻¹

/-- Parameter derivatives of the signed offsets. -/
noncomputable def i15Hx4OffsetD (u : ℝ) : I15Hx4Letter → ℝ
  | .zero | .one => 0
  | .pos => ((1 - u) ^ 2)⁻¹
  | .neg => -((1 - u) ^ 2)⁻¹

/-- Signed kernels on the slice, continued in the parameter to `u = 1`. -/
noncomputable def i15Hx4Kernel (u : ℝ) : I15Hx4Letter → ℝ → ℝ
  | .zero, x => x⁻¹
  | .one, x => (x - 1)⁻¹
  | .pos, x => (1 - u) / (u + (1 - u) * x)
  | .neg, x => -(1 - u) / (1 - (1 - u) * x)

/-- Derivatives of the signed kernels in the parameter coordinate. -/
noncomputable def i15Hx4KernelD (u : ℝ) : I15Hx4Letter → ℝ → ℝ
  | .zero, _ | .one, _ => 0
  | .pos, x => -((u + (1 - u) * x) ^ 2)⁻¹
  | .neg, x => ((1 - (1 - u) * x) ^ 2)⁻¹

/-- The four singleton words in the signed slice. -/
noncomputable def i15Hx4Log (u : ℝ) : I15Hx4Letter → ℝ → ℝ
  | .zero, x => log x
  | .one, x => log (1 - x)
  | .pos, x => i15HxA u x
  | .neg, x => i15HxB u x

/-- The normalized and signed-offset kernel forms agree off the parameter endpoint. -/
theorem i15Hx4Kernel_eq_inv (a : I15Hx4Letter) {u x : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    i15Hx4Kernel u a x = (x + i15Hx4Offset u a)⁻¹ := by
  have hv := (sub_pos.2 hu.2).ne'
  cases a with
  | zero => simp [i15Hx4Kernel, i15Hx4Offset]
  | one => rfl
  | pos =>
      simp only [i15Hx4Kernel, i15Hx4Offset]
      rw [show x + u / (1 - u) = (u + (1 - u) * x) / (1 - u) by field_simp; ring,
        inv_div]
  | neg =>
      simp only [i15Hx4Kernel, i15Hx4Offset]
      rw [show x + -(1 - u)⁻¹ = -(1 - (1 - u) * x) / (1 - u) by field_simp; ring,
        inv_div, div_neg, neg_div]

/-- The parameter differential of each signed kernel. -/
theorem hasDerivAt_i15Hx4Kernel_param (a : I15Hx4Letter) {u x : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun v => i15Hx4Kernel v a x) (i15Hx4KernelD u a x) u := by
  obtain ⟨hp, hm, _⟩ := i15Hx_den_pos hu ⟨hx.1.le, hx.2.le⟩
  have h₁ : HasDerivAt (fun v : ℝ => 1 - v) (-1) u := by
    simpa using (hasDerivAt_id u).const_sub 1
  have h₂ : HasDerivAt (fun v : ℝ => v + (1 - v) * x) (1 + -1 * x) u :=
    (hasDerivAt_id u).add (h₁.mul_const x)
  have h₃ : HasDerivAt (fun v : ℝ => 1 - (1 - v) * x) (-(-1 * x)) u :=
    (h₁.mul_const x).const_sub 1
  cases a with
  | zero => exact hasDerivAt_const u _
  | one => exact hasDerivAt_const u _
  | pos =>
      refine (h₁.div h₂ hp.ne').congr_deriv ?_
      simp only [i15Hx4KernelD]
      rw [inv_eq_one_div, ← neg_div]
      congr 1
      ring
  | neg =>
      refine (h₁.neg.div h₃ hm.ne').congr_deriv ?_
      simp only [i15Hx4KernelD]
      rw [inv_eq_one_div]
      congr 1
      change (-(-1)) * (1 - (1 - u) * x) - (-(1 - u)) * (-(-1 * x)) = 1
      ring

/-- The slice-coordinate differential of each singleton. -/
theorem hasDerivAt_i15Hx4Log (a : I15Hx4Letter) {u x : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i15Hx4Log u a) (i15Hx4Kernel u a x) x := by
  obtain ⟨hu0, _, _, hx0, hx1, hp, hm, hp'⟩ := i15Hx_pos hu hx
  have h₁ : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  cases a with
  | zero => exact Real.hasDerivAt_log hx0.ne'
  | one =>
      refine (h₁.log hx1.ne').congr_deriv ?_
      simp only [i15Hx4Kernel, neg_div, one_div, ← inv_neg]
      congr 1
      ring
  | pos =>
      have h₂ := (((hasDerivAt_id x).const_mul (1 - u)).div_const u).const_add 1
      refine (h₂.log hp'.ne').congr_deriv ?_
      simp only [i15Hx4Kernel]
      simp only [id_eq, mul_one]
      field_simp [hu0.ne', hp.ne', hp'.ne']
  | neg =>
      have h₃ := ((hasDerivAt_id x).const_mul (1 - u)).const_sub 1
      change HasDerivAt (fun y => log (1 - (1 - u) * y))
        (-(1 - u) / (1 - (1 - u) * x)) x
      simpa only [id_eq, mul_one] using h₃.log hm.ne'

/-- Both normalized moving denominators are at least the parameter. -/
theorem i15Hx4_den_ge {u x : ℝ} (hu : u ≤ 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    u ≤ u + (1 - u) * x ∧ u ≤ 1 - (1 - u) * x := by
  have hv := sub_nonneg.2 hu
  exact ⟨le_add_of_nonneg_right (mul_nonneg hv hx.1), by
    nlinarith [mul_nonneg hv (sub_nonneg.2 hx.2)]⟩

/-- The moving kernels and their parameter derivatives are uniformly bounded for `u ≥ d`. -/
theorem i15Hx4Kernel_bounds {u x d : ℝ} (hd : 0 < d) (hdu : d ≤ u) (hu : u ≤ 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (a : I15Hx4Letter)
    (hz : a ≠ .zero) (ho : a ≠ .one) :
    |i15Hx4Kernel u a x| ≤ d⁻¹ ∧ |i15Hx4KernelD u a x| ≤ (d ^ 2)⁻¹ := by
  obtain ⟨hp, hm⟩ := i15Hx4_den_ge hu hx
  have hu0 := hd.trans_le hdu
  have hpos := hu0.trans_le hp
  have hneg := hu0.trans_le hm
  have hnum : 1 - u ≤ 1 := by linarith
  have hn : 0 ≤ 1 - u := sub_nonneg.2 hu
  have hb {y : ℝ} (hy : u ≤ y) (hy0 : 0 < y) :
      (1 - u) / y ≤ d⁻¹ ∧ (y ^ 2)⁻¹ ≤ (d ^ 2)⁻¹ := by
    refine ⟨?_, inv_anti₀ (by positivity) ?_⟩
    · exact (div_le_div_of_nonneg_right hnum hy0.le).trans
        (by simpa only [one_div] using inv_anti₀ hd (hdu.trans hy))
    · exact pow_le_pow_left₀ hd.le (hdu.trans hy) 2
  cases a with
  | zero => exact (hz rfl).elim
  | one => exact (ho rfl).elim
  | pos =>
      simpa only [i15Hx4Kernel, i15Hx4KernelD, abs_neg,
        abs_of_nonneg (div_nonneg hn hpos.le),
        abs_of_nonneg (by positivity : 0 ≤ ((u + (1 - u) * x) ^ 2)⁻¹)] using hb hp hpos
  | neg =>
      simpa only [i15Hx4Kernel, i15Hx4KernelD, neg_div, abs_neg,
        abs_of_nonneg (div_nonneg hn hneg.le),
        abs_of_nonneg (by positivity : 0 ≤ ((1 - (1 - u) * x) ^ 2)⁻¹)] using hb hm hneg

/-- The offset derivatives on the open parameter interval. -/
theorem hasDerivAt_i15Hx4Offset (a : I15Hx4Letter) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun v => i15Hx4Offset v a) (i15Hx4OffsetD u a) u := by
  have h₁ : HasDerivAt (fun v : ℝ => 1 - v) (-1) u := by
    simpa using (hasDerivAt_id u).const_sub 1
  have h₂ := (sub_pos.2 hu.2).ne'
  cases a with
  | zero => exact hasDerivAt_const u _
  | one => exact hasDerivAt_const u _
  | pos =>
      refine ((hasDerivAt_id u).div h₁ h₂).congr_deriv ?_
      rw [i15Hx4OffsetD, inv_eq_one_div]
      congr 1
      simp [id_eq]
  | neg =>
      change HasDerivAt (-(fun v : ℝ => 1 - v)⁻¹) (-((1 - u) ^ 2)⁻¹) u
      simpa only [neg_neg, one_div] using (h₁.inv h₂).neg

/-- Contact coefficient for two adjacent letters in the signed alphabet. -/
noncomputable def i15Hx4Contact (u : ℝ) (a b : I15Hx4Letter) : ℝ :=
  (i15Hx4OffsetD u b - i15Hx4OffsetD u a) / (i15Hx4Offset u b - i15Hx4Offset u a)

/-- Upper transport coefficients at the right endpoint. -/
theorem i15Hx4Upper_at_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (a : I15Hx4Letter) :
    i15Hx4OffsetD u a * (1 + i15Hx4Offset u a)⁻¹ =
      match a with
      | .zero | .one => 0
      | .pos => Letter.one.kernel u
      | .neg => Letter.zero.kernel u + Letter.one.kernel u := by
  have h0 := hu.1.ne'
  have h1 := (sub_pos.2 hu.2).ne'
  have hp : 1 + u / (1 - u) ≠ 0 := (add_pos zero_lt_one
    (div_pos hu.1 (sub_pos.2 hu.2))).ne'
  have hm : 1 + -(1 - u)⁻¹ ≠ 0 := by
    intro h
    field_simp [h1] at h
    exact h0 (by linarith)
  cases a <;> simp [i15Hx4OffsetD, i15Hx4Offset]
  all_goals (field_simp [h0, h1, hp, hm]; ring_nf)
  exact mul_inv_cancel₀ h0

/-- Lower transport coefficients at the left endpoint. -/
theorem i15Hx4Lower_kernel {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (a : I15Hx4Letter) :
    -(i15Hx4OffsetD u a / i15Hx4Offset u a) =
      match a with
      | .zero | .one => 0
      | .pos => -Letter.zero.kernel u - Letter.one.kernel u
      | .neg => -Letter.one.kernel u := by
  cases a <;> simp [i15Hx4OffsetD, i15Hx4Offset]
  all_goals field_simp [hu.1.ne', (sub_pos.2 hu.2).ne']
  ring

/-- Contact coefficients in the harmonic alphabet of the parameter. -/
theorem i15Hx4Contact_kernel {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (a b : I15Hx4Letter) :
    i15Hx4Contact u a b =
      match a, b with
      | .zero, .pos | .pos, .zero | .one, .neg | .neg, .one =>
          Letter.zero.kernel u + Letter.one.kernel u
      | .zero, .neg | .neg, .zero | .one, .pos | .pos, .one => Letter.one.kernel u
      | .pos, .neg | .neg, .pos => Letter.one.kernel u + Letter.negOne.kernel u
      | _, _ => 0 := by
  have h0 := hu.1.ne'
  have h1 := (sub_pos.2 hu.2).ne'
  have hp : 1 + u ≠ 0 := by have := hu.1; positivity
  cases a <;> cases b <;> simp [i15Hx4Contact, i15Hx4OffsetD, i15Hx4Offset]
  all_goals (field_simp [h0, h1, hp]; try ring_nf)
  · exact mul_inv_cancel₀ h0
  · rw [show -1 - u = -(1 + u) by ring, inv_neg]
    linear_combination 2 * (mul_inv_cancel₀ hp)
  · linear_combination 2 * (mul_inv_cancel₀ hp)

/-- A common bound near the left endpoint for each of the nonzero letters. -/
theorem i15Hx4Kernel_left_bound {d b : ℝ} (hd : 0 < d) (hb : b < 1) :
    ∃ K, 0 ≤ K ∧ ∀ u ∈ Icc d 1, ∀ a ≠ I15Hx4Letter.zero,
      ∀ x ∈ Ioc 0 b, |i15Hx4Kernel u a x| ≤ K := by
  refine ⟨max d⁻¹ (1 - b)⁻¹, (inv_nonneg.2 hd.le).trans (le_max_left _ _), ?_⟩
  intro u hu a ha x hx
  have hx1 := hx.2.trans_lt hb
  cases a with
  | zero => exact (ha rfl).elim
  | one =>
      rw [i15Hx4Kernel, show x - 1 = -(1 - x) by ring, inv_neg, abs_neg,
        abs_of_pos (inv_pos.2 (sub_pos.2 hx1))]
      exact (inv_anti₀ (sub_pos.2 hb) (sub_le_sub_left hx.2 _)).trans (le_max_right _ _)
  | pos =>
      exact (i15Hx4Kernel_bounds hd hu.1 hu.2 ⟨hx.1.le, hx1.le⟩ .pos
        (by decide) (by decide)).1.trans (le_max_left _ _)
  | neg =>
      exact (i15Hx4Kernel_bounds hd hu.1 hu.2 ⟨hx.1.le, hx1.le⟩ .neg
        (by decide) (by decide)).1.trans (le_max_left _ _)

private theorem i15Hx4Kernel_continuousOn {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1)
    (a : I15Hx4Letter) : ContinuousOn (i15Hx4Kernel u a) (Ioo 0 1) := by
  have h (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :=
    i15Hx4_den_ge hu.2 ⟨ht.1.le, ht.2.le⟩
  cases a with
  | zero => exact continuousOn_id.inv₀ (fun _ hx => (mem_Ioo.1 hx).1.ne')
  | one =>
      exact (continuousOn_id.sub continuousOn_const).inv₀
        (fun _ hx => (sub_neg.2 (mem_Ioo.1 hx).2).ne)
  | pos =>
      exact continuousOn_const.div
        (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
        (fun t ht => (hu.1.trans_le (h t ht).1).ne')
  | neg =>
      exact continuousOn_const.div
        (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
        (fun t ht => (hu.1.trans_le (h t ht).2).ne')

/-- Words in the signed alphabet with the logarithmic convention at zero. -/
noncomputable def i15Hx4Word (u : ℝ) : List I15Hx4Letter → ℝ → ℝ
  | [], _ => 1
  | a :: w, x =>
      if (a :: w).all (· == .zero) then log x ^ (w.length + 1) / ((w.length + 1).factorial : ℝ)
      else ∫ t in (0 : ℝ)..x, i15Hx4Kernel u a t * i15Hx4Word u w t

private theorem i15Hx4Word_allZero {u x : ℝ} {w : List I15Hx4Letter}
    (hw : w.all (· == .zero) = true) :
    i15Hx4Word u w x = log x ^ w.length / (w.length.factorial : ℝ) := by
  cases w with
  | nil => simp [i15Hx4Word]
  | cons a w => simp only [i15Hx4Word, hw, ↓reduceIte, List.length_cons]

private theorem i15Hx4Word_cons_integral {u : ℝ} {a : I15Hx4Letter} {w : List I15Hx4Letter}
    (hw : (a :: w).all (· == .zero) ≠ true) :
    i15Hx4Word u (a :: w) = fun x => ∫ t in (0 : ℝ)..x, i15Hx4Kernel u a t * i15Hx4Word u w t := by
  funext t
  simp [i15Hx4Word, hw]

private theorem i15Hx4_integrand_bound {d b : ℝ} (hd : 0 < d) (hb : b < 1)
    {a : I15Hx4Letter} {w : List I15Hx4Letter}
    (hw : w.all (· == .zero) ≠ true → ∃ C, 0 ≤ C ∧ ∀ u ∈ Icc d 1, ∀ x ∈ Ioc 0 b,
      |i15Hx4Word u w x| ≤ C * x ^ (1 / 2 : ℝ))
    (haw : (a :: w).all (· == .zero) ≠ true) :
    ∃ C, 0 ≤ C ∧ ∀ u ∈ Icc d 1, ∀ x ∈ Ioc 0 b,
      |i15Hx4Kernel u a x * i15Hx4Word u w x| ≤ C * x ^ (-(1 / 2) : ℝ) := by
  by_cases ha : a = .zero
  · subst a
    have hn : w.all (· == .zero) ≠ true := by simpa using haw
    obtain ⟨C, hC, hc⟩ := hw hn
    refine ⟨C, hC, fun u hu x hx => ?_⟩
    rw [i15Hx4Kernel, abs_mul, abs_of_pos (inv_pos.2 hx.1)]
    calc x⁻¹ * |i15Hx4Word u w x| ≤ x⁻¹ * (C * x ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hc u hu x hx) (inv_nonneg.2 hx.1.le)
      _ = C * x ^ (-(1 / 2) : ℝ) := by
        rw [show (-(1 / 2) : ℝ) = 1 / 2 - 1 by norm_num, rpow_sub_one hx.1.ne']
        field_simp
  · obtain ⟨K, hK, hk⟩ := i15Hx4Kernel_left_bound hd hb
    have hbnd : ∃ C, 0 ≤ C ∧ ∀ u ∈ Icc d 1, ∀ t ∈ Ioc 0 b,
        |i15Hx4Word u w t| ≤ C * t ^ (-(1 / 2) : ℝ) := by
      by_cases hz : w.all (· == .zero) = true
      · obtain ⟨C, hC, hc⟩ := abs_log_pow_le w.length (δ := 1 / 2) (by norm_num)
        refine ⟨C, hC, fun u _ t ht => ?_⟩
        rw [i15Hx4Word_allZero (u := u) hz, abs_div, abs_pow, Nat.abs_cast]
        exact (div_le_self (by positivity) (Nat.one_le_cast.2 (Nat.factorial_pos _))).trans
          (hc t ⟨ht.1, ht.2.trans hb.le⟩)
      · obtain ⟨C, hC, hc⟩ := hw hz
        exact ⟨C, hC, fun u hu t ht => (hc u hu t ht).trans
          (mul_le_mul_of_nonneg_left
            (rpow_le_rpow_of_exponent_ge ht.1 (ht.2.trans hb.le) (by norm_num)) hC)⟩
    obtain ⟨C, hC, hc⟩ := hbnd
    refine ⟨K * C, mul_nonneg hK hC, fun u hu t ht => ?_⟩
    rw [abs_mul, mul_assoc]
    exact mul_le_mul (hk u hu a ha t ht) (hc u hu t ht) (abs_nonneg _) hK

/-- Nonzero words vanish at zero, uniformly on lower-bounded parameter intervals. -/
theorem i15Hx4Word_left_bound {d b : ℝ} (hd : 0 < d) (hb : b < 1)
    (w : List I15Hx4Letter) (hw : w.all (· == .zero) ≠ true) :
    ∃ C, 0 ≤ C ∧ ∀ u ∈ Icc d 1, ∀ x ∈ Ioc 0 b, |i15Hx4Word u w x| ≤ C * x ^ (1 / 2 : ℝ) := by
  induction w with
  | nil => exact (hw rfl).elim
  | cons a w ih =>
    obtain ⟨C, hC, hc⟩ := i15Hx4_integrand_bound hd hb ih hw
    refine ⟨2 * C, by positivity, fun u hu x hx => ?_⟩
    rw [i15Hx4Word_cons_integral hw]
    have hI := abs_integral_le_of_le_rpow hx.1.le (by norm_num : (-1 : ℝ) < -(1 / 2))
      (K := C) fun t ht => hc u hu t ⟨ht.1, ht.2.trans hx.2⟩
    convert hI using 1
    norm_num
    ring

private theorem hasDerivAt_i15Hx4Word_cons_of_continuous {u x : ℝ}
    (hu : u ∈ Ioc (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1)
    (a : I15Hx4Letter) (w : List I15Hx4Letter)
    (hc : ContinuousOn (i15Hx4Word u w) (Ioo (0 : ℝ) 1)) :
    HasDerivAt (i15Hx4Word u (a :: w)) (i15Hx4Kernel u a x * i15Hx4Word u w x) x := by
  by_cases hz : (a :: w).all (· == .zero) = true
  · have hsplit : a = .zero ∧ w.all (· == .zero) = true := by simpa using hz
    obtain ⟨rfl, hw⟩ := hsplit
    rw [show i15Hx4Word u (.zero :: w) = fun t =>
      log t ^ (w.length + 1) / ((w.length + 1).factorial : ℝ) from
      funext (fun _ => i15Hx4Word_allZero hz), i15Hx4Kernel, i15Hx4Word_allZero hw]
    exact hasDerivAt_log_pow_div hx.1
  · obtain ⟨C, _, hC⟩ := i15Hx4_integrand_bound hu.1 hx.2
      (i15Hx4Word_left_bound hu.1 hx.2 w) hz
    have hcont := (i15Hx4Kernel_continuousOn hu a).mul hc
    rw [i15Hx4Word_cons_integral hz]
    exact intervalIntegral.integral_hasDerivAt_right
      (intervalIntegrable_of_le_rpow hx.1.le hx.2 hcont (hC u ⟨le_rfl, hu.2⟩))
      (hcont.stronglyMeasurableAtFilter isOpen_Ioo x hx)
      (hcont.continuousAt (isOpen_Ioo.mem_nhds hx))

/-- The derivative with respect to the upper limit is the head kernel times the tail word. -/
theorem hasDerivAt_i15Hx4Word_cons {u x : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1)
    (a : I15Hx4Letter) (w : List I15Hx4Letter) :
    HasDerivAt (i15Hx4Word u (a :: w)) (i15Hx4Kernel u a x * i15Hx4Word u w x) x := by
  have hcont (v : List I15Hx4Letter) : ContinuousOn (i15Hx4Word u v) (Ioo (0 : ℝ) 1) := by
    induction v with
    | nil => exact continuousOn_const
    | cons b v ih =>
        exact fun _ hy =>
          (hasDerivAt_i15Hx4Word_cons_of_continuous hu hy b v ih).continuousAt.continuousWithinAt
  exact hasDerivAt_i15Hx4Word_cons_of_continuous hu hx a w (hcont w)

/-- Every signed word is continuous on the open slice. -/
theorem continuousOn_i15Hx4Word {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) (w : List I15Hx4Letter) :
    ContinuousOn (i15Hx4Word u w) (Ioo 0 1) := by
  cases w with
  | nil => exact continuousOn_const
  | cons a w =>
      exact fun _ hx => (hasDerivAt_i15Hx4Word_cons hu hx a w).continuousAt.continuousWithinAt

/-- A nonzero signed word tends to zero at the left endpoint. -/
theorem tendsto_i15Hx4Word_zero {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1)
    {w : List I15Hx4Letter} (hw : w.all (· == .zero) ≠ true) :
    Tendsto (i15Hx4Word u w) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := i15Hx4Word_left_bound hu.1 (by norm_num : (1 / 2 : ℝ) < 1) w hw
  exact tendsto_zero_of_abs_le_rpow (C := C) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num) (hC u ⟨le_rfl, hu.2⟩)

private theorem i15Hx4Word_mid_bound {d : ℝ} (hd : 0 < d) (w : List I15Hx4Letter) :
    ∃ C, 0 ≤ C ∧ ∀ u ∈ Icc d 1, |i15Hx4Word u w (1 / 2)| ≤ C := by
  by_cases hw : w.all (· == .zero) = true
  · refine ⟨|log (1 / 2) ^ w.length / (w.length.factorial : ℝ)|, abs_nonneg _, fun u _ => ?_⟩
    rw [i15Hx4Word_allZero (u := u) hw]
  · obtain ⟨C, hC, hc⟩ := i15Hx4Word_left_bound hd (by norm_num : (1 / 2 : ℝ) < 1) w hw
    refine ⟨C * (1 / 2 : ℝ) ^ (1 / 2 : ℝ), by positivity, fun u hu => ?_⟩
    exact hc u hu _ ⟨by norm_num, le_rfl⟩

private theorem i15Hx4Kernel_right_bound {d u x : ℝ} (hd : 0 < d) (hu : u ∈ Icc d 1)
    (hx : x ∈ Ico (1 / 2 : ℝ) 1) (a : I15Hx4Letter) :
    |i15Hx4Kernel u a x| ≤ max 2 d⁻¹ * (1 - x)⁻¹ := by
  have hx0 : 0 < x := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hx.1
  have h1 := sub_pos.2 hx.2
  have hi : 1 ≤ (1 - x)⁻¹ := (one_le_inv₀ h1).2 (by linarith)
  have hK : max (2 : ℝ) d⁻¹ ≤ max 2 d⁻¹ * (1 - x)⁻¹ :=
    le_mul_of_one_le_right (zero_le_two.trans (le_max_left _ _)) hi
  cases a with
  | zero =>
      rw [i15Hx4Kernel, abs_of_pos (inv_pos.2 hx0)]
      exact ((inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hx.1).trans
        (by norm_num : (1 / 2 : ℝ)⁻¹ ≤ 2)).trans ((le_max_left _ _).trans hK)
  | one =>
      rw [i15Hx4Kernel, show x - 1 = -(1 - x) by ring, inv_neg, abs_neg,
        abs_of_pos (inv_pos.2 h1)]
      exact le_mul_of_one_le_left (inv_nonneg.2 h1.le) (one_le_two.trans (le_max_left _ _))
  | pos =>
      exact (i15Hx4Kernel_bounds hd hu.1 hu.2 ⟨hx0.le, hx.2.le⟩ .pos
        (by decide) (by decide)).1.trans ((le_max_right _ _).trans hK)
  | neg =>
      exact (i15Hx4Kernel_bounds hd hu.1 hu.2 ⟨hx0.le, hx.2.le⟩ .neg
        (by decide) (by decide)).1.trans ((le_max_right _ _).trans hK)

private theorem i15Hx4_growth_of_deriv {F g : ℝ → ℝ} {x ε D E : ℝ}
    (hx : x ∈ Ico (1 / 2 : ℝ) 1) (hε : 0 < ε) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt F (g t) t)
    (hcont : ContinuousOn g (Ioo 0 1)) (hmid : |F (1 / 2)| ≤ D)
    (hb : ∀ t ∈ Ico (1 / 2 : ℝ) 1, |g t| ≤ E * (1 - t) ^ (-ε - 1)) :
    |F x| ≤ (D + E / ε) * (1 - x) ^ (-ε) := by
  have hlarge : 1 ≤ (1 - x) ^ (-ε) :=
    one_le_rpow_of_pos_of_le_one_of_nonpos (sub_pos.2 hx.2) (by linarith [hx.1])
      (neg_nonpos.2 hε.le)
  have hsub : uIcc (1 / 2 : ℝ) x ⊆ Ioo 0 1 := by
    rw [uIcc_of_le hx.1]
    exact fun _ ht => ⟨by linarith [ht.1], ht.2.trans_lt hx.2⟩
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hderiv t (hsub ht))
    (hcont.mono hsub).intervalIntegrable
  have hI := abs_integral_half_le (g := g) hx (show -ε - 1 ≠ -1 by linarith) hb
  have hI' : |∫ t in (1 / 2 : ℝ)..x, g t| ≤ E / ε * (1 - x) ^ (-ε) := by
    refine hI.trans ?_
    rw [show -ε - 1 + 1 = -ε by ring]
    have hpow : 0 ≤ (1 / 2 : ℝ) ^ (-ε) := by positivity
    rw [show E * (((1 / 2 : ℝ) ^ (-ε) - (1 - x) ^ (-ε)) / (-ε)) =
      E / ε * ((1 - x) ^ (-ε) - (1 / 2 : ℝ) ^ (-ε)) by ring]
    exact mul_le_mul_of_nonneg_left (sub_le_self _ hpow) (div_nonneg hE hε.le)
  have he' : F x =
      F (1 / 2) + ∫ t in (1 / 2 : ℝ)..x, g t := by
    rw [he]
    ring
  calc |F x|
      ≤ D + E / ε * (1 - x) ^ (-ε) := by
        rw [he']
        exact (abs_add_le _ _).trans (add_le_add hmid hI')
    _ ≤ (D + E / ε) * (1 - x) ^ (-ε) := by
      rw [add_mul]
      exact add_le_add_left (le_mul_of_one_le_right hD hlarge) _

/-- Signed words grow more slowly than every negative power at the right endpoint. -/
theorem i15Hx4Word_right_bound {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (w : List I15Hx4Letter) :
    ∃ C, 0 ≤ C ∧ ∀ u ∈ Icc d 1, ∀ x ∈ Ico (1 / 2 : ℝ) 1,
      |i15Hx4Word u w x| ≤ C * (1 - x) ^ (-ε) := by
  have hlarge {x : ℝ} (hx : x ∈ Ico (1 / 2 : ℝ) 1) : 1 ≤ (1 - x) ^ (-ε) :=
    one_le_rpow_of_pos_of_le_one_of_nonpos (sub_pos.2 hx.2) (by linarith [hx.1])
      (neg_nonpos.2 hε.le)
  induction w with
  | nil =>
      refine ⟨1, zero_le_one, fun _ _ x hx => ?_⟩
      simpa [i15Hx4Word] using hlarge hx
  | cons a w ih =>
    obtain ⟨C, hC, hc⟩ := ih
    obtain ⟨D, hD, hd'⟩ := i15Hx4Word_mid_bound hd (a :: w)
    let E := max (2 : ℝ) d⁻¹ * C
    have hmax : 0 ≤ max (2 : ℝ) d⁻¹ := zero_le_two.trans (le_max_left _ _)
    have hE : 0 ≤ E := mul_nonneg hmax hC
    refine ⟨D + E / ε, by positivity, fun u hu x hx => ?_⟩
    have hut : u ∈ Ioc (0 : ℝ) 1 := ⟨hd.trans_le hu.1, hu.2⟩
    let g := fun t => i15Hx4Kernel u a t * i15Hx4Word u w t
    have hb (t : ℝ) (ht : t ∈ Ico (1 / 2 : ℝ) 1) :
        |g t| ≤ E * (1 - t) ^ (-ε - 1) := by
      unfold g
      rw [abs_mul, rpow_sub_one (sub_pos.2 ht.2).ne', div_eq_mul_inv]
      calc |i15Hx4Kernel u a t| * |i15Hx4Word u w t|
          ≤ (max 2 d⁻¹ * (1 - t)⁻¹) * (C * (1 - t) ^ (-ε)) :=
            mul_le_mul (i15Hx4Kernel_right_bound hd hu ht a) (hc u hu t ht) (abs_nonneg _)
              (mul_nonneg hmax (inv_nonneg.2 (sub_pos.2 ht.2).le))
        _ = E * ((1 - t) ^ (-ε) * (1 - t)⁻¹) := by unfold E; ring
    exact i15Hx4_growth_of_deriv hx hε hD hE
      (fun _ ht => hasDerivAt_i15Hx4Word_cons hut ht a w)
      ((i15Hx4Kernel_continuousOn hut a).mul (continuousOn_i15Hx4Word hut w)) (hd' u hu) hb

/-- The nonsingular kernels are bounded on the upper half of the slice. -/
theorem i15Hx4Kernel_right_bound_of_ne_one {d u x : ℝ} (hd : 0 < d) (hu : u ∈ Icc d 1)
    (hx : x ∈ Ico (1 / 2 : ℝ) 1) {a : I15Hx4Letter} (ha : a ≠ .one) :
    |i15Hx4Kernel u a x| ≤ max 2 d⁻¹ := by
  have hx0 : 0 < x := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hx.1
  cases a with
  | zero =>
      rw [i15Hx4Kernel, abs_of_pos (inv_pos.2 hx0)]
      exact ((inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hx.1).trans
        (by norm_num : (1 / 2 : ℝ)⁻¹ ≤ 2)).trans (le_max_left _ _)
  | one => exact (ha rfl).elim
  | pos =>
      exact (i15Hx4Kernel_bounds hd hu.1 hu.2 ⟨hx0.le, hx.2.le⟩ .pos
        (by decide) (by decide)).1.trans (le_max_right _ _)
  | neg =>
      exact (i15Hx4Kernel_bounds hd hu.1 hu.2 ⟨hx0.le, hx.2.le⟩ .neg
        (by decide) (by decide)).1.trans (le_max_right _ _)

private theorem intervalIntegrable_i15Hx4Word_kernel {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1)
    {a : I15Hx4Letter} (ha : a ≠ .one) (w : List I15Hx4Letter)
    (hw : (a :: w).all (· == .zero) ≠ true) :
    IntervalIntegrable (fun t => i15Hx4Kernel u a t * i15Hx4Word u w t) volume 0 1 := by
  have hhalf : (1 / 2 : ℝ) < 1 := by norm_num
  have huu : u ∈ Icc u 1 := ⟨le_rfl, hu.2⟩
  obtain ⟨C, _, hc⟩ := i15Hx4_integrand_bound hu.1 hhalf
    (i15Hx4Word_left_bound hu.1 hhalf w) hw
  obtain ⟨D, hD, hd⟩ := i15Hx4Word_right_bound hu.1 (by norm_num : (0 : ℝ) < 1 / 2) w
  let g := fun t => i15Hx4Kernel u a t * i15Hx4Word u w t
  have hcont : ContinuousOn g (Ioo (0 : ℝ) 1) :=
    (i15Hx4Kernel_continuousOn hu a).mul (continuousOn_i15Hx4Word hu w)
  refine (intervalIntegrable_of_le_rpow (by norm_num) hhalf hcont (hc u huu)).trans ?_
  have hi : IntervalIntegrable (fun t => t ^ (-(1 / 2) : ℝ)) volume 0 (1 / 2) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hi' : IntervalIntegrable (fun t => (1 - t) ^ (-(1 / 2) : ℝ)) volume (1 / 2) 1 := by
    convert (hi.comp_sub_left 1).symm using 1 <;> norm_num
  have hm := hi'.const_mul (max 2 u⁻¹ * D)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hhalf.le] at hm ⊢
  refine hm.mono' ((hcont.mono fun _ ht => ⟨by linarith [ht.1], ht.2⟩).aestronglyMeasurable
    measurableSet_Ioo) ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun t ht => ?_))
  have ht' : t ∈ Ico (1 / 2 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  rw [Real.norm_eq_abs, show g t = _ from rfl, abs_mul, mul_assoc]
  exact mul_le_mul (i15Hx4Kernel_right_bound_of_ne_one hu.1 huu ht' ha) (hd u huu t ht')
    (abs_nonneg _) (zero_le_two.trans (le_max_left _ _))

/-- Words whose first letter is nonsingular at one have a finite endpoint. -/
theorem tendsto_i15Hx4Word_one {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1)
    {w : List I15Hx4Letter} (hw : w.head? ≠ some .one) :
    Tendsto (i15Hx4Word u w) (𝓝[<] 1) (𝓝 (i15Hx4Word u w 1)) := by
  by_cases hzero : w.all (· == .zero) = true
  · rw [show i15Hx4Word u w = fun x => log x ^ w.length / (w.length.factorial : ℝ) from
      funext (fun _ => i15Hx4Word_allZero hzero)]
    exact (((continuousAt_log one_ne_zero).pow _).div_const _).tendsto.mono_left
      nhdsWithin_le_nhds
  · cases w with
    | nil => exact (hzero rfl).elim
    | cons a w =>
        have ha : a ≠ .one := by simpa using hw
        rw [i15Hx4Word_cons_integral hzero]
        have hc := intervalIntegral.continuousOn_primitive_interval'
          (intervalIntegrable_i15Hx4Word_kernel hu ha w hzero) left_mem_uIcc
        rw [uIcc_of_le zero_le_one] at hc
        exact (hc 1 (right_mem_Icc.2 zero_le_one)).mono_left
          (nhdsWithin_le_of_mem (by
            filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with x hx
            exact ⟨hx.1.le, hx.2.le⟩))

/-- The signed integration-by-parts primitive of an iterated word. -/
noncomputable def i15Hx4Prim (u : ℝ) : List I15Hx4Letter → ℝ → ℝ
  | [], x => x
  | a :: w, x => (x + i15Hx4Offset u a) * i15Hx4Word u (a :: w) x - i15Hx4Prim u w x

private theorem i15Hx4Offset_ne_pole {u x : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (a : I15Hx4Letter) : x + i15Hx4Offset u a ≠ 0 := by
  obtain ⟨hp, hm, _⟩ := i15Hx_den_pos hu ⟨hx.1.le, hx.2.le⟩
  have hv := sub_pos.2 hu.2
  cases a with
  | zero => simpa [i15Hx4Offset] using hx.1.ne'
  | one => exact (sub_neg.2 hx.2).ne
  | pos => exact (add_pos hx.1 (div_pos hu.1 hv)).ne'
  | neg =>
      intro he
      simp only [i15Hx4Offset] at he
      field_simp [hv.ne'] at he
      linarith

/-- The signed primitive differentiates to the word on the open slice. -/
theorem hasDerivAt_i15Hx4Prim {u x : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (w : List I15Hx4Letter) :
    HasDerivAt (i15Hx4Prim u w) (i15Hx4Word u w x) x := by
  induction w with
  | nil => exact hasDerivAt_id x
  | cons a w ih =>
      have h := (((hasDerivAt_id' x).add_const (i15Hx4Offset u a)).mul
        (hasDerivAt_i15Hx4Word_cons ⟨hu.1, hu.2.le⟩ hx a w)).sub ih
      refine h.congr_deriv ?_
      rw [i15Hx4Kernel_eq_inv a hu, ← mul_assoc, mul_inv_cancel₀ (i15Hx4Offset_ne_pole hu hx a)]
      ring

/-- Endpoint value of the signed word primitive at one. -/
noncomputable def i15Hx4PrimOne (u : ℝ) : List I15Hx4Letter → ℝ
  | [] => 1
  | a :: w => (if a = .one then 0 else (1 + i15Hx4Offset u a) * i15Hx4Word u (a :: w) 1) -
      i15Hx4PrimOne u w

/-- The primitive has its prescribed right limit, even with a leading endpoint pole. -/
theorem tendsto_i15Hx4Prim_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (w : List I15Hx4Letter) :
    Tendsto (i15Hx4Prim u w) (𝓝[<] 1) (𝓝 (i15Hx4PrimOne u w)) := by
  have hid : Tendsto (fun t : ℝ => t) (𝓝[<] 1) (𝓝 1) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  induction w with
  | nil => exact hid
  | cons a w ih =>
      have hut : u ∈ Ioc (0 : ℝ) 1 := ⟨hu.1, hu.2.le⟩
      by_cases ha : a = .one
      · subst a
        obtain ⟨C, _, hC⟩ := i15Hx4Word_right_bound hu.1 (by norm_num : (0 : ℝ) < 1 / 2)
          (.one :: w)
        have hb : ∀ᶠ x in 𝓝[<] (1 : ℝ),
            ‖(x - 1) * i15Hx4Word u (.one :: w) x‖ ≤ C * (1 - x) ^ (1 / 2 : ℝ) := by
          filter_upwards [Ioo_mem_nhdsLT (show (1 / 2 : ℝ) < 1 by norm_num)] with x hx
          have hpos := sub_pos.2 hx.2
          rw [Real.norm_eq_abs, abs_mul, abs_of_neg (sub_neg.2 hx.2), neg_sub]
          calc (1 - x) * |i15Hx4Word u (.one :: w) x|
              ≤ (1 - x) * (C * (1 - x) ^ (-(1 / 2) : ℝ)) :=
                mul_le_mul_of_nonneg_left (hC u ⟨le_rfl, hut.2⟩ x ⟨hx.1.le, hx.2⟩) hpos.le
            _ = C * (1 - x) ^ (1 / 2 : ℝ) := by
              rw [show (1 - x) * (C * (1 - x) ^ (-(1 / 2) : ℝ)) =
                C * ((1 - x) ^ (-(1 / 2) : ℝ) * (1 - x)) by ring, ← rpow_add_one hpos.ne']
              norm_num
        have hpow := ((continuousAt_const.sub continuousAt_id :
          ContinuousAt (fun x : ℝ => 1 - x) 1).rpow_const
            (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 2))).tendsto.mono_left
              (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
        have hz : Tendsto (fun x => C * (1 - x) ^ (1 / 2 : ℝ)) (𝓝[<] 1) (𝓝 0) := by
          simpa using hpow.const_mul C
        have hlim := squeeze_zero_norm' hb hz
        simpa only [i15Hx4Prim, i15Hx4PrimOne, i15Hx4Offset, sub_eq_add_neg, ite_true, eq_self]
          using hlim.sub ih
      · have hlim := tendsto_i15Hx4Word_one hut (w := a :: w) (by simpa using ha)
        simpa only [i15Hx4Prim, i15Hx4PrimOne, ite_eq_right ha] using
          ((hid.add_const (i15Hx4Offset u a)).mul hlim).sub ih

/-- The signed primitive vanishes at zero. -/
theorem tendsto_i15Hx4Prim_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (w : List I15Hx4Letter) :
    Tendsto (i15Hx4Prim u w) (𝓝[>] 0) (𝓝 0) := by
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  induction w with
  | nil => exact hid
  | cons a w ih =>
    by_cases hw : (a :: w).all (· == .zero) = true
    · have hsplit : a = .zero ∧ w.all (· == .zero) = true := by simpa using hw
      obtain ⟨rfl, _⟩ := hsplit
      obtain ⟨C, _, hC⟩ := abs_log_pow_le (w.length + 1) (δ := 1 / 2) (by norm_num)
      have hz : Tendsto (fun x => x * i15Hx4Word u (.zero :: w) x) (𝓝[>] 0) (𝓝 0) := by
        refine tendsto_zero_of_abs_le_rpow (C := C) (by norm_num : (0 : ℝ) < 1 / 2)
          zero_lt_one (fun x hx => ?_)
        rw [abs_mul, abs_of_pos hx.1, i15Hx4Word_allZero hw, abs_div, abs_pow, Nat.abs_cast]
        calc x * (|log x| ^ (w.length + 1) / (↑(w.length + 1).factorial : ℝ))
            ≤ x * (C * x ^ (-(1 / 2) : ℝ)) := by
              apply mul_le_mul_of_nonneg_left _ hx.1.le
              exact (div_le_self (by positivity) (Nat.one_le_cast.2
                (Nat.factorial_pos _))).trans (hC x hx)
          _ = C * x ^ (1 / 2 : ℝ) := by
            rw [show x * (C * x ^ (-(1 / 2) : ℝ)) = C * (x ^ (-(1 / 2) : ℝ) * x) by ring,
              ← rpow_add_one hx.1.ne']
            norm_num
      simpa only [i15Hx4Prim, i15Hx4Offset, add_zero, sub_zero] using hz.sub ih
    · simpa only [i15Hx4Prim, mul_zero, sub_zero] using
        ((hid.add_const (i15Hx4Offset u a)).mul
          (tendsto_i15Hx4Word_zero ⟨hu.1, hu.2.le⟩ hw)).sub ih

/-- Integrating an integrable signed word gives the right endpoint of its primitive. -/
theorem integral_i15Hx4Word {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (w : List I15Hx4Letter)
    (hI : IntegrableOn (i15Hx4Word u w) (Ioo 0 1)) :
    ∫ x in Ioo (0 : ℝ) 1, i15Hx4Word u w x = i15Hx4PrimOne u w := by
  simpa only [sub_zero] using QED.Polylog.ParamHPL.setIntegral_Ioo_deriv zero_lt_one
    (fun _ hx => hasDerivAt_i15Hx4Prim hu hx w) hI
    (tendsto_i15Hx4Prim_zero hu w) (tendsto_i15Hx4Prim_one hu w)

private theorem i15Hx4_dom_split {g : ℝ → ℝ → ℝ} {d x C D : ℝ} (hx : x ≤ 1)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hL : ∀ u ∈ Icc d 1, ∀ t ∈ Ioc (0 : ℝ) (1 / 2), |g u t| ≤ C * t ^ (-(1 / 2) : ℝ))
    (hR : ∀ u ∈ Icc d 1, ∀ t ∈ Ico (1 / 2 : ℝ) 1, |g u t| ≤ D * (1 - t) ^ (-(1 / 2) : ℝ)) :
    ∃ B : ℝ → ℝ, IntegrableOn B (Ioo 0 x) ∧
      ∀ u ∈ Icc d 1, ∀ t ∈ Ioo 0 x, |g u t| ≤ B t := by
  let B := fun t : ℝ => (C + D) * (t ^ (-(1 / 2) : ℝ) + (1 - t) ^ (-(1 / 2) : ℝ))
  have hB : IntegrableOn B (Ioo 0 1) :=
    QED.Polylog.ParamHPL.integrableOn_rpow_add_one_sub_rpow.const_mul _
  refine ⟨B, hB.mono_set (Ioo_subset_Ioo_right hx), ?_⟩
  intro u hu t ht
  have ht1 := ht.2.trans_le hx
  have hl := rpow_nonneg ht.1.le (-(1 / 2) : ℝ)
  have hr := rpow_nonneg (sub_pos.2 ht1).le (-(1 / 2) : ℝ)
  dsimp only [B]
  by_cases ht' : t ≤ 1 / 2
  · exact (hL u hu t ⟨ht.1, ht'⟩).trans
      (mul_le_mul (le_add_of_nonneg_right hD) (le_add_of_nonneg_right hr) hl (by positivity))
  · exact (hR u hu t ⟨le_of_not_ge ht', ht1⟩).trans
      (mul_le_mul (le_add_of_nonneg_left hC) (le_add_of_nonneg_left hl) hr (by positivity))

private theorem i15Hx4Word_kernel_dom {a : I15Hx4Letter} {w : List I15Hx4Letter}
    {d x : ℝ} (hd : 0 < d) (hx : x ∈ Ioc (0 : ℝ) 1)
    (ha : x < 1 ∨ a ≠ .one) (hw : (a :: w).all (· == .zero) ≠ true) :
    ∃ B : ℝ → ℝ, IntegrableOn B (Ioo 0 x) ∧
      ∀ u ∈ Icc d 1, ∀ t ∈ Ioo 0 x, |i15Hx4Kernel u a t * i15Hx4Word u w t| ≤ B t := by
  rcases ha with hlt | hne
  · obtain ⟨C, _, hc⟩ := i15Hx4_integrand_bound hd hlt (i15Hx4Word_left_bound hd hlt w) hw
    refine ⟨fun t => C * t ^ (-(1 / 2) : ℝ), ?_, fun u hu t ht => hc u hu t ⟨ht.1, ht.2.le⟩⟩
    rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le hx.1.le]
    exact (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul C
  · have hhalf : (1 / 2 : ℝ) < 1 := by norm_num
    obtain ⟨C, hC, hc⟩ := i15Hx4_integrand_bound hd hhalf
      (i15Hx4Word_left_bound hd hhalf w) hw
    obtain ⟨D, hD, hd'⟩ := i15Hx4Word_right_bound hd (by norm_num : (0 : ℝ) < 1 / 2) w
    let K := max (2 : ℝ) d⁻¹
    have hK : 0 ≤ K := zero_le_two.trans (le_max_left _ _)
    refine i15Hx4_dom_split hx.2 hC (mul_nonneg hK hD) hc ?_
    intro u hu t ht
    rw [abs_mul, mul_assoc]
    exact mul_le_mul (i15Hx4Kernel_right_bound_of_ne_one hd hu ht hne) (hd' u hu t ht)
      (abs_nonneg _) hK

private theorem continuousAt_i15Hx4Kernel_param_one (a : I15Hx4Letter) (x : ℝ) :
    ContinuousAt (fun u => i15Hx4Kernel u a x) 1 := by
  cases a with
  | zero => exact continuousAt_const
  | one => exact continuousAt_const
  | pos =>
      exact (continuousAt_const.sub continuousAt_id).div
        (continuousAt_id.add ((continuousAt_const.sub continuousAt_id).mul continuousAt_const))
        (by norm_num)
  | neg =>
      exact (continuousAt_const.sub continuousAt_id).neg.div
        (continuousAt_const.sub ((continuousAt_const.sub continuousAt_id).mul continuousAt_const))
        (by norm_num)

/-- The parameter endpoint can be taken inside the signed words with a finite slice limit. -/
theorem tendsto_i15Hx4Word_param_one (w : List I15Hx4Letter) {x : ℝ}
    (hx : x ∈ Ioc (0 : ℝ) 1) (hw : x < 1 ∨ w.head? ≠ some .one) :
    Tendsto (fun u => i15Hx4Word u w x) (𝓝[<] 1) (𝓝 (i15Hx4Word 1 w x)) := by
  induction w generalizing x with
  | nil => exact tendsto_const_nhds
  | cons a w ih =>
    by_cases hz : (a :: w).all (· == .zero) = true
    · simp_rw [i15Hx4Word_allZero hz]
      exact tendsto_const_nhds
    have ha : x < 1 ∨ a ≠ .one := hw.imp_right (fun h => by simpa using h)
    obtain ⟨B, hB, hbound⟩ := i15Hx4Word_kernel_dom
      (show (0 : ℝ) < 1 / 2 by norm_num) hx ha hz
    have he : ∀ᶠ u in 𝓝[<] (1 : ℝ), u ∈ Ioo (1 / 2) 1 :=
      Ioo_mem_nhdsLT (by norm_num)
    have hlim := QED.Polylog.ParamHPL.tendsto_setIntegral_param measurableSet_Ioo
      (g := fun t u => i15Hx4Kernel u a t * i15Hx4Word u w t)
      (g₀ := fun t => i15Hx4Kernel 1 a t * i15Hx4Word 1 w t)
      (he.mono fun u hu => by
        have hu' : u ∈ Ioc (0 : ℝ) 1 := ⟨by linarith [hu.1], hu.2.le⟩
        have hc := (i15Hx4Kernel_continuousOn hu' a).mul (continuousOn_i15Hx4Word hu' w)
        exact (hc.mono (Ioo_subset_Ioo_right hx.2)).aestronglyMeasurable measurableSet_Ioo)
      (he.mono fun u hu t ht => hbound u ⟨hu.1.le, hu.2.le⟩ t ht) hB
      (fun t ht => ((continuousAt_i15Hx4Kernel_param_one a t).tendsto.mono_left
        nhdsWithin_le_nhds).mul (ih ⟨ht.1, ht.2.le.trans hx.2⟩ (Or.inl (ht.2.trans_le hx.2))))
    simp_rw [i15Hx4Word_cons_integral hz, intervalIntegral.integral_of_le hx.1.le,
      integral_Ioc_eq_integral_Ioo]
    exact hlim

/-- The surviving fixed letters in the parameter limit, with a placeholder for moving letters. -/
def i15Hx4Harmonic : I15Hx4Letter → Letter
  | .zero => .zero
  | .one => .one
  | .pos | .neg => .negOne

/-- The signed kernel multiplier after coalescence. -/
noncomputable def i15Hx4Sign : I15Hx4Letter → ℝ
  | .zero => 1
  | .one => -1
  | .pos | .neg => 0

private theorem i15Hx4Kernel_param_one (a : I15Hx4Letter) (x : ℝ) :
    i15Hx4Kernel 1 a x = i15Hx4Sign a * (i15Hx4Harmonic a).kernel x := by
  cases a <;> simp [i15Hx4Kernel, i15Hx4Sign, i15Hx4Harmonic]
  rw [show x - 1 = -(1 - x) by ring, inv_neg]

private theorem i15Hx4_allZero_map (w : List I15Hx4Letter) :
    AllZero (w.map i15Hx4Harmonic) ↔ w.all (· == .zero) = true := by
  induction w with
  | nil => simp
  | cons a w ih =>
      cases a <;> simp [i15Hx4Harmonic, ih]

/-- At the parameter endpoint, moving letters vanish and fixed letters give signed HPLs. -/
theorem i15Hx4Word_param_one_eq_hpl (w : List I15Hx4Letter) (x : ℝ) :
    i15Hx4Word 1 w x = (w.map i15Hx4Sign).prod * hpl (w.map i15Hx4Harmonic) x := by
  induction w generalizing x with
  | nil => simp [i15Hx4Word]
  | cons a w ih =>
    have hh : (a :: w).all (· == .zero) = true → ((a :: w).map i15Hx4Sign).prod = 1 := by
      intro hz
      have hz' := List.all_eq_true.1 hz
      rw [List.map_congr_left (show ∀ b ∈ a :: w, i15Hx4Sign b = (1 : ℝ) by
        intro b hb
        have h : b = .zero := by simpa using hz' b hb
        simp [h, i15Hx4Sign])]
      simp
    by_cases hz : (a :: w).all (· == .zero) = true
    · rw [i15Hx4Word_allZero hz, hpl_of_allZero ((i15Hx4_allZero_map _).2 hz), hh hz,
        one_mul, List.length_map]
    · have hn : ¬AllZero ((a :: w).map i15Hx4Harmonic) :=
        fun h => hz ((i15Hx4_allZero_map _).1 h)
      rw [i15Hx4Word_cons_integral hz]
      simp only [List.map_cons, List.prod_cons] at hn ⊢
      rw [hpl_cons_of_not_allZero hn, ← intervalIntegral.integral_const_mul]
      simp_rw [ih, i15Hx4Kernel_param_one]
      congr 1
      funext t
      ring

/-- Collapse of convergent words to the fixed HPL alphabet. -/
theorem tendsto_i15Hx4Word_param_one_hpl (w : List I15Hx4Letter) {x : ℝ}
    (hx : x ∈ Ioc (0 : ℝ) 1) (hw : x < 1 ∨ w.head? ≠ some .one) :
    Tendsto (fun u => i15Hx4Word u w x) (𝓝[<] 1)
      (𝓝 ((w.map i15Hx4Sign).prod * hpl (w.map i15Hx4Harmonic) x)) :=
  i15Hx4Word_param_one_eq_hpl w x ▸ tendsto_i15Hx4Word_param_one w hx hw

private theorem i15Hx4Word_log_bound {u : ℝ} {w : List I15Hx4Letter}
    (hw : w.all (· == .zero) = true) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) 1, |i15Hx4Word u w t| ≤ C * t ^ (-δ) := by
  obtain ⟨C, hC, h⟩ := abs_log_pow_le w.length hδ
  refine ⟨C, hC, fun t ht => ?_⟩
  rw [i15Hx4Word_allZero hw, abs_div, abs_pow, Nat.abs_cast]
  exact (div_le_self (by positivity) (Nat.one_le_cast.2 (Nat.factorial_pos _))).trans (h t ht)

private theorem tendsto_i15Hx4Word_mul_zero {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1)
    {v w : List I15Hx4Letter} (h : ¬(v.all (· == .zero) = true ∧ w.all (· == .zero) = true)) :
    Tendsto (fun t => i15Hx4Word u v t * i15Hx4Word u w t) (𝓝[>] 0) (𝓝 0) := by
  have aux (p q : List I15Hx4Letter) (hp : p.all (· == .zero) ≠ true) :
      Tendsto (fun t => i15Hx4Word u p t * i15Hx4Word u q t) (𝓝[>] 0) (𝓝 0) := by
    by_cases hq : q.all (· == .zero) = true
    · obtain ⟨C, hC, hc⟩ :=
        i15Hx4Word_left_bound hu.1 (by norm_num : (1 / 2 : ℝ) < 1) p hp
      obtain ⟨D, hD, hd⟩ := i15Hx4Word_log_bound (u := u) hq (δ := 1 / 4) (by norm_num)
      refine tendsto_zero_of_abs_le_rpow (C := C * D) (by norm_num : (0 : ℝ) < 1 / 4)
        (by norm_num : (0 : ℝ) < 1 / 2) fun t ht => ?_
      rw [abs_mul]
      calc |i15Hx4Word u p t| * |i15Hx4Word u q t|
          ≤ (C * t ^ (1 / 2 : ℝ)) * (D * t ^ (-(1 / 4) : ℝ)) :=
            mul_le_mul (hc u ⟨le_rfl, hu.2⟩ t ht) (hd t ⟨ht.1, by linarith [ht.2]⟩)
              (abs_nonneg _) (mul_nonneg hC (rpow_nonneg ht.1.le _))
        _ = C * D * t ^ (1 / 4 : ℝ) := by
          rw [show C * t ^ (1 / 2 : ℝ) * (D * t ^ (-(1 / 4) : ℝ)) =
            C * D * (t ^ (1 / 2 : ℝ) * t ^ (-(1 / 4) : ℝ)) by ring,
            ← rpow_add ht.1]
          norm_num
    · simpa only [zero_mul] using
        (tendsto_i15Hx4Word_zero hu hp).mul (tendsto_i15Hx4Word_zero hu hq)
  by_cases hv : v.all (· == .zero) = true
  · simpa only [mul_comm] using aux w v (fun hw => h ⟨hv, hw⟩)
  · exact aux v w hv

private theorem i15Hx4_allZero_shuffle {v w s : List I15Hx4Letter} (hs : s ∈ shuffle v w) :
    s.all (· == .zero) = true ↔ v.all (· == .zero) = true ∧ w.all (· == .zero) = true := by
  rw [← Bool.and_eq_true, ← List.all_append]
  simp only [List.all_eq_true]
  exact forall_congr' fun a => imp_congr (perm_of_mem_shuffle hs).mem_iff Iff.rfl

private theorem hasDerivAt_i15Hx4Word_sum {u x : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (a : I15Hx4Letter) (L : List (List I15Hx4Letter)) :
    HasDerivAt (fun t => ((L.map (a :: ·)).map fun w => i15Hx4Word u w t).sum)
      (i15Hx4Kernel u a x * (L.map fun w => i15Hx4Word u w x).sum) x := by
  induction L with
  | nil => simpa using hasDerivAt_const x (0 : ℝ)
  | cons w L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ((hasDerivAt_i15Hx4Word_cons hu hx a w).add ih).congr_deriv (by ring)

/-- Shuffle multiplication for the signed slice words. -/
theorem i15Hx4Word_mul {u x : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1)
    (v w : List I15Hx4Letter) :
    i15Hx4Word u v x * i15Hx4Word u w x =
      ((shuffle v w).map fun s => i15Hx4Word u s x).sum := by
  match v, w with
  | [], w => simp [i15Hx4Word]
  | a :: v, [] => simp [i15Hx4Word]
  | a :: v, b :: w =>
    let S : ℝ → ℝ := fun t => ((shuffle (a :: v) (b :: w)).map fun s => i15Hx4Word u s t).sum
    let F : ℝ → ℝ := fun t => i15Hx4Word u (a :: v) t * i15Hx4Word u (b :: w) t - S t
    have hS : S = fun t => (((shuffle v (b :: w)).map (a :: ·)).map
          fun s => i15Hx4Word u s t).sum +
        (((shuffle (a :: v) w).map (b :: ·)).map fun s => i15Hx4Word u s t).sum := by
      funext t
      simp only [S, shuffle_cons_cons, List.map_append, List.sum_append]
    have hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt F 0 t := by
      intro t ht
      have h1 := (hasDerivAt_i15Hx4Word_cons hu ht a v).mul
        (hasDerivAt_i15Hx4Word_cons hu ht b w)
      have h2 := (hasDerivAt_i15Hx4Word_sum hu ht a (shuffle v (b :: w))).add
        (hasDerivAt_i15Hx4Word_sum hu ht b (shuffle (a :: v) w))
      unfold F
      rw [hS]
      refine (h1.sub h2).congr_deriv ?_
      rw [← i15Hx4Word_mul hu ht v (b :: w), ← i15Hx4Word_mul hu ht (a :: v) w]
      ring
    change _ = S x
    apply sub_eq_zero.mp
    change F x = 0
    by_cases hz : (a :: v).all (· == .zero) = true ∧ (b :: w).all (· == .zero) = true
    · have tendsto_zero (s : List I15Hx4Letter) (hs : s.all (· == .zero) = true)
          (hne : s ≠ []) : Tendsto (i15Hx4Word u s) (𝓝[<] 1) (𝓝 0) := by
        have ha : s.head? ≠ some .one := by
          cases s with
          | nil => simp
          | cons c s =>
              have h : c = .zero ∧ s.all (· == .zero) = true := by simpa using hs
              simp [h.1]
        have h0 := tendsto_i15Hx4Word_one hu ha
        rwa [i15Hx4Word_allZero hs, log_one, zero_pow (List.length_pos_iff.2 hne).ne', zero_div]
          at h0
      have h1 := (tendsto_zero _ hz.1 (List.cons_ne_nil _ _)).mul
        (tendsto_zero _ hz.2 (List.cons_ne_nil _ _))
      have h2 : Tendsto S (𝓝[<] 1) (𝓝 0) := by
        have hsum := tendsto_list_sum (l := shuffle (a :: v) (b :: w))
          (f := fun s t => i15Hx4Word u s t) (a := fun _ => (0 : ℝ)) (x := 𝓝[<] 1)
          fun s hs => tendsto_zero s ((i15Hx4_allZero_shuffle hs).2 hz) (by
            intro h
            have hl := length_of_mem_shuffle hs
            simp [h] at hl)
        simpa [S] using hsum
      have hL : Tendsto F (𝓝[<] 1) (𝓝 0) := by simpa [F] using h1.sub h2
      exact eq_of_hasDerivAt_zero_of_tendsto_left zero_lt_one hd hL x hx
    · have h1 := tendsto_i15Hx4Word_mul_zero hu hz
      have h2 : Tendsto S (𝓝[>] 0) (𝓝 0) := by
        have hsum := tendsto_list_sum (l := shuffle (a :: v) (b :: w))
          (f := fun s t => i15Hx4Word u s t) (a := fun _ => (0 : ℝ)) (x := 𝓝[>] 0)
          fun s hs => tendsto_i15Hx4Word_zero hu
            (fun h => hz ((i15Hx4_allZero_shuffle hs).1 h))
        simpa [S] using hsum
      have hL : Tendsto F (𝓝[>] 0) (𝓝 0) := by simpa [F] using h1.sub h2
      exact eq_of_hasDerivAt_zero_of_tendsto_right zero_lt_one hd hL x hx
termination_by v.length + w.length

/-- Evaluate a linear combination of words, or evaluate their primitives. -/
noncomputable def i15Hx4Eval (F : List I15Hx4Letter → ℝ → ℝ)
    (L : List (ℝ × List I15Hx4Letter)) (u : ℝ) : ℝ :=
  (L.map fun cw => cw.1 * F cw.2 u).sum

/-- Multiply two linear combinations of words by shuffling each pair of words. -/
noncomputable def i15Hx4Product (L M : List (ℝ × List I15Hx4Letter)) :
    List (ℝ × List I15Hx4Letter) :=
  L.flatMap fun (a, v) => M.flatMap fun (b, w) => (shuffle v w).map fun s => (a * b, s)

/-- The shuffle power of a linear combination of words. -/
noncomputable def i15Hx4Power (L : List (ℝ × List I15Hx4Letter)) :
    ℕ → List (ℝ × List I15Hx4Letter)
  | 0 => [(1, [])]
  | n + 1 => i15Hx4Product L (i15Hx4Power L n)

private theorem i15Hx4Eval_cons (F : List I15Hx4Letter → ℝ → ℝ)
    (c : ℝ) (w : List I15Hx4Letter) (L : List (ℝ × List I15Hx4Letter)) (u : ℝ) :
    i15Hx4Eval F ((c, w) :: L) u = c * F w u + i15Hx4Eval F L u := rfl

private theorem i15Hx4Eval_nil (F : List I15Hx4Letter → ℝ → ℝ) (u : ℝ) :
    i15Hx4Eval F [] u = 0 := rfl

private theorem i15Hx4Eval_append (F : List I15Hx4Letter → ℝ → ℝ)
    (L M : List (ℝ × List I15Hx4Letter)) (u : ℝ) :
    i15Hx4Eval F (L ++ M) u = i15Hx4Eval F L u + i15Hx4Eval F M u := by
  simp only [i15Hx4Eval, List.map_append, List.sum_append]

private theorem i15Hx4Eval_shuffle {p u : ℝ} (hp : p ∈ Ioc (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1)
    (c d : ℝ) (v w : List I15Hx4Letter) :
    i15Hx4Eval (i15Hx4Word p) ((shuffle v w).map fun s => (c * d, s)) u =
      (c * i15Hx4Word p v u) * (d * i15Hx4Word p w u) := by
  rw [show (c * i15Hx4Word p v u) * (d * i15Hx4Word p w u) =
      (c * d) * (i15Hx4Word p v u * i15Hx4Word p w u) by ring, i15Hx4Word_mul hp hu v w]
  generalize shuffle v w = L
  induction L with
  | nil => simp [i15Hx4Eval]
  | cons s L ih =>
    simp only [List.map_cons, i15Hx4Eval_cons, List.sum_cons, mul_add, ih]

private theorem i15Hx4Eval_product {p u : ℝ} (hp : p ∈ Ioc (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1)
    (L M : List (ℝ × List I15Hx4Letter)) :
    i15Hx4Eval (i15Hx4Word p) (i15Hx4Product L M) u =
      i15Hx4Eval (i15Hx4Word p) L u * i15Hx4Eval (i15Hx4Word p) M u := by
  have h (c : ℝ) (v : List I15Hx4Letter) : ∀ N : List (ℝ × List I15Hx4Letter),
      i15Hx4Eval (i15Hx4Word p)
        (N.flatMap fun (d, w) => (shuffle v w).map fun s => (c * d, s)) u =
      c * i15Hx4Word p v u * i15Hx4Eval (i15Hx4Word p) N u := by
    intro N
    induction N with
    | nil => simp [i15Hx4Eval]
    | cons hd N ih =>
      obtain ⟨d, w⟩ := hd
      simp only [List.flatMap_cons, i15Hx4Eval_cons, i15Hx4Eval_append, ih,
        i15Hx4Eval_shuffle hp hu, mul_add]
  induction L with
  | nil => simp [i15Hx4Product, i15Hx4Eval]
  | cons hd L ih =>
    obtain ⟨c, v⟩ := hd
    rw [show i15Hx4Product ((c, v) :: L) M =
        (M.flatMap fun (d, w) => (shuffle v w).map fun s => (c * d, s)) ++
          i15Hx4Product L M from rfl]
    rw [i15Hx4Eval_append, h, ih, i15Hx4Eval_cons, add_mul]

private theorem i15Hx4Eval_power {p u : ℝ} (hp : p ∈ Ioc (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1)
    (L : List (ℝ × List I15Hx4Letter)) (n : ℕ) :
    i15Hx4Eval (i15Hx4Word p) (i15Hx4Power L n) u = i15Hx4Eval (i15Hx4Word p) L u ^ n := by
  induction n with
  | zero => simp [i15Hx4Power, i15Hx4Eval, i15Hx4Word]
  | succ n ih => rw [i15Hx4Power, i15Hx4Eval_product hp hu, ih, pow_succ']

private theorem hasDerivAt_i15Hx4Eval_prim {p u : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1)
    (L : List (ℝ × List I15Hx4Letter)) :
    HasDerivAt (i15Hx4Eval (i15Hx4Prim p) L) (i15Hx4Eval (i15Hx4Word p) L u) u := by
  induction L with
  | nil => exact hasDerivAt_const u (0 : ℝ)
  | cons hd L ih =>
    obtain ⟨c, w⟩ := hd
    exact ((hasDerivAt_i15Hx4Prim hp hu w).const_mul c).add ih

private theorem i15Hx4Word_single {u x : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (a : I15Hx4Letter) :
    i15Hx4Word u [a] x = i15Hx4Log u a x := by
  by_cases ha : a = .zero
  · subst a
    simp [i15Hx4Word, i15Hx4Log]
  have hl (f : ℝ → ℝ) (hcont : ContinuousAt f 0) (h0 : f 0 = 1) :
      Tendsto (fun t => log (f t)) (𝓝[>] 0) (𝓝 0) := by
    simpa [h0] using (hcont.log (by simp [h0])).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hL : Tendsto (i15Hx4Log u a) (𝓝[>] 0) (𝓝 0) := by
    cases a with
    | zero => exact (ha rfl).elim
    | one => exact hl (fun t => 1 - t) (continuousAt_const.sub continuousAt_id) (by simp)
    | pos =>
        exact hl (fun t => 1 + (1 - u) * t / u)
          (continuousAt_const.add ((continuousAt_const.mul continuousAt_id).div_const _))
          (by simp)
    | neg =>
        exact hl (fun t => 1 - (1 - u) * t)
          (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)) (by simp)
  exact QED.Polylog.ParamHPL.eqOn_of_hasDerivAt_of_tendsto_left zero_lt_one
    (fun t ht => by simpa only [i15Hx4Word, mul_one] using
      hasDerivAt_i15Hx4Word_cons ⟨hu.1, hu.2.le⟩ ht a [])
    (fun _ ht => hasDerivAt_i15Hx4Log a hu ht)
    (tendsto_i15Hx4Word_zero ⟨hu.1, hu.2.le⟩ (by simp [ha])) hL hx

/-- Word coefficients of the two logarithmic bases in the signed slice. -/
noncomputable def i15Hx4Linear (u : ℝ) (moving : ℝ) : List (ℝ × List I15Hx4Letter) :=
  [(-log u, []), (1, [.zero]), (1, [.one]), (moving, [.pos]), (moving, [.neg])]

private theorem i15Hx4Eval_linear {u x : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (c : ℝ) :
    i15Hx4Eval (i15Hx4Word u) (i15Hx4Linear u c) x =
      log x + log (1 - x) - log u + c * i15HxA u x + c * i15HxB u x := by
  simp only [i15Hx4Eval, i15Hx4Linear, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  rw [i15Hx4Word_single hu hx .zero, i15Hx4Word_single hu hx .one,
    i15Hx4Word_single hu hx .pos, i15Hx4Word_single hu hx .neg]
  simp only [i15Hx4Word, i15Hx4Log]
  ring

private theorem i15A23k_four_eq_words {u x : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    i15A23k 4 (x, u) =
      ((1 - u) ^ 2 * i15Hx4Eval (i15Hx4Word u) (i15Hx4Power (i15Hx4Linear u (-2)) 4) x -
        i15Hx4Eval (i15Hx4Word u) (i15Hx4Power (i15Hx4Linear u 0) 4) x) / (24 * u) := by
  obtain ⟨hu0, _, _, _, _, _, _, hp⟩ := i15Hx_pos hu hx
  have hA : log (u + (1 - u) * x) = log u + i15HxA u x := by
    unfold i15HxA
    rw [← log_mul hu0.ne' hp.ne']
    congr 1
    field_simp
  simp only [i15Hx4Eval_power ⟨hu.1, hu.2.le⟩ hx, i15Hx4Eval_linear hu hx,
    i15A23k, i15HxB, i15B1_eq hx hu, i15B2_eq hx, hA, Nat.factorial]
  push_cast
  ring

/-- The primitive of the fourth weight in the signed slice. -/
noncomputable def i15HxPhi4 (u x : ℝ) : ℝ :=
  ((1 - u) ^ 2 * i15Hx4Eval (i15Hx4Prim u) (i15Hx4Power (i15Hx4Linear u (-2)) 4) x -
    i15Hx4Eval (i15Hx4Prim u) (i15Hx4Power (i15Hx4Linear u 0) 4) x) / (24 * u)

/-- The endpoint of the weight-four primitive. -/
noncomputable def i15HxPhi41 (u : ℝ) : ℝ :=
  ((1 - u) ^ 2 * i15Hx4Eval (fun w _ => i15Hx4PrimOne u w)
      (i15Hx4Power (i15Hx4Linear u (-2)) 4) 1 -
    i15Hx4Eval (fun w _ => i15Hx4PrimOne u w) (i15Hx4Power (i15Hx4Linear u 0) 4) 1) / (24 * u)

/-- The signed slice's fourth-power integrand is the derivative of the word primitive. -/
theorem hasDerivAt_i15HxPhi4 {u x : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i15HxPhi4 u) (i15A23k 4 (x, u)) x := by
  rw [i15A23k_four_eq_words hu hx]
  exact (((hasDerivAt_i15Hx4Eval_prim hu hx _).const_mul ((1 - u) ^ 2)).sub
    (hasDerivAt_i15Hx4Eval_prim hu hx _)).div_const (24 * u)

private theorem tendsto_i15Hx4Eval_prim_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (L : List (ℝ × List I15Hx4Letter)) :
    Tendsto (i15Hx4Eval (i15Hx4Prim u) L) (𝓝[>] 0) (𝓝 0) := by
  induction L with
  | nil => exact tendsto_const_nhds
  | cons t L ih =>
      obtain ⟨c, w⟩ := t
      have h := ((tendsto_i15Hx4Prim_zero hu w).const_mul c).add ih
      change Tendsto (fun x => c * i15Hx4Prim u w x + i15Hx4Eval (i15Hx4Prim u) L x)
        (𝓝[>] 0) (𝓝 0)
      simpa only [mul_zero, zero_add] using h

private theorem tendsto_i15Hx4Eval_prim_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (L : List (ℝ × List I15Hx4Letter)) :
    Tendsto (i15Hx4Eval (i15Hx4Prim u) L) (𝓝[<] 1)
      (𝓝 (i15Hx4Eval (fun w _ => i15Hx4PrimOne u w) L 1)) := by
  exact tendsto_list_sum (l := L) (x := 𝓝[<] (1 : ℝ))
    (f := fun t x => t.1 * i15Hx4Prim u t.2 x) (a := fun t => t.1 * i15Hx4PrimOne u t.2)
    (fun t _ => (tendsto_i15Hx4Prim_one hu t.2).const_mul t.1)

/-- The signed weight-four primitive has zero left endpoint. -/
theorem tendsto_i15HxPhi4_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i15HxPhi4 u) (𝓝[>] 0) (𝓝 0) := by
  unfold i15HxPhi4
  simpa only [mul_zero, sub_zero, zero_div] using
    (((tendsto_i15Hx4Eval_prim_zero hu _).const_mul ((1 - u) ^ 2)).sub
      (tendsto_i15Hx4Eval_prim_zero hu _)).div_const (24 * u)

/-- The signed weight-four primitive tends to the word endpoint sum. -/
theorem tendsto_i15HxPhi4_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i15HxPhi4 u) (𝓝[<] 1) (𝓝 (i15HxPhi41 u)) :=
  (((tendsto_i15Hx4Eval_prim_one hu _).const_mul ((1 - u) ^ 2)).sub
    (tendsto_i15Hx4Eval_prim_one hu _)).div_const (24 * u)

/-- The integrable signed slice evaluates to its primitive's right endpoint. -/
theorem integral_i15A23k_four_primitive {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hI : IntegrableOn (fun x => i15A23k 4 (x, u)) (Ioo 0 1)) :
    ∫ x in Ioo (0 : ℝ) 1, i15A23k 4 (x, u) = i15HxPhi41 u := by
  simpa only [sub_zero] using QED.Polylog.ParamHPL.setIntegral_Ioo_deriv zero_lt_one
    (fun _ hx => hasDerivAt_i15HxPhi4 hu hx) hI (tendsto_i15HxPhi4_zero hu)
    (tendsto_i15HxPhi4_one hu)

/-! ### Differentiation in the parameter on a truncated slice -/

/-- Integral recursion for the parameter derivative of a signed word. -/
noncomputable def i15Hx4WordRate (u : ℝ) : List I15Hx4Letter → ℝ → ℝ
  | [], _ => 0
  | a :: w, x =>
      if (a :: w).all (· == .zero) then 0 else
        ∫ t in (0 : ℝ)..x, i15Hx4KernelD u a t * i15Hx4Word u w t +
          i15Hx4Kernel u a t * i15Hx4WordRate u w t

private theorem i15Hx4WordRate_allZero {u x : ℝ} {w : List I15Hx4Letter}
    (hw : w.all (· == .zero) = true) : i15Hx4WordRate u w x = 0 := by
  cases w with
  | nil => rfl
  | cons a w => simp [i15Hx4WordRate, hw]

private theorem i15Hx4WordRate_cons {u : ℝ} {a : I15Hx4Letter} {w : List I15Hx4Letter}
    (hw : (a :: w).all (· == .zero) ≠ true) :
    i15Hx4WordRate u (a :: w) = fun x => ∫ t in (0 : ℝ)..x,
      i15Hx4KernelD u a t * i15Hx4Word u w t + i15Hx4Kernel u a t * i15Hx4WordRate u w t := by
  funext x
  simp [i15Hx4WordRate, hw]

private theorem i15Hx4KernelD_bound {u x d : ℝ} (hd : 0 < d) (hu : u ∈ Icc d 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (a : I15Hx4Letter) :
    |i15Hx4KernelD u a x| ≤ (d ^ 2)⁻¹ := by
  cases a with
  | zero => simpa only [i15Hx4KernelD, abs_zero] using inv_nonneg.2 (sq_nonneg d)
  | one => simpa only [i15Hx4KernelD, abs_zero] using inv_nonneg.2 (sq_nonneg d)
  | pos => exact (i15Hx4Kernel_bounds hd hu.1 hu.2 hx .pos (by decide) (by decide)).2
  | neg => exact (i15Hx4Kernel_bounds hd hu.1 hu.2 hx .neg (by decide) (by decide)).2

private theorem i15Hx4Word_left_bound_neg {d b : ℝ} (hd : 0 < d) (hb : b < 1)
    (w : List I15Hx4Letter) :
    ∃ C, 0 ≤ C ∧ ∀ u ∈ Icc d 1, ∀ t ∈ Ioc 0 b,
      |i15Hx4Word u w t| ≤ C * t ^ (-(1 / 2) : ℝ) := by
  by_cases hz : w.all (· == .zero) = true
  · obtain ⟨C, hC, hc⟩ := i15Hx4Word_log_bound (u := d) hz (δ := 1 / 2) (by norm_num)
    refine ⟨C, hC, fun u _ t ht => ?_⟩
    rw [i15Hx4Word_allZero (u := u) hz, ← i15Hx4Word_allZero (u := d) hz]
    exact hc t ⟨ht.1, ht.2.trans hb.le⟩
  · obtain ⟨C, hC, hc⟩ := i15Hx4Word_left_bound hd hb w hz
    exact ⟨C, hC, fun u hu t ht => (hc u hu t ht).trans
      (mul_le_mul_of_nonneg_left
        (rpow_le_rpow_of_exponent_ge ht.1 (ht.2.trans hb.le) (by norm_num)) hC)⟩

private theorem i15Hx4_rate_integrand_bound {d b : ℝ} (hd : 0 < d) (hb : b < 1)
    (a : I15Hx4Letter) (w : List I15Hx4Letter)
    (hr : ∃ C, 0 ≤ C ∧ ∀ u ∈ Icc d 1, ∀ x ∈ Ioc 0 b,
      |i15Hx4WordRate u w x| ≤ C * x ^ (1 / 2 : ℝ)) :
    ∃ K, 0 ≤ K ∧ ∀ u ∈ Icc d 1, ∀ x ∈ Ioc 0 b,
      |i15Hx4KernelD u a x * i15Hx4Word u w x +
        i15Hx4Kernel u a x * i15Hx4WordRate u w x| ≤ K * x ^ (-(1 / 2) : ℝ) := by
  obtain ⟨C, hC, hc⟩ := hr
  obtain ⟨D, hD, hd'⟩ := i15Hx4Word_left_bound_neg hd hb w
  obtain ⟨E, hE, he⟩ := i15Hx4Kernel_left_bound hd hb
  refine ⟨(d ^ 2)⁻¹ * D + max 1 E * C, by positivity, fun u hu x hx => ?_⟩
  have hx1 := hx.2.trans hb.le
  have hfirst : |i15Hx4KernelD u a x * i15Hx4Word u w x| ≤
      ((d ^ 2)⁻¹ * D) * x ^ (-(1 / 2) : ℝ) := by
    rw [abs_mul, mul_assoc]
    exact mul_le_mul (i15Hx4KernelD_bound hd hu ⟨hx.1.le, hx1⟩ a) (hd' u hu x hx)
      (abs_nonneg _) (by positivity)
  have hsecond : |i15Hx4Kernel u a x * i15Hx4WordRate u w x| ≤
      (max 1 E * C) * x ^ (-(1 / 2) : ℝ) := by
    rw [abs_mul, mul_assoc]
    by_cases ha : a = .zero
    · subst a
      rw [i15Hx4Kernel, abs_of_pos (inv_pos.2 hx.1)]
      calc x⁻¹ * |i15Hx4WordRate u w x| ≤ x⁻¹ * (C * x ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hc u hu x hx) (inv_nonneg.2 hx.1.le)
        _ = C * x ^ (-(1 / 2) : ℝ) := by
          rw [show (-(1 / 2) : ℝ) = 1 / 2 - 1 by norm_num, rpow_sub_one hx.1.ne']
          field_simp
        _ ≤ max 1 E * (C * x ^ (-(1 / 2) : ℝ)) :=
          le_mul_of_one_le_left (mul_nonneg hC (rpow_nonneg hx.1.le _)) (le_max_left _ _)
    · exact mul_le_mul ((he u hu a ha x hx).trans (le_max_right _ _))
        ((hc u hu x hx).trans (mul_le_mul_of_nonneg_left
          (rpow_le_rpow_of_exponent_ge hx.1 hx1 (by norm_num)) hC)) (abs_nonneg _)
        (zero_le_one.trans (le_max_left _ _))
  rw [add_mul]
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

/-- The parameter derivative recursion vanishes at the lower endpoint, uniformly locally. -/
theorem i15Hx4WordRate_left_bound {d b : ℝ} (hd : 0 < d) (hb : b < 1)
    (w : List I15Hx4Letter) :
    ∃ C, 0 ≤ C ∧ ∀ u ∈ Icc d 1, ∀ x ∈ Ioc 0 b,
      |i15Hx4WordRate u w x| ≤ C * x ^ (1 / 2 : ℝ) := by
  induction w with
  | nil =>
      exact ⟨0, le_rfl, fun _ _ _ _ => by simp [i15Hx4WordRate]⟩
  | cons a w ih =>
    by_cases hz : (a :: w).all (· == .zero) = true
    · exact ⟨0, le_rfl, fun _ _ _ _ => by simp [i15Hx4WordRate, hz]⟩
    obtain ⟨C, hC, hc⟩ := i15Hx4_rate_integrand_bound hd hb a w ih
    refine ⟨2 * C, by positivity, fun u hu x hx => ?_⟩
    rw [i15Hx4WordRate_cons hz]
    have hI := abs_integral_le_of_le_rpow hx.1.le (by norm_num : (-1 : ℝ) < -(1 / 2))
      (K := C) fun t ht => hc u hu t ⟨ht.1, ht.2.trans hx.2⟩
    convert hI using 1
    norm_num
    ring

private theorem continuousOn_i15Hx4KernelD {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1)
    (a : I15Hx4Letter) : ContinuousOn (i15Hx4KernelD u a) (Ioo 0 1) := by
  have h (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :=
    i15Hx4_den_ge hu.2 ⟨ht.1.le, ht.2.le⟩
  cases a with
  | zero => exact continuousOn_const
  | one => exact continuousOn_const
  | pos =>
      exact (((continuousOn_const.add (continuousOn_const.mul continuousOn_id)).pow 2).inv₀
        (fun t ht => pow_ne_zero _ (hu.1.trans_le (h t ht).1).ne')).neg
  | neg =>
      exact ((continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).pow 2).inv₀
        (fun t ht => pow_ne_zero _ (hu.1.trans_le (h t ht).2).ne')

private theorem hasDerivAt_i15Hx4WordRate_of_continuous {u x : ℝ}
    (hu : u ∈ Ioc (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1)
    (a : I15Hx4Letter) (w : List I15Hx4Letter)
    (hc : ContinuousOn (i15Hx4WordRate u w) (Ioo 0 1)) :
    HasDerivAt (i15Hx4WordRate u (a :: w))
      (i15Hx4KernelD u a x * i15Hx4Word u w x +
        i15Hx4Kernel u a x * i15Hx4WordRate u w x) x := by
  by_cases hz : (a :: w).all (· == .zero) = true
  · have hsplit : a = .zero ∧ w.all (· == .zero) = true := by simpa using hz
    obtain ⟨rfl, hw⟩ := hsplit
    rw [show i15Hx4WordRate u (.zero :: w) = (fun _ => 0) from
      funext (fun _ => i15Hx4WordRate_allZero hz),
      i15Hx4KernelD, i15Hx4WordRate_allZero hw, zero_mul, mul_zero, add_zero]
    exact hasDerivAt_const x 0
  rw [i15Hx4WordRate_cons hz]
  have hcont := ((continuousOn_i15Hx4KernelD hu a).mul (continuousOn_i15Hx4Word hu w)).add
    ((i15Hx4Kernel_continuousOn hu a).mul hc)
  obtain ⟨K, _, hK⟩ := i15Hx4_rate_integrand_bound hu.1 hx.2 a w
    (i15Hx4WordRate_left_bound hu.1 hx.2 w)
  exact intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_of_le_rpow hx.1.le hx.2 hcont (hK u ⟨le_rfl, hu.2⟩))
    (hcont.stronglyMeasurableAtFilter isOpen_Ioo x hx)
    (hcont.continuousAt (isOpen_Ioo.mem_nhds hx))

/-- The integral rate recursion is continuous in the upper integration limit. -/
theorem continuousOn_i15Hx4WordRate {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1)
    (w : List I15Hx4Letter) : ContinuousOn (i15Hx4WordRate u w) (Ioo 0 1) := by
  induction w with
  | nil => exact continuousOn_const
  | cons a w ih =>
      exact fun _ hx =>
        (hasDerivAt_i15Hx4WordRate_of_continuous hu hx a w ih).continuousAt.continuousWithinAt

/-- The upper-limit derivative of the parameter rate is its recursive integrand. -/
theorem hasDerivAt_i15Hx4WordRate_cons {u x : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (a : I15Hx4Letter) (w : List I15Hx4Letter) :
    HasDerivAt (i15Hx4WordRate u (a :: w))
      (i15Hx4KernelD u a x * i15Hx4Word u w x +
        i15Hx4Kernel u a x * i15Hx4WordRate u w x) x :=
  hasDerivAt_i15Hx4WordRate_of_continuous hu hx a w (continuousOn_i15Hx4WordRate hu w)

/-- The parameter rates have the same sub-power growth as the signed words. -/
theorem i15Hx4WordRate_right_bound {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (w : List I15Hx4Letter) :
    ∃ C, 0 ≤ C ∧ ∀ u ∈ Icc d 1, ∀ x ∈ Ico (1 / 2 : ℝ) 1,
      |i15Hx4WordRate u w x| ≤ C * (1 - x) ^ (-ε) := by
  induction w with
  | nil => exact ⟨0, le_rfl, fun _ _ _ _ => by simp [i15Hx4WordRate]⟩
  | cons a w ih =>
    obtain ⟨C, hC, hc⟩ := ih
    obtain ⟨D, hD, hd'⟩ := i15Hx4Word_right_bound hd hε w
    obtain ⟨H, hH, hh⟩ := i15Hx4WordRate_left_bound hd (by norm_num : (1 / 2 : ℝ) < 1) (a :: w)
    let M := H * (1 / 2 : ℝ) ^ (1 / 2 : ℝ)
    let K := max (2 : ℝ) d⁻¹
    let E := (d ^ 2)⁻¹ * D + K * C
    have hK : 0 ≤ K := zero_le_two.trans (le_max_left _ _)
    have hM : 0 ≤ M := mul_nonneg hH (by positivity)
    have hE : 0 ≤ E := add_nonneg (mul_nonneg (by positivity) hD) (mul_nonneg hK hC)
    refine ⟨M + E / ε, add_nonneg hM (div_nonneg hE hε.le), fun u hu x hx => ?_⟩
    have hut : u ∈ Ioc (0 : ℝ) 1 := ⟨hd.trans_le hu.1, hu.2⟩
    refine i15Hx4_growth_of_deriv hx hε hM hE
      (fun _ ht => hasDerivAt_i15Hx4WordRate_cons hut ht a w)
      (((continuousOn_i15Hx4KernelD hut a).mul (continuousOn_i15Hx4Word hut w)).add
        ((i15Hx4Kernel_continuousOn hut a).mul (continuousOn_i15Hx4WordRate hut w)))
      (hh u hu _ ⟨by norm_num, le_rfl⟩) ?_
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have ht1 := sub_pos.2 ht.2
    rw [rpow_sub_one ht1.ne', div_eq_mul_inv]
    have hfirst := mul_le_mul (i15Hx4KernelD_bound hd hu ⟨ht0.le, ht.2.le⟩ a) (hd' u hu t ht)
      (abs_nonneg _) (by positivity)
    have hsecond := mul_le_mul (i15Hx4Kernel_right_bound hd hu ht a) (hc u hu t ht)
      (abs_nonneg _) (mul_nonneg hK (inv_nonneg.2 ht1.le))
    have hpow : 0 ≤ (1 - t) ^ (-ε) := rpow_nonneg ht1.le _
    have hle : 1 ≤ (1 - t)⁻¹ := (one_le_inv₀ ht1).2 (by linarith)
    calc |i15Hx4KernelD u a t * i15Hx4Word u w t +
          i15Hx4Kernel u a t * i15Hx4WordRate u w t|
        ≤ (d ^ 2)⁻¹ * (D * (1 - t) ^ (-ε)) +
            (K * (1 - t)⁻¹) * (C * (1 - t) ^ (-ε)) := by
          exact (abs_add_le _ _).trans (by simpa only [abs_mul] using add_le_add hfirst hsecond)
      _ ≤ E * ((1 - t) ^ (-ε) * (1 - t)⁻¹) := by
        dsimp only [E]
        have h := le_mul_of_one_le_right
          (mul_nonneg (mul_nonneg (by positivity : 0 ≤ (d ^ 2)⁻¹) hD) hpow) hle
        linarith only [h,
          show (d ^ 2)⁻¹ * (D * (1 - t) ^ (-ε)) +
                (K * (1 - t)⁻¹) * (C * (1 - t) ^ (-ε)) -
                ((d ^ 2)⁻¹ * D + K * C) * ((1 - t) ^ (-ε) * (1 - t)⁻¹) =
              (d ^ 2)⁻¹ * D * (1 - t) ^ (-ε) -
                (d ^ 2)⁻¹ * D * (1 - t) ^ (-ε) * (1 - t)⁻¹ by ring]

private theorem i15Hx4_rate_integrand_dom {a : I15Hx4Letter} {d x : ℝ}
    (hd : 0 < d) (hx : x ∈ Ioc (0 : ℝ) 1) (ha : x < 1 ∨ a ≠ .one) (w : List I15Hx4Letter) :
    ∃ B : ℝ → ℝ, IntegrableOn B (Ioo 0 x) ∧
      ∀ u ∈ Icc d 1, ∀ t ∈ Ioo 0 x, |i15Hx4KernelD u a t * i15Hx4Word u w t +
        i15Hx4Kernel u a t * i15Hx4WordRate u w t| ≤ B t := by
  rcases ha with hlt | hne
  · obtain ⟨C, _, hc⟩ := i15Hx4_rate_integrand_bound hd hlt a w
      (i15Hx4WordRate_left_bound hd hlt w)
    refine ⟨fun t => C * t ^ (-(1 / 2) : ℝ), ?_, fun u hu t ht => hc u hu t ⟨ht.1, ht.2.le⟩⟩
    rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le hx.1.le]
    exact (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul C
  · have hhalf : (1 / 2 : ℝ) < 1 := by norm_num
    obtain ⟨C, hC, hc⟩ := i15Hx4_rate_integrand_bound hd hhalf a w
      (i15Hx4WordRate_left_bound hd hhalf w)
    obtain ⟨D, hD, hw⟩ := i15Hx4Word_right_bound hd (by norm_num : (0 : ℝ) < 1 / 2) w
    obtain ⟨E, hE, hr⟩ := i15Hx4WordRate_right_bound hd (by norm_num : (0 : ℝ) < 1 / 2) w
    let K := max (2 : ℝ) d⁻¹
    have hK : 0 ≤ K := zero_le_two.trans (le_max_left _ _)
    refine i15Hx4_dom_split hx.2 hC
      (add_nonneg (mul_nonneg (by positivity : 0 ≤ (d ^ 2)⁻¹) hD) (mul_nonneg hK hE)) hc ?_
    intro u hu t ht
    have ht0 : 0 < t := by linarith [ht.1]
    rw [add_mul]
    exact (abs_add_le _ _).trans (add_le_add (by
      rw [abs_mul, mul_assoc]
      exact mul_le_mul (i15Hx4KernelD_bound hd hu ⟨ht0.le, ht.2.le⟩ a) (hw u hu t ht)
        (abs_nonneg _) (by positivity)) (by
      rw [abs_mul, mul_assoc]
      exact mul_le_mul (i15Hx4Kernel_right_bound_of_ne_one hd hu ht hne) (hr u hu t ht)
        (abs_nonneg _) hK))

/-- Differentiate a signed word in its parameter, including convergent right endpoints. -/
theorem hasDerivAt_i15Hx4Word_param (w : List I15Hx4Letter) {u x : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioc (0 : ℝ) 1)
    (hw : x < 1 ∨ w.head? ≠ some .one) :
    HasDerivAt (fun v => i15Hx4Word v w x) (i15Hx4WordRate u w x) u := by
  induction w generalizing u x with
  | nil => exact hasDerivAt_const u 1
  | cons a w ih =>
    by_cases hz : (a :: w).all (· == .zero) = true
    · simp_rw [i15Hx4Word_allZero hz, i15Hx4WordRate_allZero hz]
      exact hasDerivAt_const u _
    let d := u / 2
    have hd : 0 < d := by dsimp [d]; linarith [hu.1]
    have hdu : d ≤ u := by dsimp [d]; linarith [hu.1]
    have ha : x < 1 ∨ a ≠ .one := hw.imp_right (fun h => by simpa using h)
    obtain ⟨B, hB, hdom⟩ := i15Hx4Word_kernel_dom hd hx ha hz
    obtain ⟨M, hM, hK⟩ := i15Hx4_rate_integrand_dom hd hx ha w
    let g := fun t v => i15Hx4Kernel v a t * i15Hx4Word v w t
    let g' := fun t v => i15Hx4KernelD v a t * i15Hx4Word v w t +
      i15Hx4Kernel v a t * i15Hx4WordRate v w t
    have hm (v : ℝ) (hv : v ∈ Ioo (0 : ℝ) 1) :
        AEStronglyMeasurable (g · v) (volume.restrict (Ioo 0 x)) := by
      have hv' : v ∈ Ioc (0 : ℝ) 1 := ⟨hv.1, hv.2.le⟩
      exact (((i15Hx4Kernel_continuousOn hv' a).mul (continuousOn_i15Hx4Word hv' w)).mono
        (Ioo_subset_Ioo_right hx.2)).aestronglyMeasurable measurableSet_Ioo
    have hi : IntegrableOn (g · u) (Ioo 0 x) := hB.mono' (hm u hu)
      ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun t ht => by
        rw [Real.norm_eq_abs]
        exact hdom u ⟨hdu, hu.2.le⟩ t ht))
    have hu' : u ∈ Ioc (0 : ℝ) 1 := ⟨hu.1, hu.2.le⟩
    have hm' : AEStronglyMeasurable (g' · u) (volume.restrict (Ioo 0 x)) :=
      ((((continuousOn_i15Hx4KernelD hu' a).mul (continuousOn_i15Hx4Word hu' w)).add
        ((i15Hx4Kernel_continuousOn hu' a).mul (continuousOn_i15Hx4WordRate hu' w))).mono
        (Ioo_subset_Ioo_right hx.2)).aestronglyMeasurable measurableSet_Ioo
    have hav := QED.Polylog.ParamHPL.hasDerivAt_setIntegral_param measurableSet_Ioo hu hm
      hi hm' hd hM
      (fun t ht v hv hnear => hK v
        ⟨by have := (abs_lt.1 hnear).1; dsimp [d] at *; linarith, hv.2.le⟩ t ht)
      (fun t ht v hv => (hasDerivAt_i15Hx4Kernel_param a hv ⟨ht.1, ht.2.trans_le hx.2⟩).mul
        (ih hv ⟨ht.1, ht.2.le.trans hx.2⟩ (Or.inl (ht.2.trans_le hx.2))))
    simp_rw [i15Hx4Word_cons_integral hz, i15Hx4WordRate_cons hz,
      intervalIntegral.integral_of_le hx.1.le, integral_Ioc_eq_integral_Ioo]
    exact hav.2

/-- The parameter rate tends to zero at the left slice endpoint. -/
theorem tendsto_i15Hx4WordRate_zero {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1)
    (w : List I15Hx4Letter) :
    Tendsto (i15Hx4WordRate u w) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, _, hc⟩ := i15Hx4WordRate_left_bound hu.1 (by norm_num : (1 / 2 : ℝ) < 1) w
  exact tendsto_zero_of_abs_le_rpow (C := C) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num) (hc u ⟨le_rfl, hu.2⟩)

/-- A convergent word's parameter rate is continuous up to the right slice endpoint. -/
theorem tendsto_i15Hx4WordRate_one {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1)
    {w : List I15Hx4Letter} (hw : w.head? ≠ some .one) :
    Tendsto (i15Hx4WordRate u w) (𝓝[<] 1) (𝓝 (i15Hx4WordRate u w 1)) := by
  by_cases hz : w.all (· == .zero) = true
  · rw [show i15Hx4WordRate u w = fun _ => 0 from
      funext (fun _ => i15Hx4WordRate_allZero hz)]
    exact tendsto_const_nhds
  cases w with
  | nil => exact (hz rfl).elim
  | cons a w =>
    have ha : a ≠ .one := by simpa using hw
    obtain ⟨B, hB, hb⟩ := i15Hx4_rate_integrand_dom hu.1
      (x := 1) ⟨zero_lt_one, le_rfl⟩ (Or.inr ha) w
    let g := fun t => i15Hx4KernelD u a t * i15Hx4Word u w t +
      i15Hx4Kernel u a t * i15Hx4WordRate u w t
    have hc : ContinuousOn g (Ioo (0 : ℝ) 1) :=
      ((continuousOn_i15Hx4KernelD hu a).mul (continuousOn_i15Hx4Word hu w)).add
        ((i15Hx4Kernel_continuousOn hu a).mul (continuousOn_i15Hx4WordRate hu w))
    have hg : IntervalIntegrable g volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
      apply hB.mono' (hc.aestronglyMeasurable measurableSet_Ioo)
      refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun t ht => ?_)
      rw [Real.norm_eq_abs]
      exact hb u ⟨le_rfl, hu.2⟩ t ht
    rw [i15Hx4WordRate_cons hz]
    have hcont := intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc
    rw [uIcc_of_le zero_le_one] at hcont
    exact (hcont 1 (right_mem_Icc.2 zero_le_one)).mono_left
      (nhdsWithin_le_of_mem (by
        filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with t ht
        exact ⟨ht.1.le, ht.2.le⟩))

end QED.ThreeLoopD
