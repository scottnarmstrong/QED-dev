/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12Def
public import QED.Polylog.HPLShuffle
public import QED.Polylog.HPLLowWeight
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Set (d), master `I₁₂`: the Taylor coefficients of `P(cε - 1, ε)` as alternating HPLs

The Taylor coefficients of `ε ↦ P(cε - 1, ε)` at `0` are the integrals over `(0, 1)` of

  `F_{c,n}(x) = (log x + c log h(x)) ^ n / (x h(x)) - (log x + c log h(0)) ^ n / (x h(0))`,

`h(x) = (2 - x)/4` (`QED.ThreeLoopD.iteratedDeriv_i12HSP_lin`). The substitution
`x = 2t/(1 + t)` maps `(0, 1)` onto itself, with `log x = log 2 + log t - log (1 + t)`,
`log h(x) = -(log 2 + log (1 + t))`, `dx/(x h(x)) = 2 dt/t` and
`dx/(x h(0)) = 2 (1/t - 1/(1 + t)) dt`, so (`QED.ThreeLoopD.i12HSK_integral_F_eq`)

  `∫₀¹ F_{c,n} = ∫₀¹ G_{c,n}`, `G_{c,n}(t) = 2 ((L - c(log 2 + log (1 + t))) ^ n / t
    - (L - c log 2) ^ n (1/t - 1/(1 + t)))`, `L = log 2 + log t - log (1 + t)`.

`G_{c,n}` is a combination of the functions `f_a(t) logⁱ t logʲ (1 + t)` with
`f_0(t) = 1/t` (only with `j ≥ 1`: the `j = 0` terms cancel) and `f_{-1}(t) = 1/(1 + t)`.
Since `logⁱ t = i! H(0ⁱ; t)`, `logʲ (1 + t) = j! H((-1)ʲ; t)` and by the shuffle product,

  `∫₀¹ f_a(t) logⁱ t logʲ (1 + t) dt = i! j! ∑_{w ∈ 0ⁱ ⧢ (-1)ʲ} H(a w; 1)`

(`QED.ThreeLoopD.i12HSK_eq`), alternating harmonic polylogarithms at `1`.

## Main results

* `QED.ThreeLoopD.hpl_replicate_negOne_eq`: `H((-1)ʲ; x) = logʲ (1 + x) / j!`.
* `QED.ThreeLoopD.i12HSK_eq`: the integrals `i12HSK a i j` as sums of HPLs at `1`.
* `QED.ThreeLoopD.i12HSK_integral_combo`: linearity over a list of such integrands.
* `QED.ThreeLoopD.i12HSK_integral_F_eq`: the substitution `x = 2t/(1 + t)`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology
open QED.Polylog QED.Polylog.HPL

namespace QED.ThreeLoopD

/-- `H((-1)ʲ; x) = logʲ (1 + x) / j!` on `(0, 1)`. -/
theorem hpl_replicate_negOne_eq (j : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl (List.replicate j Letter.negOne) x = log (1 + x) ^ j / (j.factorial : ℝ) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ]
    refine eq_hpl_cons_of_hasDerivAt (a := Letter.negOne) (by simp)
      (F := fun y => log (1 + y) ^ (j + 1) / ((j + 1).factorial : ℝ)) (fun y hy => ?_)
      (tendsto_nhdsGT_of_continuousAt (c := 0) (by fun_prop (disch := norm_num))
        (by simp)) x hx
    have h1 : (1 : ℝ) + y ≠ 0 := by linarith [hy.1]
    refine ((((hasDerivAt_id y).const_add 1).log h1).pow (j + 1) |>.div_const _).congr_deriv ?_
    rw [Letter.kernel_negOne, ih hy, Nat.factorial_succ]
    simp only [id]
    push_cast
    field_simp

theorem allZero_replicate_zero (i : ℕ) : AllZero (List.replicate i Letter.zero) :=
  fun _ ha => List.eq_of_mem_replicate ha

/-- `logⁱ t logʲ (1 + t) = i! j! ∑_{w ∈ 0ⁱ ⧢ (-1)ʲ} H(w; t)` on `(0, 1)`. -/
theorem i12HSK_log_pow_eq (i j : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    log t ^ i * log (1 + t) ^ j = (i.factorial * j.factorial : ℝ) *
      ((shuffle (List.replicate i Letter.zero) (List.replicate j Letter.negOne)).map
        fun w => hpl w t).sum := by
  rw [← hpl_mul_hpl _ _ ht, hpl_of_allZero (allZero_replicate_zero i) t,
    hpl_replicate_negOne_eq j ht, List.length_replicate]
  have h1 : (i.factorial : ℝ) ≠ 0 := by positivity
  have h2 : (j.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- Integrability and integral of `f_a ∑_{w ∈ L} H(w)` over `(0, 1)`, when no `a w` is all
zeros and `a ≠ 1`. -/
theorem i12HSK_integral_list (a : Letter) (ha : a ≠ Letter.one) :
    ∀ L : List (List Letter), (∀ w ∈ L, ¬AllZero (a :: w)) →
      IntegrableOn (fun t => a.kernel t * (L.map fun w => hpl w t).sum) (Ioo 0 1) ∧
        ∫ t in Ioo (0 : ℝ) 1, a.kernel t * (L.map fun w => hpl w t).sum =
          (L.map fun w => hpl (a :: w) 1).sum
  | [], _ => by simp
  | w :: L, h => by
    obtain ⟨hI, hE⟩ := i12HSK_integral_list a ha L fun v hv => h v (List.mem_cons_of_mem _ hv)
    have hw := h w List.mem_cons_self
    have hI1 : IntegrableOn (fun t => a.kernel t * hpl w t) (Ioo 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1
        (intervalIntegrable_kernel_mul_hpl_one ha hw)
    have e : (fun t => a.kernel t * ((w :: L).map fun w => hpl w t).sum) =
        fun t => a.kernel t * hpl w t + a.kernel t * (L.map fun w => hpl w t).sum := by
      funext t; simp [mul_add]
    rw [e]
    refine ⟨hI1.add hI, ?_⟩
    rw [integral_add hI1 hI, hE, List.map_cons, List.sum_cons, hpl_cons_of_not_allZero hw]
    dsimp only
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

/-- `∫₀¹ f_a(t) logⁱ t logʲ (1 + t) dt`. -/
noncomputable def i12HSK (a : Letter) (i j : ℕ) : ℝ :=
  ∫ t in Ioo (0 : ℝ) 1, a.kernel t * (log t ^ i * log (1 + t) ^ j)

/-- The admissible integrands: `a ≠ 1`, and `j ≥ 1` if `a = 0`. -/
def i12HSKOk (q : Letter × ℕ × ℕ) : Prop :=
  q.1 ≠ Letter.one ∧ (q.1 ≠ Letter.zero ∨ q.2.2 ≠ 0)

instance (q : Letter × ℕ × ℕ) : Decidable (i12HSKOk q) := by
  unfold i12HSKOk; infer_instance

/-- **The integrals `i12HSK a i j` as alternating HPLs at `1`**:
`∫₀¹ f_a(t) logⁱ t logʲ (1 + t) dt = i! j! ∑_{w ∈ 0ⁱ ⧢ (-1)ʲ} H(a w; 1)`. -/
theorem i12HSK_eq {a : Letter} {i j : ℕ} (h : i12HSKOk (a, i, j)) :
    IntegrableOn (fun t => a.kernel t * (log t ^ i * log (1 + t) ^ j)) (Ioo 0 1) ∧
      i12HSK a i j = (i.factorial * j.factorial : ℝ) *
        ((shuffle (List.replicate i Letter.zero) (List.replicate j Letter.negOne)).map
          fun w => hpl (a :: w) 1).sum := by
  obtain ⟨ha, hz⟩ := h
  set L := shuffle (List.replicate i Letter.zero) (List.replicate j Letter.negOne)
  have hL : ∀ w ∈ L, ¬AllZero (a :: w) := by
    intro w hw hz'
    rw [allZero_cons] at hz'
    have h2 := ((allZero_of_mem_shuffle_iff hw).1 hz'.2).2
    rcases hz with hz | hz
    · exact hz hz'.1
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
      exact absurd (h2 Letter.negOne (by simp)) (by decide)
  obtain ⟨hI, hE⟩ := i12HSK_integral_list a ha L hL
  have hc : EqOn (fun t => a.kernel t * (log t ^ i * log (1 + t) ^ j))
      (fun t => (i.factorial * j.factorial : ℝ) *
        (a.kernel t * (L.map fun w => hpl w t).sum)) (Ioo 0 1) := fun t ht => by
    simp only [i12HSK_log_pow_eq i j ht]
    ring
  refine ⟨IntegrableOn.congr_fun (hI.const_mul _) hc.symm measurableSet_Ioo, ?_⟩
  rw [i12HSK, setIntegral_congr_fun measurableSet_Ioo hc, integral_const_mul, hE]

/-- **Linearity**: `∫₀¹ ∑_{(k, a, i, j) ∈ L} k f_a logⁱ t logʲ (1 + t) = ∑ k i12HSK a i j`. -/
theorem i12HSK_integral_combo :
    ∀ L : List (ℝ × Letter × ℕ × ℕ), (∀ q ∈ L.map Prod.snd, i12HSKOk q) →
      IntegrableOn (fun t => (L.map fun q =>
          q.1 * (q.2.1.kernel t * (log t ^ q.2.2.1 * log (1 + t) ^ q.2.2.2))).sum) (Ioo 0 1) ∧
        ∫ t in Ioo (0 : ℝ) 1, (L.map fun q =>
          q.1 * (q.2.1.kernel t * (log t ^ q.2.2.1 * log (1 + t) ^ q.2.2.2))).sum =
          (L.map fun q => q.1 * i12HSK q.2.1 q.2.2.1 q.2.2.2).sum
  | [], _ => by simp
  | q :: L, h => by
    obtain ⟨hI, hE⟩ := i12HSK_integral_combo L fun r hr =>
      h r (List.mem_cons_of_mem _ hr)
    obtain ⟨hI1, -⟩ := i12HSK_eq (a := q.2.1) (i := q.2.2.1) (j := q.2.2.2)
      (h q.2 List.mem_cons_self)
    have hI1' := hI1.const_mul q.1
    simp only [List.map_cons, List.sum_cons]
    refine ⟨hI1'.add hI, ?_⟩
    rw [integral_add hI1' hI, hE, integral_const_mul]
    rfl

/-! ### The substitution `x = 2t/(1 + t)` -/

/-- The real integrand `F_{c,n}` of the `n`-th Taylor coefficient of `P(cε - 1, ε)`. -/
noncomputable def i12HSKF (c : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (log x + c * log (i12H x)) ^ n / (x * i12H x) -
    (log x + c * log (i12H 0)) ^ n / (x * i12H 0)

/-- The integrand after `x = 2t/(1 + t)`:
`2 ((L - c(log 2 + log (1 + t))) ^ n / t - (L - c log 2) ^ n (1/t - 1/(1 + t)))`. -/
noncomputable def i12HSKG (c : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  2 * ((log 2 + log t - log (1 + t) - c * (log 2 + log (1 + t))) ^ n * t⁻¹ -
    (log 2 + log t - log (1 + t) - c * log 2) ^ n * (t⁻¹ - (1 + t)⁻¹))

theorem i12HSK_image : (fun t : ℝ => 2 * t / (1 + t)) '' Ioo 0 1 = Ioo 0 1 := by
  ext x
  simp only [mem_image, mem_Ioo]
  constructor
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
    have h2 : 0 < 1 + t := by linarith
    exact ⟨by positivity, by rw [div_lt_one h2]; linarith⟩
  · rintro ⟨h0, h1⟩
    have h2 : 0 < 2 - x := by linarith
    refine ⟨x / (2 - x), ⟨by positivity, by rw [div_lt_one h2]; linarith⟩, ?_⟩
    field_simp
    ring

theorem i12HSK_pointwise (c : ℝ) (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    |2 / (1 + t) ^ 2| * i12HSKF c n (2 * t / (1 + t)) = i12HSKG c n t := by
  have h0 : 0 < t := ht.1
  have h1 : 0 < 1 + t := by linarith
  have hx : log (2 * t / (1 + t)) = log 2 + log t - log (1 + t) := by
    rw [log_div (by positivity) h1.ne', log_mul (by norm_num) h0.ne']
  have hhx : i12H (2 * t / (1 + t)) = 1 / (2 * (1 + t)) := by
    unfold i12H; field_simp; ring
  have hh0 : i12H 0 = 1 / 2 := by unfold i12H; norm_num
  have hlx : log (i12H (2 * t / (1 + t))) = -(log 2 + log (1 + t)) := by
    rw [hhx, one_div, log_inv, log_mul (by norm_num) h1.ne']
  have hl0 : log (i12H 0) = -log 2 := by rw [hh0, one_div, log_inv]
  rw [abs_of_pos (by positivity), i12HSKF, hx, hlx, hl0, hhx, hh0, i12HSKG,
    show log 2 + log t - log (1 + t) + c * -(log 2 + log (1 + t)) =
      log 2 + log t - log (1 + t) - c * (log 2 + log (1 + t)) by ring,
    show log 2 + log t - log (1 + t) + c * -log 2 = log 2 + log t - log (1 + t) - c * log 2 by
      ring]
  generalize (log 2 + log t - log (1 + t) - c * (log 2 + log (1 + t))) ^ n = A
  generalize (log 2 + log t - log (1 + t) - c * log 2) ^ n = B
  field_simp
  ring

/-- **The substitution `x = 2t/(1 + t)`**: `∫₀¹ F_{c,n} = ∫₀¹ G_{c,n}`. -/
theorem i12HSK_integral_F_eq (c : ℝ) (n : ℕ) :
    ∫ x in Ioo (0 : ℝ) 1, i12HSKF c n x = ∫ t in Ioo (0 : ℝ) 1, i12HSKG c n t := by
  have hder : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt (fun t : ℝ => 2 * t / (1 + t))
      (2 / (1 + t) ^ 2) (Ioo 0 1) t := by
    intro t ht
    have h1 : (1 : ℝ) + t ≠ 0 := by linarith [ht.1]
    refine (((hasDerivAt_id t).const_mul 2).div ((hasDerivAt_id t).const_add 1) h1).congr_deriv
      ?_ |>.hasDerivWithinAt
    simp only [id]
    field_simp
    ring
  have hinj : InjOn (fun t : ℝ => 2 * t / (1 + t)) (Ioo 0 1) := by
    intro a ha b hb hab
    have h1 : (1 : ℝ) + a ≠ 0 := by linarith [ha.1]
    have h2 : (1 : ℝ) + b ≠ 0 := by linarith [hb.1]
    simp only at hab
    field_simp at hab
    linarith
  rw [← i12HSK_image, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hder hinj,
    i12HSK_image]
  exact setIntegral_congr_fun measurableSet_Ioo fun t ht => by
    rw [smul_eq_mul, i12HSK_pointwise c n ht]

end QED.ThreeLoopD
