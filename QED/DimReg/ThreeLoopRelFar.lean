/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopTmplFar
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Relations among the face values `val3` from relations at convergent points

The argument of `QED.DimReg.ThreeLoop.eventually_tmpl_far` and
`QED.DimReg.ThreeLoop.ibpHoldsAt_val3`, for an arbitrary finite relation with dimension shifts.
Let `T` be a finite list of terms `t`, each with a label shift `σ_t ∈ ℤ⁹` (entries in
`[-1, B]`), a dimension shift `2 j_t` and a coefficient `a_t(ν, d)` holomorphic in `(ν, d)`.
Suppose that at every point `(ν, d)` with `re d > 0` where the integrals of
`QED.DimReg.ThreeLoop.Shifted` converge,
`Σ_t a_t(ν, d) N(ν + σ_t, d + 2j_t) J(ν + σ_t, d + 2j_t) = 0` (`N = normLP`, `J` the nine-variable
Lee–Pomeransky integral). Let `n` be a label with `n₇, n₈ ≤ 0`, and suppose that a term raising
`ν₇` or `ν₈` to a positive value has coefficient `0` at `ν_k = n_k`. Then:

* `eventually_rel_far`: for `re λ` large,
  `Σ_t a_t(ν(λ), d(λ)) · Iline3 (n + σ_t) (d₀ + 2j_t) λ = 0` along the line
  `(ν', ν₇, ν₈, d) = (n' + λw₇, n₇, n₈, d₀ + 6λ)` (continuation in `s₇`, then in `s₈`, from the
  strip `1 < re s < 2` by the identity theorem, and the face theorem
  `QED.DimReg.ThreeLoop.eventually_norm9_mul_cont9` at `(n₇, n₈)`);
* `rel_val3`: for `d₀ ∉ ℚ`, `Σ_t a_t(n, d₀) · val3 (n + σ_t) (d₀ + 2j_t) = 0`.
-/

@[expose] public section

open Complex Filter Topology Set MeasureTheory QED.DimReg QED.DimReg.Sector QED.DimReg.LineCont
open QED.DimReg.TwoLoopSESector (atRe eventually_list eventually_re_gt halfPlane
  zero_mem_halfPlane Irr eventuallyEq_nhdsNE_of_atRe meromorphicOn_list_sum)

namespace QED.DimReg.ThreeLoop

/-! ### Shifts and points along the line -/

/-- An integer shift as a complex vector. -/
def shZ (σ : Fin 9 → ℤ) : Fin 9 → ℂ := fun k => ((σ k : ℤ) : ℂ)

theorem nu9_add_shZ (n σ : Fin 9 → ℤ) (l s₇ s₈ : ℂ) :
    nu9 (lineNu w7 (lbl3 n []) l) s₇ s₈ + shZ σ =
      nu9 (lineNu w7 (lbl3 (n + σ) []) l) (s₇ + σ 7) (s₈ + σ 8) := by
  funext i
  induction i using Fin.lastCases with
  | last => rfl
  | cast j =>
    induction j using Fin.lastCases with
    | last => rfl
    | cast b =>
      simp only [Pi.add_apply, nu9_castSucc, lineNu, lbl3_nil, shZ]
      push_cast
      ring_nf
      rfl

theorem lineD_add_two_mul (d₀ l : ℂ) (j : ℕ) :
    lineD h7 (d₀ + 2 * j) l = lineD h7 d₀ l + 2 * j := by
  simp only [lineD]; ring

theorem differentiable_nu9_seven (ν : Fin 7 → ℂ) (c : ℂ) :
    Differentiable ℂ fun s => nu9 ν s c := by
  have e : (fun s => nu9 ν s c) = fun s => Function.update (nu9 ν 0 c) 7 s :=
    funext fun s => update_nu9_seven_zero ν s c
  rw [e]
  exact fun s => (hasFDerivAt_update (nu9 ν 0 c) s).differentiableAt

theorem differentiable_nu9_eight (ν : Fin 7 → ℂ) (a : ℂ) :
    Differentiable ℂ fun s => nu9 ν a s := by
  have e : (fun s => nu9 ν a s) = fun s => Function.update (nu9 ν a 0) 8 s :=
    funext fun s => update_nu9_eight_zero ν a s
  rw [e]
  exact fun s => (hasFDerivAt_update (nu9 ν a 0) s).differentiableAt

theorem differentiable_nu9_line (m : Fin 7 → ℤ) (a c : ℂ) :
    Differentiable ℂ fun l => nu9 (lineNu w7 m l) a c := by
  refine differentiable_pi.2 fun k => ?_
  induction k using Fin.lastCases with
  | last => exact differentiable_const _
  | cast j =>
    induction j using Fin.lastCases with
    | last => exact differentiable_const _
    | cast b =>
      simp only [nu9_castSucc]
      unfold lineNu; fun_prop

theorem re_add_intCast (s : ℂ) (k : ℤ) : (s + (k : ℂ)).re = s.re + k := by simp

/-! ### The relation at large exponent -/

variable {β : Type*}

/-- **A relation for `Iline3` at large exponent**, from the same relation for the normalized
nine-variable integrals at convergent points (labels with `n₇, n₈ ≤ 0`). -/
theorem eventually_rel_far (T : List β) (σ : β → Fin 9 → ℤ) (j : β → ℕ)
    (a : β → (Fin 9 → ℂ) → ℂ → ℂ) (B : ℕ)
    (hσ : ∀ t ∈ T, ∀ k, -1 ≤ σ t k ∧ σ t k ≤ B)
    (ha : ∀ t ∈ T, Differentiable ℂ fun p : (Fin 9 → ℂ) × ℂ => a t p.1 p.2)
    (hrel : ∀ (ν : Fin 9 → ℂ) (d : ℂ), 0 < d.re →
      (∀ μ e, Shifted ν d μ e → LPConvergent (fun x => lpPoly.eval x) μ e) →
      (T.map fun t => a t ν d * (normLP (ν + shZ (σ t)) (d + 2 * j t) *
        lpIntegral (fun x => lpPoly.eval x) (ν + shZ (σ t)) (d + 2 * j t))).sum = 0)
    (n : Fin 9 → ℤ) (hn7 : n 7 ≤ 0) (hn8 : n 8 ≤ 0)
    (hz : ∀ t ∈ T, ∀ k : Fin 9, (k = 7 ∨ k = 8) → n k ≤ 0 → 0 < n k + σ t k →
      ∀ ν d, ν k = (n k : ℂ) → a t ν d = 0)
    (d₀ : ℂ) :
    ∀ᶠ l in atRe, (T.map fun t =>
      a t (nu9 (lineNu w7 (lbl3 n []) l) (n 7) (n 8)) (lineD h7 d₀ l) *
        Iline3 (n + σ t) (d₀ + 2 * j t) l).sum = 0 := by
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  filter_upwards [eventually_list T fun t =>
      eventually_lpIntegral_eq_cont9 (n + σ t) (d₀ + 2 * j t) (B + 2),
    eventually_lpConvergent9 (lbl3 n []) d₀ 8,
    eventually_list T fun t =>
      eventually_differentiableOn_cont9_seven (n + σ t) (d₀ + 2 * j t) (M := B + 4)
        (by positivity),
    eventually_list T fun t =>
      eventually_differentiableOn_cont9_eight (n + σ t) (d₀ + 2 * j t) (M := B + 4)
        (by positivity),
    eventually_list T fun t => eventually_norm9_mul_cont9 (n + σ t) (d₀ + 2 * j t),
    eventually_re_gt (|d₀.re| + 1)]
    with l hE hC hD7 hD8 hF hre
  set ν' := lineNu w7 (lbl3 n []) l
  set d := lineD h7 d₀ l
  set V : β → ℂ → ℂ → ℂ := fun t s₇ s₈ =>
    pf9 (lbl3 (n + σ t) []) (d₀ + 2 * j t) l (s₇ + σ t 7) (s₈ + σ t 8) *
      cont9 (n + σ t) (d₀ + 2 * j t) l (s₇ + σ t 7) (s₈ + σ t 8) with hV
  set Φ : ℂ → ℂ → ℂ := fun s₇ s₈ =>
    (T.map fun t => a t (nu9 ν' s₇ s₈) d * V t s₇ s₈).sum with hΦ
  have hσR : ∀ t ∈ T, ∀ k, (-1 : ℝ) ≤ σ t k ∧ (σ t k : ℝ) ≤ B := fun t ht k => by
    obtain ⟨h1, h2⟩ := hσ t ht k
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hn7' : (n 7 : ℝ) ≤ 0 := by exact_mod_cast hn7
  have hn8' : (n 8 : ℝ) ≤ 0 := by exact_mod_cast hn8
  have hm7 : ∀ t, (((n + σ t) 7 : ℤ) : ℝ) = n 7 + σ t 7 := fun t => by simp
  have hm8 : ∀ t, (((n + σ t) 8 : ℤ) : ℝ) = n 8 + σ t 8 := fun t => by simp
  have hdre : 0 < d.re := by
    have : d.re = d₀.re + 6 * l.re := by norm_num [d, lineD, ThreeLoop.h7]
    rw [this]
    linarith [neg_abs_le d₀.re, abs_nonneg d₀.re]
  have hca : ∀ t ∈ T, ∀ c : ℂ, Differentiable ℂ fun s => a t (nu9 ν' s c) d := fun t ht c =>
    (ha t ht).comp ((differentiable_nu9_seven ν' c).prodMk (differentiable_const _))
  have hcb : ∀ t ∈ T, ∀ c : ℂ, Differentiable ℂ fun s => a t (nu9 ν' c s) d := fun t ht c =>
    (ha t ht).comp ((differentiable_nu9_eight ν' c).prodMk (differentiable_const _))
  -- Step 1: the relation where all integrals converge
  have step1 : ∀ s₇ s₈ : ℂ, 1 < s₇.re → s₇.re < 2 → 1 < s₈.re → s₈.re < 2 → Φ s₇ s₈ = 0 := by
    intro s₇ s₈ h1 h2 h3 h4
    have H := hrel (nu9 ν' s₇ s₈) d hdre fun μ e hμ =>
      hC μ e (near9_of_shifted h1 h2 h3 h4 hμ)
    rw [← H]
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    congr 1
    have b7 := hσR t ht 7
    have b8 := hσR t ht 8
    have hE' := hE t ht (s₇ + σ t 7) (s₈ + σ t 8)
      (by rw [re_add_intCast]; linarith [b7.1]) (by rw [re_add_intCast]; linarith [b7.2])
      (by rw [re_add_intCast]; linarith [b8.1]) (by rw [re_add_intCast]; linarith [b8.2])
    rw [nu9_add_shZ, ← lineD_add_two_mul, normLP_nu9, hV]
    simp only
    rw [← hE']
    ring
  -- Step 2: continuation in `s₇`
  have step2 : ∀ s₈ : ℂ, 1 < s₈.re → s₈.re < 2 → Φ (n 7) s₈ = 0 := by
    intro s₈ h3 h4
    refine eqOn_zero_strip (f := fun s => Φ s s₈) (a := (n 7 : ℝ) - 1 / 2) (b := 3)
      (by linarith) (by norm_num) ?_ (fun s h1 h2 => step1 s s₈ h1 h2 h3 h4) ?_
    · refine differentiableOn_list_sum' T fun t ht => ?_
      refine ((hca t ht s₈).differentiableOn).mul ?_
      have b7 := hσR t ht 7
      have b8 := hσR t ht 8
      have hmaps : MapsTo (fun s : ℂ => s + (σ t 7 : ℂ))
          {s | (n 7 : ℝ) - 1 / 2 < s.re ∧ s.re < 3}
          {a | -(ord7 (n + σ t) : ℝ) - 1 / 2 < a.re ∧ a.re < B + 4} := by
        intro s hs
        simp only [mem_ofPred_eq, re_add_intCast] at hs ⊢
        have := neg_ord7_le (n + σ t)
        rw [hm7 t] at this
        constructor <;> linarith [hs.1, hs.2, b7.2]
      have hc := (hD7 t ht (s₈ + σ t 8) (by
          rw [re_add_intCast]
          linarith [b8.1, (Nat.cast_nonneg _ : (0 : ℝ) ≤ ord8 (n + σ t))])
        (by rw [re_add_intCast]; linarith [b8.2])).comp
        ((differentiable_id.add (differentiable_const _)).differentiableOn) hmaps
      exact ((differentiable_pf9_seven _ _ l _).comp
        (differentiable_id.add (differentiable_const _))).differentiableOn.mul hc
    · simp only [intCast_re]
      constructor <;> linarith
  -- Step 3: continuation in `s₈`
  have step3 : Φ (n 7) (n 8) = 0 := by
    refine eqOn_zero_strip (f := fun s => Φ (n 7) s) (a := (n 8 : ℝ) - 1 / 2) (b := 3)
      (by linarith) (by norm_num) ?_ (fun s h1 h2 => step2 s h1 h2) ?_
    · refine differentiableOn_list_sum' T fun t ht => ?_
      refine ((hcb t ht (n 7)).differentiableOn).mul ?_
      have b7 := hσR t ht 7
      have b8 := hσR t ht 8
      have hmaps : MapsTo (fun s : ℂ => s + (σ t 8 : ℂ))
          {s | (n 8 : ℝ) - 1 / 2 < s.re ∧ s.re < 3}
          {c | -(ord8 (n + σ t) : ℝ) - 1 / 2 < c.re ∧ c.re < B + 4} := by
        intro s hs
        simp only [mem_ofPred_eq, re_add_intCast] at hs ⊢
        have := neg_ord8_le (n + σ t)
        rw [hm8 t] at this
        constructor <;> linarith [hs.1, hs.2, b8.2]
      have h7le := neg_ord7_le (n + σ t)
      rw [hm7 t] at h7le
      have hc := (hD8 t ht ((n 7 : ℂ) + σ t 7) (by
          rw [re_add_intCast, intCast_re]; linarith)
        (by rw [re_add_intCast, intCast_re]; linarith [b7.2])).comp
        ((differentiable_id.add (differentiable_const _)).differentiableOn) hmaps
      exact ((differentiable_pf9_eight _ _ l _).comp
        (differentiable_id.add (differentiable_const _))).differentiableOn.mul hc
    · simp only [intCast_re]
      constructor <;> linarith
  -- Step 4: the face theorem at `(n₇, n₈)`
  rw [← step3]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  set m := n + σ t
  have e7 : (n 7 : ℂ) + σ t 7 = ((m 7 : ℤ) : ℂ) := by simp [m]
  have e8 : (n 8 : ℂ) + σ t 8 = ((m 8 : ℤ) : ℂ) := by simp [m]
  by_cases h78 : m 7 ≤ 0 ∧ m 8 ≤ 0
  · congr 1
    rw [hV]
    simp only
    rw [e7, e8, intCast_eq_neg_ord7 h78.1, intCast_eq_neg_ord8 h78.2, pf9_neg_ord]
    exact (hF t ht).symm
  · rw [not_and_or, not_le, not_le] at h78
    have h0 : a t (nu9 ν' (n 7) (n 8)) d = 0 := by
      rcases h78 with h | h
      · exact hz t ht 7 (Or.inl rfl) hn7 (by simpa [m] using h) _ d (nu9_seven _ _ _)
      · exact hz t ht 8 (Or.inr rfl) hn8 (by simpa [m] using h) _ d (nu9_eight _ _ _)
    rw [h0, zero_mul, zero_mul]

/-! ### The relation at `λ = 0` -/

/-- **A relation for the face values `val3`** at a label with `n₇, n₈ ≤ 0`, for `d₀ ∉ ℚ`, from
the same relation for the normalized nine-variable integrals at convergent points. -/
theorem rel_val3 (T : List β) (σ : β → Fin 9 → ℤ) (j : β → ℕ)
    (a : β → (Fin 9 → ℂ) → ℂ → ℂ) (B : ℕ)
    (hσ : ∀ t ∈ T, ∀ k, -1 ≤ σ t k ∧ σ t k ≤ B)
    (ha : ∀ t ∈ T, Differentiable ℂ fun p : (Fin 9 → ℂ) × ℂ => a t p.1 p.2)
    (hrel : ∀ (ν : Fin 9 → ℂ) (d : ℂ), 0 < d.re →
      (∀ μ e, Shifted ν d μ e → LPConvergent (fun x => lpPoly.eval x) μ e) →
      (T.map fun t => a t ν d * (normLP (ν + shZ (σ t)) (d + 2 * j t) *
        lpIntegral (fun x => lpPoly.eval x) (ν + shZ (σ t)) (d + 2 * j t))).sum = 0)
    (n : Fin 9 → ℤ) (hn7 : n 7 ≤ 0) (hn8 : n 8 ≤ 0)
    (hz : ∀ t ∈ T, ∀ k : Fin 9, (k = 7 ∨ k = 8) → n k ≤ 0 → 0 < n k + σ t k →
      ∀ ν d, ν k = (n k : ℂ) → a t ν d = 0)
    {d₀ : ℂ} (hd : Irr d₀) :
    (T.map fun t => a t (fun k => (n k : ℂ)) d₀ * val3 (n + σ t) (d₀ + 2 * j t)).sum = 0 := by
  have han : ∀ t ∈ T, ∀ z, AnalyticAt ℂ (fun l =>
      a t (nu9 (lineNu w7 (lbl3 n []) l) (n 7) (n 8)) (lineD h7 d₀ l)) z := fun t ht z =>
    ((ha t ht).comp ((differentiable_nu9_line _ _ _).prodMk
      (by fun_prop))).analyticAt z
  have hm : MeromorphicOn (fun l => (T.map fun t =>
      a t (nu9 (lineNu w7 (lbl3 n []) l) (n 7) (n 8)) (lineD h7 d₀ l) *
        Iline3 (n + σ t) (d₀ + 2 * j t) l).sum) halfPlane :=
    meromorphicOn_list_sum _ fun t ht z hz =>
      (han t ht z).meromorphicAt.mul (meromorphicOn_Iline3 _ _ z hz)
  have h0 := eventuallyEq_nhdsNE_of_atRe hm (fun z _ => analyticAt_const.meromorphicAt)
    (eventually_rel_far T σ j a B hσ ha hrel n hn7 hn8 hz d₀) zero_mem_halfPlane
  have hT := TwoLoopSESector.tendsto_list_sum T (f := fun t l =>
    (fun l => a t (nu9 (lineNu w7 (lbl3 n []) l) (n 7) (n 8)) (lineD h7 d₀ l)) l *
      Iline3 (n + σ t) (d₀ + 2 * j t) l)
    (v := fun t => a t (nu9 (lineNu w7 (lbl3 n []) 0) (n 7) (n 8)) (lineD h7 d₀ 0) *
      val3 (n + σ t) (d₀ + 2 * j t)) fun t ht =>
    ((han t ht 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
      (tendsto_Iline3 _ (irr_add_two_mul hd (j t)))
  have := tendsto_nhds_unique (hT.congr' h0) tendsto_const_nhds
  simpa only [nu9_line_zero, lineD, mul_zero, add_zero] using this

end QED.DimReg.ThreeLoop
