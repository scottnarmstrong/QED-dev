/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopFaceHolo

/-!
# The IBP relations of set (d) for the face values `val3`

Let `n` be a label with `n₇, n₈ ≤ 0`. For each template `(i, j)` of
`QED.ThreeLoopD.SetDCert.lbl`:

* **Template match at large exponent** (`eventually_tmpl_far`): for `re λ` large,
  `Σ_t coeff_t(λ) · Iline3 (n + σ_t) d₀ λ = 0`, the coefficients evaluated along the line
  `(ν', ν₇, ν₈, d) = (n' + λw₇, n₇, n₈, d₀ + 6λ)`. Proof: at fixed `λ`, consider
  `Φ(s₇, s₈) = Σ_t coeff_t · pf9 · cont9 (n + σ_t) (s₇ + σ_{t,7}) (s₈ + σ_{t,8})`. For
  `1 < re s₇, re s₈ < 2` every term is the normalized nine-variable integral
  (`QED.DimReg.ThreeLoop.eventually_lpIntegral_eq_cont9`, `normLP_nu9`), so `Φ = 0` by
  `QED.DimReg.ThreeLoop.tmpl_lp`. `Φ` is holomorphic in `s₇` on a strip containing `n₇`
  (`eventually_differentiableOn_cont9_seven`), hence `Φ(n₇, s₈) = 0` (identity theorem), then
  likewise in `s₈`. At `(n₇, n₈)` every term with `(n + σ_t)₇, (n + σ_t)₈ ≤ 0` is
  `coeff_t · Iline3 (n + σ_t)` by the face theorem
  (`QED.DimReg.ThreeLoop.eventually_norm9_mul_cont9`); a term raising `ν₇` or `ν₈` to `1` has the
  coefficient `c ν₇ = 0` or `c ν₈ = 0` (`tcoef_eq_zero_of_raise`).
* **The relation at `λ = 0`** (`ibpHoldsAt_val3`): by meromorphy of `Iline3` and
  `QED.DimReg.ThreeLoop.tendsto_Iline3`, for `d₀ ∉ ℚ` the values `val3` satisfy the relation
  `QED.Algebra.IBPCert.Family.IBPHoldsAt lbl val3 d₀ i j n`.
-/

@[expose] public section

open Complex Filter Topology Set MeasureTheory QED.DimReg QED.DimReg.Sector QED.DimReg.LineCont
open QED.Algebra.IBPCert QED.ThreeLoopD.SetDCert
open QED.DimReg.TwoLoopSESector (atRe eventually_list halfPlane zero_mem_halfPlane Irr
  eventuallyEq_nhdsNE_of_atRe meromorphicOn_list_sum analyticAt_poch)

namespace QED.DimReg.ThreeLoop

/-! ### The template shifts -/

theorem getD_shiftVec (a b : ℕ) {k : ℕ} (hk : k < 9) :
    (Family.shiftVec 9 a b).getD k 0 = (if k = a then 1 else 0) - (if k = b then 1 else 0) := by
  simp only [Family.shiftVec, getD_range_map_int _ hk, Bool.cond_eq_ite, Nat.beq_eq]

/-- The entries of a template shift are `-1`, `0` or `1`. -/
theorem shift_bounds {i j : ℕ} {t : Term} (ht : t ∈ lbl.template i j) (k : Fin 9) :
    -1 ≤ t.shift.getD k 0 ∧ t.shift.getD k 0 ≤ 1 := by
  rcases mem_template ht with rfl | ⟨a, -, b, -, c, rfl⟩
  · simp
  · simp only [show lbl.nProp = 9 from rfl, getD_shiftVec a b k.isLt]
    split_ifs <;> omega

/-- **A term raising an index `k` with `n_k ≤ 0` to a positive value has coefficient `0`**: it is
`c ν_k I(ν + e_k - e_b)` or `c ν_k I(ν + e_k)`, and `n_k = 0`. -/
theorem tcoef_eq_zero_of_raise {i j : ℕ} {t : Term} (ht : t ∈ lbl.template i j) {n : Fin 9 → ℤ}
    {k : Fin 9} (hk : n k ≤ 0) (hpos : 0 < n k + t.shift.getD k 0) (d : ℂ) {ν : Fin 9 → ℂ}
    (hν : ν k = n k) : tcoef t d ν = 0 := by
  rcases mem_template ht with rfl | ⟨a, ha, b, -, c, rfl⟩
  · simp at hpos; omega
  · simp only [show lbl.nProp = 9 from rfl] at ha hpos ⊢
    rw [getD_shiftVec a b k.isLt] at hpos
    have hka : (k : ℕ) = a := by
      by_contra h
      rw [ite_eq_right h] at hpos
      split_ifs at hpos <;> omega
    have hn0 : n k = 0 := by split_ifs at hpos <;> omega
    have hk' : (⟨a, ha⟩ : Fin 9) = k := Fin.ext hka.symm
    simp only [tcoef, Int.cast_zero, zero_mul, add_zero, zero_add, ha, dite_true, hk', hν, hn0]
    simp

/-! ### Points along the line -/

theorem nu9_add_shC (n : Fin 9 → ℤ) (σ : List ℤ) (l s₇ s₈ : ℂ) :
    nu9 (lineNu w7 (lbl3 n []) l) s₇ s₈ + shC σ =
      nu9 (lineNu w7 (lbl3 (n + toVec 9 σ) []) l) (s₇ + shC σ 7) (s₈ + shC σ 8) := by
  funext i
  induction i using Fin.lastCases with
  | last => rfl
  | cast j =>
    induction j using Fin.lastCases with
    | last => rfl
    | cast b =>
      simp only [Pi.add_apply, nu9_castSucc, lineNu, lbl3_nil, shC, Pi.add_apply, toVec]
      push_cast
      simp only [Fin.val_castLE, Fin.val_castSucc]
      ring

theorem nu9_line_zero (n : Fin 9 → ℤ) :
    nu9 (lineNu w7 (lbl3 n []) 0) (n 7) (n 8) = fun k => (n k : ℂ) := by
  funext i
  induction i using Fin.lastCases with
  | last => rfl
  | cast j =>
    induction j using Fin.lastCases with
    | last => rfl
    | cast b =>
      simp only [nu9_castSucc, lineNu, lbl3_nil, mul_zero, add_zero]
      rfl

theorem intCast_eq_neg_ord7 {m : Fin 9 → ℤ} (h : m 7 ≤ 0) : ((m 7 : ℤ) : ℂ) = -(ord7 m : ℂ) := by
  have : ((ord7 m : ℕ) : ℤ) = -m 7 := by simp only [ord7]; omega
  rw [show ((ord7 m : ℕ) : ℂ) = (((ord7 m : ℕ) : ℤ) : ℂ) from rfl, this]
  push_cast; ring

theorem intCast_eq_neg_ord8 {m : Fin 9 → ℤ} (h : m 8 ≤ 0) : ((m 8 : ℤ) : ℂ) = -(ord8 m : ℂ) := by
  have : ((ord8 m : ℕ) : ℤ) = -m 8 := by simp only [ord8]; omega
  rw [show ((ord8 m : ℕ) : ℂ) = (((ord8 m : ℕ) : ℤ) : ℂ) from rfl, this]
  push_cast; ring

theorem neg_ord7_le (m : Fin 9 → ℤ) : -(ord7 m : ℝ) ≤ (m 7 : ℝ) := by
  have : -((ord7 m : ℕ) : ℤ) ≤ m 7 := by simp only [ord7]; omega
  exact_mod_cast this

theorem neg_ord8_le (m : Fin 9 → ℤ) : -(ord8 m : ℝ) ≤ (m 8 : ℝ) := by
  have : -((ord8 m : ℕ) : ℤ) ≤ m 8 := by simp only [ord8]; omega
  exact_mod_cast this

theorem re_shC (σ : List ℤ) (k : Fin 9) : (shC σ k).re = (σ.getD k 0 : ℝ) := by
  simp [shC]

/-! ### Holomorphy of the terms -/

theorem differentiableOn_list_sum' {β : Type*} (L : List β) {f : β → ℂ → ℂ} {U : Set ℂ}
    (h : ∀ t ∈ L, DifferentiableOn ℂ (f t) U) :
    DifferentiableOn ℂ (fun s => (L.map fun t => f t s).sum) U := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a List.mem_cons_self).add (ih fun t ht => h t (List.mem_cons_of_mem a ht))

theorem differentiable_tcoef_seven (t : Term) (d : ℂ) (ν : Fin 7 → ℂ) (c : ℂ) :
    Differentiable ℂ fun s => tcoef t d (nu9 ν s c) := by
  unfold tcoef
  split_ifs with h
  · refine (differentiable_const _).add ((differentiable_const _).mul ?_)
    have e : (fun s => nu9 ν s c ⟨t.idx, h⟩) =
        fun s => Function.update (nu9 ν 0 c) 7 s ⟨t.idx, h⟩ :=
      funext fun s => by rw [← update_nu9_seven_zero]
    rw [e]
    simp only [Function.update_apply]
    split_ifs
    · exact differentiable_id
    · exact differentiable_const _
  · exact differentiable_const _

theorem differentiable_tcoef_eight (t : Term) (d : ℂ) (ν : Fin 7 → ℂ) (a : ℂ) :
    Differentiable ℂ fun s => tcoef t d (nu9 ν a s) := by
  unfold tcoef
  split_ifs with h
  · refine (differentiable_const _).add ((differentiable_const _).mul ?_)
    have e : (fun s => nu9 ν a s ⟨t.idx, h⟩) =
        fun s => Function.update (nu9 ν a 0) 8 s ⟨t.idx, h⟩ :=
      funext fun s => by rw [← update_nu9_eight_zero]
    rw [e]
    simp only [Function.update_apply]
    split_ifs
    · exact differentiable_id
    · exact differentiable_const _
  · exact differentiable_const _

theorem isPreconnected_strip (a b : ℝ) : IsPreconnected {s : ℂ | a < s.re ∧ s.re < b} :=
  ((convex_halfSpace_re_gt a).inter (convex_halfSpace_re_lt b)).isPreconnected

theorem isOpen_strip (a b : ℝ) : IsOpen {s : ℂ | a < s.re ∧ s.re < b} :=
  (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)

/-- **Identity theorem on a strip**: a function holomorphic on `{a < re s < b}` that vanishes on
`{1 < re s < 2}` (inside the strip) vanishes on the strip. -/
theorem eqOn_zero_strip {f : ℂ → ℂ} {a b : ℝ} (ha : a < 1) (hb : 2 < b)
    (hf : DifferentiableOn ℂ f {s | a < s.re ∧ s.re < b})
    (h0 : ∀ s : ℂ, 1 < s.re → s.re < 2 → f s = 0) {z : ℂ} (hz : a < z.re ∧ z.re < b) :
    f z = 0 := by
  have hz0 : (3 / 2 : ℂ) ∈ {s : ℂ | a < s.re ∧ s.re < b} := by
    simp only [mem_ofPred_eq]
    norm_num
    constructor <;> linarith
  have hev : f =ᶠ[𝓝 (3 / 2 : ℂ)] 0 := by
    filter_upwards [(isOpen_strip 1 2).mem_nhds (by norm_num)] with s hs
    exact h0 s hs.1 hs.2
  exact (hf.analyticOnNhd (isOpen_strip a b)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (isPreconnected_strip a b) hz0 hev hz

/-! ### The template relations at large exponent -/

/-- The convergence hypotheses of `tmpl_lp` near the line, for `1 < re s₇, re s₈ < 2`. -/
theorem near9_of_shifted {n' : Fin 7 → ℤ} {d₀ l s₇ s₈ : ℂ} (h1 : 1 < s₇.re) (h2 : s₇.re < 2)
    (h3 : 1 < s₈.re) (h4 : s₈.re < 2) {μ : Fin 9 → ℂ} {e : ℂ}
    (h : Shifted (nu9 (lineNu w7 n' l) s₇ s₈) (lineD h7 d₀ l) μ e) : Near9 n' d₀ 8 l μ e := by
  obtain ⟨hk, he⟩ := h
  have hb : ∀ k, (nu9 (lineNu w7 n' l) s₇ s₈ k).re - 1 ≤ (μ k).re ∧
      (μ k).re ≤ (nu9 (lineNu w7 n' l) s₇ s₈ k).re + 6 := by
    intro k
    obtain ⟨m, hm, hμ | hμ⟩ := hk k
    · have : (m : ℝ) ≤ 6 := by exact_mod_cast hm
      rw [hμ]; simp only [add_re, natCast_re]
      constructor <;> linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    · have : (m : ℝ) ≤ 6 := by exact_mod_cast hm
      rw [hμ]; simp only [sub_re, add_re, natCast_re, one_re]
      constructor <;> linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have b7 := hb 7
  have b8 := hb 8
  simp only [nu9_seven, nu9_eight] at b7 b8
  refine ⟨fun b => ?_, by linarith [b7.1], by linarith [b7.2], by linarith [b8.1],
    by linarith [b8.2], ?_⟩
  · have := hb (Fin.castSucc (Fin.castSucc b))
    simp only [nu9_castSucc] at this
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  · rcases he with rfl | rfl
    · simp
    · simp only [add_re, re_ofNat]; rw [abs_le]; constructor <;> norm_num

/-- **The template relations for `Iline3` at large exponent** (labels with `n₇, n₈ ≤ 0`). -/
theorem eventually_tmpl_far {i j : ℕ} (hi : i < 3) (hj : j < 4) (n : Fin 9 → ℤ)
    (hn7 : n 7 ≤ 0) (hn8 : n 8 ≤ 0) (d₀ : ℂ) :
    ∀ᶠ l in atRe, ((lbl.template i j).map fun t =>
      tcoef t (lineD h7 d₀ l) (nu9 (lineNu w7 (lbl3 n []) l) (n 7) (n 8)) *
        Iline3 (n + toVec 9 t.shift) d₀ l).sum = 0 := by
  set T := lbl.template i j
  filter_upwards [eventually_list T fun t =>
      eventually_lpIntegral_eq_cont9 (n + toVec 9 t.shift) d₀ 4,
    eventually_lpConvergent9 (lbl3 n []) d₀ 8,
    eventually_list T fun t =>
      eventually_differentiableOn_cont9_seven (n + toVec 9 t.shift) d₀ (M := 4) (by norm_num),
    eventually_list T fun t =>
      eventually_differentiableOn_cont9_eight (n + toVec 9 t.shift) d₀ (M := 4) (by norm_num),
    eventually_list T fun t => eventually_norm9_mul_cont9 (n + toVec 9 t.shift) d₀]
    with l hE hC hD7 hD8 hF
  set ν' := lineNu w7 (lbl3 n []) l
  set d := lineD h7 d₀ l
  set V : Term → ℂ → ℂ → ℂ := fun t s₇ s₈ =>
    pf9 (lbl3 (n + toVec 9 t.shift) []) d₀ l (s₇ + shC t.shift 7) (s₈ + shC t.shift 8) *
      cont9 (n + toVec 9 t.shift) d₀ l (s₇ + shC t.shift 7) (s₈ + shC t.shift 8) with hV
  set Φ : ℂ → ℂ → ℂ := fun s₇ s₈ =>
    (T.map fun t => tcoef t d (nu9 ν' s₇ s₈) * V t s₇ s₈).sum with hΦ
  have hσ : ∀ t ∈ T, ∀ k : Fin 9, -1 ≤ (shC t.shift k).re ∧ (shC t.shift k).re ≤ 1 := by
    intro t ht k
    rw [re_shC]
    have := shift_bounds ht k
    constructor <;> exact_mod_cast (by omega : _)
  have hm7 : ∀ t ∈ T, (((n + toVec 9 t.shift) 7 : ℤ) : ℝ) = (n 7 : ℝ) + (shC t.shift 7).re := by
    intro t _; rw [re_shC]; simp [toVec]
  have hm8 : ∀ t ∈ T, (((n + toVec 9 t.shift) 8 : ℤ) : ℝ) = (n 8 : ℝ) + (shC t.shift 8).re := by
    intro t _; rw [re_shC]; simp [toVec]
  -- Step 1: the relation where all integrals converge
  have step1 : ∀ s₇ s₈ : ℂ, 1 < s₇.re → s₇.re < 2 → 1 < s₈.re → s₈.re < 2 → Φ s₇ s₈ = 0 := by
    intro s₇ s₈ h1 h2 h3 h4
    have H := tmpl_lp hi hj (nu9 ν' s₇ s₈) d fun μ e hμ =>
      hC μ e (near9_of_shifted h1 h2 h3 h4 hμ)
    rw [← H]
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    congr 1
    have b7 := hσ t ht 7
    have b8 := hσ t ht 8
    have hE' := hE t ht (s₇ + shC t.shift 7) (s₈ + shC t.shift 8)
      (by rw [add_re]; linarith [b7.1]) (by rw [add_re]; linarith [b7.2])
      (by rw [add_re]; linarith [b8.1]) (by rw [add_re]; linarith [b8.2])
    rw [nu9_add_shC, normLP_nu9, hV]
    simp only
    rw [← hE']
    ring
  -- Step 2: continuation in `s₇`
  have step2 : ∀ s₈ : ℂ, 1 < s₈.re → s₈.re < 2 → Φ (n 7) s₈ = 0 := by
    intro s₈ h3 h4
    refine eqOn_zero_strip (f := fun s => Φ s s₈) (a := (n 7 : ℝ) - 1 / 2) (b := 3)
      (by have : (n 7 : ℝ) ≤ 0 := by exact_mod_cast hn7
          linarith) (by norm_num) ?_ (fun s h1 h2 => step1 s s₈ h1 h2 h3 h4) ?_
    · refine differentiableOn_list_sum' T fun t ht => ?_
      refine ((differentiable_tcoef_seven t d ν' s₈).differentiableOn).mul ?_
      have b7 := hσ t ht 7
      have b8 := hσ t ht 8
      have hmaps : MapsTo (fun s : ℂ => s + shC t.shift 7) {s | (n 7 : ℝ) - 1 / 2 < s.re ∧ s.re < 3}
          {a | -(ord7 (n + toVec 9 t.shift) : ℝ) - 1 / 2 < a.re ∧ a.re < 4} := by
        intro s hs
        simp only [mem_ofPred_eq, add_re] at hs ⊢
        have := neg_ord7_le (n + toVec 9 t.shift)
        rw [hm7 t ht] at this
        constructor <;> linarith [hs.1, hs.2, b7.2]
      have hc := (hD7 t ht (s₈ + shC t.shift 8) (by
          rw [add_re]; linarith [b8.1, (Nat.cast_nonneg _ : (0 : ℝ) ≤ ord8 (n + toVec 9 t.shift))])
        (by rw [add_re]; linarith [b8.2])).comp
        ((differentiable_id.add (differentiable_const _)).differentiableOn) hmaps
      exact ((differentiable_pf9_seven _ d₀ l _).comp
        (differentiable_id.add (differentiable_const _))).differentiableOn.mul hc
    · simp only [intCast_re]
      constructor <;> linarith [show (n 7 : ℝ) ≤ 0 by exact_mod_cast hn7]
  -- Step 3: continuation in `s₈`
  have step3 : Φ (n 7) (n 8) = 0 := by
    refine eqOn_zero_strip (f := fun s => Φ (n 7) s) (a := (n 8 : ℝ) - 1 / 2) (b := 3)
      (by have : (n 8 : ℝ) ≤ 0 := by exact_mod_cast hn8
          linarith) (by norm_num) ?_ (fun s h1 h2 => step2 s h1 h2) ?_
    · refine differentiableOn_list_sum' T fun t ht => ?_
      refine ((differentiable_tcoef_eight t d ν' (n 7)).differentiableOn).mul ?_
      have b7 := hσ t ht 7
      have b8 := hσ t ht 8
      have hmaps : MapsTo (fun s : ℂ => s + shC t.shift 8) {s | (n 8 : ℝ) - 1 / 2 < s.re ∧ s.re < 3}
          {c | -(ord8 (n + toVec 9 t.shift) : ℝ) - 1 / 2 < c.re ∧ c.re < 4} := by
        intro s hs
        simp only [mem_ofPred_eq, add_re] at hs ⊢
        have := neg_ord8_le (n + toVec 9 t.shift)
        rw [hm8 t ht] at this
        constructor <;> linarith [hs.1, hs.2, b8.2]
      have h7le := neg_ord7_le (n + toVec 9 t.shift)
      rw [hm7 t ht] at h7le
      have hn7' : (n 7 : ℝ) ≤ 0 := by exact_mod_cast hn7
      have hc := (hD8 t ht ((n 7 : ℂ) + shC t.shift 7) (by
          rw [add_re, intCast_re]; linarith)
        (by rw [add_re, intCast_re]; linarith [b7.2])).comp
        ((differentiable_id.add (differentiable_const _)).differentiableOn) hmaps
      exact ((differentiable_pf9_eight _ d₀ l _).comp
        (differentiable_id.add (differentiable_const _))).differentiableOn.mul hc
    · simp only [intCast_re]
      constructor <;> linarith [show (n 8 : ℝ) ≤ 0 by exact_mod_cast hn8]
  -- Step 4: the face theorem at `(n₇, n₈)`
  rw [← step3]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  set m := n + toVec 9 t.shift
  have e7 : (n 7 : ℂ) + shC t.shift 7 = ((m 7 : ℤ) : ℂ) := by simp [m, shC, toVec]
  have e8 : (n 8 : ℂ) + shC t.shift 8 = ((m 8 : ℤ) : ℂ) := by simp [m, shC, toVec]
  by_cases h78 : m 7 ≤ 0 ∧ m 8 ≤ 0
  · congr 1
    rw [hV]
    simp only
    rw [e7, e8, intCast_eq_neg_ord7 h78.1, intCast_eq_neg_ord8 h78.2, pf9_neg_ord]
    exact (hF t ht).symm
  · rw [not_and_or, not_le, not_le] at h78
    have h0 : tcoef t d (nu9 ν' (n 7) (n 8)) = 0 := by
      rcases h78 with h | h
      · exact tcoef_eq_zero_of_raise ht (k := 7) hn7 (by simpa [m, toVec] using h) d
          (nu9_seven _ _ _)
      · exact tcoef_eq_zero_of_raise ht (k := 8) hn8 (by simpa [m, toVec] using h) d
          (nu9_eight _ _ _)
    rw [h0, zero_mul, zero_mul]

/-! ### The relations for `val3` -/

theorem analyticAt_coef3 (n : Fin 9 → ℤ) (d₀ : ℂ) (j : ℕ) (β : List ℕ) (c : ℤ) (z : ℂ) :
    AnalyticAt ℂ (coef3 n d₀ j β c) z := by
  have hz : AnalyticAt ℂ (fun l => 2 * lineD h7 d₀ l - ∑ b : Fin 7, lineNu w7 (lbl3 n []) l b +
      (ord7 n + ord8 n : ℂ)) z := by
    unfold lineD lineNu; fun_prop
  have hp : AnalyticAt ℂ (fun l => ∏ b : Fin 7, TwoLoopSESector.poch (lineNu w7 (lbl3 n []) l b)
      (β.getD b 0)) z :=
    Finset.analyticAt_fun_prod _ fun b _ => analyticAt_poch (by unfold lineNu; fun_prop) _
  unfold coef3
  exact (analyticAt_const.mul (analyticAt_poch hz _)).mul hp

theorem meromorphicOn_Iline3 (n : Fin 9 → ℤ) (d₀ : ℂ) : MeromorphicOn (Iline3 n d₀) halfPlane :=
  meromorphicOn_list_sum (terms3 n) fun t _ z hz =>
    (analyticAt_coef3 n d₀ t.1 t.2.1 t.2.2 z).meromorphicAt.mul
      (F7.meromorphicOn_Iline (lbl3 n t.2.1) (d₀ + 2 * t.1) z hz)

theorem analyticAt_tcoef_line (t : Term) (n : Fin 9 → ℤ) (d₀ z : ℂ) :
    AnalyticAt ℂ (fun l => tcoef t (lineD h7 d₀ l) (nu9 (lineNu w7 (lbl3 n []) l) (n 7) (n 8)))
      z := by
  have hd : AnalyticAt ℂ (fun l => lineD h7 d₀ l) z := by unfold lineD; fun_prop
  unfold tcoef
  split_ifs with h
  · have hν : AnalyticAt ℂ (fun l => nu9 (lineNu w7 (lbl3 n []) l) (n 7) (n 8) ⟨t.idx, h⟩) z := by
      generalize (⟨t.idx, h⟩ : Fin 9) = k
      induction k using Fin.lastCases with
      | last => exact analyticAt_const
      | cast j =>
        induction j using Fin.lastCases with
        | last => exact analyticAt_const
        | cast b =>
          simp only [nu9_castSucc]
          unfold lineNu; fun_prop
    fun_prop
  · fun_prop

theorem tcoef_line_zero (t : Term) (n : Fin 9 → ℤ) (d₀ : ℂ) :
    tcoef t (lineD h7 d₀ 0) (nu9 (lineNu w7 (lbl3 n []) 0) (n 7) (n 8)) = t.coeff d₀ n := by
  rw [nu9_line_zero]
  simp only [tcoef, Term.coeff, vecGet, lineD, mul_zero, add_zero]
  split_ifs <;> push_cast <;> ring

/-- **The IBP relations of set (d) for `val3`** at every label with `n₇, n₈ ≤ 0`, for
`d₀ ∉ ℚ`: `Σ_t coeff_t(d₀, n) · val3 (n + σ_t) d₀ = 0` for each template `(i, j)`. -/
theorem ibpHoldsAt_val3 {d₀ : ℂ} (hd : Irr d₀) {i j : ℕ} (hi : i < 3) (hj : j < 4)
    (n : Fin 9 → ℤ) (hn7 : n 7 ≤ 0) (hn8 : n 8 ≤ 0) : lbl.IBPHoldsAt val3 d₀ i j n := by
  show ((lbl.template i j).map fun t => t.coeff d₀ n * val3 (n + toVec 9 t.shift) d₀).sum = 0
  have hm : MeromorphicOn (fun l => ((lbl.template i j).map fun t =>
      tcoef t (lineD h7 d₀ l) (nu9 (lineNu w7 (lbl3 n []) l) (n 7) (n 8)) *
        Iline3 (n + toVec 9 t.shift) d₀ l).sum) halfPlane :=
    meromorphicOn_list_sum _ fun t _ z hz =>
      (analyticAt_tcoef_line t n d₀ z).meromorphicAt.mul (meromorphicOn_Iline3 _ _ z hz)
  have h0 := eventuallyEq_nhdsNE_of_atRe hm (fun z _ => analyticAt_const.meromorphicAt)
    (eventually_tmpl_far hi hj n hn7 hn8 d₀) zero_mem_halfPlane
  have T := TwoLoopSESector.tendsto_list_sum (lbl.template i j) (f := fun t l =>
    tcoef t (lineD h7 d₀ l) (nu9 (lineNu w7 (lbl3 n []) l) (n 7) (n 8)) *
      Iline3 (n + toVec 9 t.shift) d₀ l) fun t _ =>
    ((analyticAt_tcoef_line t n d₀ 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
      (tendsto_Iline3 _ hd)
  have := tendsto_nhds_unique (T.congr' h0) tendsto_const_nhds
  simpa only [tcoef_line_zero] using this

end QED.DimReg.ThreeLoop
