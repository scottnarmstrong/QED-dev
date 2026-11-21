/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLRegular
public import QED.Polylog.HPLSeries
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import QED.Polylog.ExtraIntegrals

/-!
# Duality of harmonic polylogarithms at `1`

For words over `{0, 1}`, the substitution `t ↦ 1 - t` exchanges the kernels `1/t` and
`1/(1 - t)` and reverses the order of integration. At `x = 1` this gives the duality of
multiple zeta values: `H(w; 1) = H(w*; 1)` where `w*` is `w` reversed with `0 ↔ 1`
(e.g. `ζ(2, 1, 1) = ζ(4)`, `ζ(4, 1) = ζ(2, 1, 1, 1)`).

The proof is the path-composition identity
`Φ(x) = ∑_{w = u v} H(u*; 1 - x) H(v; x)`:
`Φ` has derivative zero on `(0, 1)` (the terms telescope), tends to `H(w; 1)` at `1⁻` and to
`H(w*; 1)` at `0⁺`. It is set up recursively, with the reversed prefix as a parameter.

## Main definitions

* `QED.Polylog.HPL.dualLetter`, `QED.Polylog.HPL.dualWord`: `0 ↔ 1`, and `w ↦ w*`.

## Main results

* `QED.Polylog.HPL.hpl_one_eq_hpl_one_dualWord`: `H(w; 1) = H(w*; 1)` for a word over
  `{0, 1}` starting with `0` and ending with `1`.
-/

@[expose] public section

open Real Set Filter Topology

namespace QED.Polylog.HPL

open Letter

/-- The duality of letters, `0 ↔ 1` (and `-1 ↦ -1`). -/
def dualLetter : Letter → Letter
  | zero => one
  | one => zero
  | negOne => negOne

/-- The dual word `w* `: reversed, with `0 ↔ 1`. -/
def dualWord (w : List Letter) : List Letter := (w.map dualLetter).reverse

theorem kernel_dualLetter {c : Letter} (hc : c ≠ negOne) (x : ℝ) :
    (dualLetter c).kernel (1 - x) = c.kernel x := by
  cases c with
  | zero => simp [dualLetter]
  | one => simp [dualLetter]
  | negOne => exact absurd rfl hc

/-- `H(u; 1 - x) H(v; x) → 0` as `x → 0⁺` when `v` is not all zeros. -/
theorem tendsto_hpl_one_sub_mul_hpl_zero (u : List Letter) {v : List Letter}
    (hv : ¬AllZero v) :
    Tendsto (fun x => hpl u (1 - x) * hpl v x) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC, hCv⟩ := abs_hpl_le_sqrt hv (b := 1 / 2) (by norm_num)
  obtain ⟨D, hD, hDu⟩ := abs_hpl_le_one_sub_rpow u (ε := 1 / 4) (by norm_num)
  refine tendsto_zero_of_abs_le_rpow (C := D * C) (r := 1 / 4) (b := 1 / 2) (by norm_num)
    (by norm_num) fun t ht => ?_
  have h1 : |hpl u (1 - t)| ≤ D * t ^ (-(1 / 4) : ℝ) := by
    have := hDu (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rwa [sub_sub_cancel] at this
  rw [abs_mul]
  calc |hpl u (1 - t)| * |hpl v t| ≤ (D * t ^ (-(1 / 4) : ℝ)) * (C * t ^ (1 / 2 : ℝ)) :=
        mul_le_mul h1 (hCv t ht) (abs_nonneg _) (mul_nonneg hD (rpow_nonneg ht.1.le _))
    _ = D * C * (t ^ (-(1 / 4) : ℝ) * t ^ (1 / 2 : ℝ)) := by ring
    _ = D * C * t ^ (1 / 4 : ℝ) := by
      rw [← rpow_add ht.1]
      norm_num

/-- `H(u; 1 - x) H(v; x) → 0` as `x → 1⁻` when `u` is not all zeros. -/
theorem tendsto_hpl_one_sub_mul_hpl_one {u : List Letter} (hu : ¬AllZero u)
    (v : List Letter) :
    Tendsto (fun x => hpl u (1 - x) * hpl v x) (𝓝[<] 1) (𝓝 0) := by
  have h := (tendsto_hpl_one_sub_mul_hpl_zero v hu).comp tendsto_one_sub_nhdsLT_one
  refine h.congr fun x => ?_
  simp only [Function.comp_apply, sub_sub_cancel]
  ring

/-! ### The path-composition function -/

/-- `G q x = H(q̄; 1 - x)`, `q̄` the letterwise dual of `q` (a reversed prefix). -/
noncomputable def dualG (q : List Letter) (x : ℝ) : ℝ := hpl (q.map dualLetter) (1 - x)

/-- The derivative of `dualG`: `0` for `q = []`, and `-f c (x) G q' x` for `q = c :: q'`. -/
noncomputable def dualGDeriv : List Letter → ℝ → ℝ
  | [], _ => 0
  | c :: q, x => -(c.kernel x * dualG q x)

/-- `Φ(q, v)(x) = ∑_{v = v₁ v₂} H((v₁ʳᵉᵛ ++ q)‾; 1 - x) H(v₂; x)`. -/
noncomputable def dualPhi : List Letter → List Letter → ℝ → ℝ
  | q, [], x => dualG q x
  | q, c :: v, x => dualG q x * hpl (c :: v) x + dualPhi (c :: q) v x

theorem hasDerivAt_dualG {q : List Letter} (hq : negOne ∉ q) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (dualG q) (dualGDeriv q x) x := by
  cases q with
  | nil =>
    simp only [dualGDeriv]
    exact hasDerivAt_const x 1
  | cons c q =>
    have hc : c ≠ negOne := fun h => hq (h ▸ List.mem_cons_self)
    have hy : 1 - x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have h := (hasDerivAt_hpl_cons (dualLetter c) (q.map dualLetter) hy).comp x
      ((hasDerivAt_id x).const_sub 1)
    rw [kernel_dualLetter hc] at h
    have e : dualG (c :: q) = fun x => hpl (dualLetter c :: q.map dualLetter) (1 - x) := rfl
    rw [e]
    simpa [dualGDeriv, dualG, Function.comp_def] using h

theorem hasDerivAt_dualPhi : ∀ (v q : List Letter), negOne ∉ q → negOne ∉ v →
    ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (dualPhi q v) (dualGDeriv q x * hpl v x) x
  | [], q, hq, _, x, hx => by
    simpa [dualPhi] using hasDerivAt_dualG hq hx
  | c :: v, q, hq, hv, x, hx => by
    have hc : c ≠ negOne := fun h => hv (h ▸ List.mem_cons_self)
    have hv' : negOne ∉ v := fun h => hv (List.mem_cons_of_mem _ h)
    have hcq : negOne ∉ c :: q := by simp [hq, Ne.symm hc]
    have h := ((hasDerivAt_dualG hq hx).mul (hasDerivAt_hpl_cons c v hx)).add
      (hasDerivAt_dualPhi v (c :: q) hcq hv' x hx)
    have e : dualPhi q (c :: v) = fun x => dualG q x * hpl (c :: v) x + dualPhi (c :: q) v x :=
      rfl
    rw [e]
    convert h using 1
    simp only [dualGDeriv]
    ring

/-- `Φ(q, v) → H((vʳᵉᵛ ++ q)‾; 1)` at `0⁺`, if `v` has no trailing zero and `vʳᵉᵛ ++ q` does
not start with `0`. -/
theorem tendsto_dualPhi_zero : ∀ (v q : List Letter), v.getLast? ≠ some zero →
    (v.reverse ++ q).head? ≠ some zero →
    Tendsto (dualPhi q v) (𝓝[>] 0) (𝓝 (hpl ((v.reverse ++ q).map dualLetter) 1))
  | [], q, _, hq => by
    have hq' : (q.map dualLetter).head? ≠ some one := by
      cases q with
      | nil => simp
      | cons c q =>
        cases c with
        | zero => simp at hq
        | one => simp [dualLetter]
        | negOne => simp [dualLetter]
    simpa [dualPhi, dualG, Function.comp_def] using
      (tendsto_hpl_of_head_ne_one hq').comp tendsto_one_sub_nhdsGT_zero
  | c :: v, q, hv, hq => by
    have ih := tendsto_dualPhi_zero v (c :: q) (getLast?_ne_of_cons hv) (by simpa using hq)
    have h0 := tendsto_hpl_one_sub_mul_hpl_zero (q.map dualLetter)
      (not_allZero_of_getLast? (List.cons_ne_nil c v) hv)
    have := h0.add ih
    rw [zero_add] at this
    simpa [dualPhi, dualG, Function.comp_def] using this

/-- `Φ(q, v) → 0` at `1⁻` if `q` contains a `0`. -/
theorem tendsto_dualPhi_one : ∀ (v q : List Letter), zero ∈ q →
    Tendsto (dualPhi q v) (𝓝[<] 1) (𝓝 0)
  | [], q, hq => by
    have hnz : ¬AllZero (q.map dualLetter) := fun h => by
      have := h one (List.mem_map.2 ⟨zero, hq, rfl⟩)
      exact absurd this (by decide)
    simpa [dualPhi, dualG, Function.comp_def] using
      (tendsto_hpl_zero hnz).comp tendsto_one_sub_nhdsLT_one
  | c :: v, q, hq => by
    have hnz : ¬AllZero (q.map dualLetter) := fun h => by
      have := h one (List.mem_map.2 ⟨zero, hq, rfl⟩)
      exact absurd this (by decide)
    have := (tendsto_hpl_one_sub_mul_hpl_one hnz (c :: v)).add
      (tendsto_dualPhi_one v (c :: q) (List.mem_cons_of_mem _ hq))
    rw [zero_add] at this
    simpa [dualPhi, dualG, Function.comp_def] using this

/-- **Duality at `1`.** For a word over `{0, 1}` starting with `0` and ending with `1`,
`H(w; 1) = H(w*; 1)`, `w*` the reversed word with `0 ↔ 1`. -/
theorem hpl_one_eq_hpl_one_dualWord {w : List Letter} (h0 : w.head? = some zero)
    (h1 : w.getLast? = some one) (hn : negOne ∉ w) :
    hpl w 1 = hpl (dualWord w) 1 := by
  obtain ⟨a, w', rfl⟩ := List.exists_cons_of_ne_nil (show w ≠ [] by rintro rfl; simp at h0)
  simp only [List.head?_cons, Option.some.injEq] at h0
  subst h0
  have hlast : (zero :: w').getLast? ≠ some zero := by rw [h1]; simp
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (dualPhi [] (zero :: w')) 0 x := fun x hx => by
    simpa [dualGDeriv] using hasDerivAt_dualPhi (zero :: w') [] (by simp) hn x hx
  have hlim0 := tendsto_dualPhi_zero (zero :: w') [] hlast (by
    rw [List.append_nil, List.head?_reverse, h1]; simp)
  have hconst := eq_of_hasDerivAt_zero_of_tendsto_right zero_lt_one hd hlim0
  have hlim1 : Tendsto (dualPhi [] (zero :: w')) (𝓝[<] 1) (𝓝 (hpl (zero :: w') 1)) := by
    have := (tendsto_hpl_one (a := zero) (by decide) w').add
      (tendsto_dualPhi_one w' [zero] List.mem_cons_self)
    rw [add_zero] at this
    simpa [dualPhi, dualG, Function.comp_def] using this
  have hlim1' : Tendsto (dualPhi [] (zero :: w')) (𝓝[<] 1)
      (𝓝 (hpl (((zero :: w').reverse ++ []).map dualLetter) 1)) :=
    tendsto_nhds_of_eventually_eq (by
      filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with x hx using hconst x hx)
  rw [tendsto_nhds_unique hlim1 hlim1', List.append_nil, dualWord, List.map_reverse]

end QED.Polylog.HPL
