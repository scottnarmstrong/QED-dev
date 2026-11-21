/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Algebra.Monoid

/-!
# Harmonic polylogarithms: the shuffle product

The shuffle product of harmonic polylogarithms,

`H(u; x) H(v; x) = ∑_{w ∈ u ⧢ v} H(w; x)` for `0 < x < 1`,

where the sum runs over the shuffles of `u` and `v` counted with multiplicity
(`QED.Polylog.HPL.shuffle`).

The proof is by induction on `|u| + |v|`. The case of an empty word is trivial. For
`u = a · u'`, `v = b · v'`, both sides have the same derivative on `(0, 1)`: by the derivative
formula `QED.Polylog.HPL.hasDerivAt_hpl_cons`, the left side has derivative
`f a H(u') H(v) + f b H(u) H(v')` and the right side
`f a ∑_{u' ⧢ v} H + f b ∑_{u ⧢ v'} H`, which agree by the induction hypothesis. Their difference
is therefore constant, and the constant is `0`:

* if `u` and `v` are not both all zeros, every shuffle is not all zeros, and both sides tend to
  `0` as `x → 0⁺` (`QED.Polylog.HPL.tendsto_hpl_mul_hpl_zero`, `QED.Polylog.HPL.tendsto_hpl_zero`);
* if `u` and `v` are both all zeros, so is every shuffle, and both sides are polynomials in
  `log x` without constant term, tending to `0` as `x → 1⁻`.

## Main results

* `QED.Polylog.HPL.hasDerivAt_sum_hpl_cons`: the derivative of `∑_{w ∈ L} H(a · w)`.
* `QED.Polylog.HPL.hpl_mul_hpl`: the shuffle product.
-/

public section

open Real Set Filter Topology

namespace QED.Polylog.HPL

/-- The derivative of `x ↦ ∑_{w ∈ L} H(a · w; x)` is `f a x ∑_{w ∈ L} H(w; x)` on `(0, 1)`. -/
theorem hasDerivAt_sum_hpl_cons (a : Letter) (L : List (List Letter)) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y => ((L.map (a :: ·)).map fun w => hpl w y).sum)
      (a.kernel x * (L.map fun w => hpl w x).sum) x := by
  induction L with
  | nil => simpa using hasDerivAt_const x (0 : ℝ)
  | cons w L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ((hasDerivAt_hpl_cons a w hx).add ih).congr_deriv (by ring)

/-- An all-zero nonempty word has `H(w; x) → 0` as `x → 1⁻`. -/
theorem tendsto_hpl_allZero_one {w : List Letter} (hw : AllZero w) (hne : w ≠ []) :
    Tendsto (hpl w) (𝓝[<] 1) (𝓝 0) := by
  rw [show hpl w = fun x => log x ^ w.length / (w.length.factorial : ℝ) from
    funext (hpl_of_allZero hw)]
  have h : Tendsto log (𝓝[<] 1) (𝓝 0) := by
    simpa using (continuousAt_log one_ne_zero).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio 1))
  simpa [zero_pow (List.length_pos_iff.2 hne).ne'] using
    (h.pow w.length).div_const (w.length.factorial : ℝ)

/-- The shuffle product, with `x` explicit (for the recursion). -/
private theorem hpl_mul_hpl_aux : ∀ (u v : List Letter) (x : ℝ), x ∈ Ioo (0 : ℝ) 1 →
    hpl u x * hpl v x = ((shuffle u v).map fun w => hpl w x).sum
  | [], v, x, _ => by simp
  | a :: u, [], x, _ => by simp
  | a :: u, b :: v, x, hx => by
    set S : ℝ → ℝ := fun y => ((shuffle (a :: u) (b :: v)).map fun w => hpl w y).sum with hS
    have hSsplit : S = fun y => (((shuffle u (b :: v)).map (a :: ·)).map fun w => hpl w y).sum +
        (((shuffle (a :: u) v).map (b :: ·)).map fun w => hpl w y).sum := by
      funext y
      simp only [hS, shuffle_cons_cons, List.map_append, List.sum_append]
    have hd : ∀ y ∈ Ioo (0 : ℝ) 1,
        HasDerivAt (fun y => hpl (a :: u) y * hpl (b :: v) y - S y) 0 y := by
      intro y hy
      have h1 := (hasDerivAt_hpl_cons a u hy).mul (hasDerivAt_hpl_cons b v hy)
      have h2 := (hasDerivAt_sum_hpl_cons a (shuffle u (b :: v)) hy).add
        (hasDerivAt_sum_hpl_cons b (shuffle (a :: u) v) hy)
      rw [hSsplit]
      refine (h1.sub h2).congr_deriv ?_
      rw [← hpl_mul_hpl_aux u (b :: v) y hy, ← hpl_mul_hpl_aux (a :: u) v y hy]
      ring
    have hmem : ∀ w ∈ shuffle (a :: u) (b :: v), (AllZero w ↔ AllZero (a :: u) ∧
        AllZero (b :: v)) := fun w hw => allZero_of_mem_shuffle_iff hw
    by_cases hz : AllZero (a :: u) ∧ AllZero (b :: v)
    · -- both words are all zeros: compare the limits at `1⁻`
      have hL : Tendsto (fun y => hpl (a :: u) y * hpl (b :: v) y - S y) (𝓝[<] 1) (𝓝 0) := by
        have h1 := (tendsto_hpl_allZero_one hz.1 (List.cons_ne_nil _ _)).mul
          (tendsto_hpl_allZero_one hz.2 (List.cons_ne_nil _ _))
        have h2 : Tendsto S (𝓝[<] 1) (𝓝 0) := by
          have := tendsto_list_sum (l := shuffle (a :: u) (b :: v)) (f := fun w y => hpl w y)
            (a := fun _ => (0 : ℝ)) (x := 𝓝[<] 1) fun w hw => by
              refine tendsto_hpl_allZero_one ((hmem w hw).2 hz) ?_
              intro h
              have := length_of_mem_shuffle hw
              simp [h] at this
          simpa using this
        simpa using h1.sub h2
      have := eq_of_hasDerivAt_zero_of_tendsto_left zero_lt_one hd hL x hx
      linarith
    · -- otherwise: compare the limits at `0⁺`
      have hL : Tendsto (fun y => hpl (a :: u) y * hpl (b :: v) y - S y) (𝓝[>] 0) (𝓝 0) := by
        have h1 := tendsto_hpl_mul_hpl_zero hz
        have h2 : Tendsto S (𝓝[>] 0) (𝓝 0) := by
          have := tendsto_list_sum (l := shuffle (a :: u) (b :: v)) (f := fun w y => hpl w y)
            (a := fun _ => (0 : ℝ)) (x := 𝓝[>] 0) fun w hw =>
              tendsto_hpl_zero fun h => hz ((hmem w hw).1 h)
          simpa using this
        simpa using h1.sub h2
      have := eq_of_hasDerivAt_zero_of_tendsto_right zero_lt_one hd hL x hx
      linarith
termination_by u v => u.length + v.length

/-- The shuffle product of harmonic polylogarithms: for `0 < x < 1`,
`H(u; x) H(v; x) = ∑_{w ∈ u ⧢ v} H(w; x)`, the sum over the shuffles counted with
multiplicity. -/
theorem hpl_mul_hpl (u v : List Letter) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl u x * hpl v x = ((shuffle u v).map fun w => hpl w x).sum :=
  hpl_mul_hpl_aux u v x hx

end QED.Polylog.HPL
