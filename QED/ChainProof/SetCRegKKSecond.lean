/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegKKFirst
public import QED.ChainProof.SetCRegKKQChg

/-!
# Set (c): the second Ward step summed over the twelve main classes

Helper level for `QED.ChainProof.SetCRegDisp.IsKKSum` (`QED/ChainProof/SetCRegKKNorm.lean`).
After the first Ward step (`QED.ChainProof.SetCRegDisp.kkLimX_sum_first`) the sum of the
pointwise limits of the twelve longitudinal integrands is `K₀ + K₆ + K₁₀ + kCst · S`, `S` ten
pinched values. The second Ward step (`QED/ChainProof/SetCRegKKQ.lean`) writes each pinched value
through doubly pinched values `Q(i, d, d')` and end terms; the classes `0`, `6`, `10` carry the
doubly pinched values `Q(i, 0, 3)` and three end terms
(`QED.ChainProof.SetCMainB.kkLimX_kkH_ext`). Of the fifteen doubly pinched values twelve cancel
in pairs (`QED/ChainProof/SetCRegKKQChg.lean`); three survive:

* `Q(5, 1, 0)`: the chain `γ^z S(p' + ℓ₁) γ^μ S(p + ℓ₁) γ^z`, in which no electron line carries
  the element momentum (the one-loop vertex times the element integral);
* `Q(4, 1, 3)`: `γ^μ S(p - k) Σ(p)`, and `Q(9, 2, 0)`: `Σ(p') S(p' - k) γ^μ`, `Σ` the one-loop
  self-energy chain, each depending on one external momentum only.

* `kkZ`, `kkLimX_kkH_ext_Z`: the end terms of the classes with the Ward identities at both ends;
* `kkEndSum`: the eight end terms of the second step;
* **`kkSurv_eq`**: the ten survivors of the first step in doubly pinched values and end terms;
* **`kkLimX_sum_second`**: `∑ᵢ K_i = kCst (Q(5, 1, 0) + Q(4, 1, 3) + Q(9, 2, 0) + E)
  - kCst (Z₀ + Z₆ + Z₁₀)`.
-/

@[expose] public section

open Complex MeasureTheory Set
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCMainB QED.ChainProof.SetCMain QED.ChainProof.SetCUnitM
open QED.TwoLoop.Enumeration

/-- The end terms of a class with the Ward identities at both ends: the terms with `2m - A(p')`
at the Ward vertex or `A(p) - 2m` at the other end. -/
noncomputable def kkZ (i : Fin 12) (R : Params) (p p' : Fin 4 → ℝ) (t : ℝ) (μ a b : Fin 4)
    (x : ℝ) : ℂ :=
  ((kkLimX (kkT i R p p' t (fun a : Fin 9 => (9 : Fin 10).succAbove a)
      fun ℓ => kNi i R p p' .out .inn Finset.univ μ ℓ a b) x -
    ((R.Λ ^ 2 : ℝ) : ℂ) * kkLimX (kkT i R p p' t (fun a : Fin 10 => a)
      fun ℓ => kNi i R p p' .out .inn Finset.univ μ ℓ a b) x) +
  (kkLimX (kkT i R p p' t (fun a : Fin 8 => (eIdx 0).succAbove ((8 : Fin 9).succAbove a))
      fun ℓ => kNi i R p p' .out .one (Finset.univ.erase 0) μ ℓ a b) x -
    ((R.Λ ^ 2 : ℝ) : ℂ) * kkLimX (kkT i R p p' t (fun a : Fin 9 => (eIdx 0).succAbove a)
      fun ℓ => kNi i R p p' .out .one (Finset.univ.erase 0) μ ℓ a b) x)) +
  -1 * (kkLimX (kkT i R p p' t
      (fun a : Fin 8 => (eIdx 3).succAbove ((8 : Fin 9).succAbove a))
      fun ℓ => kNi i R p p' .one .inn (Finset.univ.erase 3) μ ℓ a b) x -
    ((R.Λ ^ 2 : ℝ) : ℂ) * kkLimX (kkT i R p p' t (fun a : Fin 9 => (eIdx 3).succAbove a)
      fun ℓ => kNi i R p p' .one .inn (Finset.univ.erase 3) μ ℓ a b) x)

/-- The eight end terms of the second Ward step on the survivors of the first. -/
noncomputable def kkEndSum (R : Params) (p p' : Fin 4 → ℝ) (t : ℝ) (μ a b : Fin 4) (x : ℝ) :
    ℂ :=
  kkEnd 2 R p p' t 0 .out μ a b x - kkEnd 3 R p p' t 3 .inn μ a b x -
    kkEnd 4 R p p' t 1 .out μ a b x + kkEnd 4 R p p' t 0 .out μ a b x +
    kkEnd 5 R p p' t 1 .inn μ a b x - kkEnd 8 R p p' t 2 .out μ a b x -
    kkEnd 9 R p p' t 3 .inn μ a b x + kkEnd 9 R p p' t 2 .inn μ a b x

theorem qι_zero_three : qι 0 3 = fun a : Fin 8 => (eIdx 0).succAbove ((2 : Fin 9).succAbove a) := by
  decide

section Values

variable {R : Params} {p p' : Fin 4 → ℝ} {t x : ℝ}
  (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) (hp : Minkowski.dot p p = -R.m ^ 2)
  (hp' : Minkowski.dot p' p' = -R.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
  (ht : R.m ≤ t) (hx : x ∈ Ioo (0 : ℝ) 1)
include hm hγ hγΛ hp hp' hq ht hx

/-- **A class with the Ward identities at both ends**: `K_i = -kCst (Z_i - Q(i, 0, 3))`. -/
theorem kkLimX_kkH_ext_Z {i : Fin 12} (hW : kWardD i = 4) (hs : kSgnW i * kSgnO i = -1)
    (μ a b : Fin 4) :
    kkLimX (kkH i R p p' t μ a b) x =
      -kCst R * (kkZ i R p p' t μ a b x - kkQ i R p p' t 0 3 μ a b x) := by
  rw [kkLimX_kkH_ext (w := fun _ => 1) hm hγ hγΛ hp hp' hq ht (integrableOn_const (by simp)) hx
    hW μ a b, kkQ, qι_zero_three, erase_erase_comm 0 3, kkZ]
  have e : (((kSgnW i : ℤ) : ℝ) : ℂ) * (((kSgnO i : ℤ) : ℝ) : ℂ) = -1 := by
    rw [← Complex.ofReal_mul, ← Int.cast_mul, hs]
    simp
  rw [e]
  ring

/-- **The ten survivors of the first step in doubly pinched values and end terms.** -/
theorem kkSurv_eq (μ a b : Fin 4) :
    kkSurv R p p' t μ a b x =
      kkQ 1 R p p' t 0 3 μ a b x - kkQ 1 R p p' t 0 2 μ a b x - kkQ 2 R p p' t 0 3 μ a b x -
        kkQ 3 R p p' t 3 0 μ a b x + kkQ 4 R p p' t 1 3 μ a b x - kkQ 4 R p p' t 0 3 μ a b x +
        kkQ 5 R p p' t 1 0 μ a b x - kkQ 7 R p p' t 2 1 μ a b x + kkQ 7 R p p' t 2 0 μ a b x +
        kkQ 8 R p p' t 2 3 μ a b x - kkQ 9 R p p' t 3 0 μ a b x + kkQ 9 R p p' t 2 0 μ a b x +
        kkEndSum R p p' t μ a b x := by
  have hw : IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Ioo 0 1) := integrableOn_const (by simp)
  have i₁ := kkPin_eq_int hm hγ hγΛ hp hp' hq ht hw hx (i := 1) (d := 0) 2 rfl (by decide)
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) μ a b
  have i₇ := kkPin_eq_int hm hγ hγΛ hp hp' hq ht hw hx (i := 7) (d := 2) 0 rfl (by decide)
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) μ a b
  have o₂ := kkPin_eq_out hm hγ hγΛ hp hp' hq ht hw hx (i := 2) (d := 0) rfl (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) μ a b
  have o₄₁ := kkPin_eq_out hm hγ hγΛ hp hp' hq ht hw hx (i := 4) (d := 1) rfl (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) μ a b
  have o₄₀ := kkPin_eq_out hm hγ hγΛ hp hp' hq ht hw hx (i := 4) (d := 0) rfl (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) μ a b
  have o₈ := kkPin_eq_out hm hγ hγΛ hp hp' hq ht hw hx (i := 8) (d := 2) rfl (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) μ a b
  have n₃ := kkPin_eq_in hm hγ hγΛ hp hp' hq ht hw hx (i := 3) (d := 3) rfl (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) μ a b
  have n₅ := kkPin_eq_in hm hγ hγΛ hp hp' hq ht hw hx (i := 5) (d := 1) rfl (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) μ a b
  have n₉₃ := kkPin_eq_in hm hγ hγΛ hp hp' hq ht hw hx (i := 9) (d := 3) rfl (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) μ a b
  have n₉₂ := kkPin_eq_in hm hγ hγΛ hp hp' hq ht hw hx (i := 9) (d := 2) rfl (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) μ a b
  rw [kkSurv, i₁, i₇, o₂, o₄₁, o₄₀, o₈, n₃, n₅, n₉₃, n₉₂, kkEndSum]
  simp only [kSgnO]
  push_cast
  ring

/-- **The second Ward step summed over the twelve main classes**: of the doubly pinched values
only `Q(5, 1, 0)`, `Q(4, 1, 3)`, `Q(9, 2, 0)` survive, besides the end terms. -/
theorem kkLimX_sum_second (μ a b : Fin 4) :
    ∑ i, kkLimX (kkH i R p p' t μ a b) x =
      kCst R * (kkQ 5 R p p' t 1 0 μ a b x + kkQ 4 R p p' t 1 3 μ a b x +
          kkQ 9 R p p' t 2 0 μ a b x + kkEndSum R p p' t μ a b x) -
        kCst R * (kkZ 0 R p p' t μ a b x + kkZ 6 R p p' t μ a b x +
          kkZ 10 R p p' t μ a b x) := by
  rw [kkLimX_sum_first hm hγ hγΛ hp hp' hq ht hx μ a b,
    kkLimX_kkH_ext_Z hm hγ hγΛ hp hp' hq ht hx (i := 0) rfl (by decide) μ a b,
    kkLimX_kkH_ext_Z hm hγ hγΛ hp hp' hq ht hx (i := 6) rfl (by decide) μ a b,
    kkLimX_kkH_ext_Z hm hγ hγΛ hp hp' hq ht hx (i := 10) rfl (by decide) μ a b,
    kkSurv_eq hm hγ hγΛ hp hp' hq ht hx μ a b, kkQ_zero_three, kkQ_one_two, kkQ_ten_nine,
    kkQ_one_seven, kkQ_seven_eight, kkQ_six_four]
  ring

end Values

end QED.ChainProof.SetCRegDisp

end
