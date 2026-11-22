/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.LeafForm

/-!
# Leaf exponents as integer-affine forms

The leaf exponents `ℓₖ` of `QED.DimReg.Sector.leafExp` are affine in `(ν, d / 2)` with integer
coefficients. This module computes them as data, `(c₀, (cᵢ)ᵢ, c_d)` with
`ℓₖ = c₀ + Σᵢ cᵢ νᵢ + c_d · d / 2` (`QED.DimReg.Sector.leafForm`), by list arithmetic that the
kernel evaluates, and proves that the data evaluate to `leafExp`
(`QED.DimReg.Sector.leafExp_eq_eval_leafForm`). Boxes are given by flag lists
(`QED.DimReg.Sector.flagSet`), so that a family's sector data can be checked by `decide`.

Forms emitted by an untrusted program can then be compared with `leafForm` by `decide`, and
statements about the leaf exponents along a line (positivity of slopes, convergence intervals)
become finite integer checks.
-/

@[expose] public section

open Complex

namespace QED.DimReg.Sector

variable {N : ℕ}

/-! ### Boxes as flag lists -/

/-- The box of a flag list: the coordinates `i` with flag `true`. -/
def flagSet (fl : List Bool) : Finset (Fin N) := Finset.univ.filter fun i => fl.getD i false

/-- The flag list of a box. -/
def flagsOf (T : Finset (Fin N)) : List Bool := (List.finRange N).map fun i => decide (i ∈ T)

theorem getD_map_finRange {α : Type*} (f : Fin N → α) (i : Fin N) (a : α) :
    ((List.finRange N).map f).getD i a = f i := by
  simp [List.getD_eq_getElem?_getD]

theorem mem_flagSet {fl : List Bool} {i : Fin N} : i ∈ flagSet fl ↔ fl.getD i false = true := by
  simp [flagSet]

theorem flagSet_flagsOf (T : Finset (Fin N)) : flagSet (flagsOf T) = T := by
  ext i
  rw [mem_flagSet, flagsOf, getD_map_finRange, decide_eq_true_iff]

/-! ### Integer-affine forms -/

/-- An integer-affine form `c₀ + Σᵢ cᵢ νᵢ + c_d · d / 2`, as `(c₀, [cᵢ], c_d)`. -/
abbrev AffForm := ℤ × List ℤ × ℤ

/-- The value of an affine form. -/
noncomputable def AffForm.eval (f : AffForm) (ν : Fin N → ℂ) (d : ℂ) : ℂ :=
  (f.1 : ℂ) + ∑ i : Fin N, (f.2.1.getD i 0 : ℂ) * ν i + (f.2.2 : ℂ) * (d / 2)

/-- The exponent of `yₖ` in `(φ_σ y)ᵢ`, as an integer. -/
def pullZ (ps : List (Fin N × Fin N)) (k i : Fin N) : ℤ := ((pullExp ps (unitExp i)).getD k 0 : ℕ)

/-- **The leaf exponent `ℓₖ` as an affine form**, on the box with flags `fl`. -/
def leafForm (D : List ℕ) (fl : List Bool) (ps : List (Fin N × Fin N)) (m : List ℕ) (k : Fin N) :
    AffForm :=
  (1 + ((jacExp ps).getD k 0 : ℕ) - ((List.finRange N).map (pullZ ps k)).sum,
    (List.finRange N).map (fun i : Fin N =>
      if fl.getD i false then -pullZ ps k i else pullZ ps k i),
    ((List.finRange N).map fun i : Fin N =>
      if fl.getD i false then ((D.getD i 0 : ℕ) : ℤ) * pullZ ps k i else 0).sum -
      ((m.getD k 0 : ℕ) : ℤ))

/-- The forms of all coordinates of a leaf. -/
def leafForms (D : List ℕ) (fl : List Bool) (ps : List (Fin N × Fin N)) (m : List ℕ) :
    List AffForm :=
  (List.finRange N).map (leafForm D fl ps m)

theorem sum_map_finRange {M : Type*} [AddCommMonoid M] (f : Fin N → M) :
    ((List.finRange N).map f).sum = ∑ i, f i := (Fin.sum_univ_def f).symm

/-- **The forms evaluate to the leaf exponents.** -/
theorem leafExp_eq_eval_leafForm (D : List ℕ) (fl : List Bool) (ps : List (Fin N × Fin N))
    (m : List ℕ) (ν : Fin N → ℂ) (d : ℂ) (k : Fin N) :
    leafExp D (flagSet fl) ps m ν d k = (leafForm D fl ps m k).eval ν d := by
  simp only [leafExp, boxE, AffForm.eval, leafForm, sum_map_finRange, getD_map_finRange,
    mem_flagSet, pullE]
  push_cast
  simp only [pullZ]
  simp only [Int.cast_natCast]
  have h : ∀ i : Fin N, (if fl.getD i false = true then -ν i - 1 + (D.getD i 0 : ℂ) * (d / 2)
      else ν i - 1) * ((pullExp ps (unitExp i)).getD k 0 : ℂ) =
      -((pullExp ps (unitExp i)).getD k 0 : ℂ) +
        (if fl.getD i false = true then -((pullExp ps (unitExp i)).getD k 0 : ℂ)
          else ((pullExp ps (unitExp i)).getD k 0 : ℂ)) * ν i +
        (if fl.getD i false = true then (D.getD i 0 : ℂ) *
          ((pullExp ps (unitExp i)).getD k 0 : ℂ) else 0) * (d / 2) := by
    intro i; split_ifs <;> ring
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, Finset.sum_neg_distrib]
  ring

end QED.DimReg.Sector
