/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopPoly
public import QED.DimReg.ThreeLoopLine

/-!
# The face `x₇ = x₈ = 0` of the three-loop Lee–Pomeransky polynomial: data and checker

Every label of the set (d) certificate has `ν₇, ν₈ ≤ 0`. Their values are expressed through the
Lee–Pomeransky integrals of the restriction `G₇ = G|_{x₇ = x₈ = 0}`
(`QED.DimReg.ThreeLoop.g7`, 64 terms in seven variables, partial degrees `(1,1,1,2,2,2,2)`).
This file holds the computable data used to certify a sector decomposition of `G₇` and the line
`λ ↦ (n + λw, d₀ + 6λ)` with `w = (1, 1, 1, 1, 2, 2, 2)`:

* `faceRestrict`, `g7`, `d7`, `deg_g7`;
* `decodeTree`: splitting trees stored as preorder codes (`48` a leaf, `7i + j` a node `(i, j)`)
  packed into natural numbers, so the data are a few kilobytes of literals;
* `formU`, `leafForm_snd`: the `ν`- and `d`-parts of a leaf form from the pulled-back unit
  exponents, which the checker of `QED.DimReg.ThreeLoopPrune` carries down the tree;
* `boxPoly7`, `boxPoly7_eq`: the box polynomials by list operations.
-/

@[expose] public section

namespace QED.DimReg.ThreeLoop

open QED.DimReg.Sector QED.DimReg.LineCont

/-- The terms of a polynomial in nine variables with `x₇`- and `x₈`-exponent `0`, as a polynomial
in the first seven variables. -/
def faceRestrict (P : NPoly) : NPoly :=
  (P.filter fun t => t.1.getD 7 0 == 0 && t.1.getD 8 0 == 0).map fun t => (t.1.take 7, t.2)

/-- **The face polynomial** `G₇ = G|_{x₇ = x₈ = 0}`. -/
def g7 : NPoly := faceRestrict lpPolyLit

theorem length_g7 : g7.length = 64 := by decide +kernel

/-- Bounds for the partial degrees of `G₇`. -/
def d7 : List ℕ := [1, 1, 1, 2, 2, 2, 2]

theorem deg_g7 : ∀ t ∈ g7, ∀ i : Fin 7, t.1.getD i 0 ≤ d7.getD i 0 := by decide +kernel

/-- The direction of the line in `ν`. -/
def w7 : Fin 7 → ℕ := ![1, 1, 1, 1, 2, 2, 2]

/-- The direction of the line in `d / 2`. -/
def h7 : ℕ := 3

/-! ### Trees as packed codes -/

/-- The node `(i, j)` of a code `c = 7i + j`. -/
def nodeOf (c : ℕ) : Fin 7 × Fin 7 := (⟨c / 7 % 7, Nat.mod_lt _ (by decide)⟩, ⟨c % 7,
  Nat.mod_lt _ (by decide)⟩)

/-- The `k` six-bit codes of a packed number, lowest first. -/
def unpack : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, n => n % 64 :: unpack k (n / 64)

/-- Decode a preorder code list into a tree, with fuel (`48` a leaf, `7i + j` a node). -/
def decodeAux : ℕ → List ℕ → Option (SplitTree 7 × List ℕ)
  | 0, _ => none
  | _ + 1, [] => none
  | n + 1, c :: cs =>
    if c = 48 then some (.leaf, cs) else
      match decodeAux n cs with
      | none => none
      | some (l, cs') =>
        match decodeAux n cs' with
        | none => none
        | some (r, cs'') => some (.node (nodeOf c).1 (nodeOf c).2 l r, cs'')

/-- Decode a packed tree (the leaf if the data are malformed). -/
def decodeTree (data : List ℕ) : SplitTree 7 :=
  match decodeAux (45 * data.length + 1) (data.flatMap (unpack 45)) with
  | some (t, _) => t
  | none => .leaf

/-! ### Leaf forms from pulled unit exponents -/

end QED.DimReg.ThreeLoop

namespace QED.DimReg.LineCont

open QED.DimReg.Sector

variable {N : ℕ}

/-- The `ν`- and `d`-parts of a leaf form, from the pulled unit exponents `U` (constant `0`). -/
def formU (D : List ℕ) (fl : List Bool) (U : List (List ℕ)) (m : List ℕ) (k : Fin N) :
    AffForm :=
  (0, (List.finRange N).map (fun i : Fin N =>
      if fl.getD i false then -(((U.getD i []).getD k 0 : ℕ) : ℤ)
      else (((U.getD i []).getD k 0 : ℕ) : ℤ)),
    ((List.finRange N).map fun i : Fin N =>
      if fl.getD i false then ((D.getD i 0 : ℕ) : ℤ) * (((U.getD i []).getD k 0 : ℕ) : ℤ)
      else 0).sum - ((m.getD k 0 : ℕ) : ℤ))

/-- The unit exponents `e₀, …, e_{N-1}`. -/
def unitList (N : ℕ) : List (List ℕ) := (List.finRange N).map fun i : Fin N => unitExp i

theorem pull_nil (Q : NPoly) : Q.pull ([] : List (Fin N × Fin N)) = Q := by
  simp [NPoly.pull, pullExp]

theorem pull_cons (p : Fin N × Fin N) (ps : List (Fin N × Fin N)) (Q : NPoly) :
    Q.pull (p :: ps) = (Q.pull [p]).pull ps := by
  simp [NPoly.pull, pullExp, Function.comp_def]

theorem map_pullExp_cons (p : Fin N × Fin N) (ps : List (Fin N × Fin N)) (U : List (List ℕ)) :
    U.map (pullExp (p :: ps)) = (U.map (pullStep p.1 p.2)).map (pullExp ps) := by
  simp [pullExp, Function.comp_def]

theorem formOk_congr {w : Fin N → ℕ} {h : ℕ} {f g : AffForm} (e : f.2 = g.2) :
    formOk w h f = formOk w h g := by
  obtain ⟨a, b⟩ := f
  obtain ⟨c, d⟩ := g
  simp only at e
  subst e
  rfl

theorem leafForm_snd (D : List ℕ) (fl : List Bool) (ps : List (Fin N × Fin N)) (m : List ℕ)
    (k : Fin N) :
    (leafForm D fl ps m k).2 = (formU D fl ((unitList N).map (pullExp ps)) m k).2 := by
  have hU : ∀ i : Fin N, ((unitList N).map (pullExp ps)).getD i [] = pullExp ps (unitExp i) := by
    intro i
    simp only [unitList, List.map_map]
    exact getD_map_finRange (fun i : Fin N => (pullExp ps ∘ unitExp) i) i []
  simp only [leafForm, formU, hU, pullZ]

end QED.DimReg.LineCont

namespace QED.DimReg.ThreeLoop

open QED.DimReg.Sector QED.DimReg.LineCont

/-! ### The checker of one box -/

/-- The box exponent with flags `fl`, by list operations. -/
def boxExpL (fl : List Bool) (α : List ℕ) : List ℕ :=
  (List.finRange 7).map fun i : Fin 7 =>
    if fl.getD i false then d7.getD i 0 - α.getD i 0 else α.getD i 0

/-- The box polynomial on the box with flags `fl`. -/
def boxPoly7 (fl : List Bool) : NPoly := g7.map fun t => (boxExpL fl t.1, t.2)

theorem boxPoly7_eq (fl : List Bool) : boxPoly7 fl = boxPolyF (flagSet (N := 7) fl) d7 g7 := by
  simp only [boxPoly7, boxPolyF, boxExpL, boxExpF, mem_flagSet]

end QED.DimReg.ThreeLoop
