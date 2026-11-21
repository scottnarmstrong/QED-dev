/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.Symanzik

/-!
# A certified sector decomposition of the two-loop self-energy family

The Lee–Pomeransky polynomial of `QED.Algebra.IBPCert.Pilot.twoLoopSE` is `G = U + F`
(`QED.DimReg.Symanzik`), with positive coefficients and partial degrees `D = (1, 1, 2, 2, 2)`.
The orthant `(0, ∞)⁵` is the union of the `2⁵` boxes of `QED.DimReg.Convergence`; on the box
`T` (the coordinates `i ∈ T` lie in `(1, ∞)`) the substitution `xᵢ = 1 / yᵢ` turns
`G` into `y^{-D_T} P_T(y)` with `P_T` a polynomial with positive coefficients on the unit cube
(`QED.DimReg.TwoLoopSESector.boxPoly`: the exponent `αᵢ` becomes `Dᵢ - αᵢ` for `i ∈ T`).

For every box an untrusted program produced a splitting tree (`boxTrees`, 401 leaves in all).
`QED.DimReg.TwoLoopSESector.check_boxCerts` checks by `decide +kernel` that every tree is valid
and that `P_T` passes the leaf test on every leaf. By `QED.DimReg.Sector.SDCert.sound`, on every
leaf `P_T ∘ φ_σ = y ^ m · P̃` with `P̃ ≥ 1` on the closed cube.

## Main results

* `QED.DimReg.TwoLoopSESector.lpPoly_eq`, `degs_eq`: `G` as a natural sparse polynomial and its
  partial degrees.
* `QED.DimReg.TwoLoopSESector.check_boxCerts`: the 32 certificates pass.
* `QED.DimReg.TwoLoopSESector.boxCert_sound`: their consequences, by the soundness theorem.
-/

@[expose] public section

namespace QED.DimReg.TwoLoopSESector

open QED.Algebra.IBPCert QED.DimReg.Sector QED.DimReg.Symanzik

/-- The Lee–Pomeransky polynomial `G = U + F` of `twoLoopSE`, with natural coefficients. -/
def lpPoly : NPoly := toNPoly (LinComb.add (symU Pilot.twoLoopSE) (symF Pilot.twoLoopSE))

/-- The partial degrees of a sparse polynomial. -/
def degs (P : NPoly) : List ℕ := P.foldr (fun t acc => List.zipWith Nat.max t.1 acc)
  (List.replicate 5 0)

/-- The exponent on a box: `αᵢ ↦ Dᵢ - αᵢ` where the flag is set. -/
def boxExp : List ℕ → List ℕ → List Bool → List ℕ
  | a :: as, dd :: ds, b :: bs => (bif b then dd - a else a) :: boxExp as ds bs
  | _, _, _ => []

/-- The polynomial `P_T` on the box `T` (exponent `αᵢ ↦ Dᵢ - αᵢ` for `i ∈ T`). -/
def boxPoly (T : List Bool) (P : NPoly) : NPoly :=
  P.map fun t => (boxExp t.1 (degs P) T, t.2)

theorem isNat_lpPoly :
    isNat (LinComb.add (symU Pilot.twoLoopSE) (symF Pilot.twoLoopSE)) = true := by
  decide +kernel

theorem degs_eq : degs lpPoly = [1, 1, 2, 2, 2] := by
  decide +kernel

theorem length_lpPoly : lpPoly.length = 21 := by
  decide +kernel

def boxTrees : List (List Bool × SplitTree 5) := [
  ([false, false, false, false, false], (.node 0 2 (.node 2 4 (.node 1 3 (.node 2 3 .leaf (.node
    3 4 .leaf .leaf)) (.node 1 2 (.node 1 4 .leaf .leaf) .leaf)) (.node 1 3 (.node 2 3 .leaf
    (.node 3 4 .leaf .leaf)) (.node 1 2 (.node 1 4 .leaf .leaf) .leaf))) (.node 0 4 (.node 1 3
    (.node 0 3 .leaf (.node 3 4 .leaf .leaf)) (.node 0 1 .leaf (.node 1 4 .leaf .leaf))) (.node 1
    3 (.node 0 3 .leaf (.node 3 4 .leaf .leaf)) (.node 0 1 .leaf (.node 1 4 .leaf .leaf)))))),
  ([true, false, false, false, false], (.node 1 3 (.node 3 4 .leaf .leaf) (.node 1 4 .leaf
    .leaf))),
  ([false, true, false, false, false], (.node 0 2 (.node 2 4 .leaf .leaf) (.node 0 4 .leaf
    .leaf))),
  ([false, false, true, false, false], (.node 1 3 (.node 3 4 .leaf .leaf) (.node 1 4 .leaf
    .leaf))),
  ([false, false, false, true, false], (.node 0 2 (.node 2 4 .leaf .leaf) (.node 0 4 .leaf
    .leaf))),
  ([false, false, false, false, true], (.node 0 1 (.node 1 2 (.node 2 3 .leaf .leaf) (.node 1 3
    .leaf .leaf)) (.node 0 2 (.node 2 3 .leaf .leaf) (.node 0 3 .leaf .leaf)))),
  ([true, true, false, false, false], .leaf),
  ([true, false, true, false, false], (.node 1 3 (.node 3 4 (.node 0 2 (.node 0 2 .leaf .leaf)
    .leaf) (.node 0 2 (.node 0 2 .leaf .leaf) .leaf)) (.node 1 4 (.node 0 2 (.node 0 2 .leaf
    .leaf) .leaf) (.node 0 2 (.node 0 2 .leaf .leaf) .leaf)))),
  ([true, false, false, true, false], .leaf),
  ([true, false, false, false, true], .leaf),
  ([false, true, true, false, false], .leaf),
  ([false, true, false, true, false], (.node 0 2 (.node 2 4 (.node 1 3 (.node 1 3 .leaf .leaf)
    .leaf) (.node 1 3 (.node 1 3 .leaf .leaf) .leaf)) (.node 0 4 (.node 1 3 (.node 1 3 .leaf
    .leaf) .leaf) (.node 1 3 (.node 1 3 .leaf .leaf) .leaf)))),
  ([false, true, false, false, true], .leaf),
  ([false, false, true, true, false], (.node 2 3 .leaf .leaf)),
  ([false, false, true, false, true], (.node 2 4 .leaf .leaf)),
  ([false, false, false, true, true], (.node 3 4 .leaf .leaf)),
  ([true, true, true, false, false], (.node 0 2 (.node 0 2 .leaf .leaf) .leaf)),
  ([true, true, false, true, false], (.node 1 3 (.node 1 3 .leaf .leaf) .leaf)),
  ([true, true, false, false, true], (.node 0 1 (.node 1 4 (.node 1 4 .leaf .leaf) .leaf) (.node
    0 4 (.node 0 4 .leaf .leaf) .leaf))),
  ([true, false, true, true, false], (.node 0 2 (.node 0 2 .leaf (.node 2 3 .leaf .leaf)) (.node
    0 3 .leaf (.node 2 3 .leaf .leaf)))),
  ([true, false, true, false, true], (.node 0 2 (.node 0 2 .leaf (.node 2 4 .leaf .leaf)) (.node
    0 4 .leaf (.node 2 4 .leaf .leaf)))),
  ([true, false, false, true, true], (.node 3 4 (.node 0 4 .leaf .leaf) (.node 0 3 .leaf
    .leaf))),
  ([false, true, true, true, false], (.node 1 3 (.node 1 3 .leaf (.node 2 3 .leaf .leaf)) (.node
    1 2 .leaf (.node 2 3 .leaf .leaf)))),
  ([false, true, true, false, true], (.node 2 4 (.node 1 4 .leaf .leaf) (.node 1 2 .leaf
    .leaf))),
  ([false, true, false, true, true], (.node 1 3 (.node 1 3 .leaf (.node 3 4 .leaf .leaf)) (.node
    1 4 .leaf (.node 3 4 .leaf .leaf)))),
  ([false, false, true, true, true], (.node 2 3 (.node 3 4 .leaf (.node 2 4 .leaf .leaf)) (.node
    2 4 .leaf (.node 3 4 .leaf .leaf)))),
  ([true, true, true, true, false], (.node 0 2 (.node 0 2 (.node 1 3 (.node 1 3 .leaf .leaf)
    .leaf) (.node 1 3 (.node 1 3 .leaf (.node 2 3 .leaf .leaf)) (.node 1 2 .leaf (.node 2 3 .leaf
    .leaf)))) (.node 1 3 (.node 0 3 .leaf (.node 1 3 .leaf (.node 2 3 .leaf .leaf))) (.node 0 1
    (.node 0 3 .leaf (.node 2 3 .leaf .leaf)) (.node 1 2 .leaf (.node 2 3 .leaf .leaf)))))),
  ([true, true, true, false, true], (.node 2 4 (.node 1 4 (.node 1 4 (.node 0 2 (.node 0 2
    (.node 0 4 (.node 0 4 .leaf .leaf) .leaf) .leaf) .leaf) (.node 0 1 (.node 0 1 (.node 0 2
    (.node 0 2 (.node 0 4 .leaf .leaf) .leaf) .leaf) .leaf) .leaf)) (.node 0 1 (.node 0 2 (.node 0
    2 (.node 0 4 .leaf .leaf) .leaf) .leaf) .leaf)) (.node 0 2 (.node 1 2 (.node 0 1 (.node 1 2
    (.node 1 4 (.node 1 4 .leaf .leaf) .leaf) .leaf) (.node 0 2 (.node 0 4 (.node 0 4 .leaf .leaf)
    .leaf) .leaf)) .leaf) (.node 0 1 .leaf (.node 1 2 .leaf .leaf))))),
  ([true, true, false, true, true], (.node 3 4 (.node 0 4 (.node 0 4 (.node 1 3 (.node 1 3
    (.node 1 4 (.node 1 4 .leaf .leaf) .leaf) .leaf) .leaf) (.node 0 1 .leaf (.node 0 1 .leaf
    (.node 1 3 (.node 1 3 (.node 1 4 .leaf .leaf) .leaf) .leaf)))) (.node 0 1 .leaf (.node 1 3
    (.node 1 3 (.node 1 4 .leaf .leaf) .leaf) .leaf))) (.node 0 3 (.node 1 3 (.node 0 1 (.node 1 3
    (.node 1 4 (.node 1 4 .leaf .leaf) .leaf) .leaf) (.node 0 3 (.node 0 4 (.node 0 4 .leaf .leaf)
    .leaf) .leaf)) .leaf) (.node 0 1 .leaf (.node 1 3 .leaf .leaf))))),
  ([true, false, true, true, true], (.node 3 4 (.node 2 4 (.node 2 3 (.node 0 2 (.node 0 2
    (.node 0 3 (.node 0 4 .leaf .leaf) .leaf) .leaf) .leaf) (.node 0 2 (.node 0 4 .leaf .leaf)
    .leaf)) (.node 0 2 (.node 0 4 .leaf .leaf) .leaf)) (.node 2 3 (.node 2 4 (.node 0 2 (.node 0 2
    (.node 0 3 (.node 0 4 .leaf .leaf) .leaf) .leaf) .leaf) (.node 0 2 (.node 0 3 .leaf .leaf)
    .leaf)) (.node 0 2 (.node 0 3 .leaf .leaf) .leaf)))),
  ([false, true, true, true, true], (.node 2 4 (.node 3 4 (.node 2 3 (.node 1 3 (.node 1 4 .leaf
    .leaf) .leaf) (.node 1 2 (.node 1 3 (.node 1 3 (.node 1 4 .leaf .leaf) .leaf) .leaf) .leaf))
    (.node 1 3 (.node 1 4 .leaf .leaf) .leaf)) (.node 2 3 (.node 1 2 (.node 1 3 .leaf .leaf)
    .leaf) (.node 3 4 (.node 1 2 (.node 1 3 (.node 1 3 (.node 1 4 .leaf .leaf) .leaf) .leaf)
    .leaf) (.node 1 2 (.node 1 3 .leaf .leaf) .leaf))))),
  ([true, true, true, true, true], (.node 2 4 (.node 3 4 (.node 2 3 (.node 0 2 (.node 0 2 (.node
    0 1 (.node 1 3 (.node 1 4 (.node 1 3 (.node 1 4 .leaf .leaf) .leaf) (.node 0 4 .leaf .leaf))
    (.node 0 3 (.node 0 4 .leaf .leaf) .leaf)) (.node 0 3 (.node 0 4 (.node 0 3 (.node 0 4 .leaf
    .leaf) .leaf) (.node 1 4 .leaf .leaf)) (.node 1 3 (.node 1 4 .leaf .leaf) .leaf))) (.node 1 3
    (.node 1 4 .leaf .leaf) .leaf)) (.node 1 3 (.node 1 4 .leaf .leaf) .leaf)) (.node 0 2 (.node 0
    4 (.node 1 2 (.node 1 3 (.node 1 3 (.node 1 4 (.node 0 1 (.node 1 2 (.node 1 4 .leaf .leaf)
    .leaf) (.node 0 2 (.node 0 4 .leaf .leaf) .leaf)) .leaf) .leaf) .leaf) .leaf) (.node 0 1 .leaf
    (.node 1 2 (.node 1 3 (.node 1 3 (.node 1 4 .leaf .leaf) .leaf) .leaf) .leaf))) (.node 0 1
    .leaf (.node 1 2 (.node 1 3 (.node 1 3 (.node 1 4 .leaf .leaf) .leaf) .leaf) .leaf)))) (.node
    0 2 (.node 0 2 (.node 0 1 (.node 1 3 (.node 1 4 (.node 1 3 (.node 1 4 .leaf .leaf) .leaf)
    (.node 0 4 .leaf .leaf)) (.node 0 3 (.node 0 4 .leaf .leaf) .leaf)) (.node 0 3 (.node 0 4
    (.node 0 3 (.node 0 4 .leaf .leaf) .leaf) (.node 1 4 .leaf .leaf)) (.node 1 3 (.node 1 4 .leaf
    .leaf) .leaf))) (.node 1 3 (.node 1 4 .leaf .leaf) .leaf)) (.node 1 3 (.node 1 4 .leaf .leaf)
    .leaf))) (.node 0 3 (.node 2 3 (.node 0 2 (.node 1 2 (.node 1 3 (.node 0 1 (.node 1 2 (.node 1
    3 (.node 1 4 (.node 1 4 .leaf .leaf) .leaf) .leaf) .leaf) (.node 0 2 (.node 0 3 (.node 0 4
    (.node 0 4 .leaf .leaf) .leaf) .leaf) .leaf)) .leaf) .leaf) (.node 0 1 .leaf (.node 1 2 (.node
    1 3 .leaf .leaf) .leaf))) (.node 3 4 (.node 1 2 (.node 1 3 (.node 1 3 (.node 1 4 (.node 0 1
    (.node 1 2 (.node 1 4 .leaf .leaf) .leaf) (.node 1 3 (.node 0 2 (.node 0 4 .leaf (.node 3 4
    .leaf .leaf)) (.node 2 3 .leaf (.node 3 4 .leaf .leaf))) (.node 0 2 (.node 0 4 .leaf (.node 1
    4 .leaf .leaf)) (.node 1 2 (.node 1 4 .leaf .leaf) .leaf)))) .leaf) .leaf) .leaf) .leaf)
    (.node 1 2 (.node 1 3 (.node 0 1 (.node 1 2 (.node 1 3 (.node 1 4 (.node 1 4 .leaf .leaf)
    .leaf) .leaf) .leaf) (.node 0 2 (.node 0 3 (.node 0 4 (.node 0 4 .leaf .leaf) .leaf) .leaf)
    .leaf)) .leaf) .leaf))) (.node 0 2 (.node 0 4 (.node 0 1 .leaf (.node 0 1 .leaf (.node 1 2
    (.node 1 3 (.node 1 3 (.node 1 4 (.node 0 1 (.node 1 2 (.node 1 4 .leaf .leaf) .leaf) (.node 0
    2 (.node 0 4 .leaf .leaf) .leaf)) .leaf) .leaf) .leaf) .leaf))) (.node 3 4 (.node 0 1 .leaf
    (.node 1 2 (.node 1 3 (.node 1 3 (.node 1 4 .leaf .leaf) .leaf) .leaf) .leaf)) (.node 0 1
    .leaf (.node 1 2 (.node 1 3 .leaf .leaf) .leaf)))) (.node 2 3 (.node 0 1 .leaf (.node 1 2
    (.node 1 3 .leaf .leaf) .leaf)) (.node 3 4 (.node 0 1 .leaf (.node 1 2 (.node 1 3 (.node 1 3
    (.node 1 4 .leaf .leaf) .leaf) .leaf) .leaf)) (.node 0 1 .leaf (.node 1 2 (.node 1 3 .leaf
    .leaf) .leaf))))))))]

/-- The 32 box certificates. -/
def boxCerts : List (List Bool × SDCert 5) :=
  boxTrees.map fun bt => (bt.1, ⟨bt.2, [boxPoly bt.1 lpPoly]⟩)

/-- The trees cover all `2⁵` boxes. -/
theorem boxes_eq : (boxCerts.map Prod.fst).length = 32 ∧ (boxCerts.map Prod.fst).Nodup := by
  decide +kernel

/-- **The sector certificates of `twoLoopSE` pass the kernel check.** -/
theorem check_boxCerts : boxCerts.all (fun bc => bc.2.check) = true := by
  decide +kernel

/-- The consequences of the check, for every box: the cube integral of an integrable `g` splits
into the leaf integrals, and on every leaf the box polynomial factorizes as a monomial times a
polynomial `≥ 1` on the closed cube. -/
theorem boxCert_sound {T : List Bool} {c : SDCert 5} (hc : (T, c) ∈ boxCerts)
    {g : (Fin 5 → ℝ) → ℂ} (hg : MeasureTheory.IntegrableOn g (unitCube 5)) :
    (∀ ps ∈ c.tree.paths, MeasureTheory.IntegrableOn (leafIntegrand g ps) (unitCube 5)) ∧
    (∫ y in unitCube 5, g y =
      (c.tree.paths.map fun ps => ∫ y in unitCube 5, leafIntegrand g ps y).sum) ∧
    ∀ ps ∈ c.tree.paths, (∀ y, leafJac ps y = mono (jacExp ps) y) ∧
      ∀ P ∈ c.polys, ∃ (m : List ℕ) (Q : NPoly),
        (∀ y, P.eval (leafMap ps y) = mono m y * Q.eval y) ∧
        ∀ y : Fin 5 → ℝ, (∀ k, 0 ≤ y k) → 1 ≤ Q.eval y := by
  have h := check_boxCerts
  rw [List.all_eq_true] at h
  exact SDCert.sound (h _ hc) hg

end QED.DimReg.TwoLoopSESector
