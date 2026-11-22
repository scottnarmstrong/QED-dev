/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.IBPCertKron

/-!
# Symmetry relations for split IBP certificates (layer L2)

IBP relations alone do not identify integrals related by a relabelling of the loop momenta: for
example, two sectors with the same graph give two copies of the same master. This module adds
such identities as hypotheses that a certificate step can use.

* `QED.Algebra.IBPCert.permLabel σ ν`: the index vector `a ↦ ν (σ a)` (entries out of range read
  as `0`). If a change of loop momenta maps the denominator `D_a` to `D_{σ a}` for every `a`, the
  integrals at `permLabel σ ν` and at `ν` agree. That is the hypothesis
  `QED.Algebra.IBPCert.Family.SymHoldsAt`, a plain Prop to be proved from the integral.
* `QED.Algebra.IBPCert.symRel σ ν`: the relation `[ν] - [permLabel σ ν]`.
  `QED.Algebra.IBPCert.symRel_eval` shows that it holds under `SymHoldsAt`. A step uses it like
  any proved relation: as an entry `(symRel σ ν, multiplier)` of its `rels`, with the proof in
  `RelsHold` supplied by `symRel_eval`.

Symmetries under which numerators change into combinations of other denominators are relations of
the same kind with more terms; any relation the integral is known to satisfy can enter a step's
`rels` in the same way.
-/

@[expose] public section

namespace QED.Algebra.IBPCert

/-- The index vector `a ↦ ν (σ a)`, for `σ` given as the list of its values. -/
def permLabel (σ : List ℕ) (ν : List ℤ) : List ℤ := σ.map fun a => ν.getD a 0

/-- The relation `[ν] - [permLabel σ ν]`. -/
def symRel (σ : List ℕ) (ν : List ℤ) : List (List ℤ × Poly) := [(ν, [1]), (permLabel σ ν, [-1])]

namespace Family

/-- The integrals at `permLabel σ ν` and at `ν` agree at `d` (a relabelling symmetry). -/
def SymHoldsAt {K : Type*} [Ring K] (F : Family) (I : (Fin F.nProp → ℤ) → K → K) (d : K)
    (σ : List ℕ) (ν : List ℤ) : Prop :=
  I (toVec F.nProp (permLabel σ ν)) d = I (toVec F.nProp ν) d

end Family

theorem symRel_eval {K : Type*} [CommRing K] {F : Family} {I : (Fin F.nProp → ℤ) → K → K}
    {d : K} {σ : List ℕ} {ν : List ℤ} (h : F.SymHoldsAt I d σ ν) :
    LinComb.eval (fun l => I (toVec F.nProp l) d) d (symRel σ ν) = 0 := by
  unfold Family.SymHoldsAt at h
  simp [symRel, LinComb.eval, Poly.eval, h]

end QED.Algebra.IBPCert
