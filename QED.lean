/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.Minkowski
public import QED.Algebra.Dirac
public import QED.Algebra.Gordon
public import QED.Algebra.Contraction
public import QED.Algebra.Spinor

/-!
# QED

Library root of the QED-dev formalization of experimentally relevant quantum
electrodynamics calculations, beginning with the one-loop electron magnetic
anomaly.

The package pins Lean `v4.35.0` and Mathlib `v4.35.0`. The modules so far
are proved infrastructure:

* `QED.Algebra.Minkowski`: four-vectors and the mostly-plus Minkowski form;
* `QED.Algebra.Dirac`: Weyl-representation gamma matrices with the Clifford
  relation, the Dirac-adjoint matrix, slash, and Lorentz generators;
* `QED.Algebra.Gordon`: gamma-matrix products, eqs. (38.19)–(38.20), and the
  Gordon identity (38.18);
* `QED.Algebra.Contraction`: the contraction identities (47.18)–(47.21) at
  `d = 4`;
* `QED.Algebra.Spinor`: the Dirac adjoint, on-shell spinors with the Dirac
  equation and normalization (38.17), and the Gordon identity for spinors.

No source-facing declaration has been approved or frozen. See `README.md` and
`docs/campaign/STATUS.md` for the campaign state.
-/
