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
public import QED.Algebra.OnShell
public import QED.Integration.EnergyIntegral
public import QED.Integration.ShiftedEnergyIntegral
public import QED.Integration.FeynmanParameter
public import QED.Integration.LoopBounds
public import QED.OneLoop.VertexAlgebra
public import QED.OneLoop.VertexEnergyFirst
public import QED.OneLoop.VertexClosedForm
public import QED.OneLoop.NumeratorReduction
public import QED.Integration.SpatialIntegral
public import QED.Algebra.FormFactorIndependence
public import QED.Frozen.OneLoop.ElectronPropagator
public import QED.Frozen.OneLoop.PhotonPropagator
public import QED.Frozen.OneLoop.VertexIntegrand
public import QED.Frozen.OneLoop.EnergyFirstIntegral
public import QED.Frozen.OneLoop.VertexLimitExists

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
  equation and normalization (38.17), and the Gordon identity for spinors;
* `QED.Algebra.OnShell`: reverse Cauchy–Schwarz for future-pointing vectors
  on one mass shell, so `q² ≥ 0`;
* `QED.Integration.EnergyIntegral`: the loop-energy integrals evaluated by
  analytic continuation to the slit plane, which replaces Wick rotation
  (obligation O-7);
* `QED.Integration.ShiftedEnergyIntegral`: shifted quadratic-numerator energy
  integrals, boundary values from the upper half plane, and Lipschitz bounds
  for complex powers;
* `QED.Integration.FeynmanParameter`: Feynman parameters for two and three
  denominators (obligation O-5);
* `QED.Integration.LoopBounds`: uniform lower bounds for regulated
  denominators;
* `QED.OneLoop.VertexAlgebra`: the entrywise factorization of the frozen
  vertex integrand, its numerator's structure, and the Feynman combination of
  its denominators.
* `QED.OneLoop.VertexEnergyFirst`: the analysis behind theorem (E) and the
  representation of its limit;
* `QED.OneLoop.VertexClosedForm`: the Fubini swap at `ε = 0` and the reflection
  symmetry of the Feynman measure;
* `QED.OneLoop.NumeratorReduction`: the contraction of the numerator and its
  on-shell reduction (63.14)–(63.17);
* `QED.Integration.SpatialIntegral`: three-dimensional loop integrals;
* `QED.Algebra.FormFactorIndependence`: gamma-matrix traces and the linear
  independence of the two on-shell vertex structures.

Author-approved frozen declarations live under `QED/Frozen/` and are bound by
`QED/Frozen/manifest.json` (checked by `scripts/check_frozen_anchors.py`). The
Minkowski and Dirac definitions (`metric`, `dot`, `lower`, `gamma`, `slash`) are
frozen in `QED/Frozen/Algebra/` and re-exported by `QED.Algebra.Minkowski` and
`QED.Algebra.Dirac`. The root imports every frozen anchor. The theorem anchor
`QED.Frozen.OneLoop.VertexLimitExists` is sealed: its proof is
`QED.Provider.OneLoop.vertexLimit_existsUnique`. See `README.md` and
`docs/campaign/STATUS.md` for the campaign state.
-/
