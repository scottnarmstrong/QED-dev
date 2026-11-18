# Crossed-ladder graph checks

Numerical sanity checks (not proofs) for `QED/TwoLoop/UnitXGraph*.lean`.

- `lean_crossed.py`: a model of `openNum .X` and `openV .X` in the Lean conventions; `paramNum`
  by finite differences along the eigenvectors of G (independent of the Wick formula).
- `target_check.py`: (1) the pointwise second coefficients of `UnitXGraphTraceMain.lean`,
  `c₂[T₁] = (3/K) Ψ₁/U⁶`, `c₂[T₂] = -(1/K) Ψ₂/U⁵`, `c₂[T₃] = 0`, against that model at four
  points (ratios 1 to 7 digits); (2) `Ψ₁, Ψ₂` affine in the split of the electron pair, `U` of the
  engine equal to `xU`, and the exact identities `A₂ = z_M Ψ₁(z_M/2)/(2U⁶)`,
  `A₁ = -z_M Ψ₂(z_M/2)/(2U⁵)` with the engine coefficients of
  `../two_loop_unit_integrals.py` (`integrand_parts('X', [z_A, z_M, z_c, z_a, z_b])`), i.e. the
  merged integrand `crossedTerm 0 0` of `UnitXGraphReduce.lean` is the engine integrand of X.

Run with `nice -n 10 python3 target_check.py` from this directory (numpy, sympy; about a minute).
