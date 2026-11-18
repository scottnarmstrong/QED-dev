# Ladder graph-half checks

Numerical sanity checks (not proofs) for `QED/TwoLoop/ParamNumEval*.lean` and
`QED/TwoLoop/UnitLGraph.lean`.

- `lean_ladder.py`: a model of `openNum .L` and `openV` in the Lean conventions; `paramNum` by
  finite differences along the eigenvectors of G (independent of the Wick formula).
- `wick_check.py`: the formula of `openNum_L_explicit` against that model.
- `compare_engine.py`: the model integrated over the electron-pair splits against the engine
  integrand of `../two_loop_units.py`.
- `split_check.py`: the second coefficients of T1, T2 do not depend on the splits.
- `target_check.py`: the pointwise targets stated in `UnitLGraph.lean` (not yet proved).

Run each with `nice -n 10 python3 <file>` from any directory (numpy, mpmath).
