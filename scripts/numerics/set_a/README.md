# Set (a) value: generator and check scripts

These sympy/mpmath scripts produced the generated Lean files `QED/Chain/SetAW1.lean`
(`gen1.py` → `gen1lean.py` → `gen1file.py`, with `gen1main.py`) and `QED/Chain/SetAW1Lim.lean`
(`genlim.py`, with `wraplib.py`). The other scripts check the antiderivatives, endpoint values and
weight-3/weight-4 constants numerically (`chk*.py`, `g*.py`, `numG.py`, `sym.py`). The `.pkl` files
are their intermediate data (`red2.pkl` holds the reduction coefficients). The scripts read and write
files in the working directory, so run them from this directory. `gen1file.py` writes
`QED/Chain/SetAW1.lean` directly. The Lean proofs do not depend on these scripts; they only
regenerate the two generated files.
