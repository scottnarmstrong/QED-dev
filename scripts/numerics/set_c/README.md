# Set (c) value: generator and check scripts

These sympy/mpmath scripts produced the generated Lean files in `QED/Chain/`:
- `SetCKernel.lean` (`gen_kernel.py`);
- `SetCW1.lean` (`gen_w1.py`);
- `SetCW1Lim.lean` and `SetCJInt.lean` (`gen_lim.py G` and `gen_lim.py J`, with `expand.py`).

The Lean header and footer templates the generators read (`*head*.lean`, `*tail*.lean`) are stored
here with a `.lean.txt` suffix, so they are not mistaken for Lean modules. Rename them back before
regenerating. `noring.txt` lists the equations where `field_simp` alone closes the goal.

`setc_num.py` checks the integral representation against Barbieri–Remiddi 1974, eq. (3); run it as
`python3 setc_num.py 50` for 50 digits. `muon_chk.py` checks the same kernel against their eq. (4).
The other scripts check the reduction, the antiderivatives and the endpoint values. The `.pkl` files
hold their intermediate data. Run everything from this directory.

The Lean proofs do not depend on these scripts; they only regenerate the generated files.
