# Fixed-epsilon one-loop vacuum polarization checks

Numerical sanity checks (not proofs) behind the VP-half analysis in
`QED/TwoLoop/VPHalf*.lean`. They evaluate the energy-first one-loop vacuum polarization at fixed
epsilon (energy integral by residues, spatial integral by mpmath, flavour-summed with m = 1,
M1 = 2, M2 = 3) and find

  Pi_eps^{st}(k) = (k^2 g - k k) PiHat(k^2; M_f^2 - i eps) + eps g^{st} S_eps(k),

with the transverse part given by the complex-mass function and an extra non-transverse term
proportional to eps (`fixed_eps_vp.py` at k = 0, `fixed_eps_vp_k.py` at timelike k,
`compare_cov.py`). Run each with `nice -n 10 python3 <file>`.

`n1_complex_spectral.py`: the spectral identity with complex mass M^2 - i eps (line-dependent
prescription eps_v = 4 eps/(1 - v^2)). `n2_fixed_q_rhs.py`: the spectral and outer forms of the
right side of `VPHalfSubAt` agree.
