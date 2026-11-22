/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetALinkIntVTerm
public import QED.ChainProof.SetCLinkReps

/-!
# Set (c), family `B`: line classes and minimal exponent vectors

Helper for the Phase 5 Stage 3 goal (HS₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setC`
(decision D-58). The data of the class obligations of `QED.ChainProof.SetCLink.repB i`
(the two-loop vertex with a bubble on a photon line, three loops, seven `gauge` vertices),
for `QED.ChainProof.SetALinkV.jef_nsClosed3`: the rows of the five line classes up to sign
(`rowsB i`), the class of a line (`clsB i`), and the minimal exponent vectors of the expansion
terms (`esB i`, five per orbit). The closed loop is the bubble (two lines); the merged
exponents are those of the budget of `QED/ChainProof/SetALinkIntVTerm.lean` (photon `4`, open
electron `1`, loop line `2 n - d`).
-/

@[expose] public section

namespace QED.ChainProof.SetCLink

open QED.WickModel QED.GradedProof.X0 QED.ChainProof.SetALinkV

/-- The rows of the line classes of `repB i`. -/
def rowsB : Fin 12 → Fin 5 → Fin 3 → ℤ :=
  ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 0, 1], ![-1, 1, 0]],
    ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![-1, 1, 1], ![-1, 1, 0]],
    ![![1, 0, 0], ![0, 1, 0], ![-1, 1, 0], ![0, 0, 1], ![1, 0, 1]],
    ![![1, 0, 0], ![0, 1, 0], ![-1, 1, 0], ![0, 0, 1], ![-1, 1, 1]],
    ![![1, 0, 0], ![0, 1, 0], ![-1, 1, 0], ![0, 0, 1], ![1, 0, 1]],
    ![![1, 0, 0], ![0, 1, 0], ![-1, 1, 0], ![0, 0, 1], ![-1, 1, 1]],
    ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 0, 1], ![-1, 1, 0]],
    ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![-1, 1, 1], ![-1, 1, 0]],
    ![![1, 0, 0], ![0, 1, 0], ![-1, 1, 0], ![0, 0, 1], ![1, 0, 1]],
    ![![1, 0, 0], ![0, 1, 0], ![-1, 1, 0], ![0, 0, 1], ![-1, 1, 1]],
    ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 0, 1], ![-1, 1, 0]],
    ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![-1, 1, 1], ![-1, 1, 0]]]

/-- The class of a line of `repB i`. -/
def clsB (i : Fin 12) (l : Line (repB i)) : Fin 5 := clsOf (rowsB i) (row3 (repB i) l)

/-- The minimal exponent vectors of `repB i`. -/
def esB : Fin 12 → List (Fin 5 → ℕ) :=
  ![[![10, 2, 1, 5, 4],
      ![10, 2, 2, 4, 4],
      ![10, 2, 3, 3, 4],
      ![10, 2, 4, 2, 4],
      ![10, 2, 5, 1, 4]],
    [![6, 2, 1, 5, 8],
      ![6, 2, 2, 4, 8],
      ![6, 2, 3, 3, 8],
      ![6, 2, 4, 2, 8],
      ![6, 2, 5, 1, 8]],
    [![9, 2, 5, 1, 5],
      ![9, 2, 5, 2, 4],
      ![9, 2, 5, 3, 3],
      ![9, 2, 5, 4, 2],
      ![9, 2, 5, 5, 1]],
    [![5, 2, 9, 1, 5],
      ![5, 2, 9, 2, 4],
      ![5, 2, 9, 3, 3],
      ![5, 2, 9, 4, 2],
      ![5, 2, 9, 5, 1]],
    [![10, 1, 5, 1, 5],
      ![10, 1, 5, 2, 4],
      ![10, 1, 5, 3, 3],
      ![10, 1, 5, 4, 2],
      ![10, 1, 5, 5, 1]],
    [![6, 1, 9, 1, 5],
      ![6, 1, 9, 2, 4],
      ![6, 1, 9, 3, 3],
      ![6, 1, 9, 4, 2],
      ![6, 1, 9, 5, 1]],
    [![11, 1, 1, 5, 4],
      ![11, 1, 2, 4, 4],
      ![11, 1, 3, 3, 4],
      ![11, 1, 4, 2, 4],
      ![11, 1, 5, 1, 4]],
    [![7, 1, 1, 5, 8],
      ![7, 1, 2, 4, 8],
      ![7, 1, 3, 3, 8],
      ![7, 1, 4, 2, 8],
      ![7, 1, 5, 1, 8]],
    [![9, 1, 6, 1, 5],
      ![9, 1, 6, 2, 4],
      ![9, 1, 6, 3, 3],
      ![9, 1, 6, 4, 2],
      ![9, 1, 6, 5, 1]],
    [![5, 1, 10, 1, 5],
      ![5, 1, 10, 2, 4],
      ![5, 1, 10, 3, 3],
      ![5, 1, 10, 4, 2],
      ![5, 1, 10, 5, 1]],
    [![11, 1, 1, 5, 4],
      ![11, 1, 2, 4, 4],
      ![11, 1, 3, 3, 4],
      ![11, 1, 4, 2, 4],
      ![11, 1, 5, 1, 4]],
    [![7, 1, 1, 5, 8],
      ![7, 1, 2, 4, 8],
      ![7, 1, 3, 3, 8],
      ![7, 1, 4, 2, 8],
      ![7, 1, 5, 1, 8]]]

end QED.ChainProof.SetCLink

end
