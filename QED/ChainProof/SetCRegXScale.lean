/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitMPauli
public import QED.TwoLoop.MassScalingOpen

/-!
# Mass scaling of the extended Pauli numerator

The quartic dilation of `QED/TwoLoop/MassScalingBasic.lean` applies with the
extra photon rows present. The second Symanzik function has degree two and
the projected Pauli numerator has degree thirteen.
-/

public section

namespace QED.ChainProof.SetCUnitM

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge
open QED.TwoLoop.ClassIntegrable QED.TwoLoop.PauliZero
open QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.MassScaling

variable {r : ℕ}

private theorem unitMMomenta_smul (c : Class5) (s : Fin 8) (κ : Fin r → ℝ)
    (p p' : Fin 4 → ℝ) (t : ℝ) :
    unitMMomenta c s κ (t • p) (t • p') = t • unitMMomenta c s κ p p' := by
  unfold unitMMomenta
  rw [pvMomentaE_smul]
  funext i
  simp only [Pi.smul_apply]
  exact smul_comm _ _ _

/-- At zero momentum transfer, the extended second Symanzik function scales
quadratically in the common mass dilation. -/
theorem unitMV0_massScale (c : Class5) (P : Params) (s : Fin 8)
    (κ : Fin r → ℝ) (M : Fin (r + 8) → ℝ) (x : Fin (r + 7) → ℝ) (t : ℝ) :
    unitMV0 c (massScale t P) s κ (t • M) x = t ^ 2 * unitMV0 c P s κ M x := by
  simp only [unitMV0, massScale_m, restMomentum_smul, unitMMomenta_smul, symanzikV_smul]

/-- The extended projected numerator has the same mass homogeneity as the
eight-line numerator. -/
theorem unitMPauliNum_massScale {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (s : Fin 8) (κ : Fin r → ℝ) (M : Fin (r + 8) → ℝ) (x : Fin (r + 7) → ℝ)
    (u : ℝ) {t : ℝ} (ht : t ≠ 0) :
    unitMPauliNum c (massScale t P) s κ (t • M) x u =
      (t : ℂ) ^ 13 * unitMPauliNum c P s κ M x u := by
  simp only [unitMPauliNum, massScale_m, curveMomentum_smul, restMomentum_smul, pauliWt_smul,
    unitMMomenta_smul, openF_massScale hc ht]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [paramNumOf_smul (exists_quartic_openF hc P _ j) _ ht]
  ring

end QED.ChainProof.SetCUnitM

end
