/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.PacketCurrentDensity
public import QED.Frozen.OneLoop.PacketNormSq
import Mathlib.Tactic.Ring

/-!
# The amplitude of the wave-packet current density

The frozen current density `QED.OneLoop.packetCurrentDensity` (packet 4b, (W₁)) is the
two-momentum Fourier integral `∫ d³k ∫ d³k' F(k, k') e^{i(k - k')·x}` of the packet amplitude
`F(k, k') = w(k') w(k) M(k', k)`, where

* `w(k) = φ(|k|²/λ²) / ((2π)³ 2ω)` is the packet weight (`packetWeight`), and
* `M(k', k) = ū₊(k') V²(k', k) u₊(k)` is the one-electron matrix element of `J²` between
  plane-wave states (`packetMatrixElement`).

This module names these pieces and proves the rewriting `packetCurrentDensity_eq`.

## Main statements

* `QED.OneLoop.packetCurrentDensity_eq`: the current density as a Fourier integral of
  `packetAmplitude`.
* `QED.OneLoop.packetNormSq_eq`: the squared norm as an integral of `packetWeight`.
-/

@[expose] public section

open Matrix Complex MeasureTheory

namespace QED.OneLoop

/-- The one-electron matrix element `M(k', k) = ū₊(k') V²(k', k) u₊(k)` of the current
component `J²` between plane-wave states of spatial momenta `k⃗'` and `k⃗`. -/
noncomputable def packetMatrixElement (e Z₁ m mγ Λ : ℝ) (hm : 0 < m) (hmγ : 0 < mγ)
    (hΛ : 0 < Λ) (k' k : Fin 3 → ℝ) : ℂ :=
  Dirac.bar (Dirac.spinor m (oneParticleMomentum m k') 0) ⬝ᵥ
    (vertexFunction e Z₁ m mγ Λ hm hmγ hΛ (oneParticleMomentum m k') (oneParticleMomentum m k)
      (dot_oneParticleMomentum m k') (dot_oneParticleMomentum m k)
      (oneParticleMomentum_pos hm k') (oneParticleMomentum_pos hm k) 2
      *ᵥ Dirac.spinor m (oneParticleMomentum m k) 0)

/-- The packet weight `w(k) = φ(|k⃗|²/λ²) / ((2π)³ 2ω)`. -/
noncomputable def packetWeight (m : ℝ) (φ : ℝ → ℝ) (lam : ℝ) (k : Fin 3 → ℝ) : ℝ :=
  φ ((∑ j, k j ^ 2) / lam ^ 2) / ((2 * Real.pi) ^ 3 * (2 * oneParticleMomentum m k 0))

/-- The packet amplitude `F(k, k') = w(k') w(k) M(k', k)`; the ket momentum `k` comes first. -/
noncomputable def packetAmplitude (e Z₁ m mγ Λ : ℝ) (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (φ : ℝ → ℝ) (lam : ℝ) (k k' : Fin 3 → ℝ) : ℂ :=
  ((packetWeight m φ lam k' * packetWeight m φ lam k : ℝ) : ℂ)
    * packetMatrixElement e Z₁ m mγ Λ hm hmγ hΛ k' k

/-- The current density (W₁) is the two-momentum Fourier integral of the packet amplitude. -/
theorem packetCurrentDensity_eq (e Z₁ m mγ Λ : ℝ) (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (φ : ℝ → ℝ) (lam : ℝ) (x : Fin 3 → ℝ) :
    packetCurrentDensity e Z₁ m mγ Λ hm hmγ hΛ φ lam x =
      ∫ k : Fin 3 → ℝ, ∫ k' : Fin 3 → ℝ,
        packetAmplitude e Z₁ m mγ Λ hm hmγ hΛ φ lam k k'
          * Complex.exp (I * ((∑ j, (k j - k' j) * x j : ℝ) : ℂ)) := by
  unfold packetCurrentDensity packetAmplitude packetMatrixElement packetWeight
  congr 1; ext k; congr 1; ext k'
  rw [mul_right_comm]
  congr 2
  push_cast
  ring

/-- The squared norm (W₂) is `∫ w(k)² (2π)³ 2ω d³k`. -/
theorem packetNormSq_eq (m : ℝ) (φ : ℝ → ℝ) (lam : ℝ) :
    packetNormSq m φ lam = ∫ k : Fin 3 → ℝ,
      packetWeight m φ lam k ^ 2 * ((2 * Real.pi) ^ 3 * (2 * oneParticleMomentum m k 0)) := by
  unfold packetNormSq packetWeight
  congr 1; ext k
  by_cases h : (2 * Real.pi) ^ 3 * (2 * oneParticleMomentum m k 0) = 0
  · simp [h]
  · field_simp

end QED.OneLoop

end
