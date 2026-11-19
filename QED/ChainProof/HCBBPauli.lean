/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCBBLimit

/-!
# The Pauli projection of the bubble–bubble integrand, pointwise

Helper level, Phase 5 Stage 1a, toward the nested value of the bubble–bubble class
(`QED.ChainProof.HCBB.BBNestedAt`, the `r = 0` component of
`QED.ChainProof.HCValue.ClassNestedAtLink enumClass enumPhoton`). For the one-loop vertex with the
double insertion `bbInsertion` (`QED/ChainProof/HCBBContract.lean`), at every loop momentum `k`
and every prescription `ε`:

* `pauliNum_bbVertex`: the Pauli numerator is
  `(1/i)² d(k)³ D_m(p' + k)⁻¹ D_m(p + k)⁻¹ (A' k² + B') P_g(k)`, with `P_g = pauliChain` the Pauli
  projection of the Feynman-gauge chain: the longitudinal part `A' k_ν k_ρ` of the insertion drops
  out exactly (`QED.TwoLoop.VPUnitNested.pauliNum_longitudinal`).
* `pauliNum_bbVertex_split`: with `A' = -Π̂_ε² k² + 2iεΠ̂_ε S_ε` and `B' = ε² S_ε²`, the Pauli
  numerator is `d³ D⁻¹ D⁻¹ (Π̂_ε(k²)² k⁴ - ε (2i Π̂_ε S_ε k² + ε S_ε²)) P_g(k)`.

This is an identity of integrands; exchanging it with the energy-first integral needs the
integrability of each entry of the vertex integrand.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.HCBB

open QED.WickModel QED.TwoLoop.Insertion QED.TwoLoop.VPUnitNested QED.TwoLoop.PauliZeroLimit
open QED.TwoLoop.Bridge

/-- **The Pauli numerator of the bubble–bubble vertex integrand**: the longitudinal part of the
double insertion drops out. -/
theorem pauliNum_bbVertex (P : Params) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (hm : P.m ≠ 0) (ε : ℝ) (k : Fin 4 → ℝ) :
    pauliNum P.m p' p (fun μ => vertexChain P.e μ (QED.OneLoop.electronPropagator P.m ε (p' + k))
        (QED.OneLoop.electronPropagator P.m ε (p + k)) (bbInsertion P ε k)) =
      (1 / I) ^ 2 * photonScalar P.mγ P.Λ ε k ^ 3 *
        ((propDenom P.m ε (p' + k))⁻¹ * (propDenom P.m ε (p + k))⁻¹) *
        (bbA2 P ε k * (Minkowski.dot k k : ℂ) + bbB P ε k * bbB P ε k) *
        pauliChain P.e P.m p' p k := by
  set X : ℂ := (1 / I) ^ 2 * photonScalar P.mγ P.Λ ε k ^ 3 *
    (bbA2 P ε k * (Minkowski.dot k k : ℂ) + bbB P ε k * bbB P ε k)
  set Y : ℂ := (1 / I) ^ 2 * photonScalar P.mγ P.Λ ε k ^ 3 * bbA2 P ε k
  set c : ℂ := (propDenom P.m ε (p' + k))⁻¹ * (propDenom P.m ε (p + k))⁻¹
  have e4 : bbInsertion P ε k = fun ν ρ => X * gPhoton ν ρ +
      (-Y) * (((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ)) := by
    funext ν ρ
    rw [bbInsertion_eq]
    ring
  have hmat : (fun μ => vertexChain P.e μ (QED.OneLoop.electronPropagator P.m ε (p' + k))
      (QED.OneLoop.electronPropagator P.m ε (p + k)) (bbInsertion P ε k)) =
      fun μ => (c * X) • vertexChain P.e μ (electronNumerator P.m (p' + k))
          (electronNumerator P.m (p + k)) gPhoton +
        (c * (-Y)) • vertexChain P.e μ (electronNumerator P.m (p' + k))
          (electronNumerator P.m (p + k))
          (fun ν ρ => ((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ)) := by
    funext μ
    rw [e4, QED.TwoLoop.CountertermLimit.electronPropagator_eq_smul,
      QED.TwoLoop.CountertermLimit.electronPropagator_eq_smul, vertexChain_smul_out,
      vertexChain_smul_in, vertexChain_add_photon, vertexChain_smul_photon,
      vertexChain_smul_photon]
    simp only [smul_add, smul_smul, c]
    congr 1 <;> congr 1 <;> ring
  rw [hmat, QED.TwoLoop.PauliZeroLimit.pauliNum_add, pauliNum_smul, pauliNum_smul,
    pauliNum_longitudinal P.e hm hp' hp hq k,
    ← pauliChain]
  simp only [X, c]
  ring

/-- **The Pauli numerator with the `ε`-free part separated**:
`d³ D⁻¹ D⁻¹ (Π̂_ε² k⁴ - ε (2i Π̂_ε S_ε k² + ε S_ε²)) P_g(k)`. -/
theorem pauliNum_bbVertex_split (P : Params) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (hm : P.m ≠ 0) (ε : ℝ) (k : Fin 4 → ℝ) :
    pauliNum P.m p' p (fun μ => vertexChain P.e μ (QED.OneLoop.electronPropagator P.m ε (p' + k))
        (QED.OneLoop.electronPropagator P.m ε (p + k)) (bbInsertion P ε k)) =
      photonScalar P.mγ P.Λ ε k ^ 3 *
        ((propDenom P.m ε (p' + k))⁻¹ * (propDenom P.m ε (p + k))⁻¹) *
        (QED.TwoLoop.VPHalfAt.vpLoopEps P ε (Minkowski.dot k k) ^ 2 *
            (Minkowski.dot k k : ℂ) ^ 2 -
          (ε : ℂ) * (2 * I * QED.TwoLoop.VPHalfAt.vpLoopEps P ε (Minkowski.dot k k) *
              QED.TwoLoop.VPHalfAt.vpExtraEps P ε (Minkowski.dot k k) * (Minkowski.dot k k : ℂ) +
            (ε : ℂ) * QED.TwoLoop.VPHalfAt.vpExtraEps P ε (Minkowski.dot k k) ^ 2)) *
        pauliChain P.e P.m p' p k := by
  rw [pauliNum_bbVertex P hp' hp hq hm, bbA2, bbA, bbB]
  have hI : (1 / I) ^ 2 = -1 := by rw [one_div, inv_pow, I_sq]; norm_num
  rw [hI]
  ring_nf
  rw [I_sq]
  ring

end QED.ChainProof.HCBB

end
