/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCBBWick
public import QED.TwoLoop.VPHalfAtAssemblyProj
public import QED.Integration.EnergyFirstShift

/-!
# The bubble–bubble representative as a one-loop vertex with a double insertion

Helper level, Phase 5 Stage 1a, obligation O3-6 for `QED.ChainProof.Enum.repBB`, continuing
`QED/ChainProof/HCBBWick.lean`. At fixed `ε > 0`, with both bubbles integrated in closed form,

`Π_ε^{ab}(k) = T^{ab}(k) = A (k² g^{ab} - k^a k^b) + B g^{ab}`,
`A = i Π̂_ε(k²)`, `B = ε S_ε(k²)` (`QED.TwoLoop.VPHalfAtAssembly.vpT`,
`QED.TwoLoop.VPHalfAt.energyFirstIntegral_vacuumPolarizationIntegrand_eq`),

the outer factor `chainOuter` contracts the two bubbles into a one-loop vertex chain with the double
insertion `bbInsertion = (1/i)² Δ̃ T Δ̃ T Δ̃`, exactly as the `δ₃`–`δ₃` class has
`ddInsertion = (1/i)² Δ̃ V Δ̃ V Δ̃` (`QED.ChainProof.HCLimit.contractionValue₂_repDD`), with the
photon counterterm factor `V` replaced by the closed-form bubble `T`.

* `sum_vpT_metric_vpT`: `T g T = T'` with `A' = A² k² + 2AB`, `B' = B²` (the transverse projector
  identity `P g P = k² P`).
* `bbInsertion_eq`: `bbInsertion = (1/i)² d(k)³ ((A' k² + B') g_{νρ} - A' k_ν k_ρ)`, `d` the scalar
  part of the photon propagator.
* `sum_chainOuter_vpT`: `∑_{a b} chainOuter(k)_{a b} T_a T_b` is the vertex chain of the open line
  with the insertion `(1/i)² Δ̃ T Δ̃ T Δ̃`.
* **`contractionValue₂_repBB_eq_vertex`**: at fixed `ε > 0`, under the mass and Pauli–Villars
  conditions and the conditional three-loop integrability `hF`, the value (F₇) at T1's flavours of
  `repBB` is `∫_D dk vertexChain e μ S̃(p' + k) S̃(p + k) bbInsertion(k)`.

With `A' = -Π̂_ε² k² + 2iεΠ̂_ε S_ε` and `B' = ε² S_ε²`, the `ε → 0⁺` limit of this one-loop integral
is the remaining analytic step (`RepLimit repBB`); its integrand has the photon factor
`d(k)³ Π̂_ε(k²)² k² (k² g - k k)` plus terms carrying explicit factors `ε`, `ε²`.
-/

@[expose] public section

namespace QED.ChainProof.HCBB

open QED.WickModel QED.ChainProof.Enum QED.ChainProof.HCLimit QED.TwoLoop.Insertion
open QED.TwoLoop.VPHalfAtAssembly QED.TwoLoop.VPUnitNested Complex

/-! ### The transverse projector -/

/-- **`T g T`** for the inserted vacuum polarization `T = A (k² g - k k) + B g`: it is again of
this form, with `A' = A² k² + 2AB` and `B' = B²`. -/
theorem sum_vpT_metric_vpT (A B : ℂ) (k : Fin 4 → ℝ) (ρ σ : Fin 4) :
    ∑ x, ∑ y, vpT A B k ρ x * (Minkowski.metric x y : ℂ) * vpT A B k y σ =
      vpT (A * A * (Minkowski.dot k k : ℂ) + 2 * A * B) (B * B) k ρ σ := by
  simp only [vpT, Fin.sum_univ_four, Minkowski.metric, Minkowski.dot]
  fin_cases ρ <;> fin_cases σ <;> simp <;> ring

/-- The transverse coefficient `A = i Π̂_ε(k²)` of the closed-form bubble. -/
noncomputable def bbA (P : Params) (ε : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  I * QED.TwoLoop.VPHalfAt.vpLoopEps P ε (Minkowski.dot k k)

/-- The metric coefficient `B = ε S_ε(k²)` of the closed-form bubble. -/
noncomputable def bbB (P : Params) (ε : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  (ε : ℂ) * QED.TwoLoop.VPHalfAt.vpExtraEps P ε (Minkowski.dot k k)

/-- The transverse coefficient `A' = A² k² + 2AB` of `T g T`. -/
noncomputable def bbA2 (P : Params) (ε : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  bbA P ε k * bbA P ε k * (Minkowski.dot k k : ℂ) + 2 * bbA P ε k * bbB P ε k

/-- The closed-form bubble at the prescription `ε`: `T = i Π̂_ε(k²)(k² g - k k) + ε S_ε(k²) g`. -/
noncomputable def bbT (P : Params) (ε : ℝ) (k : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℂ :=
  vpT (bbA P ε k) (bbB P ε k) k

/-- **The double insertion of the bubble–bubble class**:
`(1/i)² ∑ Δ̃_{νx} T^{xy} Δ̃_{yz} T^{zw} Δ̃_{wρ}`, with `T = bbT` the closed-form bubble. -/
noncomputable def bbInsertion (P : Params) (ε : ℝ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) : ℂ :=
  (1 / I) ^ 2 * ∑ x, ∑ y, ∑ z, ∑ w, QED.OneLoop.photonPropagator P.mγ P.Λ ε k ν x *
    bbT P ε k x y * QED.OneLoop.photonPropagator P.mγ P.Λ ε k y z *
    bbT P ε k z w * QED.OneLoop.photonPropagator P.mγ P.Λ ε k w ρ

/-- **The double insertion in closed form**:
`bbInsertion = (1/i)² d(k)³ ((A' k² + B') g_{νρ} - A' k_ν k_ρ)`, `A' = A² k² + 2AB`, `B' = B²`. -/
theorem bbInsertion_eq (P : Params) (ε : ℝ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) :
    bbInsertion P ε k ν ρ =
      (1 / I) ^ 2 * (photonScalar P.mγ P.Λ ε k ^ 3 *
        ((bbA2 P ε k * (Minkowski.dot k k : ℂ) + bbB P ε k * bbB P ε k) * gPhoton ν ρ -
          bbA2 P ε k * ((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ))) := by
  set A := bbA P ε k
  set B := bbB P ε k
  set d := photonScalar P.mγ P.Λ ε k
  have hinner : ∀ x w, ∑ y, ∑ z, bbT P ε k x y *
      QED.OneLoop.photonPropagator P.mγ P.Λ ε k y z * bbT P ε k z w =
      d * vpT (A * A * (Minkowski.dot k k : ℂ) + 2 * A * B) (B * B) k x w := by
    intro x w
    rw [← sum_vpT_metric_vpT, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [bbT, photonPropagator_eq_metric_mul, d]
    ring
  have hsand := sandwich_vpT P.mγ P.Λ ε (A * A * (Minkowski.dot k k : ℂ) + 2 * A * B) (B * B) k
    ν ρ
  unfold bbInsertion
  congr 1
  have e : ∑ x, ∑ y, ∑ z, ∑ w, QED.OneLoop.photonPropagator P.mγ P.Λ ε k ν x *
      bbT P ε k x y * QED.OneLoop.photonPropagator P.mγ P.Λ ε k y z *
      bbT P ε k z w * QED.OneLoop.photonPropagator P.mγ P.Λ ε k w ρ =
      d * ∑ x, ∑ w, QED.OneLoop.photonPropagator P.mγ P.Λ ε k ν x *
        vpT (A * A * (Minkowski.dot k k : ℂ) + 2 * A * B) (B * B) k x w *
        QED.OneLoop.photonPropagator P.mγ P.Λ ε (-k) ρ w := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    conv_lhs => enter [2, y]; rw [Finset.sum_comm]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [photonPropagator_neg', photonPropagator_comm' _ _ _ k ρ w,
      show ∀ a b c : ℂ, d * (a * b * c) = a * (d * b) * c from fun a b c => by ring,
      ← hinner x w]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  rw [e, hsand, bbA2]
  ring

/-! ### The contraction with the outer factor -/

/-- **The outer factor contracted with the two closed-form bubbles** is the one-loop vertex chain
of the open line with the double insertion `bbInsertion`. -/
theorem sum_chainOuter_bbT (P : Params) (p kext k : Fin 4 → ℝ) (α β μ : Fin 4) :
    ∑ a : Fin 4 × Fin 4, ∑ b : Fin 4 × Fin 4, chainOuter P p kext k α β μ a b *
        bbT P P.ε k a.1 a.2 * bbT P P.ε k b.1 b.2 =
      vertexChain P.e μ (QED.OneLoop.electronPropagator P.m P.ε (p + kext - k))
        (QED.OneLoop.electronPropagator P.m P.ε (p - k)) (bbInsertion P P.ε k) α β := by
  unfold chainOuter bbInsertion vertexChain QED.TwoLoop.NestedVP.outerChain
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Fintype.sum_prod_type,
    photonPropagator_neg', Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [sum_comm_out_four]
  conv_lhs => enter [2, l0]; rw [sum_comm_out_four]
  refine Finset.sum_congr rfl fun l0 _ => Finset.sum_congr rfl fun l2 _ =>
    Finset.sum_congr rfl fun a1 _ => Finset.sum_congr rfl fun a2 _ =>
    Finset.sum_congr rfl fun b1 _ => Finset.sum_congr rfl fun b2 _ => ?_
  rw [photonPropagator_comm' _ _ _ k b2 l2]
  ring

theorem bbT_neg (P : Params) (ε : ℝ) (k : Fin 4 → ℝ) (ρ σ : Fin 4) :
    bbT P ε (-k) ρ σ = bbT P ε k ρ σ := by
  simp only [bbT, bbA, bbB, QED.TwoLoop.CountertermMirror.dot_neg_neg, vpT_neg]

theorem bbInsertion_neg (P : Params) (ε : ℝ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) :
    bbInsertion P ε (-k) ν ρ = bbInsertion P ε k ν ρ := by
  simp only [bbInsertion, bbT_neg, photonPropagator_neg']

/-- `Π_ε(k)` is the closed-form bubble `bbT`. -/
theorem piEps_eq_bbT {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hε : 0 < P.ε) (k : Fin 4 → ℝ) (a : Fin 4 × Fin 4) : piEps P k a = bbT P P.ε k a.1 a.2 :=
  piEps_eq hm hM₁ hM₂ hPV₁ hPV₂ hε k a

/-- **The value of the bubble–bubble representative as a one-loop vertex with a double
insertion**, at fixed `ε > 0`: under the mass and Pauli–Villars conditions and the conditional
three-loop integrability `hF`, the value (F₇) at T1's flavours is the energy-first integral of the
one-loop vertex chain with the insertion `bbInsertion = (1/i)² Δ̃ T Δ̃ T Δ̃`. -/
theorem contractionValue₂_repBB_eq_vertex {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hε : 0 < P.ε)
    (p' p : Fin 4 → ℝ) (α β μ : Fin 4)
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable 3
      (bbIntegrand P fun k => chainOuter P p (p' - p) k α β μ)) :
    QED.Lepton.contractionValue₂ P (QED.ChainProof.chainFlavors P) repBB (fun _ => p')
        (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) =
      QED.OneLoop.energyFirstIntegral fun k =>
        vertexChain P.e μ (QED.OneLoop.electronPropagator P.m P.ε (p' + k))
          (QED.OneLoop.electronPropagator P.m P.ε (p + k)) (bbInsertion P P.ε k) α β := by
  rw [contractionValue₂_repBB_eq_outer hm hM₁ hM₂ hPV₁ hPV₂ hε p' p α β μ hF]
  simp only [piEps_eq_bbT hm hM₁ hM₂ hPV₁ hPV₂ hε, sum_chainOuter_bbT]
  rw [← QED.OneLoop.energyFirstIntegral_neg_eq_self (fun k =>
    vertexChain P.e μ (QED.OneLoop.electronPropagator P.m P.ε (p' + k))
      (QED.OneLoop.electronPropagator P.m P.ε (p + k)) (bbInsertion P P.ε k) α β)]
  refine congrArg _ (funext fun k => ?_)
  have e1 : p + (p' - p) - k = p' + -k := by abel
  have e2 : p - k = p + -k := by abel
  have e3 : bbInsertion P P.ε k = bbInsertion P P.ε (-k) :=
    funext fun ν => funext fun ρ => (bbInsertion_neg P P.ε k ν ρ).symm
  rw [e1, e2, e3]

end QED.ChainProof.HCBB

end
