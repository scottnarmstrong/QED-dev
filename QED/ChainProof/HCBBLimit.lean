/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCBBContract
public import QED.ChainProof.HCLimitDDLimit
public import QED.ChainProof.IntegrableChainReduction

/-!
# The `ε → 0⁺` limit of the bubble–bubble class, reduced to a one-loop statement

Helper level, Phase 5 Stage 1a, obligation O3-6 for `QED.ChainProof.Enum.repBB`
(`QED.ChainProof.HCLimit.RepLimit repBB`), continuing `QED/ChainProof/HCBBContract.lean`.

* `bbInsertion_split`: the double insertion is
  `d(k)³ (Π̂_ε(k²)² k² (k² g - k k) - ε (2i Π̂_ε S_ε (k² g - k k) + ε S_ε² g))` (lower indices):
  an `ε`-free form in `Π̂_ε` plus a term with an explicit factor `ε`.
* `BBInsertionLimit` (**the remaining analytic statement**, one loop): at admissible parameters,
  every on-shell positive-energy pair with `q² > 0` and all indices, the energy-first integral of
  the one-loop vertex chain with the insertion `bbInsertion` at prescription `ε` converges as
  `ε → 0⁺`.
* **`repLimit_repBB_of`**: `RepLimit repBB` from the three-loop integrability
  `QED.ChainProof.HCBB.BBJointIntegrable` (the transport of (HC₀) for `repBB`) and
  `BBInsertionLimit`.
* `classLimitLink_enum_of_bb`: `ClassLimitLink enumClass` from these two and the bubble–`δ₃` and
  `δ₃`–bubble limits (the `δ₃`–`δ₃` limits are proved, `QED.ChainProof.HCLimit.repLimit_repDD`).
* `isClassLimit_zero_iff`: given `BBJointIntegrable`, the class limits of the bubble–bubble class
  (`r = 0` of `enumClass`) are exactly the limits `BBLim` of `(1/i)` times the one-loop vertex with
  the double insertion.
* `BBNestedAt`, `classNestedAt_zero_of`: the `r = 0` component of
  `ClassNestedAtLink enumClass enumPhoton` from `BBJointIntegrable` and the one-loop statement
  `BBNestedAt` (the Pauli projection of `BBLim` at the canonical pair is
  `e² outerAt m Q (Π_loop² s² D³)`).
* `BBCov`, `classCov_zero_of`: the `r = 0` component of `ClassCovLink enumClass` from
  `BBJointIntegrable` and the one-loop covariance statement `BBCov` for `BBLim`.
* `jointEnergyFirstIntegrable_bb_of_chainValue`, `bbJointIntegrable_of_chainValue`: the
  integrability hypothesis from (T₉′) for `repBB` in the frozen routing
  (`QED.ChainProof.ChainValueIntegrable`, the per-representative form of (HC₀)), through the
  inverse unimodular change of loop momenta `bbMatInv`.

`BBInsertionLimit`, `BBNestedAt` and `BBCov` are one-loop statements about the explicit integrand
`vertexChain e μ S̃(p' + k) S̃(p + k) bbInsertion(k)` and are not proved here.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.ChainProof.HCBB

open QED.WickModel QED.ChainProof.Enum QED.ChainProof.HCLimit QED.TwoLoop.Insertion
open QED.TwoLoop.VPHalfAtAssembly QED.TwoLoop.VPUnitNested QED.ChainProof.HCValue

/-- **The double insertion with its `ε`-free part separated**:
`bbInsertion = d³ (Π̂_ε² k² (k² g - k k) - ε (2i Π̂_ε S_ε (k² g - k k) + ε S_ε² g))`, with lower
indices on `k` and `d` the scalar part of the photon propagator. -/
theorem bbInsertion_split (P : Params) (ε : ℝ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) :
    bbInsertion P ε k ν ρ =
      photonScalar P.mγ P.Λ ε k ^ 3 *
        (QED.TwoLoop.VPHalfAt.vpLoopEps P ε (Minkowski.dot k k) ^ 2 * (Minkowski.dot k k : ℂ) *
            ((Minkowski.dot k k : ℂ) * gPhoton ν ρ -
              ((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ)) -
          (ε : ℂ) * (2 * I * QED.TwoLoop.VPHalfAt.vpLoopEps P ε (Minkowski.dot k k) *
              QED.TwoLoop.VPHalfAt.vpExtraEps P ε (Minkowski.dot k k) *
              ((Minkowski.dot k k : ℂ) * gPhoton ν ρ -
                ((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ)) +
            (ε : ℂ) * QED.TwoLoop.VPHalfAt.vpExtraEps P ε (Minkowski.dot k k) ^ 2 *
              gPhoton ν ρ)) := by
  rw [bbInsertion_eq, bbA2, bbA, bbB]
  have hI : (1 / I) ^ 2 = -1 := by rw [one_div, inv_pow, I_sq]; norm_num
  rw [hI]
  ring_nf
  rw [I_sq]
  ring

/-- **The `ε → 0⁺` limit of the one-loop vertex with the double insertion** (the remaining
analytic statement for the bubble–bubble class; not proved here): at admissible parameters, every
on-shell positive-energy pair with `q² > 0` and all indices, the energy-first integral of the
vertex chain with the insertion `bbInsertion` at prescription `ε` has a limit as `ε → 0⁺`. -/
def BBInsertionLimit : Prop :=
  ∀ P : Params, QED.ChainProof.ChainAdmissible P → ∀ p' p : Fin 4 → ℝ,
    QED.ChainProof.IsPairQ P.m p' p → ∀ α β μ : Fin 4, ∃ L : ℂ,
      Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun k =>
        vertexChain P.e μ (QED.OneLoop.electronPropagator P.m ε (p' + k))
          (QED.OneLoop.electronPropagator P.m ε (p + k)) (bbInsertion P ε k) α β)
        (𝓝[>] 0) (𝓝 L)

/-- The value of `repBB` at prescription `ε` as the one-loop vertex with the double insertion, at
admissible parameters. -/
theorem contractionValue₂_repBB_eps (hF : BBJointIntegrable) {P : Params}
    (hA : QED.ChainProof.ChainAdmissible P) {p' p : Fin 4 → ℝ}
    (hpq : QED.ChainProof.IsPairQ P.m p' p) (α β μ : Fin 4) {ε : ℝ} (hε : 0 < ε) :
    QED.Lepton.contractionValue₂ { P with ε := ε } (QED.ChainProof.chainFlavors P) repBB
        (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) =
      QED.OneLoop.energyFirstIntegral fun k =>
        vertexChain P.e μ (QED.OneLoop.electronPropagator P.m ε (p' + k))
          (QED.OneLoop.electronPropagator P.m ε (p + k)) (bbInsertion P ε k) α β :=
  contractionValue₂_repBB_eq_vertex (P := { P with ε := ε }) hA.hm hA.hM₁ hA.hM₂ hA.hPV₁
    hA.hPV₂ hε p' p α β μ (hF P hA ε hε p' p hpq α β μ)

/-- **`RepLimit repBB` from the three-loop integrability and the one-loop insertion limit.** -/
theorem repLimit_repBB_of (hF : BBJointIntegrable) (hL : BBInsertionLimit) : RepLimit repBB := by
  intro P hA p' p hpq α β μ
  obtain ⟨L, hLim⟩ := hL P hA p' p hpq α β μ
  refine ⟨L, hLim.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (contractionValue₂_repBB_eps hF hA hpq α β μ hε).symm

/-- **`ClassLimitLink enumClass` from the bubble–bubble reduction** and the bubble–`δ₃` and
`δ₃`–bubble limits. -/
theorem classLimitLink_enum_of_bb (hF : BBJointIntegrable) (hL : BBInsertionLimit)
    (hBD : ∀ s, RepLimit (repBD s)) (hDB : ∀ s, RepLimit (repDB s)) :
    QED.ChainProof.ClassLimitLink enumClass :=
  classLimitLink_enum_of_reps' (repLimit_repBB_of hF hL) hBD hDB

/-! ### The class limits, the nested value and covariance -/

/-- `Y` is the `ε → 0⁺` limit of `(1/i)` times the one-loop vertex with the double insertion, at the
pair `(p', p)`, entrywise. -/
def BBLim (P : Params) (p' p : Fin 4 → ℝ) (Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ μ i j, Tendsto (fun ε => (1 / I) * QED.OneLoop.energyFirstIntegral fun k =>
    vertexChain P.e μ (QED.OneLoop.electronPropagator P.m ε (p' + k))
      (QED.OneLoop.electronPropagator P.m ε (p + k)) (bbInsertion P ε k) i j)
    (𝓝[>] 0) (𝓝 (Y μ i j))

/-- **The bubble–bubble class limits are the limits of the one-loop vertex with the double
insertion**, given the three-loop integrability. -/
theorem isClassLimit_zero_iff (hF : BBJointIntegrable) {P : Params}
    (hA : QED.ChainProof.ChainAdmissible P) {p' p : Fin 4 → ℝ}
    (hpq : QED.ChainProof.IsPairQ P.m p' p) (Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    QED.ChainProof.IsClassLimit enumClass 0 P p' p Y ↔ BBLim P p' p Y := by
  have hev : ∀ μ i j, (fun ε => enumClass 0 { P with ε := ε } p' p μ i j) =ᶠ[𝓝[>] 0]
      fun ε => (1 / I) * QED.OneLoop.energyFirstIntegral fun k =>
        vertexChain P.e μ (QED.OneLoop.electronPropagator P.m ε (p' + k))
          (QED.OneLoop.electronPropagator P.m ε (p + k)) (bbInsertion P ε k) i j := by
    intro μ i j
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    change (1 / I) * QED.Lepton.contractionValue₂ { P with ε := ε }
      (QED.ChainProof.chainFlavors P) repBB (fun _ => p') (fun _ => p) (fun _ => p' - p)
      (fun _ => i) (fun _ => j) (fun _ => μ) = _
    rw [contractionValue₂_repBB_eps hF hA hpq i j μ hε]
  exact ⟨fun h μ i j => (h μ i j).congr' (hev μ i j),
    fun h μ i j => (h μ i j).congr' (hev μ i j).symm⟩

/-- **The nested value of the bubble–bubble class at fixed `q² = Q`** (one loop; not proved here):
at admissible parameters, for all small `Q > 0`, every limit of `(1/i)` times the vertex with the
double insertion at the canonical pair has Pauli projection `e² outerAt m Q (Π_loop² s² D³)`
(the photon function `enumPhoton 0 P` of the class). -/
def BBNestedAt : Prop :=
  ∀ P : Params, QED.ChainProof.ChainAdmissible P → ∀ᶠ Q in 𝓝[>] (0 : ℝ), ∀ Y,
    BBLim P (QED.TwoLoop.PauliZero.boostMomentum P.m Q) (QED.TwoLoop.PauliZero.restMomentum P.m)
      Y →
      QED.OneLoop.formFactorProj₂ P.e P.m (QED.TwoLoop.PauliZero.boostMomentum P.m Q)
          (QED.TwoLoop.PauliZero.restMomentum P.m) Y =
        ((P.e ^ 2 * outerAt P.m Q (enumPhoton 0 P) : ℝ) : ℂ)

/-- **The bubble–bubble component of `ClassNestedAtLink enumClass enumPhoton`**, from the
three-loop integrability and `BBNestedAt`. -/
theorem classNestedAt_zero_of (hF : BBJointIntegrable) (hN : BBNestedAt) (P : Params)
    (hA : QED.ChainProof.ChainAdmissible P) :
    ∀ᶠ Q in 𝓝[>] (0 : ℝ), ∀ Y, QED.ChainProof.IsClassLimit enumClass 0 P
      (QED.TwoLoop.PauliZero.boostMomentum P.m Q) (QED.TwoLoop.PauliZero.restMomentum P.m) Y →
      QED.OneLoop.formFactorProj₂ P.e P.m (QED.TwoLoop.PauliZero.boostMomentum P.m Q)
          (QED.TwoLoop.PauliZero.restMomentum P.m) Y =
        ((P.e ^ 2 * outerAt P.m Q (enumPhoton 0 P) : ℝ) : ℂ) := by
  filter_upwards [hN P hA, self_mem_nhdsWithin] with Q hQ (hQ0 : 0 < Q)
  intro Y hY
  exact hQ Y ((isClassLimit_zero_iff hF hA (isPairQ_canonical' hA.hm hQ0) Y).mp hY)

/-- **Covariance of the bubble–bubble limits** (one loop; proved in `HCBB2CovBB`): at admissible
parameters, the limits `BBLim` are covariant under every spinor-lifted `L` that keeps positive
energies. -/
def BBCov : Prop :=
  ∀ P : Params, QED.ChainProof.ChainAdmissible P →
    ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ),
    QED.TwoLoop.LimitCovariance.IsSpinLift L S T →
    ∀ p' p, QED.ChainProof.IsPairQ P.m p' p → 0 < (L *ᵥ p') 0 → 0 < (L *ᵥ p) 0 →
    ∀ Y Z, BBLim P p' p Y → BBLim P (L *ᵥ p') (L *ᵥ p) Z →
      ∀ μ, S * Z μ * T = QED.Dirac.vecAct L Y μ

/-- **The bubble–bubble component of `ClassCovLink enumClass`**, from the three-loop
integrability and `BBCov`. -/
theorem classCov_zero_of (hF : BBJointIntegrable) (hC : BBCov) (P : Params)
    (hA : QED.ChainProof.ChainAdmissible P) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (S T : Matrix (Fin 4) (Fin 4) ℂ) (h : QED.TwoLoop.LimitCovariance.IsSpinLift L S T)
    (p' p : Fin 4 → ℝ) (hpq : QED.ChainProof.IsPairQ P.m p' p) (h0 : 0 < (L *ᵥ p') 0)
    (h1 : 0 < (L *ᵥ p) 0) (Y Z : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hY : QED.ChainProof.IsClassLimit enumClass 0 P p' p Y)
    (hZ : QED.ChainProof.IsClassLimit enumClass 0 P (L *ᵥ p') (L *ᵥ p) Z) (μ : Fin 4) :
    S * Z μ * T = QED.Dirac.vecAct L Y μ :=
  hC P hA L S T h p' p hpq h0 h1 Y Z ((isClassLimit_zero_iff hF hA hpq Y).mp hY)
    ((isClassLimit_zero_iff hF hA (QED.ChainProof.isPairQ_map h hpq h0 h1) Z).mp hZ) μ

/-! ### The integrability hypothesis from (HC₀) in the frozen routing -/

/-- The inverse change of loop momenta `λ ↦ (-λ 2, λ 1 + λ 2, λ 0 + λ 2)`. -/
def bbMatInv : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, -1; 0, 1, 1; 1, 0, 1]

theorem isUnit_det_bbMatInv : IsUnit bbMatInv.det := by
  rw [Matrix.det_fin_three]
  simp [bbMatInv]

/-- **The integrability in the nested routing from the integrability in the frozen routing**:
(T₉′) for the integrand of the value (T₁₀) of `repBB` (the form of
`QED.ChainProof.ChainValueIntegrable`, the per-representative content of (HC₀)) gives (T₉′) for
`bbIntegrand P (chainOuter …)`. -/
theorem jointEnergyFirstIntegrable_bb_of_chainValue (P : Params)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4)
    (h : QED.ChainProof.ChainValueIntegrable P repBB pOut pIn kIn αOut βIn μ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 3
      (bbIntegrand P fun k => chainOuter P (pIn 0) (kIn 0) k (αOut 0) (βIn 0) (μ 0)) := by
  unfold QED.ChainProof.ChainValueIntegrable at h
  rw [loopCount_repBB] at h
  have h' := QED.TwoLoop.NestedVP.jointEnergyFirstIntegrable_comp_matrix_add 3 _ bbMatInv
    isUnit_det_bbMatInv ![pIn 0, 0, 0] h
  have hx : ∀ (ℓ : Fin 3 → Fin 4 → ℝ) (p : Fin 4 → ℝ),
      ((fun s => ∑ r, bbMatInv s r • ℓ r) + ![p, 0, 0]) 2 +
          ((fun s => ∑ r, bbMatInv s r • ℓ r) + ![p, 0, 0]) 0 - p = ℓ 0 ∧
        ((fun s => ∑ r, bbMatInv s r • ℓ r) + ![p, 0, 0]) 1 +
          ((fun s => ∑ r, bbMatInv s r • ℓ r) + ![p, 0, 0]) 0 - p = ℓ 1 ∧
        p - ((fun s => ∑ r, bbMatInv s r • ℓ r) + ![p, 0, 0]) 0 = ℓ 2 := by
    intro ℓ p
    refine ⟨?_, ?_, ?_⟩ <;>
      · simp only [Pi.add_apply, Fin.sum_univ_three, bbMatInv]
        simp
  have e : (fun ℓ : Fin 3 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 3) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P repBB pIn kIn (lineMomentum₂ repBB pOut pIn kIn
        ((fun s => ∑ r, bbMatInv s r • ℓ r) + ![pIn 0, 0, 0])) αOut βIn μ) =
      bbIntegrand P fun k => chainOuter P (pIn 0) (kIn 0) k (αOut 0) (βIn 0) (μ 0) := by
    funext ℓ
    obtain ⟨x0, x1, x2⟩ := hx ℓ (pIn 0)
    rw [lineMomentum₂_repBB hmom, x0, x1, x2, integrand_eq, vec_eta]
  have h'' : QED.TwoLoop.jointEnergyFirstIntegrable 3 fun ℓ : Fin 3 → Fin 4 → ℝ =>
      (((2 * Real.pi) ^ (4 * 3) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P repBB pIn kIn (lineMomentum₂ repBB pOut pIn kIn
          ((fun s => ∑ r, bbMatInv s r • ℓ r) + ![pIn 0, 0, 0])) αOut βIn μ := h'
  rwa [e] at h''

/-- **`BBJointIntegrable` from (T₉′) for `repBB` in the frozen routing**, at T1's flavours and
the external data of the chain vertex. -/
theorem bbJointIntegrable_of_chainValue (h : ∀ P : Params, QED.ChainProof.ChainAdmissible P →
    ∀ ε : ℝ, 0 < ε → ∀ p' p : Fin 4 → ℝ, QED.ChainProof.IsPairQ P.m p' p → ∀ α β μ : Fin 4,
      QED.ChainProof.ChainValueIntegrable { P with ε := ε } repBB (fun _ => p') (fun _ => p)
        (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ)) : BBJointIntegrable := by
  intro P hA ε hε p' p hpq α β μ
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  have key := jointEnergyFirstIntegrable_bb_of_chainValue { P with ε := ε }
    (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p) hmom (fun _ => α)
    (fun _ => β) (fun _ => μ) (h P hA ε hε p' p hpq α β μ)
  exact key

end QED.ChainProof.HCBB

end
