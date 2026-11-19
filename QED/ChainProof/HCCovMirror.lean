/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCClasses
public import QED.Algebra.FormFactorIndependence
public import Mathlib.Topology.Instances.Matrix

/-!
# The mirror link of the chain vertex from a fixed-regulator identity

Helper level, Phase 5 Stage 1a, obligation O3-8 (no `q^μ` term). The link
`QED.ChainProof.ChainMirrorLink` of `QED/ChainProof/HCLinks.lean` asks every `ε → 0⁺` limit of
the chain vertex with two insertions to be mirror symmetric,
`S_K C (V^μ)ᵀ C S_K⁻¹ = -(R_K)^μ_ν V^ν` with `K = p' + p`.

The two-loop proof (`QED/TwoLoop/LimitMirror*.lean`) splits this into charge conjugation at fixed
`ε`, which relates `(p', p)` to the negative-energy point `(-p, -p')`, and covariance of the limits
under the time-reversing reflection `R_K`. Neither the limits at negative energies nor `R_K`
covariance are part of the Stage 1a links. Here the reflection is replaced by `-R_K`, which keeps
positive energies (`-R_K p' = p`, `-R_K p = p'`) and has the spinor lift `(S_K Γ, Γ S_K⁻¹)` with
the chirality matrix `Γ = diag(-1, -1, 1, 1)` (`isSpinLift_neg_reflect`). It is therefore covered
by `ChainCovLink`. The step from `(-p, -p')` back to `(p, p')` is the inversion of all momenta,
which holds at fixed `ε` (`QED/ChainProof/HCCovInv.lean`). The fixed-`ε` input is then the single
identity, between two positive-energy points:

* `ChainMirrorAt`: `C V_ε(p', p)^μᵀ C = Γ V_ε(p, p')^μ Γ` for the chain vertex at every `ε > 0`.
  It is proved in `QED/ChainProof/HCCovConj.lean` (`QED.ChainProof.Conj.chainMirrorAt`).

Proved here:
* `chainMirrorLink_of_mirrorAt`: **`ChainMirrorLink` from `ChainExistsLink`, `ChainCovLink` and
  `ChainMirrorAt`**.
* `chainMirrorAt_of_classes`: `ChainMirrorAt` from the class decomposition and the per-class
  identity `ClassMirrorLink X σ`, `C X_r(p', p)ᵀ C = Γ X_{σ r}(p, p') Γ` at fixed `ε` for a
  permutation `σ` of the classes. `σ` swaps the bubble–`δ₃` and `δ₃`–bubble classes, so the
  identity is stated for the sum and not class by class.
* `isFormFactorPair_vertexChain_two_pauli_limit_of_classes_mirrorAt`: the exact proposition of
  (HC₃) from the class decomposition, the two per-class limit links, the per-class fixed-`ε`
  mirror identity and the Pauli link. It needs no mirror statement about limits.
-/

@[expose] public section

open Complex Matrix Filter Topology
open scoped Real
open QED.WickModel (Params IsElectronOnShell IsPhotonOnShell)

namespace QED.ChainProof

open QED.TwoLoop.LimitCovariance QED.Dirac

/-- The chirality matrix `Γ = diag(-1, -1, 1, 1)` of the Weyl representation. -/
abbrev chir : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![(-1 : ℂ), -1, 1, 1]

theorem chir_mul_chir : chir * chir = 1 := chirality_mul_chirality

theorem chir_mul_gamma_mul_chir (μ : Fin 4) : chir * gamma μ * chir = -gamma μ := by
  rw [chirality_mul_gamma, Matrix.neg_mul, Matrix.mul_assoc, chir_mul_chir, Matrix.mul_one]

theorem vecAct_neg (L : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (μ : Fin 4) : vecAct (-L) V μ = -vecAct L V μ := by
  simp only [vecAct, Matrix.neg_apply, ofReal_neg, neg_smul, Finset.sum_neg_distrib]

/-- **The spinor lift of `-R_a`**: `(S_a Γ, Γ S_a⁻¹)`. -/
theorem isSpinLift_neg_reflect {a : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0) :
    IsSpinLift (-reflectMatrix a) (reflSpin a * chir)
      (chir * (((Minkowski.dot a a : ℝ) : ℂ)⁻¹ • reflSpin a)) where
  mul_eq_one := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc chir chir, chir_mul_chir, Matrix.one_mul,
      reflSpin_mul_inv ha]
  cov := fun μ => by
    have e : reflSpin a * chir * gamma μ * (chir * (((Minkowski.dot a a : ℝ) : ℂ)⁻¹ •
        reflSpin a)) = -(reflSpin a * gamma μ * (((Minkowski.dot a a : ℝ) : ℂ)⁻¹ •
        reflSpin a)) := by
      rw [show reflSpin a * chir * gamma μ * (chir * (((Minkowski.dot a a : ℝ) : ℂ)⁻¹ •
          reflSpin a)) = reflSpin a * (chir * gamma μ * chir) *
          (((Minkowski.dot a a : ℝ) : ℂ)⁻¹ • reflSpin a) by simp only [Matrix.mul_assoc],
        chir_mul_gamma_mul_chir, Matrix.mul_neg, Matrix.neg_mul]
    rw [e, isCovariantUnder_reflect_gamma ha μ, vecAct_neg]

/-- The pairs with `q² > 0` are symmetric. -/
theorem isPairQ_swap {m : ℝ} {p' p : Fin 4 → ℝ} (h : IsPairQ m p' p) : IsPairQ m p p' := by
  obtain ⟨hp', hp, h0', h0, hq⟩ := h
  refine ⟨hp, hp', h0, h0', ?_⟩
  have e : Minkowski.dot (p - p') (p - p') = Minkowski.dot (p' - p) (p' - p) := by
    simp only [Minkowski.dot_eq, Pi.sub_apply]
    ring
  rw [e]
  exact hq

/-- A sequence of `4 × 4` matrices converges iff every entry does. -/
theorem tendsto_matrix_iff {α : Type*} {F : Filter α} {f : α → Matrix (Fin 4) (Fin 4) ℂ}
    {A : Matrix (Fin 4) (Fin 4) ℂ} :
    Tendsto f F (𝓝 A) ↔ ∀ i j, Tendsto (fun x => f x i j) F (𝓝 (A i j)) :=
  tendsto_pi_nhds.trans (forall_congr' fun _ => tendsto_pi_nhds)

/-- **The mirror identity of the chain vertex at fixed `ε`**, between the two positive-energy
points `(p', p)` and `(p, p')`: `C V_ε(p', p)^μᵀ C = Γ V_ε(p, p')^μ Γ`. It combines charge
conjugation, `C V_ε(p', p)ᵀ C = -V_ε(-p, -p')`, with the inversion of all momenta,
`V_ε(-p, -p') = -Γ V_ε(p, p') Γ`. -/
def ChainMirrorAt : Prop :=
  ∀ P : Params, ChainAdmissible P → ∀ ε : ℝ, 0 < ε → ∀ p' p, IsPairQ P.m p' p → ∀ μ,
    chargeConj * (QED.VPChain.vertexChain 2 { P with ε := ε } (chainFlavors P) p' p μ)ᵀ *
        chargeConj =
      chir * QED.VPChain.vertexChain 2 { P with ε := ε } (chainFlavors P) p p' μ * chir

/-- The fixed-`ε` mirror identity passes to the limits. -/
theorem chargeConj_chainLim (hMA : ChainMirrorAt) {P : Params} (hA : ChainAdmissible P)
    {p' p : Fin 4 → ℝ} (hpq : IsPairQ P.m p' p) {V W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hV : chainLim P p' p V) (hW : chainLim P p p' W) (μ : Fin 4) :
    chargeConj * (V μ)ᵀ * chargeConj = chir * W μ * chir := by
  have hV' := tendsto_matrix_iff.2 (hV μ)
  have hW' := tendsto_matrix_iff.2 (hW μ)
  have c1 : Continuous fun M : Matrix (Fin 4) (Fin 4) ℂ => chargeConj * Mᵀ * chargeConj :=
    (continuous_const.matrix_mul continuous_id.matrix_transpose).matrix_mul continuous_const
  have c2 : Continuous fun M : Matrix (Fin 4) (Fin 4) ℂ => chir * M * chir :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have h1 := (c1.tendsto (V μ)).comp hV'
  have h2 := (c2.tendsto (W μ)).comp hW'
  refine tendsto_nhds_unique (h1.congr' ?_) h2
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hMA P hA ε hε p' p hpq μ

/-- **The mirror link from existence, covariance and the fixed-`ε` mirror identity.** -/
theorem chainMirrorLink_of_mirrorAt (hE : ChainExistsLink) (hC : ChainCovLink)
    (hMA : ChainMirrorAt) : ChainMirrorLink := by
  intro P hA p' p hpq V hV
  have hpq' := isPairQ_swap hpq
  obtain ⟨hp', hp, hp0', hp0, hq⟩ := id hpq
  obtain ⟨W, hW⟩ := hE P hA p p' hpq'
  have hK := QED.OneLoop.dot_add_self_ne_zero hp' hp hq
  obtain ⟨hRp, hRp', -⟩ := QED.OneLoop.reflect_add_self hp' hp hq
  have hLp' : (-reflectMatrix (p' + p)) *ᵥ p' = p := by
    rw [Matrix.neg_mulVec, reflectMatrix_mulVec, hRp', neg_neg]
  have hLp : (-reflectMatrix (p' + p)) *ᵥ p = p' := by
    rw [Matrix.neg_mulVec, reflectMatrix_mulVec, hRp, neg_neg]
  have hcov := hC P hA _ _ _ (isSpinLift_neg_reflect hK) p' p hpq (by rw [hLp']; exact hp0)
    (by rw [hLp]; exact hp0') V W hV (by rw [hLp', hLp]; exact hW)
  intro μ
  rw [chargeConj_chainLim hMA hA hpq hV hW μ, ← vecAct_neg, ← hcov μ]
  simp only [Matrix.mul_assoc]

section Classes

variable {ι : Type*} [Fintype ι]
  {X : ι → Params → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}

variable (X) in
/-- **The per-class mirror identity at fixed `ε`**: for a permutation `σ` of the classes,
`C X_r(p', p)^μᵀ C = Γ X_{σ r}(p, p')^μ Γ` at every `ε > 0` and every positive-energy pair with
`q² > 0`. For set (b), `σ` swaps the bubble–`δ₃` and `δ₃`–bubble classes and fixes the
bubble–bubble and `δ₃`–`δ₃` classes up to the orientations of the insertions. -/
def ClassMirrorLink (σ : ι ≃ ι) : Prop :=
  ∀ r P, ChainAdmissible P → ∀ ε : ℝ, 0 < ε → ∀ p' p, IsPairQ P.m p' p → ∀ μ,
    chargeConj * (X r { P with ε := ε } p' p μ)ᵀ * chargeConj =
      chir * X (σ r) { P with ε := ε } p p' μ * chir

/-- **The fixed-`ε` mirror identity of the chain vertex from the classes.** -/
theorem chainMirrorAt_of_classes (hD : ChainClassDecomposition X) {σ : ι ≃ ι}
    (hX : ClassMirrorLink X σ) : ChainMirrorAt := by
  intro P hA ε hε p' p hpq μ
  rw [hD P hA ε hε p' p hpq μ, hD P hA ε hε p p' (isPairQ_swap hpq) μ, Matrix.transpose_sum,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_sum, Matrix.sum_mul,
    ← Equiv.sum_comp σ (fun r => chir * X r { P with ε := ε } p p' μ * chir)]
  exact Finset.sum_congr rfl fun r _ => hX r P hA ε hε p' p hpq μ

/-- **The set (b) headline (HC₃) with the mirror obligation at fixed `ε`.** The conclusion is,
verbatim, the proposition of the frozen `QED.VPChain.isFormFactorPair_vertexChain_two_pauli_limit`;
the hypotheses are the class decomposition (O3-4), the per-class limits (O3-5/O3-6) and their
covariance (O3-8), the per-class fixed-`ε` mirror identity (O3-8), and the Pauli link (O3-9). -/
theorem isFormFactorPair_vertexChain_two_pauli_limit_of_classes_mirrorAt
    (hD : ChainClassDecomposition X) (hL : ClassLimitLink X) (hC : ClassCovLink X) {σ : ι ≃ ι}
    (hX : ClassMirrorLink X σ) (hPA : ChainPauliAtLink)
    (P₀ : Params) (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (η : ℝ) (hη : 0 < η) :
    ∃ RM : ℝ, ∀ (M₁ M₂ c₁ c₂ : ℝ) (hM₁ : P₀.m < M₁) (hM₂ : P₀.m < M₂), RM < M₁ → RM < M₂ →
      ∀ (hPV₁ : 1 + c₁ + c₂ = 0) (hPV₂ : P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0),
      ∃ δ > 0, ∃ R : ℝ, ∀ (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ), mγ < δ → R < Λ →
        (∃ d₁ d₂ dm d₃ : ℝ,
          IsElectronOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hmγ hΛ ∧
          QED.OneLoop.IsChargeNormalized P₀.e (1 + d₁) P₀.m mγ Λ hm hmγ hΛ ∧
          IsPhotonOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hM₁ hM₂ hPV₁ hPV₂) ∧
        ∀ d₁ d₂ dm d₃ : ℝ,
          IsElectronOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hmγ hΛ →
          QED.OneLoop.IsChargeNormalized P₀.e (1 + d₁) P₀.m mγ Λ hm hmγ hΛ →
          IsPhotonOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hM₁ hM₂ hPV₁ hPV₂ →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ V, QED.VPChain.IsVertexChainLimit 2
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ }
              ⟨![P₀.m, M₁, M₂], ![1, c₁, c₂], 0⟩ p' p V) ∧
            ∀ V, QED.VPChain.IsVertexChainLimit 2
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ }
              ⟨![P₀.m, M₁, M₂], ![1, c₁, c₂], 0⟩ p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 -
                  (QED.VPChain.a1SixSetB : ℂ)‖ < η :=
  isFormFactorPair_vertexChain_two_pauli_limit_of_classes hD hL hC
    (chainMirrorLink_of_mirrorAt (chainExistsLink_of_classes hD hL)
      (chainCovLink_of_classes hD hL hC) (chainMirrorAt_of_classes hD hX)) hPA P₀ he hm η hη

end Classes

end QED.ChainProof

end
