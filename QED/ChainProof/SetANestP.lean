/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetALinkIntP
public import QED.TwoLoop.CountertermInsertion
public import QED.ChainProof.SetASpecOuterAlg

/-!
# Set (a), obligation (N): the outer integrand and the `photonCt` classes

Helper level for the set (a) headline (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`,
obligation (N) of `QED.ChainProof.SetAPauli.SetALimitLink`: the nested form of the family vertex
at fixed `ε`.

* `nestPhoton`, `nestInt`: a photon tensor `X(ℓ)` sandwiched as `Δ(ℓ) X(ℓ) Δ(-ℓ)` and inserted in
  the outer one-loop vertex chain (the shape of `QED.ChainProof.SetASpec.saOuterInt` and of
  `QED.ChainProof.SetASpec.saOuterForm_list`); linear in `X` (`nestInt_add`,
  `nestInt_const_mul`).
* `nestTree c`: the tree `-c (k² g - k k)`, the first term of
  `QED.GradedProof.VP2.vacuumPolarizationPart_two_eq` at `c = e⁴ d₃(1)`; its sandwich is twice
  the one-slot `photonCt` insertion (`nestPhoton_tree`).
* `repP_zero_eq`, `repP_one_eq`: the set (a) `photonCt` representatives are the two-loop `δ₃`
  representatives `repD3Slot1`, `repD3Slot0`.
* **`contractionValue_repP`**, **`contractionValue_repP_add`**: the value (G₅) of `repP s` at
  `gradP` is the one-loop vertex chain with one `δ₃ = e⁴ d₃(1)` slot pairing
  (`QED.TwoLoop.Insertion.contractionValue₂_repD3Slot0`), and the two together are the energy-first
  integral of `nestInt (nestTree (e⁴ d₃(1)))`. No hypothesis.
* **`efInt_nestInt_tree`**: that integrand is integrable in both stages at `ε > 0` on shell
  (the pieces `numG`, `numS`, `numL`, `numQ` of `QED.ChainProof.SetASpec.saOuterInt_false`,
  `saOuterInt_true` without spectral factor, and `QED.TwoLoop.VPHalfAtGen.efInt_powInt`).
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.ChainProof.SetANest

open QED.OneLoop QED.Integration.Feynman QED.TwoLoop.VPUnitNested QED.TwoLoop.VPHalfAtGen
open QED.TwoLoop.Insertion QED.ChainProof.HCBB2 QED.ChainProof.SetASpec
open QED.ChainProof.SetALink QED.WickModel

/-! ### The outer integrand of a photon tensor -/

/-- A photon tensor `X(ℓ)^{ab}` sandwiched between the two photon propagators,
`∑_{ab} Δ(ℓ)_{νa} X(ℓ)^{ab} Δ(-ℓ)_{ρb}` (the shape of `saOuterPhoton`). -/
noncomputable def nestPhoton (mγ Λ ε : ℝ) (X : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (ℓ : Fin 4 → ℝ) (ν ρ : Fin 4) : ℂ :=
  ∑ a, ∑ b, photonPropagator mγ Λ ε ℓ ν a * X ℓ a b * photonPropagator mγ Λ ε (-ℓ) ρ b

/-- **The outer integrand of a photon tensor**: the `(i, j)` entry of the one-loop vertex chain
with the electron propagators at `p' + ℓ`, `p + ℓ` and the photon factor `nestPhoton`. -/
noncomputable def nestInt (e m mγ Λ ε : ℝ) (p' p : Fin 4 → ℝ)
    (X : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (μ i j : Fin 4) (ℓ : Fin 4 → ℝ) : ℂ :=
  vertexChain e μ (electronPropagator m ε (p' + ℓ)) (electronPropagator m ε (p + ℓ))
    (nestPhoton mγ Λ ε X ℓ) i j

theorem nestInt_add (e m mγ Λ ε : ℝ) (p' p : Fin 4 → ℝ) (X Y : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (μ i j : Fin 4) (ℓ : Fin 4 → ℝ) :
    nestInt e m mγ Λ ε p' p (fun k a b => X k a b + Y k a b) μ i j ℓ =
      nestInt e m mγ Λ ε p' p X μ i j ℓ + nestInt e m mγ Λ ε p' p Y μ i j ℓ := by
  have h : nestPhoton mγ Λ ε (fun k a b => X k a b + Y k a b) ℓ =
      fun ν ρ => nestPhoton mγ Λ ε X ℓ ν ρ + nestPhoton mγ Λ ε Y ℓ ν ρ := by
    funext ν ρ
    simp only [nestPhoton, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [nestInt, h, vertexChain_add_photon]
  rfl

theorem nestInt_const_mul (e m mγ Λ ε : ℝ) (p' p : Fin 4 → ℝ) (c : ℂ)
    (X : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (μ i j : Fin 4) (ℓ : Fin 4 → ℝ) :
    nestInt e m mγ Λ ε p' p (fun k a b => c * X k a b) μ i j ℓ =
      c * nestInt e m mγ Λ ε p' p X μ i j ℓ := by
  have h : nestPhoton mγ Λ ε (fun k a b => c * X k a b) ℓ =
      fun ν ρ => c * nestPhoton mγ Λ ε X ℓ ν ρ := by
    funext ν ρ
    simp only [nestPhoton, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [nestInt, h, vertexChain_smul_photon]
  rfl

/-! ### The tree term -/

/-- The photon counterterm tree `-c (k² g^{ab} - k^a k^b)`, with `c = e⁴ d₃(1)` the first term of
`QED.GradedProof.VP2.vacuumPolarizationPart_two_eq`. -/
noncomputable def nestTree (c : ℝ) (k : Fin 4 → ℝ) (a b : Fin 4) : ℂ :=
  -((c * (Minkowski.dot k k * Minkowski.metric a b - k a * k b) : ℝ) : ℂ)

/-- The sandwich of the tree is the photon line with both slot pairings of the `photonCt`
vertex. -/
theorem nestPhoton_tree (c mγ Λ ε : ℝ) (ℓ : Fin 4 → ℝ) (ν ρ : Fin 4) :
    nestPhoton mγ Λ ε (nestTree c) ℓ ν ρ = 2 * photonInsertion c mγ Λ ε ℓ ν ρ := by
  simp only [nestPhoton, photonInsertion, photonCtFactor, nestTree, photonPropagator_neg',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  field_simp

/-! ### The value of the `photonCt` classes -/

/-- `repP 1` is the slot-`0` representative of the two-loop `δ₃` class. -/
theorem repP_one_eq : (repP 1 : Contraction 1 1 QED.TwoLoop.Enumeration.k_gggp) =
    QED.TwoLoop.Relabel.repD3Slot0 :=
  Subtype.ext (Prod.ext (Equiv.ext (by decide +kernel)) (Equiv.ext (by decide +kernel)))

/-- `repP 0` is the slot-`1` representative of the two-loop `δ₃` class. -/
theorem repP_zero_eq : (repP 0 : Contraction 1 1 QED.TwoLoop.Enumeration.k_gggp) =
    QED.TwoLoop.Relabel.repD3Slot1 :=
  Subtype.ext (Prod.ext (Equiv.ext (by decide +kernel)) (Equiv.ext (by decide +kernel)))

/-- **The value of a `photonCt` class**: the energy-first integral of the one-loop vertex chain
whose photon factor is one slot pairing of the level-`1` photon counterterm, `δ₃ = e⁴ d₃(1)`,
with the open-line mass. No hypothesis. -/
theorem contractionValue_repP (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (s : Fin 2) (p' p : Fin 4 → ℝ)
    (μ i j : Fin 4) :
    Graded.contractionValue P Φ D (repP s) gradP (fun _ => p') (fun _ => p) (fun _ => p' - p)
        (fun _ => i) (fun _ => j) (fun _ => μ) =
      energyFirstIntegral fun ℓ =>
        vertexChain P.e μ (electronPropagator (Φ.mass Φ.openLine) P.ε (p' + ℓ))
          (electronPropagator (Φ.mass Φ.openLine) P.ε (p + ℓ))
          (photonInsertion (P.e ^ 4 * D.d₃ 1) P.mγ P.Λ P.ε ℓ) i j := by
  have h1 : Graded.contractionValue P Φ D (repP s) gradP (fun _ => p') (fun _ => p)
      (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) =
      contractionValue₂ (ctParamsP P Φ D) (repP s) (fun _ => p') (fun _ => p) (fun _ => p' - p)
        (fun _ => i) (fun _ => j) (fun _ => μ) := by
    unfold Graded.contractionValue contractionValue₂
    simp only [regulatedAmplitude_repP, regulatedAmplitude₂_eq_zeroFlavoring _ (repP_cycle s)]
  have hmom : p' = p + (p' - p) := by abel
  have h2 := contractionValue₂_repD3Slot0 (ctParamsP P Φ D) (pOut := fun _ => p')
    (pIn := fun _ => p) (kIn := fun _ => p' - p) hmom (fun _ => i) (fun _ => j) (fun _ => μ)
  rw [h1]
  fin_cases s
  · have e0 := congrArg (fun C => contractionValue₂ (ctParamsP P Φ D) C (fun _ => p')
      (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ)) repP_zero_eq
    exact e0.trans ((contractionValue₂_d3Slot0_eq_d3Slot1 _ (pOut := fun _ => p')
      (pIn := fun _ => p) (kIn := fun _ => p' - p) hmom _ _ _).symm.trans h2)
  · have e1 := congrArg (fun C => contractionValue₂ (ctParamsP P Φ D) C (fun _ => p')
      (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ)) repP_one_eq
    exact e1.trans h2

/-- **The two `photonCt` classes together** are the energy-first integral of the outer integrand
of the tree `nestTree (e⁴ d₃(1))`. No hypothesis. -/
theorem contractionValue_repP_add (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    Graded.contractionValue P Φ D (repP 0) gradP (fun _ => p') (fun _ => p) (fun _ => p' - p)
        (fun _ => i) (fun _ => j) (fun _ => μ) +
      Graded.contractionValue P Φ D (repP 1) gradP (fun _ => p') (fun _ => p) (fun _ => p' - p)
        (fun _ => i) (fun _ => j) (fun _ => μ) =
      energyFirstIntegral (nestInt P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p
        (nestTree (P.e ^ 4 * D.d₃ 1)) μ i j) := by
  rw [contractionValue_repP, contractionValue_repP, ← two_mul, ← efi_const_mul]
  congr 1
  funext ℓ
  have h : nestPhoton P.mγ P.Λ P.ε (nestTree (P.e ^ 4 * D.d₃ 1)) ℓ =
      fun ν ρ => 2 * photonInsertion (P.e ^ 4 * D.d₃ 1) P.mγ P.Λ P.ε ℓ ν ρ :=
    funext fun ν => funext fun ρ => nestPhoton_tree _ _ _ _ ℓ ν ρ
  rw [nestInt, h, vertexChain_smul_photon]
  rfl

/-! ### Integrability of the tree term -/

theorem integral_simplexSet_zero (c : ℂ) : ∫ _ in simplexSet 0, c = c := by
  have ht : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h : simplexSet 0 = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    rw [← snoc_smul_mem_simplexSet_iff ht x, snoc_mem_simplexSet_iff]
    norm_num
  rw [h, Measure.restrict_univ, integral_const, volume_pi, Measure.pi_of_empty]
  simp

/-- The scalar of a term without spectral factor is `(k²)ʲ`. -/
theorem saSpecScalar_zero (J : ℕ) (ε : ℝ) (k : Fin 4 → ℝ) :
    saSpecScalar J 0 (fun _ : Fin 0 → ℝ => 0) (fun _ => 0) (fun _ => 1) ε k =
      ((Minkowski.dot k k : ℝ) : ℂ) ^ J := by
  simp only [saSpecScalar, pow_zero, inv_one, mul_one, integral_simplexSet_zero]

theorem saLimTermInt_zero (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (J : ℕ) {k : ℕ}
    (Ms : Fin (k + 2) → ℝ) (ε : ℝ) (p' p ℓ : Fin 4 → ℝ) :
    saLimTermInt N m J Ms 0 (fun _ : Fin 0 → ℝ => 0) (fun _ => 0) (fun _ => 1) ε p' p ℓ =
      powInt N m J Ms (fun _ => ε) ε p' p ℓ := by
  rw [saLimTermInt_eq_mul]
  simp only [pow_zero, inv_one, mul_one, integral_simplexSet_zero]

/-- The sandwich of the tree as two spectral terms without spectral factor. -/
theorem nestPhoton_tree_eq (c mγ Λ ε : ℝ) (ℓ : Fin 4 → ℝ) :
    nestPhoton mγ Λ ε (nestTree c) ℓ = fun ν ρ =>
      (-(c : ℂ)) * saOuterPhoton mγ Λ false 1 0 (fun _ : Fin 0 → ℝ => 0) (fun _ => 0)
          (fun _ => 1) ε ℓ ν ρ +
        (c : ℂ) * saOuterPhoton mγ Λ true 0 0 (fun _ : Fin 0 → ℝ => 0) (fun _ => 0)
          (fun _ => 1) ε ℓ ν ρ := by
  funext ν ρ
  simp only [saOuterPhoton, saSpecScalar_zero, nestPhoton, nestTree, Finset.mul_sum,
    ← Finset.sum_add_distrib, saTens]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  push_cast
  ring

section Int

variable {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hmΛ : mγ ≤ Λ) {p' p : Fin 4 → ℝ}
  (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
  (hp0 : 0 < p 0)
include hm hmγ hmΛ hp' hp hp0' hp0

theorem efInt_powInt_saMs4 {N : (Fin 4 → ℝ) → ℂ} (hN : QuadN N) {J : ℕ} (hJ : J ≤ 2)
    {ε : ℝ} (hε : 0 < ε) : EFInt (powInt N m J (saMs4 mγ Λ) (fun _ => ε) ε p' p) := by
  obtain ⟨α, hα⟩ := hN.quad
  obtain ⟨C, hC⟩ := hN.bound
  refine efInt_powInt (α := α) (CN := C) hm hmγ hp' hp hp0' hp0 hN.cont hα hC hJ ?_
    (fun _ => hε) hε
  intro i
  fin_cases i <;> simp [saMs4, hmΛ]

/-- **The outer integrand of the tree is integrable in both stages**, at `ε > 0`, on shell. -/
theorem efInt_nestInt_tree (e c : ℝ) (μ i j : Fin 4) {ε : ℝ} (hε : 0 < ε) :
    EFInt (nestInt e m mγ Λ ε p' p (nestTree c) μ i j) := by
  have hG := efInt_powInt_saMs4 hm hmγ hmΛ hp' hp hp0' hp0 (quadN_numG m p' p μ i j)
    (J := 1) (by norm_num) hε
  have hS := efInt_powInt_saMs4 hm hmγ hmΛ hp' hp hp0' hp0 (quadN_numS μ i j)
    (J := 0 + 1) (by norm_num) hε
  have hL := efInt_powInt_saMs4 hm hmγ hmΛ hp' hp hp0' hp0 (quadN_numL m p' p μ i j)
    (J := 0 + 1) (by norm_num) hε
  have hQ := efInt_powInt_saMs4 hm hmγ hmΛ hp' hp hp0' hp0 (quadN_numQ m p' p μ i j)
    (J := 0) (by norm_num) hε
  have h := ((hG.const_mul (kap e * (((Λ ^ 2 - mγ ^ 2) ^ 2 : ℝ) : ℂ))).const_mul (-(c : ℂ))).add
    ((((hS.add hL).add hQ).const_mul (kap e * (((Λ ^ 2 - mγ ^ 2) ^ 2 : ℝ) : ℂ))).const_mul
      (c : ℂ))
  have e' : nestInt e m mγ Λ ε p' p (nestTree c) μ i j = fun ℓ =>
      -(c : ℂ) * (kap e * (((Λ ^ 2 - mγ ^ 2) ^ 2 : ℝ) : ℂ) *
          powInt (numG m p' p μ i j) m 1 (saMs4 mγ Λ) (fun _ => ε) ε p' p ℓ) +
        (c : ℂ) * (kap e * (((Λ ^ 2 - mγ ^ 2) ^ 2 : ℝ) : ℂ) *
          (powInt (numS μ i j) m (0 + 1) (saMs4 mγ Λ) (fun _ => ε) ε p' p ℓ +
            powInt (numL m p' p μ i j) m (0 + 1) (saMs4 mγ Λ) (fun _ => ε) ε p' p ℓ +
            powInt (numQ m p' p μ i j) m 0 (saMs4 mγ Λ) (fun _ => ε) ε p' p ℓ)) := by
    funext ℓ
    rw [nestInt, nestPhoton_tree_eq, vertexChain_add_photon, vertexChain_smul_photon,
      vertexChain_smul_photon]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have h1 := saOuterInt_false e m mγ Λ p' p μ i j 1 0 (fun _ : Fin 0 → ℝ => 0) (fun _ => 0)
      (fun _ => 1) hε ℓ
    have h2 := saOuterInt_true e m mγ Λ p' p μ i j 0 0 (fun _ : Fin 0 → ℝ => 0) (fun _ => 0)
      (fun _ => 1) hε ℓ
    simp only [saOuterInt, saLimTermInt_zero] at h1 h2
    rw [h1, h2]
  rw [e']
  exact h

end Int

end QED.ChainProof.SetANest
