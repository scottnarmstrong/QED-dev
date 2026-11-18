/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.CountertermLimitProduct
public import QED.TwoLoop.CountertermInsertion
public import QED.TwoLoop.ParametricBridgeVPFlavour
public import QED.OneLoop.VertexEnergyFirst

/-!
# The `ε → 0⁺` limit of the seven counterterm classes

Obligation O2-7 for the counterterm classes of the order-`e⁵` vertex
(`QED.TwoLoop.Relabel.CtClass`, `docs/TWO-LOOP-DERIVATION.md`, sections 4.3 and 5.1): for
`m, m_γ, Λ > 0`, on-shell `p = pIn 0`, `p' = pOut 0` with `(p' - p)² ≥ 0` and momentum
conservation, the value (T₁₀) of each class representative at the prescription `ε` converges as
`ε → 0⁺`, for every choice of indices and every value of the counterterms.

* **`δ₂`, `δ_m` on either internal electron line** (`exists_tendsto_contractionValue₂_d2In`,
  `…_d2Out`) and **`δ₃` on the internal photon, both slot pairings**
  (`exists_tendsto_contractionValue₂_d3Slot0`, `…Slot1`). The value is the energy-first integral
  of the one-loop vertex chain with the inserted line (`contractionValue₂_repD2In`, …). At
  `ε ≠ 0` its integrand is a polynomial of degree at most four in the loop momentum
  (`numD2In`, `numD2Out`, `numD3`) times five, resp. six, inverse propagator denominators
  (`integrand_d2In_eq`, …): the inserted line is doubled, and for `δ₃` both Pauli–Villars photon
  denominators are squared. The limit is given by
  `QED.TwoLoop.CountertermLimit.exists_tendsto_energyFirstIntegral_of_product`, with the line
  kinds `kindsD2In`, `kindsD2Out`, `kindsD3`; the criterion is checked by `decide`, the numerator
  bound is `refinedBound_of_dependsOnZero` and the positivity is `symanzikV_kinds_ge`. Neither
  the `O(ε)` defect of the `δ₂` insertion identity nor the longitudinal part of the `δ₃` insertion
  needs separate treatment: the whole class integrand is handled at once.
* **`δ₁` at each of the three vertices** (`exists_tendsto_contractionValue₂_d1At1`, …): the value
  is `δ₁` times the one-loop vertex (`contractionValue₂_d1At1`), whose limit is
  `QED.OneLoop.VertexLimit.tendsto_energyFirstIntegral_vertexIntegrand`. That proof uses positive
  energies `p⁰, p'⁰ > 0`, which are therefore assumed for these three classes.

## Main statements

* `exists_tendsto_contractionValue₂_ctClass`: every counterterm class value has a limit.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology

namespace QED.TwoLoop.CountertermLimit

open QED.WickModel QED.TwoLoop.Insertion QED.TwoLoop.Bridge QED.TwoLoop.Relabel
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix LoopQuartic RefinedBound
  NoSubdivergenceRefined IntNoSubdivergenceRefined noSubdivergenceRefined_castLoopMatrix_iff
  symanzikU symanzikV)

/-! ### Degree bounds for matrix-valued polynomials -/

section PolyMat

variable {L n n' : ℕ} {A B : (Fin L → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}

theorem isLoopPolyMat_mono (h : IsLoopPolyMat L n A) (hn : n ≤ n') : IsLoopPolyMat L n' A :=
  fun i j => (h i j).mono hn

theorem isLoopPolyMat_add (hA : IsLoopPolyMat L n A) (hB : IsLoopPolyMat L n B) :
    IsLoopPolyMat L n fun ℓ => A ℓ + B ℓ := fun i j => by
  simp only [Matrix.add_apply]
  exact (hA i j).add (hB i j)

theorem isLoopPolyMat_smul (c : ℂ) (hA : IsLoopPolyMat L n A) :
    IsLoopPolyMat L n fun ℓ => c • A ℓ := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (hA i j).const_mul c

theorem isLoopPolyMat_neg (hA : IsLoopPolyMat L n A) : IsLoopPolyMat L n fun ℓ => -A ℓ :=
  fun i j => by
  simp only [Matrix.neg_apply]
  simpa using (hA i j).const_mul (-1)

end PolyMat

theorem isLoopPolyMat_vertexChain (e : ℝ) (μ : Fin 4) {L a b d : ℕ}
    {A B : (Fin L → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    {D : (Fin L → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} (hA : IsLoopPolyMat L a A)
    (hB : IsLoopPolyMat L b B) (hD : ∀ ν ρ, IsLoopPoly L d fun ℓ => D ℓ ν ρ) :
    IsLoopPolyMat L (d + (a + b)) fun ℓ => vertexChain e μ (A ℓ) (B ℓ) (D ℓ) := by
  intro i j
  unfold vertexChain
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  refine IsLoopPoly.const_mul _ (IsLoopPoly.sum _ fun ν _ => IsLoopPoly.sum _ fun ρ _ => ?_)
  have h := ((((IsLoopPolyMat.const (L := L) (Dirac.gamma ρ)).mul hA).mul
    (IsLoopPolyMat.const (Dirac.gamma μ))).mul hB).mul (IsLoopPolyMat.const (Dirac.gamma ν))
  exact (hD ν ρ).mul ((h i j).mono (by omega))

theorem isLoopAffine_add_zero (p : Fin 4 → ℝ) :
    IsLoopAffine fun ℓ : Fin 2 → Fin 4 → ℝ => p + ℓ 0 :=
  ⟨![1, 0], p, fun ℓ => by
    funext ν
    simp [Fin.sum_univ_two, add_comm]⟩

theorem isLoopAffine_zero : IsLoopAffine fun ℓ : Fin 2 → Fin 4 → ℝ => ℓ 0 :=
  ⟨![1, 0], 0, fun ℓ => by
    funext ν
    simp [Fin.sum_univ_two]⟩

/-! ### Propagators in denominator form -/

/-- The photon numerator `g_{νρ} (Λ² - m_γ²)` of the combined Pauli–Villars pair. -/
noncomputable def pvPhotonNum (mγ Λ : ℝ) (ν ρ : Fin 4) : ℂ :=
  ((Minkowski.metric ν ρ * (Λ ^ 2 - mγ ^ 2) : ℝ) : ℂ)

theorem electronPropagator_eq_smul (m ε : ℝ) (k : Fin 4 → ℝ) :
    QED.OneLoop.electronPropagator m ε k = (propDenom m ε k)⁻¹ • electronNumerator m k :=
  rfl

theorem photonPropagator_eq_scalar (mγ Λ : ℝ) {ε : ℝ} (hε : ε ≠ 0) (k : Fin 4 → ℝ) :
    QED.OneLoop.photonPropagator mγ Λ ε k =
      fun ν ρ => ((propDenom mγ ε k)⁻¹ * (propDenom Λ ε k)⁻¹) * pvPhotonNum mγ Λ ν ρ := by
  funext ν ρ
  rw [photonPropagator_eq_mul _ _ hε, pvPhotonNum]
  ring

theorem electronInsertion_eq_smul (m ε δ₂ δm : ℝ) (k : Fin 4 → ℝ) :
    electronInsertion m ε δ₂ δm k = ((propDenom m ε k)⁻¹ * (propDenom m ε k)⁻¹) •
      -(electronNumerator m k * fermionCtMatrix δ₂ δm m k * electronNumerator m k) := by
  rw [electronInsertion, electronPropagator_eq_smul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, smul_neg]

theorem fermionCtMatrix_eq (δ₂ δm m : ℝ) (k : Fin 4 → ℝ) :
    fermionCtMatrix δ₂ δm m k =
      (-(δ₂ : ℂ)) • electronNumerator 0 k +
        ((δm * m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  simp [fermionCtMatrix, electronNumerator]

theorem isLoopPolyMat_electronNumerator_add (m : ℝ) (p : Fin 4 → ℝ) :
    IsLoopPolyMat 2 1 fun ℓ => electronNumerator m (p + ℓ 0) :=
  (isLoopAffine_add_zero p).isLoopPolyMat_electronNumerator m

theorem isLoopPolyMat_insertion (m δ₂ δm : ℝ) (p : Fin 4 → ℝ) :
    IsLoopPolyMat 2 3 fun ℓ => -(electronNumerator m (p + ℓ 0) *
      fermionCtMatrix δ₂ δm m (p + ℓ 0) * electronNumerator m (p + ℓ 0)) := by
  have hC : IsLoopPolyMat 2 1 fun ℓ => fermionCtMatrix δ₂ δm m (p + ℓ 0) := by
    simp only [fermionCtMatrix_eq]
    exact isLoopPolyMat_add
      (isLoopPolyMat_smul _ ((isLoopAffine_add_zero p).isLoopPolyMat_electronNumerator 0))
      (isLoopPolyMat_mono (isLoopPolyMat_smul _
        (IsLoopPolyMat.const (1 : Matrix (Fin 4) (Fin 4) ℂ))) (Nat.zero_le _))
  exact isLoopPolyMat_neg (((isLoopPolyMat_electronNumerator_add m p).mul hC).mul
    (isLoopPolyMat_electronNumerator_add m p))

/-! ### `δ₂`, `δ_m` on the incoming internal electron line -/

/-- The numerator of the `δ₂`, `δ_m` class on the incoming line. -/
noncomputable def numD2In (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) (k : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  vertexChain P.e μ (electronNumerator P.m (p' + k))
    (-(electronNumerator P.m (p + k) * fermionCtMatrix P.δ₂ P.δm P.m (p + k) *
      electronNumerator P.m (p + k)))
    (pvPhotonNum P.mγ P.Λ)

theorem integrand_d2In_eq (P : Params) {ε : ℝ} (hε : ε ≠ 0) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (k : Fin 4 → ℝ) :
    vertexChain P.e μ (QED.OneLoop.electronPropagator P.m ε (p' + k))
        (electronInsertion P.m ε P.δ₂ P.δm (p + k)) (QED.OneLoop.photonPropagator P.mγ P.Λ ε k) =
      ((propDenom P.m ε (p' + k))⁻¹ *
        ((propDenom P.m ε (p + k))⁻¹ * (propDenom P.m ε (p + k))⁻¹) *
          ((propDenom P.mγ ε k)⁻¹ * (propDenom P.Λ ε k)⁻¹)) • numD2In P p' p μ k := by
  rw [photonPropagator_eq_scalar _ _ hε, electronInsertion_eq_smul,
    electronPropagator_eq_smul P.m ε (p' + k), vertexChain_smul_out, vertexChain_smul_in,
    vertexChain_smul_photon, smul_smul, smul_smul]
  unfold numD2In
  congr 1

theorem isLoopPoly_numD2In (P : Params) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    IsLoopPoly 2 4 fun ℓ => numD2In P p' p μ (ℓ 0) i j := by
  have h := isLoopPolyMat_vertexChain (L := 2) (a := 1) (b := 3) (d := 0) P.e μ
    (A := fun ℓ => electronNumerator P.m (p' + ℓ 0))
    (B := fun ℓ => -(electronNumerator P.m (p + ℓ 0) * fermionCtMatrix P.δ₂ P.δm P.m (p + ℓ 0) *
      electronNumerator P.m (p + ℓ 0)))
    (D := fun _ => pvPhotonNum P.mγ P.Λ) (isLoopPolyMat_electronNumerator_add P.m p')
    (isLoopPolyMat_insertion P.m P.δ₂ P.δm p) (fun _ _ => IsLoopPoly.const _)
  exact h i j

/-- The line kinds of the product data of the `δ₂` class on the incoming line. -/
def kindsD2In : Fin 8 → LineKind := ![.out, .inn, .inn, .pho, .pho, .aux, .aux, .aux]

/-- The line masses of the product data of the `δ₂` class on the incoming line. -/
def massesD2In (P : Params) : Fin 8 → ℝ := ![P.m, P.m, P.m, P.mγ, P.Λ, P.m, P.m, P.m]

/-! ### `δ₂`, `δ_m` on the outgoing internal electron line -/

/-- The numerator of the `δ₂`, `δ_m` class on the outgoing line. -/
noncomputable def numD2Out (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) (k : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  vertexChain P.e μ
    (-(electronNumerator P.m (p' + k) * fermionCtMatrix P.δ₂ P.δm P.m (p' + k) *
      electronNumerator P.m (p' + k)))
    (electronNumerator P.m (p + k)) (pvPhotonNum P.mγ P.Λ)

theorem integrand_d2Out_eq (P : Params) {ε : ℝ} (hε : ε ≠ 0) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (k : Fin 4 → ℝ) :
    vertexChain P.e μ (electronInsertion P.m ε P.δ₂ P.δm (p' + k))
        (QED.OneLoop.electronPropagator P.m ε (p + k)) (QED.OneLoop.photonPropagator P.mγ P.Λ ε k) =
      (((propDenom P.m ε (p' + k))⁻¹ * (propDenom P.m ε (p' + k))⁻¹) *
        (propDenom P.m ε (p + k))⁻¹ *
          ((propDenom P.mγ ε k)⁻¹ * (propDenom P.Λ ε k)⁻¹)) • numD2Out P p' p μ k := by
  rw [photonPropagator_eq_scalar _ _ hε, electronInsertion_eq_smul,
    electronPropagator_eq_smul P.m ε (p + k), vertexChain_smul_out, vertexChain_smul_in,
    vertexChain_smul_photon, smul_smul, smul_smul]
  unfold numD2Out
  congr 1

theorem isLoopPoly_numD2Out (P : Params) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    IsLoopPoly 2 4 fun ℓ => numD2Out P p' p μ (ℓ 0) i j := by
  have h := isLoopPolyMat_vertexChain (L := 2) (a := 3) (b := 1) (d := 0) P.e μ
    (A := fun ℓ => -(electronNumerator P.m (p' + ℓ 0) *
      fermionCtMatrix P.δ₂ P.δm P.m (p' + ℓ 0) * electronNumerator P.m (p' + ℓ 0)))
    (B := fun ℓ => electronNumerator P.m (p + ℓ 0))
    (D := fun _ => pvPhotonNum P.mγ P.Λ) (isLoopPolyMat_insertion P.m P.δ₂ P.δm p')
    (isLoopPolyMat_electronNumerator_add P.m p) (fun _ _ => IsLoopPoly.const _)
  exact h i j

/-- The line kinds of the product data of the `δ₂` class on the outgoing line. -/
def kindsD2Out : Fin 8 → LineKind := ![.out, .out, .inn, .pho, .pho, .aux, .aux, .aux]

/-! ### `δ₃` on the internal photon -/

/-- The photon numerator of the `δ₃` insertion:
`(1/i) ∑_{a b} g_{νa} (Λ² - m_γ²) V^{ab}(k) g_{ρb} (Λ² - m_γ²)`. -/
noncomputable def photonNum (δ₃ mγ Λ : ℝ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) : ℂ :=
  (1 / I) * ∑ a, ∑ b, pvPhotonNum mγ Λ ν a * photonCtFactor δ₃ k a b * pvPhotonNum mγ Λ ρ b

theorem photonInsertion_eq_scalar (δ₃ mγ Λ : ℝ) {ε : ℝ} (hε : ε ≠ 0) (k : Fin 4 → ℝ) :
    photonInsertion δ₃ mγ Λ ε k = fun ν ρ =>
      (((propDenom mγ ε k)⁻¹ * (propDenom Λ ε k)⁻¹) *
        ((propDenom mγ ε k)⁻¹ * (propDenom Λ ε k)⁻¹)) * photonNum δ₃ mγ Λ k ν ρ := by
  funext ν ρ
  simp only [photonInsertion, photonPropagator_eq_scalar _ _ hε, photonNum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem photonCtFactor_eq (δ₃ : ℝ) (k : Fin 4 → ℝ) (a b : Fin 4) :
    photonCtFactor δ₃ k a b =
      (-(I / 2) * δ₃ * Minkowski.metric a b) * propDenom 0 0 k +
        (I / 2 * δ₃) * (((k a : ℝ) : ℂ) * ((k b : ℝ) : ℂ)) := by
  simp only [photonCtFactor, propDenom]
  push_cast
  ring

theorem isLoopPoly_photonNum (δ₃ mγ Λ : ℝ) (ν ρ : Fin 4) :
    IsLoopPoly 2 2 fun ℓ => photonNum δ₃ mγ Λ (ℓ 0) ν ρ := by
  unfold photonNum
  refine IsLoopPoly.const_mul _ (IsLoopPoly.sum _ fun a _ => IsLoopPoly.sum _ fun b _ => ?_)
  simp only [photonCtFactor_eq]
  have h1 := isLoopAffine_zero.isLoopPoly_propDenom 0 0
  have h2 := (isLoopAffine_zero.isLoopPoly_coord a).mul (isLoopAffine_zero.isLoopPoly_coord b)
  have h := (h1.const_mul (-(I / 2) * δ₃ * Minkowski.metric a b)).add
    (h2.const_mul (I / 2 * δ₃))
  have e : ∀ ℓ : Fin 2 → Fin 4 → ℝ, pvPhotonNum mγ Λ ν a *
      ((-(I / 2) * δ₃ * Minkowski.metric a b) * propDenom 0 0 (ℓ 0) +
        (I / 2 * δ₃) * (((ℓ 0 a : ℝ) : ℂ) * ((ℓ 0 b : ℝ) : ℂ))) * pvPhotonNum mγ Λ ρ b =
      (pvPhotonNum mγ Λ ν a * pvPhotonNum mγ Λ ρ b) *
        ((-(I / 2) * δ₃ * Minkowski.metric a b) * propDenom 0 0 (ℓ 0) +
          (I / 2 * δ₃) * (((ℓ 0 a : ℝ) : ℂ) * ((ℓ 0 b : ℝ) : ℂ))) := fun ℓ => by ring
  simp only [e]
  exact h.const_mul _

/-- The numerator of the `δ₃` class (either slot pairing). -/
noncomputable def numD3 (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) (k : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  vertexChain P.e μ (electronNumerator P.m (p' + k)) (electronNumerator P.m (p + k))
    (photonNum P.δ₃ P.mγ P.Λ k)

theorem integrand_d3_eq (P : Params) {ε : ℝ} (hε : ε ≠ 0) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (k : Fin 4 → ℝ) :
    vertexChain P.e μ (QED.OneLoop.electronPropagator P.m ε (p' + k))
        (QED.OneLoop.electronPropagator P.m ε (p + k)) (photonInsertion P.δ₃ P.mγ P.Λ ε k) =
      ((propDenom P.m ε (p' + k))⁻¹ * (propDenom P.m ε (p + k))⁻¹ *
        (((propDenom P.mγ ε k)⁻¹ * (propDenom P.Λ ε k)⁻¹) *
          ((propDenom P.mγ ε k)⁻¹ * (propDenom P.Λ ε k)⁻¹))) • numD3 P p' p μ k := by
  rw [photonInsertion_eq_scalar _ _ _ hε, electronPropagator_eq_smul P.m ε (p' + k),
    electronPropagator_eq_smul P.m ε (p + k), vertexChain_smul_out, vertexChain_smul_in,
    vertexChain_smul_photon, smul_smul, smul_smul]
  unfold numD3
  congr 1

theorem isLoopPoly_numD3 (P : Params) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    IsLoopPoly 2 4 fun ℓ => numD3 P p' p μ (ℓ 0) i j := by
  have h := isLoopPolyMat_vertexChain (L := 2) (a := 1) (b := 1) (d := 2) P.e μ
    (A := fun ℓ => electronNumerator P.m (p' + ℓ 0))
    (B := fun ℓ => electronNumerator P.m (p + ℓ 0))
    (D := fun ℓ => photonNum P.δ₃ P.mγ P.Λ (ℓ 0)) (isLoopPolyMat_electronNumerator_add P.m p')
    (isLoopPolyMat_electronNumerator_add P.m p) (fun ν ρ => isLoopPoly_photonNum _ _ _ ν ρ)
  exact h i j

/-- The line kinds of the product data of the `δ₃` class. -/
def kindsD3 : Fin 9 → LineKind := ![.out, .inn, .pho, .pho, .pho, .pho, .aux, .aux, .aux]

/-- The line masses of the product data of the `δ₃` class. -/
def massesD3 (P : Params) : Fin 9 → ℝ := ![P.m, P.m, P.mγ, P.Λ, P.mγ, P.Λ, P.m, P.m, P.m]

/-! ### The common argument -/

theorem prod_lineDenom_kinds {m : ℕ} (κ : Fin (m + 1) → LineKind) (Ms : Fin (m + 1) → ℝ)
    (p p' : Fin 4 → ℝ) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∏ i, (lineDenom (castLoopMatrix fun i => (κ i).dir) (fun i => (κ i).mom p p') Ms ε i ℓ)⁻¹ =
      ∏ i, (propDenom (Ms i) ε ((κ i).lineMom p p' ℓ))⁻¹ := by
  simp only [lineDenom_eq_propDenom, lineMomentum_kinds]

/-- The bound `μ = min(m_γ, Λ)` for the photon masses. -/
theorem sq_min_le (P : Params) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    min P.mγ P.Λ ^ 2 ≤ P.mγ ^ 2 ∧ min P.mγ P.Λ ^ 2 ≤ P.Λ ^ 2 :=
  ⟨pow_le_pow_left₀ (lt_min hmγ hΛ).le (min_le_left _ _) 2,
    pow_le_pow_left₀ (lt_min hmγ hΛ).le (min_le_right _ _) 2⟩

/-- **The one-loop limit for product data given by kinds**: the hypotheses of
`exists_tendsto_energyFirstIntegral_of_product` with the line data of `κ`, the numerator lines
`E = {0, 1, 2, 3}` and the positivity from `symanzikV_kinds_ge`. -/
theorem exists_tendsto_of_kinds {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind)
    (Ms : Fin (m + 1) → ℝ) {mass μ : ℝ} (hmass : 0 < mass) (hμ : 0 < μ) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hMe : ∀ i, κ i ≠ .pho → Ms i ^ 2 = mass ^ 2) (hMp : ∀ i, κ i = .pho → μ ^ 2 ≤ Ms i ^ 2)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (κ i).dir)
    (hcard : ({0, 1, 2, 3} : Finset (Fin (m + 1))).card = 4)
    (hE : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (m + 1))), κ e ≠ .aux)
    (N : (Fin 4 → ℝ) → ℂ) (hN : IsLoopPoly 2 4 fun ℓ => N (ℓ 0)) (F : ℝ → (Fin 4 → ℝ) → ℂ)
    (hfac : ∀ ε : ℝ, 0 < ε → ∀ ℓ : Fin 2 → Fin 4 → ℝ,
      N (ℓ 0) * ∏ i, (propDenom (Ms i) ε ((κ i).lineMom p p' ℓ))⁻¹ =
        F ε (ℓ 0) * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3) :
    ∃ L : ℂ, Tendsto (fun ε => QED.OneLoop.energyFirstIntegral (F ε)) (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨Q, hQ⟩ := hN.exists_loopQuartic
  have hα : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (m + 1))),
      (castLoopMatrix fun i => (κ i).dir) e = ![1, 0] := by
    intro e he
    have h := hE e he
    funext s
    rcases hk : κ e with _ | _ | _ | _
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · exact absurd hk h
  have hB : RefinedBound (castLoopMatrix fun i => (κ i).dir) {0, 1, 2, 3} 4 Q.eval :=
    refinedBound_of_dependsOnZero _ hcard hα Q fun ℓ => by simp only [hQ, Matrix.cons_val_zero]
  have hc : 0 < 3 / 4 * min (mass ^ 2) (μ ^ 2) := by positivity
  exact exists_tendsto_energyFirstIntegral_of_product hm7 _ _ Ms Q
    ((noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit) hB hc
    (fun z hz hz1 hU => symanzikV_kinds_ge κ Ms hp hp' hq hMe hMp hz hz1 hU) hmass F
    fun ε hε ℓ => by rw [hQ, prod_lineDenom_kinds]; exact hfac ε hε ℓ

/-! ### The limits of the counterterm classes -/

section Limits

variable (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
  {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
  (hp : Minkowski.dot (pIn 0) (pIn 0) = -P.m ^ 2)
  (hp' : Minkowski.dot (pOut 0) (pOut 0) = -P.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (pOut 0 - pIn 0) (pOut 0 - pIn 0)) (αOut βIn μ : Fin 1 → Fin 4)
include hm hmγ hΛ hmom hp hp' hq

/-- **The `δ₂`, `δ_m` class on the incoming line has an `ε → 0⁺` limit.** -/
theorem exists_tendsto_contractionValue₂_d2In :
    ∃ L : ℂ, Tendsto (fun ε => contractionValue₂ { P with ε := ε } repD2In pOut pIn kIn αOut βIn μ)
      (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨h1, h2⟩ := sq_min_le P hmγ hΛ
  obtain ⟨L, hL⟩ := exists_tendsto_of_kinds (by norm_num) kindsD2In (massesD2In P) hm
    (lt_min hmγ hΛ) hp hp' hq
    (fun i hi => by fin_cases i <;> simp_all [kindsD2In, massesD2In])
    (fun i hi => by fin_cases i <;> simp_all [kindsD2In, massesD2In])
    (by decide) (by decide) (by decide)
    (fun k => numD2In P (pOut 0) (pIn 0) (μ 0) k (αOut 0) (βIn 0))
    (isLoopPoly_numD2In P _ _ _ _ _)
    (fun ε k => vertexChain P.e (μ 0) (QED.OneLoop.electronPropagator P.m ε (pOut 0 + k))
      (electronInsertion P.m ε P.δ₂ P.δm (pIn 0 + k))
      (QED.OneLoop.photonPropagator P.mγ P.Λ ε k) (αOut 0) (βIn 0))
    (fun ε hε ℓ => by
      rw [integrand_d2In_eq P hε.ne', Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsD2In, massesD2In,
        LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring)
  exact ⟨L, hL.congr' (Eventually.of_forall fun ε =>
    (contractionValue₂_repD2In { P with ε := ε } hmom αOut βIn μ).symm)⟩

/-- **The `δ₂`, `δ_m` class on the outgoing line has an `ε → 0⁺` limit.** -/
theorem exists_tendsto_contractionValue₂_d2Out :
    ∃ L : ℂ, Tendsto
      (fun ε => contractionValue₂ { P with ε := ε } repD2Out pOut pIn kIn αOut βIn μ)
      (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨h1, h2⟩ := sq_min_le P hmγ hΛ
  obtain ⟨L, hL⟩ := exists_tendsto_of_kinds (by norm_num) kindsD2Out (massesD2In P) hm
    (lt_min hmγ hΛ) hp hp' hq
    (fun i hi => by fin_cases i <;> simp_all [kindsD2Out, massesD2In])
    (fun i hi => by fin_cases i <;> simp_all [kindsD2Out, massesD2In])
    (by decide) (by decide) (by decide)
    (fun k => numD2Out P (pOut 0) (pIn 0) (μ 0) k (αOut 0) (βIn 0))
    (isLoopPoly_numD2Out P _ _ _ _ _)
    (fun ε k => vertexChain P.e (μ 0) (electronInsertion P.m ε P.δ₂ P.δm (pOut 0 + k))
      (QED.OneLoop.electronPropagator P.m ε (pIn 0 + k))
      (QED.OneLoop.photonPropagator P.mγ P.Λ ε k) (αOut 0) (βIn 0))
    (fun ε hε ℓ => by
      rw [integrand_d2Out_eq P hε.ne', Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsD2Out, massesD2In,
        LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring)
  exact ⟨L, hL.congr' (Eventually.of_forall fun ε =>
    (contractionValue₂_repD2Out { P with ε := ε } hmom αOut βIn μ).symm)⟩

/-- **The `δ₃` class, slot `0` towards `v₁`, has an `ε → 0⁺` limit.** -/
theorem exists_tendsto_contractionValue₂_d3Slot0 :
    ∃ L : ℂ, Tendsto
      (fun ε => contractionValue₂ { P with ε := ε } repD3Slot0 pOut pIn kIn αOut βIn μ)
      (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨h1, h2⟩ := sq_min_le P hmγ hΛ
  obtain ⟨L, hL⟩ := exists_tendsto_of_kinds (by norm_num) kindsD3 (massesD3 P) hm
    (lt_min hmγ hΛ) hp hp' hq
    (fun i hi => by fin_cases i <;> simp_all [kindsD3, massesD3])
    (fun i hi => by fin_cases i <;> simp_all [kindsD3, massesD3])
    (by decide) (by decide) (by decide)
    (fun k => numD3 P (pOut 0) (pIn 0) (μ 0) k (αOut 0) (βIn 0))
    (isLoopPoly_numD3 P _ _ _ _ _)
    (fun ε k => vertexChain P.e (μ 0) (QED.OneLoop.electronPropagator P.m ε (pOut 0 + k))
      (QED.OneLoop.electronPropagator P.m ε (pIn 0 + k))
      (photonInsertion P.δ₃ P.mγ P.Λ ε k) (αOut 0) (βIn 0))
    (fun ε hε ℓ => by
      rw [integrand_d3_eq P hε.ne', Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsD3, massesD3,
        LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring)
  exact ⟨L, hL.congr' (Eventually.of_forall fun ε =>
    (contractionValue₂_repD3Slot0 { P with ε := ε } hmom αOut βIn μ).symm)⟩

/-- **The `δ₃` class, slot `1` towards `v₁`, has an `ε → 0⁺` limit** (the same value as slot
`0`, `contractionValue₂_d3Slot0_eq_d3Slot1`). -/
theorem exists_tendsto_contractionValue₂_d3Slot1 :
    ∃ L : ℂ, Tendsto
      (fun ε => contractionValue₂ { P with ε := ε } repD3Slot1 pOut pIn kIn αOut βIn μ)
      (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨L, hL⟩ := exists_tendsto_contractionValue₂_d3Slot0 P hm hmγ hΛ hmom hp hp' hq αOut βIn μ
  exact ⟨L, hL.congr' (Eventually.of_forall fun ε =>
    contractionValue₂_d3Slot0_eq_d3Slot1 { P with ε := ε } hmom αOut βIn μ)⟩

end Limits

section LimitsD1

variable (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
  {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
  (hp : Minkowski.dot (pIn 0) (pIn 0) = -P.m ^ 2)
  (hp' : Minkowski.dot (pOut 0) (pOut 0) = -P.m ^ 2) (hp0 : 0 < pIn 0 0) (hp0' : 0 < pOut 0 0)
  (αOut βIn μ : Fin 1 → Fin 4)
include hm hmγ hΛ hmom hp hp' hp0 hp0'

omit hmom in
/-- The one-loop vertex value at prescription `ε` converges (packet 1's (E), helper level). -/
theorem tendsto_vertexValue :
    Tendsto (fun ε => vertexValue { P with ε := ε } (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0))
      (𝓝[>] 0) (𝓝 (∫ v, QED.OneLoop.VertexLimit.spatialG P.e P.m P.mγ P.Λ 0 (pOut 0) (pIn 0)
        (μ 0) (αOut 0) (βIn 0) v)) :=
  QED.OneLoop.VertexLimit.tendsto_energyFirstIntegral_vertexIntegrand hm hmγ hΛ hp' hp hp0' hp0
    (μ 0) (αOut 0) (βIn 0)

/-- **The `δ₁` class at `v₁` has an `ε → 0⁺` limit.** -/
theorem exists_tendsto_contractionValue₂_d1At1 :
    ∃ L : ℂ, Tendsto
      (fun ε => contractionValue₂ { P with ε := ε } repD1At1 pOut pIn kIn αOut βIn μ)
      (𝓝[>] 0) (𝓝 L) :=
  ⟨_, ((tendsto_vertexValue P hm hmγ hΛ hp hp' hp0 hp0' αOut βIn μ).const_mul
    (P.δ₁ : ℂ)).congr' (Eventually.of_forall fun ε =>
      (contractionValue₂_d1At1 { P with ε := ε } hmom αOut βIn μ).symm)⟩

/-- **The `δ₁` class at `v₂` has an `ε → 0⁺` limit.** -/
theorem exists_tendsto_contractionValue₂_d1At2 :
    ∃ L : ℂ, Tendsto
      (fun ε => contractionValue₂ { P with ε := ε } repD1At2 pOut pIn kIn αOut βIn μ)
      (𝓝[>] 0) (𝓝 L) :=
  ⟨_, ((tendsto_vertexValue P hm hmγ hΛ hp hp' hp0 hp0' αOut βIn μ).const_mul
    (P.δ₁ : ℂ)).congr' (Eventually.of_forall fun ε =>
      (contractionValue₂_d1At2 { P with ε := ε } hmom αOut βIn μ).symm)⟩

/-- **The `δ₁` class at `v₃` has an `ε → 0⁺` limit.** -/
theorem exists_tendsto_contractionValue₂_d1At3 :
    ∃ L : ℂ, Tendsto
      (fun ε => contractionValue₂ { P with ε := ε } repD1At3 pOut pIn kIn αOut βIn μ)
      (𝓝[>] 0) (𝓝 L) :=
  ⟨_, ((tendsto_vertexValue P hm hmγ hΛ hp hp' hp0 hp0' αOut βIn μ).const_mul
    (P.δ₁ : ℂ)).congr' (Eventually.of_forall fun ε =>
      (contractionValue₂_d1At3 { P with ε := ε } hmom αOut βIn μ).symm)⟩

end LimitsD1

/-- **Every counterterm class value has an `ε → 0⁺` limit**, for `m, m_γ, Λ > 0`, on-shell
positive-energy `p = pIn 0`, `p' = pOut 0` with `(p' - p)² ≥ 0`, momentum conservation, every
choice of indices and every value of the counterterms. -/
theorem exists_tendsto_contractionValue₂_ctClass (c : CtClass) (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (hp : Minkowski.dot (pIn 0) (pIn 0) = -P.m ^ 2)
    (hp' : Minkowski.dot (pOut 0) (pOut 0) = -P.m ^ 2) (hp0 : 0 < pIn 0 0) (hp0' : 0 < pOut 0 0)
    (hq : 0 ≤ Minkowski.dot (pOut 0 - pIn 0) (pOut 0 - pIn 0)) (αOut βIn μ : Fin 1 → Fin 4) :
    ∃ L : ℂ, Tendsto (fun ε => contractionValue₂ { P with ε := ε } c.rep pOut pIn kIn αOut βIn μ)
      (𝓝[>] 0) (𝓝 L) := by
  cases c
  · exact exists_tendsto_contractionValue₂_d2In P hm hmγ hΛ hmom hp hp' hq αOut βIn μ
  · exact exists_tendsto_contractionValue₂_d2Out P hm hmγ hΛ hmom hp hp' hq αOut βIn μ
  · exact exists_tendsto_contractionValue₂_d3Slot0 P hm hmγ hΛ hmom hp hp' hq αOut βIn μ
  · exact exists_tendsto_contractionValue₂_d3Slot1 P hm hmγ hΛ hmom hp hp' hq αOut βIn μ
  · exact exists_tendsto_contractionValue₂_d1At1 P hm hmγ hΛ hmom hp hp' hp0 hp0' αOut βIn μ
  · exact exists_tendsto_contractionValue₂_d1At2 P hm hmγ hΛ hmom hp hp' hp0 hp0' αOut βIn μ
  · exact exists_tendsto_contractionValue₂_d1At3 P hm hmγ hΛ hmom hp hp' hp0 hp0' αOut βIn μ

end QED.TwoLoop.CountertermLimit

end
