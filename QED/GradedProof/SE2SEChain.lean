/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.IntegrableOrderFiveCt
public import QED.WickModel.ThreePointClassification
public import QED.WickModel.SelfEnergyExistsUnique

/-!
# One-loop self-energy integrands with a counterterm insertion

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), step 2. The classes `F` (the `fermionCt` vertex on the internal electron line)
and `P0`, `P1` (the `photonCt` vertex on the internal photon line) of
`QED/GradedProof/SE2Classes.lean` are one-loop self-energy graphs with an inserted line. In the
self-energy chain `seChain A D = ∑_{νρ} D_{νρ} γ^ρ A γ^ν` (so that the integrand (62.28) is
`selfEnergyIntegrand = κ • seChain S̃ Δ̃`, `selfEnergyIntegrand_eq_seChain`):

* **`δ₃` insertion** (`energyFirst_seP`): `seChain S̃(p + k) (photonInsertion k)` is a numerator
  of degree three over one electron and four photon denominators. With an auxiliary loop of three
  lines these are eight lines, and both stages of the energy-first integral (D) converge at every
  `ε > 0` by `QED.TwoLoop.IntegrableOrderFive.energyFirst_of_kinds` (line kinds `kindsSEP`).
* **`δ₂`, `δ_m` insertion** (`energyFirst_seF`): the inserted electron line
  `-S̃ (δ₂ k̸ + δ_m m) S̃` has a numerator of degree three over only four denominators. The
  identity `k̸ k̸ = -k²` reduces it (`electronInsertion_decomp`) to
  `-δ₂ S̃_m - (δ₂ - δ_m)/2 (S̃_m - S̃_{-m}) - D⁻² R` with `R` of degree one: the first two terms
  are self-energy integrands at the masses `±m`, integrable at every `ε > 0` and every `p` by
  `QED.WickModel.SelfEnergyLimit.integrable_selfEnergyIntegrand_sub`; the last, written as
  `D⁻³ (D R)`, has eight lines with the auxiliary loop (line kinds `kindsSEF`).
-/

@[expose] public section

namespace QED.GradedProof.SE2

open QED.WickModel QED.TwoLoop.Insertion QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.IntegrableOrderFive
open Complex MeasureTheory

/-! ### Integrability in both stages -/

theorem IntegrableEnergyFirst.add {F G : (Fin 4 → ℝ) → ℂ} (hF : IntegrableEnergyFirst F)
    (hG : IntegrableEnergyFirst G) : IntegrableEnergyFirst fun ℓ => F ℓ + G ℓ := by
  refine ⟨fun v => (hF.1 v).add (hG.1 v), ?_⟩
  have h : ∀ v : Fin 3 → ℝ, ∫ t : ℝ, (F (Fin.cons t v) + G (Fin.cons t v)) =
      (∫ t : ℝ, F (Fin.cons t v)) + ∫ t : ℝ, G (Fin.cons t v) := fun v =>
    integral_add (hF.1 v) (hG.1 v)
  simp_rw [h]
  exact hF.2.add hG.2

theorem IntegrableEnergyFirst.congr {F G : (Fin 4 → ℝ) → ℂ} (hF : IntegrableEnergyFirst F)
    (h : ∀ ℓ, F ℓ = G ℓ) : IntegrableEnergyFirst G := by
  have : F = G := funext h
  exact this ▸ hF

/-- The one-loop self-energy integrand is integrable in both stages, at every `ε > 0`. -/
theorem integrableEnergyFirst_selfEnergyIntegrand (P : Params) {ε : ℝ} (hε : 0 < ε)
    (p : Fin 4 → ℝ) (i j : Fin 4) :
    IntegrableEnergyFirst fun q => selfEnergyIntegrand P ε p q i j := by
  obtain ⟨h1, h2⟩ := SelfEnergyLimit.integrable_selfEnergyIntegrand_sub hε P p 0 i j
  simp only [sub_zero] at h1 h2
  exact ⟨h1, h2⟩

/-! ### The self-energy chain -/

/-- The self-energy chain `∑_{νρ} D_{νρ} γ^ρ A γ^ν`. -/
noncomputable def seChain (A : Matrix (Fin 4) (Fin 4) ℂ) (D : Fin 4 → Fin 4 → ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ ν, ∑ ρ, D ν ρ • (Dirac.gamma ρ * A * Dirac.gamma ν)

theorem seChain_smul_in (c : ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) (D : Fin 4 → Fin 4 → ℂ) :
    seChain (c • A) D = c • seChain A D := by
  simp only [seChain, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, smul_smul, mul_comm]

theorem seChain_smul_photon (c : ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) (D : Fin 4 → Fin 4 → ℂ) :
    seChain A (fun ν ρ => c * D ν ρ) = c • seChain A D := by
  simp only [seChain, Finset.smul_sum, smul_smul]

theorem seChain_add_in (A B : Matrix (Fin 4) (Fin 4) ℂ) (D : Fin 4 → Fin 4 → ℂ) :
    seChain (A + B) D = seChain A D + seChain B D := by
  simp only [seChain, Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib]

theorem seChain_sub_in (A B : Matrix (Fin 4) (Fin 4) ℂ) (D : Fin 4 → Fin 4 → ℂ) :
    seChain (A - B) D = seChain A D - seChain B D := by
  simp only [seChain, Matrix.mul_sub, Matrix.sub_mul, smul_sub, Finset.sum_sub_distrib]

/-- The integrand (62.28) as a self-energy chain. -/
theorem selfEnergyIntegrand_eq_seChain (P : Params) (ε : ℝ) (p q : Fin 4 → ℝ) :
    selfEnergyIntegrand P ε p q =
      ((I * P.e) ^ 2 * (1 / I) ^ 2 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹) •
        seChain (QED.OneLoop.electronPropagator P.m ε (p + q))
          (QED.OneLoop.photonPropagator P.mγ P.Λ ε q) :=
  rfl

theorem isLoopPolyMat_seChain {L a d : ℕ} {A : (Fin L → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    {D : (Fin L → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} (hA : IsLoopPolyMat L a A)
    (hD : ∀ ν ρ, IsLoopPoly L d fun ℓ => D ℓ ν ρ) :
    IsLoopPolyMat L (d + a) fun ℓ => seChain (A ℓ) (D ℓ) := by
  intro i j
  unfold seChain
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine IsLoopPoly.sum _ fun ν _ => IsLoopPoly.sum _ fun ρ _ => ?_
  have h := ((IsLoopPolyMat.const (L := L) (Dirac.gamma ρ)).mul hA).mul
    (IsLoopPolyMat.const (Dirac.gamma ν))
  exact (hD ν ρ).mul ((h i j).mono (by omega))

/-! ### `δ₃` on the internal photon line -/

/-- The numerator of the self-energy with the `δ₃` insertion. -/
noncomputable def numSEP (P : Params) (p k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  seChain (electronNumerator P.m (p + k)) (photonNum P.δ₃ P.mγ P.Λ k)

theorem integrand_seP_eq (P : Params) {ε : ℝ} (hε : ε ≠ 0) (p k : Fin 4 → ℝ) :
    seChain (QED.OneLoop.electronPropagator P.m ε (p + k)) (photonInsertion P.δ₃ P.mγ P.Λ ε k) =
      ((propDenom P.m ε (p + k))⁻¹ *
        (((propDenom P.mγ ε k)⁻¹ * (propDenom P.Λ ε k)⁻¹) *
          ((propDenom P.mγ ε k)⁻¹ * (propDenom P.Λ ε k)⁻¹))) • numSEP P p k := by
  rw [photonInsertion_eq_scalar _ _ _ hε,
    QED.TwoLoop.Bridge.electronPropagator_eq_smul, seChain_smul_in,
    seChain_smul_photon, smul_smul]
  rfl

theorem isLoopPoly_numSEP (P : Params) (p : Fin 4 → ℝ) (i j : Fin 4) :
    IsLoopPoly 2 4 fun ℓ => numSEP P p (ℓ 0) i j :=
  ((isLoopPolyMat_seChain (a := 1) (d := 2) (isLoopPolyMat_electronNumerator_add P.m p)
    (fun ν ρ => isLoopPoly_photonNum P.δ₃ P.mγ P.Λ ν ρ)) i j).mono (by norm_num)

/-- The line kinds of the product data of the self-energy with the `δ₃` insertion. -/
def kindsSEP : Fin 8 → LineKind := ![.inn, .pho, .pho, .pho, .pho, .aux, .aux, .aux]

/-- The line masses of the product data of the self-energy with the `δ₃` insertion. -/
def massesSEP (P : Params) : Fin 8 → ℝ := ![P.m, P.mγ, P.Λ, P.mγ, P.Λ, P.m, P.m, P.m]

/-- **Both stages for the self-energy with the `δ₃` insertion**, at every `ε > 0`. -/
theorem energyFirst_seP (P : Params) (hε : 0 < P.ε) (p : Fin 4 → ℝ) (i j : Fin 4) :
    IntegrableEnergyFirst fun k =>
      seChain (QED.OneLoop.electronPropagator P.m P.ε (p + k))
        (photonInsertion P.δ₃ P.mγ P.Λ P.ε k) i j :=
  energyFirst_of_kinds (by norm_num) kindsSEP (massesSEP P) P.m hε p p
    (by decide) (by decide) (by decide)
    (fun k => numSEP P p k i j) (isLoopPoly_numSEP P p i j)
    (fun k => seChain (QED.OneLoop.electronPropagator P.m P.ε (p + k))
        (photonInsertion P.δ₃ P.mγ P.Λ P.ε k) i j)
    (fun ℓ => by
      rw [integrand_seP_eq P hε.ne', Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsSEP, massesSEP,
        LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring)

/-! ### `δ₂`, `δ_m` on the internal electron line -/

/-- The degree-one remainder `R` of the reduced electron insertion. -/
noncomputable def insR (m ε δ₂ δm : ℝ) (k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((ε : ℂ) * I * δ₂ + 2 * (m : ℂ) ^ 2 * (δm - δ₂)) • electronNumerator m k +
    ((ε : ℂ) * I * m * (δ₂ - δm)) • (1 : Matrix (Fin 4) (Fin 4) ℂ)

theorem propDenom_neg_mass (m ε : ℝ) (k : Fin 4 → ℝ) : propDenom (-m) ε k = propDenom m ε k := by
  simp [propDenom]

/-- **The reduced electron insertion**: with `k̸ k̸ = -k²`,
`-S̃ (δ₂ k̸ + δ_m m) S̃ = -δ₂ S̃_m - (δ₂ - δ_m)/2 (S̃_m - S̃_{-m}) - D⁻² R`. -/
theorem electronInsertion_decomp (m ε δ₂ δm : ℝ) (hε : ε ≠ 0) (k : Fin 4 → ℝ) :
    electronInsertion m ε δ₂ δm k =
      (-(δ₂ : ℂ)) • QED.OneLoop.electronPropagator m ε k
        - (((δ₂ - δm) / 2 : ℝ) : ℂ) • (QED.OneLoop.electronPropagator m ε k -
            QED.OneLoop.electronPropagator (-m) ε k)
        - ((propDenom m ε k)⁻¹ * (propDenom m ε k)⁻¹) • insR m ε δ₂ δm k := by
  have hD := propDenom_ne_zero (M := m) hε k
  have hss := Dirac.slash_mul_slash k
  rw [electronInsertion_eq_smul, QED.TwoLoop.Bridge.electronPropagator_eq_smul m,
    QED.TwoLoop.Bridge.electronPropagator_eq_smul (-m), propDenom_neg_mass]
  simp only [insR, electronNumerator, fermionCtMatrix, sub_mul, mul_sub, add_mul, mul_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hss, smul_smul]
  set u := (propDenom m ε k)⁻¹ with hu
  set dk : ℂ := ((Minkowski.dot k k : ℝ) : ℂ) with hdk
  have hDu : u * (dk + (m : ℂ) ^ 2 - (ε : ℂ) * I) = 1 := by
    rw [hu, hdk, ← mul_inv_cancel₀ hD, mul_comm]
    simp [propDenom]
  have h1 : -(u * u * (2 * m * δ₂ * dk + δm * m * (m ^ 2 - dk))) =
      -(δ₂ * u * m) - (δ₂ - δm) / 2 * u * (2 * m) -
        u * u * ((ε * I * δ₂ + 2 * m ^ 2 * (δm - δ₂)) * m + ε * I * m * (δ₂ - δm)) := by
    linear_combination (-(m : ℂ) * (2 * δ₂ - δm) * u) * hDu
  have h2 : -(u * u * (δ₂ * (m ^ 2 - dk) - 2 * m ^ 2 * δm)) =
      δ₂ * u + u * u * (ε * I * δ₂ + 2 * m ^ 2 * (δm - δ₂)) := by
    linear_combination ((δ₂ : ℂ) * u) * hDu
  push_cast
  linear_combination (norm := module) h1 • (1 : Matrix (Fin 4) (Fin 4) ℂ) + h2 • Dirac.slash k

theorem isLoopPolyMat_insR (m ε δ₂ δm : ℝ) (p : Fin 4 → ℝ) :
    IsLoopPolyMat 2 1 fun ℓ => insR m ε δ₂ δm (p + ℓ 0) :=
  isLoopPolyMat_add (isLoopPolyMat_smul _ (isLoopPolyMat_electronNumerator_add m p))
    (isLoopPolyMat_mono (isLoopPolyMat_smul _
      (IsLoopPolyMat.const (1 : Matrix (Fin 4) (Fin 4) ℂ))) (Nat.zero_le _))

/-- The numerator of the remainder of the self-energy with the `δ₂`, `δ_m` insertion. -/
noncomputable def numSEF (P : Params) (p k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  seChain (propDenom P.m P.ε (p + k) • insR P.m P.ε P.δ₂ P.δm (p + k)) (pvPhotonNum P.mγ P.Λ)

theorem integrand_seF_eq (P : Params) (hε : P.ε ≠ 0) (p k : Fin 4 → ℝ) :
    seChain (((propDenom P.m P.ε (p + k))⁻¹ * (propDenom P.m P.ε (p + k))⁻¹) •
        insR P.m P.ε P.δ₂ P.δm (p + k)) (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k) =
      ((propDenom P.m P.ε (p + k))⁻¹ * (propDenom P.m P.ε (p + k))⁻¹ *
          (propDenom P.m P.ε (p + k))⁻¹ * ((propDenom P.mγ P.ε k)⁻¹ * (propDenom P.Λ P.ε k)⁻¹)) •
        numSEF P p k := by
  have hD := propDenom_ne_zero (M := P.m) hε (p + k)
  rw [photonPropagator_eq_scalar _ _ hε, seChain_smul_photon, seChain_smul_in, numSEF,
    seChain_smul_in, smul_smul, smul_smul]
  congr 1
  field_simp

theorem isLoopPoly_numSEF (P : Params) (p : Fin 4 → ℝ) (i j : Fin 4) :
    IsLoopPoly 2 4 fun ℓ => numSEF P p (ℓ 0) i j := by
  have hA : IsLoopPolyMat 2 3 fun ℓ =>
      propDenom P.m P.ε (p + ℓ 0) • insR P.m P.ε P.δ₂ P.δm (p + ℓ 0) := fun a b => by
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact ((isLoopAffine_add_zero p).isLoopPoly_propDenom P.m P.ε).mul
      (isLoopPolyMat_insR P.m P.ε P.δ₂ P.δm p a b)
  exact ((isLoopPolyMat_seChain (d := 0) hA
    (fun ν ρ => IsLoopPoly.const (pvPhotonNum P.mγ P.Λ ν ρ))) i j).mono (by norm_num)

/-- The line kinds of the product data of the remainder term. -/
def kindsSEF : Fin 8 → LineKind := ![.inn, .inn, .inn, .pho, .pho, .aux, .aux, .aux]

/-- The line masses of the product data of the remainder term. -/
def massesSEF (P : Params) : Fin 8 → ℝ := ![P.m, P.m, P.m, P.mγ, P.Λ, P.m, P.m, P.m]

/-- Both stages for the remainder term of the self-energy with the `δ₂`, `δ_m` insertion. -/
theorem energyFirst_seFrem (P : Params) (hε : 0 < P.ε) (p : Fin 4 → ℝ) (i j : Fin 4) :
    IntegrableEnergyFirst fun k =>
      seChain (((propDenom P.m P.ε (p + k))⁻¹ * (propDenom P.m P.ε (p + k))⁻¹) •
        insR P.m P.ε P.δ₂ P.δm (p + k)) (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k) i j :=
  energyFirst_of_kinds (by norm_num) kindsSEF (massesSEF P) P.m hε p p
    (by decide) (by decide) (by decide)
    (fun k => numSEF P p k i j) (isLoopPoly_numSEF P p i j)
    (fun k => seChain (((propDenom P.m P.ε (p + k))⁻¹ * (propDenom P.m P.ε (p + k))⁻¹) •
        insR P.m P.ε P.δ₂ P.δm (p + k)) (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k) i j)
    (fun ℓ => by
      rw [integrand_seF_eq P hε.ne', Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsSEF, massesSEF,
        LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring)

/-- **Both stages for the self-energy with the `δ₂`, `δ_m` insertion**, at every `ε > 0` and
every `p`: `κ` times the chain of the inserted electron line with the photon propagator. -/
theorem energyFirst_seF (P : Params) (hε : 0 < P.ε) (p : Fin 4 → ℝ) (i j : Fin 4) :
    IntegrableEnergyFirst fun q =>
      ((I * P.e) ^ 2 * (1 / I) ^ 2 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹) *
        seChain (electronInsertion P.m P.ε P.δ₂ P.δm (p + q))
          (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε q) i j := by
  have hS := integrableEnergyFirst_selfEnergyIntegrand P hε p i j
  have hS' := integrableEnergyFirst_selfEnergyIntegrand { P with m := -P.m } hε p i j
  have hR := energyFirst_seFrem P hε p i j
  set c : ℂ := (((P.δ₂ - P.δm) / 2 : ℝ) : ℂ)
  set κ : ℂ := (I * P.e) ^ 2 * (1 / I) ^ 2 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹
  refine IntegrableEnergyFirst.congr (IntegrableEnergyFirst.add
    (hS.const_mul (-(P.δ₂ : ℂ) - c))
    (IntegrableEnergyFirst.add (hS'.const_mul c) (hR.const_mul (-κ)))) fun q => ?_
  rw [electronInsertion_decomp _ _ _ _ hε.ne', selfEnergyIntegrand_eq_seChain,
    selfEnergyIntegrand_eq_seChain]
  simp only [seChain_sub_in, seChain_smul_in, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end QED.GradedProof.SE2

end
