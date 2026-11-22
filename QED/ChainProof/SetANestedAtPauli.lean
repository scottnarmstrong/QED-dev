/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAPauliLink
public import QED.ChainProof.SetASpecUStar
public import QED.ChainProof.SetASpecOuterTerm
public import QED.ChainProof.SetANestP
public import QED.ChainProof.HCBB2Pauli
public import QED.GradedProof.RPi4Setup

/-!
# The Pauli projection of the set (a) limits, from the nested form

Helper level for `QED.ChainProof.SetAPauli.SetANestedAt` (the nested value of the set (a)
limits). The nested form at fixed `ε` (`SetANestForm`, the conclusion of
`QED.ChainProof.SetANest.familyVertex_setA_eq_nested` at every admissible regulator set, which
is obligation (N) of `SetALimitLink` and is **not** proved here) writes each entry of the set (a)
family vertex as `(1/i)` times the energy-first integral of the one-loop vertex chain with the
photon factor `Δ Π⁽⁴⁾_ε Δ`. With the `ε`-uniform spectral form `T★ᵤ`
(`QED.ChainProof.SetASpec.setASpecU_vacuumPolarizationPart_two`, proved), this file computes the
Pauli numerator of every `ε → 0⁺` limit:

* `pauliNum_outerPhoton`: pointwise in the loop momentum, the Pauli numerator of the outer
  integrand of one spectral term is `(Λ² - m_γ²)²` times the engine integrand with the
  Pauli-projected chain `pauliChain` for a `g` term, and `0` for a `k k` term (the longitudinal
  part drops out exactly, `QED.TwoLoop.VPUnitNested.pauliNum_longitudinal`);
* `pauliNum_nestPhoton_list`: the same for a list of terms;
* `regFlavors_spec`: `T★ᵤ` at the flavours of (HA₆);
* `pauliNum_familyVertex_eq`: at `ε ∈ (0, 1]`, the Pauli numerator of the family vertex is
  `(1/i)` times a finite combination of the engine values `SALimTerm.val`;
* **`exists_pauliNum_setALim`**: under `SetANestForm`, one list `L` of spectral terms (the
  `T★ᵤ` list, independent of the external momenta) gives, at every on-shell positive-energy
  pair with `q² > 0`, `pauliNum V = (1/i) setAPauliLim L` for every limit `V`, where
  `setAPauliLim` is an explicit combination of the engine limits `SALimTerm.lim` of `pauliChain`
  over the photon-type masses `(m_γ, Λ, m_γ, Λ)` and the spectral factors of the `g` terms.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real
open QED.WickModel (Params IsOnePI)

namespace QED.ChainProof.SetANestedAt

open QED.OneLoop QED.TwoLoop.VPUnitNested QED.TwoLoop.VPHalfAtGen QED.TwoLoop.VPHalfAtLimit
open QED.TwoLoop.PauliZeroLimit QED.TwoLoop.Insertion QED.TwoLoop.VPHalfAtAssembly
open QED.TwoLoop.Bridge QED.ChainProof.HCBB2 QED.ChainProof.SetASpec QED.ChainProof.SetANest
open QED.ChainProof.SetAPauli
open QED.Integration.Feynman (simplexSet)

/-! ### Linearity of the Pauli numerator -/

theorem pauliNum_smul' (m : ℝ) (p' p : Fin 4 → ℝ) (c : ℂ)
    (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    pauliNum m p' p (fun μ => c • V μ) = c * pauliNum m p' p V := by
  simp only [pauliNum_eq_sum, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

/-! ### One spectral term -/

/-- The Pauli factor of a term: `(Λ² - m_γ²)²` for a `g` term, `0` for a `k k` term. -/
noncomputable def termCoef (mγ Λ : ℝ) (τ : SAOuterTerm) : ℂ :=
  if τ.t then 0 else (((Λ ^ 2 - mγ ^ 2) ^ 2 : ℝ) : ℂ)

/-- The Pauli-projected outer integrand of a term. -/
noncomputable def termPauli (e m mγ Λ : ℝ) (p' p : Fin 4 → ℝ) (τ : SAOuterTerm) (ε : ℝ)
    (ℓ : Fin 4 → ℝ) : ℂ :=
  termCoef mγ Λ τ * saLimTermInt (pauliChain e m p' p) m τ.j (saMs4 mγ Λ) τ.r τ.A τ.ξ (τ.w ε)
    ε p' p ℓ

/-- **The Pauli numerator of the outer integrand of one term**, pointwise at `ε > 0`. -/
theorem pauliNum_outerPhoton {e m : ℝ} (mγ Λ : ℝ) (hm : m ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) {ε : ℝ} (hε : 0 < ε) (τ : SAOuterTerm)
    (ℓ : Fin 4 → ℝ) :
    pauliNum m p' p (fun μ => vertexChain e μ (electronPropagator m ε (p' + ℓ))
      (electronPropagator m ε (p + ℓ)) (saOuterPhoton mγ Λ τ.t τ.j τ.r τ.A τ.ξ (τ.w ε) ε ℓ)) =
      termPauli e m mγ Λ p' p τ ε ℓ := by
  set S := saSpecScalar τ.j τ.r τ.A τ.ξ (τ.w ε) ε ℓ with hS
  set c : ℂ := (propDenom m ε (p' + ℓ))⁻¹ * (propDenom m ε (p + ℓ))⁻¹ *
    (photonScalar mγ Λ ε ℓ ^ 2 * S) with hc
  unfold termPauli termCoef
  cases ht : τ.t
  · have hph : saOuterPhoton mγ Λ false τ.j τ.r τ.A τ.ξ (τ.w ε) ε ℓ = fun ν ρ =>
        (photonScalar mγ Λ ε ℓ ^ 2 * S) * gPhoton ν ρ :=
      funext fun ν => funext fun ρ => saSandwich_false mγ Λ ε ℓ _ ν ρ
    have hV : (fun μ => vertexChain e μ (electronPropagator m ε (p' + ℓ))
        (electronPropagator m ε (p + ℓ)) (saOuterPhoton mγ Λ false τ.j τ.r τ.A τ.ξ (τ.w ε) ε ℓ))
        = fun μ => c • vertexChain e μ (electronNumerator m (p' + ℓ))
          (electronNumerator m (p + ℓ)) gPhoton := by
      funext μ
      rw [hph, QED.TwoLoop.CountertermLimit.electronPropagator_eq_smul,
        QED.TwoLoop.CountertermLimit.electronPropagator_eq_smul, vertexChain_smul_out,
        vertexChain_smul_in, vertexChain_smul_photon, smul_smul, smul_smul]
    rw [hV, pauliNum_smul']
    change c * pauliChain e m p' p ℓ = _
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [saLimTermInt_eq_mul]
    have hG := saOuter_scalar mγ Λ hε τ.j m p' p ℓ (pauliChain e m p' p)
    rw [hc, hS, saSpecScalar]
    linear_combination (∫ x in simplexSet τ.n, τ.w ε x * (fDen (√(τ.A x)) ε (τ.ξ x) ℓ ^ τ.r)⁻¹)
      * hG
  · have hph : saOuterPhoton mγ Λ true τ.j τ.r τ.A τ.ξ (τ.w ε) ε ℓ = fun ν ρ =>
        (photonScalar mγ Λ ε ℓ ^ 2 * S) *
          (((Minkowski.lower ℓ ν : ℝ) : ℂ) * ((Minkowski.lower ℓ ρ : ℝ) : ℂ)) :=
      funext fun ν => funext fun ρ => saSandwich_true mγ Λ ε ℓ _ ν ρ
    have hV : (fun μ => vertexChain e μ (electronPropagator m ε (p' + ℓ))
        (electronPropagator m ε (p + ℓ)) (saOuterPhoton mγ Λ true τ.j τ.r τ.A τ.ξ (τ.w ε) ε ℓ))
        = fun μ => c • vertexChain e μ (electronNumerator m (p' + ℓ))
          (electronNumerator m (p + ℓ))
          (fun ν ρ => ((Minkowski.lower ℓ ν : ℝ) : ℂ) * ((Minkowski.lower ℓ ρ : ℝ) : ℂ)) := by
      funext μ
      rw [hph, QED.TwoLoop.CountertermLimit.electronPropagator_eq_smul,
        QED.TwoLoop.CountertermLimit.electronPropagator_eq_smul, vertexChain_smul_out,
        vertexChain_smul_in, vertexChain_smul_photon, smul_smul, smul_smul]
    rw [hV, pauliNum_smul', pauliNum_longitudinal e hm hp' hp hq ℓ]
    simp only [↓reduceIte, mul_zero, zero_mul]

/-! ### Lists of terms -/

/-- The Pauli numerator of the vertex chain is linear in a list of photon factors. -/
theorem pauliNum_vertexChain_list (e m : ℝ) (p' p : Fin 4 → ℝ)
    (A B : Matrix (Fin 4) (Fin 4) ℂ) (L : List (ℂ × SAOuterTerm))
    (F : SAOuterTerm → Fin 4 → Fin 4 → ℂ) :
    pauliNum m p' p (fun μ => vertexChain e μ A B
      (fun ν ρ => (L.map fun q => q.1 * F q.2 ν ρ).sum)) =
      (L.map fun q => q.1 * pauliNum m p' p (fun μ => vertexChain e μ A B (F q.2))).sum := by
  induction L with
  | nil => simp [vertexChain, pauliNum_eq_sum]
  | cons q L ih =>
    simp only [List.map_cons, List.sum_cons, vertexChain_add_photon, vertexChain_smul_photon]
    rw [QED.TwoLoop.PauliZeroLimit.pauliNum_add, pauliNum_smul', ih]

/-- **The Pauli numerator of the nested outer integrand of a list of terms**, pointwise. -/
theorem pauliNum_nestPhoton_list {e m : ℝ} (mγ Λ : ℝ) (hm : m ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) {ε : ℝ} (hε : 0 < ε)
    (L : List (ℂ × SAOuterTerm)) (ℓ : Fin 4 → ℝ) :
    pauliNum m p' p (fun μ => vertexChain e μ (electronPropagator m ε (p' + ℓ))
      (electronPropagator m ε (p + ℓ))
      (nestPhoton mγ Λ ε (fun k a b => saOuterTensor L ε k a b) ℓ)) =
      (L.map fun q => q.1 * termPauli e m mγ Λ p' p q.2 ε ℓ).sum := by
  have hph : nestPhoton mγ Λ ε (fun k a b => saOuterTensor L ε k a b) ℓ = fun ν ρ =>
      (L.map fun q => q.1 * saOuterPhoton mγ Λ q.2.t q.2.j q.2.r q.2.A q.2.ξ (q.2.w ε) ε ℓ ν ρ
        ).sum :=
    funext fun ν => funext fun ρ => saOuterPhoton_list mγ Λ L ε ℓ ν ρ
  have hlin := pauliNum_vertexChain_list e m p' p (electronPropagator m ε (p' + ℓ))
    (electronPropagator m ε (p + ℓ)) L
    (fun τ ν ρ => saOuterPhoton mγ Λ τ.t τ.j τ.r τ.A τ.ξ (τ.w ε) ε ℓ ν ρ)
  rw [hph, hlin]
  exact congrArg List.sum (List.map_congr_left fun q _ => by
    rw [pauliNum_outerPhoton mγ Λ hm hp' hp hq hε q.2 ℓ])

/-! ### `T★ᵤ` at the flavours of (HA₆) -/

theorem regFlavors_mass_openLine (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) :
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ).mass (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ).openLine = P₀.m :=
  rfl

/-- **`T★ᵤ` at fixed admissible regulators**: one list of good outer terms gives the two-loop
vacuum polarization at every `ε ∈ (0, 1]`. -/
theorem regFlavors_spec {P₀ : Params} (hm : 0 < P₀.m) {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt}
    (hA : SetAAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D) :
    ∃ L : List (ℂ × SAOuterTerm), (∀ q ∈ L, q.2.Good (min P₀.m (min mγ Λ))) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ k a b,
        Graded.vacuumPolarizationPart { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
          (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D 2 k a b = saOuterTensor L ε k a b := by
  obtain ⟨hM₁, hM₂, hPV₁, hPV₂, hmγ, hΛ, hmΛ, -, hD⟩ := hA
  exact setASpecU_vacuumPolarizationPart_two (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D Graded.leptonRep P₀.m hm
    (QED.GradedProof.RPi4.le_leptonFlavors_mass (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) _ hM₁ hM₂
      (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0))
    hmγ hΛ QED.GradedProof.RPi4.leptonRep_idem
    (QED.GradedProof.RPi4.leptonFlavors_blockPV₁ (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) _ hPV₁
      fun ℓ => ℓ.elim0)
    (QED.GradedProof.RPi4.leptonFlavors_blockPV₂ (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) _ hPV₂
      fun ℓ => ℓ.elim0)
    (QED.GradedProof.RPi4.hD_of_renormalized _ _ _ hD)

/-! ### The nested form at fixed `ε` (open) -/

/-- The set (a) family vertex at `ε`, at fixed regulators. -/
noncomputable abbrev famV (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) (D : RegCt) (ε : ℝ)
    (p' p : Fin 4 → ℝ) (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  Graded.familyVertex { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D (fun C _ => IsOnePI C ∧ ThreeLoop.IsSetA C) 7 p' p μ

/-- The two-loop vacuum polarization at `ε`, at fixed regulators. -/
noncomputable abbrev vpTwo (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) (D : RegCt) (ε : ℝ) :
    (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ :=
  fun ℓ a b => Graded.vacuumPolarizationPart { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D 2 ℓ a b

/-- **The nested form of the set (a) family vertex at fixed `ε`** (open; obligation (N) of
`SetALimitLink`, the conclusion of `QED.ChainProof.SetANest.familyVertex_setA_eq_nested`): at
admissible regulators, on-shell positive-energy pairs with `q² > 0` and `ε ∈ (0, 1]`, every entry
is `(1/i)` times the energy-first integral of the outer integrand with the photon factor
`Δ Π⁽⁴⁾_ε Δ`, which is integrable in both stages. -/
def SetANestForm (P₀ : Params) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D, SetAAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D →
    ∀ p' p, IsPairQ P₀.m p' p → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ μ i j,
      EFInt (nestInt P₀.e P₀.m mγ Λ ε p' p (vpTwo P₀ M₁ M₂ c₁ c₂ mγ Λ D ε) μ i j) ∧
        famV P₀ M₁ M₂ c₁ c₂ mγ Λ D ε p' p μ i j = (1 / I) *
          energyFirstIntegral (nestInt P₀.e P₀.m mγ Λ ε p' p
            (vpTwo P₀ M₁ M₂ c₁ c₂ mγ Λ D ε) μ i j)

/-! ### The Pauli numerator at fixed `ε` and its limit -/

/-- The engine term of the Pauli-projected outer integrand of a term. -/
noncomputable def pauliTerm (e m : ℝ) (p' p : Fin 4 → ℝ) (τ : SAOuterTerm) : SALimTerm :=
  τ.engine (pauliChain e m p' p) (pauliChain_quadratic e m p' p).choose τ.j

theorem quadN_pauliChain (e m : ℝ) (p' p : Fin 4 → ℝ) : QuadN (pauliChain e m p' p) :=
  ⟨continuous_pauliChain e m p' p, pauliChain_quadratic e m p' p, pauliChain_bound e m p' p⟩

theorem pauliTerm_hyp {e m Mlo : ℝ} {p' p : Fin 4 → ℝ} {τ : SAOuterTerm} (hτ : τ.Good Mlo) :
    (pauliTerm e m p' p τ).Hyp 2 Mlo :=
  SAOuterTerm.engine_hyp hτ (quadN_pauliChain e m p' p) (by have := hτ.1; split_ifs at this <;>
    omega)

/-- **The explicit Pauli limit** of a list of terms: the combination of the engine limits of
the Pauli-projected outer integrands of its `g` terms. -/
noncomputable def setAPauliLim (e m mγ Λ : ℝ) (L : List (ℂ × SAOuterTerm)) (p' p : Fin 4 → ℝ) :
    ℂ :=
  (L.map fun q => q.1 * (termCoef mγ Λ q.2 *
    (pauliTerm e m p' p q.2).lim m (saMs4 mγ Λ) p' p)).sum

theorem efi_list_sum {ι : Type*} (L : List ι) (F : ι → (Fin 4 → ℝ) → ℂ)
    (h : ∀ q ∈ L, EFInt (F q)) :
    energyFirstIntegral (fun ℓ => (L.map fun q => F q ℓ).sum) =
      (L.map fun q => energyFirstIntegral (F q)).sum := by
  induction L with
  | nil => simp [energyFirstIntegral]
  | cons q L ih =>
    simp only [List.map_cons, List.sum_cons]
    have hL : EFInt fun ℓ => (L.map fun q => F q ℓ).sum := by
      clear ih
      induction L with
      | nil =>
        simpa using (h q (List.mem_cons_self ..)).const_mul 0
      | cons q' L ih' =>
        simp only [List.map_cons, List.sum_cons]
        exact (h q' (by simp)).add (ih' fun r hr => h r (by
          rcases List.mem_cons.mp hr with rfl | hr
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))
    rw [efi_add (h q (List.mem_cons_self ..)) hL,
      ih fun r hr => h r (List.mem_cons_of_mem _ hr)]

theorem tendsto_list_sum' {ι : Type*} (L : List ι) {f : ι → ℝ → ℂ} {a : ι → ℂ}
    {l : Filter ℝ} (h : ∀ q ∈ L, Tendsto (f q) l (𝓝 (a q))) :
    Tendsto (fun ε => (L.map fun q => f q ε).sum) l (𝓝 (L.map a).sum) := by
  induction L with
  | nil => simpa using tendsto_const_nhds
  | cons q L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h q (List.mem_cons_self ..)).add (ih fun r hr => h r (List.mem_cons_of_mem _ hr))

section Fixed

variable {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt}

/-- **The Pauli numerator of the family vertex at fixed `ε`**, from the nested form and a `T★ᵤ`
list. -/
theorem pauliNum_familyVertex_eq (hm : 0 < P₀.m) (hN : SetANestForm P₀)
    (hA : SetAAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D) {L : List (ℂ × SAOuterTerm)}
    (hL : ∀ q ∈ L, q.2.Good (min P₀.m (min mγ Λ)))
    (hVP : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ k a b,
      Graded.vacuumPolarizationPart { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
        (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D 2 k a b = saOuterTensor L ε k a b)
    {p' p : Fin 4 → ℝ} (hpq : IsPairQ P₀.m p' p) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    pauliNum P₀.m p' p (famV P₀ M₁ M₂ c₁ c₂ mγ Λ D ε p' p) = (1 / I) *
      (L.map fun q => q.1 * (termCoef mγ Λ q.2 *
        (pauliTerm P₀.e P₀.m p' p q.2).val P₀.m (saMs4 mγ Λ) p' p ε)).sum := by
  obtain ⟨hp', hp, hp0', hp0, hq⟩ := hpq
  have hpq : IsPairQ P₀.m p' p := ⟨hp', hp, hp0', hp0, hq⟩
  obtain ⟨-, -, -, -, hmγ, hΛ, -, -, -⟩ := id hA
  set Mlo := min P₀.m (min mγ Λ)
  have hMlo : 0 < Mlo := lt_min hm (lt_min hmγ hΛ)
  have hMs : ∀ i, Mlo ≤ saMs4 mγ Λ i := fun i => by
    have h1 : Mlo ≤ mγ := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : Mlo ≤ Λ := (min_le_right _ _).trans (min_le_right _ _)
    fin_cases i <;> simp [saMs4, h1, h2]
  have hX : vpTwo P₀ M₁ M₂ c₁ c₂ mγ Λ D ε = fun k a b => saOuterTensor L ε k a b :=
    funext fun k => funext fun a => funext fun b => hVP ε hε hε1 k a b
  have hent := fun (j : Idx) => hN M₁ M₂ c₁ c₂ mγ Λ D hA p' p hpq ε hε hε1 j.1 j.2.1 j.2.2
  rw [pauliNum_eq_sum_idx]
  have e1 : ∀ j : Idx, pauliWt P₀.m p' p j.1 j.2.1 j.2.2 *
      famV P₀ M₁ M₂ c₁ c₂ mγ Λ D ε p' p j.1 j.2.1 j.2.2 = (1 / I) * energyFirstIntegral
        (fun ℓ => pauliWt P₀.m p' p j.1 j.2.1 j.2.2 * nestInt P₀.e P₀.m mγ Λ ε p' p
          (vpTwo P₀ M₁ M₂ c₁ c₂ mγ Λ D ε) j.1 j.2.1 j.2.2 ℓ) := by
    intro j
    rw [(hent j).2, efi_const_mul]
    ring
  simp only [e1, ← Finset.mul_sum]
  congr 1
  rw [← efi_sum _ fun j _ => (hent j).1.const_mul _]
  have e2 : (fun ℓ => ∑ j : Idx, pauliWt P₀.m p' p j.1 j.2.1 j.2.2 *
      nestInt P₀.e P₀.m mγ Λ ε p' p (vpTwo P₀ M₁ M₂ c₁ c₂ mγ Λ D ε) j.1 j.2.1 j.2.2 ℓ) =
      fun ℓ => (L.map fun q => q.1 * termPauli P₀.e P₀.m mγ Λ p' p q.2 ε ℓ).sum := by
    funext ℓ
    rw [← pauliNum_nestPhoton_list mγ Λ hm.ne' hp' hp hq hε L ℓ, pauliNum_eq_sum_idx, hX]
    rfl
  have hI : ∀ q ∈ L, EFInt fun ℓ => q.1 * termPauli P₀.e P₀.m mγ Λ p' p q.2 ε ℓ :=
    fun q hq => ((SALimTerm.efInt_val hm hMlo le_rfl hp' hp hp0' hp0 hMs
      (pauliTerm_hyp (hL q hq)) hε hε1).const_mul (termCoef mγ Λ q.2)).const_mul q.1
  rw [e2, efi_list_sum L (fun q ℓ => q.1 * termPauli P₀.e P₀.m mγ Λ p' p q.2 ε ℓ) hI]
  refine congrArg List.sum (List.map_congr_left fun q _ => ?_)
  simp only [termPauli, efi_const_mul, SALimTerm.val, pauliTerm, SAOuterTerm.engine]

/-- **The Pauli numerator of every set (a) limit**, from the nested form and a `T★ᵤ` list. -/
theorem pauliNum_setALim_eq (hm : 0 < P₀.m) (hN : SetANestForm P₀)
    (hA : SetAAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D) {L : List (ℂ × SAOuterTerm)}
    (hL : ∀ q ∈ L, q.2.Good (min P₀.m (min mγ Λ)))
    (hVP : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ k a b,
      Graded.vacuumPolarizationPart { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
        (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D 2 k a b = saOuterTensor L ε k a b)
    {p' p : Fin 4 → ℝ} (hpq : IsPairQ P₀.m p' p) {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hV : setALim P₀ M₁ M₂ c₁ c₂ mγ Λ D p' p V) :
    pauliNum P₀.m p' p V = (1 / I) * setAPauliLim P₀.e P₀.m mγ Λ L p' p := by
  obtain ⟨hp', hp, hp0', hp0, -⟩ := id hpq
  obtain ⟨-, -, -, -, hmγ, hΛ, -, -, -⟩ := id hA
  set Mlo := min P₀.m (min mγ Λ)
  have hMlo : 0 < Mlo := lt_min hm (lt_min hmγ hΛ)
  have hMs : ∀ i, Mlo ≤ saMs4 mγ Λ i := fun i => by
    have h1 : Mlo ≤ mγ := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : Mlo ≤ Λ := (min_le_right _ _).trans (min_le_right _ _)
    fin_cases i <;> simp [saMs4, h1, h2]
  have hT : Tendsto (fun ε => pauliNum P₀.m p' p (famV P₀ M₁ M₂ c₁ c₂ mγ Λ D ε p' p))
      (𝓝[>] 0) (𝓝 (pauliNum P₀.m p' p V)) := by
    simp only [pauliNum_eq_sum_idx]
    exact tendsto_finsetSum _ fun j _ => (hV j.1 j.2.1 j.2.2).const_mul _
  have hT2 := (tendsto_list_sum' L (l := 𝓝[>] (0 : ℝ))
    (f := fun q ε => q.1 * (termCoef mγ Λ q.2 *
      (pauliTerm P₀.e P₀.m p' p q.2).val P₀.m (saMs4 mγ Λ) p' p ε))
    (a := fun q => q.1 * (termCoef mγ Λ q.2 *
      (pauliTerm P₀.e P₀.m p' p q.2).lim P₀.m (saMs4 mγ Λ) p' p))
    fun q hq => ((SALimTerm.tendsto hm hMlo le_rfl hp' hp hp0' hp0 hMs
      (pauliTerm_hyp (hL q hq))).const_mul _).const_mul _).const_mul (1 / I)
  refine tendsto_nhds_unique hT (hT2.congr' ?_)
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
  exact (pauliNum_familyVertex_eq hm hN hA hL hVP hpq hε.1 hε.2).symm

/-- **The Pauli numerator of the set (a) limits from the nested form**: under `SetANestForm`, at
admissible regulators there is one list of good spectral terms (the `T★ᵤ` list of `Π⁽⁴⁾_ε`,
independent of the external momenta) such that at every on-shell positive-energy pair with
`q² > 0` every limit `V` has `pauliNum V = (1/i) setAPauliLim L`. -/
theorem exists_pauliNum_setALim (hm : 0 < P₀.m) (hN : SetANestForm P₀)
    (hA : SetAAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D) :
    ∃ L : List (ℂ × SAOuterTerm), (∀ q ∈ L, q.2.Good (min P₀.m (min mγ Λ))) ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ k a b,
        Graded.vacuumPolarizationPart { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
          (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D 2 k a b = saOuterTensor L ε k a b) ∧
      ∀ p' p, IsPairQ P₀.m p' p → ∀ V, setALim P₀ M₁ M₂ c₁ c₂ mγ Λ D p' p V →
        pauliNum P₀.m p' p V = (1 / I) * setAPauliLim P₀.e P₀.m mγ Λ L p' p := by
  obtain ⟨L, hL, hVP⟩ := regFlavors_spec hm hA
  exact ⟨L, hL, hVP, fun p' p hpq V hV => pauliNum_setALim_eq hm hN hA hL hVP hpq hV⟩

end Fixed

end QED.ChainProof.SetANestedAt

end
