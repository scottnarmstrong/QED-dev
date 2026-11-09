/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.ThreePointClassificationCount
public import QED.WickModel.ThreePointClassificationPhotonCt
import QED.Wick.Classification
import QED.WickModel.SelfEnergyExistsUnique
import QED.WickModel.VacuumPolarizationEnergyFirst

/-!
# The diagram decomposition of the three-point function

The connected three-point function of the general Wick model at order `≤ 3` (packet 6a,
decision D-24), `connectedFunction P 1 1 3` with outgoing momentum `p'`, incoming momentum `p` and
photon momentum `q = p' - p`, is its 1PI part plus the corrections on its three external legs:

* the counterterm `-i (δ₂ p̸ + δ_m m)` and the self-energy loop on the incoming electron leg,
  each followed by `i e γ^μ (1/i) S̃(p)`;
* the same on the outgoing electron leg at `p'`, each preceded by `(1/i) S̃(p') i e γ^μ`;
* the counterterm `-i δ₃ (q² g^{μρ} - q^μ q^ρ)` and the vacuum polarization loop on the photon
  leg, joined to `i e γ^ν` by `(1/i) Δ̃_{νρ}(q)`.

The tadpoles (a one-vertex closed fermion loop attached by a zero-momentum photon line to the
electron line) contribute `0` at every `ε`: their loop integrand is odd.

The sum over the vertex sequences of total order at most `3` reduces to the empty sequence and
the single vertices (no connected contraction that is not 1PI), the sequences of a gauge vertex
and a fermion or photon counterterm (`QED.WickModel.ThreePointClassificationFermionCt`,
`QED.WickModel.ThreePointClassificationPhotonCt`; each ordering contributes twice what survives
the `1/2!`), and three gauge vertices (`QED.WickModel.ThreePointClassificationCount`; each
correction appears for the six orderings, cancelling the `1/3!`).

## Main statements

* `connectedFunction_threePoint_eq`: the decomposition with no hypothesis, every loop correction
  written as the energy-first integral of its integrand, the leg factor inside.
* `connectedFunction_threePoint`: the decomposition into the 1PI vertex, the self-energy
  `onePIFunction P 1 0 2` and the vacuum polarization `onePIFunction P 0 2 2`, assuming that the
  self-energy and vacuum polarization integrands are integrable in both stages of the
  energy-first prescription (`IntegrableEnergyFirst`). This is what moving the leg factor out of
  the loop integral needs: the energy-first integral returns `0` on non-integrable integrands, so
  it is linear only on integrable ones.
* `connectedFunction_threePoint_of_pos`: the same for `ε > 0`, `m > 0`, regulator fermions
  heavier than the electron and the Pauli–Villars conditions, which supply the integrability.
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.WickModel

/-! ### Integrability in both stages of the energy-first prescription -/

/-- An integrand is integrable in both stages of the energy-first prescription M1: in the loop
energy at every spatial loop momentum, and its energy integral over the spatial loop momentum. -/
def IntegrableEnergyFirst (F : (Fin 4 → ℝ) → ℂ) : Prop :=
  (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ => F (Fin.cons t v)) ∧
    Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ, F (Fin.cons t v)

/-- Integrability in both stages is preserved by a constant factor. -/
theorem IntegrableEnergyFirst.const_mul {F : (Fin 4 → ℝ) → ℂ} (hF : IntegrableEnergyFirst F)
    (c : ℂ) : IntegrableEnergyFirst fun ℓ => c * F ℓ :=
  ⟨fun v => (hF.1 v).const_mul c, by
    simp only [integral_const_mul]
    exact hF.2.const_mul c⟩

/-- **The energy-first integral is additive on integrable integrands.** -/
theorem energyFirstIntegral_finsetSum {ι : Type*} (s : Finset ι) (F : ι → (Fin 4 → ℝ) → ℂ)
    (hF : ∀ i ∈ s, IntegrableEnergyFirst (F i)) :
    QED.OneLoop.energyFirstIntegral (fun ℓ => ∑ i ∈ s, F i ℓ) =
      ∑ i ∈ s, QED.OneLoop.energyFirstIntegral (F i) := by
  unfold QED.OneLoop.energyFirstIntegral
  have hinner : ∀ v : Fin 3 → ℝ, ∫ t : ℝ, ∑ i ∈ s, F i (Fin.cons t v) =
      ∑ i ∈ s, ∫ t : ℝ, F i (Fin.cons t v) := fun v =>
    integral_finsetSum s fun i hi => (hF i hi).1 v
  simp_rw [hinner]
  exact integral_finsetSum s fun i hi => (hF i hi).2

/-- Integrability in both stages is preserved by finite sums. -/
theorem IntegrableEnergyFirst.finsetSum {ι : Type*} (s : Finset ι) {F : ι → (Fin 4 → ℝ) → ℂ}
    (hF : ∀ i ∈ s, IntegrableEnergyFirst (F i)) :
    IntegrableEnergyFirst fun ℓ => ∑ i ∈ s, F i ℓ := by
  refine ⟨fun v => integrable_finsetSum s fun i hi => (hF i hi).1 v, ?_⟩
  have hinner : ∀ v : Fin 3 → ℝ, ∫ t : ℝ, ∑ i ∈ s, F i (Fin.cons t v) =
      ∑ i ∈ s, ∫ t : ℝ, F i (Fin.cons t v) := fun v =>
    integral_finsetSum s fun i hi => (hF i hi).1 v
  simp_rw [hinner]
  exact integrable_finsetSum s fun i hi => (hF i hi).2


/-- Integrability in both stages is preserved by a constant factor on the right. -/
theorem IntegrableEnergyFirst.mul_const {F : (Fin 4 → ℝ) → ℂ} (hF : IntegrableEnergyFirst F)
    (c : ℂ) : IntegrableEnergyFirst fun ℓ => F ℓ * c := by
  simpa only [mul_comm _ c] using hF.const_mul c

/-- A leg factor on the left moves out of the energy-first integral of a sum of integrable
integrands. -/
theorem energyFirstIntegral_sum_mul_left (c : Fin 4 → ℂ) (F : Fin 4 → (Fin 4 → ℝ) → ℂ)
    (hF : ∀ γ, IntegrableEnergyFirst (F γ)) :
    QED.OneLoop.energyFirstIntegral (fun ℓ => ∑ γ, c γ * F γ ℓ) =
      ∑ γ, c γ * QED.OneLoop.energyFirstIntegral (F γ) := by
  rw [energyFirstIntegral_finsetSum _ _ fun γ _ => (hF γ).const_mul (c γ)]
  simp only [QED.OneLoop.energyFirstIntegral_const_mul]

/-- A leg factor on the right moves out of the energy-first integral of a sum of integrable
integrands. -/
theorem energyFirstIntegral_sum_mul_right (c : Fin 4 → ℂ) (F : Fin 4 → (Fin 4 → ℝ) → ℂ)
    (hF : ∀ γ, IntegrableEnergyFirst (F γ)) :
    QED.OneLoop.energyFirstIntegral (fun ℓ => ∑ γ, F γ ℓ * c γ) =
      ∑ γ, QED.OneLoop.energyFirstIntegral (F γ) * c γ := by
  simp only [mul_comm _ (c _)]
  exact energyFirstIntegral_sum_mul_left c F hF

/-- A leg factor moves out of the energy-first integral of a double sum of integrable
integrands. -/
theorem energyFirstIntegral_sum_sum_mul (c : Fin 4 → Fin 4 → ℂ) (F : Fin 4 → (Fin 4 → ℝ) → ℂ)
    (hF : ∀ ρ, IntegrableEnergyFirst (F ρ)) :
    QED.OneLoop.energyFirstIntegral (fun ℓ => ∑ ν, ∑ ρ, c ν ρ * F ρ ℓ) =
      ∑ ν, ∑ ρ, c ν ρ * QED.OneLoop.energyFirstIntegral (F ρ) := by
  rw [energyFirstIntegral_finsetSum _ _ fun ν _ =>
    IntegrableEnergyFirst.finsetSum _ fun ρ _ => (hF ρ).const_mul (c ν ρ)]
  exact Finset.sum_congr rfl fun ν _ => energyFirstIntegral_sum_mul_left (c ν) F hF

/-! ### The vertex sequences of order at most three -/

/-- Two vertices of total order at most `3`: a gauge vertex with a gauge vertex, a fermion
counterterm or a photon counterterm. -/
theorem fin_two_of_sum_order_le {κ : Fin 2 → Wick.VertexKind} (h : ∑ t, (κ t).order ≤ 3) :
    κ = ![.gauge, .gauge] ∨ κ = ![.gauge, .fermionCt] ∨ κ = ![.fermionCt, .gauge] ∨
      κ = ![.gauge, .photonCt] ∨ κ = ![.photonCt, .gauge] := by
  have key : ∀ k₀ k₁ : Wick.VertexKind, k₀.order + k₁.order ≤ 3 →
      (k₀ = .gauge ∧ k₁ = .gauge) ∨ (k₀ = .gauge ∧ k₁ = .fermionCt) ∨
        (k₀ = .fermionCt ∧ k₁ = .gauge) ∨ (k₀ = .gauge ∧ k₁ = .photonCt) ∨
        (k₀ = .photonCt ∧ k₁ = .gauge) := by
    decide
  rw [Fin.sum_univ_two] at h
  have hκ : κ = ![κ 0, κ 1] := by
    funext t
    fin_cases t <;> rfl
  rcases key _ _ h with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
    rw [hκ, h0, h1] <;> simp

open scoped Classical in
/-- The sum over two vertices of total order at most `3` of the connected contractions that are
not 1PI: the fermion counterterm on either electron leg and the photon counterterm on the photon
leg, each twice. -/
theorem sum_nonOnePI_fin_two (P : Params) (p' p : Fin 4 → ℝ) (α β μ : Fin 4) :
    ∑ κ ∈ (Finset.univ : Finset (Fin 2 → Wick.VertexKind)).filter
        (fun κ => ∑ t, (κ t).order ≤ 3),
      ∑ C ∈ (Finset.univ : Finset (Contraction 1 1 κ)).filter
          (fun C => (ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C),
        ((fermionSign C : ℤ) : ℂ) * contractionValue P C ![p'] ![p] ![p' - p] ![α] ![β] ![μ] =
      2 * (∑ γ, ((I * P.e) • Dirac.gamma μ *
          ((1 / I) • QED.OneLoop.electronPropagator P.m P.ε p)) α γ *
        (-I * (((P.δ₂ : ℂ) • Dirac.slash p +
          ((P.δm * P.m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) γ β)) +
      ∑ γ, (-I * (((P.δ₂ : ℂ) • Dirac.slash p' +
          ((P.δm * P.m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α γ)) *
        (((1 / I) • QED.OneLoop.electronPropagator P.m P.ε p') *
          (I * P.e) • Dirac.gamma μ) γ β) +
      2 * ∑ ν, ∑ ρ, (I * P.e) * Dirac.gamma ν α β *
        ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (p' - p) ν ρ) *
          (-I * ((P.δ₃ * (Minkowski.dot (p' - p) (p' - p) * Minkowski.metric μ ρ -
            (p' - p) μ * (p' - p) ρ) : ℝ) : ℂ)) := by
  have hfilter : (Finset.univ : Finset (Fin 2 → Wick.VertexKind)).filter
      (fun κ => ∑ t, (κ t).order ≤ 3) =
      {![.gauge, .gauge], ![.gauge, .fermionCt], ![.fermionCt, .gauge], ![.gauge, .photonCt],
        ![.photonCt, .gauge]} := by
    ext κ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    refine ⟨fin_two_of_sum_order_le, ?_⟩
    rintro (rfl | rfl | rfl | rfl | rfl) <;> decide
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  rw [hfilter, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_eq_zero fun C _ =>
      (isEmpty_contraction_of_not_two_dvd (nf := 1) (by decide) :
        IsEmpty (Contraction 1 1 ![Wick.VertexKind.gauge, .gauge])).elim C,
    sum_nonOnePI_fermionCt h01 rfl rfl, sum_nonOnePI_fermionCt h01.symm rfl rfl,
    sum_nonOnePI_photonCt h01 rfl rfl, sum_nonOnePI_photonCt h01.symm rfl rfl]
  ring

/-! ### The decomposition -/

open scoped Classical in
/-- **The diagram decomposition of the three-point function**, with no hypothesis. The
connected function with one external fermion pair and one external photon at order `≤ 3`, with
outgoing momentum `p'`, incoming momentum `p` and photon momentum `q = p' - p`, is the 1PI
function plus

* on the incoming leg, `[i e γ^μ (1/i) S̃(p)]_{αγ}` times the self-energy counterterm
  `-i (δ₂ p̸ + δ_m m)_{γβ}`, plus the energy-first integral of `[i e γ^μ (1/i) S̃(p)]_{αγ}` times
  the self-energy integrand `selfEnergyIntegrand(p, ℓ)_{γβ}`;
* on the outgoing leg, the same at `p'`, with the factor `[(1/i) S̃(p') i e γ^μ]_{γβ}` on the
  right;
* on the photon leg, `∑_{νρ} [i e γ^ν]_{αβ} (1/i) Δ̃_{νρ}(q)` times the photon counterterm
  `-i δ₃ (q² g^{μρ} - q^μ q^ρ)`, plus the energy-first integral of the same factor times the
  vacuum polarization integrand `vacuumPolarizationIntegrand(q, ℓ)^{μρ}`.

The tadpoles contribute `0`. -/
theorem connectedFunction_threePoint_eq (P : Params) (p' p : Fin 4 → ℝ) (α β μ : Fin 4) :
    connectedFunction P 1 1 3 ![p'] ![p] ![p' - p] ![α] ![β] ![μ] =
      onePIFunction P 1 1 3 ![p'] ![p] ![p' - p] ![α] ![β] ![μ] +
      (∑ γ, ((I * P.e) • Dirac.gamma μ *
          ((1 / I) • QED.OneLoop.electronPropagator P.m P.ε p)) α γ *
        (-I * (((P.δ₂ : ℂ) • Dirac.slash p +
          ((P.δm * P.m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) γ β)) +
        QED.OneLoop.energyFirstIntegral (fun ℓ =>
          ∑ γ, ((I * P.e) • Dirac.gamma μ *
            ((1 / I) • QED.OneLoop.electronPropagator P.m P.ε p)) α γ *
              selfEnergyIntegrand P P.ε p ℓ γ β)) +
      (∑ γ, (-I * (((P.δ₂ : ℂ) • Dirac.slash p' +
          ((P.δm * P.m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α γ)) *
        (((1 / I) • QED.OneLoop.electronPropagator P.m P.ε p') *
          (I * P.e) • Dirac.gamma μ) γ β +
        QED.OneLoop.energyFirstIntegral (fun ℓ =>
          ∑ γ, selfEnergyIntegrand P P.ε p' ℓ α γ *
            (((1 / I) • QED.OneLoop.electronPropagator P.m P.ε p') *
              (I * P.e) • Dirac.gamma μ) γ β)) +
      (∑ ν, ∑ ρ, (I * P.e) * Dirac.gamma ν α β *
          ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (p' - p) ν ρ) *
            (-I * ((P.δ₃ * (Minkowski.dot (p' - p) (p' - p) * Minkowski.metric μ ρ -
              (p' - p) μ * (p' - p) ρ) : ℝ) : ℂ)) +
        QED.OneLoop.energyFirstIntegral (fun ℓ =>
          ∑ ν, ∑ ρ, (I * P.e) * Dirac.gamma ν α β *
            ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (p' - p) ν ρ) *
              vacuumPolarizationIntegrand P P.ε (p' - p) ℓ μ ρ)) := by
  rw [connectedFunction_eq_onePIFunction_add]
  simp only [add_assoc]
  congr 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [Finset.sum_eq_zero fun κ _ => Finset.sum_eq_zero fun C hC =>
      absurd (Finset.mem_filter.mp hC).2.1.1 (not_externalsAttached_of_fin_zero C),
    Finset.sum_eq_zero fun κ _ => Finset.sum_eq_zero fun C hC =>
      absurd (isOnePI_of_le_one le_rfl (Finset.mem_filter.mp hC).2.1.1
        (Finset.mem_filter.mp hC).2.1.2) (Finset.mem_filter.mp hC).2.2,
    sum_nonOnePI_fin_two,
    Finset.sum_eq_single_of_mem Wick.gauge3 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩)
      fun κ hκ hne => absurd (Wick.eq_gauge3_of_sum_order_le (Finset.mem_filter.mp hκ).2) hne,
    sum_nonOnePI_gauge3]
  simp only [Nat.factorial, Nat.cast_one, Nat.cast_mul, Nat.succ_eq_add_one]
  ring

/-- **The diagram decomposition of the three-point function** into the 1PI vertex, the
self-energy insertions on the two electron legs and the vacuum polarization insertion on the
photon leg, with photon momentum `q = p' - p` flowing in at `μ`:

* incoming leg: `[i e γ^μ (1/i) S̃(p)]_{αγ} [i Σ(p)]_{γβ}`;
* outgoing leg: `[i Σ(p')]_{αγ} [(1/i) S̃(p') i e γ^μ]_{γβ}`;
* photon leg: `[i e γ^ν]_{αβ} (1/i) Δ̃_{νρ}(q) [i Π^{μρ}(q)]`.

The tadpoles contribute `0`. The hypotheses are the integrability, in both stages of the
energy-first prescription, of the self-energy integrand at `p` and `p'` and of the vacuum
polarization integrand at `q`: they let the leg factors move out of the loop integrals. -/
theorem connectedFunction_threePoint (P : Params) (p' p : Fin 4 → ℝ) (α β μ : Fin 4)
    (hSE : ∀ k ∈ ({p, p'} : Set (Fin 4 → ℝ)), ∀ γ δ : Fin 4,
      IntegrableEnergyFirst fun ℓ => selfEnergyIntegrand P P.ε k ℓ γ δ)
    (hVP : ∀ ν ρ : Fin 4,
      IntegrableEnergyFirst fun ℓ => vacuumPolarizationIntegrand P P.ε (p' - p) ℓ ν ρ) :
    connectedFunction P 1 1 3 ![p'] ![p] ![p' - p] ![α] ![β] ![μ] =
      onePIFunction P 1 1 3 ![p'] ![p] ![p' - p] ![α] ![β] ![μ]
      + ∑ γ, ((I * P.e) • Dirac.gamma μ *
          ((1 / I) • QED.OneLoop.electronPropagator P.m P.ε p)) α γ
          * onePIFunction P 1 0 2 ![p] ![p] ![] ![γ] ![β] ![]
      + ∑ γ, onePIFunction P 1 0 2 ![p'] ![p'] ![] ![α] ![γ] ![]
          * (((1 / I) • QED.OneLoop.electronPropagator P.m P.ε p') *
            (I * P.e) • Dirac.gamma μ) γ β
      + ∑ ν, ∑ ρ, (I * P.e) * Dirac.gamma ν α β
          * ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (p' - p) ν ρ)
          * onePIFunction P 0 2 2 ![] ![] ![p' - p, -(p' - p)] ![] ![] ![μ, ρ] := by
  rw [connectedFunction_threePoint_eq,
    energyFirstIntegral_sum_mul_left _ (fun γ ℓ => selfEnergyIntegrand P P.ε p ℓ γ β)
      fun γ => hSE p (by simp) γ β,
    energyFirstIntegral_sum_mul_right _ (fun γ ℓ => selfEnergyIntegrand P P.ε p' ℓ α γ)
      fun γ => hSE p' (by simp) α γ,
    energyFirstIntegral_sum_sum_mul _ (fun ρ ℓ => vacuumPolarizationIntegrand P P.ε (p' - p) ℓ μ ρ)
      fun ρ => hVP μ ρ]
  simp only [onePIFunction_selfEnergy, onePIFunction_vacuumPolarization, mul_add, add_mul,
    Finset.sum_add_distrib]

/-- **The diagram decomposition of the three-point function at fixed `ε > 0`**, for `m > 0`,
regulator fermions heavier than the electron and the Pauli–Villars conditions
`1 + c₁ + c₂ = 0`, `m² + c₁ M₁² + c₂ M₂² = 0` (decision D-22): the 1PI vertex plus the
self-energy insertions on the electron legs and the vacuum polarization insertion on the photon
leg, the tadpoles contributing `0`. The integrability needed by `connectedFunction_threePoint`
holds for these parameters (packet 6b). -/
theorem connectedFunction_threePoint_of_pos (P : Params) (hε : 0 < P.ε) (hm : 0 < P.m)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (p' p : Fin 4 → ℝ)
    (α β μ : Fin 4) :
    connectedFunction P 1 1 3 ![p'] ![p] ![p' - p] ![α] ![β] ![μ] =
      onePIFunction P 1 1 3 ![p'] ![p] ![p' - p] ![α] ![β] ![μ]
      + ∑ γ, ((I * P.e) • Dirac.gamma μ *
          ((1 / I) • QED.OneLoop.electronPropagator P.m P.ε p)) α γ
          * onePIFunction P 1 0 2 ![p] ![p] ![] ![γ] ![β] ![]
      + ∑ γ, onePIFunction P 1 0 2 ![p'] ![p'] ![] ![α] ![γ] ![]
          * (((1 / I) • QED.OneLoop.electronPropagator P.m P.ε p') *
            (I * P.e) • Dirac.gamma μ) γ β
      + ∑ ν, ∑ ρ, (I * P.e) * Dirac.gamma ν α β
          * ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (p' - p) ν ρ)
          * onePIFunction P 0 2 2 ![] ![] ![p' - p, -(p' - p)] ![] ![] ![μ, ρ] := by
  refine connectedFunction_threePoint P p' p α β μ (fun k _ γ δ => ?_) (fun ν ρ => ?_)
  · unfold IntegrableEnergyFirst
    simpa only [sub_zero] using SelfEnergyLimit.integrable_selfEnergyIntegrand_sub hε P k 0 γ δ
  · exact ⟨fun v => VacuumPolarizationLimit.integrable_vacuumPolarizationIntegrand_time hε P
      (p' - p) ν ρ v, VacuumPolarizationLimit.integrable_integral_vacuumPolarizationIntegrand hm
      hM₁ hM₂ hPV₁ hPV₂ hε (p' - p) ν ρ⟩

end QED.WickModel

end
