/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.LeptonProof.HMSimple
public import QED.Frozen.Lepton.VertexOrderFive
public import QED.Frozen.Lepton.LeptonFlavors
public import QED.Frozen.TwoLoop.VertexOrderFive
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegrableVertexOrderFive
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The flavour-block split of the multi-lepton order-`e⁵` vertex

Helper level, Phase 5 Stage 0 (decision D-50): obligation O3-M1e of the Stage 0 design note,
in the form used by the proof of (HM₂).

## The auxiliary Pauli–Villars parameter sets

For a heavy lepton `h` (mass `m_ℓ`, regulators `M_{ℓ,1}, M_{ℓ,2}`, coefficients `c_{ℓ,1}, c_{ℓ,2}`)
and an auxiliary mass `X`, the three T1 parameter sets `auxParams P h X j` (`j : Fin 3`) are `P`
with the regulator fermions `(M_j, X)` and the coefficients fixed by the two Pauli–Villars
conditions at the electron mass `m = P.m`, where `M_j = m_ℓ, M_{ℓ,1}, M_{ℓ,2}`. With the weights
`auxWeight P h X j = a_j (M_j² - X²)/(X² - m²)` (`a_j = 1, c_{ℓ,1}, c_{ℓ,2}`), the signed sum of
their loop-flavour measures is the heavy lepton's own measure `∑_j a_j δ_{M_j}`
(`sum_auxWeight_loop`), and the weights sum to `0` (`sum_auxWeight`) when `h` satisfies its two
Pauli–Villars conditions. Every auxiliary set satisfies T1's Pauli–Villars conditions, so T1's
results (the sealed (HV₀), the form-factor clause, the `q² → 0` limit, the units) apply to it.

## Main statement

* `vertexOrderFive_leptonFlavors_eq`: at every `ε > 0`, with T1's Pauli–Villars conditions for the
  electron and each heavy lepton's own,
  `vertexOrderFive P (leptonFlavors P H) = vertexOrderFive_T1 P
    + ∑_ℓ ∑_j auxWeight_{ℓ j} • vertexOrderFive_T1 (auxParams P (H ℓ) X_ℓ j)`.

The proof is contraction by contraction (`contractionValue₂_leptonFlavors_eq`): every 1PI
contraction of the order-`e⁵` vertex is simple (`QED/LeptonProof/HMSimple.lean`); without a
closed loop all the integrands are equal and the weights sum to `0`; with one, the regulated
amplitudes are affine in the loop-flavour measure (`QED/LeptonProof/HMFlavourLoop.lean`), and the
values split because each T1 integrand is integrable (the sealed (HV₀)).
-/

@[expose] public section

open Complex Finset
open QED.WickModel (Params Contraction IsOnePI fermionSign loopCount lineMomentum₂)

namespace QED.Lepton.Proof.HM

/-! ### T1's flavours -/

/-- T1's flavour data: masses (X₀′), coefficients (X₀″), open line `0`. -/
def t1F (P : Params) : Flavors (Fin 3) := ⟨P.mass, P.loopCoeff, 0⟩

theorem regulatedAmplitude₂_t1F (P : Params) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) :
    regulatedAmplitude₂ P (t1F P) C = QED.WickModel.regulatedAmplitude₂ P C := rfl

theorem contractionValue₂_t1F (P : Params) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) :
    contractionValue₂ P (t1F P) C = QED.WickModel.contractionValue₂ P C := rfl

theorem vertexOrderFive_t1F (P : Params) :
    vertexOrderFive P (t1F P) = QED.TwoLoop.vertexOrderFive P := rfl

/-! ### The auxiliary parameter sets -/

/-- The loop masses `m_ℓ, M_{ℓ,1}, M_{ℓ,2}` of a heavy lepton. -/
def hMass (h : HeavyLepton) : Fin 3 → ℝ := ![h.m, h.M₁, h.M₂]

/-- The loop coefficients `1, c_{ℓ,1}, c_{ℓ,2}` of a heavy lepton. -/
def hCoeff (h : HeavyLepton) : Fin 3 → ℝ := ![1, h.c₁, h.c₂]

/-- The first regulator coefficient of the auxiliary set `j`. -/
noncomputable def auxC₁ (m X M : ℝ) : ℝ := (X ^ 2 - m ^ 2) / (M ^ 2 - X ^ 2)

/-- **The auxiliary T1 parameter set** `j` of the heavy lepton `h`: regulators `(M_j, X)`,
coefficients fixed by T1's two Pauli–Villars conditions at `m = P.m`. -/
noncomputable def auxParams (P : Params) (h : HeavyLepton) (X : ℝ) (j : Fin 3) : Params :=
  { P with
    M₁ := hMass h j, M₂ := X, c₁ := auxC₁ P.m X (hMass h j), c₂ := -1 - auxC₁ P.m X (hMass h j) }

/-- **The weight of the auxiliary set** `j`. -/
noncomputable def auxWeight (P : Params) (h : HeavyLepton) (X : ℝ) (j : Fin 3) : ℝ :=
  hCoeff h j * ((hMass h j) ^ 2 - X ^ 2) / (X ^ 2 - P.m ^ 2)

theorem auxParams_PV₁ (P : Params) (h : HeavyLepton) (X : ℝ) (j : Fin 3) :
    1 + (auxParams P h X j).c₁ + (auxParams P h X j).c₂ = 0 := by
  simp only [auxParams]
  ring

theorem auxParams_PV₂ (P : Params) (h : HeavyLepton) {X : ℝ} (j : Fin 3)
    (hX : (hMass h j) ^ 2 ≠ X ^ 2) :
    (auxParams P h X j).m ^ 2 + (auxParams P h X j).c₁ * (auxParams P h X j).M₁ ^ 2 +
      (auxParams P h X j).c₂ * (auxParams P h X j).M₂ ^ 2 = 0 := by
  simp only [auxParams, auxC₁]
  have : (hMass h j) ^ 2 - X ^ 2 ≠ 0 := sub_ne_zero.mpr hX
  field_simp
  ring

/-- The heavy lepton's Pauli–Villars conditions, in the `Fin 3` form. -/
theorem sum_hCoeff {h : HeavyLepton} (h₁ : 1 + h.c₁ + h.c₂ = 0) : ∑ j, hCoeff h j = 0 := by
  simp [Fin.sum_univ_three, hCoeff, ← h₁, add_assoc]

theorem sum_hCoeff_mul {h : HeavyLepton} (h₂ : h.m ^ 2 + h.c₁ * h.M₁ ^ 2 + h.c₂ * h.M₂ ^ 2 = 0) :
    ∑ j, hCoeff h j * hMass h j ^ 2 = 0 := by
  simp [Fin.sum_univ_three, hCoeff, hMass, ← h₂, add_assoc]

/-- **The weights sum to `0`.** -/
theorem sum_auxWeight (P : Params) {h : HeavyLepton} (X : ℝ) (h₁ : 1 + h.c₁ + h.c₂ = 0)
    (h₂ : h.m ^ 2 + h.c₁ * h.M₁ ^ 2 + h.c₂ * h.M₂ ^ 2 = 0) :
    ∑ j, auxWeight P h X j = 0 := by
  have e : ∑ j, auxWeight P h X j =
      (∑ j, hCoeff h j * hMass h j ^ 2 - X ^ 2 * ∑ j, hCoeff h j) / (X ^ 2 - P.m ^ 2) := by
    simp only [auxWeight, Fin.sum_univ_three]
    ring
  rw [e, sum_hCoeff h₁, sum_hCoeff_mul h₂]
  simp

/-- **The signed sum of the auxiliary loop measures is the heavy lepton's measure**: for every
`G`, `∑_j w_j ∑_i c^{(j)}_i G(M^{(j)}_i) = ∑_j a_j G(M_j)`. -/
theorem sum_auxWeight_loop {M : Type*} [AddCommGroup M] [Module ℝ M] (P : Params)
    {h : HeavyLepton} {X : ℝ} (h₁ : 1 + h.c₁ + h.c₂ = 0)
    (h₂ : h.m ^ 2 + h.c₁ * h.M₁ ^ 2 + h.c₂ * h.M₂ ^ 2 = 0) (hXm : X ^ 2 ≠ P.m ^ 2)
    (hX : ∀ j, hMass h j ^ 2 ≠ X ^ 2) (G : ℝ → M) :
    ∑ j, auxWeight P h X j • ∑ i, (auxParams P h X j).loopCoeff i • G ((auxParams P h X j).mass i) =
      ∑ j, hCoeff h j • G (hMass h j) := by
  have hw : ∀ j, auxWeight P h X j * auxC₁ P.m X (hMass h j) = hCoeff h j := by
    intro j
    have h1 : X ^ 2 - P.m ^ 2 ≠ 0 := sub_ne_zero.mpr hXm
    have h2 : hMass h j ^ 2 - X ^ 2 ≠ 0 := sub_ne_zero.mpr (hX j)
    simp only [auxWeight, auxC₁]
    field_simp
  have hs := sum_auxWeight P X h₁ h₂
  have e : ∀ j, auxWeight P h X j • ∑ i, (auxParams P h X j).loopCoeff i •
      G ((auxParams P h X j).mass i) =
      auxWeight P h X j • G P.m + hCoeff h j • G (hMass h j) +
        (-auxWeight P h X j - hCoeff h j) • G X := by
    intro j
    simp only [Fin.sum_univ_three, Params.loopCoeff, Params.mass, auxParams,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_smul, smul_add, smul_smul, hw]
    rw [show auxWeight P h X j * (-1 - auxC₁ P.m X (hMass h j)) =
      -auxWeight P h X j - hCoeff h j by rw [← hw j]; ring]
  simp only [e, sum_add_distrib, ← sum_smul, hs, zero_smul, zero_add, sum_sub_distrib,
    sum_neg_distrib, sum_hCoeff h₁, neg_zero, sub_zero, add_zero]

/-! ### The joint integral of a finite sum -/

theorem jointIntegrable_add {L : ℕ} {F G : (Fin L → Fin 4 → ℝ) → ℂ}
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable L F)
    (hG : QED.TwoLoop.jointEnergyFirstIntegrable L G) :
    QED.TwoLoop.jointEnergyFirstIntegrable L fun ℓ => F ℓ + G ℓ := by
  obtain ⟨hF1, hF2⟩ := hF
  obtain ⟨hG1, hG2⟩ := hG
  refine ⟨fun v => (hF1 v).add (hG1 v), ?_⟩
  have e : (fun v : Fin L → Fin 3 → ℝ => ∫ t : Fin L → ℝ,
      (F fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) +
        G fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) =
      fun v => (∫ t : Fin L → ℝ, F fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) +
        ∫ t : Fin L → ℝ, G fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ) :=
    funext fun v => MeasureTheory.integral_add (hF1 v) (hG1 v)
  rw [e]
  exact hF2.add hG2

theorem jointIntegral_add {L : ℕ} {F G : (Fin L → Fin 4 → ℝ) → ℂ}
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable L F)
    (hG : QED.TwoLoop.jointEnergyFirstIntegrable L G) :
    QED.TwoLoop.jointEnergyFirstIntegral L (fun ℓ => F ℓ + G ℓ) =
      QED.TwoLoop.jointEnergyFirstIntegral L F + QED.TwoLoop.jointEnergyFirstIntegral L G := by
  obtain ⟨hF1, hF2⟩ := hF
  obtain ⟨hG1, hG2⟩ := hG
  unfold QED.TwoLoop.jointEnergyFirstIntegral
  rw [← MeasureTheory.integral_add hF2 hG2]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v =>
    MeasureTheory.integral_add (hF1 v) (hG1 v))

theorem jointIntegrable_const_mul {L : ℕ} (c : ℂ) {F : (Fin L → Fin 4 → ℝ) → ℂ}
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable L F) :
    QED.TwoLoop.jointEnergyFirstIntegrable L fun ℓ => c * F ℓ := by
  obtain ⟨hF1, hF2⟩ := hF
  refine ⟨fun v => (hF1 v).const_mul c, ?_⟩
  simp only [MeasureTheory.integral_const_mul]
  exact hF2.const_mul c

theorem jointIntegral_const_mul {L : ℕ} (c : ℂ) (F : (Fin L → Fin 4 → ℝ) → ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegral L (fun ℓ => c * F ℓ) =
      c * QED.TwoLoop.jointEnergyFirstIntegral L F := by
  unfold QED.TwoLoop.jointEnergyFirstIntegral
  simp only [MeasureTheory.integral_const_mul]

theorem jointIntegrable_zero (L : ℕ) :
    QED.TwoLoop.jointEnergyFirstIntegrable L fun _ => (0 : ℂ) := by
  refine ⟨fun _ => MeasureTheory.integrable_zero _ _ _, ?_⟩
  simp only [MeasureTheory.integral_zero]
  exact MeasureTheory.integrable_zero _ _ _

theorem jointIntegrable_sum {ι : Type*} (s : Finset ι) {L : ℕ}
    {F : ι → (Fin L → Fin 4 → ℝ) → ℂ}
    (hF : ∀ i ∈ s, QED.TwoLoop.jointEnergyFirstIntegrable L (F i)) :
    QED.TwoLoop.jointEnergyFirstIntegrable L fun ℓ => ∑ i ∈ s, F i ℓ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using jointIntegrable_zero L
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact jointIntegrable_add (hF a (Finset.mem_insert_self a s))
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

theorem jointIntegral_sum {ι : Type*} (s : Finset ι) {L : ℕ}
    {F : ι → (Fin L → Fin 4 → ℝ) → ℂ}
    (hF : ∀ i ∈ s, QED.TwoLoop.jointEnergyFirstIntegrable L (F i)) :
    QED.TwoLoop.jointEnergyFirstIntegral L (fun ℓ => ∑ i ∈ s, F i ℓ) =
      ∑ i ∈ s, QED.TwoLoop.jointEnergyFirstIntegral L (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [QED.TwoLoop.jointEnergyFirstIntegral]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [jointIntegral_add (hF a (Finset.mem_insert_self a s))
      (jointIntegrable_sum s fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

/-! ### Contraction by contraction -/

section Split

variable {n : ℕ} (H : Fin n → HeavyLepton) (X : Fin n → ℝ)

/-- **The admissibility of the auxiliary masses**: each heavy lepton satisfies its two
Pauli–Villars conditions, and `X_ℓ²` differs from `m²` and from the three loop masses squared. -/
structure AuxOK (m : ℝ) : Prop where
  pv₁ : ∀ ℓ, 1 + (H ℓ).c₁ + (H ℓ).c₂ = 0
  pv₂ : ∀ ℓ, (H ℓ).m ^ 2 + (H ℓ).c₁ * (H ℓ).M₁ ^ 2 + (H ℓ).c₂ * (H ℓ).M₂ ^ 2 = 0
  hXm : ∀ ℓ, X ℓ ^ 2 ≠ m ^ 2
  hX : ∀ ℓ j, hMass (H ℓ) j ^ 2 ≠ X ℓ ^ 2

theorem leptonFlavors_mass_openLine (P : Params) :
    (leptonFlavors P H).mass (leptonFlavors P H).openLine = P.m := rfl

theorem t1F_mass_openLine (P : Params) : (t1F P).mass (t1F P).openLine = P.m := rfl

theorem sum_leptonFlavors {M : Type*} [AddCommMonoid M] [Module ℝ M] (P : Params) (G : ℝ → M) :
    ∑ f, (leptonFlavors P H).coeff f • G ((leptonFlavors P H).mass f) =
      ∑ i, P.loopCoeff i • G (P.mass i) + ∑ ℓ, ∑ j, hCoeff (H ℓ) j • G (hMass (H ℓ) j) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  rfl

variable {H X}

/-- **The regulated amplitude splits by flavour blocks** (any simple contraction). -/
theorem regulatedAmplitude₂_leptonFlavors_eq (P : Params) (hok : AuxOK H X P.m)
    {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ} (hS : IsSimple C)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : QED.WickModel.Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    regulatedAmplitude₂ P (leptonFlavors P H) C pIn kIn k αOut βIn μ =
      regulatedAmplitude₂ P (t1F P) C pIn kIn k αOut βIn μ +
        ∑ ℓ, ∑ j, (auxWeight P (H ℓ) (X ℓ) j : ℂ) *
          regulatedAmplitude₂ (auxParams P (H ℓ) (X ℓ) j) (t1F (auxParams P (H ℓ) (X ℓ) j)) C
            pIn kIn k αOut βIn μ := by
  by_cases hL : HasLoop C
  · simp only [regulatedAmplitude₂_of_hasLoop _ _ hS hL, leptonFlavors_mass_openLine,
      t1F_mass_openLine]
    have hQ : ∀ ℓ j, (auxParams P (H ℓ) (X ℓ) j).m = P.m := fun _ _ => rfl
    simp only [hQ]
    set G : ℝ → ℂ := fun b => loopAmp P hS P.m b pIn kIn k αOut βIn μ with hG
    have hGQ : ∀ ℓ j b, loopAmp (auxParams P (H ℓ) (X ℓ) j) hS P.m b pIn kIn k αOut βIn μ =
        G b := fun _ _ _ => rfl
    simp only [hGQ]
    have e1 : ∑ f, ((leptonFlavors P H).coeff f : ℂ) * G ((leptonFlavors P H).mass f) =
        ∑ f, (leptonFlavors P H).coeff f • G ((leptonFlavors P H).mass f) := by
      simp only [Complex.real_smul]
    have e2 : ∀ Q : Params, ∑ f, ((t1F Q).coeff f : ℂ) * G ((t1F Q).mass f) =
        ∑ i, Q.loopCoeff i • G (Q.mass i) := fun Q => by
      simp only [Complex.real_smul]
      rfl
    rw [e1, e2, sum_leptonFlavors]
    congr 1
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [← sum_auxWeight_loop P (hok.pv₁ ℓ) (hok.pv₂ ℓ) (hok.hXm ℓ) (hok.hX ℓ) G]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [e2, Complex.real_smul]
  · simp only [regulatedAmplitude₂_of_not_hasLoop _ _ hS hL, leptonFlavors_mass_openLine,
      t1F_mass_openLine]
    have hQ : ∀ ℓ j, (auxParams P (H ℓ) (X ℓ) j).m = P.m := fun _ _ => rfl
    have hGQ : ∀ ℓ j, loopAmp (auxParams P (H ℓ) (X ℓ) j) hS P.m P.m pIn kIn k αOut βIn μ =
        loopAmp P hS P.m P.m pIn kIn k αOut βIn μ := fun _ _ => rfl
    simp only [hQ, hGQ, ← Finset.sum_mul]
    have : ∀ ℓ, ∑ j, (auxWeight P (H ℓ) (X ℓ) j : ℂ) = 0 := fun ℓ => by
      exact_mod_cast sum_auxWeight P (X ℓ) (hok.pv₁ ℓ) (hok.pv₂ ℓ)
    simp [this]

theorem auxParams_ε (P : Params) (h : HeavyLepton) (X : ℝ) (j : Fin 3) :
    (auxParams P h X j).ε = P.ε := rfl

theorem auxParams_with_ε (P : Params) (h : HeavyLepton) (X ε : ℝ) (j : Fin 3) :
    auxParams { P with ε := ε } h X j = { auxParams P h X j with ε := ε } := rfl

/-- The sealed (HV₀), for the flavour data `t1F`. -/
theorem jointIntegrable_t1F (P : Params) (hε : 0 < P.ε) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {N : ℕ}
    {κ : Fin N → Wick.VertexKind} (hκ : ∑ t, (κ t).order = 5) (C : Contraction 1 1 κ)
    (hC : IsOnePI C) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P (t1F P) C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ :=
  QED.TwoLoop.jointEnergyFirstIntegrable_vertexOrderFive P hε hc₁ hc₂ hκ C hC hmom αOut βIn μ

/-- **The value of an order-`e⁵` 1PI contraction splits by flavour blocks.** -/
theorem contractionValue₂_leptonFlavors_eq (P : Params) (hε : 0 < P.ε)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0) (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hok : AuxOK H X P.m) {N : ℕ} {κ : Fin N → Wick.VertexKind} (hκ : ∑ t, (κ t).order = 5)
    (C : Contraction 1 1 κ) (hC : IsOnePI C) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P (leptonFlavors P H) C pOut pIn kIn αOut βIn μ =
      contractionValue₂ P (t1F P) C pOut pIn kIn αOut βIn μ +
        ∑ ℓ, ∑ j, (auxWeight P (H ℓ) (X ℓ) j : ℂ) *
          contractionValue₂ (auxParams P (H ℓ) (X ℓ) j) (t1F (auxParams P (H ℓ) (X ℓ) j)) C
            pOut pIn kIn αOut βIn μ := by
  have hS := isSimple_of_orderFive hκ C hC
  by_cases hL : HasLoop C
  · unfold contractionValue₂
    set c : ℂ := (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹
    have hP := jointIntegrable_t1F P hε hc₁ hc₂ hκ C hC hmom αOut βIn μ
    have hQ : ∀ ℓ j, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun x =>
        c * regulatedAmplitude₂ (auxParams P (H ℓ) (X ℓ) j) (t1F (auxParams P (H ℓ) (X ℓ) j)) C
          pIn kIn (lineMomentum₂ C pOut pIn kIn x) αOut βIn μ := fun ℓ j =>
      jointIntegrable_t1F (auxParams P (H ℓ) (X ℓ) j) hε (auxParams_PV₁ P (H ℓ) (X ℓ) j)
        (auxParams_PV₂ P (H ℓ) j (hok.hX ℓ j)) hκ C hC hmom αOut βIn μ
    have hQ' : ∀ ℓ j, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun x =>
        (auxWeight P (H ℓ) (X ℓ) j : ℂ) * (c * regulatedAmplitude₂ (auxParams P (H ℓ) (X ℓ) j)
          (t1F (auxParams P (H ℓ) (X ℓ) j)) C pIn kIn (lineMomentum₂ C pOut pIn kIn x) αOut βIn
            μ) := fun ℓ j => jointIntegrable_const_mul _ (hQ ℓ j)
    have e : (fun x : Fin (loopCount C) → Fin 4 → ℝ => c * regulatedAmplitude₂ P
        (leptonFlavors P H) C pIn kIn
        (lineMomentum₂ C pOut pIn kIn x) αOut βIn μ) = fun x =>
        c * regulatedAmplitude₂ P (t1F P) C pIn kIn (lineMomentum₂ C pOut pIn kIn x) αOut βIn μ +
          ∑ ℓ, ∑ j, (auxWeight P (H ℓ) (X ℓ) j : ℂ) * (c * regulatedAmplitude₂
            (auxParams P (H ℓ) (X ℓ) j) (t1F (auxParams P (H ℓ) (X ℓ) j)) C pIn kIn
              (lineMomentum₂ C pOut pIn kIn x) αOut βIn μ) := by
      funext x
      rw [regulatedAmplitude₂_leptonFlavors_eq P hok hS, mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e, jointIntegral_add hP (jointIntegrable_sum _ fun ℓ _ =>
      jointIntegrable_sum _ fun j _ => hQ' ℓ j), jointIntegral_sum _ fun ℓ _ =>
      jointIntegrable_sum _ fun j _ => hQ' ℓ j]
    congr 1
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [jointIntegral_sum _ fun j _ => hQ' ℓ j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [jointIntegral_const_mul]
  · have hv : ∀ (Q : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Flavors F),
        Φ.mass Φ.openLine = P.m → Q.e = P.e → Q.δ₁ = P.δ₁ → Q.δ₂ = P.δ₂ → Q.δm = P.δm →
        Q.δ₃ = P.δ₃ → Q.m = P.m → Q.mγ = P.mγ → Q.Λ = P.Λ → Q.ε = P.ε →
        contractionValue₂ Q Φ C pOut pIn kIn αOut βIn μ =
          contractionValue₂ P (t1F P) C pOut pIn kIn αOut βIn μ := by
      intro Q F _ _ Φ hΦ he h1 h2 hm' h3 hm hγ hΛ hε'
      unfold contractionValue₂
      congr 1
      funext x
      rw [regulatedAmplitude₂_of_not_hasLoop _ _ hS hL,
        regulatedAmplitude₂_of_not_hasLoop _ _ hS hL,
        hΦ, t1F_mass_openLine]
      unfold loopAmp contractionAmplitude₂
      rw [he, h1, h2, hm', h3, hm, hγ, hΛ, hε']
    rw [hv P (leptonFlavors P H) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl]
    have hQv : ∀ ℓ j, contractionValue₂ (auxParams P (H ℓ) (X ℓ) j)
        (t1F (auxParams P (H ℓ) (X ℓ) j)) C pOut pIn kIn αOut βIn μ =
          contractionValue₂ P (t1F P) C pOut pIn kIn αOut βIn μ := fun ℓ j =>
      hv _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    simp only [hQv, ← Finset.sum_mul]
    have : ∀ ℓ, ∑ j, (auxWeight P (H ℓ) (X ℓ) j : ℂ) = 0 := fun ℓ => by
      exact_mod_cast sum_auxWeight P (X ℓ) (hok.pv₁ ℓ) (hok.pv₂ ℓ)
    simp [this]

end Split

end QED.Lepton.Proof.HM

end
