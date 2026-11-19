/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.LeptonRep
public import QED.Frozen.Graded.IsRenormalizedThrough
public import QED.Frozen.Lepton.LeptonFlavors
public import QED.Frozen.Graded.VacuumPolarizationPartTwoExistsUnique
public import QED.GradedProof.VP2Final

/-!
# (R-Π₄) setup: the multi-lepton blocks and the fixed-regulator form factor

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57). The frozen statement fixes
the flavour data `leptonFlavors P H` (L₁) with the per-lepton scheme `leptonRep` (G₁₂′). This file
supplies the fixed-regulator facts that do not involve any regulator limit.

* `leptonRep_idem`, `sum_filter_leptonRep_inl`, `sum_filter_leptonRep_inr`: the blocks of
  `leptonRep` are the electron triple and the heavy-lepton triples.
* `leptonFlavors_blockPV₁`, `leptonFlavors_blockPV₂`: the per-block Pauli–Villars hypotheses of
  (G-Π₂) are the two conditions of each lepton.
* `le_leptonFlavors_mass`: every flavour mass is at least the electron mass.
* `exists_pol`: at fixed regulators and renormalized counterterms the order-`e⁴` vacuum
  polarization has a transverse limit on `s > -4m²` (from the sealed (G-Π₂)).
* `pol_eq_of_tendsto`: any two such form factors agree on the region.
* `pol_zero`: the order-`e⁴` photon condition gives `Π(0) = 0`.
-/

@[expose] public section

open Filter Topology
open QED.WickModel (Params)
open QED.Graded
open QED.GradedProof.VP2 (vpT exists_vpT_canonVec_ne)
open QED.GradedProof.SE2 (canonVec dot_canonVec nullVec dot_nullVec)

namespace QED.GradedProof.RPi4

variable {n : ℕ}

/-! ### The blocks of `leptonRep` -/

theorem leptonRep_idem (f : Fin 3 ⊕ Fin n × Fin 3) : leptonRep (leptonRep f) = leptonRep f := by
  cases f <;> rfl

theorem leptonRep_fixed {b : Fin 3 ⊕ Fin n × Fin 3} (hb : leptonRep b = b) :
    b = .inl 0 ∨ ∃ ℓ : Fin n, b = .inr (ℓ, 0) := by
  rcases b with i | x
  · exact Or.inl hb.symm
  · exact Or.inr ⟨x.1, hb.symm⟩

theorem sum_filter_leptonRep_inl {M : Type*} [AddCommMonoid M] (G : Fin 3 ⊕ Fin n × Fin 3 → M) :
    ∑ f ∈ Finset.univ.filter (fun f => leptonRep f = .inl 0), G f = ∑ i : Fin 3, G (.inl i) := by
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  simp [leptonRep]

theorem sum_filter_leptonRep_inr {M : Type*} [AddCommMonoid M] (G : Fin 3 ⊕ Fin n × Fin 3 → M)
    (ℓ : Fin n) :
    ∑ f ∈ Finset.univ.filter (fun f => leptonRep f = .inr (ℓ, 0)), G f =
      ∑ i : Fin 3, G (.inr (ℓ, i)) := by
  rw [Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [leptonRep, reduceCtorEq, ite_false, Finset.sum_const_zero, zero_add, Sum.inr.injEq,
    Prod.mk.injEq, and_true]
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun _ => Finset.univ)
    (h := fun _ _ => by simp)]
  simp

/-! ### The per-block Pauli–Villars conditions -/

section Blocks

variable (P : Params) (H : Fin n → Lepton.HeavyLepton)

theorem leptonFlavors_blockPV₁ (hPV : 1 + P.c₁ + P.c₂ = 0) (hH : ∀ ℓ, 1 + (H ℓ).c₁ + (H ℓ).c₂ = 0)
    (b : Fin 3 ⊕ Fin n × Fin 3) (hb : leptonRep b = b) :
    ∑ f ∈ Finset.univ.filter (fun f => leptonRep f = b), (Lepton.leptonFlavors P H).coeff f =
      0 := by
  rcases leptonRep_fixed hb with rfl | ⟨ℓ, rfl⟩
  · rw [sum_filter_leptonRep_inl, Fin.sum_univ_three]
    simpa [Lepton.leptonFlavors, Params.loopCoeff] using hPV
  · rw [sum_filter_leptonRep_inr, Fin.sum_univ_three]
    simpa [Lepton.leptonFlavors] using hH ℓ

theorem leptonFlavors_blockPV₂ (hPV : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hH : ∀ ℓ, (H ℓ).m ^ 2 + (H ℓ).c₁ * (H ℓ).M₁ ^ 2 + (H ℓ).c₂ * (H ℓ).M₂ ^ 2 = 0)
    (b : Fin 3 ⊕ Fin n × Fin 3) (hb : leptonRep b = b) :
    ∑ f ∈ Finset.univ.filter (fun f => leptonRep f = b),
      (Lepton.leptonFlavors P H).coeff f * (Lepton.leptonFlavors P H).mass f ^ 2 = 0 := by
  rcases leptonRep_fixed hb with rfl | ⟨ℓ, rfl⟩
  · rw [sum_filter_leptonRep_inl, Fin.sum_univ_three]
    simpa [Lepton.leptonFlavors, Params.loopCoeff, Params.mass] using hPV
  · rw [sum_filter_leptonRep_inr, Fin.sum_univ_three]
    simpa [Lepton.leptonFlavors] using hH ℓ

theorem le_leptonFlavors_mass (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hH : ∀ ℓ, P.m < (H ℓ).m) (hH₁ : ∀ ℓ, (H ℓ).m < (H ℓ).M₁) (hH₂ : ∀ ℓ, (H ℓ).m < (H ℓ).M₂)
    (f : Fin 3 ⊕ Fin n × Fin 3) : P.m ≤ (Lepton.leptonFlavors P H).mass f := by
  rcases f with i | ⟨ℓ, i⟩
  · fin_cases i <;> simp [Lepton.leptonFlavors, Params.mass] <;> linarith
  · have h1 := hH ℓ
    have h2 := hH₁ ℓ
    have h3 := hH₂ ℓ
    fin_cases i <;> simp [Lepton.leptonFlavors] <;> linarith

end Blocks

/-! ### The fixed-regulator form factor -/

section Pol

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F)

/-- The level-`0` counterterms of a scheme renormalized through order `e⁴` are block constant. -/
theorem hD_of_renormalized {rep : F → F} (h : IsRenormalizedThrough P Φ D rep 2) (f : F) :
    D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0 :=
  h.1 f 0 (by norm_num)

/-- **Existence of the fixed-regulator form factor** (from the sealed (G-Π₂)), as a function on
`ℝ`. -/
theorem exists_pol (rep : F → F) (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : IsRenormalizedThrough P Φ D rep 2) :
    ∃ Pol : ℝ → ℂ, ∀ k : Fin 4 → ℝ, -(4 * m₀ ^ 2) < Minkowski.dot k k → ∀ μ ν : Fin 4,
      Tendsto (fun ε : ℝ => vacuumPolarizationPart { P with ε := ε } Φ D 2 k μ ν) (𝓝[>] 0)
        (𝓝 (Pol (Minkowski.dot k k) *
          ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ))) := by
  obtain ⟨-, Pol, hPol, -⟩ := vacuumPolarizationPart_two_existsUnique P Φ D rep m₀ hm₀ hmass hmγ
    hΛ hrep hPV₁ hPV₂ (hD_of_renormalized P Φ D hD)
  refine ⟨fun s => if hs : -(4 * m₀ ^ 2) < s then Pol ⟨s, hs⟩ else 0, fun k hk μ ν => ?_⟩
  simpa [hk] using hPol k hk μ ν

/-- The transverse limit property of a form factor on the region `s > -T`. -/
def IsPol (T : ℝ) (Pol : ℝ → ℂ) : Prop :=
  ∀ k : Fin 4 → ℝ, -T < Minkowski.dot k k → ∀ μ ν : Fin 4,
    Tendsto (fun ε : ℝ => vacuumPolarizationPart { P with ε := ε } Φ D 2 k μ ν) (𝓝[>] 0)
      (𝓝 (Pol (Minkowski.dot k k) *
        ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ)))

/-- **Uniqueness on the region**: two form factors with the transverse limit property agree at
every `s > -T`. -/
theorem pol_eq_of_tendsto {T : ℝ} {Pol Pol' : ℝ → ℂ} (h : IsPol P Φ D T Pol)
    (h' : IsPol P Φ D T Pol') {s : ℝ} (hs : -T < s) : Pol s = Pol' s := by
  have hk : -T < Minkowski.dot (canonVec s) (canonVec s) := by rwa [dot_canonVec]
  obtain ⟨μ, ν, hv⟩ := exists_vpT_canonVec_ne s
  have e := tendsto_nhds_unique (h _ hk μ ν) (h' _ hk μ ν)
  have hv' : ((s * Minkowski.metric μ ν - canonVec s μ * canonVec s ν : ℝ) : ℂ) ≠ 0 := by
    simpa only [vpT, dot_canonVec] using hv
  rw [dot_canonVec] at e
  exact mul_right_cancel₀ hv' e

/-- **The photon condition fixes `Π(0) = 0`**: with the order-`e⁴` photon on-shell condition
(G₁₁), every form factor with the transverse limit property on a region containing `0` vanishes
at `0`. -/
theorem pol_zero {T : ℝ} (hT : 0 < T) {Pol : ℝ → ℂ} (h : IsPol P Φ D T Pol)
    (hph : IsPhotonOnShellAt P Φ D 2) : Pol 0 = 0 := by
  have hk : -T < Minkowski.dot nullVec nullVec := by rw [dot_nullVec]; linarith
  have e := tendsto_nhds_unique (h _ hk 0 0) (hph nullVec dot_nullVec 0 0)
  have hv : (((0 : ℝ) * Minkowski.metric 0 0 - nullVec 0 * nullVec 0 : ℝ) : ℂ) ≠ 0 := by
    norm_num [nullVec]
  rw [dot_nullVec] at e
  rcases mul_eq_zero.1 e with h0 | h0
  · exact h0
  · exact absurd h0 hv

end Pol

end QED.GradedProof.RPi4

end
