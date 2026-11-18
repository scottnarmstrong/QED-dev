/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.OnePIFunction
public import QED.Frozen.Lepton.VertexOrderFive
public import QED.Frozen.Lepton.IsVertexOrderFiveLimit
public import QED.Frozen.Lepton.IsPhotonOnShell
public import QED.Frozen.Lepton.LeptonFlavors
public import QED.Frozen.TwoLoop.OnePIFunction
public import QED.Frozen.TwoLoop.VertexOrderFive
public import QED.Frozen.TwoLoop.IsVertexOrderFiveLimit
public import QED.Frozen.WickModel.IsPhotonOnShell
public import QED.Frozen.TwoLoop.OnePIFunctionEqOnePIFunction
public import QED.Frozen.WickModel.VacuumPolarizationSpec

/-!
# Embedding of packet T1 in the flavour successor: relabelling and the electron alone

Proofs of the Phase 5 Stage 0 embedding goals (E₂), (E₃), (E₃′) and (E₄) (decision D-50),
as the primed helper theorems of `QED.Lepton.Proof`. At T1's flavours
`⟨P.mass, P.loopCoeff, 0⟩` the successor 1PI function and vertex are T1's by `rfl` ((E₁),
(E₁′)); this is used inline.

* (E₂) `onePIFunction₂_relabel'`: composing a flavouring with `e : F ≃ G` is a bijection of the
  flavourings that preserves `Preserves`, the loop weight and the amplitude, so the regulated
  amplitude, the value and the 1PI function do not change.
* (E₃), (E₃′): with no heavy lepton, `leptonFlavors P H` is T1's flavour set up to
  `Fin 3 ⊕ Fin 0 × Fin 3 ≃ Fin 3`, so (E₂) and (E₁′) give T1's vertex and limit predicate.
* (E₄): with no heavy lepton, the two-photon function at order `2` is packet 6a's by (E₂), (E₁)
  and (T₁₄); by (Z₇′) its lightlike limit is `Π(k²) (k² g^{μν} - k^μ k^ν) = -Π(0) k^μ k^ν`, and
  at `k = (1, 1, 0, 0)`, `μ = ν = 0` this is `-Π(0)`.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params Contraction)

namespace QED.Lepton.Proof

/-! ### (E₂): relabelling the flavours -/

section Relabel

variable {F G : Type} (e : F ≃ G) {Φ : Flavors F} {Ψ : Flavors G}
  (hopen : e Φ.openLine = Ψ.openLine)
  {N : ℕ} {κ : Fin N → Wick.VertexKind}

include hopen

/-- Composition with `e` as an equivalence of the flavourings of `Φ` and `Ψ`. -/
def flavoringEquiv : Flavoring Φ κ ≃ Flavoring Ψ κ where
  toFun φ := ⟨fun t => e (φ.1 t), fun t ht => by simp only [φ.2 t ht, hopen]⟩
  invFun ψ := ⟨fun t => e.symm (ψ.1 t), fun t ht => by
    simp only [ψ.2 t ht, ← hopen, Equiv.symm_apply_apply]⟩
  left_inv φ := Subtype.ext (funext fun t => e.symm_apply_apply _)
  right_inv ψ := Subtype.ext (funext fun t => e.apply_symm_apply _)

theorem flavoringEquiv_apply (φ : Flavoring Φ κ) (t : Wick.FermionVertex κ) :
    (flavoringEquiv e hopen φ).1 t = e (φ.1 t) := rfl

theorem fermionFlavor_flavoringEquiv {nf : ℕ} (φ : Flavoring Φ κ)
    (a : Fin nf ⊕ Wick.FermionVertex κ) :
    fermionFlavor Ψ (flavoringEquiv e hopen φ) a = e (fermionFlavor Φ φ a) := by
  rcases a with i | t
  · exact hopen.symm
  · rfl

theorem preserves_flavoringEquiv_iff {nf nA : ℕ} (C : Contraction nf nA κ) (φ : Flavoring Φ κ) :
    Preserves Ψ C (flavoringEquiv e hopen φ) ↔ Preserves Φ C φ := by
  simp only [Preserves, fermionFlavor_flavoringEquiv, EmbeddingLike.apply_eq_iff_eq]

theorem loopWeight_flavoringEquiv (hcoeff : ∀ f, Ψ.coeff (e f) = Φ.coeff f) {nf nA : ℕ}
    (C : Contraction nf nA κ) (φ : Flavoring Φ κ) :
    loopWeight Ψ C (flavoringEquiv e hopen φ) = loopWeight Φ C φ := by
  simp only [loopWeight, fermionFlavor_flavoringEquiv, hcoeff]

theorem contractionAmplitude₂_flavoringEquiv (P : Params) (hmass : ∀ f, Ψ.mass (e f) = Φ.mass f)
    {nf nA : ℕ} (C : Contraction nf nA κ) (φ : Flavoring Φ κ) :
    contractionAmplitude₂ P Ψ C (flavoringEquiv e hopen φ) =
      contractionAmplitude₂ P Φ C φ := by
  funext pIn kIn k αOut βIn μ
  simp only [contractionAmplitude₂, flavoringEquiv_apply, hmass]

theorem regulatedAmplitude₂_relabel (P : Params) [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] (hmass : ∀ f, Ψ.mass (e f) = Φ.mass f)
    (hcoeff : ∀ f, Ψ.coeff (e f) = Φ.coeff f) {nf nA : ℕ} (C : Contraction nf nA κ) :
    regulatedAmplitude₂ P Φ C = regulatedAmplitude₂ P Ψ C := by
  funext pIn kIn k αOut βIn μ
  simp only [regulatedAmplitude₂, Finset.sum_filter]
  refine Fintype.sum_equiv (flavoringEquiv e hopen) _ _ fun φ => ?_
  by_cases h : Preserves Φ C φ
  · rw [ite_eq_left h, ite_eq_left ((preserves_flavoringEquiv_iff e hopen C φ).2 h),
      loopWeight_flavoringEquiv e hopen hcoeff,
      contractionAmplitude₂_flavoringEquiv e hopen P hmass]
  · rw [ite_eq_right h, ite_eq_right (mt (preserves_flavoringEquiv_iff e hopen C φ).1 h)]

theorem contractionValue₂_relabel (P : Params) [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] (hmass : ∀ f, Ψ.mass (e f) = Φ.mass f)
    (hcoeff : ∀ f, Ψ.coeff (e f) = Φ.coeff f) {nf nA : ℕ} (C : Contraction nf nA κ) :
    contractionValue₂ P Φ C = contractionValue₂ P Ψ C := by
  funext pOut pIn kIn αOut βIn μ
  simp only [contractionValue₂, regulatedAmplitude₂_relabel e hopen P hmass hcoeff C]

end Relabel

/-- (E₂) **Relabelling the flavours** does not change the 1PI function. -/
theorem onePIFunction₂_relabel' (P : Params) {F G : Type} [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] (e : F ≃ G)
    (Φ : Flavors F) (Ψ : Flavors G) (hmass : ∀ f, Ψ.mass (e f) = Φ.mass f)
    (hcoeff : ∀ f, Ψ.coeff (e f) = Φ.coeff f) (hopen : e Φ.openLine = Ψ.openLine) :
    onePIFunction₂ P Φ = onePIFunction₂ P Ψ := by
  funext nf nA K pOut pIn kIn αOut βIn μ
  simp only [onePIFunction₂, contractionValue₂_relabel e hopen P hmass hcoeff]

/-! ### (E₃), (E₃′): the electron alone -/

/-- `Fin 3 ⊕ Fin 0 × Fin 3 ≃ Fin 3`: with no heavy lepton only the electron block remains. -/
def leptonFlavorsZeroEquiv : Fin 3 ⊕ Fin 0 × Fin 3 ≃ Fin 3 := Equiv.sumEmpty _ _

/-- With no heavy lepton, the multi-lepton 1PI function is T1's (T₁₁), for any parameters `Q`
whose masses and loop coefficients are those of `P`. -/
theorem onePIFunction₂_leptonFlavors_zero_of (Q P : Params) (H : Fin 0 → HeavyLepton)
    (hmass : Q.mass = P.mass) (hcoeff : Q.loopCoeff = P.loopCoeff) :
    onePIFunction₂ Q (leptonFlavors P H) = QED.WickModel.onePIFunction₂ Q := by
  rw [onePIFunction₂_relabel' Q leptonFlavorsZeroEquiv (leptonFlavors P H)
    ⟨Q.mass, Q.loopCoeff, 0⟩ ?_ ?_ rfl]
  · rfl
  · rintro (i | ⟨j, _⟩)
    · exact congrFun hmass i
    · exact j.elim0
  · rintro (i | ⟨j, _⟩)
    · exact congrFun hcoeff i
    · exact j.elim0

/-- (E₃) for any parameters `Q` with the masses and loop coefficients of `P`. -/
theorem vertexOrderFive_leptonFlavors_zero_of (Q P : Params) (H : Fin 0 → HeavyLepton)
    (hmass : Q.mass = P.mass) (hcoeff : Q.loopCoeff = P.loopCoeff) :
    vertexOrderFive Q (leptonFlavors P H) = QED.TwoLoop.vertexOrderFive Q := by
  unfold vertexOrderFive
  rw [onePIFunction₂_leptonFlavors_zero_of Q P H hmass hcoeff]
  rfl

/-- (E₃) **The electron alone: the vertex.** -/
theorem vertexOrderFive_leptonFlavors_zero' (P : Params) (H : Fin 0 → HeavyLepton) :
    vertexOrderFive P (leptonFlavors P H) = QED.TwoLoop.vertexOrderFive P :=
  vertexOrderFive_leptonFlavors_zero_of P P H rfl rfl

/-- (E₃′) **The electron alone: the limit predicate.** -/
theorem isVertexOrderFiveLimit_leptonFlavors_zero_iff' (P : Params) (H : Fin 0 → HeavyLepton)
    (p' p : Fin 4 → ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    IsVertexOrderFiveLimit P (leptonFlavors P H) p' p V ↔
      QED.TwoLoop.IsVertexOrderFiveLimit P p' p V := by
  have h : ∀ ε : ℝ, vertexOrderFive { P with ε := ε } (leptonFlavors P H) =
      QED.TwoLoop.vertexOrderFive { P with ε := ε } := fun ε =>
    vertexOrderFive_leptonFlavors_zero_of _ P H rfl rfl
  simp only [IsVertexOrderFiveLimit, QED.TwoLoop.IsVertexOrderFiveLimit, h]

/-! ### (E₄): the photon condition with the electron alone -/

/-- The lightlike momentum `k = (1, 1, 0, 0)`. -/
def nullMomentum : Fin 4 → ℝ := ![1, 1, 0, 0]

theorem dot_nullMomentum : Minkowski.dot nullMomentum nullMomentum = 0 := by
  simp [Minkowski.dot, Minkowski.metric, nullMomentum, Fin.sum_univ_four]

/-- With no heavy lepton, the regulated two-photon function of the successor at order `2` is
packet 6a's (X₂₈). -/
theorem onePIFunction₂_leptonFlavors_zero_polarization (P : Params) (H : Fin 0 → HeavyLepton)
    (ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    onePIFunction₂ { P with ε := ε } (leptonFlavors P H) 0 2 2 ![] ![] ![k, -k] ![] ![]
        ![μ, ν] =
      QED.WickModel.onePIFunction { P with ε := ε } 0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν] := by
  rw [onePIFunction₂_leptonFlavors_zero_of { P with ε := ε } P H rfl rfl]
  exact QED.WickModel.onePIFunction₂_eq_onePIFunction _ 0 2 2 (by norm_num) _ _ _ _ _ _

/-- (E₄) **The electron alone: the photon condition.** -/
theorem isPhotonOnShell_leptonFlavors_zero_iff' (P : Params) (H : Fin 0 → HeavyLepton)
    (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) :
    IsPhotonOnShell P (leptonFlavors P H) ↔
      QED.WickModel.IsPhotonOnShell P hm hM₁ hM₂ hPV₁ hPV₂ := by
  have hspec := (QED.WickModel.vacuumPolarization_spec P hm hM₁ hM₂ hPV₁ hPV₂).1
  have hneg : -(4 * P.m ^ 2) < 0 := neg_lt_zero.mpr (by positivity)
  have hsub : ∀ (k : Fin 4 → ℝ) (hk : -(4 * P.m ^ 2) < Minkowski.dot k k),
      Minkowski.dot k k = 0 →
        (⟨_, hk⟩ : {s : ℝ // -(4 * P.m ^ 2) < s}) = ⟨0, hneg⟩ :=
    fun k _ h0 => Subtype.ext h0
  simp only [IsPhotonOnShell, QED.WickModel.IsPhotonOnShell,
    onePIFunction₂_leptonFlavors_zero_polarization]
  constructor
  · intro h
    have hk : -(4 * P.m ^ 2) < Minkowski.dot nullMomentum nullMomentum := by
      rw [dot_nullMomentum]; exact hneg
    have h2 := hspec nullMomentum hk 0 0
    have h1 := h nullMomentum dot_nullMomentum 0 0
    have := tendsto_nhds_unique h2 h1
    rw [hsub _ hk dot_nullMomentum, dot_nullMomentum] at this
    simpa [Minkowski.metric, nullMomentum] using this
  · intro h0 k hk0 μ ν
    have hk : -(4 * P.m ^ 2) < Minkowski.dot k k := by rw [hk0]; exact hneg
    have h2 := hspec k hk μ ν
    rw [hsub k hk hk0, h0, zero_mul] at h2
    exact h2

end QED.Lepton.Proof

end
