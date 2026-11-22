/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.GradedMirrorConj
public import QED.ChainProof.SetCPauliLink

/-!
# The fixed-`ε` mirror identity of the set (c) family vertex

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, discharging the
open statement `QED.ChainProof.SetCPauli.SetCMirrorAt` of `QED/ChainProof/SetCPauliLink.lean`.

* `isSetC_ccC`: the set (c) contractions (Sc₃) are closed under charge conjugation
  `QED.ChainProof.Conj.ccC` (every fermion line reversed), at the same grading. The level
  condition on `photonCt` vertices reads only `κ` and `g`; "on the open line" (sharing the cycle
  of `Ψ(x)`) is unchanged, since `σ` and `σ⁻¹` have the same cycles; and a bubble `u → w → u`
  stays a bubble, `u ↔ w`.
* **`setCMirrorAt`**: `SetCMirrorAt P₀` holds for every `P₀`, unconditionally: the selection
  `IsOnePI ∧ IsSetC` is closed under `ccC` (`QED.ChainProof.GradedMirror.isOnePI_ccC`) and implies
  one-particle irreducibility, so the generic mirror identity
  `QED.ChainProof.GradedMirror.chargeConj_familyVertex` applies at every `ε`, all regulators and
  all counterterm data (in particular those with the VP share substituted), counterterm vertices
  (`photonCt`, `gaugeCt`, `fermionCt`) included.
* `setCPauliLink_of_pauliAt'`, `setCFixedLink_of_pauliAt'`: the Pauli link and the fixed link of
  (HS₆) without the mirror hypothesis.
-/

@[expose] public section

open Complex Matrix
open QED.WickModel (Params Contraction IsOnePI)

namespace QED.ChainProof.SetCMirror

open QED.ChainProof.Conj QED.ChainProof.GradedMirror

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- **Being on the open line is unchanged by charge conjugation.** -/
theorem sameCycle_ccC_iff (C : Contraction 1 1 κ) (v : Wick.FermionVertex κ) :
    ((ccC C).1.1).SameCycle (.inl 0) (.inr v) ↔ (C.1.1).SameCycle (.inl 0) (.inr v) := by
  rw [ccC_fst, Equiv.Perm.sameCycle_inv]

/-- **The set (c) contractions are closed under charge conjugation**, at the same grading. -/
theorem isSetC_ccC {C : Contraction 1 1 κ} {g : Graded.Grading κ} (hC : ThreeLoop.IsSetC C g) :
    ThreeLoop.IsSetC (ccC C) g := by
  obtain ⟨hph, hD | hB | hS⟩ := hC
  · obtain ⟨t₀, k0, hall⟩ := hD
    refine ⟨hph, Or.inl ⟨t₀, k0, fun t => ?_⟩⟩
    rcases hall t with h | ⟨v, hv, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨v, hv, (sameCycle_ccC_iff C v).mpr h⟩
  · obtain ⟨u, w, ku, kw, huw, su, sw, hall⟩ := hB
    refine ⟨hph, Or.inr (Or.inl ⟨w, u, kw, ku, Ne.symm huw, (ccC_apply_eq_iff C _ _).mpr su,
      (ccC_apply_eq_iff C _ _).mpr sw, fun t => ?_⟩)⟩
    rcases hall t with h | h | ⟨v, hv, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨v, hv, (sameCycle_ccC_iff C v).mpr h⟩)
  · obtain ⟨hall, t₀, hg1, hu⟩ := hS
    refine ⟨hph, Or.inr (Or.inr ⟨fun t => ?_, t₀, hg1, hu⟩)⟩
    obtain ⟨v, hv, h⟩ := hall t
    exact ⟨v, hv, (sameCycle_ccC_iff C v).mpr h⟩

theorem isSetC_ccC_iff (C : Contraction 1 1 κ) (g : Graded.Grading κ) :
    ThreeLoop.IsSetC (ccC C) g ↔ ThreeLoop.IsSetC C g :=
  ⟨fun h => by simpa using isSetC_ccC h, isSetC_ccC⟩

/-- **The fixed-`ε` mirror identity of the set (c) family vertex**, for all parameters, flavour
and counterterm data and momenta: `C V_ε(p', p)^μᵀ C = Γ V_ε(p, p')^μ Γ`. -/
theorem chargeConj_familyVertex_setC (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : QED.Lepton.Flavors F) (D : Graded.Counterterms F) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    QED.Dirac.chargeConj *
        (Graded.familyVertex P Φ D (fun C g => IsOnePI C ∧ ThreeLoop.IsSetC C g) 7 p' p μ)ᵀ *
        QED.Dirac.chargeConj =
      chir * Graded.familyVertex P Φ D (fun C g => IsOnePI C ∧ ThreeLoop.IsSetC C g) 7 p p' μ *
        chir :=
  chargeConj_familyVertex P Φ D _ (fun _ _ h => ⟨isOnePI_ccC h.1, isSetC_ccC h.2⟩)
    (fun _ _ h => h.1) 7 p' p μ

/-- **`SetCMirrorAt` holds**, unconditionally. -/
theorem setCMirrorAt (P₀ : Params) : SetCPauli.SetCMirrorAt P₀ :=
  fun _ _ _ _ _ _ D s _ _ _ _ p' p _ μ =>
    chargeConj_familyVertex_setC _ _ (SetCPauli.shareCt D s) p' p μ

/-- **The set (c) Pauli link** from the limit link, covariance and the canonical Pauli limit;
the mirror obligation is discharged. -/
theorem setCPauliLink_of_pauliAt' {P₀ : Params} {b : ℝ → ℝ → ℝ → ℝ → ℝ} (he : P₀.e ≠ 0)
    (hm : 0 < P₀.m) (hL : SetCPauli.SetCLimitLink P₀) (hC : SetCPauli.SetCCovLink P₀)
    (hB : SetCPauli.SetCPauliAt P₀ b) :
    SetCPauli.SetCPauliLink P₀ (SetCPauli.setCPauliValue P₀ b) :=
  SetCPauli.setCPauliLink_of_pauliAt he hm hL hC (setCMirrorAt P₀) hB

/-- **The fixed link of (HS₆)**; the mirror obligation is discharged. -/
theorem setCFixedLink_of_pauliAt' {P₀ : Params} {b : ℝ → ℝ → ℝ → ℝ → ℝ} (he : P₀.e ≠ 0)
    (hm : 0 < P₀.m) (hL : SetCPauli.SetCLimitLink P₀) (hC : SetCPauli.SetCCovLink P₀)
    (hB : SetCPauli.SetCPauliAt P₀ b) :
    SetCPauli.SetCFixedLink P₀ (SetCPauli.setCPauliValue P₀ b) :=
  SetCPauli.setCFixedLink_of_pauliAt he hm hL hC (setCMirrorAt P₀) hB

end QED.ChainProof.SetCMirror

end
