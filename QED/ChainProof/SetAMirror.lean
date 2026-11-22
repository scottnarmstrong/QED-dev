/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.GradedMirrorConj
public import QED.ChainProof.SetAPauliLink

/-!
# The fixed-`ε` mirror identity of the set (a) family vertex

Helper level for (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`, discharging the
open statement `QED.ChainProof.SetAPauli.SetAMirrorAt` of `QED/ChainProof/SetAPauliLink.lean`.

* `isSetA_ccC`: the set (a) contractions (A₁) are closed under charge conjugation
  `QED.ChainProof.Conj.ccC` (every fermion line reversed): `a ↔ c`, `sa ↔ sc`, `x ↔ y`, and on a
  closed-loop insertion `u ↔ w`, since `σ` and `σ⁻¹` have the same cycles.
* **`setAMirrorAt`**: `SetAMirrorAt P₀` holds for every `P₀`, unconditionally: the selection
  `IsOnePI ∧ IsSetA` is closed under `ccC` (`QED.ChainProof.GradedMirror.isOnePI_ccC`) and implies
  one-particle irreducibility, so the generic mirror identity
  `QED.ChainProof.GradedMirror.chargeConj_familyVertex` applies at every `ε`, all regulators and
  all counterterm data, counterterm vertices (`photonCt`, `gaugeCt`, `fermionCt`) included.
* `setAPauliLink_of_nested'`, `setAFixedLink_of_nested'`: the Pauli link and the fixed link of
  (HA₆) without the mirror hypothesis.
-/

@[expose] public section

open Complex Matrix
open QED.WickModel (Params Contraction IsOnePI)

namespace QED.ChainProof.SetAMirror

open QED.ChainProof.Conj QED.ChainProof.GradedMirror

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- **The set (a) contractions are closed under charge conjugation.** -/
theorem isSetA_ccC {C : Contraction 1 1 κ} (hC : ThreeLoop.IsSetA C) :
    ThreeLoop.IsSetA (ccC C) := by
  obtain ⟨a, b, c, sa, sb, sc, x, y, hka, hkb, hkc, h0a, hab, hbc, hc0, hsb, hext, hsa, hsc, hax,
    hcy, hins⟩ := hC
  refine ⟨c, b, a, sc, sb, sa, y, x, hkc, hkb, hka, (ccC_apply_eq_iff C _ _).mpr hc0,
    (ccC_apply_eq_iff C _ _).mpr hbc, (ccC_apply_eq_iff C _ _).mpr hab,
    (ccC_apply_eq_iff C _ _).mpr h0a, hsb, hext, hsc, hsa, hcy, hax, ?_⟩
  rcases hins with ⟨hk, hyx, hne, hall⟩ | ⟨u, w, hu, hw, hnot, huw, hall⟩
  · refine Or.inl ⟨by rw [hyx]; exact hk, hyx.symm, Ne.symm hne, fun t => ?_⟩
    rcases hall t with h | h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (h.trans hyx.symm)))
  · refine Or.inr ⟨w, u, hw, hu, fun i h => ?_, ?_, fun t => ?_⟩
    · rw [ccC_fst, Equiv.Perm.sameCycle_inv] at h
      exact hnot i (h.trans huw.symm)
    · rw [ccC_fst, Equiv.Perm.sameCycle_inv]
      exact huw.symm
    · rcases hall t with h | h | h | ⟨v, hv, h⟩
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · refine Or.inr (Or.inr (Or.inr ⟨v, hv, ?_⟩))
        rw [ccC_fst, Equiv.Perm.sameCycle_inv]
        exact huw.symm.trans h

theorem isSetA_ccC_iff (C : Contraction 1 1 κ) : ThreeLoop.IsSetA (ccC C) ↔ ThreeLoop.IsSetA C :=
  ⟨fun h => by simpa using isSetA_ccC h, isSetA_ccC⟩

/-- **The fixed-`ε` mirror identity of the set (a) family vertex**, for all parameters, flavour
and counterterm data and momenta: `C V_ε(p', p)^μᵀ C = Γ V_ε(p, p')^μ Γ`. -/
theorem chargeConj_familyVertex_setA (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : QED.Lepton.Flavors F) (D : Graded.Counterterms F) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    QED.Dirac.chargeConj *
        (Graded.familyVertex P Φ D (fun C _ => IsOnePI C ∧ ThreeLoop.IsSetA C) 7 p' p μ)ᵀ *
        QED.Dirac.chargeConj =
      chir * Graded.familyVertex P Φ D (fun C _ => IsOnePI C ∧ ThreeLoop.IsSetA C) 7 p p' μ *
        chir :=
  chargeConj_familyVertex P Φ D _ (fun _ _ h => ⟨isOnePI_ccC h.1, isSetA_ccC h.2⟩)
    (fun _ _ h => h.1) 7 p' p μ

/-- **`SetAMirrorAt` holds**, unconditionally. -/
theorem setAMirrorAt (P₀ : Params) : SetAPauli.SetAMirrorAt P₀ :=
  fun _ _ _ _ _ _ D _ _ _ _ p' p _ μ =>
    chargeConj_familyVertex_setA _ _ D p' p μ

/-- **The set (a) Pauli link** from the limit link, covariance, the nested value and the
regularity of the photon function; the mirror obligation is discharged. -/
theorem setAPauliLink_of_nested' {P₀ : Params} {R : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ} (he : P₀.e ≠ 0)
    (hm : 0 < P₀.m) (hL : SetAPauli.SetALimitLink P₀) (hC : SetAPauli.SetACovLink P₀)
    (hN : SetAPauli.SetANestedAt P₀ R) (hR : SetAPauli.SetAPhotonReg P₀ R) :
    SetAPauli.SetAPauliLink P₀ (SetAPauli.setAPauliValue P₀ R) :=
  SetAPauli.setAPauliLink_of_nested he hm hL hC (setAMirrorAt P₀) hN hR

/-- **The fixed link of (HA₆)**; the mirror obligation is discharged. -/
theorem setAFixedLink_of_nested' {P₀ : Params} {R : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ} (he : P₀.e ≠ 0)
    (hm : 0 < P₀.m) (hL : SetAPauli.SetALimitLink P₀) (hC : SetAPauli.SetACovLink P₀)
    (hN : SetAPauli.SetANestedAt P₀ R) (hR : SetAPauli.SetAPhotonReg P₀ R) :
    SetAPauli.SetAFixedLink P₀ (SetAPauli.setAPauliValue P₀ R) :=
  SetAPauli.setAFixedLink_of_nested he hm hL hC (setAMirrorAt P₀) hN hR

end QED.ChainProof.SetAMirror

end
