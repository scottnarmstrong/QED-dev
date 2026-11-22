/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitMRepB
public import QED.ChainProof.SetCLimCtCB
public import QED.ChainProof.SetCLimCtS
public import QED.ChainProof.SetCLinkIntD

/-!
# Set (c), the 36 main classes: relabelling, T1 values and the `δ₃` split

Helper level for the per-class links `QED.ChainProof.SetCPauli.SetCClassLim`, `SetCClassCov` of
the 36 two-loop-outer classes (`MainIdx`): `repB i` (the bubble on a photon line of a two-loop
skeleton, three loops) and `repD i s` (the `δ₃` element there, two loops).

**The relabelling of `repD`** (kernel evaluation, all twenty-four orbits). As for `repB`
(`QED.ChainProof.SetCUnitM.repB_sigma`), the open line of `repD i s` runs opposite to that of
the class representative: vertex `t` of `Class5.rep (repBClass i)` is vertex `4 - t` of
`repD i s`. With the `photonCt` vertex `5` bypassed, the photon pairing is that of the class
representative, and the element sits on the class line `repBElemLine i`, whose line index is
`pvLines (repBSlot i)`. So `repD i s` has the class and slot of `repB i`, for both `s`.

* `fvD`, `embFD`, `embPD`, `bypassD`;
* **`repD_sigma`**, **`repD_tau_bypass`**, **`repD_elem_ct`**.

**T1 values at the set (c) data.**

* **`mainVal_inl_eq`**: `mainVal (.inl i) = -V₂(repB i)`, the T1 value `contractionValue₂` at
  `{regParams … with ε}` (the bubble at the set (c) flavours);
* **`mainVal_inr_eq`**: `mainVal (.inr (i, s)) = V₂(repD i s)` at the open-line parameters
  `ctParamsLevel … 0` (the level-`0` share counterterms, `δ₃ = e² d₃(0)`).

**The `δ₃` split of `repD`** (every `ε > 0`, any flavours and counterterms). The `photonCt`
factor is `ctGD + ctKD` (`k² g^{ab}` and `k^a k^b`, `QED.ChainProof.SetCLink.ctF_eq`):

* `dGIntegrand`, `dKIntegrand`: the two parts of the integrand;
* **`contractionValue_kD_split`**: for every `kD` contraction with the data of
  `QED.ChainProof.SetCLink.classIntA_of_data`, both parts are integrable at both stages and the
  graded value is the sum of their joint energy-first integrals;
* **`contractionValue_repD_split`**, **`mainVal_inr_split`**: the twenty-four orbits.
-/

@[expose] public section

open Complex Matrix Filter Topology
open QED.WickModel (Params IsOnePI Contraction contractionValue₂ loopCount lineMomentum₂
  FermionLine PhotonLine Line photonMomentum₂)

namespace QED.ChainProof.SetCMain

open QED.TwoLoop.Enumeration QED.ChainProof.SetCLink QED.ChainProof.SetCUnitM
open QED.ChainProof.SetCPauli QED.ChainProof.SetALink
open QED.ChainProof.Enum (pc)
open QED.ChainProof.SetAPauli (regParams regFlavors)

/-! ### The relabelling of `repD` -/

theorem kD_castSucc : ∀ t : Fin 5, kD (Fin.castSucc t) ≠ .photonCt := by decide

/-- The open-line fermion vertex `t` of `kD`. -/
def fvD (t : Fin 5) : Wick.FermionVertex kD := ⟨Fin.castSucc t, kD_castSucc t⟩

/-- The fermion fields of the class representative inside those of `repD i s`: vertex `t` of the
class is vertex `4 - t` of `repD i s`. -/
def embFD : Fin 1 ⊕ Wick.FermionVertex (gauges 5) → Fin 1 ⊕ Wick.FermionVertex kD
  | .inl a => .inl a
  | .inr v => .inr (fvD (Fin.rev v.1))

/-- The photon fields of the class representative inside those of `repD i s`. -/
def embPD : Fin 1 ⊕ Wick.PhotonSlot (gauges 5) → Fin 1 ⊕ Wick.PhotonSlot kD
  | .inl a => .inl a
  | .inr y => .inr (plD (Fin.rev y.1))

/-- A photon pairing of `kD` with the path through the `photonCt` fields bypassed. -/
def bypassD (τ : Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot kD)) (x : Fin 1 ⊕ Wick.PhotonSlot kD) :
    Fin 1 ⊕ Wick.PhotonSlot kD :=
  if τ x = .inr (pc kD 5 0) then τ (.inr (pc kD 5 1)) else
    if τ x = .inr (pc kD 5 1) then τ (.inr (pc kD 5 0)) else τ x

/-- **The fermion pairing of `repD`**: the open line of `repD i s` is that of the class
representative of `repB i`, vertex `t` of the class being vertex `4 - t` of `repD i s`. -/
theorem repD_sigma : ∀ i s x,
    (repD i s).1.1 (embFD x) = embFD ((repBClass i).rep.1.1 x) := by
  decide +kernel

/-- **The photon pairing of `repD`**: with the `photonCt` vertex bypassed, it is that of the class
representative of `repB i`. -/
theorem repD_tau_bypass : ∀ i s x,
    bypassD (repD i s).1.2 (embPD x) = embPD ((repBClass i).rep.1.2 x) := by
  decide +kernel

/-- **The element of `repD i s` sits on the element line of `repB i`** (line index
`pvLines (repBSlot i)`, `QED.ChainProof.SetCUnitM.lineIdx_repBElemLine`). -/
theorem repD_elem_ct : ∀ i s,
    (repD i s).1.2 (embPD (.inr (ps5 (repBLow i)))) = .inr (pc kD 5 0) ∨
      (repD i s).1.2 (embPD (.inr (ps5 (repBLow i)))) = .inr (pc kD 5 1) := by
  decide +kernel

/-! ### T1 values at the set (c) data -/

variable {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}

/-- **The bubble classes as T1 values**: at the set (c) data, `mainVal (.inl i)` is minus the T1
value of `repB i` at `{regParams … with ε}`. -/
theorem mainVal_inl_eq (ε : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (i : Fin 12) :
    mainVal { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (shareCt D s) p' p μ (.inl i) =
      -Matrix.of fun α β => contractionValue₂ { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
        (repB i) (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β)
        (fun _ => μ) := by
  simp only [mainVal, clsVal]
  congr 1
  ext α β
  simp only [Matrix.of_apply]
  exact contractionValue_gauges_regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ ε (shareCt D s)
    (C := (repB i : Contraction 1 1 (gauges 7))) _ _ _ _ _ _

/-- **The `δ₃` classes as T1 values**: `mainVal (.inr (i, s))` is the T1 value of `repD i s` at
the open-line parameters with the level-`0` counterterms (any parameters, flavours and
counterterms). -/
theorem mainVal_inr_eq (Q : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (i : Fin 12) (t : Fin 2) :
    mainVal Q Φ D p' p μ (.inr (i, t)) =
      Matrix.of fun α β => contractionValue₂ (ctParamsLevel Q Φ D 0) (repD i t)
        (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) := by
  simp only [mainVal, clsVal]
  ext α β
  simp only [Matrix.of_apply]
  exact contractionValue_eq_ctLevel Q Φ D (repD i t) (cycle_repD i t) 0 _ _ _ _ _ _

/-! ### The `δ₃` split of `repD` -/

section Split

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (δ₃ : ℝ)
  (C : Contraction 1 1 kD) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)

/-- The `k² g^{ab}` (transverse) part of the integrand of a `kD` contraction, with the loop
measure `(2π)⁻⁸`. -/
noncomputable def dGIntegrand (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * ∑ α, ∑ β, ∑ lor,
    extI C αOut βIn μ α β lor *
      (ctGD δ₃ lor (photonMomentum₂ C kIn (lineMomentum₂ C pOut pIn kIn ℓ) (pc kD 5 0)) *
        (gV P.e α β lor *
          lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) (lineMomentum₂ C pOut pIn kIn ℓ)))

/-- The `k^a k^b` (longitudinal) part of the integrand of a `kD` contraction, with the loop
measure `(2π)⁻⁸`. -/
noncomputable def dKIntegrand (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * ∑ α, ∑ β, ∑ lor,
    extI C αOut βIn μ α β lor *
      (ctKD δ₃ lor (photonMomentum₂ C kIn (lineMomentum₂ C pOut pIn kIn ℓ) (pc kD 5 0)) *
        (gV P.e α β lor *
          lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) (lineMomentum₂ C pOut pIn kIn ℓ)))

end Split

/-- **The `δ₃` split of a `kD` contraction**: at every `ε > 0`, with the data of
`QED.ChainProof.SetCLink.classIntA_of_data`, the transverse and longitudinal parts are
integrable at both stages and the graded value is the sum of their joint energy-first
integrals. -/
theorem contractionValue_kD_split (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (hε : 0 < P.ε) (C : Contraction 1 1 kD)
    (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) (hL : loopCount C = 2)
    (hG : GData C) (hK : WardData C ∨ ExtData C) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2
        (dGIntegrand P Φ (P.e ^ 2 * D.d₃ 0) C pOut pIn kIn αOut βIn μ) ∧
      QED.TwoLoop.jointEnergyFirstIntegrable 2
        (dKIntegrand P Φ (P.e ^ 2 * D.d₃ 0) C pOut pIn kIn αOut βIn μ) ∧
      Graded.contractionValue P Φ D C 0 pOut pIn kIn αOut βIn μ =
        QED.TwoLoop.jointEnergyFirstIntegral 2
            (dGIntegrand P Φ (P.e ^ 2 * D.d₃ 0) C pOut pIn kIn αOut βIn μ) +
          QED.TwoLoop.jointEnergyFirstIntegral 2
            (dKIntegrand P Φ (P.e ^ 2 * D.d₃ 0) C pOut pIn kIn αOut βIn μ) := by
  obtain ⟨g, hρ, h₀, h₁⟩ := hG
  have hA := jointEnergyFirstIntegrable_ctG P Φ hε (P.e ^ 2 * D.d₃ 0) C pOut pIn kIn hmom
    αOut βIn μ g hρ h₀ h₁
  have hB : QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ => ∑ α, ∑ β, ∑ lor,
      extI C αOut βIn μ α β lor *
        (ctKD (P.e ^ 2 * D.d₃ 0) lor
          (photonMomentum₂ C kIn (lineMomentum₂ C pOut pIn kIn ℓ) (pc kD 5 0)) *
          (gV P.e α β lor *
            lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) (lineMomentum₂ C pOut pIn kIn ℓ))) := by
    rcases hK with ⟨fa, fb, gW, gK, sW, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ |
      ⟨f0, f3, gW, gK, sW, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    · exact jointEnergyFirstIntegrable_ctK_ward P Φ hε _ C pOut pIn kIn hmom αOut βIn μ fa fb
        gW gK sW h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    · exact jointEnergyFirstIntegrable_ctK_ext P Φ hε _ C pOut pIn kIn hmom αOut βIn μ f0 f3
        gW gK sW h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hA' : QED.TwoLoop.jointEnergyFirstIntegrable 2
      (dGIntegrand P Φ (P.e ^ 2 * D.d₃ 0) C pOut pIn kIn αOut βIn μ) :=
    QED.TwoLoop.ClassLimit.jointEnergyFirstIntegrable_const_mul _ hA
  have hB' : QED.TwoLoop.jointEnergyFirstIntegrable 2
      (dKIntegrand P Φ (P.e ^ 2 * D.d₃ 0) C pOut pIn kIn αOut βIn μ) :=
    QED.TwoLoop.ClassLimit.jointEnergyFirstIntegrable_const_mul _ hB
  refine ⟨hA', hB', ?_⟩
  rw [← QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add hA' hB']
  unfold Graded.contractionValue
  rw [hL]
  congr 1
  funext ℓ
  rw [regulatedAmplitude_kD P Φ D hε.ne' C hcyc]
  simp only [dGIntegrand, dKIntegrand, ctF_eq, add_mul, mul_add, Finset.sum_add_distrib]

/-- **The `δ₃` split of the twenty-four orbits `repD i s`** (every `ε > 0`). -/
theorem contractionValue_repD_split (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (hε : 0 < P.ε) (i : Fin 12) (t : Fin 2)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2
        (dGIntegrand P Φ (P.e ^ 2 * D.d₃ 0) (repD i t) pOut pIn kIn αOut βIn μ) ∧
      QED.TwoLoop.jointEnergyFirstIntegrable 2
        (dKIntegrand P Φ (P.e ^ 2 * D.d₃ 0) (repD i t) pOut pIn kIn αOut βIn μ) ∧
      Graded.contractionValue P Φ D (repD i t) 0 pOut pIn kIn αOut βIn μ =
        QED.TwoLoop.jointEnergyFirstIntegral 2
            (dGIntegrand P Φ (P.e ^ 2 * D.d₃ 0) (repD i t) pOut pIn kIn αOut βIn μ) +
          QED.TwoLoop.jointEnergyFirstIntegral 2
            (dKIntegrand P Φ (P.e ^ 2 * D.d₃ 0) (repD i t) pOut pIn kIn αOut βIn μ) :=
  contractionValue_kD_split P Φ D hε _ (cycle_repD i t) (loopCount_repD i t)
    (data_repD i t).1 (data_repD i t).2 hmom αOut βIn μ

/-- **The `δ₃` classes split** into their transverse and longitudinal parts, entrywise, at
every `ε > 0`. -/
theorem mainVal_inr_split (Q : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (hε : 0 < Q.ε) (p' p : Fin 4 → ℝ)
    (μ : Fin 4) (i : Fin 12) (t : Fin 2) (α β : Fin 4) :
    mainVal Q Φ D p' p μ (.inr (i, t)) α β =
      QED.TwoLoop.jointEnergyFirstIntegral 2
          (dGIntegrand Q Φ (Q.e ^ 2 * D.d₃ 0) (repD i t) (fun _ => p') (fun _ => p)
            (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ)) +
        QED.TwoLoop.jointEnergyFirstIntegral 2
          (dKIntegrand Q Φ (Q.e ^ 2 * D.d₃ 0) (repD i t) (fun _ => p') (fun _ => p)
            (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ)) := by
  simp only [mainVal, clsVal, Matrix.of_apply]
  exact (contractionValue_repD_split Q Φ D hε i t (by simp) _ _ _).2.2

end QED.ChainProof.SetCMain

end
