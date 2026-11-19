/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0SepGroup
public import QED.GradedProof.X0ClosedFlavor2
public import QED.GradedProof.X0Sep

/-!
# (X₀): the index terms of a two-loop contraction whose loops share no line

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57). Let `C` be a
contraction of `gauge` vertices with two loop momenta in which no line carries both
(`loopCoeff C l 0 = 0 ∨ loopCoeff C l 1 = 0`). Then one index term of the amplitude (G₃) at the
zero grading is a constant (the vertex factors, the lines carrying no loop momentum) times a
product of the lines along `ℓ₀` and the lines along `ℓ₁` (`ampTerm_sep`). Each group is either
a closed loop (`grpZ C j`: the vertices whose outgoing fermion line carries `ℓ_j`), whose
flavour sum satisfies (T₉′) at one loop (`jointEnergyFirstIntegrable_closedGrp`), or a group of
open-line and photon lines passing the one-loop count (`jointEnergyFirstIntegrable_openGrp`);
the two combine by Fubini (`jointEnergyFirstIntegrable_two_mul`).
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0

open QED.Graded
open QED.WickModel

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind} {F : Type} {C : Contraction 1 nA κ}

/-- The fermion vertices whose outgoing fermion line carries the loop momentum `ℓ_j`. -/
def grpZ (C : Contraction 1 nA κ) (j : ℕ) (s : Wick.FermionVertex κ) : Prop :=
  ∃ h : (C.1.1 (.inr s)).isRight, loopCoeff C (.inl ⟨s, h⟩) j ≠ 0

instance (C : Contraction 1 nA κ) (j : ℕ) : DecidablePred (grpZ C j) := fun _ => by
  unfold grpZ; infer_instance

theorem grpZ_iff (j : ℕ) (f : FermionLine C) : grpZ C j f.1 ↔ loopCoeff C (.inl f) j ≠ 0 :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨f.2, h⟩⟩

/-- A product of fermion propagator entries over a set of fermion lines. -/
noncomputable def fProd (P : Params) (Φ : Lepton.Flavors F) (φ : Flavoring F κ)
    (α β : Wick.FermionVertex κ → Fin 4) (S : Finset (FermionLine C))
    (k : FermionLine C → Fin 4 → ℝ) : ℂ :=
  ∏ f ∈ S, (1 / I) * QED.OneLoop.electronPropagator (Φ.mass (φ f.1)) P.ε (k f) (β f.1) (α f.tail)

/-- A product of photon propagator entries over a set of photon lines. -/
noncomputable def gProd (P : Params) (lor : Wick.PhotonSlot κ → Fin 4) (S : Finset (PhotonLine C))
    (k : PhotonLine C → Fin 4 → ℝ) : ℂ :=
  ∏ g ∈ S, (1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k g) (lor g.1) (lor g.head)

theorem fProd_congr (P : Params) (Φ : Lepton.Flavors F) {φ ψ : Flavoring F κ}
    (α β : Wick.FermionVertex κ → Fin 4) {S : Finset (FermionLine C)}
    (h : ∀ f ∈ S, φ f.1 = ψ f.1) (k : FermionLine C → Fin 4 → ℝ) :
    fProd P Φ φ α β S k = fProd P Φ ψ α β S k :=
  Finset.prod_congr rfl fun f hf => by rw [h f hf]

/-- A product over lines each carrying at most one of two loop momenta, split by the loop
momentum carried (the symmetric form of `prod_sep`). -/
theorem prod_sep₂ {T : Type*} [Fintype T] (X : T → (Fin 4 → ℝ) → ℂ) (c₀ c₁ : T → ℤ)
    (hF : ∀ f, c₀ f = 0 ∨ c₁ f = 0) (p : T → Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∏ f, X f ((c₀ f : ℝ) • ℓ 0 + (c₁ f : ℝ) • ℓ 1 + p f) =
      (∏ f ∈ Finset.univ.filter (fun f => c₀ f = 0 ∧ c₁ f = 0), X f (p f)) *
        ((∏ f ∈ Finset.univ.filter (fun f => c₀ f ≠ 0), X f ((c₀ f : ℝ) • ℓ 0 + p f)) *
          ∏ f ∈ Finset.univ.filter (fun f => c₁ f ≠ 0), X f ((c₁ f : ℝ) • ℓ 1 + p f)) := by
  rw [prod_sep X c₀ c₁ hF p ℓ]
  have e1 : Finset.univ.filter (fun f => ¬ c₀ f ≠ 0 ∧ c₁ f ≠ 0) =
      Finset.univ.filter (fun f => c₁ f ≠ 0) :=
    Finset.filter_congr fun f _ => by rcases hF f with h | h <;> simp [h]
  have e2 : Finset.univ.filter (fun f => ¬ c₀ f ≠ 0 ∧ ¬ c₁ f ≠ 0) =
      Finset.univ.filter (fun f => c₀ f = 0 ∧ c₁ f = 0) :=
    Finset.filter_congr fun f _ => by simp
  rw [e1, e2]
  ring

/-- The fermion lines carrying `ℓ_j`. -/
def grpF (C : Contraction 1 nA κ) (j : ℕ) : Finset (FermionLine C) :=
  Finset.univ.filter fun f => loopCoeff C (.inl f) j ≠ 0

/-- The photon lines carrying `ℓ_j`. -/
def grpG (C : Contraction 1 nA κ) (j : ℕ) : Finset (PhotonLine C) :=
  Finset.univ.filter fun g => loopCoeff C (.inr g) j ≠ 0

/-- The fermion lines carrying no loop momentum. -/
def treeF (C : Contraction 1 nA κ) : Finset (FermionLine C) :=
  Finset.univ.filter fun f => loopCoeff C (.inl f) 0 = 0 ∧ loopCoeff C (.inl f) 1 = 0

/-- The photon lines carrying no loop momentum. -/
def treeG (C : Contraction 1 nA κ) : Finset (PhotonLine C) :=
  Finset.univ.filter fun g => loopCoeff C (.inr g) 0 = 0 ∧ loopCoeff C (.inr g) 1 = 0

/-- The momentum of a fermion line along `ℓ_j`. -/
noncomputable def kF (C : Contraction 1 nA κ) (j : ℕ) (pOut pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (x : Fin 4 → ℝ) (f : FermionLine C) : Fin 4 → ℝ :=
  ((loopCoeff C (.inl f) j : ℤ) : ℝ) • x + extPart C pOut pIn kIn (.inl f)

/-- The momentum of a photon line along `ℓ_j`. -/
noncomputable def kG (C : Contraction 1 nA κ) (j : ℕ) (pOut pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (x : Fin 4 → ℝ) (g : PhotonLine C) : Fin 4 → ℝ :=
  ((loopCoeff C (.inr g) j : ℤ) : ℝ) • x + extPart C pOut pIn kIn (.inr g)

open scoped Classical in
/-- The constant part of an index term: external index constraints, vertex factors, lines
carrying no loop momentum. -/
noncomputable def sepConst (P : Params) (Φ : Lepton.Flavors F) (C : Contraction 1 nA κ)
    (φ : Flavoring F κ) (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) : ℂ :=
  (if (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
      (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
      (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) then 1 else 0) *
    (∏ t, Wick.vertexFactor P.e 0 0 0 0 0 α β lor 0 0 t) *
    fProd P Φ φ α β (treeF C) (fun f => extPart C pOut pIn kIn (.inl f)) *
    gProd P lor (treeG C) (fun g => extPart C pOut pIn kIn (.inr g))

/-- **An index term of a separated contraction of `gauge` vertices** is a constant times the
product of the lines along `ℓ₀` and the lines along `ℓ₁`. -/
theorem ampTerm_sep (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
    (hκ : ∀ t, κ t = .gauge) (hF : ∀ l : Line C, loopCoeff C l 0 = 0 ∨ loopCoeff C l 1 = 0)
    (φ : Flavoring F κ) (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ampTerm P Φ D C φ pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ α β lor =
      sepConst P Φ C φ pOut pIn kIn αOut βIn μ α β lor *
        ((fProd P Φ φ α β (grpF C 0) (kF C 0 pOut pIn kIn (ℓ 0)) *
          gProd P lor (grpG C 0) (kG C 0 pOut pIn kIn (ℓ 0))) *
        (fProd P Φ φ α β (grpF C 1) (kF C 1 pOut pIn kIn (ℓ 1)) *
          gProd P lor (grpG C 1) (kG C 1 pOut pIn kIn (ℓ 1)))) := by
  classical
  have hk : ∀ l : Line C, lineMomentum₂ C pOut pIn kIn ℓ l =
      ((loopCoeff C l 0 : ℤ) : ℝ) • ℓ 0 + ((loopCoeff C l 1 : ℤ) : ℝ) • ℓ 1 +
        extPart C pOut pIn kIn l := fun l => by
    rw [lineMomentum₂_eq_loopCoeff, Fin.sum_univ_two]
    rfl
  have hv : ∀ t, vf0 P D (flOf Φ φ t) (Φ.mass (flOf Φ φ t)) α β lor
      (psiMomentum₂ C pIn (lineMomentum₂ C pOut pIn kIn ℓ))
      (photonMomentum₂ C kIn (lineMomentum₂ C pOut pIn kIn ℓ)) t =
      Wick.vertexFactor P.e 0 0 0 0 0 α β lor 0 0 t := fun t => vf0_gauge _ _ _ _ _ _ _ _ _ t (hκ t)
  have hXF := prod_sep₂ (fun f k => (1 / I) * QED.OneLoop.electronPropagator
    (Φ.mass (φ f.1)) P.ε k (β f.1) (α f.tail)) (fun f => loopCoeff C (.inl f) 0)
    (fun f => loopCoeff C (.inl f) 1) (fun f => hF _) (fun f => extPart C pOut pIn kIn (.inl f)) ℓ
  have hYG := prod_sep₂ (fun g k => (1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k
    (lor g.1) (lor g.head)) (fun g => loopCoeff C (.inr g) 0)
    (fun g => loopCoeff C (.inr g) 1) (fun g => hF _) (fun g => extPart C pOut pIn kIn (.inr g)) ℓ
  beta_reduce at hXF hYG
  unfold ampTerm sepConst fProd gProd grpF grpG treeF treeG kF kG
  simp only [hv, hk]
  rw [hXF, hYG]
  ring

/-! ### Fubini, zero terms -/

/-- (T₉′) of the zero integrand, any number of loops. -/
theorem jointEnergyFirstIntegrable_zero_fun' {L : ℕ} :
    QED.TwoLoop.jointEnergyFirstIntegrable L fun _ => (0 : ℂ) :=
  ⟨fun _ => by simp, by simp⟩

/-- **Fubini for two one-loop factors.** -/
theorem jointEnergyFirstIntegrable_two_mul {A B : (Fin 4 → ℝ) → ℂ}
    (hA : QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ => A (ℓ 0))
    (hB : QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ => B (ℓ 0)) (z : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ => z * (A (ℓ 0) * B (ℓ 1)) := by
  have h := QED.TwoLoop.ClassLimit.jointEnergyFirstIntegrable_const_mul z
    (jointEnergyFirstIntegrable_mul hA hB)
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  rfl

/-- If the vertex factors do not vanish, every fermion vertex has a different-block index
pair. -/
theorem not_blk_of_prod_ne_zero (e : ℝ) (hκ : ∀ t, κ t = .gauge)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
    (h : ∏ t, Wick.vertexFactor e 0 0 0 0 0 α β lor 0 0 t ≠ 0) (s : Wick.FermionVertex κ) :
    ¬ blk (α s) = blk (β s) := fun hb =>
  (Finset.prod_ne_zero_iff.mp h) s.1 (Finset.mem_univ _)
    (vertexFactor_gauge_eq_zero_of_blk e α β lor s (hκ s.1) hb)

/-! ### The two kinds of groups -/

/-- **(T₉′) of a group of open-line and photon lines** carrying one loop momentum. -/
theorem jointEnergyFirstIntegrable_openGrp (P : Params) (Φ : Lepton.Flavors F)
    (hε : 0 < P.ε) (ψ : Flavoring F κ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (j : ℕ) (pOut pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (h3 : (grpF C j).card ≤ 3)
    (h4 : 4 < (grpF C j).card + 4 * (grpG C j).card) :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ =>
      fProd P Φ ψ α β (grpF C j) (kF C j pOut pIn kIn (ℓ 0)) *
        gProd P lor (grpG C j) (kG C j pOut pIn kIn (ℓ 0)) := by
  classical
  have h := jointEnergyFirstIntegrable_entries (F := {f // f ∈ grpF C j})
    (G := {g // g ∈ grpG C j}) (fun f => ((loopCoeff C (.inl f.1) j : ℤ) : ℝ))
    (fun f => Int.cast_ne_zero.mpr (Finset.mem_filter.mp f.2).2)
    (fun f => extPart C pOut pIn kIn (.inl f.1)) (fun f => Φ.mass (ψ f.1.1))
    (fun f => β f.1.1) (fun f => α f.1.tail) (fun g => ((loopCoeff C (.inr g.1) j : ℤ) : ℝ))
    (fun g => Int.cast_ne_zero.mpr (Finset.mem_filter.mp g.2).2)
    (fun g => extPart C pOut pIn kIn (.inr g.1)) (fun g => lor g.1.1) (fun g => lor g.1.head)
    P.mγ P.Λ hε (by rwa [Fintype.card_coe]) (by rwa [Fintype.card_coe, Fintype.card_coe])
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  unfold fProd gProd kF kG
  rw [← Finset.prod_coe_sort (grpF C j), ← Finset.prod_coe_sort (grpG C j)]

variable [Fintype F] [DecidableEq F]

/-- **(T₉′) of a closed loop carrying one loop momentum**, summed over the flavours of the
loop. -/
theorem jointEnergyFirstIntegrable_closedGrp (P : Params) (Φ : Lepton.Flavors F) (rep : F → F)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hε : 0 < P.ε) (j : ℕ) (hZ : ∀ x, isZ (grpZ C j) (C.1.1 x) = isZ (grpZ C j) x)
    (α β : Wick.FermionVertex κ → Fin 4) (hd : ∀ s : Wick.FermionVertex κ, ¬ blk (α s) = blk (β s))
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (h1 : 1 ≤ Fintype.card (ZLine C (grpZ C j))) (h4 : Fintype.card (ZLine C (grpZ C j)) ≤ 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ =>
      ∑ f, (Φ.coeff f : ℂ) * fProd P Φ (closedFlavoring Φ (grpZ C j) f) α β (grpF C j)
        (kF C j pOut pIn kIn (ℓ 0)) := by
  classical
  have h := jointEnergyFirstIntegrable_zGroup Φ rep hrep hPV₁ hPV₂ hε hZ α β (fun s => hd s.1)
    (fun l => ((loopCoeff C (.inl l.1) j : ℤ) : ℝ))
    (fun l => Int.cast_ne_zero.mpr ((grpZ_iff j l.1).mp l.2))
    (fun l => extPart C pOut pIn kIn (.inl l.1)) h1 h4
  refine (congrArg _ (funext fun ℓ => Finset.sum_congr rfl fun f _ => ?_)).mp h
  congr 1
  unfold fProd kF grpF
  rw [Finset.prod_subtype _ (p := fun l : FermionLine C => grpZ C j l.1)
    fun l => by rw [Finset.mem_filter, grpZ_iff]; simp]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp only [closedFlavoring, l.2, ite_true]

end QED.GradedProof.X0

end
