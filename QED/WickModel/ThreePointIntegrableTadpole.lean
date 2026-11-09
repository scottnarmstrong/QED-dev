/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.ThreePointIntegrableTadpoleBound
public import QED.WickModel.ThreePointClassificationShapes
import QED.WickModel.ThreePointClassificationPolarization
import QED.WickModel.ThreePointClassificationTadpole

/-!
# Integrability of the tadpoles of the three-point function

A tadpole `IsTP C a b c u` of the three-point function (packet 6a, decision D-24) has a
one-vertex closed fermion loop at `c`, which is its loop line, attached by a photon line to the
open fermion line. Its value vanishes by oddness (`IsTP.contractionValue_eq_zero`); here we show
that its loop integrand is also integrable in both stages of the energy-first prescription M1 at
every `ε > 0`, under the Pauli–Villars conditions.

* `contractionAmplitude_eq_of_selfLoop`: when the loop line is a self-loop `l` at a gauge vertex,
  the amplitude of every flavoring is a sum, over the spinor and Lorentz indices, of a factor
  independent of the loop momentum (`selfLoopCoeff`) times the entry
  `S̃(ℓ)_{β_l α_l}` of the self-loop's propagator; the factor vanishes when `β_l = α_l`.
* The closed loop of a tadpole may have any flavor `f`, with weight `c_f`, and the open line is
  an electron line, so the regulated amplitude is a sum of `ℓ`-independent factors times the
  off-diagonal entries of `∑_f c_f S̃_f(ℓ)`.
* `IsTP.integrableEnergyFirst_regulatedAmplitude`: the loop integrand is integrable in both
  stages (`TadpoleBound.integrableEnergyFirst_sum_electronPropagator`).
-/

@[expose] public section

open Complex

namespace QED.WickModel

/-! ### Self-loops -/

section SelfLoop

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

open scoped Classical in
/-- The part of the amplitude of a contraction whose loop line is the self-loop `l` that does not
depend on the loop momentum: every other line carries its momentum at `ℓ = 0`. -/
noncomputable def selfLoopCoeff (P : Params) (C : Contraction nf nA κ) (l : FermionLine C)
    (φ : Flavoring κ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) : ℂ :=
  (if (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
      (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
      (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) then 1 else 0) *
    (∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
      (psiMomentum C pOut pIn kIn 0) (photonMomentum C pOut pIn kIn 0) t) *
    (1 / I) *
    (∏ f ∈ Finset.univ.erase l, (1 / I) *
      QED.OneLoop.electronPropagator (P.mass (φ.1 f.1)) P.ε
        (lineMomentum C pOut pIn kIn 0 (.inl f)) (β f.1) (α f.tail)) *
    ∏ g : PhotonLine C, (1 / I) *
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (lineMomentum C pOut pIn kIn 0 (.inr g))
        (lor g.1) (lor g.head)

variable {C : Contraction nf nA κ}

/-- **The amplitude of a contraction whose loop line is a self-loop.** If the loop line is a
fermion line `l` from a gauge vertex to itself (all vertices being gauge vertices), the amplitude
is `∑_{α β lor} selfLoopCoeff · S̃(ℓ)_{β_l α_l}`. -/
theorem contractionAmplitude_eq_of_selfLoop (P : Params) (hκ : ∀ t, κ t = .gauge)
    {l : FermionLine C} (hl : IsLoopLine (.inl l : Line C)) (hself : l.tail = l.1)
    (φ : Flavoring κ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (ℓ : Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionAmplitude P C φ pOut pIn kIn ℓ αOut βIn μ =
      ∑ α, ∑ β, ∑ lor, selfLoopCoeff P C l φ pOut pIn kIn αOut βIn μ α β lor *
        QED.OneLoop.electronPropagator (P.mass (φ.1 l.1)) P.ε ℓ (β l.1) (α l.1) := by
  classical
  have hends : (Line.ends (.inl l : Line C)).1 = (Line.ends (.inl l : Line C)).2 := by
    change l.tail.1 = l.1.1
    rw [hself]
  have hm : ∀ (ℓ' : Fin 4 → ℝ) (g : Line C), g ≠ .inl l →
      lineMomentum C pOut pIn kIn ℓ' g = lineMomentum C pOut pIn kIn 0 g := fun ℓ' g hg =>
    lineMomentum_eq_of_selfLoop hl hends hg _ _ _ _ _
  have hloop : lineMomentum C pOut pIn kIn ℓ (.inl l) = ℓ :=
    lineMomentum_of_isLoopLine hl _ _ _ _
  have hF : ∀ α β : Wick.FermionVertex κ → Fin 4,
      ∏ f : FermionLine C, (1 / I) *
          QED.OneLoop.electronPropagator (P.mass (φ.1 f.1)) P.ε
            (lineMomentum C pOut pIn kIn ℓ (.inl f)) (β f.1) (α f.tail) =
        ((1 / I) * QED.OneLoop.electronPropagator (P.mass (φ.1 l.1)) P.ε ℓ (β l.1) (α l.1)) *
          ∏ f ∈ Finset.univ.erase l, (1 / I) *
            QED.OneLoop.electronPropagator (P.mass (φ.1 f.1)) P.ε
              (lineMomentum C pOut pIn kIn 0 (.inl f)) (β f.1) (α f.tail) := by
    intro α β
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ l), hloop, hself]
    refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun f hf => ?_)
    rw [hm ℓ (.inl f) fun h => (Finset.mem_erase.mp hf).1 (Sum.inl_injective h)]
  have hG : ∀ lor : Wick.PhotonSlot κ → Fin 4,
      ∏ g : PhotonLine C, (1 / I) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (lineMomentum C pOut pIn kIn ℓ (.inr g))
            (lor g.1) (lor g.head) =
        ∏ g : PhotonLine C, (1 / I) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (lineMomentum C pOut pIn kIn 0 (.inr g))
            (lor g.1) (lor g.head) := fun lor =>
    Finset.prod_congr rfl fun g _ => by rw [hm ℓ (.inr g) Sum.inr_ne_inl]
  rw [contractionAmplitude]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => ?_
  rw [hF α β, hG lor, prod_vertexFactor_of_forall_gauge hκ _ _ _ _ _ _ α β lor
    (psiMomentum C pOut pIn kIn ℓ) (psiMomentum C pOut pIn kIn 0)
    (photonMomentum C pOut pIn kIn ℓ) (photonMomentum C pOut pIn kIn 0), selfLoopCoeff]
  ring

/-- The factor vanishes when the two spinor indices of the self-loop's vertex agree. -/
theorem selfLoopCoeff_eq_zero (P : Params) (hκ : ∀ t, κ t = .gauge) (l : FermionLine C)
    (φ : Flavoring κ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) {α β : Wick.FermionVertex κ → Fin 4}
    (lor : Wick.PhotonSlot κ → Fin 4) (h : β l.1 = α l.1) :
    selfLoopCoeff P C l φ pOut pIn kIn αOut βIn μ α β lor = 0 := by
  rw [selfLoopCoeff, prod_vertexFactor_eq_zero hκ _ _ _ _ _ _ α β lor _ _ h]
  ring

/-- The factor depends on the flavoring only through the lines other than the self-loop. -/
theorem selfLoopCoeff_congr (P : Params) (l : FermionLine C) {φ φ' : Flavoring κ}
    (hφ : ∀ f ∈ Finset.univ.erase l, φ.1 f.1 = φ'.1 f.1) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) :
    selfLoopCoeff P C l φ pOut pIn kIn αOut βIn μ α β lor =
      selfLoopCoeff P C l φ' pOut pIn kIn αOut βIn μ α β lor := by
  have hprod : ∏ f ∈ Finset.univ.erase l, (1 / I) *
      QED.OneLoop.electronPropagator (P.mass (φ.1 f.1)) P.ε
        (lineMomentum C pOut pIn kIn 0 (.inl f)) (β f.1) (α f.tail) =
      ∏ f ∈ Finset.univ.erase l, (1 / I) *
        QED.OneLoop.electronPropagator (P.mass (φ'.1 f.1)) P.ε
          (lineMomentum C pOut pIn kIn 0 (.inl f)) (β f.1) (α f.tail) :=
    Finset.prod_congr rfl fun f hf => by rw [hφ f hf]
  rw [selfLoopCoeff, selfLoopCoeff, hprod]

end SelfLoop

/-- Integrability in both stages holds for the zero integrand. -/
theorem integrableEnergyFirst_zero : IntegrableEnergyFirst fun _ => (0 : ℂ) :=
  ⟨fun _ => MeasureTheory.integrable_zero _ _ _, by
    simp only [MeasureTheory.integral_zero]
    exact MeasureTheory.integrable_zero _ _ _⟩

/-! ### Tadpoles: flavors -/

open Wick (gauge3)

variable {C : Contraction 1 1 gauge3}

/-- The flavoring in which the self-loop vertex `c` has flavor `f` and the other two fermion
vertices are electrons. -/
def tpFlavoring (c f : Fin 3) : Flavoring gauge3 :=
  ⟨fun t => if t = Wick.fv c then f else 0, fun _ h => absurd rfl h⟩

namespace IsTP

variable {a b c u : Fin 3}

/-- The flavor of the self-loop vertex `c` under `tpFlavoring c f` is `f`. -/
theorem tpFlavoring_c (f : Fin 3) : (tpFlavoring c f).1 (Wick.fv c) = f := by
  simp [tpFlavoring]

/-- **The flavorings preserved by a tadpole**: the open line is an electron line, and the
self-loop may have any flavor. -/
theorem preserves_iff (hC : IsTP C a b c u) (φ : Flavoring gauge3) :
    Preserves C φ ↔ φ = tpFlavoring c (φ.1 (Wick.fv c)) := by
  have hab := hC.hab
  have hbc := hC.hbc
  have hac := hC.hac
  have hfa : Wick.fv a ≠ Wick.fv c := fv3_injective.ne hac
  have hfb : Wick.fv b ≠ Wick.fv c := fv3_injective.ne hbc
  constructor
  · intro hφ
    have ha : φ.1 (Wick.fv a) = 0 := by
      have := hφ (.inl 0)
      rwa [hC.out] at this
    have hb : φ.1 (Wick.fv b) = 0 := by
      have := hφ (.inr (Wick.fv a))
      rw [hC.ab] at this
      exact this.trans ha
    apply Subtype.ext
    funext t
    rcases fv3_cases hab hbc hac t with rfl | rfl | rfl
    · simp [tpFlavoring, hfa, ha]
    · simp [tpFlavoring, hfb, hb]
    · simp [tpFlavoring]
  · intro hφ y
    rw [hφ]
    rcases fermion_field_cases hab hbc hac y with rfl | rfl | rfl | rfl
    · rw [hC.out]
      simp [fermionFlavor, tpFlavoring, hfa]
    · rw [hC.ab]
      simp [fermionFlavor, tpFlavoring, hfa, hfb]
    · rw [hC.inn]
      simp [fermionFlavor, tpFlavoring, hfb]
    · rw [hC.cc]

/-- **The sum over the preserved flavorings** is the sum over the flavor of the self-loop. -/
theorem sum_preserves (hC : IsTP C a b c u) {M : Type*} [AddCommMonoid M]
    [Fintype (Flavoring gauge3)] [DecidablePred (Preserves C)] (F : Flavoring gauge3 → M) :
    ∑ φ ∈ (Finset.univ : Finset (Flavoring gauge3)).filter (Preserves C), F φ =
      ∑ f : Fin 3, F (tpFlavoring c f) := by
  refine Finset.sum_nbij' (fun φ => φ.1 (Wick.fv c)) (tpFlavoring c)
    (fun _ _ => Finset.mem_univ _)
    (fun f _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hC.preserves_iff _).mpr (by
      rw [tpFlavoring_c])⟩)
    (fun φ hφ => ((hC.preserves_iff φ).mp (Finset.mem_filter.mp hφ).2).symm)
    (fun f _ => tpFlavoring_c f)
    (fun φ hφ => by rw [← (hC.preserves_iff φ).mp (Finset.mem_filter.mp hφ).2])

/-- The closed fermion loop at `c`. -/
def closedLoop (hC : IsTP C a b c u) : ClosedLoop C :=
  ⟨Quotient.mk _ (.inr (Wick.fv c)), fun i h => by
    have h' : Equiv.Perm.SameCycle C.1.1 (.inl i) (.inr (Wick.fv c)) := Quotient.exact h
    rcases sameCycle_of_swap hC.cc hC.cc h'.symm with h'' | h'' <;>
      exact Sum.inl_ne_inr h''⟩

/-- The contraction has one closed fermion loop. -/
theorem eq_closedLoop (hC : IsTP C a b c u) (q : ClosedLoop C) : q = hC.closedLoop := by
  obtain ⟨q, hq⟩ := q
  obtain ⟨y, rfl⟩ := Quotient.exists_rep q
  apply Subtype.ext
  change Quotient.mk _ y = Quotient.mk _ (.inr (Wick.fv c))
  rcases fermion_field_cases hC.hab hC.hbc hC.hac y with rfl | rfl | rfl | rfl
  · exact absurd rfl (hq 0)
  · exact absurd (Quotient.sound
      (show Equiv.Perm.SameCycle C.1.1 _ _ from ⟨1, by simp [hC.out]⟩)) (hq 0)
  · exact absurd (Quotient.sound
      (show Equiv.Perm.SameCycle C.1.1 _ _ from ⟨1, by simp [hC.inn]⟩)).symm (hq 0)
  · rfl

/-- The regulator weight of the flavor-`f` self-loop is `c_f`. -/
theorem loopWeight_tpFlavoring (P : Params) (hC : IsTP C a b c u) (f : Fin 3) :
    loopWeight P C (tpFlavoring c f) = P.loopCoeff f := by
  classical
  rw [loopWeight, Fintype.prod_eq_single hC.closedLoop fun q hq => absurd (hC.eq_closedLoop q) hq]
  have hmem0 : Equiv.Perm.SameCycle C.1.1
      (Quotient.out (Quotient.mk (Equiv.Perm.SameCycle.setoid C.1.1) (.inr (Wick.fv c))))
      (.inr (Wick.fv c)) :=
    Quotient.exact (Quotient.out_eq (Quotient.mk (Equiv.Perm.SameCycle.setoid C.1.1)
      (.inr (Wick.fv c))))
  change P.loopCoeff (fermionFlavor (tpFlavoring c f) (Quotient.out (Quotient.mk
    (Equiv.Perm.SameCycle.setoid C.1.1) (.inr (Wick.fv c))))) = _
  rcases sameCycle_of_swap hC.cc hC.cc hmem0.symm with h | h <;> rw [h] <;>
    simp [fermionFlavor, tpFlavoring]

open scoped Classical in
/-- The regulated amplitude of a tadpole: the sum over the flavors of the self-loop, with
weights `c_f`. -/
theorem regulatedAmplitude_eq (P : Params) (hC : IsTP C a b c u)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (ℓ : Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    regulatedAmplitude P C pOut pIn kIn ℓ αOut βIn μ =
      ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
        contractionAmplitude P C (tpFlavoring c f) pOut pIn kIn ℓ αOut βIn μ := by
  rw [regulatedAmplitude, hC.sum_preserves]
  simp only [hC.loopWeight_tpFlavoring]

/-- The self-loop is indexed by `c` and returns to `c`. -/
theorem loopC_val (hC : IsTP C a b c u) : hC.loopC.1 = Wick.fv c := rfl

/-- The self-loop returns to its vertex. -/
theorem tail_loopC (hC : IsTP C a b c u) : hC.loopC.tail = hC.loopC.1 := tail_fline hC.cc

/-- **The regulated amplitude of a tadpole**, as a sum of factors independent of the loop
momentum times the entries of `∑_f c_f S̃_f(ℓ)`; the factors vanish on the diagonal. -/
theorem exists_regulatedAmplitude_eq (P : Params) (hC : IsTP C a b c u)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    ∃ X : (Wick.FermionVertex gauge3 → Fin 4) → (Wick.FermionVertex gauge3 → Fin 4) →
        (Wick.PhotonSlot gauge3 → Fin 4) → ℂ,
      (∀ α β lor, β (Wick.fv c) = α (Wick.fv c) → X α β lor = 0) ∧
      ∀ ℓ, regulatedAmplitude P C pOut pIn kIn ℓ αOut βIn μ =
        ∑ α, ∑ β, ∑ lor, X α β lor * ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
          QED.OneLoop.electronPropagator (P.mass f) P.ε ℓ (β (Wick.fv c)) (α (Wick.fv c)) := by
  have hcongr : ∀ f : Fin 3, ∀ g ∈ Finset.univ.erase hC.loopC,
      (tpFlavoring c f).1 g.1 = (tpFlavoring c 0).1 g.1 := by
    intro f g hg
    have hne : g.1 ≠ Wick.fv c := fun h => (Finset.mem_erase.mp hg).1 (Subtype.ext h)
    simp [tpFlavoring, hne]
  refine ⟨selfLoopCoeff P C hC.loopC (tpFlavoring c 0) pOut pIn kIn αOut βIn μ,
    fun α β lor h => selfLoopCoeff_eq_zero P (fun _ => rfl) hC.loopC _ _ _ _ _ _ _ lor h,
    fun ℓ => ?_⟩
  rw [hC.regulatedAmplitude_eq]
  simp only [contractionAmplitude_eq_of_selfLoop P (fun _ => rfl) hC.isLoopLine hC.tail_loopC,
    hC.loopC_val, tpFlavoring_c, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun lor _ => Finset.sum_congr rfl fun f _ => ?_
  rw [selfLoopCoeff_congr P hC.loopC (hcongr f)]
  ring

/-- **The loop integrand of a tadpole is integrable in both stages of the energy-first
prescription**, for `ε > 0`, regulator fermions heavier than the electron, and the
Pauli–Villars conditions. -/
theorem integrableEnergyFirst_regulatedAmplitude {P : Params} (hm : 0 < P.m)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hε : 0 < P.ε)
    (hC : IsTP C a b c u) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    IntegrableEnergyFirst fun ℓ => regulatedAmplitude P C pOut pIn kIn ℓ αOut βIn μ := by
  obtain ⟨X, hX0, hX⟩ := hC.exists_regulatedAmplitude_eq P pOut pIn kIn αOut βIn μ
  simp only [hX]
  refine IntegrableEnergyFirst.finsetSum _ fun α _ => IntegrableEnergyFirst.finsetSum _
    fun β _ => IntegrableEnergyFirst.finsetSum _ fun lor _ => ?_
  by_cases h : β (Wick.fv c) = α (Wick.fv c)
  · simp only [hX0 α β lor h, zero_mul]
    exact integrableEnergyFirst_zero
  · exact (TadpoleBound.integrableEnergyFirst_sum_electronPropagator hm hM₁ hM₂ hPV₁ hPV₂ hε
      h).const_mul _

end IsTP

end QED.WickModel

end
