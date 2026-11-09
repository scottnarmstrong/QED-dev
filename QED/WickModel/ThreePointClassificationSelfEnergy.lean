/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.ThreePointClassificationSort
public import QED.WickModel.TwoPoint
import QED.WickModel.ThreePointClassificationIndex
import QED.Integration.EnergyFirstShift

/-!
# Three gauge vertices: the self-energy loops on the electron legs

The values of the self-energy loops on the incoming and the outgoing leg of the three-point
function (packet 6a, decision D-24). In the chain `Ψ̄(y) → c → b → a → Ψ(x)` every fermion field
lies on the open fermion line, so only the all-electron flavoring is preserved, and the
fermionic sign is `(-1)³` from the vertices times the sign `-1` of a 4-cycle, that is `+1`.

* `IsSEin C a b c` (external photon at `a`, photon line `b – c`): the loop line is the fermion
  line `c → b`, carrying `ℓ`; the bridge `b → a` carries the incoming momentum `p`, and the photon
  line `±(ℓ - p)`. After the shift `ℓ ↦ ℓ - p` the value is the energy-first integral of
  `[i e γ^μ (1/i) S̃(p)]_{αγ} × selfEnergyIntegrand(p, ℓ)_{γβ}`.
* `IsSEout C a b c` (external photon at `c`, photon line `a – b`): the loop line is the fermion
  line `b → a`; the bridge `c → b` carries the outgoing momentum `p'`, and the value is the
  energy-first integral of `selfEnergyIntegrand(p', ℓ)_{αγ} × [(1/i) S̃(p') i e γ^μ]_{γβ}`.
-/

@[expose] public section

open Complex

namespace QED.WickModel

open Wick (gauge3)

variable {C : Contraction 1 1 gauge3}

/-! ### Chains: flavor and sign -/

namespace IsChain3

variable {a b c : Fin 3}

/-- **Flavor collapse.** All three fermion vertices lie on the open fermion line, so the only
flavoring that a chain preserves is the all-electron one. -/
theorem eq_electronFlavoring (hC : IsChain3 C a b c) {φ : Flavoring gauge3}
    (hφ : Preserves C φ) : φ = electronFlavoring gauge3 := by
  have ha : φ.1 (Wick.fv a) = 0 := by
    have := hφ (.inl 0)
    rwa [hC.out] at this
  have hb : φ.1 (Wick.fv b) = 0 := by
    have := hφ (.inr (Wick.fv a))
    rw [hC.ab] at this
    exact this.trans ha
  have hc : φ.1 (Wick.fv c) = 0 := by
    have := hφ (.inr (Wick.fv b))
    rw [hC.bc] at this
    exact this.trans hb
  apply Subtype.ext
  funext t
  rcases fv3_cases hC.hab hC.hbc hC.hac t with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc

/-- The fermion pairing of a chain is the 4-cycle `Ψ(x) → a → b → c → Ψ̄(y)`. -/
theorem fst_eq (hC : IsChain3 C a b c) :
    C.1.1 = Equiv.swap (.inl 0) (.inr (Wick.fv c)) * Equiv.swap (.inl 0) (.inr (Wick.fv b)) *
      Equiv.swap (.inl 0) (.inr (Wick.fv a)) := by
  have hne : ∀ s t : Fin 3, s ≠ t → (Sum.inr (Wick.fv s) : Fin 1 ⊕ Wick.FermionVertex gauge3) ≠
      .inr (Wick.fv t) := fun s t h h' => h (fv3_injective (Sum.inr_injective h'))
  ext1 y
  rcases fermion_field_cases hC.hab hC.hbc hC.hac y with rfl | rfl | rfl | rfl <;>
    simp only [Equiv.Perm.mul_apply]
  · rw [hC.out, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl
      (hne a b hC.hab), Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (hne a c hC.hac)]
  · rw [hC.ab, Equiv.swap_apply_right, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (hne b c hC.hbc)]
  · rw [hC.bc, Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (hne b a hC.hab.symm),
      Equiv.swap_apply_right, Equiv.swap_apply_left]
  · rw [hC.inn, Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (hne c a hC.hac.symm),
      Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (hne c b hC.hbc.symm), Equiv.swap_apply_right]

/-- A chain has fermionic sign `+1`: `(-1)³` from the vertices times the sign `-1` of a
4-cycle. -/
theorem fermionSign_eq (hC : IsChain3 C a b c) : fermionSign C = 1 := by
  rw [fermionSign, card_fermionVertex_gauge3, hC.fst_eq, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_mul, Equiv.Perm.sign_swap Sum.inl_ne_inr, Equiv.Perm.sign_swap Sum.inl_ne_inr,
    Equiv.Perm.sign_swap Sum.inl_ne_inr]
  simp

end IsChain3

/-- The photon propagator contracted symmetrically: the two Lorentz indices may be exchanged. -/
theorem sum_photonPropagator_swap (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (S : Matrix (Fin 4) (Fin 4) ℂ)
    (i j : Fin 4) :
    ∑ μ, ∑ ν, QED.OneLoop.photonPropagator mγ Λ ε k μ ν * (Dirac.gamma ν * S * Dirac.gamma μ) i j =
      ∑ μ, ∑ ν, QED.OneLoop.photonPropagator mγ Λ ε k μ ν *
        (Dirac.gamma μ * S * Dirac.gamma ν) i j := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by
    rw [QED.OneLoop.photonPropagator_comm]

/-! ### The incoming leg -/

namespace IsSEin

variable {a b c : Fin 3}

/-- The loop fermion line `c → b` is not a bridge: the photon line joins the same vertices. -/
theorem not_isBridge_lineB (hC : IsSEin C a b c) : ¬ IsBridge (.inl hC.chain.lineB : Line C) :=
  not_isBridge_of_parallel (g := .inr hC.photonLine) Sum.inr_ne_inl (by
    rw [hC.chain.ends_lineB]
    rcases hC.ends_photonLine with h | h
    · exact Or.inr h
    · exact Or.inl h)

/-- The loop line is the fermion line `c → b`: the line `b → a` is a bridge, and the photon
line has a larger label. -/
theorem isLoopLine_iff (hC : IsSEin C a b c) (l : Line C) :
    IsLoopLine l ↔ l = .inl hC.chain.lineB := by
  have hl : IsLoopLine (.inl hC.chain.lineB : Line C) := by
    refine ⟨hC.not_isBridge_lineB, fun g hg => ?_⟩
    rcases hC.line_cases g with rfl | rfl | rfl
    · exact absurd hC.isBridge_lineA hg
    · exact le_rfl
    · have := label_inr_ge hC.photonLine
      have hb : Line.label (.inl hC.chain.lineB : Line C) = b.val := label_fline _
      omega
  exact hl.isLoopLine_iff l

/-- The external momenta: `p` enters at `c`, `q = p' - p` at `a`, and `p'` leaves at `a`. -/
theorem externalMomentum_eq (hC : IsSEin C a b c) (p' p : Fin 4 → ℝ) (v : Fin 3) :
    externalMomentum C ![p'] ![p] ![p' - p] v =
      (if c = v then p else 0) + (if a = v then p' - p else 0) - (if a = v then p' else 0) := by
  rw [externalMomentum_eq_of_one hC.chain.out hC.chain.inn hC.photon]
  simp

open scoped Classical in
theorem loopTerm_eq (hC : IsSEin C a b c) (ℓ : Fin 4 → ℝ) (v : Fin 3) :
    ∑ g ∈ Finset.univ.filter (fun g : Line C => IsLoopLine g),
        ((if g.ends.2 = v then ℓ else 0) - (if g.ends.1 = v then ℓ else 0)) =
      (if b = v then ℓ else 0) - (if c = v then ℓ else 0) := by
  rw [sum_isLoopLine_eq ((hC.isLoopLine_iff _).mpr rfl), hC.chain.ends_lineB]

/-- The bridge `b → a` carries the incoming momentum `p`. -/
theorem lineMomentum_lineA (hC : IsSEin C a b c) (p' p ℓ : Fin 4 → ℝ) :
    lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inl hC.chain.lineA) = p := by
  have hab := hC.chain.hab
  have hbc := hC.chain.hbc
  have hac := hC.chain.hac
  have hA : ¬ IsLoopLine (.inl hC.chain.lineA : Line C) := fun h =>
    hC.chain.lineA_ne_lineB (Sum.inl_injective ((hC.isLoopLine_iff _).mp h))
  rw [lineMomentum_of_joined hA (g := .inr hC.photonLine) (x := c)
    (by simp [hC.isLoopLine_iff]) (by rw [hC.chain.ends_lineA]; exact hbc.symm)
    (by rw [hC.chain.ends_lineA]; exact hC.ends_photonLine)
    (fun g hg => by
      simp only [Set.mem_ofPred_eq, not_or, hC.isLoopLine_iff] at hg
      rcases hC.line_cases g with h | h | h
      · exact absurd h hg.1
      · exact absurd h hg.2
      · exact h),
    hC.chain.ends_lineA, hC.loopTerm_eq, hC.loopTerm_eq, hC.externalMomentum_eq,
    hC.externalMomentum_eq]
  simp [hab, hbc, hac, hbc.symm]

/-- The photon line carries `±(ℓ - p)`. -/
theorem lineMomentum_photonLine (hC : IsSEin C a b c) (p' p ℓ : Fin 4 → ℝ) :
    lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inr hC.photonLine) = ℓ - p ∨
      lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inr hC.photonLine) = -(ℓ - p) := by
  have hab := hC.chain.hab
  have hbc := hC.chain.hbc
  have hac := hC.chain.hac
  have hP : ¬ IsLoopLine (.inr hC.photonLine : Line C) := fun h =>
    Sum.inr_ne_inl ((hC.isLoopLine_iff _).mp h)
  rcases hC.ends_photonLine with he | he
  · left
    rw [lineMomentum_of_joined hP (g := .inl hC.chain.lineA) (x := a)
      (by simp [hC.isLoopLine_iff, hC.chain.lineA_ne_lineB]) (by rw [he]; exact hab)
      (by rw [he, hC.chain.ends_lineA]; exact Or.inl rfl)
      (fun g hg => by
        simp only [Set.mem_ofPred_eq, not_or, hC.isLoopLine_iff] at hg
        rcases hC.line_cases g with h | h | h
        · exact h
        · exact absurd h hg.2
        · exact absurd h hg.1),
      he, hC.loopTerm_eq, hC.loopTerm_eq, hC.externalMomentum_eq, hC.externalMomentum_eq]
    simp [hab, hab.symm, hbc.symm, hac.symm]
    abel
  · right
    rw [lineMomentum_of_forall_not_joined hP (fun w hw => by
        obtain ⟨g, hg, hgw⟩ := hw
        simp only [Set.mem_ofPred_eq, not_or, hC.isLoopLine_iff] at hg
        rcases hC.line_cases g with rfl | h | h
        · rw [hC.chain.ends_lineA, he] at hgw
          simp only [Prod.mk.injEq] at hgw
          rcases hgw with ⟨h1, -⟩ | ⟨-, h2⟩
          · exact absurd h1 hbc
          · exact absurd h2 hac
        · exact absurd h hg.2
        · exact absurd h hg.1),
      he, hC.loopTerm_eq, hC.externalMomentum_eq]
    simp [hbc, hac]
    abel

/-- **The amplitude of an incoming-leg self-energy loop**:
`[i e γ^μ (1/i) S̃(p)]_{αγ} [(ie)² (1/i)² ∑ Δ̃_{μ'ν'}(ℓ - p) γ^{μ'} S̃(ℓ) γ^{ν'}]_{γβ}`. -/
theorem contractionAmplitude_eq (P : Params) (hC : IsSEin C a b c) (p' p ℓ : Fin 4 → ℝ)
    (α β μ : Fin 4) :
    contractionAmplitude P C (electronFlavoring gauge3) ![p'] ![p] ![p' - p] ℓ ![α] ![β] ![μ] =
      ∑ γ, ((I * P.e) • Dirac.gamma μ * ((1 / I) • QED.OneLoop.electronPropagator P.m P.ε p)) α γ *
        ((I * P.e) ^ 2 * (1 / I) ^ 2 * ∑ μ', ∑ ν',
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (ℓ - p) μ' ν' *
            (Dirac.gamma μ' * QED.OneLoop.electronPropagator P.m P.ε ℓ * Dirac.gamma ν') γ β) := by
  have hab := hC.chain.hab
  have hbc := hC.chain.hbc
  have hac := hC.chain.hac
  have hloop : lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inl hC.chain.lineB) = ℓ :=
    lineMomentum_of_isLoopLine ((hC.isLoopLine_iff _).mpr rfl) _ _ _ _
  have hprop : ∀ lor : Wick.PhotonSlot gauge3 → Fin 4,
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε
          (lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inr hC.photonLine))
          (lor hC.photonLine.1) (lor hC.photonLine.head) =
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (ℓ - p) (lor (Wick.ps b)) (lor (Wick.ps c)) :=
    fun lor => photonPropagator_of_pair (hC.lineMomentum_photonLine p' p ℓ) lor
      (hC.photon.line_spec _ _ _)
  rw [contractionAmplitude]
  simp only [spinor_constraint_out_iff_of_one hC.chain.out,
    spinor_constraint_in_iff_of_one hC.chain.inn, lorentz_constraint_iff_of_one hC.photon,
    prod_fin_three_eq hab hbc hac, vertexFactor_gauge3,
    prod_eq_mul_of_two hC.chain.lineA_ne_lineB hC.chain.fermionLine_cases,
    Fintype.prod_eq_single hC.photonLine fun l hl => absurd (hC.photon.eq_line _ _ _ l) hl,
    IsChain3.lineA_val, IsChain3.tail_lineA, IsChain3.lineB_val, IsChain3.tail_lineB,
    mass_electronFlavoring, hloop, hC.lineMomentum_lineA, hprop]
  rw [show (∑ α : Wick.FermionVertex gauge3 → Fin 4, ∑ β : Wick.FermionVertex gauge3 → Fin 4,
      ∑ lor : Wick.PhotonSlot gauge3 → Fin 4, _) =
      ∑ lor : Wick.PhotonSlot gauge3 → Fin 4, ∑ α : Wick.FermionVertex gauge3 → Fin 4,
        ∑ β : Wick.FermionVertex gauge3 → Fin 4, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  have hfa : Wick.fv a ≠ Wick.fv b := fv3_injective.ne hab
  have hfb : Wick.fv b ≠ Wick.fv c := fv3_injective.ne hbc
  have hfc : Wick.fv a ≠ Wick.fv c := fv3_injective.ne hac
  have hpa : Wick.ps a ≠ Wick.ps b := ps3_injective.ne hab
  have hpb : Wick.ps b ≠ Wick.ps c := ps3_injective.ne hbc
  have hpc : Wick.ps a ≠ Wick.ps c := ps3_injective.ne hac
  simp only [sum_pi_eq_of_three hpa hpb hpc (ps3_cases hab hbc hac),
    sum_pi_eq_of_three hfa hfb hfc (fv3_cases hab hbc hac), ite_true, hfa.symm, hfb.symm,
    hfc.symm, hpa.symm, hpb.symm, hpc.symm, ite_false]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Matrix.cons_val_zero]
  exact sum_chain_index_in _ _ _ _ _ _ _ _ _


/-- **The value of an incoming-leg self-energy loop**: the energy-first integral of
`[i e γ^μ (1/i) S̃(p)]_{αγ} × selfEnergyIntegrand(p, ℓ)_{γβ}`, after the shift `ℓ ↦ ℓ - p`. -/
theorem contractionValue_eq (P : Params) (hC : IsSEin C a b c) (p' p : Fin 4 → ℝ)
    (α β μ : Fin 4) :
    contractionValue P C ![p'] ![p] ![p' - p] ![α] ![β] ![μ] =
      QED.OneLoop.energyFirstIntegral fun ℓ =>
        ∑ γ, ((I * P.e) • Dirac.gamma μ *
          ((1 / I) • QED.OneLoop.electronPropagator P.m P.ε p)) α γ *
            selfEnergyIntegrand P P.ε p ℓ γ β := by
  rw [contractionValue_of_isLoopLine P ((hC.isLoopLine_iff _).mpr rfl)]
  conv_rhs => rw [← QED.OneLoop.energyFirstIntegral_sub_right_eq_self _ p]
  congr 1
  funext ℓ
  rw [regulatedAmplitude_eq_of_forall_preserves P (fun φ hφ => hC.chain.eq_electronFlavoring hφ),
    hC.contractionAmplitude_eq]
  simp only [selfEnergyIntegrand, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    add_sub_cancel, sum_photonPropagator_swap, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring

end IsSEin

/-! ### The outgoing leg -/

namespace IsSEout

variable {a b c : Fin 3}

/-- The loop fermion line `b → a` is not a bridge: the photon line joins the same vertices. -/
theorem not_isBridge_lineA (hC : IsSEout C a b c) : ¬ IsBridge (.inl hC.chain.lineA : Line C) :=
  not_isBridge_of_parallel (g := .inr hC.photonLine) Sum.inr_ne_inl (by
    rw [hC.chain.ends_lineA]
    rcases hC.ends_photonLine with h | h
    · exact Or.inr h
    · exact Or.inl h)

/-- The loop line is the fermion line `b → a`: the line `c → b` is a bridge, and the photon
line has a larger label. -/
theorem isLoopLine_iff (hC : IsSEout C a b c) (l : Line C) :
    IsLoopLine l ↔ l = .inl hC.chain.lineA := by
  have hl : IsLoopLine (.inl hC.chain.lineA : Line C) := by
    refine ⟨hC.not_isBridge_lineA, fun g hg => ?_⟩
    rcases hC.line_cases g with rfl | rfl | rfl
    · exact le_rfl
    · exact absurd hC.isBridge_lineB hg
    · have := label_inr_ge hC.photonLine
      have ha : Line.label (.inl hC.chain.lineA : Line C) = a.val := label_fline _
      omega
  exact hl.isLoopLine_iff l

/-- The external momenta: `p` and `q = p' - p` enter at `c`, and `p'` leaves at `a`. -/
theorem externalMomentum_eq (hC : IsSEout C a b c) (p' p : Fin 4 → ℝ) (v : Fin 3) :
    externalMomentum C ![p'] ![p] ![p' - p] v =
      (if c = v then p else 0) + (if c = v then p' - p else 0) - (if a = v then p' else 0) := by
  rw [externalMomentum_eq_of_one hC.chain.out hC.chain.inn hC.photon]
  simp

open scoped Classical in
theorem loopTerm_eq (hC : IsSEout C a b c) (ℓ : Fin 4 → ℝ) (v : Fin 3) :
    ∑ g ∈ Finset.univ.filter (fun g : Line C => IsLoopLine g),
        ((if g.ends.2 = v then ℓ else 0) - (if g.ends.1 = v then ℓ else 0)) =
      (if a = v then ℓ else 0) - (if b = v then ℓ else 0) := by
  rw [sum_isLoopLine_eq ((hC.isLoopLine_iff _).mpr rfl), hC.chain.ends_lineA]

/-- The bridge `c → b` carries the outgoing momentum `p'`. -/
theorem lineMomentum_lineB (hC : IsSEout C a b c) (p' p ℓ : Fin 4 → ℝ) :
    lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inl hC.chain.lineB) = p' := by
  have hab := hC.chain.hab
  have hbc := hC.chain.hbc
  have hac := hC.chain.hac
  have hB : ¬ IsLoopLine (.inl hC.chain.lineB : Line C) := fun h =>
    hC.chain.lineA_ne_lineB (Sum.inl_injective ((hC.isLoopLine_iff _).mp h)).symm
  rw [lineMomentum_of_forall_not_joined hB (fun w hw => by
      obtain ⟨g, hg, hgw⟩ := hw
      simp only [Set.mem_ofPred_eq, not_or, hC.isLoopLine_iff] at hg
      rw [hC.chain.ends_lineB] at hgw
      rcases hC.line_cases g with h | h | rfl
      · exact absurd h hg.2
      · exact absurd h hg.1
      · rcases hC.ends_photonLine with he | he <;> rw [he] at hgw <;>
          simp only [Prod.mk.injEq] at hgw <;> omega),
    hC.chain.ends_lineB, hC.loopTerm_eq, hC.externalMomentum_eq]
  simp [hac, hbc]

/-- The photon line carries `±(ℓ - p')`. -/
theorem lineMomentum_photonLine (hC : IsSEout C a b c) (p' p ℓ : Fin 4 → ℝ) :
    lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inr hC.photonLine) = ℓ - p' ∨
      lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inr hC.photonLine) = -(ℓ - p') := by
  have hab := hC.chain.hab
  have hbc := hC.chain.hbc
  have hac := hC.chain.hac
  have hP : ¬ IsLoopLine (.inr hC.photonLine : Line C) := fun h =>
    Sum.inr_ne_inl ((hC.isLoopLine_iff _).mp h)
  rcases hC.ends_photonLine with he | he
  · left
    rw [lineMomentum_of_forall_not_joined hP (fun w hw => by
        obtain ⟨g, hg, hgw⟩ := hw
        simp only [Set.mem_ofPred_eq, not_or, hC.isLoopLine_iff] at hg
        rw [he] at hgw
        rcases hC.line_cases g with h | rfl | h
        · exact absurd h hg.2
        · rw [hC.chain.ends_lineB] at hgw
          simp only [Prod.mk.injEq] at hgw
          omega
        · exact absurd h hg.1),
      he, hC.loopTerm_eq, hC.externalMomentum_eq]
    simp [hab.symm, hac.symm]
    abel
  · right
    rw [lineMomentum_of_joined hP (g := .inl hC.chain.lineB) (x := c)
      (by simp [hC.isLoopLine_iff, hC.chain.lineA_ne_lineB.symm]) (by rw [he]; exact hbc.symm)
      (by rw [he, hC.chain.ends_lineB]; exact Or.inr rfl)
      (fun g hg => by
        simp only [Set.mem_ofPred_eq, not_or, hC.isLoopLine_iff] at hg
        rcases hC.line_cases g with h | h | h
        · exact absurd h hg.2
        · exact h
        · exact absurd h hg.1),
      he, hC.loopTerm_eq, hC.loopTerm_eq, hC.externalMomentum_eq, hC.externalMomentum_eq]
    simp [hab, hbc, hac, hbc.symm]
    abel

/-- **The amplitude of an outgoing-leg self-energy loop**:
`[(ie)² (1/i)² ∑ Δ̃_{μ'ν'}(ℓ - p') γ^{μ'} S̃(ℓ) γ^{ν'}]_{αγ} [(1/i) S̃(p') i e γ^μ]_{γβ}`. -/
theorem contractionAmplitude_eq (P : Params) (hC : IsSEout C a b c) (p' p ℓ : Fin 4 → ℝ)
    (α β μ : Fin 4) :
    contractionAmplitude P C (electronFlavoring gauge3) ![p'] ![p] ![p' - p] ℓ ![α] ![β] ![μ] =
      ∑ γ, ((I * P.e) ^ 2 * (1 / I) ^ 2 * ∑ μ', ∑ ν',
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (ℓ - p') μ' ν' *
            (Dirac.gamma μ' * QED.OneLoop.electronPropagator P.m P.ε ℓ * Dirac.gamma ν') α γ) *
        (((1 / I) • QED.OneLoop.electronPropagator P.m P.ε p') *
          (I * P.e) • Dirac.gamma μ) γ β := by
  have hab := hC.chain.hab
  have hbc := hC.chain.hbc
  have hac := hC.chain.hac
  have hloop : lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inl hC.chain.lineA) = ℓ :=
    lineMomentum_of_isLoopLine ((hC.isLoopLine_iff _).mpr rfl) _ _ _ _
  have hprop : ∀ lor : Wick.PhotonSlot gauge3 → Fin 4,
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε
          (lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inr hC.photonLine))
          (lor hC.photonLine.1) (lor hC.photonLine.head) =
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (ℓ - p') (lor (Wick.ps a)) (lor (Wick.ps b)) :=
    fun lor => photonPropagator_of_pair (hC.lineMomentum_photonLine p' p ℓ) lor
      (hC.photon.line_spec _ _ _)
  rw [contractionAmplitude]
  simp only [spinor_constraint_out_iff_of_one hC.chain.out,
    spinor_constraint_in_iff_of_one hC.chain.inn, lorentz_constraint_iff_of_one hC.photon,
    prod_fin_three_eq hab hbc hac, vertexFactor_gauge3,
    prod_eq_mul_of_two hC.chain.lineA_ne_lineB hC.chain.fermionLine_cases,
    Fintype.prod_eq_single hC.photonLine fun l hl => absurd (hC.photon.eq_line _ _ _ l) hl,
    IsChain3.lineA_val, IsChain3.tail_lineA, IsChain3.lineB_val, IsChain3.tail_lineB,
    mass_electronFlavoring, hloop, hC.lineMomentum_lineB, hprop]
  rw [show (∑ α : Wick.FermionVertex gauge3 → Fin 4, ∑ β : Wick.FermionVertex gauge3 → Fin 4,
      ∑ lor : Wick.PhotonSlot gauge3 → Fin 4, _) =
      ∑ lor : Wick.PhotonSlot gauge3 → Fin 4, ∑ α : Wick.FermionVertex gauge3 → Fin 4,
        ∑ β : Wick.FermionVertex gauge3 → Fin 4, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  have hfa : Wick.fv a ≠ Wick.fv b := fv3_injective.ne hab
  have hfb : Wick.fv b ≠ Wick.fv c := fv3_injective.ne hbc
  have hfc : Wick.fv a ≠ Wick.fv c := fv3_injective.ne hac
  have hpa : Wick.ps a ≠ Wick.ps b := ps3_injective.ne hab
  have hpb : Wick.ps b ≠ Wick.ps c := ps3_injective.ne hbc
  have hpc : Wick.ps a ≠ Wick.ps c := ps3_injective.ne hac
  simp only [sum_pi_eq_of_three hpa hpb hpc (ps3_cases hab hbc hac),
    sum_pi_eq_of_three hfa hfb hfc (fv3_cases hab hbc hac), ite_true, hfa.symm, hfb.symm,
    hfc.symm, hpa.symm, hpb.symm, hpc.symm, ite_false]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Matrix.cons_val_zero]
  exact sum_chain_index_out _ _ _ _ _ _ _ _ _


/-- **The value of an outgoing-leg self-energy loop**: the energy-first integral of
`selfEnergyIntegrand(p', ℓ)_{αγ} × [(1/i) S̃(p') i e γ^μ]_{γβ}`, after the shift
`ℓ ↦ ℓ - p'`. -/
theorem contractionValue_eq (P : Params) (hC : IsSEout C a b c) (p' p : Fin 4 → ℝ)
    (α β μ : Fin 4) :
    contractionValue P C ![p'] ![p] ![p' - p] ![α] ![β] ![μ] =
      QED.OneLoop.energyFirstIntegral fun ℓ =>
        ∑ γ, selfEnergyIntegrand P P.ε p' ℓ α γ *
          (((1 / I) • QED.OneLoop.electronPropagator P.m P.ε p') *
            (I * P.e) • Dirac.gamma μ) γ β := by
  rw [contractionValue_of_isLoopLine P ((hC.isLoopLine_iff _).mpr rfl)]
  conv_rhs => rw [← QED.OneLoop.energyFirstIntegral_sub_right_eq_self _ p']
  congr 1
  funext ℓ
  rw [regulatedAmplitude_eq_of_forall_preserves P (fun φ hφ => hC.chain.eq_electronFlavoring hφ),
    hC.contractionAmplitude_eq]
  simp only [selfEnergyIntegrand, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    add_sub_cancel, sum_photonPropagator_swap, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring

end IsSEout

end QED.WickModel

end
