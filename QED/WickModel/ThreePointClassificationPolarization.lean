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
# Three gauge vertices: the vacuum polarization loop on the photon leg

The value of the vacuum polarization loops `IsVP C a v w` of the three-point function (packet 6a,
decision D-24): the fermion line `Ψ̄(y) → a → Ψ(x)`, a closed fermion loop through `v` and `w`,
the external photon at `v`, and the photon line joining `w` to `a`.

* The closed loop may have any flavor `f`, with regulator weight `c_f`; the open line is an
  electron line.
* The loop line is the fermion line of the loop with the smaller label. The photon line is a
  bridge carrying `±q`, `q = p' - p`, and the other loop line carries `ℓ ± q`.
* The fermionic sign is `(-1)³` from the vertices times the sign `+1` of two transpositions, that
  is `-1`, the sign of a closed fermion loop.
* `IsVP.neg_contractionValue_eq`: minus the value is the energy-first integral of
  `∑_{νρ} [i e γ^ν]_{αβ} (1/i) Δ̃_{νρ}(q) × vacuumPolarizationIntegrand(q, ℓ)^{μρ}`.
-/

@[expose] public section

open Complex

namespace QED.WickModel

open Wick (gauge3)

variable {C : Contraction 1 1 gauge3}

/-- A permutation exchanging two points keeps their cycle within them. -/
theorem sameCycle_of_swap {X : Type*} [Finite X] {σ : Equiv.Perm X} {x y z : X} (hxy : σ x = y)
    (hyx : σ y = x) (h : Equiv.Perm.SameCycle σ x z) : z = x ∨ z = y := by
  have key : ∀ n : ℕ, (σ ^ n) x = x ∨ (σ ^ n) x = y := by
    intro n
    induction n with
    | zero => exact Or.inl rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases ih with h' | h' <;> rw [h']
      · exact Or.inr hxy
      · exact Or.inl hyx
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  exact key n

/-- The flavoring in which the open-line vertex `a` is an electron and the other two fermion
vertices have flavor `f`. -/
def vpFlavoring (a f : Fin 3) : Flavoring gauge3 :=
  ⟨fun t => if t = Wick.fv a then 0 else f, fun _ h => absurd rfl h⟩

namespace IsVP

variable {a v w : Fin 3}

/-! ### Loop line and routing -/

/-- The loop fermion line `w → v` is not a bridge: the line `v → w` joins the same vertices. -/
theorem not_isBridge_lineV (hC : IsVP C a v w) : ¬ IsBridge (.inl hC.lineV : Line C) :=
  not_isBridge_of_parallel (g := .inl hC.lineW)
    (fun h => hC.lineV_ne_lineW (Sum.inl_injective h).symm)
    (by rw [hC.ends_lineV, hC.ends_lineW]; exact Or.inr rfl)

/-- The loop fermion line `v → w` is not a bridge: the line `w → v` joins the same vertices. -/
theorem not_isBridge_lineW (hC : IsVP C a v w) : ¬ IsBridge (.inl hC.lineW : Line C) :=
  not_isBridge_of_parallel (g := .inl hC.lineV) (fun h => hC.lineV_ne_lineW (Sum.inl_injective h))
    (by rw [hC.ends_lineV, hC.ends_lineW]; exact Or.inr rfl)

/-- The loop line is the fermion line with the smaller label. -/
theorem isLoopLine_lineV (hC : IsVP C a v w) (h : v < w) : IsLoopLine (.inl hC.lineV : Line C) := by
  refine ⟨hC.not_isBridge_lineV, fun g hg => ?_⟩
  have hV : Line.label (.inl hC.lineV : Line C) = v.val := label_fline _
  rcases hC.line_cases g with rfl | rfl | rfl
  · exact le_rfl
  · have hW : Line.label (.inl hC.lineW : Line C) = w.val := label_fline _
    rw [hV, hW]; exact Fin.le_def.mp h.le
  · exact absurd hC.isBridge_photonLine hg

/-- For `w < v` the loop line is the fermion line `v → w`, the one with the smaller label. -/
theorem isLoopLine_lineW (hC : IsVP C a v w) (h : w < v) : IsLoopLine (.inl hC.lineW : Line C) := by
  refine ⟨hC.not_isBridge_lineW, fun g hg => ?_⟩
  have hW : Line.label (.inl hC.lineW : Line C) = w.val := label_fline _
  rcases hC.line_cases g with rfl | rfl | rfl
  · have hV : Line.label (.inl hC.lineV : Line C) = v.val := label_fline _
    rw [hV, hW]; exact Fin.le_def.mp h.le
  · exact le_rfl
  · exact absurd hC.isBridge_photonLine hg

/-- The external momenta: `p` enters and `p'` leaves at `a`, and `q = p' - p` enters at `v`. -/
theorem externalMomentum_eq (hC : IsVP C a v w) (p' p : Fin 4 → ℝ) (x : Fin 3) :
    externalMomentum C ![p'] ![p] ![p' - p] x =
      (if a = x then p else 0) + (if v = x then p' - p else 0) - (if a = x then p' else 0) := by
  rw [externalMomentum_eq_of_one hC.out hC.inn hC.photon]
  simp

/-- The routing for `v < w`: the line `v → w` carries `q + ℓ` and the photon line `±q`. -/
theorem lineMomentum_of_lt (hC : IsVP C a v w) (h : v < w) (p' p ℓ : Fin 4 → ℝ) :
    lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inl hC.lineW) = p' - p + ℓ ∧
      (lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inr hC.photonLine) = p' - p ∨
        lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inr hC.photonLine) = -(p' - p)) := by
  classical
  have hav := hC.hav
  have hvw := hC.hvw
  have haw := hC.haw
  have hl := hC.isLoopLine_lineV h
  have hiff := hl.isLoopLine_iff
  have hloop : ∀ x : Fin 3, ∑ g ∈ Finset.univ.filter (fun g : Line C => IsLoopLine g),
      ((if g.ends.2 = x then ℓ else 0) - (if g.ends.1 = x then ℓ else 0)) =
        (if v = x then ℓ else 0) - (if w = x then ℓ else 0) := fun x => by
    rw [sum_isLoopLine_eq hl, hC.ends_lineV]
  have hW : ¬ IsLoopLine (.inl hC.lineW : Line C) := fun h' =>
    hC.lineV_ne_lineW (Sum.inl_injective ((hiff _).mp h')).symm
  have hP : ¬ IsLoopLine (.inr hC.photonLine : Line C) := fun h' => Sum.inr_ne_inl ((hiff _).mp h')
  constructor
  · rw [lineMomentum_of_forall_not_joined hW (fun x hx => by
        obtain ⟨g, hg, hgx⟩ := hx
        simp only [Set.mem_ofPred_eq, not_or, hiff] at hg
        rw [hC.ends_lineW] at hgx
        rcases hC.line_cases g with h' | h' | rfl
        · exact absurd h' hg.2
        · exact absurd h' hg.1
        · rcases hC.ends_photonLine with he | he <;> rw [he] at hgx <;>
            simp only [Prod.mk.injEq] at hgx <;> omega),
      hC.ends_lineW, hloop, hC.externalMomentum_eq]
    simp [hav, hvw.symm]
  · rcases hC.ends_photonLine with he | he
    · right
      rw [lineMomentum_of_forall_not_joined hP (fun x hx => by
          obtain ⟨g, hg, hgx⟩ := hx
          simp only [Set.mem_ofPred_eq, not_or, hiff] at hg
          rw [he] at hgx
          rcases hC.line_cases g with h' | rfl | h'
          · exact absurd h' hg.2
          · rw [hC.ends_lineW] at hgx
            simp only [Prod.mk.injEq] at hgx
            omega
          · exact absurd h' hg.1),
        he, hloop, hC.externalMomentum_eq]
      simp [hav.symm, haw.symm]
    · left
      rw [lineMomentum_of_joined hP (g := .inl hC.lineW) (x := v)
        (by simp [hiff, hC.lineV_ne_lineW.symm]) (by rw [he]; exact hvw)
        (by rw [he, hC.ends_lineW]; exact Or.inr rfl)
        (fun g hg => by
          simp only [Set.mem_ofPred_eq, not_or, hiff] at hg
          rcases hC.line_cases g with h' | h' | h'
          · exact absurd h' hg.2
          · exact h'
          · exact absurd h' hg.1),
        he, hloop, hloop, hC.externalMomentum_eq, hC.externalMomentum_eq]
      simp [hav, hvw, haw, hvw.symm]

/-- The routing for `w < v`: the line `w → v` carries `ℓ - q` and the photon line `±q`. -/
theorem lineMomentum_of_gt (hC : IsVP C a v w) (h : w < v) (p' p ℓ : Fin 4 → ℝ) :
    lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inl hC.lineV) = ℓ - (p' - p) ∧
      (lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inr hC.photonLine) = p' - p ∨
        lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inr hC.photonLine) = -(p' - p)) := by
  classical
  have hav := hC.hav
  have hvw := hC.hvw
  have haw := hC.haw
  have hl := hC.isLoopLine_lineW h
  have hiff := hl.isLoopLine_iff
  have hloop : ∀ x : Fin 3, ∑ g ∈ Finset.univ.filter (fun g : Line C => IsLoopLine g),
      ((if g.ends.2 = x then ℓ else 0) - (if g.ends.1 = x then ℓ else 0)) =
        (if w = x then ℓ else 0) - (if v = x then ℓ else 0) := fun x => by
    rw [sum_isLoopLine_eq hl, hC.ends_lineW]
  have hV : ¬ IsLoopLine (.inl hC.lineV : Line C) := fun h' =>
    hC.lineV_ne_lineW (Sum.inl_injective ((hiff _).mp h'))
  have hP : ¬ IsLoopLine (.inr hC.photonLine : Line C) := fun h' => Sum.inr_ne_inl ((hiff _).mp h')
  constructor
  · rw [lineMomentum_of_joined hV (g := .inr hC.photonLine) (x := a)
      (by simp [hiff]) (by rw [hC.ends_lineV]; exact haw)
      (by rw [hC.ends_lineV]; rcases hC.ends_photonLine with he | he
          · exact Or.inr he
          · exact Or.inl he)
      (fun g hg => by
        simp only [Set.mem_ofPred_eq, not_or, hiff] at hg
        rcases hC.line_cases g with h' | h' | h'
        · exact absurd h' hg.1
        · exact absurd h' hg.2
        · exact h'),
      hC.ends_lineV, hloop, hloop, hC.externalMomentum_eq, hC.externalMomentum_eq]
    simp [hvw, haw, hav.symm, haw.symm]
    abel
  · rcases hC.ends_photonLine with he | he
    · right
      rw [lineMomentum_of_forall_not_joined hP (fun x hx => by
          obtain ⟨g, hg, hgx⟩ := hx
          simp only [Set.mem_ofPred_eq, not_or, hiff] at hg
          rw [he] at hgx
          rcases hC.line_cases g with rfl | h' | h'
          · rw [hC.ends_lineV] at hgx
            simp only [Prod.mk.injEq] at hgx
            omega
          · exact absurd h' hg.2
          · exact absurd h' hg.1),
        he, hloop, hC.externalMomentum_eq]
      simp [hav.symm, haw.symm]
    · left
      rw [lineMomentum_of_joined hP (g := .inl hC.lineV) (x := v)
        (by simp [hiff, hC.lineV_ne_lineW]) (by rw [he]; exact hvw)
        (by rw [he, hC.ends_lineV]; exact Or.inl rfl)
        (fun g hg => by
          simp only [Set.mem_ofPred_eq, not_or, hiff] at hg
          rcases hC.line_cases g with h' | h' | h'
          · exact h'
          · exact absurd h' hg.2
          · exact absurd h' hg.1),
        he, hloop, hloop, hC.externalMomentum_eq, hC.externalMomentum_eq]
      simp [hav, hvw, haw, hvw.symm]


/-! ### Flavors -/

/-- A preserved flavoring gives the closed loop a single flavor. -/
theorem flavor_w (hC : IsVP C a v w) {φ : Flavoring gauge3} (hφ : Preserves C φ) :
    φ.1 (Wick.fv w) = φ.1 (Wick.fv v) := by
  have := hφ (.inr (Wick.fv v))
  rwa [hC.vw] at this

/-- The flavor of the loop vertex `v` under `vpFlavoring a f` is `f`. -/
theorem vpFlavoring_v (hC : IsVP C a v w) (f : Fin 3) : (vpFlavoring a f).1 (Wick.fv v) = f := by
  simp [vpFlavoring, hC.hav.symm]

/-- **The flavorings preserved by a vacuum polarization loop**: the open line is an electron line,
and the closed loop has a single flavor. -/
theorem preserves_iff (hC : IsVP C a v w) (φ : Flavoring gauge3) :
    Preserves C φ ↔ φ = vpFlavoring a (φ.1 (Wick.fv v)) := by
  have hav := hC.hav
  have hvw := hC.hvw
  have haw := hC.haw
  constructor
  · intro hφ
    have ha : φ.1 (Wick.fv a) = 0 := by
      have := hφ (.inl 0)
      rwa [hC.out] at this
    apply Subtype.ext
    funext t
    rcases fv3_cases hav hvw haw t with rfl | rfl | rfl
    · simp [vpFlavoring, ha]
    · simp [vpFlavoring, hav.symm]
    · simp [vpFlavoring, haw.symm, hC.flavor_w hφ]
  · intro hφ y
    rw [hφ]
    rcases fermion_field_cases hav hvw haw y with rfl | rfl | rfl | rfl
    · rw [hC.out]
      simp [fermionFlavor, vpFlavoring]
    · rw [hC.inn]
      simp [fermionFlavor, vpFlavoring]
    · rw [hC.vw]
      simp [fermionFlavor, vpFlavoring, hav.symm, haw.symm]
    · rw [hC.wv]
      simp [fermionFlavor, vpFlavoring, hav.symm, haw.symm]

/-- **The sum over the preserved flavorings** is the sum over the flavor of the closed loop. -/
theorem sum_preserves (hC : IsVP C a v w) {M : Type*} [AddCommMonoid M]
    [Fintype (Flavoring gauge3)] [DecidablePred (Preserves C)] (F : Flavoring gauge3 → M) :
    ∑ φ ∈ (Finset.univ : Finset (Flavoring gauge3)).filter (Preserves C), F φ =
      ∑ f : Fin 3, F (vpFlavoring a f) := by
  refine Finset.sum_nbij' (fun φ => φ.1 (Wick.fv v)) (vpFlavoring a)
    (fun _ _ => Finset.mem_univ _)
    (fun f _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hC.preserves_iff _).mpr (by
      rw [hC.vpFlavoring_v])⟩)
    (fun φ hφ => ((hC.preserves_iff φ).mp (Finset.mem_filter.mp hφ).2).symm)
    (fun f _ => hC.vpFlavoring_v f)
    (fun φ hφ => by rw [← (hC.preserves_iff φ).mp (Finset.mem_filter.mp hφ).2])

/-- The closed fermion loop through `v` and `w`. -/
def closedLoop (hC : IsVP C a v w) : ClosedLoop C :=
  ⟨Quotient.mk _ (.inr (Wick.fv v)), fun i h => by
    have h' : Equiv.Perm.SameCycle C.1.1 (.inl i) (.inr (Wick.fv v)) := Quotient.exact h
    rw [Subsingleton.elim i 0] at h'
    rcases sameCycle_of_swap hC.out (by rw [hC.inn]) h' with h'' | h''
    · exact Sum.inr_ne_inl h''
    · exact hC.hav (fv3_injective (Sum.inr_injective h'')).symm⟩

/-- The contraction has one closed fermion loop. -/
theorem eq_closedLoop (hC : IsVP C a v w) (q : ClosedLoop C) : q = hC.closedLoop := by
  obtain ⟨q, hq⟩ := q
  obtain ⟨y, rfl⟩ := Quotient.exists_rep q
  apply Subtype.ext
  change Quotient.mk _ y = Quotient.mk _ (.inr (Wick.fv v))
  rcases fermion_field_cases hC.hav hC.hvw hC.haw y with rfl | rfl | rfl | rfl
  · exact absurd rfl (hq 0)
  · exact absurd (Quotient.sound
      (show Equiv.Perm.SameCycle C.1.1 _ _ from ⟨1, by simp [hC.out]⟩)) (hq 0)
  · rfl
  · exact Quotient.sound (show Equiv.Perm.SameCycle C.1.1 _ _ from ⟨1, by simp [hC.wv]⟩)

/-- The regulator weight of the flavor-`f` loop is `c_f`. -/
theorem loopWeight_vpFlavoring (P : Params) (hC : IsVP C a v w) (f : Fin 3) :
    loopWeight P C (vpFlavoring a f) = P.loopCoeff f := by
  classical
  rw [loopWeight, Fintype.prod_eq_single hC.closedLoop fun q hq => absurd (hC.eq_closedLoop q) hq]
  have hmem0 : Equiv.Perm.SameCycle C.1.1
      (Quotient.out (Quotient.mk (Equiv.Perm.SameCycle.setoid C.1.1) (.inr (Wick.fv v))))
      (.inr (Wick.fv v)) :=
    Quotient.exact (Quotient.out_eq (Quotient.mk (Equiv.Perm.SameCycle.setoid C.1.1)
      (.inr (Wick.fv v))))
  have hmem := hmem0.symm
  change P.loopCoeff (fermionFlavor (vpFlavoring a f) (Quotient.out (Quotient.mk
    (Equiv.Perm.SameCycle.setoid C.1.1) (.inr (Wick.fv v))))) = _
  rcases sameCycle_of_swap hC.vw hC.wv hmem with h | h <;> rw [h]
  · simp [fermionFlavor, vpFlavoring, hC.hav.symm]
  · simp [fermionFlavor, vpFlavoring, hC.haw.symm]

/-- The fermion pairing of a vacuum polarization loop: two transpositions. -/
theorem fst_eq (hC : IsVP C a v w) :
    C.1.1 = Equiv.swap (.inl 0) (.inr (Wick.fv a)) *
      Equiv.swap (.inr (Wick.fv v)) (.inr (Wick.fv w)) := by
  have hne : ∀ s t : Fin 3, s ≠ t → (Sum.inr (Wick.fv s) : Fin 1 ⊕ Wick.FermionVertex gauge3) ≠
      .inr (Wick.fv t) := fun s t h h' => h (fv3_injective (Sum.inr_injective h'))
  ext1 y
  rcases fermion_field_cases hC.hav hC.hvw hC.haw y with rfl | rfl | rfl | rfl <;>
    simp only [Equiv.Perm.mul_apply]
  · rw [hC.out, Equiv.swap_apply_of_ne_of_ne Sum.inl_ne_inr Sum.inl_ne_inr,
      Equiv.swap_apply_left]
  · rw [hC.inn, Equiv.swap_apply_of_ne_of_ne (hne a v hC.hav) (hne a w hC.haw),
      Equiv.swap_apply_right]
  · rw [hC.vw, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl
      (hne w a hC.haw.symm)]
  · rw [hC.wv, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl
      (hne v a hC.hav.symm)]

/-- A vacuum polarization loop has fermionic sign `-1`: `(-1)³` from the vertices times the sign
`+1` of two transpositions. -/
theorem fermionSign_eq (hC : IsVP C a v w) : fermionSign C = -1 := by
  have hne : (Sum.inr (Wick.fv v) : Fin 1 ⊕ Wick.FermionVertex gauge3) ≠ .inr (Wick.fv w) :=
    fun h' => hC.hvw (fv3_injective (Sum.inr_injective h'))
  rw [fermionSign, card_fermionVertex_gauge3, hC.fst_eq, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap Sum.inl_ne_inr, Equiv.Perm.sign_swap hne]
  simp

/-! ### Amplitude and value -/

/-- **The amplitude of a vacuum polarization loop** of the flavor of `v`, with loop line momenta
`kV`, `kW`: `∑_{νρ} [i e γ^ν]_{αβ} (1/i) Δ̃_{νρ}(q) (ie)² (1/i)² Tr[γ^μ S̃(kV) γ^ρ S̃(kW)]`. -/
theorem contractionAmplitude_eq (P : Params) (hC : IsVP C a v w) {φ : Flavoring gauge3}
    (hφ : Preserves C φ) {p' p ℓ kV kW : Fin 4 → ℝ}
    (hV : lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inl hC.lineV) = kV)
    (hW : lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inl hC.lineW) = kW)
    (hP : lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inr hC.photonLine) = p' - p ∨
      lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inr hC.photonLine) = -(p' - p))
    (α β μ : Fin 4) :
    contractionAmplitude P C φ ![p'] ![p] ![p' - p] ℓ ![α] ![β] ![μ] =
      ∑ ν, ∑ ρ, (I * P.e) * Dirac.gamma ν α β *
        ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (p' - p) ν ρ) *
        ((I * P.e) ^ 2 * (1 / I) ^ 2 *
          Matrix.trace (Dirac.gamma μ *
            QED.OneLoop.electronPropagator (P.mass (φ.1 (Wick.fv v))) P.ε kV *
            Dirac.gamma ρ * QED.OneLoop.electronPropagator (P.mass (φ.1 (Wick.fv v))) P.ε kW)) := by
  have hav := hC.hav
  have hvw := hC.hvw
  have haw := hC.haw
  have hprop : ∀ lor : Wick.PhotonSlot gauge3 → Fin 4,
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε
          (lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inr hC.photonLine))
          (lor hC.photonLine.1) (lor hC.photonLine.head) =
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (p' - p) (lor (Wick.ps a)) (lor (Wick.ps w)) :=
    fun lor => photonPropagator_of_pair hP lor (hC.photon.line_spec _ _ _)
  rw [contractionAmplitude]
  simp only [spinor_constraint_out_iff_of_one hC.out,
    spinor_constraint_in_iff_of_one hC.inn, lorentz_constraint_iff_of_one hC.photon,
    prod_fin_three_eq hav hvw haw, vertexFactor_gauge3,
    prod_eq_mul_of_two hC.lineV_ne_lineW hC.fermionLine_cases,
    Fintype.prod_eq_single hC.photonLine fun l hl => absurd (hC.photon.eq_line _ _ _ l) hl,
    IsVP.lineV_val, IsVP.tail_lineV, IsVP.lineW_val, IsVP.tail_lineW, hC.flavor_w hφ, hV, hW,
    hprop]
  rw [show (∑ α : Wick.FermionVertex gauge3 → Fin 4, ∑ β : Wick.FermionVertex gauge3 → Fin 4,
      ∑ lor : Wick.PhotonSlot gauge3 → Fin 4, _) =
      ∑ lor : Wick.PhotonSlot gauge3 → Fin 4, ∑ α : Wick.FermionVertex gauge3 → Fin 4,
        ∑ β : Wick.FermionVertex gauge3 → Fin 4, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  have hfa : Wick.fv a ≠ Wick.fv v := fv3_injective.ne hav
  have hfb : Wick.fv v ≠ Wick.fv w := fv3_injective.ne hvw
  have hfc : Wick.fv a ≠ Wick.fv w := fv3_injective.ne haw
  have hpa : Wick.ps a ≠ Wick.ps v := ps3_injective.ne hav
  have hpb : Wick.ps v ≠ Wick.ps w := ps3_injective.ne hvw
  have hpc : Wick.ps a ≠ Wick.ps w := ps3_injective.ne haw
  simp only [sum_pi_eq_of_three hpa hpb hpc (ps3_cases hav hvw haw),
    sum_pi_eq_of_three hfa hfb hfc (fv3_cases hav hvw haw), ite_true, hfa.symm, hfb.symm,
    hfc.symm, hpa.symm, hpb.symm, hpc.symm, ite_false]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Matrix.cons_val_zero]
  exact sum_polarization_index3 _ _ _ _ _ _ _ _ _


/-- The trace of a product of four matrices, rotated. -/
theorem trace_rotate (A B C D : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix.trace (A * B * C * D) = Matrix.trace (B * C * D * A) := by
  rw [show A * B * C * D = A * (B * C * D) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]

open scoped Classical in
/-- The regulated amplitude of a vacuum polarization loop: the sum over the flavors of the
closed loop, with weights `c_f`. -/
theorem regulatedAmplitude_eq (P : Params) (hC : IsVP C a v w) (p' p ℓ : Fin 4 → ℝ)
    (α β μ : Fin 4) :
    regulatedAmplitude P C ![p'] ![p] ![p' - p] ℓ ![α] ![β] ![μ] =
      ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
        contractionAmplitude P C (vpFlavoring a f) ![p'] ![p] ![p' - p] ℓ ![α] ![β] ![μ] := by
  rw [regulatedAmplitude, hC.sum_preserves]
  simp only [hC.loopWeight_vpFlavoring]

/-- The preserved flavoring `vpFlavoring a f`. -/
theorem preserves_vpFlavoring (hC : IsVP C a v w) (f : Fin 3) : Preserves C (vpFlavoring a f) :=
  (hC.preserves_iff _).mpr (by rw [hC.vpFlavoring_v])

/-- **The value of a vacuum polarization loop.** Minus its value (its fermionic sign is `-1`) is
the energy-first integral of `∑_{νρ} [i e γ^ν]_{αβ} (1/i) Δ̃_{νρ}(q)` times the vacuum
polarization integrand `vacuumPolarizationIntegrand(q, ℓ)^{μρ}`, `q = p' - p`. For `v < w` the
routed trace is the source's by cyclicity; for `w < v` it is the source's at the shifted loop
momentum `ℓ - q`. -/
theorem neg_contractionValue_eq (P : Params) (hC : IsVP C a v w) (p' p : Fin 4 → ℝ)
    (α β μ : Fin 4) :
    -contractionValue P C ![p'] ![p] ![p' - p] ![α] ![β] ![μ] =
      QED.OneLoop.energyFirstIntegral fun ℓ =>
        ∑ ν, ∑ ρ, (I * P.e) * Dirac.gamma ν α β *
          ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (p' - p) ν ρ) *
            vacuumPolarizationIntegrand P P.ε (p' - p) ℓ μ ρ := by
  rcases lt_or_gt_of_ne hC.hvw with h | h
  · have hl := hC.isLoopLine_lineV h
    rw [contractionValue_of_isLoopLine P hl, neg_eq_neg_one_mul,
      ← QED.OneLoop.energyFirstIntegral_const_mul]
    congr 1
    funext ℓ
    obtain ⟨hW, hP⟩ := hC.lineMomentum_of_lt h p' p ℓ
    simp only [hC.regulatedAmplitude_eq,
      hC.contractionAmplitude_eq P (hC.preserves_vpFlavoring _)
        (lineMomentum_of_isLoopLine hl _ _ _ _) hW hP, hC.vpFlavoring_v,
      vacuumPolarizationIntegrand, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun f _ => ?_
    rw [trace_rotate (QED.OneLoop.electronPropagator _ _ (ℓ + (p' - p))), add_comm ℓ]
    ring
  · have hl := hC.isLoopLine_lineW h
    rw [contractionValue_of_isLoopLine P hl, neg_eq_neg_one_mul,
      ← QED.OneLoop.energyFirstIntegral_const_mul]
    conv_rhs => rw [← QED.OneLoop.energyFirstIntegral_sub_right_eq_self _ (p' - p)]
    congr 1
    funext ℓ
    obtain ⟨hV, hP⟩ := hC.lineMomentum_of_gt h p' p ℓ
    simp only [hC.regulatedAmplitude_eq,
      hC.contractionAmplitude_eq P (hC.preserves_vpFlavoring _) hV
        (lineMomentum_of_isLoopLine hl _ _ _ _) hP, hC.vpFlavoring_v,
      vacuumPolarizationIntegrand, Finset.mul_sum, sub_add_cancel]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun f _ => ?_
    rw [trace_rotate (QED.OneLoop.electronPropagator _ _ ℓ)]
    ring

end IsVP

end QED.WickModel

end
