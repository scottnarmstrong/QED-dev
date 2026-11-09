/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Wick.Gauge3
public import QED.Frozen.OneLoop.VertexIntegrand
import QED.Integration.EnergyFirstShift
import QED.Algebra.Minkowski
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# The value of a vertex-correction contraction

The evaluation part of the frozen goal (W₁) `QED.Wick.wickVertex_eq`: for a contraction `C` of
the three gauge vertices `gauge3` with `IsChain C a b c` (fermion chain `c → b → a`, external
photon at `b`, internal photon joining `a` and `c`), the value `contractionValue` is the
energy-first integral of the frozen one-loop vertex integrand `QED.OneLoop.vertexIntegrand`.

The proof has three steps.

* **Routing.** `C` has three internal lines: the fermion lines `b → a` and `c → b` and the photon
  line between `a` and `c`. The loop line is the fermion line with the smaller label, `b → a` if
  `a < b` and `c → b` otherwise, and the canonical routing (V₁₆) gives the fermion lines
  `p' + ℓ'` and `p + ℓ'` and the photon line `±ℓ'`, with `ℓ' = ℓ - p'` if `a < b` and
  `ℓ' = ℓ - p` otherwise.
* **Index sums.** With the external indices fixed, the sum over the spinor and Lorentz indices of
  the vertex fields is the matrix product `γ^ρ S̃ γ^μ S̃ γ^ν` contracted with `Δ̃_{νρ}`
  (`QED.Wick.sum_chain_eq`); the photon propagator is symmetric and even in its momentum.
* **Shift.** The amplitude at `ℓ`, times `(2π)⁻⁴`, is the vertex integrand at `ℓ'`, and the
  energy-first integral is invariant under the shift `ℓ ↦ ℓ - p'` or `ℓ ↦ ℓ - p`
  (`QED.OneLoop.energyFirstIntegral_sub_right_eq_self`).

No hypothesis on the parameters is needed.

## Main statements

* `QED.Wick.sum_chain_eq`: the index sum of the vertex-correction amplitude.
* `QED.Wick.IsChain.contractionAmplitude_apply`: the amplitude of a vertex-correction
  contraction.
* `QED.Wick.IsChain.integrand_eq`: its integrand is the shifted vertex integrand.
* `QED.Wick.contractionValue_of_isChain`: its value is the energy-first integral of the vertex
  integrand.
-/

@[expose] public section

open Complex

namespace QED.Wick

section Triple

variable {X : Type*} [Fintype X] [DecidableEq X] {u v w : X}

/-- A finite type covered by three elements `u, v, w` has `univ = {u, v, w}`. -/
private theorem univ_eq_of_forall_eq_or_eq_or_eq (hX : ∀ x, x = u ∨ x = v ∨ x = w) :
    (Finset.univ : Finset X) = {u, v, w} := by
  ext x
  simpa using hX x

/-- A product over a finite type covered by three distinct elements. -/
theorem prod_eq_mul_mul_of_forall_eq_or_eq_or_eq {M : Type*} [CommMonoid M] (huv : u ≠ v)
    (huw : u ≠ w) (hvw : v ≠ w) (hX : ∀ x, x = u ∨ x = v ∨ x = w) (f : X → M) :
    ∏ x, f x = f u * f v * f w := by
  rw [univ_eq_of_forall_eq_or_eq_or_eq hX, Finset.prod_insert (by simp [huv, huw]),
    Finset.prod_pair hvw, mul_assoc]

/-- A sum over a finite type covered by three distinct elements. -/
theorem sum_eq_add_add_of_forall_eq_or_eq_or_eq {M : Type*} [AddCommMonoid M] (huv : u ≠ v)
    (huw : u ≠ w) (hvw : v ≠ w) (hX : ∀ x, x = u ∨ x = v ∨ x = w) (f : X → M) :
    ∑ x, f x = f u + f v + f w := by
  rw [univ_eq_of_forall_eq_or_eq_or_eq hX, Finset.sum_insert (by simp [huv, huw]),
    Finset.sum_pair hvw, add_assoc]

/-- A sum over the functions on a finite type covered by three distinct elements `u, v, w` is a
triple sum over their values at `u`, `v` and `w`. -/
theorem sum_pi_eq_of_forall_eq_or_eq_or_eq {R M : Type*} [Fintype R] [AddCommMonoid M]
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hX : ∀ x, x = u ∨ x = v ∨ x = w)
    (g : (X → R) → M) :
    ∑ f, g f = ∑ x, ∑ y, ∑ z, g (fun t => if t = u then x else if t = v then y else z) := by
  let e : (X → R) ≃ R × R × R :=
    { toFun := fun f => (f u, f v, f w)
      invFun := fun q t => if t = u then q.1 else if t = v then q.2.1 else q.2.2
      left_inv := fun f => by
        funext t
        rcases hX t with rfl | rfl | rfl <;> simp [huv.symm, huw.symm, hvw.symm]
      right_inv := fun q => by simp [huv.symm, huw.symm, hvw.symm] }
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rfl

end Triple

/-- The entry of a product of five matrices as an iterated sum over the four internal indices. -/
private theorem mul_mul_mul_mul_apply (A B D E G : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    (A * B * D * E * G) i j =
      ∑ y, ∑ w, ∑ x, ∑ z, A i x * B x y * D y z * E z w * G w j := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  calc ∑ w, ∑ z, ∑ y, ∑ x, A i x * B x y * D y z * E z w * G w j
      = ∑ w, ∑ y, ∑ z, ∑ x, A i x * B x y * D y z * E z w * G w j :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ w, ∑ y, ∑ x, ∑ z, A i x * B x y * D y z * E z w * G w j :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

section ChainSum

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  {xa xb xc : X} {ya yb yc : Y}

/-- The index sum of the vertex-correction amplitude: the sum over the spinor indices `α, β` and
the Lorentz indices `lor` of the fields at three vertices, with the external indices fixed, is
the matrix product `γ^ρ S₁ γ^μ S₂ γ^ν` contracted with `D_{νρ}`. -/
theorem sum_chain_eq (hxab : xa ≠ xb) (hxac : xa ≠ xc) (hxbc : xb ≠ xc)
    (hX : ∀ x, x = xa ∨ x = xb ∨ x = xc) (hyab : ya ≠ yb) (hyac : ya ≠ yc) (hybc : yb ≠ yc)
    (hY : ∀ y, y = ya ∨ y = yb ∨ y = yc) (G : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (S₁ S₂ : Matrix (Fin 4) (Fin 4) ℂ) (D : Fin 4 → Fin 4 → ℂ) (c₁ c₂ : ℂ) (μ αe βe : Fin 4) :
    ∑ α : X → Fin 4, ∑ β : X → Fin 4, ∑ lor : Y → Fin 4,
      (if α xa = αe ∧ β xc = βe ∧ lor yb = μ then 1 else 0) *
        ((c₁ * G (lor ya) (α xa) (β xa) * (c₁ * G (lor yb) (α xb) (β xb)) *
            (c₁ * G (lor yc) (α xc) (β xc))) *
          (c₂ * S₁ (β xa) (α xb) * (c₂ * S₂ (β xb) (α xc))) *
          (c₂ * D (lor yc) (lor ya))) =
      c₁ ^ 3 * c₂ ^ 3 * ∑ ν, ∑ ρ, D ν ρ * (G ρ * S₁ * G μ * S₂ * G ν) αe βe := by
  rw [show (∑ α : X → Fin 4, ∑ β : X → Fin 4, ∑ lor : Y → Fin 4, _) =
      ∑ lor : Y → Fin 4, ∑ α : X → Fin 4, ∑ β : X → Fin 4, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  have hXs := fun (g : (X → Fin 4) → ℂ) =>
    sum_pi_eq_of_forall_eq_or_eq_or_eq hxab hxac hxbc hX g
  have hYs := fun (g : (Y → Fin 4) → ℂ) =>
    sum_pi_eq_of_forall_eq_or_eq_or_eq hyab hyac hybc hY g
  simp only [hXs, hYs, ite_true, hxab.symm, hxac.symm, hxbc.symm, hyab.symm, hyac.symm,
    hybc.symm, ite_false]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  conv_lhs => rw [Finset.sum_comm]
  simp only [mul_mul_mul_mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

end ChainSum

/-! ### Generic facts about routing -/

/-- Reachability for a relation that only relates `x` and `y`, in either order. -/
private theorem reflTransGen_iff_of_forall_iff {α : Type*} {R : α → α → Prop} {x y : α}
    (h : ∀ u w, R u w ↔ (u = x ∧ w = y) ∨ (u = y ∧ w = x)) {s v : α} :
    Relation.ReflTransGen R s v ↔ v = s ∨ (s = x ∧ v = y) ∨ (s = y ∧ v = x) := by
  constructor
  · intro hR
    induction hR with
    | refl => exact Or.inl rfl
    | tail _ hbc ih =>
      rw [h] at hbc
      grind
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ((h _ _).2 (Or.inl ⟨rfl, rfl⟩))
    · exact Relation.ReflTransGen.single ((h _ _).2 (Or.inr ⟨rfl, rfl⟩))

open scoped Classical in
/-- The routed momentum of a non-loop line `f` of a contraction with exactly three internal
lines `f`, the loop line `l`, and `r`: the momentum injected into the vertices reachable from the
tail of `f` through `r`. -/
private theorem lineMomentum_eq_sum_filter {N : ℕ} {κ : Fin N → VertexKind} {C : Contraction κ}
    {f l r : Line C} (hall : ∀ g, g = f ∨ g = l ∨ g = r) (hloop : ∀ g, IsLoopLine g ↔ g = l)
    (hfl : f ≠ l) (hrf : r ≠ f) (hrl : r ≠ l) (p' p ℓ : Fin 4 → ℝ) :
    lineMomentum C p' p ℓ f =
      ∑ v ∈ Finset.univ.filter (fun v => v = f.ends.1 ∨ (f.ends.1 = r.ends.1 ∧ v = r.ends.2) ∨
          (f.ends.1 = r.ends.2 ∧ v = r.ends.1)),
        (externalMomentum C p' p v +
          ((if l.ends.2 = v then ℓ else 0) - (if l.ends.1 = v then ℓ else 0))) := by
  have hJ : ∀ u w, Joined C {g | g = f ∨ IsLoopLine g} u w ↔
      (u = r.ends.1 ∧ w = r.ends.2) ∨ (u = r.ends.2 ∧ w = r.ends.1) := by
    intro u w
    constructor
    · rintro ⟨g, hg, h⟩
      rcases hall g with rfl | rfl | rfl
      · exact absurd (Or.inl rfl) hg
      · exact absurd (Or.inr ((hloop _).2 rfl)) hg
      · rcases h with h | h <;> simp [h]
    · intro h
      refine ⟨r, ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq, hloop]
        tauto
      · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
  unfold lineMomentum
  rw [ite_eq_right (fun h => hfl ((hloop f).1 h))]
  have hL : (Finset.univ.filter fun g : Line C => IsLoopLine g) = {l} := by
    ext g
    simp [hloop]
  simp only [hL, Finset.sum_singleton]
  exact Finset.sum_congr
    (Finset.filter_congr fun v _ => reflTransGen_iff_of_forall_iff hJ) fun _ _ => rfl

/-! ### The three gauge vertices -/

private theorem fv_injective : Function.Injective fv := fun _ _ h => congrArg Subtype.val h

private theorem ps_injective : Function.Injective ps := fun _ _ h => congrArg Sigma.fst h

private theorem fv_val_eq (x : FermionVertex gauge3) : fv x.1 = x := rfl

private theorem fv_val (t : Fin 3) : (fv t).1 = t := rfl

private theorem ps_fst (t : Fin 3) : (ps t).1 = t := rfl

private theorem ps_fst_eq (x : PhotonSlot gauge3) : ps x.1 = x := by
  obtain ⟨t, k⟩ := x
  exact Sigma.ext rfl (heq_of_eq (Subsingleton.elim (α := Fin 1) _ _))

private theorem photonKey_ps (t : Fin 3) : photonKey (ps t) = 2 * t.val := rfl

private theorem vertexFactor_gauge3 (e δ₁ δ₂ δm δ₃ m : ℝ) (α β : FermionVertex gauge3 → Fin 4)
    (lor : PhotonSlot gauge3 → Fin 4) (kψ : FermionVertex gauge3 → Fin 4 → ℝ)
    (kA : PhotonSlot gauge3 → Fin 4 → ℝ) (t : Fin 3) :
    vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      I * e * Dirac.gamma (lor (ps t)) (α (fv t)) (β (fv t)) := rfl

private theorem photonPropagator_neg (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    QED.OneLoop.photonPropagator mγ Λ ε (-k) μ ν = QED.OneLoop.photonPropagator mγ Λ ε k μ ν := by
  simp [QED.OneLoop.photonPropagator, Minkowski.dot]

private theorem photonPropagator_comm (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    QED.OneLoop.photonPropagator mγ Λ ε k μ ν = QED.OneLoop.photonPropagator mγ Λ ε k ν μ := by
  simp only [QED.OneLoop.photonPropagator, Minkowski.metric_symm μ ν]

namespace IsChain

variable {C : Contraction gauge3} {a b c : Fin 3}

private theorem ne_ab (hC : IsChain C a b c) : a ≠ b := hC.1
private theorem ne_bc (hC : IsChain C a b c) : b ≠ c := hC.2.1
private theorem ne_ac (hC : IsChain C a b c) : a ≠ c := hC.2.2.1
private theorem psi_none (hC : IsChain C a b c) : C.1.1 none = some (fv a) := hC.2.2.2.1
private theorem psi_a (hC : IsChain C a b c) : C.1.1 (some (fv a)) = some (fv b) :=
  hC.2.2.2.2.1
private theorem psi_b (hC : IsChain C a b c) : C.1.1 (some (fv b)) = some (fv c) :=
  hC.2.2.2.2.2.1
private theorem psi_c (hC : IsChain C a b c) : C.1.1 (some (fv c)) = none :=
  hC.2.2.2.2.2.2.1
private theorem photon_none (hC : IsChain C a b c) : C.1.2 none = some (ps b) :=
  hC.2.2.2.2.2.2.2.1
private theorem photon_a (hC : IsChain C a b c) : C.1.2 (some (ps a)) = some (ps c) :=
  hC.2.2.2.2.2.2.2.2

private theorem photon_b (hC : IsChain C a b c) : C.1.2 (some (ps b)) = none := by
  rw [← hC.photon_none]
  exact (C.2 none).1

private theorem photon_c (hC : IsChain C a b c) : C.1.2 (some (ps c)) = some (ps a) := by
  rw [← hC.photon_a]
  exact (C.2 _).1

private theorem eq_or_eq_or_eq (hC : IsChain C a b c) (t : Fin 3) : t = a ∨ t = b ∨ t = c := by
  have := hC.ne_ab
  have := hC.ne_bc
  have := hC.ne_ac
  omega

private theorem psi_some_eq_none_iff (hC : IsChain C a b c) (t : FermionVertex gauge3) :
    C.1.1 (some t) = none ↔ t = fv c :=
  ⟨fun h => Option.some_injective _ (C.1.1.injective (h.trans hC.psi_c.symm)),
    fun h => h ▸ hC.psi_c⟩

private theorem externalMomentum_eq (hC : IsChain C a b c) (p' p : Fin 4 → ℝ) (v : Fin 3) :
    externalMomentum C p' p v =
      (if v = c then p else 0) + (if v = b then p' - p else 0) - (if v = a then p' else 0) := by
  have h1 : (∃ t : FermionVertex gauge3, t.1 = v ∧ C.1.1 (some t) = none) ↔ v = c := by
    constructor
    · rintro ⟨t, ht, h⟩
      rw [hC.psi_some_eq_none_iff] at h
      subst h
      exact ht.symm
    · rintro rfl
      exact ⟨fv v, rfl, hC.psi_c⟩
  have h2 : (∃ s : PhotonSlot gauge3, s.1 = v ∧ C.1.2 none = some s) ↔ v = b := by
    constructor
    · rintro ⟨s, hs, h⟩
      rw [hC.photon_none, Option.some_inj] at h
      subst h
      exact hs.symm
    · rintro rfl
      exact ⟨ps v, rfl, hC.photon_none⟩
  have h3 : (∃ t : FermionVertex gauge3, t.1 = v ∧ C.1.1 none = some t) ↔ v = a := by
    constructor
    · rintro ⟨t, ht, h⟩
      rw [hC.psi_none, Option.some_inj] at h
      subst h
      exact ht.symm
    · rintro rfl
      exact ⟨fv v, rfl, hC.psi_none⟩
  unfold externalMomentum
  simp only [h1, h2, h3]

/-- The fermion line of `C` from `b` to `a`. -/
private def lineA (hC : IsChain C a b c) : Line C := .inl ⟨fv a, by simp [hC.psi_a]⟩

/-- The fermion line of `C` from `c` to `b`. -/
private def lineB (hC : IsChain C a b c) : Line C := .inl ⟨fv b, by simp [hC.psi_b]⟩

private theorem ends_lineA (hC : IsChain C a b c) : hC.lineA.ends = (b, a) := by
  simp [lineA, Line.ends, Option.get_of_eq_some _ hC.psi_a, fv_val]

private theorem ends_lineB (hC : IsChain C a b c) : hC.lineB.ends = (c, b) := by
  simp [lineB, Line.ends, Option.get_of_eq_some _ hC.psi_b, fv_val]

private theorem lineA_ne_lineB (hC : IsChain C a b c) : hC.lineA ≠ hC.lineB := by
  intro h
  exact hC.ne_ab (fv_injective (congrArg Subtype.val (Sum.inl_injective h)))

/-- The photon line is the field of `a` contracted with that of `c` if `a < c`, and conversely. -/
private theorem photonLine_cases (hC : IsChain C a b c) (g : PhotonLine C) :
    (g.1 = ps a ∧ C.1.2 (some g.1) = some (ps c) ∧ a < c) ∨
      (g.1 = ps c ∧ C.1.2 (some g.1) = some (ps a) ∧ c < a) := by
  obtain ⟨s, s', hs', hkey⟩ := g
  show (s = ps a ∧ C.1.2 (some s) = some (ps c) ∧ a < c) ∨
    (s = ps c ∧ C.1.2 (some s) = some (ps a) ∧ c < a)
  have hs := (ps_fst_eq s).symm
  rcases hC.eq_or_eq_or_eq s.1 with h | h | h <;> rw [h] at hs <;> subst hs
  · rw [hC.photon_a, Option.some_inj] at hs'
    subst hs'
    rw [photonKey_ps, photonKey_ps] at hkey
    exact Or.inl ⟨rfl, hC.photon_a, by omega⟩
  · rw [hC.photon_b] at hs'
    exact absurd hs' (Option.some_ne_none _).symm
  · rw [hC.photon_c, Option.some_inj] at hs'
    subst hs'
    rw [photonKey_ps, photonKey_ps] at hkey
    exact Or.inr ⟨rfl, hC.photon_c, by omega⟩

private theorem photonLine_eq (hC : IsChain C a b c) (g g' : PhotonLine C) : g = g' := by
  rcases hC.photonLine_cases g with ⟨h, -, h'⟩ | ⟨h, -, h'⟩ <;>
    rcases hC.photonLine_cases g' with ⟨k, -, k'⟩ | ⟨k, -, k'⟩
  · exact Subtype.ext (h.trans k.symm)
  · omega
  · omega
  · exact Subtype.ext (h.trans k.symm)

/-- The internal photon line of `C`. -/
private def photonLine (hC : IsChain C a b c) : PhotonLine C :=
  if h : a < c then ⟨ps a, ps c, hC.photon_a, by rw [photonKey_ps, photonKey_ps]; omega⟩
  else ⟨ps c, ps a, hC.photon_c, by
    rw [photonKey_ps, photonKey_ps]
    have := hC.ne_ac
    omega⟩

private theorem ends_inr (hC : IsChain C a b c) (g : PhotonLine C) :
    (Line.ends (Sum.inr g : Line C) = (a, c) ∧ a < c) ∨
      (Line.ends (Sum.inr g : Line C) = (c, a) ∧ c < a) := by
  rcases hC.photonLine_cases g with ⟨h, h', h''⟩ | ⟨h, h', h''⟩
  · refine Or.inl ⟨?_, h''⟩
    simp [Line.ends, h, Option.get_of_eq_some _ hC.photon_a, ps_fst]
  · refine Or.inr ⟨?_, h''⟩
    simp [Line.ends, h, Option.get_of_eq_some _ hC.photon_c, ps_fst]

private theorem eq_line (hC : IsChain C a b c) (g : Line C) :
    g = hC.lineA ∨ g = hC.lineB ∨ g = .inr hC.photonLine := by
  rcases g with ⟨t, ht⟩ | g
  · rcases hC.eq_or_eq_or_eq t.1 with h | h | h
    · exact Or.inl (congrArg Sum.inl (Subtype.ext ((fv_val_eq t).symm.trans (congrArg fv h))))
    · exact Or.inr (Or.inl
        (congrArg Sum.inl (Subtype.ext ((fv_val_eq t).symm.trans (congrArg fv h)))))
    · exact absurd ((hC.psi_some_eq_none_iff t).2
        ((fv_val_eq t).symm.trans (congrArg fv h))) ht
  · exact Or.inr (Or.inr (congrArg Sum.inr (hC.photonLine_eq _ _)))

private theorem isLoopLine_iff_of_lt (hC : IsChain C a b c) (hab : a < b) (g : Line C) :
    IsLoopLine g ↔ g = hC.lineA := by
  constructor
  · intro hg
    rcases hC.eq_line g with rfl | rfl | rfl
    · rfl
    · exact absurd (show b.val ≤ a.val from hg hC.lineA) (by omega)
    · exact absurd (show 3 + photonKey hC.photonLine.1 ≤ a.val from hg hC.lineA) (by omega)
  · rintro rfl g'
    rcases hC.eq_line g' with rfl | rfl | rfl
    · exact le_rfl
    · exact (show a.val ≤ b.val by omega)
    · exact (show a.val ≤ 3 + photonKey hC.photonLine.1 by omega)

private theorem isLoopLine_iff_of_gt (hC : IsChain C a b c) (hab : b < a) (g : Line C) :
    IsLoopLine g ↔ g = hC.lineB := by
  constructor
  · intro hg
    rcases hC.eq_line g with rfl | rfl | rfl
    · exact absurd (show a.val ≤ b.val from hg hC.lineB) (by omega)
    · rfl
    · exact absurd (show 3 + photonKey hC.photonLine.1 ≤ b.val from hg hC.lineB) (by omega)
  · rintro rfl g'
    rcases hC.eq_line g' with rfl | rfl | rfl
    · exact (show b.val ≤ a.val by omega)
    · exact le_rfl
    · exact (show b.val ≤ 3 + photonKey hC.photonLine.1 by omega)

/-- The line from `b` to `a` carries `p' + ℓ'`, with `ℓ' = ℓ - p'` if it is the loop line
(`a < b`) and `ℓ' = ℓ - p` otherwise. -/
private theorem lineMomentum_lineA (hC : IsChain C a b c) (p' p ℓ : Fin 4 → ℝ) :
    lineMomentum C p' p ℓ hC.lineA = p' + (ℓ - if a < b then p' else p) := by
  have hab := hC.ne_ab
  have hbc := hC.ne_bc
  have hac := hC.ne_ac
  rcases lt_or_gt_of_ne hab with h | h
  · rw [lineMomentum, ite_eq_left ((hC.isLoopLine_iff_of_lt h _).2 rfl), ite_eq_left h]
    abel
  · rw [lineMomentum_eq_sum_filter (r := .inr hC.photonLine) hC.eq_line
      (hC.isLoopLine_iff_of_gt h) hC.lineA_ne_lineB (fun h' => Sum.inr_ne_inl h')
      (fun h' => Sum.inr_ne_inl h'), Finset.sum_filter,
      sum_eq_add_add_of_forall_eq_or_eq_or_eq hab hac hbc hC.eq_or_eq_or_eq,
      ite_eq_right (show ¬ a < b by omega)]
    rcases hC.ends_inr hC.photonLine with ⟨hP, -⟩ | ⟨hP, -⟩ <;>
      simp [hC.ends_lineA, hC.ends_lineB, hP, hC.externalMomentum_eq, hab, hab.symm, hbc,
        hbc.symm, hac, hac.symm] <;> abel

/-- The line from `c` to `b` carries `p + ℓ'`. -/
private theorem lineMomentum_lineB (hC : IsChain C a b c) (p' p ℓ : Fin 4 → ℝ) :
    lineMomentum C p' p ℓ hC.lineB = p + (ℓ - if a < b then p' else p) := by
  have hab := hC.ne_ab
  have hbc := hC.ne_bc
  have hac := hC.ne_ac
  rcases lt_or_gt_of_ne hab with h | h
  · rw [lineMomentum_eq_sum_filter (l := hC.lineA) (r := .inr hC.photonLine)
      (fun g => by rcases hC.eq_line g with h' | h' | h' <;> simp [h'])
      (hC.isLoopLine_iff_of_lt h) hC.lineA_ne_lineB.symm (fun h' => Sum.inr_ne_inl h')
      (fun h' => Sum.inr_ne_inl h'), Finset.sum_filter,
      sum_eq_add_add_of_forall_eq_or_eq_or_eq hab hac hbc hC.eq_or_eq_or_eq, ite_eq_left h]
    rcases hC.ends_inr hC.photonLine with ⟨hP, -⟩ | ⟨hP, -⟩ <;>
      simp [hC.ends_lineA, hC.ends_lineB, hP, hC.externalMomentum_eq, hab, hab.symm, hbc,
        hbc.symm, hac, hac.symm] <;> abel
  · rw [lineMomentum, ite_eq_left ((hC.isLoopLine_iff_of_gt h _).2 rfl),
      ite_eq_right (show ¬ a < b by omega)]
    abel

/-- The photon line carries `±ℓ'`. -/
private theorem lineMomentum_inr (hC : IsChain C a b c) (p' p ℓ : Fin 4 → ℝ) (g : PhotonLine C) :
    lineMomentum C p' p ℓ (.inr g) = ℓ - (if a < b then p' else p) ∨
      lineMomentum C p' p ℓ (.inr g) = -(ℓ - if a < b then p' else p) := by
  have hab := hC.ne_ab
  have hbc := hC.ne_bc
  have hac := hC.ne_ac
  rw [hC.photonLine_eq g hC.photonLine]
  rcases lt_or_gt_of_ne hab with h | h
  · rw [lineMomentum_eq_sum_filter (l := hC.lineA) (r := hC.lineB)
      (fun g => by rcases hC.eq_line g with h' | h' | h' <;> simp [h'])
      (hC.isLoopLine_iff_of_lt h) (fun h' => Sum.inr_ne_inl h')
      (fun h' => Sum.inl_ne_inr h') hC.lineA_ne_lineB.symm, Finset.sum_filter,
      sum_eq_add_add_of_forall_eq_or_eq_or_eq hab hac hbc hC.eq_or_eq_or_eq, ite_eq_left h]
    rcases hC.ends_inr hC.photonLine with ⟨hP, -⟩ | ⟨hP, -⟩
    · left
      simp [hC.ends_lineA, hC.ends_lineB, hP, hC.externalMomentum_eq, hab, hab.symm, hbc,
        hbc.symm, hac, hac.symm]
      abel
    · right
      simp [hC.ends_lineA, hC.ends_lineB, hP, hC.externalMomentum_eq, hab, hab.symm, hbc,
        hbc.symm, hac, hac.symm]
      abel
  · rw [lineMomentum_eq_sum_filter (l := hC.lineB) (r := hC.lineA)
      (fun g => by rcases hC.eq_line g with h' | h' | h' <;> simp [h'])
      (hC.isLoopLine_iff_of_gt h) (fun h' => Sum.inr_ne_inl h')
      (fun h' => Sum.inl_ne_inr h') hC.lineA_ne_lineB, Finset.sum_filter,
      sum_eq_add_add_of_forall_eq_or_eq_or_eq hab hac hbc hC.eq_or_eq_or_eq,
      ite_eq_right (show ¬ a < b by omega)]
    rcases hC.ends_inr hC.photonLine with ⟨hP, -⟩ | ⟨hP, -⟩
    · left
      simp [hC.ends_lineA, hC.ends_lineB, hP, hC.externalMomentum_eq, hab, hab.symm, hbc,
        hbc.symm, hac, hac.symm]
      abel
    · right
      simp [hC.ends_lineA, hC.ends_lineB, hP, hC.externalMomentum_eq, hab, hab.symm, hbc,
        hbc.symm, hac, hac.symm]
      abel

private theorem forall_fv (hC : IsChain C a b c) (x : FermionVertex gauge3) :
    x = fv a ∨ x = fv b ∨ x = fv c := by
  rcases hC.eq_or_eq_or_eq x.1 with h | h | h
  · exact Or.inl ((fv_val_eq x).symm.trans (congrArg fv h))
  · exact Or.inr (Or.inl ((fv_val_eq x).symm.trans (congrArg fv h)))
  · exact Or.inr (Or.inr ((fv_val_eq x).symm.trans (congrArg fv h)))

private theorem forall_ps (hC : IsChain C a b c) (y : PhotonSlot gauge3) :
    y = ps a ∨ y = ps b ∨ y = ps c := by
  rcases hC.eq_or_eq_or_eq y.1 with h | h | h
  · exact Or.inl ((ps_fst_eq y).symm.trans (congrArg ps h))
  · exact Or.inr (Or.inl ((ps_fst_eq y).symm.trans (congrArg ps h)))
  · exact Or.inr (Or.inr ((ps_fst_eq y).symm.trans (congrArg ps h)))

private theorem prod_fermionLine (hC : IsChain C a b c) (F : FermionLine C → ℂ) :
    ∏ f, F f = F ⟨fv a, by simp [hC.psi_a]⟩ * F ⟨fv b, by simp [hC.psi_b]⟩ := by
  refine Fintype.prod_eq_mul _ _
    (fun h => hC.ne_ab (fv_injective (congrArg Subtype.val h))) fun f hf => ?_
  exfalso
  rcases hC.eq_line (.inl f) with h | h | h
  · exact hf.1 (Sum.inl_injective h)
  · exact hf.2 (Sum.inl_injective h)
  · exact Sum.inl_ne_inr h

private theorem prod_photonLine (hC : IsChain C a b c) (F : PhotonLine C → ℂ) :
    ∏ g, F g = F hC.photonLine :=
  Fintype.prod_eq_single _ fun g hg => absurd (hC.photonLine_eq g _) hg

private theorem lineMomentum_inl_a (hC : IsChain C a b c) (p' p ℓ : Fin 4 → ℝ)
    (h : C.1.1 (some (fv a)) ≠ none) :
    lineMomentum C p' p ℓ (.inl ⟨fv a, h⟩) = p' + (ℓ - if a < b then p' else p) :=
  hC.lineMomentum_lineA p' p ℓ

private theorem lineMomentum_inl_b (hC : IsChain C a b c) (p' p ℓ : Fin 4 → ℝ)
    (h : C.1.1 (some (fv b)) ≠ none) :
    lineMomentum C p' p ℓ (.inl ⟨fv b, h⟩) = p + (ℓ - if a < b then p' else p) :=
  hC.lineMomentum_lineB p' p ℓ

private theorem photonPropagator_lineMomentum (hC : IsChain C a b c) (mγ Λ ε : ℝ)
    (p' p ℓ : Fin 4 → ℝ) (lor : PhotonSlot gauge3 → Fin 4) (g : PhotonLine C)
    (h : (C.1.2 (some g.1)).isSome) :
    QED.OneLoop.photonPropagator mγ Λ ε (lineMomentum C p' p ℓ (.inr g)) (lor g.1)
        (lor ((C.1.2 (some g.1)).get h)) =
      QED.OneLoop.photonPropagator mγ Λ ε (ℓ - if a < b then p' else p) (lor (ps c))
        (lor (ps a)) := by
  have hk : QED.OneLoop.photonPropagator mγ Λ ε (lineMomentum C p' p ℓ (.inr g)) =
      QED.OneLoop.photonPropagator mγ Λ ε (ℓ - if a < b then p' else p) := by
    funext μ ν
    rcases hC.lineMomentum_inr p' p ℓ g with hm | hm <;> rw [hm]
    exact photonPropagator_neg mγ Λ ε _ μ ν
  rw [hk]
  rcases hC.photonLine_cases g with ⟨hg, hg', -⟩ | ⟨hg, hg', -⟩ <;>
    rw [Option.get_of_eq_some h hg', hg]
  exact photonPropagator_comm mγ Λ ε _ _ _

/-- **The amplitude of a vertex-correction contraction.** Its entries are those of the integrand
`(ie)³ (1/i)³ γ^ρ S̃(p̸' + ℓ̸') γ^μ S̃(p̸ + ℓ̸') γ^ν Δ̃_{νρ}(ℓ')` of the one-loop vertex at the
shifted loop momentum `ℓ' = ℓ - p'` if `a < b` (the loop line is the line from `b` to `a`) and
`ℓ' = ℓ - p` otherwise. -/
theorem contractionAmplitude_apply (hC : IsChain C a b c) (e δ₁ δ₂ δm δ₃ m mγ Λ ε : ℝ)
    (p' p ℓ : Fin 4 → ℝ) (μ αe βe : Fin 4) :
    contractionAmplitude e δ₁ δ₂ δm δ₃ m mγ Λ ε C p' p ℓ μ αe βe =
      (I * e) ^ 3 * (1 / I) ^ 3 * ∑ ν, ∑ ρ,
        QED.OneLoop.photonPropagator mγ Λ ε (ℓ - if a < b then p' else p) ν ρ *
          (Dirac.gamma ρ *
              QED.OneLoop.electronPropagator m ε (p' + (ℓ - if a < b then p' else p)) *
            Dirac.gamma μ *
              QED.OneLoop.electronPropagator m ε (p + (ℓ - if a < b then p' else p)) *
            Dirac.gamma ν) αe βe := by
  have hab := hC.ne_ab
  have hbc := hC.ne_bc
  have hac := hC.ne_ac
  rw [contractionAmplitude, Matrix.of_apply]
  refine Eq.trans ?_ (sum_chain_eq (fv_injective.ne hab) (fv_injective.ne hac)
    (fv_injective.ne hbc) hC.forall_fv (ps_injective.ne hab) (ps_injective.ne hac)
    (ps_injective.ne hbc) hC.forall_ps Dirac.gamma _ _
    (QED.OneLoop.photonPropagator mγ Λ ε (ℓ - if a < b then p' else p)) (I * e) (1 / I) μ αe βe)
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => ?_
  congr 1
  · refine if_congr ?_ rfl rfl
    simp [hC.psi_none, hC.psi_some_eq_none_iff, hC.photon_none]
  · rw [prod_eq_mul_mul_of_forall_eq_or_eq_or_eq hab hac hbc hC.eq_or_eq_or_eq,
      hC.prod_fermionLine, hC.prod_photonLine]
    simp only [vertexFactor_gauge3, hC.lineMomentum_inl_a, hC.lineMomentum_inl_b,
      Option.get_of_eq_some _ hC.psi_a, Option.get_of_eq_some _ hC.psi_b,
      hC.photonPropagator_lineMomentum]

/-- The integrand of the value of a vertex-correction contraction is the one-loop vertex
integrand at the shifted loop momentum `ℓ - p'` (if `a < b`) or `ℓ - p` (otherwise). -/
theorem integrand_eq (hC : IsChain C a b c) (e δ₁ δ₂ δm δ₃ m mγ Λ ε : ℝ) (p' p ℓ : Fin 4 → ℝ)
    (μ i j : Fin 4) :
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
        contractionAmplitude e δ₁ δ₂ δm δ₃ m mγ Λ ε C p' p ℓ μ i j =
      QED.OneLoop.vertexIntegrand e m mγ Λ ε p' p μ (ℓ - if a < b then p' else p) i j := by
  rw [hC.contractionAmplitude_apply, QED.OneLoop.vertexIntegrand]
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  ring

end IsChain

/-- **The value of a vertex-correction contraction (W₁, evaluation part).** For the contraction
`C` of three gauge vertices with fermion chain `c → b → a`, the external photon at `b` and the
internal photon joining `a` and `c`, the value is the energy-first integral of the one-loop
vertex integrand. No hypothesis on the parameters is needed: the routing of `C` is the routing
of the vertex integrand after a shift of the loop momentum, which leaves the energy-first integral
unchanged. -/
theorem contractionValue_of_isChain (e δ₁ δ₂ δm δ₃ m mγ Λ ε : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    {C : Contraction gauge3} {a b c : Fin 3} (hC : IsChain C a b c) :
    contractionValue e δ₁ δ₂ δm δ₃ m mγ Λ ε C p' p μ =
      Matrix.of fun i j => QED.OneLoop.energyFirstIntegral fun ℓ =>
        QED.OneLoop.vertexIntegrand e m mγ Λ ε p' p μ ℓ i j := by
  rw [contractionValue, ite_eq_right (not_isEmpty_iff.2 ⟨hC.lineA⟩)]
  ext i j
  simp only [Matrix.of_apply, hC.integrand_eq]
  exact QED.OneLoop.energyFirstIntegral_sub_right_eq_self
    (fun ℓ => QED.OneLoop.vertexIntegrand e m mγ Λ ε p' p μ ℓ i j) _

end QED.Wick

end
