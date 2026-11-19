/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.VPChain.VertexChain
public import QED.Frozen.WickModel.IsOnePI
public import QED.TwoLoop.JointIntegralInvariance
public import QED.Algebra.ChargeConjugation
public import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Inversion of all momenta at fixed `ε`

Helper level, Phase 5 Stage 1a, part of obligation O3-8. The value (F₇) of **every** contraction
whose external fermion fields are attached to vertices satisfies, at every parameter set (so at
every `ε`) and for all external data,

`V_C(-p_out, -p_in, -k)_{αβ…} = (-1)^{n_A} ∏ᵢ s(αᵢ) s(βᵢ) · V_C(p_out, p_in, k)_{αβ…}`

with `s = (-1, -1, 1, 1)` the diagonal of the chirality matrix `Γ` (`contractionValue₂_neg`). No
integrability is needed: the loop momenta change by `ℓ ↦ -ℓ`, which leaves the joint energy-first
integral unchanged for every integrand
(`QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_neg`), and the routing is
linear (`lineMomentum₂_neg`).

The integrand identity is index by index. Conjugation by `Γ` multiplies the entry `(a, b)` by
`s(a) s(b)`. It sends `γ^μ ↦ -γ^μ`, `S̃(k) ↦ S̃(-k)` and the `δ₂, δ_m` vertex at `k` to the one at
`-k`, and leaves the photon propagator and the `δ₃` vertex (even in `k`) alone
(`vertexFactor_neg`). Each vertex thus gives `(-1)^{#photon fields}`. The signs `s` of the
internal spinor indices cancel in pairs along the fermion pairing `σ`, which leaves the external
ones (`prod_sign_pairing`). The number of photon fields has the parity of `n_A`, since the photon
pairing is a fixed-point-free involution of `Fin n_A ⊕ PhotonSlot κ` (`neg_one_pow_card_photonSlot`).

Summed over a family (`onePIFamilyFunction₂_neg`, the `IsOnePI` filter gives attached externals),
the chain vertex satisfies `V_ε(-p', -p)_{ij} = -s(i) s(j) V_ε(p', p)_{ij}`
(`vertexChain_neg`), that is, `V(-p', -p) = -Γ V(p', p) Γ`.
-/

@[expose] public section

open Complex Matrix
open QED.WickModel (Params Contraction Line FermionLine PhotonLine psiMomentum₂ photonMomentum₂
  lineMomentum₂ chordMomentum externalMomentum IsOnePI)

namespace QED.ChainProof.Inv

/-! ### The chirality signs -/

/-- The diagonal `s = (-1, -1, 1, 1)` of the chirality matrix `Γ`. -/
def sg : Fin 4 → ℂ := ![-1, -1, 1, 1]

theorem sg_mul_self (a : Fin 4) : sg a * sg a = 1 := by
  fin_cases a <;> simp [sg]

theorem sg_gamma (μ a b : Fin 4) : sg a * sg b * QED.Dirac.gamma μ a b = -QED.Dirac.gamma μ a b := by
  fin_cases μ <;> fin_cases a <;> fin_cases b <;> simp [sg, QED.Dirac.gamma]

theorem sg_slash (k : Fin 4 → ℝ) (a b : Fin 4) :
    sg a * sg b * QED.Dirac.slash k a b = -QED.Dirac.slash k a b := by
  simp only [QED.Dirac.slash, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [mul_left_comm, sg_gamma, mul_neg]

theorem sg_one (a b : Fin 4) :
    sg a * sg b * (1 : Matrix (Fin 4) (Fin 4) ℂ) a b = (1 : Matrix (Fin 4) (Fin 4) ℂ) a b := by
  by_cases h : a = b
  · subst h
    rw [sg_mul_self, one_mul]
  · simp [h]

theorem dot_neg_neg (k : Fin 4 → ℝ) : Minkowski.dot (-k) (-k) = Minkowski.dot k k := by
  simp only [Minkowski.dot_eq, Pi.neg_apply]
  ring

theorem electronPropagator_neg (m ε : ℝ) (k : Fin 4 → ℝ) (a b : Fin 4) :
    QED.OneLoop.electronPropagator m ε (-k) a b =
      sg a * sg b * QED.OneLoop.electronPropagator m ε k a b := by
  simp only [QED.OneLoop.electronPropagator, dot_neg_neg, QED.Dirac.slash_neg, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul]
  have h1 := sg_one a b
  have h2 := sg_slash k a b
  linear_combination
    (-((((Minkowski.dot k k + m ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹) * (m : ℂ)) * h1 +
      (((Minkowski.dot k k + m ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹ * h2

theorem photonPropagator_neg (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    QED.OneLoop.photonPropagator mγ Λ ε (-k) μ ν = QED.OneLoop.photonPropagator mγ Λ ε k μ ν := by
  simp only [QED.OneLoop.photonPropagator, dot_neg_neg]

/-! ### Vertex factors -/

section VertexFactor

variable {N : ℕ} {κ : Fin N → Wick.VertexKind} (e δ₁ δ₂ δm δ₃ m : ℝ)
  (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
  (kψ : Wick.FermionVertex κ → Fin 4 → ℝ) (kA : Wick.PhotonSlot κ → Fin 4 → ℝ)

/-- The sign of vertex `t` for a sign function `s` on spinor indices: `(-1)^{#photon fields}` times
`s(α_t) s(β_t)` when the vertex has fermion fields. With `s = sg` it is the sign of vertex `t`
under `Γ`-conjugation and inversion. -/
noncomputable def vsgn (s : Fin 4 → ℂ) (t : Fin N) : ℂ :=
  (-1) ^ (κ t).photonSlots * if h : κ t ≠ .photonCt then s (α ⟨t, h⟩) * s (β ⟨t, h⟩) else 1

theorem vf_gauge {t : Fin N} (h : κ t = .gauge) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      I * e * Dirac.gamma (lor ⟨t, ⟨0, by simp [h, Wick.VertexKind.photonSlots]⟩⟩)
        (α ⟨t, by simp [h]⟩) (β ⟨t, by simp [h]⟩) := by
  unfold Wick.vertexFactor
  split <;> rename_i h' <;> first | rfl | exact absurd (h.symm.trans h') (by decide)

theorem vf_gaugeCt {t : Fin N} (h : κ t = .gaugeCt) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      I * ((δ₁ * e : ℝ) : ℂ) * Dirac.gamma (lor ⟨t, ⟨0, by simp [h, Wick.VertexKind.photonSlots]⟩⟩)
        (α ⟨t, by simp [h]⟩) (β ⟨t, by simp [h]⟩) := by
  unfold Wick.vertexFactor
  split <;> rename_i h' <;> first | rfl | exact absurd (h.symm.trans h') (by decide)

theorem vf_fermionCt {t : Fin N} (h : κ t = .fermionCt) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      -I * (((δ₂ : ℂ) • Dirac.slash (kψ ⟨t, by simp [h]⟩)
        + ((δm * m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ))
          (α ⟨t, by simp [h]⟩) (β ⟨t, by simp [h]⟩)) := by
  unfold Wick.vertexFactor
  split <;> rename_i h' <;> first | rfl | exact absurd (h.symm.trans h') (by decide)

theorem vf_photonCt {t : Fin N} (h : κ t = .photonCt) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      -(I / 2) * ((δ₃ *
        (Minkowski.dot (kA ⟨t, ⟨0, by simp [h, Wick.VertexKind.photonSlots]⟩⟩)
            (kA ⟨t, ⟨0, by simp [h, Wick.VertexKind.photonSlots]⟩⟩) *
          Minkowski.metric (lor ⟨t, ⟨0, by simp [h, Wick.VertexKind.photonSlots]⟩⟩)
            (lor ⟨t, ⟨1, by simp [h, Wick.VertexKind.photonSlots]⟩⟩) -
        kA ⟨t, ⟨0, by simp [h, Wick.VertexKind.photonSlots]⟩⟩
            (lor ⟨t, ⟨0, by simp [h, Wick.VertexKind.photonSlots]⟩⟩) *
          kA ⟨t, ⟨0, by simp [h, Wick.VertexKind.photonSlots]⟩⟩
            (lor ⟨t, ⟨1, by simp [h, Wick.VertexKind.photonSlots]⟩⟩)) : ℝ) : ℂ) := by
  unfold Wick.vertexFactor
  split <;> rename_i h' <;> first | rfl | exact absurd (h.symm.trans h') (by decide)

theorem vertexFactor_neg (t : Fin N) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor (-kψ) (-kA) t =
      vsgn α β sg t * Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t := by
  unfold vsgn
  have hcases : κ t = .gauge ∨ κ t = .gaugeCt ∨ κ t = .fermionCt ∨ κ t = .photonCt := by
    cases κ t <;> simp
  rcases hcases with hk | hk | hk | hk
  · have hne : κ t ≠ .photonCt := by rw [hk]; decide
    have hs : (κ t).photonSlots = 1 := by rw [hk]; rfl
    rw [dite_eq_left hne, hs, pow_one, vf_gauge _ _ _ _ _ _ _ _ _ _ _ hk,
      vf_gauge _ _ _ _ _ _ _ _ _ _ _ hk]
    linear_combination (I * e) * sg_gamma _ (α ⟨t, hne⟩) (β ⟨t, hne⟩)
  · have hne : κ t ≠ .photonCt := by rw [hk]; decide
    have hs : (κ t).photonSlots = 1 := by rw [hk]; rfl
    rw [dite_eq_left hne, hs, pow_one, vf_gaugeCt _ _ _ _ _ _ _ _ _ _ _ hk,
      vf_gaugeCt _ _ _ _ _ _ _ _ _ _ _ hk]
    linear_combination (I * ((δ₁ * e : ℝ) : ℂ)) * sg_gamma _ (α ⟨t, hne⟩) (β ⟨t, hne⟩)
  · have hne : κ t ≠ .photonCt := by rw [hk]; decide
    have hs : (κ t).photonSlots = 0 := by rw [hk]; rfl
    rw [dite_eq_left hne, hs, pow_zero, one_mul, vf_fermionCt _ _ _ _ _ _ _ _ _ _ _ hk,
      vf_fermionCt _ _ _ _ _ _ _ _ _ _ _ hk]
    simp only [Pi.neg_apply, QED.Dirac.slash_neg, Matrix.add_apply, Matrix.smul_apply,
      Matrix.neg_apply, smul_eq_mul]
    linear_combination (I * (δ₂ : ℂ)) * sg_slash (kψ ⟨t, hne⟩) (α ⟨t, hne⟩) (β ⟨t, hne⟩) +
      (I * ((δm * m : ℝ) : ℂ)) * sg_one (α ⟨t, hne⟩) (β ⟨t, hne⟩)
  · have hs : (κ t).photonSlots = 2 := by rw [hk]; rfl
    rw [dite_eq_right (by rw [hk]; exact fun h => h rfl), hs, vf_photonCt _ _ _ _ _ _ _ _ _ _ _ hk,
      vf_photonCt _ _ _ _ _ _ _ _ _ _ _ hk]
    simp only [Pi.neg_apply, dot_neg_neg, neg_mul_neg]
    ring

theorem prod_vsgn (s : Fin 4 → ℂ) :
    ∏ t, vsgn α β s t = (-1) ^ Fintype.card (Wick.PhotonSlot κ) *
      ∏ t : Wick.FermionVertex κ, s (α t) * s (β t) := by
  unfold vsgn
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  congr 1
  rw [← Finset.prod_filter_of_ne (p := fun t => κ t ≠ .photonCt) (fun t _ h => by
    by_contra hc
    exact h (dite_eq_right (fun h' => h' hc)))]
  rw [Finset.prod_subtype (Finset.univ.filter fun t => κ t ≠ .photonCt) (p := fun t =>
    κ t ≠ .photonCt) (fun t => by simp)]
  exact Finset.prod_congr rfl fun x _ => dite_eq_left x.2

end VertexFactor

/-! ### Parity of the photon fields -/

/-- The photon fields have the parity of the external photons: the photon pairing is a
fixed-point-free involution of `Fin n_A ⊕ PhotonSlot κ`. -/
theorem neg_one_pow_card_photonSlot {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) :
    ((-1 : ℂ)) ^ Fintype.card (Wick.PhotonSlot κ) = (-1) ^ nA := by
  classical
  let f : Function.End (Fin nA ⊕ Wick.PhotonSlot κ) := fun x => C.1.2 x
  have hf : f ^ 2 ^ 1 = 1 := by
    funext x
    change C.1.2 (C.1.2 x) = x
    exact (C.2 x).1
  have : IsEmpty (Function.fixedPoints f) := ⟨fun x => (C.2 x.1).2 (by exact x.2)⟩
  have := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hf
  rw [Fintype.card_sum, Fintype.card_fin] at this
  simp only [Fintype.card_eq_zero] at this
  have hev : Even (nA + Fintype.card (Wick.PhotonSlot κ)) := Nat.even_iff.mpr this
  obtain ⟨r, hr⟩ := hev
  have : (-1 : ℂ) ^ nA * (-1) ^ Fintype.card (Wick.PhotonSlot κ) = 1 := by
    rw [← pow_add, hr, ← two_mul, pow_mul]
    norm_num
  calc ((-1 : ℂ)) ^ Fintype.card (Wick.PhotonSlot κ)
      = (-1) ^ nA * (-1) ^ Fintype.card (Wick.PhotonSlot κ) * (-1) ^ nA := by
        rw [mul_comm ((-1 : ℂ) ^ nA), mul_assoc, ← pow_add, ← two_mul, pow_mul]
        norm_num
    _ = (-1) ^ nA := by rw [this, one_mul]

/-! ### The signs along the fermion pairing -/

section Pairing

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- **The internal signs cancel in pairs.** Under the external-index constraints of (F₅) and with
the external fermion fields attached, the signs of all vertex spinor indices times those of the
two ends of each internal fermion line leave the signs of the external indices. -/
theorem prod_sign_pairing (C : Contraction nf nA κ) (hatt : ∀ i j : Fin nf, C.1.1 (.inl i) ≠ .inl j)
    (s : Fin 4 → ℂ) (hs : ∀ a, s a * s a = 1) (α β : Wick.FermionVertex κ → Fin 4)
    (αOut βIn : Fin nf → Fin 4)
    (hα : ∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i)
    (hβ : ∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) :
    (∏ t : Wick.FermionVertex κ, s (α t) * s (β t)) *
        (∏ f : FermionLine C, s (β f.1) * s (α f.tail)) =
      ∏ i, s (αOut i) * s (βIn i) := by
  set ψ : Fin nf ⊕ Wick.FermionVertex κ → Fin 4 := Sum.elim αOut β
  set ψb : Fin nf ⊕ Wick.FermionVertex κ → Fin 4 := Sum.elim βIn α
  have hall : ∏ a, s (ψ a) * s (ψb (C.1.1 a)) =
      (∏ i, s (αOut i) * s (βIn i)) * ∏ t : Wick.FermionVertex κ, s (α t) * s (β t) := by
    rw [Finset.prod_mul_distrib, Equiv.prod_comp C.1.1 (fun b => s (ψb b)), Fintype.prod_sum_type,
      Fintype.prod_sum_type]
    simp only [ψ, ψb, Sum.elim_inl, Sum.elim_inr, Finset.prod_mul_distrib]
    ring
  have hlines : ∏ a, s (ψ a) * s (ψb (C.1.1 a)) = ∏ f : FermionLine C, s (β f.1) * s (α f.tail) := by
    rw [Fintype.prod_sum_type]
    have h1 : ∏ i : Fin nf, s (ψ (.inl i)) * s (ψb (C.1.1 (.inl i))) = 1 := by
      refine Finset.prod_eq_one fun i _ => ?_
      rcases hci : C.1.1 (.inl i) with j | t
      · exact absurd hci (hatt i j)
      · simp only [ψ, ψb, Sum.elim_inl, Sum.elim_inr, hα i t hci, hs]
    rw [h1, one_mul]
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun t : Wick.FermionVertex κ =>
      (C.1.1 (.inr t)).isRight)]
    have h2 : ∏ t : {t : Wick.FermionVertex κ // ¬ (C.1.1 (.inr t)).isRight},
        s (ψ (.inr t.1)) * s (ψb (C.1.1 (.inr t.1))) = 1 := by
      refine Finset.prod_eq_one fun t _ => ?_
      rcases hct : C.1.1 (.inr t.1) with i | u
      · simp only [ψ, ψb, Sum.elim_inl, Sum.elim_inr, hβ t.1 i hct, hs]
      · exact absurd (by rw [hct]; rfl) t.2
    rw [h2, mul_one]
    refine Finset.prod_congr rfl fun f _ => ?_
    have e : C.1.1 (.inr f.1) = .inr (QED.WickModel.FermionLine.tail f) := by
      simp only [FermionLine.tail]
      exact (Sum.inr_getRight _ _).symm
    simp only [ψ, ψb, Sum.elim_inr, e]
  rw [← hlines, hall]
  have hA : (∏ t : Wick.FermionVertex κ, s (α t) * s (β t)) *
      (∏ t : Wick.FermionVertex κ, s (α t) * s (β t)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun t _ => ?_
    rw [show s (α t) * s (β t) * (s (α t) * s (β t)) = (s (α t) * s (α t)) * (s (β t) * s (β t)) by
      ring, hs, hs, one_mul]
  linear_combination (∏ i, s (αOut i) * s (βIn i)) * hA

end Pairing

/-! ### Momenta -/

section Momenta

variable {nf nA N L : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ)

theorem psiMomentum₂_neg (pIn : Fin nf → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ) :
    psiMomentum₂ C (-pIn) (-k) = -psiMomentum₂ C pIn k := by
  funext t
  rw [Pi.neg_apply]
  unfold psiMomentum₂
  split <;> rfl

theorem photonMomentum₂_neg (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ) :
    photonMomentum₂ C (-kIn) (-k) = -photonMomentum₂ C kIn k := by
  funext a
  simp only [photonMomentum₂, Pi.neg_apply, neg_add, ← Finset.sum_neg_distrib]
  congr 1 <;> refine Finset.sum_congr rfl fun _ _ => ?_ <;> split_ifs <;> simp

theorem chordMomentum_neg (ℓ : Fin L → Fin 4 → ℝ) (f : Line C) :
    chordMomentum (-ℓ) f = -chordMomentum ℓ f := by
  unfold chordMomentum
  split_ifs <;> simp

theorem externalMomentum_neg (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (v : Fin N) :
    externalMomentum C (-pOut) (-pIn) (-kIn) v = -externalMomentum C pOut pIn kIn v := by
  have e : ∀ (P : Prop) [Decidable P] (x : Fin 4 → ℝ), (if P then -x else 0) = -(if P then x else 0) :=
    fun P _ x => by split_ifs <;> simp
  simp only [externalMomentum, Pi.neg_apply, e, Finset.sum_neg_distrib]
  abel

theorem lineMomentum₂_neg (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (ℓ : Fin L → Fin 4 → ℝ) :
    lineMomentum₂ C (-pOut) (-pIn) (-kIn) (-ℓ) = -lineMomentum₂ C pOut pIn kIn ℓ := by
  funext f
  unfold lineMomentum₂
  simp only [Pi.neg_apply]
  split_ifs
  · exact chordMomentum_neg C ℓ f
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [externalMomentum_neg, neg_add, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [chordMomentum_neg]
    split_ifs <;> simp

end Momenta

/-! ### Amplitude, value and family function -/

section Value

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : QED.Lepton.Flavors F)
  {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- The joint energy-first integral commutes with constant factors, for every integrand. -/
theorem jointEnergyFirstIntegral_const_mul (L : ℕ) (c : ℂ) (G : (Fin L → Fin 4 → ℝ) → ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegral L (fun ℓ => c * G ℓ) =
      c * QED.TwoLoop.jointEnergyFirstIntegral L G := by
  unfold QED.TwoLoop.jointEnergyFirstIntegral
  simp only [MeasureTheory.integral_const_mul]

omit [Fintype F] [DecidableEq F] in
open scoped Classical in
/-- **Inversion of the amplitude** (F₅). -/
theorem contractionAmplitude₂_neg (C : Contraction nf nA κ)
    (hatt : ∀ i j : Fin nf, C.1.1 (.inl i) ≠ .inl j) (φ : QED.Lepton.Flavoring Φ κ)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    QED.Lepton.contractionAmplitude₂ P Φ C φ (-pIn) (-kIn) (-k) αOut βIn μ =
      ((-1) ^ nA * ∏ i, sg (αOut i) * sg (βIn i)) *
        QED.Lepton.contractionAmplitude₂ P Φ C φ pIn kIn k αOut βIn μ := by
  unfold QED.Lepton.contractionAmplitude₂
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => ?_
  split_ifs with hc
  · have hp := prod_sign_pairing C hatt sg sg_mul_self α β αOut βIn hc.1 hc.2.1
    have hV : ∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
        (-psiMomentum₂ C pIn k) (-photonMomentum₂ C kIn k) t =
        (∏ t, vsgn α β sg t) * ∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
          (psiMomentum₂ C pIn k) (photonMomentum₂ C kIn k) t := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun t _ => vertexFactor_neg _ _ _ _ _ _ _ _ _ _ _ t
    have hF : ∏ f : FermionLine C, (1 / I) *
        QED.OneLoop.electronPropagator (Φ.mass (φ.1 f.1)) P.ε ((-k) (.inl f)) (β f.1) (α f.tail) =
        (∏ f : FermionLine C, sg (β f.1) * sg (α f.tail)) * ∏ f : FermionLine C, (1 / I) *
        QED.OneLoop.electronPropagator (Φ.mass (φ.1 f.1)) P.ε (k (.inl f)) (β f.1) (α f.tail) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun f _ => ?_
      rw [Pi.neg_apply, electronPropagator_neg]
      ring
    have hG : ∏ g : PhotonLine C, (1 / I) *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε ((-k) (.inr g)) (lor g.1) (lor g.head) =
        ∏ g : PhotonLine C, (1 / I) *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr g)) (lor g.1) (lor g.head) :=
      Finset.prod_congr rfl fun g _ => by rw [Pi.neg_apply, photonPropagator_neg]
    rw [psiMomentum₂_neg, photonMomentum₂_neg, hV, hF, hG, prod_vsgn,
      neg_one_pow_card_photonSlot C, ← hp]
    ring
  · simp

open scoped Classical in
theorem regulatedAmplitude₂_neg (C : Contraction nf nA κ)
    (hatt : ∀ i j : Fin nf, C.1.1 (.inl i) ≠ .inl j)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    QED.Lepton.regulatedAmplitude₂ P Φ C (-pIn) (-kIn) (-k) αOut βIn μ =
      ((-1) ^ nA * ∏ i, sg (αOut i) * sg (βIn i)) *
        QED.Lepton.regulatedAmplitude₂ P Φ C pIn kIn k αOut βIn μ := by
  unfold QED.Lepton.regulatedAmplitude₂
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [contractionAmplitude₂_neg P Φ C hatt]
  ring

/-- **Inversion of all momenta in the value** (F₇), at every parameter set and for all external
data, for a contraction whose external fermion fields are attached to vertices. -/
theorem contractionValue₂_neg (C : Contraction nf nA κ)
    (hatt : ∀ i j : Fin nf, C.1.1 (.inl i) ≠ .inl j)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    QED.Lepton.contractionValue₂ P Φ C (-pOut) (-pIn) (-kIn) αOut βIn μ =
      ((-1) ^ nA * ∏ i, sg (αOut i) * sg (βIn i)) *
        QED.Lepton.contractionValue₂ P Φ C pOut pIn kIn αOut βIn μ := by
  unfold QED.Lepton.contractionValue₂
  rw [← QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_neg]
  have e : ∀ ℓ : Fin (QED.WickModel.loopCount C) → Fin 4 → ℝ,
      lineMomentum₂ C (-pOut) (-pIn) (-kIn) (-ℓ) = -lineMomentum₂ C pOut pIn kIn ℓ :=
    fun ℓ => lineMomentum₂_neg C pOut pIn kIn ℓ
  simp only [e, regulatedAmplitude₂_neg P Φ C hatt]
  rw [← jointEnergyFirstIntegral_const_mul]
  congr 1
  funext ℓ
  ring

open scoped Classical in
/-- **Inversion of all momenta in the 1PI function of a family** (C₂). -/
theorem onePIFamilyFunction₂_neg (nf nA : ℕ)
    (Fam : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction nf nA κ → Prop) (K : ℕ)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    QED.Lepton.onePIFamilyFunction₂ P Φ nf nA Fam K (-pOut) (-pIn) (-kIn) αOut βIn μ =
      ((-1) ^ nA * ∏ i, sg (αOut i) * sg (βIn i)) *
        QED.Lepton.onePIFamilyFunction₂ P Φ nf nA Fam K pOut pIn kIn αOut βIn μ := by
  unfold QED.Lepton.onePIFamilyFunction₂
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun N _ => Finset.sum_congr rfl fun κ _ =>
    Finset.sum_congr rfl fun C hC => ?_
  have hatt : ∀ i j : Fin nf, C.1.1 (.inl i) ≠ .inl j := (Finset.mem_filter.mp hC).2.1.1.1
  rw [contractionValue₂_neg P Φ C hatt]
  ring

/-- **Inversion of all momenta in the chain vertex** (C₃) at fixed `ε`:
`V_ε(-p', -p)_{ij} = -s(i) s(j) V_ε(p', p)_{ij}`, i.e. `V(-p', -p) = -Γ V(p', p) Γ`. -/
theorem vertexChain_neg (n : ℕ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (i j : Fin 4) :
    QED.VPChain.vertexChain n P Φ (-p') (-p) μ i j =
      -(sg i * sg j) * QED.VPChain.vertexChain n P Φ p' p μ i j := by
  simp only [QED.VPChain.vertexChain, Matrix.of_apply]
  have e1 : (fun _ : Fin 1 => -p') = -fun _ : Fin 1 => p' := rfl
  have e2 : (fun _ : Fin 1 => -p) = -fun _ : Fin 1 => p := rfl
  have e3 : (fun _ : Fin 1 => -p' - -p) = -fun _ : Fin 1 => p' - p := by
    funext _
    simp only [Pi.neg_apply]
    abel
  rw [e1, e2, e3, onePIFamilyFunction₂_neg]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton, pow_one]
  ring

end Value

end QED.ChainProof.Inv

end
