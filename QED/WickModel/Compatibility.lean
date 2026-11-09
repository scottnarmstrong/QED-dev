/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.CompatibilityLines
import QED.Wick.Classification
import QED.Wick.ClassificationSmall
import QED.Wick.ClassificationGauge3

/-!
# Packet 5's Wick vertex as a 1PI function of the general model

The proof of the packet 6a theorem goal (Y₁) (decision D-24): packet 5's Wick vertex
`QED.Wick.wickVertex` is the general model's `onePIFunction P 1 1 3` at outgoing momentum `p'`,
incoming momentum `p` and photon momentum `p' - p`.

The two sums are matched term by term along `contractionEquiv κ`, which preserves the fermionic
sign and one-particle irreducibility (`QED.WickModel.CompatibilityLines`). For a 1PI contraction
it also preserves the routing, the momenta at the vertex fields, and the amplitude of the
flavoring `electronFlavoring κ` in which every fermion is an electron. The new ingredient is the
flavor collapse: in every 1PI contraction of order at most `3` each fermion vertex lies on the
open fermion line through the externals (packet 5's classification: the two trees and the six
vertex corrections), so `electronFlavoring κ` is the only flavoring that the contraction
preserves, and its regulator weight is `1`.

## Main statements

* `contractionValue_contractionEquiv`: the values of corresponding 1PI contractions agree when
  only `electronFlavoring κ` is preserved.
* `eq_electronFlavoring_of_preserves`: the flavor collapse at order at most `3`.
* `wickVertex_eq_onePIFunction'`: the theorem goal (Y₁).
-/

@[expose] public section

open Complex

namespace QED.WickModel

variable {N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Wick.Contraction κ}

/-! ### Momenta -/

/-- The transport preserves the external momentum flowing into each vertex. -/
theorem externalMomentum_contractionEquiv (C : Wick.Contraction κ) (p' p : Fin 4 → ℝ)
    (v : Fin N) :
    externalMomentum (contractionEquiv κ C) (fun _ => p') (fun _ => p) (fun _ => p' - p) v =
      Wick.externalMomentum C p' p v := by
  simp only [externalMomentum, Wick.externalMomentum, Fintype.sum_unique, contractionEquiv_fst_inl,
    contractionEquiv_fst_inr, contractionEquiv_snd_inl, optionEquivFinOneSum_eq_inl_iff,
    optionEquivFinOneSum_eq_inr_iff]

/-- The transport preserves the canonical routing of a 1PI contraction. -/
theorem lineMomentum_contractionEquiv (hC : Wick.IsOnePI C) (p' p ℓ : Fin 4 → ℝ)
    (f : Wick.Line C) :
    lineMomentum (contractionEquiv κ C) (fun _ => p') (fun _ => p) (fun _ => p' - p) ℓ
        (lineEquiv C f) = Wick.lineMomentum C p' p ℓ f := by
  rw [lineMomentum, Wick.lineMomentum,
    joined_contractionEquiv (S := {g | g = f ∨ Wick.IsLoopLine g})
      (S' := {g | g = lineEquiv C f ∨ IsLoopLine g})
      fun g => by simp [isLoopLine_lineEquiv hC], ends_lineEquiv]
  by_cases hf : Wick.IsLoopLine f
  · rw [ite_eq_left ((isLoopLine_lineEquiv hC f).mpr hf), ite_eq_left hf]
  · rw [ite_eq_right (mt (isLoopLine_lineEquiv hC f).mp hf), ite_eq_right hf]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [externalMomentum_contractionEquiv]
    congr 1
    exact (Finset.sum_equiv (lineEquiv C) (fun g => by simp [isLoopLine_lineEquiv hC])
      fun g _ => by rw [ends_lineEquiv]).symm

/-- The transport preserves the momentum entering each vertex through its `Ψ` field. -/
theorem psiMomentum_contractionEquiv (hC : Wick.IsOnePI C) (p' p ℓ : Fin 4 → ℝ)
    (t : Wick.FermionVertex κ) :
    psiMomentum (contractionEquiv κ C) (fun _ => p') (fun _ => p) (fun _ => p' - p) ℓ t =
      Wick.psiMomentum C p' p ℓ t := by
  rw [psiMomentum, Wick.psiMomentum]
  split
  · next i h =>
    rw [contractionEquiv_fst_inr, optionEquivFinOneSum_eq_inl_iff] at h
    rw [dite_eq_left h]
  · next s h =>
    rw [contractionEquiv_fst_inr, optionEquivFinOneSum_eq_inr_iff] at h
    have h' : C.1.1 (some t) ≠ none := by
      rw [h]
      exact Option.some_ne_none s
    rw [dite_eq_right h']
    exact lineMomentum_contractionEquiv hC p' p ℓ (.inl ⟨t, h'⟩)

/-- The transport preserves the momentum entering each vertex through each photon field. -/
theorem photonMomentum_contractionEquiv (hC : Wick.IsOnePI C) (p' p ℓ : Fin 4 → ℝ)
    (a : Wick.PhotonSlot κ) :
    photonMomentum (contractionEquiv κ C) (fun _ => p') (fun _ => p) (fun _ => p' - p) ℓ a =
      Wick.photonMomentum C p' p ℓ a := by
  rw [photonMomentum, Wick.photonMomentum, Fintype.sum_unique]
  congr 1
  · exact if_congr (by simp) rfl rfl
  · refine (Fintype.sum_equiv (photonLineEquiv C) _ _ fun g => ?_).symm
    have hm := lineMomentum_contractionEquiv hC p' p ℓ (.inr g)
    rw [lineEquiv_inr] at hm
    rw [hm]
    congr 1
    refine if_congr ?_ rfl rfl
    rw [← some_head_photonLineEquiv]
    exact Option.some_inj

/-! ### Amplitudes and values -/

/-- The flavoring in which every fermion field is an electron, of flavor `0`. -/
def electronFlavoring (κ : Fin N → Wick.VertexKind) : Flavoring κ :=
  ⟨fun _ => 0, fun _ _ => rfl⟩

/-- Under `electronFlavoring` every fermion field has flavor `0`. -/
@[simp]
theorem fermionFlavor_electronFlavoring {nf : ℕ} (x : Fin nf ⊕ Wick.FermionVertex κ) :
    fermionFlavor (electronFlavoring κ) x = 0 := by
  cases x <;> rfl

/-- Every contraction preserves `electronFlavoring`. -/
theorem preserves_electronFlavoring {nf nA : ℕ} (C : Contraction nf nA κ) :
    Preserves C (electronFlavoring κ) := fun a => by
  rw [fermionFlavor_electronFlavoring, fermionFlavor_electronFlavoring]

/-- The regulator weight of `electronFlavoring` is `1`: every closed loop is an electron loop. -/
theorem loopWeight_electronFlavoring (P : Params) {nf nA : ℕ} (C : Contraction nf nA κ) :
    loopWeight P C (electronFlavoring κ) = 1 := by
  rw [loopWeight]
  exact Finset.prod_eq_one fun q _ => by rw [fermionFlavor_electronFlavoring]; rfl

open scoped Classical in
/-- If `electronFlavoring` is the only flavoring that `C` preserves, the regulated amplitude is the
electron amplitude. -/
theorem regulatedAmplitude_eq_of_forall_preserves (P : Params) {nf nA : ℕ}
    {C : Contraction nf nA κ} (hφ : ∀ φ, Preserves C φ → φ = electronFlavoring κ)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (ℓ : Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    regulatedAmplitude P C pOut pIn kIn ℓ αOut βIn μ =
      contractionAmplitude P C (electronFlavoring κ) pOut pIn kIn ℓ αOut βIn μ := by
  have hfilter : (Finset.univ : Finset (Flavoring κ)).filter (Preserves C) =
      {electronFlavoring κ} := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨hφ φ, fun h => h ▸ preserves_electronFlavoring C⟩
  rw [regulatedAmplitude, hfilter, Finset.sum_singleton, loopWeight_electronFlavoring]
  simp

/-- The transport preserves the amplitude of a 1PI contraction, all fermions being electrons. -/
theorem contractionAmplitude_contractionEquiv (P : Params) (hC : Wick.IsOnePI C)
    (p' p ℓ : Fin 4 → ℝ) (μ i j : Fin 4) :
    contractionAmplitude P (contractionEquiv κ C) (electronFlavoring κ) (fun _ => p')
        (fun _ => p) (fun _ => p' - p) ℓ (fun _ => i) (fun _ => j) (fun _ => μ) =
      Wick.contractionAmplitude P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m P.mγ P.Λ P.ε C p' p ℓ μ i j := by
  have hψ : psiMomentum (contractionEquiv κ C) (fun _ => p') (fun _ => p) (fun _ => p' - p) ℓ =
      Wick.psiMomentum C p' p ℓ := funext (psiMomentum_contractionEquiv hC p' p ℓ)
  have hA : photonMomentum (contractionEquiv κ C) (fun _ => p') (fun _ => p) (fun _ => p' - p) ℓ =
      Wick.photonMomentum C p' p ℓ := funext (photonMomentum_contractionEquiv hC p' p ℓ)
  rw [contractionAmplitude, Wick.contractionAmplitude, Matrix.of_apply, hψ, hA]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => ?_
  refine congrArg₂ (· * ·) (if_congr ?_ rfl rfl)
    (congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl ?_) ?_)
  · simp
  · refine (Fintype.prod_equiv (fermionLineEquiv C) _ _ fun f => ?_).symm
    have hm := lineMomentum_contractionEquiv hC p' p ℓ (.inl f)
    rw [lineEquiv_inl] at hm
    rw [hm, tail_fermionLineEquiv, fermionLineEquiv_val]
    rfl
  · refine (Fintype.prod_equiv (photonLineEquiv C) _ _ fun g => ?_).symm
    have hm := lineMomentum_contractionEquiv hC p' p ℓ (.inr g)
    rw [lineEquiv_inr] at hm
    rw [hm, head_photonLineEquiv, photonLineEquiv_val]

/-- **The values of corresponding 1PI contractions agree** when `electronFlavoring` is the only
flavoring that the transported contraction preserves. -/
theorem contractionValue_contractionEquiv (P : Params) (hC : Wick.IsOnePI C)
    (hφ : ∀ φ, Preserves (contractionEquiv κ C) φ → φ = electronFlavoring κ)
    (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    contractionValue P (contractionEquiv κ C) (fun _ => p') (fun _ => p) (fun _ => p' - p)
        (fun _ => i) (fun _ => j) (fun _ => μ) =
      Wick.contractionValue P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m P.mγ P.Λ P.ε C p' p μ i j := by
  rw [contractionValue, Wick.contractionValue]
  by_cases hE : IsEmpty (Wick.Line C)
  · rw [ite_eq_right (mt (exists_isLoopLine_iff hC).mp (not_not.mpr hE)), ite_eq_left hE,
      regulatedAmplitude_eq_of_forall_preserves P hφ, contractionAmplitude_contractionEquiv P hC]
  · rw [ite_eq_left ((exists_isLoopLine_iff hC).mpr hE), ite_eq_right hE, Matrix.of_apply]
    simp only [regulatedAmplitude_eq_of_forall_preserves P hφ,
      contractionAmplitude_contractionEquiv P hC]

/-! ### The flavor collapse -/

/-- Every vertex has order at least `1`. -/
theorem one_le_order (k : Wick.VertexKind) : 1 ≤ k.order := by
  cases k <;> decide

/-- A vertex sequence of total order at most `3` has at most three vertices. -/
theorem le_three_of_sum_order_le (hκ : ∑ t, (κ t).order ≤ 3) : N ≤ 3 :=
  calc N = ∑ _t : Fin N, 1 := by simp
    _ ≤ ∑ t, (κ t).order := Finset.sum_le_sum fun t _ => one_le_order (κ t)
    _ ≤ 3 := hκ

/-- A flavoring preserved by the transported contraction gives the `Ψ̄` contracted with a `Ψ`
field the flavor of that field. -/
theorem flavor_eq_of_preserves {φ : Flavoring κ} (hφ : Preserves (contractionEquiv κ C) φ)
    {x : Option (Wick.FermionVertex κ)} {s : Wick.FermionVertex κ} (h : C.1.1 x = some s) :
    φ.1 s = fermionFlavor φ (optionEquivFinOneSum _ x) := by
  have hx := hφ (optionEquivFinOneSum _ x)
  rw [contractionEquiv_fst, Equiv.permCongr_apply, Equiv.symm_apply_apply, h,
    optionEquivFinOneSum_some] at hx
  exact hx

/-- Three distinct elements of `Fin 3` exhaust it. -/
theorem fin_three_eq_or_eq_or_eq {a b c : Fin 3} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (t : Fin 3) : t = a ∨ t = b ∨ t = c := by
  revert a b c t
  decide

/-- **The flavor collapse.** In a 1PI contraction of order at most `3`, every fermion vertex lies
on the open fermion line from `Ψ̄(y)` to `Ψ(x)` (packet 5's classification), so the only
flavoring that the transported contraction preserves is `electronFlavoring`. -/
theorem eq_electronFlavoring_of_preserves (hκ : ∑ t, (κ t).order ≤ 3) (hC : Wick.IsOnePI C)
    {φ : Flavoring κ} (hφ : Preserves (contractionEquiv κ C) φ) : φ = electronFlavoring κ := by
  apply Subtype.ext
  funext t
  change φ.1 t = 0
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hC.1
  have hs0 : φ.1 s = 0 := flavor_eq_of_preserves hφ hs
  obtain rfl | rfl | rfl | rfl : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 := by
    have := le_three_of_sum_order_le hκ
    omega
  · exact t.1.elim0
  · rwa [(Subtype.ext (Subsingleton.elim t.1 s.1) : t = s)]
  · exact absurd hC (Wick.not_isOnePI_of_fin_two κ hκ C)
  · obtain rfl := Wick.eq_gauge3_of_sum_order_le hκ
    obtain ⟨a, b, c, hab, hbc, hac, h1, h2, h3, -, -, -⟩ := hC.exists_isChain
    have ha : φ.1 (Wick.fv a) = 0 := flavor_eq_of_preserves hφ h1
    have hb : φ.1 (Wick.fv b) = 0 := (flavor_eq_of_preserves hφ h2).trans ha
    have hc : φ.1 (Wick.fv c) = 0 := (flavor_eq_of_preserves hφ h3).trans hb
    obtain ⟨t, ht⟩ := t
    rcases fin_three_eq_or_eq_or_eq hab hbc hac t with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc

/-! ### The theorem goal -/

open scoped Classical in
/-- For a vertex sequence of order at most `3`, the sum over packet 5's 1PI contractions is the
sum over the general model's 1PI contractions with one external fermion pair and one external
photon. -/
theorem sum_isOnePI_contractionEquiv (P : Params) (hκ : ∑ t, (κ t).order ≤ 3)
    (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    ∑ C ∈ (Finset.univ : Finset (Wick.Contraction κ)).filter Wick.IsOnePI,
        ((Wick.fermionSign C : ℤ) : ℂ) *
          Wick.contractionValue P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m P.mγ P.Λ P.ε C p' p μ i j =
      ∑ C ∈ (Finset.univ : Finset (Contraction 1 1 κ)).filter IsOnePI,
        ((fermionSign C : ℤ) : ℂ) * contractionValue P C (fun _ => p') (fun _ => p)
          (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) := by
  refine Finset.sum_equiv (contractionEquiv κ) (fun C => by simp [isOnePI_contractionEquiv_iff])
    fun C hC => ?_
  have hC := (Finset.mem_filter.mp hC).2
  rw [fermionSign_contractionEquiv, contractionValue_contractionEquiv P hC
    (fun _ hφ => eq_electronFlavoring_of_preserves hκ hC hφ)]

/-- (Y₁) **Packet 5 is the special case.** Packet 5's Wick vertex is the 1PI function with one
external fermion pair and one external photon, at order `≤ 3`: outgoing momentum `p'`, incoming
momentum `p`, incoming photon momentum `p' - p`, and the spinor indices `i`, `j` and Lorentz
index `μ`. The contractions correspond along `contractionEquiv`, and in every 1PI contraction
of this order the only flavoring preserved is `electronFlavoring`, of weight `1`. -/
theorem wickVertex_eq_onePIFunction' (P : Params) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    QED.Wick.wickVertex P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m P.mγ P.Λ P.ε p' p μ i j =
      onePIFunction P 1 1 3 (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i)
        (fun _ => j) (fun _ => μ) := by
  rw [Wick.wickVertex, onePIFunction]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun N _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun κ hκ =>
    sum_isOnePI_contractionEquiv P (Finset.mem_filter.mp hκ).2 p' p μ i j

end QED.WickModel

end
