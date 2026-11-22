/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetANestLGen
public import QED.ChainProof.SetANestVNest
public import QED.ChainProof.SetANestLRoute
public import QED.ChainProof.SetALinkIntVA
public import QED.GradedProof.VP2VLim
public import QED.TwoLoop.EnumerationDecide

/-!
# Set (a), obligation (N): the nested form of the three-loop class `VA`

Helper level for obligation (N) of `QED.ChainProof.SetAPauli.SetALimitLink`: the nested form
`QED.ChainProof.SetANest.LoopNested` of `QED.ChainProof.SetALink.repVA` (the two-loop
vacuum-polarization insertion with a self-energy on the loop line `w → u`), by
`QED.ChainProof.SetANestV.loopNested_of_nestGL1`. Also the pieces shared with `VB`, `VC`
(`QED/ChainProof/SetANestVB.lean`, `QED/ChainProof/SetANestVC.lean`).

* Shared: `vertexFactor_kV`, the Lorentz sum `sum_lor_kV` over the photon fields of `kV`, the
  spinor sum `sum_spinor_chain3_loop4` of an open chain through three vertices and a loop through
  four, `chordMomentum_eq_of_card`, the sum reorderings `sum_flavor_out_four`, `sum_pair_out_three`.
* Routing: `v3aMom`, with inner momenta `ℓ 0`, `ℓ 1` and outer momentum `ℓ 2 = k` (lines
  `0 → 1`: `p + k`, `1 → 2`: `p' + k`, `4 → 3`: `ℓ 0 - k`, `5 → 4`: `ℓ 0`, `6 → 5`: `ℓ 1`,
  `3 → 6`: `ℓ 0`; photons `0 → 4`: `-k`, `2 → 3`: `k`, `5 → 6`: `ℓ 1 - ℓ 0`), conserved, with the
  chords (lines `0 → 1`, `4 → 3`, `6 → 5`) at the frozen loop momenta `v3aMat ℓ + (p, 0, 0)`.
  The loop `4 → 3 → 6 → 5 → 4` is the loop `0 → 1 → 2 → 3 → 0` of the two-photon class `VA` of
  `Π⁽⁴⁾` (`QED.GradedProof.VP2.repVA`) at the photon momentum `-k`.
* `v3a_amplitude` (Wick), **`v3a_routedIntegrand`**: the integrand of the value in the routing
  `v3aMom` is `nestG nestOuter v3aY`, `v3aY_{ab}(k, q) = (1/i) vSumF(VA)(-k, q)_{ab}`; the
  constant `(2π)⁻¹² (ie)⁷ (1/i)⁹` is the product of the constant `(2π)⁻⁴ (ie)³ (1/i)³` of
  `nestOuter`, the constant `(2π)⁻⁸ (ie)⁴ (1/i)⁵` inside `vSumF` and `1/i`.
* `v3a_hval`, `v3a_hF` (from `QED.ChainProof.SetALinkV.classIntA_repVA`), `v3a_efi`:
  `∫∫ v3aY(k, ·) = (1/i) val0(VA)(-k)`.
* **`loopNested_v3a`**: under `IntHypA` and masses bounded below by `m₀ > 0`, `VA` is in nested
  form with `X(k)^{ab} = (1/i) val0(VA)(-k)^{ab}`.
* `vertexType_group_sum`: the vertex-type group identity of `SetANestClasses` for these tensors.
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.ChainProof.SetANest

open QED.WickModel QED.TwoLoop.Routing QED.ChainProof.SetALink QED.ChainProof.Enum
open scoped QED.TwoLoop.Enumeration

/-! ### Shared: chords, vertex factors, Lorentz and spinor sums -/

/-- A chord whose predecessors among the chords number `n` carries `ℓ n`. -/
theorem chordMomentum_eq_of_card {nf nA N L : ℕ} {κ : Fin N → Wick.VertexKind}
    {C : Contraction nf nA κ} (ℓ : Fin L → Fin 4 → ℝ) (f : Line C) (n : Fin L)
    (h : (Finset.univ.filter fun g : Line C => IsChord g ∧ g.label < f.label).card = n) :
    chordMomentum ℓ f = ℓ n := by
  unfold chordMomentum
  split_ifs with hc
  · congr 1
    exact Fin.ext (by convert h)
  · exact absurd (by convert n.2 using 2; convert h) hc


theorem vertexFactor_kV (e δ₁ δ₂ δm δ₃ m : ℝ) (α β : Wick.FermionVertex kV → Fin 4)
    (lor : Wick.PhotonSlot kV → Fin 4) (kψ : Wick.FermionVertex kV → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot kV → Fin 4 → ℝ) (t : Fin 7) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      I * e * Dirac.gamma (lor (pg kV t (by simp [kV, Wick.VertexKind.photonSlots])))
        (α (fv kV t (by simp [kV]))) (β (fv kV t (by simp [kV]))) :=
  QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge e δ₁ δ₂ δm δ₃ m α β lor kψ kA rfl

/-- **The Lorentz sum over the photon fields of `kV`**, in the order `1, 4, 3, 0, 2, 6, 5`. -/
theorem sum_lor_kV {R M : Type*} [Fintype R] [AddCommMonoid M]
    (g : (Wick.PhotonSlot kV → R) → M) :
    ∑ lor, g lor = ∑ a1, ∑ a4, ∑ a3, ∑ a0, ∑ a2, ∑ a6, ∑ a5,
      g (fun s => ![a0, a1, a2, a3, a4, a5, a6] s.1) := by
  let e : (R × R × R × R × R × R × R) ≃ (Wick.PhotonSlot kV → R) :=
    { toFun := fun q s => ![q.2.2.2.1, q.1, q.2.2.2.2.1, q.2.2.1, q.2.1, q.2.2.2.2.2.2,
        q.2.2.2.2.2.1] s.1
      invFun := fun lor => (lor (pg kV 1), lor (pg kV 4), lor (pg kV 3), lor (pg kV 0),
        lor (pg kV 2), lor (pg kV 6), lor (pg kV 5))
      left_inv := fun _ => rfl
      right_inv := fun lor => by
        funext s
        obtain ⟨j, b⟩ := s
        fin_cases j <;>
        · have hb : b = ⟨0, by decide⟩ := Fin.ext (Nat.lt_one_iff.mp b.2)
          subst hb
          rfl }
  rw [← e.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

section Spin

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **The spinor sum of an open chain through three vertices and a closed loop through four**. -/
theorem sum_spinor_chain3_loop4 (e : X ≃ Fin 3 ⊕ Fin 4) {x₁ x₂ x₃ y₁ y₂ y₃ y₄ : X}
    (h₁ : e x₁ = .inl 0) (h₂ : e x₂ = .inl 1) (h₃ : e x₃ = .inl 2) (h₄ : e y₁ = .inr 0)
    (h₅ : e y₂ = .inr 1) (h₆ : e y₃ = .inr 2) (h₇ : e y₄ = .inr 3) (c : ℂ)
    (A₁ A₂ A₃ S₁ S₂ B₁ B₂ B₃ B₄ T₁ T₂ T₃ T₄ : Matrix (Fin 4) (Fin 4) ℂ) (a b : Fin 4) :
    ∑ α : X → Fin 4, ∑ β : X → Fin 4,
      (if α x₁ = a ∧ β x₃ = b then (1 : ℂ) else 0) *
        (c * (A₁ (α x₁) (β x₁) * S₁ (β x₁) (α x₂) * A₂ (α x₂) (β x₂) * S₂ (β x₂) (α x₃) *
          A₃ (α x₃) (β x₃)) *
          (B₁ (α y₁) (β y₁) * T₁ (β y₁) (α y₂) * B₂ (α y₂) (β y₂) * T₂ (β y₂) (α y₃) *
            B₃ (α y₃) (β y₃) * T₃ (β y₃) (α y₄) * B₄ (α y₄) (β y₄) * T₄ (β y₄) (α y₁))) =
      c * Matrix.trace (B₁ * T₁ * B₂ * T₂ * B₃ * T₃ * B₄ * T₄) * (A₁ * S₁ * A₂ * S₂ * A₃) a b := by
  rw [sum_pi_sum_equiv e]
  simp only [sum_pi_sum_equiv e (g := fun β => _ * _), h₁, h₂, h₃, h₄, h₅, h₆, h₇, Sum.elim_inl,
    Sum.elim_inr]
  have hL := QED.GradedProof.VP2.sum_spinor_loop4 (X := Fin 4) (x₁ := 0) (x₂ := 1) (x₃ := 2)
    (x₄ := 3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) B₁ B₂ B₃ B₄ T₁ T₂ T₃ T₄
  have hC := QED.TwoLoop.Insertion.sum_spinor_chain3 (X := Fin 3) (x₁ := 0) (x₂ := 1)
    (x₃ := 2) (by decide) (by decide) (by decide) (by decide)
    (c * Matrix.trace (B₁ * T₁ * B₂ * T₂ * B₃ * T₃ * B₄ * T₄)) A₁ A₂ A₃ S₁ S₂ a b
  rw [← hC]
  refine Finset.sum_congr rfl fun α₁ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β₁ _ => ?_
  rw [← hL]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun α₂ _ => Finset.sum_congr rfl fun β₂ _ => ?_
  ring

end Spin

theorem sum_flavor_out_four {F : Type} [Fintype F] (g : F → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
    ∑ f, ∑ a, ∑ b, ∑ c, ∑ d, g f a b c d = ∑ a, ∑ b, ∑ c, ∑ d, ∑ f, g f a b c d := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

theorem sum_pair_out_three {F : Type} [Fintype F] (g : F → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
    ∑ f, ∑ x, ∑ y, ∑ ν, ∑ ρ, g f x y ν ρ = ∑ ν, ∑ ρ, ∑ f, ∑ x, ∑ y, g f x y ν ρ := by
  calc ∑ f, ∑ x, ∑ y, ∑ ν, ∑ ρ, g f x y ν ρ
      = ∑ f, ∑ x, ∑ y, ∑ q : Fin 4 × Fin 4, g f x y q.1 q.2 := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ f, ∑ x, ∑ q : Fin 4 × Fin 4, ∑ y, g f x y q.1 q.2 :=
        Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ f, ∑ q : Fin 4 × Fin 4, ∑ x, ∑ y, g f x y q.1 q.2 :=
        Finset.sum_congr rfl fun f _ => Finset.sum_comm
    _ = ∑ q : Fin 4 × Fin 4, ∑ f, ∑ x, ∑ y, g f x y q.1 q.2 := Finset.sum_comm
    _ = ∑ ν, ∑ ρ, ∑ f, ∑ x, ∑ y, g f x y ν ρ := by simp only [Fintype.sum_prod_type]

/-! ### Lines and routing of `VA` -/

/-- The fermion lines of `repVA`, by head `1, …, 6`. -/
def v3aL : Fin 6 → FermionLine repVA :=
  ![⟨fv kV 1, by decide +kernel⟩, ⟨fv kV 2, by decide +kernel⟩, ⟨fv kV 3, by decide +kernel⟩,
    ⟨fv kV 4, by decide +kernel⟩, ⟨fv kV 5, by decide +kernel⟩, ⟨fv kV 6, by decide +kernel⟩]

/-- The photon lines `0 — 4`, `2 — 3`, `5 — 6` of `repVA`. -/
def v3aP : Fin 3 → PhotonLine repVA :=
  ![⟨pg kV 0, by decide +kernel⟩, ⟨pg kV 2, by decide +kernel⟩, ⟨pg kV 5, by decide +kernel⟩]

theorem v3aL_bijective : Function.Bijective v3aL := by decide +kernel

theorem v3aP_bijective : Function.Bijective v3aP := by decide +kernel

theorem v3a_ends : (Line.ends (.inl (v3aL 0) : Line repVA)) = (0, 1) ∧
    (Line.ends (.inl (v3aL 1) : Line repVA)) = (1, 2) ∧
    (Line.ends (.inl (v3aL 2) : Line repVA)) = (4, 3) ∧
    (Line.ends (.inl (v3aL 3) : Line repVA)) = (5, 4) ∧
    (Line.ends (.inl (v3aL 4) : Line repVA)) = (6, 5) ∧
    (Line.ends (.inl (v3aL 5) : Line repVA)) = (3, 6) ∧
    (Line.ends (.inr (v3aP 0) : Line repVA)) = (0, 4) ∧
    (Line.ends (.inr (v3aP 1) : Line repVA)) = (2, 3) ∧
    (Line.ends (.inr (v3aP 2) : Line repVA)) = (5, 6) := by decide +kernel

theorem v3a_isChord_iff : ∀ f : Line repVA,
    IsChord f ↔ f = .inl (v3aL 0) ∨ f = .inl (v3aL 2) ∨ f = .inl (v3aL 4) := by
  decide +kernel

theorem v3a_sum_line {M : Type*} [AddCommMonoid M] (g : Line repVA → M) :
    ∑ f, g f = g (.inl (v3aL 0)) + g (.inl (v3aL 1)) + g (.inl (v3aL 2)) + g (.inl (v3aL 3)) +
      g (.inl (v3aL 4)) + g (.inl (v3aL 5)) +
      (g (.inr (v3aP 0)) + g (.inr (v3aP 1)) + g (.inr (v3aP 2))) := by
  rw [Fintype.sum_sum_type, ← (Equiv.ofBijective _ v3aL_bijective).sum_comp,
    ← (Equiv.ofBijective _ v3aP_bijective).sum_comp, Fin.sum_univ_six, Fin.sum_univ_three]
  rfl

theorem v3a_ext (v : Fin 7) :
    ((∃ t : Wick.FermionVertex kV, t.1 = v ∧ repVA.1.1 (.inr t) = .inl 0) ↔ v = 0) ∧
    ((∃ a : Wick.PhotonSlot kV, a.1 = v ∧ repVA.1.2 (.inl 0) = .inr a) ↔ v = 1) ∧
    ((∃ t : Wick.FermionVertex kV, t.1 = v ∧ repVA.1.1 (.inl 0) = .inr t) ↔ v = 2) := by
  revert v
  decide +kernel

/-- **The nested routing of `VA`**: inner momenta `ℓ 0`, `ℓ 1`, outer momentum `ℓ 2`. -/
def v3aMom (p kext : Fin 4 → ℝ) (ℓ : Fin 3 → Fin 4 → ℝ) (f : Line repVA) : Fin 4 → ℝ :=
  match f.label with
  | 1 => p + ℓ 2
  | 2 => p + kext + ℓ 2
  | 3 => ℓ 0 - ℓ 2
  | 4 => ℓ 0
  | 5 => ℓ 1
  | 6 => ℓ 0
  | 7 => -ℓ 2
  | 11 => ℓ 2
  | _ => ℓ 1 - ℓ 0

theorem v3aMom_apply (p kext : Fin 4 → ℝ) (ℓ : Fin 3 → Fin 4 → ℝ) :
    v3aMom p kext ℓ (.inl (v3aL 0)) = p + ℓ 2 ∧ v3aMom p kext ℓ (.inl (v3aL 1)) = p + kext + ℓ 2 ∧
      v3aMom p kext ℓ (.inl (v3aL 2)) = ℓ 0 - ℓ 2 ∧ v3aMom p kext ℓ (.inl (v3aL 3)) = ℓ 0 ∧
      v3aMom p kext ℓ (.inl (v3aL 4)) = ℓ 1 ∧ v3aMom p kext ℓ (.inl (v3aL 5)) = ℓ 0 ∧
      v3aMom p kext ℓ (.inr (v3aP 0)) = -ℓ 2 ∧ v3aMom p kext ℓ (.inr (v3aP 1)) = ℓ 2 ∧
      v3aMom p kext ℓ (.inr (v3aP 2)) = ℓ 1 - ℓ 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem isConserved_v3aMom {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 3 → Fin 4 → ℝ) : IsConserved repVA pOut pIn kIn (v3aMom (pIn 0) (kIn 0) ℓ) := by
  obtain ⟨e0, e1, e2, e3, e4, e5, g0, g1, g2⟩ := v3a_ends
  obtain ⟨n0, n1, n2, n3, n4, n5, m0, m1, m2⟩ := v3aMom_apply (pIn 0) (kIn 0) ℓ
  intro v
  obtain ⟨x0, x1, x2⟩ := v3a_ext v
  rw [inflow, v3a_sum_line, QED.TwoLoop.Insertion.externalMomentum_one_one, hmom]
  simp only [e0, e1, e2, e3, e4, e5, g0, g1, g2, n0, n1, n2, n3, n4, n5, m0, m1, m2, x0, x1, x2]
  fin_cases v
  all_goals simp
  all_goals abel

theorem v3a_chordMomentum (ℓ : Fin 3 → Fin 4 → ℝ) :
    chordMomentum ℓ (.inl (v3aL 0) : Line repVA) = ℓ 0 ∧
      chordMomentum ℓ (.inl (v3aL 2) : Line repVA) = ℓ 1 ∧
      chordMomentum ℓ (.inl (v3aL 4) : Line repVA) = ℓ 2 :=
  ⟨chordMomentum_eq_of_card ℓ _ 0 (by decide +kernel),
    chordMomentum_eq_of_card ℓ _ 1 (by decide +kernel),
    chordMomentum_eq_of_card ℓ _ 2 (by decide +kernel)⟩

/-- The unimodular change of loop momenta of `VA`: `ℓ ↦ (ℓ 2, ℓ 0 - ℓ 2, ℓ 1)`. -/
def v3aMat : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, 1; 1, 0, -1; 0, 1, 0]

theorem isUnit_det_v3aMat : IsUnit v3aMat.det := by
  rw [Matrix.det_fin_three]
  simp [v3aMat]

/-- The chords of `VA` carry the frozen loop momenta at `v3aMat ℓ + (p, 0, 0)`. -/
theorem v3a_hchord (p kext : Fin 4 → ℝ) (ℓ : Fin 3 → Fin 4 → ℝ) (f : Line repVA)
    (hf : IsChord f) : v3aMom p kext ℓ f =
      chordMomentum ((fun s => ∑ r, v3aMat s r • ℓ r) + ![p, 0, 0]) f := by
  obtain ⟨c0, c1, c2⟩ := v3a_chordMomentum ((fun s => ∑ r, v3aMat s r • ℓ r) + ![p, 0, 0])
  obtain ⟨n0, -, n2, -, n4, -⟩ := v3aMom_apply p kext ℓ
  rcases (v3a_isChord_iff f).mp hf with rfl | rfl | rfl
  · rw [c0, n0]
    simp [v3aMat, Fin.sum_univ_three]
    abel
  · rw [c1, n2]
    simp [v3aMat, Fin.sum_univ_three]
    abel
  · rw [c2, n4]
    simp [v3aMat, Fin.sum_univ_three]

/-! ### The amplitude of `VA` -/

open QED.OneLoop (photonPropagator electronPropagator)
open QED.GradedProof.X0 (closedFlavoring zOf)

theorem v3a_tails : (v3aL 0).tail = fv kV 0 ∧ (v3aL 1).tail = fv kV 1 ∧
    (v3aL 2).tail = fv kV 4 ∧ (v3aL 3).tail = fv kV 5 ∧ (v3aL 4).tail = fv kV 6 ∧
    (v3aL 5).tail = fv kV 3 := by decide +kernel

theorem v3a_heads : (v3aP 0).head = pg kV 4 ∧ (v3aP 1).head = pg kV 3 ∧
    (v3aP 2).head = pg kV 6 := by decide +kernel

theorem v3a_vals : (v3aL 0).1 = fv kV 1 ∧ (v3aL 1).1 = fv kV 2 ∧ (v3aL 2).1 = fv kV 3 ∧
    (v3aL 3).1 = fv kV 4 ∧ (v3aL 4).1 = fv kV 5 ∧ (v3aL 5).1 = fv kV 6 ∧
    (v3aP 0).1 = pg kV 0 ∧ (v3aP 1).1 = pg kV 2 ∧ (v3aP 2).1 = pg kV 5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem v3a_prod_fermionLine {M : Type*} [CommMonoid M] (g : FermionLine repVA → M) :
    ∏ f, g f = g (v3aL 0) * g (v3aL 1) * g (v3aL 2) * g (v3aL 3) * g (v3aL 4) * g (v3aL 5) := by
  rw [← (Equiv.ofBijective _ v3aL_bijective).prod_comp, Fin.prod_univ_six]
  rfl

theorem v3a_prod_photonLine {M : Type*} [CommMonoid M] (g : PhotonLine repVA → M) :
    ∏ f, g f = g (v3aP 0) * g (v3aP 1) * g (v3aP 2) := by
  rw [← (Equiv.ofBijective _ v3aP_bijective).prod_comp, Fin.prod_univ_three]
  rfl

theorem v3a_cond (α β : Wick.FermionVertex kV → Fin 4) (lor : Wick.PhotonSlot kV → Fin 4)
    (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, repVA.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, repVA.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, repVA.1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      (lor (pg kV 1) = μ 0 ∧ (α (fv kV 2) = αOut 0 ∧ β (fv kV 0) = βIn 0)) := by
  have h0 : ∀ t, repVA.1.1 (.inl 0) = .inr t ↔ t = fv kV 2 := by decide +kernel
  have h1 : ∀ t, repVA.1.1 (.inr t) = .inl 0 ↔ t = fv kV 0 := by decide +kernel
  have h2 : ∀ a, repVA.1.2 (.inl 0) = .inr a ↔ a = pg kV 1 := by decide +kernel
  simp only [Fin.forall_fin_one, h0, h1, h2, forall_eq]
  tauto

theorem v3a_flav {F : Type} (Φ : Lepton.Flavors F) (f : F) :
    closedFlavoring Φ (zOf repVA) f (fv kV 0) = Φ.openLine ∧
    closedFlavoring Φ (zOf repVA) f (fv kV 1) = Φ.openLine ∧
    closedFlavoring Φ (zOf repVA) f (fv kV 2) = Φ.openLine ∧
    closedFlavoring Φ (zOf repVA) f (fv kV 3) = f ∧
    closedFlavoring Φ (zOf repVA) f (fv kV 4) = f ∧
    closedFlavoring Φ (zOf repVA) f (fv kV 5) = f ∧
    closedFlavoring Φ (zOf repVA) f (fv kV 6) = f := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold closedFlavoring <;> split_ifs with h <;>
    first | rfl | exact absurd h (by decide +kernel)

/-- The splitting of the fermion fields of `repVA` into the open line `2, 1, 0` and the loop
`4, 5, 6, 3`. -/
noncomputable def v3aSplit : Wick.FermionVertex kV ≃ Fin 3 ⊕ Fin 4 :=
  Equiv.ofBijective (fun t => (![.inl 2, .inl 1, .inl 0, .inr 3, .inr 0, .inr 1, .inr 2] :
    Fin 7 → _) t.1) (by decide +kernel)

/-- **The amplitude of `repVA`** at the flavouring with loop flavour `f`. -/
theorem v3a_amplitude (P : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Graded.Counterterms F)
    (f : F) (pIn kIn : Fin 1 → Fin 4 → ℝ) (kk : Line repVA → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    Graded.contractionAmplitude P Φ D repVA (closedFlavoring Φ (zOf repVA) f) 0 pIn kIn kk
        αOut βIn μ =
      (I * P.e) ^ 7 * (1 / I) ^ 9 *
        ∑ l4 : Fin 4, ∑ l3 : Fin 4, ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l6 : Fin 4, ∑ l5 : Fin 4,
          photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3aP 0))) l0 l4 *
          photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3aP 1))) l2 l3 *
          photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3aP 2))) l5 l6 *
          Matrix.trace (Dirac.gamma l4 * electronPropagator (Φ.mass f) P.ε (kk (.inl (v3aL 3))) *
            Dirac.gamma l5 * electronPropagator (Φ.mass f) P.ε (kk (.inl (v3aL 4))) *
            Dirac.gamma l6 * electronPropagator (Φ.mass f) P.ε (kk (.inl (v3aL 5))) *
            Dirac.gamma l3 * electronPropagator (Φ.mass f) P.ε (kk (.inl (v3aL 2)))) *
          (Dirac.gamma l2 * electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (v3aL 1))) *
            Dirac.gamma (μ 0) *
            electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (v3aL 0))) * Dirac.gamma l0)
            (αOut 0) (βIn 0) := by
  obtain ⟨t0, t1, t2, t3, t4, t5⟩ := v3a_tails
  obtain ⟨g0, g1, g2⟩ := v3a_heads
  obtain ⟨v0, v1, v2, v3, v4, v5, w0, w1, w2⟩ := v3a_vals
  obtain ⟨f0, f1, f2, f3, f4, f5, f6⟩ := v3a_flav Φ f
  unfold Graded.contractionAmplitude
  rw [show (∑ α : Wick.FermionVertex kV → Fin 4, ∑ β : Wick.FermionVertex kV → Fin 4,
      ∑ lor : Wick.PhotonSlot kV → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  simp only [v3a_cond, Fin.prod_univ_seven, v3a_prod_fermionLine, v3a_prod_photonLine, t0, t1, t2,
    t3, t4, t5, g0, g1, g2, v0, v1, v2, v3, v4, v5, w0, w1, w2, vertexFactor_kV, f1, f2, f3, f4,
    f5, f6, ite_and_eq_mul_ite]
  set K : ℂ := (I * P.e) ^ 7 * (1 / I) ^ 9 with hK
  have hR : K * ∑ l4 : Fin 4, ∑ l3 : Fin 4, ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l6 : Fin 4,
      ∑ l5 : Fin 4,
        photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3aP 0))) l0 l4 *
        photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3aP 1))) l2 l3 *
        photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3aP 2))) l5 l6 *
        Matrix.trace (Dirac.gamma l4 * electronPropagator (Φ.mass f) P.ε (kk (.inl (v3aL 3))) *
          Dirac.gamma l5 * electronPropagator (Φ.mass f) P.ε (kk (.inl (v3aL 4))) *
          Dirac.gamma l6 * electronPropagator (Φ.mass f) P.ε (kk (.inl (v3aL 5))) *
          Dirac.gamma l3 * electronPropagator (Φ.mass f) P.ε (kk (.inl (v3aL 2)))) *
        (Dirac.gamma l2 * electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (v3aL 1))) *
          Dirac.gamma (μ 0) *
          electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (v3aL 0))) * Dirac.gamma l0)
          (αOut 0) (βIn 0) =
      ∑ lor : Wick.PhotonSlot kV → Fin 4, (if lor (pg kV 1) = μ 0 then (1 : ℂ) else 0) *
        (K * (photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3aP 0))) (lor (pg kV 0)) (lor (pg kV 4)) *
          photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3aP 1))) (lor (pg kV 2)) (lor (pg kV 3)) *
          photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3aP 2))) (lor (pg kV 5)) (lor (pg kV 6)) *
          Matrix.trace (Dirac.gamma (lor (pg kV 4)) *
            electronPropagator (Φ.mass f) P.ε (kk (.inl (v3aL 3))) *
            Dirac.gamma (lor (pg kV 5)) * electronPropagator (Φ.mass f) P.ε (kk (.inl (v3aL 4))) *
            Dirac.gamma (lor (pg kV 6)) * electronPropagator (Φ.mass f) P.ε (kk (.inl (v3aL 5))) *
            Dirac.gamma (lor (pg kV 3)) *
            electronPropagator (Φ.mass f) P.ε (kk (.inl (v3aL 2)))) *
          (Dirac.gamma (lor (pg kV 2)) *
            electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (v3aL 1))) *
            Dirac.gamma (lor (pg kV 1)) *
            electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (v3aL 0))) *
            Dirac.gamma (lor (pg kV 0))) (αOut 0) (βIn 0))) := by
    rw [sum_lor_kV]
    simp only [pg, Matrix.cons_val]
    symm
    rw [Finset.sum_eq_single (μ 0)
      (fun b _ hb => by simp only [hb, ite_false, zero_mul, Finset.sum_const_zero])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp only [ite_true, one_mul, Finset.mul_sum]
  rw [hR]
  refine Finset.sum_congr rfl fun lor _ => ?_
  by_cases hL : lor (pg kV 1) = μ 0
  · have h := sum_spinor_chain3_loop4 v3aSplit (x₁ := fv kV 2) (x₂ := fv kV 1) (x₃ := fv kV 0)
      (y₁ := fv kV 4) (y₂ := fv kV 5) (y₃ := fv kV 6) (y₄ := fv kV 3) rfl rfl rfl rfl rfl rfl rfl
      (K * photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3aP 0))) (lor (pg kV 0)) (lor (pg kV 4)) *
        photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3aP 1))) (lor (pg kV 2)) (lor (pg kV 3)) *
        photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3aP 2))) (lor (pg kV 5)) (lor (pg kV 6)))
      (Dirac.gamma (lor (pg kV 2))) (Dirac.gamma (μ 0)) (Dirac.gamma (lor (pg kV 0)))
      (electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (v3aL 1))))
      (electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (v3aL 0))))
      (Dirac.gamma (lor (pg kV 4))) (Dirac.gamma (lor (pg kV 5))) (Dirac.gamma (lor (pg kV 6)))
      (Dirac.gamma (lor (pg kV 3)))
      (electronPropagator (Φ.mass f) P.ε (kk (.inl (v3aL 3))))
      (electronPropagator (Φ.mass f) P.ε (kk (.inl (v3aL 4))))
      (electronPropagator (Φ.mass f) P.ε (kk (.inl (v3aL 5))))
      (electronPropagator (Φ.mass f) P.ε (kk (.inl (v3aL 2)))) (αOut 0) (βIn 0)
    simp only [hL, ite_true, one_mul]
    refine Eq.trans ?_ (h.trans ?_)
    · refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
      rw [hK]
      by_cases ha : α (fv kV 2) = αOut 0 <;> by_cases hb : β (fv kV 0) = βIn 0 <;>
        simp only [ha, hb, and_true, and_false, ite_true, ite_false] <;> ring
    · ring
  · simp only [hL, ite_false, zero_mul, Finset.sum_const_zero]

/-! ### The inner integrand of `VA` -/

/-- The block-summed integrand of the two-photon class `VA` of `Π⁽⁴⁾` is `(2π)⁻⁸` times its
regulated amplitude in its routing. -/
theorem v3a_vSumF_eq (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Graded.Counterterms F) (hε : P.ε ≠ 0) (k : Fin 4 → ℝ) (q : Fin 2 → Fin 4 → ℝ)
    (a b : Fin 4) :
    QED.GradedProof.VP2.vSumF Φ P.e QED.GradedProof.VP2.aVA QED.GradedProof.VP2.baseVA
        QED.GradedProof.VP2.cVA P.mγ P.Λ P.ε k q a b =
      (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        Graded.regulatedAmplitude P Φ D QED.GradedProof.VP2.repVA 0 ![] ![k, -k]
          (QED.GradedProof.VP2.vaMom k q) ![] ![] ![a, b] := by
  rw [QED.GradedProof.VP2.va_integrand P Φ D hε k q a b,
    QED.GradedProof.VP2.pp_eq_ppc QED.GradedProof.VP2.ppVA_eq k]
  exact (QED.GradedProof.VP2.sum_vterm_eq Φ _ _ _ P.e P.mγ P.Λ P.ε k q a b).symm

/-- The inner integrands of `VA`: `(1/i)` times the block-summed integrand of the two-photon class
`VA` at `-k`. -/
noncomputable def v3aY (P : Params) {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (a b : Fin 4)
    (k : Fin 4 → ℝ) (q : Fin 2 → Fin 4 → ℝ) : ℂ :=
  (1 / I) * QED.GradedProof.VP2.vSumF Φ P.e QED.GradedProof.VP2.aVA QED.GradedProof.VP2.baseVA
    QED.GradedProof.VP2.cVA P.mγ P.Λ P.ε (-k) q a b

/-- **The Wick factorization of `VA`**: in the nested routing, the integrand of the value of
`repVA` is `nestG` of the outer factor and the inner integrands `v3aY`. -/
theorem v3a_routedIntegrand (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (hε : P.ε ≠ 0) (p' p : Fin 4 → ℝ)
    (μ i j : Fin 4) (ℓ : Fin 3 → Fin 4 → ℝ) :
    routedIntegrand P Φ D repVA 0 3 (fun _ => p) (fun _ => p' - p) (v3aMom p (p' - p) ℓ)
        (fun _ => i) (fun _ => j) (fun _ => μ) =
      QED.ChainProof.SetANestV.nestG
        (QED.ChainProof.SetANestV.nestOuter P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p μ i j)
        (v3aY P Φ) ℓ := by
  obtain ⟨s1, s2, s3⟩ := QED.ChainProof.SetALinkV.shapeOK_repVA
  have hC : QED.GradedProof.X0.ClosedShape repVA (zOf repVA) :=
    ⟨s1, fun t ht => s2 t ht not_false, s3⟩
  obtain ⟨n0, n1, n2, n3, n4, n5, m0, m1, m2⟩ := v3aMom_apply p (p' - p) ℓ
  obtain ⟨u0, u1, u2, u3, u4⟩ := QED.GradedProof.VP2.vaMom_apply (-ℓ 2) ![ℓ 0, ℓ 1]
  have hp : p + (p' - p) + ℓ 2 = p' + ℓ 2 := by abel
  have hq : ℓ 1 - ℓ 0 = -(ℓ 0 - ℓ 1) := by abel
  have hk : ℓ 0 + -ℓ 2 = ℓ 0 - ℓ 2 := by abel
  simp only [routedIntegrand, QED.GradedProof.X0.regulatedAmplitude_eq_closed Φ P D hC,
    v3a_amplitude, QED.ChainProof.SetANestV.nestG, v3aY, v3a_vSumF_eq P Φ D hε,
    QED.GradedProof.VP2.regulatedAmplitude_of_oneLoop Φ P D QED.GradedProof.VP2.oneLoop_repVA
      (QED.GradedProof.SE2.fv4 0),
    QED.GradedProof.VP2.va_amplitude, QED.ChainProof.SetANestV.nestOuter,
    QED.TwoLoop.Insertion.vertexChain, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    n0, n1, n2, n3, n4, n5, m0, m1, m2, u0, u1, u2, u3, u4, hp, hq, hk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Finset.mul_sum, Finset.sum_mul]
  rw [sum_flavor_out_four]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [sum_pair_out_three]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl
    fun f _ => Finset.sum_congr rfl fun ρ' _ => Finset.sum_congr rfl fun σ' _ => ?_
  rw [QED.TwoLoop.Insertion.photonPropagator_neg', QED.TwoLoop.Insertion.photonPropagator_neg',
    QED.TwoLoop.Insertion.photonPropagator_neg' _ _ _ (ℓ 2),
    QED.TwoLoop.Insertion.photonPropagator_comm' _ _ _ (ℓ 0 - ℓ 1) σ' ρ']
  push_cast
  ring

/-! ### The inputs of the nested form of `VA` -/

/-- The value of `repVA` is the joint three-loop integral of `nestG nestOuter v3aY`. -/
theorem v3a_hval (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Graded.Counterterms F) (hε : P.ε ≠ 0) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    Graded.contractionValue P Φ D repVA 0 (fun _ => p') (fun _ => p) (fun _ => p' - p)
        (fun _ => i) (fun _ => j) (fun _ => μ) =
      QED.TwoLoop.jointEnergyFirstIntegral 3 (QED.ChainProof.SetANestV.nestG
        (QED.ChainProof.SetANestV.nestOuter P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p μ i j)
        (v3aY P Φ)) := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  have hcons := isConserved_v3aMom (pOut := fun _ => p') (pIn := fun _ => p)
    (kIn := fun _ => p' - p) hmom
  rw [contractionValue_eq_of_routing P Φ D repVA 0 loopCount_repVA (v3aMom p (p' - p))
    hcons v3aMat isUnit_det_v3aMat ![p, 0, 0] (v3a_hchord p (p' - p))]
  exact congrArg _ (funext fun ℓ => v3a_routedIntegrand P Φ D hε p' p μ i j ℓ)

/-- (HA₀) for `repVA` in the nested routing. -/
theorem v3a_hF (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Graded.Counterterms F) (rep : F → F) (hH : QED.ChainProof.SetALink.IntHypA P Φ D rep)
    (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable 3 (QED.ChainProof.SetANestV.nestG
        (QED.ChainProof.SetANestV.nestOuter P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p μ i j)
        (v3aY P Φ)) := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  have hcons := isConserved_v3aMom (pOut := fun _ => p') (pIn := fun _ => p)
    (kIn := fun _ => p' - p) hmom
  have h := jointEnergyFirstIntegrable_of_routing P Φ D repVA 0 loopCount_repVA
    (v3aMom p (p' - p)) hcons v3aMat isUnit_det_v3aMat ![p, 0, 0]
    (v3a_hchord p (p' - p)) _ _ _
    (QED.ChainProof.SetALinkV.classIntA_repVA P Φ D rep hH (fun _ => p') (fun _ => p)
      (fun _ => p' - p) hmom (fun _ => i) (fun _ => j) (fun _ => μ))
  exact (congrArg _ (funext fun ℓ => v3a_routedIntegrand P Φ D hH.hε.ne' p' p μ i j ℓ)).mp h

/-- The photon tensor of `VA`: the joint integral of `v3aY` is `(1/i)` times the value of the
two-photon class `VA` at `-k`. -/
theorem v3a_efi (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Graded.Counterterms F) (hε : P.ε ≠ 0) (k : Fin 4 → ℝ) (a b : Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegral 2 (v3aY P Φ a b k) =
      (1 / I) * QED.GradedProof.VP2.val0 P Φ D (-k) a b QED.GradedProof.VP2.repVA := by
  rw [show v3aY P Φ a b k = fun q => (1 / I) * QED.GradedProof.VP2.vSumF Φ P.e
      QED.GradedProof.VP2.aVA QED.GradedProof.VP2.baseVA QED.GradedProof.VP2.cVA P.mγ P.Λ P.ε
      (-k) q a b from rfl, QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul]
  exact congrArg _ (QED.GradedProof.VP2.val0_repVA Φ D P hε (-k) a b).symm

/-- **The nested form of `VA`.** Under the hypotheses `IntHypA` of (HA₀) and masses bounded below
by `m₀ > 0`, the class `VA` is in nested form with the photon tensor
`X(k)^{ab} = (1/i) val0(VA)(-k)^{ab}` of the two-photon class `VA` of `Π⁽⁴⁾`. -/
theorem loopNested_v3a (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (rep : F → F)
    (hH : QED.ChainProof.SetALink.IntHypA P Φ D rep) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (p' p : Fin 4 → ℝ) :
    LoopNested P Φ D repVA
      (fun k a b => (1 / I) * QED.GradedProof.VP2.val0 P Φ D (-k) a b QED.GradedProof.VP2.repVA)
      p' p := by
  have hE := QED.ChainProof.SetANestV.el1_VA Φ rep hm₀ hmass hH.hrep hH.hPV₁ hH.hPV₂ P.e P.mγ P.Λ
  have h := QED.ChainProof.SetANestV.loopNested_of_nestGL1 P Φ D repVA hH.hε p' p (v3aY P Φ)
    (fun μ i j => v3a_hval P Φ D hH.hε.ne' p' p μ i j) (fun μ i j => v3a_hF P Φ D rep hH p' p μ i j)
    (fun a b k => QED.ChainProof.SetANestV.jointEnergyFirstIntegrable_vSumF_neg Φ P.e P.mγ P.Λ _ _ _
      hE hH.hε (1 / I) a b k)
    (fun a b => QED.ChainProof.SetANestV.innerBoundL1_vSumF_neg Φ P.e P.mγ P.Λ _ _ _ hE hH.hε
      (1 / I) a b)
  have e : (fun k a b => QED.TwoLoop.jointEnergyFirstIntegral 2 (v3aY P Φ a b k)) =
      fun k a b => (1 / I) *
        QED.GradedProof.VP2.val0 P Φ D (-k) a b QED.GradedProof.VP2.repVA :=
    funext fun k => funext fun a => funext fun b => v3a_efi P Φ D hH.hε.ne' k a b
  rwa [e] at h

/-- **The vertex-type group identity** for `QED.ChainProof.SetAPauliAssembly.SetANestClasses`: the
photon tensors of `VA` (`loopNested_v3a`), `VB` and `VC` sum to `(1/i)` times the values of the
two-photon classes `VA`, `VB`, `VC` at `-ℓ`. -/
theorem vertexType_group_sum (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (ℓ : Fin 4 → ℝ) (a b : Fin 4) :
    (1 / I) * QED.GradedProof.VP2.val0 P Φ D (-ℓ) a b QED.GradedProof.VP2.repVA +
        (1 / I) * QED.GradedProof.VP2.val0 P Φ D (-ℓ) a b QED.GradedProof.VP2.repVB +
        (1 / I) * QED.GradedProof.VP2.val0 P Φ D (-ℓ) a b QED.GradedProof.VP2.repVC =
      (1 / I) * (QED.GradedProof.VP2.val0 P Φ D (-ℓ) a b QED.GradedProof.VP2.repVA +
        QED.GradedProof.VP2.val0 P Φ D (-ℓ) a b QED.GradedProof.VP2.repVB +
        QED.GradedProof.VP2.val0 P Φ D (-ℓ) a b QED.GradedProof.VP2.repVC) := by
  ring

end QED.ChainProof.SetANest

end
