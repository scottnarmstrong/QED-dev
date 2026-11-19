/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.LeptonProof.HMPhoton
public import QED.GradedProof.LevelOnePhoton
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The order-`e²` two-photon function of arbitrary flavour data through T1's

Helper level for the Phase 5 Stage 2 goal (G-ex₁) `QED.Graded.existsUnique_withLevel_zero`
(decision D-57). For flavour data `Φ` with positive masses and the two Pauli–Villars conditions
`∑_f c_f = 0`, `∑_f c_f M_f² = 0`, the order-`e²` two-photon 1PI function (F₈) splits into T1
two-photon functions (`onePIFunction₂_photon_split`):

`Π_Φ = Π_T1(P₀) + ∑_i γ_i Π_T1(Q_i)`,

where `P₀ = refParams P` is T1 at the masses `(1, 2, 3)` with the Pauli–Villars coefficients
`(1, -8/5, 3/5)`, and `Q_i = blockParams P Φ i` is T1 at the masses `(a_i, X, Y)`, for the atoms
`(a_i, γ_i)` of the signed measure `∑_f c_f δ_{M_f} - ∑_j c^{(0)}_j δ_{M^{(0)}_j}` and two masses
`X < Y` above all `a_i`. The weights sum to `0`. This is the argument of
`QED.Lepton.Proof.HM.onePIFunction₂_photon_leptonFlavors_eq` for arbitrary flavour data.

The two-photon contractions of order `≤ 2` have no fermion counterterm vertex and no open fermion
line, so their amplitude reads neither the mass field `m` of the parameters nor the open-line
mass (`loopAmp_zero_eq`, `loopAmp_zero_eq_of_not_hasLoop`); this is what allows T1 blocks with
masses other than `P.m`.
-/

@[expose] public section

open Complex Finset
open QED.WickModel (Params Contraction IsOnePI fermionSign loopCount lineMomentum₂)
open QED.Lepton QED.Lepton.Proof.HM

namespace QED.GradedProof.PhotonSplit

open scoped Classical

/-! ### The amplitudes do not read `m` or the open-line mass -/

section Amplitude

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- Away from a fermion counterterm vertex, the vertex factor does not read the mass `m`. -/
theorem vertexFactor_congr_m (e δ₁ δ₂ δm δ₃ m m' : ℝ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (kψ : Wick.FermionVertex κ → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) (t : Fin N) (ht : κ t ≠ .fermionCt) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      Wick.vertexFactor e δ₁ δ₂ δm δ₃ m' α β lor kψ kA t := by
  unfold Wick.vertexFactor
  split <;> rename_i h <;> first | rfl | exact absurd h ht

/-- Without a fermion counterterm vertex, the amplitude reads only `e`, the counterterms and the
photon-propagator data of the parameters. -/
theorem contractionAmplitude₂_congr_params (P Q : Params) {F' : Type} (Ψ : Flavors F')
    (C : Contraction nf nA κ) (φ : Flavoring Ψ κ) (hκ : ∀ t, κ t ≠ .fermionCt)
    (he : Q.e = P.e) (h₁ : Q.δ₁ = P.δ₁) (h₂ : Q.δ₂ = P.δ₂) (hδm : Q.δm = P.δm)
    (h₃ : Q.δ₃ = P.δ₃) (hγ : Q.mγ = P.mγ) (hΛ : Q.Λ = P.Λ) (hε : Q.ε = P.ε)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : QED.WickModel.Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionAmplitude₂ Q Ψ C φ pIn kIn k αOut βIn μ =
      contractionAmplitude₂ P Ψ C φ pIn kIn k αOut βIn μ := by
  unfold contractionAmplitude₂
  rw [he, h₁, h₂, hδm, h₃, hγ, hΛ, hε]
  refine sum_congr rfl fun α _ => sum_congr rfl fun β _ => sum_congr rfl fun lor _ => ?_
  rw [prod_congr rfl fun t _ => vertexFactor_congr_m P.e P.δ₁ P.δ₂ P.δm P.δ₃ Q.m P.m α β lor _ _
    t (hκ t)]

theorem not_onOpen_zero (C : Contraction 0 nA κ) (t : Wick.FermionVertex κ) : ¬ OnOpen C t :=
  fun ⟨i, _⟩ => i.elim0

/-- **With no external fermion**, the loop amplitude reads only the loop mass, and not `m`. -/
theorem loopAmp_zero_eq (P Q : Params) {C : Contraction 0 nA κ} (hS : IsSimple C)
    (hκ : ∀ t, κ t ≠ .fermionCt) (he : Q.e = P.e) (h₁ : Q.δ₁ = P.δ₁) (h₂ : Q.δ₂ = P.δ₂)
    (hδm : Q.δm = P.δm) (h₃ : Q.δ₃ = P.δ₃) (hγ : Q.mγ = P.mγ) (hΛ : Q.Λ = P.Λ) (hε : Q.ε = P.ε)
    (a a' b : ℝ) (pIn : Fin 0 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (k : QED.WickModel.Line C → Fin 4 → ℝ) (αOut βIn : Fin 0 → Fin 4) (μ : Fin nA → Fin 4) :
    loopAmp Q hS a b pIn kIn k αOut βIn μ = loopAmp P hS a' b pIn kIn k αOut βIn μ := by
  unfold loopAmp
  rw [contractionAmplitude₂_congr_params P Q _ C _ hκ he h₁ h₂ hδm h₃ hγ hΛ hε]
  refine contractionAmplitude₂_congr _ _ P C _ _ (fun l => ?_) pIn kIn k αOut βIn μ
  rw [loopFlavoring_apply, loopFlavoring_apply]
  simp [not_onOpen_zero C l.1, biFlavors]

/-- **With no external fermion and no loop**, the loop amplitude reads no mass at all. -/
theorem loopAmp_zero_eq_of_not_hasLoop (P Q : Params) {C : Contraction 0 nA κ}
    (hS : IsSimple C) (hL : ¬ HasLoop C) (hκ : ∀ t, κ t ≠ .fermionCt) (he : Q.e = P.e)
    (h₁ : Q.δ₁ = P.δ₁) (h₂ : Q.δ₂ = P.δ₂) (hδm : Q.δm = P.δm) (h₃ : Q.δ₃ = P.δ₃)
    (hγ : Q.mγ = P.mγ) (hΛ : Q.Λ = P.Λ) (hε : Q.ε = P.ε) (a a' b b' : ℝ)
    (pIn : Fin 0 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (k : QED.WickModel.Line C → Fin 4 → ℝ) (αOut βIn : Fin 0 → Fin 4) (μ : Fin nA → Fin 4) :
    loopAmp Q hS a b pIn kIn k αOut βIn μ = loopAmp P hS a' b' pIn kIn k αOut βIn μ := by
  unfold loopAmp
  rw [contractionAmplitude₂_congr_params P Q _ C _ hκ he h₁ h₂ hδm h₃ hγ hΛ hε]
  refine contractionAmplitude₂_congr _ _ P C _ _ (fun l => ?_) pIn kIn k αOut βIn μ
  exact absurd ⟨l.1, not_onOpen_zero C l.1⟩ hL

end Amplitude

/-! ### The T1 blocks -/

section Blocks

variable {F : Type} [Fintype F]

/-- The reference T1 parameters: masses `(1, 2, 3)`, coefficients `(1, -8/5, 3/5)`. -/
noncomputable def refParams (P : Params) : Params :=
  { P with m := 1, M₁ := 2, M₂ := 3, c₁ := -8 / 5, c₂ := 3 / 5 }

/-- The atom masses: the flavour masses, then the reference masses. -/
def atomMass (Φ : Flavors F) : F ⊕ Fin 3 → ℝ :=
  Sum.elim Φ.mass ![1, 2, 3]

/-- The atom weights: the flavour coefficients, then minus the reference coefficients. -/
noncomputable def atomCoeff (Φ : Flavors F) : F ⊕ Fin 3 → ℝ :=
  Sum.elim Φ.coeff ![-1, 8 / 5, -3 / 5]

/-- The first auxiliary regulator mass, above every atom mass. -/
def bigX (Φ : Flavors F) : ℝ :=
  4 + ∑ f, |Φ.mass f|

/-- The first T1 coefficient fixed by the Pauli–Villars conditions at the masses `(M, X, Y)`. -/
noncomputable def alpha (X Y M : ℝ) : ℝ :=
  (Y ^ 2 - M ^ 2) / (X ^ 2 - Y ^ 2)

/-- **The T1 block of atom `i`**: masses `(a_i, X, X + 1)` with the Pauli–Villars
coefficients. -/
noncomputable def blockParams (P : Params) (Φ : Flavors F) (i : F ⊕ Fin 3) : Params :=
  { P with
    m := atomMass Φ i, M₁ := bigX Φ, M₂ := bigX Φ + 1,
    c₁ := alpha (bigX Φ) (bigX Φ + 1) (atomMass Φ i),
    c₂ := -1 - alpha (bigX Φ) (bigX Φ + 1) (atomMass Φ i) }

theorem four_le_bigX (Φ : Flavors F) : 4 ≤ bigX Φ := by
  unfold bigX
  have := sum_nonneg fun f (_ : f ∈ (univ : Finset F)) => abs_nonneg (Φ.mass f)
  linarith

theorem atomMass_lt_bigX (Φ : Flavors F) (i : F ⊕ Fin 3) : atomMass Φ i < bigX Φ := by
  have h4 := four_le_bigX Φ
  rcases i with f | j
  · have h1 : Φ.mass f ≤ ∑ g, |Φ.mass g| :=
      (le_abs_self _).trans (single_le_sum (fun g _ => abs_nonneg (Φ.mass g)) (mem_univ f))
    show Φ.mass f < bigX Φ
    unfold bigX
    linarith
  · fin_cases j <;> simp [atomMass] <;> linarith

omit [Fintype F] in
theorem atomMass_pos (Φ : Flavors F) (hmass : ∀ f, 0 < Φ.mass f) (i : F ⊕ Fin 3) :
    0 < atomMass Φ i := by
  rcases i with f | j
  · exact hmass f
  · fin_cases j <;> simp [atomMass]

theorem sq_bigX_ne (Φ : Flavors F) : bigX Φ ^ 2 - (bigX Φ + 1) ^ 2 ≠ 0 := by
  have := four_le_bigX Φ
  nlinarith

theorem sum_atomCoeff (Φ : Flavors F) (hPV₁ : ∑ f, Φ.coeff f = 0) : ∑ i, atomCoeff Φ i = 0 := by
  simp only [Fintype.sum_sum_type, atomCoeff, Sum.elim_inl, Sum.elim_inr, hPV₁,
    Fin.sum_univ_three]
  simp
  norm_num

theorem sum_atomCoeff_mul_sq (Φ : Flavors F) (hPV₂ : ∑ f, Φ.coeff f * Φ.mass f ^ 2 = 0) :
    ∑ i, atomCoeff Φ i * atomMass Φ i ^ 2 = 0 := by
  simp only [Fintype.sum_sum_type, atomCoeff, atomMass, Sum.elim_inl, Sum.elim_inr, hPV₂,
    Fin.sum_univ_three]
  simp
  norm_num

theorem sum_atomCoeff_mul_alpha (Φ : Flavors F) (hPV₁ : ∑ f, Φ.coeff f = 0)
    (hPV₂ : ∑ f, Φ.coeff f * Φ.mass f ^ 2 = 0) :
    ∑ i, atomCoeff Φ i * alpha (bigX Φ) (bigX Φ + 1) (atomMass Φ i) = 0 := by
  have e : ∑ i, atomCoeff Φ i * alpha (bigX Φ) (bigX Φ + 1) (atomMass Φ i) =
      ((bigX Φ + 1) ^ 2 * ∑ i, atomCoeff Φ i - ∑ i, atomCoeff Φ i * atomMass Φ i ^ 2) /
        (bigX Φ ^ 2 - (bigX Φ + 1) ^ 2) := by
    rw [mul_sum, ← sum_sub_distrib, sum_div]
    refine sum_congr rfl fun i _ => ?_
    unfold alpha
    ring
  rw [e, sum_atomCoeff Φ hPV₁, sum_atomCoeff_mul_sq Φ hPV₂]
  simp

theorem refParams_PV₁ (P : Params) :
    1 + (refParams P).c₁ + (refParams P).c₂ = 0 := by
  simp only [refParams]
  norm_num

theorem refParams_PV₂ (P : Params) :
    (refParams P).m ^ 2 + (refParams P).c₁ * (refParams P).M₁ ^ 2 +
      (refParams P).c₂ * (refParams P).M₂ ^ 2 = 0 := by
  simp only [refParams]
  norm_num

theorem blockParams_PV₁ (P : Params) (Φ : Flavors F) (i : F ⊕ Fin 3) :
    1 + (blockParams P Φ i).c₁ + (blockParams P Φ i).c₂ = 0 := by
  simp only [blockParams]
  ring

theorem blockParams_PV₂ (P : Params) (Φ : Flavors F) (i : F ⊕ Fin 3) :
    (blockParams P Φ i).m ^ 2 + (blockParams P Φ i).c₁ * (blockParams P Φ i).M₁ ^ 2 +
      (blockParams P Φ i).c₂ * (blockParams P Φ i).M₂ ^ 2 = 0 := by
  have h := sq_bigX_ne Φ
  simp only [blockParams, alpha]
  field_simp
  ring

/-- **The loop-flavour measure splits into the T1 blocks**: for every `G`,
`∑_f c_f G(M_f) = ∑_j c^{(0)}_j G(M^{(0)}_j) + ∑_i γ_i ∑_j c^{(i)}_j G(M^{(i)}_j)`. -/
theorem sum_coeff_split (P : Params) (Φ : Flavors F) (hPV₁ : ∑ f, Φ.coeff f = 0)
    (hPV₂ : ∑ f, Φ.coeff f * Φ.mass f ^ 2 = 0) (G : ℝ → ℂ) :
    ∑ f, (Φ.coeff f : ℂ) * G (Φ.mass f) =
      ∑ j, ((refParams P).loopCoeff j : ℂ) * G ((refParams P).mass j) +
        ∑ i, (atomCoeff Φ i : ℂ) *
          ∑ j, ((blockParams P Φ i).loopCoeff j : ℂ) * G ((blockParams P Φ i).mass j) := by
  set X := bigX Φ
  have e : ∀ i, (atomCoeff Φ i : ℂ) *
      ∑ j, ((blockParams P Φ i).loopCoeff j : ℂ) * G ((blockParams P Φ i).mass j) =
      (atomCoeff Φ i : ℂ) * G (atomMass Φ i) +
        ((atomCoeff Φ i * alpha X (X + 1) (atomMass Φ i) : ℝ) : ℂ) * (G X - G (X + 1)) -
          (atomCoeff Φ i : ℂ) * G (X + 1) := by
    intro i
    simp only [Fin.sum_univ_three, Params.loopCoeff, Params.mass, blockParams,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    push_cast
    ring
  rw [sum_congr rfl fun i _ => e i, sum_sub_distrib, sum_add_distrib, ← sum_mul, ← sum_mul,
    ← ofReal_sum, ← ofReal_sum, sum_atomCoeff_mul_alpha Φ hPV₁ hPV₂, sum_atomCoeff Φ hPV₁]
  simp only [Fintype.sum_sum_type, atomCoeff, atomMass, Sum.elim_inl, Sum.elim_inr,
    Fin.sum_univ_three, refParams, Params.loopCoeff, Params.mass, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  ring

end Blocks

/-! ### The split, contraction by contraction -/

section Split

variable {F : Type} [Fintype F] [DecidableEq F] {nA N : ℕ} {κ : Fin N → Wick.VertexKind}

theorem t1F_coeff (Q : Params) : (t1F Q).coeff = Q.loopCoeff := rfl

theorem t1F_mass (Q : Params) : (t1F Q).mass = Q.mass := rfl

/-- **The regulated amplitude splits into the T1 blocks** (a simple contraction without external
fermion and without fermion counterterm vertex). -/
theorem regulatedAmplitude₂_split (P : Params) (Φ : Flavors F) (hPV₁ : ∑ f, Φ.coeff f = 0)
    (hPV₂ : ∑ f, Φ.coeff f * Φ.mass f ^ 2 = 0) {C : Contraction 0 nA κ} (hS : IsSimple C)
    (hκ : ∀ t, κ t ≠ .fermionCt) (pIn : Fin 0 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (k : QED.WickModel.Line C → Fin 4 → ℝ) (αOut βIn : Fin 0 → Fin 4) (μ : Fin nA → Fin 4) :
    regulatedAmplitude₂ P Φ C pIn kIn k αOut βIn μ =
      regulatedAmplitude₂ (refParams P) (t1F (refParams P)) C pIn kIn k αOut βIn μ +
        ∑ i, (atomCoeff Φ i : ℂ) * regulatedAmplitude₂ (blockParams P Φ i)
          (t1F (blockParams P Φ i)) C pIn kIn k αOut βIn μ := by
  by_cases hL : HasLoop C
  · simp only [regulatedAmplitude₂_of_hasLoop _ _ hS hL, t1F_coeff, t1F_mass]
    have h0 : ∀ a b, loopAmp (refParams P) hS a b pIn kIn k αOut βIn μ =
        loopAmp P hS (Φ.mass Φ.openLine) b pIn kIn k αOut βIn μ := fun a b =>
      loopAmp_zero_eq P (refParams P) hS hκ rfl rfl rfl rfl rfl rfl rfl rfl a _ b pIn kIn k αOut
        βIn μ
    have hi : ∀ i a b, loopAmp (blockParams P Φ i) hS a b pIn kIn k αOut βIn μ =
        loopAmp P hS (Φ.mass Φ.openLine) b pIn kIn k αOut βIn μ := fun i a b =>
      loopAmp_zero_eq P (blockParams P Φ i) hS hκ rfl rfl rfl rfl rfl rfl rfl rfl a _ b pIn kIn k
        αOut βIn μ
    simp only [h0, hi]
    exact sum_coeff_split P Φ hPV₁ hPV₂
      (fun b => loopAmp P hS (Φ.mass Φ.openLine) b pIn kIn k αOut βIn μ)
  · simp only [regulatedAmplitude₂_of_not_hasLoop _ _ hS hL]
    have h0 : ∀ a b, loopAmp (refParams P) hS a b pIn kIn k αOut βIn μ =
        loopAmp P hS (Φ.mass Φ.openLine) (Φ.mass Φ.openLine) pIn kIn k αOut βIn μ := fun a b =>
      loopAmp_zero_eq_of_not_hasLoop P (refParams P) hS hL hκ rfl rfl rfl rfl rfl rfl rfl rfl a _
        b _ pIn kIn k αOut βIn μ
    have hi : ∀ i a b, loopAmp (blockParams P Φ i) hS a b pIn kIn k αOut βIn μ =
        loopAmp P hS (Φ.mass Φ.openLine) (Φ.mass Φ.openLine) pIn kIn k αOut βIn μ :=
      fun i a b => loopAmp_zero_eq_of_not_hasLoop P (blockParams P Φ i) hS hL hκ rfl rfl rfl rfl
        rfl rfl rfl rfl a _ b _ pIn kIn k αOut βIn μ
    simp only [h0, hi, ← sum_mul, ← ofReal_sum, sum_atomCoeff Φ hPV₁]
    simp

/-- Without a loop, the value of a contraction does not depend on the parameters `m, M, c` or on
the flavour data. -/
theorem contractionValue₂_eq_of_not_hasLoop (P Q : Params) {F' : Type} [Fintype F']
    [DecidableEq F'] (Φ : Flavors F) (Ψ : Flavors F') {C : Contraction 0 nA κ} (hS : IsSimple C)
    (hL : ¬ HasLoop C) (hκ : ∀ t, κ t ≠ .fermionCt) (he : Q.e = P.e) (h₁ : Q.δ₁ = P.δ₁)
    (h₂ : Q.δ₂ = P.δ₂) (hδm : Q.δm = P.δm) (h₃ : Q.δ₃ = P.δ₃) (hγ : Q.mγ = P.mγ)
    (hΛ : Q.Λ = P.Λ) (hε : Q.ε = P.ε) (pOut pIn : Fin 0 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin 0 → Fin 4) (μ : Fin nA → Fin 4) :
    contractionValue₂ Q Ψ C pOut pIn kIn αOut βIn μ =
      contractionValue₂ P Φ C pOut pIn kIn αOut βIn μ := by
  unfold contractionValue₂
  congr 1
  funext ℓ
  congr 1
  rw [regulatedAmplitude₂_of_not_hasLoop _ _ hS hL, regulatedAmplitude₂_of_not_hasLoop _ _ hS hL]
  exact loopAmp_zero_eq_of_not_hasLoop P Q hS hL hκ he h₁ h₂ hδm h₃ hγ hΛ hε _ _ _ _ _ _ _ _ _ _

/-- **The value of a contraction splits into the T1 blocks**, when in case of a loop either there
is no loop momentum or all the T1 integrands are integrable. -/
theorem contractionValue₂_split (P : Params) (Φ : Flavors F) (hPV₁ : ∑ f, Φ.coeff f = 0)
    (hPV₂ : ∑ f, Φ.coeff f * Φ.mass f ^ 2 = 0) {C : Contraction 0 nA κ} (hS : IsSimple C)
    (hκ : ∀ t, κ t ≠ .fermionCt) (pOut pIn : Fin 0 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin 0 → Fin 4) (μ : Fin nA → Fin 4)
    (hint : HasLoop C → loopCount C = 0 ∨
      ((QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
        (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
          regulatedAmplitude₂ (refParams P) (t1F (refParams P)) C pIn kIn
            (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ) ∧
      ∀ i, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
        (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
          regulatedAmplitude₂ (blockParams P Φ i) (t1F (blockParams P Φ i)) C pIn kIn
            (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ)) :
    contractionValue₂ P Φ C pOut pIn kIn αOut βIn μ =
      contractionValue₂ (refParams P) (t1F (refParams P)) C pOut pIn kIn αOut βIn μ +
        ∑ i, (atomCoeff Φ i : ℂ) * contractionValue₂ (blockParams P Φ i)
          (t1F (blockParams P Φ i)) C pOut pIn kIn αOut βIn μ := by
  by_cases hL : HasLoop C
  · rcases hint hL with h0 | ⟨hP, hQ⟩
    · simp only [contractionValue₂_of_loopCount_zero _ _ C h0,
        regulatedAmplitude₂_split P Φ hPV₁ hPV₂ hS hκ]
    · unfold contractionValue₂
      set c : ℂ := (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹
      have hQ' : ∀ i, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun x =>
          (atomCoeff Φ i : ℂ) * (c * regulatedAmplitude₂ (blockParams P Φ i)
            (t1F (blockParams P Φ i)) C pIn kIn (lineMomentum₂ C pOut pIn kIn x) αOut βIn μ) :=
        fun i => jointIntegrable_const_mul _ (hQ i)
      have e : (fun x : Fin (loopCount C) → Fin 4 → ℝ => c * regulatedAmplitude₂ P Φ C pIn kIn
          (lineMomentum₂ C pOut pIn kIn x) αOut βIn μ) = fun x =>
          c * regulatedAmplitude₂ (refParams P) (t1F (refParams P)) C pIn kIn
            (lineMomentum₂ C pOut pIn kIn x) αOut βIn μ +
            ∑ i, (atomCoeff Φ i : ℂ) * (c * regulatedAmplitude₂ (blockParams P Φ i)
              (t1F (blockParams P Φ i)) C pIn kIn (lineMomentum₂ C pOut pIn kIn x) αOut βIn μ) := by
        funext x
        rw [regulatedAmplitude₂_split P Φ hPV₁ hPV₂ hS hκ, mul_add, mul_sum]
        congr 1
        refine sum_congr rfl fun i _ => ?_
        ring
      rw [e, jointIntegral_add hP (jointIntegrable_sum _ fun i _ => hQ' i),
        jointIntegral_sum _ fun i _ => hQ' i]
      congr 1
      refine sum_congr rfl fun i _ => ?_
      rw [jointIntegral_const_mul]
  · have h0 := contractionValue₂_eq_of_not_hasLoop P (refParams P) Φ (t1F (refParams P)) hS hL hκ
      rfl rfl rfl rfl rfl rfl rfl rfl pOut pIn kIn αOut βIn μ
    have hi : ∀ i, contractionValue₂ (blockParams P Φ i) (t1F (blockParams P Φ i)) C pOut pIn
        kIn αOut βIn μ = contractionValue₂ P Φ C pOut pIn kIn αOut βIn μ := fun i =>
      contractionValue₂_eq_of_not_hasLoop P (blockParams P Φ i) Φ (t1F (blockParams P Φ i)) hS
        hL hκ rfl rfl rfl rfl rfl rfl rfl rfl pOut pIn kIn αOut βIn μ
    simp only [h0, hi, ← sum_mul, ← ofReal_sum, sum_atomCoeff Φ hPV₁]
    simp

/-- A 1PI two-photon contraction of order at most `2` has no fermion counterterm vertex. -/
theorem ne_fermionCt_of_photon (hκ : ∑ t, (κ t).order ≤ 2) (C : Contraction 0 2 κ)
    (hC : IsOnePI C) (t : Fin N) : κ t ≠ .fermionCt := by
  rcases lt_or_eq_of_le hκ with hlt | h2
  · exact absurd hC (not_isOnePI_two_photon_of_lt hlt C)
  · rcases gauge_or_photonCt_of_two_photon h2 C hC t with h | h <;> rw [h] <;> decide

/-- **The order-`e²` two-photon function of `Φ` splits into T1 two-photon functions** at every
`ε > 0`. -/
theorem onePIFunction₂_photon_split (P : Params) (hε : 0 < P.ε) (Φ : Flavors F)
    (hmass : ∀ f, 0 < Φ.mass f) (hPV₁ : ∑ f, Φ.coeff f = 0)
    (hPV₂ : ∑ f, Φ.coeff f * Φ.mass f ^ 2 = 0) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    onePIFunction₂ P Φ 0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν] =
      onePIFunction₂ (refParams P) (t1F (refParams P)) 0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν] +
        ∑ i, (atomCoeff Φ i : ℂ) * onePIFunction₂ (blockParams P Φ i) (t1F (blockParams P Φ i))
          0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν] := by
  simp only [onePIFunction₂_eq_ctSum]
  rw [ctSum_congr fun N κ hκ C hC => contractionValue₂_split P Φ hPV₁ hPV₂
    (isSimple_of_photon hκ C hC) (ne_fermionCt_of_photon hκ C hC) ![] ![] ![k, -k] ![] ![]
    ![μ, ν] fun _ => ?_]
  · rw [ctSum_add, ctSum_sum]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [ctSum_const_mul]
  · have hle := QED.TwoLoop.LoopBound.loopCount_le_one_of_order hκ (by norm_num) C hC
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
    · exact Or.inl h0
    · refine Or.inr ⟨jointIntegrable_photon (refParams P) hε (by norm_num [refParams])
        (by norm_num [refParams]) (by norm_num [refParams]) (refParams_PV₁ P) (refParams_PV₂ P)
        hκ C hC h1 k μ ν, fun i => ?_⟩
      exact jointIntegrable_photon (blockParams P Φ i) hε (atomMass_pos Φ hmass i)
        (atomMass_lt_bigX Φ i) ((atomMass_lt_bigX Φ i).trans (lt_add_one _))
        (blockParams_PV₁ P Φ i) (blockParams_PV₂ P Φ i) hκ C hC h1 k μ ν

end Split

end QED.GradedProof.PhotonSplit

end
