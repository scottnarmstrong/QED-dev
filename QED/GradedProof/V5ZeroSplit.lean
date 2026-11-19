/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.LeptonProof.HMSplit

/-!
# The general-flavour order-`e⁵` vertex through T1 parameter sets: the parameter sets

Helper level for the Phase 5 Stage 2 goal (G-ex₂), the `V5Zero` effort. For flavour data `Φ`
(masses `M_g`, loop coefficients `a_g`, open line of mass `m`) with the total Pauli–Villars
conditions `∑ a_g = 0`, `∑ a_g M_g² = 0`, and an auxiliary mass `X` with `X² ≠ m²`,
`M_g² ≠ X²`, the T1 parameter sets are

* `zParams Q X`: regulators `(m, X)`, coefficients `(-1, 0)`; its loop measure `δ_m - δ_m` is `0`;
* `gParams Q Φ X g`: regulators `(M_g, X)`, coefficients fixed by T1's two Pauli–Villars
  conditions at `m = Q.m`;

with the weights `weight Q Φ X g = a_g (M_g² - X²)/(X² - m²)`. The weights sum to `0`
(`sum_weight`) and the signed sum of the loop measures is `Φ`'s (`loop_split`). The amplitude of
every simple contraction splits accordingly (`regulatedAmplitude₂_split`).
-/

@[expose] public section

open Complex Finset
open QED.WickModel (Params Contraction)
open QED.Lepton.Proof.HM (t1F auxC₁ IsSimple HasLoop loopAmp t1F_mass_openLine
  regulatedAmplitude₂_of_hasLoop regulatedAmplitude₂_of_not_hasLoop)

namespace QED.GradedProof.V5Zero.Split

variable {F : Type}

/-! ### The parameter sets and weights -/

/-- **The no-loop parameter set**: regulators `(m, X)`, coefficients `(-1, 0)`. -/
def zParams (Q : Params) (X : ℝ) : Params :=
  { Q with M₁ := Q.m, M₂ := X, c₁ := -1, c₂ := 0 }

/-- **The parameter set of the flavour `g`**: regulators `(M_g, X)`, coefficients fixed by T1's
two Pauli–Villars conditions at `m = Q.m`. -/
noncomputable def gParams (Q : Params) (Φ : Lepton.Flavors F) (X : ℝ) (g : F) : Params :=
  { Q with
    M₁ := Φ.mass g, M₂ := X, c₁ := auxC₁ Q.m X (Φ.mass g), c₂ := -1 - auxC₁ Q.m X (Φ.mass g) }

/-- **The weight of the flavour `g`**: `a_g (M_g² - X²)/(X² - m²)`. -/
noncomputable def weight (Q : Params) (Φ : Lepton.Flavors F) (X : ℝ) (g : F) : ℝ :=
  Φ.coeff g * (Φ.mass g ^ 2 - X ^ 2) / (X ^ 2 - Q.m ^ 2)

/-! ### Field lemmas -/

section Fields

variable (Q : Params) (Φ : Lepton.Flavors F) (X : ℝ) (g : F)

@[simp] theorem zParams_e : (zParams Q X).e = Q.e := rfl
@[simp] theorem zParams_δ₁ : (zParams Q X).δ₁ = Q.δ₁ := rfl
@[simp] theorem zParams_δ₂ : (zParams Q X).δ₂ = Q.δ₂ := rfl
@[simp] theorem zParams_δm : (zParams Q X).δm = Q.δm := rfl
@[simp] theorem zParams_δ₃ : (zParams Q X).δ₃ = Q.δ₃ := rfl
@[simp] theorem zParams_m : (zParams Q X).m = Q.m := rfl
@[simp] theorem zParams_mγ : (zParams Q X).mγ = Q.mγ := rfl
@[simp] theorem zParams_Λ : (zParams Q X).Λ = Q.Λ := rfl
@[simp] theorem zParams_ε : (zParams Q X).ε = Q.ε := rfl
@[simp] theorem zParams_M₁ : (zParams Q X).M₁ = Q.m := rfl
@[simp] theorem zParams_M₂ : (zParams Q X).M₂ = X := rfl
@[simp] theorem zParams_c₁ : (zParams Q X).c₁ = -1 := rfl
@[simp] theorem zParams_c₂ : (zParams Q X).c₂ = 0 := rfl

@[simp] theorem gParams_e : (gParams Q Φ X g).e = Q.e := rfl
@[simp] theorem gParams_δ₁ : (gParams Q Φ X g).δ₁ = Q.δ₁ := rfl
@[simp] theorem gParams_δ₂ : (gParams Q Φ X g).δ₂ = Q.δ₂ := rfl
@[simp] theorem gParams_δm : (gParams Q Φ X g).δm = Q.δm := rfl
@[simp] theorem gParams_δ₃ : (gParams Q Φ X g).δ₃ = Q.δ₃ := rfl
@[simp] theorem gParams_m : (gParams Q Φ X g).m = Q.m := rfl
@[simp] theorem gParams_mγ : (gParams Q Φ X g).mγ = Q.mγ := rfl
@[simp] theorem gParams_Λ : (gParams Q Φ X g).Λ = Q.Λ := rfl
@[simp] theorem gParams_ε : (gParams Q Φ X g).ε = Q.ε := rfl
@[simp] theorem gParams_M₁ : (gParams Q Φ X g).M₁ = Φ.mass g := rfl
@[simp] theorem gParams_M₂ : (gParams Q Φ X g).M₂ = X := rfl

theorem zParams_with_ε (ε : ℝ) : zParams { Q with ε := ε } X = { zParams Q X with ε := ε } :=
  rfl

theorem gParams_with_ε (ε : ℝ) :
    gParams { Q with ε := ε } Φ X g = { gParams Q Φ X g with ε := ε } := rfl

theorem weight_with_ε (ε : ℝ) : weight { Q with ε := ε } Φ X g = weight Q Φ X g := rfl

/-- **T1's first Pauli–Villars condition for `zParams`.** -/
theorem zParams_PV₁ : 1 + (zParams Q X).c₁ + (zParams Q X).c₂ = 0 := by
  simp [zParams]

/-- **T1's second Pauli–Villars condition for `zParams`.** -/
theorem zParams_PV₂ :
    (zParams Q X).m ^ 2 + (zParams Q X).c₁ * (zParams Q X).M₁ ^ 2 +
      (zParams Q X).c₂ * (zParams Q X).M₂ ^ 2 = 0 := by
  simp [zParams]

/-- **T1's first Pauli–Villars condition for `gParams`.** -/
theorem gParams_PV₁ : 1 + (gParams Q Φ X g).c₁ + (gParams Q Φ X g).c₂ = 0 := by
  simp only [gParams]
  ring

/-- **T1's second Pauli–Villars condition for `gParams`** (when `M_g² ≠ X²`). -/
theorem gParams_PV₂ (hX : Φ.mass g ^ 2 ≠ X ^ 2) :
    (gParams Q Φ X g).m ^ 2 + (gParams Q Φ X g).c₁ * (gParams Q Φ X g).M₁ ^ 2 +
      (gParams Q Φ X g).c₂ * (gParams Q Φ X g).M₂ ^ 2 = 0 := by
  simp only [gParams, auxC₁]
  have : Φ.mass g ^ 2 - X ^ 2 ≠ 0 := sub_ne_zero.mpr hX
  field_simp
  ring

end Fields

/-- **A choice of the auxiliary mass**: `X = 1 + |m| + ∑_g |M_g|` exceeds `m`, `|m|` and every
`M_g`, `|M_g|`, so `X > 0`, `X² ≠ m²` and `M_g² ≠ X²`. -/
theorem exists_aux [Fintype F] (m : ℝ) (M : F → ℝ) :
    ∃ X : ℝ, 0 < X ∧ m < X ∧ |m| < X ∧ (∀ g, M g < X) ∧ (∀ g, |M g| < X) ∧
      X ^ 2 ≠ m ^ 2 ∧ ∀ g, M g ^ 2 ≠ X ^ 2 := by
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ g', |M g'| := ⟨_, rfl⟩
  have hs : ∀ g, |M g| ≤ S := fun g => hS ▸
    single_le_sum (f := fun g' => |M g'|) (fun _ _ => abs_nonneg _) (mem_univ g)
  have h0 : 0 ≤ S := hS ▸ sum_nonneg fun _ _ => abs_nonneg _
  have ha := abs_nonneg m
  have hpos : 0 < 1 + |m| + S := by linarith
  have hm : |m| < 1 + |m| + S := by linarith
  have hM : ∀ g, |M g| < 1 + |m| + S := fun g => by linarith [hs g]
  have habs : |1 + |m| + S| = 1 + |m| + S := abs_of_pos hpos
  refine ⟨1 + |m| + S, hpos, lt_of_le_of_lt (le_abs_self m) hm, hm,
    fun g => lt_of_le_of_lt (le_abs_self _) (hM g), hM, ?_, fun g => ?_⟩
  · exact (ne_of_lt (sq_lt_sq.mpr (by rwa [habs]))).symm
  · exact ne_of_lt (sq_lt_sq.mpr (by rw [habs]; exact hM g))

/-! ### The weights -/

variable {Q : Params} {Φ : Lepton.Flavors F} {X : ℝ}

/-- **The weights sum to `0`** under the total Pauli–Villars conditions. -/
theorem sum_weight [Fintype F] (h₁ : ∑ g, Φ.coeff g = 0) (h₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) :
    ∑ g, weight Q Φ X g = 0 := by
  have e : ∑ g, weight Q Φ X g =
      (∑ g, Φ.coeff g * Φ.mass g ^ 2 - X ^ 2 * ∑ g, Φ.coeff g) / (X ^ 2 - Q.m ^ 2) := by
    simp only [weight, ← sum_div, mul_sum, ← sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun g _ => ?_
    ring
  rw [e, h₁, h₂]
  simp

theorem weight_mul_auxC₁ (hXm : X ^ 2 ≠ Q.m ^ 2) (hX : ∀ g, Φ.mass g ^ 2 ≠ X ^ 2) (g : F) :
    weight Q Φ X g * auxC₁ Q.m X (Φ.mass g) = Φ.coeff g := by
  have h1 : X ^ 2 - Q.m ^ 2 ≠ 0 := sub_ne_zero.mpr hXm
  have h2 : Φ.mass g ^ 2 - X ^ 2 ≠ 0 := sub_ne_zero.mpr (hX g)
  simp only [weight, auxC₁]
  field_simp

/-- **The loop measures**: for every `G`,
`∑_i c^Z_i G(M^Z_i) + ∑_g w_g ∑_i c^{(g)}_i G(M^{(g)}_i) = ∑_g a_g G(M_g)`. -/
theorem loop_split [Fintype F] {M : Type*} [AddCommGroup M] [Module ℝ M] (h₁ : ∑ g, Φ.coeff g = 0)
    (h₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) (hXm : X ^ 2 ≠ Q.m ^ 2)
    (hX : ∀ g, Φ.mass g ^ 2 ≠ X ^ 2) (G : ℝ → M) :
    ∑ i, (zParams Q X).loopCoeff i • G ((zParams Q X).mass i) +
        ∑ g, weight Q Φ X g • ∑ i, (gParams Q Φ X g).loopCoeff i • G ((gParams Q Φ X g).mass i) =
      ∑ g, Φ.coeff g • G (Φ.mass g) := by
  have hw := weight_mul_auxC₁ hXm hX
  have hz : ∑ i, (zParams Q X).loopCoeff i • G ((zParams Q X).mass i) = 0 := by
    simp [Fin.sum_univ_three, Params.loopCoeff, Params.mass, zParams]
  have e : ∀ g, weight Q Φ X g • ∑ i, (gParams Q Φ X g).loopCoeff i •
      G ((gParams Q Φ X g).mass i) =
      weight Q Φ X g • G Q.m + Φ.coeff g • G (Φ.mass g) +
        (-weight Q Φ X g - Φ.coeff g) • G X := by
    intro g
    simp only [Fin.sum_univ_three, Params.loopCoeff, Params.mass, gParams,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_smul, smul_add, smul_smul, hw]
    rw [show weight Q Φ X g * (-1 - auxC₁ Q.m X (Φ.mass g)) =
      -weight Q Φ X g - Φ.coeff g by rw [← hw g]; ring]
  simp only [hz, zero_add, e, sum_add_distrib, ← sum_smul, sum_weight h₁ h₂, zero_smul,
    sum_sub_distrib, sum_neg_distrib, h₁, neg_zero, sub_zero, add_zero]

/-! ### The amplitude of a simple contraction -/

/-- **The regulated amplitude of a simple contraction splits** into the T1 amplitudes at
`zParams` and the `gParams g`. -/
theorem regulatedAmplitude₂_split [Fintype F] [DecidableEq F] (hm : Q.m = Φ.mass Φ.openLine)
    (h₁ : ∑ g, Φ.coeff g = 0) (h₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) (hXm : X ^ 2 ≠ Q.m ^ 2)
    (hX : ∀ g, Φ.mass g ^ 2 ≠ X ^ 2)
    {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ} (hS : IsSimple C)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : QED.WickModel.Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    Lepton.regulatedAmplitude₂ Q Φ C pIn kIn k αOut βIn μ =
      Lepton.regulatedAmplitude₂ (zParams Q X) (t1F (zParams Q X)) C pIn kIn k αOut βIn μ +
        ∑ g, (weight Q Φ X g : ℂ) *
          Lepton.regulatedAmplitude₂ (gParams Q Φ X g) (t1F (gParams Q Φ X g)) C
            pIn kIn k αOut βIn μ := by
  have hZ : loopAmp (zParams Q X) hS = loopAmp Q hS := rfl
  have hG : ∀ g, loopAmp (gParams Q Φ X g) hS = loopAmp Q hS := fun _ => rfl
  by_cases hL : HasLoop C
  · simp only [regulatedAmplitude₂_of_hasLoop _ _ hS hL, t1F_mass_openLine, hZ, hG, ← hm,
      zParams_m, gParams_m]
    set G : ℝ → ℂ := fun b => loopAmp Q hS Q.m b pIn kIn k αOut βIn μ with hGdef
    have e2 : ∀ P : Params, ∑ f, ((t1F P).coeff f : ℂ) * G ((t1F P).mass f) =
        ∑ i, P.loopCoeff i • G (P.mass i) := fun P => by
      simp only [Complex.real_smul]
      rfl
    have e1 : ∑ f, (Φ.coeff f : ℂ) * G (Φ.mass f) = ∑ f, Φ.coeff f • G (Φ.mass f) := by
      simp only [Complex.real_smul]
    rw [e1, e2, ← loop_split h₁ h₂ hXm hX G]
    congr 1
  · simp only [regulatedAmplitude₂_of_not_hasLoop _ _ hS hL, t1F_mass_openLine, hZ, hG, ← hm,
      zParams_m, gParams_m, ← sum_mul]
    have : ∑ g, (weight Q Φ X g : ℂ) = 0 := by exact_mod_cast sum_weight h₁ h₂
    simp [this]

end QED.GradedProof.V5Zero.Split

end
