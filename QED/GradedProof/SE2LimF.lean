/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2LimP
public import QED.GradedProof.SE2ClassF

/-!
# The class `F`: the `ε → 0⁺` limit

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 2, step L1. The value of `repF` (a `δ₂`, `δ_m` vertex on the internal
electron line of the one-loop self-energy) converges below the threshold `-(m + min(m_γ, Λ))²`
(`exists_tendsto_contractionValue₂_repF`).

## Proof

By `electronInsertion_decomp` the integrand is
`a Σ_m + c Σ_{-m} - κ D⁻³ (D_γ D_Λ)⁻¹ numSEF_ε`, with `Σ_{±m}` the self-energy integrands of
(62.28) at the masses `±m`.

* `Σ_{-m} = -γ⁵ Σ_m γ⁵` (`selfEnergyIntegrand_neg_mass`), and `γ⁵` is diagonal, so each entry of
  `Σ_{-m}` is `∓` the entry of `Σ_m`, whose limit is `QED.WickModel`'s one-loop limit.
* The numerator `numSEF_ε` is quadratic in `ε`: `numSEF_ε = n₀ + ε n₁ + ε² n₂` with
  `ε`-independent `nₖ` of degree at most four with the auxiliary loop (`numSEF_eq`). Each
  `D⁻³ (D_γ D_Λ)⁻¹ nₖ` converges by `exists_tendsto_of_kinds_se` (kinds `kindsSEF`) and is
  integrable in both stages at `ε > 0`.
* The energy-first integral is linear on integrable integrands, and `ε, ε² → 0`.
-/

@[expose] public section

namespace QED.GradedProof.SE2

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.IntegrableOrderFive
open Complex Filter Topology

/-! ### The self-energy integrand at the mass `-m` -/

theorem electronNumerator_neg_mass (m : ℝ) (k : Fin 4 → ℝ) :
    electronNumerator (-m) k = -(gamma5 * electronNumerator m k * gamma5) := by
  have h : gamma5 * electronNumerator m k * gamma5 = (m : ℂ) • 1 + Dirac.slash k := by
    simp only [electronNumerator, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, gamma5_mul_gamma5, gamma5_conj_slash, sub_neg_eq_add]
  rw [h, electronNumerator]
  push_cast
  module

theorem gamma_conj_gamma5 (ν μ : Fin 4) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    gamma5 * (Dirac.gamma ν * X * Dirac.gamma μ) * gamma5 =
      Dirac.gamma ν * (gamma5 * X * gamma5) * Dirac.gamma μ := by
  rw [gamma5_conj_mul, gamma5_conj_mul, gamma5_conj_gamma, gamma5_conj_gamma]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]

/-- `Σ_{-m} = -γ⁵ Σ_m γ⁵`. -/
theorem selfEnergyIntegrand_neg_mass (Q : Params) (ε : ℝ) (p q : Fin 4 → ℝ) :
    selfEnergyIntegrand { Q with m := -Q.m } ε p q =
      -(gamma5 * selfEnergyIntegrand Q ε p q * gamma5) := by
  simp only [selfEnergyIntegrand, QED.TwoLoop.Bridge.electronPropagator_eq_smul,
    propDenom_neg_mass, electronNumerator_neg_mass, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_neg, Matrix.neg_mul, smul_neg,
    Finset.sum_neg_distrib, gamma_conj_gamma5]

/-- The diagonal of `γ⁵`. -/
def g5 : Fin 4 → ℂ := ![-1, -1, 1, 1]

theorem gamma5_conj_apply (A : Matrix (Fin 4) (Fin 4) ℂ) (α β : Fin 4) :
    (gamma5 * A * gamma5) α β = g5 α * g5 β * A α β := by
  rw [gamma5, Matrix.mul_diagonal, Matrix.diagonal_mul, g5]
  ring

/-! ### The remainder numerator is quadratic in `ε` -/

/-- The coefficient of `ε` in `insR`. -/
noncomputable def insJ (m δ₂ δm : ℝ) (k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (I * δ₂) • electronNumerator m k + (I * m * (δ₂ - δm)) • (1 : Matrix (Fin 4) (Fin 4) ℂ)

theorem insR_eq (m ε δ₂ δm : ℝ) (k : Fin 4 → ℝ) :
    insR m ε δ₂ δm k = insR m 0 δ₂ δm k + (ε : ℂ) • insJ m δ₂ δm k := by
  simp only [insR, insJ]
  push_cast
  module

theorem propDenom_eq_zero_sub (M ε : ℝ) (k : Fin 4 → ℝ) :
    propDenom M ε k = propDenom M 0 k - (ε : ℂ) * I := by
  simp [propDenom]

/-- The three `ε`-independent numerators. -/
noncomputable def numF0 (Q : Params) (p k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  seChain (propDenom Q.m 0 (p + k) • insR Q.m 0 Q.δ₂ Q.δm (p + k)) (pvPhotonNum Q.mγ Q.Λ)

noncomputable def numF1 (Q : Params) (p k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  seChain (propDenom Q.m 0 (p + k) • insJ Q.m Q.δ₂ Q.δm (p + k) -
    I • insR Q.m 0 Q.δ₂ Q.δm (p + k)) (pvPhotonNum Q.mγ Q.Λ)

noncomputable def numF2 (Q : Params) (p k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  seChain ((-I) • insJ Q.m Q.δ₂ Q.δm (p + k)) (pvPhotonNum Q.mγ Q.Λ)

theorem numSEF_eq (Q : Params) (ε : ℝ) (p k : Fin 4 → ℝ) :
    numSEF { Q with ε := ε } p k =
      numF0 Q p k + (ε : ℂ) • numF1 Q p k + ((ε : ℂ) ^ 2) • numF2 Q p k := by
  have hA : propDenom Q.m ε (p + k) • insR Q.m ε Q.δ₂ Q.δm (p + k) =
      propDenom Q.m 0 (p + k) • insR Q.m 0 Q.δ₂ Q.δm (p + k) +
        (ε : ℂ) • (propDenom Q.m 0 (p + k) • insJ Q.m Q.δ₂ Q.δm (p + k) -
          I • insR Q.m 0 Q.δ₂ Q.δm (p + k)) +
        ((ε : ℂ) ^ 2) • ((-I) • insJ Q.m Q.δ₂ Q.δm (p + k)) := by
    rw [propDenom_eq_zero_sub, insR_eq]
    module
  show seChain (propDenom Q.m ε (p + k) • insR Q.m ε Q.δ₂ Q.δm (p + k))
    (pvPhotonNum Q.mγ Q.Λ) = _
  rw [hA, seChain_add_in, seChain_add_in, seChain_smul_in (ε : ℂ),
    seChain_smul_in ((ε : ℂ) ^ 2)]
  rfl

theorem isLoopPolyMat_insJ (m δ₂ δm : ℝ) (p : Fin 4 → ℝ) :
    IsLoopPolyMat 2 1 fun ℓ => insJ m δ₂ δm (p + ℓ 0) :=
  isLoopPolyMat_add (isLoopPolyMat_smul _ (isLoopPolyMat_electronNumerator_add m p))
    (isLoopPolyMat_mono (isLoopPolyMat_smul _
      (IsLoopPolyMat.const (1 : Matrix (Fin 4) (Fin 4) ℂ))) (Nat.zero_le _))

theorem isLoopPolyMat_propDenom_smul (m : ℝ) (p : Fin 4 → ℝ)
    {X : (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ} (hX : IsLoopPolyMat 2 1 X) :
    IsLoopPolyMat 2 3 fun ℓ => propDenom m 0 (p + ℓ 0) • X ℓ := fun a b => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact ((isLoopAffine_add_zero p).isLoopPoly_propDenom m 0).mul (hX a b)

theorem isLoopPoly_seChain_pv (mγ Λ : ℝ) {X : (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    (hX : IsLoopPolyMat 2 3 X) (i j : Fin 4) :
    IsLoopPoly 2 4 fun ℓ => seChain (X ℓ) (pvPhotonNum mγ Λ) i j :=
  ((isLoopPolyMat_seChain (d := 0) hX (fun ν ρ => IsLoopPoly.const (pvPhotonNum mγ Λ ν ρ)))
    i j).mono (by norm_num)

theorem isLoopPoly_numF (Q : Params) (p : Fin 4 → ℝ) (i j : Fin 4) :
    IsLoopPoly 2 4 (fun ℓ => numF0 Q p (ℓ 0) i j) ∧
      IsLoopPoly 2 4 (fun ℓ => numF1 Q p (ℓ 0) i j) ∧
      IsLoopPoly 2 4 (fun ℓ => numF2 Q p (ℓ 0) i j) := by
  have hR := isLoopPolyMat_insR Q.m 0 Q.δ₂ Q.δm p
  have hJ := isLoopPolyMat_insJ Q.m Q.δ₂ Q.δm p
  refine ⟨isLoopPoly_seChain_pv _ _ (isLoopPolyMat_propDenom_smul Q.m p hR) i j,
    isLoopPoly_seChain_pv _ _ ?_ i j,
    isLoopPoly_seChain_pv _ _ (isLoopPolyMat_mono (isLoopPolyMat_smul _ hJ) (by norm_num)) i j⟩
  have h := isLoopPolyMat_add (isLoopPolyMat_propDenom_smul Q.m p hJ)
    (isLoopPolyMat_mono (isLoopPolyMat_smul (-I) hR) (by norm_num))
  refine fun a b => (congrArg (IsLoopPoly 2 3) (funext fun ℓ => ?_)).mp (h a b)
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-! ### The pieces of the remainder -/

/-- The denominators of the remainder. -/
noncomputable def prefF (Q : Params) (ε : ℝ) (p k : Fin 4 → ℝ) : ℂ :=
  (propDenom Q.m ε (p + k))⁻¹ * (propDenom Q.m ε (p + k))⁻¹ * (propDenom Q.m ε (p + k))⁻¹ *
    ((propDenom Q.mγ ε k)⁻¹ * (propDenom Q.Λ ε k)⁻¹)

theorem massesSEF_bounds (Q : Params) (hmγ : 0 < Q.mγ) (hΛ : 0 < Q.Λ) :
    (∀ i, kindsSEF i ≠ .pho → Q.m ^ 2 ≤ massesSEF Q i ^ 2) ∧
      (∀ i, kindsSEF i = .pho → min Q.mγ Q.Λ ^ 2 ≤ massesSEF Q i ^ 2) := by
  obtain ⟨h1, h2⟩ := sq_min_le Q hmγ hΛ
  constructor <;> intro i hi <;> fin_cases i <;> simp_all [kindsSEF, massesSEF]

theorem hfac_F (Q : Params) (p : Fin 4 → ℝ) (n : (Fin 4 → ℝ) → ℂ) (ε : ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    n (ℓ 0) * ∏ i, (propDenom (massesSEF Q i) ε ((kindsSEF i).lineMom p p ℓ))⁻¹ =
      prefF Q ε p (ℓ 0) * n (ℓ 0) * ((propDenom Q.m ε (ℓ 1))⁻¹) ^ 3 := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsSEF, massesSEF, prefF,
    LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

theorem piece_F (Q : Params) (hm : 0 < Q.m) (hmγ : 0 < Q.mγ) (hΛ : 0 < Q.Λ) {p : Fin 4 → ℝ}
    (hs : -(Q.m + min Q.mγ Q.Λ) ^ 2 < Minkowski.dot p p) (n : (Fin 4 → ℝ) → ℂ)
    (hn : IsLoopPoly 2 4 fun ℓ => n (ℓ 0)) :
    (∀ ε : ℝ, 0 < ε → IntegrableEnergyFirst fun q => prefF Q ε p q * n q) ∧
      ∃ L : ℂ, Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun q => prefF Q ε p q * n q)
        (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨hMe, hMp⟩ := massesSEF_bounds Q hmγ hΛ
  refine ⟨fun ε hε => ?_, exists_tendsto_of_kinds_se (by norm_num) kindsSEF (by decide)
    (massesSEF Q) hm hm (lt_min hmγ hΛ) p hs hMe hMp (by decide) (by decide) (by decide) n hn
    (fun ε q => prefF Q ε p q * n q) fun ε _ ℓ => hfac_F Q p n ε ℓ⟩
  obtain ⟨h1, h2⟩ := energyFirst_of_kinds (by norm_num) kindsSEF (massesSEF Q) Q.m hε p p
    (by decide) (by decide) (by decide) n hn (fun q => prefF Q ε p q * n q)
    (fun ℓ => hfac_F Q p n ε ℓ)
  exact ⟨h1, h2⟩

/-! ### The class `F` -/

/-- The integrand of `repF` as five pieces. -/
theorem integrand_F_eq (Q : Params) {ε : ℝ} (hε : 0 < ε) (p q : Fin 4 → ℝ) (α β : Fin 4) :
    kappaSE Q.e * seChain (electronInsertion Q.m ε Q.δ₂ Q.δm (p + q))
        (QED.OneLoop.photonPropagator Q.mγ Q.Λ ε q) α β =
      (-(Q.δ₂ : ℂ) - (((Q.δ₂ - Q.δm) / 2 : ℝ) : ℂ) +
          (((Q.δ₂ - Q.δm) / 2 : ℝ) : ℂ) * (-(g5 α * g5 β))) *
          selfEnergyIntegrand Q ε p q α β +
        (-kappaSE Q.e) * (prefF Q ε p q * numF0 Q p q α β) +
        (-kappaSE Q.e * ε) * (prefF Q ε p q * numF1 Q p q α β) +
        (-kappaSE Q.e * ε ^ 2) * (prefF Q ε p q * numF2 Q p q α β) := by
  have hR := integrand_seF_eq { Q with ε := ε } hε.ne' p q
  rw [numSEF_eq] at hR
  dsimp only at hR
  have hS' := congrArg (fun A => A α β) (selfEnergyIntegrand_neg_mass Q ε p q)
  simp only [Matrix.neg_apply, gamma5_conj_apply] at hS'
  have e1 := selfEnergyIntegrand_eq_seChain Q ε p q
  have e2 := selfEnergyIntegrand_eq_seChain { Q with m := -Q.m } ε p q
  dsimp only at e2
  have a1 := congrArg (fun A => A α β) e1
  have a2 := congrArg (fun A => A α β) e2
  have a3 := congrArg (fun A => A α β) hR
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply] at a1 a2 a3
  rw [electronInsertion_decomp _ _ _ _ hε.ne', seChain_sub_in, seChain_sub_in, seChain_smul_in,
    seChain_smul_in, seChain_sub_in]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  have hk : kappaSE Q.e = (I * Q.e) ^ 2 * (1 / I) ^ 2 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ := rfl
  have hp : prefF Q ε p q = (propDenom Q.m ε (p + q))⁻¹ * (propDenom Q.m ε (p + q))⁻¹ *
      (propDenom Q.m ε (p + q))⁻¹ * ((propDenom Q.mγ ε q)⁻¹ * (propDenom Q.Λ ε q)⁻¹) := rfl
  rw [hp, hk]
  linear_combination ((Q.δ₂ : ℂ) + (((Q.δ₂ - Q.δm) / 2 : ℝ) : ℂ)) * a1 -
    (((Q.δ₂ - Q.δm) / 2 : ℝ) : ℂ) * a2 + (((Q.δ₂ - Q.δm) / 2 : ℝ) : ℂ) * hS' -
    ((I * Q.e) ^ 2 * (1 / I) ^ 2 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹) * a3

/-- Linearity of the energy-first integral on four integrable pieces. -/
theorem energyFirstIntegral_lin4 {f₀ f₁ f₂ f₃ : (Fin 4 → ℝ) → ℂ} (h₀ : IntegrableEnergyFirst f₀)
    (h₁ : IntegrableEnergyFirst f₁) (h₂ : IntegrableEnergyFirst f₂)
    (h₃ : IntegrableEnergyFirst f₃) (c₀ c₁ c₂ c₃ : ℂ) :
    QED.OneLoop.energyFirstIntegral (fun q => c₀ * f₀ q + c₁ * f₁ q + c₂ * f₂ q + c₃ * f₃ q) =
      c₀ * QED.OneLoop.energyFirstIntegral f₀ + c₁ * QED.OneLoop.energyFirstIntegral f₁ +
        c₂ * QED.OneLoop.energyFirstIntegral f₂ + c₃ * QED.OneLoop.energyFirstIntegral f₃ := by
  have g₀ := h₀.const_mul c₀
  have g₁ := h₁.const_mul c₁
  have g₂ := h₂.const_mul c₂
  have g₃ := h₃.const_mul c₃
  have g₀₁ := IntegrableEnergyFirst.add g₀ g₁
  have g₀₁₂ := IntegrableEnergyFirst.add g₀₁ g₂
  rw [energyFirstIntegral_add ⟨g₀₁₂.1, g₀₁₂.2⟩ ⟨g₃.1, g₃.2⟩,
    energyFirstIntegral_add ⟨g₀₁.1, g₀₁.2⟩ ⟨g₂.1, g₂.2⟩,
    energyFirstIntegral_add ⟨g₀.1, g₀.2⟩ ⟨g₁.1, g₁.2⟩,
    QED.OneLoop.energyFirstIntegral_const_mul, QED.OneLoop.energyFirstIntegral_const_mul,
    QED.OneLoop.energyFirstIntegral_const_mul, QED.OneLoop.energyFirstIntegral_const_mul]

theorem tendsto_ofReal_mul_nhdsWithin (c : ℂ) (n : ℕ) :
    Tendsto (fun ε : ℝ => c * (ε : ℂ) ^ n) (𝓝[>] 0) (𝓝 (c * ((0 : ℝ) : ℂ) ^ n)) :=
  ((continuous_const.mul (Complex.continuous_ofReal.pow n)).tendsto 0).mono_left
    nhdsWithin_le_nhds

/-- **The limit of the class `F`** exists below threshold. -/
theorem exists_tendsto_contractionValue₂_repF {Q : Params} (hm : 0 < Q.m) (hmγ : 0 < Q.mγ)
    (hΛ : 0 < Q.Λ) {p : Fin 4 → ℝ} (hs : -(Q.m + min Q.mγ Q.Λ) ^ 2 < Minkowski.dot p p)
    (α β : Fin 4) :
    ∃ L : ℂ, Tendsto (fun ε : ℝ =>
      contractionValue₂ { Q with ε := ε } repF ![p] ![p] ![] ![α] ![β] ![]) (𝓝[>] 0) (𝓝 L) := by
  have hmin := lt_min hmγ hΛ
  have hpγ : -(Q.m + Q.mγ) ^ 2 < Minkowski.dot p p :=
    lt_of_le_of_lt (neg_le_neg (pow_le_pow_left₀ (by positivity)
      (add_le_add_right (min_le_left Q.mγ Q.Λ) Q.m) 2)) hs
  have hpΛ : -(Q.m + Q.Λ) ^ 2 < Minkowski.dot p p :=
    lt_of_le_of_lt (neg_le_neg (pow_le_pow_left₀ (by positivity)
      (add_le_add_right (min_le_right Q.mγ Q.Λ) Q.m) 2)) hs
  have hSE := tendsto_energyFirstIntegral_selfEnergyIntegrand hm hmγ hΛ hpγ hpΛ α β
  obtain ⟨hn0, hn1, hn2⟩ := isLoopPoly_numF Q p α β
  obtain ⟨i0, L0, t0⟩ := piece_F Q hm hmγ hΛ hs (fun q => numF0 Q p q α β) hn0
  obtain ⟨i1, L1, t1⟩ := piece_F Q hm hmγ hΛ hs (fun q => numF1 Q p q α β) hn1
  obtain ⟨i2, L2, t2⟩ := piece_F Q hm hmγ hΛ hs (fun q => numF2 Q p q α β) hn2
  set a : ℂ := -(Q.δ₂ : ℂ) - (((Q.δ₂ - Q.δm) / 2 : ℝ) : ℂ) +
    (((Q.δ₂ - Q.δm) / 2 : ℝ) : ℂ) * (-(g5 α * g5 β))
  set κ := kappaSE Q.e
  have hlim := (((tendsto_const_nhds (x := a)).mul hSE).add
    ((tendsto_const_nhds (x := -κ)).mul t0)).add
      (((tendsto_ofReal_mul_nhdsWithin (-κ) 1).mul t1).add
        ((tendsto_ofReal_mul_nhdsWithin (-κ) 2).mul t2))
  refine ⟨_, hlim.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [contractionValue₂_of_one_chord _ f_isChord_iff (fMom p) (f_isConserved p)
    (fun ℓ => (fMom_apply p ℓ).1) ![α] ![β] ![]
    (fun q => kappaSE Q.e * seChain (electronInsertion Q.m ε Q.δ₂ Q.δm (p + q))
      (QED.OneLoop.photonPropagator Q.mγ Q.Λ ε q) α β) p
    (fun ℓ => f_integrand { Q with ε := ε } p ℓ α β)]
  have hfun : (fun q => kappaSE Q.e * seChain (electronInsertion Q.m ε Q.δ₂ Q.δm (p + q))
        (QED.OneLoop.photonPropagator Q.mγ Q.Λ ε q) α β) =
      fun q => a * selfEnergyIntegrand Q ε p q α β + (-κ) * (prefF Q ε p q * numF0 Q p q α β) +
        (-κ * ε) * (prefF Q ε p q * numF1 Q p q α β) +
        (-κ * ε ^ 2) * (prefF Q ε p q * numF2 Q p q α β) := by
    funext q
    exact integrand_F_eq Q hε p q α β
  rw [hfun, energyFirstIntegral_lin4 (integrableEnergyFirst_selfEnergyIntegrand Q hε p α β)
    (i0 ε hε) (i1 ε hε) (i2 ε hε)]
  simp only [pow_one]
  ring

end QED.GradedProof.SE2

end
