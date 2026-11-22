/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKBPiece
public import QED.ChainProof.SetAKSKBTrace
public import QED.TwoLoop.ParamNumEvalChain

/-!
# Set (a), stage B2: a chain quartic of the `(2, 3)` entry with vanishing quartic contraction

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage B2. The merge of a
doubled line (`ksB_pieceA_merge`, `ksB_pieceB_merge`) needs a quartic `Q` representing the
numerator with `Q.contractFour A = 0` for **every** matrix `A`. The entry `(2, 3)` of a class
numerator is a photon sum of traces of eight gamma matrices in which the index `2` occurs an odd
number of times, so conjugation by `γ²` reverses its sign:

* `KsFlip`, `ksFlip_mul`, `ksFlip_gamma`, `ksFlip_gammaLower`, `ksFlip_trace`: `γ² X = s X γ²`
  is multiplicative, `s = ±1` on `γ^μ`, `γ_μ`, and `s = -1` forces `tr X = 0`;
* `ksBRep`, `ksBRep_eval`: the chain quartic (`QED.TwoLoop.ParamNumEval.chainQuartic`) of the
  `(2, 3)` entry of `vNum e 0 1`;
* **`ksBRep_contractFour`**: its quartic contraction vanishes for every `A`;
* **`ksB_vNumE4_eq_zero`**: the `m⁴` coefficient of the `(2, 3)` entry vanishes;
* `ksB_flip_VA`, `ksB_flip_VB`, `ksB_flip_VC`: the hypothesis for the three classes.
-/

@[expose] public section

open Complex Matrix

namespace QED.ChainProof.SetAKS

open QED.Integration.TwoLoop QED.TwoLoop.ParamNumEval QED.GradedProof.VP2 QED.GradedProof.RPi4
open QED.Dirac QED.TwoLoop.LimitCovariance

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-! ### The reflection of the second axis -/

/-- `γ² X = s (X γ²)`: conjugation by `γ²` multiplies `X` by `s`. -/
def KsFlip (X : Mat) (s : ℂ) : Prop := gamma 2 * X = s • (X * gamma 2)

theorem ksFlip_mul {X Y : Mat} {a b : ℂ} (hX : KsFlip X a) (hY : KsFlip Y b) :
    KsFlip (X * Y) (a * b) := by
  unfold KsFlip at *
  rw [← Matrix.mul_assoc, hX, Matrix.smul_mul, Matrix.mul_assoc, hY, Matrix.mul_smul, smul_smul,
    ← Matrix.mul_assoc]

theorem ksFlip_smul {X : Mat} {s : ℂ} (c : ℂ) (h : KsFlip X s) : KsFlip (c • X) s := by
  unfold KsFlip at *
  rw [Matrix.mul_smul, h, Matrix.smul_mul, smul_comm]

/-- The sign of `γ^μ` under conjugation by `γ²`. -/
noncomputable def ksSgn (μ : Fin 4) : ℂ := if μ = 2 then 1 else -1

theorem ksSgn_mul_self (μ : Fin 4) : ksSgn μ * ksSgn μ = 1 := by
  unfold ksSgn; split_ifs <;> norm_num

theorem ksFlip_gamma (μ : Fin 4) : KsFlip (gamma μ) (ksSgn μ) := by
  have h := gamma_anticomm 2 μ
  unfold KsFlip ksSgn
  fin_cases μ
  · simp [Minkowski.metric] at h ⊢
    exact eq_neg_of_add_eq_zero_left h
  · simp [Minkowski.metric] at h ⊢
    exact eq_neg_of_add_eq_zero_left h
  · simp
  · simp [Minkowski.metric] at h ⊢
    exact eq_neg_of_add_eq_zero_left h

theorem ksFlip_gammaLower (μ : Fin 4) : KsFlip (gammaLower μ) (ksSgn μ) := by
  rw [faceId_gammaLower_eq_smul]
  exact ksFlip_smul _ (ksFlip_gamma μ)

theorem ksB_gamma_two_sq : gamma 2 * gamma 2 = -(1 : Mat) := by
  have h := gamma_anticomm 2 2
  have h2 : (2 : ℂ) • (gamma 2 * gamma 2) = (2 : ℂ) • (-(1 : Mat)) := by
    rw [two_smul, h]
    simp [Minkowski.metric]
  exact smul_right_injective _ two_ne_zero h2

theorem ksFlip_trace {X : Mat} (h : KsFlip X (-1)) : X.trace = 0 := by
  unfold KsFlip at h
  have e1 : (gamma 2 * X * gamma 2).trace = -X.trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ksB_gamma_two_sq]
    simp
  have e2 : gamma 2 * X * gamma 2 = X := by
    rw [h, Matrix.smul_mul, Matrix.mul_assoc, ksB_gamma_two_sq]
    simp
  rw [e2] at e1
  linear_combination e1 / 2

theorem ksB_ch_zero {B Y : Fin 4 → Mat} {s t : Fin 4 → ℂ} (hB : ∀ l, KsFlip (B l) (s l))
    (hs : s 0 * s 1 * s 2 * s 3 = -1) (hY : ∀ l, KsFlip (Y l) (t l))
    (ht : t 0 * t 1 * t 2 * t 3 = 1) : ch B (Y 0) (Y 1) (Y 2) (Y 3) = 0 := by
  unfold ch
  apply ksFlip_trace
  have h := ksFlip_mul (ksFlip_mul (ksFlip_mul (ksFlip_mul (ksFlip_mul (ksFlip_mul
    (ksFlip_mul (hB 0) (hY 0)) (hB 1)) (hY 1)) (hB 2)) (hY 2)) (hB 3)) (hY 3)
  have e : s 0 * t 0 * s 1 * t 1 * s 2 * t 2 * s 3 * t 3 = -1 := by
    linear_combination (t 0 * t 1 * t 2 * t 3) * hs - ht
  rwa [e] at h

/-! ### The chain representative of an entry of a class numerator -/

section Rep

variable (e : ℝ) (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Mat) (base : Fin 5 → Fin 2 → ℤ)
  (c : Fin 5 → ℝ)

/-- **The chain quartic of the `(2, 3)` entry** of the class numerator `vNum e 0 1` at the fermion
mass `m`: the photon sum of the chain quartics of the four electron numerators. -/
noncomputable def ksBRep (m : ℝ) (k : Fin 4 → ℝ) : LoopQuartic :=
  qsum Finset.univ (fun p : Fin 4 × Fin 4 => kV e 0 1 p.1 p.2) fun p =>
    chainQuartic (A 2 3 p.1 p.2) (elecAt (castLoopMatrix base) (ppc c k) (fun _ => m)
      Fin.castSucc 0) (fun j => elecLin (castLoopMatrix base) (Fin.castSucc j))

theorem ksBRep_eval (m : ℝ) (k : Fin 4 → ℝ) :
    (ksBRep e A base c m k).eval = fun ℓ => vNum e 0 1 A base c m k ℓ 2 3 := by
  funext ℓ
  rw [ksBRep, eval_qsum]
  simp only [eval_chainQuartic_elec, zero_add]
  rw [vNum, ← Finset.univ_product_univ, Finset.sum_product]
  rfl

/-- **The quartic contraction of the chain representative vanishes**, for every matrix `A'`,
when the diagonal photon vertices of the `(2, 3)` entry flip sign under `γ²`. -/
theorem ksBRep_contractFour
    (hA : ∀ σ, ∃ s : Fin 4 → ℂ, (∀ l, KsFlip (A 2 3 σ σ l) (s l)) ∧ s 0 * s 1 * s 2 * s 3 = -1)
    (m : ℝ) (k : Fin 4 → ℝ) (A' : Matrix (Fin 2) (Fin 2) ℝ) :
    (ksBRep e A base c m k).contractFour A' = 0 := by
  rw [ksBRep, contractFour_qsum]
  simp only [contractFour_chainQuartic]
  rw [← Finset.univ_product_univ, Finset.sum_product, faceId_sum_kV]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun σ _ => ?_)
  obtain ⟨s, hs, hs1⟩ := hA σ
  have h1 : ∀ ν ρ, ch (A 2 3 σ σ) (gammaLower ν) (gamma ν) (gammaLower ρ) (gamma ρ) = 0 :=
    fun ν ρ => ksB_ch_zero (Y := ![gammaLower ν, gamma ν, gammaLower ρ, gamma ρ])
      (t := ![ksSgn ν, ksSgn ν, ksSgn ρ, ksSgn ρ]) hs hs1
      (fun l => by fin_cases l
                   exacts [ksFlip_gammaLower ν, ksFlip_gamma ν, ksFlip_gammaLower ρ,
                     ksFlip_gamma ρ])
      (show ksSgn ν * ksSgn ν * ksSgn ρ * ksSgn ρ = 1 by
        linear_combination (ksSgn ρ * ksSgn ρ) * ksSgn_mul_self ν + ksSgn_mul_self ρ)
  have h2 : ∀ ν ρ, ch (A 2 3 σ σ) (gammaLower ν) (gammaLower ρ) (gamma ν) (gamma ρ) = 0 :=
    fun ν ρ => ksB_ch_zero (Y := ![gammaLower ν, gammaLower ρ, gamma ν, gamma ρ])
      (t := ![ksSgn ν, ksSgn ρ, ksSgn ν, ksSgn ρ]) hs hs1
      (fun l => by fin_cases l
                   exacts [ksFlip_gammaLower ν, ksFlip_gammaLower ρ, ksFlip_gamma ν,
                     ksFlip_gamma ρ])
      (show ksSgn ν * ksSgn ρ * ksSgn ν * ksSgn ρ = 1 by
        linear_combination (ksSgn ρ * ksSgn ρ) * ksSgn_mul_self ν + ksSgn_mul_self ρ)
  have h3 : ∀ ν ρ, ch (A 2 3 σ σ) (gammaLower ν) (gammaLower ρ) (gamma ρ) (gamma ν) = 0 :=
    fun ν ρ => ksB_ch_zero (Y := ![gammaLower ν, gammaLower ρ, gamma ρ, gamma ν])
      (t := ![ksSgn ν, ksSgn ρ, ksSgn ρ, ksSgn ν]) hs hs1
      (fun l => by fin_cases l
                   exacts [ksFlip_gammaLower ν, ksFlip_gammaLower ρ, ksFlip_gamma ρ,
                     ksFlip_gamma ν])
      (show ksSgn ν * ksSgn ρ * ksSgn ρ * ksSgn ν = 1 by
        linear_combination (ksSgn ρ * ksSgn ρ) * ksSgn_mul_self ν + ksSgn_mul_self ρ)
  simp only [chainFour, h1, h2, h3, Finset.sum_const_zero, mul_zero, add_zero]

/-- **The `m⁴` coefficient of the `(2, 3)` entry vanishes** under the same condition. -/
theorem ksB_vNumE4_eq_zero
    (hA : ∀ σ, ∃ s : Fin 4 → ℂ, (∀ l, KsFlip (A 2 3 σ σ l) (s l)) ∧ s 0 * s 1 * s 2 * s 3 = -1)
    (k : Fin 4 → ℝ) : vNumE4 e 0 1 A k 2 3 = 0 := by
  rw [vNumE4, faceId_sum_kV]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun σ _ => ?_)
  obtain ⟨s, hs, hs1⟩ := hA σ
  refine mul_eq_zero_of_right _ (ksFlip_trace ?_)
  have h := ksFlip_mul (hs 0) (ksFlip_mul (hs 1) (ksFlip_mul (hs 2) (hs 3)))
  rwa [show s 0 * (s 1 * (s 2 * s 3)) = -1 by rw [← hs1]; ring] at h

end Rep

/-! ### The three classes -/

theorem ksB_flip_VA (σ : Fin 4) : ∃ s : Fin 4 → ℂ,
    (∀ l, KsFlip (aVA 2 3 σ σ l) (s l)) ∧ s 0 * s 1 * s 2 * s 3 = -1 := by
  refine ⟨![ksSgn 2, ksSgn σ, ksSgn σ, ksSgn 3], fun l => ?_, ?_⟩
  · fin_cases l
    exacts [ksFlip_gamma 2, ksFlip_gamma σ, ksFlip_gamma σ, ksFlip_gamma 3]
  · show ksSgn 2 * ksSgn σ * ksSgn σ * ksSgn 3 = -1
    linear_combination (ksSgn 2 * ksSgn 3) * ksSgn_mul_self σ +
      (by simp [ksSgn] : ksSgn 2 * ksSgn 3 = -1)

theorem ksB_flip_VB (σ : Fin 4) : ∃ s : Fin 4 → ℂ,
    (∀ l, KsFlip (aVB 2 3 σ σ l) (s l)) ∧ s 0 * s 1 * s 2 * s 3 = -1 := by
  refine ⟨![ksSgn 2, ksSgn σ, ksSgn 3, ksSgn σ], fun l => ?_, ?_⟩
  · fin_cases l
    exacts [ksFlip_gamma 2, ksFlip_gamma σ, ksFlip_gamma 3, ksFlip_gamma σ]
  · show ksSgn 2 * ksSgn σ * ksSgn 3 * ksSgn σ = -1
    linear_combination (ksSgn 2 * ksSgn 3) * ksSgn_mul_self σ +
      (by simp [ksSgn] : ksSgn 2 * ksSgn 3 = -1)

theorem ksB_flip_VC (σ : Fin 4) : ∃ s : Fin 4 → ℂ,
    (∀ l, KsFlip (aVC 2 3 σ σ l) (s l)) ∧ s 0 * s 1 * s 2 * s 3 = -1 := by
  refine ⟨![ksSgn 2, ksSgn 3, ksSgn σ, ksSgn σ], fun l => ?_, ?_⟩
  · fin_cases l
    exacts [ksFlip_gamma 2, ksFlip_gamma 3, ksFlip_gamma σ, ksFlip_gamma σ]
  · show ksSgn 2 * ksSgn 3 * ksSgn σ * ksSgn σ = -1
    linear_combination (ksSgn 2 * ksSgn 3) * ksSgn_mul_self σ +
      (by simp [ksSgn] : ksSgn 2 * ksSgn 3 = -1)

end QED.ChainProof.SetAKS

end
