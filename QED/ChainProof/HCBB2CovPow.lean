/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCBB2CovProd
public import QED.TwoLoop.VPHalfAtGenSpec
public import QED.TwoLoop.VPHalfAtAssemblyPieces

/-!
# Covariance of the engine limits `powLimit` and `specLimit`

Helper level, Phase 5 Stage 1a (O3-8 for `QED.ChainProof.Enum.repBB`). The limits `powLimit`
(`(k²)ʲ` over photon-type denominators) and `specLimit` (with spectral denominators at fixed
Feynman parameters) of the `QED.TwoLoop.VPHalfAtGen` engine are linear combinations of
`prodLimit`s with coefficients depending only on the masses and the Feynman parameters. Hence
the covariance of the `prodLimit`s (`QED.ChainProof.HCBB2.conj_prodLim`) passes to them:

* `CovRel L S T A B`: `S B^μ T = L^μ_ν A^ν` for all `μ`, with its linearity;
* `powM`, `specM`: the matrices of `powLimit`, `specLimit` of a numerator family;
* `covRel_prodM`: the `prodLimit` matrices at `(p', p)` and `(L p', L p)` are related, for
  `4` to `8` photon-type masses bounded below by `M₀ > 0` (positive energies at both points);
* `covRel_powM`, `covRel_specM`: the same for `powLimit` and `specLimit`.
-/

@[expose] public section

open Complex Matrix MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.HCBB2

open QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance QED.TwoLoop.VPHalfAtLimit
open QED.TwoLoop.VPHalfAtGen QED.TwoLoop.VPHalfAtAssembly QED.Dirac

/-! ### The covariance relation -/

/-- `S B^μ T = L^μ_ν A^ν` for every `μ`. -/
def CovRel (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ)
    (A B : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ μ, S * B μ * T = vecAct L A μ

namespace CovRel

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}
  {A B A' B' : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}

theorem sub (h : CovRel L S T A B) (h' : CovRel L S T A' B') :
    CovRel L S T (A - A') (B - B') := fun μ => by
  simp only [Pi.sub_apply, Matrix.mul_sub, Matrix.sub_mul, h μ, h' μ, vecAct, smul_sub,
    Finset.sum_sub_distrib]

theorem add (h : CovRel L S T A B) (h' : CovRel L S T A' B') :
    CovRel L S T (A + A') (B + B') := fun μ => by
  simp only [Pi.add_apply, Matrix.mul_add, Matrix.add_mul, h μ, h' μ, vecAct, smul_add,
    Finset.sum_add_distrib]

theorem smul (c : ℂ) (h : CovRel L S T A B) : CovRel L S T (c • A) (c • B) := fun μ => by
  simp only [Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, h μ, vecAct, Finset.smul_sum,
    smul_comm c]

theorem zero : CovRel L S T 0 0 := fun μ => by simp [vecAct]

theorem sum {ι : Type*} (s : Finset ι) {A B : ι → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (h : ∀ i ∈ s, CovRel L S T (A i) (B i)) : CovRel L S T (∑ i ∈ s, A i) (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : CovRel L S T 0 0)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end CovRel

/-! ### The matrices of the engine limits -/

/-- The matrices of `powLimit` of the numerator entries `E μ i j`. -/
noncomputable def powM (α : Fin 4 → Fin 4 → Fin 4 → ℂ)
    (E : Fin 4 → Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℂ) (m : ℝ) (p' p : Fin 4 → ℝ) (j : ℕ) {k : ℕ}
    (Ms : Fin (k + 2) → ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => Matrix.of fun i i' => powLimit (α μ i i') (E μ i i') m p' p j Ms

/-- The matrices of `specLimit` of the numerator entries `E μ i j`. -/
noncomputable def specM (α : Fin 4 → Fin 4 → Fin 4 → ℂ)
    (E : Fin 4 → Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℂ) (m : ℝ) (p' p : Fin 4 → ℝ) (j r : ℕ) {k : ℕ}
    (Ms : Fin (k + 2) → ℝ) (Msp xs : Fin r → ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => Matrix.of fun i i' => specLimit (α μ i i') (E μ i i') m p' p j r Ms Msp xs

section Rec

variable (α : Fin 4 → Fin 4 → Fin 4 → ℂ) (E : Fin 4 → Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℂ)
  (m : ℝ) (p' p : Fin 4 → ℝ)

theorem powM_succ (j : ℕ) {k : ℕ} (Ms : Fin (k + 1 + 2) → ℝ) :
    powM α E m p' p (j + 1) Ms =
      powM α E m p' p j (Fin.tail Ms) - ((Ms 0 ^ 2 : ℝ) : ℂ) • powM α E m p' p j Ms := by
  funext μ
  ext i i'
  simp only [powM, powLimit, Pi.sub_apply, Pi.smul_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul]

theorem specM_zero (j : ℕ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (Msp xs : Fin 0 → ℝ) :
    specM α E m p' p j 0 Ms Msp xs = powM α E m p' p j Ms := rfl

theorem specM_succ (j r : ℕ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (Msp xs : Fin (r + 1) → ℝ) :
    specM α E m p' p j (r + 1) Ms Msp xs = ((xs 0 * (1 - xs 0) : ℝ) : ℂ)⁻¹ •
      specM α E m p' p j r (k := k + 1)
        (Fin.snoc Ms (specMu (Msp 0) (xs 0)) : Fin (k + 1 + 2) → ℝ) (Fin.tail Msp)
        (Fin.tail xs) := by
  funext μ
  ext i i'
  simp only [specM, specLimit, Pi.smul_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]

end Rec

/-! ### Propagation of covariance -/

section Propagate

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}
  {α α₂ : Fin 4 → Fin 4 → Fin 4 → ℂ} {E E₂ : Fin 4 → Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℂ}
  {m M₀ : ℝ} {q' q q₂' q₂ : Fin 4 → ℝ}

theorem covRel_powM (H0 : ∀ (k : ℕ) (Ms : Fin (k + 2) → ℝ), 2 ≤ k → k ≤ 6 →
      (∀ i, M₀ ≤ Ms i) → CovRel L S T (powM α E m q' q 0 Ms) (powM α₂ E₂ m q₂' q₂ 0 Ms)) :
    ∀ (j k : ℕ) (Ms : Fin (k + 2) → ℝ), j + 2 ≤ k → k ≤ 6 → (∀ i, M₀ ≤ Ms i) →
      CovRel L S T (powM α E m q' q j Ms) (powM α₂ E₂ m q₂' q₂ j Ms)
  | 0, k, Ms, h1, h2, hMs => H0 k Ms (by omega) h2 hMs
  | _ + 1, 0, _, h1, _, _ => absurd h1 (by omega)
  | j + 1, k + 1, Ms, h1, h2, hMs => by
    rw [powM_succ, powM_succ]
    exact (covRel_powM H0 j k (Fin.tail Ms) (by omega) (by omega) fun i => hMs _).sub
      ((covRel_powM H0 j (k + 1) Ms (by omega) (by omega) hMs).smul _)

theorem covRel_specM (hM₀ : 0 < M₀) (H0 : ∀ (k : ℕ) (Ms : Fin (k + 2) → ℝ), 2 ≤ k → k ≤ 6 →
      (∀ i, M₀ ≤ Ms i) → CovRel L S T (powM α E m q' q 0 Ms) (powM α₂ E₂ m q₂' q₂ 0 Ms))
    (j : ℕ) : ∀ (r k : ℕ) (Ms : Fin (k + 2) → ℝ) (Msp xs : Fin r → ℝ), j + 2 ≤ k + r →
      k + r ≤ 6 → (∀ i, M₀ ≤ Ms i) → (∀ i, M₀ ≤ Msp i) → (∀ i, xs i ∈ Ioo (0 : ℝ) 1) →
      CovRel L S T (specM α E m q' q j r Ms Msp xs) (specM α₂ E₂ m q₂' q₂ j r Ms Msp xs)
  | 0, k, Ms, _, _, h1, h2, hMs, _, _ => covRel_powM H0 j k Ms h1 (by omega) hMs
  | r + 1, k, Ms, Msp, xs, h1, h2, hMs, hMsp, hxs => by
    rw [specM_succ, specM_succ]
    refine (covRel_specM hM₀ H0 j r (k + 1) _ (Fin.tail Msp) (Fin.tail xs) (by omega)
      (by omega) (fun i => ?_) (fun i => hMsp _) (fun i => hxs _)).smul _
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [Fin.snoc_last]
      exact (hMsp 0).trans (specMu_ge (hM₀.trans_le (hMsp 0)) (hxs 0))
    · rw [Fin.snoc_castSucc]
      exact hMs i

end Propagate

/-! ### The base case -/

/-- **Covariance of the `prodLimit` matrices** of a covariant numerator family, for `4` to `8`
photon-type masses bounded below, with positive energies at `(p', p)` and `(L p', L p)`. -/
theorem covRel_prodM {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀) {L : Matrix (Fin 4) (Fin 4) ℝ}
    {S T : Matrix (Fin 4) (Fin 4) ℂ} (h : IsSpinLift L S T) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
    (h0 : 0 < (L *ᵥ p') 0) (h1 : 0 < (L *ᵥ p) 0)
    (Nf : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (hP : ∀ p' p μ i j, IsLoopPoly 2 4 fun ℓ => Nf p' p μ (ℓ 0) i j)
    (hC : ∀ μ ℓ, S * Nf (L *ᵥ p') (L *ᵥ p) μ (L *ᵥ ℓ) * T = vecAct L (fun ν => Nf p' p ν ℓ) μ)
    (hc : ∀ p' p μ i j, Continuous fun ℓ => Nf p' p μ ℓ i j)
    (hb : ∀ p' p μ i j, ∃ C : ℝ, ∀ ℓ, ‖Nf p' p μ ℓ i j‖ ≤ C * (1 + ‖ℓ‖) ^ 2)
    {α α₂ : Fin 4 → Fin 4 → Fin 4 → ℂ}
    (hα : ∀ μ i j (v : Fin 3 → ℝ), ∃ β γ : ℂ, ∀ t : ℝ,
      Nf p' p μ (Fin.cons t v : Fin 4 → ℝ) i j = α μ i j * (t : ℂ) ^ 2 + β * t + γ)
    (hα₂ : ∀ μ i j (v : Fin 3 → ℝ), ∃ β γ : ℂ, ∀ t : ℝ,
      Nf (L *ᵥ p') (L *ᵥ p) μ (Fin.cons t v : Fin 4 → ℝ) i j = α₂ μ i j * (t : ℂ) ^ 2 + β * t + γ)
    (k : ℕ) (Ms : Fin (k + 2) → ℝ) (hk : 2 ≤ k) (hk' : k ≤ 6) (hMs : ∀ i, M₀ ≤ Ms i) :
    CovRel L S T (powM α (fun μ i j ℓ => Nf p' p μ ℓ i j) m p' p 0 Ms)
      (powM α₂ (fun μ i j ℓ => Nf (L *ᵥ p') (L *ᵥ p) μ ℓ i j) m (L *ᵥ p') (L *ᵥ p) 0 Ms) := by
  have hpL : Minkowski.dot (L *ᵥ p) (L *ᵥ p) = -m ^ 2 := by rw [h.dot_mulVec]; exact hp
  have hpL' : Minkowski.dot (L *ᵥ p') (L *ᵥ p') = -m ^ 2 := by rw [h.dot_mulVec]; exact hp'
  refine conj_prodLim hk hk' hm hM₀ hMs h hp hp' hq Nf hP hC (fun μ i j => ?_) (fun μ i j => ?_)
  · obtain ⟨C, hC⟩ := hb p' p μ i j
    simp only [powM, powLimit_zero, Matrix.of_apply]
    exact tendsto_energyFirstIntegral_prodIntegrand hm hM₀ hp' hp hp0' hp0 (hc p' p μ i j)
      (hα μ i j) hC hMs (es := fun ε _ => ε) tendsto_id (fun _ => tendsto_id)
  · obtain ⟨C, hC⟩ := hb (L *ᵥ p') (L *ᵥ p) μ i j
    simp only [powM, powLimit_zero, Matrix.of_apply]
    exact tendsto_energyFirstIntegral_prodIntegrand hm hM₀ hpL' hpL h0 h1
      (hc (L *ᵥ p') (L *ᵥ p) μ i j) (hα₂ μ i j) hC hMs (es := fun ε _ => ε) tendsto_id
      (fun _ => tendsto_id)

end QED.ChainProof.HCBB2

end
