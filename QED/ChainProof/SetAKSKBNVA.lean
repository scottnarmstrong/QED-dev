/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKBNSlice
public import QED.ChainProof.SetAKSKBNCW
public import QED.ChainProof.SetAKSKBVDens

/-!
# Set (a), stage B3: the nested one-loop form of the class `VA`

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage B3. The five-line
integrand of `VA` (stage B2, `ksB_vDens_VA`) has two equal lines `ℓ₀`; merging them
(`ksN_merge_VA`) gives the four-line data of `SetAKSKBNSlice` with the weight `z₀`. Hierarchical
Cheng–Wu variables (`ksN_nest`) and the slice identity `ksN_slice_VA` then give the nested form:

* **`ksN_nest_VA`**: `∫_{Δ₄} ∑_f c_f ksBAtom(VA, M_f) =
  ∫₀¹ x⁻¹ ∫_{Δ₂} ∑_f c_f K ksNGA(M_f, u, x, k) dx`, with `K = faceIdKV e 0 1`, the outer function
  integrable on `(0, 1)`;
* **`ksN_vDens_VA`**: `vDens(VA)₂₃ = -π⁴ ∫₀¹ x⁻¹ ∫_{Δ₂} ∑_f c_f K ksNGA(M_f, u, x, k) dx`.

On the outer simplex (`y₀ + y₁ + y₂ = 1`; `y₀` the merged line `ℓ₀`, `y₁` the line `k + ℓ₀`, `y₂`
the inner self-energy of mass `m_x² = M²/(1 - x) + u/x`), `ksNGA = k²k³ y₀ [a₀/D² + 2a₁/D]`,
`D = y₁(1 - y₁) s + (y₀ + y₁)M² + y₂ m_x²`, `a₀ = 16 y₁(1 - y₁)(4M² - ξM² + ξ s y₁²)`,
`a₁ = -8 ξ y₁ (4y₁ - 3)`, `ξ = 1 - x`, `s = k·k` (the INTERFACE form of `setAKS4/outerVA.py`).
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.ChainProof.SetAKS

open QED.Integration.TwoLoop QED.GradedProof.RPi4 QED.GradedProof.VP2
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet)
open QED.GradedProof.WI2 (dbl)
open QED.Integration.SimplexMerge (integral_simplex_splitAt splitAt)

/-- The relabelling of the five `VA` lines that puts the second `ℓ₀` line last. -/
def ksNPermA : Equiv.Perm (Fin 5) := Equiv.swap 2 4 * Equiv.swap 2 3

theorem ksN_permA_base :
    (fun l => castLoopMatrix baseVA (ksNPermA l)) = dbl 0 (castLoopMatrix ksNBaseA) := by
  funext l
  fin_cases l <;> rfl

theorem ksN_permA_pp (k : Fin 4 → ℝ) :
    (fun l => (fun l => cVA l • k) (ksNPermA l)) = dbl 0 (ksNppA k) := by
  funext l
  fin_cases l <;> simp [ksNPermA, cVA, ksNppA, dbl, Equiv.swap_apply_def]

theorem ksN_permA_M (M : ℝ) :
    (fun l => ksBM5 (fun _ => M) (ksNPermA l)) = Fin.snoc (ksNMA M) M := by
  funext l
  fin_cases l <;> rfl

theorem ksN_permA_last : ksNPermA (3 : Fin 4).castSucc = Fin.last 4 := by decide

/-- **A doubled line with equal masses merges**: the integrand at a split point of line `i` is
the merged integrand, whatever the split. -/
theorem ksN_pieceF_merge {m : ℕ} (Q : LoopQuartic) {i γ : Fin (m + 1)} (hγ : γ ≠ i)
    (α : Fin (m + 1) → Fin 2 → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ)
    (u : ℝ) (z : Fin (m + 1) → ℝ) (t : ℝ) :
    pieceF 5 Q (dbl i α) (dbl i pp) (Fin.snoc M (M i)) γ.castSucc u (splitAt i z t) =
      pieceF 5 Q α pp M γ u z := by
  rw [ksB_pieceF_dbl_splitAt 5 Q hγ α pp M (M i) u z t]
  have hV : symanzikV α pp (Function.update M i 0) z + z γ * u + t * M i ^ 2 +
      (z i - t) * M i ^ 2 = symanzikV α pp M z + z γ * u := by
    rw [ksB_symanzikV_self α pp M z i]
    ring
  rw [hV]
  rfl

theorem ksN_vec_four (x : ℝ) (v : Fin 2 → ℝ) :
    (Fin.snoc (Fin.insertNth 1 x v) (1 - x) : Fin 4 → ℝ) = ![v 0, x, v 1, 1 - x] := by
  funext i
  fin_cases i <;> rfl

theorem ksN_vec_three (v : Fin 2 → ℝ) (τ : ℝ) :
    (Fin.snoc v τ : Fin 3 → ℝ) = ![v 0, v 1, τ] := by
  funext i
  fin_cases i <;> rfl

section Classes

variable {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hPV₁ : ∑ f, Φ.coeff f = 0)
  (hPV₂ : ∑ f, Φ.coeff f * Φ.mass f ^ 2 = 0) {m₀ : ℝ} (hm₀ : 0 < m₀)
  (hmass : ∀ g, m₀ ≤ Φ.mass g) (e : ℝ) {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k)
  {u : ℝ} (hu : 0 < u)

/-- The flavour sum of the outer `VA` integrands at the inner Cheng–Wu variable `x`. -/
noncomputable def ksNGAsum (e u : ℝ) (k : Fin 4 → ℝ) (x : ℝ) (y : Fin 3 → ℝ) : ℂ :=
  ∑ f, (Φ.coeff f : ℂ) * (faceIdKV e 0 1 * (ksNGA (Φ.mass f) u x k y : ℂ))

theorem ksN_eval_VA (M : ℝ) :
    (ksBRep e aVA baseVA cVA M k).eval =
      fun ℓ => faceIdKV e 0 1 * (ksNTA M (ℓ 0) (ℓ 1) k : ℂ) := by
  rw [ksBRep_eval]
  funext ℓ
  exact ksN_vNum_VA e M k ℓ

include hPV₁ hPV₂ hm₀ hmass hk hu

/-- **The nested form of `VA`**: hierarchical Cheng–Wu variables, inner loop first. -/
theorem ksN_nest_VA :
    IntegrableOn (fun x => x⁻¹ • ∫ y in simplexSet 2, ksNGAsum Φ e u k x (simplexPoint y))
      (Ioo (0 : ℝ) 1) ∧
    ∫ y in simplexSet 4, ∑ f, (Φ.coeff f : ℂ) * ksBAtom baseVA cVA k
      (ksBRep e aVA baseVA cVA (Φ.mass f) k) u (simplexPoint y) (fun _ => Φ.mass f) =
    ∫ x in Ioo (0 : ℝ) 1, x⁻¹ • ∫ y in simplexSet 2, ksNGAsum Φ e u k x (simplexPoint y) := by
  obtain ⟨hI5, -⟩ := ksB_vDens_VA Φ hPV₁ hPV₂ hm₀ hmass e hk hu
  set Qf := fun f => ksBRep e aVA baseVA cVA (Φ.mass f) k
  -- the permutation putting the second `ℓ₀` line last
  have hperm := ksB_integral_pieceF_perm Finset.univ ksNPermA 5 Qf (castLoopMatrix baseVA)
    (fun l => cVA l • k) (fun f => (Φ.coeff f : ℂ)) (fun f => ksBM5 fun _ => Φ.mass f)
    (3 : Fin 4).castSucc u
  rw [ksN_permA_last, ksN_permA_base, ksN_permA_pp] at hperm
  simp only [ksN_permA_M] at hperm
  simp only [ksBAtom] at hI5 ⊢
  rw [← hperm.1] at hI5
  rw [← hperm.2]
  -- the merge `Δ₄ → Δ₃`
  set F3 : (Fin 4 → ℝ) → ℂ := fun z => ∑ f, (Φ.coeff f : ℂ) *
    ((z 0 : ℂ) * pieceF 5 (Qf f) (castLoopMatrix ksNBaseA) (ksNppA k) (ksNMA (Φ.mass f)) 3 u z)
    with hF3
  have hsplit : ∀ (z : Fin 4 → ℝ) (t : ℝ), (∑ f, (Φ.coeff f : ℂ) * pieceF 5 (Qf f)
      (dbl 0 (castLoopMatrix ksNBaseA)) (dbl 0 (ksNppA k)) (Fin.snoc (ksNMA (Φ.mass f))
        (Φ.mass f)) (3 : Fin 4).castSucc u (splitAt 0 z t)) = ∑ f, (Φ.coeff f : ℂ) *
      pieceF 5 (Qf f) (castLoopMatrix ksNBaseA) (ksNppA k) (ksNMA (Φ.mass f)) 3 u z :=
    fun z t => Finset.sum_congr rfl fun f _ =>
      congrArg _ (ksN_pieceF_merge (Qf f) (by decide) _ _ (ksNMA (Φ.mass f)) u z t)
  obtain ⟨hI4, hE4⟩ := integral_simplex_splitAt (m := 3) (by norm_num) (0 : Fin 4)
    (f := fun z : Fin 5 → ℝ => ∑ f, (Φ.coeff f : ℂ) * pieceF 5 (Qf f)
      (dbl 0 (castLoopMatrix ksNBaseA)) (dbl 0 (ksNppA k)) (Fin.snoc (ksNMA (Φ.mass f))
        (Φ.mass f)) (3 : Fin 4).castSucc u z) hI5
  simp only [hsplit, intervalIntegral.integral_const, sub_zero] at hI4 hE4
  have hF3eq : ∀ z : Fin 4 → ℝ, z 0 • (∑ f, (Φ.coeff f : ℂ) * pieceF 5 (Qf f)
      (castLoopMatrix ksNBaseA) (ksNppA k) (ksNMA (Φ.mass f)) 3 u z) = F3 z := by
    intro z
    rw [hF3, Complex.real_smul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun f _ => by ring
  simp only [hF3eq] at hI4 hE4
  rw [hE4]
  -- the hierarchical Cheng–Wu variables
  refine ksN_nest (F := F3) ?_ hI4 (ksNGAsum Φ e u k) ?_ ?_
  · intro z hz t ht
    rw [hF3, Complex.real_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [ksN_pieceF_smul (ht := ht.ne'), Pi.smul_apply, smul_eq_mul]
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
    push_cast
    field_simp
  · intro x _ z hz t ht
    simp only [ksNGAsum, Complex.real_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [ksN_ksNGA_smul _ _ _ _ _ hz ht]
    push_cast
    ring
  · intro x hx v hv
    rw [ksN_vec_four, ksN_vec_three, hF3]
    simp only [ksNGAsum, Complex.real_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    have h := ksN_slice_VA k (ksN_eval_VA e (Φ.mass f)) (ksBRep_contractFour e aVA baseVA cVA
      ksB_flip_VA (Φ.mass f) k) u hx (hv 0) (hv 1)
    simp only [Matrix.cons_val_zero]
    rw [h]
    ring

/-- **`VA` at the entry `(2, 3)` in nested one-loop form.** -/
theorem ksN_vDens_VA :
    IntegrableOn (fun x => x⁻¹ • ∫ y in simplexSet 2, ksNGAsum Φ e u k x (simplexPoint y))
      (Ioo (0 : ℝ) 1) ∧
    vDens aVA baseVA cVA Φ e m₀ u k 2 3 = -((π : ℂ) ^ 4) *
      ∫ x in Ioo (0 : ℝ) 1, x⁻¹ • ∫ y in simplexSet 2, ksNGAsum Φ e u k x (simplexPoint y) := by
  obtain ⟨h1, h2⟩ := ksN_nest_VA Φ hPV₁ hPV₂ hm₀ hmass e hk hu
  exact ⟨h1, by rw [(ksB_vDens_VA Φ hPV₁ hPV₂ hm₀ hmass e hk hu).2, h2]⟩

end Classes

end QED.ChainProof.SetAKS

end
