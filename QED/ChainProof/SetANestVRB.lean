/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2VNum

/-!
# The pointwise bound by the line weights, additive in the external momentum

Helper level for the set (a) headline (HA₆), obligation (N), step NL for `VA`, `VB`, `VC`.
`QED.Integration.TwoLoop.RefinedBound α E n F` bounds `‖F ℓ‖` by
`C w_E(A) (1 + ℓᵀAℓ)^{n/2}` with a constant `C` that, for a family `F_k`, grows with the external
momentum `k`. Here the dependence on `k` is additive:

`RBK α E n F`: `‖F_k(ℓ)‖ ≤ C w_E(A) (1 + Σ_μ k_μ² + ℓᵀAℓ)^{n/2}` with one `C` for all `k`.

This is the hypothesis of `QED.ChainProof.SetANestV.integral_norm_energyIntegral_le`. The algebra
(`RBK.add`, `RBK.mul`, …) and the base case `rbk_lineMomentum` (line momenta `αₑ·ℓ + cₑ k`) mirror
those of `RefinedBound`; then `rbk_electronNumerator`, `rbk_vT`, `rbk_vNum` and
`rbk_propDenom_pad` give the bounds of the numerators of the classes `VA`, `VB`, `VC`
(`QED.GradedProof.VP2.rb_vNum`, `QED.GradedProof.VP2.rb_propDenom_pad`).
-/

@[expose] public section

open Complex Matrix

namespace QED.ChainProof.SetANestV

open QED.Integration.TwoLoop (RefinedBound lineWeight loopNorm lineMomentum castLoopMatrix
  lineWeight_nonneg loopNorm_nonneg lineWeight_union lineWeight_mono lineWeight_singleton
  one_le_sqrt_lineFactor abs_dotProduct_le qf_le_loopNorm)

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-- The size `Σ_μ k_μ²` of the external momentum. -/
def kSq (k : Fin 4 → ℝ) : ℝ := ∑ μ, k μ ^ 2

theorem kSq_nonneg (k : Fin 4 → ℝ) : 0 ≤ kSq k := Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **The pointwise bound, additive in the external momentum.** -/
def RBK {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (E : Finset (Fin (m + 1))) (n : ℕ)
    (F : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Fin 4 → ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ), A.PosDef → ∀ ℓ,
    ‖F k ℓ‖ ≤ C * lineWeight α E A * Real.sqrt (1 + kSq k + loopNorm A ℓ) ^ n

theorem one_le_sqrt_kSq {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) (k : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) : 1 ≤ Real.sqrt (1 + kSq k + loopNorm A ℓ) := by
  rw [Real.one_le_sqrt]
  linarith [kSq_nonneg k, loopNorm_nonneg hA ℓ]

namespace RBK

variable {m : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ} {E E' : Finset (Fin (m + 1))} {n n' : ℕ}
  {F G : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ}

theorem mono (h : RBK α E n F) (hE : E ⊆ E') (hn : n ≤ n') : RBK α E' n' F := by
  obtain ⟨C, hC, hF⟩ := h
  refine ⟨C, hC, fun k A hA ℓ => (hF k A hA ℓ).trans ?_⟩
  have h1 := lineWeight_mono α hA hE
  have h2 := pow_le_pow_right₀ (one_le_sqrt_kSq hA k ℓ) hn
  have h3 := lineWeight_nonneg α E A
  have h4 := lineWeight_nonneg α E' A
  have h5 : 0 ≤ Real.sqrt (1 + kSq k + loopNorm A ℓ) ^ n := pow_nonneg (Real.sqrt_nonneg _) n
  calc C * lineWeight α E A * Real.sqrt (1 + kSq k + loopNorm A ℓ) ^ n
      ≤ C * lineWeight α E' A * Real.sqrt (1 + kSq k + loopNorm A ℓ) ^ n := by gcongr
    _ ≤ C * lineWeight α E' A * Real.sqrt (1 + kSq k + loopNorm A ℓ) ^ n' :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hC h4)

theorem const (c : ℂ) : RBK α ∅ 0 fun _ _ => c :=
  ⟨‖c‖, norm_nonneg _, fun k A _ ℓ => by simp [lineWeight]⟩

theorem add (hF : RBK α E n F) (hG : RBK α E n G) : RBK α E n fun k ℓ => F k ℓ + G k ℓ := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨D, hD, hG⟩ := hG
  refine ⟨C + D, add_nonneg hC hD, fun k A hA ℓ => ?_⟩
  calc ‖F k ℓ + G k ℓ‖ ≤ ‖F k ℓ‖ + ‖G k ℓ‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (hF k A hA ℓ) (hG k A hA ℓ)
    _ = _ := by ring

theorem const_mul (c : ℂ) (hF : RBK α E n F) : RBK α E n fun k ℓ => c * F k ℓ := by
  obtain ⟨C, hC, hF⟩ := hF
  refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC, fun k A hA ℓ => ?_⟩
  rw [norm_mul, mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [← mul_assoc]
  exact hF k A hA ℓ

theorem neg (hF : RBK α E n F) : RBK α E n fun k ℓ => -F k ℓ := by
  simpa using hF.const_mul (-1)

theorem sub (hF : RBK α E n F) (hG : RBK α E n G) : RBK α E n fun k ℓ => F k ℓ - G k ℓ := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

theorem zero : RBK α E n fun _ _ => 0 :=
  ⟨0, le_rfl, fun k A hA ℓ => by simp⟩

theorem sum {ι : Type*} (s : Finset ι) {F : ι → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ s, RBK α E n (F i)) : RBK α E n fun k ℓ => ∑ i ∈ s, F i k ℓ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : RBK α E n fun _ _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mul (hF : RBK α E n F) (hG : RBK α E' n' G) (hd : Disjoint E E') :
    RBK α (E ∪ E') (n + n') fun k ℓ => F k ℓ * G k ℓ := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨D, hD, hG⟩ := hG
  refine ⟨C * D, mul_nonneg hC hD, fun k A hA ℓ => ?_⟩
  rw [norm_mul, lineWeight_union α hd, pow_add]
  calc ‖F k ℓ‖ * ‖G k ℓ‖ ≤ (C * lineWeight α E A * Real.sqrt (1 + kSq k + loopNorm A ℓ) ^ n) *
        (D * lineWeight α E' A * Real.sqrt (1 + kSq k + loopNorm A ℓ) ^ n') :=
        mul_le_mul (hF k A hA ℓ) (hG k A hA ℓ) (norm_nonneg _)
          (by have := lineWeight_nonneg α E A; positivity)
    _ = _ := by ring

/-- At a fixed external momentum the additive bound is a `RefinedBound`. -/
theorem refinedBound (h : RBK α E n F) (k : Fin 4 → ℝ) : RefinedBound α E n (F k) := by
  obtain ⟨C, hC, hF⟩ := h
  refine ⟨C * Real.sqrt (1 + kSq k) ^ n, by positivity, fun A hA ℓ => (hF k A hA ℓ).trans ?_⟩
  have hk := kSq_nonneg k
  have hL := loopNorm_nonneg hA ℓ
  have h1 : Real.sqrt (1 + kSq k + loopNorm A ℓ) ≤
      Real.sqrt (1 + kSq k) * Real.sqrt (1 + loopNorm A ℓ) := by
    rw [← Real.sqrt_mul (by linarith)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 n
  rw [mul_pow] at h2
  have := lineWeight_nonneg α E A
  calc C * lineWeight α E A * Real.sqrt (1 + kSq k + loopNorm A ℓ) ^ n
      ≤ C * lineWeight α E A * (Real.sqrt (1 + kSq k) ^ n * Real.sqrt (1 + loopNorm A ℓ) ^ n) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

end RBK

/-- **A component of a line momentum `αₑ·ℓ + cₑ k`** is bounded by its line, additively in `k`:
`|αₑ·ℓ^ν + cₑ k_ν| ≤ (1 + |cₑ|) (1 + αₑᵀA⁻¹αₑ)^{1/2} (1 + Σ k² + ℓᵀAℓ)^{1/2}`. -/
theorem rbk_lineMomentum {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (c : Fin (m + 1) → ℝ)
    (e : Fin (m + 1)) (ν : Fin 4) :
    RBK α {e} 1 fun k ℓ => ((lineMomentum α (fun i => c i • k) e ℓ ν : ℝ) : ℂ) := by
  refine ⟨1 + |c e|, by positivity, fun k A hA ℓ => ?_⟩
  rw [norm_real, Real.norm_eq_abs, lineWeight_singleton, pow_one]
  set W := Real.sqrt (1 + kSq k + loopNorm A ℓ) with hW
  set Q := Real.sqrt (1 + α e ⬝ᵥ A⁻¹ *ᵥ α e) with hQ
  have hcs := abs_dotProduct_le hA (α e) (fun s => ℓ s ν)
  have hk := kSq_nonneg k
  have hL := loopNorm_nonneg hA ℓ
  have hq := Real.sqrt_le_sqrt (qf_le_loopNorm hA ℓ ν)
  have hQ1 : 1 ≤ Q := one_le_sqrt_lineFactor α hA e
  have hQ' : Real.sqrt (α e ⬝ᵥ A⁻¹ *ᵥ α e) ≤ Q := Real.sqrt_le_sqrt (by linarith)
  have hN : Real.sqrt (loopNorm A ℓ) ≤ W := Real.sqrt_le_sqrt (by linarith)
  have hkν : |k ν| ≤ W := by
    have h1 : k ν ^ 2 ≤ kSq k :=
      Finset.single_le_sum (f := fun μ => k μ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ ν)
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  have hW0 : 0 ≤ W := Real.sqrt_nonneg _
  have hlm : lineMomentum α (fun i => c i • k) e ℓ ν = α e ⬝ᵥ (fun s => ℓ s ν) + c e * k ν := by
    simp [lineMomentum, dotProduct]
  rw [hlm]
  have h1 : |α e ⬝ᵥ (fun s => ℓ s ν)| ≤ Q * W :=
    hcs.trans (mul_le_mul hQ' (hq.trans hN) (Real.sqrt_nonneg _) (by linarith))
  have h2 : |c e * k ν| ≤ |c e| * (Q * W) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hkν.trans (le_mul_of_one_le_left hW0 hQ1)) (abs_nonneg _)
  calc |α e ⬝ᵥ (fun s => ℓ s ν) + c e * k ν| ≤ |α e ⬝ᵥ (fun s => ℓ s ν)| + |c e * k ν| :=
        abs_add_le _ _
    _ ≤ Q * W + |c e| * (Q * W) := add_le_add h1 h2
    _ = _ := by ring

/-! ### Matrix-valued numerators -/

/-- Every entry of a matrix-valued family satisfies the additive bound. -/
def RBKMat {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (E : Finset (Fin (m + 1))) (n : ℕ)
    (A : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Mat) : Prop :=
  ∀ i j, RBK α E n fun k ℓ => A k ℓ i j

namespace RBKMat

variable {m : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ} {E E' : Finset (Fin (m + 1))} {n n' : ℕ}
  {A B : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Mat}

theorem const (C : Mat) : RBKMat α ∅ 0 fun _ _ => C := fun _ _ => RBK.const _

theorem mono (h : RBKMat α E n A) (hE : E ⊆ E') (hn : n ≤ n') : RBKMat α E' n' A :=
  fun i j => (h i j).mono hE hn

theorem mul (hA : RBKMat α E n A) (hB : RBKMat α E' n' B) (hd : Disjoint E E') :
    RBKMat α (E ∪ E') (n + n') fun k ℓ => A k ℓ * B k ℓ := fun i j => by
  simp only [Matrix.mul_apply]
  exact RBK.sum _ fun l _ => (hA i l).mul (hB l j) hd

theorem trace (hA : RBKMat α E n A) : RBK α E n fun k ℓ => (A k ℓ).trace := by
  simp only [Matrix.trace, Matrix.diag]
  exact RBK.sum _ fun i _ => hA i i

theorem mulC (h : RBKMat α E n A) (C : Mat) : RBKMat α E n fun k ℓ => A k ℓ * C :=
  (h.mul (const C) (Finset.disjoint_empty_right E)).mono (by simp) (by simp)

theorem mulN (h : RBKMat α E n A) {e : Fin (m + 1)} (hB : RBKMat α {e} 1 B) (he : e ∉ E) :
    RBKMat α (insert e E) (n + 1) fun k ℓ => A k ℓ * B k ℓ :=
  (h.mul hB (Finset.disjoint_singleton_right.mpr he)).mono
    (by rw [Finset.union_comm, ← Finset.insert_eq]) le_rfl

end RBKMat

/-- `m - k̸` at a line momentum `αₑ·ℓ + cₑ k`. -/
theorem rbk_electronNumerator {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (c : Fin (m + 1) → ℝ)
    (e : Fin (m + 1)) (mass : ℝ) :
    RBKMat α {e} 1 fun k ℓ =>
      QED.TwoLoop.Bridge.electronNumerator mass (lineMomentum α (fun i => c i • k) e ℓ) :=
  fun a b => by
  have h : (fun k ℓ => QED.TwoLoop.Bridge.electronNumerator mass
      (lineMomentum α (fun i => c i • k) e ℓ) a b) = fun k ℓ =>
      (if a = b then (mass : ℂ) else 0) - ∑ μ, ∑ ν,
        (((Minkowski.metric μ ν : ℝ) : ℂ) * Dirac.gamma μ a b) *
          ((lineMomentum α (fun i => c i • k) e ℓ ν : ℝ) : ℂ) := by
    funext k ℓ
    rw [QED.TwoLoop.Bridge.electronNumerator_apply]
    congr 1
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring
  rw [h]
  exact ((RBK.const _).mono (Finset.empty_subset _) (Nat.zero_le _)).sub
    (RBK.sum _ fun μ _ => RBK.sum _ fun ν _ => (rbk_lineMomentum α c e ν).const_mul _)

/-! ### The numerators of `VA`, `VB`, `VC` -/

section VP2

open QED.GradedProof.VP2 (fm ppc vT vNum kV)

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)

theorem rbk_fm {m : ℕ} (sh : Fin (m + 1) → Fin 5) (n : Fin (m + 1)) (l : Fin 4)
    (h : sh n = l.castSucc) (M : ℝ) :
    RBKMat (castLoopMatrix fun r => base (sh r)) {n} 1
      fun k ℓ => QED.TwoLoop.Bridge.electronNumerator M (fm base (ppc c k) l ℓ) := by
  have := rbk_electronNumerator (castLoopMatrix fun r => base (sh r)) (fun r => c (sh r)) n M
  have e : ∀ (k : Fin 4 → ℝ) ℓ, lineMomentum (castLoopMatrix fun r => base (sh r))
      (fun i => c (sh i) • k) n ℓ = fm base (ppc c k) l ℓ := fun k ℓ => by
    simp only [fm, ← h]
    rfl
  simpa only [e] using this

/-- **The additive bound of the loop trace** on four lines carrying the four fermion momenta. -/
theorem rbk_vT {m : ℕ} (sh : Fin (m + 1) → Fin 5) (e : Fin 4 → Fin (m + 1))
    (he : ∀ l, sh (e l) = l.castSucc) (h01 : e 0 ≠ e 1) (h02 : e 0 ≠ e 2) (h03 : e 0 ≠ e 3)
    (h12 : e 1 ≠ e 2) (h13 : e 1 ≠ e 3) (h23 : e 2 ≠ e 3) (A : Fin 4 → Mat) (M : ℝ) :
    RBK (castLoopMatrix fun k => base (sh k)) {e 0, e 1, e 2, e 3} 4
      fun k ℓ => vT A M (fun l => fm base (ppc c k) l ℓ) := by
  have N := fun l => rbk_fm base c sh (e l) l (he l) M
  have h0 : RBKMat (castLoopMatrix fun k => base (sh k)) ∅ 0 fun _ _ => A 0 :=
    RBKMat.const _
  have h := RBKMat.trace (RBKMat.mulN (RBKMat.mulC (RBKMat.mulN (RBKMat.mulC (RBKMat.mulN
    (RBKMat.mulC (RBKMat.mulN h0 (N 0) (Finset.notMem_empty _)) (A 1)) (N 1)
    (by simp [h01.symm])) (A 2)) (N 2) (by simp [h02.symm, h12.symm])) (A 3)) (N 3)
    (by simp [h03.symm, h13.symm, h23.symm]))
  refine h.mono (fun x hx => ?_) le_rfl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

/-- **The additive bound of a class numerator** on the four fermion lines of a shape. -/
theorem rbk_vNum (e mγ Λ : ℝ) (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Mat) {n : ℕ}
    (sh : Fin (n + 1) → Fin 5) (e4 : Fin 4 → Fin (n + 1))
    (he : ∀ l, sh (e4 l) = l.castSucc) (h01 : e4 0 ≠ e4 1) (h02 : e4 0 ≠ e4 2)
    (h03 : e4 0 ≠ e4 3) (h12 : e4 1 ≠ e4 2) (h13 : e4 1 ≠ e4 3) (h23 : e4 2 ≠ e4 3) (m : ℝ)
    (a b : Fin 4) :
    RBK (castLoopMatrix fun r => base (sh r)) {e4 0, e4 1, e4 2, e4 3} 4
      fun k ℓ => vNum e mγ Λ A base c m k ℓ a b :=
  RBK.sum _ fun ρ _ => RBK.sum _ fun σ _ =>
    (rbk_vT base c sh e4 he h01 h02 h03 h12 h13 h23 (A a b ρ σ) m).const_mul _

/-- The denominator of a line, padded by a second line with the same momentum, is bounded on the
two lines, additively in `k`. -/
theorem rbk_propDenom_pad {m : ℕ} (sh : Fin (m + 1) → Fin 5) (a b : Fin (m + 1)) (hab : a ≠ b)
    (l : Fin 4) (ha : sh a = l.castSucc) (hb : sh b = l.castSucc) (Y ε : ℝ) :
    RBK (castLoopMatrix fun k => base (sh k)) {a, b} 2
      fun k ℓ => QED.TwoLoop.Bridge.propDenom Y ε (fm base (ppc c k) l ℓ) := by
  have e : (fun k ℓ => QED.TwoLoop.Bridge.propDenom Y ε (fm base (ppc c k) l ℓ)) = fun k ℓ =>
      (∑ μ ∈ Finset.univ, ∑ ν ∈ Finset.univ, ((Minkowski.metric μ ν : ℝ) : ℂ) *
        (((fm base (ppc c k) l ℓ μ : ℝ) : ℂ) * ((fm base (ppc c k) l ℓ ν : ℝ) : ℂ))) +
          (((Y ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) := by
    funext k ℓ
    simp only [QED.TwoLoop.Bridge.propDenom, Minkowski.dot]
    push_cast
    simp only [mul_assoc]
    ring
  rw [e]
  have hm : ∀ (n : Fin (m + 1)), sh n = l.castSucc → ∀ (k : Fin 4 → ℝ) ℓ μ,
      lineMomentum (castLoopMatrix fun r => base (sh r)) (fun i => c (sh i) • k) n ℓ μ =
        fm base (ppc c k) l ℓ μ := fun n hn k ℓ μ => by
    simp only [fm, ← hn]
    rfl
  have La := fun μ => rbk_lineMomentum (castLoopMatrix fun k => base (sh k))
    (fun k => c (sh k)) a μ
  have Lb := fun μ => rbk_lineMomentum (castLoopMatrix fun k => base (sh k))
    (fun k => c (sh k)) b μ
  simp only [hm a ha, hm b hb] at La Lb
  have hd : Disjoint ({a} : Finset (Fin (m + 1))) {b} := Finset.disjoint_singleton.mpr hab
  refine RBK.add (RBK.sum _ fun μ _ => RBK.sum _ fun ν _ => ?_)
    ((RBK.const _).mono (Finset.empty_subset _) (by norm_num))
  refine (((La μ).mul (Lb ν) hd).const_mul _).mono (fun x hx => ?_) le_rfl
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert] at hx ⊢
  exact hx

end VP2

end QED.ChainProof.SetANestV

end
