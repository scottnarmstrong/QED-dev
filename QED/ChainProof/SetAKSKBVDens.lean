/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKBLeib
public import QED.ChainProof.SetAKSKBQuart
public import QED.ChainProof.SetAKSKBPos

/-!
# Set (a), stage B2: a class density as one integral over the five-line simplex

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage B2 (undoing the
auxiliary-mass partial fractions). The photon-mass density `QED.GradedProof.RPi4.vDens` of a
class is the block-summed flavour sum of `triDens` (ten seven-line pieces, four six-line pieces
and a padded piece). At the entry `(2, 3)`, for every photon mass `u > 0` and momentum below
threshold:

* `ksB_pairDens_pieceA`, `ksB_pairDens_pieceB`: each piece is an integral over `Δ₄` of a divided
  difference of the five-line integrand (`ksB_pieceA_merge`, `ksB_pieceB_merge`, with the chain
  quartics `ksBRep`, `ksB_integrableOn_pieceF`, `ksB_pos5`, `ksB_pos6`);
* `ksB_pairDens_zero`: the padded piece vanishes (`ksB_vNumE4_eq_zero`);
* **`ksB_triDens_eq`**: `triDens = -π⁴ ∫_{Δ₄} ksBTri` (the Leibniz rule `ksB_leibniz`);
* **`ksB_vDens_eq`**: under the two Pauli–Villars conditions,
  `vDens = -π⁴ ∫_{Δ₄} ∑_f c_f ksBAtom(ksBRep(M_f))(M_f, M_f, M_f, M_f)`, the integrand integrable
  (one integral of the flavour sum: the five-line integrand of one flavour has a log-divergent
  fermion subloop and is not claimed integrable);
* `ksB_vDens_VA`, `ksB_vDens_VB`, `ksB_vDens_VC`: the three classes.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.ChainProof.SetAKS

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.GradedProof.RPi4 QED.GradedProof.VP2
open QED.GradedProof.SE2 QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet)

/-! ### Linearity of the collapsed integrand in the quartic -/

/-- `ksBAtom` is linear in the quartic. -/
theorem ksBAtom_qsum (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (k : Fin 4 → ℝ) (u : ℝ)
    {ι : Type*} (s : Finset ι) (w : ι → ℂ) (Qs : ι → LoopQuartic) {Q : LoopQuartic}
    (hQ : Q.eval = (qsum s w Qs).eval) (z : Fin 5 → ℝ) (mf : Fin 4 → ℝ) :
    ksBAtom base c k Q u z mf = ∑ i ∈ s, w i * ksBAtom base c k (Qs i) u z mf := by
  simp only [ksBAtom, pieceF, paramAtV_congr hQ, paramAtV_qsum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The five-line collapsed integrand as a function of the four fermion masses. -/
noncomputable def ksBG (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (k : Fin 4 → ℝ)
    (Q : LoopQuartic) (u : ℝ) (z : Fin 5 → ℝ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun a b c' d => ksBAtom base c k Q u z ![a, b, c', d]

/-- `ksBG` is `ksBAtom` as a function of four masses. -/
theorem ksBOf_ksBG (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (k : Fin 4 → ℝ)
    (Q : LoopQuartic) (u : ℝ) (z : Fin 5 → ℝ) (mf : Fin 4 → ℝ) :
    ksBOf (ksBG base c k Q u z) mf = ksBAtom base c k Q u z mf := rfl

/-- **A density with the numerator `0` vanishes.** -/
theorem ksB_pairDens_zero {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (Ms : Fin (m + 1) → ℝ) (γ : Fin (m + 1)) (u : ℝ) :
    pairDens (fun _ => 0) α p Ms γ u = 0 := by
  have h0 : (qsum (∅ : Finset Unit) (fun _ => 0) (fun _ => ⟨0, 0, 0, 0, 0⟩)).eval = fun _ => 0 := by
    funext ℓ; simp [eval_qsum]
  rw [pairDens_eq h0]
  simp [paramAtV_qsum]

/-! ### The pieces of `triDens` on `Δ₄` -/

section Pieces

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)

include hflow

/-- **A seven-line piece of `triDens` on `Δ₄`**, for `i ≤ j`. -/
theorem ksB_pairDens_pieceA (i j : Fin 4)
    (hcA : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => base (shA i j n))
    (F : (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : IsLoopPoly 2 4 F)
    (hB : RefinedBound (castLoopMatrix fun n => base (shA i j n)) {0, 1, 2, 3} 4 F)
    (R : LoopQuartic) (hR : R.eval = F) (hR4 : ∀ A, R.contractFour A = 0)
    {m₀ : ℝ} (hm₀ : 0 < m₀) {M X Y : ℝ} (hM : m₀ ≤ M) (hMX : M < X) (hXY : X < Y)
    {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun y => ksBdd (fun mf' => ksBdd (fun mf => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
      ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * ksBOf (ksBG base c k R u (simplexPoint y)) mf) mf' i X)
      (mA M X Y i j) j Y) (simplexSet 4) ∧
    pairDens (fun ℓ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * F ℓ)
        (castLoopMatrix fun l : Fin 7 => base (shA i j l.castSucc))
        (fun l => c (shA i j l.castSucc) • k)
        ![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2, mA M X Y i j 3, X, Y, 0]
        (Fin.last 6) u =
      -((π : ℂ) ^ 4) * ∫ y in simplexSet 4, ksBdd (fun mf' => ksBdd (fun mf =>
        ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          ksBOf (ksBG base c k R u (simplexPoint y)) mf) mf' i X) (mA M X Y i j) j Y := by
  set C : ℂ := ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) with hC
  set QA := qsum (Finset.univ : Finset Unit) (fun _ => C) (fun _ => R) with hQA_def
  have hQA : QA.eval = fun ℓ => C * F ℓ := by
    funext ℓ; simp [QA, eval_qsum, hR]
  have hC4 : ∀ A, QA.contractFour A = 0 := fun A => by simp [QA, contractFour_qsum, hR4]
  have hX0 : m₀ ≤ X := by linarith
  have hY0 : m₀ ≤ Y := by linarith
  have hM0 : 0 < M := by linarith
  have hmf : ∀ l, m₀ ≤ mA M X Y i j l := fun l => by unfold mA; split_ifs <;> linarith
  have hI := ksB_integrableOn_pieceF base c y₁ y₂ hflow (m := 6) (Or.inr rfl) (shA i j)
    (fun l => by fin_cases l <;> simp [shA, Fin.ext_iff] <;> omega) hcA _
    (hpoly.const_mul C) (hB.const_mul C) QA hQA hm₀ (ksBM7 (mA M X Y i j) X Y)
    (fun l hl => by
      fin_cases l
      exacts [hmf 0, hmf 1, hmf 2, hmf 3, hX0, hY0, absurd rfl hl]) hk hu
  have hYne : mA M X Y i j j ^ 2 ≠ Y ^ 2 := by
    unfold mA
    split_ifs with h1 h2
    · exact ksB_sq_ne hM0 (by linarith)
    · exact ksB_sq_ne (by linarith) hXY
    · exact absurd le_rfl h2
  have hX1 : Function.update (mA M X Y i j) j Y i ^ 2 ≠ X ^ 2 := by
    by_cases hji : i = j
    · subst hji
      rw [Function.update_self]
      exact (ksB_sq_ne (by linarith) hXY).symm
    · rw [Function.update_of_ne hji]
      simp only [mA, le_refl, ite_true]
      exact ksB_sq_ne hM0 hMX
  have hX2 : mA M X Y i j i ^ 2 ≠ X ^ 2 := by
    simp only [mA, le_refl, ite_true]
    exact ksB_sq_ne hM0 hMX
  have hj := ksB_update_ge hmf j hY0
  obtain ⟨hInt, hEq⟩ := ksB_pieceA_merge base c k QA u hC4 i j (mA M X Y i j) hYne hX1 hX2 hI
    ⟨ksB_pos6 base c y₁ y₂ hflow hm₀ hk hu i hmf hX0,
      ksB_pos6 base c y₁ y₂ hflow hm₀ hk hu i hj hX0⟩
    ⟨ksB_pos5 base c y₁ y₂ hflow hm₀ hk hu hmf,
      ksB_pos5 base c y₁ y₂ hflow hm₀ hk hu (ksB_update_ge hmf i hX0),
      ksB_pos5 base c y₁ y₂ hflow hm₀ hk hu hj,
      ksB_pos5 base c y₁ y₂ hflow hm₀ hk hu (ksB_update_ge hj i hX0)⟩
  have hat : ∀ z, ksBAtom base c k QA u z = fun mf => C * ksBOf (ksBG base c k R u z) mf :=
    fun z => funext fun mf => by
      rw [ksBAtom_qsum base c k u Finset.univ (fun _ => C) (fun _ => R) rfl]
      simp [ksBOf_ksBG]
  simp only [hat] at hInt hEq
  refine ⟨hInt, ?_⟩
  rw [pairDens_eq hQA, ← hEq]
  have hupd : Function.update (![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2,
      mA M X Y i j 3, X, Y, 0] : Fin 7 → ℝ) (Fin.last 6) 0 =
      ![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2, mA M X Y i j 3, X, Y, 0] :=
    Function.update_eq_self_iff.2 rfl
  rw [hupd]
  rfl

/-- **A six-line piece of `triDens` on `Δ₄`.** -/
theorem ksB_pairDens_pieceB (i : Fin 4)
    (hcB : IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB i n))
    {M X Y : ℝ} (FX FM : (Fin 2 → Fin 4 → ℝ) → ℂ)
    (hpoly : IsLoopPoly 2 3 fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (FX ℓ - FM ℓ))
    (hB : RefinedBound (castLoopMatrix fun n => base (shB i n)) {0, 1, 2, 3, 4} 4
      fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (FX ℓ - FM ℓ))
    (RX RM : LoopQuartic) (hRX : RX.eval = FX) (hRM : RM.eval = FM)
    (hR4X : ∀ A, RX.contractFour A = 0) (hR4M : ∀ A, RM.contractFour A = 0)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (hM : m₀ ≤ M) (hMX : M < X) (hXY : X < Y)
    {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun y => ksBdd (fun mf => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
      (ksBOf (ksBG base c k RX u (simplexPoint y)) mf -
        ksBOf (ksBG base c k RM u (simplexPoint y)) mf)) (mB X Y i) i Y) (simplexSet 4) ∧
    pairDens (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (FX ℓ - FM ℓ))
        (castLoopMatrix fun l : Fin 6 => base (shB i l.castSucc))
        (fun l => c (shB i l.castSucc) • k)
        ![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, 0] (Fin.last 5) u =
      -((π : ℂ) ^ 4) * ∫ y in simplexSet 4, ksBdd (fun mf => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        (ksBOf (ksBG base c k RX u (simplexPoint y)) mf -
          ksBOf (ksBG base c k RM u (simplexPoint y)) mf)) (mB X Y i) i Y := by
  set D : ℂ := (Y : ℂ) ^ 2 - (M : ℂ) ^ 2 with hD
  set QB := qsum (Finset.univ : Finset (Fin 2)) ![-D, D] ![RX, RM] with hQB_def
  have hQB : QB.eval = fun ℓ => -D * (FX ℓ - FM ℓ) := by
    funext ℓ
    simp only [QB, eval_qsum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      hRX, hRM]
    ring
  have hC4 : ∀ A, QB.contractFour A = 0 := fun A => by
    simp [QB, contractFour_qsum, Fin.sum_univ_two, hR4X, hR4M]
  have hX0 : m₀ ≤ X := by linarith
  have hY0 : m₀ ≤ Y := by linarith
  have hmf : ∀ l, m₀ ≤ mB X Y i l := fun l => by unfold mB; split_ifs <;> linarith
  have hI := ksB_integrableOn_pieceF base c y₁ y₂ hflow (m := 5) (Or.inl rfl) (shB i)
    (fun l => by fin_cases l <;> simp [shB, Fin.ext_iff]; omega) hcB _ hpoly hB QB hQB hm₀
    (ksBM6 (mB X Y i) Y)
    (fun l hl => by
      fin_cases l
      exacts [hmf 0, hmf 1, hmf 2, hmf 3, hY0, absurd rfl hl]) hk hu
  have hYne : mB X Y i i ^ 2 ≠ Y ^ 2 := by
    simp only [mB, le_refl, ite_true]
    exact ksB_sq_ne (by linarith) hXY
  obtain ⟨hInt, hEq⟩ := ksB_pieceB_merge base c k QB u hC4 i (mB X Y i) hYne hI
    ⟨ksB_pos5 base c y₁ y₂ hflow hm₀ hk hu hmf,
      ksB_pos5 base c y₁ y₂ hflow hm₀ hk hu (ksB_update_ge hmf i hY0)⟩
  have hat : ∀ z, ksBAtom base c k QB u z = fun mf => -D *
      (ksBOf (ksBG base c k RX u z) mf - ksBOf (ksBG base c k RM u z) mf) :=
    fun z => funext fun mf => by
      rw [ksBAtom_qsum base c k u Finset.univ ![-D, D] ![RX, RM] rfl]
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, ksBOf_ksBG]
      ring
  simp only [hat] at hInt hEq
  refine ⟨hInt, ?_⟩
  rw [pairDens_eq hQB, ← hEq]
  have hupd : Function.update (![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, 0] :
      Fin 6 → ℝ) (Fin.last 5) 0 = ![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, 0] :=
    Function.update_eq_self_iff.2 rfl
  rw [hupd]
  rfl


/-- **The merged integrand of `triDens`** at the masses `(M, X, Y)`: the diagonal values of the
five-line integrands of the numerators at `M` and `X` (`ksB_leibniz`). -/
noncomputable def ksBTri (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (k : Fin 4 → ℝ)
    (R : ℝ → LoopQuartic) (M X Y u : ℝ) (y : Fin 4 → ℝ) : ℂ :=
  ksBG base c k (R M) u (simplexPoint y) M M M M +
    ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2) *
      ksBG base c k (R X) u (simplexPoint y) X X X X +
    ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) / ((Y : ℂ) ^ 2 - (X : ℂ) ^ 2) *
      ksBG base c k (R X) u (simplexPoint y) Y Y Y Y -
    ksBG base c k (R M) u (simplexPoint y) Y Y Y Y

/-- **`triDens` at the entry `(2, 3)` is one integral over `Δ₄`**, for a numerator whose
`m⁴` coefficient vanishes there and whose quartics `R m` have vanishing quartic contraction. -/
theorem ksB_triDens_eq
    (hcA : ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => base (shA i j n))
    (hcB : ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB i n))
    (Num : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (E0 E2 : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (E4 : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hE : ∀ m k ℓ a b, Num m k ℓ a b =
      E0 k ℓ a b + (m : ℂ) ^ 2 * E2 k ℓ a b + ((m : ℂ) ^ 2) ^ 2 * E4 k a b)
    (hP : ∀ m k a b, IsLoopPoly 2 4 fun ℓ => Num m k ℓ a b)
    (hP2 : ∀ k a b, IsLoopPoly 2 2 fun ℓ => E2 k ℓ a b)
    (hBA : ∀ m k a b i j, RefinedBound (castLoopMatrix fun n => base (shA i j n)) {0, 1, 2, 3} 4
      fun ℓ => Num m k ℓ a b)
    (hBB : ∀ m k a b i, RefinedBound (castLoopMatrix fun n => base (shB i n)) {0, 1, 2, 3} 4
      fun ℓ => Num m k ℓ a b)
    (k : Fin 4 → ℝ) (R : ℝ → LoopQuartic) (hR : ∀ m, (R m).eval = fun ℓ => Num m k ℓ 2 3)
    (hR4 : ∀ m A, (R m).contractFour A = 0) (hE4 : E4 k 2 3 = 0)
    {m₀ : ℝ} (hm₀ : 0 < m₀) {M X Y : ℝ} (hM : m₀ ≤ M) (hMX : M < X) (hXY : X < Y)
    (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (ksBTri base c k R M X Y u) (simplexSet 4) ∧
    triDens base c Num E4 M X Y u k 2 3 =
      -((π : ℂ) ^ 4) * ∫ y in simplexSet 4, ksBTri base c k R M X Y u y := by
  set fA : Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℂ := fun i j y => if i ≤ j then
    ksBdd (fun mf' => ksBdd (fun mf => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
      ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * ksBOf (ksBG base c k (R M) u (simplexPoint y)) mf) mf' i X)
      (mA M X Y i j) j Y else 0 with hfA
  set fB : Fin 4 → (Fin 4 → ℝ) → ℂ := fun i y => ksBdd (fun mf => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
      (ksBOf (ksBG base c k (R X) u (simplexPoint y)) mf -
        ksBOf (ksBG base c k (R M) u (simplexPoint y)) mf)) (mB X Y i) i Y with hfB
  have PA : ∀ i j, IntegrableOn (fA i j) (simplexSet 4) ∧
      (if i ≤ j then pairDens (fun ℓ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * Num M k ℓ 2 3)
        (castLoopMatrix fun l : Fin 7 => base (shA i j l.castSucc))
        (fun l => c (shA i j l.castSucc) • k)
        ![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2, mA M X Y i j 3, X, Y, 0]
        (Fin.last 6) u else 0) = -((π : ℂ) ^ 4) * ∫ y in simplexSet 4, fA i j y := by
    intro i j
    by_cases hij : i ≤ j
    · simp only [hfA, hij, ite_true]
      exact ksB_pairDens_pieceA base c y₁ y₂ hflow i j (hcA i j) (fun ℓ => Num M k ℓ 2 3)
        (hP M k 2 3) (hBA M k 2 3 i j) (R M) (hR M) (hR4 M) hm₀ hM hMX hXY hk hu
    · simp only [hfA, hij, ite_false, integral_zero, mul_zero]
      exact ⟨integrableOn_zero, trivial⟩
  have PB : ∀ i, IntegrableOn (fB i) (simplexSet 4) ∧
      pairDens (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ 2 3 - Num M k ℓ 2 3))
        (castLoopMatrix fun l : Fin 6 => base (shB i l.castSucc))
        (fun l => c (shB i l.castSucc) • k)
        ![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, 0] (Fin.last 5) u =
      -((π : ℂ) ^ 4) * ∫ y in simplexSet 4, fB i y := by
    intro i
    have hpoly : IsLoopPoly 2 3 fun ℓ =>
        -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ 2 3 - Num M k ℓ 2 3) := by
      have e : (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ 2 3 - Num M k ℓ 2 3)) =
          fun ℓ => (-((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2)) *
            (E2 k ℓ 2 3 + ((M : ℂ) ^ 2 + (X : ℂ) ^ 2) * E4 k 2 3) := by
        funext ℓ; rw [hE, hE]; ring
      rw [e]
      exact (((hP2 k 2 3).add (IsLoopPoly.const _)).const_mul _).mono (by norm_num)
    exact ksB_pairDens_pieceB base c y₁ y₂ hflow i (hcB i) (fun ℓ => Num X k ℓ 2 3)
      (fun ℓ => Num M k ℓ 2 3) hpoly
      ((((hBB X k 2 3 i).sub (hBB M k 2 3 i)).const_mul _).mono (by decide) le_rfl)
      (R X) (R M) (hR X) (hR M) (hR4 X) (hR4 M) hm₀ hM hMX hXY hk hu
  have PC : pairDens (fun ℓ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
      E4 k 2 3 * propDenom Y 0 (fm base (ppc c k) 0 ℓ))
      (castLoopMatrix fun l : Fin 6 => base (shB 0 l.castSucc))
      (fun l => c (shB 0 l.castSucc) • k) ![Y, Y, Y, Y, Y, 0] (Fin.last 5) u = 0 := by
    simp only [hE4, mul_zero, zero_mul]
    exact ksB_pairDens_zero _ _ _ _ _
  have hIA : ∀ i, IntegrableOn (fun y => ∑ j, fA i j y) (simplexSet 4) :=
    fun i => integrable_finsetSum _ fun j _ => (PA i j).1
  have hIAA : IntegrableOn (fun y => ∑ i, ∑ j, fA i j y) (simplexSet 4) :=
    integrable_finsetSum _ fun i _ => hIA i
  have hIB : IntegrableOn (fun y => ∑ i, fB i y) (simplexSet 4) :=
    integrable_finsetSum _ fun i _ => (PB i).1
  have hM0 : 0 < M := by linarith
  have hpt : ∀ y, (∑ i, ∑ j, fA i j y) + ∑ i, fB i y = ksBTri base c k R M X Y u y := fun y =>
    ksB_leibniz _ _ (ksB_sq_ne hM0 hMX) (ksB_sq_ne hM0 (by linarith))
      (ksB_sq_ne (by linarith) hXY)
  have hsum : (fun y => (∑ i, ∑ j, fA i j y) + ∑ i, fB i y) = ksBTri base c k R M X Y u :=
    funext hpt
  refine ⟨hsum ▸ hIAA.add hIB, ?_⟩
  rw [triDens]
  simp only [fun i j => (PA i j).2, fun i => (PB i).2, PC, add_zero]
  rw [← hsum, integral_add hIAA hIB, integral_finsetSum _ fun i _ => hIA i,
    integral_finsetSum _ fun i _ => (PB i).1, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (PA i j).1, Finset.mul_sum]

/-! ### The flavour sum -/

/-- **A class density `vDens` at the entry `(2, 3)` is one integral over `Δ₄`** of the
flavour-summed five-line integrand, under the two Pauli–Villars conditions. -/
theorem ksB_vDens_eq (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (e : ℝ)
    (hA : ∀ σ, ∃ s : Fin 4 → ℂ, (∀ l, KsFlip (A 2 3 σ σ l) (s l)) ∧ s 0 * s 1 * s 2 * s 3 = -1)
    (hodd : ∀ a b ρ σ l, IsOddG (A a b ρ σ l))
    (hcA : ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => base (shA i j n))
    (hcB : ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB i n))
    (hBA : ∀ m k a b i j, RefinedBound (castLoopMatrix fun n => base (shA i j n)) {0, 1, 2, 3} 4
      fun ℓ => vNum e 0 1 A base c m k ℓ a b)
    (hBB : ∀ m k a b i, RefinedBound (castLoopMatrix fun n => base (shB i n)) {0, 1, 2, 3} 4
      fun ℓ => vNum e 0 1 A base c m k ℓ a b)
    {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hPV₁ : ∑ f, Φ.coeff f = 0)
    (hPV₂ : ∑ f, Φ.coeff f * Φ.mass f ^ 2 = 0) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k)
    {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun y => ∑ f, (Φ.coeff f : ℂ) * ksBAtom base c k
      (ksBRep e A base c (Φ.mass f) k) u (simplexPoint y) fun _ => Φ.mass f) (simplexSet 4) ∧
    vDens A base c Φ e m₀ u k 2 3 = -((π : ℂ) ^ 4) * ∫ y in simplexSet 4, ∑ f,
      (Φ.coeff f : ℂ) * ksBAtom base c k (ksBRep e A base c (Φ.mass f) k) u (simplexPoint y)
        fun _ => Φ.mass f := by
  set R : ℝ → LoopQuartic := fun m => ksBRep e A base c m k with hRdef
  set X := blockX Φ m₀ with hXdef
  have hR : ∀ m, (R m).eval = fun ℓ => vNum e 0 1 A base c m k ℓ 2 3 := fun m =>
    ksBRep_eval e A base c m k
  have hR4 : ∀ m A', (R m).contractFour A' = 0 := fun m A' =>
    ksBRep_contractFour e A base c hA m k A'
  have hE4 := ksB_vNumE4_eq_zero e A hA k
  have hS0 : ∀ f, Φ.mass f < X := fun f => by
    have h0 : ∀ g ∈ Finset.univ, 0 ≤ Φ.mass g := fun g _ => hm₀.le.trans (hmass g)
    have := Finset.single_le_sum h0 (Finset.mem_univ f)
    simp only [hXdef, blockX]
    linarith
  have T : ∀ f, IntegrableOn (ksBTri base c k R (Φ.mass f) X (X + 1) u) (simplexSet 4) ∧
      triDens base c (vNum e 0 1 A base c) (vNumE4 e 0 1 A) (Φ.mass f) X (X + 1) u k 2 3 =
        -((π : ℂ) ^ 4) * ∫ y in simplexSet 4, ksBTri base c k R (Φ.mass f) X (X + 1) u y :=
    fun f => ksB_triDens_eq base c y₁ y₂ hflow hcA hcB _ _ _ _
      (vNum_eq e 0 1 A base c hodd) (isLoopPoly_vNum e 0 1 A base c)
      (isLoopPoly_vNumE2 e 0 1 A base c) hBA hBB k R hR hR4 hE4 hm₀ (hmass f) (hS0 f)
      (by linarith) hk hu
  -- the numerator is affine in the squared mass
  have hlin : ∀ m z mf, ksBAtom base c k (R m) u z mf = (1 - (m : ℂ) ^ 2) *
      ksBAtom base c k (R 0) u z mf + (m : ℂ) ^ 2 * ksBAtom base c k (R 1) u z mf := by
    intro m z mf
    have h : (R m).eval = (qsum Finset.univ ![1 - (m : ℂ) ^ 2, (m : ℂ) ^ 2] ![R 0, R 1]).eval := by
      funext ℓ
      simp only [eval_qsum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hR]
      rw [vNum_eq e 0 1 A base c hodd, vNum_eq e 0 1 A base c hodd,
        vNum_eq e 0 1 A base c hodd, hE4]
      push_cast
      ring
    rw [ksBAtom_qsum base c k u Finset.univ _ _ h]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hpt : ∀ y, ∑ f, (Φ.coeff f : ℂ) * ksBTri base c k R (Φ.mass f) X (X + 1) u y =
      ∑ f, (Φ.coeff f : ℂ) * ksBAtom base c k (R (Φ.mass f)) u (simplexPoint y)
        fun _ => Φ.mass f := by
    intro y
    set z := simplexPoint y
    set hX := ksBAtom base c k (R X) u z ![X, X, X, X]
    set hY := ksBAtom base c k (R X) u z ![X + 1, X + 1, X + 1, X + 1]
    set g0 := ksBAtom base c k (R 0) u z ![X + 1, X + 1, X + 1, X + 1]
    set g1 := ksBAtom base c k (R 1) u z ![X + 1, X + 1, X + 1, X + 1]
    set K0 : ℂ := ((X + 1 : ℝ) : ℂ) ^ 2 / ((X : ℂ) ^ 2 - ((X + 1 : ℝ) : ℂ) ^ 2) * hX +
      ((X + 1 : ℝ) : ℂ) ^ 2 / (((X + 1 : ℝ) : ℂ) ^ 2 - (X : ℂ) ^ 2) * hY - g0
    set K1 : ℂ := -hX / ((X : ℂ) ^ 2 - ((X + 1 : ℝ) : ℂ) ^ 2) -
      hY / (((X + 1 : ℝ) : ℂ) ^ 2 - (X : ℂ) ^ 2) + g0 - g1
    have e1 : ∀ f, ksBTri base c k R (Φ.mass f) X (X + 1) u y =
        ksBAtom base c k (R (Φ.mass f)) u z (fun _ => Φ.mass f) +
          (K0 + ((Φ.mass f : ℝ) : ℂ) ^ 2 * K1) := fun f => by
      have hc : ksBAtom base c k (R (Φ.mass f)) u z ![Φ.mass f, Φ.mass f, Φ.mass f, Φ.mass f] =
          ksBAtom base c k (R (Φ.mass f)) u z fun _ => Φ.mass f := rfl
      simp only [ksBTri, ksBG]
      rw [hlin (Φ.mass f) z ![X + 1, X + 1, X + 1, X + 1], hc]
      simp only [K0, K1, hX, hY, g0, g1, z]
      ring
    simp only [e1, mul_add, Finset.sum_add_distrib]
    have p1 : ∑ f, (Φ.coeff f : ℂ) * K0 = 0 := by
      rw [← Finset.sum_mul]; exact mul_eq_zero_of_left (by exact_mod_cast hPV₁) _
    have p2 : ∑ f, (Φ.coeff f : ℂ) * (((Φ.mass f : ℝ) : ℂ) ^ 2 * K1) = 0 := by
      simp only [← mul_assoc, ← Finset.sum_mul]
      exact mul_eq_zero_of_left (by exact_mod_cast hPV₂) _
    rw [p1, p2, add_zero, add_zero]
  have hint : IntegrableOn (fun y => ∑ f, (Φ.coeff f : ℂ) *
      ksBTri base c k R (Φ.mass f) X (X + 1) u y) (simplexSet 4) :=
    integrable_finsetSum _ fun f _ => (T f).1.const_mul _
  refine ⟨(funext hpt) ▸ hint, ?_⟩
  rw [vDens, blockDens, ← hXdef, ← funext hpt,
    integral_finsetSum _ fun f _ => (T f).1.const_mul _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [(T f).2, integral_const_mul]
  ring

end Pieces

/-! ### The three classes -/

section Classes

variable {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hPV₁ : ∑ f, Φ.coeff f = 0)
  (hPV₂ : ∑ f, Φ.coeff f * Φ.mass f ^ 2 = 0) {m₀ : ℝ} (hm₀ : 0 < m₀)
  (hmass : ∀ g, m₀ ≤ Φ.mass g) (e : ℝ) {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k)
  {u : ℝ} (hu : 0 < u)

include hPV₁ hPV₂ hm₀ hmass hk hu

/-- **The class `VA` at the entry `(2, 3)`** as one integral over `Δ₄` (`ksB_vDens_eq`). -/
theorem ksB_vDens_VA :
    IntegrableOn (fun y => ∑ f, (Φ.coeff f : ℂ) * ksBAtom baseVA cVA k
      (ksBRep e aVA baseVA cVA (Φ.mass f) k) u (simplexPoint y) fun _ => Φ.mass f)
      (simplexSet 4) ∧
    vDens aVA baseVA cVA Φ e m₀ u k 2 3 = -((π : ℂ) ^ 4) * ∫ y in simplexSet 4, ∑ f,
      (Φ.coeff f : ℂ) * ksBAtom baseVA cVA k (ksBRep e aVA baseVA cVA (Φ.mass f) k) u
        (simplexPoint y) fun _ => Φ.mass f :=
  ksB_vDens_eq baseVA cVA ![0, 0] ![-1, -1] flowVA aVA e ksB_flip_VA
    (fun a b ρ σ => isOddG_aVA a b ρ σ) critA_VA critB_VA
    (fun m k a' b' i j => rb_vNum e 0 1 aVA baseVA cVA (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVA baseVA cVA (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b') Φ hPV₁ hPV₂ hm₀ hmass hk hu

/-- **The class `VB` at the entry `(2, 3)`** as one integral over `Δ₄` (`ksB_vDens_eq`). -/
theorem ksB_vDens_VB :
    IntegrableOn (fun y => ∑ f, (Φ.coeff f : ℂ) * ksBAtom baseVB cVB k
      (ksBRep e aVB baseVB cVB (Φ.mass f) k) u (simplexPoint y) fun _ => Φ.mass f)
      (simplexSet 4) ∧
    vDens aVB baseVB cVB Φ e m₀ u k 2 3 = -((π : ℂ) ^ 4) * ∫ y in simplexSet 4, ∑ f,
      (Φ.coeff f : ℂ) * ksBAtom baseVB cVB k (ksBRep e aVB baseVB cVB (Φ.mass f) k) u
        (simplexPoint y) fun _ => Φ.mass f :=
  ksB_vDens_eq baseVB cVB ![0, 1] ![-1, 0] flowVB aVB e ksB_flip_VB
    (fun a b ρ σ => isOddG_aVB a b ρ σ) critA_VB critB_VB
    (fun m k a' b' i j => rb_vNum e 0 1 aVB baseVB cVB (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVB baseVB cVB (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b') Φ hPV₁ hPV₂ hm₀ hmass hk hu

/-- **The class `VC` at the entry `(2, 3)`** as one integral over `Δ₄` (`ksB_vDens_eq`). -/
theorem ksB_vDens_VC :
    IntegrableOn (fun y => ∑ f, (Φ.coeff f : ℂ) * ksBAtom baseVC cVC k
      (ksBRep e aVC baseVC cVC (Φ.mass f) k) u (simplexPoint y) fun _ => Φ.mass f)
      (simplexSet 4) ∧
    vDens aVC baseVC cVC Φ e m₀ u k 2 3 = -((π : ℂ) ^ 4) * ∫ y in simplexSet 4, ∑ f,
      (Φ.coeff f : ℂ) * ksBAtom baseVC cVC k (ksBRep e aVC baseVC cVC (Φ.mass f) k) u
        (simplexPoint y) fun _ => Φ.mass f :=
  ksB_vDens_eq baseVC cVC ![0, 1] ![-1, 0] flowVC aVC e ksB_flip_VC
    (fun a b ρ σ => isOddG_aVC a b ρ σ) critA_VC critB_VC
    (fun m k a' b' i j => rb_vNum e 0 1 aVC baseVC cVC (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVC baseVC cVC (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b') Φ hPV₁ hPV₂ hm₀ hmass hk hu

end Classes

end QED.ChainProof.SetAKS

end
