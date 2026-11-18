/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.LeptonProof.HMBracket
public import QED.Frozen.OneLoop.IsFormFactorPair
public import QED.TwoLoop.FormFactorClause
public import QED.TwoLoop.PauliZero
import QED.Algebra.FormFactorProjector

/-!
# Tools for the assembly of (HM₂)

Helper level, Phase 5 Stage 0 (decision D-50).

* `isFormFactorPair_add`, `isFormFactorPair_smul`, `isFormFactorPair_sum`: the form-factor
  decomposition (G₀) is linear in the pair `(V, F)`.
* `exists_isVertexOrderFiveLimit_t1`, `uniform_pauli_t1`: T1's form-factor clause and uniform
  `q² → 0⁺` limit at a fixed admissible parameter set (`T1Adm`), restated for an arbitrary `X`.
* `exists_pos_le_forall`, `le_sum_abs`: finite minima and maxima of thresholds.
* `auxOK_of`, `auxGt_of`: the auxiliary masses `X_ℓ = m_ℓ + M_{ℓ,1} + M_{ℓ,2}` are admissible.
-/

@[expose] public section

open Complex Finset Matrix Filter Topology
open QED.WickModel (Params)

namespace QED.Lepton.Proof.HM

/-! ### Linearity of (G₀) -/

section FormFactor

variable {e m : ℝ} {p' p : Fin 4 → ℝ}

theorem isFormFactorPair_add {V W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {F G : ℂ × ℂ}
    (hV : QED.OneLoop.IsFormFactorPair e m p' p V F)
    (hW : QED.OneLoop.IsFormFactorPair e m p' p W G) :
    QED.OneLoop.IsFormFactorPair e m p' p (V + W) (F + G) := by
  intro μ u w hu hw
  have h1 := hV μ u w hu hw
  have h2 := hW μ u w hu hw
  simp only [Pi.add_apply, Matrix.add_mulVec, dotProduct_add, h1, h2, Prod.fst_add,
    Prod.snd_add, add_smul, mul_add, sub_eq_add_neg, neg_add, Matrix.add_mulVec, Matrix.neg_mulVec]
  ring

theorem isFormFactorPair_smul {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {F : ℂ × ℂ} (c : ℂ)
    (hV : QED.OneLoop.IsFormFactorPair e m p' p V F) :
    QED.OneLoop.IsFormFactorPair e m p' p (c • V) (c • F) := by
  intro μ u w hu hw
  have h1 := hV μ u w hu hw
  simp only [Pi.smul_apply, Matrix.smul_mulVec, dotProduct_smul, h1, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, sub_eq_add_neg, Matrix.add_mulVec, Matrix.neg_mulVec,
    dotProduct_add, dotProduct_neg, mul_smul, Matrix.smul_mulVec]
  ring

theorem isFormFactorPair_zero : QED.OneLoop.IsFormFactorPair e m p' p 0 0 := by
  intro μ u w _ _
  simp

theorem isFormFactorPair_sum {ι : Type*} (s : Finset ι)
    {V : ι → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {F : ι → ℂ × ℂ}
    (h : ∀ i ∈ s, QED.OneLoop.IsFormFactorPair e m p' p (V i) (F i)) :
    QED.OneLoop.IsFormFactorPair e m p' p (∑ i ∈ s, V i) (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isFormFactorPair_zero
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact isFormFactorPair_add (h a (mem_insert_self a s))
      (ih fun i hi => h i (mem_insert_of_mem hi))

end FormFactor

/-! ### T1 at a fixed admissible parameter set -/

open QED.TwoLoop.FormFactorClause in
/-- T1's form-factor clause at `X`. -/
theorem exists_isVertexOrderFiveLimit_t1 {X : Params} (hX : T1Adm X) (he : X.e ≠ 0)
    {p' p : Fin 4 → ℝ} (hp' : QED.Minkowski.dot p' p' = -X.m ^ 2)
    (hp : QED.Minkowski.dot p p = -X.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
    (hq : 0 < QED.Minkowski.dot (p' - p) (p' - p)) :
    (∃ V, QED.TwoLoop.IsVertexOrderFiveLimit X p' p V) ∧
      ∀ V, QED.TwoLoop.IsVertexOrderFiveLimit X p' p V →
        ∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair X.e X.m p' p V F := by
  obtain ⟨h1, h2⟩ :=
    exists_isVertexOrderFiveLimit_and_existsUnique_isFormFactorPair_headline
    X he hX.hm X.M₁ X.M₂ X.c₁ X.c₂ hX.hM₁ hX.hM₂ hX.pv₁ hX.pv₂ X.mγ X.Λ hX.hmγ
    (hX.hmγ.trans hX.hmΛ) X.δ₁ X.δ₂ X.δm X.δ₃ p' p hp' hp hp0' hp0 hq
  exact ⟨h1, fun V hV => (h2 V hV).1⟩

/-- T1's uniform `q² → 0⁺` limit at `X`. -/
theorem uniform_pauli_t1 {X : Params} (hX : T1Adm X) (he : X.e ≠ 0) {τ : ℝ} (hτ : 0 < τ) :
    ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, QED.Minkowski.dot p p = -X.m ^ 2 →
      QED.Minkowski.dot p' p' = -X.m ^ 2 → 0 < p 0 → 0 < p' 0 →
      0 < QED.Minkowski.dot (p' - p) (p' - p) → QED.Minkowski.dot (p' - p) (p' - p) < q₀ →
      ∀ V, QED.TwoLoop.IsVertexOrderFiveLimit X p' p V → ∀ F : ℂ × ℂ,
        QED.OneLoop.IsFormFactorPair X.e X.m p' p V F →
          ‖F.2 - QED.TwoLoop.PauliZeroLimit.pauliZeroLimit X X.e‖ < τ := by
  have hΛ := hX.hmγ.trans hX.hmΛ
  exact QED.TwoLoop.PauliZero.uniform_isFormFactorPair_of_tendsto_pauliAt X hX.hm hX.hmγ hΛ
    hX.hM₁.le hX.hM₂.le hX.pv₁ hX.pv₂ he
    (QED.TwoLoop.PauliZeroLimit.tendsto_pauliZeroLimit X hX.hm hX.hmγ hΛ hX.hM₁.le hX.hM₂.le
      hX.pv₁ hX.pv₂ X.e) τ hτ

/-! ### Finite minima and maxima -/

theorem exists_pos_le_forall {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ δ > 0, ∀ i, δ ≤ f i := by
  classical
  by_cases hι : Nonempty ι
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
    exact ⟨f i₀, hf i₀, fun i => hi₀ i (Finset.mem_univ i)⟩
  · exact ⟨1, one_pos, fun i => absurd ⟨i⟩ hι⟩

theorem le_sum_abs {ι : Type*} [Fintype ι] (f : ι → ℝ) (i : ι) : f i ≤ ∑ j, |f j| :=
  (le_abs_self (f i)).trans (Finset.single_le_sum (fun j _ => abs_nonneg (f j))
    (Finset.mem_univ i))

/-! ### The auxiliary masses -/

/-- The auxiliary mass of a heavy lepton: the sum of its three loop masses. -/
def auxMass (h : HeavyLepton) : ℝ := h.m + h.M₁ + h.M₂

theorem hMass_lt_auxMass {h : HeavyLepton} (h0 : 0 < h.m) (h1 : h.m < h.M₁) (h2 : h.m < h.M₂)
    (j : Fin 3) : hMass h j < auxMass h := by
  fin_cases j <;> simp [hMass, auxMass] <;> linarith

theorem auxOK_of {n : ℕ} {H : Fin n → HeavyLepton} {m : ℝ} (hm : 0 < m)
    (hmH : ∀ ℓ, m < (H ℓ).m) (h1 : ∀ ℓ, (H ℓ).m < (H ℓ).M₁) (h2 : ∀ ℓ, (H ℓ).m < (H ℓ).M₂)
    (pv₁ : ∀ ℓ, 1 + (H ℓ).c₁ + (H ℓ).c₂ = 0)
    (pv₂ : ∀ ℓ, (H ℓ).m ^ 2 + (H ℓ).c₁ * (H ℓ).M₁ ^ 2 + (H ℓ).c₂ * (H ℓ).M₂ ^ 2 = 0) :
    AuxOK H (fun ℓ => auxMass (H ℓ)) m := by
  have h0 : ∀ ℓ, 0 < (H ℓ).m := fun ℓ => hm.trans (hmH ℓ)
  have hpos : ∀ ℓ j, 0 < hMass (H ℓ) j := fun ℓ j => by
    fin_cases j <;> simp [hMass] <;> linarith [h0 ℓ, h1 ℓ, h2 ℓ]
  refine ⟨pv₁, pv₂, fun ℓ => ?_, fun ℓ j => ?_⟩
  · have := hMass_lt_auxMass (h0 ℓ) (h1 ℓ) (h2 ℓ) 0
    have h3 : m < auxMass (H ℓ) := (hmH ℓ).trans (by simpa [hMass] using this)
    nlinarith
  · have := hMass_lt_auxMass (h0 ℓ) (h1 ℓ) (h2 ℓ) j
    have := hpos ℓ j
    nlinarith

theorem auxGt_of {n : ℕ} {H : Fin n → HeavyLepton} {m : ℝ} (hm : 0 < m)
    (hmH : ∀ ℓ, m < (H ℓ).m) (h1 : ∀ ℓ, (H ℓ).m < (H ℓ).M₁) (h2 : ∀ ℓ, (H ℓ).m < (H ℓ).M₂) :
    AuxGt H (fun ℓ => auxMass (H ℓ)) m := by
  have h0 : ∀ ℓ, 0 < (H ℓ).m := fun ℓ => hm.trans (hmH ℓ)
  refine ⟨fun ℓ j => ?_, fun ℓ => ?_⟩
  · fin_cases j <;> simp [hMass] <;> linarith [hmH ℓ, h1 ℓ, h2 ℓ]
  · have := hMass_lt_auxMass (h0 ℓ) (h1 ℓ) (h2 ℓ) 0
    exact (hmH ℓ).trans (by simpa [hMass] using this)

end QED.Lepton.Proof.HM

end
