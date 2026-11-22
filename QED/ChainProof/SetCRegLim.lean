/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAPauliAssembly
public import QED.ChainProof.SetCLimCtCB01Link
public import QED.ChainProof.SetCLimCtCD01
public import QED.ChainProof.SetCMirror
public import QED.ChainProof.SetCPauliAtCt

/-!
# The set (c) regulator limit over distinct regulator masses, and the headline assembly

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`
(`QED/Frozen/ThreeLoop/VertexSetCPauliLimit.lean`, `DRAFT_SORRY`, not imported).

**The diagonal.** The regulator limit `QED.ChainProof.SetCPauli.SetCRegLimit a` of
`QED/ChainProof/SetCPauliCond.lean` quantifies over all large `M₁, M₂`, including `M₁ = M₂`. No
admissible regulator has `M₁ = M₂` (`QED.ChainProof.SetAPauliAssembly.ne_of_pv`: the
Pauli–Villars conditions force `m² = M₁²`), so the fixed link `SetCFixedLink P₀ a` and the
canonical Pauli limit `SetCPauliAt P₀ b` say nothing about `a`, `b` there, while a closed-form
fixed-regulator value (such as set (a)'s `setAR`, `QED.ChainProof.SetAPauliAssemblyR`) can take
the wrong value on the diagonal, where `SetCRegLimit` then fails. As for set (a), the regulator
limit is to be proved over distinct masses (`SetCRegLimitPV`), and the value is patched to
`A₁⁽⁶⁾(c)` on the diagonal (`patchC`): the patched value has the same fixed link
(`setCFixedLink_patch`) and satisfies `SetCRegLimit` (`setCRegLimit_patch`). The frozen
statement is unchanged.

## Main statements

* `SetCRegLimitPV a`: the regulator limit over `M₁ ≠ M₂`;
* `setCFixedLink_patch`, **`setCRegLimit_patch`**;
* `SetCRegLimitB P₀ b`, **`setCRegLimitPV_of_b`**: the regulator limit of the canonical Pauli value
  `b`, `b → e⁶ A₁⁽⁶⁾(c)/(64π⁶)`, gives `SetCRegLimitPV (setCPauliValue P₀ b)` for `e ≠ 0`;
* **`isFormFactorPair_vertexSetC_pauli_limit_of_pauliAt`**: the proposition of (HS₆) from the
  limit and covariance links, the canonical Pauli limit and the regulator limit over `M₁ ≠ M₂`;
* **`isFormFactorPair_vertexSetC_pauli_limit_of_main`**: the proposition of (HS₆) from the limit,
  covariance and per-class Pauli links of the 36 main classes, the per-class Pauli links of the
  four classes `CB0`, `CB1`, `CD0 t`, `CD1 t`, the sum of the class values, and the regulator
  limit over `M₁ ≠ M₂`.
-/

@[expose] public section

open Complex Filter Topology
open scoped Real
open QED.WickModel (Params IsOnePI)

namespace QED.ChainProof.SetCPauli

open QED.ChainProof.SetAPauli (regParams regFlavors)

/-! ### The regulator limit over distinct masses -/

/-- **The regulator limit of (HS₆) over `M₁ ≠ M₂`** (open for a given `a`): the fixed-regulator
value `a` tends to `A₁⁽⁶⁾(c)` in the iterated order of D-37.4, the regulator fermion masses
ranging over distinct pairs (the admissible ones). -/
def SetCRegLimitPV (a : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ η > 0, ∃ RM : ℝ, ∀ M₁ M₂ : ℝ, RM < M₁ → RM < M₂ → M₁ ≠ M₂ → ∃ δ > 0, ∃ Λ₀ : ℝ,
    ∀ mγ Λ : ℝ, 0 < mγ → mγ < δ → Λ₀ < Λ → |a mγ Λ M₁ M₂ - ThreeLoop.a1SixSetC| < η

open scoped Classical in
/-- The fixed-regulator value patched to `A₁⁽⁶⁾(c)` at `M₁ = M₂`. -/
noncomputable def patchC (a : ℝ → ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun mγ Λ M₁ M₂ => if M₁ = M₂ then ThreeLoop.a1SixSetC else a mγ Λ M₁ M₂

/-- The patched value has the same fixed link. -/
theorem setCFixedLink_patch {P₀ : Params} {a : ℝ → ℝ → ℝ → ℝ → ℝ} (hm : 0 < P₀.m)
    (h : SetCFixedLink P₀ a) : SetCFixedLink P₀ (patchC a) := by
  intro M₁ M₂ c₁ c₂ mγ Λ hM₁ hM₂ hPV₁ hPV₂ hmγ hΛ hmΛ hm2 D hD s hs η hη
  have hp : patchC a mγ Λ M₁ M₂ = a mγ Λ M₁ M₂ := by
    simp [patchC, QED.ChainProof.SetAPauliAssembly.ne_of_pv hm hM₁ hPV₁ hPV₂]
  rw [hp]
  exact h M₁ M₂ c₁ c₂ mγ Λ hM₁ hM₂ hPV₁ hPV₂ hmγ hΛ hmΛ hm2 D hD s hs η hη

/-- **The patched value satisfies the regulator limit of (HS₆).** -/
theorem setCRegLimit_patch {a : ℝ → ℝ → ℝ → ℝ → ℝ} (h : SetCRegLimitPV a) :
    SetCRegLimit (patchC a) := by
  intro η hη
  obtain ⟨RM, hRM⟩ := h η hη
  refine ⟨RM, fun M₁ M₂ h₁ h₂ => ?_⟩
  by_cases hM : M₁ = M₂
  · exact ⟨1, one_pos, 0, fun mγ Λ _ _ _ => by simp [patchC, hM, hη]⟩
  · obtain ⟨δ, hδ, Λ₀, hΛ₀⟩ := hRM M₁ M₂ h₁ h₂ hM
    exact ⟨δ, hδ, Λ₀, fun mγ Λ h0 h1 h2 => by
      simpa [patchC, hM] using hΛ₀ mγ Λ h0 h1 h2⟩

/-- **The regulator limit of the canonical Pauli value `b`** over `M₁ ≠ M₂` (open for a given
`b`): `b → e⁶ A₁⁽⁶⁾(c) / (64π⁶)` in the iterated order of D-37.4. -/
def SetCRegLimitB (P₀ : Params) (b : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ η > 0, ∃ RM : ℝ, ∀ M₁ M₂ : ℝ, RM < M₁ → RM < M₂ → M₁ ≠ M₂ → ∃ δ > 0, ∃ Λ₀ : ℝ,
    ∀ mγ Λ : ℝ, 0 < mγ → mγ < δ → Λ₀ < Λ →
      |b mγ Λ M₁ M₂ - P₀.e ^ 6 * ThreeLoop.a1SixSetC / (64 * π ^ 6)| < η

/-- **The regulator limit of `b` gives that of `a = 64π⁶ b / e⁶`.** -/
theorem setCRegLimitPV_of_b {P₀ : Params} {b : ℝ → ℝ → ℝ → ℝ → ℝ} (he : P₀.e ≠ 0)
    (h : SetCRegLimitB P₀ b) : SetCRegLimitPV (setCPauliValue P₀ b) := by
  intro η hη
  have hK : 0 < 64 * π ^ 6 / P₀.e ^ 6 := by
    have : 0 < P₀.e ^ 6 := by positivity
    positivity
  obtain ⟨RM, hRM⟩ := h (η / (64 * π ^ 6 / P₀.e ^ 6)) (div_pos hη hK)
  refine ⟨RM, fun M₁ M₂ h₁ h₂ hM => ?_⟩
  obtain ⟨δ, hδ, Λ₀, hΛ₀⟩ := hRM M₁ M₂ h₁ h₂ hM
  refine ⟨δ, hδ, Λ₀, fun mγ Λ h0 h1 h2 => ?_⟩
  have hb := hΛ₀ mγ Λ h0 h1 h2
  have e : setCPauliValue P₀ b mγ Λ M₁ M₂ - ThreeLoop.a1SixSetC =
      64 * π ^ 6 / P₀.e ^ 6 *
        (b mγ Λ M₁ M₂ - P₀.e ^ 6 * ThreeLoop.a1SixSetC / (64 * π ^ 6)) := by
    unfold setCPauliValue
    have he6 : P₀.e ^ 6 ≠ 0 := pow_ne_zero 6 he
    have hπ : (64 * π ^ 6 : ℝ) ≠ 0 := by positivity
    field_simp
  rw [e, abs_mul, abs_of_pos hK]
  calc 64 * π ^ 6 / P₀.e ^ 6 *
        |b mγ Λ M₁ M₂ - P₀.e ^ 6 * ThreeLoop.a1SixSetC / (64 * π ^ 6)|
      < 64 * π ^ 6 / P₀.e ^ 6 * (η / (64 * π ^ 6 / P₀.e ^ 6)) :=
        mul_lt_mul_of_pos_left hb hK
    _ = η := by field_simp

/-! ### The headline proposition -/

/-- **(HS₆) from the limit and covariance links, the canonical Pauli limit and the regulator
limit over `M₁ ≠ M₂`.** The conclusion is, verbatim, the proposition of the frozen
`QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. -/
theorem isFormFactorPair_vertexSetC_pauli_limit_of_pauliAt {b : ℝ → ℝ → ℝ → ℝ → ℝ}
    (P₀ : Params) (hL : SetCLimitLink P₀) (hC : SetCCovLink P₀) (hB : SetCPauliAt P₀ b)
    (hreg : SetCRegLimitPV (setCPauliValue P₀ b)) (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (η : ℝ)
    (hη : 0 < η) :
    ∃ RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
      1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
      ∃ δ > 0, ∃ R : ℝ, ∀ mγ Λ : ℝ, 0 < mγ → 0 < Λ → mγ < δ → R < Λ →
        (∃ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2) ∧
        ∀ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2 →
          (∃ s : ℝ × ℝ × ℝ, ThreeLoop.IsVPShareOnShell
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D s) ∧
          ∀ s : ℝ × ℝ × ℝ, ThreeLoop.IsVPShareOnShell
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D s →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) (D.withLevel 1 (fun _ => s) (D.d₃ 1))
              (fun C g => IsOnePI C ∧ ThreeLoop.IsSetC C g) 7 p' p V) ∧
            ∀ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) (D.withLevel 1 (fun _ => s) (D.d₃ 1))
              (fun C g => IsOnePI C ∧ ThreeLoop.IsSetC C g) 7 p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 -
                  (ThreeLoop.a1SixSetC : ℂ)‖ < η :=
  isFormFactorPair_vertexSetC_pauli_limit_of_links P₀
    (setCFixedLink_patch hm (setCFixedLink_of_pauliAt he hm hL hC (SetCMirror.setCMirrorAt P₀)
      hB))
    (setCRegLimit_patch hreg) he hm η hη

/-- **(HS₆) from the 36 main classes, four counterterm classes and the regulator limit.** The
inputs are the limit, covariance and per-class Pauli links of the 36 two-loop-outer classes, the
per-class Pauli links of `CB0`, `CB1`, `CD0 t`, `CD1 t` (their limit and covariance links are
proved, `QED/ChainProof/SetCLimCtCB01Link.lean` and `QED/ChainProof/SetCLimCtCD01.lean`), a real
`b` equal to `(1/i)` times the sum of the 56 class values, and the regulator limit of
`a = 64π⁶ b / e⁶` over `M₁ ≠ M₂`. The conclusion is, verbatim, the proposition of the frozen
`QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. -/
theorem isFormFactorPair_vertexSetC_pauli_limit_of_main {b : ℝ → ℝ → ℝ → ℝ → ℝ}
    {βM : MainIdx → ClsPauliVal} {βx : CtIdx → ClsPauliVal} (P₀ : Params)
    (hM : ∀ r, SetCClassLim mainFam P₀ r) (hMc : ∀ r, SetCClassCov mainFam P₀ r)
    (hPM : ∀ r, SetCClassPauli mainFam P₀ r (βM r))
    (hCB : ∀ k : Fin 5, k < 2 → SetCClassPauli ctFam P₀ (.inl k) (βx (.inl k)))
    (hCD : ∀ (k : Fin 5) (t : Fin 2), k < 2 →
      SetCClassPauli ctFam P₀ (.inr (.inl (k, t))) (βx (.inr (.inl (k, t)))))
    (hsum : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
      (1 / I) * (∑ r, βM r M₁ M₂ c₁ c₂ mγ Λ D s +
        ∑ r, ctPauliVal P₀ βx r M₁ M₂ c₁ c₂ mγ Λ D s) = ((b mγ Λ M₁ M₂ : ℝ) : ℂ))
    (hreg : SetCRegLimitPV (setCPauliValue P₀ b)) (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (η : ℝ)
    (hη : 0 < η) :
    ∃ RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
      1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
      ∃ δ > 0, ∃ R : ℝ, ∀ mγ Λ : ℝ, 0 < mγ → 0 < Λ → mγ < δ → R < Λ →
        (∃ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2) ∧
        ∀ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2 →
          (∃ s : ℝ × ℝ × ℝ, ThreeLoop.IsVPShareOnShell
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D s) ∧
          ∀ s : ℝ × ℝ × ℝ, ThreeLoop.IsVPShareOnShell
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D s →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) (D.withLevel 1 (fun _ => s) (D.d₃ 1))
              (fun C g => IsOnePI C ∧ ThreeLoop.IsSetC C g) 7 p' p V) ∧
            ∀ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) (D.withLevel 1 (fun _ => s) (D.d₃ 1))
              (fun C g => IsOnePI C ∧ ThreeLoop.IsSetC C g) 7 p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 -
                  (ThreeLoop.a1SixSetC : ℂ)‖ < η :=
  isFormFactorPair_vertexSetC_pauli_limit_of_pauliAt P₀ (setCLimitLink_of_main hM)
    (setCCovLink_of_main hM hMc)
    (setCPauliAt_of_classes hm hM
      (setCClassLim_ct (setCClassLim_CB_all fun k hk => setCClassLim_CB01 k hk)
        (setCClassLim_CD_all fun k t hk => setCClassLim_CD01 k hk t))
      hPM (setCClassPauli_ct hCB hCD) hsum)
    hreg he hm η hη

end QED.ChainProof.SetCPauli

end
