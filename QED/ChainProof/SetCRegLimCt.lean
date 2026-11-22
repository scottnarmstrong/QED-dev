/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegLim
public import QED.ChainProof.SetCPauliAtCB
public import QED.ChainProof.SetCPauliAtCD
public import QED.ChainProof.SetCKFormOCFinal

/-!
# Set (c): the per-class Pauli limits of all 20 counterterm classes, and the headline from the
main classes

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`
(`QED/Frozen/ThreeLoop/VertexSetCPauliLimit.lean`, `DRAFT_SORRY`, not imported). The four
counterterm classes left open in `QED/ChainProof/SetCPauliAtCt.lean` have their canonical Pauli
limits: `CB0`, `CB1` (`QED.ChainProof.SetCPauli.setCClassPauli_CB01`, values `clsPauliLim`) and
`CD0 t`, `CD1 t` (`QED.ChainProof.SetCPauli.setCClassPauli_CD01`, values `cd01PauliVal`).

## Main statements

* `ctPauliX`: the values of the four classes; `ctPauliAll P₀ = ctPauliVal P₀ (ctPauliX P₀)`;
* **`setCClassPauli_ct_all`**: the per-class Pauli limits of all 20 counterterm and VP-share
  classes, unconditionally;
* **`isFormFactorPair_vertexSetC_pauli_limit_of_mainB`**: the proposition of (HS₆) from the
  limit, covariance and per-class Pauli links of the 36 main classes, a real `b` equal to `(1/i)`
  times the sum of the 56 class values (`hsum`), and the regulator limit `SetCRegLimitB P₀ b`;
* `SetCRegLimitDisp P₀ b`, **`setCRegLimitB_of_disp`**: the regulator limit with the Stage K
  dispersion integral `setCKDisp = ∫₀¹ ρ(v) A_(c)(t_v) dv` as target gives `SetCRegLimitB P₀ b`
  (the Stieltjes identity (S), `QED.ChainProof.SetCK.setCKDisp_eq_aSetC_proved`, and
  `A₁⁽⁶⁾(c) = aSetC` by unfolding).
-/

@[expose] public section

open Complex Filter Topology
open scoped Real
open QED.WickModel (Params IsOnePI)

namespace QED.ChainProof.SetCPauli

open QED.ChainProof.SetAPauli (regParams regFlavors)

/-- The per-class Pauli values of `CB0`, `CB1`, `CD0 t`, `CD1 t` (the other entries are not used
by `ctPauliVal`). -/
noncomputable def ctPauliX (P₀ : Params) : CtIdx → ClsPauliVal
  | .inl k => clsPauliLim ctFam P₀ (.inl k)
  | .inr (.inl (k, _)) => cd01PauliVal P₀ k
  | .inr (.inr _) => fun _ _ _ _ _ _ _ _ => 0

/-- The per-class Pauli values of the 20 counterterm and VP-share classes. -/
noncomputable abbrev ctPauliAll (P₀ : Params) : CtIdx → ClsPauliVal := ctPauliVal P₀ (ctPauliX P₀)

/-- **The per-class Pauli limits of the 20 counterterm and VP-share classes.** -/
theorem setCClassPauli_ct_all (P₀ : Params) : ∀ r, SetCClassPauli ctFam P₀ r (ctPauliAll P₀ r) :=
  setCClassPauli_ct (fun k hk => setCClassPauli_CB01 k hk) fun k t hk => setCClassPauli_CD01 k hk t

/-- **(HS₆) from the 36 main classes and the regulator limit of `b`.** The inputs are the limit,
covariance and per-class Pauli links of the 36 two-loop-outer classes, a real `b` equal to `(1/i)`
times the sum of the 56 class values, and `b → e⁶ A₁⁽⁶⁾(c)/(64π⁶)` over `M₁ ≠ M₂`. The conclusion
is, verbatim, the proposition of the frozen `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`.
-/
theorem isFormFactorPair_vertexSetC_pauli_limit_of_mainB {b : ℝ → ℝ → ℝ → ℝ → ℝ}
    {βM : MainIdx → ClsPauliVal} (P₀ : Params)
    (hM : ∀ r, SetCClassLim mainFam P₀ r) (hMc : ∀ r, SetCClassCov mainFam P₀ r)
    (hPM : ∀ r, SetCClassPauli mainFam P₀ r (βM r))
    (hsum : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
      (1 / I) * (∑ r, βM r M₁ M₂ c₁ c₂ mγ Λ D s +
        ∑ r, ctPauliAll P₀ r M₁ M₂ c₁ c₂ mγ Λ D s) = ((b mγ Λ M₁ M₂ : ℝ) : ℂ))
    (hreg : SetCRegLimitB P₀ b) (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (η : ℝ) (hη : 0 < η) :
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
      hPM (setCClassPauli_ct_all P₀) hsum)
    (setCRegLimitPV_of_b he hreg) he hm η hη

/-- **The regulator limit of `b` towards the Stage K dispersion integral** (open for a given
`b`): `b → e⁶ a_(c) / (64π⁶)` over `M₁ ≠ M₂` in the iterated order of D-37.4, with
`a_(c) = setCKDisp = ∫₀¹ ρ(v) A_(c)(t_v) dv` the dispersion integral of the twelve kernel
placements. -/
def SetCRegLimitDisp (P₀ : Params) (b : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ η > 0, ∃ RM : ℝ, ∀ M₁ M₂ : ℝ, RM < M₁ → RM < M₂ → M₁ ≠ M₂ → ∃ δ > 0, ∃ Λ₀ : ℝ,
    ∀ mγ Λ : ℝ, 0 < mγ → mγ < δ → Λ₀ < Λ →
      |b mγ Λ M₁ M₂ - P₀.e ^ 6 * SetCK.setCKDisp / (64 * π ^ 6)| < η

/-- **The dispersion target is `A₁⁽⁶⁾(c)`**: (S) and `setCKDisp = aSetC`. -/
theorem setCRegLimitB_of_disp {P₀ : Params} {b : ℝ → ℝ → ℝ → ℝ → ℝ}
    (h : SetCRegLimitDisp P₀ b) : SetCRegLimitB P₀ b := by
  have e : SetCK.setCKDisp = ThreeLoop.a1SixSetC := SetCK.setCKDisp_eq_aSetC_proved
  intro η hη
  simpa only [e] using h η hη

end QED.ChainProof.SetCPauli

end
