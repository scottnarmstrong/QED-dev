/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCPauliMainCanon
public import QED.ChainProof.SetCMainDUnit
public import QED.ChainProof.SetCUnitMDisp
public import QED.GradedProof.V5ZeroSharpOpen
public import QED.GradedProof.V5ZeroSharpParam

/-!
# Set (c): the main class limits are `♯`-odd

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hSM` of
`QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit_of_mainSharp`. As for the order-`e⁵`
vertex (`QED.GradedProof.V5Zero.Sharp.sharp_classLimitV`), the phase of a limit is read off its
parametric form: the entries of the multi-denominator units at `n = 0` are parametric values
(`QED.ChainProof.SetCUnitM.isParamValue_unitMLimitV`) of the open-class numerator, which is
`♯`-odd (`QED.GradedProof.V5Zero.Sharp.sharp_classNumM`), and the powers `(k²)ⁿ` and the
dispersion integral of `repB` are combinations with real coefficients and weights.

* **`sharp_unitMLimitV`**: the multi-denominator unit limits are `♯`-odd, every power `n` with the
  last `n` extra lines unscaled;
* **`sharp_unitMDispRepB`**: the dispersion integral of the transverse `repB` unit against a real
  weight is `♯`-odd;
* `conj_wD`, **`sharp_dGLimD`**: the transverse limit of `repD i s` is `♯`-odd;
* `DKSharpLink P₀ i t` (open, with the longitudinal links `DKLimLink`, `DKCovLink`): the limits of
  the longitudinal part of `repD i t` at the set (c) data are `♯`-odd;
* **`setCClassSharp_inr_of_dK`**: `SetCClassSharp mainFam P₀ (.inr (i, t))` from `DKSharpLink`;
* **`setCClassSharp_main`**: the input `hSM` from the `repB` classes and `DKSharpLink`;
* **`isFormFactorPair_vertexSetC_pauli_limit_of_mainParts`**: (HS₆) with `hcan` discharged and
  `hSM` reduced to the `repB` classes and the longitudinal parts of the `repD` classes.
-/

@[expose] public section

open Complex Matrix Filter Topology MeasureTheory Set
open QED.WickModel (Params IsOnePI)

namespace QED.ChainProof.SetCUnitM

open QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassIntegrable QED.TwoLoop.ClassLimit
open QED.TwoLoop.LimitCovariance QED.ChainProof.SetCUnit
open QED.GradedProof.SE2Real (sharp sharp_sub sharp_smul)
open QED.GradedProof.V5Zero.Sharp (sharp_eq_smul_of_isParamValue_vertex sharp_classNumM
  conj_twoLoopNorm sharp_apply sgn conj_sgn)

/-! ### The units -/

section Unit

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {s : Fin 8}
  (hs : 4 ≤ (s : ℕ)) {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
  {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
include hc hm hs hμ₀ hM hp hp' hq

/-- **The multi-denominator unit limits are `♯`-odd**, every power `n` with the last `n ≤ r`
extra lines unscaled. -/
theorem sharp_unitMLimitV (n : ℕ) :
    ∀ {r : ℕ} {κ cs : Fin r → ℝ}, n ≤ r → TrailOne n κ → ExtraGe μ₀ κ cs → ∀ μ : Fin 4,
      sharp (unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' n μ) =
        -unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' n μ := by
  induction n with
  | zero =>
    intro r κ cs _ _ hX μ
    have h := sharp_eq_smul_of_isParamValue_vertex
      (D := unitMData hc P hm hs hμ₀ hM hX hp hp' hq)
      (fun μ ℓ => twoLoopNorm • classNumM c P p p' μ ℓ) _ (-1)
      (fun μ ℓ => by rw [sharp_smul, conj_twoLoopNorm, sharp_classNumM hc, smul_comm])
      (fun μ i j => isParamValue_unitMLimitV hc P hm hs hμ₀ hM hp hp' hq hX μ i j) μ
    rw [h, neg_one_smul]
  | succ n ih =>
    intro r κ cs hnr hT hX μ
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [unitMLimitV_succ_mat hc P hm hs hμ₀ hM hp hp' hq hnr hT hX, sharp_sub, sharp_smul,
      Complex.conj_ofReal, ih (by omega) hT.init hX.init, ih (by omega) hT.of_succ hX, smul_neg]
    abel

end Unit

section Disp

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {s : Fin 8}
  (hs : 4 ≤ (s : ℕ)) {μ₀ mγ Λ : ℝ} (hμ₀ : 0 < μ₀) (hmγ : μ₀ ≤ mγ) (hΛ : μ₀ ≤ Λ)
  {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
include hc hm hs hμ₀ hmγ hΛ hp hp' hq

/-- **The dispersion integral of the transverse `repB` unit is `♯`-odd** for every real weight
`w` (no integrability needed: both sides are Bochner integrals of the same integrand up to
sign). -/
theorem sharp_unitMDispRepB {M : ℝ} (hM : μ₀ ≤ M) {w : ℝ → ℂ}
    (hw : ∀ x, starRingEnd ℂ (w x) = w x) (μ : Fin 4) :
    sharp (unitMDispRepB c P s w M mγ Λ p p' μ) = -unitMDispRepB c P s w M mγ Λ p p' μ := by
  have hL : ∀ x ∈ Ioo (0 : ℝ) 1, sharp (unitMLimitV c P s (repBKappa x)
      (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) p p' 2 μ) =
        -unitMLimitV c P s (repBKappa x) (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ))
          p p' 2 μ := fun x hx =>
    sharp_unitMLimitV hc P hm hs hμ₀ (massesGe_repB hmγ hΛ) hp hp' hq 2 (by norm_num)
      (trailOne_repBKappa x) (extraGe_repB hx hM hmγ hΛ) μ
  ext i j
  simp only [unitMDispRepB, sharp_apply, Matrix.neg_apply, Matrix.of_apply]
  rw [← integral_conj, ← integral_const_mul, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have h := congrFun (congrFun (hL x hx) i) j
  rw [sharp_apply, Matrix.neg_apply] at h
  simp only [map_mul, hw]
  rw [mul_left_comm, h, mul_neg]

end Disp

end QED.ChainProof.SetCUnitM

namespace QED.ChainProof.SetCMain

open QED.ChainProof.SetCUnitM
open QED.ChainProof.SetCUnit (MassesGe)
open QED.GradedProof.SE2Real (sharp sharp_add sharp_smul)
open QED.ChainProof.SetCPauli
open QED.ChainProof.SetAPauli (regParams regFlavors)

/-! ### The `δ₃` classes -/

/-- The constant `wD = -(i/2) δ₃ (1/i)(Λ² - m_γ²)` of the transverse part is real. -/
theorem conj_wD (P : Params) (δ₃ : ℝ) : starRingEnd ℂ (wD P δ₃) = wD P δ₃ := by
  have h : wD P δ₃ = ((-(1 / 2) * δ₃ * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ) := by
    unfold wD
    push_cast
    field_simp
  rw [h, Complex.conj_ofReal]

/-- **The transverse limit of `repD i s` is `♯`-odd.** -/
theorem sharp_dGLimD {R : Params} (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ)
    {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -R.m ^ 2) (hp' : Minkowski.dot p' p' = -R.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (δ₃ : ℝ) (i : Fin 12) (μ : Fin 4) :
    sharp (dGLimD R δ₃ i p p' μ) = -dGLimD R δ₃ i p p' μ := by
  have hM : MassesGe R.mγ R.mγ R.Λ R.mγ R.Λ := ⟨le_rfl, hγΛ, le_rfl, hγΛ⟩
  simp only [dGLimD]
  rw [sharp_smul, conj_wD, sharp_unitMLimitV (repBClass_mem i) R hm (four_le_repBSlot i) hγ hM
    hp hp' hq 1 (by norm_num) trailOne_one_two (extraGe_two hγΛ) μ, smul_neg]

variable {P₀ : Params}

/-- **The `♯`-law of the longitudinal part of `repD i t`** (open, with `DKLimLink`, `DKCovLink`):
at the set (c) data, every limit of the longitudinal part at an on-shell positive-energy pair with
`q² > 0` is `♯`-odd. -/
def DKSharpLink (P₀ : Params) (i : Fin 12) (t : Fin 2) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
    ∀ p' p, IsPairQ P₀.m p' p → ∀ Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ,
      (∀ μ α β, Tendsto (dKValD P₀ M₁ M₂ c₁ c₂ mγ Λ D s i t p' p μ α β) (𝓝[>] 0)
        (𝓝 (Y μ α β))) →
      ∀ μ, sharp (Y μ) = -Y μ

/-- **The `♯`-law of `repD i t` from that of its longitudinal part.** -/
theorem setCClassSharp_inr_of_dK {i : Fin 12} {t : Fin 2} (hK : DKSharpLink P₀ i t) :
    SetCClassSharp mainFam P₀ (.inr (i, t)) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq Y hY μ
  set R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ
  set δ₃ := P₀.e ^ 2 * (shareCt D s).d₃ 0
  have hKY : ∀ μ α β, Tendsto (dKValD P₀ M₁ M₂ c₁ c₂ mγ Λ D s i t p' p μ α β) (𝓝[>] 0)
      (𝓝 ((fun ν => Y ν - dGLimD R δ₃ i p p' ν) μ α β)) := fun μ α β => by
    refine ((hY μ α β).sub (tendsto_dG_setC hA hpq i t μ α β)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [mainVal_inr_eq_dG_add hε p' p μ i t α β]
    ring
  have h1 := hK M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq _ hKY μ
  obtain ⟨hm, hγ, hγΛ⟩ := setCAdm_masses hA
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  have h2 := sharp_dGLimD (R := R) hm hγ hγΛ hp hp' hq.le δ₃ i μ
  have hY' : Y μ = (Y μ - dGLimD R δ₃ i p p' μ) + dGLimD R δ₃ i p p' μ := by abel
  rw [hY', sharp_add, h1, h2]
  abel

/-- **The `♯`-law of the 36 main classes** from that of the twelve `repB` classes and of the
longitudinal parts of the twenty-four `repD` classes. -/
theorem setCClassSharp_main (hB : ∀ i, SetCClassSharp mainFam P₀ (.inl i))
    (hK : ∀ i t, DKSharpLink P₀ i t) : ∀ r, SetCClassSharp mainFam P₀ r
  | .inl i => hB i
  | .inr (i, t) => setCClassSharp_inr_of_dK (hK i t)

end QED.ChainProof.SetCMain

namespace QED.ThreeLoop

open QED.ChainProof.SetCPauli (MainIdx ClsPauliVal mainFam SetCClassLim SetCClassCov
  SetCClassPauli SetCClassSharp SetCRegLimitB setCPauliB)
open QED.ChainProof.SetCMain (DKSharpLink)

/-- **The remaining interface of set (c), by parts**: (HS₆) from the main-class limit,
covariance and Pauli links, the `♯`-law of the twelve `repB` classes and of the longitudinal parts
of the twenty-four `repD` classes, and the regulator limit of `b = setCPauliB P₀ βᴹ`. -/
theorem isFormFactorPair_vertexSetC_pauli_limit_of_mainParts (P₀ : Params)
    {βM : MainIdx → ClsPauliVal}
    (hM : ∀ r, SetCClassLim mainFam P₀ r) (hMc : ∀ r, SetCClassCov mainFam P₀ r)
    (hPM : ∀ r, SetCClassPauli mainFam P₀ r (βM r))
    (hSB : ∀ i, SetCClassSharp mainFam P₀ (.inl i)) (hSK : ∀ i t, DKSharpLink P₀ i t)
    (hreg : SetCRegLimitB P₀ (setCPauliB P₀ βM))
    (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (η : ℝ) (hη : 0 < η) :
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
          (∃ s : ℝ × ℝ × ℝ, IsVPShareOnShell
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D s) ∧
          ∀ s : ℝ × ℝ × ℝ, IsVPShareOnShell
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
              (fun C g => IsOnePI C ∧ IsSetC C g) 7 p' p V) ∧
            ∀ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) (D.withLevel 1 (fun _ => s) (D.d₃ 1))
              (fun C g => IsOnePI C ∧ IsSetC C g) 7 p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 - (a1SixSetC : ℂ)‖ < η :=
  isFormFactorPair_vertexSetC_pauli_limit_of_mainLinks P₀ hM hMc hPM
    (QED.ChainProof.SetCMain.setCClassSharp_main hSB hSK) hreg he hm η hη

end QED.ThreeLoop

end
