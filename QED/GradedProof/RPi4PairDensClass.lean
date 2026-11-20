/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4PairDens
public import QED.GradedProof.RPi4LightClass

/-!
# (R-Π₄) step L6b′: the two-loop classes as photon-mass integrals

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6b′ (heavy photon
pair). The explicit class values `QED.GradedProof.RPi4.vVal` (the limits `wV` of `VA`, `VB`,
`VC` at the photon pair `(a, b)`) are photon-mass integrals
`vVal(a, b) = ∫_{a²}^{b²} vDens(u) du` of a density `vDens` that does not depend on the pair:
the sum over the fifteen pieces of each flavour, block-summed, of the one-photon-line densities
`QED.GradedProof.RPi4.pairDens` of the merged shapes, with the normalized numerator
`vNum e 0 1`.

* `triDens`, `pairInt_triVal`: the fifteen pieces (as `QED.GradedProof.RPi4.triVal`);
* `blockDens`, `pairInt_blockVal`: the block sum (as `QED.GradedProof.RPi4.blockVal`);
* `vDens`, `pairInt_vVal_VA`, `pairInt_vVal_VB`, `pairInt_vVal_VC`: the three classes.
-/

@[expose] public section

open Complex MeasureTheory Matrix

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance

section Setting

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)

/-- **The photon-mass density of the three-flavour combination** of a two-loop numerator `Num`
(with `E₄` its `m⁴` coefficient): the densities of the ten merged pieces with seven lines, the
four with six lines and the padded one (as `QED.GradedProof.RPi4.triVal`). -/
noncomputable def triDens (Num : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (E4 : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (M X Y u : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  (∑ i : Fin 4, ∑ j : Fin 4, if i ≤ j then
      pairDens (fun ℓ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          Num M k ℓ μ ν)
        (castLoopMatrix fun l : Fin 7 => base (shA i j l.castSucc))
        (fun l => c (shA i j l.castSucc) • k)
        ![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2, mA M X Y i j 3, X, Y, 0]
        (Fin.last 6) u
    else 0) +
  ∑ i : Fin 4, pairDens (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        (Num X k ℓ μ ν - Num M k ℓ μ ν))
      (castLoopMatrix fun l : Fin 6 => base (shB i l.castSucc))
      (fun l => c (shB i l.castSucc) • k)
      ![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, 0] (Fin.last 5) u +
  pairDens (fun ℓ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * E4 k μ ν *
      propDenom Y 0 (fm base (ppc c k) 0 ℓ))
    (castLoopMatrix fun l : Fin 6 => base (shB 0 l.castSucc))
    (fun l => c (shB 0 l.castSucc) • k) ![Y, Y, Y, Y, Y, 0] (Fin.last 5) u

/-- **The photon-mass density of a block-summed class**: `∑_f c_f triDens(M_f, X, X + 1)`. -/
noncomputable def blockDens (Num : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (E4 : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) {F : Type} [Fintype F] (Φ : Lepton.Flavors F)
    (m₀ u : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  ∑ f, (Φ.coeff f : ℂ) *
    triDens base c Num E4 (Φ.mass f) (blockX Φ m₀) (blockX Φ m₀ + 1) u k μ ν

variable (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1]) {m₀ : ℝ} (hm₀ : 0 < m₀)

include hflow hrow hrow4 hm₀

/-- **The three-flavour combination at a photon pair** is the photon-mass integral of
`triDens`, for a numerator carrying the photon factor `b² - a²`. -/
theorem pairInt_triVal
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
    {M X Y : ℝ} (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y) (μ ν : Fin 4) :
    PairInt m₀ (fun a b k =>
      triVal base c (fun m k ℓ μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * Num m k ℓ μ ν)
        (fun k μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * E4 k μ ν) a b M X Y k μ ν)
      fun u k => triDens base c Num E4 M X Y u k μ ν := by
  set C : ℂ := ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) with hC
  -- the ten pieces with eight lines
  have PA : ∀ i j : Fin 4, PairInt m₀ (fun a b k => if i ≤ j then
      pieceVal base c (shA i j) ![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2,
        mA M X Y i j 3, X, Y, a, b]
        (fun k ℓ μ ν => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          (fun m k ℓ μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * Num m k ℓ μ ν) M k ℓ μ ν) k μ ν
      else 0)
      fun u k => if i ≤ j then
        pairDens (fun ℓ => C * Num M k ℓ μ ν)
          (castLoopMatrix fun l : Fin 7 => base (shA i j l.castSucc))
          (fun l => c (shA i j l.castSucc) • k)
          ![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2, mA M X Y i j 3, X, Y, 0]
          (Fin.last 6) u
      else 0 := by
    intro i j
    by_cases hij : i ≤ j
    · simp only [hij, ite_true]
      refine (pairInt_pieceA base c y₁ y₂ hflow hrow hrow4 hm₀ i j (hcA i j)
        (mA M X Y i j) (fun l => by unfold mA; split_ifs <;> assumption) hX hY
        (fun k ℓ => C * Num M k ℓ μ ν) (fun k => (hP M k μ ν).const_mul _)
        (fun k => (hBA M k μ ν i j).const_mul _)).congr fun k _ a b _ _ => ?_
      simp only [pieceVal]
      exact pvOf_congr_fun (fun ℓ => by simp only [hC]; ring) _ _ _
    · simp only [hij, ite_false]
      exact PairInt.zero
  -- the four pieces with seven lines
  have PB : ∀ i : Fin 4, PairInt m₀ (fun a b k =>
      pieceVal base c (shB i) ![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, a, b]
        (fun k ℓ μ ν => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          ((fun m k ℓ μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * Num m k ℓ μ ν) X k ℓ μ ν -
            (fun m k ℓ μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * Num m k ℓ μ ν) M k ℓ μ ν)) k μ ν)
      fun u k => pairDens (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          (Num X k ℓ μ ν - Num M k ℓ μ ν))
        (castLoopMatrix fun l : Fin 6 => base (shB i l.castSucc))
        (fun l => c (shB i l.castSucc) • k)
        ![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, 0] (Fin.last 5) u := by
    intro i
    have hpoly : ∀ k, IsLoopPoly 2 3 fun ℓ =>
        -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν) := by
      intro k
      have e : (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν)) =
          fun ℓ => (-((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2)) *
            (E2 k ℓ μ ν + ((M : ℂ) ^ 2 + (X : ℂ) ^ 2) * E4 k μ ν) := by
        funext ℓ; rw [hE, hE]; ring
      rw [e]
      exact (((hP2 k μ ν).add (IsLoopPoly.const _)).const_mul _).mono (by norm_num)
    refine (pairInt_pieceB base c y₁ y₂ hflow hrow hrow4 hm₀ i (hcB i) (mB X Y i)
      (fun l => by unfold mB; split_ifs <;> assumption) hY
      (fun k ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν)) hpoly
      (fun k => (((hBB X k μ ν i).sub (hBB M k μ ν i)).const_mul _).mono (by decide)
        le_rfl)).congr fun k _ a b _ _ => ?_
    simp only [pieceVal]
    exact pvOf_congr_fun (fun ℓ => by ring) _ _ _
  -- the padded piece
  have PC : PairInt m₀ (fun a b k =>
      pieceVal base c (shB 0) ![Y, Y, Y, Y, Y, a, b]
        (fun k ℓ μ ν => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          (fun k μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * E4 k μ ν) k μ ν *
          propDenom Y 0 (fm base (ppc c k) 0 ℓ)) k μ ν)
      fun u k => pairDens (fun ℓ => C * E4 k μ ν * propDenom Y 0 (fm base (ppc c k) 0 ℓ))
        (castLoopMatrix fun l : Fin 6 => base (shB 0 l.castSucc))
        (fun l => c (shB 0 l.castSucc) • k) ![Y, Y, Y, Y, Y, 0] (Fin.last 5) u := by
    refine (pairInt_pieceB base c y₁ y₂ hflow hrow hrow4 hm₀ 0 (hcB 0) (fun _ => Y)
      (fun _ => hY) hY (fun k ℓ => C * E4 k μ ν * propDenom Y 0 (fm base (ppc c k) 0 ℓ))
      (fun k => ((IsLoopPoly.const (n := 0) _).mul
        ((isLoopAffine_lineMomentum _ _ _).isLoopPoly_propDenom Y 0)).mono (by norm_num))
      (fun k => ((rb_propDenom_pad base (ppc c k) (shB 0) 0 4 (by decide) 0 rfl rfl Y
        0).const_mul _).mono (by decide) (by norm_num))).congr fun k _ a b _ _ => ?_
    simp only [pieceVal]
    exact pvOf_congr_fun (fun ℓ => by simp only [hC]; ring) _ _ _
  refine ((((PairInt.sum Finset.univ fun i _ => PairInt.sum Finset.univ fun j _ =>
    PA i j).add (PairInt.sum Finset.univ fun i _ => PB i)).add PC).congr
    fun k _ a b _ _ => ?_).congr_dens fun u k => ?_
  · simp only [triVal]
  · simp only [triDens, hC]

/-- **The block-summed flavour sum at a photon pair** is the photon-mass integral of
`blockDens`. -/
theorem pairInt_blockVal
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
    {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hmass : ∀ g, m₀ ≤ Φ.mass g) (μ ν : Fin 4) :
    PairInt m₀ (fun a b k =>
      blockVal base c (fun m k ℓ μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * Num m k ℓ μ ν)
        (fun k μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * E4 k μ ν) Φ m₀ a b k μ ν)
      fun u k => blockDens base c Num E4 Φ m₀ u k μ ν := by
  have hS0 : 0 ≤ ∑ g, Φ.mass g :=
    Finset.sum_nonneg fun g _ => hm₀.le.trans (hmass g)
  have hX : m₀ ≤ blockX Φ m₀ := by simp only [blockX]; linarith
  exact PairInt.sum Finset.univ fun f _ => (pairInt_triVal base c y₁ y₂ hflow hrow hrow4 hm₀
    hcA hcB Num E0 E2 E4 hE hP hP2 hBA hBB (hmass f) hX (by linarith) μ ν).const_mul
    (Φ.coeff f : ℂ)

end Setting

/-- **The photon-mass density of a class**: `blockDens` of the normalized numerator
`vNum e 0 1`. -/
noncomputable def vDens (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) {F : Type} [Fintype F] (Φ : Lepton.Flavors F)
    (e m₀ u : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  blockDens base c (vNum e 0 1 A base c) (vNumE4 e 0 1 A) Φ m₀ u k μ ν

section Classes

variable {F : Type} [Fintype F] (Φ : Lepton.Flavors F) {m₀ : ℝ} (hm₀ : 0 < m₀)
  (hmass : ∀ g, m₀ ≤ Φ.mass g) (e : ℝ) (μ ν : Fin 4)

include hm₀ hmass

/-- **The class `VA` at a photon pair is the photon-mass integral of `vDens`.** -/
theorem pairInt_vVal_VA : PairInt m₀ (fun a b k => vVal aVA baseVA cVA Φ e m₀ a b k μ ν)
    fun u k => vDens aVA baseVA cVA Φ e m₀ u k μ ν := by
  refine (pairInt_blockVal baseVA cVA ![0, 0] ![-1, -1] flowVA (by decide) (by decide) hm₀
    critA_VA critB_VA _ _ _ _
    (vNum_eq e 0 1 aVA baseVA cVA fun a b ρ σ => isOddG_aVA a b ρ σ)
    (isLoopPoly_vNum e 0 1 aVA baseVA cVA) (isLoopPoly_vNumE2 e 0 1 aVA baseVA cVA)
    (fun m k a' b' i j => rb_vNum e 0 1 aVA baseVA cVA (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVA baseVA cVA (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b') Φ hmass μ ν).congr fun k _ a b _ _ => ?_
  rw [vVal_eq_blockVal]

/-- **The class `VB` at a photon pair is the photon-mass integral of `vDens`.** -/
theorem pairInt_vVal_VB : PairInt m₀ (fun a b k => vVal aVB baseVB cVB Φ e m₀ a b k μ ν)
    fun u k => vDens aVB baseVB cVB Φ e m₀ u k μ ν := by
  refine (pairInt_blockVal baseVB cVB ![0, 1] ![-1, 0] flowVB (by decide) (by decide) hm₀
    critA_VB critB_VB _ _ _ _
    (vNum_eq e 0 1 aVB baseVB cVB fun a b ρ σ => isOddG_aVB a b ρ σ)
    (isLoopPoly_vNum e 0 1 aVB baseVB cVB) (isLoopPoly_vNumE2 e 0 1 aVB baseVB cVB)
    (fun m k a' b' i j => rb_vNum e 0 1 aVB baseVB cVB (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVB baseVB cVB (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b') Φ hmass μ ν).congr fun k _ a b _ _ => ?_
  rw [vVal_eq_blockVal]

/-- **The class `VC` at a photon pair is the photon-mass integral of `vDens`.** -/
theorem pairInt_vVal_VC : PairInt m₀ (fun a b k => vVal aVC baseVC cVC Φ e m₀ a b k μ ν)
    fun u k => vDens aVC baseVC cVC Φ e m₀ u k μ ν := by
  refine (pairInt_blockVal baseVC cVC ![0, 1] ![-1, 0] flowVC (by decide) (by decide) hm₀
    critA_VC critB_VC _ _ _ _
    (vNum_eq e 0 1 aVC baseVC cVC fun a b ρ σ => isOddG_aVC a b ρ σ)
    (isLoopPoly_vNum e 0 1 aVC baseVC cVC) (isLoopPoly_vNumE2 e 0 1 aVC baseVC cVC)
    (fun m k a' b' i j => rb_vNum e 0 1 aVC baseVC cVC (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVC baseVC cVC (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b') Φ hmass μ ν).congr fun k _ a b _ _ => ?_
  rw [vVal_eq_blockVal]

end Classes

end QED.GradedProof.RPi4

end
