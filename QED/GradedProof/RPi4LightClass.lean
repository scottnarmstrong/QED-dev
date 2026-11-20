/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4LightVP
public import QED.GradedProof.RPi4VJVClass

/-!
# (R-Π₄) step L7: the two-loop classes at a light photon pair

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L7 (light photon
pair). The explicit class values `QED.GradedProof.RPi4.vVal` (the limits `wV` of `VA`, `VB`,
`VC` at the photon pair `(a, b)`) are `O(b)` for light comparable pairs
`0 < a ≤ b ≤ min(2a, 1)`, uniformly along a segment of momenta below threshold.

* `lightBdd_pieceA`, `lightBdd_pieceB`: the pieces with eight and seven lines, from
  `QED.GradedProof.RPi4.lightBdd_vpPiece`;
* `lightBdd_triVal`, `lightBdd_blockVal`: the fifteen pieces of `triVal` (hypotheses as in
  `QED.GradedProof.RPi4.vpjv_gTriple`) and the block sum;
* `vNumE4_eq_mul`, `vVal_eq_blockVal`: the photon factor `b² - a²` pulled out of the numerator;
* `lightBdd_vVal_VA`, `lightBdd_vVal_VB`, `lightBdd_vVal_VC`: the three classes.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance

theorem pvOf_congr_fun {m : ℕ} {F G : (Fin 2 → Fin 4 → ℝ) → ℂ} (h : ∀ ℓ, F ℓ = G ℓ)
    (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) :
    pvOf F α p M = pvOf G α p M := by
  rw [funext h]

section Setting

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1])
  {m₀ : ℝ} (hm₀ : 0 < m₀) {k₀ w : Fin 4 → ℝ} {S₀ : ℝ} (hS₀ : -(2 * m₀) ^ 2 < S₀)
  (hseg : ∀ u : ℝ, |u| ≤ 1 / 2 → S₀ ≤ Minkowski.dot (lineK k₀ w u) (lineK k₀ w u))

include hflow hrow hrow4 hm₀ hS₀ hseg

/-- **A piece with eight lines at a light pair.** -/
theorem lightBdd_pieceA (i j : Fin 4)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => base (shA i j n))
    (Mf : Fin 4 → ℝ) (hMf : ∀ l, m₀ ≤ Mf l) {X Y : ℝ} (hX : m₀ ≤ X) (hY : m₀ ≤ Y)
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : ∀ k, IsLoopPoly 2 4 (N k))
    (hB : ∀ k, RefinedBound (castLoopMatrix fun n => base (shA i j n)) {0, 1, 2, 3} 4 (N k))
    {d : ℕ} (hk : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ) :
    LightBdd k₀ w fun a b k => pvOf (fun ℓ => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * N k ℓ)
      (castLoopMatrix fun l => base (shA i j l)) (fun l => c (shA i j l) • k)
      ![Mf 0, Mf 1, Mf 2, Mf 3, X, Y, a, b] :=
  lightBdd_vpPiece base c y₁ y₂ hflow hrow hrow4 (Or.inr rfl) (shA i j)
    (fun l => by fin_cases l <;> simp [shA, Fin.ext_iff] <;> omega)
    (fun a b => ![Mf 0, Mf 1, Mf 2, Mf 3, X, Y, a, b])
    (fun a b l => by fin_cases l <;> simp) hcrit N hpoly hB hk hm₀
    (fun l hl => by
      fin_cases l
      exacts [hMf 0, hMf 1, hMf 2, hMf 3, hX, hY, absurd rfl hl, absurd rfl hl])
    hS₀ hseg

/-- **A piece with seven lines at a light pair.** -/
theorem lightBdd_pieceB (i : Fin 4)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB i n))
    (Mf : Fin 4 → ℝ) (hMf : ∀ l, m₀ ≤ Mf l) {Y : ℝ} (hY : m₀ ≤ Y)
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : ∀ k, IsLoopPoly 2 3 (N k))
    (hB : ∀ k, RefinedBound (castLoopMatrix fun n => base (shB i n)) {0, 1, 2, 3, 4} 4 (N k))
    {d : ℕ} (hk : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ) :
    LightBdd k₀ w fun a b k => pvOf (fun ℓ => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * N k ℓ)
      (castLoopMatrix fun l => base (shB i l)) (fun l => c (shB i l) • k)
      ![Mf 0, Mf 1, Mf 2, Mf 3, Y, a, b] :=
  lightBdd_vpPiece base c y₁ y₂ hflow hrow hrow4 (Or.inl rfl) (shB i)
    (fun l => by fin_cases l <;> simp [shB, Fin.ext_iff]; omega)
    (fun a b => ![Mf 0, Mf 1, Mf 2, Mf 3, Y, a, b])
    (fun a b l => by fin_cases l <;> simp) hcrit N hpoly hB hk hm₀
    (fun l hl => by
      fin_cases l
      exacts [hMf 0, hMf 1, hMf 2, hMf 3, hY, absurd rfl hl, absurd rfl hl])
    hS₀ hseg

/-- **The three-flavour combination at a light pair**: `triVal` of a numerator carrying the
photon factor `b² - a²` is `O(b)`. -/
theorem lightBdd_triVal
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
    {d : ℕ} (hk : ∀ m ℓ a b, IsLoopPoly 1 d fun y => Num m (y 0) ℓ a b)
    {M X Y : ℝ} (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y) (μ ν : Fin 4) :
    LightBdd k₀ w fun a b k =>
      triVal base c (fun m k ℓ μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * Num m k ℓ μ ν)
        (fun k μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * E4 k μ ν) a b M X Y k μ ν := by
  have hE4 : ∀ k ℓ a b, E4 k a b =
      1 / 12 * (Num 2 k ℓ a b - 4 * Num 1 k ℓ a b + 3 * Num 0 k ℓ a b) := fun k ℓ a b => by
    rw [hE, hE, hE]; push_cast; ring
  have hk4 : ∀ (ℓ : Fin 2 → Fin 4 → ℝ) a b, IsLoopPoly 1 d fun y => E4 (y 0) a b := by
    intro ℓ a b
    have e : (fun y : Fin 1 → Fin 4 → ℝ => E4 (y 0) a b) = fun y =>
        1 / 12 * (Num 2 (y 0) ℓ a b - 4 * Num 1 (y 0) ℓ a b + 3 * Num 0 (y 0) ℓ a b) :=
      funext fun y => hE4 (y 0) ℓ a b
    rw [e]
    exact (((hk 2 ℓ a b).sub ((hk 1 ℓ a b).const_mul 4)).add
      ((hk 0 ℓ a b).const_mul 3)).const_mul _
  set C : ℂ := ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) with hC
  -- the ten pieces with eight lines
  have PA : ∀ i j : Fin 4, LightBdd k₀ w fun a b k => if i ≤ j then
      pieceVal base c (shA i j) ![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2,
        mA M X Y i j 3, X, Y, a, b]
        (fun k ℓ μ ν => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          (fun m k ℓ μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * Num m k ℓ μ ν) M k ℓ μ ν) k μ ν
      else 0 := by
    intro i j
    by_cases hij : i ≤ j
    · simp only [hij, ite_true]
      refine (lightBdd_pieceA base c y₁ y₂ hflow hrow hrow4 hm₀ hS₀ hseg i j (hcA i j)
        (mA M X Y i j) (fun l => by unfold mA; split_ifs <;> assumption) hX hY
        (fun k ℓ => C * Num M k ℓ μ ν) (fun k => (hP M k μ ν).const_mul _)
        (fun k => (hBA M k μ ν i j).const_mul _) (fun ℓ => (hk M ℓ μ ν).const_mul _)).congr
        fun u _ a b _ _ => ?_
      simp only [pieceVal]
      exact pvOf_congr_fun (fun ℓ => by simp only [hC]; ring) _ _ _
    · simp only [hij, ite_false]
      exact LightBdd.zero
  -- the four pieces with seven lines
  have PB : ∀ i : Fin 4, LightBdd k₀ w fun a b k =>
      pieceVal base c (shB i) ![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, a, b]
        (fun k ℓ μ ν => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          ((fun m k ℓ μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * Num m k ℓ μ ν) X k ℓ μ ν -
            (fun m k ℓ μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * Num m k ℓ μ ν) M k ℓ μ ν)) k μ ν := by
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
    refine (lightBdd_pieceB base c y₁ y₂ hflow hrow hrow4 hm₀ hS₀ hseg i (hcB i) (mB X Y i)
      (fun l => by unfold mB; split_ifs <;> assumption) hY
      (fun k ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν)) hpoly
      (fun k => (((hBB X k μ ν i).sub (hBB M k μ ν i)).const_mul _).mono (by decide) le_rfl)
      (fun ℓ => ((hk X ℓ μ ν).sub (hk M ℓ μ ν)).const_mul _)).congr fun u _ a b _ _ => ?_
    simp only [pieceVal]
    exact pvOf_congr_fun (fun ℓ => by ring) _ _ _
  -- the padded piece
  have PC : LightBdd k₀ w fun a b k =>
      pieceVal base c (shB 0) ![Y, Y, Y, Y, Y, a, b]
        (fun k ℓ μ ν => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          (fun k μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * E4 k μ ν) k μ ν *
          propDenom Y 0 (fm base (ppc c k) 0 ℓ)) k μ ν := by
    refine (lightBdd_pieceB base c y₁ y₂ hflow hrow hrow4 hm₀ hS₀ hseg 0 (hcB 0) (fun _ => Y)
      (fun _ => hY) hY (fun k ℓ => C * E4 k μ ν * propDenom Y 0 (fm base (ppc c k) 0 ℓ))
      (fun k => ((IsLoopPoly.const (n := 0) _).mul
        ((isLoopAffine_lineMomentum _ _ _).isLoopPoly_propDenom Y 0)).mono (by norm_num))
      (fun k => ((rb_propDenom_pad base (ppc c k) (shB 0) 0 4 (by decide) 0 rfl rfl Y
        0).const_mul _).mono (by decide) (by norm_num))
      (fun ℓ => ((hk4 ℓ μ ν).const_mul C).mul
        ((isLoopAffine_lineMomentum_k base c _ ℓ).isLoopPoly_propDenom Y 0))).congr
      fun u _ a b _ _ => ?_
    simp only [pieceVal]
    exact pvOf_congr_fun (fun ℓ => by simp only [hC]; ring) _ _ _
  refine (((LightBdd.sum Finset.univ fun i _ => LightBdd.sum Finset.univ fun j _ => PA i j).add
    (LightBdd.sum Finset.univ fun i _ => PB i)).add PC).congr fun u _ a b _ _ => ?_
  simp only [triVal]

/-- **The block-summed flavour sum at a light pair.** -/
theorem lightBdd_blockVal
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
    {d : ℕ} (hk : ∀ m ℓ a b, IsLoopPoly 1 d fun y => Num m (y 0) ℓ a b)
    {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hmass : ∀ g, m₀ ≤ Φ.mass g) (μ ν : Fin 4) :
    LightBdd k₀ w fun a b k =>
      blockVal base c (fun m k ℓ μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * Num m k ℓ μ ν)
        (fun k μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * E4 k μ ν) Φ m₀ a b k μ ν := by
  have hS0 : 0 ≤ ∑ g, Φ.mass g :=
    Finset.sum_nonneg fun g _ => hm₀.le.trans (hmass g)
  have hX : m₀ ≤ blockX Φ m₀ := by simp only [blockX]; linarith
  exact LightBdd.sum Finset.univ fun f _ => (lightBdd_triVal base c y₁ y₂ hflow hrow hrow4 hm₀
    hS₀ hseg hcA hcB Num E0 E2 E4 hE hP hP2 hBA hBB hk (hmass f) hX (by linarith) μ ν).const_mul
    (Φ.coeff f : ℂ)

end Setting

/-- The `m⁴` coefficient of the class numerator is `Λ² - m_γ²` times its value at `(0, 1)`. -/
theorem vNumE4_eq_mul (e a b : ℝ)
    (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    vNumE4 e a b A k μ ν = ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * vNumE4 e 0 1 A k μ ν := by
  simp only [vNumE4, kV_eq_mul e a b, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- `vVal` at the photon pair `(a, b)` is the block value of the numerator at `(0, 1)` times
`b² - a²`. -/
theorem vVal_eq_blockVal {F : Type} [Fintype F] (Φ : Lepton.Flavors F)
    (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (e m₀ a b : ℝ) :
    vVal A base c Φ e m₀ a b = blockVal base c
      (fun m k ℓ μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * vNum e 0 1 A base c m k ℓ μ ν)
      (fun k μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * vNumE4 e 0 1 A k μ ν) Φ m₀ a b := by
  have h1 : vNum e a b A base c =
      fun m k ℓ μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * vNum e 0 1 A base c m k ℓ μ ν := by
    funext m k ℓ μ ν
    exact vNum_eq_mul e a b A base c m k ℓ μ ν
  have h2 : vNumE4 e a b A = fun k μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * vNumE4 e 0 1 A k μ ν := by
    funext k μ ν
    exact vNumE4_eq_mul e a b A k μ ν
  rw [vVal, h1, h2]

section Classes

variable {F : Type} [Fintype F] (Φ : Lepton.Flavors F) {m₀ : ℝ} (hm₀ : 0 < m₀)
  (hmass : ∀ g, m₀ ≤ Φ.mass g) (e : ℝ) {k₀ w : Fin 4 → ℝ} {S₀ : ℝ}
  (hS₀ : -(2 * m₀) ^ 2 < S₀)
  (hseg : ∀ u : ℝ, |u| ≤ 1 / 2 → S₀ ≤ Minkowski.dot (lineK k₀ w u) (lineK k₀ w u))
  (μ ν : Fin 4)

include hm₀ hmass hS₀ hseg

/-- **The class `VA` at a light pair is `O(b)`.** -/
theorem lightBdd_vVal_VA : LightBdd k₀ w fun a b k => vVal aVA baseVA cVA Φ e m₀ a b k μ ν := by
  refine (lightBdd_blockVal baseVA cVA ![0, 0] ![-1, -1] flowVA (by decide) (by decide) hm₀ hS₀
    hseg critA_VA critB_VA _ _ _ _
    (vNum_eq e 0 1 aVA baseVA cVA fun a b ρ σ => isOddG_aVA a b ρ σ)
    (isLoopPoly_vNum e 0 1 aVA baseVA cVA) (isLoopPoly_vNumE2 e 0 1 aVA baseVA cVA)
    (fun m k a' b' i j => rb_vNum e 0 1 aVA baseVA cVA (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVA baseVA cVA (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (isLoopPoly_vNum_k e 0 1 aVA baseVA cVA) Φ hmass μ ν).congr fun u _ a b _ _ => ?_
  rw [vVal_eq_blockVal]

/-- **The class `VB` at a light pair is `O(b)`.** -/
theorem lightBdd_vVal_VB : LightBdd k₀ w fun a b k => vVal aVB baseVB cVB Φ e m₀ a b k μ ν := by
  refine (lightBdd_blockVal baseVB cVB ![0, 1] ![-1, 0] flowVB (by decide) (by decide) hm₀ hS₀
    hseg critA_VB critB_VB _ _ _ _
    (vNum_eq e 0 1 aVB baseVB cVB fun a b ρ σ => isOddG_aVB a b ρ σ)
    (isLoopPoly_vNum e 0 1 aVB baseVB cVB) (isLoopPoly_vNumE2 e 0 1 aVB baseVB cVB)
    (fun m k a' b' i j => rb_vNum e 0 1 aVB baseVB cVB (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVB baseVB cVB (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (isLoopPoly_vNum_k e 0 1 aVB baseVB cVB) Φ hmass μ ν).congr fun u _ a b _ _ => ?_
  rw [vVal_eq_blockVal]

/-- **The class `VC` at a light pair is `O(b)`.** -/
theorem lightBdd_vVal_VC : LightBdd k₀ w fun a b k => vVal aVC baseVC cVC Φ e m₀ a b k μ ν := by
  refine (lightBdd_blockVal baseVC cVC ![0, 1] ![-1, 0] flowVC (by decide) (by decide) hm₀ hS₀
    hseg critA_VC critB_VC _ _ _ _
    (vNum_eq e 0 1 aVC baseVC cVC fun a b ρ σ => isOddG_aVC a b ρ σ)
    (isLoopPoly_vNum e 0 1 aVC baseVC cVC) (isLoopPoly_vNumE2 e 0 1 aVC baseVC cVC)
    (fun m k a' b' i j => rb_vNum e 0 1 aVC baseVC cVC (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVC baseVC cVC (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (isLoopPoly_vNum_k e 0 1 aVC baseVC cVC) Φ hmass μ ν).congr fun u _ a b _ _ => ?_
  rw [vVal_eq_blockVal]

end Classes

end QED.GradedProof.RPi4

end
