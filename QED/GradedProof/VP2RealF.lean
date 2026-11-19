/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2RealKinds
public import QED.GradedProof.VP2LimF
public import QED.GradedProof.SE2RealPiece

/-!
# The classes `F0`, `F1`: imaginary limits

Helper level for the Phase 5 Stage 2 goal (G-ex₂) `QED.Graded.existsUnique_withLevel_one`
(decision D-57), input `VPReal`; the phase counterpart of `QED/GradedProof/VP2FPieces.lean`,
`QED/GradedProof/VP2FTriple.lean` and `QED/GradedProof/VP2LimF.lean`.

* `VPFC T d F`: `F` is `VPF T` and, for every multiplier with a real limit, `h(ε) ∫ F` has a limit
  with phase `d`; closed under sums, real-limit multipliers, real constants, pointwise equality.
* The tensor numerators `n_j` of the inserted bubble (traces of gamma matrices and slashes of real
  vectors, real counterterms, `V₀ = y²`) are real (`conj_tn`, `conj_tnS`), and so is the constant
  `kF = (2π)⁻⁴ (ie)² (-i) (1/i)³ = -(2π)⁻⁴ e²` (`conj_kF`). Through the auxiliary loop the one-loop
  pieces have phase `-1` (`vpfc_five`, …), hence so do the three-flavour and block-summed bubbles
  (`vpfc_insTriple`, `vpfc_fBubble`) and the classes (`hasConjLim_F0`, `hasConjLim_F1`).
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.VP2Real

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.GradedProof.SE2 QED.GradedProof.VP2 QED.GradedProof.SE2Real

/-- **One-loop families with a phase-`d` limit** for every multiplier with a real limit. -/
def VPFC (T : ℝ) (d : ℂ) (F : ℝ → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  VPF T F ∧ ∀ (h : ℝ → ℂ) (h₀ : ℝ), Tendsto h (𝓝[>] 0) (𝓝 (h₀ : ℂ)) →
    HasConjLim T d fun ε k i j => h ε * QED.OneLoop.energyFirstIntegral fun q => F ε k q i j

namespace VPFC

variable {T : ℝ} {d : ℂ} {F G : ℝ → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

theorem add (hF : VPFC T d F) (hG : VPFC T d G) :
    VPFC T d fun ε k q i j => F ε k q i j + G ε k q i j := by
  refine ⟨hF.1.add hG.1, fun h h₀ hh => ((hF.2 h h₀ hh).add (hG.2 h h₀ hh)).congr
    fun k _ i j => ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [efi_add (hF.1.2 ε hε k i j) (hG.1.2 ε hε k i j), mul_add]

theorem mul (hF : VPFC T d F) {c : ℝ → ℂ} {c₀ : ℝ} (hc : Tendsto c (𝓝[>] 0) (𝓝 (c₀ : ℂ))) :
    VPFC T d fun ε k q i j => c ε * F ε k q i j := by
  refine ⟨hF.1.mul hc, fun h h₀ hh => ?_⟩
  have hm : Tendsto (fun ε => h ε * c ε) (𝓝[>] 0) (𝓝 ((h₀ * c₀ : ℝ) : ℂ)) := by
    rw [ofReal_mul]
    exact hh.mul hc
  refine (hF.2 (fun ε => h ε * c ε) _ hm).congr fun k _ i j => ?_
  filter_upwards with ε
  rw [QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul, mul_assoc]

/-- Multiplication by a constant fixed by conjugation. -/
theorem const_mul_conj (hF : VPFC T d F) (c : ℂ) (hc : starRingEnd ℂ c = c) :
    VPFC T d fun ε k q i j => c * F ε k q i j := by
  have hc' : c = ((c.re : ℝ) : ℂ) := (Complex.conj_eq_iff_re.mp hc).symm
  exact hF.mul (c := fun _ => c) (c₀ := c.re) (by rw [← hc']; exact tendsto_const_nhds)

theorem congr (hF : VPFC T d F)
    (e : ∀ ε : ℝ, 0 < ε → ∀ k q i j, F ε k q i j = G ε k q i j) : VPFC T d G := by
  refine ⟨hF.1.congr e, fun h h₀ hh => (hF.2 h h₀ hh).congr fun k _ i j => ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [show (fun q => F ε k q i j) = fun q => G ε k q i j from funext (e ε hε k · i j)]

theorem sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hF : ∀ a ∈ s, VPFC T d (F a)) (hT : -T ^ 2 < 0) :
    VPFC T d fun ε k q i j => ∑ a ∈ s, F a ε k q i j := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨(VPF.sum (∅ : Finset ι) (F := F) (fun _ h => absurd h (Finset.notMem_empty _))
      hT).congr fun _ _ _ _ _ _ => by simp, fun h h₀ hh => (HasConjLim.zero).congr
      fun k _ i j => ?_⟩
    filter_upwards with ε
    simp [QED.OneLoop.energyFirstIntegral]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))

/-- The energy-first integral of a `VPFC` family has a limit with phase `d`. -/
theorem hasConjLim (hF : VPFC T d F) :
    HasConjLim T d fun ε k i j => QED.OneLoop.energyFirstIntegral fun q => F ε k q i j :=
  (hF.2 (fun _ => 1) 1 (by rw [ofReal_one]; exact tendsto_const_nhds)).congr fun _ _ _ _ => by
    filter_upwards with ε
    rw [one_mul]

end VPFC

/-! ### Real numerators -/

theorem conj_insT0 (μ ν : Fin 4) (d₂ : ℝ) (x y : Fin 4 → ℝ) :
    starRingEnd ℂ (insT0 (Dirac.gamma μ) (Dirac.gamma ν) d₂ x y) =
      insT0 (Dirac.gamma μ) (Dirac.gamma ν) d₂ x y := by
  simp only [insT0, map_mul, map_neg, Complex.conj_ofReal]
  rw [conj_trace_of_sharp (by simp only [sharp_mul, sharp_gamma, sharp_slash])]

theorem conj_insT2 (μ ν : Fin 4) (d₂ dm : ℝ) (x y : Fin 4 → ℝ) :
    starRingEnd ℂ (insT2 (Dirac.gamma μ) (Dirac.gamma ν) d₂ dm x y) =
      insT2 (Dirac.gamma μ) (Dirac.gamma ν) d₂ dm x y := by
  simp only [insT2, map_add, map_mul, map_sub, map_ofNat, Complex.conj_ofReal]
  rw [conj_trace_of_sharp (by simp only [sharp_mul, sharp_gamma, sharp_slash]),
    conj_trace_of_sharp (by simp only [sharp_mul, sharp_gamma, sharp_slash])]

theorem conj_insT4 (μ ν : Fin 4) (dm : ℝ) :
    starRingEnd ℂ (insT4 (Dirac.gamma μ) (Dirac.gamma ν) dm) =
      insT4 (Dirac.gamma μ) (Dirac.gamma ν) dm := by
  simp only [insT4, map_mul, Complex.conj_ofReal]
  rw [conj_trace_of_sharp (by simp only [sharp_mul, sharp_gamma])]

theorem conj_v0 (y : Fin 4 → ℝ) : starRingEnd ℂ (v0 y) = v0 y := conj_propDenom_zero 0 y

theorem conj_tn (j : Fin 3) (d₂ dm : ℝ) (bx bY : Bool) (k q : Fin 4 → ℝ) (μ ν : Fin 4) :
    starRingEnd ℂ (tn j d₂ dm bx bY k q μ ν) = tn j d₂ dm bx bY k q μ ν := by
  match j with
  | 0 => simp only [tn, nT0, map_add, map_sub, map_mul, map_pow, conj_insT0, conj_insT2,
      conj_insT4, conj_v0]
  | 1 => simp only [tn, nT1, map_sub, map_mul, map_ofNat, conj_insT2, conj_insT4, conj_v0]
  | 2 => simp only [tn, nT2, conj_insT4]

theorem conj_tnS (sw : Bool) (j : Fin 3) (d₂ dm : ℝ) (bx bY : Bool) (k q : Fin 4 → ℝ)
    (μ ν : Fin 4) :
    starRingEnd ℂ (tnS sw j d₂ dm bx bY k q μ ν) = 1 * tnS sw j d₂ dm bx bY k q μ ν := by
  rw [one_mul]
  cases sw
  · exact conj_tn j d₂ dm bx bY k q μ ν
  · exact conj_tn j d₂ dm bx bY k q ν μ

theorem conj_kF (e : ℝ) : starRingEnd ℂ (kF e) = kF e := by
  simp only [kF, map_mul, map_inv₀, map_neg, map_pow, Complex.conj_I, Complex.conj_ofReal,
    one_div, Complex.inv_I, neg_neg]
  ring

theorem tendsto_epsI' : Tendsto (fun ε : ℝ => (ε : ℂ) * I) (𝓝[>] 0) (𝓝 ((0 : ℝ) : ℂ)) := by
  rw [ofReal_zero]
  exact tendsto_epsI

theorem tendsto_epsI2 : Tendsto (fun ε : ℝ => ((ε : ℂ) * I) ^ 2) (𝓝[>] 0) (𝓝 ((0 : ℝ) : ℂ)) := by
  have h := tendsto_epsI.pow 2
  rwa [zero_pow two_ne_zero, ← ofReal_zero] at h

theorem tendsto_epsI_two :
    Tendsto (fun ε : ℝ => 2 * ((ε : ℂ) * I)) (𝓝[>] 0) (𝓝 ((0 : ℝ) : ℂ)) := by
  have h := tendsto_epsI.const_mul 2
  rwa [mul_zero, ← ofReal_zero] at h

/-! ### Pieces -/

section PiecesC

variable {m₀ : ℝ} (hm₀ : 0 < m₀)
include hm₀

theorem vpfc_five (m0 m1 m2 m3 m4 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3 ∧ m₀ ≤ m4)
    (c0 c1 c2 c3 c4 : Bool) (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 4 fun ℓ => N p (ℓ 0) i j) (hcov : TCovN N)
    {d : ℕ} (hpoly : ∀ q i j, IsLoopPoly 1 d fun y => N (y 0) q i j) {ph : ℂ}
    (hph : ∀ p q i j, starRingEnd ℂ (N p q i j) = ph * N p q i j) :
    VPFC (m₀ + m₀) (-ph) fun ε k q i j => N k q i j * ((propDenom m0 ε (zk k c0 q))⁻¹ *
      (propDenom m1 ε (zk k c1 q))⁻¹ * (propDenom m2 ε (zk k c2 q))⁻¹ *
      (propDenom m3 ε (zk k c3 q))⁻¹ * (propDenom m4 ε (zk k c4 q))⁻¹) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hm
  refine ⟨vpf_five hm₀ m0 m1 m2 m3 m4 ⟨h0, h1, h2, h3, h4⟩ c0 c1 c2 c3 c4 N hN hcov hpoly,
    fun h h₀ hh => ?_⟩
  refine (hasConjLim_five hm₀ ![m0, m1, m2, m3, m4] (fun l => by fin_cases l <;> assumption)
    ![c0, c1, c2, c3, c4] N hN hcov hpoly hph hh).congr fun k _ i j => ?_
  filter_upwards with ε
  simp only [Fin.prod_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  rfl

theorem vpfc_four (m0 m1 m2 m3 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3)
    (c0 c1 c2 c3 : Bool) (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 2 fun ℓ => N p (ℓ 0) i j) (hcov : TCovN N)
    {d : ℕ} (hpoly : ∀ q i j, IsLoopPoly 1 d fun y => N (y 0) q i j) {ph : ℂ}
    (hph : ∀ p q i j, starRingEnd ℂ (N p q i j) = ph * N p q i j) :
    VPFC (m₀ + m₀) (-ph) fun ε k q i j => N k q i j * ((propDenom m0 ε (zk k c0 q))⁻¹ *
      (propDenom m1 ε (zk k c1 q))⁻¹ * (propDenom m2 ε (zk k c2 q))⁻¹ *
      (propDenom m3 ε (zk k c3 q))⁻¹) := by
  obtain ⟨h0, h1, h2, h3⟩ := hm
  refine ⟨vpf_four hm₀ m0 m1 m2 m3 ⟨h0, h1, h2, h3⟩ c0 c1 c2 c3 N hN hcov hpoly,
    fun h h₀ hh => ?_⟩
  refine (hasConjLim_four hm₀ ![m0, m1, m2, m3] (fun l => by fin_cases l <;> assumption)
    ![c0, c1, c2, c3] N hN hcov hpoly hph hh).congr fun k _ i j => ?_
  filter_upwards with ε
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  rfl

theorem vpfc_three (m0 m1 m2 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2)
    (c0 c1 c2 : Bool) (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 0 fun ℓ => N p (ℓ 0) i j) (hcov : TCovN N)
    {d : ℕ} (hpoly : ∀ q i j, IsLoopPoly 1 d fun y => N (y 0) q i j) {ph : ℂ}
    (hph : ∀ p q i j, starRingEnd ℂ (N p q i j) = ph * N p q i j) :
    VPFC (m₀ + m₀) (-ph) fun ε k q i j => N k q i j * ((propDenom m0 ε (zk k c0 q))⁻¹ *
      (propDenom m1 ε (zk k c1 q))⁻¹ * (propDenom m2 ε (zk k c2 q))⁻¹) := by
  obtain ⟨h0, h1, h2⟩ := hm
  refine ⟨vpf_three hm₀ m0 m1 m2 ⟨h0, h1, h2⟩ c0 c1 c2 N hN hcov hpoly,
    fun h h₀ hh => ?_⟩
  refine (hasConjLim_three hm₀ ![m0, m1, m2] (fun l => by fin_cases l <;> assumption)
    ![c0, c1, c2] N hN hcov hpoly hph hh).congr fun k _ i j => ?_
  filter_upwards with ε
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail]
  rfl

end PiecesC

section TripleC

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool)
include hm₀

theorem vpfc_E0 (m0 m1 m2 m3 m4 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3 ∧ m₀ ≤ m4)
    (c0 c1 c2 c3 c4 : Bool) :
    VPFC (m₀ + m₀) (-1) fun ε k q i j => (tnS sw 0 d₂ dm bx bY k q i j +
      (ε * I) * tnS sw 1 d₂ dm bx bY k q i j + (ε * I) ^ 2 * tnS sw 2 d₂ dm bx bY k q i j) *
      ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
        (propDenom m2 ε (zk k c2 q))⁻¹ * (propDenom m3 ε (zk k c3 q))⁻¹ *
        (propDenom m4 ε (zk k c4 q))⁻¹) := by
  have P := fun (j : Fin 3)
      (hN : ∀ p i l, IsLoopPoly 2 4 fun ℓ => tnS sw j d₂ dm bx bY p (ℓ 0) i l) =>
    vpfc_five hm₀ m0 m1 m2 m3 m4 hm c0 c1 c2 c3 c4 (tnS sw j d₂ dm bx bY) hN
      (tcovN_tnS sw j d₂ dm bx bY) (isLoopPoly_tnS_k sw j d₂ dm bx bY) (conj_tnS sw j d₂ dm bx bY)
  have p0 := P 0 (isLoopPoly_tnS0 sw d₂ dm bx bY)
  have p1 := (P 1 fun p i l => (isLoopPoly_tnS1 sw d₂ dm bx bY p i l).mono (by norm_num)).mul
    tendsto_epsI'
  have p2 := (P 2 fun p i l => (isLoopPoly_tnS2 sw d₂ dm bx bY p i l).mono (by norm_num)).mul
    tendsto_epsI2
  refine ((p0.add p1).add p2).congr fun ε _ k q i j => ?_
  ring

theorem vpfc_E2 (m0 m1 m2 m3 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3)
    (c0 c1 c2 c3 : Bool) :
    VPFC (m₀ + m₀) (-1) fun ε k q i j => (tnS sw 1 d₂ dm bx bY k q i j +
      2 * (ε * I) * tnS sw 2 d₂ dm bx bY k q i j) *
      ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
        (propDenom m2 ε (zk k c2 q))⁻¹ * (propDenom m3 ε (zk k c3 q))⁻¹) := by
  have p1 := vpfc_four hm₀ m0 m1 m2 m3 hm c0 c1 c2 c3 (tnS sw 1 d₂ dm bx bY)
    (isLoopPoly_tnS1 sw d₂ dm bx bY) (tcovN_tnS sw 1 d₂ dm bx bY)
    (isLoopPoly_tnS_k sw 1 d₂ dm bx bY) (conj_tnS sw 1 d₂ dm bx bY)
  have p2 := (vpfc_four hm₀ m0 m1 m2 m3 hm c0 c1 c2 c3 (tnS sw 2 d₂ dm bx bY)
    (fun p i l => (isLoopPoly_tnS2 sw d₂ dm bx bY p i l).mono (by norm_num))
    (tcovN_tnS sw 2 d₂ dm bx bY) (isLoopPoly_tnS_k sw 2 d₂ dm bx bY)
    (conj_tnS sw 2 d₂ dm bx bY)).mul
    tendsto_epsI_two
  refine (p1.add p2).congr fun ε _ k q i j => ?_
  ring

theorem vpfc_E4 (m0 m1 m2 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2) (c0 c1 c2 : Bool) :
    VPFC (m₀ + m₀) (-1) fun ε k q i j => tnS sw 2 d₂ dm bx bY k q i j *
      ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
        (propDenom m2 ε (zk k c2 q))⁻¹) :=
  vpfc_three hm₀ m0 m1 m2 hm c0 c1 c2 (tnS sw 2 d₂ dm bx bY) (isLoopPoly_tnS2 sw d₂ dm bx bY)
    (tcovN_tnS sw 2 d₂ dm bx bY) (isLoopPoly_tnS_k sw 2 d₂ dm bx bY)
    (conj_tnS sw 2 d₂ dm bx bY)

/-- **The three-flavour inserted bubble has a purely imaginary limit.** -/
theorem vpfc_insTriple (M X Y : ℝ) (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y)
    (hXY : X ^ 2 - Y ^ 2 ≠ 0) :
    VPFC (m₀ + m₀) (-1) fun ε k q i j =>
      insG (gAF sw i j) (gBF sw i j) d₂ dm M ε (zk k bx q) (zk k bY q) +
        (triA M X Y : ℂ) * insG (gAF sw i j) (gBF sw i j) d₂ dm X ε (zk k bx q) (zk k bY q) +
        (triB M X Y : ℂ) * insG (gAF sw i j) (gBF sw i j) d₂ dm Y ε (zk k bx q) (zk k bY q) := by
  have E0 := vpfc_E0 hm₀ sw d₂ dm bx bY
  have E2 := vpfc_E2 hm₀ sw d₂ dm bx bY
  have s := ((((((((((E0 M M X Y M ⟨hM, hM, hX, hY, hM⟩ bx bY bY bY bY).add
    (E0 M M X Y X ⟨hM, hM, hX, hY, hX⟩ bx bY bY bY bY)).add
    (E0 M M X Y Y ⟨hM, hM, hX, hY, hY⟩ bx bY bY bY bY)).add
    (E0 M X X Y X ⟨hM, hX, hX, hY, hX⟩ bx bx bY bY bY)).add
    (E0 M X X Y Y ⟨hM, hX, hX, hY, hY⟩ bx bx bY bY bY)).add
    (E0 M X Y Y Y ⟨hM, hX, hY, hY, hY⟩ bx bx bx bY bY)).add
    (E2 M M X Y ⟨hM, hM, hX, hY⟩ bx bY bY bY)).add
    (E2 M X X Y ⟨hM, hX, hX, hY⟩ bx bx bY bY)).add
    (E2 M X Y Y ⟨hM, hX, hY, hY⟩ bx bx bx bY)).add
    (vpfc_E4 hm₀ sw d₂ dm bx bY M X Y ⟨hM, hX, hY⟩ bx bx bx)).const_mul_conj
    (((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2))
    (by simp only [map_mul, map_sub, map_pow, Complex.conj_ofReal])
  refine s.congr fun ε hε k q i j => ?_
  have hA : IsOddG (gAF sw i j) := isOddG_gamma _
  have hB : IsOddG (gBF sw i j) := isOddG_gamma _
  rw [insTriple_eq hA hB d₂ dm M X Y hXY hε.ne' (zk k bx q) (zk k bY q),
    nT0_gAB, nT1_gAB, nT2_gAB sw d₂ dm bx bY k q]

end TripleC

/-! ### The classes -/

section Classes

open QED.Graded
open QED.WickModel (Params)

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F) (rep : F → F)

/-- **The block-summed inserted bubble has a purely imaginary limit.** -/
theorem vpfc_fBubble (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (sw bx bY : Bool) :
    VPFC (m₀ + m₀) (-1) fun ε k q μ ν => fBubble P Φ D rep sw bx bY ε k q μ ν := by
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  set X : ℝ := auxX Φ with hX
  have hlt : ∀ g, Φ.mass g < X := fun g => by
    have := Finset.single_le_sum (f := Φ.mass) (fun g _ => (hpos g).le) (Finset.mem_univ g)
    simp only [hX, auxX]
    linarith
  have hX0 : 0 < X := by
    have := Finset.sum_nonneg (s := Finset.univ) fun g (_ : g ∈ Finset.univ) => (hpos g).le
    simp only [hX, auxX]
    linarith
  have hXY : X ^ 2 - (X + 1) ^ 2 ≠ 0 := by nlinarith
  refine (VPFC.sum Finset.univ (fun f _ => (vpfc_insTriple hm₀ sw (P.e ^ 2 * D.d₂ (rep f) 0)
    (P.e ^ 2 * D.dm (rep f) 0) bx bY (Φ.mass f) X (X + 1) (hmass f)
    (by linarith [hlt f, hmass f]) (by linarith [hlt f, hmass f]) hXY).const_mul_conj
      ((Φ.coeff f : ℂ) * kF P.e) (by rw [map_mul, Complex.conj_ofReal, conj_kF]))
    (by nlinarith)).congr fun ε _ k q μ ν => ?_
  simp only [fBubble]
  rw [sum_block_eq_sum_triple Φ rep hrep hPV₁ hPV₂ X (X + 1) (fun r M => kF P.e *
    insG (gAF sw μ ν) (gBF sw μ ν) (P.e ^ 2 * D.d₂ r 0) (P.e ^ 2 * D.dm r 0) M ε (zk k bx q)
      (zk k bY q))]
  refine Finset.sum_congr rfl fun f _ => ?_
  ring


/-- **The class `F0` has a purely imaginary limit.** -/
theorem hasConjLim_F0 (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0) :
    HasConjLim (m₀ + m₀) (-1) fun ε k μ ν => val0 { P with ε := ε } Φ D k μ ν repF0 :=
  (vpfc_fBubble P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ true true false).hasConjLim.congr
    fun k _ μ ν => Eventually.of_forall fun ε =>
      (val0_repF0 { P with ε := ε } Φ D rep hD k μ ν).symm

/-- **The class `F1` has a purely imaginary limit.** -/
theorem hasConjLim_F1 (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0) :
    HasConjLim (m₀ + m₀) (-1) fun ε k μ ν => val0 { P with ε := ε } Φ D k μ ν repF1 :=
  (vpfc_fBubble P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ false false true).hasConjLim.congr
    fun k _ μ ν => Eventually.of_forall fun ε =>
      (val0_repF1 { P with ε := ε } Φ D rep hD k μ ν).symm

end Classes

end QED.GradedProof.VP2Real

end
