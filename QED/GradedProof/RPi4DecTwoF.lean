/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecSegTwo
public import QED.GradedProof.RPi4DecTwoTilt
public import QED.GradedProof.RPi4QDens

/-!
# (R-Π₄) step L9: second differences of the mass-insertion part of the density

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (second
differences in `s`), item D2s-b. The mass-insertion part of `QED.GradedProof.RPi4.qDens` is
`∑_g σ(M_g, t) · fLim(single g 1)(k'(s))`; the one-loop factor is of class `DecTwoReg` in `s`
(the eight-line pieces along the segment, `QED.GradedProof.RPi4.dec_segTwo_kinds`, and the tilt
chain rule `QED.GradedProof.RPi4.dec_twoReg_tilt`), and `|t σ(t)| ≤ e²/(4π²)` for all `t > 0`.

* `dec_segTwo_fVal5`, …, `dec_segTwo_fbVal`: the one-loop pieces;
* `dec_twoReg_fLim_tilt`: `s ↦ fLim(δ)(k'(s))₂₃` on `[S₀, S]`;
* `dec_abs_mul_sigma_le`: `|t σ(e, m, t)| ≤ e²/(4π²)`;
* `decMassDens`, **`dec_massDens_two`**: `‖Δ²ₕ decMassDens(s, t)‖ ≤ B h² / t`.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set
open scoped Real Interval

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.CountertermLimit
open QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance
open QED.Graded (Counterterms)
open QED.WickModel (Params)

/-! ### The one-loop pieces along the segment -/

section Pieces

variable {m₀ : ℝ} (hm₀ : 0 < m₀) {k₀ w : Fin 4 → ℝ} {S₀ : ℝ} (hS₀ : -(4 * m₀ ^ 2) < S₀)
  (hseg : ∀ u : ℝ, |u| ≤ 1 / 2 → S₀ ≤ Minkowski.dot (lineK k₀ w u) (lineK k₀ w u))
include hm₀ hS₀ hseg

theorem dec_segTwo_fVal5 (Ms : Fin 5 → ℝ) (hMs : ∀ l, m₀ ≤ Ms l) (b : Fin 5 → Bool)
    (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 4 fun ℓ => N p (ℓ 0) i j)
    {d : ℕ} (hpoly : ∀ q i j, IsLoopPoly 1 d fun y => N (y 0) q i j) (i j : Fin 4) :
    DecSegTwo k₀ w fun k => fVal5 m₀ Ms b N k i j := by
  have hsq : ∀ l, m₀ ^ 2 ≤ Ms l ^ 2 := fun l => pow_le_pow_left₀ hm₀.le (hMs l) 2
  have hM : ∀ i, m₀ ^ 2 ≤ (![Ms 0, Ms 1, Ms 2, Ms 3, Ms 4, m₀, m₀, m₀] : Fin 8 → ℝ) i ^ 2 := by
    intro i
    fin_cases i
    exacts [hsq 0, hsq 1, hsq 2, hsq 3, hsq 4, le_rfl, le_rfl, le_rfl]
  have hout : ∀ c : Bool, kd c ≠ .out := fun c => by cases c <;> decide
  have h := dec_segTwo_kinds (by norm_num) (kinds5 b) (fun i => by
      fin_cases i <;> simp [kinds5, hout])
    ![Ms 0, Ms 1, Ms 2, Ms 3, Ms 4, m₀, m₀, m₀] hm₀ hm₀ (fun i _ => hM i) (fun i _ => hM i)
    (crit_kinds5 _) (by decide) (ne_aux_kinds5 _) N hN hpoly
    (by nlinarith : -(m₀ + m₀) ^ 2 < S₀) hseg i j
  exact (h.const_mul (auxLimit m₀)⁻¹).congr fun u _ => rfl

variable (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool)

theorem dec_segTwo_eVal0 (m0 m1 m2 m3 m4 : ℝ)
    (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3 ∧ m₀ ≤ m4) (c0 c1 c2 c3 c4 : Bool) (i j : Fin 4) :
    DecSegTwo k₀ w fun k => eVal0 m₀ sw d₂ dm bx bY m0 m1 m2 m3 m4 c0 c1 c2 c3 c4 k i j := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hm
  exact dec_segTwo_fVal5 hm₀ hS₀ hseg _ (fun l => by fin_cases l <;> assumption) _ _
    (isLoopPoly_tnS0 sw d₂ dm bx bY) (isLoopPoly_tnS_k sw 0 d₂ dm bx bY) i j

theorem dec_segTwo_eVal2 (m0 m1 m2 m3 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3)
    (c0 c1 c2 c3 : Bool) (i j : Fin 4) :
    DecSegTwo k₀ w fun k => eVal2 m₀ sw d₂ dm bx bY m0 m1 m2 m3 c0 c1 c2 c3 k i j := by
  obtain ⟨h0, h1, h2, h3⟩ := hm
  have hN' : ∀ p i j, IsLoopPoly 2 4 fun ℓ => padN (tnS sw 1 d₂ dm bx bY) m0 c0 p (ℓ 0) i j :=
    fun p i j => ((isLoopPoly_tnS1 sw d₂ dm bx bY p i j).mul
      ((isLoopAffine_zk p c0).isLoopPoly_propDenom m0 0)).mono (by norm_num)
  have hpoly' := fun q i j => (isLoopPoly_tnS_k sw 1 d₂ dm bx bY q i j).mul
    ((isLoopAffine_zk_one q c0).isLoopPoly_propDenom m0 0)
  exact dec_segTwo_fVal5 hm₀ hS₀ hseg _ (fun l => by fin_cases l <;> assumption) _ _ hN' hpoly'
    i j

theorem dec_segTwo_eVal4 (m0 m1 m2 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2) (c0 c1 c2 : Bool)
    (i j : Fin 4) :
    DecSegTwo k₀ w fun k => eVal4 m₀ sw d₂ dm bx bY m0 m1 m2 c0 c1 c2 k i j := by
  obtain ⟨h0, h1, h2⟩ := hm
  have hN' : ∀ p i j, IsLoopPoly 2 2 fun ℓ => padN (tnS sw 2 d₂ dm bx bY) m0 c0 p (ℓ 0) i j :=
    fun p i j => ((isLoopPoly_tnS2 sw d₂ dm bx bY p i j).mul
      ((isLoopAffine_zk p c0).isLoopPoly_propDenom m0 0)).mono (by norm_num)
  have hN'' : ∀ p i j, IsLoopPoly 2 4 fun ℓ =>
      padN (padN (tnS sw 2 d₂ dm bx bY) m0 c0) m0 c0 p (ℓ 0) i j :=
    fun p i j => ((hN' p i j).mul ((isLoopAffine_zk p c0).isLoopPoly_propDenom m0 0)).mono
      (by norm_num)
  have hpoly' := fun q i j => (isLoopPoly_tnS_k sw 2 d₂ dm bx bY q i j).mul
    ((isLoopAffine_zk_one q c0).isLoopPoly_propDenom m0 0)
  have hpoly'' := fun q i j => (hpoly' q i j).mul
    ((isLoopAffine_zk_one q c0).isLoopPoly_propDenom m0 0)
  exact dec_segTwo_fVal5 hm₀ hS₀ hseg _ (fun l => by fin_cases l <;> assumption) _ _ hN'' hpoly''
    i j

theorem dec_segTwo_insVal (M X Y : ℝ) (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y) (i j : Fin 4) :
    DecSegTwo k₀ w fun k => insVal m₀ sw d₂ dm bx bY M X Y k i j := by
  have E0 := fun m0 m1 m2 m3 m4 hm c0 c1 c2 c3 c4 =>
    dec_segTwo_eVal0 hm₀ hS₀ hseg sw d₂ dm bx bY m0 m1 m2 m3 m4 hm c0 c1 c2 c3 c4 i j
  have E2 := fun m0 m1 m2 m3 hm c0 c1 c2 c3 =>
    dec_segTwo_eVal2 hm₀ hS₀ hseg sw d₂ dm bx bY m0 m1 m2 m3 hm c0 c1 c2 c3 i j
  have E4 := dec_segTwo_eVal4 hm₀ hS₀ hseg sw d₂ dm bx bY M X Y ⟨hM, hX, hY⟩ bx bx bx i j
  exact (((((((((((E0 M M X Y M ⟨hM, hM, hX, hY, hM⟩ bx bY bY bY bY).add
    (E0 M M X Y X ⟨hM, hM, hX, hY, hX⟩ bx bY bY bY bY)).add
    (E0 M M X Y Y ⟨hM, hM, hX, hY, hY⟩ bx bY bY bY bY)).add
    (E0 M X X Y X ⟨hM, hX, hX, hY, hX⟩ bx bx bY bY bY)).add
    (E0 M X X Y Y ⟨hM, hX, hX, hY, hY⟩ bx bx bY bY bY)).add
    (E0 M X Y Y Y ⟨hM, hX, hY, hY, hY⟩ bx bx bx bY bY)).add
    (E2 M M X Y ⟨hM, hM, hX, hY⟩ bx bY bY bY)).add
    (E2 M X X Y ⟨hM, hX, hX, hY⟩ bx bx bY bY)).add
    (E2 M X Y Y ⟨hM, hX, hY, hY⟩ bx bx bx bY)).add E4).const_mul _).congr fun u _ => rfl

end Pieces

theorem dec_segTwo_fbVal (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (rep : F → F) {m₀ : ℝ} (D : Counterterms F) {k₀ w : Fin 4 → ℝ}
    {S₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hS₀ : -(4 * m₀ ^ 2) < S₀)
    (hseg : ∀ u : ℝ, |u| ≤ 1 / 2 → S₀ ≤ Minkowski.dot (lineK k₀ w u) (lineK k₀ w u))
    (sw bx bY : Bool) (i j : Fin 4) :
    DecSegTwo k₀ w fun k => fbVal P Φ D rep m₀ sw bx bY k i j := by
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  have hlt : ∀ g, Φ.mass g < auxX Φ := fun g => by
    have := Finset.single_le_sum (f := Φ.mass) (fun g _ => (hpos g).le) (Finset.mem_univ g)
    simp only [auxX]
    linarith
  exact (DecSegTwo.sum Finset.univ fun f _ => (dec_segTwo_insVal hm₀ hS₀ hseg sw _ _ bx bY
    (Φ.mass f) (auxX Φ) (auxX Φ + 1) (hmass f) (by linarith [hlt f, hmass f])
    (by linarith [hlt f, hmass f]) i j).const_mul ((Φ.coeff f : ℂ) * kF P.e)).congr
    fun u _ => rfl

/-! ### The weighted block along the tilted vectors -/

section Block

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F]
  (Φ : Lepton.Flavors F) (rep : F → F)
  {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **The limit of the weighted block at the tilted vectors is of class `DecTwoReg` in `s`.** -/
theorem dec_twoReg_fLim_tilt (he : P.e ≠ 0) (δ : F → ℝ) {c S₀ S : ℝ}
    (hS₀ : -(4 * m₀ ^ 2) < S₀) (hS₀S : S₀ < S) (hS : S < 2 * c ^ 2) :
    ∃ M L K : ℝ, DecTwoReg S₀ S (fun s => fLim Φ rep P.e δ (tiltVec c s) 2 3) M L K := by
  have hseg := fun u (hu : |u| ≤ 1 / 2) => (dot_lineK_tilt_mem (c := c) hS hS₀S.le hu).1
  obtain ⟨M, L, K, h⟩ := DecSegTwo.congr (H := fun k => fLim Φ rep P.e δ k 2 3)
    ((dec_segTwo_fbVal P Φ rep (ctδ (ctOf P.e δ)) hm₀ hmass hS₀ hseg true true false 2 3).add
      (dec_segTwo_fbVal P Φ rep (ctδ (ctOf P.e δ)) hm₀ hmass hS₀ hseg false false true 2 3))
      fun u hu => (fLim_eq_fbVal P Φ rep hm₀ hmass hrep hPV₁ hPV₂ he δ
        (by linarith [hseg u hu]) 2 3).symm
  obtain ⟨L', K', h'⟩ := dec_twoReg_tilt (G := fun k => fLim Φ rep P.e δ k 2 3) hS₀S hS h
  exact ⟨M, L', K', h'⟩

end Block

/-! ### The mass-insertion density -/

/-- **`|t σ(e, m, t)| ≤ e²/(4π²)`** for every `t > 0`. -/
theorem dec_abs_mul_sigma_le (e : ℝ) {m t : ℝ} (hm : m ≠ 0) (ht : 0 < t) :
    |t * sigma e m t| ≤ e ^ 2 / (4 * π ^ 2) := by
  have hb : ∀ x ∈ Ι (0 : ℝ) 1,
      ‖t * ((1 - x ^ 2) / (x ^ 2 * m ^ 2 + (1 - x) * t))‖ ≤ 2 := by
    intro x hx
    rw [uIoc_of_le zero_le_one] at hx
    have hD := onShell_denom_pos hm ⟨hx.1.le, hx.2⟩ ht
    have h1 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_div_assoc, div_le_iff₀ hD]
    nlinarith [mul_nonneg ht.le (sq_nonneg (1 - x)), sq_nonneg (x * m)]
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [intervalIntegral.integral_const_mul] at hI
  simp only [sub_zero, abs_one, mul_one, Real.norm_eq_abs] at hI
  rw [sigma, mul_left_comm, abs_mul, abs_neg, abs_of_nonneg (by positivity)]
  calc e ^ 2 / (8 * π ^ 2) * |t * ∫ x in (0 : ℝ)..1,
        (1 - x ^ 2) / (x ^ 2 * m ^ 2 + (1 - x) * t)|
      ≤ e ^ 2 / (8 * π ^ 2) * 2 := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = e ^ 2 / (4 * π ^ 2) := by ring

section Mass

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

/-- The mass-insertion part of `qDens` (before the factor `-i/c²`):
`∑_g σ(M_g, t) fLim(single g 1)(k'(s))₂₃`. -/
noncomputable def decMassDens (e c s t : ℝ) : ℂ :=
  ∑ g, (sigma e (Φ.mass g) t : ℂ) * fLim Φ rep e (Pi.single g 1) (tiltVec c s) 2 3

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **Second differences of the mass-insertion density**: `‖Δ²ₕ decMassDens(s, t)‖ ≤ B h² / t`
for `s, s + 2h ∈ [S₀, S]` and every `t > 0`. -/
theorem dec_massDens_two (P : Params) (he : P.e ≠ 0) {c S₀ S : ℝ}
    (hS₀ : -(4 * m₀ ^ 2) < S₀) (hS₀S : S₀ < S) (hS : S < 2 * c ^ 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s h : ℝ, s ∈ Icc S₀ S → s + 2 * h ∈ Icc S₀ S → ∀ t : ℝ, 0 < t →
      ‖decMassDens Φ rep P.e c (s + 2 * h) t - 2 * decMassDens Φ rep P.e c (s + h) t +
        decMassDens Φ rep P.e c s t‖ ≤ B / t * h ^ 2 := by
  choose Mg Lg Kg hg using fun g : F => dec_twoReg_fLim_tilt P Φ rep hm₀ hmass hrep hPV₁ hPV₂
    he (Pi.single g 1) hS₀ hS₀S hS
  set A : ℝ := P.e ^ 2 / (4 * π ^ 2)
  have hA : 0 ≤ A := by positivity
  have hK : ∀ g, 0 ≤ Kg g := fun g => (hg g).nonneg.2.2
  refine ⟨A * ∑ g, Kg g, mul_nonneg hA (Finset.sum_nonneg fun g _ => hK g),
    fun s h hs h2 t ht => ?_⟩
  set Fg : F → ℝ → ℂ := fun g s => fLim Φ rep P.e (Pi.single g 1) (tiltVec c s) 2 3
  have e : decMassDens Φ rep P.e c (s + 2 * h) t - 2 * decMassDens Φ rep P.e c (s + h) t +
      decMassDens Φ rep P.e c s t = ∑ g, (sigma P.e (Φ.mass g) t : ℂ) *
        (Fg g (s + 2 * h) - 2 * Fg g (s + h) + Fg g s) := by
    simp only [decMassDens, Fg, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    ring
  rw [e, Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => ?_)
  have hσ : ‖(sigma P.e (Φ.mass g) t : ℂ)‖ ≤ A / t := by
    rw [Complex.norm_real, Real.norm_eq_abs, le_div_iff₀ ht, mul_comm, ← abs_of_pos ht,
      ← abs_mul, abs_of_pos ht]
    exact dec_abs_mul_sigma_le P.e (hm₀.trans_le (hmass g)).ne' ht
  rw [norm_mul]
  calc ‖(sigma P.e (Φ.mass g) t : ℂ)‖ * ‖Fg g (s + 2 * h) - 2 * Fg g (s + h) + Fg g s‖
      ≤ A / t * (Kg g * h ^ 2) :=
        mul_le_mul hσ ((hg g).two s h hs h2) (norm_nonneg _) (by positivity)
    _ = A * Kg g / t * h ^ 2 := by ring

end Mass

end QED.GradedProof.RPi4

end
