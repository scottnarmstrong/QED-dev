/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecSegLip
public import QED.GradedProof.RPi4DecContF

/-!
# (R-Π₄) step L9: the one-loop functional is Lipschitz near `s = 0` (`DecLipD`)

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (decoupling),
regularity input D3c₂ (`DecLipD48`) of `QED.GradedProof.RPi4.dec_scalAff_of_weak`. As for
continuity (`RPi4DecContF`): `fLim` is a finite sum of eight-line parametric values, each
Lipschitz along a segment (`QED.GradedProof.RPi4.dec_segLip_kinds`), and the segment parameter of
the tilted vector `k'(s)` is Lipschitz in `s` (`|u - u'| ≤ (4/3) |t(u) - t(u')|`, and `t` is
affine in `√(2c² - s)`).

* `dec_segLip_fVal5`, …, `dec_segLip_fbVal`: the one-loop pieces;
* `dec_abs_sub_le_tpar`, `dec_lip_tilt`: Lipschitz along the segment gives Lipschitz in `s`;
* `dec_lip_fLim_tilt`, `dec_lip_projS_fLim`;
* **`dec_lipD : DecLipD P.e`** (every configuration `x > 0`), hence `dec_lipD48`.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set
open scoped Real

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

theorem dec_segLip_fVal5 (Ms : Fin 5 → ℝ) (hMs : ∀ l, m₀ ≤ Ms l) (b : Fin 5 → Bool)
    (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 4 fun ℓ => N p (ℓ 0) i j)
    {d : ℕ} (hpoly : ∀ q i j, IsLoopPoly 1 d fun y => N (y 0) q i j) (i j : Fin 4) :
    DecSegLip k₀ w fun k => fVal5 m₀ Ms b N k i j := by
  have hsq : ∀ l, m₀ ^ 2 ≤ Ms l ^ 2 := fun l => pow_le_pow_left₀ hm₀.le (hMs l) 2
  have hM : ∀ i, m₀ ^ 2 ≤ (![Ms 0, Ms 1, Ms 2, Ms 3, Ms 4, m₀, m₀, m₀] : Fin 8 → ℝ) i ^ 2 := by
    intro i
    fin_cases i
    exacts [hsq 0, hsq 1, hsq 2, hsq 3, hsq 4, le_rfl, le_rfl, le_rfl]
  have hout : ∀ c : Bool, kd c ≠ .out := fun c => by cases c <;> decide
  have h := dec_segLip_kinds (by norm_num) (kinds5 b) (fun i => by
      fin_cases i <;> simp [kinds5, hout])
    ![Ms 0, Ms 1, Ms 2, Ms 3, Ms 4, m₀, m₀, m₀] hm₀ hm₀ (fun i _ => hM i) (fun i _ => hM i)
    (crit_kinds5 _) (by decide) (ne_aux_kinds5 _) N hN hpoly
    (by nlinarith : -(m₀ + m₀) ^ 2 < S₀) hseg i j
  exact (h.const_mul (auxLimit m₀)⁻¹).congr fun u _ => rfl

variable (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool)

theorem dec_segLip_eVal0 (m0 m1 m2 m3 m4 : ℝ)
    (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3 ∧ m₀ ≤ m4) (c0 c1 c2 c3 c4 : Bool) (i j : Fin 4) :
    DecSegLip k₀ w fun k => eVal0 m₀ sw d₂ dm bx bY m0 m1 m2 m3 m4 c0 c1 c2 c3 c4 k i j := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hm
  exact dec_segLip_fVal5 hm₀ hS₀ hseg _ (fun l => by fin_cases l <;> assumption) _ _
    (isLoopPoly_tnS0 sw d₂ dm bx bY) (isLoopPoly_tnS_k sw 0 d₂ dm bx bY) i j

theorem dec_segLip_eVal2 (m0 m1 m2 m3 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3)
    (c0 c1 c2 c3 : Bool) (i j : Fin 4) :
    DecSegLip k₀ w fun k => eVal2 m₀ sw d₂ dm bx bY m0 m1 m2 m3 c0 c1 c2 c3 k i j := by
  obtain ⟨h0, h1, h2, h3⟩ := hm
  have hN' : ∀ p i j, IsLoopPoly 2 4 fun ℓ => padN (tnS sw 1 d₂ dm bx bY) m0 c0 p (ℓ 0) i j :=
    fun p i j => ((isLoopPoly_tnS1 sw d₂ dm bx bY p i j).mul
      ((isLoopAffine_zk p c0).isLoopPoly_propDenom m0 0)).mono (by norm_num)
  have hpoly' := fun q i j => (isLoopPoly_tnS_k sw 1 d₂ dm bx bY q i j).mul
    ((isLoopAffine_zk_one q c0).isLoopPoly_propDenom m0 0)
  exact dec_segLip_fVal5 hm₀ hS₀ hseg _ (fun l => by fin_cases l <;> assumption) _ _ hN' hpoly'
    i j

theorem dec_segLip_eVal4 (m0 m1 m2 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2) (c0 c1 c2 : Bool)
    (i j : Fin 4) :
    DecSegLip k₀ w fun k => eVal4 m₀ sw d₂ dm bx bY m0 m1 m2 c0 c1 c2 k i j := by
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
  exact dec_segLip_fVal5 hm₀ hS₀ hseg _ (fun l => by fin_cases l <;> assumption) _ _ hN'' hpoly''
    i j

theorem dec_segLip_insVal (M X Y : ℝ) (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y) (i j : Fin 4) :
    DecSegLip k₀ w fun k => insVal m₀ sw d₂ dm bx bY M X Y k i j := by
  have E0 := fun m0 m1 m2 m3 m4 hm c0 c1 c2 c3 c4 =>
    dec_segLip_eVal0 hm₀ hS₀ hseg sw d₂ dm bx bY m0 m1 m2 m3 m4 hm c0 c1 c2 c3 c4 i j
  have E2 := fun m0 m1 m2 m3 hm c0 c1 c2 c3 =>
    dec_segLip_eVal2 hm₀ hS₀ hseg sw d₂ dm bx bY m0 m1 m2 m3 hm c0 c1 c2 c3 i j
  have E4 := dec_segLip_eVal4 hm₀ hS₀ hseg sw d₂ dm bx bY M X Y ⟨hM, hX, hY⟩ bx bx bx i j
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

theorem dec_segLip_fbVal (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (rep : F → F) {m₀ : ℝ} (D : Counterterms F) {k₀ w : Fin 4 → ℝ}
    {S₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hS₀ : -(4 * m₀ ^ 2) < S₀)
    (hseg : ∀ u : ℝ, |u| ≤ 1 / 2 → S₀ ≤ Minkowski.dot (lineK k₀ w u) (lineK k₀ w u))
    (sw bx bY : Bool) (i j : Fin 4) :
    DecSegLip k₀ w fun k => fbVal P Φ D rep m₀ sw bx bY k i j := by
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  have hlt : ∀ g, Φ.mass g < auxX Φ := fun g => by
    have := Finset.single_le_sum (f := Φ.mass) (fun g _ => (hpos g).le) (Finset.mem_univ g)
    simp only [auxX]
    linarith
  exact (DecSegLip.sum Finset.univ fun f _ => (dec_segLip_insVal hm₀ hS₀ hseg sw _ _ bx bY
    (Φ.mass f) (auxX Φ) (auxX Φ + 1) (hmass f) (by linarith [hlt f, hmass f])
    (by linarith [hlt f, hmass f]) i j).const_mul ((Φ.coeff f : ℂ) * kF P.e)).congr
    fun u _ => rfl

/-! ### Lipschitz in `s` at the tilted vectors -/

/-- The segment parameter is controlled by `t = u / (1 - u²)`: `|u - u'| ≤ (4/3) |t - t'|`. -/
theorem dec_abs_sub_le_tpar {u u' : ℝ} (hu : |u| ≤ 1 / 2) (hu' : |u'| ≤ 1 / 2) :
    |u - u'| ≤ 4 / 3 * |tpar u - tpar u'| := by
  have h1 : 3 / 4 ≤ 1 - u ^ 2 := by nlinarith [sq_abs u, abs_nonneg u]
  have h2 : 3 / 4 ≤ 1 - u' ^ 2 := by nlinarith [sq_abs u', abs_nonneg u']
  have h1' : 1 - u ^ 2 ≤ 1 := by nlinarith [sq_nonneg u]
  have h2' : 1 - u' ^ 2 ≤ 1 := by nlinarith [sq_nonneg u']
  have huu : 3 / 4 ≤ 1 + u * u' := by
    have : |u * u'| ≤ 1 / 4 := by
      rw [abs_mul]; nlinarith [abs_nonneg u, abs_nonneg u']
    linarith [neg_abs_le (u * u')]
  have e : tpar u - tpar u' = (u - u') * (1 + u * u') / ((1 - u ^ 2) * (1 - u' ^ 2)) := by
    simp only [tpar]
    field_simp
    ring
  rw [e, abs_div, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + u * u'),
    abs_of_pos (by positivity : (0 : ℝ) < (1 - u ^ 2) * (1 - u' ^ 2))]
  have hd : (1 - u ^ 2) * (1 - u' ^ 2) ≤ 1 := by nlinarith
  have hd0 : 0 < (1 - u ^ 2) * (1 - u' ^ 2) := by positivity
  rw [mul_div_assoc]
  have : 3 / 4 ≤ (1 + u * u') / ((1 - u ^ 2) * (1 - u' ^ 2)) := by
    rw [le_div_iff₀ hd0]; nlinarith
  nlinarith [abs_nonneg (u - u')]

/-- **Lipschitz along the segment gives Lipschitz in `s` at the tilted vectors.** -/
theorem dec_lip_tilt {c S₀ S : ℝ} (hS₀S : S₀ < S) (hS : S < 2 * c ^ 2)
    {G : (Fin 4 → ℝ) → ℂ} (hG : DecSegLip (tiltBase c S₀ S) (tiltDir c S₀ S) G) :
    ∃ L : ℝ, ∀ s s' : ℝ, s ∈ Icc S₀ S → s' ∈ Icc S₀ S →
      ‖G (tiltVec c s) - G (tiltVec c s')‖ ≤ L * |s - s'| := by
  obtain ⟨L, hL⟩ := hG
  set lo := Real.sqrt (2 * c ^ 2 - S)
  set hi := Real.sqrt (2 * c ^ 2 - S₀)
  have hlo : 0 < lo := Real.sqrt_pos.2 (by linarith)
  have hlohi : lo < hi := Real.sqrt_lt_sqrt (by linarith) (by linarith)
  set w := 3 / 4 * (hi - lo)
  have hw : 0 < w := by simp only [w]; linarith
  refine ⟨|L| * (4 / 3) / w / (2 * lo), fun s s' hs hs' => ?_⟩
  obtain ⟨hu, he⟩ := dec_tiltVec_eq_lineK hS₀S hS hs.1 hs.2
  obtain ⟨hu', he'⟩ := dec_tiltVec_eq_lineK hS₀S hS hs'.1 hs'.2
  rw [he, he']
  refine (hL _ _ hu hu').trans ?_
  have ht : ∀ r, tpar (decTiltU c S₀ S r) =
      (Real.sqrt (2 * c ^ 2 - r) - (lo + hi) / 2) / w := fun r => by
    rw [show decTiltU c S₀ S r = upar ((Real.sqrt (2 * c ^ 2 - r) - (lo + hi) / 2) / w)
      from rfl, tpar_upar]
  have hsq : |Real.sqrt (2 * c ^ 2 - s) - Real.sqrt (2 * c ^ 2 - s')| ≤ |s - s'| / (2 * lo) := by
    have ha : lo ≤ Real.sqrt (2 * c ^ 2 - s) := Real.sqrt_le_sqrt (by linarith [hs.2])
    have hb : lo ≤ Real.sqrt (2 * c ^ 2 - s') := Real.sqrt_le_sqrt (by linarith [hs'.2])
    have hA := Real.sq_sqrt (show 0 ≤ 2 * c ^ 2 - s by linarith [hs.2])
    have hB := Real.sq_sqrt (show 0 ≤ 2 * c ^ 2 - s' by linarith [hs'.2])
    rw [le_div_iff₀ (by positivity)]
    have e : (Real.sqrt (2 * c ^ 2 - s) - Real.sqrt (2 * c ^ 2 - s')) *
        (Real.sqrt (2 * c ^ 2 - s) + Real.sqrt (2 * c ^ 2 - s')) = s' - s := by
      nlinarith
    have : |Real.sqrt (2 * c ^ 2 - s) - Real.sqrt (2 * c ^ 2 - s')| *
        (Real.sqrt (2 * c ^ 2 - s) + Real.sqrt (2 * c ^ 2 - s')) = |s - s'| := by
      rw [← abs_of_pos (by linarith : 0 < Real.sqrt (2 * c ^ 2 - s) +
        Real.sqrt (2 * c ^ 2 - s')), ← abs_mul, e, abs_sub_comm]
    nlinarith [abs_nonneg (Real.sqrt (2 * c ^ 2 - s) - Real.sqrt (2 * c ^ 2 - s'))]
  have htt : |tpar (decTiltU c S₀ S s) - tpar (decTiltU c S₀ S s')| ≤ |s - s'| / (2 * lo) / w := by
    rw [ht, ht, ← sub_div, abs_div, abs_of_pos hw]
    rw [show Real.sqrt (2 * c ^ 2 - s) - (lo + hi) / 2 -
      (Real.sqrt (2 * c ^ 2 - s') - (lo + hi) / 2) =
      Real.sqrt (2 * c ^ 2 - s) - Real.sqrt (2 * c ^ 2 - s') by ring]
    exact div_le_div_of_nonneg_right hsq hw.le
  have hu2 := dec_abs_sub_le_tpar hu hu'
  calc L * |decTiltU c S₀ S s - decTiltU c S₀ S s'|
      ≤ |L| * |decTiltU c S₀ S s - decTiltU c S₀ S s'| :=
        mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg _)
    _ ≤ |L| * (4 / 3 * (|s - s'| / (2 * lo) / w)) :=
        mul_le_mul_of_nonneg_left (hu2.trans (mul_le_mul_of_nonneg_left htt (by norm_num)))
          (abs_nonneg _)
    _ = |L| * (4 / 3) / w / (2 * lo) * |s - s'| := by field_simp

/-! ### The limit of the weighted block, Lipschitz in `s` -/

section Block

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F]
  (Φ : Lepton.Flavors F) (rep : F → F)
  {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **The projection of the limit of the weighted block is Lipschitz** on a compact interval of
the region. -/
theorem dec_lip_projS_fLim (he : P.e ≠ 0) (δ : F → ℝ) {S₀ S : ℝ}
    (hS₀ : -(4 * m₀ ^ 2) < S₀) (hS₀S : S₀ < S) :
    ∃ L : ℝ, ∀ s s' : ℝ, s ∈ Icc S₀ S → s' ∈ Icc S₀ S →
      ‖projS (fLim Φ rep P.e δ) s - projS (fLim Φ rep P.e δ) s'‖ ≤ L * |s - s'| := by
  set c : ℝ := 1 + |S|
  have hc : 0 < c := by positivity
  have hS : S < 2 * c ^ 2 := by
    have := le_abs_self S
    nlinarith [abs_nonneg S]
  have hseg := fun u (hu : |u| ≤ 1 / 2) => (dot_lineK_tilt_mem (c := c) hS hS₀S.le hu).1
  have h := DecSegLip.congr (H := fun k => fLim Φ rep P.e δ k 2 3)
    ((dec_segLip_fbVal P Φ rep (ctδ (ctOf P.e δ)) hm₀ hmass hS₀ hseg true true false 2 3).add
      (dec_segLip_fbVal P Φ rep (ctδ (ctOf P.e δ)) hm₀ hmass hS₀ hseg false false true 2 3))
      fun u hu => (fLim_eq_fbVal P Φ rep hm₀ hmass hrep hPV₁ hPV₂ he δ
        (by linarith [hseg u hu]) 2 3).symm
  obtain ⟨L, hL⟩ := dec_lip_tilt hS₀S hS h
  have hT : TCov (2 * m₀) (fLim Φ rep P.e δ) :=
    tcov_fLim Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he δ
  have hT' : -(2 * m₀) ^ 2 < S₀ := by nlinarith
  refine ⟨L / c ^ 2, fun s s' hs hs' => ?_⟩
  rw [projS_eq_tilt hT hc (hT'.trans_le hs.1) (hs.2.trans_lt hS),
    projS_eq_tilt hT hc (hT'.trans_le hs'.1) (hs'.2.trans_lt hS), ← sub_div, norm_div,
    ← neg_sub', norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
    div_le_iff₀ (by positivity)]
  have := hL s s' hs hs'
  have hc2 : 0 < c ^ 2 := by positivity
  calc ‖fLim Φ rep P.e δ (tiltVec c s) 2 3 - fLim Φ rep P.e δ (tiltVec c s') 2 3‖
      ≤ L * |s - s'| := this
    _ = L / c ^ 2 * |s - s'| * c ^ 2 := by field_simp

end Block

/-! ### `DecLipD` -/

/-- **`DecLipD`: the one-loop functional is Lipschitz near `s = 0`** at every configuration. -/
theorem dec_lipD (P : Params) : DecLipD P.e := by
  intro x hx
  by_cases he : P.e = 0
  · have e0 : decD₀ P.e 1 x = fun _ => 0 := funext fun s => by simp [decD₀, he]
    rw [e0]
    exact ⟨1, 0, one_pos, fun t t' _ _ => by simp⟩
  set m₀ : ℝ := min 1 x with hm₀d
  have hm₀ : 0 < m₀ := dec_min_one_pos hx
  have hmass : ∀ g, m₀ ≤ (decCfg 1 x).mass g := dec_cfg_mass_ge (min_le_left _ _) hm₀
    (dec_min_one_sq_le hx)
  have hpv := dec_cfg_pv (μ := 1) one_ne_zero hx.le
  have hδ : 0 < m₀ ^ 2 := by positivity
  obtain ⟨L, hL⟩ := dec_lip_projS_fLim P (decCfg 1 x) (fun _ => 0) hm₀ hmass (fun _ => rfl)
    hpv.1 hpv.2 he (fun _ => 1) (S₀ := -(m₀ ^ 2)) (S := m₀ ^ 2) (by linarith) (by linarith)
  refine ⟨m₀ ^ 2, L / P.e ^ 2, hδ, fun t t' ht ht' => ?_⟩
  have hmem : ∀ r : ℝ, |r| ≤ m₀ ^ 2 → r ∈ Icc (-(m₀ ^ 2)) (m₀ ^ 2) := fun r hr => abs_le.mp hr
  have h := hL t t' (hmem t ht) (hmem t' ht')
  have he2 : 0 < P.e ^ 2 := by positivity
  have e : decD₀ P.e 1 x t - decD₀ P.e 1 x t' = I * (projS (fLim (decCfg 1 x) (fun _ => 0) P.e
      fun _ => 1) t - projS (fLim (decCfg 1 x) (fun _ => 0) P.e fun _ => 1) t') /
      (P.e : ℂ) ^ 2 := by
    simp only [decD₀]
    ring
  rw [e, norm_div, norm_mul, Complex.norm_I, one_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, div_le_iff₀ he2]
  calc _ ≤ L * |t - t'| := h
    _ = L / P.e ^ 2 * |t - t'| * P.e ^ 2 := by field_simp

/-- **D3c₂: `DecLipD48`.** -/
theorem dec_lipD48 (P : Params) : DecLipD48 P.e := (DecLipD.weak (dec_lipD P)).2

end QED.GradedProof.RPi4

end
