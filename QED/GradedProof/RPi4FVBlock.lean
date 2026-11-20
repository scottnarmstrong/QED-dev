/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FV
public import QED.GradedProof.RPi4PairF

/-!
# (R-Π₄) step L6a′: the explicit value of the mass-insertion block

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6a′. The replays of
`QED.GradedProof.VP2.vpf_insTriple`, `QED.GradedProof.VP2.vpf_fBubble` and
`QED.GradedProof.RPi4.vpf_dBlock` with the values of `QED.GradedProof.RPi4.vpfv_five`, ….

* `eVal0`, `eVal2`, `eVal4`: the values of the pieces with numerators `E₀`, `E₂`, `E₄` of
  `QED.GradedProof.VP2.insTriple_eq` (the `iε` parts have the value `0`);
* `insVal`: the value of the three-flavour inserted bubble, `(X² - M²)(Y² - M²)` times ten piece
  values (`vpfv_insTriple`);
* `fbVal`: the value of the block-summed inserted bubble (`vpfv_fBubble`);
* **`fLim_eq_fbVal`**: the named limit `fLim Φ rep e δ` of the weighted mass-derivative block is
  `fbVal` of `F0` plus `fbVal` of `F1` at the counterterms `ctδ (ctOf e δ)`, on the region. Every
  term is an explicit eight-line parametric integral divided by `auxLimit m₀`.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2
open QED.TwoLoop.Bridge (propDenom IsLoopPoly)

/-! ### The pieces of the inserted bubble -/

/-- The value of the five-line piece with numerator `E₀`. -/
noncomputable def eVal0 (m₀ : ℝ) (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool) (m0 m1 m2 m3 m4 : ℝ)
    (c0 c1 c2 c3 c4 : Bool) : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ :=
  fVal5 m₀ ![m0, m1, m2, m3, m4] ![c0, c1, c2, c3, c4] (tnS sw 0 d₂ dm bx bY)

/-- The value of the four-line piece with numerator `E₂`. -/
noncomputable def eVal2 (m₀ : ℝ) (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool) (m0 m1 m2 m3 : ℝ)
    (c0 c1 c2 c3 : Bool) : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ :=
  fVal5 m₀ ![m0, m0, m1, m2, m3] ![c0, c0, c1, c2, c3] (padN (tnS sw 1 d₂ dm bx bY) m0 c0)

/-- The value of the three-line piece with numerator `E₄`. -/
noncomputable def eVal4 (m₀ : ℝ) (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool) (m0 m1 m2 : ℝ)
    (c0 c1 c2 : Bool) : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ :=
  fVal5 m₀ ![m0, m0, m0, m1, m2] ![c0, c0, c0, c1, c2]
    (padN (padN (tnS sw 2 d₂ dm bx bY) m0 c0) m0 c0)

/-- **The value of the three-flavour inserted bubble.** -/
noncomputable def insVal (m₀ : ℝ) (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool) (M X Y : ℝ)
    (k : Fin 4 → ℝ) (i j : Fin 4) : ℂ :=
  (((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2)) *
    (eVal0 m₀ sw d₂ dm bx bY M M X Y M bx bY bY bY bY k i j +
      eVal0 m₀ sw d₂ dm bx bY M M X Y X bx bY bY bY bY k i j +
      eVal0 m₀ sw d₂ dm bx bY M M X Y Y bx bY bY bY bY k i j +
      eVal0 m₀ sw d₂ dm bx bY M X X Y X bx bx bY bY bY k i j +
      eVal0 m₀ sw d₂ dm bx bY M X X Y Y bx bx bY bY bY k i j +
      eVal0 m₀ sw d₂ dm bx bY M X Y Y Y bx bx bx bY bY k i j +
      eVal2 m₀ sw d₂ dm bx bY M M X Y bx bY bY bY k i j +
      eVal2 m₀ sw d₂ dm bx bY M X X Y bx bx bY bY k i j +
      eVal2 m₀ sw d₂ dm bx bY M X Y Y bx bx bx bY k i j +
      eVal4 m₀ sw d₂ dm bx bY M X Y bx bx bx k i j)

section Pieces

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool)
include hm₀

theorem vpfv_E0 (m0 m1 m2 m3 m4 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3 ∧ m₀ ≤ m4)
    (c0 c1 c2 c3 c4 : Bool) :
    VPFV (m₀ + m₀) (fun ε k q i j => (tnS sw 0 d₂ dm bx bY k q i j +
      (ε * I) * tnS sw 1 d₂ dm bx bY k q i j + (ε * I) ^ 2 * tnS sw 2 d₂ dm bx bY k q i j) *
      ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
        (propDenom m2 ε (zk k c2 q))⁻¹ * (propDenom m3 ε (zk k c3 q))⁻¹ *
        (propDenom m4 ε (zk k c4 q))⁻¹))
      (eVal0 m₀ sw d₂ dm bx bY m0 m1 m2 m3 m4 c0 c1 c2 c3 c4) := by
  have P := fun (j : Fin 3)
      (hN : ∀ p i l, IsLoopPoly 2 4 fun ℓ => tnS sw j d₂ dm bx bY p (ℓ 0) i l) =>
    vpfv_five hm₀ m0 m1 m2 m3 m4 hm c0 c1 c2 c3 c4 (tnS sw j d₂ dm bx bY) hN
      (tcovN_tnS sw j d₂ dm bx bY) (isLoopPoly_tnS_k sw j d₂ dm bx bY)
  have p0 := P 0 (isLoopPoly_tnS0 sw d₂ dm bx bY)
  have p1 := (P 1 fun p i l => (isLoopPoly_tnS1 sw d₂ dm bx bY p i l).mono (by norm_num)).mul
    tendsto_epsI
  have p2 := (P 2 fun p i l => (isLoopPoly_tnS2 sw d₂ dm bx bY p i l).mono (by norm_num)).mul
    (tendsto_epsI.pow 2)
  refine (((p0.add p1).add p2).congr fun ε _ k q i j => ?_).congr_val fun k _ i j => ?_
  · ring
  · simp only [eVal0]
    ring

theorem vpfv_E2 (m0 m1 m2 m3 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3)
    (c0 c1 c2 c3 : Bool) :
    VPFV (m₀ + m₀) (fun ε k q i j => (tnS sw 1 d₂ dm bx bY k q i j +
      2 * (ε * I) * tnS sw 2 d₂ dm bx bY k q i j) *
      ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
        (propDenom m2 ε (zk k c2 q))⁻¹ * (propDenom m3 ε (zk k c3 q))⁻¹))
      (eVal2 m₀ sw d₂ dm bx bY m0 m1 m2 m3 c0 c1 c2 c3) := by
  have p1 := vpfv_four hm₀ m0 m1 m2 m3 hm c0 c1 c2 c3 (tnS sw 1 d₂ dm bx bY)
    (isLoopPoly_tnS1 sw d₂ dm bx bY) (tcovN_tnS sw 1 d₂ dm bx bY)
    (isLoopPoly_tnS_k sw 1 d₂ dm bx bY)
  have p2 := (vpfv_four hm₀ m0 m1 m2 m3 hm c0 c1 c2 c3 (tnS sw 2 d₂ dm bx bY)
    (fun p i l => (isLoopPoly_tnS2 sw d₂ dm bx bY p i l).mono (by norm_num))
    (tcovN_tnS sw 2 d₂ dm bx bY) (isLoopPoly_tnS_k sw 2 d₂ dm bx bY)).mul
    (tendsto_epsI.const_mul 2)
  refine ((p1.add p2).congr fun ε _ k q i j => ?_).congr_val fun k _ i j => ?_
  · ring
  · simp only [eVal2]
    ring

theorem vpfv_E4 (m0 m1 m2 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2) (c0 c1 c2 : Bool) :
    VPFV (m₀ + m₀) (fun ε k q i j => tnS sw 2 d₂ dm bx bY k q i j *
      ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
        (propDenom m2 ε (zk k c2 q))⁻¹))
      (eVal4 m₀ sw d₂ dm bx bY m0 m1 m2 c0 c1 c2) :=
  vpfv_three hm₀ m0 m1 m2 hm c0 c1 c2 (tnS sw 2 d₂ dm bx bY) (isLoopPoly_tnS2 sw d₂ dm bx bY)
    (tcovN_tnS sw 2 d₂ dm bx bY) (isLoopPoly_tnS_k sw 2 d₂ dm bx bY)

/-- **The three-flavour inserted bubble with its value.** -/
theorem vpfv_insTriple (M X Y : ℝ) (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y)
    (hXY : X ^ 2 - Y ^ 2 ≠ 0) :
    VPFV (m₀ + m₀) (fun ε k q i j =>
      insG (gAF sw i j) (gBF sw i j) d₂ dm M ε (zk k bx q) (zk k bY q) +
        (triA M X Y : ℂ) * insG (gAF sw i j) (gBF sw i j) d₂ dm X ε (zk k bx q) (zk k bY q) +
        (triB M X Y : ℂ) * insG (gAF sw i j) (gBF sw i j) d₂ dm Y ε (zk k bx q) (zk k bY q))
      (insVal m₀ sw d₂ dm bx bY M X Y) := by
  have E0 := vpfv_E0 hm₀ sw d₂ dm bx bY
  have E2 := vpfv_E2 hm₀ sw d₂ dm bx bY
  have s := ((((((((((E0 M M X Y M ⟨hM, hM, hX, hY, hM⟩ bx bY bY bY bY).add
    (E0 M M X Y X ⟨hM, hM, hX, hY, hX⟩ bx bY bY bY bY)).add
    (E0 M M X Y Y ⟨hM, hM, hX, hY, hY⟩ bx bY bY bY bY)).add
    (E0 M X X Y X ⟨hM, hX, hX, hY, hX⟩ bx bx bY bY bY)).add
    (E0 M X X Y Y ⟨hM, hX, hX, hY, hY⟩ bx bx bY bY bY)).add
    (E0 M X Y Y Y ⟨hM, hX, hY, hY, hY⟩ bx bx bx bY bY)).add
    (E2 M M X Y ⟨hM, hM, hX, hY⟩ bx bY bY bY)).add
    (E2 M X X Y ⟨hM, hX, hX, hY⟩ bx bx bY bY)).add
    (E2 M X Y Y ⟨hM, hX, hY, hY⟩ bx bx bx bY)).add
    (vpfv_E4 hm₀ sw d₂ dm bx bY M X Y ⟨hM, hX, hY⟩ bx bx bx)).const_mul
    (((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2))
  refine (s.congr fun ε hε k q i j => ?_).congr_val fun k _ i j => rfl
  have hA : IsOddG (gAF sw i j) := isOddG_gamma _
  have hB : IsOddG (gBF sw i j) := isOddG_gamma _
  rw [insTriple_eq hA hB d₂ dm M X Y hXY hε.ne' (zk k bx q) (zk k bY q),
    nT0_gAB, nT1_gAB, nT2_gAB sw d₂ dm bx bY k q]

end Pieces

/-! ### The block-summed bubble and the mass-derivative block -/

section Block

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F) (rep : F → F)

/-- **The value of the block-summed inserted bubble.** -/
noncomputable def fbVal (m₀ : ℝ) (sw bx bY : Bool) (k : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  ∑ f, ((Φ.coeff f : ℂ) * kF P.e) * insVal m₀ sw (P.e ^ 2 * D.d₂ (rep f) 0)
    (P.e ^ 2 * D.dm (rep f) 0) bx bY (Φ.mass f) (auxX Φ) (auxX Φ + 1) k μ ν

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **The block-summed inserted bubble with its value.** -/
theorem vpfv_fBubble (sw bx bY : Bool) :
    VPFV (m₀ + m₀) (fun ε k q μ ν => fBubble P Φ D rep sw bx bY ε k q μ ν)
      (fbVal P Φ D rep m₀ sw bx bY) := by
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
  refine (VPFV.sum Finset.univ (fun f _ => (vpfv_insTriple hm₀ sw (P.e ^ 2 * D.d₂ (rep f) 0)
    (P.e ^ 2 * D.dm (rep f) 0) bx bY (Φ.mass f) X (X + 1) (hmass f)
    (by linarith [hlt f, hmass f]) (by linarith [hlt f, hmass f]) hXY).const_mul
      ((Φ.coeff f : ℂ) * kF P.e))).congr fun ε _ k q μ ν => ?_
  simp only [fBubble]
  rw [sum_block_eq_sum_triple Φ rep hrep hPV₁ hPV₂ X (X + 1) (fun r M => kF P.e *
    insG (gAF sw μ ν) (gBF sw μ ν) (P.e ^ 2 * D.d₂ r 0) (P.e ^ 2 * D.dm r 0) M ε (zk k bx q)
      (zk k bY q))]
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

/-- **The mass-derivative block with its value**: the values of `F0` and `F1` at the pure mass
insertion `ctδ D`; the `iε` remainder has the value `0`. -/
theorem vpfv_dBlock :
    VPFV (m₀ + m₀) (fun ε k q μ ν => dBlock P Φ D rep ε k q μ ν)
      fun k μ ν => fbVal P Φ (ctδ D) rep m₀ true true false k μ ν +
        fbVal P Φ (ctδ D) rep m₀ false false true k μ ν := by
  have h := ((vpfv_fBubble P Φ (ctδ D) rep hm₀ hmass hrep hPV₁ hPV₂ true true false).add
    (vpfv_fBubble P Φ (ctδ D) rep hm₀ hmass hrep hPV₁ hPV₂ false false true)).add
    (VPFV.of_mul_zero (vpf_remMBlock hm₀ P Φ D rep hmass) tendsto_epsI)
  refine (h.congr fun ε hε k q μ ν => ?_).congr_val fun k _ μ ν => add_zero _
  rw [dBlock_eq P Φ D rep hε.ne']

/-- **(L6a′) The explicit value of the limit of the weighted mass-derivative block**: on the
region, `fLim Φ rep e δ` is the value of the inserted bubbles of `F0` and `F1` at the counterterms
`ctδ (ctOf e δ)` (pure mass insertion `δ / e²`). -/
theorem fLim_eq_fbVal (he : P.e ≠ 0) (δ : F → ℝ) {k : Fin 4 → ℝ}
    (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    fLim Φ rep P.e δ k μ ν = fbVal P Φ (ctδ (ctOf P.e δ)) rep m₀ true true false k μ ν +
      fbVal P Φ (ctδ (ctOf P.e δ)) rep m₀ false false true k μ ν := by
  have h := (vpfv_dBlock P Φ (ctOf P.e δ) rep hm₀ hmass hrep hPV₁ hPV₂).2 k (by nlinarith) μ ν
  rw [dBlock_ctOf Φ rep P he δ] at h
  exact limT_eq h

end Block

end QED.GradedProof.RPi4

end
