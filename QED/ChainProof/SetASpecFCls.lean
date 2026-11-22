/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetASpecOne
public import QED.GradedProof.VP2LimF

/-!
# Set (a): the classes `F0`, `F1` have the spectral tensor form

Helper level for the set (a) headline (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`.
The fixed-`ε` copy of `QED.GradedProof.VP2.vpf_insTriple` and `vpf_fBubble` with the predicate
`SAJ1 M_lo` (`QED.ChainProof.SetASpec.SAJ1`) in place of `VPF`:

* `saPolyK1_tnS`, `saCov_of_tcovN`: the numerators `n₀, n₁, n₂` are polynomial along affine loop
  momenta, and a covariant numerator at `q = 0` is reflection covariant;
* `saj1_E0`, `saj1_E2`: the pieces with five and four lines (both momenta `q`, `k + q` present);
* `saj1_E4`: the piece with three lines at the same momentum, a constant tensor times a
  `k`-independent integral (`saForm_const`);
* **`saj1_insTriple`**: the three-flavour inserted bubble (ten pieces of `insTriple_eq`);
* **`saj1_fBubble`**: the block-summed inserted bubble;
* **`saForm_val0_repF0`**, **`saForm_val0_repF1`**: at `ε = P.ε > 0` the values of the classes
  `F0`, `F1` are `SAForm M_lo P.ε` for every `0 ≤ M_lo ≤ m₀`.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.ChainProof.SetASpec

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.GradedProof.VP2

/-! ### The numerators -/

theorem saPolyK1_tnS (sw : Bool) (j : Fin 3) (d₂ dm : ℝ) (bx bY : Bool) :
    SAPolyK1 4 (tnS sw j d₂ dm bx bY) := by
  intro lam δ μ ν
  have hx := saAffine_zk bx lam δ
  have hy := saAffine_zk bY lam δ
  match j with
  | 0 => cases sw <;> exact isLoopPoly_nT0 hx hy d₂ dm
  | 1 => cases sw <;> exact (isLoopPoly_nT1 hx hy d₂ dm).mono (by norm_num)
  | 2 =>
    show IsLoopPoly 1 4 fun _ => tnS sw 2 d₂ dm bx bY 0 0 μ ν
    exact IsLoopPoly.const _

/-- A covariant numerator at `q = 0` is reflection covariant. -/
theorem saCov_of_tcovN {N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} (h : TCovN N) :
    SACov fun k => N k 0 := fun a ha k => by
  funext μ ν
  show N (QED.Dirac.reflect a k) 0 μ ν = rAct a (N k 0) μ ν
  rw [h.reflect ha (QED.Dirac.reflect a k) 0 μ ν, QED.Dirac.reflect_reflect ha,
    Matrix.mulVec_zero]
  rfl

/-! ### The pieces -/

section Pieces

variable {Mlo : ℝ} (hMlo0 : 0 ≤ Mlo) (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool)
include hMlo0

theorem saj1_E0 (m0 m1 m2 m3 m4 : ℝ)
    (hm : Mlo ≤ m0 ∧ Mlo ≤ m1 ∧ Mlo ≤ m2 ∧ Mlo ≤ m3 ∧ Mlo ≤ m4) (c0 c1 c2 c3 c4 : Bool)
    (hb : ∃ l l', (![c0, c1, c2, c3, c4] : Fin 5 → Bool) l ≠ ![c0, c1, c2, c3, c4] l') :
    SAJ1 Mlo fun ε k q i j => (tnS sw 0 d₂ dm bx bY k q i j +
      (ε * I) * tnS sw 1 d₂ dm bx bY k q i j + (ε * I) ^ 2 * tnS sw 2 d₂ dm bx bY k q i j) *
      ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
        (propDenom m2 ε (zk k c2 q))⁻¹ * (propDenom m3 ε (zk k c3 q))⁻¹ *
        (propDenom m4 ε (zk k c4 q))⁻¹) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hm
  have P := fun (j : Fin 3)
      (hN : ∀ p i l, IsLoopPoly 2 4 fun ℓ => tnS sw j d₂ dm bx bY p (ℓ 0) i l) =>
    saj1_five hMlo0 ![m0, m1, m2, m3, m4] (fun l => by fin_cases l <;> assumption)
      ![c0, c1, c2, c3, c4] hb (tnS sw j d₂ dm bx bY) hN (tcovN_tnS sw j d₂ dm bx bY)
      (saPolyK1_tnS sw j d₂ dm bx bY)
  have p0 := P 0 (isLoopPoly_tnS0 sw d₂ dm bx bY)
  have p1 := (P 1 fun p i l => (isLoopPoly_tnS1 sw d₂ dm bx bY p i l).mono (by norm_num)).mul
    fun ε => (ε : ℂ) * I
  have p2 := (P 2 fun p i l => (isLoopPoly_tnS2 sw d₂ dm bx bY p i l).mono (by norm_num)).mul
    fun ε => ((ε : ℂ) * I) ^ 2
  refine ((p0.add p1).add p2).congr fun ε _ k q i j => ?_
  simp only [Fin.prod_univ_five, Matrix.cons_val]
  ring

theorem saj1_E2 (m0 m1 m2 m3 : ℝ) (hm : Mlo ≤ m0 ∧ Mlo ≤ m1 ∧ Mlo ≤ m2 ∧ Mlo ≤ m3)
    (c0 c1 c2 c3 : Bool)
    (hb : ∃ l l', (![c0, c1, c2, c3] : Fin 4 → Bool) l ≠ ![c0, c1, c2, c3] l') :
    SAJ1 Mlo fun ε k q i j => (tnS sw 1 d₂ dm bx bY k q i j +
      2 * (ε * I) * tnS sw 2 d₂ dm bx bY k q i j) *
      ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
        (propDenom m2 ε (zk k c2 q))⁻¹ * (propDenom m3 ε (zk k c3 q))⁻¹) := by
  obtain ⟨h0, h1, h2, h3⟩ := hm
  have P := fun (j : Fin 3)
      (hN : ∀ p i l, IsLoopPoly 2 2 fun ℓ => tnS sw j d₂ dm bx bY p (ℓ 0) i l)
      (hK : SAPolyK1 2 (tnS sw j d₂ dm bx bY)) =>
    saj1_four hMlo0 ![m0, m1, m2, m3] (fun l => by fin_cases l <;> assumption)
      ![c0, c1, c2, c3] hb (tnS sw j d₂ dm bx bY) hN (tcovN_tnS sw j d₂ dm bx bY) hK
  have p1 := P 1 (isLoopPoly_tnS1 sw d₂ dm bx bY) fun lam δ μ ν => by
    have hx := saAffine_zk bx lam δ
    have hy := saAffine_zk bY lam δ
    cases sw <;> exact isLoopPoly_nT1 hx hy d₂ dm
  have p2 := (P 2 (fun p i l => (isLoopPoly_tnS2 sw d₂ dm bx bY p i l).mono (by norm_num))
    fun _ _ μ ν => show IsLoopPoly 1 2 fun _ => tnS sw 2 d₂ dm bx bY 0 0 μ ν from
      IsLoopPoly.const _).mul fun ε => 2 * ((ε : ℂ) * I)
  refine (p1.add p2).congr fun ε _ k q i j => ?_
  simp only [Fin.prod_univ_four, Matrix.cons_val]
  ring

omit hMlo0 in
/-- **Three lines at the same momentum**: a constant tensor times a `k`-independent integral. -/
theorem saj1_E4 (m0 m1 m2 : ℝ) (c : Bool) :
    SAJ1 Mlo fun ε k q i j => tnS sw 2 d₂ dm bx bY k q i j *
      ((propDenom m0 ε (zk k c q))⁻¹ * (propDenom m1 ε (zk k c q))⁻¹ *
        (propDenom m2 ε (zk k c q))⁻¹) := by
  intro ε hε
  refine ⟨fun k i j => ef3 k hε _ (isLoopPoly_tnS2 sw d₂ dm bx bY k i j) m0 m1 m2 c c c, ?_⟩
  set G : ℂ := QED.OneLoop.energyFirstIntegral fun q =>
    (propDenom m0 ε q)⁻¹ * (propDenom m1 ε q)⁻¹ * (propDenom m2 ε q)⁻¹ with hG
  have hS := saForm_const (C := fun k => tnS sw 2 d₂ dm bx bY k 0)
    (saCov_of_tcovN (tcovN_tnS sw 2 d₂ dm bx bY))
    (fun μ ν => isLoopPoly_tnS_k sw 2 d₂ dm bx bY 0 μ ν) G hε Mlo
  refine hS.congr fun k i j => ?_
  have e : (QED.OneLoop.energyFirstIntegral fun q => tnS sw 2 d₂ dm bx bY k q i j *
      ((propDenom m0 ε (zk k c q))⁻¹ * (propDenom m1 ε (zk k c q))⁻¹ *
        (propDenom m2 ε (zk k c q))⁻¹)) = tnS sw 2 d₂ dm bx bY k 0 i j *
      QED.OneLoop.energyFirstIntegral fun q => (propDenom m0 ε (zk k c q))⁻¹ *
        (propDenom m1 ε (zk k c q))⁻¹ * (propDenom m2 ε (zk k c q))⁻¹ := by
    rw [← QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul]
    congr 1
  rw [e, hG]
  congr 1
  cases c
  · rfl
  · simp only [zk, ite_true]
    have := QED.OneLoop.energyFirstIntegral_add_right_eq_self (fun q =>
      (propDenom m0 ε q)⁻¹ * (propDenom m1 ε q)⁻¹ * (propDenom m2 ε q)⁻¹) k
    simp only [add_comm _ k] at this
    exact this.symm

end Pieces

/-- **The three-flavour inserted bubble** is `SAJ1`. -/
theorem saj1_insTriple {Mlo : ℝ} (hMlo0 : 0 ≤ Mlo) (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool)
    (hb : bx ≠ bY) (M X Y : ℝ) (hM : Mlo ≤ M) (hX : Mlo ≤ X) (hY : Mlo ≤ Y)
    (hXY : X ^ 2 - Y ^ 2 ≠ 0) :
    SAJ1 Mlo fun ε k q i j =>
      insG (gAF sw i j) (gBF sw i j) d₂ dm M ε (zk k bx q) (zk k bY q) +
        (triA M X Y : ℂ) * insG (gAF sw i j) (gBF sw i j) d₂ dm X ε (zk k bx q) (zk k bY q) +
        (triB M X Y : ℂ) * insG (gAF sw i j) (gBF sw i j) d₂ dm Y ε (zk k bx q) (zk k bY q) := by
  have E0 := saj1_E0 hMlo0 sw d₂ dm bx bY
  have E2 := saj1_E2 hMlo0 sw d₂ dm bx bY
  have b1 : ∃ l l', (![bx, bY, bY, bY, bY] : Fin 5 → Bool) l ≠ ![bx, bY, bY, bY, bY] l' :=
    ⟨0, 1, by simpa using hb⟩
  have b2 : ∃ l l', (![bx, bx, bY, bY, bY] : Fin 5 → Bool) l ≠ ![bx, bx, bY, bY, bY] l' :=
    ⟨0, 2, by simpa using hb⟩
  have b3 : ∃ l l', (![bx, bx, bx, bY, bY] : Fin 5 → Bool) l ≠ ![bx, bx, bx, bY, bY] l' :=
    ⟨0, 3, by simpa using hb⟩
  have b4 : ∃ l l', (![bx, bY, bY, bY] : Fin 4 → Bool) l ≠ ![bx, bY, bY, bY] l' :=
    ⟨0, 1, by simpa using hb⟩
  have b5 : ∃ l l', (![bx, bx, bY, bY] : Fin 4 → Bool) l ≠ ![bx, bx, bY, bY] l' :=
    ⟨0, 2, by simpa using hb⟩
  have b6 : ∃ l l', (![bx, bx, bx, bY] : Fin 4 → Bool) l ≠ ![bx, bx, bx, bY] l' :=
    ⟨0, 3, by simpa using hb⟩
  have s := ((((((((((E0 M M X Y M ⟨hM, hM, hX, hY, hM⟩ bx bY bY bY bY b1).add
    (E0 M M X Y X ⟨hM, hM, hX, hY, hX⟩ bx bY bY bY bY b1)).add
    (E0 M M X Y Y ⟨hM, hM, hX, hY, hY⟩ bx bY bY bY bY b1)).add
    (E0 M X X Y X ⟨hM, hX, hX, hY, hX⟩ bx bx bY bY bY b2)).add
    (E0 M X X Y Y ⟨hM, hX, hX, hY, hY⟩ bx bx bY bY bY b2)).add
    (E0 M X Y Y Y ⟨hM, hX, hY, hY, hY⟩ bx bx bx bY bY b3)).add
    (E2 M M X Y ⟨hM, hM, hX, hY⟩ bx bY bY bY b4)).add
    (E2 M X X Y ⟨hM, hX, hX, hY⟩ bx bx bY bY b5)).add
    (E2 M X Y Y ⟨hM, hX, hY, hY⟩ bx bx bx bY b6)).add
    (saj1_E4 (Mlo := Mlo) sw d₂ dm bx bY M X Y bx)).const_mul
    (((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2))
  refine s.congr fun ε hε k q i j => ?_
  have hA : IsOddG (gAF sw i j) := isOddG_gamma _
  have hB : IsOddG (gBF sw i j) := isOddG_gamma _
  rw [insTriple_eq hA hB d₂ dm M X Y hXY hε.ne' (zk k bx q) (zk k bY q),
    nT0_gAB, nT1_gAB, nT2_gAB sw d₂ dm bx bY k q]

/-! ### The classes -/

section Classes

variable (P : QED.WickModel.Params) {F : Type} [Fintype F] [DecidableEq F]
  (Φ : Lepton.Flavors F) (D : QED.Graded.Counterterms F) (rep : F → F)

/-- **The block-summed inserted bubble** is `SAJ1`. -/
theorem saj1_fBubble {m₀ Mlo : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hlo0 : 0 ≤ Mlo) (hlo : Mlo ≤ m₀) (sw bx bY : Bool) (hb : bx ≠ bY) :
    SAJ1 Mlo fun ε k q μ ν => fBubble P Φ D rep sw bx bY ε k q μ ν := by
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
  refine (SAJ1.sum Finset.univ (fun f _ => (saj1_insTriple hlo0 sw (P.e ^ 2 * D.d₂ (rep f) 0)
    (P.e ^ 2 * D.dm (rep f) 0) bx bY hb (Φ.mass f) X (X + 1) (hlo.trans (hmass f))
    (by linarith [hlt f, hmass f]) (by linarith [hlt f, hmass f]) hXY).const_mul
      ((Φ.coeff f : ℂ) * kF P.e))).congr fun ε _ k q μ ν => ?_
  simp only [fBubble]
  rw [sum_block_eq_sum_triple Φ rep hrep hPV₁ hPV₂ X (X + 1) (fun r M => kF P.e *
    insG (gAF sw μ ν) (gBF sw μ ν) (P.e ^ 2 * D.d₂ r 0) (P.e ^ 2 * D.dm r 0) M ε (zk k bx q)
      (zk k bY q))]
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

variable {m₀ Mlo : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  (hD : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0)
  (hlo0 : 0 ≤ Mlo) (hlo : Mlo ≤ m₀) (hε : 0 < P.ε)
include hm₀ hmass hrep hPV₁ hPV₂ hD hlo0 hlo hε

/-- **The class `F0` at `ε = P.ε > 0`** has the spectral tensor form. -/
theorem saForm_val0_repF0 : SAForm Mlo P.ε fun k μ ν => val0 P Φ D k μ ν repF0 :=
  ((saj1_fBubble P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hlo0 hlo true true false (by decide))
    P.ε hε).2.congr fun k μ ν => (val0_repF0 P Φ D rep hD k μ ν).symm

/-- **The class `F1` at `ε = P.ε > 0`** has the spectral tensor form. -/
theorem saForm_val0_repF1 : SAForm Mlo P.ε fun k μ ν => val0 P Φ D k μ ν repF1 :=
  ((saj1_fBubble P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hlo0 hlo false false true (by decide))
    P.ε hε).2.congr fun k μ ν => (val0_repF1 P Φ D rep hD k μ ν).symm

end Classes

end QED.ChainProof.SetASpec

end
