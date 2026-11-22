/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetASpecUOne
public import QED.ChainProof.SetASpecFCls

/-!
# Set (a): the classes `F0`, `F1` have the uniform spectral tensor form

Helper level for the set (a) headline (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`.
The `ε`-uniform copy of `QED.ChainProof.SetASpec.saj1_E0`, …, `saForm_val0_repF1`. The
coefficients `iε`, `(iε)²`, `2iε` of `E₀ = n₀ + iε n₁ + (iε)² n₂` are uniform coefficients.
The piece with three lines at one momentum, whose integral does not depend on `k`, is not treated
as a constant: it is multiplied by `1 = (D(0, y) - iε) / D(ε, y)` at the other momentum `y`, so
that it is a four-line piece with both momenta present (`saUj1_E4`).

* `saUj1_E0`, `saUj1_E2`, `saUj1_E4`, **`saUj1_insTriple`**, **`saUj1_fBubble`**;
* **`saUForm_val0_repF0`**, **`saUForm_val0_repF1`**: for `ε ∈ (0, 1]` the values of the classes
  `F0`, `F1` at `{P with ε := ε}` are `SAUForm M_lo`.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.ChainProof.SetASpec

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.GradedProof.VP2

/-! ### The pieces -/

section Pieces

variable {Mlo : ℝ} (hMlo0 : 0 ≤ Mlo) (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool)
include hMlo0

theorem saUj1_E0 (m0 m1 m2 m3 m4 : ℝ)
    (hm : Mlo ≤ m0 ∧ Mlo ≤ m1 ∧ Mlo ≤ m2 ∧ Mlo ≤ m3 ∧ Mlo ≤ m4) (c0 c1 c2 c3 c4 : Bool)
    (hb : ∃ l l', (![c0, c1, c2, c3, c4] : Fin 5 → Bool) l ≠ ![c0, c1, c2, c3, c4] l') :
    SAUJ1 Mlo fun ε k q i j => (tnS sw 0 d₂ dm bx bY k q i j +
      (ε * I) * tnS sw 1 d₂ dm bx bY k q i j + (ε * I) ^ 2 * tnS sw 2 d₂ dm bx bY k q i j) *
      ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
        (propDenom m2 ε (zk k c2 q))⁻¹ * (propDenom m3 ε (zk k c3 q))⁻¹ *
        (propDenom m4 ε (zk k c4 q))⁻¹) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hm
  have P := fun (j : Fin 3)
      (hN : ∀ p i l, IsLoopPoly 2 4 fun ℓ => tnS sw j d₂ dm bx bY p (ℓ 0) i l) =>
    saUj1_five hMlo0 ![m0, m1, m2, m3, m4] (fun l => by fin_cases l <;> assumption)
      ![c0, c1, c2, c3, c4] hb (tnS sw j d₂ dm bx bY) hN (tcovN_tnS sw j d₂ dm bx bY)
      (saPolyK1_tnS sw j d₂ dm bx bY)
  have p0 := P 0 (isLoopPoly_tnS0 sw d₂ dm bx bY)
  have p1 := (P 1 fun p i l => (isLoopPoly_tnS1 sw d₂ dm bx bY p i l).mono (by norm_num)).mul
    (SAUCoef.of_continuous (c := fun ε : ℝ => (ε : ℂ) * I) (by fun_prop))
  have p2 := (P 2 fun p i l => (isLoopPoly_tnS2 sw d₂ dm bx bY p i l).mono (by norm_num)).mul
    (SAUCoef.of_continuous (c := fun ε : ℝ => ((ε : ℂ) * I) ^ 2) (by fun_prop))
  refine ((p0.add p1).add p2).congr fun ε _ k q i j => ?_
  simp only [Fin.prod_univ_five, Matrix.cons_val]
  ring

theorem saUj1_E2 (m0 m1 m2 m3 : ℝ) (hm : Mlo ≤ m0 ∧ Mlo ≤ m1 ∧ Mlo ≤ m2 ∧ Mlo ≤ m3)
    (c0 c1 c2 c3 : Bool)
    (hb : ∃ l l', (![c0, c1, c2, c3] : Fin 4 → Bool) l ≠ ![c0, c1, c2, c3] l') :
    SAUJ1 Mlo fun ε k q i j => (tnS sw 1 d₂ dm bx bY k q i j +
      2 * (ε * I) * tnS sw 2 d₂ dm bx bY k q i j) *
      ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
        (propDenom m2 ε (zk k c2 q))⁻¹ * (propDenom m3 ε (zk k c3 q))⁻¹) := by
  obtain ⟨h0, h1, h2, h3⟩ := hm
  have P := fun (j : Fin 3)
      (hN : ∀ p i l, IsLoopPoly 2 2 fun ℓ => tnS sw j d₂ dm bx bY p (ℓ 0) i l)
      (hK : SAPolyK1 2 (tnS sw j d₂ dm bx bY)) =>
    saUj1_four hMlo0 ![m0, m1, m2, m3] (fun l => by fin_cases l <;> assumption)
      ![c0, c1, c2, c3] hb (tnS sw j d₂ dm bx bY) hN (tcovN_tnS sw j d₂ dm bx bY) hK
  have p1 := P 1 (isLoopPoly_tnS1 sw d₂ dm bx bY) fun lam δ μ ν => by
    have hx := saAffine_zk bx lam δ
    have hy := saAffine_zk bY lam δ
    cases sw <;> exact isLoopPoly_nT1 hx hy d₂ dm
  have p2 := (P 2 (fun p i l => (isLoopPoly_tnS2 sw d₂ dm bx bY p i l).mono (by norm_num))
    fun _ _ μ ν => show IsLoopPoly 1 2 fun _ => tnS sw 2 d₂ dm bx bY 0 0 μ ν from
      IsLoopPoly.const _).mul
    (SAUCoef.of_continuous (c := fun ε : ℝ => 2 * ((ε : ℂ) * I)) (by fun_prop))
  refine (p1.add p2).congr fun ε _ k q i j => ?_
  simp only [Fin.prod_univ_four, Matrix.cons_val]
  ring

/-- **Three lines at the same momentum** `x`, times `1 = (D_{m₀}(0, y) - iε) / D_{m₀}(ε, y)` at
the other momentum `y`: four lines with both momenta present. -/
theorem saUj1_E4 (m0 m1 m2 : ℝ) (hm : Mlo ≤ m0 ∧ Mlo ≤ m1 ∧ Mlo ≤ m2) (hb : bx ≠ bY) :
    SAUJ1 Mlo fun ε k q i j => tnS sw 2 d₂ dm bx bY k q i j *
      ((propDenom m0 ε (zk k bx q))⁻¹ * (propDenom m1 ε (zk k bx q))⁻¹ *
        (propDenom m2 ε (zk k bx q))⁻¹) := by
  obtain ⟨h0, h1, h2⟩ := hm
  have hK0 : SAPolyK1 0 (tnS sw 2 d₂ dm bx bY) := fun _ _ μ ν =>
    show IsLoopPoly 1 0 fun _ => tnS sw 2 d₂ dm bx bY 0 0 μ ν from IsLoopPoly.const _
  have hb4 : ∃ l l', (![bx, bx, bx, bY] : Fin 4 → Bool) l ≠ ![bx, bx, bx, bY] l' :=
    ⟨0, 3, by simpa using hb⟩
  have hm4 : ∀ l, Mlo ≤ (![m0, m1, m2, m0] : Fin 4 → ℝ) l := fun l => by
    fin_cases l <;> assumption
  have A := saUj1_four hMlo0 ![m0, m1, m2, m0] hm4 ![bx, bx, bx, bY] hb4
    (fun k q i j => tnS sw 2 d₂ dm bx bY k q i j * propDenom m0 0 (zk k bY q))
    (fun p i l => ((isLoopPoly_tnS2 sw d₂ dm bx bY p i l).mul
      ((isLoopAffine_zk p bY).isLoopPoly_propDenom m0 0)).mono (by norm_num))
    ((tcovN_tnS sw 2 d₂ dm bx bY).mul_propDenom _ _ _)
    ((hK0.mul_propDenom m0 0 bY).mono (by norm_num))
  have B := (saUj1_four hMlo0 ![m0, m1, m2, m0] hm4 ![bx, bx, bx, bY] hb4
    (tnS sw 2 d₂ dm bx bY)
    (fun p i l => (isLoopPoly_tnS2 sw d₂ dm bx bY p i l).mono (by norm_num))
    (tcovN_tnS sw 2 d₂ dm bx bY) (hK0.mono (by norm_num))).mul
    (SAUCoef.of_continuous (c := fun ε : ℝ => -(ε : ℂ) * I) (by fun_prop))
  refine (A.add B).congr fun ε hε k q i j => ?_
  have hd := propDenom_ne_zero (M := m0) hε.ne' (zk k bY q)
  have hz : propDenom m0 0 (zk k bY q) = propDenom m0 ε (zk k bY q) + ε * I := by
    simp only [propDenom]; push_cast; ring
  simp only [Fin.prod_univ_four, Matrix.cons_val, hz]
  field_simp
  ring

end Pieces

/-- **The three-flavour inserted bubble** is `SAUJ1`. -/
theorem saUj1_insTriple {Mlo : ℝ} (hMlo0 : 0 ≤ Mlo) (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool)
    (hb : bx ≠ bY) (M X Y : ℝ) (hM : Mlo ≤ M) (hX : Mlo ≤ X) (hY : Mlo ≤ Y)
    (hXY : X ^ 2 - Y ^ 2 ≠ 0) :
    SAUJ1 Mlo fun ε k q i j =>
      insG (gAF sw i j) (gBF sw i j) d₂ dm M ε (zk k bx q) (zk k bY q) +
        (triA M X Y : ℂ) * insG (gAF sw i j) (gBF sw i j) d₂ dm X ε (zk k bx q) (zk k bY q) +
        (triB M X Y : ℂ) * insG (gAF sw i j) (gBF sw i j) d₂ dm Y ε (zk k bx q) (zk k bY q) := by
  have E0 := saUj1_E0 hMlo0 sw d₂ dm bx bY
  have E2 := saUj1_E2 hMlo0 sw d₂ dm bx bY
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
    (saUj1_E4 hMlo0 sw d₂ dm bx bY M X Y ⟨hM, hX, hY⟩ hb)).const_mul
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

/-- **The block-summed inserted bubble** is `SAUJ1`. -/
theorem saUj1_fBubble {m₀ Mlo : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hlo0 : 0 ≤ Mlo) (hlo : Mlo ≤ m₀) (sw bx bY : Bool) (hb : bx ≠ bY) :
    SAUJ1 Mlo fun ε k q μ ν => fBubble P Φ D rep sw bx bY ε k q μ ν := by
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
  refine (SAUJ1.sum Finset.univ (fun f _ => (saUj1_insTriple hlo0 sw (P.e ^ 2 * D.d₂ (rep f) 0)
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
  (hlo0 : 0 ≤ Mlo) (hlo : Mlo ≤ m₀)
include hm₀ hmass hrep hPV₁ hPV₂ hD hlo0 hlo

/-- **The class `F0`** has the uniform spectral tensor form. -/
theorem saUForm_val0_repF0 :
    SAUForm Mlo fun ε k μ ν => val0 { P with ε := ε } Φ D k μ ν repF0 :=
  ((saUj1_fBubble P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hlo0 hlo true true false (by decide))
    ).2.congr fun ε _ _ k μ ν => (val0_repF0 { P with ε := ε } Φ D rep hD k μ ν).symm

/-- **The class `F1`** has the uniform spectral tensor form. -/
theorem saUForm_val0_repF1 :
    SAUForm Mlo fun ε k μ ν => val0 { P with ε := ε } Φ D k μ ν repF1 :=
  ((saUj1_fBubble P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hlo0 hlo false false true (by decide))
    ).2.congr fun ε _ _ k μ ν => (val0_repF1 { P with ε := ε } Φ D rep hD k μ ν).symm

end Classes

end QED.ChainProof.SetASpec

end
