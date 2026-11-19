/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4Counterterm

/-!
# (R-Π₄) step L2: the `d₂` remainder of the inserted bubble converges

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L2. The `d₂` part of a
`fermionCt` insertion contracts one propagator up to `iε`
(`QED.GradedProof.RPi4.insG_eq`): `d₂ (1 + iε D_y⁻¹) B`, with the bubble `B`. The remainder is
`iε` times `remG = Tr[A N_x B N_y] D_x⁻¹ D_y⁻²`. Its block sum has a covariant limit
(`vpf_remBlock`), so `iε ∫ remG → 0`.

* `bubTr_eq`: `Tr[A (M - x̸) B (M - y̸)] = Tr[A x̸ B y̸] + M² Tr[A B]` for odd `A`, `B`;
* `tri_rem_eq`, `remTriple_eq`: the three-flavour combination of `remG` as nine pieces (the
  second divided difference `QED.GradedProof.VP2.tri_ins_eq` with `E₄ = 0`), whose numerators
  are the inserted-bubble numerators `n₁`, `n₂` at `d₂ = d_m = 1` (`nT1_one_one`);
* `vpf_remTriple`, `vpf_remBlock`: covariant, null-continuous limits (`VPF`).
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2
open QED.TwoLoop.Bridge (electronNumerator propDenom propDenom_ne_zero IsLoopPoly)

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-! ### Algebra -/

/-- **The bubble trace is even in the mass.** -/
theorem bubTr_eq {A B : Mat} (hA : IsOddG A) (hB : IsOddG B) (M : ℝ) (x y : Fin 4 → ℝ) :
    bubTr A B M x y = (A * (Dirac.slash x * (B * Dirac.slash y))).trace +
      (M : ℂ) ^ 2 * (A * B).trace := by
  have h1 : (A * (B * Dirac.slash y)).trace = 0 := IsOddG.trace3 hA hB (isOddG_slash y)
  have h2 : (A * (Dirac.slash x * B)).trace = 0 := IsOddG.trace3 hA (isOddG_slash x) hB
  simp only [bubTr, electronNumerator, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.mul_assoc, smul_eq_mul, h1, h2]
  ring

/-- **The `n₁` numerator at `d₂ = d_m = 1`** is `Tr[A x̸ B y̸] - y² Tr[A B]`. -/
theorem nT1_one_one (A B : Mat) (x y : Fin 4 → ℝ) :
    nT1 A B 1 1 x y = (A * (Dirac.slash x * (B * Dirac.slash y))).trace - v0 y * (A * B).trace := by
  simp only [nT1, insT2, insT4, slash_mul_slash_v0, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_smul, smul_eq_mul]
  push_cast
  ring

/-- **The three-flavour combination of `t₀ + s t₂` over `(U + s)(V + s)²`.** -/
theorem tri_rem_eq (U V s0 s1 s2 t0 t2 : ℂ) (h12 : s1 - s2 ≠ 0)
    (ha0 : U + s0 ≠ 0) (ha1 : U + s1 ≠ 0) (ha2 : U + s2 ≠ 0)
    (hb0 : V + s0 ≠ 0) (hb1 : V + s1 ≠ 0) (hb2 : V + s2 ≠ 0) :
    (t0 + s0 * t2) * (U + s0)⁻¹ * ((V + s0)⁻¹) ^ 2 +
        (s2 - s0) / (s1 - s2) * ((t0 + s1 * t2) * (U + s1)⁻¹ * ((V + s1)⁻¹) ^ 2) +
        (s0 - s1) / (s1 - s2) * ((t0 + s2 * t2) * (U + s2)⁻¹ * ((V + s2)⁻¹) ^ 2) =
      (s1 - s0) * (s2 - s0) *
        ((t0 - V * t2) *
            ((U + s0)⁻¹ * (V + s0)⁻¹ * (V + s1)⁻¹ * (V + s2)⁻¹ * (V + s0)⁻¹ +
              (U + s0)⁻¹ * (V + s0)⁻¹ * (V + s1)⁻¹ * (V + s2)⁻¹ * (V + s1)⁻¹ +
              (U + s0)⁻¹ * (V + s0)⁻¹ * (V + s1)⁻¹ * (V + s2)⁻¹ * (V + s2)⁻¹ +
              (U + s0)⁻¹ * (U + s1)⁻¹ * (V + s1)⁻¹ * (V + s2)⁻¹ * (V + s1)⁻¹ +
              (U + s0)⁻¹ * (U + s1)⁻¹ * (V + s1)⁻¹ * (V + s2)⁻¹ * (V + s2)⁻¹ +
              (U + s0)⁻¹ * (U + s1)⁻¹ * (U + s2)⁻¹ * (V + s2)⁻¹ * (V + s2)⁻¹) +
          t2 * ((U + s0)⁻¹ * (V + s0)⁻¹ * (V + s1)⁻¹ * (V + s2)⁻¹ +
              (U + s0)⁻¹ * (U + s1)⁻¹ * (V + s1)⁻¹ * (V + s2)⁻¹ +
              (U + s0)⁻¹ * (U + s1)⁻¹ * (U + s2)⁻¹ * (V + s2)⁻¹)) := by
  have h := tri_ins_eq U V s0 s1 s2 t0 t2 0 h12 ha0 ha1 ha2 hb0 hb1 hb2
  linear_combination h

/-- The remainder `Tr[A N_x B N_y] D_x⁻¹ D_y⁻²` of the `d₂` part of an inserted bubble. -/
noncomputable def remG (A B : Mat) (M ε : ℝ) (x y : Fin 4 → ℝ) : ℂ :=
  bubTr A B M x y * (propDenom M ε x)⁻¹ * ((propDenom M ε y)⁻¹) ^ 2

/-- **The three-flavour remainder as nine pieces.** -/
theorem remTriple_eq {A B : Mat} (hA : IsOddG A) (hB : IsOddG B) (M X Y : ℝ)
    (hXY : X ^ 2 - Y ^ 2 ≠ 0) {ε : ℝ} (hε : ε ≠ 0) (x y : Fin 4 → ℝ) :
    remG A B M ε x y + (triA M X Y : ℂ) * remG A B X ε x y +
        (triB M X Y : ℂ) * remG A B Y ε x y =
      (((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2)) *
        ((nT1 A B 1 1 x y + (ε * I) * nT2 A B 1) *
            (pd M ε x * pd M ε y * pd X ε y * pd Y ε y * pd M ε y) +
          (nT1 A B 1 1 x y + (ε * I) * nT2 A B 1) *
            (pd M ε x * pd M ε y * pd X ε y * pd Y ε y * pd X ε y) +
          (nT1 A B 1 1 x y + (ε * I) * nT2 A B 1) *
            (pd M ε x * pd M ε y * pd X ε y * pd Y ε y * pd Y ε y) +
          (nT1 A B 1 1 x y + (ε * I) * nT2 A B 1) *
            (pd M ε x * pd X ε x * pd X ε y * pd Y ε y * pd X ε y) +
          (nT1 A B 1 1 x y + (ε * I) * nT2 A B 1) *
            (pd M ε x * pd X ε x * pd X ε y * pd Y ε y * pd Y ε y) +
          (nT1 A B 1 1 x y + (ε * I) * nT2 A B 1) *
            (pd M ε x * pd X ε x * pd Y ε x * pd Y ε y * pd Y ε y) +
          nT2 A B 1 * (pd M ε x * pd M ε y * pd X ε y * pd Y ε y) +
          nT2 A B 1 * (pd M ε x * pd X ε x * pd X ε y * pd Y ε y) +
          nT2 A B 1 * (pd M ε x * pd X ε x * pd Y ε x * pd Y ε y)) := by
  have h12 : (X : ℂ) ^ 2 - (Y : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hXY
  have hA' : (triA M X Y : ℂ) =
      ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2) := by
    simp only [triA]; push_cast; rfl
  have hB' : (triB M X Y : ℂ) =
      ((M : ℂ) ^ 2 - (X : ℂ) ^ 2) / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2) := by
    simp only [triB]; push_cast; rfl
  have hd : ∀ (m : ℝ) (z : Fin 4 → ℝ), propDenom 0 ε z + (m : ℂ) ^ 2 ≠ 0 := fun m z => by
    rw [← propDenom_eq_add]
    exact propDenom_ne_zero hε _
  have hn1 : nT1 A B 1 1 x y + (ε * I) * nT2 A B 1 =
      (A * (Dirac.slash x * (B * Dirac.slash y))).trace - propDenom 0 ε y * (A * B).trace := by
    rw [nT1_one_one, propDenom_zero_eps]
    simp only [nT2, insT4]
    push_cast
    ring
  have hn2 : nT2 A B 1 = (A * B).trace := by
    simp only [nT2, insT4]
    push_cast
    ring
  rw [hn1, hn2]
  simp only [pd, remG, bubTr_eq hA hB]
  rw [propDenom_eq_add M ε x, propDenom_eq_add X ε x, propDenom_eq_add Y ε x,
    propDenom_eq_add M ε y, propDenom_eq_add X ε y, propDenom_eq_add Y ε y, hA', hB']
  have h := tri_rem_eq (propDenom 0 ε x) (propDenom 0 ε y) ((M : ℂ) ^ 2) ((X : ℂ) ^ 2)
    ((Y : ℂ) ^ 2) (A * (Dirac.slash x * (B * Dirac.slash y))).trace (A * B).trace h12
    (hd M x) (hd X x) (hd Y x) (hd M y) (hd X y) (hd Y y)
  linear_combination h

/-! ### Covariant limits -/

section Pieces

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (sw bx bY : Bool)
include hm₀

theorem vpf_rem5 (m0 m1 m2 m3 m4 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3 ∧ m₀ ≤ m4)
    (c0 c1 c2 c3 c4 : Bool) :
    VPF (m₀ + m₀) fun ε k q i j => (tnS sw 1 1 1 bx bY k q i j +
      (ε * I) * tnS sw 2 1 1 bx bY k q i j) *
      ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
        (propDenom m2 ε (zk k c2 q))⁻¹ * (propDenom m3 ε (zk k c3 q))⁻¹ *
        (propDenom m4 ε (zk k c4 q))⁻¹) := by
  have P := fun (j : Fin 3)
      (hN : ∀ p i l, IsLoopPoly 2 4 fun ℓ => tnS sw j 1 1 bx bY p (ℓ 0) i l) =>
    vpf_five hm₀ m0 m1 m2 m3 m4 hm c0 c1 c2 c3 c4 (tnS sw j 1 1 bx bY) hN
      (tcovN_tnS sw j 1 1 bx bY) (isLoopPoly_tnS_k sw j 1 1 bx bY)
  have p1 := P 1 fun p i l => (isLoopPoly_tnS1 sw 1 1 bx bY p i l).mono (by norm_num)
  have p2 := (P 2 fun p i l => (isLoopPoly_tnS2 sw 1 1 bx bY p i l).mono (by norm_num)).mul
    tendsto_epsI
  refine (p1.add p2).congr fun ε _ k q i j => ?_
  ring

theorem vpf_rem4 (m0 m1 m2 m3 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3)
    (c0 c1 c2 c3 : Bool) :
    VPF (m₀ + m₀) fun ε k q i j => tnS sw 2 1 1 bx bY k q i j *
      ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
        (propDenom m2 ε (zk k c2 q))⁻¹ * (propDenom m3 ε (zk k c3 q))⁻¹) :=
  vpf_four hm₀ m0 m1 m2 m3 hm c0 c1 c2 c3 (tnS sw 2 1 1 bx bY)
    (fun p i l => (isLoopPoly_tnS2 sw 1 1 bx bY p i l).mono (by norm_num))
    (tcovN_tnS sw 2 1 1 bx bY) (isLoopPoly_tnS_k sw 2 1 1 bx bY)

/-- **The three-flavour remainder has a covariant, null-continuous limit.** -/
theorem vpf_remTriple (M X Y : ℝ) (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y)
    (hXY : X ^ 2 - Y ^ 2 ≠ 0) :
    VPF (m₀ + m₀) fun ε k q i j =>
      remG (gAF sw i j) (gBF sw i j) M ε (zk k bx q) (zk k bY q) +
        (triA M X Y : ℂ) * remG (gAF sw i j) (gBF sw i j) X ε (zk k bx q) (zk k bY q) +
        (triB M X Y : ℂ) * remG (gAF sw i j) (gBF sw i j) Y ε (zk k bx q) (zk k bY q) := by
  have E0 := vpf_rem5 hm₀ sw bx bY
  have E2 := vpf_rem4 hm₀ sw bx bY
  have s := (((((((((E0 M M X Y M ⟨hM, hM, hX, hY, hM⟩ bx bY bY bY bY).add
    (E0 M M X Y X ⟨hM, hM, hX, hY, hX⟩ bx bY bY bY bY)).add
    (E0 M M X Y Y ⟨hM, hM, hX, hY, hY⟩ bx bY bY bY bY)).add
    (E0 M X X Y X ⟨hM, hX, hX, hY, hX⟩ bx bx bY bY bY)).add
    (E0 M X X Y Y ⟨hM, hX, hX, hY, hY⟩ bx bx bY bY bY)).add
    (E0 M X Y Y Y ⟨hM, hX, hY, hY, hY⟩ bx bx bx bY bY)).add
    (E2 M M X Y ⟨hM, hM, hX, hY⟩ bx bY bY bY)).add
    (E2 M X X Y ⟨hM, hX, hX, hY⟩ bx bx bY bY)).add
    (E2 M X Y Y ⟨hM, hX, hY, hY⟩ bx bx bx bY)).const_mul
    (((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2))
  refine s.congr fun ε hε k q i j => ?_
  have hA : IsOddG (gAF sw i j) := isOddG_gamma _
  have hB : IsOddG (gBF sw i j) := isOddG_gamma _
  rw [remTriple_eq hA hB M X Y hXY hε.ne' (zk k bx q) (zk k bY q), nT1_gAB,
    nT2_gAB sw 1 1 bx bY k q]

end Pieces

section Block

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

/-- The block-summed remainder `∑_f c_f d(rep f) remG(M_f)` with the gamma matrices of the index
order `sw`. -/
noncomputable def remBlock (d : F → ℂ) (sw bx bY : Bool) (ε : ℝ) (k q : Fin 4 → ℝ)
    (μ ν : Fin 4) : ℂ :=
  ∑ f, (Φ.coeff f : ℂ) * (d (rep f) *
    remG (gAF sw μ ν) (gBF sw μ ν) (Φ.mass f) ε (zk k bx q) (zk k bY q))

/-- **The block-summed remainder has a covariant, null-continuous limit.** -/
theorem vpf_remBlock (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (d : F → ℂ) (sw bx bY : Bool) :
    VPF (m₀ + m₀) fun ε k q μ ν => remBlock Φ rep d sw bx bY ε k q μ ν := by
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
  refine (VPF.sum Finset.univ (fun f _ => (vpf_remTriple hm₀ sw bx bY (Φ.mass f) X (X + 1)
    (hmass f) (by linarith [hlt f, hmass f]) (by linarith [hlt f, hmass f]) hXY).const_mul
      ((Φ.coeff f : ℂ) * d (rep f))) (by nlinarith)).congr fun ε _ k q μ ν => ?_
  simp only [remBlock]
  rw [sum_block_eq_sum_triple Φ rep hrep hPV₁ hPV₂ X (X + 1) (fun r M => d r *
    remG (gAF sw μ ν) (gBF sw μ ν) M ε (zk k bx q) (zk k bY q))]
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

end Block

end QED.GradedProof.RPi4

end
