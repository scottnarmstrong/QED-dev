/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2FPieces

/-!
# The inserted bubble at three masses: the limit

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2, classes `F0`,
`F1`.

* `insTriple_eq`: the three-flavour inserted bubble is `(X² - M²)(Y² - M²)` times ten pieces with
  the numerators `E₀ = n₀ + iε n₁ + (iε)² n₂`, `E₂ = n₁ + 2 iε n₂`, `E₄ = n₂` (the identity
  behind `QED.GradedProof.VP2.ef_insTriple`).
* `vpf_insTriple`: the three-flavour inserted bubble at the gamma matrices `γ^μ, γ^ν` (`sw =
  false`) or `γ^ν, γ^μ` (`sw = true`) satisfies `VPF (m₀ + m₀)` when all masses are at least `m₀`.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.VP2

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-- The inverse denominator `(x² + m² - iε)⁻¹`. -/
noncomputable abbrev pd (m ε : ℝ) (x : Fin 4 → ℝ) : ℂ := (propDenom m ε x)⁻¹

/-- **The three-flavour inserted bubble as ten pieces.** -/
theorem insTriple_eq {A B : Mat} (hA : IsOddG A) (hB : IsOddG B) (d₂ dm M X Y : ℝ)
    (hXY : X ^ 2 - Y ^ 2 ≠ 0) {ε : ℝ} (hε : ε ≠ 0) (x y : Fin 4 → ℝ) :
    insG A B d₂ dm M ε x y + (triA M X Y : ℂ) * insG A B d₂ dm X ε x y +
        (triB M X Y : ℂ) * insG A B d₂ dm Y ε x y =
      (((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2)) *
        ((nT0 A B d₂ dm x y + (ε * I) * nT1 A B d₂ dm x y + (ε * I) ^ 2 * nT2 A B dm) *
            (pd M ε x * pd M ε y * pd X ε y * pd Y ε y * pd M ε y) +
          (nT0 A B d₂ dm x y + (ε * I) * nT1 A B d₂ dm x y + (ε * I) ^ 2 * nT2 A B dm) *
            (pd M ε x * pd M ε y * pd X ε y * pd Y ε y * pd X ε y) +
          (nT0 A B d₂ dm x y + (ε * I) * nT1 A B d₂ dm x y + (ε * I) ^ 2 * nT2 A B dm) *
            (pd M ε x * pd M ε y * pd X ε y * pd Y ε y * pd Y ε y) +
          (nT0 A B d₂ dm x y + (ε * I) * nT1 A B d₂ dm x y + (ε * I) ^ 2 * nT2 A B dm) *
            (pd M ε x * pd X ε x * pd X ε y * pd Y ε y * pd X ε y) +
          (nT0 A B d₂ dm x y + (ε * I) * nT1 A B d₂ dm x y + (ε * I) ^ 2 * nT2 A B dm) *
            (pd M ε x * pd X ε x * pd X ε y * pd Y ε y * pd Y ε y) +
          (nT0 A B d₂ dm x y + (ε * I) * nT1 A B d₂ dm x y + (ε * I) ^ 2 * nT2 A B dm) *
            (pd M ε x * pd X ε x * pd Y ε x * pd Y ε y * pd Y ε y) +
          (nT1 A B d₂ dm x y + 2 * (ε * I) * nT2 A B dm) *
            (pd M ε x * pd M ε y * pd X ε y * pd Y ε y) +
          (nT1 A B d₂ dm x y + 2 * (ε * I) * nT2 A B dm) *
            (pd M ε x * pd X ε x * pd X ε y * pd Y ε y) +
          (nT1 A B d₂ dm x y + 2 * (ε * I) * nT2 A B dm) *
            (pd M ε x * pd X ε x * pd Y ε x * pd Y ε y) +
          nT2 A B dm * (pd M ε x * pd X ε x * pd Y ε x)) := by
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
  have e0 := eE0_eq A B d₂ dm ε x y
  have e2 := eE2_eq A B d₂ dm ε x y
  simp only [pd, insG, insTr_eq hA hB]
  rw [propDenom_eq_add M ε x, propDenom_eq_add X ε x, propDenom_eq_add Y ε x,
    propDenom_eq_add M ε y, propDenom_eq_add X ε y, propDenom_eq_add Y ε y, hA', hB']
  rw [tri_ins_eq _ _ _ _ _ _ _ _ h12 (hd M x) (hd X x) (hd Y x) (hd M y) (hd X y) (hd Y y)]
  rw [← e0, ← e2]
  simp only [nT2]
  ring

/-! ### The covariant numerators in either index order -/

/-- `n_j` at `(γ^μ, γ^ν)` (`sw = false`) or `(γ^ν, γ^μ)` (`sw = true`). -/
noncomputable def tnS (sw : Bool) (j : Fin 3) (d₂ dm : ℝ) (bx bY : Bool) (k q : Fin 4 → ℝ)
    (μ ν : Fin 4) : ℂ :=
  if sw then tn j d₂ dm bx bY k q ν μ else tn j d₂ dm bx bY k q μ ν

theorem tcovN_tnS (sw : Bool) (j : Fin 3) (d₂ dm : ℝ) (bx bY : Bool) :
    TCovN (tnS sw j d₂ dm bx bY) := by
  cases sw
  · exact tcovN_tn j d₂ dm bx bY
  · exact (tcovN_tn j d₂ dm bx bY).transpose

theorem isLoopPoly_tnS0 (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    IsLoopPoly 2 4 fun ℓ => tnS sw 0 d₂ dm bx bY k (ℓ 0) μ ν := by
  cases sw
  · exact isLoopPoly_tn 0 d₂ dm bx bY k μ ν
  · exact isLoopPoly_tn 0 d₂ dm bx bY k ν μ

theorem isLoopPoly_tnS1 (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    IsLoopPoly 2 2 fun ℓ => tnS sw 1 d₂ dm bx bY k (ℓ 0) μ ν := by
  cases sw
  · exact isLoopPoly_tn 1 d₂ dm bx bY k μ ν
  · exact isLoopPoly_tn 1 d₂ dm bx bY k ν μ

theorem isLoopPoly_tnS2 (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    IsLoopPoly 2 0 fun ℓ => tnS sw 2 d₂ dm bx bY k (ℓ 0) μ ν := by
  cases sw
  · exact isLoopPoly_tn 2 d₂ dm bx bY k μ ν
  · exact isLoopPoly_tn 2 d₂ dm bx bY k ν μ

theorem isLoopPoly_tnS_k (sw : Bool) (j : Fin 3) (d₂ dm : ℝ) (bx bY : Bool) (q : Fin 4 → ℝ)
    (μ ν : Fin 4) : IsLoopPoly 1 4 fun y => tnS sw j d₂ dm bx bY (y 0) q μ ν := by
  cases sw
  · exact isLoopPoly_tn_k j d₂ dm bx bY q μ ν
  · exact isLoopPoly_tn_k j d₂ dm bx bY q ν μ

/-- The gamma matrices of the index order `sw`. -/
noncomputable def gAF (sw : Bool) (μ ν : Fin 4) : Mat :=
  Dirac.gamma (if sw then ν else μ)

/-- The gamma matrices of the index order `sw`. -/
noncomputable def gBF (sw : Bool) (μ ν : Fin 4) : Mat :=
  Dirac.gamma (if sw then μ else ν)

theorem nT0_gAB (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool) (k q : Fin 4 → ℝ) (μ ν : Fin 4) :
    nT0 (gAF sw μ ν) (gBF sw μ ν) d₂ dm (zk k bx q) (zk k bY q) = tnS sw 0 d₂ dm bx bY k q μ ν := by
  cases sw <;> rfl

theorem nT1_gAB (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool) (k q : Fin 4 → ℝ) (μ ν : Fin 4) :
    nT1 (gAF sw μ ν) (gBF sw μ ν) d₂ dm (zk k bx q) (zk k bY q) = tnS sw 1 d₂ dm bx bY k q μ ν := by
  cases sw <;> rfl

theorem nT2_gAB (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool) (k q : Fin 4 → ℝ) (μ ν : Fin 4) :
    nT2 (gAF sw μ ν) (gBF sw μ ν) dm = tnS sw 2 d₂ dm bx bY k q μ ν := by
  cases sw <;> rfl

/-! ### The pieces -/

theorem tendsto_epsI : Tendsto (fun ε : ℝ => (ε : ℂ) * I) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous fun ε : ℝ => (ε : ℂ) * I := continuous_ofReal.mul continuous_const
  have h := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simp only [ofReal_zero, zero_mul] at h
  exact h

section Pieces

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool)
include hm₀

theorem vpf_E0 (m0 m1 m2 m3 m4 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3 ∧ m₀ ≤ m4)
    (c0 c1 c2 c3 c4 : Bool) :
    VPF (m₀ + m₀) fun ε k q i j => (tnS sw 0 d₂ dm bx bY k q i j +
      (ε * I) * tnS sw 1 d₂ dm bx bY k q i j + (ε * I) ^ 2 * tnS sw 2 d₂ dm bx bY k q i j) *
      ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
        (propDenom m2 ε (zk k c2 q))⁻¹ * (propDenom m3 ε (zk k c3 q))⁻¹ *
        (propDenom m4 ε (zk k c4 q))⁻¹) := by
  have P := fun (j : Fin 3)
      (hN : ∀ p i l, IsLoopPoly 2 4 fun ℓ => tnS sw j d₂ dm bx bY p (ℓ 0) i l) =>
    vpf_five hm₀ m0 m1 m2 m3 m4 hm c0 c1 c2 c3 c4 (tnS sw j d₂ dm bx bY) hN
      (tcovN_tnS sw j d₂ dm bx bY) (isLoopPoly_tnS_k sw j d₂ dm bx bY)
  have p0 := P 0 (isLoopPoly_tnS0 sw d₂ dm bx bY)
  have p1 := (P 1 fun p i l => (isLoopPoly_tnS1 sw d₂ dm bx bY p i l).mono (by norm_num)).mul
    tendsto_epsI
  have p2 := (P 2 fun p i l => (isLoopPoly_tnS2 sw d₂ dm bx bY p i l).mono (by norm_num)).mul
    (tendsto_epsI.pow 2)
  refine ((p0.add p1).add p2).congr fun ε _ k q i j => ?_
  ring

theorem vpf_E2 (m0 m1 m2 m3 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3)
    (c0 c1 c2 c3 : Bool) :
    VPF (m₀ + m₀) fun ε k q i j => (tnS sw 1 d₂ dm bx bY k q i j +
      2 * (ε * I) * tnS sw 2 d₂ dm bx bY k q i j) *
      ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
        (propDenom m2 ε (zk k c2 q))⁻¹ * (propDenom m3 ε (zk k c3 q))⁻¹) := by
  have p1 := vpf_four hm₀ m0 m1 m2 m3 hm c0 c1 c2 c3 (tnS sw 1 d₂ dm bx bY)
    (isLoopPoly_tnS1 sw d₂ dm bx bY) (tcovN_tnS sw 1 d₂ dm bx bY)
    (isLoopPoly_tnS_k sw 1 d₂ dm bx bY)
  have p2 := (vpf_four hm₀ m0 m1 m2 m3 hm c0 c1 c2 c3 (tnS sw 2 d₂ dm bx bY)
    (fun p i l => (isLoopPoly_tnS2 sw d₂ dm bx bY p i l).mono (by norm_num))
    (tcovN_tnS sw 2 d₂ dm bx bY) (isLoopPoly_tnS_k sw 2 d₂ dm bx bY)).mul
    (tendsto_epsI.const_mul 2)
  refine (p1.add p2).congr fun ε _ k q i j => ?_
  ring

theorem vpf_E4 (m0 m1 m2 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2) (c0 c1 c2 : Bool) :
    VPF (m₀ + m₀) fun ε k q i j => tnS sw 2 d₂ dm bx bY k q i j *
      ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
        (propDenom m2 ε (zk k c2 q))⁻¹) :=
  vpf_three hm₀ m0 m1 m2 hm c0 c1 c2 (tnS sw 2 d₂ dm bx bY) (isLoopPoly_tnS2 sw d₂ dm bx bY)
    (tcovN_tnS sw 2 d₂ dm bx bY) (isLoopPoly_tnS_k sw 2 d₂ dm bx bY)

/-- **The three-flavour inserted bubble has a covariant, null-continuous limit.** -/
theorem vpf_insTriple (M X Y : ℝ) (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y)
    (hXY : X ^ 2 - Y ^ 2 ≠ 0) :
    VPF (m₀ + m₀) fun ε k q i j =>
      insG (gAF sw i j) (gBF sw i j) d₂ dm M ε (zk k bx q) (zk k bY q) +
        (triA M X Y : ℂ) * insG (gAF sw i j) (gBF sw i j) d₂ dm X ε (zk k bx q) (zk k bY q) +
        (triB M X Y : ℂ) * insG (gAF sw i j) (gBF sw i j) d₂ dm Y ε (zk k bx q) (zk k bY q) := by
  have E0 := vpf_E0 hm₀ sw d₂ dm bx bY
  have E2 := vpf_E2 hm₀ sw d₂ dm bx bY
  have s := ((((((((((E0 M M X Y M ⟨hM, hM, hX, hY, hM⟩ bx bY bY bY bY).add
    (E0 M M X Y X ⟨hM, hM, hX, hY, hX⟩ bx bY bY bY bY)).add
    (E0 M M X Y Y ⟨hM, hM, hX, hY, hY⟩ bx bY bY bY bY)).add
    (E0 M X X Y X ⟨hM, hX, hX, hY, hX⟩ bx bx bY bY bY)).add
    (E0 M X X Y Y ⟨hM, hX, hX, hY, hY⟩ bx bx bY bY bY)).add
    (E0 M X Y Y Y ⟨hM, hX, hY, hY, hY⟩ bx bx bx bY bY)).add
    (E2 M M X Y ⟨hM, hM, hX, hY⟩ bx bY bY bY)).add
    (E2 M X X Y ⟨hM, hX, hX, hY⟩ bx bx bY bY)).add
    (E2 M X Y Y ⟨hM, hX, hY, hY⟩ bx bx bx bY)).add
    (vpf_E4 hm₀ sw d₂ dm bx bY M X Y ⟨hM, hX, hY⟩ bx bx bx)).const_mul
    (((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2))
  refine s.congr fun ε hε k q i j => ?_
  have hA : IsOddG (gAF sw i j) := isOddG_gamma _
  have hB : IsOddG (gBF sw i j) := isOddG_gamma _
  rw [insTriple_eq hA hB d₂ dm M X Y hXY hε.ne' (zk k bx q) (zk k bY q),
    nT0_gAB, nT1_gAB, nT2_gAB sw d₂ dm bx bY k q]

end Pieces

end QED.GradedProof.VP2

end
