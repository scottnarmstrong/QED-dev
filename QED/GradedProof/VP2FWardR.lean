/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2FWardAlg

/-!
# The remainder of the Ward identity of the inserted bubbles has a limit

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2, the Ward step of
the classes `F0`, `F1`. The remainder `R(x, y) = (δ₂ y² + δ_m M²) D_y⁻² D_x⁻¹`
(`QED.GradedProof.VP2.wfR`) of the Ward identity `wardF_mass` comes with a factor `iε`; its block
sum, times the constant tensor `Tr[γ^i γ^j]`, has a limit as `ε → 0⁺` (a `VPF` family), so the
remainder term vanishes in the limit.

* `rTriple_eq`: one three-flavour set of `R` as nine pieces (the second divided difference
  `QED.GradedProof.VP2.tri_ins_eq` with `E₀ = δ₂ y²`, `E₂ = δ_m`, `E₄ = 0`);
* `vpf_rTriple`, `vpf_rBlock`: the pieces, one set, and the block sum are `VPF` families.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.VP2

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance

/-- **One three-flavour set of the remainder as nine pieces.** -/
theorem rTriple_eq (d₂ dm M X Y : ℝ) (hXY : X ^ 2 - Y ^ 2 ≠ 0) {ε : ℝ} (hε : ε ≠ 0)
    (x y : Fin 4 → ℝ) :
    wfR d₂ dm M ε x y + (triA M X Y : ℂ) * wfR d₂ dm X ε x y +
        (triB M X Y : ℂ) * wfR d₂ dm Y ε x y =
      (((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2)) *
        ((((d₂ : ℂ) - dm) * v0 y + (ε * I) * dm) *
            (pd M ε x * pd M ε y * pd X ε y * pd Y ε y * pd M ε y +
              pd M ε x * pd M ε y * pd X ε y * pd Y ε y * pd X ε y +
              pd M ε x * pd M ε y * pd X ε y * pd Y ε y * pd Y ε y +
              pd M ε x * pd X ε x * pd X ε y * pd Y ε y * pd X ε y +
              pd M ε x * pd X ε x * pd X ε y * pd Y ε y * pd Y ε y +
              pd M ε x * pd X ε x * pd Y ε x * pd Y ε y * pd Y ε y) +
          (dm : ℂ) * (pd M ε x * pd M ε y * pd X ε y * pd Y ε y +
            pd M ε x * pd X ε x * pd X ε y * pd Y ε y +
            pd M ε x * pd X ε x * pd Y ε x * pd Y ε y)) := by
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
  have key := tri_ins_eq (propDenom 0 ε x) (propDenom 0 ε y) ((M : ℂ) ^ 2) ((X : ℂ) ^ 2)
    ((Y : ℂ) ^ 2) ((d₂ : ℂ) * v0 y) (dm : ℂ) 0 h12 (hd M x) (hd X x) (hd Y x) (hd M y)
    (hd X y) (hd Y y)
  have hv := propDenom_zero_eps ε y
  simp only [pd, wfR]
  rw [propDenom_eq_add M ε x, propDenom_eq_add X ε x, propDenom_eq_add Y ε x,
    propDenom_eq_add M ε y, propDenom_eq_add X ε y, propDenom_eq_add Y ε y, hA', hB']
  rw [hv] at key ⊢
  linear_combination key

/-! ### The pieces -/

/-- The numerator `Tr[γ^i γ^j] c y²` of a piece. -/
noncomputable def tRv (c : ℝ) (bY : Bool) (k q : Fin 4 → ℝ) (i j : Fin 4) : ℂ :=
  traceT 1 1 i j * ((c : ℂ) * v0 (zk k bY q))

/-- The numerator `Tr[γ^i γ^j] c` of a piece. -/
noncomputable def tRc (c : ℝ) (_k _q : Fin 4 → ℝ) (i j : Fin 4) : ℂ := traceT 1 1 i j * c

theorem tcovN_tRv (c : ℝ) (bY : Bool) : TCovN (tRv c bY) := by
  have h := (tcovN_traceT MCov.one MCov.one).mul_inv
    (c := fun k q => (c : ℂ) * v0 (zk k bY q)) fun L S S' hL k q => by
      simp only [v0_inv bY L S S' hL]
  refine (congrArg TCovN ?_).mp h
  funext k q i j
  simp only [tRv]
  ring

theorem tcovN_tRc (c : ℝ) : TCovN (tRc c) := by
  have h := (tcovN_traceT MCov.one MCov.one).mul_inv (c := fun _ _ => (c : ℂ))
    fun _ _ _ _ _ _ => rfl
  refine (congrArg TCovN ?_).mp h
  funext k q i j
  simp only [tRc]
  ring

theorem isLoopPoly_tRv (c : ℝ) (bY : Bool) (k : Fin 4 → ℝ) (i j : Fin 4) :
    IsLoopPoly 2 4 fun ℓ => tRv c bY k (ℓ 0) i j :=
  ((((isLoopAffine_zk k bY).isLoopPoly_propDenom 0 0).const_mul (c : ℂ)).const_mul
    (traceT 1 1 i j)).mono (by norm_num)

theorem isLoopPoly_tRv_k (c : ℝ) (bY : Bool) (q : Fin 4 → ℝ) (i j : Fin 4) :
    IsLoopPoly 1 2 fun y => tRv c bY (y 0) q i j :=
  (((isLoopAffine_zk_one q bY).isLoopPoly_propDenom 0 0).const_mul (c : ℂ)).const_mul
    (traceT 1 1 i j)

theorem isLoopPoly_tRc {L : ℕ} (c : ℝ) (k q : Fin 4 → ℝ) (i j : Fin 4) {n : ℕ} :
    IsLoopPoly L n fun _ => tRc c k q i j :=
  (IsLoopPoly.const (n := 0) _).mono (Nat.zero_le _)

section Pieces

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (d₂ dm : ℝ) (bx bY : Bool)
include hm₀

theorem vpf_R5 (m0 m1 m2 m3 m4 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3 ∧ m₀ ≤ m4)
    (c0 c1 c2 c3 c4 : Bool) :
    VPF (m₀ + m₀) fun ε k q i j =>
      traceT 1 1 i j * (((d₂ : ℂ) - dm) * v0 (zk k bY q) + (ε * I) * dm) *
      ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
        (propDenom m2 ε (zk k c2 q))⁻¹ * (propDenom m3 ε (zk k c3 q))⁻¹ *
        (propDenom m4 ε (zk k c4 q))⁻¹) := by
  have p0 := vpf_five hm₀ m0 m1 m2 m3 m4 hm c0 c1 c2 c3 c4 (tRv (d₂ - dm) bY)
    (isLoopPoly_tRv (d₂ - dm) bY) (tcovN_tRv (d₂ - dm) bY) (isLoopPoly_tRv_k (d₂ - dm) bY)
  have p1 := (vpf_five hm₀ m0 m1 m2 m3 m4 hm c0 c1 c2 c3 c4 (tRc dm)
    (fun p i j => isLoopPoly_tRc dm p 0 i j) (tcovN_tRc dm)
    (fun q i j => isLoopPoly_tRc (n := 0) dm 0 q i j)).mul tendsto_epsI
  refine (p0.add p1).congr fun ε _ k q i j => ?_
  simp only [tRv, tRc]
  push_cast
  ring

theorem vpf_R4 (m0 m1 m2 m3 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3)
    (c0 c1 c2 c3 : Bool) :
    VPF (m₀ + m₀) fun ε k q i j => traceT 1 1 i j * (dm : ℂ) *
      ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
        (propDenom m2 ε (zk k c2 q))⁻¹ * (propDenom m3 ε (zk k c3 q))⁻¹) :=
  vpf_four hm₀ m0 m1 m2 m3 hm c0 c1 c2 c3 (tRc dm) (fun p i j => isLoopPoly_tRc dm p 0 i j)
    (tcovN_tRc dm) (fun q i j => isLoopPoly_tRc (n := 0) dm 0 q i j)

/-- **One three-flavour set of the remainder, times `Tr[γ^i γ^j]`, is a `VPF` family.** -/
theorem vpf_rTriple (M X Y : ℝ) (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y)
    (hXY : X ^ 2 - Y ^ 2 ≠ 0) :
    VPF (m₀ + m₀) fun ε k q i j => traceT 1 1 i j *
      (wfR d₂ dm M ε (zk k bx q) (zk k bY q) +
        (triA M X Y : ℂ) * wfR d₂ dm X ε (zk k bx q) (zk k bY q) +
        (triB M X Y : ℂ) * wfR d₂ dm Y ε (zk k bx q) (zk k bY q)) := by
  have E0 := vpf_R5 hm₀ d₂ dm bY
  have E2 := vpf_R4 hm₀ dm
  have s := ((((((((E0 M M X Y M ⟨hM, hM, hX, hY, hM⟩ bx bY bY bY bY).add
    (E0 M M X Y X ⟨hM, hM, hX, hY, hX⟩ bx bY bY bY bY)).add
    (E0 M M X Y Y ⟨hM, hM, hX, hY, hY⟩ bx bY bY bY bY)).add
    (E0 M X X Y X ⟨hM, hX, hX, hY, hX⟩ bx bx bY bY bY)).add
    (E0 M X X Y Y ⟨hM, hX, hX, hY, hY⟩ bx bx bY bY bY)).add
    (E0 M X Y Y Y ⟨hM, hX, hY, hY, hY⟩ bx bx bx bY bY)).add
    (E2 M M X Y ⟨hM, hM, hX, hY⟩ bx bY bY bY)).add
    (E2 M X X Y ⟨hM, hX, hX, hY⟩ bx bx bY bY)).add
    (E2 M X Y Y ⟨hM, hX, hY, hY⟩ bx bx bx bY) |>.const_mul
    (((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2))
  refine s.congr fun ε hε k q i j => ?_
  rw [rTriple_eq d₂ dm M X Y hXY hε.ne' (zk k bx q) (zk k bY q)]
  simp only [pd]
  ring

end Pieces

/-- **The block-summed remainder, times `Tr[γ^i γ^j]`, is a `VPF` family.** -/
theorem vpf_rBlock {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (rep : F → F) (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (d₂ dm : F → ℝ) (K : ℂ) (bx bY : Bool) :
    VPF (m₀ + m₀) fun ε k q i j => traceT 1 1 i j * ∑ f, (Φ.coeff f : ℂ) *
      (K * wfR (d₂ (rep f)) (dm (rep f)) (Φ.mass f) ε (zk k bx q) (zk k bY q)) := by
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
  refine (VPF.sum Finset.univ (fun f _ => (vpf_rTriple hm₀ (d₂ (rep f)) (dm (rep f)) bx bY
    (Φ.mass f) X (X + 1) (hmass f) (by linarith [hlt f, hmass f])
    (by linarith [hlt f, hmass f]) hXY).const_mul ((Φ.coeff f : ℂ) * K))
    (by nlinarith)).congr fun ε _ k q i j => ?_
  rw [sum_block_eq_sum_triple Φ rep hrep hPV₁ hPV₂ X (X + 1) (fun r M =>
    K * wfR (d₂ r) (dm r) M ε (zk k bx q) (zk k bY q)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

end QED.GradedProof.VP2

end
