/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2Piece
public import QED.GradedProof.SE2FormP
public import QED.GradedProof.VP2FAlg
public import QED.TwoLoop.LimitCovarianceVP

/-!
# One-loop vacuum-polarization pieces through product data

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2, for the one-loop
classes `F0`, `F1`. The two-index analogue of `QED.GradedProof.SE2.hasSEForm_kinds`.

* `hasVPLim_kinds`: a one-loop integrand `F_ε(k, q)^{μν}` that, multiplied by the auxiliary loop
  `D_aux(ℓ₁)⁻³`, is an `ε`-independent numerator `N_k(q)^{μν}` over the denominators of product
  data given by line kinds, with `N` tensor covariant (`N_{Lk}(Lq) = L L N_k(q)` for every spinor
  lift of `L`) and polynomial in `k`, gives, times any convergent multiplier `h ε`, a family with a
  covariant, null-continuous limit (`HasVPLim`) below `-(m_e + μ)²`. The energy-first integral is
  the joint integral divided by that of the auxiliary loop (`auxLimit ≠ 0`).
* `hasVPLim_five`, `hasVPLim_four`, `hasVPLim_three`: the forms with five, four and three
  propagators at `q` or `k + q` (kinds `kinds5`), the shorter ones by padding a line
  (`D = D⁰ - iε`, so padding produces a second piece with the multiplier `-iε h`).
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.VP2

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.GradedProof.SE2

/-- A tensor family `N_k(q)^{μν}` is **covariant** under every spinor lift. -/
def TCovN (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S S' : Matrix (Fin 4) (Fin 4) ℂ), IsSpinLift L S S' →
    ∀ k q, N (L *ᵥ k) (L *ᵥ q) = upperAct L (N k q)

theorem reflectMatrix_mulVec_mulVec {a : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0)
    (v : Fin 4 → ℝ) : QED.Dirac.reflectMatrix a *ᵥ (QED.Dirac.reflectMatrix a *ᵥ v) = v := by
  rw [QED.Dirac.reflectMatrix_mulVec, QED.Dirac.reflectMatrix_mulVec, QED.Dirac.reflect_reflect ha]

/-- The reflection form of covariance used by `VPPiece`. -/
theorem TCovN.reflect {N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} (hN : TCovN N)
    {a : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0) (k q : Fin 4 → ℝ) (μ ν : Fin 4) :
    N k q μ ν = ∑ α, ∑ β, ((QED.Dirac.reflectMatrix a μ α : ℝ) : ℂ) *
      ((QED.Dirac.reflectMatrix a ν β : ℝ) : ℂ) *
        N (QED.Dirac.reflect a k) (QED.Dirac.reflectMatrix a *ᵥ q) α β := by
  have h := hN _ _ _ (QED.TwoLoop.ReflCovariance.isSpinLift_reflect ha)
    (QED.Dirac.reflect a k) (QED.Dirac.reflectMatrix a *ᵥ q)
  rw [← QED.Dirac.reflectMatrix_mulVec a k, reflectMatrix_mulVec_mulVec ha,
    reflectMatrix_mulVec_mulVec ha] at h
  rw [QED.Dirac.reflectMatrix_mulVec] at h
  rw [h]
  rfl

/-- **One-loop vacuum-polarization integrands through product data** have a covariant,
null-continuous limit, times any convergent multiplier. -/
theorem hasVPLim_kinds {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind)
    (hκ : ∀ i, κ i ≠ .out) (Ms : Fin (m + 1) → ℝ) {mass : ℝ} (hmass : 0 < mass) {me μ : ℝ}
    (hme : 0 < me) (hμ : 0 < μ)
    (hMe : ∀ i, κ i ≠ .pho → me ^ 2 ≤ Ms i ^ 2) (hMp : ∀ i, κ i = .pho → μ ^ 2 ≤ Ms i ^ 2)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (κ i).dir)
    (hcard : ({0, 1, 2, 3} : Finset (Fin (m + 1))).card = 4)
    (hE : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (m + 1))), κ e ≠ .aux)
    (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 4 fun ℓ => N p (ℓ 0) i j) (hcov : TCovN N)
    {d : ℕ} (hpoly : ∀ q i j, IsLoopPoly 1 d fun y => N (y 0) q i j)
    {h : ℝ → ℂ} {h₀ : ℂ} (hh : Tendsto h (𝓝[>] 0) (𝓝 h₀))
    (F : ℝ → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hfac : ∀ ε : ℝ, 0 < ε → ∀ p (ℓ : Fin 2 → Fin 4 → ℝ) i j,
      N p (ℓ 0) i j * ∏ k, (propDenom (Ms k) ε ((κ k).lineMom p p ℓ))⁻¹ =
        F ε p (ℓ 0) i j * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3) :
    HasVPLim (me + μ) fun ε p i j =>
      h ε * QED.OneLoop.energyFirstIntegral fun q => F ε p q i j := by
  set D := kindsData hm7 κ Ms hcrit
  have hmom := kindsData_mom hm7 κ hκ Ms hcrit
  have hα : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (m + 1))),
      (castLoopMatrix fun i => (κ i).dir) e = ![1, 0] := by
    intro e he
    have h := hE e he
    funext s
    rcases hk : κ e with _ | _ | _ | _
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · exact absurd hk h
  have hc : ∀ p : Fin 4 → ℝ, -(me + μ) ^ 2 < Minkowski.dot p p →
      0 < min 1 (1 + Minkowski.dot p p / (me + μ) ^ 2) * min (me ^ 2) (μ ^ 2) := fun p hs => by
    refine mul_pos (lt_min one_pos ?_) (lt_min (by positivity) (by positivity))
    have hT2 : 0 < (me + μ) ^ 2 := by positivity
    have h1 : 0 < (me + μ) ^ 2 + Minkowski.dot p p := by linarith
    calc (0 : ℝ) < ((me + μ) ^ 2 + Minkowski.dot p p) / (me + μ) ^ 2 := by positivity
      _ = 1 + Minkowski.dot p p / (me + μ) ^ 2 := by field_simp
  let P : VPPiece (me + μ) :=
    { D := D
      N := fun p ℓ => N p (ℓ 0)
      hQ := fun p i j => by
        obtain ⟨Q, hQ⟩ := (hN p i j).exists_loopQuartic
        refine ⟨Q, ⟨Or.inl hm7, ?_⟩, hQ⟩
        exact refinedBound_of_dependsOnZero _ hcard hα Q fun ℓ => by
          simp only [hQ, Matrix.cons_val_zero]
      hV := fun p hp => ⟨_, hc p hp, fun z hz hz1 hU => by
        rw [hmom p]
        exact symanzikV_kinds_se_ge κ hκ Ms hme hμ hp hMe hMp hz hz1 hU⟩
      hcov := fun a ha p ℓ μ ν => hcov.reflect ha p (ℓ 0) μ ν }
  have hH := tendsto_energyFirstIntegral_aux hmass
  have hH0 := auxLimit_ne_zero hmass
  refine P.hasVPLim (by nlinarith [hme, hμ]) (d := d) (fun ℓ i j => hpoly (ℓ 0) i j)
    (h := fun ε => h ε * (QED.OneLoop.energyFirstIntegral fun k =>
      ((propDenom mass ε k)⁻¹) ^ 3)⁻¹)
    (hh.mul (hH.inv₀ hH0)) fun p _ i j => ?_
  filter_upwards [self_mem_nhdsWithin, hH.eventually_ne hH0] with ε (hε : 0 < ε) hne
  have e : (fun ℓ => P.N p ℓ i j * ∏ k, (lineDenom P.D.α (P.D.mom p) P.D.M ε k ℓ)⁻¹) =
      fun ℓ => F ε p (ℓ 0) i j * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3 := by
    funext ℓ
    show N p (ℓ 0) i j * ∏ k, (lineDenom (castLoopMatrix fun i => (κ i).dir) (D.mom p) Ms ε k
      ℓ)⁻¹ = _
    rw [hmom p, prod_lineDenom_kinds]
    exact hfac ε hε p ℓ i j
  rw [e, jointEnergyFirstIntegral_two_mul (fun q => F ε p q i j)
    (fun k => ((propDenom mass ε k)⁻¹) ^ 3)]
  generalize (QED.OneLoop.energyFirstIntegral fun k => ((propDenom mass ε k)⁻¹) ^ 3) = A at hne ⊢
  field_simp

/-! ### Five, four and three lines at `q` or `k + q` -/

theorem efi_add {F G : (Fin 4 → ℝ) → ℂ} (hF : EF F) (hG : EF G) :
    QED.OneLoop.energyFirstIntegral (fun q => F q + G q) =
      QED.OneLoop.energyFirstIntegral F + QED.OneLoop.energyFirstIntegral G :=
  QED.TwoLoop.Insertion.energyFirstIntegral_add ⟨hF.1, hF.2⟩ ⟨hG.1, hG.2⟩

theorem isLoopAffine_zk_one (q : Fin 4 → ℝ) (c : Bool) :
    IsLoopAffine fun y : Fin 1 → Fin 4 → ℝ => zk (y 0) c q := by
  cases c
  · exact ⟨![0], q, fun y => by simp [zk]⟩
  · exact ⟨![1], q, fun y => by simp [zk]⟩

theorem zk_mulVec (L : Matrix (Fin 4) (Fin 4) ℝ) (k q : Fin 4 → ℝ) (c : Bool) :
    zk (L *ᵥ k) c (L *ᵥ q) = L *ᵥ zk k c q := by
  cases c <;> simp [zk, Matrix.mulVec_add]

theorem propDenom_mulVec' {L : Matrix (Fin 4) (Fin 4) ℝ} {S S' : Matrix (Fin 4) (Fin 4) ℂ}
    (h : IsSpinLift L S S') (M ε : ℝ) (u : Fin 4 → ℝ) :
    propDenom M ε (L *ᵥ u) = propDenom M ε u := by
  simp only [propDenom, h.dot_mulVec]

theorem upperAct_mul_const (L : Matrix (Fin 4) (Fin 4) ℝ) (X : Fin 4 → Fin 4 → ℂ) (c : ℂ) :
    upperAct L (fun i j => X i j * c) = fun i j => upperAct L X i j * c := by
  funext i j
  simp only [upperAct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- Multiplying a covariant numerator by an invariant denominator keeps it covariant. -/
theorem TCovN.mul_propDenom {N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hN : TCovN N) (M ε : ℝ) (c : Bool) :
    TCovN fun k q i j => N k q i j * propDenom M ε (zk k c q) := by
  intro L S S' h k q
  beta_reduce
  rw [zk_mulVec, propDenom_mulVec' h, hN L S S' h k q, upperAct_mul_const]

theorem prod_five_cons (Ms : Fin 4 → ℝ) (b : Fin 4 → Bool) (ε : ℝ) (k q : Fin 4 → ℝ) :
    ∏ l, (propDenom ((Fin.cons (Ms 0) Ms : Fin 5 → ℝ) l) ε
      (zk k ((Fin.cons (b 0) b : Fin 5 → Bool) l) q))⁻¹ =
      (propDenom (Ms 0) ε (zk k (b 0) q))⁻¹ * ∏ l, (propDenom (Ms l) ε (zk k (b l) q))⁻¹ := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]


section Lines

variable {m₀ : ℝ} (hm₀ : 0 < m₀)
include hm₀

/-- **Five lines at `q` or `k + q`** with masses at least `m₀`: a covariant numerator of degree
four in `q` gives a family with a covariant, null-continuous limit below `-(2 m₀)²`. -/
theorem hasVPLim_five (Ms : Fin 5 → ℝ) (hMs : ∀ i, m₀ ≤ Ms i) (b : Fin 5 → Bool)
    (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 4 fun ℓ => N p (ℓ 0) i j) (hcov : TCovN N)
    {d : ℕ} (hpoly : ∀ q i j, IsLoopPoly 1 d fun y => N (y 0) q i j)
    {h : ℝ → ℂ} {h₀ : ℂ} (hh : Tendsto h (𝓝[>] 0) (𝓝 h₀)) :
    HasVPLim (m₀ + m₀) fun ε k i j => h ε * QED.OneLoop.energyFirstIntegral fun q =>
      N k q i j * ∏ l, (propDenom (Ms l) ε (zk k (b l) q))⁻¹ := by
  have hsq : ∀ l, m₀ ^ 2 ≤ Ms l ^ 2 := fun l => pow_le_pow_left₀ hm₀.le (hMs l) 2
  have hM : ∀ i, m₀ ^ 2 ≤ (![Ms 0, Ms 1, Ms 2, Ms 3, Ms 4, m₀, m₀, m₀] : Fin 8 → ℝ) i ^ 2 := by
    intro i
    fin_cases i <;> first | exact hsq _ | exact le_rfl
  have hout : ∀ c : Bool, kd c ≠ .out := fun c => by cases c <;> decide
  refine hasVPLim_kinds (by norm_num) (kinds5 b) (fun i => by
      fin_cases i <;> simp [kinds5, hout])
    ![Ms 0, Ms 1, Ms 2, Ms 3, Ms 4, m₀, m₀, m₀] hm₀ hm₀ hm₀ (fun i _ => hM i) (fun i _ => hM i)
    (crit_kinds5 b) (by decide) (ne_aux_kinds5 b) N hN hcov hpoly hh _ fun ε _ p ℓ i j => ?_
  rw [Fin.prod_univ_five]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kinds5, Matrix.cons_val_zero,
    Matrix.cons_val_succ, mul_one, zk]
  rcases b 0 <;> rcases b 1 <;> rcases b 2 <;> rcases b 3 <;> rcases b 4 <;>
    simp only [kd, LineKind.lineMom, ite_true, Bool.false_eq_true, ite_false, add_comm p] <;>
    ring

/-- **Four lines**, padded to five with a numerator of degree two. -/
theorem hasVPLim_four (Ms : Fin 4 → ℝ) (hMs : ∀ i, m₀ ≤ Ms i) (b : Fin 4 → Bool)
    (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 2 fun ℓ => N p (ℓ 0) i j) (hcov : TCovN N)
    {d : ℕ} (hpoly : ∀ q i j, IsLoopPoly 1 d fun y => N (y 0) q i j)
    {h : ℝ → ℂ} {h₀ : ℂ} (hh : Tendsto h (𝓝[>] 0) (𝓝 h₀)) :
    HasVPLim (m₀ + m₀) fun ε k i j => h ε * QED.OneLoop.energyFirstIntegral fun q =>
      N k q i j * ∏ l, (propDenom (Ms l) ε (zk k (b l) q))⁻¹ := by
  set Ms' : Fin 5 → ℝ := Fin.cons (Ms 0) Ms
  set b' : Fin 5 → Bool := Fin.cons (b 0) b
  have hMs' : ∀ i, m₀ ≤ Ms' i := fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hMs 0
    · simp only [Ms', Fin.cons_succ]; exact hMs j
  set N' : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ :=
    fun k q i j => N k q i j * propDenom (Ms 0) 0 (zk k (b 0) q)
  have hN' : ∀ p i j, IsLoopPoly 2 4 fun ℓ => N' p (ℓ 0) i j := fun p i j =>
    ((hN p i j).mul ((isLoopAffine_zk p (b 0)).isLoopPoly_propDenom (Ms 0) 0)).mono
      (by norm_num)
  have hN4 : ∀ p i j, IsLoopPoly 2 4 fun ℓ => N p (ℓ 0) i j := fun p i j =>
    (hN p i j).mono (by norm_num)
  have hpoly' : ∀ q i j, IsLoopPoly 1 (d + 2) fun y => N' (y 0) q i j := fun q i j =>
    (hpoly q i j).mul ((isLoopAffine_zk_one q (b 0)).isLoopPoly_propDenom (Ms 0) 0)
  have hε : Tendsto (fun ε : ℝ => h ε * (-(ε : ℂ) * I)) (𝓝[>] 0) (𝓝 (h₀ * (-((0 : ℝ) : ℂ) * I))) :=
    hh.mul ((((continuous_ofReal.neg).mul continuous_const).tendsto 0).mono_left
      nhdsWithin_le_nhds)
  have A := hasVPLim_five hm₀ Ms' hMs' b' N' hN' (hcov.mul_propDenom _ _ _) hpoly' hh
  have B := hasVPLim_five hm₀ Ms' hMs' b' N hN4 hcov hpoly hε
  refine (A.add B).congr fun k _ i j => ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hεp : 0 < ε)
  have e1 : EF fun q => N' k q i j * ∏ l, (propDenom (Ms' l) ε (zk k (b' l) q))⁻¹ :=
    ef_piece5 b' Ms' hεp k (fun q => N' k q i j) (hN' k i j)
  have e2 : EF fun q => (-(ε : ℂ) * I) *
      (N k q i j * ∏ l, (propDenom (Ms' l) ε (zk k (b' l) q))⁻¹) :=
    (ef_piece5 b' Ms' hεp k (fun q => N k q i j) (hN4 k i j)).const_mul (-(ε : ℂ) * I)
  have key : (QED.OneLoop.energyFirstIntegral fun q =>
      N k q i j * ∏ l, (propDenom (Ms l) ε (zk k (b l) q))⁻¹) =
      (QED.OneLoop.energyFirstIntegral fun q =>
        N' k q i j * ∏ l, (propDenom (Ms' l) ε (zk k (b' l) q))⁻¹) +
      (QED.OneLoop.energyFirstIntegral fun q =>
        (-(ε : ℂ) * I) * (N k q i j * ∏ l, (propDenom (Ms' l) ε (zk k (b' l) q))⁻¹)) := by
    rw [← efi_add e1 e2]
    congr 1
    funext q
    have hd := propDenom_ne_zero (M := Ms 0) hεp.ne' (zk k (b 0) q)
    have h0 : propDenom (Ms 0) 0 (zk k (b 0) q) =
        propDenom (Ms 0) ε (zk k (b 0) q) + ε * I := by
      simp only [propDenom]; push_cast; ring
    simp only [Ms', b', prod_five_cons, N', h0]
    field_simp
    ring
  rw [key, QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul]
  ring

/-- **Three lines**, padded to four with a numerator constant in `q`. -/
theorem hasVPLim_three (Ms : Fin 3 → ℝ) (hMs : ∀ i, m₀ ≤ Ms i) (b : Fin 3 → Bool)
    (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 0 fun ℓ => N p (ℓ 0) i j) (hcov : TCovN N)
    {d : ℕ} (hpoly : ∀ q i j, IsLoopPoly 1 d fun y => N (y 0) q i j)
    {h : ℝ → ℂ} {h₀ : ℂ} (hh : Tendsto h (𝓝[>] 0) (𝓝 h₀)) :
    HasVPLim (m₀ + m₀) fun ε k i j => h ε * QED.OneLoop.energyFirstIntegral fun q =>
      N k q i j * ∏ l, (propDenom (Ms l) ε (zk k (b l) q))⁻¹ := by
  set Ms' : Fin 4 → ℝ := Fin.cons (Ms 0) Ms
  set b' : Fin 4 → Bool := Fin.cons (b 0) b
  have hMs' : ∀ i, m₀ ≤ Ms' i := fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hMs 0
    · simp only [Ms', Fin.cons_succ]; exact hMs j
  set N' : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ :=
    fun k q i j => N k q i j * propDenom (Ms 0) 0 (zk k (b 0) q)
  have hN' : ∀ p i j, IsLoopPoly 2 2 fun ℓ => N' p (ℓ 0) i j := fun p i j =>
    ((hN p i j).mul ((isLoopAffine_zk p (b 0)).isLoopPoly_propDenom (Ms 0) 0)).mono
      (by norm_num)
  have hN2 : ∀ p i j, IsLoopPoly 2 2 fun ℓ => N p (ℓ 0) i j := fun p i j =>
    (hN p i j).mono (by norm_num)
  have hpoly' : ∀ q i j, IsLoopPoly 1 (d + 2) fun y => N' (y 0) q i j := fun q i j =>
    (hpoly q i j).mul ((isLoopAffine_zk_one q (b 0)).isLoopPoly_propDenom (Ms 0) 0)
  have hε : Tendsto (fun ε : ℝ => h ε * (-(ε : ℂ) * I)) (𝓝[>] 0) (𝓝 (h₀ * (-((0 : ℝ) : ℂ) * I))) :=
    hh.mul ((((continuous_ofReal.neg).mul continuous_const).tendsto 0).mono_left
      nhdsWithin_le_nhds)
  have A := hasVPLim_four hm₀ Ms' hMs' b' N' hN' (hcov.mul_propDenom _ _ _) hpoly' hh
  have B := hasVPLim_four hm₀ Ms' hMs' b' N hN2 hcov hpoly hε
  refine (A.add B).congr fun k _ i j => ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hεp : 0 < ε)
  have e1 := ef4 k hεp (fun q => N' k q i j) (hN' k i j) (Ms' 0) (Ms' 1) (Ms' 2) (Ms' 3)
    (b' 0) (b' 1) (b' 2) (b' 3)
  have e2 := (ef4 k hεp (fun q => N k q i j) (hN2 k i j) (Ms' 0) (Ms' 1) (Ms' 2) (Ms' 3)
    (b' 0) (b' 1) (b' 2) (b' 3)).const_mul (-(ε : ℂ) * I)
  have e1' : EF fun q => N' k q i j * ∏ l, (propDenom (Ms' l) ε (zk k (b' l) q))⁻¹ :=
    e1.congr fun q => by rw [Fin.prod_univ_four]
  have e2' : EF fun q => (-(ε : ℂ) * I) *
      (N k q i j * ∏ l, (propDenom (Ms' l) ε (zk k (b' l) q))⁻¹) :=
    e2.congr fun q => by rw [Fin.prod_univ_four]
  have key : (QED.OneLoop.energyFirstIntegral fun q =>
      N k q i j * ∏ l, (propDenom (Ms l) ε (zk k (b l) q))⁻¹) =
      (QED.OneLoop.energyFirstIntegral fun q =>
        N' k q i j * ∏ l, (propDenom (Ms' l) ε (zk k (b' l) q))⁻¹) +
      (QED.OneLoop.energyFirstIntegral fun q =>
        (-(ε : ℂ) * I) * (N k q i j * ∏ l, (propDenom (Ms' l) ε (zk k (b' l) q))⁻¹)) := by
    rw [← efi_add e1' e2']
    congr 1
    funext q
    have hd := propDenom_ne_zero (M := Ms 0) hεp.ne' (zk k (b 0) q)
    have h0 : propDenom (Ms 0) 0 (zk k (b 0) q) =
        propDenom (Ms 0) ε (zk k (b 0) q) + ε * I := by
      simp only [propDenom]; push_cast; ring
    rw [Fin.prod_univ_succ (n := 3)]
    simp only [Ms', b', N', Fin.cons_zero, Fin.cons_succ, h0]
    field_simp
    ring
  rw [key, QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul]
  ring

end Lines

end QED.GradedProof.VP2

end
