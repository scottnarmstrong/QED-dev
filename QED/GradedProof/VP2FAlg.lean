/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2ClassG0
public import QED.TwoLoop.IntegrableOrderFiveCt

/-!
# The `δ₂, δ_m` bubble: evenness, divided differences and one-loop pieces

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), step 2, for the classes
`F0`, `F1` (a `δ₂, δ_m` insertion on the one-loop bubble). For one loop flavour of mass `M`, the
integrand is a constant times `N(M) a(M) b(M)²`, `a = D_M(x)⁻¹`, `b = D_M(y)⁻¹` with
`D_M(p) = p² + M² - iε`, and `N(M)` the trace `Tr[A (M - x̸) B (M - y̸)(δ₂ y̸ + δ_m M)(M - y̸)]`.

* `trace_ins_expand`: `N(M) = T₀ + M² T₂ + M⁴ T₄` (the traces of odd numbers of gamma matrices
  vanish, `γ⁵`), with `T₀` of degree `4`, `T₂` of degree `2`, `T₄` constant in the momenta.
* `tri_ins_eq`: for a three-flavour Pauli–Villars set `(M, X, Y)` with the coefficients
  `triA`, `triB`, the flavour sum of `(E₀ + s E₂ + s² E₄) a(s) b(s)²` (`s` the squared mass) is
  `(X² - M²)(Y² - M²)` times the second divided difference, a combination of ten products of
  five inverse denominators (`D_M(y) = V + M²`, `E₀ - V E₂ + V² E₄` with the six products of
  `(a b²)[s₀, s₁, s₂]`, `E₂ - 2 V E₄` with the three of `(a b)[s₀, s₁, s₂]`, and `E₄ a₀ a₁ a₂`).
* `ef_piece5`: a polynomial of degree at most `4` in `q` over five inverse denominators at `q` or
  `q + p` is integrable in both stages of the energy-first integral (`EF`), through the
  auxiliary loop (`QED.TwoLoop.IntegrableOrderFive.energyFirst_of_kinds`).
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.GradedProof.VP2

open QED.TwoLoop.Bridge QED.TwoLoop.CountertermLimit

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-! ### Odd matrices and the evenness of the inserted bubble -/

/-- A matrix anticommuting with `γ⁵`. -/
def IsOddG (X : Mat) : Prop := gamma5 * X * gamma5 = -X

theorem isOddG_gamma (μ : Fin 4) : IsOddG (Dirac.gamma μ) := gamma5_conj_gamma μ

theorem isOddG_slash (p : Fin 4 → ℝ) : IsOddG (Dirac.slash p) := gamma5_conj_slash p

theorem IsOddG.trace5 {A B C D E : Mat} (hA : IsOddG A) (hB : IsOddG B) (hC : IsOddG C)
    (hD : IsOddG D) (hE : IsOddG E) : (A * (B * (C * (D * E)))).trace = 0 := by
  apply trace_eq_zero_of_gamma5_conj
  rw [gamma5_conj_mul, gamma5_conj_mul, gamma5_conj_mul, gamma5_conj_mul, hA, hB, hC, hD, hE]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]

theorem IsOddG.trace3 {A B C : Mat} (hA : IsOddG A) (hB : IsOddG B) (hC : IsOddG C) :
    (A * (B * C)).trace = 0 := by
  apply trace_eq_zero_of_gamma5_conj
  rw [gamma5_conj_mul, gamma5_conj_mul, hA, hB, hC]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]

/-- **The inserted bubble trace is even in the loop mass.** -/
theorem trace_ins_expand {A B X Y : Mat} (hA : IsOddG A) (hB : IsOddG B) (hX : IsOddG X)
    (hY : IsOddG Y) (d₂ dm M : ℂ) :
    (A * (M • 1 - X) * B * (M • 1 - Y) * (d₂ • Y + (dm * M) • 1) * (M • 1 - Y)).trace =
      -d₂ * (A * (X * (B * (Y * (Y * Y))))).trace +
        M ^ 2 * ((dm - 2 * d₂) * (A * (B * (Y * Y))).trace +
          (2 * dm - d₂) * (A * (X * (B * Y))).trace) + M ^ 4 * (dm * (A * B).trace) := by
  have o1 := IsOddG.trace5 hA hB hY hY hY
  have o2 := IsOddG.trace5 hA hX hB hY hY
  have o3 := IsOddG.trace3 hA hX hB
  have o4 := IsOddG.trace3 hA hB hY
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, smul_sub, smul_add, smul_smul]
  rw [o1, o2, o3, o4]
  ring

/-! ### The second divided difference -/

/-- **The three-flavour sum of the inserted bubble as a second divided difference.** -/
theorem tri_ins_eq (U V s0 s1 s2 E0 E2 E4 : ℂ) (h12 : s1 - s2 ≠ 0)
    (ha0 : U + s0 ≠ 0) (ha1 : U + s1 ≠ 0) (ha2 : U + s2 ≠ 0)
    (hb0 : V + s0 ≠ 0) (hb1 : V + s1 ≠ 0) (hb2 : V + s2 ≠ 0) :
    (E0 + s0 * E2 + s0 ^ 2 * E4) * (U + s0)⁻¹ * ((V + s0)⁻¹) ^ 2 +
        (s2 - s0) / (s1 - s2) * ((E0 + s1 * E2 + s1 ^ 2 * E4) * (U + s1)⁻¹ * ((V + s1)⁻¹) ^ 2) +
        (s0 - s1) / (s1 - s2) * ((E0 + s2 * E2 + s2 ^ 2 * E4) * (U + s2)⁻¹ * ((V + s2)⁻¹) ^ 2) =
      (s1 - s0) * (s2 - s0) *
        ((E0 - V * E2 + V ^ 2 * E4) *
            ((U + s0)⁻¹ * (V + s0)⁻¹ * (V + s1)⁻¹ * (V + s2)⁻¹ *
                ((V + s0)⁻¹ + (V + s1)⁻¹ + (V + s2)⁻¹) +
              (U + s0)⁻¹ * (U + s1)⁻¹ * (V + s1)⁻¹ * (V + s2)⁻¹ * ((V + s1)⁻¹ + (V + s2)⁻¹) +
              (U + s0)⁻¹ * (U + s1)⁻¹ * (U + s2)⁻¹ * ((V + s2)⁻¹) ^ 2) +
          (E2 - 2 * V * E4) *
            ((U + s0)⁻¹ * (V + s0)⁻¹ * (V + s1)⁻¹ * (V + s2)⁻¹ +
              (U + s0)⁻¹ * (U + s1)⁻¹ * (V + s1)⁻¹ * (V + s2)⁻¹ +
              (U + s0)⁻¹ * (U + s1)⁻¹ * (U + s2)⁻¹ * (V + s2)⁻¹) +
          E4 * ((U + s0)⁻¹ * (U + s1)⁻¹ * (U + s2)⁻¹)) := by
  field_simp
  ring

/-! ### Both stages of the energy-first integral -/

/-- Both stages of the energy-first integral (D) of a one-loop integrand are integrable. -/
def EF (G : (Fin 4 → ℝ) → ℂ) : Prop :=
  (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ => G (Fin.cons t v)) ∧
    Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ, G (Fin.cons t v)

namespace EF

variable {G H : (Fin 4 → ℝ) → ℂ}

theorem congr (h : EF G) (e : ∀ q, G q = H q) : EF H := by
  have : G = H := funext e
  exact this ▸ h

theorem add (hG : EF G) (hH : EF H) : EF fun q => G q + H q := by
  refine ⟨fun v => (hG.1 v).add (hH.1 v), ?_⟩
  have e : ∀ v : Fin 3 → ℝ, (∫ t : ℝ, G (Fin.cons t v) + H (Fin.cons t v)) =
      (∫ t : ℝ, G (Fin.cons t v)) + ∫ t : ℝ, H (Fin.cons t v) := fun v =>
    integral_add (hG.1 v) (hH.1 v)
  simp only [e]
  exact hG.2.add hH.2

theorem const_mul (hG : EF G) (c : ℂ) : EF fun q => c * G q := by
  refine ⟨fun v => (hG.1 v).const_mul c, ?_⟩
  simp only [integral_const_mul]
  exact hG.2.const_mul c

theorem zero : EF fun _ => 0 := by
  refine ⟨fun _ => integrable_zero _ _ _, ?_⟩
  simp only [integral_zero]
  exact integrable_zero _ _ _

theorem sum {ι : Type*} (s : Finset ι) {G : ι → (Fin 4 → ℝ) → ℂ} (h : ∀ i ∈ s, EF (G i)) :
    EF fun q => ∑ i ∈ s, G i q := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end EF

/-! ### Five one-loop lines -/

/-- A one-loop line kind: `inn` (momentum `p + q`) or `pho` (momentum `q`). -/
def kd (c : Bool) : LineKind := if c then .inn else .pho

theorem lineMom_kd (c : Bool) (p _p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    (kd c).lineMom p _p' ℓ = if c then p + ℓ 0 else ℓ 0 := by
  cases c <;> rfl

/-- The kinds of a five-line piece with its auxiliary loop. -/
def kinds5 (b : Fin 5 → Bool) : Fin 8 → LineKind :=
  ![kd (b 0), kd (b 1), kd (b 2), kd (b 3), kd (b 4), .aux, .aux, .aux]

theorem crit_kinds5 : ∀ b : Fin 5 → Bool,
    QED.Integration.TwoLoop.IntNoSubdivergenceRefined 2 {0, 1, 2, 3}
      fun i => (kinds5 b i).dir := by
  decide

theorem ne_aux_kinds5 : ∀ b : Fin 5 → Bool, ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin 8)),
    kinds5 b e ≠ .aux := by
  decide

/-- **A degree-four numerator over five one-loop lines is integrable in both stages.** -/
theorem ef_piece5 (b : Fin 5 → Bool) (Ms : Fin 5 → ℝ) {ε : ℝ} (hε : 0 < ε) (p : Fin 4 → ℝ)
    (N : (Fin 4 → ℝ) → ℂ) (hN : IsLoopPoly 2 4 fun ℓ => N (ℓ 0)) :
    EF fun q => N q * ∏ i, (propDenom (Ms i) ε (if b i then p + q else q))⁻¹ := by
  refine QED.TwoLoop.IntegrableOrderFive.energyFirst_of_kinds (by norm_num) (kinds5 b)
    ![Ms 0, Ms 1, Ms 2, Ms 3, Ms 4, 1, 1, 1] 1 hε p 0 (crit_kinds5 b) (by decide)
    (ne_aux_kinds5 b) N hN
    (fun q => N q * ∏ i, (propDenom (Ms i) ε (if b i then p + q else q))⁻¹) fun ℓ => ?_
  rw [Fin.prod_univ_five]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kinds5, Matrix.cons_val_zero,
    Matrix.cons_val_succ, mul_one]
  rcases b 0 <;> rcases b 1 <;> rcases b 2 <;> rcases b 3 <;> rcases b 4 <;>
    simp only [kd, LineKind.lineMom, ite_true,
      Bool.false_eq_true, ite_false, add_comm p] <;> ring

/-! ### Five lines at `q` or `k + q` -/

/-- The momentum `k + q` (`c = true`) or `q` (`c = false`). -/
def zk (k : Fin 4 → ℝ) (c : Bool) (q : Fin 4 → ℝ) : Fin 4 → ℝ := if c then k + q else q

theorem isLoopAffine_zk (k : Fin 4 → ℝ) (c : Bool) :
    IsLoopAffine fun ℓ : Fin 2 → Fin 4 → ℝ => zk k c (ℓ 0) := by
  refine (congrArg IsLoopAffine (funext fun ℓ => ?_)).mp
    (isLoopAffine_affine ![1, 0] (if c then k else 0))
  cases c <;> simp [zk, add_comm]

/-- `ef_piece5` with the five factors written out. -/
theorem ef5 (k : Fin 4 → ℝ) {ε : ℝ} (hε : 0 < ε) (N : (Fin 4 → ℝ) → ℂ)
    (hN : IsLoopPoly 2 4 fun ℓ => N (ℓ 0)) (m0 m1 m2 m3 m4 : ℝ) (c0 c1 c2 c3 c4 : Bool) :
    EF fun q => N q * ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
      (propDenom m2 ε (zk k c2 q))⁻¹ * (propDenom m3 ε (zk k c3 q))⁻¹ *
      (propDenom m4 ε (zk k c4 q))⁻¹) := by
  refine (ef_piece5 ![c0, c1, c2, c3, c4] ![m0, m1, m2, m3, m4] hε k N hN).congr fun q => ?_
  rw [Fin.prod_univ_five]
  simp only [zk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  rfl

/-- Four lines and a numerator of degree at most `2` (pad one line). -/
theorem ef4 (k : Fin 4 → ℝ) {ε : ℝ} (hε : 0 < ε) (N : (Fin 4 → ℝ) → ℂ)
    (hN : IsLoopPoly 2 2 fun ℓ => N (ℓ 0)) (m0 m1 m2 m3 : ℝ) (c0 c1 c2 c3 : Bool) :
    EF fun q => N q * ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
      (propDenom m2 ε (zk k c2 q))⁻¹ * (propDenom m3 ε (zk k c3 q))⁻¹) := by
  have hP := (isLoopAffine_zk k c0).isLoopPoly_propDenom m0 ε
  refine (ef5 k hε (fun q => N q * propDenom m0 ε (zk k c0 q)) ((hN.mul hP).mono (by norm_num))
    m0 m0 m1 m2 m3 c0 c0 c1 c2 c3).congr fun q => ?_
  have h := mul_inv_cancel₀ (propDenom_ne_zero (M := m0) hε.ne' (zk k c0 q))
  linear_combination (N q * ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
    (propDenom m2 ε (zk k c2 q))⁻¹ * (propDenom m3 ε (zk k c3 q))⁻¹)) * h

/-- Three lines and a numerator constant in the momenta (pad two lines). -/
theorem ef3 (k : Fin 4 → ℝ) {ε : ℝ} (hε : 0 < ε) (N : (Fin 4 → ℝ) → ℂ)
    (hN : IsLoopPoly 2 0 fun ℓ => N (ℓ 0)) (m0 m1 m2 : ℝ) (c0 c1 c2 : Bool) :
    EF fun q => N q * ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
      (propDenom m2 ε (zk k c2 q))⁻¹) := by
  have hP := (isLoopAffine_zk k c0).isLoopPoly_propDenom m0 ε
  refine (ef4 k hε (fun q => N q * propDenom m0 ε (zk k c0 q)) ((hN.mul hP).mono (by norm_num))
    m0 m0 m1 m2 c0 c0 c1 c2).congr fun q => ?_
  have h := mul_inv_cancel₀ (propDenom_ne_zero (M := m0) hε.ne' (zk k c0 q))
  linear_combination (N q * ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
    (propDenom m2 ε (zk k c2 q))⁻¹)) * h

/-! ### The inserted bubble at three masses -/

theorem propDenom_eq_add (M ε : ℝ) (p : Fin 4 → ℝ) :
    propDenom M ε p = propDenom 0 ε p + (M : ℂ) ^ 2 := by
  simp only [propDenom]
  push_cast
  ring

/-- The trace `Tr[A (M - x̸) B (M - y̸)(δ₂ y̸ + δ_m M)(M - y̸)]` of the inserted bubble. -/
noncomputable def insTr (A B : Mat) (d₂ dm M : ℝ) (x y : Fin 4 → ℝ) : ℂ :=
  (A * electronNumerator M x * B * electronNumerator M y *
    QED.TwoLoop.Insertion.fermionCtMatrix d₂ dm M y * electronNumerator M y).trace

/-- The inserted bubble of mass `M` without its constant. -/
noncomputable def insG (A B : Mat) (d₂ dm M ε : ℝ) (x y : Fin 4 → ℝ) : ℂ :=
  insTr A B d₂ dm M x y * (propDenom M ε x)⁻¹ * ((propDenom M ε y)⁻¹) ^ 2

/-- The `M`-independent part `T₀` of the inserted bubble trace. -/
noncomputable def insT0 (A B : Mat) (d₂ : ℝ) (x y : Fin 4 → ℝ) : ℂ :=
  -(d₂ : ℂ) * (A * (Dirac.slash x * (B * (Dirac.slash y * (Dirac.slash y * Dirac.slash y))))).trace

/-- The coefficient `T₂` of `M²` in the inserted bubble trace. -/
noncomputable def insT2 (A B : Mat) (d₂ dm : ℝ) (x y : Fin 4 → ℝ) : ℂ :=
  ((dm : ℂ) - 2 * d₂) * (A * (B * (Dirac.slash y * Dirac.slash y))).trace +
    (2 * (dm : ℂ) - d₂) * (A * (Dirac.slash x * (B * Dirac.slash y))).trace

/-- The coefficient `T₄` of `M⁴` in the inserted bubble trace. -/
noncomputable def insT4 (A B : Mat) (dm : ℝ) : ℂ := (dm : ℂ) * (A * B).trace

theorem insTr_eq {A B : Mat} (hA : IsOddG A) (hB : IsOddG B) (d₂ dm M : ℝ) (x y : Fin 4 → ℝ) :
    insTr A B d₂ dm M x y = insT0 A B d₂ x y + ((M : ℂ) ^ 2) * insT2 A B d₂ dm x y +
      ((M : ℂ) ^ 2) ^ 2 * insT4 A B dm := by
  have h := trace_ins_expand hA hB (isOddG_slash x) (isOddG_slash y) d₂ dm M
  unfold insTr insT0 insT2 insT4
  rw [show electronNumerator M x = (M : ℂ) • 1 - Dirac.slash x from rfl,
    show electronNumerator M y = (M : ℂ) • 1 - Dirac.slash y from rfl,
    show QED.TwoLoop.Insertion.fermionCtMatrix d₂ dm M y =
      (d₂ : ℂ) • Dirac.slash y + ((dm : ℂ) * M) • 1 by
        simp only [QED.TwoLoop.Insertion.fermionCtMatrix]; push_cast; rfl, h]
  ring

theorem isLoopPolyMat_slash {F : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ} (hF : IsLoopAffine F) :
    IsLoopPolyMat 2 1 fun ℓ => Dirac.slash (F ℓ) := fun i j => by
  have h := (hF.isLoopPolyMat_electronNumerator 0 i j).const_mul (-1)
  refine (congrArg (IsLoopPoly 2 1) (funext fun ℓ => ?_)).mp h
  simp [electronNumerator]

section Poly

variable {A B : Mat} {x y : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ}

theorem isLoopPoly_insT0 (hx : IsLoopAffine x) (hy : IsLoopAffine y) (d₂ : ℝ) :
    IsLoopPoly 2 4 fun ℓ => insT0 A B d₂ (x ℓ) (y ℓ) := by
  have h := (((IsLoopPolyMat.const A).mul ((isLoopPolyMat_slash hx).mul
    ((IsLoopPolyMat.const B).mul ((isLoopPolyMat_slash hy).mul ((isLoopPolyMat_slash hy).mul
      (isLoopPolyMat_slash hy))))))).trace.const_mul (-(d₂ : ℂ))
  exact h.mono (by norm_num)

theorem isLoopPoly_insT2 (hx : IsLoopAffine x) (hy : IsLoopAffine y) (d₂ dm : ℝ) :
    IsLoopPoly 2 2 fun ℓ => insT2 A B d₂ dm (x ℓ) (y ℓ) := by
  have h1 := (((IsLoopPolyMat.const A).mul ((IsLoopPolyMat.const B).mul
    ((isLoopPolyMat_slash hy).mul (isLoopPolyMat_slash hy))))).trace.const_mul
      ((dm : ℂ) - 2 * d₂)
  have h2 := (((IsLoopPolyMat.const A).mul ((isLoopPolyMat_slash hx).mul
    ((IsLoopPolyMat.const B).mul (isLoopPolyMat_slash hy))))).trace.const_mul
      (2 * (dm : ℂ) - d₂)
  exact (h1.mono (by norm_num)).add (h2.mono (by norm_num))

end Poly

/-- **Both stages for one three-flavour set of the inserted bubble.** -/
theorem ef_insTriple {A B : Mat} (hA : IsOddG A) (hB : IsOddG B) (d₂ dm M X Y : ℝ)
    (hXY : X ^ 2 - Y ^ 2 ≠ 0) {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) (bx bY : Bool) :
    EF fun q => insG A B d₂ dm M ε (zk k bx q) (zk k bY q) +
      (triA M X Y : ℂ) * insG A B d₂ dm X ε (zk k bx q) (zk k bY q) +
      (triB M X Y : ℂ) * insG A B d₂ dm Y ε (zk k bx q) (zk k bY q) := by
  have hε' : ε ≠ 0 := hε.ne'
  have h12 : (X : ℂ) ^ 2 - (Y : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hXY
  have hA' : (triA M X Y : ℂ) =
      ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2) := by
    simp only [triA]; push_cast; rfl
  have hB' : (triB M X Y : ℂ) =
      ((M : ℂ) ^ 2 - (X : ℂ) ^ 2) / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2) := by
    simp only [triB]; push_cast; rfl
  have hxA := isLoopAffine_zk k bx
  have hyA := isLoopAffine_zk k bY
  -- the numerators
  set E0 : (Fin 4 → ℝ) → ℂ := fun q => insT0 A B d₂ (zk k bx q) (zk k bY q) -
    propDenom 0 ε (zk k bY q) * insT2 A B d₂ dm (zk k bx q) (zk k bY q) +
    propDenom 0 ε (zk k bY q) * propDenom 0 ε (zk k bY q) * insT4 A B dm with hE0
  set E2 : (Fin 4 → ℝ) → ℂ := fun q => insT2 A B d₂ dm (zk k bx q) (zk k bY q) -
    2 * propDenom 0 ε (zk k bY q) * insT4 A B dm with hE2
  set E4 : (Fin 4 → ℝ) → ℂ := fun _ => insT4 A B dm with hE4
  have hV := hyA.isLoopPoly_propDenom 0 ε
  have hU := hxA.isLoopPoly_propDenom M ε
  have hT0 := isLoopPoly_insT0 (A := A) (B := B) hxA hyA d₂
  have hT2 := isLoopPoly_insT2 (A := A) (B := B) hxA hyA d₂ dm
  have hT4 : IsLoopPoly 2 0 fun _ : Fin 2 → Fin 4 → ℝ => insT4 A B dm := IsLoopPoly.const _
  have p0 : IsLoopPoly 2 4 fun ℓ => E0 (ℓ 0) :=
    (hT0.sub ((hV.mul hT2).mono (n' := 4) (by norm_num))).add
      (((hV.mul hV).mul hT4).mono (n' := 4) (by norm_num))
  have p2 : IsLoopPoly 2 2 fun ℓ => E2 (ℓ 0) :=
    hT2.sub ((((IsLoopPoly.const (n := 0) (2 : ℂ)).mul hV).mul hT4).mono (n' := 2)
      (by norm_num))
  have p4 : IsLoopPoly 2 0 fun ℓ => E4 (ℓ 0) := hT4
  have K := fun (N : (Fin 4 → ℝ) → ℂ) (hN : IsLoopPoly 2 4 fun ℓ => N (ℓ 0)) => ef5 k hε N hN
  -- the ten pieces
  have e1 := K E0 p0 M M X Y M bx bY bY bY bY
  have e2 := K E0 p0 M M X Y X bx bY bY bY bY
  have e3 := K E0 p0 M M X Y Y bx bY bY bY bY
  have e4 := K E0 p0 M X X Y X bx bx bY bY bY
  have e5 := K E0 p0 M X X Y Y bx bx bY bY bY
  have e6 := K E0 p0 M X Y Y Y bx bx bx bY bY
  have e7 := ef4 k hε E2 p2 M M X Y bx bY bY bY
  have e8 := ef4 k hε E2 p2 M X X Y bx bx bY bY
  have e9 := ef4 k hε E2 p2 M X Y Y bx bx bx bY
  have e10 := ef3 k hε E4 p4 M X Y bx bx bx
  have hsum := ((((((((((e1.add e2).add e3).add e4).add e5).add e6).add e7).add e8).add e9).add
    e10).const_mul (((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2)))
  refine hsum.congr fun q => ?_
  have hd : ∀ (m : ℝ) (c : Bool), propDenom 0 ε (zk k c q) + (m : ℂ) ^ 2 ≠ 0 := fun m c => by
    rw [← propDenom_eq_add]
    exact propDenom_ne_zero hε' _
  simp only [insG, insTr_eq hA hB]
  rw [propDenom_eq_add M ε (zk k bx q), propDenom_eq_add X ε (zk k bx q),
    propDenom_eq_add Y ε (zk k bx q), propDenom_eq_add M ε (zk k bY q),
    propDenom_eq_add X ε (zk k bY q), propDenom_eq_add Y ε (zk k bY q), hA', hB']
  rw [tri_ins_eq _ _ _ _ _ _ _ _ h12 (hd M bx) (hd X bx) (hd Y bx) (hd M bY) (hd X bY) (hd Y bY)]
  simp only [E0, E2, E4]
  ring

/-- **Both stages for the block-summed inserted bubble.** -/
theorem ef_insBubble {A B : Mat} (hA : IsOddG A) (hB : IsOddG B) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F) (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (d₂ dm : F → ℝ) {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) (bx bY : Bool) (K : ℂ) :
    EF fun q => ∑ f, (Φ.coeff f : ℂ) *
      (K * insG A B (d₂ (rep f)) (dm (rep f)) (Φ.mass f) ε (zk k bx q) (zk k bY q)) := by
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  set X : ℝ := 1 + ∑ g, Φ.mass g with hX
  have hX0 : 0 < X := by
    have := Finset.sum_nonneg (s := Finset.univ) fun g _ => (hpos g).le
    linarith
  have hXY : X ^ 2 - (X + 1) ^ 2 ≠ 0 := by nlinarith
  refine (EF.sum Finset.univ fun f _ =>
    (ef_insTriple hA hB (d₂ (rep f)) (dm (rep f)) (Φ.mass f) X (X + 1) hXY hε k bx bY).const_mul
      ((Φ.coeff f : ℂ) * K)).congr fun q => ?_
  rw [sum_block_eq_sum_triple Φ rep hrep hPV₁ hPV₂ X (X + 1)
    (fun r M => K * insG A B (d₂ r) (dm r) M ε (zk k bx q) (zk k bY q))]
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

end QED.GradedProof.VP2

end
