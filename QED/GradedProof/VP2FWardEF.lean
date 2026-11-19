/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2LimF
public import QED.GradedProof.SE2TwoLoopGggg

/-!
# Two-line one-loop pieces with a cubic numerator: both stages of the energy-first integral

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2, the Ward step of
the classes `F0`, `F1`. The Ward identity for the inserted bubbles produces one-loop integrands
with two propagators and a numerator `E₀ + M² E₂` of degree three (`E₀`) and one (`E₂`) in the
loop momentum (the tadpole-like trace `Tr[γ^ν S X S]` and the bubble). Their block sums are
integrable in both stages of the energy-first integral (D):

* `ef_piece4c`, `ef4c`: four one-loop lines and a cubic numerator, through an auxiliary loop of
  three lines (seven lines in all, the cubic criterion
  `QED.Integration.TwoLoop.jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_cubic`
  with three numerator lines, `refinedBound_of_dependsOnZero_cubic`); `ef3l`: three lines and
  a linear numerator (pad one line);
* `tri_two_eq`: the three-flavour sum of `(E₀ + s E₂)/((U + s)(V + s))` as a second divided
  difference;
* `ef_twoTriple`, `ef_twoBlock`: both stages for one three-flavour set and for a block sum.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology

namespace QED.GradedProof.VP2

open QED.Integration QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge

/-! ### A growth bound for cubic numerators -/

/-- A crude growth bound for a polynomial of degree at most three. -/
theorem exists_norm_evalC_le_cubic (Q : LoopQuartic) (hq : Q.quart = 0) :
    ∃ C, 0 ≤ C ∧ ∀ X : LoopIndex → ℂ, ‖Q.evalC X‖ ≤ C * (1 + ‖X‖) ^ 3 := by
  refine ⟨‖Q.const‖ + ∑ a, ‖Q.lin a‖ + ∑ a, ∑ b, ‖Q.quad a b‖ +
    ∑ a, ∑ b, ∑ c, ‖Q.cub a b c‖, by positivity, fun X => ?_⟩
  set r := 1 + ‖X‖ with hr_def
  have hr : 1 ≤ r := le_add_of_nonneg_right (norm_nonneg _)
  have hr0 : 0 ≤ r := by linarith
  have hX : ∀ a, ‖X a‖ ≤ r := fun a => (norm_le_pi_norm X a).trans (by linarith)
  have hr1 : r ≤ r ^ 3 := le_self_pow₀ hr (by norm_num)
  have hr2 : r ^ 2 ≤ r ^ 3 := pow_le_pow_right₀ hr (by norm_num)
  have hr4 : 1 ≤ r ^ 3 := one_le_pow₀ hr
  have t0 : ‖Q.const‖ ≤ ‖Q.const‖ * r ^ 3 := le_mul_of_one_le_right (norm_nonneg _) hr4
  have t1 : ‖∑ a, Q.lin a * X a‖ ≤ (∑ a, ‖Q.lin a‖) * r ^ 3 := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((hX a).trans hr1) (norm_nonneg _)
  have t2 : ‖∑ a, ∑ b, Q.quad a b * (X a * X b)‖ ≤ (∑ a, ∑ b, ‖Q.quad a b‖) * r ^ 3 := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖X a‖ * ‖X b‖ ≤ r * r := mul_le_mul (hX a) (hX b) (norm_nonneg _) hr0
      _ = r ^ 2 := by ring
      _ ≤ r ^ 3 := hr2
  have t3 : ‖∑ a, ∑ b, ∑ c, Q.cub a b c * (X a * X b * X c)‖ ≤
      (∑ a, ∑ b, ∑ c, ‖Q.cub a b c‖) * r ^ 3 := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [norm_mul, norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖X a‖ * ‖X b‖ * ‖X c‖ ≤ r * r * r :=
          mul_le_mul (mul_le_mul (hX a) (hX b) (norm_nonneg _) hr0) (hX c) (norm_nonneg _)
            (by positivity)
      _ = r ^ 3 := by ring
  unfold LoopQuartic.evalC
  simp only [hq, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  have e2 := norm_add_le (Q.const + ∑ a, Q.lin a * X a + ∑ a, ∑ b, Q.quad a b * (X a * X b))
    (∑ a, ∑ b, ∑ c, Q.cub a b c * (X a * X b * X c))
  have e3 := norm_add_le (Q.const + ∑ a, Q.lin a * X a) (∑ a, ∑ b, Q.quad a b * (X a * X b))
  have e4 := norm_add_le Q.const (∑ a, Q.lin a * X a)
  nlinarith

/-- **The pointwise bound for a cubic numerator depending only on `ℓ₀`**: if `Q(ℓ) = Q(ℓ₀, 0)`
and `E` consists of three lines of loop direction `(1, 0)`, then `Q` satisfies the refined bound
of exponent four for `E`. -/
theorem refinedBound_of_dependsOnZero_cubic {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    {E : Finset (Fin (m + 1))} (hE : E.card = 3) (hα : ∀ e ∈ E, α e = ![1, 0])
    (Q : LoopQuartic) (hq : Q.quart = 0) (hQ : ∀ ℓ, Q.eval ℓ = Q.eval ![ℓ 0, 0]) :
    RefinedBound α E 4 Q.eval := by
  obtain ⟨e₀, he₀⟩ : E.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨C, hC, hQC⟩ := exists_norm_evalC_le_cubic Q hq
  have hν : ∀ ν : Fin 4, ∃ Cν : ℝ, 0 ≤ Cν ∧ ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A.PosDef →
      ∀ ℓ : Fin 2 → Fin 4 → ℝ,
        |ℓ 0 ν| ≤ Cν * lineWeight α {e₀} A * Real.sqrt (1 + loopNorm A ℓ) := by
    intro ν
    obtain ⟨Cν, hCν, h⟩ := refinedBound_lineMomentum α (fun _ => 0) e₀ ν
    refine ⟨Cν, hCν, fun A hA ℓ => ?_⟩
    have h1 := h A hA ℓ
    have hl : lineMomentum α (fun _ => 0) e₀ ℓ ν = ℓ 0 ν := by
      simp [lineMomentum, hα e₀ he₀, Fin.sum_univ_two]
    simp only at h1
    rwa [hl, norm_real, Real.norm_eq_abs, pow_one] at h1
  choose Cν hCν hbound using hν
  set K := 1 + ∑ ν, Cν ν with hK
  have hK0 : 0 ≤ ∑ ν, Cν ν := Finset.sum_nonneg fun ν _ => hCν ν
  refine ⟨C * K ^ 3, by positivity, fun A hA ℓ => ?_⟩
  set w := Real.sqrt (1 + α e₀ ⬝ᵥ Matrix.mulVec A⁻¹ (α e₀)) with hw
  have hw1 : 1 ≤ w := one_le_sqrt_lineFactor α hA e₀
  have hs1 := sqrt_one_add_loopNorm_one_le hA ℓ
  set s := Real.sqrt (1 + loopNorm A ℓ) with hs
  have hlw : lineWeight α {e₀} A = w := lineWeight_singleton α e₀ A
  have hLW : lineWeight α E A = w ^ 3 := by
    unfold lineWeight
    rw [Finset.prod_congr rfl (fun e he => by rw [hα e he, ← hα e₀ he₀]), Finset.prod_const, hE]
  have hX : ‖loopComp ![ℓ 0, 0]‖ ≤ (∑ ν, Cν ν) * w * s := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_
    obtain ⟨i, ν⟩ := a
    fin_cases i
    · simp only [loopComp, Fin.zero_eta, Matrix.cons_val_zero, norm_real, Real.norm_eq_abs]
      calc |ℓ 0 ν| ≤ Cν ν * w * s := by rw [← hlw]; exact hbound ν A hA ℓ
        _ ≤ (∑ ν, Cν ν) * w * s := by
          gcongr
          exact Finset.single_le_sum (f := Cν) (fun ν _ => hCν ν) (Finset.mem_univ ν)
    · simp only [loopComp, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Pi.zero_apply, ofReal_zero, norm_zero]
      positivity
  have hws : 1 ≤ w * s := one_le_mul_of_one_le_of_one_le hw1 hs1
  have h1X : 1 + ‖loopComp ![ℓ 0, 0]‖ ≤ K * (w * s) := by nlinarith
  have hs4 : s ^ 3 ≤ s ^ 4 := pow_le_pow_right₀ hs1 (by norm_num)
  rw [hQ ℓ, LoopQuartic.eval]
  calc ‖Q.evalC (loopComp ![ℓ 0, 0])‖ ≤ C * (1 + ‖loopComp ![ℓ 0, 0]‖) ^ 3 := hQC _
    _ ≤ C * (K * (w * s)) ^ 3 := by gcongr
    _ = C * K ^ 3 * w ^ 3 * s ^ 3 := by ring
    _ ≤ C * K ^ 3 * w ^ 3 * s ^ 4 := by gcongr
    _ = C * K ^ 3 * lineWeight α E A * s ^ 4 := by rw [hLW]

/-! ### Four lines and a cubic numerator -/

/-- The kinds of a four-line piece with its auxiliary loop of three lines. -/
def kinds4c (b : Fin 4 → Bool) : Fin 7 → LineKind :=
  ![kd (b 0), kd (b 1), kd (b 2), kd (b 3), .aux, .aux, .aux]

theorem crit_kinds4c : ∀ b : Fin 4 → Bool,
    QED.Integration.TwoLoop.IntNoSubdivergenceRefined 2 {0, 1, 2}
      fun i => (kinds4c b i).dir := by
  decide

theorem ne_aux_kinds4c : ∀ b : Fin 4 → Bool, ∀ e ∈ ({0, 1, 2} : Finset (Fin 7)),
    kinds4c b e ≠ .aux := by
  decide

/-- **A cubic numerator over four one-loop lines is integrable in both stages.** -/
theorem ef_piece4c (b : Fin 4 → Bool) (Ms : Fin 4 → ℝ) {ε : ℝ} (hε : 0 < ε) (p : Fin 4 → ℝ)
    (N : (Fin 4 → ℝ) → ℂ) (hN : IsLoopPoly 2 3 fun ℓ => N (ℓ 0)) :
    EF fun q => N q * ∏ i, (propDenom (Ms i) ε (if b i then p + q else q))⁻¹ := by
  obtain ⟨Q, hq, hQ⟩ := QED.GradedProof.SE2.IsLoopPoly.exists_loopQuartic_cubic hN
  have hα : ∀ e ∈ ({0, 1, 2} : Finset (Fin 7)),
      (castLoopMatrix fun i => (kinds4c b i).dir) e = ![1, 0] := by
    intro e he
    have h := ne_aux_kinds4c b e he
    funext s
    rcases hk : kinds4c b e with _ | _ | _ | _
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · exact absurd hk h
  have hB : RefinedBound (castLoopMatrix fun i => (kinds4c b i).dir) {0, 1, 2} 4 Q.eval :=
    refinedBound_of_dependsOnZero_cubic _ (by decide) hα Q hq fun ℓ => by
      simp only [hQ, Matrix.cons_val_zero]
  have hJ := jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_cubic Q
    (castLoopMatrix fun i => (kinds4c b i).dir) (fun i => (kinds4c b i).mom p p)
    ![Ms 0, Ms 1, Ms 2, Ms 3, 1, 1, 1] hq (le_refl 6) hε
    ((noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr (crit_kinds4c b)) hB
  have hfun : (fun ℓ : Fin 2 → Fin 4 → ℝ => Q.eval ℓ * ∏ i,
      (lineDenom (castLoopMatrix fun i => (kinds4c b i).dir) (fun i => (kinds4c b i).mom p p)
        ![Ms 0, Ms 1, Ms 2, Ms 3, 1, 1, 1] ε i ℓ)⁻¹) =
      fun ℓ => (N (ℓ 0) * ∏ i, (propDenom (Ms i) ε (if b i then p + ℓ 0 else ℓ 0))⁻¹) *
        ((propDenom 1 ε (ℓ 1))⁻¹) ^ 3 := by
    funext ℓ
    rw [hQ, prod_lineDenom_kinds, Fin.prod_univ_four]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kinds4c, Matrix.cons_val_zero,
      Matrix.cons_val_succ, mul_one]
    rcases b 0 <;> rcases b 1 <;> rcases b 2 <;> rcases b 3 <;>
      simp only [kd, LineKind.lineMom, ite_true, Bool.false_eq_true, ite_false] <;> ring
  rw [hfun] at hJ
  obtain ⟨h1, h2⟩ :=
    QED.TwoLoop.IntegrableOrderFive.energyFirst_of_jointEnergyFirstIntegrable_mul_aux
      (F := fun q => N q * ∏ i, (propDenom (Ms i) ε (if b i then p + q else q))⁻¹) 1 hε hJ
  exact ⟨h1, h2⟩

/-- `ef_piece4c` with the four factors written out. -/
theorem ef4c (k : Fin 4 → ℝ) {ε : ℝ} (hε : 0 < ε) (N : (Fin 4 → ℝ) → ℂ)
    (hN : IsLoopPoly 2 3 fun ℓ => N (ℓ 0)) (m0 m1 m2 m3 : ℝ) (c0 c1 c2 c3 : Bool) :
    EF fun q => N q * ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
      (propDenom m2 ε (zk k c2 q))⁻¹ * (propDenom m3 ε (zk k c3 q))⁻¹) := by
  refine (ef_piece4c ![c0, c1, c2, c3] ![m0, m1, m2, m3] hε k N hN).congr fun q => ?_
  rw [Fin.prod_univ_four]
  simp only [zk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  rfl

/-- Three lines and a numerator of degree at most `1` (pad one line). -/
theorem ef3l (k : Fin 4 → ℝ) {ε : ℝ} (hε : 0 < ε) (N : (Fin 4 → ℝ) → ℂ)
    (hN : IsLoopPoly 2 1 fun ℓ => N (ℓ 0)) (m0 m1 m2 : ℝ) (c0 c1 c2 : Bool) :
    EF fun q => N q * ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
      (propDenom m2 ε (zk k c2 q))⁻¹) := by
  have hP := (isLoopAffine_zk k c0).isLoopPoly_propDenom m0 ε
  refine (ef4c k hε (fun q => N q * propDenom m0 ε (zk k c0 q)) ((hN.mul hP).mono (by norm_num))
    m0 m0 m1 m2 c0 c0 c1 c2).congr fun q => ?_
  have h := mul_inv_cancel₀ (propDenom_ne_zero (M := m0) hε.ne' (zk k c0 q))
  linear_combination (N q * ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
    (propDenom m2 ε (zk k c2 q))⁻¹)) * h

/-! ### The two-line form and its second divided difference -/

/-- **The three-flavour sum of `(E₀ + s E₂)/((U + s)(V + s))` as a second divided difference.** -/
theorem tri_two_eq (U V s0 s1 s2 E0 E2 : ℂ) (h12 : s1 - s2 ≠ 0)
    (ha0 : U + s0 ≠ 0) (ha1 : U + s1 ≠ 0) (ha2 : U + s2 ≠ 0)
    (hb0 : V + s0 ≠ 0) (hb1 : V + s1 ≠ 0) (hb2 : V + s2 ≠ 0) :
    (E0 + s0 * E2) * (U + s0)⁻¹ * (V + s0)⁻¹ +
        (s2 - s0) / (s1 - s2) * ((E0 + s1 * E2) * (U + s1)⁻¹ * (V + s1)⁻¹) +
        (s0 - s1) / (s1 - s2) * ((E0 + s2 * E2) * (U + s2)⁻¹ * (V + s2)⁻¹) =
      (s1 - s0) * (s2 - s0) *
        ((E0 - U * E2) *
            ((U + s0)⁻¹ * (V + s0)⁻¹ * (V + s1)⁻¹ * (V + s2)⁻¹ +
              (U + s0)⁻¹ * (U + s1)⁻¹ * (V + s1)⁻¹ * (V + s2)⁻¹ +
              (U + s0)⁻¹ * (U + s1)⁻¹ * (U + s2)⁻¹ * (V + s2)⁻¹) +
          E2 * ((V + s0)⁻¹ * (V + s1)⁻¹ * (V + s2)⁻¹)) := by
  field_simp
  ring

/-- The two-line integrand `(E₀ + M² E₂) / ((x² + M² - iε)(y² + M² - iε))`. -/
noncomputable def tw (E0 E2 : ℂ) (M ε : ℝ) (x y : Fin 4 → ℝ) : ℂ :=
  (E0 + (M : ℂ) ^ 2 * E2) * (propDenom M ε x)⁻¹ * (propDenom M ε y)⁻¹

/-- **Both stages for one three-flavour set of the two-line form.** -/
theorem ef_twoTriple (k : Fin 4 → ℝ) {ε : ℝ} (hε : 0 < ε) (E0 E2 : (Fin 4 → ℝ) → ℂ)
    (h0 : IsLoopPoly 2 3 fun ℓ => E0 (ℓ 0)) (h2 : IsLoopPoly 2 1 fun ℓ => E2 (ℓ 0))
    (M X Y : ℝ) (hXY : X ^ 2 - Y ^ 2 ≠ 0) (bx bY : Bool) :
    EF fun q => tw (E0 q) (E2 q) M ε (zk k bx q) (zk k bY q) +
      (triA M X Y : ℂ) * tw (E0 q) (E2 q) X ε (zk k bx q) (zk k bY q) +
      (triB M X Y : ℂ) * tw (E0 q) (E2 q) Y ε (zk k bx q) (zk k bY q) := by
  have hε' : ε ≠ 0 := hε.ne'
  have h12 : (X : ℂ) ^ 2 - (Y : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hXY
  have hA' : (triA M X Y : ℂ) =
      ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2) := by
    simp only [triA]; push_cast; rfl
  have hB' : (triB M X Y : ℂ) =
      ((M : ℂ) ^ 2 - (X : ℂ) ^ 2) / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2) := by
    simp only [triB]; push_cast; rfl
  have hU := (isLoopAffine_zk k bx).isLoopPoly_propDenom 0 ε
  set N0 : (Fin 4 → ℝ) → ℂ := fun q => E0 q - propDenom 0 ε (zk k bx q) * E2 q with hN0
  have p0 : IsLoopPoly 2 3 fun ℓ => N0 (ℓ 0) := h0.sub ((hU.mul h2).mono (by norm_num))
  have e1 := ef4c k hε N0 p0 M M X Y bx bY bY bY
  have e2 := ef4c k hε N0 p0 M X X Y bx bx bY bY
  have e3 := ef4c k hε N0 p0 M X Y Y bx bx bx bY
  have e4 := ef3l k hε E2 h2 M X Y bY bY bY
  have hsum := (((e1.add e2).add e3).add e4).const_mul
    (((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2))
  refine hsum.congr fun q => ?_
  have hd : ∀ (m : ℝ) (c : Bool), propDenom 0 ε (zk k c q) + (m : ℂ) ^ 2 ≠ 0 := fun m c => by
    rw [← propDenom_eq_add]
    exact propDenom_ne_zero hε' _
  simp only [tw]
  rw [propDenom_eq_add M ε (zk k bx q), propDenom_eq_add X ε (zk k bx q),
    propDenom_eq_add Y ε (zk k bx q), propDenom_eq_add M ε (zk k bY q),
    propDenom_eq_add X ε (zk k bY q), propDenom_eq_add Y ε (zk k bY q), hA', hB']
  rw [tri_two_eq _ _ _ _ _ _ _ h12 (hd M bx) (hd X bx) (hd Y bx) (hd M bY) (hd X bY) (hd Y bY)]
  simp only [N0]
  ring

/-- **Both stages for the block sum of the two-line form.** -/
theorem ef_twoBlock {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (rep : F → F) (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (E0 E2 : F → (Fin 4 → ℝ) → ℂ) (h0 : ∀ r, IsLoopPoly 2 3 fun ℓ => E0 r (ℓ 0))
    (h2 : ∀ r, IsLoopPoly 2 1 fun ℓ => E2 r (ℓ 0)) {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ)
    (bx bY : Bool) (K : ℂ) :
    EF fun q => ∑ f, (Φ.coeff f : ℂ) *
      (K * tw (E0 (rep f) q) (E2 (rep f) q) (Φ.mass f) ε (zk k bx q) (zk k bY q)) := by
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  set X : ℝ := 1 + ∑ g, Φ.mass g with hX
  have hX0 : 0 < X := by
    have := Finset.sum_nonneg (s := Finset.univ) fun g (_ : g ∈ Finset.univ) => (hpos g).le
    linarith
  have hXY : X ^ 2 - (X + 1) ^ 2 ≠ 0 := by nlinarith
  refine (EF.sum Finset.univ fun f _ =>
    (ef_twoTriple k hε (E0 (rep f)) (E2 (rep f)) (h0 (rep f)) (h2 (rep f)) (Φ.mass f) X (X + 1)
      hXY bx bY).const_mul ((Φ.coeff f : ℂ) * K)).congr fun q => ?_
  rw [sum_block_eq_sum_triple Φ rep hrep hPV₁ hPV₂ X (X + 1)
    (fun r M => K * tw (E0 r q) (E2 r q) M ε (zk k bx q) (zk k bY q))]
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

end QED.GradedProof.VP2

end
