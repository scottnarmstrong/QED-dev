/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdDup

/-!
# (R-Π₄) step L6d3: one-loop rests on the Minkowski side

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. The face values
of the two-loop pieces are reduced one-loop functionals `∫_Δ faceIdRedBr` of the rest lines. Here
these functionals are identified with the `ε → 0⁺` limits of the energy-first integrals of the
one-loop integrands of the rests: lines at momentum `q` or `k + q` (flags `b`), masses `≥ m₀`,
below threshold `k² > -4m₀²`.

* `faceIdBP`: the external momenta of the rest lines; `faceId_VR_ge`: `V̂ ≥ c > 0`;
* `faceId_tendsto_core`: the limit through product data with a given quartic;
* **`faceId_tendsto_four`**, **`faceId_tendsto_five`**: four (cubic numerator) and five lines;
* **`faceId_tendsto_three`**: three lines with a constant numerator, through the duplicated
  four-line data (`faceId_pvOf_dup`) and an `iε` correction.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.Integration.Feynman (simplexSet simplexPoint simplexPoint_mem_stdSimplex)

/-! ### The rest data -/

/-- The external momenta of rest lines: `k` on the flagged lines, `0` otherwise. -/
def faceIdBP {n : ℕ} (k : Fin 4 → ℝ) (b : Fin n → Bool) : Fin n → Fin 4 → ℝ :=
  fun i => if b i then k else 0

theorem faceId_kd_dir (c : Bool) : (kd c).dir = ![1, 0] := by
  cases c <;> rfl

theorem faceId_kd_mom (c : Bool) (k : Fin 4 → ℝ) : (kd c).mom k k = if c then k else 0 := by
  cases c <;> rfl

theorem faceId_kd_ne_out (c : Bool) : kd c ≠ .out := by
  cases c <;> decide

/-- **`V̂` of a rest is bounded below below threshold**: masses `≥ m₀ > 0`, `k² > -4m₀²`. -/
theorem faceId_VR_ge {n : ℕ} (k : Fin 4 → ℝ) (b : Fin (n + 1) → Bool) (MR : Fin (n + 1) → ℝ)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (hMR : ∀ i, m₀ ≤ MR i) {z : Fin (n + 1) → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hz1 : ∑ i, z i = 1) :
    min (m₀ ^ 2) (m₀ ^ 2 + Minkowski.dot k k / 4) ≤ faceIdVR (faceIdBP k b) MR z := by
  set Z : ℝ := ∑ j, if b j then z j else 0 with hZ
  set s := Minkowski.dot k k
  have hP : faceIdP0 (faceIdBP k b) z = Z • k := by
    funext μ
    simp only [faceIdP0, faceIdBP, Pi.smul_apply, smul_eq_mul, hZ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hS : ∑ j, z j * (MR j ^ 2 + Minkowski.dot (faceIdBP k b j) (faceIdBP k b j)) =
      ∑ j, z j * MR j ^ 2 + Z * s := by
    rw [hZ, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [faceIdBP]
    split_ifs
    · ring
    · simp [Minkowski.dot]
  have hM : m₀ ^ 2 ≤ ∑ j, z j * MR j ^ 2 := by
    calc m₀ ^ 2 = ∑ j, z j * m₀ ^ 2 := by rw [← Finset.sum_mul, hz1, one_mul]
      _ ≤ ∑ j, z j * MR j ^ 2 := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm₀.le (hMR j) 2) (hz j)
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun j _ => by split_ifs <;> simp [hz j]
  have hZ1 : Z ≤ 1 := by
    rw [← hz1]
    exact Finset.sum_le_sum fun j _ => by split_ifs <;> simp [hz j]
  have hV : faceIdVR (faceIdBP k b) MR z = ∑ j, z j * MR j ^ 2 + Z * (1 - Z) * s := by
    unfold faceIdVR
    rw [hS, hP, faceId_dot_smul]
    ring
  rw [hV]
  rcases le_or_gt 0 s with hs | hs
  · have : 0 ≤ Z * (1 - Z) * s := mul_nonneg (mul_nonneg hZ0 (by linarith)) hs
    exact (min_le_left _ _).trans (by linarith)
  · have h4 : Z * (1 - Z) ≤ 1 / 4 := by nlinarith [sq_nonneg (Z - 1 / 2)]
    have : s / 4 ≤ Z * (1 - Z) * s := by nlinarith
    exact (min_le_right _ _).trans (by linarith)

theorem faceId_VR_pos {m₀ : ℝ} (hm₀ : 0 < m₀) {k : Fin 4 → ℝ}
    (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) :
    0 < min (m₀ ^ 2) (m₀ ^ 2 + Minkowski.dot k k / 4) :=
  lt_min (by positivity) (by linarith)

/-- `V̂ ≥ c` on the one-loop simplex, in the form of `faceId_pvOf_pad`. -/
theorem faceId_VR_ge_simplex {n : ℕ} (k : Fin 4 → ℝ) (b : Fin (n + 1) → Bool)
    (Ms : Fin (n + 1) → ℝ) {m₀ : ℝ} (hm₀ : 0 < m₀) (hMs : ∀ i, m₀ ≤ Ms i) :
    ∀ w ∈ simplexSet n, min (m₀ ^ 2) (m₀ ^ 2 + Minkowski.dot k k / 4) ≤
      faceIdVR (faceIdBP k b) Ms (simplexPoint w) := by
  intro w hw
  obtain ⟨h0, h1⟩ := simplexPoint_mem_stdSimplex hw
  exact faceId_VR_ge k b Ms hm₀ hMs h0 h1

/-! ### The limit through product data -/

/-- **The limit through product data with a given quartic** (the common part of
`tendsto_kinds`): if the quartic times the line denominators factors as a one-loop integrand
`F ε` times the cube of the auxiliary propagator, then `∫ F ε → (auxLimit mass)⁻¹ · pv`. -/
theorem faceId_tendsto_core (D : SEData) {Q : LoopQuartic} (hQ : D.Good Q) {p : Fin 4 → ℝ}
    (hV : D.VPos (D.mom p)) {mass : ℝ} (hmass : 0 < mass) (F : ℝ → (Fin 4 → ℝ) → ℂ)
    (hfac : ∀ ε : ℝ, 0 < ε → ∀ ℓ : Fin 2 → Fin 4 → ℝ,
      Q.eval ℓ * ∏ i, (lineDenom D.α (D.mom p) D.M ε i ℓ)⁻¹ =
        F ε (ℓ 0) * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral (F ε)) (𝓝[>] 0)
      (𝓝 ((auxLimit mass)⁻¹ * D.pv Q (D.mom p))) := by
  have h := SEData.tendsto_pv hQ hV
  have hH := tendsto_energyFirstIntegral_aux hmass
  have hH0 := auxLimit_ne_zero hmass
  refine ((hH.inv₀ hH0).mul h).congr' ?_
  filter_upwards [self_mem_nhdsWithin, hH.eventually_ne hH0] with ε (hε : 0 < ε) hne
  have e : (fun ℓ => Q.eval ℓ * ∏ i, (lineDenom D.α (D.mom p) D.M ε i ℓ)⁻¹) =
      fun ℓ => F ε (ℓ 0) * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3 := funext (hfac ε hε)
  rw [e, jointEnergyFirstIntegral_two_mul (F ε) (fun k => ((propDenom mass ε k)⁻¹) ^ 3)]
  generalize (QED.OneLoop.energyFirstIntegral fun k => ((propDenom mass ε k)⁻¹) ^ 3) = A at hne ⊢
  field_simp

/-! ### Four lines -/

theorem faceId_alpha_kinds4c (b : Fin 4 → Bool) :
    castLoopMatrix (fun i => (kinds4c b i).dir) = faceIdPadα 3 := by
  funext i s
  fin_cases i <;> fin_cases s <;>
    simp [castLoopMatrix, kinds4c, faceId_kd_dir, faceIdPadα, Fin.append, Fin.addCases] <;> rfl

theorem faceId_mom_kinds4c (b : Fin 4 → Bool) (k : Fin 4 → ℝ) :
    (fun i => (kinds4c b i).mom k k) = faceIdPadP (faceIdBP k b) := by
  funext i
  fin_cases i <;> simp [kinds4c, faceId_kd_mom] <;> rfl

theorem faceId_padM_four (Ms : Fin 4 → ℝ) (m₀ : ℝ) :
    (faceIdPadM Ms m₀ : Fin 7 → ℝ) = ![Ms 0, Ms 1, Ms 2, Ms 3, m₀, m₀, m₀] := by
  funext i
  fin_cases i <;> rfl

theorem faceId_ne_out_kinds4c (b : Fin 4 → Bool) : ∀ i, kinds4c b i ≠ .out := by
  intro i
  fin_cases i <;> simp [kinds4c, faceId_kd_ne_out]

section Four

variable (b : Fin 4 → Bool) (Ms : Fin 4 → ℝ) {m₀ : ℝ} (hm₀ : 0 < m₀) (hMs : ∀ i, m₀ ≤ Ms i)
  {k : Fin 4 → ℝ} (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) {Q : LoopQuartic} (hq : Q.quart = 0)
  {N : (Fin 4 → ℝ) → ℂ} (hN : ∀ ℓ, Q.eval ℓ = N (ℓ 0))

/-- The product data of four rest lines and three auxiliary lines of mass `m₀`. -/
noncomputable def faceIdD4 (m₀ : ℝ) : SEData :=
  faceIdKData (le_refl 6) (kinds4c b) ![Ms 0, Ms 1, Ms 2, Ms 3, m₀, m₀, m₀] (crit_kinds4c b)

include hm₀ hMs hk in
theorem faceId_vpos_four : (faceIdD4 b Ms m₀).VPos ((faceIdD4 b Ms m₀).mom k) := by
  have hM : ∀ i, m₀ ^ 2 ≤ (![Ms 0, Ms 1, Ms 2, Ms 3, m₀, m₀, m₀] : Fin 7 → ℝ) i ^ 2 := by
    intro i
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] <;>
      first | exact le_rfl | exact pow_le_pow_left₀ hm₀.le (hMs _) 2
  have hp : -(m₀ + m₀) ^ 2 < Minkowski.dot k k := by nlinarith
  refine ⟨min 1 (1 + Minkowski.dot k k / (m₀ + m₀) ^ 2) * min (m₀ ^ 2) (m₀ ^ 2), ?_,
    fun z hz hz1 hU => ?_⟩
  rotate_left
  · unfold faceIdD4 at hU ⊢
    rw [faceId_kData_mom _ _ (faceId_ne_out_kinds4c b)]
    exact symanzikV_kinds_se_ge (kinds4c b) (faceId_ne_out_kinds4c b) _ hm₀ hm₀ hp
      (fun i _ => hM i) (fun i _ => hM i) hz hz1 hU
  · have hT2 : 0 < (m₀ + m₀) ^ 2 := by positivity
    refine mul_pos (lt_min one_pos ?_) (lt_min (by positivity) (by positivity))
    have h1 : 0 < (m₀ + m₀) ^ 2 + Minkowski.dot k k := by linarith
    calc (0 : ℝ) < ((m₀ + m₀) ^ 2 + Minkowski.dot k k) / (m₀ + m₀) ^ 2 := by positivity
      _ = 1 + Minkowski.dot k k / (m₀ + m₀) ^ 2 := by field_simp

include hq hN in
theorem faceId_good_four : (faceIdD4 b Ms m₀).Good Q := by
  have hα : ∀ e ∈ ({0, 1, 2} : Finset (Fin 7)),
      (castLoopMatrix fun i => (kinds4c b i).dir) e = ![1, 0] := by
    intro e he
    rw [faceId_alpha_kinds4c]
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> rfl
  exact ⟨Or.inr hq, refinedBound_of_dependsOnZero_cubic _ (by decide) hα Q hq fun ℓ => by
    rw [hN, hN]
    rfl⟩

theorem faceId_mom_four : (faceIdD4 b Ms m₀).mom k = faceIdPadP (faceIdBP k b) :=
  (faceId_kData_mom (m := 6) _ _ (faceId_ne_out_kinds4c b) _ _ k).trans (faceId_mom_kinds4c b k)

include hm₀ hMs hk hq hN in
/-- **Integrability of the padded four-line data.** -/
theorem faceId_int_four : IntegrableOn (QED.TwoLoop.ClassLimit.paramIntegrand Q (faceIdPadα 3)
    (faceIdPadP (faceIdBP k b)) (faceIdPadM Ms m₀) 0) (simplexSet 6) := by
  have h := SEData.integrableOn_pv (faceId_good_four b Ms hq hN)
    (faceId_vpos_four b Ms hm₀ hMs hk)
  rw [faceId_mom_four] at h
  rw [faceId_padM_four, ← faceId_alpha_kinds4c b]
  exact h

include hm₀ hMs hk hq hN in
/-- **Four rest lines through the padded data**: the limit is `(auxLimit m₀)⁻¹ pvOf`. -/
theorem faceId_tendsto_four_pv :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun q =>
        N q * ∏ i, (propDenom (Ms i) ε (if b i then k + q else q))⁻¹) (𝓝[>] 0)
      (𝓝 ((auxLimit m₀)⁻¹ * pvOf Q.eval (faceIdPadα 3) (faceIdPadP (faceIdBP k b))
        (faceIdPadM Ms m₀))) := by
  have h := faceId_tendsto_core (faceIdD4 b Ms m₀) (faceId_good_four b Ms hq hN)
    (faceId_vpos_four b Ms hm₀ hMs hk) hm₀
    (fun ε q => N q * ∏ i, (propDenom (Ms i) ε (if b i then k + q else q))⁻¹) ?_
  · have hv : (faceIdD4 b Ms m₀).pv Q ((faceIdD4 b Ms m₀).mom k) =
        pvOf Q.eval (faceIdPadα 3) (faceIdPadP (faceIdBP k b)) (faceIdPadM Ms m₀) := by
      rw [pvOf_eq rfl, faceId_mom_four, faceId_padM_four, ← faceId_alpha_kinds4c b]
      rfl
    rwa [hv] at h
  intro ε _ ℓ
  show Q.eval ℓ * ∏ i, (lineDenom (castLoopMatrix fun i => (kinds4c b i).dir)
    ((faceIdD4 b Ms m₀).mom k) ![Ms 0, Ms 1, Ms 2, Ms 3, m₀, m₀, m₀] ε i ℓ)⁻¹ = _
  rw [faceId_mom_four, ← faceId_mom_kinds4c b k, prod_lineDenom_kinds, hN, Fin.prod_univ_four]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kinds4c, Matrix.cons_val_zero,
    Matrix.cons_val_succ, mul_one]
  rcases b 0 <;> rcases b 1 <;> rcases b 2 <;> rcases b 3 <;>
    simp only [kd, LineKind.lineMom, ite_true, Bool.false_eq_true, ite_false] <;> ring

include hm₀ hMs hk hq hN in
/-- **Four rest lines**: the limit of the one-loop integrand is `iπ²` times the reduced one-loop
functional of the four lines (numerator of loop-`1` degree at most one, cubic). -/
theorem faceId_tendsto_four (hQ1 : LoopDegLe 1 1 Q) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun q =>
        N q * ∏ i, (propDenom (Ms i) ε (if b i then k + q else q))⁻¹) (𝓝[>] 0)
      (𝓝 (I * (π : ℂ) ^ 2 * ∫ w in simplexSet 3, faceIdRedBr 4 Q
        (faceIdX0 (faceIdP0 (faceIdBP k b) (simplexPoint w)))
        (faceIdVR (faceIdBP k b) Ms (simplexPoint w)))) := by
  have h := faceId_tendsto_four_pv b Ms hm₀ hMs hk hq hN
  rwa [faceId_pvOf_pad (r := 0) hQ1 (fun _ => hq) (faceIdBP k b) Ms (faceId_VR_pos hm₀ hk) hm₀
    (faceId_VR_ge_simplex k b Ms hm₀ hMs) rfl (faceId_int_four b Ms hm₀ hMs hk hq hN)] at h

end Four

/-! ### Five lines -/

theorem faceId_alpha_kinds5 (b : Fin 5 → Bool) :
    castLoopMatrix (fun i => (kinds5 b i).dir) = faceIdPadα 4 := by
  funext i s
  fin_cases i <;> fin_cases s <;>
    simp [castLoopMatrix, kinds5, faceId_kd_dir, faceIdPadα, Fin.append, Fin.addCases] <;> rfl

theorem faceId_mom_kinds5 (b : Fin 5 → Bool) (k : Fin 4 → ℝ) :
    (fun i => (kinds5 b i).mom k k) = faceIdPadP (faceIdBP k b) := by
  funext i
  fin_cases i <;> simp [kinds5, faceId_kd_mom] <;> rfl

theorem faceId_padM_five (Ms : Fin 5 → ℝ) (m₀ : ℝ) :
    (faceIdPadM Ms m₀ : Fin 8 → ℝ) = ![Ms 0, Ms 1, Ms 2, Ms 3, Ms 4, m₀, m₀, m₀] := by
  funext i
  fin_cases i <;> rfl

theorem faceId_ne_out_kinds5 (b : Fin 5 → Bool) : ∀ i, kinds5 b i ≠ .out := by
  intro i
  fin_cases i <;> simp [kinds5, faceId_kd_ne_out]

section Five

variable (b : Fin 5 → Bool) (Ms : Fin 5 → ℝ) {m₀ : ℝ} (hm₀ : 0 < m₀) (hMs : ∀ i, m₀ ≤ Ms i)
  {k : Fin 4 → ℝ} (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) {Q : LoopQuartic}
  {N : (Fin 4 → ℝ) → ℂ} (hN : ∀ ℓ, Q.eval ℓ = N (ℓ 0))

/-- The product data of five rest lines and three auxiliary lines of mass `m₀`. -/
noncomputable def faceIdD5 (m₀ : ℝ) : SEData :=
  kindsData (le_refl 7) (kinds5 b) ![Ms 0, Ms 1, Ms 2, Ms 3, Ms 4, m₀, m₀, m₀] (crit_kinds5 b)

theorem faceId_mom_five : (faceIdD5 b Ms m₀).mom k = faceIdPadP (faceIdBP k b) :=
  (kindsData_mom (m := 7) _ _ (faceId_ne_out_kinds5 b) _ _ k).trans (faceId_mom_kinds5 b k)

include hm₀ hMs hk in
theorem faceId_vpos_five : (faceIdD5 b Ms m₀).VPos ((faceIdD5 b Ms m₀).mom k) := by
  have hM : ∀ i, m₀ ^ 2 ≤ (![Ms 0, Ms 1, Ms 2, Ms 3, Ms 4, m₀, m₀, m₀] : Fin 8 → ℝ) i ^ 2 := by
    intro i
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] <;>
      first | exact le_rfl | exact pow_le_pow_left₀ hm₀.le (hMs _) 2
  have hp : -(m₀ + m₀) ^ 2 < Minkowski.dot k k := by nlinarith
  refine ⟨min 1 (1 + Minkowski.dot k k / (m₀ + m₀) ^ 2) * min (m₀ ^ 2) (m₀ ^ 2), ?_,
    fun z hz hz1 hU => ?_⟩
  rotate_left
  · unfold faceIdD5 at hU ⊢
    rw [kindsData_mom _ _ (faceId_ne_out_kinds5 b)]
    exact symanzikV_kinds_se_ge (kinds5 b) (faceId_ne_out_kinds5 b) _ hm₀ hm₀ hp
      (fun i _ => hM i) (fun i _ => hM i) hz hz1 hU
  · have hT2 : 0 < (m₀ + m₀) ^ 2 := by positivity
    refine mul_pos (lt_min one_pos ?_) (lt_min (by positivity) (by positivity))
    have h1 : 0 < (m₀ + m₀) ^ 2 + Minkowski.dot k k := by linarith
    calc (0 : ℝ) < ((m₀ + m₀) ^ 2 + Minkowski.dot k k) / (m₀ + m₀) ^ 2 := by positivity
      _ = 1 + Minkowski.dot k k / (m₀ + m₀) ^ 2 := by field_simp

include hN in
theorem faceId_good_five : (faceIdD5 b Ms m₀).Good Q := by
  have hα : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin 8)),
      (castLoopMatrix fun i => (kinds5 b i).dir) e = ![1, 0] := by
    intro e he
    rw [faceId_alpha_kinds5]
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;> rfl
  exact ⟨Or.inl le_rfl, refinedBound_of_dependsOnZero _ (by decide) hα Q fun ℓ => by
    rw [hN, hN]
    rfl⟩

include hm₀ hMs hk hN in
/-- **Integrability of the padded five-line data.** -/
theorem faceId_int_five : IntegrableOn (QED.TwoLoop.ClassLimit.paramIntegrand Q (faceIdPadα 4)
    (faceIdPadP (faceIdBP k b)) (faceIdPadM Ms m₀) 0) (simplexSet 7) := by
  have h := SEData.integrableOn_pv (faceId_good_five b Ms hN) (faceId_vpos_five b Ms hm₀ hMs hk)
  rw [faceId_mom_five] at h
  rw [faceId_padM_five, ← faceId_alpha_kinds5 b]
  exact h

include hm₀ hMs hk hN in
/-- **Five rest lines through the padded data**: the limit is `(auxLimit m₀)⁻¹ pvOf`. -/
theorem faceId_tendsto_five_pv :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun q =>
        N q * ∏ i, (propDenom (Ms i) ε (if b i then k + q else q))⁻¹) (𝓝[>] 0)
      (𝓝 ((auxLimit m₀)⁻¹ * pvOf Q.eval (faceIdPadα 4) (faceIdPadP (faceIdBP k b))
        (faceIdPadM Ms m₀))) := by
  have h := faceId_tendsto_core (faceIdD5 b Ms m₀) (faceId_good_five b Ms hN)
    (faceId_vpos_five b Ms hm₀ hMs hk) hm₀
    (fun ε q => N q * ∏ i, (propDenom (Ms i) ε (if b i then k + q else q))⁻¹) ?_
  · have hv : (faceIdD5 b Ms m₀).pv Q ((faceIdD5 b Ms m₀).mom k) =
        pvOf Q.eval (faceIdPadα 4) (faceIdPadP (faceIdBP k b)) (faceIdPadM Ms m₀) := by
      rw [pvOf_eq rfl, faceId_mom_five, faceId_padM_five, ← faceId_alpha_kinds5 b]
      rfl
    rwa [hv] at h
  intro ε _ ℓ
  show Q.eval ℓ * ∏ i, (lineDenom (castLoopMatrix fun i => (kinds5 b i).dir)
    ((faceIdD5 b Ms m₀).mom k) ![Ms 0, Ms 1, Ms 2, Ms 3, Ms 4, m₀, m₀, m₀] ε i ℓ)⁻¹ = _
  rw [faceId_mom_five, ← faceId_mom_kinds5 b k, prod_lineDenom_kinds, hN, Fin.prod_univ_five]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kinds5, Matrix.cons_val_zero,
    Matrix.cons_val_succ, mul_one]
  rcases b 0 <;> rcases b 1 <;> rcases b 2 <;> rcases b 3 <;> rcases b 4 <;>
    simp only [kd, LineKind.lineMom, ite_true, Bool.false_eq_true, ite_false] <;> ring

include hm₀ hMs hk hN in
/-- **Five rest lines**: the limit of the one-loop integrand is `iπ²` times the reduced one-loop
functional of the five lines (numerator of loop-`1` degree at most one). -/
theorem faceId_tendsto_five (hQ1 : LoopDegLe 1 1 Q) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun q =>
        N q * ∏ i, (propDenom (Ms i) ε (if b i then k + q else q))⁻¹) (𝓝[>] 0)
      (𝓝 (I * (π : ℂ) ^ 2 * ∫ w in simplexSet 4, faceIdRedBr 5 Q
        (faceIdX0 (faceIdP0 (faceIdBP k b) (simplexPoint w)))
        (faceIdVR (faceIdBP k b) Ms (simplexPoint w)))) := by
  have h := faceId_tendsto_five_pv b Ms hm₀ hMs hk hN
  rwa [faceId_pvOf_pad (r := 1) hQ1 (fun h => absurd h one_ne_zero) (faceIdBP k b) Ms
    (faceId_VR_pos hm₀ hk) hm₀ (faceId_VR_ge_simplex k b Ms hm₀ hMs) rfl
    (faceId_int_five b Ms hm₀ hMs hk hN)] at h

end Five

/-! ### Three lines -/

/-- The constant quartic `C`. -/
noncomputable def faceIdConstQ (C : ℂ) : LoopQuartic where
  const := C
  lin _ := 0
  quad _ _ := 0
  cub _ _ _ := 0
  quart _ _ _ _ := 0

theorem faceId_eval_constQ (C : ℂ) (ℓ : Fin 2 → Fin 4 → ℝ) : (faceIdConstQ C).eval ℓ = C := by
  simp [LoopQuartic.eval, LoopQuartic.evalC, faceIdConstQ]

theorem faceId_dupP_bp {k : Fin 4 → ℝ} (b : Fin 3 → Bool) :
    (faceIdBP k ![b 0, b 0, b 1, b 2] : Fin 4 → Fin 4 → ℝ) = faceIdDupP (faceIdBP k b) := by
  funext i
  fin_cases i <;> rfl

theorem faceId_dupM_eq (Ms : Fin 3 → ℝ) :
    (![Ms 0, Ms 0, Ms 1, Ms 2] : Fin 4 → ℝ) = faceIdDupM Ms := by
  funext i
  fin_cases i <;> rfl

section Three

variable (b : Fin 3 → Bool) (Ms : Fin 3 → ℝ) {m₀ : ℝ} (hm₀ : 0 < m₀) (hMs : ∀ i, m₀ ≤ Ms i)
  {k : Fin 4 → ℝ} (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k)

include hm₀ hMs hk in
/-- **Three rest lines with a constant numerator**: the limit of the one-loop integrand is
`iπ² ∫_{Δ₂} C V̂⁻¹`, through the duplicated four-line data (`faceId_pvOf_dup`) and the
correction `C · iε/(D₀² D₁ D₂)`, whose integral stays bounded. -/
theorem faceId_tendsto_three (C : ℂ) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun q =>
        C * ∏ i, (propDenom (Ms i) ε (if b i then k + q else q))⁻¹) (𝓝[>] 0)
      (𝓝 (I * (π : ℂ) ^ 2 * ∫ x in simplexSet 2,
        C * ((faceIdVR (faceIdBP k b) Ms (simplexPoint x) : ℝ) : ℂ)⁻¹)) := by
  set b4 : Fin 4 → Bool := ![b 0, b 0, b 1, b 2] with hb4
  set M4 : Fin 4 → ℝ := ![Ms 0, Ms 0, Ms 1, Ms 2] with hM4
  have hM4m : ∀ i, m₀ ≤ M4 i := by
    intro i
    fin_cases i
    exacts [hMs 0, hMs 0, hMs 1, hMs 2]
  set Qd := faceIdDenQ C (faceIdBP k b 0) (Ms 0) with hQd
  set Nd : (Fin 4 → ℝ) → ℂ := fun q => C * propDenom (Ms 0) 0 (zk k (b 0) q) with hNd
  have hQN : ∀ ℓ, Qd.eval ℓ = Nd (ℓ 0) := by
    intro ℓ
    rw [hQd, faceId_eval_denQ_prop]
    simp only [hNd, zk, faceIdBP]
    cases b 0
    · simp
    · simp [add_comm]
  -- the duplicated four-line integrand
  have A := faceId_tendsto_four_pv b4 M4 hm₀ hM4m hk (faceId_quart_denQ _ _ _) hQN
  have hint := faceId_int_four b4 M4 hm₀ hM4m hk (faceId_quart_denQ _ _ _) hQN
  rw [hb4, faceId_dupP_bp, hM4, faceId_dupM_eq] at hint
  have hval := faceId_pvOf_dup (faceIdBP k b) Ms C (faceId_VR_pos hm₀ hk) hm₀
    (fun z hz hz1 => faceId_VR_ge k b Ms hm₀ hMs hz hz1) hint
  rw [← faceId_dupP_bp, ← faceId_dupM_eq] at hval
  rw [hval] at A
  -- the correction
  have B := faceId_tendsto_four_pv b4 M4 hm₀ hM4m hk (Q := faceIdConstQ C) (N := fun _ => C) rfl
    (faceId_eval_constQ C)
  have hB := tendsto_negEpsI.mul B
  rw [zero_mul] at hB
  have hAB := A.add hB
  rw [add_zero] at hAB
  refine hAB.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hNp : IsLoopPoly 2 3 fun ℓ : Fin 2 → Fin 4 → ℝ => Nd (ℓ 0) :=
    ((IsLoopPoly.const (n := 0) C).mul
      ((isLoopAffine_zk k (b 0)).isLoopPoly_propDenom (Ms 0) 0)).mono (by norm_num)
  have E1 := ef_piece4c b4 M4 hε k Nd hNp
  have E2 := (ef_piece4c b4 M4 hε k (fun _ => C)
    ((IsLoopPoly.const (n := 0) C).mono (by norm_num))).const_mul (-((ε : ℂ) * I))
  rw [← QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul, ← efi_add E1 E2]
  congr 1
  funext q
  simp only [Fin.prod_univ_four, Fin.prod_univ_three]
  simp only [hb4, hM4, hNd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  have hd := propDenom_ne_zero (M := Ms 0) hε.ne' (zk k (b 0) q)
  have h0 : propDenom (Ms 0) 0 (zk k (b 0) q) = propDenom (Ms 0) ε (zk k (b 0) q) + ε * I := by
    simp only [propDenom]; push_cast; ring
  have hz : (if b 0 then k + q else q) = zk k (b 0) q := rfl
  rw [h0, hz]
  generalize propDenom (Ms 0) ε (zk k (b 0) q) = D at hd ⊢
  field_simp
  ring

end Three

end QED.GradedProof.RPi4

end
