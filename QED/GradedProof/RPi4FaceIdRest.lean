/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdMid
public import QED.GradedProof.RPi4FaceIdMink
public import QED.GradedProof.RPi4FaceIdPiece

/-!
# (R-Π₄) step L6d3: the rest data of a sorted face

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. A sort of a
piece (`FaceSort`) is only given existentially (`faceId_exists_sort`). Its rest lines are the
lines of row `(1, 0)` in some order; the one-loop Minkowski integrand of the rest is a product
over them, so it does not depend on the order:

* **`faceId_prod_rest`**: the product over the sorted rest lines is the product over the lines of
  row `(1, 0)`;
* `faceIdFlag`, **`faceId_shape_pR`**, `faceId_prod_rest_bp`: rest momenta in `{0, k}` are
  `faceIdBP k` of a flag, and the rest integrand is `∏ D_l(pp l + x)⁻¹`;
* `faceId_continuousOn_redBr_fam`, `faceId_continuous_seT`, `faceId_se_int`: the integrability
  hypothesis of `faceId_faceIdVal_se_mid`, discharged;
* **`faceId_faceIdVal_se_sort`**: the self-energy face of a sort as a reduced functional;
* **`faceId_tendsto_se_five`**, **`faceId_tendsto_se_four`**, **`faceId_tendsto_vtx_four`**,
  **`faceId_tendsto_vtx_three`**: the face values of a sort as `ε → 0⁺` limits of one-loop
  Minkowski integrals (`iπ²` resp. `2iπ²` times the face value);
* `faceId_filter_swapFlip_10`, `faceId_flipMom_of_row01`, `faceId_lapF_swapQ`: loop-`0` data.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.Integration.Feynman (simplexSet simplexPoint)

/-- The flag of a line: its momentum is `k`. -/
noncomputable def faceIdFlag {n : ℕ} (pp : Fin n → Fin 4 → ℝ) (k : Fin 4 → ℝ) (l : Fin n) : Bool :=
  @decide (pp l = k) (Classical.dec _)

section RestSort

variable {p q : ℕ} {α : Fin (p + 1 + 1 + q + 1) → Fin 2 → ℝ}
  {e : Equiv.Perm (Fin (p + 1 + 1 + q + 1))}

/-- **The product over the sorted rest lines** is the product over the lines of row `(1, 0)`. -/
theorem faceId_prod_rest {R : Type*} [CommMonoid R] (hS : FaceSort p q α e)
    (f : Fin (p + 1 + 1 + q + 1) → R) :
    ∏ j : Fin (q + 1), f (e (Fin.natAdd (p + 1 + 1) j)) =
      ∏ l ∈ Finset.univ.filter (fun l => α l = ![1, 0]), f l := by
  classical
  refine Finset.prod_bij (fun j _ => e (Fin.natAdd (p + 1 + 1) j)) (fun j _ => ?_)
    (fun j₁ _ j₂ _ h => ?_) (fun l hl => ?_) (fun _ _ => rfl)
  · simpa using hS.hR j
  · simpa using e.injective h
  · have hl' : α l = ![1, 0] := by simpa using hl
    obtain ⟨i, rfl⟩ := e.surjective l
    revert hl'
    refine Fin.addCases (m := p + 1 + 1) (n := q + 1) (fun i => ?_) (fun j => ?_) i
    · intro hα
      exfalso
      rcases hS.hF i with h | h
      · rw [h] at hα; exact row01_ne hα
      · rw [h] at hα; exact row1m1_ne hα
    · intro _
      exact ⟨j, Finset.mem_univ _, rfl⟩

/-- **The rest momenta of a sort as `faceIdBP`**: rest momenta in `{0, k}` are `faceIdBP k` of
the flags `pp l = k`. -/
theorem faceId_shape_pR (hS : FaceSort p q α e) (pp : Fin (p + 1 + 1 + q + 1) → Fin 4 → ℝ)
    (M : Fin (p + 1 + 1 + q + 1) → ℝ) {k : Fin 4 → ℝ}
    (hpp : ∀ l, α l = ![1, 0] → pp l = 0 ∨ pp l = k) :
    (hS.shape pp M).pR = faceIdBP k (fun j => faceIdFlag pp k (e (Fin.natAdd (p + 1 + 1) j))) := by
  funext j
  simp only [FaceSort.shape, faceIdBP, faceIdFlag, decide_eq_true_eq]
  split_ifs with h
  · exact h
  · exact ((hpp _ (hS.hR j)).resolve_right h)

/-- **The rest masses of a sort are bounded below.** -/
theorem faceId_shape_MR_ge (hS : FaceSort p q α e) (pp : Fin (p + 1 + 1 + q + 1) → Fin 4 → ℝ)
    (M : Fin (p + 1 + 1 + q + 1) → ℝ) {m₀ : ℝ} (hM : ∀ l, α l = ![1, 0] → m₀ ≤ M l)
    (j : Fin (q + 1)) : m₀ ≤ (hS.shape pp M).MR j :=
  hM _ (hS.hR j)

/-- **The one-loop rest integrand of a sort**, in the piece's own line order: flagged lines carry
`k + q`, the others `q`; momenta in `{0, k}` give `pp l + q`. -/
theorem faceId_prod_rest_bp (hS : FaceSort p q α e) (pp : Fin (p + 1 + 1 + q + 1) → Fin 4 → ℝ)
    (M : Fin (p + 1 + 1 + q + 1) → ℝ) {k : Fin 4 → ℝ}
    (hpp : ∀ l, α l = ![1, 0] → pp l = 0 ∨ pp l = k) (ε : ℝ) (x : Fin 4 → ℝ) :
    ∏ j : Fin (q + 1), (propDenom ((hS.shape pp M).MR j) ε
        (if faceIdFlag pp k (e (Fin.natAdd (p + 1 + 1) j)) then k + x else x))⁻¹ =
      ∏ l ∈ Finset.univ.filter (fun l => α l = ![1, 0]), (propDenom (M l) ε (pp l + x))⁻¹ := by
  rw [← faceId_prod_rest hS]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [FaceSort.shape, faceIdFlag, decide_eq_true_eq]
  split_ifs with h
  · rw [h]
  · rw [(hpp _ (hS.hR j)).resolve_right h, zero_add]

end RestSort

/-! ### Continuity of the self-energy family -/

/-- **The reduced bracket of a continuous family of quartics is continuous** where `v ≠ 0`. -/
theorem faceId_continuousOn_redBr_fam {β : Type*} [TopologicalSpace β] (n : ℕ)
    {T : β → LoopQuartic} (h0 : Continuous fun w => (T w).const)
    (h1 : ∀ a, Continuous fun w => (T w).lin a) (h2 : ∀ a b, Continuous fun w => (T w).quad a b)
    (h3 : ∀ a b c, Continuous fun w => (T w).cub a b c)
    (h4 : ∀ a b c d, Continuous fun w => (T w).quart a b c d) {X : β → LoopIndex → ℂ}
    (hX : ∀ a, Continuous fun w => X w a) {v : β → ℝ} (hv : Continuous v) {s : Set β}
    (hs : ∀ w ∈ s, v w ≠ 0) :
    ContinuousOn (fun w => faceIdRedBr n (T w) (X w) (v w)) s := by
  have hinv : ∀ j : ℕ, ContinuousOn (fun w => (((v w ^ j : ℝ) : ℂ))⁻¹) s := fun j =>
    (continuous_ofReal.comp (hv.pow j)).continuousOn.inv₀ fun w hw =>
      ofReal_ne_zero.2 (pow_ne_zero _ (hs w hw))
  have hE : Continuous fun w => (T w).evalC (X w) := by
    unfold LoopQuartic.evalC
    fun_prop
  have hC2 : Continuous fun w => cTwoG (T w) (eS 0) (X w) := by
    unfold cTwoG LoopQuartic.hess LoopQuartic.quartSym
    fun_prop
  have hC4 : Continuous fun w => cFourG (T w) (eS 0) := by
    unfold cFourG
    fun_prop
  unfold faceIdRedBr
  exact (((continuous_const.mul hE).continuousOn.mul (hinv _)).add
    ((continuous_const.mul hC2).continuousOn.mul (hinv _))).add
    ((continuous_const.mul hC4).continuousOn.mul (hinv _))

section SE

variable {q : ℕ} (S : FaceShape (0 + 1) q) (Q : LoopQuartic)

/-- **The coefficients of the self-energy family are continuous** in the face weights. -/
theorem faceId_continuous_seT :
    (Continuous fun W => (faceIdSET S Q W).const) ∧
      (∀ a, Continuous fun W => (faceIdSET S Q W).lin a) ∧
      (∀ a b, Continuous fun W => (faceIdSET S Q W).quad a b) ∧
      (∀ a b c, Continuous fun W => (faceIdSET S Q W).cub a b c) ∧
      (∀ a b c d, Continuous fun W => (faceIdSET S Q W).quart a b c d) := by
  have hb : Continuous fun W : Fin (0 + 1) → ℝ => S.b (simplexPoint W) := by
    simp only [FaceShape.b]
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_simplexPoint i).mul continuous_const).mul continuous_const
  have hb₁ : ∀ μ, Continuous fun W : Fin (0 + 1) → ℝ => S.b₁ (simplexPoint W) μ := by
    intro μ
    simp only [FaceShape.b₁]
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_simplexPoint i).mul continuous_const).mul continuous_const
  obtain ⟨l0, l1, l2, l3, l4⟩ := faceId_continuous_lmap Q (faceId_continuous_faceIdMb hb)
  have hD : ∀ a, Continuous fun W : Fin (0 + 1) → ℝ =>
      loopComp ![0, -S.b₁ (simplexPoint W)] a := by
    rintro ⟨i, μ⟩
    simp only [loopComp]
    fin_cases i
    · simpa using continuous_const
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.neg_apply,
        ofReal_neg]
      exact (continuous_ofReal.comp (hb₁ μ)).neg
  exact faceId_continuous_shift l0 l1 l2 l3 l4 hD

theorem faceId_P0_eq {p q : ℕ} (S : FaceShape p q) (V : Fin (q + 1) → ℝ) :
    S.P0 V = faceIdP0 S.pR V := rfl

theorem faceId_mR_sub_eq {p q : ℕ} (S : FaceShape p q) (V : Fin (q + 1) → ℝ) :
    S.mR V - Minkowski.dot (S.P0 V) (S.P0 V) = faceIdVR S.pR S.MR V := by
  unfold faceIdVR FaceShape.mR
  rfl

/-- **The bracket of the self-energy family is integrable** on `Δ₁ × Δ_q` when `V̂ ≥ c > 0`. -/
theorem faceId_se_int (n : ℕ) {c : ℝ} (hc : 0 < c)
    (hVR : ∀ w ∈ simplexSet q, c ≤ faceIdVR S.pR S.MR (simplexPoint w)) :
    IntegrableOn (fun x : (Fin (0 + 1) → ℝ) × (Fin q → ℝ) =>
      faceIdRedBr n (faceIdSET S Q x.1) (faceIdX0 (faceIdP0 S.pR (simplexPoint x.2)))
        (faceIdVR S.pR S.MR (simplexPoint x.2)))
      (simplexSet (0 + 1) ×ˢ simplexSet q) := by
  obtain ⟨c0, c1, c2, c3, c4⟩ := faceId_continuous_seT S Q
  have hX : Continuous fun w : Fin q → ℝ => faceIdX0 (faceIdP0 S.pR (simplexPoint w)) :=
    faceId_continuous_X0 S.pR
  have hc : ContinuousOn (fun x : (Fin (0 + 1) → ℝ) × (Fin q → ℝ) =>
      faceIdRedBr n (faceIdSET S Q x.1) (faceIdX0 (faceIdP0 S.pR (simplexPoint x.2)))
        (faceIdVR S.pR S.MR (simplexPoint x.2))) (simplexSet (0 + 1) ×ˢ simplexSet q) := by
    refine faceId_continuousOn_redBr_fam (β := (Fin (0 + 1) → ℝ) × (Fin q → ℝ)) n
      (T := fun x => faceIdSET S Q x.1)
      (X := fun x => faceIdX0 (faceIdP0 S.pR (simplexPoint x.2)))
      (v := fun x => faceIdVR S.pR S.MR (simplexPoint x.2)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact c0.comp continuous_fst
    · exact fun a => (c1 a).comp continuous_fst
    · exact fun a b => (c2 a b).comp continuous_fst
    · exact fun a b c => (c3 a b c).comp continuous_fst
    · exact fun a b c d => (c4 a b c d).comp continuous_fst
    · exact fun a => ((continuous_apply a).comp hX).comp continuous_snd
    · exact (faceId_continuous_VR S.pR S.MR).comp continuous_snd
    · exact fun x hx => (hc.trans_le (hVR x.2 hx.2)).ne'
  exact hc.integrableOn_compact ((QED.Integration.Feynman.isCompact_simplexSet _).prod
    (QED.Integration.Feynman.isCompact_simplexSet _))

end SE

/-! ### The self-energy face of a sort -/

section SESort

variable {q : ℕ} {α : Fin (0 + 1 + 1 + q + 1) → Fin 2 → ℝ}
  {e : Equiv.Perm (Fin (0 + 1 + 1 + q + 1))} (hS : FaceSort 0 q α e)
  (pp : Fin (0 + 1 + 1 + q + 1) → Fin 4 → ℝ) (M : Fin (0 + 1 + 1 + q + 1) → ℝ)

/-- The fermion line of a self-energy face block has row `(0, 1)`. -/
theorem faceId_shape_αF_zero_se (huniq : ∀ l, α l = ![1, -1] ↔ l = FaceSort.gam e) :
    (hS.shape pp M).αF 0 = ![0, 1] := by
  rcases hS.hF 0 with h | h
  · exact h
  · exfalso
    have h' := (huniq _).1 h
    simp only [FaceSort.gam] at h'
    have := congrArg Fin.val (e.injective h')
    simp at this

/-- **The rest bound `V̂ ≥ c` of a sort.** -/
theorem faceId_shape_VR_ge {m₀ : ℝ} (hm₀ : 0 < m₀) (hM : ∀ l, α l = ![1, 0] → m₀ ≤ M l)
    {k : Fin 4 → ℝ} (hpp : ∀ l, α l = ![1, 0] → pp l = 0 ∨ pp l = k) :
    ∀ w ∈ simplexSet q, min (m₀ ^ 2) (m₀ ^ 2 + Minkowski.dot k k / 4) ≤
      faceIdVR (hS.shape pp M).pR (hS.shape pp M).MR (simplexPoint w) := by
  rw [faceId_shape_pR hS pp M hpp]
  exact faceId_VR_ge_simplex k _ _ hm₀ (faceId_shape_MR_ge hS pp M hM)

variable {Q : LoopQuartic}

/-- **The self-energy face of a sort is a reduced one-loop functional** of any `P` that agrees
with `Q` at the midpoint `ℓ₁ = (ℓ₀ + p_γ - p_f)/2` of the face (`f` the fermion line of row
`(0, 1)`); rest masses `≥ m₀ > 0`, rest momenta in `{0, k}`, `k² > -4m₀²`. -/
theorem faceId_faceIdVal_se_sort (huniq : ∀ l, α l = ![1, -1] ↔ l = FaceSort.gam e)
    {n : ℕ} (hQ : LoopDegLe 1 1 Q) (hn : n = 7 ∨ (n = 6 ∧ Q.quart = 0)) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hM : ∀ l, α l = ![1, 0] → m₀ ≤ M l) {k : Fin 4 → ℝ}
    (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (hpp : ∀ l, α l = ![1, 0] → pp l = 0 ∨ pp l = k)
    {P : LoopQuartic} (hP : ∀ f, α f = ![0, 1] → ∀ ℓ₀ : Fin 4 → ℝ,
      Q.eval ![ℓ₀, (1 / 2 : ℝ) • (ℓ₀ + pp (FaceSort.gam e) - pp f)] = P.eval ![ℓ₀, 0]) :
    faceIdVal n (hS.shape pp M) Q = (hS.shape pp M).faceIdRedVal (n - 2) P := by
  set S := hS.shape pp M with hSdef
  have hpos := faceId_VR_pos hm₀ hk
  have hVR := faceId_shape_VR_ge hS pp M hm₀ hM hpp
  have hint := faceId_se_int S Q (n - 2) hpos hVR
  simp only [← faceId_mR_sub_eq, ← faceId_P0_eq] at hint
  have h0 : S.αF 0 = ![0, 1] := faceId_shape_αF_zero_se hS pp M huniq
  have h1 : S.αF 1 = ![1, -1] := (huniq _).2 rfl
  refine faceId_faceIdVal_se_mid S hQ hn hint fun ℓ₀ => ?_
  rw [faceId_seY_half_01 S h0 h1]
  exact hP _ h0 ℓ₀

end SESort

/-! ### Self-energy faces on the Minkowski side -/

section SEMink

variable {Q : LoopQuartic} {m₀ : ℝ} (hm₀ : 0 < m₀) {k : Fin 4 → ℝ}
  (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) {N : (Fin 4 → ℝ) → ℂ} {P : LoopQuartic}
  (hP1 : LoopDegLe 1 1 P) (hPN : ∀ ℓ, P.eval ℓ = N (ℓ 0))

include hm₀ hk hP1 hPN

/-- **A self-energy face with five rest lines** (`n = 7`) is `(iπ²)⁻¹` times the `ε → 0⁺` limit
of the one-loop integrand `N(x) ∏_{rest} D_l(x)⁻¹` (rest lines at `pp l + x`), where `N` is the
numerator `Q` at the midpoint of the face. -/
theorem faceId_tendsto_se_five {α : Fin (0 + 1 + 1 + 4 + 1) → Fin 2 → ℝ}
    {e : Equiv.Perm (Fin (0 + 1 + 1 + 4 + 1))} (hS : FaceSort 0 4 α e)
    (pp : Fin (0 + 1 + 1 + 4 + 1) → Fin 4 → ℝ) (M : Fin (0 + 1 + 1 + 4 + 1) → ℝ)
    (huniq : ∀ l, α l = ![1, -1] ↔ l = FaceSort.gam (p := 0) (q := 4) e)
    (hQ : LoopDegLe 1 1 Q)
    (hM : ∀ l, α l = ![1, 0] → m₀ ≤ M l) (hpp : ∀ l, α l = ![1, 0] → pp l = 0 ∨ pp l = k)
    (hP : ∀ f, α f = ![0, 1] → ∀ ℓ₀ : Fin 4 → ℝ,
      Q.eval ![ℓ₀, (1 / 2 : ℝ) • (ℓ₀ + pp (FaceSort.gam (p := 0) (q := 4) e) - pp f)] = N ℓ₀) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun x => N x *
        ∏ l ∈ Finset.univ.filter (fun l => α l = ![1, 0]), (propDenom (M l) ε (pp l + x))⁻¹)
      (𝓝[>] 0) (𝓝 (I * (π : ℂ) ^ 2 * faceIdVal 7 (hS.shape pp M) Q)) := by
  rw [faceId_faceIdVal_se_sort hS pp M huniq hQ (Or.inl rfl) hm₀ hM hk hpp (P := P)
    fun f hf ℓ₀ => (hP f hf ℓ₀).trans (by rw [hPN]; simp)]
  have h5 := faceId_tendsto_five (b := fun j => faceIdFlag pp k (e (Fin.natAdd (0 + 1 + 1) j)))
    (Ms := (hS.shape pp M).MR) hm₀ (faceId_shape_MR_ge hS pp M hM) hk hPN hP1
  rw [← faceId_shape_pR hS pp M hpp] at h5
  simp only [faceId_prod_rest_bp hS pp M hpp] at h5
  simp only [FaceShape.faceIdRedVal, faceId_P0_eq]
  exact h5

/-- **A self-energy face with four rest lines** (`n = 6`, numerators without quartic part). -/
theorem faceId_tendsto_se_four (hPq : P.quart = 0) {α : Fin (0 + 1 + 1 + 3 + 1) → Fin 2 → ℝ}
    {e : Equiv.Perm (Fin (0 + 1 + 1 + 3 + 1))} (hS : FaceSort 0 3 α e)
    (pp : Fin (0 + 1 + 1 + 3 + 1) → Fin 4 → ℝ) (M : Fin (0 + 1 + 1 + 3 + 1) → ℝ)
    (huniq : ∀ l, α l = ![1, -1] ↔ l = FaceSort.gam (p := 0) (q := 3) e)
    (hQ : LoopDegLe 1 1 Q) (hQq : Q.quart = 0)
    (hM : ∀ l, α l = ![1, 0] → m₀ ≤ M l) (hpp : ∀ l, α l = ![1, 0] → pp l = 0 ∨ pp l = k)
    (hP : ∀ f, α f = ![0, 1] → ∀ ℓ₀ : Fin 4 → ℝ,
      Q.eval ![ℓ₀, (1 / 2 : ℝ) • (ℓ₀ + pp (FaceSort.gam (p := 0) (q := 3) e) - pp f)] = N ℓ₀) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun x => N x *
        ∏ l ∈ Finset.univ.filter (fun l => α l = ![1, 0]), (propDenom (M l) ε (pp l + x))⁻¹)
      (𝓝[>] 0) (𝓝 (I * (π : ℂ) ^ 2 * faceIdVal 6 (hS.shape pp M) Q)) := by
  rw [faceId_faceIdVal_se_sort hS pp M huniq hQ (Or.inr ⟨rfl, hQq⟩) hm₀ hM hk hpp (P := P)
    fun f hf ℓ₀ => (hP f hf ℓ₀).trans (by rw [hPN]; simp)]
  have h4 := faceId_tendsto_four (b := fun j => faceIdFlag pp k (e (Fin.natAdd (0 + 1 + 1) j)))
    (Ms := (hS.shape pp M).MR) hm₀ (faceId_shape_MR_ge hS pp M hM) hk hPq hPN hP1
  rw [← faceId_shape_pR hS pp M hpp] at h4
  simp only [faceId_prod_rest_bp hS pp M hpp] at h4
  simp only [FaceShape.faceIdRedVal, faceId_P0_eq]
  exact h4

end SEMink

/-! ### Vertex faces on the Minkowski side -/

theorem faceId_cTwoG_constQ (C : ℂ) (G : Matrix (Fin 2) (Fin 2) ℝ) (X : LoopIndex → ℂ) :
    cTwoG (faceIdConstQ C) G X = 0 := by
  simp [cTwoG, LoopQuartic.hess, LoopQuartic.quartSym, faceIdConstQ]

theorem faceId_cFourG_constQ (C : ℂ) (G : Matrix (Fin 2) (Fin 2) ℝ) :
    cFourG (faceIdConstQ C) G = 0 := by
  simp [cFourG, faceIdConstQ]

theorem faceId_evalC_constQ (C : ℂ) (X : LoopIndex → ℂ) : (faceIdConstQ C).evalC X = C := by
  simp [LoopQuartic.evalC, faceIdConstQ]

section VtxMink

variable {Q : LoopQuartic} {m₀ : ℝ} (hm₀ : 0 < m₀) {k : Fin 4 → ℝ}
  (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k)

include hm₀ hk

/-- **A vertex face with four rest lines** (`n = 7`): twice the face value is `(iπ²)⁻¹` times the
`ε → 0⁺` limit of the one-loop integrand `N(x) ∏_{rest} D_l(x)⁻¹`, where `N` is the half loop-`1`
Laplacian of `Q` on the slice `ℓ₁ = 0` (`faceIdLapF`). -/
theorem faceId_tendsto_vtx_four {N : (Fin 4 → ℝ) → ℂ} {P : LoopQuartic} (hPq : P.quart = 0)
    (hP1 : LoopDegLe 1 1 P) (hPN : ∀ ℓ, P.eval ℓ = N (ℓ 0))
    {α : Fin (1 + 1 + 1 + 3 + 1) → Fin 2 → ℝ} {e : Equiv.Perm (Fin (1 + 1 + 1 + 3 + 1))}
    (hS : FaceSort 1 3 α e) (pp : Fin (1 + 1 + 1 + 3 + 1) → Fin 4 → ℝ)
    (M : Fin (1 + 1 + 1 + 3 + 1) → ℝ) (hQ : LoopDegLe 1 2 Q)
    (hM : ∀ l, α l = ![1, 0] → m₀ ≤ M l) (hpp : ∀ l, α l = ![1, 0] → pp l = 0 ∨ pp l = k)
    (hL : ∀ ℓ₀ : Fin 4 → ℝ, faceIdLapF 1 Q.eval ![ℓ₀, 0] = N ℓ₀) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun x => N x *
        ∏ l ∈ Finset.univ.filter (fun l => α l = ![1, 0]), (propDenom (M l) ε (pp l + x))⁻¹)
      (𝓝[>] 0) (𝓝 (2 * I * (π : ℂ) ^ 2 * faceIdVal 7 (hS.shape pp M) Q)) := by
  rw [faceId_faceIdVal_vtx_lapF (hS.shape pp M) hQ (Or.inl rfl) (P := P)
    fun ℓ₀ => (hL ℓ₀).trans (by rw [hPN]; simp), faceId_volume_simplexSet_two]
  have h4 := faceId_tendsto_four (b := fun j => faceIdFlag pp k (e (Fin.natAdd (1 + 1 + 1) j)))
    (Ms := (hS.shape pp M).MR) hm₀ (faceId_shape_MR_ge hS pp M hM) hk hPq hPN hP1
  rw [← faceId_shape_pR hS pp M hpp] at h4
  simp only [faceId_prod_rest_bp hS pp M hpp] at h4
  have e2 : 2 * I * (π : ℂ) ^ 2 * (((1 / 2 : ℝ) : ℂ) * (hS.shape pp M).faceIdRedVal (7 - 3) P) =
      I * (π : ℂ) ^ 2 * (hS.shape pp M).faceIdRedVal 4 P := by
    push_cast
    ring
  rw [e2]
  simp only [FaceShape.faceIdRedVal, faceId_P0_eq]
  exact h4

/-- **A vertex face with three rest lines** (`n = 6`): the half loop-`1` Laplacian of `Q` on the
slice is a constant `C`; twice the face value is `(iπ²)⁻¹` times the limit of
`C ∏_{rest} D_l(x)⁻¹`. -/
theorem faceId_tendsto_vtx_three (C : ℂ) {α : Fin (1 + 1 + 1 + 2 + 1) → Fin 2 → ℝ}
    {e : Equiv.Perm (Fin (1 + 1 + 1 + 2 + 1))} (hS : FaceSort 1 2 α e)
    (pp : Fin (1 + 1 + 1 + 2 + 1) → Fin 4 → ℝ) (M : Fin (1 + 1 + 1 + 2 + 1) → ℝ)
    (hQ : LoopDegLe 1 2 Q) (hQq : Q.quart = 0)
    (hM : ∀ l, α l = ![1, 0] → m₀ ≤ M l) (hpp : ∀ l, α l = ![1, 0] → pp l = 0 ∨ pp l = k)
    (hL : ∀ ℓ₀ : Fin 4 → ℝ, faceIdLapF 1 Q.eval ![ℓ₀, 0] = C) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun x => C *
        ∏ l ∈ Finset.univ.filter (fun l => α l = ![1, 0]), (propDenom (M l) ε (pp l + x))⁻¹)
      (𝓝[>] 0) (𝓝 (2 * I * (π : ℂ) ^ 2 * faceIdVal 6 (hS.shape pp M) Q)) := by
  rw [faceId_faceIdVal_vtx_lapF (hS.shape pp M) hQ (Or.inr ⟨rfl, hQq⟩) (P := faceIdConstQ C)
    fun ℓ₀ => (hL ℓ₀).trans (faceId_eval_constQ C _).symm, faceId_volume_simplexSet_two]
  have h3 := faceId_tendsto_three (b := fun j => faceIdFlag pp k (e (Fin.natAdd (1 + 1 + 1) j)))
    (Ms := (hS.shape pp M).MR) hm₀ (faceId_shape_MR_ge hS pp M hM) hk C
  rw [← faceId_shape_pR hS pp M hpp] at h3
  simp only [faceId_prod_rest_bp hS pp M hpp] at h3
  have e2 : 2 * I * (π : ℂ) ^ 2 * (((1 / 2 : ℝ) : ℂ) *
      (hS.shape pp M).faceIdRedVal (6 - 3) (faceIdConstQ C)) =
      I * (π : ℂ) ^ 2 * (hS.shape pp M).faceIdRedVal 3 (faceIdConstQ C) := by
    push_cast
    ring
  rw [e2]
  simp only [FaceShape.faceIdRedVal, faceId_redBr_three (faceId_cTwoG_constQ C _ _)
    (faceId_cFourG_constQ C _), faceId_evalC_constQ]
  exact h3

end VtxMink

/-! ### Loop-`0` faces: the swapped data -/

section Loop0

variable {m : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ}

theorem faceId_filter_swapFlip_10 (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1]) :
    Finset.univ.filter (fun l => swapFlip α l = ![1, 0]) =
      Finset.univ.filter (fun l => α l = ![0, 1]) := by
  refine Finset.filter_congr fun l _ => ?_
  rcases hrow l with h | h | h
  · rw [swapFlip_row_10 h, h]
    exact ⟨fun h' => absurd h' row01_ne, fun h' => absurd h'.symm row01_ne⟩
  · rw [swapFlip_row_01 h, h]
    exact iff_of_true rfl rfl
  · rw [swapFlip_row_1m1 h, h]
    exact ⟨fun h' => absurd h' row1m1_ne, fun h' => absurd h'.symm row01_ne_row1m1⟩

theorem faceId_swapFlip_10_iff (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (l : Fin (m + 1)) : swapFlip α l = ![1, 0] ↔ α l = ![0, 1] := by
  have h := congrArg (l ∈ ·) (faceId_filter_swapFlip_10 hrow)
  simpa using h

theorem faceId_flipMom_of_row01 (pp : Fin (m + 1) → Fin 4 → ℝ) {l : Fin (m + 1)}
    (h : α l = ![0, 1]) : flipMom (photonSign α) pp l = pp l := by
  have hs : photonSign α l = 1 := by simp [photonSign, h]
  funext μ
  simp [flipMom, hs]

theorem faceId_hrow_swapFlip (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (l : Fin (m + 1)) :
    swapFlip α l = ![1, 0] ∨ swapFlip α l = ![0, 1] ∨ swapFlip α l = ![1, -1] := by
  rcases hrow l with h | h | h
  · exact Or.inr (Or.inl (swapFlip_row_10 h))
  · exact Or.inl (swapFlip_row_01 h)
  · exact Or.inr (Or.inr (swapFlip_row_1m1 h))

/-- The half loop-`1` Laplacian of the swapped numerator on the slice `ℓ₁ = 0` is the half
loop-`0` Laplacian of the numerator on the slice `ℓ₀ = 0`. -/
theorem faceId_lapF_swapQ (Q : LoopQuartic) (x : Fin 4 → ℝ) :
    faceIdLapF 1 (swapQ Q).eval ![x, 0] = faceIdLapF 0 Q.eval ![0, x] := by
  have h : (swapQ Q).eval = fun ℓ => Q.eval (ℓ ∘ lsw) := funext (faceId_eval_swapQ Q)
  have hc : (![x, 0] : Fin 2 → Fin 4 → ℝ) ∘ lsw = ![0, x] := by
    funext i
    fin_cases i <;> simp [lsw]
  rw [h, faceId_lapF_comp_lsw, hc]

end Loop0

end QED.GradedProof.RPi4

end
