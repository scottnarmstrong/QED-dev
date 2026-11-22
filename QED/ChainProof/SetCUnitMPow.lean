/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitMUnit

/-!
# Multi-denominator two-loop vertex units: powers of `k²` on the element line

Helper level for set (c) (stage L2). The element line of `repB`, `repD` carries powers `(k²)ⁿ` of
its momentum (from `Π(k²) ∝ k²` and the transverse tensor `k² g`). With the degree-four numerator
of the class these are outside the `LoopQuartic` engine, so each factor `k²` cancels one unscaled
extra denominator `D = k² + μ² - iε` of the element line:

`k² D⁻¹ = 1 - (μ² - iε) D⁻¹`.

* `unitMIntegrand_succ`: at `ε ≠ 0`, the integrand with `(k²)ⁿ⁺¹` and `r + 1` extra lines (the last
  one unscaled, mass `μ`) is the integrand with `(k²)ⁿ` and the first `r` extra lines minus
  `(μ² - iε)` times the integrand with `(k²)ⁿ` and all `r + 1`;
* **`unitM_pow`**: if the last `n` extra lines are unscaled (`TrailOne n κ`, `n ≤ r`), the unit
  with `(k²)ⁿ` is integrable at both stages for every `ε > 0` and has its `ε → 0⁺` limit;
* **`unitMLimitV_succ`**: the limits satisfy the same recursion, `L_{n+1} = L_n(init) - μ² L_n`,
  so every limit is an explicit linear combination of parametric (`n = 0`) limits;
* **`norm_unitMLimitV_pow_le`**: `‖L_n‖ ≤ C (1 + ∑ⱼ csⱼ²)ⁿ` for all masses `≥ μ₀` (polynomial
  growth in the extra masses, the form needed in a dispersion integral);
* **`continuousOn_unitMLimitV_pow`**: continuity along families of masses `≥ μ₀`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.ChainProof.SetCUnitM

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassIntegrable
open QED.TwoLoop.ClassLimit QED.ChainProof.SetCUnit
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix class5LoopMatrixPV)

/-! ### Linearity of the joint energy-first integral -/

section Linear

variable {F G : (Fin 2 → Fin 4 → ℝ) → ℂ}

theorem jointEnergyFirstIntegrable_sub_mul (hF : QED.TwoLoop.jointEnergyFirstIntegrable 2 F)
    (hG : QED.TwoLoop.jointEnergyFirstIntegrable 2 G) (a : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (fun ℓ => F ℓ - a * G ℓ) ∧
      QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => F ℓ - a * G ℓ) =
        QED.TwoLoop.jointEnergyFirstIntegral 2 F -
          a * QED.TwoLoop.jointEnergyFirstIntegral 2 G := by
  obtain ⟨hF1, hF2⟩ := hF
  obtain ⟨hG1, hG2⟩ := hG
  have hin : ∀ v : Fin 2 → Fin 3 → ℝ,
      (∫ t : Fin 2 → ℝ, F (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) -
          a * G (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))) =
        (∫ t : Fin 2 → ℝ, F fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) -
          a * ∫ t : Fin 2 → ℝ, G fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ) := fun v => by
    rw [integral_sub (hF1 v) ((hG1 v).const_mul a), integral_const_mul]
  refine ⟨⟨fun v => (hF1 v).sub ((hG1 v).const_mul a), ?_⟩, ?_⟩
  · simp only [hin]
    exact hF2.sub (hG2.const_mul a)
  · unfold QED.TwoLoop.jointEnergyFirstIntegral
    simp only [hin]
    rw [integral_sub hF2 (hG2.const_mul a), integral_const_mul]

end Linear

/-! ### Dropping the last extra line -/

section Drop

variable {r : ℕ}

theorem mExt_castSucc {X : Type*} (x : Fin 8 → X) (y : Fin (r + 1) → X) (i : Fin (r + 8)) :
    mExt x y (Fin.castSucc i) = mExt x (Fin.init y) i := by
  unfold mExt Fin.init
  by_cases h : (i : ℕ) < 8
  · simp [h]
  · simp only [Fin.val_castSucc, h, dite_false]
    rfl

theorem mExtra_last : mExtra (r + 1) (Fin.last r) = Fin.last (r + 8) :=
  Fin.ext (by simp [mExtra])

theorem lineDenom_congr {n n' : ℕ} {α : Fin (n + 1) → Fin 2 → ℝ} {α' : Fin (n' + 1) → Fin 2 → ℝ}
    {p : Fin (n + 1) → Fin 4 → ℝ} {p' : Fin (n' + 1) → Fin 4 → ℝ} {M : Fin (n + 1) → ℝ}
    {M' : Fin (n' + 1) → ℝ} {i : Fin (n + 1)} {i' : Fin (n' + 1)} (hα : α i = α' i')
    (hp : p i = p' i') (hM : M i = M' i') (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineDenom α p M ε i ℓ = lineDenom α' p' M' ε i' ℓ := by
  have hk : QED.Integration.TwoLoop.lineMomentum α p i ℓ =
      QED.Integration.TwoLoop.lineMomentum α' p' i' ℓ := by
    unfold QED.Integration.TwoLoop.lineMomentum
    rw [hα, hp]
  simp only [lineDenom, hk, hM]

theorem lineDenom_unitM_castSucc (c : Class5) (s : Fin 8) (κ : Fin (r + 1) → ℝ)
    (p p' : Fin 4 → ℝ) (m a A b B : ℝ) (cs : Fin (r + 1) → ℝ) (ε : ℝ) (i : Fin (r + 8))
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineDenom (unitMMatrix c s κ) (unitMMomenta c s κ p p') (unitMMasses m a A b B cs) ε
        (Fin.castSucc i) ℓ =
      lineDenom (unitMMatrix c s (Fin.init κ)) (unitMMomenta c s (Fin.init κ) p p')
        (unitMMasses m a A b B (Fin.init cs)) ε i ℓ := by
  refine lineDenom_congr ?_ ?_ ?_ ε ℓ <;>
    simp only [unitMMatrix, unitMMomenta, unitMMasses, mScale, mLine, mExt_castSucc] <;> rfl

/-- **One factor `k²` cancels the last extra denominator.** At `ε ≠ 0`, with the last extra line
unscaled: `(k²)ⁿ⁺¹ ∏_{r+1} D⁻¹ = (k²)ⁿ ∏_r D⁻¹ - (μ² - iε) (k²)ⁿ ∏_{r+1} D⁻¹`, `μ` its mass. -/
theorem unitMIntegrand_succ (c : Class5) (P : Params) (s : Fin 8) {κ : Fin (r + 1) → ℝ}
    (hκ : κ (Fin.last r) = 1) (m a A b B : ℝ) (cs : Fin (r + 1) → ℝ) {ε : ℝ} (hε : ε ≠ 0)
    (p p' : Fin 4 → ℝ) (n : ℕ) (μ i j : Fin 4) :
    unitMIntegrand c P s κ (unitMMasses m a A b B cs) ε p p' (n + 1) μ i j =
      fun ℓ => unitMIntegrand c P s (Fin.init κ) (unitMMasses m a A b B (Fin.init cs)) ε p p' n
          μ i j ℓ -
        (((cs (Fin.last r) ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) *
          unitMIntegrand c P s κ (unitMMasses m a A b B cs) ε p p' n μ i j ℓ := by
  funext ℓ
  have hprod : ∀ f : Fin (r + 1 + 8) → ℂ,
      ∏ k, f k = (∏ k : Fin (r + 8), f (Fin.castSucc k)) * f (Fin.last (r + 8)) :=
    fun f => Fin.prod_univ_castSucc f
  have hlast := lineDenom_unitM_mExtra c s κ p p' m a A b B cs ε (Fin.last r) ℓ
  rw [mExtra_last, hκ] at hlast
  simp only [unitMIntegrand, hprod, lineDenom_unitM_castSucc, hlast]
  set D : ℂ := ((1 ^ 2 * Minkowski.dot (elemMom c s p p' ℓ) (elemMom c s p p' ℓ) +
    cs (Fin.last r) ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I with hD
  have hD0 : D ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp only [hD, Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, Complex.zero_im] at this
    exact hε (by linarith)
  have he : elemSq c s p p' ℓ = D - (((cs (Fin.last r) ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) := by
    simp only [hD, elemSq]
    push_cast
    ring
  rw [pow_succ, he]
  field_simp

end Drop

/-! ### The powers -/

/-- The last `n` of the `r` extra lines are unscaled. -/
def TrailOne {r : ℕ} (n : ℕ) (κ : Fin r → ℝ) : Prop := ∀ j : Fin r, r ≤ (j : ℕ) + n → κ j = 1

theorem TrailOne.init {r n : ℕ} {κ : Fin (r + 1) → ℝ} (h : TrailOne (n + 1) κ) :
    TrailOne n (Fin.init κ) := fun j hj => h (Fin.castSucc j) (by simp; omega)

theorem TrailOne.of_succ {r n : ℕ} {κ : Fin r → ℝ} (h : TrailOne (n + 1) κ) : TrailOne n κ :=
  fun j hj => h j (by omega)

theorem TrailOne.last {r n : ℕ} {κ : Fin (r + 1) → ℝ} (h : TrailOne (n + 1) κ) :
    κ (Fin.last r) = 1 := h _ (by simp)

theorem ExtraGe.init {r : ℕ} {μ₀ : ℝ} {κ cs : Fin (r + 1) → ℝ} (h : ExtraGe μ₀ κ cs) :
    ExtraGe μ₀ (Fin.init κ) (Fin.init cs) := fun j => h (Fin.castSucc j)

section Pow

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {s : Fin 8}
  (hs : 4 ≤ (s : ℕ)) {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
  {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
include hc hm hs hμ₀ hM hp hp' hq

/-- **The `ε → 0⁺` limit with powers of `k²`.** If the last `n ≤ r` extra lines are unscaled, the
unit with `(k²)ⁿ` is integrable at both stages for every `ε > 0` and converges as `ε → 0⁺`. -/
theorem unitM_pow (n : ℕ) : ∀ {r : ℕ} {κ cs : Fin r → ℝ}, n ≤ r → TrailOne n κ →
    ExtraGe μ₀ κ cs →
    (∀ ε, 0 < ε → ∀ μ i j, QED.TwoLoop.jointEnergyFirstIntegrable 2
      (unitMIntegrand c P s κ (unitMMasses P.m a A b B cs) ε p p' n μ i j)) ∧
    ∀ μ i j, Tendsto (fun ε => unitMValue c P s κ (unitMMasses P.m a A b B cs) ε p p' n μ i j)
      (𝓝[>] 0) (𝓝 (unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' n μ i j)) := by
  induction n with
  | zero =>
    intro r κ cs _ _ hX
    exact ⟨fun ε hε μ i j => jointEnergyFirstIntegrable_unitM hc P s hX.ne_zero _ p p' hε μ i j,
      fun μ i j => tendsto_unitMLimitV hc P hm hs hμ₀ hM hX hp hp' hq μ i j⟩
  | succ n ih =>
    intro r κ cs hnr hT hX
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    obtain ⟨hI₁, hI₂⟩ := ih (by omega) hT.init hX.init
    obtain ⟨hF₁, hF₂⟩ := ih (by omega) hT.of_succ hX
    have hstep : ∀ ε, 0 < ε → ∀ μ i j,
        QED.TwoLoop.jointEnergyFirstIntegrable 2
          (unitMIntegrand c P s κ (unitMMasses P.m a A b B cs) ε p p' (n + 1) μ i j) ∧
        unitMValue c P s κ (unitMMasses P.m a A b B cs) ε p p' (n + 1) μ i j =
          unitMValue c P s (Fin.init κ) (unitMMasses P.m a A b B (Fin.init cs)) ε p p' n μ i j -
            (((cs (Fin.last r) ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) *
              unitMValue c P s κ (unitMMasses P.m a A b B cs) ε p p' n μ i j := by
      intro ε hε μ i j
      have h := jointEnergyFirstIntegrable_sub_mul (hI₁ ε hε μ i j) (hF₁ ε hε μ i j)
        (((cs (Fin.last r) ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)
      unfold unitMValue
      rw [unitMIntegrand_succ c P s hT.last P.m a A b B cs hε.ne' p p' n μ i j]
      exact h
    refine ⟨fun ε hε μ i j => (hstep ε hε μ i j).1, fun μ i j => ?_⟩
    have hlim : Tendsto (fun ε => unitMValue c P s κ (unitMMasses P.m a A b B cs) ε p p' (n + 1)
        μ i j) (𝓝[>] 0)
        (𝓝 (unitMLimitV c P s (Fin.init κ) (unitMMasses P.m a A b B (Fin.init cs)) p p' n μ i j -
          (((cs (Fin.last r) ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I) *
            unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' n μ i j)) := by
      have hc' : Tendsto (fun ε : ℝ => ((cs (Fin.last r) ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) (𝓝[>] 0)
          (𝓝 (((cs (Fin.last r) ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I)) :=
        ((continuous_const.sub (continuous_ofReal.mul continuous_const)).tendsto 0).mono_left
          nhdsWithin_le_nhds
      refine ((hI₂ μ i j).sub (hc'.mul (hF₂ μ i j))).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      exact (hstep ε hε μ i j).2.symm
    have e := hlim.limUnder_eq
    simp only [unitMLimitV, Matrix.of_apply] at e ⊢
    rw [e]
    exact hlim

/-- **The recursion of the limits**: with the last extra line unscaled, of mass `μ`,
`L_{n+1} = L_n(first r extra lines) - μ² L_n`. -/
theorem unitMLimitV_succ {r n : ℕ} {κ cs : Fin (r + 1) → ℝ} (hnr : n + 1 ≤ r + 1)
    (hT : TrailOne (n + 1) κ) (hX : ExtraGe μ₀ κ cs) (μ i j : Fin 4) :
    unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' (n + 1) μ i j =
      unitMLimitV c P s (Fin.init κ) (unitMMasses P.m a A b B (Fin.init cs)) p p' n μ i j -
        (cs (Fin.last r) ^ 2 : ℝ) * unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' n μ i j
    := by
  have hS := (unitM_pow hc P hm hs hμ₀ hM hp hp' hq (n + 1) hnr hT hX).2 μ i j
  have hI := (unitM_pow hc P hm hs hμ₀ hM hp hp' hq n (by omega) hT.init hX.init).2 μ i j
  have hF := (unitM_pow hc P hm hs hμ₀ hM hp hp' hq n (by omega) hT.of_succ hX).2 μ i j
  have hc' : Tendsto (fun ε : ℝ => ((cs (Fin.last r) ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) (𝓝[>] 0)
      (𝓝 (((cs (Fin.last r) ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I)) :=
    ((continuous_const.sub (continuous_ofReal.mul continuous_const)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  rw [ofReal_zero, zero_mul, sub_zero] at hc'
  refine tendsto_nhds_unique hS ((hI.sub (hc'.mul hF)).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have h := jointEnergyFirstIntegrable_sub_mul
    ((unitM_pow hc P hm hs hμ₀ hM hp hp' hq n (by omega) hT.init hX.init).1 ε hε μ i j)
    ((unitM_pow hc P hm hs hμ₀ hM hp hp' hq n (by omega) hT.of_succ hX).1 ε hε μ i j)
    (((cs (Fin.last r) ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)
  unfold unitMValue
  rw [unitMIntegrand_succ c P s hT.last P.m a A b B cs hε.ne' p p' n μ i j]
  exact h.2.symm

end Pow

/-! ### Uniformity in the masses -/

/-- **Polynomial growth in the extra masses.** If the last `n ≤ r` extra lines are unscaled,
`‖L_n‖ ≤ C (1 + ∑ⱼ csⱼ²)ⁿ` for all photon masses and extra masses `≥ μ₀` (the scales fixed). -/
theorem norm_unitMLimitV_pow_le {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (μ i j : Fin 4) (n : ℕ) :
    ∀ {r : ℕ} {κ : Fin r → ℝ}, n ≤ r → TrailOne n κ → (∀ j, 0 < κ j ∧ κ j ≤ 1) →
    ∃ C : ℝ, ∀ (a A b B : ℝ) (cs : Fin r → ℝ), MassesGe μ₀ a A b B → (∀ j, μ₀ ≤ cs j) →
      ‖unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' n μ i j‖ ≤
        C * (1 + ∑ j, cs j ^ 2) ^ n := by
  induction n with
  | zero =>
    intro r κ _ _ hκ
    obtain ⟨C, hC⟩ := norm_unitMLimitV_le hc P hm hs hμ₀ hκ hp hp' hq μ i j
    exact ⟨C, fun a A b B cs hM hcs => by simpa using hC a A b B cs hM hcs⟩
  | succ n ih =>
    intro r κ hnr hT hκ
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    obtain ⟨C₁, hC₁⟩ := ih (r := r) (κ := Fin.init κ) (by omega) hT.init fun j => hκ _
    obtain ⟨C₂, hC₂⟩ := ih (r := r + 1) (κ := κ) (by omega) hT.of_succ hκ
    refine ⟨|C₁| + |C₂|, fun a A b B cs hM hcs => ?_⟩
    have hX : ExtraGe μ₀ κ cs := fun j => ⟨(hκ j).1, (hκ j).2, hcs j⟩
    rw [unitMLimitV_succ hc P hm hs hμ₀ hM hp hp' hq hnr hT hX]
    set S := ∑ j, cs j ^ 2 with hS
    have hS₁ : ∑ j, Fin.init cs j ^ 2 + cs (Fin.last r) ^ 2 = S := by
      rw [hS, Fin.sum_univ_castSucc]
      rfl
    have hS₁0 : 0 ≤ ∑ j, Fin.init cs j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hl0 : 0 ≤ cs (Fin.last r) ^ 2 := sq_nonneg _
    have h1 := hC₁ a A b B (Fin.init cs) hM fun j => hcs _
    have h2 := hC₂ a A b B cs hM hcs
    have hpow₁ : (1 + ∑ j, Fin.init cs j ^ 2) ^ n ≤ (1 + S) ^ n :=
      pow_le_pow_left₀ (by positivity) (by linarith) n
    have hpow : (1 + S) ^ n ≤ (1 + S) ^ (n + 1) :=
      pow_le_pow_right₀ (by linarith) (Nat.le_succ n)
    have hP0 : 0 ≤ (1 + S) ^ n := pow_nonneg (by linarith) n
    have hn1 : ‖unitMLimitV c P s (Fin.init κ) (unitMMasses P.m a A b B (Fin.init cs)) p p' n μ
        i j‖ ≤ |C₁| * (1 + S) ^ (n + 1) :=
      h1.trans ((mul_le_mul_of_nonneg_left hpow₁ (abs_nonneg _)).trans'
        (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg (by positivity) n)) |>.trans
        (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)))
    have hn2 : ‖((cs (Fin.last r) ^ 2 : ℝ) : ℂ) *
        unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' n μ i j‖ ≤
          |C₂| * (1 + S) ^ (n + 1) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hl0, pow_succ]
      have h3 : C₂ * (1 + S) ^ n ≤ |C₂| * (1 + S) ^ n :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hP0
      have h4 : cs (Fin.last r) ^ 2 ≤ 1 + S := by linarith
      calc cs (Fin.last r) ^ 2 * ‖unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' n μ i j‖
          ≤ (1 + S) * (|C₂| * (1 + S) ^ n) :=
            mul_le_mul h4 (h2.trans h3) (norm_nonneg _) (by linarith)
        _ = |C₂| * ((1 + S) ^ n * (1 + S)) := by ring
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ |C₁| * (1 + S) ^ (n + 1) + |C₂| * (1 + S) ^ (n + 1) := add_le_add hn1 hn2
      _ = (|C₁| + |C₂|) * (1 + S) ^ (n + 1) := by ring

/-- **Continuity in the masses with powers of `k²`**: along any family of photon and extra masses
`≥ μ₀`, continuous on `s'`, the limit `L_n` is continuous on `s'` (the scales fixed, the last
`n ≤ r` extra lines unscaled). -/
theorem continuousOn_unitMLimitV_pow {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {s : Fin 8}
    (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {s' : Set X} {a A b B : X → ℝ}
    (ha : ContinuousOn a s') (hA : ContinuousOn A s') (hb : ContinuousOn b s')
    (hB : ContinuousOn B s') (hM : ∀ t ∈ s', MassesGe μ₀ (a t) (A t) (b t) (B t))
    (μ i j : Fin 4) (n : ℕ) :
    ∀ {r : ℕ} {κ : Fin r → ℝ} {cs : X → Fin r → ℝ}, n ≤ r → TrailOne n κ →
      (∀ j, 0 < κ j ∧ κ j ≤ 1) → (∀ j, ContinuousOn (fun t => cs t j) s') →
      (∀ t ∈ s', ∀ j, μ₀ ≤ cs t j) →
      ContinuousOn (fun t => unitMLimitV c P s κ
        (unitMMasses P.m (a t) (A t) (b t) (B t) (cs t)) p p' n μ i j) s' := by
  induction n with
  | zero =>
    intro r κ cs _ _ hκ hcs hcs0
    exact continuousOn_unitMLimitV hc P hm hs hμ₀ hκ hp hp' hq ha hA hb hB hcs hM hcs0 μ i j
  | succ n ih =>
    intro r κ cs hnr hT hκ hcs hcs0
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have h₁ := ih (r := r) (κ := Fin.init κ) (cs := fun t => Fin.init (cs t)) (by omega) hT.init
      (fun j => hκ _) (fun j => hcs _) fun t ht j => hcs0 t ht _
    have h₂ := ih (r := r + 1) (κ := κ) (cs := cs) (by omega) hT.of_succ hκ hcs hcs0
    have hl : ContinuousOn (fun t => ((cs t (Fin.last r) ^ 2 : ℝ) : ℂ)) s' :=
      continuous_ofReal.comp_continuousOn ((hcs _).pow 2)
    refine (h₁.sub (hl.mul h₂)).congr fun t ht => ?_
    exact unitMLimitV_succ hc P hm hs hμ₀ (hM t ht) hp hp' hq hnr hT
      (fun j => ⟨(hκ j).1, (hκ j).2, hcs0 t ht j⟩) μ i j

end QED.ChainProof.SetCUnitM

end
