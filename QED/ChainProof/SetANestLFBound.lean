/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetANestLFBoundPV
public import QED.ChainProof.SetANestLBubble

/-!
# Set (a), obligation (N): the inner bound for the block-summed `δ₂, δ_m` bubble

Helper level for obligation (N) of `QED.ChainProof.SetAPauli.SetALimitLink`: the hypothesis
`OneLoopInnerBound` of `QED.ChainProof.SetANest.loopNested_of_lOuter` for the fermion-counterterm
classes `FA`, `FB`, whose inner integrand is the block-summed inserted bubble
`∑_f c_f K insG(d₂(rep f), d_m(rep f), M_f; σ k + q, q)` (counterterm on the unshifted line).

* `exists_norm_sum_insCF_le`: for a three-flavour Pauli–Villars set, the flavour sum of the closed
  forms is at most `C (1 + ‖p‖)⁸ (1 + ‖v⃗‖)⁻⁴`, uniformly in the Feynman parameter;
* `exists_norm_integral_sum_insG_le`: the same bound for the energy integral of the flavour sum;
* **`oneLoopInnerBound_insBubble`**: under the mass floor and the Pauli–Villars block conditions,
  at `ε > 0`, the block-summed bubble satisfies `OneLoopInnerBound 8 4` (three-flavour reduction
  `QED.GradedProof.VP2.sum_block_eq_sum_triple`; both stages from
  `QED.GradedProof.VP2.ef_insBubble`; joint measurability from continuity).
-/

@[expose] public section

open Complex MeasureTheory Set

namespace QED.ChainProof.SetANest

open QED.GradedProof.VP2 QED.TwoLoop.Bridge QED.TwoLoop.VPHalfAtLimit
open QED.WickModel.SelfEnergyLimit (massW)

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-- The constant of `rpow_key`. -/
noncomputable def insCk (ε σ : ℝ) : ℝ :=
  5 ^ 4 * 4 ^ 4 * ε ^ (-(σ + 2)) + 2 ^ 4 * (2 / 9 : ℝ) ^ (-(σ + 2))

theorem insCk_nonneg {ε : ℝ} (hε : 0 < ε) (σ : ℝ) : 0 ≤ insCk ε σ := by
  unfold insCk; positivity

theorem norm_mul_insS_le {ε : ℝ} (hε : 0 < ε) (M : ℝ) (p : Fin 4 → ℝ) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (v : Fin 3 → ℝ) {n : ℕ} (hn : n ≤ 4) {σ : ℝ}
    (hσ : 2 * σ = n + 1) {a S : ℂ} {K D : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D)
    (ha : ‖a‖ ≤ K * (1 + ‖p‖ + ‖v‖) ^ n)
    (hS : ‖S‖ ≤ D * (max ε (massW M M p u v)) ^ (-(σ + 2))) :
    ‖a * S‖ ≤ K * D * insCk ε σ * (1 + ‖p‖) ^ 8 * ((1 + ‖v‖) ^ 4)⁻¹ := by
  have hkey := rpow_key hε M p hu v hn hσ
  rw [norm_mul]
  calc ‖a‖ * ‖S‖ ≤ (K * (1 + ‖p‖ + ‖v‖) ^ n) * (D * (max ε (massW M M p u v)) ^ (-(σ + 2))) :=
        mul_le_mul ha hS (norm_nonneg _) (by positivity)
    _ = K * D * ((1 + ‖p‖ + ‖v‖) ^ n * (max ε (massW M M p u v)) ^ (-(σ + 2))) := by ring
    _ ≤ K * D * (insCk ε σ * (1 + ‖p‖) ^ 8 * ((1 + ‖v‖) ^ 4)⁻¹) :=
        mul_le_mul_of_nonneg_left hkey (mul_nonneg hK hD)
    _ = _ := by ring

section Triple

variable {A B : Mat} (hA : IsOddG A) (hB : IsOddG B) (d₂ dm : ℝ) {ε : ℝ} (hε : 0 < ε)
  (cs Ms : Fin 3 → ℝ) (hc : ∑ i, cs i = 0) (hcM : ∑ i, cs i * Ms i ^ 2 = 0)
  (hle : ∀ i, Ms 0 ^ 2 ≤ Ms i ^ 2)

include hε hc hcM hle in
/-- **The Pauli–Villars sum of the closed forms**, uniformly in the Feynman parameter. -/
theorem exists_norm_sum_insCF_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ p u v, u ∈ Icc (0 : ℝ) 1 →
    ‖∑ i, (cs i : ℂ) * insCF A B d₂ dm (Ms i) ε p u v‖ ≤
      C * (1 + ‖p‖) ^ 8 * ((1 + ‖v‖) ^ 4)⁻¹ := by
  obtain ⟨K5, hK5, h5⟩ := insBd_a5 A B d₂ dm ε hε.le
  obtain ⟨K3, hK3, h3⟩ := insBd_a3 A B d₂ dm ε hε.le
  obtain ⟨K1, hK1, h1⟩ := insBd_a1 A B d₂ dm
  have hCP : 0 ≤ insCPV cs Ms := Finset.sum_nonneg fun i _ => by positivity
  set D5 := 5 / 2 * (5 / 2 + 1) * insCPV cs Ms
  set D3 := 3 / 2 * (3 / 2 + 1) * insCPV cs Ms
  set D1 := 1 / 2 * (1 / 2 + 1) * insCPV cs Ms
  have hD5 : 0 ≤ D5 := mul_nonneg (by norm_num) hCP
  have hD3 : 0 ≤ D3 := mul_nonneg (by norm_num) hCP
  have hD1 : 0 ≤ D1 := mul_nonneg (by norm_num) hCP
  have hk := insCk_nonneg hε
  refine ⟨K5 * D5 * insCk ε (5 / 2) + K3 * D3 * insCk ε (3 / 2) + K1 * D1 * insCk ε (1 / 2),
    add_nonneg (add_nonneg (mul_nonneg (mul_nonneg hK5 hD5) (hk _))
      (mul_nonneg (mul_nonneg hK3 hD3) (hk _))) (mul_nonneg (mul_nonneg hK1 hD1) (hk _)),
    fun p u v hu => ?_⟩
  rw [sum_insCF_eq d₂ dm hε cs Ms p u v, norm_neg]
  have t5 := norm_mul_insS_le hε (Ms 0) p hu v (n := 4) le_rfl (σ := 5 / 2) (by norm_num) hK5
    hD5 (h5 p u v hu) (norm_insS_le hε cs Ms hc hcM hle (by norm_num) p u v)
  have t3 := norm_mul_insS_le hε (Ms 0) p hu v (n := 2) (by norm_num) (σ := 3 / 2) (by norm_num)
    hK3 hD3 (h3 p u v hu) (norm_insS_le hε cs Ms hc hcM hle (by norm_num) p u v)
  have t1 := norm_mul_insS_le hε (Ms 0) p hu v (n := 0) (by norm_num) (σ := 1 / 2) (by norm_num)
    hK1 hD1 (h1 p u v hu) (norm_insS_le hε cs Ms hc hcM hle (by norm_num) p u v)
  refine (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add t5 t3)) t1).trans
    (le_of_eq ?_))
  ring

include hA hB hε hc hcM hle in
/-- **The energy integral of the Pauli–Villars sum** is at most
`C (1 + ‖p‖)⁸ (1 + ‖v⃗‖)⁻⁴`. -/
theorem exists_norm_integral_sum_insG_le : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (p : Fin 4 → ℝ) (v : Fin 3 → ℝ),
    ‖∫ t : ℝ, ∑ i, (cs i : ℂ) * insG A B d₂ dm (Ms i) ε (p + Fin.cons t v) (Fin.cons t v)‖ ≤
      C * (1 + ‖p‖) ^ 8 * ((1 + ‖v‖) ^ 4)⁻¹ := by
  obtain ⟨C, hC, h⟩ := exists_norm_sum_insCF_le d₂ dm hε cs Ms hc hcM hle (A := A) (B := B)
  set V := (volume.restrict (Ioc (0 : ℝ) 1)).real univ
  have hV : 0 ≤ V := measureReal_nonneg
  refine ⟨2 * C * V, by positivity, fun p v => ?_⟩
  rw [integral_finsetSum _ fun i _ =>
    (integrable_insG_time hA hB d₂ dm (Ms i) hε p v).const_mul _]
  simp only [integral_const_mul, integral_insG_time hA hB d₂ dm _ hε p v]
  simp only [← integral_const_mul]
  rw [← integral_finsetSum _ fun i _ =>
    (integrableOn_insCF hA hB d₂ dm (Ms i) hε p v).const_mul _]
  have hb := norm_integral_le_of_norm_le_const (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (f := fun u => ∑ i, (cs i : ℂ) * (2 * (1 - (u : ℂ)) * insCF A B d₂ dm (Ms i) ε p u v))
    (C := 2 * (C * (1 + ‖p‖) ^ 8 * ((1 + ‖v‖) ^ 4)⁻¹))
    ((ae_restrict_mem measurableSet_Ioc).mono fun u hu => by
      have e : ∑ i, (cs i : ℂ) * (2 * (1 - (u : ℂ)) * insCF A B d₂ dm (Ms i) ε p u v) =
          2 * (1 - (u : ℂ)) * ∑ i, (cs i : ℂ) * insCF A B d₂ dm (Ms i) ε p u v := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e, norm_mul]
      have h2 : ‖2 * (1 - (u : ℂ))‖ ≤ 2 := by
        rw [norm_mul, show (1 : ℂ) - u = ((1 - u : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_of_nonneg (by linarith [hu.2])]
        norm_num
        linarith [hu.1]
      exact mul_le_mul h2 (h p u v (Ioc_subset_Icc_self hu)) (norm_nonneg _) (by norm_num))
  refine hb.trans (le_of_eq ?_)
  ring

end Triple

/-! ### Continuity -/

theorem insContinuous_slash : Continuous Dirac.slash := by
  have hl : ∀ μ, Continuous fun p : Fin 4 → ℝ => Minkowski.lower p μ := fun μ => by
    simp only [Minkowski.lower_eq]
    fin_cases μ <;> simp <;> fun_prop
  unfold Dirac.slash
  exact continuous_finsetSum _ fun μ _ =>
    (continuous_ofReal.comp (hl μ)).smul continuous_const

theorem insContinuous_dot : Continuous fun y : Fin 4 → ℝ => Minkowski.dot y y := by
  simp only [Minkowski.dot_eq]
  fun_prop

theorem continuous_insG {A B : Mat} (hA : IsOddG A) (hB : IsOddG B) (d₂ dm M : ℝ) {ε : ℝ}
    (hε : ε ≠ 0) {X : Type*} [TopologicalSpace X] {f g : X → Fin 4 → ℝ} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => insG A B d₂ dm M ε (f x) (g x) := by
  have hs := insContinuous_slash
  have hτ : Continuous fun x => insTau A B (f x) (g x) := by
    unfold insTau
    exact (continuous_const.matrix_mul ((hs.comp hf).matrix_mul
      (continuous_const.matrix_mul (hs.comp hg)))).matrix_trace
  have hd : ∀ h : X → Fin 4 → ℝ, Continuous h →
      Continuous fun x => (propDenom M ε (h x))⁻¹ := fun h hh => by
    refine Continuous.inv₀ ?_ fun x => propDenom_ne_zero hε _
    unfold propDenom
    exact (continuous_ofReal.comp ((insContinuous_dot.comp hh).add continuous_const)).sub
      continuous_const
  have hdot := continuous_ofReal.comp (insContinuous_dot.comp hg)
  simp only [insG, insTr_eq_tau hA hB]
  exact (((((continuous_const.mul hdot).mul hτ).add (continuous_const.mul
    (((continuous_const.mul hdot).mul continuous_const).add (continuous_const.mul hτ)))).add
    continuous_const).mul (hd _ hf)).mul ((hd _ hg).pow 2)

/-! ### The inner bound -/

theorem insZk_true (k q : Fin 4 → ℝ) : zk k true q = k + q := rfl

theorem insZk_false (k q : Fin 4 → ℝ) : zk k false q = q := rfl

section Bound

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)
  {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  (d₂ dm : F → ℝ) {ε : ℝ} (hε : 0 < ε) (K : ℂ)

/-- The block-summed inserted bubble at photon momentum `σ k` (counterterm on the line `q`). -/
noncomputable def insBubble (A B : Fin 4 → Fin 4 → Mat) (σ : ℝ) (k q : Fin 4 → ℝ)
    (a b : Fin 4) : ℂ :=
  ∑ f, (Φ.coeff f : ℂ) * (K * insG (A a b) (B a b) (d₂ (rep f)) (dm (rep f)) (Φ.mass f) ε
    (zk (σ • k) true q) (zk (σ • k) false q))

include hm₀ hmass hrep hPV₁ hPV₂ hε in
theorem insBubble_time_bound {A B : Mat} (hA : IsOddG A) (hB : IsOddG B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Fin 4 → ℝ) (v : Fin 3 → ℝ),
      ‖∫ t : ℝ, ∑ f, (Φ.coeff f : ℂ) * (K * insG A B (d₂ (rep f)) (dm (rep f)) (Φ.mass f) ε
        (p + Fin.cons t v) (Fin.cons t v))‖ ≤ C * (1 + ‖p‖) ^ 8 * ((1 + ‖v‖) ^ 4)⁻¹ := by
  set X := heavyX Φ
  have hX1 : 1 ≤ X := by
    have := Finset.sum_nonneg fun g (_ : g ∈ Finset.univ) => (hm₀.trans_le (hmass g)).le
    simp only [X, heavyX]
    linarith
  have hXY : X ^ 2 - (X + 1) ^ 2 ≠ 0 := by nlinarith
  have htri : ∀ f, ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Fin 4 → ℝ) (v : Fin 3 → ℝ),
      ‖∫ t : ℝ, ∑ i, ((![1, triA (Φ.mass f) X (X + 1), triB (Φ.mass f) X (X + 1)] i : ℝ) : ℂ) *
        insG A B (d₂ (rep f)) (dm (rep f)) (![Φ.mass f, X, X + 1] i) ε (p + Fin.cons t v)
          (Fin.cons t v)‖ ≤ C * (1 + ‖p‖) ^ 8 * ((1 + ‖v‖) ^ 4)⁻¹ := fun f => by
    obtain ⟨h0, h1⟩ := mass_lt_heavyX Φ hm₀ hmass f
    refine exists_norm_integral_sum_insG_le hA hB _ _ hε _ _ ?_ ?_ ?_
    · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      exact triA_triB_pv₁ _ _ _ hXY
    · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      linarith [triA_triB_pv₂ (Φ.mass f) X (X + 1) hXY]
    · intro i
      fin_cases i <;> simp <;> nlinarith
  choose C hC0 hC using htri
  refine ⟨∑ f, ‖(Φ.coeff f : ℂ) * K‖ * C f, Finset.sum_nonneg fun f _ =>
    mul_nonneg (norm_nonneg _) (hC0 f), fun p v => ?_⟩
  have hpt : ∀ t : ℝ, ∑ f, (Φ.coeff f : ℂ) * (K * insG A B (d₂ (rep f)) (dm (rep f))
      (Φ.mass f) ε (p + Fin.cons t v) (Fin.cons t v)) =
      ∑ f, ((Φ.coeff f : ℂ) * K) * ∑ i,
        ((![1, triA (Φ.mass f) X (X + 1), triB (Φ.mass f) X (X + 1)] i : ℝ) : ℂ) *
        insG A B (d₂ (rep f)) (dm (rep f)) (![Φ.mass f, X, X + 1] i) ε (p + Fin.cons t v)
          (Fin.cons t v) := fun t => by
    rw [sum_block_eq_sum_triple Φ rep hrep hPV₁ hPV₂ X (X + 1)
      (fun r M => K * insG A B (d₂ r) (dm r) M ε (p + (Fin.cons t v : Fin 4 → ℝ))
        (Fin.cons t v))]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun f _ => (integrable_finsetSum _ fun i _ =>
    (integrable_insG_time hA hB _ _ _ hε p v).const_mul _).const_mul _]
  simp only [integral_const_mul]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun f _ => ?_
  rw [norm_mul, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left ((hC f p v).trans_eq (by ring)) (norm_nonneg _)

include hm₀ hmass hrep hPV₁ hPV₂ hε in
/-- **The inner bound for the block-summed `δ₂, δ_m` bubble**: the hypotheses
`OneLoopInnerBound 8 4` of `QED.ChainProof.SetANest.loopNested_of_lOuter`, at `ε > 0`, under the
mass floor and the Pauli–Villars block conditions, for every photon momentum `σ k`,
`|σ| ≤ 1`. -/
theorem oneLoopInnerBound_insBubble (A B : Fin 4 → Fin 4 → Mat)
    (hA : ∀ a b, IsOddG (A a b)) (hB : ∀ a b, IsOddG (B a b)) (σ : ℝ) (hσ : |σ| ≤ 1) :
    OneLoopInnerBound 8 4 (fun k q a b => ∑ f, (Φ.coeff f : ℂ) * (K * insG (A a b) (B a b)
      (d₂ (rep f)) (dm (rep f)) (Φ.mass f) ε (zk (σ • k) true q) (zk (σ • k) false q))) := by
  refine ⟨fun k a b v => ?_, fun k a b => ?_, fun w a b => ?_, fun a b => ?_⟩
  · exact (ef_insBubble (hA a b) (hB a b) Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ d₂ dm hε (σ • k)
      true false K).1 v
  · exact (ef_insBubble (hA a b) (hB a b) Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ d₂ dm hε (σ • k)
      true false K).2
  · have hk : Continuous fun z : (ℝ × (Fin 3 → ℝ)) × ℝ => (Fin.cons z.1.1 w : Fin 4 → ℝ) :=
      Continuous.finCons (A := fun _ : Fin 4 => ℝ) (continuous_fst.comp continuous_fst)
        continuous_const
    have hq : Continuous fun z : (ℝ × (Fin 3 → ℝ)) × ℝ => (Fin.cons z.2 z.1.2 : Fin 4 → ℝ) :=
      Continuous.finCons (A := fun _ : Fin 4 => ℝ) continuous_snd
        (continuous_snd.comp continuous_fst)
    have hc : Continuous fun z : (ℝ × (Fin 3 → ℝ)) × ℝ => ∑ f, (Φ.coeff f : ℂ) *
        (K * insG (A a b) (B a b) (d₂ (rep f)) (dm (rep f)) (Φ.mass f) ε
          (σ • (Fin.cons z.1.1 w : Fin 4 → ℝ) + Fin.cons z.2 z.1.2) (Fin.cons z.2 z.1.2)) := by
      have hs : Continuous fun z : (ℝ × (Fin 3 → ℝ)) × ℝ =>
          σ • (Fin.cons z.1.1 w : Fin 4 → ℝ) := hk.const_smul σ
      have ha : Continuous fun z : (ℝ × (Fin 3 → ℝ)) × ℝ =>
          σ • (Fin.cons z.1.1 w : Fin 4 → ℝ) + (Fin.cons z.2 z.1.2 : Fin 4 → ℝ) := hs.add hq
      have hf : ∀ f, Continuous fun z : (ℝ × (Fin 3 → ℝ)) × ℝ =>
          insG (A a b) (B a b) (d₂ (rep f)) (dm (rep f)) (Φ.mass f) ε
            (σ • (Fin.cons z.1.1 w : Fin 4 → ℝ) + Fin.cons z.2 z.1.2) (Fin.cons z.2 z.1.2) :=
        fun f => continuous_insG (hA a b) (hB a b) (d₂ (rep f)) (dm (rep f)) (Φ.mass f)
          hε.ne' ha hq
      exact continuous_finsetSum _ fun f _ => continuous_const.mul (continuous_const.mul (hf f))
    simp only [insZk_true, insZk_false]
    exact hc.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  · obtain ⟨C, hC0, hC⟩ := insBubble_time_bound Φ rep hm₀ hmass hrep hPV₁ hPV₂ d₂ dm hε K
      (hA a b) (hB a b)
    refine ⟨C, fun k v => ?_⟩
    have hk : 1 + ‖σ • k‖ ≤ 1 + ‖k‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have := norm_nonneg k
      nlinarith
    have h8 : (1 + ‖k‖) ^ (8 : ℝ) = (1 + ‖k‖) ^ 8 := by
      rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h4 : (1 + ‖v‖) ^ (-(4 : ℝ)) = ((1 + ‖v‖) ^ 4)⁻¹ := by
      rw [Real.rpow_neg (by positivity), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
    rw [h8, h4]
    simp only [insZk_true, insZk_false]
    refine (hC (σ • k) v).trans ?_
    have h0 : 0 ≤ ((1 + ‖v‖) ^ 4)⁻¹ := by positivity
    have := norm_nonneg (σ • k)
    gcongr

end Bound

end QED.ChainProof.SetANest

end
