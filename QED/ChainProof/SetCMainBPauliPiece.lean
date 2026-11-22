/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCPauliSumReal

/-!
# Set (c): pieces of a class limit with covariance, `♯`-law and Pauli limit

Helper level for the per-class links `QED.ChainProof.SetCPauli.SetCClassCov`, `SetCClassPauli`,
`SetCClassSharp`. A *piece* is a vertex function `G p' p` of the external momenta. The three
properties needed of a class limit are stated for pieces and are closed under the operations
that assemble a class limit from its parts:

* `PieceCov m G`: covariance under every spinor-lifted `L` keeping positive energies, on the
  pairs `IsPairQ m`;
* `PieceSharp m G`: `G^μ♯ = -G^μ` on the pairs `IsPairQ m`;
* `PiecePauli m G Z`: the even quotient of the Pauli numerator along the curve tends to `Z`;
* closure: sums, constant multiples (real ones for `♯`), negation;
* `dispMat`, **`pieceCov_dispMat`**, **`sharp_dispMat`**: a dispersion integral `∫₀¹ w(x) F_x dx`
  of covariant, resp. `♯`-odd, families against a weight (a real one for `♯`);
* `IsPieceClass V P₀ r`: at the admissible data, the class limits are a piece with the three
  properties; **`setCClassCov_of_piece`**, **`setCClassSharp_of_piece`**,
  **`setCClassPauli_of_piece`** (value `clsPauliLim V P₀ r`), `clsPauliLim_of_piece`.
-/

@[expose] public section

open Complex Matrix Filter Topology Set MeasureTheory
open QED.WickModel (Params)

namespace QED.ChainProof.SetCMainB

open QED.Dirac QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.LimitCovariance
open QED.ChainProof.SetCPauli
open QED.GradedProof.SE2Real (sharp sharp_add sharp_neg sharp_smul)

/-- A vertex function of the external momenta `(p', p)`. -/
abbrev Piece : Type := (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ

/-- **Covariance of a piece** on the pairs `IsPairQ m`. -/
def PieceCov (m : ℝ) (G : Piece) : Prop :=
  ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ), IsSpinLift L S T →
    ∀ p' p, IsPairQ m p' p → 0 < (L *ᵥ p') 0 → 0 < (L *ᵥ p) 0 →
      ∀ μ, S * G (L *ᵥ p') (L *ᵥ p) μ * T = vecAct L (G p' p) μ

/-- **The `♯`-law of a piece** on the pairs `IsPairQ m`. -/
def PieceSharp (m : ℝ) (G : Piece) : Prop :=
  ∀ p' p, IsPairQ m p' p → ∀ μ, sharp (G p' p μ) = -G p' p μ

/-- **The Pauli limit of a piece**: the even quotient of its Pauli numerator along the curve
tends to `Z`. -/
def PiecePauli (m : ℝ) (G : Piece) (Z : ℂ) : Prop :=
  Tendsto (evenQuot fun u => pauliNum m (curveMomentum m u) (restMomentum m)
    (G (curveMomentum m u) (restMomentum m))) (𝓝[≠] 0) (𝓝 Z)

/-! ### Closure -/

section Closure

variable {m : ℝ} {G H : Piece}

theorem PieceCov.add (hG : PieceCov m G) (hH : PieceCov m H) :
    PieceCov m fun p' p μ => G p' p μ + H p' p μ := by
  intro L S T h p' p hpq h0 h1 μ
  rw [Matrix.mul_add, Matrix.add_mul, hG L S T h p' p hpq h0 h1 μ,
    hH L S T h p' p hpq h0 h1 μ, vecAct_add]

theorem PieceCov.smul (c : ℂ) (hG : PieceCov m G) : PieceCov m fun p' p μ => c • G p' p μ := by
  intro L S T h p' p hpq h0 h1 μ
  rw [Matrix.mul_smul, Matrix.smul_mul, hG L S T h p' p hpq h0 h1 μ, vecAct_smul]

theorem PieceCov.neg (hG : PieceCov m G) : PieceCov m fun p' p μ => -G p' p μ := by
  have h := hG.smul (-1)
  simpa only [neg_one_smul] using h

theorem PieceCov.sum {ι : Type*} [Fintype ι] {F : ι → Piece} (hF : ∀ f, PieceCov m (F f)) :
    PieceCov m fun p' p μ => ∑ f, F f p' p μ := by
  intro L S T h p' p hpq h0 h1 μ
  rw [Finset.mul_sum, Finset.sum_mul]
  simp only [fun f => hF f L S T h p' p hpq h0 h1 μ, vecAct, Finset.smul_sum]
  exact Finset.sum_comm

theorem PieceSharp.add (hG : PieceSharp m G) (hH : PieceSharp m H) :
    PieceSharp m fun p' p μ => G p' p μ + H p' p μ := by
  intro p' p hpq μ
  rw [sharp_add, hG p' p hpq μ, hH p' p hpq μ, neg_add]

theorem PieceSharp.smul {c : ℂ} (hc : starRingEnd ℂ c = c) (hG : PieceSharp m G) :
    PieceSharp m fun p' p μ => c • G p' p μ := by
  intro p' p hpq μ
  rw [sharp_smul, hc, hG p' p hpq μ, smul_neg]

theorem PieceSharp.neg (hG : PieceSharp m G) : PieceSharp m fun p' p μ => -G p' p μ := by
  intro p' p hpq μ
  rw [sharp_neg, hG p' p hpq μ]

theorem PieceSharp.sum {ι : Type*} [Fintype ι] {F : ι → Piece} (hF : ∀ f, PieceSharp m (F f)) :
    PieceSharp m fun p' p μ => ∑ f, F f p' p μ := by
  intro p' p hpq μ
  classical
  have key : ∀ s : Finset ι, sharp (∑ f ∈ s, F f p' p μ) = -∑ f ∈ s, F f p' p μ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [QED.GradedProof.SE2Real.sharp_zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, sharp_add, ih, hF a p' p hpq μ, neg_add]
  exact key Finset.univ

theorem PiecePauli.add {Z W : ℂ} (hG : PiecePauli m G Z) (hH : PiecePauli m H W) :
    PiecePauli m (fun p' p μ => G p' p μ + H p' p μ) (Z + W) := by
  refine (Filter.Tendsto.add hG hH).congr fun u => ?_
  simp only [evenQuot]
  rw [pauliNum_add, pauliNum_add]
  ring

theorem PiecePauli.smul (c : ℂ) {Z : ℂ} (hG : PiecePauli m G Z) :
    PiecePauli m (fun p' p μ => c • G p' p μ) (c * Z) := by
  refine (hG.const_mul c).congr fun u => ?_
  simp only [evenQuot, pauliNum_smul]
  ring

theorem PiecePauli.neg {Z : ℂ} (hG : PiecePauli m G Z) :
    PiecePauli m (fun p' p μ => -G p' p μ) (-Z) := by
  have h := hG.smul (-1)
  simpa only [neg_one_smul, neg_one_mul] using h

theorem PiecePauli.sum {ι : Type*} [Fintype ι] {F : ι → Piece} {Z : ι → ℂ}
    (hF : ∀ f, PiecePauli m (F f) (Z f)) :
    PiecePauli m (fun p' p μ => ∑ f, F f p' p μ) (∑ f, Z f) := by
  refine (tendsto_finsetSum _ fun f _ => hF f).congr fun u => ?_
  simp only [evenQuot]
  rw [pauliNum_sum, pauliNum_sum, ← Finset.sum_div, ← Finset.sum_add_distrib]

/-- From `S(u)/u² → Z` to the even quotient. -/
theorem tendsto_evenQuot_of_div {S : ℝ → ℂ} {Z : ℂ}
    (h : Tendsto (fun u => S u / (u : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 Z)) :
    Tendsto (evenQuot S) (𝓝[≠] 0) (𝓝 Z) := by
  have hneg : Tendsto (fun u : ℝ => -u) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (continuous_neg (G := ℝ)).tendsto 0
      rw [neg_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u (hu : u ≠ 0)
      exact neg_ne_zero.mpr hu
  have h2 := h.comp hneg
  refine ((h.add h2).div_const 2).congr' (Eventually.of_forall fun u => ?_) |>.trans
    (by rw [add_self_div_two])
  simp only [Function.comp, evenQuot, ofReal_neg, neg_sq]
  ring

end Closure

/-! ### Dispersion integrals of pieces -/

section Disp

/-- The dispersion integral `∫₀¹ w(x) F_x dx`, entrywise. -/
noncomputable def dispMat (w : ℝ → ℂ) (F : ℝ → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => ∫ x in Ioo (0 : ℝ) 1, w x * F x μ i j

theorem sandwich_apply (S X T : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    (S * X * T) i j = ∑ b, ∑ a, S i a * X a b * T b j := by
  simp only [Matrix.mul_apply, Finset.sum_mul]

theorem vecAct_apply' (L : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (μ i j : Fin 4) : vecAct L V μ i j = ∑ ν, ((L μ ν : ℝ) : ℂ) * V ν i j := by
  simp only [vecAct, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

/-- **Covariance of a dispersion integral** of a covariant family, given the integrability of
the entries. -/
theorem pieceCov_dispMat {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}
    {w : ℝ → ℂ} {F G : ℝ → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hFG : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ μ, S * F x μ * T = vecAct L (G x) μ)
    (hF : ∀ μ i j, IntegrableOn (fun x => w x * F x μ i j) (Ioo 0 1))
    (hG : ∀ μ i j, IntegrableOn (fun x => w x * G x μ i j) (Ioo 0 1)) (μ : Fin 4) :
    S * dispMat w F μ * T = vecAct L (dispMat w G) μ := by
  ext i j
  rw [sandwich_apply, vecAct_apply']
  simp only [dispMat, Matrix.of_apply]
  have e1 : ∀ a b, S i a * (∫ x in Ioo (0 : ℝ) 1, w x * F x μ a b) * T b j =
      ∫ x in Ioo (0 : ℝ) 1, S i a * (w x * F x μ a b) * T b j := fun a b => by
    rw [integral_mul_const, integral_const_mul]
  have e2 : ∀ ν, ((L μ ν : ℝ) : ℂ) * (∫ x in Ioo (0 : ℝ) 1, w x * G x ν i j) =
      ∫ x in Ioo (0 : ℝ) 1, ((L μ ν : ℝ) : ℂ) * (w x * G x ν i j) := fun ν => by
    rw [integral_const_mul]
  simp only [e1, e2]
  rw [← integral_finsetSum _ fun ν _ => (hG ν i j).const_mul _]
  simp only [← integral_finsetSum _ fun a _ => ((hF μ a _).const_mul _).mul_const _]
  rw [← integral_finsetSum _ fun b _ => integrable_finsetSum _ fun a _ =>
    ((hF μ a b).const_mul _).mul_const _]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have h := congrFun (congrFun (hFG x hx μ) i) j
  rw [sandwich_apply, vecAct_apply'] at h
  calc ∑ b, ∑ a, S i a * (w x * F x μ a b) * T b j
      = w x * ∑ b, ∑ a, S i a * F x μ a b * T b j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => by ring
    _ = w x * ∑ ν, ((L μ ν : ℝ) : ℂ) * G x ν i j := by rw [h]
    _ = ∑ ν, ((L μ ν : ℝ) : ℂ) * (w x * G x ν i j) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ν _ => by ring

/-- **A dispersion integral of a `♯`-odd family against a real weight is `♯`-odd.** -/
theorem sharp_dispMat {w : ℝ → ℂ} {F : ℝ → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hw : ∀ x, starRingEnd ℂ (w x) = w x)
    (hF : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ μ, sharp (F x μ) = -F x μ) (μ : Fin 4) :
    sharp (dispMat w F μ) = -dispMat w F μ := by
  ext i j
  simp only [dispMat, QED.GradedProof.V5Zero.Sharp.sharp_apply, Matrix.neg_apply,
    Matrix.of_apply]
  rw [← integral_conj, ← integral_const_mul, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have h := congrFun (congrFun (hF x hx μ) i) j
  rw [QED.GradedProof.V5Zero.Sharp.sharp_apply, Matrix.neg_apply] at h
  simp only [map_mul, hw]
  rw [mul_left_comm, h, mul_neg]

end Disp

/-! ### Classes whose limits are pieces -/

section Class

variable {ι : Type} {V : ClsFam ι} {P₀ : Params} {r : ι}

/-- **A class whose limits form a piece with the three properties**: at the admissible data the
class value has the limit `G p' p` at every pair `IsPairQ`, and `G` is covariant, `♯`-odd and has
a Pauli limit. -/
def IsPieceClass (V : ClsFam ι) (P₀ : Params) (r : ι) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∃ (G : Piece) (Z : ℂ),
    (∀ p' p, IsPairQ P₀.m p' p → IsClassLimC V P₀ M₁ M₂ c₁ c₂ mγ Λ D s r p' p (G p' p)) ∧
      PieceCov P₀.m G ∧ PieceSharp P₀.m G ∧ PiecePauli P₀.m G Z

theorem setCClassLim_of_piece (hP : IsPieceClass V P₀ r) : SetCClassLim V P₀ r := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq
  obtain ⟨G, -, hG, -⟩ := hP M₁ M₂ c₁ c₂ mγ Λ D s hA
  exact ⟨_, hG p' p hpq⟩

theorem setCClassCov_of_piece (hP : IsPieceClass V P₀ r) : SetCClassCov V P₀ r := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA L S T h p' p hpq h0 h1 Y Z hY hZ μ
  obtain ⟨G, -, hG, hC, -⟩ := hP M₁ M₂ c₁ c₂ mγ Λ D s hA
  rw [isClassLimC_unique hY (hG p' p hpq),
    isClassLimC_unique hZ (hG _ _ (isPairQ_map h hpq h0 h1))]
  exact hC L S T h p' p hpq h0 h1 μ

theorem setCClassSharp_of_piece (hP : IsPieceClass V P₀ r) : SetCClassSharp V P₀ r := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq Y hY μ
  obtain ⟨G, -, hG, -, hS, -⟩ := hP M₁ M₂ c₁ c₂ mγ Λ D s hA
  rw [isClassLimC_unique hY (hG p' p hpq)]
  exact hS p' p hpq μ

theorem eventually_curve_pair : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 ∧ u ≠ 0 := by
  filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1)), self_mem_nhdsWithin] with u hu (hu0 : u ≠ 0)
  exact ⟨hu, hu0⟩

/-- Along the curve, the even quotient of the class limit is that of the piece. -/
theorem tendsto_evenQuot_of_piece {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}
    (hm : 0 < P₀.m) {G : Piece} {Z : ℂ}
    (hG : ∀ p' p, IsPairQ P₀.m p' p → IsClassLimC V P₀ M₁ M₂ c₁ c₂ mγ Λ D s r p' p (G p' p))
    (hZ : PiecePauli P₀.m G Z) :
    Tendsto (evenQuot fun u => pauliNum P₀.m (curveMomentum P₀.m u) (restMomentum P₀.m)
      (clsLimAt V P₀ M₁ M₂ c₁ c₂ mγ Λ D s r (curveMomentum P₀.m u) (restMomentum P₀.m)))
      (𝓝[≠] 0) (𝓝 Z) := by
  refine hZ.congr' ?_
  filter_upwards [eventually_curve_pair] with u hu
  simp only [evenQuot]
  rw [clsLimAt_eq (hG _ _ (isPairQ_curve hm hu.1 hu.2)),
    clsLimAt_eq (hG _ _ (isPairQ_curve hm (neg_mem_Ioo_one hu.1) (neg_ne_zero.mpr hu.2)))]

theorem setCClassPauli_of_piece (hP : IsPieceClass V P₀ r) :
    SetCClassPauli V P₀ r (clsPauliLim V P₀ r) := by
  refine setCClassPauli_of_evenQuot (setCClassLim_of_piece hP) (setCClassCov_of_piece hP)
    fun M₁ M₂ c₁ c₂ mγ Λ D s hA => ?_
  have hm : 0 < P₀.m := by obtain ⟨-, -, -, -, hmγ, -, -, hm2, -⟩ := hA; linarith
  obtain ⟨G, Z, hG, -, -, hZ⟩ := hP M₁ M₂ c₁ c₂ mγ Λ D s hA
  exact ⟨Z, tendsto_evenQuot_of_piece hm hG hZ⟩

/-- The canonical Pauli value of a class whose limits are a piece with Pauli limit `Z`. -/
theorem clsPauliLim_of_piece {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}
    (hm : 0 < P₀.m) {G : Piece} {Z : ℂ}
    (hG : ∀ p' p, IsPairQ P₀.m p' p → IsClassLimC V P₀ M₁ M₂ c₁ c₂ mγ Λ D s r p' p (G p' p))
    (hZ : PiecePauli P₀.m G Z) :
    clsPauliLim V P₀ r M₁ M₂ c₁ c₂ mγ Λ D s = Z / (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5) := by
  rw [clsPauliLim, (tendsto_evenQuot_of_piece hm hG hZ).limUnder_eq]

end Class

end QED.ChainProof.SetCMainB

end
