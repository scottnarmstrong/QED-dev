/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetANestVFub
public import QED.TwoLoop.NestedVPFubiniBound
public import QED.GradedProof.SE2Decomp

/-!
# Set (a), obligation (N): the outer factor and the Fubini condition for `VA`, `VB`, `VC`

Helper level for the set (a) headline (HA₆), obligation (N), step NL.3 for the loop classes with
a two-loop inner insertion, continuing `QED/ChainProof/SetANestVFub.lean`.

* `nestOuter`: the outer factor of the photon slot `(a, b)`, the `(i, j)` entry of the vertex
  chain with photon factor `Δ(k)_{ν a} Δ(-k)_{ρ b}`; `nestInt X = ∑_{a b} X_{a b} nestOuter_{a b}`
  (`nestInt_eq_sum`). Along `k = (t, w)` at fixed `ε > 0` it is continuous in `t` and decays like
  `(1 + |t|)⁻¹⁰` (two electron propagators `1 + 1`, two regulated photon propagators `4 + 4`).
* `InnerBound Y r`: the **analytic core** for an inner two-loop integrand `Y(k, q)`: the energy
  integral `∫ dt₁ dt₂ Y` is measurable in `(t₃, v)` and bounded by `C (1 + ‖k‖)^r B(v)` with `B`
  integrable over the six inner spatial components.
* `nestG O Y`: the three-loop integrand `∑_{a b} O(k)_{a b} Y_{a b}(k, q)` in the nested routing,
  inner momenta `ℓ 0, ℓ 1`, outer momentum `ℓ 2`.
* **`integrable_innerT_nestG`**: the Fubini condition `hK` of
  `QED.ChainProof.SetANestV.jointEnergyFirstIntegral_three_eq_outer`, at every outer spatial
  momentum, from `InnerBound` with `0 ≤ r < 9` and stage 1 of the inner integrands.
* **`loopNested_of_nestG`**: the nested form `QED.ChainProof.SetANest.LoopNested` of a class
  whose value is the joint three-loop integral of `nestG nestOuter Y` (`hval`, the routing and
  Wick steps), from (HA₀) in the nested routing (`hF`), joint integrability of the inner
  integrands at every `k` (`hY`, the clause of `QED.ChainProof.SetASpec.SAUJ`) and
  `InnerBound` (`hB`), with photon tensor `X(k)_{a b} = ∫∫ Y_{a b}(k, ·)`.
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.ChainProof.SetANestV

open QED.OneLoop QED.TwoLoop.VPUnitNested QED.TwoLoop.Insertion QED.ChainProof.SetANest
open QED.TwoLoop.NestedVPFubiniBound (DecaysLike one_add_abs_pos one_add_norm_cons_le
  decaysLike_electronPropagator decaysLike_photonPropagator continuous_electronPropagator
  continuous_photonPropagator)

/-! ### The outer factor -/

/-- The outer factor of the photon slot `(a, b)`: the `(i, j)` entry of the one-loop vertex
chain with photon factor `Δ(k)_{ν a} Δ(-k)_{ρ b}`. -/
noncomputable def nestOuter (e m mγ Λ ε : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4)
    (k : Fin 4 → ℝ) (a b : Fin 4) : ℂ :=
  vertexChain e μ (electronPropagator m ε (p' + k)) (electronPropagator m ε (p + k))
    (fun ν ρ => photonPropagator mγ Λ ε k ν a * photonPropagator mγ Λ ε (-k) ρ b) i j

theorem nestSum_comm4 (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
    ∑ ν, ∑ ρ, ∑ a, ∑ b, f ν ρ a b = ∑ a, ∑ b, ∑ ν, ∑ ρ, f ν ρ a b := by
  refine (Finset.sum_congr rfl fun ν _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

/-- The outer integrand of a photon tensor is linear in the tensor entries. -/
theorem nestInt_eq_sum (e m mγ Λ ε : ℝ) (p' p : Fin 4 → ℝ)
    (X : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (μ i j : Fin 4) (k : Fin 4 → ℝ) :
    nestInt e m mγ Λ ε p' p X μ i j k =
      ∑ a, ∑ b, X k a b * nestOuter e m mγ Λ ε p' p μ i j k a b := by
  simp only [nestInt, nestOuter, vertexChain, nestPhoton, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [nestSum_comm4]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ => ?_
  ring

section Decay

variable {ε : ℝ} (hε : 0 < ε)
include hε

section MatrixNorm

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem decaysLike_electronPropagator_add (m : ℝ) (a : Fin 4 → ℝ) (w : Fin 3 → ℝ) :
    DecaysLike (fun t => electronPropagator m ε (a + (Fin.cons t w : Fin 4 → ℝ))) 1 := by
  refine decaysLike_electronPropagator m hε _ (abs_nonneg (a 0))
    (by positivity : 0 ≤ ‖a‖ + ‖w‖) (fun t => ?_) (fun t i => ?_) (fun t => ?_)
  · simp only [Pi.add_apply, Fin.cons_zero]
    have := abs_sub (a 0 + t) (a 0)
    simp only [add_sub_cancel_left] at this
    linarith
  · simp
  · refine (norm_add_le _ _).trans ?_
    have := QED.Integration.norm_finCons_le t w
    linarith

theorem decaysLike_photon_cons (mγ Λ : ℝ) (w : Fin 3 → ℝ) (ρ σ : Fin 4) :
    DecaysLike (fun t => photonPropagator mγ Λ ε (Fin.cons t w : Fin 4 → ℝ) ρ σ) 4 :=
  decaysLike_photonPropagator mγ Λ hε (fun t => (Fin.cons t w : Fin 4 → ℝ))
    (fun t => by simp) (fun t i => by simp) ρ σ

theorem decaysLike_photon_neg_cons (mγ Λ : ℝ) (w : Fin 3 → ℝ) (ρ σ : Fin 4) :
    DecaysLike (fun t => photonPropagator mγ Λ ε (-(Fin.cons t w : Fin 4 → ℝ)) ρ σ) 4 :=
  decaysLike_photonPropagator mγ Λ hε (fun t => -(Fin.cons t w : Fin 4 → ℝ))
    (fun t => by simp) (fun t i => by simp) ρ σ

theorem decaysLike_chain (m : ℝ) (p' p : Fin 4 → ℝ) (w : Fin 3 → ℝ) (μ ν ρ : Fin 4) :
    DecaysLike (fun t => Dirac.gamma ρ * electronPropagator m ε (p' + Fin.cons t w) *
      Dirac.gamma μ * electronPropagator m ε (p + Fin.cons t w) * Dirac.gamma ν) 2 :=
  ((((DecaysLike.const (Dirac.gamma ρ)).mul (decaysLike_electronPropagator_add hε m p' w)).mul
    (DecaysLike.const (Dirac.gamma μ))).mul (decaysLike_electronPropagator_add hε m p w)).mul
    (DecaysLike.const (Dirac.gamma ν))

/-- **The outer factor decays like `(1 + |t|)⁻¹⁰`** along `k = (t, w)`, at fixed `ε > 0`. -/
theorem decaysLike_nestOuter (e m mγ Λ : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4)
    (w : Fin 3 → ℝ) (a b : Fin 4) :
    DecaysLike (fun t => nestOuter e m mγ Λ ε p' p μ i j (Fin.cons t w) a b) 10 := by
  have h := (DecaysLike.const ((I * e) ^ 3 * (1 / I) ^ 3 *
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹)).smul (DecaysLike.sum Finset.univ fun ν _ =>
      DecaysLike.sum Finset.univ fun ρ _ =>
        ((decaysLike_photon_cons hε mγ Λ w ν a).mul
          (decaysLike_photon_neg_cons hε mγ Λ w ρ b)).smul
        (decaysLike_chain hε m p' p w μ ν ρ))
  exact (QED.TwoLoop.NestedVPFubiniBound.DecaysLike.apply h i j).congr fun t => rfl

end MatrixNorm

/-- The outer factor is continuous in the outer energy, at fixed `ε > 0`. -/
theorem continuous_nestOuter (e m mγ Λ : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4)
    (w : Fin 3 → ℝ) (a b : Fin 4) :
    Continuous fun t => nestOuter e m mγ Λ ε p' p μ i j (Fin.cons t w) a b := by
  have hk : Continuous fun t : ℝ => (Fin.cons t w : Fin 4 → ℝ) :=
    Continuous.finCons (A := fun _ : Fin 4 => ℝ) continuous_id continuous_const
  have hS : ∀ c : Fin 4 → ℝ, Continuous fun t =>
      electronPropagator m ε (c + (Fin.cons t w : Fin 4 → ℝ)) :=
    fun c => continuous_electronPropagator m hε (continuous_const.add hk)
  simp only [nestOuter, vertexChain, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  refine continuous_const.mul (continuous_finsetSum _ fun ν _ =>
    continuous_finsetSum _ fun ρ _ => ?_)
  exact ((continuous_photonPropagator mγ Λ hε hk ν a).mul
    (continuous_photonPropagator mγ Λ hε hk.neg ρ b)).mul
    (((((continuous_const.matrix_mul (hS p')).matrix_mul continuous_const).matrix_mul
      (hS p)).matrix_mul continuous_const).matrix_elem i j)

end Decay

/-! ### The analytic core and the Fubini condition -/

/-- **The bound on the inner energy integrals** of a two-loop integrand `Y(k, q)`: the energy
integral `∫ dt₁ dt₂ Y(k, ·)` at the inner spatial momenta `v` is measurable in `(t₃, v)` along
`k = (t₃, w)` and bounded by `C (1 + ‖k‖)^r B(v)`, `B` integrable. -/
structure InnerBound (Y : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) (r : ℝ) : Prop where
  meas : ∀ w : Fin 3 → ℝ, AEStronglyMeasurable fun x : ℝ × (Fin 2 → Fin 3 → ℝ) =>
    ∫ t : Fin 2 → ℝ, Y (Fin.cons x.1 w) fun s => (Fin.cons (t s) (x.2 s) : Fin 4 → ℝ)
  bound : ∃ C : ℝ, ∃ B : (Fin 2 → Fin 3 → ℝ) → ℝ, 0 ≤ C ∧ (∀ v, 0 ≤ B v) ∧ Integrable B ∧
    ∀ k v, ‖∫ t : Fin 2 → ℝ, Y k fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)‖ ≤
      C * (1 + ‖k‖) ^ r * B v

/-- One term of the Fubini condition: a continuous factor decaying like `(1 + |t|)⁻¹⁰` times an
inner energy integral with `InnerBound`, `0 ≤ r < 9`, is integrable in `(t₃, v)`. -/
theorem integrable_outer_mul_inner {g : ℝ → ℂ} (hc : Continuous g) (hd : DecaysLike g 10)
    {Y : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ} {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 9)
    (hY : InnerBound Y r) (w : Fin 3 → ℝ) :
    Integrable fun x : ℝ × (Fin 2 → Fin 3 → ℝ) => g x.1 *
      ∫ t : Fin 2 → ℝ, Y (Fin.cons x.1 w) fun s => (Fin.cons (t s) (x.2 s) : Fin 4 → ℝ) := by
  obtain ⟨Co, hCo⟩ := hd
  have hCo0 := QED.TwoLoop.NestedVPFubiniBound.DecaysLike.const_nonneg hCo
  obtain ⟨Ci, B, hCi0, hB0, hB, hCi⟩ := hY.bound
  set K := Co * Ci * (1 + ‖w‖) ^ r
  have hint : Integrable fun x : ℝ × (Fin 2 → Fin 3 → ℝ) =>
      K * ((1 + ‖x.1‖) ^ (-(10 - r)) * B x.2) := by
    refine Integrable.const_mul ?_ K
    exact (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 10 - r)
      (by simp; linarith)).mul_prod hB
  refine hint.mono' ((hc.comp continuous_fst).aestronglyMeasurable.mul (hY.meas w))
    (Filter.Eventually.of_forall fun x => ?_)
  obtain ⟨t, v⟩ := x
  simp only
  rw [norm_mul]
  have ht0 : 0 < 1 + |t| := one_add_abs_pos t
  have hw0 : 0 < 1 + ‖w‖ := by positivity
  have h1 := hCo t
  have h2 := hCi (Fin.cons t w) v
  have := hB0 v
  have hk : (1 + ‖(Fin.cons t w : Fin 4 → ℝ)‖) ^ r ≤ (1 + |t|) ^ r * (1 + ‖w‖) ^ r := by
    rw [← Real.mul_rpow ht0.le hw0.le]
    exact Real.rpow_le_rpow (by positivity) (one_add_norm_cons_le t w) hr0
  have hz : (1 + |t|) ^ (-(10 : ℤ)) * (1 + |t|) ^ r = (1 + |t|) ^ (-(10 - r)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_add ht0]
    congr 1
    push_cast
    ring
  rw [Real.norm_eq_abs t]
  calc ‖g t‖ * ‖∫ t' : Fin 2 → ℝ, Y (Fin.cons t w) fun s => (Fin.cons (t' s) (v s) : Fin 4 → ℝ)‖
      ≤ (Co * (1 + |t|) ^ (-(10 : ℤ))) * (Ci * (1 + ‖(Fin.cons t w : Fin 4 → ℝ)‖) ^ r * B v) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ ≤ (Co * (1 + |t|) ^ (-(10 : ℤ))) * (Ci * ((1 + |t|) ^ r * (1 + ‖w‖) ^ r) * B v) := by
        gcongr
    _ = K * (((1 + |t|) ^ (-(10 : ℤ)) * (1 + |t|) ^ r) * B v) := by ring
    _ = K * ((1 + |t|) ^ (-(10 - r)) * B v) := by rw [hz]

/-! ### The three-loop integrand of an outer factor and inner integrands -/

/-- The three-loop integrand `∑_{a b} O(k)_{a b} Y_{a b}(k, q)` in the nested routing: inner
momenta `q = (ℓ 0, ℓ 1)`, outer momentum `k = ℓ 2`. -/
noncomputable def nestG (O : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (Y : Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) (ℓ : Fin 3 → Fin 4 → ℝ) : ℂ :=
  ∑ a, ∑ b, O (ℓ 2) a b * Y a b (ℓ 2) ![ℓ 0, ℓ 1]

theorem nestG_insertNth (O : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (Y : Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) (k : Fin 4 → ℝ)
    (q : Fin 2 → Fin 4 → ℝ) :
    nestG O Y (Fin.insertNth 2 k q) = ∑ a, ∑ b, O k a b * Y a b k q := by
  have hq : (![q 0, q 1] : Fin 2 → Fin 4 → ℝ) = q := by
    funext s
    fin_cases s <;> rfl
  rw [nestG, insertNth_two_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, hq]
  rfl

/-- The inner energy integral of `nestG`, from stage 1 of the inner integrands. -/
theorem innerT_nestG (O : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (Y : Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (hY : ∀ a b k, QED.TwoLoop.jointEnergyFirstIntegrable 2 (Y a b k)) (t₃ : ℝ)
    (w : Fin 3 → ℝ) (v : Fin 2 → Fin 3 → ℝ) :
    innerT (nestG O Y) t₃ w v = ∑ a, ∑ b, O (Fin.cons t₃ w) a b *
      ∫ t : Fin 2 → ℝ, Y a b (Fin.cons t₃ w) fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ) := by
  have hI := fun a b => (hY a b (Fin.cons t₃ w)).1 v
  simp only [innerT, nestG_insertNth]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hI a b).const_mul _]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => (hI a b).const_mul _]
  simp only [integral_const_mul]

theorem joint_finsetSum {ι : Type*} (s : Finset ι) {L : ℕ}
    (G : ι → (Fin L → Fin 4 → ℝ) → ℂ)
    (h : ∀ i ∈ s, QED.TwoLoop.jointEnergyFirstIntegrable L (G i)) :
    QED.TwoLoop.jointEnergyFirstIntegral L (fun ℓ => ∑ i ∈ s, G i ℓ) =
      ∑ i ∈ s, QED.TwoLoop.jointEnergyFirstIntegral L (G i) := by
  unfold QED.TwoLoop.jointEnergyFirstIntegral
  have hin : ∀ v : Fin L → Fin 3 → ℝ, ∫ t : Fin L → ℝ,
      ∑ i ∈ s, G i (fun s' => (Fin.cons (t s') (v s') : Fin 4 → ℝ)) =
      ∑ i ∈ s, ∫ t : Fin L → ℝ, G i (fun s' => (Fin.cons (t s') (v s') : Fin 4 → ℝ)) :=
    fun v => integral_finsetSum s fun i hi => (h i hi).1 v
  simp only [hin]
  exact integral_finsetSum s fun i hi => (h i hi).2

/-- The inner joint integral of `nestG`, from the joint integrability of the inner integrands. -/
theorem innerJ_nestG (O : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (Y : Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (hY : ∀ a b k, QED.TwoLoop.jointEnergyFirstIntegrable 2 (Y a b k)) (k : Fin 4 → ℝ) :
    innerJ (nestG O Y) k =
      ∑ a, ∑ b, O k a b * QED.TwoLoop.jointEnergyFirstIntegral 2 (Y a b k) := by
  simp only [innerJ, nestG_insertNth]
  rw [joint_finsetSum _ _ fun a _ =>
    QED.GradedProof.SE2.jointEnergyFirstIntegrable_sum _ _ _ fun b _ => hY a b k]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact QED.GradedProof.SE2.jointEnergyFirstIntegral_sum _ _ _ fun b _ => hY a b k

/-- **The Fubini condition for `nestG`** at every outer spatial momentum, for an outer factor
with entries continuous and decaying like `(1 + |t|)⁻¹⁰` along `k = (t, w)` and inner integrands
with `InnerBound`, `0 ≤ r < 9`. -/
theorem integrable_innerT_nestG (O : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (Y : Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (hc : ∀ w a b, Continuous fun t => O (Fin.cons t w) a b)
    (hd : ∀ w a b, DecaysLike (fun t => O (Fin.cons t w) a b) 10)
    (hY : ∀ a b k, QED.TwoLoop.jointEnergyFirstIntegrable 2 (Y a b k)) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < 9) (hB : ∀ a b, InnerBound (Y a b) r) (w : Fin 3 → ℝ) :
    Integrable fun x : ℝ × (Fin 2 → Fin 3 → ℝ) => innerT (nestG O Y) x.1 w x.2 := by
  simp only [innerT_nestG O Y hY]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    integrable_outer_mul_inner (hc w a b) (hd w a b) hr0 hr (hB a b) w

open QED.WickModel in
/-- **The nested form of a class with a two-loop inner insertion.** If every entry of the value
(G₅) of `C` is the joint three-loop integral of `nestG nestOuter Y` (`hval`: routing and Wick
steps), that integrand is integrable in both stages (`hF`: (HA₀) in the nested routing), the inner
integrands are jointly integrable at every outer momentum (`hY`) and satisfy `InnerBound` with
`0 ≤ r < 9` (`hB`, the analytic core), then `C` is in nested form with the photon tensor
`X(k)_{a b} = ∫∫ Y_{a b}(k, ·)`, at `ε > 0`. -/
theorem loopNested_of_nestG (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction 1 1 κ) (hε : 0 < P.ε) (p' p : Fin 4 → ℝ)
    (Y : Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (hval : ∀ μ i j, Graded.contractionValue P Φ D C 0 (fun _ => p') (fun _ => p)
        (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) =
      QED.TwoLoop.jointEnergyFirstIntegral 3
        (nestG (nestOuter P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p μ i j) Y))
    (hF : ∀ μ i j, QED.TwoLoop.jointEnergyFirstIntegrable 3
        (nestG (nestOuter P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p μ i j) Y))
    (hY : ∀ a b k, QED.TwoLoop.jointEnergyFirstIntegrable 2 (Y a b k)) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < 9) (hB : ∀ a b, InnerBound (Y a b) r) :
    LoopNested P Φ D C (fun k a b => QED.TwoLoop.jointEnergyFirstIntegral 2 (Y a b k)) p' p :=
  loopNested_of_joint P Φ D C _ p' p _ hval hF
    (fun μ i j => integrable_innerT_nestG _ Y
      (continuous_nestOuter hε _ _ _ _ p' p μ i j) (decaysLike_nestOuter hε _ _ _ _ p' p μ i j)
      hY hr0 hr hB)
    (fun μ i j k => by
      rw [innerJ_nestG _ Y hY, nestInt_eq_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _)

end QED.ChainProof.SetANestV

end
