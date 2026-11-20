/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceV
public import QED.GradedProof.RPi4FaceJoinData

/-!
# (R-Π₄) step L6d2: the face sector of a heavy-photon density in join coordinates

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d2. A collapsed
piece whose lines are sorted face block first (`p + 1` lines with loop rows `(0, 1)` or `(1, -1)`,
among them the photon `γ`) and rest (`q + 1` lines with loop row `(1, 0)`) is a `FaceShape`. In
the join coordinates `z = (ρ W, (1 - ρ) V)` the integrand `z_γ paramAtV(V₀(z) + z_γ u)` times the
Jacobian factor `ρᵖ` is, for `ρ > 0`, the **rescaled face integrand** `hJ ρ (ρ u) W V`, defined by
a formula that is regular at `ρ = 0`:

* `FaceShape`, the rescaled data `aJ`, `FaceShape.b`, `FaceShape.c`, `PJ`, `FaceShape.b₁`, and
  the rescaled second Symanzik function `vHat`; **`symanzikV_join_eq`**: `V₀ = vHat` for `ρ > 0`;
* `FaceBr` (the bracket `∑ⱼ Cⱼ v^{-kⱼ}` of a face, with the order `d` of the face) and
  `FaceBr.Rep` (the identity `ρ^{p+1} paramAtV = Û⁻² ρ^{p-d} ∑ⱼ Cⱼ v^{-kⱼ}` on face matrices),
  with instances `FaceBr.se`, `FaceBr.vtx` (`rep_se`, `rep_vtx`, from `paramAtV_face_se/vtx`);
* `hJ`, `gJ` (`gJ ρ σ = (1 - ρ)^q ∫_{Δ_p × Δ_q} hJ ρ σ`); **`integrand_join_eq`** (pointwise) and
  **`integral_faceCut_eq`**: the integral over the simplex of the integrand cut to
  `{∑_{face block} z ≤ ρ₀}` is `∫₀^{ρ₀} gJ ρ (ρ u) dρ`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet
  simplexPoint_mem_stdSimplex)

/-- A collapsed piece sorted face block first: face-block lines (rows `(0, 1)` or `(1, -1)`,
momenta `pF`, masses `MF`, photon `γ`) and rest lines (row `(1, 0)`, momenta `pR`, masses `MR`). -/
structure FaceShape (p q : ℕ) where
  /-- The loop rows of the face block. -/
  αF : Fin (p + 1) → Fin 2 → ℝ
  /-- The external momenta of the face block. -/
  pF : Fin (p + 1) → Fin 4 → ℝ
  /-- The masses of the face block. -/
  MF : Fin (p + 1) → ℝ
  /-- The external momenta of the rest. -/
  pR : Fin (q + 1) → Fin 4 → ℝ
  /-- The masses of the rest. -/
  MR : Fin (q + 1) → ℝ
  /-- The photon line of the face block. -/
  γ : Fin (p + 1)
  /-- The face rows. -/
  hF : ∀ i, αF i = ![0, 1] ∨ αF i = ![1, -1]

namespace FaceShape

variable {p q : ℕ} (S : FaceShape p q)

/-- The loop rows of the whole piece. -/
def α : Fin (p + 1 + q + 1) → Fin 2 → ℝ := joinA S.αF fun _ => ![1, 0]

/-- The external momenta of the whole piece. -/
def pp : Fin (p + 1 + q + 1) → Fin 4 → ℝ := joinA S.pF S.pR

/-- The masses of the whole piece. -/
def M : Fin (p + 1 + q + 1) → ℝ := joinA S.MF S.MR

/-- The photon line in the whole piece. -/
def γJ : Fin (p + 1 + q + 1) := Fin.castAdd (q + 1) S.γ

/-- The `ρ`-independent part `a₀ = ∑ V` of the rescaled `A₀₀`. -/
def a0 (V : Fin (q + 1) → ℝ) : ℝ := ∑ j, V j

/-- The `ρ`-slope `a₁` of the rescaled `A₀₀`. -/
def a1 (W : Fin (p + 1) → ℝ) (V : Fin (q + 1) → ℝ) : ℝ :=
  ∑ i, W i * S.αF i 0 * S.αF i 0 - ∑ j, V j

/-- The rescaled `A₀₀ = a₀ + ρ a₁`. -/
def aJ (ρ : ℝ) (W : Fin (p + 1) → ℝ) (V : Fin (q + 1) → ℝ) : ℝ := a0 V + ρ * S.a1 W V

/-- The rescaled off-diagonal entry `b`. -/
def b (W : Fin (p + 1) → ℝ) : ℝ := ∑ i, W i * S.αF i 0 * S.αF i 1

/-- The rescaled entry `c`. -/
def c (W : Fin (p + 1) → ℝ) : ℝ := ∑ i, W i * S.αF i 1 * S.αF i 1

/-- The `ρ`-independent part of `β₀`. -/
def P0 (V : Fin (q + 1) → ℝ) : Fin 4 → ℝ := fun μ => ∑ j, V j * S.pR j μ

/-- The `ρ`-slope of `β₀`. -/
def P1 (W : Fin (p + 1) → ℝ) (V : Fin (q + 1) → ℝ) : Fin 4 → ℝ :=
  fun μ => ∑ i, W i * S.αF i 0 * S.pF i μ - ∑ j, V j * S.pR j μ

/-- `β₀ = P₀ + ρ P₁`. -/
def PJ (ρ : ℝ) (W : Fin (p + 1) → ℝ) (V : Fin (q + 1) → ℝ) : Fin 4 → ℝ :=
  fun μ => S.P0 V μ + ρ * S.P1 W V μ

/-- The rescaled `β₁ = ρ b₁`. -/
def b₁ (W : Fin (p + 1) → ℝ) : Fin 4 → ℝ := fun μ => ∑ i, W i * S.αF i 1 * S.pF i μ

/-- The mass term of the face block. -/
def mF (W : Fin (p + 1) → ℝ) : ℝ :=
  ∑ i, W i * (S.MF i ^ 2 + Minkowski.dot (S.pF i) (S.pF i))

/-- The mass term of the rest. -/
def mR (V : Fin (q + 1) → ℝ) : ℝ :=
  ∑ j, V j * (S.MR j ^ 2 + Minkowski.dot (S.pR j) (S.pR j))

/-- The rescaled determinant at the join data. -/
def uJ (ρ : ℝ) (W : Fin (p + 1) → ℝ) (V : Fin (q + 1) → ℝ) : ℝ :=
  uHat ρ (S.aJ ρ W V) (S.b W) (S.c W)

/-- **The rescaled second Symanzik function**, regular at `ρ = 0`. -/
noncomputable def vHat (ρ : ℝ) (W : Fin (p + 1) → ℝ) (V : Fin (q + 1) → ℝ) : ℝ :=
  (S.mR V + ρ * (S.mF W - S.mR V)) -
    (S.c W * Minkowski.dot (S.PJ ρ W V) (S.PJ ρ W V) -
      2 * ρ * S.b W * Minkowski.dot (S.PJ ρ W V) (S.b₁ W) +
      ρ * S.aJ ρ W V * Minkowski.dot (S.b₁ W) (S.b₁ W)) / S.uJ ρ W V

variable (ρ : ℝ) (W : Fin (p + 1) → ℝ) (V : Fin (q + 1) → ℝ)

theorem isFaceMat : IsFaceMat (symanzikMatrix S.α (joinZ ρ W V)) ρ (S.aJ ρ W V) (S.b W) (S.c W) :=
  isFaceMat_join S.αF ρ W V (αR := fun _ => ![1, 0]) fun _ => rfl

theorem symanzikVector_one (μ : Fin 4) :
    symanzikVector S.α S.pp (joinZ ρ W V) 1 μ = ρ * S.b₁ W μ :=
  symanzikVector_join_one S.αF S.pF S.pR ρ W V (αR := fun _ => ![1, 0]) (fun _ => rfl) μ

theorem symanzikVector_zero : symanzikVector S.α S.pp (joinZ ρ W V) 0 = S.PJ ρ W V :=
  funext fun μ =>
    symanzikVector_join_zero S.αF S.pF S.pR ρ W V (αR := fun _ => ![1, 0]) (fun _ => rfl) μ

theorem joinZ_γJ : joinZ ρ W V S.γJ = ρ * W S.γ := by
  simp [γJ, joinZ]

theorem uJ_ge (hW : ∀ i, 0 ≤ W i) (hW1 : ∑ i, W i = 1) (hV1 : ∑ j, V j = 1) (hρ : 0 ≤ ρ) :
    1 - ρ ≤ S.uJ ρ W V :=
  uHat_join_ge S.αF ρ W V S.hF hW hW1 hV1 hρ

/-- **`V₀` in join coordinates is the rescaled `vHat`** for `ρ ≠ 0`. -/
theorem symanzikV_join_eq (hρ : ρ ≠ 0) (hu : S.uJ ρ W V ≠ 0) :
    symanzikV S.α S.pp S.M (joinZ ρ W V) = S.vHat ρ W V := by
  have hq := quadForm_face (S.isFaceMat ρ W V) hρ hu (S.symanzikVector_one ρ W V)
  rw [S.symanzikVector_zero] at hq
  rw [symanzikV, hq, vHat, uJ]
  congr 1
  rw [sum_join]
  simp only [joinZ, M, pp, joinA, Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul,
    mF, mR]
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

end FaceShape

/-! ### The bracket of a face -/

/-- The bracket `∑ⱼ Cⱼ(ρ, a, b, c, β₀, b₁) v^{-kⱼ}` of a face of order `d`. -/
structure FaceBr (r : ℕ) where
  /-- The order of the face (`1` for self-energy faces, `2` for vertex faces). -/
  d : ℕ
  /-- The exponents. -/
  k : Fin r → ℕ
  /-- The coefficients. -/
  C : Fin r → ℝ → ℝ → ℝ → ℝ → (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℂ

namespace FaceBr

/-- The value of the bracket. -/
noncomputable def val {r : ℕ} (B : FaceBr r) (ρ a b c : ℝ) (β₀ b₁ : Fin 4 → ℝ) (v : ℝ) : ℂ :=
  ∑ j, B.C j ρ a b c β₀ b₁ * ((v : ℂ) ^ B.k j)⁻¹

/-- **The rescaling identity of a face**: on every face matrix (of loop `1`),
`ρ^{p+1} paramAtV = Û⁻² ρ^{p-d} [bracket]`. -/
def Rep {r : ℕ} (B : FaceBr r) (n p : ℕ) (Q : LoopQuartic) {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    (pp : Fin (m + 1) → Fin 4 → ℝ) : Prop :=
  ∀ (z : Fin (m + 1) → ℝ) (ρ a b c : ℝ) (b₁ : Fin 4 → ℝ),
    IsFaceMat (symanzikMatrix α z) ρ a b c → ρ ≠ 0 → uHat ρ a b c ≠ 0 →
    (∀ μ, symanzikVector α pp z 1 μ = ρ * b₁ μ) → ∀ v : ℝ,
      (ρ : ℂ) ^ (p + 1) * paramAtV n Q α pp z v = ((uHat ρ a b c ^ 2 : ℝ) : ℂ)⁻¹ *
        ((ρ : ℂ) ^ (p - B.d) * B.val ρ a b c (symanzikVector α pp z 0) b₁ v)

/-- The self-energy bracket `faceBrSE` as a `FaceBr`. -/
noncomputable def se (n : ℕ) (Q : LoopQuartic) : FaceBr 3 where
  d := 1
  k := ![n - 3, n - 4, n - 5]
  C := ![fun ρ a b c β₀ b₁ => ((n - 4).factorial : ℂ) * Q.evalC (faceX ρ a b c β₀ b₁),
    fun ρ a b c β₀ b₁ => ((n - 5).factorial : ℂ) / 2 *
      cTwoG Q (faceG ρ a b c) (faceX ρ a b c β₀ b₁),
    fun ρ a b c _ _ => ((n - 6).factorial : ℂ) / 4 * cFourG Q (faceG ρ a b c)]

/-- The vertex bracket `faceBrVtx` as a `FaceBr`. -/
noncomputable def vtx (n : ℕ) (Q : LoopQuartic) : FaceBr 3 where
  d := 2
  k := ![n - 3, n - 4, n - 5]
  C := ![fun ρ a b c β₀ b₁ => ((n - 4).factorial : ℂ) * ((ρ : ℂ) * Q.evalC (faceX ρ a b c β₀ b₁)),
    fun ρ a b c β₀ b₁ => ((n - 5).factorial : ℂ) / 2 *
      ((ρ : ℂ) * cTwoG Q (faceG ρ a b c) (faceX ρ a b c β₀ b₁) +
        ((a / uHat ρ a b c : ℝ) : ℂ) * cTwoG Q (eS 1) (faceX ρ a b c β₀ b₁)),
    fun ρ a b c _ _ => ((n - 6).factorial : ℂ) / 4 * ((ρ : ℂ) * cFourG Q (faceG ρ a b c) +
      ((a / uHat ρ a b c : ℝ) : ℂ) * cFourX Q (faceG ρ a b c) (eS 1))]

theorem val_se (n : ℕ) (Q : LoopQuartic) (ρ a b c : ℝ) (β₀ b₁ : Fin 4 → ℝ) (v : ℝ) :
    (se n Q).val ρ a b c β₀ b₁ v = faceBrSE n Q ρ a b c β₀ b₁ v := by
  simp only [val, se]
  rw [Fin.sum_univ_three]
  rfl

theorem val_vtx (n : ℕ) (Q : LoopQuartic) (ρ a b c : ℝ) (β₀ b₁ : Fin 4 → ℝ) (v : ℝ) :
    (vtx n Q).val ρ a b c β₀ b₁ v = faceBrVtx n Q ρ a b c β₀ b₁ v := by
  simp only [val, vtx]
  rw [Fin.sum_univ_three]
  rfl

variable {n p m : ℕ} {Q : LoopQuartic} {α : Fin (m + 1) → Fin 2 → ℝ} {pp : Fin (m + 1) → Fin 4 → ℝ}

theorem rep_se (hQ : LoopDegLe 1 1 Q) (hp : 1 ≤ p) : (se n Q).Rep n p Q α pp :=
  fun _ _ _ _ _ _ h hρ hu hβ v => by
    rw [val_se]; exact paramAtV_face_se hQ hp h hρ hu hβ v

theorem rep_vtx (hQ : LoopDegLe 1 2 Q) (hp : 2 ≤ p) : (vtx n Q).Rep n p Q α pp :=
  fun _ _ _ _ _ _ h hρ hu hβ v => by
    rw [val_vtx]; exact paramAtV_face_vtx hQ hp h hρ hu hβ v

end FaceBr

/-! ### The rescaled face integrand -/

namespace FaceShape

variable {p q r : ℕ} (S : FaceShape p q) (B : FaceBr r)

/-- The full coefficient `Û⁻² ρ^{p-d} Cⱼ` at the join data. -/
noncomputable def coefJ (j : Fin r) (ρ : ℝ) (W : Fin (p + 1) → ℝ) (V : Fin (q + 1) → ℝ) : ℂ :=
  ((S.uJ ρ W V ^ 2 : ℝ) : ℂ)⁻¹ *
    ((ρ : ℂ) ^ (p - B.d) * B.C j ρ (S.aJ ρ W V) (S.b W) (S.c W) (S.PJ ρ W V) (S.b₁ W))

/-- **The rescaled face integrand** `θ ∑ⱼ Û⁻² ρ^{p-d} Cⱼ (vHat + θσ)^{-kⱼ}`, `θ = W_γ`. -/
noncomputable def hJ (ρ σ : ℝ) (W : Fin (p + 1) → ℝ) (V : Fin (q + 1) → ℝ) : ℂ :=
  (W S.γ : ℂ) * ∑ j, S.coefJ B j ρ W V * (((S.vHat ρ W V + W S.γ * σ : ℝ) : ℂ) ^ B.k j)⁻¹

/-- **The rescaled face function** `g(ρ, σ) = (1 - ρ)^q ∫_{Δ_p × Δ_q} hJ ρ σ`. -/
noncomputable def gJ (ρ σ : ℝ) : ℂ :=
  (((1 - ρ) ^ q : ℝ) : ℂ) * ∫ x in simplexSet p ×ˢ simplexSet q,
    S.hJ B ρ σ (simplexPoint x.1) (simplexPoint x.2)

/-- The integrand of the collapsed density at the squared photon mass `u`. -/
noncomputable def fU (n : ℕ) (Q : LoopQuartic) (u : ℝ) (z : Fin (p + 1 + q + 1) → ℝ) : ℂ :=
  (z S.γJ : ℂ) * paramAtV n Q S.α S.pp z (symanzikV S.α S.pp S.M z + z S.γJ * u)

variable {B} {n : ℕ} {Q : LoopQuartic}

/-- **The integrand in join coordinates is the rescaled face integrand** (`ρ > 0`). -/
theorem integrand_join_eq (hB : B.Rep n p Q S.α S.pp) {ρ : ℝ} (hρ : 0 < ρ)
    (W : Fin (p + 1) → ℝ) (V : Fin (q + 1) → ℝ) (hu : S.uJ ρ W V ≠ 0) (u : ℝ) :
    (ρ : ℂ) ^ p * S.fU n Q u (joinZ ρ W V) = S.hJ B ρ (ρ * u) W V := by
  have h := hB (joinZ ρ W V) ρ _ _ _ (S.b₁ W) (S.isFaceMat ρ W V) hρ.ne' hu
    (S.symanzikVector_one ρ W V)
    (symanzikV S.α S.pp S.M (joinZ ρ W V) + joinZ ρ W V S.γJ * u)
  rw [S.symanzikVector_zero, S.symanzikV_join_eq ρ W V hρ.ne' hu, S.joinZ_γJ] at h
  rw [fU, S.symanzikV_join_eq ρ W V hρ.ne' hu, S.joinZ_γJ, hJ]
  have e : S.vHat ρ W V + ρ * W S.γ * u = S.vHat ρ W V + W S.γ * (ρ * u) := by ring
  rw [e] at h ⊢
  simp only [coefJ, FaceBr.val, Finset.mul_sum] at h ⊢
  calc (ρ : ℂ) ^ p * (((ρ * W S.γ : ℝ) : ℂ) * paramAtV n Q S.α S.pp (joinZ ρ W V)
        (S.vHat ρ W V + W S.γ * (ρ * u)))
      = (W S.γ : ℂ) * ((ρ : ℂ) ^ (p + 1) * paramAtV n Q S.α S.pp (joinZ ρ W V)
        (S.vHat ρ W V + W S.γ * (ρ * u))) := by push_cast; ring
    _ = _ := by
      rw [h, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by rw [uJ]; ring

/-- The weight of the face block. -/
def blockSum (z : Fin (p + 1 + q + 1) → ℝ) : ℝ := ∑ i : Fin (p + 1), z (Fin.castAdd (q + 1) i)

theorem blockSum_joinZ (ρ : ℝ) (w : Fin p → ℝ) (V : Fin (q + 1) → ℝ) :
    blockSum (joinZ ρ (simplexPoint w) V) = ρ := by
  simp [blockSum, joinZ, ← Finset.mul_sum, sum_simplexPoint]

theorem measurableSet_blockSum_le (ρ₀ : ℝ) :
    MeasurableSet {z : Fin (p + 1 + q + 1) → ℝ | blockSum z ≤ ρ₀} :=
  measurableSet_le (by unfold blockSum; fun_prop) measurable_const

/-- **The face sector of the density**: for `0 < ρ₀ < 1`, the integral over the simplex of the
integrand cut to `{∑_{face block} z ≤ ρ₀}` is `∫₀^{ρ₀} gJ ρ (ρ u) dρ`. -/
theorem integral_faceCut_eq (hB : B.Rep n p Q S.α S.pp) {ρ₀ u : ℝ} (hρ₀ : 0 < ρ₀)
    (hρ₁ : ρ₀ < 1)
    (hf : IntegrableOn (fun x => S.fU n Q u (simplexPoint x)) (simplexSet (p + 1 + q)))
    (hHi : ∀ ρ, 0 < ρ → ρ ≤ ρ₀ → IntegrableOn
      (fun x : (Fin p → ℝ) × (Fin q → ℝ) => S.hJ B ρ (ρ * u) (simplexPoint x.1) (simplexPoint x.2))
      (simplexSet p ×ˢ simplexSet q)) :
    ∫ x in simplexSet (p + 1 + q),
        {z | blockSum z ≤ ρ₀}.indicator (S.fU n Q u) (simplexPoint x) =
      ∫ ρ in (0 : ℝ)..ρ₀, S.gJ B ρ (ρ * u) := by
  have hm : MeasurableSet ((fun x : Fin (p + 1 + q) → ℝ => simplexPoint x) ⁻¹'
      {z | blockSum z ≤ ρ₀}) :=
    continuous_simplexPoint'.measurable (measurableSet_blockSum_le ρ₀)
  have hf' : IntegrableOn (fun x => {z | blockSum z ≤ ρ₀}.indicator (S.fU n Q u) (simplexPoint x))
      (simplexSet (p + 1 + q)) := by
    have := hf.indicator hm
    refine this.congr_fun (fun x _ => ?_) (measurableSet_simplexSet _)
    by_cases hx : simplexPoint x ∈ {z | blockSum z ≤ ρ₀}
    · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ _ from hx)]
    · rw [indicator_of_notMem hx, indicator_of_notMem (show x ∉ _ from hx)]
  set G : ℝ → ℂ := fun ρ => (ρ ^ p * (1 - ρ) ^ q) • ∫ w in simplexSet p,
    ∫ v in simplexSet q, S.fU n Q u (joinZ ρ (simplexPoint w) (simplexPoint v)) with hG
  have hcut : ∀ ρ, (ρ ^ p * (1 - ρ) ^ q) • ∫ w in simplexSet p, ∫ v in simplexSet q,
      {z | blockSum z ≤ ρ₀}.indicator (S.fU n Q u) (joinZ ρ (simplexPoint w) (simplexPoint v)) =
      (Iic ρ₀).indicator G ρ := by
    intro ρ
    have hb : ∀ (w : Fin p → ℝ) (v : Fin q → ℝ),
        blockSum (p := p) (q := q) (joinZ ρ (simplexPoint w) (simplexPoint v)) = ρ :=
      fun w v => blockSum_joinZ ρ w _
    by_cases hρ : ρ ≤ ρ₀
    · rw [indicator_of_mem (show ρ ∈ Iic ρ₀ from hρ)]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun w => integral_congr_ae (ae_of_all _ fun v => ?_))
      exact indicator_of_mem (s := {z : Fin (p + 1 + q + 1) → ℝ | blockSum z ≤ ρ₀})
        (show blockSum (p := p) (q := q) (joinZ ρ (simplexPoint w) (simplexPoint v)) ≤ ρ₀ by
          rw [hb w v]; exact hρ) (S.fU n Q u)
    · rw [indicator_of_notMem (show ρ ∉ Iic ρ₀ from hρ)]
      have h0 : ∀ (w : Fin p → ℝ) (v : Fin q → ℝ), {z | blockSum z ≤ ρ₀}.indicator (S.fU n Q u)
          (joinZ ρ (simplexPoint w) (simplexPoint v)) = 0 := fun w v =>
        indicator_of_notMem (show joinZ ρ (simplexPoint w) (simplexPoint v) ∉
          {z : Fin (p + 1 + q + 1) → ℝ | blockSum z ≤ ρ₀} from fun h => hρ (by
            have h' : blockSum (p := p) (q := q) (joinZ ρ (simplexPoint w) (simplexPoint v)) ≤ ρ₀ :=
              h
            rwa [hb w v] at h')) _
      simp only [h0, integral_zero, smul_zero]
  rw [integral_simplex_join hf']
  refine (intervalIntegral.integral_congr (fun ρ _ => hcut ρ)).trans ?_
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le hρ₀.le,
    setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right hρ₁.le]
  refine setIntegral_congr_fun measurableSet_Ioc fun ρ hρ => ?_
  have hρ0 : 0 < ρ := hρ.1
  have hρ1 : ρ < 1 := lt_of_le_of_lt hρ.2 hρ₁
  have hpt : ∀ w ∈ simplexSet p, ∀ v ∈ simplexSet q,
      (ρ : ℂ) ^ p * S.fU n Q u (joinZ ρ (simplexPoint w) (simplexPoint v)) =
        S.hJ B ρ (ρ * u) (simplexPoint w) (simplexPoint v) := by
    intro w hw v hv
    obtain ⟨hw0, hw1⟩ := simplexPoint_mem_stdSimplex hw
    obtain ⟨-, hv1⟩ := simplexPoint_mem_stdSimplex hv
    refine S.integrand_join_eq hB hρ0 _ _ (ne_of_gt ?_) u
    linarith [S.uJ_ge ρ _ _ hw0 hw1 hv1 hρ0.le]
  have hprod := setIntegral_prod (μ := (volume : Measure (Fin p → ℝ)))
    (ν := (volume : Measure (Fin q → ℝ)))
    (fun x : (Fin p → ℝ) × (Fin q → ℝ) => S.hJ B ρ (ρ * u) (simplexPoint x.1) (simplexPoint x.2))
    (s := simplexSet p) (t := simplexSet q)
    (by rw [← Measure.volume_eq_prod]; exact hHi ρ hρ0 hρ.2)
  rw [← Measure.volume_eq_prod] at hprod
  rw [gJ, hprod, hG]
  dsimp only
  rw [Complex.real_smul, ofReal_mul, ofReal_pow, mul_comm ((ρ : ℂ) ^ p), mul_assoc,
    ← integral_const_mul]
  congr 1
  refine setIntegral_congr_fun (measurableSet_simplexSet p) fun w hw => ?_
  rw [← integral_const_mul]
  exact setIntegral_congr_fun (measurableSet_simplexSet q) fun v hv => hpt w hw v hv

end FaceShape

end QED.GradedProof.RPi4

end
