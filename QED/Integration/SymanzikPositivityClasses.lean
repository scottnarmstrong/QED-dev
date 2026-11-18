/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.SymanzikPositivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

/-!
# Positivity of the two-loop Symanzik remainder for the corner, self-energy and VP classes

Helper theorems for obligation O2-12 (`docs/TWO-LOOP-DERIVATION.md`, section 4.4), continuing
`QED/Integration/SymanzikPositivity.lean` (the ladder `L` and the crossed ladder `X`) to the
corner classes `C₊`, `C₋`, the self-energy classes `S₊`, `S₋` and the vacuum-polarization class
`VP` of the order-`e⁵` vertex, with the loop matrices `class5LoopMatrix`
(`QED/Integration/SymanzikIntegrabilityClasses.lean`). The Furry classes `F±` are not treated:
they cancel (O2-3).

Kinematics as for `L`, `X`: on-shell `p·p = p'·p' = -m²`, `q = p' - p` with `q·q ≥ 0`, photon
masses `λᵢ² ≥ m_γ²`; external momenta routed along the open electron line (`p` before the
external-photon vertex, `p'` after it, photon and closed-loop lines carrying none). For `VP` the
two closed-loop lines have mass `M_f` (any real; `M_f² ≥ m²` is used only for the uniform
constant).

## The method

As for `L`, `X`: `V = ∑ᵢ zᵢ Mᵢ² - m² R(a) + (q²/4) (R(b) - R(a))` (`le_symanzikV_of_routing`, a
class-independent form of `le_symanzikV_classLX_of`), with

* `R(b) - R(a) = 4 β(x)ᵀ A⁻¹ β(y)` for the indicator vectors `x`, `y` of the open-line lines
  before and after the external vertex, and `U · β(x)ᵀ A⁻¹ β(y)` a polynomial with nonnegative
  coefficients (`remainder_classCp_le`, …); so `V` is nondecreasing in `q² ≥ 0`;
* `R(a) ≤ ∑ᵢ zᵢ (αᵢ·y + aᵢ)²` for trial loop momenta `y`, read as trial flows: a fraction of the
  current is diverted from a segment of the electron path through a photon line joining its
  endpoints (`C±`: two segments, `S±`: the photon `(v₀v₄)`), or, for `VP`, through the path
  photon–loop line–photon.

The bounds (`E = z₀ + z₁ + z₂ + z₃` the fermion weight):

* `C₊`, `C₋`: `V ≥ m² E²/4 + m_γ² (1 - E)` (`le_symanzikV_classCp`, `le_symanzikV_classCm`);
* `S₊`, `S₋`: `V ≥ m² E² + m_γ² (1 - E)` (`le_symanzikV_classSp`, `le_symanzikV_classSm`);
* `VP`: `V ≥ m² (z₀ + z₁)² + M_f² (z₂ + z₃) + m_γ² (z₄ + z₅)` (`le_symanzikV_classVP`);

hence `V ≥ (3/4) min(m²/4, m_γ²)` (`C±`) and `V ≥ (3/4) min(m², m_γ²)` (`S±`, and `VP` when
`M_f² ≥ m²`), and `V > 0` when `m, m_γ ≠ 0`.

## Repeated lines

`symanzikV_comp`: for a map `σ` of lines (repeating line `σ i` as line `i`, with the same loop
row and momentum), `V` of the repeated graph at `z` is `V` of the original graph at the merged
weights `wⱼ = ∑_{σ i = j} zᵢ`, plus `∑ᵢ zᵢ (M'ᵢ² - M_{σ i}²)`; and `U` is likewise `U` at `w`
(`symanzikU_comp`). So every lower bound of the original graph transfers when each repeated line
has mass at least that of its original (`le_symanzikV_comp_of`). This covers the Pauli–Villars
forms `class5LoopMatrixPV` (each photon line doubled; `symanzikV_classLPV_ge`, …,
`symanzikV_classVPPV_ge`, for `L`, `X`, `C±`, `S±`, `VP`) and the doubled bubble
`loopMatrixVPBubble` (`symanzikV_VPBubble_ge`), with the same uniform constants.

The hypothesis `U(z) ≠ 0` is necessary, as for `L` and `X` (the junk value of the inverse).
-/

@[expose] public section

open Matrix Finset

namespace QED.Integration.TwoLoop

/-! ### The class-independent reduction -/

/-- **The reduction.** For line momenta `pᵢ = aᵢ P + bᵢ K`, `P = (p + p')/2`, `K = (p' - p)/2`
with `p`, `p'` on shell and `q² ≥ 0`: if `∑ᵢ zᵢ Mᵢ² ≥ m² E + L`, `R(a) ≤ E - B` and
`R(a) ≤ R(b)`, then `V ≥ m² B + L`. -/
theorem le_symanzikV_of_routing {n : ℕ} {α : Fin (n + 1) → Fin 2 → ℝ} {M : Fin (n + 1) → ℝ}
    {a b : Fin (n + 1) → ℝ} {mass E B L : ℝ} {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {z : Fin (n + 1) → ℝ}
    (hM : mass ^ 2 * E + L ≤ ∑ i, z i * M i ^ 2)
    (hRa : remainder α z a ≤ E - B) (hRb : remainder α z a ≤ remainder α z b) :
    mass ^ 2 * B + L ≤ symanzikV α
      (fun i => a i • ((1 / 2 : ℝ) • (p + p')) + b i • ((1 / 2 : ℝ) • (p' - p))) M z := by
  rw [symanzikV_smul_add_smul _ _ _ _ _ (dot_half_add_half_sub hp hp'), dot_half_add_self hp hp']
  have hK := dot_half_sub_self_nonneg hq
  set k := Minkowski.dot ((1 / 2 : ℝ) • (p' - p)) ((1 / 2 : ℝ) • (p' - p))
  have h1 : 0 ≤ k * (remainder α z b - remainder α z a) := mul_nonneg hK (by linarith)
  have h2 : mass ^ 2 * remainder α z a ≤ mass ^ 2 * (E - B) :=
    mul_le_mul_of_nonneg_left hRa (sq_nonneg _)
  nlinarith

/-- `m² E² + c s ≥ (3/4) c'`-type bound with a separate coefficient: if `c ≤ k`, `c ≤ μ`,
`E + s = 1`, then `k E² + μ s ≥ (3/4) c`. -/
theorem three_quarters_le_of {k μ c E s : ℝ} (hc : c ≤ k) (hc' : c ≤ μ) (hc0 : 0 ≤ c)
    (hE : E + s = 1) (hs : 0 ≤ s) :
    3 / 4 * c ≤ k * E ^ 2 + μ * s := by
  have h1 : c * E ^ 2 ≤ k * E ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
  have h2 : c * s ≤ μ * s := mul_le_mul_of_nonneg_right hc' hs
  nlinarith [mul_nonneg hc0 (sq_nonneg (E - 1 / 2))]

/-! ### Loop matrices, momenta and masses -/

/-- The loop matrix of `C₊` (lines `v₀v₁, v₁v₂, v₂v₃, v₃v₄`, photons `(v₀v₃)`, `(v₂v₄)`;
external photon at `v₁`). -/
noncomputable abbrev loopMatrixCp : Fin 6 → Fin 2 → ℝ := castLoopMatrix (class5LoopMatrix .Cp)

/-- The loop matrix of `C₋` (photons `(v₀v₂)`, `(v₁v₄)`; external photon at `v₃`). -/
noncomputable abbrev loopMatrixCm : Fin 6 → Fin 2 → ℝ := castLoopMatrix (class5LoopMatrix .Cm)

/-- The loop matrix of `S₊` (photons `(v₀v₄)`, `(v₂v₃)`; external photon at `v₁`). -/
noncomputable abbrev loopMatrixSp : Fin 6 → Fin 2 → ℝ := castLoopMatrix (class5LoopMatrix .Sp)

/-- The loop matrix of `S₋` (photons `(v₀v₄)`, `(v₁v₂)`; external photon at `v₃`). -/
noncomputable abbrev loopMatrixSm : Fin 6 → Fin 2 → ℝ := castLoopMatrix (class5LoopMatrix .Sm)

/-- The loop matrix of `VP` (lines `v₀v₁, v₁v₂`, the loop `v₃v₄, v₄v₃`, photons `(v₀v₃)`,
`(v₂v₄)`; external photon at `v₁`). -/
noncomputable abbrev loopMatrixVP : Fin 6 → Fin 2 → ℝ := castLoopMatrix (class5LoopMatrix .VP)

/-- The external momenta of the lines of `C₊` and `S₊` (external photon at `v₁`), routed along
the electron path: `p` on `v₀v₁`, `p'` on `v₁v₂, v₂v₃, v₃v₄`, none on the photons. -/
def classCpSpMomenta (p p' : Fin 4 → ℝ) : Fin 6 → Fin 4 → ℝ := ![p, p', p', p', 0, 0]

/-- The external momenta of the lines of `C₋` and `S₋` (external photon at `v₃`): `p` on
`v₀v₁, v₁v₂, v₂v₃`, `p'` on `v₃v₄`. -/
def classCmSmMomenta (p p' : Fin 4 → ℝ) : Fin 6 → Fin 4 → ℝ := ![p, p, p, p', 0, 0]

/-- The external momenta of the lines of `VP`: `p` on `v₀v₁`, `p'` on `v₁v₂`, none on the
loop and the photons. -/
def classVPMomenta (p p' : Fin 4 → ℝ) : Fin 6 → Fin 4 → ℝ := ![p, p', 0, 0, 0, 0]

/-- The masses of the lines of `VP`: open line `m`, loop `M_f`, photons `λ₁`, `λ₂`. -/
def classVPMasses (mass massF lam₁ lam₂ : ℝ) : Fin 6 → ℝ :=
  ![mass, mass, massF, massF, lam₁, lam₂]

theorem classCpSpMomenta_eq (p p' : Fin 4 → ℝ) :
    classCpSpMomenta p p' = fun i =>
      (![1, 1, 1, 1, 0, 0] : Fin 6 → ℝ) i • ((1 / 2 : ℝ) • (p + p')) +
        (![-1, 1, 1, 1, 0, 0] : Fin 6 → ℝ) i • ((1 / 2 : ℝ) • (p' - p)) := by
  funext i μ
  fin_cases i <;> simp [classCpSpMomenta] <;> ring

theorem classCmSmMomenta_eq (p p' : Fin 4 → ℝ) :
    classCmSmMomenta p p' = fun i =>
      (![1, 1, 1, 1, 0, 0] : Fin 6 → ℝ) i • ((1 / 2 : ℝ) • (p + p')) +
        (![-1, -1, -1, 1, 0, 0] : Fin 6 → ℝ) i • ((1 / 2 : ℝ) • (p' - p)) := by
  funext i μ
  fin_cases i <;> simp [classCmSmMomenta] <;> ring

theorem classVPMomenta_eq (p p' : Fin 4 → ℝ) :
    classVPMomenta p p' = fun i =>
      (![1, 1, 0, 0, 0, 0] : Fin 6 → ℝ) i • ((1 / 2 : ℝ) • (p + p')) +
        (![-1, 1, 0, 0, 0, 0] : Fin 6 → ℝ) i • ((1 / 2 : ℝ) • (p' - p)) := by
  funext i μ
  fin_cases i <;> simp [classVPMomenta] <;> ring

theorem sum_mul_classVPMasses_sq (mass massF lam₁ lam₂ : ℝ) (z : Fin 6 → ℝ) :
    ∑ i, z i * classVPMasses mass massF lam₁ lam₂ i ^ 2 =
      mass ^ 2 * (z 0 + z 1) + massF ^ 2 * (z 2 + z 3) + lam₁ ^ 2 * z 4 + lam₂ ^ 2 * z 5 := by
  simp [classVPMasses, Fin.sum_univ_six]
  ring

/-- The mass term of the open-line classes: `∑ᵢ zᵢ Mᵢ² ≥ m² E + m_γ² (z₄ + z₅)`. -/
theorem le_sum_mul_classLXMasses_sq {mass mγ lam₁ lam₂ : ℝ} (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2)
    (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ} (hz : ∀ i, 0 ≤ z i) :
    mass ^ 2 * (z 0 + z 1 + z 2 + z 3) + mγ ^ 2 * (z 4 + z 5) ≤
      ∑ i, z i * classLXMasses mass lam₁ lam₂ i ^ 2 := by
  rw [sum_mul_classLXMasses_sq]
  have h3 : mγ ^ 2 * z 4 ≤ lam₁ ^ 2 * z 4 := mul_le_mul_of_nonneg_right hlam₁ (hz 4)
  have h4 : mγ ^ 2 * z 5 ≤ lam₂ ^ 2 * z 5 := mul_le_mul_of_nonneg_right hlam₂ (hz 5)
  linarith

/-- Two trial bounds `R ≤ E - G²`, `R ≤ E - H²` with `G + H ≥ E ≥ 0` give `R ≤ E - E²/4`. -/
theorem le_sub_sq_div_four {R E G H : ℝ} (hG : R ≤ E - G ^ 2) (hH : R ≤ E - H ^ 2)
    (hE : 0 ≤ E) (hGH : E ≤ G + H) : R ≤ E - E ^ 2 / 4 := by
  have h : E ^ 2 / 4 ≤ (G ^ 2 + H ^ 2) / 2 := by
    nlinarith [sq_nonneg (G - H), mul_le_mul hGH hGH hE (hE.trans hGH)]
  linarith

/-! ### `C₊` -/

/-- `C₊`: `R(b) - R(a) = 4 β(x)ᵀ A⁻¹ β(y) ≥ 0`, `U β(x)ᵀ A⁻¹ β(y) = z₀ (z₁z₂ + z₁z₃ + z₁z₅ +
z₂z₅)`. -/
theorem remainder_classCp_le {z : Fin 6 → ℝ} (hz : ∀ i, 0 ≤ z i) :
    remainder loopMatrixCp z ![1, 1, 1, 1, 0, 0] ≤
      remainder loopMatrixCp z ![-1, 1, 1, 1, 0, 0] := by
  have h := remainder_sub_sub_remainder_add loopMatrixCp z ![1, 0, 0, 0, 0, 0] ![0, 1, 1, 1, 0, 0]
  have ha : (fun i => (![1, 0, 0, 0, 0, 0] : Fin 6 → ℝ) i + (![0, 1, 1, 1, 0, 0] : Fin 6 → ℝ) i) =
      ![1, 1, 1, 1, 0, 0] := by
    funext i; fin_cases i <;> simp
  have hb : (fun i => (![0, 1, 1, 1, 0, 0] : Fin 6 → ℝ) i - (![1, 0, 0, 0, 0, 0] : Fin 6 → ℝ) i) =
      ![-1, 1, 1, 1, 0, 0] := by
    funext i; fin_cases i <;> simp
  rw [ha, hb, dotProduct_inv_symanzikMatrix_mulVec] at h
  simp [coefVec, symanzikMatrix, Fin.sum_univ_six, castLoopMatrix, class5LoopMatrix] at h
  have hpoly : 0 ≤ (symanzikU loopMatrixCp z)⁻¹ *
      (z 0 * (z 1 * z 2 + z 1 * z 3 + z 1 * z 5 + z 2 * z 5)) := by
    have := hz 0; have := hz 1; have := hz 2; have := hz 3; have := hz 4; have := hz 5
    have := symanzikU_nonneg loopMatrixCp hz
    positivity
  nlinarith [h, hpoly]

/-- `C₊`: `R(a) ≤ G (1 - G)² + z₃ + z₄ G²`, `G = z₀ + z₁ + z₂`, from `y = (-G, 0)` (the current
fraction `G` through the photon `(v₀v₃)`). -/
theorem remainder_classCp_le_sum₁ {z : Fin 6 → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hU : symanzikU loopMatrixCp z ≠ 0) :
    remainder loopMatrixCp z ![1, 1, 1, 1, 0, 0] ≤
      (z 0 + z 1 + z 2) * (1 - (z 0 + z 1 + z 2)) ^ 2 + z 3 + z 4 * (z 0 + z 1 + z 2) ^ 2 := by
  refine (remainder_le_sum_sq loopMatrixCp hz hU _ ![-(z 0 + z 1 + z 2), 0]).trans (le_of_eq ?_)
  simp [Fin.sum_univ_six, castLoopMatrix, class5LoopMatrix]
  ring

/-- `C₊`: `R(a) ≤ z₀ + z₁ + H (1 - H)² + z₅ H²`, `H = z₂ + z₃`, from `y = (-H, H)` (the current
fraction `H` through the photon `(v₂v₄)`). -/
theorem remainder_classCp_le_sum₂ {z : Fin 6 → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hU : symanzikU loopMatrixCp z ≠ 0) :
    remainder loopMatrixCp z ![1, 1, 1, 1, 0, 0] ≤
      z 0 + z 1 + (z 2 + z 3) * (1 - (z 2 + z 3)) ^ 2 + z 5 * (z 2 + z 3) ^ 2 := by
  refine (remainder_le_sum_sq loopMatrixCp hz hU _ ![-(z 2 + z 3), z 2 + z 3]).trans
    (le_of_eq ?_)
  simp [Fin.sum_univ_six, castLoopMatrix, class5LoopMatrix]
  ring

/-- **No thresholds for `C₊`.** For the corner class `C₊` with electron mass `m`, photon masses
`λᵢ² ≥ m_γ²`, on-shell `p·p = p'·p' = -m²` and `q = p' - p` with `q·q ≥ 0`, at every point of the
simplex with `U(z) ≠ 0`: `V(z) ≥ m² E²/4 + m_γ² (1 - E)`, `E = z₀ + z₁ + z₂ + z₃`. -/
theorem le_symanzikV_classCp {mass mγ lam₁ lam₂ : ℝ} {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2) (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU loopMatrixCp z ≠ 0) :
    mass ^ 2 * ((z 0 + z 1 + z 2 + z 3) ^ 2 / 4) + mγ ^ 2 * (z 4 + z 5) ≤
      symanzikV loopMatrixCp (classCpSpMomenta p p') (classLXMasses mass lam₁ lam₂) z := by
  rw [classCpSpMomenta_eq]
  refine le_symanzikV_of_routing hp hp' hq (le_sum_mul_classLXMasses_sq hlam₁ hlam₂ hz) ?_
    (remainder_classCp_le hz)
  have r1 := remainder_classCp_le_sum₁ hz hU
  have r2 := remainder_classCp_le_sum₂ hz hU
  have h1 : z 0 + z 1 + z 2 + z 3 + z 4 + z 5 = 1 := by
    simpa [Fin.sum_univ_six] using hz1
  have hz0 := hz 0; have hz1' := hz 1; have hz2 := hz 2; have hz3 := hz 3
  have hz4 := hz 4; have hz5 := hz 5
  refine le_sub_sq_div_four (G := z 0 + z 1 + z 2) (H := z 2 + z 3) ?_ ?_ (by linarith)
    (by linarith)
  · have : z 4 * (z 0 + z 1 + z 2) ^ 2 ≤ (1 - (z 0 + z 1 + z 2)) * (z 0 + z 1 + z 2) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    nlinarith
  · have : z 5 * (z 2 + z 3) ^ 2 ≤ (1 - (z 2 + z 3)) * (z 2 + z 3) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    nlinarith

/-- **No thresholds for `C₊`, uniform constant:** `V(z) ≥ (3/4) min(m²/4, m_γ²)`. -/
theorem symanzikV_classCp_ge {mass mγ lam₁ lam₂ : ℝ} {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2) (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU loopMatrixCp z ≠ 0) :
    3 / 4 * min (mass ^ 2 / 4) (mγ ^ 2) ≤
      symanzikV loopMatrixCp (classCpSpMomenta p p') (classLXMasses mass lam₁ lam₂) z := by
  refine le_trans ?_ (le_symanzikV_classCp hp hp' hq hlam₁ hlam₂ hz hz1 hU)
  have h1 : z 0 + z 1 + z 2 + z 3 + (z 4 + z 5) = 1 := by
    have := hz1; simp only [Fin.sum_univ_six] at this; linarith
  have h := three_quarters_le_of (k := mass ^ 2 / 4) (μ := mγ ^ 2) (min_le_left _ _)
    (min_le_right _ _) (le_min (by positivity) (sq_nonneg _)) h1 (add_nonneg (hz 4) (hz 5))
  linarith

theorem symanzikV_classCp_pos {mass mγ lam₁ lam₂ : ℝ} (hm : mass ≠ 0) (hmγ : mγ ≠ 0)
    {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2) (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU loopMatrixCp z ≠ 0) :
    0 < symanzikV loopMatrixCp (classCpSpMomenta p p') (classLXMasses mass lam₁ lam₂) z := by
  have h0 : 0 < min (mass ^ 2 / 4) (mγ ^ 2) := lt_min (by positivity) (by positivity)
  linarith [symanzikV_classCp_ge hp hp' hq hlam₁ hlam₂ hz hz1 hU]

/-! ### `C₋` -/

/-- `C₋`: `R(b) - R(a) = 4 β(x)ᵀ A⁻¹ β(y) ≥ 0`, `U β(x)ᵀ A⁻¹ β(y) = z₃ (z₀z₂ + z₁z₂ + z₁z₄ +
z₂z₄)`. -/
theorem remainder_classCm_le {z : Fin 6 → ℝ} (hz : ∀ i, 0 ≤ z i) :
    remainder loopMatrixCm z ![1, 1, 1, 1, 0, 0] ≤
      remainder loopMatrixCm z ![-1, -1, -1, 1, 0, 0] := by
  have h := remainder_sub_sub_remainder_add loopMatrixCm z ![1, 1, 1, 0, 0, 0] ![0, 0, 0, 1, 0, 0]
  have ha : (fun i => (![1, 1, 1, 0, 0, 0] : Fin 6 → ℝ) i + (![0, 0, 0, 1, 0, 0] : Fin 6 → ℝ) i) =
      ![1, 1, 1, 1, 0, 0] := by
    funext i; fin_cases i <;> simp
  have hb : (fun i => (![0, 0, 0, 1, 0, 0] : Fin 6 → ℝ) i - (![1, 1, 1, 0, 0, 0] : Fin 6 → ℝ) i) =
      ![-1, -1, -1, 1, 0, 0] := by
    funext i; fin_cases i <;> simp
  rw [ha, hb, dotProduct_inv_symanzikMatrix_mulVec] at h
  simp [coefVec, symanzikMatrix, Fin.sum_univ_six, castLoopMatrix, class5LoopMatrix] at h
  have hpoly : 0 ≤ (symanzikU loopMatrixCm z)⁻¹ *
      (z 3 * (z 0 * z 2 + z 1 * z 2 + z 1 * z 4 + z 2 * z 4)) := by
    have := hz 0; have := hz 1; have := hz 2; have := hz 3; have := hz 4; have := hz 5
    have := symanzikU_nonneg loopMatrixCm hz
    positivity
  nlinarith [h, hpoly]

/-- `C₋`: `R(a) ≤ G (1 - G)² + z₂ + z₃ + z₄ G²`, `G = z₀ + z₁`, from `y = (-G, 0)` (the current
fraction `G` through the photon `(v₀v₂)`). -/
theorem remainder_classCm_le_sum₁ {z : Fin 6 → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hU : symanzikU loopMatrixCm z ≠ 0) :
    remainder loopMatrixCm z ![1, 1, 1, 1, 0, 0] ≤
      (z 0 + z 1) * (1 - (z 0 + z 1)) ^ 2 + z 2 + z 3 + z 4 * (z 0 + z 1) ^ 2 := by
  refine (remainder_le_sum_sq loopMatrixCm hz hU _ ![-(z 0 + z 1), 0]).trans (le_of_eq ?_)
  simp [Fin.sum_univ_six, castLoopMatrix, class5LoopMatrix]
  ring

/-- `C₋`: `R(a) ≤ z₀ + H (1 - H)² + z₅ H²`, `H = z₁ + z₂ + z₃`, from `y = (-H, -H)` (the current
fraction `H` through the photon `(v₁v₄)`). -/
theorem remainder_classCm_le_sum₂ {z : Fin 6 → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hU : symanzikU loopMatrixCm z ≠ 0) :
    remainder loopMatrixCm z ![1, 1, 1, 1, 0, 0] ≤
      z 0 + (z 1 + z 2 + z 3) * (1 - (z 1 + z 2 + z 3)) ^ 2 + z 5 * (z 1 + z 2 + z 3) ^ 2 := by
  refine (remainder_le_sum_sq loopMatrixCm hz hU _
    ![-(z 1 + z 2 + z 3), -(z 1 + z 2 + z 3)]).trans (le_of_eq ?_)
  simp [Fin.sum_univ_six, castLoopMatrix, class5LoopMatrix]
  ring

/-- **No thresholds for `C₋`.** Hypotheses as for `C₊`: `V(z) ≥ m² E²/4 + m_γ² (1 - E)`,
`E = z₀ + z₁ + z₂ + z₃`. -/
theorem le_symanzikV_classCm {mass mγ lam₁ lam₂ : ℝ} {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2) (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU loopMatrixCm z ≠ 0) :
    mass ^ 2 * ((z 0 + z 1 + z 2 + z 3) ^ 2 / 4) + mγ ^ 2 * (z 4 + z 5) ≤
      symanzikV loopMatrixCm (classCmSmMomenta p p') (classLXMasses mass lam₁ lam₂) z := by
  rw [classCmSmMomenta_eq]
  refine le_symanzikV_of_routing hp hp' hq (le_sum_mul_classLXMasses_sq hlam₁ hlam₂ hz) ?_
    (remainder_classCm_le hz)
  have r1 := remainder_classCm_le_sum₁ hz hU
  have r2 := remainder_classCm_le_sum₂ hz hU
  have h1 : z 0 + z 1 + z 2 + z 3 + z 4 + z 5 = 1 := by
    simpa [Fin.sum_univ_six] using hz1
  have hz0 := hz 0; have hz1' := hz 1; have hz2 := hz 2; have hz3 := hz 3
  have hz4 := hz 4; have hz5 := hz 5
  refine le_sub_sq_div_four (G := z 0 + z 1) (H := z 1 + z 2 + z 3) ?_ ?_ (by linarith)
    (by linarith)
  · have : z 4 * (z 0 + z 1) ^ 2 ≤ (1 - (z 0 + z 1)) * (z 0 + z 1) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    nlinarith
  · have : z 5 * (z 1 + z 2 + z 3) ^ 2 ≤ (1 - (z 1 + z 2 + z 3)) * (z 1 + z 2 + z 3) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    nlinarith

/-- **No thresholds for `C₋`, uniform constant:** `V(z) ≥ (3/4) min(m²/4, m_γ²)`. -/
theorem symanzikV_classCm_ge {mass mγ lam₁ lam₂ : ℝ} {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2) (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU loopMatrixCm z ≠ 0) :
    3 / 4 * min (mass ^ 2 / 4) (mγ ^ 2) ≤
      symanzikV loopMatrixCm (classCmSmMomenta p p') (classLXMasses mass lam₁ lam₂) z := by
  refine le_trans ?_ (le_symanzikV_classCm hp hp' hq hlam₁ hlam₂ hz hz1 hU)
  have h1 : z 0 + z 1 + z 2 + z 3 + (z 4 + z 5) = 1 := by
    have := hz1; simp only [Fin.sum_univ_six] at this; linarith
  have h := three_quarters_le_of (k := mass ^ 2 / 4) (μ := mγ ^ 2) (min_le_left _ _)
    (min_le_right _ _) (le_min (by positivity) (sq_nonneg _)) h1 (add_nonneg (hz 4) (hz 5))
  linarith

theorem symanzikV_classCm_pos {mass mγ lam₁ lam₂ : ℝ} (hm : mass ≠ 0) (hmγ : mγ ≠ 0)
    {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2) (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU loopMatrixCm z ≠ 0) :
    0 < symanzikV loopMatrixCm (classCmSmMomenta p p') (classLXMasses mass lam₁ lam₂) z := by
  have h0 : 0 < min (mass ^ 2 / 4) (mγ ^ 2) := lt_min (by positivity) (by positivity)
  linarith [symanzikV_classCm_ge hp hp' hq hlam₁ hlam₂ hz hz1 hU]

/-! ### `S₊` -/

/-- `S₊`: `R(b) - R(a) = 4 β(x)ᵀ A⁻¹ β(y) ≥ 0`, `U β(x)ᵀ A⁻¹ β(y) = z₀ (z₁z₂ + z₁z₅ + z₂z₃ +
z₂z₅ + z₃z₅)`. -/
theorem remainder_classSp_le {z : Fin 6 → ℝ} (hz : ∀ i, 0 ≤ z i) :
    remainder loopMatrixSp z ![1, 1, 1, 1, 0, 0] ≤
      remainder loopMatrixSp z ![-1, 1, 1, 1, 0, 0] := by
  have h := remainder_sub_sub_remainder_add loopMatrixSp z ![1, 0, 0, 0, 0, 0] ![0, 1, 1, 1, 0, 0]
  have ha : (fun i => (![1, 0, 0, 0, 0, 0] : Fin 6 → ℝ) i + (![0, 1, 1, 1, 0, 0] : Fin 6 → ℝ) i) =
      ![1, 1, 1, 1, 0, 0] := by
    funext i; fin_cases i <;> simp
  have hb : (fun i => (![0, 1, 1, 1, 0, 0] : Fin 6 → ℝ) i - (![1, 0, 0, 0, 0, 0] : Fin 6 → ℝ) i) =
      ![-1, 1, 1, 1, 0, 0] := by
    funext i; fin_cases i <;> simp
  rw [ha, hb, dotProduct_inv_symanzikMatrix_mulVec] at h
  simp [coefVec, symanzikMatrix, Fin.sum_univ_six, castLoopMatrix, class5LoopMatrix] at h
  have hpoly : 0 ≤ (symanzikU loopMatrixSp z)⁻¹ *
      (z 0 * (z 1 * z 2 + z 1 * z 5 + z 2 * z 3 + z 2 * z 5 + z 3 * z 5)) := by
    have := hz 0; have := hz 1; have := hz 2; have := hz 3; have := hz 4; have := hz 5
    have := symanzikU_nonneg loopMatrixSp hz
    positivity
  nlinarith [h, hpoly]

/-- `S₊`: `R(a) ≤ E (1 - E)² + z₄ E²`, from `y = (-E, 0)` (the current fraction `E` through the
photon `(v₀v₄)`). -/
theorem remainder_classSp_le_sum {z : Fin 6 → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hU : symanzikU loopMatrixSp z ≠ 0) :
    remainder loopMatrixSp z ![1, 1, 1, 1, 0, 0] ≤
      (z 0 + z 1 + z 2 + z 3) * (1 - (z 0 + z 1 + z 2 + z 3)) ^ 2 +
        z 4 * (z 0 + z 1 + z 2 + z 3) ^ 2 := by
  refine (remainder_le_sum_sq loopMatrixSp hz hU _ ![-(z 0 + z 1 + z 2 + z 3), 0]).trans
    (le_of_eq ?_)
  simp [Fin.sum_univ_six, castLoopMatrix, class5LoopMatrix]
  ring

/-- **No thresholds for `S₊`.** For the self-energy class `S₊` with electron mass `m`, photon
masses `λᵢ² ≥ m_γ²`, on-shell `p·p = p'·p' = -m²` and `q = p' - p` with `q·q ≥ 0`, at every point
of the simplex with `U(z) ≠ 0`: `V(z) ≥ m² E² + m_γ² (1 - E)`, `E = z₀ + z₁ + z₂ + z₃`. -/
theorem le_symanzikV_classSp {mass mγ lam₁ lam₂ : ℝ} {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2) (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU loopMatrixSp z ≠ 0) :
    mass ^ 2 * (z 0 + z 1 + z 2 + z 3) ^ 2 + mγ ^ 2 * (z 4 + z 5) ≤
      symanzikV loopMatrixSp (classCpSpMomenta p p') (classLXMasses mass lam₁ lam₂) z := by
  rw [classCpSpMomenta_eq]
  refine le_symanzikV_of_routing hp hp' hq (le_sum_mul_classLXMasses_sq hlam₁ hlam₂ hz) ?_
    (remainder_classSp_le hz)
  have h := remainder_classSp_le_sum hz hU
  have h1 : z 0 + z 1 + z 2 + z 3 + z 4 + z 5 = 1 := by
    simpa [Fin.sum_univ_six] using hz1
  set E := z 0 + z 1 + z 2 + z 3
  have h4 : z 4 * E ^ 2 ≤ (1 - E) * E ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith [hz 5]) (sq_nonneg _)
  nlinarith

/-- **No thresholds for `S₊`, uniform constant:** `V(z) ≥ (3/4) min(m², m_γ²)`. -/
theorem symanzikV_classSp_ge {mass mγ lam₁ lam₂ : ℝ} {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2) (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU loopMatrixSp z ≠ 0) :
    3 / 4 * min (mass ^ 2) (mγ ^ 2) ≤
      symanzikV loopMatrixSp (classCpSpMomenta p p') (classLXMasses mass lam₁ lam₂) z := by
  refine le_trans ?_ (le_symanzikV_classSp hp hp' hq hlam₁ hlam₂ hz hz1 hU)
  have h1 : z 0 + z 1 + z 2 + z 3 + (z 4 + z 5) = 1 := by
    have := hz1; simp only [Fin.sum_univ_six] at this; linarith
  exact three_quarters_le (min_le_left _ _) (min_le_right _ _)
    (le_min (sq_nonneg _) (sq_nonneg _)) h1 (add_nonneg (hz 4) (hz 5))

theorem symanzikV_classSp_pos {mass mγ lam₁ lam₂ : ℝ} (hm : mass ≠ 0) (hmγ : mγ ≠ 0)
    {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2) (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU loopMatrixSp z ≠ 0) :
    0 < symanzikV loopMatrixSp (classCpSpMomenta p p') (classLXMasses mass lam₁ lam₂) z := by
  have h0 : 0 < min (mass ^ 2) (mγ ^ 2) := lt_min (by positivity) (by positivity)
  linarith [symanzikV_classSp_ge hp hp' hq hlam₁ hlam₂ hz hz1 hU]

/-! ### `S₋` -/

/-- `S₋`: `R(b) - R(a) = 4 β(x)ᵀ A⁻¹ β(y) ≥ 0`, `U β(x)ᵀ A⁻¹ β(y) = z₃ (z₀z₁ + z₀z₅ + z₁z₂ +
z₁z₅ + z₂z₅)`. -/
theorem remainder_classSm_le {z : Fin 6 → ℝ} (hz : ∀ i, 0 ≤ z i) :
    remainder loopMatrixSm z ![1, 1, 1, 1, 0, 0] ≤
      remainder loopMatrixSm z ![-1, -1, -1, 1, 0, 0] := by
  have h := remainder_sub_sub_remainder_add loopMatrixSm z ![1, 1, 1, 0, 0, 0] ![0, 0, 0, 1, 0, 0]
  have ha : (fun i => (![1, 1, 1, 0, 0, 0] : Fin 6 → ℝ) i + (![0, 0, 0, 1, 0, 0] : Fin 6 → ℝ) i) =
      ![1, 1, 1, 1, 0, 0] := by
    funext i; fin_cases i <;> simp
  have hb : (fun i => (![0, 0, 0, 1, 0, 0] : Fin 6 → ℝ) i - (![1, 1, 1, 0, 0, 0] : Fin 6 → ℝ) i) =
      ![-1, -1, -1, 1, 0, 0] := by
    funext i; fin_cases i <;> simp
  rw [ha, hb, dotProduct_inv_symanzikMatrix_mulVec] at h
  simp [coefVec, symanzikMatrix, Fin.sum_univ_six, castLoopMatrix, class5LoopMatrix] at h
  have hpoly : 0 ≤ (symanzikU loopMatrixSm z)⁻¹ *
      (z 3 * (z 0 * z 1 + z 0 * z 5 + z 1 * z 2 + z 1 * z 5 + z 2 * z 5)) := by
    have := hz 0; have := hz 1; have := hz 2; have := hz 3; have := hz 4; have := hz 5
    have := symanzikU_nonneg loopMatrixSm hz
    positivity
  nlinarith [h, hpoly]

/-- `S₋`: `R(a) ≤ E (1 - E)² + z₄ E²`, from `y = (-E, 0)` (the current fraction `E` through the
photon `(v₀v₄)`). -/
theorem remainder_classSm_le_sum {z : Fin 6 → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hU : symanzikU loopMatrixSm z ≠ 0) :
    remainder loopMatrixSm z ![1, 1, 1, 1, 0, 0] ≤
      (z 0 + z 1 + z 2 + z 3) * (1 - (z 0 + z 1 + z 2 + z 3)) ^ 2 +
        z 4 * (z 0 + z 1 + z 2 + z 3) ^ 2 := by
  refine (remainder_le_sum_sq loopMatrixSm hz hU _ ![-(z 0 + z 1 + z 2 + z 3), 0]).trans
    (le_of_eq ?_)
  simp [Fin.sum_univ_six, castLoopMatrix, class5LoopMatrix]
  ring

/-- **No thresholds for `S₋`.** Hypotheses as for `S₊`: `V(z) ≥ m² E² + m_γ² (1 - E)`,
`E = z₀ + z₁ + z₂ + z₃`. -/
theorem le_symanzikV_classSm {mass mγ lam₁ lam₂ : ℝ} {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2) (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU loopMatrixSm z ≠ 0) :
    mass ^ 2 * (z 0 + z 1 + z 2 + z 3) ^ 2 + mγ ^ 2 * (z 4 + z 5) ≤
      symanzikV loopMatrixSm (classCmSmMomenta p p') (classLXMasses mass lam₁ lam₂) z := by
  rw [classCmSmMomenta_eq]
  refine le_symanzikV_of_routing hp hp' hq (le_sum_mul_classLXMasses_sq hlam₁ hlam₂ hz) ?_
    (remainder_classSm_le hz)
  have h := remainder_classSm_le_sum hz hU
  have h1 : z 0 + z 1 + z 2 + z 3 + z 4 + z 5 = 1 := by
    simpa [Fin.sum_univ_six] using hz1
  set E := z 0 + z 1 + z 2 + z 3
  have h4 : z 4 * E ^ 2 ≤ (1 - E) * E ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith [hz 5]) (sq_nonneg _)
  nlinarith

/-- **No thresholds for `S₋`, uniform constant:** `V(z) ≥ (3/4) min(m², m_γ²)`. -/
theorem symanzikV_classSm_ge {mass mγ lam₁ lam₂ : ℝ} {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2) (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU loopMatrixSm z ≠ 0) :
    3 / 4 * min (mass ^ 2) (mγ ^ 2) ≤
      symanzikV loopMatrixSm (classCmSmMomenta p p') (classLXMasses mass lam₁ lam₂) z := by
  refine le_trans ?_ (le_symanzikV_classSm hp hp' hq hlam₁ hlam₂ hz hz1 hU)
  have h1 : z 0 + z 1 + z 2 + z 3 + (z 4 + z 5) = 1 := by
    have := hz1; simp only [Fin.sum_univ_six] at this; linarith
  exact three_quarters_le (min_le_left _ _) (min_le_right _ _)
    (le_min (sq_nonneg _) (sq_nonneg _)) h1 (add_nonneg (hz 4) (hz 5))

theorem symanzikV_classSm_pos {mass mγ lam₁ lam₂ : ℝ} (hm : mass ≠ 0) (hmγ : mγ ≠ 0)
    {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2) (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU loopMatrixSm z ≠ 0) :
    0 < symanzikV loopMatrixSm (classCmSmMomenta p p') (classLXMasses mass lam₁ lam₂) z := by
  have h0 : 0 < min (mass ^ 2) (mγ ^ 2) := lt_min (by positivity) (by positivity)
  linarith [symanzikV_classSm_ge hp hp' hq hlam₁ hlam₂ hz hz1 hU]

/-! ### `VP` -/

/-- `VP`: `R(b) - R(a) = 4 β(x)ᵀ A⁻¹ β(y) ≥ 0`, `U β(x)ᵀ A⁻¹ β(y) = z₀ z₁ (z₂ + z₃)`. -/
theorem remainder_classVP_le {z : Fin 6 → ℝ} (hz : ∀ i, 0 ≤ z i) :
    remainder loopMatrixVP z ![1, 1, 0, 0, 0, 0] ≤
      remainder loopMatrixVP z ![-1, 1, 0, 0, 0, 0] := by
  have h := remainder_sub_sub_remainder_add loopMatrixVP z ![1, 0, 0, 0, 0, 0] ![0, 1, 0, 0, 0, 0]
  have ha : (fun i => (![1, 0, 0, 0, 0, 0] : Fin 6 → ℝ) i + (![0, 1, 0, 0, 0, 0] : Fin 6 → ℝ) i) =
      ![1, 1, 0, 0, 0, 0] := by
    funext i; fin_cases i <;> simp
  have hb : (fun i => (![0, 1, 0, 0, 0, 0] : Fin 6 → ℝ) i - (![1, 0, 0, 0, 0, 0] : Fin 6 → ℝ) i) =
      ![-1, 1, 0, 0, 0, 0] := by
    funext i; fin_cases i <;> simp
  rw [ha, hb, dotProduct_inv_symanzikMatrix_mulVec] at h
  simp [coefVec, symanzikMatrix, Fin.sum_univ_six, castLoopMatrix, class5LoopMatrix] at h
  have hpoly : 0 ≤ (symanzikU loopMatrixVP z)⁻¹ * (z 0 * z 1 * (z 2 + z 3)) := by
    have := hz 0; have := hz 1; have := hz 2; have := hz 3; have := hz 4; have := hz 5
    have := symanzikU_nonneg loopMatrixVP hz
    positivity
  nlinarith [h, hpoly]

/-- `VP`: `R(a) ≤ P (1 - P)² + (z₂ + z₄ + z₅) P²`, `P = z₀ + z₁`, from `y = (0, -P)` (the current
fraction `P` through the photon `(v₀v₃)`, the loop line `v₃v₄` and the photon `(v₂v₄)`). -/
theorem remainder_classVP_le_sum {z : Fin 6 → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hU : symanzikU loopMatrixVP z ≠ 0) :
    remainder loopMatrixVP z ![1, 1, 0, 0, 0, 0] ≤
      (z 0 + z 1) * (1 - (z 0 + z 1)) ^ 2 + (z 2 + z 4 + z 5) * (z 0 + z 1) ^ 2 := by
  refine (remainder_le_sum_sq loopMatrixVP hz hU _ ![0, -(z 0 + z 1)]).trans (le_of_eq ?_)
  simp [Fin.sum_univ_six, castLoopMatrix, class5LoopMatrix]
  ring

/-- **No thresholds for `VP`.** For the vacuum-polarization class `VP` with open-line mass `m`,
loop mass `M_f`, photon masses `λᵢ² ≥ m_γ²`, on-shell `p·p = p'·p' = -m²` and `q = p' - p` with
`q·q ≥ 0`, at every point of the simplex with `U(z) ≠ 0`:
`V(z) ≥ m² (z₀ + z₁)² + M_f² (z₂ + z₃) + m_γ² (z₄ + z₅)`. -/
theorem le_symanzikV_classVP {mass massF mγ lam₁ lam₂ : ℝ} {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2) (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU loopMatrixVP z ≠ 0) :
    mass ^ 2 * (z 0 + z 1) ^ 2 + (massF ^ 2 * (z 2 + z 3) + mγ ^ 2 * (z 4 + z 5)) ≤
      symanzikV loopMatrixVP (classVPMomenta p p') (classVPMasses mass massF lam₁ lam₂) z := by
  rw [classVPMomenta_eq]
  refine le_symanzikV_of_routing (E := z 0 + z 1) hp hp' hq ?_ ?_ (remainder_classVP_le hz)
  · rw [sum_mul_classVPMasses_sq]
    have h3 : mγ ^ 2 * z 4 ≤ lam₁ ^ 2 * z 4 := mul_le_mul_of_nonneg_right hlam₁ (hz 4)
    have h4 : mγ ^ 2 * z 5 ≤ lam₂ ^ 2 * z 5 := mul_le_mul_of_nonneg_right hlam₂ (hz 5)
    linarith
  · have h := remainder_classVP_le_sum hz hU
    have h1 : z 0 + z 1 + z 2 + z 3 + z 4 + z 5 = 1 := by
      simpa [Fin.sum_univ_six] using hz1
    have h4 : (z 2 + z 4 + z 5) * (z 0 + z 1) ^ 2 ≤ (1 - (z 0 + z 1)) * (z 0 + z 1) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith [hz 3]) (sq_nonneg _)
    nlinarith

/-- **No thresholds for `VP`, uniform constant:** if `M_f² ≥ m²`,
`V(z) ≥ (3/4) min(m², m_γ²)`. -/
theorem symanzikV_classVP_ge {mass massF mγ lam₁ lam₂ : ℝ} (hF : mass ^ 2 ≤ massF ^ 2)
    {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2) (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU loopMatrixVP z ≠ 0) :
    3 / 4 * min (mass ^ 2) (mγ ^ 2) ≤
      symanzikV loopMatrixVP (classVPMomenta p p') (classVPMasses mass massF lam₁ lam₂) z := by
  refine le_trans ?_ (le_symanzikV_classVP hp hp' hq hlam₁ hlam₂ hz hz1 hU)
  have h1 : z 0 + z 1 + (z 2 + z 3 + z 4 + z 5) = 1 := by
    have := hz1; simp only [Fin.sum_univ_six] at this; linarith
  set c := min (mass ^ 2) (mγ ^ 2)
  have hc0 : 0 ≤ c := le_min (sq_nonneg _) (sq_nonneg _)
  have h := three_quarters_le_of (k := mass ^ 2) (μ := c) (min_le_left _ _) le_rfl hc0 h1
    (by linarith [hz 2, hz 3, hz 4, hz 5])
  have h2 : c * (z 2 + z 3) ≤ massF ^ 2 * (z 2 + z 3) :=
    mul_le_mul_of_nonneg_right ((min_le_left _ _).trans hF) (by linarith [hz 2, hz 3])
  have h3 : c * (z 4 + z 5) ≤ mγ ^ 2 * (z 4 + z 5) :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith [hz 4, hz 5])
  nlinarith

theorem symanzikV_classVP_pos {mass massF mγ lam₁ lam₂ : ℝ} (hm : mass ≠ 0) (hmγ : mγ ≠ 0)
    (hF : mass ^ 2 ≤ massF ^ 2) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2) (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU loopMatrixVP z ≠ 0) :
    0 < symanzikV loopMatrixVP (classVPMomenta p p') (classVPMasses mass massF lam₁ lam₂) z := by
  have h0 : 0 < min (mass ^ 2) (mγ ^ 2) := lt_min (by positivity) (by positivity)
  linarith [symanzikV_classVP_ge hF hp hp' hq hlam₁ hlam₂ hz hz1 hU]

/-! ### Repeated lines -/

section Repeat

variable {n k : ℕ}

/-- The weights merged along a map of lines `σ`: `wⱼ = ∑_{σ i = j} zᵢ`. -/
def mergeWeights (σ : Fin (k + 1) → Fin (n + 1)) (z : Fin (k + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun j => ∑ i ∈ univ.filter (fun i => σ i = j), z i

theorem sum_mul_comp_eq (σ : Fin (k + 1) → Fin (n + 1)) (z : Fin (k + 1) → ℝ)
    (f : Fin (n + 1) → ℝ) : ∑ i, z i * f (σ i) = ∑ j, mergeWeights σ z j * f j := by
  rw [← Finset.sum_fiberwise univ σ (fun i => z i * f (σ i))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mergeWeights, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.mp hi).2]

theorem sum_mergeWeights (σ : Fin (k + 1) → Fin (n + 1)) (z : Fin (k + 1) → ℝ) :
    ∑ j, mergeWeights σ z j = ∑ i, z i := by
  simpa using (sum_mul_comp_eq σ z fun _ => 1).symm

theorem mergeWeights_nonneg (σ : Fin (k + 1) → Fin (n + 1)) {z : Fin (k + 1) → ℝ}
    (hz : ∀ i, 0 ≤ z i) (j : Fin (n + 1)) : 0 ≤ mergeWeights σ z j :=
  Finset.sum_nonneg fun i _ => hz i

theorem symanzikMatrix_comp (σ : Fin (k + 1) → Fin (n + 1)) (α : Fin (n + 1) → Fin 2 → ℝ)
    (z : Fin (k + 1) → ℝ) :
    symanzikMatrix (fun i => α (σ i)) z = symanzikMatrix α (mergeWeights σ z) := by
  ext s t
  simp only [symanzikMatrix, of_apply, mul_assoc]
  exact sum_mul_comp_eq σ z fun j => α j s * α j t

theorem symanzikU_comp (σ : Fin (k + 1) → Fin (n + 1)) (α : Fin (n + 1) → Fin 2 → ℝ)
    (z : Fin (k + 1) → ℝ) :
    symanzikU (fun i => α (σ i)) z = symanzikU α (mergeWeights σ z) := by
  rw [symanzikU, symanzikMatrix_comp, symanzikU]

theorem symanzikVector_comp (σ : Fin (k + 1) → Fin (n + 1)) (α : Fin (n + 1) → Fin 2 → ℝ)
    (p : Fin (n + 1) → Fin 4 → ℝ) (z : Fin (k + 1) → ℝ) :
    symanzikVector (fun i => α (σ i)) (fun i => p (σ i)) z =
      symanzikVector α p (mergeWeights σ z) := by
  funext s μ
  simp only [symanzikVector, mul_assoc]
  exact sum_mul_comp_eq σ z fun j => α j s * p j μ

/-- **Repeated lines.** Repeating line `σ i` as line `i` (same loop row, same momentum, mass
`M'ᵢ`): `V` is `V` of the original graph at the merged weights, plus `∑ᵢ zᵢ (M'ᵢ² - M_{σ i}²)`.
Pure algebra. -/
theorem symanzikV_comp (σ : Fin (k + 1) → Fin (n + 1)) (α : Fin (n + 1) → Fin 2 → ℝ)
    (p : Fin (n + 1) → Fin 4 → ℝ) (M' : Fin (k + 1) → ℝ) (M : Fin (n + 1) → ℝ)
    (z : Fin (k + 1) → ℝ) :
    symanzikV (fun i => α (σ i)) (fun i => p (σ i)) M' z =
      symanzikV α p M (mergeWeights σ z) + ∑ i, z i * (M' i ^ 2 - M (σ i) ^ 2) := by
  have h : ∑ i, z i * (M' i ^ 2 + Minkowski.dot (p (σ i)) (p (σ i))) =
      ∑ j, mergeWeights σ z j * (M j ^ 2 + Minkowski.dot (p j) (p j)) +
        ∑ i, z i * (M' i ^ 2 - M (σ i) ^ 2) := by
    rw [← sum_mul_comp_eq σ z (fun j => M j ^ 2 + Minkowski.dot (p j) (p j)),
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [symanzikV, symanzikV, h, symanzikMatrix_comp, symanzikVector_comp]
  ring

/-- **Repeated lines preserve lower bounds.** If every repeated line has mass at least that of its
original (`M_{σ i}² ≤ M'ᵢ²`), a lower bound valid on the simplex where `U ≠ 0` for the original
graph holds for the repeated graph. -/
theorem le_symanzikV_comp_of {σ : Fin (k + 1) → Fin (n + 1)} {α : Fin (n + 1) → Fin 2 → ℝ}
    {p : Fin (n + 1) → Fin 4 → ℝ} {M : Fin (n + 1) → ℝ} {M' : Fin (k + 1) → ℝ} {c : ℝ}
    (hbase : ∀ w : Fin (n + 1) → ℝ, (∀ i, 0 ≤ w i) → ∑ i, w i = 1 → symanzikU α w ≠ 0 →
      c ≤ symanzikV α p M w)
    (hM : ∀ i, M (σ i) ^ 2 ≤ M' i ^ 2) {z : Fin (k + 1) → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hz1 : ∑ i, z i = 1) (hU : symanzikU (fun i => α (σ i)) z ≠ 0) :
    c ≤ symanzikV (fun i => α (σ i)) (fun i => p (σ i)) M' z := by
  rw [symanzikV_comp σ α p M' M]
  have h1 := hbase (mergeWeights σ z) (mergeWeights_nonneg σ hz)
    ((sum_mergeWeights σ z).trans hz1) (by rwa [← symanzikU_comp])
  have h2 : 0 ≤ ∑ i, z i * (M' i ^ 2 - M (σ i) ^ 2) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hz i) (sub_nonneg.mpr (hM i))
  linarith

end Repeat

/-! ### The Pauli–Villars forms and the doubled bubble -/

/-- The line map of `class5LoopMatrixPV`: lines `6`, `7` repeat the photons `4`, `5`. -/
def pvLines : Fin 8 → Fin 6 := ![0, 1, 2, 3, 4, 5, 4, 5]

/-- The line map of `loopMatrixVPBubble`: lines `6, 7, 8, 9` repeat `4, 5, 2, 3`. -/
def vpBubbleLines : Fin 10 → Fin 6 := ![0, 1, 2, 3, 4, 5, 4, 5, 2, 3]

theorem castLoopMatrix_class5LoopMatrixPV (c : QED.TwoLoop.Enumeration.Class5) :
    castLoopMatrix (class5LoopMatrixPV c) =
      fun i => castLoopMatrix (class5LoopMatrix c) (pvLines i) :=
  rfl

theorem castLoopMatrix_loopMatrixVPBubble :
    castLoopMatrix loopMatrixVPBubble = fun i => loopMatrixVP (vpBubbleLines i) :=
  rfl

/-- The masses of the Pauli–Villars form of an open-line class: electrons `m`, photons
`λ₁, λ₂, λ₃, λ₄` (lines `4, 5, 6, 7`). -/
def classPVMasses (mass lam₁ lam₂ lam₃ lam₄ : ℝ) : Fin 8 → ℝ :=
  ![mass, mass, mass, mass, lam₁, lam₂, lam₃, lam₄]

/-- The masses of the Pauli–Villars form of `VP`: open line `m`, loop `M_f`, photons
`λ₁, λ₂, λ₃, λ₄`. -/
def classVPPVMasses (mass massF lam₁ lam₂ lam₃ lam₄ : ℝ) : Fin 8 → ℝ :=
  ![mass, mass, massF, massF, lam₁, lam₂, lam₃, lam₄]

/-- The masses of the doubled-bubble form of `VP`: open line `m`, loop lines `M₁, M₂, M₃, M₄`
(lines `2, 3, 8, 9`), photons `λ₁, λ₂, λ₃, λ₄` (lines `4, 5, 6, 7`). -/
def classVPBubbleMasses (mass M₁ M₂ M₃ M₄ lam₁ lam₂ lam₃ lam₄ : ℝ) : Fin 10 → ℝ :=
  ![mass, mass, M₁, M₂, lam₁, lam₂, lam₃, lam₄, M₃, M₄]

theorem classLXMasses_pvLines_le {mass mγ lam₁ lam₂ lam₃ lam₄ : ℝ}
    (h₁ : mγ ^ 2 ≤ lam₁ ^ 2) (h₂ : mγ ^ 2 ≤ lam₂ ^ 2) (h₃ : mγ ^ 2 ≤ lam₃ ^ 2)
    (h₄ : mγ ^ 2 ≤ lam₄ ^ 2) (i : Fin 8) :
    classLXMasses mass mγ mγ (pvLines i) ^ 2 ≤ classPVMasses mass lam₁ lam₂ lam₃ lam₄ i ^ 2 := by
  fin_cases i <;> simp [classLXMasses, pvLines, classPVMasses, h₁, h₂, h₃, h₄]

/-- The Pauli–Villars form of `L` (photon lines doubled, all four photon masses `λᵢ² ≥ m_γ²`,
`z` on the simplex in `8` variables with `U ≠ 0`): `V ≥ (3/4) min(m², m_γ²)`, transferred from
`symanzikV_classL_ge` by `le_symanzikV_comp_of`. The theorems for `X`, `C±`, `S±` below are the
same with the constant of the class. -/
theorem symanzikV_classLPV_ge {mass mγ lam₁ lam₂ lam₃ lam₄ : ℝ} {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (h₁ : mγ ^ 2 ≤ lam₁ ^ 2) (h₂ : mγ ^ 2 ≤ lam₂ ^ 2) (h₃ : mγ ^ 2 ≤ lam₃ ^ 2)
    (h₄ : mγ ^ 2 ≤ lam₄ ^ 2) {z : Fin 8 → ℝ} (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1)
    (hU : symanzikU (castLoopMatrix (class5LoopMatrixPV .L)) z ≠ 0) :
    3 / 4 * min (mass ^ 2) (mγ ^ 2) ≤
      symanzikV (castLoopMatrix (class5LoopMatrixPV .L))
        (fun i => classLXMomenta p p' (pvLines i)) (classPVMasses mass lam₁ lam₂ lam₃ lam₄) z :=
  le_symanzikV_comp_of (fun _ hw hw1 hU' => symanzikV_classL_ge hp hp' hq le_rfl le_rfl hw hw1 hU')
    (classLXMasses_pvLines_le h₁ h₂ h₃ h₄) hz hz1 hU

theorem symanzikV_classXPV_ge {mass mγ lam₁ lam₂ lam₃ lam₄ : ℝ} {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (h₁ : mγ ^ 2 ≤ lam₁ ^ 2) (h₂ : mγ ^ 2 ≤ lam₂ ^ 2) (h₃ : mγ ^ 2 ≤ lam₃ ^ 2)
    (h₄ : mγ ^ 2 ≤ lam₄ ^ 2) {z : Fin 8 → ℝ} (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1)
    (hU : symanzikU (castLoopMatrix (class5LoopMatrixPV .X)) z ≠ 0) :
    3 / 4 * min (mass ^ 2 / 4) (mγ ^ 2) ≤
      symanzikV (castLoopMatrix (class5LoopMatrixPV .X))
        (fun i => classLXMomenta p p' (pvLines i)) (classPVMasses mass lam₁ lam₂ lam₃ lam₄) z :=
  le_symanzikV_comp_of (fun _ hw hw1 hU' => symanzikV_classX_ge hp hp' hq le_rfl le_rfl hw hw1 hU')
    (classLXMasses_pvLines_le h₁ h₂ h₃ h₄) hz hz1 hU

theorem symanzikV_classCpPV_ge {mass mγ lam₁ lam₂ lam₃ lam₄ : ℝ} {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (h₁ : mγ ^ 2 ≤ lam₁ ^ 2) (h₂ : mγ ^ 2 ≤ lam₂ ^ 2) (h₃ : mγ ^ 2 ≤ lam₃ ^ 2)
    (h₄ : mγ ^ 2 ≤ lam₄ ^ 2) {z : Fin 8 → ℝ} (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1)
    (hU : symanzikU (castLoopMatrix (class5LoopMatrixPV .Cp)) z ≠ 0) :
    3 / 4 * min (mass ^ 2 / 4) (mγ ^ 2) ≤
      symanzikV (castLoopMatrix (class5LoopMatrixPV .Cp))
        (fun i => classCpSpMomenta p p' (pvLines i)) (classPVMasses mass lam₁ lam₂ lam₃ lam₄) z :=
  le_symanzikV_comp_of
    (fun _ hw hw1 hU' => symanzikV_classCp_ge hp hp' hq le_rfl le_rfl hw hw1 hU')
    (classLXMasses_pvLines_le h₁ h₂ h₃ h₄) hz hz1 hU

theorem symanzikV_classCmPV_ge {mass mγ lam₁ lam₂ lam₃ lam₄ : ℝ} {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (h₁ : mγ ^ 2 ≤ lam₁ ^ 2) (h₂ : mγ ^ 2 ≤ lam₂ ^ 2) (h₃ : mγ ^ 2 ≤ lam₃ ^ 2)
    (h₄ : mγ ^ 2 ≤ lam₄ ^ 2) {z : Fin 8 → ℝ} (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1)
    (hU : symanzikU (castLoopMatrix (class5LoopMatrixPV .Cm)) z ≠ 0) :
    3 / 4 * min (mass ^ 2 / 4) (mγ ^ 2) ≤
      symanzikV (castLoopMatrix (class5LoopMatrixPV .Cm))
        (fun i => classCmSmMomenta p p' (pvLines i)) (classPVMasses mass lam₁ lam₂ lam₃ lam₄) z :=
  le_symanzikV_comp_of
    (fun _ hw hw1 hU' => symanzikV_classCm_ge hp hp' hq le_rfl le_rfl hw hw1 hU')
    (classLXMasses_pvLines_le h₁ h₂ h₃ h₄) hz hz1 hU

theorem symanzikV_classSpPV_ge {mass mγ lam₁ lam₂ lam₃ lam₄ : ℝ} {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (h₁ : mγ ^ 2 ≤ lam₁ ^ 2) (h₂ : mγ ^ 2 ≤ lam₂ ^ 2) (h₃ : mγ ^ 2 ≤ lam₃ ^ 2)
    (h₄ : mγ ^ 2 ≤ lam₄ ^ 2) {z : Fin 8 → ℝ} (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1)
    (hU : symanzikU (castLoopMatrix (class5LoopMatrixPV .Sp)) z ≠ 0) :
    3 / 4 * min (mass ^ 2) (mγ ^ 2) ≤
      symanzikV (castLoopMatrix (class5LoopMatrixPV .Sp))
        (fun i => classCpSpMomenta p p' (pvLines i)) (classPVMasses mass lam₁ lam₂ lam₃ lam₄) z :=
  le_symanzikV_comp_of
    (fun _ hw hw1 hU' => symanzikV_classSp_ge hp hp' hq le_rfl le_rfl hw hw1 hU')
    (classLXMasses_pvLines_le h₁ h₂ h₃ h₄) hz hz1 hU

theorem symanzikV_classSmPV_ge {mass mγ lam₁ lam₂ lam₃ lam₄ : ℝ} {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (h₁ : mγ ^ 2 ≤ lam₁ ^ 2) (h₂ : mγ ^ 2 ≤ lam₂ ^ 2) (h₃ : mγ ^ 2 ≤ lam₃ ^ 2)
    (h₄ : mγ ^ 2 ≤ lam₄ ^ 2) {z : Fin 8 → ℝ} (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1)
    (hU : symanzikU (castLoopMatrix (class5LoopMatrixPV .Sm)) z ≠ 0) :
    3 / 4 * min (mass ^ 2) (mγ ^ 2) ≤
      symanzikV (castLoopMatrix (class5LoopMatrixPV .Sm))
        (fun i => classCmSmMomenta p p' (pvLines i)) (classPVMasses mass lam₁ lam₂ lam₃ lam₄) z :=
  le_symanzikV_comp_of
    (fun _ hw hw1 hU' => symanzikV_classSm_ge hp hp' hq le_rfl le_rfl hw hw1 hU')
    (classLXMasses_pvLines_le h₁ h₂ h₃ h₄) hz hz1 hU

/-- The Pauli–Villars form of `VP` (photons doubled), loop mass `M_f² ≥ m²`:
`V ≥ (3/4) min(m², m_γ²)`. -/
theorem symanzikV_classVPPV_ge {mass massF mγ lam₁ lam₂ lam₃ lam₄ : ℝ}
    (hF : mass ^ 2 ≤ massF ^ 2) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (h₁ : mγ ^ 2 ≤ lam₁ ^ 2) (h₂ : mγ ^ 2 ≤ lam₂ ^ 2) (h₃ : mγ ^ 2 ≤ lam₃ ^ 2)
    (h₄ : mγ ^ 2 ≤ lam₄ ^ 2) {z : Fin 8 → ℝ} (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1)
    (hU : symanzikU (castLoopMatrix (class5LoopMatrixPV .VP)) z ≠ 0) :
    3 / 4 * min (mass ^ 2) (mγ ^ 2) ≤
      symanzikV (castLoopMatrix (class5LoopMatrixPV .VP))
        (fun i => classVPMomenta p p' (pvLines i))
        (classVPPVMasses mass massF lam₁ lam₂ lam₃ lam₄) z := by
  refine le_symanzikV_comp_of (M := classVPMasses mass massF mγ mγ)
    (fun _ hw hw1 hU' => symanzikV_classVP_ge hF hp hp' hq le_rfl le_rfl hw hw1 hU') ?_ hz hz1 hU
  intro i
  fin_cases i <;> simp [classVPMasses, classVPPVMasses, h₁, h₂, h₃, h₄]

/-- The doubled-bubble form of `VP` (`loopMatrixVPBubble`: photons and bubble lines doubled),
loop masses `Mᵢ² ≥ m²`, photon masses `λᵢ² ≥ m_γ²`: `V ≥ (3/4) min(m², m_γ²)`. -/
theorem symanzikV_VPBubble_ge {mass mγ M₁ M₂ M₃ M₄ lam₁ lam₂ lam₃ lam₄ : ℝ}
    (hM₁ : mass ^ 2 ≤ M₁ ^ 2) (hM₂ : mass ^ 2 ≤ M₂ ^ 2) (hM₃ : mass ^ 2 ≤ M₃ ^ 2)
    (hM₄ : mass ^ 2 ≤ M₄ ^ 2) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (h₁ : mγ ^ 2 ≤ lam₁ ^ 2) (h₂ : mγ ^ 2 ≤ lam₂ ^ 2) (h₃ : mγ ^ 2 ≤ lam₃ ^ 2)
    (h₄ : mγ ^ 2 ≤ lam₄ ^ 2) {z : Fin 10 → ℝ} (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1)
    (hU : symanzikU (castLoopMatrix loopMatrixVPBubble) z ≠ 0) :
    3 / 4 * min (mass ^ 2) (mγ ^ 2) ≤
      symanzikV (castLoopMatrix loopMatrixVPBubble)
        (fun i => classVPMomenta p p' (vpBubbleLines i))
        (classVPBubbleMasses mass M₁ M₂ M₃ M₄ lam₁ lam₂ lam₃ lam₄) z := by
  refine le_symanzikV_comp_of (M := classVPMasses mass mass mγ mγ)
    (fun _ hw hw1 hU' => symanzikV_classVP_ge le_rfl hp hp' hq le_rfl le_rfl hw hw1 hU') ?_
    hz hz1 hU
  intro i
  fin_cases i <;> simp [classVPMasses, classVPBubbleMasses, h₁, h₂, h₃, h₄,
    hM₁, hM₂, hM₃, hM₄]

end QED.Integration.TwoLoop

end
