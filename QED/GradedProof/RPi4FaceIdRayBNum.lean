/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdRayBRay

/-!
# (R-Π₄) step L10, T2.UV: normalized numerator families along the ray

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (the rate input
(B) of `QED.GradedProof.RPi4.faceIdRay_of_size_rate`). The rate of one merged piece along the ray
`k'(s) = √s (1, 0, 1, 1)`, `QED.GradedProof.RPi4.faceIdRayB_vpPiece`, asks for representatives
`Q(s)` of the normalized numerators `ℓ ↦ s^{-D/2} N(k'(s))(√s ℓ)` with coefficients bounded
uniformly in `s ≥ 1`. They are built from finitely many node quartics:

* `Qr(r) = jointQuartic (2d) d Qk (upar r)` represents `N(r v̂)` (nodes along `lineK 0 v̂`);
  its weights grow at most like `r^d` (`faceIdRayB_norm_lam_le`, from
  `1 / (1 - u²) ≤ 1 + |tpar u|`);
* `Q̃(s) = dilateQ (√s^{-D}) √s (Qr √s)` with `D = d + 4` has bounded coefficients
  (`faceIdRayB_lqBdd_dilate`): the degree-`j` coefficient is `√s^{j - D}` times one of size
  `√s^d`;
* **`faceIdRayB_numFamily`**: the family, with its value, degree bound and quartic part;
* **`faceIdRayB_vpPiece_of_nodes`**: `faceIdRayB_vpPiece` with the numerator hypotheses of
  `QED.GradedProof.RPi4.heavyRate_vpPiece` (polynomial in `k`, representatives at every `k`).
-/

@[expose] public section

open Complex Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZeroLimit QED.TwoLoop.MassScaling
open QED.TwoLoop.Bridge (IsLoopPoly)

/-! ### Dilated quartics -/

theorem faceIdRayB_loopDegLe_dilateQ (a b : ℂ) {t : Fin 2} {d : ℕ} {Q : LoopQuartic}
    (h : LoopDegLe t d Q) : LoopDegLe t d (dilateQ a b Q) where
  lin i hi := by simp [dilateQ, h.lin i hi]
  quad i j hi := by simp [dilateQ, h.quad i j hi]
  cub i j k hi := by simp [dilateQ, h.cub i j k hi]
  quart i j k l hi := by simp [dilateQ, h.quart i j k l hi]

theorem faceIdRayB_quart_dilateQ (a b : ℂ) {Q : LoopQuartic} (h : Q.quart = 0) :
    (dilateQ a b Q).quart = 0 := by
  funext i j k l
  simp [dilateQ, h]

/-- The value of `dilateQ (r^D) r⁻¹` of a quartic representing `r^{-D} G(r ·)`. -/
theorem faceIdRayB_eval_dilateQ_inv {r : ℝ} (hr : 0 < r) (D : ℕ) {Q : LoopQuartic}
    {G : (Fin 2 → Fin 4 → ℝ) → ℂ} (hQ : Q.eval = fun ℓ => ((r : ℂ) ^ D)⁻¹ * G (r • ℓ)) :
    (dilateQ ((r : ℂ) ^ D) ((r⁻¹ : ℝ) : ℂ) Q).eval = G := by
  funext ℓ
  have hr0 : (r : ℂ) ^ D ≠ 0 := pow_ne_zero _ (ofReal_ne_zero.2 hr.ne')
  rw [eval_dilateQ, hQ]
  dsimp only
  rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, ← mul_assoc, mul_inv_cancel₀ hr0, one_mul]

/-! ### The interpolation weights along the ray -/

theorem faceIdRayB_inv_wt_le {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    (1 - u ^ 2)⁻¹ ≤ 1 + |tpar u| := by
  have h0 : 0 < 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
  have habs : |u| < 1 := abs_lt.2 hu
  have hsq : u ^ 2 ≤ |u| := by
    rw [← sq_abs]; nlinarith [abs_nonneg u]
  rw [tpar, abs_div, abs_of_pos h0, inv_eq_one_div, div_le_iff₀ h0, add_mul,
    div_mul_cancel₀ _ h0.ne']
  nlinarith

/-- **The interpolation weights at `upar r` grow at most like `r^n`** (`r ≥ 1`). -/
theorem faceIdRayB_norm_lam_le (D n : ℕ) :
    ∃ Λ : ℝ, ∀ r : ℝ, 1 ≤ r → ∀ k, ‖lam D n (upar r) k‖ ≤ Λ * r ^ n := by
  have hB : ∀ k : Fin (D + 1), ∃ B, ∀ u ∈ Icc (-1 : ℝ) 1,
      ‖(lbasis D k).eval (u : ℂ)‖ ≤ B := fun k =>
    isCompact_Icc.exists_bound_of_continuousOn
      ((Polynomial.continuous _).comp continuous_ofReal).continuousOn
  choose B hB using hB
  refine ⟨2 ^ n * ∑ k, ‖wt (node D k) ^ n‖ * |B k|, fun r hr k => ?_⟩
  set u := upar r
  have hu : u ∈ Ioo (-1 : ℝ) 1 := upar_mem r
  have hu' : u ∈ Icc (-1 : ℝ) 1 := Ioo_subset_Icc_self hu
  have h0 : 0 < 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
  have hwt : wt u = ((1 - u ^ 2 : ℝ) : ℂ) := by simp [wt]
  have hinv : ‖(wt u ^ n)⁻¹‖ ≤ 2 ^ n * r ^ n := by
    rw [norm_inv, norm_pow, ← inv_pow, hwt, Complex.norm_real, Real.norm_of_nonneg h0.le,
      ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ n
    have h := faceIdRayB_inv_wt_le hu
    rw [show tpar u = r from tpar_upar r, abs_of_nonneg (by linarith)] at h
    linarith
  have hsum : ‖wt (node D k) ^ n‖ * |B k| ≤ ∑ k, ‖wt (node D k) ^ n‖ * |B k| :=
    Finset.single_le_sum (f := fun k : Fin (D + 1) => ‖wt (node D k) ^ n‖ * |B k|)
      (fun k _ => by positivity) (Finset.mem_univ k)
  simp only [lam, norm_mul]
  calc ‖(wt u ^ n)⁻¹‖ * (‖wt (node D k) ^ n‖ * ‖(lbasis D k).eval (u : ℂ)‖)
      ≤ (2 ^ n * r ^ n) * (‖wt (node D k) ^ n‖ * |B k|) :=
        mul_le_mul hinv (mul_le_mul_of_nonneg_left ((hB k u hu').trans (le_abs_self _))
          (norm_nonneg _)) (by positivity) (by positivity)
    _ ≤ (2 ^ n * r ^ n) * ∑ k, ‖wt (node D k) ^ n‖ * |B k| :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-! ### Bounded dilated families -/

theorem faceIdRayB_norm_dilate_le {r : ℝ} (hr : 1 ≤ r) {d j : ℕ} (hj : j ≤ 4) {x : ℂ} {B : ℝ}
    (hx : ‖x‖ ≤ B * r ^ d) : ‖((r : ℂ) ^ (d + 4))⁻¹ * (r : ℂ) ^ j * x‖ ≤ B := by
  have hr0 : 0 < r := one_pos.trans_le hr
  have hB : 0 ≤ B := by
    have := (norm_nonneg x).trans hx
    exact nonneg_of_mul_nonneg_left this (pow_pos hr0 d)
  rw [norm_mul, norm_mul, norm_inv, norm_pow, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hr0.le]
  have hpow : r ^ j * r ^ d ≤ r ^ (d + 4) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hr (by omega)
  have hD : 0 < r ^ (d + 4) := pow_pos hr0 _
  rw [mul_assoc, inv_mul_le_iff₀ hD]
  calc r ^ j * ‖x‖ ≤ r ^ j * (B * r ^ d) := mul_le_mul_of_nonneg_left hx (by positivity)
    _ = B * (r ^ j * r ^ d) := by ring
    _ ≤ B * r ^ (d + 4) := mul_le_mul_of_nonneg_left hpow hB
    _ = r ^ (d + 4) * B := by ring

theorem faceIdRayB_norm_sum_le {κ : Type*} [Fintype κ] {c x : κ → ℂ} {Λ B r : ℝ} {d : ℕ}
    (hc : ∀ k, ‖c k‖ ≤ Λ * r ^ d) (hx : ∀ k, ‖x k‖ ≤ B) :
    ‖∑ k, c k * x k‖ ≤ Fintype.card κ * (Λ * B) * r ^ d :=
  (norm_sum_mul_le hc hx).trans (le_of_eq (by ring))

/-- **Dilated combinations with weights of growth `r^d` are bounded.** -/
theorem faceIdRayB_lqBdd_dilate {κ : Type*} [Fintype κ] {Qk : κ → LoopQuartic} {BQ : ℝ}
    (hQ : LQBdd Qk BQ) {ι : Type*} (r : ι → ℝ) (hr : ∀ i, 1 ≤ r i) (c : ι → κ → ℂ) {Λ : ℝ}
    (d : ℕ) (hc : ∀ i k, ‖c i k‖ ≤ Λ * r i ^ d) :
    LQBdd (fun i => dilateQ (((r i : ℂ) ^ (d + 4))⁻¹) (r i) (qsum Finset.univ (c i) Qk))
      (Fintype.card κ * (Λ * BQ)) where
  const i := by
    have h := faceIdRayB_norm_dilate_le (hr i) (j := 0) (by norm_num)
      (faceIdRayB_norm_sum_le (hc i) fun k => hQ.const k)
    simpa [dilateQ, qsum] using h
  lin i a := by
    have h := faceIdRayB_norm_dilate_le (hr i) (j := 1) (by norm_num)
      (faceIdRayB_norm_sum_le (hc i) fun k => hQ.lin k a)
    simpa [dilateQ, qsum] using h
  quad i a b := faceIdRayB_norm_dilate_le (hr i) (j := 2) (by norm_num)
      (faceIdRayB_norm_sum_le (hc i) fun k => hQ.quad k a b)
  cub i a b e := faceIdRayB_norm_dilate_le (hr i) (j := 3) (by norm_num)
      (faceIdRayB_norm_sum_le (hc i) fun k => hQ.cub k a b e)
  quart i a b e f := faceIdRayB_norm_dilate_le (hr i) (j := 4) (by norm_num)
      (faceIdRayB_norm_sum_le (hc i) fun k => hQ.quart k a b e f)

/-! ### The numerator family -/

theorem faceIdRayB_lineK_upar (r : ℝ) : lineK 0 faceIdRayB_vhat (upar r) = r • faceIdRayB_vhat := by
  simp [lineK, tpar_upar]

/-- **The normalized numerator family along the ray.** If `N` is polynomial of degree `d` in `k`
and has, at every `k`, a representative of degree `≤ d'` along loop `t` (without quartic part
unless `p`), there is a family `Q(s)`, `s ≥ 1`, with uniformly bounded coefficients,
`Q(s)(ℓ) = s^{-D/2} N(k'(s))(√s ℓ)`, `D = d + 4`, of degree `≤ d'` along loop `t`. -/
theorem faceIdRayB_numFamily (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) {d : ℕ}
    (hk : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ) {t : Fin 2} {d' : ℕ} {p : Prop}
    (hQ : ∀ k, ∃ Q : LoopQuartic, Q.eval = N k ∧ LoopDegLe t d' Q ∧ (p ∨ Q.quart = 0)) :
    ∃ (Q : {s : ℝ // 1 ≤ s} → LoopQuartic) (B : ℝ), LQBdd Q B ∧
      (∀ s : {s : ℝ // 1 ≤ s}, (Q s).eval = fun ℓ => ((Real.sqrt s.1 : ℂ) ^ (d + 4))⁻¹ *
        N (tiltVec (Real.sqrt s.1) s.1) (Real.sqrt s.1 • ℓ)) ∧
      (∀ s, LoopDegLe t d' (Q s)) ∧ (p ∨ ∀ s, (Q s).quart = 0) := by
  classical
  set F : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ := fun u ℓ => N (lineK 0 faceIdRayB_vhat u) ℓ with hF_def
  have hF : IsUPoly (2 * d) fun ℓ u => wt u ^ d * F u ℓ := fun ℓ => by
    have h := isUPoly_eval_of_isLoopPoly (hk ℓ) (ι := Unit)
      (ℓ := fun _ u _ => lineK 0 faceIdRayB_vhat u) fun _ ν => by
        simpa using isUPoly_lineK (ι := Unit) 1 0 faceIdRayB_vhat ν
    exact h ()
  choose Qf hQfe hQfd hQfq using hQ
  set Qk : Fin (2 * d + 1) → LoopQuartic := fun j =>
    Qf (lineK 0 faceIdRayB_vhat (node (2 * d) j)) with hQk
  obtain ⟨BQ, hBQ⟩ := lqBdd_finite Qk
  obtain ⟨Λ, hΛ⟩ := faceIdRayB_norm_lam_le (2 * d) d
  set r : {s : ℝ // 1 ≤ s} → ℝ := fun s => Real.sqrt s.1 with hr_def
  have hr : ∀ s, 1 ≤ r s := fun s => by
    simp only [hr_def]; rw [Real.one_le_sqrt]; exact s.2
  refine ⟨fun s => dilateQ (((r s : ℂ) ^ (d + 4))⁻¹) (r s)
      (qsum Finset.univ (lam (2 * d) d (upar (r s))) Qk), _,
    faceIdRayB_lqBdd_dilate hBQ r hr (fun s => lam (2 * d) d (upar (r s))) d
      fun s k => hΛ (r s) (hr s) k, fun s => ?_, fun s => ?_, ?_⟩
  · have he : (jointQuartic (2 * d) d Qk (upar (r s))).eval = F (upar (r s)) :=
      eval_jointQuartic hF (fun j => hQfe _) (upar_mem _)
    funext ℓ
    rw [eval_dilateQ]
    change ((r s : ℂ) ^ (d + 4))⁻¹ * (jointQuartic (2 * d) d Qk (upar (r s))).eval _ = _
    rw [he, hF_def]
    dsimp only
    rw [faceIdRayB_lineK_upar, faceIdRayB_tiltVec_eq (zero_le_one.trans s.2)]
  · exact faceIdRayB_loopDegLe_dilateQ _ _
      (loopDegLe_jointQuartic (2 * d) d (fun j => hQfd _) (upar (r s)))
  · by_cases hp : p
    · exact Or.inl hp
    · exact Or.inr fun s => faceIdRayB_quart_dilateQ _ _
        (quart_jointQuartic (2 * d) d (fun j => (hQfq _).resolve_left hp) (upar (r s)))

/-! ### One piece from the numerator at every momentum -/

section Piece

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1])

include hflow hrow hrow4

/-- **The rate of one merged piece along the ray**, with the numerator hypotheses of
`heavyRate_vpPiece`: `N` polynomial of degree `d` in `k`, with representatives at every `k` of
degree `≤ d₁` along loop `1`, `≤ d₀` along loop `0` (no quartic part for `m = 5`). -/
theorem faceIdRayB_vpPiece_of_nodes {m : ℕ} (hm : m = 5 ∨ m = 6) (sh : Fin (m + 2) → Fin 5)
    (hsh : ∀ l : Fin (m + 2), sh l = 4 ↔ m ≤ (l : ℕ)) {E : Finset (Fin (m + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : ∀ k, IsLoopPoly 2 (m + 1 - 3) (N k))
    (hB : ∀ k, RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 (N k))
    {d : ℕ} (hk : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ) {d₁ d₀ : ℕ}
    (hQ₁ : ∀ k, ∃ Q : LoopQuartic, Q.eval = N k ∧ LoopDegLe 1 d₁ Q ∧ (m = 6 ∨ Q.quart = 0))
    (hQ₀ : ∀ k, ∃ Q : LoopQuartic, Q.eval = N k ∧ LoopDegLe 0 d₀ Q ∧ (m = 6 ∨ Q.quart = 0))
    (hd₁ : d₁ ≤ 3) (hd₀ : d₀ ≤ 3)
    (hA1 : 2 ≤ (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![1, 0]).card)
    (hd11 : (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![1, 0]).card = 2 →
      d₁ ≤ 1)
    (hR1 : ∃ l : Fin (m + 1), base (sh l.castSucc) = ![1, 0])
    (hA0 : 2 ≤ (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![0, 1]).card)
    (hd01 : (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![0, 1]).card = 2 →
      d₀ ≤ 1)
    (hR0 : ∃ l : Fin (m + 1), base (sh l.castSucc) = ![0, 1])
    {m₀ : ℝ} (hm₀ : 0 < m₀) (Ms : Fin (m + 1) → ℝ) (hMs : Ms (Fin.last m) = 0)
    (hf : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l) :
    FaceIdRayRateB fun t k => pairDens (N k)
      (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
      (fun l => c (sh l.castSucc) • k) Ms (Fin.last m) t := by
  obtain ⟨Q₁, B₁, hB₁, he₁, hd₁', hq₁⟩ := faceIdRayB_numFamily N hk hQ₁
  obtain ⟨Q₀, B₀, hB₀, he₀, hd₀', hq₀⟩ := faceIdRayB_numFamily N hk hQ₀
  have hr : ∀ s : {s : ℝ // 1 ≤ s}, 0 < Real.sqrt s.1 := fun s =>
    Real.sqrt_pos.2 (one_pos.trans_le s.2)
  refine faceIdRayB_vpPiece base c y₁ y₂ hflow hrow hrow4 hm sh hsh hcrit N hpoly hB (d + 4)
    Q₁ Q₀ hB₁ hB₀ (fun s => faceIdRayB_eval_dilateQ_inv (hr s) (d + 4) (he₁ s))
    (fun s => (he₀ s).trans (he₁ s).symm) hd₁' hd₀' ?_ hd₁ hd₀ hA1 hd11 hR1 hA0 hd01 hR0 hm₀ Ms
    hMs hf
  rcases hq₁ with h | h
  · exact Or.inl h
  · rcases hq₀ with h' | h'
    · exact Or.inl h'
    · exact Or.inr fun s => ⟨h s, h' s⟩

end Piece

end QED.GradedProof.RPi4

end
