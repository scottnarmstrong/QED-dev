/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLRegular
public import QED.Polylog.HPLSeries
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import QED.Polylog.ExtraIntegrals

/-!
# The Möbius duality of alternating harmonic polylogarithms at `1`

The involution `φ(t) = (1 - t) / (1 + t)` of `[0, 1]` (exchanging the endpoints) pulls the
kernels back to combinations of kernels:
`φ^*(dt/t) = -(dt/(1 - t) + dt/(1 + t))`, `φ^*(dt/(1 - t)) = -(dt/t - dt/(1 + t))`,
`φ^*(dt/(1 + t)) = -dt/(1 + t)`.
Since `φ` reverses the path `[0, 1]`, for every convergent word `w` over `{0, 1, -1}`
(first letter not `1`, last letter not `0`), `H(w; 1)` equals the signed sum of the values
`H(w'; 1)` over the words `w'` obtained by reversing `w` and replacing each letter by one of its
images `0 ↦ 1, -1`, `1 ↦ 0, -(-1)`, `-1 ↦ -1`. All words on the right are convergent.

The proof is the path-composition identity of `QED.Polylog.HPLDuality` with `1 - x` replaced
by `φ(x)`: `Φ(x) = ∑_{w = u v} G(u)(x) H(v; x)`, where `G(u)(x)` is the signed sum of
`H(u'; φ(x))` over the images `u'` of `u`; `Φ` has derivative zero on `(0, 1)`.

## Main definitions

* `QED.Polylog.HPL.mobLetter`, `QED.Polylog.HPL.mobImage`: the signed images of a letter and
  of a (reversed) word.
* `QED.Polylog.HPL.mobEval`: the value of a signed list of words.

## Main results

* `QED.Polylog.HPL.hpl_one_eq_mobEval_mobImage`:
  `H(w; 1) = ∑_{(k, w') ∈ mobImage wʳᵉᵛ} k H(w'; 1)` for a convergent word `w`.
-/

@[expose] public section

open Real Set Filter Topology

namespace QED.Polylog.HPL

open Letter

/-- The signed images of a letter under `t ↦ (1 - t)/(1 + t)`:
`0 ↦ 1 + (-1)`, `1 ↦ 0 - (-1)`, `-1 ↦ -1`. -/
def mobLetter : Letter → List (ℤ × Letter)
  | zero => [(1, one), (1, negOne)]
  | one => [(1, zero), (-1, negOne)]
  | negOne => [(1, negOne)]

/-- The signed images of a word, letter by letter. -/
def mobImage : List Letter → List (ℤ × List Letter)
  | [] => [(1, [])]
  | c :: q => (mobLetter c).flatMap fun p => (mobImage q).map fun r => (p.1 * r.1, p.2 :: r.2)

/-- The value `∑ k H(w; y)` of a signed list of words. -/
noncomputable def mobEval (L : List (ℤ × List Letter)) (y : ℝ) : ℝ :=
  (L.map fun r => (r.1 : ℝ) * hpl r.2 y).sum

/-- The involution `φ(x) = (1 - x)/(1 + x)`. -/
noncomputable def mobMap (x : ℝ) : ℝ := (1 - x) / (1 + x)

@[simp] theorem mobEval_nil (y : ℝ) : mobEval [] y = 0 := rfl

@[simp] theorem mobEval_cons (r : ℤ × List Letter) (L : List (ℤ × List Letter)) (y : ℝ) :
    mobEval (r :: L) y = r.1 * hpl r.2 y + mobEval L y := by
  simp [mobEval]

theorem mobEval_cons_fun (r : ℤ × List Letter) (L : List (ℤ × List Letter)) :
    mobEval (r :: L) = fun y => r.1 * hpl r.2 y + mobEval L y := by
  funext y
  exact mobEval_cons r L y

theorem mobEval_nil_fun : mobEval [] = fun _ => 0 := rfl

theorem mobEval_append (L M : List (ℤ × List Letter)) (y : ℝ) :
    mobEval (L ++ M) y = mobEval L y + mobEval M y := by
  simp [mobEval]

/-- The signed list `L` with the letter `d` prepended to every word. -/
def mobCons (d : Letter) (L : List (ℤ × List Letter)) : List (ℤ × List Letter) :=
  L.map fun r => (r.1, d :: r.2)

theorem mobEval_map_mul (e : ℤ) (d : Letter) (L : List (ℤ × List Letter)) (y : ℝ) :
    mobEval (L.map fun r => (e * r.1, d :: r.2)) y = e * mobEval (mobCons d L) y := by
  induction L with
  | nil => simp [mobCons]
  | cons r L ih =>
    simp only [List.map_cons, mobEval_cons, mobCons] at ih ⊢
    rw [ih]
    push_cast
    ring

theorem mobEval_mobImage_cons (c : Letter) (q : List Letter) (y : ℝ) :
    mobEval (mobImage (c :: q)) y =
      ((mobLetter c).map fun p => (p.1 : ℝ) * mobEval (mobCons p.2 (mobImage q)) y).sum := by
  simp only [mobImage]
  induction mobLetter c with
  | nil => simp
  | cons p l ih => simp [List.flatMap_cons, mobEval_append, ih, mobEval_map_mul]

theorem mobMap_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : mobMap x ∈ Ioo (0 : ℝ) 1 := by
  have h1 : 0 < 1 + x := by linarith [hx.1]
  refine ⟨div_pos (by linarith [hx.2]) h1, (div_lt_one h1).2 (by linarith [hx.1])⟩

theorem hasDerivAt_mobMap {x : ℝ} (hx : 0 < 1 + x) :
    HasDerivAt mobMap (-2 / (1 + x) ^ 2) x := by
  have h := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id' x)).div
    ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id' x)) hx.ne'
  convert h using 1
  · funext y
    simp [mobMap]
  · simp only [Pi.add_apply, Pi.sub_apply]
    ring

theorem hasDerivAt_mobEval_mobCons (d : Letter) :
    ∀ (L : List (ℤ × List Letter)) {y : ℝ}, y ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt (mobEval (mobCons d L)) (d.kernel y * mobEval L y) y
  | [], y, _ => by
    have e : mobEval (mobCons d []) = fun _ => 0 := by
      funext y
      simp [mobCons]
    rw [e]
    simpa using hasDerivAt_const y (0 : ℝ)
  | r :: L, y, hy => by
    have h := ((hasDerivAt_hpl_cons d r.2 hy).const_mul (r.1 : ℝ)).add
      (hasDerivAt_mobEval_mobCons d L hy)
    have e : mobEval (mobCons d (r :: L)) =
        fun y => (r.1 : ℝ) * hpl (d :: r.2) y + mobEval (mobCons d L) y := by
      funext y
      simp [mobCons]
    rw [e]
    convert h using 1
    simp only [mobEval_cons]
    ring

/-! ### The prefix function `G` -/

/-- `G q x = ∑_{(k, u') ∈ mobImage q} k H(u'; φ(x))`. -/
noncomputable def mobG (q : List Letter) (x : ℝ) : ℝ := mobEval (mobImage q) (mobMap x)

/-- The derivative of `mobG`: `0` for `q = []` and `-f c (x) G q' x` for `q = c :: q'`. -/
noncomputable def mobGDeriv : List Letter → ℝ → ℝ
  | [], _ => 0
  | c :: q, x => -(c.kernel x * mobG q x)

theorem mobG_nil : mobG [] = fun _ => 1 := by
  funext x
  simp [mobG, mobImage]

theorem hasDerivAt_mobG (q : List Letter) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (mobG q) (mobGDeriv q x) x := by
  cases q with
  | nil =>
    rw [mobG_nil]
    exact hasDerivAt_const x 1
  | cons c q =>
    have h1 : 0 < 1 + x := by linarith [hx.1]
    have hx0 : x ≠ 0 := hx.1.ne'
    have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
    have dφ := hasDerivAt_mobMap h1
    have hy := mobMap_mem_Ioo hx
    have dE := fun d : Letter => (hasDerivAt_mobEval_mobCons d (mobImage q) hy).comp x dφ
    have k1 : (1 - mobMap x)⁻¹ = (1 + x) / (2 * x) := by
      rw [mobMap, show 1 - (1 - x) / (1 + x) = 2 * x / (1 + x) by field_simp; ring, inv_div]
    have kn : (1 + mobMap x)⁻¹ = (1 + x) / 2 := by
      rw [mobMap, show 1 + (1 - x) / (1 + x) = 2 / (1 + x) by field_simp; ring, inv_div]
    have k0 : (mobMap x)⁻¹ = (1 + x) / (1 - x) := by
      rw [mobMap, inv_div]
    cases c with
    | zero =>
      have e : mobG (zero :: q) = (mobEval (mobCons one (mobImage q)) ∘ mobMap) +
          (mobEval (mobCons negOne (mobImage q)) ∘ mobMap) := by
        funext y
        simp [mobG, mobEval_mobImage_cons, mobLetter]
      rw [e]
      refine ((dE one).add (dE negOne)).congr_deriv ?_
      simp only [mobGDeriv, mobG, kernel_one, kernel_zero, kernel_negOne, k1, kn]
      field_simp
      ring
    | one =>
      have e : mobG (one :: q) = (mobEval (mobCons zero (mobImage q)) ∘ mobMap) -
          (mobEval (mobCons negOne (mobImage q)) ∘ mobMap) := by
        funext y
        simp [mobG, mobEval_mobImage_cons, mobLetter, sub_eq_add_neg]
      rw [e]
      refine ((dE zero).sub (dE negOne)).congr_deriv ?_
      simp only [mobGDeriv, mobG, kernel_one, kernel_zero, kernel_negOne, k0, kn]
      field_simp
      ring
    | negOne =>
      have e : mobG (negOne :: q) = mobEval (mobCons negOne (mobImage q)) ∘ mobMap := by
        funext y
        simp [mobG, mobEval_mobImage_cons, mobLetter]
      rw [e]
      refine (dE negOne).congr_deriv ?_
      simp only [mobGDeriv, mobG, kernel_negOne, kn]
      field_simp

/-! ### Words of the image -/

theorem mem_mobImage_cons {c : Letter} {q : List Letter} {r : ℤ × List Letter}
    (hr : r ∈ mobImage (c :: q)) :
    ∃ p ∈ mobLetter c, ∃ r' ∈ mobImage q, r = (p.1 * r'.1, p.2 :: r'.2) := by
  simp only [mobImage, List.mem_flatMap, List.mem_map] at hr
  obtain ⟨p, hp, r', hr', rfl⟩ := hr
  exact ⟨p, hp, r', hr', rfl⟩

theorem not_allZero_of_mem_mobImage : ∀ {q : List Letter}, (∃ c ∈ q, c ≠ one) →
    ∀ r ∈ mobImage q, ¬AllZero r.2
  | [], ⟨c, hc, _⟩, _, _ => by simp at hc
  | c :: q, hq, r, hr => by
    obtain ⟨p, hp, r', hr', rfl⟩ := mem_mobImage_cons hr
    by_cases hc : c = one
    · subst hc
      have hq' : ∃ c ∈ q, c ≠ one := by
        obtain ⟨d, hd, hd1⟩ := hq
        rcases List.mem_cons.1 hd with rfl | hd
        · exact absurd rfl hd1
        · exact ⟨d, hd, hd1⟩
      have := not_allZero_of_mem_mobImage hq' r' hr'
      simp only [allZero_cons, not_and]
      exact fun _ => this
    · simp only [allZero_cons, not_and]
      intro h0
      cases c with
      | zero => simp [mobLetter] at hp; rcases hp with rfl | rfl <;> simp at h0
      | one => exact absurd rfl hc
      | negOne => simp [mobLetter] at hp; subst hp; simp at h0

theorem head_ne_one_of_mem_mobImage {q : List Letter} (hq : q.head? ≠ some zero)
    {r : ℤ × List Letter} (hr : r ∈ mobImage q) : r.2.head? ≠ some one := by
  cases q with
  | nil => simp [mobImage] at hr; subst hr; simp
  | cons c q =>
    obtain ⟨p, hp, r', -, rfl⟩ := mem_mobImage_cons hr
    cases c with
    | zero => simp at hq
    | one => simp [mobLetter] at hp; rcases hp with rfl | rfl <;> simp
    | negOne => simp [mobLetter] at hp; subst hp; simp

/-! ### Bounds and limits -/

theorem abs_mobEval_le_one_sub_rpow (L : List (ℤ × List Letter)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Ico (1 / 2 : ℝ) 1, |mobEval L t| ≤ C * (1 - t) ^ (-ε) := by
  induction L with
  | nil => exact ⟨0, le_rfl, fun t _ => by simp⟩
  | cons r L ih =>
    obtain ⟨C, hC, hCb⟩ := ih
    obtain ⟨D, hD, hDb⟩ := abs_hpl_le_one_sub_rpow r.2 hε
    refine ⟨|(r.1 : ℝ)| * D + C, by positivity, fun t ht => ?_⟩
    rw [mobEval_cons]
    calc |(r.1 : ℝ) * hpl r.2 t + mobEval L t|
        ≤ |(r.1 : ℝ)| * |hpl r.2 t| + |mobEval L t| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |(r.1 : ℝ)| * (D * (1 - t) ^ (-ε)) + C * (1 - t) ^ (-ε) := by
          gcongr
          · exact hDb t ht
          · exact hCb t ht
      _ = (|(r.1 : ℝ)| * D + C) * (1 - t) ^ (-ε) := by ring

theorem abs_mobEval_le_sqrt (L : List (ℤ × List Letter)) (hL : ∀ r ∈ L, ¬AllZero r.2)
    {b : ℝ} (hb : b < 1) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Ioc 0 b, |mobEval L t| ≤ C * t ^ (1 / 2 : ℝ) := by
  induction L with
  | nil => exact ⟨0, le_rfl, fun t _ => by simp⟩
  | cons r L ih =>
    obtain ⟨C, hC, hCb⟩ := ih fun r' hr' => hL r' (List.mem_cons_of_mem _ hr')
    obtain ⟨D, hD, hDb⟩ := abs_hpl_le_sqrt (hL r List.mem_cons_self) hb
    refine ⟨|(r.1 : ℝ)| * D + C, by positivity, fun t ht => ?_⟩
    rw [mobEval_cons]
    calc |(r.1 : ℝ) * hpl r.2 t + mobEval L t|
        ≤ |(r.1 : ℝ)| * |hpl r.2 t| + |mobEval L t| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |(r.1 : ℝ)| * (D * t ^ (1 / 2 : ℝ)) + C * t ^ (1 / 2 : ℝ) := by
          gcongr
          · exact hDb t ht
          · exact hCb t ht
      _ = (|(r.1 : ℝ)| * D + C) * t ^ (1 / 2 : ℝ) := by ring

theorem tendsto_mobEval_one : ∀ (L : List (ℤ × List Letter)),
    (∀ r ∈ L, r.2.head? ≠ some one) → Tendsto (mobEval L) (𝓝[<] 1) (𝓝 (mobEval L 1))
  | [], _ => by
    rw [mobEval_nil_fun]
    exact tendsto_const_nhds
  | r :: L, hL => by
    have h := ((tendsto_hpl_of_head_ne_one (hL r List.mem_cons_self)).const_mul (r.1 : ℝ)).add
      (tendsto_mobEval_one L fun r' hr' => hL r' (List.mem_cons_of_mem _ hr'))
    rw [mobEval_cons_fun]
    simpa using h

theorem tendsto_mobEval_zero : ∀ (L : List (ℤ × List Letter)),
    (∀ r ∈ L, ¬AllZero r.2) → Tendsto (mobEval L) (𝓝[>] 0) (𝓝 0)
  | [], _ => by
    rw [mobEval_nil_fun]
    exact tendsto_const_nhds
  | r :: L, hL => by
    have h := ((tendsto_hpl_zero (hL r List.mem_cons_self)).const_mul (r.1 : ℝ)).add
      (tendsto_mobEval_zero L fun r' hr' => hL r' (List.mem_cons_of_mem _ hr'))
    rw [mobEval_cons_fun]
    simpa using h

theorem tendsto_mobMap_zero : Tendsto mobMap (𝓝[>] 0) (𝓝[<] 1) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : ContinuousAt mobMap 0 :=
      (continuousAt_const.sub continuousAt_id).div (continuousAt_const.add continuousAt_id)
        (by norm_num)
    have h := this.tendsto
    rw [show mobMap 0 = 1 by norm_num [mobMap]] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    exact (div_lt_one (by linarith)).2 (by linarith)

theorem tendsto_mobMap_one : Tendsto mobMap (𝓝[<] 1) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : ContinuousAt mobMap 1 :=
      (continuousAt_const.sub continuousAt_id).div (continuousAt_const.add continuousAt_id)
        (by norm_num)
    have h := this.tendsto
    rw [show mobMap 1 = 0 by norm_num [mobMap]] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsLT (show (-1 : ℝ) < 1 by norm_num)] with x
      (hx : x < 1) hx'
    exact div_pos (by linarith) (by linarith [hx'.1])

/-- `G q x H(v; x) → 0` as `x → 0⁺` when `v` is not all zeros. -/
theorem tendsto_mobG_mul_hpl_zero (q : List Letter) {v : List Letter} (hv : ¬AllZero v) :
    Tendsto (fun x => mobG q x * hpl v x) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC, hCv⟩ := abs_hpl_le_sqrt hv (b := 1 / 3) (by norm_num)
  obtain ⟨D, hD, hDu⟩ := abs_mobEval_le_one_sub_rpow (mobImage q) (ε := 1 / 4) (by norm_num)
  refine tendsto_zero_of_abs_le_rpow (C := D * C) (r := 1 / 4) (b := 1 / 3) (by norm_num)
    (by norm_num) fun t ht => ?_
  have h1t : 0 < 1 + t := by linarith [ht.1]
  have hφ : mobMap t ∈ Ico (1 / 2 : ℝ) 1 := by
    refine ⟨?_, (div_lt_one h1t).2 (by linarith [ht.1])⟩
    rw [mobMap, le_div_iff₀ h1t]
    linarith [ht.2]
  have hle : t ≤ 1 - mobMap t := by
    rw [mobMap, show 1 - (1 - t) / (1 + t) = 2 * t / (1 + t) by field_simp; ring,
      le_div_iff₀ h1t]
    nlinarith [ht.1, ht.2]
  have h1 : |mobG q t| ≤ D * t ^ (-(1 / 4) : ℝ) := by
    exact (hDu _ hφ).trans
      (mul_le_mul_of_nonneg_left (rpow_le_rpow_of_nonpos ht.1 hle (by norm_num)) hD)
  rw [abs_mul]
  calc |mobG q t| * |hpl v t| ≤ (D * t ^ (-(1 / 4) : ℝ)) * (C * t ^ (1 / 2 : ℝ)) :=
        mul_le_mul h1 (hCv t ht) (abs_nonneg _) (mul_nonneg hD (rpow_nonneg ht.1.le _))
    _ = D * C * (t ^ (-(1 / 4) : ℝ) * t ^ (1 / 2 : ℝ)) := by ring
    _ = D * C * t ^ (1 / 4 : ℝ) := by
      rw [← rpow_add ht.1]
      norm_num

/-- `G q x H(v; x) → 0` as `x → 1⁻` when `q` has a letter other than `1`. -/
theorem tendsto_mobG_mul_hpl_one {q : List Letter} (hq : ∃ c ∈ q, c ≠ one) (v : List Letter) :
    Tendsto (fun x => mobG q x * hpl v x) (𝓝[<] 1) (𝓝 0) := by
  obtain ⟨C, hC, hCq⟩ := abs_mobEval_le_sqrt (mobImage q) (not_allZero_of_mem_mobImage hq)
    (b := 1 / 2) (by norm_num)
  obtain ⟨D, hD, hDv⟩ := abs_hpl_le_one_sub_rpow v (ε := 1 / 4) (by norm_num)
  have h0 : Tendsto (fun s => mobG q (1 - s) * hpl v (1 - s)) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_zero_of_abs_le_rpow (C := C * D) (r := 1 / 4) (b := 1 / 2) (by norm_num)
      (by norm_num) fun s hs => ?_
    have h2s : 0 < 1 + (1 - s) := by linarith [hs.2]
    have hφ0 : 0 < mobMap (1 - s) := div_pos (by linarith [hs.1]) h2s
    have hφs : mobMap (1 - s) ≤ s := by
      rw [mobMap, div_le_iff₀ h2s]
      nlinarith [hs.1, hs.2]
    have h1 : |mobG q (1 - s)| ≤ C * s ^ (1 / 2 : ℝ) := by
      refine (hCq _ ⟨hφ0, hφs.trans hs.2⟩).trans ?_
      gcongr
    have h2 : |hpl v (1 - s)| ≤ D * s ^ (-(1 / 4) : ℝ) := by
      have := hDv (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
      rwa [sub_sub_cancel] at this
    rw [abs_mul]
    calc |mobG q (1 - s)| * |hpl v (1 - s)| ≤
          (C * s ^ (1 / 2 : ℝ)) * (D * s ^ (-(1 / 4) : ℝ)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hC (rpow_nonneg hs.1.le _))
      _ = C * D * (s ^ (1 / 2 : ℝ) * s ^ (-(1 / 4) : ℝ)) := by ring
      _ = C * D * s ^ (1 / 4 : ℝ) := by
        rw [← rpow_add hs.1]
        norm_num
  refine (h0.comp tendsto_one_sub_nhdsLT_one).congr fun x => ?_
  simp only [Function.comp_apply, sub_sub_cancel]

/-! ### The path-composition function -/

/-- `Φ(q, v)(x) = ∑_{v = v₁ v₂} G(v₁ʳᵉᵛ ++ q)(x) H(v₂; x)`. -/
noncomputable def mobPhi : List Letter → List Letter → ℝ → ℝ
  | q, [], x => mobG q x
  | q, c :: v, x => mobG q x * hpl (c :: v) x + mobPhi (c :: q) v x

theorem hasDerivAt_mobPhi : ∀ (v q : List Letter), ∀ x ∈ Ioo (0 : ℝ) 1,
    HasDerivAt (mobPhi q v) (mobGDeriv q x * hpl v x) x
  | [], q, x, hx => by
    simpa [mobPhi] using hasDerivAt_mobG q hx
  | c :: v, q, x, hx => by
    have h := ((hasDerivAt_mobG q hx).mul (hasDerivAt_hpl_cons c v hx)).add
      (hasDerivAt_mobPhi v (c :: q) x hx)
    have e : mobPhi q (c :: v) = fun x => mobG q x * hpl (c :: v) x + mobPhi (c :: q) v x :=
      rfl
    rw [e]
    convert h using 1
    simp only [mobGDeriv]
    ring

/-- `Φ(q, v) → ∑ k H(u'; 1)` (over the images of `vʳᵉᵛ ++ q`) at `0⁺`, if `v` has no trailing
zero and `vʳᵉᵛ ++ q` does not start with `0`. -/
theorem tendsto_mobPhi_zero : ∀ (v q : List Letter), v.getLast? ≠ some zero →
    (v.reverse ++ q).head? ≠ some zero →
    Tendsto (mobPhi q v) (𝓝[>] 0) (𝓝 (mobEval (mobImage (v.reverse ++ q)) 1))
  | [], q, _, hq => by
    simp only [List.reverse_nil, List.nil_append] at hq ⊢
    exact (tendsto_mobEval_one _ fun r hr => head_ne_one_of_mem_mobImage hq hr).comp
      tendsto_mobMap_zero
  | c :: v, q, hv, hq => by
    have ih := tendsto_mobPhi_zero v (c :: q) (getLast?_ne_of_cons hv) (by simpa using hq)
    have h0 := tendsto_mobG_mul_hpl_zero q
      (not_allZero_of_getLast? (List.cons_ne_nil c v) hv)
    have := h0.add ih
    rw [zero_add] at this
    simpa [mobPhi] using this

/-- `Φ(q, v) → 0` at `1⁻` if `q` has a letter other than `1`. -/
theorem tendsto_mobPhi_one : ∀ (v q : List Letter), (∃ c ∈ q, c ≠ one) →
    Tendsto (mobPhi q v) (𝓝[<] 1) (𝓝 0)
  | [], q, hq => by
    exact (tendsto_mobEval_zero _ (not_allZero_of_mem_mobImage hq)).comp tendsto_mobMap_one
  | c :: v, q, hq => by
    obtain ⟨d, hd, hd1⟩ := hq
    have := (tendsto_mobG_mul_hpl_one ⟨d, hd, hd1⟩ (c :: v)).add
      (tendsto_mobPhi_one v (c :: q) ⟨d, List.mem_cons_of_mem _ hd, hd1⟩)
    rw [zero_add] at this
    simpa [mobPhi] using this

/-- **The Möbius duality at `1`.** For a word `w` over `{0, 1, -1}` with first letter not `1`
and last letter not `0`, `H(w; 1) = ∑_{(k, w') ∈ mobImage wʳᵉᵛ} k H(w'; 1)`. -/
theorem hpl_one_eq_mobEval_mobImage {w : List Letter} (h1 : w.head? ≠ some one)
    (h0 : w.getLast? ≠ some zero) :
    hpl w 1 = mobEval (mobImage w.reverse) 1 := by
  cases w with
  | nil => simp [mobImage]
  | cons a w' =>
    have ha : a ≠ one := fun h => h1 (by simp [h])
    have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (mobPhi [] (a :: w')) 0 x := fun x hx => by
      simpa [mobGDeriv] using hasDerivAt_mobPhi (a :: w') [] x hx
    have hlim0 := tendsto_mobPhi_zero (a :: w') [] h0 (by
      rw [List.append_nil, List.head?_reverse]; exact h0)
    have hconst := eq_of_hasDerivAt_zero_of_tendsto_right zero_lt_one hd hlim0
    have hlim1 : Tendsto (mobPhi [] (a :: w')) (𝓝[<] 1) (𝓝 (hpl (a :: w') 1)) := by
      have := (tendsto_hpl_one ha w').add
        (tendsto_mobPhi_one w' [a] ⟨a, List.mem_cons_self, ha⟩)
      rw [add_zero] at this
      refine this.congr fun x => ?_
      simp [mobPhi, mobG_nil]
    have hlim1' : Tendsto (mobPhi [] (a :: w')) (𝓝[<] 1)
        (𝓝 (mobEval (mobImage ((a :: w').reverse ++ [])) 1)) :=
      tendsto_nhds_of_eventually_eq (by
        filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with x hx using hconst x hx)
    rw [tendsto_nhds_unique hlim1 hlim1', List.append_nil]

end QED.Polylog.HPL
