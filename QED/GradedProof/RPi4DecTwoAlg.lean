/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# (R-Π₄) step L9: three-point calculus of second differences

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (second
differences in `s`). A derivative-free calculus for functions on an interval `[lo, hi]` that are
bounded by `M`, `L`-Lipschitz and have second differences `‖f(u + 2h) - 2f(u + h) + f(u)‖ ≤ K h²`
(`QED.GradedProof.RPi4.DecTwoReg`). The class is closed under sums, products, inverses away from
`0`, square roots away from `0` (real values) and composition with a real map of the same
class; the constants are explicit, so that the bounds can be integrated over a parameter.

* `DecTwoReg` and its API: `const`, `id`, `ofReal`, `add`, `sub`, `const_mul`, `sum`, `mul`,
  `inv`, `div`, `pow`, `comp`, `sqrt`, `congr`, `mono`.
-/

@[expose] public section

open Set

namespace QED.GradedProof.RPi4

/-- On `[lo, hi]`, `f` is bounded by `M`, `L`-Lipschitz, and its second differences are at most
`K h²`; the constants are nonnegative. -/
structure DecTwoReg {𝕜 : Type*} [RCLike 𝕜] (lo hi : ℝ) (f : ℝ → 𝕜) (M L K : ℝ) : Prop where
  nonneg : 0 ≤ M ∧ 0 ≤ L ∧ 0 ≤ K
  bound : ∀ u ∈ Icc lo hi, ‖f u‖ ≤ M
  lip : ∀ u ∈ Icc lo hi, ∀ v ∈ Icc lo hi, ‖f u - f v‖ ≤ L * |u - v|
  two : ∀ u h : ℝ, u ∈ Icc lo hi → u + 2 * h ∈ Icc lo hi →
    ‖f (u + 2 * h) - 2 * f (u + h) + f u‖ ≤ K * h ^ 2

theorem dec_mid_mem {lo hi u h : ℝ} (hu : u ∈ Icc lo hi) (h2 : u + 2 * h ∈ Icc lo hi) :
    u + h ∈ Icc lo hi :=
  ⟨by linarith [hu.1, h2.1], by linarith [hu.2, h2.2]⟩

namespace DecTwoReg

variable {𝕜 : Type*} [RCLike 𝕜] {lo hi : ℝ} {f g : ℝ → 𝕜} {M L K M' L' K' : ℝ}

theorem mono (hf : DecTwoReg lo hi f M L K) {M₂ L₂ K₂ : ℝ} (hM : M ≤ M₂) (hL : L ≤ L₂)
    (hK : K ≤ K₂) : DecTwoReg lo hi f M₂ L₂ K₂ where
  nonneg := ⟨hf.nonneg.1.trans hM, hf.nonneg.2.1.trans hL, hf.nonneg.2.2.trans hK⟩
  bound u hu := (hf.bound u hu).trans hM
  lip u hu v hv := (hf.lip u hu v hv).trans (mul_le_mul_of_nonneg_right hL (abs_nonneg _))
  two u h hu h2 := (hf.two u h hu h2).trans (mul_le_mul_of_nonneg_right hK (sq_nonneg _))

theorem congr (hf : DecTwoReg lo hi f M L K) (e : ∀ u ∈ Icc lo hi, f u = g u) :
    DecTwoReg lo hi g M L K where
  nonneg := hf.nonneg
  bound u hu := by rw [← e u hu]; exact hf.bound u hu
  lip u hu v hv := by rw [← e u hu, ← e v hv]; exact hf.lip u hu v hv
  two u h hu h2 := by
    rw [← e u hu, ← e _ h2, ← e _ (dec_mid_mem hu h2)]; exact hf.two u h hu h2

theorem subinterval (hf : DecTwoReg lo hi f M L K) {a b : ℝ} (ha : lo ≤ a) (hb : b ≤ hi) :
    DecTwoReg a b f M L K where
  nonneg := hf.nonneg
  bound u hu := hf.bound u ⟨ha.trans hu.1, hu.2.trans hb⟩
  lip u hu v hv := hf.lip u ⟨ha.trans hu.1, hu.2.trans hb⟩ v ⟨ha.trans hv.1, hv.2.trans hb⟩
  two u h hu h2 := hf.two u h ⟨ha.trans hu.1, hu.2.trans hb⟩ ⟨ha.trans h2.1, h2.2.trans hb⟩

theorem const (c : 𝕜) : DecTwoReg lo hi (fun _ => c) ‖c‖ 0 0 where
  nonneg := ⟨norm_nonneg _, le_rfl, le_rfl⟩
  bound _ _ := le_rfl
  lip _ _ _ _ := by simp
  two _ _ _ _ := by
    rw [show c - 2 * c + c = 0 by ring]; simp

theorem id : DecTwoReg lo hi (fun u : ℝ => u) (max |lo| |hi|) 1 0 where
  nonneg := ⟨(abs_nonneg _).trans (le_max_left _ _), zero_le_one, le_rfl⟩
  bound u hu := by
    rw [Real.norm_eq_abs]
    exact abs_le_max_abs_abs hu.1 hu.2
  lip u _ v _ := by rw [Real.norm_eq_abs, one_mul]
  two u h _ _ := by
    rw [show u + 2 * h - 2 * (u + h) + u = 0 by ring]; simp

theorem ofReal {φ : ℝ → ℝ} (hφ : DecTwoReg lo hi φ M L K) :
    DecTwoReg lo hi (fun u => (φ u : 𝕜)) M L K where
  nonneg := hφ.nonneg
  bound u hu := by rw [RCLike.norm_ofReal]; exact hφ.bound u hu
  lip u hu v hv := by
    rw [← RCLike.ofReal_sub, RCLike.norm_ofReal]; exact hφ.lip u hu v hv
  two u h hu h2 := by
    have e : (φ (u + 2 * h) : 𝕜) - 2 * (φ (u + h) : 𝕜) + (φ u : 𝕜) =
        ((φ (u + 2 * h) - 2 * φ (u + h) + φ u : ℝ) : 𝕜) := by push_cast; ring
    rw [e, RCLike.norm_ofReal]
    exact hφ.two u h hu h2

theorem add (hf : DecTwoReg lo hi f M L K) (hg : DecTwoReg lo hi g M' L' K') :
    DecTwoReg lo hi (fun u => f u + g u) (M + M') (L + L') (K + K') where
  nonneg := ⟨add_nonneg hf.nonneg.1 hg.nonneg.1, add_nonneg hf.nonneg.2.1 hg.nonneg.2.1,
    add_nonneg hf.nonneg.2.2 hg.nonneg.2.2⟩
  bound u hu := (norm_add_le _ _).trans (add_le_add (hf.bound u hu) (hg.bound u hu))
  lip u hu v hv := by
    rw [show f u + g u - (f v + g v) = (f u - f v) + (g u - g v) by ring, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hf.lip u hu v hv) (hg.lip u hu v hv))
  two u h hu h2 := by
    rw [show f (u + 2 * h) + g (u + 2 * h) - 2 * (f (u + h) + g (u + h)) + (f u + g u) =
      (f (u + 2 * h) - 2 * f (u + h) + f u) + (g (u + 2 * h) - 2 * g (u + h) + g u) by ring,
      add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hf.two u h hu h2) (hg.two u h hu h2))

theorem const_mul (hf : DecTwoReg lo hi f M L K) (c : 𝕜) :
    DecTwoReg lo hi (fun u => c * f u) (‖c‖ * M) (‖c‖ * L) (‖c‖ * K) where
  nonneg := ⟨mul_nonneg (norm_nonneg _) hf.nonneg.1, mul_nonneg (norm_nonneg _) hf.nonneg.2.1,
    mul_nonneg (norm_nonneg _) hf.nonneg.2.2⟩
  bound u hu := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hf.bound u hu) (norm_nonneg _)
  lip u hu v hv := by
    rw [← mul_sub, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hf.lip u hu v hv) (norm_nonneg _)
  two u h hu h2 := by
    rw [show c * f (u + 2 * h) - 2 * (c * f (u + h)) + c * f u =
      c * (f (u + 2 * h) - 2 * f (u + h) + f u) by ring, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hf.two u h hu h2) (norm_nonneg _)

theorem neg (hf : DecTwoReg lo hi f M L K) : DecTwoReg lo hi (fun u => -f u) M L K := by
  have h := hf.const_mul (-1)
  simp only [norm_neg, norm_one, one_mul, neg_one_mul] at h
  exact h

theorem sub (hf : DecTwoReg lo hi f M L K) (hg : DecTwoReg lo hi g M' L' K') :
    DecTwoReg lo hi (fun u => f u - g u) (M + M') (L + L') (K + K') :=
  (hf.add hg.neg).congr fun u _ => by ring

theorem zero : DecTwoReg lo hi (fun _ => (0 : 𝕜)) 0 0 0 := by
  simpa using (const (lo := lo) (hi := hi) (0 : 𝕜))

theorem sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → 𝕜} {Mi Li Ki : ι → ℝ}
    (h : ∀ i ∈ s, DecTwoReg lo hi (F i) (Mi i) (Li i) (Ki i)) :
    DecTwoReg lo hi (fun u => ∑ i ∈ s, F i u) (∑ i ∈ s, Mi i) (∑ i ∈ s, Li i)
      (∑ i ∈ s, Ki i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : DecTwoReg lo hi (fun _ => (0 : 𝕜)) 0 0 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mul (hf : DecTwoReg lo hi f M L K) (hg : DecTwoReg lo hi g M' L' K') :
    DecTwoReg lo hi (fun u => f u * g u) (M * M') (L * M' + M * L')
      (K * M' + M * K' + 2 * (L * L')) where
  nonneg := by
    obtain ⟨a, b, c⟩ := hf.nonneg
    obtain ⟨a', b', c'⟩ := hg.nonneg
    exact ⟨by positivity, by positivity, by positivity⟩
  bound u hu := by
    rw [norm_mul]
    exact mul_le_mul (hf.bound u hu) (hg.bound u hu) (norm_nonneg _) hf.nonneg.1
  lip u hu v hv := by
    rw [show f u * g u - f v * g v = (f u - f v) * g u + f v * (g u - g v) by ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 := mul_le_mul (hf.lip u hu v hv) (hg.bound u hu) (norm_nonneg _)
      (mul_nonneg hf.nonneg.2.1 (abs_nonneg _))
    have h2 := mul_le_mul (hf.bound v hv) (hg.lip u hu v hv) (norm_nonneg _) hf.nonneg.1
    nlinarith
  two u h hu h2 := by
    have h1 := dec_mid_mem hu h2
    have e : ∀ f0 f1 f2 g0 g1 g2 : 𝕜, f2 * g2 - 2 * (f1 * g1) + f0 * g0 =
        (f2 - 2 * f1 + f0) * g1 + f1 * (g2 - 2 * g1 + g0) + (f2 - f1) * (g2 - g1) +
          (f1 - f0) * (g1 - g0) := fun _ _ _ _ _ _ => by ring
    rw [e]
    have hd : ∀ (F : ℝ → 𝕜) (L₀ : ℝ), 0 ≤ L₀ → (∀ a ∈ Icc lo hi, ∀ b ∈ Icc lo hi,
        ‖F a - F b‖ ≤ L₀ * |a - b|) →
        ‖F (u + 2 * h) - F (u + h)‖ ≤ L₀ * |h| ∧ ‖F (u + h) - F u‖ ≤ L₀ * |h| :=
      fun F L₀ _ hF => ⟨by simpa [show u + 2 * h - (u + h) = h by ring] using hF _ h2 _ h1,
        by simpa using hF _ h1 _ hu⟩
    obtain ⟨df2, df1⟩ := hd f L hf.nonneg.2.1 hf.lip
    obtain ⟨dg2, dg1⟩ := hd g L' hg.nonneg.2.1 hg.lip
    have t1 := mul_le_mul (hf.two u h hu h2) (hg.bound _ h1) (norm_nonneg _)
      (mul_nonneg hf.nonneg.2.2 (sq_nonneg h))
    have t2 := mul_le_mul (hf.bound _ h1) (hg.two u h hu h2) (norm_nonneg _) hf.nonneg.1
    have t3 := mul_le_mul df2 dg2 (norm_nonneg _) (mul_nonneg hf.nonneg.2.1 (abs_nonneg _))
    have t4 := mul_le_mul df1 dg1 (norm_nonneg _) (mul_nonneg hf.nonneg.2.1 (abs_nonneg _))
    have hh : |h| * |h| = h ^ 2 := by rw [← abs_mul, ← sq, abs_sq]
    have hLL : L * |h| * (L' * |h|) = L * L' * h ^ 2 := by rw [← hh]; ring
    refine norm_add₄_le.trans ?_
    simp only [norm_mul]
    linarith

theorem inv (hf : DecTwoReg lo hi f M L K) {m : ℝ} (hm : 0 < m)
    (hlow : ∀ u ∈ Icc lo hi, m ≤ ‖f u‖) :
    DecTwoReg lo hi (fun u => (f u)⁻¹) m⁻¹ (L / m ^ 2) ((2 * L ^ 2 + M * K) / m ^ 3) where
  nonneg := by
    obtain ⟨a, b, c⟩ := hf.nonneg
    exact ⟨by positivity, by positivity, by positivity⟩
  bound u hu := by
    rw [norm_inv]; exact inv_anti₀ hm (hlow u hu)
  lip u hu v hv := by
    have hu0 : f u ≠ 0 := norm_pos_iff.mp (hm.trans_le (hlow u hu))
    have hv0 : f v ≠ 0 := norm_pos_iff.mp (hm.trans_le (hlow v hv))
    rw [show (f u)⁻¹ - (f v)⁻¹ = (f v - f u) / (f u * f v) by field_simp, norm_div, norm_mul,
      norm_sub_rev, div_le_iff₀ (by positivity : 0 < ‖f u‖ * ‖f v‖)]
    have hmm : m ^ 2 ≤ ‖f u‖ * ‖f v‖ := by
      rw [sq]; exact mul_le_mul (hlow u hu) (hlow v hv) hm.le (norm_nonneg _)
    have hL : 0 ≤ L / m ^ 2 * |u - v| := mul_nonneg (by have := hf.nonneg.2.1; positivity)
      (abs_nonneg _)
    calc ‖f u - f v‖ ≤ L * |u - v| := hf.lip u hu v hv
      _ = L / m ^ 2 * |u - v| * m ^ 2 := by field_simp
      _ ≤ L / m ^ 2 * |u - v| * (‖f u‖ * ‖f v‖) := mul_le_mul_of_nonneg_left hmm hL
  two u h hu h2 := by
    have h1 := dec_mid_mem hu h2
    have n0 := hlow u hu; have n1 := hlow _ h1; have n2 := hlow _ h2
    set g0 := f u; set g1 := f (u + h); set g2 := f (u + 2 * h)
    have z0 : g0 ≠ 0 := norm_pos_iff.mp (hm.trans_le n0)
    have z1 : g1 ≠ 0 := norm_pos_iff.mp (hm.trans_le n1)
    have z2 : g2 ≠ 0 := norm_pos_iff.mp (hm.trans_le n2)
    rw [show g2⁻¹ - 2 * g1⁻¹ + g0⁻¹ =
      (2 * ((g1 - g0) * (g2 - g1)) - g1 * (g2 - 2 * g1 + g0)) / (g0 * g1 * g2) by
      field_simp; ring, norm_div]
    have d2 : ‖g2 - g1‖ ≤ L * |h| := by
      simpa [show u + 2 * h - (u + h) = h by ring] using hf.lip _ h2 _ h1
    have d1 : ‖g1 - g0‖ ≤ L * |h| := by simpa using hf.lip _ h1 _ hu
    have hh : |h| * |h| = h ^ 2 := by rw [← abs_mul, ← sq, abs_sq]
    have hL := hf.nonneg.2.1
    have hnum : ‖2 * ((g1 - g0) * (g2 - g1)) - g1 * (g2 - 2 * g1 + g0)‖ ≤
        (2 * L ^ 2 + M * K) * h ^ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_mul, RCLike.norm_ofNat]
      have t1 := mul_le_mul d1 d2 (norm_nonneg _) (mul_nonneg hL (abs_nonneg _))
      have t2 := mul_le_mul (hf.bound _ h1) (hf.two u h hu h2) (norm_nonneg _) hf.nonneg.1
      nlinarith
    have hden : m ^ 3 ≤ ‖g0 * g1 * g2‖ := by
      rw [norm_mul, norm_mul, pow_three]
      have := mul_le_mul n0 n1 hm.le (norm_nonneg _)
      calc m * (m * m) = m * m * m := by ring
        _ ≤ ‖g0‖ * ‖g1‖ * ‖g2‖ := mul_le_mul this n2 hm.le (by positivity)
    rw [div_le_iff₀ ((by positivity : (0 : ℝ) < m ^ 3).trans_le hden)]
    have hc : 0 ≤ (2 * L ^ 2 + M * K) * h ^ 2 / m ^ 3 := by
      have := hf.nonneg; have := hf.nonneg.2.2; have := hf.nonneg.1; positivity
    calc _ ≤ (2 * L ^ 2 + M * K) * h ^ 2 := hnum
      _ = (2 * L ^ 2 + M * K) * h ^ 2 / m ^ 3 * m ^ 3 := by field_simp
      _ ≤ (2 * L ^ 2 + M * K) * h ^ 2 / m ^ 3 * ‖g0 * g1 * g2‖ :=
          mul_le_mul_of_nonneg_left hden hc
      _ = (2 * L ^ 2 + M * K) / m ^ 3 * h ^ 2 * ‖g0 * g1 * g2‖ := by ring

theorem div (hf : DecTwoReg lo hi f M L K) (hg : DecTwoReg lo hi g M' L' K') {m : ℝ}
    (hm : 0 < m) (hlow : ∀ u ∈ Icc lo hi, m ≤ ‖g u‖) :
    ∃ M₂ L₂ K₂, DecTwoReg lo hi (fun u => f u / g u) M₂ L₂ K₂ :=
  ⟨_, _, _, (hf.mul (hg.inv hm hlow)).congr fun _ _ => (div_eq_mul_inv _ _).symm⟩

theorem pow (hf : DecTwoReg lo hi f M L K) (n : ℕ) :
    ∃ M₂ L₂ K₂, DecTwoReg lo hi (fun u => f u ^ n) M₂ L₂ K₂ := by
  induction n with
  | zero => exact ⟨_, _, _, (const 1).congr fun u _ => (pow_zero _).symm⟩
  | succ n ih =>
    obtain ⟨M₂, L₂, K₂, h⟩ := ih
    exact ⟨_, _, _, (h.mul hf).congr fun u _ => (pow_succ _ _).symm⟩

/-- **Composition with a real map of the class.** -/
theorem comp {a b : ℝ} {φ : ℝ → ℝ} {Mφ Lφ Kφ : ℝ} (hf : DecTwoReg lo hi f M L K)
    (hφ : DecTwoReg a b φ Mφ Lφ Kφ) (hmap : ∀ s ∈ Icc a b, φ s ∈ Icc lo hi) :
    DecTwoReg a b (fun s => f (φ s)) M (L * Lφ) (K * Lφ ^ 2 + L * Kφ) where
  nonneg := by
    obtain ⟨_, b₁, c₁⟩ := hf.nonneg
    obtain ⟨_, b₂, c₂⟩ := hφ.nonneg
    exact ⟨hf.nonneg.1, by positivity, by positivity⟩
  bound s hs := hf.bound _ (hmap s hs)
  lip s hs t ht := by
    refine (hf.lip _ (hmap s hs) _ (hmap t ht)).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (by simpa using hφ.lip s hs t ht) hf.nonneg.2.1
  two s h hs h2 := by
    have h1 := dec_mid_mem hs h2
    set p0 := φ s; set p1 := φ (s + h); set p2 := φ (s + 2 * h)
    have m0 := hmap s hs; have m2 := hmap _ h2
    set η := (p2 - p0) / 2
    have hη2 : p0 + 2 * η = p2 := by simp only [η]; ring
    have m2' : p0 + 2 * η ∈ Icc lo hi := by rw [hη2]; exact m2
    have mη := dec_mid_mem m0 m2'
    rw [show f p2 - 2 * f p1 + f p0 = (f (p0 + 2 * η) - 2 * f (p0 + η) + f p0) +
      2 * (f (p0 + η) - f p1) by rw [hη2]; ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, RCLike.norm_ofNat]
    have e1 := hf.two p0 η m0 m2'
    have e2 := hf.lip _ mη _ (hmap _ h1)
    have hφl : |p2 - p0| ≤ Lφ * |2 * h| := by
      simpa [Real.norm_eq_abs, show s + 2 * h - s = 2 * h by ring] using hφ.lip _ h2 _ hs
    have hφt : |p2 - 2 * p1 + p0| ≤ Kφ * h ^ 2 := by
      simpa [Real.norm_eq_abs] using hφ.two s h hs h2
    have hηb : η ^ 2 ≤ Lφ ^ 2 * h ^ 2 := by
      have : |η| ≤ Lφ * |h| := by
        simp only [η, abs_div, abs_two]
        rw [abs_mul, abs_two] at hφl
        linarith
      rw [← sq_abs η, ← sq_abs h, ← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have hmid : |p0 + η - p1| = |p2 - 2 * p1 + p0| / 2 := by
      rw [show p0 + η - p1 = (p2 - 2 * p1 + p0) / 2 by simp only [η]; ring, abs_div, abs_two]
    have hK := hf.nonneg.2.2
    have hL := hf.nonneg.2.1
    have t1 : K * η ^ 2 ≤ K * (Lφ ^ 2 * h ^ 2) := mul_le_mul_of_nonneg_left hηb hK
    have t2 : L * |p0 + η - p1| ≤ L * (Kφ * h ^ 2 / 2) := by
      rw [hmid]; exact mul_le_mul_of_nonneg_left (by linarith) hL
    nlinarith

/-- **Square roots of real functions bounded below by `m > 0`.** -/
theorem sqrt {φ : ℝ → ℝ} (hφ : DecTwoReg lo hi φ M L K) {m : ℝ} (hm : 0 < m)
    (hlow : ∀ u ∈ Icc lo hi, m ≤ φ u) :
    DecTwoReg lo hi (fun u => Real.sqrt (φ u)) (Real.sqrt M) (L / (2 * Real.sqrt m))
      (K / (2 * Real.sqrt m) + L ^ 2 / (4 * Real.sqrt m ^ 3)) := by
  set σ := Real.sqrt m with hσ
  have hσ0 : 0 < σ := Real.sqrt_pos.2 hm
  have hr : ∀ u ∈ Icc lo hi, σ ≤ Real.sqrt (φ u) := fun u hu => Real.sqrt_le_sqrt (hlow u hu)
  have hsq : ∀ u ∈ Icc lo hi, Real.sqrt (φ u) ^ 2 = φ u := fun u hu =>
    Real.sq_sqrt (hm.le.trans (hlow u hu))
  have hL := hφ.nonneg.2.1
  have hlip : ∀ u ∈ Icc lo hi, ∀ v ∈ Icc lo hi,
      |Real.sqrt (φ u) - Real.sqrt (φ v)| ≤ L / (2 * σ) * |u - v| := by
    intro u hu v hv
    have e : (Real.sqrt (φ u) - Real.sqrt (φ v)) * (Real.sqrt (φ u) + Real.sqrt (φ v)) =
        φ u - φ v := by nlinarith [hsq u hu, hsq v hv]
    have hs : 2 * σ ≤ Real.sqrt (φ u) + Real.sqrt (φ v) := by linarith [hr u hu, hr v hv]
    have hl : |φ u - φ v| ≤ L * |u - v| := by simpa using hφ.lip u hu v hv
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : |Real.sqrt (φ u) - Real.sqrt (φ v)| * (Real.sqrt (φ u) + Real.sqrt (φ v)) =
        |φ u - φ v| := by
      rw [← e, abs_mul, abs_of_pos (by linarith : 0 < Real.sqrt (φ u) + Real.sqrt (φ v))]
    nlinarith [abs_nonneg (Real.sqrt (φ u) - Real.sqrt (φ v))]
  refine ⟨⟨Real.sqrt_nonneg _, by positivity, ?_⟩, fun u hu => ?_, fun u hu v hv => ?_,
    fun u h hu h2 => ?_⟩
  · have := hφ.nonneg.2.2; positivity
  · rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt ((le_abs_self _).trans (by simpa using hφ.bound u hu))
  · rw [Real.norm_eq_abs]; exact hlip u hu v hv
  · have h1 := dec_mid_mem hu h2
    set r0 := Real.sqrt (φ u); set r1 := Real.sqrt (φ (u + h))
    set r2 := Real.sqrt (φ (u + 2 * h))
    have key : (r2 - 2 * r1 + r0) * (r2 + r1) =
        (φ (u + 2 * h) - 2 * φ (u + h) + φ u) + (r1 - r0) * (r0 - r2) := by
      linear_combination hsq _ h2 - 2 * hsq _ h1 + hsq _ hu
    have hs : 2 * σ ≤ r2 + r1 := by linarith [hr _ h2, hr _ h1]
    have d1 : |r1 - r0| ≤ L / (2 * σ) * |h| := by simpa using hlip _ h1 _ hu
    have d2 : |r0 - r2| ≤ L / (2 * σ) * |2 * h| := by
      simpa [show u - (u + 2 * h) = -(2 * h) by ring, abs_neg] using hlip _ hu _ h2
    have tw : |φ (u + 2 * h) - 2 * φ (u + h) + φ u| ≤ K * h ^ 2 := by
      simpa using hφ.two u h hu h2
    rw [abs_mul, abs_two] at d2
    have hh : |h| * |h| = h ^ 2 := by rw [← abs_mul, ← sq, abs_sq]
    have hA : 0 ≤ L / (2 * σ) := by positivity
    have hprod : |r1 - r0| * |r0 - r2| ≤ L / (2 * σ) * |h| * (L / (2 * σ) * (2 * |h|)) :=
      mul_le_mul d1 d2 (abs_nonneg _) (by positivity)
    have hnum : |r2 - 2 * r1 + r0| * (r2 + r1) ≤ K * h ^ 2 + L ^ 2 / (2 * σ ^ 2) * h ^ 2 := by
      rw [← abs_of_pos (by linarith : 0 < r2 + r1), ← abs_mul, key]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      have e : L / (2 * σ) * |h| * (L / (2 * σ) * (2 * |h|)) = L ^ 2 / (2 * σ ^ 2) * h ^ 2 := by
        rw [← hh]; field_simp
      linarith
    rw [Real.norm_eq_abs]
    have hfin : (K / (2 * σ) + L ^ 2 / (4 * σ ^ 3)) * h ^ 2 * (2 * σ) =
        K * h ^ 2 + L ^ 2 / (2 * σ ^ 2) * h ^ 2 := by field_simp; ring
    have hc : 0 ≤ K * h ^ 2 + L ^ 2 / (2 * σ ^ 2) * h ^ 2 := by
      have := hφ.nonneg.2.2; positivity
    by_contra hcon
    replace hcon := lt_of_not_ge hcon
    have := mul_lt_mul hcon hs (by positivity) (abs_nonneg _)
    nlinarith [abs_nonneg (r2 - 2 * r1 + r0)]

end DecTwoReg

end QED.GradedProof.RPi4

end
