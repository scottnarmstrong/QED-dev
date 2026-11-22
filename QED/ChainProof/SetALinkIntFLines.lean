/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0NsAmp

/-!
# A block-summed product of line factors at two loops

Helper for the Phase 5 Stage 3a goal (HA₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setA`
(decision D-58), for the classes `FA`, `FB`. Lines `i : ι` carry the momenta
`k_i = a_{i0} ℓ₀ + a_{i1} ℓ₁ + q_i` (`QED.GradedProof.X0.rowMom`), numerator factors `N_i` of
degree `d_i`, the denominators of the masses `ms i`, and, on the lines of `Z`, one more
denominator at the flavour mass `M_f`. If the multiplicities pass `BlockCrit`, then
`∑_f c_f w_f (M_f²)^j ∏_i N_i(k_i) ∏_{M ∈ ms i} D_M(k_i)⁻¹ ∏_{i ∈ Z} D_{M_f}(k_i)⁻¹` satisfies
(T₉′) at two loops (`jointEnergyFirstIntegrable_blockLines`), for weights `w` constant on the
Pauli–Villars blocks.

## Proof

The mass expansion of the flavour sum (`QED.GradedProof.X0.jointEnergyFirstIntegrable_blockSumGen`,
with the lines of `Z`) leaves terms with one or two extra lines parallel to lines of `Z`; each is
an integrand of `QED.GradedProof.X0.jointEnergyFirstIntegrable_lines_pad` with the
multiplicities checked by `BlockCrit`. This is the argument of
`QED.GradedProof.X0.jointEnergyFirstIntegrable_nsTerm`, with abstract lines.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetALink

open QED.GradedProof.X0
open QED.TwoLoop.Bridge (propDenom)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `n` with one more on each line of `S`. -/
def addS (n : ι → ℕ) (S : Finset ι) : ι → ℕ :=
  fun i => n i + if i ∈ S then 1 else 0

/-- The terms with two extra lines parallel to one line of `Z`, or one extra line parallel to
each line of a subset of `Z` with at least two elements. -/
def MultiCrit (a : ι → Fin 2 → ℤ) (n d : ι → ℕ) (Z : Finset ι) : Prop :=
  (∀ l ∈ Z, PadCrit a (bump n l 2) d) ∧
    ∀ S ∈ Z.powerset, 2 ≤ S.card → PadCrit a (addS n S) d

instance (a : ι → Fin 2 → ℤ) (n d : ι → ℕ) (Z : Finset ι) : Decidable (MultiCrit a n d Z) := by
  unfold MultiCrit; infer_instance

/-- **The criterion for a block-summed term of mass order `(M²)^j`.** -/
def BlockCrit (a : ι → Fin 2 → ℤ) (n d : ι → ℕ) (Z : Finset ι) (j : ℕ) : Prop :=
  j ≤ 2 ∧ (j = 2 → PadCrit a n d) ∧
    (j = 1 → (∀ l ∈ Z, PadCrit a (bump n l 1) d) ∧ MultiCrit a n d Z) ∧
    (j = 0 → MultiCrit a n d Z)

instance (a : ι → Fin 2 → ℤ) (n d : ι → ℕ) (Z : Finset ι) (j : ℕ) :
    Decidable (BlockCrit a n d Z j) := by
  unfold BlockCrit; infer_instance

/-- **(T₉′) for lines with extra denominators.** -/
theorem jointEnergyFirstIntegrable_linesExt (a : ι → Fin 2 → ℤ) (q : ι → Fin 4 → ℝ)
    (ms : ι → List ℝ) (d : ι → ℕ) (N : ι → (Fin 4 → ℝ) → ℂ)
    (hN : ∀ i, AffPoly (d i) (N i) ∨ a i = 0) (G : ι → List ℝ)
    (hcrit : PadCrit a (fun i => (ms i ++ G i).length) d) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      z * ((∏ i, N i (rowMom (a i) (q i) ℓ) * dProd ε (ms i) (rowMom (a i) (q i) ℓ)) *
        ∏ i, dProd ε (G i) (rowMom (a i) (q i) ℓ)) := by
  have h := jointEnergyFirstIntegrable_lines_pad a q (fun i => ms i ++ G i) d N hN hcrit hε z
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  rw [← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [dProd, List.map_append, List.prod_append]
  ring

theorem prod_dProd_ite (Z : Finset ι) (ε : ℝ) (g : ι → List ℝ) (K : ι → Fin 4 → ℝ) :
    ∏ i, dProd ε (if i ∈ Z then g i else []) (K i) = ∏ x : Z, dProd ε (g x.1) (K x.1) := by
  have h : ∀ i, dProd ε (if i ∈ Z then g i else []) (K i) =
      if i ∈ Z then dProd ε (g i) (K i) else 1 := fun i => by
    split_ifs <;> simp [dProd]
  rw [Finset.prod_congr rfl fun i _ => h i, Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_coe_sort Z fun i => dProd ε (g i) (K i)]

omit [Fintype ι] in
theorem length_ite (Z : Finset ι) (ms g : ι → List ℝ) (i : ι) :
    (ms i ++ if i ∈ Z then g i else []).length =
      (ms i).length + if i ∈ Z then (g i).length else 0 := by
  split_ifs <;> simp

variable {F : Type} [Fintype F] [DecidableEq F]

/-- **(T₉′) of a block-summed product of line factors.** -/
theorem jointEnergyFirstIntegrable_blockLines (Φ : Lepton.Flavors F) (rep : F → F)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (a : ι → Fin 2 → ℤ) (q : ι → Fin 4 → ℝ) (ms : ι → List ℝ) (d : ι → ℕ)
    (N : ι → (Fin 4 → ℝ) → ℂ) (hN : ∀ i, AffPoly (d i) (N i) ∨ a i = 0) (Z : Finset ι)
    (j : ℕ) (hcrit : BlockCrit a (fun i => (ms i).length + if i ∈ Z then 1 else 0) d Z j)
    {ε : ℝ} (hε : 0 < ε) (w : F → ℂ) (hw : ∀ f, w f = w (rep f)) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      ∑ f, (Φ.coeff f : ℂ) * (w f * ((Φ.mass f : ℂ) ^ 2) ^ j *
        ((∏ i, N i (rowMom (a i) (q i) ℓ) * dProd ε (ms i) (rowMom (a i) (q i) ℓ)) *
          ∏ i ∈ Z, (propDenom (Φ.mass f) ε (rowMom (a i) (q i) ℓ))⁻¹)) := by
  classical
  obtain ⟨hj, h2, h1, h0⟩ := hcrit
  set n : ι → ℕ := fun i => (ms i).length + if i ∈ Z then 1 else 0 with hn
  set K : ι → (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ := fun i ℓ => rowMom (a i) (q i) ℓ with hK
  set k : Z → (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ := fun x ℓ => K x.1 ℓ with hk
  set W : (Fin 2 → Fin 4 → ℝ) → ℂ := fun ℓ => ∏ i, N i (K i ℓ) * dProd ε (ms i) (K i ℓ)
    with hW
  set E : ℕ → F → (Fin 2 → Fin 4 → ℝ) → ℂ := fun i b ℓ => if j = i then w b * W ℓ else 0
    with hE
  -- the expansion terms with extra denominators `g` on the lines of `Z`
  have hL : ∀ (g : ι → List ℝ), PadCrit a (fun i => (ms i).length +
      if i ∈ Z then (g i).length else 0) d → ∀ z : ℂ,
      QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
        z * (W ℓ * ∏ x : Z, dProd ε (g x.1) (k x ℓ)) := by
    intro g hg z
    have h := jointEnergyFirstIntegrable_linesExt a q ms d N hN
      (fun i => if i ∈ Z then g i else []) (by simpa only [length_ite] using hg) hε z
    refine (congrArg _ (funext fun ℓ => ?_)).mp h
    rw [prod_dProd_ite Z ε g fun i => K i ℓ]
  have hzero : ∀ i, ¬ j = i → ∀ X : (Fin 2 → Fin 4 → ℝ) → ℂ, ∀ b (z : ℂ),
      QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ => z * (E i b ℓ * X ℓ) := by
    intro i hi X b z
    simp only [hE, hi, ↓reduceIte, zero_mul, mul_zero]
    exact jointEnergyFirstIntegrable_zero_fun'
  have hcons : ∀ (h : ι → List ℝ) ℓ, ∏ x : Z, dProd ε (0 :: h x.1) (k x ℓ) =
      (∏ x : Z, (propDenom 0 ε (k x ℓ))⁻¹) * ∏ x : Z, dProd ε (h x.1) (k x ℓ) := by
    intro h ℓ
    simp only [dProd_cons, Finset.prod_mul_distrib]
  have hone : ∀ (l : Z) (ms' : List ℝ) ℓ,
      ∏ x : Z, dProd ε (if x.1 = l.1 then ms' else []) (k x ℓ) = dProd ε ms' (k l ℓ) := by
    intro l ms' ℓ
    have h : ∀ x : Z, dProd ε (if x.1 = l.1 then ms' else []) (k x ℓ) =
        if l = x then dProd ε ms' (k x ℓ) else 1 := fun x => by
      by_cases hx : l = x
      · subst hx; simp
      · have hx' : ¬ x.1 = l.1 := fun h => hx (Subtype.ext h).symm
        simp [hx, hx', dProd_nil]
    rw [Finset.prod_congr rfl fun x _ => h x, Finset.prod_ite_eq]
    simp
  have hlen : ∀ (l : Z) (c : ℕ) (ms' : List ℝ), ms'.length = c → (fun i => (ms i).length +
      if i ∈ Z then (0 :: if i = l.1 then ms' else []).length else 0) = bump n l.1 c := by
    intro l c ms' hc
    funext i
    simp only [hn, bump]
    by_cases hi : i = l.1
    · subst hi
      simp [l.2, hc]
      omega
    · split_ifs <;> simp_all
  -- two extra lines on one line of `Z`
  have key₀₁ : ∀ i, (j = i → MultiCrit a n d Z) → ∀ b (M : ℝ) (z : ℂ) (l : Z),
      QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
        z * (E i b ℓ * ((∏ l', (propDenom 0 ε (k l' ℓ))⁻¹) * (propDenom 0 ε (k l ℓ))⁻¹ *
          (propDenom M ε (k l ℓ))⁻¹)) := by
    intro i hi b M z l
    by_cases hji : j = i
    · have h := hL (fun i => 0 :: if i = l.1 then [0, M] else [])
        (by rw [hlen l 2 [0, M] rfl]; exact (hi hji).1 l.1 l.2) (z * w b)
      refine (congrArg _ (funext fun ℓ => ?_)).mp h
      rw [hcons (fun i => if i = l.1 then [0, M] else []), hone]
      simp only [hE, hji, ↓reduceIte, dProd_cons, dProd_nil]
      ring
    · exact hzero i hji _ b z
  -- one extra line on each line of `S`
  have keyS : ∀ i, (j = i → MultiCrit a n d Z) → ∀ b (M : ℝ) (z : ℂ) (S : Finset Z),
      2 ≤ S.card → QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
        z * (E i b ℓ * ((∏ l', (propDenom 0 ε (k l' ℓ))⁻¹) *
          ∏ l ∈ S, (propDenom M ε (k l ℓ))⁻¹)) := by
    intro i hi b M z S hS
    by_cases hji : j = i
    · set S' := S.map (Function.Embedding.subtype fun i => i ∈ Z) with hS'
      have hmem : ∀ x : Z, x.1 ∈ S' ↔ x ∈ S := fun x =>
        Finset.mem_map' (Function.Embedding.subtype fun i => i ∈ Z)
      have hsub : S' ⊆ Z := fun i hi => by
        obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hi
        exact x.2
      have hl : (fun i => (ms i).length +
          if i ∈ Z then (0 :: if i ∈ S' then [M] else []).length else 0) = addS n S' := by
        funext i
        simp only [hn, addS]
        by_cases hi : i ∈ S'
        · simp [hsub hi, hi]
        · split_ifs <;> simp_all
      have hS'c : 2 ≤ S'.card := by rw [hS', Finset.card_map]; exact hS
      have h := hL (fun i => 0 :: if i ∈ S' then [M] else [])
        (by rw [hl]; exact (hi hji).2 S' (Finset.mem_powerset.mpr hsub) hS'c) (z * w b)
      refine (congrArg _ (funext fun ℓ => ?_)).mp h
      rw [hcons (fun i => if i ∈ S' then [M] else [])]
      have hS2 : ∏ x : Z, dProd ε (if x.1 ∈ S' then [M] else []) (k x ℓ) =
          ∏ x ∈ S, (propDenom M ε (k x ℓ))⁻¹ := by
        have h' : ∀ x : Z, dProd ε (if x.1 ∈ S' then [M] else []) (k x ℓ) =
            if x ∈ S then (propDenom M ε (k x ℓ))⁻¹ else 1 := fun x => by
          by_cases hx : x ∈ S
          · simp [(hmem x).mpr hx, hx, dProd]
          · simp [mt (hmem x).mp hx, hx, dProd]
        rw [Finset.prod_congr rfl fun x _ => h' x, Finset.prod_ite_mem, Finset.univ_inter]
      rw [hS2]
      simp only [hE, hji, ↓reduceIte]
      ring
    · exact hzero i hji _ b z
  have multi : ∀ i, (i = 0 ∨ i = 1) → j = i → MultiCrit a n d Z := by
    rintro i (rfl | rfl) rfl
    · exact h0 rfl
    · exact (h1 rfl).2
  have h := jointEnergyFirstIntegrable_blockSumGen Φ rep hrep hPV₁ hPV₂ k hε (E 0) (E 1) (E 2)
    (fun b M z => by
      by_cases hj2 : j = 2
      · have h := hL (fun _ => [M]) (by simpa [hn] using h2 hj2) (z * w b)
        refine (congrArg _ (funext fun ℓ => ?_)).mp h
        simp only [hE, hj2, ↓reduceIte, dProd_cons, dProd_nil, mul_one]
        ring
      · exact hzero 2 hj2 _ b z)
    (fun b z l => by
      by_cases hj1 : j = 1
      · have h := hL (fun i => 0 :: if i = l.1 then [0] else [])
          (by rw [hlen l 1 [0] rfl]; exact (h1 hj1).1 l.1 l.2) (z * w b)
        refine (congrArg _ (funext fun ℓ => ?_)).mp h
        rw [hcons (fun i => if i = l.1 then [0] else []), hone]
        simp only [hE, hj1, ↓reduceIte, dProd_cons, dProd_nil, mul_one]
        ring
      · exact hzero 1 hj1 _ b z)
    (fun E' hE' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hE'
      rcases hE' with rfl | rfl
      · exact key₀₁ 0 (multi 0 (Or.inl rfl))
      · exact key₀₁ 1 (multi 1 (Or.inr rfl)))
    (fun E' hE' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hE'
      rcases hE' with rfl | rfl
      · exact keyS 0 (multi 0 (Or.inl rfl))
      · exact keyS 1 (multi 1 (Or.inr rfl)))
  refine (congrArg _ (funext fun ℓ => Finset.sum_congr rfl fun f _ => ?_)).mp h
  rw [← Finset.prod_coe_sort Z, hw f]
  interval_cases j <;> simp +decide only [hE, hk, hW, hK, ↓reduceIte] <;> ring

end QED.ChainProof.SetALink

end
