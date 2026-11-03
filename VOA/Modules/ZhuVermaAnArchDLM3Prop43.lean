/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDefectDerivation
import VOA.Modules.ZhuVermaAnArchDLM3PBWSplit

/-!
# DLM3 Proposition 4.3 at `n = 0` — the bottom of `M_0(U)` pairs to zero

Dong–Li–Mason (`q-alg/9612010v2`) §4 close their Theorem 4.1 with the chain
Proposition 4.3 ⟹ Proposition 4.6 ⟹ Proposition 4.7 ⟹ `U(V̂)W ⊆ J`.  **Proposition 4.3** — the
base of the chain — says that the associativity defect, paired against `U*` at the *bottom*
`u ∈ U ⊆ M_n(U)`, vanishes; it rests on their key **Lemma 4.4** (the `i ≥ 1` half of which is the
free `ℓ ≥ 0` iterate identity, the `i = 0` half of which is the genuine content) together with
**Lemma 4.5** (the `L₋₁`-derivation induction that pushes `i = 0` down to every negative pole).

This file ports that base **at `n = 0`**, where it is Zhu's classical situation, and proves more
than the pairing: in the level-`0` slice the bottom defect is *literally zero*.

## Main results

* `indDefectVec_bottom_neg_one` (with `indDefectVec_bottom_neg_one_nat` / `_gen` covering the
  weight-`0` slot `𝒱₀ = ℂ𝟙` and negative weights) — **DLM3 Lemma 4.4 at `i = 0`, `n = 0`**:
  `δ(a, b, [1 ⊗ u], −1, wt a + wt b − 1) = 0`.  The proof is DLM3's, specialized:
  * the whole "product" family `a₍₋₁₋ᵢ₎b₍…₊ᵢ₎[1 ⊗ u]` dies because `P₀ = V̂_{≤0}` kills the bottom;
  * each surviving "opposite" term is straightened by the `V̂` commutator, whose degree-`0` value in
    `A(𝒱)` is `zhuDeg0_bracket_gen_complement`;
  * the leftover collapses through `zhuMul_eq_resFull_sum` into exactly
    `ρ([a ∗ b])u − ρ([a])ρ([b])u`, which is **zero by the `A(𝒱)`-module axiom on `U`**
    (`AMod.ρ_mul`) — DLM3's "the `A_n(V)`-module structure on `U` is equivalent to
    `o(a)o(b)u = a(wt a − 1)b(wt b − 1)u`".
* `indDefectVec_bottom_negPole` — **DLM3 Lemma 4.5 at `n = 0`**: the same vanishing for every
  `ℓ < 0`, by downward induction through `defectVec_Lneg1_left`.
* `indDefectVec_bottom_level_zero` / `indDefectVec_bottom_level_le` — the level-`≤ 0` slice of the
  bottom defect vanishes outright (`ℓ ≥ 0` is the proved `indDefectVec_nonneg`, level `< 0` the
  proved `indDefectVec_bottom_eq_zero_of_level_neg`).  **Unconditional: no PBW.**
* `proj_indDefectVec_bottom` — **DLM3 Proposition 4.3 at `n = 0`**, in the repo's
  `BottomProjection` language: `π₀(δ(a, b, [1 ⊗ u], ℓ, N)) = 0` for *all* `a, b ∈ 𝒱` and all
  `(ℓ, N)`.  The only carried input is the `BottomProjection` datum (i.e. the PBW
  hypothesis `PBWFreeness`); positive
  levels are killed by the projection, non-positive ones by the theorems above.

## What this does *not* yet give (named precisely)

`DefectPairsToZero` (DLM3's `U(V̂)W ⊆ J`) additionally needs

* **DLM3 Proposition 4.6** — propagation of `proj_indDefectVec_bottom` from the bottom `1 ⊗ U` to
  every vector of `M_0(U)` (`bottomPropagates` below); and
* **DLM3 Proposition 4.7** — propagation across the `U(V̂)`-orbit (`orbitPropagates` below).

Both are stated here as explicit `Prop`s and `defectPairsToZero_of_prop43` assembles them with this
file's Proposition 4.3 into `DefectPairsToZero`, hence (via the proved
`indBarBottom_injective_of_defectPairsToZero`) into the survival of `U`.  They are **carried, never
assumed silently**.

## References
DLM3 (`q-alg/9612010v2`) §4: Lemma 4.4 (pp. 14–17), Lemma 4.5 (pp. 17–18), Props 4.3/4.6/4.7;
DLM2 (`q-alg/9509005`) Prop 6.1 (the unpaired form of DLM3 Prop 4.6);
`ZhuVermaAnArchDefectDerivation`, `ZhuVermaAnArchDLM3PBWSplit`, `ZhuVermaAnArchDLM3Survival`,
`ZhuVermaAnArchDLM3Zero` (`parabolicRepOfAMod`, `indBottom_zhu_equivariant`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat

namespace DLM3

variable {W : VertexOperatorAlgebra 𝒱}

/-- `V̂(0) ⊆ P₀`. -/
theorem deg_zero_le_parabolic (W : VertexOperatorAlgebra 𝒱) :
    deg W 0 ≤ parabolic W 0 := by
  have h : degSpan W {(0 : ℤ)} ≤ degSpan W (parabolicSet 0) :=
    degSpan_mono W (fun d hd => Or.inl (by simpa using hd))
  rw [degSpan_singleton] at h
  exact h

/-- **DLM3 Lemma 4.4 at `i = 0`, `n = 0`** — the `ℓ = −1` iterate defect at the bottom of
`M_0(U)` in the level-`0` slice is **zero**, and its vanishing is exactly the `A(𝒱)`-module axiom
`o(a)o(b)u = o(a∗b)u` on `U`. -/
theorem indDefectVec_bottom_neg_one (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {kk : ℕ}
    (hkk : 1 ≤ kk) {l : ℤ} {a b : 𝒱} (ha : a ∈ W.grading (kk : ℤ)) (hb : b ∈ W.grading l)
    (u : U.carrier) :
    VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a b
      (indBottom (parabolicRepOfAMod W U) u) (-1) ((kk : ℤ) + l - 1) = 0 := by
  obtain ⟨kk', rfl⟩ : ∃ kk' : ℕ, kk = kk' + 1 := ⟨kk - 1, by omega⟩
  set Q := parabolicRepOfAMod W U with hQdef
  set K : ℤ := ((kk' + 1 : ℕ) : ℤ) + l - 1 with hKdef
  set z := indBottom Q u with hzdef
  -- the two scalar normalizations at `ℓ = -1`
  have hsc : ∀ i : ℕ, negOnePow (i : ℤ) * cbz (-1) (i : ℤ) = 1 := by
    intro i
    rw [ZhuRes.cbz_neg_one i, negOnePow_natCast]
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hm1 : negOnePow (-1 : ℤ) = -1 := by simp [negOnePow]
  rw [VHatRep.defectVec_eq_split (indRho Q) (ind_actModeTruncated Q) a b z (-1) K]
  -- (1) the product half vanishes identically
  have hA : ∀ i : ℤ, VHatRep.aterm (indRho Q) a b z (-1) K i = 0 := by
    intro i
    rcases lt_or_ge i 0 with h | h
    · rw [VHatRep.aterm, cbz_apply_neg (-1) h, mul_zero, zero_smul]
    · rw [VHatRep.aterm, hzdef, indBottom_actMode_eq_zero_of_neg Q hb (by omega) u, map_zero,
        smul_zero]
  rw [finsum_congr hA, finsum_zero, sub_zero]
  -- (2) the opposite half is supported on `0 ≤ i ≤ kk'`
  have hBzero : ∀ i : ℤ, i < 0 ∨ (((kk' + 1 : ℕ)) : ℤ) ≤ i →
      VHatRep.bterm (indRho Q) a b z (-1) K i = 0 := by
    intro i hi
    rcases hi with hi | hi
    · rw [VHatRep.bterm, cbz_apply_neg (-1) hi, mul_zero, zero_smul]
    · rw [VHatRep.bterm, hzdef, indBottom_actMode_eq_zero_of_neg Q ha (by omega) u, map_zero,
        smul_zero, smul_zero]
  -- (3) the commutation step, term by term
  have hkey : ∀ j : ℕ, VHatRep.bterm (indRho Q) a b z (-1) K (j : ℤ)
      = indBottom Q (U.ρ (_root_.VOA.mk W (resFull W (j : ℤ) 0 a b)) u)
        - (indRho Q).actMode a (j : ℤ) ((indRho Q).actMode b (-1 + K - (j : ℤ)) z) := by
    intro j
    have hmem : ⁅gen W a (j : ℤ), gen W b (-1 + K - (j : ℤ))⁆ ∈ parabolic W 0 := by
      refine degSpan_lie_mem W (S := {((kk' + 1 : ℕ) : ℤ) - (j : ℤ) - 1})
        (T := {l - (-1 + K - (j : ℤ)) - 1}) ?_ (gen_mem_degSpan W ha rfl)
        (gen_mem_degSpan W hb rfl)
      intro d hd e he
      rw [Set.mem_singleton_iff] at hd he
      have hsum0 : d + e = 0 := by rw [hd, he, hKdef]; push_cast; ring
      exact Or.inl hsum0
    have hact : (indRho Q) ⁅gen W a (j : ℤ), gen W b (-1 + K - (j : ℤ))⁆ z
        = indBottom Q (U.ρ (_root_.VOA.mk W (resFull W (j : ℤ) 0 a b)) u) := by
      have h := indBottom_equivariant Q
        (⟨⁅gen W a (j : ℤ), gen W b (-1 + K - (j : ℤ))⁆, hmem⟩ : Pn W 0) u
      rw [← h, hQdef, parabolicRepOfAMod_act]
      congr 2
      have hdeg : ((kk' + 1 : ℕ) : ℤ) - (j : ℤ) - 1 + (l - (-1 + K - (j : ℤ)) - 1) = 0 := by
        rw [hKdef]; push_cast; ring
      rw [show ((⟨⁅gen W a (j : ℤ), gen W b (-1 + K - (j : ℤ))⁆, hmem⟩ : Pn W 0) :
            VHatCarrier W) = vhb W (gen W a (j : ℤ)) (gen W b (-1 + K - (j : ℤ))) from
          (vhb_eq_bracket W _ _).symm,
        zhuDeg0_bracket_gen_complement W ha hb hdeg]
    have hcomm : (indRho Q).actMode b (-1 + K - (j : ℤ)) ((indRho Q).actMode a (j : ℤ) z)
        = (indRho Q).actMode a (j : ℤ) ((indRho Q).actMode b (-1 + K - (j : ℤ)) z)
          - indBottom Q (U.ρ (_root_.VOA.mk W (resFull W (j : ℤ) 0 a b)) u) := by
      rw [← hact, (indRho Q).map_lie, Ring.lie_def]
      simp only [VHatRep.actMode_def, LinearMap.sub_apply, Module.End.mul_apply]
      abel
    rw [VHatRep.bterm, hsc j, one_smul, hm1, hcomm, neg_smul, one_smul, neg_sub]
  -- (4) all but the top term of the second half vanish
  have hlow : ∀ j : ℕ, j < kk' → (indRho Q).actMode b (-1 + K - (j : ℤ)) z = 0 := by
    intro j hj
    rw [hzdef]
    exact indBottom_actMode_eq_zero_of_neg Q hb (by rw [hKdef]; push_cast; omega) u
  have hlast : (indRho Q).actMode a (kk' : ℤ) ((indRho Q).actMode b (-1 + K - (kk' : ℤ)) z)
      = indBottom Q (U.ρ (_root_.VOA.mk W a) (U.ρ (_root_.VOA.mk W b) u)) := by
    have hbstep : (indRho Q).actMode b (-1 + K - (kk' : ℤ)) z
        = indBottom Q (U.ρ (_root_.VOA.mk W b) u) := by
      rw [hzdef, hQdef, indBottom_zhu_equivariant W U hb u]
      congr 1
      rw [hKdef]; push_cast; ring
    rw [hbstep, hQdef, show ((kk' : ℤ)) = ((kk' + 1 : ℕ) : ℤ) - 1 from by push_cast; ring,
      ← indBottom_zhu_equivariant W U ha]
  -- (5) assemble
  rw [← range_sum_eq_finsumZ (kk' + 1) (fun i : ℤ => VHatRep.bterm (indRho Q) a b z (-1) K i)
      hBzero,
    Finset.sum_congr rfl (fun j _ => hkey j), Finset.sum_sub_distrib,
    Finset.sum_range_succ (fun j : ℕ =>
      (indRho Q).actMode a (j : ℤ) ((indRho Q).actMode b (-1 + K - (j : ℤ)) z)) kk']
  have hzerosum : (∑ j ∈ Finset.range kk',
      (indRho Q).actMode a (j : ℤ) ((indRho Q).actMode b (-1 + K - (j : ℤ)) z)) = 0 :=
    Finset.sum_eq_zero fun j hj => by rw [hlow j (Finset.mem_range.mp hj), map_zero]
  rw [hzerosum, zero_add, hlast]
  -- the head term
  have hhead : (indRho Q).actMode (W.smul a (-1) b) K z
      = indBottom Q (U.ρ (_root_.VOA.mk W (W.smul a (-1) b)) u) := by
    rw [hzdef, hQdef,
      indBottom_zhu_equivariant W U (W.toPreVertexAlgebra.smul_mem_grading ha hb (-1)) u]
    congr 1
    rw [hKdef]; push_cast; ring
  have hcollapse : U.ρ (_root_.VOA.mk W (W.smul a (-1) b)) u
      + ((∑ x ∈ Finset.range (kk' + 1),
            U.ρ (_root_.VOA.mk W (resFull W (x : ℤ) 0 a b)) u)
        - U.ρ (_root_.VOA.mk W a) (U.ρ (_root_.VOA.mk W b) u)) = 0 := by
    have hsum : (∑ x ∈ Finset.range (kk' + 1),
        U.ρ (_root_.VOA.mk W (resFull W (x : ℤ) 0 a b)) u)
        = U.ρ (_root_.VOA.mk W
            (∑ x ∈ Finset.range (kk' + 1), resFull W (x : ℤ) 0 a b)) u := by
      rw [map_sum, map_sum, LinearMap.sum_apply]
    rw [hsum, ← add_sub_assoc, ← LinearMap.add_apply, ← map_add, ← map_add,
      ← zhuMul_eq_resFull_sum W ha b, U.ρ_mul a b]
    simp [Module.End.mul_apply]
  rw [hhead, ← map_sum (indBottom Q), ← map_sub, ← map_add, hcollapse, map_zero]

/-- The `ℓ = −1` bottom defect vanishes for every homogeneous `a` of *natural* weight (the
weight-`0` case is the vacuum, `𝒱₀ = ℂ𝟙`). -/
theorem indDefectVec_bottom_neg_one_nat (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {kk : ℕ}
    {l : ℤ} {a b : 𝒱} (ha : a ∈ W.grading (kk : ℤ)) (hb : b ∈ W.grading l) (u : U.carrier) :
    VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a b
      (indBottom (parabolicRepOfAMod W U) u) (-1) ((kk : ℤ) + l - 1) = 0 := by
  rcases Nat.eq_zero_or_pos kk with hk | hk
  · subst hk
    rw [Nat.cast_zero] at ha ⊢
    rw [W.vacuum_grade, Submodule.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [VHatRep.defectVec_smul_left₁ _ (ind_actModeTruncated _),
      VHatRep.defectVec_vacuum_left _ (ind_vacuumCreation _), smul_zero]
  · exact indDefectVec_bottom_neg_one W U hk ha hb u

/-- The `ℓ = −1` bottom defect vanishes for every homogeneous `a` (any integer weight). -/
theorem indDefectVec_bottom_neg_one_gen (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {w l : ℤ}
    {a b : 𝒱} (ha : a ∈ W.grading w) (hb : b ∈ W.grading l) (u : U.carrier) :
    VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a b
      (indBottom (parabolicRepOfAMod W U) u) (-1) (w + l - 1) = 0 := by
  rcases lt_or_ge w 0 with hw | hw
  · rw [W.positivity w hw, Submodule.mem_bot] at ha
    subst ha
    exact VHatRep.defectVec_zero_left₁ _ (ind_actModeTruncated _) b _ (-1) (w + l - 1)
  · obtain ⟨kk, rfl⟩ : ∃ kk : ℕ, w = (kk : ℤ) := ⟨w.toNat, by omega⟩
    exact indDefectVec_bottom_neg_one_nat W U ha hb u

/-- **DLM3 Lemma 4.5 at `n = 0`** — every strictly negative-pole iterate defect at the bottom of
`M_0(U)`, in the level-`0` slice, vanishes.  Downward induction on `−ℓ` from the `ℓ = −1` case
through the `L₋₁`-derivation `defectVec_Lneg1_left`. -/
theorem indDefectVec_bottom_negPole (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    ∀ (s : ℕ) {w l : ℤ} {a b : 𝒱}, a ∈ W.grading w → b ∈ W.grading l → ∀ u : U.carrier,
      VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a b
        (indBottom (parabolicRepOfAMod W U) u) (-1 - (s : ℤ))
        (w + l - (-1 - (s : ℤ)) - 2) = 0 := by
  intro s
  induction s with
  | zero =>
    intro w l a b ha hb u
    have h := indDefectVec_bottom_neg_one_gen W U ha hb u
    rw [Nat.cast_zero, sub_zero, show (w + l - -1 - 2 : ℤ) = w + l - 1 from by ring]
    exact h
  | succ s ih =>
    intro w l a b ha hb u
    have hL : W.L (-1) a ∈ W.grading (w + 1) := L_neg_one_mem_grading_succ W ha
    have hih := ih hL hb u
    have hrec := VHatRep.defectVec_Lneg1_left (indRho (parabolicRepOfAMod W U))
      (ind_actModeTruncated _) a b (indBottom (parabolicRepOfAMod W U) u) (-1 - (s : ℤ))
      (w + l - (-1 - ((s : ℤ) + 1)) - 2)
    rw [show (w + 1 + l - (-1 - (s : ℤ)) - 2) = w + l - (-1 - ((s : ℤ) + 1)) - 2 from by ring]
      at hih
    rw [hih] at hrec
    have hne : (-((-1 - (s : ℤ) : ℤ) : ℂ)) ≠ 0 := by
      have heq : (-((-1 - (s : ℤ) : ℤ) : ℂ)) = ((s + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [heq]
      exact_mod_cast Nat.succ_ne_zero s
    have hz := (smul_eq_zero.mp hrec.symm).resolve_left hne
    rw [show (-1 - ((s : ℕ) : ℤ) - 1) = -1 - (((s + 1 : ℕ)) : ℤ) from by push_cast; ring,
      show (w + l - (-1 - ((s : ℤ) + 1)) - 2) = w + l - (-1 - (((s + 1 : ℕ)) : ℤ)) - 2 from by
        push_cast; ring] at hz
    exact hz

/-! ## The level-`≤ 0` slice, unconditional -/

/-- **The bottom defect vanishes in the level-`0` slice, for every pole order.**  `ℓ ≥ 0` is the
proved `indDefectVec_nonneg`; `ℓ < 0` is `indDefectVec_bottom_negPole`. -/
theorem indDefectVec_bottom_level_zero (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {w l : ℤ}
    {a b : 𝒱} (ha : a ∈ W.grading w) (hb : b ∈ W.grading l) (u : U.carrier) {ℓ N : ℤ}
    (hS : w + l - ℓ - N - 2 = 0) :
    VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a b
      (indBottom (parabolicRepOfAMod W U) u) ℓ N = 0 := by
  rcases lt_or_ge ℓ 0 with hl | hl
  · obtain ⟨s, hs⟩ : ∃ s : ℕ, ℓ = -1 - (s : ℤ) := ⟨(-1 - ℓ).toNat, by omega⟩
    subst hs
    have h := indDefectVec_bottom_negPole W U s ha hb u
    rwa [show w + l - (-1 - (s : ℤ)) - 2 = N from by omega] at h
  · obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le hl
    subst hj
    exact indDefectVec_nonneg _ a b _ j N

/-- **The bottom defect vanishes in every level `≤ 0`.**  Unconditional (no PBW). -/
theorem indDefectVec_bottom_level_le (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {w l : ℤ}
    {a b : 𝒱} (ha : a ∈ W.grading w) (hb : b ∈ W.grading l) (u : U.carrier) {ℓ N : ℤ}
    (hS : w + l - ℓ - N - 2 ≤ 0) :
    VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a b
      (indBottom (parabolicRepOfAMod W U) u) ℓ N = 0 := by
  rcases lt_or_eq_of_le hS with h | h
  · exact indDefectVec_bottom_eq_zero_of_level_neg _ ha hb u ℓ N h
  · exact indDefectVec_bottom_level_zero W U ha hb u h

/-! ## DLM3 Proposition 4.3 at `n = 0` -/

/-- **DLM3 Proposition 4.3 at `n = 0`, homogeneous slots.**  With the PBW-supplied projection
`π₀ : M_0(U) → U`, the bottom defect pairs to zero for every `(ℓ, N)`: if the defect sits in level
`0` it is already zero (`indDefectVec_bottom_level_zero`), and otherwise `π₀` kills it
(`BottomProjection.proj_defect_bottom_eq_zero_of_ne`). -/
theorem proj_indDefectVec_bottom_homog (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U)) {w l : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading w) (hb : b ∈ W.grading l) (u : U.carrier) (ℓ N : ℤ) :
    Pr.proj (VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a b
      (indBottom (parabolicRepOfAMod W U) u) ℓ N) = 0 := by
  by_cases hS : w + l - ℓ - N - 2 = 0
  · rw [indDefectVec_bottom_level_zero W U ha hb u hS, map_zero]
  · exact Pr.proj_defect_bottom_eq_zero_of_ne ha hb u ℓ N (by omega)

/-- **DLM3 Proposition 4.3 at `n = 0`** — for **all** `a, b ∈ 𝒱` (not merely homogeneous) and all
`(ℓ, N)`, the bottom defect pairs to zero.  Extended from `proj_indDefectVec_bottom_homog` by the
proved bilinearity of `defectVec` in its two `𝒱`-slots. -/
theorem proj_indDefectVec_bottom (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U)) (a b : 𝒱) (u : U.carrier) (ℓ N : ℤ) :
    Pr.proj (VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a b
      (indBottom (parabolicRepOfAMod W U) u) ℓ N) = 0 := by
  have htr := ind_actModeTruncated (parabolicRepOfAMod W U)
  have hkey : ∀ (w : ℤ) (a' : 𝒱), a' ∈ W.grading w → ∀ b' : 𝒱,
      Pr.proj (VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a' b'
        (indBottom (parabolicRepOfAMod W U) u) ℓ N) = 0 := by
    intro w a' ha' b'
    have hbtop : b' ∈ ⨆ i, W.grading i := by
      rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
    refine Submodule.iSup_induction W.grading
      (motive := fun b' => Pr.proj (VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a' b'
        (indBottom (parabolicRepOfAMod W U) u) ℓ N) = 0) hbtop ?_ ?_ ?_
    · intro i y hy
      exact proj_indDefectVec_bottom_homog W U Pr ha' hy u ℓ N
    · change Pr.proj (VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a' 0
        (indBottom (parabolicRepOfAMod W U) u) ℓ N) = 0
      rw [VHatRep.defectVec_zero_left₂ _ htr, map_zero]
    · intro y z hy hz
      change Pr.proj (VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a' (y + z)
        (indBottom (parabolicRepOfAMod W U) u) ℓ N) = 0
      rw [VHatRep.defectVec_add_left₂ _ htr, map_add, hy, hz, add_zero]
  have hatop : a ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun a => Pr.proj (VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a b
      (indBottom (parabolicRepOfAMod W U) u) ℓ N) = 0) hatop ?_ ?_ ?_
  · intro i y hy
    exact hkey i y hy b
  · change Pr.proj (VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) 0 b
      (indBottom (parabolicRepOfAMod W U) u) ℓ N) = 0
    rw [VHatRep.defectVec_zero_left₁ _ htr, map_zero]
  · intro y z hy hz
    change Pr.proj (VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) (y + z) b
      (indBottom (parabolicRepOfAMod W U) u) ℓ N) = 0
    rw [VHatRep.defectVec_add_left₁ _ htr, map_add, hy, hz, add_zero]

/-! ## The two remaining DLM3 propagations, named -/

/-- **DLM3 Proposition 4.6** (the `u ∈ U ↦ u ∈ M` propagation), as an explicit `Prop`.  DLM3 give no
printed proof; the unpaired form is DLM2 Proposition 6.1 (`refs/dlm2.txt:784-911`), and the
`⟨u′, ·⟩` insertion is mechanical.  **Carried, not assumed.** -/
def BottomPropagates {W : VertexOperatorAlgebra 𝒱} {U : AMod W}
    (Pr : BottomProjection (parabolicRepOfAMod W U)) : Prop :=
  (∀ (a b : 𝒱) (u : U.carrier) (ℓ N : ℤ),
      Pr.proj (VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a b
        (indBottom (parabolicRepOfAMod W U) u) ℓ N) = 0) →
    ∀ (a b : 𝒱) (z : IndMod (parabolicRepOfAMod W U)) (ℓ N : ℤ),
      Pr.proj (VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a b z ℓ N) = 0

/-- **DLM3 Proposition 4.7** (the `U(V̂)`-orbit propagation), as an explicit `Prop`: once the defect
pairs to zero at every vector, it pairs to zero after any `U(V̂)`-translate.  **Carried, not
assumed.** -/
def OrbitPropagates {W : VertexOperatorAlgebra 𝒱} {U : AMod W}
    (Pr : BottomProjection (parabolicRepOfAMod W U)) : Prop :=
  (∀ (a b : 𝒱) (z : IndMod (parabolicRepOfAMod W U)) (ℓ N : ℤ),
      Pr.proj (VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a b z ℓ N) = 0) →
    ∀ (a b : 𝒱) (z : IndMod (parabolicRepOfAMod W U)) (ℓ N : ℤ) (y : UEnv W),
      Pr.proj ((indRho (parabolicRepOfAMod W U)).toAlgHom y
        (VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a b z ℓ N)) = 0

/-- **The assembly.**  This file's Proposition 4.3 (`proj_indDefectVec_bottom`) plus the two
carried DLM3 propagations give `DefectPairsToZero` — DLM3's `U(V̂)W ⊆ J` at `n = 0`. -/
theorem defectPairsToZero_of_prop43 (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U))
    (h46 : BottomPropagates Pr) (h47 : OrbitPropagates Pr) : DefectPairsToZero Pr :=
  fun a b z ℓ N y =>
    h47 (h46 (fun a' b' u' ℓ' N' => proj_indDefectVec_bottom W U Pr a' b' u' ℓ' N')) a b z ℓ N y

/-- **`U` survives** — DLM3 Theorem 4.1 at `n = 0`, on this file's Proposition 4.3 plus the two
named propagations: the bottom map `U → M̄_0(U)` is injective. -/
theorem indBarBottom_injective_of_prop43 (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U))
    (h46 : BottomPropagates Pr) (h47 : OrbitPropagates Pr) :
    Function.Injective (indBarBottom (parabolicRepOfAMod W U)) :=
  indBarBottom_injective_of_defectPairsToZero Pr (defectPairsToZero_of_prop43 W U Pr h46 h47)

/-- **`U` survives, conditional on the independent `PBWFreeness` hypothesis.** Same statement
with the `BottomProjection` datum replaced by `PBWFreeness` from
`ZhuVermaAnArchDLM3PBWSplit`. Its exact remaining field is bottom injectivity, because level
independence is unconditional. Concrete adjoint and Heisenberg instances are proved axiom-free;
the companion `voaPBWFreeness` supplies arbitrary parabolic instances from the generic
relative-induction field of the theorem `VOA.pbw : PBWPrinciple`. -/
theorem indBarBottom_injective_of_pbw (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hP : PBWFreeness (parabolicRepOfAMod W U))
    (h46 : BottomPropagates hP.bottomProjection) (h47 : OrbitPropagates hP.bottomProjection) :
    Function.Injective (indBarBottom (parabolicRepOfAMod W U)) :=
  indBarBottom_injective_of_prop43 W U hP.bottomProjection h46 h47

end DLM3
end VHat

end VOA

-- Axiom check. Explicit `PBWFreeness`/`BottomProjection` parameters are not printed.
