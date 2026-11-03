/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDLM3Survival
import VOA.Modules.ZhuVermaAnArchVhatDescent
import VOA.Modules.ZhuVermaAnArchZeroModeLaw

/-!
# The `L₋₁`-derivation law for the iterate defect, and two scalar/residue toolkits

This file collects the *representation-independent* machinery that DLM3's §4 induction (their
Lemma 4.5) runs on, plus the two small scalar toolkits it consumes.

## Main results

* `cbz_mul_sub` / `cbz_mul_index` — the two binomial absorption identities
  `C(ℓ,i)(ℓ−i) = ℓ·C(ℓ−1,i)` and `C(ℓ,i)·i = ℓ·C(ℓ−1,i−1)`.
* `resFull_pascal`, `resFull_zero_one`, `resFull_one_sum`, `zhuMul_eq_resFull_sum` — the Pascal
  recursion for the honest residue `Res_z (1+z)^E z^{−P} Y(u,z)v` and the resulting splitting
  `u ∗ v = u₍₋₁₎v + ∑_{i<wt u} Res_z (1+z)^i Y(u,z)v` of the Zhu product.  (This is the
  "hockey-stick" identity `∑_{i<k} C(i,ℓ) = C(k,ℓ+1)` in residue form; note the `ℓ = −1` column,
  where the two sides differ by exactly the head `u₍₋₁₎v`.)
* `zhuDeg0_bracket_gen_complement` — the class in `A(𝒱)` of `⁅a(m), b(k)⁆` for **any**
  degree-complementary pair, generalizing the proved diagonal case `zhuDeg0_bracket_gen_diag`.
* `VHatRep.defectVec_Lneg1_left` — **`δ(L₋₁a, b, x, ℓ, N) = −ℓ · δ(a, b, x, ℓ−1, N)`**, for every
  `V̂`-representation.  This is the engine of DLM3 Lemma 4.5: it moves the negative-pole index down
  by one at the cost of applying `L₋₁` to the left slot, so a single `ℓ = −1` statement propagates
  to all `ℓ < 0` by induction.
* `VHatRep.defectVec_vacuum_left` — the defect with `a = 𝟙` vanishes identically (VA2 on the
  representation, `VacuumCreation`).  This is what covers the weight-`0` slot `𝒱₀ = ℂ𝟙`.

Everything here is unconditional (no PBW, no bottom, no grading of the module) and sorry-free.

## References
DLM3 (`q-alg/9612010v2`) Lemma 4.4, Lemma 4.5, (4.9); Zhu Lemma 2.1;
`ZhuVermaAnArchMUjacobiClose` (`defectVec`), `ZhuVermaAnArchGradedCloseDeep` (linearity of
`defectVec`), `ZhuVermaAnArchDLM3Zero` (`zhuDeg0`, `zhuDeg0_bracket_gen_diag`),
`ZhuVermaAnArchResSkew` (`resFull`), `ZhuVermaAnArchVhatDescent` (`gBinom_succ_index`,
`gBinom_pred_index`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Casting helper -/

/-- `((i.toNat : ℕ) : ℂ) = (i : ℂ)` for `0 ≤ i`. -/
theorem toNat_cast_complex {i : ℤ} (hi : 0 ≤ i) : ((i.toNat : ℕ) : ℂ) = (i : ℂ) := by
  have h : ((i.toNat : ℕ) : ℤ) = i := Int.toNat_of_nonneg hi
  exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) h

/-- `C(ℓ,i)·(ℓ−i) = ℓ·C(ℓ−1,i)`. -/
theorem cbz_mul_sub (l i : ℤ) : cbz l i * ((l : ℂ) - (i : ℂ)) = (l : ℂ) * cbz (l - 1) i := by
  rcases lt_or_ge i 0 with hi | hi
  · rw [cbz_apply_neg l hi, cbz_apply_neg (l - 1) hi]; ring
  · rw [cbz_apply_nonneg l hi, cbz_apply_nonneg (l - 1) hi, ← toNat_cast_complex hi,
      VHat.gBinom_pred_index l i.toNat]
    ring

/-- `C(ℓ,i)·i = ℓ·C(ℓ−1,i−1)`. -/
theorem cbz_mul_index (l i : ℤ) : cbz l i * (i : ℂ) = (l : ℂ) * cbz (l - 1) (i - 1) := by
  rcases lt_or_ge i 0 with hi | hi
  · rw [cbz_apply_neg l hi, cbz_apply_neg (l - 1) (by omega)]; ring
  rcases eq_or_lt_of_le hi with hi0 | hi1
  · rw [← hi0, show ((0 : ℤ) - 1) = -1 by ring,
      cbz_apply_neg (l - 1) (by norm_num : (-1 : ℤ) < 0)]
    simp
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = (j : ℤ) + 1 := ⟨(i - 1).toNat, by omega⟩
    rw [cbz_apply_nonneg l (by omega), cbz_apply_nonneg (l - 1) (by omega),
      show ((j : ℤ) + 1).toNat = j + 1 by omega, show ((j : ℤ) + 1 - 1).toNat = j by omega]
    have h1 := VHat.gBinom_succ_index l j
    have h2 := VHat.gBinom_pred_index l j
    push_cast
    rw [h2, ← h1]
    ring



/-! ## resFull -/

/-- **Pascal for the honest residue**: `R(E,P) = R(E−1,P) + R(E−1,P−1)`. -/
theorem resFull_pascal (W : VertexOperatorAlgebra 𝒱) (E P : ℤ) (u v : 𝒱) :
    resFull W E P u v = resFull W (E - 1) P u v + resFull W (E - 1) (P - 1) u v := by
  rw [resFull, resFull, resFull,
    ← finsum_add_distrib (resFull_support_finite W (E - 1) P u v)
      (resFull_support_finite W (E - 1) (P - 1) u v)]
  refine finsum_congr fun l => ?_
  rw [← add_smul]
  congr 1
  rw [cbz_pascal E (l + P), show (l + P - 1 : ℤ) = l + (P - 1) from by ring]

/-- `Res_z (1+z)^0 z^{−1} Y(u,z)v = u₍₋₁₎v`. -/
theorem resFull_zero_one (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    resFull W 0 1 u v = W.smul u (-1) v := by
  rw [resFull]
  have hsingle : ∀ l : ℤ, l ≠ -1 → cbz 0 (l + 1) • W.smul u l v = 0 := by
    intro l hl
    rcases lt_or_ge (l + 1) 0 with h | h
    · rw [cbz_apply_neg 0 h, zero_smul]
    · have hpos : 0 < (l + 1).toNat := by omega
      rw [cbz_apply_nonneg 0 h,
        show (0 : ℤ) = ((0 : ℕ) : ℤ) from by norm_num,
        gBinom_natCast_eq_zero hpos, zero_smul]
  rw [finsum_eq_single _ (-1) hsingle]
  norm_num

/-- **The residue hockey stick**, in `resFull` form:
`Res_z (1+z)^n z^{−1} Y(u,z)v = u₍₋₁₎v + ∑_{i<n} Res_z (1+z)^i Y(u,z)v`. -/
theorem resFull_one_sum (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (n : ℕ) :
    resFull W (n : ℤ) 1 u v
      = W.smul u (-1) v + ∑ i ∈ Finset.range n, resFull W (i : ℤ) 0 u v := by
  induction n with
  | zero => rw [Nat.cast_zero, resFull_zero_one]; simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih,
      show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 from by push_cast; ring,
      resFull_pascal W ((n : ℤ) + 1) 1 u v]
    norm_num

/-- **The Zhu product, split off its `u₍₋₁₎v` head.** -/
theorem zhuMul_eq_resFull_sum (W : VertexOperatorAlgebra 𝒱) {kk : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (kk : ℤ)) (b : 𝒱) :
    zhuMul W a b = W.smul a (-1) b + ∑ i ∈ Finset.range kk, resFull W (i : ℤ) 0 a b := by
  have huv : zhuMul W a b = resFull W (kk : ℤ) 1 a b := by
    have h := resHom_eq_resFull (W := W) (K := kk) (s := 0) ha 1 b
    rw [Nat.cast_zero, add_zero, resHom_zero_one] at h
    exact h
  rw [huv, resFull_one_sum]

namespace VHat

/-- **Degree-complementary bracket.**  Generalizes `zhuDeg0_bracket_gen_diag` from the diagonal
`(m,k) = (wt a − 1, wt b − 1)` to every pair whose `V̂`-degrees are complementary. -/
theorem zhuDeg0_bracket_gen_complement (W : VertexOperatorAlgebra 𝒱) {wa wb m k : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading wa) (hb : b ∈ W.grading wb)
    (hd : wa - m - 1 + (wb - k - 1) = 0) :
    zhuDeg0 W (vhb W (gen W a m) (gen W b k))
      = _root_.VOA.mk W (resFull W m 0 a b) := by
  have hfin : (Function.support fun i : ℕ =>
      (gBinom m i) • W.smul a (i : ℤ) b).Finite := by
    obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a b
    refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
    intro i hi
    rw [Function.mem_support] at hi
    rw [Set.mem_Iio]
    by_contra hcon
    rw [not_lt] at hcon
    exact hi (by
      rw [hNz (i : ℤ) (le_trans (Int.self_le_toNat Nz) (by exact_mod_cast hcon)), smul_zero])
  rw [vhb_gen, map_finsum (zhuDeg0 W) (genOPE_support_finite W a b m k)]
  have hterm : ∀ i : ℕ,
      zhuDeg0 W ((gBinom m i) • gen W (W.smul a i b) (m + k - i))
        = _root_.VOA.mk W ((gBinom m i) • W.smul a (i : ℤ) b) := by
    intro i
    rw [map_smul, zhuDeg0_gen_deg_zero W (W.toPreVertexAlgebra.smul_mem_grading ha hb (i : ℤ))
      (by omega), map_smul]
  rw [finsum_congr hterm, ← map_finsum (_root_.VOA.mk W) hfin]
  congr 1
  rw [resFull]
  refine finsum_nat_to_int _ _ ?_ ?_
  · intro p hp
    have hc : cbz m (p + 0) = 0 := cbz_apply_neg _ (by omega)
    rw [hc, zero_smul]
  · intro j
    have hc : cbz m ((j : ℤ) + 0) = gBinom m j := by
      rw [show ((j : ℤ) + 0) = (j : ℤ) from by ring, cbz_apply_nonneg _ (by omega)]
      simp
    rw [hc]


namespace VHatRep

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **The `L₋₁` mode relation on a `V̂`-representation**: `(L₋₁a)₍ₘ₎ = −m·a₍ₘ₋₁₎`
(the relation `gen_Lneg1` of `V̂` pushed through `ρ`). -/
theorem actMode_Lneg1 (ρ : VHatRep W M) (a : 𝒱) (m : ℤ) :
    ρ.actMode (W.L (-1) a) m = (-(m : ℂ)) • ρ.actMode a (m - 1) := by
  rw [actMode_def, gen_Lneg1, map_smul, actMode_def]

/-- The "product" half of the defect family. -/
noncomputable def aterm (ρ : VHatRep W M) (a b : 𝒱) (x : M) (ℓ N i : ℤ) : M :=
  (negOnePow i * cbz ℓ i) • ρ.actMode a (ℓ - i) (ρ.actMode b (N + i) x)

/-- The "opposite" half of the defect family. -/
noncomputable def bterm (ρ : VHatRep W M) (a b : 𝒱) (x : M) (ℓ N i : ℤ) : M :=
  (negOnePow i * cbz ℓ i) • (negOnePow ℓ • ρ.actMode b (ℓ + N - i) (ρ.actMode a i x))

/-- The product half of the defect family has finite support. -/
theorem aterm_support_finite (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (a b : 𝒱) (x : M)
    (ℓ N : ℤ) : (Function.support (aterm ρ a b x ℓ N)).Finite := by
  obtain ⟨Nv, hNv⟩ := htr b x
  apply Set.Finite.subset (Set.finite_Icc 0 (Nv - N))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · simp only [aterm]; rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · simp only [aterm]; rw [hNv (N + i) (by omega), map_zero]; simp

/-- The opposite half of the defect family has finite support. -/
theorem bterm_support_finite (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (a b : 𝒱) (x : M)
    (ℓ N : ℤ) : (Function.support (bterm ρ a b x ℓ N)).Finite := by
  obtain ⟨Nu, hNu⟩ := htr a x
  apply Set.Finite.subset (Set.finite_Icc 0 Nu)
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · simp only [bterm]; rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · simp only [bterm]; rw [hNu i (by omega), map_zero]; simp

/-- `defectVec` split into its two halves. -/
theorem defectVec_eq_split (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (a b : 𝒱) (x : M)
    (ℓ N : ℤ) :
    defectVec ρ a b x ℓ N
      = ρ.actMode (W.smul a ℓ b) N x
        - (∑ᶠ i : ℤ, aterm ρ a b x ℓ N i) + ∑ᶠ i : ℤ, bterm ρ a b x ℓ N i := by
  rw [defectVec]
  have hcongr : ∀ i : ℤ,
      (negOnePow i * cbz ℓ i) •
        (ρ.actMode a (ℓ - i) (ρ.actMode b (N + i) x)
          - negOnePow ℓ • ρ.actMode b (ℓ + N - i) (ρ.actMode a i x))
      = aterm ρ a b x ℓ N i - bterm ρ a b x ℓ N i := by
    intro i; simp only [aterm, bterm, smul_sub]
  rw [finsum_congr hcongr,
    finsum_sub_distrib (aterm_support_finite ρ htr a b x ℓ N)
      (bterm_support_finite ρ htr a b x ℓ N)]
  abel


/-- The product half is a term-by-term `L₋₁`-derivation (absorption identity `cbz_mul_sub`). -/
theorem aterm_Lneg1 (ρ : VHatRep W M) (a b : 𝒱) (x : M) (ℓ N i : ℤ) :
    aterm ρ (W.L (-1) a) b x ℓ N i = (-(ℓ : ℂ)) • aterm ρ a b x (ℓ - 1) N i := by
  have hs : negOnePow i * cbz ℓ i * (-(((ℓ - i : ℤ)) : ℂ))
      = (-(ℓ : ℂ)) * (negOnePow i * cbz (ℓ - 1) i) := by
    have h := cbz_mul_sub ℓ i
    calc negOnePow i * cbz ℓ i * (-(((ℓ - i : ℤ)) : ℂ))
        = -negOnePow i * (cbz ℓ i * ((ℓ : ℂ) - (i : ℂ))) := by push_cast; ring
      _ = -negOnePow i * ((ℓ : ℂ) * cbz (ℓ - 1) i) := by rw [h]
      _ = (-(ℓ : ℂ)) * (negOnePow i * cbz (ℓ - 1) i) := by ring
  simp only [aterm, actMode_Lneg1, LinearMap.smul_apply, smul_smul, hs,
    show ℓ - i - 1 = ℓ - 1 - i from by ring]

/-- The opposite half is an `L₋₁`-derivation **after an index shift by one** (absorption
identity `cbz_mul_index`). -/
theorem bterm_Lneg1 (ρ : VHatRep W M) (a b : 𝒱) (x : M) (ℓ N i : ℤ) :
    bterm ρ (W.L (-1) a) b x ℓ N i = (-(ℓ : ℂ)) • bterm ρ a b x (ℓ - 1) N (i - 1) := by
  have hs : negOnePow i * cbz ℓ i * (negOnePow ℓ * (-(i : ℂ)))
      = (-(ℓ : ℂ)) * (negOnePow (i - 1) * cbz (ℓ - 1) (i - 1) * negOnePow (ℓ - 1)) := by
    have h := cbz_mul_index ℓ i
    rw [negOnePow_pred, negOnePow_pred]
    calc negOnePow i * cbz ℓ i * (negOnePow ℓ * (-(i : ℂ)))
        = -(negOnePow i * negOnePow ℓ) * (cbz ℓ i * (i : ℂ)) := by ring
      _ = -(negOnePow i * negOnePow ℓ) * ((ℓ : ℂ) * cbz (ℓ - 1) (i - 1)) := by rw [h]
      _ = (-(ℓ : ℂ)) * (-negOnePow i * cbz (ℓ - 1) (i - 1) * -negOnePow ℓ) := by ring
  simp only [bterm, actMode_Lneg1, LinearMap.smul_apply, map_smul, smul_smul, hs,
    show ℓ - 1 + N - (i - 1) = ℓ + N - i from by ring]


/-- Finiteness of the shifted opposite half. -/
theorem bterm_shift_support_finite (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (a b : 𝒱)
    (x : M) (ℓ N : ℤ) :
    (Function.support (fun i : ℤ => bterm ρ a b x (ℓ - 1) N (i - 1))).Finite := by
  obtain ⟨Nu, hNu⟩ := htr a x
  apply Set.Finite.subset (Set.finite_Icc 0 (Nu + 1))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · simp only [bterm]; rw [cbz_apply_neg (ℓ - 1) (by omega), mul_zero, zero_smul]
  · simp only [bterm]; rw [hNu (i - 1) (by omega), map_zero]; simp

/-- The shifted sum of the opposite half, reindexed. -/
theorem bterm_sum_Lneg1 (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (a b : 𝒱) (x : M)
    (ℓ N : ℤ) :
    (∑ᶠ i : ℤ, bterm ρ (W.L (-1) a) b x ℓ N i)
      = (-(ℓ : ℂ)) • ∑ᶠ i : ℤ, bterm ρ a b x (ℓ - 1) N i := by
  rw [finsum_congr (bterm_Lneg1 ρ a b x ℓ N),
    ← smul_finsum' (-(ℓ : ℂ)) (bterm_shift_support_finite ρ htr a b x ℓ N)]
  congr 1
  exact finsum_comp_equiv (Equiv.subRight (1 : ℤ))

/-- **DLM3 Lemma 4.5's engine**: the iterate defect is a `L₋₁`-derivation in its left slot. -/
theorem defectVec_Lneg1_left (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (a b : 𝒱) (x : M)
    (ℓ N : ℤ) :
    defectVec ρ (W.L (-1) a) b x ℓ N = (-(ℓ : ℂ)) • defectVec ρ a b x (ℓ - 1) N := by
  rw [defectVec_eq_split ρ htr (W.L (-1) a) b x ℓ N, defectVec_eq_split ρ htr a b x (ℓ - 1) N,
    W.smul_Lneg1_shift a b ℓ, actMode_smul_left, LinearMap.smul_apply,
    finsum_congr (aterm_Lneg1 ρ a b x ℓ N),
    ← smul_finsum' (-(ℓ : ℂ)) (aterm_support_finite ρ htr a b x (ℓ - 1) N),
    bterm_sum_Lneg1 ρ htr a b x ℓ N]
  rw [smul_add, smul_sub]


/-- **The vacuum defect vanishes**: `𝟙₍ₘ₎ = δ_{m,−1}` forces every iterate defect with `a = 𝟙`
to be zero, for every vector and every `(ℓ,N)`. -/
theorem defectVec_vacuum_left (ρ : VHatRep W M) (hvac : VacuumCreation ρ) (b : 𝒱) (x : M)
    (ℓ N : ℤ) : defectVec ρ W.vacuum b x ℓ N = 0 := by
  have hP2 : ∀ i : ℤ, 0 ≤ i → ρ.actMode b (ℓ + N - i) (ρ.actMode W.vacuum i x) = 0 := by
    intro i hi
    rw [hvac i, if_neg (by omega), LinearMap.zero_apply, map_zero]
  rw [defectVec]
  by_cases hl : ℓ = -1
  · subst hl
    rw [W.smul_vacuum_left, if_pos rfl]
    have hsingle : ∀ i : ℤ, i ≠ 0 →
        (negOnePow i * cbz (-1) i) •
          (ρ.actMode W.vacuum (-1 - i) (ρ.actMode b (N + i) x)
            - negOnePow (-1) • ρ.actMode b (-1 + N - i) (ρ.actMode W.vacuum i x)) = 0 := by
      intro i hi
      rcases lt_or_ge i 0 with h | h
      · rw [cbz_apply_neg (-1) h, mul_zero, zero_smul]
      · rw [hvac (-1 - i), if_neg (by omega), LinearMap.zero_apply, hP2 i h]
        simp
    rw [finsum_eq_single _ 0 hsingle]
    rw [hvac (-1 - 0), if_pos (by norm_num), hP2 0 le_rfl]
    simp [negOnePow]
  · have hzero : ∀ i : ℤ,
        (negOnePow i * cbz ℓ i) •
          (ρ.actMode W.vacuum (ℓ - i) (ρ.actMode b (N + i) x)
            - negOnePow ℓ • ρ.actMode b (ℓ + N - i) (ρ.actMode W.vacuum i x)) = 0 := by
      intro i
      rcases lt_or_ge i 0 with h | h
      · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
      by_cases hi : ℓ - i = -1
      · have hcz : cbz ℓ i = 0 := by
          have hii : i = ℓ + 1 := by omega
          rcases lt_or_ge ℓ 0 with hlneg | hlpos
          · exact cbz_apply_neg ℓ (by omega)
          · exact cbz_lt hlpos (by omega)
        rw [hcz, mul_zero, zero_smul]
      · rw [hvac (ℓ - i), if_neg hi, LinearMap.zero_apply, hP2 i h]
        simp
    rw [finsum_congr hzero, finsum_zero, W.smul_vacuum_left, if_neg hl, actMode_def,
      gen_zero_left, map_zero]
    simp

/-- The defect vanishes when the left `𝒱`-slot is `0`. -/
theorem defectVec_zero_left₁ (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (b : 𝒱) (x : M)
    (ℓ N : ℤ) : defectVec ρ 0 b x ℓ N = 0 := by
  have h := defectVec_smul_left₁ ρ htr (0 : ℂ) (0 : 𝒱) b x ℓ N
  rwa [smul_zero, zero_smul] at h

/-- The defect vanishes when the right `𝒱`-slot is `0`. -/
theorem defectVec_zero_left₂ (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (a : 𝒱) (x : M)
    (ℓ N : ℤ) : defectVec ρ a 0 x ℓ N = 0 := by
  have h := defectVec_smul_left₂ ρ htr (0 : ℂ) a (0 : 𝒱) x ℓ N
  rwa [smul_zero, zero_smul] at h

end VHatRep

end VHat

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
