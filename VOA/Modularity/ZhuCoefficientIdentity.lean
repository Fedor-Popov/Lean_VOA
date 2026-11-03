/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.ExpLogBinomial

/-!
# The coefficient identity behind Zhu's recursion  (Zhu Prop. 4.3.2, the combinatorial half)

The recursion `𝒵_M(a[−1]v) = tr o(a)o(v)q^{L₀−c/24} + Σ_k G_{2k} ⋆ 𝒵_M(a[2k−1]v)` is, after the
structural reductions of `ZhuAssembly`/`GradedTrace`, an identity between coefficient families
attached to the one-point functions `Z_r = 𝒵_M(a₍ᵣ₎v)`.  This file proves that identity in the
abstract: for an **arbitrary** family `Z : ℤ → (ℂ → ℂ)` that is eventually zero in `r` and
supported in bounded-below degrees, and satisfies the `a[0]`-vanishing `Σ_r c(k,0,r)Z_r(e) = 0`,

  `[telescoped pairs] + Σ_{r≥0} c(k,−1,r)Z_r(e) = Σ_m Σ_n G_{2m+2}(n)·Σ_r c(k,2m+1,r)Z_r(e−n)`.

The two inputs are the identities of `ExpLogBinomial`: (I3) matches the divisor tails
(`n ≥ 1`), and (I2) matches the constant term (`n = 0`) — up to `½Σ_r c(k,0,r)Z_r(e)`, which
is where the companion vanishing `𝒵_M(a[0]v) = 0` (`zhuVanishing_holds`) enters.

## Status
Proved, axiom-clean, `pbw`-free.  The VOA-side reduction feeding this identity is in
`ZhuRecursionClose`.
-/

namespace VOA

open scoped BigOperators

/-! ## `finsum` utilities -/

/-- Splitting a finitely supported sum over `ℤ` along two injective maps from `ℕ` with disjoint
ranges covering `ℤ`. -/
theorem finsum_int_split_two {α : Type*} [AddCommMonoid α] (f : ℤ → α)
    (hf : (Function.support f).Finite) (g₁ g₂ : ℕ → ℤ)
    (h₁ : Function.Injective g₁) (h₂ : Function.Injective g₂)
    (hdisj : Disjoint (Set.range g₁) (Set.range g₂))
    (hcover : Set.range g₁ ∪ Set.range g₂ = Set.univ) :
    ∑ᶠ p : ℤ, f p = (∑ᶠ d : ℕ, f (g₁ d)) + ∑ᶠ d : ℕ, f (g₂ d) := by
  rw [← finsum_mem_univ, ← hcover,
    finsum_mem_union' hdisj (hf.subset Set.inter_subset_right) (hf.subset Set.inter_subset_right),
    finsum_mem_range h₁, finsum_mem_range h₂]

/-- `Σᶠ_p f(p) = Σᶠ_d f(c+d) + Σᶠ_d f(c−1−d)`. -/
theorem finsum_int_split_at {α : Type*} [AddCommMonoid α] (f : ℤ → α)
    (hf : (Function.support f).Finite) (c : ℤ) :
    ∑ᶠ p : ℤ, f p = (∑ᶠ d : ℕ, f (c + d)) + ∑ᶠ d : ℕ, f (c - 1 - d) := by
  refine finsum_int_split_two f hf (fun d => c + d) (fun d => c - 1 - d) ?_ ?_ ?_ ?_
  · intro a b h; simpa using h
  · intro a b h; simpa using h
  · rw [Set.disjoint_left]
    rintro p ⟨a, rfl⟩ ⟨b, hb⟩
    simp only at hb
    omega
  · refine Set.eq_univ_of_forall (fun p => ?_)
    by_cases hp : c ≤ p
    · exact Or.inl ⟨(p - c).toNat, by simp; omega⟩
    · exact Or.inr ⟨(c - 1 - p).toNat, by simp; omega⟩

/-- `Σᶠ_n f(n) = f(0) + Σᶠ_n f(n+1)`. -/
theorem finsum_nat_succ {α : Type*} [AddCommMonoid α] (f : ℕ → α)
    (hf : (Function.support f).Finite) :
    ∑ᶠ n : ℕ, f n = f 0 + ∑ᶠ n : ℕ, f (n + 1) := by
  have hcover : ({0} : Set ℕ) ∪ Set.range Nat.succ = Set.univ := by
    refine Set.eq_univ_of_forall (fun n => ?_)
    rcases n with _ | m
    · exact Or.inl rfl
    · exact Or.inr ⟨m, rfl⟩
  have hdisj : Disjoint ({0} : Set ℕ) (Set.range Nat.succ) := by
    rw [Set.disjoint_left]
    rintro p hp ⟨a, ha⟩
    simp only [Set.mem_singleton_iff] at hp
    omega
  rw [← finsum_mem_univ, ← hcover,
    finsum_mem_union' hdisj (hf.subset Set.inter_subset_right) (hf.subset Set.inter_subset_right),
    finsum_mem_singleton, finsum_mem_range Nat.succ_injective]

/-- `Σᶠ_p f(p) = f(c) + Σᶠ_d f(c+1+d) + Σᶠ_d f(c−1−d)`: the three-way split of `ℤ` around `c`. -/
theorem finsum_int_split_three {α : Type*} [AddCommMonoid α] (f : ℤ → α)
    (hf : (Function.support f).Finite) (c : ℤ) :
    ∑ᶠ p : ℤ, f p = f c + (∑ᶠ d : ℕ, f (c + 1 + d)) + ∑ᶠ d : ℕ, f (c - 1 - d) := by
  rw [finsum_int_split_at f hf c, finsum_nat_succ (fun d => f (c + d))]
  · simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
    congr 2
    refine finsum_congr (fun d => ?_)
    congr 1; ring
  · refine (hf.preimage (f := fun d : ℕ => c + (d : ℤ)) ?_).subset ?_
    · intro a _ b _ h; simpa using h
    · intro d hd; exact hd

/-- Shifting a sum over `ℕ × ℕ` that vanishes on the axes. -/
theorem finsum_prod_succ_succ (g : ℕ × ℕ → ℂ)
    (haxes : ∀ q : ℕ × ℕ, q.1 = 0 ∨ q.2 = 0 → g q = 0) :
    ∑ᶠ q : ℕ × ℕ, g q = ∑ᶠ q : ℕ × ℕ, g (q.1 + 1, q.2 + 1) := by
  have hinj : Function.Injective (fun q : ℕ × ℕ => (q.1 + 1, q.2 + 1)) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (by omega) (by omega)
  rw [← finsum_mem_range hinj, ← finsum_mem_univ]
  refine finsum_mem_inter_support_eq' g _ _ (fun q hq => ?_)
  simp only [Set.mem_univ, Set.mem_range, true_iff]
  rw [Function.mem_support] at hq
  rcases q with ⟨q1, q2⟩
  rcases q1 with _ | q1
  · exact absurd (haxes _ (Or.inl rfl)) hq
  rcases q2 with _ | q2
  · exact absurd (haxes _ (Or.inr rfl)) hq
  exact ⟨(q1, q2), rfl⟩

/-- Hockey stick for `cbz`: `Σ_{i<n} C(i,r) = C(n,r+1)` for `r ≥ 0`. -/
theorem sum_range_cbz_eq (n : ℕ) {r : ℤ} (hr : 0 ≤ r) :
    ∑ i ∈ Finset.range n, cbz (i : ℤ) r = cbz (n : ℤ) (r + 1) := by
  induction n with
  | zero =>
      rw [Finset.sum_range_zero, Nat.cast_zero, cbz_zero_left, if_neg (by omega)]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, Nat.cast_succ, cbz_pascal_up,
        show r + 1 - 1 = r from by ring]

/-! ## The coefficient identity, pointwise in `(r, n)` -/

/-- The divisor-tail coefficient `Φ′_r(n) = Σ_{(D,J)∈DA(n)} (C(k−1+D,r) − C(k−1−D,r))`. -/
noncomputable def zhuTailCoeff (ka : ℕ) (r : ℤ) (n : ℕ) : ℂ :=
  ∑ q ∈ n.divisorsAntidiagonal, (cbz ((ka : ℤ) - 1 + q.1) r - cbz ((ka : ℤ) - 1 - q.1) r)

@[simp] theorem zhuTailCoeff_zero (ka : ℕ) (r : ℤ) : zhuTailCoeff ka r 0 = 0 := by
  rw [zhuTailCoeff, Nat.divisorsAntidiagonal_zero, Finset.sum_empty]

theorem zhuTailCoeff_of_neg (ka : ℕ) {r : ℤ} (hr : r < 0) (n : ℕ) : zhuTailCoeff ka r n = 0 := by
  rw [zhuTailCoeff]
  refine Finset.sum_eq_zero (fun q _ => ?_)
  rw [cbz_apply_neg _ hr, cbz_apply_neg _ hr, sub_self]

/-- The constant-term coefficient `κ_r = [r ≥ 0]·(c(k,−1,r) − C(k−1,r+1))`. -/
noncomputable def zhuConstCoeff (ka : ℕ) (r : ℤ) : ℂ :=
  if 0 ≤ r then sqBracketCoeffZ ka (-1) r - cbz ((ka : ℤ) - 1) (r + 1) else 0

/-- The full "Zhu side" coefficient `Ψ_r(n)`: constant at `n = 0`, divisor tail for `n ≥ 1`. -/
noncomputable def zhuSideCoeff (ka : ℕ) (r : ℤ) (n : ℕ) : ℂ :=
  if n = 0 then zhuConstCoeff ka r else zhuTailCoeff ka r n

/-- `sqBracketCoeffZ` at the odd index `2(m+1)−1` versus `sqBracketCoeff (2m+1)`. -/
theorem sqBracketCoeffZ_odd_eq (ka : ℕ) (m : ℕ) (r : ℤ) :
    sqBracketCoeffZ ka (2 * (m + 1) - 1 : ℤ) r
      = if 0 ≤ r then sqBracketCoeff ka (2 * m + 1) r.toNat else 0 := by
  by_cases hr : 0 ≤ r
  · rw [if_pos hr]
    obtain ⟨r', rfl⟩ := Int.eq_ofNat_of_zero_le hr
    rw [Int.toNat_natCast, show (2 * (m + 1) - 1 : ℤ) = ((2 * m + 1 : ℕ) : ℤ) from by push_cast; ring,
      sqBracketCoeffZ_of_nonneg]
  · rw [if_neg hr, sqBracketCoeffZ_of_lt ka (by omega)]

/-- **The pointwise coefficient identity (C1)**:

  `Ψ_r(n) = Σᶠ_m G_{2m+2}(n)·c(k,2m+1,r) + [n=0]·½·c(k,0,r)`,

for every `r ∈ ℤ`, `n ∈ ℕ`.  At `n ≥ 1` this is (I3) summed over the divisors of `n`; at `n = 0`
it is (I2). -/
theorem zhuSideCoeff_eq {ka : ℕ} (hk : 1 ≤ ka) (r : ℤ) (n : ℕ) :
    zhuSideCoeff ka r n
      = (∑ᶠ m : ℕ, zhuG (m + 1) n * sqBracketCoeffZ ka (2 * (m + 1) - 1 : ℤ) r)
        + (if n = 0 then (1 / 2) * sqBracketCoeffZ ka 0 r else 0) := by
  by_cases hr : 0 ≤ r
  · obtain ⟨r', rfl⟩ := Int.eq_ofNat_of_zero_le hr
    simp only [sqBracketCoeffZ_odd_eq, if_pos hr, Int.toNat_natCast]
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, sqBracketCoeffZ_of_nonneg,
      sqBracketCoeff_zero ka r' hk]
    have hbin : ((ka - 1).choose r' : ℂ) = cbz ((ka : ℤ) - 1) (r' : ℤ) := by
      rw [show ((ka : ℤ) - 1) = ((ka - 1 : ℕ) : ℤ) from by omega, cbz_apply_nonneg _ (by positivity),
        Int.toNat_natCast, gBinom_natCast]
    rw [hbin]
    rcases n with _ | n
    · rw [zhuSideCoeff, if_pos rfl, if_pos rfl, zhuConstCoeff, if_pos hr]
      have h := sqBracketCoeffZ_neg_one_eq hk r'
      linear_combination h
    · rw [zhuSideCoeff, if_neg (Nat.succ_ne_zero n), if_neg (Nat.succ_ne_zero n), add_zero,
        zhuTailCoeff]
      have hfin : ∀ q ∈ (n + 1).divisorsAntidiagonal, (Function.support fun m : ℕ =>
          (2 * ((q.1 : ℤ) : ℂ) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℂ))
            * sqBracketCoeff ka (2 * m + 1) r').Finite := by
        intro q _
        refine Set.Finite.subset (Set.finite_Iio r') (fun m hm => ?_)
        simp only [Function.mem_support, ne_eq] at hm
        simp only [Set.mem_Iio]
        by_contra hc
        push_neg at hc
        exact hm (by rw [sqBracketCoeff_eq_zero_of_lt ka (by omega), mul_zero])
      rw [Finset.sum_congr rfl (fun q _ => (finsum_odd_pow_mul_sqBracketCoeff hk (q.1 : ℤ) r').symm),
        ← finsum_sum_comm _ _ hfin]
      refine finsum_congr (fun m => ?_)
      rw [zhuG_of_ne_zero _ (Nat.succ_ne_zero n), lambertCoeff, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [show 2 * (m + 1) - 1 = 2 * m + 1 from by omega]
      push_cast
      ring
  · push_neg at hr
    rw [zhuSideCoeff, zhuConstCoeff, if_neg (not_le.mpr hr), zhuTailCoeff_of_neg ka hr, ite_self,
      sqBracketCoeffZ_of_lt ka (by omega), mul_zero, ite_self, add_zero]
    refine (finsum_eq_zero_of_forall_eq_zero (fun m => ?_)).symm
    rw [sqBracketCoeffZ_of_lt ka (by omega), mul_zero]

/-! ## The abstract assembly

Everything below is about an **arbitrary** family `Z : ℤ → ℂ → ℂ` (to be instantiated by
`Z r e = 𝒵_M(a₍ᵣ₎v)(e)`), eventually zero in `r` and vanishing in degrees `e − n` for `n > D`. -/

section Abstract

variable (Z : ℤ → ℂ → ℂ)

/-- The commutator-trace combination `Σ_r C(p,r)·Z_r(e)` (the trace of `[a₍ₚ₎, v₍…₎]`). -/
noncomputable def commTraceZ (p : ℤ) (e : ℂ) : ℂ := ∑ᶠ r : ℤ, cbz p r * Z r e

/-- The distance `|p − (kₐ − 1)|` of a mode index from the zero-mode index. -/
def modeDist (ka : ℕ) (p : ℤ) : ℕ := (p - ((ka : ℤ) - 1)).natAbs

/-- The sign of `p − (kₐ − 1)` (`0` at the zero mode). -/
noncomputable def modeSgn (ka : ℕ) (p : ℤ) : ℂ :=
  if (ka : ℤ) - 1 < p then 1 else if p < (ka : ℤ) - 1 then -1 else 0

/-- The telescoped geometric tail `G_p = Σ_{j ≤ D} Cz(p)(e − (j+1)·|s_p|)`. -/
noncomputable def telescopeZ (ka D : ℕ) (e : ℂ) (p : ℤ) : ℂ :=
  ∑ j ∈ Finset.range (D + 1), commTraceZ Z p (e - ((j : ℂ) + 1) * (modeDist ka p : ℂ))

variable {Z}

theorem modeDist_add (ka : ℕ) (d : ℕ) : modeDist ka ((ka : ℤ) - 1 + 1 + d) = d + 1 := by
  rw [modeDist, show ((ka : ℤ) - 1 + 1 + d) - ((ka : ℤ) - 1) = ((d + 1 : ℕ) : ℤ) from by
    push_cast; ring, Int.natAbs_natCast]

theorem modeDist_sub (ka : ℕ) (d : ℕ) : modeDist ka ((ka : ℤ) - 1 - 1 - d) = d + 1 := by
  rw [modeDist, show ((ka : ℤ) - 1 - 1 - d) - ((ka : ℤ) - 1) = -((d + 1 : ℕ) : ℤ) from by
    push_cast; ring, Int.natAbs_neg, Int.natAbs_natCast]

theorem modeSgn_self (ka : ℕ) : modeSgn ka ((ka : ℤ) - 1) = 0 := by
  rw [modeSgn, if_neg (lt_irrefl _), if_neg (lt_irrefl _)]

theorem modeSgn_add (ka : ℕ) (d : ℕ) : modeSgn ka ((ka : ℤ) - 1 + 1 + d) = 1 := by
  rw [modeSgn, if_pos (by omega)]

theorem modeSgn_sub (ka : ℕ) (d : ℕ) : modeSgn ka ((ka : ℤ) - 1 - 1 - d) = -1 := by
  rw [modeSgn, if_neg (by omega), if_pos (by omega)]

section Hyps

variable {ka : ℕ} {e : ℂ} {R : ℤ} {D : ℕ}
variable (hR : ∀ r, R ≤ r → ∀ e', Z r e' = 0)
variable (hD : ∀ r, ∀ n : ℕ, D < n → Z r (e - n) = 0)

include hR in
/-- The commutator trace as a finite sum over `r ∈ [0, R)`. -/
theorem commTraceZ_eq_sum (p : ℤ) (e' : ℂ) :
    commTraceZ Z p e' = ∑ r ∈ Finset.Ico (0 : ℤ) R, cbz p r * Z r e' := by
  rw [commTraceZ]
  refine finsum_eq_sum_of_support_subset _ (fun r hr => ?_)
  simp only [Function.mem_support, ne_eq] at hr
  simp only [Finset.coe_Ico, Set.mem_Ico]
  refine ⟨?_, ?_⟩
  · by_contra hc; push_neg at hc
    exact hr (by rw [cbz_apply_neg _ hc, zero_mul])
  · by_contra hc; push_neg at hc
    exact hr (by rw [hR r hc, mul_zero])

include hD in
theorem commTraceZ_shift_eq_zero (p : ℤ) {n : ℕ} (hn : D < n) : commTraceZ Z p (e - n) = 0 := by
  rw [commTraceZ]
  exact finsum_eq_zero_of_forall_eq_zero (fun r => by rw [hD r n hn, mul_zero])

include hD in
/-- The telescoped tail vanishes once the mode is farther than `D` from the zero mode. -/
theorem telescopeZ_eq_zero_of_lt (p : ℤ) (hp : D < modeDist ka p) : telescopeZ Z ka D e p = 0 := by
  rw [telescopeZ]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [show e - ((j : ℂ) + 1) * (modeDist ka p : ℂ) = e - (((j + 1) * modeDist ka p : ℕ) : ℂ) from by
    push_cast; ring]
  exact commTraceZ_shift_eq_zero hD p (by nlinarith)

include hR hD in
/-- **Step 4 — the divisor regrouping.**  The signed sum of telescoped tails over all mode
indices `p` regroups, via `(p, j) ↦ (|s_p|, j+1) ↦ |s_p|·(j+1) = n`, into the divisor-tail
coefficients `zhuTailCoeff`. -/
theorem finsum_modeSgn_telescopeZ :
    ∑ᶠ p : ℤ, modeSgn ka p * telescopeZ Z ka D e p
      = ∑ᶠ n : ℕ, ∑ r ∈ Finset.Ico (0 : ℤ) R, zhuTailCoeff ka r n * Z r (e - n) := by
  -- the pair function `h(D', J') = (Cz(kₐ−1+D') − Cz(kₐ−1−D'))(e − D'J')`
  set h : ℕ × ℕ → ℂ := fun q =>
    (commTraceZ Z ((ka : ℤ) - 1 + q.1) (e - ((q.1 * q.2 : ℕ) : ℂ))
      - commTraceZ Z ((ka : ℤ) - 1 - q.1) (e - ((q.1 * q.2 : ℕ) : ℂ))) with hh
  set ht : ℕ × ℕ → ℂ := fun q => if q.1 = 0 ∨ q.2 = 0 then 0 else h q with hht
  have hsupp : (Function.support fun p : ℤ => modeSgn ka p * telescopeZ Z ka D e p).Finite := by
    refine Set.Finite.subset (Set.finite_Icc ((ka : ℤ) - 1 - D) ((ka : ℤ) - 1 + D)) (fun p hp => ?_)
    simp only [Function.mem_support, ne_eq] at hp
    simp only [Set.mem_Icc]
    by_contra hc
    have hdist : D < modeDist ka p := by rw [modeDist]; omega
    exact hp (by rw [telescopeZ_eq_zero_of_lt hD p hdist, mul_zero])
  -- three-way split around the zero mode
  rw [finsum_int_split_three _ hsupp ((ka : ℤ) - 1), modeSgn_self, zero_mul, zero_add]
  simp only [modeSgn_add, modeSgn_sub, one_mul, neg_one_mul]
  have hfin1 : (Function.support fun d : ℕ => telescopeZ Z ka D e ((ka : ℤ) - 1 + 1 + d)).Finite := by
    refine Set.Finite.subset (Set.finite_Iio D) (fun d hd => ?_)
    simp only [Function.mem_support, ne_eq] at hd
    simp only [Set.mem_Iio]
    by_contra hc; push_neg at hc
    exact hd (telescopeZ_eq_zero_of_lt hD _ (by rw [modeDist_add]; omega))
  have hfin2 : (Function.support fun d : ℕ => telescopeZ Z ka D e ((ka : ℤ) - 1 - 1 - d)).Finite := by
    refine Set.Finite.subset (Set.finite_Iio D) (fun d hd => ?_)
    simp only [Function.mem_support, ne_eq] at hd
    simp only [Set.mem_Iio]
    by_contra hc; push_neg at hc
    exact hd (telescopeZ_eq_zero_of_lt hD _ (by rw [modeDist_sub]; omega))
  rw [finsum_neg_distrib, ← sub_eq_add_neg, ← finsum_sub_distrib hfin1 hfin2]
  -- each `d`-slice is `Σᶠ_j h(d+1, j+1)`
  have hslice : ∀ d : ℕ, telescopeZ Z ka D e ((ka : ℤ) - 1 + 1 + d)
      - telescopeZ Z ka D e ((ka : ℤ) - 1 - 1 - d) = ∑ᶠ j : ℕ, h (d + 1, j + 1) := by
    intro d
    rw [telescopeZ, telescopeZ, modeDist_add, modeDist_sub, ← Finset.sum_sub_distrib]
    rw [finsum_eq_sum_of_support_subset (s := Finset.range (D + 1))]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hh]
      simp only
      rw [show ((ka : ℤ) - 1 + 1 + (d : ℤ)) = (ka : ℤ) - 1 + ((d + 1 : ℕ) : ℤ) from by push_cast; ring,
        show ((ka : ℤ) - 1 - 1 - (d : ℤ)) = (ka : ℤ) - 1 - ((d + 1 : ℕ) : ℤ) from by push_cast; ring,
        show ((j : ℂ) + 1) * ((d + 1 : ℕ) : ℂ) = (((d + 1) * (j + 1) : ℕ) : ℂ) from by push_cast; ring]
    · intro j hj
      simp only [Function.mem_support, ne_eq] at hj
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hc; push_neg at hc
      refine hj ?_
      rw [hh]
      simp only
      rw [commTraceZ_shift_eq_zero hD _ (by nlinarith), commTraceZ_shift_eq_zero hD _ (by nlinarith),
        sub_self]
  simp_rw [hslice]
  -- uncurry, shift, regroup by the product
  have hprod : (Function.support fun q : ℕ × ℕ => h (q.1 + 1, q.2 + 1)).Finite := by
    refine Set.Finite.subset ((Set.finite_Iio D).prod (Set.finite_Iio D)) (fun q hq => ?_)
    simp only [Function.mem_support, ne_eq] at hq
    simp only [Set.mem_prod, Set.mem_Iio]
    by_contra hc
    refine hq ?_
    rw [hh]
    simp only
    have hn : D < (q.1 + 1) * (q.2 + 1) := by
      rcases not_and_or.mp hc with h1 | h1 <;> push_neg at h1 <;> nlinarith
    rw [commTraceZ_shift_eq_zero hD _ hn, commTraceZ_shift_eq_zero hD _ hn, sub_self]
  rw [← finsum_curry _ hprod]
  have haxes : ∀ q : ℕ × ℕ, q.1 = 0 ∨ q.2 = 0 → ht q = 0 := fun q hq => by
    rw [hht]; simp only; rw [if_pos hq]
  have hshift : (fun q : ℕ × ℕ => h (q.1 + 1, q.2 + 1)) = fun q => ht (q.1 + 1, q.2 + 1) := by
    funext q
    rw [hht]
    simp only
    rw [if_neg (by omega)]
  rw [hshift, ← finsum_prod_succ_succ ht haxes]
  have hfin3 : (Function.support fun q : ℕ × ℕ => ht (q.1, q.2)).Finite := by
    refine Set.Finite.subset ((Set.finite_Iic D).prod (Set.finite_Iic D)) (fun q hq => ?_)
    simp only [Function.mem_support, ne_eq] at hq
    simp only [Set.mem_prod, Set.mem_Iic]
    rw [hht] at hq
    simp only at hq
    by_contra hc
    refine hq ?_
    by_cases h0 : q.1 = 0 ∨ q.2 = 0
    · rw [if_pos h0]
    · rw [if_neg h0]
      push_neg at h0
      have hn : D < q.1 * q.2 := by
        rcases not_and_or.mp hc with h1 | h1 <;> push_neg at h1
        · exact lt_of_lt_of_le h1 (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h0.2))
        · exact lt_of_lt_of_le h1 (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h0.1))
      rw [hh]
      simp only
      rw [commTraceZ_shift_eq_zero hD _ hn, commTraceZ_shift_eq_zero hD _ hn, sub_self]
  rw [show (∑ᶠ q : ℕ × ℕ, ht q) = ∑ᶠ q : ℕ × ℕ, (fun a b : ℕ => ht (a, b)) q.1 q.2 from rfl,
    finsum_prod_eq_finsum_divisorsAntidiagonal (fun a b => ht (a, b)) hfin3
      (fun a b hab => haxes (a, b) (by simpa using Nat.mul_eq_zero.mp hab))]
  refine finsum_congr (fun n => ?_)
  -- on `divisorsAntidiagonal n` neither coordinate vanishes and the product is `n`
  have hterm : ∀ q ∈ n.divisorsAntidiagonal, ht (q.1, q.2)
      = ∑ r ∈ Finset.Ico (0 : ℤ) R,
          (cbz ((ka : ℤ) - 1 + q.1) r - cbz ((ka : ℤ) - 1 - q.1) r) * Z r (e - n) := by
    intro q hq
    have hq' := Nat.mem_divisorsAntidiagonal.mp hq
    have h1 : q.1 ≠ 0 := by rintro h0; rw [h0, zero_mul] at hq'; exact hq'.2 hq'.1.symm
    have h2 : q.2 ≠ 0 := by rintro h0; rw [h0, mul_zero] at hq'; exact hq'.2 hq'.1.symm
    rw [hht]
    simp only
    rw [if_neg (not_or.mpr ⟨h1, h2⟩), hh]
    simp only
    rw [hq'.1, commTraceZ_eq_sum hR, commTraceZ_eq_sum hR, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [zhuTailCoeff, Finset.sum_mul]

include hR in
/-- The constant part `−Σ_{0≤p≤kₐ−2} Cz(p)(e)` as `−Σ_r C(kₐ−1,r+1)·Z_r(e)` (hockey stick). -/
theorem finsum_const_part (hk : 1 ≤ ka) :
    ∑ᶠ p : ℤ, (if 0 ≤ p ∧ p ≤ (ka : ℤ) - 2 then -(commTraceZ Z p e) else 0)
      = -∑ r ∈ Finset.Ico (0 : ℤ) R, cbz ((ka : ℤ) - 1) (r + 1) * Z r e := by
  have hsub : (Function.support fun p : ℤ =>
      (if 0 ≤ p ∧ p ≤ (ka : ℤ) - 2 then -(commTraceZ Z p e) else 0))
        ⊆ ((Finset.map (Nat.castEmbedding : ℕ ↪ ℤ) (Finset.range (ka - 1)) : Finset ℤ) : Set ℤ) := by
    intro p hp
    simp only [Function.mem_support, ne_eq] at hp
    by_cases hc : 0 ≤ p ∧ p ≤ (ka : ℤ) - 2
    · simp only [Finset.coe_map, Nat.castEmbedding_apply, Set.mem_image, Finset.mem_coe,
        Finset.mem_range]
      exact ⟨p.toNat, by omega, by omega⟩
    · exact absurd (if_neg hc) hp
  rw [finsum_eq_sum_of_support_subset _ hsub, Finset.sum_map]
  simp only [Nat.castEmbedding_apply]
  rw [Finset.sum_congr rfl (fun i hi => if_pos ⟨by positivity, by
      rw [Finset.mem_range] at hi; omega⟩)]
  simp_rw [commTraceZ_eq_sum hR, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  rw [Finset.mem_Ico] at hr
  rw [Finset.sum_neg_distrib, ← Finset.sum_mul, sum_range_cbz_eq (ka - 1) hr.1,
    show (((ka - 1 : ℕ)) : ℤ) = (ka : ℤ) - 1 from by omega]

end Hyps

/-- **The abstract assembly of Zhu's recursion.**  For any family `Z` that is eventually
zero in `r`, vanishes in degrees `e − n` for `n > D`, and satisfies the `a[0]`-vanishing
`Σ_r c(k,0,r)Z_r(e) = 0`:

  `[telescoped pairs] + Σ_{r≥0} c(k,−1,r)·Z_r(e)
     = Σᶠ_m Σᶠ_n G_{2m+2}(n) · Σ_r c(k,2m+1,r)·Z_r(e−n)`.

The right-hand side is exactly `Σ_m (G_{2m+2} ⋆ 𝒵_M(a[2m+1]v))(e)` once `Z_r = 𝒵_M(a₍ᵣ₎v)`. -/
theorem zhu_abstract_assembly {ka : ℕ} (hk : 1 ≤ ka) (e : ℂ) (R : ℤ) (D : ℕ)
    (hR : ∀ r, R ≤ r → ∀ e', Z r e' = 0)
    (hD : ∀ r, ∀ n : ℕ, D < n → Z r (e - n) = 0)
    (hvan : ∑ᶠ r : ℤ, sqBracketCoeffZ ka 0 r * Z r e = 0) :
    (∑ᶠ p : ℤ, ((if 0 ≤ p ∧ p ≤ (ka : ℤ) - 2 then -(commTraceZ Z p e) else 0)
        + modeSgn ka p * telescopeZ Z ka D e p))
      + (∑ᶠ r : ℤ, (if 0 ≤ r then sqBracketCoeffZ ka (-1) r * Z r e else 0))
    = ∑ᶠ m : ℕ, ∑ᶠ n : ℕ, zhuG (m + 1) n
        * ∑ᶠ r : ℤ, sqBracketCoeffZ ka (2 * (m + 1) - 1 : ℤ) r * Z r (e - n) := by
  -- the two pieces of the `p`-sum have finite support
  have hsupp1 : (Function.support fun p : ℤ =>
      (if 0 ≤ p ∧ p ≤ (ka : ℤ) - 2 then -(commTraceZ Z p e) else 0)).Finite := by
    refine Set.Finite.subset (Set.finite_Icc (0 : ℤ) ((ka : ℤ) - 2)) (fun p hp => ?_)
    simp only [Function.mem_support, ne_eq] at hp
    simp only [Set.mem_Icc]
    by_contra hc
    exact hp (if_neg hc)
  have hsupp2 : (Function.support fun p : ℤ => modeSgn ka p * telescopeZ Z ka D e p).Finite := by
    refine Set.Finite.subset (Set.finite_Icc ((ka : ℤ) - 1 - D) ((ka : ℤ) - 1 + D)) (fun p hp => ?_)
    simp only [Function.mem_support, ne_eq] at hp
    simp only [Set.mem_Icc]
    by_contra hc
    have hdist : D < modeDist ka p := by rw [modeDist]; omega
    exact hp (by rw [telescopeZ_eq_zero_of_lt hD p hdist, mul_zero])
  rw [finsum_add_distrib hsupp1 hsupp2, finsum_modeSgn_telescopeZ hR hD, finsum_const_part hR hk]
  -- the `c(k,−1,r)` sum as a finite sum
  have hlhs3 : (∑ᶠ r : ℤ, (if 0 ≤ r then sqBracketCoeffZ ka (-1) r * Z r e else 0))
      = ∑ r ∈ Finset.Ico (0 : ℤ) R, sqBracketCoeffZ ka (-1) r * Z r e := by
    rw [finsum_eq_sum_of_support_subset (s := Finset.Ico (0 : ℤ) R)]
    · refine Finset.sum_congr rfl (fun r hr => ?_)
      rw [Finset.mem_Ico] at hr
      rw [if_pos hr.1]
    · intro r hr
      simp only [Function.mem_support, ne_eq] at hr
      simp only [Finset.coe_Ico, Set.mem_Ico]
      refine ⟨?_, ?_⟩
      · by_contra hc; exact hr (if_neg hc)
      · by_contra hc; push_neg at hc
        exact hr (by rw [hR r hc, mul_zero, ite_self])
  rw [hlhs3]
  -- LHS as `Σᶠ_n S n` with the full Zhu-side coefficient
  set S : ℕ → ℂ := fun n => ∑ r ∈ Finset.Ico (0 : ℤ) R, zhuSideCoeff ka r n * Z r (e - n) with hS
  have hSfin : (Function.support S).Finite := by
    refine Set.Finite.subset (Set.finite_Iic D) (fun n hn => ?_)
    simp only [Function.mem_support, ne_eq] at hn
    simp only [Set.mem_Iic]
    by_contra hc; push_neg at hc
    exact hn (Finset.sum_eq_zero (fun r _ => by rw [hD r n hc, mul_zero]))
  have hTfin : (Function.support fun n : ℕ =>
      ∑ r ∈ Finset.Ico (0 : ℤ) R, zhuTailCoeff ka r n * Z r (e - n)).Finite := by
    refine Set.Finite.subset (Set.finite_Iic D) (fun n hn => ?_)
    simp only [Function.mem_support, ne_eq] at hn
    simp only [Set.mem_Iic]
    by_contra hc; push_neg at hc
    exact hn (Finset.sum_eq_zero (fun r _ => by rw [hD r n hc, mul_zero]))
  have hLHS : -(∑ r ∈ Finset.Ico (0 : ℤ) R, cbz ((ka : ℤ) - 1) (r + 1) * Z r e)
      + (∑ᶠ n : ℕ, ∑ r ∈ Finset.Ico (0 : ℤ) R, zhuTailCoeff ka r n * Z r (e - n))
      + ∑ r ∈ Finset.Ico (0 : ℤ) R, sqBracketCoeffZ ka (-1) r * Z r e = ∑ᶠ n : ℕ, S n := by
    rw [finsum_nat_succ S hSfin, finsum_nat_succ _ hTfin]
    simp only [Nat.cast_zero, sub_zero, zhuTailCoeff_zero, zero_mul, Finset.sum_const_zero,
      zero_add]
    have h0 : S 0 = ∑ r ∈ Finset.Ico (0 : ℤ) R,
        (sqBracketCoeffZ ka (-1) r - cbz ((ka : ℤ) - 1) (r + 1)) * Z r e := by
      rw [hS]
      simp only [Nat.cast_zero, sub_zero]
      refine Finset.sum_congr rfl (fun r hr => ?_)
      rw [Finset.mem_Ico] at hr
      rw [zhuSideCoeff, if_pos rfl, zhuConstCoeff, if_pos hr.1]
    have h1 : ∀ n : ℕ, S (n + 1) = ∑ r ∈ Finset.Ico (0 : ℤ) R,
        zhuTailCoeff ka r (n + 1) * Z r (e - ((n + 1 : ℕ) : ℂ)) := by
      intro n
      rw [hS]
      simp only
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [zhuSideCoeff, if_neg (Nat.succ_ne_zero n)]
    simp_rw [h1]
    rw [h0]
    have hsplit : ∑ r ∈ Finset.Ico (0 : ℤ) R,
        (sqBracketCoeffZ ka (-1) r - cbz ((ka : ℤ) - 1) (r + 1)) * Z r e
        = ∑ r ∈ Finset.Ico (0 : ℤ) R, sqBracketCoeffZ ka (-1) r * Z r e
          - ∑ r ∈ Finset.Ico (0 : ℤ) R, cbz ((ka : ℤ) - 1) (r + 1) * Z r e := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun r _ => by ring)
    rw [hsplit]
    ring
  rw [hLHS]
  -- RHS as a finite triple sum
  have hinner : ∀ m n : ℕ,
      (∑ᶠ r : ℤ, sqBracketCoeffZ ka (2 * (m + 1) - 1 : ℤ) r * Z r (e - n))
      = ∑ r ∈ Finset.Ico (0 : ℤ) R, sqBracketCoeffZ ka (2 * (m + 1) - 1 : ℤ) r * Z r (e - n) := by
    intro m n
    refine finsum_eq_sum_of_support_subset _ (fun r hr => ?_)
    simp only [Function.mem_support, ne_eq] at hr
    simp only [Finset.coe_Ico, Set.mem_Ico]
    refine ⟨?_, ?_⟩
    · by_contra hc; push_neg at hc
      exact hr (by rw [sqBracketCoeffZ_of_lt ka (by omega), zero_mul])
    · by_contra hc; push_neg at hc
      exact hr (by rw [hR r hc, mul_zero])
  simp_rw [hinner]
  have hn_eq : ∀ m : ℕ, (∑ᶠ n : ℕ, zhuG (m + 1) n
      * ∑ r ∈ Finset.Ico (0 : ℤ) R, sqBracketCoeffZ ka (2 * (m + 1) - 1 : ℤ) r * Z r (e - n))
      = ∑ n ∈ Finset.range (D + 1), zhuG (m + 1) n
          * ∑ r ∈ Finset.Ico (0 : ℤ) R, sqBracketCoeffZ ka (2 * (m + 1) - 1 : ℤ) r * Z r (e - n) := by
    intro m
    refine finsum_eq_sum_of_support_subset _ (fun n hn => ?_)
    simp only [Function.mem_support, ne_eq] at hn
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc; push_neg at hc
    exact hn (by rw [Finset.sum_eq_zero (fun r _ => by rw [hD r n (by omega), mul_zero]), mul_zero])
  simp_rw [hn_eq]
  have hm_eq : (∑ᶠ m : ℕ, ∑ n ∈ Finset.range (D + 1), zhuG (m + 1) n
      * ∑ r ∈ Finset.Ico (0 : ℤ) R, sqBracketCoeffZ ka (2 * (m + 1) - 1 : ℤ) r * Z r (e - n))
      = ∑ m ∈ Finset.range R.toNat, ∑ n ∈ Finset.range (D + 1), zhuG (m + 1) n
          * ∑ r ∈ Finset.Ico (0 : ℤ) R, sqBracketCoeffZ ka (2 * (m + 1) - 1 : ℤ) r * Z r (e - n) := by
    refine finsum_eq_sum_of_support_subset _ (fun m hm => ?_)
    simp only [Function.mem_support, ne_eq] at hm
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc; push_neg at hc
    refine hm (Finset.sum_eq_zero (fun n _ => ?_))
    rw [Finset.sum_eq_zero (fun r hr => ?_), mul_zero]
    rw [Finset.mem_Ico] at hr
    rw [sqBracketCoeffZ_of_lt ka (by omega), zero_mul]
  rw [hm_eq]
  -- swap to `Σ_n Σ_r (Σ_m …)·Z_r(e−n)`
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hswap : ∀ n ∈ Finset.range (D + 1),
      (∑ m ∈ Finset.range R.toNat, ∑ r ∈ Finset.Ico (0 : ℤ) R,
        zhuG (m + 1) n * (sqBracketCoeffZ ka (2 * (m + 1) - 1 : ℤ) r * Z r (e - n)))
      = ∑ r ∈ Finset.Ico (0 : ℤ) R, (∑ m ∈ Finset.range R.toNat,
          zhuG (m + 1) n * sqBracketCoeffZ ka (2 * (m + 1) - 1 : ℤ) r) * Z r (e - n) := by
    intro n _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  rw [Finset.sum_congr rfl hswap]
  -- the finite `m`-sum is the `finsum` of `zhuSideCoeff_eq`
  have hm_fin : ∀ n : ℕ, ∀ r ∈ Finset.Ico (0 : ℤ) R, (∑ m ∈ Finset.range R.toNat,
      zhuG (m + 1) n * sqBracketCoeffZ ka (2 * (m + 1) - 1 : ℤ) r)
      = ∑ᶠ m : ℕ, zhuG (m + 1) n * sqBracketCoeffZ ka (2 * (m + 1) - 1 : ℤ) r := by
    intro n r hr
    rw [Finset.mem_Ico] at hr
    symm
    refine finsum_eq_sum_of_support_subset _ (fun m hm => ?_)
    simp only [Function.mem_support, ne_eq] at hm
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc; push_neg at hc
    exact hm (by rw [sqBracketCoeffZ_of_lt ka (by omega), mul_zero])
  rw [Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun r hr => by rw [hm_fin n r hr]))]
  -- apply (C1) pointwise and separate the `½·c(k,0,r)` correction
  have hC1 : ∀ n : ℕ, ∀ r ∈ Finset.Ico (0 : ℤ) R,
      (∑ᶠ m : ℕ, zhuG (m + 1) n * sqBracketCoeffZ ka (2 * (m + 1) - 1 : ℤ) r)
      = zhuSideCoeff ka r n - (if n = 0 then (1 / 2) * sqBracketCoeffZ ka 0 r else 0) := by
    intro n r _
    rw [zhuSideCoeff_eq hk r n]
    ring
  rw [Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun r hr => by rw [hC1 n r hr]))]
  simp only [sub_mul, Finset.sum_sub_distrib]
  have hcorr : ∑ n ∈ Finset.range (D + 1), ∑ r ∈ Finset.Ico (0 : ℤ) R,
      (if n = 0 then (1 / 2) * sqBracketCoeffZ ka 0 r else 0) * Z r (e - n) = 0 := by
    rw [Finset.sum_eq_single 0]
    · simp only [if_true, Nat.cast_zero, sub_zero]
      have hv : ∑ r ∈ Finset.Ico (0 : ℤ) R, sqBracketCoeffZ ka 0 r * Z r e = 0 := by
        rw [← hvan]
        symm
        refine finsum_eq_sum_of_support_subset _ (fun r hr => ?_)
        simp only [Function.mem_support, ne_eq] at hr
        simp only [Finset.coe_Ico, Set.mem_Ico]
        refine ⟨?_, ?_⟩
        · by_contra hc; push_neg at hc
          exact hr (by rw [sqBracketCoeffZ_of_lt ka (by omega), zero_mul])
        · by_contra hc; push_neg at hc
          exact hr (by rw [hR r hc, mul_zero])
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, hv, mul_zero]
    · intro n _ hn
      exact Finset.sum_eq_zero (fun r _ => by rw [if_neg hn, zero_mul])
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos D)) h
  rw [hcorr, sub_zero]
  -- and the remaining finite `n`-sum is `Σᶠ_n S n`
  rw [hS]
  dsimp only
  refine finsum_eq_sum_of_support_subset _ (fun n hn => ?_)
  simp only [Function.mem_support, ne_eq] at hn
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc; push_neg at hc
  exact hn (Finset.sum_eq_zero (fun r _ => by rw [hD r n (by omega), mul_zero]))

end Abstract

end VOA
