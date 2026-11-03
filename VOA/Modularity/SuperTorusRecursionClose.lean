/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperTorusRecursion
import VOA.Modularity.ZhuRecursionClose
import VOA.Modularity.SuperHalfSquareGrading
import VOA.Modularity.SuperTwistedTrace

/-!
# Closed integral super torus recursion

This file closes the signed geometric calculation begun in `SuperTorusRecursion`.  The
compensated pair in the exchanged half of the iterate carries one Koszul scalar.  Moving that
pair around the supertrace contributes the same scalar, so their product is one.  Consequently
the remaining coefficient identity is literally the bosonic scalar Lambert--Eisenstein
resummation; no parity sign survives in its input.

The result is deliberately confined to the integral identity sector.  The identity-twisted
expression from `SuperTwistedTrace` is identified with this same one-point map below, so no second
parity involution is inserted.  No twisted-sector or Type-II odd-trace recursion is claimed:
`TwistedQueerTraceData` currently represents only zero-mode blocks and does not supply the
displaced-mode products needed by the geometric telescope.
-/

namespace VOA

open Module (End)
open scoped BigOperators

set_option autoImplicit false

universe u v

variable {VType : Type u} [AddCommGroup VType] [Module ℂ VType]
variable {W : SuperVertexOperatorAlgebra VType}
variable {M : Type v} [AddCommGroup M] [Module ℂ M]

namespace SuperOrdVModule

/-! ## Linear traces and the compensated super pair -/

/-- The two-point term which survives at the conformal zero mode. -/
noncomputable def superTorusTwoPoint (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) (a b : VType) : FormalQSeries :=
  N.superGradedTraceOp (N.superOMod hW a * N.superOMod hW b)

/-- The graded trace of a global zero mode is the torus one-point function. -/
theorem superGradedTraceOp_superOMod (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) (a : VType) :
    N.superGradedTraceOp (N.superOMod hW a) = N.superTorusOnePoint hW a := rfl

/-- Evaluation at a fixed formal degree as a linear functional on module endomorphisms. -/
noncomputable def superGradedTraceAt (N : SuperOrdVModule W M) (e : ℂ) :
    End ℂ M →ₗ[ℂ] ℂ where
  toFun A := N.superGradedTraceOp A e
  map_add' A B := congrFun (N.superGradedTraceOp_add A B) e
  map_smul' c A := congrFun (N.superGradedTraceOp_smul c A) e

@[simp] theorem superGradedTraceAt_apply (N : SuperOrdVModule W M)
    (e : ℂ) (A : End ℂ M) :
    N.superGradedTraceAt e A = N.superGradedTraceOp A e := rfl

/-- Uniform vanishing below one depth, independent of the inserted endomorphism. -/
theorem exists_superGradedTraceOp_bound (N : SuperOrdVModule W M) (e : ℂ) :
    ∃ D : ℕ, ∀ (A : End ℂ M) (n : ℕ), D < n →
      N.superGradedTraceOp A (e - n) = 0 := by
  obtain ⟨B, hB⟩ := N.boundedBelow
  obtain ⟨D, hD⟩ := exists_nat_gt (e.re + (W.centralCharge / 24).re - B)
  refine ⟨D, fun A n hn => N.superGradedTraceOp_eq_zero_of_weight_bot A _ ?_⟩
  by_contra hne
  have h := hB _ hne
  simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re] at h
  have hDn : (D : ℝ) < n := by exact_mod_cast hn
  linarith

/-- The compensated iterate pair.  The reversed branch contains the unique Koszul factor. -/
noncomputable def superPairOp (N : SuperOrdVModule W M) (a b : VType)
    (ka l r : ℤ) (p q : ZMod 2) : End ℂ M :=
  if r ≤ -1 then
    mode (N.YM a) r * mode (N.YM b) (ka + l - r - 2)
  else
    koszul p q • (mode (N.YM b) (ka + l - r - 2) * mode (N.YM a) r)

/-- The compensating supercommutator has finite state-mode support. -/
theorem superCompensatingSupportFinite (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) (a b : VType) (i : ℤ) :
    (Function.support fun r : ℤ =>
      cbz i r • N.superOMod hW (W.toSuperNearVOA.smul a r b)).Finite := by
  obtain ⟨R, hR⟩ := W.toSuperNearVOA.regularity a b
  refine Set.Finite.subset (Set.finite_Ico (0 : ℤ) R) (fun r hr => ?_)
  simp only [Function.mem_support, ne_eq] at hr
  simp only [Set.mem_Ico]
  refine ⟨?_, ?_⟩
  · by_contra hnonneg
    push Not at hnonneg
    exact hr (by rw [cbz_apply_neg i hnonneg, zero_smul])
  · by_contra hlt
    push Not at hlt
    exact hr (by
      rw [show W.toSuperNearVOA.smul a r b = 0 from hR r hlt, map_zero, smul_zero])

/-- Operator form of the compensated mode supercommutator. -/
theorem mode_compensating_supercommutator_op (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) {p q : ZMod 2} {ka l : ℤ}
    {a b : VType} (ha : a ∈ W.toSuperNearVOA.gradingZ ka)
    (hb : b ∈ W.toSuperNearVOA.gradingZ l)
    (hap : a ∈ W.parity p) (hbq : b ∈ W.parity q) (i : ℤ) :
    mode (N.YM a) i * mode (N.YM b) (ka + l - i - 2) -
        koszul p q • (mode (N.YM b) (ka + l - i - 2) * mode (N.YM a) i) =
      ∑ᶠ r : ℤ, cbz i r • N.superOMod hW (W.toSuperNearVOA.smul a r b) := by
  apply LinearMap.ext
  intro x
  change mode (N.YM a) i (mode (N.YM b) (ka + l - i - 2) x) -
      koszul p q • mode (N.YM b) (ka + l - i - 2) (mode (N.YM a) i x) = _
  rw [N.toSuperWeakModule.mode_supercommutator hap hbq x i (ka + l - i - 2)]
  change (∑ᶠ r : ℤ, cbz i r •
      mode (N.YM (W.toSuperNearVOA.smul a r b))
        (i + (ka + l - i - 2) - r) x) =
    (LinearMap.applyₗ x)
      (∑ᶠ r : ℤ, cbz i r • N.superOMod hW (W.toSuperNearVOA.smul a r b))
  rw [map_finsum (LinearMap.applyₗ x) (N.superCompensatingSupportFinite hW a b i)]
  refine finsum_congr (fun r => ?_)
  rw [map_smul]
  congr 1
  rw [N.superOMod_of_mem_gradingZ hW
    (W.toSuperNearVOA.smul_mem_gradingZ ha hb r)]
  congr 1
  ring

/-- The trace of the compensated supercommutator is a sum of honest one-point functions. -/
theorem superGradedTraceOp_compensating_supercommutator
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights)
    {p q : ZMod 2} {ka l : ℤ} {a b : VType}
    (ha : a ∈ W.toSuperNearVOA.gradingZ ka)
    (hb : b ∈ W.toSuperNearVOA.gradingZ l)
    (hap : a ∈ W.parity p) (hbq : b ∈ W.parity q) (i : ℤ) (e : ℂ) :
    N.superGradedTraceOp
      (mode (N.YM a) i * mode (N.YM b) (ka + l - i - 2) -
        koszul p q • (mode (N.YM b) (ka + l - i - 2) * mode (N.YM a) i)) e =
      ∑ᶠ r : ℤ, cbz i r *
        N.superTorusOnePoint hW (W.toSuperNearVOA.smul a r b) e := by
  rw [N.mode_compensating_supercommutator_op hW ha hb hap hbq i]
  have hmap := map_finsum (N.superGradedTraceAt e)
    (N.superCompensatingSupportFinite hW a b i)
  simpa only [superGradedTraceAt_apply, map_smul, smul_eq_mul,
    N.superGradedTraceOp_superOMod hW] using hmap

/-! ## Signed geometric solutions for the two orientations -/

/-- The standard orientation telescopes down.  The reversed commutator produced by cyclicity is
`-koszul` times the standard supercommutator, so the two Koszul factors leave the bosonic minus
sign. -/
theorem superGradedTraceOp_mode_pair_geomSolve
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights)
    {p q : ZMod 2} {ka l : ℤ} {a b : VType}
    (ha : a ∈ W.toSuperNearVOA.gradingZ ka)
    (hb : b ∈ W.toSuperNearVOA.gradingZ l)
    (hap : a ∈ W.parity p) (hbq : b ∈ W.parity q)
    (i : ℤ) (e : ℂ) (n : ℕ)
    (hvanish : N.superGradedTraceOp
      (mode (N.YM a) i * mode (N.YM b) (ka + l - i - 2))
        (e - (n : ℂ) * ((ka : ℂ) - (i : ℂ) - 1)) = 0) :
    N.superGradedTraceOp
      (mode (N.YM a) i * mode (N.YM b) (ka + l - i - 2)) e =
      -∑ j ∈ Finset.range n, ∑ᶠ r : ℤ, cbz i r *
        N.superTorusOnePoint hW (W.toSuperNearVOA.smul a r b)
          (e - ((j : ℂ) + 1) * ((ka : ℂ) - (i : ℂ) - 1)) := by
  let A := mode (N.YM b) (ka + l - i - 2)
  let B := mode (N.YM a) i
  let s : ℂ := (ka : ℂ) - (i : ℂ) - 1
  have hBw : N.SuperWeightShift B s := N.superWeightShift_mode ha i
  have hAw : N.SuperWeightShift A (-s) := by
    have h := N.superWeightShift_mode hb (ka + l - i - 2)
    rwa [show (l : ℂ) - ((ka + l - i - 2 : ℤ) : ℂ) - 1 = -s from by
      simp only [s]; push_cast; ring] at h
  have hBp : N.SuperParityDegree p B := N.superParityDegree_mode hap i
  have hAp : N.SuperParityDegree q A := N.superParityDegree_mode hbq (ka + l - i - 2)
  have hgeom := N.superGradedTraceOp_geomSolve A B s hAw hBw hAp hBp e n hvanish
  rw [hgeom, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have heps : koszul p q * koszul p q = 1 := koszul_mul_self p q
  have hrev : A * B - koszul p q • (B * A) =
      (-koszul p q) • (B * A - koszul p q • (A * B)) := by
    rw [smul_sub, smul_smul]
    have hcoef : (-koszul p q) * koszul p q = -1 := by
      rw [neg_mul, heps]
    rw [hcoef, neg_one_smul, neg_smul, sub_neg_eq_add]
    abel
  rw [show koszul q p = koszul p q from koszul_comm q p]
  rw [hrev, N.superGradedTraceOp_smul, Pi.smul_apply, smul_eq_mul,
    N.superGradedTraceOp_compensating_supercommutator hW ha hb hap hbq i]
  simp only [s]
  rw [← mul_assoc,
    show koszul p q * (-koszul p q) = -1 by rw [mul_neg, heps], neg_one_mul]

/-- In the reversed iterate branch its carried Koszul factor cancels the geometric cyclicity
factor, leaving a positive copy of the same commutator trace. -/
theorem superGradedTraceOp_reversed_compensated_geomSolve
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights)
    {p q : ZMod 2} {ka l : ℤ} {a b : VType}
    (ha : a ∈ W.toSuperNearVOA.gradingZ ka)
    (hb : b ∈ W.toSuperNearVOA.gradingZ l)
    (hap : a ∈ W.parity p) (hbq : b ∈ W.parity q)
    (i : ℤ) (e : ℂ) (n : ℕ)
    (hvanish : N.superGradedTraceOp
      (mode (N.YM b) (ka + l - i - 2) * mode (N.YM a) i)
        (e - (n : ℂ) * ((i : ℂ) - (ka : ℂ) + 1)) = 0) :
    N.superGradedTraceOp
      (koszul p q •
        (mode (N.YM b) (ka + l - i - 2) * mode (N.YM a) i)) e =
      ∑ j ∈ Finset.range n, ∑ᶠ r : ℤ, cbz i r *
        N.superTorusOnePoint hW (W.toSuperNearVOA.smul a r b)
          (e - ((j : ℂ) + 1) * ((i : ℂ) - (ka : ℂ) + 1)) := by
  let A := mode (N.YM a) i
  let B := mode (N.YM b) (ka + l - i - 2)
  let s : ℂ := (i : ℂ) - (ka : ℂ) + 1
  have hAw : N.SuperWeightShift A (-s) := by
    have h := N.superWeightShift_mode ha i
    rwa [show (ka : ℂ) - (i : ℂ) - 1 = -s from by simp only [s]; ring] at h
  have hBw : N.SuperWeightShift B s := by
    have h := N.superWeightShift_mode hb (ka + l - i - 2)
    rwa [show (l : ℂ) - ((ka + l - i - 2 : ℤ) : ℂ) - 1 = s from by
      simp only [s]; push_cast; ring] at h
  have hAp : N.SuperParityDegree p A := N.superParityDegree_mode hap i
  have hBp : N.SuperParityDegree q B := N.superParityDegree_mode hbq (ka + l - i - 2)
  have hgeom := N.superGradedTraceOp_geomSolve A B s hAw hBw hAp hBp e n hvanish
  rw [N.superGradedTraceOp_smul, Pi.smul_apply, smul_eq_mul, hgeom]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [N.superGradedTraceOp_compensating_supercommutator hW ha hb hap hbq i]
  simp only [s]
  rw [← mul_assoc, show koszul p q * koszul p q = 1 from koszul_mul_self p q,
    one_mul]

/-! ## The mode-pair expansion of the minus-one iterate -/

/-- A product whose right factor kills a weight space has zero graded supertrace there. -/
theorem superGradedTraceOp_mul_eq_zero_of_kills (N : SuperOrdVModule W M)
    (A B : End ℂ M) (e : ℂ)
    (hB : ∀ x ∈ N.weight (e + W.centralCharge / 24), B x = 0) :
    N.superGradedTraceOp (A * B) e = 0 := by
  haveI := N.weight_finite (e + W.centralCharge / 24)
  have hblk : N.superWeightBlock (A * B) (e + W.centralCharge / 24) = 0 := by
    refine LinearMap.ext (fun y => Subtype.ext ?_)
    change ((internalProjTo N.weight_isInternal _) (A (B (y : M))) : M) = _
    rw [hB (y : M) y.2, map_zero, map_zero]
    simp
  change supertrace (N.weightParityGrading _) (N.superWeightBlock (A * B) _) = 0
  rw [hblk]
  unfold supertrace
  rw [mul_zero, map_zero]

/-- Uniform truncation of a module field on one finite-dimensional super weight space. -/
theorem superMode_eventually_zero_on_weight (N : SuperOrdVModule W M)
    (u : VType) (α : ℂ) :
    ∃ N₀ : ℤ, ∀ m : ℤ, N₀ ≤ m → ∀ x ∈ N.weight α, mode (N.YM u) m x = 0 := by
  haveI := N.weight_finite α
  set b := Module.finBasis ℂ (N.weight α) with hb
  obtain ⟨N₀, hN₀⟩ := Finite.exists_le
    (fun i : Fin (Module.finrank ℂ (N.weight α)) =>
      (N.truncation u ((b i : N.weight α) : M)).choose)
  refine ⟨N₀, fun m hm x hx => ?_⟩
  have hxy : x = ∑ i, (b.repr ⟨x, hx⟩ i) • ((b i : N.weight α) : M) := by
    have h := congrArg (N.weight α).subtype (b.sum_repr ⟨x, hx⟩)
    rw [map_sum] at h
    simp only [map_smul] at h
    exact h.symm
  rw [hxy, map_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [map_smul,
    (N.truncation u ((b i : N.weight α) : M)).choose_spec m (le_trans (hN₀ i) hm),
    smul_zero]

/-- Pointwise signed iterate expansion into the two compensated mode families. -/
theorem superOMod_smul_neg_one_eq_finsum_superPairOp
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights)
    {p q : ZMod 2} {ka l : ℤ} {a b : VType}
    (ha : a ∈ W.toSuperNearVOA.gradingZ ka)
    (hb : b ∈ W.toSuperNearVOA.gradingZ l)
    (hap : a ∈ W.parity p) (hbq : b ∈ W.parity q) (x : M) :
    N.superOMod hW (W.toSuperNearVOA.smul a (-1) b) x =
      ∑ᶠ r : ℤ, N.superPairOp a b ka l r p q x := by
  rw [N.superOMod_smul_eq_iterate hW ha hb hap hbq (-1) x]
  have hw : ∀ j : ℤ, (negOnePow j * cbz (-1) j) •
      (mode (N.YM a) (-1 - j)
          (mode (N.YM b) (ka + l - (-1 - j) - 2) x)
        - (koszul p q * negOnePow (-1)) •
          mode (N.YM b) (ka + l - j - 2) (mode (N.YM a) j x)) =
      if 0 ≤ j then
        mode (N.YM a) (-1 - j)
            (mode (N.YM b) (ka + l - (-1 - j) - 2) x)
          + koszul p q •
            mode (N.YM b) (ka + l - j - 2) (mode (N.YM a) j x)
      else 0 := by
    intro j
    by_cases hj : 0 ≤ j
    · rw [if_pos hj, iterate_weight_neg_one hj, one_smul, negOnePow_neg_one,
        mul_neg_one, neg_smul, sub_neg_eq_add]
    · push Not at hj
      rw [if_neg (not_le.mpr hj), cbz_apply_neg _ hj, mul_zero, zero_smul]
  simp_rw [hw]
  obtain ⟨Nb, hNb⟩ := N.truncation b x
  obtain ⟨Na, hNa⟩ := N.truncation a x
  have hfinA : (Function.support fun j : ℕ =>
      mode (N.YM a) (-1 - j)
        (mode (N.YM b) (ka + l - (-1 - j) - 2) x)).Finite := by
    refine Set.Finite.subset (Set.finite_Iio (Nb - ka - l + 1).toNat) (fun j hj => ?_)
    simp only [Function.mem_support, ne_eq] at hj
    simp only [Set.mem_Iio]
    by_contra hc
    push Not at hc
    exact hj (by rw [hNb _ (by omega), map_zero])
  have hfinB : (Function.support fun j : ℕ =>
      koszul p q • mode (N.YM b) (ka + l - j - 2) (mode (N.YM a) j x)).Finite := by
    refine Set.Finite.subset (Set.finite_Iio Na.toNat) (fun j hj => ?_)
    simp only [Function.mem_support, ne_eq] at hj
    simp only [Set.mem_Iio]
    by_contra hc
    push Not at hc
    exact hj (by rw [hNa _ (by omega), map_zero, smul_zero])
  have hL : (∑ᶠ j : ℤ, if 0 ≤ j then
      mode (N.YM a) (-1 - j)
          (mode (N.YM b) (ka + l - (-1 - j) - 2) x)
        + koszul p q •
          mode (N.YM b) (ka + l - j - 2) (mode (N.YM a) j x)
      else 0) =
      ∑ᶠ j : ℕ, (
        mode (N.YM a) (-1 - (j : ℤ))
            (mode (N.YM b) (ka + l - (-1 - (j : ℤ)) - 2) x)
          + koszul p q •
            mode (N.YM b) (ka + l - (j : ℤ) - 2)
              (mode (N.YM a) (j : ℤ) x)) := by
    rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ Set.univ
      (Set.range (Nat.cast : ℕ → ℤ)) (fun j hj => ?_),
      finsum_mem_range Nat.cast_injective]
    · refine finsum_congr (fun j => ?_)
      rw [if_pos (by positivity)]
    · simp only [Set.mem_univ, Set.mem_range, true_iff]
      rw [Function.mem_support] at hj
      by_cases h0 : 0 ≤ j
      · exact ⟨j.toNat, by omega⟩
      · exact absurd (if_neg h0) hj
  rw [hL, finsum_add_distrib hfinA hfinB]
  have hfinR : (Function.support fun r : ℤ =>
      N.superPairOp a b ka l r p q x).Finite := by
    refine Set.Finite.subset
      (Set.finite_Icc (-(Nb - ka - l + 1).toNat - 1 : ℤ) Na.toNat) (fun r hr => ?_)
    simp only [Function.mem_support, ne_eq] at hr
    simp only [Set.mem_Icc]
    by_contra hc
    refine hr ?_
    rw [superPairOp]
    by_cases hr1 : r ≤ -1
    · rw [if_pos hr1]
      change mode (N.YM a) r (mode (N.YM b) (ka + l - r - 2) x) = 0
      rw [hNb _ (by omega), map_zero]
    · rw [if_neg hr1]
      change koszul p q •
        mode (N.YM b) (ka + l - r - 2) (mode (N.YM a) r x) = 0
      rw [hNa _ (by omega), map_zero, smul_zero]
  have hsplit := finsum_int_split_two
    (fun r => N.superPairOp a b ka l r p q x) hfinR
    (fun j : ℕ => (j : ℤ)) (fun j : ℕ => -1 - j)
    Nat.cast_injective (fun c d h => by simpa using h) ?_ ?_
  · rw [hsplit, add_comm]
    congr 1
    · refine finsum_congr (fun j => ?_)
      show _ = N.superPairOp a b ka l (j : ℤ) p q x
      rw [superPairOp, if_neg (by omega)]
      rfl
    · refine finsum_congr (fun j => ?_)
      show _ = N.superPairOp a b ka l (-1 - (j : ℤ)) p q x
      rw [superPairOp, if_pos (by omega)]
      rfl
  · rw [Set.disjoint_left]
    rintro r ⟨c, rfl⟩ ⟨d, hd⟩
    simp only at hd
    omega
  · refine Set.eq_univ_of_forall (fun r => ?_)
    by_cases hr : 0 ≤ r
    · exact Or.inl ⟨r.toNat, by simp; omega⟩
    · exact Or.inr ⟨(-1 - r).toNat, by simp; omega⟩

/-- The minus-one one-point coefficient is the finite sum of compensated pair traces. -/
theorem superTorusOnePoint_smul_neg_one_eq_finsum_superPairOp
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights)
    {p q : ZMod 2} {ka l : ℤ} {a b : VType}
    (ha : a ∈ W.toSuperNearVOA.gradingZ ka)
    (hb : b ∈ W.toSuperNearVOA.gradingZ l)
    (hap : a ∈ W.parity p) (hbq : b ∈ W.parity q) (e : ℂ) :
    N.superTorusOnePoint hW (W.toSuperNearVOA.smul a (-1) b) e =
      ∑ᶠ r : ℤ, N.superGradedTraceOp (N.superPairOp a b ka l r p q) e := by
  set α : ℂ := e + W.centralCharge / 24 with hα
  obtain ⟨Nb, hNb⟩ := N.superMode_eventually_zero_on_weight b α
  obtain ⟨Na, hNa⟩ := N.superMode_eventually_zero_on_weight a α
  set lo : ℤ := min (-1) (ka + l - 2 - Nb) with hlo
  set hi : ℤ := max 0 Na with hhi
  have hkill : ∀ r : ℤ, ¬ (lo ≤ r ∧ r ≤ hi) →
      ∀ x ∈ N.weight α, N.superPairOp a b ka l r p q x = 0 := by
    intro r hr x hx
    rw [superPairOp]
    by_cases hr1 : r ≤ -1
    · rw [if_pos hr1]
      change mode (N.YM a) r (mode (N.YM b) (ka + l - r - 2) x) = 0
      rw [hNb _ (by omega) x hx, map_zero]
    · rw [if_neg hr1]
      change koszul p q •
        mode (N.YM b) (ka + l - r - 2) (mode (N.YM a) r x) = 0
      rw [hNa _ (by omega) x hx, map_zero, smul_zero]
  set Op : End ℂ M := ∑ r ∈ Finset.Icc lo hi, N.superPairOp a b ka l r p q with hOp
  have hagree : ∀ x ∈ N.weight α,
      N.superOMod hW (W.toSuperNearVOA.smul a (-1) b) x = Op x := by
    intro x hx
    rw [N.superOMod_smul_neg_one_eq_finsum_superPairOp hW ha hb hap hbq x,
      hOp, LinearMap.sum_apply]
    refine finsum_eq_sum_of_support_subset _ (fun r hr => ?_)
    simp only [Function.mem_support, ne_eq] at hr
    simp only [Finset.coe_Icc, Set.mem_Icc]
    by_contra hc
    exact hr (hkill r hc x hx)
  have hblk : N.superOModWeightBlock hW
      (W.toSuperNearVOA.smul a (-1) b) α = N.superWeightBlock Op α := by
    refine LinearMap.ext (fun y => Subtype.ext ?_)
    change ((internalProjTo N.weight_isInternal α)
        (N.superOMod hW (W.toSuperNearVOA.smul a (-1) b) (y : M)) : M) =
      ((internalProjTo N.weight_isInternal α) (Op (y : M)) : M)
    rw [hagree (y : M) y.2]
  have hlhs : N.superTorusOnePoint hW
      (W.toSuperNearVOA.smul a (-1) b) e = N.superGradedTraceOp Op e := by
    haveI := N.weight_finite α
    change supertrace (N.weightParityGrading α)
      (N.superOModWeightBlock hW (W.toSuperNearVOA.smul a (-1) b) α) =
      supertrace (N.weightParityGrading α) (N.superWeightBlock Op α)
    rw [hblk]
  rw [hlhs, hOp, ← N.superGradedTraceAt_apply, map_sum]
  simp only [N.superGradedTraceAt_apply]
  symm
  refine finsum_eq_sum_of_support_subset _ (fun r hr => ?_)
  simp only [Function.mem_support, ne_eq] at hr
  simp only [Finset.coe_Icc, Set.mem_Icc]
  by_contra hc
  refine hr ?_
  rw [superPairOp]
  by_cases hr1 : r ≤ -1
  · rw [if_pos hr1]
    exact N.superGradedTraceOp_mul_eq_zero_of_kills _ _ e
      (fun x hx => hNb _ (by omega) x hx)
  · rw [if_neg hr1]
    rw [N.superGradedTraceOp_smul, Pi.smul_apply, smul_eq_mul]
    rw [N.superGradedTraceOp_mul_eq_zero_of_kills _ _ e
      (fun x hx => hNa _ (by omega) x hx), mul_zero]

/-! ## Trace of one compensated pair -/

/-- Crossing the reversed branch through the supertrace contributes a second Koszul sign,
which cancels the sign already built into `superPairOp`. -/
theorem superGradedTraceOp_compensated_reversed_pair
    (N : SuperOrdVModule W M) {p q : ZMod 2} {ka l i : ℤ} {a b : VType}
    (ha : a ∈ W.toSuperNearVOA.gradingZ ka)
    (hb : b ∈ W.toSuperNearVOA.gradingZ l)
    (hap : a ∈ W.parity p) (hbq : b ∈ W.parity q) (e : ℂ) :
    N.superGradedTraceOp
        (koszul p q •
          (mode (N.YM b) (ka + l - i - 2) * mode (N.YM a) i)) e =
      N.superGradedTraceOp
        (mode (N.YM a) i * mode (N.YM b) (ka + l - i - 2))
          (e + ((ka : ℂ) - (i : ℂ) - 1)) := by
  let A := mode (N.YM b) (ka + l - i - 2)
  let B := mode (N.YM a) i
  let s : ℂ := (ka : ℂ) - (i : ℂ) - 1
  have hBw : N.SuperWeightShift B s := N.superWeightShift_mode ha i
  have hAw : N.SuperWeightShift A (-s) := by
    have h := N.superWeightShift_mode hb (ka + l - i - 2)
    rwa [show (l : ℂ) - ((ka + l - i - 2 : ℤ) : ℂ) - 1 = -s from by
      simp only [s]; push_cast; ring] at h
  have hBp : N.SuperParityDegree p B := N.superParityDegree_mode hap i
  have hAp : N.SuperParityDegree q A :=
    N.superParityDegree_mode hbq (ka + l - i - 2)
  rw [N.superGradedTraceOp_smul, Pi.smul_apply, smul_eq_mul,
    N.superGradedTraceOp_comm_shift A B s hAw hBw hAp hBp e,
    show koszul q p = koszul p q from koszul_comm q p, ← mul_assoc,
    show koszul p q * koszul p q = 1 from koszul_mul_self p q, one_mul]

/-- At the conformal zero-mode index the standard pair is the torus two-point term. -/
theorem superGradedTraceOp_mode_pair_eq_superTorusTwoPoint
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights)
    {ka l : ℤ} {a b : VType}
    (ha : a ∈ W.toSuperNearVOA.gradingZ ka)
    (hb : b ∈ W.toSuperNearVOA.gradingZ l) :
    N.superGradedTraceOp
      (mode (N.YM a) (ka - 1) * mode (N.YM b) (l - 1)) =
      N.superTorusTwoPoint hW a b := by
  rw [superTorusTwoPoint, N.superOMod_of_mem_gradingZ hW ha,
    N.superOMod_of_mem_gradingZ hW hb]

/-- The trace of `superPairOp` in all three mode regimes.  Its scalar output is exactly the
bosonic `commTraceZ` and `telescopeZ` expression because both possible super signs have already
cancelled in the operator layer. -/
theorem superGradedTraceOp_superPairOp_eq
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights)
    {p q : ZMod 2} {ka : ℕ} {l : ℤ} {a b : VType}
    (hk : 1 ≤ ka) (ha : a ∈ W.toSuperNearVOA.gradingZ (ka : ℤ))
    (hb : b ∈ W.toSuperNearVOA.gradingZ l)
    (hap : a ∈ W.parity p) (hbq : b ∈ W.parity q)
    (e : ℂ) (D : ℕ)
    (hD : ∀ (A : End ℂ M) (n : ℕ), D < n → N.superGradedTraceOp A (e - n) = 0)
    (i : ℤ) :
    N.superGradedTraceOp (N.superPairOp a b ka l i p q) e =
      (if i = (ka : ℤ) - 1 then N.superTorusTwoPoint hW a b e else 0)
        + (if 0 ≤ i ∧ i ≤ (ka : ℤ) - 2 then
            -(commTraceZ (fun r e' =>
              N.superTorusOnePoint hW (W.toSuperNearVOA.smul a r b) e') i e)
          else 0)
        + modeSgn ka i * telescopeZ
            (fun r e' => N.superTorusOnePoint hW
              (W.toSuperNearVOA.smul a r b) e') ka D e i := by
  set Z : ℤ → ℂ → ℂ := fun r e' =>
    N.superTorusOnePoint hW (W.toSuperNearVOA.smul a r b) e' with hZ
  have hCz : ∀ e' : ℂ, (∑ᶠ r : ℤ, cbz i r *
      N.superTorusOnePoint hW (W.toSuperNearVOA.smul a r b) e') =
      commTraceZ Z i e' := fun _ => rfl
  rcases lt_trichotomy i ((ka : ℤ) - 1) with hlt | heq | hgt
  · have hdist : ((modeDist ka i : ℕ) : ℂ) =
        (ka : ℂ) - (i : ℂ) - 1 := modeDist_cast_of_le hlt.le
    have hdpos : 1 ≤ modeDist ka i := modeDist_pos_of_ne hlt.ne
    rw [if_neg hlt.ne, zero_add, modeSgn, if_neg (not_lt.mpr hlt.le),
      if_pos hlt, neg_one_mul]
    have hstd : ∀ n : ℕ, D < n * modeDist ka i →
        N.superGradedTraceOp
          (mode (N.YM a) i * mode (N.YM b) ((ka : ℤ) + l - i - 2)) e =
          -∑ j ∈ Finset.range n, commTraceZ Z i
            (e - ((j : ℂ) + 1) * (modeDist ka i : ℂ)) := by
      intro n hn
      rw [N.superGradedTraceOp_mode_pair_geomSolve hW ha hb hap hbq i e n]
      · simp only [Int.cast_natCast, hCz, hdist]
      · simp only [Int.cast_natCast]
        rw [show e - (n : ℂ) * ((ka : ℂ) - (i : ℂ) - 1) =
            e - ((n * modeDist ka i : ℕ) : ℂ) from by
          rw [Nat.cast_mul, hdist]]
        exact hD _ _ hn
    by_cases hi0 : 0 ≤ i
    · rw [if_pos ⟨hi0, by omega⟩, superPairOp, if_neg (by omega),
        N.superGradedTraceOp_compensated_reversed_pair ha hb hap hbq e]
      simp only [Int.cast_natCast]
      have hstd' : ∀ n : ℕ, D < n * modeDist ka i →
          N.superGradedTraceOp
            (mode (N.YM a) i * mode (N.YM b) ((ka : ℤ) + l - i - 2))
              (e + ((ka : ℂ) - (i : ℂ) - 1)) =
            -∑ j ∈ Finset.range (n + 1), commTraceZ Z i
              (e - (j : ℂ) * (modeDist ka i : ℂ)) := by
        intro n hn
        rw [N.superGradedTraceOp_mode_pair_geomSolve hW ha hb hap hbq i _ (n + 1)]
        · simp only [Int.cast_natCast, hCz, hdist]
          congr 1
          refine Finset.sum_congr rfl (fun j _ => ?_)
          congr 1
          ring
        · simp only [Int.cast_natCast]
          rw [show e + ((ka : ℂ) - (i : ℂ) - 1) -
              ((n + 1 : ℕ) : ℂ) * ((ka : ℂ) - (i : ℂ) - 1) =
              e - ((n * modeDist ka i : ℕ) : ℂ) from by
            rw [Nat.cast_mul, hdist]; push_cast; ring]
          exact hD _ _ hn
      rw [hstd' (D + 1) (by nlinarith), Finset.sum_range_succ', telescopeZ, hZ]
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, sub_zero]
      rw [neg_add, add_comm]
    · push Not at hi0
      rw [if_neg (fun h => absurd h.1 (not_le.mpr hi0)), zero_add,
        superPairOp, if_pos (by omega), hstd (D + 1) (by nlinarith), telescopeZ]
  · subst heq
    rw [if_pos rfl, if_neg (fun h => by omega), add_zero, modeSgn_self,
      zero_mul, add_zero, superPairOp, if_neg (by omega),
      N.superGradedTraceOp_compensated_reversed_pair ha hb hap hbq e,
      show ((ka : ℤ) + l - ((ka : ℤ) - 1) - 2) = l - 1 by ring,
      N.superGradedTraceOp_mode_pair_eq_superTorusTwoPoint hW ha hb]
    congr 1
    push_cast
    ring
  · have hdist : ((modeDist ka i : ℕ) : ℂ) =
        (i : ℂ) - (ka : ℂ) + 1 := modeDist_cast_of_ge hgt.le
    have hdpos : 1 ≤ modeDist ka i := modeDist_pos_of_ne hgt.ne'
    rw [if_neg hgt.ne', zero_add, if_neg (fun h => by omega), zero_add,
      modeSgn, if_pos hgt, one_mul, superPairOp, if_neg (by omega),
      N.superGradedTraceOp_reversed_compensated_geomSolve hW ha hb hap hbq i e (D + 1)]
    · rw [telescopeZ, hZ]
      simp only [Int.cast_natCast]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hdist]
      exact hCz _
    · simp only [Int.cast_natCast]
      rw [show e - ((D + 1 : ℕ) : ℂ) *
            ((i : ℂ) - (ka : ℂ) + 1) =
          e - (((D + 1) * modeDist ka i : ℕ) : ℂ) from by
        rw [Nat.cast_mul, hdist]]
      exact hD _ _ (by nlinarith)

/-! ## The closed super Zhu recursion -/

/-- Zhu's pinned integral recursion for the untwisted supertrace sector.  The coefficient
family is the same `zhuG` as in the bosonic theorem; parity has already been discharged in the
operator calculation above. -/
def SuperZhuRecursionPinned (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) (a b : VType) (ka : ℕ) : Prop :=
  N.superTorusOnePoint hW (W.toSuperNearVOA.superVSqZ a ka (-1) b) =
    N.superTorusTwoPoint hW a b +
      ∑ᶠ m : ℕ, qConv (zhuG (m + 1))
        (N.superTorusOnePoint hW
          (W.toSuperNearVOA.superVSqZ a ka (2 * (m + 1) - 1 : ℤ) b))

/-- Only finitely many square modes contribute to the pinned recursion tail. -/
theorem superZhuRecursion_support_finite (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) (a b : VType) (ka : ℕ) :
    (Function.support fun m : ℕ => qConv (zhuG (m + 1))
      (N.superTorusOnePoint hW
        (W.toSuperNearVOA.superVSqZ a ka (2 * (m + 1) - 1 : ℤ) b))).Finite := by
  obtain ⟨R, hR⟩ := W.toSuperNearVOA.superVSqZ_eventually_zero a ka b
  refine Set.Finite.subset (Set.finite_Iio R.toNat) (fun m hm => ?_)
  simp only [Function.mem_support, ne_eq] at hm
  simp only [Set.mem_Iio]
  by_contra hc
  push Not at hc
  exact hm (by
    rw [hR (2 * (m + 1) - 1 : ℤ) (by omega), map_zero, qConv_zero_right])

/-- Expansion of a square-bracket insertion under the linear torus one-point map. -/
theorem superTorusOnePoint_superVSqZ_expand (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) (a b : VType)
    (k : ℕ) (m : ℤ) (e : ℂ) :
    N.superTorusOnePoint hW (W.toSuperNearVOA.superVSqZ a k m b) e =
      ∑ᶠ i : ℤ, sqBracketCoeffZ k m i *
        N.superTorusOnePoint hW (W.toSuperNearVOA.smul a i b) e := by
  let F : VType →ₗ[ℂ] ℂ := {
    toFun := fun u => N.superTorusOnePoint hW u e
    map_add' := fun u v => congrFun (map_add (N.superTorusOnePoint hW) u v) e
    map_smul' := fun c u => congrFun (map_smul (N.superTorusOnePoint hW) c u) e }
  have hmap := map_finsum F
    (W.toSuperNearVOA.superSqModeZ_support_finite a k m b)
  simpa only [F, W.toSuperNearVOA.superVSqZ_apply, map_smul, smul_eq_mul] using hmap

/-- Closed recursion for a pair which is homogeneous for both weight and parity. -/
theorem superZhuRecursionPinned_of_bihomogeneous
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights)
    {p q : ZMod 2} {ka : ℕ} (hk : 1 ≤ ka) {l : ℤ} {a b : VType}
    (ha : a ∈ W.toSuperNearVOA.gradingZ (ka : ℤ))
    (hb : b ∈ W.toSuperNearVOA.gradingZ l)
    (hap : a ∈ W.parity p) (hbq : b ∈ W.parity q) :
    N.SuperZhuRecursionPinned hW a b ka := by
  rw [SuperZhuRecursionPinned]
  funext e
  set Z : ℤ → ℂ → ℂ := fun r e' =>
    N.superTorusOnePoint hW (W.toSuperNearVOA.smul a r b) e' with hZ
  obtain ⟨D, hD⟩ := N.exists_superGradedTraceOp_bound e
  obtain ⟨R, hR⟩ := W.toSuperNearVOA.regularity a b
  have hL1 : N.superTorusOnePoint hW
      (W.toSuperNearVOA.superVSqZ a ka (-1) b) e =
      N.superTorusOnePoint hW (W.toSuperNearVOA.smul a (-1) b) e +
        ∑ᶠ r : ℤ,
          (if 0 ≤ r then sqBracketCoeffZ ka (-1) r * Z r e else 0) := by
    rw [N.superTorusOnePoint_superVSqZ_expand hW]
    have hsplit : ∀ i : ℤ,
        sqBracketCoeffZ ka (-1) i *
            N.superTorusOnePoint hW (W.toSuperNearVOA.smul a i b) e =
          (if i = -1 then
              N.superTorusOnePoint hW (W.toSuperNearVOA.smul a (-1) b) e else 0) +
            (if 0 ≤ i then sqBracketCoeffZ ka (-1) i * Z i e else 0) := by
      intro i
      rcases lt_trichotomy i (-1) with hi | hi | hi
      · rw [if_neg hi.ne, if_neg (by omega), sqBracketCoeffZ_of_lt ka hi,
          zero_mul, add_zero]
      · subst hi
        rw [if_pos rfl, if_neg (by norm_num), add_zero,
          sqBracketCoeffZ_neg_one_diag, one_mul]
      · rw [if_neg hi.ne', if_pos (by omega), zero_add]
    rw [finsum_congr hsplit, finsum_add_distrib,
      finsum_eq_single _ (-1 : ℤ) (fun i hi => if_neg hi), if_pos rfl]
    · refine Set.Finite.subset (Set.finite_singleton (-1 : ℤ)) (fun i hi => ?_)
      simp only [Function.mem_support, ne_eq] at hi
      simp only [Set.mem_singleton_iff]
      by_contra hc
      exact hi (if_neg hc)
    · refine Set.Finite.subset (Set.finite_Ico (0 : ℤ) R) (fun i hi => ?_)
      simp only [Function.mem_support, ne_eq] at hi
      simp only [Set.mem_Ico]
      constructor
      · by_contra hc
        exact hi (if_neg hc)
      · by_contra hc
        push Not at hc
        exact hi (by
          by_cases hi0 : 0 ≤ i
          · rw [if_pos hi0]
            change sqBracketCoeffZ ka (-1) i *
              N.superTorusOnePoint hW (W.toSuperNearVOA.smul a i b) e = 0
            rw [show W.toSuperNearVOA.smul a i b = 0 from hR i hc,
              map_zero, Pi.zero_apply, mul_zero]
          · rw [if_neg hi0])
  have hL2 : N.superTorusOnePoint hW
      (W.toSuperNearVOA.smul a (-1) b) e =
      N.superTorusTwoPoint hW a b e +
        ∑ᶠ i : ℤ,
          ((if 0 ≤ i ∧ i ≤ (ka : ℤ) - 2 then -(commTraceZ Z i e) else 0) +
            modeSgn ka i * telescopeZ Z ka D e i) := by
    rw [N.superTorusOnePoint_smul_neg_one_eq_finsum_superPairOp hW ha hb hap hbq e,
      finsum_congr
        (fun i => N.superGradedTraceOp_superPairOp_eq hW hk ha hb hap hbq e D hD i)]
    have hfin1 : (Function.support fun i : ℤ =>
        if i = (ka : ℤ) - 1 then N.superTorusTwoPoint hW a b e else 0).Finite := by
      refine Set.Finite.subset (Set.finite_singleton ((ka : ℤ) - 1)) (fun i hi => ?_)
      simp only [Function.mem_support, ne_eq] at hi
      simp only [Set.mem_singleton_iff]
      by_contra hc
      exact hi (if_neg hc)
    have hfin2 : (Function.support fun i : ℤ =>
        ((if 0 ≤ i ∧ i ≤ (ka : ℤ) - 2 then -(commTraceZ Z i e) else 0) +
          modeSgn ka i * telescopeZ Z ka D e i)).Finite := by
      refine Set.Finite.subset
        (Set.finite_Icc (-(D : ℤ) - ka) ((ka : ℤ) + D)) (fun i hi => ?_)
      simp only [Function.mem_support, ne_eq] at hi
      simp only [Set.mem_Icc]
      by_contra hc
      have hdist : D < modeDist ka i := by rw [modeDist]; omega
      have hDZ : ∀ r, ∀ n : ℕ, D < n → Z r (e - n) = 0 :=
        fun r n hn => hD _ n hn
      exact hi (by
        rw [telescopeZ_eq_zero_of_lt hDZ i hdist, mul_zero, add_zero,
          if_neg (fun h => by omega)])
    simp_rw [add_assoc]
    rw [finsum_add_distrib hfin1 hfin2,
      finsum_eq_single _ ((ka : ℤ) - 1) (fun i hi => if_neg hi), if_pos rfl]
  have hRZ : ∀ r, R ≤ r → ∀ e', Z r e' = 0 := by
    intro r hr e'
    change N.superTorusOnePoint hW (W.toSuperNearVOA.smul a r b) e' = 0
    rw [show W.toSuperNearVOA.smul a r b = 0 from hR r hr, map_zero, Pi.zero_apply]
  have hDZ : ∀ r, ∀ n : ℕ, D < n → Z r (e - n) = 0 :=
    fun r n hn => hD _ n hn
  have hvan : ∑ᶠ r : ℤ, sqBracketCoeffZ ka 0 r * Z r e = 0 := by
    have h := N.superTorusOnePoint_superVSqZ_zero_eq_zero hW ka hk ha b
    have h' := congrFun h e
    rw [N.superTorusOnePoint_superVSqZ_expand hW] at h'
    exact h'
  rw [hL1, hL2, add_assoc,
    zhu_abstract_assembly hk e R D hRZ hDZ hvan, Pi.add_apply,
    finsum_apply (N.superZhuRecursion_support_finite hW a b ka)]
  congr 1
  refine finsum_congr (fun m => ?_)
  rw [qConv]
  refine finsum_congr (fun n => ?_)
  rw [N.superTorusOnePoint_superVSqZ_expand hW]

/-! ### Removing the auxiliary parity and right-weight homogeneity -/

theorem superTorusTwoPoint_add_right (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) (a b c : VType) :
    N.superTorusTwoPoint hW a (b + c) =
      N.superTorusTwoPoint hW a b + N.superTorusTwoPoint hW a c := by
  rw [superTorusTwoPoint, superTorusTwoPoint, superTorusTwoPoint,
    map_add, mul_add, N.superGradedTraceOp_add]

theorem superTorusTwoPoint_zero_right (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) (a : VType) :
    N.superTorusTwoPoint hW a 0 = 0 := by
  rw [superTorusTwoPoint, map_zero, mul_zero]
  rw [← zero_smul ℂ (0 : End ℂ M), N.superGradedTraceOp_smul]
  simp

theorem superTorusTwoPoint_add_left (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) (a b c : VType) :
    N.superTorusTwoPoint hW (a + b) c =
      N.superTorusTwoPoint hW a c + N.superTorusTwoPoint hW b c := by
  rw [superTorusTwoPoint, superTorusTwoPoint, superTorusTwoPoint,
    map_add, add_mul, N.superGradedTraceOp_add]

theorem superTorusTwoPoint_zero_left (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) (b : VType) :
    N.superTorusTwoPoint hW 0 b = 0 := by
  rw [superTorusTwoPoint, map_zero, zero_mul]
  rw [← zero_smul ℂ (0 : End ℂ M), N.superGradedTraceOp_smul]
  simp

/-- The module lower bound gives the finiteness needed to distribute `qConv` over a sum. -/
theorem support_mul_superTorusOnePoint_shift_finite
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights)
    (u : VType) (e : ℂ) (f : ℕ → ℂ) :
    (Function.support fun n : ℕ =>
      f n * N.superTorusOnePoint hW u (e - n)).Finite := by
  obtain ⟨D, hD⟩ := N.exists_superGradedTraceOp_bound e
  refine Set.Finite.subset (Set.finite_Iic D) (fun n hn => ?_)
  simp only [Function.mem_support, ne_eq] at hn
  simp only [Set.mem_Iic]
  by_contra hc
  push Not at hc
  exact hn (by
    change f n * N.superGradedTraceOp (N.superOMod hW u) (e - n) = 0
    rw [hD _ n hc, mul_zero])

/-- The pinned recursion is additive in its right input. -/
theorem superZhuRecursionPinned_add_right
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights)
    (a b c : VType) (ka : ℕ)
    (hb : N.SuperZhuRecursionPinned hW a b ka)
    (hc : N.SuperZhuRecursionPinned hW a c ka) :
    N.SuperZhuRecursionPinned hW a (b + c) ka := by
  rw [SuperZhuRecursionPinned] at hb hc ⊢
  funext e
  have hb' := congrFun hb e
  have hc' := congrFun hc e
  rw [map_add, map_add, Pi.add_apply, hb', hc',
    N.superTorusTwoPoint_add_right hW]
  simp only [Pi.add_apply]
  rw [
    finsum_apply (N.superZhuRecursion_support_finite hW a (b + c) ka),
    finsum_apply (N.superZhuRecursion_support_finite hW a b ka),
    finsum_apply (N.superZhuRecursion_support_finite hW a c ka)]
  have hterm : ∀ m : ℕ,
      qConv (zhuG (m + 1))
          (N.superTorusOnePoint hW
            (W.toSuperNearVOA.superVSqZ a ka (2 * (m + 1) - 1 : ℤ) (b + c))) e =
        qConv (zhuG (m + 1))
            (N.superTorusOnePoint hW
              (W.toSuperNearVOA.superVSqZ a ka (2 * (m + 1) - 1 : ℤ) b)) e +
          qConv (zhuG (m + 1))
            (N.superTorusOnePoint hW
              (W.toSuperNearVOA.superVSqZ a ka (2 * (m + 1) - 1 : ℤ) c)) e := by
    intro m
    rw [map_add, map_add,
      qConv_add_apply _ _ _ e
        (N.support_mul_superTorusOnePoint_shift_finite hW _ e _)
        (N.support_mul_superTorusOnePoint_shift_finite hW _ e _)]
  rw [finsum_congr hterm, finsum_add_distrib]
  · ring
  · exact (N.superZhuRecursion_support_finite hW a b ka).subset (fun m hm => by
      simp only [Function.mem_support, ne_eq] at hm ⊢
      intro hz
      exact hm (by rw [hz]; rfl))
  · exact (N.superZhuRecursion_support_finite hW a c ka).subset (fun m hm => by
      simp only [Function.mem_support, ne_eq] at hm ⊢
      intro hz
      exact hm (by rw [hz]; rfl))

theorem superZhuRecursionPinned_zero_right
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights)
    (a : VType) (ka : ℕ) : N.SuperZhuRecursionPinned hW a 0 ka := by
  rw [SuperZhuRecursionPinned, map_zero, map_zero,
    N.superTorusTwoPoint_zero_right hW, zero_add]
  symm
  refine finsum_eq_zero_of_forall_eq_zero (fun m => ?_)
  rw [map_zero, map_zero, qConv_zero_right]

/-- The pinned recursion is additive in its left input when the declared weight is fixed. -/
theorem superZhuRecursionPinned_add_left
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights)
    (a b c : VType) (ka : ℕ)
    (ha : N.SuperZhuRecursionPinned hW a c ka)
    (hb : N.SuperZhuRecursionPinned hW b c ka) :
    N.SuperZhuRecursionPinned hW (a + b) c ka := by
  rw [SuperZhuRecursionPinned] at ha hb ⊢
  funext e
  have ha' := congrFun ha e
  have hb' := congrFun hb e
  rw [W.toSuperNearVOA.superVSqZ_add_left, map_add, Pi.add_apply, ha', hb',
    N.superTorusTwoPoint_add_left hW]
  simp only [Pi.add_apply]
  rw [
    finsum_apply (N.superZhuRecursion_support_finite hW (a + b) c ka),
    finsum_apply (N.superZhuRecursion_support_finite hW a c ka),
    finsum_apply (N.superZhuRecursion_support_finite hW b c ka)]
  have hterm : ∀ m : ℕ,
      qConv (zhuG (m + 1))
          (N.superTorusOnePoint hW
            (W.toSuperNearVOA.superVSqZ (a + b) ka (2 * (m + 1) - 1 : ℤ) c)) e =
        qConv (zhuG (m + 1))
            (N.superTorusOnePoint hW
              (W.toSuperNearVOA.superVSqZ a ka (2 * (m + 1) - 1 : ℤ) c)) e +
          qConv (zhuG (m + 1))
            (N.superTorusOnePoint hW
              (W.toSuperNearVOA.superVSqZ b ka (2 * (m + 1) - 1 : ℤ) c)) e := by
    intro m
    rw [W.toSuperNearVOA.superVSqZ_add_left, map_add,
      qConv_add_apply _ _ _ e
        (N.support_mul_superTorusOnePoint_shift_finite hW _ e _)
        (N.support_mul_superTorusOnePoint_shift_finite hW _ e _)]
  rw [finsum_congr hterm, finsum_add_distrib]
  · ring
  · exact (N.superZhuRecursion_support_finite hW a c ka).subset (fun m hm => by
      simp only [Function.mem_support, ne_eq] at hm ⊢
      intro hz
      exact hm (by rw [hz]; rfl))
  · exact (N.superZhuRecursion_support_finite hW b c ka).subset (fun m hm => by
      simp only [Function.mem_support, ne_eq] at hm ⊢
      intro hz
      exact hm (by rw [hz]; rfl))

theorem superZhuRecursionPinned_zero_left
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights)
    (b : VType) (ka : ℕ) : N.SuperZhuRecursionPinned hW 0 b ka := by
  rw [SuperZhuRecursionPinned, W.toSuperNearVOA.superVSqZ_zero_left,
    map_zero, N.superTorusTwoPoint_zero_left hW, zero_add]
  symm
  refine finsum_eq_zero_of_forall_eq_zero (fun m => ?_)
  rw [W.toSuperNearVOA.superVSqZ_zero_left, map_zero, qConv_zero_right]

/-- Closed integral super Zhu recursion with no parity hypothesis and no homogeneity hypothesis
on the right input. -/
theorem superZhuRecursionPinned_holds
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights)
    {ka : ℕ} (hk : 1 ≤ ka) {a : VType}
    (ha : a ∈ W.toSuperNearVOA.gradingZ (ka : ℤ)) (b : VType) :
    N.SuperZhuRecursionPinned hW a b ka := by
  classical
  let V := W.toSuperNearVOA
  obtain ⟨s, hs, _⟩ := V.exists_sum_parProj a
  have hcomp : ∀ p : ZMod 2,
      N.SuperZhuRecursionPinned hW (V.parProj p a) b ka := by
    intro p
    have hap : V.parProj p a ∈ V.parity p := V.parProj_mem p a
    have hak : V.parProj p a ∈ V.gradingZ (ka : ℤ) := V.parProj_mem_grading p ha
    exact V.reduce_bihomogeneous hW
      (P := fun x => N.SuperZhuRecursionPinned hW (V.parProj p a) x ka)
      (fun l q x hx => N.superZhuRecursionPinned_of_bihomogeneous hW hk
        hak hx.1 hap hx.2)
      (N.superZhuRecursionPinned_zero_right hW (V.parProj p a) ka)
      (fun x y hx hy => N.superZhuRecursionPinned_add_right hW _ _ _ ka hx hy) b
  have hsum : ∀ t : Finset (ZMod 2),
      N.SuperZhuRecursionPinned hW (∑ p ∈ t, V.parProj p a) b ka := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using N.superZhuRecursionPinned_zero_left hW b ka
    | @insert p t hp ih =>
        rw [Finset.sum_insert hp]
        exact N.superZhuRecursionPinned_add_left hW _ _ _ ka (hcomp p) ih
  rw [← hs]
  exact hsum s

/-! ## Square translation and the minus-two relation -/

/-- The global zero mode kills square translation.  This is the integral super analogue of
`o(L(-1)a + L(0)a)=0`; its proof uses module translation covariance and contains no parity
exchange. -/
theorem superOMod_L_translation_all
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights)
    (a : VType) :
    N.superOMod hW
      (W.toSuperNearVOA.L (-1) a + W.toSuperNearVOA.L 0 a) = 0 := by
  let V := W.toSuperNearVOA
  have hatop : a ∈ ⨆ k : ℤ, V.gradingZ k := by
    rw [(V.gradingZ_isInternal hW).submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction V.gradingZ
    (motive := fun x => N.superOMod hW (V.L (-1) x + V.L 0 x) = 0)
    hatop ?_ ?_ ?_
  · intro k x hx
    have hx' : x ∈ V.grading (k : ℂ) := hx
    have hL0 : V.L 0 x = (k : ℂ) • x := V.L0_eigenvalue hx'
    have hT : V.L (-1) x ∈ V.gradingZ (k + 1) := by
      change V.smul V.conformalVector 0 x ∈ V.grading ((k + 1 : ℤ) : ℂ)
      have h := V.smul_mem_grading V.conformal_mem hx' 0
      have hidx : (((k + 1 : ℤ) : ℂ)) = (2 : ℂ) + (k : ℂ) - 1 := by
        push_cast
        ring
      rw [hidx]
      simpa only [Int.cast_zero, sub_zero] using h
    rw [hL0, map_add, N.superOMod_of_mem_gradingZ hW hT,
      map_smul, N.superOMod_of_mem_gradingZ hW hx]
    apply LinearMap.ext
    intro y
    change N.toSuperWeakModule.act (W.L (-1) x) (k + 1 - 1) y +
      (k : ℂ) • N.toSuperWeakModule.act x (k - 1) y = 0
    rw [show k + 1 - 1 = k by ring,
      N.toSuperWeakModule.act_T_covariance x k y]
    module
  · simp only [map_zero, add_zero]
  · intro x y hx hy
    simp only [map_add]
    rw [show N.superOMod hW (V.L (-1) x) + N.superOMod hW (V.L (-1) y) +
          (N.superOMod hW (V.L 0 x) + N.superOMod hW (V.L 0 y)) =
        N.superOMod hW (V.L (-1) x + V.L 0 x) +
          N.superOMod hW (V.L (-1) y + V.L 0 y) by
            rw [map_add, map_add]
            abel,
      hx, hy, add_zero]

/-- Torus one-point supertraces vanish on square translations. -/
theorem superTorusOnePoint_superLsq_neg_one
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights)
    (x : VType) :
    N.superTorusOnePoint hW (W.toSuperNearVOA.superLsq (-1) x) = 0 := by
  rw [W.toSuperNearVOA.superLsq_neg_one, LinearMap.add_apply]
  change N.superGradedTraceOp
    (N.superOMod hW
      (W.toSuperNearVOA.L (-1) x + W.toSuperNearVOA.L 0 x)) = 0
  rw [N.superOMod_L_translation_all hW]
  funext e
  change N.superGradedTraceOp 0 e = 0
  rw [← zero_smul ℂ (0 : End ℂ M), N.superGradedTraceOp_smul]
  simp

/-- Square translation acts on an integral square mode by the usual sign-free derivation law. -/
theorem superLsq_neg_one_superVSqZ_comm
    {ka : ℕ} {a : VType}
    (ha : a ∈ W.toSuperNearVOA.gradingZ (ka : ℤ))
    (m : ℤ) (b : VType) :
    W.toSuperNearVOA.superLsq (-1)
        (W.toSuperNearVOA.superVSqZ a ka m b) -
      W.toSuperNearVOA.superVSqZ a ka m
        (W.toSuperNearVOA.superLsq (-1) b) =
      (-(m : ℂ)) • W.toSuperNearVOA.superVSqZ a ka (m - 1) b := by
  rw [← W.toSuperNearVOA.superVSqC_natCast a ka m,
    ← W.toSuperNearVOA.superVSqC_natCast a ka (m - 1)]
  exact W.toSuperNearVOA.superLsq_neg_one_superVSqC_comm ha m b

/-- The full Lambert--Eisenstein minus-two relation for the untwisted module supertrace. -/
theorem superZhuRecursion_neg_two
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights)
    {ka : ℕ} (hk : 1 ≤ ka) {a : VType}
    (ha : a ∈ W.toSuperNearVOA.gradingZ (ka : ℤ)) (b : VType) :
    N.superTorusOnePoint hW (W.toSuperNearVOA.superVSqZ a ka (-2) b) +
      ∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ) •
        qConv (zhuG (m + 1))
          (N.superTorusOnePoint hW
            (W.toSuperNearVOA.superVSqZ a ka (2 * (m + 1) - 2 : ℤ) b)) = 0 := by
  let V := W.toSuperNearVOA
  set w : VType := V.superLsq (-1) b with hw
  have hrec := N.superZhuRecursionPinned_holds hW hk ha w
  rw [SuperZhuRecursionPinned] at hrec
  have hL : V.superVSqZ a ka (-1) w =
      V.superLsq (-1) (V.superVSqZ a ka (-1) b) -
        V.superVSqZ a ka (-2) b := by
    have h := superLsq_neg_one_superVSqZ_comm (W := W) ha (-1) b
    rw [show (-1 : ℤ) - 1 = -2 by norm_num,
      show (-((-1 : ℤ) : ℂ)) = 1 by push_cast; ring, one_smul] at h
    rw [hw, ← h]
    abel
  have htwo : N.superTorusTwoPoint hW a w = 0 := by
    rw [superTorusTwoPoint, hw, V.superLsq_neg_one, LinearMap.add_apply,
      N.superOMod_L_translation_all hW, mul_zero]
    rw [← zero_smul ℂ (0 : End ℂ M), N.superGradedTraceOp_smul]
    simp
  have hLZ : N.superTorusOnePoint hW (V.superVSqZ a ka (-1) w) =
      -N.superTorusOnePoint hW (V.superVSqZ a ka (-2) b) := by
    rw [hL, map_sub, N.superTorusOnePoint_superLsq_neg_one hW,
      zero_sub]
  have htail : ∀ m : ℕ,
      N.superTorusOnePoint hW
          (V.superVSqZ a ka (2 * (m + 1) - 1 : ℤ) w) =
        ((2 * (m + 1) - 1 : ℕ) : ℂ) •
          N.superTorusOnePoint hW
            (V.superVSqZ a ka (2 * (m + 1) - 2 : ℤ) b) := by
    intro m
    have h := superLsq_neg_one_superVSqZ_comm (W := W) ha
      (2 * (m + 1) - 1 : ℤ) b
    rw [show (2 * (m + 1) - 1 - 1 : ℤ) = 2 * (m + 1) - 2 by ring,
      ← hw, sub_eq_iff_eq_add] at h
    have hc : (((2 * (m + 1) - 1 : ℕ) : ℂ)) =
        ((2 * (m + 1) - 1 : ℤ) : ℂ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * (m + 1))]
      ring
    have hidx : V.superVSqZ a ka (2 * (m + 1) - 1 : ℤ) w =
        V.superLsq (-1) (V.superVSqZ a ka (2 * (m + 1) - 1 : ℤ) b) +
          ((2 * (m + 1) - 1 : ℕ) : ℂ) •
            V.superVSqZ a ka (2 * (m + 1) - 2 : ℤ) b := by
      rw [hc, h, neg_smul]
      abel
    rw [hidx, map_add, map_smul,
      N.superTorusOnePoint_superLsq_neg_one hW, zero_add]
  rw [hLZ, htwo, zero_add] at hrec
  dsimp only [V] at htail hrec
  simp_rw [htail] at hrec
  simp_rw [qConv_smul_right] at hrec
  rw [neg_eq_iff_eq_neg] at hrec
  rw [hrec, neg_add_cancel]

/-! ## The even conformal-vector specialization -/

/-- Distinct weight components have zero projection, for the super ordinary-module grading. -/
theorem internalProjTo_superWeight_eq_zero_of_ne
    (N : SuperOrdVModule W M) {α β : ℂ} {x : M}
    (hx : x ∈ N.weight α) (hβ : β ≠ α) :
    internalProjTo N.weight_isInternal β x = 0 := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.weight_isInternal
  apply Subtype.ext
  have hdec := DirectSum.decompose_of_mem_ne N.weight hx (Ne.symm hβ)
  show ((DirectSum.component ℂ ℂ (fun j => N.weight j) β)
      (DirectSum.decomposeLinearEquiv N.weight x) : N.weight β) =
    ((0 : N.weight β) : M)
  rw [show DirectSum.decomposeLinearEquiv N.weight x =
      DirectSum.decompose N.weight x from rfl,
    ← DirectSum.apply_eq_component, hdec]
  rfl

/-- Left multiplication by module `L(0)` multiplies the degree-`e` supertrace coefficient by
`e+c/24`.  The parity involution causes no extra sign because `L(0)` is even and acts by a
scalar on each weight block. -/
theorem superGradedTraceOp_L0_mul
    (N : SuperOrdVModule W M) (A : End ℂ M) (e : ℂ) :
    N.superGradedTraceOp (mode (N.YM W.conformalVector) 1 * A) e =
      (e + W.centralCharge / 24) * N.superGradedTraceOp A e := by
  haveI := N.weight_finite (e + W.centralCharge / 24)
  set α := e + W.centralCharge / 24 with hα
  have hblk : N.superWeightBlock
      (mode (N.YM W.conformalVector) 1 * A) α =
      α • N.superWeightBlock A α := by
    refine LinearMap.ext (fun y => Subtype.ext ?_)
    change ((internalProjTo N.weight_isInternal α)
        (mode (N.YM W.conformalVector) 1 (A (y : M))) : M) =
      ((α • (internalProjTo N.weight_isInternal α) (A (y : M)) : N.weight α) : M)
    have hproj : ∀ x : M,
        internalProjTo N.weight_isInternal α
            (mode (N.YM W.conformalVector) 1 x) =
          α • internalProjTo N.weight_isInternal α x := by
      intro x
      classical
      letI := DirectSum.IsInternal.chooseDecomposition N.weight N.weight_isInternal
      have hdec := DirectSum.sum_support_decompose N.weight x
      conv_lhs => rw [← hdec]
      conv_rhs => rw [← hdec]
      rw [map_sum, map_sum, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun β _ => ?_)
      have hβ : ((DirectSum.decompose N.weight x β : N.weight β) : M) ∈ N.weight β :=
        (DirectSum.decompose N.weight x β).2
      rw [N.L0_weight β _ hβ, map_smul]
      by_cases hβα : β = α
      · subst hβα
        rfl
      · rw [N.internalProjTo_superWeight_eq_zero_of_ne hβ (Ne.symm hβα),
          smul_zero, smul_zero]
    rw [hproj]
  change supertrace (N.weightParityGrading α)
      (N.superWeightBlock (mode (N.YM W.conformalVector) 1 * A) α) =
    α * supertrace (N.weightParityGrading α) (N.superWeightBlock A α)
  rw [hblk, supertrace_smul]

/-- The global zero mode of the conformal vector is module `L(0)`. -/
theorem superOMod_conformalVector
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights) :
    N.superOMod hW W.conformalVector = mode (N.YM W.conformalVector) 1 := by
  have hω : W.conformalVector ∈ W.toSuperNearVOA.gradingZ 2 := W.conformal_mem
  rw [N.superOMod_of_mem_gradingZ hW hω]
  norm_num

/-- The omega recursion: the `c/24` shift in the square conformal vector cancels the shift in
the formal supercharacter exponent. -/
theorem superZhuRecursion_omega
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights)
    (b : VType) :
    N.superTorusOnePoint hW (W.toSuperNearVOA.superLsq (-2) b) =
      qDeriv (N.superTorusOnePoint hW b) +
        ∑ᶠ m : ℕ, qConv (zhuG (m + 1))
          (N.superTorusOnePoint hW
            (W.toSuperNearVOA.superLsq (2 * (m + 1) - 2 : ℤ) b)) := by
  have hrec := N.superZhuRecursionPinned_holds hW (ka := 2) (by norm_num)
    (show W.conformalVector ∈ W.toSuperNearVOA.gradingZ (2 : ℤ) from W.conformal_mem) b
  rw [SuperZhuRecursionPinned] at hrec
  have hm1 : W.toSuperNearVOA.superVSqZ W.conformalVector 2 (-1) b =
      W.toSuperNearVOA.superLsq (-2) b + (W.centralCharge / 24) • b := by
    rw [W.toSuperNearVOA.Lsq_apply, show (-2 : ℤ) + 1 = -1 by norm_num,
      sqBracketCoeffZ_vacuum_neg_one, mul_one]
    norm_num
    abel
  have hodd : ∀ m : ℕ,
      W.toSuperNearVOA.superVSqZ W.conformalVector 2 (2 * (m + 1) - 1 : ℤ) b =
        W.toSuperNearVOA.superLsq (2 * (m + 1) - 2 : ℤ) b := by
    intro m
    change W.toSuperNearVOA.superVSqZ W.toSuperNearVOA.conformalVector 2
        (2 * (m + 1) - 1 : ℤ) b = _
    rw [W.toSuperNearVOA.Lsq_apply,
      show (2 * (m + 1) - 2 : ℤ) + 1 = 2 * (m + 1) - 1 by ring,
      sqBracketCoeffZ_vacuum_of_ne _ (by omega), mul_zero, zero_smul, sub_zero]
  have htwo : N.superTorusTwoPoint hW W.conformalVector b =
      qDeriv (N.superTorusOnePoint hW b) +
        (W.centralCharge / 24) • N.superTorusOnePoint hW b := by
    funext e
    rw [superTorusTwoPoint, N.superOMod_conformalVector hW,
      N.superGradedTraceOp_L0_mul, Pi.add_apply, Pi.smul_apply, qDeriv, smul_eq_mul]
    rw [show N.superTorusOnePoint hW b =
        N.superGradedTraceOp (N.superOMod hW b) from rfl]
    ring
  rw [hm1, map_add, map_smul, htwo] at hrec
  simp_rw [hodd] at hrec
  funext e
  have h := congrFun hrec e
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [Pi.add_apply]
  linear_combination h

/-- The untwisted integral torus one-point supertrace is an honest formal super block. -/
theorem superTorusOnePoint_isSuperFormalBlock
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights) :
    SuperNearVOA.IsSuperFormalBlock W (N.superTorusOnePoint hW) := by
  constructor
  · intro hbase hsupp
    apply W.toSuperNearVOA.superBlockRelSpanG_le_ker hsupp
    exact {
      vanish := fun k hk _a ha b =>
        N.superTorusOnePoint_superVSqZ_zero_eq_zero hW k hk ha b
      negTwo := fun k hk _a ha b => N.superZhuRecursion_neg_two hW hk ha b }
  · exact fun b => N.superZhuRecursion_omega hW b

/-- The identity-twisted expression is the same integral formal super block.  The equality used
here is literal equality of the finite-block supertrace formulas; in particular it does not apply
the parity involution a second time. -/
theorem identityTwistedSuperOnePoint_isSuperFormalBlock
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights) :
    SuperNearVOA.IsSuperFormalBlock W
      (N.toIdentityTwist.twistedSuperOnePoint N.identityTwistedIntertwiner hW) := by
  rw [N.twistedSuperOnePoint_identity hW]
  exact N.superTorusOnePoint_isSuperFormalBlock hW

/-! ## The proved part of the identity-sector odd trace

The represented queer data is enough to transport the square-bracket-zero supercommutator into
`Queer` and apply odd-trace Koszul cyclicity.  It is not enough for the displaced mode products in
the minus-two telescope; no full odd formal-block assertion is made here.
-/

/-- The inverse block of the identity implementer is the identity. -/
@[simp] theorem identityTwistedIntertwiner_inverseWeightBlock
    (N : SuperOrdVModule W M) (α : ℂ) :
    N.identityTwistedIntertwiner.inverseWeightBlock α = 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- On a fixed weight block, the square-bracket-zero mode is the represented homogeneous
supercommutator. -/
theorem ordinaryZeroModeAction_superVSqZ_zero_bihomogeneous
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights)
    {p q : ZMod 2} {k : ℕ} {l : ℤ} {a b : VType} (hk : 1 ≤ k)
    (hak : a ∈ W.toSuperNearVOA.gradingZ (k : ℤ))
    (hbl : b ∈ W.toSuperNearVOA.gradingZ l)
    (hap : a ∈ W.parity p) (hbq : b ∈ W.parity q) (α : ℂ) :
    N.ordinaryZeroModeAction hW α (W.toSuperNearVOA.superVSqZ a k 0 b) =
      N.ordinaryZeroModeAction hW α a * N.ordinaryZeroModeAction hW α b -
        koszul p q •
          (N.ordinaryZeroModeAction hW α b * N.ordinaryZeroModeAction hW α a) := by
  have hop : N.superOMod hW (W.toSuperNearVOA.superVSqZ a k 0 b) =
      N.superOMod hW a * N.superOMod hW b -
        koszul p q • (N.superOMod hW b * N.superOMod hW a) := by
    apply LinearMap.ext
    intro x
    exact N.superOMod_superVSqZ_zero hW hk hak hbl hap hbq x
  have haW : ∀ x ∈ N.weight α, N.superOMod hW a x ∈ N.weight α :=
    fun _ hx => N.superOMod_mem_weight hW hak hx
  have hbW : ∀ x ∈ N.weight α, N.superOMod hW b x ∈ N.weight α :=
    fun _ hx => N.superOMod_mem_weight hW hbl hx
  change N.superOModWeightBlock hW (W.toSuperNearVOA.superVSqZ a k 0 b) α = _
  unfold superOModWeightBlock
  rw [hop]
  apply LinearMap.ext
  intro x
  change (internalProjTo N.weight_isInternal α)
      (((N.superOMod hW a * N.superOMod hW b) x) -
        koszul p q • ((N.superOMod hW b * N.superOMod hW a) x)) =
    (N.superOModWeightBlock hW a α * N.superOModWeightBlock hW b α) x -
      koszul p q •
        (N.superOModWeightBlock hW b α * N.superOModWeightBlock hW a α) x
  rw [map_sub, map_smul]
  have hab := congrArg (fun f : End ℂ (N.weight α) => f x)
    (N.superOModWeightBlock_mul hW (a := a) (b := b) hbW)
  have hba := congrArg (fun f : End ℂ (N.weight α) => f x)
    (N.superOModWeightBlock_mul hW (a := b) (b := a) haW)
  exact congrArg₂ (fun y z => y - koszul p q • z) hab hba

/-- A represented identity-sector odd trace kills every bihomogeneous square-bracket-zero
relation.  This is the exact odd-trace consequence available without displaced-mode queer data. -/
theorem identityTwistedInverseOddOnePoint_superVSqZ_zero_eq_zero_bihomogeneous
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights)
    (Θ : SuperTwistedModule.TwistedQueerTraceData
      N.toIdentityTwist N.identityTwistedIntertwiner hW)
    {p q : ZMod 2} {k : ℕ} {l : ℤ} {a b : VType} (hk : 1 ≤ k)
    (hak : a ∈ W.toSuperNearVOA.gradingZ (k : ℤ))
    (hbl : b ∈ W.toSuperNearVOA.gradingZ l)
    (hap : a ∈ W.parity p) (hbq : b ∈ W.parity q) :
    N.toIdentityTwist.twistedInverseOddOnePoint N.identityTwistedIntertwiner hW Θ
        (W.toSuperNearVOA.superVSqZ a k 0 b) = 0 := by
  funext e
  let α : ℂ := e + W.centralCharge / 24
  let R := Θ.block α
  let A := Θ.preimage α a
  let B := Θ.preimage α b
  let C := Θ.preimage α (W.toSuperNearVOA.superVSqZ a k 0 b)
  have hA : A ∈ Queer.parity p := Θ.preimage_parity α p (k : ℤ) a hak hap
  have hB : B ∈ Queer.parity q := Θ.preimage_parity α q l b hbl hbq
  have hC : C = A * B - koszul p q • (B * A) := by
    apply R.faithful
    rw [map_sub, map_smul, map_mul, map_mul]
    dsimp only [C, A, B, R]
    rw [Θ.represents, Θ.represents, Θ.represents,
      N.identityTwistedIntertwiner_inverseWeightBlock, one_mul,
      N.toIdentityTwist_twistedZeroModeAction]
    simpa only [one_mul] using
      N.ordinaryZeroModeAction_superVSqZ_zero_bihomogeneous
        hW hk hak hbl hap hbq α
  change Queer.oddTrace C = 0
  rw [hC, map_sub, map_smul, N.toIdentityTwist.twistedQueerRepresented_koszul_cyclic R hA hB]
  simp only [smul_eq_mul, sub_self]

end SuperOrdVModule

end VOA
