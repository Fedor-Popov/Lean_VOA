/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.LocalSystem

/-!
# All integer products in a local system of fields

This is the algebraic first phase of Li's local-system construction.  It equips the weak
vertex operators `Fld M` with their vector-space operations and with the field `n`-th product
for every integer `n`:

* for `n >= 0`, the commutator residue `cCoeff n (bracketDist a b)`;
* for `n = -k-1`, the divided normal product `negProd a b k`.

A `LocalFieldSystem M` is then a vector subspace of fields containing the identity, pairwise
local, and closed under all these products.

This file deliberately does **not** construct a `BarePreVA` and does not assert a Jacobi identity.
That requires the field-product Borcherds theorem and belongs to the next phase.
-/

namespace VOA

open Module (End)

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-! ## The vector space of fields -/

namespace Fld

theorem isField_zero : IsField (0 : FormalDist (End ℂ M)) :=
  fun _ => ⟨0, fun _ _ => rfl⟩

theorem isField_add {a b : FormalDist (End ℂ M)} (ha : IsField a) (hb : IsField b) :
    IsField (a + b) := by
  intro x
  obtain ⟨A, hA⟩ := ha x
  obtain ⟨B, hB⟩ := hb x
  refine ⟨min A B, fun n hn => ?_⟩
  change a n x + b n x = 0
  rw [hA n (by omega), hB n (by omega), add_zero]

theorem isField_smul (c : ℂ) {a : FormalDist (End ℂ M)} (ha : IsField a) :
    IsField (c • a) := by
  intro x
  obtain ⟨A, hA⟩ := ha x
  refine ⟨A, fun n hn => ?_⟩
  change c • a n x = 0
  rw [hA n hn, smul_zero]

/-- The fields form a linear subspace of all endomorphism-valued distributions. -/
def submodule : Submodule ℂ (FormalDist (End ℂ M)) where
  carrier := {a | IsField a}
  zero_mem' := isField_zero
  add_mem' ha hb := isField_add ha hb
  smul_mem' c _ ha := isField_smul c ha

instance instAddCommGroup : AddCommGroup (Fld M) :=
  inferInstanceAs (AddCommGroup (submodule (M := M)))

instance instModule : Module ℂ (Fld M) :=
  inferInstanceAs (Module ℂ (submodule (M := M)))

@[simp] theorem zero_val : (0 : Fld M).1 = (0 : FormalDist (End ℂ M)) := rfl

@[simp] theorem add_val (a b : Fld M) :
    (a + b : Fld M).1 = a.1 + b.1 := rfl

@[simp] theorem smul_val (c : ℂ) (a : Fld M) :
    (c • a : Fld M).1 = c • a.1 := rfl

/-! ## Field closure of the nonnegative products -/

/-- A commutator residue of two fields is again a field.  Only finitely many coefficients of
the first field occur in `cCoeff k`; the varying coefficient belongs to the second field, so a
common lower-truncation bound is obtained from a finite infimum. -/
theorem isField_cCoeff_bracket {a b : FormalDist (End ℂ M)}
    (_ha : IsField a) (hb : IsField b) (k : ℕ) :
    IsField (cCoeff k (bracketDist a b)) := by
  intro x
  classical
  let bx : ℤ := Classical.choose (hb x)
  have hbx : ∀ q : ℤ, q < bx → b q x = 0 := Classical.choose_spec (hb x)
  let ba : ℕ → ℤ := fun r => Classical.choose (hb (a (-1 - (r : ℤ)) x))
  have hba : ∀ r : ℕ, ∀ q : ℤ, q < ba r → b q (a (-1 - (r : ℤ)) x) = 0 :=
    fun r => Classical.choose_spec (hb (a (-1 - (r : ℤ)) x))
  let bound : ℕ → ℤ := fun r => min bx (ba r) + ((k - r : ℕ) : ℤ)
  have hrange : (Finset.range (k + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ k)⟩
  let B : ℤ := (Finset.range (k + 1)).inf' hrange bound
  refine ⟨B, fun n hn => ?_⟩
  rw [cCoeff_apply, mulBySubPow_apply_sum]
  rw [LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro r hr
  have hrk : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  have hle : B ≤ bound r := Finset.inf'_le bound hr
  have hq : n - ((k - r : ℕ) : ℤ) < min bx (ba r) := by
    dsimp only [bound] at hle
    omega
  rw [bracketDist_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.mul_apply, Module.End.mul_apply,
    show (-1 : ℤ) - (r : ℤ) = -1 - (r : ℤ) by ring,
    hbx _ (lt_of_lt_of_le hq (min_le_left _ _)),
    hba r _ (lt_of_lt_of_le hq (min_le_right _ _)), map_zero, sub_zero, smul_zero]

theorem isField_negProd {a b : FormalDist (End ℂ M)} (ha : IsField a) (hb : IsField b)
    (k : ℕ) : IsField (negProd ha hb k) := by
  rw [negProd]
  exact isField_smul _ ((ha.deriv_iterate k).nprod hb)

/-! ## Bilinearity helpers for normal products -/

theorem deriv_add (a b : FormalDist (End ℂ M)) :
    VOA.deriv (a + b) = VOA.deriv a + VOA.deriv b := by
  funext n
  change (n + 1) • (a (n + 1) + b (n + 1)) =
    (n + 1) • a (n + 1) + (n + 1) • b (n + 1)
  exact smul_add _ _ _

theorem deriv_smul (c : ℂ) (a : FormalDist (End ℂ M)) :
    VOA.deriv (c • a) = c • VOA.deriv a := by
  funext n
  change (n + 1 : ℤ) • (c • a (n + 1)) = c • ((n + 1 : ℤ) • a (n + 1))
  exact smul_comm (n + 1 : ℤ) c (a (n + 1))

theorem deriv_iterate_add (k : ℕ) (a b : FormalDist (End ℂ M)) :
    (VOA.deriv^[k]) (a + b) =
      (VOA.deriv^[k]) a + (VOA.deriv^[k]) b := by
  induction k with
  | zero => rfl
  | succ j ih =>
      simp only [Function.iterate_succ_apply', ih, deriv_add]

theorem deriv_iterate_smul (k : ℕ) (c : ℂ) (a : FormalDist (End ℂ M)) :
    (VOA.deriv^[k]) (c • a) = c • (VOA.deriv^[k]) a := by
  induction k with
  | zero => rfl
  | succ j ih =>
      simp only [Function.iterate_succ_apply', ih, deriv_smul]

theorem nprod_add_left {a b c : FormalDist (End ℂ M)}
    (ha : IsField a) (hb : IsField b) (hc : IsField c) :
    VOA.nprod (isField_add ha hb) hc =
      VOA.nprod ha hc + VOA.nprod hb hc := by
  funext s
  apply LinearMap.ext
  intro x
  change (∑ᶠ m : ℤ, normalOrdered (a + b) c m (s - m) x) =
    (∑ᶠ m : ℤ, normalOrdered a c m (s - m) x) +
      ∑ᶠ m : ℤ, normalOrdered b c m (s - m) x
  rw [← finsum_add_distrib (normalOrdered_diag_support_finite ha hc s x)
      (normalOrdered_diag_support_finite hb hc s x)]
  apply finsum_congr
  intro m
  rw [normalOrdered_apply, normalOrdered_apply, normalOrdered_apply]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm, if_pos hm, if_pos hm]
    exact DFunLike.congr_fun (add_mul (a m) (b m) (c (s - m))) x
  · rw [if_neg hm, if_neg hm, if_neg hm]
    exact DFunLike.congr_fun (mul_add (c (s - m)) (a m) (b m)) x

theorem nprod_add_right {a b c : FormalDist (End ℂ M)}
    (ha : IsField a) (hb : IsField b) (hc : IsField c) :
    VOA.nprod ha (isField_add hb hc) =
      VOA.nprod ha hb + VOA.nprod ha hc := by
  funext s
  apply LinearMap.ext
  intro x
  change (∑ᶠ m : ℤ, normalOrdered a (b + c) m (s - m) x) =
    (∑ᶠ m : ℤ, normalOrdered a b m (s - m) x) +
      ∑ᶠ m : ℤ, normalOrdered a c m (s - m) x
  rw [← finsum_add_distrib (normalOrdered_diag_support_finite ha hb s x)
      (normalOrdered_diag_support_finite ha hc s x)]
  apply finsum_congr
  intro m
  rw [normalOrdered_apply, normalOrdered_apply, normalOrdered_apply]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm, if_pos hm, if_pos hm]
    exact DFunLike.congr_fun (mul_add (a m) (b (s - m)) (c (s - m))) x
  · rw [if_neg hm, if_neg hm, if_neg hm]
    exact DFunLike.congr_fun (add_mul (b (s - m)) (c (s - m)) (a m)) x

theorem nprod_smul_left (d : ℂ) {a b : FormalDist (End ℂ M)}
    (ha : IsField a) (hb : IsField b) :
    VOA.nprod (isField_smul d ha) hb = d • VOA.nprod ha hb := by
  funext s
  apply LinearMap.ext
  intro x
  change (∑ᶠ m : ℤ, normalOrdered (d • a) b m (s - m) x) =
    d • ∑ᶠ m : ℤ, normalOrdered a b m (s - m) x
  rw [smul_finsum' d (normalOrdered_diag_support_finite ha hb s x)]
  apply finsum_congr
  intro m
  rw [normalOrdered_apply, normalOrdered_apply]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm, if_pos hm]
    change ((d • a m) * b (s - m)) x = (d • (a m * b (s - m))) x
    rw [smul_mul_assoc]
  · rw [if_neg hm, if_neg hm]
    change (b (s - m) * (d • a m)) x = (d • (b (s - m) * a m)) x
    rw [mul_smul_comm]

theorem nprod_smul_right (d : ℂ) {a b : FormalDist (End ℂ M)}
    (ha : IsField a) (hb : IsField b) :
    VOA.nprod ha (isField_smul d hb) = d • VOA.nprod ha hb := by
  funext s
  apply LinearMap.ext
  intro x
  change (∑ᶠ m : ℤ, normalOrdered a (d • b) m (s - m) x) =
    d • ∑ᶠ m : ℤ, normalOrdered a b m (s - m) x
  rw [smul_finsum' d (normalOrdered_diag_support_finite ha hb s x)]
  apply finsum_congr
  intro m
  rw [normalOrdered_apply, normalOrdered_apply]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm, if_pos hm]
    change (a m * (d • b (s - m))) x = (d • (a m * b (s - m))) x
    rw [mul_smul_comm]
  · rw [if_neg hm, if_neg hm]
    change ((d • b (s - m)) * a m) x = (d • (b (s - m) * a m)) x
    rw [smul_mul_assoc]

theorem raw_nprod_congr {a a' b : FormalDist (End ℂ M)}
    (ha : IsField a) (ha' : IsField a') (hb : IsField b) (h : a = a') :
    VOA.nprod ha hb = VOA.nprod ha' hb := by
  subst h
  rfl

/-! ## Identity-field normal products -/

theorem nprod_idField_left {a : FormalDist (End ℂ M)} (ha : IsField a) :
    VOA.nprod (idField_isField (V := M)) ha = a := by
  funext s
  apply LinearMap.ext
  intro x
  rw [nprod_apply, finsum_eq_single _ 0]
  · rw [normalOrdered_apply, if_pos le_rfl, idField_apply, if_pos rfl,
      show s - 0 = s by ring]
    rfl
  · intro m hm
    rw [normalOrdered_apply, idField_apply, if_neg hm]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0, zero_mul]
      rfl
    · rw [if_neg h0, mul_zero]
      rfl

theorem nprod_zero_left {a : FormalDist (End ℂ M)} (ha : IsField a) :
    VOA.nprod (isField_zero (M := M)) ha = 0 := by
  funext s
  apply LinearMap.ext
  intro x
  rw [nprod_apply]
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  rw [normalOrdered_apply]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm]
    change ((0 : End ℂ M) * a (s - m)) x = 0
    rw [zero_mul]
    rfl
  · rw [if_neg hm]
    change (a (s - m) * (0 : End ℂ M)) x = 0
    rw [mul_zero]
    rfl

theorem deriv_idField :
    VOA.deriv (idField : FormalDist (End ℂ M)) = 0 := by
  funext n
  change (n + 1 : ℤ) • (if n + 1 = 0 then LinearMap.id else 0) = (0 : End ℂ M)
  by_cases h : n + 1 = 0
  · rw [if_pos h, h, zero_smul]
  · rw [if_neg h, smul_zero]

theorem deriv_iterate_idField_of_pos {k : ℕ} (hk : 0 < k) :
    (VOA.deriv^[k]) (idField : FormalDist (End ℂ M)) = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  induction j with
  | zero => simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
      (deriv_idField (M := M))
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih (Nat.succ_pos j)]
      funext n
      change (n + 1 : ℤ) • (0 : End ℂ M) = 0
      rw [smul_zero]

/-! ## The total integer product -/

/-- The `n`-th product of fields, at every integer index. -/
noncomputable def prod (n : ℤ) (a b : Fld M) : Fld M :=
  if _hn : 0 ≤ n then
    ⟨cCoeff n.toNat (bracketDist a.1 b.1), isField_cCoeff_bracket a.2 b.2 n.toNat⟩
  else
    ⟨negProd a.2 b.2 (-n - 1).toNat, isField_negProd a.2 b.2 (-n - 1).toNat⟩

@[simp] theorem prod_of_nonneg {n : ℤ} (hn : 0 ≤ n) (a b : Fld M) :
    (prod n a b).1 = cCoeff n.toNat (bracketDist a.1 b.1) := by
  simp [prod, hn]

@[simp] theorem prod_of_neg {n : ℤ} (hn : n < 0) (a b : Fld M) :
    (prod n a b).1 = negProd a.2 b.2 (-n - 1).toNat := by
  simp [prod, not_le.mpr hn]

theorem bracketDist_add_left (a b c : FormalDist (End ℂ M)) :
    bracketDist (a + b) c = bracketDist a c + bracketDist b c := by
  apply FormalDist₂.ext
  intro p q
  change (a p + b p) * c q - c q * (a p + b p) =
    (a p * c q - c q * a p) + (b p * c q - c q * b p)
  rw [add_mul, mul_add]
  abel

theorem bracketDist_add_right (a b c : FormalDist (End ℂ M)) :
    bracketDist a (b + c) = bracketDist a b + bracketDist a c := by
  apply FormalDist₂.ext
  intro p q
  change a p * (b q + c q) - (b q + c q) * a p =
    (a p * b q - b q * a p) + (a p * c q - c q * a p)
  rw [mul_add, add_mul]
  abel

theorem bracketDist_smul_left (d : ℂ) (a b : FormalDist (End ℂ M)) :
    bracketDist (d • a) b = d • bracketDist a b := by
  apply FormalDist₂.ext
  intro p q
  change (d • a p) * b q - b q * (d • a p) = d • (a p * b q - b q * a p)
  rw [smul_mul_assoc, mul_smul_comm, smul_sub]

theorem bracketDist_smul_right (d : ℂ) (a b : FormalDist (End ℂ M)) :
    bracketDist a (d • b) = d • bracketDist a b := by
  apply FormalDist₂.ext
  intro p q
  change a p * (d • b q) - (d • b q) * a p = d • (a p * b q - b q * a p)
  rw [mul_smul_comm, smul_mul_assoc, smul_sub]

theorem bracketDist_idField_right' (a : FormalDist (End ℂ M)) :
    bracketDist a (idField : FormalDist (End ℂ M)) = 0 := by
  apply FormalDist₂.ext
  intro p q
  rw [bracketDist_apply, idField_apply]
  by_cases hq : q = 0
  · rw [if_pos hq]
    change a p * (1 : End ℂ M) - (1 : End ℂ M) * a p = 0
    rw [mul_one, one_mul, sub_self]
  · rw [if_neg hq, mul_zero, zero_mul, sub_zero]
    rfl

theorem cCoeff_add (k : ℕ) (f g : FormalDist₂ (End ℂ M)) :
    cCoeff k (f + g) = cCoeff k f + cCoeff k g := by
  funext q
  change mulBySubPow k (f + g) (-1) q =
    mulBySubPow k f (-1) q + mulBySubPow k g (-1) q
  rw [map_add]
  rfl

theorem cCoeff_smul (k : ℕ) (d : ℂ) (f : FormalDist₂ (End ℂ M)) :
    cCoeff k (d • f) = d • cCoeff k f := by
  funext q
  change mulBySubPow k (d • f) (-1) q = d • mulBySubPow k f (-1) q
  rw [map_smul]
  rfl

theorem negProd_add_left {a b c : FormalDist (End ℂ M)}
    (ha : IsField a) (hb : IsField b) (hc : IsField c) (k : ℕ) :
    negProd (isField_add ha hb) hc k = negProd ha hc k + negProd hb hc k := by
  rw [negProd, negProd, negProd]
  rw [show VOA.nprod ((isField_add ha hb).deriv_iterate k) hc =
      VOA.nprod (isField_add (ha.deriv_iterate k) (hb.deriv_iterate k)) hc by
      apply raw_nprod_congr
      exact deriv_iterate_add k a b]
  rw [nprod_add_left, smul_add]

theorem negProd_add_right {a b c : FormalDist (End ℂ M)}
    (ha : IsField a) (hb : IsField b) (hc : IsField c) (k : ℕ) :
    negProd ha (isField_add hb hc) k = negProd ha hb k + negProd ha hc k := by
  rw [negProd, negProd, negProd, nprod_add_right, smul_add]

theorem negProd_smul_left (d : ℂ) {a b : FormalDist (End ℂ M)}
    (ha : IsField a) (hb : IsField b) (k : ℕ) :
    VOA.negProd (a := d • a) (b := b) (isField_smul d ha) hb k =
      d • ((k.factorial : ℂ)⁻¹ •
        @VOA.nprod M _ _ ((VOA.deriv^[k]) a) b
          (IsField.deriv_iterate ha k) hb) := by
  rw [negProd]
  rw [show VOA.nprod ((isField_smul d ha).deriv_iterate k) hb =
      VOA.nprod (isField_smul d (ha.deriv_iterate k)) hb by
      apply raw_nprod_congr
      exact deriv_iterate_smul k d a]
  rw [nprod_smul_left d (ha.deriv_iterate k) hb, smul_smul, smul_smul]
  ring_nf

theorem negProd_smul_right (d : ℂ) {a b : FormalDist (End ℂ M)}
    (ha : IsField a) (hb : IsField b) (k : ℕ) :
    negProd ha (isField_smul d hb) k = d • negProd ha hb k := by
  rw [negProd, negProd, nprod_smul_right d (ha.deriv_iterate k) hb,
    smul_smul, smul_smul]
  ring_nf

@[simp] theorem prod_add_left (n : ℤ) (a b c : Fld M) :
    prod n (a + b) c = prod n a c + prod n b c := by
  apply Subtype.ext
  change (prod n (a + b) c).1 = (prod n a c).1 + (prod n b c).1
  rcases lt_or_ge n 0 with hn | hn
  · rw [prod_of_neg hn, prod_of_neg hn, prod_of_neg hn]
    change negProd (isField_add a.2 b.2) c.2 (-n - 1).toNat = _
    exact negProd_add_left a.2 b.2 c.2 _
  · rw [prod_of_nonneg hn, prod_of_nonneg hn, prod_of_nonneg hn]
    change cCoeff n.toNat (bracketDist (a.1 + b.1) c.1) = _
    rw [bracketDist_add_left, cCoeff_add]

@[simp] theorem prod_add_right (n : ℤ) (a b c : Fld M) :
    prod n a (b + c) = prod n a b + prod n a c := by
  apply Subtype.ext
  change (prod n a (b + c)).1 = (prod n a b).1 + (prod n a c).1
  rcases lt_or_ge n 0 with hn | hn
  · rw [prod_of_neg hn, prod_of_neg hn, prod_of_neg hn]
    change negProd a.2 (isField_add b.2 c.2) (-n - 1).toNat = _
    exact negProd_add_right a.2 b.2 c.2 _
  · rw [prod_of_nonneg hn, prod_of_nonneg hn, prod_of_nonneg hn]
    change cCoeff n.toNat (bracketDist a.1 (b.1 + c.1)) = _
    rw [bracketDist_add_right, cCoeff_add]

@[simp] theorem prod_smul_left (n : ℤ) (d : ℂ) (a b : Fld M) :
    prod n (d • a) b = d • prod n a b := by
  apply Subtype.ext
  change (prod n (d • a) b).1 = d • (prod n a b).1
  rcases lt_or_ge n 0 with hn | hn
  · rw [prod_of_neg hn, prod_of_neg hn]
    change negProd (isField_smul d a.2) b.2 (-n - 1).toNat = _
    exact negProd_smul_left d a.2 b.2 _
  · rw [prod_of_nonneg hn, prod_of_nonneg hn]
    change cCoeff n.toNat (bracketDist (d • a.1) b.1) = _
    rw [bracketDist_smul_left, cCoeff_smul]

@[simp] theorem prod_smul_right (n : ℤ) (d : ℂ) (a b : Fld M) :
    prod n a (d • b) = d • prod n a b := by
  apply Subtype.ext
  change (prod n a (d • b)).1 = d • (prod n a b).1
  rcases lt_or_ge n 0 with hn | hn
  · rw [prod_of_neg hn, prod_of_neg hn]
    change negProd a.2 (isField_smul d b.2) (-n - 1).toNat = _
    exact negProd_smul_right d a.2 b.2 _
  · rw [prod_of_nonneg hn, prod_of_nonneg hn]
    change cCoeff n.toNat (bracketDist a.1 (d • b.1)) = _
    rw [bracketDist_smul_right, cCoeff_smul]

/-! ## Identity laws -/

@[simp] theorem prod_one_left_nat (k : ℕ) (a : Fld M) :
    prod (k : ℤ) one a = 0 := by
  apply Subtype.ext
  change (prod (k : ℤ) one a).1 = (0 : FormalDist (End ℂ M))
  rw [prod_of_nonneg (Int.natCast_nonneg k)]
  change cCoeff k (bracketDist (idField : FormalDist (End ℂ M)) a.1) = 0
  rw [bracketDist_idField_left]
  funext q
  rw [cCoeff_apply, map_zero]
  rfl

@[simp] theorem prod_one_left_neg_one (a : Fld M) :
    prod (-1) one a = a := by
  apply Subtype.ext
  change (prod (-1) one a).1 = a.1
  rw [prod_of_neg (by norm_num)]
  change negProd (idField_isField (V := M)) a.2 0 = a.1
  norm_num [negProd]
  exact nprod_idField_left a.2

@[simp] theorem prod_one_left_negsucc {k : ℕ} (hk : 0 < k) (a : Fld M) :
    prod (-(k : ℤ) - 1) one a = 0 := by
  apply Subtype.ext
  change (prod (-(k : ℤ) - 1) one a).1 = (0 : FormalDist (End ℂ M))
  rw [prod_of_neg (by omega)]
  rw [show (-(-(k : ℤ) - 1) - 1).toNat = k by omega]
  change negProd (idField_isField (V := M)) a.2 k = 0
  rw [negProd]
  rw [show VOA.nprod ((idField_isField (V := M)).deriv_iterate k) a.2 =
      VOA.nprod (isField_zero (M := M)) a.2 by
      apply raw_nprod_congr
      exact deriv_iterate_idField_of_pos hk,
    nprod_zero_left, smul_zero]

@[simp] theorem prod_one_right_nat (k : ℕ) (a : Fld M) :
    prod (k : ℤ) a one = 0 := by
  apply Subtype.ext
  change (prod (k : ℤ) a one).1 = (0 : FormalDist (End ℂ M))
  rw [prod_of_nonneg (Int.natCast_nonneg k)]
  change cCoeff k (bracketDist a.1 (idField : FormalDist (End ℂ M))) = 0
  rw [bracketDist_idField_right']
  funext q
  rw [cCoeff_apply, map_zero]
  rfl

@[simp] theorem prod_one_right_neg_one (a : Fld M) :
    prod (-1) a one = a := by
  apply Subtype.ext
  change (prod (-1) a one).1 = a.1
  rw [prod_of_neg (by norm_num)]
  change negProd a.2 (idField_isField (V := M)) 0 = a.1
  norm_num [negProd]
  exact nprod_idField a.2

theorem prod_one_right_negsucc (k : ℕ) (a : Fld M) :
    (prod (-(k : ℤ) - 1) a one).1 =
      (k.factorial : ℂ)⁻¹ • (VOA.deriv^[k]) a.1 := by
  rw [prod_of_neg (by omega)]
  rw [show (-(-(k : ℤ) - 1) - 1).toNat = k by omega]
  change negProd a.2 (idField_isField (V := M)) k = _
  simp only [negProd]
  rw [nprod_idField]

/-! ## Locality gives product truncation -/

theorem prod_eq_zero_of_locality {a b : Fld M} {N : ℕ}
    (hN : mulBySubPow N (bracketDist a.1 b.1) = 0)
    {n : ℤ} (hn : (N : ℤ) ≤ n) : prod n a b = 0 := by
  have hn0 : 0 ≤ n := le_trans (Int.natCast_nonneg N) hn
  have hNt : N ≤ n.toNat := by omega
  apply Subtype.ext
  rw [prod_of_nonneg hn0]
  funext q
  rw [cCoeff_apply, mulBySubPow_eq_zero_mono hNt hN]
  rfl

theorem prod_eventually_zero_of_local {a b : Fld M} (h : Local a.1 b.1) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → prod n a b = 0 := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun _ hn => prod_eq_zero_of_locality hN hn⟩

end Fld

/-! ## Closed local field systems -/

/-- A linear local system of weak vertex operators, closed under every integer field product. -/
structure LocalFieldSystem (M : Type*) [AddCommGroup M] [Module ℂ M] where
  carrier : Submodule ℂ (Fld M)
  one_mem : Fld.one ∈ carrier
  locality : ∀ a ∈ carrier, ∀ b ∈ carrier, Local a.1 b.1
  prod_mem : ∀ (n : ℤ) {a b : Fld M}, a ∈ carrier → b ∈ carrier → Fld.prod n a b ∈ carrier

namespace LocalFieldSystem

instance : Membership (Fld M) (LocalFieldSystem M) :=
  ⟨fun L a => a ∈ L.carrier⟩

@[simp] theorem mem_carrier (L : LocalFieldSystem M) (a : Fld M) :
    a ∈ L.carrier ↔ a ∈ L := Iff.rfl

theorem zero_mem (L : LocalFieldSystem M) : (0 : Fld M) ∈ L := L.carrier.zero_mem

theorem add_mem (L : LocalFieldSystem M) {a b : Fld M} (ha : a ∈ L) (hb : b ∈ L) :
    a + b ∈ L := L.carrier.add_mem ha hb

theorem smul_mem (L : LocalFieldSystem M) (c : ℂ) {a : Fld M} (ha : a ∈ L) :
    c • a ∈ L := L.carrier.smul_mem c ha

theorem prod_eventually_zero (L : LocalFieldSystem M) {a b : Fld M}
    (ha : a ∈ L) (hb : b ∈ L) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → Fld.prod n a b = 0 :=
  Fld.prod_eventually_zero_of_local (L.locality a ha b hb)

end LocalFieldSystem

end VOA
