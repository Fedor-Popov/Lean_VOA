/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.HeisenbergTwistedModuleTwistedComm
import VOA.Moonshine.HeisenbergTwistedModuleVertex

/-!
# The twisted word fields: order independence and creation  (Moonshine step M6a)

The rescaled twisted field `Ywt r l` of a word `l` (`HeisenbergTwistedModuleVertex`) is defined
recursively by inverting the twisted product formula against the generators, with an explicit
finite cut-off.  This file shows that the definition is the twisted product of
`Moonshine/HeisenbergTwistedModuleTwistedComm.lean`, independent of the order of the letters:

* `prod_Fgen_Ywt_eq_zero` — the generators have pole order `≤ wt l` against `Ywt r l`, so the
  cut-off in `Ywt` is harmless;
* `Ywt_cons_star` — `Ỹ((n,a) :: w) = star ½ (Fgen a) (−n−1) Ỹ(w)`;
* `star_gen_gen` — the twisted products of two generators: `Fgen_a ⋆₀ Fgen_b = 0`,
  `Fgen_a ⋆₁ Fgen_b = δ_{ab} z`, all others zero (the `½δ` of the untwisted product is cancelled
  by `C(−½,1)`);
* `star_gen_swap` — two creation twisted products commute (from `star_comm`);
* `Ywt_perm` — **`Ywt` depends only on the multiset of letters**;
* `FT_mul_X` — **the creation part of the twisted product formula for the generators**: for
  every state `w` (rescaled on any class `e`) and every letter `(n, a)`,
  `F_{e+1}(h_a(−n−1) w) = star ½ (Fgen a) (−n−1) F_e(w)`, where `F_e(u) = resc (Y^T u) 2 e`.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA

namespace Moonshine

open MvPolynomial TwistedHeisenberg HeisenbergN TwistedReduction
open Module (End)
open scoped BigOperators

variable (r : ℕ)

/-! ## The generated system -/

theorem genSet_local : ∀ a ∈ genSet r, ∀ b ∈ genSet r, Local a.1 b.1 := by
  rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
  exact Fgen_local r c d

theorem FgenFld_mem (a : Fin r) : FgenFld r a ∈ TGenerated (genSet r) :=
  subset_tgenerated ⟨a, rfl⟩

theorem tlocal {a b : Fld (FockT r)} (ha : a ∈ TGenerated (genSet r))
    (hb : b ∈ TGenerated (genSet r)) : Local a.1 b.1 :=
  tgenerated_local (genSet_local r) ha hb

/-! ## Generator products as fields -/

theorem prod_Fgen_two_le_fld (a b : Fin r) {n : ℤ} (hn : 2 ≤ n) :
    Fld.prod n (FgenFld r a) (FgenFld r b) = 0 :=
  Subtype.ext (prod_Fgen_of_two_le r a b hn)

theorem prod_Fgen_one_fld (a b : Fin r) :
    Fld.prod 1 (FgenFld r a) (FgenFld r b)
      = (if a = b then (1 : ℂ) else 0) • fzmul 1 (Fld.one : Fld (FockT r)) := by
  apply Subtype.ext
  rw [prod_Fgen_one, Fld.smul_val, fzmul_val, Fld.one_val]
  funext t
  change opeOne r a b t = (if a = b then (1 : ℂ) else 0) • (idField (t - 1))
  rw [opeOne, idField]
  split_ifs <;> first | (exfalso; omega) | simp

theorem prod_Fgen_zero_fld (a b : Fin r) :
    Fld.prod 0 (FgenFld r a) (FgenFld r b)
      = (if a = b then (1 / 2 : ℂ) else 0) • (Fld.one : Fld (FockT r)) := by
  apply Subtype.ext
  rw [prod_Fgen_zero, Fld.smul_val, Fld.one_val]
  funext t
  change opeZero r a b t = (if a = b then (1 / 2 : ℂ) else 0) • (idField t)
  rw [opeZero, idField]
  split_ifs <;> simp

/-- **The twisted products of two generators.** -/
theorem star_gen_gen (a b : Fin r) (i : ℕ) :
    star (1 / 2) (FgenFld r a) i (FgenFld r b)
      = if i = 1 then (if a = b then (1 : ℂ) else 0) • fzmul 1 (Fld.one : Fld (FockT r))
        else 0 := by
  rw [star_eq_sum_range _ _ _ _ 2 (fun j hj => prod_Fgen_two_le_fld r a b (by omega))]
  have h1 : cbinom (-(1 / 2)) 1 = -(1 / 2) := by simp [cbinom]
  rcases i with _ | _ | i
  · rw [if_neg (by norm_num), Finset.sum_range_succ, Finset.sum_range_one]
    simp only [Nat.cast_zero, Nat.cast_one, add_zero, zero_add, neg_zero, cbinom_zero, one_smul,
      fzmul_zero_shift]
    rw [prod_Fgen_zero_fld, prod_Fgen_one_fld, h1, fzmul_smul, fzmul_fzmul,
      show (-1 : ℤ) + 1 = 0 by norm_num, fzmul_zero_shift, smul_smul]
    split_ifs <;> module
  · rw [if_pos rfl, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [Nat.cast_zero, Nat.cast_one, add_zero, neg_zero, cbinom_zero, one_smul,
      fzmul_zero_shift]
    rw [show ((0 + 1 : ℕ) : ℤ) = 1 by norm_num, prod_Fgen_one_fld, show (1 : ℤ) + 1 = 2 by norm_num,
      prod_Fgen_two_le_fld r a b (by norm_num), fzmul_zero, smul_zero, add_zero]
  · rw [Finset.sum_eq_zero (fun j _ => by rw [prod_Fgen_two_le_fld r a b (by omega), fzmul_zero,
      smul_zero]), if_neg (by omega)]

/-! ## The cut-off of `Ywt` is harmless -/

theorem FgenFld_local (a b : Fin r) : Local (FgenFld r a).1 (FgenFld r b).1 :=
  tlocal r (FgenFld_mem r a) (FgenFld_mem r b)

/-- **The generators have pole order at most `wt l` against `Ywt r l`.** -/
theorem prod_Fgen_Ywt_eq_zero (b : Fin r) :
    ∀ (l : List (ℕ × Fin r)) (k : ℤ), 1 + (wordWeightNN l : ℤ) ≤ k →
      Fld.prod k (FgenFld r b) (Ywt r l) = 0 := by
  intro l
  induction l with
  | nil =>
      intro k hk
      exact prod_one_right_nonneg' k (by simp at hk; omega) _
  | cons c w ih =>
      intro k hk
      rw [wordWeightNN_cons] at hk
      rw [Ywt_cons, prod_sum_right]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Fld.prod_smul_right, prod_fzmul_right]
      have hcomm := prod_comm_formula (FgenFld_local r b c.2) 2
        (fun s hs => prod_Fgen_two_le_fld r b c.2 (by omega)) k (-(c.1 : ℤ) - 1 + i)
        (C := Ywt r w)
      rw [ih k (by push_cast at hk; omega), prod_zero_right, sub_zero] at hcomm
      rw [hcomm, Finset.sum_range_succ, Finset.sum_range_one]
      simp only [Nat.cast_zero, Nat.cast_one, sub_zero]
      rw [prod_Fgen_zero_fld, prod_Fgen_one_fld,
        prod_scalar_one_nonneg _ (by push_cast at hk; omega),
        prod_scalar_z_nonneg _ (by push_cast at hk; omega)]
      simp

/-- **`Ywt` is the twisted product**: `Ỹ((n,a) :: w) = star ½ (Fgen a) (−n−1) Ỹ(w)`. -/
theorem Ywt_cons_star (c : ℕ × Fin r) (w : List (ℕ × Fin r)) :
    Ywt r (c :: w) = star (1 / 2) (FgenFld r c.2) (-(c.1 : ℤ) - 1) (Ywt r w) := by
  rw [Ywt_cons, star_eq_sum_range _ _ _ _ (c.1 + 3 + 2 * wordWeightNN w)
    (fun i hi => prod_Fgen_Ywt_eq_zero r c.2 w _ (by omega))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_div]

/-! ## Order independence -/

/-- **Two creation twisted products of generators commute.** -/
theorem star_gen_swap (c c' : ℕ × Fin r) {F : Fld (FockT r)} (hF : F ∈ TGenerated (genSet r)) :
    star (1 / 2) (FgenFld r c.2) (-(c.1 : ℤ) - 1)
        (star (1 / 2) (FgenFld r c'.2) (-(c'.1 : ℤ) - 1) F)
      = star (1 / 2) (FgenFld r c'.2) (-(c'.1 : ℤ) - 1)
          (star (1 / 2) (FgenFld r c.2) (-(c.1 : ℤ) - 1) F) := by
  have h := star_comm (genSet_local r) (FgenFld_mem r c.2) (FgenFld_mem r c'.2) hF (1 / 2) (1 / 2)
    (-(c.1 : ℤ) - 1) (-(c'.1 : ℤ) - 1) 2 (fun s hs => prod_Fgen_two_le_fld r _ _ (by omega))
  rw [Finset.sum_range_succ, Finset.sum_range_one, star_gen_gen, star_gen_gen, if_neg (by norm_num),
    if_pos (by norm_num), star_zero_left, smul_zero, zero_add,
    star_smul_left (local_fzmul_one_left 1 F),
    show (1 / 2 : ℂ) + 1 / 2 = ((1 : ℤ) : ℂ) by norm_num, star_fzmul_one,
    if_neg (show -(c.1 : ℤ) - 1 + (-(c'.1 : ℤ) - 1) - ((1 : ℕ) : ℤ) ≠ -1 by push_cast; omega),
    smul_zero, smul_zero] at h
  exact sub_eq_zero.mp h

/-- **`Ywt` depends only on the multiset of letters.** -/
theorem Ywt_perm {l l' : List (ℕ × Fin r)} (h : l.Perm l') : Ywt r l = Ywt r l' := by
  induction h with
  | nil => rfl
  | cons x _ ih => rw [Ywt_cons_star, Ywt_cons_star, ih]
  | swap x y l =>
      rw [Ywt_cons_star, Ywt_cons_star, Ywt_cons_star, Ywt_cons_star,
        star_gen_swap r y x (Ywt_mem r l)]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem coe_monoWordN (m : (ℕ × Fin r) →₀ ℕ) :
    ((monoWordN m : List (ℕ × Fin r)) : Multiset (ℕ × Fin r)) = Finsupp.toMultiset m := by
  classical
  ext v
  rw [Finsupp.count_toMultiset, monoWordN, ← Multiset.coe_bind, Finset.coe_toList,
    Multiset.count_bind]
  simp only [Multiset.coe_replicate, Multiset.count_replicate]
  rw [show (Multiset.map (fun ia => if ia = v then m ia else 0) m.support.val).sum
      = ∑ ia ∈ m.support, (if ia = v then m ia else 0) from rfl, Finset.sum_ite_eq']
  split_ifs with hv
  · rfl
  · exact (Finsupp.notMem_support_iff.mp hv).symm

theorem monoWordN_add_single_perm (m : (ℕ × Fin r) →₀ ℕ) (c : ℕ × Fin r) :
    (monoWordN (m + Finsupp.single c 1)).Perm (c :: monoWordN m) := by
  rw [← Multiset.coe_eq_coe, coe_monoWordN, ← Multiset.cons_coe, coe_monoWordN,
    Finsupp.toMultiset_add, Finsupp.toMultiset_single, one_nsmul, add_comm,
    Multiset.singleton_add]

/-- The word form of the creation formula. -/
theorem Ywt_monoWordN_add_single (m : (ℕ × Fin r) →₀ ℕ) (c : ℕ × Fin r) :
    Ywt r (monoWordN (m + Finsupp.single c 1))
      = star (1 / 2) (FgenFld r c.2) (-(c.1 : ℤ) - 1) (Ywt r (monoWordN m)) := by
  rw [Ywt_perm r (monoWordN_add_single_perm r m c), Ywt_cons_star]

/-! ## The rescaled twisted vertex operators `F_e(u)` -/

/-- **The rescaled twisted vertex operator** of `u` on the class `e`:
`F_e(u) = resc (Y^T u) 2 e`, the field with `p`-th mode `u₍(2p+e)/2₎`. -/
noncomputable def FT (e : ℤ) (u : FockN r) : Fld (FockT r) :=
  rescFld (by norm_num : 0 < 2) (YT_truncation r u) e

@[simp] theorem FT_val (e : ℤ) (u : FockN r) : (FT r e u).1 = resc (YT r u) 2 e := rfl

theorem FT_add (e : ℤ) (u v : FockN r) : FT r e (u + v) = FT r e u + FT r e v :=
  Subtype.ext (by rw [FT_val, map_add, resc_add_fun]; rfl)

theorem FT_smul (e : ℤ) (c : ℂ) (u : FockN r) : FT r e (c • u) = c • FT r e u :=
  Subtype.ext (by rw [FT_val, map_smul, resc_smul_fun]; rfl)

theorem FT_zero (e : ℤ) : FT r e 0 = 0 := by
  have := FT_smul r e 0 0
  rwa [zero_smul, zero_smul] at this

theorem FT_sub (e : ℤ) (u v : FockN r) : FT r e (u - v) = FT r e u - FT r e v := by
  rw [sub_eq_add_neg, FT_add, show -v = (-1 : ℂ) • v by simp, FT_smul, sub_eq_add_neg]
  simp

/-- `F_e` as a linear map. -/
noncomputable def FTL (e : ℤ) : FockN r →ₗ[ℂ] Fld (FockT r) where
  toFun := FT r e
  map_add' := FT_add r e
  map_smul' := FT_smul r e

theorem FT_sum {ι : Type*} (e : ℤ) (s : Finset ι) (f : ι → FockN r) :
    FT r e (∑ i ∈ s, f i) = ∑ i ∈ s, FT r e (f i) := map_sum (FTL r e) f s

theorem FT_mem (e : ℤ) (u : FockN r) : FT r e u ∈ TGenerated (genSet r) := by
  obtain ⟨F, hF, hFe⟩ := resc_YT_mem r u e
  have : FT r e u = F := Subtype.ext hFe
  rw [this]
  exact hF

theorem FT_local (e e' : ℤ) (u v : FockN r) : Local (FT r e u).1 (FT r e' v).1 :=
  tlocal r (FT_mem r e u) (FT_mem r e' v)

theorem gen_FT_local (b : Fin r) (e : ℤ) (u : FockN r) : Local (FgenFld r b).1 (FT r e u).1 :=
  tlocal r (FgenFld_mem r b) (FT_mem r e u)

/-- Moving the class by `2` multiplies by `z`. -/
theorem FT_add_two (e : ℤ) (u : FockN r) : FT r (e + 2) u = fzmul 1 (FT r e u) :=
  Subtype.ext (by
    rw [FT_val, fzmul_val, FT_val]
    exact resc_add_N (YT r u) 2 e)

theorem FT_shift (e c : ℤ) (u : FockN r) : FT r (e + 2 * c) u = fzmul c (FT r e u) := by
  induction c using Int.induction_on with
  | zero => simp
  | succ c ih =>
      rw [show e + 2 * (c + 1) = (e + 2 * c) + 2 by ring, FT_add_two, ih, fzmul_fzmul, add_comm]
  | pred c ih =>
      have h := FT_add_two r (e + 2 * (-(c : ℤ) - 1)) u
      rw [show e + 2 * (-(c : ℤ) - 1) + 2 = e + 2 * (-(c : ℤ)) by ring, ih] at h
      have h' := congrArg (fzmul (-1)) h
      rw [fzmul_fzmul, fzmul_fzmul, show (-1 : ℤ) + 1 = 0 by norm_num, fzmul_zero_shift] at h'
      rw [← h', show (-1 : ℤ) + -(c : ℤ) = -(c : ℤ) - 1 by ring]

/-- `F_e` of a monomial: a power of `z` times its word field, or `0` off the class. -/
theorem FT_monomial (e : ℤ) (m : (ℕ × Fin r) →₀ ℕ) :
    FT r e (monomial m 1) = if (e - m.degree) % 2 = 0
      then fzmul ((e - m.degree) / 2) (Ywt r (monoWordN m)) else 0 := by
  apply Subtype.ext
  rw [FT_val, YT_monomial, one_smul, resc_YTmon, length_monoWordN]
  split_ifs <;> rfl

/-- `F_e(u) = 0` when `e` is off the class of `u`. -/
theorem FT_eq_zero_of_parity {j : ℕ} {u : FockN r} (hu : u ∈ (sigma1 r).twistedEigenspace 2 j)
    {e : ℤ} (he : (e + j) % 2 ≠ 0) : FT r e u = 0 := by
  apply fld_ext_mode
  intro p x
  rw [FT_val, mode_resc, YT_support r j u hu _ (by push_cast; omega), Fld.zero_val, mode_zero]

/-! ## The creation part of the twisted product formula -/

theorem X_mul_monomial' (c : ℕ × Fin r) (m : (ℕ × Fin r) →₀ ℕ) (a : ℂ) :
    (X c : FockN r) * monomial m a = monomial (m + Finsupp.single c 1) a := by
  rw [X, monomial_mul, one_mul, add_comm]

/-- **Creation**: `F_{e+1}(h_a(−n−1) w) = star ½ (Fgen a) (−n−1) F_e(w)` for every state `w`
and every class `e`. -/
theorem FT_mul_X (e : ℤ) (c : ℕ × Fin r) (w : FockN r) :
    FT r (e + 1) (X c * w) = star (1 / 2) (FgenFld r c.2) (-(c.1 : ℤ) - 1) (FT r e w) := by
  induction w using MvPolynomial.induction_on' with
  | monomial m a =>
      rw [X_mul_monomial', show (monomial (m + Finsupp.single c 1) a : FockN r)
          = a • monomial (m + Finsupp.single c 1) 1 by rw [smul_monomial, smul_eq_mul, mul_one],
        show (monomial m a : FockN r) = a • monomial m 1 by
          rw [smul_monomial, smul_eq_mul, mul_one],
        FT_smul, FT_smul, star_smul_right (gen_FT_local r _ _ _), FT_monomial, FT_monomial,
        map_add, Finsupp.degree_single]
      push_cast
      rw [show e + 1 - ((m.degree : ℤ) + 1) = e - m.degree by ring]
      split_ifs
      · rw [Ywt_monoWordN_add_single, star_fzmul_right]
      · rw [star_zero_right]
  | add p q hp hq =>
      rw [mul_add, FT_add, FT_add, hp, hq,
        star_add_right (gen_FT_local r _ _ _) (gen_FT_local r _ _ _)]

/-- The negative modes of the generators on `FockN r` are the creation operators. -/
theorem smul_X_neg (b : Fin r) (n : ℕ) (w : FockN r) :
    (heisVOA1 r).smul (X (0, b)) (-(n : ℤ) - 1) w = X (n, b) * w := by
  rw [PreVertexAlgebra.smul_def]
  change mode (YN r 1 (X (0, b))) (-(n : ℤ) - 1) w = _
  rw [← oscN_neg_one_vacuum r 1 b, YN_current, currentN_mode, oscN_neg_eq_mulXN]

/-- **The twisted product formula for a generator in a creation mode**:
`F_{e+1}(b₍₋ₙ₋₁₎ w) = star ½ (Fgen b) (−n−1) F_e(w)`. -/
theorem FT_gen_creation (e : ℤ) (b : Fin r) (n : ℕ) (w : FockN r) :
    FT r (e + 1) ((heisVOA1 r).smul (X (0, b)) (-(n : ℤ) - 1) w)
      = star (1 / 2) (FgenFld r b) (-(n : ℤ) - 1) (FT r e w) := by
  rw [smul_X_neg, FT_mul_X r e (n, b) w]

end Moonshine

end VOA
