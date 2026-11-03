/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.HeisenbergFock
import VOA.Examples.HeisenbergVertex
import VOA.Examples.HeisenbergVirasoro

/-!
# VA1 grading and VA5 regularity for the Heisenberg VOA
-/

namespace VOA

open scoped BigOperators
open MvPolynomial
open Module (End)

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-! ## IsField closure under `+`, `•`, `0`, finite sums (for `Y k u`) -/

theorem IsField.zero : IsField (0 : FormalDist (End ℂ V)) := by
  intro x; exact ⟨0, fun n _ => by show (0 : FormalDist (End ℂ V)) n x = 0; rfl⟩

theorem IsField.add {a b : FormalDist (End ℂ V)} (ha : IsField a) (hb : IsField b) :
    IsField (a + b) := by
  intro x
  obtain ⟨Ba, hBa⟩ := ha x
  obtain ⟨Bb, hBb⟩ := hb x
  refine ⟨min Ba Bb, fun n hn => ?_⟩
  show (a + b) n x = 0
  have h1 : a n x = 0 := hBa n (lt_of_lt_of_le hn (min_le_left _ _))
  have h2 : b n x = 0 := hBb n (lt_of_lt_of_le hn (min_le_right _ _))
  show a n x + b n x = 0
  rw [h1, h2, add_zero]

theorem IsField.smul (c : ℂ) {a : FormalDist (End ℂ V)} (ha : IsField a) :
    IsField (c • a) := by
  intro x
  obtain ⟨B, hB⟩ := ha x
  refine ⟨B, fun n hn => ?_⟩
  show (c • a) n x = 0
  show c • a n x = 0
  rw [hB n hn, smul_zero]

theorem IsField.finsetSum {ι : Type*} (s : Finset ι) (f : ι → FormalDist (End ℂ V))
    (hf : ∀ i ∈ s, IsField (f i)) : IsField (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (IsField.zero (V := V))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- **`Y k u` is a field for every `u`** (the linear-combination of the monomial fields). -/
theorem Y_isField (k : ℂ) (u : Fock) : IsField (Y k u) := by
  classical
  rw [show Y k u = Finsupp.linearCombination ℂ (Ymon k) u from rfl,
      Finsupp.linearCombination_apply, Finsupp.sum]
  exact IsField.finsetSum _ _ (fun a _ => IsField.smul _ (Ymon_isField k a))

/-! ## VA5 — regularity: `u₍ₙ₎ v = 0` for `n` large

`mode (Y k u) n v = (Y k u) (-n-1) v` and `Y k u` is a field (lower-truncated on `v`), so
the high `n`-modes vanish: with `B` the truncation bound for `v`, every `n ≥ -B` gives
`-n-1 < B`, hence `(Y k u) (-n-1) v = 0`.  This is the regularity axiom VA5. -/

/-- **VA5 (regularity).** For every `u, v` the products `u₍ₙ₎v = mode (Y k u) n v` vanish for
all large `n`: there is `N` with `mode (Y k u) n v = 0` for all `n ≥ N`.  Here `N = -B`,
where `B` is the lower-truncation bound of the field `Y k u` on the vector `v`. -/
theorem va5_regularity (k : ℂ) (u v : Fock) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (Y k u) n v = 0 := by
  obtain ⟨B, hB⟩ := Y_isField k u v
  refine ⟨-B, fun n hn => ?_⟩
  rw [mode_apply]
  exact hB (-n - 1) (by omega)

/-! ## VA1 — grading: the `ℤ`-extension `gradingZ` and graded fields

The Fock grading `gradingW : ℕ → Submodule ℂ Fock` is extended to `ℤ` by `⊥` in negative
weight, matching the VOA4 positivity `𝒱ₙ = 0` for `n < 0`.  The vertex operators `Y(u,z)`
are *graded fields*: for `u` of weight `D`, the `zʲ`-coefficient `(Y u) j` maps `F_w` into
`F_{D+w+j}`.  This is the coefficient form of VA1 `u₍ₙ₎ : F_ℓ → F_{D+ℓ-n-1}`
(set `j = -n-1`). -/

/-- The `ℤ`-extension of the Fock grading: `gradingW w` in non-negative weight, `⊥` below. -/
noncomputable def gradingZ (n : ℤ) : Submodule ℂ Fock :=
  if 0 ≤ n then gradingW n.toNat else ⊥

theorem gradingZ_of_nonneg {n : ℤ} (hn : 0 ≤ n) : gradingZ n = gradingW n.toNat := by
  rw [gradingZ, if_pos hn]

theorem gradingZ_of_neg {n : ℤ} (hn : n < 0) : gradingZ n = ⊥ := by
  rw [gradingZ, if_neg (by omega)]

/-- Membership of a non-negative-weight homogeneous element in `gradingZ`. -/
theorem mem_gradingZ_of_gradingW {w : ℕ} {p : Fock} (hp : p ∈ gradingW w) :
    p ∈ gradingZ (w : ℤ) := by
  rw [gradingZ_of_nonneg (by positivity), Int.toNat_natCast]; exact hp

theorem zero_mem_gradingZ (n : ℤ) : (0 : Fock) ∈ gradingZ n := (gradingZ n).zero_mem

/-- A **graded field of weight `D`**: each coefficient `a j` sends `F_w` into `F_{D+w+j}`
(the `ℤ`-extended grading).  This is the field-level form of the VA1 grading law. -/
def GradedField (a : FormalDist (End ℂ Fock)) (D : ℤ) : Prop :=
  ∀ (j : ℤ) (w : ℕ) (p : Fock), p ∈ gradingW w → a j p ∈ gradingZ (D + w + j)

/-! ### The oscillator `osc k n` is grading-covariant: `osc k n : F_w → F_{w-n}` -/

/-- An annihilation `osc k n` (`n > 0`) of weight bigger than the source kills it:
`pderiv` of a weight-`w` homogeneous polynomial by a variable of weight `> w` is `0`. -/
theorem pderiv_eq_zero_of_weight_lt {i : ℕ} {w : ℕ} {p : Fock}
    (hp : p ∈ gradingW w) (hlt : w < weightFn i) : pderiv i p = 0 := by
  classical
  apply pderiv_eq_zero_of_notMem_vars
  intro hi
  rw [MvPolynomial.mem_vars_iff_mem_support] at hi
  obtain ⟨d, hd, hid⟩ := hi
  rw [mem_gradingW] at hp
  have hwd : Finsupp.weight weightFn d = w := hp (MvPolynomial.mem_support_iff.mp hd)
  have hle : weightFn i ≤ Finsupp.weight weightFn d :=
    Finsupp.le_weight_of_ne_zero' (w := weightFn) (Finsupp.mem_support_iff.mp hid)
  omega

/-- **`osc k n` is grading-covariant**: it shifts weight by `-n`, i.e.
`osc k n : F_w → F_{w-n}` (in the `ℤ`-extended grading; the target is `⊥` when `w-n < 0`,
where `osc k n p = 0`). -/
theorem osc_mem_gradingZ (k : ℂ) (n : ℤ) {w : ℕ} {p : Fock} (hp : p ∈ gradingW w) :
    osc k n p ∈ gradingZ ((w : ℤ) - n) := by
  rcases lt_trichotomy n 0 with hn | hn | hn
  · -- creation: weight rises by `-n`, lands in non-negative weight
    have h := osc_neg_weight k hn hp
    have hcast : ((w + (-n).toNat : ℕ) : ℤ) = (w : ℤ) - n := by
      rw [Nat.cast_add, Int.toNat_of_nonneg (by omega)]; ring
    rw [← hcast]; exact mem_gradingZ_of_gradingW h
  · -- n = 0: `osc k 0 = 0`
    subst hn
    rw [osc_zero, LinearMap.zero_apply, sub_zero]
    exact zero_mem_gradingZ _
  · -- annihilation
    by_cases hwn : (n : ℤ) ≤ w
    · -- enough weight: `osc k n : F_w → F_{w-n}`
      have h := osc_pos_weight k hn (w := w) (w' := w - n.toNat)
        (by omega) hp
      have hcast : ((w - n.toNat : ℕ) : ℤ) = (w : ℤ) - n := by
        rw [Nat.cast_sub (by omega), Int.toNat_of_nonneg (le_of_lt hn)]
      rw [← hcast]; exact mem_gradingZ_of_gradingW h
    · -- not enough weight: result is `0`, target is `⊥`
      have hpd : pderiv (n - 1).toNat p = 0 := by
        apply pderiv_eq_zero_of_weight_lt hp
        rw [weightFn_apply, show (n - 1).toNat + 1 = n.toNat from by omega]
        omega
      rw [osc_apply_pos k hn, hpd, smul_zero, smul_zero]
      exact zero_mem_gradingZ _

/-! ### The basic graded fields: `idField` (weight 0) and `genField k i` (weight `i+1`) -/

/-- The identity field `Y(1,z)` is a graded field of weight `0`. -/
theorem idField_gradedField : GradedField (idField : FormalDist (End ℂ Fock)) 0 := by
  intro j w p hp
  rw [idField_apply]
  by_cases hj : j = 0
  · rw [if_pos hj, LinearMap.id_apply, hj]
    simpa using mem_gradingZ_of_gradingW hp
  · rw [if_neg hj, LinearMap.zero_apply]
    exact zero_mem_gradingZ _

/-- The `zʲ`-coefficient of `genField k i` is a falling-factorial (ℂ) times an integer
falling-factorial smul of the oscillator `osc k (-j-1-i)`. -/
theorem genField_coeff' (k : ℂ) (i : ℕ) (j : ℤ) :
    (genField k i) j =
      (i.factorial : ℂ)⁻¹ •
        ((∏ p ∈ Finset.range i, (-(-j - 1 - (p : ℤ)))) • osc k (-j - 1 - i)) := by
  have hmode : (genField k i) j = mode (genField k i) (-j - 1) := by
    rw [mode_apply]; congr 1; ring
  rw [hmode, genField, mode_smul, dcurrent_mode]

/-- **`genField k i` is a graded field of weight `i+1`** (`= Y(a₋(i+1)1, z)`): each coefficient
shifts weight by `(i+1) + j`, via the oscillator-grading `osc k (-j-1-i) : F_w → F_{w+j+1+i}`. -/
theorem genField_gradedField (k : ℂ) (i : ℕ) :
    GradedField (genField k i) ((i : ℤ) + 1) := by
  intro j w p hp
  rw [genField_coeff']
  -- merge the two scalars into one `ℂ`-scalar
  set c : ℂ := (i.factorial : ℂ)⁻¹ *
    (((∏ p ∈ Finset.range i, (-(-j - 1 - (p : ℤ)))) : ℤ) : ℂ) with hc
  have hcoeff : (i.factorial : ℂ)⁻¹ •
        ((∏ p ∈ Finset.range i, (-(-j - 1 - (p : ℤ)))) • osc k (-j - 1 - i))
      = c • osc k (-j - 1 - i) := by
    rw [hc, mul_smul, Int.cast_smul_eq_zsmul]
  rw [hcoeff, LinearMap.smul_apply]
  have hosc : osc k (-j - 1 - i) p ∈ gradingZ ((w : ℤ) - (-j - 1 - i)) :=
    osc_mem_gradingZ k (-j - 1 - i) hp
  have htgt : ((w : ℤ) - (-j - 1 - i)) = (i : ℤ) + 1 + w + j := by ring
  rw [htgt] at hosc
  exact (gradingZ _).smul_mem _ hosc

/-! ### The normal-ordered product of graded fields is a graded field

If `a` is graded of weight `Da` and `b` of weight `Db`, then `:a(z)b(z):` is graded of weight
`Da + Db`.  Each diagonal summand `normalOrdered a b m (s-m) p` lands in the same fixed piece
`F_{Da+Db+w+s}` (the `m`-dependence cancels: `b` contributes `Db+w+(s-m)`, then `a` adds
`Da+·+m`), so the finite diagonal sum stays in that piece. -/

/-- A finite-support finsum of submodule elements lies in the submodule. -/
theorem finsum_mem_submodule {ι : Type*} (S : Submodule ℂ Fock) (g : ι → Fock)
    (hfin : (Function.support g).Finite) (hmem : ∀ i, g i ∈ S) : (∑ᶠ i, g i) ∈ S := by
  rw [finsum_eq_finsetSum_of_support_subset g (s := hfin.toFinset)
    (by rw [hfin.coe_toFinset])]
  exact Submodule.sum_mem _ (fun i _ => hmem i)

/-- The `gradingZ`-input form of `GradedField`: a graded field of weight `D` sends a `gradingZ`
piece `F_d` to `F_{D+d+j}` (the negative-`d` inputs are `0`). -/
theorem GradedField.mem_gradingZ {a : FormalDist (End ℂ Fock)} {D : ℤ} (hga : GradedField a D)
    (j d : ℤ) {p : Fock} (hp : p ∈ gradingZ d) : a j p ∈ gradingZ (D + d + j) := by
  rcases lt_or_ge d 0 with hd | hd
  · rw [gradingZ_of_neg hd, Submodule.mem_bot] at hp
    rw [hp, map_zero]; exact zero_mem_gradingZ _
  · rw [gradingZ_of_nonneg hd] at hp
    have := hga j d.toNat p hp
    rwa [Int.toNat_of_nonneg hd] at this

/-- **The normal-ordered product of graded fields is a graded field**, with weights adding:
`GradedField a Da → GradedField b Db → GradedField (:a b:) (Da+Db)`. -/
theorem GradedField.nprod {a b : FormalDist (End ℂ Fock)} (ha : IsField a) (hb : IsField b)
    {Da Db : ℤ} (hga : GradedField a Da) (hgb : GradedField b Db) :
    GradedField (nprod ha hb) (Da + Db) := by
  intro s w p hp
  rw [nprod_apply]
  apply finsum_mem_submodule
  · exact normalOrdered_diag_support_finite ha hb s p
  · intro m
    rw [normalOrdered_apply]
    have hpz : p ∈ gradingZ (w : ℤ) := mem_gradingZ_of_gradingW hp
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0]
      show a m (b (s - m) p) ∈ gradingZ (Da + Db + w + s)
      have hb' := hgb.mem_gradingZ (s - m) (w : ℤ) hpz
      have ha' := hga.mem_gradingZ m (Db + w + (s - m)) hb'
      have htgt : Da + (Db + (w : ℤ) + (s - m)) + m = Da + Db + w + s := by ring
      rwa [htgt] at ha'
    · rw [if_neg h0]
      show b (s - m) (a m p) ∈ gradingZ (Da + Db + w + s)
      have ha' := hga.mem_gradingZ m (w : ℤ) hpz
      have hb' := hgb.mem_gradingZ (s - m) (Da + w + m) ha'
      have htgt : Db + (Da + (w : ℤ) + m) + (s - m) = Da + Db + w + s := by ring
      rwa [htgt] at hb'

/-! ### Words and monomials: `Yword`/`Ymon` are graded fields of weight = the state weight -/

/-- The (ℕ-valued) weight of a word `l = [i₁,…,iᵣ]`: the sum of the generator weights
`∑ (iₜ+1)`. -/
def wordWeightN (l : List ℕ) : ℕ := (l.map (fun i => i + 1)).sum

/-- The weight of a word, as an integer (for the `ℤ`-graded field statement). -/
def wordWeight (l : List ℕ) : ℤ := (wordWeightN l : ℤ)

@[simp] theorem wordWeightN_nil : wordWeightN [] = 0 := rfl

@[simp] theorem wordWeight_nil : wordWeight [] = 0 := rfl

theorem wordWeightN_cons (i : ℕ) (rest : List ℕ) :
    wordWeightN (i :: rest) = (i + 1) + wordWeightN rest := by
  simp only [wordWeightN, List.map_cons, List.sum_cons]

theorem wordWeight_cons (i : ℕ) (rest : List ℕ) :
    wordWeight (i :: rest) = ((i : ℤ) + 1) + wordWeight rest := by
  rw [wordWeight, wordWeight, wordWeightN_cons]; push_cast; ring

/-- **`Yword k l` is a graded field of weight `wordWeight l`** (induction over the word: the base
case is the identity field, weight `0`; the step is `nprod` with a `genField`, adding `i+1`). -/
theorem Yword_gradedField (k : ℂ) : ∀ l : List ℕ, GradedField (Yword k l) (wordWeight l)
  | [] => by rw [Yword_nil, wordWeight_nil]; exact idField_gradedField
  | (i :: rest) => by
      rw [Yword_cons, wordWeight_cons]
      exact GradedField.nprod (genField_isField k i) (Yword_isField k rest)
        (genField_gradedField k i) (Yword_gradedField k rest)

/-! ### The monomial weight matches `wordWeight (monoWord a)`

For a monomial exponent vector `a : ℕ →₀ ℕ`, the state weight is `∑ aᵢ·(i+1) = weight weightFn a`,
which equals `wordWeight (monoWord a)` (each `i` is replicated `aᵢ` times). -/

/-- `wordWeightN` is additive over append. -/
theorem wordWeightN_append (l₁ l₂ : List ℕ) :
    wordWeightN (l₁ ++ l₂) = wordWeightN l₁ + wordWeightN l₂ := by
  rw [wordWeightN, wordWeightN, wordWeightN, List.map_append, List.sum_append]

/-- `wordWeightN` of a flatMap over a list is the list-sum of the per-element weights. -/
theorem wordWeightN_flatMap (L : List ℕ) (g : ℕ → List ℕ) :
    wordWeightN (L.flatMap g) = (L.map (fun i => wordWeightN (g i))).sum := by
  induction L with
  | nil => simp [wordWeightN]
  | cons i rest ih =>
    rw [List.flatMap_cons, wordWeightN_append, List.map_cons, List.sum_cons, ih]

/-- `wordWeightN (List.replicate n i) = n·(i+1)`. -/
theorem wordWeightN_replicate (n i : ℕ) :
    wordWeightN (List.replicate n i) = n * (i + 1) := by
  rw [wordWeightN, List.map_replicate, List.sum_replicate, smul_eq_mul]

/-- `wordWeightN (monoWord a) = ∑_{i∈a.support} aᵢ·(i+1)`, the weighted degree of the monomial. -/
theorem wordWeightN_monoWord (a : ℕ →₀ ℕ) :
    wordWeightN (monoWord a) = ∑ i ∈ a.support, (a i * (i + 1)) := by
  classical
  rw [monoWord, wordWeightN_flatMap]
  have hmap : (a.support.sort (· ≤ ·)).map (fun i => wordWeightN (List.replicate (a i) i))
       = (a.support.sort (· ≤ ·)).map (fun i => (a i * (i + 1))) :=
    List.map_congr_left (fun i _ => wordWeightN_replicate (a i) i)
  rw [hmap]
  -- `List.sum` over `s.sort` = `Multiset.sum` over `s.val` = `Finset.sum`
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.sort_eq]
  rfl

/-- The word weight of `monoWord a` is the weighted degree `weight weightFn a` of the monomial. -/
theorem wordWeightN_monoWord_eq_weight (a : ℕ →₀ ℕ) :
    wordWeightN (monoWord a) = Finsupp.weight weightFn a := by
  rw [wordWeightN_monoWord, Finsupp.weight_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [weightFn_apply, smul_eq_mul]

/-- **`Ymon k a` is a graded field of the monomial's weighted degree** `weight weightFn a`. -/
theorem Ymon_gradedField (k : ℂ) (a : ℕ →₀ ℕ) :
    GradedField (Ymon k a) ((Finsupp.weight weightFn a : ℕ) : ℤ) := by
  rw [Ymon, ← wordWeightN_monoWord_eq_weight]
  exact Yword_gradedField k (monoWord a)

/-! ## VA1 — the grading axiom for the general vertex operator `Y k u`

Assemble the monomial-level grading into the full statement: for `u ∈ F_{ku}` and `v ∈ F_ℓ`,
`u₍ₙ₎ v = mode (Y k u) n v ∈ F_{ku+ℓ-n-1}`.  Since `u` is weighted-homogeneous of degree `ku`,
each monomial `monomial a c` of `u` has `weight weightFn a = ku`, so `Ymon k a` is graded of
weight `ku`; the linear combination `Y k u` is then graded of weight `ku`, and the mode form
`(set j = -n-1)` gives the VA1 grading law. -/

/-- A `gradingW`-membership of a monomial pins its weighted degree (for `c ≠ 0`). -/
theorem weight_of_monomial_mem_gradingW {a : ℕ →₀ ℕ} {c : ℂ} (hc : c ≠ 0) {w : ℕ}
    (hmem : (monomial a c : Fock) ∈ gradingW w) : Finsupp.weight weightFn a = w := by
  rw [mem_gradingW] at hmem
  apply hmem
  rwa [MvPolynomial.coeff_monomial, if_pos rfl]

/-- **`Y k u` is a graded field of weight `w`** whenever `u ∈ F_w`: the linear combination of the
monomial fields, each graded of the same weight `w` (the weighted degree of every monomial of the
homogeneous `u`). -/
theorem Y_gradedField_of_mem (k : ℂ) {w : ℕ} {u : Fock} (hu : u ∈ gradingW w) :
    GradedField (Y k u) (w : ℤ) := by
  classical
  -- `Y k u = ∑ a ∈ u.support, (u a) • Ymon k a`, each `Ymon k a` graded of weight `w`
  intro j w' p hp
  rw [show Y k u = Finsupp.linearCombination ℂ (Ymon k) u from rfl,
      Finsupp.linearCombination_apply, Finsupp.sum]
  show (∑ a ∈ u.support, (u a) • Ymon k a) j p ∈ gradingZ ((w : ℤ) + w' + j)
  have hsum : (∑ a ∈ u.support, (u a) • Ymon k a) j p
      = ∑ a ∈ u.support, ((u a) • Ymon k a) j p := by
    rw [show ((∑ a ∈ u.support, (u a) • Ymon k a) j : End ℂ Fock)
          = ∑ a ∈ u.support, ((u a) • Ymon k a) j from
        (Finset.sum_apply (s := u.support) (g := fun a => (u a) • Ymon k a) j),
      LinearMap.sum_apply]
  rw [hsum]
  apply Submodule.sum_mem
  intro a ha
  show ((u a) • Ymon k a) j p ∈ gradingZ ((w : ℤ) + w' + j)
  have heval : ((u a) • Ymon k a) j p = (u a) • (Ymon k a j p) := rfl
  rw [heval]
  -- the coefficient of `u` at `a` is the monomial coefficient; `u` is homogeneous so weight a = w
  have hcoeff : u.coeff a ≠ 0 := by
    rw [MvPolynomial.coeff] -- `u a = u.coeff a`
    exact Finsupp.mem_support_iff.mp ha
  have hwa : Finsupp.weight weightFn a = w := by
    rw [mem_gradingW] at hu; exact hu hcoeff
  have hYmon : (Ymon k a) j p ∈ gradingZ (((Finsupp.weight weightFn a : ℕ) : ℤ) + w' + j) :=
    Ymon_gradedField k a j w' p hp
  rw [hwa] at hYmon
  exact (gradingZ _).smul_mem _ hYmon

/-- **VA1 (grading), the structure-field form** with the `ℤ`-extended grading `gradingZ`:
for `u ∈ F_k` and `v ∈ F_ℓ` (any `k, ℓ : ℤ`), `u₍ₙ₎v = mode (Y kk u) n v ∈ F_{k+ℓ-n-1}`.
This is exactly `PreVertexAlgebra.grading_mode` for the Heisenberg model, with the convention that
`gradingZ` is `⊥` in negative degree (matching VOA4 positivity). -/
theorem va1_grading_mode (kk : ℂ) {k ℓ : ℤ} (u : Fock) (hu : u ∈ gradingZ k)
    (v : Fock) (hv : v ∈ gradingZ ℓ) (n : ℤ) :
    mode (Y kk u) n v ∈ gradingZ (k + ℓ - n - 1) := by
  rcases lt_or_ge k 0 with hk | hk
  · -- `u = 0`, so `Y kk u = 0` and the mode is `0`
    rw [gradingZ_of_neg hk, Submodule.mem_bot] at hu
    rw [hu, map_zero, mode_apply]
    show (0 : FormalDist (End ℂ Fock)) (-n - 1) v ∈ _
    rw [show (0 : FormalDist (End ℂ Fock)) (-n - 1) = 0 from rfl, LinearMap.zero_apply]
    exact zero_mem_gradingZ _
  · -- `u ∈ F_{k.toNat}`, so `Y kk u` is graded of weight `k`; evaluate the coefficient form
    rw [gradingZ_of_nonneg hk] at hu
    have hgf := Y_gradedField_of_mem kk hu  -- `GradedField (Y kk u) (k.toNat)`
    rw [mode_apply]
    have := hgf.mem_gradingZ (-n - 1) ℓ hv
    rw [Int.toNat_of_nonneg hk] at this
    have htgt : k + ℓ + (-n - 1) = k + ℓ - n - 1 := by ring
    rwa [htgt] at this

/-! ## Axiom audit -/


/-! ## Role in the assembly of `VertexOperatorAlgebra Fock` (Heisenberg / free boson, level `k≠0`)

The grading is `gradingZ : ℤ → Submodule ℂ Fock` (`gradingW` on `ℕ`, `⊥` below); `Y := Y k`,
`vacuum := vacuum`, `conformalVector := ω k`, `centralCharge := 1`.

This file supplies the `grading` field (`gradingZ`), the VA1 grading axiom (`va1_grading_mode`),
VA5 regularity (`va5_regularity`) and VOA4b positivity (`gradingZ_of_neg`).  The vacuum,
creation, locality and conformal fields come from `HeisenbergVertex`, `HeisenbergVirasoro` and
the other `Heisenberg*` modules; the instance itself, `heisenbergVOA k hk`, is assembled in
`Examples.HeisenbergVOA`.
-/

end VOA

-- supplementary axiom audit (chain integrity)
namespace VOA
end VOA
