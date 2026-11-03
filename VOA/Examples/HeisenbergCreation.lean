/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.HeisenbergVertex

/-!
# FRONT A — VA3 general creation (probe)
-/

namespace VOA

open scoped BigOperators
open MvPolynomial
open Module (End)

/-- Raw `z^s`-coefficient of `dcurrent k j` is a falling-factorial multiple of the
oscillator `osc k (-(s+j)-1)`. -/
theorem dcurrent_coeff (k : ℂ) (j : ℕ) (s : ℤ) :
    dcurrent k j s = (∏ i ∈ Finset.range j, ((s : ℤ) + 1 + i)) • osc k (-(s + j) - 1) := by
  have h := dcurrent_mode k j (-s - 1)
  rw [mode_apply, show -(-s - 1) - 1 = s from by ring] at h
  rw [h]
  rw [show (-s - 1 : ℤ) - j = -(s + j) - 1 from by ring]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by ring

/-- Raw `z^s`-coefficient of `genField k i`, with the scalar as a single `ℂ`-coefficient. -/
theorem genField_coeff (k : ℂ) (i : ℕ) (s : ℤ) :
    genField k i s
      = (((∏ l ∈ Finset.range i, ((s : ℤ) + 1 + l) : ℤ) : ℂ) * (i.factorial : ℂ)⁻¹)
          • osc k (-(s + i) - 1) := by
  show ((i.factorial : ℂ)⁻¹ • dcurrent k i) s = _
  show (i.factorial : ℂ)⁻¹ • dcurrent k i s = _
  rw [dcurrent_coeff,
    ← Int.cast_smul_eq_zsmul ℂ (∏ l ∈ Finset.range i, ((s : ℤ) + 1 + l)) (osc k (-(s + i) - 1)),
    smul_smul, mul_comm]

-- PROBE: genField on vacuum vanishes when s+i < 0
example (k : ℂ) (i : ℕ) (s : ℤ) (hs : s + i < 0) : genField k i s vacuum = 0 := by
  rw [genField_coeff, LinearMap.smul_apply, osc_vacuum k _ (by omega), smul_zero]

/-- The falling factorial product at `s=0` is `i!`. -/
theorem prod_range_zero_eq_factorial (i : ℕ) :
    (∏ l ∈ Finset.range i, ((0:ℤ) + 1 + l)) = (i.factorial : ℤ) := by
  induction i with
  | zero => simp
  | succ p ih => rw [Finset.prod_range_succ, ih, Nat.factorial_succ]; push_cast; ring

/-- `genField k i 0 vacuum = X i`. -/
theorem genField_creation_zero (k : ℂ) (i : ℕ) : genField k i 0 vacuum = X i := by
  rw [genField_coeff, LinearMap.smul_apply, prod_range_zero_eq_factorial,
    osc_apply_neg k (by omega), vacuum, mul_one]
  rw [show (-(-(0 + (i:ℤ)) - 1) - 1).toNat = (i:ℕ) from by omega]
  rw [show ((i.factorial : ℤ) : ℂ) * (i.factorial : ℂ)⁻¹ = 1 from by
    rw [Int.cast_natCast]; exact mul_inv_cancel₀ (by exact_mod_cast (Nat.factorial_pos i).ne')]
  rw [one_smul]

/-- `genField k i s vacuum = 0` when `s + i < 0`. -/
theorem genField_creation_neg (k : ℂ) (i : ℕ) {s : ℤ} (hs : s + i < 0) :
    genField k i s vacuum = 0 := by
  rw [genField_coeff, LinearMap.smul_apply, osc_vacuum k _ (by omega), smul_zero]

/-- `genField k i s vacuum = (scalar) • X (s+i)` for `s + i ≥ 0`: a single creation variable. -/
theorem genField_vacuum_coeff (k : ℂ) (i : ℕ) {s : ℤ} (hs : 0 ≤ s + i) :
    genField k i s vacuum
      = (((∏ l ∈ Finset.range i, ((s : ℤ) + 1 + l) : ℤ) : ℂ) * (i.factorial : ℂ)⁻¹)
          • X (s + i).toNat := by
  rw [genField_coeff, LinearMap.smul_apply, osc_apply_neg k (by omega), vacuum, mul_one]
  congr 2
  omega

/-! ## §A  The `nprod_vacuum` decomposition (regularity threading)

For two fields `a, b` with `b` regular on the vacuum (`b l 1 = 0` for `l < 0`), the
same-variable normal product on the vacuum collapses its `m ≥ 0` half: for `j < 0` only the
`m < 0` summands survive, and for `j = 0` the `m ≥ 0` half contributes the single term
`a₀(b₀1)`.  This is the recursion the creation property threads through each `nprod` layer. -/

/-- **`nprod`-on-vacuum, `j < 0` half**: the `m ≥ 0` summands of `:a(z)b(z): 1` all vanish (the
inner `b(j-m)1` has `j - m < 0`), leaving only the `m < 0` (creation-of-`a`) summands. -/
theorem nprod_vacuum_lt {a b : FormalDist (End ℂ Fock)} (ha : IsField a) (hb : IsField b)
    (hb_lt : ∀ l : ℤ, l < 0 → b l vacuum = 0) {j : ℤ} (hj : j < 0) :
    nprod ha hb j vacuum = ∑ᶠ m : ℤ, (if m < 0 then b (j - m) (a m vacuum) else 0) := by
  rw [nprod_apply]
  refine finsum_congr fun m => ?_
  rw [normalOrdered_apply]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0, if_neg (by omega : ¬ m < 0), Module.End.mul_apply]
    rw [hb_lt (j - m) (by omega), map_zero]
  · rw [if_neg h0, if_pos (by omega : m < 0), Module.End.mul_apply]

/-- **`nprod`-on-vacuum, `j = 0` half**: the `m ≥ 0` summands collapse to the single `m = 0`
term `a₀(b₀1)`, plus the `m < 0` (creation-of-`a`) summands. -/
theorem nprod_vacuum_zero {a b : FormalDist (End ℂ Fock)} (ha : IsField a) (hb : IsField b)
    (hb_lt : ∀ l : ℤ, l < 0 → b l vacuum = 0) :
    nprod ha hb 0 vacuum
      = a 0 (b 0 vacuum) + ∑ᶠ m : ℤ, (if m < 0 then b (0 - m) (a m vacuum) else 0) := by
  rw [nprod_apply]
  -- split off the m = 0 term and the m > 0 (vanishing) terms from the m < 0 terms
  have key : ∀ m : ℤ, normalOrdered a b m (0 - m) vacuum
      = (if m < 0 then b (0 - m) (a m vacuum) else 0) + (if m = 0 then a 0 (b 0 vacuum) else 0) := by
    intro m
    rw [normalOrdered_apply]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0, if_neg (by omega : ¬ m < 0), zero_add, Module.End.mul_apply]
      rcases h0.lt_or_eq with hpos | hz
      · rw [if_neg (by omega : ¬ m = 0)]
        rw [hb_lt (0 - m) (by omega), map_zero]
      · rw [← hz, if_pos rfl, sub_zero]
    · rw [if_neg h0, if_pos (by omega : m < 0),
        if_neg (by omega : ¬ m = 0), add_zero, Module.End.mul_apply]
  rw [finsum_congr key]
  have hfin1 : (Function.support (fun m : ℤ => if m < 0 then b (0 - m) (a m vacuum) else 0)).Finite := by
    obtain ⟨B, hB⟩ := ha vacuum
    apply Set.Finite.subset (Set.finite_Icc B (-1))
    intro m hm
    rw [Function.mem_support] at hm
    rw [Set.mem_Icc]
    by_cases h0 : m < 0
    · rw [if_pos h0] at hm
      refine ⟨?_, by omega⟩
      by_contra hlt
      exact hm (by rw [hB m (by omega), map_zero])
    · exact absurd (by rw [if_neg h0] at hm; exact hm) (by simp)
  have hfin2 : (Function.support (fun m : ℤ => if m = 0 then a 0 (b 0 vacuum) else 0)).Finite := by
    apply Set.Finite.subset (Set.finite_singleton 0)
    intro m hm
    rw [Function.mem_support] at hm
    by_contra hne
    exact hm (by rw [if_neg (by simpa using hne)])
  rw [finsum_add_distrib hfin1 hfin2]
  rw [add_comm]
  congr 1
  rw [finsum_eq_single (fun m => if m = 0 then a 0 (b 0 vacuum) else 0) 0
      (fun m hm => if_neg hm), if_pos rfl]

/-! ## §B  The creation property for fields whose left factor's negative modes kill the vacuum

When `a`'s negative-`m` coefficients annihilate the vacuum (`a m 1 = 0` for `m < 0`), the
`m < 0` half of the `nprod_vacuum` decomposition vanishes identically, so `:a(z)b(z): 1`
inherits `b`'s regularity and creates `a₀(b₀1)`.  This is the clean recursion that closes
for the lowest generator `genField k 0 = α(z)` (whose negative modes are the creation
oscillators `aₘ`, `m ≤ -1`, which act as `osc k (-m-1)` with `-m-1 ≥ 0`, killing the vacuum)
and hence for every word in that single generator. -/

/-- If `a`'s negative coefficients kill the vacuum, the `m < 0` half of the decomposition is
`0` and `nprod a b 1` inherits the regularity of `b`: `(nprod a b) j 1 = 0` for `j < 0`. -/
theorem nprod_creation_lt {a b : FormalDist (End ℂ Fock)} (ha : IsField a) (hb : IsField b)
    (hb_lt : ∀ l : ℤ, l < 0 → b l vacuum = 0) (ha_neg : ∀ m : ℤ, m < 0 → a m vacuum = 0)
    {j : ℤ} (hj : j < 0) : nprod ha hb j vacuum = 0 := by
  rw [nprod_vacuum_lt ha hb hb_lt hj]
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  by_cases h0 : m < 0
  · rw [if_pos h0, ha_neg m h0, map_zero]
  · rw [if_neg h0]

/-- If `a`'s negative coefficients kill the vacuum, `nprod a b` creates `a₀(b₀1)` at `z⁰`. -/
theorem nprod_creation_zero {a b : FormalDist (End ℂ Fock)} (ha : IsField a) (hb : IsField b)
    (hb_lt : ∀ l : ℤ, l < 0 → b l vacuum = 0) (ha_neg : ∀ m : ℤ, m < 0 → a m vacuum = 0) :
    nprod ha hb 0 vacuum = a 0 (b 0 vacuum) := by
  rw [nprod_vacuum_zero ha hb hb_lt]
  rw [finsum_eq_zero_of_forall_eq_zero (fun m => ?_), add_zero]
  by_cases h0 : m < 0
  · rw [if_pos h0, ha_neg m h0, map_zero]
  · rw [if_neg h0]

/-- The falling-factorial coefficient `∏_{l<i}(j+1+l)` of `genField k i` vanishes whenever
`-i ≤ j ≤ -1`: the factor at `l = -j-1 ∈ {0,…,i-1}` is `0`.  This is what makes *every*
generator field regular on the vacuum across the whole window `-i ≤ j ≤ -1`. -/
theorem genField_falling_factorial_eq_zero (i : ℕ) {j : ℤ} (hj1 : -(i : ℤ) ≤ j) (hj2 : j ≤ -1) :
    (∏ l ∈ Finset.range i, ((j : ℤ) + 1 + l)) = 0 := by
  apply Finset.prod_eq_zero (i := (-j - 1).toNat)
  · rw [Finset.mem_range]; omega
  · push_cast [Int.toNat_of_nonneg (show (0:ℤ) ≤ -j - 1 from by omega)]; ring

/-- **The negative coefficients of EVERY generator field `genField k i` kill the vacuum**:
`genField k i m 1 = 0` for `m < 0`.  Either the falling-factorial scalar vanishes (window
`-i ≤ m ≤ -1`, factor `l = -m-1`) or the oscillator `osc k (-(m+i)-1)` annihilates the
vacuum (`m ≤ -i-1`, where `-(m+i)-1 ≥ 0`).  This is the fact that makes the `m < 0` half of
the `nprod_vacuum` decomposition vanish for every word — the creation property closes in full
generality, *not* just for the lowest generator. -/
theorem genField_neg_vacuum (k : ℂ) (i : ℕ) {m : ℤ} (hm : m < 0) :
    genField k i m vacuum = 0 := by
  rw [genField_coeff, LinearMap.smul_apply]
  by_cases hwin : -(i : ℤ) ≤ m
  · rw [genField_falling_factorial_eq_zero i hwin (by omega)]; simp
  · rw [osc_vacuum k _ (by omega), smul_zero]

/-- The negative coefficients of the lowest generator field `genField k 0 = α(z)` kill the
vacuum (the `i = 0` instance of `genField_neg_vacuum`). -/
theorem genField_zero_neg_vacuum (k : ℂ) {m : ℤ} (hm : m < 0) :
    genField k 0 m vacuum = 0 := genField_neg_vacuum k 0 hm

/-! ## §C  Creation for the length-1 words and the `a₋₁`-tower

The length-1 word `[i]` has `Yword k [i] = genField k i` (the rest is the identity field,
`nprod_idField`), so its creation is the `genField` computation directly — covering every
single generator `a₋(i+1)1`.  The words `replicate n 0` (the `a₋₁`-tower `(a₋₁)ⁿ1 = X₀ⁿ`)
close under the `nprod_creation_*` recursion, since `genField k 0`'s negative modes kill the
vacuum (`genField_zero_neg_vacuum`). -/

/-- `Yword k [i] = genField k i`. -/
theorem Yword_singleton (k : ℂ) (i : ℕ) : Yword k [i] = genField k i := by
  have h := nprod_idField (genField_isField k i)
  rw [Yword_cons]
  exact h

/-- **Creation, length-1, `j < 0`**: `Yword k [i] j 1 = 0` for `j < 0` — every single
generator `a₋(i+1)1` is created without a negative-power singularity. -/
theorem Yword_singleton_creation_lt (k : ℂ) (i : ℕ) {j : ℤ} (hj : j < 0) :
    Yword k [i] j vacuum = 0 := by
  rw [Yword_singleton]; exact genField_neg_vacuum k i hj

/-- **Creation, length-1, `z⁰`**: `Yword k [i] 0 1 = X i = a₋(i+1)1`. -/
theorem Yword_singleton_creation_zero (k : ℂ) (i : ℕ) :
    Yword k [i] 0 vacuum = X i := by
  rw [Yword_singleton, genField_creation_zero]

/-! ## §D  The full general creation property (every word)

Because `genField k i m 1 = 0` for *every* `m < 0` (`genField_neg_vacuum`), the `m < 0` half
of the `nprod_vacuum` decomposition vanishes for every left factor `genField k i`.  Hence the
`nprod_creation_*` recursion closes over an arbitrary word `l`, with no surviving commutator
sum: `Yword k l` is regular on the vacuum and creates the monomial `∏ⱼ X_{lⱼ}`. -/

/-- The `z⁰`-coefficient operator of a generator field is multiplication by `X i`:
`genField k i 0 = X i · (-)` (the falling-factorial scalar is `i!`, cancelling `(i!)⁻¹`).
This is the operator identity behind "`nprod` creates `X i · (rest state)`". -/
theorem genField_zero_apply (k : ℂ) (i : ℕ) (p : Fock) : genField k i 0 p = X i * p := by
  rw [genField_coeff, LinearMap.smul_apply, prod_range_zero_eq_factorial,
    osc_apply_neg k (by omega : -(0 + (i:ℤ)) - 1 < 0)]
  rw [show (-(-(0 + (i:ℤ)) - 1) - 1).toNat = (i:ℕ) from by omega]
  rw [show ((i.factorial : ℤ) : ℂ) * (i.factorial : ℂ)⁻¹ = 1 from by
    rw [Int.cast_natCast]; exact mul_inv_cancel₀ (by exact_mod_cast (Nat.factorial_pos i).ne')]
  rw [one_smul]

/-- The monomial state created by a word `[i₁,…,iᵣ]`: the product `X i₁ · X i₂ ⋯ 1`. -/
noncomputable def wordState (l : List ℕ) : Fock := (l.map (fun i => (X i : Fock))).prod

@[simp] theorem wordState_nil : wordState [] = (1 : Fock) := rfl

@[simp] theorem wordState_cons (i : ℕ) (rest : List ℕ) :
    wordState (i :: rest) = X i * wordState rest := rfl

/-- **VA3, general creation — the two clauses together, for every word `l`.**  By induction on
`l`, threading `nprod_vacuum` through each `nprod` layer; the `m < 0` half is empty since every
generator's negative modes kill the vacuum (`genField_neg_vacuum`). -/
theorem Yword_creation (k : ℂ) (l : List ℕ) :
    (∀ j : ℤ, j < 0 → Yword k l j vacuum = 0) ∧ Yword k l 0 vacuum = wordState l := by
  induction l with
  | nil =>
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [Yword_nil, idField_apply, if_neg (by omega)]; rfl
    · rw [Yword_nil, idField_apply, if_pos rfl, wordState_nil]; rfl
  | cons i rest ih =>
    obtain ⟨ih_lt, ih_zero⟩ := ih
    have ha_neg : ∀ m : ℤ, m < 0 → genField k i m vacuum = 0 := fun m hm =>
      genField_neg_vacuum k i hm
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [Yword_cons]
      exact nprod_creation_lt (genField_isField k i) (Yword_isField k rest) ih_lt ha_neg hj
    · rw [Yword_cons,
        nprod_creation_zero (genField_isField k i) (Yword_isField k rest) ih_lt ha_neg]
      rw [ih_zero, genField_zero_apply, wordState_cons]

/-- **VA3 / general creation, `j < 0`**: `Yword k l j 1 = 0` for `j < 0`, every word `l`. -/
theorem Yword_creation_lt (k : ℂ) (l : List ℕ) {j : ℤ} (hj : j < 0) :
    Yword k l j vacuum = 0 := (Yword_creation k l).1 j hj

/-- **VA3 / general creation, `z⁰`**: `Yword k l 0 1 = ∏ⱼ X_{lⱼ}`, every word `l`. -/
theorem Yword_creation_zero (k : ℂ) (l : List ℕ) :
    Yword k l 0 vacuum = wordState l := (Yword_creation k l).2

/-! ## §E  Creation for monomial fields and the assembled VA3 statement -/

/-- The created state of `monoWord a` is the monomial `∏ Xᵢ^{aᵢ}` of `a`.  (`monoWord a`
flattens, in increasing `i`, `a i` copies of each variable `i`; its `wordState` is the product
of the corresponding `X`'s, which is `monomial a 1`.) -/
theorem wordState_monoWord (a : ℕ →₀ ℕ) : wordState (monoWord a) = monomial a 1 := by
  rw [wordState, monoWord]
  -- pass to multisets: list-prod of a map of a flatMap = multiset-prod of a bind
  rw [← Multiset.prod_coe, ← Multiset.map_coe, ← Multiset.coe_bind,
    Finset.sort_eq, Multiset.map_bind, Multiset.prod_bind]
  -- the inner product over `replicate (a i) i` collapses to `X i ^ a i`
  have hinner : ∀ i : ℕ,
      (Multiset.map (fun i => (X i : Fock)) (Multiset.replicate (a i) i)).prod = X i ^ a i := by
    intro i; rw [Multiset.map_replicate, Multiset.prod_replicate]
  simp only [Multiset.coe_replicate, hinner]
  -- `∏_{i ∈ support} X i ^ a i = monomial a 1`, with the support sum = `a` as Finsupp.prod
  rw [show (Multiset.map (fun i => (X i : Fock) ^ a i) a.support.val).prod
        = ∏ i ∈ a.support, (X i : Fock) ^ a i from rfl]
  rw [monomial_eq, map_one, one_mul, Finsupp.prod]

/-- **VA3 / creation for monomial fields, `j < 0`**: `Ymon k a j 1 = 0` for `j < 0`. -/
theorem Ymon_creation_lt (k : ℂ) (a : ℕ →₀ ℕ) {j : ℤ} (hj : j < 0) :
    Ymon k a j vacuum = 0 := Yword_creation_lt k (monoWord a) hj

/-- **VA3 / creation for monomial fields, `z⁰`**: `Ymon k a 0 1 = ∏ Xᵢ^{aᵢ} = monomial a 1`. -/
theorem Ymon_creation_zero (k : ℂ) (a : ℕ →₀ ℕ) :
    Ymon k a 0 vacuum = monomial a 1 := by
  rw [Ymon, Yword_creation_zero, wordState_monoWord]

/-! ## §F  VA3 for EVERY state, by linearity, and the final mode form

`Y k` is the `ℂ`-linear extension `Finsupp.linearCombination (Ymon k)` of the monomial fields,
so the two creation clauses extend off the monomial basis: the `z`-evaluation-then-vacuum map
`f ↦ f j 1` is `ℂ`-linear, and on the basis `monomial a 1` it gives `0` (for `j < 0`) resp.
`monomial a 1` (for `j = 0`).  Together: `Y(u,z)1` is regular and `Y(u,0)1 = u`. -/

/-- The "evaluate at `z`-power `j`, then act on the vacuum" functional, as a `ℂ`-linear map
`FormalDist (End Fock) →ₗ[ℂ] Fock`.  This is what extends the monomial creation by linearity. -/
noncomputable def evalVacAt (j : ℤ) : FormalDist (End ℂ Fock) →ₗ[ℂ] Fock where
  toFun f := f j vacuum
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem evalVacAt_apply (j : ℤ) (f : FormalDist (End ℂ Fock)) :
    evalVacAt j f = f j vacuum := rfl

/-- `Y k u j vacuum` expanded as the `Finsupp` sum over the monomial support of `u`. -/
theorem Y_apply_vacuum_sum (k : ℂ) (u : Fock) (j : ℤ) :
    Y k u j vacuum = u.sum (fun a c => c • (Ymon k a j vacuum)) := by
  show evalVacAt j (Y k u) = _
  show evalVacAt j (Finsupp.linearCombination ℂ (Ymon k) u) = _
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, evalVacAt_apply]

/-- **VA3 / general creation, `j < 0`, every state**: `Y(u,z)_j 1 = 0` for `j < 0`. -/
theorem Y_creation_lt (k : ℂ) (u : Fock) {j : ℤ} (hj : j < 0) :
    Y k u j vacuum = 0 := by
  rw [Y_apply_vacuum_sum, Finsupp.sum]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Ymon_creation_lt k a hj, smul_zero]

/-- **VA3 / the `z⁰`-coefficient creates `u`, every state**: `Y(u,0)1 = u`. -/
theorem Y_creation_zero (k : ℂ) (u : Fock) : Y k u 0 vacuum = u := by
  rw [Y_apply_vacuum_sum]
  -- replace `Ymon a 0 1` by `monomial a 1`, then `cₐ • monomial a 1 = monomial a cₐ`, then sum = u
  rw [show u.sum (fun a c => c • (Ymon k a 0 vacuum))
        = u.sum (fun a c => monomial a c) from
      Finsupp.sum_congr fun a _ => by
        rw [Ymon_creation_zero, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
  -- `u.sum (monomial · ·) = u` is the canonical monomial decomposition
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff u]
  rw [Finsupp.sum]
  rfl

/-! ## §G  The VA3 mode form — `u₍ₙ₎1 = 0` for `n ≥ 0`, `u₍₋₁₎1 = u` — for every state

Recall `mode (Y k u) n = (Y k u) (-n-1)` (the `Y(u,z) = ∑ u₍ₙ₎ z^{-n-1}` indexing).  So the
`z`-power creation lemmas above translate verbatim into the mode form of axiom VA3. -/

/-- **VA3, mode form (regularity on the vacuum)**: `u₍ₙ₎1 = 0` for `n ≥ 0`, every state `u`. -/
theorem mode_Y_creation_nonneg (k : ℂ) (u : Fock) {n : ℤ} (hn : 0 ≤ n) :
    mode (Y k u) n vacuum = 0 := by
  rw [mode_apply]; exact Y_creation_lt k u (by omega)

/-- **VA3, mode form (the `(-1)`-mode creates `u`)**: `u₍₋₁₎1 = u`, every state `u`. -/
theorem mode_Y_creation_neg_one (k : ℂ) (u : Fock) :
    mode (Y k u) (-1) vacuum = u := by
  rw [mode_apply, show (-(-1 : ℤ) - 1) = 0 from by ring]; exact Y_creation_zero k u

/-- **The full VA3 statement** for the Heisenberg Fock space, in the exact shape of the
`PreVertexAlgebra.creation` field: for every state `u`, `u₍₋₁₎1 = u` and `u₍ₙ₎1 = 0` for `n ≥ 0`. -/
theorem Y_creation (k : ℂ) (u : Fock) :
    mode (Y k u) (-1) vacuum = u ∧ ∀ n : ℤ, 0 ≤ n → mode (Y k u) n vacuum = 0 :=
  ⟨mode_Y_creation_neg_one k u, fun _ hn => mode_Y_creation_nonneg k u hn⟩

end VOA
