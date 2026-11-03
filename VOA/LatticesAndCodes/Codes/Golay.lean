/-
Copyright (c) 2026 Leonardo Rastelli and Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.LatticesAndCodes.Codes.Defs


/-!
# The binary Golay code

**Ebeling, Theorem 2.6 (existence).** This file constructs the extended binary Golay code as
`Code.golay : Code 2 24` and proves that it is a `[24, 12, 8]` doubly even self-dual binary code:

* `Code.golay_rank` — dimension `12`;
* `Code.golay_isSelfDual`, `Code.golay_isDoublyEven`;
* `Code.golay_minDist` — minimum distance `8`.

Deleting the last coordinate gives the perfect binary Golay code `Code.golay23 : Code 2 23`,
with `Code.golay23_rank` and `Code.golay23_minDist` — a `[23, 12, 7]` code.

## The construction

`golay` is the row space of `[I₁₂ | B]`, encoded as the range of `Code.golayEnc : x ↦ (x, xB)`.
The `12 × 12` matrix `B` is the Paley matrix of `ℙ¹(𝔽₁₁)`: labels `0, …, 10` are the elements of
`𝔽₁₁` and `11` is `∞`; off the last row and column the entry is `1` exactly when the index
difference is `0` or a nonzero quadratic residue mod `11`.

## Why there is no brute force here

`2¹² = 4096` codewords is beyond kernel evaluation: `decide` on
`∀ x : Fin 12 → ZMod 2, x ≠ 0 → 8 ≤ weight x + weight (xB)` does not finish in ten minutes.
What *is* cheap — a few seconds in total — are the five statements quantified over
`Fin 12` and `Fin 12 × Fin 12`: `golayB_mul_transpose` (`BBᵀ = I`), `golayB_row_weight`,
`golayB_col_weight`, `golayB_pair_weight` and `golayB_zero_weight`. The minimum distance is then
a five-line case analysis on `weight x`, using double evenness to rule out everything except
`weight = 4`, and `BBᵀ = I` to invert `x ↦ xB`.

## References

Ebeling, *Lattices and Codes*, §2.8.
-/

open scoped Matrix

namespace Code

/-! ### The matrix -/

/-- The `12 × 12` matrix `B` of the extended binary Golay code `[I₁₂ | B]`. Rows and columns are
indexed by `ℙ¹(𝔽₁₁)`: labels `0, …, 10` are the elements of `𝔽₁₁`, label `11` is `∞`. Off the
last row and column the entry is `1` exactly when the index difference is `0` or a nonzero
quadratic residue mod `11` (Ebeling §2.8; the Paley construction). -/
def golayB (i j : Fin 12) : ZMod 2 :=
  if (i : ℕ) = 11 then (if (j : ℕ) = 11 then 0 else 1)
  else if (j : ℕ) = 11 then 1
  else if (i : ℕ) = (j : ℕ) then 1
  else
    let d := ((j : ℕ) + 11 - (i : ℕ)) % 11
    if d = 1 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 9 then 1 else 0

set_option maxRecDepth 20000 in
/-- `B Bᵀ = I` over `𝔽₂`; this is what makes `[I₁₂ | B]` self-orthogonal. -/
theorem golayB_mul_transpose : ∀ i j : Fin 12,
    ∑ k, golayB i k * golayB j k = if i = j then 1 else 0 := by decide

set_option maxRecDepth 20000 in
theorem golayB_row_weight : ∀ i : Fin 12,
    weight (golayB i) = 7 ∨ weight (golayB i) = 11 := by decide

set_option maxRecDepth 20000 in
theorem golayB_col_weight : ∀ j : Fin 12, 7 ≤ weight (fun i => golayB i j) := by decide

set_option maxRecDepth 20000 in
theorem golayB_pair_weight : ∀ i j : Fin 12, i ≠ j → 6 ≤ weight (golayB i + golayB j) := by
  decide

set_option maxRecDepth 20000 in
theorem golayB_zero_weight : weight (golayB 0) = 7 := by decide

/-! ### Splitting a word of length `24` -/

theorem weight_append {m n : ℕ} (u : Fin m → ZMod 2) (v : Fin n → ZMod 2) :
    weight (Fin.append u v) = weight u + weight v := by
  classical
  have hcard : ∀ {N : ℕ} (c : Fin N → ZMod 2),
      weight c = ∑ j : Fin N, if c j ≠ 0 then 1 else 0 := by
    intro N c
    rw [weight_eq_card_support, support, Finset.card_filter]
  rw [hcard, hcard u, hcard v, Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by rw [Fin.append_left]
  · exact Finset.sum_congr rfl fun i _ => by rw [Fin.append_right]

theorem dotProduct_append {m n : ℕ} (u u' : Fin m → ZMod 2) (v v' : Fin n → ZMod 2) :
    Fin.append u v ⬝ᵥ Fin.append u' v' = u ⬝ᵥ u' + v ⬝ᵥ v' := by
  rw [dotProduct, dotProduct, dotProduct, Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by rw [Fin.append_left, Fin.append_left]
  · exact Finset.sum_congr rfl fun i _ => by rw [Fin.append_right, Fin.append_right]

/-! ### The code -/

/-- The encoder `x ↦ (x, xB)` of the extended binary Golay code. -/
def golayEnc : (Fin 12 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun x := Fin.append x (fun k => ∑ i, x i * golayB i k)
  map_add' x y := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun k => ?_) j <;>
      simp only [Pi.add_apply, Fin.append_left, Fin.append_right]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  map_smul' a x := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun k => ?_) j <;>
      simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Fin.append_left, Fin.append_right,
        Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem golayEnc_apply (x : Fin 12 → ZMod 2) :
    golayEnc x = Fin.append x (fun k => ∑ i, x i * golayB i k) := rfl

/-- The **extended binary Golay code** `[24, 12, 8]` (Ebeling, Theorem 2.6). -/
def golay : Code 2 24 := LinearMap.range golayEnc

theorem mem_golay {c : Fin 24 → ZMod 2} : c ∈ golay ↔ ∃ x, golayEnc x = c := Iff.rfl

theorem golayEnc_mem (x : Fin 12 → ZMod 2) : golayEnc x ∈ golay := ⟨x, rfl⟩

theorem golayEnc_injective : Function.Injective golayEnc := by
  intro x y h
  funext i
  have := congrFun h (Fin.castAdd 12 i)
  rwa [golayEnc_apply, golayEnc_apply, Fin.append_left, Fin.append_left] at this

theorem weight_golayEnc (x : Fin 12 → ZMod 2) :
    weight (golayEnc x) = weight x + weight (fun k => ∑ i, x i * golayB i k) := by
  rw [golayEnc_apply]
  exact weight_append (m := 12) (n := 12) x _

/-! ### `B` is an involution up to transpose -/

theorem dotProduct_mulB (u v : Fin 12 → ZMod 2) :
    (fun k => ∑ i, u i * golayB i k) ⬝ᵥ (fun k => ∑ i, v i * golayB i k) = u ⬝ᵥ v := by
  have hterm : ∀ k : Fin 12, (∑ i, u i * golayB i k) * (∑ j, v j * golayB j k)
      = ∑ i, ∑ j, u i * v j * (golayB i k * golayB j k) := by
    intro k
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [dotProduct]
  show (∑ k, (∑ i, u i * golayB i k) * (∑ j, v j * golayB j k)) = _
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_comm]
  have hin : ∀ i : Fin 12, (∑ k, ∑ j, u i * v j * (golayB i k * golayB j k))
      = ∑ j, u i * v j * (if i = j then 1 else 0) := by
    intro i
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, golayB_mul_transpose i j]
  rw [Finset.sum_congr rfl fun i _ => hin i]
  rw [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, mul_one]
  · intro j _ hj
    rw [if_neg (fun hc => hj hc.symm), mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem golayB_inv (x : Fin 12 → ZMod 2) (m : Fin 12) :
    (∑ k, (∑ i, x i * golayB i k) * golayB m k) = x m := by
  have hterm : ∀ k : Fin 12, (∑ i, x i * golayB i k) * golayB m k
      = ∑ i, x i * (golayB i k * golayB m k) := by
    intro k
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_comm]
  have hin : ∀ i : Fin 12, (∑ k, x i * (golayB i k * golayB m k))
      = x i * (if i = m then 1 else 0) := by
    intro i
    rw [← Finset.mul_sum, golayB_mul_transpose i m]
  rw [Finset.sum_congr rfl fun i _ => hin i, Finset.sum_eq_single m]
  · rw [if_pos rfl, mul_one]
  · intro j _ hj
    rw [if_neg hj, mul_zero]
  · intro hm
    exact absurd (Finset.mem_univ m) hm

theorem single_mulB (j : Fin 12) :
    (fun k => ∑ i, (Pi.single j (1 : ZMod 2) : Fin 12 → ZMod 2) i * golayB i k) = golayB j := by
  funext k
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, one_mul]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, zero_mul]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-! ### Rank, self-duality, double evenness -/

theorem golay_rank : golay.rank = 12 := by
  have h := LinearMap.finrank_range_of_inj golayEnc_injective
  show Module.finrank (ZMod 2) (LinearMap.range golayEnc) = 12
  rw [h]
  simp

theorem golay_isSelfOrthogonal : golay.IsSelfOrthogonal := by
  rw [isSelfOrthogonal_iff]
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
  rw [golayEnc_apply, golayEnc_apply, dotProduct_append, dotProduct_mulB]
  have : (u ⬝ᵥ v) + (u ⬝ᵥ v) = 0 := by
    have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
    have : (u ⬝ᵥ v) + (u ⬝ᵥ v) = ((2 : ℕ) : ZMod 2) * (u ⬝ᵥ v) := by push_cast; ring
    rw [this, h2, zero_mul]
  exact this

theorem golay_eq_span :
    golay = Submodule.span (ZMod 2)
      (Set.range (fun i : Fin 12 => golayEnc (Pi.single i (1 : ZMod 2)))) := by
  classical
  rw [golay, LinearMap.range_eq_map, ← (Pi.basisFun (ZMod 2) (Fin 12)).span_eq,
    Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, by rw [Pi.basisFun_apply]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Pi.basisFun (ZMod 2) (Fin 12) i, ⟨i, rfl⟩, by rw [Pi.basisFun_apply]⟩

theorem golay_isDoublyEven : golay.IsDoublyEven := by
  intro c hc
  rw [golay_eq_span] at hc
  induction hc using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    rw [weight_golayEnc, single_mulB]
    have h1 : weight (Pi.single i (1 : ZMod 2)) = 1 := by
      rw [weight_eq_card_support]
      have : support (Pi.single i (1 : ZMod 2)) = {i} := by
        ext m
        simp only [mem_support, Finset.mem_singleton]
        constructor
        · intro hm
          by_contra hc'
          exact hm (Pi.single_eq_of_ne hc' 1)
        · rintro rfl
          rw [Pi.single_eq_same]
          exact one_ne_zero
      rw [this, Finset.card_singleton]
    rw [h1]
    rcases golayB_row_weight i with h | h <;> rw [h] <;> decide
  | zero => simp
  | add u v hu hv IHu IHv =>
    have hduv : u ⬝ᵥ v = 0 :=
      (isSelfOrthogonal_iff.mp golay_isSelfOrthogonal) u (by rw [golay_eq_span]; exact hu) v
        (by rw [golay_eq_span]; exact hv)
    obtain ⟨a, ha⟩ := IHu
    obtain ⟨b, hb⟩ := IHv
    have hw := weight_add_two_mul_card_inter u v
    have hcard : ((support u ∩ support v).card : ZMod 2) = 0 := by
      rw [← dotProduct_eq_card_inter]; exact hduv
    have heven : 2 ∣ (support u ∩ support v).card := by
      rwa [ZMod.natCast_eq_zero_iff] at hcard
    obtain ⟨t, ht⟩ := heven
    exact ⟨a + b - t, by omega⟩
  | smul a u hu IH =>
    have ha : a = 0 ∨ a = 1 := by
      have hall : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
      exact hall a
    rcases ha with rfl | rfl
    · rw [zero_smul]
      simp
    · rw [one_smul]
      exact IH

theorem golay_isSelfDual : golay.IsSelfDual := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isSelfDual_iff.mpr ⟨golay_isSelfOrthogonal, by rw [golay_rank]⟩

/-! ### The minimum distance -/

theorem weight_single {N : ℕ} [NeZero N] (i : Fin N) :
    weight (Pi.single i (1 : ZMod 2) : Fin N → ZMod 2) = 1 := by
  classical
  rw [weight_eq_card_support]
  have hsupp : support (Pi.single i (1 : ZMod 2) : Fin N → ZMod 2) = {i} := by
    ext m
    simp only [mem_support, Finset.mem_singleton]
    constructor
    · intro hm
      by_contra hc
      exact hm (Pi.single_eq_of_ne hc 1)
    · rintro rfl
      rw [Pi.single_eq_same]
      exact one_ne_zero
  rw [hsupp, Finset.card_singleton]

theorem eq_single_of_weight_eq_one {N : ℕ} {x : Fin N → ZMod 2} (h : weight x = 1) :
    ∃ i, x = Pi.single i 1 := by
  classical
  rw [weight_eq_card_support, Finset.card_eq_one] at h
  obtain ⟨i, hi⟩ := h
  have hall : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  refine ⟨i, funext fun m => ?_⟩
  by_cases hm : m = i
  · subst hm
    have hms : m ∈ support x := by rw [hi]; exact Finset.mem_singleton_self m
    rw [mem_support] at hms
    rw [Pi.single_eq_same]
    exact hall _ hms
  · have hms : m ∉ support x := by rw [hi, Finset.mem_singleton]; exact hm
    rw [mem_support, not_not] at hms
    rw [hms, Pi.single_eq_of_ne hm]

theorem eq_pair_of_weight_eq_two {N : ℕ} {x : Fin N → ZMod 2} (h : weight x = 2) :
    ∃ i j, i ≠ j ∧ x = Pi.single i 1 + Pi.single j 1 := by
  classical
  rw [weight_eq_card_support, Finset.card_eq_two] at h
  obtain ⟨i, j, hij, hsupp⟩ := h
  have hall : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  refine ⟨i, j, hij, funext fun m => ?_⟩
  by_cases hmi : m = i
  · subst hmi
    have hms : m ∈ support x := by rw [hsupp]; simp
    rw [mem_support] at hms
    rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij 1, add_zero]
    exact hall _ hms
  · by_cases hmj : m = j
    · subst hmj
      have hms : m ∈ support x := by rw [hsupp]; simp
      rw [mem_support] at hms
      rw [Pi.add_apply, Pi.single_eq_of_ne hmi 1, Pi.single_eq_same, zero_add]
      exact hall _ hms
    · have hms : m ∉ support x := by rw [hsupp]; simp [hmi, hmj]
      rw [mem_support, not_not] at hms
      rw [hms, Pi.add_apply, Pi.single_eq_of_ne hmi 1, Pi.single_eq_of_ne hmj 1, add_zero]

theorem mulB_add (u v : Fin 12 → ZMod 2) :
    (fun k => ∑ i, (u + v) i * golayB i k)
      = (fun k => ∑ i, u i * golayB i k) + (fun k => ∑ i, v i * golayB i k) := by
  funext k
  rw [Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply]; ring

theorem single_dotB (j m : Fin 12) :
    (∑ k, (Pi.single j (1 : ZMod 2) : Fin 12 → ZMod 2) k * golayB m k) = golayB m j := by
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, one_mul]
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, zero_mul]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- **No codeword of the extended Golay code has weight `4`.** -/
theorem golay_eight_le_weight {c : Fin 24 → ZMod 2} (hc : c ∈ golay) (hne : c ≠ 0) :
    8 ≤ weight c := by
  obtain ⟨x, rfl⟩ := hc
  have hx : x ≠ 0 := fun h => hne (by rw [h, map_zero])
  have hdiv : 4 ∣ weight (golayEnc x) := golay_isDoublyEven _ ⟨x, rfl⟩
  by_contra hlt
  have hposw : weight (golayEnc x) ≠ 0 := by
    rw [Ne, weight_eq_zero]; exact hne
  have hw4 : weight (golayEnc x) = 4 := by omega
  rw [weight_golayEnc] at hw4
  have hxne : weight x ≠ 0 := by rw [Ne, weight_eq_zero]; exact hx
  -- the inverse relation `x = (xB)Bᵀ`
  have hinv : ∀ m, x m = ∑ k, (fun k => ∑ i, x i * golayB i k) k * golayB m k := fun m =>
    (golayB_inv x m).symm
  have hcase : weight x = 1 ∨ weight x = 2 ∨ weight x = 3 ∨ weight x = 4 := by omega
  rcases hcase with hwx | hwx | hwx | hwx
  · obtain ⟨i, rfl⟩ := eq_single_of_weight_eq_one hwx
    rw [single_mulB] at hw4
    rcases golayB_row_weight i with h | h <;> rw [h] at hw4 <;> omega
  · obtain ⟨i, j, hij, rfl⟩ := eq_pair_of_weight_eq_two hwx
    rw [mulB_add, single_mulB, single_mulB] at hw4
    have := golayB_pair_weight i j hij
    omega
  · -- `weight (xB) = 1`
    have hy1 : weight (fun k => ∑ i, x i * golayB i k) = 1 := by omega
    obtain ⟨j, hj⟩ := eq_single_of_weight_eq_one hy1
    have hxeq : x = fun m => golayB m j := by
      funext m
      rw [hinv m, hj]
      exact single_dotB j m
    rw [hxeq] at hwx
    have := golayB_col_weight j
    omega
  · -- `weight (xB) = 0`
    have hy0 : weight (fun k => ∑ i, x i * golayB i k) = 0 := by omega
    rw [weight_eq_zero] at hy0
    have hx0 : x = 0 := by
      funext m
      rw [hinv m, hy0]
      simp
    exact hx hx0

theorem golayEnc_single_ne_zero (i : Fin 12) :
    golayEnc (Pi.single i (1 : ZMod 2)) ≠ 0 := by
  intro h
  have := congrFun h (Fin.castAdd 12 i)
  rw [golayEnc_apply, Fin.append_left, Pi.single_eq_same] at this
  exact one_ne_zero this

theorem golay_ne_bot : golay ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  exact ⟨golayEnc (Pi.single 0 1), ⟨_, rfl⟩, golayEnc_single_ne_zero 0⟩

/-- **Ebeling, Theorem 2.6 (existence).** The extended binary Golay code is a
`[24, 12, 8]` doubly even self-dual binary code. -/
theorem golay_minDist : golay.minDist = 8 := by
  refine le_antisymm ?_ ?_
  · have hw : weight (golayEnc (Pi.single (0 : Fin 12) (1 : ZMod 2))) = 8 := by
      rw [weight_golayEnc, single_mulB, golayB_zero_weight, weight_single]
    rw [← hw]
    exact minDist_le_weight ⟨_, rfl⟩ (golayEnc_single_ne_zero 0)
  · obtain ⟨c, hc, hcne, hw⟩ := exists_weight_eq_minDist golay_ne_bot
    rw [← hw]
    exact golay_eight_le_weight hc hcne

/-! ### The perfect `[23, 12, 7]` code

Deleting the last coordinate of `golay` gives the perfect binary Golay code. -/

/-- Deletion of the last coordinate. -/
def punct : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 23 → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.castSucc : Fin 23 → Fin 24)

theorem punct_apply (c : Fin 24 → ZMod 2) (i : Fin 23) : punct c i = c i.castSucc := rfl

theorem weight_punct (c : Fin 24 → ZMod 2) :
    weight (punct c) + (if c (Fin.last 23) ≠ 0 then 1 else 0) = weight c := by
  classical
  have hcard : ∀ {N : ℕ} (d : Fin N → ZMod 2),
      weight d = ∑ j : Fin N, if d j ≠ 0 then 1 else 0 := by
    intro N d
    rw [weight_eq_card_support, support, Finset.card_filter]
  rw [hcard (punct c), hcard c,
    Fin.sum_univ_castSucc (f := fun j : Fin (23 + 1) => if c j ≠ 0 then 1 else 0)]
  congr 1

/-- The **perfect binary Golay code** `[23, 12, 7]`. -/
def golay23 : Code 2 23 := golay.map punct

theorem punct_golayEnc_mem (x : Fin 12 → ZMod 2) : punct (golayEnc x) ∈ golay23 :=
  ⟨golayEnc x, ⟨x, rfl⟩, rfl⟩

theorem castSucc_castAdd (m : Fin 12) :
    (Fin.castSucc (⟨(m : ℕ), by omega⟩ : Fin 23) : Fin 24) = Fin.castAdd 12 m :=
  Fin.ext rfl

theorem punct_golayEnc_injective : Function.Injective (punct ∘ golayEnc) := by
  intro x y h
  funext m
  have hm := congrFun h (⟨(m : ℕ), by omega⟩ : Fin 23)
  rw [Function.comp_apply, Function.comp_apply, punct_apply, punct_apply, castSucc_castAdd,
    golayEnc_apply, golayEnc_apply, Fin.append_left, Fin.append_left] at hm
  exact hm

theorem golay23_eq_range : golay23 = LinearMap.range (punct.comp golayEnc) := by
  rw [golay23, golay, LinearMap.range_comp]

theorem golay23_rank : golay23.rank = 12 := by
  rw [golay23_eq_range]
  show Module.finrank (ZMod 2) (LinearMap.range (punct.comp golayEnc)) = 12
  rw [LinearMap.finrank_range_of_inj punct_golayEnc_injective]
  simp

set_option maxRecDepth 20000 in
theorem golayB_zero_last : golayB 0 (⟨11, by omega⟩ : Fin 12) = 1 := by decide

theorem golayEnc_single_last :
    golayEnc (Pi.single (0 : Fin 12) (1 : ZMod 2)) (Fin.last 23) = 1 := by
  have hlast : (Fin.last 23 : Fin (12 + 12)) = Fin.natAdd 12 (⟨11, by omega⟩ : Fin 12) :=
    Fin.ext rfl
  rw [golayEnc_apply, hlast, Fin.append_right]
  have h := congrFun (single_mulB (0 : Fin 12)) (⟨11, by omega⟩ : Fin 12)
  rw [h, golayB_zero_last]

theorem weight_punct_single :
    weight (punct (golayEnc (Pi.single (0 : Fin 12) (1 : ZMod 2)))) = 7 := by
  have hw8 : weight (golayEnc (Pi.single (0 : Fin 12) (1 : ZMod 2))) = 8 := by
    rw [weight_golayEnc, single_mulB, golayB_zero_weight, weight_single]
  have hw := weight_punct (golayEnc (Pi.single (0 : Fin 12) (1 : ZMod 2)))
  rw [golayEnc_single_last, hw8, if_pos one_ne_zero] at hw
  omega

theorem golay23_ne_bot : golay23 ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  refine ⟨punct (golayEnc (Pi.single (0 : Fin 12) (1 : ZMod 2))), punct_golayEnc_mem _, ?_⟩
  rw [Ne, ← weight_eq_zero, weight_punct_single]
  omega

/-- The perfect binary Golay code has minimum distance `7`. -/
theorem golay23_minDist : golay23.minDist = 7 := by
  refine le_antisymm ?_ ?_
  · rw [← weight_punct_single]
    refine minDist_le_weight (punct_golayEnc_mem _) ?_
    rw [Ne, ← weight_eq_zero, weight_punct_single]
    omega
  · obtain ⟨c, hc, hcne, hw⟩ := exists_weight_eq_minDist golay23_ne_bot
    obtain ⟨d, hd, rfl⟩ := hc
    have hdne : d ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hcne
      exact hcne rfl
    have h8 := golay_eight_le_weight hd hdne
    have hwp := weight_punct d
    rw [← hw]
    split_ifs at hwp <;> omega

end Code
