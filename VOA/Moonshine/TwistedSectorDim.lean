/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.TwistedHeisenberg
import VOA.Moonshine.ExtraspecialModule
import VOA.Moonshine.LatticeGradedDim
import Mathlib.RingTheory.Flat.Basic

/-!
# The twisted sector `V_Λ^T = S[θ] ⊗ T` and its graded dimensions  (Moonshine step M7c)

FLM's twisted sector for the Leech lattice is `V_Λ^T = S[θ] ⊗ T`, with `S[θ] = FockT 24` the
half-integer-moded Fock space (`TwistedHeisenberg.lean`) and `T = leechT` the `2¹²`-dimensional
module of the extraspecial group (`ExtraspecialModule.lean`).  Its `L₀`-weights are
`24/16 + d/2 = 3/2 + d/2` for doubled oscillator weight `d`.  FLM let `θ` act on `T` by `-1`, so
`θ_tw = θ ⊗ (-1)`.  This file builds the carrier as a `ℂ`-vector space, without vertex operators,
and counts its `θ`-fixed graded pieces.

The key fact: the doubled weight `d = Σ (2n+1)` has the same parity as the oscillator number
(`weight_wT_mod_two`), so `θ = (-1)^d` on `S[θ]_{(d)}` (`thetaT_of_mem_gradingT`) and
`θ_tw = (-1)^{d+1}` on `S[θ]_{(d)} ⊗ T` (`twTheta_of_mem_twGrading`).

## Main declarations
* §1  `TwistedSector.thetaT_of_mem_gradingT`; the `θ`-eigenspaces `fockTPlus`, `fockTMinus` of
  `S[θ]` and `finrank_gradingT_inf_fockTPlus` / `finrank_gradingT_inf_fockTMinus`
  (`= P_T(r,d)` or `0` according to the parity of `d`).
* §2  The twisted Fock count `twCount r d = P_T(r, d)` (exponents of doubled weight `d`, i.e.
  `r`-coloured partitions of `d` into odd parts), `finrank_gradingT_eq_twCount`, the colour
  convolution `twCount_succ`, one colour = odd partitions (`twCount_one_colour`, via the bijection
  `toOddPartition_bijective`), and `twCount_zero` (1), `twCount_one` (r), `twCount_two`
  (`C(r+1,2)`), `twCount_three` (`r + C(r+2,3)`).
* §3  `hasProd_twGenFun : Σ_d P_T(r,d) X^d = ∏_{i≥0} (1 - X^{2i+1})^{-r}` in `ℂ⟦X⟧`, `X = q^{1/2}`,
  i.e. `∏_{n≥1} (1 - q^{n-1/2})^{-r}`.
* §5  For any `ℂ`-module `T`: `twGrading r T d`, `twWeight r T q`, `twTheta r T` (`= θ ⊗ (-1)`),
  `twFixed r T`; `twFixed_eq_iSup_odd` (the fixed part is the sum of the odd-`d` pieces),
  `finrank_twGrading` (`P_T(r,d) · dim T`), `finrank_twFixed_inf_twGrading`.  For `r = 24`:
  **`twFixed_eq_iSup_int`** (the `θ`-fixed part is exactly the sum of the integer-weight pieces),
  **`twFixed_inf_twWeight_of_lt_two`** (no fixed states of weight `< 2`; in particular
  `twFixed_inf_twWeight_zero`, `twFixed_inf_twWeight_one`), and
  `finrank_twFixed_inf_twWeight_24 : dim (S[θ] ⊗ T)^+_{n+2} = P_T(24, 2n+1) · dim T`.
* §6  `Moonshine.leechTwistedSpace := FockT 24 ⊗[ℂ] leechT`,
  `leechTwisted_finrank_fixed_two` (98304 = 24·4096), `leechTwisted_finrank_fixed_three`
  (10747904 = 2624·4096), `leechTwisted_fixed_weight_zero_one`, and the two-sector dimension
  identities `finrank_sectors_two` (`98580 + 98304 = 196884`) and `finrank_sectors_three`
  (`10745856 + 10747904 = 21493760`).

## Status
All declarations proved, no `sorry`; `#print axioms` for `finrank_sectors_two`, `finrank_sectors_three`,
`twFixed_eq_iSup_int`, `hasProd_twGenFun`, `leechTwisted_fixed_weight_zero_one` is
`[propext, Classical.choice, Quot.sound]` (no `pbw`).  Unconditional.  Honest scope: this is
linear algebra on the carrier.  `twWeight` is the `L₀`-grading *defined* by the oscillator
weight (`L₀ = d/2 + 3/2`, consistent with `TwistedHeisenberg.L0T`), and `θ_tw` is defined as
`θ ⊗ (-1)` following FLM; neither is yet tied to a twisted-module structure (step M6) nor to an
automorphism of `V♮`.  The identities `finrank_sectors_*` are sums of dimensions of the two
summands of `V♮ = V_Λ^+ ⊕ (V_Λ^T)^+`, stated on the carriers.  The VOA `V♮` is constructed
downstream (`Moonshine.moonshine`, `TopPairs.lean`) and its graded dimension `q·J` is
`finrank_gradingNat_eq_coeff_JShift` (`VnatCarrier.lean`), via `sectorSeries_eq_JShift`
(`Character.lean`).  Imported by the umbrella `VOA/Moonshine.lean`.

## References
* FLM, *Vertex Operator Algebras and the Monster*, §§9.1–9.3, 10.4.
-/

set_option linter.style.longLine false

open scoped TensorProduct

namespace VOA

namespace TwistedSector

open TwistedHeisenberg MvPolynomial Module

/-! ## §1  Parity: doubled weight ≡ oscillator number (mod 2) -/

/-- The doubled weight `Σ (2n+1)` of a monomial has the parity of its oscillator number. -/
theorem weight_wT_mod_two {r : ℕ} (m : (ℕ × Fin r) →₀ ℕ) :
    Finsupp.weight wT m % 2 = m.degree % 2 := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add]; omega
  | single v e =>
    rw [Finsupp.weight_single, Finsupp.degree_single, wT_apply, smul_eq_mul,
      show e * (2 * v.1 + 1) = 2 * (e * v.1) + e by ring]
    omega

/-- **`θ = (-1)^d` on the doubled-weight-`d` piece of `S[θ]`.** -/
theorem thetaT_of_mem_gradingT {r d : ℕ} {p : FockT r} (hp : p ∈ gradingT r d) :
    thetaT r p = (-1 : ℂ) ^ d • p := by
  ext m
  rw [coeff_thetaT, coeff_smul, smul_eq_mul]
  by_cases hm : coeff m p = 0
  · simp [hm]
  · have hw : Finsupp.weight wT m = d := hp hm
    have h2 := weight_wT_mod_two m
    rw [hw] at h2
    rw [neg_one_pow_eq_pow_mod_two (R := ℂ), ← h2, ← neg_one_pow_eq_pow_mod_two]

/-- `θ`-fixed vectors of `S[θ]`. -/
noncomputable def fockTPlus (r : ℕ) : Submodule ℂ (FockT r) :=
  LinearMap.ker ((thetaT r).toLinearMap - LinearMap.id)

/-- `θ`-anti-fixed vectors of `S[θ]`. -/
noncomputable def fockTMinus (r : ℕ) : Submodule ℂ (FockT r) :=
  LinearMap.ker ((thetaT r).toLinearMap + LinearMap.id)

theorem mem_fockTPlus {r : ℕ} {p : FockT r} : p ∈ fockTPlus r ↔ thetaT r p = p := by
  simp [fockTPlus, sub_eq_zero]

theorem mem_fockTMinus {r : ℕ} {p : FockT r} : p ∈ fockTMinus r ↔ thetaT r p = -p := by
  simp [fockTMinus, add_eq_zero_iff_eq_neg]

/-- In a `ℂ`-module, `x = -x` forces `x = 0`. -/
theorem eq_zero_of_eq_neg {M : Type*} [AddCommGroup M] [Module ℂ M] {x : M} (h : x = -x) :
    x = 0 := by
  have h2 : (2 : ℂ) • x = 0 := by
    rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel x
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- The doubled-weight-`d` piece is `θ`-even for `d` even. -/
theorem gradingT_le_fockTPlus {r d : ℕ} (hd : Even d) : gradingT r d ≤ fockTPlus r :=
  fun p hp => by rw [mem_fockTPlus, thetaT_of_mem_gradingT hp, hd.neg_one_pow, one_smul]

/-- The doubled-weight-`d` piece is `θ`-odd for `d` odd. -/
theorem gradingT_le_fockTMinus {r d : ℕ} (hd : Odd d) : gradingT r d ≤ fockTMinus r :=
  fun p hp => by rw [mem_fockTMinus, thetaT_of_mem_gradingT hp, hd.neg_one_pow, neg_one_smul]

theorem gradingT_inf_fockTPlus {r d : ℕ} (hd : Odd d) : gradingT r d ⊓ fockTPlus r = ⊥ := by
  rw [eq_bot_iff]
  rintro p ⟨hp, hf⟩
  rw [SetLike.mem_coe, mem_fockTPlus, thetaT_of_mem_gradingT hp, hd.neg_one_pow, neg_one_smul] at hf
  exact (Submodule.mem_bot ℂ).mpr (eq_zero_of_eq_neg hf.symm)

theorem gradingT_inf_fockTMinus {r d : ℕ} (hd : Even d) : gradingT r d ⊓ fockTMinus r = ⊥ := by
  rw [eq_bot_iff]
  rintro p ⟨hp, hf⟩
  rw [SetLike.mem_coe, mem_fockTMinus, thetaT_of_mem_gradingT hp, hd.neg_one_pow, one_smul] at hf
  exact (Submodule.mem_bot ℂ).mpr (eq_zero_of_eq_neg hf)

/-! ## §2  The twisted Fock count -/

/-- **The twisted Fock count** `P_T(r, d)`: the number of exponent vectors of doubled weight `d`,
i.e. of `r`-coloured partitions of `d/2` into parts in `½ + ℕ` (equivalently, of `d` into odd
parts). -/
noncomputable def twCount (r d : ℕ) : ℕ := (degSetT r d).ncard

/-- `dim S[θ]_{d/2 + r/16} = P_T(r, d)`. -/
theorem finrank_gradingT_eq_twCount (r d : ℕ) : finrank ℂ (gradingT r d) = twCount r d := by
  rw [finrank_gradingT, Nat.card_coe_set_eq, twCount]

/-- The `θ`-even part of the doubled-weight-`d` piece: everything for `d` even, nothing for `d`
odd. -/
theorem finrank_gradingT_inf_fockTPlus (r d : ℕ) :
    finrank ℂ (gradingT r d ⊓ fockTPlus r : Submodule ℂ (FockT r))
      = if Even d then twCount r d else 0 := by
  split_ifs with hd
  · rw [inf_eq_left.mpr (gradingT_le_fockTPlus hd), finrank_gradingT_eq_twCount]
  · rw [gradingT_inf_fockTPlus (Nat.not_even_iff_odd.mp hd), finrank_bot]

/-- The `θ`-odd part of the doubled-weight-`d` piece: everything for `d` odd, nothing for `d`
even. -/
theorem finrank_gradingT_inf_fockTMinus (r d : ℕ) :
    finrank ℂ (gradingT r d ⊓ fockTMinus r : Submodule ℂ (FockT r))
      = if Odd d then twCount r d else 0 := by
  split_ifs with hd
  · rw [inf_eq_left.mpr (gradingT_le_fockTMinus hd), finrank_gradingT_eq_twCount]
  · rw [gradingT_inf_fockTMinus (Nat.not_odd_iff_even.mp hd), finrank_bot]

theorem twCount_zero (r : ℕ) : twCount r 0 = 1 := by
  rw [← finrank_gradingT_eq_twCount, finrank_gradingT_zero]

theorem twCount_one (r : ℕ) : twCount r 1 = r := by
  rw [← finrank_gradingT_eq_twCount, finrank_gradingT_one]

/-- The exponent vectors of doubled weight `d`, as a finset. -/
noncomputable def twFinset (r d : ℕ) : Finset ((ℕ × Fin r) →₀ ℕ) := (degSetT_finite r d).toFinset

theorem mem_twFinset {r d : ℕ} {m : (ℕ × Fin r) →₀ ℕ} :
    m ∈ twFinset r d ↔ Finsupp.weight wT m = d :=
  Set.Finite.mem_toFinset _

theorem twCount_eq_card (r d : ℕ) : twCount r d = (twFinset r d).card :=
  Set.ncard_eq_toFinset_card _ (degSetT_finite r d)

theorem wT_colourSplit (r : ℕ) :
    ((wT : ℕ × Fin (r + 1) → ℕ) ∘ LatGen.colourSplit r) = Sum.elim wT wT := by
  funext x; rcases x with ⟨i, a⟩ | ⟨i, a⟩ <;> simp [LatGen.colourSplit, wT]

theorem weightT_splitExp (r : ℕ) (p : ((ℕ × Fin r) →₀ ℕ) × ((ℕ × Fin 1) →₀ ℕ)) :
    Finsupp.weight wT (LatGen.splitExp r p) = Finsupp.weight wT p.1 + Finsupp.weight wT p.2 := by
  simp only [LatGen.splitExp, Equiv.trans_apply, Finsupp.equivCongrLeft_apply,
    Finsupp.equivMapDomain_eq_mapDomain, Finsupp.sumFinsuppEquivProdFinsupp_symm_apply]
  rw [LatGen.weight_mapDomain, wT_colourSplit, Finsupp.sumElim_eq_add, map_add,
    LatGen.weight_mapDomain, LatGen.weight_mapDomain]
  rfl

theorem twFinset_succ (r n : ℕ) :
    twFinset (r + 1) n = ((Finset.antidiagonal n).biUnion
      fun x => twFinset r x.1 ×ˢ twFinset 1 x.2).map (LatGen.splitExp r).toEmbedding := by
  classical
  ext d
  rw [Finset.mem_map_equiv, mem_twFinset, Finset.mem_biUnion]
  constructor
  · intro h
    refine ⟨(Finsupp.weight wT ((LatGen.splitExp r).symm d).1,
      Finsupp.weight wT ((LatGen.splitExp r).symm d).2), ?_, ?_⟩
    · rw [Finset.mem_antidiagonal, ← weightT_splitExp, Equiv.apply_symm_apply, h]
    · rw [Finset.mem_product, mem_twFinset, mem_twFinset]; exact ⟨rfl, rfl⟩
  · rintro ⟨x, hx, hd⟩
    rw [Finset.mem_product, mem_twFinset, mem_twFinset] at hd
    rw [Finset.mem_antidiagonal] at hx
    rw [← Equiv.apply_symm_apply (LatGen.splitExp r) d, weightT_splitExp, hd.1, hd.2, hx]

theorem twFinset_pairwiseDisjoint (r n : ℕ) :
    (Finset.antidiagonal n : Set (ℕ × ℕ)).PairwiseDisjoint
      fun x => twFinset r x.1 ×ˢ twFinset 1 x.2 := by
  intro x _ y _ hxy
  rw [Function.onFun, Finset.disjoint_left]
  rintro ⟨d1, d2⟩ h1 h2
  rw [Finset.mem_product, mem_twFinset, mem_twFinset] at h1 h2
  exact hxy (Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2))

/-- **Colour convolution** `P_T(r+1, n) = Σ_{i+j=n} P_T(r,i) · P_T(1,j)`. -/
theorem twCount_succ (r n : ℕ) :
    twCount (r + 1) n = ∑ x ∈ Finset.antidiagonal n, twCount r x.1 * twCount 1 x.2 := by
  classical
  rw [twCount_eq_card, twFinset_succ, Finset.card_map,
    Finset.card_biUnion (twFinset_pairwiseDisjoint r n)]
  exact Finset.sum_congr rfl fun x _ => by
    rw [Finset.card_product, twCount_eq_card, twCount_eq_card]

theorem weightT_toFinsupp {r : ℕ} (m : Multiset (ℕ × Fin r)) :
    Finsupp.weight wT (Multiset.toFinsupp m) = (m.map wT).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, map_add,
        ih, Finsupp.weight_single, Multiset.map_add, Multiset.sum_add, Multiset.map_singleton,
        Multiset.sum_singleton, one_smul]

/-- One colour: exponents of doubled weight `n` ↦ partitions of `n` into odd parts. -/
noncomputable def toOddPartition (n : ℕ) (d : degSetT 1 n) :
    {p : n.Partition // ∀ i ∈ p.parts, Odd i} :=
  ⟨{ parts := (Finsupp.toMultiset d.1).map wT
     parts_pos := by
       intro i hi
       obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp hi
       rw [wT_apply]; omega
     parts_sum := by
       have h := weightT_toFinsupp (Finsupp.toMultiset d.1)
       rw [Finsupp.toMultiset_toFinsupp] at h
       rw [← h]; exact d.2 }, by
    intro i hi
    obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp hi
    rw [wT_apply]; exact odd_two_mul_add_one _⟩

theorem toOddPartition_bijective (n : ℕ) : Function.Bijective (toOddPartition n) := by
  constructor
  · intro d d' h
    have h1 := congrArg (fun p => Nat.Partition.parts p.1) h
    simp only [toOddPartition] at h1
    have hinj : Function.Injective (wT : ℕ × Fin 1 → ℕ) := by
      rintro ⟨i, a⟩ ⟨j, b⟩ hij
      rw [wT_apply, wT_apply] at hij
      rw [Prod.mk.injEq]; exact ⟨by omega, Subsingleton.elim a b⟩
    have h2 := congrArg Multiset.toFinsupp (Multiset.map_injective hinj h1)
    rw [Finsupp.toMultiset_toFinsupp, Finsupp.toMultiset_toFinsupp] at h2
    exact Subtype.ext h2
  · rintro ⟨p, hp⟩
    let m : Multiset (ℕ × Fin 1) := p.parts.map fun i => ((i - 1) / 2, 0)
    have hm : m.map wT = p.parts := by
      rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id p.parts]
      refine Multiset.map_congr rfl fun i hi => ?_
      obtain ⟨k, rfl⟩ := hp i hi
      simp only [Function.comp_apply, wT_apply, id]; omega
    refine ⟨⟨Multiset.toFinsupp m, ?_⟩, ?_⟩
    · change Finsupp.weight wT _ = n
      rw [weightT_toFinsupp, hm, p.parts_sum]
    · apply Subtype.ext
      apply Nat.Partition.ext
      simp only [toOddPartition, Multiset.toFinsupp_toMultiset]
      exact hm

/-- One colour: `P_T(1, n)` is the number of partitions of `n` into odd parts. -/
theorem twCount_one_colour (n : ℕ) :
    twCount 1 n = (Nat.Partition.restricted n Odd).card := by
  rw [twCount, ← Nat.card_coe_set_eq, Nat.card_eq_of_bijective _ (toOddPartition_bijective n),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

/-- No colours: only the empty exponent. -/
theorem twCount_zero_colours (n : ℕ) : twCount 0 n = if n = 0 then 1 else 0 := by
  have hS : degSetT 0 n = if n = 0 then {0} else ∅ := by
    ext d
    have hd : d = 0 := Subsingleton.elim _ _
    subst hd
    simp only [degSetT, Set.mem_setOf_eq, map_zero]
    split_ifs with h <;> simp [h, eq_comm]
  rw [twCount, hS]
  split_ifs <;> simp

/-- The finite model of one-colour exponents of doubled weight `n`: multiplicities
`f k ∈ {0,…,n}` of the variable `(k, 0)`, `k < n`, with `Σ f k (2k+1) = n`. -/
def oneColSet (n : ℕ) : Finset (Fin n → Fin (n + 1)) :=
  Finset.univ.filter fun f => ∑ k, (f k : ℕ) * (2 * (k : ℕ) + 1) = n

/-- The exponent `Σ_k f k · e_{(k,0)}`. -/
noncomputable def oneColExp {n : ℕ} (f : Fin n → ℕ) : (ℕ × Fin 1) →₀ ℕ :=
  ∑ k : Fin n, Finsupp.single ((k : ℕ), (0 : Fin 1)) (f k)

theorem oneColExp_apply {n : ℕ} (f : Fin n → ℕ) (j : ℕ) (i : Fin 1) :
    oneColExp f (j, i) = if h : j < n then f ⟨j, h⟩ else 0 := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  rw [oneColExp, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply, Prod.mk.injEq, and_true]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hbj; exact hb (Fin.ext hbj)
    · simp
  · exact Finset.sum_eq_zero fun k _ => by rw [if_neg]; omega

theorem weight_oneColExp {n : ℕ} (f : Fin n → ℕ) :
    Finsupp.weight wT (oneColExp f) = ∑ k, f k * (2 * (k : ℕ) + 1) := by
  rw [oneColExp, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finsupp.weight_single, wT_apply, smul_eq_mul]

/-- One colour, computably: `P_T(1, n) = #oneColSet n`. -/
theorem twCount_one_colour_eq_card (n : ℕ) : twCount 1 n = (oneColSet n).card := by
  classical
  rw [twCount_eq_card]
  refine Finset.card_nbij' (fun m k => ⟨min (m ((k : ℕ), 0)) n, by omega⟩)
    (fun f => oneColExp fun k => (f k : ℕ)) ?_ ?_ ?_ ?_
  · intro m hm
    have hm' := mem_twFinset.mp (Finset.mem_coe.mp hm)
    have hle : ∀ v, m v ≤ n := fun v => by
      have := Finsupp.le_weight (wT (r := 1)) (s := v) (by simp) m
      rw [hm'] at this; exact this
    have hlt : ∀ v, m v ≠ 0 → 2 * v.1 + 1 ≤ n := fun v hv => by
      have := Finsupp.le_weight_of_ne_zero' (wT (r := 1)) hv
      rw [hm', wT_apply] at this; exact this
    have hext : m = oneColExp fun k : Fin n => m ((k : ℕ), 0) := by
      ext ⟨j, i⟩
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      rw [oneColExp_apply]
      split_ifs with h
      · rfl
      · by_contra hne; have := hlt (j, 0) hne; simp at this; omega
    rw [Finset.mem_coe, oneColSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hw := hm'
    rw [hext, weight_oneColExp] at hw
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) hw
    change min _ _ * _ = _
    rw [min_eq_left (hle _)]
  · intro f hf
    rw [Finset.mem_coe, oneColSet, Finset.mem_filter] at hf
    rw [Finset.mem_coe, mem_twFinset, weight_oneColExp, hf.2]
  · intro m hm
    have hm' := mem_twFinset.mp (Finset.mem_coe.mp hm)
    have hle : ∀ v, m v ≤ n := fun v => by
      have := Finsupp.le_weight (wT (r := 1)) (s := v) (by simp) m
      rw [hm'] at this; exact this
    have hlt : ∀ v, m v ≠ 0 → 2 * v.1 + 1 ≤ n := fun v hv => by
      have := Finsupp.le_weight_of_ne_zero' (wT (r := 1)) hv
      rw [hm', wT_apply] at this; exact this
    ext ⟨j, i⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rw [oneColExp_apply]
    split_ifs with h
    · exact min_eq_left (hle _)
    · by_contra hne; have := hlt (j, 0) (Ne.symm hne); simp at this; omega
  · intro f _
    funext k
    apply Fin.ext
    change min _ _ = _
    rw [oneColExp_apply, dif_pos k.2]
    exact min_eq_left (by have := (f k).2; omega)

theorem twCount_one_colour_two : twCount 1 2 = 1 := by
  rw [twCount_one_colour_eq_card]; decide

theorem twCount_one_colour_three : twCount 1 3 = 2 := by
  rw [twCount_one_colour_eq_card]; decide

/-- `P_T(r, 2) = C(r+1, 2)`: the states `h_a(-½) h_b(-½) 1`, `a ≤ b`. -/
theorem twCount_two (r : ℕ) : twCount r 2 = (r + 1).choose 2 := by
  induction r with
  | zero => rw [twCount_zero_colours]; rfl
  | succ r ih =>
    rw [twCount_succ, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceSub]
    rw [twCount_zero, twCount_one, ih, twCount_one_colour_two, twCount_one 1, twCount_zero,
      Nat.choose_succ_succ' (r + 1) 1, Nat.choose_one_right]
    ring

/-- `P_T(r, 3) = r + C(r+2, 3)`: the states `h_a(-3/2) 1` and `h_a(-½) h_b(-½) h_c(-½) 1`. -/
theorem twCount_three (r : ℕ) : twCount r 3 = r + (r + 2).choose 3 := by
  induction r with
  | zero => rw [twCount_zero_colours]; rfl
  | succ r ih =>
    rw [twCount_succ, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceSub]
    rw [twCount_one_colour_two, twCount_one_colour_three, twCount_one 1, twCount_zero,
      twCount_zero, twCount_one, twCount_two, ih,
      show r + 1 + 2 = (r + 2) + 1 by ring, Nat.choose_succ_succ' (r + 2) 2,
      show r + 2 = (r + 1) + 1 by ring, Nat.choose_succ_succ' (r + 1) 1, Nat.choose_one_right]
    ring

/-! ## §3  The generating function `Σ_d P_T(r,d) X^d = ∏_{n≥0} (1 - X^{2n+1})^{-r}`, `X = q^{1/2}` -/

section GenFun

open PowerSeries

/-- The generating function `Σ_d P_T(r, d) X^d` in the variable `X = q^{1/2}`. -/
noncomputable def twGenFun (r : ℕ) : PowerSeries ℂ := PowerSeries.mk fun d => (twCount r d : ℂ)

theorem twGenFun_succ (r : ℕ) : twGenFun (r + 1) = twGenFun r * twGenFun 1 := by
  ext n
  rw [twGenFun, PowerSeries.coeff_mk, twCount_succ, PowerSeries.coeff_mul]
  push_cast
  simp only [twGenFun, PowerSeries.coeff_mk]

theorem twGenFun_zero : twGenFun 0 = 1 := by
  ext n
  rw [twGenFun, PowerSeries.coeff_mk, twCount_zero_colours, PowerSeries.coeff_one]
  split_ifs <;> simp

theorem twGenFun_eq_pow (r : ℕ) : twGenFun r = twGenFun 1 ^ r := by
  induction r with
  | zero => rw [twGenFun_zero, pow_zero]
  | succ r ih => rw [twGenFun_succ, ih, pow_succ]

theorem twGenFun_one :
    twGenFun 1 = PowerSeries.mk fun n => ((Nat.Partition.restricted n Odd).card : ℂ) := by
  ext n
  simp [twGenFun, twCount_one_colour]

open scoped PowerSeries.WithPiTopology in
/-- **The twisted Fock generating function**: with `X = q^{1/2}`,
`Σ_d dim S[θ]_{d/2 + r/16} X^d = ∏_{n≥1} (1 - q^{n-1/2})^{-r} = ∏_{i≥0} (1 - X^{2i+1})^{-r}`,
as an infinite product of formal power series (coefficientwise topology). -/
theorem hasProd_twGenFun (r : ℕ) :
    HasProd (fun i : ℕ => ((1 - (PowerSeries.X : ℂ⟦X⟧) ^ (2 * i + 1))⁻¹) ^ r) (twGenFun r) := by
  rw [twGenFun_eq_pow, twGenFun_one]
  have h := Nat.Partition.hasProd_powerSeriesMk_card_restricted ℂ (fun n : ℕ => Odd n)
  have hg : Function.Injective fun i : ℕ => 2 * i := fun a b hab => by
    have : 2 * a = 2 * b := hab
    omega
  have hf : ∀ x ∉ Set.range (fun i : ℕ => 2 * i),
      (fun i : ℕ => if Odd (i + 1) then ∑' j : ℕ, (PowerSeries.X : ℂ⟦X⟧) ^ ((i + 1) * j) else 1) x
        = 1 := by
    intro x hx
    have : ¬ Odd (x + 1) := by
      rintro ⟨k, hk⟩; exact hx ⟨k, show 2 * k = x by omega⟩
    simp only [this, if_false]
  have h2 := (hg.hasProd_iff hf).mpr h
  have h3 : ((fun i : ℕ => if Odd (i + 1) then ∑' j : ℕ, (PowerSeries.X : ℂ⟦X⟧) ^ ((i + 1) * j)
      else 1) ∘ fun i : ℕ => 2 * i) = fun i : ℕ => (1 - (PowerSeries.X : ℂ⟦X⟧) ^ (2 * i + 1))⁻¹ := by
    funext i
    simp only [Function.comp_apply]
    rw [if_pos (odd_two_mul_add_one i), LatGen.tsum_X_pow_mul_eq_inv]
  rw [h3] at h2
  exact h2.pow r

end GenFun

/-! ## §4  The odd part of `S[θ]` is spanned by the odd doubled weights -/

/-- `θ`-odd vectors of `S[θ]` lie in the sum of the odd doubled-weight pieces. -/
theorem fockTMinus_le_iSup_odd (r : ℕ) :
    fockTMinus r ≤ ⨆ (d : ℕ) (_ : Odd d), gradingT r d := by
  intro p hp
  rw [mem_fockTMinus, thetaT_eq_neg_iff] at hp
  rw [p.as_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hodd : Odd (Finsupp.weight wT m) := by
    rw [Nat.odd_iff, weight_wT_mod_two, ← Nat.odd_iff]
    exact hp m (MvPolynomial.mem_support_iff.mp hm)
  exact (le_iSup₂_of_le (f := fun (d : ℕ) (_ : Odd d) => gradingT r d) _ hodd le_rfl)
    (isWeightedHomogeneous_monomial wT m _ rfl)

/-! ## §5  The twisted sector `V_Λ^T = S[θ] ⊗ T` -/

section TwistedSpace

variable (r : ℕ) (T : Type*) [AddCommGroup T] [Module ℂ T]

/-- The doubled-weight-`d` piece `S[θ]_{(d)} ⊗ T` of `S[θ] ⊗ T` (`L₀ = d/2 + r/16`). -/
noncomputable def twGrading (d : ℕ) : Submodule ℂ (FockT r ⊗[ℂ] T) :=
  LinearMap.range ((gradingT r d).subtype.rTensor T)

/-- The `L₀ = q` eigenspace of `S[θ] ⊗ T` (`L₀` acts on the first factor only). -/
noncomputable def twWeight (q : ℚ) : Submodule ℂ (FockT r ⊗[ℂ] T) :=
  ⨆ (d : ℕ) (_ : levelT r d = q), twGrading r T d

theorem twWeight_levelT (d : ℕ) : twWeight r T (levelT r d) = twGrading r T d := by
  apply le_antisymm
  · refine iSup₂_le fun e he => ?_
    rw [levelT_injective r he]
  · exact le_iSup₂_of_le (f := fun (e : ℕ) (_ : levelT r e = levelT r d) => twGrading r T e)
      d rfl le_rfl

theorem tmul_mem_twGrading {d : ℕ} {p : FockT r} (hp : p ∈ gradingT r d) (t : T) :
    p ⊗ₜ t ∈ twGrading r T d :=
  ⟨⟨p, hp⟩ ⊗ₜ t, rfl⟩

/-- **The involution `θ ⊗ (-1)`** of `S[θ] ⊗ T` (FLM: `θ` acts on `T` by `-1`). -/
noncomputable def twTheta : Module.End ℂ (FockT r ⊗[ℂ] T) :=
  TensorProduct.map (thetaT r).toLinearMap (-LinearMap.id)

@[simp] theorem twTheta_tmul (p : FockT r) (t : T) :
    twTheta r T (p ⊗ₜ t) = thetaT r p ⊗ₜ (-t) := rfl

theorem twTheta_eq : twTheta r T = -((thetaT r).toLinearMap.rTensor T) := by
  apply TensorProduct.ext'
  intro p t
  simp [TensorProduct.tmul_neg]

theorem twTheta_twTheta (x : FockT r ⊗[ℂ] T) : twTheta r T (twTheta r T x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p t => rw [twTheta_tmul, twTheta_tmul, thetaT_thetaT, neg_neg]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The `θ`-fixed part `(V_Λ^T)^+` of the twisted sector. -/
noncomputable def twFixed : Submodule ℂ (FockT r ⊗[ℂ] T) :=
  LinearMap.ker (twTheta r T - LinearMap.id)

variable {r T}

theorem mem_twFixed {x : FockT r ⊗[ℂ] T} : x ∈ twFixed r T ↔ twTheta r T x = x := by
  simp [twFixed, sub_eq_zero]

/-- **`θ ⊗ (-1) = (-1)^{d+1}` on the doubled-weight-`d` piece.** -/
theorem twTheta_of_mem_twGrading {d : ℕ} {x : FockT r ⊗[ℂ] T} (hx : x ∈ twGrading r T d) :
    twTheta r T x = (-1 : ℂ) ^ (d + 1) • x := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul p t =>
    rw [LinearMap.rTensor_tmul, Submodule.coe_subtype, twTheta_tmul,
      thetaT_of_mem_gradingT p.2, TensorProduct.tmul_neg, ← TensorProduct.smul_tmul', pow_succ,
      mul_neg_one, neg_smul]
  | add y z hy hz => rw [map_add, map_add, hy, hz, smul_add]

/-- Odd doubled weight (`L₀ ∈ r/16 + ½ + ℤ`) is `θ`-fixed. -/
theorem twGrading_le_twFixed {d : ℕ} (hd : Odd d) : twGrading r T d ≤ twFixed r T :=
  fun x hx => by rw [mem_twFixed, twTheta_of_mem_twGrading hx, hd.add_one.neg_one_pow, one_smul]

/-- Even doubled weight meets the `θ`-fixed part trivially. -/
theorem twGrading_inf_twFixed {d : ℕ} (hd : Even d) : twGrading r T d ⊓ twFixed r T = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hf⟩
  rw [SetLike.mem_coe, mem_twFixed, twTheta_of_mem_twGrading hx, hd.add_one.neg_one_pow,
    neg_one_smul] at hf
  exact (Submodule.mem_bot ℂ).mpr (eq_zero_of_eq_neg hf.symm)

/-- `q ⊗ t` lies in the odd-weight sum whenever `q` does. -/
theorem tmul_mem_iSup_odd {q : FockT r} (hq : q ∈ ⨆ (d : ℕ) (_ : Odd d), gradingT r d) (t : T) :
    q ⊗ₜ t ∈ ⨆ (d : ℕ) (_ : Odd d), twGrading r T d := by
  have hle : (⨆ (d : ℕ) (_ : Odd d), gradingT r d)
      ≤ (⨆ (d : ℕ) (_ : Odd d), twGrading r T d).comap ((TensorProduct.mk ℂ (FockT r) T).flip t) := by
    refine iSup₂_le fun d hd p hp => ?_
    rw [Submodule.mem_comap, LinearMap.flip_apply, TensorProduct.mk_apply]
    exact (le_iSup₂_of_le (f := fun (e : ℕ) (_ : Odd e) => twGrading r T e) d hd le_rfl)
      (tmul_mem_twGrading r T hp t)
  exact hle hq

/-- **The `θ`-fixed part of `S[θ] ⊗ T` is the sum of its odd-doubled-weight pieces.** -/
theorem twFixed_eq_iSup_odd : twFixed r T = ⨆ (d : ℕ) (_ : Odd d), twGrading r T d := by
  apply le_antisymm
  · intro x hx
    rw [mem_twFixed, twTheta_eq, LinearMap.neg_apply, neg_eq_iff_eq_neg] at hx
    have hψ : ∀ y : FockT r ⊗[ℂ] T,
        y - (thetaT r).toLinearMap.rTensor T y ∈ ⨆ (d : ℕ) (_ : Odd d), twGrading r T d := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul p t =>
        rw [LinearMap.rTensor_tmul, ← TensorProduct.sub_tmul]
        refine tmul_mem_iSup_odd (fockTMinus_le_iSup_odd r ?_) t
        rw [mem_fockTMinus, map_sub, AlgEquiv.toLinearMap_apply, thetaT_thetaT, neg_sub]
      | add y z hy hz =>
        rw [map_add, add_sub_add_comm]; exact add_mem hy hz
    have hx2 : x = (1 / 2 : ℂ) • (x - (thetaT r).toLinearMap.rTensor T x) := by
      rw [hx, sub_neg_eq_add, ← two_smul ℂ x, smul_smul]; norm_num
    rw [hx2]
    exact Submodule.smul_mem _ _ (hψ x)
  · exact iSup₂_le fun d hd => twGrading_le_twFixed hd

/-- `dim (S[θ]_{(d)} ⊗ T) = P_T(r, d) · dim T`. -/
theorem finrank_twGrading (d : ℕ) :
    finrank ℂ (twGrading r T d) = twCount r d * finrank ℂ T := by
  rw [twGrading, LinearMap.finrank_range_of_inj
    (Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)),
    Module.finrank_tensorProduct, finrank_gradingT_eq_twCount]

/-- The `θ`-fixed part of the doubled-weight-`d` piece has dimension `P_T(r,d) · dim T` for `d`
odd and `0` for `d` even. -/
theorem finrank_twFixed_inf_twGrading (d : ℕ) :
    finrank ℂ (twFixed r T ⊓ twGrading r T d : Submodule ℂ (FockT r ⊗[ℂ] T))
      = if Odd d then twCount r d * finrank ℂ T else 0 := by
  split_ifs with hd
  · rw [inf_eq_right.mpr (twGrading_le_twFixed hd), finrank_twGrading]
  · rw [inf_comm, twGrading_inf_twFixed (Nat.not_odd_iff_even.mp hd), finrank_bot]

/-! ### Rank 24: integer weights -/

theorem levelT_24 (d : ℕ) : levelT 24 d = ((d : ℚ) + 3) / 2 := by
  rw [levelT]; push_cast; ring

/-- In rank 24 the doubled weight `2n+1` has `L₀ = n + 2`. -/
theorem levelT_24_odd (n : ℕ) : levelT 24 (2 * n + 1) = ((n : ℤ) + 2 : ℤ) := by
  rw [levelT_24]; push_cast; ring

theorem twWeight_24_nat (n : ℕ) :
    twWeight 24 T (((n : ℤ) + 2 : ℤ) : ℚ) = twGrading 24 T (2 * n + 1) := by
  rw [← levelT_24_odd, twWeight_levelT]

/-- **For `r = 24`, the `θ`-fixed part of `S[θ] ⊗ T` is exactly the sum of its integer-weight
pieces** (`L₀ = 3/2 + d/2 ∈ ℤ` iff `d` is odd iff the oscillator number is odd). -/
theorem twFixed_eq_iSup_int : twFixed 24 T = ⨆ n : ℤ, twWeight 24 T n := by
  apply le_antisymm
  · rw [twFixed_eq_iSup_odd]
    refine iSup₂_le fun d hd => ?_
    obtain ⟨k, rfl⟩ := hd
    exact le_iSup_of_le ((k : ℤ) + 2) (twWeight_24_nat (T := T) k).ge
  · refine iSup_le fun n => iSup₂_le fun d hd => twGrading_le_twFixed ?_
    rw [levelT_24] at hd
    have h : ((d : ℤ) : ℚ) = ((2 * n - 3 : ℤ) : ℚ) := by push_cast; linarith
    have h' : (d : ℤ) = 2 * n - 3 := by exact_mod_cast h
    rw [← Int.odd_coe_nat, h']
    exact ⟨n - 2, by ring⟩

/-- Weights below `2` in rank 24 occur only at doubled weight `0` (`L₀ = 3/2`). -/
theorem twWeight_le_twGrading_zero {q : ℚ} (hq : q < 2) : twWeight 24 T q ≤ twGrading 24 T 0 :=
  iSup₂_le fun d hd => by
    rw [levelT_24] at hd
    have h1 : (d : ℚ) < 1 := by linarith
    have h0 : d = 0 := by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast h1)
    rw [h0]

/-- **No `θ`-fixed twisted states of weight `< 2`** (rank 24): in particular `(V_Λ^T)^+` has
nothing in weights `0`, `1` (and `3/2`). -/
theorem twFixed_inf_twWeight_of_lt_two {q : ℚ} (hq : q < 2) :
    twFixed 24 T ⊓ twWeight 24 T q = ⊥ := by
  refine eq_bot_iff.mpr ((inf_le_inf_left _ (twWeight_le_twGrading_zero hq)).trans ?_)
  rw [inf_comm, twGrading_inf_twFixed ⟨0, rfl⟩]

theorem twFixed_inf_twWeight_zero : twFixed 24 T ⊓ twWeight 24 T 0 = ⊥ :=
  twFixed_inf_twWeight_of_lt_two (by norm_num)

theorem twFixed_inf_twWeight_one : twFixed 24 T ⊓ twWeight 24 T 1 = ⊥ :=
  twFixed_inf_twWeight_of_lt_two (by norm_num)

/-- **`dim (S[θ] ⊗ T)^+_{n+2} = P_T(24, 2n+1) · dim T`** for every `n : ℕ`. -/
theorem finrank_twFixed_inf_twWeight_24 (n : ℕ) :
    finrank ℂ (twFixed 24 T ⊓ twWeight 24 T (((n : ℤ) + 2 : ℤ) : ℚ) :
        Submodule ℂ (FockT 24 ⊗[ℂ] T))
      = twCount 24 (2 * n + 1) * finrank ℂ T := by
  rw [twWeight_24_nat, finrank_twFixed_inf_twGrading, if_pos (odd_two_mul_add_one n)]

end TwistedSpace

end TwistedSector

namespace Moonshine

open TwistedHeisenberg TwistedSector Module

/-! ## §6  The Leech twisted sector `V_Λ^T = S[θ] ⊗ T`, `dim T = 2¹²` -/

/-- **The FLM twisted sector** `V_Λ^T = S[θ] ⊗ T` (rank-24 twisted Fock space times the
`2¹²`-dimensional module `T`), as a `ℂ`-vector space.  No vertex operators yet (step M6). -/
abbrev leechTwistedSpace : Type := FockT 24 ⊗[ℂ] leechT

/-- `P_T(24, 3) = 24 + C(26, 3) = 2624`. -/
theorem twCount_24_three : twCount 24 3 = 2624 := by
  rw [twCount_three, show Nat.choose 26 3 = 2600 by decide]

/-- **`dim (V_Λ^T)^+_2 = 24 · 4096 = 98304`** (the states `h_i(-½) ⊗ t`). -/
theorem leechTwisted_finrank_fixed_two :
    finrank ℂ (twFixed 24 leechT ⊓ twWeight 24 leechT 2 : Submodule ℂ leechTwistedSpace)
      = 98304 := by
  have h := finrank_twFixed_inf_twWeight_24 (T := leechT) 0
  rw [twCount_one, finrank_leechT] at h
  exact h

/-- **`dim (V_Λ^T)^+_3 = 2624 · 4096 = 10747904`** (the states `h_i(-3/2) ⊗ t` and
`h_a(-½) h_b(-½) h_c(-½) ⊗ t`). -/
theorem leechTwisted_finrank_fixed_three :
    finrank ℂ (twFixed 24 leechT ⊓ twWeight 24 leechT 3 : Submodule ℂ leechTwistedSpace)
      = 10747904 := by
  have h := finrank_twFixed_inf_twWeight_24 (T := leechT) 1
  rw [twCount_24_three, finrank_leechT] at h
  exact h

/-- The `θ`-fixed twisted sector has nothing in weights `0` and `1`. -/
theorem leechTwisted_fixed_weight_zero_one :
    twFixed 24 leechT ⊓ twWeight 24 leechT 0 = ⊥ ∧ twFixed 24 leechT ⊓ twWeight 24 leechT 1 = ⊥ :=
  ⟨twFixed_inf_twWeight_zero, twFixed_inf_twWeight_one⟩

/-- **Dimension identity of the two sectors at weight 2**:
`dim (V_Λ^+)_2 + dim (V_Λ^T)^+_2 = 98580 + 98304 = 196884`.  This is a statement about the two
summands separately (the VOA `V♮` is constructed downstream, `Moonshine.moonshine`). -/
theorem finrank_sectors_two :
    finrank ℂ (leechVOAPlus.grading 2)
      + finrank ℂ (twFixed 24 leechT ⊓ twWeight 24 leechT 2 : Submodule ℂ leechTwistedSpace)
      = 196884 := by
  rw [leechVOAPlus_finrank_grading_two, leechTwisted_finrank_fixed_two]

/-- **Dimension identity of the two sectors at weight 3**:
`dim (V_Λ^+)_3 + dim (V_Λ^T)^+_3 = 10745856 + 10747904 = 21493760`. -/
theorem finrank_sectors_three :
    finrank ℂ (leechVOAPlus.grading 3)
      + finrank ℂ (twFixed 24 leechT ⊓ twWeight 24 leechT 3 : Submodule ℂ leechTwistedSpace)
      = 21493760 := by
  rw [leechVOAPlus_finrank_grading_three, leechTwisted_finrank_fixed_three]

end Moonshine

end VOA
