/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.PlusWeightTwo
import VOA.LatticesAndCodes.Leech.RepCountHigher
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher

/-!
# The graded dimension of a lattice VOA and of its `θ`-fixed part  (Moonshine step M7b)

For an even positive-definite lattice `L` of rank `r`, `V_L = ⨁_α Fock ⊗ e^α` and the weight of
`p ⊗ e^α` is `wt p + ½⟨α,α⟩`.  This file turns that into dimension formulas.

* **Fock count** (§1).  `LatGen.fockCount r w` is the number of exponents
  `d : (ℕ × Fin r) →₀ ℕ` of Fock weight `w` (the `r`-coloured partitions of `w`), and
  `LatGen.finrank_gradingWN : finrank ℂ (gradingWN r w) = fockCount r w` (the weight space is the
  span of its monomials, `Finsupp.supported`).  The even/odd-degree counts `fockCountEven`,
  `fockCountOdd` add up to it (`fockCount_eq_even_add_odd`) and span `evenFock`/`oddFock`, on which
  `σ = ±1`.
* **Lattice** (§2).  `LatGen.finrank_gradingLatGen_eq_sum :
  dim (V_L)_k = Σ_{½⟨α,α⟩ ≤ k} P(r, k - ½⟨α,α⟩)` and the theta-series form
  `LatGen.finrank_gradingLatGen_eq_sum_theta :
  dim (V_L)_k = Σ_{n ≤ k} #{⟨α,α⟩ = 2n} · P(r, k-n)`, the `q^k` coefficient of
  `θ_L(q) ∏_{n≥1}(1-q^n)^{-r}`.
* **`θ`-split** (§3).  With `S = halfLE k` one of each pair `±α ≠ 0`,
  `LatGen.finrank_plusK_minusK : dim (V_L^±)_k = P^±(r,k) + Σ_{α∈S} P(r, k - ½⟨α,α⟩)`
  (lower bounds `(Fock_k)^{even/odd} ⊗ e^0 ⊕ {x ± θx : x ∈ B_S}` that exhaust `dim (V_L)_k`, as in
  `finrank_plusTwo`), and the trace forms `LatGen.two_mul_finrank_plusK`,
  `LatGen.two_mul_finrank_plusK_eq_signed : 2 dim (V_L^+)_k = dim (V_L)_k + fockSigned r k`.
* **Small weights** (§4).  `fockCount r 0 = 1`, `fockCount r 1 = r`,
  `fockCount r 2 = r + C(r+1,2)`, `fockCount r 3 = r + r² + C(r+2,3)`, with the parity splits
  `fockCountOdd r 2 = r`, `fockCountEven r 3 = r²`, `fockCountOdd r 3 = r + C(r+2,3)`
  (explicit enumeration `weight_eq_three`).
* **Generating functions** (§5).  `LatGen.hasProd_fockGenFun :
  Σ_w P(r,w) q^w = ∏_{n≥1} (1-q^n)^{-r}` and `LatGen.hasProd_fockSignedGenFun :
  Σ_w (P⁺-P⁻)(r,w) q^w = ∏_{n≥1} (1+q^n)^{-r}`, as `HasProd` in `ℂ⟦X⟧` with the coefficientwise
  topology.  Route: one colour is Mathlib's `Nat.Partition.genFun` (bijection `toPartition`);
  `r` colours by the colour convolution `fockCount_succ` / `fockSigned_succ`.
* **Leech** (§6).  From the general formulas, with `Leech.repCount_four = 196560` and
  `Leech.repCount_six = 16773120`:
  `Moonshine.leechVOA_finrank_grading_two_theta` (196884),
  `Moonshine.leechVOAPlus_finrank_grading_two_theta` (98580),
  `Moonshine.leechVOA_finrank_grading_three` (21493760 = 3200 + 24·196560 + 16773120),
  `Moonshine.leechVOAPlus_finrank_grading_three` (10745856 = 576 + (4717440 + 16773120)/2).

## Status
All declarations `sorry`-free; no new axioms.  Unconditional given `hEven`/`hPos` (and, for Leech,
the proved `leech_even`, `leech_posDef`, `leech_no_roots`, `leech_rank`, `Leech.repCount_four`,
`Leech.repCount_six`).  The trace of `θ` appears only through the equivalent dimension identity
`2 dim V^+ = dim V + (P⁺ - P⁻)`, not as `LinearMap.trace`.  Not done here: the full character
`χ_{V_L}` as a single power-series identity (the per-coefficient formula plus `hasProd_fockGenFun`
give it coefficientwise), and the twisted sector.
-/

set_option linter.style.longLine false

open scoped TensorProduct

namespace VOA

namespace LatGen

open HeisenbergN MvPolynomial Module IntegralLattice

/-! ## §1  The Fock count -/

section FockCount

variable (r : ℕ)

/-- The weight-`w` monomials of even total degree. -/
def fockSetEven (w : ℕ) : Set ((ℕ × Fin r) →₀ ℕ) :=
  {d | Finsupp.weight weightFnN d = w ∧ Even d.degree}

/-- The weight-`w` monomials of odd total degree. -/
def fockSetOdd (w : ℕ) : Set ((ℕ × Fin r) →₀ ℕ) :=
  {d | Finsupp.weight weightFnN d = w ∧ Odd d.degree}

/-- **The `r`-coloured partition number** `P r w`: the number of monomials
`∏ h_{a}(-(i+1))^{d(i,a)}` of Fock weight `w`, i.e. the coefficient of `q^w` in
`∏_{n ≥ 1} (1 - q^n)^{-r}`. -/
noncomputable def fockCount (w : ℕ) : ℕ := (weightDegSetN r w).ncard

/-- The even-degree part of `fockCount`. -/
noncomputable def fockCountEven (w : ℕ) : ℕ := (fockSetEven r w).ncard

/-- The odd-degree part of `fockCount`. -/
noncomputable def fockCountOdd (w : ℕ) : ℕ := (fockSetOdd r w).ncard

theorem fockSetEven_subset (w : ℕ) : fockSetEven r w ⊆ weightDegSetN r w := fun _ h => h.1

theorem fockSetOdd_subset (w : ℕ) : fockSetOdd r w ⊆ weightDegSetN r w := fun _ h => h.1

theorem fockCount_eq_even_add_odd (w : ℕ) :
    fockCount r w = fockCountEven r w + fockCountOdd r w := by
  have hU : weightDegSetN r w = fockSetEven r w ∪ fockSetOdd r w := by
    ext d
    simp only [fockSetEven, fockSetOdd, weightDegSetN, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · intro h
      rcases Nat.even_or_odd d.degree with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
    · rintro (h | h) <;> exact h.1
  have hD : Disjoint (fockSetEven r w) (fockSetOdd r w) := by
    rw [Set.disjoint_left]
    rintro d ⟨_, he⟩ ⟨_, ho⟩
    exact (Nat.not_even_iff_odd.mpr ho) he
  rw [fockCount, fockCountEven, fockCountOdd, hU,
    Set.ncard_union_eq hD ((weightDegSetN_finite r w).subset (fockSetEven_subset r w))
      ((weightDegSetN_finite r w).subset (fockSetOdd_subset r w))]

/-- The span of the monomials with exponent in `s`. -/
noncomputable abbrev fockSupp (s : Set ((ℕ × Fin r) →₀ ℕ)) : Submodule ℂ (FockN r) :=
  Finsupp.supported ℂ ℂ s

theorem finrank_fockSupp (s : Set ((ℕ × Fin r) →₀ ℕ)) (hs : s.Finite) :
    finrank ℂ (fockSupp r s) = s.ncard := by
  haveI := hs.fintype
  refine ((Finsupp.supportedEquivFinsupp (M := ℂ) (R := ℂ) s).finrank_eq).trans ?_
  rw [Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

theorem gradingWN_eq_fockSupp (w : ℕ) : gradingWN r w = fockSupp r (weightDegSetN r w) :=
  weightedHomogeneousSubmodule_eq_finsupp_supported (R := ℂ) weightFnN w

/-- **`dim (FockN r)_w = P r w`.** -/
theorem finrank_gradingWN (w : ℕ) : finrank ℂ (gradingWN r w) = fockCount r w := by
  rw [gradingWN_eq_fockSupp, finrank_fockSupp r _ (weightDegSetN_finite r w)]; rfl

/-- `σ` acts by the constant sign `c` on the span of monomials whose degree-sign is `c`. -/
theorem sigmaN_of_mem_fockSupp {s : Set ((ℕ × Fin r) →₀ ℕ)} {c : ℂ}
    (hs : ∀ d ∈ s, (-1 : ℂ) ^ d.degree = c) {p : FockN r} (hp : p ∈ fockSupp r s) :
    sigmaN r p = c • p := by
  rw [fockSupp, Finsupp.supported_eq_span_single] at hp
  induction hp using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨d, hd, rfl⟩ := hx
      change sigmaN r (monomial d 1) = c • monomial d 1
      rw [sigmaN_monomial, hs d hd]
  | zero => rw [map_zero]; exact (smul_zero c).symm
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx]; exact smul_comm a c x

/-- The even-degree part of `(FockN r)_w`. -/
noncomputable def evenFock (w : ℕ) : Submodule ℂ (FockN r) := fockSupp r (fockSetEven r w)

/-- The odd-degree part of `(FockN r)_w`. -/
noncomputable def oddFock (w : ℕ) : Submodule ℂ (FockN r) := fockSupp r (fockSetOdd r w)

theorem finrank_evenFock (w : ℕ) : finrank ℂ (evenFock r w) = fockCountEven r w :=
  finrank_fockSupp r _ ((weightDegSetN_finite r w).subset (fockSetEven_subset r w))

theorem finrank_oddFock (w : ℕ) : finrank ℂ (oddFock r w) = fockCountOdd r w :=
  finrank_fockSupp r _ ((weightDegSetN_finite r w).subset (fockSetOdd_subset r w))

theorem evenFock_le (w : ℕ) : evenFock r w ≤ gradingWN r w := by
  rw [gradingWN_eq_fockSupp]; exact Finsupp.supported_mono (fockSetEven_subset r w)

theorem oddFock_le (w : ℕ) : oddFock r w ≤ gradingWN r w := by
  rw [gradingWN_eq_fockSupp]; exact Finsupp.supported_mono (fockSetOdd_subset r w)

theorem sigmaN_of_mem_evenFock {w : ℕ} {p : FockN r} (hp : p ∈ evenFock r w) :
    sigmaN r p = p := by
  rw [sigmaN_of_mem_fockSupp r (c := 1) (fun d hd => hd.2.neg_one_pow) hp, one_smul]

theorem sigmaN_of_mem_oddFock {w : ℕ} {p : FockN r} (hp : p ∈ oddFock r w) :
    sigmaN r p = -p := by
  rw [sigmaN_of_mem_fockSupp r (c := -1) (fun d hd => hd.2.neg_one_pow) hp, neg_one_smul]

end FockCount


/-! ## §2  The lattice VOA: `dim (V_L)_k = Σ_α P r (k - ½⟨α,α⟩)` -/

section Lattice

variable (L : IntegralLattice) (hPos : L.PosDef)

include hPos in
theorem normLE_finite (k : ℤ) : {α : L.carrier | halfNorm L α ≤ k}.Finite :=
  (IntegralLattice.boundedFinite L hPos (2 * k + 1)).subset fun α h => by
    simp only [Set.mem_setOf_eq, halfNorm] at h ⊢; omega

/-- The lattice vectors with `½⟨α,α⟩ ≤ k`, as a finset. -/
noncomputable def normLE (k : ℤ) : Finset L.carrier := (normLE_finite L hPos k).toFinset

theorem mem_normLE {k : ℤ} {α : L.carrier} : α ∈ normLE L hPos k ↔ halfNorm L α ≤ k :=
  Set.Finite.mem_toFinset _

include hPos in
theorem normEq_finite (m : ℤ) : {α : L.carrier | L.form α α = m}.Finite :=
  (IntegralLattice.boundedFinite L hPos m).subset fun _ h => le_of_eq h

/-- The lattice vectors of norm `⟨α,α⟩ = m`, as a finset (`#normEq m` is the `q^{m/2}` coefficient
of the theta series `θ_L`). -/
noncomputable def normEq (m : ℤ) : Finset L.carrier := (normEq_finite L hPos m).toFinset

theorem mem_normEq {m : ℤ} {α : L.carrier} : α ∈ normEq L hPos m ↔ L.form α α = m :=
  Set.Finite.mem_toFinset _

/-- The weight-`k` charge-`α` sector `bigradα (k - ½⟨α,α⟩, α) = (Fock)_{k-½⟨α,α⟩} ⊗ e^α`. -/
noncomputable def sectorK (k : ℤ) (α : L.carrier) : Submodule ℂ (LatModuleGen L) :=
  bigradα L (k - halfNorm L α, α)

instance sectorK_finiteDimensional (k : ℤ) (α : L.carrier) :
    FiniteDimensional ℂ (sectorK L k α) :=
  bigradα_finiteDimensional L _

theorem iSupIndep_sectorK (k : ℤ) : iSupIndep (sectorK L k) :=
  (bigradα_iSupIndep L).comp (f := levelMapGen L k) (fun _ _ h => (Prod.mk.inj h).2)

theorem gradingLatGen_eq_biSup_normLE (k : ℤ) :
    gradingLatGen L k = ⨆ α ∈ normLE L hPos k, sectorK L k α := by
  apply le_antisymm
  · refine iSup_le fun α => ?_
    by_cases h : halfNorm L α ≤ k
    · exact le_biSup (sectorK L k) ((mem_normLE L hPos).mpr h)
    · rw [bigradα_eq_bot_of_neg L α (by omega)]; exact bot_le
  · exact iSup₂_le fun α _ => le_iSup (fun β => bigradα L (k - halfNorm L β, β)) α

theorem finrank_sectorK (k : ℕ) (α : L.carrier) (h : halfNorm L α ≤ k) :
    finrank ℂ (sectorK L k α) = fockCount (rank L) ((k : ℤ) - halfNorm L α).toNat := by
  rw [← finrank_gradingWN, ← finrank_bigradα, sectorK,
    Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ k - halfNorm L α)]

/-- **`dim (V_L)_k = Σ_{½⟨α,α⟩ ≤ k} P r (k - ½⟨α,α⟩)`.** -/
theorem finrank_gradingLatGen_eq_sum (k : ℕ) :
    finrank ℂ (gradingLatGen L k)
      = ∑ α ∈ normLE L hPos k, fockCount (rank L) ((k : ℤ) - halfNorm L α).toNat := by
  rw [gradingLatGen_eq_biSup_normLE L hPos,
    (finrank_biSup_of_iSupIndep _ (iSupIndep_sectorK L k) _).2]
  exact Finset.sum_congr rfl fun α hα => finrank_sectorK L k α ((mem_normLE L hPos).mp hα)

/-- **The theta-series form**: `dim (V_L)_k = Σ_{n ≤ k} #{⟨α,α⟩ = 2n} · P r (k - n)`, the
coefficient of `q^k` in `θ_L(q) · ∏_{n≥1} (1 - q^n)^{-r}`. -/
theorem finrank_gradingLatGen_eq_sum_theta (hEven : L.Even) (k : ℕ) :
    finrank ℂ (gradingLatGen L k)
      = ∑ n ∈ Finset.range (k + 1), (normEq L hPos (2 * n)).card * fockCount (rank L) (k - n) := by
  rw [finrank_gradingLatGen_eq_sum L hPos k,
    ← Finset.sum_fiberwise_of_maps_to (g := fun α => (halfNorm L α).toNat)
      (t := Finset.range (k + 1)) (fun α hα => by
        have := (mem_normLE L hPos).mp hα
        rw [Finset.mem_range]; change (halfNorm L α).toNat < k + 1; omega)]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_range] at hn
  have hfib : (normLE L hPos k).filter (fun α => (halfNorm L α).toNat = n)
      = normEq L hPos (2 * n) := by
    ext α
    rw [Finset.mem_filter, mem_normLE, mem_normEq]
    have h2 := two_halfNorm L hEven α
    have h0 := halfNorm_nonneg L hEven hPos α
    constructor
    · rintro ⟨_, h⟩; omega
    · intro h; constructor <;> omega
  rw [Finset.sum_congr rfl (g := fun _ => fockCount (rank L) (k - n)) (fun α hα => by
      rw [Finset.mem_filter] at hα
      have h0 := halfNorm_nonneg L hEven hPos α
      congr 1; omega), Finset.sum_const, smul_eq_mul, hfib]

end Lattice

/-! ## §3  The `θ`-split of `(V_L)_k` -/

section Theta

open Classical

variable (L : IntegralLattice) (hPos : L.PosDef)

/-- The `θ`-fixed part of `(V_L)_k`. -/
noncomputable def plusK (k : ℤ) : Submodule ℂ (LatModuleGen L) :=
  gradingLatGen L k ⊓ LinearMap.ker ((thetaLat L).toLinearMap - LinearMap.id)

/-- The `θ`-anti-fixed part of `(V_L)_k`. -/
noncomputable def minusK (k : ℤ) : Submodule ℂ (LatModuleGen L) :=
  gradingLatGen L k ⊓ LinearMap.ker ((thetaLat L).toLinearMap + LinearMap.id)

theorem plusK_two : plusK L 2 = plusTwo L := rfl

theorem mem_plusK {k : ℤ} {x : LatModuleGen L} :
    x ∈ plusK L k ↔ x ∈ gradingLatGen L k ∧ thetaLat L x = x := by
  rw [plusK, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]; rfl

theorem mem_minusK {k : ℤ} {x : LatModuleGen L} :
    x ∈ minusK L k ↔ x ∈ gradingLatGen L k ∧ thetaLat L x = -x := by
  rw [minusK, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.add_apply, add_eq_zero_iff_eq_neg]
  rfl

theorem disjoint_plusK_minusK (k : ℤ) : Disjoint (plusK L k) (minusK L k) := by
  rw [Submodule.disjoint_def]
  intro x hp hm
  have h1 := ((mem_plusK L).mp hp).2
  have h2 := ((mem_minusK L).mp hm).2
  rw [h1] at h2
  have h3 : (2 : ℂ) • x = 0 := by rw [two_smul]; nth_rewrite 1 [h2]; exact neg_add_cancel x
  exact (smul_eq_zero.mp h3).resolve_left two_ne_zero

/-- Half of the nonzero vectors with `½⟨α,α⟩ ≤ k`: exactly one of `α, -α` (chosen by a
well-order on `L`). -/
noncomputable def halfLE (k : ℤ) : Finset L.carrier :=
  (normLE L hPos k).filter fun α => WellOrderingRel α (-α)

theorem zero_notMem_halfLE (k : ℤ) : (0 : L.carrier) ∉ halfLE L hPos k := by
  simp only [halfLE, Finset.mem_filter, neg_zero, not_and]
  exact fun _ => irrefl _

theorem zero_notMem_halfLE_neg (k : ℤ) :
    (0 : L.carrier) ∉ (halfLE L hPos k).image Neg.neg := by
  rw [Finset.mem_image]
  rintro ⟨α, hα, h0⟩
  rw [neg_eq_zero] at h0
  exact zero_notMem_halfLE L hPos k (h0 ▸ hα)

theorem neg_mem_normLE {k : ℤ} {α : L.carrier} (h : α ∈ normLE L hPos k) :
    -α ∈ normLE L hPos k := by
  rw [mem_normLE] at h ⊢; rwa [halfNorm_neg]

theorem ne_neg_of_ne_zero {α : L.carrier} (h : α ≠ 0) : α ≠ -α := by
  intro he
  have h2α : (2 : ℤ) • α = 0 := by rw [two_smul]; nth_rewrite 2 [he]; exact add_neg_cancel α
  exact h ((smul_eq_zero.mp h2α).resolve_left two_ne_zero)

theorem normLE_erase_eq (k : ℤ) :
    (normLE L hPos k).erase 0 = halfLE L hPos k ∪ (halfLE L hPos k).image Neg.neg := by
  ext α
  simp only [halfLE, Finset.mem_erase, Finset.mem_union, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨h0, hα⟩
    rcases trichotomous_of (WellOrderingRel (α := L.carrier)) α (-α) with h | h | h
    · exact Or.inl ⟨hα, h⟩
    · exact absurd h (ne_neg_of_ne_zero L h0)
    · exact Or.inr ⟨-α, ⟨neg_mem_normLE L hPos hα, by rwa [neg_neg]⟩, neg_neg α⟩
  · rintro (⟨hα, h⟩ | ⟨β, ⟨hβ, h⟩, rfl⟩)
    · refine ⟨fun h0 => ?_, hα⟩
      subst h0; rw [neg_zero] at h; exact irrefl _ h
    · refine ⟨fun h0 => ?_, neg_mem_normLE L hPos hβ⟩
      rw [neg_eq_zero] at h0; subst h0; rw [neg_zero] at h; exact irrefl _ h

theorem disjoint_halfLE_neg (k : ℤ) :
    Disjoint (halfLE L hPos k) ((halfLE L hPos k).image Neg.neg) := by
  rw [Finset.disjoint_left]
  intro α hα hα'
  simp only [halfLE, Finset.mem_filter, Finset.mem_image] at hα hα'
  obtain ⟨β, ⟨_, hβ⟩, rfl⟩ := hα'
  rw [neg_neg] at hα
  exact (asymm hβ) hα.2

/-- For an even function `g`, `Σ_{½⟨α,α⟩ ≤ k} g = g 0 + 2 Σ_{α ∈ halfLE} g`. -/
theorem sum_normLE_eq {M : Type*} [AddCommMonoid M] (k : ℤ) (g : L.carrier → M)
    (hg : ∀ α, g (-α) = g α) (h0 : (0 : L.carrier) ∈ normLE L hPos k) :
    ∑ α ∈ normLE L hPos k, g α = g 0 + 2 • ∑ α ∈ halfLE L hPos k, g α := by
  rw [← Finset.add_sum_erase _ _ h0, normLE_erase_eq L hPos k,
    Finset.sum_union (disjoint_halfLE_neg L hPos k), Finset.sum_image (fun _ _ _ _ h => neg_injective h),
    two_nsmul]
  simp only [hg]

/-- `B_S = ⨁_{α ∈ S} (Fock)_{k-½⟨α,α⟩} ⊗ e^α` for the half `S = halfLE k`. -/
noncomputable def chargeHalfK (k : ℤ) : Submodule ℂ (LatModuleGen L) :=
  ⨆ α ∈ halfLE L hPos k, sectorK L k α

/-- `B_{-S}`. -/
noncomputable def chargeHalfNegK (k : ℤ) : Submodule ℂ (LatModuleGen L) :=
  ⨆ α ∈ (halfLE L hPos k).image Neg.neg, sectorK L k α

instance chargeHalfK_finiteDimensional (k : ℤ) : FiniteDimensional ℂ (chargeHalfK L hPos k) :=
  (finrank_biSup_of_iSupIndep _ (iSupIndep_sectorK L k) _).1

theorem finrank_chargeHalfK (k : ℕ) :
    finrank ℂ (chargeHalfK L hPos k)
      = ∑ α ∈ halfLE L hPos k, fockCount (rank L) ((k : ℤ) - halfNorm L α).toNat := by
  rw [chargeHalfK, (finrank_biSup_of_iSupIndep _ (iSupIndep_sectorK L k) _).2]
  refine Finset.sum_congr rfl fun α hα => finrank_sectorK L k α ?_
  exact (mem_normLE L hPos).mp (Finset.mem_filter.mp hα).1

theorem disjoint_chargeHalfK (k : ℤ) :
    Disjoint (chargeHalfK L hPos k) (chargeHalfNegK L hPos k) :=
  (iSupIndep_sectorK L k).disjoint_biSup_biSup
    (s := (halfLE L hPos k : Set L.carrier))
    (t := ((halfLE L hPos k).image Neg.neg : Set L.carrier))
    (Finset.disjoint_coe.mpr (disjoint_halfLE_neg L hPos k))

theorem sectorK_le_gradingLatGen (k : ℤ) (α : L.carrier) : sectorK L k α ≤ gradingLatGen L k :=
  le_iSup (fun β => bigradα L (k - halfNorm L β, β)) α

theorem chargeHalfK_le (k : ℤ) : chargeHalfK L hPos k ≤ gradingLatGen L k :=
  iSup₂_le fun α _ => sectorK_le_gradingLatGen L k α

theorem chargeHalfNegK_le (k : ℤ) : chargeHalfNegK L hPos k ≤ gradingLatGen L k :=
  iSup₂_le fun α _ => sectorK_le_gradingLatGen L k α

theorem chargeHalfK_le_ne (k : ℤ) :
    chargeHalfK L hPos k ≤ ⨆ (j : L.carrier) (_ : j ≠ 0), sectorK L k j :=
  iSup₂_le fun α hα => le_iSup₂ (f := fun (j : L.carrier) (_ : j ≠ 0) => sectorK L k j) α
    (fun h => zero_notMem_halfLE L hPos k (h ▸ hα))

theorem chargeHalfNegK_le_ne (k : ℤ) :
    chargeHalfNegK L hPos k ≤ ⨆ (j : L.carrier) (_ : j ≠ 0), sectorK L k j :=
  iSup₂_le fun α hα => le_iSup₂ (f := fun (j : L.carrier) (_ : j ≠ 0) => sectorK L k j) α
    (fun h => zero_notMem_halfLE_neg L hPos k (h ▸ hα))

theorem thetaLat_mem_sectorK {k : ℤ} {α : L.carrier} {x : LatModuleGen L}
    (hx : x ∈ sectorK L k α) : thetaLat L x ∈ sectorK L k (-α) := by
  have h := thetaLat_mem_bigradα L hx
  rwa [sectorK, halfNorm_neg]

theorem thetaLat_mem_chargeHalfNegK {k : ℤ} {x : LatModuleGen L}
    (hx : x ∈ chargeHalfK L hPos k) : thetaLat L x ∈ chargeHalfNegK L hPos k := by
  have hle : chargeHalfK L hPos k ≤
      (chargeHalfNegK L hPos k).comap (thetaLat L).toLinearMap := by
    refine iSup₂_le fun α hα y hy => ?_
    exact (le_biSup (sectorK L k) (Finset.mem_image_of_mem Neg.neg hα))
      (thetaLat_mem_sectorK L hy)
  exact hle hx

theorem injOn_chargeHalfK (k : ℤ) (c : ℂ) (x : LatModuleGen L) (hx : x ∈ chargeHalfK L hPos k)
    (h0 : x + c • thetaLat L x = 0) : x = 0 := by
  rw [add_eq_zero_iff_eq_neg] at h0
  have hm : x ∈ chargeHalfNegK L hPos k := by
    rw [h0]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ c (thetaLat_mem_chargeHalfNegK L hPos hx))
  exact (Submodule.disjoint_def.mp (disjoint_chargeHalfK L hPos k)) x hx hm

theorem map_mkEα_zero_le {k : ℕ} {q : Submodule ℂ (FockN (rank L))}
    (hq : q ≤ gradingWN (rank L) k) : q.map (mkEα L 0) ≤ sectorK L k 0 := by
  rw [sectorK, bigradα, halfNorm_zero, sub_zero, gradingZN_of_nonneg (by positivity),
    Int.toNat_natCast]
  exact Submodule.map_mono hq

/-- **The `θ`-fixed and `θ`-odd dimensions** of `(V_L)_k`: with `S = halfLE k` a half of the nonzero
vectors of `½⟨α,α⟩ ≤ k`,

  `dim (V_L^+)_k = P⁺(r,k) + Σ_{α ∈ S} P(r, k - ½⟨α,α⟩)`,
  `dim (V_L^-)_k = P⁻(r,k) + Σ_{α ∈ S} P(r, k - ½⟨α,α⟩)`,

where `P^±(r,k)` count the weight-`k` Fock monomials of even/odd degree.  The fixed space contains
`(Fock_k)^{even} ⊗ e^0 ⊕ {x + θx : x ∈ B_S}`, the anti-fixed space `(Fock_k)^{odd} ⊗ e^0 ⊕
{x - θx : x ∈ B_S}`; the two lower bounds exhaust `dim (V_L)_k`. -/
theorem finrank_plusK_minusK (hEven : L.Even) (k : ℕ) :
    finrank ℂ (plusK L k) = fockCountEven (rank L) k
        + ∑ α ∈ halfLE L hPos k, fockCount (rank L) ((k : ℤ) - halfNorm L α).toNat ∧
      finrank ℂ (minusK L k) = fockCountOdd (rank L) k
        + ∑ α ∈ halfLE L hPos k, fockCount (rank L) ((k : ℤ) - halfNorm L α).toNat := by
  haveI : FiniteDimensional ℂ (gradingLatGen L k) := gradingLatGen_finrank_of_posDef L hEven hPos k
  haveI : FiniteDimensional ℂ (plusK L k) := Submodule.finiteDimensional_of_le inf_le_left
  haveI : FiniteDimensional ℂ (minusK L k) := Submodule.finiteDimensional_of_le inf_le_left
  set H := ∑ α ∈ halfLE L hPos k, fockCount (rank L) ((k : ℤ) - halfNorm L α).toNat with hH
  set θl : LatModuleGen L →ₗ[ℂ] LatModuleGen L := (thetaLat L).toLinearMap with hθl
  have hdisj0 : Disjoint (sectorK L k 0) (⨆ (j : L.carrier) (_ : j ≠ 0), sectorK L k j) :=
    (iSupIndep_def.mp (iSupIndep_sectorK L k)) 0
  -- the map `x ↦ x + c θx` on `B_S`
  have hpiece : ∀ c : ℂ, ((chargeHalfK L hPos k).map (LinearMap.id + c • θl)) ≤
      (⨆ (j : L.carrier) (_ : j ≠ 0), sectorK L k j) ⊓ gradingLatGen L k := by
    intro c
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    rw [Submodule.mem_comap, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have h1 := thetaLat_mem_chargeHalfNegK L hPos hy
    refine Submodule.mem_inf.mpr ⟨Submodule.add_mem _ (chargeHalfK_le_ne L hPos k hy)
      (Submodule.smul_mem _ c (chargeHalfNegK_le_ne L hPos k h1)),
      Submodule.add_mem _ (chargeHalfK_le L hPos k hy)
        (Submodule.smul_mem _ c (chargeHalfNegK_le L hPos k h1))⟩
  have hfinB : ∀ c : ℂ, finrank ℂ ((chargeHalfK L hPos k).map (LinearMap.id + c • θl)) = H := by
    intro c
    rw [finrank_map_of_injOn _ _ (fun x hx h0 => injOn_chargeHalfK L hPos k c x hx h0),
      finrank_chargeHalfK]
  have hdimSup : ∀ {q : Submodule ℂ (FockN (rank L))} (c : ℂ), q ≤ gradingWN (rank L) k →
      finrank ℂ ↥(q.map (mkEα L 0) ⊔ (chargeHalfK L hPos k).map (LinearMap.id + c • θl))
        = finrank ℂ q + H := by
    intro q c hq
    haveI := gradingWN_finiteDimensional (rank L) k
    haveI : FiniteDimensional ℂ q := Submodule.finiteDimensional_of_le hq
    have h := Submodule.finrank_sup_add_finrank_inf_eq (q.map (mkEα L 0))
      ((chargeHalfK L hPos k).map (LinearMap.id + c • θl))
    rw [(hdisj0.mono (map_mkEα_zero_le L hq) ((hpiece c).trans inf_le_left)).eq_bot, finrank_bot,
      add_zero] at h
    rw [h, hfinB c, ← (Submodule.equivMapOfInjective _ (mkEα_injective L 0) q).finrank_eq]
  -- lower bounds
  have hPle : (evenFock (rank L) k).map (mkEα L 0) ⊔
      (chargeHalfK L hPos k).map (LinearMap.id + (1 : ℂ) • θl) ≤ plusK L k := by
    refine sup_le ?_ ?_
    · rintro _ ⟨p, hp, rfl⟩
      refine (mem_plusK L).mpr ⟨sectorK_le_gradingLatGen L k 0
        (map_mkEα_zero_le L (evenFock_le _ k) ⟨p, hp, rfl⟩), ?_⟩
      rw [mkEα_apply, thetaLat_tmul, sigmaN_of_mem_evenFock _ hp, neg_zero]
    · rintro _ ⟨y, hy, rfl⟩
      refine (mem_plusK L).mpr ⟨((hpiece 1) ⟨y, hy, rfl⟩).2, ?_⟩
      change thetaLat L (y + (1 : ℂ) • thetaLat L y) = y + (1 : ℂ) • thetaLat L y
      rw [map_add, map_smul, thetaLat_thetaLat, one_smul, one_smul, add_comm]
  have hMle : (oddFock (rank L) k).map (mkEα L 0) ⊔
      (chargeHalfK L hPos k).map (LinearMap.id + (-1 : ℂ) • θl) ≤ minusK L k := by
    refine sup_le ?_ ?_
    · rintro _ ⟨p, hp, rfl⟩
      refine (mem_minusK L).mpr ⟨sectorK_le_gradingLatGen L k 0
        (map_mkEα_zero_le L (oddFock_le _ k) ⟨p, hp, rfl⟩), ?_⟩
      rw [mkEα_apply, thetaLat_tmul, sigmaN_of_mem_oddFock _ hp, neg_zero, TensorProduct.neg_tmul]
    · rintro _ ⟨y, hy, rfl⟩
      refine (mem_minusK L).mpr ⟨((hpiece (-1)) ⟨y, hy, rfl⟩).2, ?_⟩
      change thetaLat L (y + (-1 : ℂ) • thetaLat L y) = -(y + (-1 : ℂ) • thetaLat L y)
      rw [map_add, map_smul, thetaLat_thetaLat, neg_one_smul, neg_one_smul, neg_add, neg_neg,
        add_comm]
  have h1 := Submodule.finrank_mono hPle
  have h2 := Submodule.finrank_mono hMle
  rw [hdimSup 1 (evenFock_le _ k), finrank_evenFock] at h1
  rw [hdimSup (-1) (oddFock_le _ k), finrank_oddFock] at h2
  -- upper bound
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (plusK L k) (minusK L k)
  rw [(disjoint_plusK_minusK L k).eq_bot, finrank_bot, add_zero] at h3
  have h4 : finrank ℂ ↥(plusK L k ⊔ minusK L k) ≤ finrank ℂ (gradingLatGen L k) :=
    Submodule.finrank_mono (sup_le inf_le_left inf_le_left)
  have h5 : finrank ℂ (gradingLatGen L k) = fockCount (rank L) k + 2 * H := by
    rw [finrank_gradingLatGen_eq_sum L hPos k, sum_normLE_eq L hPos k _
      (fun α => by rw [halfNorm_neg]) ((mem_normLE L hPos).mpr (by rw [halfNorm_zero]; positivity)),
      halfNorm_zero, sub_zero, Int.toNat_natCast, smul_eq_mul]
  rw [h5, fockCount_eq_even_add_odd] at h4
  constructor <;> omega

include hPos in
/-- **The trace form of the `θ`-split**: `2·dim (V_L^+)_k = dim (V_L)_k + (P⁺(r,k) - P⁻(r,k))`,
i.e. `dim (V_L^+)_k = ½(dim (V_L)_k + tr(θ | (V_L)_k))` with the trace equal to the signed Fock
count `P⁺ - P⁻` (only the charge-`0` sector contributes; the generating function of `P⁺ - P⁻` is
`∏_{n≥1}(1+q^n)^{-r}`).  Stated additively in `ℕ`. -/
theorem two_mul_finrank_plusK (hEven : L.Even) (k : ℕ) :
    2 * finrank ℂ (plusK L k) + fockCountOdd (rank L) k
      = finrank ℂ (gradingLatGen L k) + fockCountEven (rank L) k := by
  obtain ⟨h1, -⟩ := finrank_plusK_minusK L hPos hEven k
  have h5 : finrank ℂ (gradingLatGen L k) = fockCount (rank L) k
      + 2 * ∑ α ∈ halfLE L hPos k, fockCount (rank L) ((k : ℤ) - halfNorm L α).toNat := by
    rw [finrank_gradingLatGen_eq_sum L hPos k, sum_normLE_eq L hPos k _
      (fun α => by rw [halfNorm_neg]) ((mem_normLE L hPos).mpr (by rw [halfNorm_zero]; positivity)),
      halfNorm_zero, sub_zero, Int.toNat_natCast, smul_eq_mul]
  rw [h5, h1, fockCount_eq_even_add_odd]
  ring

include hPos in
/-- `dim (V_L^+)_k + dim (V_L^-)_k = dim (V_L)_k`. -/
theorem finrank_plusK_add_minusK (hEven : L.Even) (k : ℕ) :
    finrank ℂ (plusK L k) + finrank ℂ (minusK L k) = finrank ℂ (gradingLatGen L k) := by
  obtain ⟨h1, h2⟩ := finrank_plusK_minusK L hPos hEven k
  rw [h1, h2, finrank_gradingLatGen_eq_sum L hPos k, sum_normLE_eq L hPos k _
    (fun α => by rw [halfNorm_neg]) ((mem_normLE L hPos).mpr (by rw [halfNorm_zero]; positivity)),
    halfNorm_zero, sub_zero, Int.toNat_natCast, smul_eq_mul, fockCount_eq_even_add_odd]
  ring

end Theta

/-! ## §4  Small Fock weights -/

section SmallWeight

variable (r : ℕ)

theorem fockCount_zero : fockCount r 0 = 1 := by
  rw [← finrank_gradingWN, gradingWN_zero_eq_span_one, finrank_span_singleton one_ne_zero]

theorem fockCount_one : fockCount r 1 = r := by
  have hS : weightDegSetN r 1 = Set.range fun a : Fin r => Finsupp.single ((0 : ℕ), a) 1 := by
    ext d
    constructor
    · intro h
      obtain ⟨a, rfl⟩ := weight_eq_one r d h
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      change Finsupp.weight weightFnN _ = 1
      rw [Finsupp.weight_single, weightFnN_apply]; rfl
  rw [fockCount, hS, Set.ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
  intro a b h
  exact (Prod.mk.inj ((Finsupp.single_left_inj one_ne_zero).mp h)).2

theorem fockCount_two : fockCount r 2 = r + (r + 1).choose 2 := by
  rw [← finrank_gradingWN, finrank_gradingWN_two]

theorem fockCountOdd_two : fockCountOdd r 2 = r := by
  have hS : fockSetOdd r 2 = Set.range fun a : Fin r => Finsupp.single ((1 : ℕ), a) 1 := by
    ext d
    constructor
    · rintro ⟨h, ho⟩
      rcases weight_eq_two r d h with ⟨a, rfl⟩ | ⟨a, b, rfl⟩
      · exact ⟨a, rfl⟩
      · exfalso
        rw [map_add, Finsupp.degree_single, Finsupp.degree_single] at ho
        exact (Nat.not_even_iff_odd.mpr ho) even_two
    · rintro ⟨a, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [Finsupp.weight_single, weightFnN_apply]; rfl
      · rw [Finsupp.degree_single]; exact odd_one
  rw [fockCountOdd, hS, Set.ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
  intro a b h
  exact (Prod.mk.inj ((Finsupp.single_left_inj one_ne_zero).mp h)).2

theorem fockCountEven_two : fockCountEven r 2 = (r + 1).choose 2 := by
  have h := fockCount_eq_even_add_odd r 2
  rw [fockCount_two, fockCountOdd_two] at h
  omega

theorem weight_eq_three (d : (ℕ × Fin r) →₀ ℕ) (h : Finsupp.weight weightFnN d = 3) :
    (∃ a : Fin r, d = Finsupp.single (2, a) 1) ∨
      (∃ a b : Fin r, d = Finsupp.single (1, a) 1 + Finsupp.single (0, b) 1) ∨
      ∃ a b c : Fin r, d = Finsupp.single (0, a) 1 + Finsupp.single (0, b) 1 + Finsupp.single (0, c) 1 := by
  have hd : d ≠ 0 := by rintro rfl; simp at h
  obtain ⟨⟨m, a⟩, hx⟩ := Finsupp.ne_iff.mp hd
  rw [Finsupp.coe_zero, Pi.zero_apply] at hx
  have hs : Finsupp.weight weightFnN d = d (m, a) * (m + 1) + Finsupp.weight weightFnN (d.erase (m, a)) :=
    weight_split r d (m, a)
  rw [h] at hs
  have h1 : d (m, a) ≤ d (m, a) * (m + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have h2 : m + 1 ≤ d (m, a) * (m + 1) := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hx)
  have hdecomp := Finsupp.single_add_erase (m, a) d
  have hn3 : d (m, a) ≤ 3 := by omega
  have hm2 : m ≤ 2 := by omega
  interval_cases hn : d (m, a)
  · exact absurd rfl hx
  · interval_cases m
    · rcases weight_eq_two r (d.erase (0, a)) (by omega) with ⟨b, hb⟩ | ⟨b, c, hb⟩
      · right; left
        exact ⟨b, a, by rw [← hdecomp, hb, add_comm]⟩
      · right; right
        exact ⟨a, b, c, by rw [← hdecomp, hb, add_assoc]⟩
    · obtain ⟨b, hb⟩ := weight_eq_one r (d.erase (1, a)) (by omega)
      right; left
      exact ⟨a, b, by rw [← hdecomp, hb]⟩
    · have he : d.erase (2, a) = 0 := weight_eq_zero_iff r _ (by omega)
      left; exact ⟨a, by rw [← hdecomp, he, add_zero]⟩
  · interval_cases m
    · obtain ⟨b, hb⟩ := weight_eq_one r (d.erase (0, a)) (by omega)
      right; right
      exact ⟨a, a, b, by rw [← hdecomp, hb, ← Finsupp.single_add]⟩
    · omega
    · omega
  · interval_cases m
    · have he : d.erase (0, a) = 0 := weight_eq_zero_iff r _ (by omega)
      right; right
      exact ⟨a, a, a, by rw [← hdecomp, he, add_zero, ← Finsupp.single_add, ← Finsupp.single_add]⟩
    · omega
    · omega

theorem weight_toFinsupp (m : Multiset (ℕ × Fin r)) :
    Finsupp.weight weightFnN (Multiset.toFinsupp m) = (m.map weightFnN).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, map_add,
        ih, Finsupp.weight_single, Multiset.map_add, Multiset.sum_add, Multiset.map_singleton,
        Multiset.sum_singleton, one_smul]

theorem degree_toFinsupp (m : Multiset (ℕ × Fin r)) :
    (Multiset.toFinsupp m).degree = Multiset.card m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, map_add,
        ih, Finsupp.degree_single, Multiset.card_add, Multiset.card_singleton, add_comm]

/-- The cubic level-`0` exponent `h_a(-1)h_b(-1)h_c(-1)`, indexed by `Sym (Fin r) 3`. -/
noncomputable def cubExp (s : Sym (Fin r) 3) : (ℕ × Fin r) →₀ ℕ :=
  Multiset.toFinsupp (s.1.map fun a => ((0 : ℕ), a))

theorem cubExp_injective : Function.Injective (cubExp r) := by
  intro s t h
  have h1 := Multiset.toFinsupp.injective h
  exact Subtype.ext (Multiset.map_injective (fun a b hab => (Prod.mk.inj hab).2) h1)

theorem weight_cubExp (s : Sym (Fin r) 3) : Finsupp.weight weightFnN (cubExp r s) = 3 := by
  rw [cubExp, weight_toFinsupp, Multiset.map_map]
  have : (weightFnN ∘ fun a : Fin r => ((0 : ℕ), a)) = fun _ => 1 := funext fun _ => rfl
  rw [this, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one]
  exact s.2

theorem degree_cubExp (s : Sym (Fin r) 3) : (cubExp r s).degree = 3 := by
  rw [cubExp, degree_toFinsupp, Multiset.card_map]; exact s.2

theorem cubExp_mk (a b c : Fin r) :
    cubExp r ⟨{a, b, c}, by simp⟩
      = Finsupp.single (0, a) 1 + Finsupp.single (0, b) 1 + Finsupp.single (0, c) 1 := by
  simp only [cubExp, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
  rw [← Multiset.singleton_add, ← Multiset.singleton_add, Multiset.toFinsupp_add,
    Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, Multiset.toFinsupp_singleton,
    Multiset.toFinsupp_singleton, add_assoc]

/-- The odd weight-`3` exponents: `h_a(-3)` and `h_a(-1)h_b(-1)h_c(-1)`. -/
noncomputable def odd3Exp : Fin r ⊕ Sym (Fin r) 3 → (ℕ × Fin r) →₀ ℕ
  | Sum.inl a => Finsupp.single (2, a) 1
  | Sum.inr s => cubExp r s

theorem odd3Exp_injective : Function.Injective (odd3Exp r) := by
  rintro (a | s) (b | t) h
  · exact congrArg Sum.inl (Prod.mk.inj ((Finsupp.single_left_inj one_ne_zero).mp h)).2
  · have h1 := congrArg Finsupp.degree h
    simp only [odd3Exp] at h1
    rw [Finsupp.degree_single, degree_cubExp] at h1
    omega
  · have h1 := congrArg Finsupp.degree h
    simp only [odd3Exp] at h1
    rw [Finsupp.degree_single, degree_cubExp] at h1
    omega
  · exact congrArg Sum.inr (cubExp_injective r h)

/-- The even weight-`3` exponents `h_a(-2)h_b(-1)`. -/
noncomputable def even3Exp (p : Fin r × Fin r) : (ℕ × Fin r) →₀ ℕ :=
  Finsupp.single (1, p.1) 1 + Finsupp.single (0, p.2) 1

theorem even3Exp_injective : Function.Injective (even3Exp r) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [even3Exp] at h
  have ha : a = a' := by
    by_contra hne
    have := congrArg (fun f => f ((1 : ℕ), a)) h
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, Prod.mk.injEq] at this
    simp [Ne.symm hne] at this
  subst ha
  have hb := add_left_cancel h
  rw [(Prod.mk.inj ((Finsupp.single_left_inj one_ne_zero).mp hb)).2]

theorem degree_even3Exp (p : Fin r × Fin r) : (even3Exp r p).degree = 2 := by
  rw [even3Exp, map_add, Finsupp.degree_single, Finsupp.degree_single]

theorem weight_even3Exp (p : Fin r × Fin r) : Finsupp.weight weightFnN (even3Exp r p) = 3 := by
  rw [even3Exp, map_add, Finsupp.weight_single, Finsupp.weight_single, weightFnN_apply,
    weightFnN_apply]; rfl

theorem fockCountEven_three : fockCountEven r 3 = r * r := by
  have hS : fockSetEven r 3 = Set.range (even3Exp r) := by
    ext d
    constructor
    · rintro ⟨h, he⟩
      rcases weight_eq_three r d h with ⟨a, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, b, c, rfl⟩
      · rw [Finsupp.degree_single] at he; exact absurd he (by decide)
      · exact ⟨(a, b), rfl⟩
      · rw [← cubExp_mk, degree_cubExp] at he; exact absurd he (by decide)
    · rintro ⟨p, rfl⟩
      exact ⟨weight_even3Exp r p, by rw [degree_even3Exp]; exact even_two⟩
  rw [fockCountEven, hS, Set.ncard_range_of_injective (even3Exp_injective r),
    Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin]

theorem fockCountOdd_three : fockCountOdd r 3 = r + (r + 2).choose 3 := by
  have hS : fockSetOdd r 3 = Set.range (odd3Exp r) := by
    ext d
    constructor
    · rintro ⟨h, ho⟩
      rcases weight_eq_three r d h with ⟨a, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, b, c, rfl⟩
      · exact ⟨Sum.inl a, rfl⟩
      · rw [map_add, Finsupp.degree_single, Finsupp.degree_single] at ho
        exact absurd ho (by decide)
      · exact ⟨Sum.inr ⟨{a, b, c}, by simp⟩, cubExp_mk r a b c⟩
    · rintro ⟨i | s, rfl⟩
      · refine ⟨?_, ?_⟩
        · change Finsupp.weight weightFnN (Finsupp.single _ 1) = 3
          rw [Finsupp.weight_single, weightFnN_apply]; rfl
        · change Odd (Finsupp.single _ 1).degree
          rw [Finsupp.degree_single]; exact odd_one
      · exact ⟨weight_cubExp r s, by change Odd (cubExp r s).degree; rw [degree_cubExp]; decide⟩
  rw [fockCountOdd, hS, Set.ncard_range_of_injective (odd3Exp_injective r),
    Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin, Sym.card_sym_eq_choose,
    Fintype.card_fin]
  rfl

theorem fockCount_three : fockCount r 3 = r + r * r + (r + 2).choose 3 := by
  rw [fockCount_eq_even_add_odd, fockCountEven_three, fockCountOdd_three]; ring

end SmallWeight

/-! ## §5  The generating function `Σ_w P(r,w) q^w = ∏_{n≥1} (1 - q^n)^{-r}` -/

section GenFun

theorem weight_mapDomain {σ τ : Type*} (w : τ → ℕ) (f : σ → τ) (l : σ →₀ ℕ) :
    Finsupp.weight w (Finsupp.mapDomain f l) = Finsupp.weight (w ∘ f) l := by
  change Finsupp.linearCombination ℕ w _ = Finsupp.linearCombination ℕ (w ∘ f) l
  exact Finsupp.linearCombination_mapDomain (R := ℕ) (v' := w) f l

/-- One colour: `P(1,n)` is the number of partitions of `n`
(`d ↦ the multiset of levels + 1`). -/
noncomputable def toPartition (n : ℕ) (d : weightDegSetN 1 n) : n.Partition where
  parts := (Finsupp.toMultiset d.1).map weightFnN
  parts_pos := by
    intro i hi
    obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp hi
    rw [weightFnN_apply]; omega
  parts_sum := by
    have h := weight_toFinsupp 1 (Finsupp.toMultiset d.1)
    rw [Finsupp.toMultiset_toFinsupp] at h
    rw [← h]; exact d.2

theorem toPartition_bijective (n : ℕ) : Function.Bijective (toPartition n) := by
  constructor
  · intro d d' h
    have h1 := congrArg Nat.Partition.parts h
    simp only [toPartition] at h1
    have hinj : Function.Injective (weightFnN : ℕ × Fin 1 → ℕ) := by
      rintro ⟨i, a⟩ ⟨j, b⟩ hij
      rw [weightFnN_apply, weightFnN_apply] at hij
      rw [Prod.mk.injEq]; exact ⟨by omega, Subsingleton.elim a b⟩
    have h2 := congrArg Multiset.toFinsupp (Multiset.map_injective hinj h1)
    rw [Finsupp.toMultiset_toFinsupp, Finsupp.toMultiset_toFinsupp] at h2
    exact Subtype.ext h2
  · intro p
    let m : Multiset (ℕ × Fin 1) := p.parts.map fun i => (i - 1, 0)
    have hm : m.map weightFnN = p.parts := by
      rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id p.parts]
      refine Multiset.map_congr rfl fun i hi => ?_
      have := p.parts_pos hi
      simp only [Function.comp_apply, weightFnN_apply, id]; omega
    refine ⟨⟨Multiset.toFinsupp m, ?_⟩, ?_⟩
    · change Finsupp.weight weightFnN _ = n
      rw [weight_toFinsupp, hm, p.parts_sum]
    · apply Nat.Partition.ext
      simp only [toPartition, Multiset.toFinsupp_toMultiset]
      exact hm

theorem fockCount_one_eq_card_partition (n : ℕ) :
    fockCount 1 n = Fintype.card n.Partition := by
  rw [fockCount, ← Nat.card_coe_set_eq, Nat.card_eq_of_bijective _ (toPartition_bijective n),
    Nat.card_eq_fintype_card]

/-- No colours: only the empty monomial. -/
theorem fockCount_zero_colours (n : ℕ) : fockCount 0 n = if n = 0 then 1 else 0 := by
  have hS : weightDegSetN 0 n = if n = 0 then {0} else ∅ := by
    ext d
    have hd : d = 0 := Subsingleton.elim _ _
    subst hd
    simp only [weightDegSetN, Set.mem_setOf_eq, map_zero]
    split_ifs with h <;> simp [h, eq_comm]
  rw [fockCount, hS]
  split_ifs <;> simp

/-- Splitting off the last colour: `ℕ × Fin (r+1) ≃ (ℕ × Fin r) ⊕ (ℕ × Fin 1)` preserving levels. -/
def colourSplit (r : ℕ) : (ℕ × Fin r) ⊕ (ℕ × Fin 1) ≃ ℕ × Fin (r + 1) :=
  (Equiv.prodSumDistrib ℕ (Fin r) (Fin 1)).symm.trans (Equiv.prodCongr (Equiv.refl ℕ) finSumFinEquiv)

theorem weightFnN_colourSplit (r : ℕ) :
    (weightFnN ∘ colourSplit r) = Sum.elim weightFnN weightFnN := by
  funext x; rcases x with ⟨i, a⟩ | ⟨i, a⟩ <;> simp [colourSplit, weightFnN]

/-- The colour-splitting equivalence on exponents. -/
noncomputable def splitExp (r : ℕ) :
    ((ℕ × Fin r) →₀ ℕ) × ((ℕ × Fin 1) →₀ ℕ) ≃ ((ℕ × Fin (r + 1)) →₀ ℕ) :=
  Finsupp.sumFinsuppEquivProdFinsupp.symm.trans (Finsupp.equivCongrLeft (colourSplit r))

theorem weight_splitExp (r : ℕ) (p : ((ℕ × Fin r) →₀ ℕ) × ((ℕ × Fin 1) →₀ ℕ)) :
    Finsupp.weight weightFnN (splitExp r p)
      = Finsupp.weight weightFnN p.1 + Finsupp.weight weightFnN p.2 := by
  simp only [splitExp, Equiv.trans_apply, Finsupp.equivCongrLeft_apply,
    Finsupp.equivMapDomain_eq_mapDomain, Finsupp.sumFinsuppEquivProdFinsupp_symm_apply]
  rw [weight_mapDomain, weightFnN_colourSplit, Finsupp.sumElim_eq_add, map_add, weight_mapDomain,
    weight_mapDomain]
  rfl

/-- The weight-`w` exponents, as a finset. -/
noncomputable def fockFinset (r w : ℕ) : Finset ((ℕ × Fin r) →₀ ℕ) :=
  (weightDegSetN_finite r w).toFinset

theorem mem_fockFinset {r w : ℕ} {d : (ℕ × Fin r) →₀ ℕ} :
    d ∈ fockFinset r w ↔ Finsupp.weight weightFnN d = w :=
  Set.Finite.mem_toFinset _

theorem fockCount_eq_card (r w : ℕ) : fockCount r w = (fockFinset r w).card :=
  Set.ncard_eq_toFinset_card _ (weightDegSetN_finite r w)

theorem fockFinset_succ (r n : ℕ) :
    fockFinset (r + 1) n = ((Finset.antidiagonal n).biUnion
      fun x => fockFinset r x.1 ×ˢ fockFinset 1 x.2).map (splitExp r).toEmbedding := by
  classical
  ext d
  rw [Finset.mem_map_equiv, mem_fockFinset, Finset.mem_biUnion]
  constructor
  · intro h
    refine ⟨(Finsupp.weight weightFnN ((splitExp r).symm d).1,
      Finsupp.weight weightFnN ((splitExp r).symm d).2), ?_, ?_⟩
    · rw [Finset.mem_antidiagonal, ← weight_splitExp, Equiv.apply_symm_apply, h]
    · rw [Finset.mem_product, mem_fockFinset, mem_fockFinset]; exact ⟨rfl, rfl⟩
  · rintro ⟨x, hx, hd⟩
    rw [Finset.mem_product, mem_fockFinset, mem_fockFinset] at hd
    rw [Finset.mem_antidiagonal] at hx
    rw [← Equiv.apply_symm_apply (splitExp r) d, weight_splitExp, hd.1, hd.2, hx]

theorem fockFinset_pairwiseDisjoint (r n : ℕ) :
    (Finset.antidiagonal n : Set (ℕ × ℕ)).PairwiseDisjoint
      fun x => fockFinset r x.1 ×ˢ fockFinset 1 x.2 := by
  intro x _ y _ hxy
  rw [Function.onFun, Finset.disjoint_left]
  rintro ⟨d1, d2⟩ h1 h2
  rw [Finset.mem_product, mem_fockFinset, mem_fockFinset] at h1 h2
  exact hxy (Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2))

/-- **Colour convolution** `P(r+1, n) = Σ_{i+j=n} P(r,i) · P(1,j)`. -/
theorem fockCount_succ (r n : ℕ) :
    fockCount (r + 1) n
      = ∑ x ∈ Finset.antidiagonal n, fockCount r x.1 * fockCount 1 x.2 := by
  classical
  rw [fockCount_eq_card, fockFinset_succ, Finset.card_map,
    Finset.card_biUnion (fockFinset_pairwiseDisjoint r n)]
  exact Finset.sum_congr rfl fun x _ => by
    rw [Finset.card_product, fockCount_eq_card, fockCount_eq_card]

open PowerSeries

/-- The generating function `Σ_w P(r,w) q^w`. -/
noncomputable def fockGenFun (r : ℕ) : PowerSeries ℂ := PowerSeries.mk fun w => (fockCount r w : ℂ)

theorem fockGenFun_succ (r : ℕ) : fockGenFun (r + 1) = fockGenFun r * fockGenFun 1 := by
  ext n
  rw [fockGenFun, PowerSeries.coeff_mk, fockCount_succ, PowerSeries.coeff_mul]
  push_cast
  simp only [fockGenFun, PowerSeries.coeff_mk]

theorem fockGenFun_zero : fockGenFun 0 = 1 := by
  ext n
  rw [fockGenFun, PowerSeries.coeff_mk, fockCount_zero_colours, PowerSeries.coeff_one]
  split_ifs <;> simp

theorem fockGenFun_eq_pow (r : ℕ) : fockGenFun r = fockGenFun 1 ^ r := by
  induction r with
  | zero => rw [fockGenFun_zero, pow_zero]
  | succ r ih => rw [fockGenFun_succ, ih, pow_succ]

theorem fockGenFun_one :
    fockGenFun 1 = PowerSeries.mk fun n => ((Nat.Partition.restricted n fun _ => True).card : ℂ) := by
  ext n
  simp [fockGenFun, fockCount_one_eq_card_partition, Nat.Partition.restricted]

open scoped PowerSeries.WithPiTopology in
/-- The geometric factor `Σ_j q^{(n+1)j} = (1 - q^{n+1})^{-1}`. -/
theorem tsum_X_pow_mul_eq_inv (n : ℕ) :
    ∑' j : ℕ, (PowerSeries.X : ℂ⟦X⟧) ^ ((n + 1) * j) = (1 - PowerSeries.X ^ (n + 1))⁻¹ := by
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp)]
  simp_rw [pow_mul]
  exact PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)

open scoped PowerSeries.WithPiTopology in
/-- **The Fock generating function**: `Σ_w P(r,w) q^w = ∏_{n≥1} (1 - q^n)^{-r}` as an infinite
product of formal power series (`X`-adic / coefficientwise topology). -/
theorem hasProd_fockGenFun (r : ℕ) :
    HasProd (fun i : ℕ => ((1 - (PowerSeries.X : ℂ⟦X⟧) ^ (i + 1))⁻¹) ^ r) (fockGenFun r) := by
  rw [fockGenFun_eq_pow, fockGenFun_one]
  have h := Nat.Partition.hasProd_powerSeriesMk_card_restricted ℂ (fun _ => True)
  simp only [if_true, tsum_X_pow_mul_eq_inv] at h
  exact h.pow r

/-! ### The signed count `P⁺ - P⁻` and `∏_{n≥1}(1+q^n)^{-r}` -/

/-- The signed Fock count `Σ_{weight d = w} (-1)^{deg d} = P⁺(r,w) - P⁻(r,w) = tr(σ | (Fock)_w)`. -/
noncomputable def fockSigned (r w : ℕ) : ℤ := ∑ d ∈ fockFinset r w, (-1 : ℤ) ^ d.degree

theorem fockSigned_eq (r w : ℕ) :
    fockSigned r w = (fockCountEven r w : ℤ) - fockCountOdd r w := by
  classical
  have hE : fockCountEven r w = ((fockFinset r w).filter fun d : (ℕ × Fin r) →₀ ℕ => _root_.Even d.degree).card := by
    rw [fockCountEven, ← Set.ncard_coe_finset]
    congr 1; ext d; simp [fockSetEven, mem_fockFinset]
  have hO : fockCountOdd r w = ((fockFinset r w).filter fun d : (ℕ × Fin r) →₀ ℕ => ¬ _root_.Even d.degree).card := by
    rw [fockCountOdd, ← Set.ncard_coe_finset]
    congr 1; ext d; simp [fockSetOdd, mem_fockFinset, Nat.not_even_iff_odd]
  rw [fockSigned, ← Finset.sum_filter_add_sum_filter_not _ (fun d : (ℕ × Fin r) →₀ ℕ => _root_.Even d.degree), hE, hO,
    Finset.sum_congr rfl (g := fun _ => (1 : ℤ)) (fun d hd => (Finset.mem_filter.mp hd).2.neg_one_pow),
    Finset.sum_congr rfl (g := fun _ => (-1 : ℤ))
      (fun d hd => (Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hd).2).neg_one_pow)]
  simp [sub_eq_add_neg]

theorem degree_mapDomain {σ τ : Type*} (f : σ → τ) (l : σ →₀ ℕ) :
    (Finsupp.mapDomain f l).degree = l.degree := by
  rw [Finsupp.degree_eq_weight_one, weight_mapDomain, Finsupp.degree_eq_weight_one]
  rfl

theorem degree_splitExp (r : ℕ) (p : ((ℕ × Fin r) →₀ ℕ) × ((ℕ × Fin 1) →₀ ℕ)) :
    (splitExp r p).degree = p.1.degree + p.2.degree := by
  simp only [splitExp, Equiv.trans_apply, Finsupp.equivCongrLeft_apply,
    Finsupp.equivMapDomain_eq_mapDomain, Finsupp.sumFinsuppEquivProdFinsupp_symm_apply]
  rw [degree_mapDomain, Finsupp.sumElim_eq_add, map_add, degree_mapDomain, degree_mapDomain]

/-- Signed colour convolution. -/
theorem fockSigned_succ (r n : ℕ) :
    fockSigned (r + 1) n
      = ∑ x ∈ Finset.antidiagonal n, fockSigned r x.1 * fockSigned 1 x.2 := by
  classical
  rw [fockSigned, fockFinset_succ, Finset.sum_map,
    Finset.sum_biUnion (fockFinset_pairwiseDisjoint r n)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [fockSigned, fockSigned, Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Equiv.coe_toEmbedding, degree_splitExp, pow_add]

theorem fockFinset_zero_colours (n : ℕ) :
    fockFinset 0 n = if n = 0 then {0} else ∅ := by
  ext d
  have hd : d = 0 := Subsingleton.elim _ _
  subst hd
  rw [mem_fockFinset, map_zero]
  split_ifs with h <;> simp [h, eq_comm]

theorem fockSigned_zero_colours (n : ℕ) : fockSigned 0 n = if n = 0 then 1 else 0 := by
  rw [fockSigned, fockFinset_zero_colours]
  split_ifs <;> simp

/-- One colour: `Σ_d (-1)^{deg d} = Σ_{λ ⊢ n} (-1)^{#parts λ}`. -/
theorem fockSigned_one (n : ℕ) :
    fockSigned 1 n = ∑ p : n.Partition, (-1 : ℤ) ^ Multiset.card p.parts := by
  rw [fockSigned]
  refine Finset.sum_bij (fun d hd => toPartition n ⟨d, mem_fockFinset.mp hd⟩)
    (fun _ _ => Finset.mem_univ _) (fun d hd d' hd' h => ?_) (fun p _ => ?_) (fun d hd => ?_)
  · exact congrArg Subtype.val ((toPartition_bijective n).1 h)
  · obtain ⟨⟨d, hd⟩, rfl⟩ := (toPartition_bijective n).2 p
    exact ⟨d, mem_fockFinset.mpr hd, rfl⟩
  · simp only [toPartition, Multiset.card_map, Finsupp.card_toMultiset]
    rfl

open scoped PowerSeries.WithPiTopology in
/-- The signed geometric factor `1 + Σ_{j≥1} (-1)^j q^{(n+1)j} = (1 + q^{n+1})^{-1}`. -/
theorem signed_factor_eq_inv (n : ℕ) :
    1 + ∑' j : ℕ, (-1 : ℂ) ^ (j + 1) • (PowerSeries.X : ℂ⟦X⟧) ^ ((n + 1) * (j + 1))
      = (1 + PowerSeries.X ^ (n + 1))⁻¹ := by
  set g : ℂ⟦X⟧ := -PowerSeries.X ^ (n + 1) with hg
  have hg0 : PowerSeries.constantCoeff g = 0 := by simp [hg]
  have hterm : ∀ j : ℕ, (-1 : ℂ) ^ (j + 1) • (PowerSeries.X : ℂ⟦X⟧) ^ ((n + 1) * (j + 1))
      = g ^ (j + 1) := by
    intro j
    rw [hg, pow_mul]
    rcases Nat.even_or_odd (j + 1) with h | h
    · rw [h.neg_one_pow, one_smul, h.neg_pow]
    · rw [h.neg_one_pow, neg_one_smul, h.neg_pow]
  simp_rw [hterm]
  have hsum := PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero hg0
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp)]
  have h1 := PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero hg0
  rw [hsum.tsum_eq_zero_add, pow_zero] at h1
  rw [show (1 : ℂ⟦X⟧) + PowerSeries.X ^ (n + 1) = 1 - g by rw [hg, sub_neg_eq_add]]
  exact h1

/-- The signed generating function `Σ_w (P⁺ - P⁻)(r,w) q^w`. -/
noncomputable def fockSignedGenFun (r : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun w => (fockSigned r w : ℂ)

theorem fockSignedGenFun_succ (r : ℕ) :
    fockSignedGenFun (r + 1) = fockSignedGenFun r * fockSignedGenFun 1 := by
  ext n
  rw [fockSignedGenFun, PowerSeries.coeff_mk, fockSigned_succ, PowerSeries.coeff_mul]
  push_cast
  simp only [fockSignedGenFun, PowerSeries.coeff_mk]

theorem fockSignedGenFun_zero : fockSignedGenFun 0 = 1 := by
  ext n
  rw [fockSignedGenFun, PowerSeries.coeff_mk, fockSigned_zero_colours, PowerSeries.coeff_one]
  split_ifs <;> simp

theorem fockSignedGenFun_eq_pow (r : ℕ) : fockSignedGenFun r = fockSignedGenFun 1 ^ r := by
  induction r with
  | zero => rw [fockSignedGenFun_zero, pow_zero]
  | succ r ih => rw [fockSignedGenFun_succ, ih, pow_succ]

theorem fockSignedGenFun_one :
    fockSignedGenFun 1 = Nat.Partition.genFun fun (_ c : ℕ) => (-1 : ℂ) ^ c := by
  ext n
  rw [fockSignedGenFun, PowerSeries.coeff_mk, Nat.Partition.coeff_genFun, fockSigned_one]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← Multiset.toFinsupp_sum_eq]
  rfl

open scoped PowerSeries.WithPiTopology in
/-- **The signed Fock generating function**: `Σ_w (P⁺ - P⁻)(r,w) q^w = ∏_{n≥1} (1 + q^n)^{-r}`,
the graded trace of `σ = (-1)^{degree}` on the rank-`r` Fock space. -/
theorem hasProd_fockSignedGenFun (r : ℕ) :
    HasProd (fun i : ℕ => ((1 + (PowerSeries.X : ℂ⟦X⟧) ^ (i + 1))⁻¹) ^ r)
      (fockSignedGenFun r) := by
  rw [fockSignedGenFun_eq_pow, fockSignedGenFun_one]
  have h := Nat.Partition.hasProd_genFun fun (_ c : ℕ) => (-1 : ℂ) ^ c
  simp only [signed_factor_eq_inv] at h
  exact h.pow r

/-- **`dim (V_L^+)_k = ½(dim (V_L)_k + tr(θ|(V_L)_k))`** with `tr θ = fockSigned r k`, the
`q^k` coefficient of `∏_{n≥1}(1+q^n)^{-r}` (`hasProd_fockSignedGenFun`). -/
theorem two_mul_finrank_plusK_eq_signed (L : IntegralLattice) (hPos : L.PosDef) (hEven : L.Even)
    (k : ℕ) :
    2 * (finrank ℂ (plusK L k) : ℤ) = finrank ℂ (gradingLatGen L k) + fockSigned (rank L) k := by
  have h := two_mul_finrank_plusK L hPos hEven k
  rw [fockSigned_eq]
  omega

end GenFun

end LatGen

namespace Moonshine

/-! ## §6  The Leech lattice -/

open LatGen IntegralLattice Module

theorem leech_normEq_zero_card : (normEq leech leech_posDef 0).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨0, ?_⟩
  ext α
  rw [mem_normEq, Finset.mem_singleton]
  constructor
  · intro h
    by_contra hα
    have := leech_posDef α hα
    omega
  · rintro rfl; simp

theorem leech_normEq_two_card : (normEq leech leech_posDef 2).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro α hα
  exact leech_no_roots α ((mem_normEq _ _).mp hα)

theorem leech_normEq_four_card : (normEq leech leech_posDef 4).card = 196560 := by
  rw [normEq, ← Set.ncard_eq_toFinset_card _ (normEq_finite leech leech_posDef 4)]
  exact Leech.repCount_four

theorem leech_normEq_six_card : (normEq leech leech_posDef 6).card = 16773120 := by
  rw [normEq, ← Set.ncard_eq_toFinset_card _ (normEq_finite leech leech_posDef 6)]
  exact Leech.repCount_six

/-- **`dim (V_Λ)₂ = 196884`, recovered from the general theta-series formula**
`dim (V_Λ)₂ = #{0}·P(24,2) + #{⟨α,α⟩=2}·P(24,1) + #{⟨α,α⟩=4}·P(24,0) = 324 + 0 + 196560`. -/
theorem leechVOA_finrank_grading_two_theta : finrank ℂ (leechVOA.grading 2) = 196884 := by
  change finrank ℂ (gradingLatGen leech ((2 : ℕ) : ℤ)) = 196884
  rw [finrank_gradingLatGen_eq_sum_theta leech leech_posDef leech_even 2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num only [leech_normEq_zero_card, leech_normEq_two_card, leech_normEq_four_card,
    fockCount_zero, fockCount_two, leech_rank]
  simp [Nat.choose_two_right]

/-- The weight-`k` space of `V_Λ⁺` is the `θ`-fixed part of `(V_Λ)_k`. -/
noncomputable def leechVOAPlusGradingEquiv (k : ℤ) : leechVOAPlus.grading k ≃ₗ[ℂ] plusK leech k := by
  refine (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).trans
    (LinearEquiv.ofEq _ _ ?_)
  rw [show leechVOAPlus.grading k = (leechVOA.grading k).comap
      (orbifold (Subgroup.zpowers leechTheta)).carrier.subtype from rfl,
    Submodule.map_comap_subtype]
  ext x
  rw [Submodule.mem_inf, mem_plusK, mem_leechVOAPlus_iff, and_comm]
  rfl

/-- **`dim (V_Λ⁺)₂ = 98580`, recovered from the general `θ`-split**
`2·dim (V_Λ⁺)₂ + P⁻(24,2) = dim (V_Λ)₂ + P⁺(24,2)`, i.e. `2·98580 + 24 = 196884 + 300`. -/
theorem leechVOAPlus_finrank_grading_two_theta : finrank ℂ (leechVOAPlus.grading 2) = 98580 := by
  rw [(leechVOAPlusGradingEquiv 2).finrank_eq]
  have h := two_mul_finrank_plusK leech leech_posDef leech_even 2
  have hV : finrank ℂ (gradingLatGen leech ((2 : ℕ) : ℤ)) = 196884 :=
    leechVOA_finrank_grading_two_theta
  have hO : fockCountOdd (rank leech) 2 = 24 := by rw [fockCountOdd_two, leech_rank]
  have hE : fockCountEven (rank leech) 2 = 300 := by rw [fockCountEven_two, leech_rank]; rfl
  rw [hV, hO, hE] at h
  change 2 * finrank ℂ (plusK leech 2) + 24 = 196884 + 300 at h
  omega

/-- **`dim (V_Λ)₃ = 21493760`** from the theta-series formula:
`P(24,3) + 0·P(24,2) + 196560·P(24,1) + 16773120·P(24,0) = 3200 + 4717440 + 16773120`
(the `q²` coefficient `21493760` of `J`). -/
theorem leechVOA_finrank_grading_three : finrank ℂ (leechVOA.grading 3) = 21493760 := by
  change finrank ℂ (gradingLatGen leech ((3 : ℕ) : ℤ)) = 21493760
  rw [finrank_gradingLatGen_eq_sum_theta leech leech_posDef leech_even 3]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num only [leech_normEq_zero_card, leech_normEq_two_card, leech_normEq_four_card,
    leech_normEq_six_card, fockCount_zero, fockCount_one, fockCount_three, leech_rank]
  rw [show Nat.choose 26 3 = 2600 by decide]; simp

/-- **`dim (V_Λ⁺)₃ = 10745856`** from the `θ`-split: `2·dim (V_Λ⁺)₃ + P⁻(24,3) = dim (V_Λ)₃ + P⁺(24,3)`
with `P⁺(24,3) = 24² = 576` (`h_a(-2)h_b(-1)𝟙`) and `P⁻(24,3) = 24 + C(26,3) = 2624`
(`h_a(-3)𝟙`, `h_a(-1)h_b(-1)h_c(-1)𝟙`). -/
theorem leechVOAPlus_finrank_grading_three : finrank ℂ (leechVOAPlus.grading 3) = 10745856 := by
  rw [(leechVOAPlusGradingEquiv 3).finrank_eq]
  have h := two_mul_finrank_plusK leech leech_posDef leech_even 3
  have hV : finrank ℂ (gradingLatGen leech ((3 : ℕ) : ℤ)) = 21493760 :=
    leechVOA_finrank_grading_three
  have hO : fockCountOdd (rank leech) 3 = 2624 := by rw [fockCountOdd_three, leech_rank, show Nat.choose 26 3 = 2600 by decide]
  have hE : fockCountEven (rank leech) 3 = 576 := by rw [fockCountEven_three, leech_rank]
  rw [hV, hO, hE] at h
  change 2 * finrank ℂ (plusK leech 3) + 2624 = 21493760 + 576 at h
  generalize finrank ℂ (plusK leech 3) = X at h ⊢
  omega

end Moonshine

end VOA
