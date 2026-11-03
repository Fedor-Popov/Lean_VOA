/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.PlusWeightOne
import VOA.LatticesAndCodes.Leech.RepCount
import Mathlib.Data.Sym.Card

/-!
# `dim (V_Λ)₂ = 196884` and `dim (V_Λ⁺)₂ = 98580`  (Moonshine step M7a)

For an even positive-definite lattice `L` **without roots**, the weight-`2` space of the lattice VOA
`V_L` is

  `(V_L)₂ = (Fock)₂ ⊗ e^0 ⊕ ⨁_{⟨α,α⟩ = 4} ℂ e^α`        (`LatGen.gradingLatGen_two_of_rootless`),

and `(Fock)₂` is spanned by the `r` states `h_a(-2)𝟙` and the `r(r+1)/2` states `h_a(-1)h_b(-1)𝟙`
(`LatGen.finrank_gradingWN_two`, via the explicit monomial count `LatGen.weight_eq_two`).  Hence
`dim (V_L)₂ = r + r(r+1)/2 + #{⟨α,α⟩ = 4}` (`LatGen.finrank_gradingLatGen_two`).

For the involution `θ = σ ⊗ (e^α ↦ e^{-α})`: `σ = (-1)^{degree}` is `+1` on the quadratic states and
`-1` on `h_a(-2)𝟙` (`LatGen.sigmaN_of_mem_quadFock`, `LatGen.sigmaN_of_mem_linFock`); and `θ`
swaps `e^α ↔ e^{-α}`.  Choosing a half `S` of the norm-`4` vectors (one of each pair `±α`, via a
well-order: `LatGen.halfFour`), the fixed space contains `h(-1)h(-1)𝟙 ⊕ {x + θx : x ∈ B_S}` and the
anti-fixed space contains `h(-2)𝟙 ⊕ {x - θx : x ∈ B_S}`; the two lower bounds already add up to
`dim (V_L)₂`, so both are equalities (`LatGen.finrank_plusTwo`).  No trace or projection
argument is needed.

For the Leech lattice (`r = 24`, `196560` minimal vectors by `Leech.repCount_four`):

* `Moonshine.leechVOA_finrank_grading_two : finrank ℂ (leechVOA.grading 2) = 196884`
  (`= 24 + 300 + 196560`);
* `Moonshine.leechVOAPlus_finrank_grading_two : finrank ℂ (leechVOAPlus.grading 2) = 98580`
  (`= 300 + 98280`).

Together with the twisted-sector count `dim ((V_Λ^T)⁺)₂ = 2¹²·24 = 98304` (not done here) this
gives the Griess-algebra dimension `98580 + 98304 = 196884`.

## Status
All declarations `sorry`-free; `#print axioms` for both Leech theorems gives
`[propext, Classical.choice, Quot.sound]` (no `VOA.pbw`).  Unconditional: the only inputs are
`leech_even`, `leech_posDef`, `leech_no_roots`, `leech_rank` and `Leech.repCount_four`, all proved.
Not done here: the twisted-sector weight-`2` count (needs M5/M6) and the full graded dimension.
-/

set_option linter.style.longLine false

open scoped TensorProduct

namespace VOA

namespace LatGen

open HeisenbergN MvPolynomial Module IntegralLattice

/-! ## §1  The weight-`2` Fock space -/

section Fock

variable (r : ℕ)

theorem weight_eq_zero_iff (d : (ℕ × Fin r) →₀ ℕ) :
    Finsupp.weight weightFnN d = 0 → d = 0 := by
  intro h
  ext i
  by_contra hi
  have := Finsupp.le_weight_of_ne_zero' weightFnN hi
  rw [h, weightFnN_apply] at this
  omega

/-- Split off one support point: `weight d = d x · (x.1+1) + weight (d.erase x)`. -/
theorem weight_split (d : (ℕ × Fin r) →₀ ℕ) (x : ℕ × Fin r) :
    Finsupp.weight weightFnN d
      = d x * (x.1 + 1) + Finsupp.weight weightFnN (d.erase x) := by
  conv_lhs => rw [← Finsupp.single_add_erase x d]
  rw [map_add, Finsupp.weight_single, weightFnN_apply, smul_eq_mul]

theorem weight_eq_one (d : (ℕ × Fin r) →₀ ℕ) (h : Finsupp.weight weightFnN d = 1) :
    ∃ a : Fin r, d = Finsupp.single (0, a) 1 := by
  have hd : d ≠ 0 := by rintro rfl; simp at h
  obtain ⟨⟨m, a⟩, hx⟩ := Finsupp.ne_iff.mp hd
  rw [Finsupp.coe_zero, Pi.zero_apply] at hx
  have hs : Finsupp.weight weightFnN d = d (m, a) * (m + 1) + Finsupp.weight weightFnN (d.erase (m, a)) :=
    weight_split r d (m, a)
  rw [h] at hs
  have h1 : d (m, a) ≤ d (m, a) * (m + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have h2 : m + 1 ≤ d (m, a) * (m + 1) := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hx)
  have hn : d (m, a) = 1 := by omega
  have hm : m = 0 := by omega
  have he : d.erase (m, a) = 0 := weight_eq_zero_iff r _ (by rw [hn] at hs; omega)
  refine ⟨a, ?_⟩
  rw [← Finsupp.single_add_erase (m, a) d, he, add_zero, hn, hm]

theorem weight_eq_two (d : (ℕ × Fin r) →₀ ℕ) (h : Finsupp.weight weightFnN d = 2) :
    (∃ a : Fin r, d = Finsupp.single (1, a) 1) ∨
      ∃ a b : Fin r, d = Finsupp.single (0, a) 1 + Finsupp.single (0, b) 1 := by
  have hd : d ≠ 0 := by rintro rfl; simp at h
  obtain ⟨⟨m, a⟩, hx⟩ := Finsupp.ne_iff.mp hd
  rw [Finsupp.coe_zero, Pi.zero_apply] at hx
  have hs : Finsupp.weight weightFnN d = d (m, a) * (m + 1) + Finsupp.weight weightFnN (d.erase (m, a)) :=
    weight_split r d (m, a)
  rw [h] at hs
  have h1 : d (m, a) ≤ d (m, a) * (m + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have h2 : m + 1 ≤ d (m, a) * (m + 1) := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hx)
  have hdecomp := Finsupp.single_add_erase (m, a) d
  have hn2 : d (m, a) ≤ 2 := by omega
  have hm1 : m ≤ 1 := by omega
  interval_cases hn : d (m, a)
  · exact absurd rfl hx
  · interval_cases m
    · -- one variable at level 0, remaining weight 1
      obtain ⟨b, hb⟩ := weight_eq_one r (d.erase (0, a)) (by omega)
      right; exact ⟨a, b, by rw [← hdecomp, hb]⟩
    · have he : d.erase (1, a) = 0 := weight_eq_zero_iff r _ (by omega)
      left; exact ⟨a, by rw [← hdecomp, he, add_zero]⟩
  · interval_cases m
    · have he : d.erase (0, a) = 0 := weight_eq_zero_iff r _ (by omega)
      right
      exact ⟨a, a, by rw [← hdecomp, he, add_zero, ← Finsupp.single_add]⟩
    · omega

/-- The quadratic level-`0` exponent `h_a(-1) h_b(-1)`, symmetric in `a, b`. -/
noncomputable def quadExp : Sym2 (Fin r) → (ℕ × Fin r) →₀ ℕ :=
  Sym2.lift ⟨fun a b => Finsupp.single (0, a) 1 + Finsupp.single (0, b) 1,
    fun _ _ => add_comm _ _⟩

@[simp] theorem quadExp_mk (a b : Fin r) :
    quadExp r s(a, b) = Finsupp.single (0, a) 1 + Finsupp.single (0, b) 1 := rfl

theorem quadExp_injective : Function.Injective (quadExp r) := by
  intro s t hst
  induction s using Sym2.ind with
  | _ a b =>
  induction t using Sym2.ind with
  | _ c d =>
  rw [quadExp_mk, quadExp_mk] at hst
  rw [Sym2.eq_iff]
  have hsingle : ∀ x y : Fin r, Finsupp.single ((0 : ℕ), x) 1 = Finsupp.single (0, y) 1 → x = y :=
    fun x y hxy => by
      have := (Finsupp.single_left_inj (one_ne_zero (α := ℕ))).mp hxy
      exact (Prod.mk.inj this).2
  by_cases hac : a = c
  · subst hac
    exact Or.inl ⟨rfl, hsingle _ _ (add_left_cancel hst)⟩
  · by_cases had : a = d
    · subst had
      rw [add_comm (Finsupp.single (0, c) 1)] at hst
      exact Or.inr ⟨rfl, hsingle _ _ (add_left_cancel hst)⟩
    · exfalso
      have := congrArg (fun f => f ((0 : ℕ), a)) hst
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, Prod.mk.injEq, true_and,
        Ne.symm hac, Ne.symm had, if_false, if_true] at this
      omega

theorem degree_quadExp (s : Sym2 (Fin r)) : (quadExp r s).degree = 2 := by
  induction s using Sym2.ind with
  | _ a b => rw [quadExp_mk, map_add, Finsupp.degree_single, Finsupp.degree_single]

/-- The weight-`2` exponents: `h_a(-2)` (`Sum.inl a`) and `h_a(-1)h_b(-1)` (`Sum.inr s(a,b)`). -/
noncomputable def wt2Exp : Fin r ⊕ Sym2 (Fin r) → (ℕ × Fin r) →₀ ℕ
  | Sum.inl a => Finsupp.single (1, a) 1
  | Sum.inr s => quadExp r s

theorem degree_wt2Exp_inl (a : Fin r) : (wt2Exp r (Sum.inl a)).degree = 1 :=
  Finsupp.degree_single _ _

theorem wt2Exp_injective : Function.Injective (wt2Exp r) := by
  rintro (a | s) (b | t) h
  · have := (Finsupp.single_left_inj (one_ne_zero (α := ℕ))).mp h
    rw [(Prod.mk.inj this).2]
  · have h1 := congrArg Finsupp.degree h
    simp only [wt2Exp] at h1
    rw [Finsupp.degree_single, degree_quadExp] at h1
    omega
  · have h1 := congrArg Finsupp.degree h
    simp only [wt2Exp] at h1
    rw [Finsupp.degree_single, degree_quadExp] at h1
    omega
  · exact congrArg Sum.inr (quadExp_injective r h)

theorem weight_wt2Exp (i : Fin r ⊕ Sym2 (Fin r)) : Finsupp.weight weightFnN (wt2Exp r i) = 2 := by
  rcases i with a | s
  · simp only [wt2Exp]; rw [Finsupp.weight_single, weightFnN_apply]; rfl
  · induction s using Sym2.ind with
    | _ a b =>
      simp only [wt2Exp, quadExp_mk]
      rw [map_add, Finsupp.weight_single, Finsupp.weight_single, weightFnN_apply, weightFnN_apply]
      rfl

/-- The weight-`2` monomials. -/
noncomputable def wt2Mon (i : Fin r ⊕ Sym2 (Fin r)) : FockN r := monomial (wt2Exp r i) 1

theorem wt2Mon_linearIndependent : LinearIndependent ℂ (wt2Mon r) := by
  have h := (MvPolynomial.basisMonomials (ℕ × Fin r) ℂ).linearIndependent.comp _
    (wt2Exp_injective r)
  convert h using 1

theorem gradingWN_two_eq_span : gradingWN r 2 = Submodule.span ℂ (Set.range (wt2Mon r)) := by
  apply le_antisymm
  · refine le_trans (gradingWN_le_span r 2) (Submodule.span_mono ?_)
    rintro _ ⟨d, hd, rfl⟩
    rcases weight_eq_two r d hd with ⟨a, rfl⟩ | ⟨a, b, rfl⟩
    · exact ⟨Sum.inl a, rfl⟩
    · exact ⟨Sum.inr s(a, b), rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact isWeightedHomogeneous_monomial weightFnN _ _ (weight_wt2Exp r i)

/-- **`dim (FockN r)₂ = r + r(r+1)/2`**: the states `h_a(-2)𝟙` and `h_a(-1)h_b(-1)𝟙`. -/
theorem finrank_gradingWN_two : finrank ℂ (gradingWN r 2) = r + (r + 1).choose 2 := by
  rw [gradingWN_two_eq_span, finrank_span_eq_card (wt2Mon_linearIndependent r),
    Fintype.card_sum, Sym2.card, Fintype.card_fin]

/-- The quadratic part `span {h_a(-1)h_b(-1)𝟙}`. -/
noncomputable def quadFock : Submodule ℂ (FockN r) :=
  Submodule.span ℂ (Set.range (wt2Mon r ∘ Sum.inr))

/-- The linear part `span {h_a(-2)𝟙}`. -/
noncomputable def linFock : Submodule ℂ (FockN r) :=
  Submodule.span ℂ (Set.range (wt2Mon r ∘ Sum.inl))

theorem finrank_quadFock : finrank ℂ (quadFock r) = (r + 1).choose 2 := by
  rw [quadFock, finrank_span_eq_card ((wt2Mon_linearIndependent r).comp _ Sum.inr_injective),
    Sym2.card, Fintype.card_fin]

theorem finrank_linFock : finrank ℂ (linFock r) = r := by
  rw [linFock, finrank_span_eq_card ((wt2Mon_linearIndependent r).comp _ Sum.inl_injective),
    Fintype.card_fin]

theorem quadFock_le : quadFock r ≤ gradingWN r 2 := by
  rw [gradingWN_two_eq_span]; exact Submodule.span_mono (Set.range_comp_subset_range _ _)

theorem linFock_le : linFock r ≤ gradingWN r 2 := by
  rw [gradingWN_two_eq_span]; exact Submodule.span_mono (Set.range_comp_subset_range _ _)

/-- `σ = +1` on the quadratic states. -/
theorem sigmaN_of_mem_quadFock {p : FockN r} (hp : p ∈ quadFock r) : sigmaN r p = p := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      change sigmaN r (monomial (quadExp r s) 1) = monomial (quadExp r s) 1
      rw [sigmaN_monomial, degree_quadExp]; simp
  | zero => rw [map_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

/-- `σ = -1` on the linear states. -/
theorem sigmaN_of_mem_linFock {p : FockN r} (hp : p ∈ linFock r) : sigmaN r p = -p := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      change sigmaN r (monomial (wt2Exp r (Sum.inl a)) 1) = -monomial (wt2Exp r (Sum.inl a)) 1
      rw [sigmaN_monomial, degree_wt2Exp_inl]; simp
  | zero => rw [map_zero, neg_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy, neg_add]
  | smul c x _ hx => rw [map_smul, hx, smul_neg]

end Fock

/-! ## §2  Finite sums of independent submodules -/

section Indep

variable {ι V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- For an independent family, the dimension of a finite `⨆` is the sum of the dimensions. -/
theorem finrank_biSup_of_iSupIndep (p : ι → Submodule ℂ V) (hp : iSupIndep p)
    [∀ i, FiniteDimensional ℂ (p i)] (s : Finset ι) :
    FiniteDimensional ℂ ↥(⨆ i ∈ s, p i) ∧
      finrank ℂ ↥(⨆ i ∈ s, p i) = ∑ i ∈ s, finrank ℂ (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 : (⨆ i ∈ (∅ : Finset ι), p i) = ⊥ := by simp
      rw [h0, Finset.sum_empty, finrank_bot]
      exact ⟨inferInstance, rfl⟩
  | insert a s ha ih =>
      obtain ⟨hfd, hrk⟩ := ih
      rw [Finset.iSup_insert, Finset.sum_insert ha]
      have hdisj : Disjoint (p a) (⨆ i ∈ s, p i) := by
        have := hp.disjoint_biSup (y := (s : Set ι)) (by simpa using ha)
        simpa using this
      refine ⟨inferInstance, ?_⟩
      have h := Submodule.finrank_sup_add_finrank_inf_eq (p a) (⨆ i ∈ s, p i)
      rw [hdisj.eq_bot, finrank_bot, add_zero] at h
      rw [h, hrk]

/-- A linear map injective on `p` preserves its dimension. -/
theorem finrank_map_of_injOn (p : Submodule ℂ V) (f : V →ₗ[ℂ] W)
    (hf : ∀ x ∈ p, f x = 0 → x = 0) : finrank ℂ ↥(p.map f) = finrank ℂ p := by
  rw [← LinearMap.range_domRestrict]
  apply LinearMap.finrank_range_of_inj
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  exact (Submodule.mem_bot ℂ).mpr (Subtype.ext (hf x x.2 hx))

end Indep

/-! ## §3  The weight-`2` space of a rootless lattice VOA -/

section Lattice

variable (L : IntegralLattice)

theorem mkEα_injective (α : L.carrier) : Function.Injective (mkEα L α) := by
  intro p q h
  have := congrArg (coordEα L α) h
  rwa [mkEα_apply, mkEα_apply, coordEα_apply, coordEα_apply, if_pos rfl, if_pos rfl] at this

theorem finrank_bigradα (w : ℕ) (α : L.carrier) :
    finrank ℂ (bigradα L (w, α)) = finrank ℂ (gradingWN (rank L) w) := by
  rw [bigradα, ← (Submodule.equivMapOfInjective _ (mkEα_injective L α) _).finrank_eq,
    gradingZN_of_nonneg (by positivity), Int.toNat_natCast]

theorem finrank_bigradα_zero (α : L.carrier) : finrank ℂ (bigradα L (0, α)) = 1 := by
  rw [show ((0 : ℤ), α) = (((0 : ℕ) : ℤ), α) from rfl, finrank_bigradα,
    gradingWN_zero_eq_span_one, finrank_span_singleton one_ne_zero]

/-- The charge-sector family `α ↦ ℂ e^α = bigradα (0, α)` is independent. -/
theorem iSupIndep_bigradα_zero : iSupIndep (fun α : L.carrier => bigradα L (0, α)) :=
  (bigradα_iSupIndep L).comp (f := fun α => ((0 : ℤ), α)) (fun _ _ h => (Prod.mk.inj h).2)

theorem normFour_finite (hPos : L.PosDef) : {α : L.carrier | L.form α α = 4}.Finite :=
  (IntegralLattice.boundedFinite L hPos 4).subset fun _ h => le_of_eq h

/-- The norm-`4` vectors of `L`, as a finset. -/
noncomputable def normFour (hPos : L.PosDef) : Finset L.carrier := (normFour_finite L hPos).toFinset

theorem mem_normFour (hPos : L.PosDef) {α : L.carrier} : α ∈ normFour L hPos ↔ L.form α α = 4 :=
  Set.Finite.mem_toFinset _

/-- The span of the `e^α`, `⟨α,α⟩ = 4`. -/
noncomputable def chargeFour (hPos : L.PosDef) : Submodule ℂ (LatModuleGen L) :=
  ⨆ α ∈ normFour L hPos, bigradα L (0, α)

theorem disjoint_bigradα_chargeFour (hPos : L.PosDef) :
    Disjoint (bigradα L (2, 0)) (chargeFour L hPos) := by
  refine Disjoint.mono_right ?_ ((iSupIndep_def.mp (bigradα_iSupIndep L)) (2, 0))
  refine iSup₂_le fun α _ => ?_
  exact le_iSup₂ (f := fun (j : ℤ × L.carrier) (_ : j ≠ (2, 0)) => bigradα L j) ((0 : ℤ), α)
    (by simp)

/-- **The weight-`2` space of a rootless `V_L`**: `V_2 = (Fock weight 2 ⊗ e^0) ⊕ ⨁_{⟨α,α⟩=4} ℂ e^α`. -/
theorem gradingLatGen_two_of_rootless (hEven : L.Even) (hPos : L.PosDef)
    (hR : ∀ v : L.carrier, L.form v v ≠ 2) :
    gradingLatGen L 2 = bigradα L (2, 0) ⊔ chargeFour L hPos := by
  apply le_antisymm
  · refine iSup_le fun α => ?_
    rcases eq_or_ne α 0 with rfl | hα
    · rw [halfNorm_zero L, sub_zero]; exact le_sup_left
    · have hpos := halfNorm_pos L hEven hPos hα
      have h2 := two_halfNorm L hEven α
      have hne := hR α
      by_cases h4 : L.form α α = 4
      · rw [show (2 : ℤ) - halfNorm L α = 0 by omega]
        exact le_sup_of_le_right
          (le_biSup (fun α => bigradα L (0, α)) ((mem_normFour L hPos).mpr h4))
      · rw [bigradα_eq_bot_of_neg L α (by omega : 2 - halfNorm L α < 0)]; exact bot_le
  · refine sup_le ?_ (iSup₂_le fun α hα => ?_)
    · have h := bigradα_le_gradingLatGen L 2 0
      rwa [halfNorm_zero L, add_zero] at h
    · have h := bigradα_le_gradingLatGen L 0 α
      have h2 := two_halfNorm L hEven α
      rw [(mem_normFour L hPos).mp hα] at h2
      rwa [show (0 : ℤ) + halfNorm L α = 2 by omega] at h

instance chargeFour_finiteDimensional (hPos : L.PosDef) :
    FiniteDimensional ℂ (chargeFour L hPos) :=
  (finrank_biSup_of_iSupIndep _ (iSupIndep_bigradα_zero L) (normFour L hPos)).1

theorem finrank_biSup_bigradα_zero (s : Finset L.carrier) :
    finrank ℂ ↥(⨆ α ∈ s, bigradα L (0, α)) = s.card := by
  rw [(finrank_biSup_of_iSupIndep _ (iSupIndep_bigradα_zero L) s).2]
  simp [finrank_bigradα_zero]

theorem finrank_chargeFour (hPos : L.PosDef) :
    finrank ℂ (chargeFour L hPos) = (normFour L hPos).card :=
  finrank_biSup_bigradα_zero L _

/-- **`dim V_2 = dim (Fock)₂ + #{α : ⟨α,α⟩ = 4}`** for a rootless even positive-definite `L`. -/
theorem finrank_gradingLatGen_two (hEven : L.Even) (hPos : L.PosDef)
    (hR : ∀ v : L.carrier, L.form v v ≠ 2) :
    finrank ℂ (gradingLatGen L 2)
      = rank L + (rank L + 1).choose 2 + (normFour L hPos).card := by
  rw [gradingLatGen_two_of_rootless L hEven hPos hR]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (bigradα L (2, 0)) (chargeFour L hPos)
  rw [(disjoint_bigradα_chargeFour L hPos).eq_bot, finrank_bot, add_zero] at h
  rw [h, show ((2 : ℤ), (0 : L.carrier)) = (((2 : ℕ) : ℤ), 0) from rfl, finrank_bigradα,
    finrank_gradingWN_two, finrank_chargeFour]

end Lattice

/-! ## §4  The `θ`-fixed part of the weight-`2` space -/

section Theta

open Classical

variable (L : IntegralLattice)

/-- The `θ`-fixed part of `V_2`. -/
noncomputable def plusTwo : Submodule ℂ (LatModuleGen L) :=
  gradingLatGen L 2 ⊓ LinearMap.ker ((thetaLat L).toLinearMap - LinearMap.id)

/-- The `θ`-anti-fixed part of `V_2`. -/
noncomputable def minusTwo : Submodule ℂ (LatModuleGen L) :=
  gradingLatGen L 2 ⊓ LinearMap.ker ((thetaLat L).toLinearMap + LinearMap.id)

theorem mem_plusTwo {x : LatModuleGen L} :
    x ∈ plusTwo L ↔ x ∈ gradingLatGen L 2 ∧ thetaLat L x = x := by
  rw [plusTwo, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]; rfl

theorem mem_minusTwo {x : LatModuleGen L} :
    x ∈ minusTwo L ↔ x ∈ gradingLatGen L 2 ∧ thetaLat L x = -x := by
  rw [minusTwo, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.add_apply, add_eq_zero_iff_eq_neg]
  rfl

theorem disjoint_plusTwo_minusTwo : Disjoint (plusTwo L) (minusTwo L) := by
  rw [Submodule.disjoint_def]
  intro x hp hm
  have h1 := ((mem_plusTwo L).mp hp).2
  have h2 := ((mem_minusTwo L).mp hm).2
  rw [h1] at h2
  have h3 : (2 : ℂ) • x = 0 := by rw [two_smul]; nth_rewrite 1 [h2]; exact neg_add_cancel x
  exact (smul_eq_zero.mp h3).resolve_left two_ne_zero

variable (hPos : L.PosDef)

/-- A half `S` of the norm-`4` vectors: exactly one of `α, -α` lies in `S` (chosen by a
well-order on `L`). -/
noncomputable def halfFour : Finset L.carrier :=
  (normFour L hPos).filter fun α => WellOrderingRel α (-α)

theorem neg_mem_normFour {α : L.carrier} (h : α ∈ normFour L hPos) : -α ∈ normFour L hPos := by
  rw [mem_normFour] at h ⊢; simpa using h

theorem ne_neg_of_mem_normFour {α : L.carrier} (h : α ∈ normFour L hPos) : α ≠ -α := by
  intro he
  have h2α : (2 : ℤ) • α = 0 := by rw [two_smul]; nth_rewrite 2 [he]; exact add_neg_cancel α
  have h0 : α = 0 := (smul_eq_zero.mp h2α).resolve_left two_ne_zero
  rw [mem_normFour, h0] at h
  simp at h

theorem normFour_eq_union :
    normFour L hPos = halfFour L hPos ∪ (halfFour L hPos).image Neg.neg := by
  ext α
  simp only [halfFour, Finset.mem_union, Finset.mem_filter, Finset.mem_image]
  constructor
  · intro hα
    rcases trichotomous_of (WellOrderingRel (α := L.carrier)) α (-α) with h | h | h
    · exact Or.inl ⟨hα, h⟩
    · exact absurd h (ne_neg_of_mem_normFour L hPos hα)
    · exact Or.inr ⟨-α, ⟨neg_mem_normFour L hPos hα, by rwa [neg_neg]⟩, neg_neg α⟩
  · rintro (⟨hα, _⟩ | ⟨β, ⟨hβ, _⟩, rfl⟩)
    · exact hα
    · exact neg_mem_normFour L hPos hβ

theorem disjoint_halfFour_neg :
    Disjoint (halfFour L hPos) ((halfFour L hPos).image Neg.neg) := by
  rw [Finset.disjoint_left]
  intro α hα hα'
  simp only [halfFour, Finset.mem_filter, Finset.mem_image] at hα hα'
  obtain ⟨β, ⟨_, hβ⟩, rfl⟩ := hα'
  rw [neg_neg] at hα
  exact (asymm hβ) hα.2

theorem card_normFour_eq : (normFour L hPos).card = 2 * (halfFour L hPos).card := by
  rw [normFour_eq_union L hPos, Finset.card_union_of_disjoint (disjoint_halfFour_neg L hPos),
    Finset.card_image_of_injective _ neg_injective, two_mul]

/-- `B_S = ⨁_{α ∈ S} ℂ e^α`. -/
noncomputable def chargeHalf : Submodule ℂ (LatModuleGen L) :=
  ⨆ α ∈ halfFour L hPos, bigradα L (0, α)

/-- `B_{-S} = ⨁_{α ∈ S} ℂ e^{-α}`. -/
noncomputable def chargeHalfNeg : Submodule ℂ (LatModuleGen L) :=
  ⨆ α ∈ (halfFour L hPos).image Neg.neg, bigradα L (0, α)

instance chargeHalf_finiteDimensional : FiniteDimensional ℂ (chargeHalf L hPos) :=
  (finrank_biSup_of_iSupIndep _ (iSupIndep_bigradα_zero L) _).1

theorem finrank_chargeHalf : finrank ℂ (chargeHalf L hPos) = (halfFour L hPos).card :=
  finrank_biSup_bigradα_zero L _

theorem disjoint_chargeHalf : Disjoint (chargeHalf L hPos) (chargeHalfNeg L hPos) := by
  have h := (iSupIndep_bigradα_zero L).disjoint_biSup_biSup
    (s := (halfFour L hPos : Set L.carrier)) (t := ((halfFour L hPos).image Neg.neg : Set L.carrier))
    (Finset.disjoint_coe.mpr (disjoint_halfFour_neg L hPos))
  exact h

theorem chargeHalf_le : chargeHalf L hPos ≤ chargeFour L hPos :=
  biSup_mono fun α hα => by
    rw [normFour_eq_union L hPos]; exact Finset.mem_union_left _ hα

theorem chargeHalfNeg_le : chargeHalfNeg L hPos ≤ chargeFour L hPos :=
  biSup_mono fun α hα => by
    rw [normFour_eq_union L hPos]; exact Finset.mem_union_right _ hα

theorem thetaLat_mem_chargeHalfNeg {x : LatModuleGen L} (hx : x ∈ chargeHalf L hPos) :
    thetaLat L x ∈ chargeHalfNeg L hPos := by
  have hle : chargeHalf L hPos ≤ (chargeHalfNeg L hPos).comap (thetaLat L).toLinearMap := by
    refine iSup₂_le fun α hα y hy => ?_
    have h := thetaLat_mem_bigradα L hy
    exact (le_biSup (fun β => bigradα L (0, β)) (Finset.mem_image_of_mem Neg.neg hα)) h
  exact hle hx

/-- `x ↦ x ± θx` is injective on `B_S`. -/
theorem injOn_chargeHalf (c : ℂ) (x : LatModuleGen L) (hx : x ∈ chargeHalf L hPos)
    (h0 : (LinearMap.id + c • (thetaLat L).toLinearMap : LatModuleGen L →ₗ[ℂ] LatModuleGen L) x = 0) : x = 0 := by
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
    add_eq_zero_iff_eq_neg] at h0
  have hm : x ∈ chargeHalfNeg L hPos := by
    rw [h0]; exact Submodule.neg_mem _ (Submodule.smul_mem _ c (thetaLat_mem_chargeHalfNeg L hPos hx))
  exact (Submodule.disjoint_def.mp (disjoint_chargeHalf L hPos)) x hx hm

/-- **`dim (V_L^+)_2 = r(r+1)/2 + ½·#{⟨α,α⟩ = 4}`** for a rootless even positive-definite `L`
(stated with the half `S = halfFour`, `#{⟨α,α⟩ = 4} = 2·#S`).  The fixed space contains
`h(-1)h(-1)𝟙 ⊕ {x + θx : x ∈ B_S}`, the anti-fixed space contains `h(-2)𝟙 ⊕ {x - θx : x ∈ B_S}`,
and the two lower bounds already exhaust `dim V_2`. -/
theorem finrank_plusTwo (hEven : L.Even) (hR : ∀ v : L.carrier, L.form v v ≠ 2) :
    finrank ℂ (plusTwo L) = (rank L + 1).choose 2 + (halfFour L hPos).card := by
  haveI : FiniteDimensional ℂ (gradingLatGen L 2) := gradingLatGen_finrank_of_posDef L hEven hPos 2
  haveI : FiniteDimensional ℂ (plusTwo L) := Submodule.finiteDimensional_of_le inf_le_left
  haveI : FiniteDimensional ℂ (minusTwo L) := Submodule.finiteDimensional_of_le inf_le_left
  have hG := gradingLatGen_two_of_rootless L hEven hPos hR
  have hZ : HeisenbergN.gradingZN (rank L) 2 = gradingWN (rank L) 2 := gradingZN_of_nonneg (by norm_num)
  set θl : LatModuleGen L →ₗ[ℂ] LatModuleGen L := (thetaLat L).toLinearMap with hθl
  set fp : LatModuleGen L →ₗ[ℂ] LatModuleGen L := LinearMap.id + (1 : ℂ) • θl with hfp
  set fm : LatModuleGen L →ₗ[ℂ] LatModuleGen L := LinearMap.id + (-1 : ℂ) • θl with hfm
  have hfp_apply : ∀ y, fp y = y + thetaLat L y := fun y => by
    rw [hfp, LinearMap.add_apply, LinearMap.smul_apply, one_smul]; rfl
  have hfm_apply : ∀ y, fm y = y - thetaLat L y := fun y => by
    rw [hfm, LinearMap.add_apply, LinearMap.smul_apply, neg_one_smul, ← sub_eq_add_neg]; rfl
  -- the four pieces
  have hB2 : ∀ {q : Submodule ℂ (FockN (rank L))}, q ≤ gradingWN (rank L) 2 →
      q.map (mkEα L 0) ≤ bigradα L (2, 0) := fun hq => by
    rw [bigradα]; exact Submodule.map_mono (by rw [hZ]; exact hq)
  have hC : ∀ (f : LatModuleGen L →ₗ[ℂ] LatModuleGen L) (c : ℂ),
      (∀ y, f y = y + c • thetaLat L y) → (chargeHalf L hPos).map f ≤ chargeFour L hPos := by
    intro f c hf
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    rw [Submodule.mem_comap, hf]
    exact Submodule.add_mem _ (chargeHalf_le L hPos hy)
      (Submodule.smul_mem _ c (chargeHalfNeg_le L hPos (thetaLat_mem_chargeHalfNeg L hPos hy)))
  have hfinB : ∀ (f : LatModuleGen L →ₗ[ℂ] LatModuleGen L) (c : ℂ),
      f = LinearMap.id + c • θl →
      finrank ℂ ((chargeHalf L hPos).map f) = (halfFour L hPos).card := by
    intro f c hf
    rw [finrank_map_of_injOn _ _ (fun x hx h0 => injOn_chargeHalf L hPos c x hx (by rw [← hf]; exact h0)),
      finrank_chargeHalf]
  have hfinF : ∀ q : Submodule ℂ (FockN (rank L)), finrank ℂ (q.map (mkEα L 0)) = finrank ℂ q :=
    fun q => (Submodule.equivMapOfInjective _ (mkEα_injective L 0) q).finrank_eq.symm
  have hdimSup : ∀ {q : Submodule ℂ (FockN (rank L))} (f : LatModuleGen L →ₗ[ℂ] LatModuleGen L)
      (c : ℂ), q ≤ gradingWN (rank L) 2 → (∀ y, f y = y + c • thetaLat L y) →
      f = LinearMap.id + c • θl →
      finrank ℂ ↥(q.map (mkEα L 0) ⊔ (chargeHalf L hPos).map f)
        = finrank ℂ q + (halfFour L hPos).card := by
    intro q f c hq hf hf'
    haveI := gradingWN_finiteDimensional (rank L) 2
    haveI : FiniteDimensional ℂ q := Submodule.finiteDimensional_of_le hq
    have h := Submodule.finrank_sup_add_finrank_inf_eq (q.map (mkEα L 0)) ((chargeHalf L hPos).map f)
    rw [((disjoint_bigradα_chargeFour L hPos).mono (hB2 hq) (hC f c hf)).eq_bot, finrank_bot,
      add_zero] at h
    rw [h, hfinF, hfinB f c hf']
  -- lower bound for the fixed space
  have hPle : (quadFock (rank L)).map (mkEα L 0) ⊔ (chargeHalf L hPos).map fp ≤ plusTwo L := by
    refine sup_le ?_ ?_
    · rintro _ ⟨p, hp, rfl⟩
      refine (mem_plusTwo L).mpr ⟨?_, ?_⟩
      · rw [hG]; exact Submodule.mem_sup_left (hB2 (quadFock_le _) ⟨p, hp, rfl⟩)
      · rw [mkEα_apply, thetaLat_tmul, sigmaN_of_mem_quadFock _ hp, neg_zero]
    · rintro _ ⟨y, hy, rfl⟩
      refine (mem_plusTwo L).mpr ⟨?_, ?_⟩
      · rw [hG]
        exact Submodule.mem_sup_right (hC fp 1 (fun y => by rw [hfp_apply, one_smul]) ⟨y, hy, rfl⟩)
      · rw [hfp_apply, map_add, thetaLat_thetaLat, add_comm]
  have hMle : (linFock (rank L)).map (mkEα L 0) ⊔ (chargeHalf L hPos).map fm ≤ minusTwo L := by
    refine sup_le ?_ ?_
    · rintro _ ⟨p, hp, rfl⟩
      refine (mem_minusTwo L).mpr ⟨?_, ?_⟩
      · rw [hG]; exact Submodule.mem_sup_left (hB2 (linFock_le _) ⟨p, hp, rfl⟩)
      · rw [mkEα_apply, thetaLat_tmul, sigmaN_of_mem_linFock _ hp, neg_zero, TensorProduct.neg_tmul]
    · rintro _ ⟨y, hy, rfl⟩
      refine (mem_minusTwo L).mpr ⟨?_, ?_⟩
      · rw [hG]
        exact Submodule.mem_sup_right
          (hC fm (-1) (fun y => by rw [hfm_apply, neg_one_smul, sub_eq_add_neg]) ⟨y, hy, rfl⟩)
      · rw [hfm_apply, map_sub, thetaLat_thetaLat, neg_sub]
  have h1 := Submodule.finrank_mono hPle
  have h2 := Submodule.finrank_mono hMle
  rw [hdimSup fp 1 (quadFock_le _) (fun y => by rw [hfp_apply, one_smul]) hfp,
    finrank_quadFock] at h1
  rw [hdimSup fm (-1) (linFock_le _) (fun y => by rw [hfm_apply, neg_one_smul, sub_eq_add_neg]) hfm,
    finrank_linFock] at h2
  -- upper bound
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (plusTwo L) (minusTwo L)
  rw [(disjoint_plusTwo_minusTwo L).eq_bot, finrank_bot, add_zero] at h3
  have h4 : finrank ℂ ↥(plusTwo L ⊔ minusTwo L) ≤ finrank ℂ (gradingLatGen L 2) :=
    Submodule.finrank_mono (sup_le inf_le_left inf_le_left)
  rw [finrank_gradingLatGen_two L hEven hPos hR, card_normFour_eq L hPos] at h4
  omega

end Theta

end LatGen

namespace Moonshine

open LatGen IntegralLattice Module

theorem leech_normFour_card : (normFour leech leech_posDef).card = 196560 := by
  rw [normFour, ← Set.ncard_eq_toFinset_card _ (normFour_finite leech leech_posDef)]
  exact Leech.repCount_four

/-- **`dim (V_Λ)₂ = 196884`** `= 24 + 300 + 196560`: the states `h(-2)𝟙`, `h(-1)h(-1)𝟙` and `e^α`
for the `196560` minimal vectors of the Leech lattice. -/
theorem leechVOA_finrank_grading_two : finrank ℂ (leechVOA.grading 2) = 196884 := by
  change finrank ℂ (gradingLatGen leech 2) = 196884
  rw [finrank_gradingLatGen_two leech leech_even leech_posDef leech_no_roots, leech_rank,
    leech_normFour_card]
  rfl

theorem leech_halfFour_card : (halfFour leech leech_posDef).card = 98280 := by
  have h := card_normFour_eq leech leech_posDef
  rw [leech_normFour_card] at h
  omega

/-- The weight-`2` space of `V_Λ⁺` is the `θ`-fixed part of `(V_Λ)₂`. -/
noncomputable def leechVOAPlusGradingTwoEquiv : leechVOAPlus.grading 2 ≃ₗ[ℂ] plusTwo leech := by
  refine (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).trans
    (LinearEquiv.ofEq _ _ ?_)
  rw [show leechVOAPlus.grading 2 = (leechVOA.grading 2).comap
      (orbifold (Subgroup.zpowers leechTheta)).carrier.subtype from rfl,
    Submodule.map_comap_subtype]
  ext x
  rw [Submodule.mem_inf, mem_plusTwo, mem_leechVOAPlus_iff, and_comm]
  rfl

/-- **`dim (V_Λ⁺)₂ = 98580`** `= 300 + 196560/2`: the `θ`-fixed states are the `300` quadratic
states `h_a(-1)h_b(-1)𝟙` and one `e^α + e^{-α}` for each pair `±α` of minimal vectors; the `24`
states `h_a(-2)𝟙` are `θ`-odd. -/
theorem leechVOAPlus_finrank_grading_two : finrank ℂ (leechVOAPlus.grading 2) = 98580 := by
  rw [leechVOAPlusGradingTwoEquiv.finrank_eq,
    finrank_plusTwo leech leech_posDef leech_even leech_no_roots, leech_rank, leech_halfFour_card]
  rfl

end Moonshine

end VOA
