/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesSliceMapBasis

/-!
# The Whittaker coinvariant map `W₀ : V^k(sl₂) → ℂ[X₀, X₁, …]`

Let `E = ℂ[X₀, X₁, …]`, where `X_n` stands for the class of `e_{-n-1}`.  On the
`(f, h, e)`-ordered PBW basis `f^λ h^ν e^μ |0⟩` (`TwoSeriesSliceMapBasis.Fbasis`) define

`W₀ (f^λ h^ν e^μ |0⟩) = χ(f^λ) · [ν = 0] · X^μ`,

where `χ(f_{-1}) = -1` and `χ(f_{-j}) = 0` for `j ≥ 2`.  Equivalently `W₀` sends the sorted word
of a list of letters to the product `classicalW` of the letter values
`f_{-1} ↦ -1`, `f_{-j-2} ↦ 0`, `h ↦ 0`, `e_{-n-1} ↦ X_n`.

## Results

* `W0_J_f`, `W0_J_fOne`, `W0_J_fHigh`, `W0_J_h` — the **exact Whittaker relations**
  `W₀ ∘ f_{-1} = -W₀`, `W₀ ∘ f_{-j-2} = 0`, `W₀ ∘ h_{-j-1} = 0`;
* `whitIdeal` (the span of `(x - χ(x))V`), `W0_whitIdeal` (`W₀` kills it), the section
  `sE : E → V` (`X^ν ↦ e`-word), `W0_sE` (`W₀ ∘ sE = id`) and `sub_sE_W0_mem` (`y ≡ sE(W₀ y)`
  modulo the Whittaker ideal);
* `W0_rword_sub_classicalW` — **the filtration lemma**: for every creation word `l`,
  `W₀(l) - classicalW(l)` has total degree `≤ (K(l) - 1)/2`, where `K = 2#e + #h` is the
  Kazhdan weight.  Hence `W₀(l)` has total degree `≤ K(l)/2` (`W0_rword_mem`);
* `KC p q` — the span of creation words of Kazhdan weight `≤ p` and charge `#f - #e = q`;
* `chargeLift G` — the `ℤ`-graded lift of a linear map along the charge, with
  `chargeLift_rword`: a word of charge `q` goes to degree `q`.

Everything is proved; no new axiom.
-/

namespace VOA.TwoSeries.SliceMap

open VOA.AffineVOA MvPolynomial

noncomputable section

/-! ## §1  Letter values and the classical product -/

/-- The target polynomial space: `X_n` is the class of `e_{-n-1}`. -/
abbrev EPoly : Type := MvPolynomial ℕ ℂ

/-- The Whittaker character on `f`-depths: `χ(f_{-1}) = -1`, `χ(f_{-j-2}) = 0`. -/
def chiF (d : ℕ) : ℂ := if d = 0 then -1 else 0

/-- Value of a rank letter: `f ↦ χ`, `h ↦ 0`, `e_{-n-1} ↦ X_n`. -/
def letterVal (q : RLetter) : EPoly :=
  if (ofLex q).1 = 0 then MvPolynomial.C (chiF (dep q))
  else if (ofLex q).1 = 1 then 0 else X (dep q)

/-- The classical product of a word. -/
def classicalW (l : List RLetter) : EPoly := (l.map letterVal).prod

@[simp] theorem classicalW_nil : classicalW [] = 1 := rfl

theorem classicalW_cons (q : RLetter) (l : List RLetter) :
    classicalW (q :: l) = letterVal q * classicalW l := rfl

theorem classicalW_append (l l' : List RLetter) :
    classicalW (l ++ l') = classicalW l * classicalW l' := by
  simp [classicalW, List.prod_append]

theorem classicalW_perm {l l' : List RLetter} (h : l.Perm l') : classicalW l = classicalW l' :=
  (h.map _).prod_eq

theorem letterVal_f (d : ℕ) : letterVal (toLex (0, d)) = MvPolynomial.C (chiF d) := by
  simp [letterVal]

theorem letterVal_h (d : ℕ) : letterVal (toLex (1, d)) = 0 := by
  simp [letterVal]

theorem letterVal_e (d : ℕ) : letterVal (toLex (2, d)) = X d := by
  simp [letterVal]

theorem letterVal_of_rank_one {q : RLetter} (hq : (ofLex q).1 = 1) : letterVal q = 0 := by
  simp [letterVal, hq]

theorem letterVal_of_rank_two {q : RLetter} (hq : (ofLex q).1 = 2) : letterVal q = X (dep q) := by
  simp [letterVal, hq]

/-! ## §2  Order facts on rank letters -/

theorem fin3_one_le {x : Fin 3} (h : x ≠ 0) : 1 ≤ x := by
  fin_cases x <;> simp_all

theorem fin3_eq_two_of_ne {x : Fin 3} (h0 : x ≠ 0) (h1 : x ≠ 1) : x = 2 := by
  fin_cases x <;> simp_all

theorem fin3_eq_two_of_le {x : Fin 3} (h : 2 ≤ x) : x = 2 := by
  fin_cases x <;> simp_all

theorem rank_le_of_le {r q : RLetter} (h : r ≤ q) : (ofLex r).1 ≤ (ofLex q).1 := by
  have h' : toLex (ofLex r) ≤ toLex (ofLex q) := h
  rcases Prod.Lex.toLex_le_toLex.mp h' with h1 | ⟨h1, _⟩
  · exact h1.le
  · exact h1.le

theorem rank_eq_zero_of_lt_f {r : RLetter} {d : ℕ} (h : r < toLex (0, d)) :
    (ofLex r).1 = 0 := by
  have := rank_le_of_le h.le
  simp only [ofLex_toLex] at this
  exact Fin.le_zero_iff.mp this

theorem rank_le_one_of_lt_h {r : RLetter} {d : ℕ} (h : r < toLex (1, d)) :
    (ofLex r).1 ≤ 1 := by
  have := rank_le_of_le h.le
  simpa using this

/-! ## §3  The map `W₀` -/

variable (k : ℂ) (hk : k + 2 ≠ 0)

/-- **The Whittaker coinvariant map** `W₀`, defined on the `(f, h, e)`-ordered PBW basis. -/
def W0 : WakModule k →ₗ[ℂ] EPoly :=
  (Fbasis k hk).constr ℂ fun μ => classicalW (expWord μ)

theorem W0_Fvec (μ : RLetter →₀ ℕ) : W0 k hk (Fvec k μ) = classicalW (expWord μ) := by
  rw [← Fbasis_apply k hk, W0, Module.Basis.constr_basis]

theorem W0_rword_sorted (l : List RLetter) (hl : l.Pairwise (fun a b => a ≤ b)) :
    W0 k hk (rword k l) = classicalW l := by
  rw [rword_sorted k l hl, W0_Fvec, ← eq_expWord_toFinsupp l hl]

theorem W0_vacuum : W0 k hk (vacuumA k) = 1 := by
  rw [← rword_nil k, W0_rword_sorted k hk [] List.Pairwise.nil, classicalW_nil]

/-- **Insertion of a commuting letter.** -/
theorem rword_cons_eq_orderedInsert (q : RLetter) :
    ∀ l : List RLetter, l.Pairwise (fun a b => a ≤ b) →
      (∀ r ∈ l, r < q → ∀ c : Fin 3, fabc (col q) (col r) c = 0) →
      rword k (q :: l) = rword k (l.orderedInsert (fun a b => a ≤ b) q)
  | [], _, _ => rfl
  | r :: l', hl, hc => by
      by_cases hqr : q ≤ r
      · rw [List.orderedInsert_cons_of_le _ _ hqr]
      · have hrq : r < q := lt_of_not_ge hqr
        rw [List.orderedInsert_of_not_le _ _ hqr]
        have hsw := rword_swap k [] l' q r
        simp only [List.nil_append] at hsw
        rw [hsw, Finset.sum_eq_zero (fun c _ => by rw [hc r (by simp) hrq c, zero_smul]),
          add_zero, rword_cons, rword_cons_eq_orderedInsert q l' (List.Pairwise.of_cons hl)
            (fun r' hr' h => hc r' (List.mem_cons_of_mem _ hr') h), ← rword_cons]

theorem classicalW_orderedInsert (q : RLetter) (l : List RLetter) :
    classicalW (l.orderedInsert (fun a b => a ≤ b) q) = letterVal q * classicalW l := by
  rw [classicalW_perm (List.perm_orderedInsert _ q l), classicalW_cons]

/-- An `f`-mode on a PBW vector is again a PBW vector. -/
theorem J_f_Fvec (d : ℕ) (μ : RLetter →₀ ℕ) :
    J k 1 (-(d : ℤ) - 1) (Fvec k μ) = Fvec k (μ + Finsupp.single (toLex (0, d)) 1) := by
  rw [Fvec, Fvec, expWord_add_single, ← rword_cons_eq_orderedInsert k _ _ (expWord_pairwise μ)]
  · rfl
  · intro r _ hr c
    have h0 := rank_eq_zero_of_lt_f hr
    have hcol : col r = 1 := by simp [col, h0, rankColor]
    rw [hcol]
    simp only [col_toLex, rankColor]
    fin_cases c <;> simp [fabc]

/-- **Whittaker relation for `f`.** -/
theorem W0_J_f (d : ℕ) (y : WakModule k) :
    W0 k hk (J k 1 (-(d : ℤ) - 1) y) = chiF d • W0 k hk y := by
  have h : (W0 k hk).comp (J k 1 (-(d : ℤ) - 1)) = chiF d • W0 k hk := by
    refine (Fbasis k hk).ext fun μ => ?_
    rw [LinearMap.comp_apply, Fbasis_apply, J_f_Fvec, W0_Fvec, LinearMap.smul_apply, W0_Fvec,
      expWord_add_single, classicalW_orderedInsert, letterVal_f, smul_eq_C_mul]
  exact LinearMap.congr_fun h y

theorem W0_J_fOne (y : WakModule k) : W0 k hk (J k 1 (-1) y) = -W0 k hk y := by
  have h := W0_J_f k hk 0 y
  simp only [Nat.cast_zero, neg_zero, zero_sub, chiF, if_true] at h
  rw [h, neg_one_smul]

theorem W0_J_fHigh (d : ℕ) (y : WakModule k) : W0 k hk (J k 1 (-(d : ℤ) - 2) y) = 0 := by
  have h := W0_J_f k hk (d + 1) y
  rw [show (-((d + 1 : ℕ) : ℤ) - 1) = -(d : ℤ) - 2 by push_cast; ring] at h
  rw [h, chiF, if_neg (by omega), zero_smul]

/-- The `h`-mode commuted past an `f`-mode. -/
theorem J_h_J_f (d e : ℕ) (z : WakModule k) :
    J k 2 (-(d : ℤ) - 1) (J k 1 (-(e : ℤ) - 1) z) =
      J k 1 (-(e : ℤ) - 1) (J k 2 (-(d : ℤ) - 1) z) +
        (-2 : ℂ) • J k 1 (-((d + e + 1 : ℕ) : ℤ) - 1) z := by
  have h := congrArg (fun T : Module.End ℂ (WakModule k) => T z)
    (current_comm k 2 1 (-(d : ℤ) - 1) (-(e : ℤ) - 1))
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply] at h
  rw [if_neg (by omega), LinearMap.zero_apply, add_zero, Fin.sum_univ_three] at h
  simp only [fabc, zero_smul, zero_add, add_zero] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h, add_comm]
  congr 2
  push_cast; ring_nf

/-- **Whittaker relation for `h`** on sorted words. -/
theorem W0_J_h_sorted (d : ℕ) :
    ∀ l : List RLetter, l.Pairwise (fun a b => a ≤ b) →
      W0 k hk (J k 2 (-(d : ℤ) - 1) (rword k l)) = 0
  | [], _ => by
      have : J k 2 (-(d : ℤ) - 1) (rword k []) = rword k [toLex (1, d)] := rfl
      rw [this, W0_rword_sorted k hk _ (List.pairwise_singleton _ _), classicalW_cons,
        letterVal_h, zero_mul]
  | r :: l', hl => by
      by_cases hr : (ofLex r).1 = 0
      · have hcol : col r = 1 := by simp [col, hr, rankColor]
        rw [rword_cons, hcol, J_h_J_f, map_add, map_smul, W0_J_f, W0_J_f,
          W0_J_h_sorted d l' (List.Pairwise.of_cons hl), smul_zero, zero_add, chiF,
          if_neg (by omega), zero_smul, smul_zero]
      · have hall : ∀ r' ∈ r :: l', 1 ≤ (ofLex r').1 := by
          intro r' hr'
          rcases List.mem_cons.mp hr' with rfl | hr'
          · exact fin3_one_le hr
          · exact le_trans (fin3_one_le hr)
              (rank_le_of_le ((List.pairwise_cons.mp hl).1 r' hr'))
        have hins : J k 2 (-(d : ℤ) - 1) (rword k (r :: l')) =
            rword k ((r :: l').orderedInsert (fun a b => a ≤ b) (toLex (1, d))) := by
          rw [← rword_cons_eq_orderedInsert k _ _ hl]
          · rfl
          · intro r' hr' hlt c
            have h1 := rank_le_one_of_lt_h hlt
            have h2 := hall r' hr'
            have heq : (ofLex r').1 = 1 := le_antisymm h1 h2
            have hcol : col r' = 2 := by simp [col, heq, rankColor]
            rw [hcol]
            simp only [col_toLex, rankColor]
            fin_cases c <;> simp [fabc]
        rw [hins, W0_rword_sorted k hk _ (List.Pairwise.orderedInsert _ _ hl),
          classicalW_orderedInsert, letterVal_h, zero_mul]

theorem W0_J_h (d : ℕ) (y : WakModule k) : W0 k hk (J k 2 (-(d : ℤ) - 1) y) = 0 := by
  have h : (W0 k hk).comp (J k 2 (-(d : ℤ) - 1)) = 0 := by
    refine (Fbasis k hk).ext fun μ => ?_
    rw [LinearMap.comp_apply, Fbasis_apply, LinearMap.zero_apply, Fvec]
    exact W0_J_h_sorted k hk d _ (expWord_pairwise μ)
  exact LinearMap.congr_fun h y

/-! ## §4  `e`-words and the section `sE` -/

/-- The `e`-letter of depth `n`. -/
def eL (n : ℕ) : RLetter := toLex (2, n)

theorem eL_of_rank_two {q : RLetter} (hq : (ofLex q).1 = 2) : eL (dep q) = q := by
  change toLex (2, (ofLex q).2) = q
  rw [← hq]
  rfl

/-- `e`-words are insensitive to the order of their letters. -/
theorem rword_perm_of_rank_two {l l' : List RLetter} (h : l.Perm l')
    (hl : ∀ q ∈ l, (ofLex q).1 = 2) : rword k l = rword k l' := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
      rw [rword_cons, rword_cons, ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))]
  | swap x y l =>
      have hx := hl x (by simp)
      have hy := hl y (by simp)
      have hsw := rword_swap k [] l y x
      simp only [List.nil_append] at hsw
      rw [hsw, Finset.sum_eq_zero, add_zero]
      intro c _
      have hcx : col x = 0 := by simp [col, hx, rankColor]
      have hcy : col y = 0 := by simp [col, hy, rankColor]
      rw [hcx, hcy]
      fin_cases c <;> simp [fabc]
  | trans h₁ _ ih₁ ih₂ =>
      rw [ih₁ hl, ih₂ (fun q hq => hl q (h₁.symm.subset hq))]

/-- The `e`-word of an exponent `ν`: `∏ e_{-n-1}^{ν n} |0⟩`. -/
def eword (ν : ℕ →₀ ℕ) : WakModule k :=
  rword k ((Finsupp.toMultiset ν).toList.map eL)

theorem prod_X_toMultiset (ν : ℕ →₀ ℕ) :
    ((Finsupp.toMultiset ν).map (X : ℕ → EPoly)).prod = monomial ν 1 := by
  induction ν using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
      rw [map_add, Multiset.map_add, Multiset.prod_add, ih, Finsupp.toMultiset_single,
        Multiset.map_nsmul, Multiset.map_singleton, Multiset.prod_nsmul,
        Multiset.prod_singleton, X_pow_eq_monomial, monomial_mul, one_mul]

theorem classicalW_eList (ν : ℕ →₀ ℕ) :
    classicalW ((Finsupp.toMultiset ν).toList.map eL) = monomial ν 1 := by
  rw [classicalW, List.map_map, ← prod_X_toMultiset]
  have : (letterVal ∘ eL) = (X : ℕ → EPoly) := by
    funext n; exact letterVal_e n
  rw [this, ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]

theorem W0_rword_of_rank_two (l : List RLetter) (hl : ∀ q ∈ l, (ofLex q).1 = 2) :
    W0 k hk (rword k l) = classicalW l := by
  have hp := List.mergeSort_perm l (fun a b => decide (a ≤ b))
  rw [rword_perm_of_rank_two k hp.symm hl, W0_rword_sorted k hk _
    (by simpa using List.pairwise_mergeSort' (fun a b => a ≤ b) l), classicalW_perm hp]

theorem W0_eword (ν : ℕ →₀ ℕ) : W0 k hk (eword k ν) = monomial ν 1 := by
  rw [eword, W0_rword_of_rank_two, classicalW_eList]
  intro q hq
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp hq
  rfl

/-- **The section** `sE : E → V`, `X^ν ↦ e`-word. -/
def sE : EPoly →ₗ[ℂ] WakModule k :=
  (basisMonomials ℕ ℂ).constr ℂ (eword k)

theorem sE_monomial (ν : ℕ →₀ ℕ) : sE k (monomial ν 1) = eword k ν := by
  have h := (basisMonomials ℕ ℂ).constr_basis ℂ (eword k) ν
  simp only [coe_basisMonomials] at h
  exact h

theorem W0_sE (P : EPoly) : W0 k hk (sE k P) = P := by
  have h : (W0 k hk).comp (sE k) = LinearMap.id := by
    refine (basisMonomials ℕ ℂ).ext fun ν => ?_
    rw [LinearMap.comp_apply, coe_basisMonomials, sE_monomial, W0_eword, LinearMap.id_apply]
  exact LinearMap.congr_fun h P

theorem sE_one : sE k 1 = vacuumA k := by
  rw [show (1 : EPoly) = monomial 0 1 from rfl, sE_monomial, eword]
  simp

/-- An `e`-word with a list of rank-two letters is the `e`-word of its depth multiset. -/
theorem rword_eq_eword (l : List RLetter) (hl : ∀ q ∈ l, (ofLex q).1 = 2) :
    rword k l = eword k (Multiset.toFinsupp ((l.map dep : List ℕ) : Multiset ℕ)) := by
  rw [eword, Multiset.toFinsupp_toMultiset]
  apply rword_perm_of_rank_two k _ hl
  rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, Multiset.map_coe,
    List.map_map]
  congr 1
  conv_lhs => rw [← List.map_id l]
  apply List.map_congr_left
  intro q hq
  exact (eL_of_rank_two (hl q hq)).symm

/-! ## §5  The Whittaker ideal -/

/-- The generators `(x - χ(x)) v` of the Whittaker ideal. -/
def whitGens : Set (WakModule k) :=
  {y | ∃ v, y = J k 1 (-1) v + v} ∪ {y | ∃ (d : ℕ) (v : WakModule k), y = J k 1 (-(d : ℤ) - 2) v} ∪
    {y | ∃ (d : ℕ) (v : WakModule k), y = J k 2 (-(d : ℤ) - 1) v}

/-- **The Whittaker ideal** `Σ (x - χ(x)) V`. -/
def whitIdeal : Submodule ℂ (WakModule k) := Submodule.span ℂ (whitGens k)

theorem fOne_mem (v : WakModule k) : J k 1 (-1) v + v ∈ whitIdeal k :=
  Submodule.subset_span (Or.inl (Or.inl ⟨v, rfl⟩))

theorem fHigh_mem (d : ℕ) (v : WakModule k) : J k 1 (-(d : ℤ) - 2) v ∈ whitIdeal k :=
  Submodule.subset_span (Or.inl (Or.inr ⟨d, v, rfl⟩))

theorem h_mem (d : ℕ) (v : WakModule k) : J k 2 (-(d : ℤ) - 1) v ∈ whitIdeal k :=
  Submodule.subset_span (Or.inr ⟨d, v, rfl⟩)

theorem W0_whitIdeal {y : WakModule k} (hy : y ∈ whitIdeal k) : W0 k hk y = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
      rcases hx with (⟨v, rfl⟩ | ⟨d, v, rfl⟩) | ⟨d, v, rfl⟩
      · rw [map_add, W0_J_fOne, neg_add_cancel]
      · exact W0_J_fHigh k hk d v
      · exact W0_J_h k hk d v
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]

/-- The `f`-letter congruence `f_{-d-1} z ≡ χ(d) z`. -/
theorem J_f_sub_mem (d : ℕ) (z : WakModule k) :
    J k 1 (-(d : ℤ) - 1) z - chiF d • z ∈ whitIdeal k := by
  rcases d with _ | d
  · simp only [Nat.cast_zero, neg_zero, zero_sub, chiF, if_true, neg_one_smul, sub_neg_eq_add]
    exact fOne_mem k z
  · rw [chiF, if_neg (by omega), zero_smul, sub_zero,
      show (-((d + 1 : ℕ) : ℤ) - 1) = -(d : ℤ) - 2 by push_cast; ring]
    exact fHigh_mem k d z

/-- **Every vector is congruent to the section of its `W₀`-image** modulo the Whittaker
ideal. -/
theorem sub_sE_W0_mem (y : WakModule k) : y - sE k (W0 k hk y) ∈ whitIdeal k := by
  have hsorted : ∀ l : List RLetter, l.Pairwise (fun a b => a ≤ b) →
      rword k l - sE k (W0 k hk (rword k l)) ∈ whitIdeal k := by
    intro l
    induction l with
    | nil =>
        intro _
        rw [rword_nil, W0_vacuum, sE_one, sub_self]
        exact Submodule.zero_mem _
    | cons r l' ih =>
        intro hl
        have ih' := ih (List.Pairwise.of_cons hl)
        by_cases h0 : (ofLex r).1 = 0
        · have hcol : col r = 1 := by simp [col, h0, rankColor]
          have hW : W0 k hk (rword k (r :: l')) = chiF (dep r) • W0 k hk (rword k l') := by
            rw [rword_cons, hcol, W0_J_f]
          rw [hW, map_smul, rword_cons, hcol]
          have hsplit : J k 1 (-(dep r : ℤ) - 1) (rword k l') -
              chiF (dep r) • sE k (W0 k hk (rword k l')) =
              (J k 1 (-(dep r : ℤ) - 1) (rword k l') - chiF (dep r) • rword k l') +
                chiF (dep r) • (rword k l' - sE k (W0 k hk (rword k l'))) := by
            rw [smul_sub]; abel
          rw [hsplit]
          exact Submodule.add_mem _ (J_f_sub_mem k _ _) (Submodule.smul_mem _ _ ih')
        · by_cases h1 : (ofLex r).1 = 1
          · have hcol : col r = 2 := by simp [col, h1, rankColor]
            rw [rword_cons, hcol, W0_J_h, map_zero, sub_zero]
            exact h_mem k _ _
          · have h2 : (ofLex r).1 = 2 := fin3_eq_two_of_ne h0 h1
            have hall : ∀ q ∈ r :: l', (ofLex q).1 = 2 := by
              intro q hq
              rcases List.mem_cons.mp hq with rfl | hq
              · exact h2
              · apply fin3_eq_two_of_le
                rw [← h2]
                exact rank_le_of_le ((List.pairwise_cons.mp hl).1 q hq)
            rw [rword_eq_eword k _ hall, W0_eword, sE_monomial, sub_self]
            exact Submodule.zero_mem _
  have hle : Submodule.span ℂ (Set.range (Fvec k)) ≤
      (whitIdeal k).comap (LinearMap.id - (sE k).comp (W0 k hk)) := by
    rw [Submodule.span_le]
    rintro _ ⟨μ, rfl⟩
    simpa [Fvec] using hsorted _ (expWord_pairwise μ)
  have h := hle (by rw [Fvec_span_eq_top]; trivial : y ∈ Submodule.span ℂ (Set.range (Fvec k)))
  simpa using h


/-! ## §6  The Kazhdan filtration lemma -/

/-- Rank value of a letter (`f = 0`, `h = 1`, `e = 2`): its Kazhdan weight. -/
def rk (q : RLetter) : ℕ := ((ofLex q).1 : ℕ)

/-- Kazhdan weight `2#e + #h` of a word. -/
def Kl (l : List RLetter) : ℕ := (l.map rk).sum

/-- Charge `#f - #e` of a word. -/
def chl (l : List RLetter) : ℤ := (l.map fun q => 1 - (rk q : ℤ)).sum

/-- Polynomials of total degree `≤ d`. -/
abbrev Dg (d : ℕ) : Submodule ℂ EPoly := restrictTotalDegree ℕ ℂ d

theorem mem_Dg {d : ℕ} {P : EPoly} : P ∈ Dg d ↔ P.totalDegree ≤ d := by
  rw [Dg, mem_restrictTotalDegree]

theorem Dg_mono {a b : ℕ} (h : a ≤ b) : Dg a ≤ Dg b := fun _ hP =>
  mem_Dg.mpr ((mem_Dg.mp hP).trans h)

theorem Dg_mul {a b : ℕ} {P Q : EPoly} (hP : P ∈ Dg a) (hQ : Q ∈ Dg b) : P * Q ∈ Dg (a + b) :=
  mem_Dg.mpr ((totalDegree_mul P Q).trans (add_le_add (mem_Dg.mp hP) (mem_Dg.mp hQ)))

@[simp] theorem Kl_nil : Kl [] = 0 := rfl
@[simp] theorem Kl_cons (q : RLetter) (l : List RLetter) : Kl (q :: l) = rk q + Kl l := by
  simp [Kl]
theorem Kl_append (l l' : List RLetter) : Kl (l ++ l') = Kl l + Kl l' := by
  simp [Kl, List.sum_append]
@[simp] theorem chl_nil : chl [] = 0 := rfl
@[simp] theorem chl_cons (q : RLetter) (l : List RLetter) :
    chl (q :: l) = (1 - (rk q : ℤ)) + chl l := by
  simp [chl]
theorem chl_append (l l' : List RLetter) : chl (l ++ l') = chl l + chl l' := by
  simp [chl, List.sum_append]

@[simp] theorem rk_toLex (r : Fin 3) (d : ℕ) : rk (toLex (r, d)) = (r : ℕ) := rfl

/-- A nonzero structure constant lowers the Kazhdan weight by exactly one. -/
theorem fabc_rank (a b : RLetter) (c : Fin 3) (h : fabc (col a) (col b) c ≠ 0) :
    ((colorRank c : Fin 3) : ℕ) + 1 = rk a + rk b := by
  unfold col rk at *
  generalize (ofLex a).1 = x at *
  generalize (ofLex b).1 = y at *
  fin_cases x <;> fin_cases y <;> fin_cases c <;> simp_all [fabc, rankColor, colorRank]

theorem Kl_swap (pre post : List RLetter) (a b : RLetter) :
    Kl (pre ++ b :: a :: post) = Kl (pre ++ a :: b :: post) := by
  simp only [Kl_append, Kl_cons]; omega

theorem chl_swap (pre post : List RLetter) (a b : RLetter) :
    chl (pre ++ b :: a :: post) = chl (pre ++ a :: b :: post) := by
  simp only [chl_append, chl_cons]; ring

theorem Kl_bracket (pre post : List RLetter) (a b : RLetter) (c : Fin 3)
    (h : fabc (col a) (col b) c ≠ 0) :
    Kl (pre ++ toLex (colorRank c, dep a + dep b + 1) :: post) + 1 =
      Kl (pre ++ a :: b :: post) := by
  have := fabc_rank a b c h
  simp only [Kl_append, Kl_cons, rk_toLex]; omega

theorem chl_bracket (pre post : List RLetter) (a b : RLetter) (c : Fin 3)
    (h : fabc (col a) (col b) c ≠ 0) :
    chl (pre ++ toLex (colorRank c, dep a + dep b + 1) :: post) =
      chl (pre ++ a :: b :: post) := by
  have := fabc_rank a b c h
  simp only [chl_append, chl_cons, rk_toLex]
  have h' : ((colorRank c : Fin 3) : ℤ) + 1 = (rk a : ℤ) + rk b := by exact_mod_cast this
  linarith

theorem classicalW_swap (pre post : List RLetter) (a b : RLetter) :
    classicalW (pre ++ b :: a :: post) = classicalW (pre ++ a :: b :: post) :=
  classicalW_perm (List.Perm.append_left pre (List.Perm.swap a b post))

theorem letterVal_mem (q : RLetter) : letterVal q ∈ Dg (rk q / 2) := by
  rw [mem_Dg]
  unfold letterVal rk
  generalize hx : (ofLex q).1 = x
  fin_cases x
  · simp [totalDegree_C]
  · simp
  · simp [totalDegree_X]

/-- The classical product has total degree `≤ K/2`. -/
theorem classicalW_mem (l : List RLetter) : classicalW l ∈ Dg (Kl l / 2) := by
  induction l with
  | nil => simp [mem_Dg]
  | cons q l ih =>
      rw [classicalW_cons, Kl_cons]
      exact Dg_mono (by omega) (Dg_mul (letterVal_mem q) ih)

/-- **The filtration lemma**: `W₀(l) - classicalW(l)` has total degree `≤ (K(l) - 1)/2`. -/
theorem W0_rword_sub (l : List RLetter) :
    W0 k hk (rword k l) - classicalW l ∈ Dg ((Kl l - 1) / 2) := by
  refine straighten (P := fun l => W0 k hk (rword k l) - classicalW l ∈ Dg ((Kl l - 1) / 2))
    (fun l hl => ?_) (fun pre a b post _ hswap hbr => ?_) l
  · dsimp only
    rw [W0_rword_sorted k hk l hl, sub_self]
    exact Submodule.zero_mem _
  · dsimp only at hswap hbr ⊢
    have hKs := Kl_swap pre post a b
    rw [rword_swap, map_add, map_sum, ← classicalW_swap pre post a b, ← hKs,
      add_sub_right_comm]
    refine Submodule.add_mem _ hswap (Submodule.sum_mem _ fun c _ => ?_)
    by_cases hc : fabc (col a) (col b) c = 0
    · rw [hc, zero_smul, map_zero]; exact Submodule.zero_mem _
    · rw [map_smul]
      refine Submodule.smul_mem _ _ ?_
      have hK := Kl_bracket pre post a b c hc
      have h1 := hbr c hc
      have h2 := classicalW_mem (pre ++ toLex (colorRank c, dep a + dep b + 1) :: post)
      rw [← sub_add_cancel (W0 k hk _) (classicalW _)]
      refine Submodule.add_mem _ (Dg_mono ?_ h1) (Dg_mono ?_ h2) <;> omega

/-- `W₀` of a word of Kazhdan weight `K` has total degree `≤ K/2`. -/
theorem W0_rword_mem (l : List RLetter) : W0 k hk (rword k l) ∈ Dg (Kl l / 2) := by
  rw [← sub_add_cancel (W0 k hk _) (classicalW l)]
  exact Submodule.add_mem _ (Dg_mono (by omega) (W0_rword_sub k hk l)) (classicalW_mem l)

/-! ## §7  Kazhdan–charge spans and the charge lift -/

/-- The span of creation words of Kazhdan weight `≤ p` and charge `q`. -/
def KC (p : ℕ) (q : ℤ) : Submodule ℂ (WakModule k) :=
  Submodule.span ℂ {y | ∃ l : List RLetter, Kl l ≤ p ∧ chl l = q ∧ rword k l = y}

theorem rword_mem_KC {l : List RLetter} {p : ℕ} {q : ℤ} (hp : Kl l ≤ p) (hq : chl l = q) :
    rword k l ∈ KC k p q :=
  Submodule.subset_span ⟨l, hp, hq, rfl⟩

theorem KC_mono {p p' : ℕ} (h : p ≤ p') (q : ℤ) : KC k p q ≤ KC k p' q :=
  Submodule.span_mono fun _ ⟨l, hl, hq, he⟩ => ⟨l, hl.trans h, hq, he⟩

theorem W0_KC {p : ℕ} {q : ℤ} {y : WakModule k} (hy : y ∈ KC k p q) : W0 k hk y ∈ Dg (p / 2) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, hl, _, rfl⟩ := hx
      exact Dg_mono (Nat.div_le_div_right hl) (W0_rword_mem k hk l)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- A creation letter maps a Kazhdan–charge span to the shifted one. -/
theorem J_letter_KC (r : RLetter) {p : ℕ} {q : ℤ} {y : WakModule k} (hy : y ∈ KC k p q) :
    J k (col r) (-(dep r : ℤ) - 1) y ∈ KC k (p + rk r) (q + (1 - (rk r : ℤ))) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, hl, hq, rfl⟩ := hx
      rw [← rword_cons]
      refine rword_mem_KC k (by rw [Kl_cons]; omega) (by rw [chl_cons, hq]; ring)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- **The charge lift** of a linear map: the image of a PBW vector sits in its charge. -/
def chargeLift (G : WakModule k →ₗ[ℂ] M) : WakModule k →ₗ[ℂ] (ℤ →₀ M) :=
  (Fbasis k hk).constr ℂ fun μ => Finsupp.single (chl (expWord μ)) (G (Fvec k μ))

theorem chargeLift_rword (G : WakModule k →ₗ[ℂ] M) (l : List RLetter) :
    chargeLift k hk G (rword k l) = Finsupp.single (chl l) (G (rword k l)) := by
  refine straighten (P := fun l => chargeLift k hk G (rword k l) =
      Finsupp.single (chl l) (G (rword k l))) (fun l hl => ?_)
    (fun pre a b post _ hswap hbr => ?_) l
  · dsimp only
    rw [rword_sorted k l hl, chargeLift, ← Fbasis_apply k hk, Module.Basis.constr_basis,
      Fbasis_apply, ← eq_expWord_toFinsupp l hl]
  · dsimp only at hswap hbr ⊢
    rw [rword_swap, map_add, map_add, map_sum, map_sum, hswap, chl_swap, Finsupp.single_add]
    congr 1
    rw [Finsupp.single_finsetSum]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : fabc (col a) (col b) c = 0
    · simp [hc]
    · rw [map_smul, map_smul, hbr c hc, chl_bracket pre post a b c hc, Finsupp.smul_single]

theorem chargeLift_KC (G : WakModule k →ₗ[ℂ] M) {p : ℕ} {q : ℤ} {y : WakModule k}
    (hy : y ∈ KC k p q) : chargeLift k hk G y = Finsupp.single q (G y) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, _, hq, rfl⟩ := hx
      rw [chargeLift_rword, hq]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, Finsupp.single_add]
  | smul r x _ hx => rw [map_smul, map_smul, hx, Finsupp.smul_single]

/-- Every vector is a sum of words; words lie in their own Kazhdan–charge span. -/
theorem rword_mem_KC_self (l : List RLetter) : rword k l ∈ KC k (Kl l) (chl l) :=
  rword_mem_KC k le_rfl rfl

end

end VOA.TwoSeries.SliceMap
