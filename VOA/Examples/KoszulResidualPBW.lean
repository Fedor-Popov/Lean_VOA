/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.AffineSl2BelowCriticalPBWFlag

/-!
# Leading terms of the PBW straightening, and PBW coordinates of `V^k(sl₂)`

The universal affine vertex algebra `V^k(sl₂)` (`k ≠ -2`) has the ordered PBW basis
`currentPBWBasis`, indexed by multiplicity functions `μ : LexLetter →₀ ℕ`. Reading the
coordinates as a polynomial gives the linear equivalence

  `pbwCoord : V^k(sl₂) ≃ₗ[ℂ] ℂ[x_q : q ∈ LexLetter]`,  `e_μ ↦ x^μ`.

The letter `q = (a, j)` stands for the creation mode `J^a_{-j-1}`.

## Results

* `lexState_sub_basis_mem` — **leading term of the straightening**: an arbitrary creation word
  of length `L` equals the ordered basis vector of the same multiset of letters, modulo the span
  of PBW monomials of length `< L`.
* `J_basis_sub_mem` — consequently `J^a_{-j-1} e_μ ≡ e_{μ + (a,j)}` modulo length `≤ |μ|`.
* `mem_ordinaryPiece_iff_coord` — a vector lies in the `p`-th ordinary piece iff its PBW
  coordinate polynomial has no monomial of degree `> p`.
* `homogeneousComponent_J` — **the leading part of a creation mode is multiplication by the
  variable**: for `x` in the `t`-th ordinary piece, the degree-`(t+1)` part of the coordinates of
  `J^a_{-j-1} x` is `x_{(a,j)}` times the degree-`t` part of the coordinates of `x`.

Everything is proved outright.
-/

namespace VOA.KoszulResidual

open AffineVOA AffineVOA.Inst AffineSl2GeneralRigidity AffineSl2BelowCritical
open AffineSl2PBWWakimotoReduction MvPolynomial

noncomputable section

variable (k : ℂ) (hk : k + 2 ≠ 0)

/-! ### Multiplicity functions of words -/

/-- The multiplicity function of a word of letters. -/
abbrev expOf (l : List LexLetter) : CurrentIndex := Multiset.toFinsupp (l : Multiset LexLetter)

theorem expOf_cons (q : LexLetter) (l : List LexLetter) :
    expOf (q :: l) = Finsupp.single q 1 + expOf l := by
  classical
  simp only [expOf, ← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add,
    Multiset.toFinsupp_singleton]

theorem expOf_lexExponentWord (mu : CurrentIndex) : expOf (lexExponentWord mu) = mu := by
  classical
  simp only [expOf, lexExponentWord_toMultiset, Finsupp.toMultiset_toFinsupp]

theorem degree_expOf (l : List LexLetter) : (expOf l).degree = l.length := by
  classical
  induction l with
  | nil => simp [expOf]
  | cons q l ih =>
      rw [expOf_cons, map_add, ih, List.length_cons, add_comm]
      simp

theorem pbwLength_eq_degree (mu : CurrentIndex) : pbwLength mu = mu.degree := by
  rw [pbwLength, orderedPBWColorWord_eq, List.length_map, ← degree_expOf,
    expOf_lexExponentWord]

theorem basis_eq_lexState (mu : CurrentIndex) :
    currentPBWBasis k hk mu = lexState k (lexExponentWord mu) := by
  rw [currentPBWBasis_apply, orderedPBWColorWord_eq]
  rfl

theorem basis_expOf_of_sorted (l : List LexLetter) (hl : l.Pairwise (fun a b => a ≤ b)) :
    currentPBWBasis k hk (expOf l) = lexState k l := by
  rw [basis_eq_lexState]
  conv_rhs => rw [eq_lexExponentWord_toFinsupp l hl]

/-! ### The leading term of the straightening -/

/-- **Leading term of the PBW straightening.** A creation word equals the ordered PBW basis
vector of its multiset of letters, modulo PBW monomials of strictly smaller length. -/
theorem lexState_sub_basis_mem (l : List LexLetter) :
    lexState k l - currentPBWBasis k hk (expOf l) ∈ pbwSpan k hk (l.length - 1) := by
  by_cases hsort : l.Pairwise (fun a b => a ≤ b)
  · rw [basis_expOf_of_sorted k hk l hsort, sub_self]
    exact Submodule.zero_mem _
  · obtain ⟨pre, a, b, post, hba, heq⟩ :=
      exists_adjacent_inversion_of_not_pairwise l hsort
    subst l
    have ih := lexState_sub_basis_mem (pre ++ b :: a :: post)
    have hperm : expOf (pre ++ b :: a :: post) = expOf (pre ++ a :: b :: post) := by
      simp only [expOf]
      congr 1
      exact Multiset.coe_eq_coe.mpr (List.Perm.append_left pre (List.Perm.swap a b post))
    have hlen : (pre ++ b :: a :: post).length = (pre ++ a :: b :: post).length := by simp
    rw [hperm, hlen] at ih
    have hbracket : ∀ c : Fin 3,
        lexState k (pre ++ toLex (c, (ofLex a).2 + (ofLex b).2 + 1) :: post) ∈
          pbwSpan k hk ((pre ++ a :: b :: post).length - 1) := by
      intro c
      refine pbwSpan_mono k hk (le_of_eq ?_) (lexState_mem_pbwSpan k hk _)
      simp
    rw [lexState_adjacent_swap k, add_sub_right_comm]
    exact Submodule.add_mem _ ih (Submodule.sum_mem _ fun c _ =>
      Submodule.smul_mem _ _ (hbracket c))
termination_by (l.length, inversionCount l)
decreasing_by
  rw [heq]
  rw [show (pre ++ b :: a :: post).length = (pre ++ a :: b :: post).length by simp]
  apply Prod.Lex.right
  exact inversionCount_swap pre post a b hba

/-- **The leading term of a creation mode on a basis vector.** -/
theorem J_basis_sub_mem (q : LexLetter) (mu : CurrentIndex) :
    J k (ofLex q).1 (-((ofLex q).2 : ℤ) - 1) (currentPBWBasis k hk mu) -
        currentPBWBasis k hk (Finsupp.single q 1 + mu) ∈ pbwSpan k hk mu.degree := by
  have h := lexState_sub_basis_mem k hk (q :: lexExponentWord mu)
  rw [lexState_cons, expOf_cons, expOf_lexExponentWord, List.length_cons,
    Nat.add_sub_cancel, ← basis_eq_lexState] at h
  have hl : (lexExponentWord mu).length = mu.degree := by
    rw [← degree_expOf, expOf_lexExponentWord]
  rwa [hl] at h

/-! ### PBW coordinates -/

/-- **PBW coordinates**: `V^k(sl₂) ≃ ℂ[x_q]`, `e_μ ↦ x^μ`. -/
def pbwCoord : WakModule k ≃ₗ[ℂ] MvPolynomial LexLetter ℂ :=
  (currentPBWBasis k hk).repr.trans (basisMonomials LexLetter ℂ).repr.symm

theorem pbwCoord_basis (mu : CurrentIndex) :
    pbwCoord k hk (currentPBWBasis k hk mu) = monomial mu 1 := by
  simp [pbwCoord, coe_basisMonomials]

theorem coeff_pbwCoord (mu : CurrentIndex) (x : WakModule k) :
    coeff mu (pbwCoord k hk x) = (currentPBWBasis k hk).repr x mu := by
  simp only [pbwCoord, LinearEquiv.trans_apply]
  rfl

theorem pbwCoord_symm_monomial (mu : CurrentIndex) :
    (pbwCoord k hk).symm (monomial mu 1) = currentPBWBasis k hk mu := by
  rw [LinearEquiv.symm_apply_eq, pbwCoord_basis]

/-- Membership in the `p`-th ordinary piece is a degree bound on the PBW coordinates. -/
theorem mem_ordinaryPiece_iff_coord (p : ℕ) (x : WakModule k) :
    x ∈ ordinaryPiece k p ↔ ∀ mu, p < mu.degree → coeff mu (pbwCoord k hk x) = 0 := by
  rw [mem_ordinaryPiece_iff_repr k hk]
  simp only [coeff_pbwCoord, pbwLength_eq_degree]

theorem mem_ordinaryPiece_iff_homog (p : ℕ) (x : WakModule k) :
    x ∈ ordinaryPiece k p ↔
      ∀ d, p < d → homogeneousComponent d (pbwCoord k hk x) = 0 := by
  rw [mem_ordinaryPiece_iff_coord k hk]
  constructor
  · intro h d hd
    ext mu
    rw [coeff_homogeneousComponent, coeff_zero]
    split_ifs with hmu
    · exact h mu (by rw [hmu]; exact hd)
    · rfl
  · intro h mu hmu
    have := congrArg (coeff mu) (h mu.degree hmu)
    rwa [coeff_homogeneousComponent, if_pos rfl, coeff_zero] at this

theorem homogeneousComponent_eq_zero_of_mem {p d : ℕ} (hd : p < d) {x : WakModule k}
    (hx : x ∈ ordinaryPiece k p) : homogeneousComponent d (pbwCoord k hk x) = 0 :=
  (mem_ordinaryPiece_iff_homog k hk p x).mp hx d hd

theorem pbwSpan_eq_ordinaryPiece (p : ℕ) : pbwSpan k hk p = ordinaryPiece k p :=
  (ordinaryPiece_eq_pbwSpan k hk p).symm

/-- A vector is the sum of its degree-`≤ p` coordinates; the basis expansion restricted to a
degree, read back in `V^k`. -/
def degPart (d : ℕ) : WakModule k →ₗ[ℂ] WakModule k :=
  (pbwCoord k hk).symm.toLinearMap ∘ₗ (homogeneousComponent d).restrictScalars ℂ ∘ₗ
    (pbwCoord k hk).toLinearMap

theorem pbwCoord_degPart (d : ℕ) (x : WakModule k) :
    pbwCoord k hk (degPart k hk d x) = homogeneousComponent d (pbwCoord k hk x) := by
  simp [degPart]

theorem degPart_mem (d : ℕ) (x : WakModule k) : degPart k hk d x ∈ ordinaryPiece k d := by
  rw [mem_ordinaryPiece_iff_homog k hk, pbwCoord_degPart]
  intro e he
  rw [homogeneousComponent_of_mem (homogeneousComponent_mem d _), if_neg (by omega)]

/-- A vector of the `t`-th piece minus its top-degree part lies in the previous piece. -/
theorem sub_degPart_mem {t : ℕ} {x : WakModule k} (hx : x ∈ ordinaryPiece k t) :
    x - degPart k hk t x ∈ ordinaryPiece k (t - 1) := by
  rw [mem_ordinaryPiece_iff_homog k hk]
  intro d hd
  rw [map_sub, map_sub, pbwCoord_degPart]
  by_cases hdt : d = t
  · subst hdt
    rw [homogeneousComponent_of_mem (homogeneousComponent_mem d _), if_pos rfl, sub_self]
  · rw [homogeneousComponent_of_mem (homogeneousComponent_mem t _), if_neg hdt,
      sub_zero]
    exact homogeneousComponent_eq_zero_of_mem k hk (by omega) hx

/-! ### The leading part of a creation mode -/

/-- On the top degree, `J^a_{-j-1}` acts as multiplication by `x_{(a,j)}`: for `x` in the `t`-th
piece, the degree-`(t+1)` part of the coordinates of `J^a_{-j-1} x` is `x_{(a,j)}` times the
degree-`t` part of the coordinates of `x`. -/
theorem homogeneousComponent_J (q : LexLetter) {t : ℕ} {x : WakModule k}
    (hx : x ∈ ordinaryPiece k t) :
    homogeneousComponent (t + 1)
        (pbwCoord k hk (J k (ofLex q).1 (-((ofLex q).2 : ℤ) - 1) x)) =
      X q * homogeneousComponent t (pbwCoord k hk x) := by
  classical
  -- expand `x` in the basis
  have hx' : x = ∑ mu ∈ ((currentPBWBasis k hk).repr x).support,
      (currentPBWBasis k hk).repr x mu • currentPBWBasis k hk mu := by
    conv_lhs => rw [← (currentPBWBasis k hk).linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  set s := ((currentPBWBasis k hk).repr x).support
  set c := (currentPBWBasis k hk).repr x
  have hdeg : ∀ mu ∈ s, mu.degree ≤ t := by
    intro mu hmu
    by_contra h
    have := (mem_ordinaryPiece_iff_repr k hk t x).mp hx mu (by rw [pbwLength_eq_degree]; omega)
    exact (Finsupp.mem_support_iff.mp hmu) this
  conv_lhs => rw [hx']
  conv_rhs => rw [hx']
  simp only [map_sum, map_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun mu hmu => ?_
  rw [mul_smul_comm]
  congr 1
  rw [pbwCoord_basis]
  have hJ := J_basis_sub_mem k hk q mu
  rw [pbwSpan_eq_ordinaryPiece] at hJ
  have hsplit : pbwCoord k hk (J k (ofLex q).1 (-((ofLex q).2 : ℤ) - 1)
      (currentPBWBasis k hk mu)) =
      pbwCoord k hk (J k (ofLex q).1 (-((ofLex q).2 : ℤ) - 1) (currentPBWBasis k hk mu) -
        currentPBWBasis k hk (Finsupp.single q 1 + mu)) + monomial (Finsupp.single q 1 + mu) 1 := by
    rw [map_sub, pbwCoord_basis, sub_add_cancel]
  rw [hsplit, map_add, homogeneousComponent_eq_zero_of_mem k hk (by have := hdeg mu hmu; omega) hJ,
    zero_add, homogeneousComponent_of_mem (isHomogeneous_monomial _ rfl),
    homogeneousComponent_of_mem (isHomogeneous_monomial _ rfl)]
  rw [map_add, Finsupp.degree_single]
  by_cases ht : mu.degree = t
  · rw [if_pos (by omega), if_pos ht.symm, X, monomial_mul, one_mul]
  · rw [if_neg (by omega), if_neg (Ne.symm ht), mul_zero]

/-! ### The top-degree part of a creation word -/

theorem homogeneousComponent_lexState (l : List LexLetter) :
    homogeneousComponent l.length (pbwCoord k hk (lexState k l)) = monomial (expOf l) 1 := by
  rcases l with _ | ⟨q, l⟩
  · have h : lexState k [] = currentPBWBasis k hk (expOf []) := by
      rw [basis_expOf_of_sorted k hk [] List.Pairwise.nil]
    rw [h, pbwCoord_basis, homogeneousComponent_of_mem (isHomogeneous_monomial _ rfl)]
    simp [expOf]
  · have h := lexState_sub_basis_mem k hk (q :: l)
    rw [pbwSpan_eq_ordinaryPiece] at h
    have hsplit : pbwCoord k hk (lexState k (q :: l)) =
        pbwCoord k hk (lexState k (q :: l) - currentPBWBasis k hk (expOf (q :: l))) +
          monomial (expOf (q :: l)) 1 := by
      rw [map_sub, pbwCoord_basis, sub_add_cancel]
    rw [hsplit, map_add, homogeneousComponent_eq_zero_of_mem k hk (by simp) h, zero_add,
      homogeneousComponent_of_mem (isHomogeneous_monomial _ rfl), if_pos]
    rw [degree_expOf]

/-! ### The degree-preserving part of a nonnegative mode -/

/-- The letter `(i, j - m)`, the creation letter of `J^i_{m - j - 1}` when `j ≥ m`. -/
abbrev shiftLetter (i : Fin 3) (q : LexLetter) (m : ℕ) : LexLetter := toLex (i, (ofLex q).2 - m)

/-- **The symbol derivation of `J^c_m` (`m ≥ 0`)**: `x_{(b,j)} ↦ Σ_i f^{cb}_i x_{(i, j - m)}` if
`j ≥ m`, and `0` otherwise. -/
def symDer (c : Fin 3) (m : ℕ) : Derivation ℂ (MvPolynomial LexLetter ℂ) (MvPolynomial LexLetter ℂ) :=
  mkDerivation ℂ fun q => if m ≤ (ofLex q).2 then
    ∑ i : Fin 3, fabc c (ofLex q).1 i • X (shiftLetter i q m) else 0

theorem symDer_X (c : Fin 3) (m : ℕ) (q : LexLetter) :
    symDer c m (X q) = if m ≤ (ofLex q).2 then
      ∑ i : Fin 3, fabc c (ofLex q).1 i • X (shiftLetter i q m) else 0 :=
  mkDerivation_X _ _ _

theorem J_nonneg_mem (c : Fin 3) (m : ℕ) {p : ℕ} {x : WakModule k}
    (hx : x ∈ ordinaryPiece k p) : J k c m x ∈ ordinaryPiece k p :=
  J_mem_ordinaryPiece_of_nonneg c (Int.natCast_nonneg m) hx

/-- **On the top degree, `J^c_m` (`m ≥ 0`) acts on a creation word as the symbol
derivation.** -/
theorem homogeneousComponent_J_nonneg_lexState (c : Fin 3) (m : ℕ) (l : List LexLetter) :
    homogeneousComponent l.length (pbwCoord k hk (J k c m (lexState k l))) =
      symDer c m (monomial (expOf l) 1) := by
  induction l with
  | nil =>
      have h0 : J k c m (lexState k []) = 0 := by
        rw [lexState, List.map_nil, wordStateA_nil]
        exact J_vacuum_nonneg k c (Int.natCast_nonneg m)
      rw [h0, map_zero, map_zero]
      simp [expOf]
  | cons q l ih =>
      set y := lexState k l
      have hy : y ∈ ordinaryPiece k l.length := by
        rw [← pbwSpan_eq_ordinaryPiece k hk]; exact lexState_mem_pbwSpan k hk l
      have hcomm := LinearMap.congr_fun
        (current_comm k c (ofLex q).1 (m : ℤ) (-((ofLex q).2 : ℤ) - 1)) y
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
        LinearMap.sum_apply, LinearMap.smul_apply] at hcomm
      rw [sub_eq_iff_eq_add] at hcomm
      rw [lexState_cons, hcomm, map_add, map_add, map_add, map_add, List.length_cons,
        homogeneousComponent_J k hk q (J_nonneg_mem k c m hy), ih]
      -- the central term
      have hcen : homogeneousComponent (l.length + 1) (pbwCoord k hk
          ((if (m : ℤ) + (-((ofLex q).2 : ℤ) - 1) = 0 then
            ((((m : ℤ) : ℂ)) * k * kappa c (ofLex q).1) •
            (LinearMap.id : Module.End ℂ (WakModule k)) else 0) y)) = 0 := by
        refine homogeneousComponent_eq_zero_of_mem k hk (p := l.length) (by omega) ?_
        split_ifs
        · exact Submodule.smul_mem _ _ hy
        · exact Submodule.zero_mem _
      rw [hcen, add_zero]
      -- the structure-constant terms
      have hsum : homogeneousComponent (l.length + 1) (pbwCoord k hk
          (∑ i : Fin 3, fabc c (ofLex q).1 i • J k i ((m : ℤ) + (-((ofLex q).2 : ℤ) - 1)) y)) =
          (if m ≤ (ofLex q).2 then
            ∑ i : Fin 3, fabc c (ofLex q).1 i • X (shiftLetter i q m) else 0) *
            monomial (expOf l) 1 := by
        simp only [map_sum, map_smul]
        split_ifs with hjm
        · rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_mul_assoc]
          congr 1
          have hidx : (m : ℤ) + (-((ofLex q).2 : ℤ) - 1) =
              -(((ofLex (shiftLetter i q m)).2 : ℕ) : ℤ) - 1 := by
            simp only [shiftLetter, ofLex_toLex]
            omega
          have hlet : (ofLex (shiftLetter i q m)).1 = i := by simp [shiftLetter]
          have hJ : J k i (-(((ofLex (shiftLetter i q m)).2 : ℕ) : ℤ) - 1) y =
              lexState k (shiftLetter i q m :: l) := by
            rw [lexState_cons, hlet]
          have hlen : l.length + 1 = (shiftLetter i q m :: l).length := rfl
          rw [hidx, hJ, hlen, homogeneousComponent_lexState, expOf_cons, X, monomial_mul,
            one_mul]
        · rw [zero_mul]
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [homogeneousComponent_eq_zero_of_mem k hk (p := l.length) (by omega)
            (J_mem_ordinaryPiece_of_nonneg i (by omega) hy), smul_zero]
      rw [hsum, expOf_cons, ← one_mul (1 : ℂ), ← monomial_mul, one_mul, ← X,
        Derivation.leibniz, symDer_X, smul_eq_mul, smul_eq_mul]
      ring

/-- **The degree-preserving part of a nonnegative mode is the symbol derivation**: for `x`
in the `t`-th piece, the degree-`t` part of the coordinates of `J^c_m x` is `symDer c m` of the
degree-`t` part of the coordinates of `x`. -/
theorem homogeneousComponent_J_nonneg (c : Fin 3) (m : ℕ) {t : ℕ} {x : WakModule k}
    (hx : x ∈ ordinaryPiece k t) :
    homogeneousComponent t (pbwCoord k hk (J k c m x)) =
      symDer c m (homogeneousComponent t (pbwCoord k hk x)) := by
  classical
  have hx' : x = ∑ mu ∈ ((currentPBWBasis k hk).repr x).support,
      (currentPBWBasis k hk).repr x mu • currentPBWBasis k hk mu := by
    conv_lhs => rw [← (currentPBWBasis k hk).linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  set s := ((currentPBWBasis k hk).repr x).support
  set c' := (currentPBWBasis k hk).repr x
  have hdeg : ∀ mu ∈ s, mu.degree ≤ t := by
    intro mu hmu
    by_contra h
    have := (mem_ordinaryPiece_iff_repr k hk t x).mp hx mu (by rw [pbwLength_eq_degree]; omega)
    exact (Finsupp.mem_support_iff.mp hmu) this
  conv_lhs => rw [hx']
  conv_rhs => rw [hx']
  simp only [map_sum, map_smul, Derivation.map_smul]
  refine Finset.sum_congr rfl fun mu hmu => ?_
  congr 1
  rw [pbwCoord_basis, homogeneousComponent_of_mem (isHomogeneous_monomial _ rfl)]
  by_cases ht : t = mu.degree
  · rw [if_pos ht, basis_eq_lexState]
    have hl : (lexExponentWord mu).length = t := by
      rw [← degree_expOf, expOf_lexExponentWord, ht]
    rw [← hl, homogeneousComponent_J_nonneg_lexState, expOf_lexExponentWord]
  · rw [if_neg ht, map_zero]
    refine homogeneousComponent_eq_zero_of_mem k hk (p := mu.degree)
      (lt_of_le_of_ne (hdeg mu hmu) (Ne.symm ht)) (J_nonneg_mem k c m ?_)
    rw [← pbwSpan_eq_ordinaryPiece k hk]
    exact Submodule.subset_span ⟨mu, by simp [pbwLength_eq_degree], rfl⟩

/-! ### Conformal weights of PBW monomials -/

/-- The conformal weight of the letter `(a, j)` (the mode `J^a_{-j-1}`) is `j + 1`. -/
abbrev letterWt (q : LexLetter) : ℕ := (ofLex q).2 + 1

/-- The conformal weight of a PBW exponent. -/
abbrev enOf (mu : CurrentIndex) : ℕ := Finsupp.weight letterWt mu

theorem wordDegA_map_ofLex (l : List LexLetter) :
    wordDegA (l.map ofLex) = (enOf (expOf l) : ℤ) := by
  induction l with
  | nil => simp [expOf]
  | cons q l ih =>
      rw [List.map_cons, wordDegA_cons, ih, expOf_cons]
      simp only [enOf, map_add, Finsupp.weight_single, letterWt, smul_eq_mul, one_mul]
      push_cast
      ring

theorem currentEnergy_eq_enOf (mu : CurrentIndex) : currentEnergy mu = (enOf mu : ℤ) := by
  rw [currentEnergy, orderedPBWColorWord_eq, wordDegA_map_ofLex, expOf_lexExponentWord]

theorem basis_mem_grading (mu : CurrentIndex) :
    currentPBWBasis k hk mu ∈ (universal k hk).grading (enOf mu : ℤ) := by
  rw [← currentEnergy_eq_enOf, currentPBWBasis_apply, currentEnergy]
  exact creation_state_grading k hk _

/-- Coordinates of a vector of weight `m` are supported on exponents of weight `m`. -/
theorem coeff_eq_zero_of_mem_grading {m : ℤ} {x : WakModule k}
    (hx : x ∈ (universal k hk).grading m) {mu : CurrentIndex} (hmu : (enOf mu : ℤ) ≠ m) :
    coeff mu (pbwCoord k hk x) = 0 := by
  rw [coeff_pbwCoord]
  have h := basis_diagonal_coordinate (currentPBWBasis k hk) ((universal k hk).L 0)
    (fun mu => (currentEnergy mu : ℂ)) (currentPBWBasis_L0 k hk) x mu
  rw [(universal k hk).L_zero_grading x hx, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
  have h' : ((m : ℂ) - (currentEnergy mu : ℂ)) * (currentPBWBasis k hk).repr x mu = 0 := by
    rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.mp h' with h0 | h0
  · exfalso
    apply hmu
    rw [← currentEnergy_eq_enOf]
    exact_mod_cast (sub_eq_zero.mp h0).symm
  · exact h0

/-- A vector whose coordinates are supported on exponents of weight `m` has weight `m`. -/
theorem mem_grading_of_coeff {m : ℤ} {x : WakModule k}
    (h : ∀ mu, (enOf mu : ℤ) ≠ m → coeff mu (pbwCoord k hk x) = 0) :
    x ∈ (universal k hk).grading m := by
  classical
  have hx' : x = ∑ mu ∈ ((currentPBWBasis k hk).repr x).support,
      (currentPBWBasis k hk).repr x mu • currentPBWBasis k hk mu := by
    conv_lhs => rw [← (currentPBWBasis k hk).linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  rw [hx']
  refine Submodule.sum_mem _ fun mu hmu => ?_
  by_cases hm : (enOf mu : ℤ) = m
  · exact Submodule.smul_mem _ _ (hm ▸ basis_mem_grading k hk mu)
  · have := h mu hm
    rw [coeff_pbwCoord] at this
    rw [this, zero_smul]
    exact Submodule.zero_mem _

theorem degPart_mem_grading (d : ℕ) {m : ℤ} {x : WakModule k}
    (hx : x ∈ (universal k hk).grading m) : degPart k hk d x ∈ (universal k hk).grading m := by
  refine mem_grading_of_coeff k hk fun mu hmu => ?_
  rw [pbwCoord_degPart, coeff_homogeneousComponent]
  split_ifs
  · exact coeff_eq_zero_of_mem_grading k hk hx hmu
  · rfl

theorem degPart_of_mem_zero {x : WakModule k} (hx : x ∈ ordinaryPiece k 0) :
    degPart k hk 0 x = x := by
  apply (pbwCoord k hk).injective
  rw [pbwCoord_degPart]
  ext mu
  rw [coeff_homogeneousComponent]
  split_ifs with h
  · rfl
  · exact ((mem_ordinaryPiece_iff_coord k hk 0 x).mp hx mu (by omega)).symm

end

end VOA.KoszulResidual
