/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.AffineSl2PBWWakimotoReduction
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The first Li-leading terms of the Wakimoto currents

This file begins the triangularity argument left open by
`AffineSl2PBWWakimotoReduction`.  Give every Wakimoto variable its jet index:

* `b_i = X (0,i-1)` and `A_i = X (2,i-1)` have free Li weight `i-1`;
* `c_j = X (1,j)` has free Li weight `j`.

For a current of mode `-n-1`, all classical Wakimoto terms have weight `n`.  The derivative
correction in the `f` current is `k(n+1)c_(n+1)`, hence has weight `n+1`.  At the one-current level
this gives a very simple top component.  It does **not** by itself give a word-level order:
contractions in a later composite current can raise this weight.

The file also proves two abstract no-cancellation lemmas used by the word-level
argument.  `linearIndependent_of_lowerLeading` says that a family is linearly independent when
its first nonzero filtered components form an independent family.  `linearIndependent_of_pivot`
is the coefficient-extraction version for multivariable polynomials.

## Status

The one-current decompositions, their exact finite convolution formulas, and both abstract
triangularity lemmas are proved.  A tempting order maximizing free Li weight first
**fails** already on two `h` currents: `BG_{-1}(BG_{-2}|0>)` contains the surviving terms
`-b_3 c_0 + b_1 c_2`, of weight two rather than the naive depth sum one.  The stable replacement
is the minimal-weight classical symbol.  The operator theorem is proved for all basic
modes, `BG`, `AG`, `GG`, `BGG`, all three currents, and arbitrary negative-current words: every
contraction is deeper, every component below the sum of current depths vanishes, and the component
at that minimum is exactly the product of the classical one-current symbols.  A second
lexicographic triangular order has pivots `e_n ↦ b_n`, `f_n ↦ A_0 c_n`, and `h_n ↦ A_n`.
Its exponent map is injective, including the `h_0` coordinate after recovering the total number
of `f` letters from the target `c` exponent.  Consequently the classical substitution is
injective at every level, the Wakimoto ordered current words are linearly independent at every
level, and the named ordinary affine PBW basis is **proved** at every noncritical level.
-/

namespace VOA
namespace AffineSl2WakimotoLiLeading

open VOA.AffineLie
open VOA.AffineSl2PBWWakimotoReduction

noncomputable section

/-! ## Abstract filtered and coefficient triangularity -/

section AbstractLeading

variable {R ι M : Type*} [DivisionRing R] [AddCommGroup M] [Module R M]

/-- A family is independent if its first nonzero filtered components are an independent family.

The hypotheses say that `lead i` is the component of `f i` in degree `degree i`, and that every
component strictly below `degree i` vanishes.  The proof applies a fixed component projection to
a finite relation and inducts upward on the degrees occurring in that relation. -/
theorem linearIndependent_of_lowerLeading (degree : ι → ℕ) (f lead : ι → M)
    (component : ℕ → M →ₗ[R] M)
    (hself : ∀ i, component (degree i) (f i) = lead i)
    (hlower : ∀ i n, n < degree i → component n (f i) = 0)
    (hlead : LinearIndependent R lead) : LinearIndependent R f := by
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have hvanish : ∀ n : ℕ, ∀ j ∈ s, degree j = n → g j = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        have hprojected := congrArg (component n) hsum
        simp only [map_sum, map_smul, map_zero] at hprojected
        have hleadRel : ∑ j ∈ s, (if degree j = n then g j else 0) • lead j = 0 := by
          rw [← hprojected]
          refine Finset.sum_congr rfl fun j hj => ?_
          by_cases heq : degree j = n
          · rw [if_pos heq, ← heq, hself]
          · rw [if_neg heq]
            rcases lt_or_gt_of_ne heq with hlt | hgt
            · rw [ih (degree j) hlt j hj rfl]
              simp
            · rw [hlower j n hgt]
              simp
        have hz := linearIndependent_iff'.mp hlead s
          (fun j => if degree j = n then g j else 0) hleadRel
        intro j hj hjn
        have := hz j hj
        simpa [hjn] using this
  exact hvanish (degree i) i hi rfl

/-- Finite-minimum version of `linearIndependent_of_lowerLeading`, valid for an arbitrary linear
order on the grading set.  No global well-foundedness is needed because every linear relation has
finite support. -/
theorem linearIndependent_of_lowerLeading_linearOrder {D : Type*} [LinearOrder D]
    (degree : ι → D) (f lead : ι → M) (component : D → M →ₗ[R] M)
    (hself : ∀ i, component (degree i) (f i) = lead i)
    (hlower : ∀ i d, d < degree i → component d (f i) = 0)
    (hlead : LinearIndependent R lead) : LinearIndependent R f := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  let t := s.filter fun j => g j ≠ 0
  have ht : t.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  let d := (t.image degree).min' (ht.image degree)
  have hdmem : d ∈ t.image degree := Finset.min'_mem _ _
  obtain ⟨j₀, hj₀t, hj₀deg⟩ := Finset.mem_image.mp hdmem
  have hprojected := congrArg (component d) hsum
  simp only [map_sum, map_smul, map_zero] at hprojected
  have hleadRel : ∑ j ∈ s, (if degree j = d then g j else 0) • lead j = 0 := by
    rw [← hprojected]
    refine Finset.sum_congr rfl fun j hj => ?_
    by_cases hjg : g j = 0
    · simp [hjg]
    · have hjt : j ∈ t := Finset.mem_filter.mpr ⟨hj, hjg⟩
      have hdle : d ≤ degree j := Finset.min'_le _ _ (Finset.mem_image.mpr ⟨j, hjt, rfl⟩)
      rcases hdle.eq_or_lt with heq | hlt
      · rw [if_pos heq.symm, ← hself j, ← heq]
      · rw [if_neg (ne_of_gt hlt), hlower j d hlt]
        simp
  have hz := linearIndependent_iff'.mp hlead s
    (fun j => if degree j = d then g j else 0) hleadRel
  have hj₀s : j₀ ∈ s := (Finset.mem_filter.mp hj₀t).1
  have := hz j₀ hj₀s
  have hj₀zero : g j₀ = 0 := by simpa only [hj₀deg, ↓reduceIte] using this
  exact (Finset.mem_filter.mp hj₀t).2 hj₀zero

end AbstractLeading

section PolynomialPivot

variable {R σ ι : Type*} [CommRing R] [IsDomain R]

/-- Coefficient pivots prove polynomial linear independence: each member has a nonzero
coefficient at its own pivot monomial and every other member has zero coefficient there. -/
theorem linearIndependent_of_pivot (f : ι → MvPolynomial σ R) (pivot : ι → σ →₀ ℕ)
    (hpivot : ∀ i, MvPolynomial.coeff (pivot i) (f i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → MvPolynomial.coeff (pivot i) (f j) = 0) :
    LinearIndependent R f := by
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have hcoeff := congrArg (MvPolynomial.coeff (pivot i)) hsum
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single i] at hcoeff
  · exact (mul_eq_zero.mp hcoeff).resolve_right (hpivot i)
  · intro j hj hji
    simp [hoff i j (Ne.symm hji)]
  · exact fun hnot => (hnot hi).elim

end PolynomialPivot

/-! ## The free-field Li weight -/

/-- Jet-index weight on the three Wakimoto variable colours.  This is conformal weight minus the
number of `b` and `A` creation variables. -/
def freeLiWeight : Fin 3 × ℕ → ℕ := fun v => v.2

/-- Polynomial degree in the bosonic `A` variables alone.  It is the second coordinate of the
lexicographic boundary triangular order. -/
def aDegreeWeight : Fin 3 × ℕ → ℕ := fun v => if v.1 = 2 then 1 else 0

/-! ## A lexicographic classical-symbol filtration -/

/-- The classical-symbol order first minimizes the number of `c` variables and, subject to that,
maximizes their total jet index. -/
abbrev ClassicalTriDegree := Lex (ℤ × ℤ)

/-- Additivity of the lexicographic order, not currently packaged as a typeclass for `Lex`. -/
theorem classicalTri_add_le_add {a b c d : ClassicalTriDegree} (hab : a ≤ b) (hcd : c ≤ d) :
    a + c ≤ b + d := by
  rw [Prod.Lex.le_iff] at hab hcd ⊢
  rcases hab with hab | ⟨hab, hab'⟩
  · rcases hcd with hcd | ⟨hcd, hcd'⟩
    · left; simp only [ofLex_add, Prod.fst_add]; omega
    · left; simp only [ofLex_add, Prod.fst_add]; omega
  · rcases hcd with hcd | ⟨hcd, hcd'⟩
    · left; simp only [ofLex_add, Prod.fst_add]; omega
    · right
      simp only [ofLex_add, Prod.fst_add, Prod.snd_add]
      constructor <;> omega

theorem classicalTri_add_lt_add_of_lt_of_le {a b c d : ClassicalTriDegree}
    (hab : a < b) (hcd : c ≤ d) : a + c < b + d := by
  rw [Prod.Lex.lt_iff] at hab ⊢
  rw [Prod.Lex.le_iff] at hcd
  rcases hab with hab | ⟨hab, hab'⟩
  · rcases hcd with hcd | ⟨hcd, hcd'⟩
    · left; simp only [ofLex_add, Prod.fst_add]; omega
    · left; simp only [ofLex_add, Prod.fst_add]; omega
  · rcases hcd with hcd | ⟨hcd, hcd'⟩
    · left; simp only [ofLex_add, Prod.fst_add]; omega
    · right
      simp only [ofLex_add, Prod.fst_add, Prod.snd_add]
      constructor <;> omega

theorem classicalTri_add_lt_add_of_le_of_lt {a b c d : ClassicalTriDegree}
    (hab : a ≤ b) (hcd : c < d) : a + c < b + d := by
  rw [add_comm a c, add_comm b d]
  exact classicalTri_add_lt_add_of_lt_of_le hcd hab

/-- Lexicographic weight of a Fock monomial: `(number of c's, - total c jet index)`. -/
def classicalTriWeight : Fin 3 × ℕ → ClassicalTriDegree := fun v =>
  if v.1 = 1 then toLex (1, -(v.2 : ℤ)) else 0

@[simp] theorem classicalTriWeight_zero (n : ℕ) :
    classicalTriWeight ((0 : Fin 3), n) = 0 := by simp [classicalTriWeight]

@[simp] theorem classicalTriWeight_one (n : ℕ) :
    classicalTriWeight ((1 : Fin 3), n) = toLex (1, -(n : ℤ)) := by
  simp [classicalTriWeight]

@[simp] theorem classicalTriWeight_two (n : ℕ) :
    classicalTriWeight ((2 : Fin 3), n) = 0 := by simp [classicalTriWeight]

/-- Polynomials all of whose monomials have triangular weight at least `d`. -/
def classicalTriAtLeast (d : ClassicalTriDegree) : Submodule ℂ Wak.WakFock where
  carrier := {P | ∀ e, MvPolynomial.coeff e P ≠ 0 →
    d ≤ Finsupp.weight classicalTriWeight e}
  zero_mem' := by simp
  add_mem' := by
    intro P Q hP hQ e he
    rw [MvPolynomial.coeff_add] at he
    by_cases hp : MvPolynomial.coeff e P = 0
    · exact hQ e (by simpa only [hp, zero_add] using he)
    · exact hP e hp
  smul_mem' := by
    intro c P hP e he
    rw [MvPolynomial.coeff_smul] at he
    exact hP e (right_ne_zero_of_mul he)

/-- Polynomials all of whose monomials have triangular weight strictly above `d`. -/
def classicalTriAbove (d : ClassicalTriDegree) : Submodule ℂ Wak.WakFock where
  carrier := {P | ∀ e, MvPolynomial.coeff e P ≠ 0 →
    d < Finsupp.weight classicalTriWeight e}
  zero_mem' := by simp
  add_mem' := by
    intro P Q hP hQ e he
    rw [MvPolynomial.coeff_add] at he
    by_cases hp : MvPolynomial.coeff e P = 0
    · exact hQ e (by simpa only [hp, zero_add] using he)
    · exact hP e hp
  smul_mem' := by
    intro c P hP e he
    rw [MvPolynomial.coeff_smul] at he
    exact hP e (right_ne_zero_of_mul he)

theorem classicalTriAtLeast_mul {a b : ClassicalTriDegree} {P Q : Wak.WakFock}
    (hP : P ∈ classicalTriAtLeast a) (hQ : Q ∈ classicalTriAtLeast b) :
    P * Q ∈ classicalTriAtLeast (a + b) := by
  intro e he
  rw [MvPolynomial.coeff_mul] at he
  obtain ⟨⟨u, v⟩, huv, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  have hPu : MvPolynomial.coeff u P ≠ 0 := left_ne_zero_of_mul hterm
  have hQv : MvPolynomial.coeff v Q ≠ 0 := right_ne_zero_of_mul hterm
  have huv' : u + v = e := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
  rw [← huv', map_add]
  exact classicalTri_add_le_add (hP u hPu) (hQ v hQv)

theorem classicalTriAbove_mul_atLeast {a b : ClassicalTriDegree} {P Q : Wak.WakFock}
    (hP : P ∈ classicalTriAbove a) (hQ : Q ∈ classicalTriAtLeast b) :
    P * Q ∈ classicalTriAbove (a + b) := by
  intro e he
  rw [MvPolynomial.coeff_mul] at he
  obtain ⟨⟨u, v⟩, huv, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  have hPu : MvPolynomial.coeff u P ≠ 0 := left_ne_zero_of_mul hterm
  have hQv : MvPolynomial.coeff v Q ≠ 0 := right_ne_zero_of_mul hterm
  have huv' : u + v = e := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
  rw [← huv', map_add]
  exact classicalTri_add_lt_add_of_lt_of_le (hP u hPu) (hQ v hQv)

theorem classicalTriAtLeast_mul_above {a b : ClassicalTriDegree} {P Q : Wak.WakFock}
    (hP : P ∈ classicalTriAtLeast a) (hQ : Q ∈ classicalTriAbove b) :
    P * Q ∈ classicalTriAbove (a + b) := by
  intro e he
  rw [MvPolynomial.coeff_mul] at he
  obtain ⟨⟨u, v⟩, huv, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  have hPu : MvPolynomial.coeff u P ≠ 0 := left_ne_zero_of_mul hterm
  have hQv : MvPolynomial.coeff v Q ≠ 0 := right_ne_zero_of_mul hterm
  have huv' : u + v = e := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
  rw [← huv', map_add]
  exact classicalTri_add_lt_add_of_le_of_lt (hP u hPu) (hQ v hQv)

theorem classicalTriAbove_component_eq_zero {d r : ClassicalTriDegree} {P : Wak.WakFock}
    (hP : P ∈ classicalTriAbove d) (hr : r ≤ d) :
    MvPolynomial.weightedHomogeneousComponent classicalTriWeight r P = 0 := by
  ext e
  rw [MvPolynomial.coeff_weightedHomogeneousComponent]
  split_ifs with he
  · by_cases hc : MvPolynomial.coeff e P = 0
    · exact hc
    · exact (not_lt_of_ge hr (he ▸ hP e hc)).elim
  · rfl

theorem classicalTriAtLeast_component_eq_zero {d r : ClassicalTriDegree} {P : Wak.WakFock}
    (hP : P ∈ classicalTriAtLeast d) (hr : r < d) :
    MvPolynomial.weightedHomogeneousComponent classicalTriWeight r P = 0 := by
  ext e
  rw [MvPolynomial.coeff_weightedHomogeneousComponent]
  split_ifs with he
  · by_cases hc : MvPolynomial.coeff e P = 0
    · exact hc
    · exact (not_lt_of_ge (hP e hc) (he ▸ hr)).elim
  · rfl

theorem isWeightedHomogeneous_mem_classicalTriAtLeast {d : ClassicalTriDegree}
    {P : Wak.WakFock}
    (hP : MvPolynomial.IsWeightedHomogeneous classicalTriWeight P d) :
    P ∈ classicalTriAtLeast d := fun e he => (hP he).ge

theorem isWeightedHomogeneous_mem_classicalTriAbove {d e : ClassicalTriDegree}
    {P : Wak.WakFock} (hde : d < e)
    (hP : MvPolynomial.IsWeightedHomogeneous classicalTriWeight P e) :
    P ∈ classicalTriAbove d := fun m hm => hP hm ▸ hde

theorem classicalTriAbove_le_atLeast (d : ClassicalTriDegree) :
    classicalTriAbove d ≤ classicalTriAtLeast d := fun _ hP m hm => (hP m hm).le

theorem X_isWeightedHomogeneous_classicalTri (a : Fin 3) (n : ℕ) :
    (MvPolynomial.X (a, n) : Wak.WakFock).IsWeightedHomogeneous classicalTriWeight
      (classicalTriWeight (a, n)) :=
  MvPolynomial.isWeightedHomogeneous_X ℂ classicalTriWeight (a, n)

theorem X_isWeightedHomogeneous_freeLi (a : Fin 3) (n : ℕ) :
    (MvPolynomial.X (a, n) : Wak.WakFock).IsWeightedHomogeneous freeLiWeight n := by
  exact MvPolynomial.isWeightedHomogeneous_X ℂ freeLiWeight (a, n)

theorem X_isWeightedHomogeneous_aDegree (a : Fin 3) (n : ℕ) :
    (MvPolynomial.X (a, n) : Wak.WakFock).IsWeightedHomogeneous aDegreeWeight
      (if a = 2 then 1 else 0) := by
  exact MvPolynomial.isWeightedHomogeneous_X ℂ aDegreeWeight (a, n)

/-! ## The minimum free-Li filtration -/

/-- Polynomials all of whose monomials have free-Li weight at least `d`, presented as the span of
the corresponding monomials.  This increasing lower bound is the stable direction for Wakimoto
contractions. -/
def freeLiAtLeast (d : ℕ) : Submodule ℂ Wak.WakFock :=
  Submodule.span ℂ {P | ∃ e : (Fin 3 × ℕ) →₀ ℕ,
    d ≤ Finsupp.weight freeLiWeight e ∧ P = MvPolynomial.monomial e 1}

theorem monomial_mem_freeLiAtLeast {d : ℕ} (e : (Fin 3 × ℕ) →₀ ℕ)
    (he : d ≤ Finsupp.weight freeLiWeight e) :
    MvPolynomial.monomial e (1 : ℂ) ∈ freeLiAtLeast d :=
  Submodule.subset_span ⟨e, he, rfl⟩

theorem freeLiAtLeast_mono {d e : ℕ} (hde : d ≤ e) : freeLiAtLeast e ≤ freeLiAtLeast d := by
  apply Submodule.span_mono
  rintro P ⟨a, ha, rfl⟩
  exact ⟨a, le_trans hde ha, rfl⟩

/-- Weight zero is no restriction. -/
theorem mem_freeLiAtLeast_zero (P : Wak.WakFock) : P ∈ freeLiAtLeast 0 := by
  rw [MvPolynomial.as_sum P]
  exact Submodule.sum_mem _ fun e _ => by
    have hmono := monomial_mem_freeLiAtLeast (d := 0) e (Nat.zero_le _)
    have hsmul := Submodule.smul_mem (freeLiAtLeast 0) (MvPolynomial.coeff e P) hmono
    simpa only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one] using hsmul

/-- Multiplication by a variable of jet weight `r` raises the minimum free-Li weight by `r`. -/
theorem X_mul_mem_freeLiAtLeast (v : Fin 3 × ℕ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    MvPolynomial.X v * P ∈ freeLiAtLeast (d + freeLiWeight v) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨e, he, rfl⟩ := hP
      rw [MvPolynomial.X, MvPolynomial.monomial_mul]
      have hweight : d + freeLiWeight v ≤
          Finsupp.weight freeLiWeight (Finsupp.single v 1 + e) := by
        simpa only [map_add, Finsupp.weight_single, one_nsmul, add_comm] using
          add_le_add_left he (freeLiWeight v)
      simpa only [one_mul] using
        (monomial_mem_freeLiAtLeast (Finsupp.single v 1 + e) hweight)
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add P Q _ _ hP hQ => rw [mul_add]; exact Submodule.add_mem _ hP hQ
  | smul c P _ hP => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hP

/-- Differentiating in a variable of jet weight `r` lowers a known minimum weight by at most
`r`.  The zero derivative case is included. -/
theorem pderiv_mem_freeLiAtLeast (v : Fin 3 × ℕ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast (d + freeLiWeight v)) :
    MvPolynomial.pderiv v P ∈ freeLiAtLeast d := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨e, he, rfl⟩ := hP
      rw [MvPolynomial.pderiv_monomial, one_mul]
      by_cases hev : e v = 0
      · rw [hev, Nat.cast_zero, MvPolynomial.monomial_zero]
        exact Submodule.zero_mem _
      · have hmono := monomial_mem_freeLiAtLeast (d := d) (e - Finsupp.single v 1) (by
          have hw := Finsupp.weight_sub_single_add (w := freeLiWeight) hev
          omega)
        have hsmul := Submodule.smul_mem (freeLiAtLeast d) (e v : ℂ) hmono
        simpa only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one] using hsmul
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add P Q _ _ hP hQ => rw [map_add]; exact Submodule.add_mem _ hP hQ
  | smul c P _ hP =>
      change MvPolynomial.pderiv v (c • P) ∈ freeLiAtLeast d
      rw [(MvPolynomial.pderiv v).map_smul]
      exact Submodule.smul_mem _ c hP

/-- Subtraction form of the derivative estimate, convenient when the input lower bound is not
known to exceed the differentiated variable's weight. -/
theorem pderiv_mem_freeLiAtLeast_sub (v : Fin 3 × ℕ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    MvPolynomial.pderiv v P ∈ freeLiAtLeast (d - freeLiWeight v) := by
  by_cases hle : freeLiWeight v ≤ d
  · apply pderiv_mem_freeLiAtLeast v
    rw [Nat.sub_add_cancel hle]
    exact hP
  · have hz : d - freeLiWeight v = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [hz]
    exact mem_freeLiAtLeast_zero _

theorem bV_mul_mem_freeLiAtLeast {i : ℤ} (hi : 1 ≤ i) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.bV i * P ∈ freeLiAtLeast (d + (i - 1).toNat) := by
  rw [Wak.bV_of_pos hi]
  simpa only [freeLiWeight] using
    (X_mul_mem_freeLiAtLeast ((0 : Fin 3), (i - 1).toNat) hP)

theorem cV_mul_mem_freeLiAtLeast {j : ℤ} (hj : 0 ≤ j) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.cV j * P ∈ freeLiAtLeast (d + j.toNat) := by
  rw [Wak.cV_of_nonneg hj]
  simpa only [freeLiWeight] using
    (X_mul_mem_freeLiAtLeast ((1 : Fin 3), j.toNat) hP)

theorem aV_mul_mem_freeLiAtLeast {i : ℤ} (hi : 1 ≤ i) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.aV i * P ∈ freeLiAtLeast (d + (i - 1).toNat) := by
  rw [Wak.aV_of_pos hi]
  simpa only [freeLiWeight] using
    (X_mul_mem_freeLiAtLeast ((2 : Fin 3), (i - 1).toNat) hP)

theorem bD_mem_freeLiAtLeast {i : ℤ} (hi : 1 ≤ i) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.bD i P ∈ freeLiAtLeast (d - (i - 1).toNat) := by
  rw [Wak.bD_of_pos hi, Wak.dV_apply]
  simpa only [freeLiWeight] using
    (pderiv_mem_freeLiAtLeast_sub ((0 : Fin 3), (i - 1).toNat) hP)

theorem cD_mem_freeLiAtLeast {j : ℤ} (hj : 0 ≤ j) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.cD j P ∈ freeLiAtLeast (d - j.toNat) := by
  rw [Wak.cD_of_nonneg hj, Wak.dV_apply]
  simpa only [freeLiWeight] using
    (pderiv_mem_freeLiAtLeast_sub ((1 : Fin 3), j.toNat) hP)

theorem aD_mem_freeLiAtLeast {i : ℤ} (hi : 1 ≤ i) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.aD i P ∈ freeLiAtLeast (d - (i - 1).toNat) := by
  rw [Wak.aD_of_pos hi, Wak.dV_apply]
  simpa only [freeLiWeight] using
    (pderiv_mem_freeLiAtLeast_sub ((2 : Fin 3), (i - 1).toNat) hP)

/-- Every summand of `:βγ:_{-n-1}` raises the minimum free-Li weight by at least `n`.
The pure creation summands raise it by exactly `n`; every contraction raises it more. -/
theorem bgFam_neg_mem_freeLiAtLeast (n : ℕ) (p : ℤ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.bgFam (-((n : ℤ)) - 1) p P ∈ freeLiAtLeast (d + n) := by
  by_cases hp : p ≤ -1
  · rw [Wak.bgFam, if_pos hp, Module.End.mul_apply]
    by_cases hq : -((n : ℤ)) - 1 - p ≤ 0
    · rw [Wak.Gam_of_nonpos hq, Wak.mulL_apply, Wak.Bet_of_neg hp, Wak.mulL_apply]
      have hc := cV_mul_mem_freeLiAtLeast (j := -(-((n : ℤ)) - 1 - p)) (by omega) hP
      have hb := bV_mul_mem_freeLiAtLeast (i := -p) (by omega) hc
      have hweight : (d + (-(-((n : ℤ)) - 1 - p)).toNat) + (-p - 1).toNat = d + n := by
        omega
      rwa [hweight] at hb
    · rw [Wak.Gam_of_pos (by omega), Wak.Bet_of_neg hp, Wak.mulL_apply, LinearMap.neg_apply]
      have hd := bD_mem_freeLiAtLeast (i := -((n : ℤ)) - 1 - p) (by omega) hP
      have hb := bV_mul_mem_freeLiAtLeast (i := -p) (by omega)
        (Submodule.neg_mem _ hd)
      apply freeLiAtLeast_mono (d := d + n) (e :=
        (d - (-((n : ℤ)) - 1 - p - 1).toNat) + (-p - 1).toNat) (by omega)
      exact hb
  · rw [Wak.bgFam, if_neg hp, Module.End.mul_apply, Wak.Bet_of_nonneg (by omega)]
    have hd := cD_mem_freeLiAtLeast (j := p) (by omega) hP
    have hq : -((n : ℤ)) - 1 - p ≤ 0 := by omega
    rw [Wak.Gam_of_nonpos hq, Wak.mulL_apply]
    have hc := cV_mul_mem_freeLiAtLeast (j := -(-((n : ℤ)) - 1 - p)) (by omega) hd
    apply freeLiAtLeast_mono (d := d + n) (e :=
      (d - p.toNat) + (-(-((n : ℤ)) - 1 - p)).toNat) (by omega)
    exact hc

/-- The full negative `:βγ:` mode satisfies the minimum free-Li bound. -/
theorem BG_neg_mem_freeLiAtLeast (n : ℕ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.BG (-((n : ℤ)) - 1) P ∈ freeLiAtLeast (d + n) := by
  rw [Wak.BG, Wak.opSum_apply (Wak.bgFam_locFin (-((n : ℤ)) - 1)) P]
  exact QuotVOA.finsum_mem_submodule _ _ fun p => bgFam_neg_mem_freeLiAtLeast n p hP

/-- The finite convolution which is `:βγ:_{-n-1}|0⟩`. -/
def bgVac (n : ℕ) : Wak.WakFock :=
  ∑ p ∈ Finset.Icc (-((n : ℤ)) - 1) (-1), Wak.bV (-p) * Wak.cV ((n : ℤ) + 1 + p)

/-- The finite convolution which is `:aγ:_{-n-1}|0⟩`. -/
def agVac (n : ℕ) : Wak.WakFock :=
  ∑ p ∈ Finset.Icc (-((n : ℤ)) - 1) (-1), Wak.aV (-p) * Wak.cV ((n : ℤ) + 1 + p)

/-- The finite convolution which is `:γγ:_{-r}|0⟩`. -/
def ggVac (r : ℕ) : Wak.WakFock :=
  ∑ q ∈ Finset.Icc (-(r : ℤ)) 0, Wak.cV (-q) * Wak.cV ((r : ℤ) + q)

/-- The finite convolution which is `:βγγ:_{-n-1}|0⟩`. -/
def bggVac (n : ℕ) : Wak.WakFock :=
  ∑ p ∈ Finset.Icc (-((n : ℤ)) - 1) (-1),
    Wak.bV (-p) * ggVac (((n : ℤ) + 1 + p).toNat)

/-- Pure-creation summand of the negative `:βγ:` mode on an arbitrary input. -/
def bgClassicalFam (n : ℕ) (p : ℤ) (P : Wak.WakFock) : Wak.WakFock :=
  if -((n : ℤ)) - 1 ≤ p ∧ p ≤ -1 then
    (Wak.bV (-p) * Wak.cV ((n : ℤ) + 1 + p)) * P else 0

theorem bgClassicalFam_support_finite (n : ℕ) (P : Wak.WakFock) :
    (Function.support fun p : ℤ => bgClassicalFam n p P).Finite := by
  apply Set.Finite.subset (Finset.finite_toSet (Finset.Icc (-((n : ℤ)) - 1) (-1)))
  intro p hp
  simp only [Function.mem_support, Finset.coe_Icc, Set.mem_Icc] at hp ⊢
  by_contra hc
  exact hp (by rw [bgClassicalFam, if_neg hc])

/-- Summing the pure-creation family is multiplication by the vacuum convolution. -/
theorem finsum_bgClassicalFam (n : ℕ) (P : Wak.WakFock) :
    (∑ᶠ p : ℤ, bgClassicalFam n p P) = bgVac n * P := by
  rw [finsum_eq_finsetSum_of_support_subset _
    (s := Finset.Icc (-((n : ℤ)) - 1) (-1)) (by
      intro p hp
      simp only [Function.mem_support, Finset.coe_Icc, Set.mem_Icc] at hp ⊢
      by_contra hc
      exact hp (by rw [bgClassicalFam, if_neg hc]))]
  · rw [bgVac, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p hp => by
      rw [bgClassicalFam, if_pos (by simpa only [Finset.mem_Icc] using hp)]

/-- Every non-classical `:βγ:` summand is one step deeper in minimum free-Li weight. -/
theorem bgFam_sub_classical_mem_freeLiAtLeast (n : ℕ) (p : ℤ) {d : ℕ}
    {P : Wak.WakFock} (hP : P ∈ freeLiAtLeast d) :
    Wak.bgFam (-((n : ℤ)) - 1) p P - bgClassicalFam n p P ∈
      freeLiAtLeast (d + n + 1) := by
  by_cases hp : p ≤ -1
  · rw [Wak.bgFam, if_pos hp, Module.End.mul_apply]
    by_cases hq : -((n : ℤ)) - 1 - p ≤ 0
    · rw [Wak.Gam_of_nonpos hq, Wak.mulL_apply, Wak.Bet_of_neg hp, Wak.mulL_apply,
        bgClassicalFam, if_pos (by omega)]
      have hz : Wak.bV (-p) * (Wak.cV (-(-((n : ℤ)) - 1 - p)) * P) -
          Wak.bV (-p) * Wak.cV ((n : ℤ) + 1 + p) * P = 0 := by
        have hcarg : -(-((n : ℤ)) - 1 - p) = (n : ℤ) + 1 + p := by ring
        rw [hcarg]
        ring
      rw [hz]
      exact Submodule.zero_mem _
    · rw [Wak.Gam_of_pos (by omega), Wak.Bet_of_neg hp, Wak.mulL_apply,
        LinearMap.neg_apply, bgClassicalFam, if_neg (by omega), sub_zero]
      have hd := bD_mem_freeLiAtLeast (i := -((n : ℤ)) - 1 - p) (by omega) hP
      have hb := bV_mul_mem_freeLiAtLeast (i := -p) (by omega)
        (Submodule.neg_mem _ hd)
      apply freeLiAtLeast_mono (d := d + n + 1) (e :=
        (d - (-((n : ℤ)) - 1 - p - 1).toNat) + (-p - 1).toNat) (by omega)
      exact hb
  · rw [Wak.bgFam, if_neg hp, Module.End.mul_apply, Wak.Bet_of_nonneg (by omega),
      bgClassicalFam, if_neg (by omega), sub_zero]
    have hd := cD_mem_freeLiAtLeast (j := p) (by omega) hP
    have hq : -((n : ℤ)) - 1 - p ≤ 0 := by omega
    rw [Wak.Gam_of_nonpos hq, Wak.mulL_apply]
    have hc := cV_mul_mem_freeLiAtLeast (j := -(-((n : ℤ)) - 1 - p)) (by omega) hd
    apply freeLiAtLeast_mono (d := d + n + 1) (e :=
      (d - p.toNat) + (-(-((n : ℤ)) - 1 - p)).toNat) (by omega)
    exact hc

/-- The negative `:βγ:` mode differs from multiplication by its classical vacuum symbol by one
strict filtration step. -/
theorem BG_sub_classical_mem_freeLiAtLeast (n : ℕ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.BG (-((n : ℤ)) - 1) P - bgVac n * P ∈ freeLiAtLeast (d + n + 1) := by
  have hbg := Wak.bgFam_locFin (-((n : ℤ)) - 1) P
  have hcl : (fun p : ℤ => bgClassicalFam n p P).HasFiniteSupport :=
    bgClassicalFam_support_finite n P
  rw [Wak.BG, Wak.opSum_apply (Wak.bgFam_locFin (-((n : ℤ)) - 1)) P,
    ← finsum_bgClassicalFam n P, ← finsum_sub_distrib hbg hcl]
  exact QuotVOA.finsum_mem_submodule _ _ fun p =>
    bgFam_sub_classical_mem_freeLiAtLeast n p hP

/-- Every summand of `:aγ:_{-n-1}` raises the minimum free-Li weight by at least `n`. -/
theorem agFam_neg_mem_freeLiAtLeast (k : ℂ) (n : ℕ) (p : ℤ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.agFam k (-((n : ℤ)) - 1) p P ∈ freeLiAtLeast (d + n) := by
  by_cases hp : p ≤ -1
  · rw [Wak.agFam, if_pos hp, Module.End.mul_apply]
    by_cases hq : -((n : ℤ)) - 1 - p ≤ 0
    · rw [Wak.Gam_of_nonpos hq, Wak.mulL_apply, Wak.Aos_of_neg k hp, Wak.mulL_apply]
      have hc := cV_mul_mem_freeLiAtLeast (j := -(-((n : ℤ)) - 1 - p)) (by omega) hP
      have ha := aV_mul_mem_freeLiAtLeast (i := -p) (by omega) hc
      have hweight : (d + (-(-((n : ℤ)) - 1 - p)).toNat) + (-p - 1).toNat = d + n := by
        omega
      rwa [hweight] at ha
    · rw [Wak.Gam_of_pos (by omega), Wak.Aos_of_neg k hp, Wak.mulL_apply,
        LinearMap.neg_apply]
      have hd := bD_mem_freeLiAtLeast (i := -((n : ℤ)) - 1 - p) (by omega) hP
      have ha := aV_mul_mem_freeLiAtLeast (i := -p) (by omega)
        (Submodule.neg_mem _ hd)
      apply freeLiAtLeast_mono (d := d + n) (e :=
        (d - (-((n : ℤ)) - 1 - p - 1).toNat) + (-p - 1).toNat) (by omega)
      exact ha
  · rw [Wak.agFam, if_neg hp, Module.End.mul_apply, Wak.Aos_of_nonneg k (by omega),
      LinearMap.smul_apply]
    by_cases hp0 : p = 0
    · subst hp0
      rw [Wak.aD_of_nonpos (by omega), LinearMap.zero_apply, smul_zero, map_zero]
      exact Submodule.zero_mem _
    · have hp1 : 1 ≤ p := by omega
      have hd := aD_mem_freeLiAtLeast hp1 hP
      have hq : -((n : ℤ)) - 1 - p ≤ 0 := by omega
      rw [Wak.Gam_of_nonpos hq, Wak.mulL_apply]
      have hs : ((2 * (k + 2)) * (p : ℂ)) • Wak.aD p P ∈
          freeLiAtLeast (d - (p - 1).toNat) := Submodule.smul_mem _ _ hd
      have hc := cV_mul_mem_freeLiAtLeast (j := -(-((n : ℤ)) - 1 - p)) (by omega)
        hs
      apply freeLiAtLeast_mono (d := d + n) (e :=
        (d - (p - 1).toNat) + (-(-((n : ℤ)) - 1 - p)).toNat) (by omega)
      exact hc

/-- The full negative `:aγ:` mode satisfies the minimum free-Li bound. -/
theorem AG_neg_mem_freeLiAtLeast (k : ℂ) (n : ℕ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.AG k (-((n : ℤ)) - 1) P ∈ freeLiAtLeast (d + n) := by
  rw [Wak.AG, Wak.opSum_apply (Wak.agFam_locFin k (-((n : ℤ)) - 1)) P]
  exact QuotVOA.finsum_mem_submodule _ _ fun p => agFam_neg_mem_freeLiAtLeast k n p hP

/-- Pure-creation summand of the negative `:aγ:` mode on an arbitrary input. -/
def agClassicalFam (n : ℕ) (p : ℤ) (P : Wak.WakFock) : Wak.WakFock :=
  if -((n : ℤ)) - 1 ≤ p ∧ p ≤ -1 then
    (Wak.aV (-p) * Wak.cV ((n : ℤ) + 1 + p)) * P else 0

theorem agClassicalFam_support_finite (n : ℕ) (P : Wak.WakFock) :
    (Function.support fun p : ℤ => agClassicalFam n p P).Finite := by
  apply Set.Finite.subset (Finset.finite_toSet (Finset.Icc (-((n : ℤ)) - 1) (-1)))
  intro p hp
  simp only [Function.mem_support, Finset.coe_Icc, Set.mem_Icc] at hp ⊢
  by_contra hc
  exact hp (by rw [agClassicalFam, if_neg hc])

theorem finsum_agClassicalFam (n : ℕ) (P : Wak.WakFock) :
    (∑ᶠ p : ℤ, agClassicalFam n p P) = agVac n * P := by
  rw [finsum_eq_finsetSum_of_support_subset _
    (s := Finset.Icc (-((n : ℤ)) - 1) (-1)) (by
      intro p hp
      simp only [Function.mem_support, Finset.coe_Icc, Set.mem_Icc] at hp ⊢
      by_contra hc
      exact hp (by rw [agClassicalFam, if_neg hc]))]
  · rw [agVac, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p hp => by
      rw [agClassicalFam, if_pos (by simpa only [Finset.mem_Icc] using hp)]

/-- Every non-classical `:aγ:` summand is one step deeper in minimum free-Li weight. -/
theorem agFam_sub_classical_mem_freeLiAtLeast (k : ℂ) (n : ℕ) (p : ℤ) {d : ℕ}
    {P : Wak.WakFock} (hP : P ∈ freeLiAtLeast d) :
    Wak.agFam k (-((n : ℤ)) - 1) p P - agClassicalFam n p P ∈
      freeLiAtLeast (d + n + 1) := by
  by_cases hp : p ≤ -1
  · rw [Wak.agFam, if_pos hp, Module.End.mul_apply]
    by_cases hq : -((n : ℤ)) - 1 - p ≤ 0
    · rw [Wak.Gam_of_nonpos hq, Wak.mulL_apply, Wak.Aos_of_neg k hp, Wak.mulL_apply,
        agClassicalFam, if_pos (by omega)]
      have hcarg : -(-((n : ℤ)) - 1 - p) = (n : ℤ) + 1 + p := by ring
      rw [hcarg]
      ring_nf
      exact Submodule.zero_mem _
    · rw [Wak.Gam_of_pos (by omega), Wak.Aos_of_neg k hp, Wak.mulL_apply,
        LinearMap.neg_apply, agClassicalFam, if_neg (by omega), sub_zero]
      have hd := bD_mem_freeLiAtLeast (i := -((n : ℤ)) - 1 - p) (by omega) hP
      have ha := aV_mul_mem_freeLiAtLeast (i := -p) (by omega)
        (Submodule.neg_mem _ hd)
      apply freeLiAtLeast_mono (d := d + n + 1) (e :=
        (d - (-((n : ℤ)) - 1 - p - 1).toNat) + (-p - 1).toNat) (by omega)
      exact ha
  · rw [Wak.agFam, if_neg hp, Module.End.mul_apply, Wak.Aos_of_nonneg k (by omega),
      LinearMap.smul_apply, agClassicalFam, if_neg (by omega), sub_zero]
    by_cases hp0 : p = 0
    · subst hp0
      rw [Wak.aD_of_nonpos (by omega), LinearMap.zero_apply, smul_zero, map_zero]
      exact Submodule.zero_mem _
    · have hp1 : 1 ≤ p := by omega
      have hd := aD_mem_freeLiAtLeast hp1 hP
      have hq : -((n : ℤ)) - 1 - p ≤ 0 := by omega
      rw [Wak.Gam_of_nonpos hq, Wak.mulL_apply]
      have hs : ((2 * (k + 2)) * (p : ℂ)) • Wak.aD p P ∈
          freeLiAtLeast (d - (p - 1).toNat) := Submodule.smul_mem _ _ hd
      have hc := cV_mul_mem_freeLiAtLeast (j := -(-((n : ℤ)) - 1 - p)) (by omega) hs
      apply freeLiAtLeast_mono (d := d + n + 1) (e :=
        (d - (p - 1).toNat) + (-(-((n : ℤ)) - 1 - p)).toNat) (by omega)
      exact hc

/-- The negative `:aγ:` mode has its vacuum classical multiplication as minimum symbol. -/
theorem AG_sub_classical_mem_freeLiAtLeast (k : ℂ) (n : ℕ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.AG k (-((n : ℤ)) - 1) P - agVac n * P ∈ freeLiAtLeast (d + n + 1) := by
  have hag := Wak.agFam_locFin k (-((n : ℤ)) - 1) P
  have hcl : (fun p : ℤ => agClassicalFam n p P).HasFiniteSupport :=
    agClassicalFam_support_finite n P
  rw [Wak.AG, Wak.opSum_apply (Wak.agFam_locFin k (-((n : ℤ)) - 1)) P,
    ← finsum_agClassicalFam n P, ← finsum_sub_distrib hag hcl]
  exact QuotVOA.finsum_mem_submodule _ _ fun p =>
    agFam_sub_classical_mem_freeLiAtLeast k n p hP

/-- Every summand of `:γγ:_{-r}` raises the minimum free-Li weight by at least `r`. -/
theorem ggFam_nonpos_mem_freeLiAtLeast (r : ℕ) (q : ℤ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.ggFam (-(r : ℤ)) q P ∈ freeLiAtLeast (d + r) := by
  by_cases hq : q ≤ 0
  · rw [Wak.ggFam, if_pos hq, Module.End.mul_apply]
    by_cases ht : -(r : ℤ) - q ≤ 0
    · rw [Wak.Gam_of_nonpos (n := -(r : ℤ) - q) ht,
        Wak.Gam_of_nonpos (n := q) hq, Wak.mulL_apply, Wak.mulL_apply]
      have hc₁ := cV_mul_mem_freeLiAtLeast (j := -(-(r : ℤ) - q)) (by omega) hP
      have hc₂ := cV_mul_mem_freeLiAtLeast (j := -q) (by omega) hc₁
      have hweight : (d + (-(-(r : ℤ) - q)).toNat) + (-q).toNat = d + r := by omega
      rwa [hweight] at hc₂
    · rw [Wak.Gam_of_pos (n := -(r : ℤ) - q) (by omega),
        Wak.Gam_of_nonpos (n := q) hq, LinearMap.neg_apply, Wak.mulL_apply]
      have hd := bD_mem_freeLiAtLeast (i := -(r : ℤ) - q) (by omega) hP
      have hc := cV_mul_mem_freeLiAtLeast (j := -q) (by omega) (Submodule.neg_mem _ hd)
      apply freeLiAtLeast_mono (d := d + r) (e :=
        (d - (-(r : ℤ) - q - 1).toNat) + (-q).toNat) (by omega)
      exact hc
  · rw [Wak.ggFam, if_neg hq, Module.End.mul_apply,
      Wak.Gam_of_pos (n := q) (by omega), LinearMap.neg_apply]
    have hd := bD_mem_freeLiAtLeast (i := q) (by omega) hP
    have ht : -(r : ℤ) - q ≤ 0 := by omega
    rw [Wak.Gam_of_nonpos (n := -(r : ℤ) - q) ht, Wak.mulL_apply]
    have hc := cV_mul_mem_freeLiAtLeast (j := -(-(r : ℤ) - q)) (by omega)
      (Submodule.neg_mem _ hd)
    apply freeLiAtLeast_mono (d := d + r) (e :=
      (d - (q - 1).toNat) + (-(-(r : ℤ) - q)).toNat) (by omega)
    exact hc

/-- The full nonpositive `:γγ:` mode satisfies the minimum free-Li bound. -/
theorem GG_nonpos_mem_freeLiAtLeast (r : ℕ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.GG (-(r : ℤ)) P ∈ freeLiAtLeast (d + r) := by
  rw [Wak.GG, Wak.opSum_apply (Wak.ggFam_locFin (-(r : ℤ))) P]
  exact QuotVOA.finsum_mem_submodule _ _ fun q => ggFam_nonpos_mem_freeLiAtLeast r q hP

/-- Pure-creation summand of `:γγ:_{-r}` on an arbitrary input. -/
def ggClassicalFam (r : ℕ) (q : ℤ) (P : Wak.WakFock) : Wak.WakFock :=
  if -(r : ℤ) ≤ q ∧ q ≤ 0 then
    (Wak.cV (-q) * Wak.cV ((r : ℤ) + q)) * P else 0

theorem ggClassicalFam_support_finite (r : ℕ) (P : Wak.WakFock) :
    (Function.support fun q : ℤ => ggClassicalFam r q P).Finite := by
  apply Set.Finite.subset (Finset.finite_toSet (Finset.Icc (-(r : ℤ)) 0))
  intro q hq
  simp only [Function.mem_support, Finset.coe_Icc, Set.mem_Icc] at hq ⊢
  by_contra hc
  exact hq (by rw [ggClassicalFam, if_neg hc])

theorem finsum_ggClassicalFam (r : ℕ) (P : Wak.WakFock) :
    (∑ᶠ q : ℤ, ggClassicalFam r q P) = ggVac r * P := by
  rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.Icc (-(r : ℤ)) 0) (by
    intro q hq
    simp only [Function.mem_support, Finset.coe_Icc, Set.mem_Icc] at hq ⊢
    by_contra hc
    exact hq (by rw [ggClassicalFam, if_neg hc]))]
  · rw [ggVac, Finset.sum_mul]
    exact Finset.sum_congr rfl fun q hq => by
      rw [ggClassicalFam, if_pos (by simpa only [Finset.mem_Icc] using hq)]

/-- Every non-classical summand of `:γγ:_{-r}` is one free-Li step deeper. -/
theorem ggFam_sub_classical_mem_freeLiAtLeast (r : ℕ) (q : ℤ) {d : ℕ}
    {P : Wak.WakFock} (hP : P ∈ freeLiAtLeast d) :
    Wak.ggFam (-(r : ℤ)) q P - ggClassicalFam r q P ∈
      freeLiAtLeast (d + r + 1) := by
  by_cases hq : q ≤ 0
  · rw [Wak.ggFam, if_pos hq, Module.End.mul_apply]
    by_cases ht : -(r : ℤ) - q ≤ 0
    · rw [Wak.Gam_of_nonpos (n := -(r : ℤ) - q) ht,
        Wak.Gam_of_nonpos (n := q) hq, Wak.mulL_apply, Wak.mulL_apply,
        ggClassicalFam, if_pos (by omega)]
      have hcarg : -(-(r : ℤ) - q) = (r : ℤ) + q := by ring
      rw [hcarg]
      ring_nf
      exact Submodule.zero_mem _
    · rw [Wak.Gam_of_pos (n := -(r : ℤ) - q) (by omega),
        Wak.Gam_of_nonpos (n := q) hq, LinearMap.neg_apply, Wak.mulL_apply,
        ggClassicalFam, if_neg (by omega), sub_zero]
      have hd := bD_mem_freeLiAtLeast (i := -(r : ℤ) - q) (by omega) hP
      have hc := cV_mul_mem_freeLiAtLeast (j := -q) (by omega) (Submodule.neg_mem _ hd)
      apply freeLiAtLeast_mono (d := d + r + 1) (e :=
        (d - (-(r : ℤ) - q - 1).toNat) + (-q).toNat) (by omega)
      exact hc
  · rw [Wak.ggFam, if_neg hq, Module.End.mul_apply,
      Wak.Gam_of_pos (n := q) (by omega), LinearMap.neg_apply,
      ggClassicalFam, if_neg (by omega), sub_zero]
    have hd := bD_mem_freeLiAtLeast (i := q) (by omega) hP
    have ht : -(r : ℤ) - q ≤ 0 := by omega
    rw [Wak.Gam_of_nonpos (n := -(r : ℤ) - q) ht, Wak.mulL_apply]
    have hc := cV_mul_mem_freeLiAtLeast (j := -(-(r : ℤ) - q)) (by omega)
      (Submodule.neg_mem _ hd)
    apply freeLiAtLeast_mono (d := d + r + 1) (e :=
      (d - (q - 1).toNat) + (-(-(r : ℤ) - q)).toNat) (by omega)
    exact hc

/-- A nonpositive `:γγ:` mode has its vacuum classical multiplication as minimum symbol. -/
theorem GG_sub_classical_mem_freeLiAtLeast (r : ℕ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.GG (-(r : ℤ)) P - ggVac r * P ∈ freeLiAtLeast (d + r + 1) := by
  have hgg := Wak.ggFam_locFin (-(r : ℤ)) P
  have hcl : (fun q : ℤ => ggClassicalFam r q P).HasFiniteSupport :=
    ggClassicalFam_support_finite r P
  rw [Wak.GG, Wak.opSum_apply (Wak.ggFam_locFin (-(r : ℤ))) P,
    ← finsum_ggClassicalFam r P, ← finsum_sub_distrib hgg hcl]
  exact QuotVOA.finsum_mem_submodule _ _ fun q =>
    ggFam_sub_classical_mem_freeLiAtLeast r q hP

/-- Every summand of a positive `:γγ:_s` mode lowers the minimum free-Li weight by at most `s`.
This is the estimate needed for the far-negative outer `β` terms in `BGG`. -/
theorem ggFam_pos_mem_freeLiAtLeast (s : ℕ) (hs : 1 ≤ s) (q : ℤ)
    {d : ℕ} {P : Wak.WakFock} (hP : P ∈ freeLiAtLeast d) :
    Wak.ggFam (s : ℤ) q P ∈ freeLiAtLeast (d + 1 - s) := by
  by_cases hq : q ≤ 0
  · rw [Wak.ggFam, if_pos hq, Module.End.mul_apply,
      Wak.Gam_of_pos (n := (s : ℤ) - q) (by omega),
      Wak.Gam_of_nonpos (n := q) hq, LinearMap.neg_apply, Wak.mulL_apply]
    have hd := bD_mem_freeLiAtLeast (i := (s : ℤ) - q) (by omega) hP
    have hc := cV_mul_mem_freeLiAtLeast (j := -q) (by omega) (Submodule.neg_mem _ hd)
    apply freeLiAtLeast_mono (d := d + 1 - s) (e :=
      (d - ((s : ℤ) - q - 1).toNat) + (-q).toNat) (by omega)
    exact hc
  · rw [Wak.ggFam, if_neg hq, Module.End.mul_apply,
      Wak.Gam_of_pos (n := q) (by omega), LinearMap.neg_apply]
    have hdq := bD_mem_freeLiAtLeast (i := q) (by omega) hP
    by_cases ht : (s : ℤ) - q ≤ 0
    · rw [Wak.Gam_of_nonpos (n := (s : ℤ) - q) ht, Wak.mulL_apply]
      have hc := cV_mul_mem_freeLiAtLeast (j := -((s : ℤ) - q)) (by omega)
        (Submodule.neg_mem _ hdq)
      apply freeLiAtLeast_mono (d := d + 1 - s) (e :=
        (d - (q - 1).toNat) + (-((s : ℤ) - q)).toNat) (by omega)
      exact hc
    · rw [Wak.Gam_of_pos (n := (s : ℤ) - q) (by omega), LinearMap.neg_apply]
      have hdt := bD_mem_freeLiAtLeast (i := (s : ℤ) - q) (by omega)
        (Submodule.neg_mem _ hdq)
      apply freeLiAtLeast_mono (d := d + 1 - s) (e :=
        (d - (q - 1).toNat) - ((s : ℤ) - q - 1).toNat) (by omega)
      exact Submodule.neg_mem _ hdt

/-- The full positive `:γγ:` mode satisfies the minimum free-Li bound. -/
theorem GG_pos_mem_freeLiAtLeast (s : ℕ) (hs : 1 ≤ s) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.GG (s : ℤ) P ∈ freeLiAtLeast (d + 1 - s) := by
  rw [Wak.GG, Wak.opSum_apply (Wak.ggFam_locFin (s : ℤ)) P]
  exact QuotVOA.finsum_mem_submodule _ _ fun q => ggFam_pos_mem_freeLiAtLeast s hs q hP

/-- Every summand of `:βγγ:_{-n-1}` raises the minimum free-Li weight by at least `n`. -/
theorem bggFam_neg_mem_freeLiAtLeast (n : ℕ) (p : ℤ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.bggFam (-((n : ℤ)) - 1) p P ∈ freeLiAtLeast (d + n) := by
  by_cases hp : p ≤ -1
  · rw [Wak.bggFam, if_pos hp, Module.End.mul_apply, Wak.Bet_of_neg hp, Wak.mulL_apply]
    by_cases hs : -((n : ℤ)) - 1 - p ≤ 0
    · let r : ℕ := (-(-((n : ℤ)) - 1 - p)).toNat
      have hmode : -((n : ℤ)) - 1 - p = -(r : ℤ) := by
        dsimp [r]
        rw [Int.toNat_of_nonneg (by omega)]
        ring
      have hgg : Wak.GG (-((n : ℤ)) - 1 - p) P ∈ freeLiAtLeast (d + r) := by
        rw [hmode]
        exact GG_nonpos_mem_freeLiAtLeast r hP
      have hb := bV_mul_mem_freeLiAtLeast (i := -p) (by omega) hgg
      have hweight : (d + r) + (-p - 1).toNat = d + n := by
        dsimp [r]
        omega
      rwa [hweight] at hb
    · let s : ℕ := (-((n : ℤ)) - 1 - p).toNat
      have hspos : 1 ≤ s := by dsimp [s]; omega
      have hmode : -((n : ℤ)) - 1 - p = (s : ℤ) := by
        dsimp [s]
        rw [Int.toNat_of_nonneg (by omega)]
      have hgg : Wak.GG (-((n : ℤ)) - 1 - p) P ∈ freeLiAtLeast (d + 1 - s) := by
        rw [hmode]
        exact GG_pos_mem_freeLiAtLeast s hspos hP
      have hb := bV_mul_mem_freeLiAtLeast (i := -p) (by omega) hgg
      apply freeLiAtLeast_mono (d := d + n) (e := (d + 1 - s) + (-p - 1).toNat) (by
        dsimp [s]
        omega)
      exact hb
  · rw [Wak.bggFam, if_neg hp, Module.End.mul_apply, Wak.Bet_of_nonneg (by omega)]
    have hd := cD_mem_freeLiAtLeast (j := p) (by omega) hP
    let r : ℕ := (-(-((n : ℤ)) - 1 - p)).toNat
    have hmode : -((n : ℤ)) - 1 - p = -(r : ℤ) := by
      dsimp [r]
      rw [Int.toNat_of_nonneg (by omega)]
      ring
    have hgg : Wak.GG (-((n : ℤ)) - 1 - p) (Wak.cD p P) ∈
        freeLiAtLeast ((d - p.toNat) + r) := by
      rw [hmode]
      exact GG_nonpos_mem_freeLiAtLeast r hd
    apply freeLiAtLeast_mono (d := d + n) (e := (d - p.toNat) + r) (by
      dsimp [r]
      omega)
    exact hgg

/-- The full negative `:βγγ:` mode satisfies the minimum free-Li bound. -/
theorem BGG_neg_mem_freeLiAtLeast (n : ℕ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.BGG (-((n : ℤ)) - 1) P ∈ freeLiAtLeast (d + n) := by
  rw [Wak.BGG, Wak.opSum_apply (Wak.bggFam_locFin (-((n : ℤ)) - 1)) P]
  exact QuotVOA.finsum_mem_submodule _ _ fun p => bggFam_neg_mem_freeLiAtLeast n p hP

/-- Pure-creation summand of `:βγγ:_{-n-1}` on an arbitrary input. -/
def bggClassicalFam (n : ℕ) (p : ℤ) (P : Wak.WakFock) : Wak.WakFock :=
  if -((n : ℤ)) - 1 ≤ p ∧ p ≤ -1 then
    (Wak.bV (-p) * ggVac (((n : ℤ) + 1 + p).toNat)) * P else 0

theorem bggClassicalFam_support_finite (n : ℕ) (P : Wak.WakFock) :
    (Function.support fun p : ℤ => bggClassicalFam n p P).Finite := by
  apply Set.Finite.subset (Finset.finite_toSet (Finset.Icc (-((n : ℤ)) - 1) (-1)))
  intro p hp
  simp only [Function.mem_support, Finset.coe_Icc, Set.mem_Icc] at hp ⊢
  by_contra hc
  exact hp (by rw [bggClassicalFam, if_neg hc])

theorem finsum_bggClassicalFam (n : ℕ) (P : Wak.WakFock) :
    (∑ᶠ p : ℤ, bggClassicalFam n p P) = bggVac n * P := by
  rw [finsum_eq_finsetSum_of_support_subset _
    (s := Finset.Icc (-((n : ℤ)) - 1) (-1)) (by
      intro p hp
      simp only [Function.mem_support, Finset.coe_Icc, Set.mem_Icc] at hp ⊢
      by_contra hc
      exact hp (by rw [bggClassicalFam, if_neg hc]))]
  · rw [bggVac, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p hp => by
      rw [bggClassicalFam, if_pos (by simpa only [Finset.mem_Icc] using hp)]

/-- Every non-classical summand of `:βγγ:_{-n-1}` is one free-Li step deeper. -/
theorem bggFam_sub_classical_mem_freeLiAtLeast (n : ℕ) (p : ℤ) {d : ℕ}
    {P : Wak.WakFock} (hP : P ∈ freeLiAtLeast d) :
    Wak.bggFam (-((n : ℤ)) - 1) p P - bggClassicalFam n p P ∈
      freeLiAtLeast (d + n + 1) := by
  by_cases hp : p ≤ -1
  · rw [Wak.bggFam, if_pos hp, Module.End.mul_apply, Wak.Bet_of_neg hp, Wak.mulL_apply]
    by_cases hs : -((n : ℤ)) - 1 - p ≤ 0
    · let r : ℕ := (-(-((n : ℤ)) - 1 - p)).toNat
      have hmode : -((n : ℤ)) - 1 - p = -(r : ℤ) := by
        dsimp [r]
        rw [Int.toNat_of_nonneg (by omega)]
        ring
      rw [bggClassicalFam, if_pos (by omega)]
      have hindex : ((n : ℤ) + 1 + p).toNat = r := by
        dsimp [r]
        congr 1
        ring
      rw [hindex]
      have hgg : Wak.GG (-((n : ℤ)) - 1 - p) P - ggVac r * P ∈
          freeLiAtLeast (d + r + 1) := by
        rw [hmode]
        exact GG_sub_classical_mem_freeLiAtLeast r hP
      have hrearrange : Wak.bV (-p) * Wak.GG (-((n : ℤ)) - 1 - p) P -
          Wak.bV (-p) * ggVac r * P =
          Wak.bV (-p) * (Wak.GG (-((n : ℤ)) - 1 - p) P - ggVac r * P) := by ring
      rw [hrearrange]
      have hb := bV_mul_mem_freeLiAtLeast (i := -p) (by omega) hgg
      have hweight : (d + r + 1) + (-p - 1).toNat = d + n + 1 := by
        dsimp [r]
        omega
      rwa [hweight] at hb
    · rw [bggClassicalFam, if_neg (by omega), sub_zero]
      let s : ℕ := (-((n : ℤ)) - 1 - p).toNat
      have hspos : 1 ≤ s := by dsimp [s]; omega
      have hmode : -((n : ℤ)) - 1 - p = (s : ℤ) := by
        dsimp [s]
        rw [Int.toNat_of_nonneg (by omega)]
      have hgg : Wak.GG (-((n : ℤ)) - 1 - p) P ∈ freeLiAtLeast (d + 1 - s) := by
        rw [hmode]
        exact GG_pos_mem_freeLiAtLeast s hspos hP
      have hb := bV_mul_mem_freeLiAtLeast (i := -p) (by omega) hgg
      apply freeLiAtLeast_mono (d := d + n + 1) (e :=
        (d + 1 - s) + (-p - 1).toNat) (by
          dsimp [s]
          omega)
      exact hb
  · rw [Wak.bggFam, if_neg hp, Module.End.mul_apply, Wak.Bet_of_nonneg (by omega),
      bggClassicalFam, if_neg (by omega), sub_zero]
    have hd := cD_mem_freeLiAtLeast (j := p) (by omega) hP
    let r : ℕ := (-(-((n : ℤ)) - 1 - p)).toNat
    have hmode : -((n : ℤ)) - 1 - p = -(r : ℤ) := by
      dsimp [r]
      rw [Int.toNat_of_nonneg (by omega)]
      ring
    have hgg : Wak.GG (-((n : ℤ)) - 1 - p) (Wak.cD p P) ∈
        freeLiAtLeast ((d - p.toNat) + r) := by
      rw [hmode]
      exact GG_nonpos_mem_freeLiAtLeast r hd
    apply freeLiAtLeast_mono (d := d + n + 1) (e := (d - p.toNat) + r) (by
      dsimp [r]
      omega)
    exact hgg

/-- The negative `:βγγ:` mode has its vacuum classical multiplication as minimum symbol. -/
theorem BGG_sub_classical_mem_freeLiAtLeast (n : ℕ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.BGG (-((n : ℤ)) - 1) P - bggVac n * P ∈ freeLiAtLeast (d + n + 1) := by
  have hbgg := Wak.bggFam_locFin (-((n : ℤ)) - 1) P
  have hcl : (fun p : ℤ => bggClassicalFam n p P).HasFiniteSupport :=
    bggClassicalFam_support_finite n P
  rw [Wak.BGG, Wak.opSum_apply (Wak.bggFam_locFin (-((n : ℤ)) - 1)) P,
    ← finsum_bggClassicalFam n P, ← finsum_sub_distrib hbgg hcl]
  exact QuotVOA.finsum_mem_submodule _ _ fun p =>
    bggFam_sub_classical_mem_freeLiAtLeast n p hP

/-- A negative Wakimoto `e` current raises minimum free-Li weight by at least its depth. -/
theorem Ecur_neg_mem_freeLiAtLeast (n : ℕ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.Ecur (-((n : ℤ)) - 1) P ∈ freeLiAtLeast (d + n) := by
  rw [Wak.Ecur, Wak.Bet_of_neg (by omega), Wak.mulL_apply]
  rw [show -(-((n : ℤ)) - 1) = (n : ℤ) + 1 by ring]
  have hb := bV_mul_mem_freeLiAtLeast (i := (n : ℤ) + 1) (by omega) hP
  have hindex : ((n : ℤ) + 1 - 1).toNat = n := by omega
  rwa [hindex] at hb

/-- A negative Wakimoto `h` current raises minimum free-Li weight by at least its depth. -/
theorem Hcur_neg_mem_freeLiAtLeast (k : ℂ) (n : ℕ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.Hcur k (-((n : ℤ)) - 1) P ∈ freeLiAtLeast (d + n) := by
  rw [Wak.Hcur, LinearMap.add_apply, LinearMap.smul_apply,
    Wak.Aos_of_neg k (by omega), Wak.mulL_apply]
  rw [show -(-((n : ℤ)) - 1) = (n : ℤ) + 1 by ring]
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ (BG_neg_mem_freeLiAtLeast n hP)
  · have ha := aV_mul_mem_freeLiAtLeast (i := (n : ℤ) + 1) (by omega) hP
    have hindex : ((n : ℤ) + 1 - 1).toNat = n := by omega
    rwa [hindex] at ha

/-- A negative Wakimoto `f` current raises minimum free-Li weight by at least its depth. -/
theorem Fcur_neg_mem_freeLiAtLeast (k : ℂ) (n : ℕ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.Fcur k (-((n : ℤ)) - 1) P ∈ freeLiAtLeast (d + n) := by
  rw [Wak.Fcur, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.smul_apply, Wak.Gam_of_nonpos (by omega), Wak.mulL_apply]
  rw [show -(-((n : ℤ)) - 1) = (n : ℤ) + 1 by ring]
  apply Submodule.sub_mem
  · exact Submodule.add_mem _ (Submodule.neg_mem _ (BGG_neg_mem_freeLiAtLeast n hP))
      (AG_neg_mem_freeLiAtLeast k n hP)
  · have hc := cV_mul_mem_freeLiAtLeast (j := (n : ℤ) + 1) (by omega) hP
    apply Submodule.smul_mem
    apply freeLiAtLeast_mono (d := d + n) (e := d + ((n : ℤ) + 1).toNat) (by omega)
    exact hc

/-- Uniform negative-current minimum free-Li bound for the three Chevalley colours. -/
theorem Jw_neg_mem_freeLiAtLeast (k : ℂ) (a : Fin 3) (n : ℕ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.Jw k a (-((n : ℤ)) - 1) P ∈ freeLiAtLeast (d + n) := by
  fin_cases a
  · change Wak.Jw k 0 (-((n : ℤ)) - 1) P ∈ freeLiAtLeast (d + n)
    rw [Wak.Jw_E]
    exact Ecur_neg_mem_freeLiAtLeast n hP
  · change Wak.Jw k 1 (-((n : ℤ)) - 1) P ∈ freeLiAtLeast (d + n)
    rw [Wak.Jw_F]
    exact Fcur_neg_mem_freeLiAtLeast k n hP
  · change Wak.Jw k 2 (-((n : ℤ)) - 1) P ∈ freeLiAtLeast (d + n)
    rw [Wak.Jw_H]
    exact Hcur_neg_mem_freeLiAtLeast k n hP

/-- Total Li depth of a negative-current word. -/
def wordFreeLiDegree (l : List (Fin 3 × ℕ)) : ℕ := (l.map Prod.snd).sum

@[simp] theorem wordFreeLiDegree_nil : wordFreeLiDegree [] = 0 := rfl

@[simp] theorem wordFreeLiDegree_cons (a : Fin 3) (n : ℕ) (l : List (Fin 3 × ℕ)) :
    wordFreeLiDegree ((a, n) :: l) = n + wordFreeLiDegree l := rfl

/-- Every iterated negative-current Wakimoto state has minimum free-Li weight at least the sum of
its current depths. -/
theorem wakimotoWordState_mem_freeLiAtLeast (k : ℂ) : ∀ l : List (Fin 3 × ℕ),
    wakimotoWordState k l ∈ freeLiAtLeast (wordFreeLiDegree l)
  | [] => mem_freeLiAtLeast_zero 1
  | (a, n) :: l => by
      rw [wakimotoWordState, wordFreeLiDegree_cons]
      have h := Jw_neg_mem_freeLiAtLeast k a n (wakimotoWordState_mem_freeLiAtLeast k l)
      rwa [add_comm] at h

/-- Membership in `freeLiAtLeast d` kills every weighted component below `d`. -/
theorem weightedComponent_eq_zero_of_mem_freeLiAtLeast {d r : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) (hr : r < d) :
    MvPolynomial.weightedHomogeneousComponent freeLiWeight r P = 0 := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨e, he, rfl⟩ := hP
      have hhom := MvPolynomial.isWeightedHomogeneous_monomial
        (R := ℂ) (w := freeLiWeight) e (1 : ℂ) rfl
      exact hhom.weightedHomogeneousComponent_ne r (by omega)
  | zero => exact map_zero _
  | add P Q _ _ hP hQ => rw [map_add, hP, hQ, add_zero]
  | smul c P _ hP => rw [map_smul, hP, smul_zero]

/-- Concrete lower-vanishing half of the ordered-word leading-component theorem. -/
theorem weightedComponent_wakimotoWordState_eq_zero (k : ℂ) (l : List (Fin 3 × ℕ)) (r : ℕ)
    (hr : r < wordFreeLiDegree l) :
    MvPolynomial.weightedHomogeneousComponent freeLiWeight r (wakimotoWordState k l) = 0 :=
  weightedComponent_eq_zero_of_mem_freeLiAtLeast
    (wakimotoWordState_mem_freeLiAtLeast k l) hr

private theorem bgFam_one_neg (n : ℕ) (p : ℤ) :
    Wak.bgFam (-((n : ℤ)) - 1) p (1 : Wak.WakFock) =
      if -((n : ℤ)) - 1 ≤ p ∧ p ≤ -1 then
        Wak.bV (-p) * Wak.cV ((n : ℤ) + 1 + p) else 0 := by
  by_cases hp : p ≤ -1
  · rw [Wak.bgFam, if_pos hp, Module.End.mul_apply]
    by_cases hlow : -((n : ℤ)) - 1 ≤ p
    · rw [if_pos ⟨hlow, hp⟩, Wak.Gam_one_nonpos (by omega), Wak.Bet_of_neg hp,
        Wak.mulL_apply]
      congr 2 <;> ring
    · rw [if_neg (by omega), Wak.Gam_one (by omega), map_zero]
  · rw [Wak.bgFam, if_neg hp, if_neg (by omega), Module.End.mul_apply,
      Wak.Bet_one (by omega), map_zero]

private theorem agFam_one_neg (k : ℂ) (n : ℕ) (p : ℤ) :
    Wak.agFam k (-((n : ℤ)) - 1) p (1 : Wak.WakFock) =
      if -((n : ℤ)) - 1 ≤ p ∧ p ≤ -1 then
        Wak.aV (-p) * Wak.cV ((n : ℤ) + 1 + p) else 0 := by
  by_cases hp : p ≤ -1
  · rw [Wak.agFam, if_pos hp, Module.End.mul_apply]
    by_cases hlow : -((n : ℤ)) - 1 ≤ p
    · rw [if_pos ⟨hlow, hp⟩, Wak.Gam_one_nonpos (by omega), Wak.Aos_of_neg k hp,
        Wak.mulL_apply]
      congr 2 <;> ring
    · rw [if_neg (by omega), Wak.Gam_one (by omega), map_zero]
  · rw [Wak.agFam, if_neg hp, if_neg (by omega), Module.End.mul_apply,
      Wak.Aos_one k (by omega), map_zero]

private theorem ggFam_one_nonpos (r : ℕ) (q : ℤ) :
    Wak.ggFam (-(r : ℤ)) q (1 : Wak.WakFock) =
      if -(r : ℤ) ≤ q ∧ q ≤ 0 then
        Wak.cV (-q) * Wak.cV ((r : ℤ) + q) else 0 := by
  by_cases hq : q ≤ 0
  · rw [Wak.ggFam, if_pos hq, Module.End.mul_apply]
    by_cases hlow : -(r : ℤ) ≤ q
    · rw [if_pos ⟨hlow, hq⟩, Wak.Gam_one_nonpos (by omega), Wak.Gam_of_nonpos hq,
        Wak.mulL_apply]
      congr 2 <;> ring
    · rw [if_neg (by omega), Wak.Gam_one (by omega), map_zero]
  · rw [Wak.ggFam, if_neg hq, if_neg (by omega), Module.End.mul_apply,
      Wak.Gam_one (by omega), map_zero]

/-- Exact finite vacuum formula for the negative `:βγ:` mode. -/
theorem BG_one_neg (n : ℕ) : Wak.BG (-((n : ℤ)) - 1) (1 : Wak.WakFock) = bgVac n := by
  rw [Wak.BG, Wak.opSum_apply (Wak.bgFam_locFin (-((n : ℤ)) - 1)) 1,
    finsum_congr (bgFam_one_neg n)]
  have hsupp : Function.support (fun p : ℤ =>
      if -((n : ℤ)) - 1 ≤ p ∧ p ≤ -1 then
        Wak.bV (-p) * Wak.cV ((n : ℤ) + 1 + p) else 0) ⊆
      ↑(Finset.Icc (-((n : ℤ)) - 1) (-1)) := by
    intro p hp
    simp only [Function.mem_support] at hp
    simp only [Finset.coe_Icc, Set.mem_Icc]
    by_contra hc
    exact hp (if_neg hc)
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp, bgVac]
  exact Finset.sum_congr rfl fun p hp => by
    rw [if_pos (by simpa only [Finset.mem_Icc] using hp)]

/-- Exact finite vacuum formula for the negative `:aγ:` mode. -/
theorem AG_one_neg (k : ℂ) (n : ℕ) :
    Wak.AG k (-((n : ℤ)) - 1) (1 : Wak.WakFock) = agVac n := by
  rw [Wak.AG, Wak.opSum_apply (Wak.agFam_locFin k (-((n : ℤ)) - 1)) 1,
    finsum_congr (agFam_one_neg k n)]
  have hsupp : Function.support (fun p : ℤ =>
      if -((n : ℤ)) - 1 ≤ p ∧ p ≤ -1 then
        Wak.aV (-p) * Wak.cV ((n : ℤ) + 1 + p) else 0) ⊆
      ↑(Finset.Icc (-((n : ℤ)) - 1) (-1)) := by
    intro p hp
    simp only [Function.mem_support] at hp
    simp only [Finset.coe_Icc, Set.mem_Icc]
    by_contra hc
    exact hp (if_neg hc)
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp, agVac]
  exact Finset.sum_congr rfl fun p hp => by
    rw [if_pos (by simpa only [Finset.mem_Icc] using hp)]

/-- Exact finite vacuum formula for a nonpositive `:γγ:` mode. -/
theorem GG_one_nonpos (r : ℕ) : Wak.GG (-(r : ℤ)) (1 : Wak.WakFock) = ggVac r := by
  rw [Wak.GG, Wak.opSum_apply (Wak.ggFam_locFin (-(r : ℤ))) 1,
    finsum_congr (ggFam_one_nonpos r)]
  have hsupp : Function.support (fun q : ℤ =>
      if -(r : ℤ) ≤ q ∧ q ≤ 0 then
        Wak.cV (-q) * Wak.cV ((r : ℤ) + q) else 0) ⊆
      ↑(Finset.Icc (-(r : ℤ)) 0) := by
    intro q hq
    simp only [Function.mem_support] at hq
    simp only [Finset.coe_Icc, Set.mem_Icc]
    by_contra hc
    exact hq (if_neg hc)
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp, ggVac]
  exact Finset.sum_congr rfl fun q hq => by
    rw [if_pos (by simpa only [Finset.mem_Icc] using hq)]

private theorem bggFam_one_neg (n : ℕ) (p : ℤ) :
    Wak.bggFam (-((n : ℤ)) - 1) p (1 : Wak.WakFock) =
      if -((n : ℤ)) - 1 ≤ p ∧ p ≤ -1 then
        Wak.bV (-p) * ggVac (((n : ℤ) + 1 + p).toNat) else 0 := by
  by_cases hp : p ≤ -1
  · rw [Wak.bggFam, if_pos hp, Module.End.mul_apply]
    by_cases hlow : -((n : ℤ)) - 1 ≤ p
    · rw [if_pos ⟨hlow, hp⟩, Wak.Bet_of_neg hp, Wak.mulL_apply]
      congr 2
      have hr : (0 : ℤ) ≤ (n : ℤ) + 1 + p := by omega
      rw [← GG_one_nonpos ((n : ℤ) + 1 + p).toNat]
      congr 2
      rw [Int.toNat_of_nonneg hr]
      ring
    · rw [if_neg (by omega), Wak.GG_one (by omega), map_zero]
  · rw [Wak.bggFam, if_neg hp, if_neg (by omega), Module.End.mul_apply,
      Wak.Bet_one (by omega), map_zero]

/-- Exact finite vacuum formula for the negative `:βγγ:` mode. -/
theorem BGG_one_neg (n : ℕ) : Wak.BGG (-((n : ℤ)) - 1) (1 : Wak.WakFock) = bggVac n := by
  rw [Wak.BGG, Wak.opSum_apply (Wak.bggFam_locFin (-((n : ℤ)) - 1)) 1,
    finsum_congr (bggFam_one_neg n)]
  have hsupp : Function.support (fun p : ℤ =>
      if -((n : ℤ)) - 1 ≤ p ∧ p ≤ -1 then
        Wak.bV (-p) * ggVac (((n : ℤ) + 1 + p).toNat) else 0) ⊆
      ↑(Finset.Icc (-((n : ℤ)) - 1) (-1)) := by
    intro p hp
    simp only [Function.mem_support] at hp
    simp only [Finset.coe_Icc, Set.mem_Icc]
    by_contra hc
    exact hp (if_neg hc)
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp, bggVac]
  exact Finset.sum_congr rfl fun p hp => by
    rw [if_pos (by simpa only [Finset.mem_Icc] using hp)]

private theorem bgVac_term_isWeightedHomogeneous (n : ℕ) (p : ℤ)
    (hp : p ∈ Finset.Icc (-((n : ℤ)) - 1) (-1)) :
    MvPolynomial.IsWeightedHomogeneous freeLiWeight
      (Wak.bV (-p) * Wak.cV ((n : ℤ) + 1 + p)) n := by
  simp only [Finset.mem_Icc] at hp
  rw [Wak.bV_of_pos (by omega), Wak.cV_of_nonneg (by omega)]
  have hweight : (-p - 1).toNat + ((n : ℤ) + 1 + p).toNat = n := by omega
  have hb := X_isWeightedHomogeneous_freeLi (0 : Fin 3) (-p - 1).toNat
  have hc := X_isWeightedHomogeneous_freeLi (1 : Fin 3) ((n : ℤ) + 1 + p).toNat
  have hmul := hb.mul hc
  rwa [hweight] at hmul

private theorem agVac_term_isWeightedHomogeneous (n : ℕ) (p : ℤ)
    (hp : p ∈ Finset.Icc (-((n : ℤ)) - 1) (-1)) :
    MvPolynomial.IsWeightedHomogeneous freeLiWeight
      (Wak.aV (-p) * Wak.cV ((n : ℤ) + 1 + p)) n := by
  simp only [Finset.mem_Icc] at hp
  rw [Wak.aV_of_pos (by omega), Wak.cV_of_nonneg (by omega)]
  have hweight : (-p - 1).toNat + ((n : ℤ) + 1 + p).toNat = n := by omega
  have ha := X_isWeightedHomogeneous_freeLi (2 : Fin 3) (-p - 1).toNat
  have hc := X_isWeightedHomogeneous_freeLi (1 : Fin 3) ((n : ℤ) + 1 + p).toNat
  have hmul := ha.mul hc
  rwa [hweight] at hmul

/-- The negative `:βγ:` vacuum convolution has free Li weight `n`. -/
theorem bgVac_isWeightedHomogeneous (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous freeLiWeight (bgVac n) n := by
  rw [bgVac]
  exact MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun p hp =>
    bgVac_term_isWeightedHomogeneous n p hp

/-- The negative `:aγ:` vacuum convolution has free Li weight `n`. -/
theorem agVac_isWeightedHomogeneous (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous freeLiWeight (agVac n) n := by
  rw [agVac]
  exact MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun p hp =>
    agVac_term_isWeightedHomogeneous n p hp

private theorem ggVac_term_isWeightedHomogeneous (r : ℕ) (q : ℤ)
    (hq : q ∈ Finset.Icc (-(r : ℤ)) 0) :
    MvPolynomial.IsWeightedHomogeneous freeLiWeight
      (Wak.cV (-q) * Wak.cV ((r : ℤ) + q)) r := by
  simp only [Finset.mem_Icc] at hq
  rw [Wak.cV_of_nonneg (by omega), Wak.cV_of_nonneg (by omega)]
  have hweight : (-q).toNat + ((r : ℤ) + q).toNat = r := by omega
  have hc₁ := X_isWeightedHomogeneous_freeLi (1 : Fin 3) (-q).toNat
  have hc₂ := X_isWeightedHomogeneous_freeLi (1 : Fin 3) ((r : ℤ) + q).toNat
  have hmul := hc₁.mul hc₂
  rwa [hweight] at hmul

/-- The nonpositive `:γγ:` vacuum convolution has free Li weight `r`. -/
theorem ggVac_isWeightedHomogeneous (r : ℕ) :
    MvPolynomial.IsWeightedHomogeneous freeLiWeight (ggVac r) r := by
  rw [ggVac]
  exact MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun q hq =>
    ggVac_term_isWeightedHomogeneous r q hq

private theorem bggVac_term_isWeightedHomogeneous (n : ℕ) (p : ℤ)
    (hp : p ∈ Finset.Icc (-((n : ℤ)) - 1) (-1)) :
    MvPolynomial.IsWeightedHomogeneous freeLiWeight
      (Wak.bV (-p) * ggVac (((n : ℤ) + 1 + p).toNat)) n := by
  simp only [Finset.mem_Icc] at hp
  rw [Wak.bV_of_pos (by omega)]
  have hweight : (-p - 1).toNat + ((n : ℤ) + 1 + p).toNat = n := by omega
  have hb := X_isWeightedHomogeneous_freeLi (0 : Fin 3) (-p - 1).toNat
  have hgg := ggVac_isWeightedHomogeneous (((n : ℤ) + 1 + p).toNat)
  have hmul := hb.mul hgg
  rwa [hweight] at hmul

/-- The negative `:βγγ:` vacuum convolution has free Li weight `n`. -/
theorem bggVac_isWeightedHomogeneous (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous freeLiWeight (bggVac n) n := by
  rw [bggVac]
  exact MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun p hp =>
    bggVac_term_isWeightedHomogeneous n p hp

private theorem bgVac_term_isAdegreeZero (n : ℕ) (p : ℤ)
    (hp : p ∈ Finset.Icc (-((n : ℤ)) - 1) (-1)) :
    MvPolynomial.IsWeightedHomogeneous aDegreeWeight
      (Wak.bV (-p) * Wak.cV ((n : ℤ) + 1 + p)) 0 := by
  simp only [Finset.mem_Icc] at hp
  rw [Wak.bV_of_pos (by omega), Wak.cV_of_nonneg (by omega)]
  have hb := X_isWeightedHomogeneous_aDegree (0 : Fin 3) (-p - 1).toNat
  have hc := X_isWeightedHomogeneous_aDegree (1 : Fin 3) ((n : ℤ) + 1 + p).toNat
  simpa [aDegreeWeight] using hb.mul hc

/-- The `:βγ:` vacuum convolution contains no `A` variable. -/
theorem bgVac_isAdegreeZero (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous aDegreeWeight (bgVac n) 0 := by
  rw [bgVac]
  exact MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun p hp =>
    bgVac_term_isAdegreeZero n p hp

/-! ## Exact one-current decompositions -/

/-- The classical part of one Wakimoto `e` creation current. -/
def eClassical (n : ℕ) : Wak.WakFock := MvPolynomial.X ((0 : Fin 3), n)

/-- The classical part of one Wakimoto `h` creation current, kept in normal-ordered form. -/
def hClassical (k : ℂ) (n : ℕ) : Wak.WakFock :=
  (-2 : ℂ) • Wak.BG (-((n : ℤ)) - 1) 1 + Wak.aV ((n : ℤ) + 1)

/-- The classical part of one Wakimoto `f` creation current, kept in normal-ordered form.  The
omitted summand is precisely the one-step-deeper derivative correction. -/
def fClassical (k : ℂ) (n : ℕ) : Wak.WakFock :=
  -Wak.BGG (-((n : ℤ)) - 1) 1 + Wak.AG k (-((n : ℤ)) - 1) 1

/-- Multiplication by the `:βγ:` vacuum symbol has the expected filtration shift. -/
theorem bgVac_mul_mem_freeLiAtLeast (n : ℕ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) : bgVac n * P ∈ freeLiAtLeast (d + n) := by
  have hmain := BG_neg_mem_freeLiAtLeast n hP
  have herr := freeLiAtLeast_mono (d := d + n) (e := d + n + 1) (by omega)
    (BG_sub_classical_mem_freeLiAtLeast n hP)
  have hsub := Submodule.sub_mem (freeLiAtLeast (d + n)) hmain herr
  convert hsub using 1 <;> ring

/-- Multiplication by the `:aγ:` vacuum symbol has the expected filtration shift. -/
theorem agVac_mul_mem_freeLiAtLeast (n : ℕ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) : agVac n * P ∈ freeLiAtLeast (d + n) := by
  have hmain := AG_neg_mem_freeLiAtLeast (0 : ℂ) n hP
  have herr := freeLiAtLeast_mono (d := d + n) (e := d + n + 1) (by omega)
    (AG_sub_classical_mem_freeLiAtLeast (0 : ℂ) n hP)
  have hsub := Submodule.sub_mem (freeLiAtLeast (d + n)) hmain herr
  convert hsub using 1 <;> ring

/-- Multiplication by the `:βγγ:` vacuum symbol has the expected filtration shift. -/
theorem bggVac_mul_mem_freeLiAtLeast (n : ℕ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) : bggVac n * P ∈ freeLiAtLeast (d + n) := by
  have hmain := BGG_neg_mem_freeLiAtLeast n hP
  have herr := freeLiAtLeast_mono (d := d + n) (e := d + n + 1) (by omega)
    (BGG_sub_classical_mem_freeLiAtLeast n hP)
  have hsub := Submodule.sub_mem (freeLiAtLeast (d + n)) hmain herr
  convert hsub using 1 <;> ring

/-- Multiplication by a classical `e` symbol raises the lower bound by its depth. -/
theorem eClassical_mul_mem_freeLiAtLeast (n : ℕ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) : eClassical n * P ∈ freeLiAtLeast (d + n) := by
  rw [eClassical]
  simpa only [freeLiWeight] using
    (X_mul_mem_freeLiAtLeast ((0 : Fin 3), n) hP)

/-- Multiplication by a classical `h` symbol raises the lower bound by its depth. -/
theorem hClassical_mul_mem_freeLiAtLeast (k : ℂ) (n : ℕ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) : hClassical k n * P ∈ freeLiAtLeast (d + n) := by
  rw [hClassical, BG_one_neg, add_mul, smul_mul_assoc]
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ (bgVac_mul_mem_freeLiAtLeast n hP)
  · have ha := aV_mul_mem_freeLiAtLeast (i := (n : ℤ) + 1) (by omega) hP
    have hindex : ((n : ℤ) + 1 - 1).toNat = n := by omega
    rwa [hindex] at ha

/-- Multiplication by a classical `f` symbol raises the lower bound by its depth. -/
theorem fClassical_mul_mem_freeLiAtLeast (k : ℂ) (n : ℕ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) : fClassical k n * P ∈ freeLiAtLeast (d + n) := by
  rw [fClassical, BGG_one_neg, AG_one_neg, add_mul, neg_mul]
  exact Submodule.add_mem _ (Submodule.neg_mem _ (bggVac_mul_mem_freeLiAtLeast n hP))
    (agVac_mul_mem_freeLiAtLeast n hP)

/-- The classical polynomial attached to a Chevalley-coloured current. -/
def currentClassical (k : ℂ) (a : Fin 3) (n : ℕ) : Wak.WakFock :=
  if a = 0 then eClassical n else if a = 1 then fClassical k n else hClassical k n

theorem currentClassical_mul_mem_freeLiAtLeast (k : ℂ) (a : Fin 3) (n : ℕ)
    {d : ℕ} {P : Wak.WakFock} (hP : P ∈ freeLiAtLeast d) :
    currentClassical k a n * P ∈ freeLiAtLeast (d + n) := by
  fin_cases a <;> simp only [currentClassical, Fin.zero_eta, Fin.mk_one, ↓reduceIte,
    OfNat.ofNat] <;>
    first | exact eClassical_mul_mem_freeLiAtLeast n hP |
      exact fClassical_mul_mem_freeLiAtLeast k n hP |
      exact hClassical_mul_mem_freeLiAtLeast k n hP

/-- A negative `e` current is exactly multiplication by its classical symbol. -/
theorem Ecur_sub_classical_mem_freeLiAtLeast (n : ℕ) {d : ℕ} {P : Wak.WakFock} :
    Wak.Ecur (-((n : ℤ)) - 1) P - eClassical n * P ∈ freeLiAtLeast (d + n + 1) := by
  rw [Wak.Ecur, Wak.Bet_of_neg (by omega), Wak.mulL_apply,
    show -(-((n : ℤ)) - 1) = (n : ℤ) + 1 by ring, Wak.bV_of_pos (by omega), eClassical]
  have hindex : ((n : ℤ) + 1 - 1).toNat = n := by omega
  rw [hindex, sub_self]
  exact Submodule.zero_mem _

/-- A negative `h` current differs from classical-symbol multiplication by one filtration step. -/
theorem Hcur_sub_classical_mem_freeLiAtLeast (k : ℂ) (n : ℕ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.Hcur k (-((n : ℤ)) - 1) P - hClassical k n * P ∈
      freeLiAtLeast (d + n + 1) := by
  rw [Wak.Hcur, LinearMap.add_apply, LinearMap.smul_apply,
    Wak.Aos_of_neg k (by omega), Wak.mulL_apply, hClassical, BG_one_neg, add_mul,
    smul_mul_assoc]
  rw [show -(-((n : ℤ)) - 1) = (n : ℤ) + 1 by ring]
  have hrearrange : (-2 : ℂ) • Wak.BG (-((n : ℤ)) - 1) P + Wak.aV ((n : ℤ) + 1) * P -
      ((-2 : ℂ) • (bgVac n * P) + Wak.aV ((n : ℤ) + 1) * P) =
      (-2 : ℂ) • (Wak.BG (-((n : ℤ)) - 1) P - bgVac n * P) := by module
  rw [hrearrange]
  exact Submodule.smul_mem _ _ (BG_sub_classical_mem_freeLiAtLeast n hP)

/-- A negative `f` current differs from classical-symbol multiplication by one filtration step. -/
theorem Fcur_sub_classical_mem_freeLiAtLeast (k : ℂ) (n : ℕ) {d : ℕ} {P : Wak.WakFock}
    (hP : P ∈ freeLiAtLeast d) :
    Wak.Fcur k (-((n : ℤ)) - 1) P - fClassical k n * P ∈
      freeLiAtLeast (d + n + 1) := by
  rw [Wak.Fcur, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.smul_apply, Wak.Gam_of_nonpos (by omega), Wak.mulL_apply,
    fClassical, BGG_one_neg, AG_one_neg, add_mul, neg_mul]
  rw [show -(-((n : ℤ)) - 1) = (n : ℤ) + 1 by ring]
  have hrearrange :
      (-Wak.BGG (-((n : ℤ)) - 1) P + Wak.AG k (-((n : ℤ)) - 1) P -
          (k * ((-((n : ℤ)) - 1 : ℤ) : ℂ)) • (Wak.cV ((n : ℤ) + 1) * P)) -
        (-(bggVac n * P) + agVac n * P) =
      -(Wak.BGG (-((n : ℤ)) - 1) P - bggVac n * P) +
        (Wak.AG k (-((n : ℤ)) - 1) P - agVac n * P) -
          (k * ((-((n : ℤ)) - 1 : ℤ) : ℂ)) • (Wak.cV ((n : ℤ) + 1) * P) := by
    abel
  rw [hrearrange]
  apply Submodule.sub_mem
  · exact Submodule.add_mem _
      (Submodule.neg_mem _ (BGG_sub_classical_mem_freeLiAtLeast n hP))
      (AG_sub_classical_mem_freeLiAtLeast k n hP)
  · apply Submodule.smul_mem
    have hc := cV_mul_mem_freeLiAtLeast (j := (n : ℤ) + 1) (by omega) hP
    have hindex : ((n : ℤ) + 1).toNat = n + 1 := by omega
    simpa only [hindex, Nat.add_assoc] using hc

/-- Uniform sharp minimum-symbol estimate for all three negative Wakimoto currents. -/
theorem Jw_sub_classical_mem_freeLiAtLeast (k : ℂ) (a : Fin 3) (n : ℕ)
    {d : ℕ} {P : Wak.WakFock} (hP : P ∈ freeLiAtLeast d) :
    Wak.Jw k a (-((n : ℤ)) - 1) P - currentClassical k a n * P ∈
      freeLiAtLeast (d + n + 1) := by
  fin_cases a
  · change Wak.Jw k 0 (-((n : ℤ)) - 1) P - eClassical n * P ∈
      freeLiAtLeast (d + n + 1)
    rw [Wak.Jw_E]
    exact Ecur_sub_classical_mem_freeLiAtLeast n
  · change Wak.Jw k 1 (-((n : ℤ)) - 1) P - fClassical k n * P ∈
      freeLiAtLeast (d + n + 1)
    rw [Wak.Jw_F]
    exact Fcur_sub_classical_mem_freeLiAtLeast k n hP
  · change Wak.Jw k 2 (-((n : ℤ)) - 1) P - hClassical k n * P ∈
      freeLiAtLeast (d + n + 1)
    rw [Wak.Jw_H]
    exact Hcur_sub_classical_mem_freeLiAtLeast k n hP

/-- The classical `e` symbol has free Li weight `n`. -/
theorem eClassical_isWeightedHomogeneous (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous freeLiWeight (eClassical n) n := by
  exact X_isWeightedHomogeneous_freeLi (0 : Fin 3) n

/-- The classical `h` symbol has free Li weight `n`. -/
theorem hClassical_isWeightedHomogeneous (k : ℂ) (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous freeLiWeight (hClassical k n) n := by
  rw [hClassical, BG_one_neg, Wak.aV_of_pos (by omega)]
  have hindex : (((n : ℤ) + 1 - 1).toNat) = n := by omega
  rw [hindex]
  have hbg := (bgVac_isWeightedHomogeneous n).C_mul (-2 : ℂ)
  have ha := X_isWeightedHomogeneous_freeLi (2 : Fin 3) n
  simpa only [MvPolynomial.smul_eq_C_mul] using hbg.add ha

/-- The classical `f` symbol has free Li weight `n`. -/
theorem fClassical_isWeightedHomogeneous (k : ℂ) (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous freeLiWeight (fClassical k n) n := by
  rw [fClassical, BGG_one_neg, AG_one_neg]
  have hbgg : MvPolynomial.IsWeightedHomogeneous freeLiWeight (-bggVac n) n :=
    (MvPolynomial.weightedHomogeneousSubmodule ℂ freeLiWeight n).neg_mem
      (bggVac_isWeightedHomogeneous n)
  have hag := agVac_isWeightedHomogeneous n
  exact hbgg.add hag

/-- Every one-current classical symbol is homogeneous of its current depth. -/
theorem currentClassical_isWeightedHomogeneous (k : ℂ) (a : Fin 3) (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous freeLiWeight (currentClassical k a n) n := by
  fin_cases a <;> simp only [currentClassical, Fin.zero_eta, Fin.mk_one, ↓reduceIte,
    OfNat.ofNat] <;>
    first | exact eClassical_isWeightedHomogeneous n |
      exact fClassical_isWeightedHomogeneous k n | exact hClassical_isWeightedHomogeneous k n

/-! ## Lexicographic leading monomials of the classical currents -/

/-- The monomial selected from the classical symbol of one current. -/
def classicalCurrentPivot (a : Fin 3) (n : ℕ) : Wak.WakFock :=
  if a = 0 then MvPolynomial.X ((0 : Fin 3), n)
  else if a = 1 then
    MvPolynomial.X ((2 : Fin 3), 0) * MvPolynomial.X ((1 : Fin 3), n)
  else MvPolynomial.X ((2 : Fin 3), n)

/-- Triangular degree of one current: only an `f` current contributes a `c` variable. -/
def classicalCurrentTriDegree (a : Fin 3) (n : ℕ) : ClassicalTriDegree :=
  if a = 1 then toLex (1, -(n : ℤ)) else 0

/-- Exponent of the selected pivot monomial for one abstract affine-current variable. -/
def classicalPivotLetterExponent (q : Fin 3 ×ₗ ℕ) : (Fin 3 × ℕ) →₀ ℕ :=
  Finsupp.single (ofLex q) 1 +
    if (ofLex q).1 = 1 then Finsupp.single ((2 : Fin 3), 0) 1 else 0

/-- Additive exponent map induced by the pivot monomials. -/
def classicalPivotExponent (mu : (Fin 3 ×ₗ ℕ) →₀ ℕ) : (Fin 3 × ℕ) →₀ ℕ :=
  mu.sum fun q m => m • classicalPivotLetterExponent q

/-- Total number of abstract `f`-letters in an affine PBW exponent. -/
def classicalFCount (mu : (Fin 3 ×ₗ ℕ) →₀ ℕ) : ℕ :=
  mu.sum fun q m => if (ofLex q).1 = 1 then m else 0

/-- Total exponent of the target `c` variables.  This recovers the number of abstract
`f`-letters from a pivot exponent. -/
def classicalTargetCCount : ((Fin 3 × ℕ) →₀ ℕ) →+ ℕ :=
  Finsupp.weight fun q => if q.1 = 1 then 1 else 0

@[simp] private theorem classicalTargetCCount_single (q : Fin 3 × ℕ) (m : ℕ) :
    classicalTargetCCount (Finsupp.single q m) = if q.1 = 1 then m else 0 := by
  classical
  rw [classicalTargetCCount, Finsupp.weight_single]
  by_cases hq : q.1 = 1 <;> simp [hq]

private theorem classicalTargetCCount_pivotLetter (q : Fin 3 ×ₗ ℕ) (m : ℕ) :
    classicalTargetCCount (m • classicalPivotLetterExponent q) =
      if (ofLex q).1 = 1 then m else 0 := by
  classical
  rw [classicalPivotLetterExponent, smul_add, map_add, Finsupp.smul_single_one]
  by_cases hq : (ofLex q).1 = 1 <;> simp [hq]

theorem classicalTargetCCount_pivotExponent (mu : (Fin 3 ×ₗ ℕ) →₀ ℕ) :
    classicalTargetCCount (classicalPivotExponent mu) = classicalFCount mu := by
  classical
  rw [classicalPivotExponent, classicalFCount]
  simp only [Finsupp.sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact classicalTargetCCount_pivotLetter q (mu q)

private theorem classicalPivotExtra_apply_of_ne (mu : (Fin 3 ×ₗ ℕ) →₀ ℕ)
    (x : Fin 3 × ℕ) (hx : x ≠ ((2 : Fin 3), 0)) :
    (mu.sum fun q m =>
      if (ofLex q).1 = 1 then Finsupp.single ((2 : Fin 3), 0) m else 0) x = 0 := by
  classical
  rw [Finsupp.sum]
  let ev : ((Fin 3 × ℕ) →₀ ℕ) →+ ℕ :=
    { toFun := fun e => e x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ q ∈ mu.support,
    if (ofLex q).1 = 1 then Finsupp.single ((2 : Fin 3), 0) (mu q) else 0) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro q hq
  by_cases hqf : (ofLex q).1 = 1
  · simp [ev, hqf, hx]
  · simp [ev, hqf]

@[simp] theorem classicalPivotExponent_apply_b (mu : (Fin 3 ×ₗ ℕ) →₀ ℕ) (n : ℕ) :
    classicalPivotExponent mu ((0 : Fin 3), n) = mu (toLex ((0 : Fin 3), n)) := by
  classical
  rw [classicalPivotExponent]
  simp only [classicalPivotLetterExponent, smul_add, Finsupp.smul_single_one,
    Finsupp.sum, Finset.sum_add_distrib, smul_ite, smul_zero,
    Finsupp.add_apply, Finset.sum_apply]
  change (Finsupp.mapDomain ofLex mu) ((0 : Fin 3), n) +
      (mu.sum fun q m =>
        if (ofLex q).1 = 1 then Finsupp.single ((2 : Fin 3), 0) m else 0)
          ((0 : Fin 3), n) = _
  rw [show ((0 : Fin 3), n) = ofLex (toLex ((0 : Fin 3), n)) by simp,
    Finsupp.mapDomain_apply ofLex.injective]
  rw [classicalPivotExtra_apply_of_ne mu
    (ofLex (toLex ((0 : Fin 3), n))) (by simp), add_zero]
  simp

@[simp] theorem classicalPivotExponent_apply_c (mu : (Fin 3 ×ₗ ℕ) →₀ ℕ) (n : ℕ) :
    classicalPivotExponent mu ((1 : Fin 3), n) = mu (toLex ((1 : Fin 3), n)) := by
  classical
  rw [classicalPivotExponent]
  simp only [classicalPivotLetterExponent, smul_add, Finsupp.smul_single_one,
    Finsupp.sum, Finset.sum_add_distrib, smul_ite, smul_zero,
    Finsupp.add_apply, Finset.sum_apply]
  change (Finsupp.mapDomain ofLex mu) ((1 : Fin 3), n) +
      (mu.sum fun q m =>
        if (ofLex q).1 = 1 then Finsupp.single ((2 : Fin 3), 0) m else 0)
          ((1 : Fin 3), n) = _
  rw [show ((1 : Fin 3), n) = ofLex (toLex ((1 : Fin 3), n)) by simp,
    Finsupp.mapDomain_apply ofLex.injective]
  rw [classicalPivotExtra_apply_of_ne mu
    (ofLex (toLex ((1 : Fin 3), n))) (by simp), add_zero]
  simp

@[simp] theorem classicalPivotExponent_apply_A_pos (mu : (Fin 3 ×ₗ ℕ) →₀ ℕ) (n : ℕ)
    (hn : 0 < n) :
    classicalPivotExponent mu ((2 : Fin 3), n) = mu (toLex ((2 : Fin 3), n)) := by
  classical
  rw [classicalPivotExponent]
  simp only [classicalPivotLetterExponent, smul_add, Finsupp.smul_single_one,
    Finsupp.sum, Finset.sum_add_distrib, smul_ite, smul_zero,
    Finsupp.add_apply, Finset.sum_apply]
  change (Finsupp.mapDomain ofLex mu) ((2 : Fin 3), n) +
      (mu.sum fun q m =>
        if (ofLex q).1 = 1 then Finsupp.single ((2 : Fin 3), 0) m else 0)
          ((2 : Fin 3), n) = _
  rw [show ((2 : Fin 3), n) = ofLex (toLex ((2 : Fin 3), n)) by simp,
    Finsupp.mapDomain_apply ofLex.injective]
  rw [classicalPivotExtra_apply_of_ne mu
    (ofLex (toLex ((2 : Fin 3), n))) (by
      intro h
      have hsnd := congrArg Prod.snd h
      simp only [ofLex_toLex] at hsnd
      omega), add_zero]
  simp

@[simp] theorem classicalPivotExponent_apply_A_zero (mu : (Fin 3 ×ₗ ℕ) →₀ ℕ) :
    classicalPivotExponent mu ((2 : Fin 3), 0) =
      mu (toLex ((2 : Fin 3), 0)) + classicalFCount mu := by
  classical
  rw [classicalPivotExponent]
  simp only [classicalPivotLetterExponent, smul_add, Finsupp.smul_single_one,
    Finsupp.sum, Finset.sum_add_distrib, smul_ite, smul_zero,
    Finsupp.add_apply, Finset.sum_apply]
  change (Finsupp.mapDomain ofLex mu) ((2 : Fin 3), 0) +
      (mu.sum fun q m =>
        if (ofLex q).1 = 1 then Finsupp.single ((2 : Fin 3), 0) m else 0)
          ((2 : Fin 3), 0) = _
  rw [show ((2 : Fin 3), 0) = ofLex (toLex ((2 : Fin 3), 0)) by simp,
    Finsupp.mapDomain_apply ofLex.injective]
  simp only [ofLex_toLex]
  congr 1
  rw [classicalFCount]
  simp only [Finsupp.sum]
  let ev : ((Fin 3 × ℕ) →₀ ℕ) →+ ℕ :=
    { toFun := fun e => e ((2 : Fin 3), 0)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ q ∈ mu.support,
    if (ofLex q).1 = 1 then Finsupp.single ((2 : Fin 3), 0) (mu q) else 0) =
      ∑ q ∈ mu.support, if (ofLex q).1 = 1 then mu q else 0
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hqf : (ofLex q).1 = 1 <;> simp [ev, hqf]

/-- The selected pivot exponent remembers the original affine PBW exponent.  The `b_n` and
`c_n` coordinates recover the `e_n` and `f_n` multiplicities, the positive `A_n` coordinates
recover the positive `h_n` multiplicities, and `A_0` recovers `h_0` after subtracting the total
`c` exponent. -/
theorem classicalPivotExponent_injective : Function.Injective classicalPivotExponent := by
  intro mu nu h
  have hfcount : classicalFCount mu = classicalFCount nu := by
    rw [← classicalTargetCCount_pivotExponent mu,
      ← classicalTargetCCount_pivotExponent nu, h]
  apply Finsupp.ext
  intro q
  rcases hq : ofLex q with ⟨a, n⟩
  have hq' : q = toLex (a, n) := by
    rw [← hq]
    simp
  rw [hq']
  fin_cases a
  · have hb := congrArg
      (fun e : (Fin 3 × ℕ) →₀ ℕ => e ((0 : Fin 3), n)) h
    simpa using hb
  · have hc := congrArg
      (fun e : (Fin 3 × ℕ) →₀ ℕ => e ((1 : Fin 3), n)) h
    simpa using hc
  · by_cases hn : n = 0
    · subst n
      have hA := congrArg
        (fun e : (Fin 3 × ℕ) →₀ ℕ => e ((2 : Fin 3), 0)) h
      simpa [hfcount] using hA
    · have hA := congrArg
        (fun e : (Fin 3 × ℕ) →₀ ℕ => e ((2 : Fin 3), n)) h
      simpa [classicalPivotExponent_apply_A_pos, Nat.pos_of_ne_zero hn] using hA

/-- Each selected current pivot is the monomial with the corresponding letter exponent. -/
theorem classicalCurrentPivot_eq_monomial (a : Fin 3) (n : ℕ) :
    classicalCurrentPivot a n =
      MvPolynomial.monomial (classicalPivotLetterExponent (toLex (a, n))) 1 := by
  fin_cases a <;>
    simp [classicalCurrentPivot, classicalPivotLetterExponent, MvPolynomial.X,
      MvPolynomial.monomial_mul, add_comm]

theorem classicalCurrentPivot_isWeightedHomogeneous (a : Fin 3) (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous classicalTriWeight
      (classicalCurrentPivot a n) (classicalCurrentTriDegree a n) := by
  fin_cases a
  · change MvPolynomial.IsWeightedHomogeneous classicalTriWeight
      (MvPolynomial.X ((0 : Fin 3), n)) 0
    simpa using X_isWeightedHomogeneous_classicalTri (0 : Fin 3) n
  · change MvPolynomial.IsWeightedHomogeneous classicalTriWeight
      (MvPolynomial.X ((2 : Fin 3), 0) * MvPolynomial.X ((1 : Fin 3), n))
        (toLex (1, -(n : ℤ)))
    have hA := X_isWeightedHomogeneous_classicalTri (2 : Fin 3) 0
    have hc := X_isWeightedHomogeneous_classicalTri (1 : Fin 3) n
    have hmul := hA.mul hc
    have hdeg : classicalTriWeight ((2 : Fin 3), 0) +
        classicalTriWeight ((1 : Fin 3), n) = toLex (1, -(n : ℤ)) := by simp
    rwa [hdeg] at hmul
  · change MvPolynomial.IsWeightedHomogeneous classicalTriWeight
      (MvPolynomial.X ((2 : Fin 3), n)) 0
    simpa using X_isWeightedHomogeneous_classicalTri (2 : Fin 3) n

private theorem bgVac_term_mem_classicalTriAbove (n : ℕ) (p : ℤ)
    (hp : p ∈ Finset.Icc (-((n : ℤ)) - 1) (-1)) :
    Wak.bV (-p) * Wak.cV ((n : ℤ) + 1 + p) ∈ classicalTriAbove 0 := by
  simp only [Finset.mem_Icc] at hp
  rw [Wak.bV_of_pos (by omega), Wak.cV_of_nonneg (by omega)]
  apply isWeightedHomogeneous_mem_classicalTriAbove
    (e := toLex (1, -(((n : ℤ) + 1 + p).toNat : ℤ)))
  · change toLex (0, 0) < toLex (1, -(((n : ℤ) + 1 + p).toNat : ℤ))
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inl (by omega)
  · have hb := X_isWeightedHomogeneous_classicalTri (0 : Fin 3) (-p - 1).toNat
    have hc := X_isWeightedHomogeneous_classicalTri
      (1 : Fin 3) ((n : ℤ) + 1 + p).toNat
    have hmul := hb.mul hc
    have hdeg : classicalTriWeight ((0 : Fin 3), (-p - 1).toNat) +
        classicalTriWeight ((1 : Fin 3), ((n : ℤ) + 1 + p).toNat) =
          toLex (1, -(((n : ℤ) + 1 + p).toNat : ℤ)) := by simp
    rwa [hdeg] at hmul

theorem bgVac_mem_classicalTriAbove (n : ℕ) : bgVac n ∈ classicalTriAbove 0 := by
  rw [bgVac]
  exact Submodule.sum_mem _ fun p hp => bgVac_term_mem_classicalTriAbove n p hp

private theorem agVac_term_isWeightedHomogeneous_classicalTri (n : ℕ) (p : ℤ)
    (hp : p ∈ Finset.Icc (-((n : ℤ)) - 1) (-1)) :
    MvPolynomial.IsWeightedHomogeneous classicalTriWeight
      (Wak.aV (-p) * Wak.cV ((n : ℤ) + 1 + p))
      (toLex (1, -(((n : ℤ) + 1 + p).toNat : ℤ))) := by
  simp only [Finset.mem_Icc] at hp
  rw [Wak.aV_of_pos (by omega), Wak.cV_of_nonneg (by omega)]
  have hA := X_isWeightedHomogeneous_classicalTri (2 : Fin 3) (-p - 1).toNat
  have hc := X_isWeightedHomogeneous_classicalTri
    (1 : Fin 3) ((n : ℤ) + 1 + p).toNat
  have hmul := hA.mul hc
  have hdeg : classicalTriWeight ((2 : Fin 3), (-p - 1).toNat) +
      classicalTriWeight ((1 : Fin 3), ((n : ℤ) + 1 + p).toNat) =
        toLex (1, -(((n : ℤ) + 1 + p).toNat : ℤ)) := by simp
  rwa [hdeg] at hmul

private theorem agVac_top_term (n : ℕ) :
    Wak.aV 1 * Wak.cV (n : ℤ) = classicalCurrentPivot 1 n := by
  rw [Wak.aV_of_pos (by omega), Wak.cV_of_nonneg (by omega)]
  change MvPolynomial.X ((2 : Fin 3), 0) * MvPolynomial.X ((1 : Fin 3), n) = _
  congr 2 <;> omega

/-- All non-leading terms of the classical `:aγ:` convolution are strictly larger in the
classical triangular order. -/
theorem agVac_sub_pivot_mem_classicalTriAbove (n : ℕ) :
    agVac n - classicalCurrentPivot 1 n ∈
      classicalTriAbove (classicalCurrentTriDegree 1 n) := by
  let s := Finset.Icc (-((n : ℤ)) - 1) (-1)
  have hm : (-1 : ℤ) ∈ s := by simp [s]
  have htop : Wak.aV (-(-1 : ℤ)) * Wak.cV ((n : ℤ) + 1 + (-1 : ℤ)) =
      classicalCurrentPivot 1 n := by simpa using agVac_top_term n
  rw [agVac, show Finset.Icc (-((n : ℤ)) - 1) (-1) = s by rfl,
    ← Finset.sum_erase_add _ _ hm, htop, add_sub_cancel_right]
  apply Submodule.sum_mem
  intro p hp
  have hps := (Finset.mem_erase.mp hp).2
  have hpne := (Finset.mem_erase.mp hp).1
  have hhom := agVac_term_isWeightedHomogeneous_classicalTri n p hps
  refine isWeightedHomogeneous_mem_classicalTriAbove
    (e := toLex (1, -(((n : ℤ) + 1 + p).toNat : ℤ))) ?_ hhom
  change toLex (1, -(n : ℤ)) < toLex (1, -(((n : ℤ) + 1 + p).toNat : ℤ))
  rw [Prod.Lex.toLex_lt_toLex]
  right
  constructor
  · rfl
  · have hps' : -((n : ℤ)) - 1 ≤ p ∧ p ≤ -1 := by simpa [s] using hps
    rw [Int.toNat_of_nonneg (by omega)]
    omega

private theorem ggVac_term_isWeightedHomogeneous_classicalTri (r : ℕ) (q : ℤ)
    (hq : q ∈ Finset.Icc (-(r : ℤ)) 0) :
    MvPolynomial.IsWeightedHomogeneous classicalTriWeight
      (Wak.cV (-q) * Wak.cV ((r : ℤ) + q)) (toLex (2, -(r : ℤ))) := by
  simp only [Finset.mem_Icc] at hq
  rw [Wak.cV_of_nonneg (by omega), Wak.cV_of_nonneg (by omega)]
  have hc₁ := X_isWeightedHomogeneous_classicalTri (1 : Fin 3) (-q).toNat
  have hc₂ := X_isWeightedHomogeneous_classicalTri (1 : Fin 3) ((r : ℤ) + q).toNat
  have hsum : ((-q).toNat : ℤ) + (((r : ℤ) + q).toNat : ℤ) = r := by omega
  have hmul := hc₁.mul hc₂
  have hdeg : classicalTriWeight ((1 : Fin 3), (-q).toNat) +
      classicalTriWeight ((1 : Fin 3), ((r : ℤ) + q).toNat) =
        toLex (2, -(r : ℤ)) := by
    apply ofLex.injective
    simp only [classicalTriWeight_one, ofLex_add, ofLex_toLex, Prod.fst_add, Prod.snd_add]
    apply Prod.ext
    · norm_num
    · simp only [Prod.snd_add]
      omega
  rwa [hdeg] at hmul

theorem ggVac_isWeightedHomogeneous_classicalTri (r : ℕ) :
    MvPolynomial.IsWeightedHomogeneous classicalTriWeight (ggVac r)
      (toLex (2, -(r : ℤ))) := by
  rw [ggVac]
  exact MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun q hq =>
    ggVac_term_isWeightedHomogeneous_classicalTri r q hq

private theorem bggVac_term_mem_classicalTriAbove (n : ℕ) (p : ℤ)
    (hp : p ∈ Finset.Icc (-((n : ℤ)) - 1) (-1)) :
    Wak.bV (-p) * ggVac (((n : ℤ) + 1 + p).toNat) ∈
      classicalTriAbove (classicalCurrentTriDegree 1 n) := by
  simp only [Finset.mem_Icc] at hp
  rw [Wak.bV_of_pos (by omega)]
  have hb := X_isWeightedHomogeneous_classicalTri (0 : Fin 3) (-p - 1).toNat
  have hgg := ggVac_isWeightedHomogeneous_classicalTri (((n : ℤ) + 1 + p).toNat)
  apply isWeightedHomogeneous_mem_classicalTriAbove
    (e := toLex (2, -((((n : ℤ) + 1 + p).toNat : ℕ) : ℤ)))
  · change toLex (1, -(n : ℤ)) < toLex (2, -((((n : ℤ) + 1 + p).toNat : ℕ) : ℤ))
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inl (by omega)
  · have hmul := hb.mul hgg
    have hdeg : classicalTriWeight ((0 : Fin 3), (-p - 1).toNat) +
        toLex (2, -((((n : ℤ) + 1 + p).toNat : ℕ) : ℤ)) =
          toLex (2, -((((n : ℤ) + 1 + p).toNat : ℕ) : ℤ)) := by simp
    rwa [hdeg] at hmul

theorem bggVac_mem_classicalTriAbove (n : ℕ) :
    bggVac n ∈ classicalTriAbove (classicalCurrentTriDegree 1 n) := by
  rw [bggVac]
  exact Submodule.sum_mem _ fun p hp => bggVac_term_mem_classicalTriAbove n p hp

/-- The classical current differs from its lexicographic pivot by strictly higher terms. -/
theorem currentClassical_sub_pivot_mem_classicalTriAbove (k : ℂ) (a : Fin 3) (n : ℕ) :
    currentClassical k a n - classicalCurrentPivot a n ∈
      classicalTriAbove (classicalCurrentTriDegree a n) := by
  fin_cases a
  · change eClassical n - MvPolynomial.X ((0 : Fin 3), n) ∈ classicalTriAbove 0
    rw [eClassical, sub_self]
    exact Submodule.zero_mem _
  · change fClassical k n -
      (MvPolynomial.X ((2 : Fin 3), 0) * MvPolynomial.X ((1 : Fin 3), n)) ∈
        classicalTriAbove (toLex (1, -(n : ℤ)))
    rw [fClassical, BGG_one_neg, AG_one_neg]
    have hbgg := Submodule.neg_mem _ (bggVac_mem_classicalTriAbove n)
    have hag := agVac_sub_pivot_mem_classicalTriAbove n
    have hadd := Submodule.add_mem _ hbgg hag
    have hpivot : classicalCurrentPivot 1 n =
        MvPolynomial.X ((2 : Fin 3), 0) * MvPolynomial.X ((1 : Fin 3), n) := by
      norm_num [classicalCurrentPivot]
    rw [hpivot] at hadd
    convert hadd using 1 <;> ring
  · change hClassical k n - MvPolynomial.X ((2 : Fin 3), n) ∈ classicalTriAbove 0
    rw [hClassical, BG_one_neg, Wak.aV_of_pos (by omega)]
    have hindex : ((n : ℤ) + 1 - 1).toNat = n := by omega
    rw [hindex]
    have hbg := Submodule.smul_mem (classicalTriAbove 0) (-2 : ℂ)
      (bgVac_mem_classicalTriAbove n)
    convert hbg using 1 <;> module

theorem currentClassical_mem_classicalTriAtLeast (k : ℂ) (a : Fin 3) (n : ℕ) :
    currentClassical k a n ∈ classicalTriAtLeast (classicalCurrentTriDegree a n) := by
  have hpivot := isWeightedHomogeneous_mem_classicalTriAtLeast
    (classicalCurrentPivot_isWeightedHomogeneous a n)
  have herr := classicalTriAbove_le_atLeast (classicalCurrentTriDegree a n)
    (currentClassical_sub_pivot_mem_classicalTriAbove k a n)
  have hadd := Submodule.add_mem (classicalTriAtLeast (classicalCurrentTriDegree a n)) hpivot herr
  convert hadd using 1 <;> ring

/-- Product of the classical Wakimoto current symbols in a colour-and-depth word. -/
def classicalWordState (k : ℂ) : List (Fin 3 × ℕ) → Wak.WakFock
  | [] => 1
  | (a, n) :: l => currentClassical k a n * classicalWordState k l

@[simp] theorem classicalWordState_nil (k : ℂ) : classicalWordState k [] = 1 := rfl

@[simp] theorem classicalWordState_cons (k : ℂ) (a : Fin 3) (n : ℕ)
    (l : List (Fin 3 × ℕ)) :
    classicalWordState k ((a, n) :: l) =
      currentClassical k a n * classicalWordState k l := rfl

/-- Product of the selected classical pivot monomials in a current word. -/
def classicalPivotWord : List (Fin 3 × ℕ) → Wak.WakFock
  | [] => 1
  | (a, n) :: l => classicalCurrentPivot a n * classicalPivotWord l

/-- Sum of the lexicographic current degrees in a word. -/
def classicalWordTriDegree (l : List (Fin 3 × ℕ)) : ClassicalTriDegree :=
  (l.map fun q => classicalCurrentTriDegree q.1 q.2).sum

@[simp] theorem classicalWordTriDegree_nil : classicalWordTriDegree [] = 0 := rfl

@[simp] theorem classicalWordTriDegree_cons (a : Fin 3) (n : ℕ) (l : List (Fin 3 × ℕ)) :
    classicalWordTriDegree ((a, n) :: l) =
      classicalCurrentTriDegree a n + classicalWordTriDegree l := rfl

theorem classicalPivotWord_isWeightedHomogeneous : ∀ l : List (Fin 3 × ℕ),
    MvPolynomial.IsWeightedHomogeneous classicalTriWeight
      (classicalPivotWord l) (classicalWordTriDegree l)
  | [] => MvPolynomial.isWeightedHomogeneous_one ℂ classicalTriWeight
  | (a, n) :: l => by
      exact (classicalCurrentPivot_isWeightedHomogeneous a n).mul
        (classicalPivotWord_isWeightedHomogeneous l)

theorem classicalWordState_mem_classicalTriAtLeast (k : ℂ) : ∀ l : List (Fin 3 × ℕ),
    classicalWordState k l ∈ classicalTriAtLeast (classicalWordTriDegree l)
  | [] => isWeightedHomogeneous_mem_classicalTriAtLeast
      (MvPolynomial.isWeightedHomogeneous_one ℂ classicalTriWeight)
  | (a, n) :: l =>
      classicalTriAtLeast_mul (currentClassical_mem_classicalTriAtLeast k a n)
        (classicalWordState_mem_classicalTriAtLeast k l)

/-- The product of full classical currents differs from the product of their selected pivot
monomials only in strictly higher lexicographic weight. -/
theorem classicalWordState_sub_pivot_mem_classicalTriAbove (k : ℂ) :
    ∀ l : List (Fin 3 × ℕ),
      classicalWordState k l - classicalPivotWord l ∈
        classicalTriAbove (classicalWordTriDegree l)
  | [] => by
      rw [classicalWordState, classicalPivotWord, sub_self]
      exact Submodule.zero_mem _
  | (a, n) :: l => by
      rw [classicalWordState, classicalPivotWord, classicalWordTriDegree_cons]
      have hcurrent := currentClassical_sub_pivot_mem_classicalTriAbove k a n
      have hword := classicalWordState_mem_classicalTriAtLeast k l
      have h₁ := classicalTriAbove_mul_atLeast hcurrent hword
      have hpivot := isWeightedHomogeneous_mem_classicalTriAtLeast
        (classicalCurrentPivot_isWeightedHomogeneous a n)
      have h₂ := classicalTriAtLeast_mul_above hpivot
        (classicalWordState_sub_pivot_mem_classicalTriAbove k l)
      have hadd := Submodule.add_mem
        (classicalTriAbove
          (classicalCurrentTriDegree a n + classicalWordTriDegree l)) h₁ h₂
      convert hadd using 1 <;> ring

/-- The selected pivot product is exactly the minimum lexicographic component of every classical
current word. -/
theorem weightedComponent_classicalWordState_triMin (k : ℂ) (l : List (Fin 3 × ℕ)) :
    MvPolynomial.weightedHomogeneousComponent classicalTriWeight (classicalWordTriDegree l)
        (classicalWordState k l) = classicalPivotWord l := by
  have herr := classicalWordState_sub_pivot_mem_classicalTriAbove k l
  have hz := classicalTriAbove_component_eq_zero herr le_rfl
  have hpivot :=
    (classicalPivotWord_isWeightedHomogeneous l).weightedHomogeneousComponent_same
  have hdecompose : classicalWordState k l = classicalPivotWord l +
      (classicalWordState k l - classicalPivotWord l) := by ring
  rw [hdecompose, map_add, hpivot, hz, add_zero]

theorem weightedComponent_classicalWordState_triBelow (k : ℂ) (l : List (Fin 3 × ℕ))
    (d : ClassicalTriDegree) (hd : d < classicalWordTriDegree l) :
    MvPolynomial.weightedHomogeneousComponent classicalTriWeight d
        (classicalWordState k l) = 0 :=
  classicalTriAtLeast_component_eq_zero (classicalWordState_mem_classicalTriAtLeast k l) hd

/-! ## Minimum free-Li symbols of arbitrary current words -/

/-- The classical symbol product is homogeneous of total current depth. -/
theorem classicalWordState_isWeightedHomogeneous (k : ℂ) : ∀ l : List (Fin 3 × ℕ),
    MvPolynomial.IsWeightedHomogeneous freeLiWeight
      (classicalWordState k l) (wordFreeLiDegree l)
  | [] => MvPolynomial.isWeightedHomogeneous_one ℂ freeLiWeight
  | (a, n) :: l => by
      rw [classicalWordState_cons, wordFreeLiDegree_cons]
      exact (currentClassical_isWeightedHomogeneous k a n).mul
        (classicalWordState_isWeightedHomogeneous k l)

/-- An arbitrary Wakimoto current word differs from the product of its classical symbols only in
free-Li weights strictly above the sum of current depths.  This is the operator-side
triangularity theorem: it includes all contractions created when later currents act on earlier
states. -/
theorem wakimotoWordState_sub_classical_mem_freeLiAtLeast (k : ℂ) :
    ∀ l : List (Fin 3 × ℕ),
      wakimotoWordState k l - classicalWordState k l ∈
        freeLiAtLeast (wordFreeLiDegree l + 1)
  | [] => by
      rw [wakimotoWordState, classicalWordState, sub_self]
      exact Submodule.zero_mem _
  | (a, n) :: l => by
      rw [wakimotoWordState, classicalWordState_cons, wordFreeLiDegree_cons]
      have hword := wakimotoWordState_mem_freeLiAtLeast k l
      have hcurrent := Jw_sub_classical_mem_freeLiAtLeast k a n hword
      have hcurrent' :
          Wak.Jw k a (-((n : ℤ)) - 1) (wakimotoWordState k l) -
              currentClassical k a n * wakimotoWordState k l ∈
            freeLiAtLeast (n + wordFreeLiDegree l + 1) := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcurrent
      have htail := currentClassical_mul_mem_freeLiAtLeast k a n
        (wakimotoWordState_sub_classical_mem_freeLiAtLeast k l)
      have htail' :
          currentClassical k a n *
              (wakimotoWordState k l - classicalWordState k l) ∈
            freeLiAtLeast (n + wordFreeLiDegree l + 1) := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
      have hadd := Submodule.add_mem (freeLiAtLeast (n + wordFreeLiDegree l + 1))
        hcurrent' htail'
      convert hadd using 1 <;> ring

/-- The minimum free-Li component of any iterated Wakimoto current word is exactly the product
of the three classical current symbols. -/
theorem weightedComponent_wakimotoWordState_min (k : ℂ) (l : List (Fin 3 × ℕ)) :
    MvPolynomial.weightedHomogeneousComponent freeLiWeight (wordFreeLiDegree l)
        (wakimotoWordState k l) =
      classicalWordState k l := by
  have herr := wakimotoWordState_sub_classical_mem_freeLiAtLeast k l
  have herrComponent := weightedComponent_eq_zero_of_mem_freeLiAtLeast
    (d := wordFreeLiDegree l + 1) (r := wordFreeLiDegree l) herr (Nat.lt_succ_self _)
  have hclass :=
    (classicalWordState_isWeightedHomogeneous k l).weightedHomogeneousComponent_same
  have hdecompose :
      wakimotoWordState k l =
        classicalWordState k l +
          (wakimotoWordState k l - classicalWordState k l) := by ring
  rw [hdecompose, map_add, hclass, herrComponent, add_zero]

/-- The ordered product of classical symbols attached to an affine PBW exponent. -/
def classicalOrderedCreationState (k : ℂ) : ((Fin 3 ×ₗ ℕ) →₀ ℕ) → Wak.WakFock :=
  fun mu => classicalWordState k (orderedPBWColorWord mu)

/-- Substitution homomorphism from abstract affine-current jets to their classical Wakimoto
symbols. -/
def classicalSubstitution (k : ℂ) :
    MvPolynomial (Fin 3 ×ₗ ℕ) ℂ →ₐ[ℂ] Wak.WakFock :=
  MvPolynomial.aeval fun q => currentClassical k (ofLex q).1 (ofLex q).2

private theorem classicalWordState_eq_list_prod (k : ℂ) :
    ∀ l : List (Fin 3 × ℕ),
      classicalWordState k l =
        (l.map fun q => currentClassical k q.1 q.2).prod
  | [] => rfl
  | (a, n) :: l => by
      rw [classicalWordState_cons, List.map_cons, List.prod_cons,
        classicalWordState_eq_list_prod k l]

private theorem list_prod_flatMap {α M : Type*} [CommMonoid M]
    (f : α → List M) : ∀ l : List α,
    (l.flatMap f).prod = (l.map fun a => (f a).prod).prod
  | [] => rfl
  | a :: l => by
      rw [List.flatMap_cons, List.prod_append, List.map_cons, List.prod_cons,
        list_prod_flatMap f l]

private theorem list_prod_sort_eq_finset_prod {α M : Type*} [LinearOrder α] [CommMonoid M]
    (s : Finset α) (f : α → M) :
    ((s.sort (fun a b => a ≤ b)).map f).prod = ∏ a ∈ s, f a := by
  have hcoe :
      (↑((s.sort (fun a b => a ≤ b)).map f) : Multiset M) = s.1.map f := by
    change (↑(s.sort (fun a b => a ≤ b)) : Multiset α).map f = s.1.map f
    exact congrArg (Multiset.map f) (Finset.sort_eq s (fun a b => a ≤ b))
  exact (congrArg Multiset.prod hcoe).trans (Finset.prod_map_val s f)

private theorem finset_prod_monomial {R α σ : Type*} [CommSemiring R]
    (s : Finset α) (e : α → σ →₀ ℕ) (m : α → ℕ) :
    (∏ q ∈ s, (MvPolynomial.monomial (e q) (1 : R)) ^ (m q)) =
      MvPolynomial.monomial (∑ q ∈ s, (m q) • e q) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert q s hq ih =>
      rw [Finset.prod_insert hq, Finset.sum_insert hq, ih]
      simp [MvPolynomial.monomial_pow, MvPolynomial.monomial_mul, add_comm]

/-- The ordered product of selected pivot monomials. -/
def classicalPivotOrderedCreationState : ((Fin 3 ×ₗ ℕ) →₀ ℕ) → Wak.WakFock :=
  fun mu => classicalPivotWord (orderedPBWColorWord mu)

private theorem classicalPivotWord_eq_list_prod : ∀ l : List (Fin 3 × ℕ),
    classicalPivotWord l = (l.map fun q => classicalCurrentPivot q.1 q.2).prod
  | [] => rfl
  | (a, n) :: l => by
      rw [classicalPivotWord, List.map_cons, List.prod_cons,
        classicalPivotWord_eq_list_prod l]

/-- The selected pivot product of an ordered PBW word is the monomial encoded by the injective
pivot exponent map. -/
theorem classicalPivotOrderedCreationState_eq_monomial (mu : (Fin 3 ×ₗ ℕ) →₀ ℕ) :
    classicalPivotOrderedCreationState mu =
      MvPolynomial.monomial (classicalPivotExponent mu) 1 := by
  rw [classicalPivotOrderedCreationState, classicalPivotWord_eq_list_prod,
    orderedPBWColorWord, List.map_flatMap, list_prod_flatMap]
  simp only [List.map_replicate, List.prod_replicate]
  rw [list_prod_sort_eq_finset_prod]
  simp_rw [classicalCurrentPivot_eq_monomial]
  rw [finset_prod_monomial]
  congr 1

/-- Distinct ordered PBW exponents give distinct selected pivot monomials. -/
theorem classicalPivotOrderedCreationState_linearIndependent :
    LinearIndependent ℂ classicalPivotOrderedCreationState := by
  have hmono : LinearIndependent ℂ
      (fun e : (Fin 3 × ℕ) →₀ ℕ =>
        (MvPolynomial.monomial e 1 : Wak.WakFock)) :=
    (MvPolynomial.basisMonomials (Fin 3 × ℕ) ℂ).linearIndependent
  have hpivot := hmono.comp classicalPivotExponent classicalPivotExponent_injective
  rw [show classicalPivotOrderedCreationState =
      (fun mu => MvPolynomial.monomial (classicalPivotExponent mu) 1) from by
    funext mu
    exact classicalPivotOrderedCreationState_eq_monomial mu]
  simpa only [Function.comp_apply] using hpivot

/-- Minimum triangular degree of the ordered classical word. -/
def classicalOrderedTriDegree (mu : (Fin 3 ×ₗ ℕ) →₀ ℕ) : ClassicalTriDegree :=
  classicalWordTriDegree (orderedPBWColorWord mu)

/-- The products of the full classical Wakimoto current symbols are linearly independent for
every level.  This is the commutative-algebra core of the affine PBW proof. -/
theorem classicalOrderedCreationState_linearIndependent (k : ℂ) :
    LinearIndependent ℂ (classicalOrderedCreationState k) := by
  apply linearIndependent_of_lowerLeading_linearOrder classicalOrderedTriDegree
    (classicalOrderedCreationState k) classicalPivotOrderedCreationState
    (fun d => MvPolynomial.weightedHomogeneousComponent classicalTriWeight d)
  · intro mu
    exact weightedComponent_classicalWordState_triMin k (orderedPBWColorWord mu)
  · intro mu d hd
    exact weightedComponent_classicalWordState_triBelow k (orderedPBWColorWord mu) d hd
  · exact classicalPivotOrderedCreationState_linearIndependent

/-- The ordered classical word is the substitution image of the corresponding monomial. -/
theorem classicalOrderedCreationState_eq_substitution_monomial (k : ℂ)
    (mu : (Fin 3 ×ₗ ℕ) →₀ ℕ) :
    classicalOrderedCreationState k mu =
      classicalSubstitution k (MvPolynomial.monomial mu 1) := by
  rw [classicalOrderedCreationState, classicalWordState_eq_list_prod,
    classicalSubstitution, MvPolynomial.aeval_monomial, map_one, one_mul]
  rw [orderedPBWColorWord, List.map_flatMap, list_prod_flatMap]
  simp only [List.map_replicate, List.prod_replicate]
  rw [list_prod_sort_eq_finset_prod]
  exact Finset.prod_congr rfl fun _ _ => rfl

/-- The prolonged classical Wakimoto substitution is injective for every level. -/
theorem classicalSubstitution_injective (k : ℂ) :
    Function.Injective (classicalSubstitution k) := by
  have himage : LinearIndependent ℂ
      (fun mu : (Fin 3 ×ₗ ℕ) →₀ ℕ =>
        classicalSubstitution k (MvPolynomial.monomial mu 1)) := by
    rw [← show classicalOrderedCreationState k =
        (fun mu => classicalSubstitution k (MvPolynomial.monomial mu 1)) from by
      funext mu
      exact classicalOrderedCreationState_eq_substitution_monomial k mu]
    exact classicalOrderedCreationState_linearIndependent k
  intro x y hxy
  let b := MvPolynomial.basisMonomials (Fin 3 ×ₗ ℕ) ℂ
  apply b.repr.injective
  apply himage
  have hrepr (z : MvPolynomial (Fin 3 ×ₗ ℕ) ℂ) :
      Finsupp.linearCombination ℂ
          (fun mu : (Fin 3 ×ₗ ℕ) →₀ ℕ =>
            classicalSubstitution k (MvPolynomial.monomial mu 1)) (b.repr z) =
        classicalSubstitution k z := by
    calc
      Finsupp.linearCombination ℂ
          (fun mu : (Fin 3 ×ₗ ℕ) →₀ ℕ =>
            classicalSubstitution k (MvPolynomial.monomial mu 1)) (b.repr z) =
          classicalSubstitution k
            (Finsupp.linearCombination ℂ
              (fun mu : (Fin 3 ×ₗ ℕ) →₀ ℕ => MvPolynomial.monomial mu 1)
              (b.repr z)) := by
        simpa only [Function.comp_apply, AlgHom.toLinearMap_apply] using
          (Finsupp.apply_linearCombination ℂ (classicalSubstitution k).toLinearMap
            (fun mu : (Fin 3 ×ₗ ℕ) →₀ ℕ => MvPolynomial.monomial mu 1)
            (b.repr z)).symm
      _ = classicalSubstitution k z := by
        congr 1
        simpa only [b, MvPolynomial.coe_basisMonomials] using b.linearCombination_repr z
  rw [hrepr x, hrepr y, hxy]

/-- Injectivity of the classical substitution implies independence of all ordered classical
symbol products. -/
theorem classicalOrderedCreationState_linearIndependent_of_substitution_injective
    (k : ℂ) (hinj : Function.Injective (classicalSubstitution k)) :
    LinearIndependent ℂ (classicalOrderedCreationState k) := by
  have hmono : LinearIndependent ℂ
      (fun mu : (Fin 3 ×ₗ ℕ) →₀ ℕ => (MvPolynomial.monomial mu 1 :
        MvPolynomial (Fin 3 ×ₗ ℕ) ℂ)) :=
    (MvPolynomial.basisMonomials (Fin 3 ×ₗ ℕ) ℂ).linearIndependent
  have himage := hmono.map' (classicalSubstitution k).toLinearMap
    (LinearMap.ker_eq_bot.mpr hinj)
  rw [show classicalOrderedCreationState k =
      (fun mu => classicalSubstitution k (MvPolynomial.monomial mu 1)) from by
    funext mu
    exact classicalOrderedCreationState_eq_substitution_monomial k mu]
  simpa only [Function.comp_apply, AlgHom.toLinearMap_apply] using himage

/-- Minimum free-Li degree of an ordered affine PBW word. -/
def orderedFreeLiDegree (mu : ((Fin 3 ×ₗ ℕ) →₀ ℕ)) : ℕ :=
  wordFreeLiDegree (orderedPBWColorWord mu)

/-- Algebraic independence of the ordered classical symbol products implies linear independence
of the full Wakimoto current words.  The only remaining input is a finite-jet commutative
algebra statement. -/
theorem wakimotoOrderedCreationState_linearIndependent_of_classical
    (k : ℂ) (hli : LinearIndependent ℂ (classicalOrderedCreationState k)) :
    LinearIndependent ℂ (wakimotoOrderedCreationState k) := by
  apply linearIndependent_of_lowerLeading orderedFreeLiDegree
    (wakimotoOrderedCreationState k) (classicalOrderedCreationState k)
    (fun n => MvPolynomial.weightedHomogeneousComponent freeLiWeight n)
  · intro mu
    exact weightedComponent_wakimotoWordState_min k (orderedPBWColorWord mu)
  · intro mu n hn
    exact weightedComponent_wakimotoWordState_eq_zero k (orderedPBWColorWord mu) n hn
  · exact hli

/-- The universal affine PBW basis follows once the explicit finite-jet classical products are
linearly independent. -/
theorem pbwBasis_of_classicalOrderedCreationState_linearIndependent
    (k : ℂ) (hk : k + 2 ≠ 0)
    (hli : LinearIndependent ℂ (classicalOrderedCreationState k)) :
    PBWBasis AffineVOA.kappaForm AffineVOA.kappaForm_isInvariant
      (Pi.basisFun ℂ (Fin 3)) k :=
  pbwBasis_of_wakimotoOrderedCreationState_linearIndependent k hk
    (wakimotoOrderedCreationState_linearIndependent_of_classical k hli)

/-- A single injectivity theorem for the prolonged classical Wakimoto substitution supplies the
ordinary affine PBW basis. -/
theorem pbwBasis_of_classicalSubstitution_injective
    (k : ℂ) (hk : k + 2 ≠ 0) (hinj : Function.Injective (classicalSubstitution k)) :
    PBWBasis AffineVOA.kappaForm AffineVOA.kappaForm_isInvariant
      (Pi.basisFun ℂ (Fin 3)) k :=
  pbwBasis_of_classicalOrderedCreationState_linearIndependent k hk
    (classicalOrderedCreationState_linearIndependent_of_substitution_injective k hinj)

/-- The ordered negative-current Wakimoto states are linearly independent at every level. -/
theorem wakimotoOrderedCreationState_linearIndependent (k : ℂ) :
    LinearIndependent ℂ (wakimotoOrderedCreationState k) :=
  wakimotoOrderedCreationState_linearIndependent_of_classical k
    (classicalOrderedCreationState_linearIndependent k)

/-- **Ordinary affine `sl₂` PBW at every noncritical level.** -/
theorem affineSl2PBWBasis (k : ℂ) (hk : k + 2 ≠ 0) :
    PBWBasis AffineVOA.kappaForm AffineVOA.kappaForm_isInvariant
      (Pi.basisFun ℂ (Fin 3)) k :=
  pbwBasis_of_wakimotoOrderedCreationState_linearIndependent k hk
    (wakimotoOrderedCreationState_linearIndependent k)

/-- The universal affine `C2` symbol map is injective at every noncritical level. -/
theorem universalSymbolAlg_injective (k : ℂ) (hk : k + 2 ≠ 0) :
    Function.Injective (Sl2Pres.symbolAlg k hk) :=
  AffineSl2UniversalC2PBW.symbolAlg_injective_of_PBWBasis k hk
    (affineSl2PBWBasis k hk)

/-- A negative `e` current on the vacuum is exactly its classical variable. -/
theorem Jw_e_one (k : ℂ) (n : ℕ) :
    Wak.Jw k 0 (-((n : ℤ)) - 1) (1 : Wak.WakFock) = eClassical n := by
  rw [Wak.Jw_E, Wak.Ecur, Wak.Bet_one_neg (by omega), Wak.bV_of_pos (by omega)]
  simp [eClassical]

/-- A negative `h` current on the vacuum has no derivative correction. -/
theorem Jw_h_one (k : ℂ) (n : ℕ) :
    Wak.Jw k 2 (-((n : ℤ)) - 1) (1 : Wak.WakFock) = hClassical k n := by
  rw [Wak.Jw_H, Wak.Hcur, LinearMap.add_apply, LinearMap.smul_apply,
    Wak.Aos_one_neg k (by omega), hClassical]
  congr 2
  ring

/-- Fully finite form of the one-current `h` vacuum state. -/
theorem Jw_h_one_explicit (k : ℂ) (n : ℕ) :
    Wak.Jw k 2 (-((n : ℤ)) - 1) (1 : Wak.WakFock) =
      (-2 : ℂ) • bgVac n + MvPolynomial.X ((2 : Fin 3), n) := by
  rw [Jw_h_one, hClassical, BG_one_neg, Wak.aV_of_pos (by omega)]
  congr 2
  norm_num

/-- A negative `f` current is its classical normal-ordered part plus
`k(n+1)c_(n+1)`.  The displayed correction is the unique one-current term one step deeper in
free Li weight. -/
theorem Jw_f_one (k : ℂ) (n : ℕ) :
    Wak.Jw k 1 (-((n : ℤ)) - 1) (1 : Wak.WakFock) =
      fClassical k n + (k * ((n : ℂ) + 1)) • MvPolynomial.X ((1 : Fin 3), n + 1) := by
  rw [Wak.Jw_F, Wak.Fcur, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.smul_apply, Wak.Gam_one_nonpos (by omega), Wak.cV_of_nonneg (by omega), fClassical]
  have hindex : (-(-((n : ℤ)) - 1)).toNat = n + 1 := by omega
  rw [hindex, sub_eq_add_neg, ← neg_smul]
  congr 1
  push_cast
  ring

/-- Fully finite form of the one-current `f` vacuum state. -/
theorem Jw_f_one_explicit (k : ℂ) (n : ℕ) :
    Wak.Jw k 1 (-((n : ℤ)) - 1) (1 : Wak.WakFock) =
      -bggVac n + agVac n +
        (k * ((n : ℂ) + 1)) • MvPolynomial.X ((1 : Fin 3), n + 1) := by
  rw [Jw_f_one, fClassical, BGG_one_neg, AG_one_neg]

/-- The derivative correction in `Jw_f_one` is homogeneous of free Li weight `n+1`. -/
theorem f_quantumCorrection_isWeightedHomogeneous (k : ℂ) (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous freeLiWeight
      ((k * ((n : ℂ) + 1)) • MvPolynomial.X ((1 : Fin 3), n + 1) : Wak.WakFock)
      (n + 1) := by
  simpa only [MvPolynomial.smul_eq_C_mul] using
    (X_isWeightedHomogeneous_freeLi (1 : Fin 3) (n + 1)).C_mul (k * ((n : ℂ) + 1))

/-- Projecting the derivative correction to the classical free-Li weight gives zero. -/
theorem weightedComponent_f_quantumCorrection (k : ℂ) (n : ℕ) :
    MvPolynomial.weightedHomogeneousComponent freeLiWeight n
      ((k * ((n : ℂ) + 1)) • MvPolynomial.X ((1 : Fin 3), n + 1) : Wak.WakFock) = 0 := by
  apply (f_quantumCorrection_isWeightedHomogeneous k n).weightedHomogeneousComponent_ne
  omega

/-- The weight-`n` component of a one-current `e` state is its classical symbol. -/
theorem weightedComponent_Jw_e_one (k : ℂ) (n : ℕ) :
    MvPolynomial.weightedHomogeneousComponent freeLiWeight n
      (Wak.Jw k 0 (-((n : ℤ)) - 1) (1 : Wak.WakFock)) = eClassical n := by
  rw [Jw_e_one, (eClassical_isWeightedHomogeneous n).weightedHomogeneousComponent_same]

/-- The weight-`n` component of a one-current `h` state is its classical symbol. -/
theorem weightedComponent_Jw_h_one (k : ℂ) (n : ℕ) :
    MvPolynomial.weightedHomogeneousComponent freeLiWeight n
      (Wak.Jw k 2 (-((n : ℤ)) - 1) (1 : Wak.WakFock)) = hClassical k n := by
  rw [Jw_h_one, (hClassical_isWeightedHomogeneous k n).weightedHomogeneousComponent_same]

/-- At the one-current level, the highest `A`-degree component of an `h` state is the single
variable `A_(n+1)`.  Iterated contractions prevent using this after maximizing free Li weight. -/
theorem aDegreeComponent_Jw_h_one (k : ℂ) (n : ℕ) :
    MvPolynomial.weightedHomogeneousComponent aDegreeWeight 1
      (Wak.Jw k 2 (-((n : ℤ)) - 1) (1 : Wak.WakFock)) =
        MvPolynomial.X ((2 : Fin 3), n) := by
  have hA : MvPolynomial.IsWeightedHomogeneous aDegreeWeight
      (MvPolynomial.X ((2 : Fin 3), n) : Wak.WakFock) 1 := by
    simpa [aDegreeWeight] using X_isWeightedHomogeneous_aDegree (2 : Fin 3) n
  rw [Jw_h_one_explicit, map_add, map_smul,
    (bgVac_isAdegreeZero n).weightedHomogeneousComponent_ne 1 (by norm_num), smul_zero,
    hA.weightedHomogeneousComponent_same, zero_add]

/-- The weight-`n` component of a one-current `f` state is its classical symbol. -/
theorem weightedComponent_Jw_f_one (k : ℂ) (n : ℕ) :
    MvPolynomial.weightedHomogeneousComponent freeLiWeight n
      (Wak.Jw k 1 (-((n : ℤ)) - 1) (1 : Wak.WakFock)) = fClassical k n := by
  rw [Jw_f_one, map_add, weightedComponent_f_quantumCorrection, add_zero,
    (fClassical_isWeightedHomogeneous k n).weightedHomogeneousComponent_same]

/-- The highest free-Li component of a one-current `f` state is exactly the quantum correction.
This tempting top component does not remain the top component of an arbitrary current word. -/
theorem weightedComponent_Jw_f_one_top (k : ℂ) (n : ℕ) :
    MvPolynomial.weightedHomogeneousComponent freeLiWeight (n + 1)
      (Wak.Jw k 1 (-((n : ℤ)) - 1) (1 : Wak.WakFock)) =
        (k * ((n : ℂ) + 1)) • MvPolynomial.X ((1 : Fin 3), n + 1) := by
  rw [Jw_f_one, map_add,
    (fClassical_isWeightedHomogeneous k n).weightedHomogeneousComponent_ne (n + 1) (by omega),
    (f_quantumCorrection_isWeightedHomogeneous k n).weightedHomogeneousComponent_same, zero_add]

/-- The scalar on the one-current `f` pivot is nonzero precisely under the boundary-relevant
hypothesis `k != 0`. -/
theorem f_pivotCoefficient_ne_zero {k : ℂ} (hk : k ≠ 0) (n : ℕ) :
    k * ((n : ℂ) + 1) ≠ 0 := by
  exact mul_ne_zero hk (Nat.cast_add_one_ne_zero n)

end
end AffineSl2WakimotoLiLeading
end VOA

section AxiomAudit
#print axioms VOA.AffineSl2WakimotoLiLeading.linearIndependent_of_lowerLeading
#print axioms VOA.AffineSl2WakimotoLiLeading.linearIndependent_of_pivot
#print axioms VOA.AffineSl2WakimotoLiLeading.Jw_neg_mem_freeLiAtLeast
#print axioms VOA.AffineSl2WakimotoLiLeading.wakimotoWordState_mem_freeLiAtLeast
#print axioms VOA.AffineSl2WakimotoLiLeading.weightedComponent_wakimotoWordState_eq_zero
#print axioms VOA.AffineSl2WakimotoLiLeading.Jw_f_one
#print axioms VOA.AffineSl2WakimotoLiLeading.BGG_one_neg
#print axioms VOA.AffineSl2WakimotoLiLeading.fClassical_isWeightedHomogeneous
#print axioms VOA.AffineSl2WakimotoLiLeading.aDegreeComponent_Jw_h_one
#print axioms VOA.AffineSl2WakimotoLiLeading.weightedComponent_Jw_f_one_top
#print axioms VOA.AffineSl2WakimotoLiLeading.weightedComponent_f_quantumCorrection
#print axioms VOA.AffineSl2WakimotoLiLeading.BG_sub_classical_mem_freeLiAtLeast
#print axioms VOA.AffineSl2WakimotoLiLeading.AG_sub_classical_mem_freeLiAtLeast
#print axioms VOA.AffineSl2WakimotoLiLeading.GG_sub_classical_mem_freeLiAtLeast
#print axioms VOA.AffineSl2WakimotoLiLeading.BGG_sub_classical_mem_freeLiAtLeast
#print axioms VOA.AffineSl2WakimotoLiLeading.Jw_sub_classical_mem_freeLiAtLeast
#print axioms VOA.AffineSl2WakimotoLiLeading.wakimotoWordState_sub_classical_mem_freeLiAtLeast
#print axioms VOA.AffineSl2WakimotoLiLeading.weightedComponent_wakimotoWordState_min
#print axioms VOA.AffineSl2WakimotoLiLeading.wakimotoOrderedCreationState_linearIndependent_of_classical
#print axioms VOA.AffineSl2WakimotoLiLeading.pbwBasis_of_classicalOrderedCreationState_linearIndependent
#print axioms VOA.AffineSl2WakimotoLiLeading.classicalOrderedCreationState_eq_substitution_monomial
#print axioms VOA.AffineSl2WakimotoLiLeading.classicalOrderedCreationState_linearIndependent_of_substitution_injective
#print axioms VOA.AffineSl2WakimotoLiLeading.pbwBasis_of_classicalSubstitution_injective
#print axioms VOA.AffineSl2WakimotoLiLeading.classicalPivotExponent_injective
#print axioms VOA.AffineSl2WakimotoLiLeading.classicalPivotOrderedCreationState_linearIndependent
#print axioms VOA.AffineSl2WakimotoLiLeading.classicalOrderedCreationState_linearIndependent
#print axioms VOA.AffineSl2WakimotoLiLeading.classicalSubstitution_injective
#print axioms VOA.AffineSl2WakimotoLiLeading.wakimotoOrderedCreationState_linearIndependent
#print axioms VOA.AffineSl2WakimotoLiLeading.affineSl2PBWBasis
#print axioms VOA.AffineSl2WakimotoLiLeading.universalSymbolAlg_injective
end AxiomAudit
