/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2OscillatorWordPairing
import VOA.Examples.AffineSl2HighestGramRoot

/-!
# Nonzero leading matrices in the actual Fock factorization

The highest-weight-leading creation matrix is triangular in boson count
with diagonal one. The adjoint row matrix is triangular in the opposite
direction, with diagonal the explicit pure-derivative multiplier. The
calculation uses actual operators and includes every repeated oscillator.
-/
namespace VOA.Wak.Charged
open MvPolynomial Matrix
noncomputable section
local instance fockTopFintype (n : ℕ) (c : ℤ) : Fintype (JointIndex n c) := jointIndexFintype n c
local instance fockTopDecidable (n : ℕ) (c : ℤ) : DecidableEq (JointIndex n c) := Classical.decEq _

/-- Boson multiplicity of an occupation, measured on its literal chosen list. -/
def occupationBosons (d : Occupation) : ℕ := bosonCount d.toMultiset.toList

/-- Signed weight of an occupation equals signed boson multiplicity. -/
theorem occupation_bosonWeight (s : ℤ) (d : Occupation) :
    Finsupp.weight (bosonWeight s) d=s*(occupationBosons d : ℤ) := by
  rw [← listOccupation_toList d,listOccupation_bosonWeight]
  rw [listOccupation_toList]
  rfl

/-- The highest-weight-leading creation coordinate matrix. -/
def creationTopMatrix (k : ℂ) (n : ℕ) (c : ℤ) :
    Matrix (JointIndex n c) (JointIndex n c) ℂ := fun i j =>
  coeff i.val (leadingCreationWord k j.val.toMultiset.toList 1)

/-- The highest-weight-leading positive row matrix; the creation list is
reversed because opposite-mode adjoints reverse products. -/
def rowTopMatrix (k : ℂ) (n : ℕ) (c : ℤ) :
    Matrix (JointIndex n c) (JointIndex n c) ℂ := fun i j =>
  constantCoeff (leadingAnnihilationWord k i.val.toMultiset.toList.reverse (monomial j.val 1))

/-- The Fock vacuum has signed boson weight zero. -/
theorem one_mem_bosonAtLeast (s : ℤ) : (1 : WakFock)∈bosonAtLeast s 0 := by
  simpa using boson_monomial_mem s 0 0 (by simp)

/-- The creation top matrix vanishes when output boson multiplicity exceeds
that of the input creation word. -/
theorem creationTopMatrix_zero (k : ℂ) (n : ℕ) (c : ℤ) (i j : JointIndex n c)
    (h : occupationBosons j.val<occupationBosons i.val) : creationTopMatrix k n c i j=0 := by
  apply boson_coeff_zero (-1) (0-(occupationBosons j.val : ℤ))
    (leadingCreationWord_mem k _ (one_mem_bosonAtLeast (-1))) i.val
  rw [occupation_bosonWeight]
  simp only [neg_mul,one_mul]
  omega

/-- On equal boson-count blocks the creation top matrix is exactly the
identity. Every beta-gamma correction has smaller output boson count. -/
theorem creationTopMatrix_equal_bosons (k : ℂ) (n : ℕ) (c : ℤ) (i j : JointIndex n c)
    (h : occupationBosons i.val=occupationBosons j.val) :
    creationTopMatrix k n c i j=if i=j then 1 else 0 := by
  have he := boson_coeff_zero (-1) (0-(occupationBosons j.val : ℤ)+1)
    (leadingCreationWord_error k _ (one_mem_bosonAtLeast (-1))) i.val (by
      rw [occupation_bosonWeight,h]; simp)
  rw [coeff_sub,oscillatorMonomial_eq,listOccupation_toList,mul_one,coeff_monomial] at he
  have hh : j.val=i.val ↔ i=j := by
    constructor
    · intro hh; exact (Subtype.ext hh).symm
    · intro hh; exact congrArg Subtype.val hh.symm
  simpa only [creationTopMatrix,hh] using sub_eq_zero.mp he

/-- A positive row cannot remove more bosons than its number of neutral
letters, so its constant coefficient vanishes below the opposite triangle. -/
theorem rowTopMatrix_zero (k : ℂ) (n : ℕ) (c : ℤ) (i j : JointIndex n c)
    (h : occupationBosons i.val<occupationBosons j.val) : rowTopMatrix k n c i j=0 := by
  have hm := boson_monomial_mem 1 (occupationBosons j.val : ℤ) j.val
    (by rw [occupation_bosonWeight]; simp)
  have he := leadingAnnihilationWord_mem k i.val.toMultiset.toList.reverse hm
  apply boson_coeff_zero 1 _ he 0
  simp only [map_zero,bosonCount_reverse]
  change 0<(occupationBosons j.val : ℤ)-(occupationBosons i.val : ℤ)
  omega

/-- Equal-count positive row entries are exactly pure oscillator pairings,
with their mode signs, level factors and repeated-occupation multiplicities. -/
theorem rowTopMatrix_equal_bosons (k : ℂ) (n : ℕ) (c : ℤ) (i j : JointIndex n c)
    (h : occupationBosons i.val=occupationBosons j.val) :
    rowTopMatrix k n c i j=if i=j then
      derivativeMultiplier k i.val.toMultiset.toList.reverse 0 else 0 := by
  have hm := boson_monomial_mem 1 (occupationBosons j.val : ℤ) j.val
    (by rw [occupation_bosonWeight]; simp)
  have he := boson_coeff_zero 1 _ (leadingAnnihilationWord_error k i.val.toMultiset.toList.reverse hm) 0 (by
    simp only [map_zero,bosonCount_reverse]
    change 0<(occupationBosons j.val : ℤ)-(occupationBosons i.val : ℤ)+1
    rw [h]; simp)
  rw [coeff_sub] at he
  have heq := sub_eq_zero.mp he
  change rowTopMatrix k n c i j=constantCoeff (pureAnnihilationWord k _ (monomial j.val 1)) at heq
  rw [heq,pureAnnihilationWord_pair,listOccupation_reverse,listOccupation_toList]
  have hh : j.val=i.val ↔ i=j := by
    constructor
    · intro hh; exact (Subtype.ext hh).symm
    · intro hh; exact congrArg Subtype.val hh.symm
  simp only [hh]

/-- A finite matrix triangular by a numerical weight, with diagonal
weight blocks, has determinant equal to its diagonal product. No ordering
of the index type or distinctness of its numerical weights is needed. -/
theorem det_weight_triangular {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (d : ι→ℕ)
    (hup : ∀ i j,d j<d i→A i j=0)
    (heq : ∀ i j,d i=d j→i≠j→A i j=0) : A.det=∏ i,A i i := by
  classical
  have hp (σ : Equiv.Perm ι) (hσ : σ≠1) : (∏ j,A (σ j) j)=0 := by
    by_contra hn
    have hall : ∀ j,A (σ j) j≠0 := fun j hz => hn (Finset.prod_eq_zero (Finset.mem_univ j) hz)
    have hle : ∀ j,d (σ j)≤d j := by
      intro j; by_contra hh; exact hall j (hup _ _ (by omega))
    have hs : (∑ j,d (σ j))=∑ j,d j := Equiv.sum_comp σ d
    have he : ∀ j,d (σ j)=d j := fun j =>
      (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp hs j (Finset.mem_univ j)
    apply hσ
    apply Equiv.ext
    intro j
    change σ j=j
    by_contra hj
    exact hall j (heq _ _ (he j) hj)
  rw [Matrix.det_apply,Finset.sum_eq_single (1 : Equiv.Perm ι)]
  · simp
  · intro σ hσ hne; rw [hp σ hne,smul_zero]
  · simp

/-- The creation leading determinant is one at every level and joint label. -/
theorem creationTopMatrix_det (k : ℂ) (n : ℕ) (c : ℤ) : (creationTopMatrix k n c).det=1 := by
  rw [det_weight_triangular _ (fun i => occupationBosons i.val)
    (creationTopMatrix_zero k n c) (fun i j he hn => by
      rw [creationTopMatrix_equal_bosons k n c i j he,if_neg hn])]
  simp [creationTopMatrix_equal_bosons]

/-- The positive leading determinant is its exact nonzero oscillator product. -/
theorem rowTopMatrix_det (k : ℂ) (n : ℕ) (c : ℤ) :
    (rowTopMatrix k n c).det=∏ i : JointIndex n c,derivativeMultiplier k i.val.toMultiset.toList.reverse 0 := by
  rw [← Matrix.det_transpose (rowTopMatrix k n c)]
  change Matrix.det (fun i j => rowTopMatrix k n c j i)=_
  rw [det_weight_triangular _ (fun i => occupationBosons i.val)
    (fun i j hij => rowTopMatrix_zero k n c j i hij) (fun i j he hn => by
      change rowTopMatrix k n c j i=0
      rw [rowTopMatrix_equal_bosons k n c j i he.symm,if_neg (Ne.symm hn)])]
  apply Finset.prod_congr rfl
  intro i hi
  simp [rowTopMatrix_equal_bosons]

/-- No top adjoint determinant vanishes away from critical level. -/
theorem rowTopMatrix_det_ne_zero (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ) :
    (rowTopMatrix k n c).det≠0 := by
  rw [rowTopMatrix_det]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => derivativeMultiplier_ne_zero k hk _ _)

end
end VOA.Wak.Charged
