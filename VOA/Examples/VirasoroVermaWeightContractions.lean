/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaGramDegree

/-!
# Leading highest-weight contractions in actual Verma pairings

Count a highest-weight power twice and a remaining negative mode once.
Positive modes increase this count by at most one. Their leading action
retains only opposite-mode brackets producing 2m times the highest weight;
all other terms have lower count. This controls every discarded term in
comparison with the actual polynomial action.
-/
namespace VOA.InverseDS.VirasoroVerma
open Polynomial VirModule
open scoped Classical

/-- Polynomial word expressions of weighted degree at most d. Each highest-weight
power counts twice and each remaining creation operator counts once. The span formulation
keeps the estimate valid when different contributions cancel. -/
noncomputable def vermaContractionFiltration (d : ℕ) :
    Submodule ℂ (VermaPolynomialForm (Polynomial ℂ)) :=
  Submodule.span ℂ {f | ∃ k : ℕ, ∃ w : List ℕ,
    2*k+w.length≤d ∧ f=Finsupp.single w (X^k)}

/-- A larger filtration bound permits every expression allowed by the smaller one. -/
theorem vermaContractionFiltration_mono {d e : ℕ} (h : d≤e) :
    vermaContractionFiltration d≤vermaContractionFiltration e :=
  Submodule.span_mono (by rintro f ⟨k,w,hw,rfl⟩; exact ⟨k,w,hw.trans h,rfl⟩)

/-- A scalar multiple of a single highest-weight monomial has the expected
filtration bound. The scalar is complex and independent of highest weight. -/
theorem vermaContractionFiltration_single (k : ℕ) (w : List ℕ) (a : ℂ)
    {d : ℕ} (h : 2*k+w.length≤d) :
    Finsupp.single w (a • (X^k : Polynomial ℂ))∈vermaContractionFiltration d := by
  have hm : Finsupp.single w (X^k : Polynomial ℂ)∈vermaContractionFiltration d :=
    Submodule.subset_span ⟨k,w,h,rfl⟩
  simpa only [Finsupp.smul_single] using (vermaContractionFiltration d).smul_mem a hm

/-- Prefixing one negative mode increases the permitted creation length by one. -/
theorem vermaContractionFiltration_prepend (i : ℕ) {d : ℕ}
    {f : VermaPolynomialForm (Polynomial ℂ)} (h : f∈vermaContractionFiltration d) :
    polynomialPrepend i f∈vermaContractionFiltration (d+1) := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k,w,hw,rfl⟩ := hf
    simp only [polynomialPrepend,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
    simpa only [one_smul] using vermaContractionFiltration_single k (i::w) 1 (by simp only [List.length_cons]; omega)
  | zero => simp
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [LinearMap.map_smul_of_tower] using Submodule.smul_mem _ a hf

/-- Multiplication by p powers of highest weight increases the filtration
bound by twice p, for arbitrary finite polynomial word expressions. -/
theorem vermaContractionFiltration_shift (p : ℕ) {d : ℕ}
    {f : VermaPolynomialForm (Polynomial ℂ)} (h : f∈vermaContractionFiltration d) :
    (X^p : Polynomial ℂ) • f∈vermaContractionFiltration (2*p+d) := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k,w,hw,rfl⟩ := hf
    rw [Finsupp.smul_single,smul_eq_mul,← pow_add]
    simpa only [one_smul] using vermaContractionFiltration_single (p+k) w 1 (by omega)
  | zero => simp
  | add f g _ _ hf hg => simpa only [smul_add] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [smul_comm (X^p : Polynomial ℂ) a] using Submodule.smul_mem _ a hf

/-- A negative mode simply prefixes its creation index in the polynomial
word algorithm, including the translation mode L₋₁. -/
theorem vermaModePolynomial_negative (c : ℂ) (m : ℤ) (hm : m<0) (w : List ℕ) :
    vermaModePolynomial (Polynomial.C c) X m w=
      Finsupp.single ((-m-1).toNat::w) 1 := by
  cases w <;> simp [vermaModePolynomial,hm]

/-- L₀ acts on a word by highest weight plus its relative energy, already
as a polynomial word expression. This exposes its leading X term exactly. -/
theorem vermaModePolynomial_zero (c : ℂ) (w : List ℕ) :
    vermaModePolynomial (Polynomial.C c) X 0 w=
      Finsupp.single w (X+Polynomial.C (energyHW w : ℂ)) := by
  induction w with
  | nil => simp [vermaModePolynomial,energyHW_nil]
  | cons i w ih =>
    have hn : (0:ℤ)-(i:ℤ)-1<0 := by omega
    have hi : (-(0-(i:ℤ)-1)-1).toNat=i := by omega
    rw [vermaModePolynomial,if_neg (by omega : ¬(0:ℤ)<0),ih,
      vermaModePolynomial_negative c _ hn,if_neg (by omega : ¬(0:ℤ)-(i:ℤ)-1=0)]
    simp only [hi,polynomialPrepend,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,
      Finsupp.smul_single,smul_eq_mul,mul_one,add_zero,← Finsupp.single_add,
      energyHW_cons]
    congr 1
    simp only [Int.cast_zero,zero_add,Nat.cast_add,Nat.cast_one,algebraMap_eq,map_add,map_one]
    ring

/-- Every nonzero mode raises the weighted filtration by at most one;
L₀ raises it by at most two through multiplication by highest weight. -/
theorem vermaModePolynomial_contractionFiltration (c : ℂ) (m : ℤ) (w : List ℕ) :
    vermaModePolynomial (Polynomial.C c) X m w∈
      vermaContractionFiltration (w.length+if m=0 then 2 else 1) := by
  induction w generalizing m with
  | nil =>
    by_cases hm : m<0
    · rw [vermaModePolynomial_negative c m hm]
      simpa only [pow_zero,one_smul,if_neg (by omega : m≠0)] using
        vermaContractionFiltration_single 0 [(-m-1).toNat] 1 (by simp)
    · by_cases hz : m=0
      · subst m
        rw [vermaModePolynomial_zero]
        simpa [energyHW_nil] using vermaContractionFiltration_single 1 [] 1 (by simp)
      · simp [vermaModePolynomial,hm,hz]
  | cons i w ih =>
    by_cases hz : m=0
    · subst m
      rw [vermaModePolynomial_zero,Finsupp.single_add]
      apply Submodule.add_mem
      · simpa only [pow_one,one_smul,ite_true] using
          vermaContractionFiltration_single 1 (i::w) 1 (by simp; omega)
      · simpa [Algebra.smul_def] using
          vermaContractionFiltration_single 0 (i::w) (energyHW (i::w) : ℂ) (by simp)
    · by_cases hm : m<0
      · rw [vermaModePolynomial_negative c m hm]
        simpa only [pow_zero,one_smul,if_neg hz] using
          vermaContractionFiltration_single 0 ((-m-1).toNat::i::w) 1 (by simp)
      · rw [vermaModePolynomial,if_neg hm,if_neg hz]
        apply Submodule.add_mem
        · apply Submodule.add_mem
          · simpa only [if_neg hz,List.length_cons] using
              vermaContractionFiltration_prepend i (ih m)
          · have hh := vermaContractionFiltration_mono
              (show w.length+(if m-(i:ℤ)-1=0 then 2 else 1)≤(i::w).length+1
                by simp only [List.length_cons]; split_ifs <;> omega) (ih _)
            simpa only [algebraMap_smul] using
              (vermaContractionFiltration _).smul_mem ((m:ℂ)+(i:ℂ)+1) hh
        · split_ifs
          · simpa [Algebra.smul_def,← map_mul] using
              vermaContractionFiltration_single 0 w ((((m:ℂ)^3-m)/12)*c) (by simp; omega)
          · exact Submodule.zero_mem _

/-- Keep only the highest-weight part of each opposite-mode contraction.
A matching positive mode removes one letter and contributes its bracket
coefficient times X. The remaining letters retain their original order. -/
noncomputable def vermaContractionNormal (m : ℤ) :
    List ℕ → VermaPolynomialForm (Polynomial ℂ)
  | [] => 0
  | i::w => polynomialPrepend i (vermaContractionNormal m w) +
      if m-(i:ℤ)-1=0 then
        Finsupp.single w ((algebraMap ℂ (Polynomial ℂ)) ((m:ℂ)+(i:ℂ)+1)*X) else 0

/-- The leading contraction algorithm attains at most one extra weighted
unit per positive mode. This estimate also holds at arbitrary mode indices. -/
theorem vermaContractionNormal_mem (m : ℤ) (w : List ℕ) :
    vermaContractionNormal m w∈vermaContractionFiltration (w.length+1) := by
  induction w with
  | nil => exact Submodule.zero_mem _
  | cons i w ih =>
    apply Submodule.add_mem
    · exact vermaContractionFiltration_prepend i ih
    · split_ifs
      · simpa only [pow_one,Algebra.smul_def] using
          vermaContractionFiltration_single 1 w ((m:ℂ)+(i:ℂ)+1) (by simp; omega)
      · exact Submodule.zero_mem _

/-- All terms discarded by leading contraction have at least one unit less
weighted degree. Opposite-mode L₀ brackets leave only the word energy after
their X term is removed; central terms and nonmatching brackets are lower. -/
theorem vermaModePolynomial_sub_contraction_mem (c : ℂ) (m : ℤ) (hm : 0<m)
    (w : List ℕ) :
    vermaModePolynomial (Polynomial.C c) X m w-vermaContractionNormal m w∈
      vermaContractionFiltration w.length := by
  induction w with
  | nil => simp [vermaModePolynomial,vermaContractionNormal,show ¬m<0 by omega,show m≠0 by omega]
  | cons i w ih =>
    by_cases hq : m-(i:ℤ)-1=0
    · have he : vermaModePolynomial (Polynomial.C c) X m (i::w)-vermaContractionNormal m (i::w)=
          polynomialPrepend i (vermaModePolynomial (Polynomial.C c) X m w-vermaContractionNormal m w)+
          (algebraMap ℂ (Polynomial ℂ)) ((m:ℂ)+(i:ℂ)+1) •
            Finsupp.single w (Polynomial.C (energyHW w : ℂ)) +
          Finsupp.single w ((algebraMap ℂ (Polynomial ℂ)) (((m:ℂ)^3-m)/12)*Polynomial.C c) := by
        simp only [vermaModePolynomial,if_neg (by omega : ¬m<0),vermaContractionNormal,
          hq,ite_true,vermaModePolynomial_zero,map_sub,Finsupp.single_add,smul_add,
          Finsupp.smul_single,smul_eq_mul]
        abel
      rw [he]
      apply Submodule.add_mem
      · apply Submodule.add_mem _ (vermaContractionFiltration_prepend i ih)
        rw [algebraMap_smul]
        apply Submodule.smul_mem
        simpa [Algebra.smul_def] using
          vermaContractionFiltration_single 0 w (energyHW w : ℂ) (by simp)
      · simpa [Algebra.smul_def,← map_mul] using
          vermaContractionFiltration_single 0 w ((((m:ℂ)^3-m)/12)*c) (by simp)
    · have he : vermaModePolynomial (Polynomial.C c) X m (i::w)-vermaContractionNormal m (i::w)=
          polynomialPrepend i (vermaModePolynomial (Polynomial.C c) X m w-vermaContractionNormal m w)+
          (algebraMap ℂ (Polynomial ℂ)) ((m:ℂ)+(i:ℂ)+1) •
            vermaModePolynomial (Polynomial.C c) X (m-(i:ℤ)-1) w := by
        simp only [vermaModePolynomial,if_neg (by omega : ¬m<0),vermaContractionNormal,
          if_neg hq,add_zero,map_sub]
        abel
      rw [he]
      apply Submodule.add_mem _ (vermaContractionFiltration_prepend i ih)
      rw [algebraMap_smul]
      exact Submodule.smul_mem _ _ (by simpa only [if_neg hq] using
        vermaModePolynomial_contractionFiltration c (m-(i:ℤ)-1) w)

/-- Extend leading contraction to all polynomial word expressions by polynomial
linearity. This is an explicitly defined auxiliary operator, not an assumed action. -/
noncomputable def vermaContractionAction (m : ℤ) :
    VermaPolynomialForm (Polynomial ℂ) →ₗ[Polynomial ℂ] VermaPolynomialForm (Polynomial ℂ) :=
  Finsupp.linearCombination (Polynomial ℂ) (vermaContractionNormal m)

/-- Every positive actual mode raises the weighted bound by at most one. -/
theorem polynomialModeAction_contractionFiltration (c : ℂ) (m : ℤ) (hm : 0<m)
    {d : ℕ} {f : VermaPolynomialForm (Polynomial ℂ)}
    (h : f∈vermaContractionFiltration d) :
    polynomialModeAction (Polynomial.C c) X m f∈vermaContractionFiltration (d+1) := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k,w,hw,rfl⟩ := hf
    rw [polynomialModeAction_single]
    have hh := vermaContractionFiltration_shift k
      (vermaModePolynomial_contractionFiltration c m w)
    apply vermaContractionFiltration_mono (show 2*k+(w.length+1)≤d+1 by omega)
    simpa only [if_neg (by omega : m≠0)] using hh
  | zero => simp
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [LinearMap.map_smul_of_tower] using Submodule.smul_mem _ a hf

/-- Leading contractions obey the same upper bound on arbitrary inputs. -/
theorem vermaContractionAction_mem (m : ℤ) {d : ℕ}
    {f : VermaPolynomialForm (Polynomial ℂ)} (h : f∈vermaContractionFiltration d) :
    vermaContractionAction m f∈vermaContractionFiltration (d+1) := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k,w,hw,rfl⟩ := hf
    simp only [vermaContractionAction,Finsupp.linearCombination_single]
    exact vermaContractionFiltration_mono (by omega)
      (vermaContractionFiltration_shift k (vermaContractionNormal_mem m w))
  | zero => simp
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [LinearMap.map_smul_of_tower] using Submodule.smul_mem _ a hf

/-- Replacing one positive mode by its leading contraction leaves an error
that preserves, rather than raises, the input's weighted filtration. -/
theorem polynomialModeAction_sub_contraction_mem (c : ℂ) (m : ℤ) (hm : 0<m)
    {d : ℕ} {f : VermaPolynomialForm (Polynomial ℂ)}
    (h : f∈vermaContractionFiltration d) :
    polynomialModeAction (Polynomial.C c) X m f-vermaContractionAction m f∈
      vermaContractionFiltration d := by
  change (polynomialModeAction (Polynomial.C c) X m-vermaContractionAction m) f∈_
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k,w,hw,rfl⟩ := hf
    simp only [LinearMap.sub_apply,polynomialModeAction_single,vermaContractionAction,
      Finsupp.linearCombination_single,← smul_sub]
    exact vermaContractionFiltration_mono hw
      (vermaContractionFiltration_shift k (vermaModePolynomial_sub_contraction_mem c m hm w))
  | zero => simp
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [LinearMap.map_smul_of_tower] using Submodule.smul_mem _ a hf

/-- Extract the polynomial coefficient of the highest vector after constant
negative-word straightening. This is polynomial-linear, so differences and
scalar multiples can be compared before specializing highest weight. -/
noncomputable def vermaHighestPolynomial :
    VermaPolynomialForm (Polynomial ℂ) →ₗ[Polynomial ℂ] Polynomial ℂ :=
  Finsupp.linearCombination (Polynomial ℂ) (fun w =>
    Polynomial.C ((vermaSortedBasis 0 0).repr (negWord 0 0 w) ⟨[],sortedWord_nil⟩))

/-- The bundled highest-coordinate map is the coordinate used in the actual
universal pairing algorithm. -/
theorem vermaHighestPolynomial_apply (f : VermaPolynomialForm (Polynomial ℂ)) :
    vermaHighestPolynomial f=polynomialFormCoordinate f ⟨[],sortedWord_nil⟩ := rfl

/-- A weighted bound d gives highest-coordinate degree at most floor(d/2).
Creation terms cannot increase that bound when straightened. -/
theorem vermaHighestPolynomial_natDegree_le {d : ℕ}
    {f : VermaPolynomialForm (Polynomial ℂ)} (h : f∈vermaContractionFiltration d) :
    (vermaHighestPolynomial f).natDegree≤d/2 := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k,w,hw,rfl⟩ := hf
    simp only [vermaHighestPolynomial,Finsupp.linearCombination_single,smul_eq_mul]
    apply natDegree_mul_le.trans
    simpa using (show k≤d/2 by omega)
  | zero => simp
  | add f g _ _ hf hg =>
    rw [map_add]
    exact natDegree_add_le_of_degree_le hf hg
  | smul a f _ hf =>
    rw [LinearMap.map_smul_of_tower]
    exact (natDegree_smul_le _ _).trans hf

/-- Apply the opposite positive modes of a creation word, in adjoint order,
using the actual polynomial action. -/
noncomputable def vermaPositiveWord (c : ℂ) : List ℕ →
    VermaPolynomialForm (Polynomial ℂ) →ₗ[Polynomial ℂ] VermaPolynomialForm (Polynomial ℂ)
  | [] => LinearMap.id
  | i::u => (vermaPositiveWord c u).comp
      (polynomialModeAction (Polynomial.C c) X ((i:ℤ)+1))

/-- Apply the same opposite-mode word using only its leading contractions. -/
noncomputable def vermaContractionWord : List ℕ →
    VermaPolynomialForm (Polynomial ℂ) →ₗ[Polynomial ℂ] VermaPolynomialForm (Polynomial ℂ)
  | [] => LinearMap.id
  | i::u => (vermaContractionWord u).comp (vermaContractionAction ((i:ℤ)+1))

/-- The actual universal pairing is the highest coordinate after the
positive word action. Thus this comparison concerns actual Gram entries. -/
theorem vermaPairPolynomial_eq_highest (c : ℂ) (u : List ℕ)
    (f : VermaPolynomialForm (Polynomial ℂ)) :
    vermaPairPolynomial (Polynomial.C c) X u f=
      vermaHighestPolynomial (vermaPositiveWord c u f) := by
  induction u generalizing f with
  | nil => rfl
  | cons i u ih => exact ih _

/-- A positive word of length l raises the weighted bound by at most l. -/
theorem vermaPositiveWord_mem (c : ℂ) (u : List ℕ) {d : ℕ}
    {f : VermaPolynomialForm (Polynomial ℂ)} (h : f∈vermaContractionFiltration d) :
    vermaPositiveWord c u f∈vermaContractionFiltration (d+u.length) := by
  induction u generalizing d f with
  | nil => simpa [vermaPositiveWord] using h
  | cons i u ih =>
    simpa only [vermaPositiveWord,LinearMap.comp_apply,List.length_cons,Nat.add_right_comm] using
      ih (polynomialModeAction_contractionFiltration c ((i:ℤ)+1) (by omega) h)

/-- The leading contraction word obeys the same weighted upper bound. -/
theorem vermaContractionWord_mem (u : List ℕ) {d : ℕ}
    {f : VermaPolynomialForm (Polynomial ℂ)} (h : f∈vermaContractionFiltration d) :
    vermaContractionWord u f∈vermaContractionFiltration (d+u.length) := by
  induction u generalizing d f with
  | nil => simpa [vermaContractionWord] using h
  | cons i u ih =>
    simpa only [vermaContractionWord,LinearMap.comp_apply,List.length_cons,Nat.add_right_comm] using
      ih (vermaContractionAction_mem ((i:ℤ)+1) h)

/-- Replacing every positive mode by its leading contraction leaves a total
error at least one weighted unit below the maximal bound. The induction
retains errors at every stage, including their subsequent actual actions. -/
theorem vermaPositiveWord_sub_contractions_mem (c : ℂ) (u : List ℕ) {d : ℕ}
    {f : VermaPolynomialForm (Polynomial ℂ)} (h : f∈vermaContractionFiltration (d+1)) :
    vermaPositiveWord c u f-vermaContractionWord u f∈
      vermaContractionFiltration (d+u.length) := by
  induction u generalizing d f with
  | nil => simp [vermaPositiveWord,vermaContractionWord]
  | cons i u ih =>
    have he : vermaPositiveWord c (i::u) f-vermaContractionWord (i::u) f=
        vermaPositiveWord c u (polynomialModeAction (Polynomial.C c) X ((i:ℤ)+1) f-
          vermaContractionAction ((i:ℤ)+1) f)+
        (vermaPositiveWord c u (vermaContractionAction ((i:ℤ)+1) f)-
          vermaContractionWord u (vermaContractionAction ((i:ℤ)+1) f)) := by
      simp only [vermaPositiveWord,vermaContractionWord,LinearMap.comp_apply,map_sub]
      abel
    rw [he]
    apply Submodule.add_mem
    · simpa only [List.length_cons,Nat.add_right_comm] using
        vermaPositiveWord_mem c u (polynomialModeAction_sub_contraction_mem c ((i:ℤ)+1) (by omega) h)
    · simpa only [List.length_cons,Nat.add_right_comm] using
        ih (vermaContractionAction_mem ((i:ℤ)+1) h)

/-- For equally long words, the coefficient at maximal highest-weight degree
is computed entirely by the explicit leading contraction algorithm. All
nonmatching brackets, word-energy terms and central-charge terms vanish at
this degree. No Kac factorization or singular-vector assumption is involved. -/
theorem vermaPairPolynomial_top_eq_contractions (c : ℂ) (u v : List ℕ)
    (hlen : u.length=v.length) :
    (vermaPairPolynomial (Polynomial.C c) X u (Finsupp.single v 1)).coeff v.length=
      (vermaHighestPolynomial (vermaContractionWord u (Finsupp.single v 1))).coeff v.length := by
  by_cases hv : v.length=0
  · have hu : u=[] := List.length_eq_zero_iff.mp (hlen.trans hv)
    have hv' : v=[] := List.length_eq_zero_iff.mp hv
    subst u; subst v
    rfl
  · have hm : Finsupp.single v (1 : Polynomial ℂ)∈
        vermaContractionFiltration ((v.length-1)+1) := by
      simpa only [pow_zero,one_smul] using vermaContractionFiltration_single 0 v 1 (by omega)
    have he := vermaPositiveWord_sub_contractions_mem c u hm
    have hb := vermaHighestPolynomial_natDegree_le he
    have hz := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hb
      (show (v.length-1+u.length)/2<v.length by omega))
    rw [map_sub,coeff_sub] at hz
    rw [vermaPairPolynomial_eq_highest]
    exact sub_eq_zero.mp hz

/-- Every equal-length block of the actual Verma top matrix is given by
leading contractions and is therefore independent of central charge. -/
theorem vermaWeightTopMatrix_eq_contractions (c : ℂ) (n : ℕ)
    (i j : VermaPartitions n) (hlen : i.val.length=j.val.length) :
    vermaWeightTopMatrix c n i j=
      (vermaHighestPolynomial (vermaContractionWord i.val (Finsupp.single j.val 1))).coeff j.val.length :=
  vermaPairPolynomial_top_eq_contractions c i.val j.val hlen

/-- Changing central charge leaves the equal-length leading Gram blocks
unchanged. The lower-degree coefficients still depend on central charge. -/
theorem vermaWeightTopMatrix_charge_independent (c c' : ℂ) (n : ℕ)
    (i j : VermaPartitions n) (hlen : i.val.length=j.val.length) :
    vermaWeightTopMatrix c n i j=vermaWeightTopMatrix c' n i j := by
  rw [vermaWeightTopMatrix_eq_contractions c n i j hlen,
    vermaWeightTopMatrix_eq_contractions c' n i j hlen]

end VOA.InverseDS.VirasoroVerma
