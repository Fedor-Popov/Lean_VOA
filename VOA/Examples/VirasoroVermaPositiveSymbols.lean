/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaDescendantSymbols
import VOA.Examples.VirasoroTopCoordinate
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Positive Virasoro modes on the leading PBW symbol

A positive mode preserves creation length. On the longest words it acts by
the derivation sending the variable for L_(-(i+1)) to (m+i+1) times the
variable for L_(-(i+1-m)), if i>=m, and to zero otherwise. Terms involving
highest weight, charge or a positive commutator have strictly shorter length.
The statements concern actual states through the faithful free-momentum lift.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule LeeYangFockExponential LeeYangFockVirasoro LeeYangWardClosure
open scoped Classical

/-- The degree-d projected free-momentum coefficient of an actual state,
as a linear map. At maximal creation length this is its PBW symbol. -/
noncomputable def vermaSymbol (ell p : ℂ) (d : ℕ) :
    Verma (3 - 24 * ell ^ 2) (p ^ 2 - 2 * ell * p) →ₗ[ℂ] MvPolynomial (ℕ × Fin 1) ℂ :=
  vermaSymbolProjection.comp (vermaMomentumCoefficient ell p d)

/-- The commutative monomial recording every creation index of a word. -/
noncomputable def vermaWordSymbol (w : List ℕ) : MvPolynomial (ℕ × Fin 1) ℂ :=
  MvPolynomial.monomial (vermaWordExponent w) 1

/-- Prefixing a creation word multiplies its symbol by the corresponding
oscillator variable; reordering has disappeared at this degree. -/
theorem vermaWordSymbol_cons (i : ℕ) (w : List ℕ) :
    vermaWordSymbol (i::w)=MvPolynomial.X (i,0)*vermaWordSymbol w := by
  simp [vermaWordSymbol,vermaWordExponent,MvPolynomial.monomial_single_add]

/-- The leading action of a positive mode is the derivation obtained from
its bracket with each creation generator. Index zero represents L_minus_one. -/
noncomputable def vermaLeadingDerivation (m : ℕ) :
    Derivation ℂ (MvPolynomial (ℕ × Fin 1) ℂ) (MvPolynomial (ℕ × Fin 1) ℂ) :=
  MvPolynomial.mkDerivation ℂ (fun i =>
    if m ≤ i.1 then ((m+i.1+1:ℕ):ℂ) • MvPolynomial.X (i.1-m,i.2) else 0)

/-- The leading derivation on one oscillator is precisely the negative-mode
part of the Virasoro bracket. No highest-weight or charge scalar appears. -/
theorem vermaLeadingDerivation_X (m i : ℕ) :
    vermaLeadingDerivation m (MvPolynomial.X (i,0))=
      if m ≤ i then ((m+i+1:ℕ):ℂ) • MvPolynomial.X (i-m,0) else 0 :=
  MvPolynomial.mkDerivation_X _ _ _

/-- Once the next momentum coefficient of a state vanishes, a creation
mode's next symbol is just multiplication by its oscillator variable. -/
theorem vermaSymbol_negative_top (ell p : ℂ) (i d : ℕ)
    (v : Verma (3 - 24 * ell ^ 2) (p ^ 2 - 2 * ell * p))
    (hv : vermaPolynomialLift ell p v (d+1)=0) :
    vermaSymbol ell p (d+1) (vermaMode _ _ (-(i:ℤ)-1) v)=
      MvPolynomial.X (i,0)*vermaSymbol ell p d v := by
  change vermaSymbolProjection (vermaPolynomialLift ell p _ (d+1))=_
  rw [vermaPolynomialLift_negative_coeff,hv,map_zero,zero_add,
    if_pos (by omega),Nat.add_sub_cancel,vermaSymbolProjection_momentum]
  rfl

/-- Scalar multiplication acts coefficientwise on the vector polynomial
lift. This keeps scalar and polynomial multiplication separate. -/
theorem vermaScalarPolynomial_coeff (a : ℂ) (q : PolynomialModule ℂ VermaFockFamily) (k : ℕ) :
    (a • q) k=a • q k := rfl

/-- Positive modes cannot increase the momentum degree of an actual word.
The proof tracks each commutator through its negative, zero or positive
case rather than assuming a filtered action on the module. -/
theorem vermaPositive_word_above (ell p : ℂ) (w : List ℕ) (m k : ℕ)
    (hm : 0 < m) (hk : w.length < k) :
    vermaPolynomialLift ell p (vermaMode _ _ (m:ℤ) (negWord _ _ w)) k=0 := by
  induction w generalizing m k with
  | nil =>
    rw [negWord_nil,show vermaMode _ _ (m:ℤ) (highestVector _ _)=0 from
      verma_pos_annihilate _ _ _ (by exact_mod_cast hm),map_zero]
    rfl
  | cons i w ih =>
    rw [negWord_cons,vermaMode_comm_apply,map_add,map_add,map_smul]
    simp only [PolynomialModule.add_apply,vermaScalarPolynomial_coeff,Int.cast_natCast,Int.cast_sub,Int.cast_neg,Int.cast_one]
    have hk' : w.length+1<k := hk
    rw [vermaPolynomialLift_negative_coeff,ih m k hm (by omega),map_zero,
      if_pos (by omega),ih m (k-1) hm (by omega),map_zero,zero_add]
    have hz : vermaPolynomialLift ell p
        (vermaMode _ _ ((m:ℤ)+(-(i:ℤ)-1)) (negWord _ _ w)) k=0 := by
      by_cases hmi : m ≤ i
      · have he : (m:ℤ)+(-(i:ℤ)-1)=-((i-m:ℕ):ℤ)-1 := by omega
        rw [he,← negWord_cons,vermaPolynomialLift_word,
          vermaWordPolynomial_coeff_above ell p ((i-m)::w) k hk']
      · by_cases heq : m=i+1
        · have he : (m:ℤ)+(-(i:ℤ)-1)=0 := by omega
          rw [he,vermaMode_zero_negWord,map_smul,vermaScalarPolynomial_coeff]
          change _ • vermaPolynomialLift ell p (negWord _ _ w) k=0
          rw [vermaPolynomialLift_word,vermaWordPolynomial_coeff_above ell p w k (by omega),smul_zero]
        · have he : (m:ℤ)+(-(i:ℤ)-1)=((m-i-1:ℕ):ℤ) := by omega
          rw [he]
          exact ih (m-i-1) k (by omega) (by omega)
    rw [zero_add]
    change _ • vermaPolynomialLift ell p _ k + _=0
    rw [hz,smul_zero,zero_add]
    split_ifs <;> simp only [LinearMap.smul_apply,Module.End.one_apply,zero_smul,map_zero,PolynomialModule.zero_apply]
    rw [map_smul,vermaScalarPolynomial_coeff]
    change _ • vermaPolynomialLift ell p (negWord _ _ w) k=0
    rw [vermaPolynomialLift_word,vermaWordPolynomial_coeff_above ell p w k (by omega),smul_zero]

/-- On the longest-degree coefficient of ANY creation word, the actual
positive mode is exactly the explicit commutative derivation. This is the
bridge from actual Ward equations to leading-symbol differential equations. -/
theorem vermaPositive_word_symbol (ell p : ℂ) (w : List ℕ) (m : ℕ) (hm : 0 < m) :
    vermaSymbol ell p w.length (vermaMode _ _ (m:ℤ) (negWord _ _ w))=
      vermaLeadingDerivation m (vermaWordSymbol w) := by
  induction w with
  | nil =>
    rw [negWord_nil,show vermaMode _ _ (m:ℤ) (highestVector _ _)=0 from
      verma_pos_annihilate _ _ _ (by exact_mod_cast hm),map_zero]
    simp [vermaWordSymbol,vermaWordExponent]
  | cons i w ih =>
    rw [negWord_cons,vermaMode_comm_apply,map_add,map_add,map_smul,
      List.length_cons,vermaSymbol_negative_top ell p i w.length _
        (vermaPositive_word_above ell p w m (w.length+1) hm (by omega)),ih]
    simp only [Int.cast_natCast,Int.cast_sub,Int.cast_neg,Int.cast_one]
    have hword : vermaSymbol ell p (w.length+1) (negWord _ _ w)=0 := by
      change vermaSymbolProjection (vermaPolynomialLift ell p _ (w.length+1))=0
      rw [vermaPolynomialLift_word,vermaWordPolynomial_coeff_above ell p w _ (by omega),map_zero]
    have hcentral : vermaSymbol ell p (w.length+1)
        (if (m:ℤ)+(-(i:ℤ)-1)=0 then
          ((((m:ℂ)^3-(m:ℂ))/12*(3 - 24 * ell ^ 2)) •
            (1 : Module.End ℂ (Verma (3 - 24 * ell ^ 2) (p ^ 2 - 2 * ell * p)))) (negWord _ _ w) else 0)=0 := by
      split_ifs <;> simp [hword]
    rw [hcentral,add_zero,vermaWordSymbol_cons,Derivation.leibniz,
      vermaLeadingDerivation_X]
    by_cases hmi : m ≤ i
    · have he : (m:ℤ)+(-(i:ℤ)-1)=-((i-m:ℕ):ℤ)-1 := by omega
      rw [if_pos hmi,he,vermaSymbol_negative_top ell p (i-m) w.length _
        (by rw [vermaPolynomialLift_word]; exact vermaWordPolynomial_coeff_above ell p w _ (by omega))]
      have hs : vermaSymbol ell p w.length (negWord _ _ w)=vermaWordSymbol w := by
        change vermaSymbolProjection (vermaPolynomialLift ell p _ w.length)=_
        rw [vermaPolynomialLift_word,vermaWordPolynomial_top]
        rfl
      rw [hs]
      have hc : (m:ℂ)-(-(i:ℂ)-1)=((m+i+1:ℕ):ℂ) := by push_cast; ring
      rw [hc]
      simp only [smul_eq_mul,smul_mul_assoc,mul_smul_comm,mul_comm]
    · rw [if_neg hmi,smul_zero,add_zero]
      simp only [smul_eq_mul]
      have hz : vermaSymbol ell p (w.length+1)
          (vermaMode _ _ ((m:ℤ)+(-(i:ℤ)-1)) (negWord _ _ w))=0 := by
        by_cases heq : m=i+1
        · have he : (m:ℤ)+(-(i:ℤ)-1)=0 := by omega
          rw [he,vermaMode_zero_negWord,map_smul,hword,smul_zero]
        · have he : (m:ℤ)+(-(i:ℤ)-1)=((m-i-1:ℕ):ℤ) := by omega
          rw [he]
          change vermaSymbolProjection (vermaPolynomialLift ell p _ (w.length+1))=0
          rw [vermaPositive_word_above ell p w (m-i-1) _ (by omega) (by omega),map_zero]
      rw [hz,smul_zero,add_zero]

end VOA.InverseDS.VirasoroVerma
