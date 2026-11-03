/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaBSA

/-!
# Nonvanishing of the generic Verma BSA source

The free-momentum family separates the terminal source by its highest
momentum coefficient. Only repeated L₋₁ contributes at that degree; every
other source summand has smaller degree. This uses the actual Verma module
and does not assume a singular-vector normalization formula.
-/
set_option maxHeartbeats 800000

namespace VOA.InverseDS.VirasoroVerma
open VirModule LeeYangWardClosure

/-- Lift an actual Verma state to its vector polynomial in the free momentum,
using the proved PBW basis. Evaluation recovers the actual Fock family map. -/
noncomputable def vermaPolynomialLift (ell p : ℂ) :
    Verma (3-24*ell^2) (p^2-2*ell*p) →ₗ[ℂ] PolynomialModule ℂ VermaFockFamily :=
  (vermaSortedBasis (3-24*ell^2) (p^2-2*ell*p)).constr ℂ
    (fun w => vermaWordPolynomial ell p w.val)

/-- The lift agrees with the defining word polynomial on ordered words. -/
theorem vermaPolynomialLift_sorted (ell p : ℂ) (w : {w : List ℕ // SortedWord w}) :
    vermaPolynomialLift ell p (negWord (3-24*ell^2) (p^2-2*ell*p) w.val)=
      vermaWordPolynomial ell p w.val := by
  rw [← vermaSortedBasis_apply]
  exact Module.Basis.constr_basis _ _ _ _

/-- Evaluation of the lift is the actual universal family map, on all states. -/
theorem vermaPolynomialLift_eval (ell p z : ℂ)
    (v : Verma (3-24*ell^2) (p^2-2*ell*p)) :
    PolynomialModule.eval z (vermaPolynomialLift ell p v)=vermaFockFamilyMap ell p z v := by
  have he : (PolynomialModule.eval z).comp (vermaPolynomialLift ell p)=vermaFockFamilyMap ell p z := by
    apply (vermaSortedBasis (3-24*ell^2) (p^2-2*ell*p)).ext
    intro w
    simpa [vermaSortedBasis_apply,vermaPolynomialLift_sorted] using
      vermaWordPolynomial_eval ell p z w.val
  exact LinearMap.congr_fun he v

/-- Equality of vector polynomials follows from equality of all evaluations. -/
theorem vermaPolynomial_eq_of_eval (f g : PolynomialModule ℂ VermaFockFamily)
    (he : ∀ z : ℂ, PolynomialModule.eval z f=PolynomialModule.eval z g) : f=g := by
  apply sub_eq_zero.mp
  apply polynomialModule_eq_zero_of_eval
  intro z
  rw [map_sub,he,sub_self]

/-- The lift also agrees with unsorted creation words. The argument compares
all evaluations, so no charge-dependent straightening choice is introduced. -/
theorem vermaPolynomialLift_word (ell p : ℂ) (w : List ℕ) :
    vermaPolynomialLift ell p (negWord (3-24*ell^2) (p^2-2*ell*p) w)=
      vermaWordPolynomial ell p w := by
  apply vermaPolynomial_eq_of_eval
  intro z
  rw [vermaPolynomialLift_eval,vermaWordPolynomial_eval]

/-- A creation mode acts on lifted polynomials by its constant term plus
one free-momentum factor times its linear term. -/
theorem vermaPolynomialLift_negative (ell p : ℂ) (i : ℕ)
    (v : Verma (3-24*ell^2) (p^2-2*ell*p)) :
    vermaPolynomialLift ell p (vermaMode _ _ (-(i:ℤ)-1) v)=
      PolynomialModule.map ℂ ((vermaFockFamilyData ell p 0).L (-(i:ℤ)-1))
        (vermaPolynomialLift ell p v)+
      (Polynomial.X : Polynomial ℂ) • PolynomialModule.map ℂ (vermaMomentumMode i)
        (vermaPolynomialLift ell p v) := by
  apply vermaPolynomial_eq_of_eval
  intro z
  rw [map_add,PolynomialModule.eval_smul,Polynomial.eval_X,
    PolynomialModule.eval_map',PolynomialModule.eval_map',vermaPolynomialLift_eval,
    vermaPolynomialLift_eval]
  change universalMap _ _ _ (vermaRho _ _ _ _)=_
  rw [universalMap_intertwines]
  change virMode (vermaFockFamilyRep ell p z) (-(i:ℤ)-1) _=_
  rw [vermaFockFamilyRep_mode,vermaFockFamily_negative_linear]
  rfl

/-- Taking a coefficient after a negative mode gives a constant-mode term
and the previous coefficient acted on by the momentum creation operator. -/
theorem vermaPolynomialLift_negative_coeff (ell p : ℂ) (i k : ℕ)
    (v : Verma (3-24*ell^2) (p^2-2*ell*p)) :
    vermaPolynomialLift ell p (vermaMode _ _ (-(i:ℤ)-1) v) k=
      (vermaFockFamilyData ell p 0).L (-(i:ℤ)-1) (vermaPolynomialLift ell p v k)+
      if 0<k then vermaMomentumMode i (vermaPolynomialLift ell p v (k-1)) else 0 := by
  rw [vermaPolynomialLift_negative,PolynomialModule.add_apply,polynomialModule_X_coeff,
    polynomialModule_map_coeff]
  split_ifs <;> simp [polynomialModule_map_coeff]



/-- Extract one free-momentum coefficient as a linear map on actual states. -/
noncomputable def vermaMomentumCoefficient (ell p : ℂ) (k : ℕ) :
    Verma (3-24*ell^2) (p^2-2*ell*p) →ₗ[ℂ] VermaFockFamily where
  toFun v := vermaPolynomialLift ell p v k
  map_add' a b := by rw [map_add]; rfl
  map_smul' a v := by simp only [map_smul,RingHom.id_apply]; rfl

/-- Recursion states have free-momentum degree at most their level. Every
source term applies just one negative mode to a strictly earlier state. -/
theorem vermaBSAState_momentum_above (ell p t : ℂ) (N r k : ℕ) (hk : r<k) :
    vermaMomentumCoefficient ell p k
      (vermaBSAState (3-24*ell^2) (p^2-2*ell*p) t N r)=0 := by
  induction r using Nat.strong_induction_on generalizing k with
  | h r ih =>
    by_cases hr : r=0
    · subst r
      rw [vermaBSAState_zero]
      change vermaPolynomialLift ell p (negWord _ _ []) k=0
      rw [vermaPolynomialLift_word,vermaWordPolynomial_coeff_above ell p [] k (by simpa using hk)]
    · rw [vermaBSAState_eq_source _ _ _ N r (by omega),map_smul,vermaBSASource,map_sum]
      have he : (∑ j : Fin r, vermaMomentumCoefficient ell p k
          (vermaMode _ _ ((j:ℤ)-(r:ℤ)) (vermaBSAState _ _ t N j)))=0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hi : (j:ℤ)-(r:ℤ)=-((r-j-1:ℕ):ℤ)-1 := by omega
        rw [hi]
        change vermaPolynomialLift ell p (vermaMode _ _ _ _) k=0
        rw [vermaPolynomialLift_negative_coeff,if_pos (by omega)]
        have h1 := ih j j.isLt k (by omega)
        have h2 := ih j j.isLt (k-1) (by omega)
        change vermaPolynomialLift ell p _ k=0 at h1
        change vermaPolynomialLift ell p _ (k-1)=0 at h2
        rw [h1,h2,map_zero,map_zero,add_zero]
      rw [he,smul_zero]

/-- The scalar coefficient contributed by the all-L₋₁ path through the
recursion. Intermediate factors are nonzero for nonzero t and r<N. -/
noncomputable def vermaBSALeading (t : ℂ) (N : ℕ) : ℕ → ℂ
  | 0 => 1
  | r+1 => (-t/(((r:ℂ)+1)*((N:ℂ)-((r:ℂ)+1)))) * vermaBSALeading t N r

/-- The leading scalar is nonzero at every intermediate level. -/
theorem vermaBSALeading_ne_zero (t : ℂ) (N r : ℕ) (ht : t≠0) (hr : r<N) :
    vermaBSALeading t N r≠0 := by
  induction r with
  | zero => simp [vermaBSALeading]
  | succ r ih =>
    rw [vermaBSALeading]
    apply mul_ne_zero (div_ne_zero (neg_ne_zero.mpr ht) ?_) (ih (by omega))
    simpa using bsa_denominator_ne_zero N (r+1) (by omega) hr

/-- At the source's highest possible momentum degree, only its last term
survives. Projection turns that final L₋₁ into multiplication by X₀. -/
theorem vermaBSASource_momentum_top_step (ell p t : ℂ) (N r : ℕ) :
    vermaSymbolProjection (vermaMomentumCoefficient ell p (r+1)
      (vermaBSASource (3-24*ell^2) (p^2-2*ell*p) t N (r+1)))=
      MvPolynomial.X (0,0) * vermaSymbolProjection (vermaMomentumCoefficient ell p r
        (vermaBSAState (3-24*ell^2) (p^2-2*ell*p) t N r)) := by
  classical
  rw [vermaBSASource,map_sum,map_sum,Fin.sum_univ_castSucc]
  have hz : (∑ j : Fin r, vermaSymbolProjection (vermaMomentumCoefficient ell p (r+1)
      (vermaMode _ _ ((j:ℤ)-((r:ℤ)+1)) (vermaBSAState _ _ t N j))))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hi : (j:ℤ)-((r:ℤ)+1)=-((r-j:ℕ):ℤ)-1 := by omega
    rw [hi]
    change vermaSymbolProjection (vermaPolynomialLift ell p (vermaMode _ _ _ _) (r+1))=0
    rw [vermaPolynomialLift_negative_coeff,if_pos (by omega),Nat.add_sub_cancel]
    have h1 := vermaBSAState_momentum_above ell p t N j (r+1) (by omega)
    have h2 := vermaBSAState_momentum_above ell p t N j r j.isLt
    change vermaPolynomialLift ell p _ (r+1)=0 at h1
    change vermaPolynomialLift ell p _ r=0 at h2
    rw [h1,h2,map_zero,map_zero,add_zero,map_zero]
  simp only [Fin.val_castSucc,Fin.val_last,Nat.cast_add,Nat.cast_one] at *
  rw [hz,zero_add,show (r:ℤ)-((r:ℤ)+1)=-(0:ℤ)-1 by omega]
  change vermaSymbolProjection (vermaPolynomialLift ell p (vermaMode _ _ _ _) (r+1))=_
  have hc := vermaPolynomialLift_negative_coeff ell p 0 (r+1)
    (vermaBSAState (3-24*ell^2) (p^2-2*ell*p) t N r)
  simp only [Nat.cast_zero] at hc
  rw [hc,if_pos (by omega),Nat.add_sub_cancel]
  have hh := vermaBSAState_momentum_above ell p t N r (r+1) (by omega)
  change vermaPolynomialLift ell p _ (r+1)=0 at hh
  rw [hh,map_zero,zero_add,vermaSymbolProjection_momentum]
  rfl

/-- The top coefficient of each intermediate state is the nonzero all-L₋₁
path coefficient times a pure power of the first oscillator variable. -/
theorem vermaBSAState_momentum_top (ell p t : ℂ) (N r : ℕ) :
    vermaSymbolProjection (vermaMomentumCoefficient ell p r
      (vermaBSAState (3-24*ell^2) (p^2-2*ell*p) t N r))=
      vermaBSALeading t N r • MvPolynomial.X (0,0)^r := by
  induction r with
  | zero =>
    rw [vermaBSAState_zero]
    change vermaSymbolProjection (vermaPolynomialLift ell p (negWord _ _ []) 0)=_
    rw [vermaPolynomialLift_word]
    simp [vermaWordPolynomial,PolynomialModule.single_apply,vermaSymbolProjection_vacuum,
      vermaBSALeading]
  | succ r ih =>
    rw [vermaBSAState_eq_source _ _ _ N (r+1) (by omega),map_smul,map_smul,
      vermaBSASource_momentum_top_step,ih,vermaBSALeading]
    simp only [smul_smul,pow_succ]
    rw [mul_smul_comm,mul_comm (MvPolynomial.X (0,0))]
    simp only [smul_smul,Nat.cast_add,Nat.cast_one]

/-- The terminal source is nonzero in EVERY Verma module at every nonzero
t. This is stronger than the positive-mode identities and uses the genuine
free-momentum representation to exclude cancellation. -/
theorem vermaBSASource_ne_zero (c h t : ℂ) (N : ℕ) (ht : t≠0) (hN : 0<N) :
    vermaBSASource c h t N N≠0 := by
  obtain ⟨ell,p,hc,hh⟩ := exists_vermaFockFamily_parameters c h
  subst c
  subst h
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  intro he
  have hh := vermaBSASource_momentum_top_step ell p t (r+1) r
  rw [he,map_zero,map_zero,vermaBSAState_momentum_top] at hh
  have hn : (MvPolynomial.X (0,0) : MvPolynomial (ℕ × Fin 1) ℂ)≠0 := MvPolynomial.X_ne_zero _
  have hs := vermaBSALeading_ne_zero t (r+1) r ht (by omega)
  exact (mul_ne_zero hn (smul_ne_zero hs (pow_ne_zero r hn))) hh.symm



/-- A genuine nonzero singular state on the full (1,N) Verma curve for
all nonzero t and N at least three. Its level and every highest-weight
equation are proved. Survival in a vacuum quotient is not asserted. -/
theorem vermaBSA_nonzero_highest (t : ℂ) (N : ℕ) (ht : t≠0) (hN : 3≤N) :
    ∃ v : Verma (vermaBSACharge t) (vermaBSAWeight N t),
      v≠0 ∧ v∈sortedSpan (vermaBSACharge t) (vermaBSAWeight N t) N ∧
      IsHighestWeightVector (vermaRep (vermaBSACharge t) (vermaBSAWeight N t)) v
        (vermaBSACharge t) (vermaBSAWeight N t+N) := by
  refine ⟨vermaBSASource _ _ t N N,vermaBSASource_ne_zero _ _ t N ht (by omega),
    vermaBSASource_mem_level _ _ t N N,rfl,vermaBSASource_positive_terminal t N ht hN,?_⟩
  exact vermaBSASource_L0 _ _ t N N (fun j => vermaBSAState_L0 _ _ t N j)

end VOA.InverseDS.VirasoroVerma
