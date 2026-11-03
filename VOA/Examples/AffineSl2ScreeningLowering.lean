/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningLoweringCutoff

/-!
# Actual affine screening lowering annihilation

All finite beta and boson sums are identified with extracted integrands.
Weighted Vandermonde integration by parts and pair counting then cancel
these sums at the screening charge. No analytic screening premise is used.
-/
namespace VOA.Wak.Screening
open AddMonoidAlgebra VirasoroScreening MvPolynomial
open scoped BigOperators
noncomputable section

/-- The actual finite beta divided difference is symmetric in its variables. -/
theorem betaDivided_swap (r N : ℕ) (i j : Fin r) :
    betaDivided r N i j=betaDivided r N j i := by
  rw [betaDivided,betaDivided]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  rw [← Finset.sum_range_reflect (fun a => auxiliaryVariable r j^a*
    auxiliaryVariable r i^(d-a)) (d+1)]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' := Finset.mem_range.mp ha
  have he : d-(d+1-1-a)=a := by omega
  simp only [Nat.add_sub_cancel,he]
  rw [show d-(d-a)=a by omega,mul_comm]

/-- A symmetric ordered sum over distinct indices counts each unordered
pair exactly twice, in any additive commutative monoid. -/
theorem ordered_pair_sum {A : Type*} [AddCommMonoid A] (r : ℕ)
    (f : Fin r→Fin r→A) (hf : ∀ i j,f i j=f j i) :
    (∑ i : Fin r,∑ j∈Finset.univ.erase i,f i j)=
      2 • (∑ ij∈variablePairs r,f ij.1 ij.2) := by
  classical
  have he (i : Fin r) : (∑ j∈Finset.univ.erase i,f i j)=
      ∑ j : Fin r,((if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
    have hset : Finset.univ.filter (fun j : Fin r => j≠i)=Finset.univ.erase i := by
      ext j; simp
    rw [← hset,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    rcases lt_trichotomy i j with h|h|h
    · simp [h,ne_of_gt h,not_lt_of_ge h.le]
    · subst j; simp
    · simp [h,ne_of_lt h,not_lt_of_ge h.le]
  have he' (i : Fin r) : (∑ j∈Finset.univ.erase i,f i j)=
      (∑ j : Fin r,if i < j then f i j else 0)+
      (∑ j : Fin r,if j < i then f i j else 0) := by
    rw [he]
    simp only [← Finset.sum_add_distrib]
  simp_rw [he']
  rw [Finset.sum_add_distrib,Finset.sum_comm (f := fun i j : Fin r => if j < i then f i j else 0)]
  have hs : (∑ i : Fin r,∑ j : Fin r,if i < j then f j i else 0)=
      ∑ i : Fin r,∑ j : Fin r,if i < j then f i j else 0 := by
    simp_rw [hf]
  rw [hs,two_smul]
  congr 1 <;> simp only [variablePairs,Finset.sum_filter,← Finset.univ_product_univ,Finset.sum_product]

/-- The actual finite quadratic sum is twice the unordered extracted
beta divided-difference sum. -/
theorem state_quadratic_sum_unordered (r q M : ℕ) :
    (∑ d∈Finset.range (r*(q-1)+1),X (0,d)*
      ∑ a∈Finset.range (d+1),pderiv (0,d-a) (pderiv (0,a) (state r q M)))=
    (2 : ℂ) • (∑ ij∈variablePairs r,
      (betaDivided r (r*(q-1)) ij.1 ij.2*pairOmittedIntegrand r q M ij.1 ij.2)
        (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))) := by
  rw [state_quadratic_sum_selected]
  have h := ordered_pair_sum r (fun i j =>
    (betaDivided r (r*(q-1)) i j*pairOmittedIntegrand r q M i j)
      (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))) (fun i j => by
        dsimp only
        rw [betaDivided_swap r _ i j,pairOmittedIntegrand_swap r q M i j])
  simpa only [two_smul] using h

/-- After extraction, the divided and companion pair sums count every
single omission r-1 times, with the same complex scalar convention as IBP. -/
theorem selected_pair_cancellation (r q M : ℕ) :
    (∑ ij∈variablePairs r,
      (betaDivided r (r*(q-1)) ij.1 ij.2*pairOmittedIntegrand r q M ij.1 ij.2)
        (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))) +
    (∑ ij∈variablePairs r,
      (betaCompanion r (r*(q-1)) ij.1 ij.2*pairOmittedIntegrand r q M ij.1 ij.2)
        (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ)))=
    ((r-1 : ℕ) : ℂ) • (∑ i : Fin r,
      omittedIntegrand r q M i (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))) := by
  have h := congrArg (fun P : Auxiliary r => P
    (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))) (pair_divided_companion_sum r q M)
  dsimp only at h
  rw [auxiliary_sum_apply] at h
  have happ (P Q : Auxiliary r) (g : Fin r→ℤ) : (P+Q) g=P g+Q g := rfl
  simp_rw [add_mul,happ,Finset.sum_add_distrib] at h
  change _=(r-1) • ((∑ i : Fin r,omittedIntegrand r q M i)
    (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))) at h
  rw [auxiliary_sum_apply] at h
  simpa only [Nat.cast_smul_eq_nsmul] using h

/-- The ACTUAL charged lowering mode kills the finite screening vector at
the screening charge. All beta, boson and finite-boundary terms are included. -/
theorem state_lowering (r q M : ℕ) (hr : 0<r) (hq : 0<q)
    (k : ℂ) (hMk : (M : ℂ)*(k+2)=1) :
    Charged.F k ((q : ℂ)*(k+2)-(r : ℂ)-1) 1 (state r q M)=0 := by
  let g : Fin r→ℤ := fun _ => (((r-1)*M+q-1 : ℕ) : ℤ)
  let O := ∑ i : Fin r,omittedIntegrand r q M i g
  let B := ∑ i : Fin r,(bosonAuxiliarySeries r (r*(q-1)) i*omittedIntegrand r q M i) g
  let K := ∑ ij∈variablePairs r,
    (betaDivided r (r*(q-1)) ij.1 ij.2*pairOmittedIntegrand r q M ij.1 ij.2) g
  let V := ∑ ij∈variablePairs r,
    (betaCompanion r (r*(q-1)) ij.1 ij.2*pairOmittedIntegrand r q M ij.1 ij.2) g
  have hi : (M : ℂ) • B=(2*M : ℂ) • V-(((r-1)*M+q-1 : ℕ) : ℂ) • O :=
    summed_omitted_ibp r q M hq
  have hp : K+V=((r-1 : ℕ) : ℂ) • O := selected_pair_cancellation r q M
  rw [state_lowering_natural r q M hq k _ hMk,
    state_quadratic_sum_unordered,state_boson_sum_selected,state_beta_one_omissions]
  change -((2 : ℂ) • K)-B+(k-((q : ℂ)*(k+2)-(r : ℂ)-1)) • O=0
  have hm : (M : ℂ)≠0 := by intro hz; simp [hz] at hMk
  apply (smul_eq_zero.mp ?_).resolve_left hm
  have hL : (((r-1)*M+q-1 : ℕ) : ℂ)=((r : ℂ)-1)*M+q-1 := by
    rw [Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega)]
    norm_num
  rw [hL] at hi
  have hc : (M : ℂ)*(k-((q : ℂ)*(k+2)-(r : ℂ)-1))+
      (((r : ℂ)-1)*M+q-1)-2*M*((r : ℂ)-1)=0 := by
    linear_combination (1-(q : ℂ))*hMk
  have hp' : K+V=((r : ℂ)-1) • O := by
    simpa only [Nat.cast_sub (by omega : 1≤r),Nat.cast_one] using hp
  calc
    (M : ℂ) • (-((2 : ℂ) • K)-B+(k-((q : ℂ)*(k+2)-(r : ℂ)-1)) • O)=
      (-(2*M : ℂ)) • (K+V)+
        ((r-1 : ℂ)*M+q-1+M*(k-((q : ℂ)*(k+2)-(r : ℂ)-1))) • O := by
          rw [smul_add,smul_sub,smul_smul,hi]
          module
    _ = 0 := by
      rw [hp',smul_smul,← add_smul]
      have hz : -(2*(M : ℂ))*((r : ℂ)-1)+
          ((r-1 : ℂ)*M+q-1+M*(k-((q : ℂ)*(k+2)-(r : ℂ)-1)))=0 := by
        linear_combination hc
      rw [hz,zero_smul]

end
end VOA.Wak.Screening
