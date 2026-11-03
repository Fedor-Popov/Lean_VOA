/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2OccupationIndependence

/-!
# Independent affine descendants of any nonzero Wakimoto polynomial

The minimum free-Li symbol of a current word is multiplication by its
classical symbol. The first nonzero homogeneous component of an arbitrary
starting polynomial therefore cannot destroy independence: the polynomial
ring is a domain. No highest-vector condition on that polynomial is used.
-/
namespace VOA.Wak.Charged
open MvPolynomial
open AffineSl2WakimotoLiLeading AffineSl2PBWWakimotoReduction
noncomputable section

/-- A coefficient support lower bound implies the actual free-Li filtration
bound, by the finite monomial expansion. -/
theorem mem_freeLiAtLeast_of_coeff (d : ℕ) (P : WakFock)
    (hP : ∀ e,coeff e P≠0 → d≤Finsupp.weight freeLiWeight e) : P∈freeLiAtLeast d := by
  rw [P.as_sum]
  apply Submodule.sum_mem
  intro e he
  have hh := (freeLiAtLeast d).smul_mem (coeff e P)
    (monomial_mem_freeLiAtLeast e (hP e (mem_support_iff.mp he)))
  simpa only [smul_monomial,smul_eq_mul,mul_one] using hh

/-- Every nonzero polynomial has an actual first nonzero free-Li component;
the remainder is strictly above it, even though some oscillator weights vanish. -/
theorem exists_first_freeLi_component (P : WakFock) (hP : P≠0) :
    ∃ d : ℕ,∃ Q : WakFock,Q≠0 ∧ IsWeightedHomogeneous freeLiWeight Q d ∧
      P∈freeLiAtLeast d ∧ P-Q∈freeLiAtLeast (d+1) := by
  classical
  have he : ∃ d : ℕ,∃ e,coeff e P≠0 ∧ Finsupp.weight freeLiWeight e=d := by
    obtain ⟨e,he⟩ := exists_coeff_ne_zero hP
    exact ⟨_,e,he,rfl⟩
  let d := Nat.find he
  obtain ⟨e,he0,heq⟩ := Nat.find_spec he
  let Q := weightedHomogeneousComponent freeLiWeight d P
  have hmin : ∀ f,coeff f P≠0 → d≤Finsupp.weight freeLiWeight f := by
    intro f hf
    exact Nat.find_min' he ⟨f,hf,rfl⟩
  have hQ : Q≠0 := by
    intro hz
    have hh := congrArg (coeff e) hz
    apply he0
    simpa only [Q,coeff_weightedHomogeneousComponent,heq,d,if_pos rfl,coeff_zero] using hh
  refine ⟨d,Q,hQ,?_,mem_freeLiAtLeast_of_coeff d P hmin,?_⟩
  · exact weightedHomogeneousComponent_isWeightedHomogeneous d P
  · apply mem_freeLiAtLeast_of_coeff
    intro f hf
    rw [coeff_sub] at hf
    change coeff f P-coeff f (weightedHomogeneousComponent freeLiWeight d P)≠0 at hf
    rw [coeff_weightedHomogeneousComponent] at hf
    by_cases hd : Finsupp.weight freeLiWeight f=d
    · simp [hd] at hf
    · simp only [if_neg hd,sub_zero] at hf
      have := hmin f hf
      omega

/-- Literal negative-current word acting on an arbitrary initial polynomial. -/
def negativeDescendant (k : ℂ) : List (Fin 3×ℕ)→WakFock→ₗ[ℂ]WakFock
  | [] => LinearMap.id
  | an::w => (Jw k an.1 (-(an.2 : ℤ)-1)).comp (negativeDescendant k w)

/-- Current words raise the minimum free-Li degree by their total depth. -/
theorem negativeDescendant_mem (k : ℂ) (w : List (Fin 3×ℕ)) {d : ℕ} {P : WakFock}
    (hP : P∈freeLiAtLeast d) : negativeDescendant k w P∈freeLiAtLeast (d+wordFreeLiDegree w) := by
  induction w with
  | nil => simpa [negativeDescendant] using hP
  | cons an w ih =>
      simpa [negativeDescendant,wordFreeLiDegree_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
        using Jw_neg_mem_freeLiAtLeast k an.1 an.2 ih

/-- The actual descendant differs from the product of classical current
symbols times the chosen initial component only above the expected degree. -/
theorem negativeDescendant_error (k : ℂ) (w : List (Fin 3×ℕ)) {d : ℕ} {P Q : WakFock}
    (hP : P∈freeLiAtLeast d) (herr : P-Q∈freeLiAtLeast (d+1)) :
    negativeDescendant k w P-classicalWordState k w*Q∈freeLiAtLeast (d+wordFreeLiDegree w+1) := by
  induction w with
  | nil => simpa [negativeDescendant,classicalWordState] using herr
  | cons an w ih =>
      have ha := Jw_sub_classical_mem_freeLiAtLeast k an.1 an.2 (negativeDescendant_mem k w hP)
      have hb := currentClassical_mul_mem_freeLiAtLeast k an.1 an.2 ih
      have ha' : Jw k an.1 (-(an.2 : ℤ)-1) (negativeDescendant k w P)-
          currentClassical k an.1 an.2*negativeDescendant k w P∈
          freeLiAtLeast (d+wordFreeLiDegree (an::w)+1) := by
        simpa [wordFreeLiDegree,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ha
      have hb' : currentClassical k an.1 an.2*(negativeDescendant k w P-classicalWordState k w*Q)∈
          freeLiAtLeast (d+wordFreeLiDegree (an::w)+1) := by
        simpa [wordFreeLiDegree,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb
      have hw : classicalWordState k (an::w)=currentClassical k an.1 an.2*classicalWordState k w := by cases an; rfl
      convert (freeLiAtLeast _).add_mem ha' hb' using 1 <;>
        simp only [negativeDescendant,LinearMap.comp_apply,hw] <;> ring

/-- Exact lowest-degree descendant symbol for an arbitrary initial leading
component, including every current contraction in the error estimate. -/
theorem negativeDescendant_component (k : ℂ) (w : List (Fin 3×ℕ)) {d : ℕ} {P Q : WakFock}
    (hP : P∈freeLiAtLeast d) (herr : P-Q∈freeLiAtLeast (d+1))
    (hQ : IsWeightedHomogeneous freeLiWeight Q d) :
    weightedHomogeneousComponent freeLiWeight (d+wordFreeLiDegree w) (negativeDescendant k w P)=
      classicalWordState k w*Q := by
  have he := weightedComponent_eq_zero_of_mem_freeLiAtLeast
    (negativeDescendant_error k w hP herr) (Nat.lt_succ_self _)
  have hh : IsWeightedHomogeneous freeLiWeight (classicalWordState k w*Q) (d+wordFreeLiDegree w) := by
    simpa only [Nat.add_comm] using (classicalWordState_isWeightedHomogeneous k w).mul hQ
  rw [map_sub,hh.weightedHomogeneousComponent_same,sub_eq_zero] at he
  exact he

/-- Injectively relabelled creation words acting on ANY nonzero Wakimoto
polynomial are linearly independent. Polynomial-domain cancellation is the
only extra nonvanishing input beyond the already proved classical injection. -/
theorem negativeDescendants_independent (k : ℂ) (f : Fin 3×ℕ→Fin 3×ℕ)
    (hf : Function.Injective f) (P : WakFock) (hP : P≠0) :
    LinearIndependent ℂ (fun e : Occupation => negativeDescendant k (relabelledWord f e) P) := by
  obtain ⟨d,Q,hQ0,hQ,hPd,herr⟩ := exists_first_freeLi_component P hP
  apply linearIndependent_of_lowerLeading (fun e => d+wordFreeLiDegree (relabelledWord f e))
    (fun e => negativeDescendant k (relabelledWord f e) P)
    (fun e => classicalWordState k (relabelledWord f e)*Q)
    (fun n => weightedHomogeneousComponent freeLiWeight n)
  · intro e; exact negativeDescendant_component k _ hPd herr hQ
  · intro e n hn
    exact weightedComponent_eq_zero_of_mem_freeLiAtLeast (negativeDescendant_mem k _ hPd) hn
  · have hi : Function.Injective (LinearMap.mulRight ℂ Q) := by
      intro A B he
      exact mul_right_cancel₀ hQ0 he
    exact (classical_relabelled_independent k f hf).map' (LinearMap.mulRight ℂ Q)
      (LinearMap.ker_eq_bot.mpr hi)

end
end VOA.Wak.Charged
