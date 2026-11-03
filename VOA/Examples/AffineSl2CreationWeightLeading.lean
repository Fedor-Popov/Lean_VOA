/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2BosonFiltration

/-!
# Triangular boson symbols of highest-weight-leading creation words

After retaining the maximal highest-weight power, beta and gamma creation
letters are literal multiplications. A Cartan creation letter is boson
multiplication plus a beta-gamma correction of one smaller boson degree.
The statement below controls the whole actual operator word on arbitrary
inputs, so contractions and arbitrary occupation ordering are included.
-/
namespace VOA.Wak.Charged
open MvPolynomial
open AffineVOA.NormalOrdering (currentWord)
noncomputable section

/-- Number of boson-colour letters in a literal occupation list. -/
def bosonCount : List (Fin 3×ℕ)→ℕ
  | [] => 0
  | v::w => (if v.1=2 then 1 else 0)+bosonCount w

/-- Commutative oscillator monomial corresponding to a literal list,
before collecting repetitions into an occupation index. -/
def oscillatorMonomial : List (Fin 3×ℕ)→WakFock
  | [] => 1
  | v::w => X v*oscillatorMonomial w

/-- The highest-weight-leading operator attached to a creation index. -/
def leadingCreation (k : ℂ) (v : Fin 3×ℕ) : Module.End ℂ WakFock :=
  leadingCurrent k (lowerLetter v).1 (lowerLetter v).2

/-- Exact decomposition of a leading creation operator: its only correction
to oscillator multiplication is the neutral beta-gamma current. -/
theorem leadingCreation_eq (k : ℂ) (v : Fin 3×ℕ) :
    leadingCreation k v=if v.1=2 then
      (-2 : ℂ) • BG (-(v.2 : ℤ)-1)+mulL (X v) else mulL (X v) := by
  rcases v with ⟨a,j⟩
  fin_cases a
  · simp [leadingCreation,leadingCurrent,lowerLetter,J_E,Ecur,
      Bet_of_neg (show -(j : ℤ)-1≤-1 by omega),bV_of_pos (show 1≤-(-(j : ℤ)-1) by omega)]
    simp [bV]
  · simp [leadingCreation,leadingCurrent,lowerLetter,Gam_of_nonpos (show -(j : ℤ)≤0 by omega),
      cV_of_nonneg (show 0≤-(-(j : ℤ)) by omega)]
    simp [cV]
  · simp [leadingCreation,leadingCurrent,lowerLetter,J_H,H,Hcur,
      Aos_of_neg k (show -(j : ℤ)-1≤-1 by omega),
      aV_of_pos (show 1≤-(-(j : ℤ)-1) by omega)]
    simp [aV]

/-- Multiplying by the complete oscillator monomial raises boson degree by
exactly its boson count, expressed in the decreasing signed filtration. -/
theorem oscillatorMonomial_mem (w : List (Fin 3×ℕ)) {d : ℤ} {P : WakFock}
    (hP : P∈bosonAtLeast (-1) d) :
    oscillatorMonomial w*P∈bosonAtLeast (-1) (d-(bosonCount w : ℤ)) := by
  induction w with
  | nil => simpa [oscillatorMonomial,bosonCount] using hP
  | cons v w ih =>
    rw [oscillatorMonomial,mul_assoc]
    have hb := boson_X_mul (-1) v ih
    by_cases hv : v.1=2 <;>
      simpa [bosonWeight,bosonCount,hv,Int.natCast_add,sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using hb

/-- One actual leading creation operator increases the boson upper bound
by at most one for neutral colour and by zero for either charged colour. -/
theorem leadingCreation_mem (k : ℂ) (v : Fin 3×ℕ) {d : ℤ} {P : WakFock}
    (hP : P∈bosonAtLeast (-1) d) :
    leadingCreation k v P∈bosonAtLeast (-1) (d-(if v.1=2 then 1 else 0)) := by
  rw [leadingCreation_eq]
  by_cases hv : v.1=2
  · rw [if_pos hv,if_pos hv,LinearMap.add_apply,LinearMap.smul_apply,mulL_apply]
    apply Submodule.add_mem
    · apply bosonAtLeast_mono (-1) (show d-1≤d by omega)
      exact Submodule.smul_mem _ _ (boson_BG (-1) _ hP)
    · simpa [bosonWeight,hv] using boson_X_mul (-1) v hP
  · rw [if_neg hv,if_neg hv,mulL_apply,sub_zero]
    simpa [bosonWeight,hv] using boson_X_mul (-1) v hP

/-- Complete actual leading creation word in the original arbitrary order. -/
def leadingCreationWord (k : ℂ) : List (Fin 3×ℕ)→Module.End ℂ WakFock
  | [] => 1
  | v::w => leadingCreation k v*leadingCreationWord k w

/-- The entire actual leading word obeys its boson-count upper bound. -/
theorem leadingCreationWord_mem (k : ℂ) (w : List (Fin 3×ℕ)) {d : ℤ} {P : WakFock}
    (hP : P∈bosonAtLeast (-1) d) :
    leadingCreationWord k w P∈bosonAtLeast (-1) (d-(bosonCount w : ℤ)) := by
  induction w with
  | nil => simpa [leadingCreationWord,bosonCount] using hP
  | cons v w ih =>
    have hb := leadingCreation_mem k v ih
    change leadingCreation k v (leadingCreationWord k w P)∈_
    by_cases hv : v.1=2 <;> simpa [bosonCount,hv,sub_sub,add_comm] using hb

/-- All corrections to the pure oscillator product have strictly smaller
boson degree. This is an actual operator estimate on every filtered input. -/
theorem leadingCreationWord_error (k : ℂ) (w : List (Fin 3×ℕ)) {d : ℤ} {P : WakFock}
    (hP : P∈bosonAtLeast (-1) d) :
    leadingCreationWord k w P-oscillatorMonomial w*P∈
      bosonAtLeast (-1) (d-(bosonCount w : ℤ)+1) := by
  induction w with
  | nil => simp [leadingCreationWord,oscillatorMonomial,bosonCount]
  | cons v w ih =>
    let Q := oscillatorMonomial w*P
    have hQ := oscillatorMonomial_mem w hP
    have he := leadingCreation_mem k v ih
    have hd : leadingCreationWord k (v::w) P-oscillatorMonomial (v::w)*P=
        leadingCreation k v (leadingCreationWord k w P-Q)+
          (leadingCreation k v Q-X v*Q) := by
      simp only [leadingCreationWord,Module.End.mul_apply,oscillatorMonomial,map_sub,Q]
      ring
    rw [hd]
    by_cases hv : v.1=2
    · apply Submodule.add_mem
      · convert he using 1 <;> simp [bosonCount,hv,Q] <;> congr 1 <;> omega
      · rw [leadingCreation_eq,if_pos hv,LinearMap.add_apply,LinearMap.smul_apply,mulL_apply,
          add_sub_cancel_right]
        have hh := Submodule.smul_mem (bosonAtLeast (-1) (d-(bosonCount w : ℤ)))
          (-2 : ℂ) (boson_BG (-1) (-(v.2 : ℤ)-1) hQ)
        convert hh using 1 <;> simp [bosonCount,hv,Q] <;> congr 1 <;> omega
    · apply Submodule.add_mem
      · simpa [bosonCount,hv] using he
      · rw [leadingCreation_eq,if_neg hv,mulL_apply,sub_self]
        exact Submodule.zero_mem _

/-- The indexed leading word is exactly the original current-word top
operator after replacing each occupation index by its creation mode. -/
theorem leadingCreationWord_actual (k : ℂ) (w : List (Fin 3×ℕ)) :
    leadingCreationWord k w=currentWord (leadingCurrent k) (w.map lowerLetter) := by
  induction w with
  | nil => rfl
  | cons v w ih => simp only [leadingCreationWord,List.map_cons,currentWord,ih,leadingCreation]

end
end VOA.Wak.Charged
