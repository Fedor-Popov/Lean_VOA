/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2CreationWeightLeading

/-!
# Triangular boson symbols of highest-weight-leading adjoint words

In the highest-weight-leading part of an adjoint creation word, each charged
letter is an actual oscillator derivative. A neutral letter is its boson
derivative plus a beta-gamma term, which removes one fewer boson. The full
word error therefore has strictly higher remaining boson degree.
-/
namespace VOA.Wak.Charged
open MvPolynomial
open AffineVOA.NormalOrdering (currentWord)
noncomputable section

/-- Scalar multiplying the oscillator derivative in an adjoint leading
letter. The minus sign on beta derivatives comes from the gamma convention. -/
def annihilationWeight (k : ℂ) (v : Fin 3×ℕ) : ℂ :=
  if v.1=0 then -1 else if v.1=1 then 1 else 2*(k+2)*(v.2+1)

/-- Pure oscillator derivative in the adjoint leading letter. -/
def pureAnnihilation (k : ℂ) (v : Fin 3×ℕ) : Module.End ℂ WakFock :=
  annihilationWeight k v • dV v

/-- Actual highest-weight-leading adjoint of one indexed creation mode. -/
def leadingAnnihilation (k : ℂ) (v : Fin 3×ℕ) : Module.End ℂ WakFock :=
  let an := adjointLetter (lowerLetter v)
  leadingCurrent k an.1 an.2

/-- The actual leading adjoint differs from its oscillator derivative only
by a beta-gamma term for neutral colour. -/
theorem leadingAnnihilation_eq (k : ℂ) (v : Fin 3×ℕ) :
    leadingAnnihilation k v=if v.1=2 then
      (-2 : ℂ) • BG ((v.2 : ℤ)+1)+pureAnnihilation k v else pureAnnihilation k v := by
  rcases v with ⟨a,j⟩
  fin_cases a
  · simp [leadingAnnihilation,adjointLetter,lowerLetter,leadingCurrent,
      pureAnnihilation,annihilationWeight,Gam_of_pos (show 0<(j : ℤ)+1 by omega)]
    rw [Gam_of_pos (show 0<1+(j : ℤ) by omega)]
    simp [bD,dV]
  · simp [leadingAnnihilation,adjointLetter,lowerLetter,leadingCurrent,J_E,Ecur,
      pureAnnihilation,annihilationWeight,Bet_of_nonneg (show 0≤(j : ℤ) by omega)]
    simp [cD,dV]
  · simp [leadingAnnihilation,adjointLetter,lowerLetter,leadingCurrent,J_H,H,Hcur,
      pureAnnihilation,annihilationWeight,Aos_of_nonneg k (show 0≤(j : ℤ)+1 by omega)]
    rw [Aos_of_nonneg k (show 0≤1+(j : ℤ) by omega)]
    simp [aD,dV,add_comm]

/-- Pure derivatives lower the boson-count lower bound by exactly one for
neutral colour and zero for charged colour. -/
theorem pureAnnihilation_mem (k : ℂ) (v : Fin 3×ℕ) {d : ℤ} {P : WakFock}
    (hP : P∈bosonAtLeast 1 d) :
    pureAnnihilation k v P∈bosonAtLeast 1 (d-(if v.1=2 then 1 else 0)) := by
  rw [pureAnnihilation,LinearMap.smul_apply,dV_apply]
  apply Submodule.smul_mem
  simpa [bosonWeight] using boson_pderiv 1 v hP

/-- The actual leading adjoint has the same lower bound: its beta-gamma
correction preserves boson count and hence satisfies the weaker estimate. -/
theorem leadingAnnihilation_mem (k : ℂ) (v : Fin 3×ℕ) {d : ℤ} {P : WakFock}
    (hP : P∈bosonAtLeast 1 d) :
    leadingAnnihilation k v P∈bosonAtLeast 1 (d-(if v.1=2 then 1 else 0)) := by
  rw [leadingAnnihilation_eq]
  split_ifs with hv
  · rw [LinearMap.add_apply,LinearMap.smul_apply]
    apply Submodule.add_mem
    · apply bosonAtLeast_mono 1 (show d-1≤d by omega)
      exact Submodule.smul_mem _ _ (boson_BG 1 _ hP)
    · simpa [hv] using pureAnnihilation_mem k v hP
  · simpa [hv] using pureAnnihilation_mem k v hP

/-- Literal product of the pure oscillator adjoints in a supplied order. -/
def pureAnnihilationWord (k : ℂ) : List (Fin 3×ℕ)→Module.End ℂ WakFock
  | [] => 1
  | v::w => pureAnnihilation k v*pureAnnihilationWord k w

/-- Literal actual leading adjoint word in a supplied order. Reversal is
performed explicitly when this is applied to the adjoint of a creation word. -/
def leadingAnnihilationWord (k : ℂ) : List (Fin 3×ℕ)→Module.End ℂ WakFock
  | [] => 1
  | v::w => leadingAnnihilation k v*leadingAnnihilationWord k w

/-- The entire pure adjoint removes at most its number of boson letters. -/
theorem pureAnnihilationWord_mem (k : ℂ) (w : List (Fin 3×ℕ)) {d : ℤ} {P : WakFock}
    (hP : P∈bosonAtLeast 1 d) :
    pureAnnihilationWord k w P∈bosonAtLeast 1 (d-(bosonCount w : ℤ)) := by
  induction w with
  | nil => simpa [pureAnnihilationWord,bosonCount] using hP
  | cons v w ih =>
    have hb := pureAnnihilation_mem k v ih
    change pureAnnihilation k v (pureAnnihilationWord k w P)∈_
    by_cases hv : v.1=2 <;> simpa [bosonCount,hv,sub_sub,add_comm] using hb

/-- The actual leading adjoint has the same global boson-removal bound. -/
theorem leadingAnnihilationWord_mem (k : ℂ) (w : List (Fin 3×ℕ)) {d : ℤ} {P : WakFock}
    (hP : P∈bosonAtLeast 1 d) :
    leadingAnnihilationWord k w P∈bosonAtLeast 1 (d-(bosonCount w : ℤ)) := by
  induction w with
  | nil => simpa [leadingAnnihilationWord,bosonCount] using hP
  | cons v w ih =>
    have hb := leadingAnnihilation_mem k v ih
    change leadingAnnihilation k v (leadingAnnihilationWord k w P)∈_
    by_cases hv : v.1=2 <;> simpa [bosonCount,hv,sub_sub,add_comm] using hb

/-- Every correction to the pure adjoint leaves at least one additional
boson. Equal-count constant coefficients therefore see only pure derivatives. -/
theorem leadingAnnihilationWord_error (k : ℂ) (w : List (Fin 3×ℕ)) {d : ℤ} {P : WakFock}
    (hP : P∈bosonAtLeast 1 d) :
    leadingAnnihilationWord k w P-pureAnnihilationWord k w P∈
      bosonAtLeast 1 (d-(bosonCount w : ℤ)+1) := by
  induction w with
  | nil => simp [leadingAnnihilationWord,pureAnnihilationWord,bosonCount]
  | cons v w ih =>
    let Q := pureAnnihilationWord k w P
    have hQ := pureAnnihilationWord_mem k w hP
    have he := leadingAnnihilation_mem k v ih
    have hd : leadingAnnihilationWord k (v::w) P-pureAnnihilationWord k (v::w) P=
        leadingAnnihilation k v (leadingAnnihilationWord k w P-Q)+
          (leadingAnnihilation k v Q-pureAnnihilation k v Q) := by
      simp only [leadingAnnihilationWord,pureAnnihilationWord,Module.End.mul_apply,map_sub,Q]
      abel
    rw [hd]
    by_cases hv : v.1=2
    · apply Submodule.add_mem
      · convert he using 1 <;> simp [bosonCount,hv,Q] <;> congr 1 <;> omega
      · rw [leadingAnnihilation_eq,if_pos hv,LinearMap.add_apply,LinearMap.smul_apply,
          add_sub_cancel_right]
        have hh := Submodule.smul_mem (bosonAtLeast 1 (d-(bosonCount w : ℤ)))
          (-2 : ℂ) (boson_BG 1 ((v.2 : ℤ)+1) hQ)
        convert hh using 1 <;> simp [bosonCount,hv,Q] <;> congr 1 <;> omega
    · apply Submodule.add_mem
      · simpa [bosonCount,hv] using he
      · rw [leadingAnnihilation_eq,if_neg hv,sub_self]
        exact Submodule.zero_mem _

/-- All pure derivative multipliers are nonzero at every noncritical level. -/
theorem annihilationWeight_ne_zero (k : ℂ) (hk : k+2≠0) (v : Fin 3×ℕ) :
    annihilationWeight k v≠0 := by
  unfold annihilationWeight
  split_ifs
  · norm_num
  · norm_num
  · exact mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ)≠0) hk)
      (by exact_mod_cast (show v.2+1≠0 by omega))

end
end VOA.Wak.Charged
