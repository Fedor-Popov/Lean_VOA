/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2DiagramGramRoots
import VOA.Examples.AffineSl2WakimotoLiLeading

/-!
# Shifted loop embeddings in actual vacuum Fock representations

For d at least two, E_n maps to E_(dn+1), F_n to F_(dn-1), and H_n to
H_(dn) plus the original level at zero. The new level is d times the old
level and the new highest weight is the old level. Every highest-weight
creation letter, including F_0, becomes strictly negative. This permits use
of the already proved vacuum word independence in tensor constructions.
-/
namespace VOA.Wak.Charged
open Module (End)
open MvPolynomial AffineVOA
open AffineVOA.HighestNormalOrdering
open AffineVOA.NormalOrdering (currentWord)
noncomputable section

/-- Shifted loop currents on the actual level-a vacuum Fock carrier. -/
def shiftedJ (d : ℕ) (a : ℂ) (b : Fin 3) (n : ℤ) : End ℂ WakFock :=
  if b=0 then Ecur ((d : ℤ)*n+1) else if b=1 then F a 0 ((d : ℤ)*n-1) else
    H a 0 ((d : ℤ)*n)+if n=0 then a • (1 : End ℂ WakFock) else 0

/-- The shifted raising current. -/
theorem shiftedJ_E (d : ℕ) (a : ℂ) (n : ℤ) :
    shiftedJ d a 0 n=Ecur ((d : ℤ)*n+1) := by simp [shiftedJ]

/-- The shifted lowering current, with F_0 mapped to a negative mode. -/
theorem shiftedJ_F (d : ℕ) (a : ℂ) (n : ℤ) :
    shiftedJ d a 1 n=F a 0 ((d : ℤ)*n-1) := by norm_num [shiftedJ]

/-- The shifted Cartan current includes its necessary central correction. -/
theorem shiftedJ_H (d : ℕ) (a : ℂ) (n : ℤ) :
    shiftedJ d a 2 n=H a 0 ((d : ℤ)*n)+if n=0 then a • (1 : End ℂ WakFock) else 0 := by
  norm_num [shiftedJ,Fin.ext_iff]

set_option maxHeartbeats 1000000 in
/-- Actual affine commutators of the shifted currents. Loop dilation
multiplies the central level by d, while the mode shift forces the H_0 term. -/
theorem shiftedJ_comm (d : ℕ) (hd : 0<d) (a : ℂ) (ha : a+2≠0)
    (b c : Fin 3) (m n : ℤ) :
    ⁅shiftedJ d a b m,shiftedJ d a c n⁆=
      (∑ e,fabc b c e • shiftedJ d a e (m+n))+
      if m+n=0 then ((m : ℂ)*((d : ℂ)*a)*kappa b c) • (1 : End ℂ WakFock) else 0 := by
  have hd0 : (d : ℤ)≠0 := by exact_mod_cast (ne_of_gt hd)
  have hz : (d : ℤ)*(m+n)=0 ↔ m+n=0 := by exact mul_eq_zero_iff_left hd0
  have hs (z : ℂ) (T : End ℂ WakFock) : ⁅T,z • (1 : End ℂ WakFock)⁆=0 := by
    rw [lie_swap,scalar_lie,neg_zero]
  have eF : ⁅Ecur ((d : ℤ)*m+1),F a 0 ((d : ℤ)*n-1)⁆=
      H a 0 ((d : ℤ)*(m+n))+
      if m+n=0 then (((d : ℂ)*(m : ℂ)+1)*a) • (1 : End ℂ WakFock) else 0 := by
    rw [ef,show (d : ℤ)*m+1+((d : ℤ)*n-1)=(d : ℤ)*(m+n) by ring]
    simp only [hz]
    push_cast
    rfl
  have fE : ⁅F a 0 ((d : ℤ)*m-1),Ecur ((d : ℤ)*n+1)⁆=
      -H a 0 ((d : ℤ)*(m+n))+
      if m+n=0 then (((d : ℂ)*(m : ℂ)-1)*a) • (1 : End ℂ WakFock) else 0 := by
    rw [lie_swap,ef,show (d : ℤ)*n+1+((d : ℤ)*m-1)=(d : ℤ)*(m+n) by ring]
    simp only [hz]
    by_cases h : m+n=0
    · have hn : (n : ℂ)=-(m : ℂ) := by exact_mod_cast (show n= -m by omega)
      simp only [if_pos h,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_one,hn]
      module
    · simp only [if_neg h,add_zero]
  rcases fin3_cases b with rfl|rfl|rfl <;> rcases fin3_cases c with rfl|rfl|rfl <;>
    simp only [shiftedJ_E,shiftedJ_F,shiftedJ_H,Fin.sum_univ_three,fabc,kappa]
  · rw [rel_ee]; split_ifs <;> module
  · rw [eF]; split_ifs <;> module
  · simp only [lie_add]
    rw [lie_swap,he,show (d : ℤ)*n+((d : ℤ)*m+1)=(d : ℤ)*(m+n)+1 by ring]
    split_ifs <;> simp only [hs,lie_zero] <;> module
  · rw [fE]; split_ifs <;> module
  · rw [ff a 0 ha]; split_ifs <;> module
  · simp only [lie_add]
    rw [lie_swap,hf a 0 ha,show (d : ℤ)*n+((d : ℤ)*m-1)=(d : ℤ)*(m+n)-1 by ring]
    split_ifs <;> simp only [hs,lie_zero] <;> module
  · simp only [add_lie]
    rw [he,show (d : ℤ)*m+((d : ℤ)*n+1)=(d : ℤ)*(m+n)+1 by ring]
    split_ifs <;> simp only [scalar_lie,zero_lie] <;> module
  · simp only [add_lie]
    rw [hf a 0 ha,show (d : ℤ)*m+((d : ℤ)*n-1)=(d : ℤ)*(m+n)-1 by ring]
    split_ifs <;> simp only [scalar_lie,zero_lie] <;> module
  · simp only [add_lie,lie_add]
    rw [hh a 0 ha,show (d : ℤ)*m+(d : ℤ)*n=(d : ℤ)*(m+n) by ring]
    simp only [hz]
    push_cast
    split_ifs <;> simp only [scalar_lie,hs,zero_lie,lie_zero] <;> module

/-- Polynomial one is an ACTUAL highest vector of weight a for the shifted
level d*a action. The condition d>=2 handles the positive F_1 boundary. -/
theorem shiftedJ_one_highest (d : ℕ) (hd : 2≤d) (a : ℂ) (b : Fin 3) (n : ℤ)
    (hn : ¬IsLower b n) :
    shiftedJ d a b n (1 : WakFock)=if n=0 ∧ b=2 then a • (1 : WakFock) else 0 := by
  have hd' : (2 : ℤ)≤d := by exact_mod_cast hd
  have hn0 : 0≤n := by simp only [IsLower,not_or] at hn; omega
  rcases fin3_cases b with rfl|rfl|rfl
  · rw [shiftedJ_E,Ecur_one (by positivity),if_neg (by simp [Fin.ext_iff])]
  · have hp : 0<n := by by_contra h; exact hn (Or.inr ⟨by omega,rfl⟩)
    have hdn : 0<(d : ℤ)*n-1 := by nlinarith
    have he := J_one_positive a 0 1 _ hdn
    rw [J_F] at he
    rw [shiftedJ_F,he,if_neg (by simp [Fin.ext_iff])]
  · rw [shiftedJ_H]
    by_cases hz : n=0
    · subst n
      simp [H_one]
    · have hdn : 0<(d : ℤ)*n := mul_pos (by omega) (by omega)
      have hh := J_one_positive a 0 2 _ hdn
      rw [J_H] at hh
      simp only [if_neg hz,add_zero,hh]
      rw [if_neg (by simp [hz])]

/-- Literal loop-index transformation on current letters. -/
def shiftedLetter (d : ℕ) (an : Fin 3×ℤ) : Fin 3×ℤ :=
  (an.1,(d : ℤ)*an.2+colourCharge an.1)

/-- Every general highest creation letter becomes STRICTLY negative under
the shifted embedding. Thus horizontal lowering is covered by vacuum PBW. -/
theorem shiftedLetter_negative (d : ℕ) (hd : 2≤d) (an : Fin 3×ℤ)
    (hn : IsLower an.1 an.2) : (shiftedLetter d an).2<0 := by
  have hd' : (2 : ℤ)≤d := by exact_mod_cast hd
  rcases an with ⟨b,n⟩
  rcases fin3_cases b with rfl|rfl|rfl <;>
    norm_num [IsLower,shiftedLetter,colourCharge,Fin.ext_iff] at hn ⊢
  · nlinarith
  · have hn0 : n≤0 := by omega
    nlinarith
  · nlinarith

/-- On creation letters the central correction never occurs: the actual
shifted operator is exactly the original vacuum current at its new index. -/
theorem shiftedJ_lower (d : ℕ) (a : ℂ) (an : Fin 3×ℤ) (hn : IsLower an.1 an.2) :
    shiftedJ d a an.1 an.2=J a 0 (shiftedLetter d an).1 (shiftedLetter d an).2 := by
  rcases an with ⟨b,n⟩
  rcases fin3_cases b with rfl|rfl|rfl
  · simp [shiftedJ_E,shiftedLetter,colourCharge,J_E,Fin.ext_iff]
  · simp [shiftedJ_F,shiftedLetter,colourCharge,J_F,Fin.ext_iff,sub_eq_add_neg]
  · have hn0 : n≠0 := by norm_num [IsLower,Fin.ext_iff] at hn; omega
    simp [shiftedJ_H,shiftedLetter,colourCharge,J_H,Fin.ext_iff,hn0]

/-- Relabelling a literal word preserves its action whenever each of its
letters has the corresponding operator. This avoids unfolding any Fock formula. -/
theorem currentWord_map_eq {E : Type*} [AddCommGroup E] [Module ℂ E]
    (A B : Fin 3→ℤ→End ℂ E) (f : Fin 3×ℤ→Fin 3×ℤ) (w : List (Fin 3×ℤ))
    (hw : ∀ an∈w,A an.1 an.2=B (f an).1 (f an).2) :
    currentWord A w=currentWord B (w.map f) := by
  induction w with
  | nil => rfl
  | cons an w ih =>
      exact congrArg₂ (fun X Y : End ℂ E => X*Y) (hw an (by simp))
        (ih (fun bn hb => hw bn (by simp [hb])))

/-- Every shifted creation word is literally its strictly negative vacuum
word, with no discarded terms or assumptions on linear independence. -/
theorem shiftedWord_lower (d : ℕ) (a : ℂ) (w : List (Fin 3×ℤ))
    (hw : ∀ an∈w,IsLower an.1 an.2) :
    currentWord (shiftedJ d a) w=currentWord (J a 0) (w.map (shiftedLetter d)) :=
  currentWord_map_eq (shiftedJ d a) (J a 0) (shiftedLetter d) w
    (fun an han => shiftedJ_lower d a an (hw an han))

/-- Actual constant coefficient kills every nonempty shifted creation
word, and is one on the empty word. This is the tensor projection used later. -/
theorem constantCoeff_shifted_lower (d : ℕ) (hd : 2≤d) (a : ℂ) (w : List (Fin 3×ℤ))
    (hw : ∀ an∈w,IsLower an.1 an.2) :
    constantCoeff (currentWord (shiftedJ d a) w (1 : WakFock))=if w=[] then 1 else 0 := by
  rw [shiftedWord_lower d a w hw,constantCoeff_lower_word]
  · simp
  · intro bn hb
    obtain ⟨an,ha,rfl⟩ := List.mem_map.mp hb
    exact Or.inl (shiftedLetter_negative d hd an (hw an ha))

end
end VOA.Wak.Charged
