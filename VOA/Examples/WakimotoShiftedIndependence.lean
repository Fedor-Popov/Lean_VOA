/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2OccupationIndependence

/-!
# Independent general creation words in the shifted vacuum model

Dilation two maps E and F occupation depth j to vacuum depth 2j and H to
2j+1. The relabelling is injective, so the established vacuum symbol proof
applies to all general creation words, including arbitrary F_0 powers.
-/
namespace VOA.Wak.Charged
open Module (End)
open MvPolynomial
open AffineVOA.NormalOrdering (currentWord)
open AffineSl2PBWWakimotoReduction
noncomputable section

/-- The concrete vacuum depth map for dilation two. -/
def doubleDepth (v : Fin 3×ℕ) : Fin 3×ℕ :=
  (v.1,2*v.2+if v.1=2 then 1 else 0)

/-- Distinct general creation modes remain distinct after dilation two. -/
theorem doubleDepth_injective : Function.Injective doubleDepth := by
  intro v w h
  have hc := congrArg Prod.fst h
  have hd := congrArg Prod.snd h
  change v.1=w.1 at hc
  change 2*v.2+(if v.1=2 then 1 else 0)=2*w.2+(if w.1=2 then 1 else 0) at hd
  rw [hc] at hd
  exact Prod.ext hc (by omega)

/-- Zero highest-charge currents are the existing vacuum Wakimoto currents. -/
theorem J_zero_eq_Jw (k : ℂ) (a : Fin 3) (n : ℤ) : J k 0 a n=Jw k a n := by
  rcases fin3_cases a with rfl|rfl|rfl
  · rw [J_E,Jw_E]
  · rw [J_F,Jw_F]; simp [F]
  · rw [J_H,Jw_H]; simp [H]

/-- The actual loop letter at doubled depth agrees exactly with its
negative-vacuum index, including the general F_0 case. -/
theorem shifted_lowerLetter_two (v : Fin 3×ℕ) :
    shiftedLetter 2 (lowerLetter v)=((doubleDepth v).1,-((doubleDepth v).2 : ℤ)-1) := by
  rcases v with ⟨a,j⟩
  rcases fin3_cases a with rfl|rfl|rfl <;>
    norm_num [shiftedLetter,lowerLetter,doubleDepth,colourCharge,Fin.ext_iff] <;> ring

/-- Literal negative words in the zero-charge action are exactly the
already verified recursive Wakimoto vacuum words. -/
theorem negativeWord_eq_wakimoto (k : ℂ) (l : List (Fin 3×ℕ)) :
    currentWord (J k 0) (l.map (fun v => (v.1,-(v.2 : ℤ)-1))) (1 : WakFock)=
      wakimotoWordState k l := by
  induction l with
  | nil => rfl
  | cons v l ih =>
      rw [List.map_cons,currentWord,Module.End.mul_apply,ih,J_zero_eq_Jw]
      rfl

/-- The actual shifted general occupation word is a vacuum occupation word
under the injective double-depth map. No lower-order error is present. -/
theorem shiftedOccupationWord_two (k : ℂ) (d : Occupation) :
    currentWord (shiftedJ 2 k) (occupationWord d) (1 : WakFock)=
      wakimotoWordState k (relabelledWord doubleDepth d) := by
  rw [shiftedWord_lower 2 k _ (occupationWord_lower d),occupationWord,List.map_map]
  simp only [Function.comp_def,shifted_lowerLetter_two]
  simpa only [relabelledWord,List.map_map,Function.comp_def] using
    negativeWord_eq_wakimoto k (relabelledWord doubleDepth d)

/-- General highest-weight occupation words, including F_0, are ACTUALLY
independent in the shifted vacuum model at every original level. This is a
special family of highest representations, not yet the general Verma basis. -/
theorem shiftedOccupationWord_independent (k : ℂ) :
    LinearIndependent ℂ (fun d : Occupation => currentWord (shiftedJ 2 k) (occupationWord d) (1 : WakFock)) := by
  simp_rw [shiftedOccupationWord_two]
  exact wakimoto_relabelled_independent k doubleDepth doubleDepth_injective

end
end VOA.Wak.Charged
