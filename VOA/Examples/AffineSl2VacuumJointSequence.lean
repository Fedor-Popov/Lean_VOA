/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2HorizontalFirstForm
import VOA.Examples.AffineSl2JointChargeFlip

/-!
# The actual vacuum exact sequence in each finite joint weight

The horizontal embedding preserves energy and shifts the relative root
charge down by one. Explicit lifts of the existing vacuum PBW words give
surjectivity in each simultaneous eigenspace, without a character formula.
-/
namespace VOA.AffineVOA.HighestModule
open Module (End)
open NormalOrdering (currentWord)
open HighestNormalOrdering
open AffineSl2PBWWakimotoReduction
open Wak.Charged (occupationWord lowerLetter wordEnergy wordCharge)
noncomputable section

/-- The horizontal embedding intertwines all actual Lie operators. -/
theorem horizontalEmbedding_intertwines (k : ℂ) (x : AffSl2) (v : Verma k (-2)) :
    horizontalEmbedding k (rho k (-2) x v)=rho k 0 x (horizontalEmbedding k v) :=
  universalMap_intertwines _ _ _ _ _

/-- The exact shift of actual joint eigenspaces under horizontal embedding.
Injectivity proves the converse as well as grade preservation. -/
theorem horizontalEmbedding_mem_joint_iff (k : ℂ) (n : ℕ) (c : ℤ) (v : Verma k (-2)) :
    horizontalEmbedding k v∈jointSpace k 0 n c ↔ v∈jointSpace k (-2) n (c+1) := by
  rw [mem_jointSpace_iff,mem_jointSpace_iff]
  have hc : (-2 : ℂ)+2*((c+1 : ℤ):ℂ)=0+2*(c : ℂ) := by push_cast; ring
  rw [hc]
  constructor
  · rintro ⟨hd,hh⟩
    constructor
    · apply horizontalEmbedding_injective k
      rw [horizontalEmbedding_intertwines,map_smul,hd]
    · apply horizontalEmbedding_injective k
      change horizontalEmbedding k (rho k (-2) (modeElement 2 0) v)=_
      rw [horizontalEmbedding_intertwines,map_smul]
      exact hh
  · rintro ⟨hd,hh⟩
    constructor
    · rw [← horizontalEmbedding_intertwines,hd,map_smul]
    · change rho k 0 (modeElement 2 0) (horizontalEmbedding k v)=_
      rw [← horizontalEmbedding_intertwines]
      change horizontalEmbedding k (mode k (-2) 2 0 v)=_
      rw [hh,map_smul]

/-- Relabel vacuum creation depths as Verma depths. The f-colour starts
at F_-1 in a vacuum word, so its Verma depth is increased by one. -/
def vacuumLiftIndex (an : Fin 3×ℕ) : Fin 3×ℕ :=
  (an.1,an.2+if an.1=1 then 1 else 0)

/-- Relabelling preserves the exact negative current mode. -/
theorem lowerLetter_vacuumLiftIndex (an : Fin 3×ℕ) :
    lowerLetter (vacuumLiftIndex an)=(an.1,-(an.2 : ℤ)-1) := by
  rcases an with ⟨a,n⟩
  by_cases ha : a=1 <;> simp [lowerLetter,vacuumLiftIndex,ha] <;> omega

/-- One fixed creation word lifting each existing vacuum PBW vector. -/
def vacuumLiftWord (mu : AffineSl2GeneralRigidity.CurrentIndex) : List (Fin 3×ℕ) :=
  (orderedPBWColorWord mu).map vacuumLiftIndex

/-- The relabelled word has exactly the literal vacuum creation indices. -/
theorem vacuumLiftWord_modes (mu : AffineSl2GeneralRigidity.CurrentIndex) :
    (vacuumLiftWord mu).map lowerLetter=
      (orderedPBWColorWord mu).map (fun an => (an.1,-(an.2 : ℤ)-1)) := by
  simp only [vacuumLiftWord,List.map_map,Function.comp_def,lowerLetter_vacuumLiftIndex]

/-- Its relative Verma energy is precisely the vacuum PBW energy. -/
theorem vacuumLiftWord_energy (mu : AffineSl2GeneralRigidity.CurrentIndex) :
    wordEnergy ((vacuumLiftWord mu).map lowerLetter)=AffineSl2GeneralRigidity.currentEnergy mu := by
  rw [vacuumLiftWord_modes]
  unfold AffineSl2GeneralRigidity.currentEnergy
  generalize orderedPBWColorWord mu=w
  change wordEnergy (w.map (fun an => (an.1,-(an.2 : ℤ)-1)))=wordDegA w
  induction w with
  | nil => rfl
  | cons an w ih =>
    change -(-(an.2 : ℤ)-1)+wordEnergy (w.map (fun bn => (bn.1,-(bn.2 : ℤ)-1)))=wordDegA (an::w)
    rw [ih,wordDegA_cons]
    omega

/-- The existing vacuum Cartan charge is twice the Verma root-charge
statistic, with the same e/f sign convention. -/
theorem vacuumLiftWord_charge (mu : AffineSl2GeneralRigidity.CurrentIndex) :
    2*wordCharge ((vacuumLiftWord mu).map lowerLetter)=AffineSl2GeneralRigidity.currentCharge mu := by
  rw [vacuumLiftWord_modes]
  change 2*wordCharge ((orderedPBWColorWord mu).map (fun an => (an.1,-(an.2 : ℤ)-1)))=
    Sl2NonLisse.wordCharge (orderedPBWColorWord mu)
  generalize orderedPBWColorWord mu=w
  induction w with
  | nil => rfl
  | cons an w ih =>
    simp only [wordCharge,List.map_cons,List.sum_cons,Sl2NonLisse.wordCharge_cons]
    have ha : 2*Wak.Charged.colourCharge an.1=Sl2NonLisse.colourCharge an.1 := by
      rcases an with ⟨a,n⟩
      fin_cases a <;> norm_num [Wak.Charged.colourCharge,Sl2NonLisse.colourCharge]
    change 2*(Wak.Charged.colourCharge an.1+wordCharge _)=_
    rw [mul_add,ha,ih]

/-- The literal Verma lift lies in the correct actual finite joint space
at every highest weight. -/
theorem vacuumLift_mem_joint (k h : ℂ) (n : ℕ) (c : ℤ)
    (i : AffineSl2GeneralRigidity.JointIndex (n : ℤ) (2*c)) :
    indexedWord k h (vacuumLiftWord i.val)∈jointSpace k h n c := by
  apply (mem_jointSpace_iff k h n c _).mpr
  constructor
  · rw [indexedWord,degree_word,vacuumLiftWord_energy,i.property.1,Int.cast_natCast]
  · rw [indexedWord,cartan_word]
    have he := vacuumLiftWord_charge i.val
    rw [i.property.2] at he
    have he' : wordCharge ((vacuumLiftWord i.val).map lowerLetter)=c := by omega
    rw [he']

/-- Projection of the fixed lift is exactly the original normalized
vacuum PBW vector, with no scalar rescaling. -/
theorem vacuumProjection_lift (k : ℂ) (hk : k+2≠0)
    (mu : AffineSl2GeneralRigidity.CurrentIndex) :
    vacuumProjection k (indexedWord k 0 (vacuumLiftWord mu))=
      AffineSl2GeneralRigidity.currentPBWBasis k hk mu := by
  rw [indexedWord,vacuumProjection,universalMap_word,vacuumLiftWord_modes,
    AffineSl2GeneralRigidity.currentPBWBasis_apply]
  generalize orderedPBWColorWord mu=w
  change currentWord (AffineVOA.J k) (w.map (fun an => (an.1,-(an.2 : ℤ)-1)))
    (vacuumA k)=wordStateA k w
  induction w with
  | nil => rfl
  | cons an w ih => simp only [List.map_cons,currentWord,Module.End.mul_apply,wordStateA_cons,ih]

/-- The actual vacuum projection preserves the joint energy/Cartan label. -/
theorem vacuumProjection_mem_joint (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ)
    (v : Verma k 0) (hv : v∈jointSpace k 0 n c) :
    vacuumProjection k v∈AffineSl2GeneralRigidity.jointSpace k hk (n : ℤ) (2*c) := by
  have hh := (mem_jointSpace_iff k 0 n c v).mp hv
  apply (AffineSl2GeneralRigidity.mem_jointSpace_iff k hk _ _ _).mpr
  constructor
  · apply (AffineSl2GeneralRigidity.universal k hk).L_zero_grading
    change vacuumProjection k v∈gradingZA k (n : ℤ)
    rw [gradingZA_def,Module.End.mem_eigenspace_iff]
    change AffineLie.vacuumRho kappaForm kappaForm_isInvariant k
      (AffineLie.ell0 kappaForm kappaForm_isInvariant) (vacuumProjection k v)=_
    rw [← vacuumProjection_intertwines,hh.1,map_smul]
    simp
  · change AffineLie.vacuumRho kappaForm kappaForm_isInvariant k
      (modeElement 2 0) (vacuumProjection k v)=_
    rw [← vacuumProjection_intertwines]
    change vacuumProjection k (mode k 0 2 0 v)=_
    rw [hh.2,map_smul]
    simp

end
end VOA.AffineVOA.HighestModule
