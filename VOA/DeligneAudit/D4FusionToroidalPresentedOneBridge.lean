import VOA.DeligneAudit.D4FusionToroidalPresentedEigRank

/-! The two current actions at toroidal multiplicity one. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.SectorWeyl

noncomputable section

abbrev OneR := ravFam D4sector 1 0
abbrev OneU := UModG D4sector.f OneR
private abbrev R1 := OneR
private abbrev U1 := OneU

def univToroidalOne : ToroidalModule D4sector.f 1 U1 where
  op c i s := if s = 0 then (univRepG D4sector.f R1).op c i else 0
  high_zero c i s hs := by
    have : s ≠ 0 := by omega
    simp [this]
  comm a b i j r s v := by
    by_cases hr : r = 0 <;> by_cases hs : s = 0
    · subst r; subst s
      simp only [if_pos (show 0 + 0 < 1 by omega)]
      change (univRepG D4sector.f R1).op a i
          ((univRepG D4sector.f R1).op b j v) -
        (univRepG D4sector.f R1).op b j
          ((univRepG D4sector.f R1).op a i v) = _
      exact (univRepG D4sector.f R1).comm a b i j v
    · have h : ¬ r + s < 1 := by omega
      simp [hr, hs]
    · have h : ¬ r + s < 1 := by omega
      simp [hr, hs]
    · have h : ¬ r + s < 1 := by omega
      simp [hr, hs, h]

def presentedCurrentOne : CurrentModule D4sector.f (PTE 1) where
  op c i := (ρPTE 1).op c i 0
  comm a b i j v := by
    simpa using (ρPTE 1).comm a b i j 0 0 v

theorem symbolLetters_one (l : List (Ltr 28)) :
    symbolLetters 1 l = l.map (fun x => (x.1, x.2, 0)) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [symbolLetters, ih, Nat.mod_one]

theorem wordOpT_univ_symbol_one (l : List (Ltr 28)) :
    wordOpT univToroidalOne (symbolLetters 1 l) (wUG D4sector.f R1) =
      wordOp (univRepG D4sector.f R1) l (wUG D4sector.f R1) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      change (univToroidalOne.op x.1 (x.2 / 1) (x.2 % 1))
          (wordOpT univToroidalOne (symbolLetters 1 l) (wUG D4sector.f R1)) = _
      simpa [univToroidalOne, Nat.mod_one] using
        congrArg ((univRepG D4sector.f R1).op x.1 x.2) ih

theorem wordOp_presented_one (l : List (Ltr 28)) :
    wordOp presentedCurrentOne l (pTE 1) =
      wordOpT (ρPTE 1) (symbolLetters 1 l) (pTE 1) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      change (presentedCurrentOne.op x.1 x.2)
          (wordOp presentedCurrentOne l (pTE 1)) = _
      calc
        _ = (ρPTE 1).op x.1 x.2 0
            (wordOpT (ρPTE 1) (symbolLetters 1 l) (pTE 1)) :=
          congrArg ((ρPTE 1).op x.1 x.2 0) ih
        _ = _ := by simp [symbolLetters, wordOpT, Nat.mod_one]

theorem presentedOne_sat :
    Sat D4sector.f presentedCurrentOne (pTE 1) R1 where
  tail t ht := by
    rw [wordOp_presented_one]
    change wordOpT (rhoPT D4sector.f 1 (JprimeSyntaxE 1))
      (symbolLetters 1 t) (pPT D4sector.f 1 (JprimeSyntaxE 1)) = 0
    rw [wordOpT_rhoPT]
    exact mk_syntax D4sector.f 1 (JprimeSyntaxE 1)
      (swT (symbolLetters 1 t)) (Or.inl (Or.inl ⟨t, ht, rfl⟩))
  eig q hq := by
    have h := mk_syntax D4sector.f 1 (JprimeSyntaxE 1)
      (swT [(q.1, 0, 0)] - q.2 • swT [])
      (Or.inr ⟨q, hq, rfl⟩)
    rw [← Submodule.mkQ_apply, map_sub, map_smul] at h
    have h1 := wordOpT_rhoPT D4sector.f 1 (JprimeSyntaxE 1) [(q.1, 0, 0)]
    have h0 := wordOpT_rhoPT D4sector.f 1 (JprimeSyntaxE 1) []
    change (ρPTE 1).op q.1 0 0 (pTE 1) =
      (JT D4sector.f 1 (JprimeSyntaxE 1)).mkQ (swT [(q.1, 0, 0)]) at h1
    change pTE 1 = (JT D4sector.f 1 (JprimeSyntaxE 1)).mkQ (swT []) at h0
    rw [← h1, ← h0] at h
    exact sub_eq_zero.mp h

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.presentedOne_sat
