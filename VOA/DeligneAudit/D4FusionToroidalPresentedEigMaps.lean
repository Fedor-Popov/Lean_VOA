import VOA.DeligneAudit.D4FusionToroidalPresentedEigCore

/-! Equivariant maps out of the eigenvalue-corrected presentation. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4

noncomputable section

def ψPTE (m : ℕ) (hm : 1 ≤ m) :
    PTE m →ₗ[ℂ] Gr D4sector.f (ravFam D4sector m 0) m :=
  univMapT D4sector.f m (JprimeSyntaxE m) (grToroidal_D4 m hm)
    (grGenerator D4sector.f (ravFam D4sector m 0) m)
    (eval_syntaxE m hm _ _ (Jprime_le_annGr m hm) (gr_eig m hm))

theorem ψPTE_gen (m : ℕ) (hm : 1 ≤ m) :
    ψPTE m hm (pTE m) =
      grGenerator D4sector.f (ravFam D4sector m 0) m :=
  univMapT_gen D4sector.f m (JprimeSyntaxE m) _ _
    (eval_syntaxE m hm _ _ (Jprime_le_annGr m hm) (gr_eig m hm))

theorem ψPTE_op (m : ℕ) (hm : 1 ≤ m) (c : Fin 28) (i s : ℕ)
    (x : PTE m) :
    ψPTE m hm ((ρPTE m).op c i s x) =
      (grToroidal_D4 m hm).op c i s (ψPTE m hm x) :=
  univMapT_op D4sector.f m (JprimeSyntaxE m) _ _
    (eval_syntaxE m hm _ _ (Jprime_le_annGr m hm) (gr_eig m hm)) c i s x

def χPTE (m : ℕ) (hm : 1 ≤ m) :
    PTE m →ₗ[ℂ] FusionGr.Gr (D4Fusion.action m) (D4Fusion.generator m) :=
  univMapT D4sector.f m (JprimeSyntaxE m)
    (D4Fusion.gradedAction m) (D4Fusion.gradedHighest m)
    (eval_syntaxE m hm _ _ (StarB2.Jprime_le_annF m hm)
      (D4Fusion.graded_ravFam_eig m hm))

theorem χPTE_gen (m : ℕ) (hm : 1 ≤ m) :
    χPTE m hm (pTE m) = D4Fusion.gradedHighest m :=
  univMapT_gen D4sector.f m (JprimeSyntaxE m) _ _
    (eval_syntaxE m hm _ _ (StarB2.Jprime_le_annF m hm)
      (D4Fusion.graded_ravFam_eig m hm))

theorem χPTE_op (m : ℕ) (hm : 1 ≤ m) (c : Fin 28) (i s : ℕ)
    (x : PTE m) :
    χPTE m hm ((ρPTE m).op c i s x) =
      (D4Fusion.gradedAction m).op c i s (χPTE m hm x) :=
  univMapT_op D4sector.f m (JprimeSyntaxE m) _ _
    (eval_syntaxE m hm _ _ (StarB2.Jprime_le_annF m hm)
      (D4Fusion.graded_ravFam_eig m hm)) c i s x

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.ψPTE
#print axioms VOA.DeligneAudit.Toroidal.ψPTE_gen
#print axioms VOA.DeligneAudit.Toroidal.ψPTE_op
#print axioms VOA.DeligneAudit.Toroidal.χPTE
#print axioms VOA.DeligneAudit.Toroidal.χPTE_gen
#print axioms VOA.DeligneAudit.Toroidal.χPTE_op
