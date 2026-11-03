import VOA.DeligneAudit.D4FusionToroidalPresented
import VOA.DeligneAudit.D4FusionToroidalFusionD4RavFam

/-! The toroidal presentation with the Ravinder eigenrelations included. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4

noncomputable section

def EigSyntax (m : ℕ) : Set (FreeT 28) :=
  {z | ∃ q ∈ (ravFam D4sector m 0).eig,
    z = swT [(q.1, 0, 0)] - q.2 • swT []}

def JprimeSyntaxE (m : ℕ) : Set (FreeT 28) :=
  JprimeSyntax m ∪ EigSyntax m

abbrev PTE (m : ℕ) := PT' D4sector.f m (JprimeSyntaxE m)

def ρPTE (m : ℕ) : ToroidalModule D4sector.f m (PTE m) :=
  rhoPT D4sector.f m (JprimeSyntaxE m)

def pTE (m : ℕ) : PTE m := pPT D4sector.f m (JprimeSyntaxE m)

theorem PTE_cyclic (m : ℕ) :
    Submodule.span ℂ (Set.range fun l : List (TLtr 28) =>
      wordOpT (ρPTE m) l (pTE m)) = ⊤ :=
  PT'_cyclic D4sector.f m (JprimeSyntaxE m)

theorem gr_eig (m : ℕ) (hm : 1 ≤ m)
    (q : Fin 28 × ℂ) (hq : q ∈ (ravFam D4sector m 0).eig) :
    (grToroidal_D4 m hm).op q.1 0 0
      (grGenerator D4sector.f (ravFam D4sector m 0) m) =
        q.2 • grGenerator D4sector.f (ravFam D4sector m 0) m := by
  have he := (univG_sat D4sector.f (ravFam D4sector m 0)).eig q hq
  rw [grToroidal_D4_op, grGenerator]
  rw [grOp_single D4sector.f (ravFam D4sector m 0) m
    (highModeShift_D4 (ravFam D4sector m 0) m hm) q.1 0 0 0
    (wUG D4sector.f (ravFam D4sector m 0)) hm]
  have hcongr :=
    congrArg (fun x : UModG D4sector.f (ravFam D4sector m 0) =>
      (grKernel D4sector.f (ravFam D4sector m 0) m).mkQ
        (gradedSingle D4sector.f (ravFam D4sector m 0) m 0 x (by
          rw [TU_zero]; trivial))) he
  have hsmul : gradedSingle D4sector.f (ravFam D4sector m 0) m 0
      (q.2 • wUG D4sector.f (ravFam D4sector m 0)) (by rw [TU_zero]; trivial) =
      q.2 • gradedSingle D4sector.f (ravFam D4sector m 0) m 0
        (wUG D4sector.f (ravFam D4sector m 0)) (by rw [TU_zero]; trivial) := by
    apply Subtype.ext
    simp [gradedSingle]
  simpa only [zero_mul, zero_add, hsmul, map_smul] using hcongr

theorem eval_eig (m : ℕ) (_hm : 1 ≤ m)
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : ToroidalModule D4sector.f m V) (v : V)
    (he : ∀ q ∈ (ravFam D4sector m 0).eig,
      ρ.op q.1 0 0 v = q.2 • v) :
    ∀ z ∈ EigSyntax m, evalT ρ v z = 0 := by
  rintro z ⟨q, hq, rfl⟩
  change evalT ρ v (swT [(q.1, 0, 0)] - q.2 • swT []) = 0
  rw [map_sub, map_smul, evalT_swT, evalT_swT]
  exact sub_eq_zero.mpr (he q hq)

theorem eval_syntaxE (m : ℕ) (hm : 1 ≤ m)
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : ToroidalModule D4sector.f m V) (v : V)
    (hJ : Jprime m ⊆ {r | r V ρ v = 0})
    (he : ∀ q ∈ (ravFam D4sector m 0).eig,
      ρ.op q.1 0 0 v = q.2 • v) :
    ∀ z ∈ JprimeSyntaxE m, evalT ρ v z = 0 := by
  intro z hz
  rcases hz with hz | hz
  · exact evalT_JprimeSyntax_zero m ρ v hJ z hz
  · exact eval_eig m hm ρ v he z hz

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.PTE_cyclic
#print axioms VOA.DeligneAudit.Toroidal.gr_eig
#print axioms VOA.DeligneAudit.Toroidal.eval_syntaxE
