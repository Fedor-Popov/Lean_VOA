import VOA.DeligneAudit.D4FusionToroidalFusionGr

/-!
# Truncated toroidal action on the evaluation fusion graded space

The global point-polynomial identity supplies the high-mode shift premise.
The resulting module has truncation parameter equal to the number of sites.
-/

namespace VOA.DeligneAudit.Toroidal.FusionGr

open VOA.DeligneAudit.Toroidal VOA.DeligneAudit.D1TensorG
open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {n N : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (ρ : Fin N → CurrentModule f V) (z : Fin N → ℂ)
variable (w : Tensor (K := ℂ) (ι := Fin N) (W := V))

theorem evalHighTShift : HighTShift (evalAction ρ z) w N := by
  intro c i s d hs
  exact evalFbelow_high ρ z w c i s d hs

/-- The actual evaluation fusion associated graded has the truncated
two-variable current commutator. -/
def evalGrToroidal : ToroidalModule f N (Gr (evalAction ρ z) w) :=
  grToroidal (evalAction ρ z) w N (evalHighTShift ρ z w)

end

end VOA.DeligneAudit.Toroidal.FusionGr

#print axioms VOA.DeligneAudit.Toroidal.FusionGr.evalHighTShift
#print axioms VOA.DeligneAudit.Toroidal.FusionGr.evalGrToroidal
