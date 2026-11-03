import VOA.DeligneAudit.DeligneFusionD1TensorGShift
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# The actual shifted tensor space has rank (n+1)^N

The tensor basis is constructed from the actual finite basis of each checked
site. No cyclicity, realization, graded character or dimension-bound premise
is used. In particular the empty tensor product has rank one.
-/

namespace VOA.DeligneAudit.D1TensorG

noncomputable section

/-- The actual product basis of the finite tensor space. -/
def tensorBasis (n N : ℕ) :
    Module.Basis (Fin N → Fin (Module.finrank ℂ (D1SiteG.Space n))) ℂ (Space n N) :=
  Basis.piTensorProduct (fun _ : Fin N => Module.finBasis ℂ (D1SiteG.Space n))

instance finiteDimensional_space (n N : ℕ) : FiniteDimensional ℂ (Space n N) :=
  Module.Finite.of_basis (tensorBasis n N)

/-- The exact total rank of the constructed tensor space. -/
theorem finrank_space (n N : ℕ) : Module.finrank ℂ (Space n N) = (n + 1) ^ N := by
  rw [Module.finrank_eq_card_basis (tensorBasis n N), Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, D1SiteG.finrank_space]

end
end VOA.DeligneAudit.D1TensorG

#print axioms VOA.DeligneAudit.D1TensorG.finrank_space
