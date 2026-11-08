import VOA.Moonshine.AutVnat

/-! # Every moonshine automorphism preserves the concrete invariant form -/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open AutMonster SimpleNat VertexOperatorAlgebra
open scoped BigOperators

theorem vnatAut_comm_power (g : AutVnat) (n : ℤ) (j : ℕ) (v : Vnat) :
    g ((VnatVOA.L n ^ j) v) = (VnatVOA.L n ^ j) (g v) := by
  induction j with
  | zero => rfl
  | succ j hj =>
    simp only [pow_succ', Module.End.mul_apply, VertexOperatorAlgebra.aut_comm_L, hj]

def vnatAutPullbackForm (g : AutVnat) : InvariantForm VnatVOA where
  form := natForm.compl₁₂ g.toLinearEquiv.toLinearMap g.toLinearEquiv.toLinearMap
  virasoro_adj := by
    intro n v w
    change natForm (g (VnatVOA.L n v)) (g w) = natForm (g v) (g (VnatVOA.L (-n) w))
    rw [VertexOperatorAlgebra.aut_comm_L, VertexOperatorAlgebra.aut_comm_L]
    exact natForm_virasoro_adj vnat_twistedLocality n (g v) (g w)

theorem vnatAutPullbackForm_fhl (g : AutVnat) : (vnatAutPullbackForm g).IsFullyInvariant := by
  intro wt u hu n v w
  change natForm (g (VnatVOA.smul u n v)) (g w) =
    (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
      natForm (g v) (g (VnatVOA.smul ((VnatVOA.L 1 ^ j) u) (2 * wt - n - 2 - j) w))
  simp only [Aut.map_smul, vnatAut_comm_power]
  exact natForm_fhl vnat_twistedLocality wt (g u)
    (GriessAut.aut_map_mem_grading g hu) n (g v) (g w)

/-- The actual `natForm`, not an unspecified invariant form, is Aut(V♮)-invariant. -/
theorem vnatAut_preserves_natForm (g : AutVnat) (v w : Vnat) :
    natForm (g v) (g w) = natForm v w := by
  have hn : (vnatAutPullbackForm g).Normalized := by
    change natForm (g VnatVOA.vacuum) (g VnatVOA.vacuum) = 1
    rw [show g VnatVOA.vacuum = VnatVOA.vacuum from g.map_vacuum]
    exact natInvForm_normalized vnat_twistedLocality
  have he := InvariantForm.invariantForm_unique (vnatAutPullbackForm_fhl g)
    (natInvForm_isFullyInvariant vnat_twistedLocality) hn
    (natInvForm_normalized vnat_twistedLocality)
  exact congrArg (fun B : LinearMap.BilinForm ℂ Vnat => B v w) he

end VOA.Moonshine.ConwayNorton
