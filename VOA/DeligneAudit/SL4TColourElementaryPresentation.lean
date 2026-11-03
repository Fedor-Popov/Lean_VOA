import VOA.DeligneAudit.SL4TColourPowerSumContraction
import VOA.Commutative.ColoredSymmetricHilbert

/-! Elementary-generator coordinates for the actual Young-subgroup fixed polynomial algebra. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial
open VOA.IteratedBlockSymmetricInvariant VOA.ColoredSymmetricHilbert
open VOA.BlockwiseSymmetricInvariantInduction

/-- Reindexing variables and their permutation families gives an equivalence of fixed algebras. -/
def permutationFixedAlgebraEquiv {σ τ G H : Type*}
    (a : G → Equiv.Perm σ) (b : H → Equiv.Perm τ) (e : σ ≃ τ) (g : G ≃ H)
    (h : ∀ t i, e (a t i) = b (g t) (e i)) :
    rightFixedSubalgebra (K := ℂ) a ≃ₐ[ℂ] rightFixedSubalgebra (K := ℂ) b where
  toFun p := ⟨rename e p.val, by
    intro t
    have hi := rename_intertwine e (a (g.symm t)) (b t)
      (by simpa using h (g.symm t)) p.val
    rw [hi, p.property]⟩
  invFun p := ⟨rename e.symm p.val, by
    intro t
    have hi := rename_intertwine e.symm (b (g t)) (a t) (by
      intro i
      apply e.injective
      simpa using (h t (e.symm i)).symm) p.val
    rw [hi, p.property]⟩
  left_inv p := by apply Subtype.ext; exact (renameEquiv ℂ e).left_inv p.val
  right_inv p := by apply Subtype.ext; exact (renameEquiv ℂ e).right_inv p.val
  map_mul' p q := by apply Subtype.ext; exact map_mul _ _ _
  map_add' p q := by apply Subtype.ext; exact map_add _ _ _
  commutes' c := by apply Subtype.ext; exact (rename e).commutes c

variable {B n : ℕ} (colour : Fin B → Fin n) (sizes : Fin n → ℕ)
variable (fibres : ∀ c, Fin (sizes c) ≃ {i // colour i = c})

/-- Recursive block slots reindex the actual positions using their colour fibres. -/
def colourBlockSlotEquiv : BlockSlots (profileBlocks sizes) ≃ Fin B :=
  (profileBlockSlotEquiv sizes).trans
    ((Equiv.sigmaCongrRight fibres).trans (Equiv.sigmaFiberEquiv colour))

/-- Independent block permutations give exactly the Young subgroup on the actual positions. -/
def colourBlockRelabelingEquiv :
    BlockRelabeling (profileBlocks sizes) ≃ positionColourSubgroup colour := by
  change BlockRelabeling (profileBlocks sizes) ≃ ColorPermutation colour
  exact (profileBlockRelabelingEquiv sizes).trans
    ((Equiv.piCongrRight fun c => (fibres c).permCongr).trans
      (colorPermutationEquiv colour))

/-- The slot and permutation reindexings intertwine the two concrete actions. -/
theorem colourBlockSlotEquiv_action (h : BlockRelabeling (profileBlocks sizes))
    (i : BlockSlots (profileBlocks sizes)) :
    colourBlockSlotEquiv colour sizes fibres (blockAction _ h i) =
      (colourBlockRelabelingEquiv colour sizes fibres h).val
        (colourBlockSlotEquiv colour sizes fibres i) := by
  change (Equiv.sigmaFiberEquiv colour) ((Equiv.sigmaCongrRight fibres)
    (profileBlockSlotEquiv sizes (blockAction _ h i))) =
      (Equiv.sigmaFiberEquiv colour).permCongr
        (Equiv.sigmaCongrRight fun c =>
          (fibres c).permCongr (profileBlockRelabelingEquiv sizes h c))
        (Equiv.sigmaFiberEquiv colour
          (Equiv.sigmaCongrRight fibres (profileBlockSlotEquiv sizes i)))
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, profileBlockSlotEquiv_action]
  apply congrArg (Equiv.sigmaFiberEquiv colour)
  generalize profileBlockSlotEquiv sizes i = z
  rcases z with ⟨c, z⟩
  simp [Equiv.permCongr_apply]

/-- The blockwise elementary presentation of the actual Young-invariant polynomial algebra. -/
def colourElementaryPresentation :
    MvPolynomial (BlockSlots (profileBlocks sizes)) ℂ ≃ₐ[ℂ]
      ColourPolynomialRing colour := by
  let e := permutationFixedAlgebraEquiv (blockAction (profileBlocks sizes))
    (fun g : positionColourSubgroup colour => g.val)
    (colourBlockSlotEquiv colour sizes fibres) (colourBlockRelabelingEquiv colour sizes fibres)
    (colourBlockSlotEquiv_action colour sizes fibres)
  exact (blockEsymmAlgEquiv (K := ℂ) (profileBlocks sizes)).trans e

/-- Forgetting fixedness in elementary coordinates is the explicit root-variable renaming. -/
theorem colourElementaryPresentation_apply
    (p : MvPolynomial (BlockSlots (profileBlocks sizes)) ℂ) :
    (colourElementaryPresentation colour sizes fibres p).val =
      rename (colourBlockSlotEquiv colour sizes fibres)
        (blockEsymmAlgEquiv (K := ℂ) (profileBlocks sizes) p).val := rfl

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.permutationFixedAlgebraEquiv
#print axioms VOA.DeligneAudit.SL4T.colourBlockSlotEquiv
#print axioms VOA.DeligneAudit.SL4T.colourBlockRelabelingEquiv
#print axioms VOA.DeligneAudit.SL4T.colourBlockSlotEquiv_action
#print axioms VOA.DeligneAudit.SL4T.colourElementaryPresentation
#print axioms VOA.DeligneAudit.SL4T.colourElementaryPresentation_apply
