import VOA.DeligneAudit.SL4TColourElementaryPresentation

/-! Elementary coefficients in colour coordinates and their finite alphabet tails. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial
open VOA.IteratedBlockSymmetricInvariant VOA.ColoredSymmetricHilbert
open VOA.BlockSymmetricWeightedDegree

/-- A generator at a profile slot is the elementary polynomial of that block. -/
theorem blockElementary_profile_generator {n : ℕ} (sizes : Fin n → ℕ)
    (c : Fin n) (i : Fin (sizes c)) :
    (blockEsymmAlgEquiv (K := ℂ) (profileBlocks sizes)
      (X ((profileBlockSlotEquiv sizes).symm ⟨c, i⟩))).val =
        rename (fun j : Fin (sizes c) => (profileBlockSlotEquiv sizes).symm ⟨c, j⟩)
          (esymm (Fin (sizes c)) ℂ (i.val + 1)) := by
  induction n with
  | zero => exact Fin.elim0 c
  | succ n ih =>
    cases c using Fin.cases with
    | zero =>
      change (blockEsymmAlgEquiv (K := ℂ)
        (sizes 0 :: profileBlocks (fun c => sizes c.succ)) (X (Sum.inl i))).val = _
      rw [blockEsymm_X_inl]
      rfl
    | succ c =>
      change (blockEsymmAlgEquiv (K := ℂ)
        (sizes 0 :: profileBlocks (fun c => sizes c.succ))
        (X (Sum.inr ((profileBlockSlotEquiv (fun c => sizes c.succ)).symm ⟨c, i⟩)))).val = _
      rw [blockEsymm_X_inr, ih, rename_rename]
      rfl

variable {B n : ℕ} (colour : Fin B → Fin n) (sizes : Fin n → ℕ)
variable (fibres : ∀ c, Fin (sizes c) ≃ {i // colour i = c})

/-- The elementary presentation sends each coordinate to its actual colour-fibre polynomial. -/
theorem colourElementaryPresentation_generator (c : Fin n) (i : Fin (sizes c)) :
    (colourElementaryPresentation colour sizes fibres
      (X ((profileBlockSlotEquiv sizes).symm ⟨c, i⟩))).val =
        rename (fun j : Fin (sizes c) => (fibres c j).val)
          (esymm (Fin (sizes c)) ℂ (i.val + 1)) := by
  rw [colourElementaryPresentation_apply, blockElementary_profile_generator, rename_rename]
  congr 2
  funext j
  simp [colourBlockSlotEquiv]

/-- The full elementary sequence in finite block coordinates, including its zero tail. -/
def colourElementaryCoordinate (c : Fin n) (s : ℕ) :
    MvPolynomial (BlockSlots (profileBlocks sizes)) ℂ :=
  if hs : s = 0 then 1 else
    if h : s ≤ sizes c then X ((profileBlockSlotEquiv sizes).symm
      ⟨c, ⟨s - 1, by omega⟩⟩) else 0

/-- The entire finite elementary sequence specializes to the actual colour-fibre sequence. -/
theorem colourElementaryPresentation_coordinate (c : Fin n) (s : ℕ) :
    (colourElementaryPresentation colour sizes fibres
      (colourElementaryCoordinate sizes c s)).val =
        rename (fun j : Fin (sizes c) => (fibres c j).val)
          (esymm (Fin (sizes c)) ℂ s) := by
  classical
  by_cases hs : s = 0
  · subst s
    simp [colourElementaryCoordinate]
  by_cases h : s ≤ sizes c
  · rw [colourElementaryCoordinate, dif_neg hs, dif_pos h,
      colourElementaryPresentation_generator]
    congr 2
    change s - 1 + 1 = s
    omega
  · rw [colourElementaryCoordinate, dif_neg hs, dif_neg h, map_zero,
      Subalgebra.coe_zero]
    have hz : esymm (Fin (sizes c)) ℂ s = 0 := by
      rw [esymm, Finset.powersetCard_eq_empty.mpr]
      · exact Finset.sum_empty
      · simpa using (show sizes c < s by omega)
    rw [hz, map_zero]

/-- Power sums expressed in the finite elementary coordinates of a single colour. -/
def colourPowerSumCoordinate (c : Fin n) (s : ℕ) :
    MvPolynomial (BlockSlots (profileBlocks sizes)) ℂ :=
  powerSumOfCoeff (sizes c) (fun j => (-1) ^ j * colourElementaryCoordinate sizes c j) s

/-- The elementary-coordinate power sum is exactly the actual block power sum. -/
theorem colourElementaryPresentation_powerSum (c : Fin n) (s : ℕ) (hs : 1 ≤ s) :
    colourElementaryPresentation colour sizes fibres (colourPowerSumCoordinate sizes c s) =
      colourPolynomialPowerSum colour c s := by
  classical
  apply Subtype.ext
  let f := (ColourPolynomialRing colour).val.comp
    (colourElementaryPresentation colour sizes fibres).toAlgHom
  change f (powerSumOfCoeff (sizes c)
    (fun j => (-1) ^ j * colourElementaryCoordinate sizes c j) s) = _
  rw [powerSumOfCoeff_map]
  simp only [map_mul, map_pow, map_neg, map_one, f, AlgHom.comp_apply,
    AlgEquiv.coe_algHom, Subalgebra.val_apply, colourElementaryPresentation_coordinate]
  rw [powerSumOfCoeff_psum_map (Fin (sizes c))
    (rename fun j => (fibres c j).val) (sizes c) s hs]
  simp only [psum, map_sum, map_pow, rename_X]
  change (∑ j : Fin (sizes c), (X (fibres c j).val : MvPolynomial (Fin B) ℂ) ^ s) =
    ∑ i ∈ Finset.univ.filter (fun i => colour i = c), X i ^ s
  calc
    _ = ∑ i : {i // colour i = c}, (X i.val : MvPolynomial (Fin B) ℂ) ^ s :=
      Fintype.sum_equiv (fibres c) _ _ (fun _ => rfl)
    _ = _ := (Finset.sum_subtype _ (fun i => by simp) (fun i =>
      (X i : MvPolynomial (Fin B) ℂ) ^ s)).symm

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.blockElementary_profile_generator
#print axioms VOA.DeligneAudit.SL4T.colourElementaryPresentation_generator
#print axioms VOA.DeligneAudit.SL4T.colourElementaryCoordinate
#print axioms VOA.DeligneAudit.SL4T.colourElementaryPresentation_coordinate
#print axioms VOA.DeligneAudit.SL4T.colourPowerSumCoordinate
#print axioms VOA.DeligneAudit.SL4T.colourElementaryPresentation_powerSum
