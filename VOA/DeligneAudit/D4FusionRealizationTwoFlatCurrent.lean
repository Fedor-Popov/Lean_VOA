import VOA.DeligneAudit.D4FusionRealizationTwoCurrentBridge

/-! The actual tensor current, transported through the proved flat coordinate
 equivalence, equals the checked sparse-column endomorphism. -/
namespace VOA.DeligneAudit.D4Two
open Certificate VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.SectorLoop
noncomputable section

abbrev actualTwoF := DeligneSector.Sparse.fC 28 DeligneSector.D4.br

variable (hJ : JacobiCoord actualTwoF)
  (hskew : ∀ a b c, actualTwoF a b c = -actualTwoF b a c)

/-- Equality of genuine linear endomorphisms, proved on the standard basis. -/
theorem flatCurrent_eq_columns (c : Fin 28) (k : ℕ) :
    (flatCoordinates 28).toLinearMap ∘ₗ
      (D1TensorG.rep actualTwoF hJ hskew twoPoints).op c k ∘ₗ
      (flatCoordinates 28).symm.toLinearMap =
      columnsEnd 841 (pairColumn 28 (rawColumn c) c k) := by
  apply (Pi.basisFun ℂ (Fin 841)).ext
  intro x
  obtain ⟨p,rfl⟩ := (pairFlat 28).surjective x
  rw [Pi.basisFun_apply,columnsEnd_single]
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  funext x
  obtain ⟨q,rfl⟩ := (pairFlat 28).surjective x
  rw [flatCoordinates_at_pair,coordinates_current_two,flatCoordinates_symm_single]
  simpa only [vec,pairFlat_val] using
    coordinateOp_single_coeff c k p.1 p.2 q.1 q.2

/-- The certificate operator intertwines with the actual current on every tensor. -/
theorem flatCoordinates_current (c : Fin 28) (k : ℕ) (v : D1TensorG.Space 28 2) :
    flatCoordinates 28 ((D1TensorG.rep actualTwoF hJ hskew twoPoints).op c k v) =
      columnsEnd 841 (pairColumn 28 (rawColumn c) c k) (flatCoordinates 28 v) := by
  have h := LinearMap.congr_fun (flatCurrent_eq_columns hJ hskew c k)
    (flatCoordinates 28 v)
  simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] using h

end
#print axioms flatCoordinates_current
end VOA.DeligneAudit.D4Two
