import VOA.DeligneAudit.D4FusionRealizationTwoFlatCurrent
import VOA.DeligneAudit.D4FusionRealizationTwoWordLinearFacts
import VOA.DeligneAudit.DeligneFusionD1TensorGD4

/-! A fully specified cyclic D4 two-site source and its certified coordinates. -/
namespace VOA.DeligneAudit.D4Two
open Certificate VOA.DeligneAudit.SectorWeyl
noncomputable section

abbrev Source := D1TensorG.Space 28 2

def sourceRep : CurrentModule actualTwoF Source :=
  D1TensorG.rep actualTwoF D1SiteG.D4Check.table_jacobi
    D1SiteG.D4Check.table_skewC twoPoints

def sourceGenerator : Source := D1TensorG.generator (27 : Fin 28)

theorem points_two : D1TensorG.points 2 = twoPoints := by
  funext j
  fin_cases j <;> simp [D1TensorG.points,twoPoints]

theorem source_cyclic :
    Submodule.span ℂ (Set.range fun l : List (Fin 28 × ℕ) =>
      wordOp sourceRep l sourceGenerator) = ⊤ := by
  simpa only [D1TensorG.D4Check.currentRep,D1TensorG.D4Check.highest,
    points_two,sourceRep,sourceGenerator] using D1TensorG.D4Check.current_cyclic 2

theorem source_dimension : Module.finrank ℂ Source = 841 := by
  exact (D1TensorG.D4Check.dimension 2).trans (by decide)

theorem source_flat_current (c : Fin 28) (k : ℕ) (v : Source) :
    flatCoordinates 28 (sourceRep.op c k v) =
      columnsEnd 841 (pairColumn 28 (rawColumn c) c k) (flatCoordinates 28 v) :=
  flatCoordinates_current D1SiteG.D4Check.table_jacobi
    D1SiteG.D4Check.table_skewC c k v

theorem flat_source_generator :
    flatCoordinates 28 sourceGenerator = vec 841 (wordNode 0).vector := by
  rw [wordNode_initial]
  funext x
  obtain ⟨p,rfl⟩ := (pairFlat 28).surjective x
  rw [flatCoordinates_at_pair]
  change coordinates 28 (PiTensorProduct.tprod ℂ
    (fun _ : Fin 2 => D1SiteG.w (27 : Fin 28))) p = _
  rw [coordinates_generator]
  have hp : pairFlat 28 (Sum.inl (27 : Fin 28),Sum.inl (27 : Fin 28)) =
      (⟨810,by decide⟩ : Fin 841) := by
    apply Fin.ext
    rw [pairFlat_val]
    rfl
  rw [← hp]
  simp only [Pi.single_apply,Equiv.apply_eq_iff_eq]

end
#print axioms source_cyclic
#print axioms source_flat_current
#print axioms flat_source_generator
end VOA.DeligneAudit.D4Two
