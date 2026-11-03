import VOA.DeligneAudit.D4FusionRealizationTwoPairColumns
import VOA.DeligneAudit.D4FusionRealizationTwoSiteColumns
import VOA.DeligneAudit.D4FusionRealizationTwoSingleActions
import VOA.DeligneAudit.D4FusionRealizationTwoCurrent
import VOA.DeligneAudit.D4FusionRealizationTwoSparseLinear

/-! Exact actual-current interpretation of the checked sparse two-site columns. -/
namespace VOA.DeligneAudit.D4Two
open Certificate
noncomputable section

theorem siteFlat_val_eq_iff (i j : SiteIndex 28) :
    (siteFlat 28 i).val = (siteFlat 28 j).val ↔ i = j := by
  rw [Fin.val_inj,Equiv.apply_eq_iff_eq]

theorem siteFlat_val_line_iff (i : SiteIndex 28) :
    (siteFlat 28 i).val = 28 ↔ i = Sum.inr () := by
  exact siteFlat_val_eq_iff i (Sum.inr ())

theorem siteFlat_val_color_iff (i : SiteIndex 28) (c : Fin 28) :
    (siteFlat 28 i).val = c.val ↔ i = Sum.inl c := by
  exact siteFlat_val_eq_iff i (Sum.inl c)

/-- Every sparse integer current column is the actual coadjoint-plus-line
operator, including both evaluation points and every current mode. -/
theorem coordinateOp_single_coeff (c : Fin 28) (k : ℕ)
    (i j i' j' : SiteIndex 28) :
    coordinateOp (DeligneSector.Sparse.fC 28 DeligneSector.D4.br) c k
      (Pi.single (i,j) 1) (i',j') =
      (coeff (pairColumn 28 (rawColumn c) c k
        ((siteFlat 28 i).val * 29 + (siteFlat 28 j).val))
        ((siteFlat 28 i').val * 29 + (siteFlat 28 j').val) : ℂ) := by
  rw [coeff_pairColumn _ _ _ _ _ _ c.isLt (siteFlat 28 i).isLt
    (siteFlat 28 j).isLt (siteFlat 28 i').isLt (siteFlat 28 j').isLt]
  rcases k with _ | _ | k <;>
    simp only [coordinateOp,LinearMap.add_apply,LinearMap.smul_apply,
      LinearMap.zero_apply,Pi.add_apply,Pi.smul_apply,leftAction_single,
      rightAction_single,siteAction_zero_single,siteAction_one_single]
  all_goals
    simp only [Int.cast_add,apply_ite (fun z : ℤ => (z : ℂ)),Int.cast_zero,
      Int.cast_one,Int.cast_natCast,siteFlat_val_eq_iff,siteFlat_val_line_iff,
      siteFlat_val_color_iff]
    simp only [ite_true,ite_false,ite_self,Nat.cast_zero,Nat.cast_one,
      zero_smul,one_smul,zero_add,add_zero,Nat.reduceEqDiff,and_false,false_and,
      and_true,true_and,eq_comm]
  all_goals
    split_ifs <;> simp_all only [zero_smul,one_smul,smul_zero,smul_eq_mul,
      mul_zero,mul_one,Pi.zero_apply,Nat.cast_add,add_zero,zero_add,
      Nat.cast_zero,Nat.cast_one,Nat.add_eq_zero_iff,Nat.reduceAdd,Nat.reduceEqDiff,
      Nat.succ_ne_zero,and_false,false_and,and_true,true_and]
  all_goals first | contradiction | omega | ring

end
end VOA.DeligneAudit.D4Two

#print axioms VOA.DeligneAudit.D4Two.coordinateOp_single_coeff
