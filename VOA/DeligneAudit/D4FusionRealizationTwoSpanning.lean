import VOA.DeligneAudit.D4FusionRealizationTwoWords
import VOA.DeligneAudit.D4FusionRealizationTwoActionLinearFacts
import VOA.DeligneAudit.D4FusionRealizationTwoActionChecks
import VOA.DeligneAudit.D4FusionRealizationTwoSpanGeneric
import VOA.DeligneAudit.D4FusionRealizationTwoCurrentHigh

/-! Actual full-span stability and basis construction from checked action relations.
The total source rank is proved independently from its genuine tensor basis. -/
namespace VOA.DeligneAudit.D4Two
open Certificate VOA.DeligneAudit.SectorWeyl
noncomputable section

def anyWordVector (j : ℕ) : Source :=
  (flatCoordinates 28).symm (vec 841 (wordNode j).vector)

theorem action_check (c : Fin 28) (k : ℕ) (hk : k < 4) (i : Fin 841) :
    fullActionCheck actionCase (actionIndex c k i) = true :=
  List.all_eq_true.mp full_action_checks_all _
    (List.mem_range'_1.mpr ⟨Nat.zero_le _,actionIndex_lt c k i c.isLt hk i.isLt⟩)

theorem source_action_identity (c : Fin 28) (k : ℕ) (hk : k < 4) (i : Fin 841) :
    ((actionCase (actionIndex c k i)).denominator : ℂ) • sourceRep.op c k (wordVector i) =
      ((actionCase (actionIndex c k i)).terms.map fun p =>
        (p.2 : ℂ) • anyWordVector p.1).sum := by
  have he := fullAction_vector actionCase (actionIndex c k i) (action_check c k hk i)
  simp only [actionIndex_source c k i i.isLt,actionIndex_color c k i c.isLt i.isLt,
    actionIndex_mode c k i c.isLt i.isLt] at he
  apply (flatCoordinates 28).injective
  simpa only [map_smul,source_flat_current,wordVector,LinearEquiv.apply_symm_apply,
    map_list_sum,List.map_map,Function.comp_def,anyWordVector] using he

theorem source_action_mem (M : Submodule ℂ Source) (c : Fin 28) (k : ℕ)
    (hk : k < 4) (i : Fin 841)
    (htarget : ∀ p ∈ (actionCase (actionIndex c k i)).terms, anyWordVector p.1 ∈ M) :
    sourceRep.op c k (wordVector i) ∈ M := by
  have hdZ := (fullAction_parts actionCase (actionIndex c k i) (action_check c k hk i)).1
  have hdC : ((actionCase (actionIndex c k i)).denominator : ℂ) ≠ 0 :=
    Int.cast_ne_zero.mpr hdZ
  have hh : ((actionCase (actionIndex c k i)).denominator : ℂ) •
      sourceRep.op c k (wordVector i) ∈ M := by
    rw [source_action_identity c k hk i]
    apply M.list_sum_mem
    intro v hv
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv
    exact M.smul_mem _ (htarget p hp)
  have h := M.smul_mem (((actionCase (actionIndex c k i)).denominator : ℂ)⁻¹) hh
  simpa only [smul_smul,inv_mul_cancel₀ hdC,one_smul] using h

def wordSpan : Submodule ℂ Source := Submodule.span ℂ (Set.range wordVector)

theorem source_action_mem_wordSpan (c : Fin 28) (k : ℕ) (hk : k < 4) (i : Fin 841) :
    sourceRep.op c k (wordVector i) ∈ wordSpan := by
  apply source_action_mem wordSpan c k hk i
  intro p hp
  have hb := fullAction_target_bound actionCase (actionIndex c k i)
    (action_check c k hk i) p hp
  exact Submodule.subset_span ⟨⟨p.1,hb⟩,rfl⟩

theorem source_generator_mem_wordSpan : sourceGenerator ∈ wordSpan := by
  apply Submodule.subset_span
  refine ⟨(0 : Fin 841),?_⟩
  apply (flatCoordinates 28).injective
  simpa only [wordVector,LinearEquiv.apply_symm_apply] using flat_source_generator.symm

theorem source_current_high (c : Fin 28) (k : ℕ) (hk : 2 ≤ k) :
    sourceRep.op c k = ((3 : ℂ)-(k : ℂ)) • sourceRep.op c 2 +
      ((k : ℂ)-2) • sourceRep.op c 3 :=
  current_high actualTwoF D1SiteG.D4Check.table_jacobi D1SiteG.D4Check.table_skewC c k hk

/-- Full action stability includes top-level vectors before cyclicity is used. -/
theorem wordSpan_eq_top : wordSpan = ⊤ :=
  span_top_of_low_action sourceRep sourceGenerator wordVector source_cyclic
    source_generator_mem_wordSpan source_current_high
    (fun c k hk i => source_action_mem_wordSpan c k (by omega) i)

def actualBasis : Module.Basis (Fin 841) ℂ Source :=
  basisOfSpanningWords wordVector wordSpan_eq_top
    (by simpa only [Fintype.card_fin] using source_dimension.symm)

@[simp] theorem actualBasis_apply (i : Fin 841) : actualBasis i = wordVector i := by
  rw [actualBasis,basisOfSpanningWords_apply]

end
#print axioms source_action_identity
#print axioms wordSpan_eq_top
#print axioms actualBasis
end VOA.DeligneAudit.D4Two
