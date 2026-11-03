import VOA.DeligneAudit.DeligneFusionD1TensorGGrCore
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Exact restricted current-degree symbols. The ambient graded quotient is
not asserted finite; only its actual cyclic degree pieces occur here. -/
namespace VOA.DeligneAudit.D1TensorG.Gr

open VOA.DeligneAudit.SectorWeyl

noncomputable section
variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {T : Type*} [AddCommGroup T] [Module ℂ T]
variable (R : CurrentModule f T) (w : T)

def evalAt (d : ℕ) : (ℕ →₀ T) →ₗ[ℂ] T where
  toFun x := x d
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem Lsub_le_evalAt (d : ℕ) :
    Lsub R w ≤ (Fbelow R w d).comap (evalAt d) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨e, v, hv, rfl⟩
  change (Finsupp.single e v) d ∈ Fbelow R w d
  by_cases he : e = d
  · subst e
    simpa only [Finsupp.single_eq_same] using hv
  · rw [Finsupp.single_eq_of_ne (Ne.symm he)]
    exact Submodule.zero_mem _

theorem single_mem_Lsub_iff (d : ℕ) (v : T) :
    Finsupp.single d v ∈ Lsub R w ↔ v ∈ Fbelow R w d := by
  constructor
  · intro hv
    have h := Lsub_le_evalAt R w d hv
    simpa only [Submodule.mem_comap, evalAt, LinearMap.coe_mk, AddHom.coe_mk,
      Finsupp.single_eq_same] using h
  · exact single_mem_Lsub R w

def tag (d : ℕ) : T →ₗ[ℂ] ((ℕ →₀ T) ⧸ Lsub R w) :=
  (Lsub R w).mkQ ∘ₗ Finsupp.lsingle d

theorem tag_apply (d : ℕ) (v : T) :
    tag R w d v = (Lsub R w).mkQ (Finsupp.single d v) := rfl

theorem tag_eq_zero_iff (d : ℕ) (v : T) :
    tag R w d v = 0 ↔ v ∈ Fbelow R w d := by
  change (Submodule.Quotient.mk (Finsupp.single d v) :
    (ℕ →₀ T) ⧸ Lsub R w) = 0 ↔ v ∈ Fbelow R w d
  exact (Submodule.Quotient.mk_eq_zero _).trans (single_mem_Lsub_iff R w d v)

def symbol (d : ℕ) : Fle R w d →ₗ[ℂ] ((ℕ →₀ T) ⧸ Lsub R w) :=
  tag R w d ∘ₗ (Fle R w d).subtype

theorem symbol_apply (d : ℕ) (v : Fle R w d) :
    symbol R w d v = tag R w d (v : T) := rfl

theorem symbol_eq_zero_iff (d : ℕ) (v : Fle R w d) :
    symbol R w d v = 0 ↔ (v : T) ∈ Fbelow R w d := tag_eq_zero_iff R w d v

theorem tag_mem_cycDeg (d : ℕ) {v : T} (hv : v ∈ Fle R w d) :
    tag R w d v ∈ cycDeg (grRep R w) (wg R w) d := by
  change v ∈ Submodule.span ℂ _ at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, hl, rfl⟩ := hv
      by_cases he : degree l = d
      · rw [tag_apply, ← he, ← grRep_word]
        exact Submodule.subset_span ⟨l, rfl, rfl⟩
      · have hlt : degree l < d := by omega
        have hzero : tag R w d (wordOp R l w) = 0 :=
          (tag_eq_zero_iff R w d _).mpr (Submodule.subset_span ⟨l, hlt, rfl⟩)
        rw [hzero]
        exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v hu hv ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv
  | smul a v hv ih => rw [map_smul]; exact Submodule.smul_mem _ a ih

theorem range_symbol (d : ℕ) :
    LinearMap.range (symbol R w d) = cycDeg (grRep R w) (wg R w) d := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact tag_mem_cycDeg R w d v.property
  · rw [cycDeg, Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    change degree l = d at hl
    have hv : wordOp R l w ∈ Fle R w d :=
      Submodule.subset_span ⟨l, by change degree l < d + 1; omega, rfl⟩
    refine ⟨⟨wordOp R l w, hv⟩, ?_⟩
    change tag R w d (wordOp R l w) = wordOp (grRep R w) l (wg R w)
    rw [tag_apply]
    simpa only [hl] using (grRep_word R w l).symm

/-- Finite source implies finite actual cyclic graded pieces, not finite ambient quotient. -/
theorem finite_cycDeg [FiniteDimensional ℂ T] (d : ℕ) :
    FiniteDimensional ℂ (cycDeg (grRep R w) (wg R w) d) := by
  rw [← range_symbol]
  infer_instance

end
end VOA.DeligneAudit.D1TensorG.Gr

#print axioms VOA.DeligneAudit.D1TensorG.Gr.single_mem_Lsub_iff
#print axioms VOA.DeligneAudit.D1TensorG.Gr.range_symbol
#print axioms VOA.DeligneAudit.D1TensorG.Gr.finite_cycDeg
