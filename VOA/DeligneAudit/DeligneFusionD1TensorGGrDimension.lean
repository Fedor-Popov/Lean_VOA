import VOA.DeligneAudit.DeligneFusionD1TensorGGrPieces
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Rank-nullity for actual cyclic current-degree pieces, followed by telescoping.
The finite source is explicit; no claim concerns the unused ambient quotient. -/
namespace VOA.DeligneAudit.D1TensorG.Gr

open VOA.DeligneAudit.SectorWeyl

noncomputable section
variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {T : Type*} [AddCommGroup T] [Module ℂ T]
variable (R : CurrentModule f T) (w : T)

/-- The symbol kernel is the actual lower filtration piece. -/
def kernelEquivLower (d : ℕ) :
    LinearMap.ker (symbol R w d) ≃ₗ[ℂ] Fbelow R w d where
  toFun v := ⟨v.1.1, (symbol_eq_zero_iff R w d v.1).mp v.2⟩
  invFun v := by
    refine ⟨⟨v.1, Fbelow_mono R w (Nat.le_succ d) v.2⟩, ?_⟩
    exact (symbol_eq_zero_iff R w d _).mpr v.2
  left_inv v := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv v := by apply Subtype.ext; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [FiniteDimensional ℂ T]

theorem piece_rank_step (d : ℕ) :
    Module.finrank ℂ (cycDeg (grRep R w) (wg R w) d) +
      Module.finrank ℂ (Fbelow R w d) = Module.finrank ℂ (Fbelow R w (d + 1)) := by
  have he := (symbol R w d).finrank_range_add_finrank_ker
  rw [range_symbol R w d, (kernelEquivLower R w d).finrank_eq] at he
  exact he

/-- The finite degree sum is exactly the rank of the corresponding source filtration piece. -/
theorem sum_finrank_eq_Fbelow (B : ℕ) :
    (∑ d ∈ Finset.range B, Module.finrank ℂ (cycDeg (grRep R w) (wg R w) d)) =
      Module.finrank ℂ (Fbelow R w B) := by
  induction B with
  | zero =>
      rw [Finset.range_zero, Finset.sum_empty, Fbelow_zero R w]
      simp
  | succ B ih =>
      rw [Finset.sum_range_succ, ih]
      have hs := piece_rank_step R w B
      omega

theorem sum_finrank_le_source (B : ℕ) :
    (∑ d ∈ Finset.range B, Module.finrank ℂ (cycDeg (grRep R w) (wg R w) d)) ≤
      Module.finrank ℂ T := by
  rw [sum_finrank_eq_Fbelow]
  exact Submodule.finrank_le _

/-- Every vector in the actual source word span has a finite filtration bound. -/
theorem source_span_has_bound {v : T}
    (hv : v ∈ Submodule.span ℂ (Set.range fun l : List (Fin n × ℕ) => wordOp R l w)) :
    ∃ B : ℕ, v ∈ Fbelow R w B := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, rfl⟩ := hv
      exact ⟨degree l + 1, Submodule.subset_span ⟨l, Nat.lt_succ_self _, rfl⟩⟩
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add u v hu hv ihu ihv =>
      obtain ⟨a, ha⟩ := ihu
      obtain ⟨b, hb⟩ := ihv
      exact ⟨max a b, Submodule.add_mem _
        (Fbelow_mono R w (le_max_left _ _) ha) (Fbelow_mono R w (le_max_right _ _) hb)⟩
  | smul c v hv ih =>
      obtain ⟨B, hB⟩ := ih
      exact ⟨B, Submodule.smul_mem _ c hB⟩

/-- A finite cyclic source is attained by a finite current-degree filtration piece. -/
theorem exists_Fbelow_top
    (hspan : Submodule.span ℂ
      (Set.range fun l : List (Fin n × ℕ) => wordOp R l w) = ⊤) :
    ∃ B : ℕ, Fbelow R w B = ⊤ := by
  classical
  let b := Module.finBasis ℂ T
  have he : ∀ i, ∃ B : ℕ, b i ∈ Fbelow R w B := by
    intro i
    apply source_span_has_bound R w
    rw [hspan]
    exact Submodule.mem_top
  choose bounds hbounds using he
  let B : ℕ := ∑ i, bounds i
  refine ⟨B, ?_⟩
  have hb : ∀ i, b i ∈ Fbelow R w B := by
    intro i
    apply Fbelow_mono R w ?_ (hbounds i)
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (bounds j)) (Finset.mem_univ i)
  apply top_unique
  intro v _
  rw [← b.sum_repr v]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (hb i)

/-- The actual cyclic graded degree sum stabilizes at the source rank. -/
theorem exists_stable_sum_finrank
    (hspan : Submodule.span ℂ
      (Set.range fun l : List (Fin n × ℕ) => wordOp R l w) = ⊤) :
    ∃ B : ℕ, ∀ C : ℕ, B ≤ C →
      (∑ d ∈ Finset.range C, Module.finrank ℂ (cycDeg (grRep R w) (wg R w) d)) =
        Module.finrank ℂ T := by
  obtain ⟨B, hB⟩ := exists_Fbelow_top R w hspan
  refine ⟨B, fun C hBC => ?_⟩
  rw [sum_finrank_eq_Fbelow]
  have hC : Fbelow R w C = ⊤ := by
    apply top_unique
    rw [← hB]
    exact Fbelow_mono R w hBC
  rw [hC]
  simp

end
end VOA.DeligneAudit.D1TensorG.Gr

#print axioms VOA.DeligneAudit.D1TensorG.Gr.piece_rank_step
#print axioms VOA.DeligneAudit.D1TensorG.Gr.sum_finrank_eq_Fbelow

#print axioms VOA.DeligneAudit.D1TensorG.Gr.exists_Fbelow_top
#print axioms VOA.DeligneAudit.D1TensorG.Gr.exists_stable_sum_finrank
