import VOA.DeligneAudit.D4FusionToroidalFusionCyclic

/-!
# Finite cutoff of the cyclic `t` filtration

The actual evaluation tensor is finite dimensional and cyclic at distinct
points, so its increasing word filtration reaches the full source space.
-/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.D1TensorG VOA.DeligneAudit.DeligneSector

noncomputable section

variable (S : DeligneSectorData)
variable (hskew : ∀ a b c, S.f a b c = -S.f b a c)
variable {N : ℕ} (z : Fin N → ℂ)

/-- Each vector of the cyclic span has a finite `t`-degree bound. -/
theorem evalCyclic_has_bound {v : D1TensorG.Space S.n N}
    (hv : v ∈ evalCyclic S hskew z) :
    ∃ B : ℕ, v ∈ evalFbelow (d1EvalAction S.f S.jacobi hskew z)
      (D1TensorG.generator S.c₀) B := by
  change v ∈ Submodule.span ℂ (Set.range fun l : List (TLtr S.n) =>
    evalWord (d1EvalAction S.f S.jacobi hskew z) l
      (D1TensorG.generator S.c₀)) at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, rfl⟩ := hv
      exact ⟨tDegree l + 1,
        Submodule.subset_span ⟨l, Nat.lt_succ_self _, rfl⟩⟩
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add u v hu hv ihu ihv =>
      obtain ⟨a, ha⟩ := ihu
      obtain ⟨b, hb⟩ := ihv
      exact ⟨max a b, Submodule.add_mem _
        (evalFbelow_mono _ _ (le_max_left _ _) ha)
        (evalFbelow_mono _ _ (le_max_right _ _) hb)⟩
  | smul c v hv ih =>
      obtain ⟨B, hB⟩ := ih
      exact ⟨B, Submodule.smul_mem _ c hB⟩

/-- The cyclic evaluation filtration reaches the full tensor product. -/
theorem exists_evalFbelow_top (hz : Function.Injective z) :
    ∃ B : ℕ, evalFbelow (d1EvalAction S.f S.jacobi hskew z)
      (D1TensorG.generator S.c₀) B = ⊤ := by
  classical
  let b := Module.finBasis ℂ (D1TensorG.Space S.n N)
  have he : ∀ i, ∃ B : ℕ, b i ∈ evalFbelow
      (d1EvalAction S.f S.jacobi hskew z) (D1TensorG.generator S.c₀) B := by
    intro i
    apply evalCyclic_has_bound S hskew z
    rw [evalCyclic_top S hskew z hz]
    exact Submodule.mem_top
  choose bounds hbounds using he
  let B : ℕ := ∑ i, bounds i
  refine ⟨B, ?_⟩
  have hb : ∀ i, b i ∈ evalFbelow (d1EvalAction S.f S.jacobi hskew z)
      (D1TensorG.generator S.c₀) B := by
    intro i
    apply evalFbelow_mono _ _ ?_ (hbounds i)
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (bounds j)) (Finset.mem_univ i)
  apply top_unique
  intro v _
  rw [← b.sum_repr v]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (hb i)

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.evalCyclic_has_bound
#print axioms VOA.DeligneAudit.Toroidal.exists_evalFbelow_top
