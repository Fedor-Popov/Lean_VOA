import VOA.DeligneAudit.LeviKeyFiltration

/-! Finiteness propagation from finite local-Weyl layers. -/

namespace VOA.DeligneAudit.LeviKeyFiltration

noncomputable section

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- A finite chain with finite successive quotients has finite total dimension. -/
theorem finite_of_finite_steps (n : ℕ) (F : ℕ → Submodule K M)
    (hzero : F 0 = ⊥) (htop : F n = ⊤)
    (hmono : ∀ i < n, F i ≤ F (i + 1))
    (hfinite : ∀ i < n, FiniteDimensional K (StepQuot F i)) :
    FiniteDimensional K M := by
  have hchain (j : ℕ) (hj : j ≤ n) : FiniteDimensional K (F j) := by
    induction j with
    | zero =>
      rw [hzero]
      infer_instance
    | succ j ih =>
      letI : FiniteDimensional K (F j) := ih (by omega)
      let T : Submodule K (F (j + 1)) := (F j).comap (F (j + 1)).subtype
      have hm : T.map (F (j + 1)).subtype = F j := by
        simpa [T, inf_eq_right.mpr (hmono j (by omega))] using
          (Submodule.map_comap_subtype (p := F (j + 1)) (p' := F j))
      haveI : FiniteDimensional K (T.map (F (j + 1)).subtype) := by
        rw [hm]
        infer_instance
      letI : FiniteDimensional K T :=
        Module.Finite.equiv (Submodule.equivSubtypeMap (F (j + 1)) T).symm
      letI : FiniteDimensional K (StepQuot F j) := hfinite j (by omega)
      exact Module.Finite.equiv (quotient_prod_linearEquiv T).some
  haveI : FiniteDimensional K (F n) := hchain n le_rfl
  rw [htop] at this
  exact Module.Finite.of_surjective (⊤ : Submodule K M).subtype
    (fun x => ⟨⟨x, trivial⟩, rfl⟩)

/-- The key bound without assuming the generated module finite in advance. -/
theorem key_filtered_weyl_bound_of_finite_steps
    (n : ℕ) (F S : ℕ → Submodule K M) (d : ℕ → ℕ)
    (hzero : F 0 = ⊥) (htop : F n = ⊤)
    (hmono : ∀ i < n, F i ≤ F (i + 1))
    (hfinite : ∀ i < n, FiniteDimensional K (StepQuot F i))
    (hstep : ∀ i < n,
      Module.finrank K (StepQuot F i) ≤ d i * Module.finrank K (KeyQuot F S i)) :
    Module.finrank K M ≤
      ∑ i ∈ Finset.range n, d i * Module.finrank K (KeyQuot F S i) := by
  letI : FiniteDimensional K M := finite_of_finite_steps n F hzero htop hmono hfinite
  exact key_filtered_weyl_bound n F S d hzero htop hmono hstep

end
end VOA.DeligneAudit.LeviKeyFiltration

#print axioms VOA.DeligneAudit.LeviKeyFiltration.finite_of_finite_steps
#print axioms VOA.DeligneAudit.LeviKeyFiltration.key_filtered_weyl_bound_of_finite_steps
