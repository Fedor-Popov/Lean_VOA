import VOA.DeligneAudit.LeviTypeA2CertGradedCount
import VOA.DeligneAudit.LeviTypeA2CertOrderedStepRank

/-! Finite filtration estimates for a terminal submodule of an ambient module. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviKeyFiltration

noncomputable section

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem a2_finite_terminal_of_steps (n : ℕ) (F : ℕ → Submodule ℂ M)
    (hzero : F 0 = ⊥)
    (hmono : ∀ i < n, F i ≤ F (i + 1))
    (hfinite : ∀ i < n, FiniteDimensional ℂ (StepQuot F i)) :
    FiniteDimensional ℂ (F n) := by
  have hchain (j : ℕ) (hj : j ≤ n) : FiniteDimensional ℂ (F j) := by
    induction j with
    | zero =>
        rw [hzero]
        infer_instance
    | succ j ih =>
        letI : FiniteDimensional ℂ (F j) := ih (by omega)
        let T : Submodule ℂ (F (j + 1)) :=
          (F j).comap (F (j + 1)).subtype
        have hm : T.map (F (j + 1)).subtype = F j := by
          simpa [T, inf_eq_right.mpr (hmono j (by omega))] using
            (Submodule.map_comap_subtype (p := F (j + 1)) (p' := F j))
        haveI : FiniteDimensional ℂ (T.map (F (j + 1)).subtype) := by
          rw [hm]
          infer_instance
        letI : FiniteDimensional ℂ T :=
          Module.Finite.equiv (Submodule.equivSubtypeMap (F (j + 1)) T).symm
        letI : FiniteDimensional ℂ (StepQuot F j) := hfinite j (by omega)
        exact Module.Finite.equiv (quotient_prod_linearEquiv T).some
  exact hchain n le_rfl

/-- A finite chain bounds the rank of its terminal submodule. -/
theorem a2_terminal_finrank_le_sum (n : ℕ)
    (F S : ℕ → Submodule ℂ M) (L : ℕ → ℕ)
    (hzero : F 0 = ⊥)
    (hmono : ∀ i < n, F i ≤ F (i + 1))
    (hfinite : ∀ i < n, FiniteDimensional ℂ (StepQuot F i))
    (hstep : ∀ i < n,
      Module.finrank ℂ (StepQuot F i) ≤
        L i * Module.finrank ℂ (KeyQuot F S i)) :
    Module.finrank ℂ (F n) ≤
      ∑ i ∈ Finset.range n,
        L i * Module.finrank ℂ (KeyQuot F S i) := by
  have hfin (j : ℕ) (hj : j ≤ n) : FiniteDimensional ℂ (F j) :=
    a2_finite_terminal_of_steps j F hzero
      (fun i hi => hmono i (by omega))
      (fun i hi => hfinite i (by omega))
  have hrank (i : ℕ) (hi : i < n) :
      Module.finrank ℂ (F (i + 1)) ≤
        Module.finrank ℂ (F i) +
          L i * Module.finrank ℂ (KeyQuot F S i) := by
    let T : Submodule ℂ (F (i + 1)) :=
      (F i).comap (F (i + 1)).subtype
    have heq : Module.finrank ℂ (F i) = Module.finrank ℂ T := by
      rw [← Submodule.finrank_map_subtype_eq]
      have hm : T.map (F (i + 1)).subtype = F i := by
        simpa [T, inf_eq_right.mpr (hmono i hi)] using
          (Submodule.map_comap_subtype (p := F (i + 1)) (p' := F i))
      rw [hm]
    letI : FiniteDimensional ℂ (F (i + 1)) := hfin (i + 1) (by omega)
    calc
      _ = Module.finrank ℂ (StepQuot F i) + Module.finrank ℂ T :=
        (T.finrank_quotient_add_finrank).symm
      _ ≤ L i * Module.finrank ℂ (KeyQuot F S i) +
          Module.finrank ℂ (F i) :=
        Nat.add_le_add (hstep i hi) (le_of_eq heq.symm)
      _ = _ := Nat.add_comm _ _
  have hprefix (j : ℕ) (hj : j ≤ n) :
      Module.finrank ℂ (F j) ≤
        ∑ i ∈ Finset.range j,
          L i * Module.finrank ℂ (KeyQuot F S i) := by
    induction j with
    | zero =>
        rw [hzero]
        simp
    | succ j ih =>
        rw [Finset.sum_range_succ]
        exact (hrank j (by omega)).trans
          (Nat.add_le_add_right (ih (by omega)) _)
  exact hprefix n le_rfl

end
end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_finite_terminal_of_steps
#print axioms VOA.DeligneAudit.A3Sector.a2_terminal_finrank_le_sum
