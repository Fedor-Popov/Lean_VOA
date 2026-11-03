import VOA.DeligneAudit.D4CharSl2Graded

/-! Degree-preserving sl2 and extra Cartan actions on the lowering-current span. -/

namespace VOA.DeligneAudit.D4Char

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem sl2LowerDegree_self (F : ℕ → Module.End ℂ V) (y : V) :
    y ∈ sl2LowerDegree F y 0 := Submodule.subset_span ⟨[], rfl, rfl⟩

theorem sl2LowerDegree_lower (F : ℕ → Module.End ℂ V) (y : V) (d s : ℕ) :
    sl2LowerDegree F y d ≤ (sl2LowerDegree F y (d + s)).comap (F s) := by
  apply Submodule.span_le.mpr
  rintro v ⟨l, hl, rfl⟩
  exact Submodule.subset_span ⟨s :: l, by simp [hl, Nat.add_comm], rfl⟩

/-- A Cartan current, including an extra central direction, preserves exact degrees. -/
theorem sl2LowerDegree_cartan (F K : ℕ → Module.End ℂ V) (c : ℂ)
    (hKF : ∀ s k, K s * F k - F k * K s = c • F (s + k))
    (y : V) (hK0 : ∃ a : ℂ, K 0 y = a • y)
    (hKpos : ∀ s, 0 < s → K s y = 0) (d s : ℕ) :
    sl2LowerDegree F y d ≤ (sl2LowerDegree F y (d + s)).comap (K s) := by
  have hw : ∀ l : List ℕ,
      K s ((l.map F).prod y) ∈ sl2LowerDegree F y (l.sum + s) := by
    intro l
    induction l with
    | nil =>
        simp only [List.map_nil, List.prod_nil, Module.End.one_apply, List.sum_nil,
          zero_add]
        rcases Nat.eq_zero_or_pos s with rfl | hs
        · obtain ⟨a, ha⟩ := hK0
          rw [ha]
          exact Submodule.smul_mem _ _ (sl2LowerDegree_self F y)
        · rw [hKpos s hs]
          exact Submodule.zero_mem _
    | cons k l ih =>
        have hh := congrArg (fun A : Module.End ℂ V => A ((l.map F).prod y))
          (hKF s k)
        simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at hh
        simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.sum_cons]
        rw [sub_eq_iff_eq_add.mp hh]
        apply Submodule.add_mem
        · apply Submodule.smul_mem
          exact Submodule.subset_span ⟨(s + k) :: l, by simp; omega, rfl⟩
        · simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            sl2LowerDegree_lower F y (l.sum + s) k ih
  apply Submodule.span_le.mpr
  rintro v ⟨l, hl, rfl⟩
  simpa only [hl] using hw l

theorem sl2LowerDegree_raise {E H F : ℕ → Module.End ℂ V}
    (hS : CVsl2.SL2 E H F) (y : V) (hE : ∀ s, E s y = 0)
    (hH0 : ∃ a : ℂ, H 0 y = a • y) (hHpos : ∀ s, 0 < s → H s y = 0)
    (d s : ℕ) :
    sl2LowerDegree F y d ≤ (sl2LowerDegree F y (d + s)).comap (E s) := by
  have hw : ∀ l : List ℕ,
      E s ((l.map F).prod y) ∈ sl2LowerDegree F y (l.sum + s) := by
    intro l
    induction l with
    | nil => simpa only [List.map_nil, List.prod_nil, Module.End.one_apply, hE] using
        (Submodule.zero_mem (sl2LowerDegree F y (([] : List ℕ).sum + s)))
    | cons k l ih =>
        have hh := congrArg (fun A : Module.End ℂ V => A ((l.map F).prod y))
          (hS.hEF s k)
        simp only [LinearMap.sub_apply, Module.End.mul_apply] at hh
        simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.sum_cons]
        rw [sub_eq_iff_eq_add.mp hh]
        apply Submodule.add_mem
        · have hl : (l.map F).prod y ∈ sl2LowerDegree F y l.sum :=
            Submodule.subset_span ⟨l, rfl, rfl⟩
          simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            sl2LowerDegree_cartan F H (-2) hS.hHF y hH0 hHpos l.sum (s + k) hl
        · simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            sl2LowerDegree_lower F y (l.sum + s) k ih
  apply Submodule.span_le.mpr
  rintro v ⟨l, hl, rfl⟩
  simpa only [hl] using hw l

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.sl2LowerDegree_self
#print axioms VOA.DeligneAudit.D4Char.sl2LowerDegree_lower
#print axioms VOA.DeligneAudit.D4Char.sl2LowerDegree_cartan
#print axioms VOA.DeligneAudit.D4Char.sl2LowerDegree_raise
