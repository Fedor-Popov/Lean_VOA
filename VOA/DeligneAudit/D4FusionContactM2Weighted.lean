import VOA.DeligneAudit.D4FusionContactM2Spanning

/-! Well-founded sparse-row reduction for arbitrary indices, including all
commutative words. Actual rows with nonzero leading coefficient and strictly
smaller tail weights suffice; no dimension or independence premise is used. -/
namespace VOA.DeligneAudit.D4FusionContact.Polynomial

variable {K V ι A : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- An actual sparse relation lowers a natural weight. Thus the normal images
span modulo P, even when the index type is infinite. -/
theorem weighted_rows_span_le (P : Submodule K V) (b : ι → V)
    (weight : ι → ℕ) (normalVector : A → V)
    (rows : ∀ i, (∃ a, b i = normalVector a) ∨ ∃ (a : K) (tail : List (K × ι)),
      a ≠ 0 ∧ (∀ t ∈ tail, weight t.2 < weight i) ∧
        a • b i + (tail.map fun t => t.1 • b t.2).sum ∈ P) :
    Submodule.span K (Set.range b) ≤ P ⊔ Submodule.span K (Set.range normalVector) := by
  let Q := P ⊔ Submodule.span K (Set.range normalVector)
  have sum_mem : ∀ l : List (K × ι),
      (∀ t ∈ l, t.1 • b t.2 ∈ Q) → (l.map fun t => t.1 • b t.2).sum ∈ Q := by
    intro l
    induction l with
    | nil => intro _; exact Q.zero_mem
    | cons t l ih =>
      intro h
      exact Q.add_mem (h t (List.mem_cons_self))
        (ih (fun s hs => h s (List.mem_cons_of_mem t hs)))
  have hb : ∀ n : ℕ, ∀ i, weight i = n → b i ∈ Q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi
      rcases rows i with hnorm | ⟨a, tail, ha, hweight, hrow⟩
      · obtain ⟨a, ha⟩ := hnorm
        exact (show Submodule.span K (Set.range normalVector) ≤ Q from le_sup_right)
          (Submodule.subset_span ⟨a, ha.symm⟩)
      · have htail : (tail.map fun t => t.1 • b t.2).sum ∈ Q := by
          apply sum_mem
          intro t ht
          exact Q.smul_mem t.1 (ih (weight t.2) (by rw [← hi]; exact hweight t ht) t.2 rfl)
        have hfull : a • b i + (tail.map fun t => t.1 • b t.2).sum ∈ Q :=
          (show P ≤ Q from le_sup_left) hrow
        have hsingle : a • b i ∈ Q := by
          have he : a • b i =
              (a • b i + (tail.map fun t => t.1 • b t.2).sum) -
                (tail.map fun t => t.1 • b t.2).sum := by abel
          rw [he]
          exact Q.sub_mem hfull htail
        have hscale := Q.smul_mem a⁻¹ hsingle
        simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using hscale
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact hb (weight i) i rfl

end VOA.DeligneAudit.D4FusionContact.Polynomial

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.weighted_rows_span_le
