import VOA.DeligneAudit.D4LeviKSPairInvariant

/-! The unrestricted polynomial kernel of the PAIR substitution. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

/-- Choose the Y copy when lifting a paired target variable. -/
def pairSectionVariable (a b c : ℕ) : PairTarget a b c → PairSource a b c
  | Sum.inl x => Sum.inl (Sum.inr x)
  | Sum.inr (Sum.inl y) => Sum.inr (Sum.inl y)
  | Sum.inr (Sum.inr z) => Sum.inr (Sum.inr z)

theorem pairVariable_section (a b c : ℕ) (t : PairTarget a b c) :
    pairVariable a b c (pairSectionVariable a b c t) = t := by
  rcases t with x | yz
  · rfl
  rcases yz with y | z <;> rfl

noncomputable def pairSection (a b c : ℕ) :
    MvPolynomial (PairTarget a b c) ℂ →ₐ[ℂ]
      MvPolynomial (PairSource a b c) ℂ :=
  rename (pairSectionVariable a b c)

theorem pairRestriction_section (a b c : ℕ)
    (P : MvPolynomial (PairTarget a b c) ℂ) :
    pairRestriction a b c (pairSection a b c P) = P := by
  induction P using MvPolynomial.induction_on with
  | C z => simp [pairRestriction, pairSection]
  | add P Q hP hQ => simpa only [map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P t hP =>
      simp only [map_mul, hP]
      simp [pairRestriction, pairSection, pairVariable_section]

/-- The variable relations in the labelled substitution kernel. -/
noncomputable def pairVariableIdeal (a b c : ℕ) :
    Ideal (MvPolynomial (PairSource a b c) ℂ) :=
  Ideal.span (Set.range fun y : Fin b =>
    X (Sum.inl (Sum.inl y)) - X (Sum.inr (Sum.inl y)))

theorem pairVariableRelation_mem (a b c : ℕ) (y : Fin b) :
    X (Sum.inl (Sum.inl y)) - X (Sum.inr (Sum.inl y)) ∈
      pairVariableIdeal a b c :=
  Ideal.subset_span ⟨y, rfl⟩

theorem pairVariableIdeal_le_kernel (a b c : ℕ) :
    pairVariableIdeal a b c ≤
      RingHom.ker (pairRestriction a b c).toRingHom := by
  apply Ideal.span_le.mpr
  rintro P ⟨y, rfl⟩
  change pairRestriction a b c
    (X (Sum.inl (Sum.inl y)) - X (Sum.inr (Sum.inl y))) = 0
  rw [map_sub, pairRestriction_paired_X, pairRestriction_Y, sub_self]

private theorem pairVariable_sub_section_mem (a b c : ℕ)
    (i : PairSource a b c) :
    X i - pairSection a b c (pairRestriction a b c (X i)) ∈
      pairVariableIdeal a b c := by
  rcases i with x | yz
  · rcases x with y | x
    · simpa [pairSection, pairSectionVariable, pairRestriction_paired_X]
        using pairVariableRelation_mem a b c y
    · simp [pairSection, pairSectionVariable, pairRestriction_unpaired_X]
  · rcases yz with y | z
    · simp [pairSection, pairSectionVariable, pairRestriction_Y]
    · simp [pairSection, pairSectionVariable, pairRestriction_Z]

/-- Every polynomial differs from its chosen lift of the restriction by
    a combination of paired-variable differences. -/
theorem pair_sub_section_mem (a b c : ℕ)
    (P : MvPolynomial (PairSource a b c) ℂ) :
    P - pairSection a b c (pairRestriction a b c P) ∈
      pairVariableIdeal a b c := by
  let F : MvPolynomial (PairSource a b c) ℂ →ₐ[ℂ]
      MvPolynomial (PairSource a b c) ℂ :=
    (pairSection a b c).comp (pairRestriction a b c)
  change P - F P ∈ pairVariableIdeal a b c
  induction P using MvPolynomial.induction_on with
  | C z => simp [F]
  | add P Q hP hQ =>
      have h := (pairVariableIdeal a b c).add_mem hP hQ
      convert h using 1 <;> simp [map_add] <;> abel
  | mul_X P i hP =>
      have hi : X i - F (X i) ∈ pairVariableIdeal a b c := by
        simpa only [F, AlgHom.comp_apply] using
          pairVariable_sub_section_mem a b c i
      have h₁ := (pairVariableIdeal a b c).mul_mem_left (F P) hi
      have h₂ := (pairVariableIdeal a b c).mul_mem_right (X i) hP
      have h := (pairVariableIdeal a b c).add_mem h₁ h₂
      convert h using 1 <;> simp [map_mul] <;> ring

/-- Exact kernel presentation of the labelled PAIR restriction. -/
theorem pairRestriction_kernel (a b c : ℕ) :
    RingHom.ker (pairRestriction a b c).toRingHom =
      pairVariableIdeal a b c := by
  apply le_antisymm
  · intro P hP
    have hzero : pairRestriction a b c P = 0 := hP
    have h := pair_sub_section_mem a b c P
    simpa [hzero] using h
  · exact pairVariableIdeal_le_kernel a b c

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_section
#print axioms VOA.DeligneAudit.D4Levi.pairVariableRelation_mem
#print axioms VOA.DeligneAudit.D4Levi.pairVariableIdeal_le_kernel
#print axioms VOA.DeligneAudit.D4Levi.pair_sub_section_mem
#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_kernel
