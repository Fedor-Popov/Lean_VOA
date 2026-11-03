import VOA.DeligneAudit.LeviTypeA2CertBoxDefect
import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleGradeProjection

/-! The Garland ideal at one fixed length and mode degree. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.Sl2Weyl
open VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules

noncomputable section

/-- An admissible Garland generator, indexed by its length and mode degree. -/
abbrev a2JIndex (m : ℕ) :=
  {rs : ℕ × ℕ // 1 ≤ rs.1 ∧ m + 1 ≤ rs.1 + rs.2}

def a2JGenerator {m : ℕ} (i : a2JIndex m) : R := xx i.1.1 i.1.2

def a2JWeight {m : ℕ} (i : a2JIndex m) : ℕ × ℕ := i.1

/-- Monomial multiples of Garland generators at exactly one bidegree. -/
def a2GradedJTerms (m : ℕ) (n : ℕ × ℕ) : Set R :=
  {v | ∃ (f : ℕ →₀ ℕ) (r s : ℕ),
    1 ≤ r ∧ m + 1 ≤ r + s ∧
      Finsupp.weight om f + (r, s) = n ∧
        v = MvPolynomial.monomial f 1 * xx r s}

private theorem a2J_range (m : ℕ) :
    Set.range (a2JGenerator (m := m)) =
      {x : R | ∃ r s, 1 ≤ r ∧ m + 1 ≤ r + s ∧ x = xx r s} := by
  ext x
  constructor
  · rintro ⟨⟨⟨r, s⟩, ⟨hr, hrs⟩⟩, rfl⟩
    exact ⟨r, s, hr, hrs, rfl⟩
  · rintro ⟨r, s, hr, hrs, rfl⟩
    exact ⟨⟨(r, s), ⟨hr, hrs⟩⟩, rfl⟩

/-- The degree-`n` part of `J m` is spanned by monomial multiples
`z^f x(r,s)` with `weight(f) + (r,s) = n`. -/
theorem a2_J_component_explicit (m : ℕ) (n : ℕ × ℕ)
    {P : R} (hP : P ∈ J m) :
    MvPolynomial.weightedHomogeneousComponent om n P ∈
      Submodule.span ℂ (a2GradedJTerms m n) := by
  have hgen : ∀ i : a2JIndex m,
      (a2JGenerator i).IsWeightedHomogeneous om (a2JWeight i) := by
    intro i
    exact xx_hom i.1.1 i.1.2
  have hspan : P ∈ Ideal.span (Set.range (a2JGenerator (m := m))) := by
    simpa [J, a2J_range] using hP
  have h := ideal_component_mem_matching_span om
    (a2JGenerator (m := m)) (a2JWeight (m := m)) hgen hspan n
  apply (Submodule.span_mono ?_) h
  rintro v ⟨i, f, hf, rfl⟩
  exact ⟨f, i.1.1, i.1.2, i.2.1, i.2.2, hf, rfl⟩

/-- Homogeneous box reduction with every ideal defect at the same
length and mode degree as the input. -/
theorem a2_box_graded_explicit_defect (m : ℕ) {P : R} {n : ℕ × ℕ}
    (hP : P.IsWeightedHomogeneous om n) :
    P ∈ Submodule.span ℂ
        {v | ∃ f, BoxP m f ∧ Finsupp.weight om f = n ∧
          v = MvPolynomial.monomial f 1} ⊔
      Submodule.span ℂ (a2GradedJTerms m n) := by
  obtain ⟨b, hb, j, hj, hbj⟩ := Submodule.mem_sup.mp (box_span m P)
  rw [← hP.weightedHomogeneousComponent_same, ← hbj, map_add]
  refine Submodule.add_mem_sup ?_ (a2_J_component_explicit m n hj)
  clear hbj
  induction hb using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨f, hf, -, rfl⟩ := hx
      have hh := MvPolynomial.isWeightedHomogeneous_monomial om f (1 : ℂ) rfl
      by_cases hn : n = Finsupp.weight om f
      · rw [hn, hh.weightedHomogeneousComponent_same]
        exact Submodule.subset_span ⟨f, hf, rfl, rfl⟩
      · rw [hh.weightedHomogeneousComponent_ne n hn]
        exact Submodule.zero_mem _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

end
end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_J_component_explicit
#print axioms VOA.DeligneAudit.A3Sector.a2_box_graded_explicit_defect
