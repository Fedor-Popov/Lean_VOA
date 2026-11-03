import VOA.DeligneAudit.LeviTypeA2CertGradedDefect

/-! Evaluation of a fixed-bidegree Garland defect in commuting currents. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.Sl2Weyl

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (F : ℕ → Module.End ℂ V)
  (hFF : ∀ i j, F i * F j = F j * F i)

/-- Evaluated Garland defects with fixed length and mode degree. -/
def a2GradedDefect (y : V) (m : ℕ) (n : ℕ × ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ (f : ℕ →₀ ℕ) (r s : ℕ),
    1 ≤ r ∧ m + 1 ≤ r + s ∧
      Finsupp.weight om f + (r, s) = n ∧
        v = Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1 * xx r s) y}

/-- A homogeneous polynomial evaluates into the matching box monomials
plus explicit Garland products of the same length and mode degree. -/
theorem a2_span_box_graded_explicit_eval (y : V) (m : ℕ)
    {P : R} {n : ℕ × ℕ} (hP : P.IsWeightedHomogeneous om n) :
    Sl2Weyl.evAlg F hFF P y ∈
      Submodule.span ℂ {v | ∃ f, BoxP m f ∧ Finsupp.weight om f = n ∧
        v = Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1) y} ⊔
      a2GradedDefect F hFF y m n := by
  let B : Submodule ℂ V := Submodule.span ℂ
    {v | ∃ f, BoxP m f ∧ Finsupp.weight om f = n ∧
      v = Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1) y}
  let D : Submodule ℂ V := a2GradedDefect F hFF y m n
  obtain ⟨b, hb, j, hj, rfl⟩ :=
    Submodule.mem_sup.mp (a2_box_graded_explicit_defect m hP)
  clear hP
  have hbB : Sl2Weyl.evAlg F hFF b y ∈ B := by
    induction hb using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨f, hf, hw, rfl⟩ := hx
        exact Submodule.subset_span ⟨f, hf, hw, rfl⟩
    | zero => simp
    | add x z _ _ hx hz =>
        rw [map_add, LinearMap.add_apply]
        exact B.add_mem hx hz
    | smul c x _ hx =>
        rw [map_smul, LinearMap.smul_apply]
        exact B.smul_mem c hx
  have hjD : Sl2Weyl.evAlg F hFF j y ∈ D := by
    induction hj using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨f, r, s, hr, hrs, hw, rfl⟩ := hx
        exact Submodule.subset_span ⟨f, r, s, hr, hrs, hw, rfl⟩
    | zero => simp
    | add x z _ _ hx hz =>
        rw [map_add, LinearMap.add_apply]
        exact D.add_mem hx hz
    | smul c x _ hx =>
        rw [map_smul, LinearMap.smul_apply]
        exact D.smul_mem c hx
  rw [map_add, LinearMap.add_apply]
  exact Submodule.add_mem_sup hbB hjD

end
end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_span_box_graded_explicit_eval
