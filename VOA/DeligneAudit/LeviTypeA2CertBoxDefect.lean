import VOA.DeligneAudit.LeviTypeA2CertSpectatorBox

/-! Box spanning with its Garland-ideal defect retained explicitly. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.Sl2Weyl

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (F : ℕ → Module.End ℂ V)
  (hFF : ∀ i j, F i * F j = F j * F i)

/-- The image of all multiples of Garland generators for the weight `m` box. -/
def a2BoxDefect (y : V) (m : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ (r s : ℕ) (a : R),
    1 ≤ r ∧ m + 1 ≤ r + s ∧
    v = Sl2Weyl.evAlg F hFF (a * xx r s) y}

/-- Every multiple of the Garland ideal evaluates into the explicit defect span. -/
theorem a2BoxDefect_mul_mem (y : V) (m : ℕ) {x : R}
    (hx : x ∈ J m) (a : R) :
    Sl2Weyl.evAlg F hFF (a * x) y ∈ a2BoxDefect F hFF y m := by
  let D : Submodule ℂ V := a2BoxDefect F hFF y m
  induction hx using Submodule.span_induction generalizing a with
  | mem x hx =>
      obtain ⟨r, s, hr, hrs, rfl⟩ := hx
      exact Submodule.subset_span ⟨r, s, a, hr, hrs, rfl⟩
  | zero => simp
  | add x z _ _ hx hz =>
      rw [mul_add, map_add, LinearMap.add_apply]
      exact D.add_mem (hx a) (hz a)
  | smul c x _ hx =>
      rw [smul_eq_mul, ← mul_assoc]
      exact hx (a * c)

/-- Box spanning without imposing any Garland relations on `y`. -/
theorem a2_span_box_with_defect (y : V) (m : ℕ) (P : R) :
    Sl2Weyl.evAlg F hFF P y ∈
      Submodule.span ℂ {v | ∃ f, BoxP m f ∧
        v = Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1) y} ⊔
        a2BoxDefect F hFF y m := by
  let B : Submodule ℂ V := Submodule.span ℂ {v | ∃ f, BoxP m f ∧
    v = Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1) y}
  let D : Submodule ℂ V := a2BoxDefect F hFF y m
  obtain ⟨b, hb, j, hj, rfl⟩ := Submodule.mem_sup.mp (box_span m P)
  have hjD : Sl2Weyl.evAlg F hFF j y ∈ D := by
    simpa only [one_mul] using a2BoxDefect_mul_mem F hFF y m hj 1
  have hbB : Sl2Weyl.evAlg F hFF b y ∈ B := by
    induction hb using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨f, hf, -, rfl⟩ := hx
        exact Submodule.subset_span ⟨f, hf, rfl⟩
    | zero => simp
    | add x z _ _ hx hz =>
        rw [map_add, LinearMap.add_apply]
        exact B.add_mem hx hz
    | smul c x _ hx =>
        rw [map_smul, LinearMap.smul_apply]
        exact B.smul_mem c hx
  rw [map_add, LinearMap.add_apply]
  exact Submodule.add_mem_sup hbB hjD

/-- Homogeneous box spanning keeps the box monomials at the input length
and mode degree, while retaining the Garland-ideal defect. -/
theorem a2_span_box_graded_with_defect (y : V) (m : ℕ)
    {P : R} {n : ℕ × ℕ}
    (hp : MvPolynomial.IsWeightedHomogeneous om P n) :
    Sl2Weyl.evAlg F hFF P y ∈
      Submodule.span ℂ {v | ∃ f, BoxP m f ∧ Finsupp.weight om f = n ∧
        v = Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1) y} ⊔
        a2BoxDefect F hFF y m := by
  let B : Submodule ℂ V := Submodule.span ℂ {v | ∃ f, BoxP m f ∧
    Finsupp.weight om f = n ∧
    v = Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1) y}
  let D : Submodule ℂ V := a2BoxDefect F hFF y m
  obtain ⟨b, hb, j, hj, rfl⟩ := Submodule.mem_sup.mp (box_span_graded m hp)
  have hjD : Sl2Weyl.evAlg F hFF j y ∈ D := by
    simpa only [one_mul] using a2BoxDefect_mul_mem F hFF y m hj 1
  clear hp
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
  rw [map_add, LinearMap.add_apply]
  exact Submodule.add_mem_sup hbB hjD

end
end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2BoxDefect_mul_mem
#print axioms VOA.DeligneAudit.A3Sector.a2_span_box_with_defect
#print axioms VOA.DeligneAudit.A3Sector.a2_span_box_graded_with_defect
