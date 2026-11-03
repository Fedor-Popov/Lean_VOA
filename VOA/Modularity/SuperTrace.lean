/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Foundations.Parity
import Mathlib.LinearAlgebra.Trace

/-!
# The basis-independent supertrace

For a finite-dimensional internally `ZMod 2`-graded complex vector space `M`, this file defines

`supertrace P f = trace ((-1)^F * f)`.

Here `P.parityInvol = (-1)^F` is the basis-independent parity involution constructed from the
internal direct sum.  No choice of homogeneous basis occurs in the definition.

An endomorphism has parity `p` when it sends `M_q` into `M_(p+q)`.  For homogeneous
endomorphisms the supertrace obeys Koszul cyclicity

`str(f*g) = koszul p q * str(g*f)`.

The file also proves that odd endomorphisms have zero supertrace and that the construction
reduces to the ordinary trace for the canonical purely-even grading.

This is only the Type-I trace precursor.  It does not classify simple superalgebras, construct
module traces, or address queer components and odd traces.

## Status

Proved without `sorry`, `admit`, `native_decide`, or new axioms.
-/

namespace VOA

universe u

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## Homogeneous endomorphisms -/

/-- An endomorphism has parity `p` when it shifts every homogeneous component by `p`. -/
def IsParityHomogeneousEnd (P : ParityGrading M) (p : ZMod 2) (f : Module.End ℂ M) : Prop :=
  ∀ (q : ZMod 2) ⦃x : M⦄, x ∈ P.parity q → f x ∈ P.parity (p + q)

/-- Equality of endomorphisms can be checked on the two parity pieces. -/
theorem end_ext_parity (P : ParityGrading M) {f g : Module.End ℂ M}
    (h : ∀ (q : ZMod 2) ⦃x : M⦄, x ∈ P.parity q → f x = g x) : f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨x0, hx0, x1, hx1, hsum⟩ := P.exists_parity_decomp x
  rw [← hsum, map_add, map_add, h 0 hx0, h 1 hx1]

/-- The composite of degree-`p` and degree-`q` endomorphisms has degree `p+q`. -/
theorem IsParityHomogeneousEnd.mul {P : ParityGrading M} {p q : ZMod 2}
    {f g : Module.End ℂ M} (hf : IsParityHomogeneousEnd P p f)
    (hg : IsParityHomogeneousEnd P q g) : IsParityHomogeneousEnd P (p + q) (f * g) := by
  intro r x hx
  change f (g x) ∈ P.parity ((p + q) + r)
  have h := hf (q + r) (hg r hx)
  simpa only [add_assoc] using h

/-- The parity involution supercommutes with a degree-`p` endomorphism:
`theta*f = (-1)^p f*theta`. -/
theorem parityInvol_mul_of_isParityHomogeneousEnd (P : ParityGrading M) {p : ZMod 2}
    {f : Module.End ℂ M} (hf : IsParityHomogeneousEnd P p f) :
    P.parityInvol * f = parSign p • (f * P.parityInvol) := by
  apply end_ext_parity P
  intro q x hx
  change P.parityInvol (f x) = parSign p • f (P.parityInvol x)
  rw [P.parityInvol_homog (hf q hx), P.parityInvol_homog hx, map_smul,
    parSign_add, smul_smul]

/-- Equivalently, moving the parity involution from the right to the left also contributes
`(-1)^p`: `f*theta = (-1)^p theta*f`. -/
theorem mul_parityInvol_of_isParityHomogeneousEnd (P : ParityGrading M) {p : ZMod 2}
    {f : Module.End ℂ M} (hf : IsParityHomogeneousEnd P p f) :
    f * P.parityInvol = parSign p • (P.parityInvol * f) := by
  apply end_ext_parity P
  intro q x hx
  change f (P.parityInvol x) = parSign p • P.parityInvol (f x)
  rw [P.parityInvol_homog hx, map_smul, P.parityInvol_homog (hf q hx),
    parSign_add, smul_smul]
  rw [← mul_assoc, parSign_mul_self, one_mul]

/-! ## The supertrace -/

/-- The basis-independent supertrace `str(f) = tr((-1)^F f)`. -/
noncomputable def supertrace [FiniteDimensional ℂ M]
    (P : ParityGrading M) (f : Module.End ℂ M) : ℂ :=
  LinearMap.trace ℂ M (P.parityInvol * f)

/-- The supertrace is additive. -/
theorem supertrace_add [FiniteDimensional ℂ M]
    (P : ParityGrading M) (f g : Module.End ℂ M) :
    supertrace P (f + g) = supertrace P f + supertrace P g := by
  simp [supertrace, mul_add]

/-- The supertrace is complex-linear. -/
theorem supertrace_smul [FiniteDimensional ℂ M]
    (P : ParityGrading M) (c : ℂ) (f : Module.End ℂ M) :
    supertrace P (c • f) = c * supertrace P f := by
  simp [supertrace]

/-- The supertrace packaged as a linear functional on the endomorphism algebra. -/
noncomputable def supertraceLinear [FiniteDimensional ℂ M]
    (P : ParityGrading M) : Module.End ℂ M →ₗ[ℂ] ℂ where
  toFun := supertrace P
  map_add' := supertrace_add P
  map_smul' c f := by
    rw [supertrace_smul]
    rfl

@[simp] theorem supertraceLinear_apply [FiniteDimensional ℂ M]
    (P : ParityGrading M) (f : Module.End ℂ M) :
    supertraceLinear P f = supertrace P f := rfl

/-- Odd endomorphisms have zero supertrace. -/
theorem supertrace_eq_zero_of_odd [FiniteDimensional ℂ M]
    (P : ParityGrading M) {f : Module.End ℂ M}
    (hf : IsParityHomogeneousEnd P 1 f) : supertrace P f = 0 := by
  have hcomm := parityInvol_mul_of_isParityHomogeneousEnd P hf
  have hneg : supertrace P f = -supertrace P f := by
    calc
      supertrace P f = LinearMap.trace ℂ M (P.parityInvol * f) := rfl
      _ = LinearMap.trace ℂ M (- (f * P.parityInvol)) := by
        rw [hcomm, parSign_one, neg_one_smul]
      _ = - LinearMap.trace ℂ M (f * P.parityInvol) := by rw [map_neg]
      _ = - LinearMap.trace ℂ M (P.parityInvol * f) := by
        rw [LinearMap.trace_mul_comm]
      _ = -supertrace P f := rfl
  exact neg_eq_self.mp hneg.symm

/-- A useful cyclicity identity before splitting by both parities: moving a degree-`q`
endomorphism around the supertrace contributes `(-1)^q`.  When the total degree is odd both
sides vanish; the four-case theorem below refines this to the Koszul sign. -/
theorem supertrace_mul_swap_right_degree [FiniteDimensional ℂ M]
    (P : ParityGrading M) (f : Module.End ℂ M)
    {q : ZMod 2} {g : Module.End ℂ M} (hg : IsParityHomogeneousEnd P q g) :
    supertrace P (f * g) = parSign q * supertrace P (g * f) := by
  have hmove := mul_parityInvol_of_isParityHomogeneousEnd P hg
  calc
    supertrace P (f * g) = LinearMap.trace ℂ M (P.parityInvol * (f * g)) := rfl
    _ = LinearMap.trace ℂ M (P.parityInvol * f * g) := by rw [mul_assoc]
    _ = LinearMap.trace ℂ M (g * P.parityInvol * f) :=
      LinearMap.trace_mul_cycle (R := ℂ) P.parityInvol f g
    _ = LinearMap.trace ℂ M ((parSign q • (P.parityInvol * g)) * f) := by rw [hmove]
    _ = LinearMap.trace ℂ M (parSign q • ((P.parityInvol * g) * f)) := by
      rw [Algebra.smul_mul_assoc]
    _ = parSign q * LinearMap.trace ℂ M ((P.parityInvol * g) * f) := by
      rw [map_smul]
      rfl
    _ = parSign q * LinearMap.trace ℂ M (P.parityInvol * (g * f)) := by rw [mul_assoc]
    _ = parSign q * supertrace P (g * f) := rfl

/-- **Koszul cyclicity of the supertrace.** -/
theorem supertrace_mul_comm [FiniteDimensional ℂ M]
    (P : ParityGrading M) {p q : ZMod 2}
    {f g : Module.End ℂ M} (hf : IsParityHomogeneousEnd P p f)
    (hg : IsParityHomogeneousEnd P q g) :
    supertrace P (f * g) = koszul p q * supertrace P (g * f) := by
  rcases zmod2_cases p with hp | hp <;> rcases zmod2_cases q with hq | hq <;>
    subst hp <;> subst hq
  · simpa using supertrace_mul_swap_right_degree P f hg
  · have hfg : IsParityHomogeneousEnd P 1 (f * g) := by
      simpa using hf.mul hg
    have hgf : IsParityHomogeneousEnd P 1 (g * f) := by
      simpa [add_comm] using hg.mul hf
    rw [supertrace_eq_zero_of_odd P hfg, supertrace_eq_zero_of_odd P hgf]
    simp
  · have hfg : IsParityHomogeneousEnd P 1 (f * g) := by
      simpa using hf.mul hg
    have hgf : IsParityHomogeneousEnd P 1 (g * f) := by
      simpa [add_comm] using hg.mul hf
    rw [supertrace_eq_zero_of_odd P hfg, supertrace_eq_zero_of_odd P hgf]
    simp
  · simpa using supertrace_mul_swap_right_degree P f hg

/-! ## Purely even reduction -/

/-- If the odd component is zero, every vector is even and the parity involution is the
identity. -/
theorem parityInvol_eq_id_of_odd_eq_bot (P : ParityGrading M) (hodd : P.parity 1 = ⊥) :
    P.parityInvol = LinearMap.id := by
  have heven : P.parity 0 = ⊤ := by
    calc
      P.parity 0 = P.parity 0 ⊔ P.parity 1 := by rw [hodd, sup_bot_eq]
      _ = ⊤ := P.isCompl01.sup_eq_top
  apply LinearMap.ext
  intro x
  exact P.parityInvol_even (by rw [heven]; trivial)

/-- For any purely-even internal grading, the supertrace is the ordinary trace. -/
theorem supertrace_eq_trace_of_odd_eq_bot [FiniteDimensional ℂ M]
    (P : ParityGrading M) (hodd : P.parity 1 = ⊥) (f : Module.End ℂ M) :
    supertrace P f = LinearMap.trace ℂ M f := by
  rw [supertrace, parityInvol_eq_id_of_odd_eq_bot P hodd]
  change LinearMap.trace ℂ M ((1 : Module.End ℂ M) * f) = LinearMap.trace ℂ M f
  rw [one_mul]

/-- For the canonical purely-even grading, the parity involution is the identity. -/
theorem even_parityInvol_eq_id :
    (ParityGrading.even M).parityInvol = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact (ParityGrading.even M).parityInvol_even (by simp)

/-- On a purely-even vector space, the supertrace is the ordinary trace. -/
theorem supertrace_even [FiniteDimensional ℂ M] (f : Module.End ℂ M) :
    supertrace (ParityGrading.even M) f = LinearMap.trace ℂ M f := by
  rw [supertrace, even_parityInvol_eq_id]
  change LinearMap.trace ℂ M ((1 : Module.End ℂ M) * f) = LinearMap.trace ℂ M f
  rw [one_mul]

end VOA
