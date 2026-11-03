import VOA.DeligneAudit.SL4TCell
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Finite-dimensionality from two annihilating elements -/

namespace VOA.DeligneAudit.SL4T

universe u

/-- If `ab = 0`, the ideal `(a)` is a linear image of `A/(b)`. Hence finiteness of
both boundary quotients implies finiteness of `A`, with the sum of their dimensions as a bound. -/
theorem finite_of_annihilating_pair {A : Type u} [CommRing A] [Algebra ℂ A]
    (a b : A) (hab : a * b = 0)
    (hfa : FiniteDimensional ℂ (A ⧸ Ideal.span {a}))
    (hfb : FiniteDimensional ℂ (A ⧸ Ideal.span {b})) :
    FiniteDimensional ℂ A ∧ Module.finrank ℂ A ≤
      Module.finrank ℂ (A ⧸ Ideal.span {a}) + Module.finrank ℂ (A ⧸ Ideal.span {b}) := by
  let P := (Ideal.span {a}).restrictScalars ℂ
  let Q := (Ideal.span {b}).restrictScalars ℂ
  let f : A →ₗ[ℂ] P := (LinearMap.mulLeft ℂ a).codRestrict P fun x =>
    Ideal.mem_span_singleton.mpr ⟨x, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
    exact ⟨y, Subtype.ext hy.symm⟩
  have hQ : Q ≤ LinearMap.ker f := by
    intro x hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
    apply Subtype.ext
    change a * x = 0
    rw [hy, ← mul_assoc, hab, zero_mul]
  let g : (A ⧸ Q) →ₗ[ℂ] P := Q.liftQ f hQ
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨y, rfl⟩ := hf x
    exact ⟨Q.mkQ y, rfl⟩
  haveI : FiniteDimensional ℂ (A ⧸ Q) := hfb
  haveI : FiniteDimensional ℂ P := Module.Finite.of_surjective g hg
  haveI : FiniteDimensional ℂ (A ⧸ P) := hfa
  haveI : FiniteDimensional ℂ A := Module.Finite.of_submodule_quotient P
  refine ⟨inferInstance, ?_⟩
  have hp := LinearMap.finrank_le_finrank_of_surjective hg
  have hd := P.finrank_quotient_add_finrank
  change Module.finrank ℂ P ≤ Module.finrank ℂ (A ⧸ Ideal.span {b}) at hp
  change Module.finrank ℂ (A ⧸ Ideal.span {a}) + Module.finrank ℂ P =
    Module.finrank ℂ A at hd
  omega

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.finite_of_annihilating_pair
