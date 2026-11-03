import VOA.DeligneAudit.SL4TSpanningFlag

/-! Composition of ideal families obtained by successive Thom multiplications. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra ℂ R] [Algebra ℂ S] [Algebra ℂ T]

/-- Two successive Thom families equal the family for the composite quotient and product lift. -/
theorem thomFlagIdeal_composite (ρ : R →ₐ[ℂ] S) (hρ : Function.Surjective ρ)
    (ψ : S →ₐ[ℂ] T) (t v : R) (u : S) (hv : ρ v = u)
    (I : Ideal R) (J : Ideal S) (K : Ideal T) :
    thomFlagIdeal ρ t I (thomFlagIdeal ψ u J K) =
      thomFlagIdeal (ψ.comp ρ) (t * v) (thomFlagIdeal ρ t I J) K := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, hz, hx⟩, hy⟩
    obtain ⟨w, rfl⟩ := hρ z
    refine ⟨w, hz, x - v * w, ?_, ?_⟩
    · simpa only [map_sub, map_mul, hv] using hx
    · convert hy using 1
      ring
  · rintro ⟨w, hw, z, hz, hy⟩
    refine ⟨z + v * w, ⟨ρ w, hw, ?_⟩, ?_⟩
    · simpa only [map_add, map_mul, hv, add_sub_cancel_right] using hz
    · convert hy using 1
      ring

/-- A composite boundary is killed modulo the already completed outer and inner families. -/
theorem thomFlagIdeal_composite_kernel (ρ : R →ₐ[ℂ] S) (ψ : S →ₐ[ℂ] T)
    (t v : R) (u : S) (hv : ρ v = u) (I : Ideal R) (J : Ideal S)
    (hker : ∀ x, ψ x = 0 → u * x ∈ J) (x : R) (hx : (ψ.comp ρ) x = 0) :
    (t * v) * x ∈ thomFlagIdeal ρ t I J := by
  have hj : ρ (v * x) ∈ J := by
    rw [map_mul, hv]
    exact hker (ρ x) hx
  simpa only [mul_assoc] using thomFlagIdeal_mul ρ t I J hj

/-- A one-dimensional step remains one-dimensional after two successive Thom operations. -/
theorem thomFlagIdeal_composite_step (ρ : R →ₐ[ℂ] S) (hρ : Function.Surjective ρ)
    (ψ : S →ₐ[ℂ] T) (t v : R) (u : S) (hv : ρ v = u)
    (I : Ideal R) (J : Ideal S) (K L : Ideal T) (x : R)
    (h : L.restrictScalars ℂ = K.restrictScalars ℂ ⊔ ℂ ∙ (ψ.comp ρ) x) :
    (thomFlagIdeal ρ t I (thomFlagIdeal ψ u J L)).restrictScalars ℂ =
      (thomFlagIdeal ρ t I (thomFlagIdeal ψ u J K)).restrictScalars ℂ ⊔
        ℂ ∙ ((t * v) * x) := by
  rw [thomFlagIdeal_composite ρ hρ ψ t v u hv I J L,
    thomFlagIdeal_composite ρ hρ ψ t v u hv I J K]
  exact thomFlagIdeal_step (ψ.comp ρ) (t * v) (thomFlagIdeal ρ t I J) h

/-- Composite ideal families transport an entire spanning chain once the polynomial
relations are established modulo the preceding composite family. -/
theorem SpanningChain.thom_composite (ρ : R →ₐ[ℂ] S) (hρ : Function.Surjective ρ)
    (ψ : S →ₐ[ℂ] T) (hψ : Function.Surjective ψ)
    (t v : R) (u : S) (hv : ρ v = u) (I : Ideal R) (J : Ideal S)
    (A : Ideal R[X]) (B : Ideal T[X]) (shift : ℕ)
    (hrel : ∀ (K : Ideal T) (x : R) (n : ℕ),
      Polynomial.C ((ψ.comp ρ) x) * X ^ n ∈ K.map Polynomial.C ⊔ B →
      Polynomial.C ((t * v) * x) * X ^ (n + shift) ∈
        (thomFlagIdeal ρ t I (thomFlagIdeal ψ u J K)).map Polynomial.C ⊔ A)
    {K L : Ideal T} {ns : List ℕ} (h : SpanningChain B K L ns) :
    SpanningChain A (thomFlagIdeal ρ t I (thomFlagIdeal ψ u J K))
      (thomFlagIdeal ρ t I (thomFlagIdeal ψ u J L))
      (ns.map (fun n => n + shift)) := by
  simp only [thomFlagIdeal_composite ρ hρ ψ t v u hv I J] at hrel ⊢
  exact h.thom (ψ.comp ρ) (hψ.comp hρ) (t * v) (thomFlagIdeal ρ t I J) A B shift hrel

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.thomFlagIdeal_composite
#print axioms VOA.DeligneAudit.SL4T.thomFlagIdeal_composite_kernel
#print axioms VOA.DeligneAudit.SL4T.thomFlagIdeal_composite_step
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.thom_composite
