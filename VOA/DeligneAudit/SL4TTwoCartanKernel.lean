import VOA.DeligneAudit.SL4TRadicalGrassmannianPowerSums

/-!
Propagation of relative multiplicity relations using the two retained Cartan currents.
The base-saturated kernel is used because base multiplication need not preserve an
arbitrary vector in the kernel of a linear map.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {B R V ι : Type*} [CommRing B] [CommRing R] [Algebra ℂ B] [Algebra ℂ R]
variable [AddCommGroup V] [Module ℂ V]

/-- Relations that vanish after every multiplication from the coefficient algebra. -/
def baseSaturatedEvaluationKernel (β : B →ₐ[ℂ] R) (π : R →ₗ[ℂ] V) : Submodule ℂ R where
  carrier := {x | ∀ b, π (β b * x) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy b
    simp only [mul_add, map_add, hx b, hy b, add_zero]
  smul_mem' := by
    intro z x hx b
    simp only [mul_smul_comm, map_smul, hx b, smul_zero]

/-- Saturated relations are stable under further multiplication by base coefficients. -/
theorem baseSaturatedEvaluationKernel_base_mul (β : B →ₐ[ℂ] R) (π : R →ₗ[ℂ] V)
    {x : R} (hx : x ∈ baseSaturatedEvaluationKernel β π) (b : B) :
    β b * x ∈ baseSaturatedEvaluationKernel β π := by
  intro c
  simpa only [map_mul, mul_assoc] using hx (c * b)

/-- The two Cartan combinations isolate both radical power sums on saturated relations. -/
theorem twoCartan_saturatedKernel_generators (β : B →ₐ[ℂ] R) (π : R →ₗ[ℂ] V)
    (u v : B) (g₁ g₂ : R) (h₁ h₂ : Module.End ℂ V)
    (hc₁ : ∀ x, h₁ (π x) = π ((β u - (2 : ℂ) • g₁ - g₂) * x))
    (hc₂ : ∀ x, h₂ (π x) = π ((β v + g₁ - g₂) * x))
    {x : R} (hx : x ∈ baseSaturatedEvaluationKernel β π) :
    g₁ * x ∈ baseSaturatedEvaluationKernel β π ∧
      g₂ * x ∈ baseSaturatedEvaluationKernel β π := by
  have hpair (b : B) : π (β b * (g₁ * x)) = 0 ∧ π (β b * (g₂ * x)) = 0 := by
    have hfirst := hc₁ (β b * x)
    have hlast := hc₂ (β b * x)
    rw [hx b, map_zero] at hfirst hlast
    have efirst : (β u - (2 : ℂ) • g₁ - g₂) * (β b * x) =
        β (u * b) * x - (2 : ℂ) • (β b * (g₁ * x)) - β b * (g₂ * x) := by
      simp only [map_mul, Algebra.smul_def]
      ring
    have elast : (β v + g₁ - g₂) * (β b * x) =
        β (v * b) * x + β b * (g₁ * x) - β b * (g₂ * x) := by
      simp only [map_mul]
      ring
    rw [efirst, map_sub, map_sub, map_smul, hx (u * b)] at hfirst
    rw [elast, map_sub, map_add, hx (v * b)] at hlast
    have hthree : (3 : ℂ) • π (β b * (g₁ * x)) = 0 := by
      calc
        (3 : ℂ) • π (β b * (g₁ * x)) =
            (0 + π (β b * (g₁ * x)) - π (β b * (g₂ * x))) -
              (0 - (2 : ℂ) • π (β b * (g₁ * x)) - π (β b * (g₂ * x))) := by module
        _ = 0 := by rw [← hfirst, ← hlast, sub_self]
    have hz : π (β b * (g₁ * x)) = 0 :=
      (smul_eq_zero.mp hthree).resolve_left (by norm_num)
    refine ⟨hz, ?_⟩
    simpa only [hz, add_zero, zero_sub, eq_neg_iff_add_eq_zero, zero_add] using hlast
  exact ⟨fun b => (hpair b).1, fun b => (hpair b).2⟩

/-- Algebra elements preserving a subspace under multiplication form a subalgebra. -/
def multiplicationPreservingSubalgebra (S : Submodule ℂ R) : Subalgebra ℂ R where
  carrier := {p | ∀ x ∈ S, p * x ∈ S}
  zero_mem' := by intro x hx; simp
  one_mem' := by intro x hx; simpa using hx
  add_mem' := by intro p q hp hq x hx; simpa [add_mul] using S.add_mem (hp x hx) (hq x hx)
  mul_mem' := by intro p q hp hq x hx; simpa [mul_assoc] using hp (q * x) (hq x hx)
  algebraMap_mem' := by intro z x hx; simpa [Algebra.smul_def] using S.smul_mem z hx

/-- Power-sum degree induction propagates relative relations through arbitrary multipliers. -/
theorem twoCartan_saturatedKernel_mul (β : B →ₐ[ℂ] R) (π : R →ₗ[ℂ] V)
    (u v : ι → B) (g₁ g₂ : ι → R) (h₁ h₂ : ι → Module.End ℂ V)
    (hc₁ : ∀ i x, h₁ i (π x) = π ((β (u i) - (2 : ℂ) • g₁ i - g₂ i) * x))
    (hc₂ : ∀ i x, h₂ i (π x) = π ((β (v i) + g₁ i - g₂ i) * x))
    (hgen : Algebra.adjoin ℂ (Set.range β ∪ Set.range g₁ ∪ Set.range g₂) = ⊤)
    {x : R} (hx : x ∈ baseSaturatedEvaluationKernel β π) (p : R) :
    p * x ∈ baseSaturatedEvaluationKernel β π := by
  have hle : Algebra.adjoin ℂ (Set.range β ∪ Set.range g₁ ∪ Set.range g₂) ≤
      multiplicationPreservingSubalgebra (baseSaturatedEvaluationKernel β π) := by
    apply Algebra.adjoin_le
    rintro z ((⟨b, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) y hy
    · exact baseSaturatedEvaluationKernel_base_mul β π hy b
    · exact (twoCartan_saturatedKernel_generators β π (u i) (v i) (g₁ i) (g₂ i)
        (h₁ i) (h₂ i) (hc₁ i) (hc₂ i) hy).1
    · exact (twoCartan_saturatedKernel_generators β π (u i) (v i) (g₁ i) (g₂ i)
        (h₁ i) (h₂ i) (hc₁ i) (hc₂ i) hy).2
  rw [hgen] at hle
  exact hle (show p ∈ (⊤ : Subalgebra ℂ R) from trivial) x hx

/-- Relations valid at every base vector generate an ideal contained in the evaluation kernel. -/
theorem twoCartan_relationIdeal_le_kernel (β : B →ₐ[ℂ] R) (π : R →ₗ[ℂ] V)
    (u v : ι → B) (g₁ g₂ : ι → R) (h₁ h₂ : ι → Module.End ℂ V)
    (hc₁ : ∀ i x, h₁ i (π x) = π ((β (u i) - (2 : ℂ) • g₁ i - g₂ i) * x))
    (hc₂ : ∀ i x, h₂ i (π x) = π ((β (v i) + g₁ i - g₂ i) * x))
    (hgen : Algebra.adjoin ℂ (Set.range β ∪ Set.range g₁ ∪ Set.range g₂) = ⊤)
    (relations : Set R) (hrel : ∀ x ∈ relations, ∀ b, π (β b * x) = 0) :
    (Ideal.span relations).restrictScalars ℂ ≤ LinearMap.ker π := by
  let I : Ideal R :=
    { carrier := baseSaturatedEvaluationKernel β π
      zero_mem' := (baseSaturatedEvaluationKernel β π).zero_mem
      add_mem' := (baseSaturatedEvaluationKernel β π).add_mem
      smul_mem' := fun p x hx =>
        twoCartan_saturatedKernel_mul β π u v g₁ g₂ h₁ h₂ hc₁ hc₂ hgen hx p }
  have hle : Ideal.span relations ≤ I := Ideal.span_le.mpr hrel
  intro x hx
  have he := hle hx (1 : B)
  simpa only [map_one, one_mul] using he

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.baseSaturatedEvaluationKernel_base_mul
#print axioms VOA.DeligneAudit.SL4T.twoCartan_saturatedKernel_generators
#print axioms VOA.DeligneAudit.SL4T.twoCartan_saturatedKernel_mul
#print axioms VOA.DeligneAudit.SL4T.twoCartan_relationIdeal_le_kernel
