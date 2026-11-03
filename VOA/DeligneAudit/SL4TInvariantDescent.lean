import VOA.DeligneAudit.SL4TFullFlagStratumRank

/-! Averaging and exact descent of finite-group invariants over the complex numbers. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {G A D : Type*} [Group G] [Fintype G]
variable [CommRing A] [Algebra ℂ A] [CommRing D] [Algebra ℂ D]

/-- The fixed coefficient algebra of a finite group of algebra automorphisms. -/
def finiteActionFixedSubalgebra (ρ : G →* (A ≃ₐ[ℂ] A)) : Subalgebra ℂ A where
  carrier := {a | ∀ g, ρ g a = a}
  zero_mem' := by intro g; exact map_zero _
  one_mem' := by intro g; exact map_one _
  add_mem' := by intro a b ha hb g; rw [map_add, ha g, hb g]
  mul_mem' := by intro a b ha hb g; rw [map_mul, ha g, hb g]
  algebraMap_mem' := by intro c g; exact (ρ g).commutes c

/-- Averaging over a finite group, as a complex-linear endomorphism. -/
def finiteActionAverage (ρ : G →* (A ≃ₐ[ℂ] A)) : A →ₗ[ℂ] A :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g, (ρ g).toLinearMap

/-- The average of any coefficient is fixed by every group element. -/
theorem finiteActionAverage_fixed (ρ : G →* (A ≃ₐ[ℂ] A)) (a : A) :
    finiteActionAverage ρ a ∈ finiteActionFixedSubalgebra ρ := by
  intro g
  simp only [finiteActionAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    AlgEquiv.toLinearMap_apply, map_smul, map_sum]
  congr 1
  have he (h : G) : ρ g (ρ h a) = ρ (g * h) a := by rw [map_mul]; rfl
  simp only [he]
  exact Function.Bijective.sum_comp (Group.mulLeft_bijective g) (fun h => ρ h a)

/-- Averaging fixes every invariant coefficient. -/
theorem finiteActionAverage_id (ρ : G →* (A ≃ₐ[ℂ] A)) (a : A)
    (ha : a ∈ finiteActionFixedSubalgebra ρ) : finiteActionAverage ρ a = a := by
  change ∀ g, ρ g a = a at ha
  have hn : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [finiteActionAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    AlgEquiv.toLinearMap_apply, ha, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn, one_smul]

/-- The averaging projection is linear over the fixed coefficient algebra. -/
theorem finiteActionAverage_mul_fixed (ρ : G →* (A ≃ₐ[ℂ] A)) (a b : A)
    (ha : a ∈ finiteActionFixedSubalgebra ρ) :
    finiteActionAverage ρ (a * b) = a * finiteActionAverage ρ b := by
  change ∀ g, ρ g a = a at ha
  simp only [finiteActionAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    AlgEquiv.toLinearMap_apply, map_mul, ha, Finset.mul_sum, mul_smul_comm]

/-- Equivariant coefficient maps commute with finite-group averaging. -/
theorem finiteActionAverage_map (ρ : G →* (A ≃ₐ[ℂ] A))
    (σ : G →* (D ≃ₐ[ℂ] D)) (f : A →ₐ[ℂ] D)
    (hf : ∀ g a, f (ρ g a) = σ g (f a)) (a : A) :
    f (finiteActionAverage ρ a) = finiteActionAverage σ (f a) := by
  simp only [finiteActionAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    AlgEquiv.toLinearMap_apply, map_smul, map_sum, hf]

/-- An equivariant coefficient map restricts to the fixed algebras. -/
def finiteActionFixedMap (ρ : G →* (A ≃ₐ[ℂ] A))
    (σ : G →* (D ≃ₐ[ℂ] D)) (f : A →ₐ[ℂ] D)
    (hf : ∀ g a, f (ρ g a) = σ g (f a)) :
    finiteActionFixedSubalgebra ρ →ₐ[ℂ] finiteActionFixedSubalgebra σ where
  toFun a := ⟨f a.val, fun g => by rw [← hf, a.property g]⟩
  map_zero' := Subtype.ext (map_zero f)
  map_one' := Subtype.ext (map_one f)
  map_add' a b := Subtype.ext (map_add f a.val b.val)
  map_mul' a b := Subtype.ext (map_mul f a.val b.val)
  commutes' c := Subtype.ext (f.commutes c)

/-- Surjective equivariant maps remain surjective on finite-group invariant algebras. -/
theorem finiteActionFixedMap_surjective (ρ : G →* (A ≃ₐ[ℂ] A))
    (σ : G →* (D ≃ₐ[ℂ] D)) (f : A →ₐ[ℂ] D)
    (hf : ∀ g a, f (ρ g a) = σ g (f a)) (hs : Function.Surjective f) :
    Function.Surjective (finiteActionFixedMap ρ σ f hf) := by
  intro b
  obtain ⟨a, ha⟩ := hs b.val
  refine ⟨⟨finiteActionAverage ρ a, finiteActionAverage_fixed ρ a⟩, ?_⟩
  apply Subtype.ext
  change f (finiteActionAverage ρ a) = b.val
  rw [finiteActionAverage_map ρ σ f hf, ha, finiteActionAverage_id σ b.val b.property]

/-- The kernel on fixed coefficients is exactly the contraction of the original kernel. -/
theorem finiteActionFixedMap_kernel (ρ : G →* (A ≃ₐ[ℂ] A))
    (σ : G →* (D ≃ₐ[ℂ] D)) (f : A →ₐ[ℂ] D)
    (hf : ∀ g a, f (ρ g a) = σ g (f a)) :
    RingHom.ker (finiteActionFixedMap ρ σ f hf).toRingHom =
      (RingHom.ker f.toRingHom).comap (finiteActionFixedSubalgebra ρ).val.toRingHom := by
  ext a
  change (⟨f a.val, _⟩ : finiteActionFixedSubalgebra σ) = 0 ↔ f a.val = 0
  exact Subtype.ext_iff

/-- The quotient of fixed coefficients by the contracted kernel is the fixed target algebra. -/
def finiteActionFixedQuotientEquiv (ρ : G →* (A ≃ₐ[ℂ] A))
    (σ : G →* (D ≃ₐ[ℂ] D)) (f : A →ₐ[ℂ] D)
    (hf : ∀ g a, f (ρ g a) = σ g (f a)) (hs : Function.Surjective f) :
    (finiteActionFixedSubalgebra ρ ⧸
      RingHom.ker (finiteActionFixedMap ρ σ f hf).toRingHom) ≃ₐ[ℂ]
        finiteActionFixedSubalgebra σ :=
  Ideal.quotientKerAlgEquivOfSurjective (finiteActionFixedMap_surjective ρ σ f hf hs)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.finiteActionFixedSubalgebra
#print axioms VOA.DeligneAudit.SL4T.finiteActionAverage
#print axioms VOA.DeligneAudit.SL4T.finiteActionAverage_fixed
#print axioms VOA.DeligneAudit.SL4T.finiteActionAverage_id
#print axioms VOA.DeligneAudit.SL4T.finiteActionAverage_mul_fixed
#print axioms VOA.DeligneAudit.SL4T.finiteActionAverage_map
#print axioms VOA.DeligneAudit.SL4T.finiteActionFixedMap
#print axioms VOA.DeligneAudit.SL4T.finiteActionFixedMap_surjective
#print axioms VOA.DeligneAudit.SL4T.finiteActionFixedMap_kernel
#print axioms VOA.DeligneAudit.SL4T.finiteActionFixedQuotientEquiv
