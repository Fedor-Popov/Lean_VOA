import VOA.DeligneAudit.SL4TInvariantDescent

/-! Contraction of ideals generated in a finite-group fixed coefficient algebra. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {G A : Type*} [Group G] [Fintype G] [CommRing A] [Algebra ℂ A]

/-- The averaging map with codomain restricted to fixed coefficients. -/
def finiteActionAverageToFixed (ρ : G →* (A ≃ₐ[ℂ] A)) :
    A →ₗ[ℂ] finiteActionFixedSubalgebra ρ :=
  (finiteActionAverage ρ).codRestrict (finiteActionFixedSubalgebra ρ).toSubmodule
    (finiteActionAverage_fixed ρ)

/-- An invariant factor can be pulled out of the fixed-valued averaging map. -/
theorem finiteActionAverageToFixed_mul (ρ : G →* (A ≃ₐ[ℂ] A))
    (a : finiteActionFixedSubalgebra ρ) (b : A) :
    finiteActionAverageToFixed ρ (b * a.val) = finiteActionAverageToFixed ρ b * a := by
  apply Subtype.ext
  change finiteActionAverage ρ (b * a.val) = finiteActionAverage ρ b * a.val
  rw [mul_comm b, finiteActionAverage_mul_fixed ρ a.val b a.property, mul_comm]

/-- Averaging takes an extended invariant ideal back into the original fixed-algebra ideal. -/
theorem finiteActionAverage_mem_ideal (ρ : G →* (A ≃ₐ[ℂ] A))
    (J : Ideal (finiteActionFixedSubalgebra ρ)) (x : A)
    (hx : x ∈ J.map (finiteActionFixedSubalgebra ρ).val.toRingHom) :
    finiteActionAverageToFixed ρ x ∈ J := by
  have hmul : ∀ b : A, finiteActionAverageToFixed ρ (b * x) ∈ J := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨a, ha, rfl⟩ := hy
        intro b
        change finiteActionAverageToFixed ρ (b * a.val) ∈ J
        rw [finiteActionAverageToFixed_mul]
        exact J.mul_mem_left _ ha
    | zero => intro b; simpa only [mul_zero, map_zero] using J.zero_mem
    | add x y hx hy ihx ihy =>
        intro b
        rw [mul_add, map_add]
        exact J.add_mem (ihx b) (ihy b)
    | smul a x hx ih =>
        intro b
        change finiteActionAverageToFixed ρ (b * (a * x)) ∈ J
        rw [← mul_assoc]
        exact ih (b * a)
  simpa only [one_mul] using hmul 1

/-- Extension to the whole coefficient algebra and contraction preserve invariant ideals. -/
theorem finiteActionIdeal_comap_map (ρ : G →* (A ≃ₐ[ℂ] A))
    (J : Ideal (finiteActionFixedSubalgebra ρ)) :
    (J.map (finiteActionFixedSubalgebra ρ).val.toRingHom).comap
      (finiteActionFixedSubalgebra ρ).val.toRingHom = J := by
  apply le_antisymm
  · intro a ha
    have h := finiteActionAverage_mem_ideal ρ J a.val ha
    have he : finiteActionAverageToFixed ρ a.val = a := by
      apply Subtype.ext
      exact finiteActionAverage_id ρ a.val a.property
    rwa [he] at h
  · exact Ideal.le_comap_map

/-- An invariant-generated ideal contracts to the same generators in the fixed algebra. -/
theorem finiteActionInvariantGenerators_contract (ρ : G →* (A ≃ₐ[ℂ] A))
    (S : Set (finiteActionFixedSubalgebra ρ)) :
    (Ideal.span ((finiteActionFixedSubalgebra ρ).val '' S)).comap
      (finiteActionFixedSubalgebra ρ).val.toRingHom = Ideal.span S := by
  rw [← Ideal.map_span]
  exact finiteActionIdeal_comap_map ρ (Ideal.span S)

/-- Averaging preserves every group-stable coefficient ideal. -/
theorem finiteActionAverage_mem_stableIdeal (ρ : G →* (A ≃ₐ[ℂ] A)) (I : Ideal A)
    (hI : ∀ g x, x ∈ I → ρ g x ∈ I) (x : A) (hx : x ∈ I) :
    finiteActionAverage ρ x ∈ I := by
  simp only [finiteActionAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    AlgEquiv.toLinearMap_apply]
  apply (I.restrictScalars ℂ).smul_mem
  exact I.sum_mem fun g _ => hI g x hx

/-- Adding invariant-generated stratum relations commutes with contraction to fixed coefficients. -/
theorem finiteActionIdeal_comap_sup_map (ρ : G →* (A ≃ₐ[ℂ] A)) (I : Ideal A)
    (hI : ∀ g x, x ∈ I → ρ g x ∈ I) (J : Ideal (finiteActionFixedSubalgebra ρ)) :
    (I ⊔ J.map (finiteActionFixedSubalgebra ρ).val.toRingHom).comap
      (finiteActionFixedSubalgebra ρ).val.toRingHom =
        I.comap (finiteActionFixedSubalgebra ρ).val.toRingHom ⊔ J := by
  apply le_antisymm
  · intro a ha
    obtain ⟨x, hx, y, hy, he⟩ := Submodule.mem_sup.mp ha
    apply Submodule.mem_sup.mpr
    refine ⟨finiteActionAverageToFixed ρ x,
      finiteActionAverage_mem_stableIdeal ρ I hI x hx,
      finiteActionAverageToFixed ρ y, finiteActionAverage_mem_ideal ρ J y hy, ?_⟩
    apply Subtype.ext
    change finiteActionAverage ρ x + finiteActionAverage ρ y = a.val
    rw [← map_add, he]
    exact finiteActionAverage_id ρ a.val a.property
  · apply sup_le
    · exact Ideal.comap_mono le_sup_left
    · exact (Ideal.le_comap_map).trans (Ideal.comap_mono le_sup_right)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.finiteActionAverageToFixed
#print axioms VOA.DeligneAudit.SL4T.finiteActionAverageToFixed_mul
#print axioms VOA.DeligneAudit.SL4T.finiteActionAverage_mem_ideal
#print axioms VOA.DeligneAudit.SL4T.finiteActionIdeal_comap_map
#print axioms VOA.DeligneAudit.SL4T.finiteActionInvariantGenerators_contract
#print axioms VOA.DeligneAudit.SL4T.finiteActionAverage_mem_stableIdeal
#print axioms VOA.DeligneAudit.SL4T.finiteActionIdeal_comap_sup_map
