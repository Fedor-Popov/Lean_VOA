import VOA.DeligneAudit.SL4TAlphabetPeel

/-! # Surjective Thom maps without any assertion about annihilator equality -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]

/-- Multiplication followed by a quotient map, with codomain its principal ideal. -/
def principalMul (π : A →ₐ[ℂ] B) (t : A) : A →ₗ[ℂ] Ideal.span {π t} :=
  ((LinearMap.mulLeft ℂ (π t)).comp π.toLinearMap).codRestrict
    ((Ideal.span {π t}).restrictScalars ℂ)
    (fun x => Ideal.mem_span_singleton.mpr ⟨π x, rfl⟩)

/-- Only containment in the annihilator is required to descend multiplication. -/
def principalThom (π : A →ₐ[ℂ] B) (t : A) (J : Ideal A)
    (hJ : ∀ x ∈ J, π (t * x) = 0) : (A ⧸ J) →ₗ[ℂ] Ideal.span {π t} :=
  (J.restrictScalars ℂ).liftQ (principalMul π t) (by
    intro x hx
    apply Subtype.ext
    change π t * π x = 0
    rw [← map_mul]
    exact hJ x hx)

theorem principalThom_mk (π : A →ₐ[ℂ] B) (t : A) (J : Ideal A)
    (hJ : ∀ x ∈ J, π (t * x) = 0) (x : A) :
    (principalThom π t J hJ (Ideal.Quotient.mk J x) : B) = π t * π x := rfl

theorem principalThom_surjective (π : A →ₐ[ℂ] B) (hπ : Function.Surjective π)
    (t : A) (J : Ideal A) (hJ : ∀ x ∈ J, π (t * x) = 0) :
    Function.Surjective (principalThom π t J hJ) := by
  rintro ⟨x, hx⟩
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨z, rfl⟩ := hπ y
  exact ⟨Ideal.Quotient.mk J z, Subtype.ext hy.symm⟩

theorem thom_kills_span_sup (π : A →ₐ[ℂ] B) (t p q : A)
    (hp : π (t * p) = 0) (hq : π (t * q) = 0) :
    ∀ x ∈ Ideal.span {p} ⊔ Ideal.span {q}, π (t * x) = 0 := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp hy
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hz
  have hu0 : π (t * (p * u)) = 0 := by
    rw [← mul_assoc, map_mul, hp, zero_mul]
  have hv0 : π (t * (q * v)) = 0 := by
    rw [← mul_assoc, map_mul, hq, zero_mul]
  rw [hu, hv, mul_add, map_add, hu0, hv0, add_zero]

/-- The source quotient acts on the Thom image through any representative. -/
theorem principalThom_mul_mk (π : A →ₐ[ℂ] B) (t : A) (J : Ideal A)
    (hJ : ∀ x ∈ J, π (t * x) = 0) (r : A) (x : A ⧸ J) :
    (principalThom π t J hJ (Ideal.Quotient.mk J r * x) : B) =
      π r * (principalThom π t J hJ x : B) := by
  induction x using Quotient.inductionOn' with
  | h x =>
      change (principalThom π t J hJ (Ideal.Quotient.mk J (r * x)) : B) =
        π r * (principalThom π t J hJ (Ideal.Quotient.mk J x) : B)
      rw [principalThom_mk, principalThom_mk, map_mul]
      ring

/-- Images of source ideals under a Thom map are ideals of the target ring. -/
def principalThomIdeal (π : A →ₐ[ℂ] B) (hπ : Function.Surjective π)
    (t : A) (J : Ideal A) (hJ : ∀ x ∈ J, π (t * x) = 0)
    (K : Ideal (A ⧸ J)) : Ideal B where
  carrier := {y | ∃ x ∈ K, (principalThom π t J hJ x : B) = y}
  zero_mem' := ⟨0, K.zero_mem, by simp⟩
  add_mem' := by
    rintro y z ⟨x, hx, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨x + w, K.add_mem hx hw, by simp⟩
  smul_mem' := by
    rintro c y ⟨x, hx, rfl⟩
    obtain ⟨r, rfl⟩ := hπ c
    exact ⟨Ideal.Quotient.mk J r * x, K.mul_mem_left _ hx,
      principalThom_mul_mk π t J hJ r x⟩

theorem principalThomIdeal_mono (π : A →ₐ[ℂ] B) (hπ : Function.Surjective π)
    (t : A) (J : Ideal A) (hJ : ∀ x ∈ J, π (t * x) = 0)
    {K L : Ideal (A ⧸ J)} (hKL : K ≤ L) :
    principalThomIdeal π hπ t J hJ K ≤ principalThomIdeal π hπ t J hJ L := by
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, hKL hx, rfl⟩

theorem principalThomIdeal_top (π : A →ₐ[ℂ] B) (hπ : Function.Surjective π)
    (t : A) (J : Ideal A) (hJ : ∀ x ∈ J, π (t * x) = 0) :
    principalThomIdeal π hπ t J hJ ⊤ = Ideal.span {π t} := by
  apply le_antisymm
  · rintro y ⟨x, _, rfl⟩
    exact (principalThom π t J hJ x).property
  · intro y hy
    obtain ⟨x, hx⟩ := principalThom_surjective π hπ t J hJ ⟨y, hy⟩
    exact ⟨x, trivial, congrArg Subtype.val hx⟩

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.principalThom_surjective
#print axioms VOA.DeligneAudit.SL4T.thom_kills_span_sup
#print axioms VOA.DeligneAudit.SL4T.principalThom_mul_mk
#print axioms VOA.DeligneAudit.SL4T.principalThomIdeal
#print axioms VOA.DeligneAudit.SL4T.principalThomIdeal_top
