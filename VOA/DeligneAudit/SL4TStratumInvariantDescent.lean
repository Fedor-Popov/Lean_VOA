import VOA.DeligneAudit.SL4TStratumInvariantCount
import VOA.DeligneAudit.SL4TInvariantIdealContraction

/-! Reynolds descent for the polynomial fixed algebra of a determinantal full-flag stratum. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {G A : Type*} [Group G] [CommRing A] [Algebra ℂ A]

/-- Stability under a group implies equality with every translate of the ideal. -/
theorem stableIdeal_map_eq (ρ : G →* (A ≃ₐ[ℂ] A)) (I : Ideal A)
    (hI : ∀ g x, x ∈ I → ρ g x ∈ I) (g : G) :
    I = I.map (ρ g).toRingHom := by
  apply le_antisymm
  · intro x hx
    have h := Ideal.mem_map_of_mem (ρ g).toRingHom (hI g⁻¹ x hx)
    have he : ρ g (ρ g⁻¹ x) = x := by
      rw [map_inv]
      exact (ρ g).apply_symm_apply x
    change ρ g (ρ g⁻¹ x) ∈ I.map (ρ g).toRingHom at h
    rwa [he] at h
  · exact Ideal.map_le_iff_le_comap.mpr (fun x hx => hI g x hx)

/-- An action by algebra automorphisms descends to a stable ideal quotient. -/
def stableIdealQuotientAlgebraAction (ρ : G →* (A ≃ₐ[ℂ] A)) (I : Ideal A)
    (hI : ∀ g x, x ∈ I → ρ g x ∈ I) : G →* ((A ⧸ I) ≃ₐ[ℂ] (A ⧸ I)) where
  toFun g := Ideal.quotientEquivAlg I I (ρ g) (stableIdeal_map_eq ρ I hI g)
  map_one' := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | _ p => simp [map_one]
  map_mul' g h := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | _ p => simp [map_mul]

/-- The quotient map intertwines the original and descended algebra actions. -/
theorem stableIdealQuotientAlgebraAction_mk (ρ : G →* (A ≃ₐ[ℂ] A)) (I : Ideal A)
    (hI : ∀ g x, x ∈ I → ρ g x ∈ I) (g : G) (x : A) :
    stableIdealQuotientAlgebraAction ρ I hI g (Ideal.Quotient.mkₐ ℂ I x) =
      Ideal.Quotient.mkₐ ℂ I (ρ g x) := rfl

/-- Reynolds descent identifies fixed polynomials modulo the contracted ideal with fixed classes. -/
def fixedPolynomialQuotientEquiv [Fintype G] (ρ : G →* (A ≃ₐ[ℂ] A)) (I : Ideal A)
    (hI : ∀ g x, x ∈ I → ρ g x ∈ I) :
    (finiteActionFixedSubalgebra ρ ⧸
      I.comap (finiteActionFixedSubalgebra ρ).val.toRingHom) ≃ₐ[ℂ]
        finiteActionFixedSubalgebra (stableIdealQuotientAlgebraAction ρ I hI) := by
  let τ := stableIdealQuotientAlgebraAction ρ I hI
  let f := Ideal.Quotient.mkₐ ℂ I
  have hf : ∀ g x, f (ρ g x) = τ g (f x) := fun _ _ => rfl
  have he : RingHom.ker (finiteActionFixedMap ρ τ f hf).toRingHom =
      I.comap (finiteActionFixedSubalgebra ρ).val.toRingHom := by
    rw [finiteActionFixedMap_kernel]
    congr 1
    exact Ideal.mk_ker
  exact (Ideal.quotientEquivAlgOfEq ℂ he.symm).trans
    (finiteActionFixedQuotientEquiv ρ τ f hf (Ideal.Quotient.mkₐ_surjective ℂ I))

/-- Permuting variables defines an action on the polynomial algebra by algebra automorphisms. -/
def polynomialPositionAlgebraAction {σ : Type*} (η : G →* Equiv.Perm σ) :
    G →* (MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial σ ℂ) where
  toFun g := MvPolynomial.renameEquiv ℂ (η g)
  map_one' := by ext p : 1; simp
  map_mul' g h := by
    ext p : 1
    change MvPolynomial.rename (η (g * h)) p =
      MvPolynomial.rename (η g) (MvPolynomial.rename (η h) p)
    rw [MvPolynomial.rename_rename, map_mul]
    rfl

/-- The concrete stratum ideal is stable under the polynomial algebra action. -/
theorem fullFlagStratumIdeal_algebra_stable (B k j : ℕ) (Y : Finset (Fin B))
    (hk : 2 * k ≤ B) (η : G →* Equiv.Perm (Fin B))
    (hY : ∀ g, Y.map (η g).toEmbedding = Y) :
    ∀ g x, x ∈ fullFlagTruncationIdeal B (B - k) ⊔
      remainderTopIdeal (fullFlagSubalphabet Y) (B - k) j →
        polynomialPositionAlgebraAction η g x ∈ fullFlagTruncationIdeal B (B - k) ⊔
          remainderTopIdeal (fullFlagSubalphabet Y) (B - k) j := by
  intro g x hx
  exact fullFlagStratumIdeal_stable B k j Y hk η hY g hx

/-- The algebra and linear quotient actions have the same fixed vectors. -/
def fullFlagStratumFixedLinearEquiv (B k j : ℕ) (Y : Finset (Fin B))
    (hk : 2 * k ≤ B) (η : G →* Equiv.Perm (Fin B))
    (hY : ∀ g, Y.map (η g).toEmbedding = Y) :
    finiteActionFixedSubalgebra
      (stableIdealQuotientAlgebraAction (polynomialPositionAlgebraAction η)
        (fullFlagTruncationIdeal B (B - k) ⊔
          remainderTopIdeal (fullFlagSubalphabet Y) (B - k) j)
        (fullFlagStratumIdeal_algebra_stable B k j Y hk η hY)) ≃ₗ[ℂ]
      (fullFlagStratumPositionRepresentation B k j Y hk η hY).invariants := by
  let τ := stableIdealQuotientAlgebraAction (polynomialPositionAlgebraAction η)
    (fullFlagTruncationIdeal B (B - k) ⊔
      remainderTopIdeal (fullFlagSubalphabet Y) (B - k) j)
    (fullFlagStratumIdeal_algebra_stable B k j Y hk η hY)
  let ρ := fullFlagStratumPositionRepresentation B k j Y hk η hY
  have he (g : G) (v : FullFlagStratumRing B (B - k) j Y) : τ g v = ρ g v := by
    induction v using Submodule.Quotient.induction_on with
    | _ p => rfl
  exact
    { toFun := fun v => ⟨v.val, fun g => (he g v.val).symm.trans (v.property g)⟩
      invFun := fun v => ⟨v.val, fun g => (he g v.val).trans (v.property g)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The quotient of invariant polynomials by the contracted stratum ideal counts the orbits. -/
theorem fullFlagStratum_contracted_finrank [Fintype G] (B k j : ℕ)
    (Y : Finset (Fin B)) (hk : 2 * k ≤ B) (η : G →* Equiv.Perm (Fin B))
    (hY : ∀ g, Y.map (η g).toEmbedding = Y) :
    letI := fullFlagStratumPositionAction B k j Y η hY
    let S := finiteActionFixedSubalgebra (polynomialPositionAlgebraAction η)
    let I := (fullFlagTruncationIdeal B (B - k) ⊔
      remainderTopIdeal (fullFlagSubalphabet Y) (B - k) j).comap S.val.toRingHom
    FiniteDimensional ℂ (S ⧸ I) ∧ Module.finrank ℂ (S ⧸ I) =
      Nat.card (MulAction.orbitRel.Quotient G (FullFlagStratumConfiguration B k j Y)) := by
  letI := fullFlagStratumPositionAction B k j Y η hY
  dsimp only
  let e := (fixedPolynomialQuotientEquiv (polynomialPositionAlgebraAction η)
    (fullFlagTruncationIdeal B (B - k) ⊔
      remainderTopIdeal (fullFlagSubalphabet Y) (B - k) j)
    (fullFlagStratumIdeal_algebra_stable B k j Y hk η hY)).toLinearEquiv.trans
      (fullFlagStratumFixedLinearEquiv B k j Y hk η hY)
  letI := fullFlagStratum_finite B (B - k) j Y
  refine ⟨Module.Finite.of_injective e.toLinearMap e.injective, ?_⟩
  rw [e.finrank_eq]
  exact fullFlagStratum_invariant_finrank B k j Y hk η hY

/-- The descended Young-invariant polynomial ring counts the attained colour configurations. -/
theorem colourStratum_contracted_finrank {C : Type*} [DecidableEq C]
    (B k j : ℕ) (hk : 2 * k ≤ B) (colour : Fin B → C) (selected : Finset C) :
    let Y := selectedColourPositions colour selected
    let S := finiteActionFixedSubalgebra
      (polynomialPositionAlgebraAction (positionColourSubgroup colour).subtype)
    let I := (fullFlagTruncationIdeal B (B - k) ⊔
      remainderTopIdeal (fullFlagSubalphabet Y) (B - k) j).comap S.val.toRingHom
    FiniteDimensional ℂ (S ⧸ I) ∧ Module.finrank ℂ (S ⧸ I) =
      Nat.card (Set.range (fun f : FullFlagStratumConfiguration B k j Y =>
        configurationColourMultiplicity colour f.val)) := by
  letI := colourStratumPositionAction B k j colour selected
  letI := Fintype.ofFinite (positionColourSubgroup colour)
  obtain ⟨hfinite, hdim⟩ := fullFlagStratum_contracted_finrank B k j _ hk
    (positionColourSubgroup colour).subtype
    (positionColourSubgroup_preserves_selected colour selected)
  exact ⟨hfinite, hdim.trans (Nat.card_congr (colourStratumOrbitEquiv B k j colour selected))⟩

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.stableIdeal_map_eq
#print axioms VOA.DeligneAudit.SL4T.stableIdealQuotientAlgebraAction
#print axioms VOA.DeligneAudit.SL4T.stableIdealQuotientAlgebraAction_mk
#print axioms VOA.DeligneAudit.SL4T.fixedPolynomialQuotientEquiv
#print axioms VOA.DeligneAudit.SL4T.polynomialPositionAlgebraAction
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumIdeal_algebra_stable
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumFixedLinearEquiv
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratum_contracted_finrank
#print axioms VOA.DeligneAudit.SL4T.colourStratum_contracted_finrank
