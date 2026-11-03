import VOA.Huang.DLNCentralFinite

/-!
# The remaining finite central congruence problem

The propositions below are explicit, unproved arithmetic obligations, not
instances or axioms. Their equivalence with the original target uses the
unconditional finiteness theorem in `DLNCentralFinite`.

Reference: Dong--Lin--Ng, arXiv:1201.6644, Theorem 2.1 (including vanishing
of inflation), Lemma 2.2, and Theorem 2.3. Multiplier orders alone do not
supply these propositions.
-/

namespace VOA.Huang.DLNLifting

open VOA.Huang.DLN CongruenceSubgroup

attribute [local instance] Gamma_normal

/-- The natural projection from the relative central quotient onto the modular quotient. -/
def centralProjection (N : ℕ) : CentralQuotient N →* SL2Z ⧸ Gamma N :=
  QuotientGroup.lift (relativeCommutator N) (QuotientGroup.mk' (Gamma N))
    (by simpa only [QuotientGroup.ker_mk'] using relativeCommutator_le_gamma N)

theorem centralProjection_surjective (N : ℕ) :
    Function.Surjective (centralProjection N) :=
  QuotientGroup.lift_surjective_of_surjective _ _ QuotientGroup.mk_surjective _

/-- Exactness: the projection kernel is precisely the image of the principal subgroup. -/
theorem centralProjection_ker (N : ℕ) :
    (centralProjection N).ker =
      (Gamma N).map (QuotientGroup.mk' (relativeCommutator N)) := by
  rw [centralProjection, QuotientGroup.ker_lift, QuotientGroup.ker_mk']

/-- Thus this is a central extension, and at positive level its total group is finite. -/
theorem centralProjection_ker_le_center (N : ℕ) :
    (centralProjection N).ker ≤ Subgroup.center (CentralQuotient N) := by
  rw [centralProjection_ker]
  exact gamma_image_le_center N

/-- Finite normal central extensions of principal modular quotients have congruence
kernels. This true arithmetic statement is left as an explicit open obligation. -/
def CentralCongruenceSL2 : Prop :=
  ∀ N : ℕ, 0 < N → ∀ K : Subgroup SL2Z, K.Normal → K.FiniteIndex →
    relativeCommutator N ≤ K → K ≤ Gamma N →
      ∃ L : ℕ, 0 < L ∧ Gamma L ≤ K

/-- It suffices to settle finite quotients, and only their derived-group obstruction.
This true finite-group statement remains unproved here. -/
def FiniteCentralDerivedCongruenceSL2 : Prop :=
  ∀ (E : Type) [Group E] [Finite E] (f : SL2Z →* E), Function.Surjective f →
    ∀ N : ℕ, 0 < N → (Gamma N).map f ≤ Subgroup.center E →
      ∃ L : ℕ, 0 < L ∧ Gamma L ⊓ commutator SL2Z ≤ f.ker

/-- The finite-index normal-subgroup formulation is exactly the original target. -/
theorem relativeCommutatorCongruenceSome_iff_centralCongruenceSL2 :
    RelativeCommutatorCongruenceSome ↔ CentralCongruenceSL2 := by
  constructor
  · intro h N hN K _ _ hK _
    obtain ⟨L, hL, hΓ⟩ := h N hN
    exact ⟨L, hL, hΓ.trans hK⟩
  · intro h N hN
    exact h N hN (relativeCommutator N) inferInstance
      (relativeCommutator_finiteIndex N hN) le_rfl (relativeCommutator_le_gamma N)

/-- Exact reduction to the finite derived-group obstruction, using level 12 to
remove characters and Schur's theorem to supply finiteness. -/
theorem relativeCommutatorCongruenceSome_iff_finiteCentralDerived :
    RelativeCommutatorCongruenceSome ↔ FiniteCentralDerivedCongruenceSL2 := by
  constructor
  · intro h E _ _ f hf N hN hc
    obtain ⟨L, hL, hΓ⟩ := h N hN
    exact ⟨L, hL, inf_le_left.trans
      (hΓ.trans ((gamma_image_le_center_iff f hf N).mp hc))⟩
  · intro h
    apply relativeCommutatorCongruenceSome_iff_derived.mpr
    intro N hN
    letI := centralQuotient_finite N hN
    obtain ⟨L, hL, hΓ⟩ := h (CentralQuotient N)
      (QuotientGroup.mk' (relativeCommutator N)) QuotientGroup.mk_surjective
      N hN (gamma_image_le_center N)
    exact ⟨L, hL, by simpa only [QuotientGroup.ker_mk'] using hΓ⟩

/-- The finite-group obstruction, if supplied, suffices for genuine Zhu congruence. -/
theorem zhuCongruence_of_finiteCentralDerived
    (h : FiniteCentralDerivedCongruenceSL2)
    (hP : DLNBridge.ZhuProjectiveCongruenceInput.{u}) :
    DLNBridge.ZhuCongruenceInput.{u} :=
  zhuCongruence_of_relativeCommutatorSome
    (relativeCommutatorCongruenceSome_iff_finiteCentralDerived.mpr h) hP

end VOA.Huang.DLNLifting
