import VOA.Classification.COne.PlusSplitSessionFourteen

/-! Zero-mode separation with the commutator defect retained explicitly.
These sufficient tests apply to all quotient relations in the full mode algebra.
Distinct bottom characters alone do not supply their commutator hypotheses. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusSplitting
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- A relation value vanishes if its actual eigenvalue differs from the
eigenvalue transported through the relation, including the commutator shift. -/
theorem relation_zero_of_eigenvalue_separation (Z R : Module.End ℂ M)
    (x : M) (a b d : ℂ) (hx : Z x = a • x)
    (hc : Z (R x) - R (Z x) = d • R x)
    (hr : Z (R x) = b • R x) (hne : b ≠ a + d) : R x = 0 := by
  have he : (b - a - d) • R x = 0 := by
    rw [hx, map_smul, hr] at hc
    rw [sub_smul, sub_smul]
    exact sub_eq_zero.mpr hc
  exact (smul_eq_zero.mp he).resolve_left (by intro h; apply hne; linear_combination h)

/-- Test each quotient relation using a genuine homogeneous zero mode.
The separator, its eigenvalues, and the commutator shift can depend on the
relation. A single chosen lift must satisfy all tests simultaneously. -/
def ZeroModeSeparatesRelations (A : WeakModule W M)
    (P : Submodule (modeAlg A) M) (x : M) : Prop :=
  ∀ r : quotientRelations A P x,
    ∃ (a : V) (w : ℤ) (_ : a ∈ W.grading w) (α β δ : ℂ),
      mode (A.YM a) (w - 1) x = α • x ∧
      mode (A.YM a) (w - 1) (r.val • x) -
        r.val • (mode (A.YM a) (w - 1) x) = δ • (r.val • x) ∧
      mode (A.YM a) (w - 1) (r.val • x) = β • (r.val • x) ∧
      β ≠ α + δ

theorem cyclicRelationObstruction_zero_of_zeroMode_separation
    (A : WeakModule W M) (P : Submodule (modeAlg A) M) (x : M)
    (hs : ZeroModeSeparatesRelations A P x) : cyclicRelationObstruction A P x = 0 := by
  apply (liftObstruction_eq_zero_iff _ _ _).mpr
  refine ⟨0, P.zero_mem, ?_⟩
  ext r
  obtain ⟨a, w, _, α, β, δ, hx, hc, hr, hn⟩ := hs r
  simpa using relation_zero_of_eigenvalue_separation
    (mode (A.YM a) (w - 1)) r.val.val x α β δ hx hc hr hn

/-- Full mode-algebra splitting from zero-mode separation of all relation
values. This works in either orientation and uses no contragredient. -/
theorem complement_of_zeroMode_separation (A : WeakModule W M)
    (P : Submodule (modeAlg A) M) (hP : P ⋖ ⊤) (x : M) (hx : x ∉ P)
    (hs : ZeroModeSeparatesRelations A P x) :
    ∃ Q : Submodule (modeAlg A) M, IsCompl P Q :=
  complement_of_cyclicRelationObstruction A P hP x hx
    (cyclicRelationObstruction_zero_of_zeroMode_separation A P x hs)

end VOA.Classification.COne.PlusSplitting

namespace VOA.Classification.COne.PlusResonantPairs
open PlusSplitting PlusCharacterTable

/-- Explicit sufficient hypotheses for the original numerical pair statement.
The relation tests are obligations, not consequences of the character table. -/
theorem pairSplitting_of_zeroMode_separation (m : ℕ) (hm : 1 ≤ m) (i j : Label m)
    (hs : ∀ {M : Type} [AddCommGroup M] [Module ℂ M]
      (A : WeakModule (V2mPlus m hm) M) (P : Submodule (modeAlg A) M),
      IsAtom P → P ⋖ ⊤ →
      FactorBottom A ⊥ P (weight m i : ℂ) →
      FactorBottom A P ⊤ (weight m j : ℂ) →
      ∃ x : M, x ∉ P ∧ ZeroModeSeparatesRelations A P x) :
    PairSplitting m hm i j := by
  intro M _ _ A P hP hmax hi hj
  obtain ⟨x, hx, hsep⟩ := hs A P hP hmax hi hj
  exact complement_of_zeroMode_separation A P hmax x hx hsep

end VOA.Classification.COne.PlusResonantPairs
