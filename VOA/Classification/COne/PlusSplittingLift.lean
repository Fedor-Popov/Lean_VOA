import VOA.Classification.COne.PlusRationalReduction
import VOA.Classification.COne.PlusSplittingWeights

/-!
# Proper lifts and bottom detection for two-step splitting

All submodules here are arbitrary ring submodules, hence arbitrary mode-stable
subspaces in the VOA application. No admissible-level grading is assumed.

The exact remaining criterion is a proper cyclic lift of an upper-factor
generator. A lower-weight lift does not automatically satisfy properness.
`relativeComplement_of_generated_bottom_separation` isolates the needed
generation-versus-bottom assertion in equal-weight arguments.

Status: the requested `V2mPlusTwoStepSplittingFactGe2` is NOT proved here.
Its equivalence to `V2mPlusProperCyclicLiftFactGe2` is proved. The latter remains
open. The weight results in the imported file concern ordinary modules only.
To apply them to arbitrary weak subquotients requires further structure.

Source: Abe, https://arxiv.org/html/math/0311210, §§5--7, especially
Propositions 7.2--7.4 and Lemma 7.5. Equal-weight splitting needs semisimple
Zhu tops and control of the bottom of the generated lift. The remaining
integrally resonant pairs need the vacuum/sign or fusion arguments. The
certified relations used for a numerical spectrum alone do not prove these.
-/

namespace VOA.Classification.COne.PlusSplitting

set_option maxSynthPendingDepth 3

open PlusRational

/-- In a two-step interval, a proper intermediate element not below the middle
element is automatically a relative complement. -/
theorem relativeComplement_of_proper_lift
    {L : Type*} [Lattice L] {a b c d : L}
    (hab : a ⋖ b) (hbc : b ⋖ c)
    (had : a ≤ d) (hdc : d ≤ c) (hdb : ¬d ≤ b) (hdne : d ≠ c) :
    b ⊓ d = a ∧ b ⊔ d = c := by
  have hsup : b ⊔ d = c := by
    rcases hbc.wcovBy.eq_or_eq le_sup_left (sup_le hbc.le hdc) with h | h
    · exact (hdb (h ▸ le_sup_right)).elim
    · exact h
  refine ⟨?_, hsup⟩
  rcases hab.wcovBy.eq_or_eq (le_inf hab.le had) inf_le_left with h | h
  · exact h
  · have hbd : b ≤ d := h ▸ inf_le_right
    exact (hdne ((sup_eq_right.mpr hbd).symm.trans hsup)).elim

section Ring

variable {R X : Type*} [Ring R] [AddCommGroup X] [Module R X]

/-- A lift of an upper-factor generator that does not generate the whole
extension over the base. This is a substantial condition, not automatic from
its lowest weight. -/
def ProperCyclicLift (a b c : Submodule R X) : Prop :=
  ∃ x : X, x ∈ c ∧ x ∉ b ∧ a ⊔ Submodule.span R {x} ≠ c

/-- A proper cyclic lift constructs a relative complement explicitly. -/
theorem relativeComplement_of_properCyclicLift
    {a b c : Submodule R X} (hab : a ⋖ b) (hbc : b ⋖ c)
    (h : ProperCyclicLift a b c) :
    ∃ d : Submodule R X, a ≤ d ∧ d ≤ c ∧ b ⊓ d = a ∧ b ⊔ d = c := by
  obtain ⟨x, hxc, hxb, hproper⟩ := h
  have hdc : a ⊔ Submodule.span R {x} ≤ c :=
    sup_le (hab.le.trans hbc.le) (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxc))
  have hdb : ¬a ⊔ Submodule.span R {x} ≤ b := fun h =>
    hxb (h (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)))
  exact ⟨a ⊔ Submodule.span R {x}, le_sup_left, hdc,
    relativeComplement_of_proper_lift hab hbc le_sup_left hdc hdb hproper⟩

/-- This criterion is also necessary; hence it does not strengthen the target. -/
theorem properCyclicLift_iff_relativeComplement
    {a b c : Submodule R X} (hab : a ⋖ b) (hbc : b ⋖ c) :
    ProperCyclicLift a b c ↔
      ∃ d : Submodule R X, a ≤ d ∧ d ≤ c ∧ b ⊓ d = a ∧ b ⊔ d = c := by
  refine ⟨relativeComplement_of_properCyclicLift hab hbc, ?_⟩
  rintro ⟨d, had, hdc, hinf, hsup⟩
  have hdb : ¬d ≤ b := by
    intro h
    exact hbc.ne ((sup_eq_left.mpr h).symm.trans hsup)
  have hex : ∃ x : X, x ∈ d ∧ x ∉ b := by
    by_contra h
    apply hdb
    intro x hx
    by_contra hxb
    exact h ⟨x, hx, hxb⟩
  obtain ⟨x, hxd, hxb⟩ := hex
  refine ⟨x, hdc hxd, hxb, ?_⟩
  intro heq
  have hcd : c ≤ d := heq ▸ sup_le had
    (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxd))
  have hbd : b ≤ d := hbc.le.trans hcd
  exact hab.ne (hinf.symm.trans (inf_eq_left.mpr hbd))

/-- A bottom slice need only detect the nonzero lower factor and miss the
bottom of the generated lift. The slice itself need not be mode-stable or
graded. The final hypothesis is the genuine generation-control obligation. -/
theorem relativeComplement_of_generated_bottom_separation
    {a b c : Submodule R X} (hab : a ⋖ b) (hbc : b ⋖ c)
    (T U : Set X) (hUc : U ⊆ c)
    (hupper : ∃ x ∈ U, x ∉ b)
    (hlower : ∃ y ∈ T, y ∈ b ∧ y ∉ a)
    (hbottom : ∀ y ∈ T, y ∈ a ⊔ Submodule.span R U → y ∈ a) :
    ∃ d : Submodule R X, a ≤ d ∧ d ≤ c ∧ b ⊓ d = a ∧ b ⊔ d = c := by
  let d := a ⊔ Submodule.span R U
  have hdc : d ≤ c := sup_le (hab.le.trans hbc.le) (Submodule.span_le.mpr hUc)
  have hdb : ¬d ≤ b := by
    obtain ⟨x, hx, hxb⟩ := hupper
    exact fun h => hxb (h (Submodule.mem_sup_right (Submodule.subset_span hx)))
  have hproper : d ≠ c := by
    obtain ⟨y, hyT, hyb, hya⟩ := hlower
    intro heq
    exact hya (hbottom y hyT (by change y ∈ d; rw [heq]; exact hbc.le hyb))
  exact ⟨d, le_sup_left, hdc,
    relativeComplement_of_proper_lift hab hbc le_sup_left hdc hdb hproper⟩

/-- An exact ring-theoretic reformulation, with no grading on the submodules. -/
theorem twoStepSplitting_iff_properCyclicLift :
    TwoStepSplitting (Submodule R X) ↔
      ∀ a b c : Submodule R X, a ⋖ b → b ⋖ c → ProperCyclicLift a b c := by
  constructor
  · intro h a b c hab hbc
    exact (properCyclicLift_iff_relativeComplement hab hbc).mpr (h a b c hab hbc)
  · intro h a b c hab hbc
    exact relativeComplement_of_properCyclicLift hab hbc (h a b c hab hbc)

end Ring

end VOA.Classification.COne.PlusSplitting

namespace VOA.Classification.COne

set_option maxSynthPendingDepth 3

open PlusRational PlusSplitting

/-- OPEN: proper lifts for all two-step intervals of the actual cyclic mode
modules. This retains all the original quantifiers, including arbitrary
ungraded submodules. No claim of an unconditional proof is made. -/
def V2mPlusProperCyclicLiftFactGe2 : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m →
    ∀ {M : Type} [AddCommGroup M] [Module ℂ M]
      (N : AdmissibleModule (V2mPlus m hm) M) (x : M),
      ∀ a b c : Submodule (modeAlg N.toWeakModule) (cyclic N.toWeakModule x),
        a ⋖ b → b ⋖ c → ProperCyclicLift a b c

/-- Exact reduction of the requested fact to proper generated lifts. -/
theorem v2mPlusTwoStepSplittingFactGe2_iff_properCyclicLift :
    V2mPlusTwoStepSplittingFactGe2 ↔ V2mPlusProperCyclicLiftFactGe2 := by
  constructor
  · intro h m hm hm2 M _ _ N x
    exact (twoStepSplitting_iff_properCyclicLift
      (R := modeAlg N.toWeakModule) (X := cyclic N.toWeakModule x)).mp (h m hm hm2 N x)
  · intro h m hm hm2 M _ _ N x
    exact (twoStepSplitting_iff_properCyclicLift
      (R := modeAlg N.toWeakModule) (X := cyclic N.toWeakModule x)).mpr (h m hm hm2 N x)

/-- The resulting rationality reduction is still an equivalence. -/
theorem v2mPlusRationalFactGe2_iff_finiteLength_properCyclicLift :
    V2mPlusRationalFactGe2 ↔
      V2mPlusCyclicFiniteLengthFactGe2 ∧ V2mPlusProperCyclicLiftFactGe2 := by
  rw [v2mPlusRationalFactGe2_iff_finiteLength_twoStepSplitting,
    v2mPlusTwoStepSplittingFactGe2_iff_properCyclicLift]

end VOA.Classification.COne
