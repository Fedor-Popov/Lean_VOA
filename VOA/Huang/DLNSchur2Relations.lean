import VOA.Huang.DLNSchur2Lifts
import VOA.Huang.DLNSchurTwo

/-! # Exact remaining mixed-root relations

`RootLiftExtension` asks whether two torsion root lifts in the derived subgroup extend
to a homomorphism on the matrix group. This is an unproved, explicit relation problem.
For moduli coprime to six it is proved equivalent to the original Schur condition.
The family of powers of three is retained separately, without any weakening.
-/

namespace VOA.Huang.DLNSchur

open VOA.Huang.DLNBeyl
open scoped commutatorElement

/-- If a subgroup surjects onto the quotient of a central extension, it contains the
whole derived subgroup of the extension. -/
theorem commutator_le_of_central_map_top {E Q : Type*} [Group E] [Group Q]
    (π : E →* Q) (hc : π.ker ≤ Subgroup.center E) (H : Subgroup E)
    (hH : H.map π = ⊤) : commutator E ≤ H := by
  have hdecomp : ∀ e : E, ∃ z ∈ Subgroup.center E, ∃ a ∈ H, e = z * a := by
    intro e
    obtain ⟨a, ha, hpa⟩ : π e ∈ H.map π := by rw [hH]; trivial
    refine ⟨e * a⁻¹, hc ?_, a, ha, by group⟩
    simp [MonoidHom.mem_ker, hpa]
  rw [commutator_eq_closure, Subgroup.closure_le]
  rintro _ ⟨e, d, rfl⟩
  obtain ⟨z, hz, a, ha, rfl⟩ := hdecomp e
  obtain ⟨w, hw, b, hb, rfl⟩ := hdecomp d
  have hza : Commute z a := (Subgroup.mem_center_iff.mp hz a).symm
  have hzb : Commute z b := (Subgroup.mem_center_iff.mp hz b).symm
  have hwa : Commute w a := (Subgroup.mem_center_iff.mp hw a).symm
  have hwb : Commute w b := (Subgroup.mem_center_iff.mp hw b).symm
  have hzw : Commute z w := (Subgroup.mem_center_iff.mp hz w).symm
  rw [commutator_mul_mul_of_commute hza hzb hwa hwb, hzw.commutator_eq, one_mul]
  exact H.commutator_le_self (Subgroup.commutator_mem_commutator ha hb)

/-- The two corrected lifts generate exactly the derived subgroup. -/
theorem root_lifts_generate_derived {n : ℕ} [NeZero n] {E : Type*} [Group E]
    (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod n))
    (hc : π.ker ≤ Subgroup.center E) (a b : E)
    (ha : a ∈ commutator E) (hb : b ∈ commutator E)
    (hpa : π a = upperRoot 1) (hpb : π b = lowerRoot 1) :
    Subgroup.closure {a, b} = commutator E := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  · apply commutator_le_of_central_map_top π hc
    rw [MonoidHom.map_closure]
    simpa only [Set.image_insert_eq, Set.image_singleton, hpa, hpb] using root_generators n

/-- Every central extension away from six has two honest root homomorphisms whose
ranges generate its derived subgroup. The mixed-root relations are not asserted here. -/
theorem exists_root_homs {n : ℕ} [NeZero n] {E : Type*} [Group E]
    (h2 : Nat.Coprime 2 n) (h3 : Nat.Coprime 3 n)
    (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod n))
    (hs : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E) :
    ∃ X Y : Multiplicative (ZMod n) →* E,
      (∀ t, π (X t) = upperRoot t.toAdd) ∧
      (∀ t, π (Y t) = lowerRoot t.toAdd) ∧
      X.range ⊔ Y.range = commutator E := by
  obtain ⟨a, ha, hpa, han⟩ := exists_upper_torsion_lift h2 h3 π hs hc
  obtain ⟨b, hb, hpb, hbn⟩ := exists_lower_torsion_lift h2 h3 π hs hc
  let X := cyclicLift a han
  let Y := cyclicLift b hbn
  refine ⟨X, Y, cyclicLift_upper π a han hpa, cyclicLift_lower π b hbn hpb, ?_⟩
  apply le_antisymm
  · apply sup_le
    · rintro _ ⟨t, rfl⟩
      exact (commutator E).pow_mem ha t.toAdd.val
    · rintro _ ⟨t, rfl⟩
      exact (commutator E).pow_mem hb t.toAdd.val
  · rw [← root_lifts_generate_derived π hc a b ha hb hpa hpb, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · apply le_sup_left (α := Subgroup E)
      exact ⟨Multiplicative.ofAdd 1, by simpa [X] using cyclicLift_natCast _ han 1⟩
    · apply le_sup_right (α := Subgroup E)
      exact ⟨Multiplicative.ofAdd 1, by simpa [Y] using cyclicLift_natCast _ hbn 1⟩

/-- Precise remaining relations: the two torsion root lifts must extend together to a
homomorphism from the matrix group. This proposition is NOT proved unconditionally. -/
def RootLiftExtension (n : ℕ) : Prop :=
  ∀ (E : Type) [Group E] (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod n)),
    Function.Surjective π → π.ker ≤ Subgroup.center E →
    ∀ a b : E, a ∈ commutator E → b ∈ commutator E →
      π a = upperRoot 1 → π b = lowerRoot 1 → a ^ n = 1 → b ^ n = 1 →
      ∃ σ : Matrix.SpecialLinearGroup (Fin 2) (ZMod n) →* E,
        σ (upperRoot 1) = a ∧ σ (lowerRoot 1) = b

/-- Root relations suffice for the Schur condition away from two and three. -/
theorem schurTrivial_of_rootLiftExtension {n : ℕ} [NeZero n]
    (h2 : Nat.Coprime 2 n) (h3 : Nat.Coprime 3 n) (hrel : RootLiftExtension n) :
    SchurTrivial (Matrix.SpecialLinearGroup (Fin 2) (ZMod n)) := by
  apply (schurTrivial_iff_centralDerivedInjective _).mpr
  intro E _ π hs hc x hx hpx
  obtain ⟨a, ha, hpa, han⟩ := exists_upper_torsion_lift h2 h3 π hs hc
  obtain ⟨b, hb, hpb, hbn⟩ := exists_lower_torsion_lift h2 h3 π hs hc
  obtain ⟨σ, hσa, hσb⟩ := hrel E π hs hc a b ha hb hpa hpb han hbn
  have hsection : π.comp σ = MonoidHom.id _ := by
    apply MonoidHom.eq_of_eqOn_dense (s := {upperRoot 1, lowerRoot 1})
    · exact root_generators n
    · intro g hg
      rcases hg with rfl | rfl
      · simpa [hσa] using hpa
      · simpa [hσb] using hpb
  have hmem : x ∈ σ.range := by
    have hle : Subgroup.closure {a, b} ≤ σ.range := by
      rw [Subgroup.closure_le]
      intro g hg
      rcases hg with rfl | rfl
      · exact ⟨upperRoot 1, hσa⟩
      · exact ⟨lowerRoot 1, hσb⟩
    rw [root_lifts_generate_derived π hc a b ha hb hpa hpb] at hle
    exact hle hx
  obtain ⟨q, rfl⟩ := hmem
  have hq : q = 1 := by
    have he := congrArg (fun f => f q) hsection
    exact he.symm.trans hpx
  simp [hq]

/-- Conversely, the Schur condition proves the specified root relations. -/
theorem rootLiftExtension_of_schurTrivial {n : ℕ} [NeZero n]
    (hschur : SchurTrivial (Matrix.SpecialLinearGroup (Fin 2) (ZMod n))) :
    RootLiftExtension n := by
  intro E _ π hs hc a b ha hb hpa hpb _ _
  let H := commutator E
  let f : H →* Matrix.SpecialLinearGroup (Fin 2) (ZMod n) := π.comp H.subtype
  have hf_surj : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← root_generators n, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact ⟨⟨a, ha⟩, hpa⟩
    · exact ⟨⟨b, hb⟩, hpb⟩
  have hf_inj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro y hy
    apply Subtype.ext
    exact (schurTrivial_iff_centralDerivedInjective _).mp hschur E π hs hc y y.2 hy
  let e := MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  refine ⟨H.subtype.comp e.symm.toMonoidHom, ?_, ?_⟩
  · change (e.symm (upperRoot 1) : E) = a
    have he : e.symm (upperRoot 1) = ⟨a, ha⟩ := by
      apply e.injective
      simpa [e, f] using hpa.symm
    exact congrArg Subtype.val he
  · change (e.symm (lowerRoot 1) : E) = b
    have he : e.symm (lowerRoot 1) = ⟨b, hb⟩ := by
      apply e.injective
      simpa [e, f] using hpb.symm
    exact congrArg Subtype.val he

/-- An equivalence, so the residual has not silently weakened the target. -/
theorem schurTrivial_iff_rootLiftExtension {n : ℕ} [NeZero n]
    (h2 : Nat.Coprime 2 n) (h3 : Nat.Coprime 3 n) :
    SchurTrivial (Matrix.SpecialLinearGroup (Fin 2) (ZMod n)) ↔ RootLiftExtension n :=
  ⟨rootLiftExtension_of_schurTrivial, schurTrivial_of_rootLiftExtension h2 h3⟩

/-- TRUE, unproved remaining mixed-root relations for primes at least five. -/
def LargePrimeRootRelations : Prop :=
  ∀ p k : ℕ, p.Prime → 5 ≤ p → 0 < k → RootLiftExtension (p ^ k)

/-- TRUE, unproved remaining family of powers of three. -/
def ThreePowerSchur : Prop :=
  ∀ k : ℕ, 0 < k → SchurTrivial (Matrix.SpecialLinearGroup (Fin 2) (ZMod (3 ^ k)))

/-- Exact decomposition of the original target into the two remaining arithmetic problems. -/
theorem oddPrimePowerSchur_iff_rootRelations_and_three :
    OddPrimePowerSchur ↔ LargePrimeRootRelations ∧ ThreePowerSchur := by
  constructor
  · intro h
    constructor
    · intro p k hp hp5 hk
      haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
      exact rootLiftExtension_of_schurTrivial (h p k hp (by omega) hk)
    · intro k hk
      exact h 3 k (by decide) (by decide) hk
  · rintro ⟨hlarge, hthree⟩ p k hp hp2 hk
    by_cases hp3 : p = 3
    · subst p; exact hthree k hk
    · have hp5 : 5 ≤ p := by
        have := hp.two_le
        have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
        omega
      haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
      exact schurTrivial_of_rootLiftExtension (primePower_coprime_two_three hp hp5).1
        (primePower_coprime_two_three hp hp5).2 (hlarge p k hp hp5 hk)

/-- Conditional assembly; all three hypotheses remain explicit arithmetic residuals. -/
theorem matrixDLNLifting_of_rootRelations
    (hlarge : LargePrimeRootRelations) (hthree : ThreePowerSchur)
    (htwo : TwoPowerInflationFromTwo) : VOA.Huang.DLNBridge.MatrixDLNLifting :=
  matrixDLNLifting_of_remaining
    (oddPrimePowerSchur_iff_rootRelations_and_three.mpr ⟨hlarge, hthree⟩) htwo

end VOA.Huang.DLNSchur
