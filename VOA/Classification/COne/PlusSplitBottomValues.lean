import VOA.Classification.COne.PlusSplitTransport
import VOA.Classification.COne.PlusSplittingWeights

/-! Numerical character-table coverage for intrinsic weak-subquotient bottoms.
No irreducible-module classification or ordinary middle module is assumed. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusSplitting
open PlusRational ABDWeakAdmissible VOA.Huang.LogRemovalAdmissible

/-- Every intrinsic bottom of a whole weak module occurs as an ordinary
lowest weight, by passing to the cyclic module of an actual eigenvector. -/
theorem ordinary_witness_of_factorBottom
    {V M : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
    (hC2 : C2Cofinite W) (A : WeakModule W M) (h : ℂ)
    (hb : FactorBottom A ⊥ ⊤ h) :
    ∃ (X : Type) (_ : AddCommGroup X) (_ : Module ℂ X) (O : OrdVModule W X),
      IsLowestWeight O h ∧ O.weight h ≠ ⊥ := by
  have hh : (L0 A).maxGenEigenspace h ≠ ⊥ := by
    intro he
    apply hb.1
    rw [Submodule.restrictScalars_top, top_inf_eq, he]
    exact bot_le
  obtain ⟨x, hx0, hx⟩ := exists_eigenvector_of_maxGenEigenspace_ne_bot A h hh
  let P := ofR A (cyclic A x)
  let B := WeakModule.submodule A P
  let z : P.carrier := ⟨x, Submodule.mem_span_singleton_self x⟩
  obtain ⟨O, hO, hzO, hcos⟩ := eigen_cyclic_isOrdinary hC2 B z h
    (Subtype.ext hx) (cyclic_restriction_eq_top A x)
  have hne : O.weight h ≠ ⊥ := by
    intro he
    rw [he] at hzO
    exact hx0 (congrArg Subtype.val (show z = 0 from hzO))
  obtain ⟨μ, n, hlow, hμ, he⟩ := ordinary_coset_has_lowest O h hne hcos
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
  have hyA : L0 A (y : M) = μ • (y : M) := by
    have ht := O.L0_weight μ y hy
    change L0 O.toWeakModule y = μ • y at ht
    rw [hO] at ht
    exact congrArg Subtype.val ht
  have hμA : FactorWeight A ⊥ ⊤ μ := by
    intro ht
    have hygen : (y : M) ∈ (L0 A).maxGenEigenspace μ :=
      (L0 A).eigenspace_le_maxGenEigenspace
        ((Module.End.mem_eigenspace_iff).mpr hyA)
    exact hy0 (Subtype.ext (ht ⟨Submodule.mem_top, hygen⟩))
  have hbound := hb.2 μ hμA
  have hn : n = 0 := by
    have hre := congrArg Complex.re he
    simp only [Complex.add_re, Complex.natCast_re] at hre
    have : (n : ℝ) ≤ 0 := by linarith
    exact_mod_cast (le_antisymm this (Nat.cast_nonneg n))
  have heq : h = μ := by simpa [hn] using he
  exact ⟨P.carrier, inferInstance, inferInstance, O, heq ▸ hlow, hne⟩

theorem lowestWeightValue_of_whole_factorBottom
    (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : WeakModule (V2mPlus m hm) M) (h : ℂ)
    (hb : FactorBottom A ⊥ ⊤ h) : LowestWeightValue m h := by
  obtain ⟨X, a, b, O, hlo, hne⟩ :=
    ordinary_witness_of_factorBottom (V2mPlus_c2Cofinite m hm) A h hb
  exact lowestWeightValue_of_ordinary m hm hm2 O h hlo hne

set_option maxHeartbeats 1200000 in
-- Nested mode algebras and quotient transport require additional elaboration.
/-- Coverage holds for arbitrary strict weak subquotients, even without
simplicity. The factor bottom, not a grading on the ambient module, is used. -/
theorem lowestWeightValue_of_factorBottom
    (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : WeakModule (V2mPlus m hm) M)
    (a b : Submodule (modeAlg A) M) (hab : a ≤ b) (h : ℂ)
    (hb : FactorBottom A a b h) : LowestWeightValue m h := by
  let C : WeakModule (V2mPlus m hm) b := WeakModule.submodule A (ofR A b)
  let ι : C.Hom A := { toLinearMap := (b.restrictScalars ℂ).subtype
                       map_act := fun _ _ _ => rfl }
  have hr : modeMap ι ⊤ = b := by
    ext x
    change (∃ y : b, y ∈ (⊤ : Submodule ℂ b) ∧ (y : M) = x) ↔ x ∈ b
    simp
  have hk : modeComap ι ⊥ = ⊥ := by
    ext x
    change ι.toLinearMap x = 0 ↔ x = 0
    exact map_eq_zero_iff ι.toLinearMap Subtype.val_injective
  let a' := modeComap ι a
  have ha : modeMap ι a' = a := by
    rw [modeMap_comap, hr, inf_eq_left.mpr hab]
  have hb' : FactorBottom C a' ⊤ h := by
    apply (factorBottom_modeMap_iff (V2mPlus_c2Cofinite m hm) ι a' ⊤
      (by rw [hk]; exact bot_le) h).mp
    rwa [ha, hr]
  let Q := WeakModule.quotient C (ofR C a')
  let π : C.Hom Q := WeakModule.quotientMk C (ofR C a')
  have hker : modeComap π ⊥ = a' := by
    ext x
    exact Submodule.Quotient.mk_eq_zero ((ofR C a').carrier)
  have hzero : modeMap π a' = ⊥ := by
    ext y
    change (∃ x, x ∈ a' ∧ π.toLinearMap x = y) ↔ y = 0
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero ((ofR C a').carrier)).mpr hx
    · rintro rfl
      exact ⟨0, a'.zero_mem, map_zero _⟩
  have htop : modeMap π ⊤ = ⊤ := by
    ext y
    change (∃ x, x ∈ (⊤ : Submodule ℂ b) ∧ π.toLinearMap x = y) ↔ True
    simp only [Submodule.mem_top, true_and, iff_true]
    exact ((ofR C a').carrier).mkQ_surjective y
  apply lowestWeightValue_of_whole_factorBottom m hm hm2 Q h
  have ht := (factorBottom_modeMap_iff (V2mPlus_c2Cofinite m hm) π a' ⊤
    (by rw [hker]) h).mpr hb'
  rwa [hzero, htop] at ht

end VOA.Classification.COne.PlusSplitting
