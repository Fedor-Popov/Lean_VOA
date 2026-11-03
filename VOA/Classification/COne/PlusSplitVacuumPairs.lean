import VOA.Classification.COne.PlusSplitTranslationObstruction
import VOA.Classification.COne.PlusSplitPairObligations

/-! Concrete ordered pair splitting with vacuum quotient and kernel bottom
strictly above one. Weight-zero identification uses proved pseudo-unitarity;
no classification or self-duality hypothesis is added to PairSplitting. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusSplitting
open PlusRational ABDWeakAdmissible VOA.Huang.LogRemovalAdmissible
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- A simple weak module of a C2-cofinite pseudo-unitary VOA with intrinsic
bottom zero is an adjoint module. -/
theorem simple_zero_bottom_adjoint (hC2 : C2Cofinite W) (hPU : PseudoUnitary W)
    (A : WeakModule W M) (hs : IsAtom (⊤ : Submodule (modeAlg A) M))
    (hb : FactorBottom A ⊥ ⊤ 0) :
    ∃ e : M ≃ₗ[ℂ] V, ∀ a n x, e (A.act a n x) = W.smul a n (e x) := by
  have hh : (L0 A).maxGenEigenspace 0 ≠ ⊥ := by
    intro he
    apply hb.1
    rw [Submodule.restrictScalars_top, top_inf_eq, he]
    exact bot_le
  obtain ⟨x, hx0, hx⟩ := exists_eigenvector_of_maxGenEigenspace_ne_bot A 0 hh
  have hcyc : cyclic A x = ⊤ := by
    apply (hs.le_iff_eq ?_).mp le_top
    intro he
    have hxmem : x ∈ cyclic A x := Submodule.mem_span_singleton_self x
    rw [he, Submodule.mem_bot] at hxmem
    exact hx0 hxmem
  obtain ⟨O, hO, hxO, _⟩ := eigen_cyclic_isOrdinary hC2 A x 0 hx hcyc
  have hirr : O.IsIrreducible := by
    refine ⟨⟨⟨x, 0, hx0⟩⟩, ?_⟩
    rw [hO]
    intro P
    by_cases hp : toR A P = ⊥
    · left; exact congrArg (Submodule.restrictScalars ℂ) hp
    · right; exact congrArg (Submodule.restrictScalars ℂ) ((hs.le_iff_eq hp).mp le_top)
  have hne : O.weight 0 ≠ ⊥ := by
    intro he
    rw [he, Submodule.mem_bot] at hxO
    exact hx0 hxO
  have he : Nonempty (ModuleEquiv W O (adjointModule W)) := by
    by_contra hn
    letI : IsEmpty (ModuleEquiv W O (adjointModule W)) := ⟨fun e => hn ⟨e⟩⟩
    have := hPU M O hirr inferInstance 0 hne
    simp at this
  obtain ⟨e⟩ := he
  refine ⟨e.toLinearEquiv, ?_⟩
  intro a n x
  have he := e.map_act a n x
  rwa [hO] at he

set_option maxHeartbeats 800000 in
-- Transport through the quotient's dependent mode algebra needs more elaboration.
/-- A simple numerical weight-zero quotient supplies a surjection onto the
actual adjoint module, with exactly the original kernel. -/
theorem adjoint_quotient_of_zero_bottom (hC2 : C2Cofinite W) (hPU : PseudoUnitary W)
    (A : WeakModule W M) (P : Submodule (modeAlg A) M) (hP : P ⋖ ⊤)
    (hb : FactorBottom A P ⊤ 0) :
    ∃ π : A.Hom (adjointWeakModule W),
      Function.Surjective π.toLinearMap ∧ modeComap π ⊥ = P := by
  let B := WeakModule.quotient A (ofR A P)
  let q : A.Hom B := WeakModule.quotientMk A (ofR A P)
  have hker : modeComap q ⊥ = P := by
    ext x
    exact Submodule.Quotient.mk_eq_zero ((ofR A P).carrier)
  have hzero : modeMap q P = ⊥ := by
    ext y
    change (∃ x, x ∈ P ∧ q.toLinearMap x = y) ↔ y = 0
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero ((ofR A P).carrier)).mpr hx
    · rintro rfl
      exact ⟨0, P.zero_mem, map_zero _⟩
  have htop : modeMap q ⊤ = ⊤ := by
    ext y
    change (∃ x, x ∈ (⊤ : Submodule ℂ M) ∧ q.toLinearMap x = y) ↔ True
    simp only [Submodule.mem_top, true_and, iff_true]
    exact ((ofR A P).carrier).mkQ_surjective y
  have hs : IsAtom (⊤ : Submodule (modeAlg B) (M ⧸ (ofR A P).carrier)) := by
    have hc := modeMap_covBy q hP (by rw [hker])
    rw [hzero, htop] at hc
    exact hc.is_atom
  have hb' : FactorBottom B ⊥ ⊤ 0 := by
    have ht := (factorBottom_modeMap_iff hC2 q P ⊤ (by rw [hker]) 0).mpr hb
    rwa [hzero, htop] at ht
  obtain ⟨e, he⟩ := simple_zero_bottom_adjoint hC2 hPU B hs hb'
  let π : A.Hom (adjointWeakModule W) :=
    { toLinearMap := e.toLinearMap.comp q.toLinearMap
      map_act := by
        intro a n x
        change e (q.toLinearMap (A.act a n x)) = _
        rw [q.map_act, he]
        rfl }
  refine ⟨π, e.surjective.comp ((ofR A P).carrier.mkQ_surjective), ?_⟩
  ext x
  change e (q.toLinearMap x) = 0 ↔ x ∈ P
  rw [map_eq_zero_iff e e.injective]
  exact Submodule.Quotient.mk_eq_zero ((ofR A P).carrier)

/-- A concrete weak-extension theorem: numerical vacuum quotient and kernel
bottom greater than one suffice, with no model-identification assumptions. -/
theorem complement_of_zero_quotient_bottom_gt_one
    (hC2 : C2Cofinite W) (hPU : PseudoUnitary W)
    (A : WeakModule W M) (P : Submodule (modeAlg A) M) (hP : P ⋖ ⊤)
    (h : ℂ) (hb : FactorBottom A ⊥ P h) (ht : FactorBottom A P ⊤ 0)
    (hh : 1 < h.re) : ∃ Q : Submodule (modeAlg A) M, IsCompl P Q := by
  obtain ⟨π, hπ, hk⟩ := adjoint_quotient_of_zero_bottom hC2 hPU A P hP ht
  rw [← hk] at hb ⊢
  exact complement_of_vacuum_quotient_bottom_gt_one hC2 A π hπ h hb hh

end VOA.Classification.COne.PlusSplitting

namespace VOA.Classification.COne.PlusResonantPairs
open PlusSplitting PlusCharacterTable

/-- Unconditional ordered pair splitting for every kernel row above weight one
and vacuum quotient. The opposite orientation is not asserted here. -/
theorem pairSplitting_vacuum_quotient_of_gt_one (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    (i : Label m) (hi : 1 < weight m i) : PairSplitting m hm i (.inr 0) := by
  intro M _ _ A P _ hQ hb ht
  have ht0 : FactorBottom A P ⊤ 0 := by simpa [weight] using ht
  apply complement_of_zero_quotient_bottom_gt_one (V2mPlus_c2Cofinite m hm)
    (V2mPlus_pseudoUnitary_ge2 m hm hm2) A P hQ _ hb ht0
  change (1 : ℝ) < ((weight m i : ℚ) : ℝ)
  exact_mod_cast hi

theorem half_vacuum_quotient_split (m : ℕ) (hm : 1 ≤ m) (hm4 : 4 < m) :
    PairSplitting m hm (.inr 2) (.inr 0) ∧
      PairSplitting m hm (.inr 3) (.inr 0) := by
  have hgt : (1 : ℚ) < (m : ℚ) / 4 := by
    have : (4 : ℚ) < m := by exact_mod_cast hm4
    linarith
  constructor <;> apply pairSplitting_vacuum_quotient_of_gt_one m hm (by omega)
  · exact hgt
  · exact hgt

theorem charged_vacuum_quotient_split (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    (r : Fin (m - 1)) (hr : 4 * m < (r.val + 1) ^ 2) :
    PairSplitting m hm (.inl r) (.inr 0) := by
  apply pairSplitting_vacuum_quotient_of_gt_one m hm hm2
  change (1 : ℚ) < ((r.val : ℚ) + 1)^2 / (4 * m)
  apply (lt_div_iff₀ (by positivity : (0 : ℚ) < 4 * m)).mpr
  norm_num only [one_mul]
  exact_mod_cast hr

/-- Among integral-gap vacuum quotients the only remaining numerical kernel
bottom is one. Equal numerical rows impose exactly the same PairSplitting. -/
theorem vacuum_quotient_family_iff_sign (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) :
    (∀ i : Label m, (.inr 0, i) ∈ positivePairs m →
      PairSplitting m hm i (.inr 0)) ↔ PairSplitting m hm (.inr 1) (.inr 0) := by
  constructor
  · intro h M _ _ A P hP hQ hb ht
    exact h (.inr 1) (vacuum_sign_mem m) A P hP hQ hb ht
  · intro hs i hi M _ _ A P hP hQ hb ht
    obtain ⟨z, hz, he⟩ := (mem_positivePairs_iff m (.inr 0) i).mp hi
    have hw : weight m i = (z : ℚ) := by
      apply Rat.cast_injective (α := ℂ)
      simpa only [Rat.cast_intCast, weight, Matrix.cons_val_zero, Rat.cast_zero, zero_add] using he
    by_cases h1 : z = 1
    · have heq : weight m i = weight m (.inr 1) := by
        rw [hw, h1]
        norm_num [weight]
      exact hs A P hP hQ (by simpa only [heq] using hb) ht
    · have hgt : 1 < weight m i := by
        rw [hw]
        exact_mod_cast (by omega : (1 : ℤ) < z)
      exact pairSplitting_vacuum_quotient_of_gt_one m hm hm2 i hgt A P hP hQ hb ht

end VOA.Classification.COne.PlusResonantPairs
