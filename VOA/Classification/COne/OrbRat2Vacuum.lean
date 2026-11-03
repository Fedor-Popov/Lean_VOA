import VOA.Classification.COne.OrbRat2Cubic
import VOA.Classification.COne.PlusRatVacuumSign
import VOA.Classification.COne.PlusSplitVacuumPairs
import VOA.Classification.COne.PlusUnitaryVacuum

/-!
# Vacuum-quotient resonant pairs from a Zhu character table (any `C₂`-cofinite VOA)

For a `C₂`-cofinite VOA `W` with a Zhu character table (`CharTable`, `finrank A(W) ≤ n`):

* `exists_eigen_character`: every nonzero top of an ordinary module contains a vector on which
  `A(W)` acts by one of the table characters (idempotents of `A(W) ≅ ℂⁿ`);
* `charTable_trivial`: the unique table character of weight `0` vanishes on every homogeneous
  state of positive weight (it is the vacuum character);
* `zeroWeightAdjoint_of_charTable`: every irreducible ordinary module with a nonzero weight-zero
  space is the adjoint module — this REPLACES pseudo-unitarity in the library's vacuum-quotient
  identification (`adjoint_quotient_of_zero_bottom'`), which would be circular for orbifolds;
* `top_eq_zero_of_table`: a top vector of eigenvalue `c` killed by `z ∈ A(W)` vanishes when
  every table character of weight `c` is nonzero on `z`;
* `pairSplit_gt_one_zero`: every kernel bottom `h` with `Re h > 1` splits over a vacuum quotient;
* `pairSplit_one_zero_of_telescope`: kernel bottom `1` splits over a vacuum quotient as soon as
  one telescope element `PlusRatTelescope.zeta W a b N J` is nonzero on the weight-one table
  characters.

For the tetrahedral model: the pair `(4 ↘ 0)` is proved from the Zhu inputs
(`cubic_pair_four_zero`); `(1 ↘ 0)` follows from the single numerical input
`CubicVacuumTelescope` (`cubic_pair_one_zero`; numerically `λ = -96` for `a = b = U`, the
weight-nine generator, `telescope_u9.py`).  Rationality of the model is reduced to the Zhu
inputs, `CubicVacuumTelescope`, and the two NON-vacuum pairs `(4 ↘ 1)`, `(9/4 ↘ 1/4)`
(`cubicModel_admissiblyRational_of_reduced`).
-/

set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Classification.COne.OrbRat2

open VOA VertexOperatorAlgebra PlusSplitting PlusRational ABDWeakAdmissible
  VOA.Huang.LogRemovalAdmissible PlusUnitary PlusRatTelescope

section Generic

variable {V : Type} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Idempotents of `A(W) ≅ ℂⁿ` attached to distinct characters saturating the dimension. -/
theorem charTable_idempotents (hC2 : C2Cofinite W) {n : ℕ}
    (hdim : Module.finrank ℂ (VOA.A W) ≤ n)
    (χ : Fin n → (letI := instRingA W; letI := instAlgebraA W; VOA.A W →ₐ[ℂ] ℂ))
    (hχ : Function.Injective χ) :
    letI := instRingA W; letI := instAlgebraA W
    ∃ ε : Fin n → VOA.A W, (∑ i, ε i = 1) ∧ (∀ a i, a * ε i = χ i a • ε i) ∧
      (∀ a i, ε i * a = χ i a • ε i) := by
  letI := instRingA W
  letI := instAlgebraA W
  letI := finiteDimensional_A_of_C2Cofinite W hC2
  let e := characterAlgEquiv χ hχ (by simpa using hdim)
  have he : ∀ a j, e a j = χ j a := fun _ _ => rfl
  refine ⟨fun i => e.symm (Pi.single i 1), ?_, ?_, ?_⟩
  · apply e.injective
    rw [map_sum, map_one]
    simp only [AlgEquiv.apply_symm_apply]
    exact Finset.univ_sum_single 1
  · intro a i
    apply e.injective
    rw [map_mul, map_smul, AlgEquiv.apply_symm_apply]
    ext j
    by_cases hj : j = i
    · subst hj; simp [he]
    · simp [hj]
  · intro a i
    apply e.injective
    rw [map_mul, map_smul, AlgEquiv.apply_symm_apply]
    ext j
    by_cases hj : j = i
    · subst hj; simp [he]
    · simp [hj]

/-- A nonzero top vector produces a nonzero top vector on which `A(W)` acts through a
table character. -/
theorem exists_eigen_character (hC2 : C2Cofinite W) {n : ℕ}
    (hdim : Module.finrank ℂ (VOA.A W) ≤ n)
    (χ : Fin n → (letI := instRingA W; letI := instAlgebraA W; VOA.A W →ₐ[ℂ] ℂ))
    (hχ : Function.Injective χ)
    {M : Type} [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M) {h : ℂ}
    (hlow : IsLowestWeight N h) {x : N.weight h} (hx : x ≠ 0) :
    ∃ (i : Fin n) (y : N.weight h), y ≠ 0 ∧
      ∀ r, ZhuPolynomialSimplicity.actAAlgHom W N hlow r y = χ i r • y := by
  letI := instRingA W
  letI := instAlgebraA W
  obtain ⟨ε, hsum, hmul, -⟩ := charTable_idempotents hC2 hdim χ hχ
  let ρ := ZhuPolynomialSimplicity.actAAlgHom W N hlow
  have hex : ∃ i, ρ (ε i) x ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hx
    have h1 : ρ 1 x = x := by rw [map_one]; rfl
    rw [← h1, ← hsum, map_sum, LinearMap.coe_sum, Finset.sum_apply]
    exact Finset.sum_eq_zero fun i _ => hall i
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, ρ (ε i) x, hi, fun r => ?_⟩
  change ρ r (ρ (ε i) x) = _
  rw [← Module.End.mul_apply, ← map_mul, hmul, map_smul]
  rfl

theorem omega_act_top {M : Type} [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M) {h : ℂ}
    (hlow : IsLowestWeight N h) (y : N.weight h) :
    letI := instRingA W; letI := instAlgebraA W
    ZhuPolynomialSimplicity.actAAlgHom W N hlow (VOA.mk W W.conformalVector) y = h • y := by
  apply Subtype.ext
  change ((actA N hlow (VOA.mk W W.conformalVector) y : N.weight h) : M) = h • (y : M)
  rw [actA_mk_apply_coe, oMod_homogeneous _ W.conformalVector_mem_grading_two]
  exact N.L0_weight _ _ y.property

/-- The table character of weight zero is the vacuum character. -/
theorem charTable_trivial (hC2 : C2Cofinite W) (hvac : W.vacuum ≠ 0) {n : ℕ} {wt : Fin n → ℂ}
    (hdim : Module.finrank ℂ (VOA.A W) ≤ n)
    (χ : Fin n → (letI := instRingA W; letI := instAlgebraA W; VOA.A W →ₐ[ℂ] ℂ))
    (hχ : Function.Injective χ) (hω : ∀ i, χ i (VOA.mk W W.conformalVector) = wt i)
    (i₀ : Fin n) (h₀ : ∀ i, wt i = 0 → i = i₀)
    {k : ℤ} (hk : 1 ≤ k) {a : V} (ha : a ∈ W.grading k) :
    χ i₀ (VOA.mk W a) = 0 := by
  letI := instRingA W
  letI := instAlgebraA W
  obtain ⟨ε, hsum, hmul, hmul'⟩ := charTable_idempotents hC2 hdim χ hχ
  let N := adjointModule W
  have hlow := isLowestWeight_adjoint W
  let ρ := ZhuPolynomialSimplicity.actAAlgHom W N hlow
  let v : N.weight 0 := ⟨W.vacuum, vacuum_mem_adjoint_weight W⟩
  have hv : v ≠ 0 := fun h0 => hvac (congrArg Subtype.val h0)
  have hex : ∃ i, ρ (ε i) v ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hv
    have h1 : ρ 1 v = v := by rw [map_one]; rfl
    rw [← h1, ← hsum, map_sum, LinearMap.coe_sum, Finset.sum_apply]
    exact Finset.sum_eq_zero fun i _ => hall i
  obtain ⟨i, hi⟩ := hex
  have hact : ∀ r, ρ r (ρ (ε i) v) = χ i r • ρ (ε i) v := by
    intro r
    rw [← Module.End.mul_apply, ← map_mul, hmul, map_smul]
    rfl
  have hwi : wt i = 0 := by
    have h1 := hact (VOA.mk W W.conformalVector)
    rw [omega_act_top N hlow, hω, zero_smul] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_right hi
  have hii : i = i₀ := h₀ i hwi
  subst hii
  have hzero : ρ (VOA.mk W a) v = 0 := by
    apply Subtype.ext
    change ((actA N hlow (VOA.mk W a) v : N.weight 0) : V) = 0
    rw [actA_mk_apply_coe, oMod_homogeneous _ ha]
    exact (W.creation a).2 (k - 1) (by omega)
  have h2 : ρ (VOA.mk W a) (ρ (ε i) v) = 0 := by
    rw [← Module.End.mul_apply, ← map_mul, hmul, ← hmul', map_mul, Module.End.mul_apply,
      hzero, map_zero]
  rw [hact] at h2
  exact (smul_eq_zero.mp h2).resolve_right hi

/-- With a character table whose weights have nonnegative real parts and a unique weight-zero
entry, every irreducible ordinary module with a nonzero weight-zero space is the adjoint module.
(Replaces pseudo-unitarity.) -/
theorem zeroWeightAdjoint_of_charTable (hC2 : C2Cofinite W) (hS : W.IsSimple) {n : ℕ}
    {wt : Fin n → ℂ} (hdim : Module.finrank ℂ (VOA.A W) ≤ n)
    (χ : Fin n → (letI := instRingA W; letI := instAlgebraA W; VOA.A W →ₐ[ℂ] ℂ))
    (hχ : Function.Injective χ) (hω : ∀ i, χ i (VOA.mk W W.conformalVector) = wt i)
    (i₀ : Fin n) (h₀ : ∀ i, wt i = 0 → i = i₀) (hpos : ∀ i, 0 ≤ (wt i).re)
    (M : Type) [AddCommGroup M] [Module ℂ M] (O : OrdVModule W M) (hirr : O.IsIrreducible)
    (hne : O.weight 0 ≠ ⊥) : Nonempty (ModuleEquiv W O (adjointModule W)) := by
  letI := instRingA W
  letI := instAlgebraA W
  obtain ⟨h, hlow, hneh⟩ := OrdVModule.exists_isLowestWeight_of_irreducible O hirr
  obtain ⟨i, hi⟩ := exists_eq_wt_of_charTable hC2 hdim ⟨χ, hχ, hω⟩ O hlow hneh
  obtain ⟨k, hk⟩ := hlow 0 hne
  have hh : h = 0 := by
    have hre := congrArg Complex.re hk
    simp only [Complex.zero_re, Complex.add_re, Complex.natCast_re] at hre
    have h1 := hpos i
    rw [← hi] at h1
    have hk0 : (k : ℝ) = 0 := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have hk0' : k = 0 := by exact_mod_cast hk0
    subst hk0'
    simpa using hk.symm
  subst hh
  obtain ⟨x, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨j, y, hy0, hy⟩ := exists_eigen_character hC2 hdim χ hχ O hlow
    (x := ⟨x, hx0.1⟩) (fun h0 => hx0.2 (congrArg Subtype.val h0))
  have hj : j = i₀ := by
    apply h₀
    have h1 := hy (VOA.mk W W.conformalVector)
    rw [omega_act_top O hlow, hω, zero_smul] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_right hy0
  subst hj
  refine nonempty_moduleEquiv_adjoint_of_vacuumTop hS O hirr hlow y.property
    (fun h0 => hy0 (Subtype.ext h0)) ?_
  intro k hk a ha
  have h1 := congrArg Subtype.val (hy (VOA.mk W a))
  change ((actA O hlow (VOA.mk W a) y : O.weight 0) : M) = _ at h1
  rw [actA_mk_apply_coe] at h1
  rw [h1, charTable_trivial hC2 hS.vacuum_ne_zero hdim χ hχ hω j h₀ hk ha, zero_smul]
  rfl

/-- The library's simple-zero-bottom identification, with pseudo-unitarity replaced by the
exact weight-zero statement it was used for. -/
theorem simple_zero_bottom_adjoint' (hC2 : C2Cofinite W)
    (hZ : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (O : OrdVModule W M),
      O.IsIrreducible → O.weight 0 ≠ ⊥ → Nonempty (ModuleEquiv W O (adjointModule W)))
    {M : Type} [AddCommGroup M] [Module ℂ M]
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
  obtain ⟨e⟩ := hZ M O hirr hne
  refine ⟨e.toLinearEquiv, ?_⟩
  intro a n x
  have he := e.map_act a n x
  rwa [hO] at he

set_option maxHeartbeats 800000 in
-- Transport through the quotient's dependent mode algebra (as in the library original).
/-- `adjoint_quotient_of_zero_bottom` without pseudo-unitarity. -/
theorem adjoint_quotient_of_zero_bottom' (hC2 : C2Cofinite W)
    (hZ : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (O : OrdVModule W M),
      O.IsIrreducible → O.weight 0 ≠ ⊥ → Nonempty (ModuleEquiv W O (adjointModule W)))
    {M : Type} [AddCommGroup M] [Module ℂ M]
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
  obtain ⟨e, he⟩ := simple_zero_bottom_adjoint' hC2 hZ B hs hb'
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

/-- A top vector of eigenvalue `c` killed by `z` vanishes when every table character of
weight `c` is nonzero on `z`. -/
theorem top_eq_zero_of_table (hC2 : C2Cofinite W) {n : ℕ} {wt : Fin n → ℂ}
    (hdim : Module.finrank ℂ (VOA.A W) ≤ n)
    (χ : Fin n → (letI := instRingA W; letI := instAlgebraA W; VOA.A W →ₐ[ℂ] ℂ))
    (hχ : Function.Injective χ) (hω : ∀ i, χ i (VOA.mk W W.conformalVector) = wt i)
    {M : Type} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M) {y : M}
    (hy : y ∈ Omega A) {c : ℂ} (hL : L0 A y = c • y) (z : VOA.A W)
    (hz : topEvaluation A y hy z = 0) (hne : ∀ i, wt i = c → χ i z ≠ 0) : y = 0 := by
  letI := instRingA W
  letI := instAlgebraA W
  obtain ⟨ε, hsum, -, hmul'⟩ := charTable_idempotents hC2 hdim χ hχ
  have key : ∀ s, topEvaluation A y hy s = 0 → ∀ i, topEvaluation A y hy (ε i * s) = 0 := by
    intro s hs i
    obtain ⟨u, hu⟩ := VOA.mk_surjective W (ε i)
    rw [← hu, topEvaluation_mk_mul, hs, map_zero]
  have hfω : topEvaluation A y hy (VOA.mk W W.conformalVector - algebraMap ℂ _ c) = 0 := by
    rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, PlusRatSign.topEvaluation_one]
    change oLevW A 0 W.conformalVector y - c • y = 0
    rw [oLevW_homogeneous A 0 W.conformal_mem]
    change L0 A y - c • y = 0
    rw [hL, sub_self]
  have hεi : ∀ i, topEvaluation A y hy (ε i) = 0 := by
    intro i
    have h1 := key _ hfω i
    rw [mul_sub, hmul', Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, hω,
      ← sub_smul, map_smul] at h1
    have h2 := key z hz i
    rw [hmul', map_smul] at h2
    by_cases hc : wt i = c
    · exact (smul_eq_zero.mp h2).resolve_left (hne i hc)
    · exact (smul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hc)
  rw [← PlusRatSign.topEvaluation_one A y hy, ← hsum, map_sum]
  exact Finset.sum_eq_zero fun i _ => hεi i

/-- Every kernel bottom above one splits over a vacuum quotient. -/
theorem pairSplit_gt_one_zero (hC2 : C2Cofinite W)
    (hZ : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (O : OrdVModule W M),
      O.IsIrreducible → O.weight 0 ≠ ⊥ → Nonempty (ModuleEquiv W O (adjointModule W)))
    (h : ℂ) (hh : 1 < h.re) : PlusRat2Dual.PairSplit W h 0 := by
  intro M _ _ A P _ hQ hb ht
  obtain ⟨π, hπ, hk⟩ := adjoint_quotient_of_zero_bottom' hC2 hZ A P hQ ht
  rw [← hk] at hb ⊢
  exact complement_of_vacuum_quotient_bottom_gt_one hC2 A π hπ h hb hh

/-- Kernel bottom one splits over a vacuum quotient once a telescope element is nonzero on
the weight-one table characters. -/
theorem pairSplit_one_zero_of_telescope (hC2 : C2Cofinite W)
    (hZ : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (O : OrdVModule W M),
      O.IsIrreducible → O.weight 0 ≠ ⊥ → Nonempty (ModuleEquiv W O (adjointModule W)))
    {n : ℕ} {wt : Fin n → ℂ} (hdim : Module.finrank ℂ (VOA.A W) ≤ n)
    (χ : Fin n → (letI := instRingA W; letI := instAlgebraA W; VOA.A W →ₐ[ℂ] ℂ))
    (hχ : Function.Injective χ) (hω : ∀ i, χ i (VOA.mk W W.conformalVector) = wt i)
    {α β : ℤ} {a b : V} (ha : a ∈ W.grading α) (hb' : b ∈ W.grading β) (N J : ℕ)
    (hN : (N : ℤ) = α) (hN1 : 1 ≤ N) (hJ : (J : ℤ) = α + β - 2) (hβ : 0 ≤ β)
    (hnz : ∀ i, wt i = 1 → χ i (zeta W a b N J) ≠ 0) : PlusRat2Dual.PairSplit W 1 0 := by
  intro M _ _ A P _ hQ hb ht
  obtain ⟨π, hπ, hk⟩ := adjoint_quotient_of_zero_bottom' hC2 hZ A P hQ ht
  rw [← hk] at hb ⊢
  obtain ⟨x, hx, he⟩ := exists_generalized_vacuum_lift hC2 A π hπ
  apply (complement_iff_translation_zero_of_positive_bottom A π 1 hb (by norm_num) hx he).mpr
  have ht1 := translation_vacuum_lift_eigen_one A π 1 hb (by norm_num) hx he
  have hyΩ : translation A x ∈ Omega A := by
    apply kernel_bottom_mem_Omega A (modeComap π ⊥) 1 hb
    · change π.toLinearMap (A.act W.conformalVector 0 x) = 0
      rw [π.map_act, he]
      exact (W.creation _).2 0 le_rfl
    · apply Module.End.eigenspace_le_maxGenEigenspace
      apply Module.End.mem_eigenspace_iff.mpr
      simpa only [one_smul] using ht1
  have htel := translation_telescope A π 1 hb (by norm_num) hx he ha hb' N J hN hN1 hJ
  rw [telescope_eq_topEvaluation A ha hb' hyΩ N J hN hN1 hJ hβ] at htel
  exact top_eq_zero_of_table hC2 hdim χ hχ hω A hyΩ (c := 1)
    (by rw [one_smul]; exact ht1) _ htel hnz

end Generic

/-! ## The tetrahedral model -/

section Cubic

open OrbC2b

theorem cubicModel_isSimple : cubicModel.IsSimple := by
  letI : Finite tetra := Finite.of_equiv (alternatingGroup (Fin 4)) tetra_group.some.symm.toEquiv
  obtain ⟨e, he, -⟩ := tetra_cubic_iso
  exact isSimple_of_iso e he (exceptionalOrbifold_isSimple tetra)

theorem tetra_unique_zero : ∀ i, tetraWeight i = 0 → i = 0 := by
  have h : ∀ i : Fin 21, tetraWeightQ i = 0 → i = 0 := by decide +kernel
  intro i hi
  apply h i
  have : ((tetraWeightQ i : ℚ) : ℂ) = ((0 : ℚ) : ℂ) := by simpa [tetraWeight] using hi
  exact_mod_cast this

theorem tetra_nonneg : ∀ i, 0 ≤ (tetraWeight i).re := by
  have h : ∀ i : Fin 21, 0 ≤ tetraWeightQ i := by decide +kernel
  intro i
  simp only [tetraWeight, Complex.ratCast_re]
  exact_mod_cast h i

/-- From the Zhu inputs: the only irreducible with a weight-zero vector is the model itself. -/
theorem cubic_zeroWeightAdjoint (hC2 : C2Cofinite cubicModel) (hdim : CubicZhuDimensionBound)
    (htab : CubicZhuCharacterTable) (M : Type) [AddCommGroup M] [Module ℂ M]
    (O : OrdVModule cubicModel M) (hirr : O.IsIrreducible) (hne : O.weight 0 ≠ ⊥) :
    Nonempty (ModuleEquiv cubicModel O (adjointModule cubicModel)) := by
  obtain ⟨χ, hχ, hω⟩ := htab
  exact zeroWeightAdjoint_of_charTable hC2 cubicModel_isSimple hdim χ hχ hω 0 tetra_unique_zero
    tetra_nonneg M O hirr hne

/-- The resonant pair `(4 ↘ 0)` splits, from the Zhu inputs alone. -/
theorem cubic_pair_four_zero (hC2 : C2Cofinite cubicModel) (hdim : CubicZhuDimensionBound)
    (htab : CubicZhuCharacterTable) : PlusRat2Dual.PairSplit cubicModel 4 0 :=
  pairSplit_gt_one_zero hC2 (cubic_zeroWeightAdjoint hC2 hdim htab) 4 (by norm_num)

/-- OPEN (numerically true: `λ = -96` for `a = b = U`, the weight-nine generator,
by a computer-algebra evaluation outside Lean): some telescope element of the tetrahedral model is
nonzero at every Zhu character of weight one. -/
def CubicVacuumTelescope : Prop :=
  letI := instRingA cubicModel
  letI := instAlgebraA cubicModel
  ∃ (a b : (orbifold (Subgroup.zpowers kleinCubic)).carrier) (α β : ℤ) (N J : ℕ),
    a ∈ cubicModel.grading α ∧ b ∈ cubicModel.grading β ∧ (N : ℤ) = α ∧ 1 ≤ N ∧
      (J : ℤ) = α + β - 2 ∧ 0 ≤ β ∧
      ∀ χ : VOA.A cubicModel →ₐ[ℂ] ℂ, χ (VOA.mk cubicModel cubicModel.conformalVector) = 1 →
        χ (zeta cubicModel a b N J) ≠ 0

/-- The resonant pair `(1 ↘ 0)` splits, from the Zhu inputs and the telescope input. -/
theorem cubic_pair_one_zero (hC2 : C2Cofinite cubicModel) (hdim : CubicZhuDimensionBound)
    (htab : CubicZhuCharacterTable) (htel : CubicVacuumTelescope) :
    PlusRat2Dual.PairSplit cubicModel 1 0 := by
  obtain ⟨χ, hχ, hω⟩ := htab
  obtain ⟨a, b, α, β, N, J, ha, hb, hN, hN1, hJ, hβ, hnz⟩ := htel
  exact pairSplit_one_zero_of_telescope hC2 (cubic_zeroWeightAdjoint hC2 hdim ⟨χ, hχ, hω⟩)
    hdim χ hχ hω ha hb N J hN hN1 hJ hβ
    (fun i hi => hnz (χ i) (by rw [hω]; exact hi))

/-- OPEN (true by Dong–Jiang + Miyamoto): the two non-vacuum resonant pairs. -/
def CubicNonVacuumPairs : Prop :=
  PlusRat2Dual.PairSplit cubicModel 4 1 ∧ PlusRat2Dual.PairSplit cubicModel (9/4) (1/4)

theorem cubicResonantPairs_of_reduced (hC2 : C2Cofinite cubicModel)
    (hdim : CubicZhuDimensionBound) (htab : CubicZhuCharacterTable)
    (htel : CubicVacuumTelescope) (hnv : CubicNonVacuumPairs) : CubicResonantPairs :=
  ⟨cubic_pair_one_zero hC2 hdim htab htel, cubic_pair_four_zero hC2 hdim htab, hnv.1, hnv.2⟩

/-- Rationality of the tetrahedral model from `C₂`, the Zhu inputs, one telescope
nonvanishing, and the two non-vacuum resonant pairs. -/
theorem cubicModel_admissiblyRational_of_reduced (hC2 : C2Cofinite cubicModel)
    (hdim : CubicZhuDimensionBound) (htab : CubicZhuCharacterTable)
    (htel : CubicVacuumTelescope) (hnv : CubicNonVacuumPairs) :
    AdmissiblyRational cubicModel :=
  cubicModel_admissiblyRational_of_inputs hC2 hdim htab
    (cubicResonantPairs_of_reduced hC2 hdim htab htel hnv)

theorem cubicModelRationalOfC2_of_reduced (hdim : CubicZhuDimensionBound)
    (htab : CubicZhuCharacterTable) (htel : CubicVacuumTelescope)
    (hnv : CubicNonVacuumPairs) : CubicModelRationalOfC2 :=
  fun hC2 => cubicModel_admissiblyRational_of_reduced hC2 hdim htab htel hnv

/-- The non-vacuum pairs are necessary (no stronger than the target, given `C₂`). -/
theorem cubicNonVacuumPairs_of_rational (hC2 : C2Cofinite cubicModel)
    (hR : AdmissiblyRational cubicModel) : CubicNonVacuumPairs :=
  ⟨(cubicResonantPairs_of_rational hC2 hR).2.2.1, (cubicResonantPairs_of_rational hC2 hR).2.2.2⟩

end Cubic

end VOA.Classification.COne.OrbRat2
