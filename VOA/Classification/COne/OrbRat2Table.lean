import VOA.Classification.COne.OrbRatSplitting
import VOA.Classification.COne.PlusRat2DualSwap
import VOA.Classification.COne.PlusSplitBottomValues
import VOA.Modules.ZhuPolynomialSimplicity

/-!
# Zhu character tables control every factor bottom (any `C₂`-cofinite VOA)

For a `C₂`-cofinite VOA `W` whose Zhu algebra has at most `n` dimensions and admits `n` distinct
characters `χ i` with `χ i [ω] = wt i` (a `CharTable`):

* `A(W)` is semisimple (`isSemisimpleRing_of_charTable`);
* every nonzero lowest-weight space of an ordinary module has weight `wt i` for some `i`
  (`exists_eq_wt_of_charTable`), via the idempotents of `A(W) ≅ ℂⁿ` — no finite
  dimensionality of the weight space is used;
* every intrinsic factor bottom of every weak module (any subquotient) is some `wt i`
  (`factorBottom_mem_of_table`, the generic form of
  `PlusSplitting.lowestWeightValue_of_factorBottom`);
* hence admissible rationality reduces to `PairSplit` for the ORDERED PAIRS OF TABLE VALUES with
  nonzero integral gap, and by contragredient symmetry (`PlusRat2Dual.pairSplit_swap`) one
  orientation of each unordered pair suffices (`admissiblyRational_of_charTable_pairs`).
-/

set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Classification.COne.OrbRat2

open VOA VertexOperatorAlgebra PlusSplitting PlusRational ABDWeakAdmissible
  VOA.Huang.LogRemovalAdmissible

section Generic

variable {V : Type} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)

/-- A Zhu character table: `n` distinct algebra characters of `A(W)` with prescribed values on
`[ω]`.  (Distinctness + `finrank A(W) ≤ n` forces `A(W) ≅ ℂⁿ`.) -/
def CharTable (n : ℕ) (wt : Fin n → ℂ) : Prop :=
  letI := instRingA W
  letI := instAlgebraA W
  ∃ χ : Fin n → VOA.A W →ₐ[ℂ] ℂ, Function.Injective χ ∧
    ∀ i, χ i (VOA.mk W W.conformalVector) = wt i

variable {W}

theorem isSemisimpleRing_of_charTable (hC2 : C2Cofinite W) {n : ℕ} {wt : Fin n → ℂ}
    (hdim : Module.finrank ℂ (VOA.A W) ≤ n) (ht : CharTable W n wt) :
    letI := instRingA W; IsSemisimpleRing (VOA.A W) := by
  letI := instRingA W
  letI := instAlgebraA W
  letI := finiteDimensional_A_of_C2Cofinite W hC2
  obtain ⟨χ, hχ, -⟩ := ht
  exact isSemisimpleRing_of_characters χ hχ (by simpa using hdim)

/-- Every nonzero lowest-weight space of an ordinary module has a table weight. -/
theorem exists_eq_wt_of_charTable (hC2 : C2Cofinite W) {n : ℕ} {wt : Fin n → ℂ}
    (hdim : Module.finrank ℂ (VOA.A W) ≤ n) (ht : CharTable W n wt)
    {M : Type} [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M) {h : ℂ}
    (hlow : IsLowestWeight N h) (hne : N.weight h ≠ ⊥) : ∃ i, h = wt i := by
  letI := instRingA W
  letI := instAlgebraA W
  letI := finiteDimensional_A_of_C2Cofinite W hC2
  obtain ⟨χ, hχ, hω⟩ := ht
  let e := characterAlgEquiv χ hχ (by simpa using hdim)
  let ρ := ZhuPolynomialSimplicity.actAAlgHom W N hlow
  let ε : Fin n → VOA.A W := fun i => e.symm (Pi.single i 1)
  have hsum : ∑ i, ε i = 1 := by
    apply e.injective
    rw [map_sum, map_one]
    simp only [ε, AlgEquiv.apply_symm_apply]
    exact Finset.univ_sum_single 1
  have hmul : ∀ a i, a * ε i = χ i a • ε i := by
    intro a i
    apply e.injective
    rw [map_mul, map_smul]
    simp only [ε, AlgEquiv.apply_symm_apply]
    ext j
    by_cases hj : j = i
    · subst hj
      simp [e, characterAlgEquiv, characterEvaluation]
    · simp [hj]
  obtain ⟨x, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  set y : N.weight h := ⟨x, hx0.1⟩
  have hy0 : y ≠ 0 := fun hz => hx0.2 (congrArg Subtype.val hz)
  have hex : ∃ i, ρ (ε i) y ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hy0
    have h1 : ρ 1 y = y := by rw [map_one]; rfl
    rw [← h1, ← hsum, map_sum, LinearMap.coe_sum, Finset.sum_apply]
    exact Finset.sum_eq_zero fun i _ => hall i
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, ?_⟩
  set z := ρ (ε i) y
  have h1 : ρ (VOA.mk W W.conformalVector) z = h • z := by
    apply Subtype.ext
    change ((actA N hlow (VOA.mk W W.conformalVector) z : N.weight h) : M) = h • (z : M)
    rw [actA_mk_apply_coe, oMod_homogeneous _ W.conformalVector_mem_grading_two]
    exact N.L0_weight _ _ z.property
  have h2 : ρ (VOA.mk W W.conformalVector) z = χ i (VOA.mk W W.conformalVector) • z := by
    change ρ (VOA.mk W W.conformalVector) (ρ (ε i) y) = _
    rw [← Module.End.mul_apply, ← map_mul, hmul, map_smul]
    rfl
  rw [← hω i]
  exact smul_left_injective ℂ hi (h1.symm.trans h2)

set_option maxHeartbeats 1200000 in
-- Nested mode algebras and quotient transport (as in `lowestWeightValue_of_factorBottom`).
/-- Generic table coverage: if every ordinary lowest weight satisfies `S`, so does every
intrinsic factor bottom of every weak module (arbitrary subquotients). -/
theorem factorBottom_mem_of_table (hC2 : C2Cofinite W) (S : ℂ → Prop)
    (hS : ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (O : OrdVModule W X) (h : ℂ),
      IsLowestWeight O h → O.weight h ≠ ⊥ → S h)
    {M : Type} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M)
    (a b : Submodule (modeAlg A) M) (hab : a ≤ b) (h : ℂ)
    (hb : FactorBottom A a b h) : S h := by
  have hwhole : ∀ {Y : Type} [AddCommGroup Y] [Module ℂ Y] (B : WeakModule W Y) (k : ℂ),
      FactorBottom B ⊥ ⊤ k → S k := by
    intro Y _ _ B k hk
    obtain ⟨X, i1, i2, O, hlo, hne⟩ := ordinary_witness_of_factorBottom hC2 B k hk
    exact @hS X i1 i2 O k hlo hne
  let C : WeakModule W b := WeakModule.submodule A (ofR A b)
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
    apply (factorBottom_modeMap_iff hC2 ι a' ⊤ (by rw [hk]; exact bot_le) h).mp
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
  apply hwhole Q h
  have ht := (factorBottom_modeMap_iff hC2 π a' ⊤ (by rw [hker]) h).mpr hb'
  rwa [hzero, htop] at ht

/-- Every factor bottom is a table weight. -/
theorem factorBottom_eq_wt (hC2 : C2Cofinite W) {n : ℕ} {wt : Fin n → ℂ}
    (hdim : Module.finrank ℂ (VOA.A W) ≤ n) (ht : CharTable W n wt)
    {M : Type} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M)
    (a b : Submodule (modeAlg A) M) (hab : a ≤ b) (h : ℂ)
    (hb : FactorBottom A a b h) : ∃ i, h = wt i :=
  factorBottom_mem_of_table hC2 (fun h => ∃ i, h = wt i)
    (fun _ _ _ O _ hlow hne => exists_eq_wt_of_charTable hC2 hdim ht O hlow hne) A a b hab h hb

/-- Rationality from a character table and pairwise splitting for the resonant table pairs:
it suffices to split, for each pair of table weights `(wt i, wt j)` with `wt j - wt i` a nonzero
integer, EITHER orientation (supplied by `hpair`, which may choose). -/
theorem admissiblyRational_of_charTable_pairs (hC2 : C2Cofinite W) {n : ℕ} {wt : Fin n → ℂ}
    (hdim : Module.finrank ℂ (VOA.A W) ≤ n) (ht : CharTable W n wt)
    (hpair : ∀ i j : Fin n, ∀ z : ℤ, z ≠ 0 → wt j = wt i + z →
      PlusRat2Dual.PairSplit W (wt i) (wt j) ∨ PlusRat2Dual.PairSplit W (wt j) (wt i)) :
    AdmissiblyRational W := by
  apply OrbRat.admissiblyRational_of_resonantWholeSplitting hC2
    (isSemisimpleRing_of_charTable hC2 hdim ht)
  intro X _ _ B P h k hP hQ hb hk ⟨z, hz, hkz⟩
  obtain ⟨i, rfl⟩ := factorBottom_eq_wt hC2 hdim ht B ⊥ P bot_le h hb
  obtain ⟨j, rfl⟩ := factorBottom_eq_wt hC2 hdim ht B P ⊤ le_top k hk
  have hne : wt i ≠ wt j := by
    intro he
    apply hz
    have : ((z : ℤ) : ℂ) = 0 := by rw [he] at hkz; linear_combination -hkz
    exact_mod_cast this
  rcases hpair i j z hz hkz with hs | hs
  · exact hs B P hP hQ hb hk
  · exact PlusRat2Dual.pairSplit_swap hC2 hne hs B P hP hQ hb hk

end Generic

end VOA.Classification.COne.OrbRat2
