import VOA.Classification.COne.PlusSplitCosets

/-!
# Intrinsic bottoms of strict mode subquotients

Bottoms are detected by generalized conformal weights modulo the lower
submodule, so there is no hidden ordinary-extension or admissible-grading
assumption. C₂-cofiniteness supplies the finite union of natural-number rays.
-/
set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.PlusSplitting
open PlusRational ABDWeakAdmissible VOA.Huang.LogRemovalAdmissible
universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- A generalized weight survives in the factor `b/a`. -/
def FactorWeight (A : WeakModule W M) (a b : Submodule (modeAlg A) M) (h : ℂ) : Prop :=
  ¬b.restrictScalars ℂ ⊓ (L0 A).maxGenEigenspace h ≤ a.restrictScalars ℂ

/-- A nonzero least-real-part generalized weight of the factor.
For a simple factor its support is in this weight's integer coset. -/
def FactorBottom (A : WeakModule W M) (a b : Submodule (modeAlg A) M) (h : ℂ) : Prop :=
  FactorWeight A a b h ∧ ∀ k, FactorWeight A a b k → h.re ≤ k.re

/-- A subset of finitely many natural-number rays has a least real part. -/
theorem exists_min_re_of_finite_rays (s : Finset ℂ) (P : ℂ → Prop)
    (hne : ∃ h, P h) (hs : ∀ h, P h → ∃ μ ∈ s, ∃ n : ℕ, h = μ + n) :
    ∃ h, P h ∧ ∀ k, P k → h.re ≤ k.re := by
  classical
  induction s using Finset.induction_on generalizing P with
  | empty =>
    obtain ⟨h, hh⟩ := hne
    simpa using hs h hh
  | @insert μ s hμ ih =>
    by_cases hr : ∃ n : ℕ, P (μ + n)
    · let n := Nat.find hr
      have hn : P (μ + n) := Nat.find_spec hr
      have hmin : ∀ j : ℕ, P (μ + j) → (μ + n).re ≤ (μ + j).re := by
        intro j hj
        have hjn : n ≤ j := Nat.find_min' hr hj
        simp only [Complex.add_re, Complex.natCast_re]
        exact add_le_add_right (show (n : ℝ) ≤ (j : ℝ) by exact_mod_cast hjn) _
      by_cases hrest : ∃ h, P h ∧ ∃ ν ∈ s, ∃ j : ℕ, h = ν + j
      · obtain ⟨h, hh, hleast⟩ := ih (fun h => P h ∧ ∃ ν ∈ s, ∃ j : ℕ, h = ν + j)
          hrest (fun _ hh => hh.2)
        by_cases he : h.re ≤ (μ + n).re
        · refine ⟨h, hh.1, ?_⟩
          intro k hk
          obtain ⟨ν, hν, j, rfl⟩ := hs k hk
          rcases Finset.mem_insert.mp hν with rfl | hν
          · exact he.trans (hmin j hk)
          · exact hleast _ ⟨hk, ν, hν, j, rfl⟩
        · refine ⟨μ + n, hn, ?_⟩
          intro k hk
          obtain ⟨ν, hν, j, rfl⟩ := hs k hk
          rcases Finset.mem_insert.mp hν with rfl | hν
          · exact hmin j hk
          · exact (le_of_not_ge he).trans (hleast _ ⟨hk, ν, hν, j, rfl⟩)
      · refine ⟨μ + n, hn, ?_⟩
        intro k hk
        obtain ⟨ν, hν, j, rfl⟩ := hs k hk
        rcases Finset.mem_insert.mp hν with rfl | hν
        · exact hmin j hk
        · exact (hrest ⟨ν + j, hk, ν, hν, j, rfl⟩).elim
    · apply ih P hne
      intro h hh
      obtain ⟨ν, hν, n, rfl⟩ := hs h hh
      rcases Finset.mem_insert.mp hν with rfl | hν
      · exact (hr ⟨n, hh⟩).elim
      · exact ⟨ν, hν, n, rfl⟩

/-- Every strict subquotient has an intrinsic generalized bottom. -/
theorem exists_factorBottom (hC2 : C2Cofinite W) (A : WeakModule W M)
    {a b : Submodule (modeAlg A) M} (hab : a < b) :
    ∃ h, FactorBottom A a b h := by
  have hne : ∃ h, FactorWeight A a b h := by
    by_contra! h
    apply hab.not_ge
    have hb := eq_iSup_inf_maxGenEigenspace_of_locally_finite (L0 A)
      (weakL0LocallyFinite hC2 A) (b.restrictScalars ℂ)
      (fun y hy => b.smul_mem
        (⟨mode (A.YM W.conformalVector) 1,
          Algebra.subset_adjoin ⟨W.conformalVector, 1, rfl⟩⟩ : modeAlg A) hy)
    have hle : b.restrictScalars ℂ ≤ a.restrictScalars ℂ := by
      rw [hb]
      exact iSup_le (fun μ => not_not.mp (h μ))
    exact hle
  obtain ⟨s, hs⟩ := exists_finite_weak_conformal_spectrum (W := W) hC2
  apply exists_min_re_of_finite_rays s (FactorWeight A a b) hne
  intro h hh
  apply hs A h
  intro he
  apply hh
  rw [he, inf_bot_eq]
  exact bot_le

/-- Any surviving weight in a simple factor generates its coset support.
This is the bridge from intrinsic factor weights to the general coset splitter. -/
theorem factor_le_sup_cosetBlock (A : WeakModule W M)
    {a b : Submodule (modeAlg A) M} (hab : a ⋖ b) {h : ℂ}
    (hh : FactorWeight A a b h) : b ≤ a ⊔ cosetBlock A h := by
  have hbc : a ⊔ (b ⊓ cosetBlock A h) ≤ b := sup_le hab.le inf_le_left
  rcases hab.wcovBy.eq_or_eq le_sup_left hbc with he | he
  · exfalso
    apply hh
    intro x hx
    have hm : x ∈ a ⊔ (b ⊓ cosetBlock A h) :=
      Submodule.mem_sup_right ⟨hx.1, Submodule.mem_iSup_of_mem h
        (Submodule.mem_iSup_of_mem (sameCoset_refl h) hx.2)⟩
    rwa [he] at hm
  · rw [← he]
    exact sup_le le_sup_left (inf_le_right.trans le_sup_right)

/-- The nonintegral lowest-weight case, for any VOA with locally finite L(0).
Only surviving factor weights and strict covers are needed; in particular
ordinary simple factors with different lowest-weight cosets are covered. -/
theorem relativeComplement_of_nonintegral_factorWeights (A : WeakModule W M)
    (hloc : ∀ x : M, ∃ S : Submodule ℂ M, FiniteDimensional ℂ S ∧ x ∈ S ∧
      ∀ y ∈ S, L0 A y ∈ S)
    {a b c : Submodule (modeAlg A) M} (hab : a ⋖ b) (hbc : b ⋖ c)
    {h k : ℂ} (hh : FactorWeight A a b h) (hk : FactorWeight A b c k)
    (hne : ¬SameCoset h k) :
    ∃ d : Submodule (modeAlg A) M,
      a ≤ d ∧ d ≤ c ∧ b ⊓ d = a ∧ b ⊔ d = c :=
  relativeComplement_of_distinct_cosets A hloc hab.le hbc.le h k hne
    (factor_le_sup_cosetBlock A hab hh) (factor_le_sup_cosetBlock A hbc hk)

/-- Every surviving subquotient weight of a one-coset submodule remains in
that coset, without any local finiteness assumption. -/
theorem factorWeight_sameCoset_of_le_block (A : WeakModule W M)
    {a b : Submodule (modeAlg A) M} {α β : ℂ}
    (hb : b ≤ cosetBlock A α) (hβ : FactorWeight A a b β) : SameCoset α β := by
  by_contra hne
  apply hβ
  intro x hx
  have ho : x ∈ otherCosets A α :=
    Submodule.mem_iSup_of_mem β (Submodule.mem_iSup_of_mem hne hx.2)
  have hz := Submodule.disjoint_def.mp (cosetBlock_disjoint_otherCosets A α) x (hb hx.1) ho
  rw [hz]
  exact Submodule.zero_mem _

/-- In the original generalized-generator problem all factor weights lie in
the generator's coset. In particular nonintegral pairs cannot arise there. -/
theorem factorWeight_sameCoset_of_generalized_cyclic (A : WeakModule W M)
    (α : ℂ) (x : M) (hx : x ∈ (L0 A).maxGenEigenspace α)
    {a b : Submodule (modeAlg A) M} (hb : b ≤ cyclic A x)
    {β : ℂ} (hβ : FactorWeight A a b β) : SameCoset α β :=
  factorWeight_sameCoset_of_le_block A (hb.trans (cyclic_le_cosetBlock A α x hx)) hβ

end VOA.Classification.COne.PlusSplitting
