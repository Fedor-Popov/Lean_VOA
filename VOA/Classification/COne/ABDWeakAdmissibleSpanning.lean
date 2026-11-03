import VOA.Classification.COne.C2LevelFinite

/-!
# Buhl spanning for arbitrary weak cyclic modules

No admissible grading is assumed. Field truncation supplies a uniform upper
mode cutoff on the finite generator family. The existing normal-form theorem
then applies to the span of an arbitrary seed vector.

The degree bounds below concern normal words. They do not assert that the
existing normalization proof preserves degree; that is a separate step needed
for conformal local finiteness.
-/

namespace VOA.Classification.COne.ABDWeakAdmissible

open VOA.Huang.BuhlSpanning C2LevelFinite PlusRational

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- Field truncation is uniform on a finite generator family at one vector. -/
theorem exists_generator_cutoff (D : GenData W) (A : WeakModule W M) (x : M) :
    ∃ Bm : ℕ, ∀ i n, (Bm : ℤ) ≤ n → mode (A.YM (D.gen i)) n x = 0 := by
  classical
  choose b hb using fun i => A.truncation (D.gen i) x
  refine ⟨Finset.univ.sup (fun i => (b i).toNat), ?_⟩
  intro i n hn
  apply hb i n
  have hi := Finset.le_sup (f := fun i => (b i).toNat) (Finset.mem_univ i)
  have hbNat : b i ≤ ((b i).toNat : ℤ) := by omega
  dsimp only at hi
  omega

/-- In a sorted word, a mode above the cutoff forces the innermost action to vanish. -/
theorem sorted_word_eq_zero (D : GenData W) (A : WeakModule W M) (x : M)
    {Bm : ℕ} (hcut : ∀ i n, (Bm : ℤ) ≤ n → mode (A.YM (D.gen i)) n x = 0) :
    ∀ l : List (Ltr D), l.Pairwise (modeLE D) →
      (∃ e ∈ l, (Bm : ℤ) ≤ e.2) → wordL D A l x = 0 := by
  intro l
  induction l with
  | nil => rintro _ ⟨e, he, _⟩; simp at he
  | cons a l ih =>
    intro hp ⟨e, he, hbig⟩
    rw [wordL_cons]
    by_cases htail : ∃ e ∈ l, (Bm : ℤ) ≤ e.2
    · rw [ih hp.of_cons htail, map_zero]
    · push Not at htail
      have hea : e = a := by
        rcases List.mem_cons.mp he with h | h
        · exact h
        · exact absurd hbig (not_le.mpr (htail e h))
      subst a
      have hl : l = [] := by
        cases l with
        | nil => rfl
        | cons a t =>
          have hh := List.rel_of_pairwise_cons hp (List.mem_cons_self ..)
          have ht := htail a (List.mem_cons_self ..)
          simp only [modeLE] at hh
          omega
      subst l
      exact hcut e.1 e.2 hbig

/-- Every cyclic vector lies in the bounded normal span, without a grading on `M`. -/
theorem cyclic_le_boundedNormalSpan (D : GenData W) (A : WeakModule W M)
    {N₀ Bm : ℕ} (hN₀ : ∀ n : ℤ, (N₀ : ℤ) ≤ n → W.grading n ≤ O₂ W)
    (x : M) (hcut : ∀ i n, (Bm : ℤ) ≤ n → mode (A.YM (D.gen i)) n x = 0) :
    (cyclic A x).restrictScalars ℂ ≤
      Submodule.span ℂ {y | ∃ l : List (Ltr D), Normal D (N₀ + 1) l ∧
        (∀ e ∈ l, e.2 < (Bm : ℤ)) ∧ y = wordL D A l x} := by
  let B : Submodule ℂ M := Submodule.span ℂ {x}
  have hcutB : ∀ l : List (Ltr D), l.Pairwise (modeLE D) →
      (∃ e ∈ l, (Bm : ℤ) ≤ e.2) → ∀ b ∈ B, wordL D A l b = 0 := by
    intro l hl hbig b hb
    have hker : B ≤ LinearMap.ker (wordL D A l) := by
      apply Submodule.span_le.mpr
      rw [Set.singleton_subset_iff]
      exact sorted_word_eq_zero D A x hcut l hl hbig
    exact hker hb
  have hcyc : cyclic A x ≤ toR A (iSupESub (D := D) (A := A) (B₀ := B)) := by
    apply Submodule.span_le.mpr
    apply Set.singleton_subset_iff.mpr
    exact Submodule.mem_iSup_of_mem 0 (mem_E_zero (Submodule.mem_span_singleton_self x) 0)
  have hnorm : (cyclic A x).restrictScalars ℂ ≤ normalSpan D A B (N₀ + 1) := by
    apply le_trans (show (cyclic A x).restrictScalars ℂ ≤ ⨆ G, E D A B G from hcyc)
    exact iSup_le (fun G => E_le_normalSpan hN₀ hcutB G)
  refine le_trans hnorm (Submodule.span_le.mpr ?_)
  rintro _ ⟨l, b, hn, hb, rfl⟩
  by_cases hbig : ∃ e ∈ l, (Bm : ℤ) ≤ e.2
  · rw [hcutB l hn.1 hbig b hb]
    exact Submodule.zero_mem _
  push Not at hbig
  induction hb using Submodule.span_induction with
  | mem b hb =>
    have hbx : b = x := Set.mem_singleton_iff.mp hb
    subst b
    exact Submodule.subset_span ⟨l, hn, hbig, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

/-- Uniform lower degree bound for all bounded-repetition, bounded-upper-mode words. -/
theorem exists_degree_lower_bound (D : GenData W) (Q Bm : ℕ) :
    ∃ b : ℤ, ∀ l : List (Ltr D), (∀ a, l.count a < Q) →
      (∀ e ∈ l, e.2 < (Bm : ℤ)) → b ≤ degree D l := by
  classical
  let T := (innerSet_finite D Q Bm).toFinset
  let L := T.sup List.length
  refine ⟨-((Bm : ℤ) * L), ?_⟩
  intro l hc hm
  have hinner : nonnegativePart D l ∈ T := by
    rw [Set.Finite.mem_toFinset]
    constructor
    · intro e he
      have he' := List.mem_filter.mp he
      exact ⟨of_decide_eq_true he'.2, hm e he'.1⟩
    · intro a
      exact lt_of_le_of_lt (List.filter_sublist.count_le a) (hc a)
  have hlen : ((nonnegativePart D l).length : ℤ) ≤ L := by
    exact_mod_cast (Finset.le_sup (f := List.length) hinner)
  have hmul := mul_le_mul_of_nonneg_left hlen (show (0 : ℤ) ≤ Bm by positivity)
  have hcost := negativeCost_le D Bm l hm
  have hpos := negativeCost_nonneg D l
  omega

/-- The degree-`d` bounded normal-word span on an arbitrary weak seed. -/
noncomputable def normalDegreeSpan (D : GenData W) (A : WeakModule W M)
    (x : M) (Q Bm : ℕ) (d : ℤ) : Submodule ℂ M :=
  Submodule.span ℂ ((fun l => wordL D A l x) ''
    {l : List (Ltr D) | Normal D Q l ∧
      (∀ e ∈ l, e.2 < (Bm : ℤ)) ∧ degree D l = d})

/-- Each bounded normal-word degree span is finite-dimensional, even for weak modules. -/
theorem finiteDimensional_normalDegreeSpan (D : GenData W) (A : WeakModule W M)
    (x : M) (Q Bm : ℕ) (d : ℤ) :
    FiniteDimensional ℂ (normalDegreeSpan D A x Q Bm d) := by
  apply FiniteDimensional.span_of_finite
  apply Set.Finite.image
  exact (fixedDegreeWords_finite D Q Bm d).subset (fun _ h => ⟨h.1.2, h.2⟩)

/-- C₂-cofiniteness supplies cyclic spanning by normal words with a lower degree bound.
This is a spanning family, not yet a direct-sum decomposition. -/
theorem weak_cyclic_spanning (hC2 : C2Cofinite W) (A : WeakModule W M) (x : M) :
    ∃ (D : GenData W) (Q Bm : ℕ) (b : ℤ),
      (∀ l : List (Ltr D), Normal D Q l →
        (∀ e ∈ l, e.2 < (Bm : ℤ)) → b ≤ degree D l) ∧
      (cyclic A x).restrictScalars ℂ ≤ ⨆ d : ℤ, normalDegreeSpan D A x Q Bm d := by
  obtain ⟨D⟩ := exists_genData hC2
  obtain ⟨N₀, hN₀⟩ := exists_grading_le_O₂ W hC2
  obtain ⟨Bm, hcut⟩ := exists_generator_cutoff D A x
  obtain ⟨b, hb⟩ := exists_degree_lower_bound D (N₀ + 1) Bm
  refine ⟨D, N₀ + 1, Bm, b, fun l hn hm => hb l hn.2 hm, ?_⟩
  apply le_trans (cyclic_le_boundedNormalSpan D A hN₀ x hcut)
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hn, hm, rfl⟩
  exact Submodule.mem_iSup_of_mem (degree D l) (Submodule.subset_span ⟨l, ⟨hn, hm, rfl⟩, rfl⟩)

end VOA.Classification.COne.ABDWeakAdmissible
