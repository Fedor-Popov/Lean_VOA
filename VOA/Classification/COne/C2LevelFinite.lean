import VOA.Classification.COne.C2LevelFiniteCounting
import VOA.Classification.COne.PlusFiniteLengthReduction

/-!
# Finite-dimensional levels of homogeneous cyclic modules

`VertexOperatorAlgebra` already includes CFT type, and its underlying
`PreVertexAlgebra` has finite-dimensional graded pieces. No rationality or
semisimplicity hypothesis is needed here.

We extend Buhl normal-form spanning from bottom-level seeds to arbitrary
homogeneous seeds, count the words at a fixed level shift, and project onto the
admissible grading. This uses admissible levels, not eigenspaces for `L(0)`.

Sources: Abe--Buhl--Dong, arXiv:math/0204021, Theorem 3.3 (Buhl spanning);
Huang, arXiv:0712.4109, Proposition 3.15 concerns the separate finite-length
step and is not used to identify admissible levels with conformal weight spaces.
-/

namespace VOA.Classification.COne.C2LevelFinite

open VOA.Huang.BuhlSpanning PlusRational PlusFiniteLength

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- A generator word has its declared admissible level shift. -/
theorem wordL_mem_level (D : GenData W) (N : AdmissibleModule W M)
    {k : ℤ} {x : M} (hx : x ∈ N.lev k) (l : List (Ltr D)) :
    wordL D N.toWeakModule l x ∈ N.lev (k + degree D l) := by
  induction l with
  | nil => simpa using hx
  | cons a l ih =>
    have h := N.act_lev (D.gen_mem a.1) ih (p := a.2)
    rw [wordL_cons, degree_cons]
    convert h using 1 <;> congr 1 <;> omega

/-- Projection onto an admissible level, as an endomorphism of the ambient space. -/
noncomputable def levelProjection (N : AdmissibleModule W M) (j : ℤ) : M →ₗ[ℂ] M :=
  (N.lev j).subtype ∘ₗ DirectSum.component ℂ ℤ (fun i => N.lev i) j ∘ₗ
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap N.lev) N.isInternal).symm.toLinearMap

theorem levelProjection_self (N : AdmissibleModule W M) {j : ℤ} {y : M}
    (hy : y ∈ N.lev j) : levelProjection N j y = y := by
  change ((LinearEquiv.ofBijective (DirectSum.coeLinearMap N.lev)
    N.isInternal).symm y j : M) = y
  rw [N.isInternal.ofBijective_coeLinearMap_of_mem hy]

theorem levelProjection_other (N : AdmissibleModule W M) {i j : ℤ} (hij : i ≠ j)
    {y : M} (hy : y ∈ N.lev i) : levelProjection N j y = 0 := by
  change ((LinearEquiv.ofBijective (DirectSum.coeLinearMap N.lev)
    N.isInternal).symm y j : M) = 0
  rw [N.isInternal.ofBijective_coeLinearMap_of_mem_ne hij hy]
  rfl

/-- Cyclic vectors lie in the span of normal words with uniformly bounded upper modes. -/
theorem cyclic_le_boundedNormalSpan (D : GenData W) (N : AdmissibleModule W M)
    {N₀ Bm : ℕ} (hN₀ : ∀ n : ℤ, (N₀ : ℤ) ≤ n → W.grading n ≤ O₂ W)
    {k : ℤ} {x : M} (hx : x ∈ N.lev k)
    (hBm : ∀ i, k + (D.wt i : ℤ) ≤ Bm) :
    (cyclic N.toWeakModule x).restrictScalars ℂ ≤
      Submodule.span ℂ {y | ∃ l : List (Ltr D), Normal D (N₀ + 1) l ∧
        (∀ e ∈ l, e.2 < (Bm : ℤ)) ∧ y = wordL D N.toWeakModule l x} := by
  let B : Submodule ℂ M := Submodule.span ℂ {x}
  have hB : B ≤ N.lev k := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)
  have hcut : ∀ l : List (Ltr D), l.Pairwise (modeLE D) →
      (∃ e ∈ l, (Bm : ℤ) ≤ e.2) → ∀ b ∈ B, wordL D N.toWeakModule l b = 0 :=
    fun l hl hbig b hb => wordL_eq_zero_of_big_level N hBm l hl hbig b (hB hb)
  have hcyc : cyclic N.toWeakModule x ≤
      toR N.toWeakModule (iSupESub (D := D) (A := N.toWeakModule) (B₀ := B)) := by
    apply Submodule.span_le.mpr
    apply Set.singleton_subset_iff.mpr
    exact Submodule.mem_iSup_of_mem 0 (mem_E_zero (Submodule.mem_span_singleton_self x) 0)
  have hnorm : (cyclic N.toWeakModule x).restrictScalars ℂ ≤
      normalSpan D N.toWeakModule B (N₀ + 1) := by
    apply le_trans (show (cyclic N.toWeakModule x).restrictScalars ℂ ≤
      ⨆ G, E D N.toWeakModule B G from hcyc)
    exact iSup_le (fun G => E_le_normalSpan hN₀ hcut G)
  refine le_trans hnorm (Submodule.span_le.mpr ?_)
  rintro _ ⟨l, hl, hn, hb, rfl⟩
  by_cases hbig : ∃ e ∈ l, (Bm : ℤ) ≤ e.2
  · rw [hcut l hn.1 hbig hl hb]
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

/-- Projecting the bounded normal span onto one level leaves only fixed-degree words. -/
theorem cyclic_level_le_fixedDegreeSpan (D : GenData W) (N : AdmissibleModule W M)
    {N₀ Bm : ℕ} (hN₀ : ∀ n : ℤ, (N₀ : ℤ) ≤ n → W.grading n ≤ O₂ W)
    {k : ℤ} {x : M} (hx : x ∈ N.lev k)
    (hBm : ∀ i, k + (D.wt i : ℤ) ≤ Bm) (j : ℤ) {y : M}
    (hy : y ∈ cyclic N.toWeakModule x) (hyj : y ∈ N.lev j) :
    y ∈ Submodule.span ℂ ((fun l => wordL D N.toWeakModule l x) ''
      {l : List (Ltr D) | (∀ a, l.count a < N₀ + 1) ∧
        (∀ e ∈ l, e.2 < (Bm : ℤ)) ∧ degree D l = j - k}) := by
  have hs := cyclic_le_boundedNormalSpan D N hN₀ hx hBm hy
  rw [← levelProjection_self N hyj]
  clear hy hyj
  induction hs using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, hn, hm, rfl⟩ := hz
    by_cases hd : k + degree D l = j
    · rw [levelProjection_self N (hd ▸ wordL_mem_level D N hx l)]
      exact Submodule.subset_span ⟨l, ⟨hn.2, hm, by omega⟩, rfl⟩
    · rw [levelProjection_other N hd (wordL_mem_level D N hx l)]
      exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

/-- Every level intersection of a homogeneous cyclic admissible module is finite-dimensional. -/
theorem finiteDimensional_cyclicLevel (W : VertexOperatorAlgebra 𝒱) (hC2 : C2Cofinite W)
    (N : AdmissibleModule W M) (k : ℤ) (x : M) (hx : x ∈ N.lev k) (j : ℤ) :
    FiniteDimensional ℂ (cyclicLevel N x j) := by
  classical
  obtain ⟨D⟩ := exists_genData hC2
  obtain ⟨N₀, hN₀⟩ := exists_grading_le_O₂ W hC2
  let Bm := k.toNat + Finset.univ.sup D.wt
  have hBm : ∀ i, k + (D.wt i : ℤ) ≤ Bm := by
    intro i
    have h := Finset.le_sup (f := D.wt) (Finset.mem_univ i)
    dsimp [Bm]
    omega
  let T : Set (List (Ltr D)) := {l | (∀ a, l.count a < N₀ + 1) ∧
    (∀ e ∈ l, e.2 < (Bm : ℤ)) ∧ degree D l = j - k}
  let S := Submodule.span ℂ ((fun l => wordL D N.toWeakModule l x) '' T)
  haveI : FiniteDimensional ℂ S :=
    FiniteDimensional.span_of_finite ℂ ((fixedDegreeWords_finite D (N₀ + 1) Bm (j - k)).image _)
  let f : cyclicLevel N x j →ₗ[ℂ] M :=
    ((cyclic N.toWeakModule x).subtype.restrictScalars ℂ).comp (cyclicLevel N x j).subtype
  have hf : ∀ z, f z ∈ S := fun z =>
    cyclic_level_le_fixedDegreeSpan D N hN₀ hx hBm j z.val.property z.property
  apply FiniteDimensional.of_injective (f.codRestrict S hf)
  intro a b h
  have h' : (a.val.val : M) = b.val.val := congrArg (fun z : S => (z : M)) h
  exact Subtype.ext (Subtype.ext h')

end VOA.Classification.COne.C2LevelFinite

namespace VOA.Classification.COne

open PlusFiniteLength PlusRational FiniteLengthAlgebra

/-- The homogeneous cyclic level-finiteness proposition. -/
theorem c2HomogeneousCyclicLevelFinite : C2HomogeneousCyclicLevelFinite := by
  intro 𝒱 _ _ W hC2 M _ _ N k x hx j
  exact C2LevelFinite.finiteDimensional_cyclicLevel W hC2 N k x hx j

/-- The level-finiteness bridge for the lattice fixed-point VOA, for every `m ≥ 1`. -/
theorem v2mPlus_finiteDimensional_cyclicLevel (m : ℕ) (hm : 1 ≤ m)
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : AdmissibleModule (V2mPlus m hm) M) (k : ℤ) (x : M) (hx : x ∈ N.lev k) (j : ℤ) :
    FiniteDimensional ℂ (cyclicLevel N x j) :=
  c2HomogeneousCyclicLevelFinite (V2mPlus m hm) (V2mPlus_c2Cofinite m hm) N k x hx j

/-- With level finiteness proved, only the weak-subquotient detector input remains
in this finite-length route to the lattice fixed-point application. -/
theorem v2mPlusCyclicFiniteLengthFactGe2_of_windowDetects
    (hdet : C2HomogeneousCyclicWindowDetects) : V2mPlusCyclicFiniteLengthFactGe2 :=
  v2mPlusCyclicFiniteLengthFactGe2_of_levelFinite_windowDetects
    c2HomogeneousCyclicLevelFinite hdet

end VOA.Classification.COne
