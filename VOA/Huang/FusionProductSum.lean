import VOA.Huang.FusionProductBasic

/-! # Finite sums of ordinary modules

A finite dependent product is the coordinate model of the finite direct sum.
The action is componentwise and the grading is the actual L(0) eigenspace.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

noncomputable section
namespace VOA.Huang.FusionProduct
open VOA
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {ι : Type u} [Fintype ι] {E : ι → Type u}
  [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]

private theorem support_pi {J : Type*} (f : J → ∀ i, E i)
    (hf : ∀ i, (Function.support (fun j => f j i)).Finite) :
    (Function.support f).Finite := by
  apply (Set.finite_iUnion hf).subset
  intro j hj
  by_contra h
  apply hj
  funext i
  have hi : j ∉ Function.support (fun j => f j i) := fun hi => h (Set.mem_iUnion.mpr ⟨i, hi⟩)
  simpa only [Function.mem_support, not_not] using hi

private theorem finsum_pi {J : Type*} (f : J → ∀ i, E i)
    (hf : ∀ i, (Function.support (fun j => f j i)).Finite) (i : ι) :
    (∑ᶠ j, f j) i = ∑ᶠ j, f j i := map_finsum (LinearMap.proj i : (∀ i, E i) →ₗ[ℂ] E i) (support_pi f hf)

/-- The finite sum field map. -/
def sumYM (A : ∀ i, WeakModule W (E i)) : V →ₗ[ℂ] (Module.End ℂ (∀ i, E i))⟦z^±⟧ where
  toFun a := fun p => LinearMap.pi fun i => ((A i).YM a p).comp (LinearMap.proj i)
  map_add' a b := by ext p x i; exact congrArg (fun f => f p (x i)) ((A i).YM.map_add a b)
  map_smul' c a := by ext p x i; exact congrArg (fun f => f p (x i)) ((A i).YM.map_smul c a)

@[simp] theorem sumYM_mode (A : ∀ i, WeakModule W (E i)) (a : V) (n : ℤ)
    (x : ∀ i, E i) (i : ι) : mode (sumYM A a) n x i = mode ((A i).YM a) n (x i) := rfl

/-- The ordinary finite sum first as a weak module. -/
def sumWeak (A : ∀ i, WeakModule W (E i)) : WeakModule W (∀ i, E i) where
  YM := sumYM A
  vacuum_YM := by
    apply FormalDist.ext
    intro p
    ext x i
    change (A i).YM W.vacuum p (x i) = (1 : (Module.End ℂ (∀ i, E i))⟦z^±⟧) p x i
    rw [(A i).vacuum_YM]
    by_cases hp : p = 0
    · subst p; simp
    · simp [hp]
  truncation a x := by
    choose N hN using fun i => (A i).truncation a (x i)
    obtain ⟨B, hB⟩ := Finite.exists_le N
    exact ⟨B, fun n hn => funext fun i => hN i n ((hB i).trans hn)⟩
  jacobi a b x l m n := by
    have hL (i : ι) : (Function.support fun j : ℤ =>
        (negOnePow j * cbz l j) •
          (mode ((A i).YM a) (l+m-j) (mode ((A i).YM b) (n+j) (x i)) -
          negOnePow l • mode ((A i).YM b) (l+n-j) (mode ((A i).YM a) (m+j) (x i)))).Finite := by
      obtain ⟨Nb, hb⟩ := (A i).truncation b (x i)
      obtain ⟨Na, ha⟩ := (A i).truncation a (x i)
      apply (Set.finite_Ico 0 (max (Nb-n) (Na-m))).subset
      intro j hj
      by_contra hh
      apply hj
      by_cases hj0 : j < 0
      · simp [cbz_apply_neg l hj0]
      · have hjN : max (Nb-n) (Na-m) ≤ j := by simp only [Set.mem_Ico] at hh; omega
        dsimp only
        rw [hb (n+j) (by omega), ha (m+j) (by omega)]
        simp
    have hR (i : ι) : (Function.support fun j : ℤ =>
        cbz m j • mode ((A i).YM (W.smul a (l+j) b)) (m+n-j) (x i)).Finite := by
      obtain ⟨B, hB⟩ := (adjointModule W).truncation a b
      apply (Set.finite_Ico 0 (B-l)).subset
      intro j hj
      by_contra hh
      apply hj
      by_cases hj0 : j < 0
      · simp [cbz_apply_neg m hj0]
      · have hjB : B ≤ l+j := by simp only [Set.mem_Ico] at hh; omega
        dsimp only
        change cbz m j • mode ((A i).YM (mode ((adjointModule W).YM a) (l+j) b)) (m+n-j) (x i) = 0
        rw [hB _ hjB]; simp
    funext i
    exact (finsum_pi _ hL i).trans (((A i).jacobi a b (x i) l m n).trans (finsum_pi _ hR i).symm)
    /- componentwise Jacobi -/


/-- Weight spaces in the finite sum. -/
def sumWeight (A : ∀ i, OrdVModule W (E i)) (α : ℂ) : Submodule ℂ (∀ i, E i) :=
  Submodule.pi Set.univ (fun i => (A i).weight α)

@[simp] theorem mem_sumWeight (A : ∀ i, OrdVModule W (E i)) (α : ℂ) (x : ∀ i, E i) :
    x ∈ sumWeight A α ↔ ∀ i, x i ∈ (A i).weight α := by simp [sumWeight, Submodule.mem_pi]

theorem sumWeight_eq_eigenspace (A : ∀ i, OrdVModule W (E i)) (α : ℂ) :
    sumWeight A α = (mode (sumYM (fun i => (A i).toWeakModule) W.conformalVector) 1).eigenspace α := by
  ext x
  rw [mem_sumWeight, Module.End.mem_eigenspace_iff]
  constructor
  · intro hx; funext i; exact (A i).L0_weight α (x i) (hx i)
  · intro hx i; apply eigenvector_mem_weight (A i)
    exact congrFun hx i

theorem sumWeight_isInternal (A : ∀ i, OrdVModule W (E i)) :
    DirectSum.IsInternal (sumWeight A) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · have he : sumWeight A = (mode (sumYM (fun i => (A i).toWeakModule) W.conformalVector) 1).eigenspace := funext (sumWeight_eq_eigenspace A)
    rw [he]
    exact Module.End.eigenspaces_iSupIndep _
  · apply top_unique
    intro x _
    have hs (i : ι) (y : E i) : Pi.single i y ∈ ⨆ α, sumWeight A α := by
      have hy : y ∈ ⨆ α, (A i).weight α := by rw [(A i).isInternal.submodule_iSup_eq_top]; trivial
      refine Submodule.iSup_induction (fun α => (A i).weight α) (motive := fun z => Pi.single i z ∈ ⨆ α, sumWeight A α) hy ?_ ?_ ?_
      · intro α y hy
        apply Submodule.mem_iSup_of_mem α
        rw [mem_sumWeight]
        intro j
        by_cases hj : j = i
        · subst j; simpa using hy
        · simp [Pi.single_eq_of_ne hj]
      · simp
      · intro y z hy hz
        simpa only [Pi.single_add] using (⨆ α, sumWeight A α).add_mem hy hz
    have he : x = ∑ i, Pi.single i (x i) := by
      funext j
      simp only [Finset.sum_apply, Finset.sum_pi_single, Finset.mem_univ, if_true]
    rw [he]
    exact Submodule.sum_mem _ fun i _ => hs i (x i)

/-- Finite sums of ordinary modules are ordinary, with no rationality hypothesis. -/
def sumOrd (A : ∀ i, OrdVModule W (E i)) : OrdVModule W (∀ i, E i) where
  toWeakModule := sumWeak (fun i => (A i).toWeakModule)
  weight := sumWeight A
  isInternal := sumWeight_isInternal A
  L0_weight α x hx := funext fun i => (A i).L0_weight α (x i) ((mem_sumWeight A α x).mp hx i)
  finrank α := by
    letI (i : ι) := (A i).finrank α
    let f : sumWeight A α →ₗ[ℂ] (∀ i, (A i).weight α) :=
      { toFun x := fun i => ⟨x.val i, (mem_sumWeight A α x.val).mp x.property i⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact Module.Finite.of_injective f (fun x y h => Subtype.ext (funext fun i =>
      congrArg Subtype.val (congrFun h i)))
  boundedBelow := by
    choose B hB using fun i => (A i).boundedBelow
    obtain ⟨b, hb⟩ := Finite.exists_ge B
    refine ⟨b, fun α hα => ?_⟩
    have hi : ∃ i, (A i).weight α ≠ ⊥ := by
      by_contra h
      push Not at h
      apply hα
      ext x
      simp [mem_sumWeight, h, funext_iff]
    obtain ⟨i, hi⟩ := hi
    exact (hb i).trans (hB i α hi)

/-- Coordinate projection as a module homomorphism. -/
def sumProjection (A : ∀ i, OrdVModule W (E i)) (i : ι) :
    FusionUnit.homSpace (sumOrd A) (A i) :=
  ⟨LinearMap.proj i, fun _ _ _ => rfl⟩

/-- Coordinate inclusion as a module homomorphism. -/
def sumInclusion (A : ∀ i, OrdVModule W (E i)) (i : ι) :
    FusionUnit.homSpace (A i) (sumOrd A) := by
  classical
  refine ⟨LinearMap.single ℂ E i, ?_⟩
  intro a n x
  funext j
  change Pi.single i (mode ((A i).YM a) n x) j = mode ((A j).YM a) n (Pi.single i x j)
  by_cases hj : j = i
  · subst j; simp
  · simp [Pi.single_eq_of_ne hj]

variable {M₁ M₂ : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂]
  {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂}

/-- The intertwiner with the specified finite family of coordinates. -/
def sumIntertwiner (A : ∀ i, OrdVModule W (E i))
    (Y : ∀ i, IntertwiningOperator A₁ A₂ (A i)) :
    IntertwiningOperator A₁ A₂ (sumOrd A) :=
  ∑ i, postcompose (Y i) (sumOrd A) (sumInclusion A i)

@[simp] theorem sumIntertwiner_apply (A : ∀ i, OrdVModule W (E i))
    (Y : ∀ i, IntertwiningOperator A₁ A₂ (A i))
    (n : ℂ) (x : M₁) (y : M₂) (i : ι) :
    (sumIntertwiner A Y).val n x y i = (Y i).val n x y := by
  classical
  simp only [sumIntertwiner, AddSubmonoidClass.coe_finsetSum]
  simp only [Finset.sum_apply, LinearMap.sum_apply, postcompose_apply]
  change (∑ j, Pi.single j ((Y j).val n x y) i) = _
  simp [Finset.sum_pi_single]

end VOA.Huang.FusionProduct
