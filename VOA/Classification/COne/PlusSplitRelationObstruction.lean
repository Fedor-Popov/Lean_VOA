import VOA.Classification.COne.PlusSplitTranslationObstruction
import VOA.Classification.COne.PlusSplitResonantLifts

/-! A general cokernel obstruction for a cyclic quotient, including the
charged pairs. Relations mean all elements of the full mode algebra killing
the quotient generator. No unproved presentation or zero-mode sufficiency is
assumed. Computing this cokernel for charged modules remains open. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusSplitting
open PlusRational
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- Relations satisfied by the quotient class of a chosen lift. -/
def quotientRelations (A : WeakModule W M) (P : Submodule (modeAlg A) M) (x : M) :=
  {r : modeAlg A // r • x ∈ P}

/-- Simultaneous evaluation of every quotient relation. The target is the
complex vector space of functions on the relation set; evaluation is linear. -/
def relationEvaluation (A : WeakModule W M) (P : Submodule (modeAlg A) M) (x : M) :
    M →ₗ[ℂ] (quotientRelations A P x → M) where
  toFun y r := r.val • y
  map_add' y z := by ext r; exact smul_add r.val y z
  map_smul' c y := by ext r; exact smul_comm r.val c y

/-- The class of the relation defects, modulo all corrections in the kernel. -/
def cyclicRelationObstruction (A : WeakModule W M) (P : Submodule (modeAlg A) M) (x : M) :=
  liftObstruction (relationEvaluation A P x) (P.restrictScalars ℂ) x

/-- Vanishing of the simultaneous relation defects produces a disjoint cyclic
lift. This tests all modes and their products, not merely the Zhu zero modes. -/
theorem complement_of_cyclicRelationObstruction (A : WeakModule W M)
    (P : Submodule (modeAlg A) M) (hP : P ⋖ ⊤) (x : M) (hx : x ∉ P)
    (ho : cyclicRelationObstruction A P x = 0) :
    ∃ Q : Submodule (modeAlg A) M, IsCompl P Q := by
  obtain ⟨y, hy, he⟩ := (liftObstruction_eq_zero_iff _ _ _).mp ho
  have hz : x - y ∉ P := by
    intro hm
    exact hx (by simpa using P.add_mem hm hy)
  refine ⟨cyclic A (x - y), isCompl_cyclic_of_disjoint A P hP (x - y) hz ?_⟩
  apply Submodule.disjoint_def.mpr
  intro z hzP hzQ
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hzQ
  have hr : r • x ∈ P := by
    have ht := P.add_mem hzP (P.smul_mem r hy)
    simpa only [smul_sub, sub_add_cancel] using ht
  exact congrFun he (⟨r, hr⟩ : quotientRelations A P x)

/-- A complement solves the relation-correction problem for every lift. -/
theorem cyclicRelationObstruction_eq_zero_of_complement (A : WeakModule W M)
    (P Q : Submodule (modeAlg A) M) (hQ : IsCompl P Q) (x : M) :
    cyclicRelationObstruction A P x = 0 := by
  obtain ⟨y, hy, z, hz, he⟩ :=
    Submodule.mem_sup.mp (hQ.sup_eq_top ▸ (Submodule.mem_top : x ∈ ⊤))
  apply (liftObstruction_eq_zero_iff _ _ _).mpr
  refine ⟨y, hy, ?_⟩
  ext r
  change r.val • (x - y) = 0
  have hrP : r.val • (x - y) ∈ P := by
    rw [smul_sub]
    exact P.sub_mem r.property (P.smul_mem r.val hy)
  have hrQ : r.val • (x - y) ∈ Q := by
    have hxy : x - y = z := by rw [← he, add_sub_cancel_left]
    rw [hxy]
    exact Q.smul_mem r.val hz
  exact Submodule.disjoint_def.mp hQ.disjoint _ hrP hrQ

/-- The exact obstruction for any simple cyclic quotient, without grading,
finiteness, simplicity of the kernel, or model-identification assumptions. -/
theorem complement_iff_cyclicRelationObstruction (A : WeakModule W M)
    (P : Submodule (modeAlg A) M) (hP : P ⋖ ⊤) (x : M) (hx : x ∉ P) :
    (∃ Q : Submodule (modeAlg A) M, IsCompl P Q) ↔
      cyclicRelationObstruction A P x = 0 :=
  ⟨fun ⟨Q, hQ⟩ => cyclicRelationObstruction_eq_zero_of_complement A P Q hQ x,
    complement_of_cyclicRelationObstruction A P hP x hx⟩

end VOA.Classification.COne.PlusSplitting
