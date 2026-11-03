import VOA.Classification.COne.C2LevelFinite
import VOA.Classification.COne.C2WindowDetectsZhuSpectrum

/-!
# Moving a finite-dimensional weak-subquotient detector into an admissible window

This file does not prove the C₂ detector theorem. It proves that an arbitrary
finite-dimensional detecting subspace suffices, even if that subspace and the
weak submodules being detected are not graded for the admissible levels.
In particular a detector constructed using generalized conformal weights can be
used without identifying those weights with admissible levels.

## Truth assessment and remaining mathematical bridge

The original window proposition is consistent with the standard C₂ theorem and
is true by the generalized-weight argument: split the homogeneous generator into
its finitely many generalized `L(0)` weights. The conformal commutator shifts
those weights by the same integer as the admissible degree. Level finiteness
then gives finite-dimensional generalized weight spaces and only finitely many
weights below any real bound. Weak submodules are graded for these generalized
weights. A nonzero subquotient has a nonzero component below a uniform bound on
simple lowest conformal weights (Huang, arXiv:0712.4109, Proposition 3.15).
Thus the sum of those low generalized weight spaces detects all subquotients;
`exists_le_cyclicWindow` places this finite-dimensional subspace in a window.

The generalized-weight decomposition, its compatibility with weak subquotients,
and the lowest-weight argument in the preceding paragraph are NOT formalized
here. `C2WindowDetectsZhuSpectrum` supplies the uniform spectral bound for actual
Zhu representations, but the construction of the requisite Zhu bottom
representations for these subquotients is still required. Consequently neither
the original detector proposition nor unconditional cyclic finite length is
claimed as a Lean theorem in this file.

Local finiteness of `L(0)` alone does not imply admissible-level gradedness:
for the trivial VOA, put two copies of its trivial module in levels 0 and 1.
Here `L(0)=0`, yet the diagonal weak submodule is not level-graded. This is a
counterexample to that proposed shortcut, not to the homogeneous-cyclic window
proposition. No step below uses that shortcut.
-/

namespace VOA.Classification.COne.C2WindowDetects

open PlusRational PlusFiniteLength FiniteLengthAlgebra C2LevelFinite
open VOA.Huang.BuhlSpanning

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

theorem cyclicWindow_mono (N : AdmissibleModule W M) (x : M) :
    Monotone (cyclicWindow N x) := by
  intro a b hab
  apply iSup_le
  intro j
  exact le_iSup_of_le ⟨j.val, by omega⟩ le_rfl

theorem cyclicLevel_le_window (N : AdmissibleModule W M) (x : M) (j : ℤ) :
    cyclicLevel N x j ≤ cyclicWindow N x j.toNat := by
  by_cases hj : 0 ≤ j
  · have he : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj
    exact le_iSup_of_le ⟨j.toNat, by omega⟩ (by simp only [he]; exact le_rfl)
  · intro y hy
    have hz : (y : M) = 0 := by
      have : (y : M) ∈ N.lev j := hy
      rw [N.lev_eq_bot_of_neg j (by omega)] at this
      exact this
    have : y = 0 := Subtype.ext hz
    rw [this]
    exact Submodule.zero_mem _

/-- The windows exhaust a homogeneous cyclic module. No gradedness claim about
its arbitrary mode submodules is made. -/
theorem iSup_cyclicWindow_eq_top (W : VertexOperatorAlgebra 𝒱) (hC2 : C2Cofinite W)
    (N : AdmissibleModule W M) (k : ℤ) (x : M) (hx : x ∈ N.lev k) :
    (⨆ b : ℕ, cyclicWindow N x b) = ⊤ := by
  classical
  obtain ⟨D⟩ := exists_genData hC2
  obtain ⟨N₀, hN₀⟩ := exists_grading_le_O₂ W hC2
  let Bm := k.toNat + Finset.univ.sup D.wt
  have hBm : ∀ i, k + (D.wt i : ℤ) ≤ Bm := by
    intro i
    have := Finset.le_sup (f := D.wt) (Finset.mem_univ i)
    dsimp [Bm]
    omega
  let C := cyclic N.toWeakModule x
  let S := ⨆ b : ℕ, cyclicWindow N x b
  let f : C →ₗ[ℂ] M := C.subtype.restrictScalars ℂ
  have hword : ∀ l : List (Ltr D), wordL D N.toWeakModule l x ∈ C := by
    intro l
    induction l with
    | nil => exact Submodule.mem_span_singleton_self x
    | cons a l ih =>
      exact C.smul_mem
        (⟨mode (N.YM (D.gen a.1)) a.2, Algebra.subset_adjoin ⟨_, _, rfl⟩⟩ :
          modeAlg N.toWeakModule) ih
  have hle : C.restrictScalars ℂ ≤ S.map f := by
    apply le_trans (cyclic_le_boundedNormalSpan D N hN₀ hx hBm)
    apply Submodule.span_le.mpr
    rintro _ ⟨l, _, _, rfl⟩
    let y : C := ⟨wordL D N.toWeakModule l x, hword l⟩
    refine ⟨y, ?_, rfl⟩
    exact Submodule.mem_iSup_of_mem (k + degree D l).toNat
      (cyclicLevel_le_window N x _ (wordL_mem_level D N hx l))
  apply top_unique
  intro y _
  obtain ⟨z, hz, he⟩ := hle y.property
  have : z = y := Subtype.ext he
  exact this ▸ hz

/-- Each vector of the cyclic module is in some admissible window. -/
theorem exists_mem_cyclicWindow (W : VertexOperatorAlgebra 𝒱) (hC2 : C2Cofinite W)
    (N : AdmissibleModule W M) (k : ℤ) (x : M) (hx : x ∈ N.lev k)
    (y : cyclic N.toWeakModule x) : ∃ b, y ∈ cyclicWindow N x b := by
  apply (Submodule.mem_iSup_of_directed _ (cyclicWindow_mono N x).directed_le).mp
  rw [iSup_cyclicWindow_eq_top W hC2 N k x hx]
  exact Submodule.mem_top

/-- A finite-dimensional subspace, without any invariance or grading hypothesis,
is contained in a single admissible window. -/
theorem exists_le_cyclicWindow (W : VertexOperatorAlgebra 𝒱) (hC2 : C2Cofinite W)
    (N : AdmissibleModule W M) (k : ℤ) (x : M) (hx : x ∈ N.lev k)
    (S : Submodule ℂ (cyclic N.toWeakModule x)) [FiniteDimensional ℂ S] :
    ∃ b, S ≤ cyclicWindow N x b := by
  classical
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional S).mpr inferInstance
  have h : ∀ y : t, ∃ b, y.val ∈ cyclicWindow N x b :=
    fun y => exists_mem_cyclicWindow W hC2 N k x hx y.val
  choose b hb using h
  refine ⟨t.attach.sup b, ?_⟩
  rw [← ht]
  apply Submodule.span_le.mpr
  intro y hy
  exact cyclicWindow_mono N x (Finset.le_sup (f := b) (t.mem_attach ⟨y, hy⟩))
    (hb ⟨y, hy⟩)

/-- Conformal zero mode restricted to the cyclic module. -/
noncomputable def cyclicL0 (N : AdmissibleModule W M) (x : M) :
    Module.End ℂ (cyclic N.toWeakModule x) :=
  Algebra.lsmul ℂ ℂ (cyclic N.toWeakModule x)
    (⟨mode (N.YM W.conformalVector) 1,
      Algebra.subset_adjoin ⟨W.conformalVector, 1, rfl⟩⟩ : modeAlg N.toWeakModule)

/-- The zero mode preserves the windows; it need not act by their level labels. -/
theorem cyclicL0_mem_window (N : AdmissibleModule W M) (x : M) (b : ℕ) :
    ∀ y ∈ cyclicWindow N x b, cyclicL0 N x y ∈ cyclicWindow N x b := by
  change cyclicWindow N x b ≤ (cyclicWindow N x b).comap (cyclicL0 N x)
  apply iSup_le
  intro j y hy
  apply Submodule.mem_iSup_of_mem j
  change mode (N.YM W.conformalVector) 1 (y : M) ∈ N.lev (j.val : ℤ)
  simpa using N.act_lev (p := 1) W.conformal_mem
    (show (y : M) ∈ N.lev (j.val : ℤ) from hy)

/-- Local finiteness of `L(0)` on a homogeneous cyclic module, stated as a
finite-dimensional invariant subspace through each vector. This does not assert
that arbitrary mode submodules are graded for the admissible levels. -/
theorem cyclicL0_locally_finite (W : VertexOperatorAlgebra 𝒱) (hC2 : C2Cofinite W)
    (N : AdmissibleModule W M) (k : ℤ) (x : M) (hx : x ∈ N.lev k)
    (y : cyclic N.toWeakModule x) :
    ∃ S : Submodule ℂ (cyclic N.toWeakModule x),
      FiniteDimensional ℂ S ∧ y ∈ S ∧ ∀ z ∈ S, cyclicL0 N x z ∈ S := by
  obtain ⟨b, hb⟩ := exists_mem_cyclicWindow W hC2 N k x hx y
  exact ⟨cyclicWindow N x b,
    finiteDimensional_cyclicWindow N x b (finiteDimensional_cyclicLevel W hC2 N k x hx),
    hb, cyclicL0_mem_window N x b⟩

/-- Detection is monotone in the detecting complex subspace. -/
theorem detectsSubquotients_mono
    {K R A : Type*} [Field K] [Ring R] [AddCommGroup A] [Module R A] [Module K A]
    {S T : Submodule K A} (hST : S ≤ T) (hS : DetectsSubquotients (R := R) S) :
    DetectsSubquotients (R := R) T := by
  intro P Q hPQ
  obtain ⟨y, hy, hyQ, hyP⟩ := hS P Q hPQ
  exact ⟨y, hST hy, hyQ, hyP⟩

/-- Exact reformulation: the detecting subspace may be constructed using another
grading, or without a grading. All weak subquotients still have to be detected. -/
theorem windowDetects_iff_finiteDimensional_detector
    (W : VertexOperatorAlgebra 𝒱) (hC2 : C2Cofinite W)
    (N : AdmissibleModule W M) (k : ℤ) (x : M) (hx : x ∈ N.lev k) :
    (∃ b, DetectsSubquotients (R := modeAlg N.toWeakModule) (cyclicWindow N x b)) ↔
      ∃ S : Submodule ℂ (cyclic N.toWeakModule x),
        FiniteDimensional ℂ S ∧ DetectsSubquotients (R := modeAlg N.toWeakModule) S := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨cyclicWindow N x b,
      finiteDimensional_cyclicWindow N x b (finiteDimensional_cyclicLevel W hC2 N k x hx), hb⟩
  · rintro ⟨S, hfd, hS⟩
    letI := hfd
    obtain ⟨b, hb⟩ := exists_le_cyclicWindow W hC2 N k x hx S
    exact ⟨b, detectsSubquotients_mono hb hS⟩

end VOA.Classification.COne.C2WindowDetects

namespace VOA.Classification.COne

open PlusRational FiniteLengthAlgebra C2WindowDetects

/-- OPEN: the generalized conformal-weight argument must supply a finite-dimensional
subspace detecting all weak subquotients. This is equivalent to the original
window problem, not a claim that C₂-cofiniteness already supplies that subspace. -/
def C2HomogeneousCyclicFiniteDetector : Prop :=
  ∀ {𝒱 : Type} [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱),
    C2Cofinite W → ∀ {M : Type} [AddCommGroup M] [Module ℂ M]
      (N : AdmissibleModule W M) (k : ℤ) (x : M), x ∈ N.lev k →
        ∃ S : Submodule ℂ (cyclic N.toWeakModule x),
          FiniteDimensional ℂ S ∧ DetectsSubquotients (R := modeAlg N.toWeakModule) S

theorem c2HomogeneousCyclicWindowDetects_iff_finiteDetector :
    C2HomogeneousCyclicWindowDetects ↔ C2HomogeneousCyclicFiniteDetector := by
  constructor <;> intro h 𝒱 _ _ W hC2 M _ _ N k x hx
  · exact (windowDetects_iff_finiteDimensional_detector W hC2 N k x hx).mp
      (h W hC2 N k x hx)
  · exact (windowDetects_iff_finiteDimensional_detector W hC2 N k x hx).mpr
      (h W hC2 N k x hx)

theorem v2mPlusCyclicFiniteLengthFactGe2_of_finiteDetector
    (h : C2HomogeneousCyclicFiniteDetector) : V2mPlusCyclicFiniteLengthFactGe2 :=
  v2mPlusCyclicFiniteLengthFactGe2_of_windowDetects
    (c2HomogeneousCyclicWindowDetects_iff_finiteDetector.mpr h)

end VOA.Classification.COne
