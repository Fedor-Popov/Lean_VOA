import VOA.Classification.COne.ABDWeakAdmissibleComplete
import VOA.Classification.COne.C2FiniteLengthAlgebra

/-!
# Finite length of ordinary modules over C₂-cofinite VOAs

The sum of the weight spaces at the finitely many Zhu conformal roots detects
all strict weak subquotients. This includes ungraded mode submodules: ordinary
conformal semisimplicity supplies their weight decomposition.
-/

namespace VOA.Classification.COne.PlusFiniteLength

open PlusRational FiniteLengthAlgebra ABDWeakAdmissible
open VOA.Huang.LogRemovalAdmissible

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- One finite set of weights meets every nonzero ordinary module. -/
theorem exists_finite_ordinary_detecting_weights (hC2 : C2Cofinite W) :
    ∃ s : Finset ℂ, ∀ {X : Type u} [AddCommGroup X] [Module ℂ X]
      (N : OrdVModule W X) [Nontrivial X], ∃ μ ∈ s, N.weight μ ≠ ⊥ := by
  classical
  obtain ⟨s, hs⟩ := exists_finite_ordinary_lowest_spectrum (W := W) hC2
  refine ⟨s, ?_⟩
  intro X _ _ N _
  have hex : ∃ α, N.weight α ≠ ⊥ := by
    by_contra h
    push Not at h
    have ht := N.isInternal.submodule_iSup_eq_top
    exact bot_ne_top ((iSup_eq_bot.mpr h).symm.trans ht)
  obtain ⟨α, hα⟩ := hex
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα
  let P := ofR N.toWeakModule (cyclic N.toWeakModule x)
  let B := WeakModule.submodule N.toWeakModule P
  let z : P.carrier := ⟨x, Submodule.mem_span_singleton_self x⟩
  have hz : L0 B z = α • z := Subtype.ext (N.L0_weight α x hx)
  obtain ⟨O, hO, hzO, hcos⟩ := eigen_cyclic_isOrdinary hC2 B z α hz
    (cyclic_restriction_eq_top N.toWeakModule x)
  have hne : O.weight α ≠ ⊥ := by
    intro h
    rw [h] at hzO
    exact hx0 (congrArg Subtype.val (show z = 0 from hzO))
  obtain ⟨μ, n, hlow, hμ, _⟩ := ordinary_coset_has_lowest O α hne hcos
  refine ⟨μ, hs O μ hlow hμ, ?_⟩
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
  have he : L0 N.toWeakModule (y : X) = μ • (y : X) := by
    have h := O.L0_weight μ y hy
    change L0 O.toWeakModule y = μ • y at h
    rw [hO] at h
    exact congrArg Subtype.val h
  intro hbot
  have hm := eigenvector_mem_weight N he
  rw [hbot] at hm
  exact hy0 (Subtype.ext hm)

/-- Finite sums of ordinary weight spaces. -/
def ordinaryDetector (N : OrdVModule W M) (s : Finset ℂ) : Submodule ℂ M :=
  ⨆ μ ∈ s, N.weight μ

theorem finiteDimensional_ordinaryDetector (N : OrdVModule W M) (s : Finset ℂ) :
    FiniteDimensional ℂ (ordinaryDetector N s) := by
  classical
  haveI := N.finrank
  unfold ordinaryDetector
  rw [← Finset.sup_eq_iSup]
  infer_instance

/-- A uniform set meeting all nonzero ordinary modules detects every weak
subquotient of any given ordinary module. -/
theorem ordinaryDetector_detects (s : Finset ℂ)
    (hs : ∀ {X : Type u} [AddCommGroup X] [Module ℂ X]
      (N : OrdVModule W X) [Nontrivial X], ∃ μ ∈ s, N.weight μ ≠ ⊥)
    (N : OrdVModule W M) :
    DetectsSubquotients (R := modeAlg N.toWeakModule) (ordinaryDetector N s) := by
  classical
  intro P Q hPQ
  let Qw := ofR N.toWeakModule Q
  let O := N.submodule Qw
  let Pw : WeakModule.Submodule' O.toWeakModule :=
    { carrier := (P.restrictScalars ℂ).comap Qw.carrier.subtype
      act_mem := by
        intro a n x hx
        exact P.smul_mem
          (⟨mode (N.YM a) n, Algebra.subset_adjoin ⟨a, n, rfl⟩⟩ :
            modeAlg N.toWeakModule) hx }
  letI : DirectSum.Decomposition O.weight := O.isInternal.chooseDecomposition
  let T := O.quotient Pw (O.submodule_isGraded Pw)
  have hproper : Pw.carrier ≠ ⊤ := by
    intro he
    apply hPQ.not_ge
    intro x hx
    have hm : (⟨x, hx⟩ : Qw.carrier) ∈ Pw.carrier := by
      rw [he]; exact Submodule.mem_top
    exact hm
  letI : Nontrivial (Qw.carrier ⧸ Pw.carrier) :=
    (Submodule.Quotient.nontrivial_iff).mpr hproper
  obtain ⟨μ, hμ, hne⟩ := hs T
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨y, hy, he⟩ := hz
  have hyN : (y : M) ∈ N.weight μ := hy
  refine ⟨y, Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμ hyN),
    y.property, ?_⟩
  intro hyP
  apply hz0
  rw [← he]
  exact (Submodule.Quotient.mk_eq_zero Pw.carrier).mpr hyP

/-- Every ordinary module of a C₂-cofinite VOA has finite composition length
for its actual mode algebra. Neither irreducibility nor rationality is assumed. -/
theorem ordinaryFiniteLength_of_c2Cofinite (hC2 : C2Cofinite W)
    (N : OrdVModule W M) : IsFiniteLength (modeAlg N.toWeakModule) M := by
  obtain ⟨s, hs⟩ := exists_finite_ordinary_detecting_weights hC2
  letI := finiteDimensional_ordinaryDetector N s
  exact finiteLength_of_detectsSubquotients _ (ordinaryDetector_detects s hs N)

end VOA.Classification.COne.PlusFiniteLength
