import VOA.Classification.COne.PlusSplittingLocalFinite
import VOA.Classification.COne.AdmissibleOrdinaryBridge
import Mathlib.Algebra.Order.Floor.Ring

/-!
# From weak conformal spectra to admissibility

The exact citation `VOA.ABDWeakIsAdmissible` is true: ABD Proposition 5.7
(published numbering), Proposition 5.6 of arXiv:math/0204021v1, and Miyamoto
Theorem 2.7, (1) implies (3), concern all weak modules, not only irreducibles.

This file proves the spectral-to-grading implication. It does not prove
conformal local finiteness or a global spectral lower bound from C₂-cofiniteness.
Both residual propositions below are true consequences of the cited theorem.
Cyclic degree bounds alone do not give the global spectral bound: the
finite-dimensional Zhu algebra is needed to bound possible lowest weights.
-/

namespace VOA.Classification.COne.ABDWeakAdmissible

open VOA.Huang.LogRemovalAdmissible

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- A homogeneous mode intertwines the shifted conformal operators. -/
theorem shifted_L0_mode (A : WeakModule W M) {w : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading w) (p : ℤ) (α : ℂ) (x : M) :
    (L0 A - (α + ((w - p - 1 : ℤ) : ℂ)) • 1) (mode (A.YM a) p x) =
      mode (A.YM a) p ((L0 A - α • 1) x) := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    map_sub, map_smul]
  rw [L0_commutator_weak A ha, add_smul]
  have hcast : ((w - p - 1 : ℤ) : ℂ) = (w : ℂ) - p - 1 := by push_cast; rfl
  rw [hcast]
  abel

/-- Generalized eigenvectors are shifted by exactly the integer mode degree. -/
theorem mode_mem_maxGenEigenspace (A : WeakModule W M) {w : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading w) (p : ℤ) {α : ℂ} {x : M}
    (hx : x ∈ (L0 A).maxGenEigenspace α) :
    mode (A.YM a) p x ∈ (L0 A).maxGenEigenspace (α + ((w - p - 1 : ℤ) : ℂ)) := by
  obtain ⟨k, hk⟩ := Module.End.mem_genEigenspace_top.mp hx
  apply Module.End.mem_genEigenspace_top.mpr
  refine ⟨k, ?_⟩
  have hp : ∀ n : ℕ, ∀ y : M,
      ((L0 A - (α + ((w - p - 1 : ℤ) : ℂ)) • 1) ^ n) (mode (A.YM a) p y) =
        mode (A.YM a) p (((L0 A - α • 1) ^ n) y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ', Module.End.mul_apply, ih, shifted_L0_mode A ha]
      rw [pow_succ', Module.End.mul_apply]
  change ((L0 A - (α + ((w - p - 1 : ℤ) : ℂ)) • 1) ^ k) _ = 0
  rw [hp, show ((L0 A - α • 1) ^ k) x = 0 from hk, map_zero]

/-- Coarsen generalized weights using an integer-valued index. -/
noncomputable def spectralLevel (A : WeakModule W M) (index : ℂ → ℤ)
    (j : ℤ) : Submodule ℂ M :=
  ⨆ (α : ℂ) (_ : index α = j), (L0 A).maxGenEigenspace α

/-- Grouping distinct generalized weights into disjoint index fibers preserves independence. -/
theorem spectralLevel_independent (A : WeakModule W M) (index : ℂ → ℤ) :
    iSupIndep (spectralLevel A index) := by
  rw [iSupIndep_def]
  intro j
  have hi := (L0 A).independent_genEigenspace ⊤
  have hd : Disjoint {α : ℂ | index α = j} {α : ℂ | index α ≠ j} := by
    exact Set.disjoint_left.mpr (fun _ h h' => h' h)
  apply (hi.disjoint_biSup_biSup hd).mono_right
  apply iSup_le
  intro k
  apply iSup_le
  intro hkj
  apply iSup_le
  intro α
  apply iSup_le
  intro hα
  exact le_iSup_of_le α (le_iSup_of_le (by simpa [hα] using hkj) le_rfl)

/-- Spectral decomposition and a nonnegative, shift-compatible index give admissibility. -/
noncomputable def admissibleOfSpectralIndex (A : WeakModule W M) (index : ℂ → ℤ)
    (hspan : (⨆ α : ℂ, (L0 A).maxGenEigenspace α) = ⊤)
    (hnonneg : ∀ α, (L0 A).maxGenEigenspace α ≠ ⊥ → 0 ≤ index α)
    (hshift : ∀ (α : ℂ) (d : ℤ), index (α + (d : ℂ)) = index α + d) :
    AdmissibleModule W M where
  toWeakModule := A
  lev := spectralLevel A index
  lev_eq_bot_of_neg := by
    intro j hj
    apply iSup_eq_bot.mpr
    intro α
    apply iSup_eq_bot.mpr
    intro hα
    by_contra hne
    have hh := hnonneg α hne
    omega
  isInternal := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨spectralLevel_independent A index, top_unique ?_⟩
    rw [← hspan]
    apply iSup_le
    intro α
    exact le_iSup_of_le (index α) (le_iSup_of_le α (le_iSup_of_le rfl le_rfl))
  act_lev := by
    intro w p j a ha x hx
    have hle : spectralLevel A index j ≤
        (spectralLevel A index (j + (w - p - 1))).comap (mode (A.YM a) p) := by
      apply iSup_le
      intro α
      apply iSup_le
      intro hα y hy
      have hm := mode_mem_maxGenEigenspace A ha p hy
      exact Submodule.mem_iSup_of_mem (α + ((w - p - 1 : ℤ) : ℂ))
        (Submodule.mem_iSup_of_mem (by rw [hshift, hα]) hm)
    exact hle hx

/-- Local finiteness of conformal action on every weak module: still a residual input. -/
def WeakL0LocallyFinite (W : VertexOperatorAlgebra 𝒱) : Prop :=
  C2Cofinite W → ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M)
    (x : M), ∃ S : Submodule ℂ M, FiniteDimensional ℂ S ∧ x ∈ S ∧
      ∀ y ∈ S, L0 A y ∈ S

/-- A global real lower bound for weak generalized conformal spectra.
This true C₂ consequence is stronger than a separate bound for each cyclic submodule. -/
def WeakSpectrumBoundedBelow (W : VertexOperatorAlgebra 𝒱) : Prop :=
  C2Cofinite W → ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M),
    ∃ b : ℝ, ∀ α : ℂ, (L0 A).maxGenEigenspace α ≠ ⊥ → b ≤ α.re

/-- Local finiteness gives the full generalized-weight decomposition on a weak module. -/
theorem weak_spectral_decomposition (A : WeakModule W M)
    (hloc : ∀ x : M, ∃ S : Submodule ℂ M, FiniteDimensional ℂ S ∧ x ∈ S ∧
      ∀ y ∈ S, L0 A y ∈ S) :
    (⨆ α : ℂ, (L0 A).maxGenEigenspace α) = ⊤ := by
  have h := PlusSplitting.eq_iSup_inf_maxGenEigenspace_of_locally_finite
    (L0 A) hloc ⊤ (fun _ _ => Submodule.mem_top)
  simpa only [top_inf_eq] using h.symm

/-- A bounded-below generalized-weight decomposition supplies the exact original weak action. -/
theorem exists_admissible_of_spectral_bound (A : WeakModule W M)
    (hspan : (⨆ α : ℂ, (L0 A).maxGenEigenspace α) = ⊤)
    (b : ℝ) (hbound : ∀ α : ℂ, (L0 A).maxGenEigenspace α ≠ ⊥ → b ≤ α.re) :
    ∃ N : AdmissibleModule W M, N.toWeakModule = A := by
  let index : ℂ → ℤ := fun α => ⌊α.re - b⌋
  have hn : ∀ α, (L0 A).maxGenEigenspace α ≠ ⊥ → 0 ≤ index α := by
    intro α hα
    exact Int.floor_nonneg.mpr (sub_nonneg.mpr (hbound α hα))
  have hs : ∀ (α : ℂ) (d : ℤ), index (α + (d : ℂ)) = index α + d := by
    intro α d
    dsimp [index]
    rw [add_sub_right_comm, Int.floor_add_intCast]
  exact ⟨admissibleOfSpectralIndex A index hspan hn hs, rfl⟩

/-- Explicit residual reduction to the library citation; no irreducibility is imposed. -/
theorem abdWeakIsAdmissible_of_localFinite_boundedBelow
    (hloc : WeakL0LocallyFinite W) (hbound : WeakSpectrumBoundedBelow W) :
    ABDWeakIsAdmissible W := by
  intro hC2 M _ _ A
  obtain ⟨b, hb⟩ := hbound hC2 A
  exact exists_admissible_of_spectral_bound A
    (weak_spectral_decomposition A (hloc hC2 A)) b hb

/-- The existing admissible local-finiteness theorem proves necessity of the first residual. -/
theorem weakL0LocallyFinite_of_abdWeakIsAdmissible (hABD : ABDWeakIsAdmissible W) :
    WeakL0LocallyFinite W := by
  intro hC2 M _ _ A x
  obtain ⟨N, rfl⟩ := hABD hC2 A
  exact PlusSplitting.admissible_L0_locally_finite W hC2 N x

/-- Associativity with the exact two spectral residuals and the DLM finiteness input. -/
theorem associativityInput_of_spectral_inputs (hV : StronglyRational W)
    (hloc : WeakL0LocallyFinite W) (hbound : WeakSpectrumBoundedBelow W)
    (hFin : DLMFinitelyManyIrredAdmissible W) :
    VOA.Huang.AssocTarget.AssociativityInput W :=
  AdmissibleOrdinary.associativityInput_of_stronglyRational hV
    (abdWeakIsAdmissible_of_localFinite_boundedBelow hloc hbound) hFin

end VOA.Classification.COne.ABDWeakAdmissible
