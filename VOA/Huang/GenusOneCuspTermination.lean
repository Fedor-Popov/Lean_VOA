import VOA.Huang.GenusOneUniformSystem
import VOA.Huang.GenusOneZhuBridge
import Mathlib.RingTheory.Artinian.Module

/-! # Finite termination of successive coefficient subtraction

This is the linear-algebra step in Miyamoto, math/0010180, Lemma 4.13.
The coefficients must belong to a *fixed*, separating expansion model.
Finite dimensionality alone is not asserted to terminate an arbitrary sequence
of increasing exponents. Application to insertion blocks still needs their cusp
expansions and realization at the correct conformal weight.
-/
namespace VOA.Huang.GenusOne.CuspTermination
open scoped BigOperators
variable {E C : Type*} [AddCommGroup E] [Module ℂ E]
  [AddCommGroup C] [Module ℂ C]

/-- The decreasing coefficient filtration, with vector-valued coefficients. -/
def jetKernel (s : E →ₗ[ℂ] (ℕ → C)) (n : ℕ) : Submodule ℂ E where
  carrier := {x | ∀ k < n, s x k = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy k hk; simp [hx k hk, hy k hk]
  smul_mem' := by intro c x hx k hk; simp [hx k hk]

@[simp] theorem mem_jetKernel (s : E →ₗ[ℂ] (ℕ → C)) (n : ℕ) (x : E) :
    x ∈ jetKernel s n ↔ ∀ k < n, s x k = 0 := Iff.rfl

theorem jetKernel_antitone (s : E →ₗ[ℂ] (ℕ → C)) : Antitone (jetKernel s) :=
  fun _ _ h _ hx k hk => hx k (lt_of_lt_of_le hk h)

/-- A separated coefficient expansion on a finite-dimensional space has a
uniform finite determining jet. No finiteness of the coefficient space is needed. -/
theorem exists_finite_determining_jet [FiniteDimensional ℂ E]
    (s : E →ₗ[ℂ] (ℕ → C)) (hs : Function.Injective s) :
    ∃ N : ℕ, ∀ x, (∀ k < N, s x k = 0) → x = 0 := by
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes
    (⟨jetKernel s, jetKernel_antitone s⟩ : ℕ →o (Submodule ℂ E)ᵒᵈ)
  refine ⟨N, fun x hx => ?_⟩
  apply hs
  ext k
  have hm : x ∈ jetKernel s (max N (k + 1)) := by
    change x ∈ jetKernel s N at hx
    have he : jetKernel s N = jetKernel s (max N (k + 1)) :=
      hN _ (le_max_left _ _)
    rwa [← he]
  simpa using hm k (lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_right _ _))

/-- Subtracting a realized coefficient moves the residual into the next jet
kernel; this is the precise increase needed by the termination proof. -/
theorem sub_mem_next_jet (s : E →ₗ[ℂ] (ℕ → C)) {n : ℕ} {x y : E}
    (hx : x ∈ jetKernel s n) (hy : y ∈ jetKernel s n) (he : s x n = s y n) :
    x - y ∈ jetKernel s (n + 1) := by
  intro k hk
  by_cases hkn : k < n
  · simp [hx k hkn, hy k hkn]
  · have hkn' : k = n := by omega
    subst k
    simp [he]

/-- Coefficient-by-coefficient trace realization implies spanning, provided
the expansion is separating and the block space is finite-dimensional. -/
theorem eq_top_of_leading_lifts [FiniteDimensional ℂ E]
    (s : E →ₗ[ℂ] (ℕ → C)) (hs : Function.Injective s) (T : Submodule ℂ E)
    (hlift : ∀ (n : ℕ) (x : E), x ∈ jetKernel s n →
      ∃ y ∈ T, y ∈ jetKernel s n ∧ s x n = s y n) : T = ⊤ := by
  obtain ⟨N, hN⟩ := exists_finite_determining_jet s hs
  apply top_unique
  intro x _
  have happrox (n : ℕ) : ∃ y ∈ T, x - y ∈ jetKernel s n := by
    induction n with
    | zero => exact ⟨0, T.zero_mem, fun k hk => by omega⟩
    | succ n ih =>
      obtain ⟨y, hy, hxy⟩ := ih
      obtain ⟨z, hz, hzlow, hzmatch⟩ := hlift n (x - y) hxy
      refine ⟨y + z, T.add_mem hy hz, ?_⟩
      have h := sub_mem_next_jet s hxy hzlow hzmatch
      simpa only [sub_sub] using h
  obtain ⟨y, hy, hxy⟩ := happrox N
  have he : x = y := sub_eq_zero.mp (hN _ hxy)
  exact he.symm ▸ hy

end VOA.Huang.GenusOne.CuspTermination

namespace VOA.Huang.GenusOne
open VOA
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M} {ι : Type u} [Fintype ι]

/-- The actual trace range, as a subspace of analytic insertion blocks. -/
noncomputable def insertionTraceRange (hC2 : C2Cofinite W) (hA : A.IsIrreducible)
    (P : ι → IrrModule W) (h : ι → ℂ)
    (hcw : ∀ i, HasConformalWeight (P i).isMod (h i)) :
    Submodule ℂ (insertionBlockSpace A) :=
  (LinearMap.range (traceFamilyLinear hC2 hA P h hcw)).comap (insertionBlockSpace A).subtype

/-- The finite subtraction theorem feeds the original interpolation target.
The coefficient map must be the separating cusp model; its construction and
the weight-matched lifts remain explicit hypotheses. -/
theorem insertionTraceInterpolation_of_coefficient_lifts
    (hC2 : C2Cofinite W) (hA : A.IsIrreducible)
    (P : ι → IrrModule W) (h : ι → ℂ)
    (hcw : ∀ i, HasConformalWeight (P i).isMod (h i))
    {C : Type*} [AddCommGroup C] [Module ℂ C]
    (s : insertionBlockSpace A →ₗ[ℂ] (ℕ → C)) (hs : Function.Injective s)
    (hlift : ∀ (n : ℕ) (x : insertionBlockSpace A), x ∈ CuspTermination.jetKernel s n →
      ∃ y ∈ insertionTraceRange hC2 hA P h hcw,
        y ∈ CuspTermination.jetKernel s n ∧ s x n = s y n)
    (U : Finset M) (τ₀ : UpperHalfPlane) : InsertionTraceInterpolation A P h U τ₀ := by
  letI := finiteDimensional_insertionBlockSpace (moduleC2_of_irreducible hC2 hA)
  have htop := CuspTermination.eq_top_of_leading_lifts s hs
    (insertionTraceRange hC2 hA P h hcw) hlift
  apply insertionTraceInterpolation_of_spanning P h
  intro F hF
  let x : insertionBlockSpace A := ⟨insertionRestrict F, ⟨F, hF, rfl⟩⟩
  have hx : x ∈ insertionTraceRange hC2 hA P h hcw := by rw [htop]; trivial
  obtain ⟨Z, hZ⟩ := hx
  refine ⟨Z, fun w τ => ?_⟩
  exact (congrFun (congrFun hZ w) τ).symm

end VOA.Huang.GenusOne
