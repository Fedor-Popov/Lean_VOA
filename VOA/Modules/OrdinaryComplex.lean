/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.OrdinaryExact
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Data.Finset.Interval

/-!
# Complexes of ordinary VOA modules

This file gives a deliberately non-categorical API for cochain complexes of ordinary VOA modules.
The terms may have different carrier types.  Differentials are weight-preserving ordinary-module
morphisms, and `d² = 0` is explicit data.

The formal consequences are linear algebra: boundaries lie in cycles, every weight homology is
finite-dimensional, and finite Euler--Poincaré identities hold coefficientwise.  Exactness,
identification of a distinguished homology, and coefficientwise local finiteness remain explicit
inputs.  In particular, this file contains no Felder-resolution or screening exactness claim.
-/

namespace VOA

open scoped BigOperators

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
/-- A bundled ordinary module, used only so that the carrier can vary with the complex degree. -/
structure OrdinaryComplex.Term (W : VertexOperatorAlgebra 𝒱) where
  carrier : Type v
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℂ carrier]
  isMod : OrdVModule W carrier

attribute [instance] OrdinaryComplex.Term.addCommGroup OrdinaryComplex.Term.module

/-- A `ℤ`-indexed cochain complex of ordinary modules with degree-`+1` differentials.
The differential is indexed by its target: `d i : X (i-1) → X i`. -/
structure OrdinaryComplex (W : VertexOperatorAlgebra 𝒱) where
  term : ℤ → OrdinaryComplex.Term.{u, v} W
  d : ∀ (i j : ℤ), j = i + 1 → OrdVModule.Hom (term i).isMod (term j).isMod
  d_sq : ∀ (i : ℤ) (x : (term (i - 1)).carrier),
    (d i (i + 1) rfl).toLinearMap
      ((d (i - 1) i (by omega)).toLinearMap x) = 0

namespace OrdinaryComplex

variable {W : VertexOperatorAlgebra 𝒱}

/-- The carrier in cochain degree `i`. -/
abbrev X (K : OrdinaryComplex W) (i : ℤ) : Type v := (K.term i).carrier

/-- The ordinary module in cochain degree `i`. -/
abbrev obj (K : OrdinaryComplex W) (i : ℤ) : OrdVModule W (K.X i) := (K.term i).isMod

/-- The differential entering degree `i`. -/
def prevD (K : OrdinaryComplex W) (i : ℤ) :
    OrdVModule.Hom (K.obj (i - 1)) (K.obj i) := K.d (i - 1) i (by omega)

/-- The differential leaving degree `i`. -/
def nextD (K : OrdinaryComplex W) (i : ℤ) :
    OrdVModule.Hom (K.obj i) (K.obj (i + 1)) := K.d i (i + 1) rfl

/-- The incoming differential followed by the outgoing one is zero. -/
theorem d_comp_prevD (K : OrdinaryComplex W) (i : ℤ) (x : K.X (i - 1)) :
    (K.nextD i).toLinearMap ((K.prevD i).toLinearMap x) = 0 := by
  exact K.d_sq i x

/-! ## Cycles, boundaries, and weight homology -/

/-- Cycles in conformal weight `α` and cochain degree `i`. -/
def cycles (K : OrdinaryComplex W) (i : ℤ) (α : ℂ) :
    Submodule ℂ ((K.obj i).weight α) :=
  (K.nextD i).gradedKernel α

/-- Boundaries in conformal weight `α` and cochain degree `i`. -/
def boundaries (K : OrdinaryComplex W) (i : ℤ) (α : ℂ) :
    Submodule ℂ ((K.obj i).weight α) :=
  (K.prevD i).gradedRange α

/-- The outgoing range from degree `i`, used in rank-nullity and equal to the boundaries in
degree `i+1`. -/
def outgoing (K : OrdinaryComplex W) (i : ℤ) (α : ℂ) :
    Submodule ℂ ((K.obj (i + 1)).weight α) :=
  (K.nextD i).gradedRange α

/-- Every boundary is a cycle, weight by weight. -/
theorem boundaries_le_cycles (K : OrdinaryComplex W) (i : ℤ) (α : ℂ) :
    K.boundaries i α ≤ K.cycles i α := by
  rintro y ⟨x, rfl⟩
  rw [cycles, OrdVModule.Hom.mem_gradedKernel]
  apply Subtype.ext
  change (K.nextD i).toLinearMap ((K.prevD i).toLinearMap (x : K.X (i - 1))) = 0
  exact K.d_comp_prevD i (x : K.X (i - 1))

/-- Boundaries, regarded as a submodule of cycles. -/
def boundaryInCycles (K : OrdinaryComplex W) (i : ℤ) (α : ℂ) :
    Submodule ℂ (K.cycles i α) :=
  (K.boundaries i α).comap (K.cycles i α).subtype

/-- Weight-`α` homology in cochain degree `i`. -/
abbrev WeightHomology (K : OrdinaryComplex W) (i : ℤ) (α : ℂ) : Type v :=
  (K.cycles i α) ⧸ K.boundaryInCycles i α

/-- Every weight homology is finite-dimensional. -/
theorem weightHomology_finiteDimensional (K : OrdinaryComplex W) (i : ℤ) (α : ℂ) :
    FiniteDimensional ℂ (K.WeightHomology i α) := by
  letI := (K.obj i).finrank α
  infer_instance

/-- Incoming boundaries and the corresponding submodule of cycles have the same dimension. -/
theorem finrank_boundaryInCycles (K : OrdinaryComplex W) (i : ℤ) (α : ℂ) :
    Module.finrank ℂ (K.boundaryInCycles i α) =
      Module.finrank ℂ (K.boundaries i α) := by
  letI := (K.obj i).finrank α
  exact (Submodule.comapSubtypeEquivOfLe (K.boundaries_le_cycles i α)).finrank_eq

/-- Rank-nullity in degree `i`, refined by the homology quotient. -/
theorem finrank_eq_boundaries_add_homology_add_outgoing
    (K : OrdinaryComplex W) (i : ℤ) (α : ℂ) :
    Module.finrank ℂ ((K.obj i).weight α) =
      Module.finrank ℂ (K.boundaries i α) +
        Module.finrank ℂ (K.WeightHomology i α) +
          Module.finrank ℂ (K.outgoing i α) := by
  letI := (K.obj i).finrank α
  letI := (K.obj (i + 1)).finrank α
  letI := K.weightHomology_finiteDimensional i α
  have hquot := (K.boundaryInCycles i α).finrank_quotient_add_finrank
  have hrank := LinearMap.finrank_range_add_finrank_ker ((K.nextD i).weightMap α)
  rw [show LinearMap.ker ((K.nextD i).weightMap α) = K.cycles i α from rfl,
    show LinearMap.range ((K.nextD i).weightMap α) = K.outgoing i α from rfl] at hrank
  rw [K.finrank_boundaryInCycles i α] at hquot
  dsimp only [obj] at hrank ⊢
  calc
    _ = Module.finrank ℂ (K.outgoing i α) + Module.finrank ℂ (K.cycles i α) :=
      hrank.symm
    _ = Module.finrank ℂ (K.outgoing i α) +
        (Module.finrank ℂ (K.WeightHomology i α) +
          Module.finrank ℂ (K.boundaries i α)) := by rw [hquot]
    _ = _ := by ac_rfl

/-- The outgoing range in degree `i` is the incoming boundary space in degree `i+1`. -/
theorem outgoing_eq_boundaries_succ (K : OrdinaryComplex W) (i : ℤ) (α : ℂ) :
    K.outgoing i α = K.boundaries (i + 1) α := by
  simp only [outgoing, boundaries, nextD, prevD]
  have hrange : ∀ (p q r : ℤ) (hp : r = p + 1) (hq : r = q + 1), p = q →
      (K.d p r hp).gradedRange α = (K.d q r hq).gradedRange α := by
    intro p q r hp hq hpq
    subst q
    rfl
  exact hrange i (i + 1 - 1) (i + 1) rfl (by omega) (by omega)

/-! ## Exactness -/

/-- Pointwise exactness at cochain degree `i`. -/
def IsExactAt (K : OrdinaryComplex W) (i : ℤ) : Prop :=
  OrdVModule.Hom.ExactAt (K.prevD i) (K.nextD i)

/-- Exactness at every cochain degree. -/
def IsExact (K : OrdinaryComplex W) : Prop := ∀ i : ℤ, K.IsExactAt i

/-- Pointwise exactness restricts to a pointwise exact sequence on every weight space. -/
theorem isExactAt_weight (K : OrdinaryComplex W) {i : ℤ} (h : K.IsExactAt i)
    (α : ℂ) (y : (K.obj i).weight α) :
    (K.nextD i).weightMap α y = 0 ↔
      ∃ x : (K.obj (i - 1)).weight α, (K.prevD i).weightMap α x = y := by
  constructor
  · intro hy
    have hdy : (K.nextD i).toLinearMap (y : K.X i) = 0 := congrArg Subtype.val hy
    obtain ⟨x, hx⟩ := (h (y : K.X i)).mp hdy
    refine ⟨OrdVModule.Hom.weightProj (K.obj (i - 1)) α x, ?_⟩
    rw [OrdVModule.Hom.weightProj_naturality]
    apply Subtype.ext
    rw [hx, OrdVModule.Hom.weightProj_coe]
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    change (K.nextD i).toLinearMap ((K.prevD i).toLinearMap (x : K.X (i - 1))) = 0
    exact K.d_comp_prevD i (x : K.X (i - 1))

/-- Exactness identifies boundaries and cycles on every conformal-weight space. -/
theorem boundaries_eq_cycles_of_isExactAt (K : OrdinaryComplex W) {i : ℤ}
    (h : K.IsExactAt i) (α : ℂ) : K.boundaries i α = K.cycles i α := by
  ext y
  change (∃ x : (K.obj (i - 1)).weight α, (K.prevD i).weightMap α x = y) ↔
    (K.nextD i).weightMap α y = 0
  exact (K.isExactAt_weight h α y).symm

/-- Exactness forces the corresponding weight homology to have dimension zero. -/
theorem finrank_weightHomology_eq_zero_of_isExactAt (K : OrdinaryComplex W) {i : ℤ}
    (h : K.IsExactAt i) (α : ℂ) :
    Module.finrank ℂ (K.WeightHomology i α) = 0 := by
  letI := (K.obj i).finrank α
  letI := K.weightHomology_finiteDimensional i α
  have htop : K.boundaryInCycles i α = ⊤ := by
    rw [boundaryInCycles, K.boundaries_eq_cycles_of_isExactAt h α]
    simp
  change Module.finrank ℂ ((K.cycles i α) ⧸ K.boundaryInCycles i α) = 0
  have hquot := (K.boundaryInCycles i α).finrank_quotient_add_finrank
  rw [htop]
  rw [htop] at hquot
  simp only [finrank_top] at hquot
  omega

/-! ## Finite Euler--Poincaré identities -/

/-- The complex-term dimension in conformal weight `α`, cast to `ℂ`. -/
noncomputable def termCoeff (K : OrdinaryComplex W) (i : ℤ) (α : ℂ) : ℂ :=
  Module.finrank ℂ ((K.obj i).weight α)

/-- The boundary-space dimension in conformal weight `α`, cast to `ℂ`. -/
noncomputable def boundaryCoeff (K : OrdinaryComplex W) (i : ℤ) (α : ℂ) : ℂ :=
  Module.finrank ℂ (K.boundaries i α)

/-- The homology-space dimension in conformal weight `α`, cast to `ℂ`. -/
noncomputable def homologyCoeff (K : OrdinaryComplex W) (i : ℤ) (α : ℂ) : ℂ :=
  Module.finrank ℂ (K.WeightHomology i α)

/-- The outgoing-range dimension in conformal weight `α`, cast to `ℂ`. -/
noncomputable def outgoingCoeff (K : OrdinaryComplex W) (i : ℤ) (α : ℂ) : ℂ :=
  Module.finrank ℂ (K.outgoing i α)

/-- The rank identity, with dimensions cast to complex coefficients. -/
theorem termCoeff_eq (K : OrdinaryComplex W) (i : ℤ) (α : ℂ) :
    K.termCoeff i α = K.boundaryCoeff i α + K.homologyCoeff i α + K.outgoingCoeff i α := by
  unfold termCoeff boundaryCoeff homologyCoeff outgoingCoeff
  exact_mod_cast K.finrank_eq_boundaries_add_homology_add_outgoing i α

/-- Outgoing rank in degree `i` is boundary rank in degree `i+1`. -/
theorem outgoingCoeff_eq_boundaryCoeff_succ (K : OrdinaryComplex W) (i : ℤ) (α : ℂ) :
    K.outgoingCoeff i α = K.boundaryCoeff (i + 1) α := by
  rw [outgoingCoeff, boundaryCoeff, K.outgoing_eq_boundaries_succ]

/-- A finite consecutive alternating sum of complex-term dimensions.  The window contains the
`length + 1` degrees `a, …, a + length`. -/
noncomputable def truncatedEulerCoeff (K : OrdinaryComplex W) (a : ℤ) (length : ℕ) (α : ℂ) :
    ℂ :=
  ∑ j ∈ Finset.range (length + 1),
    negOnePow (a + (j : ℤ)) * K.termCoeff (a + (j : ℤ)) α

/-- The corresponding finite alternating sum of homology dimensions. -/
noncomputable def truncatedHomologyCoeff
    (K : OrdinaryComplex W) (a : ℤ) (length : ℕ) (α : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (length + 1),
    negOnePow (a + (j : ℤ)) * K.homologyCoeff (a + (j : ℤ)) α

/-- The elementary alternating-sign telescope underlying Euler--Poincaré. -/
private theorem alternating_telescope (b h : ℤ → ℂ) (a : ℤ) (length : ℕ) :
    (∑ j ∈ Finset.range (length + 1),
        negOnePow (a + (j : ℤ)) *
          (b (a + (j : ℤ)) + h (a + (j : ℤ)) + b (a + (j : ℤ) + 1))) =
      (∑ j ∈ Finset.range (length + 1),
        negOnePow (a + (j : ℤ)) * h (a + (j : ℤ))) +
        negOnePow a * b a +
          negOnePow (a + (length : ℤ)) * b (a + (length : ℤ) + 1) := by
  induction length with
  | zero => simp; ring
  | succ length ih =>
      rw [Finset.sum_range_succ
          (f := fun j => negOnePow (a + (j : ℤ)) *
            (b (a + (j : ℤ)) + h (a + (j : ℤ)) + b (a + (j : ℤ) + 1)))
          (length + 1),
        Finset.sum_range_succ
          (f := fun j => negOnePow (a + (j : ℤ)) * h (a + (j : ℤ)))
          (length + 1), ih, Nat.cast_succ]
      rw [show a + ((length : ℤ) + 1) = (a + (length : ℤ)) + 1 by ring,
        negOnePow_succ]
      ring

/-- Finite Euler--Poincaré with its two endpoint corrections. -/
theorem truncatedEulerCoeff_eq (K : OrdinaryComplex W) (a : ℤ) (length : ℕ) (α : ℂ) :
    K.truncatedEulerCoeff a length α =
      K.truncatedHomologyCoeff a length α +
        negOnePow a * K.boundaryCoeff a α +
          negOnePow (a + (length : ℤ)) * K.outgoingCoeff (a + (length : ℤ)) α := by
  rw [truncatedEulerCoeff, truncatedHomologyCoeff]
  calc
    _ = ∑ j ∈ Finset.range (length + 1),
        negOnePow (a + (j : ℤ)) *
          (K.boundaryCoeff (a + (j : ℤ)) α +
            K.homologyCoeff (a + (j : ℤ)) α +
              K.boundaryCoeff (a + (j : ℤ) + 1) α) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [K.termCoeff_eq, K.outgoingCoeff_eq_boundaryCoeff_succ]
    _ = (∑ j ∈ Finset.range (length + 1),
        negOnePow (a + (j : ℤ)) * K.homologyCoeff (a + (j : ℤ)) α) +
          negOnePow a * K.boundaryCoeff a α +
            negOnePow (a + (length : ℤ)) *
              K.boundaryCoeff (a + (length : ℤ) + 1) α := by
      exact alternating_telescope (fun i => K.boundaryCoeff i α)
        (fun i => K.homologyCoeff i α) a length
    _ = _ := by rw [K.outgoingCoeff_eq_boundaryCoeff_succ]

/-- The finite Euler sum as a formal `q`-series, using the usual central-charge shift. -/
noncomputable def truncatedEuler (K : OrdinaryComplex W) (a : ℤ) (length : ℕ) :
    FormalQSeries :=
  fun e => K.truncatedEulerCoeff a length (e + W.centralCharge / 24)

/-- Coefficientwise local finiteness of the family of complex terms.  This is an input for an
honest infinite Euler character; it is not inferred from ordinary-module finiteness. -/
def CoeffLocallyFinite (K : OrdinaryComplex W) : Prop :=
  ∀ e : ℂ, Set.Finite {i : ℤ | gradedDim (K.obj i) e ≠ 0}

/-- If both endpoint corrections vanish, the finite alternating term sum is exactly the finite
alternating homology sum. -/
theorem truncatedEulerCoeff_eq_homology_of_endpoints
    (K : OrdinaryComplex W) (a : ℤ) (length : ℕ) (α : ℂ)
    (hleft : K.boundaryCoeff a α = 0)
    (hright : K.outgoingCoeff (a + (length : ℤ)) α = 0) :
    K.truncatedEulerCoeff a length α = K.truncatedHomologyCoeff a length α := by
  rw [K.truncatedEulerCoeff_eq, hleft, hright, mul_zero, add_zero]
  simp

/-! ## A single distinguished cohomology -/

/-- The representation-theoretic data supplied by a resolution theorem with one distinguished
cohomology. Exactness away from `n` and the identification at `n` are explicit fields. -/
structure SingleCohomology (K : OrdinaryComplex W) (n : ℤ)
    {H : Type v} [AddCommGroup H] [Module ℂ H] (N : OrdVModule W H) where
  exact_off : ∀ i : ℤ, i ≠ n → K.IsExactAt i
  weightEquiv : ∀ α : ℂ, K.WeightHomology n α ≃ₗ[ℂ] N.weight α

namespace SingleCohomology

variable {H : Type v} [AddCommGroup H] [Module ℂ H] {N : OrdVModule W H}
variable {K : OrdinaryComplex W} {n : ℤ}

/-- Away from the distinguished degree, every homology coefficient vanishes. -/
theorem homologyCoeff_eq_zero (S : SingleCohomology K n N) {i : ℤ} (hi : i ≠ n) (α : ℂ) :
    K.homologyCoeff i α = 0 := by
  unfold OrdinaryComplex.homologyCoeff
  exact_mod_cast K.finrank_weightHomology_eq_zero_of_isExactAt (S.exact_off i hi) α

/-- At the distinguished degree `n`, the homology coefficient is the coefficient of `N`. -/
theorem homologyCoeff_eq (S : SingleCohomology K n N) (α : ℂ) :
    K.homologyCoeff n α = (Module.finrank ℂ (N.weight α) : ℂ) := by
  letI := K.weightHomology_finiteDimensional n α
  letI := N.finrank α
  unfold OrdinaryComplex.homologyCoeff
  exact_mod_cast (S.weightEquiv α).finrank_eq

/-- Character-normalized form of `homologyCoeff_eq`. -/
theorem homologyCoeff_shift_eq_gradedDim (S : SingleCohomology K n N) (e : ℂ) :
    K.homologyCoeff n (e + W.centralCharge / 24) = gradedDim N e := by
  rw [S.homologyCoeff_eq]
  rfl

/-- In a finite window containing `n`, exactness away from `n` collapses the alternating homology
sum to the single distinguished coefficient. -/
theorem truncatedHomologyCoeff_eq (S : SingleCohomology K n N)
    (a : ℤ) (length : ℕ) (j : ℕ) (hj : j ∈ Finset.range (length + 1))
    (hn : n = a + (j : ℤ)) (α : ℂ) :
    K.truncatedHomologyCoeff a length α =
      negOnePow n * (Module.finrank ℂ (N.weight α) : ℂ) := by
  classical
  rw [OrdinaryComplex.truncatedHomologyCoeff, Finset.sum_eq_single j]
  · rw [← hn, S.homologyCoeff_eq]
  · intro k hk hkj
    have hdeg : a + (k : ℤ) ≠ n := by
      rw [hn]
      intro hak
      apply hkj
      exact_mod_cast add_left_cancel hak
    rw [S.homologyCoeff_eq_zero hdeg, mul_zero]
  · intro hjnot
    exact (hjnot hj).elim

end SingleCohomology

/-! ## The additional support needed for an infinite Euler character -/

/-- A chosen finite coefficient window for an infinite complex. This strengthens local finiteness
by choosing a consecutive support window, requiring it to contain the distinguished degree, and
recording the two endpoint vanishings used by the finite Euler theorem. -/
structure EulerWindowSupport (K : OrdinaryComplex W) (n : ℤ) where
  locallyFinite : K.CoeffLocallyFinite
  start : ℂ → ℤ
  length : ℂ → ℕ
  distinguished_mem : ∀ e : ℂ, ∃ j ∈ Finset.range (length e + 1),
    n = start e + (j : ℤ)
  support_mem : ∀ (e : ℂ) (i : ℤ), gradedDim (K.obj i) e ≠ 0 →
    ∃ j ∈ Finset.range (length e + 1), i = start e + (j : ℤ)
  boundary_start_zero : ∀ e : ℂ,
    K.boundaryCoeff (start e) (e + W.centralCharge / 24) = 0
  outgoing_end_zero : ∀ e : ℂ,
    K.outgoingCoeff (start e + (length e : ℤ)) (e + W.centralCharge / 24) = 0

/-- The Euler character selected by an explicit coefficientwise finite window. -/
noncomputable def EulerWindowSupport.eulerCharacter {K : OrdinaryComplex W} {n : ℤ}
    (S : EulerWindowSupport K n) : FormalQSeries :=
  fun e => K.truncatedEulerCoeff (S.start e) (S.length e)
    (e + W.centralCharge / 24)

/-- Euler--Poincaré for a complex with one distinguished cohomology and an explicit finite
coefficient window. This is a coefficientwise finite theorem, not an inferred Felder exactness
claim and not an unproved infinite `finsum` rearrangement. -/
theorem EulerWindowSupport.eulerCharacter_eq
    {H : Type v} [AddCommGroup H] [Module ℂ H] {N : OrdVModule W H}
    {K : OrdinaryComplex W} {n : ℤ}
    (C : SingleCohomology K n N) (S : EulerWindowSupport K n) :
    S.eulerCharacter = fun e => negOnePow n * gradedDim N e := by
  funext e
  obtain ⟨j, hj, hn⟩ := S.distinguished_mem e
  rw [EulerWindowSupport.eulerCharacter,
    K.truncatedEulerCoeff_eq_homology_of_endpoints
      (S.start e) (S.length e) (e + W.centralCharge / 24)
      (S.boundary_start_zero e) (S.outgoing_end_zero e),
    C.truncatedHomologyCoeff_eq (S.start e) (S.length e) j hj hn]
  rfl

end OrdinaryComplex

end VOA
