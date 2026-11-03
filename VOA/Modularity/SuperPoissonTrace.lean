/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.GammaThetaStatement
import VOA.Modularity.SuperZhuCommutator
import VOA.Modularity.TraceSpace

/-!
# Super Poisson traces and the Etingof finiteness condition

This file isolates the linear-algebraic input needed by a super Arakawa--Kawasetsu theorem.
It deliberately works upstairs on the state space.  The relation subspace is

`superO₂ W ⊔ span {a₍₀₎b | a b : W}`.

Its quotient is only asserted to be a complex vector space.  In particular, this file does not
claim that the bracket span is an ideal or construct a Poisson superalgebra quotient.

Weight and parity are independent throughout.  The defining zero-mode span uses all states.  For
an integral-weight super VOA, `superZeroModeSpan_eq_bihomogeneous` identifies it with the span of
generators carrying four separate witnesses: the two integral weights and the two parities.  No
spin--statistics identification is made.
-/

namespace VOA

open Module (finrank)
open GammaThetaStmt

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The zero-mode and total relation spans -/

/-- The span of all zero-mode products `a₍₀₎b` in a super VOA. -/
def superZeroModeSpan (W : SuperVertexOperatorAlgebra 𝒱) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ {x : 𝒱 | ∃ a b : 𝒱, x = W.toSuperNearVOA.smul a 0 b}

/-- A zero-mode product with independent integral-weight and parity witnesses for both inputs. -/
def superBiHomZeroModeGen (W : SuperVertexOperatorAlgebra 𝒱) : Set 𝒱 :=
  {x : 𝒱 | ∃ (K M : ℤ) (p q : ZMod 2) (a b : 𝒱),
    a ∈ W.toSuperNearVOA.gradingZ K ∧ a ∈ W.toSuperNearVOA.parity p ∧
    b ∈ W.toSuperNearVOA.gradingZ M ∧ b ∈ W.toSuperNearVOA.parity q ∧
    x = W.toSuperNearVOA.smul a 0 b}

/-- The span of the explicitly weight/parity bi-homogeneous zero-mode products. -/
def superBiHomZeroModeSpan (W : SuperVertexOperatorAlgebra 𝒱) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ (superBiHomZeroModeGen W)

/-- Every zero-mode product belongs to `superZeroModeSpan`. -/
theorem superZeroMode_mem_span (W : SuperVertexOperatorAlgebra 𝒱) (a b : 𝒱) :
    W.toSuperNearVOA.smul a 0 b ∈ superZeroModeSpan W :=
  Submodule.subset_span ⟨a, b, rfl⟩

/-- A bi-homogeneous zero-mode product belongs to the explicitly bi-homogeneous span. -/
theorem superBiHomZeroMode_mem_span (W : SuperVertexOperatorAlgebra 𝒱)
    {K M : ℤ} {p q : ZMod 2} {a b : 𝒱}
    (haK : a ∈ W.toSuperNearVOA.gradingZ K) (hap : a ∈ W.toSuperNearVOA.parity p)
    (hbM : b ∈ W.toSuperNearVOA.gradingZ M) (hbq : b ∈ W.toSuperNearVOA.parity q) :
    W.toSuperNearVOA.smul a 0 b ∈ superBiHomZeroModeSpan W :=
  Submodule.subset_span ⟨K, M, p, q, a, b, haK, hap, hbM, hbq, rfl⟩

/-- For integral weights, all zero-mode products are spanned by products whose two inputs are
independently homogeneous in weight and parity. -/
theorem superZeroModeSpan_eq_bihomogeneous (W : SuperVertexOperatorAlgebra 𝒱)
    (hV : W.toSuperNearVOA.IntegralWeights) :
    superZeroModeSpan W = superBiHomZeroModeSpan W := by
  let V := W.toSuperNearVOA
  apply le_antisymm
  · rw [superZeroModeSpan, Submodule.span_le]
    rintro _ ⟨a, b, rfl⟩
    refine V.reduce_bihomogeneous hV
      (P := fun a => V.smul a 0 b ∈ superBiHomZeroModeSpan W) ?_ ?_ ?_ a
    · intro K p u hu
      refine V.reduce_bihomogeneous hV
        (P := fun b => V.smul u 0 b ∈ superBiHomZeroModeSpan W) ?_ ?_ ?_ b
      · intro M q v hv
        exact superBiHomZeroMode_mem_span W hu.1 hu.2 hv.1 hv.2
      · simp
      · intro x y hx hy
        rw [SuperVertexAlgebra.smul_add_right]
        exact (superBiHomZeroModeSpan W).add_mem hx hy
    · simp
    · intro x y hx hy
      rw [SuperVertexAlgebra.smul_add_left]
      exact (superBiHomZeroModeSpan W).add_mem hx hy
  · rw [superBiHomZeroModeSpan, Submodule.span_le]
    rintro _ ⟨K, M, p, q, a, b, haK, hap, hbM, hbq, rfl⟩
    exact superZeroMode_mem_span W a b

/-- The super `C₂`/Poisson-trace relation subspace upstairs on the state space. -/
def superPoissonRelSpan (W : SuperVertexOperatorAlgebra 𝒱) : Submodule ℂ 𝒱 :=
  superO₂ W ⊔ superZeroModeSpan W

/-- Under integral weights the total relation span has explicitly bi-homogeneous zero-mode
generators.  The integral weights `K,M` and parities `p,q` remain separate data. -/
theorem superPoissonRelSpan_eq_bihomogeneous (W : SuperVertexOperatorAlgebra 𝒱)
    (hV : W.toSuperNearVOA.IntegralWeights) :
    superPoissonRelSpan W = superO₂ W ⊔ superBiHomZeroModeSpan W := by
  rw [superPoissonRelSpan, superZeroModeSpan_eq_bihomogeneous W hV]

/-- Every zero-mode bracket lies in the total trace relation span. -/
theorem superZeroMode_mem_superPoissonRelSpan (W : SuperVertexOperatorAlgebra 𝒱)
    (a b : 𝒱) : W.toSuperNearVOA.smul a 0 b ∈ superPoissonRelSpan W :=
  Submodule.mem_sup_right (superZeroMode_mem_span W a b)

/-! ## The Koszul convention -/

/-- Translation by `L₋₁` is a `C₂` relation: `L₋₁x = x₍₋₂₎𝟙`. -/
theorem Lneg1_mem_superO₂ (W : SuperVertexOperatorAlgebra 𝒱) (x : 𝒱) :
    W.toSuperNearVOA.L (-1) x ∈ superO₂ W := by
  have h := W.toSuperNearVOA.creation_powε x 1
  norm_num at h
  rw [← h]
  exact Submodule.subset_span ⟨x, W.vacuum, rfl⟩

/-- Every positive power of `L₋₁` lands in `superO₂`. -/
theorem Lneg1_pow_mem_superO₂ (W : SuperVertexOperatorAlgebra 𝒱) (x : 𝒱)
    {j : ℕ} (hj : 1 ≤ j) :
    (W.toSuperNearVOA.L (-1) ^ j) x ∈ superO₂ W := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  rw [pow_succ', Module.End.mul_apply]
  exact Lneg1_mem_superO₂ W _

/-- **Koszul sign audit.**  On parity-homogeneous inputs the zero-mode bracket is
super-antisymmetric modulo `superO₂`:

`a₍₀₎b + koszul p q • b₍₀₎a ∈ superO₂`.

This follows from the unconditional Jacobi-derived super-skew theorem.  The `j = 0` term has
sign `sgn(-1) = -1`; every `j > 0` term contains a positive power of `L₋₁` and is a `C₂`
relation.  No conformal-weight hypothesis enters the sign. -/
theorem superZeroMode_koszul_antisymm_mod_superO₂
    (W : SuperVertexOperatorAlgebra 𝒱) {p q : ZMod 2} {a b : 𝒱}
    (hap : a ∈ W.toSuperNearVOA.parity p) (hbq : b ∈ W.toSuperNearVOA.parity q) :
    W.toSuperNearVOA.smul a 0 b
        + koszul p q • W.toSuperNearVOA.smul b 0 a ∈ superO₂ W := by
  let V := W.toSuperNearVOA
  let Q := superO₂ W
  let f : ℕ → 𝒱 := fun j => ((j.factorial : ℂ)⁻¹) •
    (sgn (-1 - (j : ℤ))) • ((V.L (-1) ^ j) (V.smul a (j : ℤ) b))
  have hfin : (Function.support f).Finite := by
    simpa only [f, zero_add] using V.superSkewFamily_support_finite a b 0
      (fun j => ((j.factorial : ℂ)⁻¹))
      (fun j x => (sgn (-1 - (j : ℤ))) • ((V.L (-1) ^ j) x))
      (fun j => by simp)
  have hsk : V.smul b 0 a = koszul p q • ∑ᶠ j : ℕ, f j := by
    simpa [f] using V.superSmul_eq_skew_Lpow hap hbq 0
  apply (Submodule.Quotient.mk_eq_zero Q).mp
  change Q.mkQ (V.smul a 0 b + koszul p q • V.smul b 0 a) = 0
  rw [map_add, map_smul, hsk, map_smul, smul_smul, koszul_mul_self, one_smul,
    map_finsum Q.mkQ hfin, add_comm]
  rw [finsum_eq_single _ 0]
  · simp [f, show sgn (-1 : ℤ) = (-1 : ℂ) from rfl]
  · intro j hj
    apply (Submodule.Quotient.mk_eq_zero Q).2
    exact Q.smul_mem _ (Q.smul_mem _ (Lneg1_pow_mem_superO₂ W _ (by omega)))

/-! ## The quotient and its dual trace space -/

/-- The super zeroth Poisson-homology carrier, defined only as a vector-space quotient. -/
noncomputable abbrev SuperPoissonHP₀ (W : SuperVertexOperatorAlgebra 𝒱) : Type u :=
  𝒱 ⧸ superPoissonRelSpan W

/-- Super Poisson-trace functionals: linear forms on `V` killing `O₂` and every zero-mode
product. -/
noncomputable def superPoissonTraces (W : SuperVertexOperatorAlgebra 𝒱) :
    Submodule ℂ (Module.Dual ℂ 𝒱) :=
  vanishingFunctionals ℂ 𝒱 (superPoissonRelSpan W)

/-- A functional is a super Poisson trace exactly when it kills `superO₂` and every zero-mode
product. -/
theorem mem_superPoissonTraces {W : SuperVertexOperatorAlgebra 𝒱}
    {φ : Module.Dual ℂ 𝒱} :
    φ ∈ superPoissonTraces W ↔
      superO₂ W ≤ LinearMap.ker φ ∧
      ∀ a b : 𝒱, φ (W.toSuperNearVOA.smul a 0 b) = 0 := by
  rw [superPoissonTraces, mem_vanishingFunctionals, superPoissonRelSpan, sup_le_iff,
    superZeroModeSpan, Submodule.span_le]
  constructor
  · rintro ⟨hO₂, hzero⟩
    refine ⟨hO₂, fun a b => LinearMap.mem_ker.mp (hzero ⟨a, b, rfl⟩)⟩
  · rintro ⟨hO₂, hzero⟩
    refine ⟨hO₂, ?_⟩
    rintro _ ⟨a, b, rfl⟩
    exact LinearMap.mem_ker.mpr (hzero a b)

/-- Integral-weight membership criterion using only explicitly bi-homogeneous pairs.  This is the
form in which every Koszul sign downstream is well typed: `K,M : ℤ` and `p,q : ZMod 2` are four
independent binders. -/
theorem mem_superPoissonTraces_bihomogeneous
    {W : SuperVertexOperatorAlgebra 𝒱} (hV : W.toSuperNearVOA.IntegralWeights)
    {φ : Module.Dual ℂ 𝒱} :
    φ ∈ superPoissonTraces W ↔
      superO₂ W ≤ LinearMap.ker φ ∧
      ∀ (K M : ℤ) (p q : ZMod 2) (a b : 𝒱),
        a ∈ W.toSuperNearVOA.gradingZ K → a ∈ W.toSuperNearVOA.parity p →
        b ∈ W.toSuperNearVOA.gradingZ M → b ∈ W.toSuperNearVOA.parity q →
        φ (W.toSuperNearVOA.smul a 0 b) = 0 := by
  let V := W.toSuperNearVOA
  rw [mem_superPoissonTraces]
  constructor
  · rintro ⟨hO₂, hzero⟩
    exact ⟨hO₂, fun _ _ _ _ a b _ _ _ _ => hzero a b⟩
  · rintro ⟨hO₂, hhom⟩
    refine ⟨hO₂, fun a b => ?_⟩
    refine V.reduce_bihomogeneous hV
      (P := fun a => φ (V.smul a 0 b) = 0) ?_ ?_ ?_ a
    · intro K p u hu
      refine V.reduce_bihomogeneous hV
        (P := fun b => φ (V.smul u 0 b) = 0) ?_ ?_ ?_ b
      · intro M q v hv
        exact hhom K M p q u v hu.1 hu.2 hv.1 hv.2
      · simp
      · intro x y hx hy
        rw [SuperVertexAlgebra.smul_add_right, map_add, hx, hy, add_zero]
    · simp
    · intro x y hx hy
      rw [SuperVertexAlgebra.smul_add_left, map_add, hx, hy, add_zero]

/-- Super Poisson traces are canonically the dual of the super Poisson-homology quotient. -/
noncomputable def superPoissonTracesEquiv (W : SuperVertexOperatorAlgebra 𝒱) :
    superPoissonTraces W ≃ₗ[ℂ] Module.Dual ℂ (SuperPoissonHP₀ W) :=
  vanishingEquiv (superPoissonRelSpan W)

/-- Unconditional dimension equality between super Poisson traces and their quotient carrier. -/
theorem finrank_superPoissonTraces (W : SuperVertexOperatorAlgebra 𝒱) :
    finrank ℂ (superPoissonTraces W) = finrank ℂ (SuperPoissonHP₀ W) :=
  finrank_vanishingFunctionals (superPoissonRelSpan W)

/-! ## Super Etingof finiteness -/

/-- The super Etingof finiteness condition: the vector space obtained by quotienting `V` by
`O₂(V)` and all zero-mode products is finite-dimensional. -/
def SuperEtingofFinite (W : SuperVertexOperatorAlgebra 𝒱) : Prop :=
  FiniteDimensional ℂ (SuperPoissonHP₀ W)

theorem SuperEtingofFinite_iff (W : SuperVertexOperatorAlgebra 𝒱) :
    SuperEtingofFinite W ↔ FiniteDimensional ℂ (𝒱 ⧸ superPoissonRelSpan W) := Iff.rfl

/-- The quotient map from the super `C₂` quotient onto the super Poisson-homology quotient. -/
noncomputable def superC2QuotToPoissonQuot (W : SuperVertexOperatorAlgebra 𝒱) :
    (𝒱 ⧸ superO₂ W) →ₗ[ℂ] SuperPoissonHP₀ W :=
  (superO₂ W).liftQ (superPoissonRelSpan W).mkQ (by
    intro x hx
    exact (Submodule.Quotient.mk_eq_zero (superPoissonRelSpan W)).2
      (Submodule.mem_sup_left hx))

@[simp] theorem superC2QuotToPoissonQuot_mk (W : SuperVertexOperatorAlgebra 𝒱) (x : 𝒱) :
    superC2QuotToPoissonQuot W ((superO₂ W).mkQ x) = (superPoissonRelSpan W).mkQ x := rfl

theorem superC2QuotToPoissonQuot_surjective (W : SuperVertexOperatorAlgebra 𝒱) :
    Function.Surjective (superC2QuotToPoissonQuot W) := by
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (superPoissonRelSpan W) q
  exact ⟨(superO₂ W).mkQ x, rfl⟩

/-- Super `C₂`-cofiniteness implies super Etingof finiteness.  No grading or parity
identification is used: this is only finite-dimensionality descending along a quotient map. -/
theorem SuperEtingofFinite_of_superC2Cofinite (W : SuperVertexOperatorAlgebra 𝒱)
    (hC2 : SuperC2Cofinite W) : SuperEtingofFinite W := by
  haveI : FiniteDimensional ℂ (𝒱 ⧸ superO₂ W) := hC2
  exact Module.Finite.of_surjective (superC2QuotToPoissonQuot W)
    (superC2QuotToPoissonQuot_surjective W)

/-- Dot-notation form of `SuperEtingofFinite_of_superC2Cofinite`. -/
theorem SuperC2Cofinite.superEtingofFinite {W : SuperVertexOperatorAlgebra 𝒱}
    (hC2 : SuperC2Cofinite W) : SuperEtingofFinite W :=
  SuperEtingofFinite_of_superC2Cofinite W hC2

/-- Etingof finiteness makes the dual super Poisson-trace space finite-dimensional. -/
theorem finiteDimensional_superPoissonTraces (W : SuperVertexOperatorAlgebra 𝒱)
    (hE : SuperEtingofFinite W) : FiniteDimensional ℂ (superPoissonTraces W) := by
  haveI : FiniteDimensional ℂ (SuperPoissonHP₀ W) := hE
  exact finiteDimensional_vanishingFunctionals_of_quot (superPoissonRelSpan W)

/-- The trace space is finite-dimensional in the super `C₂`-cofinite case. -/
theorem finiteDimensional_superPoissonTraces_of_superC2Cofinite
    (W : SuperVertexOperatorAlgebra 𝒱) (hC2 : SuperC2Cofinite W) :
    FiniteDimensional ℂ (superPoissonTraces W) :=
  finiteDimensional_superPoissonTraces W
    (SuperEtingofFinite_of_superC2Cofinite W hC2)

end VOA
