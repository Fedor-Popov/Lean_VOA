/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperSpinCoefficients
import VOA.Modularity.SuperAnalyticBlock
import VOA.Modularity.BlockRelSpanning
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Formal genus-one relations in the four super spin sectors

This is the algebraic, coefficient-by-coefficient part of van Ekeren's Definition 4.1,
specialized to sign eigenvalues.  For a sector `p = (mu, lambda)`:

* `mu` is the eigenvalue of the state for the automorphism twisting the module around the
  spatial cycle;
* `lambda` is its eigenvalue for the commuting temporal insertion/intertwiner;
* neither label is the parity of the state.  Parity, and hence every Koszul sign, is a separate
  datum used when a trace is cyclically reordered.  None of the residue relations below
  interchanges two states.

There is an important coordinate normalization.  Van Ekeren uses the square coordinate
`exp(2*pi*i*z)-1`; `superVSqC` uses `exp(z)-1`.  Thus the coefficient multiplying the repository
mode `a[k]` is

`spinQ p k = (2*pi*i)^(-k-1) spinP p k`.

With this normalization `spinQ (++ ) (2*j-1)` is exactly `zhuG j`.  Combining the unnormalized
`spinP` with repository square modes would be wrong by `(2*pi*i)^(2*j)`.

For the invariant sector `(++ )` we define the zero-mode family and the `wp` family

`a[-2]b + sum_(j>=2) (2*j-1) G_(2*j) a[2*j-2]b`.

The sum starts at `j=2`; the omitted `G2` coefficient is named separately below.  For any
nontrivial label the relations are `a` itself and

`-a[-1]b + sum_(k>=0) spinQ p k (Cauchy-act) a[k]b`.

All sums are truncated using ordinary regularity.  We define both the formal relation submodule
inside `FormalQSeries tensor V` and its literal constant-term (`q=0`) degeneration.  The tensor
presentation avoids falsely treating pointwise multiplication of coefficient functions as
formal-series multiplication.  No convergence, holomorphy, modular transformation, or `G2`
differential recursion is asserted here.
-/

namespace VOA

open scoped BigOperators TensorProduct

set_option autoImplicit false

universe u

/-! ## Coordinate-normalized coefficient series -/

theorem spinTwoPiI_ne_zero : spinTwoPiI ≠ 0 := by
  simp [spinTwoPiI, Real.pi_ne_zero, Complex.I_ne_zero]

/-- Van Ekeren's coefficient rescaled from his `exp(2*pi*i*z)-1` modes to the repository's
`exp(z)-1` square modes. -/
noncomputable def spinQ (p : SpinPair) (k : Nat) : FormalQSeries :=
  (spinTwoPiI ^ (k + 1))⁻¹ • spinP p k

/-- The constant term of the normalized coefficient. -/
noncomputable def spinQCusp (p : SpinPair) (k : Nat) : Complex :=
  (spinTwoPiI ^ (k + 1))⁻¹ * spinPCusp p k

@[simp] theorem spinQ_apply (p : SpinPair) (k : Nat) (e : Complex) :
    spinQ p k e = (spinTwoPiI ^ (k + 1))⁻¹ * spinP p k e := rfl

@[simp] theorem spinQ_cusp (p : SpinPair) (k : Nat) :
    spinQ p k 0 = spinQCusp p k := by
  rw [spinQ_apply, spinP_cusp]
  rfl

@[simp] theorem spinQCusp_pm_zero : spinQCusp SpinPair.pm 0 = 0 := by
  simp [spinQCusp]

@[simp] theorem spinQCusp_mp_zero : spinQCusp SpinPair.mp 0 = 0 := by
  simp [spinQCusp]

@[simp] theorem spinQCusp_mm_zero : spinQCusp SpinPair.mm 0 = 0 := by
  simp [spinQCusp]

/-- In the invariant sector, the normalized odd coefficient is exactly the repository's
Zhu-normalized Eisenstein coefficient. -/
theorem spinQ_pp_odd_eq_zhuG {j : Nat} (hj : j ≠ 0) (n : Nat) :
    spinQ SpinPair.pp (2 * j - 1) (n : Complex) = zhuG j n := by
  rw [spinQ_apply, spinP_pp_eq_spinTwoPiI_pow_zhuG hj]
  have hpow : spinTwoPiI ^ (2 * j) ≠ 0 := pow_ne_zero _ spinTwoPiI_ne_zero
  have hk : 2 * j - 1 + 1 = 2 * j := by omega
  rw [hk, inv_mul_cancel_left₀ hpow]

theorem spinQCusp_pp_odd_eq_zhuG {j : Nat} (hj : j ≠ 0) :
    spinQCusp SpinPair.pp (2 * j - 1) = zhuG j 0 := by
  have h := spinQ_pp_odd_eq_zhuG hj 0
  rw [Nat.cast_zero, spinQ_cusp] at h
  exact h

/-- The isolated `G2` coefficient.  It does not occur in the `wp` relation family; analytically
it is absorbed by the separate conformal-weight/derivative recursion. -/
noncomputable def superSpinG2Coefficient : FormalQSeries := spinQ SpinPair.pp 1

theorem superSpinG2Coefficient_eq_zhuG (n : Nat) :
    superSpinG2Coefficient (n : Complex) = zhuG 1 n := by
  exact spinQ_pp_odd_eq_zhuG (j := 1) (by norm_num) n

/-! ## Local finiteness of complex-weight square modes -/

variable {VType : Type u} [AddCommGroup VType] [Module Complex VType]

namespace SuperNearVOA

variable (V : SuperNearVOA VType)

/-- For fixed inputs, all sufficiently high complex-weight square modes vanish. -/
theorem superVSqC_eventually_zero (a : VType) (h : Complex) (b : VType) :
    exists N : Int, forall m : Int, N <= m -> V.superVSqC a h m b = 0 := by
  obtain ⟨N, hN⟩ := V.regularity a b
  refine ⟨N, fun m hm => ?_⟩
  rw [V.superVSqC_apply]
  refine finsum_eq_zero_of_forall_eq_zero (fun i => ?_)
  rcases lt_or_ge i m with hi | hi
  · rw [sqBracketCoeffC_of_lt h hi, zero_smul]
  · change sqBracketCoeffC h m i • (mode (V.Y a) i) b = 0
    rw [hN i (le_trans hm hi), smul_zero]

/-- Natural-index tail form used by the `P`-series residue. -/
theorem superVSqC_nat_eventually_zero (a : VType) (h : Complex) (b : VType) :
    exists K : Nat, forall k : Nat, K <= k -> V.superVSqC a h (k : Int) b = 0 := by
  obtain ⟨N, hN⟩ := V.superVSqC_eventually_zero a h b
  refine ⟨N.toNat, fun k hk => hN (k : Int) ?_⟩
  omega

/-! ## Formal base change and the four relation families -/

/-- Coefficient-ring base change for the four spin-sector relations. -/
abbrev SuperSpinQSpace := FormalQSeries ⊗[Complex] VType

/-- The canonical constant inclusion `v |-> 1 tensor v`. -/
noncomputable def superSpinInclude : VType →ₗ[Complex] SuperSpinQSpace (VType := VType) :=
  TensorProduct.mk Complex FormalQSeries VType 1

@[simp] theorem superSpinInclude_apply (v : VType) :
    (superSpinInclude v : SuperSpinQSpace (VType := VType)) =
      (1 : FormalQSeries) ⊗ₜ[Complex] v := rfl

/-- Constant-term evaluation on the coefficient-function carrier. -/
noncomputable def superSpinCoeffAtCusp : FormalQSeries →ₗ[Complex] Complex where
  toFun f := f 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Specialize a coefficient-labelled relation vector at `q=0`. -/
noncomputable def superSpinSpecializeCusp :
    SuperSpinQSpace (VType := VType) →ₗ[Complex] VType :=
  TensorProduct.lift
    ((LinearMap.toSpanSingleton Complex (VType →ₗ[Complex] VType) LinearMap.id).comp
      superSpinCoeffAtCusp)

@[simp] theorem superSpinSpecializeCusp_tmul (f : FormalQSeries) (v : VType) :
    superSpinSpecializeCusp (f ⊗ₜ[Complex] v) = f 0 • v := rfl

@[simp] theorem superSpinSpecializeCusp_include (v : VType) :
    superSpinSpecializeCusp (superSpinInclude v) = v := by
  rw [superSpinInclude_apply, superSpinSpecializeCusp_tmul]
  change (1 : Complex) • v = v
  rw [one_smul]

/-- Simultaneous state eigenspaces.  This is input algebra, not a bundled theorem: `sector p`
contains states with spatial-twist eigenvalue `p.mu` and temporal-insertion eigenvalue
`p.lambda`.  No relation with the parity grading is assumed. -/
abbrev SuperSpinSectors := SpinPair → Submodule Complex VType

variable (sector : SuperSpinSectors (VType := VType))

/-- The invariant-sector square zero-mode generators. -/
def superSpinX1Set : Set (SuperSpinQSpace (VType := VType)) :=
  {x | exists (h : Complex) (a b : VType), a ∈ sector SpinPair.pp /\
    a ∈ V.grading h /\ x = superSpinInclude (V.superVSqC a h 0 b)}

/-- The invariant-sector `wp` generators.  The tail starts at `j=2`, hence contains no `G2`.
Coefficient multiplication is represented by a pure tensor, not by the (incorrect here)
pointwise ring structure on `FormalQSeries`. -/
noncomputable def superSpinX2Set : Set (SuperSpinQSpace (VType := VType)) :=
  {x | exists (h : Complex) (K : Nat) (a b : VType),
    a ∈ sector SpinPair.pp /\ a ∈ V.grading h /\
    (forall m : Nat, K <= m -> V.superVSqC a h (2 * ((m : Int) + 2) - 2) b = 0) /\
    x = superSpinInclude (V.superVSqC a h (-2) b) +
      ∑ m ∈ Finset.range K,
        (((2 * (m + 2) - 1 : Nat) : Complex) • spinQ SpinPair.pp (2 * (m + 2) - 1))
          ⊗ₜ[Complex] V.superVSqC a h (2 * ((m : Int) + 2) - 2) b}

/-- In a nontrivial simultaneous eigenspace, the state itself is killed. -/
def superSpinKillSet : Set (SuperSpinQSpace (VType := VType)) :=
  {x | exists (p : SpinPair) (a : VType), p ≠ SpinPair.pp /\
    a ∈ sector p /\ x = superSpinInclude a}

/-- The nontrivial-sector `P`-series residue generators.  The leading sign is **minus**. -/
noncomputable def superSpinX3Set : Set (SuperSpinQSpace (VType := VType)) :=
  {x | exists (p : SpinPair) (h : Complex) (K : Nat) (a b : VType),
    p ≠ SpinPair.pp /\ a ∈ sector p /\ a ∈ V.grading h /\
    (forall k : Nat, K <= k -> V.superVSqC a h (k : Int) b = 0) /\
    x = -superSpinInclude (V.superVSqC a h (-1) b) +
      ∑ k ∈ Finset.range K,
        spinQ p k ⊗ₜ[Complex] V.superVSqC a h (k : Int) b}

/-- Van Ekeren's formal relation module for the four sign sectors, with complex-weight
square-bracket modes. -/
noncomputable def superSpinRelSpan :
    Submodule Complex (SuperSpinQSpace (VType := VType)) :=
  Submodule.span Complex
    (V.superSpinX1Set sector ∪ V.superSpinX2Set sector ∪
      superSpinKillSet sector ∪ V.superSpinX3Set sector)

/-! ## Literal infinity-cusp relation space -/

/-- Constant-term version of the invariant square zero-mode family. -/
def superSpinCuspX1Set : Set VType :=
  {x | exists (h : Complex) (a b : VType), a ∈ sector SpinPair.pp /\
    a ∈ V.grading h /\ x = V.superVSqC a h 0 b}

/-- Constant-term version of the invariant `wp` family. -/
noncomputable def superSpinCuspX2Set : Set VType :=
  {x | exists (h : Complex) (K : Nat) (a b : VType),
    a ∈ sector SpinPair.pp /\ a ∈ V.grading h /\
    (forall m : Nat, K <= m -> V.superVSqC a h (2 * ((m : Int) + 2) - 2) b = 0) /\
    x = V.superVSqC a h (-2) b +
      ∑ m ∈ Finset.range K,
        (((2 * (m + 2) - 1 : Nat) : Complex) *
          spinQCusp SpinPair.pp (2 * (m + 2) - 1)) •
            V.superVSqC a h (2 * ((m : Int) + 2) - 2) b}

/-- Constant-term state-kill family. -/
def superSpinCuspKillSet : Set VType :=
  {x | exists (p : SpinPair) (a : VType), p ≠ SpinPair.pp /\
    a ∈ sector p /\ x = a}

/-- Constant-term nontrivial-sector residue family. -/
noncomputable def superSpinCuspX3Set : Set VType :=
  {x | exists (p : SpinPair) (h : Complex) (K : Nat) (a b : VType),
    p ≠ SpinPair.pp /\ a ∈ sector p /\ a ∈ V.grading h /\
    (forall k : Nat, K <= k -> V.superVSqC a h (k : Int) b = 0) /\
    x = -V.superVSqC a h (-1) b +
      ∑ k ∈ Finset.range K,
        spinQCusp p k • V.superVSqC a h (k : Int) b}

/-- The literal constant-term degeneration of `superSpinRelSpan`. -/
noncomputable def superSpinCuspRelSpan : Submodule Complex VType :=
  Submodule.span Complex
    (V.superSpinCuspX1Set sector ∪ V.superSpinCuspX2Set sector ∪
      superSpinCuspKillSet sector ∪ V.superSpinCuspX3Set sector)

/-! ## Sector conformal-block predicate -/

/-- Coefficients of a normalized spin series on the doubled exponent lattice. -/
noncomputable def spinQNatCoeff (p : SpinPair) (k N : Nat) : Complex :=
  spinQ p k (halfQExponent N)

/-- Cauchy action of a half-lattice series on a coefficient function.  This is the correct
formal-series product: the doubled exponent `N` shifts the argument by `N/2`.  It is deliberately
not the inherited pointwise multiplication on functions `Complex → Complex`.

For an arbitrary coefficient function the `finsum` need not be locally finite.  The block
predicate below therefore requires `QHalfSeriesAt hbase` support, which makes every coefficient
sum finite. -/
noncomputable def halfQConv (f : Nat → Complex) (chi : FormalQSeries) : FormalQSeries :=
  fun e => ∑ᶠ N : Nat, f N * chi (e - halfQExponent N)

/-- Formal series supported on one lower-bounded half-lattice coset `h + Nat/2`. -/
def QHalfSeriesAt (h : Complex) : Submodule Complex FormalQSeries where
  carrier := {chi | ∀ e : Complex,
    (∀ N : Nat, e ≠ h + halfQExponent N) → chi e = 0}
  zero_mem' := by intro e he; rfl
  add_mem' := by
    intro chi psi hchi hpsi e he
    change chi e + psi e = 0
    rw [hchi e he, hpsi e he, add_zero]
  smul_mem' := by
    intro c chi hchi e he
    change c * chi e = 0
    rw [hchi e he, mul_zero]

/-- On a supported input, the convolution coefficient at `h + M/2` is the usual finite Cauchy
sum.  This is the local-finiteness gate that rules out the inherited pointwise product. -/
theorem halfQConv_apply_of_support (f : Nat → Complex) {h : Complex}
    {chi : FormalQSeries} (hchi : chi ∈ QHalfSeriesAt h) (M : Nat) :
    halfQConv f chi (h + halfQExponent M) =
      ∑ N ∈ Finset.range (M + 1),
        f N * chi (h + halfQExponent M - halfQExponent N) := by
  classical
  rw [halfQConv]
  refine finsum_eq_finsetSum_of_support_subset _ (fun N hN => ?_)
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hle
  have hNM : M < N := by omega
  have hzero : chi (h + halfQExponent M - halfQExponent N) = 0 := by
    apply hchi
    intro L hEq
    have hML : (M : Complex) = (N : Complex) + (L : Complex) := by
      unfold halfQExponent at hEq
      linear_combination 2 * hEq
    have hnat : M = N + L := by exact_mod_cast hML
    omega
  apply hN
  change f N * chi (h + halfQExponent M - halfQExponent N) = 0
  rw [hzero, mul_zero]

/-- Half-lattice Cauchy multiplication preserves the base coset. -/
theorem halfQConv_mem_QHalfSeriesAt (f : Nat → Complex) {h : Complex}
    {chi : FormalQSeries} (hchi : chi ∈ QHalfSeriesAt h) :
    halfQConv f chi ∈ QHalfSeriesAt h := by
  intro e he
  rw [halfQConv]
  refine finsum_eq_zero_of_forall_eq_zero (fun N => ?_)
  have hzero : chi (e - halfQExponent N) = 0 := by
    apply hchi
    intro M hEq
    apply he (N + M)
    unfold halfQExponent at hEq ⊢
    push_cast
    linear_combination hEq
  rw [hzero, mul_zero]

/-- The four formal residue relations imposed directly on a half-lattice-supported
`FormalQSeries`-valued linear functional.  Every coefficient action is the Cauchy convolution
`halfQConv`; no Hadamard product occurs. -/
structure IsSuperSpinFormalBlock (hbase : Complex)
    (S : VType →ₗ[Complex] FormalQSeries) : Prop where
  support : ∀ v : VType, S v ∈ QHalfSeriesAt hbase
  x1 : forall (h : Complex) (a b : VType), a ∈ sector SpinPair.pp -> a ∈ V.grading h ->
    S (V.superVSqC a h 0 b) = 0
  x2 : forall (h : Complex) (K : Nat) (a b : VType), a ∈ sector SpinPair.pp ->
    a ∈ V.grading h ->
    (forall m : Nat, K <= m -> V.superVSqC a h (2 * ((m : Int) + 2) - 2) b = 0) ->
    S (V.superVSqC a h (-2) b) +
      ∑ m ∈ Finset.range K,
        ((2 * (m + 2) - 1 : Nat) : Complex) •
          halfQConv (spinQNatCoeff SpinPair.pp (2 * (m + 2) - 1))
            (S (V.superVSqC a h (2 * ((m : Int) + 2) - 2) b)) = 0
  kill : forall (p : SpinPair) (a : VType), p ≠ SpinPair.pp ->
    a ∈ sector p -> S a = 0
  x3 : forall (p : SpinPair) (h : Complex) (K : Nat) (a b : VType),
    p ≠ SpinPair.pp -> a ∈ sector p -> a ∈ V.grading h ->
    (forall k : Nat, K <= k -> V.superVSqC a h (k : Int) b = 0) ->
    -S (V.superVSqC a h (-1) b) +
      ∑ k ∈ Finset.range K,
        halfQConv (spinQNatCoeff p k) (S (V.superVSqC a h (k : Int) b)) = 0

/-! ## Generator membership and cusp consequences -/

variable {V sector}

/-- Every formal spin-sector relation specializes at `q=0` to the corresponding explicit cusp
relation.  This is a literal coefficient evaluation theorem; it uses no convergence limit. -/
theorem superSpinSpecializeCusp_mem {x : SuperSpinQSpace (VType := VType)}
    (hx : x ∈ V.superSpinRelSpan sector) :
    superSpinSpecializeCusp x ∈ V.superSpinCuspRelSpan sector := by
  classical
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ((hy | hy) | hy) | hy
      · obtain ⟨h, a, b, hsec, ha, rfl⟩ := hy
        rw [superSpinSpecializeCusp_include]
        exact Submodule.subset_span
          (Or.inl (Or.inl (Or.inl ⟨h, a, b, hsec, ha, rfl⟩)))
      · obtain ⟨h, K, a, b, hsec, ha, hK, rfl⟩ := hy
        rw [map_add, superSpinSpecializeCusp_include, map_sum]
        have hterm : ∀ m ∈ Finset.range K,
            superSpinSpecializeCusp
              ((((2 * (m + 2) - 1 : Nat) : Complex) •
                  spinQ SpinPair.pp (2 * (m + 2) - 1)) ⊗ₜ[Complex]
                V.superVSqC a h (2 * ((m : Int) + 2) - 2) b)
              = (((2 * (m + 2) - 1 : Nat) : Complex) *
                  spinQCusp SpinPair.pp (2 * (m + 2) - 1)) •
                V.superVSqC a h (2 * ((m : Int) + 2) - 2) b := by
          intro m _
          rw [superSpinSpecializeCusp_tmul]
          change (((2 * (m + 2) - 1 : Nat) : Complex) *
              spinQ SpinPair.pp (2 * (m + 2) - 1) 0) • _ = _
          rw [spinQ_cusp]
        rw [Finset.sum_congr rfl hterm]
        exact Submodule.subset_span
          (Or.inl (Or.inl (Or.inr ⟨h, K, a, b, hsec, ha, hK, rfl⟩)))
      · obtain ⟨p, a, hp, hsec, rfl⟩ := hy
        rw [superSpinSpecializeCusp_include]
        exact Submodule.subset_span
          (Or.inl (Or.inr ⟨p, a, hp, hsec, rfl⟩))
      · obtain ⟨p, h, K, a, b, hp, hsec, ha, hK, rfl⟩ := hy
        rw [map_add, map_neg, superSpinSpecializeCusp_include, map_sum]
        have hterm : ∀ k ∈ Finset.range K,
            superSpinSpecializeCusp
                (spinQ p k ⊗ₜ[Complex] V.superVSqC a h (k : Int) b) =
              spinQCusp p k • V.superVSqC a h (k : Int) b := by
          intro k _
          rw [superSpinSpecializeCusp_tmul, spinQ_cusp]
        rw [Finset.sum_congr rfl hterm]
        exact Submodule.subset_span
          (Or.inr ⟨p, h, K, a, b, hp, hsec, ha, hK, rfl⟩)
  | zero => simp
  | add x y _ _ hx hy =>
      rw [map_add]
      exact (V.superSpinCuspRelSpan sector).add_mem hx hy
  | smul c x _ hx =>
      rw [map_smul]
      exact (V.superSpinCuspRelSpan sector).smul_mem c hx

theorem superSpinX1_mem {h : Complex} {a b : VType}
    (hsec : a ∈ sector SpinPair.pp) (ha : a ∈ V.grading h) :
    superSpinInclude (V.superVSqC a h 0 b) ∈ V.superSpinRelSpan sector := by
  apply Submodule.subset_span
  exact Or.inl (Or.inl (Or.inl ⟨h, a, b, hsec, ha, rfl⟩))

theorem superSpinKill_mem {p : SpinPair} (hp : p ≠ SpinPair.pp)
    {a : VType} (hsec : a ∈ sector p) :
    superSpinInclude a ∈ V.superSpinRelSpan sector := by
  apply Submodule.subset_span
  exact Or.inl (Or.inr ⟨p, a, hp, hsec, rfl⟩)

theorem superSpinCuspKill_mem {p : SpinPair} (hp : p ≠ SpinPair.pp)
    {a : VType} (hsec : a ∈ sector p) :
    a ∈ V.superSpinCuspRelSpan sector := by
  apply Submodule.subset_span
  exact Or.inl (Or.inr ⟨p, a, hp, hsec, rfl⟩)

/-- Every nontrivial simultaneous eigenspace is killed in the cusp quotient. -/
theorem sector_le_superSpinCuspRelSpan (p : SpinPair)
    (hp : p ≠ SpinPair.pp) :
    sector p ≤ V.superSpinCuspRelSpan sector := by
  intro a ha
  exact superSpinCuspKill_mem hp ha

/-- A finite family spanning modulo the explicit cusp relations makes the cusp quotient finite
dimensional and bounds its dimension.  This is the honest cusp-quotient analogue available at
this layer.  It does **not** claim that `C2`-cofiniteness alone supplies `T`: that requires the
sector-compatible half-weight `L[-1]` descent. -/
theorem finiteDimensional_superSpinCuspQuotient_of_span (T : Finset VType)
    (hspan : (⊤ : Submodule Complex VType) =
      Submodule.span Complex (T : Set VType) ⊔ V.superSpinCuspRelSpan sector) :
    FiniteDimensional Complex (VType ⧸ V.superSpinCuspRelSpan sector) ∧
      Module.finrank Complex (VType ⧸ V.superSpinCuspRelSpan sector) ≤ T.card :=
  finiteDimensional_and_finrank_quot_le_of_span_sup T hspan

end SuperNearVOA

end VOA
