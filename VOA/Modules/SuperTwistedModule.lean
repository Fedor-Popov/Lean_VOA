/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.SuperAutomorphism
import VOA.Core.SuperTranslationCovariance
import VOA.Modules.SuperOrdVModule
import VOA.Modules.Translation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Positive-energy twisted modules over a super VOA

This file is the super, grading-restricted counterpart of the honest carrier in
`Modularity.Twisted`.  For an even automorphism `g` and a positive exponent `N` with `g^N = 1`,
the integer label `k` on `YM u k` denotes the fractional mode `u_(k/N)`.  If `u` lies in the
`exp(-2πij/N)` eigenspace, only `k ≡ j (mod N)` may occur.

The conformal-weight grading and the module parity grading are independent.  The former is
complex-valued, finite on every piece, bounded below, diagonalises `L₀`, and obeys the exact
fractional weight shift.  The latter is an internal `ZMod 2` grading and modes add parities.  No
spin--statistics compatibility is assumed.

The twisted Jacobi identity uses exactly one new sign relative to the bosonic carrier: the
exchanged term is multiplied by `koszul p q`.  The fractional binomial and every index otherwise
agree with the Dong--Li--Mason mode formula already used in `Modularity.Twisted`.

No existence, irreducibility, rationality, or classification statement is made.  In particular,
the parity-twisted (Ramond, in this repository's convention) abbreviation below only packages a
possible carrier and proves its forced even/integer and odd/half-integer support pattern.

⚠⚠ **Defect: for `N ≥ 2` the structure `SuperTwistedModule` admits only the zero module.**  The
`jacobi` field is over-quantified: instantiated at `u = w = 𝟙`, `ℓ = -1`, `k = 1`, `m = -N-1`,
with `vacuum_YM`, it forces every `x : M` to be `0`.  Machine-checked (outside the library build)
as `L17Cert.superTwistedModule_eq_zero` in `Notes/Textbook/certificates/L17_Checks.lean`, with
the corollaries `superTwistedModule_weight_eq_bot` and `parityTwistedModule_eq_zero`.  So every
statement about a `SuperTwistedModule` with `N ≥ 2`, in particular every parity-twisted (Ramond)
carrier, is vacuous.  The repair is the one already made for the bosonic `TwistedModule`:
restrict `jacobi` to the admissible coset of mode labels.  Not yet done.
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Fractional eigenspaces and binomials -/

/-- The `exp(-2πij/N)` eigenspace of an even super-VOA automorphism. -/
noncomputable def SuperAut.twistedEigenspace {W : SuperVertexOperatorAlgebra 𝒱}
    (g : SuperAut W) (N : ℕ) (j : ℕ) : Submodule ℂ 𝒱 :=
  Module.End.eigenspace (g.toLinearEquiv : End ℂ 𝒱)
    (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * j) / N))

/-- The generalized binomial with complex upper index. -/
noncomputable def fractionalBinom (x : ℂ) (i : ℕ) : ℂ :=
  (∏ k ∈ Finset.range i, (x - k)) / (i.factorial : ℂ)

/-! ## Super module translation covariance -/

namespace SuperWeakModule

variable {W : SuperVertexOperatorAlgebra 𝒱} {M : Type v}
  [AddCommGroup M] [Module ℂ M]

/-- The zero-first-mode slice of super module Jacobi.  This is the super iterate formula; the
only sign relative to the bosonic formula is `koszul p q` on the exchanged term. -/
theorem module_iterate_zero (A : SuperWeakModule W.toSuperVertexAlgebra M)
    {p q : ZMod 2} (u : 𝒱) (hu : u ∈ W.parity p) (w : 𝒱) (hw : w ∈ W.parity q)
    (x : M) (ℓ n : ℤ) :
    mode (A.YM (W.smul u ℓ w)) n x =
      ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (mode (A.YM u) (ℓ - i) (mode (A.YM w) (n + i) x)
          - (koszul p q * negOnePow ℓ) •
            mode (A.YM w) (ℓ + n - i) (mode (A.YM u) i x)) := by
  have hjac := A.jacobi u hu w hw x ℓ 0 n
  have hrhs :
      (∑ᶠ i : ℤ, cbz 0 i • mode (A.YM (W.smul u (ℓ + i) w)) (0 + n - i) x) =
        mode (A.YM (W.smul u ℓ w)) n x := by
    rw [finsum_eq_single _ 0 (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_smul])]
    simp
  rw [hrhs] at hjac
  rw [← hjac]
  simp only [add_zero, zero_add]

/-- Module translation covariance for a parity-homogeneous state.  Since the vacuum is even,
the Koszul factor in the iterate formula is `koszul p 0 = 1`. -/
theorem act_T_covariance_homogeneous (A : SuperWeakModule W.toSuperVertexAlgebra M)
    {p : ZMod 2} (a : 𝒱) (ha : a ∈ W.parity p) (n : ℤ) (x : M) :
    A.act (W.L (-1) a) n x = (-(n : ℂ)) • A.act a (n - 1) x := by
  have hL : W.L (-1) a = W.smul a (-2) W.vacuum := by
    have hc := W.toSuperNearVOA.creation_powε a 1
    simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_smul, pow_one,
      show (-(1 : ℤ) - 1) = -2 by norm_num] at hc
    exact hc.symm
  have hvac : ∀ (k : ℤ) (y : M),
      mode (A.YM W.vacuum) k y = if k = -1 then y else 0 := by
    intro k y
    rw [← A.act_def]
    exact A.act_vacuum k y
  simp only [act_def]
  rw [hL, A.module_iterate_zero a ha W.vacuum W.vacuum_parity x (-2) n]
  simp only [koszul_zero_right, one_mul, hvac, smul_sub]
  rw [finsum_sub_distrib, finsum_eq_single _ (-1 - n), finsum_eq_single _ (n - 1)]
  · rw [show (n + (-1 - n) : ℤ) = -1 by ring, if_pos rfl,
      show (-2 - (-1 - n) : ℤ) = n - 1 by ring,
      show (-2 + n - (n - 1) : ℤ) = -1 by ring, if_pos rfl, smul_smul, ← sub_smul,
      cov_scalar]
  · intro i hi
    rw [if_neg (show ¬(-2 + n - i = -1) by omega), smul_zero, smul_zero]
  · intro i hi
    rw [if_neg (show ¬(n + i = -1) by omega), map_zero, smul_zero]
  · apply Set.Finite.subset (Set.finite_singleton (-1 - n))
    intro i hi
    simp only [Function.mem_support, Set.mem_singleton_iff] at hi ⊢
    by_contra hne
    exact hi (by rw [if_neg (show ¬(n + i = -1) by omega), map_zero, smul_zero])
  · apply Set.Finite.subset (Set.finite_singleton (n - 1))
    intro i hi
    simp only [Function.mem_support, Set.mem_singleton_iff] at hi ⊢
    by_contra hne
    exact hi (by rw [if_neg (show ¬(-2 + n - i = -1) by omega), smul_zero, smul_zero])

/-- Module translation covariance for an arbitrary state, obtained by splitting it into its even
and odd parts. -/
theorem act_T_covariance (A : SuperWeakModule W.toSuperVertexAlgebra M)
    (a : 𝒱) (n : ℤ) (x : M) :
    A.act (W.L (-1) a) n x = (-(n : ℂ)) • A.act a (n - 1) x := by
  let P : ParityGrading 𝒱 := ⟨W.parity, W.parity_isInternal⟩
  obtain ⟨a₀, ha₀, a₁, ha₁, ha⟩ := P.exists_parity_decomp a
  rw [← ha, map_add, A.act_add_left, A.act_add_left, smul_add,
    A.act_T_covariance_homogeneous a₀ ha₀ n x,
    A.act_T_covariance_homogeneous a₁ ha₁ n x]

end SuperWeakModule

/-! ## The positive-energy twisted carrier -/

/-- A positive-energy `g`-twisted module over a super VOA.

⚠⚠ **Vacuous for `N ≥ 2`: only the zero module satisfies this structure** (the `jacobi` field is
over-quantified; see the module docstring and `L17Cert.superTwistedModule_eq_zero` in
`Notes/Textbook/certificates/L17_Checks.lean`).

`N` is a chosen positive exponent for `g`, not asserted to be its minimal order.  This is the
right amount of data for the `1/N` mode lattice: replacing `N` by a positive multiple merely
refines the integer labels. -/
structure SuperTwistedModule (W : SuperVertexOperatorAlgebra 𝒱) (g : SuperAut W)
    (N : ℕ) (M : Type v) [AddCommGroup M] [Module ℂ M] where
  /-- The chosen denominator is positive. -/
  order_pos : 0 < N
  /-- The chosen denominator is an exponent of `g`. -/
  order_pow : g ^ N = 1
  /-- Fractional modes: the integer label `k` denotes mode number `k/N`. -/
  YM : 𝒱 →ₗ[ℂ] (ℤ → End ℂ M)
  /-- The internal module parity grading. -/
  parity : ZMod 2 → Submodule ℂ M
  parity_isInternal : DirectSum.IsInternal parity
  /-- A mode of a parity-`p` state sends module parity `q` to `p+q`. -/
  parity_mode : ∀ {p q : ZMod 2} (u : 𝒱), u ∈ W.parity p →
    ∀ (x : M), x ∈ parity q → ∀ (k : ℤ), YM u k x ∈ parity (p + q)
  /-- The vacuum has only mode `-1`, represented by integer label `-N`. -/
  vacuum_YM : ∀ k : ℤ, YM W.vacuum k = if k = -(N : ℤ) then 1 else 0
  /-- Lower truncation in the fractional-mode label. -/
  truncation : ∀ (u : 𝒱) (x : M), ∃ K : ℤ, ∀ k : ℤ, K ≤ k → YM u k x = 0
  /-- Eigenspace support: `u ∈ V^j` has modes only at `k ≡ j (mod N)`.  ⚠ **Convention differs
  from the bosonic `TwistedModule.support`** (`Modularity/Twisted.lean`), which uses `k ≡ −j`
  with the same eigenspace `V^j = {v | g v = ξ_N^{−j} v}`.  Any coset restriction added to
  `jacobi` must use the super sign `(k - j) % N = 0`. -/
  support : ∀ (j : ℕ) (u : 𝒱), u ∈ g.twistedEigenspace N j →
    ∀ k : ℤ, (k - j) % (N : ℤ) ≠ 0 → YM u k = 0
  /-- The full Koszul twisted Jacobi identity in fractional-mode form. -/
  jacobi : ∀ {p q : ZMod 2} (j : ℕ) (u : 𝒱),
    u ∈ g.twistedEigenspace N j → u ∈ W.parity p →
    ∀ (w : 𝒱), w ∈ W.parity q → ∀ (x : M) (ℓ k m : ℤ),
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (YM u (ℓ * N + k - i * N) (YM w (m + i * N) x)
          - (koszul p q * negOnePow ℓ) •
            YM w (ℓ * N + m - i * N) (YM u (k + i * N) x))) =
      ∑ᶠ i : ℕ, fractionalBinom ((k : ℂ) / N) i •
        YM (W.smul u (ℓ + i) w) (k + m - i * N) x
  /-- Translation covariance at fractional index `k/N`. -/
  translation : ∀ (u : 𝒱) (k : ℤ),
    YM (W.L (-1) u) k = (-((k : ℂ) / N)) • YM u (k - N)
  /-- The complex conformal-weight grading. -/
  weight : ℂ → Submodule ℂ M
  weight_isInternal : DirectSum.IsInternal weight
  /-- `L₀ = omega_(1)` is fractional label `N`. -/
  L0_weight : ∀ (α : ℂ) (x : M), x ∈ weight α →
    YM W.conformalVector N x = α • x
  /-- Every weight piece is finite-dimensional. -/
  weight_finite : ∀ α, FiniteDimensional ℂ (weight α)
  /-- The occurring weights are bounded below in real part. -/
  boundedBelow : ∃ B : ℝ, ∀ α : ℂ, weight α ≠ ⊥ → B ≤ α.re
  /-- Exact fractional homogeneous weight shift. -/
  weight_mode : ∀ {h α : ℂ} (u : 𝒱), u ∈ W.grading h →
    ∀ (x : M), x ∈ weight α → ∀ (k : ℤ),
      YM u k x ∈ weight (α + h - (k : ℂ) / N - 1)

namespace SuperTwistedModule

variable {W : SuperVertexOperatorAlgebra 𝒱} {g : SuperAut W} {N : ℕ}
  {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- Fractional-mode action. -/
def act (T : SuperTwistedModule W g N M) (u : 𝒱) (k : ℤ) (x : M) : M := T.YM u k x

@[simp] theorem act_def (T : SuperTwistedModule W g N M) (u : 𝒱) (k : ℤ) (x : M) :
    T.act u k x = T.YM u k x := rfl

/-- The module parity grading, packaged separately from conformal weight. -/
def toParityGrading (T : SuperTwistedModule W g N M) : ParityGrading M where
  parity := T.parity
  isInternal := T.parity_isInternal

/-- Parity of a homogeneous fractional mode. -/
theorem act_parity (T : SuperTwistedModule W g N M) {p q : ZMod 2}
    {u : 𝒱} (hu : u ∈ W.parity p) {x : M} (hx : x ∈ T.parity q) (k : ℤ) :
    T.act u k x ∈ T.parity (p + q) := T.parity_mode u hu x hx k

/-- Weight of a homogeneous fractional mode. -/
theorem act_weight (T : SuperTwistedModule W g N M) {h α : ℂ}
    {u : 𝒱} (hu : u ∈ W.grading h) {x : M} (hx : x ∈ T.weight α) (k : ℤ) :
    T.act u k x ∈ T.weight (α + h - (k : ℂ) / N - 1) :=
  T.weight_mode u hu x hx k

end SuperTwistedModule

/-! ## Centralizer intertwiners -/

/-- A chosen parity-homogeneous, weight-preserving lift of an automorphism `h` commuting with
`g` to a `g`-twisted module.  Its parity degree is explicit: odd implementers are needed for
the queer sectors in van Ekeren's trace theory.  Such a lift is extra (often projective) data;
no existence is asserted. -/
structure SuperTwistedIntertwiner {W : SuperVertexOperatorAlgebra 𝒱} {g : SuperAut W}
    {N : ℕ} {M : Type v} [AddCommGroup M] [Module ℂ M]
    (T : SuperTwistedModule W g N M) (h : SuperAut W) where
  commutes : h * g = g * h
  toLinearEquiv : M ≃ₗ[ℂ] M
  parityDegree : ZMod 2
  map_parity' : ∀ (p : ZMod 2) (x : M),
    toLinearEquiv x ∈ T.parity (parityDegree + p) ↔ x ∈ T.parity p
  map_weight' : ∀ (α : ℂ) (x : M),
    toLinearEquiv x ∈ T.weight α ↔ x ∈ T.weight α
  intertwines : ∀ (u : 𝒱) (k : ℤ) (x : M),
    toLinearEquiv (T.act u k x) = T.act (h u) k (toLinearEquiv x)

namespace SuperTwistedIntertwiner

variable {W : SuperVertexOperatorAlgebra 𝒱} {g : SuperAut W} {N : ℕ}
  {M : Type v} [AddCommGroup M] [Module ℂ M]
  {T : SuperTwistedModule W g N M} {h : SuperAut W}

instance : CoeFun (SuperTwistedIntertwiner T h) (fun _ => M → M) :=
  ⟨fun φ => φ.toLinearEquiv⟩

/-- The underlying endomorphism used as a trace insertion. -/
def toEnd (φ : SuperTwistedIntertwiner T h) : End ℂ M := φ.toLinearEquiv.toLinearMap

/-- The intertwiner commutes with `L₀`, since `h` fixes the conformal vector. -/
theorem map_L0 (φ : SuperTwistedIntertwiner T h) (x : M) :
    φ (T.YM W.conformalVector N x) = T.YM W.conformalVector N (φ x) := by
  simpa [SuperTwistedModule.act_def, h.map_omega] using φ.intertwines W.conformalVector N x

/-- On an `h`-fixed state, the lifted operator commutes with every fractional mode. -/
theorem toEnd_mul_mode_of_fixed (φ : SuperTwistedIntertwiner T h)
    {u : 𝒱} (hu : h u = u) (k : ℤ) :
    φ.toEnd * T.YM u k = T.YM u k * φ.toEnd := by
  apply LinearMap.ext
  intro x
  change φ (T.act u k x) = T.act u k (φ x)
  rw [φ.intertwines, hu]

end SuperTwistedIntertwiner

/-! ## Identity twist -/

namespace SuperOrdVModule

variable {W : SuperVertexOperatorAlgebra 𝒱} {M : Type v}
  [AddCommGroup M] [Module ℂ M]

/-- An ordinary supermodule is a positive-energy identity-twisted module with denominator one. -/
noncomputable def toIdentityTwist (A : SuperOrdVModule W M) :
    SuperTwistedModule W (1 : SuperAut W) 1 M where
  order_pos := by norm_num
  order_pow := by simp
  YM :=
    { toFun := fun u k => mode (A.YM u) k
      map_add' := fun u w => by funext k; rw [map_add, mode_add]; rfl
      map_smul' := fun c u => by funext k; rw [map_smul, mode_smul]; rfl }
  parity := A.parity
  parity_isInternal := A.parity_isInternal
  parity_mode := fun u hu x hx k => A.parity_mode u hu x hx k
  vacuum_YM := fun k => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, A.vacuum_YM, mode_one, Nat.cast_one]
  truncation := fun u x => A.truncation u x
  support := fun j u _ k hk => by
    exfalso
    apply hk
    simp
  jacobi := by
    intro p q j u _ hu w hw x ℓ k m
    have h := A.jacobi u hu w hw x ℓ k m
    simp only [Nat.cast_one, mul_one, LinearMap.coe_mk, AddHom.coe_mk, div_one]
    rw [h, ← finsum_mem_univ,
      finsum_mem_inter_support_eq' _ Set.univ (Set.range (Nat.cast : ℕ → ℤ)),
      finsum_mem_range Nat.cast_injective]
    · refine finsum_congr (fun i => ?_)
      rw [cbz_apply_nonneg _ (by positivity), Int.toNat_natCast]
      rfl
    · intro i hi
      simp only [Set.mem_univ, Set.mem_range, true_iff]
      rw [Function.mem_support] at hi
      by_cases h0 : 0 ≤ i
      · exact ⟨i.toNat, by omega⟩
      · exact absurd (by rw [cbz_apply_neg _ (not_le.mp h0), zero_smul]) hi
  translation := fun u k => by
    apply LinearMap.ext
    intro x
    simpa [SuperWeakModule.act_def] using
      A.toSuperWeakModule.act_T_covariance u k x
  weight := A.weight
  weight_isInternal := A.weight_isInternal
  L0_weight := fun α x hx => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Nat.cast_one]
    exact A.L0_weight α x hx
  weight_finite := A.weight_finite
  boundedBelow := A.boundedBelow
  weight_mode := by
    intro h α u hu x hx k
    simpa only [Nat.cast_one, div_one] using A.weight_mode u hu x hx k

@[simp] theorem toIdentityTwist_act (A : SuperOrdVModule W M)
    (u : 𝒱) (k : ℤ) (x : M) : A.toIdentityTwist.act u k x = A.act u k x := by
  simp [toIdentityTwist, SuperTwistedModule.act, SuperOrdVModule.act,
    SuperWeakModule.act]

@[simp] theorem toIdentityTwist_weight (A : SuperOrdVModule W M) (α : ℂ) :
    A.toIdentityTwist.weight α = A.weight α := by
  simp [toIdentityTwist]

end SuperOrdVModule

/-! ## The parity-twisted (Ramond) support shape -/

namespace SuperVertexOperatorAlgebra

variable {W : SuperVertexOperatorAlgebra 𝒱}

/-- A possible parity-twisted module.  In the repository convention this is the Ramond carrier.
The abbreviation asserts no existence.  ⚠⚠ With `N = 2` it is a `SuperTwistedModule`, so **only
the zero module** satisfies it (`L17Cert.parityTwistedModule_eq_zero`,
`Notes/Textbook/certificates/L17_Checks.lean`). -/
abbrev ParityTwistedModule (W : SuperVertexOperatorAlgebra 𝒱) (M : Type v)
    [AddCommGroup M] [Module ℂ M] := SuperTwistedModule W W.parityAut 2 M

/-- Even states lie in the `j=0` eigenspace of the parity automorphism. -/
theorem mem_parityAut_eigenspace_zero (W : SuperVertexOperatorAlgebra 𝒱)
    {u : 𝒱} (hu : u ∈ W.parity 0) : u ∈ W.parityAut.twistedEigenspace 2 0 := by
  rw [SuperAut.twistedEigenspace, Module.End.mem_eigenspace_iff]
  change W.parityAut u = _
  rw [W.parityAut_homog hu, parSign_zero]
  simp

/-- Odd states lie in the `j=1` eigenspace of the parity automorphism. -/
theorem mem_parityAut_eigenspace_one (W : SuperVertexOperatorAlgebra 𝒱)
    {u : 𝒱} (hu : u ∈ W.parity 1) : u ∈ W.parityAut.twistedEigenspace 2 1 := by
  rw [SuperAut.twistedEigenspace, Module.End.mem_eigenspace_iff]
  change W.parityAut u = _
  rw [W.parityAut_homog hu, parSign_one]
  have hexp : Complex.exp
      (-(2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ)) / ((2 : ℕ) : ℂ)) = -1 := by
    rw [show (-(2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ)) / ((2 : ℕ) : ℂ)) =
      -((Real.pi : ℂ) * Complex.I) by ring]
    exact Complex.exp_neg_pi_mul_I
  rw [hexp, neg_one_smul]

/-- In a parity-twisted carrier, an even state has only even integer labels, hence integral
fractional modes `k/2`. -/
theorem parityTwist_even_support {M : Type v} [AddCommGroup M] [Module ℂ M]
    (T : W.ParityTwistedModule M) {u : 𝒱} (hu : u ∈ W.parity 0) (k : ℤ)
    (hk : k % 2 ≠ 0) : T.YM u k = 0 := by
  apply T.support 0 u (W.mem_parityAut_eigenspace_zero hu) k
  simpa using hk

/-- In a parity-twisted carrier, an odd state has only odd integer labels, hence half-integral
fractional modes `k/2`.  Together with the even theorem this is the algebraic Ramond-sector
support statement in the repository convention. -/
theorem parityTwist_odd_support {M : Type v} [AddCommGroup M] [Module ℂ M]
    (T : W.ParityTwistedModule M) {u : 𝒱} (hu : u ∈ W.parity 1) (k : ℤ)
    (hk : (k + 1) % 2 ≠ 0) : T.YM u k = 0 := by
  apply T.support 1 u (W.mem_parityAut_eigenspace_one hu) k
  intro hzero
  apply hk
  omega

/-! The order-three checks below make the sign convention observable.  For the
`exp(-2*pi*I/3)` eigenspace, label `1` is the allowed residue class, while labels `0` and `2`
are forced to vanish. -/

/-- In the first nontrivial order-three eigenspace, label zero is outside the support. -/
theorem twist_three_eigenspace_one_label_zero
    {g : SuperAut W} {M : Type v} [AddCommGroup M] [Module ℂ M]
    (T : SuperTwistedModule W g 3 M) {u : 𝒱}
    (hu : u ∈ g.twistedEigenspace 3 1) : T.YM u 0 = 0 := by
  apply T.support 1 u hu 0
  norm_num

/-- In the first nontrivial order-three eigenspace, label two is outside the support. -/
theorem twist_three_eigenspace_one_label_two
    {g : SuperAut W} {M : Type v} [AddCommGroup M] [Module ℂ M]
    (T : SuperTwistedModule W g 3 M) {u : 𝒱}
    (hu : u ∈ g.twistedEigenspace 3 1) : T.YM u 2 = 0 := by
  apply T.support 1 u hu 2
  norm_num

/-- In the second nontrivial order-three eigenspace, label one is outside the support. -/
theorem twist_three_eigenspace_two_label_one
    {g : SuperAut W} {M : Type v} [AddCommGroup M] [Module ℂ M]
    (T : SuperTwistedModule W g 3 M) {u : 𝒱}
    (hu : u ∈ g.twistedEigenspace 3 2) : T.YM u 1 = 0 := by
  apply T.support 2 u hu 1
  norm_num

end SuperVertexOperatorAlgebra

end VOA
