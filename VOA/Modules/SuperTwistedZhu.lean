/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.SuperTwistedModule
import VOA.Modules.SuperZhuRing

/-!
# Finite-order twisted super Zhu algebras

This file isolates the algebraic content of Dong--Zhao's twisted Zhu construction for a
`Z`-graded super VOA.  Weight and parity remain independent.  If `u` has integral weight `k`
and lies in the `exp(-2*pi*I*r/N)` eigenspace, its circle residue is

`sum_i C(k - 1 + delta_r + r/N, i) u_(i-1-delta_r) v`,

where `delta_r` is one for `r = 0` and zero otherwise.  The product uses only the fixed part of
its left input and is the ordinary super Zhu product there.

The fixed part is selected canonically by the Reynolds average.  This avoids choosing an
eigenbasis or hiding diagonalizability in the definition.  The defining subspace is presented
by fixed-sector circle generators and by the displayed residues on the nonzero eigenspaces.
At the identity twist this presentation is definitionally tied to `superO`, so its quotient and
product agree with the untwisted construction.

The genuinely twisted residue consequences needed for the two-sided-ideal, associativity, right
unit, and bottom-space theorems are packaged in the explicit proposition
`SuperTwistedZhuRingData`.  No such result is asserted merely from finite order.  In particular,
this file makes no existence, classification, rationality, or semisimplicity claim.
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The homogeneous Dong--Zhao residue -/

/-- `delta_r` in Dong--Zhao: one in the fixed sector and zero otherwise. -/
def twistedZhuDelta (r : ℕ) : ℕ := if r = 0 then 1 else 0

@[simp] theorem twistedZhuDelta_zero : twistedZhuDelta 0 = 1 := rfl

theorem twistedZhuDelta_ne_zero {r : ℕ} (hr : r ≠ 0) : twistedZhuDelta r = 0 :=
  if_neg hr

/-- The upper binomial exponent `wt u - 1 + delta_r + r/N`.  No parity enters it. -/
noncomputable def twistedZhuExponent (N r : ℕ) (k : ℤ) : ℂ :=
  (k : ℂ) - 1 + twistedZhuDelta r + (r : ℂ) / (N : ℂ)

@[simp] theorem twistedZhuExponent_fixed (N : ℕ) (k : ℤ) :
    twistedZhuExponent N 0 k = (k : ℂ) := by
  simp [twistedZhuExponent]

/-- On integral upper indices the complex coefficient is the repository's ordinary generalized
binomial coefficient. -/
theorem fractionalBinom_intCast (k : ℤ) (i : ℕ) :
    fractionalBinom (k : ℂ) i = gBinom k i := rfl

/-- The homogeneous twisted circle residue.  Regularity makes the displayed `finsum` finite on
every pair of inputs, including when the complex binomial series itself is infinite. -/
noncomputable def twistedZhuCircleHom (W : SuperVertexOperatorAlgebra 𝒱)
    (N r : ℕ) (k : ℤ) (u v : 𝒱) : 𝒱 :=
  ∑ᶠ i : ℕ, fractionalBinom (twistedZhuExponent N r k) i •
    W.smul u ((i : ℤ) - 1 - (twistedZhuDelta r : ℤ)) v

/-- In the fixed sector the circle has the ordinary Zhu exponent and pole order two. -/
theorem twistedZhuCircleHom_fixed (W : SuperVertexOperatorAlgebra 𝒱)
    (N : ℕ) (k : ℤ) (u v : 𝒱) :
    twistedZhuCircleHom W N 0 k u v =
      ∑ᶠ i : ℕ, fractionalBinom (k : ℂ) i • W.smul u ((i : ℤ) - 2) v := by
  simp only [twistedZhuCircleHom, twistedZhuExponent_fixed, twistedZhuDelta_zero]
  congr 1
  funext i
  congr 2
  omega

/-- The parity-twist nonfixed sector has exponent `k - 1/2`, denominator `z`, and modes
`i-1`.  This is a twist shift, not a parity/weight compatibility assertion. -/
theorem twistedZhuCircleHom_parity_halfShift (W : SuperVertexOperatorAlgebra 𝒱)
    (k : ℤ) (u v : 𝒱) :
    twistedZhuCircleHom W 2 1 k u v =
      ∑ᶠ i : ℕ, fractionalBinom ((k : ℂ) - (1 / 2 : ℂ)) i •
        W.smul u ((i : ℤ) - 1) v := by
  have hdelta : twistedZhuDelta 1 = 0 := twistedZhuDelta_ne_zero (by norm_num)
  simp only [twistedZhuCircleHom, twistedZhuExponent, hdelta, Nat.cast_one, Nat.cast_ofNat,
    Nat.cast_zero, sub_zero, add_zero]
  congr 1
  funext i
  congr 2
  ring

/-- A `finsum` of vectors in a submodule remains in the submodule.  This statement also handles
the deliberately total `finsum` convention when support is infinite. -/
private theorem finsum_mem_submodule {ι : Type*} (P : Submodule ℂ 𝒱) (F : ι → 𝒱)
    (hF : ∀ i, F i ∈ P) : (∑ᶠ i, F i) ∈ P := by
  by_cases hfin : (Function.support F).Finite
  · rw [finsum_eq_finsetSum_of_support_subset F (s := hfin.toFinset)
      (fun i hi => hfin.mem_toFinset.mpr hi)]
    exact Submodule.sum_mem _ (fun i _ => hF i)
  · rw [finsum_of_infinite_support (by rwa [Set.not_finite] at hfin)]
    exact P.zero_mem

/-- Circle residues add the parities of their two inputs.  The fractional exponent is irrelevant
to the Koszul grading because no states are exchanged in a residue. -/
theorem twistedZhuCircleHom_mem_parity (W : SuperVertexOperatorAlgebra 𝒱)
    {p q : ZMod 2} {u v : 𝒱} (hu : u ∈ W.parity p) (hv : v ∈ W.parity q)
    (N r : ℕ) (k : ℤ) : twistedZhuCircleHom W N r k u v ∈ W.parity (p + q) := by
  apply finsum_mem_submodule
  intro i
  exact Submodule.smul_mem _ _ (W.smul_mem_parity hu hv _)

/-! ## The canonical fixed projection and twisted product -/

/-- The Reynolds average `(1/N) sum_{a=0}^{N-1} g^a`.  It is defined for every `N`; its
projection properties require the explicit hypothesis `0 < N` and `g^N = 1`. -/
noncomputable def SuperAut.fixedAverage {W : SuperVertexOperatorAlgebra 𝒱}
    (g : SuperAut W) (N : ℕ) : 𝒱 →ₗ[ℂ] 𝒱 :=
  ((N : ℂ)⁻¹) • ∑ a ∈ Finset.range N, (g ^ a).toLinearEquiv.toLinearMap

@[simp] theorem SuperAut.fixedAverage_identity
    (W : SuperVertexOperatorAlgebra 𝒱) (u : 𝒱) :
    (1 : SuperAut W).fixedAverage 1 u = u := by
  simp [SuperAut.fixedAverage]

/-- The Reynolds average preserves internal parity because every power of an even automorphism
does. -/
theorem SuperAut.fixedAverage_mem_parity {W : SuperVertexOperatorAlgebra 𝒱}
    (g : SuperAut W) (N : ℕ) {p : ZMod 2} {u : 𝒱} (hu : u ∈ W.parity p) :
    g.fixedAverage N u ∈ W.parity p := by
  rw [SuperAut.fixedAverage, LinearMap.smul_apply]
  apply Submodule.smul_mem
  rw [LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun a _ => (g ^ a).map_mem_parity hu

/-- A positive-length Reynolds average fixes the vacuum. -/
theorem SuperAut.fixedAverage_vacuum {W : SuperVertexOperatorAlgebra 𝒱}
    (g : SuperAut W) {N : ℕ} (hN : 0 < N) :
    g.fixedAverage N W.vacuum = W.vacuum := by
  rw [SuperAut.fixedAverage, LinearMap.smul_apply, LinearMap.sum_apply]
  change ((N : ℂ)⁻¹) • (∑ a ∈ Finset.range N, (g ^ a) W.vacuum) = W.vacuum
  have hsum : (∑ a ∈ Finset.range N, (g ^ a) W.vacuum) =
      ∑ _a ∈ Finset.range N, W.vacuum := by
    exact Finset.sum_congr rfl fun a _ => (g ^ a).map_vacuum
  rw [hsum, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast Nat.ne_of_gt hN), one_smul]

/-- The Reynolds average fixes a vector already fixed by the automorphism. -/
theorem SuperAut.fixedAverage_of_fixed {W : SuperVertexOperatorAlgebra 𝒱}
    (g : SuperAut W) {N : ℕ} (hN : 0 < N) {u : 𝒱} (hu : g u = u) :
    g.fixedAverage N u = u := by
  rw [SuperAut.fixedAverage, LinearMap.smul_apply, LinearMap.sum_apply]
  change ((N : ℂ)⁻¹) • (∑ a ∈ Finset.range N, (g ^ a) u) = u
  have hp : ∀ a : ℕ, (g ^ a) u = u := by
    intro a
    induction a with
    | zero => simp
    | succ a ih =>
      rw [pow_succ, SuperAut.mul_apply]
      rw [hu, ih]
  rw [Finset.sum_congr rfl (fun a _ => hp a), Finset.sum_const, Finset.card_range,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast Nat.ne_of_gt hN), one_smul]

/-- The sector `r=0` eigenspace is fixed pointwise by its Reynolds average. -/
theorem SuperAut.fixedAverage_eigenspace_zero {W : SuperVertexOperatorAlgebra 𝒱}
    (g : SuperAut W) {N : ℕ} (hN : 0 < N) {u : 𝒱}
    (hu : u ∈ g.twistedEigenspace N 0) : g.fixedAverage N u = u := by
  apply g.fixedAverage_of_fixed hN
  rw [SuperAut.twistedEigenspace, Module.End.mem_eigenspace_iff] at hu
  simpa using hu

/-- The twisted Zhu product: take the fixed part of the left input and apply the ordinary
Dong--Zhao/Zhu product. -/
noncomputable def SuperVertexOperatorAlgebra.twistedZhuMul
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) (u v : 𝒱) : 𝒱 :=
  W.toSuperNearVOA.superZhuMul hW (g.fixedAverage N u) v

/-- Dong--Zhao's product on a state whose eigensector is explicitly known: ordinary Zhu product
in sector zero, and zero in every nonfixed sector. -/
noncomputable def SuperVertexOperatorAlgebra.twistedZhuMulHom
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (r : ℕ) (u v : 𝒱) : 𝒱 :=
  if r = 0 then W.toSuperNearVOA.superZhuMul hW u v else 0

@[simp] theorem SuperVertexOperatorAlgebra.twistedZhuMulHom_fixed
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (u v : 𝒱) : W.twistedZhuMulHom hW 0 u v =
      W.toSuperNearVOA.superZhuMul hW u v := rfl

theorem SuperVertexOperatorAlgebra.twistedZhuMulHom_nonfixed
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    {r : ℕ} (hr : r ≠ 0) (u v : 𝒱) : W.twistedZhuMulHom hW r u v = 0 := by
  simp [SuperVertexOperatorAlgebra.twistedZhuMulHom, hr]

/-- The canonical averaged product agrees with the sector-zero formula on fixed eigenvectors. -/
theorem SuperVertexOperatorAlgebra.twistedZhuMul_of_eigenspace_zero
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) {N : ℕ} (hN : 0 < N) {u : 𝒱}
    (hu : u ∈ g.twistedEigenspace N 0) (v : 𝒱) :
    W.twistedZhuMul hW g N u v = W.twistedZhuMulHom hW 0 u v := by
  rw [SuperVertexOperatorAlgebra.twistedZhuMul,
    g.fixedAverage_eigenspace_zero hN hu,
    SuperVertexOperatorAlgebra.twistedZhuMulHom_fixed]

/-- Exact bridge for a nonfixed homogeneous state.  Its only premise is the elementary Reynolds
average vanishing statement; no residue or module theorem is hidden here. -/
theorem SuperVertexOperatorAlgebra.twistedZhuMul_of_nonfixed_average
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) {r : ℕ} (hr : r ≠ 0) {u : 𝒱}
    (hu : g.fixedAverage N u = 0) (v : 𝒱) :
    W.twistedZhuMul hW g N u v = W.twistedZhuMulHom hW r u v := by
  rw [SuperVertexOperatorAlgebra.twistedZhuMul, hu,
    SuperVertexOperatorAlgebra.twistedZhuMulHom_nonfixed W hW hr]
  change W.toSuperNearVOA.superZhuMulₗ hW 0 v = 0
  rw [map_zero, LinearMap.zero_apply]

/-- Identity twist gives exactly the untwisted super Zhu product. -/
@[simp] theorem SuperVertexOperatorAlgebra.twistedZhuMul_identity
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (u v : 𝒱) :
    W.twistedZhuMul hW (1 : SuperAut W) 1 u v =
      W.toSuperNearVOA.superZhuMul hW u v := by
  rw [SuperVertexOperatorAlgebra.twistedZhuMul, SuperAut.fixedAverage_identity]

/-- The twisted product is bilinear, exposed in the form needed for quotient descent. -/
noncomputable def SuperVertexOperatorAlgebra.twistedZhuMulₗ
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] 𝒱 :=
  (W.toSuperNearVOA.superZhuMulₗ hW).comp (g.fixedAverage N)

@[simp] theorem SuperVertexOperatorAlgebra.twistedZhuMulₗ_apply
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) (u v : 𝒱) :
    W.twistedZhuMulₗ hW g N u v = W.twistedZhuMul hW g N u v := rfl

/-- The twisted product respects parity. -/
theorem SuperVertexOperatorAlgebra.twistedZhuMul_mem_parity
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) {p q : ZMod 2} {u v : 𝒱}
    (hu : u ∈ W.parity p) (hv : v ∈ W.parity q) :
    W.twistedZhuMul hW g N u v ∈ W.parity (p + q) :=
  W.toSuperNearVOA.superZhuMul_mem_parity hW (g.fixedAverage_mem_parity N hu) hv

/-! ## `O_g`, `A_g`, and the exact residue gate -/

/-- Fixed-sector circle generators, written in the equivalent `(L_-1+L_0)*v` form.
Using this form makes identity-twist coherence exact rather than dependent on a second proof that
the two standard presentations of ordinary `O(V)` agree. -/
def SuperVertexOperatorAlgebra.twistedZhuFixedGeneratorSet
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
  (g : SuperAut W) (N : ℕ) : Set 𝒱 :=
  {x | ∃ u v : 𝒱, x = W.toSuperNearVOA.superZhuMul hW
    (W.toSuperNearVOA.L (-1) (g.fixedAverage N u) +
      W.toSuperNearVOA.L 0 (g.fixedAverage N u)) v}

/-- Nonfixed Dong--Zhao circle generators, with both conformal weight and eigensector hypotheses
kept explicit. -/
def SuperVertexOperatorAlgebra.twistedZhuNonfixedGeneratorSet
    (W : SuperVertexOperatorAlgebra 𝒱) (g : SuperAut W) (N : ℕ) : Set 𝒱 :=
  {x | ∃ (r : Fin N) (k : ℤ) (u v : 𝒱), r.1 ≠ 0 ∧
    u ∈ W.toSuperNearVOA.gradingZ k ∧ u ∈ g.twistedEigenspace N r.1 ∧
    x = twistedZhuCircleHom W N r.1 k u v}

/-- The twisted Zhu relation space `O_g(V)`.  Finite-order diagonalizability is not used in this
definition: fixed vectors are reached through the Reynolds average and nonfixed eigenvectors are
listed explicitly. -/
def SuperVertexOperatorAlgebra.twistedO
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ (W.twistedZhuFixedGeneratorSet hW g N ∪
    W.twistedZhuNonfixedGeneratorSet g N)

/-- Every displayed fixed-sector relation lies in `O_g`. -/
theorem SuperVertexOperatorAlgebra.twistedO_fixed_mem
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) (u v : 𝒱) :
    W.toSuperNearVOA.superZhuMul hW
      (W.toSuperNearVOA.L (-1) (g.fixedAverage N u) +
        W.toSuperNearVOA.L 0 (g.fixedAverage N u)) v ∈ W.twistedO hW g N := by
  apply Submodule.subset_span
  left
  exact ⟨u, v, rfl⟩

/-- Every displayed nonfixed homogeneous circle residue lies in `O_g`. -/
theorem SuperVertexOperatorAlgebra.twistedO_nonfixed_mem
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) {N : ℕ} (r : Fin N) {k : ℤ} {u v : 𝒱}
    (hr : r.1 ≠ 0) (hk : u ∈ W.toSuperNearVOA.gradingZ k)
    (heig : u ∈ g.twistedEigenspace N r.1) :
    twistedZhuCircleHom W N r.1 k u v ∈ W.twistedO hW g N := by
  apply Submodule.subset_span
  right
  exact ⟨r, k, u, v, hr, hk, heig, rfl⟩

/-- Identity twist has no nonfixed sector and its fixed average is the identity, hence `O_1` is
exactly the untwisted `superO`. -/
theorem SuperVertexOperatorAlgebra.twistedO_identity
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights) :
    W.twistedO hW (1 : SuperAut W) 1 = W.toSuperNearVOA.superO hW := by
  apply le_antisymm
  · rw [SuperVertexOperatorAlgebra.twistedO, Submodule.span_le]
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨u, v, rfl⟩ := hx
      simp only [SuperAut.fixedAverage_identity]
      exact W.toSuperNearVOA.superO_mem_of_L hW u v
    · obtain ⟨r, _, _, _, hr, _⟩ := hx
      exact absurd (congrArg Fin.val (Fin.eq_zero r)) hr
  · rw [SuperNearVOA.superO, Submodule.span_le]
    intro x hx
    obtain ⟨u, v, rfl⟩ := hx
    apply Submodule.subset_span
    left
    exact ⟨u, v, by simp only [SuperAut.fixedAverage_identity]⟩

/-- The twisted Zhu quotient `A_g(V)`. -/
abbrev SuperVertexOperatorAlgebra.twistedA
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) : Type u := 𝒱 ⧸ W.twistedO hW g N

/-- The quotient map `V -> A_g(V)`. -/
def SuperVertexOperatorAlgebra.twistedMk
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) : 𝒱 →ₗ[ℂ] W.twistedA hW g N :=
  (W.twistedO hW g N).mkQ

/-- The candidate unit `[vacuum]`. -/
def SuperVertexOperatorAlgebra.twistedOne
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) : W.twistedA hW g N :=
  W.twistedMk hW g N W.vacuum

/-- The parity-`p` image in the twisted quotient.  This definition does not by itself assert
that the two images form a direct sum; that further statement is exactly the parity-stability
of `O_g`. -/
def SuperVertexOperatorAlgebra.twistedAParity
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) (p : ZMod 2) : Submodule ℂ (W.twistedA hW g N) :=
  (W.parity p).map (W.twistedMk hW g N)

/-- A parity-homogeneous state maps to its corresponding quotient parity image. -/
theorem SuperVertexOperatorAlgebra.twistedMk_mem_parity
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) {p : ZMod 2} {u : 𝒱} (hu : u ∈ W.parity p) :
    W.twistedMk hW g N u ∈ W.twistedAParity hW g N p :=
  ⟨u, hu, rfl⟩

theorem SuperVertexOperatorAlgebra.twistedMk_surjective
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) : Function.Surjective (W.twistedMk hW g N) :=
  Submodule.mkQ_surjective _

theorem SuperVertexOperatorAlgebra.twistedMk_eq_iff
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) {u v : 𝒱} :
    W.twistedMk hW g N u = W.twistedMk hW g N v ↔
      u - v ∈ W.twistedO hW g N := by
  rw [SuperVertexOperatorAlgebra.twistedMk, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq]

theorem SuperVertexOperatorAlgebra.twistedMk_eq_zero_iff
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) {u : 𝒱} :
    W.twistedMk hW g N u = 0 ↔ u ∈ W.twistedO hW g N := by
  rw [SuperVertexOperatorAlgebra.twistedMk, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]

/-- The nonfixed Dong--Zhao circle generators vanish in the quotient. -/
theorem SuperVertexOperatorAlgebra.twistedMk_circle_nonfixed_eq_zero
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) {N : ℕ} (r : Fin N) {k : ℤ} {u v : 𝒱}
    (hr : r.1 ≠ 0) (hk : u ∈ W.toSuperNearVOA.gradingZ k)
    (heig : u ∈ g.twistedEigenspace N r.1) :
    W.twistedMk hW g N (twistedZhuCircleHom W N r.1 k u v) = 0 :=
  (W.twistedMk_eq_zero_iff hW g N).mpr
    (W.twistedO_nonfixed_mem hW g r hr hk heig)

/-- Identity-twist quotients are canonically the existing `superA`. -/
noncomputable def SuperVertexOperatorAlgebra.twistedAIdentityEquiv
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights) :
    W.twistedA hW (1 : SuperAut W) 1 ≃ₗ[ℂ] W.toSuperNearVOA.superA hW :=
  Submodule.quotEquivOfEq _ _ (W.twistedO_identity hW)

/-- The exact unproved residue content of Dong--Zhao Theorem 3.1 for this presentation.
`fixed_mod` is the right-unit residue statement: all nonfixed components die in `A_g(V)`.
The other three fields are precisely two-sided descent and associativity modulo `O_g`. -/
structure SuperTwistedZhuRingData (W : SuperVertexOperatorAlgebra 𝒱)
    (hW : W.toSuperNearVOA.IntegralWeights) (g : SuperAut W) (N : ℕ) : Prop where
  order_pos : 0 < N
  order_pow : g ^ N = 1
  fixed_mod : ∀ u : 𝒱, u - g.fixedAverage N u ∈ W.twistedO hW g N
  left_ideal : ∀ {u : 𝒱}, u ∈ W.twistedO hW g N → ∀ v,
    W.twistedZhuMul hW g N u v ∈ W.twistedO hW g N
  right_ideal : ∀ (u : 𝒱) {v : 𝒱}, v ∈ W.twistedO hW g N →
    W.twistedZhuMul hW g N u v ∈ W.twistedO hW g N
  assoc : ∀ u v w : 𝒱,
    W.twistedZhuMul hW g N (W.twistedZhuMul hW g N u v) w -
      W.twistedZhuMul hW g N u (W.twistedZhuMul hW g N v w)
        ∈ W.twistedO hW g N

/-! ## Formal descent from the exact residue gate -/

/-- Right-kernel condition for descending a bilinear map through `A_g(V)`. -/
theorem SuperVertexOperatorAlgebra.twistedDescend_right_ker
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) (B : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] 𝒱)
    (hright : ∀ (u : 𝒱) {v : 𝒱}, v ∈ W.twistedO hW g N → B u v ∈ W.twistedO hW g N) :
    W.twistedO hW g N ≤ LinearMap.ker (B.compr₂ (W.twistedMk hW g N)).flip := by
  intro v hv
  rw [LinearMap.mem_ker]
  refine LinearMap.ext fun u => ?_
  simp only [LinearMap.flip_apply, LinearMap.compr₂_apply, LinearMap.zero_apply,
    SuperVertexOperatorAlgebra.twistedMk]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (hright u hv)

/-- Left-kernel condition after the right variable has been descended. -/
theorem SuperVertexOperatorAlgebra.twistedDescend_left_ker
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) (B : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] 𝒱)
    (hleft : ∀ {u : 𝒱}, u ∈ W.twistedO hW g N → ∀ v, B u v ∈ W.twistedO hW g N)
    (hright : ∀ (u : 𝒱) {v : 𝒱}, v ∈ W.twistedO hW g N → B u v ∈ W.twistedO hW g N) :
    W.twistedO hW g N ≤ LinearMap.ker
      (((W.twistedO hW g N).liftQ (B.compr₂ (W.twistedMk hW g N)).flip
        (W.twistedDescend_right_ker hW g N B hright)).flip) := by
  intro u hu
  rw [LinearMap.mem_ker]
  refine LinearMap.ext fun vb => ?_
  refine Submodule.Quotient.induction_on _ vb fun v => ?_
  simp only [LinearMap.flip_apply, Submodule.liftQ_apply, LinearMap.compr₂_apply,
    LinearMap.zero_apply, SuperVertexOperatorAlgebra.twistedMk]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (hleft hu v)

/-- Generic bilinear descent to the twisted quotient. -/
noncomputable def SuperVertexOperatorAlgebra.twistedDescendBilin
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) (B : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] 𝒱)
    (hleft : ∀ {u : 𝒱}, u ∈ W.twistedO hW g N → ∀ v, B u v ∈ W.twistedO hW g N)
    (hright : ∀ (u : 𝒱) {v : 𝒱}, v ∈ W.twistedO hW g N → B u v ∈ W.twistedO hW g N) :
    W.twistedA hW g N →ₗ[ℂ] W.twistedA hW g N →ₗ[ℂ] W.twistedA hW g N :=
  (W.twistedO hW g N).liftQ
    (((W.twistedO hW g N).liftQ (B.compr₂ (W.twistedMk hW g N)).flip
      (W.twistedDescend_right_ker hW g N B hright)).flip)
    (W.twistedDescend_left_ker hW g N B hleft hright)

@[simp] theorem SuperVertexOperatorAlgebra.twistedDescendBilin_mk
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) (B : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] 𝒱)
    (hleft : ∀ {u : 𝒱}, u ∈ W.twistedO hW g N → ∀ v, B u v ∈ W.twistedO hW g N)
    (hright : ∀ (u : 𝒱) {v : 𝒱}, v ∈ W.twistedO hW g N → B u v ∈ W.twistedO hW g N)
    (u v : 𝒱) :
    W.twistedDescendBilin hW g N B hleft hright
      (W.twistedMk hW g N u) (W.twistedMk hW g N v) =
        W.twistedMk hW g N (B u v) := by
  simp only [SuperVertexOperatorAlgebra.twistedDescendBilin,
    SuperVertexOperatorAlgebra.twistedMk, Submodule.mkQ_apply, Submodule.liftQ_apply,
    LinearMap.flip_apply, LinearMap.compr₂_apply]

namespace SuperTwistedZhuRingData

variable {W : SuperVertexOperatorAlgebra 𝒱} {hW : W.toSuperNearVOA.IntegralWeights}
  {g : SuperAut W} {N : ℕ} (hZ : SuperTwistedZhuRingData W hW g N)

/-- The descended product on `A_g(V)`. -/
noncomputable def twistedAmul :
    W.twistedA hW g N →ₗ[ℂ] W.twistedA hW g N →ₗ[ℂ] W.twistedA hW g N :=
  W.twistedDescendBilin hW g N (W.twistedZhuMulₗ hW g N)
    (fun {_} hu v => hZ.left_ideal hu v) (fun u {_} hv => hZ.right_ideal u hv)

@[simp] theorem twistedAmul_mk (u v : 𝒱) :
    hZ.twistedAmul (W.twistedMk hW g N u) (W.twistedMk hW g N v) =
      W.twistedMk hW g N (W.twistedZhuMul hW g N u v) := by
  rw [twistedAmul, W.twistedDescendBilin_mk]
  rfl

theorem twistedAmul_assoc (a b c : W.twistedA hW g N) :
    hZ.twistedAmul (hZ.twistedAmul a b) c = hZ.twistedAmul a (hZ.twistedAmul b c) := by
  obtain ⟨u, rfl⟩ := W.twistedMk_surjective hW g N a
  obtain ⟨v, rfl⟩ := W.twistedMk_surjective hW g N b
  obtain ⟨w, rfl⟩ := W.twistedMk_surjective hW g N c
  rw [twistedAmul_mk, twistedAmul_mk, twistedAmul_mk, twistedAmul_mk,
    W.twistedMk_eq_iff hW g N]
  exact hZ.assoc u v w

theorem twistedAmul_one_left (a : W.twistedA hW g N) :
    hZ.twistedAmul (W.twistedOne hW g N) a = a := by
  obtain ⟨u, rfl⟩ := W.twistedMk_surjective hW g N a
  rw [SuperVertexOperatorAlgebra.twistedOne, twistedAmul_mk,
    SuperVertexOperatorAlgebra.twistedZhuMul, g.fixedAverage_vacuum hZ.order_pos]
  change W.twistedMk hW g N (W.toSuperNearVOA.superZhuMul hW
    W.toSuperNearVOA.vacuum u) = W.twistedMk hW g N u
  rw [W.toSuperNearVOA.superZhuMul_vacuum_left]

theorem twistedAmul_one_right (a : W.twistedA hW g N) :
    hZ.twistedAmul a (W.twistedOne hW g N) = a := by
  obtain ⟨u, rfl⟩ := W.twistedMk_surjective hW g N a
  rw [SuperVertexOperatorAlgebra.twistedOne, twistedAmul_mk,
    SuperVertexOperatorAlgebra.twistedZhuMul]
  change W.twistedMk hW g N (W.toSuperNearVOA.superZhuMul hW
    (g.fixedAverage N u) W.toSuperNearVOA.vacuum) = W.twistedMk hW g N u
  rw [W.toSuperNearVOA.superZhuMul_vacuum_right, W.twistedMk_eq_iff hW g N]
  simpa only [neg_sub] using (W.twistedO hW g N).neg_mem (hZ.fixed_mod u)

/-- The descended product adds quotient parity images. -/
theorem twistedAmul_mem_parity {p q : ZMod 2} {a b : W.twistedA hW g N}
    (ha : a ∈ W.twistedAParity hW g N p) (hb : b ∈ W.twistedAParity hW g N q) :
    hZ.twistedAmul a b ∈ W.twistedAParity hW g N (p + q) := by
  obtain ⟨u, hu, rfl⟩ := ha
  obtain ⟨v, hv, rfl⟩ := hb
  rw [twistedAmul_mk]
  exact W.twistedMk_mem_parity hW g N
    (W.twistedZhuMul_mem_parity hW g N hu hv)

/-- The associative unital ring carried by the twisted Zhu quotient. -/
@[reducible] noncomputable def AsRing : Ring (W.twistedA hW g N) :=
  { (inferInstance : AddCommGroup (W.twistedA hW g N)) with
    mul := fun a b => hZ.twistedAmul a b
    one := W.twistedOne hW g N
    mul_assoc := hZ.twistedAmul_assoc
    one_mul := hZ.twistedAmul_one_left
    mul_one := hZ.twistedAmul_one_right
    left_distrib := fun a b c => map_add (hZ.twistedAmul a) b c
    right_distrib := fun a b c => by
      exact congrFun (congrArg DFunLike.coe (map_add hZ.twistedAmul a b)) c
    zero_mul := fun a => by
      exact congrFun (congrArg DFunLike.coe (map_zero hZ.twistedAmul)) a
    mul_zero := fun a => map_zero (hZ.twistedAmul a) }

/-- The complex algebra structure obtained from bilinearity of the descended product. -/
@[reducible] noncomputable def AsAlgebra :
    @Algebra ℂ (W.twistedA hW g N) _ hZ.AsRing.toSemiring :=
  letI := hZ.AsRing
  @Algebra.ofModule ℂ (W.twistedA hW g N) _ hZ.AsRing.toSemiring
    (inferInstance : Module ℂ (W.twistedA hW g N))
    (fun c a b => by
      change hZ.twistedAmul (c • a) b = c • hZ.twistedAmul a b
      exact congrFun (congrArg DFunLike.coe (map_smul hZ.twistedAmul c a)) b)
    (fun c a b => by
      change hZ.twistedAmul a (c • b) = c • hZ.twistedAmul a b
      exact map_smul (hZ.twistedAmul a) c b)

end SuperTwistedZhuRingData

/-- Transport of the untwisted residue theorem to denominator-one identity twist. -/
def SuperTwistedZhuRingData.identityOfSuperZhu
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (hZ : SuperZhuRingData W.toSuperNearVOA hW) :
    SuperTwistedZhuRingData W hW (1 : SuperAut W) 1 where
  order_pos := by norm_num
  order_pow := by simp
  fixed_mod := fun u => by simp [W.twistedO_identity hW]
  left_ideal := by
    intro u hu v
    rw [W.twistedO_identity hW] at hu ⊢
    rw [W.twistedZhuMul_identity hW]
    exact hZ.left_ideal hu v
  right_ideal := by
    intro u v hv
    rw [W.twistedO_identity hW] at hv ⊢
    rw [W.twistedZhuMul_identity hW]
    exact hZ.right_ideal u hv
  assoc := by
    intro u v w
    rw [W.twistedO_identity hW]
    simp only [W.twistedZhuMul_identity hW]
    exact hZ.assoc u v w

/-! ## Zero modes on finite weight blocks -/

namespace SuperTwistedModule

variable {W : SuperVertexOperatorAlgebra 𝒱} {g : SuperAut W} {N : ℕ}
  {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- The integer label representing the conformal zero mode of a weight-`k` state: its
fractional mode number is `k-1`. -/
def zeroModeLabel (N : ℕ) (k : ℤ) : ℤ := (N : ℤ) * (k - 1)

/-- A homogeneous zero mode restricted to one finite-dimensional conformal-weight block. -/
noncomputable def twistedZeroModeBlock (T : SuperTwistedModule W g N M)
    (u : 𝒱) (k : ℤ) (hu : u ∈ W.toSuperNearVOA.gradingZ k) (α : ℂ) :
    End ℂ (T.weight α) where
  toFun x := ⟨T.YM u (zeroModeLabel N k) x, by
    have h := T.weight_mode u (show u ∈ W.grading (k : ℂ) from hu) x x.2
      (zeroModeLabel N k)
    have hN : (N : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt T.order_pos
    have heq : α + (k : ℂ) - (zeroModeLabel N k : ℤ) / (N : ℂ) - 1 = α := by
      rw [zeroModeLabel]
      push_cast
      field_simp [hN]
      ring
    rwa [heq] at h⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (T.YM u (zeroModeLabel N k)) (x : M) (y : M)
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul (T.YM u (zeroModeLabel N k)) c (x : M)

@[simp] theorem twistedZeroModeBlock_apply_coe (T : SuperTwistedModule W g N M)
    (u : 𝒱) (k : ℤ) (hu : u ∈ W.toSuperNearVOA.gradingZ k) (α : ℂ)
    (x : T.weight α) :
    ((T.twistedZeroModeBlock u k hu α x : T.weight α) : M) =
      T.YM u (zeroModeLabel N k) x := rfl

/-- The homogeneous block zero mode has the same parity as its state. -/
theorem twistedZeroModeBlock_parity (T : SuperTwistedModule W g N M)
    {p q : ZMod 2} {u : 𝒱} (huParity : u ∈ W.parity p) (k : ℤ)
    (huWeight : u ∈ W.toSuperNearVOA.gradingZ k) (α : ℂ)
    (x : T.weight α) (hx : (x : M) ∈ T.parity q) :
    ((T.twistedZeroModeBlock u k huWeight α x : T.weight α) : M) ∈
      T.parity (p + q) :=
  T.parity_mode u huParity x hx (zeroModeLabel N k)

/-- The weight-`k` slice of the zero-mode action on `M_alpha`. -/
noncomputable def twistedZeroModeFamily (T : SuperTwistedModule W g N M)
    (α : ℂ) (k : ℤ) : W.toSuperNearVOA.gradingZ k →ₗ[ℂ] End ℂ (T.weight α) where
  toFun uk := T.twistedZeroModeBlock uk k uk.2 α
  map_add' a b := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (congrFun (map_add T.YM (a : 𝒱) b) (zeroModeLabel N k)) x
  map_smul' c a := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (congrFun (map_smul T.YM c (a : 𝒱)) (zeroModeLabel N k)) x

/-- The basis-independent zero-mode action of an arbitrary state, obtained by summing its
integral conformal-weight components. -/
noncomputable def twistedZeroModeAction (T : SuperTwistedModule W g N M)
    (hW : W.toSuperNearVOA.IntegralWeights) (α : ℂ) : 𝒱 →ₗ[ℂ] End ℂ (T.weight α) :=
  letI := DirectSum.IsInternal.chooseDecomposition W.toSuperNearVOA.gradingZ
    (W.toSuperNearVOA.gradingZ_isInternal hW)
  (DFinsupp.lsum ℂ (T.twistedZeroModeFamily α)).comp
    (DirectSum.decomposeLinearEquiv W.toSuperNearVOA.gradingZ).toLinearMap

/-- On a homogeneous state the global action is its expected fractional zero mode. -/
theorem twistedZeroModeAction_homogeneous (T : SuperTwistedModule W g N M)
    (hW : W.toSuperNearVOA.IntegralWeights) (α : ℂ) {u : 𝒱} {k : ℤ}
    (hu : u ∈ W.toSuperNearVOA.gradingZ k) :
    T.twistedZeroModeAction hW α u = T.twistedZeroModeBlock u k hu α := by
  letI := DirectSum.IsInternal.chooseDecomposition W.toSuperNearVOA.gradingZ
    (W.toSuperNearVOA.gradingZ_isInternal hW)
  rw [twistedZeroModeAction, LinearMap.comp_apply]
  change (DFinsupp.lsum ℂ (T.twistedZeroModeFamily α))
    (DirectSum.decompose W.toSuperNearVOA.gradingZ u) = _
  rw [DirectSum.decompose_of_mem W.toSuperNearVOA.gradingZ hu]
  exact DFinsupp.lsum_single ℂ (T.twistedZeroModeFamily α) k ⟨u, hu⟩

end SuperTwistedModule

/-- The precise bottom-space residue obligations.  `O_annihilates` is Dong--Zhao's assertion
that every twisted circle relation acts trivially; `multiplicative` is the zero-mode product
lemma.  Both are consequences of the full twisted Jacobi identity plus the lowest-weight
condition, but neither is hidden in the carrier or asserted here. -/
structure SuperTwistedZhuBottomData
    {W : SuperVertexOperatorAlgebra 𝒱} (hW : W.toSuperNearVOA.IntegralWeights)
    {g : SuperAut W} {N : ℕ} {M : Type v} [AddCommGroup M] [Module ℂ M]
    (T : SuperTwistedModule W g N M) (α : ℂ) : Prop where
  O_annihilates : W.twistedO hW g N ≤ LinearMap.ker (T.twistedZeroModeAction hW α)
  multiplicative : ∀ u v : 𝒱,
    T.twistedZeroModeAction hW α (W.twistedZhuMul hW g N u v) =
      T.twistedZeroModeAction hW α u * T.twistedZeroModeAction hW α v

namespace SuperTwistedZhuBottomData

variable {W : SuperVertexOperatorAlgebra 𝒱} {hW : W.toSuperNearVOA.IntegralWeights}
  {g : SuperAut W} {N : ℕ} {M : Type v} [AddCommGroup M] [Module ℂ M]
  {T : SuperTwistedModule W g N M} {α : ℂ}

/-- The zero-mode map descended to the twisted Zhu quotient. -/
noncomputable def bottomAction (hB : SuperTwistedZhuBottomData hW T α) :
    W.twistedA hW g N →ₗ[ℂ] End ℂ (T.weight α) :=
  (W.twistedO hW g N).liftQ (T.twistedZeroModeAction hW α) hB.O_annihilates

@[simp] theorem bottomAction_mk (hB : SuperTwistedZhuBottomData hW T α) (u : 𝒱) :
    hB.bottomAction (W.twistedMk hW g N u) = T.twistedZeroModeAction hW α u := by
  rw [bottomAction, SuperVertexOperatorAlgebra.twistedMk, Submodule.mkQ_apply,
    Submodule.liftQ_apply]

/-- Multiplicativity of the descended bottom-space action. -/
theorem bottomAction_mul_mk (hB : SuperTwistedZhuBottomData hW T α)
    (hZ : SuperTwistedZhuRingData W hW g N) (u v : 𝒱) :
    hB.bottomAction (hZ.twistedAmul (W.twistedMk hW g N u) (W.twistedMk hW g N v)) =
      hB.bottomAction (W.twistedMk hW g N u) *
        hB.bottomAction (W.twistedMk hW g N v) := by
  rw [hZ.twistedAmul_mk, bottomAction_mk, bottomAction_mk, bottomAction_mk]
  exact hB.multiplicative u v

end SuperTwistedZhuBottomData

end VOA
