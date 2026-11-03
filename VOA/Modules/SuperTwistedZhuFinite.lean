/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.SuperTwistedZhu
import VOA.Modularity.SuperZhuAlgebraFinite
import VOA.Modularity.SuperSymmetricFunctionals
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Finiteness of finite-order twisted super Zhu quotients

This file supplies the finite-order linear algebra omitted from `SuperTwistedZhu`: the Reynolds
average is the identity on the fixed eigenspace and vanishes on every nonzero root-of-unity
eigenspace.  No eigenbasis is chosen for those pointwise statements.

The finite-dimensionality argument is kept separate from associativity.  The main theorem uses
the standard triangular conformal-weight reduction modulo `O_g`; it does not assume the generally
stronger inclusion of the super `C2` relation space in `O_g`.  A conditional quotient map from
that stronger inclusion is retained at the end as a useful optional interface.
-/

namespace VOA

open Module (End)
open scoped BigOperators
open GammaThetaStmt

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The Reynolds geometric-series lemma -/

/-- The Reynolds average is fixed by `g` when `g^N=1`.  The proof is the finite telescoping
identity, so it neither chooses nor assumes an eigenspace decomposition. -/
theorem SuperAut.map_fixedAverage {W : SuperVertexOperatorAlgebra 𝒱}
    (g : SuperAut W) {N : ℕ} (hpow : g ^ N = 1) (u : 𝒱) :
    g (g.fixedAverage N u) = g.fixedAverage N u := by
  let f : ℕ → 𝒱 := fun a => (g ^ a) u
  have hshift : (∑ a ∈ Finset.range N, f (a + 1)) = ∑ a ∈ Finset.range N, f a := by
    apply add_left_cancel (a := f 0)
    calc
      f 0 + ∑ a ∈ Finset.range N, f (a + 1) = ∑ a ∈ Finset.range (N + 1), f a :=
        (add_comm _ _).trans (Finset.sum_range_succ' f N).symm
      _ = (∑ a ∈ Finset.range N, f a) + f N := Finset.sum_range_succ f N
      _ = (∑ a ∈ Finset.range N, f a) + f 0 := by simp [f, hpow]
      _ = f 0 + ∑ a ∈ Finset.range N, f a := add_comm _ _
  have hterm : ∀ a : ℕ, g ((g ^ a) u) = (g ^ (a + 1)) u := by
    intro a
    rw [pow_succ']
    rfl
  rw [SuperAut.fixedAverage, LinearMap.smul_apply, LinearMap.sum_apply]
  change g.toLinearEquiv (((N : ℂ)⁻¹) • ∑ a ∈ Finset.range N, (g ^ a) u) = _
  calc
    g.toLinearEquiv (((N : ℂ)⁻¹) • ∑ a ∈ Finset.range N, (g ^ a) u) =
        ((N : ℂ)⁻¹) • g.toLinearEquiv (∑ a ∈ Finset.range N, (g ^ a) u) :=
      g.toLinearEquiv.map_smul _ _
    _ = ((N : ℂ)⁻¹) • ∑ a ∈ Finset.range N, g ((g ^ a) u) := by rw [map_sum]
    _ = ((N : ℂ)⁻¹) • ∑ a ∈ Finset.range N, (g ^ (a + 1)) u := by
      rw [Finset.sum_congr rfl (fun a _ => hterm a)]
    _ = ((N : ℂ)⁻¹) • ∑ a ∈ Finset.range N, (g ^ a) u := by rw [hshift]

/-- A Reynolds average of a nontrivial eigenvector is zero.  This is the geometric-series
argument in basis-free form: the average is simultaneously fixed and a `lambda`-eigenvector. -/
theorem SuperAut.fixedAverage_eq_zero_of_eigenvalue
    {W : SuperVertexOperatorAlgebra 𝒱} (g : SuperAut W) {N : ℕ}
    (hpow : g ^ N = 1) {u : 𝒱} {lam : ℂ} (hu : g u = lam • u) (hlam : lam ≠ 1) :
    g.fixedAverage N u = 0 := by
  have havfix := g.map_fixedAverage hpow u
  have hterm : ∀ a : ℕ, g ((g ^ a) u) = lam • (g ^ a) u := by
    intro a
    calc
      g ((g ^ a) u) = (g ^ (a + 1)) u := by rw [pow_succ']; rfl
      _ = (g ^ a) (g u) := by rw [pow_succ, SuperAut.mul_apply]
      _ = (g ^ a) (lam • u) := by rw [hu]
      _ = lam • (g ^ a) u := (g ^ a).toLinearEquiv.map_smul lam u
  have haveig : g (g.fixedAverage N u) = lam • g.fixedAverage N u := by
    rw [SuperAut.fixedAverage, LinearMap.smul_apply, LinearMap.sum_apply]
    change g.toLinearEquiv (((N : ℂ)⁻¹) • ∑ a ∈ Finset.range N, (g ^ a) u) = _
    calc
      g.toLinearEquiv (((N : ℂ)⁻¹) • ∑ a ∈ Finset.range N, (g ^ a) u) =
          ((N : ℂ)⁻¹) • ∑ a ∈ Finset.range N, g ((g ^ a) u) := by
        rw [g.toLinearEquiv.map_smul, map_sum]
      _ = ((N : ℂ)⁻¹) • ∑ a ∈ Finset.range N, lam • (g ^ a) u := by
        rw [Finset.sum_congr rfl (fun a _ => hterm a)]
      _ = lam • (((N : ℂ)⁻¹) • ∑ a ∈ Finset.range N, (g ^ a) u) := by
        rw [← Finset.smul_sum]
        module
  have hyeq : g.fixedAverage N u = lam • g.fixedAverage N u := havfix.symm.trans haveig
  have hz : (1 - lam) • g.fixedAverage N u = 0 := by
    rw [sub_smul, one_smul]
    exact sub_eq_zero.mpr hyeq
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm hlam))

/-- The root of unity labelling a nonzero residue class `r : Fin N` is not one. -/
theorem twistedEigenvalue_ne_one {N : ℕ} (r : Fin N) (hr : r.1 ≠ 0) :
    Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (r.1 : ℂ)) / (N : ℂ)) ≠ 1 := by
  intro hneg
  have hpos : Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * (r.1 : ℂ) / (N : ℂ)) = 1 := by
    have harg : -(2 * (Real.pi : ℂ) * Complex.I * (r.1 : ℂ)) / (N : ℂ) =
        -(2 * (Real.pi : ℂ) * Complex.I * (r.1 : ℂ) / (N : ℂ)) := by ring
    rw [harg, Complex.exp_neg] at hneg
    exact inv_eq_one.mp hneg
  have hN : N ≠ 0 := Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le r.1) r.isLt)
  have hdvd : N ∣ r.1 :=
    (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hN).mp hpos
  exact hr (Nat.eq_zero_of_dvd_of_lt hdvd r.isLt)

/-- The Reynolds average vanishes on every nonzero twisted eigenspace. -/
theorem SuperAut.fixedAverage_eigenspace_nonzero
    {W : SuperVertexOperatorAlgebra 𝒱} (g : SuperAut W) {N : ℕ}
    (hpow : g ^ N = 1) (r : Fin N) (hr : r.1 ≠ 0) {u : 𝒱}
    (hu : u ∈ g.twistedEigenspace N r.1) : g.fixedAverage N u = 0 := by
  rw [SuperAut.twistedEigenspace, Module.End.mem_eigenspace_iff] at hu
  exact g.fixedAverage_eq_zero_of_eigenvalue hpow hu (twistedEigenvalue_ne_one r hr)

/-- On every explicitly known eigensector, the averaged product agrees with Dong--Zhao's
piecewise product: ordinary in sector zero and zero otherwise. -/
theorem SuperVertexOperatorAlgebra.twistedZhuMul_of_eigenspace
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) {N : ℕ} (hpow : g ^ N = 1) (r : Fin N) {u : 𝒱}
    (hu : u ∈ g.twistedEigenspace N r.1) (v : 𝒱) :
    W.twistedZhuMul hW g N u v = W.twistedZhuMulHom hW r.1 u v := by
  by_cases hr : r.1 = 0
  · have hu0 : u ∈ g.twistedEigenspace N 0 := by simpa only [hr] using hu
    simpa only [hr] using W.twistedZhuMul_of_eigenspace_zero hW g
      (lt_of_le_of_lt (Nat.zero_le r.1) r.isLt) hu0 v
  · exact W.twistedZhuMul_of_nonfixed_average hW g N hr
      (g.fixedAverage_eigenspace_nonzero hpow r hr hu) v

/-! ## Explicit eigenspace-decomposition and parity gates -/

/-- An explicit simultaneous eigenspace decomposition for a finite-order automorphism.

The internality field is diagonalizability.  The two component fields say that its canonical
projections preserve conformal weight and parity.  These properties are not hidden in
`SuperAut` or inferred from finite-dimensionality. -/
structure TwistEigenspaceDecomposition (W : SuperVertexOperatorAlgebra 𝒱)
    (g : SuperAut W) (N : ℕ) : Prop where
  isInternal : DirectSum.IsInternal (fun r : Fin N => g.twistedEigenspace N r.1)
  component_mem_grading :
    letI := DirectSum.IsInternal.chooseDecomposition
      (fun r : Fin N => g.twistedEigenspace N r.1) isInternal
    ∀ (k : ℤ) (u : 𝒱), u ∈ W.toSuperNearVOA.gradingZ k → ∀ r : Fin N,
      ((DirectSum.decompose (fun s : Fin N => g.twistedEigenspace N s.1) u r :
        g.twistedEigenspace N r.1) : 𝒱) ∈ W.toSuperNearVOA.gradingZ k
  component_mem_parity :
    letI := DirectSum.IsInternal.chooseDecomposition
      (fun r : Fin N => g.twistedEigenspace N r.1) isInternal
    ∀ (p : ZMod 2) (u : 𝒱), u ∈ W.parity p → ∀ r : Fin N,
      ((DirectSum.decompose (fun s : Fin N => g.twistedEigenspace N s.1) u r :
        g.twistedEigenspace N r.1) : 𝒱) ∈ W.parity p

/-- The exact condition that `O_g` is homogeneous for the internal parity grading. -/
def SuperVertexOperatorAlgebra.TwistedOParityGraded
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) : Prop :=
  W.twistedO hW g N = ⨆ p : ZMod 2, W.twistedO hW g N ⊓ W.parity p

/-- If `O_g` is parity graded, the two quotient parity images form an internal direct sum. -/
theorem SuperVertexOperatorAlgebra.twistedAParity_isInternal
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) (hgr : W.TwistedOParityGraded hW g N) :
    DirectSum.IsInternal (W.twistedAParity hW g N) := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · exact QuotVOA.iSupIndep_map_mkQ W.parity W.parity_isInternal.submodule_iSupIndep
      (W.twistedO hW g N) hgr.le
  · change (⨆ p, (W.parity p).map (W.twistedO hW g N).mkQ) = ⊤
    rw [← Submodule.map_iSup, W.parity_isInternal.submodule_iSup_eq_top,
      Submodule.map_top, Submodule.range_mkQ]

/-- Identity twist inherits the already proved parity grading of ordinary `superO`. -/
theorem SuperVertexOperatorAlgebra.twistedOParityGraded_identity
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights) :
    W.TwistedOParityGraded hW (1 : SuperAut W) 1 := by
  rw [SuperVertexOperatorAlgebra.TwistedOParityGraded, W.twistedO_identity hW]
  exact W.toSuperNearVOA.superO_eq_iSup_inf_parity hW

/-- Identity-twist quotient parity is an internal direct sum. -/
theorem SuperVertexOperatorAlgebra.twistedAParity_isInternal_identity
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights) :
    DirectSum.IsInternal (W.twistedAParity hW (1 : SuperAut W) 1) :=
  W.twistedAParity_isInternal hW (1 : SuperAut W) 1
    (W.twistedOParityGraded_identity hW)

/-! ## Sectorwise triangular reduction -/

/-- The mode family in a nonfixed pole-one circle residue has finite support. -/
private theorem nonfixedCircleSummand_support_finite
    (W : SuperVertexOperatorAlgebra 𝒱) (N r : ℕ) (k : ℤ) (u v : 𝒱) :
    (Function.support fun i : ℕ =>
      fractionalBinom (twistedZhuExponent N r k) i • W.smul u ((i : ℤ) - 1) v).Finite := by
  obtain ⟨B, hB⟩ := W.regularity u v
  apply Set.Finite.subset (Set.finite_Iio (B.toNat + 1))
  intro i hi
  rw [Function.mem_support] at hi
  by_contra hc
  rw [Set.mem_Iio, not_lt] at hc
  refine hi ?_
  have hmode : B ≤ (i : ℤ) - 1 := by
    have hBi : B.toNat + 1 ≤ i := hc
    have hBnat : B ≤ (B.toNat : ℤ) := Int.self_le_toNat B
    omega
  rw [SuperVertexAlgebra.smul_def, hB _ hmode, smul_zero]

/-- A fixed-sector homogeneous `-2` product reduces to strictly lower conformal weights modulo
`O_g`.  This is the ordinary square/circle descent, with the Reynolds projection proved to be
the identity on the fixed eigenspace. -/
theorem SuperVertexOperatorAlgebra.smul_negTwo_mem_of_lower_twisted_fixed
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) {N : ℕ} (hN : 0 < N) {p q : ℤ} {a b : 𝒱}
    (ha : a ∈ W.toSuperNearVOA.gradingZ p) (hb : b ∈ W.toSuperNearVOA.gradingZ q)
    (haeig : a ∈ g.twistedEigenspace N 0) (hp : 0 ≤ p)
    (T : Submodule ℂ 𝒱) (hO : W.twistedO hW g N ≤ T)
    (hT : ∀ m : ℤ, m < p + q + 1 → W.toSuperNearVOA.gradingZ m ≤ T) :
    W.smul a (-2) b ∈ T := by
  let V := W.toSuperNearVOA
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, p = (M : ℤ) := ⟨p.toNat, by omega⟩
  have havg : g.fixedAverage N a = a := g.fixedAverage_eigenspace_zero hN haeig
  have hres :
      (∑ i ∈ Finset.range (M + 1),
        cbz (M : ℤ) (i : ℤ) • W.smul a ((i : ℤ) - 2) b) ∈ T := by
    change (∑ i ∈ Finset.range (M + 1),
      cbz (M : ℤ) (i : ℤ) • V.smul a ((i : ℤ) - 2) b) ∈ T
    apply hO
    rw [← V.superZhuMul_L_base hW ha b, ← havg]
    exact W.twistedO_fixed_mem hW g N a b
  let R : 𝒱 := ∑ i ∈ Finset.range M,
      cbz (M : ℤ) (((i + 1 : ℕ) : ℤ)) • W.smul a (((i + 1 : ℕ) : ℤ) - 2) b
  have hbot : cbz (M : ℤ) (((0 : ℕ) : ℤ)) • W.smul a (((0 : ℕ) : ℤ) - 2) b
      = W.smul a (-2) b := by norm_num
  have hsolve : W.smul a (-2) b =
      (∑ i ∈ Finset.range (M + 1),
        cbz (M : ℤ) (i : ℤ) • W.smul a ((i : ℤ) - 2) b) - R := by
    rw [show R = ∑ i ∈ Finset.range M,
      cbz (M : ℤ) (((i + 1 : ℕ) : ℤ)) •
        W.smul a (((i + 1 : ℕ) : ℤ) - 2) b from rfl]
    rw [Finset.sum_range_succ', hbot]
    abel
  rw [hsolve]
  refine Submodule.sub_mem _ hres ?_
  rw [show R = ∑ i ∈ Finset.range M,
    cbz (M : ℤ) (((i + 1 : ℕ) : ℤ)) •
      W.smul a (((i + 1 : ℕ) : ℤ) - 2) b from rfl]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have hw := V.smul_mem_gradingZ ha hb (((i + 1 : ℕ) : ℤ) - 2)
  have heq : (M : ℤ) + q - ((((i + 1 : ℕ)) : ℤ) - 2) - 1
      = (M : ℤ) + q - (i : ℤ) := by push_cast; ring
  rw [heq] at hw
  exact hT _ (by omega) hw

/-- A nonfixed homogeneous `-2` product reduces to strictly lower conformal weights modulo
`O_g`.  The pole-one circle relation is applied to `L_{-1}a`: its index-zero term is
`(L_{-1}a)_{-1}b=a_{-2}b`, and all positive-index terms have lower weight. -/
theorem SuperVertexOperatorAlgebra.smul_negTwo_mem_of_lower_twisted_nonfixed
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) {N : ℕ} (r : Fin N) (hr : r.1 ≠ 0)
    {p q : ℤ} {a b : 𝒱}
    (ha : a ∈ W.toSuperNearVOA.gradingZ p) (hb : b ∈ W.toSuperNearVOA.gradingZ q)
    (haeig : a ∈ g.twistedEigenspace N r.1)
    (T : Submodule ℂ 𝒱) (hO : W.twistedO hW g N ≤ T)
    (hT : ∀ m : ℤ, m < p + q + 1 → W.toSuperNearVOA.gradingZ m ≤ T) :
    W.smul a (-2) b ∈ T := by
  let V := W.toSuperNearVOA
  have hTa : V.L (-1) a ∈ V.gradingZ (p + 1) := V.L_neg_one_mem_gradingZ_succ ha
  have hTeig : V.L (-1) a ∈ g.twistedEigenspace N r.1 := by
    rw [SuperAut.twistedEigenspace, Module.End.mem_eigenspace_iff] at haeig ⊢
    change g (W.L (-1) a) =
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (r.1 : ℂ)) / (N : ℂ)) •
        W.L (-1) a
    change g a = _ at haeig
    rw [g.map_L, haeig, map_smul]
  let F : ℕ → 𝒱 := fun i =>
    fractionalBinom (twistedZhuExponent N r.1 (p + 1)) i •
      W.smul (V.L (-1) a) ((i : ℤ) - 1) b
  have hFfin : (Function.support F).Finite :=
    nonfixedCircleSummand_support_finite W N r.1 (p + 1) (V.L (-1) a) b
  have hFzero : F 0 = W.smul a (-2) b := by
    simp only [F, fractionalBinom, Finset.range_zero, Finset.prod_empty, Nat.factorial_zero,
      Nat.cast_one, inv_one, one_div, one_smul]
    change V.smul (V.L (-1) a) (-1) b = V.smul a (-2) b
    rw [V.smul_T_applyε a b (-1)]
    norm_num
  have hcircle : (∑ᶠ i : ℕ, F i) ∈ T := by
    apply hO
    have hdelta : twistedZhuDelta r.1 = 0 := twistedZhuDelta_ne_zero hr
    have hmem := W.twistedO_nonfixed_mem hW g r (v := b) hr hTa hTeig
    simpa only [twistedZhuCircleHom, hdelta, Nat.cast_zero, sub_zero] using hmem
  let R : ℕ → 𝒱 := fun i => if i = 0 then 0 else F i
  have hRfin : (Function.support R).Finite := by
    refine Set.Finite.subset hFfin ?_
    intro i hi
    rw [Function.mem_support] at hi ⊢
    change (if i = 0 then 0 else F i) ≠ 0 at hi
    by_cases h : i = 0
    · exact absurd (if_pos h) hi
    · rwa [if_neg h] at hi
  have hsplit : (∑ᶠ i : ℕ, F i) = F 0 + ∑ᶠ i : ℕ, R i := by
    let A : ℕ → 𝒱 := fun i => if i = 0 then F i else 0
    have hAfin : (Function.support A).Finite := by
      refine Set.Finite.subset (Set.finite_singleton 0) ?_
      intro i hi
      rw [Function.mem_support] at hi
      by_contra h
      exact hi (if_neg h)
    have hdecomp : ∀ i : ℕ, F i = A i + R i := by
      intro i
      by_cases h : i = 0 <;> simp [A, R, h]
    rw [finsum_congr hdecomp, finsum_add_distrib hAfin hRfin]
    congr 1
    exact (finsum_eq_single _ 0 (fun i hi => if_neg hi)).trans (if_pos rfl)
  rw [hsplit, hFzero] at hcircle
  have hRmem : (∑ᶠ i : ℕ, R i) ∈ T := by
    apply QuotVOA.finsum_mem_submodule
    intro i
    by_cases hi : i = 0
    · simp [R, hi]
    · have hi0 : 0 < i := Nat.pos_of_ne_zero hi
      have hw := V.smul_mem_gradingZ hTa hb ((i : ℤ) - 1)
      have heq : (p + 1) + q - ((i : ℤ) - 1) - 1 =
          p + q + 1 - (i : ℤ) := by ring
      rw [heq] at hw
      apply hT (p + q + 1 - (i : ℤ)) (by omega)
      simpa [R, F, hi] using
        (V.gradingZ (p + q + 1 - (i : ℤ))).smul_mem
          (fractionalBinom (twistedZhuExponent N r.1 (p + 1)) i) hw
  have hsub := Submodule.sub_mem T hcircle hRmem
  rwa [add_sub_cancel_right] at hsub

/-- After an explicit weight-compatible eigenspace decomposition, every homogeneous `-2`
product reduces to lower conformal weights modulo `O_g`.  No diagonalizability is inferred:
it is exactly the `isInternal` field of `hE`. -/
theorem SuperVertexOperatorAlgebra.smul_negTwo_mem_of_lower_twisted
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) {N : ℕ} (hN : 0 < N) (hE : TwistEigenspaceDecomposition W g N)
    {p q : ℤ} {a b : 𝒱}
    (ha : a ∈ W.toSuperNearVOA.gradingZ p) (hb : b ∈ W.toSuperNearVOA.gradingZ q)
    (hp : 0 ≤ p) (T : Submodule ℂ 𝒱) (hO : W.twistedO hW g N ≤ T)
    (hT : ∀ m : ℤ, m < p + q + 1 → W.toSuperNearVOA.gradingZ m ≤ T) :
    W.smul a (-2) b ∈ T := by
  classical
  let E : Fin N → Submodule ℂ 𝒱 := fun r => g.twistedEigenspace N r.1
  letI := DirectSum.IsInternal.chooseDecomposition E hE.isInternal
  let c : Fin N → 𝒱 := fun r => ((DirectSum.decompose E a r : E r) : 𝒱)
  have hsum : ∑ r ∈ (DirectSum.decompose E a).support, c r = a :=
    DirectSum.sum_support_decompose E a
  rw [← hsum]
  generalize (DirectSum.decompose E a).support = s
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty, SuperVertexAlgebra.smul_zero_left]
      exact T.zero_mem
  | @insert r s hrs ih =>
      rw [Finset.sum_insert hrs, W.smul_add_left]
      apply T.add_mem
      · have hcr : c r ∈ E r := (DirectSum.decompose E a r).2
        have hcweight : c r ∈ W.toSuperNearVOA.gradingZ p :=
          hE.component_mem_grading p a ha r
        by_cases hr : r.1 = 0
        · exact W.smul_negTwo_mem_of_lower_twisted_fixed hW g hN hcweight hb
            (by simpa [E, hr] using hcr) hp T hO hT
        · exact W.smul_negTwo_mem_of_lower_twisted_nonfixed hW g r hr hcweight hb
            (by simpa [E] using hcr) T hO hT
      · exact ih

/-- Every integral conformal-weight piece is spanned by a fixed finite set modulo `O_g`, under
the explicit eigenspace-decomposition gate.  This is the twisted replacement for the generally
too-strong assertion `C2(W) ≤ O_g(W)`. -/
theorem SuperVertexOperatorAlgebra.gradingZ_le_span_sup_twistedO
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) {N : ℕ} (hN : 0 < N) (hE : TwistEigenspaceDecomposition W g N)
    (S : Set 𝒱) (hShom : ∀ s ∈ S, W.toSuperNearVOA.IsHomogZ s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ superO₂ W) (n : ℤ) :
    W.toSuperNearVOA.gradingZ n ≤ Submodule.span ℂ S ⊔ W.twistedO hW g N := by
  let V := W.toSuperNearVOA
  let T : Submodule ℂ 𝒱 := Submodule.span ℂ S ⊔ W.twistedO hW g N
  have hO : W.twistedO hW g N ≤ T := le_sup_right
  rcases lt_or_ge n 0 with hneg | hnn
  · have hz : V.gradingZ n = ⊥ := by
      change W.grading (n : ℂ) = ⊥
      exact W.positivity _ (by rw [Complex.intCast_re]; exact_mod_cast hneg)
    rw [hz]
    exact bot_le
  obtain ⟨K, rfl⟩ : ∃ K : ℕ, n = (K : ℤ) := ⟨n.toNat, by omega⟩
  induction K using Nat.strong_induction_on with
  | _ K ihK =>
    have hlower : ∀ m : ℤ, m < (K : ℤ) → V.gradingZ m ≤ T := by
      intro m hm
      rcases lt_or_ge m 0 with hm0 | hm0
      · have hz : V.gradingZ m = ⊥ := by
          change W.grading (m : ℂ) = ⊥
          exact W.positivity _ (by rw [Complex.intCast_re]; exact_mod_cast hm0)
        rw [hz]
        exact bot_le
      · obtain ⟨J, rfl⟩ : ∃ J : ℕ, m = (J : ℤ) := ⟨m.toNat, by omega⟩
        exact ihK J (by exact_mod_cast hm) (by exact_mod_cast hm0)
    refine le_trans
      (SuperNearVOA.gradingZ_le_span_sup_superO₂_inf W hW S hShom htop (K : ℤ)) ?_
    refine sup_le le_sup_left ?_
    refine le_trans (SuperNearVOA.superO₂_inf_gradingZ_le_span_deg W hW (K : ℤ)) ?_
    rw [Submodule.span_le]
    rintro x ⟨p, q, a, b, ha, hb, hpq, rfl⟩
    by_cases hx0 : V.smul a (-2) b = 0
    · rw [hx0]
      exact T.zero_mem
    have hp0 : 0 ≤ p := by
      by_contra hc
      have hpneg : p < 0 := by omega
      exact hx0 (by
        have ha0 : a = 0 := by
          have hz : V.gradingZ p = ⊥ := by
            change W.grading (p : ℂ) = ⊥
            exact W.positivity _ (by rw [Complex.intCast_re]; exact_mod_cast hpneg)
          rw [hz, Submodule.mem_bot] at ha
          exact ha
        rw [ha0, SuperVertexAlgebra.smul_zero_left])
    exact W.smul_negTwo_mem_of_lower_twisted hW g hN hE ha hb hp0 T hO
      (fun m hm => hlower m (by omega))

/-- The finite homogeneous representatives supplied by `C2`-cofiniteness span all of `W`
modulo the twisted relation space. -/
theorem SuperVertexOperatorAlgebra.span_sup_twistedO_eq_top
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) {N : ℕ} (hN : 0 < N) (hE : TwistEigenspaceDecomposition W g N)
    (S : Set 𝒱) (hShom : ∀ s ∈ S, W.toSuperNearVOA.IsHomogZ s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ superO₂ W) :
    (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ W.twistedO hW g N := by
  refine le_antisymm ?_ le_top
  rw [← (W.toSuperNearVOA.gradingZ_isInternal hW).submodule_iSup_eq_top]
  exact iSup_le (W.gradingZ_le_span_sup_twistedO hW g hN hE S hShom htop)

/-- A finite-order, explicitly diagonalized twist of a `C2`-cofinite integral-weight super VOA
has finite-dimensional twisted Zhu quotient.  The order equation is recorded to expose the
finite-order input; after the eigenspace decomposition is supplied, the triangular proof itself
uses only `0 < N`. -/
theorem finiteDimensional_twistedA_of_superC2Cofinite
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) {N : ℕ} (hN : 0 < N) (_hpow : g ^ N = 1)
    (hE : TwistEigenspaceDecomposition W g N) (hC2 : SuperC2Cofinite W) :
    FiniteDimensional ℂ (W.twistedA hW g N) := by
  obtain ⟨S, hShom, hS⟩ :=
    SuperNearVOA.exists_finset_homog_span_sup_superO₂ W hW hC2
  have hspan := W.span_sup_twistedO_eq_top hW g hN hE (S : Set 𝒱) hShom hS
  have hfin : Module.Finite ℂ (W.twistedA hW g N) := by
    apply Module.finite_def.mpr
    refine Submodule.fg_def.mpr
      ⟨W.twistedMk hW g N '' (S : Set 𝒱),
        S.finite_toSet.image (W.twistedMk hW g N), ?_⟩
    rw [← Submodule.map_span, eq_top_iff]
    intro q _
    obtain ⟨x, rfl⟩ := W.twistedMk_surjective hW g N q
    have hx : x ∈ Submodule.span ℂ (S : Set 𝒱) ⊔ W.twistedO hW g N := by
      rw [← hspan]
      trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    have hz0 : W.twistedMk hW g N z = 0 := W.twistedMk_eq_zero_iff hW g N |>.mpr hz
    rw [map_add, hz0, add_zero]
    exact Submodule.mem_map_of_mem hy
  exact hfin

/-- Explicitly named alias emphasizing the visible diagonalizability hypothesis. -/
theorem finiteDimensional_twistedA_of_superC2Cofinite_eigendecomp
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) {N : ℕ} (hN : 0 < N) (hpow : g ^ N = 1)
    (hE : TwistEigenspaceDecomposition W g N) (hC2 : SuperC2Cofinite W) :
    FiniteDimensional ℂ (W.twistedA hW g N) :=
  finiteDimensional_twistedA_of_superC2Cofinite W hW g hN hpow hE hC2

/-! ## The tempting but stronger `C2` inclusion -/

/-- The precise twisted residue statement needed for finite-dimensionality: all super `C2`
relations lie in `O_g`.  It is logically independent of associativity and therefore is not a
field of `SuperTwistedZhuRingData`. -/
structure SuperTwistedZhuC2Data (W : SuperVertexOperatorAlgebra 𝒱)
    (hW : W.toSuperNearVOA.IntegralWeights) (g : SuperAut W) (N : ℕ) : Prop where
  superO2_le : superO₂ W ≤ W.twistedO hW g N

/-- The canonical map from the super `C2` quotient onto the twisted Zhu quotient. -/
noncomputable def superC2QuotToTwistedA
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) (hC2Z : SuperTwistedZhuC2Data W hW g N) :
    (𝒱 ⧸ superO₂ W) →ₗ[ℂ] W.twistedA hW g N :=
  (superO₂ W).liftQ (W.twistedMk hW g N) (by
    intro x hx
    exact (W.twistedMk_eq_zero_iff hW g N).mpr (hC2Z.superO2_le hx))

@[simp] theorem superC2QuotToTwistedA_mk
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) (hC2Z : SuperTwistedZhuC2Data W hW g N) (u : 𝒱) :
    superC2QuotToTwistedA W hW g N hC2Z ((superO₂ W).mkQ u) =
      W.twistedMk hW g N u := rfl

theorem superC2QuotToTwistedA_surjective
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) (hC2Z : SuperTwistedZhuC2Data W hW g N) :
    Function.Surjective (superC2QuotToTwistedA W hW g N hC2Z) := by
  intro q
  obtain ⟨u, rfl⟩ := W.twistedMk_surjective hW g N q
  exact ⟨(superO₂ W).mkQ u, rfl⟩

/-- A `C2`-cofinite super VOA has finite-dimensional twisted Zhu quotient once the exact
twisted `C2` residue inclusion is supplied.  No ring data is used. -/
theorem finiteDimensional_twistedA_of_superC2Cofinite_of_superO2_le
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) (hC2 : SuperC2Cofinite W)
    (hC2Z : SuperTwistedZhuC2Data W hW g N) :
    FiniteDimensional ℂ (W.twistedA hW g N) := by
  haveI : FiniteDimensional ℂ (𝒱 ⧸ superO₂ W) := hC2
  exact Module.Finite.of_surjective (superC2QuotToTwistedA W hW g N hC2Z)
    (superC2QuotToTwistedA_surjective W hW g N hC2Z)

/-- At the identity twist the finite-dimensional theorem reduces directly, by the proved linear
equivalence, to `finiteDimensional_superA_of_superC2Cofinite`. -/
theorem finiteDimensional_twistedA_identity_of_superC2Cofinite
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (hC2 : SuperC2Cofinite W) :
    FiniteDimensional ℂ (W.twistedA hW (1 : SuperAut W) 1) := by
  haveI : FiniteDimensional ℂ (W.toSuperNearVOA.superA hW) :=
    SuperNearVOA.finiteDimensional_superA_of_superC2Cofinite W hW hC2
  exact FiniteDimensional.of_injective (W.twistedAIdentityEquiv hW).toLinearMap
    (W.twistedAIdentityEquiv hW).injective

end VOA
