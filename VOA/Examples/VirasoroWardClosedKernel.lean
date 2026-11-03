/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaPolynomialWard
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Closedness of the nonzero finite-column Ward kernel

A nonzero kernel vector can be normalized to the unit sphere in the
finite-dimensional coefficient space. That sphere is compact. The full
system of row equations is closed, even when the row set is infinite.
Projection along this compact sphere therefore makes nonzero-kernel
existence a closed condition on matrices. This provides a specialization
route by continuity, without evaluating poles in a chosen vector formula.
-/
namespace VOA.VirasoroWardTopology
open Set Metric

/-- Any nonzero complex kernel vector can be normalized to norm one;
linearity preserves every row equation. -/
theorem exists_unit_kernel {I J : Type*} [Fintype J] (M : Matrix I J ℂ)
    (v : J → ℂ) (hv : v≠0) (hMv : M.mulVec v=0) :
    ∃ w : J → ℂ, ‖w‖=1 ∧ M.mulVec w=0 := by
  refine ⟨((‖v‖:ℂ)⁻¹) • v,?_,?_⟩
  · rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  · rw [Matrix.mulVec_smul,hMv,smul_zero]

/-- The matrices having a nonzero kernel form a closed set when there
are finitely many columns. The row set need not be finite: compactness
is needed only for normalized coefficient vectors. -/
theorem isClosed_nonzero_kernel {I J : Type*} [Fintype J] :
    IsClosed {M : Matrix I J ℂ | ∃ v : J → ℂ, v≠0 ∧ M.mulVec v=0} := by
  classical
  let S := sphere (0 : J → ℂ) 1
  let K : Set (Matrix I J ℂ × S) := {p | p.1.mulVec p.2.val=0}
  have hK : IsClosed K := by
    apply isClosed_eq _ continuous_const
    apply continuous_pi
    intro i
    change Continuous (fun p : Matrix I J ℂ × S => ∑ j, p.1 i j * p.2.val j)
    apply continuous_finsetSum
    intro j hj
    exact ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst)).mul
      ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd))
  have hp := isClosedMap_fst_of_compactSpace (X := Matrix I J ℂ) (Y := S) K hK
  convert hp using 1
  ext M
  constructor
  · rintro ⟨v,hv,hMv⟩
    obtain ⟨w,hw,hMw⟩ := exists_unit_kernel M v hv hMv
    exact ⟨(M,⟨w,mem_sphere_zero_iff_norm.mpr hw⟩),hMw,rfl⟩
  · rintro ⟨⟨M,w⟩,hMw,rfl⟩
    refine ⟨w.val,?_,hMw⟩
    intro hz
    have hh := mem_sphere_zero_iff_norm.mp w.property
    rw [hz,norm_zero] at hh
    exact zero_ne_one hh

/-- A limit of matrices with nonzero kernels still has a nonzero kernel.
This is a specialization theorem for actual equations, independent of how
the approaching kernel vectors were chosen or normalized. -/
theorem nonzero_kernel_of_tendsto {I J X : Type*} [Fintype J]
    {l : Filter X} [l.NeBot] (M : X → Matrix I J ℂ) (M0 : Matrix I J ℂ)
    (hlim : Filter.Tendsto M l (nhds M0))
    (hker : ∀ᶠ x in l, ∃ v : J → ℂ, v≠0 ∧ (M x).mulVec v=0) :
    ∃ v : J → ℂ, v≠0 ∧ M0.mulVec v=0 :=
  isClosed_nonzero_kernel.mem_of_tendsto hlim hker

/-- Nonreal parameters approach every complex parameter. This lets
continuous Ward equations specialize without needing a formula for the
approaching singular vectors. -/
theorem nonreal_dense : Dense {t : ℂ | t.im≠0} := by
  rw [Metric.dense_iff]
  intro z e he
  by_cases hz : z.im≠0
  · exact ⟨z,by simp [he],hz⟩
  · have hz0 : z.im=0 := not_ne_iff.mp hz
    refine ⟨z+(e/2:ℝ)*Complex.I,?_,?_⟩
    · rw [Metric.mem_ball,dist_eq_norm]
      simp only [add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (half_pos he),Complex.norm_I,mul_one]
      exact half_lt_self he
    · simp only [Set.mem_setOf_eq,Complex.add_im,Complex.mul_im,Complex.ofReal_re,
        Complex.ofReal_im,Complex.I_im,Complex.I_re,hz0,mul_one,mul_zero,add_zero,zero_add]
      exact ne_of_gt (half_pos he)

end VOA.VirasoroWardTopology

namespace VOA.InverseDS.VirasoroVerma

/-- The level basis assembles its own coordinates back into the original
actual vector. This makes coefficient kernels accessible from states. -/
theorem vermaLevelState_coordinates (c h : ℂ) (n : ℕ) (v : sortedSpan c h n) :
    vermaLevelState c h n (fun w => (vermaLevelBasis c h n).repr v w)=v.val := by
  have hh := congrArg Subtype.val ((vermaLevelBasis c h n).sum_repr v)
  simpa [vermaLevelState,vermaLevelBasis,Module.Basis.mk_apply,vermaLevelWord] using hh

/-- An actual nonzero level state killed by the two positive generators
supplies a nonzero coordinate kernel of the universal Ward equations. -/
theorem exists_ward_kernel_of_state (c h : ℂ) (n : ℕ) (v : sortedSpan c h n)
    (hv : v.val≠0) (h1 : vermaMode c h 1 v.val=0) (h2 : vermaMode c h 2 v.val=0) :
    ∃ u : VermaPartitions n → ℂ, u≠0 ∧ (vermaWardMatrix c h n).mulVec u=0 := by
  refine ⟨fun w => (vermaLevelBasis c h n).repr v w,?_,?_⟩
  · intro hz
    apply hv
    rw [← vermaLevelState_coordinates c h n v,hz]
    exact (vermaLevelState_eq_zero_iff c h n 0).mpr rfl
  · rw [vermaWardMatrix_kernel_iff,vermaLevelState_coordinates]
    exact ⟨h1,h2⟩

/-- The actual Ward matrix varies continuously with charge and highest
weight because every entry is the proved universal polynomial evaluation. -/
theorem vermaWardMatrix_continuous (n : ℕ) :
    Continuous (fun p : ℂ × ℂ => vermaWardMatrix p.1 p.2 n) := by
  apply continuous_pi
  intro row
  apply continuous_pi
  intro col
  have he : (fun p : ℂ × ℂ => vermaWardMatrix p.1 p.2 n row col)=
      (fun p => MvPolynomial.eval (fun i : Fin 2 => if i=0 then p.1 else p.2)
        (vermaUniversalWardMatrix n row col)) := by
    funext p
    have hh := congrArg (fun M => M row col) (vermaUniversalWardMatrix_eval p.1 p.2 n)
    simpa using hh.symm
  rw [he]
  apply (MvPolynomial.continuous_eval _).comp
  apply continuous_pi
  intro i
  split_ifs <;> fun_prop

attribute [local irreducible] vermaWardMatrix

/-- Nonzero singular states specialize along any convergent continuous
matrix family. Unit-sphere compactness prevents every coordinate from
vanishing in the limit; no choice of rational vector formula is needed. -/
theorem verma_highest_of_tendsto {X : Type*} {l : Filter X} [l.NeBot]
    (C H : X → ℂ) (c h : ℂ) (n : ℕ)
    (hC : Filter.Tendsto C l (nhds c)) (hH : Filter.Tendsto H l (nhds h))
    (hv : ∀ᶠ x in l, ∃ v : sortedSpan (C x) (H x) n,
      v.val≠0 ∧ vermaMode (C x) (H x) 1 v.val=0 ∧ vermaMode (C x) (H x) 2 v.val=0) :
    ∃ v : Verma c h, v≠0 ∧ v∈sortedSpan c h n ∧
      IsHighestWeightVector (vermaRep c h) v c (h+n) := by
  have hpair : Filter.Tendsto (fun x => (C x,H x)) l (nhds (c,h)) :=
    hC.prodMk_nhds hH
  have hlim : Filter.Tendsto (fun x => vermaWardMatrix (C x) (H x) n)
      l (nhds (vermaWardMatrix c h n)) := by
    exact Filter.Tendsto.comp
      (g := fun p : ℂ × ℂ => vermaWardMatrix p.1 p.2 n)
      (f := fun x => (C x,H x)) ((vermaWardMatrix_continuous n).tendsto (c,h)) hpair
  have hker : ∀ᶠ x in l, ∃ u : VermaPartitions n → ℂ,
      u≠0 ∧ (vermaWardMatrix (C x) (H x) n).mulVec u=0 := by
    filter_upwards [hv] with x hx
    obtain ⟨v,hv,h1,h2⟩ := hx
    exact exists_ward_kernel_of_state (C x) (H x) n v hv h1 h2
  obtain ⟨u,hu,hMu⟩ := VirasoroWardTopology.nonzero_kernel_of_tendsto
    (I := VermaWardRows) (J := VermaPartitions n)
    (fun x => vermaWardMatrix (C x) (H x) n) (vermaWardMatrix c h n) hlim hker
  have hh := vermaWardMatrix_highest c h n u hu hMu
  exact ⟨vermaLevelState c h n u,hh.1,vermaLevelState_mem c h n u,hh.2⟩

/-- A nonzero singular family constructed at every nonreal parameter
extends to any parameter where charge and weight are continuous. This
handles rational paths away from their poles without a rational-kernel
presentation or a normalization product. -/
theorem verma_highest_of_nonreal (C H : ℂ → ℂ) (n : ℕ) (t : ℂ)
    (hC : ContinuousAt C t) (hH : ContinuousAt H t)
    (hv : ∀ z : ℂ, z.im≠0 → ∃ v : sortedSpan (C z) (H z) n,
      v.val≠0 ∧ vermaMode (C z) (H z) 1 v.val=0 ∧ vermaMode (C z) (H z) 2 v.val=0) :
    ∃ v : Verma (C t) (H t), v≠0 ∧ v∈sortedSpan (C t) (H t) n ∧
      IsHighestWeightVector (vermaRep (C t) (H t)) v (C t) (H t+n) := by
  haveI := mem_closure_iff_nhdsWithin_neBot.mp (VirasoroWardTopology.nonreal_dense t)
  apply verma_highest_of_tendsto (l := nhdsWithin t {z : ℂ | z.im≠0}) C H (C t) (H t) n
    (hC.tendsto.mono_left nhdsWithin_le_nhds) (hH.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact hv z hz

end VOA.InverseDS.VirasoroVerma
