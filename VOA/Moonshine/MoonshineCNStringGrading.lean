/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNStringGenerators
import Mathlib.Algebra.DirectSum.Decomposition

/-! # Homogeneous projections and the graded light-cone splitting

The negative spans and positive common kernels are proved stable under every
weight projection. In particular, the abstract ungraded light-cone splitting
(`LightConeSplit`) really does restrict to a complementary pair on each weight space.
-/

namespace VOA.Moonshine.ConwayNorton.StringModule

universe u
variable {H : Type u} [AddCommGroup H] [Module ℂ H] (M : StringModule H)

noncomputable instance stringWeightDecomposition : DirectSum.Decomposition M.wt :=
  M.wt_isInternal.chooseDecomposition

/-- The weight-`N` projection, with values in the ambient module. -/
noncomputable def weightComponent (N : ℤ) : Module.End ℂ H :=
  (M.wt N).subtype.comp ((DirectSum.component ℂ ℤ (fun i => M.wt i) N).comp
    (DirectSum.decomposeLinearEquiv M.wt).toLinearMap)

theorem weightComponent_mem (N : ℤ) (x : H) : M.weightComponent N x ∈ M.wt N :=
  (DirectSum.decompose M.wt x N).property

theorem weightComponent_of_mem (N : ℤ) (x : H) (hx : x ∈ M.wt N) :
    M.weightComponent N x = x :=
  DirectSum.decompose_of_mem_same M.wt hx

theorem weightComponent_of_mem_ne (N Q : ℤ) (x : H) (hx : x ∈ M.wt Q) (h : N ≠ Q) :
    M.weightComponent N x = 0 :=
  DirectSum.decompose_of_mem_ne M.wt hx h.symm

/-- Weight projections commute with a homogeneous linear operator, with the
necessary shift of the source weight. -/
theorem weightComponent_homogeneous_map (A : Module.End ℂ H) (d : ℤ)
    (hA : ∀ N x, x ∈ M.wt N → A x ∈ M.wt (N + d)) (N : ℤ) (x : H) :
    M.weightComponent N (A x) = A (M.weightComponent (N - d) x) := by
  induction x using DirectSum.Decomposition.inductionOn M.wt with
  | zero => simp only [map_zero]
  | homogeneous x =>
    rename_i Q
    by_cases h : N = Q + d
    · subst N
      rw [M.weightComponent_of_mem _ _ (hA Q x x.property)]
      rw [show Q + d - d = Q by omega, M.weightComponent_of_mem Q x x.property]
    · rw [M.weightComponent_of_mem_ne N (Q + d) _ (hA Q x x.property) h,
        M.weightComponent_of_mem_ne (N - d) Q x x.property (by omega), map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem weightComponent_L (N n : ℤ) (x : H) :
    M.weightComponent N (M.L n x) = M.L n (M.weightComponent (N + n) x) := by
  simpa only [sub_neg_eq_add] using M.weightComponent_homogeneous_map (M.L n) (-n)
    (fun Q y hy => by simpa only [sub_eq_add_neg] using M.L_wt n Q y hy) N x

theorem weightComponent_K (N n : ℤ) (hn : n ≠ 0) (x : H) :
    M.weightComponent N (M.K n x) = M.K n (M.weightComponent (N + n) x) := by
  simpa only [sub_neg_eq_add] using M.weightComponent_homogeneous_map (M.K n) (-n)
    (fun Q y hy => by simpa only [sub_eq_add_neg] using M.K_wt n Q y hn hy) N x

theorem negativeSpan_weightComponent (D : ℕ → Module.End ℂ H)
    (hD : ∀ (n : ℕ) (N : ℤ) x, x ∈ M.wt N → D n x ∈ M.wt (N + (n + 1)))
    (N : ℤ) (x : H) (hx : x ∈ ⨆ n, LinearMap.range (D n)) :
    M.weightComponent N x ∈ ⨆ n, LinearMap.range (D n) := by
  let U : Submodule ℂ H := ⨆ n, LinearMap.range (D n)
  refine Submodule.iSup_induction (fun n => LinearMap.range (D n))
    (motive := fun x => M.weightComponent N x ∈ U) hx ?_ ?_ ?_
  · intro n y hy
    rcases hy with ⟨z, rfl⟩
    rw [M.weightComponent_homogeneous_map (D n) (n + 1) (hD n)]
    exact (le_iSup (fun n => LinearMap.range (D n)) n) ⟨_, rfl⟩
  · simpa only [map_zero] using U.zero_mem
  · intro y z hy hz
    simpa only [map_add] using U.add_mem hy hz

theorem positiveKernel_weightComponent (A : ℕ → Module.End ℂ H)
    (hA : ∀ (n : ℕ) (N : ℤ) x, x ∈ M.wt N → A n x ∈ M.wt (N - (n + 1)))
    (N : ℤ) (x : H) (hx : x ∈ ⨅ n, LinearMap.ker (A n)) :
    M.weightComponent N x ∈ ⨅ n, LinearMap.ker (A n) := by
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro n
  have h := M.weightComponent_homogeneous_map (A n) (-(n + 1 : ℤ))
    (fun Q y hy => by simpa only [sub_eq_add_neg] using hA n Q y hy)
    (N - (n + 1)) x
  rw [hx n, map_zero] at h
  simpa only [sub_neg_eq_add, sub_add_cancel] using h.symm

theorem spurious_weightComponent (N : ℤ) (x : H) (hx : x ∈ M.spurious) :
    M.weightComponent N x ∈ M.spurious :=
  M.negativeSpan_weightComponent (fun n => M.L (-(n + 1 : ℤ)))
    (fun n Q y hy => by simpa only [sub_neg_eq_add] using M.L_wt (-(n + 1 : ℤ)) Q y hy) N x hx

theorem kSpurious_weightComponent (N : ℤ) (x : H) (hx : x ∈ M.kSpurious) :
    M.weightComponent N x ∈ M.kSpurious :=
  M.negativeSpan_weightComponent (fun n => M.K (-(n + 1 : ℤ)))
    (fun n Q y hy => by
      simpa only [sub_neg_eq_add] using M.K_wt (-(n + 1 : ℤ)) Q y (by omega) hy) N x hx

theorem physical_weightComponent (N : ℤ) (x : H) (hx : x ∈ M.physical) :
    M.weightComponent N x ∈ M.physical :=
  M.positiveKernel_weightComponent _ (fun n Q y hy => M.L_wt (n + 1 : ℤ) Q y hy) N x hx

theorem kVacuum_weightComponent (N : ℤ) (x : H) (hx : x ∈ M.kVacuum) :
    M.weightComponent N x ∈ M.kVacuum :=
  M.positiveKernel_weightComponent _ (fun n Q y hy => M.K_wt (n + 1 : ℤ) Q y (by omega) hy) N x hx

/-- A spurious vector of weight `N` is a sum of the first two negative images
with source vectors of weights `N - 1` and `N - 2`. -/
theorem spurious_weight_two (N : ℤ) (x : H) (hx : x ∈ M.spurious) (hw : x ∈ M.wt N) :
    ∃ a ∈ M.wt (N - 1), ∃ b ∈ M.wt (N - 2), M.L (-1) a + M.L (-2) b = x := by
  rw [M.spurious_eq_sup_two] at hx
  obtain ⟨a, ⟨u, rfl⟩, b, ⟨v, rfl⟩, he⟩ := Submodule.mem_sup.mp hx
  refine ⟨M.weightComponent (N - 1) u, M.weightComponent_mem _ _,
    M.weightComponent (N - 2) v, M.weightComponent_mem _ _, ?_⟩
  have h := congrArg (M.weightComponent N) he
  simpa only [map_add, M.weightComponent_L, M.weightComponent_of_mem N x hw,
    ← sub_eq_add_neg] using h

/-- Homogeneous summands allow a sum decomposition to be taken weightwise. -/
theorem homogeneous_split_of_sup_eq_top (U W : Submodule ℂ H)
    (hU : ∀ N x, x ∈ U → M.weightComponent N x ∈ U)
    (hW : ∀ N x, x ∈ W → M.weightComponent N x ∈ W)
    (hs : U ⊔ W = ⊤) (N : ℤ) :
    M.weightSlice U N ⊔ M.weightSlice W N = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨u, hu, w, hw, he⟩ := Submodule.mem_sup.mp (show (x : H) ∈ U ⊔ W by rw [hs]; trivial)
  apply Submodule.mem_sup.mpr
  refine ⟨⟨M.weightComponent N u, M.weightComponent_mem N u⟩, hU N u hu,
    ⟨M.weightComponent N w, M.weightComponent_mem N w⟩, hW N w hw, ?_⟩
  apply Subtype.ext
  have h := congrArg (M.weightComponent N) he
  simpa only [map_add, M.weightComponent_of_mem N x x.property] using h

/-- The light-cone splitting restricts to a complementary pair in every finite weight space. -/
theorem lightConeSplit_weight (hF : M.LightConeSplit) (N : ℤ) :
    IsCompl (M.weightSlice M.spurious N) (M.weightSlice M.kVacuum N) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hk
    apply Subtype.ext
    exact Submodule.disjoint_def.mp hF.disjoint x hx hk
  · exact codisjoint_iff.mpr (M.homogeneous_split_of_sup_eq_top M.spurious M.kVacuum
      M.spurious_weightComponent M.kVacuum_weightComponent hF.sup_eq_top N)

end VOA.Moonshine.ConwayNorton.StringModule
