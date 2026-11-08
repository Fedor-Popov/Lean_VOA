/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNStringModule

/-! # Orthogonals inside a string module's finite weight spaces

These statements need no light-cone splitting and hold at every central charge.
The common-kernel identity is proved directly by adjointness and nondegeneracy
on the lower weight space. Double orthogonals and dimensions are then ordinary
finite-dimensional bilinear algebra.
-/

namespace VOA.Moonshine.ConwayNorton.StringModule

universe u
variable {H : Type u} [AddCommGroup H] [Module ℂ H] (M : StringModule H)

/-- Common kernels are orthogonal to the span of the adjoint images. -/
theorem positiveKernel_pair_negativeSpan (A D : ℕ → Module.End ℂ H)
    (hadj : ∀ n x y, M.B (A n x) y = M.B x (D n y))
    (x y : H) (hx : ∀ n, A n x = 0)
    (hy : y ∈ ⨆ n, LinearMap.range (D n)) : M.B x y = 0 := by
  refine Submodule.iSup_induction (fun n => LinearMap.range (D n))
    (motive := fun y => M.B x y = 0) hy ?_ ?_ ?_
  · intro n y hy
    rcases hy with ⟨z, rfl⟩
    rw [← hadj, hx n, map_zero, LinearMap.zero_apply]
  · exact map_zero _
  · intro y z hy hz
    rw [map_add, hy, hz, add_zero]

/-- The common kernel at weight `N` is exactly the orthogonal of the adjoint
negative span at that weight. The full operator degrees are explicit inputs. -/
theorem positiveKernel_weight_orthogonal (A D : ℕ → Module.End ℂ H)
    (hA : ∀ (n : ℕ) (N : ℤ) (x : H), x ∈ M.wt N → A n x ∈ M.wt (N - (n + 1)))
    (hD : ∀ (n : ℕ) (N : ℤ) (x : H), x ∈ M.wt N → D n x ∈ M.wt (N + (n + 1)))
    (hadj : ∀ n x y, M.B (A n x) y = M.B x (D n y)) (N : ℤ) :
    M.weightSlice (⨅ n, LinearMap.ker (A n)) N =
      (M.stringWeightForm N).orthogonal
        (M.weightSlice (⨆ n, LinearMap.range (D n)) N) := by
  ext x
  constructor
  · intro hx y hy
    change M.B (y : H) (x : H) = 0
    rw [M.B_symm.eq]
    apply M.positiveKernel_pair_negativeSpan A D hadj x y
    · simpa [weightSlice, Submodule.mem_iInf, LinearMap.mem_ker] using hx
    · exact hy
  · intro hx
    change (x : H) ∈ ⨅ n, LinearMap.ker (A n)
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro n
    apply M.B_nondeg (N - (n + 1)) _ (hA n N x x.property)
    intro y hy
    rw [hadj, M.B_symm.eq]
    have hw : D n y ∈ M.wt N := by
      simpa using hD n (N - (n + 1)) y hy
    exact hx ⟨D n y, hw⟩ ((le_iSup (fun i => LinearMap.range (D i)) n) ⟨y, rfl⟩)

theorem physical_pair_spurious (x y : H) (hx : x ∈ M.physical)
    (hy : y ∈ M.spurious) : M.B x y = 0 :=
  M.positiveKernel_pair_negativeSpan _ _ (fun n => M.L_adj (n + 1 : ℤ))
    x y ((M.mem_physical_iff x).mp hx) hy

theorem kVacuum_pair_kSpurious (x y : H) (hx : x ∈ M.kVacuum)
    (hy : y ∈ M.kSpurious) : M.B x y = 0 :=
  M.positiveKernel_pair_negativeSpan _ _ (fun n => M.K_adj (n + 1 : ℤ))
    x y ((M.mem_kVacuum_iff x).mp hx) hy

/-- `P` at a fixed weight is the orthogonal of `S` at that weight. -/
theorem orthogonal_spurious_eq (N : ℤ) :
    (M.stringWeightForm N).orthogonal (M.weightSlice M.spurious N) =
      M.weightSlice M.physical N := by
  symm
  apply M.positiveKernel_weight_orthogonal
    (fun n => M.L (n + 1 : ℤ)) (fun n => M.L (-(n + 1 : ℤ)))
  · exact fun n N x hx => M.L_wt _ N x hx
  · intro n N x hx
    simpa only [sub_neg_eq_add] using M.L_wt (-(n + 1 : ℤ)) N x hx
  · exact fun n => M.L_adj (n + 1 : ℤ)

/-- `K` at a fixed weight is the orthogonal of `S_K` at that weight. -/
theorem orthogonal_kSpurious_eq (N : ℤ) :
    (M.stringWeightForm N).orthogonal (M.weightSlice M.kSpurious N) =
      M.weightSlice M.kVacuum N := by
  symm
  apply M.positiveKernel_weight_orthogonal
    (fun n => M.K (n + 1 : ℤ)) (fun n => M.K (-(n + 1 : ℤ)))
  · exact fun n N x hx => M.K_wt _ N x (by omega) hx
  · intro n N x hx
    simpa only [sub_neg_eq_add] using M.K_wt (-(n + 1 : ℤ)) N x (by omega) hx
  · exact fun n => M.K_adj (n + 1 : ℤ)

/-- Finite-dimensional double orthogonals give `P`'s orthogonal exactly. -/
theorem orthogonal_physical_eq (N : ℤ) :
    (M.stringWeightForm N).orthogonal (M.weightSlice M.physical N) =
      M.weightSlice M.spurious N := by
  letI := M.wt_finite N
  rw [← M.orthogonal_spurious_eq N]
  exact (M.stringWeightForm N).orthogonal_orthogonal
    (M.stringWeightForm_nondegenerate N) (M.stringWeightForm_symm N).isRefl _

/-- Finite-dimensional double orthogonals give `K`'s orthogonal exactly. -/
theorem orthogonal_kVacuum_eq (N : ℤ) :
    (M.stringWeightForm N).orthogonal (M.weightSlice M.kVacuum N) =
      M.weightSlice M.kSpurious N := by
  letI := M.wt_finite N
  rw [← M.orthogonal_kSpurious_eq N]
  exact (M.stringWeightForm N).orthogonal_orthogonal
    (M.stringWeightForm_nondegenerate N) (M.stringWeightForm_symm N).isRefl _

/-- The dimensions of physical and spurious vectors add to the whole weight space. -/
theorem physical_spurious_finrank (N : ℤ) :
    Module.finrank ℂ (M.weightSlice M.spurious N) +
      Module.finrank ℂ (M.weightSlice M.physical N) = Module.finrank ℂ (M.wt N) := by
  letI := M.wt_finite N
  have h := (M.stringWeightForm N).finrank_add_finrank_orthogonal
    (M.stringWeightForm_symm N).isRefl (M.weightSlice M.spurious N)
  rw [M.orthogonal_spurious_eq N,
    (M.stringWeightForm N).orthogonal_top_eq_bot (M.stringWeightForm_nondegenerate N)] at h
  rw [inf_bot_eq, finrank_bot, add_zero] at h
  exact h

/-- The dimensions of longitudinal vacua and spurious vectors add to the weight space. -/
theorem kVacuum_kSpurious_finrank (N : ℤ) :
    Module.finrank ℂ (M.weightSlice M.kSpurious N) +
      Module.finrank ℂ (M.weightSlice M.kVacuum N) = Module.finrank ℂ (M.wt N) := by
  letI := M.wt_finite N
  have h := (M.stringWeightForm N).finrank_add_finrank_orthogonal
    (M.stringWeightForm_symm N).isRefl (M.weightSlice M.kSpurious N)
  rw [M.orthogonal_kSpurious_eq N,
    (M.stringWeightForm N).orthogonal_top_eq_bot (M.stringWeightForm_nondegenerate N)] at h
  rw [inf_bot_eq, finrank_bot, add_zero] at h
  exact h

end VOA.Moonshine.ConwayNorton.StringModule
