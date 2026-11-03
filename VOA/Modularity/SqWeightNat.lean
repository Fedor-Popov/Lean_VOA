/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.SqWeightSpanning

/-!
# The square-bracket weight spaces at **natural-number** weights already span `𝒱`

`Modularity.SqWeightSpanning.sqWeightSpansTop_holds` proves `⨆ k : ℂ, sqWeightSpace 𝒱 k = ⊤`.  But
every modularity statement quantified over homogeneous vectors — `TraceSpanning`,
`TraceIndependent`,
`FibreIndependent`, `ZhuModularityAnalytic` — quantifies `v ∈ sqWeightSpace 𝒱 (n : ℂ)` with
**`n : ℕ`**, because the automorphy exponent `(cτ+d)ⁿ` is a natural number.  So to pass from "the
identity holds on every homogeneous `v`" to "it holds on every `v`", the `ℕ`-indexed supremum is
what is needed.

It is available for free: the induction in `gradeLE_le_iSup_sqWeightSpace` only ever produces
eigenvectors at eigenvalue `((m : ℤ) : ℂ)` with `m : ℕ`, bottoming out at `gradeLE 𝒱 (-1) = ⊥` by
`W.positivity`.  This file records the `ℕ`-indexed conclusion.

## Main results

* `gradeLE_le_iSup_sqWeightSpace_nat`;
* `sqWeightSpace_nat_spans_top` — `⨆ n : ℕ, sqWeightSpace 𝒱 (n : ℂ) = ⊤`;
* `eq_of_forall_sqWeightSpace_nat` — a linear map vanishing on every natural-weight
  homogeneous vector is zero.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The `ℕ`-indexed form of `gradeLE_le_iSup_sqWeightSpace`. -/
theorem gradeLE_le_iSup_sqWeightSpace_nat (W : VertexOperatorAlgebra 𝒱) :
    ∀ (n : ℕ), gradeLE W ((n : ℤ) - 1) ≤ ⨆ m : ℕ, sqWeightSpace W ((m : ℕ) : ℂ) := by
  intro n
  induction n with
  | zero =>
      rw [show ((0 : ℕ) : ℤ) - 1 = -1 from by norm_num, gradeLE_eq_bot W (by norm_num)]
      exact bot_le
  | succ m ih =>
      rw [show ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) from by push_cast; ring, gradeLE_split W (m : ℤ)]
      refine sup_le (fun x hx => ?_) ih
      have hw : Lsq W 0 x - ((m : ℤ) : ℂ) • x ∈ gradeLE W ((m : ℤ) - 1) :=
        Lsq_zero_sub_smul_mem_gradeLE W hx
      obtain ⟨y, hymem, hyeq⟩ :=
        sub_smul_surj W (m : ℤ) m (Lsq W 0 x - ((m : ℤ) : ℂ) • x)
          (by rw [show ((m : ℕ) : ℤ) - 1 = (m : ℤ) - 1 from by push_cast; ring]; exact hw)
          (by push_cast; omega)
      have hymem' : y ∈ gradeLE W ((m : ℤ) - 1) := by
        rw [show ((m : ℕ) : ℤ) - 1 = (m : ℤ) - 1 from by push_cast; ring] at hymem
        exact hymem
      have heig : x - y ∈ sqWeightSpace W ((m : ℤ) : ℂ) := by
        rw [mem_sqWeightSpace_iff, map_sub, smul_sub]
        have : Lsq W 0 y - ((m : ℤ) : ℂ) • y = Lsq W 0 x - ((m : ℤ) : ℂ) • x := hyeq
        linear_combination (norm := abel) -this
      have heig' : x - y ∈ sqWeightSpace W ((m : ℕ) : ℂ) := by
        rwa [show ((m : ℕ) : ℂ) = ((m : ℤ) : ℂ) from by push_cast; ring]
      have hx' : x = (x - y) + y := by abel
      rw [hx']
      exact Submodule.add_mem _ (Submodule.mem_iSup_of_mem m heig') (ih hymem')

/-- **The natural-weight square-bracket eigenspaces span `𝒱`.** -/
theorem sqWeightSpace_nat_spans_top (W : VertexOperatorAlgebra 𝒱) :
    (⨆ m : ℕ, sqWeightSpace W ((m : ℕ) : ℂ)) = ⊤ := by
  refine eq_top_iff.mpr (fun x _ => ?_)
  obtain ⟨d, hd⟩ := exists_mem_gradeLE W x
  exact gradeLE_le_iSup_sqWeightSpace_nat W (d + 1).toNat
    (gradeLE_mono W (show d ≤ (((d + 1).toNat : ℤ)) - 1 by omega) hd)

/-- **A linear functional that kills every natural-weight homogeneous vector is zero.**  This
is the step that upgrades "for all homogeneous `v`" to "for all `v`". -/
theorem eq_zero_of_forall_sqWeightSpace_nat (W : VertexOperatorAlgebra 𝒱) {α : Type u}
    [AddCommGroup α] [Module ℂ α] (f : 𝒱 →ₗ[ℂ] α)
    (hf : ∀ (m : ℕ), ∀ v ∈ sqWeightSpace W ((m : ℕ) : ℂ), f v = 0) : f = 0 := by
  refine LinearMap.ext fun x => ?_
  have hx : x ∈ (⨆ m : ℕ, sqWeightSpace W ((m : ℕ) : ℂ)) := by
    rw [sqWeightSpace_nat_spans_top]; trivial
  refine Submodule.iSup_induction (fun m : ℕ => sqWeightSpace W ((m : ℕ) : ℂ))
    (motive := fun y => f y = 0) hx ?_ ?_ ?_
  · intro m v hv; exact hf m v hv
  · exact map_zero f
  · intro u v hu hv; rw [map_add, hu, hv, add_zero]

end VOA
