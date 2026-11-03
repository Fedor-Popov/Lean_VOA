import VOA.Huang.TensorCatSkewUnit
import VOA.Modules.OrdSubmodule

/-! # Universal modes span a fusion product as a vector space

This strengthens module-map uniqueness to linear-map uniqueness. It permits
successive tests on nested universal modes in the later coherence arguments.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {X Y : Ordinary W} (P : Product X.isMod Y.isMod)

/-- The linear span of all coefficients, with no homogeneity restriction. -/
def modeSpan : Submodule ℂ P.carrier :=
  Submodule.span ℂ {v | ∃ n x y, v = P.intertwiner.val n x y}

theorem intertwiner_mem_modeSpan (n : ℂ) (x : X.carrier) (y : Y.carrier) :
    P.intertwiner.val n x y ∈ modeSpan P :=
  Submodule.subset_span ⟨n, x, y, rfl⟩

/-- The commutator formula makes the coefficient span mode-stable. -/
def modeSpanSubmodule : WeakModule.Submodule' P.isMod.toWeakModule where
  carrier := modeSpan P
  act_mem := by
    intro a m v hv
    refine Submodule.span_induction (p := fun v _ =>
      mode (P.isMod.YM a) m v ∈ modeSpan P) ?_ ?_ ?_ ?_ hv
    · rintro v ⟨n, x, y, rfl⟩
      have h := P.intertwiner.property.commutator a x y m n
      rw [← sub_add_cancel (mode (P.isMod.YM a) m (P.intertwiner.val n x y))
        (P.intertwiner.val n x (mode (Y.isMod.YM a) m y)), h]
      exact (modeSpan P).add_mem
        (BottomRecovery.finsum_mem_submodule _ _ (fun i =>
          (modeSpan P).smul_mem _ (intertwiner_mem_modeSpan P _ _ _)))
        (intertwiner_mem_modeSpan P _ _ _)
    · simpa only [map_zero] using (modeSpan P).zero_mem
    · intro v w _ _ hv hw
      simpa only [map_add] using (modeSpan P).add_mem hv hw
    · intro c v _ hv
      simpa only [map_smul] using (modeSpan P).smul_mem c hv

private def spanModes : IntertwiningModes X.carrier Y.carrier (modeSpan P) :=
  fun n => LinearMap.mk₂ ℂ
    (fun x y => ⟨P.intertwiner.val n x y, intertwiner_mem_modeSpan P n x y⟩)
    (fun x x' y => Subtype.ext (congrArg (fun f => f y)
      ((P.intertwiner.val n).map_add x x')))
    (fun c x y => Subtype.ext (congrArg (fun f => f y)
      ((P.intertwiner.val n).map_smul c x)))
    (fun x y y' => Subtype.ext ((P.intertwiner.val n x).map_add y y'))
    (fun c x y => Subtype.ext ((P.intertwiner.val n x).map_smul c y))

private theorem spanModes_isIntertwining : IsIntertwiningOperator X.isMod Y.isMod
    (P.isMod.submodule (modeSpanSubmodule P)) (spanModes P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y n
    obtain ⟨N, hN⟩ := P.intertwiner.property.truncation x y n
    exact ⟨N, fun k hk => Subtype.ext (hN k hk)⟩
  · intro x n
    ext y
    exact congrArg (fun f => f y) (P.intertwiner.property.L_neg_one x n)
  · intro a x y l m n
    apply Subtype.ext
    rw [PzTensorSemisimple.coe_finsum_submodule, PzTensorSemisimple.coe_finsum_submodule]
    exact P.intertwiner.property.jacobi a x y l m n

/-- The full coefficient span is the entire representing module. -/
theorem modeSpan_eq_top : modeSpan P = ⊤ := by
  let S := P.isMod.submodule (modeSpanSubmodule P)
  let I : IntertwiningOperator X.isMod Y.isMod S := ⟨spanModes P, spanModes_isIntertwining P⟩
  let inc : homSpace S P.isMod := ⟨(modeSpan P).subtype, fun _ _ _ => rfl⟩
  let f := P.lift S I
  let idP : homSpace P.isMod P.isMod := ⟨LinearMap.id, fun _ _ _ => rfl⟩
  have hf : compHom inc f = idP := by
    apply P.hom_ext P.isMod
    intro n x y
    exact congrArg (fun J : IntertwiningOperator X.isMod Y.isMod S =>
      ((J.val n x y : modeSpan P) : P.carrier)) (P.lift_spec S I)
  apply top_unique
  intro x _
  have hx := congrArg (fun g : homSpace P.isMod P.isMod => g.val x) hf
  change (f.val x).val = x at hx
  exact hx ▸ (f.val x).property

/-- Arbitrary linear maps, not just module maps, are determined by universal modes. -/
theorem tensor_linear_ext {N : Type*} [AddCommGroup N] [Module ℂ N]
    (f g : P.carrier →ₗ[ℂ] N)
    (h : ∀ n x y, f (P.intertwiner.val n x y) = g (P.intertwiner.val n x y)) : f = g := by
  apply LinearMap.ext_on (s := {v | ∃ n x y, v = P.intertwiner.val n x y})
    (modeSpan_eq_top P)
  rintro v ⟨n, x, y, rfl⟩
  exact h n x y

end VOA.Huang.TensorCat
