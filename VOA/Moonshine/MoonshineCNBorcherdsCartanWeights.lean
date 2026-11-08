import VOA.Moonshine.MoonshineCNBorcherdsRootCutoff
import VOA.Moonshine.MoonshineCNBorcherdsParabolic
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.Algebra.DirectSum.Module

/-! Weight spaces of an arbitrary representation, as simultaneous Cartan eigenspaces.

They are automatically independent and are shifted by root vectors.  The only extra input
needed for an admissible grading is that weight vectors of bounded-below height span; the
kernel of a Cartan-intertwining map out of such a module is again spanned by weight vectors. -/

noncomputable section
open Module
namespace VOA.Moonshine.ConwayNorton

theorem borcherdsCartanPairing_weight_add (ξ : ℂ × ℂ) (μ α : ℤ × ℤ) :
    borcherdsCartanPairing ξ (borcherdsWeightVector (μ + α)) =
      borcherdsCartanPairing ξ (borcherdsWeightVector μ) +
        borcherdsCartanPairing ξ (borcherdsWeightVector α) := by
  simp only [borcherdsCartanPairing, borcherdsWeightVector, Prod.fst_add, Prod.snd_add,
    Int.cast_add]
  ring

theorem borcherdsCartanPairing_weight_zero (ξ : ℂ × ℂ) :
    borcherdsCartanPairing ξ (borcherdsWeightVector 0) = 0 := by
  simp [borcherdsCartanPairing, borcherdsWeightVector]

/-- A lattice weight is determined by the Cartan character it defines. -/
theorem borcherdsWeightCharacter_injective :
    Function.Injective (fun μ : ℤ × ℤ => fun ξ : ℂ × ℂ =>
      borcherdsCartanPairing ξ (borcherdsWeightVector μ)) := by
  intro μ ν h
  have h₁ := congrFun h (0, 1)
  have h₂ := congrFun h (1, 0)
  simp only [borcherdsCartanPairing, borcherdsWeightVector, zero_mul, one_mul, mul_one,
    mul_zero, zero_add, add_zero, neg_inj] at h₁ h₂
  exact Prod.ext (by exact_mod_cast h₁) (by exact_mod_cast h₂)

/-- The kernel of a map which respects two families of subspaces, the source family spanning
and the target family independent, is spanned by its intersections with the source family. -/
theorem ker_le_iSup_inf_of_graded {ι M M' : Type*}
    [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
    (W : ι → Submodule ℂ M) (W' : ι → Submodule ℂ M') (Φ : M →ₗ[ℂ] M')
    (hΦ : ∀ i, W i ≤ (W' i).comap Φ) (hW : iSup W = ⊤) (hW' : iSupIndep W') :
    LinearMap.ker Φ ≤ ⨆ i, (LinearMap.ker Φ ⊓ W i) := by
  classical
  intro k hk
  have hkW : k ∈ iSup W := by rw [hW]; trivial
  obtain ⟨f, rfl⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp W k).mp hkW
  let ψ : ∀ i, W i →ₗ[ℂ] W' i := fun i =>
    (Φ.comp (W i).subtype).codRestrict (W' i) (fun w => hΦ i w.2)
  have hcomp : (DFinsupp.lsum ℕ fun i => (W' i).subtype).comp (DFinsupp.mapRange.linearMap ψ) =
      Φ.comp (DFinsupp.lsum ℕ fun i => (W i).subtype) := by
    apply DFinsupp.lhom_ext'
    intro i
    apply LinearMap.ext
    intro w
    simp [ψ]
  have hzero : DFinsupp.mapRange.linearMap ψ f = 0 := by
    apply hW'.dfinsupp_lsum_injective
    rw [map_zero]
    have h := LinearMap.congr_fun hcomp f
    simp only [LinearMap.comp_apply] at h
    rw [h]
    exact hk
  have hker : ∀ i, Φ (f i) = 0 := by
    intro i
    have h := congrArg (fun F => ((F i : W' i) : M')) hzero
    simpa [ψ] using h
  rw [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply]
  apply Submodule.dfinsuppSum_mem
  intro i _
  exact Submodule.mem_iSup_of_mem i ⟨hker i, (f i).property⟩

variable {g M : Type*} [LieRing g] [LieAlgebra ℂ g] [AddCommGroup M] [Module ℂ M]

namespace BorcherdsData
variable (D : BorcherdsData g) (ρ : g →ₗ⁅ℂ⁆ End ℂ M)

/-- The simultaneous eigenspace of the Cartan action at a lattice weight. -/
def cartanEigenspace (μ : ℤ × ℤ) : Submodule ℂ M :=
  ⨅ ξ : ℂ × ℂ, Module.End.eigenspace (ρ (D.cartanMap ξ))
    (borcherdsCartanPairing ξ (borcherdsWeightVector μ))

theorem mem_cartanEigenspace {μ : ℤ × ℤ} {v : M} :
    v ∈ D.cartanEigenspace ρ μ ↔
      ∀ ξ, ρ (D.cartanMap ξ) v = borcherdsCartanPairing ξ (borcherdsWeightVector μ) • v := by
  simp only [cartanEigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

theorem cartan_bracket_eq_zero (ξ ζ : ℂ × ℂ) : ⁅D.cartanMap ξ, D.cartanMap ζ⁆ = 0 := by
  rw [D.cartan_action ξ 0 _ (D.cartan_mem_weight_zero ζ), borcherdsCartanPairing_weight_zero,
    zero_smul]

theorem cartan_action_commute (ξ ζ : ℂ × ℂ) :
    Commute (ρ (D.cartanMap ξ)) (ρ (D.cartanMap ζ)) := by
  have h := ρ.map_lie (D.cartanMap ξ) (D.cartanMap ζ)
  rw [D.cartan_bracket_eq_zero, map_zero, Ring.lie_def] at h
  exact (sub_eq_zero.mp h.symm : _)

/-- A homogeneous root vector shifts Cartan eigenspaces by its weight. -/
theorem cartanEigenspace_action {α μ : ℤ × ℤ} {x : g} {v : M}
    (hx : x ∈ D.weightSpace α) (hv : v ∈ D.cartanEigenspace ρ μ) :
    ρ x v ∈ D.cartanEigenspace ρ (μ + α) := by
  rw [mem_cartanEigenspace] at hv ⊢
  intro ξ
  have h := congrArg (fun T : End ℂ M => T v) (ρ.map_lie (D.cartanMap ξ) x)
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [D.cartan_action ξ α x hx, map_smul, LinearMap.smul_apply, hv ξ, map_smul] at h
  rw [eq_sub_iff_add_eq] at h
  rw [borcherdsCartanPairing_weight_add, add_smul, ← h, add_comm]

/-- Cartan eigenspaces for distinct lattice weights are independent. -/
theorem cartanEigenspace_iSupIndep : iSupIndep (D.cartanEigenspace ρ) := by
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (f := fun ξ : ℂ × ℂ => ρ (D.cartanMap ξ))
    (fun ξ ζ φ => Module.End.mapsTo_maxGenEigenspace_of_comm (D.cartan_action_commute ρ ζ ξ) φ)
  refine (h.comp borcherdsWeightCharacter_injective).mono fun μ => ?_
  exact iInf_mono fun ξ => Module.End.eigenspace_le_maxGenEigenspace

/-- If weights satisfying `P` span, every other eigenspace vanishes. -/
theorem cartanEigenspace_eq_bot_of_span (P : ℤ × ℤ → Prop)
    (hspan : ⨆ μ, ⨆ (_ : P μ), D.cartanEigenspace ρ μ = ⊤) {μ : ℤ × ℤ} (hμ : ¬ P μ) :
    D.cartanEigenspace ρ μ = ⊥ := by
  apply (iSupIndep_def.mp (D.cartanEigenspace_iSupIndep ρ) μ).eq_bot_of_le
  calc D.cartanEigenspace ρ μ ≤ ⊤ := le_top
    _ = ⨆ ν, ⨆ (_ : P ν), D.cartanEigenspace ρ ν := hspan.symm
    _ ≤ ⨆ ν, ⨆ (_ : ν ≠ μ), D.cartanEigenspace ρ ν :=
      iSup_mono fun ν => iSup_le fun hν =>
        le_iSup_of_le (fun h => hμ (h ▸ hν)) le_rfl

/-- Root vectors with weights in `Q` map the span of the eigenspaces with weights in `P` into the
span of the eigenspaces with weights in `P'`, when adding `Q` carries `P` into `P'`. -/
theorem cartanEigenspace_span_maps (P P' Q : ℤ × ℤ → Prop)
    (hPQ : ∀ μ α, P μ → Q α → P' (μ + α)) {x : g} (hx : x ∈ D.weightSpan Q) {v : M}
    (hv : v ∈ ⨆ μ, ⨆ (_ : P μ), D.cartanEigenspace ρ μ) :
    ρ x v ∈ ⨆ μ, ⨆ (_ : P' μ), D.cartanEigenspace ρ μ := by
  induction hx using Submodule.iSup_induction' with
  | mem α x hx =>
      induction hx using Submodule.iSup_induction' with
      | mem hα x hx =>
          induction hv using Submodule.iSup_induction' with
          | mem μ v hv =>
              induction hv using Submodule.iSup_induction' with
              | mem hμ v hv =>
                  exact Submodule.mem_iSup_of_mem (μ + α)
                    (Submodule.mem_iSup_of_mem (hPQ μ α hμ hα)
                      (D.cartanEigenspace_action ρ hx hv))
              | zero => simp
              | add v w _ _ hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw
          | zero => simp
          | add v w _ _ hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw
      | zero => simp
      | add x y _ _ hx hy =>
          rw [map_add, LinearMap.add_apply]
          exact Submodule.add_mem _ hx hy
  | zero => simp
  | add x y _ _ hx hy =>
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ hx hy

/-- Root vectors with weights in `Q` preserve the span of the eigenspaces with weights in `P`,
when `P` is stable under adding `Q`. -/
theorem cartanEigenspace_span_stable (P Q : ℤ × ℤ → Prop)
    (hPQ : ∀ μ α, P μ → Q α → P (μ + α)) {x : g} (hx : x ∈ D.weightSpan Q) {v : M}
    (hv : v ∈ ⨆ μ, ⨆ (_ : P μ), D.cartanEigenspace ρ μ) :
    ρ x v ∈ ⨆ μ, ⨆ (_ : P μ), D.cartanEigenspace ρ μ :=
  D.cartanEigenspace_span_maps ρ P P Q hPQ hx hv

/-- An admissible grading by Cartan eigenspaces, once the weights in a height-bounded set span. -/
def cartanAdmissible (h₀ : ℤ) (P : ℤ × ℤ → Prop)
    (hP : ∀ μ, P μ → h₀ ≤ borcherdsRootHeight μ)
    (hspan : ⨆ μ, ⨆ (_ : P μ), D.cartanEigenspace ρ μ = ⊤) : BorcherdsAdmissible D ρ where
  weightSpace := D.cartanEigenspace ρ
  weight_internal := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (D.cartanEigenspace_iSupIndep ρ)
    (top_unique (hspan.symm.le.trans (iSup_mono fun _ => iSup_le fun _ => le_rfl)))
  action_weight hx hv := D.cartanEigenspace_action ρ hx hv
  cartan_action ξ _ _ hv := (D.mem_cartanEigenspace ρ).mp hv ξ
  lowerHeight := h₀
  below_eq_bot μ hμ := D.cartanEigenspace_eq_bot_of_span ρ P hspan
    (fun h => (not_le.mpr hμ) (hP μ h))

@[simp] theorem cartanAdmissible_weightSpace (h₀ : ℤ) (P : ℤ × ℤ → Prop)
    (hP : ∀ μ, P μ → h₀ ≤ borcherdsRootHeight μ)
    (hspan : ⨆ μ, ⨆ (_ : P μ), D.cartanEigenspace ρ μ = ⊤) :
    (D.cartanAdmissible ρ h₀ P hP hspan).weightSpace = D.cartanEigenspace ρ := rfl

/-- A Cartan-intertwining map has a kernel spanned by its homogeneous kernel vectors. -/
theorem cartanEigenspace_kernel_graded {M' : Type*} [AddCommGroup M'] [Module ℂ M']
    (ρ' : g →ₗ⁅ℂ⁆ End ℂ M') (Φ : M →ₗ[ℂ] M')
    (hΦ : ∀ ξ v, Φ (ρ (D.cartanMap ξ) v) = ρ' (D.cartanMap ξ) (Φ v))
    (hspan : ⨆ μ, D.cartanEigenspace ρ μ = ⊤) :
    LinearMap.ker Φ ≤ ⨆ μ, (LinearMap.ker Φ ⊓ D.cartanEigenspace ρ μ) := by
  apply ker_le_iSup_inf_of_graded _ _ Φ _ hspan (D.cartanEigenspace_iSupIndep ρ')
  intro μ v hv
  change Φ v ∈ D.cartanEigenspace ρ' μ
  rw [mem_cartanEigenspace] at hv ⊢
  intro ξ
  rw [← hΦ, hv ξ, map_smul]

end BorcherdsData
end VOA.Moonshine.ConwayNorton
