import VOA.Classification.COne.McRaeM2Socle

/-!
# McRae's route: the double contragredient `N ≅ N''`

For a graded weak module `N` (`C2Rigid.GWModule`, `L₀` possibly non-semisimple):

* `iota N : M → (N')'`, `x ↦ ⟨·, x⟩`, characterized by `⟨φ, ι x⟩ = ⟨x, φ⟩` for homogeneous
  `φ ∈ N'` (`pairing_iota`);
* `iotaHom N : N →  N''` is a weak-module homomorphism.  The mode identity is the involution
  identity `e^{zL₁}(−z⁻²)^{L₀}` twice = identity, in the form `mode_eq_sum_dualAdj`;
* `iota_bijective` — `ι` is bijective (finite-dimensional double duality on each piece).
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.C2Rigid
open VOA.Classification.COne VOA.Classification.COne.PlusSplitting
open VOA.Huang.LogRemovalAdmissible

universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V}

section DoubleDual
variable (N : GWModule W M)

/-- Evaluation of a homogeneous vector on the matching piece of the contragredient. -/
def evW (α : ℂ) : N.weight α →ₗ[ℂ] Module.Dual ℂ ((contra N).weight α) where
  toFun y := (dualPairing N (y : M)).comp ((contra N).weight α).subtype
  map_add' a b := by
    refine LinearMap.ext fun φ => ?_
    simp only [LinearMap.comp_apply, Submodule.coe_add, LinearMap.add_apply]
    exact dualPairing_add_left N _ _ _
  map_smul' c a := by
    refine LinearMap.ext fun φ => ?_
    simp only [LinearMap.comp_apply, SetLike.val_smul, LinearMap.smul_apply, RingHom.id_apply]
    exact dualPairing_smul_left N _ _ _

@[simp] theorem evW_apply (α : ℂ) (y : N.weight α) (φ : (contra N).weight α) :
    evW N α y φ = dualPairing N (y : M) (φ : RestrictedDual N) := rfl

/-- The canonical map `M → (N')'`. -/
def iota : M →ₗ[ℂ] RestrictedDual (contra N) :=
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
  (DFinsupp.mapRange.linearMap (fun α => evW N α)) ∘ₗ
    (DirectSum.decomposeLinearEquiv N.weight).toLinearMap

theorem component_iota (β : ℂ) (x : M) :
    DirectSum.component ℂ ℂ (fun γ => Module.Dual ℂ ((contra N).weight γ)) β (iota N x) =
      evW N β ⟨cmp N β x, cmp_mem N β x⟩ := by
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
  rfl

/-- A homogeneous element of the contragredient is the extension by zero of its component. -/
theorem eq_lofD_of_mem {β : ℂ} {φ : RestrictedDual N} (hφ : φ ∈ (contra N).weight β) :
    φ = lofD N β (fc N β φ) := by
  rw [← cmpD_eq]
  exact (cmp_of_mem (Dm N) hφ).symm

/-- `⟨φ, ι x⟩ = ⟨x, φ⟩` for homogeneous `φ`. -/
theorem pairing_iota {β : ℂ} {φ : RestrictedDual N} (hφ : φ ∈ (contra N).weight β) (x : M) :
    dualPairing (contra N) φ (iota N x) = dualPairing N x φ := by
  rw [dualPairing_component (contra N) _ hφ, component_iota, evW_apply, pr_cmp]
  congr 1
  exact (eq_lofD_of_mem N hφ).symm

/-- The pairing of a module mode, transposed (the involution identity). -/
theorem pairing_mode_eq {w : ℤ} {a : V} (ha : a ∈ W.grading w) (p : ℤ) (x : M)
    (φ : RestrictedDual N) :
    dualPairing N (mode (N.YM a) p x) φ =
      ((-1 : ℂ) ^ w • ∑ j ∈ Finset.range (w.toNat + 1), ((j.factorial : ℂ))⁻¹ •
        dualPairingFlip N (mode (YMdual N ((W.L 1 ^ j) a)) (2 * w - p - 2 - j) φ)) x := by
  let L : M →ₗ[ℂ] ℂ := (dualPairingFlip N φ) ∘ₗ (mode (N.YM a) p)
  let R : M →ₗ[ℂ] ℂ := (-1 : ℂ) ^ w • ∑ j ∈ Finset.range (w.toNat + 1), ((j.factorial : ℂ))⁻¹ •
        dualPairingFlip N (mode (YMdual N ((W.L 1 ^ j) a)) (2 * w - p - 2 - j) φ)
  have hLR : L = R := by
    refine LinearMap.ext fun x => ?_
    have hx : x ∈ ⨆ α, N.weight α := by
      rw [N.isInternal.submodule_iSup_eq_top]; trivial
    refine Submodule.iSup_induction N.weight (motive := fun x => L x = R x) hx ?_ ?_ ?_
    · intro α y hy
      change dualPairing N (mode (N.YM a) p y) φ = R y
      rw [mode_eq_sum_dualAdj N ha p hy, ← dualPairingFlip_apply, map_smul, map_sum]
      simp only [R, LinearMap.smul_apply, LinearMap.coeFn_sum, Finset.sum_apply]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, dualPairingFlip_apply, dualPairingFlip_apply,
        dualPairing_mode_dualAdj N (PlusRat2Dual.L1_pow_mem_grading ha j) _ φ hy]
    · show L 0 = R 0
      rw [map_zero, map_zero]
    · intro y z hy hz
      show L (y + z) = R (y + z)
      rw [map_add, map_add, hy, hz]
  exact congrArg (fun F : M →ₗ[ℂ] ℂ => F x) hLR

/-- `ι` intertwines the modes. -/
theorem iota_mode (u : V) (n : ℤ) (x : M) :
    iota N (mode (N.YM u) n x) = mode (YMdual (contra N) u) n (iota N x) := by
  apply restrictedDual_ext_of_pairing (contra N)
  intro β φ hφ
  rw [pairing_iota N hφ]
  have hu : u ∈ ⨆ w, W.grading w := by
    rw [W.isInternal.submodule_iSup_eq_top]; trivial
  refine Submodule.iSup_induction W.grading
    (motive := fun u => dualPairing N (mode (N.YM u) n x) φ =
      dualPairing (contra N) φ (mode (YMdual (contra N) u) n (iota N x))) hu ?_ ?_ ?_
  · intro w a ha
    rw [dualPairing_mode_dualAdj (contra N) ha n (iota N x) hφ,
      pairing_iota N (dualAdj_mem (contra N) w a n β φ), dualAdj_clean (contra N) ha n hφ,
      pairing_mode_eq N ha n x φ]
    simp only [LinearMap.smul_apply, LinearMap.coeFn_sum, Finset.sum_apply,
      dualPairingFlip_apply, map_smul, map_sum]
    rfl
  · show dualPairing N (mode (N.YM 0) n x) φ =
      dualPairing (contra N) φ (mode (YMdual (contra N) 0) n (iota N x))
    have h1 : mode (N.YM (0 : V)) n = 0 := by rw [map_zero]; rfl
    have h2 : mode (YMdual (contra N) (0 : V)) n = 0 := by rw [map_zero]; rfl
    rw [h1, h2, LinearMap.zero_apply, LinearMap.zero_apply, pr_zero_left,
      LinearMap.map_zero]
  · intro a b ha hb
    show dualPairing N (mode (N.YM (a + b)) n x) φ =
      dualPairing (contra N) φ (mode (YMdual (contra N) (a + b)) n (iota N x))
    have e₁ : mode (N.YM (a + b)) n x = mode (N.YM a) n x + mode (N.YM b) n x := by
      rw [map_add]; rfl
    have e₂ : mode (YMdual (contra N) (a + b)) n (iota N x) =
        mode (YMdual (contra N) a) n (iota N x) + mode (YMdual (contra N) b) n (iota N x) := by
      rw [map_add]; rfl
    rw [e₁, e₂, dualPairing_add_left, LinearMap.map_add, ha, hb]

/-- **The canonical homomorphism `N → N''`.** -/
def iotaHom : N.toWeakModule.Hom (contra (contra N)).toWeakModule where
  toLinearMap := iota N
  map_act u n x := iota_mode N u n x

/-- `ι` is injective. -/
theorem iota_injective : Function.Injective (iota N) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  have hx0 : iota N x = 0 := hx
  have hpair : ∀ φ : RestrictedDual N, dualPairing N x φ = 0 := by
    intro φ
    refine DirectSum.induction_on (β := fun β => Module.Dual ℂ (N.weight β)) φ ?_ ?_ ?_
    · exact LinearMap.map_zero _
    · intro β g
      have hmem : (DirectSum.of (fun β => Module.Dual ℂ (N.weight β)) β g : RestrictedDual N) ∈
          (contra N).weight β := ⟨g, rfl⟩
      rw [← pairing_iota N hmem, hx0]
      exact pr_zero_left (contra N) _
    · intro a b ha hb
      have : dualPairing N x ((a + b : RestrictedDual N)) = dualPairing N x a + dualPairing N x b :=
        LinearMap.map_add _ _ _
      rw [this, ha, hb, add_zero]
  rw [eq_zero_of_pr N hpair]
  exact Submodule.zero_mem _

/-- On a homogeneous vector, `ι` is the evaluation in the matching piece. -/
theorem iota_of_mem {β : ℂ} {y : M} (hy : y ∈ N.weight β) :
    iota N y = DirectSum.lof ℂ ℂ (fun γ => Module.Dual ℂ ((contra N).weight γ)) β
      (evW N β ⟨y, hy⟩) := by
  classical
  refine DirectSum.ext_component ℂ (fun γ => ?_)
  rw [component_iota]
  by_cases hγ : γ = β
  · subst hγ
    rw [DirectSum.component.lof_self]
    congr 2
    exact cmp_of_mem N hy
  · rw [DirectSum.component.of, dif_neg (Ne.symm hγ)]
    have h0 : (⟨cmp N γ y, cmp_mem N γ y⟩ : N.weight γ) = 0 :=
      Subtype.ext (cmp_of_mem_ne N hy (Ne.symm hγ))
    rw [h0, map_zero]

theorem evW_injective (β : ℂ) : Function.Injective (evW N β) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro y hy
  have hy0 : evW N β y = 0 := hy
  have : y = 0 := by
    apply (Module.forall_dual_apply_eq_zero_iff ℂ y).mp
    intro g
    have h := congrArg (fun F : Module.Dual ℂ ((contra N).weight β) =>
      F ⟨DirectSum.lof ℂ ℂ (fun γ => Module.Dual ℂ (N.weight γ)) β g, ⟨g, rfl⟩⟩) hy0
    simp only [evW_apply, LinearMap.zero_apply] at h
    rw [dualPairing_lof, internalProjTo_coe] at h
    exact h
  rw [this]; exact Submodule.zero_mem _

theorem evW_surjective (β : ℂ) : Function.Surjective (evW N β) := by
  haveI := N.finrank β
  haveI : FiniteDimensional ℂ ((contra N).weight β) := (contra N).finrank β
  have hlof : Function.Injective (DirectSum.lof ℂ ℂ (fun γ => Module.Dual ℂ (N.weight γ)) β) :=
    DirectSum.of_injective (β := fun γ => Module.Dual ℂ (N.weight γ)) β
  have hrk : Module.finrank ℂ ((contra N).weight β) = Module.finrank ℂ (N.weight β) := by
    change Module.finrank ℂ (LinearMap.range
      (DirectSum.lof ℂ ℂ (fun γ => Module.Dual ℂ (N.weight γ)) β)) = _
    rw [LinearMap.finrank_range_of_inj hlof, Subspace.dual_finrank_eq]
  have hrk' : Module.finrank ℂ (N.weight β) =
      Module.finrank ℂ (Module.Dual ℂ ((contra N).weight β)) := by
    rw [Subspace.dual_finrank_eq, hrk]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk').mp (evW_injective N β)

/-- **`N ≅ N''`**: the canonical map is bijective. -/
theorem iota_bijective : Function.Bijective (iota N) := by
  refine ⟨iota_injective N, fun Φ => ?_⟩
  refine DirectSum.induction_on (β := fun γ => Module.Dual ℂ ((contra N).weight γ)) Φ ?_ ?_ ?_
  · exact ⟨0, LinearMap.map_zero _⟩
  · intro β ψ
    obtain ⟨y, rfl⟩ := evW_surjective N β ψ
    exact ⟨y, iota_of_mem N y.2⟩
  · rintro a b ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x + y, by rw [LinearMap.map_add, hx, hy]; rfl⟩

end DoubleDual

end VOA.C2Rigid
