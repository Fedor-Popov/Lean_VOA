/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.M8h0Gap
import VOA.Moonshine.TrialityTwSigma

/-!
# M8h key step, part 1: one twisted vector generates `TP` over `V_Λ⁺`

`M8h0.TPBlockLocal_all_of_gen` reduces DGM (4.23) for all pairs to (4.23) on a family `g` whose
`V_Λ⁺`-mode span is `TP` (`M8h0.ModeSpan g`).  Here we show that a **single** vector suffices:

  `modeSpan_x0T : t₀ ≠ 0 → ModeSpan (fun _ : Unit => x0T t₀)`,

i.e. `TP = span{u₍ₙ₎ (h₀(−½)𝟙 ⊗ t₀) | u ∈ V_Λ⁺, n ∈ ℤ}` for every nonzero `t₀ ∈ T`.  This is the
frame-mixing statement "`T₃⁺ ⊆ V₃⁺ · T₀⁺`" that the triality route needs: the
conjugation argument of `M8hKey.lean` produces (4.23) only on `T_s⁺ × T_s⁺` for the image sector
`T_s⁺ = σ(V₃⁺)`, and this file transports it to the whole of `TP`.

## Proof
The proof of `span_smul_frameX0T` (`CyclicTwisted.lean`) with the subalgebra `A = frameFix`
replaced by all of `V_Λ` (`A = ⊤`):
1. `Z(x₀) = span{Y^T(u)₍k/2₎ x₀ | u ∈ V_Λ}` is `V_Λ`-stable (`YM_mem_orbitSpan`);
2. `h₀(½) x₀ = ½ (1 ⊗ t₀)`, so `1 ⊗ t₀ ∈ Z`; then `1 ⊗ e_α t₀ ∈ Z` for **every** `α ∈ Λ`
   (`leechTwistedModule_echg_vac`), and the `e_α t₀` span `T` (`T` is a simple module over the
   twisted group algebra, `span_eA`), so `1 ⊗ T ⊆ Z`; the Heisenberg modes give `S[θ] ⊗ T ⊆ Z`;
3. the `+`-projection (`mem_span_plus_of_mem_orbitSpan`) leaves the `V_Λ⁺`-modes on `x₀`.

## Status
`sorry`-free and unconditional (no σ input).  Reached from the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.M8hKey

open LatticeTwisted TwistedHeisenberg IntegralLattice LatGen Extraspecial FrameT TwistedCyclic
  MvPolynomial
open Module (End)
open scoped TensorProduct
open TrialityTw M8h0

/-- The orbit span over **all** of `V_Λ`. -/
noncomputable abbrev fullZA (x : Tw) : Submodule ℂ Tw :=
  orbitSpan leechTwistedModule (⊤ : Submodule ℂ (LatModuleGen leech)) x

theorem YM_mem_fullZA (u : LatModuleGen leech) (k : ℤ) {x y : Tw} (hy : y ∈ fullZA x) :
    leechTwistedModule.YM u k y ∈ fullZA x :=
  YM_mem_orbitSpan leechTwistedModule ⊤ (fun _ _ _ _ _ => Submodule.mem_top)
    (fun _ _ => Submodule.mem_top) leechTheta_leechTheta Submodule.mem_top k hy

/-- If `1 ⊗ t ∈ Z(x)` then `y ⊗ t ∈ Z(x)` for every `y ∈ S[θ]`. -/
theorem tmul_mem_fullZA {t : TLeechT} {x : Tw} (h : vacT 24 ⊗ₜ t ∈ fullZA x) (y : FockT 24) :
    y ⊗ₜ t ∈ fullZA x := by
  have hw : ∀ l : List (ℕ × Fin 24), creationWordT 24 l (vacT 24) ⊗ₜ t ∈ fullZA x := by
    intro l
    induction l with
    | nil => simpa [creationWordT] using h
    | cons v l ih =>
        obtain ⟨u, -, hk⟩ := leechTwistedModule_hgen v.2
        have h1 := YM_mem_fullZA u (-(2 * (v.1 : ℤ) + 1)) ih
        rw [hk, LinearMap.rTensor_tmul] at h1
        simpa only [creationWordT, List.map_cons, List.prod_cons, Module.End.mul_apply] using h1
  have hy : y ∈ Submodule.span ℂ (Set.range fun l => creationWordT 24 l (vacT 24)) := by
    rw [span_creationWordT_vacT]; exact Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem z hz => obtain ⟨l, rfl⟩ := hz; exact hw l
  | zero => rw [TensorProduct.zero_tmul]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [TensorProduct.add_tmul]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [← TensorProduct.smul_tmul']; exact Submodule.smul_mem _ _ ha

/-- `T = span{e_α t₀ | α ∈ Λ}` for any `t₀ ≠ 0` (simplicity of `T`). -/
theorem mem_span_eT {t₀ : TLeechT} (h0 : t₀ ≠ 0) (t : TLeechT) :
    t ∈ Submodule.span ℂ (Set.range fun α => eT leech leech_even leech_isUnit_det_gramMat α t₀) := by
  obtain ⟨a, ha⟩ := IsSimpleModule.toSpanSingleton_surjective (alg (cocMat leech)) h0 t
  rw [LinearMap.toSpanSingleton_apply] at ha
  let f : alg (cocMat leech) →ₗ[ℂ] TLeechT :=
    { toFun := fun a => a • t₀
      map_add' := fun a b => add_smul a b t₀
      map_smul' := fun c a => smul_assoc c a t₀ }
  have h1 : a ∈ Submodule.span ℂ (Set.range (eA leech)) := by
    rw [span_eA]; exact Submodule.mem_top
  have h2 := Submodule.mem_map_of_mem (f := f) h1
  rw [Submodule.map_span, ← Set.range_comp] at h2
  rw [← ha]
  exact h2

/-- **`Z(x₀)` is everything** for `x₀ = h₀(−½)𝟙 ⊗ t₀`, `t₀ ≠ 0`. -/
theorem fullZA_eq_top {t₀ : TLeechT} (h0 : t₀ ≠ 0) : fullZA (frameX0T t₀) = ⊤ := by
  set Z := fullZA (frameX0T t₀)
  have hvac : vacT 24 ⊗ₜ t₀ ∈ Z := by
    obtain ⟨u, -, hk⟩ := leechTwistedModule_hgen 0
    have h1 := YM_mem_orbitSpan_of_mem (T := leechTwistedModule)
      (A := (⊤ : Submodule ℂ (LatModuleGen leech))) (Submodule.mem_top (x := u)) 1 (frameX0T t₀)
    rw [hk, frameX0T, LinearMap.rTensor_tmul] at h1
    have hm := modeT_annihilation 24 0 0 (X (0, 0))
    rw [show (2 * ((0 : ℕ) : ℤ) + 1) = 1 by norm_num, pderiv_X_self] at hm
    rw [hm] at h1
    have h2 := Submodule.smul_mem Z (2 : ℂ) h1
    rw [← TensorProduct.smul_tmul', smul_smul] at h2
    convert h2 using 2
    norm_num [vacT]
  have hα : ∀ α : leech.carrier,
      vacT 24 ⊗ₜ eT leech leech_even leech_isUnit_det_gramMat α t₀ ∈ Z := by
    intro α
    have h1 := YM_mem_fullZA (echg leech α) (leech.form α α - 2) hvac
    rw [leechTwistedModule_echg_vac] at h1
    have h2 := Submodule.smul_mem Z (((2 : ℂ) ^ (-(leech.form α α)))⁻¹) h1
    rwa [smul_smul, inv_mul_cancel₀ (zpow_ne_zero _ two_ne_zero), one_smul] at h2
  have ht : ∀ t : TLeechT, vacT 24 ⊗ₜ t ∈ Z := by
    intro t
    have hsp := mem_span_eT h0 t
    induction hsp using Submodule.span_induction with
    | mem z hz => obtain ⟨α, rfl⟩ := hz; exact hα α
    | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [TensorProduct.tmul_smul]; exact Submodule.smul_mem _ _ ha
  rw [eq_top_iff]
  intro x hx
  clear hx
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul y t => exact tmul_mem_fullZA (ht t) y
  | add a b ha hb => exact Submodule.add_mem _ ha hb

/-- **`TP` is generated by one vector over `V_Λ⁺`**: for every `t₀ ≠ 0`,
`TP = span{u₍ₙ₎ x0T t₀ | u ∈ V_Λ⁺, n ∈ ℤ}`. -/
theorem modeSpan_x0T {t₀ : TLeechT} (h0 : t₀ ≠ 0) : ModeSpan (fun _ : Unit => x0T t₀) := by
  rw [ModeSpan, eq_top_iff]
  intro y _
  have hZ : (y : Tw) ∈ fullZA ((x0T t₀ : TP) : Tw) := by
    change (y : Tw) ∈ fullZA (frameX0T t₀)
    rw [fullZA_eq_top h0]; exact Submodule.mem_top
  have h := mem_span_plus_of_mem_orbitSpan leechTwistedModule (⊤ : Submodule ℂ (LatModuleGen leech))
    (fun _ _ => Submodule.mem_top) leechTheta_leechTheta leechThetaLift (x0T t₀) y hZ
  refine Submodule.span_mono ?_ h
  rintro z ⟨u, -, n, rfl⟩
  exact ⟨u, n, (), rfl⟩

end VOA.Moonshine.M8hKey
