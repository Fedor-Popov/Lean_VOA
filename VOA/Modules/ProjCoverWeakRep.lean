import VOA.Modules.ZhuVermaAnArchRhoFZ
import VOA.Modules.ZhuVermaAnArchDLM3Admissible
import VOA.Modules.Translation
import VOA.Modularity.ZhuRecursionProof

/-!
# Every weak module is a `V̂`-representation satisfying `ModuleIterate`

The DLM3 induced module `M̄_n(U)` (`VHat.DLM3.indBarWeakModule`) has its universal property stated
against `V̂`-representations `ρ'` satisfying `ModuleIterate` (`VHat.DLM3.indBarLift`).  To use it
against an arbitrary weak module `A : WeakModule W M` one needs `A` itself as such a
representation.  This file builds it:

* `weakActGen A` — the loop-generator family `a(m) ↦ a₍ₘ₎ᴬ`;
* `weakActGen_hderiv` — the derivative relation, from `act_T_covariance`;
* `weakActGen_hbracket` — the bracket relation, from the module commutator formula;
* `weakRep A : VHatRep W M`, with `weakRep_actMode : (weakRep A).actMode a m = a₍ₘ₎ᴬ`;
* `weakRep_moduleIterate : ModuleIterate (weakRep A)` (the module Jacobi identity at `m = 0`).

This mirrors `fzRho` (the adjoint representation), with the module modes in place of the VOA modes.
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators
open Finsupp

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {M : Type u} [AddCommGroup M] [Module ℂ M]

namespace VHat

/-- The loop-generator family of a weak module: at degree `m`, `a ↦ a₍ₘ₎ᴬ`. -/
noncomputable def weakActGen (A : WeakModule W M) : ℤ → (𝒱 →ₗ[ℂ] End ℂ M) :=
  fun m =>
    { toFun := fun a => mode (A.YM a) m
      map_add' := fun a a' => by rw [map_add, mode_add]
      map_smul' := fun c a => by rw [map_smul, mode_smul, RingHom.id_apply] }

@[simp] theorem weakActGen_apply (A : WeakModule W M) (m : ℤ) (a : 𝒱) :
    weakActGen A m a = mode (A.YM a) m := rfl

theorem weakActGen_hderiv (A : WeakModule W M) (a : 𝒱) (m : ℤ) :
    weakActGen A m (W.L (-1) a) + (m : ℂ) • weakActGen A (m - 1) a = 0 := by
  refine LinearMap.ext fun x => ?_
  have h := act_T_covariance A a m x
  simp only [WeakModule.act_def] at h
  simp only [LinearMap.add_apply, LinearMap.smul_apply, weakActGen_apply, LinearMap.zero_apply,
    h, neg_smul, neg_add_cancel]

/-- The module commutator formula with natural-number binomial coefficients, as endomorphisms. -/
theorem weak_mode_commutator_finsum (A : WeakModule W M) (a b : 𝒱) (m k : ℤ) :
    ⁅mode (A.YM a) m, mode (A.YM b) k⁆
      = ∑ᶠ i : ℕ, (gBinom m i) • mode (A.YM (W.smul a i b)) (m + k - i) := by
  obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a b
  set K : ℕ := Nz.toNat with hK
  have hzero : ∀ i : ℕ, K ≤ i → W.smul a i b = 0 := fun i hi =>
    hNz i (le_trans (Int.self_le_toNat Nz) (by exact_mod_cast hi))
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range K) (by
    intro i hi
    rw [Function.mem_support] at hi
    by_contra hc
    rw [Finset.coe_range, Set.mem_Iio, not_lt] at hc
    rw [hzero i hc, map_zero, mode_zero, smul_zero] at hi
    exact hi rfl)]
  refine LinearMap.ext fun x => ?_
  rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, mode_commutator A a b x m k, LinearMap.coe_sum, Finset.sum_apply]
  rw [finsum_eq_sum_of_support_subset (s := (Finset.range K).map Nat.castEmbedding)]
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Nat.castEmbedding_apply, LinearMap.smul_apply]
    rw [cbz_apply_nonneg m (Int.natCast_nonneg i), Int.toNat_natCast]
  · intro i hi
    rw [Function.mem_support] at hi
    have h0 : 0 ≤ i := by
      by_contra hneg
      exact hi (by rw [cbz_apply_neg _ (by omega), zero_smul])
    have h1 : i < K := by
      by_contra hge
      apply hi
      have : W.smul a i b = 0 := by
        have h2 := hzero i.toNat (by omega)
        rwa [Int.toNat_of_nonneg h0] at h2
      rw [this, map_zero, mode_zero, LinearMap.zero_apply, smul_zero]
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_range,
      Nat.castEmbedding_apply]
    exact ⟨i.toNat, by omega, by omega⟩

theorem weakActGen_hbracket (A : WeakModule W M) (a b : 𝒱) (m k : ℤ) :
    assembleAct (weakActGen A) (vloopBracket W (single m a) (single k b))
      = ⁅weakActGen A m a, weakActGen A k b⁆ := by
  rw [vloopBracket_single]
  have hfin : (Function.support fun i : ℕ =>
      (gBinom m i) • (single (m + k - i) (W.smul a i b) : VLoop 𝒱)).Finite := by
    obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a b
    refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
    intro i hi
    rw [Function.mem_support] at hi
    rw [Set.mem_Iio]
    by_contra hcon
    rw [not_lt] at hcon
    refine hi ?_
    rw [hNz i (le_trans (Int.self_le_toNat Nz) (by exact_mod_cast hcon)), Finsupp.single_zero,
      smul_zero]
  rw [map_finsum _ hfin]
  rw [weakActGen_apply, weakActGen_apply, weak_mode_commutator_finsum]
  refine finsum_congr fun i => ?_
  rw [map_smul, assembleAct_single, weakActGen_apply]

/-- **A weak module as a `V̂`-representation.** -/
noncomputable def weakRep (A : WeakModule W M) : VHatRep W M :=
  (assembleModeData (weakActGen A) (weakActGen_hderiv A) (weakActGen_hbracket A)).toRep

@[simp] theorem weakRep_actMode (A : WeakModule W M) (a : 𝒱) (m : ℤ) :
    (weakRep A).actMode a m = mode (A.YM a) m := by
  rw [weakRep, VHatModeData.toRep_actMode, assembleModeData_act_single, weakActGen_apply]

theorem weakRep_gen (A : WeakModule W M) (a : 𝒱) (m : ℤ) (x : M) :
    weakRep A (gen W a m) x = mode (A.YM a) m x := by
  rw [← VHatRep.actMode_def, weakRep_actMode]

/-- **`ModuleIterate` for a weak module**: the module Jacobi identity at `m = 0`. -/
theorem weakRep_moduleIterate (A : WeakModule W M) : VHatRep.ModuleIterate (weakRep A) := by
  intro u v x ℓ N
  have h := A.jacobi u v x ℓ 0 N
  have hR : (∑ᶠ i : ℤ, cbz 0 i • mode (A.YM (W.smul u (ℓ + i) v)) (0 + N - i) x)
      = mode (A.YM (W.smul u ℓ v)) N x := by
    rw [finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_smul])]
    simp
  rw [hR] at h
  simp only [weakRep_actMode]
  rw [← h]
  refine finsum_congr fun i => ?_
  simp only [add_zero, zero_add]

end VHat

end VOA
