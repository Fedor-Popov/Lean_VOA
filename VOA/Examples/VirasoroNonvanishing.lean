/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroFock
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The pbw-free nonvanishing of the Virasoro vacuum module

The abstract Virasoro vacuum module `VirUniv c = U(𝔙𝔦𝔯)/J(c)` has a **nonzero** vacuum vector, proved
**axiom-free** (no `VOA.pbw`): the linear-dilaton free-boson realization `Lₙ^λ` of central
charge `c = 1 − 12λ²` (`Examples/VirasoroFock`) is a genuine Virasoro representation on the
free-boson Fock space with a manifestly-nonzero highest-weight vacuum, so the universal map
`VirUniv c → Fock` sends `|0⟩ ↦ 1 ≠ 0`, forcing `|0⟩ ≠ 0` in `VirUniv c`.

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA

open Module (End)
open LieAlgebra LieAlgebra.Extension UniversalEnvelopingAlgebra

/-! ## §A  The linear-dilaton Lie representation `𝔙𝔦𝔯 → End Fock`. -/

/-- The Witt-level linear map `ℓₙ ↦ Lₙ^λ` (extended `ℂ`-linearly over `Witt = ℤ →₀ ℂ`). -/
noncomputable def rhoW (lam : ℂ) : Witt →ₗ[ℂ] End ℂ Fock :=
  Finsupp.lsum ℂ (fun n => LinearMap.toSpanSingleton ℂ (End ℂ Fock) (Lld lam n))

/-- A single Witt generator with coefficient a acts as a times the corresponding linear-dilaton Virasoro operator. This fixes the normalization of the linear extension. -/
@[simp] theorem rhoW_single (lam : ℂ) (n : ℤ) (a : ℂ) :
    rhoW lam (Finsupp.single n a) = a • Lld lam n := by
  simp only [rhoW, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

/-- **The projective Witt identity**: `rhoW⁅u,v⁆ + ψ(u,v)·(c·id) = ⁅rhoW u, rhoW v⁆` with the
Gel'fand–Fuks cocycle realized by `c = 1 − 12λ²` — the operator content of the central extension,
from the linear-dilaton Virasoro relation `Lld_virasoro`. -/
theorem rhoW_proj (lam : ℂ) (u v : Witt) :
    rhoW lam ⁅u, v⁆ + (Witt.cocycleₗ u v) • ((1 - 12 * lam ^ 2) • (LinearMap.id : End ℂ Fock))
      = ⁅rhoW lam u, rhoW lam v⁆ := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ =>
      simp only [Witt.bracket_def, map_add, LinearMap.add_apply, add_lie] at h₁ h₂ ⊢
      rw [← h₁, ← h₂]; module
  | single m a =>
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add v₁ v₂ h₁ h₂ =>
          simp only [Witt.bracket_def, map_add, lie_add] at h₁ h₂ ⊢
          rw [← h₁, ← h₂]; module
      | single n b =>
          have hcomm : ⁅rhoW lam (Finsupp.single m a), rhoW lam (Finsupp.single n b)⁆
              = (a * b) • (Lld lam m * Lld lam n - Lld lam n * Lld lam m) := by
            rw [rhoW_single, rhoW_single, LieRing.of_associative_ring_bracket,
              smul_mul_assoc, mul_smul_comm, smul_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
            module
          rw [Witt.bracket_def, Witt.bracketₗ_single, rhoW_single, Witt.cocycleₗ_single, hcomm,
            Lld_virasoro, Witt.gfCoeff]
          by_cases hmn : m + n = 0
          · rw [if_pos hmn, if_pos hmn]
            simp only [smul_add, smul_smul]
            module
          · rw [if_neg hmn, if_neg hmn]
            simp only [smul_smul, zero_smul, add_zero]
            module

/-- The linear map `𝔙𝔦𝔯 → End Fock` underlying the linear-dilaton representation:
`Lₙ ↦ Lₙ^λ`, `C ↦ (1−12λ²)·id`. -/
noncomputable def rhoLin (lam : ℂ) : Virasoro →ₗ[ℂ] End ℂ Fock where
  toFun x := rhoW lam ((ofProd gfCocycle).symm x).1
    + ((ofProd gfCocycle).symm x).2 • ((1 - 12 * lam ^ 2) • (LinearMap.id : End ℂ Fock))
  map_add' x y := by
    simp only [of_symm_add, Prod.fst_add, Prod.snd_add, map_add, add_smul]
    abel
  map_smul' r x := by
    simp only [of_symm_smul, Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply]
    module

/-- **The linear-dilaton Virasoro representation** `𝔙𝔦𝔯 →ₗ⁅ℂ⁆ End Fock`, central charge
`c = 1 − 12λ²`: `Lₙ ↦ Lₙ^λ`, `C ↦ (1−12λ²)·id`. -/
noncomputable def linDilRho (lam : ℂ) : Virasoro →ₗ⁅ℂ⁆ End ℂ Fock :=
  { rhoLin lam with
    map_lie' := by
      intro x y
      show rhoLin lam ⁅x, y⁆ = ⁅rhoLin lam x, rhoLin lam y⁆
      set u := ((ofProd gfCocycle).symm x).1 with hu
      set v := ((ofProd gfCocycle).symm y).1 with hv
      have he : ∀ z : Virasoro, rhoLin lam z = rhoW lam ((ofProd gfCocycle).symm z).1
          + ((ofProd gfCocycle).symm z).2 • ((1 - 12 * lam ^ 2) • (LinearMap.id : End ℂ Fock)) :=
        fun z => rfl
      -- LHS: `rhoLin ⁅x,y⁆ = ⁅rhoW u, rhoW v⁆` via the projective identity + `bracket_ofTwoCocycle`
      have h1 : ((ofProd gfCocycle).symm ⁅x, y⁆).1 = ⁅u, v⁆ := by
        rw [bracket_ofTwoCocycle, Equiv.symm_apply_apply]
      have h2 : ((ofProd gfCocycle).symm ⁅x, y⁆).2 = Witt.cocycleₗ u v := by
        rw [bracket_ofTwoCocycle, Equiv.symm_apply_apply]
        simp only [trivial_lie_zero, add_zero, sub_zero]
        rfl
      have hL : rhoLin lam ⁅x, y⁆ = ⁅rhoW lam u, rhoW lam v⁆ := by
        rw [← rhoW_proj lam u v, he ⁅x, y⁆, h1, h2]
      -- RHS: the two central `id`-summands drop out of the bracket
      have hR : ⁅rhoLin lam x, rhoLin lam y⁆ = ⁅rhoW lam u, rhoW lam v⁆ := by
        show rhoLin lam x * rhoLin lam y - rhoLin lam y * rhoLin lam x
            = rhoW lam u * rhoW lam v - rhoW lam v * rhoW lam u
        rw [he x, he y, ← hu, ← hv]
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
          show (LinearMap.id : End ℂ Fock) = 1 from rfl, mul_one, one_mul]
        module
      rw [hL, hR] }

/-- The constructed Lie representation sends each abstract Virasoro generator L_n to the intended Fock-space differential operator, rather than merely an isomorphic unnamed action. -/
@[simp] theorem linDilRho_L (lam : ℂ) (n : ℤ) : linDilRho lam (L n) = Lld lam n := by
  show rhoLin lam (L n) = Lld lam n
  rw [rhoLin, L]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Equiv.symm_apply_apply, rhoW_single, one_smul,
    Witt.gen]
  rw [show ((0 : ℂ) : ℂ) • ((1 - 12 * lam ^ 2) • (LinearMap.id : End ℂ Fock)) = 0 from by
      rw [zero_smul], add_zero]

/-- The abstract central generator acts on Fock space by the scalar 1 minus twelve times the square of the background parameter. Choosing that parameter realizes any desired complex central charge. -/
@[simp] theorem linDilRho_C (lam : ℂ) :
    linDilRho lam C = (1 - 12 * lam ^ 2) • (LinearMap.id : End ℂ Fock) := by
  show rhoLin lam C = _
  rw [rhoLin, C]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Equiv.symm_apply_apply, map_zero, zero_add, one_smul]

/-! ## §B  The `U(𝔙𝔦𝔯)`-module structure and the pbw-free nonvanishing. -/

open VirModule

/-- The `U(𝔙𝔦𝔯)`-algebra homomorphism `U(𝔙𝔦𝔯) → End Fock` of the linear-dilaton representation. -/
noncomputable def evAlg (lam : ℂ) : UVir →ₐ[ℂ] End ℂ Fock := lift ℂ (linDilRho lam)

/-- Every choice of central charge `c ∈ ℂ` is realised: `1 − 12λ² = c` for a suitable background
charge `λ` (ℂ is algebraically closed, so `(1−c)/12` has a square root). -/
theorem exists_lam (c : ℂ) : ∃ lam : ℂ, 1 - 12 * lam ^ 2 = c := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((1 - c) / 12) (n := 2) (by norm_num : 0 < 2)
  exact ⟨z, by rw [hz]; ring⟩

/-- **The Virasoro vacuum module is nontrivial** — `|0⟩ ≠ 0` in `VirUniv c`, proved **pbw-free**: the
linear-dilaton Fock realization (central charge `c = 1−12λ²`) gives a `U(𝔙𝔦𝔯)`-module map
`VirUniv c → Fock` under which `|0⟩ ↦ 1 ≠ 0`. -/
theorem vacVec_ne_zero (c : ℂ) : VirModule.vacVec c ≠ 0 := by
  obtain ⟨lam, hlam⟩ := exists_lam c
  -- the generators of `J(c)` are killed at the vacuum
  have hgen : ∀ g ∈ vacGens c, evAlg lam g vacuum = 0 := by
    intro g hg
    rcases hg with ⟨n, hn, rfl⟩ | rfl
    · rw [evAlg, lift_ι_apply, linDilRho_L]; exact Lld_vacuum lam hn
    · rw [evAlg, map_sub, lift_ι_apply, linDilRho_C, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
        hlam, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply,
        Module.End.one_apply, sub_self]
  -- hence the whole ideal is killed at the vacuum
  have hideal : ∀ w ∈ vacIdeal c, evAlg lam w vacuum = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem g hg => exact hgen g hg
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
    | smul r a _ ha =>
        rw [show (r • a : UVir) = r * a from rfl, map_mul, Module.End.mul_apply, ha, map_zero]
  -- if `|0⟩ = 0`, the map sends `1 ↦ vacuum = 0`, contradicting `vacuum ≠ 0`
  intro hzero
  rw [vacVec, Submodule.Quotient.mk_eq_zero] at hzero
  have hv := hideal 1 hzero
  rw [map_one, Module.End.one_apply] at hv
  exact vacuum_ne_zero hv

/-- The linear-dilaton Fock realization as a `VirRep` of central charge `c`. -/
noncomputable def linDilVirRep (c : ℂ) : VirRep Fock where
  ρ := linDilRho (exists_lam c).choose
  centralCharge := c
  acts_central := by rw [linDilRho_C, (exists_lam c).choose_spec]

/-- The Virasoro vacuum module is nontrivial (`pbw`-free). -/
theorem vacuumSpace_nontrivial (c : ℂ) : Nontrivial (VirModule.VirUniv c) :=
  ⟨⟨VirModule.vacVec c, 0, vacVec_ne_zero c⟩⟩

end VOA
