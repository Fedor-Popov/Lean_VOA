/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenChargeFields
import VOA.Examples.LatticeGenModule
import VOA.Examples.LatticeFields

/-!
# The charge-`α` vertex operator `Y(e^α,z)` of the general lattice VOA  (FLM Ch. 8; Gannon §5.2.2)

The `FormalDist` boson dressing `EE(α,z) = E⁻(α,z)·E⁺(α,z)` and the vertex operator
`Y(e^α,z) = EE(α,z)·e^α·z^α` on `LatModuleGen L = FockN(rank L) ⊗ ℂ_ε{L}`, lifting the A₁
`EminusC`/`EplusC`/`EEC`/`Yemα` (`Examples/LatticeChargeMFields`) to a lattice **vector** charge
`α ∈ L`.  The one genuinely-new ingredient over A₁ is the **cocycle twist**: the lattice shift
`β ↦ α+β` carries the FLM 2-cocycle `ε(α,β) = latticeCocycle L α β` (A₁ has `ε ≡ 1`), the sign
that will make `Y(e^α), Y(e^β)` mutually local for **odd** `⟨α,β⟩`.

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN

variable (L : IntegralLattice)

/-! ## The charge-`α` half-current fields -/

/-- The charge-`α` **creation half** `E⁻(α,z) = ∑_{N≥0} E⁻(α)_N zᴺ` as a `FormalDist`. -/
noncomputable def EminusVecField (α : L.carrier) : FormalDist (End ℂ (FockN (rank L))) :=
  fun t => if 0 ≤ t then EminusVec L α t.toNat else 0

@[simp] theorem EminusVecField_apply (α : L.carrier) (t : ℤ) :
    EminusVecField L α t = if 0 ≤ t then EminusVec L α t.toNat else 0 := rfl

theorem EminusVecField_neg (α : L.carrier) {t : ℤ} (ht : t < 0) : EminusVecField L α t = 0 := by
  rw [EminusVecField_apply, if_neg (by omega)]

theorem EminusVecField_isField (α : L.carrier) : IsField (EminusVecField L α) := by
  intro x
  exact ⟨0, fun n hn => by rw [EminusVecField_neg L α hn, LinearMap.zero_apply]⟩

/-- The charge-`α` **annihilation half** `E⁺(α,z) = ∑_{N≥0} E⁺(α)_{-N} z⁻ᴺ` as a `FormalDist`. -/
noncomputable def EplusVecField (α : L.carrier) : FormalDist (End ℂ (FockN (rank L))) :=
  fun t => if t ≤ 0 then aExpVec L α (-t).toNat else 0

@[simp] theorem EplusVecField_apply (α : L.carrier) (t : ℤ) :
    EplusVecField L α t = if t ≤ 0 then aExpVec L α (-t).toNat else 0 := rfl

theorem EplusVecField_nonpos (α : L.carrier) {t : ℤ} (ht : t ≤ 0) :
    EplusVecField L α t = aExpVec L α (-t).toNat := by
  rw [EplusVecField_apply, if_pos ht]

theorem EplusVecField_isField (α : L.carrier) : IsField (EplusVecField L α) := by
  classical
  intro x
  obtain ⟨cc, rfl⟩ := (HeisenbergN.gradingWN_isInternal (rank L)).2 x
  obtain ⟨W, hW⟩ := Finset.exists_le cc.support
  refine ⟨-(W : ℤ), fun n hn => ?_⟩
  have hn0 : n ≤ 0 := by omega
  rw [EplusVecField_nonpos L α hn0, DirectSum.coeAddMonoidHom_eq_dfinsuppSum, DFinsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun w hw => ?_
  have hwW : (w : ℤ) ≤ (W : ℤ) := by exact_mod_cast hW w hw
  have hmem := aExpVec_mem_gradingZN L α (-n).toNat (cc w).2
  rw [HeisenbergN.gradingZN_of_neg (by omega : (w : ℤ) - ((-n).toNat : ℤ) < 0),
    Submodule.mem_bot] at hmem
  exact hmem

/-- The charge-`α` boson dressing `EE(α,z) = E⁻(α,z)·E⁺(α,z)` as a `FormalDist`. -/
noncomputable def EEVec (α : L.carrier) : FormalDist (End ℂ (FockN (rank L))) :=
  nprod (EminusVecField_isField L α) (EplusVecField_isField L α)

theorem EEVec_isField (α : L.carrier) : IsField (EEVec L α) :=
  IsField.nprod (EminusVecField_isField L α) (EplusVecField_isField L α)

/-! ## Vacuum actions -/

theorem EminusVecField_vacuum (α : L.carrier) (t : ℤ) :
    EminusVecField L α t (vacuumN (rank L)) = if 0 ≤ t then vSchur L α t.toNat else 0 := by
  rw [EminusVecField_apply]; split_ifs with h
  · rw [EminusVec_vacuum]
  · rfl

theorem EplusVecField_vacuum (α : L.carrier) (t : ℤ) :
    EplusVecField L α t (vacuumN (rank L)) = if t = 0 then vacuumN (rank L) else 0 := by
  rw [EplusVecField_apply]
  by_cases h : t ≤ 0
  · rw [if_pos h, aExpVec_vacuum]
    by_cases h0 : t = 0
    · rw [if_pos (by omega : (-t).toNat = 0), if_pos h0]
    · rw [if_neg (by omega : ¬ (-t).toNat = 0), if_neg h0]
  · rw [if_neg h, if_neg (by omega : ¬ t = 0), LinearMap.zero_apply]

/-- The vacuum action of the charge-`α` boson dressing: `EE(α,z)|0⟩ = E⁻(α,z)|0⟩`, the `zᴺ`
coefficient creating the vector Schur state `vSchur α N`. -/
theorem EEVec_vacuum (α : L.carrier) (t : ℤ) :
    EEVec L α t (vacuumN (rank L)) = if 0 ≤ t then vSchur L α t.toNat else 0 := by
  classical
  have hsupp : ∀ m : ℤ, m ≠ t →
      normalOrdered (EminusVecField L α) (EplusVecField L α) m (t - m) (vacuumN (rank L)) = 0 := by
    intro m hm
    rw [normalOrdered_apply]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0, Module.End.mul_apply, EplusVecField_vacuum L α, if_neg (by omega)]
      exact map_zero _
    · rw [if_neg h0, Module.End.mul_apply, EminusVecField_neg L α (by omega : m < 0)]
      simp
  rw [EEVec, nprod_apply, finsum_eq_single _ t hsupp, normalOrdered_apply]
  by_cases ht : 0 ≤ t
  · rw [if_pos ht, if_pos ht, Module.End.mul_apply, show t - t = (0 : ℤ) from by ring,
      EplusVecField_vacuum L α, if_pos rfl, EminusVecField_vacuum, if_pos ht]
  · rw [if_neg ht, if_neg ht, Module.End.mul_apply, EminusVecField_vacuum, if_neg ht]
    exact map_zero _

/-! ## The charge-`α` vertex operator `Y(e^α,z)` (with the cocycle twist) -/

/-- The per-sector family building `Y(e^α,z)`: on the charge-`β` sector, `p ⊗ e^β ↦
ε(α,β)·(EE(α, t-⟨α,β⟩) p) ⊗ e^{α+β}` — the `z^{α₀}=z^{⟨α,β⟩}` sector shift, the charge-`α` boson
dressing, the lattice shift `β ↦ α+β` with the **FLM cocycle** `ε(α,β) = latticeCocycle L α β`. -/
noncomputable def YeαvecFam (α : L.carrier) (t : ℤ) (β : L.carrier) :
    ℂ →ₗ[ℂ] (FockN (rank L) →ₗ[ℂ] LatModuleGen L) :=
  LinearMap.toSpanSingleton ℂ (FockN (rank L) →ₗ[ℂ] LatModuleGen L)
    (latticeCocycle L α β •
      (((TensorProduct.mk ℂ (FockN (rank L)) (L.carrier →₀ ℂ)).flip (eGen L (α + β))).comp
        (EEVec L α (t - L.form α β))))

/-- The **charge-`α` lattice vertex operator** `Y(e^α,z)` as a `FormalDist (End (V_L))`, the
vector-charge (and cocycle-twisted) generalization of A₁'s `Yemα`. -/
noncomputable def Yeαvec (α : L.carrier) (t : ℤ) : LatModuleGen L →ₗ[ℂ] LatModuleGen L :=
  TensorProduct.lift (Finsupp.lsum ℂ (YeαvecFam L α t)).flip

/-- The defining action of `Y(e^α,z)` on a basis state `p ⊗ e^β`: the cocycle-twisted, boson-dressed
sector shift. -/
theorem Yeαvec_tmul (α β : L.carrier) (t : ℤ) (p : FockN (rank L)) :
    Yeαvec L α t (latStateGen L p β)
      = latticeCocycle L α β • latStateGen L (EEVec L α (t - L.form α β) p) (α + β) := by
  rw [latStateGen, Yeαvec, TensorProduct.lift.tmul]
  change (Finsupp.lsum ℂ (YeαvecFam L α t)) (eGen L β) p = _
  rw [eGen, Finsupp.lsum_single, YeαvecFam, LinearMap.toSpanSingleton_apply, one_smul,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
    latStateGen, eGen]

/-- The genuine creation series of `Y(e^α,z)`: `zᵗ`-coefficient `ε(α,0)·(vSchur α t ⊗ e^α)` for
`t≥0`.  Since `ε(α,0)=1` and `⟨α,0⟩=0` this is the un-twisted charge-`α` creation state. -/
theorem Yeαvec_vacuum (α : L.carrier) (t : ℤ) :
    Yeαvec L α t (latVacuumGen L)
      = if 0 ≤ t then latStateGen L (vSchur L α t.toNat) α else 0 := by
  rw [latVacuumGen, Yeαvec_tmul, latticeCocycle_zero_right, one_smul,
    show L.form α 0 = 0 from by simp, sub_zero, add_zero]
  rw [latStateGen, EEVec_vacuum]
  split_ifs with ht
  · rfl
  · rw [TensorProduct.zero_tmul]

/-- **Creation seed** `(e^α)₍₋₁₎Ω = e^α = latChargeGen α` (`vSchur α 0 = 1`). -/
theorem Yeαvec_creation_z0 (α : L.carrier) : Yeαvec L α 0 (latVacuumGen L) = latChargeGen L α := by
  rw [Yeαvec_vacuum, if_pos le_rfl, Int.toNat_zero, vSchur_zero]
  rfl

/-- The non-negative creation modes annihilate the vacuum: `(e^α)₍ₙ₎Ω = 0` for `n ≥ 0`. -/
theorem Yeαvec_creation_nonneg (α : L.carrier) {n : ℤ} (hn : 0 ≤ n) :
    mode (Yeαvec L α) n (latVacuumGen L) = 0 := by
  rw [mode_apply, Yeαvec_vacuum, if_neg (by omega)]

theorem Yeαvec_mode_neg_one_vacuum (α : L.carrier) :
    mode (Yeαvec L α) (-1) (latVacuumGen L) = latChargeGen L α := by
  rw [mode_apply, show -(-1 : ℤ) - 1 = 0 from by ring, Yeαvec_creation_z0]

end VOA.LatGen
