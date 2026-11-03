/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeChargeM
import VOA.Examples.LatticeFields

/-!
# The general-charge half-current FIELDS `E⁻(cα,z)`, `E⁺(cα,z)`, `EE(cα,z)`  (Gannon §5.2.2; FLM Ch. 8)

The `FormalDist (End B)` packaging of the charge-`c` operator primitives `EminusOpC`/`aExpC`
(`Examples/LatticeChargeM`), mirroring the charge-`+1` `Eminus`/`Eplus`/`EE` of
`Examples/LatticeFields`.  These are the field-level boson dressing for the general-charge lattice
vertex operator `Y(e^{cα},z)`; specializing `c = 1` recovers the proved `Eminus`/`Eplus`/`EE`.

All `sorry`-free, axiom-clean, `pbw`-free.
-/

namespace VOA
namespace LatExp

open scoped BigOperators TensorProduct
open Module (End)
open HeisenbergN (FockN oscN vacuumN gradingWN gradingZN)
open LatticeVOA (LatModule LatGrp eVec latState latVacuum)

/-! ## The charge-`c` grading of `E⁺(cα)` -/

/-- The charge-`c` annihilation exponential `E⁺(cα)_{-N} = aExpC c N` lowers the boson weight by
exactly `N` (the `α` modes are unchanged by the charge scaling). -/
theorem aExpC_mem_gradingZN (c : ℂ) (N : ℕ) {w : ℕ} {p : B} (hp : p ∈ gradingWN 1 w) :
    aExpC c N p ∈ gradingZN 1 ((w : ℤ) - N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [aExpC_zero, LinearMap.id_apply, Nat.cast_zero, sub_zero]
           exact HeisenbergN.mem_gradingZN_of_gradingWN hp
    | (M+1) =>
      rw [aExpC_succ, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.sum_apply]
      refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m hm => ?_))
      simp only [Finset.mem_range] at hm
      rw [LinearMap.comp_apply, LinearMap.neg_apply]
      refine Submodule.neg_mem _ ?_
      have hrec : aExpC c (M - m) p ∈ gradingZN 1 ((w : ℤ) - (M - m : ℕ)) := ih (M - m) (by omega)
      have h := alpha_mem_gradingZN ((m : ℤ) + 1) hrec
      have hgoal : (w : ℤ) - (M - m : ℕ) - ((m : ℤ) + 1) = (w : ℤ) - ((M + 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub (by omega : m ≤ M)]; push_cast; ring
      rwa [hgoal] at h

/-! ## The charge-`c` half-current fields -/

/-- The charge-`c` **creation half** `E⁻(cα,z) = ∑_{N≥0} E⁻(cα)_N zᴺ` as a `FormalDist`. -/
noncomputable def EminusC (c : ℂ) : FormalDist (End ℂ B) :=
  fun t => if 0 ≤ t then EminusOpC c t.toNat else 0

@[simp] theorem EminusC_apply (c : ℂ) (t : ℤ) :
    EminusC c t = if 0 ≤ t then EminusOpC c t.toNat else 0 := rfl

theorem EminusC_neg (c : ℂ) {t : ℤ} (ht : t < 0) : EminusC c t = 0 := by
  rw [EminusC_apply, if_neg (by omega)]

theorem EminusC_isField (c : ℂ) : IsField (EminusC c) := by
  intro x
  exact ⟨0, fun n hn => by rw [EminusC_neg c hn, LinearMap.zero_apply]⟩

theorem EminusC_one_eq : EminusC 1 = Eminus := by
  funext t; rw [EminusC_apply, Eminus_apply]
  split_ifs with h
  · rw [EminusOpC_one_eq]
  · rfl

/-- The charge-`c` **annihilation half** `E⁺(cα,z) = ∑_{N≥0} E⁺(cα)_{-N} z⁻ᴺ` as a `FormalDist`. -/
noncomputable def EplusC (c : ℂ) : FormalDist (End ℂ B) :=
  fun t => if t ≤ 0 then aExpC c (-t).toNat else 0

@[simp] theorem EplusC_apply (c : ℂ) (t : ℤ) :
    EplusC c t = if t ≤ 0 then aExpC c (-t).toNat else 0 := rfl

theorem EplusC_nonpos (c : ℂ) {t : ℤ} (ht : t ≤ 0) : EplusC c t = aExpC c (-t).toNat := by
  rw [EplusC_apply, if_pos ht]

theorem EplusC_isField (c : ℂ) : IsField (EplusC c) := by
  classical
  intro x
  obtain ⟨cc, rfl⟩ := (HeisenbergN.gradingWN_isInternal 1).2 x
  obtain ⟨W, hW⟩ := Finset.exists_le cc.support
  refine ⟨-(W : ℤ), fun n hn => ?_⟩
  have hn0 : n ≤ 0 := by omega
  rw [EplusC_nonpos c hn0, DirectSum.coeAddMonoidHom_eq_dfinsuppSum, DFinsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun w hw => ?_
  have hwW : (w : ℤ) ≤ (W : ℤ) := by exact_mod_cast hW w hw
  have hmem := aExpC_mem_gradingZN c (-n).toNat (cc w).2
  rw [HeisenbergN.gradingZN_of_neg (by omega : (w : ℤ) - ((-n).toNat : ℤ) < 0),
    Submodule.mem_bot] at hmem
  exact hmem

theorem EplusC_one_eq : EplusC 1 = Eplus := by
  funext t; rw [EplusC_apply, Eplus_apply]
  split_ifs with h
  · rw [aExpC_one_eq]
  · rfl

/-- The charge-`c` boson dressing `EE(cα,z) = E⁻(cα,z)·E⁺(cα,z)` as a `FormalDist`. -/
noncomputable def EEC (c : ℂ) : FormalDist (End ℂ B) := nprod (EminusC_isField c) (EplusC_isField c)

theorem EEC_isField (c : ℂ) : IsField (EEC c) := IsField.nprod (EminusC_isField c) (EplusC_isField c)

/-! ## Vacuum actions -/

theorem EminusC_vacuum (c : ℂ) (t : ℤ) :
    EminusC c t (vacuumN 1) = if 0 ≤ t then cSchurC c t.toNat else 0 := by
  rw [EminusC_apply]; split_ifs with h
  · rw [EminusOpC_vacuum]
  · rfl

theorem EplusC_vacuum (c : ℂ) (t : ℤ) :
    EplusC c t (vacuumN 1) = if t = 0 then vacuumN 1 else 0 := by
  rw [EplusC_apply]
  by_cases h : t ≤ 0
  · rw [if_pos h, aExpC_vacuum]
    by_cases h0 : t = 0
    · rw [if_pos (by omega : (-t).toNat = 0), if_pos h0]
    · rw [if_neg (by omega : ¬ (-t).toNat = 0), if_neg h0]
  · rw [if_neg h, if_neg (by omega : ¬ t = 0), LinearMap.zero_apply]

/-- The vacuum action of the charge-`c` boson dressing: `EEC c (z)|0⟩ = E⁻(cα,z)|0⟩`, the `zᴺ`
coefficient creating the charge-`c` Schur state `cSchurC c N`. -/
theorem EEC_vacuum (c : ℂ) (t : ℤ) :
    EEC c t (vacuumN 1) = if 0 ≤ t then cSchurC c t.toNat else 0 := by
  classical
  have hsupp : ∀ m : ℤ, m ≠ t →
      normalOrdered (EminusC c) (EplusC c) m (t - m) (vacuumN 1) = 0 := by
    intro m hm
    rw [normalOrdered_apply]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0, Module.End.mul_apply, EplusC_vacuum, if_neg (by omega), map_zero]
    · rw [if_neg h0, Module.End.mul_apply, EminusC_neg c (by omega), LinearMap.zero_apply, map_zero]
  rw [EEC, nprod_apply, finsum_eq_single _ t hsupp, normalOrdered_apply]
  by_cases ht : 0 ≤ t
  · rw [if_pos ht, if_pos ht, Module.End.mul_apply, show t - t = (0 : ℤ) from by ring,
      EplusC_vacuum, if_pos rfl, EminusC_vacuum, if_pos ht]
  · rw [if_neg ht, if_neg ht, Module.End.mul_apply, EminusC_vacuum, if_neg ht, map_zero]

/-! ## The general-charge lattice vertex operator `Y(e^{mα},z)` -/

/-- The per-sector family building `Y(e^{mα},z)`: `p ⊗ e^{nα} ↦ (EEC m (t-2mn) p) ⊗ e^{(n+m)α}`
(the `z^{α₀}=z^{⟨mα,nα⟩}=z^{2mn}` sector shift, the charge-`m` boson dressing, the lattice shift
`n ↦ n+m` with trivial cocycle `ε(m,n)=1`). -/
noncomputable def YemαFam (m t : ℤ) (n : ℤ) : ℂ →ₗ[ℂ] (B →ₗ[ℂ] LatModule) :=
  LinearMap.toSpanSingleton ℂ (B →ₗ[ℂ] LatModule)
    (((TensorProduct.mk ℂ B LatGrp).flip (eVec (n + m))).comp (EEC (m : ℂ) (t - 2 * m * n)))

/-- The **general-charge lattice vertex operator** `Y(e^{mα},z)` as a `FormalDist (End LatModule)`,
extending the proved charge-`+1` `Yeα` to every integer charge `m`. -/
noncomputable def Yemα (m t : ℤ) : LatModule →ₗ[ℂ] LatModule :=
  TensorProduct.lift (Finsupp.lsum ℂ (YemαFam m t)).flip

/-- The defining action of `Y(e^{mα},z)` on a basis state `p ⊗ e^{nα}`. -/
theorem Yemα_tmul (m t n : ℤ) (p : B) :
    Yemα m t (p ⊗ₜ[ℂ] eVec n) = (EEC (m : ℂ) (t - 2 * m * n) p) ⊗ₜ[ℂ] eVec (n + m) := by
  rw [Yemα, TensorProduct.lift.tmul]
  change (Finsupp.lsum ℂ (YemαFam m t)) (eVec n) p = _
  rw [eVec, Finsupp.lsum_single, YemαFam, LinearMap.toSpanSingleton_apply, one_smul,
    LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply]

/-- The genuine creation series of `Y(e^{mα},z)`: `zᵗ`-coefficient `cSchurC m t ⊗ e^{mα}` for `t≥0`. -/
theorem Yemα_vacuum (m t : ℤ) :
    Yemα m t latVacuum = if 0 ≤ t then (cSchurC (m : ℂ) t.toNat) ⊗ₜ[ℂ] eVec m else 0 := by
  rw [show latVacuum = (1 : FockN 1) ⊗ₜ[ℂ] eVec 0 from rfl, Yemα_tmul,
    show (t - 2 * m * 0 : ℤ) = t from by ring]
  change (EEC (m : ℂ) t (vacuumN 1)) ⊗ₜ[ℂ] eVec (0 + m) = _
  rw [EEC_vacuum, show (0 : ℤ) + m = m from by ring]
  split_ifs with ht
  · rfl
  · rw [TensorProduct.zero_tmul]

/-- **Creation seed** `(e^{mα})₍₋₁₎Ω = e^{mα} = latState m` (`cSchurC m 0 = 1`). -/
theorem Yemα_creation_z0 (m : ℤ) : Yemα m 0 latVacuum = latState m := by
  rw [Yemα_vacuum, if_pos le_rfl, Int.toNat_zero, cSchurC_zero]
  rfl

theorem Yemα_mode_neg_one_vacuum (m : ℤ) : mode (Yemα m) (-1) latVacuum = latState m := by
  rw [mode_apply, show -(-1 : ℤ) - 1 = 0 from by ring, Yemα_creation_z0]

/-- The non-negative creation modes annihilate the vacuum: `(e^{mα})₍ₙ₎Ω = 0` for `n ≥ 0`. -/
theorem Yemα_creation_nonneg (m : ℤ) {n : ℤ} (hn : 0 ≤ n) : mode (Yemα m) n latVacuum = 0 := by
  rw [mode_apply, Yemα_vacuum, if_neg (by omega)]

end LatExp
end VOA
