/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.HeisenbergTwistedModuleVertex

/-!
# The twisted `L₀`: `Y^T(ω, z)₍₁₎ = L0T`, with the `r/16` from the `Δ_z` corrections

For the candidate twisted vertex operator `YT r` (`HeisenbergTwistedModuleVertex`), the mode
`L₀ = ω₍₁₎`, i.e. fractional index `k = N = 2`, of the conformal vector
`ω = ½ Σ_a h_a(−1)²𝟙` is exactly the twisted Virasoro zero mode of `Moonshine/TwistedHeisenberg`:

  `YT r ω 2 = L0T r = Σ_a Σ_{n ≥ 0} h_a(−n−½) h_a(n+½) + r/16`   (`YT_omega_two`).

The constant `r/16` is not put in by hand: in `Ywt [(0,a),(0,a)]` the inverse twisted product
formula contributes `C(−½,1)·(Fgen_a ₍₀₎ Fgen_a) z^{−1} + C(−½,2)·(Fgen_a ₍₁₎ Fgen_a) z^{−2}`
`= (−½)(½) z^{−1} + (⅜) z^{−1} = ⅛ z^{−1}` per boson (`mode_Ywt_pair_zero`), i.e. the FLM `Δ_z`
correction `c₁₁ = 1/16` times `h(1)² ω`-contraction.  Consequently `YT ω 2` acts on the weight
space `weightT r q` by `q` (`YT_omega_two_weightT`): this is the `L0_weight` field of a twisted
module for the `ℚ`-grading `weightT` of `S[θ]`.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA

namespace Moonshine

open MvPolynomial TwistedHeisenberg HeisenbergN TwistedReduction
open Module (End)

variable (r : ℕ)

/-! ## Bookkeeping -/

theorem fld_sum_val {ι : Type*} (s : Finset ι) (f : ι → Fld (FockT r)) :
    (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 := by
  classical
  induction s using Finset.induction with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Fld.add_val, ih]

theorem mode_finset_sum {ι : Type*} (s : Finset ι) (f : ι → FormalDist (End ℂ (FockT r)))
    (p : ℤ) : mode (∑ i ∈ s, f i) p = ∑ i ∈ s, mode (f i) p := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, mode_add, ih]

/-- The twisted number-operator term `h_a(−n−½) h_a(n+½)` attached to the variable `v = (n,a)`. -/
noncomputable def numT (v : ℕ × Fin r) : End ℂ (FockT r) :=
  modeT r v.2 (-(2 * v.1 + 1)) * modeT r v.2 (2 * v.1 + 1)

theorem numT_of_notMem {v : ℕ × Fin r} {x : FockT r} (hv : v ∉ x.vars) : numT r v x = 0 := by
  rw [numT, Module.End.mul_apply]
  have h := modeT_annihilation r v.2 v.1 x
  rw [show ((2 * (v.1 : ℤ) + 1)) = 2 * v.1 + 1 from rfl] at h
  rw [show (2 * ((v.1 : ℕ) : ℤ) + 1) = 2 * (v.1 : ℤ) + 1 from rfl, h,
    pderiv_eq_zero_of_notMem_vars hv, smul_zero, map_zero]

/-! ## The normal-ordered square `:Fgen_a Fgen_a:` -/

/-- The diagonal term of `:Fgen_a(z) Fgen_a(z):` at total index `−1` (mode `0`). -/
theorem normalOrdered_Fgen_diag (a : Fin r) (m : ℤ) (x : FockT r) :
    normalOrdered (Fgen r a) (Fgen r a) m (-1 - m) x
      = if 0 ≤ m then numT r (m.toNat, a) x else numT r ((-m - 1).toNat, a) x := by
  rw [normalOrdered_apply]
  split_ifs with h
  · rw [Module.End.mul_apply, Fgen_apply, Fgen_apply, numT, Module.End.mul_apply,
      show -2 * m - 1 = -(2 * ((m.toNat : ℕ) : ℤ) + 1) by omega,
      show -2 * (-1 - m) - 1 = 2 * ((m.toNat : ℕ) : ℤ) + 1 by omega]
  · rw [Module.End.mul_apply, Fgen_apply, Fgen_apply, numT, Module.End.mul_apply,
      show -2 * (-1 - m) - 1 = -(2 * (((-m - 1).toNat : ℕ) : ℤ) + 1) by omega,
      show -2 * m - 1 = 2 * (((-m - 1).toNat : ℕ) : ℤ) + 1 by omega]

/-- **Mode `0` of the normal-ordered square**: `:Fgen_a Fgen_a:₍₀₎ = 2 Σ_{n≥0} h_a(−n−½)h_a(n+½)`,
written as a finite sum over the variables of the vector. -/
theorem mode_nprod_Fgen_zero (a : Fin r) (x : FockT r) :
    mode (nprod (FgenFld r a).2 (FgenFld r a).2) 0 x
      = ∑ v ∈ x.vars, if v.2 = a then (2 : ℂ) • numT r v x else 0 := by
  classical
  rw [mode_apply, show -(0 : ℤ) - 1 = -1 by norm_num, nprod_apply]
  set S := x.vars.filter (fun v => v.2 = a) with hS
  set g : ℤ → FockT r := fun m => normalOrdered (Fgen r a) (Fgen r a) m (-1 - m) x with hg
  have hgv : ∀ m, g m = if 0 ≤ m then numT r (m.toNat, a) x else numT r ((-m - 1).toNat, a) x :=
    fun m => normalOrdered_Fgen_diag r a m x
  set sp : Finset ℤ := S.image (fun v => (v.1 : ℤ)) with hsp
  set sn : Finset ℤ := S.image (fun v => -(v.1 : ℤ) - 1) with hsn
  have hsupp : Function.support g ⊆ ↑(sp ∪ sn) := by
    intro m hm
    rw [Function.mem_support, hgv] at hm
    rw [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_coe]
    split_ifs at hm with h
    · left
      have hv : (m.toNat, a) ∈ x.vars := by
        by_contra hc; exact hm (numT_of_notMem r hc)
      exact Finset.mem_image.mpr ⟨(m.toNat, a), Finset.mem_filter.mpr ⟨hv, rfl⟩,
        show ((m.toNat : ℕ) : ℤ) = m by omega⟩
    · right
      have hv : ((-m - 1).toNat, a) ∈ x.vars := by
        by_contra hc; exact hm (numT_of_notMem r hc)
      exact Finset.mem_image.mpr ⟨((-m - 1).toNat, a), Finset.mem_filter.mpr ⟨hv, rfl⟩,
        show -(((-m - 1).toNat : ℕ) : ℤ) - 1 = m by omega⟩
  change ∑ᶠ m : ℤ, g m = _
  rw [finsum_eq_sum_of_support_subset g hsupp]
  have hdisj : Disjoint sp sn := by
    rw [Finset.disjoint_left]
    intro m hm hm'
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hm'
    omega
  have hinj : ∀ v ∈ S, ∀ w ∈ S, v.1 = w.1 → v = w := by
    intro v hv w hw h
    have hva := (Finset.mem_filter.mp hv).2
    have hwa := (Finset.mem_filter.mp hw).2
    exact Prod.ext h (hva.trans hwa.symm)
  rw [Finset.sum_union hdisj, Finset.sum_image (fun v hv w hw h => hinj v hv w hw (by
      simpa using h)), Finset.sum_image (fun v hv w hw h => hinj v hv w hw (by
      have h' : -(v.1 : ℤ) - 1 = -(w.1 : ℤ) - 1 := h
      omega)), ← Finset.sum_add_distrib, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs with hva
  · rw [hgv, hgv, if_pos (by positivity), if_neg (by omega), two_smul]
    have h1 : ((v.1 : ℤ).toNat, a) = v := by rw [Int.toNat_natCast, ← hva]
    have h2 : ((-(-(v.1 : ℤ) - 1) - 1).toNat, a) = v := by
      rw [show -(-(v.1 : ℤ) - 1) - 1 = v.1 by ring, Int.toNat_natCast, ← hva]
    rw [h1, h2]
  · rfl

/-! ## The twisted word field of `h_a(−1)²𝟙` -/

/-- **Mode `0` of the twisted field of `h_a(−1)²𝟙`**: the normal-ordered square plus the `Δ_z`
constant `⅛`. -/
theorem mode_Ywt_pair_zero (a : Fin r) :
    mode (Ywt r [((0 : ℕ), a), ((0 : ℕ), a)]).1 0
      = mode (nprod (FgenFld r a).2 (FgenFld r a).2) 0 + (1 / 8 : ℂ) • (1 : End ℂ (FockT r)) := by
  rw [Ywt_cons, Ywt_single]
  have hb : ((0 : ℕ), a).1 + 3 + 2 * wordWeightNN [((0 : ℕ), a)] = 5 := by
    simp [wordWeightNN]
  rw [hb, fld_sum_val, mode_finset_sum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Fld.smul_val, fzmul_val,
    mode_smul, mode_zmul]
  -- the five products `Fgen ₍₋₁₊ᵢ₎ Fgen`
  have e0 : (Fld.prod (-(((0 : ℕ), a).1 : ℤ) - 1 + ((0 : ℕ) : ℤ)) (FgenFld r a) (FgenFld r a)).1
      = nprod (FgenFld r a).2 (FgenFld r a).2 := by
    rw [show -(((0 : ℕ), a).1 : ℤ) - 1 + ((0 : ℕ) : ℤ) = -1 by simp, Fld.prod_of_neg (by norm_num),
      show (-(-1 : ℤ) - 1).toNat = 0 by norm_num, negProd_zero]
    rfl
  have e1 : (Fld.prod (-(((0 : ℕ), a).1 : ℤ) - 1 + ((1 : ℕ) : ℤ)) (FgenFld r a) (FgenFld r a)).1
      = opeZero r a a := by
    rw [show -(((0 : ℕ), a).1 : ℤ) - 1 + ((1 : ℕ) : ℤ) = 0 by simp, prod_Fgen_zero]
  have e2 : (Fld.prod (-(((0 : ℕ), a).1 : ℤ) - 1 + ((2 : ℕ) : ℤ)) (FgenFld r a) (FgenFld r a)).1
      = opeOne r a a := by
    rw [show -(((0 : ℕ), a).1 : ℤ) - 1 + ((2 : ℕ) : ℤ) = 1 by simp, prod_Fgen_one]
  have e3 : (Fld.prod (-(((0 : ℕ), a).1 : ℤ) - 1 + ((3 : ℕ) : ℤ)) (FgenFld r a) (FgenFld r a)).1
      = 0 := prod_Fgen_of_two_le r a a (by simp)
  have e4 : (Fld.prod (-(((0 : ℕ), a).1 : ℤ) - 1 + ((4 : ℕ) : ℤ)) (FgenFld r a) (FgenFld r a)).1
      = 0 := prod_Fgen_of_two_le r a a (by simp)
  rw [e0, e1, e2, e3, e4]
  have hz : mode (opeZero r a a) (-((1 : ℕ) : ℤ)) = (1 / 2 : ℂ) • (1 : End ℂ (FockT r)) := by
    rw [mode_apply, opeZero]
    norm_num
    rfl
  have ho : mode (opeOne r a a) (-((2 : ℕ) : ℤ)) = (1 : End ℂ (FockT r)) := by
    rw [mode_apply, opeOne]
    norm_num
    rfl
  have c1 : cbinom (-1 / 2) 1 = -1 / 2 := by norm_num [cbinom]
  have c2 : cbinom (-1 / 2) 2 = 3 / 8 := by norm_num [cbinom, Finset.prod_range_succ]
  rw [hz, ho, c1, c2]
  simp only [mode_zero, smul_zero, add_zero, cbinom_zero, one_smul, Nat.cast_zero, neg_zero]
  rw [smul_smul, add_assoc, ← add_smul]
  norm_num

/-! ## `L₀` -/

/-- The conformal vector of `heisVOA1 r` as a combination of the monomials `h_a(−1)²𝟙`. -/
theorem ωN_one_eq (a : Fin r) :
    ωNa r 1 a = (1 / 2 : ℂ) • monomial (Finsupp.single ((0 : ℕ), a) 2) (1 : ℂ) := by
  rw [ωNa, oscN_neg_one_sq_vacuumN, X_zero_sq_eq_monomialN]
  norm_num

/-- `YT (h_a(−1)²𝟙) 2` is mode `0` of the word field `Ywt [(0,a),(0,a)]`. -/
theorem YT_sq_two (a : Fin r) :
    YT r (monomial (Finsupp.single ((0 : ℕ), a) 2) 1) 2
      = mode (Ywt r [((0 : ℕ), a), ((0 : ℕ), a)]).1 0 := by
  rw [YT_monomial, one_smul, YTmon, monoWordN_single_two]
  simp

/-- **`L₀ = ω₍₁₎` of the twisted vertex operator is the twisted Virasoro zero mode**
`L0T r = Σ_{a,n} h_a(−n−½) h_a(n+½) + r/16`; the `r/16` is produced by the `Δ_z` corrections of
the inverse twisted product formula. -/
theorem YT_omega_two : YT r (heisVOA1 r).conformalVector 2 = L0T r := by
  refine LinearMap.ext fun x => ?_
  have hL : L0T r x = ∑ v ∈ x.vars, numT r v x + ((r : ℂ) / 16) • x := L0T_eq_modeSum r x
  rw [hL]
  change YT r (ωN r 1) 2 x = _
  have h1 : YT r (ωN r 1) 2 x = ∑ a : Fin r, (1 / 2 : ℂ) •
      (mode (nprod (FgenFld r a).2 (FgenFld r a).2) 0 x + (1 / 8 : ℂ) • x) := by
    rw [ωN, map_sum, Finset.sum_apply, LinearMap.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ωN_one_eq, map_smul, Pi.smul_apply, LinearMap.smul_apply, YT_sq_two, mode_Ywt_pair_zero,
      LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
  rw [h1]
  simp only [mode_nprod_Fgen_zero, smul_add, Finset.smul_sum]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_eq_single v.2]
    · rw [if_pos rfl, smul_smul]; norm_num
    · intro b _ hb; rw [if_neg (Ne.symm hb), smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_smul,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    ring

/-- **The `L0_weight` field**: `YT ω 2` acts on `weightT r q` by `q`. -/
theorem YT_omega_two_weightT {q : ℚ} {x : FockT r} (hx : x ∈ weightT r q) :
    YT r (heisVOA1 r).conformalVector 2 x = (q : ℂ) • x := by
  rw [YT_omega_two]
  exact L0T_of_mem_weightT hx

end Moonshine

end VOA
