/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorModel

/-!
# Type-generic assembly of the pair comparison from integer certificates

Integer two-slot tables `ZTab S` are cast to pair tables (`castT`).  `LevOK D ℓ T` says that
`H^D (z_a - z_b)^ℓ F · T` is good for every pair of slots and canonical spectators.  It is closed
under integer combinations, holds for the base table `δ_{c₀}⊗δ_{c₀}` (`levOK_base`), and is
propagated by the integer pair operators (`levOK_S`, `levOK_A`, given integer structure constants).

**`pairComparisonG_of_cert`**: if, for integer relation coefficients `q_r(c,d)` of the full `I₂`,
* `N_A (e_c⊗e_d - e_d⊗e_c)` is `LevOK D 1` for `c < d` (the `Λ²` part),
* tables `U_r` are `LevOK D 2` (a complement of `V(2θ)` in `Sym²`), and
* `N_S (e_c⊗e_d + e_d⊗e_c) - Σ_r (q_r(c,d) + q_r(d,c)) U_r` is `LevOK D 0` for `c ≤ d`
  (the `V(2θ)` part, modulo the relation coordinates),

then `PairComparisonG S` holds.  The proof splits a carrier pair table into its antisymmetric part
(divisible by `z_a - z_b`, `anti_dvd`) and its symmetric part, whose relation coordinates are
divisible by `(z_a - z_b)²` (`relSym_sq_dvd`).
-/

namespace VOA.DeligneAudit.DeligneDivisor

open MvPolynomial VOA.DeligneAudit.SectorLoop VOA.QuadraticCurrentFunctionalCarrier
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.A2 (Pm)

noncomputable section

variable {S : DeligneSectorData} {m : ℕ}

variable (S) in
/-- Integer two-slot tables. -/
abbrev ZTab := Fin S.n → Fin S.n → ℤ

/-- Cast of an integer table. -/
def castT (T : ZTab S) : PairTable S m := fun c d => MvPolynomial.C ((T c d : ℤ) : ℂ)

theorem castT_add (T U : ZTab S) : castT (m := m) (T + U) = castT T + castT U := by
  funext c d; simp [castT]

theorem castT_zero : castT (m := m) (0 : ZTab S) = 0 := by
  funext c d; simp [castT]

theorem castT_neg (T : ZTab S) : castT (m := m) (-T) = -castT T := by
  funext c d; simp [castT]

theorem castT_sub (T U : ZTab S) : castT (m := m) (T - U) = castT T - castT U := by
  funext c d; simp [castT]

theorem castT_zsmul (k : ℤ) (T : ZTab S) :
    castT (m := m) (k • T) = (MvPolynomial.C ((k : ℤ) : ℂ) : Pm m) • castT T := by
  funext c d; simp [castT]

theorem castT_sum {ι : Type*} (s : Finset ι) (T : ι → ZTab S) :
    castT (m := m) (∑ i ∈ s, T i) = ∑ i ∈ s, castT (T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [castT_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, castT_add, ih]

/-! ## The level predicate -/

/-- `H^D (z_a - z_b)^ℓ F · T` is good for all slots and canonical spectators. -/
def LevOK (D ℓ : ℕ) (T : ZTab S) : Prop :=
  ∀ (m : ℕ) (a b : Fin m), a ≠ b → ∀ s : Fin m → Fin S.n, IsCanon a b s →
    (Hpair a b ^ D * zab a b ^ ℓ * Fspec S a b) • castT (m := m) T ∈ Good a b s

theorem levOK_zero (D ℓ : ℕ) : LevOK D ℓ (0 : ZTab S) := by
  intro m a b _ s _; rw [castT_zero, smul_zero]; exact Submodule.zero_mem _

theorem levOK_add {D ℓ : ℕ} {T U : ZTab S} (hT : LevOK D ℓ T) (hU : LevOK D ℓ U) :
    LevOK D ℓ (T + U) := by
  intro m a b hab s hs; rw [castT_add, smul_add]; exact Submodule.add_mem _ (hT m a b hab s hs)
    (hU m a b hab s hs)

theorem levOK_zsmul {D ℓ : ℕ} (k : ℤ) {T : ZTab S} (hT : LevOK D ℓ T) : LevOK D ℓ (k • T) := by
  intro m a b hab s hs
  rw [castT_zsmul, smul_comm]
  exact Submodule.smul_mem _ _ (hT m a b hab s hs)

theorem levOK_neg {D ℓ : ℕ} {T : ZTab S} (hT : LevOK D ℓ T) : LevOK D ℓ (-T) := by
  have := levOK_zsmul (-1) hT; rwa [neg_one_zsmul] at this

theorem levOK_sub {D ℓ : ℕ} {T U : ZTab S} (hT : LevOK D ℓ T) (hU : LevOK D ℓ U) :
    LevOK D ℓ (T - U) := by
  rw [sub_eq_add_neg]; exact levOK_add hT (levOK_neg hU)

theorem levOK_sum {D ℓ : ℕ} {ι : Type*} (s : Finset ι) {T : ι → ZTab S}
    (h : ∀ i ∈ s, LevOK D ℓ (T i)) : LevOK D ℓ (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact levOK_zero D ℓ
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact levOK_add (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem levOK_mono {D D' ℓ ℓ' : ℕ} {T : ZTab S} (hT : LevOK D ℓ T) (hD : D ≤ D') (hℓ : ℓ ≤ ℓ') :
    LevOK D' ℓ' T := by
  intro m a b hab s hs
  have h := Submodule.smul_mem _ (Hpair a b ^ (D' - D) * zab a b ^ (ℓ' - ℓ)) (hT m a b hab s hs)
  rw [smul_smul] at h
  convert h using 2
  rw [show D' = (D' - D) + D by omega, show ℓ' = (ℓ' - ℓ) + ℓ by omega, pow_add, pow_add]
  rw [show D' - D + D - D = D' - D by omega, show ℓ' - ℓ + ℓ - ℓ = ℓ' - ℓ by omega]
  ring

/-! ## Base and pair operators on integer tables -/

/-- The base table `δ_{c₀} ⊗ δ_{c₀}`. -/
def baseZ : ZTab S := fun c d => if c = S.c₀ ∧ d = S.c₀ then 1 else 0

theorem levOK_base : LevOK 0 0 (baseZ (S := S)) := by
  intro m a b hab s hs
  have h := good_base hab hs
  have e : castT (m := m) (baseZ (S := S)) = baseT := by
    funext c d; simp only [castT, baseZ, baseT]; split_ifs <;> simp
  rw [e]
  simpa using h

section Ops

variable (fI : Fin S.n → Fin S.n → Fin S.n → ℤ) (hf : ∀ x c e, S.f x c e = (fI x c e : ℂ))
include hf

/-- Integer coadjoint action in the first slot. -/
def opAZ (x : Fin S.n) (T : ZTab S) : ZTab S := fun c d => -∑ e, fI x c e * T e d

/-- Integer coadjoint action in the second slot. -/
def opBZ (x : Fin S.n) (T : ZTab S) : ZTab S := fun c d => -∑ e, fI x d e * T c e

omit hf in
theorem castT_opAZ (hf : ∀ x c e, S.f x c e = (fI x c e : ℂ)) (x : Fin S.n) (T : ZTab S) :
    opA x (castT (m := m) T) = castT (opAZ fI x T) := by
  funext c d
  simp only [opA, castT, opAZ, hf, Int.cast_neg, Int.cast_sum, Int.cast_mul, map_neg, map_sum,
    map_mul]

omit hf in
theorem castT_opBZ (hf : ∀ x c e, S.f x c e = (fI x c e : ℂ)) (x : Fin S.n) (T : ZTab S) :
    opB x (castT (m := m) T) = castT (opBZ fI x T) := by
  funext c d
  simp only [opB, castT, opBZ, hf, Int.cast_neg, Int.cast_sum, Int.cast_mul, map_neg, map_sum,
    map_mul]

theorem levOK_S {D ℓ : ℕ} (x : Fin S.n) {T : ZTab S} (hT : LevOK D ℓ T) :
    LevOK (D + 1) ℓ (opAZ fI x T + opBZ fI x T) := by
  intro m a b hab s hs
  have h := good_S x hab (hT m a b hab s hs)
  rw [opA_smul, opB_smul, ← smul_add, smul_smul, castT_opAZ fI hf, castT_opBZ fI hf,
    ← castT_add] at h
  convert h using 2
  ring

theorem levOK_A {D ℓ : ℕ} (x : Fin S.n) {T : ZTab S} (hT : LevOK D ℓ T) :
    LevOK (D + 1) (ℓ + 1) (opAZ fI x T - opBZ fI x T) := by
  intro m a b hab s hs
  have h := good_A x hab (hT m a b hab s hs)
  rw [opA_smul, opB_smul, ← smul_sub, smul_smul, castT_opAZ fI hf, castT_opBZ fI hf,
    ← castT_sub] at h
  convert h using 2
  ring

end Ops

/-! ## Symmetric and antisymmetric elementary tables -/

/-- `e_c⊗e_d + e_d⊗e_c`. -/
def symZ (c d : Fin S.n) : ZTab S := fun c' d' =>
  (if c' = c ∧ d' = d then 1 else 0) + (if c' = d ∧ d' = c then 1 else 0)

/-- `e_c⊗e_d - e_d⊗e_c`. -/
def antiZ (c d : Fin S.n) : ZTab S := fun c' d' =>
  (if c' = c ∧ d' = d then 1 else 0) - (if c' = d ∧ d' = c then 1 else 0)

theorem symZ_comm (c d : Fin S.n) : symZ c d = symZ (S := S) d c := by
  funext c' d'; simp only [symZ]; ring

theorem antiZ_comm (c d : Fin S.n) : antiZ c d = -antiZ (S := S) d c := by
  funext c' d'; simp only [antiZ, Pi.neg_apply]; ring

theorem antiZ_self (c : Fin S.n) : antiZ c c = (0 : ZTab S) := by
  funext c' d'; simp [antiZ]

theorem sum_elem (V : PairTable S m) (c' d' : Fin S.n) :
    (∑ c, ∑ d, V c d * MvPolynomial.C (((if c' = c ∧ d' = d then 1 else 0 : ℤ)) : ℂ)) =
      V c' d' := by
  rw [Finset.sum_eq_single c']
  · rw [Finset.sum_eq_single d']
    · simp
    · intro d _ hd; simp [Ne.symm hd]
    · simp
  · intro c _ hc; refine Finset.sum_eq_zero fun d _ => ?_; simp [Ne.symm hc]
  · simp

theorem sum_symZ (V : PairTable S m) :
    (∑ c, ∑ d, V c d • castT (m := m) (symZ c d)) = fun c' d' => V c' d' + V d' c' := by
  funext c' d'
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, castT, symZ, Int.cast_add, map_add,
    mul_add, Finset.sum_add_distrib]
  rw [sum_elem V c' d']
  congr 1
  have := sum_elem V d' c'
  rw [← this]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  congr 3
  split_ifs <;> first | rfl | (exfalso; tauto)

theorem sum_antiZ (V : PairTable S m) :
    (∑ c, ∑ d, V c d • castT (m := m) (antiZ c d)) = fun c' d' => V c' d' - V d' c' := by
  funext c' d'
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, castT, antiZ, Int.cast_sub, map_sub,
    mul_sub, Finset.sum_sub_distrib]
  rw [sum_elem V c' d']
  congr 1
  have := sum_elem V d' c'
  rw [← this]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  congr 3
  split_ifs <;> first | rfl | (exfalso; tauto)

/-! ## Assembly -/

theorem good_unsmul {a b : Fin m} {s : Fin m → Fin S.n} (k : ℕ) (hk : k ≠ 0)
    {Y : PairTable S m} (h : (k : Pm m) • Y ∈ Good a b s) : Y ∈ Good a b s := by
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have := Submodule.smul_mem _ (MvPolynomial.C ((k : ℂ)⁻¹) : Pm m) h
  rwa [smul_smul, show (MvPolynomial.C ((k : ℂ)⁻¹) : Pm m) * (k : Pm m) = 1 by
    rw [← map_natCast (MvPolynomial.C (σ := Fin (m + 0)) (R := ℂ)), ← map_mul,
      inv_mul_cancel₀ hk', map_one], one_smul] at this

/-- **The pair comparison from integer certificates.** -/
theorem pairComparisonG_of_cert (qI : Option S.ρ → Fin S.n → Fin S.n → ℤ)
    (hq : ∀ r c d, S.fullMatrix r (c, d) = (qI r c d : ℂ)) (D NA NS : ℕ) (hNA : NA ≠ 0)
    (hNS : NS ≠ 0) (U : Option S.ρ → ZTab S)
    (hA : ∀ c d : Fin S.n, c < d → LevOK D 1 ((NA : ℤ) • antiZ c d))
    (hU : ∀ r, LevOK D 2 (U r))
    (hV : ∀ c d : Fin S.n, c ≤ d →
      LevOK D 0 ((NS : ℤ) • symZ c d - ∑ r, (qI r c d + qI r d c) • U r)) :
    PairComparisonG S := by
  -- extend the certificates to all pairs
  have hA' : ∀ c d : Fin S.n, LevOK D 1 ((NA : ℤ) • antiZ c d) := by
    intro c d
    rcases lt_trichotomy c d with h | rfl | h
    · exact hA c d h
    · rw [antiZ_self, smul_zero]; exact levOK_zero D 1
    · rw [antiZ_comm, smul_neg]; exact levOK_neg (hA d c h)
  have hV' : ∀ c d : Fin S.n,
      LevOK D 0 ((NS : ℤ) • symZ c d - ∑ r, (qI r c d + qI r d c) • U r) := by
    intro c d
    rcases le_total c d with h | h
    · exact hV c d h
    · have := hV d c h
      rw [symZ_comm d c] at this
      have e : ∑ r, (qI r c d + qI r d c) • U r = ∑ r, (qI r d c + qI r c d) • U r :=
        Finset.sum_congr rfl fun r _ => by rw [add_comm]
      rw [e]; exact this
  refine pairComparisonG_of_good D fun m x hx a b hab s hs => ?_
  set Y := pairTable x a b s with hY
  set K : Pm m := Hpair a b ^ D * Fspec S a b with hK
  -- antisymmetric part
  choose Z hZ using fun c d => anti_dvd a b hab s hx c d
  have hne : (zab a b : Pm m) ≠ 0 := by
    rw [zab, sub_ne_zero]; intro h
    exact hab ((Fin.castAdd_injective m 0) (X_injective h))
  have hZanti : ∀ c d, Z c d = -Z d c := by
    intro c d
    have h1 : zab a b * Z c d = -(zab a b * Z d c) := by
      rw [← hZ c d, ← hZ d c]; ring
    rw [← mul_neg] at h1
    exact mul_left_cancel₀ hne h1
  set A := ∑ c, ∑ d, Z c d • (K * zab a b) • castT (m := m) ((NA : ℤ) • antiZ c d) with hAdef
  have hAgood : A ∈ Good a b s := by
    refine Submodule.sum_mem _ fun c _ => Submodule.sum_mem _ fun d _ =>
      Submodule.smul_mem _ _ ?_
    have := hA' c d m a b hab s hs
    rwa [pow_one, show Hpair a b ^ D * zab a b * Fspec S a b = K * zab a b by rw [hK]; ring]
      at this
  -- symmetric part
  have hrel : ∀ r, ∃ φ : Pm m,
      (∑ c : Fin S.n, ∑ d : Fin S.n,
        (Y c d * MvPolynomial.C (((qI r c d + qI r d c : ℤ) : ℂ)) : Pm m)) = zab a b ^ 2 * φ := by
    intro r
    obtain ⟨φ, hφ⟩ := relSym_sq_dvd a b hab s hx r
    refine ⟨φ, ?_⟩
    rw [← hφ, relSym]
    simp only [hq, mul_add, Finset.sum_add_distrib, Int.cast_add, map_add]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_; ring
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_; ring
  choose φ hφ using hrel
  set T0 : Fin S.n → Fin S.n → ZTab S := fun c d =>
    (NS : ℤ) • symZ c d - ∑ r, (qI r c d + qI r d c) • U r with hT0
  set ψ : Option S.ρ → Fin S.n → Fin S.n → Pm m := fun r c d =>
    MvPolynomial.C (((qI r c d + qI r d c : ℤ)) : ℂ) with hψ
  have hsymsplit : ∀ c d, castT (m := m) ((NS : ℤ) • symZ c d) =
      castT (T0 c d) + ∑ r, ψ r c d • castT (U r) := by
    intro c d
    rw [hT0]
    simp only [castT_sub, castT_sum, castT_zsmul, hψ]
    abel
  set B := ∑ c, ∑ d, Y c d • K • castT (m := m) ((NS : ℤ) • symZ c d) with hBdef
  have hBgood : B ∈ Good a b s := by
    have e : B = (∑ c, ∑ d, Y c d • K • castT (m := m) (T0 c d)) +
        ∑ r, φ r • (Hpair a b ^ D * zab a b ^ 2 * Fspec S a b) • castT (m := m) (U r) := by
      rw [hBdef]
      simp only [hsymsplit, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
      congr 1
      have e3 : ∀ F : Fin S.n → Fin S.n → Option S.ρ → PairTable S m,
          ∑ c, ∑ d, ∑ r, F c d r = ∑ r, ∑ c, ∑ d, F c d r := by
        intro F
        rw [Finset.sum_congr rfl fun c _ => Finset.sum_comm]
        exact Finset.sum_comm
      rw [e3]
      refine Finset.sum_congr rfl fun r _ => ?_
      have h1 : (∑ c, ∑ d, Y c d • K • ψ r c d • castT (m := m) (U r)) =
          (∑ c, ∑ d, Y c d * ψ r c d) • K • castT (m := m) (U r) := by
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun d _ => ?_
        simp only [smul_smul]
        congr 1; ring
      rw [h1]
      have := hφ r
      simp only [hψ] at this ⊢
      rw [this]
      simp only [smul_smul]
      congr 1
      rw [hK]; ring
    rw [e]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun c _ => Submodule.sum_mem _ fun d _ =>
      Submodule.smul_mem _ _ ?_) (Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (hU r m a b
        hab s hs))
    have := hV' c d m a b hab s hs
    rwa [pow_zero, mul_one] at this
  -- combine: `4 NA NS K Y = 2 NA B + NS A`
  have hcomb : ((4 * NA * NS : ℕ) : Pm m) • (K • Y) =
      ((2 * NA : ℕ) : Pm m) • B + ((NS : ℕ) : Pm m) • A := by
    funext c' d'
    have hB : B c' d' = K * (MvPolynomial.C ((NS : ℤ) : ℂ) * (Y c' d' + Y d' c')) := by
      rw [hBdef]
      have := congrFun (congrFun (sum_symZ (S := S) (m := m) Y) c') d'
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, castT_zsmul] at this ⊢
      rw [← this, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      ring
    have hA2 : A c' d' = K * zab a b * (MvPolynomial.C ((NA : ℤ) : ℂ) * (Z c' d' - Z d' c')) := by
      rw [hAdef]
      have := congrFun (congrFun (sum_antiZ (S := S) (m := m) Z) c') d'
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, castT_zsmul] at this ⊢
      rw [← this, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      ring
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hB, hA2]
    have hz := hZ c' d'
    rw [hZanti d' c']
    simp only [map_natCast, Int.cast_natCast]
    push_cast
    linear_combination (2 * (NA : Pm m) * (NS : Pm m) * K) * hz
  have hsum : ((4 * NA * NS : ℕ) : Pm m) • (K • Y) ∈ Good a b s := by
    rw [hcomb]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hBgood) (Submodule.smul_mem _ _ hAgood)
  refine good_unsmul (4 * NA * NS) (by positivity) ?_
  rw [smul_smul] at hsum ⊢
  convert hsum using 2

end

end VOA.DeligneAudit.DeligneDivisor

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneDivisor.levOK_S
#print axioms VOA.DeligneAudit.DeligneDivisor.levOK_A
#print axioms VOA.DeligneAudit.DeligneDivisor.pairComparisonG_of_cert
end AxiomAudit
