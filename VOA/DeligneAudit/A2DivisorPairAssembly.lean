/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2DivisorPairTree
import VOA.DeligneAudit.A2PairW
import VOA.DeligneAudit.A2DivisorPairMatrixBridge
import VOA.DeligneAudit.A2DivisorPairPhi

/-!
# Assembly of `PairComparison` (B7 at the divisor), hence `DivisorComparison`

For `x ∈ W_m`, slots `a ≠ b` and canonical spectators `s`, the pair table `Y = pairTable x a b s`
(= the `twoSlot`) splits as `projV Y + projL Y + projI Y` (the `decomp`), with
`projL Y = (z_a - z_b) Z` and `relCoord r Y = (z_a - z_b)² ψ_r` (the `projL_dvd`, `relCoord_sq_dvd`).
The generation side (`goodLev`, the certificates `sym_cert`, `anti_cert`) shows that
`H⁴ F` times each part is good:
* `good_V`: symmetric tables annihilated by the relations (level-0 tables, `V(2θ)`);
* `good_L`: `(z_a - z_b)` times antisymmetric tables (level ≤ 1, `Λ²g`);
* `good_symT2`: `(z_a - z_b)²` times any symmetric table (level ≤ 2), giving the `I₂` part.
Since `H⁴ F ∣ E_{ab}^{8+3m}`, **`pairComparison : PairComparison`** follows, and with
`divisorComparison_of_pair`, **`divisorComparison : DivisorComparison`**.
-/

namespace VOA.DeligneAudit.A2

open MvPolynomial VOA.AffineSl3 VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.SectorFiber
open VOA.DeligneAudit.SectorFiberModule VOA.QuadraticCurrentFunctionalCarrier
open PairCert

noncomputable section

variable {m : ℕ}

theorem pairTable_eq_twoSlot (x : TP m) (a b : Fin m) (s : Fin m → Fin 8) :
    pairTable x a b s = twoSlot x a b s := rfl

theorem castT_zero : castT (m := m) (fun _ _ => 0) = 0 := by
  funext c d; simp [castT]

theorem castT_comb_cons (p : Fin 64 × ℤ) (L : List (Fin 64 × ℤ)) :
    castT (m := m) (comb (p :: L)) =
      (MvPolynomial.C (p.2 : ℂ) : Pm m) • castT (tB p.1) + castT (comb L) := by
  funext c d
  simp [castT, comb]

theorem castT_comb_nil : castT (m := m) (comb []) = 0 := by
  funext c d; simp [castT, comb]

theorem castT_sum (f : Option (Fin 8) → ZT) :
    castT (m := m) (fun c d => ∑ r, f r c d) = ∑ r, castT (f r) := by
  funext c d
  simp [castT, Finset.sum_apply]

theorem good_unsmul {a b : Fin m} {s : Fin m → Fin 8} (k : ℕ) (hk : k ≠ 0) {Y : PairTable m}
    (h : (k : Pm m) • Y ∈ Good a b s) : Y ∈ Good a b s := by
  have h2 := Submodule.smul_mem (Good a b s) (MvPolynomial.C ((k : ℂ)⁻¹)) h
  rwa [smul_smul, show (MvPolynomial.C ((k : ℂ)⁻¹) : Pm m) * (k : Pm m) = 1 by
    rw [← map_natCast MvPolynomial.C k, ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hk),
      map_one], one_smul] at h2

/-! ### Symmetric and antisymmetric tables -/

theorem sum_symT (V : PairTable m) :
    (∑ c, ∑ d, V c d • castT (m := m) (symT c d)) = fun c' d' => V c' d' + V d' c' := by
  funext c' d'
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, castT, symT, eT]
  simp only [Int.cast_add, map_add, mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single c']
    · rw [Finset.sum_eq_single d']
      · simp
      · intro d _ hd; simp [Ne.symm hd]
      · simp
    · intro c _ hc; refine Finset.sum_eq_zero fun d _ => ?_; simp [Ne.symm hc]
    · simp
  · rw [Finset.sum_eq_single d']
    · rw [Finset.sum_eq_single c']
      · simp
      · intro d _ hd; simp [Ne.symm hd]
      · simp
    · intro c _ hc; refine Finset.sum_eq_zero fun d _ => ?_; simp [Ne.symm hc]
    · simp

theorem sum_antiT (Z : PairTable m) :
    (∑ c, ∑ d, Z c d • castT (m := m) (antiT c d)) = fun c' d' => Z c' d' - Z d' c' := by
  funext c' d'
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, castT, antiT, eT]
  simp only [Int.cast_sub, map_sub, mul_sub, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single c']
    · rw [Finset.sum_eq_single d']
      · simp
      · intro d _ hd; simp [Ne.symm hd]
      · simp
    · intro c _ hc; refine Finset.sum_eq_zero fun d _ => ?_; simp [Ne.symm hc]
    · simp
  · rw [Finset.sum_eq_single d']
    · rw [Finset.sum_eq_single c']
      · simp
      · intro d _ hd; simp [Ne.symm hd]
      · simp
    · intro c _ hc; refine Finset.sum_eq_zero fun d _ => ?_; simp [Ne.symm hc]
    · simp

/-! ### The relations as integer tables -/

theorem fullMatrix_eq_qZ (r : Option (Fin 8)) (c d : Fin 8) :
    fullMatrix r (c, d) = (qZ r c d : ℂ) :=
  PairCert.matrix_eq_qZ_checked r c d

theorem phiZ_symT (r : Option (Fin 8)) (c d : Fin 8) :
    phiZ r (symT c d) = qZ r c d + qZ r d c :=
  PairCert.phiZ_symT_generic r c d

theorem castT_mulNat (k : ℕ) (T : ZT) :
    castT (m := m) (fun c d => (k : ℤ) * T c d) = (k : Pm m) • castT (m := m) T := by
  funext c d; simp [castT]

theorem castT_mulInt (k : ℤ) (T : ZT) :
    castT (m := m) (fun c d => k * T c d) = (k : Pm m) • castT (m := m) T := by
  funext c d; simp [castT]

/-- `72 · symT c d = (level 0) + Σ_r φ_r(symT c d) U_r`, cast to pair tables. -/
theorem castT_sym_cert (c d : Fin 8) :
    ((72 : ℕ) : Pm m) • castT (m := m) (symT c d) =
      castT (m := m) (comb (symL c d)) +
        ∑ r, ((phiZ r (symT c d) : ℤ) : Pm m) • castT (m := m) (UZ r) := by
  have h := congrArg (castT (m := m)) (sym_cert c d)
  have h72 : (fun c' d' => (72 : ℤ) * symT c d c' d') = fun c' d' => ((72 : ℕ) : ℤ) * symT c d c' d' :=
    rfl
  rw [h72, castT_mulNat] at h
  rw [h, castT_add, castT_sum]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [castT_mulInt]

theorem castT_anti_cert (c d : Fin 8) :
    ((6 : ℕ) : Pm m) • castT (m := m) (antiT c d) = castT (m := m) (comb (antiL c d)) := by
  have h := congrArg (castT (m := m)) (anti_cert c d)
  have h6 : (fun c' d' => (6 : ℤ) * antiT c d c' d') = fun c' d' => ((6 : ℕ) : ℤ) * antiT c d c' d' :=
    rfl
  rw [h6, castT_mulNat] at h
  exact h

/-- The relation pairing in integer form. -/
theorem relCoord_two (r : Option (Fin 8)) (V : PairTable m) :
    (∑ c, ∑ d, V c d * ((phiZ r (symT c d) : ℤ) : Pm m)) = (2 : Pm m) * relCoord r V := by
  rw [relCoord, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [phiZ_symT, Qsym, fullMatrix_eq_qZ, fullMatrix_eq_qZ, ← map_intCast (MvPolynomial.C (σ := Fin (m + 0)) (R := ℂ)),
    (map_ofNat (MvPolynomial.C (σ := Fin (m + 0)) (R := ℂ)) 2).symm]
  simp only [Int.cast_add]
  rw [mul_comm (V c d), ← mul_assoc, ← map_mul]
  congr 2
  ring

/-- The dual functional `ε_r` as a pair table. -/
def epsTab (r : Option (Fin 8)) : PairTable m := fun c d => MvPolynomial.C (epsI r c d)

/-! ### Generation -/

section Gen

variable {a b : Fin m} (hab : a ≠ b) {s : Fin m → Fin 8} (hs : IsCanon a b s)
include hab hs

theorem good_comb (L : List (Fin 64 × ℤ)) (ℓ : ℕ) (hL : ∀ p ∈ L, lev p.1 ≤ ℓ) :
    (Hpair a b ^ 4 * zab a b ^ ℓ * Fspec a b) • castT (comb L) ∈ Good a b s := by
  induction L with
  | nil => rw [castT_comb_nil, smul_zero]; exact Submodule.zero_mem _
  | cons p L ih =>
    rw [castT_comb_cons, smul_add]
    refine Submodule.add_mem _ ?_ (ih fun q hq => hL q (List.mem_cons_of_mem _ hq))
    rw [smul_comm]
    refine Submodule.smul_mem _ _ ?_
    have hp := hL p List.mem_cons_self
    have h := good_pad hab hs (zab a b ^ (ℓ - lev p.1)) (goodLev hab hs p.1)
    rwa [show zab a b ^ (ℓ - lev p.1) * (Hpair a b ^ 4 * zab a b ^ lev p.1 * Fspec a b) =
      Hpair a b ^ 4 * zab a b ^ ℓ * Fspec a b by
        rw [show ℓ = (ℓ - lev p.1) + lev p.1 by omega, pow_add]
        rw [show ℓ - lev p.1 + lev p.1 - lev p.1 = ℓ - lev p.1 by omega]
        ring] at h

theorem good_symT2 (c d : Fin 8) :
    (Hpair a b ^ 4 * zab a b ^ 2 * Fspec a b) • castT (symT c d) ∈ Good a b s := by
  apply good_unsmul 72 (by norm_num)
  rw [smul_comm, castT_sym_cert, smul_add, Finset.smul_sum]
  refine Submodule.add_mem _ (good_comb hab hs _ 2 fun p hp => ?_) ?_
  · have := symL_lev c d p hp; omega
  · refine Submodule.sum_mem _ fun r _ => ?_
    rw [smul_comm]
    exact Submodule.smul_mem _ _ (good_comb hab hs _ 2 (UL_lev r))

/-- **The `V(2θ)` part.** -/
theorem good_V (V : PairTable m) (hsym : ∀ c d, V c d = V d c)
    (hrel : ∀ r, relCoord r V = 0) : (Hpair a b ^ 4 * Fspec a b) • V ∈ Good a b s := by
  have h2V : (∑ c, ∑ d, V c d • castT (m := m) (symT c d)) = (2 : Pm m) • V := by
    rw [sum_symT]; funext c' d'; rw [hsym d' c']
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  have step : ∀ c, ((72 : ℕ) : Pm m) • (∑ d, V c d • castT (m := m) (symT c d)) =
      (∑ d, V c d • castT (m := m) (comb (symL c d))) +
        ∑ r, (∑ d, V c d * ((phiZ r (symT c d) : ℤ) : Pm m)) • castT (m := m) (UZ r) := by
    intro c
    rw [Finset.smul_sum]
    have e1 : ∀ d, ((72 : ℕ) : Pm m) • (V c d • castT (m := m) (symT c d)) =
        V c d • castT (m := m) (comb (symL c d)) +
          ∑ r, (V c d * ((phiZ r (symT c d) : ℤ) : Pm m)) • castT (m := m) (UZ r) := by
      intro d
      rw [smul_comm, castT_sym_cert, smul_add, Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [smul_smul]
    rw [Finset.sum_congr rfl fun d _ => e1 d, Finset.sum_add_distrib, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_smul]
  have hkey : ((72 : ℕ) : Pm m) • ((2 : Pm m) • V) =
      ∑ c, ∑ d, V c d • castT (m := m) (comb (symL c d)) := by
    rw [← h2V, Finset.smul_sum, Finset.sum_congr rfl fun c _ => step c, Finset.sum_add_distrib]
    have hz : (∑ c : Fin 8, ∑ r : Option (Fin 8),
        (∑ d, V c d * ((phiZ r (symT c d) : ℤ) : Pm m)) • castT (m := m) (UZ r)) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [← Finset.sum_smul, relCoord_two, hrel r, mul_zero, zero_smul]
    rw [hz, add_zero]
  apply good_unsmul 144 (by norm_num)
  have h144 : ((144 : ℕ) : Pm m) • V = ((72 : ℕ) : Pm m) • ((2 : Pm m) • V) := by
    rw [smul_smul]; norm_num
  rw [smul_comm, h144, hkey, Finset.smul_sum]
  refine Submodule.sum_mem _ fun c _ => ?_
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun d _ => ?_
  rw [smul_comm]
  refine Submodule.smul_mem _ _ ?_
  have h := good_comb hab hs (symL c d) 0 fun p hp => (symL_lev c d p hp).le
  rwa [pow_zero, mul_one] at h

/-- **The `Λ²` part**: `(z_a - z_b)` times an antisymmetric table. -/
theorem good_L (Z : PairTable m) (hZ : ∀ c d, Z c d = -Z d c) :
    (Hpair a b ^ 4 * zab a b * Fspec a b) • Z ∈ Good a b s := by
  have h2Z : (∑ c, ∑ d, Z c d • castT (m := m) (antiT c d)) = (2 : Pm m) • Z := by
    rw [sum_antiT]; funext c' d'; rw [hZ d' c']
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  have hkey : ((6 : ℕ) : Pm m) • ((2 : Pm m) • Z) =
      ∑ c, ∑ d, Z c d • castT (m := m) (comb (antiL c d)) := by
    rw [← h2Z, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_comm, castT_anti_cert]
  apply good_unsmul 12 (by norm_num)
  have h12 : ((12 : ℕ) : Pm m) • Z = ((6 : ℕ) : Pm m) • ((2 : Pm m) • Z) := by
    rw [smul_smul]; norm_num
  rw [smul_comm, h12, hkey, Finset.smul_sum]
  refine Submodule.sum_mem _ fun c _ => ?_
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun d _ => ?_
  rw [smul_comm]
  refine Submodule.smul_mem _ _ ?_
  have h := good_comb hab hs (antiL c d) 1 (antiL_lev c d)
  rwa [pow_one] at h

theorem good_eps (r : Option (Fin 8)) :
    (Hpair a b ^ 4 * zab a b ^ 2 * Fspec a b) • epsTab (m := m) r ∈ Good a b s := by
  apply good_unsmul 2 (by norm_num)
  have h2 : ((2 : ℕ) : Pm m) • epsTab (m := m) r =
      ∑ c, ∑ d, epsTab (m := m) r c d • castT (m := m) (symT c d) := by
    rw [sum_symT]; funext c' d'
    simp only [epsTab, Pi.smul_apply, smul_eq_mul, epsI_symm r d' c']
    push_cast; ring
  rw [smul_comm, h2, Finset.smul_sum]
  refine Submodule.sum_mem _ fun c _ => ?_
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun d _ => ?_
  rw [smul_comm]
  exact Submodule.smul_mem _ _ (good_symT2 hab hs c d)

/-- **Every carrier pair table is good with factor `H⁴ F`.** -/
theorem good_pairTable {x : TP m} (hx : x ∈ currentCarrier fullMatrix m 0) :
    (Hpair a b ^ 4 * Fspec a b) • pairTable x a b s ∈ Good a b s := by
  rw [pairTable_eq_twoSlot]
  have hdec : twoSlot x a b s = projV (twoSlot x a b s) + projL (twoSlot x a b s) +
      projI (twoSlot x a b s) := by
    funext c d; exact decomp _ c d
  -- the `Λ²` part
  choose Z hZ using fun c d => projL_dvd a b hab s hx c d
  have hne : (zab a b : Pm m) ≠ 0 := by
    rw [zab, sub_ne_zero]; intro h; exact hab ((Fin.castAdd_injective m 0) (X_injective h))
  have hZanti : ∀ c d, Z c d = -Z d c := by
    intro c d
    have h1 := projL_antisymm (twoSlot x a b s) c d
    rw [hZ c d, hZ d c, ← mul_neg] at h1
    exact mul_left_cancel₀ hne h1
  have hL : projL (twoSlot x a b s) = zab a b • Z := by
    funext c d; exact hZ c d
  -- the `I₂` part
  choose ψ hψ using fun r => relCoord_sq_dvd a b hab s hx r
  have hI : projI (twoSlot x a b s) = ∑ r, (zab a b ^ 2 * ψ r) • epsTab (m := m) r := by
    funext c d
    rw [projI_apply, Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hψ r]
    change MvPolynomial.C (epsI r c d) * ((zr (K := ℂ) a - zr b) ^ 2 * ψ r) =
      (zab a b ^ 2 * ψ r) * MvPolynomial.C (epsI r c d)
    ring
  rw [hdec, smul_add, smul_add]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact good_V hab hs _ (projV_symm _) (fun r => relCoord_projV r _)
  · rw [hL, smul_smul, show Hpair a b ^ 4 * Fspec a b * zab a b =
      Hpair a b ^ 4 * zab a b * Fspec a b by ring]
    exact good_L hab hs Z hZanti
  · rw [hI, Finset.smul_sum]
    refine Submodule.sum_mem _ fun r _ => ?_
    rw [smul_smul, show Hpair a b ^ 4 * Fspec a b * (zab a b ^ 2 * ψ r) =
      ψ r * (Hpair a b ^ 4 * zab a b ^ 2 * Fspec a b) by ring, mul_smul]
    exact Submodule.smul_mem _ _ (good_eps hab hs r)

end Gen

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.good_pairTable
end AxiomAudit
