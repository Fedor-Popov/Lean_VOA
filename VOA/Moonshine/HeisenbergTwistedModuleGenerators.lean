/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.HeisenbergTwistedModuleSigma
import VOA.Moonshine.HeisenbergTwistedModuleReduction

/-!
# The twisted generator fields and their twisted commutator  (Moonshine step M6a)

The `σ`-twisted field of the weight-one generator `h_a(−1)𝟙 = X_{(0,a)}` of `heisVOA1 r` is the
half-integer moded twisted Heisenberg field `h_a(z) = Σ_{t ∈ ½+ℤ} h_a(t) z^{−t−1}` on
`S[θ] = FockT r`; in the fractional-mode carrier of `Modularity/Twisted.lean`
(`YM u k = u₍k/2₎`) its modes are `modeT r a k` (`= h_a(k/2)`, zero for even `k`).

* **Support (5.3.22a).**  `X_{(0,a)} ∈ 𝒱¹` (`X_mem_twistedEigenspace_one`), and the modes vanish on
  every `k` with `(k + 1) % 2 ≠ 0`, i.e. on even `k` (`modeT_support`).
* **Truncation.**  `h_a(k/2) x = 0` for `k ≫ 0` (`modeT_truncation`).
* **The rescaled field** `Fgen r a = z^{1/2} h_a(z)` (offset `1`, `p`-th mode `h_a(p + ½)`) is an
  ordinary field; its commutator is the `δ`-expansion
  `[Fgen_a(z₁), Fgen_b(z₂)] = δ_{ab}(∂δ·z₂ + ½ δ)` (`bracketDist_Fgen`), so the generators are
  mutually local of order `2` (`Fgen_local`), with nonnegative products
  `Fgen_a ₍₀₎ Fgen_b = ½δ_{ab}`, `Fgen_a ₍₁₎ Fgen_b = δ_{ab} z`, `Fgen_a ₍ℓ₎ Fgen_b = 0` (`ℓ ≥ 2`)
  (`prod_Fgen_zero/one/of_two_le`).
* **The twisted commutator / Jacobi identity for the generators at `ℓ ≥ 0`**
  (`twistedJacobi_generators_nonneg`): for any linear fractional-mode map `YM` on `FockN r` which
  is lower truncated, sends `𝟙` to the identity (`YM 𝟙 k = δ_{k,−2}`) and `X_{(0,a)}` to the
  twisted Heisenberg field, the DLM twisted Jacobi identity holds for `u = X_{(0,a)}`,
  `v = X_{(0,b)}`, every `ℓ ≥ 0`, every odd `k` and every `m`.  It is obtained through the
  rescaling reduction (`TwistedReduction.twisted_jacobi_of_local_pf_ge`), which checks that the
  twisted product formula at `ℓ ≥ 0` — the fractional binomial `C(½, 1) = ½` against the central
  term `½ δ_{ab}` — is exactly the twisted Heisenberg relation
  `[h_a(k/2), h_b(m/2)] = (k/2) δ_{ab} δ_{k+m,0}`.  This pins down every convention (offset,
  binomial, vacuum index `−N`) of the reduction on a nontrivial instance.

The `ℓ < 0` part needs the twisted fields of the quadratic states `h_a(−n−1)h_b(−1)𝟙`, i.e. the
FLM `Δ_z` correction; see the Status.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
The `ℓ < 0` identities are not here.  The twisted vertex operator on all of `FockN r` (obtained
by inverting the twisted product formula against `Fgen`,
`Ỹ(h_a(−n−1)w) = Σᵢ C(−½, i) z^{−i} · Fgen_a ₍₋ₙ₋₁₊ᵢ₎ Ỹ(w)`) is built in
`HeisenbergTwistedModuleVertex`, which also specializes the theorem below to it.
-/

namespace VOA

namespace Moonshine

open MvPolynomial TwistedHeisenberg HeisenbergN TwistedReduction
open Module (End)

variable (r : ℕ)

/-! ## The twisted generator field -/

/-- **Support**: the twisted generator modes vanish off the odd (`k ≡ −1 mod 2`) coset. -/
theorem modeT_support (a : Fin r) (k : ℤ) (hk : (k + (1 : ℕ)) % ((2 : ℕ) : ℤ) ≠ 0) :
    modeT r a k = 0 :=
  modeT_even r a (by push_cast at hk; omega)

/-- **Truncation**: `h_a(k/2) x = 0` for `k ≫ 0`. -/
theorem modeT_truncation (a : Fin r) (x : FockT r) :
    ∃ K : ℤ, ∀ k : ℤ, K ≤ k → modeT r a k x = 0 := by
  refine ⟨2 * ((x.vars.sup (fun u => u.1) : ℕ) : ℤ) + 3, fun k hk => ?_⟩
  by_cases he : k % 2 = 0
  · rw [modeT_even r a he, LinearMap.zero_apply]
  · have hodd : Odd k := Int.odd_iff.mpr (by omega)
    rw [modeT_apply_pos r a hodd (by omega)]
    have hzero : pderiv (varT a k) x = 0 := by
      apply pderiv_eq_zero_of_notMem_vars
      intro hmem
      have hle : (varT a k).1 ≤ x.vars.sup (fun u => u.1) :=
        Finset.le_sup (f := fun u => u.1) hmem
      simp only [varT] at hle
      rw [abs_of_pos (by omega)] at hle
      omega
    rw [hzero, smul_zero]

/-! ## The rescaled generator field `z^{1/2} h_a(z)` -/

/-- The rescaled generator field `Fgen r a = z^{1/2} h_a(z)`: offset `1`, `p`-th mode
`h_a(p + ½) = modeT r a (2p + 1)`. -/
noncomputable def Fgen (a : Fin r) : FormalDist (End ℂ (FockT r)) := resc (modeT r a) 2 1

@[simp] theorem mode_Fgen (a : Fin r) (p : ℤ) : mode (Fgen r a) p = modeT r a (2 * p + 1) := by
  rw [Fgen, mode_resc]; push_cast; ring_nf

theorem Fgen_apply (a : Fin r) (n : ℤ) : Fgen r a n = modeT r a (-2 * n - 1) := by
  change modeT r a (((2 : ℕ) : ℤ) * (-n - 1) + 1) = _
  congr 1; push_cast; ring

/-- The order-one OPE coefficient: `δ_{ab} z · id`. -/
noncomputable def opeOne (a b : Fin r) : FormalDist (End ℂ (FockT r)) :=
  fun t => if t = 1 then (if a = b then (1 : ℂ) else 0) • LinearMap.id else 0

/-- The order-zero OPE coefficient: `½ δ_{ab} · id` — the twisted central term. -/
noncomputable def opeZero (a b : Fin r) : FormalDist (End ℂ (FockT r)) :=
  fun t => if t = 0 then (if a = b then (1 / 2 : ℂ) else 0) • LinearMap.id else 0

/-- **The twisted generator commutator** as a `δ`-expansion:
`[Fgen_a(z₁), Fgen_b(z₂)] = ∂δ · (δ_{ab} z) + δ · (½ δ_{ab})`. -/
theorem bracketDist_Fgen (a b : Fin r) :
    bracketDist (Fgen r a) (Fgen r b)
      = deltaDeriv 1 (opeOne r a b) + deltaDeriv 0 (opeZero r a b) := by
  refine FormalDist₂.ext fun m n => ?_
  rw [bracketDist_apply, Fgen_apply, Fgen_apply,
    modeT_comm r a b ⟨-m - 1, by ring⟩ ⟨-n - 1, by ring⟩]
  change _ = deltaDeriv 1 (opeOne r a b) m n + deltaDeriv 0 (opeZero r a b) m n
  rw [deltaDeriv_apply, deltaDeriv_apply, opeOne, opeZero]
  simp only [Finset.range_one, Finset.prod_singleton, Nat.cast_zero, sub_zero, Finset.range_zero,
    Finset.prod_empty, one_smul, Nat.cast_one]
  split_ifs with h1 h2 h3 h4 h5 h6 <;> first
    | (exfalso; omega)
    | (simp_all; done)
    | (simp_all only [Int.reduceNeg, neg_mul, Int.cast_sub, Int.cast_neg, Int.cast_mul,
         Int.cast_ofNat, Int.cast_one, one_smul, zsmul_eq_mul, one_div]
       refine LinearMap.ext fun y => ?_
       simp only [LinearMap.smul_apply, LinearMap.add_apply, Module.End.mul_apply,
         LinearMap.id_apply, LinearMap.sub_apply, LinearMap.neg_apply, Module.End.intCast_apply,
         Module.End.one_apply]
       rw [← Int.cast_smul_eq_zsmul ℂ]
       module)

/-- **The twisted generators are mutually local** (order `2`). -/
theorem Fgen_local (a b : Fin r) : Local (Fgen r a) (Fgen r b) :=
  ⟨2, by rw [bracketDist_Fgen, map_add, mulBySubPow_deltaDeriv_eq_zero (by norm_num),
    mulBySubPow_deltaDeriv_eq_zero (by norm_num), add_zero]⟩

/-- The rescaled generator field as an element of `Fld (FockT r)`. -/
noncomputable def FgenFld (a : Fin r) : Fld (FockT r) :=
  rescFld (A := modeT r a) (by norm_num : 0 < 2) (modeT_truncation r a) 1

@[simp] theorem FgenFld_val (a : Fin r) : (FgenFld r a).1 = Fgen r a := rfl

/-- `Fgen_a ₍₀₎ Fgen_b = ½ δ_{ab}`. -/
theorem prod_Fgen_zero (a b : Fin r) :
    (Fld.prod 0 (FgenFld r a) (FgenFld r b)).1 = opeZero r a b := by
  rw [Fld.prod_of_nonneg le_rfl, FgenFld_val, FgenFld_val, bracketDist_Fgen, cCoeff_add,
    cCoeff_deltaDeriv, cCoeff_deltaDeriv]
  simp

/-- `Fgen_a ₍₁₎ Fgen_b = δ_{ab} z`. -/
theorem prod_Fgen_one (a b : Fin r) :
    (Fld.prod 1 (FgenFld r a) (FgenFld r b)).1 = opeOne r a b := by
  rw [Fld.prod_of_nonneg zero_le_one, FgenFld_val, FgenFld_val, bracketDist_Fgen, cCoeff_add,
    cCoeff_deltaDeriv, cCoeff_deltaDeriv]
  simp

/-- `Fgen_a ₍ℓ₎ Fgen_b = 0` for `ℓ ≥ 2`. -/
theorem prod_Fgen_of_two_le (a b : Fin r) {ℓ : ℤ} (hℓ : 2 ≤ ℓ) :
    (Fld.prod ℓ (FgenFld r a) (FgenFld r b)).1 = 0 := by
  rw [Fld.prod_of_nonneg (by omega), FgenFld_val, FgenFld_val, bracketDist_Fgen, cCoeff_add,
    cCoeff_deltaDeriv, cCoeff_deltaDeriv, if_neg (by omega), if_neg (by omega), add_zero]

/-! ## The generator products inside `heisVOA1 r` -/

/-- `h_a(n) h_b(−1)𝟙` for `n ≥ 0` inside the level-one Heisenberg VOA: `δ_{n,1} δ_{ab} 𝟙`. -/
theorem smul_X_X_nonneg (a b : Fin r) {n : ℤ} (hn : 0 ≤ n) :
    (heisVOA1 r).smul (X (0, a)) n (X (0, b))
      = if n = 1 ∧ a = b then vacuumN r else 0 := by
  rw [PreVertexAlgebra.smul_def]
  change mode (YN r 1 (X (0, a))) n (X (0, b)) = _
  rw [← oscN_neg_one_vacuum r 1 a, YN_current, currentN_mode]
  rcases eq_or_lt_of_le hn with h0 | hpos
  · subst h0
    rw [oscN_zero, if_neg (by omega)]; rfl
  · rw [oscN_apply_pos r 1 a hpos, pderiv_X, one_smul]
    by_cases h : n = 1 ∧ a = b
    · obtain ⟨rfl, rfl⟩ := h
      simp [vacuumN]
    · rw [if_neg h, Pi.single_apply, if_neg, smul_zero]
      intro heq
      simp only [Prod.mk.injEq] at heq
      apply h
      exact ⟨by omega, heq.2.symm⟩

/-! ## The twisted Jacobi identity for the generators at `ℓ ≥ 0` -/

section GenJacobi

variable {r}
variable (YM : FockN r →ₗ[ℂ] (ℤ → End ℂ (FockT r)))
  (htr : ∀ (u : FockN r) (x : FockT r), ∃ K : ℤ, ∀ k : ℤ, K ≤ k → YM u k x = 0)
  (hvac : ∀ k : ℤ, YM (vacuumN r) k = if k = -2 then 1 else 0)
  (hgen : ∀ a : Fin r, YM (X (0, a)) = modeT r a)

include hvac in
/-- The rescaled field of the vacuum on an odd offset vanishes. -/
theorem resc_vac_odd (k : ℤ) (hk : k % 2 = 1) : YM (vacuumN r) k = 0 := by
  rw [hvac, if_neg (by omega)]

include hvac hgen in
/-- The twisted product formula for two generators at every `ℓ ≥ 0`, offsets `(1, e')`,
`e' ∈ {0, 1}`. -/
theorem pf_generators_nonneg (a b : Fin r) (e' : ℤ) (he' : e' = 0 ∨ e' = 1)
    (ℓ s : ℤ) (x : FockT r) (hℓ : 0 ≤ ℓ) :
    mode (Fld.prod ℓ (rescFld (by norm_num : 0 < 2) (htr (X (0, a))) 1)
        (rescFld (by norm_num : 0 < 2) (htr (X (0, b))) e')).1 s x
      = ∑ᶠ t : ℕ, cbinom (((1 : ℤ) : ℂ) / (2 : ℕ)) t •
          YM ((heisVOA1 r).smul (X (0, a)) (ℓ + t) (X (0, b))) ((2 : ℕ) * (s - t) + 1 + e') x := by
  -- the right side: only `ℓ + t = 1` survives
  have hR : (∑ᶠ t : ℕ, cbinom (((1 : ℤ) : ℂ) / (2 : ℕ)) t •
      YM ((heisVOA1 r).smul (X (0, a)) (ℓ + t) (X (0, b))) ((2 : ℕ) * (s - t) + 1 + e') x)
      = if ℓ ≤ 1 ∧ a = b then cbinom (1 / 2) (1 - ℓ).toNat •
          YM (vacuumN r) ((2 : ℕ) * (s - (1 - ℓ)) + 1 + e') x else 0 := by
    by_cases hc : ℓ ≤ 1 ∧ a = b
    · rw [if_pos hc]
      have h1 : ℓ + (((1 - ℓ).toNat : ℕ) : ℤ) = 1 := by omega
      have h2 : (((1 - ℓ).toNat : ℕ) : ℤ) = 1 - ℓ := by omega
      rw [finsum_eq_single _ (1 - ℓ).toNat (fun t ht => by
        rw [smul_X_X_nonneg r a b (by omega), if_neg (by omega), map_zero]; simp)]
      rw [smul_X_X_nonneg r a b (by omega), if_pos ⟨h1, hc.2⟩, h2]
      norm_num
    · rw [if_neg hc]
      refine finsum_eq_zero_of_forall_eq_zero fun t => ?_
      rw [smul_X_X_nonneg r a b (by omega), if_neg (fun h => hc ⟨by omega, h.2⟩), map_zero]
      simp
  rw [hR]
  -- the left side
  rcases he' with rfl | rfl
  · -- `e' = 0`: the rescaled even modes of a generator vanish
    have hzero : resc (YM (X (0, b))) 2 0 = 0 := by
      funext n
      change YM (X (0, b)) (((2 : ℕ) : ℤ) * (-n - 1) + 0) = 0
      rw [hgen, modeT_even]; push_cast; omega
    have hprod : (Fld.prod ℓ (rescFld (by norm_num : 0 < 2) (htr (X (0, a))) 1)
        (rescFld (by norm_num : 0 < 2) (htr (X (0, b))) 0)).1 = 0 := by
      rw [Fld.prod_of_nonneg hℓ, rescFld_val, rescFld_val, hzero]
      funext n
      change mulBySubPow ℓ.toNat (bracketDist _ 0) (-1) n = 0
      have : bracketDist (resc (YM (X (0, a))) 2 1) 0 = 0 := by
        apply FormalDist₂.ext; intro p q
        change resc (YM (X (0, a))) 2 1 p * 0 - 0 * resc (YM (X (0, a))) 2 1 p = 0
        simp
      rw [this, map_zero]; rfl
    rw [hprod]
    change (0 : End ℂ (FockT r)) x = _
    rw [LinearMap.zero_apply]
    split_ifs
    · rw [hvac, if_neg (by push_cast; omega), LinearMap.zero_apply, smul_zero]
    · rfl
  · -- `e' = 1`: both rescaled fields are `Fgen`
    have hF : ∀ c : Fin r, rescFld (by norm_num : 0 < 2) (htr (X (0, c))) 1 = FgenFld r c := by
      intro c
      apply Subtype.ext
      rw [rescFld_val, FgenFld_val, Fgen, hgen]
    rw [hF, hF]
    rcases lt_trichotomy ℓ 1 with hlt | rfl | hgt
    · obtain rfl : ℓ = 0 := by omega
      rw [prod_Fgen_zero, mode_apply, opeZero]
      by_cases hab : a = b
      · subst hab
        by_cases hs : s = -1
        · subst hs
          norm_num [hvac, cbinom]
        · have h1 : ¬ (-s - 1 = 0) := by omega
          have h2 : ¬ ((2 : ℤ) * (s - 1) + 1 + 1 = -2) := by omega
          simp [hvac, h1, h2]
      · simp [hab]
    · rw [prod_Fgen_one, mode_apply, opeOne]
      by_cases hab : a = b
      · subst hab
        by_cases hs : s = -2
        · subst hs
          norm_num [hvac]
        · have h1 : ¬ (-s - 1 = 1) := by omega
          have h2 : ¬ ((2 : ℤ) * s + 1 + 1 = -2) := by omega
          simp [hvac, h1, h2]
      · simp [hab]
    · rw [prod_Fgen_of_two_le r a b (by omega), if_neg (by omega)]
      rfl

include htr hvac hgen in
/-- **The twisted Jacobi identity for the generators, `ℓ ≥ 0`.**  For every linear,
lower-truncated fractional-mode map `YM` on `FockN r` sending `𝟙` to the identity field and the
generators `X_{(0,a)} = h_a(−1)𝟙` to the twisted Heisenberg fields, the DLM twisted Jacobi
identity (`N = 2`, `u = X_{(0,a)} ∈ 𝒱¹`, `v = X_{(0,b)}`) holds at every `ℓ ≥ 0`, every odd `k`
and every `m`. -/
theorem twistedJacobi_generators_nonneg (a b : Fin r) (x : FockT r) (ℓ k m : ℤ) (hℓ : 0 ≤ ℓ)
    (hk : (k + (1 : ℕ)) % ((2 : ℕ) : ℤ) = 0) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (YM (X (0, a)) (ℓ * (2 : ℕ) + k - i * (2 : ℕ)) (YM (X (0, b)) (m + i * (2 : ℕ)) x)
          - negOnePow ℓ • YM (X (0, b)) (ℓ * (2 : ℕ) + m - i * (2 : ℕ))
              (YM (X (0, a)) (k + i * (2 : ℕ)) x)))
      = ∑ᶠ i : ℕ, cbinom ((k : ℂ) / (2 : ℕ)) i •
          YM ((heisVOA1 r).smul (X (0, a)) (ℓ + i) (X (0, b))) (k + m - i * (2 : ℕ)) x := by
  have hN : (0 : ℕ) < 2 := by norm_num
  obtain ⟨q, hq⟩ : ∃ q : ℤ, k = (2 : ℕ) * q + 1 := ⟨(k - 1) / 2, by push_cast at hk ⊢; omega⟩
  have hm : m = (2 : ℕ) * (m / 2) + m % 2 := by push_cast; omega
  have he' : m % 2 = 0 ∨ m % 2 = 1 := by omega
  have hloc : Local (resc (YM (X (0, a))) 2 1) (resc (YM (X (0, b))) 2 (m % 2)) := by
    rcases he' with h | h
    · rw [h]
      have hzero : resc (YM (X (0, b))) 2 0 = 0 := by
        funext n
        change YM (X (0, b)) (((2 : ℕ) : ℤ) * (-n - 1) + 0) = 0
        rw [hgen, modeT_even]; push_cast; omega
      rw [hzero]
      refine local_of_bracketDist_eq_zero ?_
      apply FormalDist₂.ext; intro p q
      change resc (YM (X (0, a))) 2 1 p * 0 - 0 * resc (YM (X (0, a))) 2 1 p = 0
      simp
    · rw [h, hgen, hgen]
      exact Fgen_local r a b
  have h := twisted_jacobi_of_local_pf_ge (heisVOA1 r) YM hN htr (X (0, a)) (X (0, b)) 1 (m % 2)
    hloc ℓ (fun ℓ' s y hℓ' => pf_generators_nonneg YM htr hvac hgen a b (m % 2) he' ℓ' s y
      (by omega)) x q (m / 2)
  rw [← hq, ← hm] at h
  exact h

end GenJacobi

end Moonshine

end VOA
