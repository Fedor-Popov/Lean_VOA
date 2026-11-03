/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.DongMasonCOne
import VOA.Classification.COne.LatticeNice

/-!
# Lattice reconstruction at `c = 1`

`heisLatticeReconstruction : HeisLatticeReconstruction` (DM-2): a strongly rational VOA `W`
with a unit Heisenberg vector `h` and `ω = ω_h = ½h₍₋₁₎h` is isomorphic to `V_{2m}`, `m ≥ 1`.

## Route
* §1 charged vacuum vectors `IsVacE W h lam u` (`h₍ᵢ₎u = 0`, `i > 0`; `h₍₀₎u = lam u`) and their
  modes on any weak module: `chg_comm`, `chg_vanish`, `chg_recursion`, `chg_rel` (the `W`-analogs
  of the `V_{2m}` lemmas of `LatticeRational2`, valid once `u₍₋₂₎𝟙 = lam h₍₋₁₎u`, `T_vac`).
* §2 `eq_zero_of_smul_eq_zero` (no zero divisors in a simple VOA), `leading`: the top product of
  two nonzero charged vacuum vectors is a nonzero charged vacuum vector, and `lam μ ∈ ℤ`;
  `exists_vacE_neg` (the invariant form pairs opposite charges).
* §3 `vac_le_span_eig` (`h₍₀₎` is semisimple on `Ω`).
* §4 `exists_nonzero_charge`: some charge is nonzero, since otherwise `h₍₀₎ = 0` and the classes
  of `h₍₋₁₎ⁿ𝟙` are independent in `W/C₂(W)` (`not_c2_of_h0`).
* §5 `exists_charge_generator`: the charges form the lattice `ℤ lam`, `lam² = 2m`, `m ≥ 1`.
* §6 `LatData` and the normalized orbit `orb : ℤ → W` (`w₀ = 𝟙`), `LatData.raise`,
  `LatData.lower`, `LatData.vac_le_span` (multiplicity one), `LatData.basis`.
* §7 `voaIsomorphic_of_latData`: the comparison map `M(1) ⊗ Ω ≅ M(1) ⊗ Ω'` (`cmp`) intertwines
  `h` (`cmp_h`) and `w_{±1}` (`cmp_charge`, via `intertw_vac`), hence every state (`homSub`).
* §8 `V2m_latData`: `V_{2m}` carries the data `((e^α)_h, m)` (`V2m_charge_int`).

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne

namespace LatRec

open VOA VOA.VertexOperatorAlgebra Module DMCOne

universe u

variable {𝒲 : Type u} [AddCommGroup 𝒲] [Module ℂ 𝒲] {W : VertexOperatorAlgebra 𝒲}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-! ## §1 Charged vacuum vectors and their modes on any weak module -/

/-- `u` is an `h`-vacuum vector of charge `lam`: `h₍ᵢ₎u = 0` (`i > 0`), `h₍₀₎u = lam u`. -/
structure IsVacE (W : VertexOperatorAlgebra 𝒲) (h : 𝒲) (lam : ℂ) (u : 𝒲) : Prop where
  pos : ∀ i : ℤ, 0 < i → W.smul h i u = 0
  zero : W.smul h 0 u = lam • u

theorem IsVacE.smul_nonneg {h u : 𝒲} {lam : ℂ} (hu : IsVacE W h lam u) {i : ℤ} (hi : 0 ≤ i) :
    W.smul h i u = if i = 0 then lam • u else 0 := by
  rcases eq_or_lt_of_le hi with rfl | hpos
  · rw [if_pos rfl, hu.zero]
  · rw [if_neg (by omega), hu.pos i hpos]

/-- **`h` acts on a charged vector by its charge**: `[h(p), u_(q)] = lam u_(p+q)` on every weak
module. -/
theorem chg_comm (A : WeakModule W M) {h u : 𝒲} {lam : ℂ} (hu : IsVacE W h lam u)
    (p q : ℤ) (x : M) :
    mode (A.YM h) p (mode (A.YM u) q x) - mode (A.YM u) q (mode (A.YM h) p x)
      = lam • mode (A.YM u) (p + q) x := by
  have hJ := A.jacobi h u x 0 p q
  rw [finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul]),
    finsum_eq_single _ (0 : ℤ) (fun i hi => by
      rcases lt_or_ge i 0 with hneg | hnn
      · rw [cbz_apply_neg _ hneg, zero_smul]
      · rw [zero_add, hu.smul_nonneg hnn, if_neg hi, map_zero]
        simp)] at hJ
  simp only [zero_add, add_zero, sub_zero, cbz_zero, negOnePow, mul_one] at hJ
  rw [if_pos (Even.zero : Even (0 : ℤ)), one_smul, one_smul, one_smul,
    hu.smul_nonneg le_rfl, if_pos rfl, map_smul, mode_smul, LinearMap.smul_apply] at hJ
  exact hJ

variable (A : WeakModule W M) {h u : 𝒲} {lam : ℂ}

/-- The top-mode relation (cf. `charge_top`): if `u_(k') ω = 0` for `k' > k`, then
`-(k+1) u_(k) ω = lam · u_(k) h(0) ω`. -/
theorem chg_top
    (hT : W.smul u (-2) W.vacuum = lam • W.smul h (-1) u)
    (ω : M) (hω : ∀ i : ℤ, 0 < i → mode (A.YM h) i ω = 0) (k : ℤ)
    (hk : ∀ k' : ℤ, k < k' → mode (A.YM u) k' ω = 0) :
    (-((k : ℂ) + 1)) • mode (A.YM u) k ω = lam • mode (A.YM u) k (mode (A.YM h) 0 ω) := by
  have hT' := act_T_covariance A u (k + 1) ω
  have hL : W.L (-1) u = W.smul u (-2) W.vacuum := by
    have hc := creation_pow W u 1
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, inv_one, one_smul] at hc
    rw [T_eq_Lneg1, show (-(1 : ℤ) - 1) = -2 from by norm_num] at hc
    exact hc.symm
  rw [hL, hT, WeakModule.act_def, WeakModule.act_def, map_smul, mode_smul,
    LinearMap.smul_apply, show k + 1 - 1 = k by ring] at hT'
  have hI := module_iterate0 A h u ω (-1) (k + 1)
  rw [finsum_eq_single _ (0 : ℤ)] at hI
  · rw [hI, sub_zero, cbz_apply_nonneg _ le_rfl, hk (k + 1 + 0) (by omega), map_zero, zero_sub,
      show (-1 + (k + 1) - 0) = k by ring] at hT'
    have h1 : negOnePow (-1) = -1 := by simp [negOnePow]
    have h0 : negOnePow 0 * gBinom (-1) (Int.toNat 0) = 1 := by simp [negOnePow, gBinom]
    rw [h1, h0, one_smul, neg_one_smul, neg_neg] at hT'
    rw [show (-((k : ℂ) + 1)) = -((k + 1 : ℤ) : ℂ) by push_cast; ring, ← hT']
  · intro i hi
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · rw [cbz_apply_neg _ hneg, mul_zero, zero_smul]
    · rw [hk (k + 1 + i) (by omega), hω i hpos, map_zero, map_zero, smul_zero, sub_zero, smul_zero]

/-- **Vanishing of charge modes** (generalized `charge_vanish`): on a vacuum eigenvector `ω`
(`h(0)ω = μω`), `u_(k) ω = 0` as soon as `(j+1) + lam μ ≠ 0` for every `j ≥ k`. -/
theorem chg_vanish_gen
    (hT : W.smul u (-2) W.vacuum = lam • W.smul h (-1) u)
    (ω : M) (hω : ∀ i : ℤ, 0 < i → mode (A.YM h) i ω = 0)
    (μ : ℂ) (hμ : mode (A.YM h) 0 ω = μ • ω) :
    ∀ k : ℤ, (∀ j : ℤ, k ≤ j → ((j : ℂ) + 1) + lam * μ ≠ 0) → mode (A.YM u) k ω = 0 := by
  obtain ⟨T, hTr⟩ := A.truncation u ω
  have key : ∀ d : ℕ, ∀ k : ℤ, (∀ j : ℤ, k ≤ j → ((j : ℂ) + 1) + lam * μ ≠ 0) → T - d ≤ k →
      mode (A.YM u) k ω = 0 := by
    intro d
    induction d with
    | zero => intro k _ hk; exact hTr k (by simpa using hk)
    | succ d ih =>
      intro k hk1 hk2
      by_cases hkd : T - d ≤ k
      · exact ih k hk1 hkd
      · have htop := chg_top A hT ω hω k (fun k' hk' =>
          ih k' (fun j hj => hk1 j (by omega)) (by push_cast at hk2 ⊢; omega))
        rw [hμ, map_smul, smul_smul] at htop
        have hne : (-((k : ℂ) + 1)) - lam * μ ≠ 0 := by
          intro h0
          apply hk1 k le_rfl
          linear_combination -h0
        have h2 : ((-((k : ℂ) + 1)) - lam * μ) • mode (A.YM u) k ω = 0 := by
          rw [sub_smul, htop, sub_self]
        exact (smul_eq_zero.mp h2).resolve_left hne
  intro k hk
  exact key (T - k).toNat k hk (by omega)

/-- `chg_vanish_gen` at an integral charge product `lam μ = -N₁`: `u_(k) ω = 0` for `k ≥ N₁`. -/
theorem chg_vanish
    (hT : W.smul u (-2) W.vacuum = lam • W.smul h (-1) u)
    (ω : M) (hω : ∀ i : ℤ, 0 < i → mode (A.YM h) i ω = 0)
    (μ : ℂ) (hμ : mode (A.YM h) 0 ω = μ • ω) (N₁ : ℤ) (hN : lam * μ = -N₁) :
    ∀ k : ℤ, N₁ ≤ k → mode (A.YM u) k ω = 0 := by
  intro k hk
  refine chg_vanish_gen A hT ω hω μ hμ k fun j hj h0 => ?_
  rw [hN] at h0
  have h' : ((j + 1 - N₁ : ℤ) : ℂ) = 0 := by push_cast; linear_combination h0
  have := Int.cast_eq_zero.mp h'
  omega

/-- The top charge vector is a vacuum eigenvector of charge `μ + lam`. -/
theorem chg_top_vac (hu : IsVacE W h lam u)
    (hT : W.smul u (-2) W.vacuum = lam • W.smul h (-1) u)
    (ω : M) (hω : ∀ i : ℤ, 0 < i → mode (A.YM h) i ω = 0)
    (μ : ℂ) (hμ : mode (A.YM h) 0 ω = μ • ω) (N₁ : ℤ) (hN : lam * μ = -N₁) :
    (∀ i : ℤ, 0 < i → mode (A.YM h) i (mode (A.YM u) (N₁ - 1) ω) = 0)
      ∧ mode (A.YM h) 0 (mode (A.YM u) (N₁ - 1) ω) = (μ + lam) • mode (A.YM u) (N₁ - 1) ω := by
  have hv := chg_vanish A hT ω hω μ hμ N₁ hN
  constructor
  · intro i hi
    have h := chg_comm A hu i (N₁ - 1) ω
    rw [hω i hi, map_zero, sub_zero, hv (i + (N₁ - 1)) (by omega), smul_zero] at h
    exact h
  · have h := chg_comm A hu 0 (N₁ - 1) ω
    simp only [zero_add] at h
    rw [hμ, map_smul, sub_eq_iff_eq_add] at h
    rw [h, add_smul, add_comm]

/-- **The charge recursion** (cf. `charge_recursion`):
`(-n - lam μ) u_(n-1) ω = lam ∑_{i ≥ 0} h(-1-i) u_(n+i) ω`. -/
theorem chg_recursion
    (hT : W.smul u (-2) W.vacuum = lam • W.smul h (-1) u)
    (ω : M) (hω : ∀ i : ℤ, 0 < i → mode (A.YM h) i ω = 0)
    (μ : ℂ) (hμ : mode (A.YM h) 0 ω = μ • ω) (n : ℤ) :
    (-(n : ℂ) - lam * μ) • mode (A.YM u) (n - 1) ω
      = lam • ∑ᶠ i : ℤ, (if 0 ≤ i then
          mode (A.YM h) (-1 - i) (mode (A.YM u) (n + i) ω) else 0) := by
  have hT' := act_T_covariance A u n ω
  have hL : W.L (-1) u = W.smul u (-2) W.vacuum := by
    have hc := creation_pow W u 1
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, inv_one, one_smul] at hc
    rw [T_eq_Lneg1, show (-(1 : ℤ) - 1) = -2 from by norm_num] at hc
    exact hc.symm
  rw [hL, hT, WeakModule.act_def, WeakModule.act_def, map_smul, mode_smul,
    LinearMap.smul_apply] at hT'
  have hI := module_iterate0 A h u ω (-1) n
  obtain ⟨Te, hTe⟩ := A.truncation u ω
  set g : ℤ → M := fun i => if 0 ≤ i then mode (A.YM h) (-1 - i) (mode (A.YM u) (n + i) ω) else 0
  set b : ℤ → M := fun i => if i = 0 then μ • mode (A.YM u) (n - 1) ω else 0
  have hfg : ∀ i : ℤ, (negOnePow i * cbz (-1) i) •
      (mode (A.YM h) (-1 - i) (mode (A.YM u) (n + i) ω)
        - negOnePow (-1) • mode (A.YM u) (-1 + n - i) (mode (A.YM h) i ω)) = g i + b i := by
    intro i
    rcases lt_or_ge i 0 with hneg | hnn
    · rw [cbz_apply_neg _ hneg, mul_zero, zero_smul]
      simp [g, b, show ¬ 0 ≤ i by omega, show i ≠ 0 by omega]
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = k := ⟨i.toNat, by omega⟩
      have hcoef : negOnePow (k : ℤ) * cbz (-1) (k : ℤ) = 1 := by
        rw [negOnePow_natCast, cbz_apply_nonneg _ (by omega), Int.toNat_natCast, gBinom_neg_one,
          ← mul_pow]
        norm_num
      have h1 : negOnePow (-1) = -1 := by simp [negOnePow]
      rw [hcoef, one_smul, h1, neg_one_smul, sub_neg_eq_add]
      simp only [g, b, if_pos hnn]
      congr 1
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        simp only [Nat.cast_zero, if_true, hμ, map_smul, sub_zero]
        rw [show -1 + n = n - 1 by ring]
      · rw [hω k (by exact_mod_cast hk), map_zero, if_neg (by omega)]
  have hgfin : (Function.support g).Finite := by
    refine (Set.finite_Icc (0 : ℤ) (Te - n)).subset fun i hi => ?_
    rw [Function.mem_support] at hi
    simp only [g] at hi
    split_ifs at hi with h0
    · refine ⟨h0, ?_⟩
      by_contra hlt
      exact hi (by rw [hTe (n + i) (by omega), map_zero])
    · exact absurd rfl hi
  have hbfin : (Function.support b).Finite :=
    (Set.finite_singleton (0 : ℤ)).subset fun i hi => by
      rw [Function.mem_support] at hi
      simp only [b] at hi
      split_ifs at hi with h0
      · exact h0
      · exact absurd rfl hi
  rw [show (fun i : ℤ => (negOnePow i * cbz (-1) i) •
      (mode (A.YM h) (-1 - i) (mode (A.YM u) (n + i) ω)
        - negOnePow (-1) • mode (A.YM u) (-1 + n - i) (mode (A.YM h) i ω))) = fun i => g i + b i
      from funext hfg, finsum_add_distrib hgfin hbfin,
      finsum_eq_single b 0 (fun i hi => by simp only [b]; exact if_neg hi)] at hI
  simp only [b, if_pos rfl] at hI
  rw [hI, smul_add, smul_smul] at hT'
  rw [sub_smul, ← hT', add_sub_cancel_right]

/-- **The pairing relation** (cf. `charge_rel`, Jacobi only): if `u_(ℓ) v = c 𝟙`,
`u_(ℓ+i) v = 0` (`i > 0`), `u_(k) ω = 0` for `k ≥ -N` and `v_(k) ω = 0` for `k ≥ N`, then
`u_(ℓ-N) v_(N-1) ω = c ω`. -/
theorem chg_rel (u v : 𝒲) (ω : M) (ℓ N : ℤ) (c : ℂ) (huv : W.smul u ℓ v = c • W.vacuum)
    (huv' : ∀ i : ℤ, 0 < i → W.smul u (ℓ + i) v = 0)
    (hu : ∀ k : ℤ, -N ≤ k → mode (A.YM u) k ω = 0)
    (hv : ∀ k : ℤ, N ≤ k → mode (A.YM v) k ω = 0) :
    mode (A.YM u) (ℓ - N) (mode (A.YM v) (N - 1) ω) = c • ω := by
  have hJ := A.jacobi u v ω ℓ (-N) (N - 1)
  rw [finsum_eq_single _ (0 : ℤ), finsum_eq_single _ (0 : ℤ)] at hJ
  · rw [hu (-N + 0) (by omega), map_zero, smul_zero, sub_zero, cbz_apply_nonneg _ le_rfl,
      cbz_apply_nonneg _ le_rfl, add_zero, sub_zero, sub_zero, add_zero,
      show -N + (N - 1) = -1 by ring, huv, map_smul, A.vacuum_YM, mode_smul, mode_one] at hJ
    simp only [negOnePow, gBinom, Finset.range_zero, Finset.prod_empty, Nat.factorial_zero,
      Nat.cast_one, div_one, Int.toNat_zero, mul_one, one_smul, LinearMap.smul_apply] at hJ
    rw [if_pos (Even.zero : Even (0 : ℤ)), one_smul] at hJ
    rw [show ℓ + -N = ℓ - N by ring] at hJ
    rw [hJ]
    simp
  · intro i hi
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · rw [cbz_apply_neg _ hneg, zero_smul]
    · rw [huv' i hpos]; simp
  · intro i hi
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · rw [cbz_apply_neg _ hneg, mul_zero, zero_smul]
    · rw [hv (N - 1 + i) (by omega), hu (-N + i) (by omega), map_zero, map_zero, smul_zero,
        sub_zero, smul_zero]

/-! ## §2 The vacuum space of `W` when `ω = ½ h₍₋₁₎h` -/

section VacSpace

variable {h : 𝒲}

/-- With `ω = ω_h`, a charged vacuum vector satisfies `L₋₁u = lam h₍₋₁₎u`, i.e.
`u₍₋₂₎𝟙 = lam h₍₋₁₎u`. -/
theorem T_vac (hω : W.conformalVector = omegaH W h) {u : 𝒲} {lam : ℂ} (hu : IsVacE W h lam u) :
    W.smul u (-2) W.vacuum = lam • W.smul h (-1) u := by
  have hc := creation_pow W u 1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, inv_one, one_smul] at hc
  rw [show (-1 - 1 : ℤ) = -2 by norm_num, T_eq_Lneg1, W.L_def, hω, omegaH, map_smul,
    mode_smul, LinearMap.smul_apply, show (-1 : ℤ) + 1 = 0 by norm_num, ← PreVertexAlgebra.smul_def,
    VOA.VertexOperatorAlgebra.mode_iterate W h h (-1) 0 u] at hc
  rw [finsum_eq_single _ 0 (fun i hi => by
    rw [hu.pos _ (by omega), W.smul_zero_right, hu.pos _ (by omega), W.smul_zero_right, smul_zero,
      sub_zero, smul_zero])] at hc
  rw [hc]
  simp only [pow_zero, gBinom, Finset.range_zero, Finset.prod_empty, Nat.factorial_zero,
    Nat.cast_one, div_one, mul_one, one_smul, Nat.cast_zero, sub_zero, add_zero, hu.zero,
    W.smul_smul_right]
  rw [show ((-1 : ℂ) ^ (-1 : ℤ)) = -1 by norm_num, neg_one_smul, sub_neg_eq_add, smul_add,
    ← add_smul]
  module

/-- **Vertex operator algebras have no zero divisors** (Dong–Lepowsky, Prop. 11.9): in a simple
VOA, `Y(u,z)v = 0` with `v ≠ 0` forces `u = 0`.  The annihilator `{x : u₍ₖ₎x = 0 ∀k}` is an ideal
(Jacobi identity with `ℓ ≫ 0`, downward induction on the mode of the inserted field). -/
theorem eq_zero_of_smul_eq_zero (hS : W.IsSimple) {u v : 𝒲} (huv : ∀ k : ℤ, W.smul u k v = 0)
    (hv : v ≠ 0) : u = 0 := by
  let K : Submodule ℂ 𝒲 :=
    { carrier := {x | ∀ k : ℤ, W.smul u k x = 0}
      add_mem' := by
        intro a b ha hb k
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [PreVertexAlgebra.smul_def, map_add, ← PreVertexAlgebra.smul_def, ← PreVertexAlgebra.smul_def,
          ha, hb, add_zero]
      zero_mem' := by intro k; simp
      smul_mem' := by
        intro c a ha k
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [W.smul_smul_right, ha, smul_zero] }
  have hideal : W.IsIdeal K := by
    intro a x n hx
    obtain ⟨L, hL⟩ := W.regularity u a
    obtain ⟨T, hT⟩ := W.regularity a x
    set ℓ : ℤ := max L 0 with hℓ
    have key : ∀ d : ℕ, ∀ j : ℤ, W.smul u j (W.smul a (T - d) x) = 0 := by
      intro d
      induction d using Nat.strong_induction_on with
      | _ d IH =>
      intro j
      have hJ := W.jacobi u a x ℓ (j - ℓ) (T - d)
      have hR : (∑ᶠ i : ℤ, cbz (j - ℓ) i • W.smul (W.smul u (ℓ + i) a) (j - ℓ + (T - d) - i) x) = 0 := by
        refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
        rcases lt_or_ge i 0 with hneg | hnn
        · rw [cbz_apply_neg _ hneg, zero_smul]
        · have : W.smul u (ℓ + i) a = 0 := hL _ (by omega)
          rw [this, W.smul_zero_left, smul_zero]
      rw [hR, finsum_eq_single _ (0 : ℤ)] at hJ
      · rw [hx (j - ℓ + 0), W.smul_zero_right, smul_zero, sub_zero, cbz_apply_nonneg _ le_rfl,
          show ℓ + (j - ℓ) - 0 = j by ring, add_zero] at hJ
        simp only [negOnePow, gBinom, Finset.range_zero, Finset.prod_empty, Nat.factorial_zero,
          Nat.cast_one, div_one, Int.toNat_zero, mul_one] at hJ
        rw [if_pos (Even.zero : Even (0 : ℤ)), one_smul] at hJ
        exact hJ
      · intro i hi
        rcases lt_or_gt_of_ne hi with hneg | hpos
        · rw [cbz_apply_neg _ hneg, mul_zero, zero_smul]
        · rw [hx (j - ℓ + i), W.smul_zero_right, smul_zero, sub_zero]
          by_cases hid : (i : ℤ) ≤ d
          · have := IH (d - i.toNat) (by omega) (ℓ + (j - ℓ) - i)
            rw [show T - ((d - i.toNat : ℕ) : ℤ) = T - d + i by omega] at this
            rw [this, smul_zero]
          · have : W.smul a (T - d + i) x = 0 := hT _ (by omega)
            rw [this, W.smul_zero_right, smul_zero]
    intro k
    by_cases hn : T ≤ n
    · have : W.smul a n x = 0 := hT n hn
      rw [this, W.smul_zero_right]
    · have := key (T - n).toNat k
      rwa [show T - ((T - n).toNat : ℤ) = n by omega] at this
  rcases hS.2 K hideal with hK | hK
  · exact absurd ((Submodule.mem_bot ℂ).mp (hK ▸ (huv : v ∈ K))) hv
  · have h1 : W.vacuum ∈ K := hK ▸ Submodule.mem_top
    have := h1 (-1)
    rwa [W.smul_vacuum_neg_one] at this

/-- If the top charge mode vanishes, all charge modes vanish (downward `chg_recursion`). -/
theorem chg_all_zero (A : WeakModule W M) {u : 𝒲} {lam : ℂ}
    (hT : W.smul u (-2) W.vacuum = lam • W.smul h (-1) u)
    (ω : M) (hω : ∀ i : ℤ, 0 < i → mode (A.YM h) i ω = 0)
    (μ : ℂ) (hμ : mode (A.YM h) 0 ω = μ • ω) (N₁ : ℤ) (hN : lam * μ = -N₁)
    (htop : mode (A.YM u) (N₁ - 1) ω = 0) : ∀ k : ℤ, mode (A.YM u) k ω = 0 := by
  have hv := chg_vanish A hT ω hω μ hμ N₁ hN
  have key : ∀ d : ℕ, mode (A.YM u) (N₁ - 1 - d) ω = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d IH =>
    rcases d with _ | d
    · simpa using htop
    · have hrec := chg_recursion A hT ω hω μ hμ (N₁ - 1 - d)
      rw [hN, show N₁ - 1 - (d : ℤ) - 1 = N₁ - 1 - ((d + 1 : ℕ) : ℤ) by push_cast; ring] at hrec
      have hsum : (∑ᶠ i : ℤ, (if 0 ≤ i then
          mode (A.YM h) (-1 - i) (mode (A.YM u) (N₁ - 1 - d + i) ω) else 0)) = 0 := by
        refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
        split_ifs with hi
        · by_cases hid : i ≤ d
          · have := IH (d - i.toNat) (by omega)
            rw [show N₁ - 1 - ((d - i.toNat : ℕ) : ℤ) = N₁ - 1 - d + i by omega] at this
            rw [this, map_zero]
          · rw [hv _ (by omega), map_zero]
        · rfl
      rw [hsum, smul_zero] at hrec
      have hne : (-((N₁ - 1 - d : ℤ) : ℂ) - -(N₁ : ℂ)) ≠ 0 := by
        have : (-((N₁ - 1 - d : ℤ) : ℂ) - -(N₁ : ℂ)) = ((d + 1 : ℕ) : ℂ) := by push_cast; ring
        rw [this]; exact_mod_cast Nat.succ_ne_zero d
      exact (smul_eq_zero.mp hrec).resolve_left hne
  intro k
  by_cases hk : N₁ ≤ k
  · exact hv k hk
  · have := key (N₁ - 1 - k).toNat
    rwa [show N₁ - 1 - ((N₁ - 1 - k).toNat : ℤ) = k by omega] at this

/-- **The leading product of two charged vacuum vectors.**  In a simple `W` with `ω = ω_h`, for
nonzero `u ∈ Ω_lam`, `v ∈ Ω_μ`: `lam μ = -N₁` is an integer, `u₍ₖ₎v = 0` for `k ≥ N₁`, and
`u₍N₁₋₁₎v` is a **nonzero** vacuum vector of charge `lam + μ`. -/
theorem leading (hS : W.IsSimple) (hω : W.conformalVector = omegaH W h) {u v : 𝒲} {lam μ : ℂ}
    (hu : IsVacE W h lam u) (hv : IsVacE W h μ v) (hu0 : u ≠ 0) (hv0 : v ≠ 0) :
    ∃ N₁ : ℤ, lam * μ = -N₁ ∧ (∀ k : ℤ, N₁ ≤ k → W.smul u k v = 0) ∧
      W.smul u (N₁ - 1) v ≠ 0 ∧ IsVacE W h (lam + μ) (W.smul u (N₁ - 1) v) := by
  have hT := T_vac hω hu
  set A := adjointWeakModule W
  have hvA : ∀ i : ℤ, 0 < i → mode (A.YM h) i v = 0 := fun i hi => hv.pos i hi
  have hμA : mode (A.YM h) 0 v = μ • v := hv.zero
  by_cases hint : ∃ N₁ : ℤ, lam * μ = -N₁
  · obtain ⟨N₁, hN⟩ := hint
    refine ⟨N₁, hN, fun k hk => chg_vanish A hT v hvA μ hμA N₁ hN k hk, fun h0 => hu0 ?_, ?_⟩
    · exact eq_zero_of_smul_eq_zero hS (fun k => chg_all_zero A hT v hvA μ hμA N₁ hN h0 k) hv0
    · obtain ⟨h1, h2⟩ := chg_top_vac A hu hT v hvA μ hμA N₁ hN
      exact ⟨h1, by rw [add_comm]; exact h2⟩
  · exfalso
    refine hu0 (eq_zero_of_smul_eq_zero hS (fun k => ?_) hv0)
    refine chg_vanish_gen A hT v hvA μ hμA k fun j _ h0 => hint ⟨j + 1, ?_⟩
    push_cast; linear_combination h0

/-- Charge-zero vacuum vectors are multiples of `𝟙` (the commutant is trivial). -/
theorem vacE_zero (hω : W.conformalVector = omegaH W h) {x : 𝒲} (hx : IsVacE W h 0 x) :
    x ∈ ℂ ∙ W.vacuum := by
  refine commutant_le_of_conformal_eq hω (mem_commutant.mpr fun n hn => ?_)
  rw [hx.smul_nonneg hn]
  split_ifs <;> simp

theorem vacE_vacuum (h : 𝒲) : IsVacE W h 0 W.vacuum :=
  ⟨fun i hi => W.smul_vacuum_nonneg h hi.le, by rw [W.smul_vacuum_nonneg h le_rfl, zero_smul]⟩

/-- A nonzero homogeneous `h₍₀₎`-eigenvector yields a nonzero vacuum vector of the same charge
(lower it with the annihilation modes as long as possible). -/
theorem exists_vacE_of_eigen (hh : IsHeisVector W h) (c : ℂ) :
    ∀ (n : ℕ) (y : 𝒲), y ∈ W.grading n → y ≠ 0 → W.smul h 0 y = c • y →
      ∃ z, z ≠ 0 ∧ IsVacE W h c z := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro y hy hy0 hyc
  by_cases hall : ∀ i : ℤ, 0 < i → W.smul h i y = 0
  · exact ⟨y, hy0, hall, hyc⟩
  · push Not at hall
    obtain ⟨i, hi, hne⟩ := hall
    have hmem : W.smul h i y ∈ W.grading ((n : ℤ) - i) := heis_mode_mem hh hy i
    rcases lt_or_ge ((n : ℤ) - i) 0 with hneg | hnn
    · rw [W.positivity _ hneg, Submodule.mem_bot] at hmem
      exact absurd hmem hne
    · refine IH ((n : ℤ) - i).toNat (by omega) (W.smul h i y)
        (by rwa [Int.toNat_of_nonneg hnn]) hne ?_
      have hc := DMCOne.heis_comm hh 0 i y
      rw [show (if (0 : ℤ) + i = 0 then ((0 : ℤ) : ℂ) else 0) = 0 by split_ifs <;> simp,
        zero_smul, sub_eq_zero] at hc
      rw [hc, hyc, W.smul_smul_right]

/-- `(h₍₀₎a|b) = -(a|h₍₀₎b)` for a fully invariant form (`h` primary of weight one). -/
theorem form_h0 (hW : StronglyRational W) (hh : IsHeisVector W h) {B : InvariantForm W}
    (hB : B.IsFullyInvariant) (a b : 𝒲) :
    B.form (W.smul h 0 a) b = -B.form a (W.smul h 0 b) := by
  rw [hB 1 h hh.mem 0 a b]
  have hL1 : W.L 1 h = 0 := hW.L_one_grading_one_eq_zero hh.mem
  simp [Finset.sum_range_succ, hL1]

/-- **Charges come in opposite pairs.**  If `W` is strongly rational and `x ∈ Wₙ` is a nonzero
`h₍₀₎`-eigenvector with eigenvalue `lam`, then `Wₙ` has a nonzero eigenvector with eigenvalue
`-lam` (the invariant form pairs the two eigenspaces, and is nondegenerate). -/
theorem exists_neg_eigen (hW : StronglyRational W) (hh : IsHeisVector W h) {x : 𝒲} (hx0 : x ≠ 0)
    {n : ℤ} (hxn : x ∈ W.grading n) {lam : ℂ} (hx : W.smul h 0 x = lam • x) :
    ∃ y ∈ W.grading n, y ≠ 0 ∧ W.smul h 0 y = (-lam) • y := by
  by_contra hcon
  push Not at hcon
  obtain ⟨B, hBf, hrad⟩ := hW.selfDual
  haveI : FiniteDimensional ℂ (W.grading n) := W.finrank n
  set g : 𝒲 →ₗ[ℂ] 𝒲 := mode (W.Y h) 0 + lam • LinearMap.id with hg
  have hmap : ∀ y ∈ W.grading n, g y ∈ W.grading n := by
    intro y hy
    simp only [hg, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    refine add_mem ?_ (Submodule.smul_mem _ _ hy)
    have := heis_mode_mem hh hy 0
    rwa [sub_zero] at this
  set f := g.restrict hmap
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    have hy' : W.smul h 0 (y : 𝒲) + lam • (y : 𝒲) = 0 := by
      have := congrArg Subtype.val hy
      simpa [f, hg, LinearMap.restrict_apply, PreVertexAlgebra.smul_def] using this
    by_contra hy0
    have hy0' : (y : 𝒲) ≠ 0 := fun h0 => hy0 (Subtype.ext h0)
    exact hcon y y.2 hy0' (by rw [neg_smul, ← sub_eq_zero, sub_neg_eq_add]; exact hy')
  have hsurj : Function.Surjective f := LinearMap.injective_iff_surjective.mp hinj
  have hzero : ∀ b ∈ W.grading n, B.form x b = 0 := by
    intro b hb
    obtain ⟨c, hc⟩ := hsurj ⟨b, hb⟩
    have hb' : b = W.smul h 0 (c : 𝒲) + lam • (c : 𝒲) := by
      exact (congrArg Subtype.val hc).symm
    have hadj := form_h0 hW hh hBf x c
    rw [hx, map_smul, LinearMap.smul_apply, smul_eq_mul] at hadj
    rw [hb', map_add, map_smul, smul_eq_mul]
    linear_combination hadj
  apply hx0
  have hmem : x ∈ InvariantForm.leftRadical B := by
    rw [InvariantForm.mem_leftRadical]
    refine LinearMap.ext fun b => ?_
    simp only [LinearMap.zero_apply]
    have hbtop : b ∈ ⨆ i, W.grading i := by
      rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
    refine Submodule.iSup_induction W.grading (motive := fun b => B.form x b = 0) hbtop ?_ ?_ ?_
    · intro i y hy
      rcases eq_or_ne n i with rfl | hne
      · exact hzero y hy
      · exact InvariantForm.orthogonal_of_ne B hne hxn hy
    · exact map_zero _
    · intro y z hy hz; rw [map_add, hy, hz, add_zero]
  rw [hrad, Submodule.mem_bot] at hmem
  exact hmem

/-- **Negation of charges**: a nonzero vacuum vector of charge `lam` forces one of charge `-lam`. -/
theorem exists_vacE_neg (hW : StronglyRational W) (hh : IsHeisVector W h)
    (hω : W.conformalVector = omegaH W h) {x : 𝒲} {lam : ℂ} (hx : IsVacE W h lam x)
    (hx0 : x ≠ 0) : ∃ y, y ≠ 0 ∧ IsVacE W h (-lam) y := by
  obtain ⟨n, -, hxn⟩ := vac_charge_sq hω hx.pos hx0 hx.zero
  obtain ⟨y, hy, hy0, hyc⟩ := exists_neg_eigen hW hh hx0 hxn hx.zero
  exact exists_vacE_of_eigen hh (-lam) n y hy hy0 hyc

end VacSpace

/-! ## §3 Homogeneous components and the eigen-decomposition of the vacuum space -/

section Homog

variable {h : 𝒲}

/-- Every vacuum vector is a finite sum of homogeneous vacuum vectors. -/
theorem vac_homog (hh : IsHeisVector W h) {x : 𝒲} (hx : x ∈ (heisRep hh).vac) :
    ∃ s : Finset ℤ, ∃ c : ℤ → 𝒲, x = ∑ n ∈ s, c n ∧
      ∀ n, c n ∈ W.grading n ∧ c n ∈ (heisRep hh).vac := by
  classical
  letI : DirectSum.Decomposition W.grading := W.isInternal.chooseDecomposition
  refine ⟨(DirectSum.decompose W.grading x).support,
    fun n => (DirectSum.decompose W.grading x n : 𝒲),
    (DirectSum.sum_support_decompose W.grading x).symm,
    fun n => ⟨(DirectSum.decompose W.grading x n).2, ?_⟩⟩
  rw [HeisSvN.HeisRep.mem_vac] at hx ⊢
  intro i hi
  have key : ((DirectSum.decompose W.grading (mode (W.Y h) i x)) (n - i) : 𝒲)
      = mode (W.Y h) i (DirectSum.decompose W.grading x n) := by
    have hF : ∀ (t : Finset ℤ) (f : ℤ → 𝒲), ((DirectSum.decompose W.grading (∑ k ∈ t, f k)) (n - i) : 𝒲)
        = ∑ k ∈ t, ((DirectSum.decompose W.grading (f k)) (n - i) : 𝒲) := by
      intro t f
      induction t using Finset.induction_on with
      | empty => simp
      | insert a t ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, DirectSum.decompose_add,
          DirectSum.add_apply, Submodule.coe_add, ih]
    conv_lhs => rw [← DirectSum.sum_support_decompose W.grading x]
    rw [map_sum, hF, Finset.sum_eq_single n]
    · exact DirectSum.decompose_of_mem_same _ (heis_mode_mem hh (DirectSum.decompose W.grading x n).2 i)
    · intro k _ hk
      exact DirectSum.decompose_of_mem_ne _ (heis_mode_mem hh (DirectSum.decompose W.grading x k).2 i)
        (by omega)
    · intro hn
      rw [DFinsupp.notMem_support_iff.mp hn]
      simp
  have hx' := hx i hi
  rw [heisRep_a] at hx'
  change mode (W.Y h) i _ = 0
  rw [← key, hx']
  simp

/-- A homogeneous vacuum vector is a sum of (at most two) charged vacuum vectors. -/
theorem vac_homog_split (hh : IsHeisVector W h) (hω : W.conformalVector = omegaH W h) {n : ℤ}
    {x : 𝒲} (hxn : x ∈ W.grading n) (hx : x ∈ (heisRep hh).vac) :
    x ∈ Submodule.span ℂ {y | ∃ c, IsVacE W h c y} := by
  have hxv : ∀ k : ℤ, 0 < k → W.smul h k x = 0 := fun k hk => (heisRep hh).mem_vac.mp hx k hk
  have h0v : W.smul h 0 x ∈ (heisRep hh).vac := (heisRep hh).a_zero_mem_vac hx
  have h0v' : ∀ k : ℤ, 0 < k → W.smul h k (W.smul h 0 x) = 0 :=
    fun k hk => (heisRep hh).mem_vac.mp h0v k hk
  have hsq := h0_sq_on_vac hω hxv hxn
  rcases lt_trichotomy n 0 with hneg | rfl | hpos
  · rw [W.positivity n hneg, Submodule.mem_bot] at hxn
    rw [hxn]; exact Submodule.zero_mem _
  · rw [W.vacuum_grade] at hxn
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxn
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, vacE_vacuum h⟩)
  · obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq ((2 : ℂ) * n) (by norm_num : 0 < 2)
    have hs0 : s ≠ 0 := by
      rintro rfl
      have : (2 : ℂ) * n ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast hpos.ne')
      exact this (by rw [← hs]; ring)
    have hsq' : W.smul h 0 (W.smul h 0 x) = (s ^ 2) • x := by rw [hsq, hs]
    set xp := (1 / 2 : ℂ) • (x + s⁻¹ • W.smul h 0 x)
    set xm := (1 / 2 : ℂ) • (x - s⁻¹ • W.smul h 0 x)
    have hxpm : x = xp + xm := by simp only [xp, xm]; module
    have hpv : ∀ k : ℤ, 0 < k → W.smul h k xp = 0 := by
      intro k hk
      simp only [xp, W.smul_smul_right, PreVertexAlgebra.smul_def, map_add, map_smul]
      simp only [← PreVertexAlgebra.smul_def, hxv k hk, h0v' k hk]; simp
    have hmv : ∀ k : ℤ, 0 < k → W.smul h k xm = 0 := by
      intro k hk
      simp only [xm, W.smul_smul_right, PreVertexAlgebra.smul_def, map_sub, map_smul]
      simp only [← PreVertexAlgebra.smul_def, hxv k hk, h0v' k hk]; simp
    have hpe : W.smul h 0 xp = s • xp := by
      simp only [xp, W.smul_smul_right, PreVertexAlgebra.smul_def, map_add, map_smul]
      simp only [← PreVertexAlgebra.smul_def, hsq', smul_smul]
      have e1 : s⁻¹ * s ^ 2 = s := by field_simp
      rw [e1]
      match_scalars <;> field_simp
    have hme : W.smul h 0 xm = (-s) • xm := by
      simp only [xm, W.smul_smul_right, PreVertexAlgebra.smul_def, map_sub, map_smul]
      simp only [← PreVertexAlgebra.smul_def, hsq', smul_smul]
      have e1 : s⁻¹ * s ^ 2 = s := by field_simp
      rw [e1]
      match_scalars <;> field_simp
    rw [hxpm]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨s, hpv, hpe⟩)
      (Submodule.subset_span ⟨-s, hmv, hme⟩)

/-- **`h₍₀₎` is semisimple on the vacuum space**: `Ω` is spanned by charged vacuum vectors. -/
theorem vac_le_span_eig (hh : IsHeisVector W h) (hω : W.conformalVector = omegaH W h) :
    (heisRep hh).vac ≤ Submodule.span ℂ {y | ∃ c, IsVacE W h c y} := by
  intro x hx
  obtain ⟨s, c, rfl, hc⟩ := vac_homog hh hx
  exact Submodule.sum_mem _ fun n _ => vac_homog_split hh hω (hc n).1 (hc n).2

end Homog

/-! ## §4 Some charge is nonzero: the Heisenberg VOA is not `C₂`-cofinite -/

section C2

variable {h : 𝒲}

/-- If every nonzero vacuum vector has charge zero, then `h₍₀₎ = 0` on all of `W`. -/
theorem h0_eq_zero_of_charges (hh : IsHeisVector W h) (hω : W.conformalVector = omegaH W h)
    (hall : ∀ (c : ℂ) (x : 𝒲), IsVacE W h c x → x ≠ 0 → c = 0) (x : 𝒲) : W.smul h 0 x = 0 := by
  set H := heisRep hh
  let S : Submodule ℂ 𝒲 := LinearMap.ker (mode (W.Y h) 0)
  have hS : S = ⊤ := by
    refine H.eq_top_of_vac_le S ?_ ?_
    · refine le_trans (vac_le_span_eig hh hω) (Submodule.span_le.mpr ?_)
      rintro y ⟨c, hy⟩
      change mode (W.Y h) 0 y = 0
      by_cases hy0 : y = 0
      · rw [hy0, map_zero]
      have := hall c y hy hy0
      subst this
      have h2 := hy.zero
      rw [zero_smul] at h2
      exact h2
    · intro n _ y hy
      change mode (W.Y h) 0 (H.a n y) = 0
      have hy' : H.a 0 y = 0 := hy
      rw [← heisRep_a hh 0, H.a_zero_comm, hy', map_zero]
  have : x ∈ S := hS ▸ Submodule.mem_top
  exact this

/-- With `h₍₀₎ = 0`, `h₍₁₎` preserves `O₂ = C₂(W)` (it is a derivation of the `(-2)`-product). -/
theorem h1_mem_O₂ (h0 : ∀ x, W.smul h 0 x = 0) {y : 𝒲} (hy : y ∈ O₂ W) :
    W.smul h 1 y ∈ O₂ W := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, v, rfl⟩ := hy
    have hJ := W.jacobi h u v 0 1 (-2)
    rw [finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul]),
      finsum_eq_single _ (1 : ℤ) (fun i hi => by
        rcases lt_or_ge i 0 with hneg | hnn
        · rw [cbz_apply_neg _ hneg, zero_smul]
        · rcases eq_or_lt_of_le hnn with rfl | hpos
          · rw [zero_add, h0, W.smul_zero_left, smul_zero]
          · rw [cbz_apply_nonneg _ hnn, show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl,
              gBinom_natCast_eq_zero (by omega), zero_smul])] at hJ
    simp only [zero_add, add_zero, sub_zero, cbz_zero, negOnePow, mul_one] at hJ
    rw [if_pos (Even.zero : Even (0 : ℤ)), one_smul, one_smul, cbz_apply_nonneg _ zero_le_one,
      show (1 : ℤ) + -2 - 1 = -2 by norm_num] at hJ
    have hg : gBinom 1 (Int.toNat 1) = 1 := by
      simp [gBinom, Finset.range_one]
    rw [hg, one_smul] at hJ
    rw [show W.smul h 1 (W.smul u (-2) v) = W.smul u (-2) (W.smul h 1 v) + W.smul (W.smul h 1 u) (-2) v
      by rw [← hJ]; abel]
    exact add_mem (Submodule.subset_span ⟨_, _, rfl⟩) (Submodule.subset_span ⟨_, _, rfl⟩)
  | zero => rw [W.smul_zero_right]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [PreVertexAlgebra.smul_def, map_add, ← PreVertexAlgebra.smul_def, ← PreVertexAlgebra.smul_def]
    exact add_mem hx hy
  | smul c x _ hx => rw [W.smul_smul_right]; exact Submodule.smul_mem _ _ hx

/-- `O₂` lies in the positive-weight part of `W`. -/
theorem O₂_le_pos : O₂ W ≤ ⨆ (k : ℤ) (_ : 1 ≤ k), W.grading k := by
  set P := ⨆ (k : ℤ) (_ : 1 ≤ k), W.grading k
  have hgen : ∀ u v : 𝒲, W.smul u (-2) v ∈ P := by
    intro u v
    have hutop : u ∈ ⨆ i, W.grading i := by rw [W.isInternal.submodule_iSup_eq_top]; trivial
    have hvtop : v ∈ ⨆ i, W.grading i := by rw [W.isInternal.submodule_iSup_eq_top]; trivial
    induction hutop using Submodule.iSup_induction' generalizing v with
    | mem i u hu =>
      induction hvtop using Submodule.iSup_induction' with
      | mem j v hv =>
        rcases lt_or_ge i 0 with hi | hi
        · rw [W.positivity i hi, Submodule.mem_bot] at hu
          rw [hu, W.smul_zero_left]; exact P.zero_mem
        rcases lt_or_ge j 0 with hj | hj
        · rw [W.positivity j hj, Submodule.mem_bot] at hv
          rw [hv, W.smul_zero_right]; exact P.zero_mem
        have hmem := W.smul_mem_grading hu hv (-2)
        exact (le_iSup₂_of_le (f := fun (k : ℤ) (_ : 1 ≤ k) => W.grading k) (i + j - -2 - 1)
          (by omega) le_rfl) hmem
      | zero => rw [W.smul_zero_right]; exact P.zero_mem
      | add x y _ _ hx hy =>
        rw [PreVertexAlgebra.smul_def, map_add, ← PreVertexAlgebra.smul_def, ← PreVertexAlgebra.smul_def]
        exact add_mem hx hy
    | zero => rw [W.smul_zero_left]; exact P.zero_mem
    | add x y _ _ hx hy => rw [W.smul_add_left]; exact add_mem (hx v hvtop) (hy v hvtop)
  rw [O₂, Submodule.span_le]
  rintro _ ⟨u, v, rfl⟩
  exact hgen u v

theorem pos_inf_zero {x : 𝒲} (hx : x ∈ ⨆ (k : ℤ) (_ : 1 ≤ k), W.grading k)
    (hx0 : x ∈ W.grading 0) : x = 0 := by
  have hle : (⨆ (k : ℤ) (_ : 1 ≤ k), W.grading k) ≤ ⨆ (k : ℤ) (_ : k ≠ 0), W.grading k :=
    iSup₂_le fun k hk => le_iSup₂_of_le (f := fun (k : ℤ) (_ : k ≠ 0) => W.grading k) k
      (by omega) le_rfl
  exact (Submodule.disjoint_def.mp (W.isInternal.submodule_iSupIndep (0 : ℤ))) x hx0 (hle hx)

/-- **A VOA with a unit Heisenberg vector whose zero mode vanishes is not `C₂`-cofinite**
(the classes of `h₍₋₁₎ⁿ𝟙` are independent in `W/C₂(W)`: `h₍₁₎ᴺ` preserves `C₂(W)`, which lies in
positive weight, and sends `h₍₋₁₎ᴺ𝟙` to `N!·𝟙`). -/
theorem not_c2_of_h0 (hh : IsHeisVector W h) (h0 : ∀ x, W.smul h 0 x = 0)
    (hvac : W.vacuum ≠ 0) : ¬ C2Cofinite W := by
  set A1 : End ℂ 𝒲 := mode (W.Y h) 1
  set Cm : End ℂ 𝒲 := mode (W.Y h) (-1)
  set xs : ℕ → 𝒲 := fun n => (Cm ^ n) W.vacuum
  have hxs : ∀ n : ℕ, xs n ∈ W.grading n := by
    intro n
    induction n with
    | zero => simpa [xs] using (W.vacuum_mem : W.vacuum ∈ W.grading 0)
    | succ n ih =>
      have := heis_mode_mem hh ih (-1)
      simp only [xs, pow_succ', Module.End.mul_apply]
      convert this using 2
  have hA1pow : ∀ (N : ℕ) (k : ℤ) (y : 𝒲), y ∈ W.grading k → (A1 ^ N) y ∈ W.grading (k - N) := by
    intro N
    induction N with
    | zero => intro k y hy; simpa using hy
    | succ N ih =>
      intro k y hy
      rw [pow_succ', Module.End.mul_apply]
      have := heis_mode_mem hh (ih k y hy) 1
      convert this using 2; push_cast; ring
  have hlt : ∀ (N n : ℕ), n < N → (A1 ^ N) (xs n) = 0 := by
    intro N n hn
    have := hA1pow N n (xs n) (hxs n)
    rw [W.positivity _ (by omega), Submodule.mem_bot] at this
    exact this
  have hcomm : ∀ x, A1 (Cm x) = Cm (A1 x) + (1 : ℂ) • x := by
    intro x
    have hc := DMCOne.heis_comm hh 1 (-1) x
    rw [if_pos (by norm_num), Int.cast_one] at hc
    simp only [A1, Cm]
    rw [← PreVertexAlgebra.smul_def, ← PreVertexAlgebra.smul_def, ← PreVertexAlgebra.smul_def,
      ← PreVertexAlgebra.smul_def, ← hc]
    abel
  have hA1vac : A1 W.vacuum = 0 := W.smul_vacuum_nonneg h zero_le_one
  have hstep : ∀ j : ℕ, A1 (xs (j + 1)) = ((j + 1 : ℕ) : ℂ) • xs j := by
    intro j
    have := HeisSvN.B_pow_succ_apply Cm A1 1 hcomm W.vacuum j
    rw [hA1vac, map_zero, zero_add, mul_one] at this
    exact this
  have heq : ∀ N : ℕ, (A1 ^ N) (xs N) = (N.factorial : ℂ) • W.vacuum := by
    intro N
    induction N with
    | zero => simp [xs]
    | succ N ih =>
      rw [pow_succ, Module.End.mul_apply, hstep, map_smul, ih, smul_smul, Nat.factorial_succ]
      push_cast; ring_nf
  have hO : ∀ (N : ℕ) {y : 𝒲}, y ∈ O₂ W → (A1 ^ N) y ∈ O₂ W := by
    intro N
    induction N with
    | zero => intro y hy; simpa using hy
    | succ N ih =>
      intro y hy
      rw [pow_succ', Module.End.mul_apply]
      exact h1_mem_O₂ h0 (ih hy)
  have hli : LinearIndependent ℂ (fun n : ℕ => mk₂ W (xs n)) := by
    rw [linearIndependent_iff]
    intro l hl
    by_contra hne
    have hsupp : l.support.Nonempty := Finsupp.support_nonempty_iff.mpr hne
    set N := l.support.max' hsupp
    set q : 𝒲 := ∑ n ∈ l.support, l n • xs n
    have hq : q ∈ O₂ W := by
      have : mk₂ W q = 0 := by
        rw [Finsupp.linearCombination_apply, Finsupp.sum] at hl
        simp only [q, map_sum, map_smul]
        exact hl
      rwa [mk₂, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    have hAq : (A1 ^ N) q = (l N * (N.factorial : ℂ)) • W.vacuum := by
      simp only [q, map_sum, map_smul]
      rw [Finset.sum_eq_single N]
      · rw [heq, smul_smul]
      · intro n hn hnN
        have : n < N := lt_of_le_of_ne (Finset.le_max' _ _ hn) hnN
        rw [hlt N n this, smul_zero]
      · intro h; exact absurd (Finset.max'_mem _ _) h
    have hz := pos_inf_zero (O₂_le_pos (hO N hq))
      (by rw [hAq]; exact Submodule.smul_mem _ _ W.vacuum_mem)
    rw [hAq, smul_eq_zero] at hz
    rcases hz with hz | hz
    · rcases mul_eq_zero.mp hz with h1 | h1
      · exact (Finsupp.mem_support_iff.mp (Finset.max'_mem _ hsupp)) h1
      · exact Nat.factorial_ne_zero N (by exact_mod_cast h1)
    · exact hvac hz
  intro hfin
  rw [C2Cofinite] at hfin
  haveI : Module.Finite ℂ (A₂ W) := hfin
  haveI hfinite : Finite ℕ := hli.finite
  exact not_finite ℕ

/-- **Some vacuum vector has a nonzero charge** (otherwise `W` would not be `C₂`-cofinite). -/
theorem exists_nonzero_charge (hW : StronglyRational W) (hh : IsHeisVector W h)
    (hω : W.conformalVector = omegaH W h) :
    ∃ (c : ℂ) (x : 𝒲), IsVacE W h c x ∧ x ≠ 0 ∧ c ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact not_c2_of_h0 hh (h0_eq_zero_of_charges hh hω fun c x hx hx0 => hcon c x hx hx0)
    hW.toStronglyFinite.vacuum_ne_zero hW.c2Cofinite

end C2


/-! ## §5 The charge lattice -/

section Lattice

variable {h : 𝒲}

/-- `c` is a **charge** of `W`: some nonzero vacuum vector has `h₍₀₎`-eigenvalue `c`. -/
def IsCharge (W : VertexOperatorAlgebra 𝒲) (h : 𝒲) (c : ℂ) : Prop := ∃ x, x ≠ 0 ∧ IsVacE W h c x

theorem IsVacE.smul {u : 𝒲} {lam : ℂ} (hu : IsVacE W h lam u) (c : ℂ) : IsVacE W h lam (c • u) :=
  ⟨fun i hi => by rw [W.smul_smul_right, hu.pos i hi, smul_zero],
    by rw [W.smul_smul_right, hu.zero, smul_comm]⟩

theorem IsVacE.of_eq {u : 𝒲} {a b : ℂ} (hu : IsVacE W h a u) (hab : a = b) : IsVacE W h b u :=
  hab ▸ hu

/-- `leading` with the integer `N = lam μ` given in advance. -/
theorem leading' (hS : W.IsSimple) (hω : W.conformalVector = omegaH W h) {u v : 𝒲} {a b : ℂ}
    (hu : IsVacE W h a u) (hv : IsVacE W h b v) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (N : ℤ)
    (hN : a * b = N) :
    (∀ k : ℤ, -N ≤ k → W.smul u k v = 0) ∧ W.smul u (-N - 1) v ≠ 0 ∧
      IsVacE W h (a + b) (W.smul u (-N - 1) v) := by
  obtain ⟨N₁, hN₁, h1, h2, h3⟩ := leading hS hω hu hv hu0 hv0
  have : N₁ = -N := by
    have : ((N₁ : ℤ) : ℂ) = ((-N : ℤ) : ℂ) := by push_cast; rw [← hN, hN₁]; ring
    exact_mod_cast this
  subst this
  exact ⟨h1, h2, h3⟩

/-- **The pairing relation for vacuum vectors**: if `u ∈ Ω_a`, `v ∈ Ω_{-a}`, `u₍ℓ₎v = c𝟙` with
the higher products zero, then `u₍ℓ-N₎ v₍N-1₎ ω = c ω` for `ω ∈ Ω_μ`, `N = aμ`. -/
theorem rel_vac (hω : W.conformalVector = omegaH W h) {u v x : 𝒲} {a μ c : ℂ} {ℓ N : ℤ}
    (hu : IsVacE W h a u) (hv : IsVacE W h (-a) v)
    (huv : W.smul u ℓ v = c • W.vacuum) (huv' : ∀ i : ℤ, 0 < i → W.smul u (ℓ + i) v = 0)
    (hx : IsVacE W h μ x) (hN : a * μ = N) :
    W.smul u (ℓ - N) (W.smul v (N - 1) x) = c • x :=
  chg_rel (adjointWeakModule W) u v x ℓ N c huv huv'
    (chg_vanish (adjointWeakModule W) (T_vac hω hu) x hx.pos μ hx.zero (-N)
      (by rw [hN]; push_cast; ring))
    (chg_vanish (adjointWeakModule W) (T_vac hω hv) x hx.pos μ hx.zero N
      (by rw [neg_mul, hN]))

theorem isCharge_zero (hW : StronglyRational W) : IsCharge W h 0 :=
  ⟨W.vacuum, hW.toStronglyFinite.vacuum_ne_zero, vacE_vacuum h⟩

theorem isCharge_add (hW : StronglyRational W) (hω : W.conformalVector = omegaH W h) {a b : ℂ}
    (ha : IsCharge W h a) (hb : IsCharge W h b) : IsCharge W h (a + b) := by
  obtain ⟨u, hu0, hu⟩ := ha
  obtain ⟨v, hv0, hv⟩ := hb
  obtain ⟨N₁, -, -, hne, hvac⟩ := leading hW.simple hω hu hv hu0 hv0
  exact ⟨_, hne, hvac⟩

theorem isCharge_mul (hW : StronglyRational W) (hω : W.conformalVector = omegaH W h) {a b : ℂ}
    (ha : IsCharge W h a) (hb : IsCharge W h b) : ∃ N : ℤ, a * b = N := by
  obtain ⟨u, hu0, hu⟩ := ha
  obtain ⟨v, hv0, hv⟩ := hb
  obtain ⟨N₁, hN, -⟩ := leading hW.simple hω hu hv hu0 hv0
  exact ⟨-N₁, by rw [hN]; push_cast; ring⟩

theorem isCharge_neg (hW : StronglyRational W) (hh : IsHeisVector W h)
    (hω : W.conformalVector = omegaH W h) {a : ℂ} (ha : IsCharge W h a) : IsCharge W h (-a) := by
  obtain ⟨x, hx0, hx⟩ := ha
  obtain ⟨y, hy0, hy⟩ := exists_vacE_neg hW hh hω hx hx0
  exact ⟨y, hy0, hy⟩

theorem isCharge_sq (hω : W.conformalVector = omegaH W h) {a : ℂ} (ha : IsCharge W h a) :
    ∃ n : ℕ, a ^ 2 = 2 * n := by
  obtain ⟨x, hx0, hx⟩ := ha
  obtain ⟨n, hn, -⟩ := vac_charge_sq hω hx.pos hx0 hx.zero
  exact ⟨n, hn⟩

/-- The charges, as an additive subgroup of `ℂ`. -/
def chargeGroup (hW : StronglyRational W) (hh : IsHeisVector W h)
    (hω : W.conformalVector = omegaH W h) : AddSubgroup ℂ where
  carrier := {c | IsCharge W h c}
  add_mem' := isCharge_add hW hω
  zero_mem' := isCharge_zero hW
  neg_mem' := isCharge_neg hW hh hω

/-- **The charge lattice is even of rank one**: it is `ℤ lam` with `lam² = 2m`, `m ≥ 1`. -/
theorem exists_charge_generator (hW : StronglyRational W) (hh : IsHeisVector W h)
    (hω : W.conformalVector = omegaH W h) :
    ∃ (lam : ℂ) (m : ℕ), 1 ≤ m ∧ lam ^ 2 = 2 * m ∧ IsCharge W h lam ∧
      ∀ c, IsCharge W h c → ∃ k : ℤ, c = k * lam := by
  obtain ⟨c₀, x₀, hx₀, hx₀0, hc₀⟩ := exists_nonzero_charge hW hh hω
  have hC0 : IsCharge W h c₀ := ⟨x₀, hx₀0, hx₀⟩
  set Λ := chargeGroup hW hh hω
  let G : AddSubgroup ℤ := (Λ.map (AddMonoidHom.mulRight c₀)).comap (Int.castAddHom ℂ)
  obtain ⟨d, hd⟩ := Int.subgroup_cyclic G
  have hdG : d ∈ G := by rw [hd]; exact AddSubgroup.subset_closure rfl
  obtain ⟨a₀, ha₀, hda⟩ := AddSubgroup.mem_map.mp (AddSubgroup.mem_comap.mp hdG)
  simp only [AddMonoidHom.coe_mulRight, Int.coe_castAddHom] at hda
  have hall : ∀ c, IsCharge W h c → ∃ k : ℤ, c = k * a₀ := by
    intro c hc
    obtain ⟨N, hN⟩ := isCharge_mul hW hω hc hC0
    have hNG : N ∈ G := AddSubgroup.mem_comap.mpr (AddSubgroup.mem_map.mpr ⟨c, hc, by
      simp only [AddMonoidHom.coe_mulRight, Int.coe_castAddHom]; exact hN⟩)
    rw [hd, AddSubgroup.mem_closure_singleton] at hNG
    obtain ⟨k, hk⟩ := hNG
    refine ⟨k, mul_right_cancel₀ hc₀ ?_⟩
    rw [hN, ← hk, smul_eq_mul, mul_assoc, hda]
    push_cast; ring
  have ha₀ne : a₀ ≠ 0 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hall c₀ hC0
    exact hc₀ (by simpa using hk)
  obtain ⟨m, hm⟩ := isCharge_sq hω (show IsCharge W h a₀ from ha₀)
  refine ⟨a₀, m, ?_, hm, ha₀, hall⟩
  by_contra hm0
  have : m = 0 := by omega
  subst this
  simp at hm
  exact ha₀ne hm

end Lattice

/-! ## §6 The charge orbit: a normalized basis of the vacuum space -/

/-- The data of a unit Heisenberg vector with `ω = ω_h` and charge lattice `ℤ lam`, `lam² = 2m`. -/
structure LatData (W : VertexOperatorAlgebra 𝒲) (h : 𝒲) (lam : ℂ) (m : ℕ) : Prop where
  rat : StronglyRational W
  heis : IsHeisVector W h
  omega : W.conformalVector = omegaH W h
  one_le : 1 ≤ m
  sq : lam ^ 2 = 2 * m
  charge : IsCharge W h lam
  all : ∀ c, IsCharge W h c → ∃ k : ℤ, c = k * lam

theorem exists_latData (hW : StronglyRational W) {h : 𝒲} (hh : IsHeisVector W h)
    (hω : W.conformalVector = omegaH W h) : ∃ (lam : ℂ) (m : ℕ), LatData W h lam m := by
  obtain ⟨lam, m, h1, h2, h3, h4⟩ := exists_charge_generator hW hh hω
  exact ⟨lam, m, hW, hh, hω, h1, h2, h3, h4⟩

namespace LatData

variable {h : 𝒲} {lam : ℂ} {m : ℕ} (D : LatData W h lam m)
include D

theorem neg : LatData W h (-lam) m :=
  ⟨D.rat, D.heis, D.omega, D.one_le, by rw [neg_sq]; exact D.sq,
    isCharge_neg D.rat D.heis D.omega D.charge,
    fun c hc => by obtain ⟨k, hk⟩ := D.all c hc; exact ⟨-k, by rw [hk]; push_cast; ring⟩⟩

theorem lam_ne : lam ≠ 0 := by
  intro h0
  have h1 := D.sq
  have h2 := D.one_le
  rw [h0] at h1
  have : (m : ℂ) = 0 := by linear_combination -h1 / 2
  have : m = 0 := by exact_mod_cast this
  omega

theorem sq' : lam * lam = 2 * m := by rw [← D.sq]; ring

/-- A charge-zero vacuum vector is a multiple of the vacuum. -/
theorem vac_zero {x : 𝒲} {a : ℂ} (hx : IsVacE W h a x) (ha : a = 0) : ∃ c : ℂ, x = c • W.vacuum := by
  subst ha
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (vacE_zero D.omega hx)
  exact ⟨c, hc.symm⟩

/-- The normalized pair `w₊ ∈ Ω_lam`, `w₋ ∈ Ω_{-lam}` with `w₋₍₂ₘ₋₁₎w₊ = w₊₍₂ₘ₋₁₎w₋ = 𝟙`. -/
theorem exists_pair : ∃ wp wm : 𝒲, wp ≠ 0 ∧ wm ≠ 0 ∧ IsVacE W h lam wp ∧ IsVacE W h (-lam) wm ∧
    W.smul wm (2 * m - 1) wp = W.vacuum ∧ (∀ i : ℤ, 0 < i → W.smul wm (2 * m - 1 + i) wp = 0) ∧
    W.smul wp (2 * m - 1) wm = W.vacuum ∧ (∀ i : ℤ, 0 < i → W.smul wp (2 * m - 1 + i) wm = 0) := by
  obtain ⟨xp, hxp0, hxp⟩ := D.charge
  obtain ⟨xm, hxm0, hxm⟩ := isCharge_neg D.rat D.heis D.omega D.charge
  have hS := D.rat.simple
  obtain ⟨h1, h2, h3⟩ := leading' hS D.omega hxm hxp hxm0 hxp0 (-(2 * m)) (by
    rw [neg_mul, D.sq']; push_cast; ring)
  rw [neg_neg] at h1 h2 h3
  obtain ⟨c, hc⟩ := D.vac_zero h3 (by ring)
  have hc0 : c ≠ 0 := by rintro rfl; rw [zero_smul] at hc; exact h2 hc
  set wm := c⁻¹ • xm
  have hwm : IsVacE W h (-lam) wm := hxm.smul _
  have hwm0 : wm ≠ 0 := smul_ne_zero (inv_ne_zero hc0) hxm0
  have e1 : W.smul wm (2 * m - 1) xp = W.vacuum := by
    rw [W.smul_smul_left, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have e2 : ∀ i : ℤ, 0 < i → W.smul wm (2 * m - 1 + i) xp = 0 := by
    intro i hi
    rw [W.smul_smul_left, h1 _ (by omega), smul_zero]
  obtain ⟨g1, -, g3⟩ := leading' hS D.omega hxp hwm hxp0 hwm0 (-(2 * m)) (by
    rw [mul_neg, D.sq']; push_cast; ring)
  rw [neg_neg] at g1 g3
  obtain ⟨c', hc'⟩ := D.vac_zero g3 (by ring)
  have hrel := rel_vac D.omega hxp hwm hc'
    (fun i hi => g1 _ (by omega)) hxp (N := 2 * m) (by rw [D.sq']; push_cast; ring)
  rw [show (2 * (m : ℤ) - 1 - 2 * m) = -1 by ring, e1, W.smul_vacuum_neg_one] at hrel
  have hc'1 : c' = 1 := by
    by_contra hne
    have : (1 - c') • xp = 0 := by rw [sub_smul, one_smul, ← hrel, sub_self]
    exact hxp0 ((smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hne)))
  subst hc'1
  rw [one_smul] at hc'
  exact ⟨xp, wm, hxp0, hwm0, hxp, hwm, e1, e2, hc', fun i hi => g1 _ (by omega)⟩

/-- The positive generator `w₊` of the normalized pair. -/
noncomputable def wp : 𝒲 := Classical.choose D.exists_pair

/-- The negative generator `w₋` of the normalized pair. -/
noncomputable def wm : 𝒲 := Classical.choose (Classical.choose_spec D.exists_pair)

theorem pair_spec : D.wp ≠ 0 ∧ D.wm ≠ 0 ∧ IsVacE W h lam D.wp ∧ IsVacE W h (-lam) D.wm ∧
    W.smul D.wm (2 * m - 1) D.wp = W.vacuum ∧ (∀ i : ℤ, 0 < i → W.smul D.wm (2 * m - 1 + i) D.wp = 0) ∧
    W.smul D.wp (2 * m - 1) D.wm = W.vacuum ∧ (∀ i : ℤ, 0 < i → W.smul D.wp (2 * m - 1 + i) D.wm = 0) :=
  Classical.choose_spec (Classical.choose_spec D.exists_pair)

/-- The raising orbit `w_n = w₊₍₋₁₋₂ₘ₍ₙ₋₁₎₎ w_{n-1}`. -/
noncomputable def up : ℕ → 𝒲
  | 0 => W.vacuum
  | n + 1 => W.smul D.wp (-1 - 2 * m * n) (up n)

/-- The lowering orbit `w_{-n} = w₋₍₋₁₋₂ₘ₍ₙ₋₁₎₎ w_{-(n-1)}`. -/
noncomputable def down : ℕ → 𝒲
  | 0 => W.vacuum
  | n + 1 => W.smul D.wm (-1 - 2 * m * n) (down n)

/-- The charge orbit `(w_k)_{k ∈ ℤ}`. -/
noncomputable def orb (k : ℤ) : 𝒲 := if 0 ≤ k then D.up k.toNat else D.down (-k).toNat

theorem orb_nat (n : ℕ) : D.orb n = D.up n := by
  simp [orb]

theorem orb_neg_nat (n : ℕ) : D.orb (-n) = D.down n := by
  rcases n with _ | n
  · simp [orb, up, down]
  · rw [orb, if_neg (by omega)]
    congr 1

theorem orb_zero : D.orb 0 = W.vacuum := by
  simpa [up] using D.orb_nat 0

theorem up_spec (n : ℕ) : D.up n ≠ 0 ∧ IsVacE W h (n * lam) (D.up n) := by
  induction n with
  | zero =>
    exact ⟨D.rat.toStronglyFinite.vacuum_ne_zero, (vacE_vacuum h).of_eq (by simp)⟩
  | succ n ih =>
    obtain ⟨g1, g2, g3⟩ := leading' D.rat.simple D.omega D.pair_spec.2.2.1 ih.2 D.pair_spec.1 ih.1
      (2 * m * n) (by rw [← mul_assoc, mul_comm lam, mul_assoc, D.sq']; push_cast; ring)
    have e : (-1 - 2 * (m : ℤ) * n) = -(2 * m * n) - 1 := by ring
    refine ⟨?_, ?_⟩
    · change W.smul D.wp (-1 - 2 * m * n) (D.up n) ≠ 0
      rw [e]; exact g2
    · change IsVacE W h _ (W.smul D.wp (-1 - 2 * m * n) (D.up n))
      rw [e]; exact g3.of_eq (by push_cast; ring)

theorem down_spec (n : ℕ) : D.down n ≠ 0 ∧ IsVacE W h (-(n * lam)) (D.down n) := by
  induction n with
  | zero =>
    exact ⟨D.rat.toStronglyFinite.vacuum_ne_zero, (vacE_vacuum h).of_eq (by simp)⟩
  | succ n ih =>
    obtain ⟨g1, g2, g3⟩ := leading' D.rat.simple D.omega D.pair_spec.2.2.2.1 ih.2 D.pair_spec.2.1
      ih.1 (2 * m * n) (by
        rw [neg_mul_neg, ← mul_assoc, mul_comm lam, mul_assoc, D.sq']; push_cast; ring)
    have e : (-1 - 2 * (m : ℤ) * n) = -(2 * m * n) - 1 := by ring
    refine ⟨?_, ?_⟩
    · change W.smul D.wm (-1 - 2 * m * n) (D.down n) ≠ 0
      rw [e]; exact g2
    · change IsVacE W h _ (W.smul D.wm (-1 - 2 * m * n) (D.down n))
      rw [e]; exact g3.of_eq (by push_cast; ring)

theorem orb_spec (k : ℤ) : D.orb k ≠ 0 ∧ IsVacE W h (k * lam) (D.orb k) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rw [D.orb_nat]; exact ⟨(D.up_spec n).1, (D.up_spec n).2.of_eq (by push_cast; ring)⟩
  · rw [D.orb_neg_nat]; exact ⟨(D.down_spec n).1, (D.down_spec n).2.of_eq (by push_cast; ring)⟩

/-- **Raising along the orbit**: `w₊₍₋₁₋₂ₘₖ₎ w_k = w_{k+1}` for every `k ∈ ℤ`. -/
theorem raise (k : ℤ) : W.smul D.wp (-1 - 2 * m * k) (D.orb k) = D.orb (k + 1) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rw [D.orb_nat, show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, D.orb_nat]
    rfl
  · rcases n with _ | n
    · simp only [Nat.cast_zero, neg_zero, mul_zero, sub_zero, zero_add]
      rw [D.orb_zero, W.smul_vacuum_neg_one, show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, D.orb_nat]
      simp [up]
    · rw [D.orb_neg_nat, show -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) by push_cast; ring, D.orb_neg_nat]
      have hrel := rel_vac D.omega D.pair_spec.2.2.1 D.pair_spec.2.2.2.1
        (by rw [D.pair_spec.2.2.2.2.2.2.1, one_smul]) D.pair_spec.2.2.2.2.2.2.2
        (D.down_spec n).2 (N := -(2 * m * n))
        (by rw [mul_neg, ← mul_assoc, mul_comm lam, mul_assoc, D.sq']; push_cast; ring)
      rw [one_smul] at hrel
      change W.smul D.wp (-1 - 2 * m * -((n + 1 : ℕ) : ℤ)) (W.smul D.wm (-1 - 2 * m * n) (D.down n)) = _
      rw [show (-1 - 2 * (m : ℤ) * -((n + 1 : ℕ) : ℤ)) = 2 * m - 1 - -(2 * m * n) by push_cast; ring,
        show (-1 - 2 * (m : ℤ) * n) = -(2 * m * n) - 1 by ring]
      exact hrel

/-- **Lowering along the orbit**: `w₋₍₋₁₊₂ₘₖ₎ w_k = w_{k-1}` for every `k ∈ ℤ`. -/
theorem lower (k : ℤ) : W.smul D.wm (-1 + 2 * m * k) (D.orb k) = D.orb (k - 1) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rcases n with _ | n
    · simp only [Nat.cast_zero, mul_zero, add_zero, zero_sub]
      rw [D.orb_zero, W.smul_vacuum_neg_one, show (-1 : ℤ) = -((1 : ℕ) : ℤ) from rfl, D.orb_neg_nat]
      simp [down]
    · rw [D.orb_nat, show ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) by push_cast; ring, D.orb_nat]
      have hrel := rel_vac D.omega D.pair_spec.2.2.2.1 (D.pair_spec.2.2.1.of_eq (neg_neg lam).symm)
        (by rw [D.pair_spec.2.2.2.2.1, one_smul]) D.pair_spec.2.2.2.2.2.1
        (D.up_spec n).2 (N := -(2 * m * n))
        (by rw [neg_mul, ← mul_assoc, mul_comm lam, mul_assoc, D.sq']; push_cast; ring)
      rw [one_smul] at hrel
      change W.smul D.wm (-1 + 2 * m * ((n + 1 : ℕ) : ℤ)) (W.smul D.wp (-1 - 2 * m * n) (D.up n)) = _
      rw [show (-1 + 2 * (m : ℤ) * ((n + 1 : ℕ) : ℤ)) = 2 * m - 1 - -(2 * m * n) by push_cast; ring,
        show (-1 - 2 * (m : ℤ) * n) = -(2 * m * n) - 1 by ring]
      exact hrel
  · rw [D.orb_neg_nat, show -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) by push_cast; ring, D.orb_neg_nat]
    change _ = W.smul D.wm (-1 - 2 * m * n) (D.down n)
    congr 1; ring

theorem orb_one : D.orb 1 = D.wp := by
  have := D.raise 0
  rw [D.orb_zero, mul_zero, sub_zero, W.smul_vacuum_neg_one, zero_add] at this
  exact this.symm

theorem orb_neg_one : D.orb (-1) = D.wm := by
  have := D.lower 0
  rw [D.orb_zero, mul_zero, add_zero, W.smul_vacuum_neg_one, zero_sub] at this
  exact this.symm

/-- **Multiplicity one**: the vacuum space is spanned by the charge orbit. -/
theorem vac_le_span : (heisRep D.heis).vac ≤ Submodule.span ℂ (Set.range D.orb) := by
  refine le_trans (vac_le_span_eig D.heis D.omega) (Submodule.span_le.mpr ?_)
  rintro y ⟨c, hy⟩
  by_cases hy0 : y = 0
  · rw [hy0]; exact Submodule.zero_mem _
  obtain ⟨k, rfl⟩ := D.all c ⟨y, hy0, hy⟩
  have hk := D.orb_spec k
  have hmk : IsVacE W h (-(k * lam)) (D.orb (-k)) :=
    (D.orb_spec (-k)).2.of_eq (by push_cast; ring)
  set N0 : ℤ := 2 * m * k ^ 2
  have hsq : k * lam * (k * lam) = N0 := by
    simp only [N0]; push_cast; linear_combination (k : ℂ) ^ 2 * D.sq'
  obtain ⟨g1, g2, g3⟩ := leading' D.rat.simple D.omega hk.2 hmk hk.1 (D.orb_spec (-k)).1 (-N0)
    (by rw [mul_neg, hsq]; push_cast; ring)
  rw [neg_neg] at g1 g2 g3
  obtain ⟨c₁, hc₁⟩ := D.vac_zero g3 (by ring)
  have hc₁0 : c₁ ≠ 0 := by rintro rfl; rw [zero_smul] at hc₁; exact g2 hc₁
  obtain ⟨-, -, f3⟩ := leading' D.rat.simple D.omega hmk hy (D.orb_spec (-k)).1 hy0 (-N0)
    (by rw [neg_mul, hsq]; push_cast; ring)
  rw [neg_neg] at f3
  obtain ⟨d, hd⟩ := D.vac_zero f3 (by ring)
  have hrel := rel_vac D.omega hk.2 hmk hc₁ (fun i hi => g1 _ (by omega)) hy (N := N0) hsq
  rw [hd, show N0 - 1 - N0 = -1 by ring, W.smul_smul_right, W.smul_vacuum_neg_one] at hrel
  have : y = (c₁⁻¹ * d) • D.orb k := by
    rw [mul_smul, hrel, smul_smul, inv_mul_cancel₀ hc₁0, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem linearIndependent : LinearIndependent ℂ D.orb := by
  have hinj : Function.Injective (fun k : ℤ => (k : ℂ) * lam) := by
    intro a b hab
    have := mul_right_cancel₀ D.lam_ne hab
    exact_mod_cast this
  refine Module.End.eigenvectors_linearIndependent' (mode (W.Y h) 0) (fun k : ℤ => (k : ℂ) * lam)
    hinj _ fun k => ?_
  exact Module.End.hasEigenvector_iff.mpr
    ⟨Module.End.mem_eigenspace_iff.mpr (D.orb_spec k).2.zero, (D.orb_spec k).1⟩

/-- The orbit vectors as elements of the vacuum space. -/
noncomputable def orbVac (k : ℤ) : (heisRep D.heis).vac :=
  ⟨D.orb k, (heisRep D.heis).mem_vac.mpr fun n hn => (D.orb_spec k).2.pos n hn⟩

/-- **The vacuum space has basis `(w_k)_{k ∈ ℤ}`.** -/
noncomputable def basis : Module.Basis ℤ ℂ (heisRep D.heis).vac :=
  Module.Basis.mk (v := D.orbVac)
    (LinearIndependent.of_comp (heisRep D.heis).vac.subtype D.linearIndependent)
    (by
      intro x _
      have hx := D.vac_le_span x.2
      have hrange : Set.range D.orb = (heisRep D.heis).vac.subtype '' Set.range D.orbVac := by
        rw [← Set.range_comp]; rfl
      rw [hrange, Submodule.span_image] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := Subtype.ext hyx
      rwa [← this])

theorem basis_apply (k : ℤ) : D.basis k = D.orbVac k := by
  simp [basis]

end LatData

/-! ## §7 Two VOAs with the same charge data are isomorphic -/

section Iso

variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The `m = 0` slice of the Jacobi identity: the modes of a product. -/
theorem vjacobi_zero (V : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (n t : ℤ) :
    V.smul (V.smul u n v) t x
      = ∑ᶠ i : ℤ, (negOnePow i * cbz n i) •
          (V.smul u (n + 0 - i) (V.smul v (t + i) x)
            - negOnePow n • V.smul v (n + t - i) (V.smul u (0 + i) x)) := by
  rw [V.jacobi u v x n 0 t, finsum_eq_single _ (0 : ℤ)
    (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_smul]), cbz_zero_left, if_pos rfl,
    one_smul, add_zero, zero_add, sub_zero]

variable {𝒲' : Type*} [AddCommGroup 𝒲'] [Module ℂ 𝒲'] {W' : VertexOperatorAlgebra 𝒲'}

/-- The states whose modes are intertwined by `e` (a VOA-homomorphism test space). -/
def homSub (W : VertexOperatorAlgebra 𝒲) (W' : VertexOperatorAlgebra 𝒲') (e : 𝒲 →ₗ[ℂ] 𝒲') :
    Submodule ℂ 𝒲 where
  carrier := {u | ∀ (n : ℤ) (x : 𝒲), e (W.smul u n x) = W'.smul (e u) n (e x)}
  add_mem' {a b} ha hb n x := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [W.smul_add_left, map_add, ha, hb, map_add, W'.smul_add_left]
  zero_mem' n x := by
    rw [W.smul_zero_left, map_zero, W'.smul_zero_left]
  smul_mem' c a ha n x := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [W.smul_smul_left, map_smul, ha, map_smul, W'.smul_smul_left]

theorem homSub_smul (e : 𝒲 →ₗ[ℂ] 𝒲') (he : Function.Injective e) {u v : 𝒲}
    (hu : u ∈ homSub W W' e) (hv : v ∈ homSub W W' e) (n : ℤ) : W.smul u n v ∈ homSub W W' e := by
  intro t x
  rw [hu n v, vjacobi_zero W u v x n t, vjacobi_zero W' (e u) (e v) (e x) n t,
    LatMod.map_finsum_of_injective e he]
  refine finsum_congr fun i => ?_
  rw [map_smul, map_sub, map_smul, hu, hv, hv, hu]

variable {h : 𝒲} {h' : 𝒲'}

/-- **Charge modes on a vacuum vector are determined by the top one** (cf. `charge_intertw_vac`):
an injective `e` intertwining the creation modes of `h`, with `e x` again a vacuum vector of the
same charge, intertwines every mode of `u` on `x` once it intertwines the top one. -/
theorem intertw_vac (e : 𝒲 →ₗ[ℂ] 𝒲') (he : Function.Injective e)
    (hcr : ∀ n : ℤ, n < 0 → ∀ y, e (W.smul h n y) = W'.smul h' n (e y))
    {u : 𝒲} {u' : 𝒲'} {a : ℂ}
    (hT : W.smul u (-2) W.vacuum = a • W.smul h (-1) u)
    (hT' : W'.smul u' (-2) W'.vacuum = a • W'.smul h' (-1) u')
    {x : 𝒲} {μ : ℂ} (hx : IsVacE W h μ x) (hx' : IsVacE W' h' μ (e x))
    (N₁ : ℤ) (hN : a * μ = -N₁)
    (htop : e (W.smul u (N₁ - 1) x) = W'.smul u' (N₁ - 1) (e x)) :
    ∀ n : ℤ, e (W.smul u n x) = W'.smul u' n (e x) := by
  have hv : ∀ k : ℤ, N₁ ≤ k → W.smul u k x = 0 :=
    chg_vanish (adjointWeakModule W) hT x hx.pos μ hx.zero N₁ hN
  have hv' : ∀ k : ℤ, N₁ ≤ k → W'.smul u' k (e x) = 0 :=
    chg_vanish (adjointWeakModule W') hT' (e x) hx'.pos μ hx'.zero N₁ hN
  have key : ∀ d : ℕ, e (W.smul u (N₁ - 1 - d) x) = W'.smul u' (N₁ - 1 - d) (e x) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d IH =>
    rcases d with _ | d
    · simpa using htop
    · have hrec : (-((N₁ - 1 - d : ℤ) : ℂ) - a * μ) • W.smul u (N₁ - 1 - d - 1) x
          = a • ∑ᶠ i : ℤ, (if 0 ≤ i then
              W.smul h (-1 - i) (W.smul u (N₁ - 1 - d + i) x) else 0) :=
        chg_recursion (adjointWeakModule W) hT x hx.pos μ hx.zero (N₁ - 1 - d)
      have hrec' : (-((N₁ - 1 - d : ℤ) : ℂ) - a * μ) • W'.smul u' (N₁ - 1 - d - 1) (e x)
          = a • ∑ᶠ i : ℤ, (if 0 ≤ i then
              W'.smul h' (-1 - i) (W'.smul u' (N₁ - 1 - d + i) (e x)) else 0) :=
        chg_recursion (adjointWeakModule W') hT' (e x) hx'.pos μ hx'.zero (N₁ - 1 - d)
      rw [hN, show N₁ - 1 - (d : ℤ) - 1 = N₁ - 1 - ((d + 1 : ℕ) : ℤ) by push_cast; ring] at hrec hrec'
      have hcoef : (-((N₁ - 1 - d : ℤ) : ℂ) - -(N₁ : ℂ)) = ((d + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [hcoef] at hrec hrec'
      have hne : ((d + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
      have h1 := congrArg e hrec
      rw [map_smul, map_smul, LatMod.map_finsum_of_injective e he] at h1
      have hsum : (∑ᶠ i : ℤ, e (if 0 ≤ i then W.smul h (-1 - i)
            (W.smul u (N₁ - 1 - d + i) x) else 0))
          = ∑ᶠ i : ℤ, (if 0 ≤ i then W'.smul h' (-1 - i)
            (W'.smul u' (N₁ - 1 - d + i) (e x)) else 0) := by
        refine finsum_congr fun i => ?_
        split_ifs with hi
        · rw [hcr _ (by omega)]
          congr 1
          by_cases hid : i ≤ d
          · have := IH (d - i.toNat) (by omega)
            rwa [show N₁ - 1 - ((d - i.toNat : ℕ) : ℤ) = N₁ - 1 - d + i by omega] at this
          · rw [hv _ (by omega), hv' _ (by omega), map_zero]
        · exact map_zero e
      rw [hsum, ← hrec'] at h1
      exact smul_right_injective _ hne h1
  intro n
  by_cases hn : N₁ ≤ n
  · rw [hv n hn, hv' n hn, map_zero]
  · have := key (N₁ - 1 - n).toNat
    rwa [show N₁ - 1 - ((N₁ - 1 - n).toNat : ℤ) = n by omega] at this

variable {lam : ℂ} {m : ℕ} (D : LatData W h lam m) (D' : LatData W' h' lam m)

/-- The comparison map `W ≅ M(1) ⊗ Ω ≅ M(1) ⊗ Ω' ≅ W'`, `p(h) w_k ↦ p(h') w'_k`. -/
noncomputable def cmp : 𝒲 ≃ₗ[ℂ] 𝒲' :=
  (heisRep D.heis).fockEquiv.symm.trans
    ((Finsupp.mapRange.linearEquiv (D.basis.equiv D'.basis (Equiv.refl ℤ))).trans
      (heisRep D'.heis).fockEquiv)

theorem cmp_orb (k : ℤ) : cmp D D' (D.orb k) = D'.orb k := by
  have h1 : D.orb k = ((D.orbVac k : (heisRep D.heis).vac) : 𝒲) := rfl
  have h2 : D'.orb k = ((D'.orbVac k : (heisRep D'.heis).vac) : 𝒲') := rfl
  rw [cmp, LinearEquiv.trans_apply, LinearEquiv.trans_apply, h1,
    (heisRep D.heis).fockEquiv_symm_vac, Finsupp.mapRange.linearEquiv_apply,
    Finsupp.mapRange_single, ← D.basis_apply, Module.Basis.equiv_apply,
    Equiv.refl_apply, D'.basis_apply, HeisSvN.HeisRep.fockEquiv_apply,
    HeisSvN.HeisRep.fockMap_single_zero, h2]

theorem cmp_cr (i : ℕ) (x : 𝒲) :
    cmp D D' ((heisRep D.heis).cr i x) = (heisRep D'.heis).cr i (cmp D D' x) := by
  set φ := D.basis.equiv D'.basis (Equiv.refl ℤ)
  have he : ∀ f, cmp D D' ((heisRep D.heis).fockMap f)
      = (heisRep D'.heis).fockMap (Finsupp.mapRange.linearEquiv φ f) := by
    intro f
    rw [cmp, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      ← HeisSvN.HeisRep.fockEquiv_apply, LinearEquiv.symm_apply_apply,
      HeisSvN.HeisRep.fockEquiv_apply]
  obtain ⟨f, rfl⟩ := (heisRep D.heis).fockMap_surjective x
  rw [HeisSvN.HeisRep.cr_fockMap, he, he, HeisSvN.HeisRep.cr_fockMap]
  congr 1
  exact mapRange_mapDomain_comm φ.toLinearMap.toAddMonoidHom _ f

theorem cmp_hneg {n : ℤ} (hn : n < 0) (x : 𝒲) :
    cmp D D' (W.smul h n x) = W'.smul h' n (cmp D D' x) := by
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = -((i : ℤ) + 1) := ⟨(-n - 1).toNat, by omega⟩
  exact cmp_cr D D' i x

/-- The comparison map intertwines every mode of the Heisenberg vectors. -/
theorem cmp_h (n : ℤ) (x : 𝒲) : cmp D D' (W.smul h n x) = W'.smul h' n (cmp D D' x) := by
  rcases lt_or_ge n 0 with hn | hn
  · exact cmp_hneg D D' hn x
  set e := cmp D D'
  let S : Submodule ℂ 𝒲 :=
    { carrier := {x | e (W.smul h n x) = W'.smul h' n (e x)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [W.smul_add_right, map_add, ha, hb, map_add, W'.smul_add_right]
      zero_mem' := by simp
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [W.smul_smul_right, map_smul, ha, map_smul, W'.smul_smul_right] }
  have htop : S = ⊤ := by
    refine (heisRep D.heis).eq_top_of_vac_le S ?_ ?_
    · refine le_trans D.vac_le_span (Submodule.span_le.mpr ?_)
      rintro _ ⟨k, rfl⟩
      change e (W.smul h n (D.orb k)) = W'.smul h' n (e (D.orb k))
      rw [cmp_orb, (D.orb_spec k).2.smul_nonneg hn, (D'.orb_spec k).2.smul_nonneg hn]
      split_ifs
      · rw [map_smul, cmp_orb]
      · exact map_zero e
    · intro p hp y hy
      change e (W.smul h n (W.smul h p y)) = W'.smul h' n (e (W.smul h p y))
      have c1 := DMCOne.heis_comm D.heis n p y
      have c2 := DMCOne.heis_comm D'.heis n p (e y)
      have hy' : e (W.smul h n y) = W'.smul h' n (e y) := hy
      rw [eq_add_of_sub_eq c1, map_add, map_smul, cmp_hneg D D' hp, hy', cmp_hneg D D' hp,
        eq_add_of_sub_eq c2]
  have hx : x ∈ S := by rw [htop]; trivial
  exact hx

theorem cmp_vacuum : cmp D D' W.vacuum = W'.vacuum := by
  rw [← D.orb_zero, cmp_orb, D'.orb_zero]

theorem cmp_heis : cmp D D' h = h' := by
  have := cmp_hneg D D' (n := -1) (by norm_num) W.vacuum
  rw [W.smul_vacuum_neg_one, cmp_vacuum, W'.smul_vacuum_neg_one] at this
  exact this

/-- The comparison map intertwines a charged vacuum vector `u` with `u'` once the top modes on
the orbit agree. -/
theorem cmp_charge {u : 𝒲} {u' : 𝒲'} {a : ℂ} (hu : IsVacE W h a u) (hu' : IsVacE W' h' a u')
    (hint : ∀ k : ℤ, ∃ N₁ : ℤ, a * (k * lam) = -N₁ ∧
      cmp D D' (W.smul u (N₁ - 1) (D.orb k)) = W'.smul u' (N₁ - 1) (D'.orb k))
    (t : ℤ) (x : 𝒲) : cmp D D' (W.smul u t x) = W'.smul u' t (cmp D D' x) := by
  set e := cmp D D'
  let S : Submodule ℂ 𝒲 :=
    { carrier := {x | ∀ t, e (W.smul u t x) = W'.smul u' t (e x)}
      add_mem' := by
        intro a b ha hb t
        simp only [Set.mem_setOf_eq] at ha hb
        rw [W.smul_add_right, map_add, ha, hb, map_add, W'.smul_add_right]
      zero_mem' := by intro t; simp
      smul_mem' := by
        intro c a ha t
        simp only [Set.mem_setOf_eq] at ha
        rw [W.smul_smul_right, map_smul, ha, map_smul, W'.smul_smul_right] }
  have hT := T_vac D.omega hu
  have hT' := T_vac D'.omega hu'
  have htop : S = ⊤ := by
    refine (heisRep D.heis).eq_top_of_vac_le S ?_ ?_
    · refine le_trans D.vac_le_span (Submodule.span_le.mpr ?_)
      rintro _ ⟨k, rfl⟩
      obtain ⟨N₁, hN, hk⟩ := hint k
      have hx' : IsVacE W' h' (k * lam) (e (D.orb k)) := by
        rw [cmp_orb]; exact (D'.orb_spec k).2
      exact intertw_vac e.toLinearMap e.injective (fun n hn y => cmp_hneg D D' hn y) hT hT'
        (D.orb_spec k).2 hx' N₁ hN (by
          change e _ = _
          rw [hk]; congr 1; exact (cmp_orb D D' k).symm)
    · intro p hp y hy t
      change e (W.smul u t (W.smul h p y)) = W'.smul u' t (e (W.smul h p y))
      have c1 : W.smul h p (W.smul u t y) - W.smul u t (W.smul h p y) = a • W.smul u (p + t) y :=
        chg_comm (adjointWeakModule W) hu p t y
      have c2 : W'.smul h' p (W'.smul u' t (e y)) - W'.smul u' t (W'.smul h' p (e y))
          = a • W'.smul u' (p + t) (e y) :=
        chg_comm (adjointWeakModule W') hu' p t (e y)
      have hy' : ∀ t, e (W.smul u t y) = W'.smul u' t (e y) := hy
      rw [show W.smul u t (W.smul h p y) = W.smul h p (W.smul u t y) - a • W.smul u (p + t) y by
          rw [← c1]; abel,
        map_sub, map_smul, cmp_hneg D D' hp, hy', hy', cmp_hneg D D' hp, ← c2]
      abel
  have hx : x ∈ S := by rw [htop]; trivial
  exact hx t

theorem int_of_cast {N₁ : ℤ} {z : ℂ} {M : ℤ} (h1 : z = -N₁) (h2 : z = M) : N₁ = -M := by
  have : ((N₁ : ℤ) : ℂ) = ((-M : ℤ) : ℂ) := by push_cast; rw [← h2, h1]; ring
  exact_mod_cast this

include D D' in
/-- **Uniqueness**: two VOAs with the same charge data (`lam`, `m`) are isomorphic. -/
theorem voaIsomorphic_of_latData : VOAIsomorphic W W' := by
  set e := cmp D D'
  have hsq := D.sq'
  have hheis : h ∈ homSub W W' e.toLinearMap := by
    intro n x
    change e _ = W'.smul (e h) n (e x)
    rw [cmp_heis]; exact cmp_h D D' n x
  have hwp : D.wp ∈ homSub W W' e.toLinearMap := by
    intro t x
    have he : e D.wp = D'.wp := by rw [← D.orb_one, cmp_orb, D'.orb_one]
    change e _ = W'.smul (e D.wp) t (e x)
    rw [he]
    refine cmp_charge D D' D.pair_spec.2.2.1 D'.pair_spec.2.2.1 (fun k => ?_) t x
    refine ⟨-(2 * m * k), by push_cast; linear_combination (k : ℂ) * hsq, ?_⟩
    rw [show -(2 * (m : ℤ) * k) - 1 = -1 - 2 * m * k by ring, D.raise, D'.raise, cmp_orb]
  have hwm : D.wm ∈ homSub W W' e.toLinearMap := by
    intro t x
    have he : e D.wm = D'.wm := by rw [← D.orb_neg_one, cmp_orb, D'.orb_neg_one]
    change e _ = W'.smul (e D.wm) t (e x)
    rw [he]
    refine cmp_charge D D' D.pair_spec.2.2.2.1 D'.pair_spec.2.2.2.1 (fun k => ?_) t x
    refine ⟨2 * m * k, by push_cast; linear_combination -(k : ℂ) * hsq, ?_⟩
    rw [show 2 * (m : ℤ) * k - 1 = -1 + 2 * m * k by ring, D.lower, D'.lower, cmp_orb]
  have hsm := fun u (hu : u ∈ homSub W W' e.toLinearMap) v (hv : v ∈ homSub W W' e.toLinearMap)
    (n : ℤ) => homSub_smul e.toLinearMap e.injective hu hv n
  have horb : ∀ k : ℤ, D.orb k ∈ homSub W W' e.toLinearMap := by
    have h1 : D.orb 1 ∈ homSub W W' e.toLinearMap := by rw [D.orb_one]; exact hwp
    have h0 : D.orb 0 ∈ homSub W W' e.toLinearMap := by
      have := D.lower 1
      rw [show (1 : ℤ) - 1 = 0 by ring] at this
      rw [← this]; exact hsm _ hwm _ h1 _
    intro k
    induction k using Int.induction_on with
    | zero => exact h0
    | succ k ih => rw [← D.raise k]; exact hsm _ hwp _ ih _
    | pred k ih => rw [← D.lower (-k)]; exact hsm _ hwm _ ih _
  have hS : homSub W W' e.toLinearMap = ⊤ := by
    refine (heisRep D.heis).eq_top_of_vac_le _ ?_ ?_
    · exact le_trans D.vac_le_span (Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact horb k))
    · intro n _ x hx
      exact hsm _ hheis _ hx n
  refine ⟨e, ⟨cmp_vacuum D D', fun u n v => ?_⟩, ?_⟩
  · have hu : u ∈ homSub W W' e.toLinearMap := by rw [hS]; trivial
    exact hu n v
  · rw [D.omega, D'.omega, omegaH, omegaH, map_smul]
    congr 1
    exact (cmp_h D D' (-1) h).trans (by rw [cmp_heis])

end Iso

/-! ## §8 The charge data of `V_{2m}` -/

section V2mData

open VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet HeisenbergN LatMod

variable (m : ℕ) (hm : 1 ≤ m)

/-- `h₍₀₎(p ⊗ e^β) = β_h (p ⊗ e^β)` in `V_{2m}`. -/
theorem V2m_hb_zero (p : FockN (rank (latP m))) (β : ℤ) :
    (V2m m hm).smul (hb m) 0 (latStateGen (latP m) p β)
      = chargeCoord (latP m) β (a0 m) • latStateGen (latP m) p β := by
  rw [V2m, PreVertexAlgebra.smul_def, hb, latVOA_Y_bosonState, mode_apply, alphaLatGen_apply,
    LinearMap.add_apply, if_pos (by norm_num), zGradeOpGen_latStateGen]
  simp [latStateGen, currentN_apply]

include hm in
theorem chargeCoord_eq (β : ℤ) :
    chargeCoord (latP m) β (a0 m) = β * chargeCoord (latP m) (1 : ℤ) (a0 m) := by
  have h1 := chargeCoord_rankOne (m := m) hm β
  have h2 := chargeCoord_rankOne (m := m) hm 1
  have hc := chargeCoord_one_ne_zero m hm
  refine mul_right_cancel₀ hc ?_
  push_cast at h2
  linear_combination h1 - (β : ℂ) * h2

/-- Every `h₍₀₎`-eigenvalue on `V_{2m}` lies in `ℤ · (e^α)_h`. -/
theorem V2m_charge_int {c : ℂ} {x : LatModuleGen (latP m)} (hx0 : x ≠ 0)
    (hx : (V2m m hm).smul (hb m) 0 x = c • x) :
    ∃ k : ℤ, c = k * chargeCoord (latP m) (1 : ℤ) (a0 m) := by
  by_contra hne
  push Not at hne
  set f : Module.End ℂ (LatModuleGen (latP m)) := mode ((V2m m hm).Y (hb m)) 0
  have hle : ∀ y : LatModuleGen (latP m), y ∈ ⨆ (μ : ℂ) (_ : μ ≠ c), f.eigenspace μ := by
    intro y
    have hy : y ∈ Submodule.span ℂ (Set.range (fun q : FockN (rank (latP m)) × (latP m).carrier =>
        latStateGen (latP m) q.1 q.2)) := by rw [latStateGen_span]; trivial
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨p, β⟩, rfl⟩ := hy
      refine le_iSup₂_of_le (f := fun (μ : ℂ) (_ : μ ≠ c) => f.eigenspace μ)
        (chargeCoord (latP m) β (a0 m)) ?_ le_rfl ?_
      · rw [chargeCoord_eq m hm]; exact (hne β).symm
      · exact Module.End.mem_eigenspace_iff.mpr (V2m_hb_zero m hm p β)
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul a y _ hy => exact Submodule.smul_mem _ a hy
  exact hx0 (Submodule.disjoint_def.mp (Module.End.eigenspaces_iSupIndep f c) x
    (Module.End.mem_eigenspace_iff.mpr hx) (hle x))

/-- **`V_{2m}` has charge data `(e^α)_h`, `m`.** -/
theorem V2m_latData : LatData (V2m m hm) (hb m) (chargeCoord (latP m) (1 : ℤ) (a0 m)) m where
  rat := V2m_stronglyRational m hm
  heis := V2m_isHeisVector m hm
  omega := V2m_conformal_eq_omegaH m hm
  one_le := hm
  sq := by
    have := chargeCoord_rankOne (m := m) hm 1
    rw [sq, this]; push_cast; ring
  charge := ⟨latChargeGen (latP m) (1 : ℤ), Screen.latStateGen_ne_zero (latP m) one_ne_zero _,
    fun i hi => by rw [hb_smul_charge m hm 1 hi.le, if_neg hi.ne'],
    by rw [hb_smul_charge m hm 1 le_rfl, if_pos rfl]⟩
  all c := by
    rintro ⟨x, hx0, hx⟩
    exact V2m_charge_int m hm hx0 hx.zero

end V2mData

end LatRec

open LatRec VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet HeisenbergN LatMod in
/-- **DM-2, the lattice reconstruction** (Dong–Mason): a strongly rational VOA with a unit
Heisenberg vector `h` whose conformal vector is `ω_h = ½h₍₋₁₎h` is isomorphic to `V_{2m}` for some
`m ≥ 1`.  Route: Fock decomposition `W ≅ M(1) ⊗ Ω`; the charges form a rank-one even lattice
`ℤ lam`, `lam² = 2m` (`exists_charge_generator`); `Ω` has the normalized basis `(w_k)` with
`w₊₍₋₁₋₂ₘₖ₎w_k = w_{k+1}`, `w₋₍₋₁₊₂ₘₖ₎w_k = w_{k-1}` (`LatData.raise`, `LatData.lower`,
`LatData.basis`); the comparison map with the same data on `V_{2m}` is a VOA isomorphism
(`voaIsomorphic_of_latData`). -/
theorem heisLatticeReconstruction : HeisLatticeReconstruction.{u} := by
  intro 𝒲 _ _ W hW h hh hω
  obtain ⟨lam, m, D⟩ := exists_latData hW hh hω
  have hm := D.one_le
  have DV := V2m_latData m hm
  have hsq : lam ^ 2 = (chargeCoord (latP m) (1 : ℤ) (a0 m)) ^ 2 := by rw [D.sq, DV.sq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1
  · subst h1
    exact ⟨m, hm, voaIsomorphic_of_latData D DV⟩
  · subst h1
    have D2 := D.neg
    rw [neg_neg] at D2
    exact ⟨m, hm, voaIsomorphic_of_latData D2 DV⟩

end VOA.Classification.COne
