/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.HeisenbergNVertex
import VOA.Core.VertexOperatorAlgebra
import VOA.Core.Goddard
import VOA.Core.Dong

/-!
# The rank-`r` Heisenberg conformal layer + the VOA instance

Builds, namespaced under `VOA.HeisenbergN`, the conformal structure of the rank-`r`
free-boson Fock space `FockN r` on top of the vertex layer
(`Examples.HeisenbergNVertex`): the per-family Sugawara modes `LvirNa`, the total Virasoro
`LvirN = ∑_a LvirNa`, the conformal vector `ωN`, the Virasoro relation `L_virasoroN` with
**central charge `c = r`** (one boson per family, cross-family commuting), the conformal
bridge `YN(ωN) = sugawaraFieldN`, the VOA1–VOA3 conformal axioms, and the assembled
`heisenbergNVOA r k hk : VertexOperatorAlgebra (FockN r)`.

All rank-1 proofs (`Examples.HeisenbergVirasoro/Central/Conformal/VOA`) are reused as
line-by-line templates with the family index `a : Fin r` carried through; the one genuinely
new computation is the **cross-family vanishing** `[L^a_m, L^b_n] = 0` for `a ≠ b`, from the
`δ^{ab}` in `oscN_comm`.
-/

namespace VOA

namespace HeisenbergN

open scoped BigOperators
open MvPolynomial
open Module (End)
open Finset

variable {r : ℕ}

/-! ## §1  The per-family Sugawara field and its modes -/

/-- The involution `j ↦ -j-1` (current-index ↔ mode-index flip). -/
def flipIdxN : ℤ ≃ ℤ where
  toFun j := -j - 1
  invFun j := -j - 1
  left_inv j := by dsimp only; ring
  right_inv j := by dsimp only; ring

@[simp] theorem flipIdxN_apply (j : ℤ) : flipIdxN j = -j - 1 := rfl

/-- The single normal-ordered operator term `T^a_j = :aᵃ_{m-j} aᵃ_j:`. -/
noncomputable def sugTermN (r : ℕ) (k : ℂ) (a : Fin r) (m j : ℤ) : End ℂ (FockN r) :=
  if j < 0 then oscN r k a j * oscN r k a (m - j) else oscN r k a (m - j) * oscN r k a j

@[simp] theorem sugTermN_apply (r : ℕ) (k : ℂ) (a : Fin r) (m j : ℤ) (x : FockN r) :
    sugTermN r k a m j x
      = if j < 0 then oscN r k a j (oscN r k a (m - j) x) else oscN r k a (m - j) (oscN r k a j x) := by
  rw [sugTermN]; split_ifs <;> rw [Module.End.mul_apply]

/-- The `(-M-1)`-coefficient of `nprod (currentN a)(currentN a)` in the mode picture. -/
theorem nprodN_current_coeff (r : ℕ) (k : ℂ) (a : Fin r) (M : ℤ) (x : FockN r) :
    nprod (currentN_isField r k a) (currentN_isField r k a) (-M - 1) x
      = ∑ᶠ j : ℤ, (if j < 0 then oscN r k a j (oscN r k a (M - 1 - j) x)
                   else oscN r k a (M - 1 - j) (oscN r k a j x)) := by
  rw [nprod_apply]
  rw [← finsum_comp_equiv flipIdxN]
  refine finsum_congr fun j => ?_
  rw [normalOrdered_apply, flipIdxN_apply]
  rw [currentN_apply, currentN_apply,
      show -(-j - 1) - 1 = j from by ring,
      show -(-M - 1 - (-j - 1)) - 1 = M - 1 - j from by ring]
  by_cases hj : j < 0
  · rw [if_pos (by omega), if_pos hj, Module.End.mul_apply]
  · rw [if_neg (by omega), if_neg hj, Module.End.mul_apply]

/-- The **per-family Sugawara field** `Lᵃ(z) = (1/2k):αᵃ(z)αᵃ(z):`. -/
noncomputable def sugawaraFieldNa (r : ℕ) (k : ℂ) (a : Fin r) : FormalDist (End ℂ (FockN r)) :=
  (1 / (2 * k)) • nprod (currentN_isField r k a) (currentN_isField r k a)

/-- The **total Sugawara field** `L(z) = ∑_a (1/2k):αᵃαᵃ:`. -/
noncomputable def sugawaraFieldN (r : ℕ) (k : ℂ) : FormalDist (End ℂ (FockN r)) :=
  ∑ a : Fin r, sugawaraFieldNa r k a

/-- The **per-family Sugawara mode** `Lᵃₘ = (1/2k)·(nprod αᵃ αᵃ)(-m-2)`. -/
noncomputable def LvirNa (r : ℕ) (k : ℂ) (a : Fin r) (m : ℤ) : End ℂ (FockN r) :=
  (1 / (2 * k)) • nprod (currentN_isField r k a) (currentN_isField r k a) (-m - 2)

/-- The **total Virasoro mode** `Lₘ = ∑_a Lᵃₘ`. -/
noncomputable def LvirN (r : ℕ) (k : ℂ) (m : ℤ) : End ℂ (FockN r) :=
  ∑ a : Fin r, LvirNa r k a m

theorem LvirNa_apply (r : ℕ) (k : ℂ) (a : Fin r) (m : ℤ) (x : FockN r) :
    LvirNa r k a m x
      = (1 / (2 * k)) • ∑ᶠ j : ℤ, (if j < 0 then oscN r k a j (oscN r k a (m - j) x)
                                   else oscN r k a (m - j) (oscN r k a j x)) := by
  rw [LvirNa, LinearMap.smul_apply]
  congr 1
  have := nprodN_current_coeff r k a (m + 1) x
  rw [show -(m + 1) - 1 = -m - 2 from by ring] at this
  rw [this]
  exact finsum_congr fun j => by rw [show m + 1 - 1 - j = m - j from by ring]

theorem LvirNa_apply' (r : ℕ) (k : ℂ) (a : Fin r) (m : ℤ) (x : FockN r) :
    LvirNa r k a m x = (1 / (2 * k)) • ∑ᶠ j : ℤ, sugTermN r k a m j x := by
  rw [LvirNa_apply]; congr 1; exact finsum_congr fun j => (sugTermN_apply r k a m j x).symm

theorem LvirN_apply (r : ℕ) (k : ℂ) (m : ℤ) (x : FockN r) :
    LvirN r k m x = ∑ a : Fin r, LvirNa r k a m x := by
  rw [LvirN, LinearMap.sum_apply]

/-! ## §2  The commutator `[Lᵃₘ, aᵇₙ] = δ^{ab}·(-n)·aᵃ_{m+n}` and `[Lₘ, aᵇₙ] = -n aᵇ_{m+n}` -/

/-- A scalar multiple of `id` is central. -/
theorem oscN_mul_smul_id_comm (r : ℕ) (k : ℂ) (a : Fin r) (n : ℤ) (c : ℂ) :
    oscN r k a n * (c • (LinearMap.id : End ℂ (FockN r)))
      = (c • LinearMap.id) * oscN r k a n := by
  rw [mul_smul_comm, smul_mul_assoc,
    show (LinearMap.id : End ℂ (FockN r)) = (1 : End ℂ (FockN r)) from rfl, mul_one, one_mul]

/-- Reordering inside a bracket is harmless (same family `a`). -/
theorem oscN_bracket_swap (r : ℕ) (k : ℂ) (a : Fin r) (n p q : ℤ) :
    oscN r k a n * (oscN r k a p * oscN r k a q) - (oscN r k a p * oscN r k a q) * oscN r k a n
      = oscN r k a n * (oscN r k a q * oscN r k a p)
        - (oscN r k a q * oscN r k a p) * oscN r k a n := by
  have hcomm : oscN r k a p * oscN r k a q - oscN r k a q * oscN r k a p
      = (if a = a ∧ p + q = 0 then (p : ℂ) * k else 0) • LinearMap.id := oscN_comm r k a a p q
  have hswap : oscN r k a p * oscN r k a q
      = oscN r k a q * oscN r k a p
        + (if a = a ∧ p + q = 0 then (p : ℂ) * k else 0) • LinearMap.id := by
    rw [← hcomm]; abel
  rw [hswap, mul_add, add_mul, oscN_mul_smul_id_comm]
  noncomm_ring

/-- The per-term commutator `[aᵇₙ, :aᵃ_{m-j}aᵃ_j:]`, Leibniz-expanded. The `δ^{ab}` gate
appears via `oscN_comm a b`/`oscN_comm b a`; for `a ≠ b` both gates vanish. -/
theorem oscN_bracket_normalOrdered_term (r : ℕ) (k : ℂ) (a b : Fin r) (m n j : ℤ) :
    oscN r k b n * (if j < 0 then oscN r k a j * oscN r k a (m - j)
                    else oscN r k a (m - j) * oscN r k a j)
      - (if j < 0 then oscN r k a j * oscN r k a (m - j)
         else oscN r k a (m - j) * oscN r k a j) * oscN r k b n
      = (if a = b ∧ n + (m - j) = 0 then (n : ℂ) * k else 0) • oscN r k a j
        + (if a = b ∧ n + j = 0 then (n : ℂ) * k else 0) • oscN r k a (m - j) := by
  have hT : oscN r k b n * (if j < 0 then oscN r k a j * oscN r k a (m - j)
                            else oscN r k a (m - j) * oscN r k a j)
      - (if j < 0 then oscN r k a j * oscN r k a (m - j)
         else oscN r k a (m - j) * oscN r k a j) * oscN r k b n
      = oscN r k b n * (oscN r k a (m - j) * oscN r k a j)
        - (oscN r k a (m - j) * oscN r k a j) * oscN r k b n := by
    by_cases hj : j < 0
    · rw [if_pos hj]
      -- need: bn·(aj·a_{m-j}) - (aj·a_{m-j})·bn = bn·(a_{m-j}·aj) - (a_{m-j}·aj)·bn
      -- this is oscN_bracket_swap with the same-family factors a_j, a_{m-j}, but bn is family b.
      -- Use the central commutator [a_j,a_{m-j}] directly.
      have hcomm : oscN r k a j * oscN r k a (m - j) - oscN r k a (m - j) * oscN r k a j
          = (if a = a ∧ j + (m - j) = 0 then (j : ℂ) * k else 0) • LinearMap.id :=
        oscN_comm r k a a j (m - j)
      have hswap : oscN r k a j * oscN r k a (m - j)
          = oscN r k a (m - j) * oscN r k a j
            + (if a = a ∧ j + (m - j) = 0 then (j : ℂ) * k else 0) • LinearMap.id := by
        rw [← hcomm]; abel
      rw [hswap, mul_add, add_mul, oscN_mul_smul_id_comm]
      noncomm_ring
    · rw [if_neg hj]
  rw [hT]
  have leib : oscN r k b n * (oscN r k a (m - j) * oscN r k a j)
      - (oscN r k a (m - j) * oscN r k a j) * oscN r k b n
      = (oscN r k b n * oscN r k a (m - j) - oscN r k a (m - j) * oscN r k b n) * oscN r k a j
        + oscN r k a (m - j) * (oscN r k b n * oscN r k a j - oscN r k a j * oscN r k b n) := by
    rw [sub_mul, mul_sub, ← mul_assoc, ← mul_assoc]; abel
  rw [leib, oscN_comm r k b a n (m - j), oscN_comm r k b a n j, smul_mul_assoc, mul_smul_comm,
    show (LinearMap.id : End ℂ (FockN r)) * oscN r k a j = oscN r k a j from by
      rw [show (LinearMap.id : End ℂ (FockN r)) = 1 from rfl, one_mul],
    show oscN r k a (m - j) * (LinearMap.id : End ℂ (FockN r)) = oscN r k a (m - j) from by
      rw [show (LinearMap.id : End ℂ (FockN r)) = 1 from rfl, mul_one]]
  -- now reconcile the gates: oscN_comm b a gives `if b=a ∧ …`; target has `if a=b ∧ …`
  congr 1
  · congr 1
    by_cases hab : a = b
    · subst hab; rfl
    · rw [if_neg (by rintro ⟨h, _⟩; exact hab h.symm), if_neg (by rintro ⟨h, _⟩; exact hab h)]
  · congr 1
    by_cases hab : a = b
    · subst hab; rfl
    · rw [if_neg (by rintro ⟨h, _⟩; exact hab h.symm), if_neg (by rintro ⟨h, _⟩; exact hab h)]

/-- The per-family Sugawara term family `j ↦ T^a_j x` has finite support. -/
theorem sugTermN_support_finite (r : ℕ) (k : ℂ) (a : Fin r) (m : ℤ) (x : FockN r) :
    (Function.support (fun j : ℤ => sugTermN r k a m j x)).Finite := by
  have hfin := normalOrdered_diag_support_finite (currentN_isField r k a) (currentN_isField r k a)
    (-m - 2) x
  apply Set.Finite.subset (hfin.image (fun p => -p - 1))
  intro j hj
  rw [Function.mem_support] at hj
  rw [Set.mem_image]
  refine ⟨-j - 1, ?_, by ring⟩
  rw [Function.mem_support]
  rw [normalOrdered_apply, currentN_apply, currentN_apply]
  rw [show -(-j - 1) - 1 = j from by ring,
      show -(-m - 2 - (-j - 1)) - 1 = m - j from by ring]
  rw [sugTermN_apply] at hj
  by_cases hjlt : j < 0
  · rw [if_pos (by omega)]; rw [if_pos hjlt] at hj; rwa [Module.End.mul_apply]
  · rw [if_neg (by omega)]; rw [if_neg hjlt] at hj; rwa [Module.End.mul_apply]

/-- A delta-gated finsum collapses to its single nonzero point. -/
theorem finsumN_gate_collapse (c : ℂ) (w : ℤ → FockN r) (j₀ : ℤ) (p : ℤ → Prop)
    [DecidablePred p] (hp : ∀ j, p j ↔ j = j₀) :
    (∑ᶠ j : ℤ, (if p j then c else 0) • w j) = c • w j₀ := by
  rw [finsum_eq_single (fun j => (if p j then c else 0) • w j) j₀ (fun j hj => ?_)]
  · show (if p j₀ then c else 0) • w j₀ = c • w j₀
    rw [if_pos ((hp j₀).mpr rfl)]
  · show (if p j then c else 0) • w j = 0
    rw [if_neg (fun hpj => hj ((hp j).mp hpj)), zero_smul]

/-- **`[Lᵃₘ, aᵇₙ] = δ^{ab}·(-n)·aᵃ_{m+n}`** (per-family + cross-family). The diagonal `a = b`
is the rank-1 `L_comm_osc`; for `a ≠ b` the families commute (`oscN_comm` has `δ^{ab}`), so the
bracket vanishes. -/
theorem LvirNa_comm_oscN (r : ℕ) (k : ℂ) (hk : k ≠ 0) (a b : Fin r) (m n : ℤ) :
    LvirNa r k a m * oscN r k b n - oscN r k b n * LvirNa r k a m
      = (if a = b then (-(n : ℂ)) • oscN r k a (m + n) else 0) := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
  have hfin_x : (Function.support (fun j : ℤ => sugTermN r k a m j x)).Finite :=
    sugTermN_support_finite r k a m x
  have hfin_nx : (Function.support (fun j : ℤ => sugTermN r k a m j (oscN r k b n x))).Finite :=
    sugTermN_support_finite r k a m (oscN r k b n x)
  rw [LvirNa_apply' r k a m (oscN r k b n x), LvirNa_apply' r k a m x, map_smul,
      map_finsum (oscN r k b n) hfin_x, ← smul_sub]
  rw [← finsum_sub_distrib hfin_nx
      (hfin_x.subset (fun j hj => by
        rw [Function.mem_support] at hj ⊢; exact fun h => hj (by rw [h, map_zero])))]
  have hterm : ∀ j : ℤ, sugTermN r k a m j (oscN r k b n x) - oscN r k b n (sugTermN r k a m j x)
      = -((if a = b ∧ n + (m - j) = 0 then (n : ℂ) * k else 0) • oscN r k a j x
          + (if a = b ∧ n + j = 0 then (n : ℂ) * k else 0) • oscN r k a (m - j) x) := by
    intro j
    have hb := oscN_bracket_normalOrdered_term r k a b m n j
    have hop : sugTermN r k a m j * oscN r k b n - oscN r k b n * sugTermN r k a m j
        = -((if a = b ∧ n + (m - j) = 0 then (n : ℂ) * k else 0) • oscN r k a j
            + (if a = b ∧ n + j = 0 then (n : ℂ) * k else 0) • oscN r k a (m - j)) := by
      rw [sugTermN, eq_neg_iff_add_eq_zero, ← hb]; abel
    have happ := congrArg (fun (T : End ℂ (FockN r)) => T x) hop
    simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply,
      LinearMap.smul_apply, Module.End.mul_apply] using happ
  rw [finsum_congr hterm]
  rw [show (∑ᶠ j : ℤ, -((if a = b ∧ n + (m - j) = 0 then (n : ℂ) * k else 0) • oscN r k a j x
          + (if a = b ∧ n + j = 0 then (n : ℂ) * k else 0) • oscN r k a (m - j) x))
        = ∑ᶠ j : ℤ, ((if a = b ∧ n + (m - j) = 0 then -((n : ℂ) * k) else 0) • oscN r k a j x
          + (if a = b ∧ n + j = 0 then -((n : ℂ) * k) else 0) • oscN r k a (m - j) x) from
      finsum_congr fun j => by rw [neg_add]; congr 1 <;> · split_ifs <;> simp [neg_smul]]
  by_cases hab : a = b
  · subst hab
    rw [if_pos (rfl : a = a)]
    have hf1 : (Function.support (fun j : ℤ =>
        (if a = a ∧ n + (m - j) = 0 then -((n : ℂ) * k) else 0) • oscN r k a j x)).Finite := by
      apply Set.Finite.subset (Set.finite_singleton (m + n))
      intro j hj; rw [Function.mem_support] at hj; rw [Set.mem_singleton_iff]
      by_contra hne; apply hj; rw [if_neg (by rintro ⟨_, h⟩; omega), zero_smul]
    have hf2 : (Function.support (fun j : ℤ =>
        (if a = a ∧ n + j = 0 then -((n : ℂ) * k) else 0) • oscN r k a (m - j) x)).Finite := by
      apply Set.Finite.subset (Set.finite_singleton (-n))
      intro j hj; rw [Function.mem_support] at hj; rw [Set.mem_singleton_iff]
      by_contra hne; apply hj; rw [if_neg (by rintro ⟨_, h⟩; omega), zero_smul]
    rw [finsum_add_distrib hf1 hf2]
    rw [finsumN_gate_collapse (-((n:ℂ)*k)) (fun j => oscN r k a j x) (m + n)
          (fun j => a = a ∧ n + (m - j) = 0) (fun j => by constructor <;> intro h <;> [omega; exact ⟨rfl, by omega⟩]),
        finsumN_gate_collapse (-((n:ℂ)*k)) (fun j => oscN r k a (m - j) x) (-n)
          (fun j => a = a ∧ n + j = 0) (fun j => by constructor <;> intro h <;> [omega; exact ⟨rfl, by omega⟩])]
    rw [show m - -n = m + n from by ring, smul_add, smul_smul, ← add_smul]
    congr 1
    rw [show (1:ℂ) / (2 * k) * -((n:ℂ) * k) + 1 / (2 * k) * -((n:ℂ) * k)
          = -(n:ℂ) * (k / k) from by ring, div_self hk, mul_one]
  · rw [if_neg hab]
    show _ = (0 : End ℂ (FockN r)) x
    rw [show (∑ᶠ j : ℤ, ((if a = b ∧ n + (m - j) = 0 then -((n : ℂ) * k) else 0) • oscN r k a j x
          + (if a = b ∧ n + j = 0 then -((n : ℂ) * k) else 0) • oscN r k a (m - j) x))
        = ∑ᶠ _j : ℤ, (0 : FockN r) from
      finsum_congr fun j => by
        rw [if_neg (by rintro ⟨h, _⟩; exact hab h), if_neg (by rintro ⟨h, _⟩; exact hab h),
          zero_smul, zero_smul, add_zero]]
    rw [finsum_zero, smul_zero]; rfl

/-- **`[Lₘ, aᵇₙ] = -n aᵇ_{m+n}`** (total): only the `a = b` family contributes. -/
theorem LvirN_comm_oscN (r : ℕ) (k : ℂ) (hk : k ≠ 0) (b : Fin r) (m n : ℤ) :
    LvirN r k m * oscN r k b n - oscN r k b n * LvirN r k m = (-(n : ℂ)) • oscN r k b (m + n) := by
  rw [LvirN]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [show (∑ a : Fin r, (LvirNa r k a m * oscN r k b n - oscN r k b n * LvirNa r k a m))
        = ∑ a : Fin r, (if a = b then (-(n : ℂ)) • oscN r k b (m + n) else 0) from
      Finset.sum_congr rfl fun a _ => by
        rw [LvirNa_comm_oscN r k hk a b m n]
        by_cases hab : a = b
        · subst hab; rfl
        · rw [if_neg hab, if_neg hab]]
  rw [Finset.sum_ite_eq' Finset.univ b (fun _ => (-(n : ℂ)) • oscN r k b (m + n))]
  rw [if_pos (Finset.mem_univ b)]

/-- The "move `Lₘ` past a creation `aᵇₙ`" rule. -/
theorem LvirN_oscN (r : ℕ) (k : ℂ) (hk : k ≠ 0) (b : Fin r) (m n : ℤ) (y : FockN r) :
    LvirN r k m (oscN r k b n y) = (-(n : ℂ)) • oscN r k b (m + n) y + oscN r k b n (LvirN r k m y) := by
  have h := congrArg (fun (T : End ℂ (FockN r)) => T y) (LvirN_comm_oscN r k hk b m n)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
  rw [← eq_add_of_sub_eq h]

/-! ## §3  The conformal vector `ωN`, vacuum annihilation, and `L₀ωN = 2ωN`, central charge `r` -/

/-- Each per-family Sugawara term kills the vacuum when `m ≥ -1`. -/
theorem sugTermN_vacuum (r : ℕ) (k : ℂ) (a : Fin r) {m : ℤ} (hm : -1 ≤ m) (j : ℤ) :
    sugTermN r k a m j (vacuumN r) = 0 := by
  rw [sugTermN_apply]
  by_cases hj : j < 0
  · rw [if_pos hj, oscN_vacuum r k a (m - j) (by omega), map_zero]
  · rw [if_neg hj, oscN_vacuum r k a j (by omega), map_zero]

/-- `Lᵃₘ vacuum = 0` for `m ≥ -1` (per-family). -/
theorem LvirNa_vacuum (r : ℕ) (k : ℂ) (a : Fin r) {m : ℤ} (hm : -1 ≤ m) :
    LvirNa r k a m (vacuumN r) = 0 := by
  rw [LvirNa_apply' r k a m (vacuumN r),
    show (∑ᶠ j : ℤ, sugTermN r k a m j (vacuumN r)) = ∑ᶠ _j : ℤ, (0 : FockN r) from
      finsum_congr fun j => sugTermN_vacuum r k a hm j,
    finsum_zero, smul_zero]

/-- `Lₘ vacuum = 0` for `m ≥ -1` (total). -/
theorem LvirN_vacuum (r : ℕ) (k : ℂ) {m : ℤ} (hm : -1 ≤ m) : LvirN r k m (vacuumN r) = 0 := by
  rw [LvirN_apply]
  exact Finset.sum_eq_zero fun a _ => LvirNa_vacuum r k a hm

/-- The **per-family conformal piece** `ωNa = (1/2k) aᵃ₋₁aᵃ₋₁ 1`. -/
noncomputable def ωNa (r : ℕ) (k : ℂ) (a : Fin r) : FockN r :=
  (1 / (2 * k)) • oscN r k a (-1) (oscN r k a (-1) (vacuumN r))

/-- The **conformal vector** `ωN = ∑_a (1/2k) aᵃ₋₁aᵃ₋₁ 1` (Gannon §5.2.2, rank `r`). -/
noncomputable def ωN (r : ℕ) (k : ℂ) : FockN r := ∑ a : Fin r, ωNa r k a

/-- The **central charge** `c = r`. -/
def centralChargeN (r : ℕ) : ℂ := (r : ℂ)

/-- `LvirNa` moves through a creation. -/
theorem LvirNa_oscN_same (r : ℕ) (k : ℂ) (hk : k ≠ 0) (a : Fin r) (m n : ℤ) (y : FockN r) :
    LvirNa r k a m (oscN r k a n y)
      = (-(n : ℂ)) • oscN r k a (m + n) y + oscN r k a n (LvirNa r k a m y) := by
  have h := congrArg (fun (T : End ℂ (FockN r)) => T y) (LvirNa_comm_oscN r k hk a a m n)
  rw [if_pos rfl] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
  rw [← eq_add_of_sub_eq h]

/-- `Lᵃₘ` kills `ωNᵇ` for `b ≠ a` and `m ≥ -1` (cross-family annihilation). -/
theorem LvirNa_ωNa_cross (r : ℕ) (k : ℂ) (hk : k ≠ 0) (a b : Fin r) (hab : a ≠ b) {m : ℤ}
    (hm : -1 ≤ m) : LvirNa r k a m (ωNa r k b) = 0 := by
  rw [ωNa, map_smul]
  have hcross : ∀ (p q : ℤ) (y : FockN r),
      LvirNa r k a m (oscN r k b q y) = oscN r k b q (LvirNa r k a m y) := by
    intro p q y
    have h := congrArg (fun (T : End ℂ (FockN r)) => T y) (LvirNa_comm_oscN r k hk a b m q)
    rw [if_neg hab] at h
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
    rw [sub_eq_zero] at h; rw [h]
  rw [hcross (-1) (-1), hcross (-1) (-1), LvirNa_vacuum r k a hm, map_zero, map_zero, smul_zero]

/-- **`L₀ ωN = 2 ωN`**: `ωN` has conformal weight 2.  Each `ωNa` is an `L₀`-eigenvector of
eigenvalue 2 for its own family `Lᵃ₀`, and is killed by the cross-family `Lᵇ₀`. -/
theorem LvirNa_zero_ωNa_same (r : ℕ) (k : ℂ) (hk : k ≠ 0) (a : Fin r) :
    LvirNa r k a 0 (ωNa r k a) = (2 : ℂ) • ωNa r k a := by
  rw [ωNa, map_smul, LvirNa_oscN_same r k hk a 0 (-1), LvirNa_oscN_same r k hk a 0 (-1) (vacuumN r),
    LvirNa_vacuum r k a (by norm_num : (-1 : ℤ) ≤ 0)]
  simp only [map_zero, add_zero]
  rw [show (0 : ℤ) + -1 = -1 from by ring,
    show (-((-1 : ℤ) : ℂ)) = (1 : ℂ) from by push_cast; ring, one_smul, one_smul]
  rw [smul_add, show (2 : ℂ) = 1 + 1 from by ring, add_smul, one_smul]

/-- `Lᵃₘ` commutes with `aᵇ_q` for `a ≠ b` (pointwise form). -/
theorem LvirNa_oscN_cross (r : ℕ) (k : ℂ) (hk : k ≠ 0) (a b : Fin r) (hab : a ≠ b) (m q : ℤ)
    (y : FockN r) : LvirNa r k a m (oscN r k b q y) = oscN r k b q (LvirNa r k a m y) := by
  have h := congrArg (fun (T : End ℂ (FockN r)) => T y) (LvirNa_comm_oscN r k hk a b m q)
  rw [if_neg hab] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
  rw [sub_eq_zero] at h; exact h

/-! ## §4  The cross-family commuting `[Lᵃₘ, Lᵇₙ] = 0` (a ≠ b) -/

/-- Each per-family Sugawara mode `Lᵇₙ` is a finite normal-ordered sum of `oscN b` pairs;
when pushed through `Lᵃₘ` (a ≠ b), each factor commutes, so `Lᵃₘ Lᵇₙ = Lᵇₙ Lᵃₘ`. -/
theorem LvirNa_comm_LvirNa_cross (r : ℕ) (k : ℂ) (hk : k ≠ 0) (a b : Fin r) (hab : a ≠ b)
    (m n : ℤ) (x : FockN r) :
    LvirNa r k a m (LvirNa r k b n x) = LvirNa r k b n (LvirNa r k a m x) := by
  -- Lᵇₙ y = (1/2k) ∑ᶠ_j Tᵇ_j y, each Tᵇ_j a product of two oscN b factors.
  have hfin_x : (Function.support (fun j : ℤ => sugTermN r k b n j x)).Finite :=
    sugTermN_support_finite r k b n x
  rw [LvirNa_apply' r k b n x, map_smul, map_finsum (LvirNa r k a m) hfin_x]
  rw [LvirNa_apply' r k b n (LvirNa r k a m x)]
  congr 1
  -- push Lᵃₘ through each Tᵇ_j (two cross-family commutations)
  refine finsum_congr fun j => ?_
  rw [sugTermN_apply, sugTermN_apply]
  by_cases hj : j < 0
  · rw [if_pos hj, if_pos hj, LvirNa_oscN_cross r k hk a b hab m j,
      LvirNa_oscN_cross r k hk a b hab m (n - j)]
  · rw [if_neg hj, if_neg hj, LvirNa_oscN_cross r k hk a b hab m (n - j),
      LvirNa_oscN_cross r k hk a b hab m j]

/-! ## §5  The diagonal per-family Virasoro relation `[Lᵃₘ, Lᵃₙ]` with central charge `c = 1` -/

/-- Pushing `Lᵃₘ` through a single Sugawara term `Tᵃ_{n,j}` (two applications of
`LvirNa_oscN_same`, the exact `[Lᵃₘ, aᵃ] = -p·aᵃ` rule). -/
theorem LvirNa_comm_sugTermN_vec (r : ℕ) (k : ℂ) (hk : k ≠ 0) (a : Fin r) (m n j : ℤ)
    (x : FockN r) :
    LvirNa r k a m (sugTermN r k a n j x) - sugTermN r k a n j (LvirNa r k a m x)
      = if j < 0
        then (-(j : ℂ)) • oscN r k a (m + j) (oscN r k a (n - j) x)
              + (-((n - j : ℤ) : ℂ)) • oscN r k a j (oscN r k a (m + (n - j)) x)
        else (-((n - j : ℤ) : ℂ)) • oscN r k a (m + (n - j)) (oscN r k a j x)
              + (-(j : ℂ)) • oscN r k a (n - j) (oscN r k a (m + j) x) := by
  rw [sugTermN_apply, sugTermN_apply]
  by_cases hj : j < 0
  · simp only [if_pos hj]
    rw [LvirNa_oscN_same r k hk a m j (oscN r k a (n - j) x),
        LvirNa_oscN_same r k hk a m (n - j) x, map_add, map_smul]
    abel
  · simp only [if_neg hj]
    rw [LvirNa_oscN_same r k hk a m (n - j) (oscN r k a j x),
        LvirNa_oscN_same r k hk a m j x, map_add, map_smul]
    abel

/-- The commutator `[Lᵃₘ, Lᵃₙ]` acting on a vector, as the finite sum of per-term brackets. -/
theorem LvirNa_comm_eq_finsum (r : ℕ) (k : ℂ) (a : Fin r) (m n : ℤ) (x : FockN r) :
    LvirNa r k a m (LvirNa r k a n x) - LvirNa r k a n (LvirNa r k a m x)
      = (1 / (2 * k)) • ∑ᶠ j : ℤ,
          (LvirNa r k a m (sugTermN r k a n j x) - sugTermN r k a n j (LvirNa r k a m x)) := by
  have hfin_x : (Function.support (fun j : ℤ => sugTermN r k a n j x)).Finite :=
    sugTermN_support_finite r k a n x
  have hfin_Lx : (Function.support (fun j : ℤ => sugTermN r k a n j (LvirNa r k a m x))).Finite :=
    sugTermN_support_finite r k a n (LvirNa r k a m x)
  have hfin_mx : (Function.support (fun j : ℤ => LvirNa r k a m (sugTermN r k a n j x))).Finite :=
    hfin_x.subset (fun j hj => by
      rw [Function.mem_support] at hj ⊢; exact fun h => hj (by rw [h, map_zero]))
  rw [LvirNa_apply' r k a n x, map_smul, map_finsum (LvirNa r k a m) hfin_x,
    LvirNa_apply' r k a n (LvirNa r k a m x), ← smul_sub]
  congr 1
  rw [← finsum_sub_distrib hfin_mx hfin_Lx]

/-! ### The shifted-gate boundary window (per-family port of `HeisenbergCentral`) -/

/-- `oscN_comm` acting on a vector (same family): `aᵃ_p (aᵃ_q x) = aᵃ_q (aᵃ_p x) + δ_{p+q,0}(p k) x`. -/
theorem oscN_swap (r : ℕ) (k : ℂ) (a : Fin r) (p q : ℤ) (x : FockN r) :
    oscN r k a p (oscN r k a q x) = oscN r k a q (oscN r k a p x)
      + (if p + q = 0 then (p : ℂ) * k else 0) • x := by
  have h := congrArg (fun (T : End ℂ (FockN r)) => T x) (oscN_comm r k a a p q)
  simp only [eq_self_iff_true, true_and, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, LinearMap.id_apply] at h
  -- h : aᵃ_p (aᵃ_q x) - aᵃ_q (aᵃ_p x) = (if p+q=0 then p k else 0) • x
  rw [sub_eq_iff_eq_add.mp h, add_comm]

/-- The shift equivalence `i ↦ i - m`. -/
def shiftIdxN (m : ℤ) : ℤ ≃ ℤ where
  toFun i := i - m
  invFun i := i + m
  left_inv i := by dsimp only; ring
  right_inv i := by dsimp only; ring

@[simp] theorem shiftIdxN_apply (m i : ℤ) : shiftIdxN m i = i - m := rfl

/-- The shifted-gate ordered pair `tilSN_i = aᵃ_i aᵃ_{m+n-i}` with gate `i < m`. -/
noncomputable def tilSN (r : ℕ) (k : ℂ) (a : Fin r) (m n i : ℤ) (x : FockN r) : FockN r :=
  if i < m then oscN r k a i (oscN r k a (m + n - i) x) else oscN r k a (m + n - i) (oscN r k a i x)

/-- The `F`-family of the per-term bracket. -/
noncomputable def FfamN (r : ℕ) (k : ℂ) (a : Fin r) (m n j : ℤ) (x : FockN r) : FockN r :=
  (-(j : ℂ)) • (if j < 0 then oscN r k a (m + j) (oscN r k a (n - j) x)
                else oscN r k a (n - j) (oscN r k a (m + j) x))

/-- The `G`-family `= -(n-j)·Tᵃ_{m+n,j}`. -/
noncomputable def GfamN (r : ℕ) (k : ℂ) (a : Fin r) (m n j : ℤ) (x : FockN r) : FockN r :=
  (-((n - j : ℤ) : ℂ)) • sugTermN r k a (m + n) j x

theorem RN_eq_F_add_G (r : ℕ) (k : ℂ) (hk : k ≠ 0) (a : Fin r) (m n j : ℤ) (x : FockN r) :
    LvirNa r k a m (sugTermN r k a n j x) - sugTermN r k a n j (LvirNa r k a m x)
      = FfamN r k a m n j x + GfamN r k a m n j x := by
  rw [LvirNa_comm_sugTermN_vec r k hk a m n j x, FfamN, GfamN, sugTermN_apply]
  by_cases hj : j < 0
  · simp only [if_pos hj]
    rw [show m + (n - j) = m + n - j from by ring]
  · simp only [if_neg hj]
    rw [show m + (n - j) = m + n - j from by ring]
    abel

theorem FfamN_reindex (r : ℕ) (k : ℂ) (a : Fin r) (m n i : ℤ) (x : FockN r) :
    FfamN r k a m n (i - m) x = (-((i - m : ℤ) : ℂ)) • tilSN r k a m n i x := by
  rw [FfamN, tilSN]
  congr 1
  by_cases hi : i < m
  · rw [if_pos (by omega), if_pos hi,
      show m + (i - m) = i from by ring, show n - (i - m) = m + n - i from by ring]
  · rw [if_neg (by omega), if_neg hi,
      show m + (i - m) = i from by ring, show n - (i - m) = m + n - i from by ring]

theorem SN_sub_tilSN (r : ℕ) (k : ℂ) (a : Fin r) (m n i : ℤ) (x : FockN r) :
    sugTermN r k a (m + n) i x - tilSN r k a m n i x
      = (if m + n = 0 then
          (if (i < 0 ∧ ¬ i < m) then (i : ℂ) * k
           else if (¬ i < 0 ∧ i < m) then -((i : ℂ) * k) else 0)
        else 0) • x := by
  rw [sugTermN_apply, tilSN]
  have hPQ : oscN r k a i (oscN r k a (m + n - i) x) - oscN r k a (m + n - i) (oscN r k a i x)
      = (if m + n = 0 then (i : ℂ) * k else 0) • x := by
    have h := oscN_swap r k a i (m + n - i) x
    rw [show i + (m + n - i) = m + n from by ring] at h
    rw [h]; abel
  by_cases hmn : m + n = 0
  · rw [if_pos hmn] at hPQ ⊢
    by_cases h0 : i < 0 <;> by_cases hm : i < m
    · rw [if_pos h0, if_pos hm, sub_self, if_neg (by tauto), if_neg (by tauto), zero_smul]
    · rw [if_pos h0, if_neg hm, hPQ, if_pos (show i < 0 ∧ ¬ i < m from ⟨h0, hm⟩)]
    · rw [if_neg h0, if_pos hm, if_neg (show ¬(i < 0 ∧ ¬ i < m) from by tauto),
          if_pos (show ¬ i < 0 ∧ i < m from ⟨h0, hm⟩)]
      rw [show oscN r k a (m + n - i) (oscN r k a i x) - oscN r k a i (oscN r k a (m + n - i) x)
            = -(oscN r k a i (oscN r k a (m + n - i) x)
                - oscN r k a (m + n - i) (oscN r k a i x)) from by abel,
          hPQ, neg_smul]
    · rw [if_neg h0, if_neg hm, sub_self, if_neg (by tauto), if_neg (by tauto), zero_smul]
  · rw [if_neg hmn, zero_smul]
    by_cases h0 : i < 0 <;> by_cases hm : i < m
    · rw [if_pos h0, if_pos hm, sub_self]
    · rw [if_pos h0, if_neg hm, hPQ, if_neg hmn, zero_smul]
    · rw [if_neg h0, if_pos hm]
      rw [show oscN r k a (m + n - i) (oscN r k a i x) - oscN r k a i (oscN r k a (m + n - i) x)
            = -(oscN r k a i (oscN r k a (m + n - i) x)
                - oscN r k a (m + n - i) (oscN r k a i x)) from by abel,
          hPQ, if_neg hmn, zero_smul, neg_zero]
    · rw [if_neg h0, if_neg hm, sub_self]

/-! ### Finiteness of the families -/

theorem GfamN_support_finite (r : ℕ) (k : ℂ) (a : Fin r) (m n : ℤ) (x : FockN r) :
    (Function.support (fun j : ℤ => GfamN r k a m n j x)).Finite := by
  apply Set.Finite.subset (sugTermN_support_finite r k a (m + n) x)
  intro j hj
  rw [Function.mem_support] at hj ⊢
  rw [GfamN] at hj
  exact fun h => hj (by rw [h, smul_zero])

theorem weightedSN_support_finite (r : ℕ) (k : ℂ) (a : Fin r) (s : ℤ) (c : ℤ → ℂ) (x : FockN r) :
    (Function.support (fun i : ℤ => c i • sugTermN r k a s i x)).Finite := by
  apply Set.Finite.subset (sugTermN_support_finite r k a s x)
  intro i hi
  rw [Function.mem_support] at hi ⊢
  exact fun h => hi (by rw [h, smul_zero])

theorem RN_support_finite (r : ℕ) (k : ℂ) (a : Fin r) (m n : ℤ) (x : FockN r) :
    (Function.support (fun j : ℤ =>
      LvirNa r k a m (sugTermN r k a n j x) - sugTermN r k a n j (LvirNa r k a m x))).Finite := by
  apply Set.Finite.subset
    ((sugTermN_support_finite r k a n x).union (sugTermN_support_finite r k a n (LvirNa r k a m x)))
  intro j hj
  rw [Function.mem_support] at hj
  rw [Set.mem_union, Function.mem_support, Function.mem_support]
  by_contra h
  push_neg at h
  apply hj
  rw [h.1, h.2, map_zero, sub_zero]

theorem FfamN_support_finite (r : ℕ) (k : ℂ) (hk : k ≠ 0) (a : Fin r) (m n : ℤ) (x : FockN r) :
    (Function.support (fun j : ℤ => FfamN r k a m n j x)).Finite := by
  apply Set.Finite.subset ((RN_support_finite r k a m n x).union (GfamN_support_finite r k a m n x))
  intro j hj
  rw [Function.mem_support] at hj
  rw [Set.mem_union, Function.mem_support, Function.mem_support]
  by_contra h
  push_neg at h
  apply hj
  have hR := RN_eq_F_add_G r k hk a m n j x
  rw [h.1, h.2] at hR
  rw [add_zero] at hR
  exact hR.symm

theorem reindexedFN_support_finite (r : ℕ) (k : ℂ) (hk : k ≠ 0) (a : Fin r) (m n : ℤ)
    (x : FockN r) :
    (Function.support (fun i : ℤ => (-((i - m : ℤ) : ℂ)) • tilSN r k a m n i x)).Finite := by
  have hF := FfamN_support_finite r k hk a m n x
  apply Set.Finite.subset (hF.image (fun j => j + m))
  intro i hi
  rw [Function.mem_support, ← FfamN_reindex] at hi
  rw [Set.mem_image]
  exact ⟨i - m, by rw [Function.mem_support]; exact hi, by ring⟩

/-- The bracket as bulk `(m-n)Lᵃ_{m+n}` plus the finite boundary window. -/
theorem LvirNa_comm_bulk_window (r : ℕ) (k : ℂ) (hk : k ≠ 0) (a : Fin r) (m n : ℤ) (x : FockN r) :
    LvirNa r k a m (LvirNa r k a n x) - LvirNa r k a n (LvirNa r k a m x)
      = (((m : ℂ) - n) • LvirNa r k a (m + n) x)
        + (1 / (2 * k)) • ∑ᶠ i : ℤ,
            (((i : ℂ) - m) • (sugTermN r k a (m + n) i x - tilSN r k a m n i x)) := by
  rw [LvirNa_comm_eq_finsum r k a m n x]
  rw [show (∑ᶠ j : ℤ, (LvirNa r k a m (sugTermN r k a n j x) - sugTermN r k a n j (LvirNa r k a m x)))
        = ∑ᶠ j : ℤ, (FfamN r k a m n j x + GfamN r k a m n j x) from
      finsum_congr fun j => RN_eq_F_add_G r k hk a m n j x]
  rw [finsum_add_distrib (FfamN_support_finite r k hk a m n x) (GfamN_support_finite r k a m n x)]
  rw [show (∑ᶠ j : ℤ, FfamN r k a m n j x)
        = ∑ᶠ i : ℤ, (-((i - m : ℤ) : ℂ)) • tilSN r k a m n i x from by
      rw [← finsum_comp_equiv (shiftIdxN m) (f := fun j => FfamN r k a m n j x)]
      exact finsum_congr fun i => by rw [shiftIdxN_apply, FfamN_reindex]]
  rw [show (∑ᶠ j : ℤ, GfamN r k a m n j x)
        = ∑ᶠ j : ℤ, (-((n - j : ℤ) : ℂ)) • sugTermN r k a (m + n) j x from
      finsum_congr fun j => by rw [GfamN]]
  rw [← finsum_add_distrib (reindexedFN_support_finite r k hk a m n x)
        (weightedSN_support_finite r k a (m + n) (fun i => -((n - i : ℤ) : ℂ)) x)]
  rw [show (∑ᶠ i : ℤ, ((-((i - m : ℤ) : ℂ)) • tilSN r k a m n i x
              + (-((n - i : ℤ) : ℂ)) • sugTermN r k a (m + n) i x))
        = ∑ᶠ i : ℤ, (((m : ℂ) - n) • sugTermN r k a (m + n) i x
              + ((i : ℂ) - m) • (sugTermN r k a (m + n) i x - tilSN r k a m n i x)) from
      finsum_congr fun i => by push_cast; module]
  rw [finsum_add_distrib
      (weightedSN_support_finite r k a (m + n) (fun i => (m : ℂ) - n) x)
      (by
        apply Set.Finite.subset
          ((weightedSN_support_finite r k a (m + n) (fun i => (i : ℂ) - m) x).union
            (reindexedFN_support_finite r k hk a m n x))
        intro i hi
        rw [Function.mem_support] at hi
        rw [Set.mem_union, Function.mem_support, Function.mem_support]
        by_contra h; push_neg at h; apply hi
        obtain ⟨h1, h2⟩ := h
        have h2' : ((i : ℂ) - m) • tilSN r k a m n i x = 0 := by
          have : (-((i - m : ℤ) : ℂ)) • tilSN r k a m n i x = 0 := h2
          rw [neg_smul, neg_eq_zero] at this
          rw [show ((i : ℂ) - m) = ((i - m : ℤ) : ℂ) from by push_cast; ring]
          exact this
        rw [smul_sub, h1, h2', sub_zero])]
  rw [smul_add]
  congr 1
  · rw [LvirNa_apply' r k a (m + n) x,
      ← smul_finsum' ((m : ℂ) - n) (sugTermN_support_finite r k a (m + n) x),
      smul_smul, smul_smul]
    congr 1; ring

end HeisenbergN

end VOA
