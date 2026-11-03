/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.HeisenbergTwistedModuleFieldComm
import VOA.Core.LocalSystemAction

/-!
# Twisted products of local fields and their commutator formula  (Moonshine step M6a)

For a field `A` and `α ∈ ℂ` the **twisted product** (the rescaled form of Li's twisted
`n`-th products)

  `star α A p X = Σ_{i ≥ 0} C(−α, i) z^{−i} A₍ₚ₊ᵢ₎X`,

i.e. `Y⋆(A, z₀) X = (1 + z₀/z)^{−α} Y(A, z₀) X`, is a finite sum as soon as `A` and `X` are local.
For a rescaled twisted vertex operator `Ã = z^{j/N} Y_M(u, z)` the twisted product formula of
`TwistedReduction` reads `star (j/N) Ã ℓ B̃ = Ỹ(u₍ℓ₎v)`: in the `star` products the twisted
vertex operator becomes a homomorphism.

* `star`, `star_eq_sum_range`, `star_mem` — definition, finiteness, closure in a local system.
* `star_comm` — **the twisted commutator formula**: for `A, B, C` in the local system generated
  by a pairwise local set and `α, β ∈ ℂ`,
  `star α A p (star β B q C) − star β B q (star α A p C)
     = Σ_s C(p, s) · star (α + β) (star α A s B) (p + q − s) C`.
  It follows from the untwisted commutator formula (`prod_comm_formula`), the binomial expansion of
  `zᶜ` in the first slot (`prod_fzmul_left`), and the binomial identity
  `Σ_{i+k=J} C(−α,i)C(−β,k)C(p+i,σ) = Σ_{s+r=σ} C(p,s)C(−α,r)C(−α−β−r, J−r)`
  (`star_comm_coeff`).
* `star_fzmul_right`, `star_one` — `zᶜ` commutes with `star` in the second slot; the twisted
  products with the identity field.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u

namespace TwistedReduction

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## The twisted product -/

/-- **The twisted product** `star α A p X = Σ_i C(−α,i) z^{−i} A₍ₚ₊ᵢ₎X`. -/
noncomputable def star (α : ℂ) (A : Fld M) (p : ℤ) (X : Fld M) : Fld M :=
  ∑ᶠ i : ℕ, cbinom (-α) i • fzmul (-(i : ℤ)) (Fld.prod (p + i) A X)

theorem star_eq_sum_range (α : ℂ) (A : Fld M) (p : ℤ) (X : Fld M) (K : ℕ)
    (hK : ∀ i : ℕ, K ≤ i → Fld.prod (p + i) A X = 0) :
    star α A p X = ∑ i ∈ Finset.range K, cbinom (-α) i • fzmul (-(i : ℤ)) (Fld.prod (p + i) A X) :=
  finsum_nat_eq_sum_range K _ (fun i hi => by rw [hK i hi, fzmul_zero, smul_zero])

/-- Local products eventually vanish, in the offset form used by `star`. -/
theorem exists_prod_offset_zero {A X : Fld M} (h : Local A.1 X.1) (p : ℤ) :
    ∃ K : ℕ, ∀ i : ℕ, K ≤ i → Fld.prod (p + i) A X = 0 := by
  obtain ⟨N0, hN0⟩ := Fld.prod_eventually_zero_of_local h
  exact ⟨(N0 - p).toNat, fun i hi => hN0 _ (by omega)⟩

theorem sum_mem_tgenerated {ι : Type*} {S : Set (Fld M)} (s : Finset ι) (f : ι → Fld M)
    (h : ∀ i ∈ s, f i ∈ TGenerated S) : ∑ i ∈ s, f i ∈ TGenerated S :=
  Finset.sum_induction _ (· ∈ TGenerated S) (fun _ _ ha hb => add_mem_tgenerated ha hb)
    (zero_mem_tgenerated _) h

theorem sub_mem_tgenerated {S : Set (Fld M)} {a b : Fld M} (ha : a ∈ TGenerated S)
    (hb : b ∈ TGenerated S) : a - b ∈ TGenerated S := by
  rw [sub_eq_add_neg, show -b = (-1 : ℂ) • b by simp]
  exact add_mem_tgenerated ha (smul_mem_tgenerated _ hb)

theorem star_mem {S : Set (Fld M)} (hS : ∀ a ∈ S, ∀ b ∈ S, Local a.1 b.1) {A X : Fld M}
    (hA : A ∈ TGenerated S) (hX : X ∈ TGenerated S) (α : ℂ) (p : ℤ) :
    star α A p X ∈ TGenerated S := by
  obtain ⟨K, hK⟩ := exists_prod_offset_zero (tgenerated_local hS hA hX) p
  rw [star_eq_sum_range α A p X K hK]
  exact sum_mem_tgenerated _ _ fun i _ => smul_mem_tgenerated _
    (fzmul_mem_tgenerated _ (prod_mem_tgenerated _ hA hX))

/-- `zᶜ ·` as an additive map. -/
noncomputable def fzmulHom (c : ℤ) : Fld M →+ Fld M where
  toFun := fzmul c
  map_zero' := fzmul_zero c
  map_add' := fzmul_add c

theorem fzmulHom_injective (c : ℤ) : Function.Injective (fzmulHom (M := M) c) := by
  intro a b h
  have h' := congrArg (fzmul (-c)) h
  simp only [fzmulHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, fzmul_fzmul, neg_add_cancel,
    fzmul_zero_shift] at h'
  exact h'

theorem fzmul_finsum {ι : Type*} (c : ℤ) (f : ι → Fld M) :
    fzmul c (∑ᶠ i, f i) = ∑ᶠ i, fzmul c (f i) :=
  AddMonoidHom.map_finsum_of_injective (fzmulHom c) (fzmulHom_injective c) f

/-- `zᶜ` commutes with `star` in the second slot. -/
theorem star_fzmul_right (α : ℂ) (A : Fld M) (p c : ℤ) (X : Fld M) :
    star α A p (fzmul c X) = fzmul c (star α A p X) := by
  rw [star, star, fzmul_finsum]
  refine finsum_congr fun i => ?_
  rw [prod_fzmul_right, fzmul_fzmul, fzmul_smul, fzmul_fzmul, add_comm]

/-! ## Finite-sum reorganisation -/

omit [Module ℂ M] in
/-- Reindexing an antidiagonal sum whose summand vanishes for first index `< r`. -/
theorem sum_antidiagonal_shift (f : ℕ × ℕ → M) {r J : ℕ} (hrJ : r ≤ J)
    (hf : ∀ i k : ℕ, i < r → f (i, k) = 0) :
    ∑ ik ∈ Finset.antidiagonal J, f ik
      = ∑ ik ∈ Finset.antidiagonal (J - r), f (r + ik.1, ik.2) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Finset.sum_range_add_sum_Ico _ (show r ≤ J + 1 by omega),
    Finset.sum_eq_zero (fun i hi => hf i _ (Finset.mem_range.mp hi)), zero_add,
    Finset.sum_Ico_eq_sum_range, show J + 1 - r = J - r + 1 by omega]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show J - (r + i) = J - r - i by omega]

/-- Shifting the second index of a coefficient family. -/
theorem sum_range_add_shift (W : ℕ → M) (f : ℕ → ℂ) (r K : ℕ)
    (hW : ∀ J : ℕ, K ≤ J → W J = 0) :
    ∑ J ∈ Finset.range K, f J • W (J + r)
      = ∑ J' ∈ Finset.range K, (if r ≤ J' then f (J' - r) else 0) • W J' := by
  rw [sum_range_shift (fun J' => (if r ≤ J' then f (J' - r) else 0) • W J') r K
    (fun J' hJ' => by simp only; rw [if_neg (by omega), zero_smul])
    (fun J hJ => by simp only; rw [hW _ hJ, smul_zero])]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [if_pos (by omega), Nat.add_sub_cancel_left, add_comm]

/-- **The reorganisation behind the twisted commutator formula**: a triple sum indexed by
`(i, k, s)` against `W s (i+k)` and a quadruple sum indexed by `(s, m, r, t)` against
`W (s+r) (m+r+t)` agree once their coefficients agree on every `(σ, J)`. -/
theorem reorg (W : ℕ → ℕ → M) (L K : ℕ) (hLK : L ≤ K)
    (hW1 : ∀ σ J : ℕ, L ≤ σ → W σ J = 0) (hW2 : ∀ σ J : ℕ, K ≤ J → W σ J = 0)
    (a : ℕ → ℕ → ℕ → ℂ) (b : ℕ → ℕ → ℕ → ℕ → ℂ)
    (hcoef : ∀ σ J : ℕ, σ < L → J < K →
      ∑ ik ∈ Finset.antidiagonal J, a ik.1 ik.2 σ
        = ∑ sr ∈ Finset.antidiagonal σ, (if sr.2 ≤ J then
            ∑ mt ∈ Finset.antidiagonal (J - sr.2), b sr.1 mt.1 sr.2 mt.2 else 0)) :
    ∑ i ∈ Finset.range K, ∑ k ∈ Finset.range K, ∑ s ∈ Finset.range L, a i k s • W s (i + k)
      = ∑ s ∈ Finset.range L, ∑ m ∈ Finset.range K, ∑ r ∈ Finset.range K,
          ∑ t ∈ Finset.range K, b s m r t • W (s + r) (m + r + t) := by
  -- the left side, regrouped by `J = i + k`
  have hL : ∑ i ∈ Finset.range K, ∑ k ∈ Finset.range K, ∑ s ∈ Finset.range L, a i k s • W s (i + k)
      = ∑ s ∈ Finset.range L, ∑ J ∈ Finset.range K,
          (∑ ik ∈ Finset.antidiagonal J, a ik.1 ik.2 s) • W s J := by
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm), Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [sum_range_sq_eq_sum_antidiagonal K (fun i k => a i k s • W s (i + k))
      (fun i k h => by beta_reduce; rw [hW2 _ _ h, smul_zero])]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun ik hik => ?_
    rw [Finset.mem_antidiagonal] at hik
    rw [hik]
  -- the right side
  have hG : ∀ s r : ℕ, ∑ m ∈ Finset.range K, ∑ t ∈ Finset.range K,
        b s m r t • W (s + r) (m + r + t)
      = ∑ J' ∈ Finset.range K, (if r ≤ J' then
          ∑ mt ∈ Finset.antidiagonal (J' - r), b s mt.1 r mt.2 else 0) • W (s + r) J' := by
    intro s r
    rw [sum_range_sq_eq_sum_antidiagonal K (fun m t => b s m r t • W (s + r) (m + r + t))
      (fun m t h => by beta_reduce; rw [hW2 _ _ (by omega), smul_zero])]
    rw [← sum_range_add_shift (W (s + r)) (fun J => ∑ mt ∈ Finset.antidiagonal J, b s mt.1 r mt.2)
      r K (fun J hJ => hW2 _ _ hJ)]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun mt hmt => ?_
    rw [Finset.mem_antidiagonal] at hmt
    rw [show mt.1 + r + mt.2 = J + r by omega]
  have hR : ∑ s ∈ Finset.range L, ∑ m ∈ Finset.range K, ∑ r ∈ Finset.range K,
        ∑ t ∈ Finset.range K, b s m r t • W (s + r) (m + r + t)
      = ∑ σ ∈ Finset.range L, ∑ J' ∈ Finset.range K, (∑ sr ∈ Finset.antidiagonal σ,
          (if sr.2 ≤ J' then ∑ mt ∈ Finset.antidiagonal (J' - sr.2), b sr.1 mt.1 sr.2 mt.2
            else 0)) • W σ J' := by
    rw [Finset.sum_congr rfl (fun s _ => Finset.sum_comm)]
    simp only [hG]
    rw [Finset.sum_congr rfl (fun s _ => sum_range_eq_of_vanish _ hLK (fun r hr =>
      Finset.sum_eq_zero fun J' _ => by rw [hW1 _ _ (by omega), smul_zero]))]
    rw [sum_range_sq_eq_sum_antidiagonal L (fun s r => ∑ J' ∈ Finset.range K,
      (if r ≤ J' then ∑ mt ∈ Finset.antidiagonal (J' - r), b s mt.1 r mt.2 else 0)
        • W (s + r) J')
      (fun s r h => Finset.sum_eq_zero fun J' _ => by rw [hW1 _ _ h, smul_zero])]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun J' _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun sr hsr => ?_
    rw [Finset.mem_antidiagonal] at hsr
    rw [hsr]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun σ hσ => Finset.sum_congr rfl fun J hJ => ?_
  rw [hcoef σ J (Finset.mem_range.mp hσ) (Finset.mem_range.mp hJ)]

/-! ## The binomial identity -/

/-- The inner binomial sum `Σ_{i+k=J} C(−α,i) C(i,r) C(−β,k)`. -/
theorem star_inner_coeff (α β : ℂ) (r J : ℕ) :
    ∑ ik ∈ Finset.antidiagonal J, cbinom (-α) ik.1 * cbinom (ik.1 : ℂ) r * cbinom (-β) ik.2
      = if r ≤ J then cbinom (-α) r * cbinom (-α - r + -β) (J - r) else 0 := by
  split_ifs with hrJ
  · rw [sum_antidiagonal_shift (fun ik => cbinom (-α) ik.1 * cbinom (ik.1 : ℂ) r *
        cbinom (-β) ik.2) hrJ (fun i k hi => by simp only; rw [cbinom_natCast_of_lt hi]; ring),
      ← gBinom_vandermonde, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ik _ => ?_
    have h := cbinom_mul_choose (-α) r ik.1
    push_cast at h ⊢
    rw [h, mul_assoc]
  · refine Finset.sum_eq_zero fun ik hik => ?_
    rw [Finset.mem_antidiagonal] at hik
    rw [cbinom_natCast_of_lt (by omega)]
    ring

/-- **The coefficient identity of the twisted commutator formula.** -/
theorem star_comm_coeff (α β : ℂ) (p : ℤ) (σ J : ℕ) :
    ∑ ik ∈ Finset.antidiagonal J, cbinom (-α) ik.1 * cbinom (-β) ik.2 * gBinom (p + ik.1) σ
      = ∑ sr ∈ Finset.antidiagonal σ, (if sr.2 ≤ J then
          ∑ mt ∈ Finset.antidiagonal (J - sr.2), gBinom p sr.1 * cbinom (-(α + β)) mt.1
            * cbinom (-α) sr.2 * gBinom (-(sr.2 : ℤ)) mt.2 else 0) := by
  have hsplit : ∀ i : ℕ, gBinom (p + i) σ
      = ∑ sr ∈ Finset.antidiagonal σ, gBinom p sr.1 * cbinom (i : ℂ) sr.2 := by
    intro i
    rw [gBinom_eq_cbinom, Int.cast_add, Int.cast_natCast, cbinom_add]
    rfl
  simp only [hsplit, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun sr _ => ?_
  have hI := star_inner_coeff α β sr.2 J
  split_ifs with hrJ
  · rw [if_pos hrJ] at hI
    have hV : ∑ mt ∈ Finset.antidiagonal (J - sr.2), gBinom p sr.1 * cbinom (-(α + β)) mt.1
            * cbinom (-α) sr.2 * gBinom (-(sr.2 : ℤ)) mt.2
        = gBinom p sr.1 * cbinom (-α) sr.2 * cbinom (-(α + β) + -(sr.2 : ℂ)) (J - sr.2) := by
      rw [← gBinom_vandermonde, Finset.mul_sum]
      refine Finset.sum_congr rfl fun mt _ => ?_
      simp only [gBinom_eq_cbinom]
      push_cast
      ring
    rw [hV, show -(α + β) + -(sr.2 : ℂ) = -α - sr.2 + -β by ring, mul_assoc, ← hI,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun ik _ => ?_
    ring
  · rw [if_neg hrJ] at hI
    rw [show (∑ ik ∈ Finset.antidiagonal J, cbinom (-α) ik.1 * cbinom (-β) ik.2
        * (gBinom p sr.1 * cbinom (ik.1 : ℂ) sr.2))
        = gBinom p sr.1 * ∑ ik ∈ Finset.antidiagonal J,
            cbinom (-α) ik.1 * cbinom (ik.1 : ℂ) sr.2 * cbinom (-β) ik.2 by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun ik _ => by ring, hI, mul_zero]

/-! ## The twisted commutator formula -/

/-- **The twisted commutator formula.**  For `A, B, C` in the twisted local system generated by
a pairwise local set, and `L` beyond which the products `A₍ₛ₎B` vanish,
`star α A p (star β B q C) − star β B q (star α A p C)
   = Σ_{s<L} C(p,s) · star (α+β) (star α A s B) (p+q−s) C`. -/
theorem star_comm {S : Set (Fld M)} (hS : ∀ a ∈ S, ∀ b ∈ S, Local a.1 b.1) {A B C : Fld M}
    (hA : A ∈ TGenerated S) (hB : B ∈ TGenerated S) (hC : C ∈ TGenerated S) (α β : ℂ)
    (p q : ℤ) (L : ℕ) (hL : ∀ s : ℕ, L ≤ s → Fld.prod s A B = 0) :
    star α A p (star β B q C) - star β B q (star α A p C)
      = ∑ s ∈ Finset.range L, gBinom p s • star (α + β) (star α A s B) (p + q - s) C := by
  have loc : ∀ {a b : Fld M}, a ∈ TGenerated S → b ∈ TGenerated S → Local a.1 b.1 :=
    fun ha hb => tgenerated_local hS ha hb
  obtain ⟨KB, hKB⟩ := exists_prod_offset_zero (loc hB hC) q
  obtain ⟨KA0, hKA0⟩ := exists_prod_offset_zero (loc hA hC) p
  obtain ⟨cA, hcA⟩ := exists_uniform_bound (fun k n => Fld.prod n A (Fld.prod (q + k) B C) = 0)
    KB (fun k _ => Fld.prod_eventually_zero_of_local (loc hA (prod_mem_tgenerated _ hB hC)))
  obtain ⟨cB, hcB⟩ := exists_uniform_bound (fun i n => Fld.prod n B (Fld.prod (p + i) A C) = 0)
    KA0 (fun i _ => Fld.prod_eventually_zero_of_local (loc hB (prod_mem_tgenerated _ hA hC)))
  obtain ⟨cW, hcW⟩ := exists_uniform_bound (fun σ n => Fld.prod n (Fld.prod σ A B) C = 0)
    L (fun σ _ => Fld.prod_eventually_zero_of_local (loc (prod_mem_tgenerated _ hA hB) hC))
  have hnat : ∀ c : ℤ, ∃ n : ℕ, c ≤ n ∧ -c ≤ n := fun c => ⟨c.natAbs, by omega, by omega⟩
  obtain ⟨nA, hnA, -⟩ := hnat cA
  obtain ⟨nB, hnB, -⟩ := hnat cB
  obtain ⟨nW, hnW, -⟩ := hnat cW
  obtain ⟨np, hnp1, hnp2⟩ := hnat p
  obtain ⟨nq, hnq1, hnq2⟩ := hnat q
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = KB + KA0 + nA + nB + nW + np + nq + L + 1 := ⟨_, rfl⟩
  -- vanishing in the forms used below
  have vBC : ∀ k : ℕ, K ≤ k → Fld.prod (q + k) B C = 0 := fun k hk => hKB k (by omega)
  have vAC : ∀ i : ℕ, K ≤ i → Fld.prod (p + i) A C = 0 := fun i hi => hKA0 i (by omega)
  have vABC : ∀ i k : ℕ, K ≤ i → Fld.prod (p + i) A (Fld.prod (q + k) B C) = 0 := by
    intro i k hi
    by_cases hk : k < KB
    · exact hcA k hk _ (by omega)
    · rw [hKB k (by omega), prod_zero_right]
  have vBAC : ∀ i k : ℕ, K ≤ k → Fld.prod (q + k) B (Fld.prod (p + i) A C) = 0 := by
    intro i k hk
    by_cases hi : i < KA0
    · exact hcB i hi _ (by omega)
    · rw [hKA0 i (by omega), prod_zero_right]
  have vAB : ∀ s r : ℕ, L ≤ s + r → Fld.prod ((s : ℤ) + r) A B = 0 := fun s r h => by
    have := hL (s + r) h
    push_cast at this
    exact this
  have vW : ∀ σ : ℕ, ∀ n : ℤ, p + q - L + K ≤ n → Fld.prod n (Fld.prod σ A B) C = 0 := by
    intro σ n hn
    by_cases hσ : σ < L
    · exact hcW σ hσ _ (by omega)
    · rw [hL σ (by omega), prod_zero_left]
  -- the left side
  have e3 : star α A p (star β B q C) = ∑ i ∈ Finset.range K, ∑ k ∈ Finset.range K,
      (cbinom (-α) i * cbinom (-β) k) •
        fzmul (-((i : ℤ) + k)) (Fld.prod (p + i) A (Fld.prod (q + k) B C)) := by
    rw [star_eq_sum_range β B q C K vBC, star_eq_sum_range α A p _ K (fun i hi => by
      rw [prod_sum_right]
      exact Finset.sum_eq_zero fun k _ => by
        rw [Fld.prod_smul_right, prod_fzmul_right, vABC i k hi, fzmul_zero, smul_zero])]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [prod_sum_right, fzmul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fld.prod_smul_right, prod_fzmul_right, fzmul_smul, fzmul_fzmul, smul_smul,
      show -(i : ℤ) + -(k : ℤ) = -((i : ℤ) + k) by ring]
  have e4 : star β B q (star α A p C) = ∑ i ∈ Finset.range K, ∑ k ∈ Finset.range K,
      (cbinom (-α) i * cbinom (-β) k) •
        fzmul (-((i : ℤ) + k)) (Fld.prod (q + k) B (Fld.prod (p + i) A C)) := by
    rw [star_eq_sum_range α A p C K vAC, star_eq_sum_range β B q _ K (fun k hk => by
      rw [prod_sum_right]
      exact Finset.sum_eq_zero fun i _ => by
        rw [Fld.prod_smul_right, prod_fzmul_right, vBAC i k hk, fzmul_zero, smul_zero]),
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [prod_sum_right, fzmul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fld.prod_smul_right, prod_fzmul_right, fzmul_smul, fzmul_fzmul, smul_smul,
      show -(k : ℤ) + -(i : ℤ) = -((i : ℤ) + k) by ring, mul_comm]
  -- the two sides as combinations of `W σ J`
  set W : ℕ → ℕ → Fld M := fun σ J =>
    fzmul (-(J : ℤ)) (Fld.prod (p + q + J - σ) (Fld.prod σ A B) C) with hWdef
  have hLHS : star α A p (star β B q C) - star β B q (star α A p C)
      = ∑ i ∈ Finset.range K, ∑ k ∈ Finset.range K, ∑ s ∈ Finset.range L,
          (cbinom (-α) i * cbinom (-β) k * gBinom (p + i) s) • W s (i + k) := by
    rw [e3, e4, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← smul_sub, ← fzmul_sub, prod_comm_formula (loc hA hB) L hL, fzmul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [fzmul_smul, smul_smul, hWdef]
    simp only
    rw [show p + i + (q + k) - (s : ℤ) = p + q + ((i + k : ℕ) : ℤ) - s by push_cast; ring,
      show -((i : ℤ) + k) = -((i + k : ℕ) : ℤ) by push_cast; ring]
  -- the right side
  have eD : ∀ s : ℕ, star α A s B = ∑ r ∈ Finset.range K,
      cbinom (-α) r • fzmul (-(r : ℤ)) (Fld.prod (s + r) A B) := fun s =>
    star_eq_sum_range α A s B K (fun r hr => vAB s r (by omega))
  have eD2 : ∀ (s : ℕ) (n : ℤ), p + q - L ≤ n → Fld.prod n (star α A s B) C
      = ∑ r ∈ Finset.range K, cbinom (-α) r • ∑ t ∈ Finset.range K, gBinom (-(r : ℤ)) t •
          fzmul (-(r : ℤ) - t) (Fld.prod (n + t) (Fld.prod ((s + r : ℕ) : ℤ) A B) C) := by
    intro s n hn
    rw [eD s, prod_sum_left]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Fld.prod_smul_left, prod_fzmul_left (loc (prod_mem_tgenerated _ hA hB) hC) (-(r : ℤ)) n K
      (fun t ht => by rw [← Nat.cast_add]; exact vW (s + r) _ (by omega))]
    simp only [Nat.cast_add]
  have eR : ∀ s : ℕ, s < L → star (α + β) (star α A s B) (p + q - s) C
      = ∑ m ∈ Finset.range K, cbinom (-(α + β)) m • fzmul (-(m : ℤ))
          (∑ r ∈ Finset.range K, cbinom (-α) r • ∑ t ∈ Finset.range K, gBinom (-(r : ℤ)) t •
            fzmul (-(r : ℤ) - t)
              (Fld.prod (p + q - s + m + t) (Fld.prod ((s + r : ℕ) : ℤ) A B) C)) := by
    intro s hs
    rw [star_eq_sum_range _ _ _ _ K (fun m hm => by
      rw [eD2 s _ (by omega)]
      exact Finset.sum_eq_zero fun r _ => by
        rw [Finset.sum_eq_zero (fun t _ => by rw [vW (s + r) _ (by omega), fzmul_zero,
          smul_zero]), smul_zero])]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [eD2 s _ (by omega)]
  have hRHS : ∑ s ∈ Finset.range L, gBinom p s • star (α + β) (star α A s B) (p + q - s) C
      = ∑ s ∈ Finset.range L, ∑ m ∈ Finset.range K, ∑ r ∈ Finset.range K, ∑ t ∈ Finset.range K,
          (gBinom p s * cbinom (-(α + β)) m * cbinom (-α) r * gBinom (-(r : ℤ)) t)
            • W (s + r) (m + r + t) := by
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [eR s (Finset.mem_range.mp hs), Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [fzmul_sum, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [fzmul_smul, fzmul_sum, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [fzmul_smul, fzmul_fzmul, hWdef]
    simp only [smul_smul]
    rw [show -(m : ℤ) + (-(r : ℤ) - t) = -((m + r + t : ℕ) : ℤ) by push_cast; ring,
      show p + q - (s : ℤ) + m + t = p + q + ((m + r + t : ℕ) : ℤ) - ((s + r : ℕ) : ℤ) by
        push_cast; ring]
    congr 1
    ring
  rw [hLHS, hRHS]
  refine reorg W L K (by omega) (fun σ J hσ => ?_) (fun σ J hJ => ?_) _ _
    (fun σ J _ _ => star_comm_coeff α β p σ J)
  · rw [hWdef]
    simp only
    rw [hL σ hσ, prod_zero_left, fzmul_zero]
  · rw [hWdef]
    simp only
    by_cases hσ : σ < L
    · rw [vW σ _ (by omega), fzmul_zero]
    · rw [hL σ (by omega), prod_zero_left, fzmul_zero]

/-! ## Covariance under `zᶜ` and the identity field -/

theorem prod_one_right_nonneg' (n : ℤ) (hn : 0 ≤ n) (A : Fld M) : Fld.prod n A Fld.one = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) := ⟨n.toNat, by omega⟩
  exact Fld.prod_one_right_nat k A

/-- **`zᶜ` in the first slot shifts the twist**: `star α (zᶜA) p X = zᶜ · star (α − c) A p X`. -/
theorem star_fzmul_left {A X : Fld M} (h : Local A.1 X.1) (α : ℂ) (c p : ℤ) :
    star α (fzmul c A) p X = fzmul c (star (α - c) A p X) := by
  obtain ⟨K, hK⟩ := exists_prod_offset_zero h p
  have hloc : Local (fzmul c A).1 X.1 := Local.zmul_left h c
  rw [star_eq_sum_range (α - c) A p X K hK, star_eq_sum_range α (fzmul c A) p X K (fun i hi => by
    rw [prod_fzmul_left h c (p + i) K (fun t ht => by
      rw [show p + (i : ℤ) + t = p + ((i + t : ℕ) : ℤ) by push_cast; ring]; exact hK _ (by omega))]
    exact Finset.sum_eq_zero fun t _ => by
      rw [show p + (i : ℤ) + t = p + ((i + t : ℕ) : ℤ) by push_cast; ring, hK _ (by omega),
        fzmul_zero, smul_zero])]
  have hexp : ∀ i : ℕ, cbinom (-α) i • fzmul (-(i : ℤ)) (Fld.prod (p + i) (fzmul c A) X)
      = ∑ t ∈ Finset.range K, (cbinom (-α) i * gBinom c t) •
          fzmul (c - ((i + t : ℕ) : ℤ)) (Fld.prod (p + ((i + t : ℕ) : ℤ)) A X) := by
    intro i
    rw [prod_fzmul_left h c (p + i) K (fun t ht => by
      rw [show p + (i : ℤ) + t = p + ((i + t : ℕ) : ℤ) by push_cast; ring]; exact hK _ (by omega)),
      fzmul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [fzmul_smul, fzmul_fzmul, smul_smul, show p + (i : ℤ) + t = p + ((i + t : ℕ) : ℤ) by
      push_cast; ring, show -(i : ℤ) + (c - t) = c - ((i + t : ℕ) : ℤ) by push_cast; ring]
  simp only [hexp]
  rw [sum_range_sq_eq_sum_antidiagonal K _ (fun i t h => by
    rw [hK _ h, fzmul_zero, smul_zero]), fzmul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [fzmul_smul, fzmul_fzmul, show c + -(J : ℤ) = c - J by ring, show -(α - c) = -α + c by ring,
    cbinom_add, Finset.sum_smul]
  refine Finset.sum_congr rfl fun it hit => ?_
  rw [Finset.mem_antidiagonal] at hit
  rw [hit, gBinom_eq_cbinom]

/-- `star α A ℓ 1 = 0` for `ℓ ≥ 0`. -/
theorem star_one_right_nonneg (α : ℂ) (A : Fld M) {ℓ : ℤ} (hℓ : 0 ≤ ℓ) :
    star α A ℓ Fld.one = 0 := by
  rw [star_eq_sum_range α A ℓ Fld.one 0 (fun i _ => prod_one_right_nonneg' _ (by omega) A)]
  rfl

/-- `star α A (−1) 1 = A`. -/
theorem star_one_right_neg_one (α : ℂ) (A : Fld M) : star α A (-1) Fld.one = A := by
  rw [star_eq_sum_range α A (-1) Fld.one 1 (fun i hi => prod_one_right_nonneg' _ (by omega) A),
    Finset.sum_range_one]
  simp

/-- The untwisted case: `star 0 A p X = A₍ₚ₎X`. -/
theorem star_zero (A : Fld M) (p : ℤ) (X : Fld M) : star 0 A p X = Fld.prod p A X := by
  rw [star, finsum_eq_single _ 0 (fun i hi => by rw [neg_zero, cbinom_zero_left, if_neg hi,
    zero_smul])]
  simp

/-- `star (c : ℂ) (zᶜ 1) k X = δ_{k,−1} zᶜ X`: the twisted vertex operator of the vacuum on
the even class `2c`. -/
theorem star_fzmul_one (c k : ℤ) (X : Fld M) :
    star (c : ℂ) (fzmul c Fld.one) k X = if k = -1 then fzmul c X else 0 := by
  rw [star_fzmul_left (Local_idField_left X.1) (c : ℂ) c k, sub_self, star_zero,
    Fld.prod_one_left_all]
  split_ifs <;> simp

/-- **The translation identity for twisted products with the identity field**:
`star α (∂A − α z⁻¹A) n 1 = −n · star α A (n−1) 1`. -/
theorem star_deriv_one (α : ℂ) (A : Fld M) (n : ℤ) :
    star α (Fld.deriv A - α • fzmul (-1) A) n Fld.one
      = (-n : ℂ) • star α A (n - 1) Fld.one := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 1 - n ≤ K := ⟨(1 - n).toNat, by omega⟩
  set a : ℕ → Fld M := fun J => Fld.prod (n - 1 + J) A Fld.one with ha
  have hav : ∀ J : ℕ, K ≤ J → a J = 0 := fun J hJ => prod_one_right_nonneg' _ (by omega) A
  have hloc : Local A.1 (Fld.one : Fld M).1 := Local_idField_right A.1
  have hD : ∀ i : ℕ, Fld.prod (n + i) (Fld.deriv A - α • fzmul (-1) A) Fld.one
      = (-((n + i : ℤ) : ℂ)) • a i - α • ∑ t ∈ Finset.range K,
          gBinom (-1) t • fzmul (-1 - t) (a (i + t + 1)) := by
    intro i
    rw [prod_sub_left, Fld.prod_smul_left, prod_deriv_left,
      prod_fzmul_left hloc (-1) (n + i) K (fun t ht => prod_one_right_nonneg' _ (by omega) A)]
    simp only [ha]
    rw [show n + (i : ℤ) - 1 = n - 1 + i by ring]
    congr 2
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [show n + (i : ℤ) + t = n - 1 + ((i + t + 1 : ℕ) : ℤ) by push_cast; ring]
  rw [star_eq_sum_range α A (n - 1) Fld.one K hav, star_eq_sum_range α _ n Fld.one K (fun i hi => by
    rw [hD i, hav i (by omega), smul_zero, zero_sub, Finset.sum_eq_zero (fun t _ => by
      rw [hav _ (by omega), fzmul_zero, smul_zero]), smul_zero, neg_zero])]
  simp only [hD, smul_sub, fzmul_sub, fzmul_smul, fzmul_sum, Finset.smul_sum, fzmul_fzmul,
    Finset.sum_sub_distrib, smul_smul]
  set b : ℕ → Fld M := fun J => fzmul (-(J : ℤ)) (a J) with hb
  have hbv : ∀ J : ℕ, K ≤ J → b J = 0 := fun J hJ => by simp only [hb]; rw [hav J hJ, fzmul_zero]
  have hdouble : ∑ i ∈ Finset.range K, ∑ t ∈ Finset.range K,
      (cbinom (-α) i * (α * gBinom (-1) t)) • fzmul (-(i : ℤ) + (-1 - t)) (a (i + t + 1))
      = ∑ J ∈ Finset.range K, (if 1 ≤ J then α * cbinom (-α - 1) (J - 1) else 0) • b J := by
    have hre : ∀ i t : ℕ, fzmul (-(i : ℤ) + (-1 - t)) (a (i + t + 1)) = b (i + t + 1) := by
      intro i t; simp only [hb]; congr 1; push_cast; ring
    simp only [hre]
    rw [sum_range_sq_eq_sum_antidiagonal K (fun i t => (cbinom (-α) i * (α * gBinom (-1) t)) •
      b (i + t + 1)) (fun i t h => by beta_reduce; rw [hbv _ (by omega), smul_zero])]
    rw [show (∑ J ∈ Finset.range K, ∑ p ∈ Finset.antidiagonal J,
        (cbinom (-α) p.1 * (α * gBinom (-1) p.2)) • b (p.1 + p.2 + 1))
        = ∑ J ∈ Finset.range K, (α * cbinom (-α - 1) J) • b (J + 1) by
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [show -α - 1 = -α + -1 by ring, ← gBinom_vandermonde, Finset.mul_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun it hit => ?_
      rw [Finset.mem_antidiagonal] at hit
      rw [hit, gBinom_eq_cbinom]
      push_cast
      congr 1
      ring]
    rw [sum_range_add_shift b _ 1 K hbv]
  rw [hdouble, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun J _ => ?_
  simp only [hb]
  rw [← sub_smul]
  congr 1
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · simp
  · rw [if_pos (show 1 ≤ J by omega)]
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, J = j + 1 := ⟨J - 1, by omega⟩
    have h := cbinom_succ_mul (-α) j
    rw [Nat.add_sub_cancel]
    push_cast at h ⊢
    linear_combination (-1 : ℂ) * h

/-! ## Linearity -/

theorem star_add_right {A X Y : Fld M} (hX : Local A.1 X.1) (hY : Local A.1 Y.1) (α : ℂ)
    (p : ℤ) : star α A p (X + Y) = star α A p X + star α A p Y := by
  obtain ⟨K₁, hK₁⟩ := exists_prod_offset_zero hX p
  obtain ⟨K₂, hK₂⟩ := exists_prod_offset_zero hY p
  rw [star_eq_sum_range α A p X (K₁ + K₂) (fun i hi => hK₁ i (by omega)),
    star_eq_sum_range α A p Y (K₁ + K₂) (fun i hi => hK₂ i (by omega)),
    star_eq_sum_range α A p (X + Y) (K₁ + K₂) (fun i hi => by
      rw [Fld.prod_add_right, hK₁ i (by omega), hK₂ i (by omega), add_zero]),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fld.prod_add_right, fzmul_add, smul_add]

theorem star_smul_right {A X : Fld M} (hX : Local A.1 X.1) (α c : ℂ) (p : ℤ) :
    star α A p (c • X) = c • star α A p X := by
  obtain ⟨K, hK⟩ := exists_prod_offset_zero hX p
  rw [star_eq_sum_range α A p X K hK, star_eq_sum_range α A p (c • X) K (fun i hi => by
      rw [Fld.prod_smul_right, hK i hi, smul_zero]), Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fld.prod_smul_right, fzmul_smul, smul_comm]

theorem star_zero_right (α : ℂ) (A : Fld M) (p : ℤ) : star α A p 0 = 0 := by
  rw [star_eq_sum_range α A p 0 0 (fun i _ => prod_zero_right _ A)]
  rfl

theorem star_add_left {A B X : Fld M} (hA : Local A.1 X.1) (hB : Local B.1 X.1) (α : ℂ)
    (p : ℤ) : star α (A + B) p X = star α A p X + star α B p X := by
  obtain ⟨K₁, hK₁⟩ := exists_prod_offset_zero hA p
  obtain ⟨K₂, hK₂⟩ := exists_prod_offset_zero hB p
  rw [star_eq_sum_range α A p X (K₁ + K₂) (fun i hi => hK₁ i (by omega)),
    star_eq_sum_range α B p X (K₁ + K₂) (fun i hi => hK₂ i (by omega)),
    star_eq_sum_range α (A + B) p X (K₁ + K₂) (fun i hi => by
      rw [Fld.prod_add_left, hK₁ i (by omega), hK₂ i (by omega), add_zero]),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fld.prod_add_left, fzmul_add, smul_add]

theorem star_smul_left {A X : Fld M} (hA : Local A.1 X.1) (α c : ℂ) (p : ℤ) :
    star α (c • A) p X = c • star α A p X := by
  obtain ⟨K, hK⟩ := exists_prod_offset_zero hA p
  rw [star_eq_sum_range α A p X K hK, star_eq_sum_range α (c • A) p X K (fun i hi => by
      rw [Fld.prod_smul_left, hK i hi, smul_zero]), Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fld.prod_smul_left, fzmul_smul, smul_comm]

theorem star_zero_left (α : ℂ) (p : ℤ) (X : Fld M) : star α 0 p X = 0 := by
  rw [star_eq_sum_range α 0 p X 0 (fun i _ => prod_zero_left _ X)]
  rfl

/-! ## The identity field -/

theorem local_one_left (Y : Fld M) : Local (Fld.one : Fld M).1 Y.1 := Local_idField_left Y.1

theorem local_one_right (Y : Fld M) : Local Y.1 (Fld.one : Fld M).1 := Local_idField_right Y.1

theorem local_fzmul_one_left (c : ℤ) (Y : Fld M) : Local (fzmul c (Fld.one : Fld M)).1 Y.1 :=
  Local.zmul_left (local_one_left Y) c

/-- Products `(c • 1)₍ⱼ₎Y` vanish for `j ≥ 0`. -/
theorem prod_scalar_one_nonneg (c : ℂ) {j : ℤ} (hj : 0 ≤ j) (Y : Fld M) :
    Fld.prod j (c • (Fld.one : Fld M)) Y = 0 := by
  rw [Fld.prod_smul_left, Fld.prod_one_left_all, if_neg (by omega), smul_zero]

/-- Products `(c • z)₍ⱼ₎Y` vanish for `j ≥ 0`. -/
theorem prod_scalar_z_nonneg (c : ℂ) {j : ℤ} (hj : 0 ≤ j) (Y : Fld M) :
    Fld.prod j (c • fzmul 1 (Fld.one : Fld M)) Y = 0 := by
  rw [Fld.prod_smul_left, prod_fzmul_left (local_one_left Y) 1 j 0 (fun t _ => by
    rw [Fld.prod_one_left_all, if_neg (by omega)]), Finset.sum_range_zero, smul_zero]

/-! ## Derivatives of twisted products -/

theorem fld_deriv_add (a b : Fld M) : Fld.deriv (a + b) = Fld.deriv a + Fld.deriv b :=
  Subtype.ext (map_add VOA.deriv a.1 b.1)

theorem fld_deriv_smul (c : ℂ) (a : Fld M) : Fld.deriv (c • a) = c • Fld.deriv a :=
  Subtype.ext (map_smul VOA.deriv c a.1)

theorem fld_deriv_zero : Fld.deriv (0 : Fld M) = 0 := Subtype.ext (map_zero VOA.deriv)

theorem fld_deriv_sub (a b : Fld M) : Fld.deriv (a - b) = Fld.deriv a - Fld.deriv b :=
  Subtype.ext (map_sub VOA.deriv a.1 b.1)

theorem fld_deriv_sum {ι : Type*} (s : Finset ι) (f : ι → Fld M) :
    Fld.deriv (∑ i ∈ s, f i) = ∑ i ∈ s, Fld.deriv (f i) := by
  classical
  induction s using Finset.induction with
  | empty => exact fld_deriv_zero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fld_deriv_add, ih]

theorem fld_deriv_one : Fld.deriv (Fld.one : Fld M) = 0 := Subtype.ext Fld.deriv_idField

theorem cbinom_succ_mul' (x : ℂ) (k : ℕ) :
    cbinom x (k + 1) * ((k : ℂ) + 1) = cbinom x k * (x - k) := by
  rw [cbinom, cbinom, Finset.prod_range_succ, Nat.factorial_succ]
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  push_cast
  field_simp

/-- **The derivative of a twisted product**:
`∂(star α G q Y) = star α G q (∂Y) − q · star α G (q−1) Y + α z⁻¹ · star α G q Y`. -/
theorem deriv_star {G Y : Fld M} (h : Local G.1 Y.1) (α : ℂ) (q : ℤ) :
    Fld.deriv (star α G q Y)
      = star α G q (Fld.deriv Y) - (q : ℂ) • star α G (q - 1) Y
        + α • fzmul (-1) (star α G q Y) := by
  obtain ⟨K₀, hK₀⟩ := exists_prod_offset_zero h (q - 1)
  set K := K₀ + 1 with hK
  have hv : ∀ i : ℕ, K₀ ≤ i → Fld.prod (q - 1 + i) G Y = 0 := hK₀
  have hv' : ∀ i : ℕ, K ≤ i → Fld.prod (q + i) G Y = 0 := fun i hi => by
    rw [show q + (i : ℤ) = q - 1 + ((i + 1 : ℕ) : ℤ) by push_cast; ring]; exact hv _ (by omega)
  have hvd : ∀ i : ℕ, K ≤ i → Fld.prod (q + i) G (Fld.deriv Y) = 0 := fun i hi => by
    have := congrArg Fld.deriv (hv' i hi)
    rw [deriv_prod, prod_deriv_left, fld_deriv_zero] at this
    rw [show q + (i : ℤ) - 1 = q - 1 + i by ring, hv i (by omega), smul_zero, zero_add] at this
    exact this
  rw [star_eq_sum_range α G q Y K hv', star_eq_sum_range α G q (Fld.deriv Y) K hvd,
    star_eq_sum_range α G (q - 1) Y K (fun i hi => hv i (by omega)), fld_deriv_sum]
  simp only [fld_deriv_smul, deriv_fzmul, deriv_prod, prod_deriv_left, fzmul_add, fzmul_smul,
    smul_add, Finset.sum_add_distrib, fzmul_sum, Finset.smul_sum, fzmul_fzmul]
  -- reindex the `G₍q+i−1₎` family
  have hshift : ∑ i ∈ Finset.range K, cbinom (-α) i • (-((q + i : ℤ) : ℂ)) • fzmul (-(i : ℤ))
        (Fld.prod (q + i - 1) G Y)
      = ∑ i ∈ Finset.range K, (-(q : ℂ) * cbinom (-α) i) • fzmul (-(i : ℤ))
          (Fld.prod (q - 1 + i) G Y)
        + ∑ i ∈ Finset.range K, (-(i : ℂ) * cbinom (-α) i) • fzmul (-(i : ℤ))
          (Fld.prod (q - 1 + i) G Y) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show q + (i : ℤ) - 1 = q - 1 + i by ring, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring
  have hshift2 : ∑ i ∈ Finset.range K, (-(i : ℂ) * cbinom (-α) i) • fzmul (-(i : ℤ))
        (Fld.prod (q - 1 + i) G Y)
      = ∑ i ∈ Finset.range K, ((α + i) * cbinom (-α) i) • fzmul (-1 + -(i : ℤ))
          (Fld.prod (q + i) G Y) := by
    rw [sum_range_shift_one _ K (by simp) (by rw [hv K (by omega)]; simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show q - 1 + ((i + 1 : ℕ) : ℤ) = q + i by push_cast; ring,
      show -((i + 1 : ℕ) : ℤ) = -1 + -(i : ℤ) by push_cast; ring]
    congr 1
    have := cbinom_succ_mul' (-α) i
    push_cast
    linear_combination (-1 : ℂ) * this
  have hA1 : ∑ i ∈ Finset.range K, cbinom (-α) i • (((-(i : ℤ) : ℤ) : ℂ)) •
        fzmul (-(i : ℤ) - 1) (Fld.prod (q + i) G Y)
      + ∑ i ∈ Finset.range K, ((α + i) * cbinom (-α) i) • fzmul (-1 + -(i : ℤ))
          (Fld.prod (q + i) G Y)
      = ∑ i ∈ Finset.range K, α • cbinom (-α) i • fzmul (-1 + -(i : ℤ)) (Fld.prod (q + i) G Y) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show -(i : ℤ) - 1 = -1 + -(i : ℤ) by ring, smul_smul, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring
  have hBq : ∑ i ∈ Finset.range K, (-(q : ℂ) * cbinom (-α) i) • fzmul (-(i : ℤ))
        (Fld.prod (q - 1 + i) G Y)
      = -∑ i ∈ Finset.range K, (q : ℂ) • cbinom (-α) i • fzmul (-(i : ℤ))
          (Fld.prod (q - 1 + i) G Y) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, ← neg_smul, neg_mul]
  rw [hshift, hshift2, hBq, ← hA1]
  abel

end TwistedReduction

end VOA
