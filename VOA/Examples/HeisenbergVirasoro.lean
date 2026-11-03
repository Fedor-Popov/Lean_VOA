/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.HeisenbergFock
import VOA.Core.Dong
import Mathlib.Algebra.Lie.OfAssociative

/-!
# FRONT B — the Sugawara conformal field (free boson, c = 1)

The Virasoro structure built DIRECTLY from the rank-1 Heisenberg current of
`Examples.HeisenbergFock`, independent of the general vertex operator `Y`.

* `sugawaraField k := (1/2k) • nprod (current k)(current k)` — the normal-ordered square
  `:α(z)α(z):` (`Core.Dong.nprod`; `current k` is a field, `isField_current`).
* `Lvir k m := (1/2k)·(:αα:)(-m-2)` — the Sugawara modes `Lₘ = (1/2k)∑_j :a_{m-j}a_j:`
  (`Lvir_apply`/`Lvir_apply'`, the reindex `m ↦ -m-1` of the `nprod` coefficient).
* `L_comm_osc` (5.2.5e): `[Lₘ, aₙ] = -n a_{m+n}` — fully proved (the `L₀`-grading).
* `ω := (1/2k) a₋₁a₋₁1` (`= L₋₂1`, `Lvir_neg_two_vacuum`), with `L₀ω = 2ω` (`L_zero_omega`),
  `L₁ω = 0` (`L_one_omega`), and `L₂ω = (1/2)·1` (`L_two_omega`) — the **central charge c = 1**
  exhibited concretely as the double contraction `L₂ω = (c/2)·1`.
* Virasoro relation (5.2.5d) `[Lₘ,Lₙ] = (m-n)L_{m+n} + δ_{m+n,0}(m³-m)/12·id`: reduced
  (`L_comm_sugTerm_vec`, `L_comm_eq_finsum`) to the collapse of one finite reindexable sum;
  that collapse is the normal-ordering boundary-shift (central-charge anomaly) computation.

All declarations are `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace VOA

open scoped BigOperators
open MvPolynomial
open Module (End)

/-! ## `current k` is a field -/

/-- `current k` is a field: on each polynomial `p`, only finitely many modes act nonzero
(the high annihilation modes differentiate by a variable not occurring in `p`). -/
theorem isField_current (k : ℂ) : IsField (current k) := by
  intro p
  classical
  set M : ℕ := (p.vars.sup id) with hM
  refine ⟨-(M : ℤ) - 2, fun j hj => ?_⟩
  show current k j p = 0
  rw [current_apply]
  have hpos : 0 < -j - 1 := by omega
  rw [osc_apply_pos k hpos]
  have hvar : (-j - 1 - 1).toNat ∉ p.vars := by
    intro hmem
    have hle : (-j - 1 - 1).toNat ≤ M := by
      have := Finset.le_sup (f := id) hmem; simpa using this
    omega
  rw [pderiv_eq_zero_of_notMem_vars hvar, smul_zero, smul_zero]

/-! ## The Sugawara field, its modes, and the action formula -/

/-- The involution `j ↦ -j-1` of `ℤ` (the current-index ↔ mode-index flip). -/
def flipIdx : ℤ ≃ ℤ where
  toFun j := -j - 1
  invFun j := -j - 1
  left_inv j := by dsimp only; ring
  right_inv j := by dsimp only; ring

/-- Evaluate the involution converting a formal-distribution coefficient index into the
corresponding oscillator mode index. Applying the conversion twice returns the original
integer. -/
@[simp] theorem flipIdx_apply (j : ℤ) : flipIdx j = -j - 1 := rfl

/-- The **un-normalized Sugawara coefficient** at `z^{-M-1}`, acting on a vector. It is the
`(-M-1)`-coefficient of `nprod (current k)(current k)`, reindexed `m ↦ j = -m-1` into the
mode picture: `(nprod α α)(-M-1) x = ∑_j :a_{M-1-j} a_j:`, i.e.
`∑_j (if j < 0 then a_j(a_{M-1-j} x) else a_{M-1-j}(a_j x))`. The two oscillator indices
sum to `M-1`. -/
theorem nprod_current_coeff (k : ℂ) (M : ℤ) (x : Fock) :
    nprod (isField_current k) (isField_current k) (-M - 1) x
      = ∑ᶠ j : ℤ, (if j < 0 then osc k j (osc k (M - 1 - j) x)
                   else osc k (M - 1 - j) (osc k j x)) := by
  rw [nprod_apply]
  rw [← finsum_comp_equiv flipIdx]
  refine finsum_congr fun j => ?_
  rw [normalOrdered_apply, flipIdx_apply]
  -- current k (-j-1) = osc k j ; second index -M-1-(-j-1) = j-M, current → osc k (M-1-j)
  rw [current_apply, current_apply,
      show -(-j - 1) - 1 = j from by ring,
      show -(-M - 1 - (-j - 1)) - 1 = M - 1 - j from by ring]
  -- the gate: 0 ≤ -j-1 ↔ j < 0
  by_cases hj : j < 0
  · rw [if_pos (by omega), if_pos hj, Module.End.mul_apply]
  · rw [if_neg (by omega), if_neg hj, Module.End.mul_apply]

/-- The single normal-ordered operator term `T_j = :a_{m-j} a_j:` (the `j`-summand of the
Sugawara coefficient). -/
noncomputable def sugTerm (k : ℂ) (m j : ℤ) : End ℂ Fock :=
  if j < 0 then osc k j * osc k (m - j) else osc k (m - j) * osc k j

/-- Applying a normal-ordered quadratic term means composing its two oscillator actions in the
order fixed by the sign of j. Negative-index creation operators are placed to the left; this
formula exposes the action on an arbitrary Fock state. -/
@[simp] theorem sugTerm_apply (k : ℂ) (m j : ℤ) (x : Fock) :
    sugTerm k m j x = if j < 0 then osc k j (osc k (m - j) x) else osc k (m - j) (osc k j x) := by
  rw [sugTerm]; split_ifs <;> rw [Module.End.mul_apply]

/-- The **Sugawara field** `L(z) = (1/2k) :α(z)α(z):` (Gannon 5.2.5d): the normal-ordered
square of the basic current, scaled by `1/2k`. A formal distribution of `End ℂ Fock`. -/
noncomputable def sugawaraField (k : ℂ) : FormalDist (End ℂ Fock) :=
  (1 / (2 * k)) • nprod (isField_current k) (isField_current k)

/-- The **Sugawara modes** `Lₘ = (1/2k)∑_j :a_{m-j}a_j:` (Gannon 5.2.5d). The field `L(z)`
has conformal weight 2, so `L(z) = ∑ₘ Lₘ z^{-m-2}`; the mode index of `nprod` is therefore
shifted by one: `Lₘ = (1/2k)·(nprod α α)(-m-2)`. -/
noncomputable def Lvir (k : ℂ) (m : ℤ) : End ℂ Fock :=
  (1 / (2 * k)) • nprod (isField_current k) (isField_current k) (-m - 2)

/-- The Sugawara mode `Lₘ` acts on a vector as the (finite) normal-ordered sum
`Lₘ x = (1/2k)∑_j :a_{m-j}a_j: x`, the two indices summing to `m`. -/
theorem Lvir_apply (k : ℂ) (m : ℤ) (x : Fock) :
    Lvir k m x
      = (1 / (2 * k)) • ∑ᶠ j : ℤ, (if j < 0 then osc k j (osc k (m - j) x)
                                   else osc k (m - j) (osc k j x)) := by
  rw [Lvir, LinearMap.smul_apply]
  congr 1
  have := nprod_current_coeff k (m + 1) x
  rw [show -(m + 1) - 1 = -m - 2 from by ring] at this
  rw [this]
  exact finsum_congr fun j => by rw [show m + 1 - 1 - j = m - j from by ring]

/-- `Lₘ x = (1/2k)∑ᶠ_j T_j x` in the `sugTerm` packaging. -/
theorem Lvir_apply' (k : ℂ) (m : ℤ) (x : Fock) :
    Lvir k m x = (1 / (2 * k)) • ∑ᶠ j : ℤ, sugTerm k m j x := by
  rw [Lvir_apply]; congr 1; exact finsum_congr fun j => (sugTerm_apply k m j x).symm

/-! ## `[Lₘ, aₙ] = -n a_{m+n}`  (Gannon 5.2.5e) -/

/-- A scalar multiple of `id` is central: `aₙ·(c•id) = (c•id)·aₙ`. -/
theorem osc_mul_smul_id_comm (k : ℂ) (n : ℤ) (c : ℂ) :
    osc k n * (c • (LinearMap.id : End ℂ Fock)) = (c • LinearMap.id) * osc k n := by
  rw [mul_smul_comm, smul_mul_assoc,
    show (LinearMap.id : End ℂ Fock) = (1 : End ℂ Fock) from rfl, mul_one, one_mul]

/-- Reordering inside a bracket is harmless: `[aₙ, aₐaᵦ] = [aₙ, aᵦaₐ]`, since `aₐaᵦ` and
`aᵦaₐ` differ by the central scalar `[aₐ,aᵦ]`. -/
theorem osc_bracket_swap (k : ℂ) (n a b : ℤ) :
    osc k n * (osc k a * osc k b) - (osc k a * osc k b) * osc k n
      = osc k n * (osc k b * osc k a) - (osc k b * osc k a) * osc k n := by
  have hcomm : osc k a * osc k b - osc k b * osc k a
      = (if a + b = 0 then (a : ℂ) * k else 0) • LinearMap.id := osc_comm k a b
  have hswap : osc k a * osc k b
      = osc k b * osc k a + (if a + b = 0 then (a : ℂ) * k else 0) • LinearMap.id := by
    rw [← hcomm]; abel
  rw [hswap, mul_add, add_mul, osc_mul_smul_id_comm]
  noncomm_ring

/-- The per-term commutator `[aₙ, :a_{m-j}a_j:] = [aₙ, a_{m-j}a_j]` (ordering immaterial),
expanded by Leibniz into `[aₙ,a_{m-j}]·a_j + a_{m-j}·[aₙ,a_j]`, each a scalar times a single
oscillator (Gannon, step in 5.2.5e). -/
theorem osc_bracket_normalOrdered_term (k : ℂ) (m n j : ℤ) :
    osc k n * (if j < 0 then osc k j * osc k (m - j) else osc k (m - j) * osc k j)
      - (if j < 0 then osc k j * osc k (m - j) else osc k (m - j) * osc k j) * osc k n
      = (if n + (m - j) = 0 then (n : ℂ) * k else 0) • osc k j
        + (if n + j = 0 then (n : ℂ) * k else 0) • osc k (m - j) := by
  -- reduce to the fixed ordering a_{m-j} a_j
  have hT : osc k n * (if j < 0 then osc k j * osc k (m - j) else osc k (m - j) * osc k j)
      - (if j < 0 then osc k j * osc k (m - j) else osc k (m - j) * osc k j) * osc k n
      = osc k n * (osc k (m - j) * osc k j) - (osc k (m - j) * osc k j) * osc k n := by
    by_cases hj : j < 0
    · rw [if_pos hj]; exact osc_bracket_swap k n j (m - j)
    · rw [if_neg hj]
  rw [hT]
  -- Leibniz expansion
  have leib : osc k n * (osc k (m - j) * osc k j) - (osc k (m - j) * osc k j) * osc k n
      = (osc k n * osc k (m - j) - osc k (m - j) * osc k n) * osc k j
        + osc k (m - j) * (osc k n * osc k j - osc k j * osc k n) := by
    rw [sub_mul, mul_sub, ← mul_assoc, ← mul_assoc]; abel
  rw [leib, osc_comm k n (m - j), osc_comm k n j, smul_mul_assoc, mul_smul_comm,
    show (LinearMap.id : End ℂ Fock) * osc k j = osc k j from by
      rw [show (LinearMap.id : End ℂ Fock) = 1 from rfl, one_mul],
    show osc k (m - j) * (LinearMap.id : End ℂ Fock) = osc k (m - j) from by
      rw [show (LinearMap.id : End ℂ Fock) = 1 from rfl, mul_one]]

/-- The `j`-indexed Sugawara term family `j ↦ T_j x` has finite support (transport of
`normalOrdered_diag_support_finite` through the reindex `m ↦ -m-1`). -/
theorem sugTerm_support_finite (k : ℂ) (m : ℤ) (x : Fock) :
    (Function.support (fun j : ℤ => sugTerm k m j x)).Finite := by
  -- support of normalOrdered over the diagonal at s = -(m+1)-1 = -m-2, transported by j = -p-1
  have hfin := normalOrdered_diag_support_finite (isField_current k) (isField_current k)
    (-m - 2) x
  apply Set.Finite.subset (hfin.image (fun p => -p - 1))
  intro j hj
  rw [Function.mem_support] at hj
  rw [Set.mem_image]
  refine ⟨-j - 1, ?_, by ring⟩
  rw [Function.mem_support]
  -- normalOrdered (current k)(current k) (-j-1) (-m-2-(-j-1)) x  vs  sugTerm k m j x
  rw [normalOrdered_apply, current_apply, current_apply]
  rw [show -(-j - 1) - 1 = j from by ring,
      show -(-m - 2 - (-j - 1)) - 1 = m - j from by ring]
  rw [sugTerm_apply] at hj
  by_cases hjlt : j < 0
  · rw [if_pos (by omega)]; rw [if_pos hjlt] at hj; rwa [Module.End.mul_apply]
  · rw [if_neg (by omega)]; rw [if_neg hjlt] at hj; rwa [Module.End.mul_apply]

/-- A delta-gated finsum collapses to its single nonzero point: if the predicate
`p j ↔ j = j₀`, then `∑ᶠ j, (if p j then c else 0)•w j = c • w j₀`. -/
theorem finsum_gate_collapse (c : ℂ) (w : ℤ → Fock) (j₀ : ℤ) (p : ℤ → Prop)
    [DecidablePred p] (hp : ∀ j, p j ↔ j = j₀) :
    (∑ᶠ j : ℤ, (if p j then c else 0) • w j) = c • w j₀ := by
  rw [finsum_eq_single (fun j => (if p j then c else 0) • w j) j₀ (fun j hj => ?_)]
  · show (if p j₀ then c else 0) • w j₀ = c • w j₀
    rw [if_pos ((hp j₀).mpr rfl)]
  · show (if p j then c else 0) • w j = 0
    rw [if_neg (fun hpj => hj ((hp j).mp hpj)), zero_smul]

/-! ### The commutator `[Lₘ, aₙ] = -n a_{m+n}` -/

/-- **`[Lₘ, aₙ] = -n a_{m+n}`** (Gannon 5.2.5e): the Sugawara mode is a conformal vector for
the current; in particular `L₀ aₙ = -n aₙ`, the `L₀`-grading. Proved by distributing `aₙ`
through the finite normal-ordered sum `Lₘ = (1/2k)∑_j :a_{m-j}a_j:` (`map_finsum`), bracketing
each term (`osc_bracket_normalOrdered_term`), and collapsing the two resulting δ-gated sums
(`finsum_gate_collapse`): the two contributions `j=m+n` and `j=-n` each give `nk·a_{m+n}`,
summing to `2nk·a_{m+n}`, which `1/2k` turns into `-n a_{m+n}` (the global sign from
`[L,a] = -[a,L]`). -/
theorem L_comm_osc (k : ℂ) (hk : k ≠ 0) (m n : ℤ) :
    Lvir k m * osc k n - osc k n * Lvir k m = (-(n : ℂ)) • osc k (m + n) := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.smul_apply]
  -- finiteness facts
  have hfin_x : (Function.support (fun j : ℤ => sugTerm k m j x)).Finite :=
    sugTerm_support_finite k m x
  have hfin_nx : (Function.support (fun j : ℤ => sugTerm k m j (osc k n x))).Finite :=
    sugTerm_support_finite k m (osc k n x)
  -- Lₘ(aₙ x) = (1/2k) ∑ T_j (aₙ x) ;  aₙ(Lₘ x) = (1/2k) ∑ aₙ (T_j x)
  rw [Lvir_apply' k m (osc k n x), Lvir_apply' k m x, map_smul,
      map_finsum (osc k n) hfin_x, ← smul_sub]
  -- combine the two finsums into ∑ (T_j(aₙx) - aₙ(T_j x))
  rw [← finsum_sub_distrib hfin_nx
      (hfin_x.subset (fun j hj => by
        rw [Function.mem_support] at hj ⊢; exact fun h => hj (by rw [h, map_zero])))]
  -- each summand: T_j(aₙx) - aₙ(T_j x) = (T_j aₙ - aₙ T_j) x = -(per-term bracket) x
  have hterm : ∀ j : ℤ, sugTerm k m j (osc k n x) - osc k n (sugTerm k m j x)
      = -((if n + (m - j) = 0 then (n : ℂ) * k else 0) • osc k j x
          + (if n + j = 0 then (n : ℂ) * k else 0) • osc k (m - j) x) := by
    intro j
    have hb := osc_bracket_normalOrdered_term k m n j
    -- bracket as an operator equation; the LHS of hb has sugTerm's `if` unfolded
    have hop : sugTerm k m j * osc k n - osc k n * sugTerm k m j
        = -((if n + (m - j) = 0 then (n : ℂ) * k else 0) • osc k j
            + (if n + j = 0 then (n : ℂ) * k else 0) • osc k (m - j)) := by
      rw [sugTerm, eq_neg_iff_add_eq_zero, ← hb]; abel
    have happ := congrArg (fun (T : End ℂ Fock) => T x) hop
    simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply,
      LinearMap.smul_apply, Module.End.mul_apply] using happ
  rw [finsum_congr hterm]
  -- ∑ -( gate1•a_j + gate2•a_{m-j} ) : split, collapse each gate, then scale by 1/2k
  rw [show (∑ᶠ j : ℤ, -((if n + (m - j) = 0 then (n : ℂ) * k else 0) • osc k j x
          + (if n + j = 0 then (n : ℂ) * k else 0) • osc k (m - j) x))
        = ∑ᶠ j : ℤ, ((if n + (m - j) = 0 then -((n : ℂ) * k) else 0) • osc k j x
          + (if n + j = 0 then -((n : ℂ) * k) else 0) • osc k (m - j) x) from
      finsum_congr fun j => by rw [neg_add]; congr 1 <;> · split_ifs <;> simp [neg_smul]]
  have hf1 : (Function.support (fun j : ℤ =>
      (if n + (m - j) = 0 then -((n : ℂ) * k) else 0) • osc k j x)).Finite := by
    apply Set.Finite.subset (Set.finite_singleton (m + n))
    intro j hj; rw [Function.mem_support] at hj; rw [Set.mem_singleton_iff]
    by_contra hne; apply hj; rw [if_neg (by omega), zero_smul]
  have hf2 : (Function.support (fun j : ℤ =>
      (if n + j = 0 then -((n : ℂ) * k) else 0) • osc k (m - j) x)).Finite := by
    apply Set.Finite.subset (Set.finite_singleton (-n))
    intro j hj; rw [Function.mem_support] at hj; rw [Set.mem_singleton_iff]
    by_contra hne; apply hj; rw [if_neg (by omega), zero_smul]
  rw [finsum_add_distrib hf1 hf2]
  rw [finsum_gate_collapse (-((n:ℂ)*k)) (fun j => osc k j x) (m + n)
        (fun j => n + (m - j) = 0) (fun j => by constructor <;> intro h <;> omega),
      finsum_gate_collapse (-((n:ℂ)*k)) (fun j => osc k (m - j) x) (-n)
        (fun j => n + j = 0) (fun j => by constructor <;> intro h <;> omega)]
  -- (1/2k) • ( -(nk)•a_{m+n} + -(nk)•a_{m-(-n)} ) = -n • a_{m+n}
  rw [show m - -n = m + n from by ring, smul_add, smul_smul, ← add_smul]
  congr 1
  rw [show (1:ℂ) / (2 * k) * -((n:ℂ) * k) + 1 / (2 * k) * -((n:ℂ) * k)
        = -(n:ℂ) * (k / k) from by ring, div_self hk, mul_one]

/-! ## The conformal vector `ω` and `L₀ω = 2ω`, `L₂ω = (c/2)·vacuum`, c = 1  (Gannon 5.2.5d) -/

/-- Each Sugawara term kills the vacuum when `n ≥ -1`: in `:a_{n-j}a_j:`, either the right
factor `a_j` annihilates the vacuum (`j ≥ 0`), or both factors are creation but the left
`a_{n-j}` would need `n - j < 0` with `j < 0`, i.e. `n < j < 0`, impossible for `n ≥ -1`. -/
theorem sugTerm_vacuum (k : ℂ) {n : ℤ} (hn : -1 ≤ n) (j : ℤ) :
    sugTerm k n j vacuum = 0 := by
  rw [sugTerm_apply]
  by_cases hj : j < 0
  · rw [if_pos hj]
    -- left factor a_{n-j}: n-j ≥ n+1 ≥ 0, so it is an annihilation/zero applied after a_j vac.
    -- but a_j vacuum (j<0) is a creation, then a_{n-j} (n-j ≥ 0) kills it iff weight too low.
    -- Direct: a_{n-j} with n-j ≥ 0; we instead show a_j(a_{n-j}? ) -- careful: order a_j a_{n-j}.
    -- a_{n-j} vacuum first:
    rw [show osc k j (osc k (n - j) vacuum) = osc k j (osc k (n - j) vacuum) from rfl]
    rw [osc_vacuum k (n - j) (by omega), map_zero]
  · rw [if_neg hj]
    rw [osc_vacuum k j (by omega), map_zero]

/-- `Lₙ vacuum = 0` for `n ≥ -1` (the vacuum is a highest-weight/quasi-primary state). -/
theorem Lvir_vacuum (k : ℂ) {n : ℤ} (hn : -1 ≤ n) : Lvir k n vacuum = 0 := by
  rw [Lvir_apply' k n vacuum,
    show (∑ᶠ j : ℤ, sugTerm k n j vacuum) = ∑ᶠ _j : ℤ, (0 : Fock) from
      finsum_congr fun j => sugTerm_vacuum k hn j,
    finsum_zero, smul_zero]

/-- The **conformal vector** `ω = (1/2k) a₋₁a₋₁ 1` (Gannon 5.2.5d): the lowest creation
applied twice to the vacuum, scaled by `1/2k`. -/
noncomputable def ω (k : ℂ) : Fock := (1 / (2 * k)) • osc k (-1) (osc k (-1) vacuum)

/-- `ω` is the `L₋₂`-descendant of the vacuum: `L₋₂ 1 = ω`.  All Sugawara terms but `j = -1`
vanish on the vacuum, leaving `(1/2k) a₋₁a₋₁ 1`. -/
theorem Lvir_neg_two_vacuum (k : ℂ) : Lvir k (-2) vacuum = ω k := by
  rw [Lvir_apply' k (-2) vacuum, ω]
  congr 1
  -- only j = -1 contributes
  rw [finsum_eq_single (fun j => sugTerm k (-2) j vacuum) (-1) (fun j hj => ?_)]
  · show sugTerm k (-2) (-1) vacuum = _
    rw [sugTerm_apply, if_pos (by norm_num), show (-2 : ℤ) - -1 = -1 from by ring]
  · show sugTerm k (-2) j vacuum = 0
    rw [sugTerm_apply]
    by_cases hjlt : j < 0
    · rw [if_pos hjlt]
      -- need a_{-2-j} vacuum = 0; -2-j ≥ 0 ⟺ j ≤ -2, and j<0,j≠-1 ⟹ j ≤ -2
      rw [osc_vacuum k (-2 - j) (by omega), map_zero]
    · rw [if_neg hjlt, osc_vacuum k j (by omega), map_zero]

/-- The "move `Lₘ` past a creation `aₙ`" rule, from `L_comm_osc`:
`Lₘ(aₙ y) = -n·a_{m+n} y + aₙ(Lₘ y)`. -/
theorem Lvir_osc (k : ℂ) (hk : k ≠ 0) (m n : ℤ) (y : Fock) :
    Lvir k m (osc k n y) = (-(n : ℂ)) • osc k (m + n) y + osc k n (Lvir k m y) := by
  have h := congrArg (fun (T : End ℂ Fock) => T y) (L_comm_osc k hk m n)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
  -- h : Lₘ(aₙ y) - aₙ(Lₘ y) = -n • a_{m+n} y
  rw [← eq_add_of_sub_eq h]

/-- **`L₀ ω = 2 ω`** (Gannon 5.2.5d): `ω` has conformal weight 2 (`ω ∈ 𝒱₂`).  Each of the two
`a₋₁` factors contributes `+1` to the `L₀`-eigenvalue (via `[L₀,a₋₁] = a₋₁`), and `L₀` kills
the vacuum. -/
theorem L_zero_omega (k : ℂ) (hk : k ≠ 0) : Lvir k 0 (ω k) = (2 : ℂ) • ω k := by
  rw [ω, map_smul, Lvir_osc k hk 0 (-1), Lvir_osc k hk 0 (-1) vacuum,
    Lvir_vacuum k (by norm_num : (-1 : ℤ) ≤ 0)]
  simp only [map_zero, add_zero]
  rw [show (0 : ℤ) + -1 = -1 from by ring,
    show (-((-1 : ℤ) : ℂ)) = (1 : ℂ) from by push_cast; ring, one_smul, one_smul]
  rw [smul_add, show (2 : ℂ) = 1 + 1 from by ring, add_smul, one_smul]

/-- **`L₁ ω = 0`** (`ω` is annihilated by `L₁`: a quasi-primary state). -/
theorem L_one_omega (k : ℂ) (hk : k ≠ 0) : Lvir k 1 (ω k) = 0 := by
  rw [ω, map_smul, Lvir_osc k hk 1 (-1), Lvir_osc k hk 1 (-1) vacuum,
    Lvir_vacuum k (by norm_num : (-1 : ℤ) ≤ 1)]
  simp only [add_zero, map_zero]
  rw [show (1 : ℤ) + -1 = 0 from by ring, osc_zero]
  simp

/-- **`L₂ ω = (c/2)·1` with central charge `c = 1`** (Gannon 5.2.5d): the double contraction
of `:αα:` with itself.  Directly `L₂(a₋₁a₋₁1) = a₁(a₋₁1) = [a₁,a₋₁]1 = k·1`, so
`L₂ ω = (1/2k)·k·1 = (1/2)·1` — exhibiting `c = 1` for the free boson. -/
theorem L_two_omega (k : ℂ) (hk : k ≠ 0) :
    Lvir k 2 (ω k) = ((1 : ℂ) / 2) • vacuum := by
  rw [ω, map_smul, Lvir_osc k hk 2 (-1), Lvir_osc k hk 2 (-1) vacuum,
    Lvir_vacuum k (by norm_num : (-1 : ℤ) ≤ 2)]
  simp only [add_zero, map_zero]
  rw [show (2 : ℤ) + -1 = 1 from by ring,
    show (-((-1 : ℤ) : ℂ)) = (1 : ℂ) from by push_cast; ring, one_smul, one_smul]
  -- the descendant term a₋₁(L₂(a₋₁1)) collapses: a₁ vacuum = 0 inside, so it is a₋₁(0)
  rw [osc_vacuum k 1 (by norm_num), map_zero, add_zero]
  -- now goal: (1/2k) • (a₁(a₋₁ 1)) = (1/2) • 1
  -- a₁(a₋₁ 1) = [a₁,a₋₁]1 + a₋₁(a₁ 1) = k • 1
  have hcomm := congrArg (fun (T : End ℂ Fock) => T vacuum) (osc_comm k 1 (-1))
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at hcomm
  rw [osc_vacuum k 1 (by norm_num), map_zero, sub_zero,
    show (1 : ℤ) + -1 = 0 from by ring, if_pos rfl] at hcomm
  rw [hcomm, smul_smul]
  congr 1
  push_cast
  field_simp

/-! ## The Virasoro relation `[Lₘ,Lₙ]` (Gannon 5.2.5d) — the central charge c = 1 -/

/-- Pushing `Lₘ` through a single Sugawara term acting on a vector (two applications of
`Lvir_osc`, the exact `[Lₘ,a] = -p·a` rule). This is the *anomaly-free* per-term bracket;
the central term of the Virasoro relation arises only on resumming and reindexing. -/
theorem L_comm_sugTerm_vec (k : ℂ) (hk : k ≠ 0) (m n j : ℤ) (x : Fock) :
    Lvir k m (sugTerm k n j x) - sugTerm k n j (Lvir k m x)
      = if j < 0
        then (-(j : ℂ)) • osc k (m + j) (osc k (n - j) x)
              + (-((n - j : ℤ) : ℂ)) • osc k j (osc k (m + (n - j)) x)
        else (-((n - j : ℤ) : ℂ)) • osc k (m + (n - j)) (osc k j x)
              + (-(j : ℂ)) • osc k (n - j) (osc k (m + j) x) := by
  rw [sugTerm_apply, sugTerm_apply]
  by_cases hj : j < 0
  · simp only [if_pos hj]
    rw [Lvir_osc k hk m j (osc k (n - j) x), Lvir_osc k hk m (n - j) x, map_add, map_smul]
    abel
  · simp only [if_neg hj]
    rw [Lvir_osc k hk m (n - j) (osc k j x), Lvir_osc k hk m j x, map_add, map_smul]
    abel

/-- The commutator `[Lₘ,Lₙ]` acting on a vector, assembled as the (finite) sum of the exact
per-term brackets: `[Lₘ,Lₙ]x = (1/2k)∑_j R_j(x)` with `R_j` from `L_comm_sugTerm_vec`. This
is the rigorous reduction of the Virasoro relation to a single finite reindexable sum; the
collapse of this sum to `(m-n)L_{m+n}x + δ_{m+n,0}(m³-m)/12·x` is the central-charge anomaly
computation. -/
theorem L_comm_eq_finsum (k : ℂ) (m n : ℤ) (x : Fock) :
    Lvir k m (Lvir k n x) - Lvir k n (Lvir k m x)
      = (1 / (2 * k)) • ∑ᶠ j : ℤ,
          (Lvir k m (sugTerm k n j x) - sugTerm k n j (Lvir k m x)) := by
  -- Lₙ x = (1/2k) ∑ T_j x ;  Lₘ(Lₙ x) = (1/2k) ∑ Lₘ(T_j x) ;  Lₙ(Lₘ x) = (1/2k) ∑ T_j(Lₘ x)
  have hfin_x : (Function.support (fun j : ℤ => sugTerm k n j x)).Finite :=
    sugTerm_support_finite k n x
  have hfin_Lx : (Function.support (fun j : ℤ => sugTerm k n j (Lvir k m x))).Finite :=
    sugTerm_support_finite k n (Lvir k m x)
  have hfin_mx : (Function.support (fun j : ℤ => Lvir k m (sugTerm k n j x))).Finite :=
    hfin_x.subset (fun j hj => by
      rw [Function.mem_support] at hj ⊢; exact fun h => hj (by rw [h, map_zero]))
  rw [Lvir_apply' k n x, map_smul, map_finsum (Lvir k m) hfin_x,
    Lvir_apply' k n (Lvir k m x), ← smul_sub]
  congr 1
  rw [← finsum_sub_distrib hfin_mx hfin_Lx]

end VOA
