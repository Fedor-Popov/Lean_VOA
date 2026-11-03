/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.InvariantFormCanonicalFHL

/-!
# sl₂ quasi-primary decomposition — constructive, only `hqp`

`𝒱ₚ = 𝒫𝒱ₚ^{quasi-primary} ⊕ L₋₁ 𝒱ₚ₋₁` (Gannon §5.2, the sl₂ lowest-weight content).

Both `qpDecomp` and `qp_Lneg1_induction` are proved here under the **single** standing
hypothesis `hqp : ∀ v ∈ 𝒱₁, L 1 v = 0` (the universal weight-1 quasi-primality of this
subtree).  No reducibility hypothesis (`hred`) is needed: the `p ≥ 2` case is solved
*constructively* from the q.p.-tower formula
  `L₁ (L₋₁^{j+1} v) = (j+1)(2m+j) • L₋₁^{j} v`   (for q.p. `v ∈ 𝒱_m`),
which lets one invert `L₁L₋₁` term-by-term on the tower-sum expansion of `L₁ a`.

Pipeline:
* `L1_Lneg1_grading`, `Lneg1_pow_mem`, `L1_tower` — the sl₂ tower formula and its iterate bookkeeping;
* `term_invert` — per-term inversion `L₁ (coeff_k • L₋₁^{k+1} w) = L₋₁^{k} w` for q.p. `w ∈ 𝒱_{q-k}`
  (`coeff_k = ((k+1)(2q-k))⁻¹`; degenerate coefficients only occur where the base vanishes);
* `tower_sum_exists` — every `b ∈ 𝒱_q` is a finite sum `∑_{k<n} L₋₁^k (wₖ)` of towers over q.p.
  bases `wₖ ∈ 𝒱_{q-k}`, proved by strong induction on `q.toNat` (the `q ≥ 2` step reassembles
  `b = b₀ + L₋₁ c` and reindexes);
* `qpDecomp` — the explicit `a = a₀ + L₋₁ c` decomposition;
* `qp_Lneg1_induction` — the downstream induction principle, derived from `qpDecomp`.

Axiom-clean: `#print axioms` on both targets is `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.style.longLine false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open VOA VOA.VertexOperatorAlgebra
open scoped BigOperators
open Classical

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

namespace VOA

/-! ## Axiom-free sl₂ bricks -/

/-- **The sl₂ commutator on a graded piece.**  For `c ∈ 𝒱_q`,
`L₁(L₋₁ c) = L₋₁(L₁ c) + 2q·c` (from `[L₁,L₋₁] = 2L₀` and `L₀|𝒱_q = q`). -/
theorem L1_Lneg1_grading (W : VertexOperatorAlgebra V) {q : ℤ} {c : V} (hc : c ∈ W.grading q) :
    W.L 1 (W.L (-1) c) = W.L (-1) (W.L 1 c) + (2 * (q : ℂ)) • c := by
  have hbr := W.L_one_L_neg_one
  have h2 := DFunLike.congr_fun hbr c
  rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, LinearMap.smul_apply] at h2
  rw [W.L_zero_grading c hc, smul_smul] at h2
  rw [show ((2 : ℂ) * (q : ℂ)) = (2 * (q : ℂ)) by ring] at h2
  linear_combination (norm := module) h2

/-- `L₋₁^j` raises the grading by `j`: `L₋₁^j 𝒱_m ⊆ 𝒱_{m+j}`. -/
theorem Lneg1_pow_mem (W : VertexOperatorAlgebra V) {m : ℤ} {v : V} (hv : v ∈ W.grading m)
    (j : ℕ) : ((W.L (-1)) ^ j) v ∈ W.grading (m + j) := by
  induction j with
  | zero => simpa using hv
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    have := L_neg_one_raise W ih
    rwa [show (m + (n:ℤ)) + 1 = m + ((n:ℤ)+1) by ring,
      show ((n:ℤ)+1) = ((n+1 : ℕ):ℤ) by push_cast; ring] at this

/-- **The sl₂ q.p.-tower formula.**  For a quasi-primary `v ∈ 𝒱_m` (`L₁ v = 0`),
`L₁ (L₋₁^{j+1} v) = (j+1)(2m+j) • L₋₁^{j} v`.  By induction on `j` from `L1_Lneg1_grading`. -/
theorem L1_tower (W : VertexOperatorAlgebra V) {m : ℤ} {v : V} (hv : v ∈ W.grading m)
    (hqpv : W.L 1 v = 0) (j : ℕ) :
    W.L 1 (((W.L (-1)) ^ (j+1)) v) = (((j:ℂ)+1) * (2*(m:ℂ) + (j:ℂ))) • (((W.L (-1)) ^ j) v) := by
  induction j with
  | zero =>
    rw [zero_add, pow_one, pow_zero, Module.End.one_apply]
    rw [L1_Lneg1_grading W hv, hqpv, map_zero, zero_add]
    rw [show ((Nat.cast 0:ℂ)+1)*(2*(m:ℂ)+(Nat.cast 0)) = 2*(m:ℂ) by push_cast; ring]
  | succ n ih =>
    have hmem : ((W.L (-1)) ^ (n+1)) v ∈ W.grading (m + (n+1)) := Lneg1_pow_mem W hv (n+1)
    rw [show n+1+1 = (n+1)+1 from rfl, pow_succ', Module.End.mul_apply]
    rw [L1_Lneg1_grading W hmem, ih]
    rw [map_smul]
    rw [show (W.L (-1)) (((W.L (-1)) ^ n) v) = ((W.L (-1))^(n+1)) v by
      rw [pow_succ', Module.End.mul_apply]]
    rw [← add_smul]
    congr 1
    push_cast
    ring

/-- A vector in a strictly-negative grade is `0` (VOA4: `𝒱_{<0} = ⊥`). -/
theorem eq_zero_neg_grade (W : VertexOperatorAlgebra V) {k : ℤ} (hk : k < 0)
    {x : V} (hx : x ∈ W.grading k) : x = 0 := by
  rw [W.positivity k hk] at hx; exact (Submodule.mem_bot ℂ).mp hx

/-- **Per-term inversion identity.**  For a quasi-primary `w ∈ 𝒱_{q-k}` (`q ≥ 1`),
`L₁` sends `coeff_k • L₋₁^{k+1} w` to `L₋₁^{k} w`, where `coeff_k = ((k+1)(2q-k))⁻¹`.
A degenerate coefficient (`2q-k = 0`) forces `k = 2q`, hence `q-k = -q < 0` and `w = 0`,
so the identity holds in every case. -/
theorem term_invert (W : VertexOperatorAlgebra V) {q : ℤ} (hq : 1 ≤ q) (k : ℕ)
    {w : V} (hw : w ∈ W.grading (q - k)) (hqpw : W.L 1 w = 0) :
    W.L 1 ((((k:ℂ)+1) * (2*(q:ℂ) - (k:ℂ)))⁻¹ • ((W.L (-1)) ^ (k+1)) w)
      = ((W.L (-1)) ^ k) w := by
  rw [map_smul, L1_tower W hw hqpw k, smul_smul]
  have hcoeff_eq : (((k:ℂ)+1) * (2*(((q:ℤ) - (k:ℕ):ℤ):ℂ) + (k:ℂ)))
      = (((k:ℂ)+1) * (2*(q:ℂ) - (k:ℂ))) := by push_cast; ring
  rw [hcoeff_eq]
  by_cases hcoef : (((k:ℂ)+1) * (2*(q:ℂ) - (k:ℂ))) = 0
  · have hk1 : ((k:ℂ)+1) ≠ 0 := Nat.cast_add_one_ne_zero k
    have h2 : (2*(q:ℂ) - (k:ℂ)) = 0 := by
      rcases mul_eq_zero.mp hcoef with h | h
      · exact absurd h hk1
      · exact h
    have hkval : (2*q - (k:ℤ) : ℤ) = 0 := by
      have hc : ((2*q - (k:ℤ) : ℤ) : ℂ) = 0 := by push_cast; linear_combination h2
      exact_mod_cast hc
    have hneg : q - (k:ℤ) < 0 := by omega
    have hw0 : w = 0 := eq_zero_neg_grade W hneg hw
    rw [hw0]; simp
  · rw [inv_mul_cancel₀ hcoef, one_smul]

/-- `L₁` of a weight-`≤0` vector is `0` (`L₁ x ∈ 𝒱_{p-1}`, `p-1 < 0`). -/
theorem L1_eq_zero_le0 (W : VertexOperatorAlgebra V) {p : ℤ} (hp : p ≤ 0)
    {x : V} (hx : x ∈ W.grading p) : W.L 1 x = 0 :=
  eq_zero_neg_grade W (by omega) (L_one_lower W hx)

/-! ## Tower-sum expansion -/

/-- **Tower-sum existence.**  Under `hqp`, every `b ∈ 𝒱_q` is a finite sum
`∑_{k<n} L₋₁^k (wₖ)` of tower elements over quasi-primary bases `wₖ ∈ 𝒱_{q-k}`.
Strong induction on `q.toNat`: weights `≤ 0` and `= 1` are quasi-primary outright
(`L1_eq_zero_le0`, `hqp`); for `q ≥ 2` the IH on `L₁ b ∈ 𝒱_{q-1}` plus `term_invert` build
`c ∈ 𝒱_{q-1}` with `L₁(L₋₁ c) = L₁ b`, so `b = b₀ + L₋₁ c` with `b₀` quasi-primary, and the
tower-sum of `b` is `b₀` at index `0` followed by the reindexed scaled bases of `c`. -/
theorem tower_sum_exists (W : VertexOperatorAlgebra V)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) :
    ∀ {q : ℤ} {b : V}, b ∈ W.grading q →
      ∃ (n : ℕ) (w : ℕ → V), (∀ k : ℕ, w k ∈ W.grading (q - (k:ℤ))) ∧ (∀ k, W.L 1 (w k) = 0) ∧
        b = ∑ k ∈ Finset.range n, ((W.L (-1)) ^ k) (w k) := by
  intro q
  induction hN : q.toNat using Nat.strong_induction_on generalizing q with
  | _ N IH =>
  intro b hb
  rcases lt_trichotomy q 0 with hqneg | hq0 | hqpos
  · -- q < 0 : b = 0, empty tower-sum.
    have hb0 : b = 0 := eq_zero_neg_grade W hqneg hb
    refine ⟨0, fun _ => 0, fun k => Submodule.zero_mem _, fun k => map_zero _, ?_⟩
    rw [hb0]; simp
  · -- q = 0 : 𝒱₀ is quasi-primary (`L₁ 𝒱₀ ⊆ 𝒱_{-1} = ⊥`).
    subst hq0
    refine ⟨1, fun k => if k = 0 then b else 0, ?_, ?_, ?_⟩
    · intro k; by_cases hk : k = 0
      · simp only [hk]; simpa using hb
      · simp only [hk, if_neg]; exact Submodule.zero_mem _
    · intro k; by_cases hk : k = 0
      · simp only [hk, if_pos]; exact L1_eq_zero_le0 W (le_refl 0) hb
      · simp only [hk, if_neg]; exact map_zero _
    · simp [Finset.sum_range_one]
  · -- q ≥ 1
    rcases eq_or_lt_of_le (show (1:ℤ) ≤ q from hqpos) with hq1 | hq2
    · -- q = 1 : 𝒱₁ is quasi-primary by `hqp`.
      subst hq1
      refine ⟨1, fun k => if k = 0 then b else 0, ?_, ?_, ?_⟩
      · intro k; by_cases hk : k = 0
        · simp only [hk]; simpa using hb
        · simp only [hk, if_neg]; exact Submodule.zero_mem _
      · intro k; by_cases hk : k = 0
        · simp only [hk, if_pos]; exact hqp b hb
        · simp only [hk, if_neg]; exact map_zero _
      · simp [Finset.sum_range_one]
    · -- q ≥ 2 : invert `L₁L₋₁` via the IH on `L₁ b ∈ 𝒱_{q-1}`.
      have hqge2 : 2 ≤ q := hq2
      have hLb : W.L 1 b ∈ W.grading (q - 1) := L_one_lower W hb
      have hlt : (q-1).toNat < N := by omega
      obtain ⟨n', w', hw'mem, hw'qp, hsum'⟩ := IH (q-1).toNat hlt rfl hLb
      set c : V := ∑ k ∈ Finset.range n',
        (((k:ℂ)+1) * (2*(((q-1:ℤ)):ℂ) - (k:ℂ)))⁻¹ • ((W.L (-1)) ^ k) (w' k) with hc_def
      have hcmem : c ∈ W.grading (q - 1) := by
        rw [hc_def]
        apply Submodule.sum_mem
        intro k _
        apply Submodule.smul_mem
        have := Lneg1_pow_mem W (hw'mem k) k
        rwa [show (q - 1 - (k:ℤ)) + (k:ℤ) = q - 1 by ring] at this
      have hLc : W.L 1 (W.L (-1) c) = W.L 1 b := by
        rw [hc_def, map_sum, map_sum, hsum']
        apply Finset.sum_congr rfl
        intro k _
        rw [map_smul]
        rw [show (W.L (-1)) (((W.L (-1)) ^ k) (w' k)) = ((W.L (-1)) ^ (k+1)) (w' k) by
          rw [pow_succ', Module.End.mul_apply]]
        exact term_invert W (by omega : (1:ℤ) ≤ q - 1) k (hw'mem k) (hw'qp k)
      set b₀ : V := b - W.L (-1) c with hb₀_def
      have hb₀mem : b₀ ∈ W.grading q := by
        rw [hb₀_def]
        have hLcmem : W.L (-1) c ∈ W.grading ((q-1)+1) := L_neg_one_raise W hcmem
        rw [show (q-1)+1 = q by ring] at hLcmem
        exact Submodule.sub_mem _ hb hLcmem
      have hb₀qp : W.L 1 b₀ = 0 := by rw [hb₀_def, map_sub, hLc, sub_self]
      -- tower-sum of b : index 0 is b₀, index (j+1) is coeff_j • w' j.
      refine ⟨n' + 1,
        fun k => Nat.rec b₀ (fun j _ => (((j:ℂ)+1) * (2*(((q-1:ℤ)):ℂ) - (j:ℂ)))⁻¹ • w' j) k,
        ?_, ?_, ?_⟩
      · intro k
        cases k with
        | zero => simpa using hb₀mem
        | succ j =>
          simp only [Nat.rec]
          apply Submodule.smul_mem
          have := hw'mem j
          rwa [show q - 1 - (j:ℤ) = q - ((j:ℤ)+1) by ring,
            show ((j:ℤ)+1) = ((j+1:ℕ):ℤ) by push_cast; ring] at this
      · intro k
        cases k with
        | zero => simpa using hb₀qp
        | succ j =>
          simp only [Nat.rec, map_smul, hw'qp j, smul_zero]
      · rw [Finset.sum_range_succ']
        simp only [Nat.rec, pow_zero, Module.End.one_apply]
        have hbexp : b = b₀ + W.L (-1) c := by rw [hb₀_def]; abel
        rw [hbexp, add_comm]
        congr 1
        rw [hc_def, map_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [map_smul]
        rw [show (W.L (-1)) (((W.L (-1)) ^ j) (w' j)) = ((W.L (-1)) ^ (j+1)) (w' j) by
          rw [pow_succ', Module.End.mul_apply]]
        rw [map_smul]

/-! ## The quasi-primary decomposition -/

/-- **sl₂ quasi-primary decomposition** (Gannon §5.2).  For `a ∈ 𝒱_p` with `p ≥ 1`, write
`a = a₀ + L₋₁ c` with `a₀ ∈ 𝒱_p` quasi-primary (`L₁ a₀ = 0`) and `c ∈ 𝒱_{p−1}`.  The only
hypothesis is `hqp` (weight-1 quasi-primality, the universal hypothesis of this subtree); the
`p ≥ 2` case is solved constructively from the q.p.-tower formula — no reducibility input. -/
theorem qpDecomp (W : VertexOperatorAlgebra V)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    {p : ℤ} (hp : 1 ≤ p) {a : V} (ha : a ∈ W.grading p) :
    ∃ a₀ c : V, a₀ ∈ W.grading p ∧ W.L 1 a₀ = 0 ∧ c ∈ W.grading (p - 1) ∧ a = a₀ + W.L (-1) c := by
  rcases eq_or_lt_of_le hp with hp1 | hp2
  · -- p = 1 : `a` is quasi-primary by `hqp`; take `a₀ = a`, `c = 0`.
    subst hp1
    exact ⟨a, 0, ha, hqp a ha, Submodule.zero_mem _, by rw [map_zero, add_zero]⟩
  · -- p ≥ 2 : tower-sum `L₁ a`, invert `L₁L₋₁` term-by-term via `term_invert`.
    have hLa : W.L 1 a ∈ W.grading (p - 1) := L_one_lower W ha
    obtain ⟨n, w, hwmem, hwqp, hsum⟩ := tower_sum_exists W hqp hLa
    set c : V := ∑ k ∈ Finset.range n,
      (((k:ℂ)+1) * (2*(((p-1:ℤ)):ℂ) - (k:ℂ)))⁻¹ • ((W.L (-1)) ^ k) (w k) with hc_def
    have hcmem : c ∈ W.grading (p - 1) := by
      rw [hc_def]
      apply Submodule.sum_mem
      intro k _
      apply Submodule.smul_mem
      have := Lneg1_pow_mem W (hwmem k) k
      rwa [show (p - 1 - (k:ℤ)) + (k:ℤ) = p - 1 by ring] at this
    have hLc : W.L 1 (W.L (-1) c) = W.L 1 a := by
      rw [hc_def, map_sum, map_sum, hsum]
      apply Finset.sum_congr rfl
      intro k _
      rw [map_smul]
      rw [show (W.L (-1)) (((W.L (-1)) ^ k) (w k)) = ((W.L (-1)) ^ (k+1)) (w k) by
        rw [pow_succ', Module.End.mul_apply]]
      exact term_invert W (by omega : (1:ℤ) ≤ p - 1) k (hwmem k) (hwqp k)
    refine ⟨a - W.L (-1) c, c, ?_, ?_, hcmem, by abel⟩
    · have hLcmem : W.L (-1) c ∈ W.grading ((p-1)+1) := L_neg_one_raise W hcmem
      rw [show (p-1)+1 = p by ring] at hLcmem
      exact Submodule.sub_mem _ ha hLcmem
    · rw [map_sub, hLc, sub_self]

/-! ## The induction principle (what downstream needs most) -/

/-- A vector of weight `≤ 0` is quasi-primary (`L₁` lands in a strictly negative grade). -/
private theorem L1_eq_zero_of_le_zero (W : VertexOperatorAlgebra V) {p : ℤ} (hp : p ≤ 0)
    {x : V} (hx : x ∈ W.grading p) : W.L 1 x = 0 :=
  eq_zero_neg_grade W (by omega) (L_one_lower W hx)

/-- **`L₋₁`/quasi-primary induction principle.**  A predicate closed under sums, scalars, the
quasi-primary generators and `L₋₁` holds on all of `𝒱_p` (every weight `p ∈ ℤ`).  Derived from
`qpDecomp` by descending on the weight via `Int.induction_on`; only `hqp` is needed. -/
theorem qp_Lneg1_induction (W : VertexOperatorAlgebra V)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    {motive : V → Prop}
    (hadd : ∀ x y, motive x → motive y → motive (x + y))
    (hsmul : ∀ (c : ℂ) x, motive x → motive (c • x))
    (hz : motive 0)
    (hqpbase : ∀ {p : ℤ} {x : V}, x ∈ W.grading p → W.L 1 x = 0 → motive x)
    (hLneg1 : ∀ {p : ℤ} {x : V}, x ∈ W.grading p → motive x → motive (W.L (-1) x)) :
    ∀ {p : ℤ} {a : V}, a ∈ W.grading p → motive a := by
  intro p
  induction p using Int.induction_on with
  | zero =>
    -- weight 0 : `𝒱₀` is quasi-primary (`L₁ 𝒱₀ ⊆ 𝒱_{-1} = ⊥`).
    intro a ha; exact hqpbase ha (L1_eq_zero_of_le_zero W (le_refl 0) ha)
  | succ n ih =>
    -- weight `n+1 ≥ 1` : split via `qpDecomp`; descend on `c ∈ 𝒱_n`.
    intro a ha
    have hp1 : (1 : ℤ) ≤ (n : ℤ) + 1 := by omega
    obtain ⟨a₀, c, ha₀mem, ha₀qp, hcmem, hsum⟩ := qpDecomp W hqp hp1 ha
    rw [hsum]
    have hcmem' : c ∈ W.grading (n : ℤ) := by
      rwa [show ((n : ℤ) + 1 - 1) = (n : ℤ) by ring] at hcmem
    exact hadd a₀ (W.L (-1) c) (hqpbase ha₀mem ha₀qp) (hLneg1 hcmem' (ih hcmem'))
  | pred n _ =>
    -- weight `-(n+1) < 0` : quasi-primary vacuously (`𝒱_{<0} = ⊥`).
    intro a ha; exact hqpbase ha (L1_eq_zero_of_le_zero W (by omega) ha)


end VOA
