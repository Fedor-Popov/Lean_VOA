/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesJetPoincareVdm
import VOA.Examples.TwoSeriesHighJet

/-!
# The symmetric-function dual of `ℂ[T_j]` in `T`-degree `k`

The pairing of `ℂ[T_j]` with `ℂ[x_0, …, x_{k-1}]` through the polarization
`pol_B(F) = [t_B] F(T_m ↦ Σ_i t_i x_i^m)` and the coefficient dot product.

* `dot` — the coefficient dot product on `ℂ[x]`;
* `dot_key` — `⟨h_j(x_a, x_b) P, (x_b - x_a) u⟩ = 0` for `P` free of `x_a, x_b`;
* `pol` — the polarization; `pol_X_mul` — `pol_B(T_m G) = Σ_{i ∈ B} x_i^m pol_{B - i}(G)`;
* `pol_expand` — `pol_B(F) = Σ_M x_l^M pol_{B - l}(∂F/∂T_M)` for `l ∈ B`;
* `dot_pol_jet` — `⟨R pol_B(G), Y⟩ = 0` for `G ∈ J_2`, `R` free of the `x_i`, `i ∈ B`, and `Y`
  divisible by every `x_b - x_a`, `a < b` in `B`;
* `dot_pol_W` — **`⟨pol(F), W⟩ = 0`** when `∂F/∂T_M ∈ J_2` for all `M ≥ N`.

Everything is proved outright.
-/

namespace VOA.TwoSeries.JetPoincareDual

open MvPolynomial Finset JetPoincareVdm StrictModel HighJet

noncomputable section

variable {k : ℕ}

/-! ### The coefficient dot product -/

/-- `⟨A, Z⟩ = Σ_e A_e Z_e`. -/
def dot (A Z : XP k) : ℂ := Z.sum fun e z => coeff e A * z

theorem dot_eq_sum {A Z : XP k} {T : Finset (Fin k →₀ ℕ)} (hT : Z.support ⊆ T) :
    dot A Z = ∑ e ∈ T, coeff e A * coeff e Z :=
  Finsupp.sum_of_support_subset Z hT (fun e z => coeff e A * z) (fun _ _ => mul_zero _)

theorem dot_comm (A Z : XP k) : dot A Z = dot Z A := by
  classical
  rw [dot_eq_sum (T := A.support ∪ Z.support) subset_union_right,
    dot_eq_sum (T := A.support ∪ Z.support) subset_union_left]
  exact sum_congr rfl fun e _ => mul_comm _ _

theorem dot_add_right (A Z₁ Z₂ : XP k) : dot A (Z₁ + Z₂) = dot A Z₁ + dot A Z₂ := by
  classical
  rw [dot_eq_sum (T := Z₁.support ∪ Z₂.support) support_add,
    dot_eq_sum (T := Z₁.support ∪ Z₂.support) subset_union_left,
    dot_eq_sum (T := Z₁.support ∪ Z₂.support) subset_union_right, ← sum_add_distrib]
  exact sum_congr rfl fun e _ => by rw [coeff_add, mul_add]

theorem dot_add_left (A₁ A₂ Z : XP k) : dot (A₁ + A₂) Z = dot A₁ Z + dot A₂ Z := by
  rw [dot_comm, dot_add_right, dot_comm, dot_comm Z]

theorem dot_zero_right (A : XP k) : dot A 0 = 0 := Finsupp.sum_zero_index

theorem dot_zero_left (Z : XP k) : dot 0 Z = 0 := by
  rw [dot_comm, dot_zero_right]

theorem dot_sum_right {ι : Type*} (s : Finset ι) (A : XP k) (Z : ι → XP k) :
    dot A (∑ i ∈ s, Z i) = ∑ i ∈ s, dot A (Z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dot_zero_right]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, dot_add_right, ih]

theorem dot_sum_left {ι : Type*} (s : Finset ι) (A : ι → XP k) (Z : XP k) :
    dot (∑ i ∈ s, A i) Z = ∑ i ∈ s, dot (A i) Z := by
  rw [dot_comm, dot_sum_right]
  exact sum_congr rfl fun i _ => dot_comm _ _

theorem dot_smul_right (c : ℂ) (A Z : XP k) : dot A (c • Z) = c * dot A Z := by
  classical
  rw [dot_eq_sum (T := Z.support) (support_smul), dot_eq_sum (subset_refl _), mul_sum]
  exact sum_congr rfl fun e _ => by rw [coeff_smul, smul_eq_mul]; ring

theorem dot_smul_left (c : ℂ) (A Z : XP k) : dot (c • A) Z = c * dot A Z := by
  rw [dot_comm, dot_smul_right, dot_comm]

theorem dot_monomial_right (A : XP k) (e : Fin k →₀ ℕ) (c : ℂ) :
    dot A (monomial e c) = coeff e A * c := by
  classical
  by_cases hc : c = 0
  · simp [hc, dot_zero_right]
  · rw [dot_eq_sum (T := {e}) (support_monomial_subset), sum_singleton, coeff_monomial, if_pos rfl]

/-- Multiplying both sides by `x_l^n` does not change the pairing. -/
theorem dot_monomial_mul (l : Fin k) (n : ℕ) (A Z : XP k) :
    dot (monomial (Finsupp.single l n) 1 * A) (monomial (Finsupp.single l n) 1 * Z) = dot A Z := by
  classical
  set s := Finsupp.single l n
  have hsub : (monomial s 1 * Z).support ⊆ Z.support.image (· + s) := by
    intro e he
    rw [mem_support_iff, coeff_monomial_mul'] at he
    split_ifs at he with hle
    · rw [one_mul] at he
      exact mem_image.mpr ⟨e - s, mem_support_iff.mpr he, tsub_add_cancel_of_le hle⟩
    · exact absurd rfl he
  rw [dot_eq_sum hsub, sum_image (fun x _ y _ h => add_right_cancel h), dot_eq_sum (subset_refl _)]
  refine sum_congr rfl fun e _ => ?_
  simp only [coeff_monomial_mul', le_add_self, if_true, add_tsub_cancel_right, one_mul]

/-- Orthogonality by `x_l`-degree. -/
theorem dot_eq_zero_of_lt (l : Fin k) (n : ℕ) {A : XP k} (hA : ∀ e ∈ A.support, e l < n)
    (Z : XP k) : dot A (monomial (Finsupp.single l n) 1 * Z) = 0 := by
  rw [dot_comm, dot_eq_sum (subset_refl _)]
  refine sum_eq_zero fun e he => ?_
  rw [coeff_monomial_mul']
  split_ifs with hle
  · exact absurd (hA e he) (not_lt.mpr (by simpa using hle l))
  · rw [zero_mul]

/-! ### Freeness of a variable -/

theorem coeff_eq_zero_of_not_mem_vars {P : XP k} {l : Fin k} (hP : l ∉ P.vars) {e : Fin k →₀ ℕ}
    (he : e ∈ P.support) : e l = 0 := by
  by_contra h
  exact hP ((mem_vars_iff_mem_support l).mpr ⟨e, he, Finsupp.mem_support_iff.mpr h⟩)

/-- `x_l^M P` with `P` free of `x_l` against `x_l^N Y`. -/
theorem dot_shift (l : Fin k) {M N : ℕ} {P : XP k} (hP : l ∉ P.vars) (Y : XP k) :
    dot (monomial (Finsupp.single l M) 1 * P) (monomial (Finsupp.single l N) 1 * Y) =
      if N ≤ M then dot (monomial (Finsupp.single l (M - N)) 1 * P) Y else 0 := by
  classical
  split_ifs with hNM
  · have : (monomial (Finsupp.single l M) 1 * P : XP k) =
        monomial (Finsupp.single l N) 1 * (monomial (Finsupp.single l (M - N)) 1 * P) := by
      rw [← mul_assoc, monomial_mul, one_mul, ← Finsupp.single_add, Nat.add_sub_cancel' hNM]
    rw [this, dot_monomial_mul]
  · refine dot_eq_zero_of_lt l N (fun e he => ?_) Y
    rw [mem_support_iff, coeff_monomial_mul'] at he
    split_ifs at he with hle
    · rw [one_mul] at he
      have h0 := coeff_eq_zero_of_not_mem_vars hP (mem_support_iff.mpr he)
      have h1 := hle l
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same] at h0 h1
      omega
    · exact absurd rfl he

/-! ### The key orthogonality -/

/-- `h_j(x_a, x_b) = Σ_{p + q = j} x_a^p x_b^q`. -/
def hsum (a b : Fin k) (j : ℕ) : XP k :=
  ∑ x ∈ antidiagonal j, monomial (Finsupp.single a x.1 + Finsupp.single b x.2) 1

theorem hsum_comm (a b : Fin k) (j : ℕ) : hsum a b j = hsum b a j := by
  rw [hsum, hsum, ← Finset.Nat.sum_antidiagonal_swap]
  exact sum_congr rfl fun x _ => by rw [Prod.fst_swap, Prod.snd_swap, add_comm]

theorem coeff_X_mul_key {a b : Fin k} (hab : a ≠ b) {e' : Fin k →₀ ℕ} (hb : e' b = 0) (p q : ℕ)
    (u : XP k) :
    coeff (Finsupp.single a p + Finsupp.single b q + e') (X b * u) =
      if q = 0 then 0 else coeff (Finsupp.single a p + Finsupp.single b (q - 1) + e') u := by
  classical
  rw [coeff_X_mul']
  have hmem : b ∈ (Finsupp.single a p + Finsupp.single b q + e').support ↔ q ≠ 0 := by
    rw [Finsupp.mem_support_iff]
    simp [hab, hb]
  by_cases hq : q = 0
  · rw [if_neg (by rw [hmem]; exact not_not.mpr hq), if_pos hq]
  · rw [if_pos (hmem.mpr hq), if_neg hq]
    congr 1
    ext i
    simp only [Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply,
      Finsupp.single_apply]
    split_ifs <;> omega

/-- **The key orthogonality** `⟨h_j(x_a, x_b) P, (x_b - x_a) u⟩ = 0` for `P` free of
`x_a, x_b`. -/
theorem dot_key {a b : Fin k} (hab : a ≠ b) (j : ℕ) {P : XP k} (ha : a ∉ P.vars)
    (hb : b ∉ P.vars) (u : XP k) : dot (hsum a b j * P) ((X b - X a) * u) = 0 := by
  classical
  have hexp : hsum a b j * P = ∑ x ∈ antidiagonal j, ∑ e' ∈ P.support,
      monomial (Finsupp.single a x.1 + Finsupp.single b x.2 + e') (coeff e' P) := by
    conv_lhs => rw [as_sum P]
    rw [hsum, sum_mul]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun e' _ => by rw [monomial_mul, one_mul]
  rw [hexp, dot_comm, dot_sum_right]
  simp only [dot_sum_right]
  rw [sum_comm]
  refine sum_eq_zero fun e' he' => ?_
  simp only [dot_monomial_right]
  rw [← sum_mul]
  refine mul_eq_zero_of_left ?_ _
  have hea := coeff_eq_zero_of_not_mem_vars ha he'
  have heb := coeff_eq_zero_of_not_mem_vars hb he'
  simp only [sub_mul, coeff_sub, sum_sub_distrib]
  have hb' : ∀ p q, coeff (Finsupp.single a p + Finsupp.single b q + e') (X b * u) =
      if q = 0 then 0 else coeff (Finsupp.single a p + Finsupp.single b (q - 1) + e') u :=
    fun p q => coeff_X_mul_key hab heb p q u
  have ha' : ∀ p q, coeff (Finsupp.single a p + Finsupp.single b q + e') (X a * u) =
      if p = 0 then 0 else coeff (Finsupp.single a (p - 1) + Finsupp.single b q + e') u := by
    intro p q
    have := coeff_X_mul_key hab.symm hea q p u
    rw [add_comm (Finsupp.single b q)] at this
    rw [this, add_comm (Finsupp.single b q)]
  simp only [hb', ha']
  rcases j with _ | n
  · simp
  · rw [Finset.Nat.sum_antidiagonal_succ', Finset.Nat.sum_antidiagonal_succ]
    simp

/-! ### The polarization `pol` -/

/-- The outer ring `ℂ[x][t_0, …, t_{k-1}]`. -/
abbrev OP (k : ℕ) : Type := MvPolynomial (Fin k) (XP k)

/-- `T_m ↦ Σ_i t_i x_i^m`. -/
def evT (k : ℕ) : TPoly →ₐ[ℂ] OP k :=
  aeval fun m : ℕ => ∑ i : Fin k, MvPolynomial.C ((X i : XP k) ^ m) * (X i : OP k)

/-- The exponent `t_B = ∏_{i ∈ B} t_i`. -/
def ind (B : Finset (Fin k)) : Fin k →₀ ℕ := ∑ i ∈ B, Finsupp.single i 1

/-- **The polarization** `pol_B(F) = [t_B] F(T_m ↦ Σ_i t_i x_i^m)`. -/
def pol (B : Finset (Fin k)) (F : TPoly) : XP k := coeff (ind B) (evT k F)

theorem ind_apply (B : Finset (Fin k)) (i : Fin k) : ind B i = if i ∈ B then 1 else 0 := by
  classical
  rw [ind, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [sum_ite_eq']

theorem mem_support_ind {B : Finset (Fin k)} {i : Fin k} : i ∈ (ind B).support ↔ i ∈ B := by
  rw [Finsupp.mem_support_iff, ind_apply]
  split_ifs with h <;> simp [h]

theorem ind_sub {B : Finset (Fin k)} {i : Fin k} (hi : i ∈ B) :
    ind B - Finsupp.single i 1 = ind (B.erase i) := by
  classical
  ext j
  simp only [Finsupp.coe_tsub, Pi.sub_apply, ind_apply, Finsupp.single_apply, mem_erase]
  by_cases hj : j = i
  · subst hj; simp [hi]
  · simp [hj, Ne.symm hj]

theorem ind_eq_zero_iff {B : Finset (Fin k)} : ind B = 0 ↔ B = ∅ := by
  constructor
  · intro h
    rw [eq_empty_iff_forall_notMem]
    intro i hi
    have := congrArg (fun f : Fin k →₀ ℕ => f i) h
    simp [ind_apply, hi] at this
  · rintro rfl; simp [ind]

theorem pol_add (B : Finset (Fin k)) (F G : TPoly) : pol B (F + G) = pol B F + pol B G := by
  rw [pol, map_add, coeff_add]; rfl

theorem pol_smul (B : Finset (Fin k)) (c : ℂ) (F : TPoly) : pol B (c • F) = c • pol B F := by
  rw [pol, map_smul, coeff_smul]; rfl

theorem pol_zero (B : Finset (Fin k)) : pol B 0 = 0 := by
  rw [pol, map_zero, coeff_zero]

theorem pol_sum {ι : Type*} (s : Finset ι) (B : Finset (Fin k)) (F : ι → TPoly) :
    pol B (∑ i ∈ s, F i) = ∑ i ∈ s, pol B (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pol_zero]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, pol_add, ih]

theorem pol_C (B : Finset (Fin k)) (c : ℂ) :
    pol B (MvPolynomial.C c) = if B = ∅ then (MvPolynomial.C c : XP k) else 0 := by
  classical
  rw [pol, evT, aeval_C, MvPolynomial.algebraMap_apply, coeff_C]
  by_cases hB : B = ∅
  · rw [if_pos (by rw [ind_eq_zero_iff.mpr hB]), if_pos hB]; rfl
  · rw [if_neg (fun h => hB (ind_eq_zero_iff.mp h.symm)), if_neg hB]

/-- **The recursion** `pol_B(T_m G) = Σ_{i ∈ B} x_i^m pol_{B - i}(G)`. -/
theorem pol_X_mul (B : Finset (Fin k)) (m : ℕ) (G : TPoly) :
    pol B (X m * G) = ∑ i ∈ B, (X i : XP k) ^ m * pol (B.erase i) G := by
  classical
  rw [pol, map_mul, evT, aeval_X, ← evT, sum_mul, coeff_sum]
  simp only [mul_assoc, coeff_C_mul, coeff_X_mul', mem_support_ind, mul_ite, mul_zero]
  rw [sum_ite_mem, univ_inter]
  exact sum_congr rfl fun i hi => by rw [ind_sub hi]; rfl

/-- `pol_B(G)` involves only the variables `x_i`, `i ∈ B`. -/
theorem pol_vars (G : TPoly) : ∀ (B : Finset (Fin k)) (l : Fin k), l ∉ B → l ∉ (pol B G).vars := by
  classical
  induction G using MvPolynomial.induction_on with
  | C c =>
    intro B l _
    rw [pol_C]
    split_ifs <;> simp
  | add p q hp hq =>
    intro B l hl hmem
    rw [pol_add] at hmem
    rcases mem_union.mp (vars_add_subset _ _ hmem) with h | h
    · exact hp B l hl h
    · exact hq B l hl h
  | mul_X p m hp =>
    intro B l hl hmem
    rw [mul_comm, pol_X_mul] at hmem
    obtain ⟨i, hi, hmi⟩ := mem_biUnion.mp (vars_sum_subset _ _ hmem)
    rcases mem_union.mp (vars_mul _ _ hmi) with h | h
    · have h' := vars_pow _ _ h
      rw [vars_X, mem_singleton] at h'
      exact hl (h' ▸ hi)
    · exact hp (B.erase i) l (fun h' => hl (mem_of_mem_erase h')) h

/-- Monomial induction by single variable increments. -/
theorem monomial_induction {P : (ℕ →₀ ℕ) → Prop} (h0 : P 0)
    (hs : ∀ s m, P s → P (s + Finsupp.single m 1)) : ∀ s, P s := by
  intro s
  induction s using Finsupp.induction with
  | zero => exact h0
  | single_add a b f _ _ ih =>
    have key : ∀ c : ℕ, P (Finsupp.single a c + f) := by
      intro c
      induction c with
      | zero => simpa using ih
      | succ c ihc =>
        have := hs _ a ihc
        rwa [add_right_comm, ← Finsupp.single_add] at this
    exact key b

theorem monomial_add_single (s : ℕ →₀ ℕ) (m : ℕ) :
    (monomial (s + Finsupp.single m 1) 1 : TPoly) = X m * monomial s 1 := by
  rw [X, monomial_mul, one_mul, add_comm]

/-! ### The expansion along one variable -/

/-- The expansion property of `G` for the derivative index set `S`. -/
def ExpProp (S : Finset ℕ) (G : TPoly) : Prop :=
  ∀ (B : Finset (Fin k)) (l : Fin k), l ∈ B →
    pol B G = ∑ M ∈ S, (X l : XP k) ^ M * pol (B.erase l) (pderiv M G)

theorem expProp_one (S : Finset ℕ) : ExpProp (k := k) S 1 := by
  intro B l hl
  have h1 : (1 : TPoly) = MvPolynomial.C 1 := rfl
  rw [h1, pol_C, if_neg (ne_empty_of_mem hl)]
  simp [pol_zero]

theorem expProp_add {S : Finset ℕ} {F G : TPoly} (hF : ExpProp (k := k) S F)
    (hG : ExpProp (k := k) S G) : ExpProp (k := k) S (F + G) := by
  intro B l hl
  rw [pol_add, hF B l hl, hG B l hl, ← sum_add_distrib]
  exact sum_congr rfl fun M _ => by rw [map_add, pol_add, mul_add]

theorem expProp_smul {S : Finset ℕ} {F : TPoly} (c : ℂ) (hF : ExpProp (k := k) S F) :
    ExpProp (k := k) S (c • F) := by
  intro B l hl
  rw [pol_smul, hF B l hl, smul_sum]
  exact sum_congr rfl fun M _ => by rw [(pderiv M).map_smul, pol_smul, mul_smul_comm]

theorem expProp_X_mul {S : Finset ℕ} {G : TPoly} {m : ℕ} (hm : m ∈ S)
    (hG : ExpProp (k := k) S G) : ExpProp (k := k) S (X m * G) := by
  classical
  intro B l hl
  rw [pol_X_mul, ← add_sum_erase B _ hl]
  have h1 : ∀ i ∈ B.erase l, (X i : XP k) ^ m * pol (B.erase i) G =
      ∑ M ∈ S, (X i : XP k) ^ m * ((X l : XP k) ^ M * pol ((B.erase i).erase l) (pderiv M G)) := by
    intro i hi
    rw [hG (B.erase i) l (mem_erase.mpr ⟨(ne_of_mem_erase hi).symm, hl⟩), mul_sum]
  rw [sum_congr rfl h1, sum_comm]
  have h2 : ∀ M ∈ S, (X l : XP k) ^ M * pol (B.erase l) (pderiv M (X m * G)) =
      (X l : XP k) ^ M *
          ∑ i ∈ B.erase l, (X i : XP k) ^ m * pol ((B.erase l).erase i) (pderiv M G) +
        if M = m then (X l : XP k) ^ M * pol (B.erase l) G else 0 := by
    intro M _
    rw [pderiv_mul, pderiv_X, add_comm, pol_add, mul_add, pol_X_mul]
    congr 1
    by_cases hMm : M = m
    · subst hMm; simp
    · rw [if_neg hMm, Pi.single_apply, if_neg (Ne.symm hMm), zero_mul, pol_zero, mul_zero]
  rw [sum_congr rfl h2, sum_add_distrib, sum_ite_eq' S m, if_pos hm, add_comm]
  congr 1
  refine sum_congr rfl fun M _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [erase_right_comm]; ring

theorem expProp_monomial (S : Finset ℕ) : ∀ s : ℕ →₀ ℕ, s.support ⊆ S →
    ExpProp (k := k) S (monomial s 1) := by
  refine monomial_induction (fun _ => by simpa using expProp_one S) fun s m ih hsub => ?_
  have hm : m ∈ S := hsub (Finsupp.mem_support_iff.mpr (by simp))
  have hs : s.support ⊆ S := fun i hi => hsub (Finsupp.mem_support_iff.mpr (by
    have := Finsupp.mem_support_iff.mp hi
    simp only [Finsupp.coe_add, Pi.add_apply]; omega))
  rw [monomial_add_single]
  exact expProp_X_mul hm (ih hs)

/-- **The expansion along `x_l`**: `pol_B(F) = Σ_{M ∈ S} x_l^M pol_{B - l}(∂F/∂T_M)` for `l ∈ B`
and `S ⊇ vars F`. -/
theorem pol_expand {S : Finset ℕ} {F : TPoly} (hS : F.vars ⊆ S) {B : Finset (Fin k)} {l : Fin k}
    (hl : l ∈ B) : pol B F = ∑ M ∈ S, (X l : XP k) ^ M * pol (B.erase l) (pderiv M F) := by
  classical
  have h : ExpProp (k := k) S F := by
    conv => arg 2; rw [as_sum F]
    have : ∀ t : Finset (ℕ →₀ ℕ), t ⊆ F.support →
        ExpProp (k := k) S (∑ v ∈ t, monomial v (coeff v F)) := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
        intro _ B l _
        simp [pol_zero]
      | insert a t ha ih =>
        intro hsub
        rw [sum_insert ha]
        refine expProp_add ?_ (ih (fun x hx => hsub (mem_insert_of_mem hx)))
        have hmon : (monomial a (coeff a F) : TPoly) = coeff a F • monomial a 1 := by
          rw [smul_monomial, smul_eq_mul, mul_one]
        rw [hmon]
        refine expProp_smul _ (expProp_monomial S a fun i hi => hS ?_)
        exact (mem_vars_iff_mem_support i).mpr ⟨a, hsub (mem_insert_self a t), hi⟩
    exact this F.support subset_rfl
  exact h B l hl

/-! ### Orthogonality to the jet ideal `J_2` -/

theorem jg_two (j : ℕ) : jg 2 j = ∑ x ∈ antidiagonal j, (X x.1 * X x.2 : TPoly) := by
  rw [jg, pow_two, PowerSeries.coeff_mul]
  simp [tSer, PowerSeries.coeff_mk]

theorem hsum_eq (a b : Fin k) (j : ℕ) :
    hsum a b j = ∑ x ∈ antidiagonal j, (X a : XP k) ^ x.1 * (X b : XP k) ^ x.2 := by
  rw [hsum]
  exact sum_congr rfl fun x _ => by rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]

theorem pol_jg_mul (B : Finset (Fin k)) (j : ℕ) (c : TPoly) :
    pol B (jg 2 j * c) =
      ∑ i ∈ B, ∑ i' ∈ B.erase i, hsum i i' j * pol ((B.erase i).erase i') c := by
  rw [jg_two, sum_mul, pol_sum]
  have h1 : ∀ x ∈ antidiagonal j, pol B (X x.1 * X x.2 * c) = ∑ i ∈ B, ∑ i' ∈ B.erase i,
      (X i : XP k) ^ x.1 * (X i' : XP k) ^ x.2 * pol ((B.erase i).erase i') c := by
    intro x _
    rw [mul_assoc, pol_X_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [pol_X_mul, mul_sum]
    exact sum_congr rfl fun i' _ => by ring
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun i' _ => ?_
  rw [hsum_eq, sum_mul]

/-- **Orthogonality to `J_2`**: `⟨R pol_B(G), Y⟩ = 0` for `G ∈ J_2`, `R` free of the `x_i`
(`i ∈ B`) and `Y` divisible by every `x_b - x_a`, `a < b` in `B`. -/
theorem dot_pol_jet {G : TPoly} (hG : G ∈ jetIdealT 2) (B : Finset (Fin k)) {R : XP k}
    (hR : ∀ i ∈ B, i ∉ R.vars) {Y : XP k}
    (hY : ∀ a ∈ B, ∀ b ∈ B, a < b → (X b - X a : XP k) ∣ Y) : dot (R * pol B G) Y = 0 := by
  classical
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hG
  rw [Finsupp.sum, pol_sum, mul_sum, dot_sum_left]
  refine sum_eq_zero fun j _ => ?_
  have hj : (PowerSeries.coeff j (tSer ^ 2) : TPoly) = jg 2 j := rfl
  rw [smul_eq_mul, hj, mul_comm (c j), pol_jg_mul, mul_sum, dot_sum_left]
  refine sum_eq_zero fun i hi => ?_
  rw [mul_sum, dot_sum_left]
  refine sum_eq_zero fun i' hi' => ?_
  have hii' : i' ≠ i := ne_of_mem_erase hi'
  have hi'B : i' ∈ B := mem_of_mem_erase hi'
  set P := R * pol ((B.erase i).erase i') (c j) with hP
  have hPi : i ∉ P.vars := fun h => by
    rcases mem_union.mp (vars_mul _ _ h) with h | h
    · exact hR i hi h
    · exact pol_vars _ _ i (fun h' => (ne_of_mem_erase (mem_of_mem_erase h')).symm rfl) h
  have hPi' : i' ∉ P.vars := fun h => by
    rcases mem_union.mp (vars_mul _ _ h) with h | h
    · exact hR i' hi'B h
    · exact pol_vars _ _ i' (fun h' => (ne_of_mem_erase h') rfl) h
  have hterm : R * (hsum i i' j * pol ((B.erase i).erase i') (c j)) = hsum i i' j * P := by
    rw [hP]; ring
  rw [hterm]
  rcases lt_or_gt_of_ne hii' with hlt | hlt
  · obtain ⟨u, hu⟩ := hY i' hi'B i hi hlt
    rw [hu, hsum_comm]
    exact dot_key (ne_of_lt hlt) j hPi' hPi u
  · obtain ⟨u, hu⟩ := hY i hi i' hi'B hlt
    rw [hu]
    exact dot_key (ne_of_lt hlt) j hPi hPi' u

/-- `⟨pol(F), x_l^N Y⟩ = 0` for `Y ∈ Q_l` when `∂F/∂T_M ∈ J_2` for all `M ≥ N`. -/
theorem dot_pol_pow_mul {N : ℕ} {F : TPoly} (hF : ∀ M, N ≤ M → pderiv M F ∈ jetIdealT 2)
    (l : Fin k) {Y : XP k} (hY : Y ∈ Qid k l) : dot (pol univ F) ((X l : XP k) ^ N * Y) = 0 := by
  classical
  rw [pol_expand (subset_refl _) (mem_univ l), dot_sum_left]
  refine sum_eq_zero fun M _ => ?_
  rw [X_pow_eq_monomial, X_pow_eq_monomial,
    dot_shift l (pol_vars _ _ l (fun h => (ne_of_mem_erase h) rfl)) Y]
  split_ifs with hNM
  · refine dot_pol_jet (hF M hNM) (univ.erase l) (fun i hi h => ?_) (fun a ha b hb hab => ?_)
    · rw [vars_monomial one_ne_zero] at h
      have h' := h
      have : i = l := by
        by_contra hne
        have := Finsupp.mem_support_iff.mp h'
        rw [Finsupp.single_apply, if_neg (Ne.symm hne)] at this
        exact this rfl
      exact (ne_of_mem_erase hi) this
    · exact (mem_Qid.mp hY) a b hab (ne_of_mem_erase ha) (ne_of_mem_erase hb)
  · rfl

/-- **`⟨pol(F), W⟩ = 0`** when `∂F/∂T_M ∈ J_2` for all `M ≥ N`. -/
theorem dot_pol_W {N : ℕ} {F : TPoly} (hF : ∀ M, N ≤ M → pderiv M F ∈ jetIdealT 2) {w : XP k}
    (hw : w ∈ Wid k N) : dot (pol univ F) w = 0 := by
  refine Submodule.iSup_induction (p := fun l : Fin k =>
    Ideal.span {(X l ^ N : XP k)} * Qid k l) (motive := fun w => dot (pol univ F) w = 0) hw
    (fun l x hx => ?_) (dot_zero_right _)
    (fun x y hx hy => by simp only at hx hy ⊢; rw [dot_add_right, hx, hy, add_zero])
  refine Submodule.mul_induction_on hx (fun a ha y hy => ?_)
    (fun x y hx hy => by simp only at hx hy ⊢; rw [dot_add_right, hx, hy, add_zero])
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  rw [show c * (X l : XP k) ^ N * y = (X l : XP k) ^ N * (c * y) by ring]
  exact dot_pol_pow_mul hF l (Ideal.mul_mem_left _ _ hy)

/-! ### `pol` on monomials -/

/-- The multiset of exponents `{e_i : i ∈ B}`. -/
def toMS (B : Finset (Fin k)) (e : Fin k →₀ ℕ) : ℕ →₀ ℕ := ∑ i ∈ B, Finsupp.single (e i) 1

theorem pol_one (B : Finset (Fin k)) : pol B (1 : TPoly) = if B = ∅ then (1 : XP k) else 0 := by
  have h1 : (1 : TPoly) = MvPolynomial.C 1 := rfl
  rw [h1, pol_C]; rfl

theorem mem_support_X_pow_mul {i : Fin k} {m : ℕ} {P : XP k} {e : Fin k →₀ ℕ}
    (he : e ∈ ((X i : XP k) ^ m * P).support) :
    Finsupp.single i m ≤ e ∧ e - Finsupp.single i m ∈ P.support := by
  classical
  rw [X_pow_eq_monomial, mem_support_iff, coeff_monomial_mul'] at he
  split_ifs at he with hle
  · exact ⟨hle, mem_support_iff.mpr (by rwa [one_mul] at he)⟩
  · exact absurd rfl he

/-- The support of `pol_B(T^s)` consists of arrangements of `s`. -/
theorem pol_monomial_support : ∀ (s : ℕ →₀ ℕ) (B : Finset (Fin k)) (e : Fin k →₀ ℕ),
    e ∈ (pol B (monomial s 1)).support → toMS B e = s := by
  classical
  refine monomial_induction ?_ ?_
  · intro B e he
    have h0 : (monomial 0 1 : TPoly) = 1 := rfl
    rw [h0, pol_one] at he
    split_ifs at he with hB
    · subst hB; simp [toMS]
    · simp at he
  · intro s m ih B e he
    rw [monomial_add_single, pol_X_mul] at he
    obtain ⟨i, hi, hei⟩ := mem_biUnion.mp (support_sum he)
    obtain ⟨hle, he'⟩ := mem_support_X_pow_mul hei
    have hIH := ih (B.erase i) _ he'
    have hzero := coeff_eq_zero_of_not_mem_vars
      (pol_vars _ (B.erase i) i (fun h => (ne_of_mem_erase h) rfl)) he'
    have hei' : e i = m := by
      have h1 := hle i
      simp only [Finsupp.single_eq_same, Finsupp.coe_tsub, Pi.sub_apply] at h1 hzero
      omega
    rw [toMS, ← add_sum_erase B _ hi, hei', add_comm]
    congr 1
    rw [← hIH, toMS]
    refine sum_congr rfl fun j hj => ?_
    have hji : j ≠ i := ne_of_mem_erase hj
    simp [Ne.symm hji]

/-- The coefficient sum of `pol_B(T^s)` is `|B|!` when `deg s = |B|`. -/
theorem pol_monomial_eval : ∀ (s : ℕ →₀ ℕ) (B : Finset (Fin k)),
    eval (fun _ => (1 : ℂ)) (pol B (monomial s 1)) =
      if s.degree = #B then ((#B).factorial : ℂ) else 0 := by
  classical
  refine monomial_induction ?_ ?_
  · intro B
    have h0 : (monomial 0 1 : TPoly) = 1 := rfl
    rw [h0, pol_one, map_zero]
    by_cases hB : B = ∅
    · subst hB; simp
    · rw [if_neg hB, if_neg (fun h => hB (card_eq_zero.mp h.symm)), map_zero]
  · intro s m ih B
    rw [monomial_add_single, pol_X_mul, map_sum]
    have h1 : ∀ i ∈ B, eval (fun _ => (1 : ℂ)) ((X i : XP k) ^ m * pol (B.erase i) (monomial s 1)) =
        if s.degree = #B - 1 then (((#B - 1).factorial : ℕ) : ℂ) else 0 := by
      intro i hi
      rw [map_mul, map_pow, eval_X, one_pow, one_mul, ih, card_erase_of_mem hi]
    rw [sum_congr rfl h1, sum_const, nsmul_eq_mul, map_add, Finsupp.degree_single]
    generalize #B = c
    rcases c with _ | c
    · simp
    · simp only [Nat.add_sub_cancel, Nat.add_right_cancel_iff, Nat.factorial_succ]
      split_ifs <;> push_cast <;> ring

end

end VOA.TwoSeries.JetPoincareDual
