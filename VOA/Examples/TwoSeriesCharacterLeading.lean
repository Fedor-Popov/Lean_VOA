/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LeeYangCharacterSpanning
import VOA.Examples.VirasoroBSARecursion

/-!
# The leading term of the vacuum singular vector of `M(2, 2n+3)`, and its jet relations

The repository already proves (`VirModule.bsaSource_mem_maxIdeal`) that the vacuum
Benoit–Saint-Aubin source `bsaSource (bsaCharge N) N N` lies in the maximal ideal of the universal
vacuum module `V(c,0)` at `c = bsaCharge N = c_{2,N+1}`; nonvanishing was left open there.  Here
its **leading term in the PBW-length filtration** is computed, for every `N`:

* `bsaSource_lead` — for `N = 2n+2`,
  `bsaSource c N N - bsaLead N n • L_{-2}^{n+1}|0⟩ ∈ virFil c n N`, with the explicit
  coefficient `bsaLead N n = Π_{i<n} (-t)/((2i+2)(N-2i-2))`, `t = (N+1)/2`;
* `bsaLead_ne_zero` — this coefficient is nonzero.  In particular the singular vector is
  nonzero and its symbol is a nonzero multiple of `x^{n+1}`, `x = σ(L_{-2})`.

From one such vector the **jet relations** follow (`hasJetRelations_of_singular`): with
`jetSum c m k = Σ_{e₁+⋯+e_m = k} L_{-e₁-2} ⋯ L_{-e_m-2}|0⟩` (the coefficient of `z^k` in
`x(z)^m`), for every `k` there is `σ_k ∈ J_max` with `σ_k - α • jetSum c (n+1) k` of length
`≤ n`.  The key exact identity is `Lop_neg_one_jetSum : L_{-1} T_k = (k+1) T_{k+1}`.

* `twoSeries_hasJetRelations` — the jet relations hold at `c = bsaCharge (2n+2)` for every
  `n ≥ 1`.

Everything here is proved; no hypothesis is introduced.
-/

namespace VOA.TwoSeriesCharacter

open VOA.VirModule VOA.VirGoodFil VOA.VirSimple VOA.LeeYangCharacter
open scoped BigOperators

noncomputable section

variable (c : ℂ)

/-! ## §1  `L_{-1}` and creation words preserve / raise the length filtration -/

/-- `L_{-1}` applied to any creation word stays in the step of the same length. -/
theorem Lop_neg_one_negWordVir_mem (w : List ℕ) :
    Lop c (-1) (negWordVir c w) ∈ virFil c w.length ((energyVir w + 1 : ℕ) : ℤ) := by
  induction w with
  | nil =>
      rw [negWordVir_nil, Lop_vacuum c (by norm_num)]
      exact Submodule.zero_mem _
  | cons a w ih =>
      rw [negWordVir_cons, Lop_neg_one_comm]
      refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
      · have h := Lop_mem_virFil_succ c a ih
        rw [show energyVir w + 1 + a + 2 = energyVir (a :: w) + 1 by
          rw [energyVir_cons]; omega] at h
        simpa using h
      · have h := negWordVir_mem_virFil c (w := (a + 1) :: w) (ℓ := (a :: w).length)
          (N := energyVir (a :: w) + 1) (by simp) (by simp only [energyVir_cons]; omega)
        rwa [negWordVir_cons] at h

/-- `L_{-1}` preserves every length step (raising the energy by one). -/
theorem Lop_neg_one_mem_virFil {ℓ N : ℕ} {v : VirUniv c} (hv : v ∈ virFil c ℓ (N : ℤ)) :
    Lop c (-1) v ∈ virFil c ℓ ((N + 1 : ℕ) : ℤ) := by
  induction hv using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨u, -, hen, hl, rfl⟩ := hy
      have hen' : energyVir u = N := by exact_mod_cast hen
      have := Lop_neg_one_negWordVir_mem c u
      rw [hen'] at this
      exact virFil_mono c _ hl this
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ r ha

/-- A creation word `L_r` raises the length by at most `|r|`. -/
theorem applyWord_mem_virFil (r : List ℕ) {ℓ N : ℕ} {v : VirUniv c}
    (hv : v ∈ virFil c ℓ (N : ℤ)) :
    applyWord c r v ∈ virFil c (ℓ + r.length) ((N + energyVir r : ℕ) : ℤ) := by
  induction r with
  | nil => simpa [applyWord] using hv
  | cons a r ih =>
      have h := Lop_mem_virFil_succ c a ih
      change Lop c (-(a : ℤ) - 2) (applyWord c r v) ∈ _
      rw [show ℓ + (a :: r).length = ℓ + r.length + 1 by simp; omega,
        show N + energyVir (a :: r) = N + energyVir r + a + 2 by rw [energyVir_cons]; omega]
      exact h

/-! ## §2  The leading term of the vacuum BSA states -/

/-- The leading coefficient of the even BSA states. -/
def bsaLead (N : ℕ) : ℕ → ℂ
  | 0 => 1
  | m + 1 => (-bsaParameter N / (((2 * m + 2 : ℕ) : ℂ) * ((N : ℂ) - ((2 * m + 2 : ℕ) : ℂ)))) *
      bsaLead N m

theorem bsaLead_ne_zero (N : ℕ) : ∀ m, 2 * m < N → bsaLead N m ≠ 0
  | 0, _ => one_ne_zero
  | m + 1, h => by
      rw [bsaLead]
      refine mul_ne_zero (div_ne_zero (neg_ne_zero.mpr ?_) (mul_ne_zero ?_ ?_))
        (bsaLead_ne_zero N m (by omega))
      · unfold bsaParameter
        exact div_ne_zero (by exact_mod_cast Nat.succ_ne_zero N) two_ne_zero
      · exact_mod_cast (by omega : 2 * m + 2 ≠ 0)
      · rw [sub_ne_zero]
        exact_mod_cast (by omega : N ≠ 2 * m + 2)

theorem negWordVir_replicate_succ (m : ℕ) :
    negWordVir c (List.replicate (m + 1) 0) = Lop c (-((0 : ℕ) : ℤ) - 2)
      (negWordVir c (List.replicate m 0)) := by
  rw [List.replicate_succ, negWordVir_cons]

/-- The induction statement for the states: `state_r` has length `≤ r/2`, and at even levels
`2m+2` its leading part is `bsaLead (m+1) • L_{-2}^{m+1}|0⟩`. -/
def StateLead (N r : ℕ) : Prop :=
  bsaState c N r ∈ virFil c (r / 2) (r : ℤ) ∧
    ∀ m, r = 2 * m + 2 →
      bsaState c N r - bsaLead N (m + 1) • negWordVir c (List.replicate (m + 1) 0) ∈
        virFil c m (r : ℤ)

theorem bsaSource_eq_range (N r : ℕ) :
    bsaSource c N r = ∑ j ∈ Finset.range r, Lop c ((j : ℤ) - (r : ℤ)) (bsaState c N j) := by
  rw [bsaSource, Fin.sum_univ_eq_sum_range (fun j => Lop c ((j : ℤ) - (r : ℤ)) (bsaState c N j))]

/-- One term `L_{j-r} state_j` with `j + 2 ≤ r`. -/
theorem term_mem_low (N r j : ℕ) (hj : j + 2 ≤ r) {ℓ : ℕ}
    (hs : bsaState c N j ∈ virFil c ℓ (j : ℤ)) :
    Lop c ((j : ℤ) - (r : ℤ)) (bsaState c N j) ∈ virFil c (ℓ + 1) (r : ℤ) := by
  have h := Lop_mem_virFil_succ c (r - j - 2) hs
  rw [show j + (r - j - 2) + 2 = r by omega] at h
  rwa [show ((j : ℤ) - (r : ℤ)) = -((r - j - 2 : ℕ) : ℤ) - 2 by omega]

/-- The term `L_{-1} state_{r-1}`. -/
theorem term_mem_top (N r : ℕ) {ℓ : ℕ}
    (hs : bsaState c N r ∈ virFil c ℓ (r : ℤ)) :
    Lop c ((r : ℤ) - ((r + 1 : ℕ) : ℤ)) (bsaState c N r) ∈ virFil c ℓ ((r + 1 : ℕ) : ℤ) := by
  rw [show ((r : ℤ) - ((r + 1 : ℕ) : ℤ)) = -1 by push_cast; ring]
  exact Lop_neg_one_mem_virFil c hs

/-- The source at level `r`, from the state statements below `r`. -/
theorem bsaSource_lead_aux (N r : ℕ) (ih : ∀ j < r, StateLead c N j) :
    bsaSource c N r ∈ virFil c (r / 2) (r : ℤ) ∧
      ∀ m, r = 2 * m + 2 →
        bsaSource c N r - bsaLead N m • negWordVir c (List.replicate (m + 1) 0) ∈
          virFil c m (r : ℤ) := by
  constructor
  · rw [bsaSource_eq_range]
    refine Submodule.sum_mem _ fun j hj => ?_
    rw [Finset.mem_range] at hj
    rcases (by omega : j + 2 ≤ r ∨ j + 1 = r) with h2 | h1
    · exact virFil_mono c _ (by omega) (term_mem_low c N r j h2 (ih j hj).1)
    · subst h1
      exact virFil_mono c _ (by omega) (term_mem_top c N j (ih j hj).1)
  · intro m hm
    subst hm
    rw [bsaSource_eq_range, Finset.sum_range_succ, Finset.sum_range_succ]
    have hlow : ∑ j ∈ Finset.range (2 * m), Lop c ((j : ℤ) - ((2 * m + 2 : ℕ) : ℤ))
        (bsaState c N j) ∈ virFil c m ((2 * m + 2 : ℕ) : ℤ) := by
      refine Submodule.sum_mem _ fun j hj => ?_
      rw [Finset.mem_range] at hj
      exact virFil_mono c _ (by omega) (term_mem_low c N _ j (by omega) (ih j (by omega)).1)
    have htop : Lop c (((2 * m + 1 : ℕ) : ℤ) - ((2 * m + 2 : ℕ) : ℤ))
        (bsaState c N (2 * m + 1)) ∈ virFil c m ((2 * m + 2 : ℕ) : ℤ) := by
      have := term_mem_top c N (2 * m + 1) (ih (2 * m + 1) (by omega)).1
      exact virFil_mono c _ (by omega) this
    have hmid : Lop c (((2 * m : ℕ) : ℤ) - ((2 * m + 2 : ℕ) : ℤ)) (bsaState c N (2 * m)) -
        bsaLead N m • negWordVir c (List.replicate (m + 1) 0) ∈
          virFil c m ((2 * m + 2 : ℕ) : ℤ) := by
      have hmode : (((2 * m : ℕ) : ℤ) - ((2 * m + 2 : ℕ) : ℤ)) = -((0 : ℕ) : ℤ) - 2 := by
        push_cast; ring
      rw [hmode, negWordVir_replicate_succ, ← map_smul, ← map_sub]
      rcases m with _ | m'
      · simp [bsaLead, bsaState_zero, List.replicate]
      · have h := (ih (2 * m' + 2) (by omega)).2 m' rfl
        have h2 := Lop_mem_virFil_succ c 0 h
        rw [show 2 * m' + 2 + 0 + 2 = 2 * (m' + 1) + 2 by ring] at h2
        rw [show 2 * (m' + 1) = 2 * m' + 2 by ring]
        exact h2
    have hsum : ∑ j ∈ Finset.range (2 * m), Lop c ((j : ℤ) - ((2 * m + 2 : ℕ) : ℤ))
          (bsaState c N j) + Lop c (((2 * m : ℕ) : ℤ) - ((2 * m + 2 : ℕ) : ℤ))
          (bsaState c N (2 * m)) + Lop c (((2 * m + 1 : ℕ) : ℤ) - ((2 * m + 2 : ℕ) : ℤ))
          (bsaState c N (2 * m + 1)) - bsaLead N m • negWordVir c (List.replicate (m + 1) 0) =
        (∑ j ∈ Finset.range (2 * m), Lop c ((j : ℤ) - ((2 * m + 2 : ℕ) : ℤ)) (bsaState c N j) +
          (Lop c (((2 * m : ℕ) : ℤ) - ((2 * m + 2 : ℕ) : ℤ)) (bsaState c N (2 * m)) -
            bsaLead N m • negWordVir c (List.replicate (m + 1) 0))) +
          Lop c (((2 * m + 1 : ℕ) : ℤ) - ((2 * m + 2 : ℕ) : ℤ)) (bsaState c N (2 * m + 1)) := by
      abel
    rw [hsum]
    exact Submodule.add_mem _ (Submodule.add_mem _ hlow hmid) htop

/-- The leading term of every BSA state. -/
theorem bsaState_lead (N : ℕ) : ∀ r, StateLead c N r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · subst h0
    refine ⟨?_, fun m hm => by omega⟩
    rw [bsaState_zero]
    have := negWordVir_mem_virFil c (w := []) (ℓ := 0) (N := 0) le_rfl rfl
    simpa using this
  · obtain ⟨hA, hB⟩ := bsaSource_lead_aux c N r ih
    rw [StateLead, bsaState_eq_source c N r hpos]
    refine ⟨Submodule.smul_mem _ _ hA, fun m hm => ?_⟩
    have h := Submodule.smul_mem _ (-bsaParameter N / ((r : ℂ) * ((N : ℂ) - (r : ℂ)))) (hB m hm)
    subst hm
    rw [smul_sub, smul_smul] at h
    convert h using 3

/-- **The leading term of the vacuum singular vector.** For `N = 2n+2`, the terminal BSA
source is `bsaLead N n • L_{-2}^{n+1}|0⟩` modulo words of length `≤ n`. -/
theorem bsaSource_lead (n : ℕ) :
    bsaSource c (2 * n + 2) (2 * n + 2) -
        bsaLead (2 * n + 2) n • negWordVir c (List.replicate (n + 1) 0) ∈
      virFil c n ((2 * n + 2 : ℕ) : ℤ) :=
  (bsaSource_lead_aux c (2 * n + 2) (2 * n + 2) fun j _ => bsaState_lead c _ j).2 n rfl

/-! ## §3  Jet sums and the exact `L_{-1}` identity -/

/-- `jetSum c m k = Σ_{e₁+⋯+e_m=k} L_{-e₁-2} ⋯ L_{-e_m-2}|0⟩`, defined recursively. -/
def jetSum : ℕ → ℕ → VirUniv c
  | 0, k => if k = 0 then vacVec c else 0
  | m + 1, k => ∑ p ∈ Finset.antidiagonal k, Lop c (-(p.1 : ℤ) - 2) (jetSum m p.2)

theorem jetSum_succ (m k : ℕ) :
    jetSum c (m + 1) k = ∑ p ∈ Finset.antidiagonal k, Lop c (-(p.1 : ℤ) - 2) (jetSum c m p.2) :=
  rfl

theorem jetSum_zero_right : ∀ m, jetSum c m 0 = negWordVir c (List.replicate m 0)
  | 0 => by simp [jetSum]
  | m + 1 => by
      rw [jetSum_succ, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, jetSum_zero_right m,
        List.replicate_succ, negWordVir_cons]

/-- **`L_{-1} T_k = (k+1) T_{k+1}`**, exactly. -/
theorem Lop_neg_one_jetSum : ∀ (m k : ℕ),
    Lop c (-1) (jetSum c m k) = ((k : ℂ) + 1) • jetSum c m (k + 1)
  | 0, k => by
      simp only [jetSum]
      by_cases hk : k = 0
      · subst hk; simp [Lop_vacuum c (by norm_num : (-1 : ℤ) ≤ -1)]
      · simp [hk]
  | m + 1, k => by
      rw [jetSum_succ, jetSum_succ, map_sum]
      simp only [Lop_neg_one_comm, Lop_neg_one_jetSum m, map_smul]
      rw [Finset.sum_add_distrib]
      have hk : ((k : ℂ) + 1) • ∑ p ∈ Finset.antidiagonal (k + 1),
            Lop c (-(p.1 : ℤ) - 2) (jetSum c m p.2) =
          ∑ p ∈ Finset.antidiagonal (k + 1),
            ((p.1 : ℂ) • Lop c (-(p.1 : ℤ) - 2) (jetSum c m p.2)) +
          ∑ p ∈ Finset.antidiagonal (k + 1), ((p.2 : ℂ) • Lop c (-(p.1 : ℤ) - 2) (jetSum c m p.2)) := by
        rw [← Finset.sum_add_distrib, Finset.smul_sum]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.mem_antidiagonal] at hp
        rw [← add_smul]
        congr 1
        rw [show (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by push_cast; ring, ← hp]
        push_cast; ring
      rw [hk, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ']
      simp only [Nat.cast_zero, zero_smul, zero_add, Nat.cast_add, Nat.cast_one]
      rw [add_comm]

/-! ## §4  Jet relations from one singular vector -/

/-- **Jet relations of order `n+1`**: a nonzero `α` and, for every `k`, a vector of the maximal
ideal whose length-`(n+1)` part is `α • jetSum c (n+1) k`. -/
def HasJetRelations (c : ℂ) (n : ℕ) : Prop :=
  ∃ α : ℂ, α ≠ 0 ∧ ∀ k : ℕ, ∃ σ ∈ maxIdealVir c,
    σ - α • jetSum c (n + 1) k ∈ virFil c n ((2 * n + 2 + k : ℕ) : ℤ)

/-- The divided powers `L_{-1}^k s / k!`. -/
def jetVec (s : VirUniv c) : ℕ → VirUniv c
  | 0 => s
  | k + 1 => ((k : ℂ) + 1)⁻¹ • Lop c (-1) (jetVec s k)

/-- A singular vector with leading term `α L_{-2}^{n+1}|0⟩`, `α ≠ 0`, gives all jet
relations. -/
theorem hasJetRelations_of_singular (n : ℕ) (s : VirUniv c) (hs : s ∈ maxIdealVir c) (α : ℂ)
    (hα : α ≠ 0)
    (hlead : s - α • negWordVir c (List.replicate (n + 1) 0) ∈ virFil c n ((2 * n + 2 : ℕ) : ℤ)) :
    HasJetRelations c n := by
  refine ⟨α, hα, fun k => ⟨jetVec c s k, ?_, ?_⟩⟩
  · induction k with
    | zero => exact hs
    | succ k ih => exact Submodule.smul_mem _ _ (Lop_mem_maxIdealVir c _ ih)
  · induction k with
    | zero => rw [jetSum_zero_right]; simpa using hlead
    | succ k ih =>
        have h := Lop_neg_one_mem_virFil c ih
        have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
        have h2 := Submodule.smul_mem _ ((k : ℂ) + 1)⁻¹ h
        rw [map_sub, map_smul, Lop_neg_one_jetSum, smul_sub, smul_smul, smul_smul,
          show ((k : ℂ) + 1)⁻¹ * α * ((k : ℂ) + 1) = α by field_simp] at h2
        rw [show 2 * n + 2 + (k + 1) = 2 * n + 2 + k + 1 by ring]
        exact h2

/-- **The jet relations of `M(2, 2n+3)`**, for every `n ≥ 1`, at the charge
`bsaCharge (2n+2) = c_{2,2n+3}`. -/
theorem twoSeries_hasJetRelations (n : ℕ) (hn : 1 ≤ n) :
    HasJetRelations (bsaCharge (2 * n + 2)) n :=
  hasJetRelations_of_singular _ n _ (bsaSource_mem_maxIdeal (2 * n + 2) (by omega))
    (bsaLead (2 * n + 2) n) (bsaLead_ne_zero _ n (by omega)) (bsaSource_lead _ n)

end

end VOA.TwoSeriesCharacter
