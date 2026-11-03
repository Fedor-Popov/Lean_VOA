/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Core.GradedUnitarity

/-!
# Two pieces of `sl₂` linear algebra, modulo an invariant subspace

Abstract input for the unitarity of `L_1(sl₂)` (`LevelOneUnitaryPositivity`).  Everything here is
stated for endomorphisms of an arbitrary complex vector space and a subspace `I` they preserve;
"`v ∈ I`" plays the role of "`v = 0` in the quotient".

* `mem_of_F_pow_mem` — **the reflection lemma**.  If `E, F, H` satisfy the `sl₂` relations
  `[E,F] = H`, `[H,E] = 2E`, `[H,F] = -2F`, preserve `I`, `E` is nilpotent on `v` modulo `I`, and
  `H v = λ v` with `λ ∈ ℕ`, then `F^λ v ∈ I` forces `v ∈ I`.  (Equivalently, `F^λ` is injective
  on the `λ`-weight space of the quotient: the Weyl reflection of an integrable `sl₂`-module.)
  Proof: induction on the nilpotency order of `E`, using
  `E F^{m+1} v = F^{m+1} E v + (m+1)(λ-m) F^m v` (`E_F_pow_succ`).
* `exists_pow_mem_of_comm` — **propagation of local nilpotency**: if `A X = X A + Y`, `A` and
  `X` preserve `I`, and `Y` preserves the set of vectors on which `A` is nilpotent modulo `I`, then
  so does `X`.
-/

namespace VOA.LevelOneUnitary

open Module (End)

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

section Basic

variable (I : Submodule ℂ V)

theorem pow_apply_mem {A : End ℂ V} (hA : ∀ v ∈ I, A v ∈ I) (n : ℕ) {v : V} (hv : v ∈ I) :
    (A ^ n) v ∈ I := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hA _ ih

end Basic

/-! ### The reflection lemma -/

section Sl2

variable (E F H : End ℂ V) (I : Submodule ℂ V)

theorem H_F_pow (hHF : ∀ v, H (F v) = F (H v) - (2 : ℂ) • F v) {lam : ℂ} {v : V}
    (hv : H v = lam • v) (m : ℕ) : H ((F ^ m) v) = (lam - 2 * m) • (F ^ m) v := by
  induction m with
  | zero => simpa using hv
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, hHF, ih, map_smul]
      push_cast
      module

theorem E_F_pow_succ (hEF : ∀ v, E (F v) = F (E v) + H v)
    (hHF : ∀ v, H (F v) = F (H v) - (2 : ℂ) • F v) {lam : ℂ} {v : V}
    (hv : H v = lam • v) (m : ℕ) :
    E ((F ^ (m + 1)) v) = (F ^ (m + 1)) (E v) + (((m : ℂ) + 1) * (lam - m)) • (F ^ m) v := by
  induction m with
  | zero =>
      simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero, sub_zero,
        one_mul]
      rw [hEF, hv]
  | succ m ih =>
      have hH := H_F_pow F H hHF hv (m + 1)
      rw [pow_succ' F (m + 1), Module.End.mul_apply, hEF, ih, hH, map_add, map_smul,
        ← Module.End.mul_apply F (F ^ (m + 1)), ← pow_succ',
        ← Module.End.mul_apply F (F ^ m), ← pow_succ']
      push_cast
      module

variable {E F H I}

theorem mem_of_F_pow_mem (hEF : ∀ v, E (F v) = F (E v) + H v)
    (hHE : ∀ v, H (E v) = E (H v) + (2 : ℂ) • E v)
    (hHF : ∀ v, H (F v) = F (H v) - (2 : ℂ) • F v)
    (hEI : ∀ v ∈ I, E v ∈ I) (hFI : ∀ v ∈ I, F v ∈ I) :
    ∀ (N lam : ℕ) (v : V), H v = (lam : ℂ) • v → (E ^ N) v ∈ I → (F ^ lam) v ∈ I → v ∈ I := by
  intro N
  induction N with
  | zero =>
      intro lam v _ hN _
      simpa using hN
  | succ N ih =>
      intro lam v hv hN hF
      -- `E v` is a weight vector of weight `λ + 2`
      have hEv : H (E v) = ((lam + 2 : ℕ) : ℂ) • E v := by
        rw [hHE, hv, map_smul]; push_cast; module
      -- `F^{λ+2} (E v) ∈ I`
      have hF1 : (F ^ (lam + 1)) v ∈ I := by
        rw [pow_succ', Module.End.mul_apply]; exact hFI _ hF
      have hF2 : (F ^ (lam + 2)) v ∈ I := by
        rw [pow_succ', Module.End.mul_apply]; exact hFI _ hF1
      have hFE : (F ^ (lam + 2)) (E v) ∈ I := by
        have h := E_F_pow_succ E F H hEF hHF hv (lam + 1)
        have h' : (F ^ (lam + 2)) (E v) = E ((F ^ (lam + 2)) v) -
            ((((lam + 1 : ℕ) : ℂ) + 1) * ((lam : ℂ) - ((lam + 1 : ℕ) : ℂ))) •
              (F ^ (lam + 1)) v := by
          rw [h]; abel
        rw [h']
        exact I.sub_mem (hEI _ hF2) (I.smul_mem _ hF1)
      have hEN : (E ^ N) (E v) ∈ I := by
        rw [← Module.End.mul_apply, ← pow_succ]; exact hN
      have hEvI : E v ∈ I := ih (lam + 2) (E v) hEv hEN hFE
      -- `v` is primitive modulo `I`; descend the `F`-string
      have hdesc : ∀ i : ℕ, i ≤ lam → (F ^ (lam - i)) v ∈ I := by
        intro i
        induction i with
        | zero => intro _; simpa using hF
        | succ i ihi =>
            intro hi
            have hprev := ihi (by omega)
            obtain ⟨j, hj⟩ : ∃ j, lam - i = j + 1 := ⟨lam - i - 1, by omega⟩
            have hj' : lam - (i + 1) = j := by omega
            rw [hj']
            rw [hj] at hprev
            have h := E_F_pow_succ E F H hEF hHF hv j
            have hmem : (((j : ℂ) + 1) * ((lam : ℂ) - j)) • (F ^ j) v ∈ I := by
              have h' : (((j : ℂ) + 1) * ((lam : ℂ) - j)) • (F ^ j) v =
                  E ((F ^ (j + 1)) v) - (F ^ (j + 1)) (E v) := by
                rw [h]; abel
              rw [h']
              exact I.sub_mem (hEI _ hprev) (pow_apply_mem I hFI _ hEvI)
            have hne : ((j : ℂ) + 1) * ((lam : ℂ) - j) ≠ 0 := by
              apply mul_ne_zero
              · exact_mod_cast Nat.succ_ne_zero j
              · rw [sub_ne_zero]
                intro h
                have : lam = j := by exact_mod_cast h
                omega
            exact (I.smul_mem_iff hne).mp hmem
      simpa using hdesc lam le_rfl

end Sl2

/-! ### Propagation of local nilpotency -/

section Nil

variable (A : End ℂ V) (I : Submodule ℂ V)

/-- The vectors on which `A` is nilpotent modulo `I`. -/
def NilMod (y : V) : Prop := ∃ N : ℕ, (A ^ N) y ∈ I

variable {A I}

theorem nilMod_of_mem {y : V} (hy : y ∈ I) : NilMod A I y := ⟨0, by simpa using hy⟩

theorem nilMod_add (hA : ∀ v ∈ I, A v ∈ I) {x y : V} (hx : NilMod A I x) (hy : NilMod A I y) :
    NilMod A I (x + y) := by
  obtain ⟨N, hN⟩ := hx
  obtain ⟨M, hM⟩ := hy
  refine ⟨N + M, ?_⟩
  rw [map_add]
  refine I.add_mem ?_ ?_
  · rw [add_comm, pow_add, Module.End.mul_apply]; exact pow_apply_mem I hA _ hN
  · rw [pow_add, Module.End.mul_apply]; exact pow_apply_mem I hA _ hM

theorem nilMod_smul (c : ℂ) {x : V} (hx : NilMod A I x) : NilMod A I (c • x) := by
  obtain ⟨N, hN⟩ := hx
  exact ⟨N, by rw [map_smul]; exact I.smul_mem _ hN⟩

theorem nilMod_zero : NilMod A I 0 := ⟨0, by simp⟩

theorem nilMod_of_apply {y : V} (h : NilMod A I (A y)) : NilMod A I y := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N + 1, by rw [pow_succ, Module.End.mul_apply]; exact hN⟩

/-- **Propagation of local nilpotency** through a commutation relation `A X = X A + Y`. -/
theorem nilMod_of_comm {X Y : End ℂ V} (hA : ∀ v ∈ I, A v ∈ I) (hX : ∀ v ∈ I, X v ∈ I)
    (hcomm : ∀ v, A (X v) = X (A v) + Y v) (hY : ∀ y, NilMod A I y → NilMod A I (Y y)) :
    ∀ y, NilMod A I y → NilMod A I (X y) := by
  intro y ⟨M, hM⟩
  induction M generalizing y with
  | zero => exact nilMod_of_mem (hX _ (by simpa using hM))
  | succ M ih =>
      have h1 : NilMod A I (X (A y)) := by
        apply ih
        rw [← Module.End.mul_apply, ← pow_succ]; exact hM
      have h2 : NilMod A I (Y y) := hY y ⟨M + 1, hM⟩
      apply nilMod_of_apply
      rw [hcomm]
      exact nilMod_add hA h1 h2

end Nil

end VOA.LevelOneUnitary
