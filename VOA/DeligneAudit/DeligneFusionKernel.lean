/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneFusionRel

/-!
# Ravinder's kernel vector: the elementary relations

For a module with `MabRel ρ w a b` (`k = a + b`, `a ≥ 1`) and `v = (f_θ ⊗ t^{2a+b-1}) w`:
* `kernel_raising`: `(e ⊗ t^r) v = 0`;
* `kernel_cartan_pos`, `kernel_cartan_zero`: `(h ⊗ t^r) v = 0` (`r ≥ 1`), `(h ⊗ 1) v = (k-1) v`;
* `kernel_lowering_f1`, `kernel_lowering_f2`: `f_i^{k} v = 0` (sl₂ algebra: `u = f_i^k v` is killed by
  `e_i` and `f_i` and has `h_i`-weight `-(k+1)`).
The truncation relations of `M_{a-1,b}` for `v` (Garland identities) are `RavinderKernelTrunc`.
-/

namespace VOA.DeligneAudit.SectorWeyl

open VOA.AffineSl3

noncomputable section

/-! ## Generic sl₂ lemma -/

section SL2

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem sl2_H_Fpow (F H : V →ₗ[ℂ] V) (hHF : ∀ x, H (F x) - F (H x) = (-2 : ℂ) • F x)
    (u0 : V) (lam : ℂ) (hH : H u0 = lam • u0) :
    ∀ n : ℕ, H (F^[n] u0) = (lam - 2 * n) • F^[n] u0
  | 0 => by simpa using hH
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      have h := hHF (F^[n] u0)
      rw [sl2_H_Fpow F H hHF u0 lam hH n, map_smul] at h
      rw [sub_eq_iff_eq_add.mp h]
      push_cast
      rw [← add_smul]; congr 1; ring

theorem sl2_E_Fpow (E F H : V →ₗ[ℂ] V) (hEF : ∀ x, E (F x) - F (E x) = H x)
    (hHF : ∀ x, H (F x) - F (H x) = (-2 : ℂ) • F x)
    (u0 : V) (lam : ℂ) (hE : E u0 = 0) (hH : H u0 = lam • u0) :
    ∀ n : ℕ, E (F^[n + 1] u0) = (((n : ℂ) + 1) * (lam - n)) • F^[n] u0
  | 0 => by
      simp only [zero_add, Function.iterate_one, Function.iterate_zero, id, Nat.cast_zero]
      have h := hEF u0
      rw [hE, map_zero, sub_zero, hH] at h
      rw [h]; congr 1; ring
  | n + 1 => by
      rw [Function.iterate_succ_apply' F (n + 1)]
      have h := hEF (F^[n + 1] u0)
      rw [sl2_E_Fpow E F H hEF hHF u0 lam hE hH n, map_smul, sl2_H_Fpow F H hHF u0 lam hH (n + 1)]
        at h
      rw [sub_eq_iff_eq_add.mp h, ← Function.iterate_succ_apply' F n]
      rw [show F^[n + 1] u0 = F^[n + 1] u0 from rfl, ← add_smul]
      push_cast; congr 1; ring

/-- A vector killed by `e` and `f` with nonzero `h`-weight vanishes. -/
theorem sl2_vanish (E F H : V →ₗ[ℂ] V) (hEF : ∀ x, E (F x) - F (E x) = H x) {u : V} {mu : ℂ}
    (hmu : mu ≠ 0) (hEu : E u = 0) (hFu : F u = 0) (hHu : H u = mu • u) : u = 0 := by
  have h := hEF u
  rw [hFu, map_zero, hEu, map_zero, sub_zero, hHu] at h
  exact (smul_eq_zero.mp h.symm).resolve_left hmu

end SL2

/-! ## Operators of the `sl₃` current module -/

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule (bracketTable) V}

theorem comm_apply (a b : Fin 8) (r s : ℕ) (x : V) :
    ρ.op a r (ρ.op b s x) = ρ.op b s (ρ.op a r x) + ∑ e, bracketTable a b e • ρ.op e (r + s) x := by
  rw [← ρ.comm a b r s x]; abel

/-- Higher truncations from the bracket with `h₁ ⊗ t^j`. -/
theorem f_trunc_up {w : V} {fα : Fin 8} (h3 : 3 ≤ fα.val) (h6 : fα.val < 6) {N : ℕ}
    (hN : ρ.op fα N w = 0) (hcart : ∀ j, 1 ≤ j → ρ.op 6 j w = 0) :
    ∀ j, ρ.op fα (N + j) w = 0 := by
  intro j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simpa using hN
  obtain ⟨c, hc, hce⟩ := bracket_h1_f fα h3 h6
  have hcomm := ρ.comm 6 fα j N w
  rw [hN, map_zero, hcart j hj, map_zero, sub_zero] at hcomm
  rw [Finset.sum_eq_single fα (fun e _ he => by rw [hce, if_neg he, zero_smul]) (by simp),
    hce, if_pos rfl, add_comm j N] at hcomm
  exact (smul_eq_zero.mp hcomm.symm).resolve_left hc

variable {w : V} {a b : ℕ}

theorem mab_f1_trunc (h : MabRel ρ w a b) (N : ℕ) (hN : a + b ≤ N) : ρ.op 3 N w = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, N = a + b + j := ⟨N - (a + b), by omega⟩
  exact f_trunc_up (by decide) (by decide) h.trunc_f1 (fun j hj => h.cartan_pos 6 (by decide) j hj) j

theorem mab_f2_trunc (h : MabRel ρ w a b) (N : ℕ) (hN : a + b ≤ N) : ρ.op 4 N w = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, N = a + b + j := ⟨N - (a + b), by omega⟩
  exact f_trunc_up (by decide) (by decide) h.trunc_f2 (fun j hj => h.cartan_pos 6 (by decide) j hj) j

theorem mab_ftheta_trunc (h : MabRel ρ w a b) (N : ℕ) (hN : 2 * a + b ≤ N) : ρ.op 5 N w = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, N = 2 * a + b + j := ⟨N - (2 * a + b), by omega⟩
  exact f_trunc_up (by decide) (by decide) h.trunc_theta (fun j hj => h.cartan_pos 6 (by decide) j hj) j

/-! ## The kernel vector -/

/-- `(e ⊗ t^r) v = 0`. -/
theorem kernel_raising (h : MabRel ρ w a b) (ha : 1 ≤ a) (e : Fin 8) (he : e.val < 3) (r : ℕ) :
    ρ.op e r (ρ.op 5 (2 * a + b - 1) w) = 0 := by
  rw [comm_apply, h.raising e he, map_zero, zero_add]
  have : e = 0 ∨ e = 1 ∨ e = 2 := by omega
  rcases this with rfl | rfl | rfl
  · have := mab_f2_trunc h (r + (2 * a + b - 1)) (by omega)
    simp [Fin.sum_univ_eight, bracketTable, this]
  · have := mab_f1_trunc h (r + (2 * a + b - 1)) (by omega)
    simp [Fin.sum_univ_eight, bracketTable, this]
  · have hpos : 1 ≤ r + (2 * a + b - 1) := by omega
    simp [Fin.sum_univ_eight, bracketTable, h.cartan_pos 6 (by decide) _ hpos,
      h.cartan_pos 7 (by decide) _ hpos]

/-- `(h ⊗ t^r) v = 0` for `r ≥ 1`. -/
theorem kernel_cartan_pos (h : MabRel ρ w a b) (hh : Fin 8) (h6 : 6 ≤ hh.val) (r : ℕ) (hr : 1 ≤ r) :
    ρ.op hh r (ρ.op 5 (2 * a + b - 1) w) = 0 := by
  rw [comm_apply, h.cartan_pos hh h6 r hr, map_zero, zero_add]
  have : hh = 6 ∨ hh = 7 := by omega
  have ht : ρ.op 5 (r + (2 * a + b - 1)) w = 0 := mab_ftheta_trunc h _ (by omega)
  rcases this with rfl | rfl <;> simp [Fin.sum_univ_eight, bracketTable, ht]

/-- `(h ⊗ 1) v = (k - 1) v`. -/
theorem kernel_cartan_zero (h : MabRel ρ w a b) (ha : 1 ≤ a) (hh : Fin 8) (h6 : 6 ≤ hh.val) :
    ρ.op hh 0 (ρ.op 5 (2 * a + b - 1) w) = (((a - 1 + b : ℕ)) : ℂ) • ρ.op 5 (2 * a + b - 1) w := by
  rw [comm_apply, h.cartan_zero hh h6, map_smul]
  have : hh = 6 ∨ hh = 7 := by omega
  rcases this with rfl | rfl <;>
  · simp only [Fin.sum_univ_eight, bracketTable]
    simp
    rw [Nat.cast_sub ha, Nat.cast_one]
    module

/-- `F` commutes with `f_θ ⊗ t^s` when `[F, f_θ] = 0`. -/
theorem iterate_comm_op (fi : Fin 8) (hz : ∀ e, bracketTable fi 5 e = 0) (s : ℕ) :
    ∀ (n : ℕ) (x : V), (ρ.op fi 0)^[n] (ρ.op 5 s x) = ρ.op 5 s ((ρ.op fi 0)^[n] x)
  | 0, x => rfl
  | n + 1, x => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iterate_comm_op fi hz s n x,
        comm_apply]
      simp [hz]

/-- The lowering relation for the kernel vector, for a root `sl₂` `(E, F, H)`. -/
theorem kernel_lowering_aux (h : MabRel ρ w a b) (ha : 1 ≤ a)
    (ei fi hi : Fin 8) (he : ei.val < 3) (hh6 : 6 ≤ hi.val)
    (hEF : ∀ x, ρ.op ei 0 (ρ.op fi 0 x) - ρ.op fi 0 (ρ.op ei 0 x) = ρ.op hi 0 x)
    (hHF : ∀ x, ρ.op hi 0 (ρ.op fi 0 x) - ρ.op fi 0 (ρ.op hi 0 x) = (-2 : ℂ) • ρ.op fi 0 x)
    (hz : ∀ e, bracketTable fi 5 e = 0) (hFw : (ρ.op fi 0)^[a + b + 1] w = 0) :
    (ρ.op fi 0)^[a - 1 + b + 1] (ρ.op 5 (2 * a + b - 1) w) = 0 := by
  set v := ρ.op 5 (2 * a + b - 1) w with hv
  set k := a + b with hk
  have hk1 : a - 1 + b + 1 = k := by omega
  rw [hk1]
  have hE : ρ.op ei 0 v = 0 := kernel_raising h ha ei he 0
  have hH : ρ.op hi 0 v = (((k - 1 : ℕ)) : ℂ) • v := by
    rw [kernel_cartan_zero h ha hi hh6]; congr 2; omega
  set u := (ρ.op fi 0)^[k] v with hu
  have hFu : ρ.op fi 0 u = 0 := by
    rw [hu, ← Function.iterate_succ_apply' (ρ.op fi 0), hv, iterate_comm_op fi hz, hFw, map_zero]
  obtain ⟨n, hn⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hEu : ρ.op ei 0 u = 0 := by
    rw [hu, hn, sl2_E_Fpow (ρ.op ei 0) (ρ.op fi 0) (ρ.op hi 0) hEF hHF v _ hE hH n]
    have : ((k - 1 : ℕ) : ℂ) - n = 0 := by rw [show k - 1 = n by omega]; ring
    rw [this, mul_zero, zero_smul]
  have hHu : ρ.op hi 0 u = (((k - 1 : ℕ) : ℂ) - 2 * k) • u :=
    sl2_H_Fpow (ρ.op fi 0) (ρ.op hi 0) hHF v _ hH k
  refine sl2_vanish (ρ.op ei 0) (ρ.op fi 0) (ρ.op hi 0) hEF ?_ hEu hFu hHu
  rw [Nat.cast_sub (by omega : 1 ≤ k)]
  intro h0
  have : (k : ℂ) = -1 := by linear_combination -h0
  have h2 : ((k : ℕ) : ℝ) = -1 := by exact_mod_cast congrArg Complex.re this
  have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

/-- `f₁^{k} v = 0`. -/
theorem kernel_lowering_f1 (h : MabRel ρ w a b) (ha : 1 ≤ a) :
    (ρ.op 3 0)^[a - 1 + b + 1] (ρ.op 5 (2 * a + b - 1) w) = 0 :=
  kernel_lowering_aux h ha 0 3 6 (by decide) (by decide)
    (fun x => by rw [ρ.comm]; simp [Fin.sum_univ_eight, bracketTable])
    (fun x => by rw [ρ.comm]; simp [Fin.sum_univ_eight, bracketTable])
    (fun e => by fin_cases e <;> simp [bracketTable]) h.lowering_f1

/-- `f₂^{k} v = 0`. -/
theorem kernel_lowering_f2 (h : MabRel ρ w a b) (ha : 1 ≤ a) :
    (ρ.op 4 0)^[a - 1 + b + 1] (ρ.op 5 (2 * a + b - 1) w) = 0 :=
  kernel_lowering_aux h ha 1 4 7 (by decide) (by decide)
    (fun x => by rw [ρ.comm]; simp [Fin.sum_univ_eight, bracketTable])
    (fun x => by rw [ρ.comm]; simp [Fin.sum_univ_eight, bracketTable])
    (fun e => by fin_cases e <;> simp [bracketTable]) h.lowering_f2


/-- **Named literature input `RavinderKernelTrunc`** (Ravinder, Thm. 1, via the Garland identities;
Chari–Pressley, Chari–Venkatesh).  For `a ≥ 1` and `w` satisfying the relations of `M_{a,b}`, the
kernel vector `v = (f_θ ⊗ t^{2a+b-1}) w` satisfies the three truncation relations of `M_{a-1,b}`.
All the other relations of `M_{a-1,b}` for `v` are proved above. -/
def RavinderKernelTrunc : Prop :=
  ∀ (a b : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule (bracketTable) V) (w : V),
    1 ≤ a → MabRel ρ w a b →
      ρ.op 3 (a - 1 + b) (ρ.op 5 (2 * a + b - 1) w) = 0 ∧
      ρ.op 4 (a - 1 + b) (ρ.op 5 (2 * a + b - 1) w) = 0 ∧
      ρ.op 5 (2 * (a - 1) + b) (ρ.op 5 (2 * a + b - 1) w) = 0

/-- **F4′ from the named truncations**: `RavinderKernelTrunc → RavinderKernelRel`. -/
theorem ravinderKernelRel_of_trunc (hT : RavinderKernelTrunc) : RavinderKernelRel := by
  intro a b V _ _ ρ w ha h
  obtain ⟨t1, t2, t3⟩ := hT a b V ρ w ha h
  exact { raising := kernel_raising h ha
          cartan_pos := kernel_cartan_pos h
          cartan_zero := kernel_cartan_zero h ha
          lowering_f1 := kernel_lowering_f1 h ha
          lowering_f2 := kernel_lowering_f2 h ha
          trunc_f1 := t1
          trunc_f2 := t2
          trunc_theta := t3 }

end

end VOA.DeligneAudit.SectorWeyl

section AxiomAudit
#print axioms VOA.DeligneAudit.SectorWeyl.kernel_raising
#print axioms VOA.DeligneAudit.SectorWeyl.kernel_cartan_pos
#print axioms VOA.DeligneAudit.SectorWeyl.kernel_cartan_zero
#print axioms VOA.DeligneAudit.SectorWeyl.kernel_lowering_f1
#print axioms VOA.DeligneAudit.SectorWeyl.kernel_lowering_f2
#print axioms VOA.DeligneAudit.SectorWeyl.ravinderKernelRel_of_trunc
end AxiomAudit
