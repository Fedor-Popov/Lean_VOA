/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2DivisorPairCert

/-!
# Good pair tables

For slots `a ≠ b` and spectators `s`, `Good a b s` is the `P_m`-submodule of pair tables whose
embedding lies in `P_m M_m`.  It is closed under the pair operators (`good_S`, `good_A`, from
`pairS_mem`, `pairA_mem`), and contains `F · δ₅⊗δ₅` for canonical `s`, where
`F = ∏_{j ∉ {a,b}} D_j³` (`good_base`, from the `all_slots`).  Integer tables are cast to pair tables
by `castT`, intertwining the integer coadjoint matrices with `opA`, `opB`.
-/

namespace VOA.DeligneAudit.A2

open MvPolynomial VOA.AffineSl3 VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.SectorFiber
open VOA.DeligneAudit.SectorFiberModule VOA.QuadraticCurrentFunctionalCarrier
open PairCert

noncomputable section

variable {m : ℕ}

set_option maxHeartbeats 8000000 in
theorem bracketTable_eq_bZ (x c e : Fin 8) : bracketTable x c e = (bZ x c e : ℂ) := by
  fin_cases x <;> fin_cases c <;> fin_cases e <;> simp [bracketTable, bZ]

/-- Cast of an integer table. -/
def castT (T : ZT) : PairTable m := fun c d => MvPolynomial.C ((T c d : ℤ) : ℂ)

theorem opA_castT (x : Fin 8) (T : ZT) : opA x (castT (m := m) T) = castT (opAZ x T) := by
  funext c d
  simp only [opA, castT, opAZ, bracketTable_eq_bZ, Int.cast_neg, Int.cast_sum, Int.cast_mul,
    map_neg, map_sum, map_mul]

theorem opB_castT (x : Fin 8) (T : ZT) : opB x (castT (m := m) T) = castT (opBZ x T) := by
  funext c d
  simp only [opB, castT, opBZ, bracketTable_eq_bZ, Int.cast_neg, Int.cast_sum, Int.cast_mul,
    map_neg, map_sum, map_mul]

theorem castT_add (T U : ZT) :
    castT (m := m) (fun c d => T c d + U c d) = castT T + castT U := by
  funext c d; simp [castT]

theorem castT_sub (T U : ZT) :
    castT (m := m) (fun c d => T c d - U c d) = castT T - castT U := by
  funext c d; simp [castT]

theorem castT_mul (k : ℤ) (T : ZT) :
    castT (m := m) (fun c d => k * T c d) = (MvPolynomial.C (k : ℂ) : Pm m) • castT T := by
  funext c d; simp [castT]

theorem opA_smul (x : Fin 8) (p : Pm m) (Y : PairTable m) : opA x (p • Y) = p • opA x Y := by
  funext c d
  simp only [opA, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_neg]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

theorem opB_smul (x : Fin 8) (p : Pm m) (Y : PairTable m) : opB x (p • Y) = p • opB x Y := by
  funext c d
  simp only [opB, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_neg]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- `emb` as a `P_m`-linear map. -/
def embL (a b : Fin m) (s : Fin m → Fin 8) : PairTable m →ₗ[Pm m] TP m where
  toFun := emb a b s
  map_add' := emb_add a b s
  map_smul' := emb_smul a b s

/-- Pair tables whose embedding lies in `P_m M_m`. -/
def Good (a b : Fin m) (s : Fin m → Fin 8) : Submodule (Pm m) (PairTable m) :=
  (MP m).comap (embL a b s)

/-- `H = G_a G_b`. -/
abbrev Hpair (a b : Fin m) : Pm m := Gpair a b a * Gpair a b b

/-- `z_a - z_b`. -/
abbrev zab (a b : Fin m) : Pm m := zr (K := ℂ) a - zr b

theorem good_S (x : Fin 8) {a b : Fin m} (hab : a ≠ b) {s : Fin m → Fin 8} {Y : PairTable m}
    (hY : Y ∈ Good a b s) : Hpair a b • (opA x Y + opB x Y) ∈ Good a b s := by
  change emb a b s (Hpair a b • (opA x Y + opB x Y)) ∈ MP m
  rw [emb_smul, emb_add, ← slotOp_emb_a x a b hab, ← slotOp_emb_b x a b hab]
  exact pairS_mem x a b hab hY

theorem good_A (x : Fin 8) {a b : Fin m} (hab : a ≠ b) {s : Fin m → Fin 8} {Y : PairTable m}
    (hY : Y ∈ Good a b s) : (Hpair a b * zab a b) • (opA x Y - opB x Y) ∈ Good a b s := by
  change emb a b s ((Hpair a b * zab a b) • (opA x Y - opB x Y)) ∈ MP m
  have hsub : emb a b s (opA x Y - opB x Y) = emb a b s (opA x Y) - emb a b s (opB x Y) := by
    rw [sub_eq_add_neg, emb_add, ← neg_one_smul (Pm m) (opB x Y), emb_smul, neg_one_smul,
      ← sub_eq_add_neg]
  rw [emb_smul, hsub, ← slotOp_emb_a x a b hab, ← slotOp_emb_b x a b hab]
  exact pairA_mem x a b hab hY

/-- Tree step `S`. -/
theorem good_S_castT (x : Fin 8) {a b : Fin m} (hab : a ≠ b) {s : Fin m → Fin 8}
    {T T' : ZT} {q q' : Pm m} (h : q • castT T ∈ Good a b s) (hT : T' = SZ x T)
    (hq : q' = Hpair a b * q) : q' • castT T' ∈ Good a b s := by
  have := good_S x hab h
  rw [opA_smul, opB_smul, ← smul_add, smul_smul, opA_castT, opB_castT, ← castT_add] at this
  rw [hT, hq]
  exact this

/-- Tree step `A`. -/
theorem good_A_castT (x : Fin 8) {a b : Fin m} (hab : a ≠ b) {s : Fin m → Fin 8}
    {T T' : ZT} {q q' : Pm m} (h : q • castT T ∈ Good a b s) (hT : T' = AZ x T)
    (hq : q' = Hpair a b * zab a b * q) : q' • castT T' ∈ Good a b s := by
  have := good_A x hab h
  rw [opA_smul, opB_smul, ← smul_sub, smul_smul, opA_castT, opB_castT, ← castT_sub] at this
  rw [hT, hq]
  exact this

/-- `F = ∏_{j ∉ {a,b}} D_j³`. -/
def Fspec (a b : Fin m) : Pm m := ∏ j ∈ Finset.univ.filter (fun j => j ≠ a ∧ j ≠ b), Dslot j ^ 3

theorem tB0_eq (c d : Fin 8) : tB0 c d = if c = 5 ∧ d = 5 then 1 else 0 := by
  revert c d; decide

theorem emb_tB0 {a b : Fin m} (hab : a ≠ b) {s : Fin m → Fin 8} (hs : IsCanon a b s) :
    emb a b s (castT tB0) = deltaT s := by
  funext t
  rw [emb_apply a b hab]
  have hpl : pairLabel a b s 5 5 = s := by
    funext k
    by_cases hkb : k = b
    · subst hkb; simp [pairLabel, hs.2]
    · by_cases hka : k = a
      · subst hka; simp [pairLabel, Function.update_of_ne hkb, hs.1]
      · simp [pairLabel, Function.update_of_ne hka, Function.update_of_ne hkb]
  have key : t = s ↔ AgreeOff a b s t ∧ t a = 5 ∧ t b = 5 := by
    rw [← pairLabel_eq_iff a b hab s t 5 5, hpl]
  simp only [deltaT, key, castT, tB0_eq]
  by_cases h : AgreeOff a b s t <;> by_cases h1 : t a = 5 <;> by_cases h2 : t b = 5 <;> simp [h, h1, h2]

/-- **Base**: `F · δ₅⊗δ₅` is good for canonical spectators. -/
theorem good_base {a b : Fin m} (hab : a ≠ b) {s : Fin m → Fin 8} (hs : IsCanon a b s) :
    Fspec a b • castT tB0 ∈ Good a b s := by
  change emb a b s (Fspec a b • castT tB0) ∈ MP m
  rw [emb_smul, emb_tB0 hab hs, Fspec]
  apply all_slots
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_not] at hj
  rcases hj with rfl | rfl
  · exact hs.1
  · exact hs.2

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.good_S_castT
#print axioms VOA.DeligneAudit.A2.good_A_castT
#print axioms VOA.DeligneAudit.A2.good_base
end AxiomAudit
