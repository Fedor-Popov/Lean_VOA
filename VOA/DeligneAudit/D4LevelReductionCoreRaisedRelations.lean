import VOA.DeligneAudit.D4LevelReductionCoreSubsetBound

/-! Highest-weight relations of the middle-raised vector on a single-adjoint core cell. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

attribute [local instance 2000] Fin.fintype Fin.instOfNat

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The bracket with the middle positive root, in the fixed matrix-root basis. -/
def coreMiddleBracket (Q : CurrentModule A3Sector.bracketTable V) (e : Fin 15) (s : ℕ) :
    Module.End ℂ V :=
  if e = 0 then Q.op 1 s else if e = 5 then -Q.op 4 s else
  if e = 7 then -Q.op 6 s else if e = 9 then -Q.op 13 s else
  if e = 10 then Q.op 11 s else if e = 12 then -Q.op 3 s else
  if e = 13 then (2 : ℂ) • Q.op 3 s else if e = 14 then -Q.op 3 s else 0

/-- The integer root table certifies every bracket with the middle raising current. -/
theorem coreMiddle_commutator (Q : CurrentModule A3Sector.bracketTable V)
    (e : Fin 15) (r s : ℕ) (v : V) :
    Q.op e r (Q.op 3 s v) = Q.op 3 s (Q.op e r v) + coreMiddleBracket Q e (r + s) v := by
  have ht : ∀ e k : Fin 15, A3Sector.bracketInt e 3 k =
      if e = 0 then (if k = 1 then 1 else 0) else
      if e = 5 then (if k = 4 then -1 else 0) else
      if e = 7 then (if k = 6 then -1 else 0) else
      if e = 9 then (if k = 13 then -1 else 0) else
      if e = 10 then (if k = 11 then 1 else 0) else
      if e = 12 then (if k = 3 then -1 else 0) else
      if e = 13 then (if k = 3 then 2 else 0) else
      if e = 14 then (if k = 3 then -1 else 0) else 0 := by decide +kernel
  have hc := Q.comm e 3 r s v
  rw [sub_eq_iff_eq_add] at hc
  rw [hc, add_comm]
  congr 1
  fin_cases e <;>
    simp [coreMiddleBracket, A3Sector.bracketTable, ht, ite_smul]

/-- A finite-dimensional highest vector with a negative integral simple weight is zero. -/
theorem coreFinite_negative_highest [FiniteDimensional ℂ V]
    (Q : CurrentModule A3Sector.bracketTable V) (v : V) (j : Fin 3) (d : ℤ)
    (hd : d < 0) (he : Q.op (A3Sector.simpleE j) 0 v = 0)
    (hh : Q.op (A3Sector.simpleH j) 0 v = (d : ℂ) • v) : v = 0 := by
  have hEF : ∀ x, Q.op (A3Sector.simpleE j) 0 (Q.op (A3Sector.simpleF j) 0 x) -
      Q.op (A3Sector.simpleF j) 0 (Q.op (A3Sector.simpleE j) 0 x) =
        Q.op (A3Sector.simpleH j) 0 x := by
    intro x
    rw [Q.comm]
    simp [A3Sector.simple_ef_table]
  have hHF : ∀ x, Q.op (A3Sector.simpleH j) 0 (Q.op (A3Sector.simpleF j) 0 x) -
      Q.op (A3Sector.simpleF j) 0 (Q.op (A3Sector.simpleH j) 0 x) =
        (-2 : ℂ) • Q.op (A3Sector.simpleF j) 0 x := by
    intro x
    rw [Q.comm]
    simp [A3Sector.simple_hf_table]
  obtain ⟨N, hN⟩ := coreLowering_locally_nilpotent
    (Q.op (A3Sector.simpleF j) 0) (Q.op (A3Sector.simpleH j) 0) hHF v d hh
  exact (CLFilt.hw_pow _ _ _ hEF hHF he hh N hN).1 hd

/-- The data shared by all single-adjoint cell generators. -/
structure SingleAdjointCellRelations
    (Q : CurrentModule A3Sector.bracketTable V) (v : V) (b : ℕ) : Prop where
  parabolic : ∀ e : Fin 15, e.val < 6 → e ≠ 3 → ∀ r, Q.op e r v = 0
  weight : ∀ j, Q.op (A3Sector.simpleH j) 0 v = (A3Sector.weightABC 1 b 1 j : ℂ) • v
  cartan : ∀ j s, 0 < s → Q.op (A3Sector.simpleH j) s v = 0
  middle : ∀ s, 0 < s → Q.op 3 s v = 0

variable [FiniteDimensional ℂ V]
variable (Q : CurrentModule A3Sector.bracketTable V) (v : V) (b : ℕ)
variable (h : SingleAdjointCellRelations Q v b)

include h

/-- Two middle zero modes vanish because they would give a negative outer highest weight. -/
theorem singleAdjoint_middle_square : Q.op 3 0 (Q.op 3 0 v) = 0 := by
  apply coreFinite_negative_highest Q _ 0 (-1) (by omega)
  · have he0 := coreMiddle_commutator Q 0 0 0 v
    have he1 := coreMiddle_commutator Q 1 0 0 v
    have he2 := coreMiddle_commutator Q 0 0 0 (Q.op 3 0 v)
    simp [coreMiddleBracket, h.parabolic 0 (by decide) (by decide) 0,
      h.parabolic 1 (by decide) (by decide) 0] at he0 he1
    simpa [A3Sector.simpleE, coreMiddleBracket, he0, he1] using he2
  · have hw := h.weight 0
    norm_num [A3Sector.simpleH, A3Sector.weightABC] at hw
    have he1 := coreMiddle_commutator Q 12 0 0 v
    have he2 := coreMiddle_commutator Q 12 0 0 (Q.op 3 0 v)
    simp [coreMiddleBracket, hw] at he1
    simpa [A3Sector.simpleH, coreMiddleBracket, he1] using he2

/-- The raised vector has dominant middle weight with zero outer labels. -/
theorem singleAdjoint_raised_weight (j : Fin 3) :
    Q.op (A3Sector.simpleH j) 0 (Q.op 3 0 v) =
      (A3Sector.weightABC 0 (b + 2) 0 j : ℂ) • Q.op 3 0 v := by
  rw [coreMiddle_commutator, h.weight, map_smul]
  fin_cases j <;>
    norm_num [A3Sector.simpleH, A3Sector.weightABC, coreMiddleBracket, Fin.ext_iff] <;> module

/-- Positive Cartan modes kill the raised vector. -/
theorem singleAdjoint_raised_cartan (j : Fin 3) (s : ℕ) (hs : 0 < s) :
    Q.op (A3Sector.simpleH j) s (Q.op 3 0 v) = 0 := by
  rw [coreMiddle_commutator, h.cartan j s hs, map_zero, zero_add]
  fin_cases j <;> simp [A3Sector.simpleH, coreMiddleBracket, h.middle s hs]

/-- All positive root currents kill the raised vector. -/
theorem singleAdjoint_raised_highest (e : Fin 15) (he : e.val < 6) (s : ℕ) :
    Q.op e s (Q.op 3 0 v) = 0 := by
  by_cases heq : e = 3
  · subst e
    by_cases hs : s = 0
    · subst s
      exact singleAdjoint_middle_square Q v b h
    · rw [coreMiddle_commutator, h.middle s (by omega)]
      simp [coreMiddleBracket]
  · rw [coreMiddle_commutator, h.parabolic e he heq s, map_zero, zero_add]
    have he' : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 4 ∨ e = 5 := by omega
    rcases he' with rfl | rfl | rfl | rfl | rfl <;>
      simp [coreMiddleBracket, h.parabolic 1 (by decide) (by decide) s,
        h.parabolic 4 (by decide) (by decide) s]

/-- The raised vector satisfies all local Weyl relations at doubled middle weight. -/
theorem singleAdjoint_raised_localWeyl :
    A3Sector.LocalWeylRel Q (Q.op 3 0 v) (A3Sector.weightABC 0 (b + 2) 0) := by
  refine ⟨singleAdjoint_raised_highest Q v b h, singleAdjoint_raised_cartan Q v b h,
    singleAdjoint_raised_weight Q v b h, ?_⟩
  intro j
  exact coreFinite_simple_lowering Q _ j _
    (singleAdjoint_raised_highest Q v b h _ (A3Sector.simpleE_raising j) 0)
    (singleAdjoint_raised_weight Q v b h j)

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.coreMiddle_commutator
#print axioms VOA.DeligneAudit.D4LevelReduction.coreFinite_negative_highest
#print axioms VOA.DeligneAudit.D4LevelReduction.singleAdjoint_middle_square
#print axioms VOA.DeligneAudit.D4LevelReduction.singleAdjoint_raised_weight
#print axioms VOA.DeligneAudit.D4LevelReduction.singleAdjoint_raised_cartan
#print axioms VOA.DeligneAudit.D4LevelReduction.singleAdjoint_raised_highest
#print axioms VOA.DeligneAudit.D4LevelReduction.singleAdjoint_raised_localWeyl
