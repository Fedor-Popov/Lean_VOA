import VOA.DeligneAudit.D4LevelReductionCoreSubsetCellBound
import VOA.DeligneAudit.SL4TTruncatedMiddleModule

/-! Root mode cutoffs for symmetric outer labels in truncated sl4 local Weyl modules. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector

attribute [local instance 2000] Fin.fintype Fin.instOfNat

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The Cartan current for either of the two adjacent composite roots. -/
def sl4AdjacentCartan (Q : CurrentModule bracketTable V) (i : Fin 2) (s : ℕ) :
    Module.End ℂ V :=
  Q.op (if i = 0 then 12 else 13) s + Q.op (if i = 0 then 13 else 14) s

/-- Both adjacent composite roots define rank-one current subalgebras. -/
theorem sl4Adjacent_currentRelations (Q : CurrentModule bracketTable V) (i : Fin 2) :
    CVsl2.SL2 (Q.op (if i = 0 then 1 else 4)) (sl4AdjacentCartan Q i)
      (Q.op (if i = 0 then 7 else 10)) := by
  let e : Fin 15 := if i = 0 then 1 else 4
  let f : Fin 15 := if i = 0 then 7 else 10
  let h : Fin 15 := if i = 0 then 12 else 13
  let k : Fin 15 := if i = 0 then 13 else 14
  have ht :
      (∀ z, bracketTable e f z = (if z = h then 1 else 0) +
        (if z = k then 1 else 0)) ∧
      (∀ z, bracketTable h f z + bracketTable k f z = if z = f then -2 else 0) ∧
      (∀ z, bracketTable h e z + bracketTable k e z = if z = e then 2 else 0) ∧
      (∀ z, bracketTable f f z = 0) ∧ (∀ z, bracketTable e e z = 0) := by
    have hi :
        (∀ z, bracketInt e f z = (if z = h then 1 else 0) +
          (if z = k then 1 else 0)) ∧
        (∀ z, bracketInt h f z + bracketInt k f z = if z = f then -2 else 0) ∧
        (∀ z, bracketInt h e z + bracketInt k e z = if z = e then 2 else 0) ∧
        (∀ z, bracketInt f f z = 0) ∧ (∀ z, bracketInt e e z = 0) := by
      fin_cases i <;> decide +kernel
    unfold bracketTable
    exact_mod_cast hi
  obtain ⟨hEF, hHF, hHE, hFF, hEE⟩ := ht
  change CVsl2.SL2 (Q.op e) (fun s => Q.op h s + Q.op k s) (Q.op f)
  refine ⟨fun r s => ?_, fun r s => ?_, fun r s => ?_,
    fun r s => ?_, fun r s => ?_⟩
  · rw [coreCurrent_commutator]
    simp [hEF, add_smul, Finset.sum_add_distrib]
  · simp only [add_mul, mul_add, add_sub_add_comm]
    rw [coreCurrent_commutator, coreCurrent_commutator, ← Finset.sum_add_distrib]
    simp_rw [← add_smul, hHF]
    simp [ite_smul]
  · simp only [add_mul, mul_add, add_sub_add_comm]
    rw [coreCurrent_commutator, coreCurrent_commutator, ← Finset.sum_add_distrib]
    simp_rw [← add_smul, hHE]
    simp [ite_smul]
  · rw [← sub_eq_zero, coreCurrent_commutator]
    simp [hFF]
  · rw [← sub_eq_zero, coreCurrent_commutator]
    simp [hEE]

variable [FiniteDimensional ℂ V]
variable (Q : CurrentModule bracketTable V) (v : V) (a b : ℕ)
variable (hw : LocalWeylRel Q v (weightABC a b a))

include hw

/-- Each adjacent negative root has cutoff equal to the sum of its two labels. -/
theorem sl4Adjacent_mode_zero (i : Fin 2) (s : ℕ) (hs : a + b ≤ s) :
    Q.op (if i = 0 then 7 else 10) s v = 0 := by
  apply coreHighest_lowering_modes (sl4Adjacent_currentRelations Q i) v (a + b)
  · intro r
    apply hw.raising
    split_ifs <;> decide
  · have h₀ := hw.cartan_zero 0
    have h₁ := hw.cartan_zero 1
    have h₂ := hw.cartan_zero 2
    simp only [simpleH, weightABC] at h₀ h₁ h₂
    fin_cases i <;>
      simp [sl4AdjacentCartan, h₀, h₁, h₂, Nat.cast_add, add_smul, add_comm]
  · intro r hr
    have h₀ := hw.cartan_pos 0 r hr
    have h₁ := hw.cartan_pos 1 r hr
    have h₂ := hw.cartan_pos 2 r hr
    simp only [simpleH] at h₀ h₁ h₂
    fin_cases i <;> simp [sl4AdjacentCartan, h₀, h₁, h₂]
  · exact hs

/-- Among negative roots, only the highest root can survive at the mixed-label cutoff. -/
theorem sl4_nonHighest_mode_zero (e : Fin 15) (he : e ≠ 8)
    (s : ℕ) (hs : a + b ≤ s) : Q.op e s v = 0 := by
  by_cases hp : e.val < 6
  · exact hw.raising e hp s
  have h₁ := simple_mode_zero Q v (weightABC a b a) hw 0 s (by
    change a ≤ s
    omega)
  have h₂ := simple_mode_zero Q v (weightABC a b a) hw 1 s (by
    change b ≤ s
    omega)
  have h₃ := simple_mode_zero Q v (weightABC a b a) hw 2 s (by
    change a ≤ s
    omega)
  have hc : ∀ j, Q.op (simpleH j) s v = 0 := by
    intro j
    by_cases hz : s = 0
    · subst s
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst a
      subst b
      have hj := hw.cartan_zero j
      fin_cases j <;> simpa [weightABC] using hj
    · exact hw.cartan_pos j s (by omega)
  have hc₁ := hc 0
  have hc₂ := hc 1
  have hc₃ := hc 2
  have h₁₂ := sl4Adjacent_mode_zero Q v a b hw 0 s hs
  have h₂₃ := sl4Adjacent_mode_zero Q v a b hw 1 s hs
  fin_cases e <;> simp at hp he
  all_goals simp_all [simpleF, simpleH]

omit [FiniteDimensional ℂ V] in
/-- The highest-root current satisfies the quadratic Garland relation at its total weight. -/
theorem sl4Highest_quadratic_relation (s : ℕ) (hs : 2 * a + b + 1 ≤ s + 2) :
    ∑ x ∈ Finset.antidiagonal s, Q.op 8 x.1 (Q.op 8 x.2 v) = 0 := by
  have hS := coreHighest_currentRelations Q
  have hn := a3_highest_nilpotence Q v a b a hw
  have hpos : ∀ m, coreHighestCartan Q (m + 1) v = 0 := by
    intro m
    have h₀ := hw.cartan_pos 0 (m + 1) (by omega)
    have h₁ := hw.cartan_pos 1 (m + 1) (by omega)
    have h₂ := hw.cartan_pos 2 (m + 1) (by omega)
    simp only [simpleH] at h₀ h₁ h₂
    simp [coreHighestCartan, h₀, h₁, h₂]
  exact Garland.garland_two (fun k => by simpa [Nat.add_comm] using hS.hEF 1 k)
    (fun m k => hS.hHF (m + 1) k) hS.hFF (hw.raising 2 (by decide) 1)
    hpos hn s (by omega)

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.sl4Adjacent_currentRelations
#print axioms VOA.DeligneAudit.D4LevelReduction.sl4Adjacent_mode_zero
#print axioms VOA.DeligneAudit.D4LevelReduction.sl4_nonHighest_mode_zero
#print axioms VOA.DeligneAudit.D4LevelReduction.sl4Highest_quadratic_relation
