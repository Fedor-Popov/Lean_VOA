import VOA.DeligneAudit.DeligneFusionCVRoots
import VOA.DeligneAudit.DeligneFusionCVShifted

/-!
# The three-level A₂ CV presentation

This is the auxiliary presentation used in the Setia--Rani--Khandai
recursion. Its three partitions have parts 1, 2 and 3. No dimension bound
or fusion identification is assumed. `mabRel_zero_cv3` places the existing
pure-adjoint presentation in this family.
-/

namespace VOA.DeligneAudit.A2.CVFamily

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.CVPart

abbrev Weight := ℕ × ℕ

/-- A partition with `r` threes, `n` twos, and `e` ones. -/
def parts (r n e : ℕ) : List ℕ :=
  List.replicate r 3 ++ List.replicate n 2 ++ List.replicate e 1

theorem parts_length (r n e : ℕ) : (parts r n e).length = r + n + e := by
  simp [parts, Nat.add_assoc]

theorem parts_tail (r n e : ℕ) : T (r + n) (parts r n e) = e := by
  simp only [parts, T_append, T_replicate, List.length_append, List.length_replicate]
  omega

theorem parts_last_tail (r n e : ℕ) (he : 1 ≤ e) :
    T (r + n + e - 1) (parts r n e) = 1 := by
  simp only [parts, T_append, T_replicate, List.length_append, List.length_replicate]
  omega

/-- A₂ highest-weight and rootwise CV relations, with no dimension premise. -/
structure CV3Rel {V : Type} [AddCommGroup V] [Module ℂ V]
    (R : CurrentModule bracketTable V) (w : V) (ε ν ϱ : Weight) (j : ℕ) : Prop where
  raising : ∀ (e : Fin 8), e.val < 3 → ∀ k, R.op e k w = 0
  cartan_pos : ∀ (h : Fin 8), 6 ≤ h.val → ∀ k, 1 ≤ k → R.op h k w = 0
  cartan_first : R.op 6 0 w = ((ε.1 + 2 * ν.1 + 3 * ϱ.1 + j : ℕ) : ℂ) • w
  cartan_second : R.op 7 0 w = ((ε.2 + 2 * ν.2 + 3 * ϱ.2 + j : ℕ) : ℂ) • w
  lowering_first : (R.op 3 0)^[ε.1 + 2 * ν.1 + 3 * ϱ.1 + j + 1] w = 0
  lowering_second : (R.op 4 0)^[ε.2 + 2 * ν.2 + 3 * ϱ.2 + j + 1] w = 0
  first : CVRel (R.op 3) (parts ϱ.1 ν.1 (ε.1 + j)) w
  second : CVRel (R.op 4) (parts ϱ.2 ν.2 (ε.2 + j)) w
  highest : CVRel (R.op 5) (parts (ϱ.1 + ϱ.2) (ν.1 + ν.2 + j) (ε.1 + ε.2)) w

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule bracketTable V} {w : V}

/-- The adjoint-power presentation is the zero-auxiliary member of the family. -/
theorem mabRel_zero_cv3 {N : ℕ} (h : MabRel R w 0 N) (hN : 0 < N) :
    CV3Rel R w (0, 0) (0, 0) (0, 0) N := by
  refine ⟨h.raising, h.cartan_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using h.cartan_zero 6 (by decide)
  · simpa using h.cartan_zero 7 (by decide)
  · simpa using h.lowering_f1
  · simpa using h.lowering_f2
  · simpa [parts] using CVRoots.first h hN
  · simpa [parts] using CVRoots.second h hN
  · simpa [parts] using CVRoots.highest h hN

/-- Every CV presentation kills individual modes beyond the partition length. -/
theorem trunc_of_cvrel {F : ℕ → Module.End ℂ V} {ξ : List ℕ}
    (h : CVRel F ξ w) (s : ℕ) (hs : ξ.length ≤ s) : F s w = 0 := by
  have ht : T ξ.length ξ = 0 := T_of_le _ _ le_rfl
  simpa only [Q_one] using h 1 s ξ.length (by omega) (by omega)

/-- A final part equal to one gives square nilpotence of the top mode. -/
theorem top_square_of_cvrel {F : ℕ → Module.End ℂ V}
    (hFF : ∀ k l, F k * F l = F l * F k)
    {r n j : ℕ} (hj : 1 ≤ j) (h : CVRel F (parts r n j) w) :
    (F (r + n + j - 1) ^ 2) w = 0 := by
  have htr : ∀ q, r + n + j ≤ q → F q w = 0 := by
    intro q hq
    exact trunc_of_cvrel h q (by simpa only [parts_length] using hq)
  have ht := parts_last_tail r n j hj
  have hq : Q F 2 ((r + n + j - 1) * 2) w = 0 :=
    h 2 _ (r + n + j - 1) (by omega) (by omega)
  rwa [Q_top hFF htr] at hq

variable {ν ϱ : Weight} {j : ℕ}

/-- The highest-root truncation in the zero-epsilon auxiliary family. -/
theorem theta_trunc (h : CV3Rel R w (0, 0) ν ϱ j) (q : ℕ)
    (hq : (ν.1 + ϱ.1) + (ν.2 + ϱ.2) + j ≤ q) : R.op 5 q w = 0 := by
  apply trunc_of_cvrel h.highest q
  simp only [parts_length]
  omega

/-- The second simple-root top mode is square nilpotent, uniformly in the auxiliaries. -/
theorem second_top_square (h : CV3Rel R w (0, 0) ν ϱ j) (hj : 1 ≤ j) :
    (R.op 4 (ν.2 + ϱ.2 + j - 1) ^ 2) w = 0 := by
  have hsecond : CVRel (R.op 4) (parts ϱ.2 ν.2 j) w := by
    simpa only [Nat.zero_add] using h.second
  simpa only [Nat.zero_add, Nat.add_comm ϱ.2 ν.2] using
    top_square_of_cvrel (r := ϱ.2) (n := ν.2) (j := j)
      (CVRoots.sl2_second R).hFF hj hsecond

/-- The quadratic cutoff relation used in the first cross-root kernel map. -/
theorem first_cutoff_two (h : CV3Rel R w (0, 0) ν ϱ j) :
    QFrom (R.op 3) (ν.1 + ϱ.1) 2 (2 * (ν.1 + ϱ.1) + j - 1) w = 0 := by
  apply cvrel_cutoff (CVRoots.sl2_first R).hFF h.first
    (ν.1 + ϱ.1) 2 _ (by omega)
  have ht : T (ν.1 + ϱ.1) (parts ϱ.1 ν.1 (0 + j)) = j := by
    simpa only [Nat.zero_add, Nat.add_comm ν.1 ϱ.1] using parts_tail ϱ.1 ν.1 j
  rw [ht]
  omega

/-- The cubic cutoff relation used in the first cross-root kernel map. -/
theorem first_cutoff_three (h : CV3Rel R w (0, 0) ν ϱ j) (hj : 1 ≤ j) :
    QFrom (R.op 3) (ν.1 + ϱ.1) 3 (3 * (ν.1 + ϱ.1) + j - 1) w = 0 := by
  apply cvrel_cutoff (CVRoots.sl2_first R).hFF h.first
    (ν.1 + ϱ.1) 3 _ (by omega)
  have ht : T (ν.1 + ϱ.1) (parts ϱ.1 ν.1 (0 + j)) = j := by
    simpa only [Nat.zero_add, Nat.add_comm ν.1 ϱ.1] using parts_tail ϱ.1 ν.1 j
  rw [ht]
  omega

end VOA.DeligneAudit.A2.CVFamily

#print axioms VOA.DeligneAudit.A2.CVFamily.mabRel_zero_cv3
#print axioms VOA.DeligneAudit.A2.CVFamily.theta_trunc
#print axioms VOA.DeligneAudit.A2.CVFamily.second_top_square
#print axioms VOA.DeligneAudit.A2.CVFamily.first_cutoff_two
#print axioms VOA.DeligneAudit.A2.CVFamily.first_cutoff_three
