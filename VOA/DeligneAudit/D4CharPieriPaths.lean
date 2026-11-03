import VOA.DeligneAudit.D4CharPieriWeights

/-! Finite binary-state sums for the two transfer runs. All lengths are arbitrary. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

variable {R : Type*} [CommRing R]

noncomputable section

def pieriSelect (v : R × R) (s : Bool) : R := if s then v.2 else v.1

def pieriBinaryStep (M : Bool → Bool → R) (v : R × R) : R × R :=
  (v.1 * M false false + v.2 * M true false,
    v.1 * M false true + v.2 * M true true)

/-- Sum over all state strings; each of the n edges contributes its matrix entry. -/
def pieriPathSum {n : ℕ} (M : Fin n → Bool → Bool → R) (v : R × R) : R :=
  ∑ s : Fin (n + 1) → Bool,
    pieriSelect v (s 0) * ∏ i : Fin n, M i (s i.castSucc) (s i.succ)

theorem pieriPathSum_zero (M : Fin 0 → Bool → Bool → R) (v : R × R) :
    pieriPathSum M v = v.1 + v.2 := by
  classical
  unfold pieriPathSum
  rw [← (Fin.consEquiv fun _ : Fin 1 => Bool).sum_comp]
  simp [Fintype.sum_prod_type, pieriSelect, add_comm]

/-- Splitting off the first state identifies path enumeration with matrix multiplication. -/
theorem pieriPathSum_succ {n : ℕ} (M : Fin (n + 1) → Bool → Bool → R) (v : R × R) :
    pieriPathSum M v = pieriPathSum (fun i => M i.succ) (pieriBinaryStep (M 0) v) := by
  classical
  unfold pieriPathSum
  rw [← (Fin.consEquiv fun _ : Fin (n + 2) => Bool).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.consEquiv_apply, Fin.prod_univ_succ,
    Fin.castSucc_zero, Fin.cons_zero,
    Fin.castSucc_succ, Fin.cons_succ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Fintype.sum_bool]
  cases s 0 <;> simp [pieriSelect, pieriBinaryStep] <;> ring

def pieriLeftMatrix (z : R) (e : PieriEdge R) (s t : Bool) : R :=
  if t then (if s then z * e.Y else z * (1 - e.c) * e.X)
  else (if s then e.c * e.X + e.Y else e.X)

def pieriRightMatrix (z cp : R) (e : PieriEdge R) (s t : Bool) : R :=
  if t then (if s then z * e.Y else (1 - cp * e.beta) * z * e.Y) else e.X

theorem pieriBinaryStep_left (z : R) (e : PieriEdge R) (v : R × R) :
    pieriBinaryStep (pieriLeftMatrix z e) v = pieriLeftStep z e.c e.X e.Y v := by
  apply Prod.ext
  · rfl
  · dsimp [pieriBinaryStep, pieriLeftMatrix, pieriLeftStep]
    ring

theorem pieriBinaryStep_right (z cp : R) (e : PieriEdge R) (v : R × R) :
    pieriBinaryStep (pieriRightMatrix z cp e) v =
      pieriRightStep z cp e.beta e.X e.Y v := by
  ext <;> simp [pieriBinaryStep, pieriRightMatrix, pieriRightStep] <;> ring

/-- The right matrices remember the c-entry of the preceding edge. -/
def pieriRightArray (z : R) : (n : ℕ) → R → (Fin n → PieriEdge R) →
    Fin n → Bool → Bool → R
  | 0, _, _ => Fin.elim0
  | n + 1, cp, e =>
      Fin.cons (pieriRightMatrix z cp (e 0))
        (pieriRightArray z n (e 0).c (fun i => e i.succ))

theorem pieriPathSum_left_run (z : R) (n : ℕ) (e : Fin n → PieriEdge R) (v : R × R) :
    pieriPathSum (fun i => pieriLeftMatrix z (e i)) v =
      (pieriLeftRun z (List.ofFn e) v).1 + (pieriLeftRun z (List.ofFn e) v).2 := by
  induction n generalizing v with
  | zero => simp [pieriPathSum_zero, pieriLeftRun]
  | succ n ih =>
      rw [pieriPathSum_succ, pieriBinaryStep_left, List.ofFn_succ]
      exact ih (fun i => e i.succ) _

theorem pieriPathSum_right_run (z : R) (n : ℕ) (cp : R) (e : Fin n → PieriEdge R)
    (v : R × R) :
    pieriPathSum (pieriRightArray z n cp e) v =
      (pieriRightRun z cp (List.ofFn e) v).1 +
        (pieriRightRun z cp (List.ofFn e) v).2 := by
  induction n generalizing cp v with
  | zero => simp [pieriPathSum_zero, pieriRightRun]
  | succ n ih =>
      rw [pieriPathSum_succ, List.ofFn_succ]
      simp only [pieriRightArray, Fin.cons_zero, Fin.cons_succ, pieriBinaryStep_right,
        pieriRightRun]
      exact ih (e 0).c (fun i => e i.succ) _

theorem pieriRightArray_adjacent (z : R) (n : ℕ) (e : Fin (n + 1) → PieriEdge R) :
    pieriRightArray z n (e 0).c (fun i => e i.succ) =
      fun i => pieriRightMatrix z (e i.castSucc).c (e i.succ) := by
  induction n with
  | zero => exact funext fun i => Fin.elim0 i
  | succ n ih =>
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          exact congrFun (ih (fun j => e j.succ)) i

/-- E-step as an equality of finite path sums, before substituting Gaussian entries. -/
theorem pieri_transfer_binary (z : R) (n : ℕ) (e : Fin (n + 1) → PieriEdge R) :
    (∑ s : Fin (n + 2) → Bool, pieriSelect (1, z) (s 0) *
      ∏ i : Fin (n + 1), pieriLeftMatrix z (e i) (s i.castSucc) (s i.succ)) =
    (1 + z) * ∑ t : Fin (n + 1) → Bool, pieriSelect ((e 0).X, z * (e 0).Y) (t 0) *
      ∏ i : Fin n, pieriRightMatrix z (e i.castSucc).c (e i.succ)
        (t i.castSucc) (t i.succ) := by
  change pieriPathSum (fun i => pieriLeftMatrix z (e i)) (1, z) =
    (1 + z) * pieriPathSum
      (fun i => pieriRightMatrix z (e i.castSucc).c (e i.succ)) _
  rw [← pieriRightArray_adjacent, pieriPathSum_left_run, pieriPathSum_right_run,
    List.ofFn_succ]
  exact pieri_transfer_chain z (e 0) (List.ofFn fun i => e i.succ)

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.pieriPathSum_succ
#print axioms VOA.DeligneAudit.D4Char.pieriPathSum_left_run
#print axioms VOA.DeligneAudit.D4Char.pieriPathSum_right_run
#print axioms VOA.DeligneAudit.D4Char.pieriRightArray_adjacent
#print axioms VOA.DeligneAudit.D4Char.pieri_transfer_binary
