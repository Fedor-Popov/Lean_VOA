import Mathlib.Data.List.Sort
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.FinRange

/-! # Efficient enumeration of bounded words avoiding leading divisors

The recursion prunes a branch as soon as its stem contains a leading word.
Completeness is symbolic and does not rely on a list-cardinality experiment.
-/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate

def Avoids (leaders : List (List (Fin 18))) (w : List (Fin 18)) : Prop :=
  leaders.Forall fun l => ¬ l.Subperm w

instance (leaders : List (List (Fin 18))) (w : List (Fin 18)) : Decidable (Avoids leaders w) :=
  inferInstanceAs (Decidable (leaders.Forall fun l => ¬ l.Subperm w))

theorem avoids_iff (leaders : List (List (Fin 18))) (w : List (Fin 18)) :
    Avoids leaders w ↔ ∀ l ∈ leaders, ¬ l.Subperm w := List.forall_iff_forall_mem

theorem avoids_mono {leaders : List (List (Fin 18))} {a b : List (Fin 18)}
    (h : a.Subperm b) (hb : Avoids leaders b) : Avoids leaders a := by
  rw [avoids_iff] at hb ⊢
  intro l hl hla
  exact hb l hl (hla.trans h)

def enumerateFrom (leaders : List (List (Fin 18))) :
    ℕ → ℕ → List (Fin 18) → List (List (Fin 18))
  | 0, _, stem => [stem]
  | fuel+1, lower, stem => stem :: (List.finRange 18).flatMap fun v =>
      if lower ≤ v.val ∧ Avoids leaders (stem ++ [v]) then
        enumerateFrom leaders fuel v.val (stem ++ [v]) else []

theorem enumerateFrom_length (leaders : List (List (Fin 18))) (fuel lower : ℕ)
    (stem : List (Fin 18)) :
    (enumerateFrom leaders (fuel+1) lower stem).length =
      1 + ((List.finRange 18).map fun v =>
        if lower ≤ v.val ∧ Avoids leaders (stem ++ [v]) then
          (enumerateFrom leaders fuel v.val (stem ++ [v])).length else 0).sum := by
  rw [enumerateFrom,List.length_cons,List.length_flatMap,Nat.add_comm]
  apply congrArg (fun n : ℕ => 1+n)
  apply congrArg List.sum
  apply List.map_congr_left
  intro v _
  split_ifs <;> rfl

/-- Opaque child counts assemble one recursion level without recomputing subtrees. -/
theorem enumerateFrom_length_of_flags (leaders : List (List (Fin 18)))
    (fuel lower : ℕ) (stem : List (Fin 18)) (flags : Fin 18 → Bool)
    (counts : Fin 18 → ℕ)
    (hflags : ∀ v, (lower ≤ v.val ∧ Avoids leaders (stem ++ [v])) ↔ flags v = true)
    (hcounts : ∀ v, flags v = true →
      (enumerateFrom leaders fuel v.val (stem ++ [v])).length = counts v)
    (hzero : ∀ v, flags v ≠ true → counts v = 0) :
    (enumerateFrom leaders (fuel+1) lower stem).length =
      1 + ((List.finRange 18).map counts).sum := by
  rw [enumerateFrom_length]
  apply congrArg (fun n : ℕ => 1+n)
  apply congrArg List.sum
  apply List.map_congr_left
  intro v _
  by_cases h : flags v = true
  · rw [if_pos ((hflags v).mpr h)]
    exact hcounts v h
  · rw [if_neg (fun hc => h ((hflags v).mp hc)),hzero v h]

theorem mem_enumerateFrom (leaders : List (List (Fin 18))) (fuel : ℕ)
    (lower : ℕ) (stem w : List (Fin 18)) (hlen : w.length ≤ fuel)
    (hsorted : w.Pairwise (· ≤ ·)) (hlower : ∀ v ∈ w, lower ≤ v.val)
    (ha : Avoids leaders (stem ++ w)) :
    stem ++ w ∈ enumerateFrom leaders fuel lower stem := by
  induction fuel generalizing lower stem w with
  | zero =>
      have hw : w = [] := List.length_eq_zero_iff.mp (by omega)
      subst w
      simp [enumerateFrom]
  | succ fuel ih =>
      cases w with
      | nil => simp [enumerateFrom]
      | cons v w =>
          have hs := List.pairwise_cons.mp hsorted
          have hp : (stem ++ [v]).Subperm (stem ++ v::w) :=
            (List.Subperm.refl stem).append (List.prefix_append [v] w).sublist.subperm
          have hva := avoids_mono hp ha
          have hv : lower ≤ v.val ∧ Avoids leaders (stem ++ [v]) :=
            ⟨hlower v (List.mem_cons_self),hva⟩
          apply List.mem_cons_of_mem
          apply List.mem_flatMap.mpr
          refine ⟨v,by simp,?_⟩
          rw [if_pos hv]
          have hrec := ih v.val (stem ++ [v]) w (by simpa using hlen) hs.2
            (fun x hx => hs.1 x hx)
            (by simpa only [List.append_assoc,List.singleton_append] using ha)
          simpa only [List.append_assoc,List.singleton_append] using hrec

def normalWords (leaders : List (List (Fin 18))) (d : ℕ) : List (List (Fin 18)) :=
  enumerateFrom leaders d 0 []

theorem mem_normalWords_of_sorted (leaders : List (List (Fin 18))) (d : ℕ)
    (w : List (Fin 18)) (hlen : w.length ≤ d) (hsorted : w.Pairwise (· ≤ ·))
    (ha : Avoids leaders w) : w ∈ normalWords leaders d := by
  simpa only [normalWords,List.nil_append] using
    mem_enumerateFrom leaders d 0 [] w hlen hsorted (fun _ _ => Nat.zero_le _) ha

end VOA.DeligneAudit.D4FusionContact.M2Certificate

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.mem_normalWords_of_sorted
