import VOA.DeligneAudit.DeligneFusionCVBound

/-!
# A short CV presentation for partitions with parts at most three

For positive parts at most three, the full CV family follows from the
zero-mode nilpotence, the linear truncation, and the quadratic coefficient
relations. Multiplicities at least three are already in Garland's vanishing
region. No dimension bound or fusion-product identification is assumed.
-/

namespace VOA.DeligneAudit.CVPart

/-- Clipping each part at `m` gives a lower bound for every CV region. -/
theorem clipped_sum_le_region (ξ : List ℕ) (m k : ℕ) :
    (ξ.map (fun a => min m a)).sum ≤ m * k + T k ξ := by
  induction ξ generalizing k with
  | nil => simp [T]
  | cons a ξ ih =>
      cases k with
      | zero =>
          have htail := ih 0
          have ha := Nat.min_le_right m a
          simp only [Nat.mul_zero, zero_add, T, List.drop_zero] at htail ⊢
          simp only [List.map_cons, List.sum_cons]
          omega
      | succ k =>
          have htail := ih k
          have ha := Nat.min_le_left m a
          simp only [T] at htail
          simp only [List.map_cons, List.sum_cons, T, List.drop_succ_cons, Nat.mul_succ]
          omega

/-- Clipping positive parts at one counts the parts. -/
theorem clipped_sum_one (ξ : List ℕ) (hpos : ∀ a ∈ ξ, 1 ≤ a) :
    (ξ.map (fun a => min 1 a)).sum = ξ.length := by
  induction ξ with
  | nil => simp
  | cons a ξ ih =>
      have ha := hpos a List.mem_cons_self
      have hp : ∀ b ∈ ξ, 1 ≤ b := fun b hb => hpos b (List.mem_cons_of_mem a hb)
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.min_eq_left ha, ih hp]
      omega

/-- Clipping above every part preserves the total weight. -/
theorem clipped_sum_of_bound (ξ : List ℕ) (m : ℕ) (hle : ∀ a ∈ ξ, a ≤ m) :
    (ξ.map (fun a => min m a)).sum = ξ.sum := by
  induction ξ with
  | nil => simp
  | cons a ξ ih =>
      have ha := hle a List.mem_cons_self
      have ht : ∀ b ∈ ξ, b ≤ m := fun b hb => hle b (List.mem_cons_of_mem a hb)
      simp only [List.map_cons, List.sum_cons, Nat.min_eq_right ha, ih ht]

end VOA.DeligneAudit.CVPart

namespace VOA.DeligneAudit.CVsl2

open VOA.DeligneAudit.CVPart

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {E H F : ℕ → Module.End ℂ V} {y : V}

/-- For positive parts at most three, only the linear and quadratic CV
coefficients need be checked beyond the usual highest-weight nilpotence. -/
theorem cvrel_of_le_three (ξ : List ℕ)
    (hpos : ∀ a ∈ ξ, 1 ≤ a) (hle : ∀ a ∈ ξ, a ≤ 3)
    (hS : SL2 E H F) (hE : ∀ s, E s y = 0)
    (hH : ∀ p, 1 ≤ p → H p y = 0)
    (hnil : (F 0 ^ (ξ.sum + 1)) y = 0)
    (hlin : ∀ q, ξ.length ≤ q → F q y = 0)
    (hquad : ∀ s, 1 + (ξ.map (fun a => min 2 a)).sum ≤ s + 2 → Q F 2 s y = 0) :
    CVRel F ξ y := by
  intro m s k hm hreg
  have hclip := clipped_sum_le_region ξ m k
  by_cases hm1 : m = 1
  · subst m
    rw [clipped_sum_one ξ hpos] at hclip
    rw [Q_one]
    exact hlin s (by omega)
  by_cases hm2 : m = 2
  · subst m
    exact hquad s (by omega)
  have hm3 : 3 ≤ m := by omega
  rw [clipped_sum_of_bound ξ m (fun a ha => (hle a ha).trans hm3)] at hclip
  have hEF' : ∀ q, E 1 * F q - F q * E 1 = H (q + 1) :=
    fun q => by rw [hS.hEF 1 q, add_comm]
  exact Garland.garland hEF' (fun p q => hS.hHF (p + 1) q) hS.hFF (hE 1)
    (fun p => hH (p + 1) (by omega)) m hm hnil s (by omega)

/-- The three-level partition used in the enlarged A₂ CV family has a finite
short presentation. The list is explicit so this theorem has no dependency
on a universal-module family definition. -/
theorem cvrel_parts123 (r n e : ℕ)
    (hS : SL2 E H F) (hE : ∀ s, E s y = 0)
    (hH : ∀ p, 1 ≤ p → H p y = 0)
    (hnil : (F 0 ^ (3 * r + 2 * n + e + 1)) y = 0)
    (hlin : ∀ q, r + n + e ≤ q → F q y = 0)
    (hquad : ∀ s, 1 + 2 * (r + n) + e ≤ s + 2 → Q F 2 s y = 0) :
    CVRel F (List.replicate r 3 ++ List.replicate n 2 ++ List.replicate e 1) y := by
  refine cvrel_of_le_three _ ?_ ?_ hS hE hH ?_ ?_ ?_
  · intro a ha
    simp only [List.mem_append, List.mem_replicate] at ha
    omega
  · intro a ha
    simp only [List.mem_append, List.mem_replicate] at ha
    omega
  · simpa [List.sum_append, List.sum_replicate, mul_comm, add_assoc] using hnil
  · simpa [List.length_append, List.length_replicate, add_assoc] using hlin
  · intro s hs
    apply hquad s
    have heq : ((List.replicate r 3 ++ List.replicate n 2 ++ List.replicate e 1).map
        (fun a => min 2 a)).sum = 2 * (r + n) + e := by
      simp [List.map_append, List.map_replicate, List.sum_replicate]
      omega
    rw [heq] at hs
    omega

/-- With exactly one trailing part one, the sole quadratic relation not
already forced by the linear truncation is the square of the final mode.
This is the highest-root target partition of the first A₂ kernel generator. -/
theorem cvrel_parts32_one (r n : ℕ)
    (hS : SL2 E H F) (hE : ∀ s, E s y = 0)
    (hH : ∀ p, 1 ≤ p → H p y = 0)
    (hnil : (F 0 ^ (3 * r + 2 * n + 2)) y = 0)
    (hlin : ∀ q, r + n + 1 ≤ q → F q y = 0)
    (hsquare : (F (r + n) ^ 2) y = 0) :
    CVRel F (List.replicate r 3 ++ List.replicate n 2 ++ [1]) y := by
  have hR := cvrel_parts123 r n 1 hS hE hH hnil hlin (fun s hs => ?_)
  · simpa only [List.replicate_one] using hR
  have hslo : 2 * (r + n) ≤ s := by omega
  by_cases heq : s = 2 * (r + n)
  · subst s
    have ht := Q_top hS.hFF hlin 2
    have ht' : Q F 2 (2 * (r + n)) y = (F (r + n) ^ 2) y := by
      simpa only [Nat.add_sub_cancel_right, mul_comm] using ht
    exact ht'.trans hsquare
  · exact Q_high hS.hFF hlin 2 s
      (by simpa only [Nat.add_sub_cancel_right, mul_comm] using
        (show 2 * (r + n) < s by omega))

end

end VOA.DeligneAudit.CVsl2

#print axioms VOA.DeligneAudit.CVsl2.cvrel_of_le_three
#print axioms VOA.DeligneAudit.CVsl2.cvrel_parts123
#print axioms VOA.DeligneAudit.CVsl2.cvrel_parts32_one
