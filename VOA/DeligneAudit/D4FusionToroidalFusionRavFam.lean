import VOA.DeligneAudit.D4FusionToroidalFusionGrRelations
import VOA.DeligneAudit.D4FusionToroidalGr
import VOA.DeligneAudit.D4FusionKernelGeneric

/-!
# The Ravinder-family source relations on toroidal symbols

Each current mode `r` in `ravFam S m 0` is interpreted as the toroidal
letter `(r / m, r % m)`. The checked highest-vector relations imply the
entire tail and eigenrelation specification for positive site count.
-/

namespace VOA.DeligneAudit.Toroidal.FusionGr

open VOA.DeligneAudit.Toroidal VOA.DeligneAudit.D1TensorG
open VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.UnivG

noncomputable section

variable (S : DeligneSectorData)
variable (hskew : ∀ a b c, S.f a b c = -S.f b a c)
variable {m : ℕ} (z : Fin m → ℂ)

private def M : ToroidalModule S.f m
    (Gr (d1EvalAction S.f S.jacobi hskew z) (D1TensorG.generator S.c₀)) :=
  evalGrToroidal (fun _ => D1SiteG.rep S.f S.jacobi hskew) z
    (D1TensorG.generator S.c₀)

theorem symbolLetters_replicate_zero (x : Fin S.n) (k : ℕ) :
    symbolLetters m (List.replicate k (x, 0)) =
      List.replicate k (x, 0, 0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [List.replicate_succ, symbolLetters, ih, Nat.zero_div,
        Nat.zero_mod]

theorem wordOpT_replicate_zero (x : Fin S.n) (k : ℕ)
    (v : Gr (d1EvalAction S.f S.jacobi hskew z) (D1TensorG.generator S.c₀)) :
    wordOpT (M S hskew z) (List.replicate k (x, 0, 0)) v =
      (((M S hskew z).op x 0 0) ^ k) v := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [List.replicate_succ, wordOpT, ih]
      rw [pow_succ', Module.End.mul_apply]

/-- The symbols of every `ravFam S m 0` tail kill the toroidal highest vector. -/
theorem ravFam_symbol_tail (hm : 0 < m) (t : List (Ltr S.n))
    (ht : t ∈ (ravFam S m 0).tails) :
    wordOpT (M S hskew z) (symbolLetters m t) (highest S hskew z) = 0 := by
  simp only [ravFam, ravSpec, Set.mem_setOf_eq] at ht
  rcases ht with ⟨e, r, he, rfl⟩ | ⟨h, r, hh, hr, rfl⟩ |
    ⟨x, hx, rfl⟩ | ⟨x, _, rfl⟩ | ⟨h, r, hh, hr, rfl⟩
  · change grOp _ _ m e (r / m) (r % m) (highest S hskew z) = 0
    exact highest_raising S hskew z e he (r / m) (r % m)
  · change grOp _ _ m h (r / m) (r % m) (highest S hskew z) = 0
    by_cases hi : 1 ≤ r / m
    · exact highest_cartan_u S hskew z h hh (r / m) (r % m) hi
    · have hq : r / m = 0 := Nat.lt_one_iff.mp (lt_of_not_ge hi)
      have hs : 1 ≤ r % m := by
        have hdiv := Nat.mod_add_div r m
        simp only [hq, mul_zero, add_zero] at hdiv
        omega
      rw [hq]
      exact highest_cartan_t S hskew z h hh (r % m) hs
  · simp only [Nat.add_zero, symbolLetters_replicate_zero]
    rw [wordOpT_replicate_zero]
    change ((grOp _ _ m x 0 0) ^ (m * S.lowExp x + 1))
      (highest S hskew z) = 0
    exact highest_lowering S hskew z x hx hm
  · by_cases hx : x = S.c₀
    · subst x
      have hq : (2 * m + 0) / m = 2 := by
        rw [Nat.add_zero, mul_comm, Nat.mul_div_cancel_left 2 hm]
      have hr : (2 * m + 0) % m = 0 := by simp
      simp only [symbolLetters, wordOpT]
      change grOp _ _ m S.c₀ ((2 * m + 0) / m) ((2 * m + 0) % m)
        (highest S hskew z) = 0
      rw [hq, hr]
      exact highest_u_two S hskew z S.c₀ 0
    · have hq : (m + 0) / m = 1 := by simpa using Nat.div_self hm
      have hr : (m + 0) % m = 0 := by simp
      simp only [symbolLetters, wordOpT, if_neg hx]
      change grOp _ _ m x ((m + 0) / m) ((m + 0) % m)
        (highest S hskew z) = 0
      rw [hq, hr]
      exact highest_fusion_one S hskew z x hx 0
  · change grOp _ _ m h (r / m) (r % m) (highest S hskew z) = 0
    by_cases hi : 1 ≤ r / m
    · exact highest_cartanN_u S hskew z h hh (r / m) (r % m) hi
    · have hq : r / m = 0 := Nat.lt_one_iff.mp (lt_of_not_ge hi)
      have hs : 1 ≤ r % m := by
        have hdiv := Nat.mod_add_div r m
        simp only [hq, mul_zero, add_zero] at hdiv
        omega
      rw [hq]
      exact highest_cartanN_t S hskew z h hh (r % m) hs

/-- The eigenrelations of `ravFam S m 0` hold on the toroidal symbol. -/
theorem ravFam_symbol_eig (hm : 0 < m) (q : Fin S.n × ℂ)
    (hq : q ∈ (ravFam S m 0).eig) :
    (M S hskew z).op q.1 0 0 (highest S hskew z) =
      q.2 • highest S hskew z := by
  simp only [ravFam, ravSpec, Set.mem_setOf_eq] at hq
  rcases hq with ⟨h, hh, rfl⟩ | ⟨h, hh, rfl⟩
  · simpa only [Nat.add_zero] using highest_cartan_zero S hskew z h hh hm
  · simpa only [Nat.add_zero] using highest_cartanN_zero S hskew z h hh hm

end

end VOA.DeligneAudit.Toroidal.FusionGr

#print axioms VOA.DeligneAudit.Toroidal.FusionGr.ravFam_symbol_tail
#print axioms VOA.DeligneAudit.Toroidal.FusionGr.ravFam_symbol_eig
