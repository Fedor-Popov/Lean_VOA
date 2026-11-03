import VOA.DeligneAudit.D4FusionToroidalPresentedTwoSeedRoots

/-! Nilpotence for lowering actions on the quadratic seed. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.D4FusionContact

noncomputable section

private abbrev G := (ρPTE 2).op D4sector.c₀ 1 0
private abbrev F (i : Fin 12) := (ρPTE 2).op (negativeIndex i) 0 0
private abbrev Y (i : Fin 12) (s : ℕ) := (ρPTE 2).op (negativeIndex i) 0 s

private theorem negative_theta_zero : ∀ i : Fin 12, ∀ e : Fin 28,
    fZ br (negativeIndex i) 27 e = 0 := by
  decide +kernel

private theorem negative_self_zero : ∀ i : Fin 12, ∀ e : Fin 28,
    fZ br (negativeIndex i) (negativeIndex i) e = 0 := by
  decide +kernel

private theorem simple_negative_index : ∀ i : Fin 12,
    i.val < 4 → (negativeIndex i).val < 20 := by
  decide +kernel

theorem two_seed_lowering_commG (i : Fin 12) (s : ℕ) (_hs : s ≤ 1)
    (x : PTE 2) : Y i s (G x) = G (Y i s x) := by
  have h := (ρPTE 2).comm (negativeIndex i) D4sector.c₀ 0 1 s 0 x
  have hf : ∀ e : Fin 28, D4sector.f (negativeIndex i) D4sector.c₀ e = 0 := by
    intro e
    change (fZ br (negativeIndex i) 27 e : ℂ) = 0
    rw [negative_theta_zero]
    simp
  simp only [hf, zero_smul, Finset.sum_const_zero, ite_self] at h
  exact sub_eq_zero.mp h

theorem two_seed_lowering_comm_self (i : Fin 12) (s : ℕ) (_hs : s ≤ 1)
    (x : PTE 2) : F i (Y i s x) = Y i s (F i x) := by
  have h := (ρPTE 2).comm (negativeIndex i) (negativeIndex i) 0 0 0 s x
  have hf : ∀ e : Fin 28,
      D4sector.f (negativeIndex i) (negativeIndex i) e = 0 := by
    intro e
    change (fZ br (negativeIndex i) (negativeIndex i) e : ℂ) = 0
    rw [negative_self_zero]
    simp
  simp only [hf, zero_smul, Finset.sum_const_zero, ite_self] at h
  exact sub_eq_zero.mp h

private theorem commute_iter {A B : PTE 2 →ₗ[ℂ] PTE 2}
    (h : ∀ x, A (B x) = B (A x)) (n : ℕ) (x : PTE 2) :
    A^[n] (B x) = B (A^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, h, Function.iterate_succ_apply']

theorem two_seed_lowering_v_nil (i : Fin 12) (hi : i.val < 4) :
    (F i)^[2 * D4sector.lowExp (negativeIndex i) + 1] (pTE 2) = 0 := by
  let N := 2 * D4sector.lowExp (negativeIndex i) + 1
  have ht : List.replicate N (negativeIndex i, 0) ∈
      (ravFam D4sector 2 0).tails := by
    change List.replicate N (negativeIndex i, 0) ∈ (ravSpec D4sector 2 4).tails
    exact Or.inr (Or.inr (Or.inl ⟨negativeIndex i,
      (show D4sector.lowering (negativeIndex i) from
        ⟨negativeIndex_range i, simple_negative_index i hi⟩), rfl⟩))
  have h := two_syntax_tail (List.replicate N (negativeIndex i, 0)) ht
  have hs : symbolLetters 2 (List.replicate N (negativeIndex i, 0)) =
      List.replicate N (negativeIndex i, 0, 0) := by
    induction N with
    | zero => rfl
    | succ n ih => simp only [List.replicate_succ, symbolLetters, ih,
        Nat.zero_div, Nat.zero_mod]
  have h' : wordOpT (ρPTE 2)
      (List.replicate N (negativeIndex i, 0, 0)) (pTE 2) = 0 := by
    calc
      _ = wordOpT (ρPTE 2)
          (symbolLetters 2 (List.replicate N (negativeIndex i, 0))) (pTE 2) :=
            congrArg (fun w => wordOpT (ρPTE 2) w (pTE 2)) hs.symm
      _ = 0 := h
  have hw : ∀ n : ℕ,
      wordOpT (ρPTE 2) (List.replicate n (negativeIndex i, 0, 0)) (pTE 2) =
        (F i)^[n] (pTE 2) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [List.replicate_succ, wordOpT, ih,
          Function.iterate_succ_apply', F]
  exact (hw N).symm.trans h'

theorem two_seed_lowering_nil (i : Fin 12) (hi : i.val < 4)
    (s : ℕ) (hs : s ≤ 1) :
    ∃ N : ℕ, (F i)^[N] (Y i s twoQuadraticSeed) = 0 := by
  let N := 2 * D4sector.lowExp (negativeIndex i) + 1
  have hFG (x : PTE 2) : F i (G x) = G (F i x) :=
    two_seed_lowering_commG i 0 (by omega) x
  have hFY (x : PTE 2) : F i (Y i s x) = Y i s (F i x) :=
    two_seed_lowering_comm_self i s hs x
  have hGY (x : PTE 2) : Y i s (G x) = G (Y i s x) :=
    two_seed_lowering_commG i s hs x
  have haction : Y i s twoQuadraticSeed = G (G (Y i s (pTE 2))) := by
    change Y i s (G (G (pTE 2))) = _
    rw [hGY, hGY]
  refine ⟨N, ?_⟩
  rw [haction, commute_iter hFG, commute_iter hFG, commute_iter hFY]
  have hv : (F i)^[N] (pTE 2) = 0 := two_seed_lowering_v_nil i hi
  rw [hv, map_zero, map_zero, map_zero]

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_seed_lowering_commG
#print axioms VOA.DeligneAudit.Toroidal.two_seed_lowering_comm_self
#print axioms VOA.DeligneAudit.Toroidal.two_seed_lowering_v_nil
#print axioms VOA.DeligneAudit.Toroidal.two_seed_lowering_nil
