import VOA.DeligneAudit.DeligneFusionCVUniv
import VOA.DeligneAudit.DeligneFusionCVKernelHW

/-!
# Finite current-degree pieces of the actual auxiliary CV modules

The PBW and bounded-word argument needs a common nilpotence bound for the
three zero-mode lowering operators, rather than equal simple-root weights.
Full CV relations supply those powers for every auxiliary highest weight.
There is no fusion dimension bound or KR presentation premise here.
-/

namespace VOA.DeligneAudit.A2.CVFinite

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.A2.CVFamily
open VOA.DeligneAudit.A2.CVUniv VOA.DeligneAudit.A2.CVKernelHW

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {ρ : CurrentModule bracketTable V} {w : V} {ε ν ϱ : Weight} {j : ℕ}

local notation "deg" => VOA.DeligneAudit.SectorGraded.wordDeg

/-- A common zero-mode nilpotence exponent, valid for all three lowering roots. -/
def nilBound (ε ν ϱ : Weight) (j : ℕ) : ℕ := lambda1 ε ν ϱ j + lambda2 ε ν ϱ j + 1

/-- The actual rootwise CV relations give the common lowering nilpotence bound. -/
theorem lowering_nil (h : CV3Rel ρ w ε ν ϱ j) (c : Fin 8)
    (hc : 3 ≤ c.val ∧ c.val < 6) :
    (ρ.op c 0 ^ nilBound ε ν ϱ j) w = 0 := by
  have hc' : c = 3 ∨ c = 4 ∨ c = 5 := by omega
  rcases hc' with rfl | rfl | rfl
  · have hn := cvrel_zero_nil h.first
    rw [parts_sum] at hn
    exact pow_kill_wordOp_le 3 hc hn []
      (by simp only [List.length_nil, Nat.mul_zero, Nat.zero_add];
          dsimp only [nilBound, lambda1, lambda2]; omega)
  · have hn := cvrel_zero_nil h.second
    rw [parts_sum] at hn
    exact pow_kill_wordOp_le 4 hc hn []
      (by simp only [List.length_nil, Nat.mul_zero, Nat.zero_add];
          dsimp only [nilBound, lambda1, lambda2]; omega)
  · have hn := cvrel_zero_nil h.highest
    rw [parts_sum] at hn
    exact pow_kill_wordOp_le 5 hc hn []
      (by simp only [List.length_nil, Nat.mul_zero, Nat.zero_add];
          dsimp only [nilBound, lambda1, lambda2]; omega)

/-- PBW sorting needs only highest-weight and Cartan data, also for unequal weights. -/
theorem cycDeg_le_sortedFin_of_cv3Rel (h : CV3Rel ρ w ε ν ϱ j) (b : ℕ) :
    cycDeg ρ w b ≤ Submodule.span ℂ {u | ∃ l : List (Fin 8 × ℕ),
      l.IsChain (fun a c => keyFin a ≤ keyFin c) ∧ (∀ x ∈ l, lowSl3 x.1) ∧ deg l = b ∧
        u = wordOp ρ l w} := by
  have hw : ∀ (a : Fin 8) r, ¬ lowSl3 a →
      ρ.op a r w ∈ ℂ ∙ w ∧ (1 ≤ r → ρ.op a r w = 0) := by
    intro a r ha
    unfold lowSl3 at ha
    by_cases h3 : a.val < 3
    · rw [h.raising a h3 r]
      exact ⟨Submodule.zero_mem _, fun _ => rfl⟩
    · have h6 : 6 ≤ a.val := by omega
      refine ⟨?_, fun hr => h.cartan_pos a h6 r hr⟩
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · have ha' : a = 6 ∨ a = 7 := by omega
        rcases ha' with rfl | rfl
        · rw [h.cartan_first]
          exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
        · rw [h.cartan_second]
          exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
      · rw [h.cartan_pos a h6 r hr]
        exact Submodule.zero_mem _
  exact cycDeg_le_sortedLow keyFin lowSl3 ρ keyFin_low hw b

/-- The bounded sorted-word argument applies to any common zero-mode nilpotence exponent.
The existing `Gr N0` recurrence deliberately overestimates the constant term. -/
theorem length_le_of_lower_nil {N0 : ℕ}
    (hNil : ∀ c : Fin 8, 3 ≤ c.val ∧ c.val < 6 → (ρ.op c 0 ^ N0) w = 0) :
    ∀ n (l : List (Fin 8 × ℕ)), l.length = n → l.Pairwise (fun a c => keyFin a ≤ keyFin c) →
      (∀ x ∈ l, lowSl3 x.1) → wordOp ρ l w ≠ 0 → l.length ≤ Gr N0 (deg l) (tcount l) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hn hs hlow hne
  match l, hs, hlow, hne with
  | [], _, _, _ => exact Nat.zero_le _
  | (x :: rest), hs, hlow, hne =>
    by_cases hx0 : x.2 = 0
    · -- run decomposition
      set p : Fin 8 × ℕ → Bool := fun y => decide (y = x) with hp
      set T := List.takeWhile p (x :: rest) with hT
      set D := List.dropWhile p (x :: rest) with hD
      have hTD : T ++ D = x :: rest := List.takeWhile_append_dropWhile
      have hTrep : T = List.replicate T.length x :=
        List.eq_replicate_iff.mpr ⟨rfl, fun y hy => by
          have := List.all_eq_true.mp (List.all_takeWhile (p := p) (l := x :: rest)) y hy
          simpa [hp] using this⟩
      have hTlen : 1 ≤ T.length := by
        rw [hT, List.takeWhile_cons_of_pos (by simp [hp])]; simp
      have hpw : (T ++ D).Pairwise (fun a c => keyFin a ≤ keyFin c) := hTD ▸ hs
      rw [List.pairwise_append] at hpw
      have hxT : x ∈ T := by
        rw [hTrep]; exact List.mem_replicate.mpr ⟨by omega, rfl⟩
      have hxD : x ∉ D := by
        intro hxD
        cases hDc : D with
        | nil => rw [hDc] at hxD; simp at hxD
        | cons y D' =>
          have hy : p y = false := by
            have := List.head_dropWhile_not p (l := x :: rest) (by rw [← hD, hDc]; simp)
            simpa [← hD, hDc] using this
          have hyx : y ≠ x := by simpa [hp] using hy
          rw [hDc] at hxD
          rcases List.mem_cons.mp hxD with h | h
          · exact hyx h.symm
          · have h1 := hpw.2.2 x hxT y (by rw [hDc]; exact List.mem_cons_self)
            have h2 := (List.pairwise_cons.mp (hDc ▸ hpw.2.1)).1 x h
            exact hyx (keyFin_inj (le_antisymm h2 h1))
      have hDsub : ∀ z ∈ D, z ∈ x :: rest := fun z hz => hTD ▸ List.mem_append_right T hz
      have hlen : (x :: rest).length = T.length + D.length := by rw [← hTD, List.length_append]
      have hword : wordOp ρ (x :: rest) w = (ρ.op x.1 0 ^ T.length) (wordOp ρ D w) := by
        rw [← hTD, wordOp_append, hTrep, ← iterate_eq_wordOp ρ x, hx0, Module.End.pow_apply,
          List.length_replicate]
      have hc : 3 ≤ x.1.val ∧ x.1.val < 6 := hlow x List.mem_cons_self
      have hDne : wordOp ρ D w ≠ 0 := by
        intro h0; apply hne; rw [hword, h0, map_zero]
      have hr : T.length < 2 * D.length + N0 := by
        by_contra hcon
        exact hne (hword ▸ pow_kill_wordOp_le x.1 hc (hNil x.1 hc) D (by omega))
      have hIH := ih D.length (by omega) D rfl hpw.2.1 (fun z hz => hlow z (hDsub z hz)) hDne
      have hdeg : deg D = deg (x :: rest) := by
        rw [← hTD, deg_append', hTrep, show x = (x.1, 0) from Prod.ext rfl hx0, deg_replicate_zero,
          zero_add]
      have ht : tcount D + 1 ≤ tcount (x :: rest) := by
        unfold tcount
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_of_subset (fun c hc' => ?_) |>.mpr ⟨x.1, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc' ⊢; exact hDsub _ hc'
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [show (x.1, 0) = x from Prod.ext rfl hx0.symm]; exact List.mem_cons_self
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [show (x.1, 0) = x from Prod.ext rfl hx0.symm]; exact hxD
      rw [hdeg] at hIH
      have hmono := Gr_mono N0 (deg (x :: rest)) ht
      simp only [Gr] at hmono
      omega
    · -- all letters have positive grade
      have hpos : ∀ y ∈ x :: rest, y.2 ≠ 0 := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx0
        · intro hy0
          have h1 := (List.pairwise_cons.mp hs).1 y hy
          exact absurd h1 (not_le.mpr (keyFin_zero_lt (hlow y (List.mem_cons_of_mem _ hy))
            (hlow x List.mem_cons_self) hy0 hx0))
      exact (len_le_deg _ hpos).trans (Gr_mono N0 _ (Nat.zero_le _))


/-- Every exact current-degree piece of an actual auxiliary CV cyclic module is finite. -/
theorem finiteDimensional_cycDeg_of_cv3Rel (h : CV3Rel ρ w ε ν ϱ j) (b : ℕ) :
    FiniteDimensional ℂ (cycDeg ρ w b) := by
  haveI : Trans (fun a c : Fin 8 × ℕ => keyFin a ≤ keyFin c)
      (fun a c : Fin 8 × ℕ => keyFin a ≤ keyFin c)
      (fun a c : Fin 8 × ℕ => keyFin a ≤ keyFin c) :=
    ⟨fun h1 h2 => le_trans h1 h2⟩
  let N0 := nilBound ε ν ϱ j
  set S := {l : List (Fin 8 × ℕ) | l.length ≤ Gr N0 b 8 ∧ ∀ x ∈ l, x.2 ≤ b}
  have hle : cycDeg ρ w b ≤ Submodule.span ℂ ((fun l => wordOp ρ l w) '' S) := by
    refine (cycDeg_le_sortedFin_of_cv3Rel h b).trans (Submodule.span_le.mpr ?_)
    rintro _ ⟨l, hs, hlow, hd, rfl⟩
    by_cases h0 : wordOp ρ l w = 0
    · rw [h0]
      exact Submodule.zero_mem _
    · refine Submodule.subset_span ⟨l, ⟨?_, fun x hx => hd ▸ le_deg_of_mem hx⟩, rfl⟩
      have hb := length_le_of_lower_nil (lowering_nil h) l.length l rfl hs.pairwise hlow h0
      rw [hd] at hb
      exact hb.trans (Gr_mono N0 b (tcount_le l))
  haveI := FiniteDimensional.span_of_finite ℂ
    ((finite_bounded_lists (Gr N0 b 8) b).image (fun l => wordOp ρ l w))
  exact Submodule.finiteDimensional_of_le hle

/-- Finite degree pieces of the actual universal auxiliary CV module, unconditionally. -/
instance finiteDimensional_cvUniv_cycDeg (ε ν ϱ : Weight) (j b : ℕ) :
    FiniteDimensional ℂ (cycDeg (cvUnivRep ε ν ϱ j) (cv_wU ε ν ϱ j) b) :=
  finiteDimensional_cycDeg_of_cv3Rel (cvUniv_rel ε ν ϱ j) b

/-- The generic universal finiteness interface for the auxiliary CV specification. -/
theorem cvUnivFD (ε ν ϱ : Weight) (j : ℕ) :
    UnivG.UnivFD bracketTable (cvSpec ε ν ϱ j) :=
  fun b => finiteDimensional_cvUniv_cycDeg ε ν ϱ j b

end

end VOA.DeligneAudit.A2.CVFinite

#print axioms VOA.DeligneAudit.A2.CVFinite.lowering_nil
#print axioms VOA.DeligneAudit.A2.CVFinite.length_le_of_lower_nil
#print axioms VOA.DeligneAudit.A2.CVFinite.finiteDimensional_cycDeg_of_cv3Rel
#print axioms VOA.DeligneAudit.A2.CVFinite.cvUnivFD
