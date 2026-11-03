import VOA.DeligneAudit.DeligneFusionGarlandSl3
import VOA.DeligneAudit.DeligneFusionUniv

/-!
# The finiteness clause of `FusionTotalBound`

For `LocalWeylRel ρ w m`, every degree piece `cycDeg ρ w b` is finite-dimensional.

* **Local nilpotency** (`lowering_pow_wordOp`): for a grade-0 lowering letter `A = f_α ⊗ 1`
  (`α ∈ {α₁, α₂, θ}`), `A^{2|l| + 2m+1}` kills `wordOp l w` for every word `l`, because
  `(ad A)^3 = 0` on `sl₃[t]` and `A^{2m+1} w = 0`.
* **PBW with grade-0 letters first** (`cycDeg_le_sortedLow` for the key `keyFin`) and a run
  decomposition bound the length of every non-vanishing sorted word of degree `b`.
-/

namespace VOA.DeligneAudit.SectorWeyl

open VOA.AffineSl3

/-! ## A three-term commutator expansion -/

section Ring

variable {R : Type*} [Ring R]

theorem pow_mul_three {A B B1 B2 : R} (hAB : A * B = B * A + B1) (hAB1 : A * B1 = B1 * A + B2)
    (h3 : A * B2 = B2 * A) :
    ∀ n : ℕ, A ^ (n + 2) * B = B * A ^ (n + 2) + (n + 2) • (B1 * A ^ (n + 1)) +
      (n + 2).choose 2 • (B2 * A ^ n)
  | 0 => by
      simp only [zero_add, pow_two, pow_one, pow_zero, mul_one, Nat.choose_self, one_smul]
      rw [mul_assoc, hAB, mul_add, ← mul_assoc, hAB, hAB1, two_nsmul]
      noncomm_ring
  | n + 1 => by
      have ih := pow_mul_three hAB hAB1 h3 n
      rw [show n + 1 + 2 = (n + 2) + 1 from rfl, pow_succ', mul_assoc, ih, mul_add, mul_add,
        ← mul_assoc, hAB, mul_smul_comm, ← mul_assoc A B1, hAB1, mul_smul_comm, ← mul_assoc A B2,
        h3, Nat.choose_succ_succ (n + 2) 1, Nat.choose_one_right]
      simp only [add_mul, mul_assoc, ← pow_succ', add_smul, smul_add, one_smul]
      abel

end Ring

/-! ## Local nilpotency of the grade-0 lowering operators -/

section Nil

open VOA.DeligneAudit.Garland

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule (bracketTable) V}

theorem adX_add' (A T1 T2 : Module.End ℂ V) : adX A (T1 + T2) = adX A T1 + adX A T2 := by
  simp only [adX, mul_add, add_mul]; abel

theorem adX_smul' (A T : Module.End ℂ V) (k : ℂ) : adX A (k • T) = k • adX A T := by
  simp only [adX, mul_smul_comm, smul_mul_assoc, smul_sub]

theorem adX_neg' (A T : Module.End ℂ V) : adX A (-T) = -adX A T := by
  simp only [adX, mul_neg, neg_mul]; abel

theorem adX_zero' (A : Module.End ℂ V) : adX A 0 = 0 := by simp [adX]

theorem adX_op (c d : Fin 8) (s : ℕ) :
    adX (ρ.op c 0) (ρ.op d s) = ∑ e, bracketTable c d e • ρ.op e s := by
  rw [adX, op_comm_end, zero_add]

/-- `(ad f_α)^3 = 0` on every letter, for `α ∈ {α₁, α₂, θ}`. -/
theorem ad_cube (c : Fin 8) (hc : 3 ≤ c.val ∧ c.val < 6) (d : Fin 8) (s : ℕ) :
    adX (ρ.op c 0) (adX (ρ.op c 0) (adX (ρ.op c 0) (ρ.op d s))) = 0 := by
  have : c = 3 ∨ c = 4 ∨ c = 5 := by omega
  rcases this with rfl | rfl | rfl <;> fin_cases d <;>
    simp [adX_op, Fin.sum_univ_eight, bracketTable, adX_add', adX_smul', adX_neg', adX_zero']

theorem pow_kill_op (c : Fin 8) (hc : 3 ≤ c.val ∧ c.val < 6) (d : Fin 8) (s n : ℕ) {u : V}
    (hu : (ρ.op c 0 ^ n) u = 0) : (ρ.op c 0 ^ (n + 2)) (ρ.op d s u) = 0 := by
  set A := ρ.op c 0
  set B := ρ.op d s
  have hAB : A * B = B * A + adX A B := by rw [adX]; abel
  have hAB1 : A * adX A B = adX A B * A + adX A (adX A B) := by
    show _ = _ + (A * adX A B - adX A B * A); abel
  have h3 : A * adX A (adX A B) = adX A (adX A B) * A := by
    have := ad_cube c hc d s (ρ := ρ)
    rw [adX, sub_eq_zero] at this; exact this
  have key := pow_mul_three hAB hAB1 h3 n
  rw [← Module.End.mul_apply, key]
  have h1 : (A ^ (n + 1)) u = 0 := by rw [pow_succ', Module.End.mul_apply, hu, map_zero]
  have h2 : (A ^ (n + 2)) u = 0 := by rw [pow_succ', Module.End.mul_apply, h1, map_zero]
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply, hu, h1, h2, map_zero,
    smul_zero, add_zero]

/-- **Local nilpotency**: `A^{2|l| + N₀}` kills `wordOp l w` once `A^{N₀}` kills `w`. -/
theorem pow_kill_wordOp (c : Fin 8) (hc : 3 ≤ c.val ∧ c.val < 6) {w : V} {N0 : ℕ}
    (hw : (ρ.op c 0 ^ N0) w = 0) : ∀ l : List (Fin 8 × ℕ), (ρ.op c 0 ^ (2 * l.length + N0)) (wordOp ρ l w) = 0
  | [] => by simpa using hw
  | (x :: l) => by
      rw [List.length_cons, show 2 * (l.length + 1) + N0 = (2 * l.length + N0) + 2 by ring]
      exact pow_kill_op c hc x.1 x.2 _ (pow_kill_wordOp c hc hw l)

theorem pow_kill_wordOp_le (c : Fin 8) (hc : 3 ≤ c.val ∧ c.val < 6) {w : V} {N0 : ℕ}
    (hw : (ρ.op c 0 ^ N0) w = 0) (l : List (Fin 8 × ℕ)) {r : ℕ} (hr : 2 * l.length + N0 ≤ r) :
    (ρ.op c 0 ^ r) (wordOp ρ l w) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + (2 * l.length + N0) := ⟨r - (2 * l.length + N0), by omega⟩
  rw [pow_add, Module.End.mul_apply, pow_kill_wordOp c hc hw l, map_zero]

/-- The grade-0 lowering operators kill `w` at power `2m+1`. -/
theorem lowering_pow_w {w : V} {m : ℕ} (hW : LocalWeylRel ρ w m) (c : Fin 8)
    (hc : 3 ≤ c.val ∧ c.val < 6) : (ρ.op c 0 ^ (2 * m + 1)) w = 0 := by
  have hM : MabRel ρ w 0 m := (mabRel_zero_iff ρ w m).mpr hW
  have : c = 3 ∨ c = 4 ∨ c = 5 := by omega
  rcases this with rfl | rfl | rfl
  · rw [show 2 * m + 1 = m + (m + 1) by ring, pow_add, Module.End.mul_apply, Module.End.pow_apply _ (m + 1),
      hW.lowering_f1, map_zero]
  · rw [show 2 * m + 1 = m + (m + 1) by ring, pow_add, Module.End.mul_apply, Module.End.pow_apply _ (m + 1),
      hW.lowering_f2, map_zero]
  · simpa using ftheta_pow hM

end Nil

/-! ## PBW with grade-0 lowering letters first -/

section Fin

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule (bracketTable) V}

local notation "deg" => VOA.DeligneAudit.SectorGraded.wordDeg

/-- Lowering letters first; among them grade-0 letters first; then by index and grade. -/
def keyFin (x : Fin 8 × ℕ) : ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ)) :=
  toLex (if lowSl3 x.1 then 0 else 1, toLex (if x.2 = 0 then 0 else 1, toLex (x.1.val, x.2)))

theorem keyFin_low (x y : Fin 8 × ℕ) (hx : ¬ lowSl3 x.1) (hy : lowSl3 y.1) :
    keyFin y < keyFin x := by
  simp only [keyFin, if_pos hy, if_neg hx]
  exact Prod.Lex.lt_iff.mpr (Or.inl Nat.zero_lt_one)

theorem keyFin_inj {x y : Fin 8 × ℕ} (h : keyFin x = keyFin y) : x = y := by
  simp only [keyFin, toLex_inj, Prod.mk.injEq] at h
  exact Prod.ext (Fin.ext h.2.2.1) h.2.2.2

theorem keyFin_zero_lt {x y : Fin 8 × ℕ} (hx : lowSl3 x.1) (hy : lowSl3 y.1) (hx0 : x.2 = 0)
    (hy0 : y.2 ≠ 0) : keyFin x < keyFin y := by
  simp only [keyFin, if_pos hx, if_pos hy, if_pos hx0, if_neg hy0]
  exact Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, Prod.Lex.lt_iff.mpr (Or.inl Nat.zero_lt_one)⟩)

theorem cycDeg_le_sortedFin {w : V} {m : ℕ} (hW : LocalWeylRel ρ w m) (b : ℕ) :
    cycDeg ρ w b ≤ Submodule.span ℂ {u | ∃ l : List (Fin 8 × ℕ),
      l.IsChain (fun a c => keyFin a ≤ keyFin c) ∧ (∀ x ∈ l, lowSl3 x.1) ∧ deg l = b ∧
        u = wordOp ρ l w} := by
  have hw : ∀ (a : Fin 8) r, ¬ lowSl3 a → ρ.op a r w ∈ ℂ ∙ w ∧ (1 ≤ r → ρ.op a r w = 0) := by
    intro a r ha
    unfold lowSl3 at ha
    by_cases h3 : a.val < 3
    · rw [hW.raising a h3 r]; exact ⟨Submodule.zero_mem _, fun _ => rfl⟩
    · have h6 : 6 ≤ a.val := by omega
      refine ⟨?_, fun hr => hW.cartan_pos a h6 r hr⟩
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · rw [hW.cartan_zero a h6]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
      · rw [hW.cartan_pos a h6 r hr]; exact Submodule.zero_mem _
  exact cycDeg_le_sortedLow keyFin lowSl3 ρ keyFin_low hw b

/-- Number of grade-0 letter types occurring. -/
def tcount (l : List (Fin 8 × ℕ)) : ℕ := (Finset.univ.filter fun c : Fin 8 => (c, 0) ∈ l).card

theorem tcount_le (l : List (Fin 8 × ℕ)) : tcount l ≤ 8 := by
  unfold tcount
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- The length bound. -/
def Gr (m d : ℕ) : ℕ → ℕ
  | 0 => d
  | t + 1 => 3 * Gr m d t + 2 * m + 1

theorem Gr_mono (m d : ℕ) {s t : ℕ} (h : s ≤ t) : Gr m d s ≤ Gr m d t := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (by simp only [Gr]; omega)

theorem len_le_deg : ∀ l : List (Fin 8 × ℕ), (∀ y ∈ l, y.2 ≠ 0) → l.length ≤ deg l
  | [] => fun _ => le_rfl
  | (x :: l) => fun h => by
      have := len_le_deg l fun y hy => h y (List.mem_cons_of_mem _ hy)
      have hx := h x List.mem_cons_self
      simp only [List.length_cons, VOA.DeligneAudit.SectorGraded.wordDeg, List.map_cons,
        List.sum_cons] at this ⊢
      omega

theorem deg_cons' (x : Fin 8 × ℕ) (l : List (Fin 8 × ℕ)) : deg (x :: l) = x.2 + deg l := by
  simp [VOA.DeligneAudit.SectorGraded.wordDeg]

theorem deg_append' (l l' : List (Fin 8 × ℕ)) : deg (l ++ l') = deg l + deg l' := by
  simp [VOA.DeligneAudit.SectorGraded.wordDeg]

theorem deg_replicate_zero (r : ℕ) (c : Fin 8) : deg (List.replicate r (c, 0)) = 0 := by
  induction r with
  | zero => rfl
  | succ r ih => rw [List.replicate_succ, deg_cons', ih]

/-- **Length bound for non-vanishing sorted lowering words.** -/
theorem length_le_of_ne {w : V} {m : ℕ} (hW : LocalWeylRel ρ w m) :
    ∀ n (l : List (Fin 8 × ℕ)), l.length = n → l.Pairwise (fun a c => keyFin a ≤ keyFin c) →
      (∀ x ∈ l, lowSl3 x.1) → wordOp ρ l w ≠ 0 → l.length ≤ Gr m (deg l) (tcount l) := by
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
      have hr : T.length < 2 * D.length + (2 * m + 1) := by
        by_contra hcon
        exact hne (hword ▸ pow_kill_wordOp_le x.1 hc (lowering_pow_w hW x.1 hc) D (by omega))
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
      have hmono := Gr_mono m (deg (x :: rest)) ht
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
      exact (len_le_deg _ hpos).trans (Gr_mono m _ (Nat.zero_le _))

theorem le_deg_of_mem : ∀ {l : List (Fin 8 × ℕ)} {x : Fin 8 × ℕ}, x ∈ l → x.2 ≤ deg l
  | [], _, h => absurd h List.not_mem_nil
  | (y :: l), x, h => by
      rw [deg_cons']
      rcases List.mem_cons.mp h with rfl | h
      · omega
      · have := le_deg_of_mem h; omega

theorem finite_bounded_lists (L b : ℕ) :
    {l : List (Fin 8 × ℕ) | l.length ≤ L ∧ ∀ x ∈ l, x.2 ≤ b}.Finite := by
  haveI : Finite {x : Fin 8 × ℕ // x.2 ≤ b} :=
    Finite.of_injective (fun x => (x.1.1, (⟨x.1.2, by have := x.2; omega⟩ : Fin (b + 1))))
      (fun x y h => by
        simp only [Prod.mk.injEq, Fin.mk.injEq] at h
        exact Subtype.ext (Prod.ext h.1 h.2))
  refine ((List.finite_length_le {x : Fin 8 × ℕ // x.2 ≤ b} L).image
    (List.map Subtype.val)).subset ?_
  rintro l ⟨hl, hb⟩
  refine ⟨l.pmap Subtype.mk hb, by simpa using hl, ?_⟩
  simp [List.map_pmap]

/-- **The finiteness clause**: degree pieces of fusion modules are finite-dimensional. -/
theorem cycDeg_finiteDimensional {w : V} {m : ℕ} (hW : LocalWeylRel ρ w m) (b : ℕ) :
    FiniteDimensional ℂ (cycDeg ρ w b) := by
  haveI : Trans (fun a c : Fin 8 × ℕ => keyFin a ≤ keyFin c)
      (fun a c : Fin 8 × ℕ => keyFin a ≤ keyFin c) (fun a c : Fin 8 × ℕ => keyFin a ≤ keyFin c) :=
    ⟨fun h1 h2 => le_trans h1 h2⟩
  set S := {l : List (Fin 8 × ℕ) | l.length ≤ Gr m b 8 ∧ ∀ x ∈ l, x.2 ≤ b}
  have hle : cycDeg ρ w b ≤ Submodule.span ℂ ((fun l => wordOp ρ l w) '' S) := by
    refine (cycDeg_le_sortedFin hW b).trans (Submodule.span_le.mpr ?_)
    rintro _ ⟨l, hs, hlow, hd, rfl⟩
    by_cases h0 : wordOp ρ l w = 0
    · rw [h0]; exact Submodule.zero_mem _
    · refine Submodule.subset_span ⟨l, ⟨?_, fun x hx => hd ▸ le_deg_of_mem hx⟩, rfl⟩
      have := length_le_of_ne hW l.length l rfl hs.pairwise hlow h0
      rw [hd] at this
      exact this.trans (Gr_mono m b (tcount_le l))
  haveI := FiniteDimensional.span_of_finite ℂ ((finite_bounded_lists (Gr m b 8) b).image
    (fun l => wordOp ρ l w))
  exact Submodule.finiteDimensional_of_le hle

end Fin

/-- **F4, dimension part** (the named literature input that remains once the finiteness clause is proved): the total dimension of a
fusion module is at most `8^m`. -/
def FusionTotalDim : Prop :=
  ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule (bracketTable) V) (w : V),
    LocalWeylRel ρ w m → ∀ B : ℕ, ∑ b ∈ Finset.range B, Module.finrank ℂ (cycDeg ρ w b) ≤ 8 ^ m

/-- `FusionTotalBound` reduces to its dimension part. -/
theorem fusionTotalBound_of_dim (h : FusionTotalDim) : FusionTotalBound :=
  fun m V _ _ ρ w hW => ⟨cycDeg_finiteDimensional hW, h m V ρ w hW⟩

end VOA.DeligneAudit.SectorWeyl

section AxiomAudit
#print axioms VOA.DeligneAudit.SectorWeyl.pow_kill_wordOp
#print axioms VOA.DeligneAudit.SectorWeyl.length_le_of_ne
#print axioms VOA.DeligneAudit.SectorWeyl.cycDeg_finiteDimensional
#print axioms VOA.DeligneAudit.SectorWeyl.fusionTotalBound_of_dim
end AxiomAudit
