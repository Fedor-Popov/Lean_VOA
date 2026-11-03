import VOA.DeligneAudit.D4LeviKSLemma0FourDeriv
import VOA.DeligneAudit.D4LeviKSLemma0Base

/-! Rearranging radical words before the two lowering derivations. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- Adjacent radical letters commute inside any word. -/
theorem radicalWord_swap (a b : Fin 6 × ℕ)
    (l₁ l₂ : List (Fin 6 × ℕ)) :
    radicalWord ρ w (l₁ ++ a :: b :: l₂) =
      radicalWord ρ w (l₁ ++ b :: a :: l₂) := by
  induction l₁ with
  | nil =>
      rcases a with ⟨i, r⟩
      rcases b with ⟨j, s⟩
      change ρ.op (radicalColour i) r
          (ρ.op (radicalColour j) s (radicalWord ρ w l₂)) =
        ρ.op (radicalColour j) s
          (ρ.op (radicalColour i) r (radicalWord ρ w l₂))
      exact radical_ops_comm ρ i j r s _
  | cons p l ih =>
      change ρ.op (radicalColour p.1) p.2
          (radicalWord ρ w (l ++ a :: b :: l₂)) =
        ρ.op (radicalColour p.1) p.2
          (radicalWord ρ w (l ++ b :: a :: l₂))
      rw [ih]

/-- Radical words depend only on the multiset of mode-labelled letters. -/
theorem radicalWord_perm {l₁ l₂ : List (Fin 6 × ℕ)}
    (hp : l₁.Perm l₂) : radicalWord ρ w l₁ = radicalWord ρ w l₂ := by
  induction hp with
  | nil => rfl
  | @cons a l₁ l₂ _ ih =>
      change ρ.op (radicalColour a.1) a.2 (radicalWord ρ w l₁) =
        ρ.op (radicalColour a.1) a.2 (radicalWord ρ w l₂)
      rw [ih]
  | @swap a b l => exact (radicalWord_swap ρ w a b [] l).symm
  | @trans l₁ l₂ l₃ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Every key coordinate is insensitive to the order of its letters. -/
theorem wordKey_perm {l₁ l₂ : List (Fin 6 × ℕ)}
    (hp : l₁.Perm l₂) : wordKey l₁ = wordKey l₂ := by
  induction hp with
  | nil => rfl
  | @cons a l₁ l₂ _ ih =>
      simp only [wordKey, List.countP_cons, List.map_cons, List.sum_cons] at *
      simp_all [RadicalKey.mk.injEq]
  | @swap a b l =>
      simp only [wordKey, RadicalKey.mk.injEq, List.countP_cons,
        List.map_cons, List.sum_cons]
      simp [Nat.add_comm, Nat.add_left_comm]
  | @trans l₁ l₂ l₃ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- If every X has mode zero, move one selected letter to the front and
collect the remaining X letters immediately behind it. -/
theorem radicalWord_perm_zeroXs (j : Fin 6) (l : List (Fin 6 × ℕ))
    (r : ℕ) (hjr : (j, r) ∈ l)
    (hzero : ∀ p ∈ l, p.1 = 1 → p.2 = 0) :
    ∃ n : ℕ, ∃ t : List (Fin 6 × ℕ),
      l.Perm ((j, r) :: zeroXs n ++ t) ∧
        ∀ p ∈ t, p ∈ l ∧ p.1 ≠ 1 := by
  let tail := l.erase (j, r)
  let xs := tail.filter (fun p => decide (p.1 = 1))
  let t := tail.filter (fun p => !decide (p.1 = 1))
  have hp : l.Perm ((j, r) :: tail) := List.perm_cons_erase hjr
  have hxs : xs = zeroXs xs.length := by
    apply List.eq_replicate_of_mem
    intro p hpx
    have hmem : p ∈ tail := (List.mem_filter.mp hpx).1
    have hx : p.1 = 1 := of_decide_eq_true (List.mem_filter.mp hpx).2
    have hl : p ∈ l := hp.mem_iff.mpr (List.mem_cons_of_mem _ hmem)
    rcases p with ⟨i, s⟩
    dsimp at hx
    subst i
    have hs : s = 0 := hzero (1, s) hl rfl
    subst s
    rfl
  have ht : ∀ p ∈ t, p ∈ l ∧ p.1 ≠ 1 := by
    intro p hpt
    have hmem : p ∈ tail := (List.mem_filter.mp hpt).1
    have hne : p.1 ≠ 1 := by
      intro he
      have hn := (List.mem_filter.mp hpt).2
      simp [he] at hn
    exact ⟨hp.mem_iff.mpr (List.mem_cons_of_mem _ hmem), hne⟩
  refine ⟨xs.length, t, ?_, ht⟩
  have hf := List.filter_append_perm (fun p : Fin 6 × ℕ => decide (p.1 = 1)) tail
  change (xs ++ t).Perm tail at hf
  have hperm : l.Perm ((j, r) :: (xs ++ t)) :=
    hp.trans (hf.symm.cons (j, r))
  rw [hxs] at hperm
  exact hperm

/-- A selected U' is absorbed for any ordering of zero-mode X and f₃-inert letters. -/
theorem up_zeroXs_inert_perm_higher (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (l : List (Fin 6 × ℕ)) (r : ℕ) (hr : (3, r) ∈ l)
    (hzero : ∀ p ∈ l, p.1 = 1 → p.2 = 0)
    (hall : ∀ p ∈ l, p.1 = 1 ∨ p.1 = 3 ∨ p.1 = 4 ∨ p.1 = 5) :
    radicalWord ρ w l ∈ higherOrbit ρ w m (wordKey l) := by
  obtain ⟨n, t, hp, ht⟩ :=
    radicalWord_perm_zeroXs 3 l r hr hzero
  have ht' : t.Forall (fun p => p.1 = 3 ∨ p.1 = 4 ∨ p.1 = 5) := by
    apply List.forall_iff_forall_mem.mpr
    intro p hpt
    obtain ⟨hpl, hnx⟩ := ht p hpt
    rcases hall p hpl with hx | hx | hy | hz
    · exact False.elim (hnx hx)
    · exact Or.inl hx
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr hz)
  have hm := up_zeroXs_inert_higher ρ w m h n r t ht'
  rw [← wordKey_perm hp] at hm
  simpa only [radicalWord_perm ρ w hp] using hm

/-- The f₄ companion absorbs U in any ordering with zero-mode X spectators. -/
theorem u_zeroXs_inert_perm_higher (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (l : List (Fin 6 × ℕ)) (r : ℕ) (hr : (2, r) ∈ l)
    (hzero : ∀ p ∈ l, p.1 = 1 → p.2 = 0)
    (hall : ∀ p ∈ l, p.1 = 1 ∨ p.1 = 2 ∨ p.1 = 4 ∨ p.1 = 5) :
    radicalWord ρ w l ∈ higherOrbit ρ w m (wordKey l) := by
  obtain ⟨n, t, hp, ht⟩ :=
    radicalWord_perm_zeroXs 2 l r hr hzero
  have ht' : t.Forall (fun p => p.1 = 2 ∨ p.1 = 4 ∨ p.1 = 5) := by
    apply List.forall_iff_forall_mem.mpr
    intro p hpt
    obtain ⟨hpl, hnx⟩ := ht p hpt
    rcases hall p hpl with hx | hx | hy | hz
    · exact False.elim (hnx hx)
    · exact Or.inl hx
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr hz)
  have hm := u_zeroXs_inert_higher ρ w m h n r t ht'
  rw [← wordKey_perm hp] at hm
  simpa only [radicalWord_perm ρ w hp] using hm

private theorem all_modes_zero_of_sum_zero (l : List (Fin 6 × ℕ))
    (hsum : (l.map Prod.snd).sum = 0) :
    ∀ p ∈ l, p.2 = 0 := by
  induction l with
  | nil => simp
  | cons p l ih =>
      simp only [List.map_cons, List.sum_cons] at hsum
      have hp : p.2 = 0 := by omega
      have hl : (l.map Prod.snd).sum = 0 := by omega
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hp
      · exact ih hl q hq

/-- A one-sided U' key is higher if its X letters all have mode zero. -/
theorem keyLayer_le_higher_one_sided_up (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (he : k.e = 0) (hu : k.u = 0)
    (hup : 0 < k.up) (hmode : k.x = 0 ∨ k.degree = 0) :
    keyLayer ρ w k ≤ higherOrbit ρ w m k := by
  rw [keyLayer, Submodule.span_le]
  rintro v ⟨l, hk, rfl⟩
  have hcountE : l.countP (fun p => p.1 = 0) = 0 := by
    simpa [← hk, wordKey] using he
  have hcountU : l.countP (fun p => p.1 = 2) = 0 := by
    simpa [← hk, wordKey] using hu
  have hcountUp : 0 < l.countP (fun p => p.1 = 3) := by
    simpa [← hk, wordKey] using hup
  obtain ⟨⟨j, r⟩, hmem, hj⟩ := List.countP_pos_iff.mp hcountUp
  dsimp at hj
  have hj' : j = 3 := of_decide_eq_true hj
  subst j
  have hzero : ∀ p ∈ l, p.1 = 1 → p.2 = 0 := by
    rcases hmode with hx | hd
    · have hcountX : l.countP (fun p => p.1 = 1) = 0 := by
        simpa [← hk, wordKey] using hx
      intro p hp hpx
      exact False.elim ((List.countP_eq_zero.mp hcountX p hp) (by simpa using hpx))
    · have hsum : (l.map Prod.snd).sum = 0 := by
        simpa [← hk, wordKey] using hd
      have hz := all_modes_zero_of_sum_zero l hsum
      exact fun p hp _ => hz p hp
  have hall : ∀ p ∈ l, p.1 = 1 ∨ p.1 = 3 ∨ p.1 = 4 ∨ p.1 = 5 := by
    intro p hp
    have hneE := List.countP_eq_zero.mp hcountE p hp
    have hneU := List.countP_eq_zero.mp hcountU p hp
    rcases p with ⟨j, s⟩
    fin_cases j <;> simp_all
  rw [← hk]
  exact up_zeroXs_inert_perm_higher ρ w m h l r hmem hzero hall

/-- The f₄ companion for a one-sided U key. -/
theorem keyLayer_le_higher_one_sided_u (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (he : k.e = 0) (hup : k.up = 0)
    (hu : 0 < k.u) (hmode : k.x = 0 ∨ k.degree = 0) :
    keyLayer ρ w k ≤ higherOrbit ρ w m k := by
  rw [keyLayer, Submodule.span_le]
  rintro v ⟨l, hk, rfl⟩
  have hcountE : l.countP (fun p => p.1 = 0) = 0 := by
    simpa [← hk, wordKey] using he
  have hcountUp : l.countP (fun p => p.1 = 3) = 0 := by
    simpa [← hk, wordKey] using hup
  have hcountU : 0 < l.countP (fun p => p.1 = 2) := by
    simpa [← hk, wordKey] using hu
  obtain ⟨⟨j, r⟩, hmem, hj⟩ := List.countP_pos_iff.mp hcountU
  dsimp at hj
  have hj' : j = 2 := of_decide_eq_true hj
  subst j
  have hzero : ∀ p ∈ l, p.1 = 1 → p.2 = 0 := by
    rcases hmode with hx | hd
    · have hcountX : l.countP (fun p => p.1 = 1) = 0 := by
        simpa [← hk, wordKey] using hx
      intro p hp hpx
      exact False.elim ((List.countP_eq_zero.mp hcountX p hp) (by simpa using hpx))
    · have hsum : (l.map Prod.snd).sum = 0 := by
        simpa [← hk, wordKey] using hd
      have hz := all_modes_zero_of_sum_zero l hsum
      exact fun p hp _ => hz p hp
  have hall : ∀ p ∈ l, p.1 = 1 ∨ p.1 = 2 ∨ p.1 = 4 ∨ p.1 = 5 := by
    intro p hp
    have hneE := List.countP_eq_zero.mp hcountE p hp
    have hneUp := List.countP_eq_zero.mp hcountUp p hp
    rcases p with ⟨j, s⟩
    fin_cases j <;> simp_all
  rw [← hk]
  exact u_zeroXs_inert_perm_higher ρ w m h l r hmem hzero hall

/-- XYZ reduction when at most one U colour occurs and X modes vanish. -/
theorem keyLayer_le_xyzSpan_sup_higher_one_sided (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (hmode : k.x = 0 ∨ k.degree = 0)
    (hone : k.u = 0 ∨ k.up = 0) :
    keyLayer ρ w k ≤ xyzSpan ρ w k ⊔ higherOrbit ρ w m k := by
  by_cases he : k.e = 0
  · rcases hone with hu | hup
    · by_cases hup : k.up = 0
      · exact le_sup_of_le_left (keyLayer_le_xyzSpan_of_no_U ρ w m h k hu hup)
      · exact le_sup_of_le_right
          (keyLayer_le_higher_one_sided_up ρ w m h k he hu
            (Nat.pos_of_ne_zero hup) hmode)
    · by_cases hu : k.u = 0
      · exact le_sup_of_le_left (keyLayer_le_xyzSpan_of_no_U ρ w m h k hu hup)
      · exact le_sup_of_le_right
          (keyLayer_le_higher_one_sided_u ρ w m h k he hup
            (Nat.pos_of_ne_zero hu) hmode)
  · rw [keyLayer_eq_bot_of_E ρ w m h k (Nat.pos_of_ne_zero he)]
    exact bot_le

/-- The degree-zero form of the one-sided reduction. -/
theorem keyLayer_le_xyzSpan_sup_higher_zero_degree_one_sided (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (hd : k.degree = 0) (hone : k.u = 0 ∨ k.up = 0) :
    keyLayer ρ w k ≤ xyzSpan ρ w k ⊔ higherOrbit ρ w m k :=
  keyLayer_le_xyzSpan_sup_higher_one_sided ρ w m h k (Or.inr hd) hone

/-- The same one-sided reduction at a listed key, modulo its earlier prefix. -/
theorem keyLayer_le_xyzSpan_sup_prefix_one_sided (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (i : ℕ) (hi : i < (globalKeyBox m).card)
    (hmode : (keyEnum m ⟨i, hi⟩).x = 0 ∨
      (keyEnum m ⟨i, hi⟩).degree = 0)
    (hone : (keyEnum m ⟨i, hi⟩).u = 0 ∨
      (keyEnum m ⟨i, hi⟩).up = 0) :
    keyLayer ρ w (keyEnum m ⟨i, hi⟩) ≤
      xyzSpan ρ w (keyEnum m ⟨i, hi⟩) ⊔ keyPrefix ρ w m i := by
  rw [keyPrefix_eq_higher ρ w m h i hi]
  exact keyLayer_le_xyzSpan_sup_higher_one_sided ρ w m h _ hmode hone

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.radicalWord_swap
#print axioms VOA.DeligneAudit.D4Levi.radicalWord_perm
#print axioms VOA.DeligneAudit.D4Levi.wordKey_perm
#print axioms VOA.DeligneAudit.D4Levi.radicalWord_perm_zeroXs
#print axioms VOA.DeligneAudit.D4Levi.up_zeroXs_inert_perm_higher
#print axioms VOA.DeligneAudit.D4Levi.u_zeroXs_inert_perm_higher
#print axioms VOA.DeligneAudit.D4Levi.keyLayer_le_higher_one_sided_up
#print axioms VOA.DeligneAudit.D4Levi.keyLayer_le_higher_one_sided_u
#print axioms VOA.DeligneAudit.D4Levi.keyLayer_le_xyzSpan_sup_higher_one_sided
#print axioms VOA.DeligneAudit.D4Levi.keyLayer_le_xyzSpan_sup_higher_zero_degree_one_sided
#print axioms VOA.DeligneAudit.D4Levi.keyLayer_le_xyzSpan_sup_prefix_one_sided
