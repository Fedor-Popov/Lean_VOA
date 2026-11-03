import VOA.DeligneAudit.D4LeviOrbitAction

/-! A full gl₄ current orbit has the rank bound of its sl₄ cyclic image. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V)

def keyVectorOrbit (v : V) : Submodule ℂ V :=
  Submodule.span ℂ {z | ∃ l : List (Fin 28 × ℕ),
    l.Forall (fun p => IsLevi p.1) ∧ z = wordOp ρ l v}

theorem keyVectorOrbit_mem (v : V) (l : List (Fin 28 × ℕ))
    (hl : l.Forall (fun p => IsLevi p.1)) :
    wordOp ρ l v ∈ keyVectorOrbit ρ v :=
  Submodule.subset_span ⟨l, hl, rfl⟩

theorem keyVectorOrbit_inv (v : V) (a : Fin 28) (r : ℕ)
    (ha : IsLevi a) {u : V} (hu : u ∈ keyVectorOrbit ρ v) :
    ρ.op a r u ∈ keyVectorOrbit ρ v := by
  induction hu using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hl, rfl⟩ := hz
      exact keyVectorOrbit_mem ρ v ((a, r) :: l)
        (by simp only [List.forall_cons]; exact ⟨ha, hl⟩)
  | zero => simp
  | add x y _ _ hx hy =>
      simpa using (keyVectorOrbit ρ v).add_mem hx hy
  | smul c x _ hx =>
      simpa using (keyVectorOrbit ρ v).smul_mem c hx

private theorem signed_word_mem (v : V) :
    ∀ l : List (Fin 15 × ℕ),
      wordOp (leviCurrent ρ) l v ∈ keyVectorOrbit ρ v := by
  intro l
  induction l with
  | nil => exact keyVectorOrbit_mem ρ v [] (by simp)
  | cons p l ih =>
      rcases p with ⟨a, r⟩
      change (leviSign a : ℂ) •
        ρ.op (leviColour a) r (wordOp (leviCurrent ρ) l v) ∈ _
      exact (keyVectorOrbit ρ v).smul_mem _
        (keyVectorOrbit_inv ρ v (leviColour a) r
          (leviColour_isLevi a) ih)

variable (w : V) (m : ℕ)

theorem keyVectorOrbit_map_eq_cyclic
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) {v : V} (hv : v ∈ keyLayer ρ w k) :
    let N := higherOrbit ρ w m k
    (keyVectorOrbit ρ v).map N.mkQ =
      cycSubG (keyQuotCurrent ρ w m k) (N.mkQ v) := by
  let N := higherOrbit ρ w m k
  let Q := keyQuotCurrent ρ w m k
  let C := cycSubG Q (N.mkQ v)
  dsimp only
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    rw [keyVectorOrbit, Submodule.span_le]
    rintro z ⟨l, hl, rfl⟩
    have hword : ∀ l : List (Fin 28 × ℕ),
        l.Forall (fun p => IsLevi p.1) → N.mkQ (wordOp ρ l v) ∈ C := by
      intro l
      induction l with
      | nil =>
          intro _
          exact wordOp_mem_cycSubG Q (N.mkQ v) []
      | cons p l ih =>
          intro hl
          rcases p with ⟨a, r⟩
          simp only [List.forall_cons] at hl
          have ht := ih hl.2
          rcases levi_colour_or_extra a hl.1 with ha | ⟨i, hi⟩
          · subst a
            have hInv := extra_cyclic_inv ρ w m h k hv r
            exact hInv ht
          · subst a
            exact unsigned_levi_mem ρ w m k v i r ht
    exact hword l hl
  · rw [cycSubG, Submodule.span_le]
    rintro z ⟨l, rfl⟩
    change wordOp (keyQuotCurrent ρ w m k) l
      ((higherOrbit ρ w m k).mkQ v) ∈
        (keyVectorOrbit ρ v).map (higherOrbit ρ w m k).mkQ
    rw [levi_word_quot ρ w m k v l]
    exact Submodule.mem_map.mpr
      ⟨wordOp (leviCurrent ρ) l v, signed_word_mem ρ v l, rfl⟩

theorem key_vector_full_orbit_rank
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (hdom : ∀ i : Fin 3, 0 ≤ keyLabel m i k)
    {v : V} (hv : v ∈ keyLayer ρ w k) :
    let N := higherOrbit ρ w m k
    let C := (keyVectorOrbit ρ v).map N.mkQ
    FiniteDimensional ℂ C ∧
      Module.finrank ℂ C ≤
        4 ^ keyWeight m k 0 * 6 ^ keyWeight m k 1 *
          4 ^ keyWeight m k 2 := by
  dsimp only
  rw [keyVectorOrbit_map_eq_cyclic ρ w m h k hv]
  exact key_vector_rank ρ w m h k hdom hv

theorem keyOrbit_eq_iSup_vectorOrbit (k : RadicalKey) :
    keyOrbit ρ w k =
      ⨆ v : {v : V // v ∈ keyLayer ρ w k}, keyVectorOrbit ρ v.val := by
  apply le_antisymm
  · rw [keyOrbit, Submodule.span_le]
    rintro z ⟨l, r, hl, hk, rfl⟩
    let v : V := radicalWord ρ w r
    have hv : v ∈ keyLayer ρ w k := by
      rw [← hk]
      exact radicalWord_mem_key ρ w r
    apply Submodule.mem_iSup_of_mem ⟨v, hv⟩
    have hword : wordOp ρ
        (l ++ r.map fun p => (radicalColour p.1, p.2)) w =
        wordOp ρ l v := by
      induction l with
      | nil => rfl
      | cons p l ih =>
          simp only [List.cons_append, wordOp]
          simp only [List.forall_cons] at hl
          rw [ih hl.2]
    rw [hword]
    exact keyVectorOrbit_mem ρ v l hl
  · apply iSup_le
    intro v
    rw [keyVectorOrbit, Submodule.span_le]
    rintro z ⟨l, hl, rfl⟩
    have hbase : (v : V) ∈ keyOrbit ρ w k :=
      keyLayer_le_orbit ρ w k v.property
    induction l with
    | nil => exact hbase
    | cons p l ih =>
        rcases p with ⟨a, r⟩
        simp only [List.forall_cons] at hl
        exact levi_op_orbit ρ w k a r hl.1 (ih hl.2)

theorem keyOrbit_le_higher_of_non_dominant
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (hneg : ∃ i : Fin 3, keyLabel m i k < 0) :
    keyOrbit ρ w k ≤ higherOrbit ρ w m k := by
  rw [keyOrbit_eq_iSup_vectorOrbit]
  apply iSup_le
  intro v
  rw [keyVectorOrbit, Submodule.span_le]
  rintro z ⟨l, hl, rfl⟩
  have hbase : (v : V) ∈ higherOrbit ρ w m k :=
    keyLayer_le_higher_of_non_dominant ρ w m h k hneg v.property
  induction l with
  | nil => exact hbase
  | cons p l ih =>
      rcases p with ⟨a, r⟩
      simp only [List.forall_cons] at hl
      exact higherOrbit_full_levi_inv ρ w m k a hl.1 r (ih hl.2)

theorem keyOrbit_map_bot_of_non_dominant
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (hneg : ∃ i : Fin 3, keyLabel m i k < 0) :
    (keyOrbit ρ w k).map (higherOrbit ρ w m k).mkQ = ⊥ := by
  apply eq_bot_iff.mpr
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
  change (higherOrbit ρ w m k).mkQ x = 0
  exact (Submodule.Quotient.mk_eq_zero (higherOrbit ρ w m k)).mpr
    (keyOrbit_le_higher_of_non_dominant ρ w m h k hneg hx)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.keyVectorOrbit_map_eq_cyclic
#print axioms VOA.DeligneAudit.D4Levi.key_vector_full_orbit_rank
#print axioms VOA.DeligneAudit.D4Levi.keyOrbit_eq_iSup_vectorOrbit
#print axioms VOA.DeligneAudit.D4Levi.keyOrbit_le_higher_of_non_dominant
#print axioms VOA.DeligneAudit.D4Levi.keyOrbit_map_bot_of_non_dominant
