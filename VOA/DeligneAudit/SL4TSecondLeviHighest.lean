import VOA.DeligneAudit.SL4TSecondLeviCountSupport

/-! Highest-vector properties of the second radical count layers without positive-Cartan killing. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.LeviTypeA VOA.DeligneAudit.FiniteG
open VOA.DeligneAudit.DeligneSector

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- If there is no compound radical letter, every node-two raising mode kills the word. -/
theorem secondRadical_raising_zero_of_no_compound (he : ∀ s, ρ.op 1 s w = 0)
    (r : ℕ) (l : List (Fin 2 × ℕ))
    (hl : l.countP (fun x => x.1 = 1) = 0) :
    ρ.op 1 r (radicalWord (a2RadicalOp ρ) l • w) = 0 := by
  induction l with
  | nil => simpa [radicalWord] using he r
  | cons x l ih =>
      rcases x with ⟨i, s⟩
      have hi : i = 0 := by
        fin_cases i
        · rfl
        · simp at hl
      subst i
      have ht : l.countP (fun x => x.1 = 1) = 0 := by
        simpa using hl
      have hc := a2_raising_simple_comm ρ r s
      have happ := congrArg (fun T : Module.End ℂ V =>
        T (radicalWord (a2RadicalOp ρ) l • w)) hc
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at happ
      change ρ.op 1 r (a2RadicalOp ρ 0 s
        (radicalWord (a2RadicalOp ρ) l • w)) = 0
      rw [sub_eq_iff_eq_add.mp happ, ih ht]
      simp


theorem secondRadical_raised_insert_simple (r s : ℕ) (k : A2RadicalKey) :
    a2KeyRaised r (a2KeyInsert 0 s k) =
      a2KeyInsert 0 s (a2KeyRaised r k) := by
  cases k
  simp [a2KeyRaised, a2KeyInsert, Nat.add_comm,
    Nat.add_left_comm]

theorem secondRadical_raised_insert_compound (r s : ℕ) (k : A2RadicalKey)
    (hk : 0 < k.d₂) :
    a2KeyRaised r (a2KeyInsert 1 s k) =
      a2KeyInsert 1 s (a2KeyRaised r k) := by
  rcases k with ⟨d₁, d₂, degree⟩
  have hd : 1 ≤ d₂ := by simpa using hk
  simp [a2KeyRaised, a2KeyInsert, Nat.sub_add_cancel hd,
    Nat.add_comm, Nat.add_left_comm]

theorem secondRadical_raised_compound_to_simple (r s : ℕ) (k : A2RadicalKey) :
    a2KeyRaised r (a2KeyInsert 1 s k) = a2KeyInsert 0 (r + s) k := by
  cases k
  simp [a2KeyRaised, a2KeyInsert, Nat.add_comm,
    Nat.add_left_comm]

/-- Raising any radical word lies in the key obtained by replacing one
compound radical with a simple radical. With no compound letter, it is zero. -/
theorem secondRadical_raising_word_key (he : ∀ s, ρ.op 1 s w = 0) (r : ℕ) (l : List (Fin 2 × ℕ)) :
    ρ.op 1 r (radicalWord (a2RadicalOp ρ) l • w) ∈
      a2KeyLayer ρ w (a2KeyRaised r (a2WordKey l)) := by
  induction l with
  | nil =>
      simp [radicalWord, he r]
  | cons x l ih =>
      rcases x with ⟨i, s⟩
      let u := radicalWord (a2RadicalOp ρ) l • w
      fin_cases i
      · have hc := a2_raising_simple_comm ρ r s
        have happ := congrArg (fun T : Module.End ℂ V => T u) hc
        simp only [LinearMap.sub_apply, Module.End.mul_apply] at happ
        have hmap : a2RadicalOp ρ 0 s (ρ.op 1 r u) ∈
            a2KeyLayer ρ w (a2KeyRaised r (a2WordKey ((0, s) :: l))) := by
          rw [a2WordKey_cons, secondRadical_raised_insert_simple]
          exact a2RadicalOp_maps_key ρ w 0 s (a2KeyRaised r (a2WordKey l)) ih
        change ρ.op 1 r (a2RadicalOp ρ 0 s u) ∈ _
        rw [sub_eq_iff_eq_add.mp happ]
        simpa using hmap
      · have hc := a2_raising_compound_comm ρ r s
        have happ := congrArg (fun T : Module.End ℂ V => T u) hc
        simp only [LinearMap.sub_apply, Module.End.mul_apply] at happ
        have hfirst : a2RadicalOp ρ 1 s (ρ.op 1 r u) ∈
            a2KeyLayer ρ w (a2KeyRaised r (a2WordKey ((1, s) :: l))) := by
          by_cases hz : (a2WordKey l).d₂ = 0
          · have hzero : ρ.op 1 r u = 0 :=
              secondRadical_raising_zero_of_no_compound ρ w he r l hz
            rw [hzero, map_zero]
            exact (a2KeyLayer ρ w _).zero_mem
          · have hpos : 0 < (a2WordKey l).d₂ := by omega
            rw [a2WordKey_cons, secondRadical_raised_insert_compound r s _ hpos]
            exact a2RadicalOp_maps_key ρ w 1 s (a2KeyRaised r (a2WordKey l)) ih
        have hsecond : a2RadicalOp ρ 0 (r + s) u ∈
            a2KeyLayer ρ w (a2KeyRaised r (a2WordKey ((1, s) :: l))) := by
          rw [a2WordKey_cons, secondRadical_raised_compound_to_simple]
          exact a2RadicalOp_maps_key ρ w 0 (r + s) (a2WordKey l)
            (radicalWord_mem_own_key ρ w l)
        change ρ.op 1 r (a2RadicalOp ρ 1 s u) ∈ _
        rw [sub_eq_iff_eq_add.mp happ]
        exact (a2KeyLayer ρ w _).add_mem hsecond hfirst

/-- A node-two raising mode sends the entire key layer into the raised key layer. -/
theorem secondRadical_raising_maps_key (he : ∀ s, ρ.op 1 s w = 0) (r : ℕ) (k : A2RadicalKey)
    {v : V} (hv : v ∈ a2KeyLayer ρ w k) :
    ρ.op 1 r v ∈ a2KeyLayer ρ w (a2KeyRaised r k) := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hd₁, hd₂, hdeg, _, rfl⟩ := hz
      have hk : a2WordKey l = k := by
        cases k
        simp [a2WordKey, hd₁, hd₂, hdeg]
      rw [← hk]
      exact secondRadical_raising_word_key ρ w he r l
  | zero => simp
  | add x y _ _ hx hy => simpa using
      (a2KeyLayer ρ w (a2KeyRaised r k)).add_mem hx hy
  | smul c x _ hx => simpa using
      (a2KeyLayer ρ w (a2KeyRaised r k)).smul_mem c hx


theorem secondRadical_word_eq_currentWord (l : List (Fin 2 × ℕ)) :
    wordOp ρ (l.map fun x =>
      ((if x.1 = 0 then 3 else 5 : Fin 8), x.2)) w =
      radicalWord (a2RadicalOp ρ) l • w := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rcases x with ⟨i, s⟩
      fin_cases i
      · simpa [wordOp, radicalWord, a2RadicalOp] using congrArg (ρ.op 3 s) ih
      · simpa [wordOp, radicalWord, a2RadicalOp] using congrArg (ρ.op 5 s) ih

/-- The node-two lowering operator kills every vector of a fixed radical key
after a common power. The bound comes from the generic current-word lemma. -/
theorem secondRadical_key_lowering_nilpotent (q : ℕ)
    (hf : (ρ.op 4 0 ^ (q + 1)) w = 0) (k : A2RadicalKey)
    {v : V} (hv : v ∈ a2KeyLayer ρ w k) :
    (ρ.op 4 0 ^ (q + 1 + adK A2sector * (k.d₁ + k.d₂))) v = 0 := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, _, _, _, hlen, rfl⟩ := hz
      let l' : List (Fin 8 × ℕ) :=
        l.map fun x => ((if x.1 = 0 then 3 else 5 : Fin 8), x.2)
      have hw : (ρ.op 4 0 ^ (q + 1)) w = 0 := hf
      have hwt : A2sector.wt (4 : Fin 8) ≠ 0 := by
        decide
      have hpow := pow_kill_word (S := A2sector) ρ
        (⟨4, by decide⟩ : Fin A2sector.n) hwt hw l'
      have hword : wordOp ρ l' w = radicalWord (a2RadicalOp ρ) l • w :=
        secondRadical_word_eq_currentWord ρ w l
      change (ρ.op 4 0 ^ (q + 1 + adK A2sector * l'.length))
        (wordOp ρ l' w) = 0 at hpow
      rw [hword] at hpow
      simpa only [l', List.length_map, hlen] using hpow
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul c x _ hx => simp [map_smul, hx]


end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.secondRadical_raising_zero_of_no_compound
#print axioms VOA.DeligneAudit.SL4T.secondRadical_raised_insert_simple
#print axioms VOA.DeligneAudit.SL4T.secondRadical_raised_insert_compound
#print axioms VOA.DeligneAudit.SL4T.secondRadical_raised_compound_to_simple
#print axioms VOA.DeligneAudit.SL4T.secondRadical_raising_word_key
#print axioms VOA.DeligneAudit.SL4T.secondRadical_raising_maps_key
#print axioms VOA.DeligneAudit.SL4T.secondRadical_word_eq_currentWord
#print axioms VOA.DeligneAudit.SL4T.secondRadical_key_lowering_nilpotent
