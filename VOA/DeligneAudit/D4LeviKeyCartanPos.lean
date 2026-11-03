import VOA.DeligneAudit.D4LeviKeyCartan

/-! Positive simple-Cartan currents raise the degree of a radical key. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

def keyInsert (j : Fin 6) (s : ℕ) (k : RadicalKey) : RadicalKey :=
  ⟨k.e + if j = 0 then 1 else 0, k.x + if j = 1 then 1 else 0,
    k.u + if j = 2 then 1 else 0, k.up + if j = 3 then 1 else 0,
    k.y + if j = 4 then 1 else 0, k.z + if j = 5 then 1 else 0,
    k.degree + s⟩

def keyShift (r : ℕ) (k : RadicalKey) : RadicalKey :=
  { k with degree := k.degree + r }

theorem wordKey_cons (j : Fin 6) (s : ℕ) (l : List (Fin 6 × ℕ)) :
    wordKey ((j, s) :: l) = keyInsert j s (wordKey l) := by
  fin_cases j <;> simp [wordKey, keyInsert, Nat.add_comm]

theorem keyShift_insert (r : ℕ) (j : Fin 6) (s : ℕ) (k : RadicalKey) :
    keyShift r (keyInsert j s k) = keyInsert j s (keyShift r k) := by
  cases k
  fin_cases j <;> simp [keyShift, keyInsert, Nat.add_comm, Nat.add_left_comm]

theorem keyShift_insert_mode (r : ℕ) (j : Fin 6) (s : ℕ) (k : RadicalKey) :
    keyShift r (keyInsert j s k) = keyInsert j (r + s) k := by
  cases k
  fin_cases j <;> simp [keyShift, keyInsert, Nat.add_comm, Nat.add_left_comm]

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

theorem radical_op_maps_key (j : Fin 6) (s : ℕ) (k : RadicalKey)
    {v : V} (hv : v ∈ keyLayer ρ w k) :
    ρ.op (radicalColour j) s v ∈ keyLayer ρ w (keyInsert j s k) := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hk, rfl⟩ := hz
      apply Submodule.subset_span
      refine ⟨(j, s) :: l, ?_, rfl⟩
      rw [wordKey_cons, hk]
  | zero => simp
  | add x y _ _ hx hy =>
      simpa using (keyLayer ρ w (keyInsert j s k)).add_mem hx hy
  | smul c x _ hx =>
      simpa using (keyLayer ρ w (keyInsert j s k)).smul_mem c hx

theorem source_cartan_pos (m : ℕ)
    (h : VOA.DeligneAudit.UnivG.Sat D4sector.f ρ w
      (VOA.DeligneAudit.UnivG.ravFam D4sector m 0))
    (i : Fin 3) (r : ℕ) (hr : 0 < r) :
    ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH i)) r w = 0 := by
  have hs : VOA.DeligneAudit.UnivG.Sat D4sector.f ρ w
      (VOA.DeligneAudit.UnivG.ravSpec D4sector m (2 * m)) := by
    simpa [VOA.DeligneAudit.UnivG.ravFam] using h
  have hc : D4sector.cartan
      (leviColour (VOA.DeligneAudit.A3Sector.simpleH i)) := by
    change (leviColour (VOA.DeligneAudit.A3Sector.simpleH i)).val < 4
    fin_cases i <;> decide
  exact VOA.DeligneAudit.UnivG.rs_cartan_pos hs hc r (by omega)

/-- A positive Cartan mode sends a word into the key with higher degree. -/
theorem cartan_pos_word (m : ℕ)
    (h : VOA.DeligneAudit.UnivG.Sat D4sector.f ρ w
      (VOA.DeligneAudit.UnivG.ravFam D4sector m 0))
    (i : Fin 3) (r : ℕ) (hr : 0 < r) (l : List (Fin 6 × ℕ)) :
    ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH i)) r
      (radicalWord ρ w l) ∈ keyLayer ρ w (keyShift r (wordKey l)) := by
  induction l with
  | nil =>
      change ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH i)) r w ∈ _
      rw [source_cartan_pos ρ w m h i r hr]
      exact Submodule.zero_mem _
  | cons p l ih =>
      rcases p with ⟨j, s⟩
      let u := radicalWord ρ w l
      have hc := cartan_radical_comm ρ i j r s u
      have hfirst : ρ.op (radicalColour j) s
          (ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH i)) r u) ∈
          keyLayer ρ w (keyShift r (wordKey ((j, s) :: l))) := by
        rw [wordKey_cons, keyShift_insert]
        exact radical_op_maps_key ρ w j s (keyShift r (wordKey l)) ih
      have hsecond : ρ.op (radicalColour j) (r + s) u ∈
          keyLayer ρ w (keyShift r (wordKey ((j, s) :: l))) := by
        rw [wordKey_cons, keyShift_insert_mode]
        exact radical_op_maps_key ρ w j (r + s) (wordKey l)
          (radicalWord_mem_key ρ w l)
      change ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH i)) r
        (ρ.op (radicalColour j) s u) ∈ _
      rw [sub_eq_iff_eq_add.mp hc]
      exact (keyLayer ρ w _).add_mem
        ((keyLayer ρ w _).smul_mem _ hsecond) hfirst

theorem cartan_pos_maps_key (m : ℕ)
    (h : VOA.DeligneAudit.UnivG.Sat D4sector.f ρ w
      (VOA.DeligneAudit.UnivG.ravFam D4sector m 0))
    (i : Fin 3) (r : ℕ) (hr : 0 < r) (k : RadicalKey)
    {v : V} (hv : v ∈ keyLayer ρ w k) :
    ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH i)) r v ∈
      keyLayer ρ w (keyShift r k) := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hk, rfl⟩ := hz
      rw [← hk]
      exact cartan_pos_word ρ w m h i r hr l
  | zero => simp
  | add x y _ _ hx hy =>
      simpa using (keyLayer ρ w (keyShift r k)).add_mem hx hy
  | smul c x _ hx =>
      simpa using (keyLayer ρ w (keyShift r k)).smul_mem c hx

theorem cartan_pos_mem_higher (m : ℕ)
    (h : VOA.DeligneAudit.UnivG.Sat D4sector.f ρ w
      (VOA.DeligneAudit.UnivG.ravFam D4sector m 0))
    (i : Fin 3) (r : ℕ) (hr : 0 < r) (k : RadicalKey)
    {v : V} (hv : v ∈ keyLayer ρ w k) :
    ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH i)) r v ∈
      higherOrbit ρ w m k := by
  apply keyOrbit_le_higher ρ w m k (keyShift r k)
    (keyLess_degree m k r hr)
  exact keyLayer_le_orbit ρ w (keyShift r k)
    (cartan_pos_maps_key ρ w m h i r hr k hv)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.wordKey_cons
#print axioms VOA.DeligneAudit.D4Levi.radical_op_maps_key
#print axioms VOA.DeligneAudit.D4Levi.source_cartan_pos
#print axioms VOA.DeligneAudit.D4Levi.cartan_pos_word
#print axioms VOA.DeligneAudit.D4Levi.cartan_pos_maps_key
#print axioms VOA.DeligneAudit.D4Levi.cartan_pos_mem_higher
