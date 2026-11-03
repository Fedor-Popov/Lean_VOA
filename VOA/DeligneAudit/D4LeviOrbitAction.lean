import VOA.DeligneAudit.D4LeviOrbitClosure

/-! The full gl₄ orbit of a key vector reduces to its sl₄ current orbit. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

private theorem levi_sign_sq (a : Fin 15) :
    (leviSign a : ℂ) * (leviSign a : ℂ) = 1 := by
  fin_cases a <;> norm_num [leviSign]

theorem unsigned_levi_mem (k : RadicalKey) (v : V)
    (a : Fin 15) (r : ℕ)
    {u : V} (hu : (higherOrbit ρ w m k).mkQ u ∈
      cycSubG (keyQuotCurrent ρ w m k)
        ((higherOrbit ρ w m k).mkQ v)) :
    (higherOrbit ρ w m k).mkQ (ρ.op (leviColour a) r u) ∈
      cycSubG (keyQuotCurrent ρ w m k)
        ((higherOrbit ρ w m k).mkQ v) := by
  have hq := cycSubG_inv (keyQuotCurrent ρ w m k)
    ((higherOrbit ρ w m k).mkQ v) a r hu
  change (keyQuotCurrent ρ w m k).op a r
    ((higherOrbit ρ w m k).mkQ u) ∈
      cycSubG (keyQuotCurrent ρ w m k)
        ((higherOrbit ρ w m k).mkQ v) at hq
  rw [keyQuotCurrent_op] at hq
  change (leviSign a : ℂ) •
    (higherOrbit ρ w m k).mkQ (ρ.op (leviColour a) r u) ∈ _ at hq
  have hs := levi_sign_sq a
  have hh := (cycSubG (keyQuotCurrent ρ w m k)
    ((higherOrbit ρ w m k).mkQ v)).smul_mem (leviSign a : ℂ) hq
  simpa only [smul_smul, hs, one_smul] using hh

private theorem extra_comm_sum_mem (k : RadicalKey) (v u : V)
    (a : Fin 15) (r s : ℕ)
    (hu : (higherOrbit ρ w m k).mkQ u ∈
      cycSubG (keyQuotCurrent ρ w m k)
        ((higherOrbit ρ w m k).mkQ v)) :
    (higherOrbit ρ w m k).mkQ
      (∑ c : Fin 28, D4sector.f (0 : Fin 28) (leviColour a) c •
        ρ.op c (r + s) u) ∈
      cycSubG (keyQuotCurrent ρ w m k)
        ((higherOrbit ρ w m k).mkQ v) := by
  rw [map_sum]
  apply Submodule.sum_mem
  intro c _
  by_cases hc : c ∈ Set.range leviColour
  · obtain ⟨i, rfl⟩ := hc
    rw [map_smul]
    exact (cycSubG (keyQuotCurrent ρ w m k)
      ((higherOrbit ρ w m k).mkQ v)).smul_mem _
      (unsigned_levi_mem ρ w m k v i (r + s) hu)
  · simp [extra_levi_bracket_outside a c hc]

theorem levi_word_quot (k : RadicalKey) (v : V) :
    ∀ l : List (Fin 15 × ℕ),
      wordOp (keyQuotCurrent ρ w m k) l
        ((higherOrbit ρ w m k).mkQ v) =
      (higherOrbit ρ w m k).mkQ (wordOp (leviCurrent ρ) l v) := by
  intro l
  induction l with
  | nil => rfl
  | cons p l ih =>
      rcases p with ⟨a, s⟩
      simp only [wordOp]
      rw [ih, keyQuotCurrent_op]

private theorem extra_levi_word_mem
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) {v : V} (hv : v ∈ keyLayer ρ w k)
    (r : ℕ) (l : List (Fin 15 × ℕ)) :
    (higherOrbit ρ w m k).mkQ
      (ρ.op (0 : Fin 28) r (wordOp (leviCurrent ρ) l v)) ∈
    cycSubG (keyQuotCurrent ρ w m k)
      ((higherOrbit ρ w m k).mkQ v) := by
  let N := higherOrbit ρ w m k
  let Q := keyQuotCurrent ρ w m k
  let C := cycSubG Q (N.mkQ v)
  induction l with
  | nil =>
      change N.mkQ (ρ.op (0 : Fin 28) r v) ∈ C
      by_cases hr : r = 0
      · subst r
        rw [extra_weight_key ρ w m h k hv, map_smul]
        exact C.smul_mem _ (wordOp_mem_cycSubG Q (N.mkQ v) [])
      · have hpos : 0 < r := by omega
        have hh := extra_pos_higher ρ w m h r hpos k hv
        have hz : N.mkQ (ρ.op (0 : Fin 28) r v) = 0 :=
          (Submodule.Quotient.mk_eq_zero N).mpr hh
        rw [hz]
        exact C.zero_mem
  | cons p l ih =>
      rcases p with ⟨a, s⟩
      let u := wordOp (leviCurrent ρ) l v
      have hu : N.mkQ u ∈ C := by
        rw [← levi_word_quot ρ w m k v l]
        exact wordOp_mem_cycSubG Q (N.mkQ v) l
      have hc := ρ.comm (0 : Fin 28) (leviColour a) r s u
      have heq : ρ.op (0 : Fin 28) r (ρ.op (leviColour a) s u) =
          ρ.op (leviColour a) s (ρ.op (0 : Fin 28) r u) +
            ∑ c : Fin 28, D4sector.f (0 : Fin 28) (leviColour a) c •
              ρ.op c (r + s) u := by
        calc
          _ = (ρ.op (0 : Fin 28) r (ρ.op (leviColour a) s u) -
                ρ.op (leviColour a) s (ρ.op (0 : Fin 28) r u)) +
                  ρ.op (leviColour a) s (ρ.op (0 : Fin 28) r u) :=
                    (sub_add_cancel _ _).symm
          _ = _ := by rw [hc]; exact add_comm _ _
      have hfirst : N.mkQ ((leviCurrent ρ).op a s
          (ρ.op (0 : Fin 28) r u)) ∈ C := by
        change Q.op a s (N.mkQ (ρ.op (0 : Fin 28) r u)) ∈ C
        exact cycSubG_inv Q (N.mkQ v) a s ih
      have hsecond : N.mkQ ((leviSign a : ℂ) •
          (∑ c : Fin 28, D4sector.f (0 : Fin 28) (leviColour a) c •
            ρ.op c (r + s) u)) ∈ C := by
        rw [map_smul]
        exact C.smul_mem _ (extra_comm_sum_mem ρ w m k v u a r s hu)
      change N.mkQ (ρ.op (0 : Fin 28) r ((leviCurrent ρ).op a s u)) ∈ C
      change N.mkQ (ρ.op (0 : Fin 28) r
        ((leviSign a : ℂ) • ρ.op (leviColour a) s u)) ∈ C
      rw [map_smul, heq, smul_add, map_add]
      exact C.add_mem hfirst hsecond

theorem extra_cyclic_inv
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) {v : V} (hv : v ∈ keyLayer ρ w k)
    (r : ℕ) :
    let N := higherOrbit ρ w m k
    let C := cycSubG (keyQuotCurrent ρ w m k) (N.mkQ v)
    C ≤ C.comap (N.mapQ N (ρ.op (0 : Fin 28) r)
      (higherOrbit_extra_inv ρ w m k r)) := by
  dsimp only
  rw [cycSubG, Submodule.span_le]
  rintro z ⟨l, rfl⟩
  change ((higherOrbit ρ w m k).mapQ (higherOrbit ρ w m k)
    (ρ.op (0 : Fin 28) r) (higherOrbit_extra_inv ρ w m k r))
      (wordOp (keyQuotCurrent ρ w m k) l
        ((higherOrbit ρ w m k).mkQ v)) ∈
    cycSubG (keyQuotCurrent ρ w m k)
      ((higherOrbit ρ w m k).mkQ v)
  rw [levi_word_quot ρ w m k v l]
  change (higherOrbit ρ w m k).mkQ
    (ρ.op (0 : Fin 28) r (wordOp (leviCurrent ρ) l v)) ∈
      cycSubG (keyQuotCurrent ρ w m k)
        ((higherOrbit ρ w m k).mkQ v)
  exact extra_levi_word_mem ρ w m h k hv r l

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.extra_cyclic_inv
#print axioms VOA.DeligneAudit.D4Levi.unsigned_levi_mem
#print axioms VOA.DeligneAudit.D4Levi.levi_word_quot
