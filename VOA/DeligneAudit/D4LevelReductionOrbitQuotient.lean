import VOA.DeligneAudit.D4LevelReductionAdjointTransfer

/-! Full reductive Levi orbits in arbitrary invariant quotients. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.D4Levi
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)
variable (N : Submodule ℂ V)
variable (hN : ∀ a r, IsLevi a → N ≤ N.comap (ρ.op a r))

include hN in
/-- Full Levi invariance implies invariance for the signed semisimple currents. -/
theorem quotientLevi_invariant (a : Fin 15) (r : ℕ) :
    N ≤ N.comap ((leviCurrent ρ).op a r) := by
  intro v hv
  exact N.smul_mem _ (hN (leviColour a) r (leviColour_isLevi a) hv)


private theorem leviSign_square_eq_one (a : Fin 15) :
    (leviSign a : ℂ) * (leviSign a : ℂ) = 1 := by
  fin_cases a <;> norm_num [leviSign]

theorem quotient_unsignedLevi_mem (v : V)
    (a : Fin 15) (r : ℕ)
    {u : V} (hu : N.mkQ u ∈
      cycSubG (quotRepG (leviCurrent ρ) N (quotientLevi_invariant ρ N hN))
        (N.mkQ v)) :
    N.mkQ (ρ.op (leviColour a) r u) ∈
      cycSubG (quotRepG (leviCurrent ρ) N (quotientLevi_invariant ρ N hN))
        (N.mkQ v) := by
  have hq := cycSubG_inv (quotRepG (leviCurrent ρ) N (quotientLevi_invariant ρ N hN))
    (N.mkQ v) a r hu
  change (quotRepG (leviCurrent ρ) N (quotientLevi_invariant ρ N hN)).op a r
    (N.mkQ u) ∈
      cycSubG (quotRepG (leviCurrent ρ) N (quotientLevi_invariant ρ N hN))
        (N.mkQ v) at hq
  change N.mkQ ((leviCurrent ρ).op a r u) ∈ _ at hq
  change (leviSign a : ℂ) •
    N.mkQ (ρ.op (leviColour a) r u) ∈ _ at hq
  have hs := leviSign_square_eq_one a
  have hh := (cycSubG (quotRepG (leviCurrent ρ) N (quotientLevi_invariant ρ N hN))
    (N.mkQ v)).smul_mem (leviSign a : ℂ) hq
  simpa only [smul_smul, hs, one_smul] using hh

private theorem quotient_extraCartan_comm_mem (v u : V)
    (a : Fin 15) (r s : ℕ)
    (hu : N.mkQ u ∈
      cycSubG (quotRepG (leviCurrent ρ) N (quotientLevi_invariant ρ N hN))
        (N.mkQ v)) :
    N.mkQ
      (∑ c : Fin 28, D4sector.f (0 : Fin 28) (leviColour a) c •
        ρ.op c (r + s) u) ∈
      cycSubG (quotRepG (leviCurrent ρ) N (quotientLevi_invariant ρ N hN))
        (N.mkQ v) := by
  rw [map_sum]
  apply Submodule.sum_mem
  intro c _
  by_cases hc : c ∈ Set.range leviColour
  · obtain ⟨i, rfl⟩ := hc
    rw [map_smul]
    exact (cycSubG (quotRepG (leviCurrent ρ) N (quotientLevi_invariant ρ N hN))
      (N.mkQ v)).smul_mem _
      (quotient_unsignedLevi_mem ρ N hN v i (r + s) hu)
  · simp [extra_levi_bracket_outside a c hc]

theorem quotient_leviWord (v : V) :
    ∀ l : List (Fin 15 × ℕ),
      wordOp (quotRepG (leviCurrent ρ) N (quotientLevi_invariant ρ N hN)) l
        (N.mkQ v) =
      N.mkQ (wordOp (leviCurrent ρ) l v) := by
  intro l
  induction l with
  | nil => rfl
  | cons p l ih =>
      rcases p with ⟨a, s⟩
      simp only [wordOp]
      rw [ih]
      rfl

private theorem quotient_extraCartan_word_mem
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) {v : V} (hv : v ∈ keyLayer ρ w k)
    (hpos : ∀ r, 0 < r → ρ.op (0 : Fin 28) r v ∈ N)
    (r : ℕ) (l : List (Fin 15 × ℕ)) :
    N.mkQ
      (ρ.op (0 : Fin 28) r (wordOp (leviCurrent ρ) l v)) ∈
    cycSubG (quotRepG (leviCurrent ρ) N (quotientLevi_invariant ρ N hN))
      (N.mkQ v) := by
  let Q := quotRepG (leviCurrent ρ) N (quotientLevi_invariant ρ N hN)
  let C := cycSubG Q (N.mkQ v)
  induction l with
  | nil =>
      change N.mkQ (ρ.op (0 : Fin 28) r v) ∈ C
      by_cases hr : r = 0
      · subst r
        rw [extra_weight_key ρ w m h k hv, map_smul]
        exact C.smul_mem _ (wordOp_mem_cycSubG Q (N.mkQ v) [])
      · have hrpos : 0 < r := by omega
        have hh := hpos r (by omega)
        have hz : N.mkQ (ρ.op (0 : Fin 28) r v) = 0 :=
          (Submodule.Quotient.mk_eq_zero N).mpr hh
        rw [hz]
        exact C.zero_mem
  | cons p l ih =>
      rcases p with ⟨a, s⟩
      let u := wordOp (leviCurrent ρ) l v
      have hu : N.mkQ u ∈ C := by
        rw [← quotient_leviWord ρ N hN v l]
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
        exact C.smul_mem _ (quotient_extraCartan_comm_mem ρ N hN v u a r s hu)
      change N.mkQ (ρ.op (0 : Fin 28) r ((leviCurrent ρ).op a s u)) ∈ C
      change N.mkQ (ρ.op (0 : Fin 28) r
        ((leviSign a : ℂ) • ρ.op (leviColour a) s u)) ∈ C
      rw [map_smul, heq, smul_add, map_add]
      exact C.add_mem hfirst hsecond

theorem quotient_extraCartan_cyclic_invariant
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) {v : V} (hv : v ∈ keyLayer ρ w k)
    (hpos : ∀ r, 0 < r → ρ.op (0 : Fin 28) r v ∈ N)
    (r : ℕ) :
      let C := cycSubG (quotRepG (leviCurrent ρ) N (quotientLevi_invariant ρ N hN)) (N.mkQ v)
    C ≤ C.comap (N.mapQ N (ρ.op (0 : Fin 28) r)
      (hN 0 r ⟨0, rfl⟩)) := by
  dsimp only
  rw [cycSubG, Submodule.span_le]
  rintro z ⟨l, rfl⟩
  change (N.mapQ N
    (ρ.op (0 : Fin 28) r) (hN 0 r ⟨0, rfl⟩))
      (wordOp (quotRepG (leviCurrent ρ) N (quotientLevi_invariant ρ N hN)) l
        (N.mkQ v)) ∈
    cycSubG (quotRepG (leviCurrent ρ) N (quotientLevi_invariant ρ N hN))
      (N.mkQ v)
  rw [quotient_leviWord ρ N hN v l]
  change N.mkQ
    (ρ.op (0 : Fin 28) r (wordOp (leviCurrent ρ) l v)) ∈
      cycSubG (quotRepG (leviCurrent ρ) N (quotientLevi_invariant ρ N hN))
        (N.mkQ v)
  exact quotient_extraCartan_word_mem ρ w m N hN h k hv hpos r l

private theorem semisimpleWord_mem_fullOrbit (v : V) :
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


theorem keyVectorOrbit_quotient_eq_cyclic
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) {v : V} (hv : v ∈ keyLayer ρ w k)
    (hpos : ∀ r, 0 < r → ρ.op (0 : Fin 28) r v ∈ N) :
    (keyVectorOrbit ρ v).map N.mkQ =
      cycSubG (quotRepG (leviCurrent ρ) N (quotientLevi_invariant ρ N hN)) (N.mkQ v) := by
  let Q := quotRepG (leviCurrent ρ) N (quotientLevi_invariant ρ N hN)
  let C := cycSubG Q (N.mkQ v)
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
            have hInv := quotient_extraCartan_cyclic_invariant ρ w m N hN h k hv hpos r
            exact hInv ht
          · subst a
            exact quotient_unsignedLevi_mem ρ N hN v i r ht
    exact hword l hl
  · rw [cycSubG, Submodule.span_le]
    rintro z ⟨l, rfl⟩
    change wordOp (quotRepG (leviCurrent ρ) N (quotientLevi_invariant ρ N hN)) l
      (N.mkQ v) ∈
        (keyVectorOrbit ρ v).map N.mkQ
    rw [quotient_leviWord ρ N hN v l]
    exact Submodule.mem_map.mpr
      ⟨wordOp (leviCurrent ρ) l v, semisimpleWord_mem_fullOrbit ρ v l, rfl⟩

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.quotientLevi_invariant

#print axioms VOA.DeligneAudit.D4LevelReduction.quotient_unsignedLevi_mem

#print axioms VOA.DeligneAudit.D4LevelReduction.quotient_leviWord

#print axioms VOA.DeligneAudit.D4LevelReduction.quotient_extraCartan_cyclic_invariant

#print axioms VOA.DeligneAudit.D4LevelReduction.keyVectorOrbit_quotient_eq_cyclic
