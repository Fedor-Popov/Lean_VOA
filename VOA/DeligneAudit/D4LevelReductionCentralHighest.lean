import VOA.DeligneAudit.D4LevelReductionCentralGeneration

/-! The exterior-square local Weyl relations on the zero-adjoint boundary. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.D4Levi
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

/-- A central radical key contains only highest-root letters. -/
theorem centralKey_word_colours (c d : ℕ) (l : List (Fin 6 × ℕ))
    (h : wordKey l = centralLetterKey c d) : ∀ q ∈ l, q.1 = 5 := by
  have hl := wordKey_depth l
  have hz := congrArg RadicalKey.z h
  rw [h] at hl
  simp only [centralLetterKey, keyDepth, zero_add, add_zero] at hl
  simp only [wordKey, centralLetterKey] at hz
  have hc : l.countP (fun q => q.1 = 5) = l.length := hz.trans hl
  simpa using List.countP_eq_length.mp hc

/-- A nonzero raising replacement in a central word creates a Y letter at the same level. -/
theorem central_raise_replacement (m : ℕ) (i : Fin 3) (r : ℕ)
    {l q : List (Fin 6 × ℕ)} (h : RaiseReplaces i r l q)
    (hl : ∀ p ∈ l, p.1 = 5) :
    keyAlphaGrade m (wordKey q) = keyAlphaGrade m (wordKey l) ∧
      keyLeviLevel m (wordKey q) = keyLeviLevel m (wordKey l) ∧
        0 < (wordKey q).y := by
  induction h with
  | @head j s k n l h =>
      have hj : j = 5 := hl (j, s) (by simp)
      subst j
      fin_cases i <;> simp [raiseAction] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [keyAlphaGrade, keyDepth, keyLeviLevel, wordKey]
      omega
  | @tail j s l q h ih =>
      have hj : j = 5 := hl (j, s) (by simp)
      subst j
      have ht := ih (fun p hp => hl p (List.mem_cons_of_mem (5, s) hp))
      have hg (t : List (Fin 6 × ℕ)) :
          keyAlphaGrade m (wordKey ((5, s) :: t)) = keyAlphaGrade m (wordKey t) - 1 := by
        simp [keyAlphaGrade, keyDepth, wordKey]
        ring
      have hp (t : List (Fin 6 × ℕ)) :
          keyLeviLevel m (wordKey ((5, s) :: t)) = keyLeviLevel m (wordKey t) - 1 := by
        simp [keyLeviLevel, wordKey]
        ring
      refine ⟨?_, ?_, ?_⟩
      · rw [hg, hg, ht.1]
      · rw [hp, hp, ht.2.1]
      · simpa [wordKey] using ht.2.2

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- Positive simple Levi currents on a central key land in the next level. -/
theorem centralKey_simple_raise_mem_next (m c d : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (i : Fin 3) (r : ℕ)
    {v : V} (hv : v ∈ keyLayer ρ w (centralLetterKey c d)) :
    ρ.op (leviColour (A3Sector.simpleE i)) r v ∈
      levelFiltration ρ w m ((m : ℤ) - c) ((m : ℤ) - c + 1) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, hl, rfl⟩ := hv
      have hspan : raiseWordSpan ρ w i r l ≤
          levelFiltration ρ w m ((m : ℤ) - c) ((m : ℤ) - c + 1) := by
        rw [raiseWordSpan, Submodule.span_le]
        rintro z ⟨q, hq, rfl⟩
        obtain ⟨hg, hp, hy⟩ := central_raise_replacement m i r hq
          (centralKey_word_colours c d l hl)
        rw [hl] at hg hp
        apply boundaryKey_le_next_of_Y ρ w m h _ (wordKey q) _ _ hy
          (keyLayer_le_orbit ρ w _ (radicalWord_mem_key ρ w q))
        · simpa [keyAlphaGrade, keyDepth, centralLetterKey] using hg
        · simpa [keyLeviLevel, centralLetterKey] using hp
      exact hspan (simple_raise_word_span ρ w m h i r l)
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul t x _ hx => simpa using Submodule.smul_mem _ t hx

/-- Central boundary vectors have only the middle fundamental Levi label. -/
theorem centralKey_cartan_weight (b c d : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (b + c) 0))
    (i : Fin 3) {v : V} (hv : v ∈ keyLayer ρ w (centralLetterKey c d)) :
    (leviCurrent ρ).op (A3Sector.simpleH i) 0 v =
      (A3Sector.weightABC 0 b 0 i : ℂ) • v := by
  have hw := cartan_weight_key ρ w (b + c) h i (centralLetterKey c d) hv
  fin_cases i <;>
    simpa [leviCurrent, leviSign, A3Sector.simpleH, A3Sector.weightABC,
      keyLabel, centralLetterKey, Nat.cast_add, Int.cast_add, Int.cast_sub] using hw

/-- Killing the next level and positive Cartan modes gives the exterior-square relations. -/
theorem centralKey_localWeyl_quotient (b c d : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (b + c) 0)) (N : Submodule ℂ V)
    (hN : ∀ e r, N ≤ N.comap ((leviCurrent ρ).op e r))
    (hnext : levelFiltration ρ w (b + c) b ((b : ℤ) + 1) ≤ N)
    {v : V} (hv : v ∈ keyLayer ρ w (centralLetterKey c d))
    (hpos : ∀ i s, 0 < s → (leviCurrent ρ).op (A3Sector.simpleH i) s v ∈ N) :
    A3Sector.LocalWeylRel (quotRepG (leviCurrent ρ) N hN) (N.mkQ v)
      (A3Sector.weightABC 0 b 0) := by
  let Q := quotRepG (leviCurrent ρ) N hN
  have he (i : Fin 3) (r : ℕ) : Q.op (A3Sector.simpleE i) r (N.mkQ v) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero N).mpr
    apply N.smul_mem
    apply hnext
    simpa only [Nat.cast_add, add_sub_cancel_right] using
      centralKey_simple_raise_mem_next ρ w (b + c) c d h i r hv
  have hh (i : Fin 3) : Q.op (A3Sector.simpleH i) 0 (N.mkQ v) =
      (A3Sector.weightABC 0 b 0 i : ℂ) • N.mkQ v := by
    change N.mkQ ((leviCurrent ρ).op (A3Sector.simpleH i) 0 v) = _
    rw [centralKey_cartan_weight ρ w b c d h i hv, map_smul]
  refine ⟨positive_zero_of_simple Q (N.mkQ v) he, ?_, hh, ?_⟩
  · intro i r hr
    exact (Submodule.Quotient.mk_eq_zero N).mpr (hpos i r hr)
  · intro i
    let E := Q.op (A3Sector.simpleE i) 0
    let F := Q.op (A3Sector.simpleF i) 0
    let H := Q.op (A3Sector.simpleH i) 0
    have hEF : ∀ u, E (F u) - F (E u) = H u := by
      intro u
      dsimp [E, F, H]
      rw [Q.comm]
      simp [A3Sector.simple_ef_table]
    have hHF : ∀ u, H (F u) - F (H u) = (-2 : ℂ) • F u := by
      intro u
      dsimp [F, H]
      rw [Q.comm]
      simp [A3Sector.simple_hf_table]
    have hiter : ∀ n (u : V), F^[n] (N.mkQ u) =
        N.mkQ (((leviCurrent ρ).op (A3Sector.simpleF i) 0)^[n] u) := by
      intro n
      induction n with
      | zero => intro u; rfl
      | succ n ih =>
          intro u
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
          rfl
    let K := lowerBaseExponent (b + c) i + 2 * keyDepth (centralLetterKey c d)
    have hn : F^[K] (N.mkQ v) = 0 := by
      rw [hiter, ← Module.End.pow_apply]
      rw [key_simple_lower_nil_levi ρ w (b + c) h i (centralLetterKey c d) hv, map_zero]
    have hh' : H (N.mkQ v) =
        (((A3Sector.weightABC 0 b 0 i : ℕ) : ℤ) : ℂ) • N.mkQ v := by
      simpa using hh i
    have hs := (CLFilt.hw_pow E F H hEF hHF (he i 0) hh' K hn).2
      (Int.natCast_nonneg _)
    simpa only [Int.toNat_natCast] using hs

/-- Each cyclic quotient on the central boundary has the local exterior-square bound. -/
theorem centralKey_quotient_rank_le (b c d : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (b + c) 0)) (N : Submodule ℂ V)
    (hN : ∀ e r, N ≤ N.comap ((leviCurrent ρ).op e r))
    (hnext : levelFiltration ρ w (b + c) b ((b : ℤ) + 1) ≤ N)
    {v : V} (hv : v ∈ keyLayer ρ w (centralLetterKey c d))
    (hpos : ∀ i s, 0 < s → (leviCurrent ρ).op (A3Sector.simpleH i) s v ∈ N) :
    FiniteDimensional ℂ (cycSubG (quotRepG (leviCurrent ρ) N hN) (N.mkQ v)) ∧
      Module.finrank ℂ (cycSubG (quotRepG (leviCurrent ρ) N hN) (N.mkQ v)) ≤ 6 ^ b := by
  simpa using A3Sector.a3_all_weight_rank (quotRepG (leviCurrent ρ) N hN)
    (N.mkQ v) 0 b 0 (centralKey_localWeyl_quotient ρ w b c d h N hN hnext hv hpos)

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.centralKey_word_colours
#print axioms VOA.DeligneAudit.D4LevelReduction.central_raise_replacement
#print axioms VOA.DeligneAudit.D4LevelReduction.centralKey_simple_raise_mem_next
#print axioms VOA.DeligneAudit.D4LevelReduction.centralKey_cartan_weight
#print axioms VOA.DeligneAudit.D4LevelReduction.centralKey_localWeyl_quotient
#print axioms VOA.DeligneAudit.D4LevelReduction.centralKey_quotient_rank_le
