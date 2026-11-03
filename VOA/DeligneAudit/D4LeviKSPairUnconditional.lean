import VOA.DeligneAudit.D4LeviKSPairSourceSpan

/-! Discharge of PAIR transfer sources from an initial higher-key source. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem pairModeWord_zero_of_ne_nil
    (F : ℕ → Module.End ℂ V) (v : V)
    (hzero : ∀ r, F r v = 0) (rs : List ℕ) (hrs : rs ≠ []) :
    pairModeWord F rs v = 0 := by
  induction rs with
  | nil => contradiction
  | cons r rs ih =>
      cases rs with
      | nil => simp [pairModeWord, hzero]
      | cons s ss =>
          change F r (pairModeWord F (s :: ss) v) = 0
          rw [ih (by simp)]
          exact map_zero (F r)

/-- If the initial operator source lies in an invariant submodule and all
    transfer modes kill the cyclic vector, every recursive source lies there. -/
theorem pairTransferSources_of_source
    (N : Submodule ℂ V) (F : ℕ → Module.End ℂ V) (v : V)
    (hInv : ∀ r x, x ∈ N → F r x ∈ N)
    (hzero : ∀ r, F r v = 0)
    (rs : List ℕ) (A : Module.End ℂ V) (hA : A v ∈ N) :
    pairTransferSources N F v rs A := by
  induction rs generalizing A with
  | nil => trivial
  | cons r rs ih =>
      have hsource : A (pairModeWord F rs v) ∈ N := by
        by_cases hrs : rs = []
        · subst rs
          exact hA
        · rw [pairModeWord_zero_of_ne_nil F v hzero rs hrs]
          simp only [map_zero]
          exact N.zero_mem
      have hnext : (A * F r - F r * A) v ∈ N := by
        simp only [LinearMap.sub_apply, Module.End.mul_apply, hzero,
          map_zero, zero_sub]
        exact N.neg_mem (hInv r (A v) hA)
      exact ⟨hsource, ih _ hnext⟩

/-- The signed f₃ antipode identity at an enumerated D4 key. Its only
    source condition is membership of the initial operator word in the prefix. -/
theorem fThree_antipode_signed_prefix
    (ρ : CurrentModule D4sector.f V) (w : V) (m i : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (rs : List ℕ) (A : Module.End ℂ V)
    (hA : A w ∈ keyPrefix ρ w m i) :
    A (pairModeWord (ρ.op (17 : Fin 28)) rs w) -
      (-1 : ℂ) ^ rs.length •
        pairAdjoint (ρ.op (17 : Fin 28)) rs A w ∈
          keyPrefix ρ w m i := by
  rw [keyPrefix_eq_higher ρ w m h i hi] at hA ⊢
  let k := keyEnum m ⟨i, hi⟩
  apply fThree_antipode_signed_higher ρ w m k rs A w
  apply pairTransferSources_of_source
  · intro r x hx
    exact higherOrbit_full_levi_inv ρ w m k (17 : Fin 28)
      ⟨7, rfl⟩ r hx
  · exact fThree_source_mode_zero ρ w m h
  · exact hA

/-- A source with fewer than `b` PAIR substitutions satisfies every
    iterated transfer condition at the final symmetric key. -/
theorem fThree_antipode_partial_word_prefix
    (ρ : CurrentModule D4sector.f V) (w : V) (m i : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (a b c d nx ny : ℕ) (l : List (Fin 6 × ℕ))
    (hnx : nx ≤ a + b) (hstep : nx + ny < b)
    (hword : wordKey l = pairPartialKey a b c d nx ny)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c d)
    (rs : List ℕ) :
    (l.map fun p => ρ.op (radicalColour p.1) p.2).prod
        (pairModeWord (ρ.op (17 : Fin 28)) rs w) -
      (-1 : ℂ) ^ rs.length •
        pairAdjoint (ρ.op (17 : Fin 28)) rs
          (l.map fun p => ρ.op (radicalColour p.1) p.2).prod w ∈
            keyPrefix ρ w m i := by
  apply fThree_antipode_signed_prefix ρ w m i h hi rs
  rw [keyPrefix_eq_higher ρ w m h i hi, hkey]
  apply pairPartialSourceSpan_le_higher ρ w m a b c d
  have hspan : radicalWord ρ w l ∈ pairPartialSourceSpan ρ w a b c d :=
    Submodule.subset_span ⟨nx, ny, l, hnx, hstep, hword, rfl⟩
  have hprod (t : List (Fin 6 × ℕ)) :
      (t.map fun p => ρ.op (radicalColour p.1) p.2).prod w =
        radicalWord ρ w t := by
    induction t with
    | nil => simp [radicalWord, wordOp]
    | cons p t ih =>
        rcases p with ⟨j, s⟩
        simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
        change ρ.op (radicalColour j) s
          ((t.map fun p => ρ.op (radicalColour p.1) p.2).prod w) =
          ρ.op (radicalColour j) s (radicalWord ρ w t)
        rw [ih]
  rwa [hprod]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairTransferSources_of_source
#print axioms VOA.DeligneAudit.D4Levi.fThree_antipode_signed_prefix
#print axioms VOA.DeligneAudit.D4Levi.fThree_antipode_partial_word_prefix
