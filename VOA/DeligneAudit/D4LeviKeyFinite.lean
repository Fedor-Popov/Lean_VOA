import VOA.DeligneAudit.D4LeviKeys

/-! Each exact six-letter key has finitely many current monomials. -/

namespace VOA.DeligneAudit.D4Levi

theorem radicalCounts_sum (l : List (Fin 6 × ℕ)) :
    l.countP (fun p => p.1 = 0) + l.countP (fun p => p.1 = 1) +
      l.countP (fun p => p.1 = 2) + l.countP (fun p => p.1 = 3) +
        l.countP (fun p => p.1 = 4) + l.countP (fun p => p.1 = 5) =
          l.length := by
  induction l with
  | nil => simp
  | cons p l ih =>
      rcases p with ⟨i, s⟩
      fin_cases i <;> simp_all <;> omega

def keyDepth (k : RadicalKey) : ℕ :=
  k.e + k.x + k.u + k.up + k.y + k.z

theorem wordKey_depth (l : List (Fin 6 × ℕ)) :
    keyDepth (wordKey l) = l.length := by
  exact radicalCounts_sum l

/-- Lists of a fixed length and fixed total current degree form a finite set. -/
theorem finite_words (n d : ℕ) :
    {l : List (Fin 6 × ℕ) |
      l.length = n ∧ (l.map Prod.snd).sum = d}.Finite := by
  let T : Set (List (Fin 6 × Fin (d + 1))) := {l | l.length = n}
  have hT : T.Finite := List.finite_length_eq _ n
  let f : List (Fin 6 × Fin (d + 1)) → List (Fin 6 × ℕ) :=
    List.map fun p => (p.1, p.2.val)
  have hfinite : (f '' T).Finite := hT.image f
  apply hfinite.subset
  intro l hl
  have hbound : ∀ p ∈ l, p.2 < d + 1 := by
    intro p hp
    have hp' : p.2 ∈ l.map Prod.snd := List.mem_map.mpr ⟨p, hp, rfl⟩
    have hle := List.le_sum_of_mem hp'
    have hsum : (l.map Prod.snd).sum = d := hl.2
    omega
  let l' : List (Fin 6 × Fin (d + 1)) :=
    l.attach.map fun p => (p.val.1, ⟨p.val.2, hbound p.val p.property⟩)
  refine ⟨l', ?_, ?_⟩
  · simpa [T, l'] using hl.1
  · simp only [f, l', List.map_map]
    convert List.attach_map_subtype_val l using 1

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : VOA.DeligneAudit.SectorWeyl.CurrentModule
  VOA.DeligneAudit.DeligneSector.D4.fD4 V) (w : V)

/-- Every fixed radical key layer is finite-dimensional, without a source relation. -/
theorem keyLayer_finite (k : RadicalKey) :
    FiniteDimensional ℂ (keyLayer ρ w k) := by
  let S : Set (List (Fin 6 × ℕ)) :=
    {l | l.length = keyDepth k ∧ (l.map Prod.snd).sum = k.degree}
  have hS : S.Finite := finite_words (keyDepth k) k.degree
  have hgen : {v | ∃ l : List (Fin 6 × ℕ), wordKey l = k ∧
      v = radicalWord ρ w l}.Finite := by
    apply (hS.image (radicalWord ρ w)).subset
    rintro v ⟨l, hk, rfl⟩
    refine ⟨l, ?_, rfl⟩
    exact ⟨by simpa [S, ← hk] using (wordKey_depth l).symm,
      by simpa [S, wordKey] using congrArg RadicalKey.degree hk⟩
  change FiniteDimensional ℂ (Submodule.span ℂ
    {v | ∃ l : List (Fin 6 × ℕ), wordKey l = k ∧ v = radicalWord ρ w l})
  exact FiniteDimensional.span_of_finite ℂ hgen

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.radicalCounts_sum
#print axioms VOA.DeligneAudit.D4Levi.wordKey_depth
#print axioms VOA.DeligneAudit.D4Levi.finite_words
#print axioms VOA.DeligneAudit.D4Levi.keyLayer_finite
