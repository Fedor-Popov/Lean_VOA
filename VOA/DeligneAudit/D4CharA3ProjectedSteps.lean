import VOA.DeligneAudit.D4CharA3GradedOrbit

/-! The exact-degree sl4 key steps, with their original three-box multiplicities. -/

namespace VOA.DeligneAudit.D4Char

open A3Sector SectorWeyl LeviTypeA LeviKeyFiltration

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3KeyLayer_homogeneous (g : CurrentGrading ρ) (hw : w ∈ g.piece 0)
    (k : A3RadicalKey) : a3KeyLayer ρ w k ≤ g.piece k.degree := by
  have hr (l : List (Fin 3 × ℕ)) :
      radicalWord (radicalOp ρ) l • w ∈ g.piece (l.map Prod.snd).sum := by
    induction l with
    | nil => simpa [radicalWord] using hw
    | cons x l ih => exact g.op_piece (A3Sector.F x.1) x.2 _ _ ih
  apply Submodule.span_le.mpr
  rintro z ⟨l, _, _, _, hd, _, rfl⟩
  simpa only [hd] using hr l

theorem a3KeyPrefix_projection (g : CurrentGrading ρ) (hw : w ∈ g.piece 0)
    (a b c N i : ℕ) (hi : i ≤ (a3KeyBox a b c).card) :
    (a3KeyPrefix ρ w (a3KeyEnum a b c) i).map (g.proj N) ≤
      a3KeyPrefix ρ w (a3KeyEnum a b c) i := by
  induction i with
  | zero => simp [a3KeyPrefix_zero]
  | succ i ih =>
      rw [a3KeyPrefix_step ρ w (by omega), Submodule.map_sup]
      apply sup_le_sup (ih (by omega))
      rw [a3LeviClosure_eq_colourClosure]
      exact colourClosure_projection (a3RestrictedGrading ρ g) (fun _ => True)
        _ _ N (a3KeyLayer_homogeneous ρ w g hw _)

def a3GradedKeyContribution (a b c N : ℕ) (k : A3RadicalKey) : ℕ :=
  if k.degree ≤ N then
    A2.gl3Hilb (b + c + k.d₁) (c + k.d₂) k.d₃ (N - k.degree) *
      a3EffectiveMultiplicity a b c k
  else 0

theorem a3ProjectedStep_bound (g : CurrentGrading ρ) (hw : w ∈ g.piece 0)
    (a b c : ℕ) (h : LocalWeylRel ρ w (weightABC a b c)) (N : ℕ)
    (i : Fin (a3KeyBox a b c).card) :
    let G := fun j => (a3KeyPrefix ρ w (a3KeyEnum a b c) j).map (g.proj N)
    FiniteDimensional ℂ (StepQuot G i.val) ∧
      Module.finrank ℂ (StepQuot G i.val) ≤
        a3GradedKeyContribution a b c N (a3KeyEnum a b c i) := by
  let k := a3KeyEnum a b c i
  let F := a3KeyPrefix ρ w (a3KeyEnum a b c) i.val
  let S := a3KeyLayer ρ w k
  let T := a3KeyPrefix ρ w (a3KeyEnum a b c) (i.val + 1)
  let m := Module.finrank ℂ (S ⧸ F.comap S.subtype)
  let L := if k.degree ≤ N then
    A2.gl3Hilb (b + c + k.d₁) (c + k.d₂) k.d₃ (N - k.degree) else 0
  obtain ⟨v, hv⟩ := a3KeyPrefix_step_orbits ρ w i.isLt (a3KeyEnum a b c) a b c h
  have hF : F = a3HigherLeviClosure ρ w b c k :=
    a3OrderedPrefix_eq_higher ρ w a b c h i.val i.isLt
  have hm : m ≤ a3EffectiveMultiplicity a b c k := a3_fixedKeyKS a b c V ρ w h i
  have hb (j : Fin m) : k.d₁ ≤ a ∧ k.d₂ ≤ b ∧ k.d₃ ≤ c := by
    apply a3_effective_support
    intro hz
    rw [hz] at hm
    have := j.isLt
    omega
  have hgrade (j : Fin m) : (v j : V) ∈ g.piece k.degree :=
    a3KeyLayer_homogeneous ρ w g hw k (v j).property
  have horbit (j : Fin m) :
      FiniteDimensional ℂ
        (((a3LeviClosure ρ (ℂ ∙ (v j : V))).map (g.proj N)).map F.mkQ) ∧
      Module.finrank ℂ
        (((a3LeviClosure ρ (ℂ ∙ (v j : V))).map (g.proj N)).map F.mkQ) ≤ L := by
    by_cases hd : k.degree ≤ N
    · rw [a3LeviOrbit_projection ρ g k.degree N (hgrade j) hd, hF]
      have hh := a3GradedKey_orbit_bound ρ w a b c h k (v j).property
        (hb j).2.1 (hb j).2.2 (N - k.degree)
      exact ⟨hh.1, by simpa only [L, if_pos hd] using hh.2⟩
    · rw [a3LeviOrbit_projection_zero ρ g k.degree N (hgrade j) (by omega),
        Submodule.map_bot]
      exact ⟨inferInstance, by simp [L, hd]⟩
  have hs := projected_step_rank (g.proj N) (currentGrading_idem g N) F T
    (a3KeyPrefix_projection ρ w g hw a b c N i.val (Nat.le_of_lt i.isLt)) m L
    (fun j => a3LeviClosure ρ (ℂ ∙ (v j : V))) hv
    (fun j => (horbit j).1) (fun j => (horbit j).2)
  refine ⟨hs.1, hs.2.trans ?_⟩
  simpa only [L, a3GradedKeyContribution, ite_mul, zero_mul] using
    Nat.mul_le_mul_left L hm

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.a3KeyLayer_homogeneous
#print axioms VOA.DeligneAudit.D4Char.a3KeyPrefix_projection
#print axioms VOA.DeligneAudit.D4Char.a3ProjectedStep_bound
