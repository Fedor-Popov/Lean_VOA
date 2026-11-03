import VOA.DeligneAudit.D4CharCurrentGrading
import VOA.DeligneAudit.D4CharA2GradedOrbit
import VOA.DeligneAudit.D4CharTypeABoxCount
import VOA.DeligneAudit.LeviTypeA2CertGradedFinal

/-! Sharp projected steps in the all-weight A2 key filtration. -/

namespace VOA.DeligneAudit.D4Char

open A3Sector SectorWeyl LeviTypeA LeviKeyFiltration

noncomputable section

theorem gl2Hilb_remove_shift (u v d : ℕ) (hv : v ≤ u) :
    A2.gl2Hilb u v d = A2.gl2Hilb (u - v) 0 d := by
  unfold A2.gl2Hilb
  rw [show u = v + (u - v) by omega, sum_nat_interval_add,
    ← Nat.range_succ_eq_Icc_zero]
  simp only [Nat.add_sub_cancel_left, Nat.sub_zero]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  omega

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

theorem a2KeyLayer_homogeneous (g : CurrentGrading ρ) (hw : w ∈ g.piece 0)
    (k : A2RadicalKey) : a2KeyLayer ρ w k ≤ g.piece k.degree := by
  have hr (l : List (Fin 2 × ℕ)) :
      radicalWord (a2RadicalOp ρ) l • w ∈ g.piece (l.map Prod.snd).sum := by
    induction l with
    | nil => simpa [radicalWord] using hw
    | cons x l ih =>
        exact g.op_piece (if x.1 = 0 then 3 else 5) x.2 _ _ ih
  apply Submodule.span_le.mpr
  rintro z ⟨l, _, _, hd, _, rfl⟩
  simpa only [hd] using hr l

theorem a2KeyPrefix_projection (g : CurrentGrading ρ) (hw : w ∈ g.piece 0)
    (p q N i : ℕ) (hi : i ≤ (a2KeyBox p q).card) :
    (a2KeyPrefix ρ w (a2KeyEnum p q) i).map (g.proj N) ≤
      a2KeyPrefix ρ w (a2KeyEnum p q) i := by
  induction i with
  | zero => simp [a2KeyPrefix_zero]
  | succ i ih =>
      rw [a2KeyPrefix_step ρ w (by omega), Submodule.map_sup]
      exact sup_le_sup (ih (by omega))
        (colourClosure_projection g a2Levi _ _ N
          (a2KeyLayer_homogeneous ρ w g hw _))

theorem a2KeyEnum_first_le (p q : ℕ) (i : Fin (a2KeyBox p q).card) :
    (a2KeyEnum p q i).d₁ ≤ p := by
  have hmem := a2KeyEnum_mem p q i
  simp only [a2KeyBox, Finset.mem_biUnion, Finset.mem_image] at hmem
  obtain ⟨a, ha, b, _, d, _, hkey⟩ := hmem
  have heq : a = (a2KeyEnum p q i).d₁ := by
    simpa using congrArg A2RadicalKey.d₁ hkey
  have := Finset.mem_range.mp ha
  omega

def a2GradedKeyContribution (p q N : ℕ) (k : A2RadicalKey) : ℕ :=
  if k.degree ≤ N then
    A2.gl2Hilb (q + k.d₁) k.d₂ (N - k.degree) * a2EffectiveMultiplicity p q k
  else 0

/-- Each actual projected step has the Gaussian multiplicity times the GL2 graded rank. -/
theorem a2ProjectedStep_bound (g : CurrentGrading ρ) (hw : w ∈ g.piece 0)
    (p q : ℕ) (h : A2LocalWeylRel ρ w p q) (N : ℕ)
    (i : Fin (a2KeyBox p q).card) :
    let F := fun j => (a2KeyPrefix ρ w (a2KeyEnum p q) j).map (g.proj N)
    FiniteDimensional ℂ (StepQuot F i.val) ∧
      Module.finrank ℂ (StepQuot F i.val) ≤
        a2GradedKeyContribution p q N (a2KeyEnum p q i) := by
  let k := a2KeyEnum p q i
  let F := a2KeyPrefix ρ w (a2KeyEnum p q) i.val
  let S := a2KeyLayer ρ w k
  let T := a2KeyPrefix ρ w (a2KeyEnum p q) (i.val + 1)
  let m := Module.finrank ℂ (S ⧸ F.comap S.subtype)
  let L := if k.degree ≤ N then A2.gl2Hilb (q + k.d₁) k.d₂ (N - k.degree) else 0
  obtain ⟨v, hv⟩ := a2OrderedPrefix_step_orbits ρ w p q h i.val i.isLt
  have hF : F = a2LeviClosure ρ (a2HigherKeySpan ρ w q k) :=
    a2OrderedPrefix_eq_higher ρ w p q h i.val i.isLt
  have hm : m ≤ a2EffectiveMultiplicity p q k := by
    dsimp [m, S]
    rw [hF]
    exact a2_key_quot_finrank_le_effective ρ w p q h k (a2KeyEnum_first_le p q i)
  have hb (j : Fin m) : k.d₂ ≤ q := by
    by_contra hh
    rw [a2EffectiveMultiplicity, if_neg hh] at hm
    have := j.isLt
    omega
  have hgrade (j : Fin m) : (v j : V) ∈ g.piece k.degree :=
    a2KeyLayer_homogeneous ρ w g hw k (v j).property
  have horbit (j : Fin m) :
      FiniteDimensional ℂ
        (((a2LeviClosure ρ (ℂ ∙ (v j : V))).map (g.proj N)).map F.mkQ) ∧
      Module.finrank ℂ
        (((a2LeviClosure ρ (ℂ ∙ (v j : V))).map (g.proj N)).map F.mkQ) ≤ L := by
    by_cases hd : k.degree ≤ N
    · have hp := colourOrbit_projection g a2Levi k.degree N (hgrade j) hd
      change (a2LeviClosure ρ (ℂ ∙ (v j : V))).map (g.proj N) =
        gradedA2LeviOrbit ρ (v j) (N - k.degree) at hp
      rw [hp, hF]
      have hh := a2GradedKey_orbit_bound ρ w p q h k (v j).property
        (by dsimp [a2KeyHeight]; have := hb j; omega) (N - k.degree)
      have he : (a2KeyHeight q k).toNat = q + k.d₁ - k.d₂ := by
        dsimp [a2KeyHeight]
        omega
      refine ⟨hh.1, ?_⟩
      simpa only [L, if_pos hd, gl2Hilb_remove_shift (q + k.d₁) k.d₂ _
        (by have := hb j; omega), he] using hh.2
    · have hp := colourOrbit_projection_zero g a2Levi k.degree N (hgrade j)
        (by omega)
      change (a2LeviClosure ρ (ℂ ∙ (v j : V))).map (g.proj N) = ⊥ at hp
      rw [hp, Submodule.map_bot]
      exact ⟨inferInstance, by simp [L, hd]⟩
  have hs := projected_step_rank (g.proj N) (currentGrading_idem g N) F T
    (a2KeyPrefix_projection ρ w g hw p q N i.val (Nat.le_of_lt i.isLt)) m L
    (fun j => a2LeviClosure ρ (ℂ ∙ (v j : V))) hv
    (fun j => (horbit j).1) (fun j => (horbit j).2)
  refine ⟨hs.1, hs.2.trans ?_⟩
  have hm' := Nat.mul_le_mul_left L hm
  simpa only [L, a2GradedKeyContribution, ite_mul, zero_mul] using hm'

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gl2Hilb_remove_shift
#print axioms VOA.DeligneAudit.D4Char.a2KeyLayer_homogeneous
#print axioms VOA.DeligneAudit.D4Char.a2KeyPrefix_projection
#print axioms VOA.DeligneAudit.D4Char.a2KeyEnum_first_le
#print axioms VOA.DeligneAudit.D4Char.a2ProjectedStep_bound
