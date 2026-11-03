import VOA.DeligneAudit.D4CharA2GradedBound
import VOA.DeligneAudit.LeviTypeA3GradedInductionFinal

/-! The sharp graded sl3 estimate on each sl4 Levi quotient. -/

namespace VOA.DeligneAudit.D4Char

open A3Sector SectorWeyl

noncomputable section

theorem sum_interval_translate {M : Type*} [AddCommMonoid M] (a b c : ℕ)
    (hab : a ≤ b) (f : ℕ → M) :
    (∑ i ∈ Finset.Icc (a + c) (b + c), f i) =
      ∑ i ∈ Finset.Icc a b, f (i + c) := by
  rw [show b + c = (a + c) + (b - a) by omega, sum_nat_interval_add,
    show b = a + (b - a) by omega, sum_nat_interval_add]
  simp only [Nat.add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  omega

theorem gl3Hilb_add_shift (a b c N : ℕ) (hab : b ≤ a) :
    A2.gl3Hilb (a + c) (b + c) c N = A2.gl3Hilb a b 0 N := by
  unfold A2.gl3Hilb
  rw [sum_interval_translate b a c hab]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show Finset.Icc c (b + c) = Finset.Icc (0 + c) (b + c) by simp,
    sum_interval_translate 0 b c (Nat.zero_le b)]
  apply Finset.sum_congr rfl
  intro j hj
  obtain ⟨hbi, hia⟩ := Finset.mem_Icc.mp hi
  obtain ⟨_, hjb⟩ := Finset.mem_Icc.mp hj
  have hg : A2.gl2Hilb (i + c) (j + c) = A2.gl2Hilb i j := by
    funext d
    rw [gl2Hilb_remove_shift _ _ _ (by omega),
      gl2Hilb_remove_shift i j d (by omega)]
    simp only [Nat.add_sub_add_right]
  simp only [Nat.add_sub_add_right, Nat.add_sub_cancel_right, Nat.sub_zero, hg]

theorem gl3Hilb_remove_shift (u v w N : ℕ) (hvu : v ≤ u) (hwv : w ≤ v) :
    A2.gl3Hilb u v w N = A2.gl3Hilb (u - w) (v - w) 0 N := by
  have hh := gl3Hilb_add_shift (u - w) (v - w) w N (by omega)
  simpa only [Nat.sub_add_cancel (hwv.trans hvu), Nat.sub_add_cancel hwv] using hh

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V)

theorem a3Levi_word (l : List (Fin 8 × ℕ)) (v : V) :
    wordOp (a3LeviCurrent ρ) l v =
      wordOp ρ (l.map fun x => (a3LeviColour x.1, x.2)) v := by
  induction l with
  | nil => rfl
  | cons x l ih => change ρ.op _ _ _ = ρ.op _ _ _; rw [ih]

theorem a3LeviClosure_eq_colourClosure (S : Submodule ℂ V) :
    a3LeviClosure ρ S = colourClosure (ρ := a3LeviCurrent ρ) (fun _ => True) S := by
  unfold a3LeviClosure colourClosure
  simp only [a3Levi_word, List.forall_iff_forall_mem, implies_true, true_and]

def a3RestrictedGrading (g : CurrentGrading ρ) : CurrentGrading (a3LeviCurrent ρ) where
  piece := g.piece
  proj := g.proj
  proj_mem := g.proj_mem
  proj_piece := g.proj_piece
  op_piece a r d v hv := g.op_piece (a3LeviColour a) r d v hv

theorem colourDegreeOrbit_true {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
    (R : CurrentModule f V) (v : V) (d : ℕ) :
    colourDegreeOrbit (ρ := R) (fun _ => True) v d = cycDeg R v d := by
  unfold colourDegreeOrbit cycDeg
  simp only [List.forall_iff_forall_mem, implies_true, true_and]

theorem a3LeviOrbit_projection (g : CurrentGrading ρ) (d N : ℕ)
    {v : V} (hv : v ∈ g.piece d) (hd : d ≤ N) :
    (a3LeviClosure ρ (ℂ ∙ v)).map (g.proj N) =
      cycDeg (a3LeviCurrent ρ) v (N - d) := by
  rw [a3LeviClosure_eq_colourClosure]
  exact (colourOrbit_projection (a3RestrictedGrading ρ g) (fun _ => True)
    d N hv hd).trans (colourDegreeOrbit_true _ _ _)

theorem a3LeviOrbit_projection_zero (g : CurrentGrading ρ) (d N : ℕ)
    {v : V} (hv : v ∈ g.piece d) (hd : N < d) :
    (a3LeviClosure ρ (ℂ ∙ v)).map (g.proj N) = ⊥ := by
  rw [a3LeviClosure_eq_colourClosure]
  exact colourOrbit_projection_zero (a3RestrictedGrading ρ g) (fun _ => True) d N hv hd

theorem a3GradedKey_orbit_bound (w : V) (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c)) (k : A3RadicalKey)
    {v : V} (hv : v ∈ a3KeyLayer ρ w k) (h₂ : k.d₂ ≤ b) (h₃ : k.d₃ ≤ c) (d : ℕ) :
    let O := (cycDeg (a3LeviCurrent ρ) v d).map
      (a3HigherLeviClosure ρ w b c k).mkQ
    FiniteDimensional ℂ O ∧
      Module.finrank ℂ O ≤ A2.gl3Hilb (b + c + k.d₁) (c + k.d₂) k.d₃ d := by
  have hp : 0 ≤ a3KeyLabelInt b c 0 k := by simp [a3KeyLabelInt]; omega
  have hq : 0 ≤ a3KeyLabelInt b c 1 k := by simp [a3KeyLabelInt]; omega
  have hh := a2_all_weight_graded_bound _ _ _ _
    (a3_key_A2_localWeyl ρ w a b c h k hv hp hq) d
  dsimp only
  rw [← UnivG.quot_cycDegG (a3LeviCurrent ρ) (a3HigherLeviClosure ρ w b c k)
    (a3HigherLeviClosure_inv ρ w b c k)]
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  rw [gl3Hilb_remove_shift (b + c + k.d₁) (c + k.d₂) k.d₃ d
    (by omega) (by omega)]
  have he₀ : (a3KeyLabelInt b c 0 k).toNat = b + k.d₁ - k.d₂ := by
    change ((b : ℤ) + k.d₁ - k.d₂).toNat = b + k.d₁ - k.d₂
    omega
  have he₁ : (a3KeyLabelInt b c 1 k).toNat = c + k.d₂ - k.d₃ := by
    change ((c : ℤ) + k.d₂ - k.d₃).toNat = c + k.d₂ - k.d₃
    omega
  rw [he₀, he₁]
  congr 1
  omega

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.sum_interval_translate
#print axioms VOA.DeligneAudit.D4Char.gl3Hilb_add_shift
#print axioms VOA.DeligneAudit.D4Char.gl3Hilb_remove_shift
#print axioms VOA.DeligneAudit.D4Char.a3Levi_word
#print axioms VOA.DeligneAudit.D4Char.a3LeviClosure_eq_colourClosure
#print axioms VOA.DeligneAudit.D4Char.colourDegreeOrbit_true
#print axioms VOA.DeligneAudit.D4Char.a3LeviOrbit_projection
#print axioms VOA.DeligneAudit.D4Char.a3LeviOrbit_projection_zero
#print axioms VOA.DeligneAudit.D4Char.a3GradedKey_orbit_bound
