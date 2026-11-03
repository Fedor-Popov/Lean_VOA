import VOA.DeligneAudit.DeligneFusionCVRectPBWPolarizationAction

/-! # Actual raising derivations on the PBW graded cyclic module -/

namespace VOA.DeligneAudit.A2.CVRectPBWPolarization

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open CVFamily CVRectFiltered

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule bracketTable V) (w : V)

def degreeZeroLift (E : Module.End ℂ V) : Module.End ℂ (ℕ →₀ V) :=
  Finsupp.mapRange.linearMap E

theorem degreeZeroLift_single (E : Module.End ℂ V) (n : ℕ) (v : V) :
    degreeZeroLift E (Finsupp.single n v) = Finsupp.single n (E v) := by
  simp [degreeZeroLift]

theorem degreeZeroLift_inv (E : Module.End ℂ V)
    (hE : ∀ n, Pbelow R w n ≤ (Pbelow R w n).comap E) :
    Lsub R w ≤ (Lsub R w).comap (degreeZeroLift E) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨n, v, hv, rfl⟩
  change degreeZeroLift E (Finsupp.single n v) ∈ Lsub R w
  rw [degreeZeroLift_single]
  exact Submodule.subset_span ⟨n, E v, hE n hv, rfl⟩

def ambientDegreeZero (E : Module.End ℂ V)
    (hE : ∀ n, Pbelow R w n ≤ (Pbelow R w n).comap E) :
    Module.End ℂ (AmbientGr R w) :=
  (Lsub R w).mapQ (Lsub R w) (degreeZeroLift E) (degreeZeroLift_inv R w E hE)

theorem ambientDegreeZero_symbol (E : Module.End ℂ V)
    (hE : ∀ n, Pbelow R w n ≤ (Pbelow R w n).comap E) (n : ℕ) (v : V) :
    ambientDegreeZero R w E hE (symbol R w n v) = symbol R w n (E v) := by
  change (Lsub R w).mkQ (degreeZeroLift E (Finsupp.single n v)) = _
  rw [degreeZeroLift_single]
  rfl

theorem symbol_mem_graded_of_Ple (n : ℕ) {v : V} (hv : v ∈ Ple R w n) :
    symbol R w n v ∈ gradedCyclic R w := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨l, hl, rfl⟩
    by_cases he : l.length = n
    · rw [← he]
      exact Submodule.subset_span ⟨l, rfl⟩
    · have hz : nword R w l ∈ Pbelow R w n :=
        Submodule.subset_span ⟨l, by omega, rfl⟩
      rw [symbol_zero_of_mem R w hz]
      exact Submodule.zero_mem _
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

theorem ambientDegreeZero_inv (E : Module.End ℂ V)
    (hE : ∀ n, Pbelow R w n ≤ (Pbelow R w n).comap E) :
    gradedCyclic R w ≤ (gradedCyclic R w).comap (ambientDegreeZero R w E hE) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, rfl⟩
  change ambientDegreeZero R w E hE (symbol R w l.length (nword R w l)) ∈ gradedCyclic R w
  rw [ambientDegreeZero_symbol]
  exact symbol_mem_graded_of_Ple R w l.length
    (hE (l.length + 1) (nword_mem_Ple R w l))

def gradedDegreeZero (E : Module.End ℂ V)
    (hE : ∀ n, Pbelow R w n ≤ (Pbelow R w n).comap E) : Module.End ℂ (Gr R w) :=
  (ambientDegreeZero R w E hE).restrict (fun _ hx => ambientDegreeZero_inv R w E hE hx)

theorem ambientDegreeZero_comm_symbol (E : Module.End ℂ V)
    (hE : ∀ n, Pbelow R w n ≤ (Pbelow R w n).comap E)
    (a : Fin 3) (r n : ℕ) (v : V) :
    ambientDegreeZero R w E hE (ambientOp R w a r (symbol R w n v)) -
      ambientOp R w a r (ambientDegreeZero R w E hE (symbol R w n v)) =
        symbol R w (n + 1) (E (R.op (negRoot a) r v) - R.op (negRoot a) r (E v)) := by
  rw [ambientOp_symbol, ambientDegreeZero_symbol, ambientDegreeZero_symbol,
    ambientOp_symbol, ← map_sub]

def grRaising {ε ν ϱ : Weight} {j : ℕ} (h : CV3Rel R w ε ν ϱ j) (b : Bool) :
    Module.End ℂ (Gr R w) :=
  gradedDegreeZero R w (R.op (raisingRoot b) 0) (raising_Pbelow R w h b)

def grRaisingTail (b : Bool) (a : Fin 3) (r : ℕ) : Module.End ℂ (Gr R w) :=
  if b then ![0, grOp R w 0 r, 0] a else ![0, -grOp R w 2 r, 0] a

/-- The Cartan commutators have lower PBW length, so only the actual
theta-to-simple-root derivatives remain on the graded cyclic module. -/
theorem grRaising_comm {ε ν ϱ : Weight} {j : ℕ} (h : CV3Rel R w ε ν ϱ j)
    (b : Bool) (a : Fin 3) (r : ℕ) :
    grRaising R w h b * grOp R w a r - grOp R w a r * grRaising R w h b =
      grRaisingTail R w b a r := by
  apply LinearMap.ext_on_range (grWord_span_top R w)
  intro l
  apply Subtype.ext
  change ambientDegreeZero R w (R.op (raisingRoot b) 0) (raising_Pbelow R w h b)
        (ambientOp R w a r (wordSymbol R w l)) -
      ambientOp R w a r
        (ambientDegreeZero R w (R.op (raisingRoot b) 0) (raising_Pbelow R w h b)
          (wordSymbol R w l)) =
    (grRaisingTail R w b a r (grWord R w l) : AmbientGr R w)
  rw [wordSymbol, ambientDegreeZero_comm_symbol]
  have he : R.op (raisingRoot b) 0 (R.op (negRoot a) r (nword R w l)) -
      R.op (negRoot a) r (R.op (raisingRoot b) 0 (nword R w l)) =
        raisingTail R b a r (nword R w l) := by
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using (raising_comm R b a r (nword R w l))
  rw [he]
  cases b <;> fin_cases a
  · exact symbol_zero_of_mem R w (cartan_nword_mem R w h false r l)
  · simp [raisingTail, grRaisingTail, grWord, wordSymbol, negRoot]
    exact (congrArg Subtype.val (grOp_grWord R w 2 r l)).symm
  · simp [raisingTail, grRaisingTail]
  · simp [raisingTail, grRaisingTail]
  · simp [raisingTail, grRaisingTail, grWord, wordSymbol, negRoot]
    exact (congrArg Subtype.val (grOp_grWord R w 0 r l)).symm
  · exact symbol_zero_of_mem R w (cartan_nword_mem R w h true r l)

theorem grRaising_generator {ε ν ϱ : Weight} {j : ℕ} (h : CV3Rel R w ε ν ϱ j)
    (b : Bool) : grRaising R w h b (grGenerator R w) = 0 := by
  apply Subtype.ext
  change ambientDegreeZero R w (R.op (raisingRoot b) 0) (raising_Pbelow R w h b)
    (symbol R w 0 w) = 0
  rw [ambientDegreeZero_symbol, h.raising _ (by cases b <;> decide) 0, map_zero]

end

end VOA.DeligneAudit.A2.CVRectPBWPolarization

#print axioms VOA.DeligneAudit.A2.CVRectPBWPolarization.grRaising_comm
#print axioms VOA.DeligneAudit.A2.CVRectPBWPolarization.grRaising_generator
