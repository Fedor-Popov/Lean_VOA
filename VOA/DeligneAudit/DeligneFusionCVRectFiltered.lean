import VOA.DeligneAudit.DeligneFusionCVFamily

/-!
# The actual negative-current PBW filtration and its commuting graded action

The Finsupp quotient is restricted to its graded cyclic span. This restriction
matters: arbitrary vectors in the ambient quotient need not belong to the
filtered pieces, so the shifted operators need not commute there. On actual
word symbols their commutator is a shorter negative word and vanishes.
-/

namespace VOA.DeligneAudit.A2.CVRectFiltered

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl

noncomputable section

abbrev NegLtr := Fin 3 × ℕ

/-- Colors are ordered first root, highest root, second root. -/
def negRoot (a : Fin 3) : Fin 8 := ![3, 5, 4] a

def negWord (l : List NegLtr) : List (Fin 8 × ℕ) := l.map fun x => (negRoot x.1, x.2)

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule bracketTable V) (w : V)

def nword (l : List NegLtr) : V := wordOp R (negWord l) w

@[simp] theorem nword_nil : nword R w [] = w := rfl

@[simp] theorem nword_cons (x : NegLtr) (l : List NegLtr) :
    nword R w (x :: l) = R.op (negRoot x.1) x.2 (nword R w l) := rfl

/-- Actual negative-current words of PBW length strictly below n. -/
def Pbelow (n : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ l : List NegLtr, l.length < n ∧ v = nword R w l}

abbrev Ple (n : ℕ) : Submodule ℂ V := Pbelow R w (n + 1)

theorem Pbelow_mono {n m : ℕ} (hnm : n ≤ m) : Pbelow R w n ≤ Pbelow R w m :=
  Submodule.span_mono fun _ ⟨l, hl, hv⟩ => ⟨l, by omega, hv⟩

theorem Pbelow_zero : Pbelow R w 0 = ⊥ := by
  rw [Pbelow, Submodule.span_eq_bot]
  rintro _ ⟨l, hl, _⟩
  omega

theorem Pbelow_op (a : Fin 3) (r n : ℕ) : Pbelow R w n ≤
    (Pbelow R w (n + 1)).comap (R.op (negRoot a) r) := by
  rw [Pbelow, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  exact Submodule.subset_span ⟨(a, r) :: l, by simp; omega, rfl⟩

/-- The degree lift uses PBW length one for every negative current. -/
def liftOp (a : Fin 3) (r : ℕ) : (ℕ →₀ V) →ₗ[ℂ] (ℕ →₀ V) :=
  Finsupp.lmapDomain V ℂ (fun n : ℕ => n + 1) ∘ₗ
    Finsupp.mapRange.linearMap (R.op (negRoot a) r)

theorem liftOp_single (a : Fin 3) (r n : ℕ) (v : V) :
    liftOp R a r (Finsupp.single n v) =
      Finsupp.single (n + 1) (R.op (negRoot a) r v) := by
  simp [liftOp]

/-- The lower PBW filtration, placed in each length. -/
def Lsub : Submodule ℂ (ℕ →₀ V) :=
  Submodule.span ℂ {f | ∃ n v, v ∈ Pbelow R w n ∧ f = Finsupp.single n v}

theorem Lsub_inv (a : Fin 3) (r : ℕ) :
    Lsub R w ≤ (Lsub R w).comap (liftOp R a r) := by
  rw [Lsub, Submodule.span_le]
  rintro _ ⟨n, v, hv, rfl⟩
  exact Submodule.subset_span ⟨n + 1, R.op (negRoot a) r v,
    Pbelow_op R w a r n hv, liftOp_single R a r n v⟩

abbrev AmbientGr := (ℕ →₀ V) ⧸ Lsub R w

def ambientOp (a : Fin 3) (r : ℕ) : Module.End ℂ (AmbientGr R w) :=
  (Lsub R w).mapQ (Lsub R w) (liftOp R a r) (Lsub_inv R w a r)

/-- The length-n symbol is defined even for ambient vectors; its cyclic span
below is the actual graded module used for polynomial evaluation. -/
def symbol (n : ℕ) : V →ₗ[ℂ] AmbientGr R w :=
  (Lsub R w).mkQ ∘ₗ Finsupp.lsingle n

theorem symbol_zero_of_mem {n : ℕ} {v : V} (hv : v ∈ Pbelow R w n) :
    symbol R w n v = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨n, v, hv, rfl⟩)

def wordSymbol (l : List NegLtr) : AmbientGr R w :=
  symbol R w l.length (nword R w l)

theorem ambientOp_symbol (a : Fin 3) (r n : ℕ) (v : V) :
    ambientOp R w a r (symbol R w n v) =
      symbol R w (n + 1) (R.op (negRoot a) r v) := by
  change (Lsub R w).mkQ (liftOp R a r (Finsupp.single n v)) = _
  rw [liftOp_single]
  rfl

theorem ambientOp_wordSymbol (a : Fin 3) (r : ℕ) (l : List NegLtr) :
    ambientOp R w a r (wordSymbol R w l) = wordSymbol R w ((a, r) :: l) := by
  rw [wordSymbol, ambientOp_symbol]
  rfl

/-- Restricting to actual word symbols removes spurious ambient graded vectors. -/
def gradedCyclic : Submodule ℂ (AmbientGr R w) :=
  Submodule.span ℂ (Set.range (wordSymbol R w))

theorem gradedCyclic_inv (a : Fin 3) (r : ℕ) : gradedCyclic R w ≤
    (gradedCyclic R w).comap (ambientOp R w a r) := by
  rw [gradedCyclic, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  change ambientOp R w a r (wordSymbol R w l) ∈ gradedCyclic R w
  rw [ambientOp_wordSymbol]
  exact Submodule.subset_span ⟨(a, r) :: l, rfl⟩

abbrev Gr := gradedCyclic R w

def grOp (a : Fin 3) (r : ℕ) : Module.End ℂ (Gr R w) :=
  (ambientOp R w a r).restrict (fun _ hv => gradedCyclic_inv R w a r hv)

def grWord (l : List NegLtr) : Gr R w :=
  ⟨wordSymbol R w l, Submodule.subset_span ⟨l, rfl⟩⟩

def grGenerator : Gr R w := grWord R w []

theorem grOp_grWord (a : Fin 3) (r : ℕ) (l : List NegLtr) :
    grOp R w a r (grWord R w l) = grWord R w ((a, r) :: l) := by
  apply Subtype.ext
  exact ambientOp_wordSymbol R w a r l

/-- The actual lower-root bracket shortens PBW length by one. -/
theorem commutator_below (a b : Fin 3) (r s : ℕ) (l : List NegLtr) :
    R.op (negRoot a) r (R.op (negRoot b) s (nword R w l)) -
      R.op (negRoot b) s (R.op (negRoot a) r (nword R w l)) ∈
        Pbelow R w (l.length + 2) := by
  rw [R.comm]
  have hθ : R.op 5 (r + s) (nword R w l) ∈ Pbelow R w (l.length + 2) :=
    Submodule.subset_span ⟨(1, r + s) :: l, by simp, rfl⟩
  fin_cases a <;> fin_cases b <;>
    simp [negRoot, Fin.sum_univ_eight, bracketTable, hθ]

theorem ambient_comm_word (a b : Fin 3) (r s : ℕ) (l : List NegLtr) :
    ambientOp R w a r (ambientOp R w b s (wordSymbol R w l)) =
      ambientOp R w b s (ambientOp R w a r (wordSymbol R w l)) := by
  rw [ambientOp_wordSymbol, ambientOp_wordSymbol, ambientOp_wordSymbol, ambientOp_wordSymbol]
  apply sub_eq_zero.mp
  change symbol R w (l.length + 2)
      (R.op (negRoot a) r (R.op (negRoot b) s (nword R w l))) -
    symbol R w (l.length + 2)
      (R.op (negRoot b) s (R.op (negRoot a) r (nword R w l))) = 0
  rw [← map_sub]
  exact symbol_zero_of_mem R w (commutator_below R w a b r s l)

/-- The negative currents commute on the actual graded cyclic module. -/
theorem grOp_commute (a b : Fin 3) (r s : ℕ) :
    grOp R w a r * grOp R w b s = grOp R w b s * grOp R w a r := by
  have hker : gradedCyclic R w ≤ LinearMap.ker
      (ambientOp R w a r * ambientOp R w b s -
        ambientOp R w b s * ambientOp R w a r) := by
    rw [gradedCyclic, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    exact sub_eq_zero.mpr (ambient_comm_word R w a b r s l)
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact sub_eq_zero.mp (hker x.property)

theorem grWord_span_top : Submodule.span ℂ (Set.range (grWord R w)) = ⊤ := by
  let S := Submodule.span ℂ (Set.range (grWord R w))
  have hmap : S.map (gradedCyclic R w).subtype = gradedCyclic R w := by
    rw [show S = Submodule.span ℂ (Set.range (grWord R w)) from rfl,
      Submodule.map_span, ← Set.range_comp]
    rfl
  apply top_unique
  intro x _
  have hx := x.property
  change (x : AmbientGr R w) ∈ gradedCyclic R w at hx
  rw [← hmap] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  have hyx : y = x := Subtype.ext hxy
  exact hyx ▸ hy

theorem grOp_generator_zero (a : Fin 3) (r : ℕ)
    (hkill : R.op (negRoot a) r w = 0) : grOp R w a r (grGenerator R w) = 0 := by
  apply Subtype.ext
  change ambientOp R w a r (wordSymbol R w []) = 0
  rw [ambientOp_wordSymbol]
  change symbol R w 1 (R.op (negRoot a) r w) = 0
  rw [hkill, map_zero]

/-- A source truncation kills the entire actual graded cyclic module because
its symbol commutes with every other negative-current symbol. -/
theorem grOp_zero_of_source_zero (a : Fin 3) (r : ℕ)
    (hkill : R.op (negRoot a) r w = 0) : grOp R w a r = 0 := by
  have hword : ∀ l : List NegLtr, grOp R w a r (grWord R w l) = 0 := by
    intro l
    induction l with
    | nil => exact grOp_generator_zero R w a r hkill
    | cons x l ih =>
        rw [← grOp_grWord]
        rw [← Module.End.mul_apply, grOp_commute R w a x.1 r x.2,
          Module.End.mul_apply, ih, map_zero]
  apply LinearMap.ext_on_range (grWord_span_top R w)
  exact hword

/-- Every homogeneous linear word relation modulo lower PBW length becomes
an actual relation in the commuting graded module. -/
theorem homogeneous_word_relation (n : ℕ) (s : Finset (List NegLtr))
    (c : List NegLtr → ℂ) (hlen : ∀ l ∈ s, l.length = n)
    (hrel : (∑ l ∈ s, c l • nword R w l) ∈ Pbelow R w n) :
    (∑ l ∈ s, c l • grWord R w l) = 0 := by
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero, grWord]
  have he : (∑ l ∈ s, c l • wordSymbol R w l) =
      symbol R w n (∑ l ∈ s, c l • nword R w l) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro l hl
    rw [map_smul, wordSymbol, hlen l hl]
  rw [he]
  exact symbol_zero_of_mem R w hrel

end

end VOA.DeligneAudit.A2.CVRectFiltered

#print axioms VOA.DeligneAudit.A2.CVRectFiltered.grOp_commute
#print axioms VOA.DeligneAudit.A2.CVRectFiltered.homogeneous_word_relation
#print axioms VOA.DeligneAudit.A2.CVRectFiltered.grOp_zero_of_source_zero
