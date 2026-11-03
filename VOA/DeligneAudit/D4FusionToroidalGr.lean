import VOA.DeligneAudit.D4FusionToroidalCore

/-!
# Conditional associated graded for the high-mode filtration

The Finsupp numerator contains precisely components from their matching filtration steps.
The shifted symbol operators descend under `HighModeShift`, the compatibility needed for
mode `i*m+s` to have `u` degree `i`. No dimension or surjectivity claim is made.
-/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ) (R : RelSpec n) (m : ℕ)

/-- The shift needed to interpret mode `i*m+s` as a symbol of `u` degree `i`. -/
def HighModeShift : Prop :=
  ∀ c i s j, s < m →
    TU f R m j ≤ (TU f R m (j + i)).comap
      ((univRepG f R).op c (i * m + s))

theorem shift_zero (c : Fin n) (s j : ℕ) (hs : s < m) :
    TU f R m j ≤ (TU f R m (j + 0)).comap
      ((univRepG f R).op c (0 * m + s)) := by
  have h := TU_cons f R m j (c, s)
  simpa [Nat.not_le.mpr hs] using h

theorem shift_one (c : Fin n) (s j : ℕ) :
    TU f R m j ≤ (TU f R m (j + 1)).comap
      ((univRepG f R).op c (1 * m + s)) := by
  have h := TU_cons f R m j (c, m + s)
  simpa using h

/-- The direct sum of the filtration steps. -/
def grNumerator : Submodule ℂ (ℕ →₀ UModG f R) :=
  Submodule.span ℂ
    {v | ∃ j x, x ∈ TU f R m j ∧ v = Finsupp.single j x}

/-- The next filtration step, embedded in the numerator at each grade. -/
def grDenominator : Submodule ℂ (ℕ →₀ UModG f R) :=
  Submodule.span ℂ
    {v | ∃ j x, x ∈ TU f R m (j + 1) ∧ v = Finsupp.single j x}

theorem grDenominator_le_numerator :
    grDenominator f R m ≤ grNumerator f R m := by
  rw [grDenominator, Submodule.span_le]
  rintro _ ⟨j, x, hx, rfl⟩
  apply Submodule.subset_span
  exact ⟨j, x, TU_mono f R m (by omega) hx, rfl⟩

/-- The denominator as a submodule of the direct-sum numerator. -/
def grKernel : Submodule ℂ (grNumerator f R m) :=
  (grDenominator f R m).comap (grNumerator f R m).subtype

/-- The associated graded vector space. -/
abbrev Gr := grNumerator f R m ⧸ grKernel f R m

/-- A homogeneous vector in the direct-sum numerator. -/
def gradedSingle (j : ℕ) (x : UModG f R) (hx : x ∈ TU f R m j) :
    grNumerator f R m :=
  ⟨Finsupp.single j x, Submodule.subset_span ⟨j, x, hx, rfl⟩⟩

theorem gradedSingle_mem_kernel (j : ℕ) (x : UModG f R)
    (hx : x ∈ TU f R m (j + 1)) :
    gradedSingle f R m j x (TU_mono f R m (by omega) hx) ∈ grKernel f R m :=
  Submodule.subset_span ⟨j, x, hx, rfl⟩

/-- Shift component `j` to `j+i` while applying the current operator. -/
def liftedOp (c : Fin n) (i s : ℕ) :
    (ℕ →₀ UModG f R) →ₗ[ℂ] (ℕ →₀ UModG f R) :=
  Finsupp.lmapDomain (UModG f R) ℂ (fun j : ℕ => j + i) ∘ₗ
    Finsupp.mapRange.linearMap ((univRepG f R).op c (i * m + s))

theorem liftedOp_single (c : Fin n) (i s j : ℕ) (x : UModG f R) :
    liftedOp f R m c i s (Finsupp.single j x) =
      Finsupp.single (j + i) ((univRepG f R).op c (i * m + s) x) := by
  simp [liftedOp]

theorem lifted_comm (a b : Fin n) (i j r s : ℕ)
    (v : ℕ →₀ UModG f R) :
    liftedOp f R m a i r (liftedOp f R m b j s v) -
      liftedOp f R m b j s (liftedOp f R m a i r v) =
        ∑ e, f a b e • liftedOp f R m e (i + j) (r + s) v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw =>
      simp only [map_add, Finset.sum_add_distrib, smul_add] at hv hw ⊢
      rw [← hv, ← hw]
      abel
  | single p x =>
      have hmode : (i * m + r) + (j * m + s) = (i + j) * m + (r + s) := by
        ring
      rw [liftedOp_single, liftedOp_single, liftedOp_single, liftedOp_single]
      rw [show p + j + i = p + (i + j) by omega,
        show p + i + j = p + (i + j) by omega]
      rw [← Finsupp.single_sub, (univRepG f R).comm a b (i * m + r)
        (j * m + s) x, hmode, Finsupp.single_finsetSum]
      apply Finset.sum_congr rfl
      intro e _
      rw [liftedOp_single, ← Finsupp.smul_single]

theorem grNumerator_inv (h : HighModeShift f R m) (c : Fin n) (i s : ℕ)
    (hs : s < m) :
    grNumerator f R m ≤ (grNumerator f R m).comap (liftedOp f R m c i s) := by
  rw [grNumerator, Submodule.span_le]
  rintro _ ⟨j, x, hx, rfl⟩
  change liftedOp f R m c i s (Finsupp.single j x) ∈ grNumerator f R m
  rw [liftedOp_single]
  exact Submodule.subset_span ⟨j + i, _, h c i s j hs hx, rfl⟩

theorem grDenominator_inv (h : HighModeShift f R m) (c : Fin n) (i s : ℕ)
    (hs : s < m) :
    grDenominator f R m ≤ (grDenominator f R m).comap (liftedOp f R m c i s) := by
  rw [grDenominator, Submodule.span_le]
  rintro _ ⟨j, x, hx, rfl⟩
  change liftedOp f R m c i s (Finsupp.single j x) ∈ grDenominator f R m
  rw [liftedOp_single]
  apply Submodule.subset_span
  refine ⟨j + i, _, ?_, rfl⟩
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    h c i s (j + 1) hs hx

theorem lifted_carry_mem (h : HighModeShift f R m) (e : Fin n)
    (i j r s : ℕ) (hr : r < m) (hs : s < m) (hc : m ≤ r + s) :
    grNumerator f R m ≤
      (grDenominator f R m).comap (liftedOp f R m e (i + j) (r + s)) := by
  rw [grNumerator, Submodule.span_le]
  rintro _ ⟨p, x, hx, rfl⟩
  change liftedOp f R m e (i + j) (r + s) (Finsupp.single p x) ∈
    grDenominator f R m
  rw [liftedOp_single]
  apply Submodule.subset_span
  let t := r + s - m
  have ht : t < m := by dsimp [t]; omega
  have hmode : (i + j) * m + (r + s) = (i + j + 1) * m + t := by
    have heq : r + s = m + t := by dsimp [t]; omega
    rw [heq]
    ring
  refine ⟨p + (i + j), _, ?_, rfl⟩
  rw [hmode]
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    h e (i + j + 1) t p ht hx

/-- The lifted operator restricted to the direct-sum numerator. -/
def restrictedOp (h : HighModeShift f R m) (c : Fin n) (i s : ℕ)
    (hs : s < m) :
    grNumerator f R m →ₗ[ℂ] grNumerator f R m where
  toFun v := ⟨liftedOp f R m c i s v.1, grNumerator_inv f R m h c i s hs v.2⟩
  map_add' v w := by
    apply Subtype.ext
    exact map_add (liftedOp f R m c i s) v.1 w.1
  map_smul' a v := by
    apply Subtype.ext
    exact map_smul (liftedOp f R m c i s) a v.1

theorem restrictedOp_kernel_inv (h : HighModeShift f R m) (c : Fin n)
    (i s : ℕ) (hs : s < m) :
    grKernel f R m ≤ (grKernel f R m).comap (restrictedOp f R m h c i s hs) := by
  intro v hv
  exact grDenominator_inv f R m h c i s hs hv

/-- A valid symbol, zero if its residual `t` mode is outside the truncation. -/
def grOp (h : HighModeShift f R m) (c : Fin n) (i s : ℕ) :
    Gr f R m →ₗ[ℂ] Gr f R m :=
  if hs : s < m then
    (grKernel f R m).mapQ (grKernel f R m) (restrictedOp f R m h c i s hs)
      (restrictedOp_kernel_inv f R m h c i s hs)
  else 0

theorem grOp_mk (h : HighModeShift f R m) (c : Fin n) (i s : ℕ)
    (hs : s < m) (v : grNumerator f R m) :
    grOp f R m h c i s ((grKernel f R m).mkQ v) =
      (grKernel f R m).mkQ (restrictedOp f R m h c i s hs v) := by
  simp [grOp, hs, Submodule.mapQ_apply]

theorem restrictedOp_single (h : HighModeShift f R m) (c : Fin n)
    (i s j : ℕ) (x : UModG f R) (hs : s < m)
    (hx : x ∈ TU f R m j) :
    restrictedOp f R m h c i s hs (gradedSingle f R m j x hx) =
      gradedSingle f R m (j + i)
        ((univRepG f R).op c (i * m + s) x) (h c i s j hs hx) := by
  apply Subtype.ext
  exact liftedOp_single f R m c i s j x

theorem grOp_single (h : HighModeShift f R m) (c : Fin n)
    (i s j : ℕ) (x : UModG f R) (hs : s < m)
    (hx : x ∈ TU f R m j) :
    grOp f R m h c i s
        ((grKernel f R m).mkQ (gradedSingle f R m j x hx)) =
      (grKernel f R m).mkQ
        (gradedSingle f R m (j + i)
          ((univRepG f R).op c (i * m + s) x) (h c i s j hs hx)) := by
  simp [grOp, hs, Submodule.mapQ_apply, restrictedOp_single]

theorem grOp_high_zero (h : HighModeShift f R m) (c : Fin n) (i s : ℕ)
    (hs : m ≤ s) : grOp f R m h c i s = 0 := by
  simp [grOp, Nat.not_lt.mpr hs]

/-- The corrected associated graded has the toroidal commutator, given the shift premise. -/
theorem grOp_comm (h : HighModeShift f R m) (a b : Fin n)
    (i j r s : ℕ) (v : Gr f R m) :
    grOp f R m h a i r (grOp f R m h b j s v) -
      grOp f R m h b j s (grOp f R m h a i r v) =
      if r + s < m then
        ∑ e, f a b e • grOp f R m h e (i + j) (r + s) v
      else 0 := by
  by_cases hr : r < m
  · by_cases hs : s < m
    · obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (grKernel f R m) v
      by_cases hc : r + s < m
      · rw [if_pos hc]
        simp only [grOp_mk f R m h a i r hr, grOp_mk f R m h b j s hs]
        have hsub :
            restrictedOp f R m h a i r hr (restrictedOp f R m h b j s hs y) -
              restrictedOp f R m h b j s hs (restrictedOp f R m h a i r hr y) =
              ∑ e, f a b e • restrictedOp f R m h e (i + j) (r + s) hc y := by
          apply Subtype.ext
          simpa only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul]
            using lifted_comm f R m a b i j r s y.1
        rw [← map_sub, hsub, map_sum]
        apply Finset.sum_congr rfl
        intro e _
        rw [map_smul, grOp_mk f R m h e (i + j) (r + s) hc]
      · rw [if_neg hc]
        simp only [grOp_mk f R m h a i r hr, grOp_mk f R m h b j s hs]
        rw [← map_sub]
        apply (Submodule.Quotient.mk_eq_zero (grKernel f R m)).mpr
        change
          liftedOp f R m a i r (liftedOp f R m b j s y.1) -
            liftedOp f R m b j s (liftedOp f R m a i r y.1) ∈
              grDenominator f R m
        rw [lifted_comm]
        apply Submodule.sum_mem
        intro e _
        exact Submodule.smul_mem _ _
          (lifted_carry_mem f R m h e i j r s hr hs (Nat.le_of_not_lt hc) y.2)
    · have hc : ¬ r + s < m := by omega
      simp [grOp_high_zero f R m h b j s (Nat.le_of_not_lt hs), hc]
  · have hc : ¬ r + s < m := by omega
    simp [grOp_high_zero f R m h a i r (Nat.le_of_not_lt hr), hc]

/-- The toroidal action on the corrected associated graded, conditional on the shift. -/
def grToroidal (h : HighModeShift f R m) : ToroidalModule f m (Gr f R m) where
  op := grOp f R m h
  high_zero := grOp_high_zero f R m h
  comm := grOp_comm f R m h

/-- The degree-zero class of the universal generator. -/
def grGenerator : Gr f R m :=
  (grKernel f R m).mkQ
    (gradedSingle f R m 0 (wUG f R) (by rw [TU_zero]; trivial))

/-- Replace each current mode by its `u` quotient and residual `t` mode. -/
def symbolLetters : List (Ltr n) → List (TLtr n)
  | [] => []
  | x :: l => (x.1, x.2 / m, x.2 % m) :: symbolLetters l

/-- Sum of the `u` degrees of the symbol letters. -/
def symbolDegree : List (Ltr n) → ℕ
  | [] => 0
  | x :: l => x.2 / m + symbolDegree l

theorem word_mem_shift (h : HighModeShift f R m) (hm : 1 ≤ m) :
    ∀ (l : List (Ltr n)) (j : ℕ) (x : UModG f R),
      x ∈ TU f R m j →
        wordOp (univRepG f R) l x ∈ TU f R m (j + symbolDegree m l)
  | [], j, x, hx => by simpa [symbolDegree] using hx
  | a :: l, j, x, hx => by
      have hi := word_mem_shift h hm l j x hx
      have hs : a.2 % m < m := Nat.mod_lt _ hm
      have hmode : (a.2 / m) * m + a.2 % m = a.2 := by
        rw [Nat.mul_comm, Nat.add_comm]
        exact Nat.mod_add_div _ _
      have hstep := h a.1 (a.2 / m) (a.2 % m) (j + symbolDegree m l) hs hi
      rw [hmode] at hstep
      simpa only [wordOp, symbolDegree, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hstep

theorem wordOpT_gr (h : HighModeShift f R m) (hm : 1 ≤ m) :
    ∀ (l : List (Ltr n)) (j : ℕ) (x : UModG f R)
      (hx : x ∈ TU f R m j),
      wordOpT (grToroidal f R m h) (symbolLetters m l)
          ((grKernel f R m).mkQ (gradedSingle f R m j x hx)) =
        (grKernel f R m).mkQ
          (gradedSingle f R m (j + symbolDegree m l)
            (wordOp (univRepG f R) l x) (word_mem_shift f R m h hm l j x hx))
  | [], j, x, hx => by simp [symbolLetters, symbolDegree, wordOpT, wordOp]
  | a :: l, j, x, hx => by
      have hs : a.2 % m < m := Nat.mod_lt _ hm
      have hmode : (a.2 / m) * m + a.2 % m = a.2 := by
        rw [Nat.mul_comm, Nat.add_comm]
        exact Nat.mod_add_div _ _
      change grOp f R m h a.1 (a.2 / m) (a.2 % m)
        (wordOpT (grToroidal f R m h) (symbolLetters m l)
          ((grKernel f R m).mkQ (gradedSingle f R m j x hx))) = _
      rw [wordOpT_gr h hm l j x hx]
      rw [grOp_single f R m h a.1 (a.2 / m) (a.2 % m)
        (j + symbolDegree m l) _ hs (word_mem_shift f R m h hm l j x hx)]
      congr 1
      apply Subtype.ext
      simp only [gradedSingle, symbolDegree, wordOp, hmode]
      congr 1
      omega

/-- Every original tail relation kills the symbol of the universal generator. -/
theorem gr_tail (h : HighModeShift f R m) (hm : 1 ≤ m)
    (t : List (Ltr n)) (ht : t ∈ R.tails) :
    wordOpT (grToroidal f R m h) (symbolLetters m t) (grGenerator f R m) = 0 := by
  have hw : wUG f R ∈ TU f R m 0 := by rw [TU_zero]; trivial
  change wordOpT (grToroidal f R m h) (symbolLetters m t)
    ((grKernel f R m).mkQ (gradedSingle f R m 0 (wUG f R) hw)) = 0
  rw [wordOpT_gr f R m h hm t 0 (wUG f R) hw]
  have hz := (univG_sat f R).tail t ht
  have hzero :
      gradedSingle f R m (0 + symbolDegree m t)
        (wordOp (univRepG f R) t (wUG f R))
        (word_mem_shift f R m h hm t 0 (wUG f R) hw) = 0 := by
    apply Subtype.ext
    simp [gradedSingle, hz]
  rw [hzero, map_zero]

end

end VOA.DeligneAudit.Toroidal

section AxiomAudit
#print axioms VOA.DeligneAudit.Toroidal.grDenominator_le_numerator
#print axioms VOA.DeligneAudit.Toroidal.shift_zero
#print axioms VOA.DeligneAudit.Toroidal.shift_one
#print axioms VOA.DeligneAudit.Toroidal.grNumerator_inv
#print axioms VOA.DeligneAudit.Toroidal.grDenominator_inv
#print axioms VOA.DeligneAudit.Toroidal.grOp_single
#print axioms VOA.DeligneAudit.Toroidal.lifted_carry_mem
#print axioms VOA.DeligneAudit.Toroidal.grOp_comm
#print axioms VOA.DeligneAudit.Toroidal.grToroidal
#print axioms VOA.DeligneAudit.Toroidal.gr_tail
end AxiomAudit
