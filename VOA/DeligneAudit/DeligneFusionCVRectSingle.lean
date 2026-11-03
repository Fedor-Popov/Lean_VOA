import VOA.DeligneAudit.DeligneFusionCVFamily
import VOA.DeligneAudit.DeligneFusionCVPolarization
import VOA.DeligneAudit.DeligneFusionCLNormal

/-!
# Sharp upper bounds for a single A₂ rectangle

The one-rectangle presentation of weight `k ω₁` is spanned by
`f₁(0)^a fθ(0)^b w`, with `a+b ≤ k`. The proof uses actual current
relations: PBW normal ordering, the three linear truncations, and
polarization of the highest-root CV relation. No dimension or fusion
identification is a premise.

The finite family gives the sharp upper counts 3, 6 and 10 for a single
fundamental, double-fundamental or triple-fundamental rectangle. Products
of rectangles require an additional branching/spanning theorem.
-/

namespace VOA.DeligneAudit.A2.CVRectSingle

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.CVPart
open VOA.DeligneAudit.CLNormal VOA.DeligneAudit.A2.CVFamily
open VOA.DeligneAudit.A2.CVPolarization

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The exact current highest-weight and rootwise CV data for one rectangle. -/
structure RectRel (R : CurrentModule bracketTable V) (w : V) (k : ℕ) : Prop where
  raising : ∀ (e : Fin 8), e.val < 3 → ∀ q, R.op e q w = 0
  cartan_pos : ∀ (h : Fin 8), 6 ≤ h.val → ∀ q, 1 ≤ q → R.op h q w = 0
  cartan_first : R.op 6 0 w = (k : ℂ) • w
  cartan_second : R.op 7 0 w = 0
  first : CVRel (R.op 3) [k] w
  second : CVRel (R.op 4) [] w
  highest : CVRel (R.op 5) [k] w

/-- Indices of the finite triangular spanning family. -/
abbrev Index (k : ℕ) := {i : Fin (k + 1) × Fin (k + 1) // i.1.val + i.2.val ≤ k}

def triangleWord (R : CurrentModule bracketTable V) (w : V) (k : ℕ) (i : Index k) : V :=
  (R.op 3 0 ^ i.val.1.val) ((R.op 5 0 ^ i.val.2.val) w)

def triangleSpan (R : CurrentModule bracketTable V) (w : V) (k : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ (Set.range (triangleWord R w k))

/-- The actual span of all current words on the generator. -/
def cyclicSpan (R : CurrentModule bracketTable V) (w : V) : Submodule ℂ V :=
  Submodule.span ℂ (Set.range fun l : List (Fin 8 × ℕ) => wordOp R l w)

variable {R : CurrentModule bracketTable V} {w : V} {k : ℕ}

theorem first_pos (h : RectRel R w k) (q : ℕ) (hq : 1 ≤ q) : R.op 3 q w = 0 :=
  trunc_of_cvrel h.first q (by simpa using hq)

theorem theta_pos (h : RectRel R w k) (q : ℕ) (hq : 1 ≤ q) : R.op 5 q w = 0 :=
  trunc_of_cvrel h.highest q (by simpa using hq)

theorem second_all (h : RectRel R w k) (q : ℕ) : R.op 4 q w = 0 :=
  trunc_of_cvrel h.second q (by simp)

/-- Polarization kills every zero-mode monomial beyond the triangular boundary. -/
theorem mixed_power_zero (h : RectRel R w k) (a b : ℕ) (hab : k < a + b) :
    (R.op 3 0 ^ a) ((R.op 5 0 ^ b) w) = 0 := by
  have hp := theta_cvrel_mixed R (h.raising 1 (by decide) 0) h.highest
    a b 0 0 (by omega) (by simp [T]; omega)
  simpa [mixedCoeff, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    Garland.Fs, Module.End.mul_apply] using hp

theorem triangle_power_mem (h : RectRel R w k) (a b : ℕ) :
    (R.op 3 0 ^ a) ((R.op 5 0 ^ b) w) ∈ triangleSpan R w k := by
  classical
  by_cases hab : a + b ≤ k
  · exact Submodule.subset_span
      ⟨⟨(⟨a, by omega⟩, ⟨b, by omega⟩), hab⟩, rfl⟩
  · rw [mixed_power_zero h a b (by omega)]
    exact Submodule.zero_mem _

/-- A commuting block vanishes if one of its letters annihilates its input. -/
theorem block_kills_of_mem (R : CurrentModule bracketTable V) (d : Fin 8)
    (hdd : ∀ i j, R.op d i * R.op d j = R.op d j * R.op d i)
    {v : V} : ∀ (l : List ℕ) (q : ℕ), q ∈ l → R.op d q v = 0 → Fx R d l v = 0
  | [], q, hq, _ => by simp at hq
  | r :: l, q, hq, hkill => by
      rcases List.mem_cons.mp hq with hqr | hq
      · have hkillr : R.op d r v = 0 := by simpa only [hqr] using hkill
        rw [Fx_cons, Module.End.mul_apply,
          comm_block_apply R d (R.op d r) (hdd r) l v, hkillr, map_zero]
      · rw [Fx_cons, Module.End.mul_apply,
          block_kills_of_mem R d hdd l q hq hkill, map_zero]

theorem block_zero_modes (R : CurrentModule bracketTable V) (d : Fin 8) :
    ∀ (l : List ℕ), (∀ q ∈ l, q = 0) → Fx R d l = R.op d 0 ^ l.length
  | [], _ => by simp
  | q :: l, hq => by
      have hzero : q = 0 := hq q List.mem_cons_self
      rw [Fx_cons, hzero, block_zero_modes R d l
        (fun r hr => hq r (List.mem_cons_of_mem _ hr))]
      simp only [List.length_cons, pow_succ']

/-- Every PBW normal word belongs to the explicit finite triangular span. -/
theorem normal_word_mem (h : RectRel R w k) (a b c : List ℕ) :
    nw R w a b c ∈ triangleSpan R w k := by
  classical
  cases c with
  | nil =>
      change Fx R 3 a (Fx R 5 b w) ∈ triangleSpan R w k
      by_cases ha : ∀ q ∈ a, q = 0
      · rw [block_zero_modes R 3 a ha]
        by_cases hb : ∀ q ∈ b, q = 0
        · rw [block_zero_modes R 5 b hb]
          exact triangle_power_mem h a.length b.length
        · push Not at hb
          obtain ⟨q, hq, hq0⟩ := hb
          rw [block_kills_of_mem R 5 (CVRoots.sl2_highest R).hFF b q hq
            (theta_pos h q (by omega)), map_zero]
          exact Submodule.zero_mem _
      · push Not at ha
        obtain ⟨q, hq, hq0⟩ := ha
        have hkill : R.op 3 q (Fx R 5 b w) = 0 := by
          rw [comm_block_apply R 5 (R.op 3 q) (c_f1f5 R q) b w,
            first_pos h q (by omega), map_zero]
        rw [block_kills_of_mem R 3 (CVRoots.sl2_first R).hFF a q hq hkill]
        exact Submodule.zero_mem _
  | cons q c =>
      unfold nw
      rw [block_kills_of_mem R 4 (CVRoots.sl2_second R).hFF (q :: c) q
        List.mem_cons_self (second_all h q), map_zero, map_zero]
      exact Submodule.zero_mem _

theorem nonlow_hw (h : RectRel R w k) (d : Fin 8) (q : ℕ) (hd : ¬ lowSl3 d) :
    R.op d q w ∈ ℂ ∙ w ∧ (1 ≤ q → R.op d q w = 0) := by
  unfold lowSl3 at hd
  by_cases h3 : d.val < 3
  · rw [h.raising d h3 q]
    exact ⟨Submodule.zero_mem _, fun _ => rfl⟩
  · have h6 : 6 ≤ d.val := by omega
    refine ⟨?_, fun hq => h.cartan_pos d h6 q hq⟩
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · have hd' : d = 6 ∨ d = 7 := by omega
      rcases hd' with rfl | rfl
      · rw [h.cartan_first]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
      · rw [h.cartan_second]
        exact Submodule.zero_mem _
    · rw [h.cartan_pos d h6 q hq]
      exact Submodule.zero_mem _

/-- The ungraded lowering-word normal form, using only the normal-ordering
operators rather than the character-counting assembly. -/
theorem lower_word_mem_normal : ∀ (l : List (Fin 8 × ℕ)),
    (∀ x ∈ l, lowSl3 x.1) → wordOp R l w ∈ NW R w (fun _ _ _ => True)
  | [], _ => nw_mem (a := []) (b := []) (c := []) trivial
  | (⟨d, q⟩ :: l), hl => by
      have ih := lower_word_mem_normal l (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      change R.op d q (wordOp R l w) ∈ _
      have hd := hl _ List.mem_cons_self
      unfold lowSl3 at hd
      change 3 ≤ d.val ∧ d.val < 6 at hd
      have hd' : d = 3 ∨ d = 4 ∨ d = 5 := by omega
      rcases hd' with rfl | rfl | rfl
      · exact map_NW _ (fun a b c _ => by
          rw [f1_nw]; exact nw_mem trivial) ih
      · exact map_NW _ (fun a b c _ =>
          NW_mono (fun _ _ _ _ => trivial) (f2_nw q a b c)) ih
      · exact map_NW _ (fun a b c _ => by
          rw [fθ_nw]; exact nw_mem trivial) ih

/-- Every current word is spanned by the explicit triangular family. -/
theorem cyclicSpan_le_triangleSpan (h : RectRel R w k) :
    cyclicSpan R w ≤ triangleSpan R w k := by
  classical
  rw [cyclicSpan, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  have hcyc : wordOp R l w ∈ cycDeg R w (SectorGraded.wordDeg l) :=
    Submodule.subset_span ⟨l, rfl, rfl⟩
  have hlow := cycDeg_le_sortedLow keySl3 lowSl3 R keySl3_low (nonlow_hw h)
    (SectorGraded.wordDeg l) hcyc
  apply Submodule.span_le.mpr ?_ hlow
  rintro _ ⟨l', _, hlow', _, rfl⟩
  have hnw := lower_word_mem_normal (R := R) (w := w) l' hlow'
  apply Submodule.span_le.mpr ?_ hnw
  rintro _ ⟨a, b, c, _, rfl⟩
  exact normal_word_mem h a b c

/-- A one-rectangle cyclic module is finite dimensional and bounded by its
finite triangular family, without a fusion or irreducibility premise. -/
theorem rectangle_bound (h : RectRel R w k) :
    FiniteDimensional ℂ (cyclicSpan R w) ∧
      Module.finrank ℂ (cyclicSpan R w) ≤ Fintype.card (Index k) := by
  classical
  have hle := cyclicSpan_le_triangleSpan h
  haveI : FiniteDimensional ℂ (triangleSpan R w k) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  haveI : FiniteDimensional ℂ (cyclicSpan R w) := Submodule.finiteDimensional_of_le hle
  refine ⟨inferInstance, (Submodule.finrank_mono hle).trans ?_⟩
  exact finrank_range_le_card (triangleWord R w k)

theorem card_index_one : Fintype.card (Index 1) = 3 := by decide
theorem card_index_two : Fintype.card (Index 2) = 6 := by decide
theorem card_index_three : Fintype.card (Index 3) = 10 := by decide

theorem rectRel_fund (h : CV3Rel R w (1, 0) (0, 0) (0, 0) 0) : RectRel R w 1 := by
  refine ⟨h.raising, h.cartan_pos, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using h.cartan_first
  · simpa using h.cartan_second
  · simpa [parts] using h.first
  · simpa [parts] using h.second
  · simpa [parts] using h.highest

theorem rectRel_double (h : CV3Rel R w (0, 0) (1, 0) (0, 0) 0) : RectRel R w 2 := by
  refine ⟨h.raising, h.cartan_pos, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using h.cartan_first
  · simpa using h.cartan_second
  · simpa [parts] using h.first
  · simpa [parts] using h.second
  · simpa [parts] using h.highest

theorem rectRel_triple (h : CV3Rel R w (0, 0) (0, 0) (1, 0) 0) : RectRel R w 3 := by
  refine ⟨h.raising, h.cartan_pos, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using h.cartan_first
  · simpa using h.cartan_second
  · simpa [parts] using h.first
  · simpa [parts] using h.second
  · simpa [parts] using h.highest

theorem single_fund_bound (h : CV3Rel R w (1, 0) (0, 0) (0, 0) 0) :
    FiniteDimensional ℂ (cyclicSpan R w) ∧ Module.finrank ℂ (cyclicSpan R w) ≤ 3 := by
  simpa only [card_index_one] using rectangle_bound (rectRel_fund h)

theorem single_double_bound (h : CV3Rel R w (0, 0) (1, 0) (0, 0) 0) :
    FiniteDimensional ℂ (cyclicSpan R w) ∧ Module.finrank ℂ (cyclicSpan R w) ≤ 6 := by
  simpa only [card_index_two] using rectangle_bound (rectRel_double h)

theorem single_triple_bound (h : CV3Rel R w (0, 0) (0, 0) (1, 0) 0) :
    FiniteDimensional ℂ (cyclicSpan R w) ∧ Module.finrank ℂ (cyclicSpan R w) ≤ 10 := by
  simpa only [card_index_three] using rectangle_bound (rectRel_triple h)

end

end VOA.DeligneAudit.A2.CVRectSingle

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.CVRectSingle.cyclicSpan_le_triangleSpan
#print axioms VOA.DeligneAudit.A2.CVRectSingle.rectangle_bound
#print axioms VOA.DeligneAudit.A2.CVRectSingle.single_fund_bound
#print axioms VOA.DeligneAudit.A2.CVRectSingle.single_double_bound
#print axioms VOA.DeligneAudit.A2.CVRectSingle.single_triple_bound
end AxiomAudit
