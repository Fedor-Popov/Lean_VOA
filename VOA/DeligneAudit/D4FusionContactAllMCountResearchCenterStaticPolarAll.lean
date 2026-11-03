import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterStaticPolarTransfer
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterStaticPolarDataQ0
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterStaticPolarDataQ1
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterStaticPolarDataQ2
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterStaticPolarDataQ3
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterStaticPolarDataQ4
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterStaticPolarDataQ5
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterStaticPolarDataQ6
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterStaticPolarDataQ7
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterStaticPolarDataC0
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterStaticPolarDataC1
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterStaticPolarDataC2

/-! All 74 static C-color templates, as theorems about original whole currents.
The quintic templates are every degree-5 color word with bit counts (2,2,2);
quartic class k is every degree-4 word with bit counts (2,2,2) - bits(k).
Hence every static degree-5 word of bit weight (2,2,2), and every static
degree-4 word whose three bit counts lie in {1,2}, IN ANY ORDER, has its
whole coefficient 2m-3 in the literal quadratic/cubic polar ideal J, for all m.
This closes the static certificate stage only: original C-contact coverage,
reduced completion and the sharp count remain open. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.CenterStaticPolar
open VOA.DeligneAudit.D4FusionContact.Polynomial

def staticCerts : List Cert :=
  [certsQ0,certsQ1,certsQ2,certsQ3,certsQ4,certsQ5,certsQ6,certsQ7,
    certsC0,certsC1,certsC2].flatten

theorem staticCerts_valid : ∀ C ∈ staticCerts, C.valid := by
  intro C hC
  obtain ⟨l,hl,hC⟩ := List.mem_flatten.mp hC
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact certsQ0_valid C hC
  · exact certsQ1_valid C hC
  · exact certsQ2_valid C hC
  · exact certsQ3_valid C hC
  · exact certsQ4_valid C hC
  · exact certsQ5_valid C hC
  · exact certsQ6_valid C hC
  · exact certsQ7_valid C hC
  · exact certsC0_valid C hC
  · exact certsC1_valid C hC
  · exact certsC2_valid C hC

def staticTargets : List (List (Fin 8)) := staticCerts.map Cert.target

theorem staticTargets_length : staticTargets.length = 74 := by decide +kernel

theorem staticTargets_nodup : staticTargets.Nodup := by decide +kernel

/-- The whole original static word of every template lies in J, for all m. -/
theorem staticTarget_coeff_mem (m : ℕ) (w : List (Fin 8)) (hw : w ∈ staticTargets) :
    PowerSeries.coeff (2 * m - 3) ((w.map fun i => AllM.current m (cubeColor i)).prod) ∈
      quadraticCubicPolarIdeal m := by
  obtain ⟨C,hC,rfl⟩ := List.mem_map.mp hw
  exact C.original_coeff_mem (staticCerts_valid C hC) m

/-- The number of colors of `w` whose cube bit `a` is set. -/
def bitCount (w : List (Fin 8)) (a : ℕ) : ℕ := (w.map fun i => i.val / 2 ^ a % 2).sum

def QuinticShape (w : List (Fin 8)) : Prop :=
  w.length = 5 ∧ bitCount w 0 = 2 ∧ bitCount w 1 = 2 ∧ bitCount w 2 = 2

def QuarticShape (w : List (Fin 8)) : Prop :=
  w.length = 4 ∧ (bitCount w 0 = 1 ∨ bitCount w 0 = 2) ∧
    (bitCount w 1 = 1 ∨ bitCount w 1 = 2) ∧ (bitCount w 2 = 1 ∨ bitCount w 2 = 2)

instance (w : List (Fin 8)) : Decidable (QuinticShape w) :=
  inferInstanceAs (Decidable (w.length = 5 ∧ bitCount w 0 = 2 ∧ bitCount w 1 = 2 ∧
    bitCount w 2 = 2))

instance (w : List (Fin 8)) : Decidable (QuarticShape w) :=
  inferInstanceAs (Decidable (w.length = 4 ∧ (bitCount w 0 = 1 ∨ bitCount w 0 = 2) ∧
    (bitCount w 1 = 1 ∨ bitCount w 1 = 2) ∧ (bitCount w 2 = 1 ∨ bitCount w 2 = 2)))

/-- Kernel enumeration of every SORTED quintic word of the shape. -/
theorem quintic_sorted_mem : ∀ a b : Fin 8, a ≤ b → ∀ c : Fin 8, b ≤ c →
    ∀ d : Fin 8, c ≤ d → ∀ e : Fin 8, d ≤ e →
      QuinticShape [a,b,c,d,e] → [a,b,c,d,e] ∈ staticTargets := by decide +kernel

/-- Kernel enumeration of every SORTED quartic word of the shape. -/
theorem quartic_sorted_mem : ∀ a b : Fin 8, a ≤ b → ∀ c : Fin 8, b ≤ c →
    ∀ d : Fin 8, c ≤ d →
      QuarticShape [a,b,c,d] → [a,b,c,d] ∈ staticTargets := by decide +kernel

theorem bitCount_perm {w v : List (Fin 8)} (h : w.Perm v) (a : ℕ) :
    bitCount w a = bitCount v a := by
  unfold bitCount
  exact (h.map _).sum_eq

def sortWord (w : List (Fin 8)) : List (Fin 8) := w.insertionSort (· ≤ ·)

theorem sortWord_perm (w : List (Fin 8)) : (sortWord w).Perm w :=
  List.perm_insertionSort _ w

theorem sortWord_pairwise (w : List (Fin 8)) : (sortWord w).Pairwise (· ≤ ·) :=
  List.pairwise_insertionSort _ w

/-- Every quintic word of the shape sorts to a template. -/
theorem quinticShape_sort_mem (w : List (Fin 8)) (hw : QuinticShape w) :
    sortWord w ∈ staticTargets := by
  have hp := sortWord_perm w
  have hs := sortWord_pairwise w
  have hq : QuinticShape (sortWord w) := by
    obtain ⟨hl,h0,h1,h2⟩ := hw
    exact ⟨hp.length_eq.trans hl,(bitCount_perm hp 0).trans h0,
      (bitCount_perm hp 1).trans h1,(bitCount_perm hp 2).trans h2⟩
  generalize sortWord w = s at hs hq
  have hl := hq.1
  rcases s with _|⟨a,_|⟨b,_|⟨c,_|⟨d,_|⟨e,_|⟨f,s⟩⟩⟩⟩⟩⟩ <;> simp at hl
  exact quintic_sorted_mem a b (List.rel_of_pairwise_cons hs (by simp))
    c (List.rel_of_pairwise_cons hs.of_cons (by simp))
    d (List.rel_of_pairwise_cons hs.of_cons.of_cons (by simp))
    e (List.rel_of_pairwise_cons hs.of_cons.of_cons.of_cons (by simp)) hq

/-- Every quartic word of the shape sorts to a template. -/
theorem quarticShape_sort_mem (w : List (Fin 8)) (hw : QuarticShape w) :
    sortWord w ∈ staticTargets := by
  have hp := sortWord_perm w
  have hs := sortWord_pairwise w
  have hq : QuarticShape (sortWord w) := by
    obtain ⟨hl,h0,h1,h2⟩ := hw
    refine ⟨hp.length_eq.trans hl,?_,?_,?_⟩
    · rwa [bitCount_perm hp 0]
    · rwa [bitCount_perm hp 1]
    · rwa [bitCount_perm hp 2]
  generalize sortWord w = s at hs hq
  have hl := hq.1
  rcases s with _|⟨a,_|⟨b,_|⟨c,_|⟨d,_|⟨e,s⟩⟩⟩⟩⟩ <;> simp at hl
  exact quartic_sorted_mem a b (List.rel_of_pairwise_cons hs (by simp))
    c (List.rel_of_pairwise_cons hs.of_cons (by simp))
    d (List.rel_of_pairwise_cons hs.of_cons.of_cons (by simp)) hq

theorem word_prod_perm (m : ℕ) {w v : List (Fin 8)} (h : w.Perm v) :
    (w.map fun i => AllM.current m (cubeColor i)).prod =
      (v.map fun i => AllM.current m (cubeColor i)).prod :=
  (h.map _).prod_eq

/-- MAIN QUINTIC: every static quintic C-word of bit weight (2,2,2), in any
color order, has whole original coefficient 2m-3 in J, for all m. -/
theorem quintic_static_coeff_mem (m : ℕ) (w : List (Fin 8)) (hw : QuinticShape w) :
    PowerSeries.coeff (2 * m - 3) ((w.map fun i => AllM.current m (cubeColor i)).prod) ∈
      quadraticCubicPolarIdeal m := by
  rw [← word_prod_perm m (sortWord_perm w)]
  exact staticTarget_coeff_mem m _ (quinticShape_sort_mem w hw)

/-- MAIN QUARTIC: every static quartic C-word whose three bit counts lie in
{1,2}, in any color order, has whole original coefficient 2m-3 in J. -/
theorem quartic_static_coeff_mem (m : ℕ) (w : List (Fin 8)) (hw : QuarticShape w) :
    PowerSeries.coeff (2 * m - 3) ((w.map fun i => AllM.current m (cubeColor i)).prod) ∈
      quadraticCubicPolarIdeal m := by
  rw [← word_prod_perm m (sortWord_perm w)]
  exact staticTarget_coeff_mem m _ (quarticShape_sort_mem w hw)

/-- The same words are original candidate-ideal relations. -/
theorem quintic_static_coeff_mem_candidate (m : ℕ) (w : List (Fin 8))
    (hw : QuinticShape w) :
    PowerSeries.coeff (2 * m - 3) ((w.map fun i => AllM.current m (cubeColor i)).prod) ∈
      AllM.candidateIdeal m :=
  quadraticCubicPolarIdeal_le_candidate m (quintic_static_coeff_mem m w hw)

theorem quartic_static_coeff_mem_candidate (m : ℕ) (w : List (Fin 8))
    (hw : QuarticShape w) :
    PowerSeries.coeff (2 * m - 3) ((w.map fun i => AllM.current m (cubeColor i)).prod) ∈
      AllM.candidateIdeal m :=
  quadraticCubicPolarIdeal_le_candidate m (quartic_static_coeff_mem m w hw)

#print axioms staticCerts_valid
#print axioms staticTargets_nodup
#print axioms quintic_sorted_mem
#print axioms quartic_sorted_mem
#print axioms quintic_static_coeff_mem
#print axioms quartic_static_coeff_mem
#print axioms quintic_static_coeff_mem_candidate
#print axioms quartic_static_coeff_mem_candidate
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.CenterStaticPolar
