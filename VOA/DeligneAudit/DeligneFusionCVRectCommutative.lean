import VOA.DeligneAudit.DeligneFusionCVRectSingle
import VOA.DeligneAudit.DeligneFusionCVFinite

/-!
# The actual two-color commutative presentation for one orientation

The one-orientation three-level CV family has an empty second-root
partition. PBW therefore leaves only the commuting first-root and
highest-root currents, truncated at the common partition length.
Polarization gives every mixed coefficient relation at the optimized
clipped-partition bound. These are actual source relations, with no
fusion presentation or dimension premise.

The clipped bound is the degree-reversed form of the coefficient ideal
in FJKLM, arXiv:math/0208156, Section 2.3. The product dimension bound
still requires the generalized-site spanning recursion; in particular,
its normalized-integration ideal-preservation step is not proved here.
-/

namespace VOA.DeligneAudit.A2.CVRectCommutative

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.CVPart
open VOA.DeligneAudit.CLNormal VOA.DeligneAudit.A2.CVFamily
open VOA.DeligneAudit.A2.CVPolarization

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule bracketTable V} {w : V} {e n r : ℕ}

/-- The sum of the partition parts clipped at the total mixed power. -/
def clippedSum (ξ : List ℕ) (d : ℕ) : ℕ := (ξ.map (fun a => min d a)).sum

theorem clippedSum_parts (r n e d : ℕ) :
    clippedSum (parts r n e) d = r * min d 3 + n * min d 2 + e * min d 1 := by
  simp [clippedSum, parts, Nat.add_assoc]

/-- For parts at most three, the optimal CV cutoff is achieved at one of
three explicit indices. No asymptotic or partition convexity premise is used. -/
theorem parts_region_optimizer (r n e d : ℕ) (hd : 1 ≤ d) :
    ∃ k, d * k + T k (parts r n e) = clippedSum (parts r n e) d := by
  rcases (show d = 1 ∨ d = 2 ∨ 3 ≤ d by omega) with rfl | rfl | hd3
  · refine ⟨r + n + e, ?_⟩
    rw [T_of_le _ _ (by rw [parts_length]), clippedSum_parts]
    simp
  · refine ⟨r + n, ?_⟩
    rw [parts_tail, clippedSum_parts]
    norm_num
    omega
  · refine ⟨0, ?_⟩
    rw [clippedSum_parts, Nat.min_eq_right hd3,
      Nat.min_eq_right (show 2 ≤ d by omega), Nat.min_eq_right (show 1 ≤ d by omega)]
    simp [T, parts, Nat.add_assoc]

/-- A single highest-root CV relation supplies all two-color coefficients
past the exact clipped-partition threshold. -/
theorem mixedCoeff_zero_of_clipped (he2 : R.op 1 0 w = 0)
    (hCV : CVRel (R.op 5) (parts r n e) w) (p q s : ℕ)
    (hd : 1 ≤ p + q) (hs : clippedSum (parts r n e) (p + q) < s + (p + q)) :
    mixedCoeff (R.op 3) (R.op 5) p q s w = 0 := by
  obtain ⟨k, hk⟩ := parts_region_optimizer r n e (p + q) hd
  apply theta_cvrel_mixed R he2 hCV p q s k hd
  omega

/-- The actual one-orientation source satisfies the optimized mixed ideal
relations; no proposed target presentation is assumed. -/
theorem mixedCoeff_zero (h : CV3Rel R w (e, 0) (n, 0) (r, 0) 0) (p q s : ℕ)
    (hd : 1 ≤ p + q) (hs : clippedSum (parts r n e) (p + q) < s + (p + q)) :
    mixedCoeff (R.op 3) (R.op 5) p q s w = 0 := by
  apply mixedCoeff_zero_of_clipped (h.raising 1 (by decide) 0) ?_ p q s hd hs
  simpa only [Nat.add_zero] using h.highest

theorem second_all (h : CV3Rel R w (e, 0) (n, 0) (r, 0) 0) (s : ℕ) :
    R.op 4 s w = 0 := by
  apply trunc_of_cvrel h.second s
  simp [parts]

theorem first_trunc (h : CV3Rel R w (e, 0) (n, 0) (r, 0) 0) (s : ℕ)
    (hs : r + n + e ≤ s) : R.op 3 s w = 0 := by
  apply trunc_of_cvrel h.first s
  simpa only [parts_length, Nat.add_zero] using hs

theorem theta_trunc (h : CV3Rel R w (e, 0) (n, 0) (r, 0) 0) (s : ℕ)
    (hs : r + n + e ≤ s) : R.op 5 s w = 0 := by
  apply trunc_of_cvrel h.highest s
  simpa only [parts_length, Nat.add_zero] using hs

/-- The finite set of current modes in each of the two commuting colors.
Word lengths are unrestricted until a spanning recursion is proved. -/
def colorSpan (R : CurrentModule bracketTable V) (w : V) (N : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ a b : List ℕ,
    (∀ s ∈ a, s < N) ∧ (∀ s ∈ b, s < N) ∧ v = Fx R 3 a (Fx R 5 b w)}

/-- Every negative PBW word reduces to the two truncated commuting colors. -/
theorem normal_word_mem (h : CV3Rel R w (e, 0) (n, 0) (r, 0) 0)
    (a b c : List ℕ) : nw R w a b c ∈ colorSpan R w (r + n + e) := by
  classical
  cases c with
  | nil =>
      change Fx R 3 a (Fx R 5 b w) ∈ colorSpan R w (r + n + e)
      by_cases ha : ∀ s ∈ a, s < r + n + e
      · by_cases hb : ∀ s ∈ b, s < r + n + e
        · exact Submodule.subset_span ⟨a, b, ha, hb, rfl⟩
        · push Not at hb
          obtain ⟨s, hs, hsN⟩ := hb
          rw [CVRectSingle.block_kills_of_mem R 5 (CVRoots.sl2_highest R).hFF b s hs
            (theta_trunc h s (by omega)), map_zero]
          exact Submodule.zero_mem _
      · push Not at ha
        obtain ⟨s, hs, hsN⟩ := ha
        have hkill : R.op 3 s (Fx R 5 b w) = 0 := by
          rw [comm_block_apply R 5 (R.op 3 s) (c_f1f5 R s) b w,
            first_trunc h s (by omega), map_zero]
        rw [CVRectSingle.block_kills_of_mem R 3 (CVRoots.sl2_first R).hFF a s hs hkill]
        exact Submodule.zero_mem _
  | cons s c =>
      unfold nw
      rw [CVRectSingle.block_kills_of_mem R 4 (CVRoots.sl2_second R).hFF (s :: c) s
        List.mem_cons_self (second_all h s), map_zero, map_zero]
      exact Submodule.zero_mem _

/-- The actual whole cyclic submodule is spanned by words in those two
commuting colors. This is a relation transfer, not an evaluation-model bound. -/
theorem cyclicSpan_le_colorSpan (h : CV3Rel R w (e, 0) (n, 0) (r, 0) 0) :
    CVRectSingle.cyclicSpan R w ≤ colorSpan R w (r + n + e) := by
  classical
  rw [CVRectSingle.cyclicSpan, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  have hcyc : wordOp R l w ∈ cycDeg R w (SectorGraded.wordDeg l) :=
    Submodule.subset_span ⟨l, rfl, rfl⟩
  have hlow := CVFinite.cycDeg_le_sortedFin_of_cv3Rel h (SectorGraded.wordDeg l) hcyc
  apply Submodule.span_le.mpr ?_ hlow
  rintro _ ⟨l', _, hlow', _, rfl⟩
  have hnw := CVRectSingle.lower_word_mem_normal (R := R) (w := w) l' hlow'
  apply Submodule.span_le.mpr ?_ hnw
  rintro _ ⟨a, b, c, _, rfl⟩
  exact normal_word_mem h a b c

theorem colorSpan_le_cyclicSpan (N : ℕ) :
    colorSpan R w N ≤ CVRectSingle.cyclicSpan R w := by
  classical
  apply Submodule.span_le.mpr
  rintro v ⟨a, b, _, _, rfl⟩
  have hw : Fx R 3 a (Fx R 5 b w) =
      wordOp R ((a.map fun s => (3, s)) ++ b.map fun s => (5, s)) w := by
    rw [wordOp_append, wordOp_map, wordOp_map]
  exact Submodule.subset_span ⟨_, hw.symm⟩

theorem cyclicSpan_eq_colorSpan (h : CV3Rel R w (e, 0) (n, 0) (r, 0) 0) :
    CVRectSingle.cyclicSpan R w = colorSpan R w (r + n + e) :=
  le_antisymm (cyclicSpan_le_colorSpan h) (colorSpan_le_cyclicSpan _)

end

end VOA.DeligneAudit.A2.CVRectCommutative

#print axioms VOA.DeligneAudit.A2.CVRectCommutative.parts_region_optimizer
#print axioms VOA.DeligneAudit.A2.CVRectCommutative.mixedCoeff_zero
#print axioms VOA.DeligneAudit.A2.CVRectCommutative.cyclicSpan_eq_colorSpan
