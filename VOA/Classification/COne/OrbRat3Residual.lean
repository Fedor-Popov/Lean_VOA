import VOA.Classification.COne.OrbRat3Inner

/-! # The five outer products that are not kernel-certified

For `n = 0, 1, 2, 3, 4` the outer product `U₍₁₆₋ₙ₎ U₍ₙ₎ h(-1)1` needs the neutral generator `J`
acting on charge-zero states of weight up to `12 - n` with up to nine oscillators.  The kernel
evaluation of these terms exceeded the 10 GB per-process memory budget, so they are NOT proved
here.  They are isolated as the closed, decidable proposition `V8OuterCertificates` (a statement
about five explicit executable lists; the compiled interpreter evaluates both sides equal).
Everything downstream is proved from it.

`outer_of_cert` converts each list identity into the actual `V₈` identity
`U₍₁₆₋ₙ₎ U₍ₙ₎ h(-1)1 = w h(-1)1`, using the proved soundness of the evaluator.
-/
set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.OrbRat3
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e LatMod

/-- The executable outer certificate for `U₍₁₆₋ₙ₎` on the inner state `Z` (cutoff `13 - n`). -/
def OuterCert (n : ℕ) (Z : St) (w : ℚ) : Prop :=
  bucket [-2, 0, 2] (actU (16 - (n : ℤ)) (13 - n) Z) = [(-2, []), (0, [(w, [1])]), (2, [])]

/-- OPEN (decidable; evaluated true by the compiled interpreter, NOT kernel-checked): the five
outer products for `n = 0, 1, 2, 3, 4`. -/
def V8OuterCertificates : Prop :=
  OuterCert 0 Z0 (-379468800) ∧ OuterCert 1 Z1 (-86184000) ∧
    OuterCert 2 Z2 (-16416000) ∧ OuterCert 3 Z3 (-2462400) ∧ OuterCert 4 Z4 (-259200)

theorem actE_sectors (k : ℤ) (s : St) (hs : ∀ p ∈ s, p.1 ∈ [-1, 1]) :
    ∀ p ∈ actE k s, p.1 ∈ [-2, 0, 2] := by
  intro p hp
  simp only [actE, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain ⟨q, hq, hp⟩ := hp
  have := hs q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
  rcases hp with rfl | rfl <;> omega

theorem actJ_sectors (k : ℤ) (s : St) (D : List ℤ) (hs : ∀ p ∈ s, p.1 ∈ D) :
    ∀ p ∈ actJ k s, p.1 ∈ D := by
  intro p hp
  simp only [actJ, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact hs q hq

theorem scaleSt_sectors (q : ℚ) (s : St) (D : List ℤ) (hs : ∀ p ∈ s, p.1 ∈ D) :
    ∀ p ∈ scaleSt q s, p.1 ∈ D := by
  intro p hp
  simp only [scaleSt, List.mem_map] at hp
  obtain ⟨r, hr, rfl⟩ := hp
  exact hs r hr

theorem actU_sectors (k : ℤ) (B : ℕ) (s : St) (hs : ∀ p ∈ s, p.1 ∈ [-1, 1]) :
    ∀ p ∈ actU k B s, p.1 ∈ [-2, 0, 2] := by
  intro p hp
  simp only [actU, List.mem_flatMap] at hp
  obtain ⟨i, -, hp⟩ := hp
  simp only [termU] at hp
  refine scaleSt_sectors _ _ _ ?_ p hp
  intro r hr
  simp only [List.mem_append] at hr
  rcases hr with ((hr | hr) | hr) | hr
  · exact actJ_sectors _ _ _ (actE_sectors _ _ hs) r hr
  · exact scaleSt_sectors _ _ _ (actE_sectors _ _ (actJ_sectors _ _ _ hs)) r hr
  · exact scaleSt_sectors _ _ _ (actE_sectors _ _ (actJ_sectors _ _ _ hs)) r hr
  · exact actJ_sectors _ _ _ (actE_sectors _ _ hs) r hr

/-- A sound outer certificate gives the actual `V₈` identity. -/
theorem outer_of_cert (n : ℕ) (hn : n ≤ 8) (Z : St) (w : ℚ)
    (hZ : (V2m 4 four_ge_one).smul Uc n hV = evalSt Z) (hZs : ∀ p ∈ Z, p.1 ∈ [-1, 1])
    (h : OuterCert n Z w) :
    (V2m 4 four_ge_one).smul Uc (16 - (n : ℤ)) ((V2m 4 four_ge_one).smul Uc n hV) =
      (w : ℂ) • hV := by
  have hz : (V2m 4 four_ge_one).smul Uc n hV ∈ (V2m 4 four_ge_one).grading (9 - n) := by
    have := (V2m 4 four_ge_one).smul_mem_grading Uc_mem hV_mem (n : ℤ)
    convert this using 2; ring
  rw [hZ] at hz ⊢
  rw [actU_sound (16 - (n : ℤ)) (13 - n) Z hz (by omega) (by omega),
    ← evalSt_bucket _ (by decide) _ (actU_sectors _ _ _ hZs), h, evalSt_three, sector_one]

theorem Z_sectors_0 : ∀ p ∈ Z0, p.1 ∈ [-1, 1] := by decide
theorem Z_sectors_1 : ∀ p ∈ Z1, p.1 ∈ [-1, 1] := by decide
theorem Z_sectors_2 : ∀ p ∈ Z2, p.1 ∈ [-1, 1] := by decide
theorem Z_sectors_3 : ∀ p ∈ Z3, p.1 ∈ [-1, 1] := by decide
theorem Z_sectors_4 : ∀ p ∈ Z4, p.1 ∈ [-1, 1] := by decide

end VOA.Classification.COne.OrbRat3
