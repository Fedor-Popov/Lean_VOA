import VOA.DeligneAudit.D4LevelReductionCorePiece
import VOA.DeligneAudit.D4LeviKSRyWick

/-!
The two complete-symmetric relation families at the bottom of a level.
Conversion by the highest Levi lowering root sends the adjoint radical letter
to the highest-root radical letter. Every incomplete contraction has strictly
larger Levi level, so the full contraction gives the second Grassmannian tail.
-/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- A fixed three-letter multiplicity space lies in its grade and level filtration term. -/
theorem radicalCountSpan_le_levelFiltration
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (x y z : ℕ) (κ p : ℤ)
    (hg : (m : ℤ) - (x + y + z) = κ) (hp : p ≤ (m : ℤ) + x - y - z) :
    xyzCountSpan ρ w x y z ≤ levelFiltration ρ w m κ p := by
  rw [xyzCountSpan, Submodule.span_le]
  rintro v ⟨l, he, hx, hu, hup, hy, hz, rfl⟩
  apply keyOrbit_le_levelFiltration_of_sat ρ w m h κ p (wordKey l) _ _
    (keyLayer_le_orbit ρ w _ (radicalWord_mem_key ρ w l))
  · simpa [keyAlphaGrade, keyDepth, wordKey, he, hx, hu, hup, hy, hz] using hg
  · simpa [keyLeviLevel, wordKey, he, hx, hy, hz] using hp

/-- Coefficients of signed highest-Levi-root current powers preserve every level term. -/
theorem highestLevi_powerCoeff_mem (κ p : ℤ) (n s : ℕ)
    {v : V} (hv : v ∈ levelFiltration ρ w m κ p) :
    PowerSeries.coeff s (fCurrent (fTopOp ρ) ^ n) v ∈
      levelFiltration ρ w m κ p := by
  induction n generalizing s v with
  | zero =>
      by_cases hs : s = 0
      · subst s
        simpa using hv
      · simp [hs]
  | succ n ih =>
      rw [pow_succ, PowerSeries.coeff_mul]
      change (∑ q ∈ Finset.antidiagonal s,
        PowerSeries.coeff q.1 (fCurrent (fTopOp ρ) ^ n) *
          PowerSeries.coeff q.2 (fCurrent (fTopOp ρ))) • v ∈ _
      rw [Finset.sum_smul]
      apply Submodule.sum_mem
      intro q _
      have hf : fTopOp ρ q.2 v ∈ levelFiltration ρ w m κ p := by
        exact Submodule.neg_mem _ (levelFiltration_stable ρ w m κ p 23 q.2 ⟨9, rfl⟩ hv)
      simpa [fCurrent, fTopOp, mul_smul] using ih q.1 hf

/-- Incomplete highest-root contractions lie strictly above the bottom level. -/
theorem bottomConversionTerm_mem_next
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (a c s : ℕ)
    (pair : List ℕ × List ℕ)
    (hp : pair ∈ choices (List.replicate a 0 ++ List.replicate c 0))
    (hshort : pair.2.length < c) :
    conversionTerm (fTopOp ρ) (xOp ρ) (zOp ρ) c s pair w ∈
      levelFiltration ρ w m ((m : ℤ) - (a + c)) ((m : ℤ) + a - c + 1) := by
  let N := levelFiltration ρ w m ((m : ℤ) - (a + c)) ((m : ℤ) + a - c + 1)
  have hlen := choices_length (List.replicate a 0 ++ List.replicate c 0) pair hp
  simp only [List.length_append, List.length_replicate] at hlen
  have hterm (q : ℕ × ℕ) :
      ((PowerSeries.coeff q.1 (fCurrent (fTopOp ρ) ^ (c - pair.2.length)) *
          aWord (xOp ρ) pair.1) * PowerSeries.coeff q.2 (bWord (zOp ρ) pair.2)) • w ∈ N := by
    have hz := xyzCountSpan_z_coeff ρ w pair.2 q.2 0 0 0 (xyzCountSpan_zero ρ w)
    have hx := xyzCountSpan_x_word ρ w pair.1 0 0 pair.2.length (by simpa using hz)
    have hb : (aWord (xOp ρ) pair.1 *
        PowerSeries.coeff q.2 (bWord (zOp ρ) pair.2)) • w ∈ N := by
      apply radicalCountSpan_le_levelFiltration ρ w m h pair.1.length 0 pair.2.length
        _ _ (by omega) (by omega)
      simpa [aWord, mul_smul] using hx
    simpa [N, mul_assoc, mul_smul] using highestLevi_powerCoeff_mem ρ w m
      _ _ (c - pair.2.length) q.1 hb
  have hsum :
      (∑ q ∈ Finset.antidiagonal s,
        (PowerSeries.coeff q.1 (fCurrent (fTopOp ρ) ^ (c - pair.2.length)) *
          aWord (xOp ρ) pair.1) * PowerSeries.coeff q.2 (bWord (zOp ρ) pair.2)) • w ∈ N := by
    rw [Finset.sum_smul]
    exact N.sum_mem (fun q _ => hterm q)
  have hcast : ((-1 : Module.End ℂ V) ^ pair.2.length *
      (c.descFactorial pair.2.length : Module.End ℂ V)) =
      algebraMap ℂ (Module.End ℂ V)
        ((-1 : ℂ) ^ pair.2.length * (c.descFactorial pair.2.length : ℂ)) := by simp
  unfold conversionTerm
  rw [hcast]
  simpa [Module.End.mul_apply, Algebra.algebraMap_eq_smul_one] using
    N.smul_mem ((-1 : ℂ) ^ pair.2.length * (c.descFactorial pair.2.length : ℂ)) hsum

/-- The complete-symmetric highest-root tail vanishes modulo the next level, for every label. -/
theorem bottomCentral_completeRelation
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (a c s : ℕ)
    (hc : 1 ≤ c) (hs : m + 1 ≤ c + s) :
    ((xOp ρ 0) ^ a * PowerSeries.coeff s (fCurrent (zOp ρ) ^ c)) w ∈
      levelFiltration ρ w m ((m : ℤ) - (a + c)) ((m : ℤ) + a - c + 1) := by
  let N := levelFiltration ρ w m ((m : ℤ) - (a + c)) ((m : ℤ) + a - c + 1)
  have hlower : lowerSum (fTopOp ρ) (xOp ρ) (zOp ρ) c s
      (List.replicate a 0 ++ List.replicate c 0) • w ∈ N := by
    have hh := lowerSum_mem_of_higher_terms (fTopOp ρ) (xOp ρ) (zOp ρ)
      c s (List.replicate a 0 ++ List.replicate c 0) (1 : Module.End ℂ V) w N
      (fun pair hp hshort => by
        simpa using bottomConversionTerm_mem_next ρ w m h a c s pair hp hshort)
    simpa using hh
  have ht := topSum_mem_higher_linear (fTopOp ρ) (xOp ρ) (zOp ρ)
    (fTop_x_comm ρ) (fTop_z_comm ρ)
    (fun i j => by ext v; exact radical_ops_comm ρ 1 5 i j v)
    c s (List.replicate a 0 ++ List.replicate c 0) (1 : Module.End ℂ V) w
    (by intro r; simp) (fTop_garland_zero ρ w m h c s hc hs)
    (by intro t v; simp) N (by simpa using hlower)
  have hx : ∀ i j, xOp ρ i * xOp ρ j = xOp ρ j * xOp ρ i := by
    intro i j
    ext v
    exact radical_ops_comm ρ 1 1 i j v
  rw [rz_zero_topSum (xOp ρ) (zOp ρ) hx a c s] at ht
  have hsmul : (Nat.choose (a + c) c : ℂ) •
      (((xOp ρ 0) ^ a * PowerSeries.coeff s (fCurrent (zOp ρ) ^ c)) w) ∈ N := by
    simpa [aWord, Nat.cast_smul_eq_nsmul, mul_smul] using ht
  exact (Submodule.smul_mem_iff N
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (by omega))))).mp hsmul

/-- The adjoint radical complete-symmetric tail vanishes even before the level quotient. -/
theorem bottomAdjoint_completeRelation
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (a c s : ℕ)
    (ha : 1 ≤ a) (hs : m + 1 ≤ a + s) :
    ((zOp ρ 0) ^ c * PowerSeries.coeff s (fCurrent (xOp ρ) ^ a)) w = 0 := by
  have hz := radical_garland_zero ρ w m h 1 a s ha (by simpa [rootWeight] using hs)
  have hz' : PowerSeries.coeff s (fCurrent (xOp ρ) ^ a) w = 0 := by
    simpa [fCurrent, Garland.Fs, rootF, xOp, radicalColour] using hz
  simp [Module.End.mul_apply, hz']

/-- Every Levi word applied to a central complete relation still vanishes in the next level. -/
theorem bottomCentral_completeRelation_leviWord
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (a c s : ℕ)
    (hc : 1 ≤ c) (hs : m + 1 ≤ c + s) (l : List (Fin 28 × ℕ))
    (hl : l.Forall (fun q => IsLevi q.1)) :
    wordOp ρ l (((xOp ρ 0) ^ a * PowerSeries.coeff s (fCurrent (zOp ρ) ^ c)) w) ∈
      levelFiltration ρ w m ((m : ℤ) - (a + c)) ((m : ℤ) + a - c + 1) := by
  induction l with
  | nil => exact bottomCentral_completeRelation ρ w m h a c s hc hs
  | cons q l ih =>
      simp only [List.forall_cons] at hl
      exact levelFiltration_stable ρ w m _ _ q.1 q.2 hl.1 (ih hl.2)

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.radicalCountSpan_le_levelFiltration
#print axioms VOA.DeligneAudit.D4LevelReduction.highestLevi_powerCoeff_mem
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomConversionTerm_mem_next
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomCentral_completeRelation
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomAdjoint_completeRelation
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomCentral_completeRelation_leviWord
