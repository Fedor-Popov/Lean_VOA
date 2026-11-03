import VOA.DeligneAudit.D4LevelReductionCentralGeneration
import VOA.DeligneAudit.D4LeviKSRzGeneralCollapse

/-! Garland relations for central words modulo the next Levi level. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.D4Levi
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- A nonempty Y block with Z spectators lies in the next boundary level. -/
theorem boundaryYZSpan_le_next
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (y z : ℕ) (hy : 0 < y) :
    xyzCountSpan ρ w 0 y z ≤
      levelFiltration ρ w m ((m : ℤ) - (y + z)) ((m : ℤ) - (y + z) + 1) := by
  rw [xyzCountSpan, Submodule.span_le]
  rintro v ⟨l, he, hx, hu, hup, hyl, hz, rfl⟩
  apply boundaryKey_le_next_of_Y ρ w m h _ (wordKey l) _ _ _
    (keyLayer_le_orbit ρ w _ (radicalWord_mem_key ρ w l))
  · simp [keyAlphaGrade, keyDepth, wordKey, he, hx, hu, hup, hyl, hz]
  · simp [keyLeviLevel, wordKey, he, hx, hyl, hz]
    ring
  · simpa [wordKey, hyl] using hy

/-- Coefficients of products of Levi currents preserve every level term. -/
theorem leviCurrent_powerCoeff_mem (κ p : ℤ) (c : Fin 28) (hc : IsLevi c)
    (k s : ℕ) {v : V} (hv : v ∈ levelFiltration ρ w m κ p) :
    PowerSeries.coeff s (fCurrent (ρ.op c) ^ k) v ∈ levelFiltration ρ w m κ p := by
  induction k generalizing s v with
  | zero =>
      by_cases hs : s = 0
      · subst s
        simpa using hv
      · simp [hs]
  | succ k ih =>
      rw [pow_succ, PowerSeries.coeff_mul]
      change (∑ q ∈ Finset.antidiagonal s,
        PowerSeries.coeff q.1 (fCurrent (ρ.op c) ^ k) *
          PowerSeries.coeff q.2 (fCurrent (ρ.op c))) • v ∈ _
      rw [Finset.sum_smul]
      apply Submodule.sum_mem
      intro q _
      have hc' := levelFiltration_stable ρ w m κ p c q.2 hc hv
      simpa [fCurrent, mul_smul] using ih q.1 hc'

private theorem central_lowerContraction_mem_next
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (zs : List ℕ) (k : ℕ)
    (pair : List ℕ × List ℕ) (hp : pair ∈ choices (List.replicate k 0))
    (hshort : pair.2.length < k) (q : ℕ × ℕ) :
    ((PowerSeries.coeff q.1 (fCurrent (fOp ρ) ^ (k - pair.2.length)) *
        aWord (yOp ρ) pair.1) * PowerSeries.coeff q.2 (bWord (zOp ρ) pair.2)) •
      ((zs.map (zOp ρ)).prod • w) ∈
        levelFiltration ρ w m ((m : ℤ) - (zs.length + k))
          ((m : ℤ) - (zs.length + k) + 1) := by
  have hz : (zs.map (zOp ρ)).prod w ∈ xyzCountSpan ρ w 0 0 zs.length := by
    simpa using xyzCountSpan_z_word ρ w zs 0 0 0 (xyzCountSpan_zero ρ w)
  have hb := xyzCountSpan_z_coeff ρ w pair.2 q.2 0 0 zs.length hz
  have ha := xyzCountSpan_y_word ρ w pair.1 0 0 (zs.length + pair.2.length) hb
  have hlen := choices_length (List.replicate k 0) pair hp
  simp only [List.length_replicate] at hlen
  have hsum : pair.1.length + (zs.length + pair.2.length) = zs.length + k := by omega
  have hbase : (aWord (yOp ρ) pair.1 * PowerSeries.coeff q.2 (bWord (zOp ρ) pair.2)) •
      ((zs.map (zOp ρ)).prod • w) ∈
        levelFiltration ρ w m ((m : ℤ) - (zs.length + k))
          ((m : ℤ) - (zs.length + k) + 1) := by
    have hh := boundaryYZSpan_le_next ρ w m h pair.1.length
      (zs.length + pair.2.length) (by omega)
    have hsum' : (pair.1.length : ℤ) + (zs.length + pair.2.length) =
        (zs.length : ℤ) + k := by exact_mod_cast hsum
    push_cast at hh
    rw [hsum'] at hh
    apply hh
    simpa [aWord, mul_smul] using ha
  have hf := leviCurrent_powerCoeff_mem ρ w m _ _ 18 ⟨10, rfl⟩
    (k - pair.2.length) q.1 hbase
  simpa [fOp, mul_assoc, mul_smul] using hf

private theorem central_conversionTerm_mem_next
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (zs : List ℕ) (k s : ℕ)
    (pair : List ℕ × List ℕ) (hp : pair ∈ choices (List.replicate k 0))
    (hshort : pair.2.length < k) :
    conversionTerm (fOp ρ) (yOp ρ) (zOp ρ) k s pair •
      ((zs.map (zOp ρ)).prod • w) ∈
        levelFiltration ρ w m ((m : ℤ) - (zs.length + k))
          ((m : ℤ) - (zs.length + k) + 1) := by
  let N := levelFiltration ρ w m ((m : ℤ) - (zs.length + k))
    ((m : ℤ) - (zs.length + k) + 1)
  have hsum :
      (∑ q ∈ Finset.antidiagonal s,
        (PowerSeries.coeff q.1 (fCurrent (fOp ρ) ^ (k - pair.2.length)) *
          aWord (yOp ρ) pair.1) * PowerSeries.coeff q.2 (bWord (zOp ρ) pair.2)) •
        ((zs.map (zOp ρ)).prod • w) ∈ N := by
    rw [Finset.sum_smul]
    exact N.sum_mem (fun q _ => central_lowerContraction_mem_next ρ w m h zs k
      pair hp hshort q)
  have hcast : ((-1 : Module.End ℂ V) ^ pair.2.length *
      (k.descFactorial pair.2.length : Module.End ℂ V)) =
      algebraMap ℂ (Module.End ℂ V)
        ((-1 : ℂ) ^ pair.2.length * (k.descFactorial pair.2.length : ℂ)) := by simp
  have hscalar (t : ℂ) :
      (algebraMap ℂ (Module.End ℂ V) t) •
        ((∑ q ∈ Finset.antidiagonal s,
          (PowerSeries.coeff q.1 (fCurrent (fOp ρ) ^ (k - pair.2.length)) *
            aWord (yOp ρ) pair.1) * PowerSeries.coeff q.2 (bWord (zOp ρ) pair.2)) •
          ((zs.map (zOp ρ)).prod • w)) ∈ N := by
    simpa using N.smul_mem t hsum
  unfold conversionTerm
  rw [hcast]
  simpa only [mul_smul] using hscalar
    ((-1 : ℂ) ^ pair.2.length * (k.descFactorial pair.2.length : ℂ))

/-- The weight-m Garland coefficient on central words vanishes modulo the next level. -/
theorem centralGarland_spectator_mem_next
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (zs : List ℕ) (k s : ℕ)
    (hk : 1 ≤ k) (hks : m + 1 ≤ k + s) :
    PowerSeries.coeff s (fCurrent (zOp ρ) ^ k) ((zs.map (zOp ρ)).prod w) ∈
      levelFiltration ρ w m ((m : ℤ) - (zs.length + k))
        ((m : ℤ) - (zs.length + k) + 1) := by
  let N := levelFiltration ρ w m ((m : ℤ) - (zs.length + k))
    ((m : ℤ) - (zs.length + k) + 1)
  have hlower : lowerSum (fOp ρ) (yOp ρ) (zOp ρ) k s (List.replicate k 0) •
      ((zs.map (zOp ρ)).prod • w) ∈ N := by
    apply lowerSum_mem_of_higher_terms (fOp ρ) (yOp ρ) (zOp ρ)
      k s (List.replicate k 0) (zs.map (zOp ρ)).prod w N
    exact central_conversionTerm_mem_next ρ w m h zs k s
  have htop := topSum_mem_higher_linear (fOp ρ) (yOp ρ) (zOp ρ)
    (fTwo_y_comm ρ) (fTwo_z_comm ρ)
    (fun i j => by ext v; exact radical_ops_comm ρ 4 5 i j v)
    k s (List.replicate k 0) (zs.map (zOp ρ)).prod w
    (by simpa using rz_xz_spectator_comm ρ [] zs)
    (fTwo_garland_zero ρ w m h k s hk hks) (by intro t v; simp) N hlower
  have hy : ∀ i j, yOp ρ i * yOp ρ j = yOp ρ j * yOp ρ i := by
    intro i j
    ext v
    exact radical_ops_comm ρ 4 4 i j v
  have heq := rz_zero_topSum (yOp ρ) (zOp ρ) hy 0 k s
  have heq' : topSum (yOp ρ) (zOp ρ) k s (List.replicate k 0) =
      PowerSeries.coeff s (fCurrent (zOp ρ) ^ k) := by
    simpa [aWord] using heq
  rw [heq'] at htop
  exact htop

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.boundaryYZSpan_le_next
#print axioms VOA.DeligneAudit.D4LevelReduction.leviCurrent_powerCoeff_mem
#print axioms VOA.DeligneAudit.D4LevelReduction.centralGarland_spectator_mem_next
