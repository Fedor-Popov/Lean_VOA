import VOA.DeligneAudit.D4LeviRootBoxTable
import VOA.DeligneAudit.LeviTypeA3SimpleLength

/-! Rank-one current operators for all six negative-radical colours. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

noncomputable def rootF (j : Fin 6) (r : ℕ) : Module.End ℂ V :=
  ρ.op (radicalColour j) r

noncomputable def rootE (j : Fin 6) : Module.End ℂ V :=
  (rootSign j : ℂ) • ρ.op (positiveColour j) 1

noncomputable def rootH (j : Fin 6) (r : ℕ) : Module.End ℂ V :=
  (rootSign j : ℂ) •
    ∑ c : Fin 28,
      D4sector.f (positiveColour j) (radicalColour j) c • ρ.op c r

theorem rootF_comm (j : Fin 6) (r s : ℕ) :
    rootF ρ j r * rootF ρ j s = rootF ρ j s * rootF ρ j r := by
  ext v
  simpa [rootF] using radical_ops_comm ρ j j r s v

theorem rootE_source_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (j : Fin 6) : rootE ρ j w = 0 := by
  have hs : Sat D4sector.f ρ w (ravSpec D4sector m (2 * m)) := by
    simpa [ravFam] using h
  have hp : D4sector.raising (positiveColour j) := by
    change 4 ≤ (positiveColour j).val ∧ (positiveColour j).val < 16
    fin_cases j <;> decide
  simp [rootE, rs_raising hs hp 1]

theorem rootH_source_pos_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (j : Fin 6) (r : ℕ) (hr : 0 < r) : rootH ρ j r w = 0 := by
  have hs : Sat D4sector.f ρ w (ravSpec D4sector m (2 * m)) := by
    simpa [ravFam] using h
  simp only [rootH, LinearMap.smul_apply, LinearMap.sum_apply]
  have hz : (∑ c : Fin 28,
      D4sector.f (positiveColour j) (radicalColour j) c • ρ.op c r w) = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : c.val < 4
    · rw [rs_cartan_pos hs hc r hr]
      simp
    · have hf := root_ef_cartan_supportC j c (by omega)
      change fD4 (positiveColour j) (radicalColour j) c • ρ.op c r w = 0
      rw [hf]
      simp
  rw [hz]
  simp

theorem rootF_source_nil
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (j : Fin 6) :
    (rootF ρ j 0 ^ (rootWeight m j + 1)) w = 0 := by
  have hh := source_root_nil ρ w m h (radicalColour j)
    (by fin_cases j <;> decide)
  simpa [rootF, rootExponent_eq m j] using hh

theorem rootEF_comm (j : Fin 6) (r : ℕ) :
    rootE ρ j * rootF ρ j r - rootF ρ j r * rootE ρ j =
      rootH ρ j (r + 1) := by
  ext v
  simp only [rootE, rootF, rootH, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.smul_apply, map_smul,
    LinearMap.sum_apply]
  rw [← smul_sub]
  rw [ρ.comm]
  simp only [Nat.add_comm 1 r]
  rfl

theorem rootHF_comm (j : Fin 6) (r s : ℕ) :
    rootH ρ j (r + 1) * rootF ρ j s -
      rootF ρ j s * rootH ρ j (r + 1) =
        (-2 : ℂ) • rootF ρ j (r + 1 + s) := by
  ext v
  let p := positiveColour j
  let f := radicalColour j
  let t := r + 1
  have hsum :
      (∑ c : Fin 28, D4sector.f p f c • ρ.op c t (ρ.op f s v)) -
        ρ.op f s (∑ c : Fin 28, D4sector.f p f c • ρ.op c t v) =
      ∑ c : Fin 28, D4sector.f p f c •
        (ρ.op c t (ρ.op f s v) - ρ.op f s (ρ.op c t v)) := by
    simp [Finset.sum_sub_distrib, smul_sub]
  change (rootSign j : ℂ) •
      (∑ c : Fin 28, D4sector.f p f c • ρ.op c t (ρ.op f s v)) -
        ρ.op f s ((rootSign j : ℂ) •
          (∑ c : Fin 28, D4sector.f p f c • ρ.op c t v)) =
      (-2 : ℂ) • ρ.op f (t + s) v
  rw [map_smul, ← smul_sub, hsum]
  simp_rw [ρ.comm]
  have hcollapse : (rootSign j : ℂ) •
      (∑ c : Fin 28, D4sector.f p f c •
        (∑ d : Fin 28, D4sector.f c f d • ρ.op d (t + s) v)) =
      ∑ d : Fin 28,
        ((rootSign j : ℂ) *
          (∑ c : Fin 28, D4sector.f p f c * D4sector.f c f d)) •
            ρ.op d (t + s) v := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, Finset.mul_sum]
  change (rootSign j : ℂ) •
      (∑ c : Fin 28, D4sector.f p f c •
        (∑ d : Fin 28, D4sector.f c f d • ρ.op d (t + s) v)) =
    (-2 : ℂ) • ρ.op f (t + s) v
  rw [hcollapse]
  simp_rw [show ∀ d : Fin 28,
    (rootSign j : ℂ) *
      (∑ c : Fin 28, D4sector.f p f c * D4sector.f c f d) =
        if d = f then (-2 : ℂ) else 0 from
      fun d => root_hf_tableC j d]
  simp

/-- The rank-one box bounds every mixed-mode word of a fixed radical colour. -/
theorem root_word_length_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (j : Fin 6) (l : List ℕ) (hl : rootWeight m j < l.length) :
    (l.map fun s => ρ.op (radicalColour j) s).prod w = 0 := by
  let F : ℕ → Module.End ℂ V := rootF ρ j
  let H : ℕ → Module.End ℂ V := rootH ρ j
  let E : Module.End ℂ V := rootE ρ j
  have hEF : ∀ s, E * F s - F s * E = H (s + 1) :=
    rootEF_comm ρ j
  have hHF : ∀ r s, H (r + 1) * F s - F s * H (r + 1) =
      (-2 : ℂ) • F (r + 1 + s) := rootHF_comm ρ j
  have hFF : ∀ r s, F r * F s = F s * F r := rootF_comm ρ j
  have hE : E w = 0 := rootE_source_zero ρ w m h j
  have hH : ∀ r, H (r + 1) w = 0 := by
    intro r
    exact rootH_source_pos_zero ρ w m h j (r + 1) (by omega)
  have hN : (F 0 ^ (rootWeight m j + 1)) w = 0 :=
    rootF_source_nil ρ w m h j
  have hk : ∀ r s, 1 ≤ r → rootWeight m j + 1 ≤ r + s →
      (PowerSeries.coeff s (VOA.DeligneAudit.Garland.Fs F ^ r)) w = 0 := by
    intro r s hr hrs
    exact VOA.DeligneAudit.Garland.garland hEF hHF hFF hE hH
      r hr hN s hrs
  exact VOA.DeligneAudit.A3Sector.a3_box_word_length_zero F hFF w
    (rootWeight m j) hk l hl

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rootF_comm
#print axioms VOA.DeligneAudit.D4Levi.rootE_source_zero
#print axioms VOA.DeligneAudit.D4Levi.rootH_source_pos_zero
#print axioms VOA.DeligneAudit.D4Levi.rootF_source_nil
#print axioms VOA.DeligneAudit.D4Levi.rootEF_comm
#print axioms VOA.DeligneAudit.D4Levi.rootHF_comm
#print axioms VOA.DeligneAudit.D4Levi.root_word_length_zero
