import VOA.DeligneAudit.D4LeviKSRyLower

/-! Graded X-to-Z conversion from the highest Levi-root Garland relation. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

theorem ry_lower_term (xs ys zs : List ℕ) (k s d : ℕ)
    (p : List ℕ × List ℕ)
    (hp : p ∈ choices (xs ++ List.replicate k 0))
    (hshort : p.2.length < k) :
    conversionTerm (fTopOp ρ) (xOp ρ) (zOp ρ) k s p •
      (((ys.map (yOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈
        higherOrbit ρ w m (rzKey xs ys zs k d) := by
  let N := higherOrbit ρ w m (rzKey xs ys zs k d)
  have hsum :
      (∑ q ∈ Finset.antidiagonal s,
        (PowerSeries.coeff q.1
          (fCurrent (fTopOp ρ) ^ (k - p.2.length)) *
            aWord (xOp ρ) p.1) *
          PowerSeries.coeff q.2 (bWord (zOp ρ) p.2)) •
        (((ys.map (yOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈ N := by
    rw [Finset.sum_smul]
    apply N.sum_mem
    intro q hq
    exact ry_lower_base ρ w m xs ys zs k p hp hshort q d
  have hscalar (c : ℂ) :
      (algebraMap ℂ (Module.End ℂ V) c) •
        ((∑ q ∈ Finset.antidiagonal s,
          (PowerSeries.coeff q.1
            (fCurrent (fTopOp ρ) ^ (k - p.2.length)) *
              aWord (xOp ρ) p.1) *
            PowerSeries.coeff q.2 (bWord (zOp ρ) p.2)) •
          (((ys.map (yOp ρ)).prod * (zs.map (zOp ρ)).prod) • w)) ∈ N := by
    simpa using N.smul_mem c hsum
  have hcast : ((-1 : Module.End ℂ V) ^ p.2.length *
      (k.descFactorial p.2.length : Module.End ℂ V)) =
      algebraMap ℂ (Module.End ℂ V)
        ((-1 : ℂ) ^ p.2.length * (k.descFactorial p.2.length : ℂ)) := by
    simp
  unfold conversionTerm
  rw [hcast]
  simpa only [mul_smul] using
    hscalar ((-1 : ℂ) ^ p.2.length * (k.descFactorial p.2.length : ℂ))

theorem ry_lower_sum (xs ys zs : List ℕ) (k s d : ℕ) :
    lowerSum (fTopOp ρ) (xOp ρ) (zOp ρ) k s
      (xs ++ List.replicate k 0) •
      (((ys.map (yOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈
        higherOrbit ρ w m (rzKey xs ys zs k d) := by
  apply lowerSum_mem_of_higher_terms (fTopOp ρ) (xOp ρ) (zOp ρ)
    k s (xs ++ List.replicate k 0)
    ((ys.map (yOp ρ)).prod * (zs.map (zOp ρ)).prod) w
    (higherOrbit ρ w m (rzKey xs ys zs k d))
  intro p hp hshort
  exact ry_lower_term ρ w m xs ys zs k s d p hp hshort

theorem fTop_y_comm (r s : ℕ) :
    fTopOp ρ r * yOp ρ s = yOp ρ s * fTopOp ρ r := by
  have hc : ρ.op (23 : Fin 28) r * yOp ρ s -
      yOp ρ s * ρ.op (23 : Fin 28) r = 0 := by
    ext v
    have h := ρ.comm (23 : Fin 28) (26 : Fin 28) r s v
    change ρ.op (23 : Fin 28) r (ρ.op (26 : Fin 28) s v) -
      ρ.op (26 : Fin 28) s (ρ.op (23 : Fin 28) r v) = _ at h
    change ρ.op (23 : Fin 28) r (ρ.op (26 : Fin 28) s v) -
      ρ.op (26 : Fin 28) s (ρ.op (23 : Fin 28) r v) = 0
    rw [h]
    change (∑ c : Fin 28,
      fD4 (lowerColour 5) (radicalColour 4) c • ρ.op c (r + s) v) = 0
    simp [lower_coefficient, lowerAction]
  apply sub_eq_zero.mp
  calc
    fTopOp ρ r * yOp ρ s - yOp ρ s * fTopOp ρ r =
        -(ρ.op (23 : Fin 28) r * yOp ρ s -
          yOp ρ s * ρ.op (23 : Fin 28) r) := by
            simp [fTopOp]
            abel
    _ = 0 := by rw [hc]; simp

private theorem prod_comm_f (a : ℕ → Module.End ℂ V) (ls : List ℕ)
    (f : Module.End ℂ V) (h : ∀ i, a i * f = f * a i) :
    (ls.map a).prod * f = f * (ls.map a).prod := by
  induction ls with
  | nil => simp
  | cons i ls ih =>
      simp only [List.map_cons, List.prod_cons]
      calc
        (a i * (ls.map a).prod) * f = a i * ((ls.map a).prod * f) :=
          mul_assoc _ _ _
        _ = a i * (f * (ls.map a).prod) := by rw [ih]
        _ = f * (a i * (ls.map a).prod) := by rw [← mul_assoc, h i, mul_assoc]

theorem ry_yz_spectator_comm (ys zs : List ℕ) (r : ℕ) :
    ((ys.map (yOp ρ)).prod * (zs.map (zOp ρ)).prod) * fTopOp ρ r =
      fTopOp ρ r * ((ys.map (yOp ρ)).prod * (zs.map (zOp ρ)).prod) := by
  have hy := prod_comm_f (yOp ρ) ys (fTopOp ρ r)
    (fun i => (fTop_y_comm ρ r i).symm)
  have hz := prod_comm_f (zOp ρ) zs (fTopOp ρ r)
    (fun i => (fTop_z_comm ρ r i).symm)
  calc
    _ = (ys.map (yOp ρ)).prod *
      ((zs.map (zOp ρ)).prod * fTopOp ρ r) := mul_assoc _ _ _
    _ = (ys.map (yOp ρ)).prod *
      (fTopOp ρ r * (zs.map (zOp ρ)).prod) := by rw [hz]
    _ = fTopOp ρ r * ((ys.map (yOp ρ)).prod *
      (zs.map (zOp ρ)).prod) := by rw [← mul_assoc, hy, mul_assoc]

/-- The complete X-to-Z top contraction vanishes in the higher-key orbit. -/
theorem ry_top_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (xs ys zs : List ℕ) (k s : ℕ)
    (hk : 1 ≤ k) (hks : m + 1 ≤ k + s) :
    topSum (xOp ρ) (zOp ρ) k s (xs ++ List.replicate k 0) •
      (((ys.map (yOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈
        higherOrbit ρ w m
          (rzKey xs ys zs k (xs.sum + ys.sum + zs.sum + s)) := by
  have hab : ∀ i j, xOp ρ i * zOp ρ j = zOp ρ j * xOp ρ i := by
    intro i j
    ext v
    simpa [xOp, zOp] using radical_ops_comm ρ 1 5 i j v
  exact topSum_mem_higher_linear (fTopOp ρ) (xOp ρ) (zOp ρ)
    (fTop_x_comm ρ) (fTop_z_comm ρ) hab
    k s (xs ++ List.replicate k 0)
    ((ys.map (yOp ρ)).prod * (zs.map (zOp ρ)).prod) w
    (ry_yz_spectator_comm ρ ys zs)
    (fTop_garland_zero ρ w m h k s hk hks)
    (by intro c v; simp) _
    (ry_lower_sum ρ w m xs ys zs k s
      (xs.sum + ys.sum + zs.sum + s))

/-- The indexed version of the pure highest-root conversion. -/
theorem ry_top_prefix
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (xs ys zs : List ℕ) (k s i : ℕ)
    (hk : 1 ≤ k) (hks : m + 1 ≤ k + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ =
      rzKey xs ys zs k (xs.sum + ys.sum + zs.sum + s)) :
    topSum (xOp ρ) (zOp ρ) k s (xs ++ List.replicate k 0) •
      (((ys.map (yOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈
        keyPrefix ρ w m i := by
  rw [keyPrefix_eq_higher ρ w m h i hi, hkey]
  exact ry_top_higher ρ w m h xs ys zs k s hk hks

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ry_lower_term
#print axioms VOA.DeligneAudit.D4Levi.ry_lower_sum
#print axioms VOA.DeligneAudit.D4Levi.fTop_y_comm
#print axioms VOA.DeligneAudit.D4Levi.ry_yz_spectator_comm
#print axioms VOA.DeligneAudit.D4Levi.ry_top_higher
#print axioms VOA.DeligneAudit.D4Levi.ry_top_prefix
