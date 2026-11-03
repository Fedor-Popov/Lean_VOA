import VOA.DeligneAudit.D4LeviKSRzLower

/-! The f₂ Rz top contraction vanishes modulo strictly higher D4 keys. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

theorem rz_lower_term (xs ys zs : List ℕ) (k s d : ℕ)
    (p : List ℕ × List ℕ)
    (hp : p ∈ choices (ys ++ List.replicate k 0))
    (hshort : p.2.length < k) :
    conversionTerm (fOp ρ) (yOp ρ) (zOp ρ) k s p •
      (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈
        higherOrbit ρ w m (rzKey xs ys zs k d) := by
  let N := higherOrbit ρ w m (rzKey xs ys zs k d)
  have hsum :
      (∑ q ∈ Finset.antidiagonal s,
        (PowerSeries.coeff q.1 (fCurrent (fOp ρ) ^ (k - p.2.length)) *
          aWord (yOp ρ) p.1) *
          PowerSeries.coeff q.2 (bWord (zOp ρ) p.2)) •
        (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈ N := by
    rw [Finset.sum_smul]
    apply N.sum_mem
    intro q hq
    exact rz_lower_base ρ w m xs ys zs k p hp hshort q d
  have hscalar (c : ℂ) :
      (algebraMap ℂ (Module.End ℂ V) c) •
        ((∑ q ∈ Finset.antidiagonal s,
          (PowerSeries.coeff q.1 (fCurrent (fOp ρ) ^ (k - p.2.length)) *
            aWord (yOp ρ) p.1) *
            PowerSeries.coeff q.2 (bWord (zOp ρ) p.2)) •
          (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w)) ∈ N := by
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

theorem rz_lower_sum (xs ys zs : List ℕ) (k s d : ℕ) :
    lowerSum (fOp ρ) (yOp ρ) (zOp ρ) k s
        (ys ++ List.replicate k 0) •
      (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈
        higherOrbit ρ w m (rzKey xs ys zs k d) := by
  apply lowerSum_mem_of_higher_terms (fOp ρ) (yOp ρ) (zOp ρ)
    k s (ys ++ List.replicate k 0)
    ((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) w
    (higherOrbit ρ w m (rzKey xs ys zs k d))
  intro p hp hshort
  exact rz_lower_term ρ w m xs ys zs k s d p hp hshort

/-- The complete top Rz contraction is absorbed once the XZ spectator commutes with f₂. -/
theorem rz_top_higher_of_comm
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (xs ys zs : List ℕ) (k s : ℕ)
    (hk : 1 ≤ k) (hks : m + 1 ≤ k + s)
    (hR : ∀ r,
      ((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) * fOp ρ r =
        fOp ρ r * ((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod)) :
    topSum (yOp ρ) (zOp ρ) k s (ys ++ List.replicate k 0) •
      (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈
        higherOrbit ρ w m
          (rzKey xs ys zs k (xs.sum + ys.sum + zs.sum + s)) := by
  have hfa : ∀ i j, fOp ρ i * yOp ρ j - yOp ρ j * fOp ρ i =
      zOp ρ (i + j) := by
    intro i j
    change fOp ρ i * yOp ρ j - yOp ρ j * fOp ρ i = zOp ρ (i + j)
    exact fTwo_y_comm ρ i j
  have hfb : ∀ i j, fOp ρ i * zOp ρ j = zOp ρ j * fOp ρ i := by
    intro i j
    change fOp ρ i * zOp ρ j = zOp ρ j * fOp ρ i
    exact fTwo_z_comm ρ i j
  have hab : ∀ i j, yOp ρ i * zOp ρ j = zOp ρ j * yOp ρ i := by
    intro i j
    ext v
    simpa [yOp, zOp] using radical_ops_comm ρ 4 5 i j v
  have hkill : PowerSeries.coeff s (fCurrent (fOp ρ) ^ k) w = 0 := by
    have hh := fTwo_garland_zero ρ w m h k s hk hks
    exact hh
  exact topSum_mem_higher_linear (fOp ρ) (yOp ρ) (zOp ρ)
    hfa hfb hab k s (ys ++ List.replicate k 0)
    ((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) w hR hkill
    (by intro c v; simp) _
    (rz_lower_sum ρ w m xs ys zs k s
      (xs.sum + ys.sum + zs.sum + s))

theorem fOp_xOp_comm (r s : ℕ) :
    fOp ρ r * xOp ρ s = xOp ρ s * fOp ρ r := by
  apply sub_eq_zero.mp
  ext v
  have hc := ρ.comm (18 : Fin 28) (22 : Fin 28) r s v
  change ρ.op (18 : Fin 28) r (ρ.op (22 : Fin 28) s v) -
    ρ.op (22 : Fin 28) s (ρ.op (18 : Fin 28) r v) = 0
  rw [hc]
  change (∑ c : Fin 28,
    fD4 (lowerColour 2) (radicalColour 1) c • ρ.op c (r + s) v) = 0
  simp [lower_coefficient, lowerAction]

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

theorem rz_xz_spectator_comm (xs zs : List ℕ) (r : ℕ) :
    ((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) * fOp ρ r =
      fOp ρ r * ((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) := by
  have hx := prod_comm_f (xOp ρ) xs (fOp ρ r)
    (fun i => (fOp_xOp_comm ρ r i).symm)
  have hz := prod_comm_f (zOp ρ) zs (fOp ρ r)
    (fun i => (fTwo_z_comm ρ r i).symm)
  calc
    _ = (xs.map (xOp ρ)).prod *
      ((zs.map (zOp ρ)).prod * fOp ρ r) := mul_assoc _ _ _
    _ = (xs.map (xOp ρ)).prod *
      (fOp ρ r * (zs.map (zOp ρ)).prod) := by rw [hz]
    _ = fOp ρ r * ((xs.map (xOp ρ)).prod *
      (zs.map (zOp ρ)).prod) := by rw [← mul_assoc, hx, mul_assoc]

/-- Graded Rz: the top Y-to-Z conversion lies in the higher key orbit. -/
theorem rz_top_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (xs ys zs : List ℕ) (k s : ℕ)
    (hk : 1 ≤ k) (hks : m + 1 ≤ k + s) :
    topSum (yOp ρ) (zOp ρ) k s (ys ++ List.replicate k 0) •
      (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈
        higherOrbit ρ w m
          (rzKey xs ys zs k (xs.sum + ys.sum + zs.sum + s)) := by
  exact rz_top_higher_of_comm ρ w m h xs ys zs k s hk hks
    (rz_xz_spectator_comm ρ xs zs)

/-- The indexed version of Rz, stated in the actual descending key prefix. -/
theorem rz_top_prefix
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (xs ys zs : List ℕ) (k s i : ℕ)
    (hk : 1 ≤ k) (hks : m + 1 ≤ k + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ =
      rzKey xs ys zs k (xs.sum + ys.sum + zs.sum + s)) :
    topSum (yOp ρ) (zOp ρ) k s (ys ++ List.replicate k 0) •
      (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈
        keyPrefix ρ w m i := by
  rw [keyPrefix_eq_higher ρ w m h i hi, hkey]
  exact rz_top_higher ρ w m h xs ys zs k s hk hks

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rz_lower_term
#print axioms VOA.DeligneAudit.D4Levi.rz_lower_sum
#print axioms VOA.DeligneAudit.D4Levi.rz_top_higher_of_comm
#print axioms VOA.DeligneAudit.D4Levi.fOp_xOp_comm
#print axioms VOA.DeligneAudit.D4Levi.rz_xz_spectator_comm
#print axioms VOA.DeligneAudit.D4Levi.rz_top_higher
#print axioms VOA.DeligneAudit.D4Levi.rz_top_prefix
