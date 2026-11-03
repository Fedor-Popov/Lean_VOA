import VOA.DeligneAudit.D4LeviKSRzShift

/-! Concrete power-sum shifts on XYZ radical words. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- The sum of words obtained by shifting one occurrence of colour `j`. -/
noncomputable def colourPowerShift (j : Fin 6) (r : ℕ) :
    List (Fin 6 × ℕ) → V
  | [] => 0
  | (i, s) :: ls =>
      (if i = j then radicalWord ρ w ((i, r + s) :: ls) else 0) +
        ρ.op (radicalColour i) s (colourPowerShift j r ls)

private theorem cartan_xyz_shift
    (H : Module.End ℂ V) (j : Fin 6) (c : ℂ) (r : ℕ)
    (hzero : H w = 0)
    (hcomm : ∀ (i : Fin 6) (s : ℕ) (v : V),
      i = 1 ∨ i = 4 ∨ i = 5 →
      H (ρ.op (radicalColour i) s v) -
        ρ.op (radicalColour i) s (H v) =
          if i = j then c • ρ.op (radicalColour i) (r + s) v else 0)
    (ls : List (Fin 6 × ℕ))
    (hls : ∀ p ∈ ls, p.1 = 1 ∨ p.1 = 4 ∨ p.1 = 5) :
    H (radicalWord ρ w ls) = c • colourPowerShift ρ w j r ls := by
  induction ls with
  | nil => simpa [radicalWord, colourPowerShift, wordOp] using hzero
  | cons p ls ih =>
      rcases p with ⟨i, s⟩
      have hi := hls (i, s) (by simp)
      have ht : ∀ q ∈ ls, q.1 = 1 ∨ q.1 = 4 ∨ q.1 = 5 := by
        intro q hq
        exact hls q (by simp [hq])
      have hc := hcomm i s (radicalWord ρ w ls) hi
      change H (ρ.op (radicalColour i) s (radicalWord ρ w ls)) =
        c • colourPowerShift ρ w j r ((i, s) :: ls)
      rw [sub_eq_iff_eq_add.mp hc, ih ht]
      by_cases hij : i = j
      · subst i
        simp only [colourPowerShift, if_true, smul_add, map_smul]
        simp only [radicalWord, List.map_cons, wordOp]
      · simp only [colourPowerShift, hij, if_false, zero_add, map_smul]

private theorem x_comm_xyz (r : ℕ) (i : Fin 6) (s : ℕ) (v : V)
    (hi : i = 1 ∨ i = 4 ∨ i = 5) :
    xShiftCartan ρ r (ρ.op (radicalColour i) s v) -
      ρ.op (radicalColour i) s (xShiftCartan ρ r v) =
        if i = 1 then (2 : ℂ) • ρ.op (radicalColour i) (r + s) v else 0 := by
  rcases selective_cartan_pairings ρ r s v with ⟨h1, h4, h5, _⟩
  rcases hi with rfl | rfl | rfl
  · simpa [xOp, radicalColour] using h1
  · simpa [yOp, radicalColour] using h4
  · simpa [zOp, radicalColour] using h5

private theorem y_comm_xyz (r : ℕ) (i : Fin 6) (s : ℕ) (v : V)
    (hi : i = 1 ∨ i = 4 ∨ i = 5) :
    yShiftCartan ρ r (ρ.op (radicalColour i) s v) -
      ρ.op (radicalColour i) s (yShiftCartan ρ r v) =
        if i = 4 then (2 : ℂ) • ρ.op (radicalColour i) (r + s) v else 0 := by
  rcases selective_cartan_pairings ρ r s v with
    ⟨_, _, _, h1, h4, h5, _⟩
  rcases hi with rfl | rfl | rfl
  · simpa [xOp, radicalColour] using h1
  · simpa [yOp, radicalColour] using h4
  · simpa [zOp, radicalColour] using h5

private theorem z_comm_xyz (r : ℕ) (i : Fin 6) (s : ℕ) (v : V)
    (hi : i = 1 ∨ i = 4 ∨ i = 5) :
    zShiftCartan ρ r (ρ.op (radicalColour i) s v) -
      ρ.op (radicalColour i) s (zShiftCartan ρ r v) =
        if i = 5 then ρ.op (radicalColour i) (r + s) v else 0 := by
  rcases selective_cartan_pairings ρ r s v with
    ⟨_, _, _, _, _, _, h1, h4, h5⟩
  rcases hi with rfl | rfl | rfl
  · simpa [xOp, radicalColour] using h1
  · simpa [yOp, radicalColour] using h4
  · simpa [zOp, radicalColour] using h5

/-- Positive selective Cartan currents act as X, Y, and Z power-sum mode
    shifts on XYZ words, with pairing constants 2, 2, and 1. -/
theorem selective_cartan_xyz_power_shift
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (r : ℕ) (hr : 0 < r) (ls : List (Fin 6 × ℕ))
    (hls : ∀ p ∈ ls, p.1 = 1 ∨ p.1 = 4 ∨ p.1 = 5) :
    xShiftCartan ρ r (radicalWord ρ w ls) =
        (2 : ℂ) • colourPowerShift ρ w (1 : Fin 6) r ls ∧
    yShiftCartan ρ r (radicalWord ρ w ls) =
        (2 : ℂ) • colourPowerShift ρ w (4 : Fin 6) r ls ∧
    zShiftCartan ρ r (radicalWord ρ w ls) =
        colourPowerShift ρ w (5 : Fin 6) r ls := by
  rcases selective_cartan_source_zero ρ w m h r hr with ⟨hx, hy, hz⟩
  refine ⟨?_, ?_, ?_⟩
  · exact cartan_xyz_shift ρ w (xShiftCartan ρ r) 1 2 r hx
      (x_comm_xyz ρ r) ls hls
  · exact cartan_xyz_shift ρ w (yShiftCartan ρ r) 4 2 r hy
      (y_comm_xyz ρ r) ls hls
  · simpa using cartan_xyz_shift ρ w (zShiftCartan ρ r) 5 1 r hz
      (fun i s v hi => by simpa using z_comm_xyz ρ r i s v hi) ls hls

/-- A positive power-sum shift of any XYZ word already in a higher-key orbit
    stays in that orbit. This removes the Cartan pairing constants. -/
theorem colourPowerShift_mem_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (r : ℕ) (hr : 0 < r)
    (ls : List (Fin 6 × ℕ))
    (hls : ∀ p ∈ ls, p.1 = 1 ∨ p.1 = 4 ∨ p.1 = 5)
    (hmem : radicalWord ρ w ls ∈ higherOrbit ρ w m k)
    (j : Fin 6) (hj : j = 1 ∨ j = 4 ∨ j = 5) :
    colourPowerShift ρ w j r ls ∈ higherOrbit ρ w m k := by
  let N := higherOrbit ρ w m k
  rcases selective_cartan_xyz_power_shift ρ w m h r hr ls hls with
    ⟨hx, hy, hz⟩
  rcases hj with rfl | rfl | rfl
  · have hh : xShiftCartan ρ r (radicalWord ρ w ls) ∈ N := by
      simpa [selectiveCartan] using
        selectiveCartan_higher ρ w m (0 : Fin 3) r k hmem
    rw [hx] at hh
    have hh' := N.smul_mem (2 : ℂ)⁻¹ hh
    simpa [smul_smul] using hh'
  · have hh : yShiftCartan ρ r (radicalWord ρ w ls) ∈ N := by
      simpa [selectiveCartan] using
        selectiveCartan_higher ρ w m (1 : Fin 3) r k hmem
    rw [hy] at hh
    have hh' := N.smul_mem (2 : ℂ)⁻¹ hh
    simpa [smul_smul] using hh'
  · have hh : zShiftCartan ρ r (radicalWord ρ w ls) ∈ N := by
      simpa [selectiveCartan] using
        selectiveCartan_higher ρ w m (2 : Fin 3) r k hmem
    rwa [hz] at hh

/-- The same concrete power-sum shifts preserve every enumerated prefix. -/
theorem colourPowerShift_mem_prefix
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (i r : ℕ) (hi : i < (globalKeyBox m).card) (hr : 0 < r)
    (ls : List (Fin 6 × ℕ))
    (hls : ∀ p ∈ ls, p.1 = 1 ∨ p.1 = 4 ∨ p.1 = 5)
    (hmem : radicalWord ρ w ls ∈ keyPrefix ρ w m i)
    (j : Fin 6) (hj : j = 1 ∨ j = 4 ∨ j = 5) :
    colourPowerShift ρ w j r ls ∈ keyPrefix ρ w m i := by
  rw [keyPrefix_eq_higher ρ w m h i hi] at hmem ⊢
  exact colourPowerShift_mem_higher ρ w m h
    (keyEnum m ⟨i, hi⟩) r hr ls hls hmem j hj

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.selective_cartan_xyz_power_shift
#print axioms VOA.DeligneAudit.D4Levi.colourPowerShift_mem_higher
#print axioms VOA.DeligneAudit.D4Levi.colourPowerShift_mem_prefix
