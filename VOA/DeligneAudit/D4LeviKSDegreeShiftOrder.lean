import VOA.DeligneAudit.D4LeviKSMixedShift

/-! Key order is unchanged by a common positive-mode shift. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

theorem keyHeight_shift (m r : ℕ) (k : RadicalKey) :
    keyHeight m (keyShift r k) = keyHeight m k := by
  rfl

theorem keyLess_shift_iff (m r : ℕ) (k j : RadicalKey) :
    keyLess m (keyShift r k) (keyShift r j) ↔ keyLess m k j := by
  rcases k with ⟨ke, kx, ku, kup, ky, kz, kd⟩
  rcases j with ⟨je, jx, ju, jup, jy, jz, jd⟩
  simp only [keyShift, keyLess, keyHeight]
  constructor <;> intro h <;> omega

theorem keyShift_add (r s : ℕ) (k : RadicalKey) :
    keyShift r (keyShift s k) = keyShift (r + s) k := by
  cases k
  simp [keyShift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Each positive selective Cartan current raises the degree of an exact
    radical key by its mode, without changing its six letter counts. -/
theorem selectiveCartan_maps_key
    (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (q : Fin 3) (r : ℕ) (hr : 0 < r) (k : RadicalKey)
    {v : V} (hv : v ∈ keyLayer ρ w k) :
    selectiveCartan ρ q r v ∈ keyLayer ρ w (keyShift r k) := by
  let N := keyLayer ρ w (keyShift r k)
  have h0 := cartan_pos_maps_key ρ w m h 0 r hr k hv
  have h1 := cartan_pos_maps_key ρ w m h 1 r hr k hv
  have he := extra_pos_key ρ w m h r hr k hv
  fin_cases q
  · change (1 : ℂ) •
      ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH 0)) r v +
      (0 : ℂ) •
      ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH 1)) r v +
      (-1 : ℂ) • ρ.op (0 : Fin 28) r v ∈ N
    exact N.add_mem (N.add_mem (N.smul_mem _ h0) (N.smul_mem _ h1))
      (N.smul_mem _ he)
  · change (-1 : ℂ) •
      ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH 0)) r v +
      (0 : ℂ) •
      ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH 1)) r v +
      (-1 : ℂ) • ρ.op (0 : Fin 28) r v ∈ N
    exact N.add_mem (N.add_mem (N.smul_mem _ h0) (N.smul_mem _ h1))
      (N.smul_mem _ he)
  · change (-1 : ℂ) •
      ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH 0)) r v +
      (-1 : ℂ) •
      ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH 1)) r v +
      (0 : ℂ) • ρ.op (0 : Fin 28) r v ∈ N
    exact N.add_mem (N.add_mem (N.smul_mem _ h0) (N.smul_mem _ h1))
      (N.smul_mem _ he)

/-- A word of positive selective Cartan currents shifts the exact radical
    key by the sum of its modes. -/
theorem selectiveCartanWord_maps_key
    (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (ps : List (Fin 3 × ℕ))
    (hps : ∀ p ∈ ps, 0 < p.2) (k : RadicalKey)
    {v : V} (hv : v ∈ keyLayer ρ w k) :
    selectiveCartanWord ρ ps v ∈
      keyLayer ρ w (keyShift (ps.map Prod.snd).sum k) := by
  induction ps with
  | nil => simpa [selectiveCartanWord, keyShift] using hv
  | cons p ps ih =>
      have hp : 0 < p.2 := hps p (by simp)
      have htail : ∀ q ∈ ps, 0 < q.2 := by
        intro q hq
        exact hps q (by simp [hq])
      have hstep := selectiveCartan_maps_key ρ w m h p.1 p.2 hp
        (keyShift (ps.map Prod.snd).sum k) (ih htail)
      simpa [selectiveCartanWord, keyShift_add] using hstep

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.keyHeight_shift
#print axioms VOA.DeligneAudit.D4Levi.keyLess_shift_iff
#print axioms VOA.DeligneAudit.D4Levi.keyShift_add
#print axioms VOA.DeligneAudit.D4Levi.selectiveCartan_maps_key
#print axioms VOA.DeligneAudit.D4Levi.selectiveCartanWord_maps_key
