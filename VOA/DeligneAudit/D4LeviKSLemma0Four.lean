import VOA.DeligneAudit.D4LeviKSLemma0Inert

/-! The f₄ companion to the zero-mode X elimination. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- Every f₄ current mode kills the source. -/
theorem fFour_source_mode_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (s : ℕ) : ρ.op (16 : Fin 28) s w = 0 := by
  have hh := VOA.DeligneAudit.A3Sector.a3_simple_conversion_kill
    (leviCurrent ρ) w 0 m 0 (source_localWeyl ρ w m h)
    2 1 s (by omega)
      (by simp [VOA.DeligneAudit.A3Sector.weightABC])
  simpa [VOA.DeligneAudit.LeviConversion.fCurrent, leviCurrent,
    leviColour, leviSign, VOA.DeligneAudit.A3Sector.simpleF] using hh

/-- The f₄ current changes X into minus U. -/
theorem fFour_x_comm (r s : ℕ) :
    ρ.op (16 : Fin 28) r * ρ.op (22 : Fin 28) s -
      ρ.op (22 : Fin 28) s * ρ.op (16 : Fin 28) r =
        -ρ.op (24 : Fin 28) (r + s) := by
  ext v
  have hc := ρ.comm (16 : Fin 28) (22 : Fin 28) r s v
  change ρ.op (16 : Fin 28) r (ρ.op (22 : Fin 28) s v) -
    ρ.op (22 : Fin 28) s (ρ.op (16 : Fin 28) r v) = _
  rw [hc]
  change (∑ c : Fin 28,
    fD4 (lowerColour 1) (radicalColour 1) c • ρ.op c (r + s) v) = _
  have hcoef (c : Fin 28) :
      fD4 (lowerColour 1) (radicalColour 1) c =
        if c = radicalColour 2 then (-1 : ℂ) else 0 := by
    simpa [lowerAction] using lower_coefficient 1 1 c
  simp only [hcoef, ite_smul, neg_one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [radicalColour]

/-- f₄ commutes with each U, Y, or Z current. -/
theorem fFour_inert_comm (j : Fin 6) (r s : ℕ)
    (hj : j = 2 ∨ j = 4 ∨ j = 5) :
    ρ.op (16 : Fin 28) r * ρ.op (radicalColour j) s =
      ρ.op (radicalColour j) s * ρ.op (16 : Fin 28) r := by
  ext v
  have hc := ρ.comm (16 : Fin 28) (radicalColour j) r s v
  have hz : (∑ c : Fin 28,
      fD4 (lowerColour 1) (radicalColour j) c • ρ.op c (r + s) v) = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    rw [lower_coefficient]
    rcases hj with rfl | rfl | rfl <;> simp [lowerAction]
  change ρ.op (16 : Fin 28) r (ρ.op (radicalColour j) s v) -
    ρ.op (radicalColour j) s (ρ.op (16 : Fin 28) r v) =
      (∑ c : Fin 28,
        fD4 (lowerColour 1) (radicalColour j) c • ρ.op c (r + s) v) at hc
  exact sub_eq_zero.mp (hc.trans hz)

/-- f₄ kills any word made of U, Y, and Z. -/
theorem fFour_inert_word_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (r : ℕ) (l : List (Fin 6 × ℕ))
    (hl : l.Forall (fun p => p.1 = 2 ∨ p.1 = 4 ∨ p.1 = 5)) :
    ρ.op (16 : Fin 28) r (radicalWord ρ w l) = 0 := by
  induction l with
  | nil => exact fFour_source_mode_zero ρ w m h r
  | cons p l ih =>
      rcases p with ⟨j, s⟩
      simp only [List.forall_cons] at hl
      have hc := congrArg (fun T : Module.End ℂ V => T (radicalWord ρ w l))
        (fFour_inert_comm ρ j r s hl.1)
      change ρ.op (16 : Fin 28) r
          (ρ.op (radicalColour j) s (radicalWord ρ w l)) =
        ρ.op (radicalColour j) s
          (ρ.op (16 : Fin 28) r (radicalWord ρ w l)) at hc
      change ρ.op (16 : Fin 28) r
          (ρ.op (radicalColour j) s (radicalWord ρ w l)) = 0
      rw [hc, ih hl.2, map_zero]

/-- The zero-mode X block produces exactly its multiplicity of U terms. -/
theorem fFour_zeroXs_inert
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (n r : ℕ) (l : List (Fin 6 × ℕ))
    (hl : l.Forall (fun p => p.1 = 2 ∨ p.1 = 4 ∨ p.1 = 5)) :
    ρ.op (16 : Fin 28) r (radicalWord ρ w (zeroXs (n + 1) ++ l)) =
      -((n + 1 : ℕ) : ℂ) •
        radicalWord ρ w ((2, r) :: zeroXs n ++ l) := by
  induction n with
  | zero =>
      have hc := congrArg (fun T : Module.End ℂ V => T (radicalWord ρ w l))
        (fFour_x_comm ρ r 0)
      have hz := fFour_inert_word_zero ρ w m h r l hl
      have hc' : ρ.op (16 : Fin 28) r
          (ρ.op (22 : Fin 28) 0 (radicalWord ρ w l)) -
          ρ.op (22 : Fin 28) 0
            (ρ.op (16 : Fin 28) r (radicalWord ρ w l)) =
          -ρ.op (24 : Fin 28) r (radicalWord ρ w l) := by
        simpa [LinearMap.sub_apply, Module.End.mul_apply] using hc
      rw [hz] at hc'
      simpa [zeroXs, radicalWord, wordOp, radicalColour] using hc'
  | succ n ih =>
      have hc := congrArg (fun T : Module.End ℂ V =>
        T (radicalWord ρ w (zeroXs (n + 1) ++ l)))
        (fFour_x_comm ρ r 0)
      have hcomm :
          ρ.op (16 : Fin 28) r
              (ρ.op (22 : Fin 28) 0
                (radicalWord ρ w (zeroXs (n + 1) ++ l))) =
            ρ.op (22 : Fin 28) 0
              (ρ.op (16 : Fin 28) r
                (radicalWord ρ w (zeroXs (n + 1) ++ l))) -
            ρ.op (24 : Fin 28) r
              (radicalWord ρ w (zeroXs (n + 1) ++ l)) := by
        have hc' :
            ρ.op (16 : Fin 28) r
                (ρ.op (22 : Fin 28) 0
                  (radicalWord ρ w (zeroXs (n + 1) ++ l))) -
              ρ.op (22 : Fin 28) 0
                (ρ.op (16 : Fin 28) r
                  (radicalWord ρ w (zeroXs (n + 1) ++ l))) =
              -ρ.op (24 : Fin 28) r
                (radicalWord ρ w (zeroXs (n + 1) ++ l)) := by
          simpa [LinearMap.sub_apply, Module.End.mul_apply] using hc
        calc
          _ = (ρ.op (16 : Fin 28) r
              (ρ.op (22 : Fin 28) 0
                (radicalWord ρ w (zeroXs (n + 1) ++ l))) -
                ρ.op (22 : Fin 28) 0
                  (ρ.op (16 : Fin 28) r
                    (radicalWord ρ w (zeroXs (n + 1) ++ l)))) +
              ρ.op (22 : Fin 28) 0
                (ρ.op (16 : Fin 28) r
                  (radicalWord ρ w (zeroXs (n + 1) ++ l))) := by abel
          _ = _ := by rw [hc']; abel
      have hinput :
          radicalWord ρ w (zeroXs (n + 2) ++ l) =
            ρ.op (22 : Fin 28) 0
              (radicalWord ρ w (zeroXs (n + 1) ++ l)) := by
        rw [zeroXs_succ (n + 1)]
        rfl
      have hswap :
          ρ.op (22 : Fin 28) 0
            (radicalWord ρ w ((2, r) :: zeroXs n ++ l)) =
          radicalWord ρ w ((2, r) :: zeroXs (n + 1) ++ l) := by
        rw [zeroXs_succ n]
        change ρ.op (22 : Fin 28) 0
            (ρ.op (24 : Fin 28) r (radicalWord ρ w (zeroXs n ++ l))) =
          ρ.op (24 : Fin 28) r
            (ρ.op (22 : Fin 28) 0 (radicalWord ρ w (zeroXs n ++ l)))
        exact radical_ops_comm ρ 1 2 0 r _
      rw [hinput, hcomm, ih]
      simp only [map_smul, hswap]
      change -((n + 1 : ℕ) : ℂ) •
          radicalWord ρ w ((2, r) :: zeroXs (n + 1) ++ l) -
        radicalWord ρ w ((2, r) :: zeroXs (n + 1) ++ l) = _
      rw [show (((n + 2 : ℕ) : ℂ)) = ((n + 1 : ℕ) : ℂ) + 1 by
        push_cast; ring]
      simp only [neg_smul, add_smul, one_smul]
      abel

/-- A U with zero-mode X spectators and an inert tail is a higher-key vector. -/
theorem u_zeroXs_inert_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (n r : ℕ) (l : List (Fin 6 × ℕ))
    (hl : l.Forall (fun p => p.1 = 2 ∨ p.1 = 4 ∨ p.1 = 5)) :
    radicalWord ρ w ((2, r) :: zeroXs n ++ l) ∈
      higherOrbit ρ w m (wordKey ((2, r) :: zeroXs n ++ l)) := by
  let k := wordKey ((2, r) :: zeroXs n ++ l)
  let N := higherOrbit ρ w m k
  have hs : keyLess m k (wordKey (zeroXs (n + 1) ++ l)) := by
    left
    simp [k, keyHeight, wordKey, zeroXs, List.countP_replicate]
  have hsource : radicalWord ρ w (zeroXs (n + 1) ++ l) ∈ N :=
    keyOrbit_le_higher ρ w m k _ hs
      (keyLayer_le_orbit ρ w _
        (radicalWord_mem_key ρ w (zeroXs (n + 1) ++ l)))
  have hf : ρ.op (16 : Fin 28) r
      (radicalWord ρ w (zeroXs (n + 1) ++ l)) ∈ N :=
    higherOrbit_full_levi_inv ρ w m k (16 : Fin 28) ⟨12, rfl⟩ r hsource
  rw [fFour_zeroXs_inert ρ w m h n r l hl] at hf
  have hcoef : (-((n + 1 : ℕ) : ℂ)) ≠ 0 :=
    neg_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero n)
  have hscaled := N.smul_mem (-((n + 1 : ℕ) : ℂ))⁻¹ hf
  simpa only [smul_smul, inv_mul_cancel₀ hcoef, one_smul] using hscaled

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.fFour_source_mode_zero
#print axioms VOA.DeligneAudit.D4Levi.fFour_x_comm
#print axioms VOA.DeligneAudit.D4Levi.fFour_inert_comm
#print axioms VOA.DeligneAudit.D4Levi.fFour_inert_word_zero
#print axioms VOA.DeligneAudit.D4Levi.fFour_zeroXs_inert
#print axioms VOA.DeligneAudit.D4Levi.u_zeroXs_inert_higher
