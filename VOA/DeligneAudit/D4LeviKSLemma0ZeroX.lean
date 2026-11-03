import VOA.DeligneAudit.D4LeviKSLemma0YZ

/-! The zero-mode X multiplicity in the f₃ polarization identity. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- A block of zero-mode X letters. -/
def zeroXs (n : ℕ) : List (Fin 6 × ℕ) :=
  List.replicate n (1, 0)

theorem zeroXs_succ (n : ℕ) :
    zeroXs (n + 1) = (1, 0) :: zeroXs n := by
  simp [zeroXs, List.replicate_succ]

private theorem zeroXs_countP (j : Fin 6) (n : ℕ) :
    (zeroXs n).countP (fun p => p.1 = j) = if j = 1 then n else 0 := by
  simp [zeroXs, List.countP_replicate, eq_comm]

private theorem zeroXs_modes (n : ℕ) :
    ((zeroXs n).map Prod.snd).sum = 0 := by
  induction n with
  | zero => simp [zeroXs]
  | succ n ih => simp [zeroXs_succ, ih]

/-- Polarization with any number of zero-mode X spectators and a YZ tail. -/
theorem fThree_zeroXs_u_yz
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (n r u : ℕ) (l : List (Fin 6 × ℕ))
    (hl : l.Forall (fun p => p.1 = 4 ∨ p.1 = 5)) :
    ρ.op (17 : Fin 28) r
        (radicalWord ρ w (zeroXs (n + 1) ++ (2, u) :: l)) =
      -((n + 1 : ℕ) : ℂ) •
        radicalWord ρ w ((3, r) :: zeroXs n ++ (2, u) :: l) -
      radicalWord ρ w (zeroXs (n + 1) ++ (4, r + u) :: l) := by
  induction n with
  | zero =>
      have hd := fThree_radicalWord ρ w m h r ((1, 0) :: (2, u) :: l)
      have ht := fThreeDerivative_yz_zero ρ r l w hl
      simpa [zeroXs, fThreeDerivative, fThreeLetter, radicalWord,
        wordOp, radicalColour, ht, sub_eq_add_neg] using hd
  | succ n ih =>
      have hc := congrArg (fun T : Module.End ℂ V =>
        T (radicalWord ρ w (zeroXs (n + 1) ++ (2, u) :: l)))
        (fThree_x_comm ρ r 0)
      have hcomm :
          ρ.op (17 : Fin 28) r
            (ρ.op (22 : Fin 28) 0
              (radicalWord ρ w (zeroXs (n + 1) ++ (2, u) :: l))) =
          ρ.op (22 : Fin 28) 0
            (ρ.op (17 : Fin 28) r
              (radicalWord ρ w (zeroXs (n + 1) ++ (2, u) :: l))) -
          ρ.op (25 : Fin 28) r
            (radicalWord ρ w (zeroXs (n + 1) ++ (2, u) :: l)) := by
        have hc' :
            ρ.op (17 : Fin 28) r
              (ρ.op (22 : Fin 28) 0
                (radicalWord ρ w (zeroXs (n + 1) ++ (2, u) :: l))) -
            ρ.op (22 : Fin 28) 0
              (ρ.op (17 : Fin 28) r
                (radicalWord ρ w (zeroXs (n + 1) ++ (2, u) :: l))) =
            -ρ.op (25 : Fin 28) r
              (radicalWord ρ w (zeroXs (n + 1) ++ (2, u) :: l)) := by
          simpa [LinearMap.sub_apply, Module.End.mul_apply] using hc
        calc
          _ = (ρ.op (17 : Fin 28) r
              (ρ.op (22 : Fin 28) 0
                (radicalWord ρ w (zeroXs (n + 1) ++ (2, u) :: l))) -
              ρ.op (22 : Fin 28) 0
                (ρ.op (17 : Fin 28) r
                  (radicalWord ρ w (zeroXs (n + 1) ++ (2, u) :: l)))) +
              ρ.op (22 : Fin 28) 0
                (ρ.op (17 : Fin 28) r
                  (radicalWord ρ w (zeroXs (n + 1) ++ (2, u) :: l))) := by abel
          _ = _ := by rw [hc']; abel
      have hinput :
          radicalWord ρ w (zeroXs (n + 2) ++ (2, u) :: l) =
            ρ.op (22 : Fin 28) 0
              (radicalWord ρ w (zeroXs (n + 1) ++ (2, u) :: l)) := by
        rw [zeroXs_succ (n + 1)]
        rfl
      have hswap :
          ρ.op (22 : Fin 28) 0
            (radicalWord ρ w ((3, r) :: zeroXs n ++ (2, u) :: l)) =
          radicalWord ρ w ((3, r) :: zeroXs (n + 1) ++ (2, u) :: l) := by
        rw [zeroXs_succ n]
        change ρ.op (22 : Fin 28) 0
            (ρ.op (25 : Fin 28) r
              (radicalWord ρ w (zeroXs n ++ (2, u) :: l))) =
          ρ.op (25 : Fin 28) r
            (ρ.op (22 : Fin 28) 0
              (radicalWord ρ w (zeroXs n ++ (2, u) :: l)))
        exact radical_ops_comm ρ 1 3 0 r _
      have hy :
          ρ.op (22 : Fin 28) 0
            (radicalWord ρ w (zeroXs (n + 1) ++ (4, r + u) :: l)) =
          radicalWord ρ w (zeroXs (n + 2) ++ (4, r + u) :: l) := by
        rw [zeroXs_succ (n + 1)]
        rfl
      rw [hinput, hcomm, ih]
      simp only [map_sub, map_smul, hswap, hy]
      change -((n + 1 : ℕ) : ℂ) •
          radicalWord ρ w ((3, r) :: zeroXs (n + 1) ++ (2, u) :: l) -
        radicalWord ρ w (zeroXs (n + 2) ++ (4, r + u) :: l) -
        radicalWord ρ w ((3, r) :: zeroXs (n + 1) ++ (2, u) :: l) = _
      rw [show (((n + 2 : ℕ) : ℂ)) = ((n + 1 : ℕ) : ℂ) + 1 by
        push_cast; ring]
      simp only [Nat.add_assoc, neg_smul, add_smul, one_smul]
      abel

/-- A U'U pair is higher with arbitrary zero-mode X spectators and a YZ tail. -/
theorem uup_zeroXs_yz_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (n r u : ℕ) (l : List (Fin 6 × ℕ))
    (hl : l.Forall (fun p => p.1 = 4 ∨ p.1 = 5)) :
    radicalWord ρ w ((3, r) :: zeroXs n ++ (2, u) :: l) ∈
      higherOrbit ρ w m (wordKey ((3, r) :: zeroXs n ++ (2, u) :: l)) := by
  let k := wordKey ((3, r) :: zeroXs n ++ (2, u) :: l)
  let N := higherOrbit ρ w m k
  have hs : keyLess m k (wordKey (zeroXs (n + 1) ++ (2, u) :: l)) := by
    left
    simp [k, keyHeight, wordKey, zeroXs_countP]
  have hy : keyLess m k (wordKey (zeroXs (n + 1) ++ (4, r + u) :: l)) := by
    simp [k, keyLess, keyHeight, wordKey, zeroXs_countP, zeroXs_modes]
    omega
  have hsource : radicalWord ρ w (zeroXs (n + 1) ++ (2, u) :: l) ∈ N :=
    keyOrbit_le_higher ρ w m k _ hs
      (keyLayer_le_orbit ρ w _
        (radicalWord_mem_key ρ w (zeroXs (n + 1) ++ (2, u) :: l)))
  have hf : ρ.op (17 : Fin 28) r
      (radicalWord ρ w (zeroXs (n + 1) ++ (2, u) :: l)) ∈ N :=
    higherOrbit_full_levi_inv ρ w m k (17 : Fin 28) ⟨7, rfl⟩ r hsource
  have hyMem : radicalWord ρ w (zeroXs (n + 1) ++ (4, r + u) :: l) ∈ N :=
    keyOrbit_le_higher ρ w m k _ hy
      (keyLayer_le_orbit ρ w _
        (radicalWord_mem_key ρ w (zeroXs (n + 1) ++ (4, r + u) :: l)))
  rw [fThree_zeroXs_u_yz ρ w m h n r u l hl] at hf
  have hneg : -((n + 1 : ℕ) : ℂ) •
      radicalWord ρ w ((3, r) :: zeroXs n ++ (2, u) :: l) ∈ N := by
    simpa only [sub_add_cancel] using N.add_mem hf hyMem
  have hcoef : (-((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact neg_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero n)
  have hscaled := N.smul_mem (-((n + 1 : ℕ) : ℂ))⁻¹ hneg
  simpa only [smul_smul, inv_mul_cancel₀ hcoef, one_smul] using hscaled

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.fThree_zeroXs_u_yz
#print axioms VOA.DeligneAudit.D4Levi.uup_zeroXs_yz_higher
