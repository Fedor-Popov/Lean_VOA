import VOA.DeligneAudit.D4LeviKSLemma0ZeroX

/-! Eliminate U' when all X spectators have mode zero and the remaining tail is f₃-inert. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

theorem fThreeDerivative_inert (r : ℕ) (l : List (Fin 6 × ℕ)) (v : V)
    (hl : l.Forall (fun p => p.1 = 3 ∨ p.1 = 4 ∨ p.1 = 5)) :
    fThreeDerivative ρ r l v = 0 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      rcases p with ⟨j, s⟩
      simp only [List.forall_cons] at hl
      rcases hl.1 with hj | hj | hj
      · subst j
        simp [fThreeDerivative, fThreeLetter, ih hl.2]
      · subst j
        simp [fThreeDerivative, fThreeLetter, ih hl.2]
      · subst j
        simp [fThreeDerivative, fThreeLetter, ih hl.2]

/-- The zero-mode X block produces exactly its multiplicity of U' terms. -/
theorem fThree_zeroXs_inert
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (n r : ℕ) (l : List (Fin 6 × ℕ))
    (hl : l.Forall (fun p => p.1 = 3 ∨ p.1 = 4 ∨ p.1 = 5)) :
    ρ.op (17 : Fin 28) r (radicalWord ρ w (zeroXs (n + 1) ++ l)) =
      -((n + 1 : ℕ) : ℂ) •
        radicalWord ρ w ((3, r) :: zeroXs n ++ l) := by
  induction n with
  | zero =>
      have hd := fThree_radicalWord ρ w m h r ((1, 0) :: l)
      have ht := fThreeDerivative_inert ρ r l w hl
      simpa [zeroXs, fThreeDerivative, fThreeLetter,
        radicalWord, wordOp, radicalColour, ht] using hd
  | succ n ih =>
      have hc := congrArg (fun T : Module.End ℂ V =>
        T (radicalWord ρ w (zeroXs (n + 1) ++ l)))
        (fThree_x_comm ρ r 0)
      have hcomm :
          ρ.op (17 : Fin 28) r
              (ρ.op (22 : Fin 28) 0
                (radicalWord ρ w (zeroXs (n + 1) ++ l))) =
            ρ.op (22 : Fin 28) 0
              (ρ.op (17 : Fin 28) r
                (radicalWord ρ w (zeroXs (n + 1) ++ l))) -
            ρ.op (25 : Fin 28) r
              (radicalWord ρ w (zeroXs (n + 1) ++ l)) := by
        have hc' :
            ρ.op (17 : Fin 28) r
                (ρ.op (22 : Fin 28) 0
                  (radicalWord ρ w (zeroXs (n + 1) ++ l))) -
              ρ.op (22 : Fin 28) 0
                (ρ.op (17 : Fin 28) r
                  (radicalWord ρ w (zeroXs (n + 1) ++ l))) =
              -ρ.op (25 : Fin 28) r
                (radicalWord ρ w (zeroXs (n + 1) ++ l)) := by
          simpa [LinearMap.sub_apply, Module.End.mul_apply] using hc
        calc
          _ = (ρ.op (17 : Fin 28) r
              (ρ.op (22 : Fin 28) 0
                (radicalWord ρ w (zeroXs (n + 1) ++ l))) -
                ρ.op (22 : Fin 28) 0
                  (ρ.op (17 : Fin 28) r
                    (radicalWord ρ w (zeroXs (n + 1) ++ l)))) +
              ρ.op (22 : Fin 28) 0
                (ρ.op (17 : Fin 28) r
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
            (radicalWord ρ w ((3, r) :: zeroXs n ++ l)) =
          radicalWord ρ w ((3, r) :: zeroXs (n + 1) ++ l) := by
        rw [zeroXs_succ n]
        change ρ.op (22 : Fin 28) 0
            (ρ.op (25 : Fin 28) r (radicalWord ρ w (zeroXs n ++ l))) =
          ρ.op (25 : Fin 28) r
            (ρ.op (22 : Fin 28) 0 (radicalWord ρ w (zeroXs n ++ l)))
        exact radical_ops_comm ρ 1 3 0 r _
      rw [hinput, hcomm, ih]
      simp only [map_smul, hswap]
      change -((n + 1 : ℕ) : ℂ) •
          radicalWord ρ w ((3, r) :: zeroXs (n + 1) ++ l) -
        radicalWord ρ w ((3, r) :: zeroXs (n + 1) ++ l) = _
      rw [show (((n + 2 : ℕ) : ℂ)) = ((n + 1 : ℕ) : ℂ) + 1 by
        push_cast; ring]
      simp only [neg_smul, add_smul, one_smul]
      abel

/-- A U' with zero-mode X spectators and an inert tail is a higher-key vector. -/
theorem up_zeroXs_inert_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (n r : ℕ) (l : List (Fin 6 × ℕ))
    (hl : l.Forall (fun p => p.1 = 3 ∨ p.1 = 4 ∨ p.1 = 5)) :
    radicalWord ρ w ((3, r) :: zeroXs n ++ l) ∈
      higherOrbit ρ w m (wordKey ((3, r) :: zeroXs n ++ l)) := by
  let k := wordKey ((3, r) :: zeroXs n ++ l)
  let N := higherOrbit ρ w m k
  have hs : keyLess m k (wordKey (zeroXs (n + 1) ++ l)) := by
    left
    simp [k, keyHeight, wordKey, zeroXs, List.countP_replicate]
  have hsource : radicalWord ρ w (zeroXs (n + 1) ++ l) ∈ N :=
    keyOrbit_le_higher ρ w m k _ hs
      (keyLayer_le_orbit ρ w _
        (radicalWord_mem_key ρ w (zeroXs (n + 1) ++ l)))
  have hf : ρ.op (17 : Fin 28) r
      (radicalWord ρ w (zeroXs (n + 1) ++ l)) ∈ N :=
    higherOrbit_full_levi_inv ρ w m k (17 : Fin 28) ⟨7, rfl⟩ r hsource
  rw [fThree_zeroXs_inert ρ w m h n r l hl] at hf
  have hcoef : (-((n + 1 : ℕ) : ℂ)) ≠ 0 :=
    neg_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero n)
  have hscaled := N.smul_mem (-((n + 1 : ℕ) : ℂ))⁻¹ hf
  simpa only [smul_smul, inv_mul_cancel₀ hcoef, one_smul] using hscaled

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.fThreeDerivative_inert
#print axioms VOA.DeligneAudit.D4Levi.fThree_zeroXs_inert
#print axioms VOA.DeligneAudit.D4Levi.up_zeroXs_inert_higher
