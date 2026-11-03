import VOA.DeligneAudit.D4LeviKSPairZero

/-! Repeated U-to-Y conversion in the f₃ adjoint action. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def uZeroWord (n : ℕ) : List (Fin 6 × ℕ) :=
  List.replicate n (2, 0)

def yModeWord (rs : List ℕ) : List (Fin 6 × ℕ) :=
  rs.map fun r => (4, r)

def zModeWord (rs : List ℕ) : List (Fin 6 × ℕ) :=
  rs.map fun r => (5, r)

private theorem threeWords_yModeWord (r : ℕ) (rs : List ℕ) :
    threeWords r (yModeWord rs) = [] := by
  induction rs with
  | nil => rfl
  | cons s rs ih => simpa [yModeWord, threeWords] using ih

/-- One f₃ mode converts any one of the `n+1` zero-mode U letters.
    After commuting radical letters, all resulting words coincide. -/
theorem threeWords_uZero_sum
    (ρ : CurrentModule D4sector.f V) (v : V)
    (r n : ℕ) (rs : List ℕ) :
    ((threeWords r (uZeroWord (n + 1) ++ yModeWord rs)).map
      (radicalWord ρ v)).sum =
        (n + 1) • radicalWord ρ v
          (uZeroWord n ++ yModeWord (r :: rs)) := by
  induction n with
  | zero =>
      have htail := threeWords_yModeWord r rs
      simp [uZeroWord, yModeWord, threeWords, htail] at *
  | succ n ih =>
      have hrep : uZeroWord (n + 1 + 1) =
          (2, 0) :: uZeroWord (n + 1) := by
        simp [uZeroWord, List.replicate_succ]
      have hmap (ls : List (List (Fin 6 × ℕ))) :
          (ls.map fun q => radicalWord ρ v ((2, 0) :: q)).sum =
            ρ.op (radicalColour (2 : Fin 6)) 0
              ((ls.map (radicalWord ρ v)).sum) := by
        rw [map_list_sum]
        simp only [List.map_map, Function.comp_def]
        rfl
      have htail := hmap (threeWords r (uZeroWord (n + 1) ++ yModeWord rs))
      rw [ih] at htail
      have hperm :
          radicalWord ρ v ((4, r) :: uZeroWord (n + 1) ++ yModeWord rs) =
            radicalWord ρ v
              (uZeroWord (n + 1) ++ yModeWord (r :: rs)) := by
        apply radicalWord_perm ρ v
        simpa [yModeWord] using
          (List.perm_append_comm (l₁ := [(4, r)])
            (l₂ := uZeroWord (n + 1))).append_right (yModeWord rs)
      rw [hrep, List.cons_append, threeWords]
      simp only [if_false, if_true, List.singleton_append,
        List.map_append, List.sum_append, List.map_singleton,
        List.sum_singleton, List.map_map, Function.comp_def]
      rw [htail]
      simp only [map_nsmul]
      have ht :
          ρ.op (radicalColour (2 : Fin 6)) 0
              (radicalWord ρ v (uZeroWord n ++ yModeWord (r :: rs))) =
            radicalWord ρ v (uZeroWord (n + 1) ++ yModeWord (r :: rs)) := by
        change radicalWord ρ v ((2, 0) ::
          (uZeroWord n ++ yModeWord (r :: rs))) = _
        simp [uZeroWord, List.replicate_succ]
      simp only [show (2 : Fin 6) ≠ 1 by decide, if_false,
        Nat.add_zero, List.map_singleton, List.sum_singleton]
      rw [ht]
      simp only [List.cons_append] at hperm
      rw [hperm]
      simp only [add_nsmul, two_nsmul]
      abel

/-- The one-mode U conversion as an identity of word operators. -/
theorem fThree_adjoint_uZero_one
    (ρ : CurrentModule D4sector.f V) (r n : ℕ) (ys : List ℕ) :
    pairAdjoint (ρ.op (17 : Fin 28)) [r]
        (pairRadicalOp ρ (uZeroWord (n + 1) ++ yModeWord ys)) =
      -((n + 1 : ℂ) • pairRadicalOp ρ
        (uZeroWord n ++ yModeWord (r :: ys))) := by
  have hsum :
      ((threeWords r (uZeroWord (n + 1) ++ yModeWord ys)).map
        (pairRadicalOp ρ)).sum =
          (n + 1 : ℂ) • pairRadicalOp ρ
            (uZeroWord n ++ yModeWord (r :: ys)) := by
    apply LinearMap.ext
    intro v
    simp only [pairRadicalOp_sum_apply, LinearMap.smul_apply,
      pairRadicalOp_apply]
    have hcast : (n + 1 : ℂ) •
        radicalWord ρ v (uZeroWord n ++ yModeWord (r :: ys)) =
          (n + 1) • radicalWord ρ v
            (uZeroWord n ++ yModeWord (r :: ys)) := by
      norm_cast
    rw [hcast]
    exact threeWords_uZero_sum ρ v r n ys
  simpa only [pairAdjoint, fThree_adjoint_radicalOp, hsum]

theorem pairAdjoint_smul (F : ℕ → Module.End ℂ V)
    (rs : List ℕ) (z : ℂ) (A : Module.End ℂ V) :
    pairAdjoint F rs (z • A) = z • pairAdjoint F rs A := by
  induction rs generalizing A with
  | nil => rfl
  | cons r rs ih =>
      have h : F r * (z • A) - (z • A) * F r =
          z • (F r * A - A * F r) := by
        apply LinearMap.ext
        intro v
        simp only [LinearMap.sub_apply, Module.End.mul_apply,
          LinearMap.smul_apply, map_smul, smul_sub]
      simp only [pairAdjoint, h, ih]

/-- All f₃ modes convert all zero-mode U letters. The conversion factor is
    `b!`, and the D4 bracket contributes `(-1)^b`. -/
theorem fThree_adjoint_uZero_factorial
    (ρ : CurrentModule D4sector.f V) (rs ys : List ℕ) :
    pairAdjoint (ρ.op (17 : Fin 28)) rs
        (pairRadicalOp ρ (uZeroWord rs.length ++ yModeWord ys)) =
      (-1 : ℂ) ^ rs.length •
        ((Nat.factorial rs.length : ℂ) • pairRadicalOp ρ
          (yModeWord (rs.reverse ++ ys))) := by
  induction rs generalizing ys with
  | nil => simp [pairAdjoint, uZeroWord, yModeWord]
  | cons r rs ih =>
      have hone := fThree_adjoint_uZero_one ρ r rs.length ys
      change pairAdjoint (ρ.op (17 : Fin 28)) rs
          (pairAdjoint (ρ.op (17 : Fin 28)) [r]
            (pairRadicalOp ρ
              (uZeroWord (rs.length + 1) ++ yModeWord ys))) = _
      rw [hone, pairAdjoint_neg, pairAdjoint_smul, ih]
      simp only [List.length_cons, List.reverse_cons, Nat.factorial_succ]
      simp [smul_smul, pow_succ, mul_comm, mul_left_comm, mul_assoc]

/-- Radical commutativity transports a permutation of mode-labelled words
    to equality of their word operators. -/
theorem pairRadicalOp_perm (ρ : CurrentModule D4sector.f V)
    {l₁ l₂ : List (Fin 6 × ℕ)} (hp : l₁.Perm l₂) :
    pairRadicalOp ρ l₁ = pairRadicalOp ρ l₂ := by
  apply LinearMap.ext
  intro v
  simpa only [pairRadicalOp_apply] using radicalWord_perm ρ v hp

/-- The arbitrary-mode `b!` conversion, with the Y modes in input order. -/
theorem fThree_adjoint_uZero_factorial_ordered
    (ρ : CurrentModule D4sector.f V) (rs : List ℕ) :
    pairAdjoint (ρ.op (17 : Fin 28)) rs
        (pairRadicalOp ρ (uZeroWord rs.length)) =
      (-1 : ℂ) ^ rs.length •
        ((Nat.factorial rs.length : ℂ) • pairRadicalOp ρ (yModeWord rs)) := by
  have h := fThree_adjoint_uZero_factorial ρ rs []
  have h' : pairAdjoint (ρ.op (17 : Fin 28)) rs
      (pairRadicalOp ρ (uZeroWord rs.length)) =
        (-1 : ℂ) ^ rs.length •
          ((Nat.factorial rs.length : ℂ) •
            pairRadicalOp ρ (yModeWord rs.reverse)) := by
    simpa [yModeWord] using h
  have hp : (yModeWord rs.reverse).Perm (yModeWord rs) := by
    exact (List.reverse_perm rs).map (fun r => ((4 : Fin 6), r))
  rw [pairRadicalOp_perm ρ hp] at h'
  exact h'

theorem pairRadicalOp_append (ρ : CurrentModule D4sector.f V)
    (l₁ l₂ : List (Fin 6 × ℕ)) :
    pairRadicalOp ρ (l₁ ++ l₂) =
      pairRadicalOp ρ l₁ * pairRadicalOp ρ l₂ := by
  simp [pairRadicalOp, List.map_append, List.prod_append]

private theorem threeWords_zModeWord (r : ℕ) (zs : List ℕ) :
    threeWords r (zModeWord zs) = [] := by
  induction zs with
  | nil => rfl
  | cons z zs ih => simpa [zModeWord, threeWords] using ih

theorem fThree_comm_zModeWord (ρ : CurrentModule D4sector.f V)
    (r : ℕ) (zs : List ℕ) :
    ρ.op (17 : Fin 28) r * pairRadicalOp ρ (zModeWord zs) =
      pairRadicalOp ρ (zModeWord zs) * ρ.op (17 : Fin 28) r := by
  have h := fThree_adjoint_radicalOp ρ r (zModeWord zs)
  simp only [threeWords_zModeWord, List.map_nil, List.sum_nil,
    neg_zero, sub_eq_zero] at h
  exact h

theorem pairAdjoint_mul_right (F : ℕ → Module.End ℂ V)
    (rs : List ℕ) (A B : Module.End ℂ V)
    (hB : ∀ r, F r * B = B * F r) :
    pairAdjoint F rs (A * B) = pairAdjoint F rs A * B := by
  induction rs generalizing A with
  | nil => rfl
  | cons r rs ih =>
      have h : F r * (A * B) - (A * B) * F r =
          (F r * A - A * F r) * B := by
        calc
          F r * (A * B) - (A * B) * F r =
              (F r * A) * B - A * (B * F r) := by simp [mul_assoc]
          _ = (F r * A) * B - (A * F r) * B := by
            rw [← hB r]
            simp only [mul_assoc]
          _ = (F r * A - A * F r) * B := by rw [sub_mul]
      simpa only [pairAdjoint, h] using ih (F r * A - A * F r)

/-- The `b!` U-to-Y formula with arbitrary Z spectator modes. -/
theorem fThree_adjoint_uZero_z_factorial
    (ρ : CurrentModule D4sector.f V) (rs zs : List ℕ) :
    pairAdjoint (ρ.op (17 : Fin 28)) rs
        (pairRadicalOp ρ (uZeroWord rs.length ++ zModeWord zs)) =
      (-1 : ℂ) ^ rs.length •
        ((Nat.factorial rs.length : ℂ) •
          pairRadicalOp ρ (yModeWord rs ++ zModeWord zs)) := by
  rw [pairRadicalOp_append]
  rw [pairAdjoint_mul_right _ _ _ _ (fThree_comm_zModeWord ρ · zs)]
  rw [fThree_adjoint_uZero_factorial_ordered]
  rw [pairRadicalOp_append]
  simp only [smul_mul_assoc]

/-- The factorial formula after applying the operator to any vector. -/
theorem fThree_adjoint_uZero_z_factorial_word
    (ρ : CurrentModule D4sector.f V) (w : V)
    (rs zs : List ℕ) :
    pairAdjoint (ρ.op (17 : Fin 28)) rs
        (pairRadicalOp ρ (uZeroWord rs.length ++ zModeWord zs)) w =
      (-1 : ℂ) ^ rs.length •
        ((Nat.factorial rs.length : ℂ) •
          radicalWord ρ w (yModeWord rs ++ zModeWord zs)) := by
  have h := congrArg (fun A : Module.End ℂ V => A w)
    (fThree_adjoint_uZero_z_factorial ρ rs zs)
  simpa only [LinearMap.smul_apply, pairRadicalOp_apply] using h

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.threeWords_uZero_sum
#print axioms VOA.DeligneAudit.D4Levi.fThree_adjoint_uZero_one
#print axioms VOA.DeligneAudit.D4Levi.pairAdjoint_smul
#print axioms VOA.DeligneAudit.D4Levi.fThree_adjoint_uZero_factorial
#print axioms VOA.DeligneAudit.D4Levi.pairRadicalOp_perm
#print axioms VOA.DeligneAudit.D4Levi.fThree_adjoint_uZero_factorial_ordered
#print axioms VOA.DeligneAudit.D4Levi.pairRadicalOp_append
#print axioms VOA.DeligneAudit.D4Levi.fThree_comm_zModeWord
#print axioms VOA.DeligneAudit.D4Levi.pairAdjoint_mul_right
#print axioms VOA.DeligneAudit.D4Levi.fThree_adjoint_uZero_z_factorial
#print axioms VOA.DeligneAudit.D4Levi.fThree_adjoint_uZero_z_factorial_word
