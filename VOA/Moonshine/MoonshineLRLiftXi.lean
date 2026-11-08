import VOA.Moonshine.MoonshineLRLiftLiftable4

/-!
# The nonmonomial Conway generator in MOG coordinates

On each MOG column use `diag(1,-1,-1,-1) * (J - 2I) / 2`.
The coordinate numbering is the existing `Code.coord r j = r + 4*j`.
`liftXiInt_mem` proves lattice preservation directly from the MOG hexacode and
parity conditions. The induced integral map `liftXi` is a surjective isometry
with cube equal to the identity.

The spin matrix is obtained by rational descent, without a table of entries.
A rational linear functional applied entrywise to the complex charge matrix
produces a nonzero rational intertwiner. Schur's lemma makes it `z` times the
normalized charge matrix. Orthogonality makes `z^2` rational. Since `liftXi^3 = 1`,
the cube of the charge matrix normalizes the separating diagonal spin operators,
so is a rational signed permutation; consequently `z^3` is rational as well.
Thus `z = z^3 / z^2` is rational, giving `liftXiSpinMatrix` and `liftXi_liftable`.

The rational spin matrix is noncomputably chosen. An entrywise Hadamard formula
and bounds on its denominators are not asserted here.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen
open VOA.Moonshine.AutMonster VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterAction
open VOA.Moonshine.MonsterGriess.Spin
open VOA.Moonshine.MonsterGriess.LeechMatch
open scoped Matrix

/-- MOG column coordinates, with the column index first. -/
def liftXiCoords : Fin 6 × Fin 4 ≃ Fin 24 where
  toFun p := MonsterGriess.Code.coord p.2 p.1
  invFun i := (MonsterGriess.Code.col i, MonsterGriess.Code.row i)
  left_inv p := by
    rcases p with ⟨j, r⟩
    apply Prod.ext <;> apply Fin.ext <;>
      simp only [MonsterGriess.Code.coord, MonsterGriess.Code.col,
        MonsterGriess.Code.row] <;> omega
  right_inv := MonsterGriess.Code.coord_row_col

theorem liftXiRow_coord (r : Fin 4) (j : Fin 6) :
    MonsterGriess.Code.row (MonsterGriess.Code.coord r j) = r := by
  exact congrArg Prod.snd (liftXiCoords.symm_apply_apply (j, r))

theorem liftXiCol_coord (r : Fin 4) (j : Fin 6) :
    MonsterGriess.Code.col (MonsterGriess.Code.coord r j) = j := by
  exact congrArg Prod.fst (liftXiCoords.symm_apply_apply (j, r))

theorem liftXiSum_coords {A : Type*} [AddCommMonoid A] (u : Fin 24 → A) :
    ∑ i, u i = ∑ j : Fin 6, ∑ r : Fin 4, u (MonsterGriess.Code.coord r j) := by
  rw [← Equiv.sum_comp liftXiCoords, Fintype.sum_prod_type]
  rfl

/-- The four by four rational Conway block. -/
def liftXiBlock (u : Fin 4 → ℚ) : Fin 4 → ℚ :=
  fun r => if r = 0 then (∑ s, u s) / 2 - u r else u r - (∑ s, u s) / 2

theorem liftXiBlock_add (u v : Fin 4 → ℚ) :
    liftXiBlock (u + v) = liftXiBlock u + liftXiBlock v := by
  ext r
  simp only [liftXiBlock, Pi.add_apply, Finset.sum_add_distrib]
  split_ifs <;> ring

theorem liftXiBlock_smul (a : ℚ) (u : Fin 4 → ℚ) :
    liftXiBlock (a • u) = a • liftXiBlock u := by
  ext r
  simp only [liftXiBlock, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  split_ifs <;> ring

theorem liftXiBlock_cube (u : Fin 4 → ℚ) :
    liftXiBlock (liftXiBlock (liftXiBlock u)) = u := by
  ext r
  fin_cases r <;> norm_num [liftXiBlock, Fin.sum_univ_succ] <;> ring

theorem liftXiBlock_dot (u v : Fin 4 → ℚ) :
    liftXiBlock u ⬝ᵥ liftXiBlock v = u ⬝ᵥ v := by
  norm_num [dotProduct, liftXiBlock, Fin.sum_univ_succ]
  ring

/-- The rational coordinate action of Conway's generator. -/
def liftXiRat : (Fin 24 → ℚ) →ₗ[ℚ] (Fin 24 → ℚ) where
  toFun u i := liftXiBlock (fun r => u (MonsterGriess.Code.coord r
    (MonsterGriess.Code.col i))) (MonsterGriess.Code.row i)
  map_add' u v := by
    ext i
    exact congrFun (liftXiBlock_add _ _) _
  map_smul' a u := by
    ext i
    exact congrFun (liftXiBlock_smul a _) _

theorem liftXiRat_coord (u : Fin 24 → ℚ) (r : Fin 4) (j : Fin 6) :
    liftXiRat u (MonsterGriess.Code.coord r j) =
      liftXiBlock (fun s => u (MonsterGriess.Code.coord s j)) r := by
  simp only [liftXiRat, LinearMap.coe_mk, AddHom.coe_mk,
    liftXiCol_coord, liftXiRow_coord]

theorem liftXiRat_cube (u : Fin 24 → ℚ) : liftXiRat (liftXiRat (liftXiRat u)) = u := by
  ext i
  obtain ⟨⟨j, r⟩, rfl⟩ := liftXiCoords.surjective i
  change liftXiRat (liftXiRat (liftXiRat u)) (MonsterGriess.Code.coord r j) = _
  simp only [liftXiRat_coord]
  exact congrFun (liftXiBlock_cube _) r

theorem liftXiRat_dot (u v : Fin 24 → ℚ) : liftXiRat u ⬝ᵥ liftXiRat v = u ⬝ᵥ v := by
  simp only [dotProduct, liftXiSum_coords, liftXiRat_coord]
  exact Finset.sum_congr rfl fun j _ => liftXiBlock_dot _ _

/-- A MOG column sum in the integral Conway model. -/
def liftXiColSum (u : Fin 24 → ℤ) (j : Fin 6) : ℤ :=
  ∑ r : Fin 4, u (MonsterGriess.Code.coord r j)

/-- The integral formula, once the column sums have been proved even. -/
def liftXiInt (u : Fin 24 → ℤ) (i : Fin 24) : ℤ :=
  if MonsterGriess.Code.row i = 0 then liftXiColSum u (MonsterGriess.Code.col i) / 2 - u i
  else u i - liftXiColSum u (MonsterGriess.Code.col i) / 2

theorem liftXiInt_coord (u : Fin 24 → ℤ) (r : Fin 4) (j : Fin 6) :
    liftXiInt u (MonsterGriess.Code.coord r j) =
      if r = 0 then liftXiColSum u j / 2 - u (MonsterGriess.Code.coord r j)
      else u (MonsterGriess.Code.coord r j) - liftXiColSum u j / 2 := by
  simp only [liftXiInt, liftXiRow_coord, liftXiCol_coord]

/-- Column halves are integral and have one common parity on a Leech vector. -/
theorem liftXiCol_parity {u : Fin 24 → ℤ} {m : ℤ} {d : Fin 24 → ZMod 2}
    (hd : d ∈ MonsterGriess.Code.C)
    (hu : ∀ i, u i ≡ m + 2 * bitLift (d i) [ZMOD 4]) (j : Fin 6) :
    liftXiColSum u j % 2 = 0 ∧
      (liftXiColSum u j / 2) % 2 =
        (∑ k : Fin 6, bitLift (d (MonsterGriess.Code.coord 0 k))) % 2 := by
  have hp : (∑ r : Fin 4, bitLift (d (MonsterGriess.Code.coord r j))) % 2 =
      (∑ k : Fin 6, bitLift (d (MonsterGriess.Code.coord 0 k))) % 2 := by
    apply (ZMod.intCast_eq_intCast_iff' _ _ 2).mp
    simpa only [Int.cast_sum, MonsterGriess.Code.bitLift_cast] using hd.2 j
  have h0 := hu (MonsterGriess.Code.coord 0 j)
  have h1 := hu (MonsterGriess.Code.coord 1 j)
  have h2 := hu (MonsterGriess.Code.coord 2 j)
  have h3 := hu (MonsterGriess.Code.coord 3 j)
  simp only [liftXiColSum, Fin.sum_univ_four, Int.ModEq] at *
  omega

/-- Rational and integral formulas agree when the column sums are even. -/
theorem liftXiInt_cast (u : Fin 24 → ℤ)
    (he : ∀ j, liftXiColSum u j % 2 = 0) :
    (fun i => (liftXiInt u i : ℚ)) = liftXiRat (fun i => (u i : ℚ)) := by
  ext i
  have hh (j : Fin 6) : ((liftXiColSum u j / 2 : ℤ) : ℚ) =
      (∑ r : Fin 4, (u (MonsterGriess.Code.coord r j) : ℚ)) / 2 := by
    have hz : 2 * (liftXiColSum u j / 2) = liftXiColSum u j := by
      have := he j
      omega
    have hq := congrArg (fun n : ℤ => (n : ℚ)) hz
    simp only [Int.cast_mul, Int.cast_ofNat, liftXiColSum, Int.cast_sum] at hq
    dsimp only [liftXiColSum]
    linarith
  simp only [liftXiInt, liftXiRat, LinearMap.coe_mk, AddHom.coe_mk, liftXiBlock,
    MonsterGriess.Code.coord_row_col]
  split_ifs <;> push_cast <;> rw [hh]

/-- The transformed column sum is minus twice its former top entry. -/
theorem liftXiInt_colSum (u : Fin 24 → ℤ) (j : Fin 6)
    (he : liftXiColSum u j % 2 = 0) :
    liftXiColSum (liftXiInt u) j = -2 * u (MonsterGriess.Code.coord 0 j) := by
  simp only [liftXiColSum, Fin.sum_univ_four, liftXiInt_coord]
  norm_num
  simp only [liftXiColSum, Fin.sum_univ_four] at he
  omega

/-- The lower-row pair sums give the original hexacode projection. -/
theorem liftXiHex_pair (a b da db h m n : ℤ)
    (ha : a % 4 = (m + 2 * da) % 4) (hb : b % 4 = (m + 2 * db) % 4)
    (he : (m - h - n) % 2 = 0) :
    (((a - h - n) / 2 + (b - h - n) / 2 : ℤ) : ZMod 2) =
      ((da + db : ℤ) : ZMod 2) := by
  apply (ZMod.intCast_eq_intCast_iff' _ _ 2).mpr
  omega

/-- Conway's signed tetrad transformation preserves the integral Leech lattice. -/
theorem liftXiInt_mem {u : Fin 24 → ℤ} (hu : u ∈ codeLattice MonsterGriess.Code.C) :
    liftXiInt u ∈ codeLattice MonsterGriess.Code.C := by
  obtain ⟨m, _, d, hd, hud, hus⟩ := hu
  let t : ℤ := ∑ j : Fin 6, bitLift (d (MonsterGriess.Code.coord 0 j))
  let n : ℤ := (m + t) % 2
  let v := liftXiInt u
  let y : Fin 24 → ℤ := fun i => (v i - n) / 2
  have hn : n = 0 ∨ n = 1 := by dsimp [n]; omega
  have he (j) := (liftXiCol_parity hd hud j).1
  have hp (j) : (liftXiColSum u j / 2) % 2 = t % 2 :=
    (liftXiCol_parity hd hud j).2
  have hv (i) : v i % 2 = n := by
    have hi := hud i
    have hh := hp (MonsterGriess.Code.col i)
    simp only [Int.ModEq] at hi
    dsimp [v, liftXiInt, n]
    split_ifs <;> omega
  have hy (i) : 2 * y i = v i - n := by
    have := hv i
    dsimp [y]
    omega
  have ht : (∑ j : Fin 6, u (MonsterGriess.Code.coord 0 j)) % 4 =
      (6 * m + 2 * t) % 4 := by
    let k : Fin 6 → ℤ := fun j =>
      (u (MonsterGriess.Code.coord 0 j) - m -
        2 * bitLift (d (MonsterGriess.Code.coord 0 j))) / 4
    have hk (j) : u (MonsterGriess.Code.coord 0 j) =
        m + 2 * bitLift (d (MonsterGriess.Code.coord 0 j)) + 4 * k j := by
      have := hud (MonsterGriess.Code.coord 0 j)
      dsimp [k]
      simp only [Int.ModEq] at this
      omega
    have hs : (∑ j : Fin 6, u (MonsterGriess.Code.coord 0 j)) =
        6 * m + 2 * t + 4 * ∑ j, k j := by
      simp only [hk, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, t]
    omega
  have hys (j) : (∑ r : Fin 4, y (MonsterGriess.Code.coord r j)) =
      -u (MonsterGriess.Code.coord 0 j) - 2 * n := by
    have hs := liftXiInt_colSum u j (he j)
    have hh : 2 * (∑ r : Fin 4, y (MonsterGriess.Code.coord r j)) =
        liftXiColSum v j - 4 * n := by
      simp only [Finset.mul_sum, hy, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, liftXiColSum]
    change liftXiColSum v j = _ at hs
    omega
  have htop : 4 * (∑ j : Fin 6, y (MonsterGriess.Code.coord 0 j)) =
      (∑ i, u i) - 2 * (∑ j : Fin 6, u (MonsterGriess.Code.coord 0 j)) - 12 * n := by
    have hh (j) : 4 * y (MonsterGriess.Code.coord 0 j) =
        liftXiColSum u j - 2 * u (MonsterGriess.Code.coord 0 j) - 2 * n := by
      have hj := hy (MonsterGriess.Code.coord 0 j)
      have hje := he j
      simp only [v, liftXiInt_coord, if_true] at hj
      omega
    rw [Finset.mul_sum]
    simp only [hh, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, liftXiSum_coords, liftXiColSum]
    ring
  have htopParity : (∑ j : Fin 6, y (MonsterGriess.Code.coord 0 j)) % 2 = m % 2 := by
    simp only [Int.ModEq] at hus
    dsimp only [n] at htop
    omega
  have hycode : (fun i => (y i : ZMod 2)) ∈ MonsterGriess.Code.C := by
    constructor
    · have hh : MonsterGriess.Code.hexProj (fun i => (y i : ZMod 2)) =
          MonsterGriess.Code.hexProj d := by
        funext j
        rw [MonsterGriess.Code.hexProj_apply, MonsterGriess.Code.hexProj_apply]
        apply MonsterGriess.Code.F4.ext'
        all_goals
          rw [← Int.cast_add]
          have hpj : (m - liftXiColSum u j / 2 - n) % 2 = 0 := by
            have := hp j
            dsimp [n]
            omega
        · have hh := liftXiHex_pair _ _ _ _ _ _ _ (hud (MonsterGriess.Code.coord 1 j))
            (hud (MonsterGriess.Code.coord 3 j)) hpj
          simpa only [y, v, liftXiInt_coord, show (1 : Fin 4) ≠ 0 by decide,
            show (3 : Fin 4) ≠ 0 by decide, if_false, Int.cast_add,
            MonsterGriess.Code.bitLift_cast] using hh
        · have hh := liftXiHex_pair _ _ _ _ _ _ _ (hud (MonsterGriess.Code.coord 2 j))
            (hud (MonsterGriess.Code.coord 3 j)) hpj
          simpa only [y, v, liftXiInt_coord, show (2 : Fin 4) ≠ 0 by decide,
            show (3 : Fin 4) ≠ 0 by decide, if_false, Int.cast_add,
            MonsterGriess.Code.bitLift_cast] using hh
      rw [hh]
      exact hd.1
    · intro j
      change (∑ r : Fin 4, (y (MonsterGriess.Code.coord r j) : ZMod 2)) =
        ∑ k : Fin 6, (y (MonsterGriess.Code.coord 0 k) : ZMod 2)
      rw [← Int.cast_sum, ← Int.cast_sum]
      apply (ZMod.intCast_eq_intCast_iff' _ _ 2).mpr
      norm_num only [Nat.cast_ofNat]
      rw [hys, htopParity]
      have := hud (MonsterGriess.Code.coord 0 j)
      simp only [Int.ModEq] at this
      omega
  refine ⟨n, hn, _, hycode, fun i => ?_, ?_⟩
  · have hi := hy i
    rw [SpinLattice.bitLift_intCast]
    change v i ≡ n + 2 * (y i % 2) [ZMOD 4]
    unfold Int.ModEq
    omega
  · have hs : (∑ i, v i) = -2 * ∑ j : Fin 6, u (MonsterGriess.Code.coord 0 j) := by
      rw [liftXiSum_coords, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact liftXiInt_colSum u j (he j)
    change (∑ i, v i) ≡ 4 * n [ZMOD 8]
    rw [hs]
    unfold Int.ModEq
    dsimp [n]
    omega

/-- Agreement with the rational matrix on every lattice vector. -/
theorem liftXiInt_cast_mem {u : Fin 24 → ℤ} (hu : u ∈ codeLattice MonsterGriess.Code.C) :
    (fun i => (liftXiInt u i : ℚ)) = liftXiRat (fun i => (u i : ℚ)) := by
  obtain ⟨m, _, d, hd, hud, _⟩ := hu
  exact liftXiInt_cast u fun j => (liftXiCol_parity hd hud j).1

theorem liftXiInt_cube {u : Fin 24 → ℤ} (hu : u ∈ codeLattice MonsterGriess.Code.C) :
    liftXiInt (liftXiInt (liftXiInt u)) = u := by
  have h : (fun i => (liftXiInt (liftXiInt (liftXiInt u)) i : ℚ)) =
      fun i => (u i : ℚ) := by
    rw [liftXiInt_cast_mem (liftXiInt_mem (liftXiInt_mem hu)),
      liftXiInt_cast_mem (liftXiInt_mem hu), liftXiInt_cast_mem hu, liftXiRat_cube]
  ext i
  exact_mod_cast congrFun h i

theorem liftXiInt_add {u v : Fin 24 → ℤ}
    (hu : u ∈ codeLattice MonsterGriess.Code.C)
    (hv : v ∈ codeLattice MonsterGriess.Code.C) :
    liftXiInt (u + v) = liftXiInt u + liftXiInt v := by
  have h := liftXiInt_cast_mem (add_mem_codeLattice MonsterGriess.Code.allOnes_mem_C hu hv)
  have hs : (fun i => ((u + v) i : ℚ)) =
      (fun i => (u i : ℚ)) + (fun i => (v i : ℚ)) := by ext i; simp
  rw [hs, map_add, ← liftXiInt_cast_mem hu, ← liftXiInt_cast_mem hv] at h
  ext i
  have hi := congrFun h i
  simp only [Pi.add_apply] at hi ⊢
  exact_mod_cast hi

/-- The order-three additive equivalence of the Conway code lattice. -/
def liftXiCodeEquiv : codeLatticeSubgroup MonsterGriess.Code.allOnes_mem_C ≃+
    codeLatticeSubgroup MonsterGriess.Code.allOnes_mem_C where
  toFun u := ⟨liftXiInt u.val, liftXiInt_mem u.property⟩
  invFun u := ⟨liftXiInt (liftXiInt u.val), liftXiInt_mem (liftXiInt_mem u.property)⟩
  left_inv u := Subtype.ext (liftXiInt_cube u.property)
  right_inv u := Subtype.ext (liftXiInt_cube u.property)
  map_add' u v := Subtype.ext (liftXiInt_add u.property v.property)

/-- Conway's nonmonomial generator as an integral linear Leech isometry. -/
def liftXi : leech.carrier →ₗ[ℤ] leech.carrier :=
  ((leechEquiv.trans liftXiCodeEquiv).trans leechEquiv.symm).toAddMonoidHom.toIntLinearMap

theorem liftXi_coordinates (α : leech.carrier) :
    (leechEquiv (liftXi α) : Fin 24 → ℤ) = liftXiInt (leechEquiv α) := by
  exact congrArg Subtype.val (leechEquiv.apply_symm_apply _)

theorem liftXi_surjective : Function.Surjective liftXi :=
  ((leechEquiv.trans liftXiCodeEquiv).trans leechEquiv.symm).surjective

theorem liftXi_cube (α : leech.carrier) : liftXi (liftXi (liftXi α)) = α := by
  apply leechEquiv.injective
  apply Subtype.ext
  simp only [liftXi_coordinates]
  exact liftXiInt_cube (leechEquiv α).property

theorem liftXi_isometry (α β : leech.carrier) :
    leech.form (liftXi α) (liftXi β) = leech.form α β := by
  have h := liftXiRat_dot (fun i => ((leechEquiv α : Fin 24 → ℤ) i : ℚ))
    (fun i => ((leechEquiv β : Fin 24 → ℤ) i : ℚ))
  rw [← liftXiInt_cast_mem (leechEquiv α).property,
    ← liftXiInt_cast_mem (leechEquiv β).property] at h
  have hz : liftXiInt (leechEquiv α) ⬝ᵥ liftXiInt (leechEquiv β) =
      (leechEquiv α : Fin 24 → ℤ) ⬝ᵥ (leechEquiv β : Fin 24 → ℤ) := by
    simp only [dotProduct] at h ⊢
    exact_mod_cast h
  rw [← liftXi_coordinates, ← liftXi_coordinates, leechEquiv_dotProduct,
    leechEquiv_dotProduct] at hz
  omega

/-- The rational 24 by 24 coordinate matrix of the nonmonomial generator. -/
def liftXiMatrix : Matrix (Fin 24) (Fin 24) ℚ := LinearMap.toMatrix' liftXiRat

theorem liftXiMatrix_mulVec (u : Fin 24 → ℚ) : liftXiMatrix *ᵥ u = liftXiRat u :=
  LinearMap.toMatrix'_mulVec liftXiRat u

theorem liftXiMatrix_coordinates (α : leech.carrier) :
    (fun i => ((leechEquiv (liftXi α) : Fin 24 → ℤ) i : ℚ)) =
      liftXiMatrix *ᵥ (fun i => ((leechEquiv α : Fin 24 → ℤ) i : ℚ)) := by
  rw [liftXi_coordinates, liftXiMatrix_mulVec]
  exact liftXiInt_cast_mem (leechEquiv α).property

theorem liftXiMatrix_orthogonal : liftXiMatrixᵀ * liftXiMatrix = 1 := by
  ext i j
  change liftXiRat (Pi.single i 1) ⬝ᵥ liftXiRat (Pi.single j 1) = (1 : Matrix _ _ ℚ) i j
  rw [liftXiRat_dot]
  simp [dotProduct_single, Pi.single_apply, Matrix.one_apply, eq_comm]

/-- Two nonzero entries in the first row witness the nonmonomial coordinate action. -/
theorem liftXiMatrix_nonmonomial :
    liftXiMatrix 0 0 = -1 / 2 ∧ liftXiMatrix 0 1 = 1 / 2 := by
  norm_num [liftXiMatrix, LinearMap.toMatrix'_apply, liftXiRat, liftXiBlock,
    Fin.sum_univ_four, MonsterGriess.Code.row, MonsterGriess.Code.col,
    MonsterGriess.Code.coord, Pi.single_apply]

/-- The normalized spin action of the specific lattice generator. -/
def liftXiCharge : (SpinIdx → ℂ) ≃ₗ[ℂ] (SpinIdx → ℂ) :=
  liftSpinCharge liftXi liftXi_isometry

theorem liftXiCharge_dot (v w : SpinRep) : liftXiCharge v ⬝ᵥ liftXiCharge w = v ⬝ᵥ w :=
  liftLiftableChargeDot liftXi liftXi_isometry v w

theorem liftXiCharge_intertwine (α : leech.carrier) (v : SpinRep) :
    liftXiCharge ((liftMonoQmat α).map (Rat.castHom ℂ) *ᵥ v) =
      (liftMonoWeight liftXi α : ℂ) •
        ((liftMonoQmat (liftXi α)).map (Rat.castHom ℂ) *ᵥ liftXiCharge v) :=
  liftSpinCharge_intertwine liftXi liftXi_isometry α v

theorem liftXiCharge_smul (z : ℂ) (v : SpinIdx → ℂ) :
    liftXiCharge (z • v) = z • (liftXiCharge v : SpinIdx → ℂ) :=
  liftXiCharge.map_smul z (v : SpinRep)

/-- Cubing the charge action leaves every lattice class fixed, up to rational signs. -/
theorem liftXiCharge_cube_intertwine (α : leech.carrier) (v : SpinRep) :
    liftXiCharge (liftXiCharge (liftXiCharge
      ((liftMonoQmat α).map (Rat.castHom ℂ) *ᵥ v))) =
      ((liftMonoWeight liftXi α * liftMonoWeight liftXi (liftXi α) *
        liftMonoWeight liftXi (liftXi (liftXi α)) : ℚ) : ℂ) •
      ((liftMonoQmat α).map (Rat.castHom ℂ) *ᵥ
        liftXiCharge (liftXiCharge (liftXiCharge v))) := by
  simp only [liftXiCharge_intertwine, liftXiCharge_smul, smul_smul, liftXi_cube,
    Rat.cast_mul]

/-- The cube of the normalized charge operator is a rational signed permutation. -/
theorem liftXiCharge_cube_signed :
    ∃ (σ : Equiv.Perm SpinIdx) (ε : SpinIdx → ZMod 2), ∀ v : SpinRep,
      liftXiCharge (liftXiCharge (liftXiCharge v)) =
        (liftGenSignedMatrix σ ε).map (Rat.castHom ℂ) *ᵥ v := by
  let E := (liftXiCharge.trans liftXiCharge).trans liftXiCharge
  let w (t : liftSpinTest) : ℚ :=
    liftMonoWeight liftXi (liftSpinTestVector t) *
      liftMonoWeight liftXi (liftXi (liftSpinTestVector t)) *
      liftMonoWeight liftXi (liftXi (liftXi (liftSpinTestVector t)))
  apply liftSpinRational_of_diagonal E
    (fun v u => by
      change liftXiCharge (liftXiCharge (liftXiCharge v)) ⬝ᵥ
        liftXiCharge (liftXiCharge (liftXiCharge u)) = _
      rw [liftXiCharge_dot, liftXiCharge_dot, liftXiCharge_dot])
    liftSpinTestValue (fun t i => (w t : ℂ) * liftSpinTestValue t i) _
    liftSpinTest_separates
  intro t v
  have h := liftXiCharge_cube_intertwine (liftSpinTestVector t) v
  rw [liftSpinTest_diagonal] at h
  refine h.trans ?_
  dsimp only [E, LinearEquiv.trans_apply]
  funext i
  simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, w]
  push_cast
  ring

/-- Apply a rational linear functional entrywise to a complex matrix intertwiner. -/
theorem liftXiDual_intertwine (f : ℂ →ₗ[ℚ] ℚ) (M : Matrix SpinIdx SpinIdx ℂ)
    (A B : Matrix SpinIdx SpinIdx ℚ) (w : ℚ)
    (h : M * A.map (Rat.castHom ℂ) = (w : ℂ) • (B.map (Rat.castHom ℂ) * M)) :
    M.map f * A = w • (B * M.map f) := by
  have hf (a : ℚ) (z : ℂ) : f ((a : ℂ) * z) = a * f z := f.map_smul a z
  ext i j
  have hij := congrArg f (congrArg (fun N : Matrix SpinIdx SpinIdx ℂ => N i j) h)
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    Rat.coe_castHom, map_sum, hf] at hij ⊢
  convert hij using 1
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm (M i k), hf, mul_comm]

/-- Rational unphased intertwining gives the phased equation for any endomorphism. -/
theorem liftXiUnphased_to_phased (T : Matrix SpinIdx SpinIdx ℚ)
    (hT : ∀ α : leech.carrier, T * liftMonoQmat α =
      liftMonoWeight liftXi α • (liftMonoQmat (liftXi α) * T))
    (α : leech.carrier) (v : SpinRep) :
    T.map (Rat.castHom ℂ) *ᵥ (spinOp (coordOfRed (red leech α)) *ᵥ v) =
      latCob leech leech liftXi α •
        (spinOp (coordOfRed (red leech (liftXi α))) *ᵥ
          (T.map (Rat.castHom ℂ) *ᵥ v)) := by
  have h := congrArg (fun N => N.map (Rat.castHom ℂ)) (hT α)
  have hm (w : ℚ) (N : Matrix SpinIdx SpinIdx ℚ) :
      (w • N).map (Rat.castHom ℂ) = (w : ℂ) • N.map (Rat.castHom ℂ) := by
    ext i j
    simp
  dsimp only at h
  rw [Matrix.map_mul (f := Rat.castHom ℂ), hm,
    Matrix.map_mul (f := Rat.castHom ℂ), liftMonoQmat_map, liftMonoQmat_map] at h
  rw [spinOp, spinOp, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.smul_mulVec,
    smul_smul, Matrix.mulVec_mulVec, h, Matrix.smul_mulVec, smul_smul,
    mul_comm (signRefinement _), liftMonoWeight_phase liftXi liftXi_isometry,
    Matrix.mulVec_mulVec]

/-- The normalized spin action is projectively defined over the rationals. -/
theorem liftXiCharge_projective :
    ∃ (T : Matrix SpinIdx SpinIdx ℚ) (z : ℂ), z ≠ 0 ∧
      ∀ v : SpinIdx → ℂ, T.map (Rat.castHom ℂ) *ᵥ v = z • liftXiCharge v := by
  classical
  let M := LinearMap.toMatrix' liftXiCharge.toLinearMap
  have hM (v : SpinIdx → ℂ) : M *ᵥ v = liftXiCharge v :=
    LinearMap.toMatrix'_mulVec _ v
  have hne : ∃ i, M i spinIdxBase ≠ 0 := by
    by_contra! h
    have hz : liftXiCharge (Pi.single spinIdxBase 1) = 0 := funext h
    have hz' := liftXiCharge.injective (hz.trans liftXiCharge.map_zero.symm)
    have := congrFun hz' spinIdxBase
    simp at this
  obtain ⟨i₀, hi₀⟩ := hne
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℚ hi₀
  let T : Matrix SpinIdx SpinIdx ℚ := M.map f
  have ht (α : leech.carrier) : T * liftMonoQmat α =
      liftMonoWeight liftXi α • (liftMonoQmat (liftXi α) * T) := by
    apply liftXiDual_intertwine
    ext i j
    have h := congrFun (liftXiCharge_intertwine α (Pi.single j 1)) i
    rw [← hM, ← hM] at h
    simpa only [Matrix.mulVec_mulVec, Matrix.mulVec_single_one,
      Matrix.smul_apply, Pi.smul_apply, smul_eq_mul] using h
  have htc (α : leech.carrier) (v : SpinIdx → ℂ) :
      T.map (Rat.castHom ℂ) *ᵥ ((liftMonoQmat α).map (Rat.castHom ℂ) *ᵥ v) =
        (liftMonoWeight liftXi α : ℂ) •
          ((liftMonoQmat (liftXi α)).map (Rat.castHom ℂ) *ᵥ
            (T.map (Rat.castHom ℂ) *ᵥ v)) := by
    have h := congrArg (fun N : Matrix SpinIdx SpinIdx ℚ =>
      N.map (Rat.castHom ℂ)) (ht α)
    have hm (w : ℚ) (N : Matrix SpinIdx SpinIdx ℚ) :
        (w • N).map (Rat.castHom ℂ) = (w : ℂ) • N.map (Rat.castHom ℂ) := by
      ext i j
      simp
    dsimp only at h
    rw [Matrix.map_mul (f := Rat.castHom ℂ), hm,
      Matrix.map_mul (f := Rat.castHom ℂ)] at h
    rw [Matrix.mulVec_mulVec, h, Matrix.smul_mulVec, Matrix.mulVec_mulVec]
  let F : Module.End ℂ (SpinIdx → ℂ) :=
    liftXiCharge.symm.toLinearMap.comp (Matrix.mulVecLin (T.map (Rat.castHom ℂ)))
  have hef (v : SpinIdx → ℂ) : liftXiCharge (F v) = T.map (Rat.castHom ℂ) *ᵥ v := by
    dsimp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply]
    exact liftXiCharge.apply_symm_apply _
  have hcomm (α : leech.carrier) (v : SpinIdx → ℂ) :
      F ((liftMonoQmat α).map (Rat.castHom ℂ) *ᵥ v) =
        (liftMonoQmat α).map (Rat.castHom ℂ) *ᵥ F v := by
    apply liftXiCharge.injective
    rw [hef, htc, liftXiCharge_intertwine, hef]
  obtain ⟨z, hz⟩ := liftLiftableSpinCommuteScalar F (fun α v => by
    rw [spinOp, Matrix.smul_mulVec, map_smul, ← liftMonoQmat_map, hcomm,
      Matrix.smul_mulVec])
  have hspec (v : SpinIdx → ℂ) :
      T.map (Rat.castHom ℂ) *ᵥ v = z • liftXiCharge v := by
    rw [← hef, hz]
    exact liftXiCharge_smul z v
  refine ⟨T, z, ?_, hspec⟩
  intro hzero
  have hh := congrFun (hspec (Pi.single spinIdxBase 1)) i₀
  rw [hzero, zero_smul, Matrix.mulVec_single_one] at hh
  change ((f (M i₀ spinIdxBase) : ℚ) : ℂ) = 0 at hh
  rw [hf, Rat.cast_one] at hh
  exact one_ne_zero hh

/-- Orthogonality and the rational cube remove the projective scalar obstruction. -/
theorem liftXiCharge_rational :
    ∃ R : Matrix SpinIdx SpinIdx ℚ, ∀ v : SpinIdx → ℂ,
      liftXiCharge v = R.map (Rat.castHom ℂ) *ᵥ v := by
  obtain ⟨T, z, hz, hT⟩ := liftXiCharge_projective
  let e : SpinIdx → ℂ := Pi.single spinIdxBase 1
  let q₂ : ℚ := ∑ i, T i spinIdxBase * T i spinIdxBase
  have hq₂ : (q₂ : ℂ) = z ^ 2 := by
    have hh : (T.map (Rat.castHom ℂ) *ᵥ e) ⬝ᵥ (T.map (Rat.castHom ℂ) *ᵥ e) =
        z ^ 2 := by
      rw [hT, smul_dotProduct, dotProduct_smul, liftXiCharge_dot]
      simp [e, pow_two]
    simpa only [e, Matrix.mulVec_single_one, dotProduct, Matrix.map_apply,
      Rat.coe_castHom, q₂, Rat.cast_sum, Rat.cast_mul] using hh
  have hpow (v : SpinIdx → ℂ) :
      (T * T * T).map (Rat.castHom ℂ) *ᵥ v =
        z ^ 3 • liftXiCharge (liftXiCharge (liftXiCharge v)) := by
    simp only [Matrix.map_mul (f := Rat.castHom ℂ), ← Matrix.mulVec_mulVec,
      hT, liftXiCharge_smul, smul_smul]
    congr 1
    ring
  obtain ⟨σ, ε, hcube⟩ := liftXiCharge_cube_signed
  let q₃ : ℚ := (T * T * T) spinIdxBase (σ spinIdxBase) * sgnR ℚ (ε spinIdxBase)
  have hq₃ : (q₃ : ℂ) = z ^ 3 := by
    have hh := congrFun (hpow (Pi.single (σ spinIdxBase) 1)) spinIdxBase
    rw [hcube] at hh
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.map_apply, Rat.coe_castHom,
      Pi.smul_apply, smul_eq_mul, liftGenSignedMatrix, spm_apply, if_true] at hh
    dsimp only [q₃]
    rw [Rat.cast_mul, hh, mul_assoc]
    have hs := sgnR_mul_self (R := ℚ) (ε spinIdxBase)
    have hsc : (sgnR ℚ (ε spinIdxBase) : ℂ) * (sgnR ℚ (ε spinIdxBase) : ℂ) = 1 := by
      exact_mod_cast hs
    rw [hsc, mul_one]
  let c : ℚ := q₃ / q₂
  have hc : (c : ℂ) = z := by
    dsimp only [c]
    rw [Rat.cast_div, hq₂, hq₃]
    field_simp
  have hcne : c ≠ 0 := by
    intro hzero
    rw [hzero, Rat.cast_zero] at hc
    exact hz hc.symm
  refine ⟨c⁻¹ • T, fun v => ?_⟩
  have hm : (c⁻¹ • T).map (Rat.castHom ℂ) = (c : ℂ)⁻¹ • T.map (Rat.castHom ℂ) := by
    ext i j
    simp
  rw [hm, Matrix.smul_mulVec, hT, ← hc, smul_smul, inv_mul_cancel₀]
  · rw [one_smul]
  · exact_mod_cast hcne

/-- A rational spin matrix for the chosen normalized VOA lift of Conway's generator. -/
def liftXiSpinMatrix : Matrix SpinIdx SpinIdx ℚ := liftXiCharge_rational.choose

theorem liftXiSpinMatrix_spec (v : SpinIdx → ℂ) :
    liftXiCharge v = liftXiSpinMatrix.map (Rat.castHom ℂ) *ᵥ v :=
  liftXiCharge_rational.choose_spec v

theorem liftXiSpinMatrix_orthogonal : liftXiSpinMatrixᵀ * liftXiSpinMatrix = 1 := by
  ext i j
  have h := liftXiCharge_dot (Pi.single i 1) (Pi.single j 1)
  have he : (Pi.single i (1 : ℂ)) ⬝ᵥ Pi.single j 1 = if i = j then 1 else 0 := by
    simp [dotProduct_single, Pi.single_apply, eq_comm]
  rw [he, liftXiSpinMatrix_spec, liftXiSpinMatrix_spec] at h
  simp only [Matrix.mulVec_single_one, dotProduct, Matrix.col_apply,
    Matrix.map_apply, Rat.coe_castHom] at h
  change (∑ k, liftXiSpinMatrix k i * liftXiSpinMatrix k j) =
    (if i = j then (1 : ℚ) else 0)
  apply Rat.cast_injective (α := ℂ)
  push_cast
  simpa only [apply_ite, Rat.cast_one, Rat.cast_zero] using h

theorem liftXiSpinMatrix_intertwine (α : leech.carrier) :
    liftXiSpinMatrix * liftMonoQmat α =
      liftMonoWeight liftXi α • (liftMonoQmat (liftXi α) * liftXiSpinMatrix) := by
  have hm (w : ℚ) (N : Matrix SpinIdx SpinIdx ℚ) :
      (w • N).map (Rat.castHom ℂ) = (w : ℂ) • N.map (Rat.castHom ℂ) := by
    ext i j
    simp
  suffices h : (liftXiSpinMatrix * liftMonoQmat α).map (Rat.castHom ℂ) =
      (liftMonoWeight liftXi α • (liftMonoQmat (liftXi α) * liftXiSpinMatrix)).map
        (Rat.castHom ℂ) from Matrix.map_injective (Rat.cast_injective (α := ℂ)) h
  rw [Matrix.map_mul (f := Rat.castHom ℂ), hm, Matrix.map_mul (f := Rat.castHom ℂ)]
  ext i j
  have h := congrFun (liftXiCharge_intertwine α (Pi.single j 1)) i
  rw [liftXiSpinMatrix_spec, liftXiSpinMatrix_spec] at h
  simpa only [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Pi.smul_apply,
    Matrix.smul_apply, smul_eq_mul] using h

/-- The nonmonomial Conway generator has a lift in the rational Monster framework. -/
theorem liftXi_liftable : ∃ g : liftableSubgroup,
    monsterLift g = liftTwVnatAut liftXi liftXi_isometry liftXi_surjective := by
  exact liftMonoOfUnphasedIntertwiner liftXi liftXi_isometry liftXi_surjective
    liftXiSpinMatrix liftXiSpinMatrix_orthogonal liftXiSpinMatrix_intertwine

end VOA.Moonshine.ConwayNorton.M8
