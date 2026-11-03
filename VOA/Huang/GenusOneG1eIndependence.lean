import VOA.Huang.GenusOneG1eConjugation
import VOA.Huang.GenusOneG1eUnique

/-!
# (N4) `ChannelIndependence` from an algebraic trace-separation statement

Step (5i) of the proof of (G1), the reduction of Huang's Prop. 2.11.

Every generator of `Rspan` (an `(a,b)`- or `(b,a)`-orthogonal channel) and every vacuum channel
has a proved absolutely convergent expansion `Σ_s A_s(τ) u^{γ + s}` (`sum_laurent`, any inner
module), with `γ = h_k − κ − N₀` and `A_s` a one-point function of the explicit formal bracket
mode `bracketModes Y_in n_s (Σ w_a) (Σ w_b)`, `n_s = κ − 1 − h_k − (s − N₀)`. A relation
`Σ_z coef_z vacF_z ∈ Rspan` holds on a nonempty open sector, so by the proved uniqueness theorem
`gen_series_unique` the coefficient of every power `u^{−κ−N₀+s}` vanishes. Only channels whose
inner conformal weight is an INTEGER contribute to the vacuum powers (other classes mod `ℤ`
separate — this is not fixed-`τ` exponent separation among channels of the same class, which
fails at `c = 1`), and they contribute at the SAME bracket-mode index `n` as the vacuum channel.
What is left is the purely algebraic, trace-level statement

* `TraceSeparation F hv c η'` (named, TRUE): if for all insertions, all `n ∈ κ − 1 + ℤ` and all
  `τ`, `Σ_z coef_z Z_z(Y^ε[w_a]_n w_b) = Σ_l λ_l T_l(n)` with `T_l` the traces of the bracket modes
  of finitely many orthogonal channels of INTEGRAL inner weight (`(b,a)` ones with `e^{iπκ}`),
  then `coef = 0`. *Why true (Huang 2008, Prop. 2.11):* the bracket modes of an orthogonal
  channel are `q(X_n)` for the universal bracket mode `X_n ∈ M_a ⊠ M_b` (and, through the
  bracket skew-symmetry `e^{uL[−1]}`, `q'(c(X_n))` up to `L[−1]`-images, which every one-point
  function kills, for the `(b,a)` ones — the `e^{iπκ}` cancels the skew phase); the universal
  bracket modes of finitely many insertions span `M_a ⊠ M_b` in each `L[0]`-weight, so one can
  reach `X = η'(v)` for any `v ∈ V_[k]`: every orthogonal term dies (`η' ≫ q = 0`,
  `η ≫ q' = 0`), the vacuum side becomes `Σ_z coef_z Z_z(v)`, and Zhu's trace independence
  (`traceIndependent_of_irredundant`, PBW) gives `coef = 0`.

* `channelIndependence_of_separation`, `channelIndependenceInput_of_separation`;
* `fusionEigenInput_of_algebraic : IntertwinerSubstitutionInput → TraceSkewInput →
  TraceSeparationInput → FusionEigenInput` — Huang's Theorem 5.2 from three ALGEBRAIC inputs,
  with every analytic step proved.
-/

noncomputable section

namespace VOA.Huang.GenusOneG1e

open VOA VOA.Huang Complex VOA.Huang.GenusOneG1d VOA.Huang.VerlindeFusion
  VOA.Classification.COne VOA.Huang.ZhuModData VOA.Huang.TensorCat
  VOA.Huang.VerlindeTransport VOA.Huang.GenusOneG1c CategoryTheory
open VOA.Huang.GenusOne (sqL traceFunction)
open VOA.Huang.GenusOne.IntCoord (bracketModes vacuum_traceFunction_eq)
open VOA.Huang.GenusTwoPoint (vacuumLW)
open scoped BigOperators

universe u w

/-! ## §1 Elementary lemmas -/

theorem exp_mul_log_split {u : ℂ} (hu : u ≠ 0) (γ : ℂ) (s : ℕ) :
    exp ((γ + s) * log u) = exp (γ * log u) * u ^ s := by
  rw [add_mul, exp_add, Complex.exp_nat_mul, exp_log hu]

theorem tsum_ite_add_eq (a : ℕ → ℂ) (γ : ℂ) (s0 : ℕ) :
    ∑' s : ℕ, (if γ + s = γ + s0 then a s else 0) = a s0 := by
  have : ∀ s : ℕ, (if γ + s = γ + s0 then a s else 0) = if s = s0 then a s else 0 := by
    intro s
    by_cases h : s = s0
    · rw [if_pos (by rw [h]), if_pos h]
    · rw [if_neg (fun h' => h (by exact_mod_cast add_left_cancel h')), if_neg h]
  rw [tsum_congr this, tsum_ite_eq]

theorem tsum_ite_none (a : ℕ → ℂ) (γ μ : ℂ) (h : ∀ s : ℕ, γ + s ≠ μ) :
    ∑' s : ℕ, (if γ + s = μ then a s else 0) = 0 :=
  (tsum_congr fun s => if_neg (h s)).trans tsum_zero

theorem sector_isOpen (τ : UpperHalfPlane) (δ : ℝ) : IsOpen (sector τ δ) := by
  have o1 : IsOpen {u : ℂ | ‖u‖ < δ} := isOpen_lt continuous_norm continuous_const
  have o2 : IsOpen {u : ℂ | 0 < (exp u - 1).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_exp.sub continuous_const))
  have o3 : IsOpen {u : ℂ | 0 < (exp (-u / τ) - 1).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp
      ((continuous_exp.comp (continuous_neg.div_const _)).sub continuous_const))
  have : sector τ δ = {u : ℂ | ‖u‖ < δ} ∩ ({u : ℂ | 0 < (exp u - 1).re} ∩
      {u : ℂ | 0 < (exp (-u / τ) - 1).re}) := by
    ext u; simp [sector]
  rw [this]
  exact o1.inter (o2.inter o3)

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι]

/-! ## §2 Generators and the algebraic input -/

variable (F : FusionChoice W) {D : VOA.ModularData W ι} {a b : ι}

/-- The generators of `Rspan`, as a sum type. -/
abbrev Gen (η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b))
    (η : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D b) (famObj D a)) : Type _ :=
  ABChannel F D a b η' ⊕ BAChannel F D a b η

variable {F}

/-- The function of a generator. -/
def genFun {η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)}
    {η : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D b) (famObj D a)} :
    Gen F η' η → FunSpace D a b
  | .inl C => fun ins τ u => C.eval ins τ u
  | .inr B => fun ins τ u => exp ((Real.pi : ℂ) * I * ins.κ) * B.eval ins τ u

/-- The inner label of a generator. -/
def genK {η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)}
    {η : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D b) (famObj D a)} :
    Gen F η' η → ι
  | .inl C => C.k
  | .inr B => B.k

/-- The expansion coefficient of a generator at bracket-mode index `n`. -/
def genA {η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)}
    {η : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D b) (famObj D a)}
    (g : Gen F η' η) (ins : Insertion D a b) (n : ℂ) (τ : UpperHalfPlane) : ℂ :=
  match g with
  | .inl C => traceFunction C.Yout (D.h C.y)
      (bracketModes (P := lwOf D a) (Q := lwOf D b) (N := lwOf D C.k) C.inner n
        (∑ i, ins.wa i) (∑ j, ins.wb j)) τ
  | .inr B => exp ((Real.pi : ℂ) * I * ins.κ) * traceFunction B.Yout (D.h B.y)
      (bracketModes (P := lwOf D b) (Q := lwOf D a) (N := lwOf D B.k) B.inner n
        (∑ j, ins.wb j) (∑ i, ins.wa i)) τ

open Classical in
/-- The contribution of a generator to the vacuum powers: only INTEGRAL inner weights. -/
def genTerm {η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)}
    {η : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D b) (famObj D a)}
    (g : Gen F η' η) (ins : Insertion D a b) (n : ℂ) (τ : UpperHalfPlane) : ℂ :=
  if ∃ k : ℤ, D.h (genK g) = k then genA g ins n τ else 0

variable (F)

/-- **The algebraic trace-separation statement** (Huang 2008, Prop. 2.11, at trace level; TRUE —
see the module doc). -/
def TraceSeparation (hv : W.vacuum ≠ 0) (c : TransferChoice F D a b)
    (η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)) : Prop :=
  ∀ (coef : ι → ℂ) (r : ℕ) (lam : Fin r → ℂ) (G : Fin r → Gen F η' c.η),
    (∀ (ins : Insertion D a b) (n : ℂ) (τ : UpperHalfPlane), (∃ t : ℤ, n = ins.κ - 1 + t) →
      ∑ z, coef z * traceFun D.Mfam D.h z
          (bracketModes (P := lwOf D a) (Q := lwOf D b) (N := vacuumLW W hv) (epsInt F c) n
            (∑ i, ins.wa i) (∑ j, ins.wb j)) τ =
        ∑ l, lam l * genTerm (G l) ins n τ) →
    coef = 0

/-- `TraceSeparation` for every instance. -/
def TraceSeparationInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι),
      ZhuModularityAnalytic D → Irredundant D.Mfam → Complete D.Mfam →
      ∀ (F : FusionChoice W) (a b : ι) (c : TransferChoice F D a b) (hv : W.vacuum ≠ 0)
        (η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)),
        η' ≫ c.ε = 𝟙 _ → TraceSeparation F hv c η'

/-! ## §3 Expansions of the generators and of the vacuum channels -/

variable {F}

theorem genFun_mem {η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)}
    {η : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D b) (famObj D a)}
    (g : Gen F η' η) : genFun g ∈ nonVacGen η' η := by
  rcases g with C | B
  · exact Or.inl ⟨C, rfl⟩
  · exact Or.inr ⟨B, rfl⟩

/-- The expansion of a generator (aligned insertion). -/
theorem genExpansion (hV : StronglyRational W)
    {η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)}
    {η : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D b) (famObj D a)}
    (g : Gen F η' η) (ins : Insertion D a b) (N0 : ℕ)
    (hal : ∀ i j, ins.wa i ≠ 0 → ins.wb j ≠ 0 → ∃ Dn : ℕ, ins.κ - ins.αa i - ins.αb j + N0 = Dn)
    (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ → 0 < (exp u - 1).re →
      HasSum (fun s : ℕ => genA g ins (ins.κ - 1 - D.h (genK g) - ((s : ℂ) - N0)) τ *
          exp ((D.h (genK g) - ins.κ - N0 + s) * log u)) (genFun g ins τ u) := by
  rcases g with C | B
  · obtain ⟨δ, hδ, h⟩ := sum_laurent hV (lwOf_irreducible D a) (lwOf_irreducible D b)
      (lwOf_irreducible D C.y) (lwOf_irreducible D C.k) C.Yout C.inner ins.wa ins.αa ins.hwa
      ins.wb ins.αb ins.hwb ins.κ N0 hal τ
    refine ⟨δ, hδ, fun u hu hre => ?_⟩
    have hu0 : u ≠ 0 := fun h0 => by
      have := re_pos_of_exp_sub_one hre
      rw [h0, Complex.zero_re] at this
      exact lt_irrefl _ this
    have h' := h u hu hre
    rw [show (lwOf D C.k).h = D.h C.k from rfl, show (lwOf D C.y).h = D.h C.y from rfl] at h'
    refine h'.congr_fun fun s => ?_
    simp only [genA, genK]
    rw [exp_mul_log_split hu0]
    ring
  · have halr : ∀ j i, ins.wb j ≠ 0 → ins.wa i ≠ 0 →
        ∃ Dn : ℕ, ins.κ - ins.αb j - ins.αa i + N0 = Dn := by
      intro j i hj hi
      obtain ⟨Dn, h⟩ := hal i j hi hj
      exact ⟨Dn, by rw [← h]; ring⟩
    obtain ⟨δ, hδ, h⟩ := sum_laurent hV (lwOf_irreducible D b) (lwOf_irreducible D a)
      (lwOf_irreducible D B.y) (lwOf_irreducible D B.k) B.Yout B.inner ins.wb ins.αb ins.hwb
      ins.wa ins.αa ins.hwa ins.κ N0 halr τ
    refine ⟨δ, hδ, fun u hu hre => ?_⟩
    have hu0 : u ≠ 0 := fun h0 => by
      have := re_pos_of_exp_sub_one hre
      rw [h0, Complex.zero_re] at this
      exact lt_irrefl _ this
    have h' := h u hu hre
    rw [show (lwOf D B.k).h = D.h B.k from rfl, show (lwOf D B.y).h = D.h B.y from rfl] at h'
    have h2 := h'.mul_left (exp ((Real.pi : ℂ) * I * ins.κ))
    have he : genFun (.inr B : Gen F η' η) ins τ u = exp ((Real.pi : ℂ) * I * ins.κ) *
        ∑ j, ∑ i, exp (ins.αb j * u) * iterF B.Yout B.inner (ins.wb j) (ins.wa i) (ins.αb j)
          (ins.αa i) τ (exp u - 1) := by
      simp only [genFun, BAChannel.eval]
      rw [Finset.sum_comm]
    rw [he]
    refine h2.congr_fun fun s => ?_
    simp only [genA, genK]
    rw [exp_mul_log_split hu0]
    ring

/-- The expansion of a vacuum channel (aligned insertion). -/
theorem vacExpansion (hV : StronglyRational W) (hv : W.vacuum ≠ 0) (c : TransferChoice F D a b)
    (ins : Insertion D a b) (N0 : ℕ)
    (hal : ∀ i j, ins.wa i ≠ 0 → ins.wb j ≠ 0 → ∃ Dn : ℕ, ins.κ - ins.αa i - ins.αb j + N0 = Dn)
    (τ : UpperHalfPlane) (z : ι) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ → 0 < (exp u - 1).re →
      HasSum (fun s : ℕ => traceFun D.Mfam D.h z
          (bracketModes (P := lwOf D a) (Q := lwOf D b) (N := vacuumLW W hv) (epsInt F c)
            (ins.κ - 1 - 0 - ((s : ℂ) - N0)) (∑ i, ins.wa i) (∑ j, ins.wb j)) τ *
          exp ((0 - ins.κ - N0 + s) * log u)) (vacF F hv c ins z τ u) := by
  have iQ : (vacuumLW W hv).IsIrreducibleLW :=
    (isSimple_iff_adjointModule_isIrreducible W).mp hV.simple
  obtain ⟨δ, hδ, h⟩ := sum_laurent hV (lwOf_irreducible D a) (lwOf_irreducible D b)
    (lwOf_irreducible D z) iQ (moduleIntertwiner (lwOf D z).isMod) (epsInt F c) ins.wa ins.αa
    ins.hwa ins.wb ins.αb ins.hwb ins.κ N0 hal τ
  refine ⟨δ, hδ, fun u hu hre => ?_⟩
  have hu0 : u ≠ 0 := fun h0 => by
    have := re_pos_of_exp_sub_one hre
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl _ this
  have h' := h u hu hre
  rw [show (vacuumLW W hv).h = 0 from rfl] at h'
  refine h'.congr_fun fun s => ?_
  rw [exp_mul_log_split hu0]
  erw [vacuum_traceFunction_eq D z]
  ring

/-! ## §4 The reduction -/

/-- **(N4) for one instance from `TraceSeparation`.** -/
theorem channelIndependence_of_separation (hV : StronglyRational W) (hv : W.vacuum ≠ 0)
    (c : TransferChoice F D a b)
    (η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b))
    (hsep : TraceSeparation F hv c η') : ChannelIndependence F hv c η' := by
  classical
  intro coef hmem
  obtain ⟨y, hy, g0, hg0, hyg⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨r, lam, gs, hgs⟩ := Submodule.mem_span_set'.mp hy
  have hkind : ∀ l, ∃ G : Gen F η' c.η, genFun G = (gs l : FunSpace D a b) := by
    intro l
    rcases (gs l).2 with ⟨C, hC⟩ | ⟨B, hB⟩
    · exact ⟨.inl C, hC⟩
    · exact ⟨.inr B, hB⟩
  choose G hG using hkind
  refine hsep coef r lam G fun ins n τ hnt => ?_
  obtain ⟨t, ht⟩ := hnt
  have hrel : ∀ u, (∑ z, coef z * vacF F hv c ins z τ u) =
      ∑ l, lam l * genFun (G l) ins τ u + g0 ins τ u := by
    intro u
    have h1 := congrFun (congrFun (congrFun hyg ins) τ) u
    rw [← hgs] at h1
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [← h1]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by rw [hG l]
  -- the degenerate case
  by_cases hnd : (∑ i, ins.wa i) ≠ 0 ∧ (∑ j, ins.wb j) ≠ 0
  swap
  · rw [not_and_or, not_not, not_not] at hnd
    have hzA : ∀ (Q : LWModule W) (Y : IntertwiningOperator (lwOf D a).isMod (lwOf D b).isMod
        Q.isMod) (m : ℂ), bracketModes Y m (∑ i, ins.wa i) (∑ j, ins.wb j) = 0 := by
      intro Q Y m
      rcases hnd with h0 | h0
      · rw [h0, map_zero, LinearMap.zero_apply]
      · rw [h0, map_zero]
    have hzB : ∀ (Q : LWModule W) (Y : IntertwiningOperator (lwOf D b).isMod (lwOf D a).isMod
        Q.isMod) (m : ℂ), bracketModes Y m (∑ j, ins.wb j) (∑ i, ins.wa i) = 0 := by
      intro Q Y m
      rcases hnd with h0 | h0
      · rw [h0, map_zero]
      · rw [h0, map_zero, LinearMap.zero_apply]
    have hgen : ∀ l, genTerm (G l) ins n τ = 0 := by
      intro l
      unfold genTerm
      split_ifs
      · rcases G l with C | B
        · simp only [genA]; rw [hzA, traceFunction_zero]
        · simp only [genA]; rw [hzB, traceFunction_zero, mul_zero]
      · rfl
    simp only [hgen, mul_zero, Finset.sum_const_zero]
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [hzA]
    erw [traceFun_zero]
    rw [mul_zero]
  -- alignment, enlarged
  obtain ⟨N0, -, hal1⟩ := ins_align D ins
  have hal := hal1 hnd.1 hnd.2
  have hint : ∀ l, ∃ m : ℕ, ∀ k : ℤ, D.h (genK (G l)) = k → k.natAbs ≤ m := by
    intro l
    by_cases h : ∃ k : ℤ, D.h (genK (G l)) = k
    · obtain ⟨k, hk⟩ := h
      refine ⟨k.natAbs, fun k' hk' => ?_⟩
      have : (k' : ℂ) = k := hk'.symm.trans hk
      have : k' = k := by exact_mod_cast this
      rw [this]
    · exact ⟨0, fun k hk => absurd ⟨k, hk⟩ h⟩
  choose mH hmH using hint
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ, N1 = N0 + t.natAbs + ∑ l, mH l := ⟨_, rfl⟩
  have hal' : ∀ i j, ins.wa i ≠ 0 → ins.wb j ≠ 0 →
      ∃ Dn : ℕ, ins.κ - ins.αa i - ins.αb j + N1 = Dn := by
    intro i j hi hj
    obtain ⟨Dn, h⟩ := hal i j hi hj
    refine ⟨Dn + (t.natAbs + ∑ l, mH l), ?_⟩
    rw [hN1]; push_cast; linear_combination h
  have hsum_le : ∀ l, mH l ≤ ∑ l, mH l := fun l =>
    Finset.single_le_sum (f := mH) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  have htabs := Int.le_natAbs (a := t)
  have hN1t : (0 : ℤ) ≤ (N1 : ℤ) - t := by rw [hN1]; omega
  obtain ⟨svac, hsv⟩ : ∃ svac : ℕ, (svac : ℤ) = N1 - t := ⟨((N1 : ℤ) - t).toNat,
    Int.toNat_of_nonneg hN1t⟩
  have hsvC : (svac : ℂ) = N1 - t := by exact_mod_cast hsv
  have hn : n = ins.κ - 1 - 0 - ((svac : ℂ) - N1) := by rw [ht, hsvC]; ring
  -- expansions
  choose δv hδv hvx using fun z => vacExpansion hV hv c ins N1 hal' τ z
  choose δg hδg hgx using fun l => genExpansion hV (G l) ins N1 hal' τ
  obtain ⟨δ1, hδ1, hle1⟩ := exists_pos_le_fintype δv hδv
  obtain ⟨δ2, hδ2, hle2⟩ := exists_pos_le_fintype δg hδg
  obtain ⟨δ0, hδ0, hz0⟩ := hg0 ins τ
  set ρ : ℝ := min δ1 δ2 / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < δ1 := by have := min_le_left δ1 δ2; rw [hρ]; linarith
  have hρ2 : ρ < δ2 := by have := min_le_right δ1 δ2; rw [hρ]; linarith
  -- the data
  let γ : ι ⊕ Fin r → ℂ := Sum.elim (fun _ => 0 - ins.κ - N1)
    (fun l => D.h (genK (G l)) - ins.κ - N1)
  let A : ι ⊕ Fin r → ℕ → ℂ := Sum.elim
    (fun z s => coef z * traceFun D.Mfam D.h z
      (bracketModes (P := lwOf D a) (Q := lwOf D b) (N := vacuumLW W hv) (epsInt F c)
        (ins.κ - 1 - 0 - ((s : ℂ) - N1)) (∑ i, ins.wa i) (∑ j, ins.wb j)) τ)
    (fun l s => -(lam l * genA (G l) ins (ins.κ - 1 - D.h (genK (G l)) - ((s : ℂ) - N1)) τ))
  -- summability at the real radius
  have hreρ : 0 < (exp (ρ : ℂ) - 1).re := by
    rw [← Complex.ofReal_exp, Complex.sub_re, Complex.ofReal_re, Complex.one_re]
    linarith [Real.add_one_lt_exp hρ0.ne']
  have hnρ : ‖(ρ : ℂ)‖ = ρ := by rw [Complex.norm_real, Real.norm_of_nonneg hρ0.le]
  have hρne : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
  have hsumρ : ∀ (γ0 : ℂ) (f : ℕ → ℂ) (x : ℂ),
      HasSum (fun s => f s * exp ((γ0 + s) * log (ρ : ℂ))) x →
      Summable (fun s => ‖f s‖ * ρ ^ s) := by
    intro γ0 f x hx
    have h1 := summable_norm_iff.mpr hx.summable
    have hc : 0 < ‖exp (γ0 * log (ρ : ℂ))‖ := norm_pos_iff.mpr (exp_ne_zero _)
    refine (h1.div_const ‖exp (γ0 * log (ρ : ℂ))‖).congr fun s => ?_
    rw [exp_mul_log_split hρne, norm_mul, norm_mul, norm_pow, hnρ]
    field_simp
  have hA : ∀ i, Summable (fun s => ‖A i s‖ * ρ ^ s) := by
    rintro (z | l)
    · have h1 := hsumρ _ _ _ (hvx z (ρ : ℂ) (by rw [hnρ]; exact lt_of_lt_of_le hρ1 (hle1 z))
        hreρ)
      refine (h1.mul_left ‖coef z‖).congr fun s => ?_
      simp only [A, Sum.elim_inl, norm_mul]
      ring
    · have h1 := hsumρ _ _ _ (hgx l (ρ : ℂ) (by rw [hnρ]; exact lt_of_lt_of_le hρ2 (hle2 l))
        hreρ)
      refine (h1.mul_left ‖lam l‖).congr fun s => ?_
      simp only [A, Sum.elim_inr, norm_neg, norm_mul]
      ring
  -- the identity on the sector
  have h0' : ∀ u ∈ sector τ (min δ0 ρ),
      ∑ i, ∑' s : ℕ, A i s * exp ((γ i + s) * log u) = 0 := by
    intro u hu
    obtain ⟨hun, hre, hre'⟩ := hu
    have hu0 : ‖u‖ < δ0 := lt_of_lt_of_le hun (min_le_left _ _)
    have huρ : ‖u‖ < ρ := lt_of_lt_of_le hun (min_le_right _ _)
    rw [Fintype.sum_sum_type]
    have hvz : ∀ z, ∑' s : ℕ, A (Sum.inl z) s * exp ((γ (Sum.inl z) + s) * log u) =
        coef z * vacF F hv c ins z τ u := by
      intro z
      have h1 := hvx z u (lt_of_lt_of_le (huρ.trans hρ1) (hle1 z)) hre
      simp only [A, γ, Sum.elim_inl]
      rw [← h1.tsum_eq, ← tsum_mul_left]
      exact tsum_congr fun s => by ring
    have hgl : ∀ l, ∑' s : ℕ, A (Sum.inr l) s * exp ((γ (Sum.inr l) + s) * log u) =
        -(lam l * genFun (G l) ins τ u) := by
      intro l
      have h1 := hgx l u (lt_of_lt_of_le (huρ.trans hρ2) (hle2 l)) hre
      simp only [A, γ, Sum.elim_inr]
      rw [← h1.tsum_eq, ← tsum_mul_left, ← tsum_neg]
      exact tsum_congr fun s => by ring
    simp only [hvz, hgl, Finset.sum_neg_distrib]
    have hg00 : g0 ins τ u = 0 := hz0 u ⟨hu0, hre, hre'⟩
    have := hrel u
    rw [hg00, add_zero] at this
    rw [this]; ring
  have huniq := gen_series_unique γ A hρ0 hA (sector_isOpen τ _)
    (sector_nonempty τ (lt_min hδ0 hρ0))
    (fun u hu => ⟨lt_of_lt_of_le hu.1 (min_le_right _ _), re_pos_of_exp_sub_one hu.2.1⟩)
    h0' ((0 - ins.κ - N1) + svac)
  rw [Fintype.sum_sum_type] at huniq
  have hvac_eval : ∀ z, ∑' s : ℕ, (if γ (Sum.inl z) + s = (0 - ins.κ - N1) + svac then
      A (Sum.inl z) s else 0) = coef z * traceFun D.Mfam D.h z
        (bracketModes (P := lwOf D a) (Q := lwOf D b) (N := vacuumLW W hv) (epsInt F c) n
          (∑ i, ins.wa i) (∑ j, ins.wb j)) τ := by
    intro z
    simp only [γ, Sum.elim_inl]
    rw [tsum_eq_single svac]
    · rw [if_pos rfl]
      simp only [A, Sum.elim_inl]
      rw [hn]
    · intro s hs
      rw [if_neg]
      intro h
      exact hs (by exact_mod_cast add_left_cancel h)
  have hgen_eval : ∀ l, ∑' s : ℕ, (if γ (Sum.inr l) + s = (0 - ins.κ - N1) + svac then
      A (Sum.inr l) s else 0) = -(lam l * genTerm (G l) ins n τ) := by
    intro l
    simp only [γ, Sum.elim_inr]
    by_cases hk : ∃ k : ℤ, D.h (genK (G l)) = k
    · obtain ⟨k, hk'⟩ := hk
      have hkle : k.natAbs ≤ mH l := hmH l k hk'
      have hsv2 : (0 : ℤ) ≤ (svac : ℤ) - k := by
        have h1 := hsum_le l
        have h2 := Int.le_natAbs (a := k)
        rw [hsv, hN1]; omega
      obtain ⟨s1, hs1⟩ : ∃ s1 : ℕ, (s1 : ℤ) = svac - k := ⟨_, Int.toNat_of_nonneg hsv2⟩
      have hs1C : (s1 : ℂ) = svac - k := by exact_mod_cast hs1
      have hμ : (0 - ins.κ - N1) + (svac : ℂ) = (D.h (genK (G l)) - ins.κ - N1) + s1 := by
        rw [hs1C, hk']; ring
      rw [hμ, tsum_eq_single s1]
      swap
      · intro s hs
        rw [if_neg]
        intro h
        exact hs (by exact_mod_cast add_left_cancel h)
      rw [if_pos rfl]
      simp only [A, Sum.elim_inr]
      unfold genTerm
      rw [if_pos ⟨k, hk'⟩]
      have hm : ins.κ - 1 - D.h (genK (G l)) - ((s1 : ℂ) - N1) = n := by
        rw [hn, hs1C, hk']; ring
      rw [hm]
    · have hne : ∀ s : ℕ, D.h (genK (G l)) - ins.κ - N1 + s ≠ (0 - ins.κ - N1) + svac := by
        intro s hs
        apply hk
        refine ⟨(svac : ℤ) - s, ?_⟩
        push_cast
        linear_combination hs
      simp only [hne, if_false, tsum_zero]
      unfold genTerm
      rw [if_neg hk, mul_zero, neg_zero]
  simp only [hvac_eval, hgen_eval, Finset.sum_neg_distrib] at huniq
  linear_combination huniq

/-- **(N4) for every instance from `TraceSeparationInput`.** -/
theorem channelIndependenceInput_of_separation (h : TraceSeparationInput.{u, w}) :
    ChannelIndependenceInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D hZ hirr hcomp F a b c hv η' hη'
  exact channelIndependence_of_separation hNice.1 hv c η'
    (h 𝒱 W hNice ι D hZ hirr hcomp F a b c hv η' hη')

/-- **Huang's Theorem 5.2 from three ALGEBRAIC inputs.** Every analytic step of (G1) —
the genus-one convergence, the bracket-coordinate expansions, the S-transformation of the
channels, the continuation across the period cell and the coefficient extraction — is proved. -/
theorem fusionEigenInput_of_algebraic (hsub : IntertwinerSubstitutionInput.{u})
    (hS : TraceSkewInput.{u, w}) (hsep : TraceSeparationInput.{u, w}) :
    VerlindeEigen.FusionEigenInput.{u, w} :=
  fusionEigenInput_of_substitution_skew hsub hS (channelIndependenceInput_of_separation hsep)

end VOA.Huang.GenusOneG1e
