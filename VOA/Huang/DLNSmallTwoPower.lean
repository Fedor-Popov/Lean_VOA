import VOA.Huang.DLNSmallTwoAvg
import VOA.Huang.DLNSmallThreePower

/-!
# The two-adic layer bound and `TwoPowerInflationFromTwo`

For `a ≥ 1`, `G = SL₂(ℤ/2^{a+1})`, `N = ker(G → SL₂(ℤ/2^a))`, and a central extension
`π : E ↠ G` with `M = π⁻¹N`, the subgroup `⁅E, M⁆ ∩ ker π` has at most two elements: it lies in
`{1, ν}` where `ν = ⁅x(2)^, y(2^a)^⁆` (`layerAtMostTwo_rhoTwo`).

Proof. In `Ē = E/⟨ν⟩` the lifts of `x(2)` and `y(2^a)` commute. From this, conjugation by
`x(1)`, `y(1)` and the Weyl element shows: the lifts of the generators `x(2), y(2), -1` of `K₁`
centralize `π⁻¹N`, and the lifts of the central scalar `ε = 1 + 2^a` are central. The relative
averaging criterion over `C₃ ⊂ SL₂(ℤ/2)` (whose average sends `N` into `{1, ε}`) gives
`⁅Ē, M̄⁆ ∩ ker = 1`.

Consequences: `|H₂(SL₂(ℤ/4))| ≤ 2` (from the Schur-trivial quotient `SL₂(ℤ/2)`), and with the
stem-cover argument of `DLNSmallTwoCover`, Beyl's Corollary 3.10:
`TwoPowerInflationFromTwo` (`twoPowerInflationFromTwo`).
-/

namespace VOA.Huang.DLNSchur

open VOA.Huang.DLNBeyl
open scoped commutatorElement

section TwoPower

variable {a : ℕ}

theorem rhoTwoOne_surjective (a : ℕ) : Function.Surjective (rhoTwoOne a) := by
  intro g
  obtain ⟨γ, rfl⟩ := reduction_surjective 2 g
  refine ⟨VOA.Huang.DLN.reduction (2 ^ (a + 1)) γ, ?_⟩
  have := congrArg (fun f => f γ) (reductionMod_comp_reduction (2 ^ (a + 1)) 2
    (dvd_pow_self 2 (Nat.succ_ne_zero a)))
  exact this

theorem nE2_eq_pow (ha : 1 ≤ a) : nE2 a = x2 a ^ (2 ^ (a - 1)) := by
  show (upperRoot ((2 : ZMod (2 ^ (a + 1))) ^ a) : SLT a) = upperRoot 2 ^ (2 ^ (a - 1))
  rw [upperRoot_pow]; congr 1; push_cast
  rw [← pow_succ, Nat.sub_add_cancel ha]

theorem nE2_eq_pow_one : nE2 a = upperRoot 1 ^ (2 ^ a) := by
  show (upperRoot ((2 : ZMod (2 ^ (a + 1))) ^ a) : SLT a) = upperRoot 1 ^ (2 ^ a)
  rw [upperRoot_pow]; congr 1; push_cast; ring

theorem nF2_eq_pow_one : nF2 a = lowerRoot 1 ^ (2 ^ a) := by
  show (lowerRoot ((2 : ZMod (2 ^ (a + 1))) ^ a) : SLT a) = lowerRoot 1 ^ (2 ^ a)
  rw [lowerRoot_pow]; congr 1; push_cast; ring

theorem liftPair_comm {G E : Type*} [Group G] [Group E] {π : E →* G}
    {hs : Function.Surjective π} (hc : π.ker ≤ Subgroup.center E) (a b : G) :
    liftPair π hs b a = (liftPair π hs a b)⁻¹ := by
  unfold liftPair
  rw [commutatorElement_inv]

/-- **Core of the two-adic layer bound.** If lifts of `x(2)` and `y(2^a)` commute, then
`⁅E, π⁻¹N⁆ ∩ ker π = 1`. -/
theorem layerTwo_eq_one_of_commute (ha : 1 ≤ a) {E : Type} [Group E] (π : E →* SLT a)
    (hs : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E)
    (hν : ∀ x y : E, π x = x2 a → π y = nF2 a → Commute x y) :
    ∀ x ∈ ⁅(⊤ : Subgroup E), (rhoTwo a).ker.comap π⁆, π x = 1 → x = 1 := by
  have hcm : ∀ g ∈ levelOneTwo a, ∀ n ∈ (rhoTwo a).ker, Commute g n :=
    fun g hg n hn => levelOneTwo_commute_layer hg hn
  have hof : ∀ g h : SLT a, (∀ x y : E, π x = g → π y = h → Commute x y) →
      liftPair π hs g h = 1 :=
    fun g h hgh => liftPair_eq_one_of_commute hc (Function.surjInv_eq hs g)
      (Function.surjInv_eq hs h) (hgh _ _ (Function.surjInv_eq hs g) (Function.surjInv_eq hs h))
  have hto : ∀ g h : SLT a, liftPair π hs g h = 1 → ∀ x y : E, π x = g → π y = h →
      Commute x y := fun g h hgh x y hx hy => commute_of_liftPair_eq_one hc hgh hx hy
  have hNE := nE2_mem (a := a)
  have hNF := nF2_mem (a := a)
  have hEPS := eps2_mem ha
  have hX2 := x2_mem (a := a)
  have hY2 := y2_mem (a := a)
  have hMI := mI2_mem (a := a)
  have hNK : ∀ n ∈ (rhoTwo a).ker, n ∈ levelOneTwo a := fun n hn => layerTwo_le_levelOne ha hn
  -- Pairings of the generators of `K₁` with `x(q)` and `y(q)`.
  have f1 : liftPair π hs (x2 a) (nE2 a) = 1 :=
    hof _ _ (fun x y hx hy => upper_lifts_commute π hs hc hx hy)
  have f2 : liftPair π hs (y2 a) (nF2 a) = 1 :=
    hof _ _ (fun x y hx hy => lower_lifts_commute π hs hc hx hy)
  have f3 : liftPair π hs (x2 a) (nF2 a) = 1 := hof _ _ hν
  have f4 : liftPair π hs (y2 a) (nE2 a) = 1 := by
    have h := liftPair_conj (hs := hs) hc (hcm _ hX2 _ hNF) (weyl 1)
    rw [w_conj_x2, w_conj_nF2, f3, liftPair_inv_left hc (hcm _ hY2 _ hNE), inv_eq_one] at h
    exact h
  have hmI : ∀ t : ZMod (2 ^ (a + 1)), Commute (mI2 a) (upperRoot t) ∧
      Commute (mI2 a) (lowerRoot t) := fun t => ⟨mI2_central _, mI2_central _⟩
  have hsq : ∀ g : SLT a, liftPair π hs (mI2 a) g ^ 2 = 1 := by
    intro g
    rw [← liftPair_pow_left hc (mI2_central g), mI2_sq, liftPair_one_left hc]
  have hpow : ∀ g : SLT a, liftPair π hs (mI2 a) g ^ (2 ^ a) = 1 := by
    intro g
    rw [show 2 ^ a = 2 * 2 ^ (a - 1) by rw [← pow_succ']; congr 1; omega, pow_mul, hsq, one_pow]
  have f5 : liftPair π hs (mI2 a) (nE2 a) = 1 := by
    rw [nE2_eq_pow_one, liftPair_pow_right hc (hmI 1).1, hpow]
  have f6 : liftPair π hs (mI2 a) (nF2 a) = 1 := by
    rw [nF2_eq_pow_one, liftPair_pow_right hc (hmI 1).2, hpow]
  -- Pairings inside the layer.
  have g1 : liftPair π hs (nF2 a) (nE2 a) = 1 := by
    rw [nE2_eq_pow ha, liftPair_pow_right hc (hcm _ hX2 _ hNF).symm, liftPair_comm hc, f3,
      inv_one, one_pow]
  have g1' : liftPair π hs (nE2 a) (nF2 a) = 1 := by
    rw [liftPair_comm hc, g1, inv_one]
  have g2 : liftPair π hs (nE2 a) (eps2 a) = 1 := by
    have h := liftPair_conj (hs := hs) hc (hcm _ (hNK _ hNE) _ hNF) (upperRoot 1)
    rw [upperRoot_conj_upperRoot, u_conj_nF2 ha,
      liftPair_mul_right hc (hcm _ (hNK _ hNE) _ hEPS),
      liftPair_mul_right hc (hcm _ (hNK _ hNE) _ hNF),
      liftPair_inv_right hc (hcm _ (hNK _ hNE) _ hNE), g1'] at h
    have hself : liftPair π hs (nE2 a) (nE2 a) = 1 := hof _ _ (fun x y hx hy =>
      upper_lifts_commute π hs hc hx hy)
    rw [hself, inv_one, one_mul, one_mul] at h
    exact h
  have g3 : liftPair π hs (nF2 a) (eps2 a) = 1 := by
    have h := liftPair_conj (hs := hs) hc (hcm _ (hNK _ hNF) _ hNE) (lowerRoot 1)
    rw [lowerRoot_conj_lowerRoot, v_conj_nE2 ha,
      liftPair_mul_right hc (hcm _ (hNK _ hNF) _ (inv_mem hEPS)),
      liftPair_mul_right hc (hcm _ (hNK _ hNF) _ (inv_mem hNF)),
      liftPair_inv_right hc (hcm _ (hNK _ hNF) _ hNF),
      liftPair_inv_right hc (hcm _ (hNK _ hNF) _ hEPS), g1] at h
    have hself : liftPair π hs (nF2 a) (nF2 a) = 1 := hof _ _ (fun x y hx hy =>
      lower_lifts_commute π hs hc hx hy)
    rw [hself, inv_one, mul_one, one_mul, inv_eq_one] at h
    exact h
  -- The preimage of the layer is abelian.
  have hMcomm : ∀ x y : E, π x ∈ (rhoTwo a).ker → π y ∈ (rhoTwo a).ker → Commute x y := by
    intro x y hx hy
    refine commute_of_mem_closure π hs hc {nE2 a, nF2 a, eps2 a} {nE2 a, nF2 a, eps2 a} ?_ x y
      (layerTwo_le_closure ha hx) (layerTwo_le_closure ha hy)
    have hEE : liftPair π hs (nE2 a) (nE2 a) = 1 := hof _ _ (fun x y hx hy =>
      upper_lifts_commute π hs hc hx hy)
    have hFF : liftPair π hs (nF2 a) (nF2 a) = 1 := hof _ _ (fun x y hx hy =>
      lower_lifts_commute π hs hc hx hy)
    have hee : liftPair π hs (eps2 a) (eps2 a) = 1 := by
      unfold liftPair; simp
    have hEF := g1'
    have hFE := g1
    have hEe := g2
    have hFe := g3
    have heE : liftPair π hs (eps2 a) (nE2 a) = 1 := by rw [liftPair_comm hc, g2, inv_one]
    have heF : liftPair π hs (eps2 a) (nF2 a) = 1 := by rw [liftPair_comm hc, g3, inv_one]
    intro g hg h hh
    apply hto
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg hh
    rcases hg with rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl <;> assumption
  -- Lifts of `ε` commute with lifts of `x(1)` and `y(1)`.
  have hεx : ∀ x y : E, π x = upperRoot 1 → π y = eps2 a → Commute x y := by
    intro X e hX he
    set s := Function.surjInv hs (nE2 a)
    set t := Function.surjInv hs (nF2 a)
    have hs' : π s = nE2 a := Function.surjInv_eq hs _
    have ht' : π t = nF2 a := Function.surjInv_eq hs _
    set T' := X * t * X⁻¹ with hT'
    set e' := s * T' * t⁻¹ with he'
    have hπe' : π e' = eps2 a := by
      simp only [he', hT', map_mul, map_inv, hX, hs', ht']
      rw [u_conj_nF2 ha]
      have := (eps2_central ha (nF2 a)).eq
      calc nE2 a * ((nE2 a)⁻¹ * nF2 a * eps2 a) * (nF2 a)⁻¹ = nF2 a * eps2 a * (nF2 a)⁻¹ := by
            group
        _ = eps2 a := by rw [← this]; group
    have hXs : Commute X s := upper_lifts_commute π hs hc hX hs'
    have hX2t : Commute (X * X) t := hν _ _ (by rw [map_mul, hX, ← upperRoot_add]; norm_num) ht'
    have hT'N : π T' ∈ (rhoTwo a).ker := by
      simp only [hT', map_mul, map_inv, hX, ht']
      exact (rhoTwo a).normal_ker.conj_mem _ hNF _
    have htT : Commute t T' := hMcomm _ _ (by rw [ht']; exact hNF) hT'N
    have ht2 : t * t ∈ Subgroup.center E := hc (by
      rw [MonoidHom.mem_ker, map_mul, ht', ← pow_two, layerTwo_sq ha hNF])
    have hTT : T' * T' = t * t := by
      calc T' * T' = X * (t * t) * X⁻¹ := by simp only [hT']; group
        _ = t * t := by rw [Subgroup.mem_center_iff.mp ht2 X, mul_inv_cancel_right]
    have key : t * T'⁻¹ = T' * t⁻¹ := by
      have h1 : t * T'⁻¹ * (T' * t⁻¹)⁻¹ = 1 := by
        calc t * T'⁻¹ * (T' * t⁻¹)⁻¹ = t * T'⁻¹ * t * T'⁻¹ := by group
          _ = t * t * T'⁻¹ * T'⁻¹ := by
            rw [mul_assoc t T'⁻¹ t, ← htT.inv_right.eq, ← mul_assoc]
          _ = 1 := by rw [← hTT]; group
      exact mul_inv_eq_one.mp h1
    have hcomm : Commute X e' := by
      change X * e' = e' * X
      calc X * e' = s * (X * X * t) * X⁻¹ * t⁻¹ := by
            simp only [he', hT']
            calc X * (s * (X * t * X⁻¹) * t⁻¹) = (X * s) * X * t * X⁻¹ * t⁻¹ := by group
              _ = (s * X) * X * t * X⁻¹ * t⁻¹ := by rw [hXs.eq]
              _ = s * (X * X * t) * X⁻¹ * t⁻¹ := by group
        _ = s * (t * (X * X)) * X⁻¹ * t⁻¹ := by rw [hX2t.eq]
        _ = s * (t * T'⁻¹) * X := by simp only [hT']; group
        _ = s * (T' * t⁻¹) * X := by rw [key]
        _ = e' * X := by simp only [he']; group
    have hee' : π e' = π e := by rw [hπe', he]
    obtain ⟨z, hz, rfl⟩ : ∃ z ∈ Subgroup.center E, e = e' * z :=
      ⟨e'⁻¹ * e, hc (by rw [MonoidHom.mem_ker, map_mul, map_inv, hee', inv_mul_cancel]),
        by group⟩
    exact hcomm.mul_right (Subgroup.mem_center_iff.mp hz X)
  have hεy : ∀ x y : E, π x = lowerRoot 1 → π y = eps2 a → Commute x y := by
    intro Y e hY he
    set s := Function.surjInv hs (nE2 a)
    set t := Function.surjInv hs (nF2 a)
    have hs' : π s = nE2 a := Function.surjInv_eq hs _
    have ht' : π t = nF2 a := Function.surjInv_eq hs _
    obtain ⟨S', hS'⟩ : ∃ S', S' = Y * s * Y⁻¹ := ⟨_, rfl⟩
    obtain ⟨e', he'⟩ : ∃ e', e' = S'⁻¹ * s * t⁻¹ := ⟨_, rfl⟩
    have hπe' : π e' = eps2 a := by
      simp only [he', hS', map_mul, map_inv, hY, hs', ht']
      rw [v_conj_nE2 ha]
      group
    have hYt : Commute Y t := lower_lifts_commute π hs hc hY ht'
    have hY2s : Commute (Y * Y) s := by
      have hy2 : π (Y * Y) = y2 a := by rw [map_mul, hY, ← lowerRoot_add]; norm_num
      exact hto _ _ f4 _ _ hy2 hs'
    have hS'N : π S' ∈ (rhoTwo a).ker := by
      simp only [hS', map_mul, map_inv, hY, hs']
      exact (rhoTwo a).normal_ker.conj_mem _ hNE _
    have hsS : Commute s S' := hMcomm _ _ (by rw [hs']; exact hNE) hS'N
    have hs2 : s * s ∈ Subgroup.center E := hc (by
      rw [MonoidHom.mem_ker, map_mul, hs', ← pow_two, layerTwo_sq ha hNE])
    have hSS : S' * S' = s * s := by
      calc S' * S' = Y * (s * s) * Y⁻¹ := by simp only [hS']; group
        _ = s * s := by rw [Subgroup.mem_center_iff.mp hs2 Y, mul_inv_cancel_right]
    have key : s⁻¹ * S' = S'⁻¹ * s := by
      have h1 : (S'⁻¹ * s)⁻¹ * (s⁻¹ * S') = 1 := by
        calc (S'⁻¹ * s)⁻¹ * (s⁻¹ * S') = s⁻¹ * S' * s⁻¹ * S' := by group
          _ = s⁻¹ * s⁻¹ * S' * S' := by
            rw [mul_assoc s⁻¹ S' s⁻¹, ← hsS.inv_left.eq, ← mul_assoc]
          _ = 1 := by rw [mul_assoc _ S' S', hSS]; group
      exact (inv_mul_eq_one.mp h1).symm
    have hcomm : Commute Y e' := by
      change Y * e' = e' * Y
      calc Y * e' = Y * (Y * s * Y⁻¹)⁻¹ * s * t⁻¹ := by simp only [he', hS']; group
        _ = ((Y * Y) * s⁻¹) * Y⁻¹ * Y⁻¹ * Y * s * t⁻¹ := by group
        _ = (s⁻¹ * (Y * Y)) * Y⁻¹ * Y⁻¹ * Y * s * t⁻¹ := by rw [hY2s.inv_right.eq]
        _ = s⁻¹ * (Y * s * Y⁻¹) * (Y * t⁻¹) := by group
        _ = s⁻¹ * S' * (t⁻¹ * Y) := by rw [hYt.inv_right.eq, hS']
        _ = (s⁻¹ * S') * t⁻¹ * Y := by group
        _ = (S'⁻¹ * s) * t⁻¹ * Y := by rw [key]
        _ = e' * Y := by simp only [he']
    have hee' : π e' = π e := by rw [hπe', he]
    obtain ⟨z, hz, rfl⟩ : ∃ z ∈ Subgroup.center E, e = e' * z :=
      ⟨e'⁻¹ * e, hc (by rw [MonoidHom.mem_ker, map_mul, map_inv, hee', inv_mul_cancel]),
        by group⟩
    exact hcomm.mul_right (Subgroup.mem_center_iff.mp hz Y)
  -- Lifts of `ε` are central.
  have hεc : ∀ e : E, π e = eps2 a → e ∈ Subgroup.center E := by
    intro e he
    rw [Subgroup.mem_center_iff]
    intro d
    have := commute_of_mem_closure π hs hc {upperRoot 1, lowerRoot 1} {eps2 a} (by
      intro g hg h hh x y hx hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg hh
      subst hh
      rcases hg with rfl | rfl
      · exact hεx x y hx hy
      · exact hεy x y hx hy) d e (by rw [root_generators]; trivial)
      (Subgroup.subset_closure (by rw [he]; rfl))
    exact this.eq
  -- Lifts of `K₁` centralize `π⁻¹N`.
  have hcent : ∀ e m : E, rhoTwoOne a (π e) = 1 → π m ∈ (rhoTwo a).ker → Commute e m := by
    intro e m he hm
    refine commute_of_mem_closure π hs hc {x2 a, y2 a, mI2 a} {nE2 a, nF2 a, eps2 a} ?_ e m
      (levelOneTwo_le_closure ha he) (layerTwo_le_closure ha hm)
    intro g hg h hh x y hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg hh
    rcases hh with rfl | rfl | rfl
    · rcases hg with rfl | rfl | rfl
      · exact hto _ _ f1 x y hx hy
      · exact hto _ _ f4 x y hx hy
      · exact hto _ _ f5 x y hx hy
    · rcases hg with rfl | rfl | rfl
      · exact hto _ _ f3 x y hx hy
      · exact hto _ _ f2 x y hx hy
      · exact hto _ _ f6 x y hx hy
    · exact Subgroup.mem_center_iff.mp (hεc y hy) x
  -- The averaging criterion.
  have hC₀ : ∀ e : E, π e ∈ Subgroup.zpowers (eps2 a) → e ∈ Subgroup.center E := by
    intro e he
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp he
    set eh := Function.surjInv hs (eps2 a)
    have heh : eh ∈ Subgroup.center E := hεc _ (Function.surjInv_eq hs _)
    have : e = eh ^ k * ((eh ^ k)⁻¹ * e) := by group
    rw [this]
    refine mul_mem (Subgroup.zpow_mem _ heh k) (hc ?_)
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, Function.surjInv_eq hs, hk,
      inv_mul_cancel]
  exact layer_eq_one_of_averaging_rel π hs hc (rhoTwo a).ker (rhoTwoOne a)
    (rhoTwoOne_surjective a) (layerTwo_le_levelOne ha) hcent c3Finset c3Finset_conj 2
    (fun n hn => layerTwo_sq ha hn) (by rw [c3Finset_card]; norm_num) (Subgroup.zpowers (eps2 a))
    hC₀ (fun g hg n hn => layerTwo_c3_average ha g hg n hn)

theorem eq_one_or_eq_of_mem_zpowers {E : Type*} [Group E] {ν x : E} (hν : ν ^ 2 = 1)
    (hx : x ∈ Subgroup.zpowers ν) : x = 1 ∨ x = ν := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hν' : ν ^ (2 : ℤ) = 1 := by exact_mod_cast hν
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, hν', one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, hν', one_zpow, mul_one, zpow_one]

/-- **The two-adic layer bound.** For `a ≥ 1`, in every central extension of
`SL₂(ℤ/2^{a+1})`, the subgroup `⁅E, π⁻¹N⁆ ∩ ker π` has at most two elements. -/
theorem layerAtMostTwo_rhoTwo (ha : 1 ≤ a) : LayerAtMostTwo (rhoTwo a) := by
  intro E _ π hs hc
  have hcm := levelOneTwo_commute_layer (x2_mem (a := a)) (nF2_mem (a := a))
  set ν := liftPair π hs (x2 a) (nF2 a) with hνdef
  have hνc : ν ∈ Subgroup.center E := liftPair_mem_center hc hcm
  have hν2 : ν ^ 2 = 1 := by
    rw [hνdef, ← liftPair_pow_right hc hcm 2, layerTwo_sq ha nF2_mem, liftPair_one_right hc]
  have hνker : π ν = 1 := by rw [hνdef, map_liftPair, hcm.commutator_eq]
  set K := Subgroup.zpowers ν with hK
  haveI : K.Normal := by
    constructor
    intro n hn g
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hνc k) g, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers ν k
  have hKle : K ≤ π.ker := (Subgroup.zpowers_le).mpr hνker
  let πb : E ⧸ K →* SLT a := QuotientGroup.lift K π hKle
  have hπb : ∀ e : E, πb (QuotientGroup.mk e) = π e := fun e => rfl
  have hsb : Function.Surjective πb := by
    intro g
    obtain ⟨e, rfl⟩ := hs g
    exact ⟨QuotientGroup.mk e, rfl⟩
  have hcb : πb.ker ≤ Subgroup.center (E ⧸ K) := by
    intro y hy
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective K y
    have he : e ∈ Subgroup.center E := hc hy
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective K w
    change QuotientGroup.mk' K (d * e) = QuotientGroup.mk' K (e * d)
    rw [Subgroup.mem_center_iff.mp he d]
  have hνb : ∀ x y : E ⧸ K, πb x = x2 a → πb y = nF2 a → Commute x y := by
    intro x y hx hy
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective K x
    obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective K y
    have h1 : ⁅e, f⁆ = ν := commutator_eq_liftPair hc hx hy
    have h2 : QuotientGroup.mk' K ⁅e, f⁆ = 1 := by
      rw [h1]; exact (QuotientGroup.eq_one_iff ν).mpr (Subgroup.mem_zpowers ν)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2
  have core := layerTwo_eq_one_of_commute ha πb hsb hcb hνb
  have hmap : ∀ w ∈ ⁅(⊤ : Subgroup E), (rhoTwo a).ker.comap π⁆,
      QuotientGroup.mk' K w ∈ ⁅(⊤ : Subgroup (E ⧸ K)), (rhoTwo a).ker.comap πb⁆ := by
    intro w hw
    have hle : (⁅(⊤ : Subgroup E), (rhoTwo a).ker.comap π⁆).map (QuotientGroup.mk' K) ≤
        ⁅(⊤ : Subgroup (E ⧸ K)), (rhoTwo a).ker.comap πb⁆ := by
      rw [Subgroup.map_commutator]
      apply Subgroup.commutator_mono le_top
      rintro _ ⟨m, hm, rfl⟩
      exact hm
    exact hle ⟨w, hw, rfl⟩
  have hK : ∀ w ∈ ⁅(⊤ : Subgroup E), (rhoTwo a).ker.comap π⁆, π w = 1 → w = 1 ∨ w = ν := by
    intro w hw hπw
    have h1 := core _ (hmap w hw) (by rw [QuotientGroup.mk'_apply, hπb]; exact hπw)
    exact eq_one_or_eq_of_mem_zpowers hν2 ((QuotientGroup.eq_one_iff w).mp h1)
  intro x hx y hy hπx hπy
  rcases hK x hx hπx with h | h
  · exact Or.inl h
  · rcases hK y hy hπy with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (h.trans h'.symm))

end TwoPower

/-- **`|H₂(SL₂(ℤ/4))| ≤ 2`**, homology-free. -/
theorem twoBaseMult_holds : TwoBaseMult := by
  have hS : SchurTrivial (Matrix.SpecialLinearGroup (Fin 2) (ZMod (2 ^ 1))) := by
    simpa using schurTrivial_SL_two
  have h := multAtMostTwo_of_inflation_layer (rhoTwo 1) (rhoTwo_surjective 1)
    (inflationTrivial_of_schurTrivial_target _ hS) (layerAtMostTwo_rhoTwo le_rfl)
  exact h

/-- The two-adic layer bound in the range `a ≥ 2`. -/
theorem twoLayerAtMostTwo_holds : TwoLayerAtMostTwo :=
  fun _ ha => layerAtMostTwo_rhoTwo (by omega)

/-- **`|H₂(SL₂(ℤ/2^a))| ≤ 2` for all `a ≥ 2`.** -/
theorem twoPowerMultAtMostTwo_holds : TwoPowerMultAtMostTwo :=
  twoPowerMultAtMostTwo_of_base_layer twoBaseMult_holds twoLayerAtMostTwo_holds

/-- **Beyl's Corollary 3.10 (homology-free).** For `a ≥ 2`, the inflation
`H₂(SL₂(ℤ/2^{a+1})) → H₂(SL₂(ℤ/2^a))` vanishes. -/
theorem twoPowerInflationFromTwo_holds : TwoPowerInflationFromTwo :=
  twoPowerInflationFromTwo_of_base_layer twoBaseMult_holds twoLayerAtMostTwo_holds

/-- The original residual `TwoPowerInflation` (all `a ≥ 1`). -/
theorem twoPowerInflation_holds : TwoPowerInflation :=
  twoPowerInflation_iff_fromTwo.mpr twoPowerInflationFromTwo_holds

end VOA.Huang.DLNSchur
