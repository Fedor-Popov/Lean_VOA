import VOA.Huang.DLNBeylInflation

/-!
# Künneth-free splitting of inflation vanishing over a product

`inflationTrivial_of_split`: if `r : B → A` decomposes as a product `r₁ × r₂` (expressed by
bijective pairs of projections), each factor has trivial inflation, and the abelianizations
of `B₁`, `B₂` have coprime exponents, then `r` has trivial inflation.

This is the group-theoretic shadow of the Künneth formula
`H₂(B₁ × B₂) = H₂(B₁) ⊕ H₂(B₂) ⊕ (H₁B₁ ⊗ H₁B₂)`: the cross term dies by coprimality.

Proof: replace the source by the pullback `P = E ×_A B ≤ E × B`; `P = Q₁ Q₂` with
`Qᵢ = P ∩ (second coordinate in the `i`-th factor)`; the commutator pairing `Q₁ × Q₂ → ker π`
is bimultiplicative, killed by `n₁` and `n₂`, hence trivial; so `[P, P] = [Q₁, Q₁][Q₂, Q₂]`, and
each factor is controlled by the inflation hypothesis on `rᵢ`.
-/

namespace VOA.Huang.DLNBeyl

open scoped commutatorElement

section Split

variable {A B A₁ A₂ B₁ B₂ E : Type} [Group A] [Group B] [Group A₁] [Group A₂]
  [Group B₁] [Group B₂] [Group E]

/-- The pullback `E ×_A B` as a subgroup of `E × B`. -/
def pullback (π : E →* A) (r : B →* A) : Subgroup (E × B) :=
  (π.comp (MonoidHom.fst E B)).eqLocus (r.comp (MonoidHom.snd E B))

/-- The part of the pullback whose `B`-coordinate is killed by `p`. -/
def piece {C : Type} [Group C] (π : E →* A) (r : B →* A) (p : B →* C) : Subgroup (E × B) :=
  pullback π r ⊓ (p.comp (MonoidHom.snd E B)).ker

theorem mem_pullback {π : E →* A} {r : B →* A} {x : E × B} :
    x ∈ pullback π r ↔ π x.1 = r x.2 := Iff.rfl

theorem mem_piece {C : Type} [Group C] {π : E →* A} {r : B →* A} {p : B →* C} {x : E × B} :
    x ∈ piece π r p ↔ π x.1 = r x.2 ∧ p x.2 = 1 := Iff.rfl

/-- Commutators of two commuting pairs. -/
theorem commutator_mul_mul_of_commute {G : Type*} [Group G] {a b c d : G}
    (hac : Commute a c) (had : Commute a d) (hbc : Commute b c) (hbd : Commute b d) :
    ⁅a * c, b * d⁆ = ⁅a, b⁆ * ⁅c, d⁆ := by
  have h1 : a * c * (b * d) = a * b * (c * d) := (hbc.symm.mul_mul_mul_comm a d)
  have h2 : (a * c)⁻¹ * (b * d)⁻¹ = a⁻¹ * b⁻¹ * (c⁻¹ * d⁻¹) := by
    rw [mul_inv_rev, mul_inv_rev, hac.symm.inv_inv.eq, hbd.inv_inv.symm.eq]
    exact (hbc.inv_inv.symm.mul_mul_mul_comm a⁻¹ d⁻¹)
  have h3 : Commute (c * d) (a⁻¹ * b⁻¹) :=
    ((hac.symm.inv_right).mul_right hbc.symm.inv_right).mul_left
      ((had.symm.inv_right).mul_right hbd.symm.inv_right)
  calc ⁅a * c, b * d⁆ = a * c * (b * d) * ((a * c)⁻¹ * (b * d)⁻¹) := by
        rw [commutatorElement_def]; group
    _ = a * b * (c * d) * (a⁻¹ * b⁻¹ * (c⁻¹ * d⁻¹)) := by rw [h1, h2]
    _ = a * b * ((c * d) * (a⁻¹ * b⁻¹)) * (c⁻¹ * d⁻¹) := by group
    _ = a * b * ((a⁻¹ * b⁻¹) * (c * d)) * (c⁻¹ * d⁻¹) := by rw [h3.eq]
    _ = ⁅a, b⁆ * ⁅c, d⁆ := by rw [commutatorElement_def, commutatorElement_def]; group

/-- Commutators with a fixed element, all central, multiply. -/
theorem commutator_mul_left_of_central {G : Type*} [Group G] {a b e : G}
    (hb : ⁅b, e⁆ ∈ Subgroup.center G) : ⁅a * b, e⁆ = ⁅a, e⁆ * ⁅b, e⁆ := by
  have h : ⁅a * b, e⁆ = a * ⁅b, e⁆ * a⁻¹ * ⁅a, e⁆ := by
    simp only [commutatorElement_def]; group
  rw [h, Subgroup.mem_center_iff.mp hb a, mul_inv_cancel_right]
  exact (Subgroup.mem_center_iff.mp hb _).symm

variable (π : E →* A) (r : B →* A) (pB₁ : B →* B₁) (pB₂ : B →* B₂)

/-- Second coordinates in complementary pieces commute (injectivity of the splitting). -/
theorem piece_snd_commutator (hB : Function.Injective fun b => (pB₁ b, pB₂ b))
    {q₁ q₂ : E × B} (h₁ : q₁ ∈ piece π r pB₂) (h₂ : q₂ ∈ piece π r pB₁) :
    ⁅q₁.2, q₂.2⁆ = 1 := by
  apply hB
  simp only [map_commutatorElement, (mem_piece.mp h₁).2, (mem_piece.mp h₂).2,
    commutatorElement_one_left, commutatorElement_one_right, map_one]

/-- First coordinates of complementary pieces have central commutator. -/
theorem piece_fst_commutator_central (hc : π.ker ≤ Subgroup.center E)
    (hB : Function.Injective fun b => (pB₁ b, pB₂ b))
    {q₁ q₂ : E × B} (h₁ : q₁ ∈ piece π r pB₂) (h₂ : q₂ ∈ piece π r pB₁) :
    ⁅q₁.1, q₂.1⁆ ∈ Subgroup.center E := by
  apply hc
  rw [MonoidHom.mem_ker, map_commutatorElement, (mem_piece.mp h₁).1, (mem_piece.mp h₂).1,
    ← map_commutatorElement, piece_snd_commutator π r pB₁ pB₂ hB h₁ h₂, map_one]

/-- The commutator with a fixed element of the complementary piece, as a homomorphism. -/
def pieceCommHom (hc : π.ker ≤ Subgroup.center E)
    (hB : Function.Injective fun b => (pB₁ b, pB₂ b))
    {q₂ : E × B} (h₂ : q₂ ∈ piece π r pB₁) :
    ↥(piece π r pB₂) →* ↥(Subgroup.center E) where
  toFun y := ⟨⁅(y : E × B).1, q₂.1⁆, piece_fst_commutator_central π r pB₁ pB₂ hc hB y.2 h₂⟩
  map_one' := by ext; simp
  map_mul' y z := by
    ext
    simp only [Subgroup.coe_mul, Prod.fst_mul]
    exact commutator_mul_left_of_central
      (piece_fst_commutator_central π r pB₁ pB₂ hc hB z.2 h₂)

theorem pieceCommHom_commutator (hc : π.ker ≤ Subgroup.center E)
    (hB : Function.Injective fun b => (pB₁ b, pB₂ b))
    {q₂ : E × B} (h₂ : q₂ ∈ piece π r pB₁) :
    commutator ↥(piece π r pB₂) ≤ (pieceCommHom π r pB₁ pB₂ hc hB h₂).ker := by
  rw [commutator_def, Subgroup.commutator_le]
  intro u _ v _
  rw [MonoidHom.mem_ker, map_commutatorElement]
  apply commutatorElement_eq_one_iff_commute.mpr
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp ((pieceCommHom π r pB₁ pB₂ hc hB h₂) v).2 _

/-- The projection of a piece onto its factor is surjective. -/
theorem piece_proj_surjective (hπ : Function.Surjective π)
    (hB : Function.Surjective fun b => (pB₁ b, pB₂ b)) :
    Function.Surjective (pB₁.comp ((MonoidHom.snd E B).comp (piece π r pB₂).subtype)) := by
  intro b₁
  obtain ⟨b, hb⟩ := hB (b₁, 1)
  obtain ⟨e, he⟩ := hπ (r b)
  simp only [Prod.mk.injEq] at hb
  exact ⟨⟨(e, b), mem_piece.mpr ⟨he, hb.2⟩⟩, by simp [hb.1]⟩

/-- **The cross pairing is killed by the abelianization exponent of the first factor.** -/
theorem piece_commutator_pow_eq_one (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center E) (hB : Function.Bijective fun b => (pB₁ b, pB₂ b))
    {n : ℕ} (he : ∀ b : B₁, b ^ n ∈ commutator B₁)
    {q₁ q₂ : E × B} (h₁ : q₁ ∈ piece π r pB₂) (h₂ : q₂ ∈ piece π r pB₁) :
    ⁅q₁.1, q₂.1⁆ ^ n = 1 := by
  set f := pB₁.comp ((MonoidHom.snd E B).comp (piece π r pB₂).subtype)
  set ψ := pieceCommHom π r pB₁ pB₂ hc hB.1 h₂
  let y : ↥(piece π r pB₂) := ⟨q₁, h₁⟩
  have hmap : (commutator ↥(piece π r pB₂)).map f = commutator B₁ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr
      (piece_proj_surjective π r pB₁ pB₂ hπ hB.2), commutator_def]
  obtain ⟨w, hw, hfw⟩ : f (y ^ n) ∈ (commutator ↥(piece π r pB₂)).map f := by
    rw [hmap, map_pow]; exact he _
  set v := y ^ n * w⁻¹
  have hv2 : ((v : E × B)).2 = 1 := by
    apply hB.1
    have hf : f v = 1 := by simp [v, hfw]
    have hp : pB₂ (v : E × B).2 = 1 := (mem_piece.mp v.2).2
    simp only [Prod.mk.injEq, map_one]
    exact ⟨hf, hp⟩
  have hv1 : (v : E × B).1 ∈ Subgroup.center E := by
    apply hc
    rw [MonoidHom.mem_ker, (mem_piece.mp v.2).1, hv2, map_one]
  have hψv : ψ v = 1 := by
    apply Subtype.ext
    change ⁅(v : E × B).1, q₂.1⁆ = 1
    exact commutatorElement_eq_one_iff_commute.mpr
      (Subgroup.mem_center_iff.mp hv1 _).symm
  have hψw : ψ w = 1 := pieceCommHom_commutator π r pB₁ pB₂ hc hB.1 h₂ hw
  have hyn : y ^ n = v * w := by simp [v]
  have : ψ y ^ n = 1 := by rw [← map_pow, hyn, map_mul, hψv, hψw, one_mul]
  exact congrArg Subtype.val this

theorem bijective_swap {X Y₁ Y₂ : Type*} {f₁ : X → Y₁} {f₂ : X → Y₂}
    (h : Function.Bijective fun x => (f₁ x, f₂ x)) :
    Function.Bijective fun x => (f₂ x, f₁ x) :=
  (Equiv.prodComm Y₁ Y₂).bijective.comp h

/-- **Complementary pieces commute** (coprime abelianization exponents). -/
theorem piece_commute (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center E) (hB : Function.Bijective fun b => (pB₁ b, pB₂ b))
    {n₁ n₂ : ℕ} (hn : n₁.Coprime n₂)
    (he₁ : ∀ b : B₁, b ^ n₁ ∈ commutator B₁) (he₂ : ∀ b : B₂, b ^ n₂ ∈ commutator B₂)
    {q₁ q₂ : E × B} (h₁ : q₁ ∈ piece π r pB₂) (h₂ : q₂ ∈ piece π r pB₁) :
    Commute q₁ q₂ := by
  have k₁ := piece_commutator_pow_eq_one π r pB₁ pB₂ hπ hc hB he₁ h₁ h₂
  have k₂ := piece_commutator_pow_eq_one π r pB₂ pB₁ hπ hc (bijective_swap hB) he₂ h₂ h₁
  rw [← commutatorElement_inv, inv_pow, inv_eq_one] at k₂
  have hfst : ⁅q₁.1, q₂.1⁆ = 1 := by
    have := pow_gcd_eq_one.mpr ⟨k₁, k₂⟩
    rwa [Nat.Coprime.gcd_eq_one hn, pow_one] at this
  have hsnd := piece_snd_commutator π r pB₁ pB₂ hB.1 h₁ h₂
  have := commutatorElement_eq_one_iff_commute.mp (show ⁅q₁, q₂⁆ = 1 from
    Prod.ext (by simpa using hfst) (by simpa using hsnd))
  exact this

/-- Every element of the pullback is a product of complementary pieces. -/
theorem pullback_decomp (hπ : Function.Surjective π)
    (hB : Function.Surjective fun b => (pB₁ b, pB₂ b)) {p : E × B}
    (hp : p ∈ pullback π r) :
    ∃ q₁ ∈ piece π r pB₂, ∃ q₂ ∈ piece π r pB₁, p = q₁ * q₂ := by
  obtain ⟨b₁, hb₁⟩ := hB (pB₁ p.2, 1)
  simp only [Prod.mk.injEq] at hb₁
  obtain ⟨e₁, he₁⟩ := hπ (r b₁)
  refine ⟨(e₁, b₁), mem_piece.mpr ⟨he₁, hb₁.2⟩, (e₁⁻¹ * p.1, b₁⁻¹ * p.2),
    mem_piece.mpr ⟨?_, ?_⟩, ?_⟩
  · simp [map_mul, map_inv, he₁, mem_pullback.mp hp]
  · simp [map_mul, map_inv, hb₁.1]
  · ext <;> simp

/-- The derived subgroup of the pullback splits along the pieces. -/
theorem pullback_commutator_decomp (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center E) (hB : Function.Bijective fun b => (pB₁ b, pB₂ b))
    {n₁ n₂ : ℕ} (hn : n₁.Coprime n₂)
    (he₁ : ∀ b : B₁, b ^ n₁ ∈ commutator B₁) (he₂ : ∀ b : B₂, b ^ n₂ ∈ commutator B₂)
    {g : E × B} (hg : g ∈ ⁅pullback π r, pullback π r⁆) :
    ∃ a ∈ ⁅piece π r pB₂, piece π r pB₂⁆, ∃ c ∈ ⁅piece π r pB₁, piece π r pB₁⁆, g = a * c := by
  have hcomm : ∀ {a c : E × B}, a ∈ piece π r pB₂ → c ∈ piece π r pB₁ → Commute a c :=
    fun ha hc' => piece_commute π r pB₁ pB₂ hπ hc hB hn he₁ he₂ ha hc'
  have s₁ := (piece π r pB₂).commutator_le_self
  have s₂ := (piece π r pB₁).commutator_le_self
  rw [Subgroup.commutator_def] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨p, hp, p', hp', rfl⟩ := hx
    obtain ⟨a, ha, c, hc', rfl⟩ := pullback_decomp π r pB₁ pB₂ hπ hB.2 hp
    obtain ⟨b, hb, d, hd, rfl⟩ := pullback_decomp π r pB₁ pB₂ hπ hB.2 hp'
    refine ⟨⁅a, b⁆, Subgroup.commutator_mem_commutator ha hb, ⁅c, d⁆,
      Subgroup.commutator_mem_commutator hc' hd, ?_⟩
    exact commutator_mul_mul_of_commute (hcomm ha hc') (hcomm ha hd) (hcomm hb hc')
      (hcomm hb hd)
  | one => exact ⟨1, one_mem _, 1, one_mem _, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, c, hc', rfl⟩ := hx
    obtain ⟨a', ha', c', hc'', rfl⟩ := hy
    refine ⟨a * a', mul_mem ha ha', c * c', mul_mem hc' hc'', ?_⟩
    exact ((hcomm (s₁ ha') (s₂ hc')).symm.mul_mul_mul_comm a c')
  | inv x _ hx =>
    obtain ⟨a, ha, c, hc', rfl⟩ := hx
    refine ⟨a⁻¹, inv_mem ha, c⁻¹, inv_mem hc', ?_⟩
    rw [mul_inv_rev]
    exact ((hcomm (s₁ ha) (s₂ hc')).inv_inv).symm.eq

variable (pA₁ : A →* A₁) (pA₂ : A →* A₂) (r₁ : B₁ →* A₁) (r₂ : B₂ →* A₂)

/-- Inflation for a factor controls the commutators of the corresponding piece. -/
theorem piece_inflation (hπ : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E)
    (hA : Function.Bijective fun a => (pA₁ a, pA₂ a))
    (h₁ : r₁.comp pB₁ = pA₁.comp r) (h₂ : r₂.comp pB₂ = pA₂.comp r)
    (i₁ : InflationTrivial r₁) {g : E × B}
    (hg : g ∈ ⁅piece π r pB₂, piece π r pB₂⁆) (hg1 : pB₁ g.2 = 1) : g.1 = 1 := by
  set E₁ : Subgroup E := (pA₂.comp π).ker
  set Q := piece π r pB₂
  let π₁ : ↥E₁ →* A₁ := (pA₁.comp π).comp E₁.subtype
  have hπ₁ : Function.Surjective π₁ := by
    intro a₁
    obtain ⟨a, ha⟩ := hA.2 (a₁, 1)
    simp only [Prod.mk.injEq] at ha
    obtain ⟨e, rfl⟩ := hπ a
    exact ⟨⟨e, by simp [E₁, ha.2]⟩, by simp [π₁, ha.1]⟩
  have hc₁ : π₁.ker ≤ Subgroup.center ↥E₁ := by
    intro y hy
    have hy1 : pA₁ (π y) = 1 := hy
    have hy2 : pA₂ (π y) = 1 := y.2
    have hπy : π y = 1 := hA.1 (by simp [hy1, hy2])
    have hcen := hc (show (y : E) ∈ π.ker from hπy)
    rw [Subgroup.mem_center_iff] at hcen ⊢
    intro z; exact Subtype.ext (hcen z)
  have hQE : ∀ q : ↥Q, (q : E × B).1 ∈ E₁ := by
    intro q
    change pA₂ (π (q : E × B).1) = 1
    rw [(mem_piece.mp q.2).1, ← MonoidHom.comp_apply pA₂ r, ← h₂, MonoidHom.comp_apply,
      (mem_piece.mp q.2).2, map_one]
  let α₁ : ↥Q →* ↥E₁ :=
    ((MonoidHom.fst E B).comp Q.subtype).codRestrict E₁ hQE
  let β₁ : ↥Q →* B₁ := pB₁.comp ((MonoidHom.snd E B).comp Q.subtype)
  have hcompat : π₁.comp α₁ = r₁.comp β₁ := by
    ext q
    simp only [π₁, α₁, β₁, MonoidHom.comp_apply, Subgroup.coe_subtype,
      MonoidHom.codRestrict_apply, MonoidHom.coe_fst, MonoidHom.coe_snd]
    rw [(mem_piece.mp q.2).1, ← MonoidHom.comp_apply pA₁ r, ← h₁, MonoidHom.comp_apply]
  rw [← Subgroup.map_subtype_commutator] at hg
  obtain ⟨y, hy, rfl⟩ := hg
  have := i₁ (↥E₁) π₁ hπ₁ hc₁ (↥Q) α₁ β₁ hcompat y hy hg1
  exact congrArg Subtype.val this

/-- **Inflation vanishing over a split product with coprime abelianization exponents.** -/
theorem inflationTrivial_of_split
    (hA : Function.Bijective fun a => (pA₁ a, pA₂ a))
    (hB : Function.Bijective fun b => (pB₁ b, pB₂ b))
    (h₁ : r₁.comp pB₁ = pA₁.comp r) (h₂ : r₂.comp pB₂ = pA₂.comp r)
    {n₁ n₂ : ℕ} (hn : n₁.Coprime n₂)
    (he₁ : ∀ b : B₁, b ^ n₁ ∈ commutator B₁) (he₂ : ∀ b : B₂, b ^ n₂ ∈ commutator B₂)
    (i₁ : InflationTrivial r₁) (i₂ : InflationTrivial r₂) : InflationTrivial r := by
  intro E _ π hπ hc F _ α β hαβ x hx hβx
  let φ : F →* E × B := α.prod β
  have hrange : φ.range ≤ pullback π r := by
    rintro _ ⟨f, rfl⟩
    exact mem_pullback.mpr (by simpa [φ] using congrArg (fun h => h f) hαβ)
  have hφx : φ x ∈ ⁅pullback π r, pullback π r⁆ := by
    have : (commutator F).map φ ≤ ⁅pullback π r, pullback π r⁆ := by
      rw [map_commutator_eq]; exact Subgroup.commutator_mono hrange hrange
    exact this ⟨x, hx, rfl⟩
  obtain ⟨a, ha, c, hc', hac⟩ :=
    pullback_commutator_decomp π r pB₁ pB₂ hπ hc hB hn he₁ he₂ hφx
  have hsnd : a.2 * c.2 = 1 := by
    have := congrArg Prod.snd hac
    simpa [φ, hβx] using this.symm
  have ha2 : pB₂ a.2 = 1 := (mem_piece.mp ((piece π r pB₂).commutator_le_self ha)).2
  have hc2 : pB₁ c.2 = 1 := (mem_piece.mp ((piece π r pB₁).commutator_le_self hc')).2
  have hca : c.2 = a.2⁻¹ := eq_inv_of_mul_eq_one_right hsnd
  have ha1 : pB₁ a.2 = 1 := by
    have := congrArg pB₁ hca; rw [hc2, map_inv] at this
    exact (inv_eq_one.mp this.symm)
  have hc1 : pB₂ c.2 = 1 := by rw [hca, map_inv, ha2, inv_one]
  have hA1 := piece_inflation π r pB₁ pB₂ pA₁ pA₂ r₁ r₂ hπ hc hA h₁ h₂ i₁ ha ha1
  have hC1 := piece_inflation π r pB₂ pB₁ pA₂ pA₁ r₂ r₁ hπ hc (bijective_swap hA) h₂ h₁ i₂
    hc' hc1
  have := congrArg Prod.fst hac
  simp only [φ, MonoidHom.prod_apply, Prod.fst_mul] at this
  rw [this, hA1, hC1, one_mul]

end Split

end VOA.Huang.DLNBeyl
