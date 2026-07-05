/-! ## Two sixteen-point certificates: the first prime power and the
first dimension four

`FC(4,2,10)` — the certificate at the true price for the PRIME-POWER
modulus `ℤ/4` — and `FC(2,4,6)` — the certificate at the true price
for `𝔽₂⁴`.  Both spaces have sixteen points, so both certificates are
full-powerset kernel enumerations (`2¹⁶` subsets), run over `Fin 16`
index encodings for evaluation speed and transported back through
one-time structural bridges, exactly as in the `𝔽₃³` endgame.

The transfer theorem never required the small factor to be prime, so
the first certificate yields `K(4M,2) = 10·K(M,2)` for every odd `M` —
exact multiplicativity beyond squarefree moduli — and the second
yields `K(2M,4) = 6·K(M,4)`, the first exact family in dimension
four. -/

section PrimePowerCells

/-! ### The `(ℤ/4)²` index world -/

/-- Base-4 digit encoding of a `(ZMod 4)²` point. -/
def toIdx4 (p : ResiduePoint 4 2) : Fin 16 :=
  ⟨(p 0).val + 4 * (p 1).val, by
    have h0 : (p 0).val < 4 := ZMod.val_lt (p 0)
    have h1 : (p 1).val < 4 := ZMod.val_lt (p 1)
    omega⟩

def ofIdx4 (k : Fin 16) : ResiduePoint 4 2 :=
  ![((k.val % 4 : ℕ) : ZMod 4), ((k.val / 4 : ℕ) : ZMod 4)]

theorem ofIdx4_toIdx4 : ∀ p : ResiduePoint 4 2, ofIdx4 (toIdx4 p) = p := by
  decide

theorem toIdx4_ofIdx4 : ∀ k : Fin 16, toIdx4 (ofIdx4 k) = k := by decide

theorem toIdx4_injective : Function.Injective toIdx4 := by
  intro p q h
  rw [← ofIdx4_toIdx4 p, ← ofIdx4_toIdx4 q, h]

theorem mem_image_toIdx4 {S : Finset (ResiduePoint 4 2)}
    {p : ResiduePoint 4 2} :
    toIdx4 p ∈ S.image toIdx4 ↔ p ∈ S := by
  constructor
  · intro h
    obtain ⟨r, hr, he⟩ := Finset.mem_image.mp h
    rw [← toIdx4_injective he]
    exact hr
  · exact Finset.mem_image_of_mem _

/-- Index addition: digitwise mod 4. -/
def addIdx4 (a b : Fin 16) : Fin 16 :=
  ⟨(a.val % 4 + b.val % 4) % 4 + ((a.val / 4 + b.val / 4) % 4) * 4, by
    omega⟩

theorem toIdx4_add :
    ∀ p r : ResiduePoint 4 2,
      toIdx4 (p + r) = addIdx4 (toIdx4 p) (toIdx4 r) := by
  decide

/-- Anchored carrier check over `ℤ/4`: the three nonzero parameters. -/
def carriesIdx4 (S : Finset (Fin 16)) (d : Fin 16) : Prop :=
  ∃ p ∈ S, addIdx4 p d ∈ S ∧ addIdx4 (addIdx4 p d) d ∈ S ∧
    addIdx4 (addIdx4 (addIdx4 p d) d) d ∈ S

instance (S : Finset (Fin 16)) (d : Fin 16) :
    Decidable (carriesIdx4 S d) :=
  inferInstanceAs (Decidable (∃ p ∈ S, _ ∧ _ ∧ _))

/-- Parameter case split over `ZMod 4`. -/
theorem zmod4_cases : ∀ t : ZMod 4, t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by
  decide

/-- Successive line points over `ℤ/4` are successive additions. -/
theorem residueLine_add_step (p b : ResiduePoint 4 2) (t : ZMod 4) :
    residueLine p b (t + 1) = residueLine p b t + b := by
  funext i
  simp only [residueLine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem carriesIdx4_iff {S : Finset (ResiduePoint 4 2)}
    {b : ResiduePoint 4 2} :
    carriesIdx4 (S.image toIdx4) (toIdx4 b) ↔ CarriesLine S b := by
  have hline : ∀ p : ResiduePoint 4 2,
      residueLine p b 1 = p + b ∧
      residueLine p b 2 = p + b + b ∧
      residueLine p b 3 = p + b + b + b := by
    intro p
    refine ⟨?_, ?_, ?_⟩ <;>
      · funext i
        simp only [residueLine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
  constructor
  · rintro ⟨pi, hpi, h1, h2, h3⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hpi
    rw [← toIdx4_add] at h1
    rw [← toIdx4_add, ← toIdx4_add] at h2
    rw [← toIdx4_add, ← toIdx4_add, ← toIdx4_add] at h3
    refine ⟨p, fun t => ?_⟩
    obtain ⟨hl1, hl2, hl3⟩ := hline p
    rcases zmod4_cases t with rfl | rfl | rfl | rfl
    · rw [residueLine_zero]
      exact hp
    · rw [hl1]
      exact mem_image_toIdx4.mp h1
    · rw [hl2]
      exact mem_image_toIdx4.mp h2
    · rw [hl3]
      exact mem_image_toIdx4.mp h3
  · rintro ⟨a, ha⟩
    obtain ⟨hl1, hl2, hl3⟩ := hline a
    refine ⟨toIdx4 a, mem_image_toIdx4.mpr (by
        rw [← residueLine_zero a b]; exact ha 0), ?_, ?_, ?_⟩
    · rw [← toIdx4_add, ← hl1]
      exact mem_image_toIdx4.mpr (ha 1)
    · rw [← toIdx4_add, ← toIdx4_add, ← hl2]
      exact mem_image_toIdx4.mpr (ha 2)
    · rw [← toIdx4_add, ← toIdx4_add, ← toIdx4_add, ← hl3]
      exact mem_image_toIdx4.mpr (ha 3)

/-- The nonzero index menu (image of the direction menu). -/
def nzIdx4 : Finset (Fin 16) :=
  {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}

theorem nzIdx4_eq : (nonzeroDirections 4 2).image toIdx4 = nzIdx4 := by
  decide

/-- Carried-menu count, transported. -/
theorem carriedIdx4_image (S : Finset (ResiduePoint 4 2)) :
    (nzIdx4.filter fun d => carriesIdx4 (S.image toIdx4) d).card =
      ((nonzeroDirections 4 2).filter fun b => CarriesLine S b).card := by
  rw [← nzIdx4_eq, Finset.filter_image,
    Finset.card_image_of_injective _ toIdx4_injective]
  exact congrArg Finset.card (Finset.filter_congr fun b _ => by
    rw [carriesIdx4_iff])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- THE PRIME-POWER KERNEL CHECK: the `(ℤ/4)²` certificate at price
`10`, enumerated over all `2¹⁶` index windows. -/
theorem fc42_idx :
    ∀ T : Finset (Fin 16),
      (nzIdx4.filter fun d => carriesIdx4 T d).card * 10 ≤
        T.card * 15 := by
  decide +kernel

/-- `FC(4,2,10)`: the fractional cost certificate for the prime power
`ℤ/4` at its true price. -/
theorem fractionalCostAt_four_two :
    FractionalCostAt 4 2 (nonzeroDirections 4 2) 10 := by
  intro S
  have h := fc42_idx (S.image toIdx4)
  rw [carriedIdx4_image,
    Finset.card_image_of_injective _ toIdx4_injective] at h
  have hmenu : (nonzeroDirections 4 2).card = 15 := by decide
  rw [hmenu]
  exact h

/-- Lower half of the exact value: the certificate self-applied. -/
theorem ten_le_card_of_fourTwo_isKakeyaSet
    {K : Finset (ResiduePoint 4 2)} (hK : IsKakeyaSet K) :
    10 ≤ K.card := by
  have h := fractionalCostAt_four_two K
  have hall : (nonzeroDirections 4 2).filter
      (fun b => CarriesLine K b) = nonzeroDirections 4 2 :=
    Finset.filter_true_of_mem fun b _ =>
      isKakeyaSet_iff_forall_carriesLine.mp hK b
  have hmenu : (nonzeroDirections 4 2).card = 15 := by decide
  rw [hall, hmenu] at h
  omega

/-- The ten-point witness (found by search, kernel re-verified):
a full column plus a discrete tangent tail. -/
def fourTwoWitnessIdx : Finset (Fin 16) :=
  {0, 4, 8, 12, 1, 13, 2, 10, 3, 7}

def fourTwoWitness : Finset (ResiduePoint 4 2) :=
  fourTwoWitnessIdx.image ofIdx4

theorem ofIdx4_injective : Function.Injective ofIdx4 := by
  intro a b h
  rw [← toIdx4_ofIdx4 a, ← toIdx4_ofIdx4 b, h]

theorem fourTwoWitness_image :
    fourTwoWitness.image toIdx4 = fourTwoWitnessIdx := by
  unfold fourTwoWitness
  rw [Finset.image_image,
    show (toIdx4 ∘ ofIdx4) = id from funext toIdx4_ofIdx4,
    Finset.image_id]

theorem fourTwoWitness_card : fourTwoWitness.card = 10 := by
  unfold fourTwoWitness
  rw [Finset.card_image_of_injective _ ofIdx4_injective]
  decide

theorem fourTwoWitness_isKakeyaSet : IsKakeyaSet fourTwoWitness := by
  intro b
  by_cases hb : b = 0
  · subst hb
    refine ⟨ofIdx4 0, fun t => ?_⟩
    have hline : residueLine (ofIdx4 0) 0 t = ofIdx4 0 := by
      funext i
      simp only [residueLine, Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
        smul_eq_mul, mul_zero, add_zero]
    rw [hline]
    exact Finset.mem_image_of_mem _ (by decide)
  · have hidx : ∀ d ∈ nzIdx4, carriesIdx4 fourTwoWitnessIdx d := by
      decide
    have hmem : toIdx4 b ∈ nzIdx4 := by
      rw [← nzIdx4_eq]
      refine Finset.mem_image_of_mem _ ?_
      simp only [nonzeroDirections, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact hb
    have h1 : carriesIdx4 (fourTwoWitness.image toIdx4) (toIdx4 b) := by
      rw [fourTwoWitness_image]
      exact hidx _ hmem
    exact carriesIdx4_iff.mp h1

/-- THE FIRST PRIME-POWER EXACT VALUE: `K(4,2) = 10`.  Note the
curiosity: this equals the Blokhuis–Mazzocca minimum for the FIELD
`𝔽₄` — the ring and the field of order four share their plane Kakeya
minimum. -/
theorem minKakeyaSize_four_two : minKakeyaSize 4 2 = 10 := by
  refine le_antisymm ?_ ?_
  · have h := minKakeyaSize_le_card fourTwoWitness_isKakeyaSet
    rwa [fourTwoWitness_card] at h
  · obtain ⟨K, hK, hcard⟩ := exists_minKakeyaSize_witness 4 2
    rw [← hcard]
    exact ten_le_card_of_fourTwo_isKakeyaSet hK

theorem nonzeroDirections_four_two_nonempty :
    (nonzeroDirections 4 2).Nonempty := by decide

/-- BEYOND SQUAREFREE: exact multiplicativity at the prime-power
factor `4`, for every odd co-factor. -/
theorem minKakeyaSize_four_mul_dim_two (M : ℕ) [NeZero M]
    (h : Nat.Coprime 4 M) :
    minKakeyaSize (4 * M) 2 = 10 * minKakeyaSize M 2 := by
  have hfc : FractionalCostAt 4 2 (nonzeroDirections 4 2)
      (minKakeyaSize 4 2) := by
    rw [minKakeyaSize_four_two]
    exact fractionalCostAt_four_two
  have heq := minKakeyaSize_mul_eq_of_fractionalCostAt h
    nonzeroDirections_four_two_nonempty hfc
  rw [heq, minKakeyaSize_four_two]

/-- A fully formal beyond-squarefree value: `K(12,2) = 70`. -/
theorem minKakeyaSize_twelve_two : minKakeyaSize 12 2 = 70 := by
  have h := minKakeyaSize_four_mul_dim_two 3 (by decide)
  rw [show (4 * 3 : ℕ) = 12 from rfl, minKakeyaSize_three_two] at h
  omega

/-! ### The `𝔽₂⁴` index world -/

/-- Base-2 digit encoding of an `𝔽₂⁴` point. -/
def toIdx2 (p : ResiduePoint 2 4) : Fin 16 :=
  ⟨(p 0).val + 2 * (p 1).val + 4 * (p 2).val + 8 * (p 3).val, by
    have h0 : (p 0).val < 2 := ZMod.val_lt (p 0)
    have h1 : (p 1).val < 2 := ZMod.val_lt (p 1)
    have h2 : (p 2).val < 2 := ZMod.val_lt (p 2)
    have h3 : (p 3).val < 2 := ZMod.val_lt (p 3)
    omega⟩

def ofIdx2 (k : Fin 16) : ResiduePoint 2 4 :=
  ![((k.val % 2 : ℕ) : ZMod 2), ((k.val / 2 % 2 : ℕ) : ZMod 2),
    ((k.val / 4 % 2 : ℕ) : ZMod 2), ((k.val / 8 : ℕ) : ZMod 2)]

theorem ofIdx2_toIdx2 : ∀ p : ResiduePoint 2 4, ofIdx2 (toIdx2 p) = p := by
  decide

theorem toIdx2_ofIdx2 : ∀ k : Fin 16, toIdx2 (ofIdx2 k) = k := by decide

theorem toIdx2_injective : Function.Injective toIdx2 := by
  intro p q h
  rw [← ofIdx2_toIdx2 p, ← ofIdx2_toIdx2 q, h]

theorem mem_image_toIdx2 {S : Finset (ResiduePoint 2 4)}
    {p : ResiduePoint 2 4} :
    toIdx2 p ∈ S.image toIdx2 ↔ p ∈ S := by
  constructor
  · intro h
    obtain ⟨r, hr, he⟩ := Finset.mem_image.mp h
    rw [← toIdx2_injective he]
    exact hr
  · exact Finset.mem_image_of_mem _

/-- Index addition: digitwise mod 2. -/
def addIdx2 (a b : Fin 16) : Fin 16 :=
  ⟨(a.val % 2 + b.val % 2) % 2 +
    ((a.val / 2 % 2 + b.val / 2 % 2) % 2) * 2 +
    ((a.val / 4 % 2 + b.val / 4 % 2) % 2) * 4 +
    ((a.val / 8 + b.val / 8) % 2) * 8, by omega⟩

theorem toIdx2_add :
    ∀ p r : ResiduePoint 2 4,
      toIdx2 (p + r) = addIdx2 (toIdx2 p) (toIdx2 r) := by
  decide

/-- Anchored carrier check over `𝔽₂`: one nonzero parameter. -/
def carriesIdx2 (S : Finset (Fin 16)) (d : Fin 16) : Prop :=
  ∃ p ∈ S, addIdx2 p d ∈ S

instance (S : Finset (Fin 16)) (d : Fin 16) :
    Decidable (carriesIdx2 S d) :=
  inferInstanceAs (Decidable (∃ p ∈ S, _))

theorem zmod2_cases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide

theorem carriesIdx2_iff {S : Finset (ResiduePoint 2 4)}
    {b : ResiduePoint 2 4} :
    carriesIdx2 (S.image toIdx2) (toIdx2 b) ↔ CarriesLine S b := by
  have hline : ∀ p : ResiduePoint 2 4, residueLine p b 1 = p + b := by
    intro p
    funext i
    simp only [residueLine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  constructor
  · rintro ⟨pi, hpi, h1⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hpi
    rw [← toIdx2_add] at h1
    refine ⟨p, fun t => ?_⟩
    rcases zmod2_cases t with rfl | rfl
    · rw [residueLine_zero]
      exact hp
    · rw [hline]
      exact mem_image_toIdx2.mp h1
  · rintro ⟨a, ha⟩
    refine ⟨toIdx2 a, mem_image_toIdx2.mpr (by
        rw [← residueLine_zero a b]; exact ha 0), ?_⟩
    rw [← toIdx2_add, ← hline]
    exact mem_image_toIdx2.mpr (ha 1)

def nzIdx2 : Finset (Fin 16) :=
  {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}

theorem nzIdx2_eq : (nonzeroDirections 2 4).image toIdx2 = nzIdx2 := by
  decide

theorem carriedIdx2_image (S : Finset (ResiduePoint 2 4)) :
    (nzIdx2.filter fun d => carriesIdx2 (S.image toIdx2) d).card =
      ((nonzeroDirections 2 4).filter fun b => CarriesLine S b).card := by
  rw [← nzIdx2_eq, Finset.filter_image,
    Finset.card_image_of_injective _ toIdx2_injective]
  exact congrArg Finset.card (Finset.filter_congr fun b _ => by
    rw [carriesIdx2_iff])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- THE DIMENSION-FOUR KERNEL CHECK: the `𝔽₂⁴` certificate at price
`6`, over all `2¹⁶` index windows. -/
theorem fc24_idx :
    ∀ T : Finset (Fin 16),
      (nzIdx2.filter fun d => carriesIdx2 T d).card * 6 ≤
        T.card * 15 := by
  decide +kernel

/-- `FC(2,4,6)`: the certificate at the true price in dimension four —
the even-`n` half of the mod-2 parity pattern, now a theorem at
`n = 4`. -/
theorem fractionalCostAt_two_four :
    FractionalCostAt 2 4 (nonzeroDirections 2 4) 6 := by
  intro S
  have h := fc24_idx (S.image toIdx2)
  rw [carriedIdx2_image,
    Finset.card_image_of_injective _ toIdx2_injective] at h
  have hmenu : (nonzeroDirections 2 4).card = 15 := by decide
  rw [hmenu]
  exact h

theorem twoFour_six_le_card
    {K : Finset (ResiduePoint 2 4)} (hK : IsKakeyaSet K) :
    6 ≤ K.card := by
  have h := fractionalCostAt_two_four K
  have hall : (nonzeroDirections 2 4).filter
      (fun b => CarriesLine K b) = nonzeroDirections 2 4 :=
    Finset.filter_true_of_mem fun b _ =>
      isKakeyaSet_iff_forall_carriesLine.mp hK b
  have hmenu : (nonzeroDirections 2 4).card = 15 := by decide
  rw [hall, hmenu] at h
  omega

/-- The six-point witness (a perfect difference cover of `𝔽₂⁴`). -/
def twoFourWitnessIdx : Finset (Fin 16) := {8, 4, 2, 6, 1, 9}

def twoFourWitness : Finset (ResiduePoint 2 4) :=
  twoFourWitnessIdx.image ofIdx2

theorem ofIdx2_injective : Function.Injective ofIdx2 := by
  intro a b h
  rw [← toIdx2_ofIdx2 a, ← toIdx2_ofIdx2 b, h]

theorem twoFourWitness_image :
    twoFourWitness.image toIdx2 = twoFourWitnessIdx := by
  unfold twoFourWitness
  rw [Finset.image_image,
    show (toIdx2 ∘ ofIdx2) = id from funext toIdx2_ofIdx2,
    Finset.image_id]

theorem twoFourWitness_card : twoFourWitness.card = 6 := by
  unfold twoFourWitness
  rw [Finset.card_image_of_injective _ ofIdx2_injective]
  decide

theorem twoFourWitness_isKakeyaSet : IsKakeyaSet twoFourWitness := by
  intro b
  by_cases hb : b = 0
  · subst hb
    refine ⟨ofIdx2 8, fun t => ?_⟩
    have hline : residueLine (ofIdx2 8) 0 t = ofIdx2 8 := by
      funext i
      simp only [residueLine, Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
        smul_eq_mul, mul_zero, add_zero]
    rw [hline]
    exact Finset.mem_image_of_mem _ (by decide)
  · have hidx : ∀ d ∈ nzIdx2, carriesIdx2 twoFourWitnessIdx d := by
      decide
    have hmem : toIdx2 b ∈ nzIdx2 := by
      rw [← nzIdx2_eq]
      refine Finset.mem_image_of_mem _ ?_
      simp only [nonzeroDirections, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact hb
    have h1 : carriesIdx2 (twoFourWitness.image toIdx2) (toIdx2 b) := by
      rw [twoFourWitness_image]
      exact hidx _ hmem
    exact carriesIdx2_iff.mp h1

/-- The dimension-four exact value `K(2,4) = 6`, self-contained. -/
theorem minKakeyaSize_two_four' : minKakeyaSize 2 4 = 6 := by
  refine le_antisymm ?_ ?_
  · have h := minKakeyaSize_le_card twoFourWitness_isKakeyaSet
    rwa [twoFourWitness_card] at h
  · obtain ⟨K, hK, hcard⟩ := exists_minKakeyaSize_witness 2 4
    rw [← hcard]
    exact twoFour_six_le_card hK

theorem nonzeroDirections_two_four_nonempty :
    (nonzeroDirections 2 4).Nonempty := by decide

/-- THE FIRST DIMENSION-FOUR FAMILY: `K(2M,4) = 6·K(M,4)` for every
odd `M`. -/
theorem minKakeyaSize_two_mul_dim_four (M : ℕ) [NeZero M]
    (h : Nat.Coprime 2 M) :
    minKakeyaSize (2 * M) 4 = 6 * minKakeyaSize M 4 := by
  have hfc : FractionalCostAt 2 4 (nonzeroDirections 2 4)
      (minKakeyaSize 2 4) := by
    rw [minKakeyaSize_two_four']
    exact fractionalCostAt_two_four
  have heq := minKakeyaSize_mul_eq_of_fractionalCostAt h
    nonzeroDirections_two_four_nonempty hfc
  rw [heq, minKakeyaSize_two_four']

end PrimePowerCells
