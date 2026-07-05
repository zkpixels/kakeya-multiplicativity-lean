import N16A
import P14AK00
import P15AK01
import P16AK02
import P17AK03
import P18AK04
import P19AK05
import P20AK06
import P21AK07
import P22AK08
import P23AK09
import P24AK10
import P25AK11
import P26AK12
import P27AK13
import P28AK14
import P29AK15

namespace KakeyaMultiplicativity

/-- Range combiner: all 65536 masks from the sixteen slices. -/
theorem fc4n_all :
    ∀ m : ℕ, m < 65536 →
      countN4 m * 10 ≤ popcountN4 m * 15 := by
  intro m hm
  rcases (by omega : m < 4096 ∨ (4096 ≤ m ∧ m < 8192) ∨ (8192 ≤ m ∧ m < 12288) ∨ (12288 ≤ m ∧ m < 16384) ∨ (16384 ≤ m ∧ m < 20480) ∨ (20480 ≤ m ∧ m < 24576) ∨ (24576 ≤ m ∧ m < 28672) ∨ (28672 ≤ m ∧ m < 32768) ∨ (32768 ≤ m ∧ m < 36864) ∨ (36864 ≤ m ∧ m < 40960) ∨ (40960 ≤ m ∧ m < 45056) ∨ (45056 ≤ m ∧ m < 49152) ∨ (49152 ≤ m ∧ m < 53248) ∨ (53248 ≤ m ∧ m < 57344) ∨ (57344 ≤ m ∧ m < 61440) ∨ (61440 ≤ m ∧ m < 65536)) with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · have := fc4n_s00 ⟨m, by omega⟩
    simpa using this
  · have := fc4n_s01 ⟨m - 4096, by omega⟩
    rw [show 4096 + (m - 4096) = m from by omega] at this
    exact this
  · have := fc4n_s02 ⟨m - 8192, by omega⟩
    rw [show 8192 + (m - 8192) = m from by omega] at this
    exact this
  · have := fc4n_s03 ⟨m - 12288, by omega⟩
    rw [show 12288 + (m - 12288) = m from by omega] at this
    exact this
  · have := fc4n_s04 ⟨m - 16384, by omega⟩
    rw [show 16384 + (m - 16384) = m from by omega] at this
    exact this
  · have := fc4n_s05 ⟨m - 20480, by omega⟩
    rw [show 20480 + (m - 20480) = m from by omega] at this
    exact this
  · have := fc4n_s06 ⟨m - 24576, by omega⟩
    rw [show 24576 + (m - 24576) = m from by omega] at this
    exact this
  · have := fc4n_s07 ⟨m - 28672, by omega⟩
    rw [show 28672 + (m - 28672) = m from by omega] at this
    exact this
  · have := fc4n_s08 ⟨m - 32768, by omega⟩
    rw [show 32768 + (m - 32768) = m from by omega] at this
    exact this
  · have := fc4n_s09 ⟨m - 36864, by omega⟩
    rw [show 36864 + (m - 36864) = m from by omega] at this
    exact this
  · have := fc4n_s10 ⟨m - 40960, by omega⟩
    rw [show 40960 + (m - 40960) = m from by omega] at this
    exact this
  · have := fc4n_s11 ⟨m - 45056, by omega⟩
    rw [show 45056 + (m - 45056) = m from by omega] at this
    exact this
  · have := fc4n_s12 ⟨m - 49152, by omega⟩
    rw [show 49152 + (m - 49152) = m from by omega] at this
    exact this
  · have := fc4n_s13 ⟨m - 53248, by omega⟩
    rw [show 53248 + (m - 53248) = m from by omega] at this
    exact this
  · have := fc4n_s14 ⟨m - 57344, by omega⟩
    rw [show 57344 + (m - 57344) = m from by omega] at this
    exact this
  · have := fc4n_s15 ⟨m - 61440, by omega⟩
    rw [show 61440 + (m - 61440) = m from by omega] at this
    exact this

/-- The certificate inequality, original statement, via the mask
bridge: encode `T` as a bitmask, count/popcount transport, then the
range-combined bitmask theorem. -/
theorem fc42_idx :
    ∀ T : Finset (Fin 16),
      (nzIdx4.filter fun d => carriesIdx4 T d).card * 10 ≤
        T.card * 15 := by
  intro T
  have hspec : ∀ p : Fin 16,
      (maskOfList T.toList).testBit p.val = true ↔ p ∈ T :=
    fun p => (testBit_maskOfList T.toList p).trans (Finset.mem_toList)
  rw [countN4_eq hspec, popcountN4_eq hspec]
  exact fc4n_all _ (by simpa using maskOfList_lt T.toList)


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



end KakeyaMultiplicativity
