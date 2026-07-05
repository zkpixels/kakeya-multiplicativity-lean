import N16B
import P33BK00
import P34BK01
import P35BK02
import P36BK03
import P37BK04
import P38BK05
import P39BK06
import P40BK07
import P41BK08
import P42BK09
import P43BK10
import P44BK11
import P45BK12
import P46BK13
import P47BK14
import P48BK15

namespace KakeyaMultiplicativity

/-- Range combiner: all 65536 masks from the sixteen slices. -/
theorem fc2n_all :
    ∀ m : ℕ, m < 65536 →
      countN2 m * 6 ≤ popcountN2 m * 15 := by
  intro m hm
  rcases (by omega : m < 4096 ∨ (4096 ≤ m ∧ m < 8192) ∨ (8192 ≤ m ∧ m < 12288) ∨ (12288 ≤ m ∧ m < 16384) ∨ (16384 ≤ m ∧ m < 20480) ∨ (20480 ≤ m ∧ m < 24576) ∨ (24576 ≤ m ∧ m < 28672) ∨ (28672 ≤ m ∧ m < 32768) ∨ (32768 ≤ m ∧ m < 36864) ∨ (36864 ≤ m ∧ m < 40960) ∨ (40960 ≤ m ∧ m < 45056) ∨ (45056 ≤ m ∧ m < 49152) ∨ (49152 ≤ m ∧ m < 53248) ∨ (53248 ≤ m ∧ m < 57344) ∨ (57344 ≤ m ∧ m < 61440) ∨ (61440 ≤ m ∧ m < 65536)) with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · have := fc2n_s00 ⟨m, by omega⟩
    simpa using this
  · have := fc2n_s01 ⟨m - 4096, by omega⟩
    rw [show 4096 + (m - 4096) = m from by omega] at this
    exact this
  · have := fc2n_s02 ⟨m - 8192, by omega⟩
    rw [show 8192 + (m - 8192) = m from by omega] at this
    exact this
  · have := fc2n_s03 ⟨m - 12288, by omega⟩
    rw [show 12288 + (m - 12288) = m from by omega] at this
    exact this
  · have := fc2n_s04 ⟨m - 16384, by omega⟩
    rw [show 16384 + (m - 16384) = m from by omega] at this
    exact this
  · have := fc2n_s05 ⟨m - 20480, by omega⟩
    rw [show 20480 + (m - 20480) = m from by omega] at this
    exact this
  · have := fc2n_s06 ⟨m - 24576, by omega⟩
    rw [show 24576 + (m - 24576) = m from by omega] at this
    exact this
  · have := fc2n_s07 ⟨m - 28672, by omega⟩
    rw [show 28672 + (m - 28672) = m from by omega] at this
    exact this
  · have := fc2n_s08 ⟨m - 32768, by omega⟩
    rw [show 32768 + (m - 32768) = m from by omega] at this
    exact this
  · have := fc2n_s09 ⟨m - 36864, by omega⟩
    rw [show 36864 + (m - 36864) = m from by omega] at this
    exact this
  · have := fc2n_s10 ⟨m - 40960, by omega⟩
    rw [show 40960 + (m - 40960) = m from by omega] at this
    exact this
  · have := fc2n_s11 ⟨m - 45056, by omega⟩
    rw [show 45056 + (m - 45056) = m from by omega] at this
    exact this
  · have := fc2n_s12 ⟨m - 49152, by omega⟩
    rw [show 49152 + (m - 49152) = m from by omega] at this
    exact this
  · have := fc2n_s13 ⟨m - 53248, by omega⟩
    rw [show 53248 + (m - 53248) = m from by omega] at this
    exact this
  · have := fc2n_s14 ⟨m - 57344, by omega⟩
    rw [show 57344 + (m - 57344) = m from by omega] at this
    exact this
  · have := fc2n_s15 ⟨m - 61440, by omega⟩
    rw [show 61440 + (m - 61440) = m from by omega] at this
    exact this

/-- The certificate inequality, original statement, via the mask
bridge: encode `T` as a bitmask, count/popcount transport, then the
range-combined bitmask theorem. -/
theorem fc24_idx :
    ∀ T : Finset (Fin 16),
      (nzIdx2.filter fun d => carriesIdx2 T d).card * 6 ≤
        T.card * 15 := by
  intro T
  have hspec : ∀ p : Fin 16,
      (maskOfList T.toList).testBit p.val = true ↔ p ∈ T :=
    fun p => (testBit_maskOfList T.toList p).trans (Finset.mem_toList)
  rw [countN2_eq hspec, popcountN2_eq hspec]
  exact fc2n_all _ (by simpa using maskOfList_lt T.toList)


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



end KakeyaMultiplicativity
