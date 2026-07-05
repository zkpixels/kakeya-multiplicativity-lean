import P01Base
import P02Cov
import P03E1
import P04E2
import P05E3
import P06E4
import P07E5
import P08E6
import P09E7
import P10E8

namespace KakeyaMultiplicativity

/-- ENDGAME CLOSER: a window of violating size whose encoding contains
a 9-point normalized core, with the core's kernel-established count
ceilings, cannot exist.  Shared by both normalization cases. -/
private theorem endgame_absurd {S₂ : Finset (ResiduePoint 3 3)}
    {core : Finset (Fin 27)}
    (hcore_sub : core ⊆ S₂.image toIdx)
    (hcore_card : core.card = 9)
    (hbound : ∀ k : ℕ, k ≤ 3 →
      ∀ extras ∈ ((Finset.univ : Finset (Fin 27)) \ core).powersetCard k,
        classCountIdx (core ∪ extras) ≤ 9 + k)
    (hcard9 : 9 ≤ S₂.card) (hcard12 : S₂.card ≤ 12)
    (hviol : S₂.card + 1 ≤ classCount S₂) : False := by
  have hTcard : (S₂.image toIdx).card = S₂.card :=
    Finset.card_image_of_injective _ toIdx_injective
  have hsplit : core ∪ (S₂.image toIdx \ core) = S₂.image toIdx :=
    Finset.union_sdiff_of_subset hcore_sub
  have hex_card : (S₂.image toIdx \ core).card = S₂.card - 9 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hcore_sub, hTcard,
      hcore_card]
  have hex_mem : (S₂.image toIdx \ core) ∈
      ((Finset.univ : Finset (Fin 27)) \ core).powersetCard
        (S₂.card - 9) := by
    rw [Finset.mem_powersetCard]
    exact ⟨fun a ha => Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp ha).2⟩, hex_card⟩
  have hb := hbound (S₂.card - 9) (by omega) _ hex_mem
  rw [hsplit, classCountIdx_image] at hb
  omega

/-! ## The family-count bound -/

/-- THE FAMILY-COUNT BOUND: every subset of `(ZMod 3)³` carries full
lines in at most `|S|` distinct direction families.  This is the whole
content of the price-13 fractional cost certificate. -/
theorem classCount_le_card (S : Finset (ResiduePoint 3 3)) :
    classCount S ≤ S.card := by
  by_contra hlt
  have hviol : S.card + 1 ≤ classCount S := by omega
  have h13 := classCount_le_thirteen S
  -- The counting layer confines a violator to sizes 9–12.
  have hcard9 : 9 ≤ S.card := by
    rcases Nat.lt_or_ge S.card 9 with h8 | h9
    · have := classCount_le_card_of_card_le_eight (S := S) (by omega)
      omega
    · exact h9
  have hcard12 : S.card ≤ 12 := by omega
  -- Pigeonhole: a four-family pencil point.
  obtain ⟨p₀, hp₀, hpen⟩ := exists_pencil_card_ge_four hviol
  -- Stage 1: translate the pencil point to the origin.
  have hS₀card : (S.image (fun v => v + (-p₀))).card = S.card :=
    Finset.card_image_of_injective _ (add_left_injective _)
  have hS₀fam : classCount (S.image (fun v => v + (-p₀))) =
      classCount S := classCount_image_add S _
  have hpen₀ : 4 ≤ (linePencil (S.image (fun v => v + (-p₀))) 0).card :=
    le_trans hpen (Finset.card_le_card fun b hb => linePencil_translate hb)
  generalize hS₀gen : S.image (fun v => v + (-p₀)) = S₀ at hS₀card hS₀fam hpen₀
  have hPreps : linePencil S₀ 0 ⊆ classReps := Finset.filter_subset _ _
  have hPlines : ∀ b ∈ linePencil S₀ 0,
      ∀ t : ZMod 3, residueLine 0 b t ∈ S₀ :=
    fun b hb => (Finset.mem_filter.mp hb).2
  -- Stage 2: case on an independent triple among the pencil lines.
  by_cases hsplit : ∃ x ∈ linePencil S₀ 0, ∃ y ∈ linePencil S₀ 0,
      ∃ z ∈ linePencil S₀ 0, LinearIndependent (ZMod 3) ![z, x, y]
  · -- CASE A: gauge the triple to the axes; one free line remains.
    obtain ⟨x, hx, y, hy, z, hz, htriple⟩ := hsplit
    -- A fourth pencil direction outside the triple.
    have hnotsub : ¬ linePencil S₀ 0 ⊆ {x, y, z} := by
      intro hsub
      have hle := Finset.card_le_card hsub
      have h1 := Finset.card_insert_le x ({y, z} : Finset (ResiduePoint 3 3))
      have h2 := Finset.card_insert_le y ({z} : Finset (ResiduePoint 3 3))
      have h3 : ({z} : Finset (ResiduePoint 3 3)).card = 1 :=
        Finset.card_singleton z
      omega
    obtain ⟨w, hw, hwout⟩ := Finset.not_subset.mp hnotsub
    have hwx : w ≠ x := fun h =>
      hwout (by rw [h]; exact Finset.mem_insert_self _ _)
    have hwy : w ≠ y := fun h => hwout (by
      rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hwz : w ≠ z := fun h => hwout (by
      rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _)))
    -- Gauge to standard position.
    have hS₂card : (S₀.image ⇑(gaugeEquiv htriple)).card = S.card := by
      rw [Finset.card_image_of_injective _ (gaugeEquiv htriple).injective,
        hS₀card]
    have hS₂fam : classCount (S₀.image ⇑(gaugeEquiv htriple)) =
        classCount S := by
      rw [classCount_image_linearEquiv, hS₀fam]
    -- The three axis lines live in the gauged window.
    have hline_x : ∀ t : ZMod 3, residueLine 0 (stdDir 0) t ∈
        S₀.image ⇑(gaugeEquiv htriple) := by
      have h := lineThrough0_image_linearEquiv (gaugeEquiv htriple)
        (hPlines x hx)
      rwa [gaugeEquiv_snd htriple] at h
    have hline_y : ∀ t : ZMod 3, residueLine 0 (stdDir 1) t ∈
        S₀.image ⇑(gaugeEquiv htriple) := by
      have h := lineThrough0_image_linearEquiv (gaugeEquiv htriple)
        (hPlines y hy)
      rwa [gaugeEquiv_trd htriple] at h
    have hline_z : ∀ t : ZMod 3, residueLine 0 (stdDir 2) t ∈
        S₀.image ⇑(gaugeEquiv htriple) := by
      have h := lineThrough0_image_linearEquiv (gaugeEquiv htriple)
        (hPlines z hz)
      rwa [gaugeEquiv_fst htriple] at h
    -- The fourth line, with its direction transversal-normalized.
    have hgw_ne : gaugeEquiv htriple w ≠ 0 := fun h =>
      mem_classReps_ne_zero (hPreps hw)
        ((gaugeEquiv htriple).injective (by rw [h, map_zero]))
    obtain ⟨r, hr, hrval⟩ :=
      exists_classRep _ (mem_nonzeroDirections_iff.mpr hgw_ne)
    have hline_w : ∀ t : ZMod 3,
        residueLine 0 (gaugeEquiv htriple w) t ∈
          S₀.image ⇑(gaugeEquiv htriple) :=
      lineThrough0_image_linearEquiv (gaugeEquiv htriple) (hPlines w hw)
    have hline_r : lineThrough0 r ⊆ S₀.image ⇑(gaugeEquiv htriple) := by
      rcases hrval with rfl | hrneg
      · exact lineThrough0_subset_iff.mpr hline_w
      · rw [hrneg, lineThrough0_neg]
        exact lineThrough0_subset_iff.mpr hline_w
    -- `r`'s class is `w`'s, which differs from every axis class.
    have hne_axis : ∀ v ∈ linePencil S₀ 0, w ≠ v →
        r ≠ gaugeEquiv htriple v := by
      intro v hv hwv hreq
      rcases hrval with hrw | hrw
      · exact hwv ((gaugeEquiv htriple).injective (hrw.symm.trans hreq))
      · have h1 : gaugeEquiv htriple v = -(gaugeEquiv htriple w) :=
          hreq.symm.trans hrw
        have h2 : gaugeEquiv htriple w = gaugeEquiv htriple (-v) := by
          rw [map_neg, h1, neg_neg]
        have h3 : w = -v := (gaugeEquiv htriple).injective h2
        exact classReps_not_neg_mem v (hPreps hv)
          (by rw [← h3]; exact hPreps hw)
    have hr_free : toIdx r ∈ freeRepsIdx := by
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · rw [← classRepsIdx_eq]
        exact Finset.mem_image_of_mem _ hr
      · intro hmem
        have hcases : r = stdDir 0 ∨ r = stdDir 1 ∨ r = stdDir 2 := by
          rcases Finset.mem_insert.mp hmem with h | hmem'
          · exact Or.inl (toIdx_injective (by rw [h, toIdx_stdDir_zero]))
          · rcases Finset.mem_insert.mp hmem' with h | hmem''
            · exact Or.inr (Or.inl
                (toIdx_injective (by rw [h, toIdx_stdDir_one])))
            · rw [Finset.mem_singleton] at hmem''
              exact Or.inr (Or.inr
                (toIdx_injective (by rw [hmem'', toIdx_stdDir_two])))
        rcases hcases with h | h | h
        · exact hne_axis x hx hwx (by rw [h, ← gaugeEquiv_snd htriple])
        · exact hne_axis y hy hwy (by rw [h, ← gaugeEquiv_trd htriple])
        · exact hne_axis z hz hwz (by rw [h, ← gaugeEquiv_fst htriple])
    -- The standard star sits inside the encoded window.
    have hstar_sub : stdStarIdx (toIdx r) ⊆
        (S₀.image ⇑(gaugeEquiv htriple)).image toIdx := by
      unfold stdStarIdx
      refine Finset.union_subset (Finset.union_subset
        (Finset.union_subset ?_ ?_) ?_) ?_
      · rw [← toIdx_stdDir_zero, ← lineThrough0_image_toIdx]
        exact Finset.image_subset_image (lineThrough0_subset_iff.mpr hline_x)
      · rw [← toIdx_stdDir_one, ← lineThrough0_image_toIdx]
        exact Finset.image_subset_image (lineThrough0_subset_iff.mpr hline_y)
      · rw [← toIdx_stdDir_two, ← lineThrough0_image_toIdx]
        exact Finset.image_subset_image (lineThrough0_subset_iff.mpr hline_z)
      · rw [← lineThrough0_image_toIdx]
        exact Finset.image_subset_image hline_r
    exact endgame_absurd hstar_sub (stdStarIdx_card _ hr_free)
      (fun k hk extras hex => by
        have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
        rcases hk4 with rfl | rfl | rfl | rfl
        · have := endgame_caseA_nine _ hr_free _ hex; omega
        · have := endgame_caseA_ten _ hr_free _ hex; omega
        · have := endgame_caseA_eleven _ hr_free _ hex; omega
        · have := endgame_caseA_twelve _ hr_free _ hex; omega)
      (by omega) (by omega) (by omega)
  · -- CASE B: no independent triple — the pencil is planar and its
    -- four concurrent lines cover a full plane.
    have h2 : 1 < (linePencil S₀ 0).card := by omega
    obtain ⟨x, hx, y, hy, hxy_ne⟩ := Finset.one_lt_card.mp h2
    have hxy : LinearIndependent (ZMod 3) ![x, y] :=
      classReps_pair_linearIndependent (hPreps hx) (hPreps hy) hxy_ne
    have hspan : ∀ b ∈ linePencil S₀ 0, b ∈ spanPairFinset x y := by
      intro b hb
      by_contra hout
      exact hsplit ⟨x, hx, y, hy, b, hb,
        (linearIndependent_triple_iff hxy).mpr hout⟩
    -- A vector outside the 9-element span window.
    have hspan_card : (spanPairFinset x y).card ≤ 9 := by
      unfold spanPairFinset
      exact le_trans Finset.card_image_le (by decide)
    have hout : ∃ c, c ∉ spanPairFinset x y := by
      by_contra hall
      have hsub : (Finset.univ : Finset (ResiduePoint 3 3)) ⊆
          spanPairFinset x y := by
        intro c _
        by_contra hc
        exact hall ⟨c, hc⟩
      have hle := Finset.card_le_card hsub
      have h27 : (Finset.univ : Finset (ResiduePoint 3 3)).card = 27 := by
        decide
      omega
    obtain ⟨c, hc⟩ := hout
    have htriple : LinearIndependent (ZMod 3) ![c, x, y] :=
      (linearIndependent_triple_iff hxy).mpr hc
    have hS₂card : (S₀.image ⇑(gaugeEquiv htriple)).card = S.card := by
      rw [Finset.card_image_of_injective _ (gaugeEquiv htriple).injective,
        hS₀card]
    have hS₂fam : classCount (S₀.image ⇑(gaugeEquiv htriple)) =
        classCount S := by
      rw [classCount_image_linearEquiv, hS₀fam]
    -- Four pencil directions, gauged and encoded.
    obtain ⟨T4, hT4sub, hT4card⟩ := Finset.exists_subset_card_eq hpen₀
    have hinj : Function.Injective
        (fun b => toIdx (gaugeEquiv htriple b)) :=
      fun a b hab => (gaugeEquiv htriple).injective (toIdx_injective hab)
    have hDcard :
        (T4.image (fun b => toIdx (gaugeEquiv htriple b))).card = 4 := by
      rw [Finset.card_image_of_injective _ hinj, hT4card]
    have hDsub : T4.image (fun b => toIdx (gaugeEquiv htriple b)) ⊆
        zPlaneDirsIdx := by
      intro d hd
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨s, t, hst⟩ := mem_spanPairFinset.mp (hspan b (hT4sub hb))
      have hgb : gaugeEquiv htriple b = s • stdDir 0 + t • stdDir 1 := by
        rw [← hst, map_add, map_smul, map_smul,
          gaugeEquiv_snd htriple, gaugeEquiv_trd htriple]
      have hz2 : (gaugeEquiv htriple b) 2 = 0 := by
        rw [hgb]
        simp [stdDir]
      have hgb_ne : gaugeEquiv htriple b ≠ 0 := fun h =>
        mem_classReps_ne_zero (hPreps (hT4sub hb))
          ((gaugeEquiv htriple).injective (by rw [h, map_zero]))
      exact toIdx_mem_zPlaneDirsIdx _ hgb_ne hz2
    have hDneg :
        ∀ d ∈ T4.image (fun b => toIdx (gaugeEquiv htriple b)),
          dblIdx d ∉ T4.image (fun b => toIdx (gaugeEquiv htriple b)) := by
      intro d hd hdd
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨b', hb', hb'e⟩ := Finset.mem_image.mp hdd
      have hgg : gaugeEquiv htriple b' = gaugeEquiv htriple (-b) := by
        apply toIdx_injective
        rw [hb'e, ← toIdx_neg, map_neg]
      have hbb' : b' = -b := (gaugeEquiv htriple).injective hgg
      refine classReps_not_neg_mem b (hPreps (hT4sub hb)) ?_
      rw [← hbb']
      exact hPreps (hT4sub hb')
    have hcover := four_plane_classes_cover _
      (Finset.mem_powersetCard.mpr ⟨hDsub, hDcard⟩) hDneg
    -- The whole plane sits inside the encoded window.
    have hplane_sub : zPlaneIdx ⊆
        (S₀.image ⇑(gaugeEquiv htriple)).image toIdx := by
      rw [← hcover]
      refine Finset.biUnion_subset.mpr ?_
      intro d hd
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
      rw [← lineThrough0_image_toIdx]
      exact Finset.image_subset_image (lineThrough0_subset_iff.mpr
        (lineThrough0_image_linearEquiv _ (hPlines b (hT4sub hb))))
    exact endgame_absurd hplane_sub zPlaneIdx_card
      (fun k hk extras hex => by
        have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
        rcases hk4 with rfl | rfl | rfl | rfl
        · have := endgame_caseB_nine _ hex; omega
        · have := endgame_caseB_ten _ hex; omega
        · have := endgame_caseB_eleven _ hex; omega
        · have := endgame_caseB_twelve _ hex; omega)
      (by omega) (by omega) (by omega)

/-! ## The certificate of record and its consequences -/

/-- THE `(3,3)` FRACTIONAL COST CERTIFICATE AT PRICE 13.  Together
with the transfer theorem this prices the mod-3 factor of
every coprime composite in dimension three. -/
theorem fractionalCostAt_three_three :
    FractionalCostAt 3 3 (nonzeroDirections 3 3) 13 :=
  fractionalCostAt_three_three_iff_classCount_le.mpr classCount_le_card

/-- The direction menu is nonempty (transfer side condition). -/
theorem nonzeroDirections_three_three_nonempty :
    (nonzeroDirections 3 3).Nonempty := by decide

/-- Lower half of the exact cell: every Kakeya set over `(ZMod 3)³`
has at least 13 points — the certificate applied to a full carrier. -/
theorem thirteen_le_card_of_isKakeyaSet
    {K : Finset (ResiduePoint 3 3)} (hK : IsKakeyaSet K) :
    13 ≤ K.card := by
  have h := fractionalCostAt_three_three K
  have hall : (nonzeroDirections 3 3).filter
      (fun b => CarriesLine K b) = nonzeroDirections 3 3 :=
    Finset.filter_true_of_mem fun b _ =>
      isKakeyaSet_iff_forall_carriesLine.mp hK b
  have h26 : (nonzeroDirections 3 3).card = 26 := by decide
  rw [hall, h26] at h
  omega

/-- THE 13-POINT WITNESS, in encoded form — found by computer search,
re-verified by the kernel below (the search carries no authority). -/
def threeThreeWitnessIdx : Finset (Fin 27) :=
  {9, 18, 3, 6, 15, 24, 1, 19, 22, 25, 11, 20, 5}

/-- The witness on the carrier. -/
def threeThreeWitness : Finset (ResiduePoint 3 3) :=
  threeThreeWitnessIdx.image ofIdx

theorem ofIdx_injective : Function.Injective ofIdx := by
  intro a b h
  rw [← toIdx_ofIdx a, ← toIdx_ofIdx b, h]

theorem threeThreeWitness_image_toIdx :
    threeThreeWitness.image toIdx = threeThreeWitnessIdx := by
  unfold threeThreeWitness
  rw [Finset.image_image,
    show (toIdx ∘ ofIdx) = id from funext toIdx_ofIdx, Finset.image_id]

theorem threeThreeWitness_card : threeThreeWitness.card = 13 := by
  unfold threeThreeWitness
  rw [Finset.card_image_of_injective _ ofIdx_injective]
  decide

/-- The witness is Kakeya: the zero direction is anchored anywhere,
and every family is carried — checked on the transversal in the index
world and spread to all 26 directions by negation invariance. -/
theorem threeThreeWitness_isKakeyaSet : IsKakeyaSet threeThreeWitness := by
  intro b
  by_cases hb : b = 0
  · subst hb
    refine ⟨ofIdx 9, fun t => ?_⟩
    have hline : residueLine (ofIdx 9) 0 t = ofIdx 9 := by
      funext i
      simp only [residueLine, Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
        smul_eq_mul, mul_zero, add_zero]
    rw [hline]
    exact Finset.mem_image_of_mem _ (by decide)
  · obtain ⟨r, hr, hrv⟩ :=
      exists_classRep b (mem_nonzeroDirections_iff.mpr hb)
    have hidx : ∀ d ∈ classRepsIdx, carriesIdx threeThreeWitnessIdx d := by
      decide
    have hfast : CarriesLineFast threeThreeWitness r := by
      have h1 : carriesIdx (threeThreeWitness.image toIdx) (toIdx r) := by
        rw [threeThreeWitness_image_toIdx]
        refine hidx _ ?_
        rw [← classRepsIdx_eq]
        exact Finset.mem_image_of_mem _ hr
      exact carriesIdx_iff.mp h1
    have hcar : CarriesLine threeThreeWitness r :=
      carriesLineFast_iff.mp hfast
    rcases hrv with rfl | hrneg
    · exact hcar
    · rw [hrneg] at hcar
      exact carriesLine_neg.mp hcar

/-- THE NEW EXACT CELL: `minKakeyaSize 3 3 = 13`. -/
theorem minKakeyaSize_three_three : minKakeyaSize 3 3 = 13 := by
  refine le_antisymm ?_ ?_
  · have h := minKakeyaSize_le_card threeThreeWitness_isKakeyaSet
    rwa [threeThreeWitness_card] at h
  · obtain ⟨K, hK, hcard⟩ := exists_minKakeyaSize_witness 3 3
    rw [← hcard]
    exact thirteen_le_card_of_isKakeyaSet hK

/-- THE INFINITE FAMILY: exact multiplicativity of the mod-3 factor in
dimension three against EVERY coprime co-factor — the transfer theorem
fires at the now-proved true price. -/
theorem minKakeyaSize_three_mul_dim_three (M : ℕ) [NeZero M]
    (h : Nat.Coprime 3 M) :
    minKakeyaSize (3 * M) 3 = 13 * minKakeyaSize M 3 := by
  have hfc : FractionalCostAt 3 3 (nonzeroDirections 3 3)
      (minKakeyaSize 3 3) := by
    rw [minKakeyaSize_three_three]
    exact fractionalCostAt_three_three
  have heq := minKakeyaSize_mul_eq_of_fractionalCostAt h
    nonzeroDirections_three_three_nonempty hfc
  rw [heq, minKakeyaSize_three_three]

/-- THE `(6,3)` CELL, CLOSED: `minKakeyaSize 6 3 = 65`.  The mod-2
certificate fails at its true price in dimension three, leaving only
`4·min(3,3) ≤ min(6,3) ≤ 5·min(3,3)`; the certificate priced on the
mod-3 factor collapses the sandwich. -/
theorem minKakeyaSize_six_three : minKakeyaSize 6 3 = 65 := by
  have h := minKakeyaSize_three_mul_dim_three 2 (by decide)
  rw [show (3 * 2 : ℕ) = 6 from rfl, minKakeyaSize_two_three] at h
  omega

/-- ZERO CHINESE REMAINDER DEFECT at `(6,3)`: the minimum is exactly
multiplicative — the first composite exact cell in dimension three in
this development. -/
theorem minKakeyaSize_six_three_eq_product :
    minKakeyaSize 6 3 = minKakeyaSize 2 3 * minKakeyaSize 3 3 := by
  rw [minKakeyaSize_six_three, minKakeyaSize_two_three,
    minKakeyaSize_three_three]


end KakeyaMultiplicativity
