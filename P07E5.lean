import N27

namespace KakeyaMultiplicativity

set_option maxHeartbeats 0 in
theorem natA9 :
    ∀ d ∈ freeRepsList, classCountN (starMaskN d) ≤ 9 := by
  decide +kernel

/-- Case A, `u = 9`. -/
theorem endgame_caseA_nine :
    ∀ d ∈ freeRepsIdx,
      ∀ extras ∈ ((Finset.univ : Finset (Fin 27)) \ stdStarIdx d).powersetCard 0,
        classCountIdx (stdStarIdx d ∪ extras) ≤ 9 := by
  intro d hd extras hmem
  rw [Finset.powersetCard_zero, Finset.mem_singleton] at hmem
  subst hmem
  rw [Finset.union_empty, classCountN_eq (star_bit d hd)]
  exact natA9 d ((freeRepsList_mem d).mpr hd)

end KakeyaMultiplicativity
