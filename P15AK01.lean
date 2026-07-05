import N16A

namespace KakeyaMultiplicativity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fc4n_s01 :
    ∀ j : Fin 4096,
      countN4 (4096 + j.val) * 10 ≤
        popcountN4 (4096 + j.val) * 15 := by
  decide +kernel

end KakeyaMultiplicativity
