import N16B

namespace KakeyaMultiplicativity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fc2n_s08 :
    ∀ j : Fin 4096,
      countN2 (32768 + j.val) * 6 ≤
        popcountN2 (32768 + j.val) * 15 := by
  decide +kernel

end KakeyaMultiplicativity
