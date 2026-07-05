import N16A

namespace KakeyaMultiplicativity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fc4n_s15 :
    ∀ j : Fin 4096,
      countN4 (61440 + j.val) * 10 ≤
        popcountN4 (61440 + j.val) * 15 := by
  decide +kernel

end KakeyaMultiplicativity
