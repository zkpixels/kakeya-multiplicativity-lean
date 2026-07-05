import N27

namespace KakeyaMultiplicativity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Coverage guard packed into one Bool (keeps Decidable synthesis
shallow: four bounded binders + one implication). -/
def covGuard (d1 d2 d3 d4 : Fin 27) : Bool :=
  (d1.val != d2.val) &&
  (d1.val != d3.val) &&
  (d1.val != d4.val) &&
  (d2.val != d3.val) &&
  (d2.val != d4.val) &&
  (d3.val != d4.val) &&
  ((dblIdx d1).val != d1.val) &&
  ((dblIdx d1).val != d2.val) &&
  ((dblIdx d1).val != d3.val) &&
  ((dblIdx d1).val != d4.val) &&
  ((dblIdx d2).val != d1.val) &&
  ((dblIdx d2).val != d2.val) &&
  ((dblIdx d2).val != d3.val) &&
  ((dblIdx d2).val != d4.val) &&
  ((dblIdx d3).val != d1.val) &&
  ((dblIdx d3).val != d2.val) &&
  ((dblIdx d3).val != d3.val) &&
  ((dblIdx d3).val != d4.val) &&
  ((dblIdx d4).val != d1.val) &&
  ((dblIdx d4).val != d2.val) &&
  ((dblIdx d4).val != d3.val) &&
  ((dblIdx d4).val != d4.val)

set_option maxHeartbeats 0 in
/-- Coverage, bitmask form: over plane-direction 4-tuples passing the
guard, the four line masks OR to the plane mask.  4096 tuples. -/
theorem natCov :
    ∀ d1 ∈ zPlaneDirsList, ∀ d2 ∈ zPlaneDirsList,
    ∀ d3 ∈ zPlaneDirsList, ∀ d4 ∈ zPlaneDirsList,
      covGuard d1 d2 d3 d4 = true →
      lineMaskN d1 ||| lineMaskN d2 ||| lineMaskN d3 ||| lineMaskN d4
        = 511 := by
  decide +kernel

/-- CASE-B COVERAGE: four concurrent plane lines in pairwise distinct
classes cover the whole plane.  Same statement as the artifact;
proved through the bitmask decide `natCov` plus membership specs. -/
theorem four_plane_classes_cover :
    ∀ D ∈ zPlaneDirsIdx.powersetCard 4, (∀ d ∈ D, dblIdx d ∉ D) →
      D.biUnion lineIdx0 = zPlaneIdx := by
  intro D hD hdbl
  rw [Finset.mem_powersetCard] at hD
  obtain ⟨hsub, hcard⟩ := hD
  obtain ⟨a, t, hat, rfl, ht3⟩ := Finset.card_eq_succ.mp hcard
  obtain ⟨b, c, d, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_three.mp ht3
  have hab : a ≠ b := fun h => hat (by simp [h])
  have hac : a ≠ c := fun h => hat (by simp [h])
  have had : a ≠ d := fun h => hat (by simp [h])
  have ma : a ∈ zPlaneDirsIdx := hsub (by simp)
  have mb : b ∈ zPlaneDirsIdx := hsub (by simp)
  have mc : c ∈ zPlaneDirsIdx := hsub (by simp)
  have md : d ∈ zPlaneDirsIdx := hsub (by simp)
  have hV : ∀ x y : Fin 27, x ≠ y → x.val ≠ y.val :=
    fun x y h hv => h (Fin.val_injective hv)
  have hdbl' : ∀ x ∈ (insert a {b, c, d} : Finset (Fin 27)),
      dblIdx x ≠ a ∧ dblIdx x ≠ b ∧ dblIdx x ≠ c ∧ dblIdx x ≠ d := by
    intro x hx
    have := hdbl x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at this
    exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2⟩
  have da := hdbl' a (by simp)
  have db := hdbl' b (by simp)
  have dc := hdbl' c (by simp)
  have dd := hdbl' d (by simp)
  have hg : covGuard a b c d = true := by
    simp only [covGuard, Bool.and_eq_true, bne_iff_ne, ne_eq]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hV _ _ hab, hV _ _ hac⟩, hV _ _ had⟩, hV _ _ hbc⟩, hV _ _ hbd⟩, hV _ _ hcd⟩, hV _ _ da.1⟩, hV _ _ da.2.1⟩, hV _ _ da.2.2.1⟩, hV _ _ da.2.2.2⟩, hV _ _ db.1⟩, hV _ _ db.2.1⟩, hV _ _ db.2.2.1⟩, hV _ _ db.2.2.2⟩, hV _ _ dc.1⟩, hV _ _ dc.2.1⟩, hV _ _ dc.2.2.1⟩, hV _ _ dc.2.2.2⟩, hV _ _ dd.1⟩, hV _ _ dd.2.1⟩, hV _ _ dd.2.2.1⟩, hV _ _ dd.2.2.2⟩
  have hnat := natCov a ((zPlaneDirsList_mem a).mpr ma)
    b ((zPlaneDirsList_mem b).mpr mb) c ((zPlaneDirsList_mem c).mpr mc)
    d ((zPlaneDirsList_mem d).mpr md) hg
  ext p
  have hbit := congrArg (fun n : ℕ => n.testBit p.val) hnat
  simp only [or_testBit] at hbit
  simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨x, hx, hpx⟩
    refine (zplane_bit p).mp (hbit.symm.trans ?_)
    rcases hx with hx | hx | hx | hx <;> rw [hx] at hpx
    · simp [(line_bit a ma p).mpr hpx]
    · simp [(line_bit b mb p).mpr hpx]
    · simp [(line_bit c mc p).mpr hpx]
    · simp [(line_bit d md p).mpr hpx]
  · intro hp
    have hone := hbit.trans ((zplane_bit p).mpr hp)
    simp only [Bool.or_eq_true] at hone
    rcases hone with ((ha' | hb') | hc') | hd'
    · exact ⟨a, Or.inl rfl, (line_bit a ma p).mp ha'⟩
    · exact ⟨b, Or.inr (Or.inl rfl), (line_bit b mb p).mp hb'⟩
    · exact ⟨c, Or.inr (Or.inr (Or.inl rfl)), (line_bit c mc p).mp hc'⟩
    · exact ⟨d, Or.inr (Or.inr (Or.inr rfl)), (line_bit d md p).mp hd'⟩


end KakeyaMultiplicativity
