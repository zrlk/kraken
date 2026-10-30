import Scc.Cert.Rt.X64Morestack

/-!
# The segment theorems of `Scc.Cert.Rt.X64Morestack`

The theorems of `Scc/Cert/Rt/X64Morestack.lean` whose statements are stated over the
untrusted segment predicate (`Spike.Lib.Seg`, `MemSide`), moved out of the
trusted tree unchanged (same namespace, names and statements; FENCE1
follow-up 2): `seg_grow`, `seg_move`, `seg_switch`, `seg_new`, `seg_morestack`. The definitions, code
data and decided checks they use stay in `Scc.Cert.Rt.X64Morestack`.
-/

namespace Scc.Cert.Rt.X64.Morestack

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Spike.Lib Spike.Lib.X64

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {c0 : Ctl} {ra need fp : BitVec 64}

/-- The frame record and the call to `scc_rt_grow`. -/
theorem seg_grow {F : MachineData → Prop} (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -8) (hhi : 16 ≤ R.hi)
    (hcode : Code exe endPc) :
    Seg p lbl ms (At exe endPc R F (nE (_root_.Executable.labels exe).label R c0 ra need fp))
      (At exe endPc R F (nGrow (_root_.Executable.labels exe).label R c0 ra need fp)) := by
  refine (fn_seg (N := fun _ : Unit => nE _ R c0 ra need fp) (E := fun _ : Unit => nGrow _ R c0 ra need fp)
    (fun _ => seg_nd (by simp [b0]) b0_ok hF hR hlo hhi hcode.e fun σ c hJ => ⟨c, .refl c, ?_⟩) ()).mono_post
    fun _ _ ⟨_, h⟩ => h
  rw [nE, b0_run]
  obtain ⟨hc, hsp, h8, hdi, hbp⟩ := hJ
  refine .inr ⟨(), rfl, rfl, ?_⟩
  simp_all [nGrow, upd_apply, Region.addr_sub8]

/-- `%rbp` moved by the distance `scc_rt_grow` returned. -/
theorem seg_move {F' : BitVec 64 → MachineData → Prop} {v ob osz : BitVec 64} (hF' : FStable R (F' v))
    (hR : R.OK) (hlo : R.lo ≤ -8) (hhi : 16 ≤ R.hi) (hcode : Code exe endPc) :
    Seg p lbl ms (At exe endPc R (Moved R ra fp F' v) (nG1 (_root_.Executable.labels exe).label R c0 v ob osz))
      (At exe endPc R (Moved R ra fp F' v) (nSw (_root_.Executable.labels exe).label c0 v ob osz)) := by
  refine (fn_seg (N := fun _ : Unit => nG1 _ R c0 v ob osz) (E := fun _ : Unit => nSw _ c0 v ob osz)
    (fun _ => seg_nd (by simp [b1]) b1_ok (Moved.stable hF') hR hlo hhi hcode.g1
      fun σ c hJ => ⟨c, .refl c, ?_⟩) ()).mono_post fun _ _ ⟨_, h⟩ => h
  rw [nG1, b1_run]
  obtain ⟨hc, hbp, hax, hdx, hcx⟩ := hJ
  refine .inr ⟨(), by simp [nSw, Int64.add_assoc], rfl, ?_⟩
  simp_all [nSw]

/-- **The stack switch** `movq %rbp, %rsp`: onto the moved frame record. -/
theorem seg_switch {F' : BitVec 64 → MachineData → Prop} {v ob osz : BitVec 64}
    (hF'' : FStable (rN v) (F' v)) (hcode : Code exe endPc) :
    Seg p lbl ms (At exe endPc R (Moved R ra fp F' v) (nSw (_root_.Executable.labels exe).label c0 v ob osz))
      (SwAt exe endPc (-8) 16 F' (n2 (_root_.Executable.labels exe).label c0 ra v (fp + (v - R.addr 0)) ob osz)) := by
  refine sw_nd rfl hcode.sw (by simp [nSw, n2, Int64.add_assoc]) rfl fun m σ c _ hG hJ => ?_
  obtain ⟨hok, -, hcells, ⟨j0, hj0, hfr⟩, ⟨j8, hj8, hra⟩, hF⟩ := hG
  obtain ⟨hc, hbp, hdx, hcx⟩ := hJ
  obtain ⟨hsp, hx1, hx2⟩ := sw_step oS ((nSw (_root_.Executable.labels exe).label c0 v ob osz).pc + Int64.ofNat 3) σ
  simp only [nSw] at hsp hx1 hx2 ⊢
  rw [hsp, hbp]
  have hs0 : movedSlot m v 0 = fp + (v - R.addr 0) := by unfold movedSlot; rw [hj0]; exact hfr
  have hs8 : movedSlot m v 8 = ra := by unfold movedSlot; rw [hj8]; exact hra
  refine ⟨hok, hF'' _ _ hF fun _ _ _ => rfl, movedSlot m v, fun k hk => ?_, c, .refl c, ?_⟩
  · obtain ⟨j, hj⟩ := hcells k hk
    exact ⟨j, hj, by simp [movedSlot, rN, hj]⟩
  · simp only [n2, hx1, hx2, hdx, hcx, hc, hs0, hs8, hsp, hbp, and_self]

/-- On the new stack: the call to `scc_rt_stack_release` and the return. -/
theorem seg_new {F' : BitVec 64 → MachineData → Prop} {v w fr ob osz : BitVec 64}
    (hF'' : FStable (rN v) (F' v)) (hok : (rN v).OK) (hcode : Code exe endPc)
    (hrel : Seg p lbl ms (At exe endPc (rN v) (F' v) (nRel (_root_.Executable.labels exe).label c0 ra fr ob osz))
      (At exe endPc (rN v) (F' v) (nR1 (_root_.Executable.labels exe).label c0 ra fr))) :
    Seg p lbl ms (At exe endPc (rN v) (F' v) (n2 (_root_.Executable.labels exe).label c0 ra w fr ob osz))
      (At exe endPc (rN v) (F' v) (nRet c0 ra fr)) := by
  have hlo : (rN v).lo ≤ -8 := Int.le_refl _
  have hhi : 16 ≤ (rN v).hi := Int.le_refl _
  refine (fn_seg (N := NB _ c0 ra w fr ob osz) (E := fun _ : Unit => nRet c0 ra fr) (fun i => ?_) PB.n2).mono_post
    fun _ _ ⟨_, h⟩ => h
  cases i
  case n2 =>
    refine seg_nd (by simp [b2]) b2_ok hF'' hok hlo hhi hcode.n2 fun σ c hJ => ⟨c, .refl c, ?_⟩
    simp only [NB, n2] at hJ
    rw [NB, n2, b2_run]
    refine .inl ⟨PB.rel, rfl, rfl, ?_⟩
    simp_all [NB, nRel, nR1, upd_apply, BitVec.add_assoc]
  case rel => exact seg_given PB.r1 hrel
  case r1 =>
    refine seg_nd (by simp [b3]) b3_ok hF'' hok hlo hhi hcode.r1 fun σ c hJ => ⟨c, .refl c, ?_⟩
    simp only [NB, nR1] at hJ
    rw [NB, nR1, b3_run]
    refine .inr ⟨(), ?_, rfl, ?_⟩ <;> simp_all [nRet]

/-- **`scc_rt_morestack` is one segment**, given its code and its calls to
`scc_rt_grow` and `scc_rt_stack_release`: from its entry on the old stack to
its return on the new one, at the moved frame record `v`, with `%rbp` the
caller's frame pointer moved by the same distance. -/
theorem seg_morestack {F : MachineData → Prop} {F' : BitVec 64 → MachineData → Prop}
    (hcode : Code exe endPc)
    (hF : FStable R F) (hF'R : ∀ v, FStable R (F' v)) (hF'' : ∀ v, FStable (rN v) (F' v))
    (hR : R.OK) (hlo : R.lo ≤ -8) (hhi : 16 ≤ R.hi)
    (hgrow : Seg p lbl ms (At exe endPc R F (nGrow (_root_.Executable.labels exe).label R c0 ra need fp))
      (fun s c => ∃ v ob osz,
        At exe endPc R (Moved R ra fp F' v) (nG1 (_root_.Executable.labels exe).label R c0 v ob osz) s c))
    (hrel : ∀ v ob osz, Seg p lbl ms
      (At exe endPc (rN v) (F' v) (nRel (_root_.Executable.labels exe).label c0 ra (fp + (v - R.addr 0)) ob osz))
      (At exe endPc (rN v) (F' v) (nR1 (_root_.Executable.labels exe).label c0 ra (fp + (v - R.addr 0))))) :
    Seg p lbl ms (At exe endPc R F (nE (_root_.Executable.labels exe).label R c0 ra need fp))
      (fun s c => ∃ v, At exe endPc (rN v) (F' v) (nRet c0 ra (fp + (v - R.addr 0))) s c) := by
  refine ((seg_grow hF hR hlo hhi hcode).seq hgrow).seq ?_
  refine (Seg.exists_pre (P := fun g : BitVec 64 × BitVec 64 × BitVec 64 =>
      At exe endPc R (Moved R ra fp F' g.1) (nG1 _ R c0 g.1 g.2.1 g.2.2)) fun g => ?_).mono_pre
    fun _ _ ⟨v, ob, osz, h⟩ => ⟨(v, ob, osz), h⟩
  obtain ⟨v, ob, osz⟩ := g
  refine ((seg_move (hF'R v) hR hlo hhi hcode).seq (seg_switch (hF'' v) hcode)).seq
    (sw_seg fun v' hok => ?_)
  by_cases hv : v' = v
  · subst hv
    exact (seg_new (hF'' v') hok hcode (hrel v' ob osz)).mono_post fun _ _ h => ⟨v', h⟩
  · -- the switch's target is at `v`: no other region
    refine Seg.mono_pre (P := fun _ _ => False) ⟨fun _ _ => False, fun _ _ h => h, fun _ _ h => h.elim⟩ ?_
    rintro s c ⟨-, -, -, -, σ, hA, -, -, hsp, -⟩
    have := hA.so .rsp 0 (by simp [n2, oS, SO.get])
    exact hv (by rw [← hsp, this]; simp [swR, Region.addr])

end Proof

end Scc.Cert.Rt.X64.Morestack
