import Scc.Cert.Rt.A64Morestack

/-!
# The segment theorems of `Scc.Cert.Rt.A64Morestack`

The theorems of `Scc/Cert/Rt/A64Morestack.lean` whose statements are stated over the
untrusted segment predicate (`Spike.Lib.Seg`, `MemSide`), moved out of the
trusted tree unchanged (same namespace, names and statements; FENCE1
follow-up 2): `seg_grow`, `seg_move`, `seg_switch`, `seg_new`, `seg_morestack`. The definitions, code
data and decided checks they use stay in `Scc.Cert.Rt.A64Morestack`.
-/

namespace Scc.Cert.Rt.A64.Morestack

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib Spike.Lib.A64 Spike.Lib.A64.Flow
  Scc.Cert.Rt.A64.Print

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {c0 : Ctl} {ra need : BitVec 64}

/-- The frame record and the call to `scc_rt_grow`. -/
theorem seg_grow {F : MachineData → Prop} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -16) (hhi : 0 ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (nE (_root_.Executable.labels exe).label R c0 ra need).pc b0) :
    Seg p lbl ms (At exe endPc R F (nE (_root_.Executable.labels exe).label R c0 ra need))
      (At exe endPc R F (nGrow (_root_.Executable.labels exe).label R c0 ra need)) := by
  refine (fn_seg (N := fun _ : Unit => nE _ R c0 ra need) (E := fun _ : Unit => nGrow _ R c0 ra need)
    (fun _ => seg_nd (by simp [b0]) b0_ok hF hR hal hlo hhi hcode fun σ c hJ => ⟨c, .refl c, ?_⟩) ()).mono_post
    fun _ _ ⟨_, h⟩ => h
  rw [nE, b0_run]
  obtain ⟨hc, hsp, h30, h0⟩ := hJ
  refine .inr ⟨(), rfl, rfl, ?_⟩
  simp_all [nGrow, Spike.Lib.upd_apply, addr_m16]

/-- `x29` moved by the distance `scc_rt_grow` returned. -/
theorem seg_move {F' : BitVec 64 → MachineData → Prop} {v ob osz : BitVec 64} (hF' : FStable R (F' v))
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -16) (hhi : 0 ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (nG1 (_root_.Executable.labels exe).label R c0 v ob osz).pc b1) :
    Seg p lbl ms (At exe endPc R (Moved R ra F' v) (nG1 (_root_.Executable.labels exe).label R c0 v ob osz))
      (At exe endPc R (Moved R ra F' v) (nSw (_root_.Executable.labels exe).label c0 v ob osz)) := by
  refine (fn_seg (N := fun _ : Unit => nG1 _ R c0 v ob osz) (E := fun _ : Unit => nSw _ c0 v ob osz)
    (fun _ => seg_nd (by simp [b1]) b1_ok (Moved.stable hF') hR hal hlo hhi hcode
      fun σ c hJ => ⟨c, .refl c, ?_⟩) ()).mono_post fun _ _ ⟨_, h⟩ => h
  rw [nG1, b1_run]
  obtain ⟨hc, h29, h0, h1, h2⟩ := hJ
  refine .inr ⟨(), rfl, rfl, ?_⟩
  simp only [nSw, UInt64.toBitVec_add, h29, h0, h1, h2, hc, and_self, and_true]
  exact ⟨trivial, by rw [BitVec.add_comm, BitVec.sub_add_cancel]⟩

/-- **The stack switch** `add sp, x29, #0`: onto the moved frame record. -/
theorem seg_switch {F' : BitVec 64 → MachineData → Prop} {v ob osz : BitVec 64}
    (hF'' : FStable (swR v 0 16) (F' v))
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (nSw (_root_.Executable.labels exe).label c0 v ob osz).pc bs) :
    Seg p lbl ms (At exe endPc R (Moved R ra F' v) (nSw (_root_.Executable.labels exe).label c0 v ob osz))
      (SwAt exe endPc 0 16 F' (n2 (_root_.Executable.labels exe).label c0 ra ob osz)) := by
  rw [bs_eq] at hcode
  refine sw_nd rfl hcode rfl rfl fun m σ c _ hG hJ => ?_
  obtain ⟨h16, hok, -, ⟨j0, hj0⟩, ⟨j8, hj8, hra⟩, hF⟩ := hG
  obtain ⟨hc, h29, h1, h2⟩ := hJ
  obtain ⟨hsp, hx1, hx2⟩ := sw_step oS ((nSw (_root_.Executable.labels exe).label c0 v ob osz).pc + Int64.ofNat 4) σ
  simp only [nSw] at hsp hx1 hx2 ⊢
  rw [hsp, h29]
  have ha0 : (swR v 0 16).addr 0 = v := by simp [swR, Region.addr]
  have ha8 : (swR v 0 16).addr 8 = v + 8 := by simp [swR, Region.addr]
  have hs8 : movedSlot m v 8 = ra := by unfold movedSlot; rw [ha8, hj8]; exact hra
  refine ⟨h16, hok, hF'' _ _ hF fun _ _ _ => rfl, movedSlot m v, fun k hk => ?_, c, .refl c, ?_⟩
  · obtain ⟨hk8, hk0, hk16⟩ := hk
    simp only [swR] at hk0 hk16
    have : k = 0 ∨ k = 8 := by omega
    rcases this with rfl | rfl
    · exact ⟨j0, by rw [ha0]; exact hj0, by simp [movedSlot, ha0, hj0]⟩
    · exact ⟨j8, by rw [ha8]; exact hj8, by rw [hs8, hra]⟩
  · simp only [n2, hx1, hx2, h1, h2, hc, hs8, and_self]

/-- On the new stack: the call to `scc_rt_stack_release` and the return. -/
theorem seg_new {F' : BitVec 64 → MachineData → Prop} {v ob osz : BitVec 64}
    (hF'' : FStable (swR v 0 16) (F' v)) (h16 : v.toNat % 16 = 0) (hok : (swR v 0 16).OK)
    (hc2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (n2 (_root_.Executable.labels exe).label c0 ra ob osz).pc b2)
    (hc3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (nR1 (_root_.Executable.labels exe).label c0 ra).pc b3)
    (hrel : Seg p lbl ms (At exe endPc (swR v 0 16) (F' v) (nRel (_root_.Executable.labels exe).label c0 ra ob osz))
      (At exe endPc (swR v 0 16) (F' v) (nR1 (_root_.Executable.labels exe).label c0 ra))) :
    Seg p lbl ms (At exe endPc (swR v 0 16) (F' v) (n2 (_root_.Executable.labels exe).label c0 ra ob osz))
      (At exe endPc (swR v 0 16) (F' v) (nRet c0 ra)) := by
  have hal : (swR v 0 16).base.toNat % 16 = 0 := h16
  have hlo : (swR v 0 16).lo ≤ 0 := Int.le_refl _
  have hhi : 16 ≤ (swR v 0 16).hi := Int.le_refl _
  refine (fn_seg (N := NB _ c0 ra ob osz) (E := fun _ : Unit => nRet c0 ra) (fun i => ?_) PB.n2).mono_post
    fun _ _ ⟨_, h⟩ => h
  cases i
  case n2 =>
    refine seg_nd (by simp [b2]) b2_ok hF'' hok hal hlo hhi hc2 fun σ c hJ => ⟨c, .refl c, ?_⟩
    simp only [NB, n2] at hJ
    rw [NB, n2, b2_run]
    refine .inl ⟨PB.rel, rfl, rfl, ?_⟩
    simp_all [NB, nRel]
  case rel => exact seg_given PB.r1 hrel
  case r1 =>
    refine seg_nd (by simp [b3]) b3_ok hF'' hok hal hlo hhi hc3 fun σ c hJ => ⟨c, .refl c, ?_⟩
    simp only [NB, nR1] at hJ
    rw [NB, nR1, b3_run]
    refine .inr ⟨(), ?_, rfl, ?_⟩ <;> simp_all [nRet, SO.entry]

/-- **`scc_rt_morestack` is one segment** in any valid layout `exe` of a
program `prog` with `morestackIn prog = true`, given its calls to
`scc_rt_grow` and `scc_rt_stack_release`: from its entry on the old stack to
its return on the new one, at the moved frame record `v`. -/
theorem seg_morestack {F : MachineData → Prop} {F' : BitVec 64 → MachineData → Prop}
    {prog : List Directive} [Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) (hprog : morestackIn prog = true)
    (hF : FStable R F) (hF'R : ∀ v, FStable R (F' v)) (hF'' : ∀ v, FStable (swR v 0 16) (F' v))
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -16) (hhi : 0 ≤ R.hi)
    (hgrow : Seg p lbl ms (At exe endPc R F (nGrow (_root_.Executable.labels exe).label R c0 ra need))
      (fun s c => ∃ v ob osz,
        At exe endPc R (Moved R ra F' v) (nG1 (_root_.Executable.labels exe).label R c0 v ob osz) s c))
    (hrel : ∀ v ob osz, Seg p lbl ms
      (At exe endPc (swR v 0 16) (F' v) (nRel (_root_.Executable.labels exe).label c0 ra ob osz))
      (At exe endPc (swR v 0 16) (F' v) (nR1 (_root_.Executable.labels exe).label c0 ra))) :
    Seg p lbl ms (At exe endPc R F (nE (_root_.Executable.labels exe).label R c0 ra need))
      (fun s c => ∃ v, At exe endPc (swR v 0 16) (F' v) (nRet c0 ra) s c) := by
  simp only [morestackIn, Bool.and_eq_true, and_assoc] at hprog
  obtain ⟨h0, h1, hs, h2, h3⟩ := hprog
  refine ((seg_grow hF hR hal hlo hhi (code_field hp hend h0 (by simp only [nE, pc0, add0]))).seq hgrow).seq ?_
  refine (Seg.exists_pre (P := fun g : BitVec 64 × BitVec 64 × BitVec 64 =>
      At exe endPc R (Moved R ra F' g.1) (nG1 _ R c0 g.1 g.2.1 g.2.2)) fun g => ?_).mono_pre
    fun _ _ ⟨v, ob, osz, h⟩ => ⟨(v, ob, osz), h⟩
  obtain ⟨v, ob, osz⟩ := g
  refine ((seg_move (hF'R v) hR hal hlo hhi (code_field hp hend h1 (by simp only [nG1, pc0, add4, add0]))).seq
    (seg_switch (hF'' v) (code_field hp hend hs (by simp only [nSw, pc0, add4, add0])))).seq
    (sw_seg fun v' h16 hok => ?_)
  exact (seg_new (hF'' v') h16 hok (code_field hp hend h2 (by simp only [n2, pc0, add4, add0]))
    (code_field hp hend h3 (by simp only [nR1, pc0, add4, add0])) (hrel v' ob osz)).mono_post
    fun _ _ h => ⟨v', h⟩

end Proof

end Scc.Cert.Rt.A64.Morestack
