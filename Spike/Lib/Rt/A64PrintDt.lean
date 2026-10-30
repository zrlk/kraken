/-
**`scc_rt_print`'s write tail inside its frame** (AArch64): from the
routine's loop head on, its states (`Spike/Lib/A64Print.lean`'s blocks, in
the routine's region `Rp`, the caller's `x29` and the return address in
their cells, under a frame condition `C` no write inside `Rp` breaks) step
among themselves or out of the frame, at the return (`b16`'s `ret`) or the
abort call (`b14`'s `bl scc_rt_abort`), keeping the promise set. The pieces
are `Spike/Lib/Rt/A64TailDt.lean`'s: a `BlkSt` per block of the loop and of
the exits, a `Pt` at the barrier `dmb ish` leading `.2_write`
(`Spike/Lib/Rt/A64FenceDt.lean`) and one at the `write` call. Nothing names a
layout: the code enters through `PrintD.Code`, the transfer sites through
`hns`.

- `PJ x29 ra`: the frame's facts the pieces keep: the caller's `x29` at
  `-16`, the return address at `-8`;
- `PP`, `piece`: the pieces; `PrintIn exe endPc Rp x29 ra C`: some piece;
- `printIn_steps`: a certification step from `PrintIn` lands in `PrintIn`
  or in `Out`, given the routine's code, the pieces off the transfer sites
  (`hns`) and the exit blocks' ends in `Out` (`hret`, `hfail`);
- `printIn_of_at`: the `write` node (`At … (PrintD.N … .svc)`) is in
  `PrintIn`.
-/
import Spike.Lib.Rt.A64FenceDt
import Spike.Lib.A64PrintD

namespace Spike.Lib.A64.Rt

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem
open Scc.Sem.A64 (abi)
open Spike.Lib.A64.Flow
open Spike.Lib.A64
open Spike.Lib (ClosedC StepsTo)
open Spike.Lib.A64.Print (b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b16 oI)
open Spike.Lib.A64.PrintD (pcSvc)

/-! ## The pieces -/

/-- **The frame's facts**: the caller's `x29` at `-16`, the return address
at `-8`. -/
def PJ (x29 ra : BitVec 64) (σ : Flow.AS) : Prop := σ.slot (-16) = x29 ∧ σ.slot (-8) = ra

/-- The pieces: one per block of the loop and the exits, the barrier and the
`write` call. -/
inductive PP where
  | loop | n3 | fence | write | svc | n5 | n6 | n7 | chk2 | n9 | n10 | chk3 | n12 | adv | fail | done

section Pieces

variable (exe : _root_.Executable) (endPc : Int64) (Rp : Region) (x29 ra : BitVec 64) (C : MachineData → Prop)

/-- **The pieces' pcs** (their nodes' pcs, `PrintD.N`). -/
def ppc : PP → Int64
  | .loop => (_root_.Executable.labels exe).label ".L9_scc_rt_print.1_loop"
  | .n3 => (_root_.Executable.labels exe).label ".L9_scc_rt_print.1_loop" + 4 + 4 + 4 + 4
  | .fence => (_root_.Executable.labels exe).label ".L9_scc_rt_print.2_write"
  | .write => (_root_.Executable.labels exe).label ".L9_scc_rt_print.2_write" + 4
  | .svc => pcSvc (_root_.Executable.labels exe).label
  | .n5 => pcSvc (_root_.Executable.labels exe).label + 4
  | .n6 => pcSvc (_root_.Executable.labels exe).label + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4
  | .n7 => pcSvc (_root_.Executable.labels exe).label + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4
  | .chk2 => (_root_.Executable.labels exe).label ".L9_scc_rt_print.3_chk2"
  | .n9 => (_root_.Executable.labels exe).label ".L9_scc_rt_print.3_chk2" + 4 + 4 + 4 + 4 + 4 + 4
  | .n10 => (_root_.Executable.labels exe).label ".L9_scc_rt_print.3_chk2" + 4 + 4 + 4 + 4 + 4 + 4 + 4
  | .chk3 => (_root_.Executable.labels exe).label ".L9_scc_rt_print.4_chk3"
  | .n12 => (_root_.Executable.labels exe).label ".L9_scc_rt_print.4_chk3" + 4 + 4 + 4 + 4
  | .adv => (_root_.Executable.labels exe).label ".L9_scc_rt_print.5_adv"
  | .fail => (_root_.Executable.labels exe).label ".L9_scc_rt_print.6_fail"
  | .done => (_root_.Executable.labels exe).label ".L9_scc_rt_print.7_done"

/-- **A piece of `scc_rt_print`'s write tail**: before an instruction of a
block (at its node's pc, `PrintD.N`), at the barrier, or at the `write`
call (`x0 = 1`, `x8 = 64`). -/
def piece : PP → State → Prop
  | .loop => BlkSt exe endPc Rp C (ppc exe .loop) oI (PJ x29 ra) b2
  | .n3 => BlkSt exe endPc Rp C (ppc exe .n3) oI (PJ x29 ra) b3
  | .fence => Pt exe endPc Rp C (ppc exe .fence) oI (PJ x29 ra)
  | .write => BlkSt exe endPc Rp C (ppc exe .write) oI (PJ x29 ra) b4
  | .svc => Pt exe endPc Rp C (ppc exe .svc) oI (fun σ => PJ x29 ra σ ∧ σ.regs.X0 = 1 ∧ σ.regs.X8 = 64)
  | .n5 => BlkSt exe endPc Rp C (ppc exe .n5) oI (PJ x29 ra) b5
  | .n6 => BlkSt exe endPc Rp C (ppc exe .n6) oI (PJ x29 ra) b6
  | .n7 => BlkSt exe endPc Rp C (ppc exe .n7) oI (PJ x29 ra) b7
  | .chk2 => BlkSt exe endPc Rp C (ppc exe .chk2) oI (PJ x29 ra) b8
  | .n9 => BlkSt exe endPc Rp C (ppc exe .n9) oI (PJ x29 ra) b9
  | .n10 => BlkSt exe endPc Rp C (ppc exe .n10) oI (PJ x29 ra) b10
  | .chk3 => BlkSt exe endPc Rp C (ppc exe .chk3) oI (PJ x29 ra) b11
  | .n12 => BlkSt exe endPc Rp C (ppc exe .n12) oI (PJ x29 ra) b12
  | .adv => BlkSt exe endPc Rp C (ppc exe .adv) oI (PJ x29 ra) b13
  | .fail => BlkSt exe endPc Rp C (ppc exe .fail) oI (PJ x29 ra) b14
  | .done => BlkSt exe endPc Rp C (ppc exe .done) oI (PJ x29 ra) b16

/-- **`scc_rt_print`'s write tail inside its frame**: some piece. -/
def PrintIn (s : State) : Prop := ∃ i, piece exe endPc Rp x29 ra C i s

end Pieces

/-! ## The steps -/

section Steps

variable {A : Arch} {μ : Marks} {x : Kernel.KState} {tid : Nat}
  {exe : _root_.Executable} {endPc : Int64} {Rp : Region} {x29 ra : BitVec 64} {C : MachineData → Prop}

/-- A step from a piece `D` stepping into `D ∨ E`, `D` inside `T` and `E`
landing in `T`. -/
private theorem into {D E T : State → Prop} (h : StepsTo A (Kernel.certSem abi A μ x tid) tid D E)
    (hD : ∀ s, D s → T s) (hE : ∀ s, E s → T s) :
    ∀ p q : Thread isaLSE2 × Memory, D p.1.st → ThreadStepC A (Kernel.certSem abi A μ x tid) tid p q →
      T q.1.st ∧ q.1.prom = p.1.prom := by
  intro p q hd hs
  obtain ⟨h1, h2⟩ := h p q hd hs
  exact ⟨h1.elim (hD _) (hE _), h2⟩

/-- A block's entry: a state at a nonempty block's pc, related at `oI` to a
`PJ` state, under `C`. -/
private theorem ent {pc : Int64} {blk : List Directive} {s : State} {σ : Flow.AS} (hne : blk ≠ [])
    (he : s.exe = exe) (hn : s.endPc = endPc) (hd : s.decls = {}) (hpc : s.st.2 = pc)
    (hA : Flow.Abs Rp oI s.st.1 σ) (hJ : PJ x29 ra σ) (hC : C s.st.1) : BlkSt exe endPc Rp C pc oI (PJ x29 ra) blk s :=
  pt_blkSt hne ⟨he, hn, hd, hpc, σ, hJ, hA, hC⟩

/-- The frame's facts survive a write below `-16`. -/
private theorem pj_upd {σ : Flow.AS} {k : Int} {v : BitVec 64} (h : PJ x29 ra σ) (hk : k < -16) :
    PJ x29 ra { σ with slot := Spike.Lib.upd σ.slot k v } := by
  obtain ⟨h0, h8⟩ := h
  refine ⟨?_, ?_⟩
  · show Spike.Lib.upd σ.slot k v (-16) = x29
    have : (-16 : Int) ≠ k := by omega
    simp [Spike.Lib.upd_apply, this, h0]
  · show Spike.Lib.upd σ.slot k v (-8) = ra
    have : (-8 : Int) ≠ k := by omega
    simp [Spike.Lib.upd_apply, this, h8]

/-- The tail. -/
local notation "PI" => PrintIn exe endPc Rp x29 ra C

/-- **A step from `scc_rt_print`'s write tail** lands in it or in `Out`,
keeping the promises, given the routine's code (`hcode`, any ghosts), the
region's facts, `C` kept by writes inside the region (`hC`), the pieces
off the transfer sites (`hns`), and the exit blocks' ends in `Out`: the
return (`hret`, `b16`) and the abort call (`hfail`, `b14`). -/
theorem printIn_steps {Out : State → Prop} {c0 : Ctl} {x29' ra' : BitVec 64}
    (hcode : PrintD.Code c0 x29' ra' exe endPc) (hR : Rp.OK) (hal : Rp.base.toNat % 16 = 0) (hlo : Rp.lo ≤ -48)
    (hhi : 0 ≤ Rp.hi) (hC : FStable Rp C) (hns : ∀ s, PI s → Kernel.siteAt abi μ s = none)
    (hret : ∀ s, BlkEnd exe endPc Rp C (ppc exe .done) oI (PJ x29 ra) b16 s → Out s)
    (hfail : ∀ s, BlkEnd exe endPc Rp C (ppc exe .fail) oI (PJ x29 ra) b14 s → Out s) :
    StepsTo A (Kernel.certSem abi A μ x tid) tid PI Out := by
  have hsite : ∀ i : PP, ∀ s, piece exe endPc Rp x29 ra C i s → Kernel.siteAt abi μ s = none :=
    fun i s h => hns s ⟨i, h⟩
  have inj : ∀ i : PP, ∀ s, piece exe endPc Rp x29 ra C i s → PI s ∨ Out s := fun i s h => .inl ⟨i, h⟩
  rintro p q ⟨i, hD⟩ hs
  cases i
  case loop =>
    -- to `.done` or to `.n3`
    refine into (blkSt_steps (pc := ppc exe .loop) (J := PJ x29 ra) Print.b2_ok hC hR hal hlo hhi
      (fun s he hn => hcode.loop s he hn) (hsite .loop)) (inj .loop) ?_ p q hD hs
    rintro s ⟨he, hn, hd, σ0, hJ, hpc, hA, hCs⟩
    rw [Print.b2_run] at hpc hA
    split at hpc
    · exact inj .done s (ent (by simp [b16]) he hn hd hpc hA hJ hCs)
    · exact inj .n3 s (ent (by simp [b3]) he hn hd hpc hA hJ hCs)
  case n3 =>
    refine into (blkSt_steps (pc := ppc exe .n3) (J := PJ x29 ra) Print.b3_ok hC hR hal hlo hhi
      (fun s he hn => hcode.n3 s he hn) (hsite .n3)) (inj .n3) ?_ p q hD hs
    rintro s ⟨he, hn, hd, σ0, hJ, hpc, hA, hCs⟩
    rw [Print.b3_run] at hpc hA
    exact inj .fence s ⟨he, hn, hd, hpc, _, hJ, hA, hCs⟩
  case fence =>
    -- the barrier: to the write block
    refine into (fence_steps (pc := ppc exe .fence) (fun s he hn => hcode.fence s he hn) (hsite .fence))
      (inj .fence) ?_ p q hD hs
    exact fun s h => inj .write s (pt_blkSt (by simp [b4]) h)
  case write =>
    -- to the `write` call
    refine into (blkSt_steps (pc := ppc exe .write) (J := PJ x29 ra) Print.b4_ok hC hR hal hlo hhi
      (fun s he hn => hcode.write s he hn) (hsite .write)) (inj .write) ?_ p q hD hs
    rintro s ⟨he, hn, hd, σ0, hJ, hpc, hA, hCs⟩
    rw [Print.b4_run] at hpc hA
    refine inj .svc s ⟨he, hn, hd, hpc, _, ⟨?_, rfl, rfl⟩, hA, hCs⟩
    exact hJ
  case svc =>
    -- the `write` call: to `.n5`
    have hcall : ∀ σ : Flow.AS, (PJ x29 ra σ ∧ σ.regs.X0 = 1 ∧ σ.regs.X8 = 64) →
        ∃ call, svcCall σ.regs = some call ∧ ∀ st tl, call ≠ .clone st tl := by
      rintro σ ⟨-, h0, h8⟩
      have : ∃ buf n, svcCall σ.regs = some (.write 1 buf n) := by
        simp [svcCall, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.a64, h0, h8, Scc.Sem.A64.xRegs]
      obtain ⟨buf, n, hw⟩ := this
      exact ⟨_, hw, fun _ _ h => nomatch h⟩
    refine into (svc_steps (pc := ppc exe .svc) hC (fun s he hn => hcode.svc s he hn) hcall (hsite .svc))
      (inj .svc) ?_ p q hD hs
    rintro s ⟨he, hn, hd, hpc, _, ⟨σ, v, ⟨hJ, -, -⟩, rfl⟩, hA, hCs⟩
    exact inj .n5 s (ent (by simp [b5]) he hn hd hpc hA hJ hCs)
  case n5 =>
    refine into (blkSt_steps (pc := ppc exe .n5) (J := PJ x29 ra) Print.b5_ok hC hR hal hlo hhi
      (fun s he hn => hcode.n5 s he hn) (hsite .n5)) (inj .n5) ?_ p q hD hs
    rintro s ⟨he, hn, hd, σ0, hJ, hpc, hA, hCs⟩
    rw [Print.b5_run] at hpc hA
    exact inj .n6 s (ent (by simp [b6]) he hn hd hpc hA (pj_upd hJ (by decide)) hCs)
  case n6 =>
    -- to `.loop` or to `.n7`
    refine into (blkSt_steps (pc := ppc exe .n6) (J := PJ x29 ra) Print.b6_ok hC hR hal hlo hhi
      (fun s he hn => hcode.n6 s he hn) (hsite .n6)) (inj .n6) ?_ p q hD hs
    rintro s ⟨he, hn, hd, σ0, hJ, hpc, hA, hCs⟩
    rw [Print.b6_run] at hpc hA
    split at hpc
    · exact inj .loop s (ent (by simp [b2]) he hn hd hpc hA hJ hCs)
    · exact inj .n7 s (ent (by simp [b7]) he hn hd hpc hA hJ hCs)
  case n7 =>
    refine into (blkSt_steps (pc := ppc exe .n7) (J := PJ x29 ra) Print.b7_ok hC hR hal hlo hhi
      (fun s he hn => hcode.n7 s he hn) (hsite .n7)) (inj .n7) ?_ p q hD hs
    rintro s ⟨he, hn, hd, σ0, hJ, hpc, hA, hCs⟩
    rw [Print.b7_run] at hpc hA
    exact inj .chk2 s (ent (by simp [b8]) he hn hd hpc hA hJ hCs)
  case chk2 =>
    refine into (blkSt_steps (pc := ppc exe .chk2) (J := PJ x29 ra) Print.b8_ok hC hR hal hlo hhi
      (fun s he hn => hcode.chk2 s he hn) (hsite .chk2)) (inj .chk2) ?_ p q hD hs
    rintro s ⟨he, hn, hd, σ0, hJ, hpc, hA, hCs⟩
    rw [Print.b8_run] at hpc hA
    exact inj .n9 s (ent (by simp [b9]) he hn hd hpc hA hJ hCs)
  case n9 =>
    -- to `.loop` or to `.n10`
    refine into (blkSt_steps (pc := ppc exe .n9) (J := PJ x29 ra) Print.b9_ok hC hR hal hlo hhi
      (fun s he hn => hcode.n9 s he hn) (hsite .n9)) (inj .n9) ?_ p q hD hs
    rintro s ⟨he, hn, hd, σ0, hJ, hpc, hA, hCs⟩
    rw [Print.b9_run] at hpc hA
    split at hpc
    · exact inj .loop s (ent (by simp [b2]) he hn hd hpc hA hJ hCs)
    · exact inj .n10 s (ent (by simp [b10]) he hn hd hpc hA hJ hCs)
  case n10 =>
    refine into (blkSt_steps (pc := ppc exe .n10) (J := PJ x29 ra) Print.b10_ok hC hR hal hlo hhi
      (fun s he hn => hcode.n10 s he hn) (hsite .n10)) (inj .n10) ?_ p q hD hs
    rintro s ⟨he, hn, hd, σ0, hJ, hpc, hA, hCs⟩
    rw [Print.b10_run] at hpc hA
    exact inj .chk3 s (ent (by simp [b11]) he hn hd hpc hA hJ hCs)
  case chk3 =>
    -- to `.fail` or to `.n12`
    refine into (blkSt_steps (pc := ppc exe .chk3) (J := PJ x29 ra) Print.b11_ok hC hR hal hlo hhi
      (fun s he hn => hcode.chk3 s he hn) (hsite .chk3)) (inj .chk3) ?_ p q hD hs
    rintro s ⟨he, hn, hd, σ0, hJ, hpc, hA, hCs⟩
    rw [Print.b11_run] at hpc hA
    split at hpc
    · exact inj .fail s (ent (by simp [b14]) he hn hd hpc hA hJ hCs)
    · exact inj .n12 s (ent (by simp [b12]) he hn hd hpc hA hJ hCs)
  case n12 =>
    refine into (blkSt_steps (pc := ppc exe .n12) (J := PJ x29 ra) Print.b12_ok hC hR hal hlo hhi
      (fun s he hn => hcode.n12 s he hn) (hsite .n12)) (inj .n12) ?_ p q hD hs
    rintro s ⟨he, hn, hd, σ0, hJ, hpc, hA, hCs⟩
    rw [Print.b12_run] at hpc hA
    exact inj .adv s (ent (by simp [b13]) he hn hd hpc hA hJ hCs)
  case adv =>
    -- to `.loop`
    refine into (blkSt_steps (pc := ppc exe .adv) (J := PJ x29 ra) Print.b13_ok hC hR hal hlo hhi
      (fun s he hn => hcode.adv s he hn) (hsite .adv)) (inj .adv) ?_ p q hD hs
    rintro s ⟨he, hn, hd, σ0, hJ, hpc, hA, hCs⟩
    rw [Print.b13_run] at hpc hA
    have hJ' := pj_upd (k := -40) (v := σ0.slot (-40) - σ0.slot (-32))
      (pj_upd (k := -48) (v := σ0.slot (-48) + σ0.slot (-32)) hJ (by decide)) (by decide)
    exact inj .loop s (ent (by simp [b2]) he hn hd hpc hA hJ' hCs)
  case fail =>
    exact into (blkSt_steps (pc := ppc exe .fail) (J := PJ x29 ra) Print.b14_ok hC hR hal hlo hhi
      (fun s he hn => hcode.fail s he hn) (hsite .fail)) (inj .fail)
      (fun s h => .inr (hfail s h)) p q hD hs
  case done =>
    exact into (blkSt_steps (pc := ppc exe .done) (J := PJ x29 ra) Print.b16_ok hC hR hal hlo hhi
      (fun s he hn => hcode.done s he hn) (hsite .done)) (inj .done)
      (fun s h => .inr (hret s h)) p q hD hs

end Steps

/-! ## Entry -/

/-- **The `write` node is in the tail**: at `PrintD.N … .svc`, under a frame
condition `F`. -/
theorem printIn_of_at {exe : _root_.Executable} {endPc : Int64} {Rp : Region} {F : MachineData → Prop}
    {c0 c : Ctl} {x29 ra : BitVec 64} {s : State}
    (hAt : At exe endPc Rp F (PrintD.N (_root_.Executable.labels exe).label c0 x29 ra .svc) s c) :
    PrintIn exe endPc Rp x29 ra F s := by
  obtain ⟨he, hn, hd, hpc, σ, hA, hF, ⟨-, h16, h8⟩, h0, hx8⟩ := hAt
  exact ⟨.svc, he, hn, hd, hpc, σ, ⟨⟨h16, h8⟩, h0, hx8⟩, hA, hF⟩

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.A64.Rt.printIn_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms printIn_steps

/--
info: 'Spike.Lib.A64.Rt.printIn_of_at' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms printIn_of_at

end Spike.Lib.A64.Rt
