/-
**wake.w's `wc_main` from `.sp3` to `.sp4`** (AArch64, the pre-spawn
consumer), inside `W`, in any valid layout of `wakeProg`: the call block
(`Spike/Lib/A64WakeTcb2Call.lean`) and the second `scc_rt_alloc_tcb` call
(`allocTcbG_segW` at `tcb2Q g c0`):

    .sp3:     str x0, [sp, #16]         -- the reserve's id `1` (tcb2Call_keep)
              movz x0, #2307
              movk x0, #128, lsl #16    -- x0 = hdr2
              movz x1, #1
              bl scc_rt_alloc_tcb       -- the callee (allocTcbG_segW, its frame of 192)
    .sp4:                               -- `aN .n4` at `t = pinA + 104`

The frame's words `cA`, `m`, `fr` (`FrW`) and the id at `[sp, #16]` survive the
call (outside the callee's region), so the exit is `A64WakeWcSp4Seg`'s
entry `aN .n4` at the second TCB `pinA + 104` (`tcb2Q_tcbOf`).

- `tcbWG_mono`: `TcbWG` under a stronger frame condition;
- `j3`, `wcNC'`: `.sp3`'s invariant (`x0 = 1`, the frame's words) and the
  call node with the frame's words and the id;
- `WcSp3W`: the block's and the callee's states inside `W` (the callee's at
  its region `R.callee (-80) (-192) 0`, any return to `.sp4`);
- `wake_wc_sp3_segW`: the segment; the header word's store (`hhdr`) and the
  counter's add (`htcb`) as in `allocTcbG_segWA` (the counter's old value
  `80` owned at the `ldadd` node's states only: `scc_rt_start`'s call runs
  the same pc at `0`);
- `wcNS_clone`: a state at the `svc` (`wcNS` at `t2`) is at `cloneAt` with
  `x3` the TCB of `tcb2Q g c0` (`hXq`).
-/
import Spike.Lib.A64WakeWcSp4Seg
import Spike.Lib.Rt.A64RtTcbGA
import Spike.Lib.A64WakeTcb2CallW
import Spike.Lib.WakePreA

namespace Spike.Lib.A64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.WakePh.WcSp4 (FrW)
open Spike.Lib.A64.WakePh.Tcb2Call (oW tcb2Call tcb2Call_ok tcb2Call_wcNC tcb2Call_keep tcb2Q tcb2Q_tcbOf wcN3 wcNC)
open Spike.Lib.A64.Rt (TcbGG TcbWG TcbOkGA tcbNG tcbXG hdrA tcbOf allocTcbG_segWA)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)

/-- **`scc_rt_alloc_tcb`'s node obligations under a stronger frame
condition.** -/
theorem tcbWG_mono {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F F' : MachineData → Prop} {q : TcbGG} {i : Ret0.TN} (h : TcbWG W K exe endPc R F q i)
    (hFF : ∀ m, F' m → F m) : TcbWG W K exe endPc R F' q i := by
  cases i <;> dsimp only [TcbWG] at h ⊢ <;> first | exact Ret0.blkW_mono h hFF | exact Ret0.nodeW_mono h hFF

section Nodes

variable (lab : Label → Int64) (c0 : Ctl) (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64)

/-- **`.sp3`'s invariant**: the reserve's id `1` in `x0`, the frame's words. -/
def j3 (σ : AS) : Prop := σ.regs.X0.toBitVec = 1#64 ∧ FrW cA m fr σ

/-- **The call node** (`wcNC`) with the frame's words and the id at
`[sp, #16]`. -/
def wcNC' : ND := ⟨(wcNC lab c0).pc, oW, fun σ c => (wcNC lab c0).J σ c ∧ FrW cA m fr σ ∧ σ.slot (-64) = 1#64⟩

/-- The second TCB: `pinA + 104`. -/
abbrev t2 : BitVec 64 := Ret0.pinA lab + 104#64

end Nodes

/-- **The second TCB call's context in `wc_main`'s region `R`** at the
memory `mm`, for the ghost `g` (`ResCtx`'s form): a caller's state at the
call node `Jc` (`(wcNC' lab c0 cA m fr).J`), the callee's entry, the
caller's cells kept. -/
def TcbCtx (lab : Label → Int64) (R : Region) (Jc : AS → Ctl → Prop) (c0 : Ctl) (g : Ret0.AllocTcb.G)
    (mm : MachineData) : Prop :=
  ∃ mC σC c, Abs R oW mC σC ∧ Jc σC c ∧ (tcbNG lab (tcb2Q g c0) .e).J (enter (-80) σC) c ∧
    CKept R (-80) (-192) 0 mC mm

/-- **`.sp3`'s states to `.sp4` inside `W`**: the call block's and the
callee's (in its region, for any return to `.sp4`). -/
structure WcSp3W (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (c0 : Ctl) (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64) : Prop where
  blk : BlkW W K exe endPc R F (wcN3 (_root_.Executable.labels exe).label (j3 cA m fr) c0) tcb2Call
  tcb : ∀ g : Ret0.AllocTcb.G, g.ra = ((_root_.Executable.labels exe).label ".L21_wc_main.sp4").toBitVec →
    ∀ i, TcbWG W K exe endPc (R.callee (-80) (-192) 0)
      (fun mm => F mm ∧ CallerCells R (-80) (-192) 0 mm ∧
        TcbCtx (_root_.Executable.labels exe).label R (wcNC' (_root_.Executable.labels exe).label c0 cA m fr).J c0 g mm)
      (tcb2Q g c0) i

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` from `.sp3` to `.sp4` is one segment inside `W`** in any
valid layout of `wakeProg`: from `.sp3` (the reserve's id `1` in `x0`, the
frame's words `cA`, `m`, the source at `c0`) to `A64WakeWcSp4Seg`'s entry
`aN .n4` at the second TCB `pinA + 104`. `scc_rt_alloc_tcb` at
`tcb2Q g c0` writes the header word (`hhdr`) and adds to the counter
(`htcb`, its old value `80` owned at the `ldadd` node's states), moving only
memory `K` keeps off the caller's cells (`hFK`,
`hKR`). Its states lie in `W` (`hW`). -/
theorem wake_wc_sp3_segW {W : Frag isaLSE2} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.wakeProg kp) (hend : endPc = endOf exe SccCode.wakeProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -272) (hhi : 0 ≤ R.hi)
    {c0 : Ctl} {cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} (hW : WcSp3W W K exe endPc R F c0 cA m fr)
    (hhdr : ∀ g, Ret0.StOk ms F exe endPc (hdrA (_root_.Executable.labels exe).label (tcb2Q g c0))
      ((tcb2Q g c0).h ||| 1#64 <<< 36))
    (htcb : ∀ g, TcbOkGA ms F exe endPc (R.callee (-80) (-192) 0) F (tcb2Q g c0))
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-80) (-192) 0).Off (k - -80) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8) :
    SegW W K p lbl ms (At exe endPc R F (wcN3 (_root_.Executable.labels exe).label (j3 cA m fr) c0))
      (At exe endPc R F (aN (_root_.Executable.labels exe).label c0 (t2 (_root_.Executable.labels exe).label)
        cA m fr .n4)) := by
  let lab := (_root_.Executable.labels exe).label
  -- the call block
  have hA : SegW W K p lbl ms (At exe endPc R F (wcN3 lab (j3 cA m fr) c0))
      (At exe endPc R F (wcNC' lab c0 cA m fr)) := by
    refine Ret0.seg_oneW (seg_ndW (by simp [tcb2Call]) tcb2Call_ok hF hR hal (by omega) hhi
      (code_of hp hend (Spike.Lib.A64.WakePh.Tcb2Call.wake_tcb2CallIn |> fun h => by
        simp only [Spike.Lib.A64.WakePh.Tcb2Call.tcb2CallIn, Bool.and_eq_true] at h; exact h.1)
        (ofNat4_zero _)) hW.blk fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_⟩⟩)
    obtain ⟨h1, h2, h3⟩ := tcb2Call_wcNC hp hJ
    obtain ⟨-, -, hsl⟩ := tcb2Call_keep lab (lab ".L21_wc_main.sp3") σ
    obtain ⟨-, hx0, h72, h80, h16, h8⟩ := hJ
    refine ⟨h1.symm, ?_, h3, ?_, ?_⟩
    · show SO.le oW (arun lab tcb2Call ⟨lab ".L21_wc_main.sp3", oW, σ⟩).so = true
      rw [(Spike.Lib.A64.WakePh.Tcb2Call.tcb2Call_pc lab (lab ".L21_wc_main.sp3") σ).2]; rfl
    · show (arun lab tcb2Call ⟨lab ".L21_wc_main.sp3", oW, σ⟩).σ.slot (-72) = cA ∧
        (arun lab tcb2Call ⟨lab ".L21_wc_main.sp3", oW, σ⟩).σ.slot (-80) = m ∧
        (arun lab tcb2Call ⟨lab ".L21_wc_main.sp3", oW, σ⟩).σ.slot (-16) = fr.1 ∧
        (arun lab tcb2Call ⟨lab ".L21_wc_main.sp3", oW, σ⟩).σ.slot (-8) = fr.2
      rw [hsl]; simp [Spike.Lib.upd, h72, h80, h16, h8]
    · show (arun lab tcb2Call ⟨lab ".L21_wc_main.sp3", oW, σ⟩).σ.slot (-64) = 1#64
      rw [hsl]; simp [Spike.Lib.upd, hx0]
  -- the call
  have hC : SegW W K p lbl ms (At exe endPc R F (wcNC' lab c0 cA m fr))
      (At exe endPc R F (aN lab c0 (t2 lab) cA m fr .n4)) := by
    refine Ret0.seg_oneW (call_nd_FWK (KC := True) (lo' := -192) (hi' := 0) (M := fun _ => True)
      (nC := wcNC' lab c0 cA m fr) (N := fun _ : Unit => aN lab c0 (t2 lab) cA m fr .n4) (E := fun e : Empty => e.elim)
      (Ne := fun g : Ret0.AllocTcb.G => tcbNG lab (tcb2Q g c0) .e)
      (Ex := fun g : Ret0.AllocTcb.G => tcbXG lab (tcb2Q g c0))
      hR hal hF (by show R.lo ≤ -80 + -192; omega) (by decide) (by show (-80 : Int) < R.hi; omega) (by decide)
      (by show (-80 : Int) % 16 = 0; decide) (by decide) (by decide) (fun _ => hFK) (fun _ => hKR)
      (fun _ h _ => h)
      (fun R' F' hR' hal' hlo' hhi' hF' _ hFF hR'e hcc g hg hkeep => by
        subst hR'e
        obtain ⟨σC, c, ⟨⟨-, -, -, h30⟩, -, -⟩, ⟨-, -, -, h30', -, -⟩⟩ := hg
        exact (allocTcbG_segWA hp hend Spike.Lib.A64.WakePh.Tcb2W.wake_allocTcbIn hF' hR' hal' hlo' hhi'
          hFF (tcb2Q g c0)
          (by show (80#64).toNat + (Ret0.AllocTcb.lenOf Spike.Lib.A64.WakePh.hdr2).toNat ≤ 131072; decide)
          (hhdr g) ((htcb g).mono hFF)
          fun i => tcbWG_mono (hW.tcb g (h30'.symm.trans h30) i) fun m h => ⟨hFF m h, hcc m h, hkeep m h⟩).mono_post
          fun _ _ ⟨x, h⟩ => ⟨x, h, trivial⟩)
      (fun _ => rfl) ?_ ?_)
    · rintro σC c ⟨⟨rfl, h0, h1, -⟩, -, -⟩
      exact ⟨⟨σC.regs.SP.toBitVec, σC.regs.X29.toBitVec, σC.regs.X30.toBitVec⟩, rfl,
        rfl, rfl, rfl, rfl, h0, h1⟩
    · rintro g ⟨⟩ σC c σx c' σR ⟨⟨hc, -, -, h30⟩, ⟨h72, h80, h16, h8⟩, h64⟩ ⟨-, -, -, h30', -, -⟩ ⟨hc', hpost⟩ hreg -
        hsl
      have hkeep : ∀ k : Int, -80 ≤ k → k < 0 → k % 8 = 0 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
        hsl k ⟨h3, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, wcNC']; omega)
      refine .inl ⟨(), ?_, rfl, ⟨hc', ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · show lab ".L21_wc_main.sp4" = Int64.ofBitVec (tcb2Q g c0).g.ra
        rw [← h30']
        show _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [h30, int64_ofBitVec_toBitVec]
      · show σR.regs.X0.toBitVec = t2 lab
        rw [hreg, Spike.Lib.A64.Rt.postG_tcbOf lab (tcb2Q g c0) hpost, tcb2Q_tcbOf]
      · rw [hkeep (-72) (by omega) (by omega) (by omega), h72]
      · rw [hkeep (-80) (by omega) (by omega) (by omega), h80]
      · rw [hkeep (-16) (by omega) (by omega) (by omega), h16]
      · rw [hkeep (-8) (by omega) (by omega) (by omega), h8]
      · rw [hkeep (-64) (by omega) (by omega) (by omega), h64]
  exact hA.seq hC

omit [Kraken.Executable.ValidLayout exe] in
/-- **A state at the clone's `svc`** (`wcNS` at the second TCB `t2`) is at
`WakePreA.cloneAt` with `x3` the TCB of `tcb2Q g c0`, for any `g` (`hXq` of `spawn_workerPostQ`). -/
theorem wcNS_clone {k cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} {c0 c : Ctl} {s : State} (g : Ret0.AllocTcb.G)
    (h : At exe endPc R F (Spike.Lib.A64.WakePh.WcSp4.wcNS (_root_.Executable.labels exe).label c0
      (t2 (_root_.Executable.labels exe).label) k cA m fr) s c) :
    s.st.2 = Spike.Lib.WakePreA.cloneAt ".L21_wc_main" exe ∧
      (s.st.1.regs.getXReg .X3).toBitVec = tcbOf (_root_.Executable.labels exe).label (tcb2Q g c0) := by
  obtain ⟨-, -, -, hpc, σ, hA, -, hJ⟩ := h
  refine ⟨hpc, ?_⟩
  rw [hA.regs, tcb2Q_tcbOf]
  exact hJ.2.2.2.2.1

end Seg

end Spike.Lib.A64.Flow.WakeWc

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wake_wc_sp3_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wake_wc_sp3_segW

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wcNS_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wcNS_clone
