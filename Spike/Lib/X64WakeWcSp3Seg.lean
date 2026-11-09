/-
**wake.w's `wc_main` from `.x19` to `.x20`: the second TCB** (x86-64; twin
of `Spike/Lib/A64WakeWcSp3Seg.lean`), inside `W`, in any valid layout of
`wakeCells`: the call block (`Spike/Lib/X64WakeTcb2Call.lean`) and the
second `scc_rt_alloc_tcb` call (`allocTcbG_segWA` at `tcb2Q g c0`):

    .Lwc_main.x1:
      movq %rax, -24(%rbp)              -- the reserve's id `1` (tcb2Call_keep)
      movq $8391939, %rdi               -- %rdi = hdr2
      movq $1, %rsi
      call scc_rt_alloc_tcb             -- the callee, `.x20` pushed at -72
    .Lwc_main.x2:                      -- `aN .n20` at `t = pinA + 136`

The frame's words `cA`, `m`, `fr` (`FrV`) and the id at `-24` survive the
call (above the callee's region), so the exit is `X64WakeWcSp4Seg`'s entry
`aN .n20` at the second TCB `pinA + 136` (`tcb2Q_tcbOf`).

Where x86-64 differs from AArch64: the callee's region is
`R.callee (-72) (-184) 8` (based at the pushed return address; A64's
`R.callee (-80) (-192) 0`); back from the callee only `%rsp`'s offset is
known, so the call lands at `n20I` (`%rbp` from `PostG`) and `At.rbp`
restores `oW`, as in `X64WakeWcSp4Seg` (the call node `wcNCR` carries `%rbp`
from its offsets, `Ret0.At.rbp_get`); no `hal`. The reserve's exit `rX` is
at `⟨-64, []⟩` with `%rbp` in its invariant, so `rX_wcN3` restores `oW`
with `Hello1.At.rbp_addr`; the caller's saved pair is its `%rbp` and the
return address at its entry's `[%rsp]` (`FrG`, `FrMG`; A64's `x29`, `x30`).

- `tcbWG_mono`: `TcbWG` under a stronger frame condition;
- `j3`, `wcNC'`, `wcNCR`, `t2`, `n20I`: `.x19`'s invariant (`%rax = 1`, the
  frame's words), the call node with the frame's words and the id (and
  `%rbp` from its offsets), the second TCB, the landing at `.x20`;
- `TcbCtx`, `WcSp3W`: the callee's call context; the block's and the
  callee's states inside `W` (the callee's at its region, any return to
  `.x20`);
- `wake_wc_sp3_segW`: the segment; the header word's store (`hhdr`) and the
  counter's add (`htcb`) as in `allocTcbG_segWA`;
- `MidG`, `FrG`, `FrMG`, `rX_wcN3`: the reserve's exit at `.x19` is `wcN3`
  at the frame's words, with the pure facts it keeps.
-/
import Spike.Lib.X64WakeWcRes
import Spike.Lib.X64WakeWcSp4Seg
import Spike.Lib.Rt.X64RtTcbGA
import Spike.Lib.X64WakeTcb2W

namespace Spike.Lib.X64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.WakePh.WcSp4 (FrV wcN20)
open Spike.Lib.X64.WakePh.Tcb2Call (oW oC tcb2Call tcb2Call_ok tcb2Call_wcNC tcb2Call_keep tcb2Q tcb2Q_tcbOf wcN3
  wcNC)
open Spike.Lib.X64.Rt (TcbGG TcbWG TcbOkGA tcbNG tcbXG hdrA allocTcbG_segWA)
open Spike.Lib.X64.Flow.Ret0 (CallerCells StOk)
open Scc.Cert.Rt.X64 (Lays endOf code_field)

set_option linter.unusedSimpArgs false

/-- **`scc_rt_alloc_tcb`'s node obligations under a stronger frame
condition.** -/
theorem tcbWG_mono {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F F' : MachineData → Prop} {q : TcbGG} {i : Ret0.TN} (h : TcbWG W K exe endPc R F q i)
    (hFF : ∀ m, F' m → F m) : TcbWG W K exe endPc R F' q i := by
  cases i <;> dsimp only [TcbWG] at h ⊢ <;> first | exact Ret0.blkW_mono h hFF | exact Ret0.nodeW_mono h hFF

section Nodes

variable (lab : Label → Int64) (c0 : Ctl) (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64)

/-- **`.x19`'s invariant**: the reserve's id `1` in `%rax`, the frame's
words. -/
def j3 (σ : AS) : Prop := σ.regs.rax.toBitVec = 1#64 ∧ FrV cA m fr σ

/-- **The call node** (`wcNC`) with the frame's words and the id at
`-24`. -/
def wcNC' : ND := ⟨(wcNC lab c0).pc, oC, fun σ c => (wcNC lab c0).J σ c ∧ FrV cA m fr σ ∧ σ.slot (-24) = 1#64⟩

/-- **The call node with `%rbp` from its offsets** (`Ret0.At.rbp_get`):
`%rbp` `72` bytes above `%rsp`. -/
def wcNCR : ND := ⟨(wcNC' lab c0 cA m fr).pc, oC, fun σ c => (wcNC' lab c0 cA m fr).J σ c ∧
  σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (0 - -72)⟩

/-- The second TCB: `pinA + 136`. -/
abbrev t2 : BitVec 64 := Ret0.pinA lab + 136#64

/-- **Back at `.x20`** with only `%rsp`'s offset known: `aN .n20`'s facts at
`t2`, `%rbp` `64` bytes above `%rsp` (`At.rbp` makes it `aN .n20`). -/
def n20I : ND := ⟨lab WakePh.WcSp4.x20L, ⟨-64, []⟩, fun σ c => (aN lab c0 (t2 lab) cA m fr .n20).J σ c ∧
  σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (0 - -64)⟩

end Nodes

/-- **The second TCB call's context in `wc_main`'s region `R`** at the
memory `mm`, for the ghost `g` (`ResCtx`'s form): a caller's state at the
call node `Jc` (`(wcNCR lab c0 cA m fr).J`), the callee's entry, the
caller's cells kept. -/
def TcbCtx (lab : Label → Int64) (R : Region) (Jc : AS → Ctl → Prop) (c0 : Ctl) (g : Ret0.AllocTcb.G)
    (mm : MachineData) : Prop :=
  ∃ mC σC c, Abs R oC mC σC ∧ Jc σC c ∧ (tcbNG lab (tcb2Q g c0) .e).J (enter (-72) σC) c ∧
    CKept R (-72) (-184) 8 mC mm

/-- **`.x19`'s states to `.x20` inside `W`**: the call block's and the
callee's (in its region, for any return to `.x20`). -/
structure WcSp3W (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (c0 : Ctl) (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64) : Prop where
  blk : BlkW W K exe endPc R F (wcN3 (_root_.Executable.labels exe).label (j3 cA m fr) c0) tcb2Call
  tcb : ∀ g : Ret0.AllocTcb.G, g.ra = ((_root_.Executable.labels exe).label ".Lwc_main.x2").toBitVec →
    ∀ i, TcbWG W K exe endPc (R.callee (-72) (-184) 8)
      (fun mm => F mm ∧ CallerCells R (-72) (-184) 8 mm ∧
        TcbCtx (_root_.Executable.labels exe).label R (wcNCR (_root_.Executable.labels exe).label c0 cA m fr).J c0
          g mm)
      (tcb2Q g c0) i

/-- From `.x19` to `.x20` inside the trivial predicate, with no outside
moves. -/
theorem WcSp3W.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {c0 : Ctl} {cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} :
    WcSp3W (fun _ _ => True) (fun _ _ => False) exe endPc R F c0 cA m fr := by
  refine ⟨BlkW.triv, fun _ _ i => ?_⟩
  cases i <;> dsimp only [TcbWG] <;> first | exact BlkW.triv | exact NodeW.triv

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` from `.x19` to `.x20` is one segment inside `W`** in any
valid layout of `wakeCells`: from `.x19` (the reserve's id `1` in `%rax`,
the frame's words `cA`, `m`, `fr`, the source at `c0`) to
`X64WakeWcSp4Seg`'s entry `aN .n20` at the second TCB `pinA + 136`.
`scc_rt_alloc_tcb` at `tcb2Q g c0` writes the header word (`hhdr`) and adds
to the counter (`htcb`, its old value `112` owned at the `lock xadd` node's
states), moving only memory `K` keeps off the caller's cells (`hFK`, `hKR`).
Its states lie in `W` (`hW`). -/
theorem wake_wc_sp3_segW {W : Frag isa} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -256) (hhi : 16 ≤ R.hi)
    {c0 : Ctl} {cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} (hW : WcSp3W W K exe endPc R F c0 cA m fr)
    (hhdr : ∀ g, StOk ms F (hdrA (_root_.Executable.labels exe).label (tcb2Q g c0))
      ((tcb2Q g c0).h ||| 1#64 <<< 36))
    (htcb : ∀ g, TcbOkGA ms F exe endPc (R.callee (-72) (-184) 8) F (tcb2Q g c0))
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-72) (-184) 8).Off (k - -72) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8) :
    SegW W K p lbl ms (At exe endPc R F (wcN3 (_root_.Executable.labels exe).label (j3 cA m fr) c0))
      (At exe endPc R F (aN (_root_.Executable.labels exe).label c0 (t2 (_root_.Executable.labels exe).label)
        cA m fr .n20)) := by
  let lab := (_root_.Executable.labels exe).label
  have hin := WakePh.Tcb2Call.wake_tcb2CallIn
  simp only [WakePh.Tcb2Call.tcb2CallIn, Bool.and_eq_true] at hin
  -- the call block
  have hA : SegW W K p lbl ms (At exe endPc R F (wcN3 lab (j3 cA m fr) c0))
      (At exe endPc R F (wcNC' lab c0 cA m fr)) := by
    refine Ret0.seg_oneW (seg_ndW (by simp [tcb2Call]) tcb2Call_ok hF hR (by omega) hhi
      (code_field hp hend hin.1 (ofNat_zero' _)) hW.blk fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_⟩⟩)
    obtain ⟨h1, h2, h3⟩ := tcb2Call_wcNC hp hJ
    obtain ⟨-, -, hsl⟩ := tcb2Call_keep lab (lab ".Lwc_main.x1") σ
    obtain ⟨-, hax, h16, h8, h0, h8'⟩ := hJ
    refine ⟨h1.symm, ?_, h3, ?_, ?_⟩
    · show SO.le oC (arun lab tcb2Call ⟨lab ".Lwc_main.x1", oW, σ⟩).so = true
      rw [(WakePh.Tcb2Call.tcb2Call_pc lab (lab ".Lwc_main.x1") σ).2]; decide
    · show FrV cA m fr (arun lab tcb2Call ⟨lab ".Lwc_main.x1", oW, σ⟩).σ
      simp only [FrV, hsl, upd_apply]
      exact ⟨h16, h8, h0, h8'⟩
    · show (arun lab tcb2Call ⟨lab ".Lwc_main.x1", oW, σ⟩).σ.slot (-24) = 1#64
      simp only [hsl, upd_apply]
      exact hax
  -- the call
  have hC : SegW W K p lbl ms (At exe endPc R F (wcNCR lab c0 cA m fr))
      (At exe endPc R F (n20I lab c0 cA m fr)) := by
    refine Ret0.seg_oneW (call_nd_FWK (KC := True) (e0 := 0) (lo' := -184) (hi' := 8) (M := fun _ => True)
      (nC := wcNCR lab c0 cA m fr) (N := fun _ : Unit => n20I lab c0 cA m fr) (E := fun e : Empty => e.elim)
      (Ne := fun g : Ret0.AllocTcb.G => tcbNG lab (tcb2Q g c0) .e)
      (Ex := fun g : Ret0.AllocTcb.G => tcbXG lab (tcb2Q g c0))
      hR hF (by show R.lo ≤ -72 - 0 + -184; omega) (by decide) (by show (-72 : Int) - 0 < R.hi; omega)
      (by show (-72 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-72 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide) (fun _ => hFK) (fun _ => hKR) (fun _ h _ => h)
      (fun R' F' hR' hlo' hhi' hF' _ hFF hR'e hcc g hg hkeep => by
        subst hR'e
        obtain ⟨σC, c, ⟨⟨⟨-, -, -, h72⟩, -, -⟩, -⟩, ⟨-, -, -, hra, -, -⟩⟩ := hg
        have hr : g.ra = (lab ".Lwc_main.x2").toBitVec := by
          change (tcb2Q g c0).g.ra = _
          rw [← hra, ← h72]; rfl
        exact (allocTcbG_segWA hp hend WakePh.Tcb2W.wake_allocTcbIn hF' hR' hlo' hhi' hFF (tcb2Q g c0)
          (by show (112#64 : BitVec 64).toNat + (Ret0.AllocTcb.lenOf WakePh.hdr2).toNat ≤ 131072; decide)
          (hhdr g) ((htcb g).mono hFF)
          fun i => tcbWG_mono (hW.tcb g hr i) fun m h => ⟨hFF m h, hcc m h, hkeep m h⟩).mono_post
          fun _ _ ⟨x, h⟩ => ⟨x, h, trivial⟩)
      (fun _ => rfl) ?_ ?_)
    · rintro σC c ⟨⟨⟨hc, hdi, hsi, -⟩, -, -⟩, -⟩
      exact ⟨⟨σC.regs.rsp.toBitVec, σC.regs.rbp.toBitVec, σC.slot (-72 - 0 + 0)⟩, rfl, hc, rfl, rfl, rfl, hdi, hsi⟩
    · rintro g ⟨⟩ σC c σx c' σR ⟨⟨⟨-, -, -, h72⟩, ⟨h16, h8, h0, h8'⟩, h24⟩, hb⟩ ⟨-, hsp, hfp, hra, -, -⟩
        ⟨hc', hpost⟩ hreg - - hsl
      have hkeep : ∀ k : Int, -64 ≤ k → k + 8 ≤ 16 → k % 8 = 0 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
        hsl k ⟨h3, by omega, by omega⟩ fun h => by simp only [Region.Off, Region.callee, wcNCR, oC] at h; omega
      refine .inl ⟨(), ?_, by show SO.le ⟨-64, []⟩ ⟨-72 - 0 + 8, []⟩ = true; decide,
        ⟨⟨hc', ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
      · show lab WakePh.WcSp4.x20L = Int64.ofBitVec (tcb2Q g c0).g.ra
        rw [← hra]
        show _ = Int64.ofBitVec (σC.slot (-72 - 0 + 0))
        rw [show (-72 : Int) - 0 + 0 = -72 by decide, h72, int64_ofBitVec_toBitVec]
      · show σR.regs.rax.toBitVec = t2 lab
        rw [hreg, Rt.postG_tcbOf lab (tcb2Q g c0) hpost, tcb2Q_tcbOf]
      · rw [hkeep (-16) (by omega) (by omega) (by omega), h16]
      · rw [hkeep (-8) (by omega) (by omega) (by omega), h8]
      · rw [hkeep 0 (by omega) (by omega) (by omega), h0]
      · rw [hkeep 8 (by omega) (by omega) (by omega), h8']
      · rw [hkeep (-24) (by omega) (by omega) (by omega), h24]
      · show σR.regs.get64 .rbp = σR.regs.get64 .rsp + BitVec.ofInt 64 (0 - -64)
        rw [hreg]
        simp only [Reg64s.get64] at hb ⊢
        rw [hpost.2.1, hpost.1, ← hfp, ← hsp]
        show σC.regs.rbp.toBitVec = σC.regs.rsp.toBitVec + 8#64 + BitVec.ofInt 64 (0 - -64)
        rw [hb]; bv_omega
  exact (hA.mono_post fun _ _ h => Ret0.At.rbp_get rfl h).seq
    (hC.mono_post fun _ _ h => Ret0.At.imp (At.rbp h fun _ _ h => h.2) fun _ _ h => h.1)

end Seg

/-! ## The reserve's exit at `.x19` -/

/-- **The pure facts the exit keeps**: the source `c0` at `S l A` for the
box's label `l` at `A`, the frame's word `cA` the box's address. -/
def MidG (S : WeakMem.AllocLabel → Nat → Ctl → Prop) (c0 : Ctl) (cA : BitVec 64) : Prop :=
  ∃ l A, S l A c0 ∧ cA.toNat = A

/-- **The saved pair is the caller's**: `fr` is the `%rbp` and the return
address (`[%rsp]`) of some entry state of `J0` (the prologue's saves,
`wcJF`). -/
def FrG (J0 : AS → Ctl → Prop) (fr : BitVec 64 × BitVec 64) : Prop :=
  ∃ σe c, J0 σe c ∧ fr = (σe.regs.rbp.toBitVec, σe.slot 0)

/-- **The saved pair and main's word are the caller's**: `fr` and `m` are
the `%rbp`, `[%rsp]` and `%rdi` of one entry state of `J0` (`wcJF`). -/
def FrMG (J0 : AS → Ctl → Prop) (fr : BitVec 64 × BitVec 64) (m : BitVec 64) : Prop :=
  ∃ σe c, J0 σe c ∧ fr = (σe.regs.rbp.toBitVec, σe.slot 0) ∧ m = σe.regs.rdi.toBitVec

/-- **The reserve's exit at `.x19` is `wcN3`** at the frame's words `cA`
(`-16`), `m` (`-8`) and the caller's saved pair `fr` (`0`, `8`), the source
`c` its ghost, `MidG`, `FrG` and `FrMG` holding; `oW`'s `%rbp` from `rX`'s
invariant (`Hello1.At.rbp_addr`). -/
theorem rX_wcN3 {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {J0 : AS → Ctl → Prop} {S : WeakMem.AllocLabel → Nat → Ctl → Prop} {s : State} {c : Ctl}
    {x : Unit} (h : At exe endPc R F (rX ms (_root_.Executable.labels exe).label R J0 S x) s c) :
    ∃ (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64), MidG S c cA ∧ FrG J0 fr ∧ FrMG J0 fr m ∧
      At exe endPc R F (wcN3 (_root_.Executable.labels exe).label (j3 cA m fr) c) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨l, A, ⟨q, ⟨σe, hJ0, h8, h0, hm8⟩, h16, -, -⟩, hS⟩, hb, hax⟩ := h
  refine ⟨σ.slot (-16), σ.slot (-8), (σ.slot 0, σ.slot 8), ⟨l, A, hS, h16⟩, ⟨σe, _, hJ0, Prod.ext h0 h8⟩,
    ⟨σe, _, hJ0, Prod.ext h0 h8, hm8⟩, ?_⟩
  have h1 : At exe endPc R F ⟨(_root_.Executable.labels exe).label ".Lwc_main.x1", ⟨-64, []⟩, fun σ' c' =>
      (wcN3 (_root_.Executable.labels exe).label (j3 (σ.slot (-16)) (σ.slot (-8)) (σ.slot 0, σ.slot 8)) c).J σ' c' ∧
        σ'.regs.get64 .rbp = R.addr 0⟩ s c :=
    ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨rfl, hax, rfl, rfl, rfl, rfl⟩, hb⟩
  exact Ret0.At.imp (Hello1.At.rbp_addr h1 fun _ _ h => h.2) fun _ _ h => h.1

end Spike.Lib.X64.Flow.WakeWc

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wake_wc_sp3_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wake_wc_sp3_segW

/-- info: 'Spike.Lib.X64.Flow.WakeWc.rX_wcN3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.rX_wcN3
