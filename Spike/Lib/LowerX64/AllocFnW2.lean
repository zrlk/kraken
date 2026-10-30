/-
**`scc_rt_alloc`'s states inside `W2`** (x86-64; the twin of
`Spike/Lib/LowerA64/AllocFnW2.lean`): `AllocW2`'s allocator field
(`Spike/Lib/LowerX64/NewBufC2.lean`) at `W₀ := W2`
(`Spike/Lib/LowerX64/SFactsA2.lean`), from the allocator's components
(`Spike/Lib/X64AllocG*.lean`, `Spike/Lib/X64SetupPlaced.lean`): the state's
facts (`allocSt`), the write abort's phase (`allocAb`), the arena's writes
(`allocArena`), the counter's write in its context (`allocCtr`), the
frames placed (`allocPlacedS`), the abort sites off the marks (`allocPc`).

- `nodeW_noSys1`, `blkW_noSysB`: a single instruction other than a
  `syscall`, and a covered block, at its label are off a system call;
- `allocNoSys`: no node of `scc_rt_alloc` is at a system call;
- `allocCtl`: at the call's control or its hold, `main`'s `ret` excluded,
  free of `ZBad`, and the frame runs staying put (`FrameRun.eq_of_newBuf`);
- `allocCtx_of`: `allocW2`'s counter context from the allocator's next
  nodes landing in it (`ctrRow_alloc`);
- `allocW2`: every node of `scc_rt_alloc` inside `W2` at the frames `fs`,
  the counter add's states in `CtrRow` at the frames' memory side landing in
  `PendA` (`hctx`), the controls and frames placed (`hP`);
- `allocHP`: `allocW2`'s `hP` in `AllocW2`'s call context (`AllocCtx`, the
  caller's slot file kept, `hJ1`); `slotRep_nbJ1`: `hJ1` at `nbJ1` from the
  walk's facts;
- `msOfAX_fields`, `msOfAX_mp`, `ctrRow_msOfAX`: the rows' memory side
  `msOfAX … ab` agrees with `msOfA` but for the byte step and the write
  abort's justification;
- `ctrRow_alloc_n4`, `allocCtx_n4`: the counter add's row landing exactly at
  the node after the add (x86-64's `.c2`, the old count held);
- `allocW2X`: `allocW2` at `msOfAX … ab`, the counter's context reduced to
  the add's landing in `PendA` (`hX`);
- `pendA_of_selfN`: `hX` at `IN ar L0 ls0 J` for a family containing
  `StartsS … (Sg2 …)`: the landing pairs carry their own segment
  (`selfN_of`, `selfN_mem`).

Where x86-64 differs from AArch64: the allocator's frame holds the return
address (the region `R.lo ≤ -160`, `8 ≤ R.hi`, 8-aligned); the system call
is `syscall`; its entry is `Spike.Lib.X64.Alloc.fnL`.
-/
import Spike.Lib.LowerX64.AllocW2W2
import Spike.Lib.X64AllocGAb
import Spike.Lib.X64AllocGSt
import Spike.Lib.X64SetupPlaced
import Spike.Lib.X64CtrRow
import Spike.Lib.X64PlacedSE
import Spike.Lib.LowerX64.Levels2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region FrameRun MemSide)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (BlkW NodeW At ND okBlk CodeAt holdCtr DFrame)
open Spike.Lib.X64.Rt (InstOk cellOf)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.WriteAb (Ab abPcs)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.X64.Alloc (Call AllocW N iCtr iHeap iRmw iHdr iRet fnL bPro_ok bChk_ok bJ1_ok bC1_ok bC2_ok
  bJ2_ok bSlow_ok bJ3_ok bFull_ok bO0_ok bO1_ok bO2_ok bO3_ok bO4_ok bO5_ok bO6_ok bO7_ok bO8_ok bO9_ok)
open Spike.Lib.X64.AllocG (allocIn_spec allocSt allocAb allocArena allocCtr allocPc allocPhOk allocAbOk)

section Alloc

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region}
  {F : MachineData → Prop} {ms : MemSide isa} {q : Call}

/-- **A single instruction other than a `syscall` is off a system call.** -/
theorem nodeW_noSys1 (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {d : Directive} {z : Nat} {l : Label} {off : Nat} (hb : Scc.Cert.Rt.X64.blockAtB cells l off [(d, z)] = true)
    (he : lab l + Int64.ofNat off = n.pc) (hd : ∀ w w', d ≠ .instr (.regular w w' .syscall)) :
    NodeW (fun s _ => abi.atSys s = false) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, -⟩
  exact ⟨atSyscall_false_of_cellAt (cellOf hI hb he hs hn hpc) hd, fun _ h => h⟩

/-- **A covered block at its label is off a system call** (`blkW_noSys'`). -/
theorem blkW_noSysB (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {blk : List (Directive × Nat)} {l : Label} {off : Nat} {lo hi : Int}
    (hb : Scc.Cert.Rt.X64.blockAtB cells l off blk = true) (he : lab l + Int64.ofNat off = n.pc)
    (hok : okBlk lo hi n.o blk = true) :
    BlkW (fun s _ => abi.atSys s = false) (fun _ _ => False) exe endPc R F n blk :=
  blkW_noSys' (fun _ hs hn => he ▸ Spike.Lib.X64.Rt.codeOf hI hb hs hn) hok

set_option hygiene false in
/-- A covered block of `scc_rt_alloc` off a system call. -/
local macro "sblk " hb:term:max ok:term:max : tactic =>
  `(tactic| exact blkW_noSysB hI $hb (by pc_tac) $ok)

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc` off a system call. -/
local macro "ssi " hb:term:max : tactic =>
  `(tactic| exact nodeW_noSys1 hI $hb (by pc_tac) (fun _ _ h => by cases h))

/-- **No node of `scc_rt_alloc` is at a system call** (`blkW_noSysB`,
`nodeW_noSys1`). -/
theorem allocNoSys (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true) :
    AllocW ms q (fun s _ => abi.atSys s = false) (fun _ _ => False) exe endPc R F := by
  obtain ⟨-, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := allocIn_spec hA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hI.labOk]
  · sblk h0 bPro_ok
  · sblk h1 bChk_ok
  · sblk h2 bJ1_ok
  · ssi h3
  · sblk h4 bC1_ok
  · ssi h5
  · sblk h6 bC2_ok
  · sblk h7 bJ2_ok
  · sblk h8 bSlow_ok
  · sblk h9 bJ3_ok
  · sblk h10 bFull_ok
  · sblk h11 bO0_ok
  · ssi h12
  · sblk h13 bO1_ok
  · ssi h14
  · sblk h15 bO2_ok
  · ssi h16
  · sblk h17 bO3_ok
  · ssi h18
  · sblk h19 bO4_ok
  · ssi h20
  · sblk h21 bO5_ok
  · ssi h22
  · sblk h23 bO6_ok
  · ssi h24
  · sblk h25 bO7_ok
  · ssi h26
  · sblk h27 bO8_ok
  · ssi h28
  · sblk h29 bO9_ok
  · ssi h30

omit [Kraken.Executable.ValidLayout exe] in
/-- **At the call's control or its hold**, for a call `q` with its premises
(`hq`) and its control free of `ZBad` at the frames `fs` under `F`
(`hG0F`): `main`'s `ret` is excluded (the term a buffer allocation), `ZBad`
too (the hold keeps the term), and every frame run stays put (`FrameRun.eq_of_newBuf`). -/
theorem allocCtl {p : Prog} {fs : List TermRun.Frame}
    (hq : ∀ m, F m → q.OK ms (_root_.Executable.labels exe).label) (hG0F : ∀ m, F m → FrOk2 q.c0 fs) :
    AllocW ms q (fun _ c => (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs ∧
      ∀ c' fs', FrameRun p (c, fs) (c', fs') → c' = c ∧ fs' = fs) (fun _ _ => False) exe endPc R F :=
  Spike.Lib.X64SetupPlaced.allocW_of_ctl fun m0 hF _ c _ hc => by
    have hq' := hq m0 hF
    have hte : c.term = q.c0.term ∧ c.env = q.c0.env := by
      rcases hc with rfl | ⟨o, rfl⟩ <;> exact ⟨rfl, rfl⟩
    have ht : c.term = .let_ q.x (.newBuf q.a q.τ) q.e := hte.1.trans hq'.term
    have hev : TermRun.evalAt c.env q.a = some (q.ta, q.ws) := by rw [hte.2]; exact hq'.ev
    refine ⟨fun _ a h => ?_, ⟨hte.1 ▸ (hG0F m0 hF).1, (hG0F m0 hF).2⟩, fun c' fs' hr => ?_⟩
    · rw [ht] at h; cases h
    · cases Spike.Lib.X64ConsumerA.FrameRun.eq_of_newBuf hr ht hev hq'.num
      exact ⟨rfl, rfl⟩

/-- **The counter add's row landing in `X`** (`allocW2`'s `hctx`) from the
allocator's next nodes in `X` (`hX`): `ctrRow_alloc` at the allocator's
code, for a call `q` with its premises (`hq`), the counter unmapped under
the stable frame condition (`hF`, `hmc`). -/
theorem allocCtx_of (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true) (hF : Spike.Lib.X64.FStable R F)
    (hq : ∀ m, F m → q.OK ms lab) (hmc : ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none)
    {lbl0 : WeakMem.AllocLabel → Option Nat} {X : Spike.Lib.Frag isa}
    (hX : ∀ s c, Spike.Lib.X64.Next exe endPc R F (N lab ms q) (Spike.Lib.X64.Alloc.E lab ms q lbl0) s c →
      X s c) :
    ∀ s c, At exe endPc R F (N lab ms q .rmw) s c → CtrRow ms X s c := by
  intro s c hAt
  have hlab := hI.labOk
  subst hlab
  have hq' : q.OK ms (_root_.Executable.labels exe).label := by
    obtain ⟨-, -, -, -, σ, -, hD, -⟩ := hAt
    exact hq _ hD
  obtain ⟨k, op, g, x, a, τ, e, ta, ws, n, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    Spike.Lib.X64.Alloc.ctrRow_alloc (lbl := lbl0) hI.lays hI.endOk hA hF hq' hmc hAt
  exact ⟨k, op, g, x, a, τ, e, ta, ws, n, h1, h2, h3, h4, h5, h6, h7, h8, fun old hG hown hle hlo =>
    (h9 old hG hown hle hlo).imp_right (hX _ _)⟩

omit [Kraken.Executable.ValidLayout exe] in
open Spike.Lib.X64 Spike.Lib.X64.Alloc Spike.Lib.X64.Flow in
open Scc.Cert.Rt.X64 (Lays endOf code_field) in
/-- **`CtrRow` at `scc_rt_alloc`'s counter add landing at the next node**
(`ctrRow_alloc` with the landing exactly the node after the add, x86-64's
`.c2`, the old count held; no exit): the row's landing is the add's only
successor. On x86-64 the held node is `.c2` (the A64 twin's `.n4`; the name kept). -/
theorem ctrRow_alloc_n4 [Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : allocIn cells = true) (hF : Spike.Lib.X64.FStable R F)
    (hq : q.OK ms (_root_.Executable.labels exe).label)
    (hmem : ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none)
    {s : State} {c : Ctl} (hAt : At exe endPc R F (N (_root_.Executable.labels exe).label ms q .rmw) s c) :
    CtrRow ms (Spike.Lib.X64.Next exe endPc R F (fun _ : Unit => N (_root_.Executable.labels exe).label ms q .c2)
      (fun x : Empty => x.elim)) s c := by
  have hin' := hin
  simp only [allocIn, fiAt, iCtr, iHeap, iRmw, iHdr, iRet, Bool.and_eq_true] at hin'
  refine ctrRow_nd (b := .rcx) (k := 0) (r := .rax) (z := 5) (by decide) hF
    (code_field hp hend (by simp only [hin']) (l := cntL) (off := 19) rfl) (fun m σ c _ hD hJ => ?_) hAt
  obtain ⟨⟨rfl, hFr, hn28⟩, hcx, hax⟩ := hJ
  have hb : bAddr σ.regs .rcx 0 = BitVec.ofNat 64 ms.ctr := by
    rw [← hq.ctr, ← hcx]; simp [bAddr, Reg64s.get64]
  rw [hb]
  refine ⟨rfl, hq.rt, hq.mp, hmem _ hD, q.x, q.a, q.τ, q.e, q.ta, q.ws, q.n, hq.term, hq.ev,
    hq.num, hq.hold, by exact hax, fun old hG hle hlo => ⟨hq.grow old hG hle, fun fl =>
      .inl ⟨(), ofNat_add' _ 19 5, rfl, _, rfl, hle, hFr, hn28, ?_, hlo⟩⟩⟩
  simp [ownStep, Reg64s.set64]

/-- **The counter add's row landing in `X`** (`allocW2`'s `hctx`) from the
allocator's node after the add (`.c2`) in `X` (`hX`; `ctrRow_alloc_n4`):
only the add's landing, the old count held, must be in `X`, and only at
`fsBase = tp`: the add keeps `fsBase` (`exec_tp`). On x86-64 the
held node is `.c2` (the A64 twin's `.n4`; the name kept). -/
theorem allocCtx_n4 (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true) (hF : Spike.Lib.X64.FStable R F)
    (hq : ∀ m, F m → q.OK ms lab) (hmc : ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none)
    {X : Spike.Lib.Frag isa} {tp : UInt64}
    (hX : ∀ s c, At exe endPc R F (N lab ms q .c2) s c → Spike.Lib.X64.KeepTP.TP tp s → X s c) :
    ∀ s c, At exe endPc R F (N lab ms q .rmw) s c → Spike.Lib.X64.KeepTP.TP tp s → CtrRow ms X s c := by
  intro s c hAt hT
  have hlab := hI.labOk
  subst hlab
  have hq' : q.OK ms (_root_.Executable.labels exe).label := by
    obtain ⟨-, -, -, -, σ, -, hD, -⟩ := hAt
    exact hq _ hD
  obtain ⟨k, op, g, x, a, τ, e, ta, ws, n, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    ctrRow_alloc_n4 hI.lays hI.endOk hA hF hq' hmc hAt
  refine ⟨k, op, g, x, a, τ, e, ta, ws, n, h1, h2, h3, h4, h5, h6, h7, h8, fun old hG hown hle hlo => ?_⟩
  obtain ⟨hG', hL⟩ := h9 old hG hown hle hlo
  refine ⟨hG', hX _ _ ?_ (Spike.Lib.X64.KeepTP.exec_tp hT h1 old)⟩
  rcases hL with ⟨_, hj⟩ | ⟨y, _⟩
  · exact hj
  · exact y.elim

/-- **Every node of `scc_rt_alloc` inside `W2`** at the frames `fs`, any
write tail `Dt`, none moved by `K`, for a call `q` with its premises
(`hq`) returning into the entry's phase off the write abort (`hra`,
`hraAb`), its control free of `ZBad` (`hG0F`), in a region of the
allocator's frame (8-aligned) whose frame condition gives the stack range
off it (`hFO`): the allocator's code (`hA`) passing the phase and the write
abort's checks (`hph`, `habk`), the owned words factoring through the phase
(`hown`), the memory side's writable words mapped (`hmp`), the arena's
counter, base and offsets (`hctr`, `hheap`, `hoff`, the counter below the
heap, `hlt`, `h64`), the counter and every header the code may store
unmapped in private memory and owned at no phase (`hmem`, `hno`); the
counter add's states at `fsBase = tp` in `CtrRow` at the frames' memory
side landing in `PendA` (`hctx`), the controls and frames placed at every
state a frame of the region reaches (`hP`); the states are asked inside
`W2` only at `fsBase = tp` (the caller's `%fs` base, kept along the call by
`SegW.keepTP'`). The node's states are off a system call
(`allocNoSys`) and off the abort sites (`allocPc`); a frame run stays put
(`allocCtl`), so the arena's writes are `ArenaWr0`'s and the counter's
`allocCtr`'s. -/
theorem allocW2 (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true) (hph : allocPhOk okPc ph lab = true)
    (habk : allocAbOk lab = true) {Λ : Scc.Sem.Layout} {rS : Range} {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hq : ∀ m, F m → q.OK ms lab)
    (hra : ph (Int64.ofBitVec q.ra).toBitVec.toNat = ph (lab fnL).toBitVec.toNat)
    (hraAb : Int64.ofBitVec q.ra ∉ abPcs lab)
    (hmp : ∀ L, ms.mp L true → Kernel.mapped (K0 Λ) true L = true)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j)
    {ar : Arena} (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64)
    {p : Prog} (hp : ProgNoS ZBad p) {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {Jv : InvS}
    {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}
    (hG0F : ∀ m, F m → FrOk2 q.c0 fs)
    (hP : ∀ m0, F m0 → ∀ (s : State) c, DFrame R m0 s.st.1 → (c = q.c0 ∨ ∃ o, c = holdCtr ms q.c0 o) →
      Placed Λ lbl s c ∧ FramesPlaced Λ lbl s fs)
    {tp : UInt64}
    (hctx : ∀ s c, At exe endPc R F (N lab ms q .rmw) s c → Spike.Lib.X64.KeepTP.TP tp s →
      CtrRow (msOfA Λ μ rd G (fun s _ => own s) ar Jv lbl lsize fs)
        (fun s' c'' => PendA p Jv lbl lsize s' c'' fs) s c) :
    AllocW ms q (fun s c => Spike.Lib.X64.KeepTP.TP tp s →
      W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F := by
  have hSt := allocSt (Λ := Λ) (rS := rS) hI hA hph hown hR hR8 hlo hhi hl hh hsub hfit hFO hq hra hmp hmem hno
  have hAb := allocAb hI hA hph habk hR hlo hhi hq hra hraAb hmem
  have hAr := allocArena (lbl := lbl) (p := p) hI hA hR hlo hhi hq hmem hctr hheap hoff
  have hCt := allocCtr (Ctx := fun s c => Spike.Lib.X64.KeepTP.TP tp s →
      CtrRow (msOfA Λ μ rd G (fun s _ => own s) ar Jv lbl lsize fs)
      (fun s' c'' => PendA p Jv lbl lsize s' c'' fs) s c) hI hA hR hlo hhi hq
    (fun a h m hm => hmem a (.inr h) m hm) hheap hlt h64 hctx
  have hPl := Spike.Lib.X64SetupPlaced.allocPlacedS (exe := exe) (endPc := endPc) (fs := fs) hP
  have hPc := allocPc (ms := ms) (q := q) (R := R) (F := F) hI hph
  have hNs := allocNoSys (ms := ms) (q := q) (R := R) (F := F) hI hA
  have hCl := allocCtl (exe := exe) (endPc := endPc) (R := R) (p := p) (fun m h => by rw [hI.labOk]; exact hq m h) hG0F
  refine Spike.Lib.X64.AllocG.AllocW.imp (Spike.Lib.X64.AllocG.AllocW.imp (Spike.Lib.X64.AllocG.AllocW.imp
    (Spike.Lib.X64.AllocG.AllocW.imp (Spike.Lib.X64.AllocG.AllocW.imp (Spike.Lib.X64.AllocG.AllocW.imp
    (Spike.Lib.X64.AllocG.AllocW.imp hSt hAb fun _ _ => And.intro) hAr fun _ _ => And.intro) hCt
    fun _ _ => And.intro) hPl fun _ _ => And.intro) hPc fun _ _ => And.intro) hNs fun _ _ => And.intro) hCl ?_
  rintro s c ⟨⟨⟨⟨⟨⟨hst, hab⟩, har⟩, hct⟩, hpl⟩, hpc⟩, hns⟩ ⟨hnr, hf, hrun⟩ hT
  refine w2_of hp hf (hst.dt_mono fun _ h => h.elim) hab hnr (.of_placedS hpl) (fun c' fs' hr _ => ?_)
    (abortOkA_of_ne (hI.off s hpc).1.noAbort) (fun h => absurd h (by rw [hns]; decide))
  obtain ⟨rfl, rfl⟩ := hrun c' fs' hr
  exact ⟨fun L hL => (Classical.em (L = ar.ctrLoc)).elim .inl fun hne => har _ _ _ hr L hL hne lsize,
    fun hw => hct hw hT⟩

end Alloc

/-! ## The placement in the call's context -/

section Place

open Spike.Lib.X64 (FStable CKept Abs)
open Spike.Lib.X64.Flow.NewBuf (AllocCtx nbJc)
open Spike.Lib.X64.Flow.Ret0 (CallerCells)
open Spike.Lib.LowerNode (SlotRepAt)

/-- **The call's controls and the frames placed in the call's context**
(`allocW2`'s `hP`) at the allocator's region `R.callee (-size - 8) (-160) 8`
under `AllocW2`'s frame condition: the call's control the caller's at the
`callq` (`AllocCtx`, `nbJc` past `J1`; the `callq` writes only the return
address's cell below the frame, `arun_callq`), placed in the caller's slot
file (`hJ1`), each slot a caller cell outside the allocator's region
(`rsOf_bounds`) kept by the call (`CKept`) and by the allocator's frame
(`Region.callee_sep`); the hold keeps the term and the environment; the
frames placed under the caller's frame condition (`hfp`), stable under the
allocator's writes (`FStable.callee`). -/
theorem allocHP {Λ : Scc.Sem.Layout} {lbl : Lbl} {fs : List TermRun.Frame} {R : Region}
    {F : MachineData → Prop} {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h16 : fr.size % 16 = 0) (hR : R.OK)
    (hlo : R.lo ≤ -(fr.size : Int) - 8 - 160) (hhi : 0 ≤ R.hi) (hFS : FStable R F)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {ms : MemSide isa} {L : Label → Int64} {pcB : Int64} {zc : Nat} {J1 : Spike.Lib.X64.AS → Ctl → Prop}
    {q : Call} (hJ1 : ∀ σ c, J1 σ c → SlotRepAt Λ.imms lbl (rsOf fr) σ.slot c) :
    ∀ m0, (F m0 ∧ CallerCells R (-(fr.size : Int) - 8) (-160) 8 m0 ∧
        AllocCtx ms L R fr.size
          (nbJc L [(Scc.Emit.X64.i64 (.call (Scc.Emit.X64.rel Scc.Lower.Names.alloc)), zc)] pcB (oB fr) J1) q m0) →
      ∀ (s : State) c, DFrame (R.callee (-(fr.size : Int) - 8) (-160) 8) m0 s.st.1 →
        (c = q.c0 ∨ ∃ o, c = holdCtr ms q.c0 o) → Placed Λ lbl s c ∧ FramesPlaced Λ lbl s fs := by
  rintro m0 ⟨hF0, -, mC, σC, c1, hA, ⟨σ0, hJ, hσC⟩, hN, hk⟩ s c hD hc
  have hc1 : c1 = q.c0 := hN.1
  have hout : ∀ r k, rsOf fr r = some k →
      R.Off k ∧ ¬ (R.callee (-(fr.size : Int) - 8) (-160) 8).Off (k - (-(fr.size : Int) - 8)) := by
    intro r k hk'
    obtain ⟨hk1, hk2, hk3⟩ := rsOf_bounds hf hk'
    simp only [Region.Off, Region.callee]
    omega
  have hσs : ∀ r k, rsOf fr r = some k → σC.slot k = σ0.slot k := by
    intro r k hk'
    obtain ⟨hk1, -, hk3⟩ := rsOf_bounds hf hk'
    rw [hσC, arun_callq]
    simp only [oB, Spike.Lib.upd_apply]
    split <;> first | rfl | omega
  have hP : Placed Λ lbl s q.c0 := by
    refine placed_of_slotRep (pf := fun k => .slot (R.addr k).toNat) (hc1 ▸ hJ1 σ0 c1 hJ) fun r k hk' => ?_
    obtain ⟨ho1, ho2⟩ := hout r k hk'
    obtain ⟨j, hj, he⟩ := hA.slot k ho1
    have hsep := Region.callee_sep (hR := hR) (by omega) (by decide) (by omega) (by omega) (by decide)
      (by decide) ho1 ho2
    have hl : Mem.loadInt s.st.1.dmem (R.addr k) 8 = some j :=
      (hD _ (Region.addr_fit hR ho1) hsep).trans ((hk k ho1 ho2).trans hj)
    show (privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, ← hσs r k hk']
    simp only [privLoad, hl, Option.map_some, he]
  refine ⟨?_, ?_⟩
  · rcases hc with rfl | ⟨o, rfl⟩
    · exact hP
    · exact hP
  · have hFs : F s.st.1 := Spike.Lib.X64.FStable.callee hR (by omega) (by decide) (by omega) (by omega)
      hFS m0 s.st.1 hF0 hD
    exact (hfp s hFs).choose_spec.toFramesPlaced

open Spike.Lib.LowerNode (LocBaseRegAt ImmIn ofEnv2) in
open Spike.Lib.Form (lookupS) in
/-- **The call's source relation placed in the slot file** (`allocHP`'s
`hJ1` at `nbJ1`) from the walk's facts at the allocation's `let` `t`
(`SlotRepAt.of_nodeJE`). -/
theorem slotRep_nbJ1 {Λ : Scc.Sem.Layout} {p : Prog} {lbl : Lbl} {lsize : Lsize} {fr : Scc.Emit.X64.Frame}
    {R : Region} {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {t : Expr} {env : Scc.Lower.Env}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {a0 a1 a2 : Scc.IR.Operand}
    (htot : ∀ y ∈ Scc.Sem.exprFv t, (lookupS (ofEnv2 env) y).isSome) (hlb : LocBaseRegAt (ofEnv2 env) t)
    (himm : ImmIn Λ.imms (ofEnv2 env) t) :
    ∀ σ c, nbJ1 p lbl lsize fr R fp ra tp c0 t env lits cs bufs a0 a1 a2 σ c →
      SlotRepAt Λ.imms lbl (rsOf fr) σ.slot c := by
  rintro σ c ⟨-, -, -, -, -, -, -, L', sm, B, hj, -⟩
  exact SlotRepAt.of_nodeJE hj htot hlb himm

end Place

/-! ## At the rows' memory side -/

section Bridge

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : OwnS} {ar : Arena} {I : InvS} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}

/-- **The rows' memory side `msOfAX` is `msOfA`'s but for the byte step
and the write abort's justification** (`msOfAB` is `withBW`): every other
field agrees, at either phase `ab`. -/
theorem msOfAX_fields (ab : Option (State → Prop)) :
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).rd = (msOfA Λ μ rd G own ar I lbl lsize fs).rd ∧
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).rt = (msOfA Λ μ rd G own ar I lbl lsize fs).rt ∧
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).K = (msOfA Λ μ rd G own ar I lbl lsize fs).K ∧
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).G = (msOfA Λ μ rd G own ar I lbl lsize fs).G ∧
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).heap = ar.heap ∧
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).ctr = ar.ctr ∧
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).units = ar.units ∧
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).off = ar.off ∧
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).cells = ar.cells ∧
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).own = (msOfA Λ μ rd G own ar I lbl lsize fs).own ∧
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).mp = (msOfA Λ μ rd G own ar I lbl lsize fs).mp ∧
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).abortAt = (msOfA Λ μ rd G own ar I lbl lsize fs).abortAt ∧
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).pl = (msOfA Λ μ rd G own ar I lbl lsize fs).pl ∧
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).xa = (msOfA Λ μ rd G own ar I lbl lsize fs).xa := by
  cases ab <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The rows' memory side maps only kernel-mapped words** (`msOfA`'s
`mp`). -/
theorem msOfAX_mp {ab : Option (State → Prop)} {L : Loc}
    (h : (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).mp L true) : Kernel.mapped (K0 Λ) true L = true := by
  cases ab <;> exact h.1

/-- **`CtrRow` at the rows' memory side is `CtrRow` at `msOfA`'s** (it
reads neither the byte step nor the write abort's justification). -/
theorem ctrRow_msOfAX {ab : Option (State → Prop)} {X : Spike.Lib.Frag isa} {s : State} {c : Ctl}
    (h : CtrRow (msOfAX Λ μ p rd G own ar I ab lbl lsize fs) X s c) :
    CtrRow (msOfA Λ μ rd G own ar I lbl lsize fs) X s c := by
  cases ab <;> exact h

end Bridge

section AllocX

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region}
  {F : MachineData → Prop} {q : Call}

/-- **`allocW2` at the rows' memory side** `msOfAX … ab` (`AllocW2`'s `ms`
at `landStk_hxa`'s instance): the arena's fields and the mapped words by
`msOfAX_fields`, `msOfAX_mp`; the counter add's row from the allocator's
node after the add (`.c2`) in `PendA` (`hX`, `allocCtx_n4`, `ctrRow_msOfAX`), the counter
unmapped under the stable frame condition (`hFS`, `hmem`). -/
theorem allocW2X (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true) (hph : allocPhOk okPc ph lab = true)
    (habk : allocAbOk lab = true) {Λ : Scc.Sem.Layout} {rS : Range} {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : Spike.Lib.X64.FStable R F)
    {p : Prog} (hp : ProgNoS ZBad p) {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena}
    {Jv : InvS} {ab : Option (State → Prop)} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}
    {fs : List TermRun.Frame}
    (hq : ∀ m, F m → q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) lab)
    (hra : ph (Int64.ofBitVec q.ra).toBitVec.toNat = ph (lab fnL).toBitVec.toNat)
    (hraAb : Int64.ofBitVec q.ra ∉ abPcs lab)
    (hmem : ∀ a : BitVec 64, (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ a : BitVec 64, (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j)
    (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) (hG0F : ∀ m, F m → FrOk2 q.c0 fs)
    (hP : ∀ m0, F m0 → ∀ (s : State) c, DFrame R m0 s.st.1 →
      (c = q.c0 ∨ ∃ o, c = holdCtr (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) q.c0 o) →
      Placed Λ lbl s c ∧ FramesPlaced Λ lbl s fs)
    {tp : UInt64}
    (hX : ∀ s c, At exe endPc R F (N lab (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) q .c2) s c →
      Spike.Lib.X64.KeepTP.TP tp s → PendA p Jv lbl lsize s c fs) :
    AllocW (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) q
      (fun s c => Spike.Lib.X64.KeepTP.TP tp s → W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe
      endPc R F := by
  obtain ⟨-, -, -, -, hheap, hctr, hunits, hoff, hcells, -⟩ :=
    msOfAX_fields (Λ := Λ) (μ := μ) (p := p) (rd := rd) (G := G) (own := fun s _ => own s) (ar := ar) (I := Jv)
      (lbl := lbl) (lsize := lsize) (fs := fs) ab
  have hmem' : ∀ a : BitVec 64, (a = BitVec.ofNat 64 (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs).ctr ∨
      ∃ o, o + (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs).units q.n q.τ ≤
        (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs).cells ∧
        a.toNat = q.hdrAt (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none := by
    rw [hctr, hunits, hcells]; exact hmem
  have hno' : ∀ a : BitVec 64, (a = BitVec.ofNat 64 (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs).ctr ∨
      ∃ o, o + (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs).units q.n q.τ ≤
        (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs).cells ∧
        a.toNat = q.hdrAt (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j := by
    rw [hctr, hunits, hcells]; exact hno
  exact allocW2 hI hA hph habk hown hR hR8 hlo hhi hl hh hsub hfit hFO hq hra hraAb (fun L h => msOfAX_mp h)
    hmem' hno' hctr hheap (fun k τ => by rw [hoff]) hlt h64 hp hG0F hP
    (fun s c hAt hT => ctrRow_msOfAX
      (allocCtx_n4 hI hA hFS hq (fun m hm => hmem' _ (.inl rfl) m hm) hX s c hAt hT))

end AllocX

/-! ## The counter add's landing in the family -/

section Self

open Spike.Lib.AllocReach (Reach IN)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {ar : Arena} {L0 : Lbl} {ls0 : Lsize} {rS : Range} {Tk : State → Prop} {a : Int64}
  {Dt Ab : State → Prop} {ab : Option (State → Prop)}

/-- **The counter add's landing pends into the family** (`allocW2X`'s `hX`
at `Jv := IN ar L0 ls0 J`): at a family `J` containing the starts with the
self-segment pairs (`StartsS … (Sg2 …)`, `hJ`), at a reachable placement
(`hR`), every pair of `X` (the add's landing) is in an entry `Q` (`hq`)
from which, at every family containing the starts, the levels' segment
inside `W2` holds (`hQ`, the start's tail), so it carries its own segment
(`selfN_of`) and is in `J` (`selfN_mem`); `main`'s `ret` excluded at no
frame (`hnr`). -/
theorem pendA_of_selfN {S0 : FragS isa} {E : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {J : InvS}
    (hJ : ∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs,
      StartsS ar L0 ls0 (Sg2 Λ μ p rd G own rS Tk ar L0 ls0 Dt Ab a ab) S0 E L ls s c fs → J L ls s c fs)
    {lbl : Lbl} {lsize : Lsize} (hR : Reach ar L0 ls0 lbl lsize) {Q : FragS isa}
    (hQ : ∀ J' : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 E L ls s c fs →
        J' L ls s c fs) → Sg2 Λ μ p rd G own rS Tk ar L0 ls0 Dt Ab a ab J' lbl lsize Q)
    {X : Spike.Lib.Frag isa} {fs : List TermRun.Frame} (hq : ∀ s c, X s c → Q s c fs)
    (hnr : ∀ s c, X s c → fs = [] → ∀ a, c.term ≠ .ret a) :
    ∀ s c, X s c → PendA p (IN ar L0 ls0 J) lbl lsize s c fs := fun s c hx =>
  ⟨hnr s c hx, Spike.Lib.Pend.of ⟨hR, selfN_mem hJ
    (selfN_of (fun _ _ _ _ _ h sg => sg.mono_pre h) hR hQ (hq s c hx))⟩⟩

end Self

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.nodeW_noSys1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.nodeW_noSys1

/-- info: 'Spike.Lib.LowerX64.allocNoSys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocNoSys

/-- info: 'Spike.Lib.LowerX64.allocCtl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocCtl

/-- info: 'Spike.Lib.LowerX64.allocCtx_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocCtx_of

/-- info: 'Spike.Lib.LowerX64.ctrRow_alloc_n4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.ctrRow_alloc_n4

/-- info: 'Spike.Lib.LowerX64.allocCtx_n4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocCtx_n4

/-- info: 'Spike.Lib.LowerX64.allocW2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocW2

/-- info: 'Spike.Lib.LowerX64.allocHP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocHP

/-- info: 'Spike.Lib.LowerX64.slotRep_nbJ1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.slotRep_nbJ1

/-- info: 'Spike.Lib.LowerX64.msOfAX_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.msOfAX_fields

/-- info: 'Spike.Lib.LowerX64.msOfAX_mp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.msOfAX_mp

/-- info: 'Spike.Lib.LowerX64.ctrRow_msOfAX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.ctrRow_msOfAX

/-- info: 'Spike.Lib.LowerX64.allocW2X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocW2X

/-- info: 'Spike.Lib.LowerX64.pendA_of_selfN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.pendA_of_selfN
