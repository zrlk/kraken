/-
**`scc_rt_alloc`'s states inside `W2`** (AArch64): `AllocW2`'s allocator
field (`Spike/Lib/LowerA64/NewBufC2.lean`) at `W₀ := W2`
(`Spike/Lib/LowerA64/SFactsA2.lean`), from the allocator's components
(`Spike/Lib/A64AllocG*.lean`, `Spike/Lib/A64SetupPlaced.lean`): the state's
facts (`allocSt`), the write abort's phase (`allocAb`), the arena's writes
(`allocArena`), the counter's write in its context (`allocCtr`), the
frames placed (`allocPlacedS`), the abort sites off the marks (`allocPc`).

- `allocNoSys`: no node of `scc_rt_alloc` is at a system call (every
  instruction covered or a single non-`svc` one);
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
  the node `n4` (the old count held);
- `allocW2X`: `allocW2` at `msOfAX … ab`, the counter's context reduced to
  the add's landing at `n4` in `PendA` (`hX`);
- `pendA_of_selfN`: `hX` at `IN ar L0 ls0 J` for a family containing
  `StartsS … (Sg2 …)`: the landing pairs carry their own segment
  (`selfN_of`, `selfN_mem`).
-/
import Spike.Lib.LowerA64.AllocW2W2
import Spike.Lib.A64AllocGAb
import Spike.Lib.A64SetupPlaced
import Spike.Lib.A64CtrRow
import Spike.Lib.LowerA64.Levels2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region FrameRun MemSide)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (BlkW NodeW At holdCtr DFrame)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.WriteAb (Ab abPcs)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.A64.Alloc (Call AllocW N iAdrpC iAddC iAdrpH iAddH iRmw iHdr iRet b0 b1 b2 b3 b4 b5 b6 b7 b9 b11
  b12 b13 b0_ok b1_ok b2_ok b3_ok b4_ok b5_ok b6_ok b7_ok b9_ok b11_ok b12_ok b13_ok)
open Spike.Lib.A64.AllocG (allocIn_spec allocSt allocAb allocArena allocCtr allocPc allocPhOk allocAbOk)
open Spike.Lib.A64.KeepTP (TP)

section Alloc

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region}
  {F : MachineData → Prop} {ms : MemSide isaLSE2} {q : Call}

/-- **A single instruction other than an `svc` is off a system call.** -/
theorem nodeW_noSys1 (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : Spike.Lib.A64.Flow.ND}
    {d : Directive} {l : Label} {k : Nat} {p : Int64} (hb : Scc.Cert.Rt.A64.blockAt prog l k [d] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p) (hd : ∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) :
    NodeW (fun s _ => abi.atSys s = false) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, -⟩
  rw [hp] at hpc
  exact ⟨Scc.Sem.A64.atSvc_false_of_cellAt (Spike.Lib.A64.Rt.cellOf hI hb he hs hn hpc) hd, fun _ h => h⟩

set_option hygiene false in
/-- A covered block of `scc_rt_alloc` off a system call. -/
local macro "sblk " hb:term:max ok:term:max : tactic =>
  `(tactic| exact blkW_noSys hI $hb (by pc_tac) $ok)

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc` off a system call. -/
local macro "ssi " hb:term:max : tactic =>
  `(tactic| exact nodeW_noSys1 hI $hb (by pc_tac) rfl (fun _ h => by cases h))

/-- **No node of `scc_rt_alloc` is at a system call** (`blkW_noSys`,
`nodeW_noSys1`). -/
theorem allocNoSys (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true) :
    AllocW ms q (fun s _ => abi.atSys s = false) (fun _ _ => False) exe endPc R F := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, -⟩ :=
    allocIn_spec hA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hI.labOk]
  · sblk h0 b0_ok
  · sblk h1 b1_ok
  · sblk h2 b2_ok
  · ssi h3
  · ssi h4
  · sblk h5 b3_ok
  · ssi h6
  · sblk h7 b4_ok
  · sblk h8 b5_ok
  · sblk h9 b6_ok
  · sblk h10 b7_ok
  · sblk h11 b9_ok
  · sblk h12 b11_ok
  · ssi h13
  · ssi h14
  · sblk h15 b12_ok
  · ssi h16
  · sblk h17 b13_ok
  · ssi h18

omit [Kraken.Executable.ValidLayout exe] in
/-- **At the call's control or its hold**, for a call `q` with its premises
(`hq`) and its control free of `ZBad` at the frames `fs` under `F`
(`hG0F`): `main`'s `ret` is excluded (the term a buffer allocation), `ZBad`
too (the hold keeps the term), and every frame run stays put (`FrameRun.eq_of_newBuf`). -/
theorem allocCtl {p : Prog} {fs : List TermRun.Frame}
    (hq : ∀ m, F m → q.OK ms (_root_.Executable.labels exe).label) (hG0F : ∀ m, F m → FrOk2 q.c0 fs) :
    AllocW ms q (fun _ c => (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs ∧
      ∀ c' fs', FrameRun p (c, fs) (c', fs') → c' = c ∧ fs' = fs) (fun _ _ => False) exe endPc R F :=
  Spike.Lib.A64SetupPlaced.allocW_of_ctl fun m0 hF _ c _ hc => by
    have hq' := hq m0 hF
    have hte : c.term = q.c0.term ∧ c.env = q.c0.env := by
      rcases hc with rfl | ⟨o, rfl⟩ <;> exact ⟨rfl, rfl⟩
    have ht : c.term = .let_ q.x (.newBuf q.a q.τ) q.e := hte.1.trans hq'.term
    have hev : TermRun.evalAt c.env q.a = some (q.ta, q.ws) := by rw [hte.2]; exact hq'.ev
    refine ⟨fun _ a h => ?_, ⟨hte.1 ▸ (hG0F m0 hF).1, (hG0F m0 hF).2⟩, fun c' fs' hr => ?_⟩
    · rw [ht] at h; cases h
    · cases Spike.Lib.A64ConsumerA.FrameRun.eq_of_newBuf hr ht hev hq'.num
      exact ⟨rfl, rfl⟩

/-- **The counter add's row landing in `X`** (`allocW2`'s `hctx`) from the
allocator's next nodes in `X` (`hX`): `ctrRow_alloc` at the allocator's
code (`alloc_code_of`), for a call `q` with its premises (`hq`), the
counter unmapped under the stable frame condition (`hF`, `hmc`). -/
theorem allocCtx_of (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true) (hF : Spike.Lib.A64.Flow.FStable R F)
    (hq : ∀ m, F m → q.OK ms lab) (hmc : ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none)
    {lbl0 : WeakMem.AllocLabel → Option Nat} {X : Spike.Lib.Frag isaLSE2}
    (hX : ∀ s c, Spike.Lib.A64.Flow.Next exe endPc R F (N lab ms q) (Spike.Lib.A64.Alloc.E lab ms q lbl0) s c →
      X s c) :
    ∀ s c, At exe endPc R F (N lab ms q .rmw) s c → CtrRow ms X s c := by
  intro s c hAt
  have hlab := hI.labOk
  subst hlab
  have hq' : q.OK ms (_root_.Executable.labels exe).label := by
    obtain ⟨-, -, -, -, σ, -, hD, -⟩ := hAt
    exact hq _ hD
  obtain ⟨k, op, g, x, a, τ, e, ta, ws, n, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    Spike.Lib.A64.Alloc.ctrRow_alloc (lbl := lbl0) hF hq' (Spike.Lib.A64.Flow.alloc_code_of hI.lays hI.endOk hA)
      (hmc) hAt
  exact ⟨k, op, g, x, a, τ, e, ta, ws, n, h1, h2, h3, h4, h5, h6, h7, h8, fun old hG hown hle =>
    (h9 old hG hown hle).imp_right (hX _ _)⟩

omit [Kraken.Executable.ValidLayout exe] in
open Spike.Lib.A64.Alloc in
/-- **`CtrRow` at `scc_rt_alloc`'s counter add landing at `n4`**
(`ctrRow_alloc` with the landing exactly the next node `n4`, the old count
held; no exit): the row's landing is the add's only successor. -/
theorem ctrRow_alloc_n4 (hF : Spike.Lib.A64.Flow.FStable R F)
    (hq : q.OK ms (_root_.Executable.labels exe).label) (hcode : Code ms q exe endPc)
    (hmem : ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none)
    {s : State} {c : Ctl} (hAt : At exe endPc R F (N (_root_.Executable.labels exe).label ms q .rmw) s c) :
    CtrRow ms (Spike.Lib.A64.Flow.Next exe endPc R F (fun _ : Unit => N (_root_.Executable.labels exe).label ms q .n4)
      (fun x : Empty => x.elim)) s c :=
  Spike.Lib.A64.Flow.ctrRow_nd hF (fun s he hn => hcode.rmw s he hn) (fun m σ c hA hD hJ => by
    obtain ⟨⟨rfl, hF, hn28⟩, h10, h9⟩ := hJ
    exact ⟨h10, hq.rt, hq.mp, hmem _ hD, q.x, q.a, q.τ, q.e, q.ta, q.ws, q.n, hq.term, hq.ev,
      hq.num, hq.hold, by rw [getRegOrZr_x]; exact h9, fun old hG hle =>
        ⟨hq.grow old hG hle, .inl ⟨(), rfl, rfl, _, rfl, hle, hF, hn28, rfl⟩⟩⟩) hAt

/-- **The counter add's row landing in `X`** (`allocW2`'s `hctx`) from the
allocator's node `n4` in `X` (`hX`; `ctrRow_alloc_n4`): only the add's
landing, the old count held, must be in `X`. -/
theorem allocCtx_n4 (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true) (hF : Spike.Lib.A64.Flow.FStable R F)
    (hq : ∀ m, F m → q.OK ms lab) (hmc : ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none)
    {tp : UInt64} {X : Spike.Lib.Frag isaLSE2}
    (hX : ∀ s c, At exe endPc R F (N lab ms q .n4) s c → TP tp s → X s c) :
    ∀ s c, At exe endPc R F (N lab ms q .rmw) s c → TP tp s → CtrRow ms X s c := by
  intro s c hAt htp
  have hlab := hI.labOk
  subst hlab
  have hq' : q.OK ms (_root_.Executable.labels exe).label := by
    obtain ⟨-, -, -, -, σ, -, hD, -⟩ := hAt
    exact hq _ hD
  have hcode := Spike.Lib.A64.Flow.alloc_code_of (ms := ms) (q := q) hI.lays hI.endOk hA
  obtain ⟨k, op, g, x, a, τ, e, ta, ws, n, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    ctrRow_alloc_n4 hF hq' hcode hmc hAt
  -- the add keeps the thread pointer
  have hT : ∀ v, TP tp (g v) := by
    obtain ⟨he, hn, -, hpc, -⟩ := hAt
    have hc := Spike.Lib.A64.Flow.noMsrAt_of_code (hcode.rmw s he hn) (by decide) (j := 0) (by decide) rfl rfl
      (by rw [hpc, Spike.Lib.A64.Flow.ofNat4_zero])
    exact Spike.Lib.A64.KeepTP.exec_tp hc htp h1
  refine ⟨k, op, g, x, a, τ, e, ta, ws, n, h1, h2, h3, h4, h5, h6, h7, h8, fun old hG hown hle => ?_⟩
  obtain ⟨hG', hL⟩ := h9 old hG hown hle
  refine ⟨hG', hX _ _ ?_ (hT old)⟩
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
counter add's states in `CtrRow` at the frames' memory side landing in
`PendA` (`hctx`), the controls and frames placed at every state a frame of
the region reaches (`hP`). The node's states are off a system call
(`allocNoSys`) and off the abort sites (`allocPc`); a frame run stays put
(`allocCtl`), so the arena's writes are `ArenaWr0`'s and the counter's
`allocCtr`'s. -/
theorem allocW2 (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true) (hph : allocPhOk okPc ph lab = true)
    (habk : allocAbOk lab = true) {Λ : Scc.Sem.Layout} {rS : Range} {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hq : ∀ m, F m → q.OK ms lab)
    (hra : ph (Int64.ofBitVec q.ra).toBitVec.toNat = ph (lab "scc_rt_alloc").toBitVec.toNat)
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
    {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame} (hG0F : ∀ m, F m → FrOk2 q.c0 fs)
    (hP : ∀ m0, F m0 → ∀ (s : State) c, DFrame R m0 s.st.1 → (c = q.c0 ∨ ∃ o, c = holdCtr ms q.c0 o) →
      Placed Λ lbl s c ∧ FramesPlaced Λ lbl s fs) {tp : UInt64}
    (hctx : ∀ s c, At exe endPc R F (N lab ms q .rmw) s c → TP tp s →
      CtrRow (msOfA Λ μ rd G (fun s _ => own s) ar Jv lbl lsize fs)
        (fun s' c'' => PendA p Jv lbl lsize s' c'' fs) s c) :
    AllocW ms q (fun s c => TP tp s → W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F := by
  have hSt := allocSt (Λ := Λ) (rS := rS) hI hA hph hown hR hal hlo hhi hl hh hsub hfit hFO hq hra hmp hmem hno
  have hAb := allocAb hI hA hph habk hR hal hlo hhi hq hra hraAb hmem
  have hAr := allocArena (lbl := lbl) (p := p) hI hA hR hal hlo hhi hq hmem hctr hheap hoff
  have hCt := allocCtr (Ctx := fun s c => TP tp s → CtrRow (msOfA Λ μ rd G (fun s _ => own s) ar Jv lbl lsize fs)
      (fun s' c'' => PendA p Jv lbl lsize s' c'' fs) s c) hI hA hR hal hlo hhi hq
    (fun a h m hm => hmem a (.inr h) m hm) hheap hlt h64 hctx
  have hPl := Spike.Lib.A64SetupPlaced.allocPlacedS (exe := exe) (endPc := endPc) (fs := fs) hP
  have hPc := allocPc (ms := ms) (q := q) (R := R) (F := F) hI hph
  have hNs := allocNoSys (ms := ms) (q := q) (R := R) (F := F) hI hA
  have hCl := allocCtl (exe := exe) (endPc := endPc) (R := R) (p := p) (fun m h => by rw [hI.labOk]; exact hq m h) hG0F
  refine Spike.Lib.A64.AllocG.AllocW.imp (Spike.Lib.A64.AllocG.AllocW.imp (Spike.Lib.A64.AllocG.AllocW.imp
    (Spike.Lib.A64.AllocG.AllocW.imp (Spike.Lib.A64.AllocG.AllocW.imp (Spike.Lib.A64.AllocG.AllocW.imp
    (Spike.Lib.A64.AllocG.AllocW.imp hSt hAb fun _ _ => And.intro) hAr fun _ _ => And.intro) hCt
    fun _ _ => And.intro) hPl fun _ _ => And.intro) hPc fun _ _ => And.intro) hNs fun _ _ => And.intro) hCl ?_
  rintro s c ⟨⟨⟨⟨⟨⟨hst, hab⟩, har⟩, hct⟩, hpl⟩, hpc⟩, hns⟩ ⟨hnr, hf, hrun⟩ htp
  refine w2_of hp hf (hst.dt_mono fun _ h => h.elim) hab hnr (.of_placedS hpl) (fun c' fs' hr _ => ?_)
    (abortOkA_of_ne (hI.off s hpc).1.noAbort) (fun h => absurd h (by rw [hns]; decide))
  obtain ⟨rfl, rfl⟩ := hrun c' fs' hr
  exact ⟨fun L hL => (Classical.em (L = ar.ctrLoc)).elim .inl fun hne => har _ _ _ hr L hL hne lsize,
    fun hW => hct hW htp⟩

end Alloc

/-! ## The placement in the call's context -/

section Place

open Spike.Lib.A64.Flow (FStable CKept)
open Spike.Lib.A64.Flow.NewBuf (AllocCtx nbJc)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.LowerNode (SlotRepAt)
open Scc.Emit.A64 (FnCtx)
open Scc.Lower.InvA64 (FrameOk)

open Spike.Lib.A64.Flow (blD_run) in
/-- **The call's controls and the frames placed in the call's context**
(`allocW2`'s `hP`) at the allocator's region `R.callee (-frame) (-160) 0`
under `AllocW2`'s frame condition: the call's control the caller's at the
`bl` (`AllocCtx`, `nbJc` past `J1`), placed in the caller's slot file
(`hJ1`), each slot a caller cell outside the allocator's region
(`rsOf_cell`, `frame_outA`) kept by the call (`CKept`) and by the
allocator's frame (`Region.callee_sep`); the hold keeps the term and the
environment; the frames placed under the caller's frame condition (`hfp`),
stable under the allocator's writes (`FStable.callee`). -/
theorem allocHP {Λ : Scc.Sem.Layout} {lbl : Lbl} {fs : List TermRun.Frame} {R : Region}
    {F : MachineData → Prop} {cx : FnCtx} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0) (hR : R.OK)
    (hlo : R.lo ≤ -(cx.frame : Int) - 160) (hhi : 0 ≤ R.hi) (hFS : FStable R F)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {ms : MemSide isaLSE2} {L : Label → Int64} {pcB : Int64} {J1 : Spike.Lib.A64.Flow.AS → Ctl → Prop}
    {q : Call} (hJ1 : ∀ σ c, J1 σ c → SlotRepAt Λ.imms lbl (rsOf cx) σ.slot c) :
    ∀ m0, (F m0 ∧ CallerCells R (-(cx.frame : Int)) (-160) 0 m0 ∧
        AllocCtx ms L R cx.frame (nbJc L [blD Scc.Lower.Names.alloc] pcB (oF cx) J1) q m0) →
      ∀ (s : State) c, DFrame (R.callee (-(cx.frame : Int)) (-160) 0) m0 s.st.1 →
        (c = q.c0 ∨ ∃ o, c = holdCtr ms q.c0 o) → Placed Λ lbl s c ∧ FramesPlaced Λ lbl s fs := by
  rintro m0 ⟨hF0, -, mC, σC, c1, hA, ⟨σ0, hJ, hσC⟩, hN, hk⟩ s c hD hc
  have hc1 : c1 = q.c0 := hN.1
  have h8 : (cx.frame : Int) % 8 = 0 := by omega
  have hge := frame_ge16 hf
  have hout : ∀ r k, rsOf cx r = some k →
      R.Off k ∧ ¬ (R.callee (-(cx.frame : Int)) (-160) 0).Off (k - (-(cx.frame : Int))) := by
    intro r k hk'
    obtain ⟨hk1, hk2, hk3, -⟩ := rsOf_cell hf hk'
    exact frame_outC (by decide) hlo hhi hk1 hk2 (by omega)
  have hσs : σC.slot = σ0.slot := by rw [hσC]; erw [blD_run]
  have hP : Placed Λ lbl s q.c0 := by
    refine placed_of_slotRep (pf := fun k => .slot (R.addr k).toNat) (hc1 ▸ hJ1 σ0 c1 hJ) fun r k hk' => ?_
    obtain ⟨ho1, ho2⟩ := hout r k hk'
    obtain ⟨j, hj, he⟩ := hA.slot k ho1
    have hsep := Region.callee_sep (hR := hR) (by omega) (by decide) (by omega) (by omega) (by decide)
      (by decide) ho1 ho2
    have hl : Mem.loadInt s.st.1.dmem (R.addr k) 8 = some j :=
      (hD _ (R.addr_fit hR ho1) hsep).trans ((hk k ho1 ho2).trans hj)
    show (Scc.Sem.A64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, ← hσs]
    simp only [Scc.Sem.A64.privLoad, hl, Option.map_some, he]
  refine ⟨?_, ?_⟩
  · rcases hc with rfl | ⟨o, rfl⟩
    · exact hP
    · exact hP
  · have hFs : F s.st.1 := Spike.Lib.A64.Flow.FStable.callee hR (by omega) (by decide) (by omega) (by omega)
      hFS m0 s.st.1 hF0 hD
    exact (hfp s hFs).choose_spec.toFramesPlaced

open Spike.Lib.LowerNode (LocBaseRegAt ImmIn ofEnv2) in
open Spike.Lib.Form (lookupS) in
/-- **The call's source relation placed in the slot file** (`allocHP`'s
`hJ1` at `nbJ1`) from the walk's facts at the allocation's `let` `t`
(`SlotRepAt.of_nodeJE`, as `allocBl_w2`). -/
theorem slotRep_nbJ1 {Λ : Scc.Sem.Layout} {p : Prog} {lbl : Lbl} {lsize : Lsize} {cx : FnCtx}
    {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {t : Expr} {env : Scc.Lower.Env}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {a0 a1 a2 : Scc.IR.Operand}
    (htot : ∀ y ∈ Scc.Sem.exprFv t, (lookupS (ofEnv2 env) y).isSome) (hlb : LocBaseRegAt (ofEnv2 env) t)
    (himm : ImmIn Λ.imms (ofEnv2 env) t) :
    ∀ σ c, nbJ1 p lbl lsize cx fp ra tp c0 t env lits cs bufs a0 a1 a2 σ c →
      SlotRepAt Λ.imms lbl (rsOf cx) σ.slot c := by
  rintro σ c ⟨-, -, -, -, -, -, L', sm, B, hj, -⟩
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
theorem ctrRow_msOfAX {ab : Option (State → Prop)} {X : Spike.Lib.Frag isaLSE2} {s : State} {c : Ctl}
    (h : CtrRow (msOfAX Λ μ p rd G own ar I ab lbl lsize fs) X s c) :
    CtrRow (msOfA Λ μ rd G own ar I lbl lsize fs) X s c := by
  cases ab <;> exact h

end Bridge

section AllocX

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region}
  {F : MachineData → Prop} {q : Call}

/-- **`allocW2` at the rows' memory side** `msOfAX … ab` (`AllocW2`'s `ms`
at `landStk_hxa`'s instance): the arena's fields and the mapped words by
`msOfAX_fields`, `msOfAX_mp`; the counter add's row from the allocator's
node `n4` in `PendA` (`hX`, `allocCtx_n4`, `ctrRow_msOfAX`), the counter
unmapped under the stable frame condition (`hFS`, `hmem`). -/
theorem allocW2X (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true) (hph : allocPhOk okPc ph lab = true)
    (habk : allocAbOk lab = true) {Λ : Scc.Sem.Layout} {rS : Range} {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : Spike.Lib.A64.Flow.FStable R F)
    {p : Prog} (hp : ProgNoS ZBad p) {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena}
    {Jv : InvS} {ab : Option (State → Prop)} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}
    {fs : List TermRun.Frame}
    (hq : ∀ m, F m → q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) lab)
    (hra : ph (Int64.ofBitVec q.ra).toBitVec.toNat = ph (lab "scc_rt_alloc").toBitVec.toNat)
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
    (hX : ∀ s c, At exe endPc R F (N lab (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) q .n4) s c →
      TP tp s → PendA p Jv lbl lsize s c fs) :
    AllocW (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) q
      (fun s c => TP tp s → W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F := by
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
  exact allocW2 hI hA hph habk hown hR hal hlo hhi hl hh hsub hfit hFO hq hra hraAb (fun L h => msOfAX_mp h)
    hmem' hno' hctr hheap (fun k τ => by rw [hoff]) hlt h64 hp hG0F hP
    (fun s c hAt htp => ctrRow_msOfAX
      (allocCtx_n4 hI hA hFS hq (fun m hm => hmem' _ (.inl rfl) m hm) hX s c hAt htp))

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
(`hR`), every pair of `X` (the allocator's next nodes) is in an entry `Q`
(`hq`) from which, at every family containing the starts, the levels'
segment inside `W2` holds (`hQ`, the start's tail), so it carries its own
segment (`selfN_of`) and is in `J` (`selfN_mem`); `main`'s `ret` excluded at
no frame (`hnr`). -/
theorem pendA_of_selfN {S0 : FragS isaLSE2} {E : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {J : InvS}
    (hJ : ∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs,
      StartsS ar L0 ls0 (Sg2 Λ μ p rd G own rS Tk ar L0 ls0 Dt Ab a ab) S0 E L ls s c fs → J L ls s c fs)
    {lbl : Lbl} {lsize : Lsize} (hR : Reach ar L0 ls0 lbl lsize) {Q : FragS isaLSE2}
    (hQ : ∀ J' : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 E L ls s c fs →
        J' L ls s c fs) → Sg2 Λ μ p rd G own rS Tk ar L0 ls0 Dt Ab a ab J' lbl lsize Q)
    {X : Spike.Lib.Frag isaLSE2} {fs : List TermRun.Frame} (hq : ∀ s c, X s c → Q s c fs)
    (hnr : ∀ s c, X s c → fs = [] → ∀ a, c.term ≠ .ret a) :
    ∀ s c, X s c → PendA p (IN ar L0 ls0 J) lbl lsize s c fs := fun s c hx =>
  ⟨hnr s c hx, Spike.Lib.Pend.of ⟨hR, selfN_mem hJ
    (selfN_of (fun _ _ _ _ _ h sg => sg.mono_pre h) hR hQ (hq s c hx))⟩⟩

end Self

/-- info: 'Spike.Lib.LowerA64.nodeW_noSys1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_noSys1

/-- info: 'Spike.Lib.LowerA64.allocNoSys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocNoSys

/-- info: 'Spike.Lib.LowerA64.allocCtl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocCtl

/-- info: 'Spike.Lib.LowerA64.allocCtx_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocCtx_of

/-- info: 'Spike.Lib.LowerA64.ctrRow_alloc_n4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ctrRow_alloc_n4

/-- info: 'Spike.Lib.LowerA64.allocCtx_n4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocCtx_n4

/-- info: 'Spike.Lib.LowerA64.allocW2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocW2

/-- info: 'Spike.Lib.LowerA64.allocHP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocHP

/-- info: 'Spike.Lib.LowerA64.slotRep_nbJ1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms slotRep_nbJ1

/-- info: 'Spike.Lib.LowerA64.msOfAX_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms msOfAX_fields

/-- info: 'Spike.Lib.LowerA64.msOfAX_mp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms msOfAX_mp

/-- info: 'Spike.Lib.LowerA64.ctrRow_msOfAX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ctrRow_msOfAX

/-- info: 'Spike.Lib.LowerA64.allocW2X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocW2X

/-- info: 'Spike.Lib.LowerA64.pendA_of_selfN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pendA_of_selfN

end Spike.Lib.LowerA64
