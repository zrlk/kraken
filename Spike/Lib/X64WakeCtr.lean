/-
**The counter row and the box store of wake's start segment** (x86-64;
`OpenW.hctr0`, `OpenW.hnew0`): the context `Ctx` of `W0W` is the box's two
arena writes, `scc_rt_alloc`'s counter add `lock xaddq` for a box call the
start makes (`CtrAt`, the calls `Gc`) or the box's initialising store
(`StAt`, writing no counter word). At the counter add the consumer's
`CtrRow` holds at the start's memory side, landing in `I2`'s `inv0`
disjunct, given that the allocator's next node `c2` (the old count held) is
in `inv0` (`hland`, from the start segment's tail); at the store its
`NewStM` moves to `h0`'s memory side, its landings in `I2`'s `inv1`
disjunct (`hland1`).

- `Flow.ctrRow_ndS`: `ctrRow_nd` at any allocation site (`AllocSite`, as
  `ctr_ndWS`).
- `ctrRow_allocS_c2`: at `scc_rt_alloc`'s counter add for a call at its
  site premises (`Call.OKS`), landing exactly at `c2`.
- `CtrOk`, `CtrAt`, `CtxW`, `ctrRow_xa`, `hctr0_of`: the counter add's
  call facts, the context, `CtrRow` reading no `xa`, `OpenW.hctr0`'s shape.
- `StAt`, `stAt_noWr`, `ctrAt_wr`, `hnew0_of`: the store's states, the
  store writing no counter, the add writing it, `OpenW.hnew0`'s shape.
- `CtxT`, `CtxT.ctxW`, `hctr0_ofT`: the context with the thread pointer on
  the counter add, and `hctr0_of` there.

x86-64 twin of `Spike/Lib/A64WakeCtr.lean`, `Spike/Lib/A64WakeNew.lean` and
`Spike/Lib/A64WakeCtrTp.lean` (same names, namespace
`Spike.Lib.X64.WakeCtr`).

**Unlike AArch64**:
- there is no `Alloc.Code` structure: `scc_rt_alloc`'s code is from the
  layout (`hp : Lays exe cells kp`, `hend`, `hin : allocIn cells`, under
  `Executable.ValidLayout exe`), as `X64.Alloc.ctrRow_alloc`;
- the add is `lock xaddq %rax, (%rcx)` (A64: `ldadd`), its successor node
  `c2` (A64: `n4`), so `ctrRow_allocS_n4` is `ctrRow_allocS_c2` and
  `hland` is at `N … .c2`;
- `hctr0_ofT` needs no "no `MSR`" fact: no x86-64 instruction writes the
  `%fs` base (`KeepTP.exec_tp` is unconditional).
-/
import Spike.Lib.X64CtrRow
import Spike.Lib.X64AllocBox
import Spike.Lib.X64SegInstA
import Spike.Lib.X64KeepTP
import Spike.Lib.FrameNew
import Spike.Lib.OutNew

namespace Spike.Lib.X64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib.X64ConsumerA (CtrRow)

variable {ms : MemSide isa} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND} {E : κ → ND}

/-- **`CtrRow` at a state of the counter's add node** `lock xaddq %r,
k(%b)` at any allocation site (`ctrRow_nd` with the site `AllocSite
ms.newOk`, as `ctr_ndWS`). -/
theorem ctrRow_ndS {n : ND} {b r : Reg64} {k : Int64} {z : Nat} (hr : r ≠ .rsp) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(xaddDir b k r, z)])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      bAddr σ.regs b k = BitVec.ofNat 64 ms.ctr ∧ ms.rt (BitVec.ofNat 64 ms.ctr).toNat ∧
      ms.mp (ctrLoc ms) true ∧ Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none ∧
      ∃ (x : String) (τ : Ty) (e : Expr) (nn : Nat), AllocSite ms.newOk c x nn τ e ∧ c.hold = none ∧
        σ.regs.get64 r = BitVec.ofNat 64 (ms.units nn τ) ∧
        ∀ old : Val, ms.G (ctrLoc ms) old → (old.setWidth 64).toNat ≤ ms.cells → ms.lo (old.setWidth 64).toNat →
          ms.G (ctrLoc ms) ((old.setWidth 64 + BitVec.ofNat 64 (ms.units nn τ)).setWidth 128) ∧
          ∀ fl, Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill r, { ownStep r (old.setWidth 64) σ with status := fl }⟩
            (holdCtr ms c (old.setWidth 64)))
    {s : State} {c : Ctl} (hAt : At exe endPc R F n s c) :
    CtrRow ms (Next exe endPc R F N E) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := hAt
  have hc : CellAt s (xaddDir b k r) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨ha, hrt, hmp, hdm, x, τ, e, nn, hs, hh, hru, hX⟩ := hedge _ σ c hA hD hJ
  have ha' : eaddr s z (mB b k) = BitVec.ofNat 64 ms.ctr :=
    (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha)
  have hex := exec_xaddG_agrees (w := .W64) hc ha' hdm (agrees_of_decls hdc _ _)
  rw [Reg64s.get_low64] at hex
  refine ⟨.acqRel, _, _, x, τ, e, nn, hex, hrt, hmp, hs, hh, fun old => ?_, fun old hG _ hle hlo => ?_⟩
  · simp only [hA.regs, hru]
  obtain ⟨hG', hL⟩ := hX old hG hle hlo
  exact ⟨hG', land_own rfl hr hF he hn hdc hpc hA hD (hL _)⟩

end Spike.Lib.X64.Flow

namespace Spike.Lib.X64.WakeCtr

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem (Marks)
open Scc.Sem.X64 (abi)
open Scc.Cert.Rt.X64 (Lays endOf code_field)
open Spike.Lib (Region FrameRun MemSide Arena FragS Frag)
open Spike.Lib.X64ConsumerA (CtrRow PendA WrAt msOfA I2 ArenaW)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64 (At Next FStable)
open Spike.Lib.X64.Flow (ofNat_add')
open Spike.Lib.X64.Alloc
open Spike.Lib.X64.KeepTP (TP)

variable {ms : MemSide isa} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {q : Call} {cells : List (Directive × Nat)} {kp : Nat}

/-- **`CtrRow` at `scc_rt_alloc`'s counter add landing at `c2`** for a call
at its site premises (`hq`: a buffer or a box), the code from the layout
(`hp`, `hend`, `hin`), the counter unmapped under the stable frame
condition (`hF`, `hmem`). -/
theorem ctrRow_allocS_c2 [Executable.ValidLayout exe] (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : allocIn cells = true)
    (hF : FStable R F) (hq : q.OKS ms (_root_.Executable.labels exe).label)
    (hmem : ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none)
    {s : State} {c : Ctl} (hAt : At exe endPc R F (N (_root_.Executable.labels exe).label ms q .rmw) s c) :
    CtrRow ms (Next exe endPc R F (fun _ : Unit => N (_root_.Executable.labels exe).label ms q .c2)
      (fun x : Empty => x.elim)) s c := by
  have hin' := hin
  simp only [allocIn, fiAt, iCtr, iHeap, iRmw, iHdr, iRet, Bool.and_eq_true] at hin'
  refine Spike.Lib.X64.Flow.ctrRow_ndS (b := .rcx) (k := 0) (r := .rax) (z := 5) (by decide) hF
    (code_field hp hend (by simp only [hin']) (l := cntL) (off := 19) rfl) (fun m σ c _ hD hJ => ?_) hAt
  obtain ⟨⟨rfl, hFr, hn28⟩, hcx, hax⟩ := hJ
  have hb : bAddr σ.regs .rcx 0 = BitVec.ofNat 64 ms.ctr := by
    rw [← hq.ctr, ← hcx]; simp [bAddr, Reg64s.get64]
  rw [hb]
  refine ⟨rfl, hq.rt, hq.mp, hmem _ hD, q.x, q.τ, q.e, q.n, hq.site, hq.hold, by exact hax,
    fun old hG hle hlo => ⟨hq.grow old hG hle, fun fl =>
      .inl ⟨(), ofNat_add' _ 19 5, rfl, _, rfl, hle, hFr, hn28, ?_, hlo⟩⟩⟩
  simp [ownStep, Reg64s.set64]

/-- **The counter add's call facts**: a box call (`Call.OKB`), the frame
condition stable in the allocator's region with the counter unmapped. -/
structure CtrOk (ms : MemSide isa) (lab : Label → Int64) (R : Region) (F : MachineData → Prop) (q : Call) :
    Prop where
  okb : q.OKB ms lab
  fst : FStable R F
  mem : ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none

/-- **The counter add's states** of the start (no frames): `scc_rt_alloc`'s
`rmw` node for a call `Gc` admits (the start's own calls) with `CtrOk`, at a
memory side `ms0` that is `ref` but for `xa`. -/
def CtrAt (ref : MemSide isa) (exe : _root_.Executable) (endPc : Int64)
    (Gc : MemSide isa → Region → (MachineData → Prop) → Call → Prop) : FragS isa := fun s c fs =>
  fs = [] ∧ ∃ (ms0 : MemSide isa) (R : Region) (F : MachineData → Prop) (q : Call),
    ms0 = { ref with xa := ms0.xa } ∧ Gc ms0 R F q ∧ CtrOk ms0 (_root_.Executable.labels exe).label R F q ∧
    At exe endPc R F (N (_root_.Executable.labels exe).label ms0 q .rmw) s c

/-- **`W0W`'s context**: the counter add (`CtrAt`) or the box's store `St`. -/
def CtxW (ref : MemSide isa) (exe : _root_.Executable) (endPc : Int64)
    (Gc : MemSide isa → Region → (MachineData → Prop) → Call → Prop) (St : FragS isa) : FragS isa :=
  fun s c fs => CtrAt ref exe endPc Gc s c fs ∨ St s c fs

/-- **`CtrRow` reads no `xa`.** -/
theorem ctrRow_xa {ms ms' : MemSide isa} {X : Frag isa} {s : State} {c : Ctl}
    (h : CtrRow ms X s c) (he : ms' = { ms with xa := ms'.xa }) : CtrRow ms' X s c := by
  have h' : CtrRow { ms with xa := ms'.xa } X s c := h
  rw [← he] at h'
  exact h'

/-- **The counter add at a `CtrAt` state is at the call's source pair.** -/
theorem ctrAt_c0 {ms0 : MemSide isa} {s : State} {c : Ctl}
    (hAt : At exe endPc R F (N (_root_.Executable.labels exe).label ms0 q .rmw) s c) : c = q.c0 := by
  obtain ⟨-, -, -, -, σ, -, -, ⟨⟨h, -, -⟩, -, -⟩⟩ := hAt
  exact h

variable {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Spike.Lib.X64ConsumerS.OwnS} {ar : Arena} {L0 : Lbl} {ls0 : Lsize} {inv0 : FragS isa}
  {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {p : Prog} {St : FragS isa}
  {Gc : MemSide isa → Region → (MachineData → Prop) → Call → Prop}

/-- **`OpenW.hctr0` at `Ctx := CtxW`** (the reference side `msOfA` at no
fragment, at `L0`, `ls0`): the store `St` writes no counter (`hSt`); at the
counter add the frame run stays put (a box `new`) and `ctrRow_allocS_c2`
gives the row, its landing at `c2` in `inv0` (`hland`, for the calls `Gc`
admits), so in `I2`'s first disjunct. `inv0` itself is not used. -/
theorem hctr0_of [Executable.ValidLayout exe] (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : allocIn cells = true)
    (hSt : ∀ s c fs, St s c fs → ¬ WrAt s ar.ctrLoc)
    (hland : ∀ (ms0 : MemSide isa) R F q,
      ms0 = { msOfA Λ μ rd G own ar (fun _ _ _ _ _ => False) L0 ls0 [] with xa := ms0.xa } → Gc ms0 R F q →
      CtrOk ms0 (_root_.Executable.labels exe).label R F q →
      ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label ms0 q .c2) s c → inv0 s c []) :
    ∀ s c fs, inv0 s c fs →
      CtxW (msOfA Λ μ rd G own ar (fun _ _ _ _ _ => False) L0 ls0 []) exe endPc Gc St s c fs →
      WrAt s ar.ctrLoc → ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false →
      CtrRow (msOfA Λ μ rd G own ar (I2 ar L0 ls0 inv0 inv1) L0 ls0 fs')
        (fun s' c'' => PendA p (I2 ar L0 ls0 inv0 inv1) L0 ls0 s' c'' fs') s c' := by
  intro s c fs _ hC hW c' fs' hr _
  obtain ⟨rfl, ms0, R, F, q, hms, hGc, hok, hAt⟩ := hC.resolve_right fun hS => hSt s c fs hS hW
  have hc : c = q.c0 := ctrAt_c0 hAt
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Spike.Lib.FrameNew.FrameRun.eq_of_new hr (by rw [hc]; exact hok.okb.term.choose_spec))
  have hrow := ctrRow_allocS_c2 hp hend hin hok.fst hok.okb.toS hok.mem hAt
  refine ctrRow_xa ?_ (show _ = { ms0 with xa := _ } by rw [hms]; rfl)
  obtain ⟨k, op, g, x, τ, e, n, h1, h2, h3, h4, h5, h6, h7⟩ := hrow
  refine ⟨k, op, g, x, τ, e, n, h1, h2, h3, h4, h5, h6, fun old hG hown hle hlo => ?_⟩
  obtain ⟨hG', hL⟩ := h7 old hG hown hle hlo
  refine ⟨hG', fun _ a h => ?_, _, _, .refl _, .inl ⟨rfl, rfl, ?_⟩⟩
  · revert h; rw [hc]; intro h
    have h2 : q.c0.term = .ret a := h
    rw [hok.okb.term.choose_spec] at h2
    cases h2
  · rcases hL with ⟨_, hj⟩ | ⟨y, _⟩
    · exact hland ms0 R F q hms hGc hok _ _ hj
    · exact y.elim

/-! ## The box's initialising store -/

/-- **The box store's states** of the start (no frames): the store's
premises at `ref` with the allocation fragment a landing `Lnd` that `Gs`
admits. -/
def StAt (ref : MemSide isa) (p : Prog) (lbl : Lbl)
    (Gs : (WeakMem.AllocLabel → Nat → Nat → Frag isa) → Prop) : FragS isa := fun s c fs =>
  fs = [] ∧ ∃ Lnd, Gs Lnd ∧ NewStM p lbl { ref with xa := Lnd } s c

/-- **The box's store writes no counter**: it writes a cell at or above the
arena's base (`ref.heap`), the counter word below it (`hlt`). -/
theorem stAt_noWr {ref : MemSide isa} {Gs : (WeakMem.AllocLabel → Nat → Nat → Frag isa) → Prop}
    (hlt : ar.ctr + 8 ≤ ref.heap) (h64 : ar.ctr < 2 ^ 64) :
    ∀ s c fs, StAt ref p L0 Gs s c fs → ¬ WrAt s ar.ctrLoc := by
  rintro s c fs ⟨-, Lnd, -, kr, A, V, s', x, a, ty, e, w, wold, old, -, hex, -, -, -, -, -, -, -, hA, -, -⟩ hW
  rcases hW with ⟨kr', V', s'', he⟩ | ⟨k, op, g, he⟩
  · rw [hex] at he
    simp only [Option.some.injEq, EvTree.store.injEq] at he
    have hL := congrArg Loc.addr he.2.2.1
    simp only [Arena.ctrLoc] at hL
    have : A.toNat = ar.ctr := by rw [hL, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h64
    simp only at hA
    omega
  · rw [hex] at he
    simp at he

/-- **The counter add writes the counter** (`ctrRow_allocS_c2`'s step), at
a memory side `ref` but for `xa` whose counter is the arena's (`hc`). -/
theorem ctrAt_wr [Executable.ValidLayout exe] {ref : MemSide isa} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hin : allocIn cells = true) (hc : ref.ctr = ar.ctr) :
    ∀ s c fs, CtrAt ref exe endPc Gc s c fs → WrAt s ar.ctrLoc := by
  rintro s c fs ⟨-, ms0, R, F, q, hms, -, hok, hAt⟩
  obtain ⟨k, op, g, -, -, -, -, h1, -⟩ := ctrRow_allocS_c2 hp hend hin hok.fst hok.okb.toS hok.mem hAt
  have e : ms0.ctr = ar.ctr := (congrArg MemSide.ctr hms).trans hc
  refine .inr ⟨k, op, g, ?_⟩
  rw [h1, e]; rfl

/-- **`OpenW.hnew0` at `Ctx := CtxW ref … (StAt ref …)`** (`ref` the
reference side `msOfA` at no fragment, at `L0`, `ls0`): the counter add
writes the counter (`ctrAt_wr`); at the store the frame run stays put (a
box `new`) and the store's `NewStM` holds at `h0`'s side but for `xa`, its
landings `Lnd` in `h0`'s fragment (`hland1`: in `I2`'s `inv1` disjunct, for
the landings `Gs` admits). `inv0` itself is not used. -/
theorem hnew0_of [Executable.ValidLayout exe] {Gs : (WeakMem.AllocLabel → Nat → Nat → Frag isa) → Prop}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : allocIn cells = true)
    (hland1 : ∀ Lnd, Gs Lnd → ∀ l A s' c', L0 l = none → Lnd l A 1 s' c' →
      (msOfA Λ μ rd G own ar (I2 ar L0 ls0 inv0 inv1) L0 ls0 []).xa l A 1 s' c') :
    ∀ s c fs, inv0 s c fs →
      CtxW (msOfA Λ μ rd G own ar (fun _ _ _ _ _ => False) L0 ls0 []) exe endPc Gc
        (StAt (msOfA Λ μ rd G own ar (fun _ _ _ _ _ => False) L0 ls0 []) p L0 Gs) s c fs →
      ¬ WrAt s ar.ctrLoc → ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false →
      ∀ L, WrAt s L → ¬ ArenaW ar L0 ls0 c' L →
        NewStM p L0 (msOfA Λ μ rd G own ar (I2 ar L0 ls0 inv0 inv1) L0 ls0 fs') s c' := by
  intro s c fs _ hC hW c' fs' hr _ _ _ _
  obtain ⟨rfl, Lnd, hG, kr, A, V, s', x, a, ty, e, w, wold, old, hN, hex, hmp, ht, hev, hacc, hv, hh, hold, hA, hcl,
    hX⟩ := hC.resolve_left fun h => hW (ctrAt_wr hp hend hin rfl s c fs h)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Spike.Lib.FrameNew.FrameRun.eq_of_new hr ht.choose_spec)
  exact ⟨kr, A, V, s', x, a, ty, e, w, wold, old, hN, hex, hmp, ht, hev, hacc, hv, hh, hold, hA, hcl,
    fun l hl => hland1 Lnd hG l _ _ _ hl (hX l hl)⟩

/-! ## The context with the thread pointer -/

/-- **The context with the thread pointer at the counter add**: the
counter add (`CtrAt`) under `TP t`, or the box's store `St`. -/
def CtxT (ref : MemSide isa) (exe : _root_.Executable) (endPc : Int64)
    (Gc : MemSide isa → Region → (MachineData → Prop) → Call → Prop) (t : UInt64) (St : FragS isa) :
    FragS isa :=
  fun s c fs => (CtrAt ref exe endPc Gc s c fs ∧ TP t s) ∨ St s c fs

/-- `CtxT` is in `CtxW`. -/
theorem CtxT.ctxW {ref : MemSide isa} {t : UInt64} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (h : CtxT ref exe endPc Gc t St s c fs) : CtxW ref exe endPc Gc St s c fs :=
  h.imp_left And.left

/-- **`OpenW.hctr0` at `Ctx := CtxT`**: as `hctr0_of`, the tail's landing at
`c2` (`hland`) under the thread pointer `t`, kept by the add (every x86-64
instruction keeps the `%fs` base, `KeepTP.exec_tp`). -/
theorem hctr0_ofT [Executable.ValidLayout exe] {t : UInt64} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hin : allocIn cells = true)
    (hSt : ∀ s c fs, St s c fs → ¬ WrAt s ar.ctrLoc)
    (hland : ∀ (ms0 : MemSide isa) R F q,
      ms0 = { msOfA Λ μ rd G own ar (fun _ _ _ _ _ => False) L0 ls0 [] with xa := ms0.xa } → Gc ms0 R F q →
      CtrOk ms0 (_root_.Executable.labels exe).label R F q →
      ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label ms0 q .c2) s c → TP t s → inv0 s c []) :
    ∀ s c fs, inv0 s c fs →
      CtxT (msOfA Λ μ rd G own ar (fun _ _ _ _ _ => False) L0 ls0 []) exe endPc Gc t St s c fs →
      WrAt s ar.ctrLoc → ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false →
      CtrRow (msOfA Λ μ rd G own ar (I2 ar L0 ls0 inv0 inv1) L0 ls0 fs')
        (fun s' c'' => PendA p (I2 ar L0 ls0 inv0 inv1) L0 ls0 s' c'' fs') s c' := by
  intro s c fs _ hC hW c' fs' hr _
  obtain ⟨⟨rfl, ms0, R, F, q, hms, hGc, hok, hAt⟩, htp⟩ := hC.resolve_right fun hS => hSt s c fs hS hW
  have hc : c = q.c0 := ctrAt_c0 hAt
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Spike.Lib.FrameNew.FrameRun.eq_of_new hr (by rw [hc]; exact hok.okb.term.choose_spec))
  have hrow := ctrRow_allocS_c2 hp hend hin hok.fst hok.okb.toS hok.mem hAt
  refine ctrRow_xa ?_ (show _ = { ms0 with xa := _ } by rw [hms]; rfl)
  obtain ⟨k, op, g, x, τ, e, n, h1, h2, h3, h4, h5, h6, h7⟩ := hrow
  have hT := Spike.Lib.X64.KeepTP.exec_tp htp h1
  refine ⟨k, op, g, x, τ, e, n, h1, h2, h3, h4, h5, h6, fun old hG hown hle hlo => ?_⟩
  obtain ⟨hG', hL⟩ := h7 old hG hown hle hlo
  refine ⟨hG', fun _ a h => ?_, _, _, .refl _, .inl ⟨rfl, rfl, ?_⟩⟩
  · revert h; rw [hc]; intro h
    have h2 : q.c0.term = .ret a := h
    rw [hok.okb.term.choose_spec] at h2
    cases h2
  · rcases hL with ⟨_, hj⟩ | ⟨y, _⟩
    · exact hland ms0 R F q hms hGc hok _ _ hj (hT old)
    · exact y.elim

end Spike.Lib.X64.WakeCtr

/-- info: 'Spike.Lib.X64.Flow.ctrRow_ndS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.ctrRow_ndS

/-- info: 'Spike.Lib.X64.WakeCtr.ctrRow_allocS_c2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeCtr.ctrRow_allocS_c2

/-- info: 'Spike.Lib.X64.WakeCtr.ctrRow_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeCtr.ctrRow_xa

/-- info: 'Spike.Lib.X64.WakeCtr.hctr0_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeCtr.hctr0_of

/-- info: 'Spike.Lib.X64.WakeCtr.stAt_noWr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeCtr.stAt_noWr

/-- info: 'Spike.Lib.X64.WakeCtr.ctrAt_wr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeCtr.ctrAt_wr

/-- info: 'Spike.Lib.X64.WakeCtr.hnew0_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeCtr.hnew0_of

/-- info: 'Spike.Lib.X64.WakeCtr.CtxT.ctxW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeCtr.CtxT.ctxW

/-- info: 'Spike.Lib.X64.WakeCtr.hctr0_ofT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeCtr.hctr0_ofT
