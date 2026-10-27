/-
**`wc_rodata` on x86-64 from its call to its return through the generic
setup composition** (a regression check of `Spike/Lib/X64SetupW.lean`, the
twin of `Spike/Lib/A64Hello1RodataSetupG.lean`): `Setup.setup_callW` at
`hello1.w`'s setup block, the body a `Setup.chainW` walk of the allocation
(`Setup.alloc_stepW`: `rdE` and the call of `scc_rt_alloc`), the two lane
stores (`Setup.lane_stepW`, `.x13`'s blocks around each exchange) and the
epilogue (`Setup.ret_stepW`, `rpB4`), in a region of depth `240` below the
entry `%rsp`: the frame of `32` under the saved `%rbp`, the allocator's
return address and frame of `160`, and the heap abort's dispatcher of `32`
(`allocAbortDepth 40 + 32`).

- `rdQ`, `rdQ_facts`: `rodata`'s allocation as the allocator's call;
- `allocW_tp`: the allocator's obligations at a thread pointer (`tpXa`);
- `sJ0`, `sJE`, `sJ1`, `RdF`, `sJp`, `sJ2`, `sJ4`: the source controls at
  the walk's nodes (the entry, the allocation, `.x13`, between the stores,
  before the epilogue);
- `rdPostS`: the post at the return (the buffer's base at label `l` in
  `%rax`, the offset word `0` in `%rdx`, the length `2` in `%rcx`, the count
  `13` in `%rsi`), and `rdPostS_setupPostS`: it is `SetupPostS` at
  `hello1Pl`;
- `RdGW`, `RdGW.triv`: the walk's states inside `W`;
- `hello1_rodata_setupGW`: from the setup entry `uN0 .. "wc_rodata" 32 g`
  to `uNxS rdPostS g`; `hello1_rodata_setupGW_ret`: to
  `uNxS (SetupPostS lbl rdX64 hello1Pl) g`.

The region's bound `hlo` must come from `stackLimit - Tcb.headroom`, not
the need table: the runtime's frames (the allocator's, the heap abort's)
are not in the need table, which counts `40` for `wc_rodata`.
-/
import Spike.Lib.X64SetupW
import Spike.Lib.X64Hello1Rodata
import Spike.Lib.X64Hello1Segs
import Spike.Lib.Hello1RodataSrc
import Spike.Lib.Rt.X64SetupRet

namespace Spike.Lib.X64.Flow.Hello1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Spike.Lib.X64.Flow.Ret0 (CallerCells LimOk WcG limA)
open Spike.Lib.X64.Alloc (Call AllocW Ea Jfull)
open Spike.Lib.X64.Flow.NewBuf (allocAbortDepth allocAbortDepth_40 nbX nbJc NBX)
open Spike.Lib.X64.Flow.Setup (entJ sEn sRet sAb chainW alloc_stepW lane_stepW ret_stepW setup_callW
  callOK_tp callOK_untp limOk_tp)
open Spike.Lib.X64.Rt (uN0 uNxS rdX64)
open Spike.Lib.SetupRet (SetupPostS hello1Pl)
open Spike.Lib.Hello1RodataSrc (rdC0 rdCN rdCA rdC1 rdC2 rdC3 rdC4 rdRet eW0 eW1 eN τ8 rdK1 rdK2 rdC0_run
  rdCN_newBuf rdC4_run bufElem_b evalAt_b3 rdK1_lt rdK2_lt)

set_option linter.unusedSimpArgs false

/-! ## The allocation -/

/-- **`rodata`'s allocation as the allocator's call**: at `rdCN`, `b` bound
to a buffer of `m = 2` lane words, header `257`. -/
def rdQ : Call :=
  ⟨rdCN, "b", .var "m", τ8, eW0, .intS (.lit 2), [TermRun.cst (.num 2)], 2, 257#64, 0#64, 0#64⟩

/-- **A call at `rdCN` is `rodata`'s allocation**: its binder, element
type, continuation and count. -/
theorem rdQ_facts {ms : MemSide isa} {lab : Label → Int64} {q : Call} (h : q.OK ms lab)
    (hc : q.c0 = rdCN) : q.x = "b" ∧ q.τ = τ8 ∧ q.e = eW0 ∧ q.n = 2 := by
  have ht := h.term
  have hv := h.ev
  have hn := h.num
  rw [hc] at ht hv
  obtain ⟨h1, h2, h3, h4, h5⟩ := rdCN_newBuf
  rw [h1] at ht
  simp only [Expr.let_.injEq, Op.newBuf.injEq] at ht
  obtain ⟨hx, ⟨ha, hτ⟩, he⟩ := ht
  rw [← ha, h2] at hv
  simp only [Option.some.injEq, Prod.mk.injEq] at hv
  rw [← hv.2, h3] at hn
  simp only [Option.some.injEq] at hn
  exact ⟨hx.symm, hτ.symm, he.symm, hn.symm⟩

/-- The allocator's obligations at a thread pointer. -/
theorem allocW_tp {ms : MemSide isa} {t : UInt64} {q : Call} {W : Frag isa} {K : State → State → Prop}
    {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    (h : AllocW ms q W K exe endPc R F) : AllocW (tpXa ms t) q W K exe endPc R F :=
  ⟨h.e, h.entry, h.j1, h.cnt, h.c1, h.rmw, h.c2, h.j2, h.slow, h.j3, h.full, h.ok, h.f1, h.o1, h.f2, h.o2,
    h.s2, h.o3, h.f3, h.o4, h.f4, h.o5, h.f5, h.o6, h.f6, h.o7, h.f7, h.o8, h.hdr, h.o9, h.ret⟩

/-! ## The source controls at the walk's nodes -/

section Inv

variable (lab : Label → Int64) (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide isa)
  (F0 : MachineData → Prop) (g : WcG) (R : Region)

/-- **The entry's invariant**: `scc_rt_main`'s call of the setup block
(`uN0`, a frame of 32 checked). -/
abbrev sJ0 : AS → Ctl → Prop := (uN0 lab ms F0 "wc_rodata" 32 g).J

/-- **The body's entry**: after the prologue, `%rbp` at the saved `%rbp`. -/
def sJE : AS → Ctl → Prop := wJ R (entJ 32 [] (sJ0 lab ms F0 g))

/-- At the allocation: a body entry state, the source at `rdCN`. -/
def sJ1 (J : AS → Ctl → Prop) (σ : AS) (c : Ctl) : Prop := (∃ c0, J σ c0) ∧ c = rdCN

/-- **The buffer's facts** for label `l` with base `b`: placed at `A` in
the arena's cells, the frame record and `%rbp` the caller's. -/
def RdF (b : BitVec 64) (σ : AS) (l : WeakMem.AllocLabel) : Prop :=
  ∃ A old : Nat, lbl l = some A ∧ b.toNat = A ∧ A = ms.heap + 16 * old + ms.off 2 τ8 ∧
    old + ms.units 2 τ8 ≤ ms.cells ∧ σ.slot 0 = g.ra ∧ σ.slot (-8) = g.fp ∧ σ.regs.get64 .rbp = R.addr (-8)

/-- At `.x13`: the base in `%rax`, the source past the allocation. -/
def sJp (σ : AS) (c : Ctl) : Prop := ∃ l ini, RdF lbl ms g R σ.regs.rax.toBitVec σ l ∧ c = rdCA l ini

/-- Between the stores: the base at `-16`, the source past the first. -/
def sJ2 (σ : AS) (c : Ctl) : Prop := ∃ l ini wo0, RdF lbl ms g R (σ.slot (-16)) σ l ∧ c = rdC2 l ini wo0

/-- Before the epilogue: the base at `-16`, the source past the second. -/
def sJ4 (σ : AS) (c : Ctl) : Prop :=
  ∃ l ini wo0 wo1, RdF lbl ms g R (σ.slot (-16)) σ l ∧ c = rdC4 l ini wo0 wo1

/-- **The setup block's post**: the source at `ret sl` for a buffer at
label `l`, base `A` in the arena's cells, in `%rax`; `%rdx`, `%rcx`, `%rsi`
the slice's other words (the offset word `0`, the length `2`, the count
`13`). -/
def rdPostS (c : Ctl) (r : Reg64s) : Prop :=
  ∃ (l : WeakMem.AllocLabel) (ini : Nat) (wo0 wo1 : TermRun.Word) (A old : Nat), c = rdRet l ini wo0 wo1 ∧
    lbl l = some A ∧ r.rax.toNat = A ∧ A = ms.heap + 16 * old + ms.off 2 τ8 ∧ old + ms.units 2 τ8 ≤ ms.cells ∧
    r.rdx.toBitVec = 0#64 ∧ r.rcx.toBitVec = 2#64 ∧ r.rsi.toBitVec = 13#64

end Inv

/-- **`rdPostS` is the named post** `SetupPostS` at `hello1Pl`. -/
theorem rdPostS_setupPostS {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {c : Ctl}
    {r : Reg64s} (h : rdPostS lbl ms c r) : SetupPostS lbl rdX64 hello1Pl c r := by
  obtain ⟨l, ini, wo0, wo1, A, old, rfl, hl, hx0, -, -, hdx, hcx, hsi⟩ := h
  refine ⟨rfl, _, _, _, rfl, rfl, ⟨rfl, ?_, ?_⟩, ⟨by decide, ?_⟩, ⟨by decide, ?_⟩, trivial⟩
  · show lbl l = some r.rax.toNat
    rw [hx0]; exact hl
  · show r.rdx.toBitVec.toNat = 8 * 0
    rw [hdx]; rfl
  · show r.rcx.toBitVec.toNat = 2
    rw [hcx]; rfl
  · show r.rsi.toBitVec.toNat = 13
    rw [hsi]; rfl

/-! ## The walk's states inside `W` -/

/-- **`wc_rodata`'s states inside `W`** along the generic walk, none moved
by `K`: the prologue's, the allocation's block, the allocator's (for every
call returning to `.x13`), each lane store's four nodes, the epilogue's. -/
structure RdGW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isa) (lbl : WeakMem.AllocLabel → Option Nat)
    (F0 : MachineData → Prop) (g : WcG) : Prop where
  pro : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "wc_rodata") 32 8 ".Lwc_rodata.stk"
    5 9 3 2 4 [] (sJ0 (_root_.Executable.labels exe).label ms F0 g)
  e : BlkW W K exe endPc R F
    ⟨(_root_.Executable.labels exe).label ".Lwc_rodata.entry", oR, sJE (_root_.Executable.labels exe).label ms F0 g R⟩
    rdE
  alloc : ∀ q : Call, q.ra = ((_root_.Executable.labels exe).label ".Lwc_rodata.x13").toBitVec →
    AllocW ms q W K exe endPc (R.callee (-48) (-160) 8) (fun m => F m ∧ CallerCells R (-48) (-160) 8 m)
  l1 : BlkW W K exe endPc R F ⟨(_root_.Executable.labels exe).label ".Lwc_rodata.x13", oR, sJp lbl ms g R⟩ rpB0
  l1L : NodeW W K exe endPc R F (LaneStore.lsNL (_root_.Executable.labels exe).label rpB0
    ((_root_.Executable.labels exe).label ".Lwc_rodata.x13")
    ((_root_.Executable.labels exe).label ".Lwc_rodata.x13" + 8)
    oR oR "w0" "o0" "b" false .w8 rdK1 0 eW1 (sJp lbl ms g R))
  l1H : BlkW W K exe endPc R F (LaneStore.lsNH (_root_.Executable.labels exe).label rpB0
    ((_root_.Executable.labels exe).label ".Lwc_rodata.x13")
    ((_root_.Executable.labels exe).label ".Lwc_rodata.x13" + 8)
    3 oR oR .rax .rcx 0 "w0" "o0" "b" false .w8 rdK1 0 eW1 (sJp lbl ms g R)) rpB1
  l1S : NodeW W K exe endPc R F (LaneStore.lsNS (_root_.Executable.labels exe).label rpB0 rpB1
    ((_root_.Executable.labels exe).label ".Lwc_rodata.x13")
    ((_root_.Executable.labels exe).label ".Lwc_rodata.x13" + 8)
    ((_root_.Executable.labels exe).label ".Lwc_rodata.x13" + Int64.ofNat 29) 3 oR oR oR .rax .rcx 0 "w0" "o0" "b"
    false .w8 rdK1 0 eW1 (sJp lbl ms g R))
  l2 : BlkW W K exe endPc R F
    ⟨(_root_.Executable.labels exe).label ".Lwc_rodata.x13" + Int64.ofNat 29 + Int64.ofNat 3, oR, sJ2 lbl ms g R⟩ rpB2
  l2L : NodeW W K exe endPc R F (LaneStore.lsNL (_root_.Executable.labels exe).label rpB2
    ((_root_.Executable.labels exe).label ".Lwc_rodata.x13" + Int64.ofNat 29 + Int64.ofNat 3)
    ((_root_.Executable.labels exe).label ".Lwc_rodata.x13" + Int64.ofNat 36)
    oR oR "w1" "o1" "b" false .w8 rdK2 1 eN (sJ2 lbl ms g R))
  l2H : BlkW W K exe endPc R F (LaneStore.lsNH (_root_.Executable.labels exe).label rpB2
    ((_root_.Executable.labels exe).label ".Lwc_rodata.x13" + Int64.ofNat 29 + Int64.ofNat 3)
    ((_root_.Executable.labels exe).label ".Lwc_rodata.x13" + Int64.ofNat 36)
    4 oR oR .rax .rcx 8 "w1" "o1" "b" false .w8 rdK2 1 eN (sJ2 lbl ms g R)) rpB3
  l2S : NodeW W K exe endPc R F (LaneStore.lsNS (_root_.Executable.labels exe).label rpB2 rpB3
    ((_root_.Executable.labels exe).label ".Lwc_rodata.x13" + Int64.ofNat 29 + Int64.ofNat 3)
    ((_root_.Executable.labels exe).label ".Lwc_rodata.x13" + Int64.ofNat 36)
    ((_root_.Executable.labels exe).label ".Lwc_rodata.x13" + Int64.ofNat 58) 4 oR oR oR .rax .rcx 8 "w1" "o1" "b"
    false .w8 rdK2 1 eN (sJ2 lbl ms g R))
  ret : BlkW W K exe endPc R F
    ⟨(_root_.Executable.labels exe).label ".Lwc_rodata.x13" + Int64.ofNat 58 + Int64.ofNat 4, oR, sJ4 lbl ms g R⟩ rpB4

/-- The walk's states are inside the trivial predicate, with no outside
moves. -/
theorem RdGW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {lbl : WeakMem.AllocLabel → Option Nat} {F0 : MachineData → Prop} {g : WcG} :
    RdGW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms lbl F0 g :=
  ⟨XProW.triv, BlkW.triv, fun q _ => Alloc.AllocW.triv ms q, BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv,
    BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv⟩

/-! ## The walk -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **The buffer's words** `b + i` for `i ∈ {0, 8}`: at `A + i` in the
arena's cells, without wrapping. -/
theorem rdF_word {lab : Label → Int64} {g : WcG} {b : BitVec 64} {σ : AS} {l : WeakMem.AllocLabel}
    (hQ : rdQ.OK ms lab) (h : RdF lbl ms g R b σ l) {i : Nat} (hi : i = 0 ∨ i = 8) :
    ∃ A old : Nat, lbl l = some A ∧ (b + BitVec.ofNat 64 i).toNat = A + i ∧
      b + BitVec.ofNat 64 i = BitVec.ofNat 64 (ms.heap + 16 * old + ms.off 2 τ8 + i) ∧
      old + ms.units 2 τ8 ≤ ms.cells := by
  obtain ⟨A, old, hl, hb, hA, hold, -⟩ := h
  have hoff : ms.off 2 τ8 = 8 := by
    have h := hQ.off
    simp only [rdQ] at h
    rw [h]; decide
  have hcells := hQ.cells
  have hroom := hQ.room
  have hn : (b + BitVec.ofNat 64 i).toNat = A + i := by
    rw [BitVec.toNat_add, hb, BitVec.toNat_ofNat]
    rcases hi with rfl | rfl <;> omega
  refine ⟨A, old, hl, hn, BitVec.eq_of_toNat_eq ?_, hold⟩
  rw [hn, BitVec.toNat_ofNat]
  rcases hi with rfl | rfl <;> omega

omit [Executable.ValidLayout exe] in
/-- **The allocator's return after `rdE` is `sJp`'s**: the frame record
outside the allocator's region kept from the call, `%rbp` the caller's, the
source past the allocation. -/
theorem nbX_sJp (hlo : R.lo ≤ -8) (hhi : 8 ≤ R.hi) {F0 : MachineData → Prop} {g : WcG} {t : UInt64}
    {σ : AS} {c : Ctl}
    (h : (nbX (tpXa ms t) (_root_.Executable.labels exe).label lbl R 40
      ((_root_.Executable.labels exe).label ".Lwc_rodata.x13")
      (nbJc (_root_.Executable.labels exe).label rdE ((_root_.Executable.labels exe).label ".Lwc_rodata.entry") oR
        (sJ1 (sJE (_root_.Executable.labels exe).label ms F0 g R))) .ret).J σ c) :
    sJp lbl ms g R σ c := by
  obtain ⟨q, ⟨σC, ⟨σ0, ⟨⟨c0', ⟨σe, v, ⟨⟨-, hfp, hra, -, -⟩, -⟩, -, hsl⟩, hbp⟩, hc⟩, rfl⟩, hbpC, hkeep⟩,
    l, ini, old, hv, hcl, hx0, hold, -⟩ := h
  obtain ⟨hx, hτ, he, hn⟩ := rdQ_facts (callOK_untp q.2) hc
  obtain ⟨-, x, hw, hxv⟩ := hv
  simp only [Scc.Sem.wordAddr, Option.map_eq_some_iff] at hw
  obtain ⟨A, hl, rfl⟩ := hw
  have hx0' : σ.regs.rax.toNat = ms.heap + 16 * old + ms.off 2 τ8 := by rw [← hn, ← hτ]; exact hx0
  have hold' : old + ms.units 2 τ8 ≤ ms.cells := by rw [← hn, ← hτ]; exact hold
  have hk : ∀ k : Int, (k = 0 ∨ k = -8) → σ.slot k = σ0.slot k := by
    rintro k hk
    rw [hkeep k ⟨by omega, by omega, by omega⟩ (by simp only [Region.callee, Region.Off]; omega), rdE_run]
    simp only [upd_apply]
    rcases hk with rfl | rfl <;> simp
  have hs0 : σ0.slot = upd σe.slot (-8) σe.regs.rbp.toBitVec := by rw [hsl]; rfl
  refine ⟨l, ini, ⟨A, old, hl, by show σ.regs.rax.toNat = A; omega, by omega, hold', ?_, ?_, ?_⟩, ?_⟩
  · rw [hk 0 (.inl rfl), hs0, upd_apply]; simpa using hra
  · rw [hk (-8) (.inr rfl), hs0, upd_apply]; simpa using hfp
  · simp only [Reg64s.get64] at hbp ⊢
    rw [hbpC, rdE_run]
    simp only [Reg64s.set64]
    exact hbp
  · rw [hcl, hc, hx, hτ, he, hn]; rfl

/-- **`hello1.w`'s `wc_rodata` on x64 through the generic setup
composition** in any valid layout of `hello1Cells`, in a region of depth
`240` below the entry `%rsp` (`hlo`; the frame of 32 and the saved `%rbp`,
the allocator's return address and frame of 160, the heap abort's
dispatcher of 32, the last three in `Tcb.headroom` below `stackLimit`, not
in the need table) and the return address cell above (`hhi`): from the
setup call's entry (`uN0`, the source at `rodata`'s body, `hc0`) to the
return with `rdPostS`, `%rbp`, `%rsp` and the thread pointer as at the call
(`uNxS`). The allocation is `rdQ`, whose premises hold (`hQ`, `hu`); the
counter, the headers (`hmem`) and the buffer's words (`hbuf`) are unmapped
in private memory under `F`. An allocation of a fresh label lands in
`ms.xa` at the call's thread pointer (`hxa`). The heap abort's path is
given per caller's state and source control (`hstub`). The walk's states
lie in `W`, none moved by `K` (`hW`). -/
theorem hello1_rodata_setupGW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -240) (hhi : 8 ≤ R.hi) {F0 : MachineData → Prop} (hFF : ∀ m, F m → F0 m)
    (g : WcG) (hc0 : g.c0 = rdC0)
    (hQ : rdQ.OK ms (_root_.Executable.labels exe).label) (hu : ms.units 2 τ8 = 3)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hbuf : ∀ old : Nat, old + ms.units 2 τ8 ≤ ms.cells → ∀ i : Nat, (i = 0 ∨ i = 8) → ∀ m, F m →
      Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * old + ms.off 2 τ8 + i)) 8 = none)
    (hxa : ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop, (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-48, []⟩ mC σC ∧
        nbJc (_root_.Executable.labels exe).label rdE ((_root_.Executable.labels exe).label ".Lwc_rodata.entry") oR
          (sJ1 (sJE (_root_.Executable.labels exe).label ms F0 g R)) σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σC) c ∧
        CKept R (-48) (-160) 8 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R.callee (-48) (-160) 8) F' (Ea ms q.1 l b w) s c →
        TP g.tp s → ms.xa l b w s c)
    (hW : RdGW W K exe endPc R F ms lbl F0 g)
    (hstub : ∀ m0 σC c0, σC.regs.rdi.toBitVec = 2#64 →
      (∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = rdCN ∧ Jfull ms q c0) →
      Abort.Disp.StubHW W K p lbl ms exe endPc (R.callee (-216) (-24) 16)
        (fun m => F m ∧ CKept R (-216) (-24) 16 m0 m ∧ Abs R ⟨-208, []⟩ m0 σC) c0) :
    SegW W K p lbl ms
      (At exe endPc R F (uN0 (_root_.Executable.labels exe).label ms F0 "wc_rodata" 32 g))
      (At exe endPc R F (uNxS (rdPostS lbl ms) g)) := by
  let lab := (_root_.Executable.labels exe).label
  let J0 := sJ0 lab ms F0 g
  let ms' := tpXa ms g.tp
  let W' := NoSetFsW W K
  let Ab : Ctl → Prop := fun c => ∃ q : Call, q.OK ms lab ∧ q.c0 = rdCN ∧ Jfull ms q c
  have hin := hello1_rdEIn
  simp only [rdEIn, Bool.and_eq_true] at hin
  obtain ⟨h0, hgap⟩ := hin
  have e26 : lab ".Lwc_rodata.x13" = lab ".Lwc_rodata.entry" + Int64.ofNat 26 := label_labelGapB hp hgap
  have hrp := hello1_rpIn
  simp only [rpIn, Bool.and_eq_true] at hrp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩ := hrp
  have hk : oR.kill .rax = oR := rfl
  have i0 : BitVec.ofInt 64 (0 : Int64).toInt = BitVec.ofNat 64 0 := by decide
  have i8 : BitVec.ofInt 64 (8 : Int64).toInt = BitVec.ofNat 64 8 := by decide
  -- the allocation: `rdE` and the call
  have hs0 : SegW W' K p lbl ms' (At exe endPc R F (sEn lab ".Lwc_rodata.entry" 32 [] J0))
      (fun s c => At exe endPc R F ⟨lab ".Lwc_rodata.x13", ⟨-40, []⟩, sJp lbl ms g R⟩ s c ∨
        At exe endPc R F (sAb lab 40 Ab) s c) := by
    refine (alloc_stepW (fs := 40) (pc := lab ".Lwc_rodata.entry") (o := oR) (pcR := lab ".Lwc_rodata.x13")
      (J1 := sJ1 (sJE lab ms F0 g R)) (Ab := Ab) hp hend Alloc.hello1_allocIn hF hR (by decide)
      (by rw [allocAbortDepth_40]; omega) (by omega) (by simp [rdE]) rdE_ok (by omega) hhi
      (code_field hp hend h0 (ofNat_zero' _)) (fun σ => by rw [rdE_run]; exact ⟨rfl, rfl⟩) ?hloc ?hq
      ?hra (fun q hq a ha m hm => hmem q (callOK_untp hq) a ha m hm) ?hxa
      (BlkW.noSetFs hW.e (code_field hp hend h0 (ofNat_zero' _)) (by decide))
      (fun q _ hq => allocW_mono (Alloc.AllocW.noSetFs hp hend Alloc.hello1_allocIn (allocW_tp (hW.alloc q hq)))
        fun _ h => ⟨h.1, h.2.1⟩)
      (fun σ c h => nbX_sJp (by omega) hhi h) ?hab).mono_pre fun _ _ h => At.reg_addr (r := .rbp) (k := -8) rfl h
    case hloc =>
      rintro σ c hJ
      obtain ⟨⟨σe, v, ⟨⟨hc, -⟩, -⟩, -, -⟩, -⟩ := id hJ
      exact ⟨rdCN, by rw [hc, hc0]; exact rdC0_run, ⟨c, hJ⟩, rfl⟩
    case hq =>
      rintro σ c ⟨-, rfl⟩
      refine ⟨rdQ, callOK_tp hQ, rfl, ?_, ?_, ?_⟩ <;> rw [rdE_run]
      · rfl
      · rfl
      · show 3#64 = BitVec.ofNat 64 (ms.units 2 τ8)
        rw [hu]
    case hra =>
      intro σ c _
      rw [rdE_run, e26]
      simp only [upd_apply, Int64.toBitVec_add]
      simp only [show (-40 : Int) - 8 = -48 by decide, ↓reduceIte]
      rfl
    case hxa =>
      intro q F' h1 h2 l b w s c hl hAt htp
      exact hxa ⟨q.1, callOK_untp q.2⟩ F' h1 h2 l b w s c hl hAt htp
    case hab =>
      rintro c ⟨q, hf, σC, σ0, ⟨-, hc⟩, -⟩
      exact ⟨q.1, callOK_untp q.2, hc, hf⟩
  -- the first lane store, `"Hello, w"` at the buffer's base
  have hs1 : SegW W' K p lbl ms' (At exe endPc R F ⟨lab ".Lwc_rodata.x13", ⟨-40, []⟩, sJp lbl ms g R⟩)
      (fun s c => At exe endPc R F ⟨lab ".Lwc_rodata.x13" + Int64.ofNat 29 + Int64.ofNat 3, oR, sJ2 lbl ms g R⟩ s c ∨
        At exe endPc R F (sAb lab 40 Ab) s c) := by
    have hc1 := code_field hp hend c0 (ofNat_zero' _)
    have hc2 := code_field hp hend c1 (q := lab ".Lwc_rodata.x13" + 8) rfl
    have hc3 := code_field hp hend c2 (q := lab ".Lwc_rodata.x13" + 8 + Int64.ofNat 3) (by rw [Int64.add_assoc]; rfl)
    have hc4 := code_field hp hend c3 (q := lab ".Lwc_rodata.x13" + Int64.ofNat 29) rfl
    refine (lane_stepW (W := W') (B1 := rpB0) (B2 := rpB1) (zl := 3) (zs := 3) (o := oR) (oL := oR) (oS := oR)
      (t := .rax) (b := .rcx) (i := 0) (t' := .rax) (w := "w0") (ov := "o0") (bn := "b") (sg := false) (wd := .w8)
      (Kw := rdK1) (i' := 0) (e := eW1) (J := sJp lbl ms g R) (J' := sJ2 lbl ms g R)
      (by simp [rpB0]) (by simp [rpB1]) rpB0_ok rpB1_ok hF hR (by omega) hhi (by decide) hc1 hc2 hc3 hc4
      (fun σ => by rw [rpB0_run]; exact ⟨rfl, rfl⟩)
      (fun σ => by rw [hk, rpB1_run]; refine ⟨?_, rfl⟩; simp only [Int64.add_assoc]; rfl)
      (by decide) (by decide) rdK1_lt ?ht ?hsrc
      (BlkW.noSetFs hW.l1 hc1 (by decide)) (NodeW.noSetFs hW.l1L hc2 (by decide) (by decide))
      (BlkW.noSetFs hW.l1H hc3 (by decide)) (NodeW.noSetFs hW.l1S hc4 (by decide) (by decide))).mono_pre
      fun _ _ h => At.rbp_addr h fun σ c ⟨_, _, ⟨_, _, _, _, _, _, _, _, hb⟩, _⟩ => hb
    case ht =>
      rintro σ c ⟨l, ini, -, rfl⟩
      rfl
    case hsrc =>
      rintro σ c ⟨l, ini, hRF, rfl⟩
      obtain ⟨A, old, hl, hn, hb, hold⟩ := rdF_word hQ hRF (.inl rfl)
      obtain ⟨-, -, -, -, -, -, hs0', hs8, hbp⟩ := id hRF
      have ha : bAddr (arun lab rpB0 ⟨lab ".Lwc_rodata.x13", oR, σ⟩).σ.regs .rcx 0 =
          σ.regs.rax.toBitVec + BitVec.ofNat 64 0 := by
        rw [rpB0_run]; simp only [bAddr, i0, Reg64s.get64_set64_self]
      refine ⟨_, _, _, l, A, rfl, rfl, bufElem_b ini, hl, by rw [ha, hn], fun m hm => ?_, fun r => ?_⟩
      · rw [ha, hb]; exact hbuf old hold 0 (.inl rfl) m hm
      · simp only [hk, ownStep, rpB0_run, rpB1_run]
        refine ⟨?_, ?_, fun wold => ⟨l, ini, wold, ?_, rfl⟩⟩
        · simp only [bAddr, upd_apply, Reg64s.get64_set64_self,
            Reg64s.get64_set64_ne _ (show Reg64.rcx ≠ .rax by decide)]
          simp
        · rw [Reg64s.get64_set64_self]; decide
        · obtain ⟨A', old', hl', hb', hA', hold', -⟩ := hRF
          refine ⟨A', old', hl', ?_, hA', hold', ?_, ?_, ?_⟩
          · simpa [upd_apply] using hb'
          · simpa [upd_apply] using hs0'
          · simpa [upd_apply] using hs8
          · rw [Reg64s.get64_set64_ne _ (by decide), Reg64s.get64_set64_ne _ (by decide),
              Reg64s.get64_set64_ne _ (by decide), Reg64s.get64_set64_ne _ (by decide)]
            exact hbp
  -- the second lane store, `"orld\n"` at the buffer's base plus 8
  have hs2 : SegW W' K p lbl ms'
      (At exe endPc R F ⟨lab ".Lwc_rodata.x13" + Int64.ofNat 29 + Int64.ofNat 3, oR, sJ2 lbl ms g R⟩)
      (fun s c => At exe endPc R F ⟨lab ".Lwc_rodata.x13" + Int64.ofNat 58 + Int64.ofNat 4, oR, sJ4 lbl ms g R⟩ s c ∨
        At exe endPc R F (sAb lab 40 Ab) s c) := by
    have hc1 := code_field hp hend c4 (q := lab ".Lwc_rodata.x13" + Int64.ofNat 29 + Int64.ofNat 3)
      (by rw [Int64.add_assoc]; rfl)
    have hc2 := code_field hp hend c5 (q := lab ".Lwc_rodata.x13" + Int64.ofNat 36) rfl
    have hc3 := code_field hp hend c6 (q := lab ".Lwc_rodata.x13" + Int64.ofNat 36 + Int64.ofNat 4)
      (by rw [Int64.add_assoc]; rfl)
    have hc4 := code_field hp hend c7 (q := lab ".Lwc_rodata.x13" + Int64.ofNat 58) rfl
    refine lane_stepW (W := W') (B1 := rpB2) (B2 := rpB3) (zl := 4) (zs := 4) (o := oR) (oL := oR) (oS := oR)
      (t := .rax) (b := .rcx) (i := 8) (t' := .rax) (w := "w1") (ov := "o1") (bn := "b") (sg := false) (wd := .w8)
      (Kw := rdK2) (i' := 1) (e := eN) (J := sJ2 lbl ms g R) (J' := sJ4 lbl ms g R)
      (by simp [rpB2]) (by simp [rpB3]) rpB2_ok rpB3_ok hF hR (by omega) hhi (by decide) hc1 hc2 hc3 hc4
      (fun σ => by rw [rpB2_run]; refine ⟨?_, rfl⟩; simp only [Int64.add_assoc]; rfl)
      (fun σ => by rw [hk, rpB3_run]; refine ⟨?_, rfl⟩; simp only [Int64.add_assoc]; rfl)
      (by decide) (by decide) rdK2_lt ?ht ?hsrc
      (BlkW.noSetFs hW.l2 hc1 (by decide)) (NodeW.noSetFs hW.l2L hc2 (by decide) (by decide))
      (BlkW.noSetFs hW.l2H hc3 (by decide)) (NodeW.noSetFs hW.l2S hc4 (by decide) (by decide))
    case ht =>
      rintro σ c ⟨l, ini, wo0, -, rfl⟩
      rfl
    case hsrc =>
      rintro σ c ⟨l, ini, wo0, hRF, rfl⟩
      obtain ⟨A, old, hl, hn, hb, hold⟩ := rdF_word hQ hRF (.inr rfl)
      obtain ⟨-, -, -, -, -, -, hs0', hs8, hbp⟩ := id hRF
      have ha : bAddr (arun lab rpB2 ⟨lab ".Lwc_rodata.x13" + Int64.ofNat 29 + Int64.ofNat 3, oR, σ⟩).σ.regs .rcx 8 =
          σ.slot (-16) + BitVec.ofNat 64 8 := by
        rw [rpB2_run]; simp only [bAddr, i8, Reg64s.get64_set64_self]
      refine ⟨_, _, _, l, A, rfl, rfl, bufElem_b ini, hl, by rw [ha, hn], fun m hm => ?_, fun r => ?_⟩
      · rw [ha, hb]; exact hbuf old hold 8 (.inr rfl) m hm
      · simp only [hk, ownStep, rpB2_run, rpB3_run]
        refine ⟨?_, ?_, fun wold => ⟨l, ini, wo0, wold, ?_, rfl⟩⟩
        · simp only [bAddr, upd_apply, Reg64s.get64_set64_self,
            Reg64s.get64_set64_ne _ (show Reg64.rcx ≠ .rax by decide)]
        · rw [Reg64s.get64_set64_self]; decide
        · obtain ⟨A', old', hl', hb', hA', hold', -⟩ := hRF
          refine ⟨A', old', hl', ?_, hA', hold', ?_, ?_, ?_⟩
          · simpa [upd_apply] using hb'
          · simpa [upd_apply] using hs0'
          · simpa [upd_apply] using hs8
          · rw [Reg64s.get64_set64_ne _ (by decide), Reg64s.get64_set64_ne _ (by decide),
              Reg64s.get64_set64_ne _ (by decide), Reg64s.get64_set64_ne _ (by decide)]
            exact hbp
  -- the epilogue
  have hs3 : SegW W' K p lbl ms'
      (At exe endPc R F ⟨lab ".Lwc_rodata.x13" + Int64.ofNat 58 + Int64.ofNat 4, oR, sJ4 lbl ms g R⟩)
      (fun s c => At exe endPc R F (sRet (rdPostS lbl ms) g) s c ∨ At exe endPc R F (sAb lab 40 Ab) s c) := by
    have hc := code_field hp hend c8 (q := lab ".Lwc_rodata.x13" + Int64.ofNat 58 + Int64.ofNat 4)
      (by rw [Int64.add_assoc]; rfl)
    refine (ret_stepW (n := ⟨lab ".Lwc_rodata.x13" + Int64.ofNat 58 + Int64.ofNat 4, oR, sJ4 lbl ms g R⟩)
      (PostS := rdPostS lbl ms) (g := g) (by simp [rpB4]) rpB4_ok hF hR (by omega) hhi hc
      (BlkW.noSetFs hW.ret hc (by decide))
      ?_).mono_post fun _ _ h => .inl h
    rintro σ c ⟨l, ini, wo0, wo1, ⟨A, old, hl, hb, hA, hold, h0, h8, -⟩, rfl⟩
    rw [rpB4_run]
    refine ⟨by rw [h0], rfl, rdRet l ini wo0 wo1, rdC4_run l ini wo0 wo1,
      ⟨l, ini, wo0, wo1, A, old, rfl, hl, ?_, hA, hold, ?_, ?_, ?_⟩, ?_⟩
    · simpa [Reg64s.set64] using hb
    · simp [Reg64s.set64]
    · simp [Reg64s.set64]
    · simp [Reg64s.set64]
    · simpa [Reg64s.set64] using h8
  -- the walk
  have hbody : SegW W' K p lbl ms' (At exe endPc R F (sEn lab ".Lwc_rodata.entry" 32 [] J0))
      (fun s c => At exe endPc R F (sRet (rdPostS lbl ms) g) s c ∨ At exe endPc R F (sAb lab 40 Ab) s c) :=
    chainW (A := fun k => match k with
      | 0 => At exe endPc R F (sEn lab ".Lwc_rodata.entry" 32 [] J0)
      | 1 => At exe endPc R F ⟨lab ".Lwc_rodata.x13", ⟨-40, []⟩, sJp lbl ms g R⟩
      | 2 => At exe endPc R F ⟨lab ".Lwc_rodata.x13" + Int64.ofNat 29 + Int64.ofNat 3, oR, sJ2 lbl ms g R⟩
      | _ => At exe endPc R F ⟨lab ".Lwc_rodata.x13" + Int64.ofNat 58 + Int64.ofNat 4, oR, sJ4 lbl ms g R⟩) 3
      (fun k hk => by
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
        · exact hs0
        · exact hs1
        · exact hs2)
      hs3
  have e40 : (32 : Int64).toInt + 8 = 40 := by decide
  refine setup_callW hp hend hK hello1_rodataPro (by decide) (by decide) (by simp) hF hR
    (by rw [e40, allocAbortDepth_40]; omega) (by omega) hFF g hW.pro (by rw [e40]; exact hbody) ?_
  intro m0 σC c0 h2 hab
  rw [e40, allocAbortDepth_40]
  exact hstub m0 σC c0 h2 hab

/-- **`hello1_rodata_setupGW` to the named post**: the return at
`SetupPostS` with the reader `rdX64` and the places `hello1Pl`. -/
theorem hello1_rodata_setupGW_ret {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -240) (hhi : 8 ≤ R.hi) {F0 : MachineData → Prop} (hFF : ∀ m, F m → F0 m)
    (g : WcG) (hc0 : g.c0 = rdC0)
    (hQ : rdQ.OK ms (_root_.Executable.labels exe).label) (hu : ms.units 2 τ8 = 3)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hbuf : ∀ old : Nat, old + ms.units 2 τ8 ≤ ms.cells → ∀ i : Nat, (i = 0 ∨ i = 8) → ∀ m, F m →
      Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * old + ms.off 2 τ8 + i)) 8 = none)
    (hxa : ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop, (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-48, []⟩ mC σC ∧
        nbJc (_root_.Executable.labels exe).label rdE ((_root_.Executable.labels exe).label ".Lwc_rodata.entry") oR
          (sJ1 (sJE (_root_.Executable.labels exe).label ms F0 g R)) σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σC) c ∧
        CKept R (-48) (-160) 8 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R.callee (-48) (-160) 8) F' (Ea ms q.1 l b w) s c →
        TP g.tp s → ms.xa l b w s c)
    (hW : RdGW W K exe endPc R F ms lbl F0 g)
    (hstub : ∀ m0 σC c0, σC.regs.rdi.toBitVec = 2#64 →
      (∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = rdCN ∧ Jfull ms q c0) →
      Abort.Disp.StubHW W K p lbl ms exe endPc (R.callee (-216) (-24) 16)
        (fun m => F m ∧ CKept R (-216) (-24) 16 m0 m ∧ Abs R ⟨-208, []⟩ m0 σC) c0) :
    SegW W K p lbl ms
      (At exe endPc R F (uN0 (_root_.Executable.labels exe).label ms F0 "wc_rodata" 32 g))
      (At exe endPc R F (uNxS (SetupPostS lbl rdX64 hello1Pl) g)) :=
  (hello1_rodata_setupGW hp hend hK hF hR hlo hhi hFF g hc0 hQ hu hmem hbuf hxa hW hstub).mono_post
    fun _ _ ⟨he, hn, hdc, hpc, σ, hA, hD, hP, hrest⟩ => ⟨he, hn, hdc, hpc, σ, hA, hD, rdPostS_setupPostS hP, hrest⟩

end Proof

/-! ## The hand chain at `rodata`'s source

The hand chain (`hello1_rodata_pre_segW`, `hello1_rodata_post_segW`, and
`hello1_main_post_segW`, `hello1_main_segW`, `hello1_main_segW_src` over them) asks the source at
the allocation's entry to be the allocation (`hq`) and at `.x13` to be an exchange site (`h1`),
with no local steps in between. At `rodata`'s source neither holds: the entry `rdC0` is two
local steps before the allocation (`rdC0_not_call`), and the allocator returns to `rdCA`, one
`asLanes` step before the exchange (`rdCA_not_xchgSite`). So with the entry at `rdCN`, the
premises force the allocator's return node to be empty (`hand_x13_empty`). The generic walk
above takes those steps (`rdC0_run`, `lane_stepW`). -/

/-- `rodata`'s entry is no allocation: `let two = 2` comes first. -/
theorem rdC0_not_call {ms : MemSide isa} {lab : Label → Int64} {q : Call} (h : q.OK ms lab) : q.c0 ≠ rdC0 := by
  intro hc
  have ht := h.term
  rw [hc] at ht
  simp [rdC0, Spike.Lib.Hello1RodataSrc.rdBody] at ht

/-- The allocator's return `rdCA` is no exchange site: `asLanes` comes first. -/
theorem rdCA_not_xchgSite {l : WeakMem.AllocLabel} {ini : Nat} {x : String} {sa : WeakMem.Address} {u : Ty}
    {v : CoreTerm.At} {e : Expr} : ¬ XchgSite (rdCA l ini) x sa u v e := by
  rintro ⟨-, ⟨_, _, _, _, ht, -⟩ | ⟨_, _, _, _, _, _, _, _, _, ht, -⟩⟩ <;>
    simp [rdCA, Spike.Lib.Hello1RodataSrc.eW0] at ht

/-- **The allocator's returns from `rodata`'s allocation** are at `rdCA`. -/
theorem rX13_rdCA {ms : MemSide isa} {lab : Label → Int64} {lbl : WeakMem.AllocLabel → Option Nat} {R : Region}
    {J0 : AS → Ctl → Prop} (hJ0 : ∀ σ c, J0 σ c → c = rdCN) {σ : AS} {c : Ctl}
    (h : (rX ms lab lbl R J0 .x13).J σ c) : ∃ l ini, c = rdCA l ini := by
  obtain ⟨q, ⟨σe, hJe, -, -⟩, -, l, ini, old, -, hcl, -⟩ := h
  have hc := hJ0 _ _ hJe
  obtain ⟨hx, hτ, he, hn⟩ := rdQ_facts q.2 hc
  exact ⟨l, ini, by rw [hcl, hc, hx, hτ, he, hn]; rfl⟩

/-- **The hand chain is empty at `.x13` at `rodata`'s source**: with the entry at `rdCN`, an
invariant `Jp` at `.x13` holding the allocator's returns (as `hello1_main_segW`'s `hret` asks)
and an exchange site at each of its controls (as `hello1_rodata_post_segW`'s `h1` asks), the
allocator's return node has no state. -/
theorem hand_x13_empty {ms : MemSide isa} {lab : Label → Int64} {lbl : WeakMem.AllocLabel → Option Nat}
    {R : Region} {J0 Jp : AS → Ctl → Prop} {Q : AS → Ctl → String → WeakMem.Address → Ty → CoreTerm.At → Expr → Prop}
    (hJ0 : ∀ σ c, J0 σ c → c = rdCN) (hret : ∀ σ c, (rX ms lab lbl R J0 .x13).J σ c → Jp σ c)
    (h1 : ∀ σ0 c, Jp σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Q σ0 c x sa u v e) :
    ∀ σ c, ¬ (rX ms lab lbl R J0 .x13).J σ c := by
  intro σ c h
  obtain ⟨l, ini, rfl⟩ := rX13_rdCA hJ0 h
  obtain ⟨_, _, _, _, _, hx, -⟩ := h1 σ _ (hret σ _ h)
  exact rdCA_not_xchgSite hx

end Spike.Lib.X64.Flow.Hello1
