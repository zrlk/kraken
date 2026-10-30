/-
**`ret0.w` on AArch64: the instance glue** (milestone H0; `Scc/DESIGN.md`
§6, *Per-program instance glue*). This file composes the runtime and
program segments that exist (`Spike/Lib/A64Ret0Segs.lean`, the S2/S4
specifications in `Spike/Lib/A64Ret0AllocTcb.lean` and
`Spike/Lib/A64Ret0StackTake.lean`) into the whole functions of the main
path, and records the own words. It is hand-written. It is laid out as the
template the M3 generator will emit (one section per function, one node per
block or single instruction).

The main path is `_start → scc_rt_start → {alloc_tcb, thread_init
(→ stack_take)} → scc_rt_main → wc_main → exit_group`.

- **Own words** (`PcIn`, `PreRmw`, `pnextOwn`): the runtime words the
  thread holds alone on the main path, with their values by pc.
- **Calls** go through `call_nd_F` (`Spike/Lib/A64Call.lean`): the callee
  may use the caller's frame condition (the unmapped runtime words a callee
  touches are a fact of the caller's `F`).
- **The stack limit** (`limA`, `LimOk`): the facts a stack-checked prologue
  needs about `[tpidr_el0, #8]`.
- **`wc_main`** (`wc_seg`): prologue then body, from its label to the
  return address with `x0 = 42`.
- **`scc_rt_main`** (`main_seg`): prologue, the call of `wc_main`, the
  `exit_group` tail; a segment to any fragment.
- **Own-word accesses** (`ownLdop_nd`, `ownSwp_nd`, `ownLdr_nd`,
  `ownStlr_nd`): the runtime's RMWs, loads and releases of the words it
  owns, through `Out.rtRmw`/`rtLoad`/`rtStore`; the value there is the
  own map's (`OwnAt`, named until `ms.own` is wired).
- **`scc_rt_alloc_tcb`** (`alloc_tcb_seg`): one callee segment over its
  nodes `tcbN`. The header store goes through `StOk`; the counter's add
  through `ownLdop_nd` (`TcbOk`).
- **`scc_rt_stack_take`** (`stack_take_seg`) and **`scc_rt_thread_init`**
  (`thread_init_seg`, with the take nested through `call_nd_F`): callee
  segments. The TCB stores go through `StOk`; the take's four own-word
  accesses through the own-word nodes (`TakeOk`).
- **`scc_rt_start`** (`start_seg`, never returns): `start_sp2_seg` (to
  `.sp2`), `start_sp2_sw_seg` (the call of `scc_rt_thread_init`, to the
  switch), `start_switch_seg` (`add sp, x9, #0` via `sw_nd`/`sw_seq`, then
  `main_seg` in the new stack's region). The premises still open are
  listed in the TODO section at the end.

The memory-side facts of the runtime words are kept together in `LimOk`,
`StOk`, `LdOk`, `TcbOk` and `TakeOk`.
-/
import Spike.Lib.A64Ret0Segs
import Spike.Lib.A64Call
import Spike.Lib.A64Ret0AllocTcb
import Spike.Lib.A64Ret0StackTake
import Spike.Lib.A64Ret0ThreadInit
import Spike.Lib.A64Switch
import Spike.Lib.SegCommon

namespace Spike.Lib.A64.Flow.Ret0

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)

set_option linter.unusedSimpArgs false

/-! ## The stack limit -/

/-- **The stack-limit word** `[tpidr_el0, #8]` for the thread pointer `tp`
(`Scc.IR.Tcb.stackLimit`). -/
def limA (tp : UInt64) : BitVec 64 := BitVec.ofInt 64 (tp.toBitVec.toInt + (8 : Int64).toInt)

theorem tcbA_limA {r : Reg64s} {tp : UInt64} (h : r.TPIDR_EL0 = tp) : tcbA r 8 = limA tp := by
  simp [tcbA, limA, h]

/-- **What a stack-checked prologue needs of the limit word `a`** (the
memory-side facts, kept together): it is the runtime's, mapped for a read
(`MemSide.mp`), not thread-private memory under `F`, and every value runtime
memory may hold there is at most `Z`, the new
frame's `sp`. -/
structure LimOk (ms : MemSide isaLSE2) (F : MachineData → Prop) (exe : _root_.Executable) (endPc : Int64)
    (a Z : BitVec 64) : Prop where
  rt : ms.rt a.toNat
  mp : ms.mp ⟨a, 8⟩ false
  unmapped : ∀ m, F m → Mem.loadInt m.dmem a 8 = none
  room : ∀ v : Val, ms.G ⟨a, 8⟩ v → (v.setWidth 64).toNat ≤ Z.toNat

theorem LimOk.mono {ms : MemSide isaLSE2} {F F' : MachineData → Prop} {exe : _root_.Executable} {endPc : Int64}
    {a Z : BitVec 64} (h : LimOk ms F exe endPc a Z) (hFF : ∀ m, F' m → F m) : LimOk ms F' exe endPc a Z :=
  ⟨h.rt, h.mp, fun m hm => h.unmapped m (hFF m hm), h.room⟩

/-! ## `wc_main` -/

/-- **The ghosts of a call of `wc_main`**: the caller's `x29`, the return
address, `sp` and the thread pointer at the call, the source control. -/
structure WcG where
  fp : BitVec 64
  ra : BitVec 64
  sp : BitVec 64
  tp : UInt64
  c0 : Ctl

section Wc

variable (ms : MemSide isaLSE2) (F : MachineData → Prop) (exe : _root_.Executable) (endPc : Int64)
  (lab : Label → Int64)

/-- **`wc_main`'s entry**: the ghosts' registers, and the limit word's facts
for its frame of 32 (`F` the caller's frame condition). -/
def wcN0 (g : WcG) : ND := ⟨lab "wc_main", ⟨0, []⟩, fun σ c =>
  (c = g.c0 ∧ σ.regs.X29.toBitVec = g.fp ∧ σ.regs.X30.toBitVec = g.ra ∧ σ.regs.SP.toBitVec = g.sp ∧
    σ.regs.TPIDR_EL0 = g.tp) ∧ LimOk ms F exe endPc (limA g.tp) (g.sp - (32 : Int64).toBitVec)⟩

/-- `wc_main`'s body entry: the saved `x29` and return address. -/
def wcN1 (g : WcG) : ND :=
  ⟨lab ".L18_wc_main.0_entry", ⟨-32, []⟩, fun σ c => c = g.c0 ∧ σ.slot (-16) = g.fp ∧ σ.slot (-8) = g.ra⟩

/-- **`wc_main`'s return**: at the return address, `x0 = 42`, `x29`/`x30`
restored, `sp` at the entry's offset. -/
def wcNx (g : WcG) : ND := ⟨Int64.ofBitVec g.ra, ⟨0, []⟩, fun σ c =>
  c = g.c0 ∧ σ.regs.X0.toBitVec = 42#64 ∧ σ.regs.X29.toBitVec = g.fp ∧ σ.regs.X30.toBitVec = g.ra⟩

end Wc

section WcProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F F0 : MachineData → Prop}

/-- **`wc_main` is one segment** in any valid layout of `ret0Prog`, for any
region holding its frame of 32 and any frame condition implying the one the
limit word's facts are stated under. -/
theorem wc_seg (hp : Lays exe SccCode.ret0Prog) (hend : endPc = endOf exe SccCode.ret0Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -32) (hhi : 0 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (g : WcG) :
    Seg p lbl ms (At exe endPc R F (wcN0 ms F0 exe endPc (_root_.Executable.labels exe).label g))
      (At exe endPc R F (wcNx g)) := by
  let lab := (_root_.Executable.labels exe).label
  refine Seg.of_imp (P := At exe endPc R F ⟨lab "wc_main", ⟨0, []⟩, fun σ c => c = g.c0 ∧
      σ.regs.X29.toBitVec = g.fp ∧ σ.regs.X30.toBitVec = g.ra ∧ σ.regs.SP.toBitVec = g.sp ∧
      σ.regs.TPIDR_EL0 = g.tp⟩) (L := LimOk ms F0 exe endPc (limA g.tp) (g.sp - (32 : Int64).toBitVec))
      (fun hlim0 => ?_) |>.mono_pre ?_
  · have hlim := hlim0.mono hFF
    refine Seg.seq (ret0_wc_prologue_seg hp hend (nb := wcN1 lab g) hF hR hal hlo hhi rfl wcBody_le ?_)
      (ret0_wc_body_seg hp hend hF hR hal hlo hhi rfl ?_ ?_)
    · rintro σ c ⟨rfl, h29, h30, hsp, htp⟩
      rw [tcbA_limA htp]
      refine ⟨hlim.rt, hlim.mp, hlim.unmapped, fun v hv => ⟨?_, fun σ' _ hs => ⟨rfl, ?_, ?_⟩⟩⟩
      · rw [hsp]; exact hlim.room v hv
      · rw [hs]; simp [stSlots, frSlot, Spike.Lib.upd_apply, h29]
      · rw [hs]; simp [stSlots, frSlot, Spike.Lib.upd_apply, h30]
    · rintro σ c ⟨-, -, h8⟩
      simp [wcNx, h8]
    · rintro σ c ⟨rfl, h16, h8⟩ σ' - h0 h29 h30
      exact ⟨rfl, h0, h29.trans h16, h30.trans h8⟩
  · rintro s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ, hL⟩
    exact ⟨⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hL⟩

end WcProof

/-! ## `scc_rt_main` -/

/-- `scc_rt_main`'s body: the call of `wc_main`. -/
def mainCall : List Directive := parseAArch64("bl wc_main")

block_spec mainCall (-48) 0 (⟨-48, []⟩ : SO) mainCall

/-- **`scc_rt_main`'s call in `prog`**: `bl wc_main` at `.0_entry`, `.sp0`
right after it. -/
def mainIn (prog : List Directive) : Bool :=
  blockAt prog ".L1_scc_rt_main.0_entry" 0 mainCall &&
    labelGap prog ".L1_scc_rt_main.0_entry" ".L1_scc_rt_main.sp0" 1

theorem ret0_mainIn : mainIn SccCode.ret0Prog = true := by decide +kernel

/-- **The ghosts of `scc_rt_main`'s run**: `sp` and the thread pointer at
its entry, the source control. -/
structure MainG where
  sp0 : BitVec 64
  tp : UInt64
  c0 : Ctl

section Main

variable (lab : Label → Int64)

/-- `scc_rt_main`'s entry. -/
def mainN0 (g : MainG) : ND := ⟨lab "scc_rt_main", ⟨0, []⟩, fun σ c =>
  c = g.c0 ∧ σ.regs.SP.toBitVec = g.sp0 ∧ σ.regs.TPIDR_EL0 = g.tp⟩

/-- `scc_rt_main`'s body entry, the frame of 48 set up. -/
def mainN1 (g : MainG) : ND := ⟨lab ".L1_scc_rt_main.0_entry", ⟨-48, []⟩, fun σ c =>
  c = g.c0 ∧ σ.regs.SP.toBitVec = g.sp0 - (48 : Int64).toBitVec ∧ σ.regs.TPIDR_EL0 = g.tp⟩

/-- The call node: at `wc_main`'s label, the return address `.sp0`. -/
def mainNC (g : MainG) : ND := ⟨lab "wc_main", ⟨-48, []⟩, fun σ c =>
  (c = g.c0 ∧ σ.regs.SP.toBitVec = g.sp0 - (48 : Int64).toBitVec ∧ σ.regs.TPIDR_EL0 = g.tp) ∧
    σ.regs.X30.toBitVec = (lab ".L1_scc_rt_main.0_entry" + 4).toBitVec⟩

/-- Back from `wc_main`, at `.sp0`: its result `42` in `x0`. -/
def mainNR (g : MainG) : ND := ⟨lab ".L1_scc_rt_main.sp0", ⟨-48, []⟩, fun σ c =>
  c = g.c0 ∧ σ.regs.X0.toBitVec = 42#64⟩

/-- The `exit_group` call of `scc_rt_main`'s tail (after its block of
three): `main`'s result `42` still in `x0`. -/
def mainNX : ND := ⟨lab ".L1_scc_rt_main.sp0" + 4 + 4 + 4, ⟨-48, []⟩, fun σ _ => σ.regs.X0.toBitVec = 42#64⟩

end Main

section MainProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

theorem setXReg_TPIDR (r : Reg64s) (x : XReg) (v : BitVec 64) :
    (r.setXReg x v).TPIDR_EL0 = r.TPIDR_EL0 := by
  cases x <;> rfl

omit [Kraken.Executable.ValidLayout exe] in
/-- A segment to the single node of `Next`. -/
theorem seg_one {P : Frag isaLSE2} {n : ND}
    (h : Seg p lbl ms P (Next exe endPc R F (fun _ : Unit => n) (fun e : Empty => e.elim))) :
    Seg p lbl ms P (At exe endPc R F n) :=
  h.mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim

theorem ofInt_bmod (y : Int) : BitVec.ofInt 64 (y.bmod 18446744073709551616) = BitVec.ofInt 64 y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt]
  rw [Int.bmod_emod]

/-- **`scc_rt_main` does not return**: in any valid layout of `ret0Prog`,
from its entry (`sp` at offset 0 of a region holding its frame of 48 and
`wc_main`'s of 32) a segment to any fragment, given the limit word's facts
for both frames, and that the `exit_group(42)` there off an abort site is
`main`'s exit (`hexit`). -/
theorem main_seg (hp : Lays exe SccCode.ret0Prog) (hend : endPc = endOf exe SccCode.ret0Prog)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) (g : MainG)
    (hlimM : LimOk ms F exe endPc (limA g.tp) (g.sp0 - (48 : Int64).toBitVec))
    (hlimW : LimOk ms F exe endPc (limA g.tp) (g.sp0 - (48 : Int64).toBitVec - (32 : Int64).toBitVec))
    (hexit : ∀ s, At exe endPc R F (mainNX (_root_.Executable.labels exe).label) s g.c0 → ¬ ms.abortAt s →
      MainExit p ms s g.c0 42)
    {Q : Frag isaLSE2} :
    Seg p lbl ms (At exe endPc R F (mainN0 (_root_.Executable.labels exe).label g)) Q := by
  let lab := (_root_.Executable.labels exe).label
  have hin := ret0_mainIn
  simp only [mainIn, Bool.and_eq_true] at hin
  have esp0 := label_labelGap hp hin.2
  have hlo48 : R.lo ≤ -48 := by omega
  refine Seg.seq (ret0_main_prologue_seg hp hend (nb := mainN1 lab g) hF hR hal hlo48 hhi rfl
    (by show SO.le ⟨-48, []⟩ (oFr 48) = true; decide) ?_)
    (Seg.seq (Q := At exe endPc R F (mainNC lab g)) ?_
      (Seg.seq (Q := At exe endPc R F (mainNR lab g)) ?_
        (ret0_main_exit_seg hp hend rfl rfl hK hF hR hal hlo48 hhi fun s c σ0 hJ hAt => ?_)))
  · -- the prologue
    rintro σ c ⟨rfl, hsp, htp⟩
    rw [tcbA_limA htp]
    refine ⟨hlimM.rt, hlimM.mp, hlimM.unmapped, fun v hv => ⟨?_, fun σ' hr _ => ⟨rfl, ?_, ?_⟩⟩⟩
    · rw [hsp]; exact hlimM.room v hv
    · rw [hr]; simp [frRegs, ldStep, chkRegs, hsp]
    · rw [hr]; simp [frRegs, ldStep, chkRegs, setXReg_TPIDR, htp]
  · -- `bl wc_main`
    refine seg_one (seg_nd (by simp [mainCall]) mainCall_ok hF hR hal hlo48 hhi
      (code_of hp hend hin.1 (ofNat4_zero _)) fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
    · dsimp only [mainN1, mainNC]; rw [mainCall_run]
    · dsimp only [mainN1, mainNC]; rw [mainCall_run]; rfl
    · dsimp only [mainN1, mainNC] at hJ ⊢; rw [mainCall_run]
      obtain ⟨rfl, hsp, htp⟩ := hJ
      refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩ <;> simp_all [Spike.Lib.int64_ofInt_toInt]
      rw [ofInt_bmod, BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt]; rfl
  · -- the call
    refine seg_one (call_nd_F (lo' := -32) (hi' := 0) (Ne := wcN0 ms F exe endPc lab) (Ex := fun g _ => wcNx g)
      hR hal hF (by show R.lo ≤ -48 + -32; omega) (by decide) (by show (-48 : Int) < R.hi; omega) (by decide)
      (by show (-48 : Int) % 16 = 0; decide) (by decide) (by decide)
      (fun R' F' hR' hal' hlo' hhi' hF' hFF g' =>
        (wc_seg hp hend hF' hR' hal' hlo' hhi' hFF g').mono_post fun _ _ h => ⟨(), h⟩)
      (fun _ => rfl) ?_ ?_)
    · rintro σC c ⟨⟨rfl, hsp, htp⟩, h30⟩
      refine ⟨⟨σC.regs.X29.toBitVec, σC.regs.X30.toBitVec, σC.regs.SP.toBitVec, g.tp, g.c0⟩, rfl,
        ⟨rfl, rfl, rfl, rfl, htp⟩, ?_⟩
      show LimOk ms F exe endPc (limA g.tp) (σC.regs.SP.toBitVec - (32 : Int64).toBitVec)
      rw [hsp]; exact hlimW
    · rintro g' x σC c σx c' σR ⟨⟨rfl, -, -⟩, h30⟩ ⟨⟨hc, -, h30', -⟩, -⟩ ⟨hc', h42, -, -⟩ hreg - -
      refine .inl ⟨(), ?_, rfl, ⟨hc'.trans hc.symm, ?_⟩⟩
      · show lab ".L1_scc_rt_main.sp0" = Int64.ofBitVec g'.ra
        rw [← h30']
        show lab _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [h30, int64_ofBitVec_toBitVec]; exact esp0
      · show σR.regs.X0.toBitVec = 42#64
        rw [hreg]; exact h42
  · -- the exit: `exit_group(42)`
    obtain ⟨rfl, h42⟩ := hJ
    have h : σ0.regs.X0.toNat = 42 := by
      rw [show σ0.regs.X0.toNat = σ0.regs.X0.toBitVec.toNat from rfl, h42]; rfl
    rw [h]
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩ := hAt
    exact SysOk.exitGroup_main
      (hexit s ⟨he, hn, hdc, hpc, σ, hA, hD, by show σ.regs.X0.toBitVec = _; rw [hx]; exact h42⟩)

end MainProof

/-! ## `scc_rt_alloc_tcb` -/

/-- **The ghosts of a call of `scc_rt_alloc_tcb`**: `sp`, `x29`, `x30` at
entry, the own word `scc_rt_pinned_next`'s value `n0` on entry, the source
control. -/
structure TcbG where
  g : AllocTcb.G
  n0 : BitVec 64
  c0 : Ctl

/-- **What a runtime store needs of its word `a`** (the memory-side facts,
kept together as `LimOk` is for loads): it is the runtime's, mapped for a
write (`MemSide.mp`), its memory may hold `v` there, it is not thread-private memory under `F`. -/
structure StOk (ms : MemSide isaLSE2) (F : MachineData → Prop) (exe : _root_.Executable) (endPc : Int64)
    (a v : BitVec 64) : Prop where
  rt : ms.rt a.toNat
  mp : ms.mp ⟨a, 8⟩ true
  G : ms.G ⟨a, 8⟩ (v.setWidth 128)
  unmapped : ∀ m, F m → Mem.loadInt m.dmem a 8 = none

theorem StOk.mono {ms : MemSide isaLSE2} {F F' : MachineData → Prop} {exe : _root_.Executable} {endPc : Int64}
    {a v : BitVec 64} (h : StOk ms F exe endPc a v) (hFF : ∀ m, F' m → F m) : StOk ms F' exe endPc a v :=
  ⟨h.rt, h.mp, h.G, fun m hm => h.unmapped m (hFF m hm)⟩

/-- **What a runtime load needs of its word `a`**: it is the runtime's,
mapped for a read (`MemSide.mp`), not thread-private memory under `F`
(`LimOk` without the room). -/
structure LdOk (ms : MemSide isaLSE2) (F : MachineData → Prop) (exe : _root_.Executable) (endPc : Int64)
    (a : BitVec 64) : Prop where
  rt : ms.rt a.toNat
  mp : ms.mp ⟨a, 8⟩ false
  unmapped : ∀ m, F m → Mem.loadInt m.dmem a 8 = none

theorem LdOk.mono {ms : MemSide isaLSE2} {F F' : MachineData → Prop} {exe : _root_.Executable} {endPc : Int64}
    {a : BitVec 64} (h : LdOk ms F exe endPc a) (hFF : ∀ m, F' m → F m) : LdOk ms F' exe endPc a :=
  ⟨h.rt, h.mp, fun m hm => h.unmapped m (hFF m hm)⟩

/-- **The thread owns the word `a` with value `v` at `pc`** (`MemSide.own`):
at every state of the executable at that pc. A named hypothesis of the
segments until the own map is wired (TODO(own): `ms.own` from the own words
by pc, below). -/
def OwnAt (ms : MemSide isaLSE2) (exe : _root_.Executable) (endPc pc : Int64) (a v : BitVec 64) : Prop :=
  ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = pc → (⟨a, 8⟩, v.setWidth 128) ∈ ms.own s

/-- A store's address `[x10, #i]` with `x10 = t`. -/
theorem rAddr_x10 {r : Reg64s} {t : BitVec 64} (h : r.X10.toBitVec = t) (i : Int64) :
    rAddr r .X10 i = t + BitVec.ofInt 64 i.toInt := by
  simp [rAddr, Reg64s.getXReg, h, BitVec.ofInt_add]

/-- A store's value `x9`. -/
theorem getRegOrZr_x9 (r : Reg64s) : r.getRegOrZr (.low (.reg .X9) .W64) = r.X9.toBitVec := by
  rw [Spike.Lib.A64.Alloc.getRegOrZr_x]; rfl

/-! ## Own-word accesses as nodes

The runtime's accesses to its own words, through `Out.rtRmw`, `Out.rtLoad`
and `Out.rtStore`: the old value (or the value read) is the owned one
(`OwnAt`), so the state after the access is determined. The source
stutters. -/

section OwnNodes

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- The state after an access writing `Xt` (`Abs`, the frame condition, the
pc), landing in `Next`. -/
theorem land_ldStep {s : State} {c : Ctl} {n : ND} {t : XReg} {v : BitVec 64} {σ : AS} (hF : FStable R F)
    (he : s.exe = exe) (hn : s.endPc = endPc) (hdc : s.decls = {}) (hpc : s.st.2 = n.pc) (hA : Abs R n.o s.st.1 σ)
    (hD : F s.st.1) (hL : Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill t, ldStep t v σ⟩ c) :
    Next exe endPc R F N E (after s 4 { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) v }) c := by
  have hA' : Abs R (n.o.kill t) { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) v }
      (ldStep t v σ) := by
    refine ⟨by simp only [ldStep, hA.regs], hA.status, ?_, hA.slot⟩
    exact hA.so.killZ (.low (.reg t) .W64) v
  have hD' : F { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) v } :=
    hF _ _ hD fun _ _ _ => rfl
  have hs1 : after s 4 { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) v } =
      { s with st := ({ s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) v },
        n.pc + Int64.ofNat 4) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA' hD'⟩
  · exact .inr ⟨y, hy.at he hn hdc hA' hD'⟩

theorem setWidth_128_64 (v : BitVec 64) : (v.setWidth 128).setWidth 64 = v := by simp

/-- **A node at an own word's `ld<op><k> Xs, Xt, [Xn]`**: `Xn` holds the
word's address `A`, the thread owns it with value `v` (`hown`), and the new
value is one runtime memory may hold there (`StOk`); `Xt` gets `v`. Inside `W`, not moved by `K` (`hW`). -/
theorem ownLdop_ndW {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {op : AtomicOp} {k : RmwKind} {rs rt b : XReg} {A v : BitVec 64} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [ldopDir op k rs rt b])
    (hown : OwnAt ms exe endPc n.pc A v)
    (hW : NodeW W K exe endPc R F n)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = A ∧
      StOk ms F exe endPc A (op.apply v (σ.regs.getRegOrZr (.low (.reg rs) .W64))) ∧
      Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill rt, ldStep rt v σ⟩ c) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (ldopDir op k rs rt b) 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨hb, hS, hL⟩ := hedge _ σ c hA hD hJ
  have hb' : (s.st.1.regs.getXReg b).toBitVec = A := by rw [hA.regs]; exact hb
  have hex := exec_ldop hc (by rw [hb']; exact hS.unmapped _ hD)
  rw [hb', access_agrees (agrees_of_decls hdc _ _)] at hex
  refine .rtRmw k _ _ _ c hex hS.rt hS.mp (.refl c) fun old _ ho => ?_
  obtain rfl := ho _ (hown s he hn hpc)
  refine ⟨fun new hnew => ?_, ?_⟩
  · simp only [Option.some.injEq] at hnew
    subst hnew
    rw [setWidth_128_64, hA.regs]; exact hS.G
  · rw [setWidth_128_64]; exact land_ldStep hF he hn hdc hpc hA hD hL

/-- **A node at an own word's `ld<op><k> Xs, Xt, [Xn]`**: `Xn` holds the
word's address `A`, the thread owns it with value `v` (`hown`), and the new
value is one runtime memory may hold there (`StOk`); `Xt` gets `v`. -/
theorem ownLdop_nd {n : ND} {op : AtomicOp} {k : RmwKind} {rs rt b : XReg} {A v : BitVec 64} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [ldopDir op k rs rt b])
    (hown : OwnAt ms exe endPc n.pc A v)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = A ∧
      StOk ms F exe endPc A (op.apply v (σ.regs.getRegOrZr (.low (.reg rs) .W64))) ∧
      Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill rt, ldStep rt v σ⟩ c) :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (ownLdop_ndW hF hcode hown NodeW.triv hedge).toSeg

/-- **A node at an own word's `swp<k> Xs, Xt, [Xn]`**: as `ownLdop_nd`, the
new value `Xs`'s. Inside `W`, not moved by `K` (`hW`). -/
theorem ownSwp_ndW {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {k : RmwKind} {rs rt b : XReg} {A v : BitVec 64} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s n.pc [.instr ⟨.W64, .SWP k .W64 (.low (.reg rs) .W64) (.low (.reg rt) .W64) (.low (.reg b) .W64)⟩])
    (hown : OwnAt ms exe endPc n.pc A v)
    (hW : NodeW W K exe endPc R F n)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = A ∧ StOk ms F exe endPc A (σ.regs.getRegOrZr (.low (.reg rs) .W64)) ∧
      Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill rt, ldStep rt v σ⟩ c) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (.instr ⟨.W64, .SWP k .W64 (.low (.reg rs) .W64) (.low (.reg rt) .W64) (.low (.reg b) .W64)⟩) 4 :=
    (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨hb, hS, hL⟩ := hedge _ σ c hA hD hJ
  have hb' : (s.st.1.regs.getXReg b).toBitVec = A := by rw [hA.regs]; exact hb
  have hex := exec_swp hc (by rw [hb']; exact hS.unmapped _ hD)
  rw [hb', access_agrees (agrees_of_decls hdc _ _)] at hex
  refine .rtRmw k _ _ _ c hex hS.rt hS.mp (.refl c) fun old _ ho => ?_
  obtain rfl := ho _ (hown s he hn hpc)
  refine ⟨fun new hnew => ?_, ?_⟩
  · simp only [Option.some.injEq] at hnew
    subst hnew
    rw [hA.regs]; exact hS.G
  · rw [setWidth_128_64]; exact land_ldStep hF he hn hdc hpc hA hD hL

/-- **A node at an own word's `swp<k> Xs, Xt, [Xn]`**: as `ownLdop_nd`, the
new value `Xs`'s. -/
theorem ownSwp_nd {n : ND} {k : RmwKind} {rs rt b : XReg} {A v : BitVec 64} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s n.pc [.instr ⟨.W64, .SWP k .W64 (.low (.reg rs) .W64) (.low (.reg rt) .W64) (.low (.reg b) .W64)⟩])
    (hown : OwnAt ms exe endPc n.pc A v)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = A ∧ StOk ms F exe endPc A (σ.regs.getRegOrZr (.low (.reg rs) .W64)) ∧
      Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill rt, ldStep rt v σ⟩ c) :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (ownSwp_ndW hF hcode hown NodeW.triv hedge).toSeg

/-- **A node at an own word's load** `ldr Xt, [Xn, #i]`: the address is the
runtime's (`LdOk`) and the thread owns it with value `v` (`hown`); `Xt`
gets `v`. Inside `W`, not moved by `K` (`hW`). -/
theorem ownLdr_ndW {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {t b : XReg} {i : Int64} {A v : BitVec 64} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [ldrDir t b i])
    (hown : OwnAt ms exe endPc n.pc A v)
    (hW : NodeW W K exe endPc R F n)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      rAddr σ.regs b i = A ∧ LdOk ms F exe endPc A ∧
      Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill t, ldStep t v σ⟩ c) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (ldrDir t b i) 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨ha, hS, hL⟩ := hedge _ σ c hA hD hJ
  have ha' : rAddr s.st.1.regs b i = A := by rw [hA.regs]; exact ha
  have hex := exec_ldr_agrees hc ha' (hS.unmapped _ hD) (agrees_of_decls hdc _ _)
  refine .rtLoad _ _ _ c hex hS.rt hS.mp (.refl c) fun w _ ho => ?_
  obtain rfl := ho _ (hown s he hn hpc)
  rw [setWidth_128_64]; exact land_ldStep hF he hn hdc hpc hA hD hL

/-- **A node at an own word's load** `ldr Xt, [Xn, #i]`: the address is the
runtime's (`LdOk`) and the thread owns it with value `v` (`hown`); `Xt`
gets `v`. -/
theorem ownLdr_nd {n : ND} {t b : XReg} {i : Int64} {A v : BitVec 64} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [ldrDir t b i])
    (hown : OwnAt ms exe endPc n.pc A v)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      rAddr σ.regs b i = A ∧ LdOk ms F exe endPc A ∧
      Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill t, ldStep t v σ⟩ c) :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (ownLdr_ndW hF hcode hown NodeW.triv hedge).toSeg

/-- **A node at an own word's release** `stlr Xt, [Xn]`: `Xn` holds the
word's address `A` and the value is one runtime memory may hold there
(`StOk`); the abstract state is unchanged. Inside `W`, not moved by `K` (`hW`). -/
theorem ownStlr_ndW {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {t b : XReg} {A : BitVec 64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s n.pc [.instr ⟨.W64, .STLR .W64 (.low (.reg t) .W64) (.low (.reg b) .W64)⟩])
    (hW : NodeW W K exe endPc R F n)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = A ∧ StOk ms F exe endPc A (σ.regs.getRegOrZr (.low (.reg t) .W64)) ∧
      Lands N E ⟨n.pc + Int64.ofNat 4, n.o, σ⟩ c) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (.instr ⟨.W64, .STLR .W64 (.low (.reg t) .W64) (.low (.reg b) .W64)⟩) 4 :=
    (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨hb, hS, hL⟩ := hedge _ σ c hA hD hJ
  have hb' : (s.st.1.regs.getXReg b).toBitVec = A := by rw [hA.regs]; exact hb
  have hex := exec_stlr_agrees hc (by rw [hb']; exact hS.unmapped _ hD) (by rw [hb']; exact agrees_of_decls hdc _ _)
  rw [hb'] at hex
  refine .rtStore _ _ _ _ c hex hS.rt hS.mp (by rw [hA.regs]; exact hS.G) (.refl c) ?_
  have hs1 : after s 4 s.st.1 = { s with st := (s.st.1, n.pc + Int64.ofNat 4) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA hD⟩
  · exact .inr ⟨y, hy.at he hn hdc hA hD⟩

/-- **A node at an own word's release** `stlr Xt, [Xn]`: `Xn` holds the
word's address `A` and the value is one runtime memory may hold there
(`StOk`); the abstract state is unchanged. -/
theorem ownStlr_nd {n : ND} {t b : XReg} {A : BitVec 64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s n.pc [.instr ⟨.W64, .STLR .W64 (.low (.reg t) .W64) (.low (.reg b) .W64)⟩])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = A ∧ StOk ms F exe endPc A (σ.regs.getRegOrZr (.low (.reg t) .W64)) ∧
      Lands N E ⟨n.pc + Int64.ofNat 4, n.o, σ⟩ c) :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (ownStlr_ndW hcode NodeW.triv hedge).toSeg

/-- **A node at an own word's plain store** `str Xt, [Xn, #i]`: the address
is the word's `A` and the value is one runtime memory may hold there
(`StOk`); the abstract state is unchanged and the source stutters. The own
map's update (the word's new value at the next pc) is the consumer's
`OwnTree` obligation, not the segment's. Inside `W`, not moved by `K` (`hW`). -/
theorem ownStr_ndW {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {t b : XReg} {i : Int64} {A : BitVec 64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [strDir t b i])
    (hW : NodeW W K exe endPc R F n)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      rAddr σ.regs b i = A ∧ StOk ms F exe endPc A (σ.regs.getRegOrZr (.low (.reg t) .W64)) ∧
      Lands N E ⟨n.pc + Int64.ofNat 4, n.o, σ⟩ c) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  rtst_ndW hcode hW fun m σ c hA hD hJ => by
    obtain ⟨ha, hS, hL⟩ := hedge m σ c hA hD hJ
    subst ha
    exact ⟨hS.rt, hS.mp, hS.G, hS.unmapped m hD, c, .refl c, hL⟩

/-- **A node at an own word's plain store** `str Xt, [Xn, #i]`: `ownStr_ndW`
inside the trivial predicate. -/
theorem ownStr_nd {n : ND} {t b : XReg} {i : Int64} {A : BitVec 64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [strDir t b i])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      rAddr σ.regs b i = A ∧ StOk ms F exe endPc A (σ.regs.getRegOrZr (.low (.reg t) .W64)) ∧
      Lands N E ⟨n.pc + Int64.ofNat 4, n.o, σ⟩ c) :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (ownStr_ndW hcode NodeW.triv hedge).toSeg

end OwnNodes

/-- `scc_rt_alloc_tcb`'s internal nodes: one per block or single
instruction of its feasible path. -/
inductive TN where
  | e | entry | j1 | len | adrp | add | arg | rmw | bnd | j2 | ok | ok1 | ok2 | hdr | ret

section Tcb

variable (lab : Label → Int64) (q : TcbG)

/-- `scc_rt_pinned`'s address. -/
abbrev pinA : BitVec 64 := (lab "scc_rt_pinned").toBitVec
/-- `scc_rt_pinned_next`'s address. -/
abbrev pnA : BitVec 64 := (lab "scc_rt_pinned_next").toBitVec

/-- **The nodes.** -/
def tcbN : TN → ND
  | .e => ⟨lab AllocTcb.fnL, AllocTcb.oE, fun σ c => c = q.c0 ∧ AllocTcb.Pre q.g q.n0 σ⟩
  | .entry => ⟨lab AllocTcb.entryL, AllocTcb.oI, fun σ c => c = q.c0 ∧ AllocTcb.Fr0 q.g σ⟩
  | .j1 => ⟨lab AllocTcb.entryL + Int64.ofNat (4 * 4), AllocTcb.oI, fun σ c => c = q.c0 ∧ AllocTcb.Fr0 q.g σ⟩
  | .len => ⟨lab AllocTcb.lenL, AllocTcb.oI, fun σ c => c = q.c0 ∧ AllocTcb.Fr0 q.g σ⟩
  | .adrp => ⟨lab AllocTcb.lenL + Int64.ofNat (4 * 32), AllocTcb.oI, fun σ c => c = q.c0 ∧ AllocTcb.Fr1 q.g σ⟩
  | .add => ⟨lab AllocTcb.lenL + Int64.ofNat (4 * 33), AllocTcb.oI, fun σ c => c = q.c0 ∧
      ∃ σ0, AllocTcb.Fr1 q.g σ0 ∧ σ = (SI.adrp .X9 "scc_rt_pinned_next").step lab σ0⟩
  | .arg => ⟨lab AllocTcb.lenL + Int64.ofNat (4 * 34), AllocTcb.oI, fun σ c => c = q.c0 ∧
      AllocTcb.Fr1 q.g σ ∧ σ.regs.X9.toBitVec = pnA lab⟩
  | .rmw => ⟨AllocTcb.rmwPc lab, AllocTcb.oI, fun σ c => c = q.c0 ∧
      AllocTcb.Fr1 q.g σ ∧ σ.regs.X9.toBitVec = AllocTcb.tcbLen ∧ σ.regs.X10.toBitVec = pnA lab⟩
  | .bnd => ⟨lab AllocTcb.lenL + Int64.ofNat (4 * 38), AllocTcb.oI, fun σ c => c = q.c0 ∧
      AllocTcb.Fr1 q.g σ ∧ σ.regs.X11.toBitVec = q.n0⟩
  | .j2 => ⟨lab AllocTcb.lenL + Int64.ofNat (4 * 47), AllocTcb.oI, fun σ c => c = q.c0 ∧ AllocTcb.Fr2 q.g q.n0 σ⟩
  | .ok => ⟨lab AllocTcb.okL, AllocTcb.oI, fun σ c => c = q.c0 ∧ AllocTcb.Fr2 q.g q.n0 σ⟩
  | .ok1 => ⟨lab AllocTcb.okL + Int64.ofNat (4 * 1), AllocTcb.oI, fun σ c => c = q.c0 ∧
      ∃ σ0, AllocTcb.Fr2 q.g q.n0 σ0 ∧ σ = (SI.adrp .X9 "scc_rt_pinned").step lab σ0⟩
  | .ok2 => ⟨lab AllocTcb.okL + Int64.ofNat (4 * 2), AllocTcb.oI, fun σ c => c = q.c0 ∧
      AllocTcb.Fr2 q.g q.n0 σ ∧ σ.regs.X9.toBitVec = pinA lab⟩
  | .hdr => ⟨AllocTcb.hdrPc lab, AllocTcb.oI, fun σ c => c = q.c0 ∧ AllocTcb.Fr3 q.g q.n0 (pinA lab) σ ∧
      σ.regs.X9.toBitVec = AllocTcb.hdr0 ||| 1#64 <<< 36 ∧ σ.regs.X10.toBitVec = pinA lab + q.n0⟩
  | .ret => ⟨lab AllocTcb.okL + Int64.ofNat (4 * 30), AllocTcb.oI, fun σ c => c = q.c0 ∧
      AllocTcb.Fr3 q.g q.n0 (pinA lab) σ⟩

/-- **The exit**: at the return address, `Post`. -/
def tcbX : Unit → ND
  | () => ⟨Int64.ofBitVec q.g.ra, AllocTcb.oE, fun σ c => c = q.c0 ∧ AllocTcb.Post q.g q.n0 (pinA lab) σ⟩

end Tcb

/-- `k + 1` instructions on, the single-instruction node lemmas' form. -/
theorem ofNat4_succ' (a : Int64) (k : Nat) : a + Int64.ofNat (4 * k) + Int64.ofNat 4 = a + Int64.ofNat (4 * (k + 1)) := by
  rw [ofNat4_succ]; rfl

/-- **The counter's add** `ldaddal` on `scc_rt_pinned_next` (`ownLdop_nd`):
the word holds `n0` at the add (`own`, a named hypothesis until `ms.own` is
wired) and runtime memory may hold `n0 + tcbLen` there (`next`). -/
structure TcbOk (ms : MemSide isaLSE2) (F : MachineData → Prop) (exe : _root_.Executable) (endPc : Int64)
    (n0 : BitVec 64) : Prop where
  next : StOk ms F exe endPc (pnA (_root_.Executable.labels exe).label) (n0 + AllocTcb.tcbLen)
  own : OwnAt ms exe endPc (AllocTcb.rmwPc (_root_.Executable.labels exe).label)
    (pnA (_root_.Executable.labels exe).label) n0

theorem TcbOk.mono {ms : MemSide isaLSE2} {F F' : MachineData → Prop} {exe : _root_.Executable} {endPc : Int64}
    {n0 : BitVec 64} (h : TcbOk ms F exe endPc n0) (hFF : ∀ m, F' m → F m) : TcbOk ms F' exe endPc n0 :=
  ⟨h.next.mono hFF, h.own⟩

/-- **`scc_rt_alloc_tcb`'s node obligations inside `W`**: the block nodes'
states (`BlkW`) and the single instructions' (`NodeW`). -/
def TcbW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (q : TcbG) : TN → Prop
  | .e => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .e) AllocTcb.atPro
  | .entry => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .entry) AllocTcb.atChk
  | .j1 => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .j1) AllocTcb.atJ1
  | .len => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .len) AllocTcb.atLen
  | .adrp => NodeW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .adrp)
  | .add => NodeW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .add)
  | .arg => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .arg) AllocTcb.atArg
  | .rmw => NodeW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .rmw)
  | .bnd => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .bnd) AllocTcb.atBnd
  | .j2 => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .j2) AllocTcb.atJ2
  | .ok => NodeW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .ok)
  | .ok1 => NodeW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .ok1)
  | .ok2 => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .ok2) AllocTcb.atOk
  | .hdr => NodeW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .hdr)
  | .ret => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .ret) AllocTcb.atRet

section TcbProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F F0 : MachineData → Prop}

set_option hygiene false in
/-- A block node of `scc_rt_alloc_tcb`: the block, its `okBlk`, its code; the edge is left. -/
local macro "tnode " b:ident ok:ident l:term:max k:term:max : tactic =>
  `(tactic| refine seg_nd (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (code_of hp hend (by simp only [AllocTcb.allocTcbIn, Bool.and_eq_true] at hin; simp only [hin])
      (l := $l) (k := $k) (by first | rfl | exact ofNat4_zero _)) fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- **`scc_rt_alloc_tcb` is one segment** in any valid layout of `ret0Prog`,
from its entry to its return, for any region holding its frame of 192 and
any frame condition implying `F0`, given: room for the TCB below `2^17`
(`hn`), the header word's facts (`hhdr`), and the counter's add's
(`htcb`). -/
theorem alloc_tcb_seg (hp : Lays exe SccCode.ret0Prog) (hend : endPc = endOf exe SccCode.ret0Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TcbG) (hn : q.n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F0 exe endPc (pinA (_root_.Executable.labels exe).label + q.n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F0 exe endPc q.n0) :
    Seg p lbl ms (At exe endPc R F (tcbN (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x, At exe endPc R F (tcbX (_root_.Executable.labels exe).label q x) s c) := by
  have hin := AllocTcb.ret0_allocTcbIn
  have hin' := hin
  simp only [AllocTcb.allocTcbIn, Bool.and_eq_true] at hin'
  have eEntry := label_labelGap hp hin'.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
  refine fn_seg (N := tcbN _ q) (E := tcbX _ q) (fun i => ?_) TN.e
  cases i
  case e =>
    tnode AllocTcb.atPro AllocTcb.atPro_ok AllocTcb.fnL 0
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atPro_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.entry, by rw [h1, ← eEntry]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    tnode AllocTcb.atChk AllocTcb.atChk_ok AllocTcb.entryL 0
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atChk_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.j1, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case j1 =>
    tnode AllocTcb.atJ1 AllocTcb.atJ1_ok AllocTcb.entryL 4
    dsimp only [tcbN, tcbX] at hJ ⊢
    rw [AllocTcb.atJ1_run]
    exact .inl ⟨TN.len, rfl, rfl, hJ⟩
  case len =>
    tnode AllocTcb.atLen AllocTcb.atLen_ok AllocTcb.lenL 0
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atLen_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.adrp, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case adrp =>
    refine si_nd (si := .adrp .X9 "scc_rt_pinned_next") hF
      (code_of hp hend hin'.1.1.1.1.1.1.1.1.1.1.2 rfl) fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.add, ?_, rfl,
        hJ.1, σ, hJ.2, rfl⟩⟩
    exact (ofNat4_succ' _ 32).symm
  case add =>
    refine si_nd (si := .addLo12 .X9 .X9 "scc_rt_pinned_next") hF
      (code_of hp hend hin'.1.1.1.1.1.1.1.1.1.2 rfl) fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.arg, ?_, rfl, ?_⟩⟩
    · exact (ofNat4_succ' _ 33).symm
    · obtain ⟨rfl, σ0, h0, rfl⟩ := hJ
      exact ⟨rfl, AllocTcb.labStep_fr1 _ _ h0, (AllocTcb.labStep_spec _ _ σ0).1⟩
  case arg =>
    tnode AllocTcb.atArg AllocTcb.atArg_ok AllocTcb.lenL 34
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atArg_walk (_root_.Executable.labels exe).label _ hJ h9
    exact .inl ⟨TN.rmw, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case rmw =>
    refine ownLdop_nd hF (code_of hp hend hin'.1.1.1.1.1.1.1.2 rfl) htcb.own fun _ σ c _ _ hJ => ?_
    dsimp only [tcbN] at hJ ⊢
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    refine ⟨h10, ?_, .inl ⟨TN.bnd, (ofNat4_succ' _ 37).symm, rfl, rfl, ?_, ?_⟩⟩
    · rw [add_apply, getRegOrZr_x9, h9]; exact htcb.next.mono hFF
    · simpa [ldStep, AllocTcb.Fr1, AllocTcb.Fr0] using hJ
    · simp [ldStep]
  case bnd =>
    tnode AllocTcb.atBnd AllocTcb.atBnd_ok AllocTcb.lenL 38
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, h11⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atBnd_walk (_root_.Executable.labels exe).label _ hJ h11 hn
    exact .inl ⟨TN.j2, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case j2 =>
    tnode AllocTcb.atJ2 AllocTcb.atJ2_ok AllocTcb.lenL 47
    dsimp only [tcbN, tcbX] at hJ ⊢
    rw [AllocTcb.atJ2_run]
    exact .inl ⟨TN.ok, rfl, rfl, hJ⟩
  case ok =>
    refine si_nd (si := .adrp .X9 "scc_rt_pinned") hF
      (code_of hp hend hin'.1.1.1.1.2 (ofNat4_zero _)) fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.ok1, ?_, rfl,
        hJ.1, σ, hJ.2, rfl⟩⟩
    rfl
  case ok1 =>
    refine si_nd (si := .addLo12 .X9 .X9 "scc_rt_pinned") hF
      (code_of hp hend hin'.1.1.1.2 rfl) fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.ok2, ?_, rfl, ?_⟩⟩
    · exact (ofNat4_succ' _ 1).symm
    · obtain ⟨rfl, σ0, h0, rfl⟩ := hJ
      exact ⟨rfl, AllocTcb.labStep_fr2 _ _ h0, (AllocTcb.labStep_spec _ _ σ0).1⟩
  case ok2 =>
    tnode AllocTcb.atOk AllocTcb.atOk_ok AllocTcb.okL 2
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atOk_walk (_root_.Executable.labels exe).label _ hJ h9
    exact .inl ⟨TN.hdr, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case hdr =>
    refine rtst_nd (code_of hp hend hin'.1.2 rfl) fun m σ c _ hD hJ => ?_
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    have ha : rAddr σ.regs .X10 0 = pinA (_root_.Executable.labels exe).label + q.n0 := by
      rw [← h10]; simp [rAddr, Reg64s.getXReg]
    rw [ha, Spike.Lib.A64.Alloc.getRegOrZr_x]
    refine ⟨hhdr.rt, hhdr.mp, ?_, hhdr.unmapped m (hFF m hD), q.c0, .refl q.c0,
      .inl ⟨TN.ret, (ofNat4_succ' _ 29).symm, rfl, rfl, hJ⟩⟩
    have : (σ.regs.getXReg .X9).toBitVec = AllocTcb.hdr0 ||| 1#64 <<< 36 := by
      rw [← h9]; simp [Reg64s.getXReg]
    rw [this]; exact hhdr.G
  case ret =>
    tnode AllocTcb.atRet AllocTcb.atRet_ok AllocTcb.okL 30
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atRet_walk (_root_.Executable.labels exe).label _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, h3⟩


set_option hygiene false in
/-- A block node of `scc_rt_alloc_tcb` inside `W`: the block, its `okBlk`, its code, its
obligation; the edge is left. -/
local macro "tnodeW " b:ident ok:ident l:term:max k:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (code_of hp hend (by simp only [AllocTcb.allocTcbIn, Bool.and_eq_true] at hin; simp only [hin])
      (l := $l) (k := $k) (by first | rfl | exact ofNat4_zero _)) $w fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- **`scc_rt_alloc_tcb` is one segment inside `W`** (`alloc_tcb_seg`, its
states' obligations `hW`): in any valid layout of `ret0Prog`,
from its entry to its return, for any region holding its frame of 192 and
any frame condition implying `F0`, given: room for the TCB below `2^17`
(`hn`), the header word's facts (`hhdr`), and the counter's add's
(`htcb`). -/
theorem alloc_tcb_segW {W : Frag isaLSE2} {K : State → State → Prop} (hp : Lays exe SccCode.ret0Prog)
    (hend : endPc = endOf exe SccCode.ret0Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TcbG) (hn : q.n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F0 exe endPc (pinA (_root_.Executable.labels exe).label + q.n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F0 exe endPc q.n0) (hW : ∀ i, TcbW W K exe endPc R F q i) :
    SegW W K p lbl ms (At exe endPc R F (tcbN (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x, At exe endPc R F (tcbX (_root_.Executable.labels exe).label q x) s c) := by
  have hin := AllocTcb.ret0_allocTcbIn
  have hin' := hin
  simp only [AllocTcb.allocTcbIn, Bool.and_eq_true] at hin'
  have eEntry := label_labelGap hp hin'.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
  refine fn_segW (N := tcbN _ q) (E := tcbX _ q) (fun i => ?_) TN.e
  cases i
  case e =>
    tnodeW AllocTcb.atPro AllocTcb.atPro_ok AllocTcb.fnL 0 (hW TN.e)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atPro_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.entry, by rw [h1, ← eEntry]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    tnodeW AllocTcb.atChk AllocTcb.atChk_ok AllocTcb.entryL 0 (hW TN.entry)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atChk_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.j1, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case j1 =>
    tnodeW AllocTcb.atJ1 AllocTcb.atJ1_ok AllocTcb.entryL 4 (hW TN.j1)
    dsimp only [tcbN, tcbX] at hJ ⊢
    rw [AllocTcb.atJ1_run]
    exact .inl ⟨TN.len, rfl, rfl, hJ⟩
  case len =>
    tnodeW AllocTcb.atLen AllocTcb.atLen_ok AllocTcb.lenL 0 (hW TN.len)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atLen_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.adrp, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case adrp =>
    refine si_ndW (si := .adrp .X9 "scc_rt_pinned_next") hF
      (code_of hp hend hin'.1.1.1.1.1.1.1.1.1.1.2 rfl) (hW TN.adrp) fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.add, ?_, rfl,
        hJ.1, σ, hJ.2, rfl⟩⟩
    exact (ofNat4_succ' _ 32).symm
  case add =>
    refine si_ndW (si := .addLo12 .X9 .X9 "scc_rt_pinned_next") hF
      (code_of hp hend hin'.1.1.1.1.1.1.1.1.1.2 rfl) (hW TN.add) fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.arg, ?_, rfl, ?_⟩⟩
    · exact (ofNat4_succ' _ 33).symm
    · obtain ⟨rfl, σ0, h0, rfl⟩ := hJ
      exact ⟨rfl, AllocTcb.labStep_fr1 _ _ h0, (AllocTcb.labStep_spec _ _ σ0).1⟩
  case arg =>
    tnodeW AllocTcb.atArg AllocTcb.atArg_ok AllocTcb.lenL 34 (hW TN.arg)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atArg_walk (_root_.Executable.labels exe).label _ hJ h9
    exact .inl ⟨TN.rmw, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case rmw =>
    refine ownLdop_ndW hF (code_of hp hend hin'.1.1.1.1.1.1.1.2 rfl) htcb.own (hW TN.rmw) fun _ σ c _ _ hJ => ?_
    dsimp only [tcbN] at hJ ⊢
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    refine ⟨h10, ?_, .inl ⟨TN.bnd, (ofNat4_succ' _ 37).symm, rfl, rfl, ?_, ?_⟩⟩
    · rw [add_apply, getRegOrZr_x9, h9]; exact htcb.next.mono hFF
    · simpa [ldStep, AllocTcb.Fr1, AllocTcb.Fr0] using hJ
    · simp [ldStep]
  case bnd =>
    tnodeW AllocTcb.atBnd AllocTcb.atBnd_ok AllocTcb.lenL 38 (hW TN.bnd)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, h11⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atBnd_walk (_root_.Executable.labels exe).label _ hJ h11 hn
    exact .inl ⟨TN.j2, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case j2 =>
    tnodeW AllocTcb.atJ2 AllocTcb.atJ2_ok AllocTcb.lenL 47 (hW TN.j2)
    dsimp only [tcbN, tcbX] at hJ ⊢
    rw [AllocTcb.atJ2_run]
    exact .inl ⟨TN.ok, rfl, rfl, hJ⟩
  case ok =>
    refine si_ndW (si := .adrp .X9 "scc_rt_pinned") hF
      (code_of hp hend hin'.1.1.1.1.2 (ofNat4_zero _)) (hW TN.ok) fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.ok1, ?_, rfl,
        hJ.1, σ, hJ.2, rfl⟩⟩
    rfl
  case ok1 =>
    refine si_ndW (si := .addLo12 .X9 .X9 "scc_rt_pinned") hF
      (code_of hp hend hin'.1.1.1.2 rfl) (hW TN.ok1) fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.ok2, ?_, rfl, ?_⟩⟩
    · exact (ofNat4_succ' _ 1).symm
    · obtain ⟨rfl, σ0, h0, rfl⟩ := hJ
      exact ⟨rfl, AllocTcb.labStep_fr2 _ _ h0, (AllocTcb.labStep_spec _ _ σ0).1⟩
  case ok2 =>
    tnodeW AllocTcb.atOk AllocTcb.atOk_ok AllocTcb.okL 2 (hW TN.ok2)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atOk_walk (_root_.Executable.labels exe).label _ hJ h9
    exact .inl ⟨TN.hdr, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case hdr =>
    refine rtst_ndW (code_of hp hend hin'.1.2 rfl) (hW TN.hdr) fun m σ c _ hD hJ => ?_
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    have ha : rAddr σ.regs .X10 0 = pinA (_root_.Executable.labels exe).label + q.n0 := by
      rw [← h10]; simp [rAddr, Reg64s.getXReg]
    rw [ha, Spike.Lib.A64.Alloc.getRegOrZr_x]
    refine ⟨hhdr.rt, hhdr.mp, ?_, hhdr.unmapped m (hFF m hD), q.c0, .refl q.c0,
      .inl ⟨TN.ret, (ofNat4_succ' _ 29).symm, rfl, rfl, hJ⟩⟩
    have : (σ.regs.getXReg .X9).toBitVec = AllocTcb.hdr0 ||| 1#64 <<< 36 := by
      rw [← h9]; simp [Reg64s.getXReg]
    rw [this]; exact hhdr.G
  case ret =>
    tnodeW AllocTcb.atRet AllocTcb.atRet_ok AllocTcb.okL 30 (hW TN.ret)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atRet_walk (_root_.Executable.labels exe).label _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, h3⟩

end TcbProof

/-! ## `scc_rt_start` up to `.sp2` -/

/-- `scc_rt_start`'s call of `scc_rt_alloc_tcb` with the header and `k = 1`. -/
def startCall : List Directive := parseAArch64("str x0, [sp, #8]
movz x0, #2307
movz x1, #1
bl scc_rt_alloc_tcb")

block_spec startCall (-48) 0 Abort.oI startCall

/-- **The call's code in `prog`**: the block after the system call, `.sp2`
right after it. -/
def startCallIn (prog : List Directive) : Bool :=
  blockAt prog startE 9 startCall && labelGap prog startE ".L0_scc_rt_start.sp2" 13

theorem ret0_startCallIn : startCallIn SccCode.ret0Prog = true := by decide +kernel

section Start

variable (lab : Label → Int64)

/-- `scc_rt_start`'s entry, the source control `c0`. -/
def startN0 (c0 : Ctl) : ND := ⟨lab "scc_rt_start", Abort.oE, fun _ c => c = c0⟩

/-- After `rt_sigaction`, at the call's block. -/
def startN1 (c0 : Ctl) : ND := ⟨lab startE + Int64.ofNat (4 * 9), Abort.oI, fun _ c => c = c0⟩

/-- **The call node**: at `scc_rt_alloc_tcb`'s label, its arguments and the
return address `.sp2`. -/
def startNC (c0 : Ctl) : ND := ⟨lab AllocTcb.fnL, Abort.oI, fun σ c => c = c0 ∧
  σ.regs.X0.toBitVec = AllocTcb.hdr0 ∧ σ.regs.X1.toBitVec = 1#64 ∧
  σ.regs.X30.toBitVec = (lab ".L0_scc_rt_start.sp2").toBitVec⟩

/-- **Back at `.sp2`**: `x0` the TCB, one word past its header at
`scc_rt_pinned + n0`. -/
def startN2 (n0 : BitVec 64) (c0 : Ctl) : ND := ⟨lab ".L0_scc_rt_start.sp2", Abort.oI, fun σ c => c = c0 ∧
  σ.regs.X0.toBitVec = pinA lab + n0 + 8#64⟩

end Start

section StartProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`scc_rt_start` from its entry to `.sp2`** in any valid layout of
`ret0Prog`: S1, the call's block, and `scc_rt_alloc_tcb` through
`call_nd_F`, with `scc_rt_pinned_next` holding `n0` (room below `2^17`,
`hn`), the header word's facts (`hhdr`) and the counter's add's
(`htcb`). -/
theorem start_sp2_seg (hp : Lays exe SccCode.ret0Prog) (hend : endPc = endOf exe SccCode.ret0Prog)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -240) (hhi : 0 ≤ R.hi) (n0 : BitVec 64) (c0 : Ctl) (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F exe endPc (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F exe endPc n0) :
    Seg p lbl ms (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0))
      (At exe endPc R F (startN2 (_root_.Executable.labels exe).label n0 c0)) := by
  let lab := (_root_.Executable.labels exe).label
  have hin := ret0_startCallIn
  simp only [startCallIn, Bool.and_eq_true] at hin
  have esp2 := label_labelGap hp hin.2
  have hlo48 : R.lo ≤ -48 := by omega
  refine Seg.seq (ret0_start_seg hp hend hK hF hR hal hlo48 hhi (nC := startN1 lab c0) rfl rfl fun _ _ h => h)
    (Seg.seq (Q := At exe endPc R F (startNC lab c0)) ?_ ?_)
  · -- the call's block
    refine seg_one (seg_nd (by simp [startCall]) startCall_ok hF hR hal hlo48 hhi
      (code_of hp hend hin.1 rfl) fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
    · dsimp only [startN1, startNC]; rw [startCall_run]
    · dsimp only [startN1, startNC]; rw [startCall_run]; rfl
    · dsimp only [startN1, startNC] at hJ ⊢; rw [startCall_run]
      refine ⟨hJ, rfl, rfl, ?_⟩
      simp only [ofInt_bmod]
      rw [show lab ".L0_scc_rt_start.sp2" = _ from esp2,
        show Int64.ofNat (4 * 13) = Int64.ofNat (4 * 9) + 16 from rfl, ← Int64.add_assoc, Int64.toBitVec_add,
        show ∀ y : Int, y + 4 + 4 + 4 + 4 = y + 16 from fun y => by omega, BitVec.ofInt_add,
        Spike.Lib.int64_ofInt_toInt]; rfl
  · -- `scc_rt_alloc_tcb`
    refine seg_one (call_nd_F (lo' := -192) (hi' := 0) (Ne := fun g => tcbN lab ⟨g, n0, c0⟩ .e)
      (Ex := fun g => tcbX lab ⟨g, n0, c0⟩)
      hR hal hF (by show R.lo ≤ -48 + -192; omega) (by decide) (by show (-48 : Int) < R.hi; omega) (by decide)
      (by show (-48 : Int) % 16 = 0; decide) (by decide) (by decide)
      (fun R' F' hR' hal' hlo' hhi' hF' hFF g' =>
        alloc_tcb_seg hp hend hF' hR' hal' hlo' hhi' hFF ⟨g', n0, c0⟩ hn hhdr htcb)
      (fun _ => rfl) ?_ ?_)
    · rintro σC c ⟨rfl, h0, h1, -⟩
      exact ⟨⟨σC.regs.SP.toBitVec, σC.regs.X29.toBitVec, σC.regs.X30.toBitVec⟩, rfl,
        rfl, rfl, rfl, rfl, h0, h1⟩
    · rintro g x σC c σx c' σR ⟨-, -, -, h30⟩ ⟨-, -, -, h30', -⟩ ⟨rfl, hPost⟩ hregs - -
      refine .inl ⟨(), ?_, rfl, rfl, ?_⟩
      · show lab ".L0_scc_rt_start.sp2" = Int64.ofBitVec g.ra
        rw [← h30']
        show lab _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [h30, int64_ofBitVec_toBitVec]
      · show σR.regs.X0.toBitVec = _
        rw [hregs]; exact hPost.2.2.2

end StartProof

/-! ## Label addresses -/

section LabPair

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- The node between a label pair's two instructions: `x9` the page of `L`,
after `adrp` from a state of `P`. -/
def labMid (lab : Label → Int64) (l L : Label) (k : Nat) (sp : Int) (P : AS → Ctl → Prop) : ND :=
  ⟨lab l + Int64.ofNat (4 * k) + Int64.ofNat 4, (SI.adrp .X9 L).so ⟨sp, []⟩,
    fun σ c => ∃ σ0, P σ0 c ∧ σ = (SI.adrp .X9 L).step lab σ0⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- A segment to the single node of `Next`, inside `W`. -/
theorem seg_oneW {W : Frag isaLSE2} {K : State → State → Prop} {P : Frag isaLSE2} {n : ND}
    (h : SegW W K p lbl ms P (Next exe endPc R F (fun _ : Unit => n) (fun e : Empty => e.elim))) :
    SegW W K p lbl ms P (At exe endPc R F n) :=
  h.mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim

/-- **A label's address** `adrp x9, L; add x9, x9, :lo12:L` at `l`, `k`
(`StackTake.labIn`), inside `W`: from a node there to node `n'` two
instructions on, with `sp` at offset `sp` and no register offsets; both
instructions' states in `W` and not moved by `K` (`hW0`, `hW1`). -/
theorem labPair_segW {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp)
    {l L : Label} {k : Nat} (hin : StackTake.labIn prog l k L = true) (hF : FStable R F) {sp : Int}
    {P : AS → Ctl → Prop} {n' : ND}
    (hpc : n'.pc = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * (k + 1 + 1)))
    (ho : n'.o = ⟨sp, []⟩)
    (hW0 : NodeW W K exe endPc R F ⟨(_root_.Executable.labels exe).label l + Int64.ofNat (4 * k), ⟨sp, []⟩, P⟩)
    (hW1 : NodeW W K exe endPc R F (labMid (_root_.Executable.labels exe).label l L k sp P))
    (h : ∀ σ c, P σ c → n'.J (AllocTcb.labStep (_root_.Executable.labels exe).label L σ) c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label l + Int64.ofNat (4 * k), ⟨sp, []⟩, P⟩)
      (At exe endPc R F n') := by
  let lab := (_root_.Executable.labels exe).label
  simp only [StackTake.labIn, Bool.and_eq_true] at hin
  refine SegW.seq (Q := At exe endPc R F (labMid lab l L k sp P))
    (seg_oneW (si_ndW (si := .adrp .X9 L) hF (code_of hp hend hin.1 rfl) hW0 fun σ c hJ =>
      ⟨c, .refl c, .inl ⟨(), rfl, by simp [labMid, SO.le, SI.so, SI.dst, SO.kill, rm], σ, hJ, rfl⟩⟩))
    (seg_oneW (si_ndW (si := .addLo12 .X9 .X9 L) hF (code_of hp hend hin.2 (ofNat4_succ' _ k).symm) hW1
      fun σ c ⟨σ0, hP, hσ⟩ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩))
  · rw [hpc, ← ofNat4_succ', ← ofNat4_succ']; rfl
  · rw [ho]; simp [labMid, SO.le, SI.so, SI.dst, SO.kill, rm]
  · subst hσ; exact h σ0 c hP

/-- **A label's address** `adrp x9, L; add x9, x9, :lo12:L` at `l`, `k`
(`StackTake.labIn`): from a node there to node `n'` two instructions on,
with `sp` at offset `sp` and no register offsets. -/
theorem labPair_seg {prog : List Directive} {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    {l L : Label} {k : Nat} (hin : StackTake.labIn prog l k L = true) (hF : FStable R F) {sp : Int}
    {P : AS → Ctl → Prop} {n' : ND}
    (hpc : n'.pc = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * (k + 1 + 1)))
    (ho : n'.o = ⟨sp, []⟩)
    (h : ∀ σ c, P σ c → n'.J (AllocTcb.labStep (_root_.Executable.labels exe).label L σ) c) :
    Seg p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label l + Int64.ofNat (4 * k), ⟨sp, []⟩, P⟩)
      (At exe endPc R F n') :=
  (labPair_segW hp hend hin hF hpc ho NodeW.triv NodeW.triv h).toSeg

end LabPair

/-! ## The take

At the take site the kernel takes the thread's step: the stack range `rS`
named by `x0`/`x1` moves into the thread's private memory with whatever
bytes the pool holds there, and the thread moves past the site's `nop`
(`Kernel.step_at_take`). In a segment this is an outside move (`SegW`'s
`K`): `TakeK a rS`, at the site's pc `a`. A pair at the site is moved by it
for every pool, so no `Out` row is asked there; every other pair is not. -/

section TakeNode

/-- **The take of the range `rS` at the pc `a`**: the pool's bytes `pm`
copied onto `rS` in private memory, the pc past the `nop`
(`Scc.Sem.A64.abi`'s `skip` and `setDmem`). -/
def TakeK (a : Int64) (rS : Scc.Sem.Range) (s s' : State) : Prop :=
  s.st.2 = a ∧ ∃ pm : _root_.Mem 64,
    s' = Scc.Sem.A64.abi.skip (Scc.Sem.A64.abi.setDmem s (Scc.Sem.Kernel.copyRange pm (Scc.Sem.A64.abi.dmem s) rS))

/-- The machine data after a take of `rS` from the pool `pm`. -/
def takeMem (pm : _root_.Mem 64) (rS : Scc.Sem.Range) (m : MachineData) : MachineData :=
  { m with dmem := Scc.Sem.Kernel.copyRange pm m.dmem rS }

/-- Only a state at `a` is moved. -/
theorem TakeK.pc {a : Int64} {rS : Scc.Sem.Range} {s s' : State} (h : TakeK a rS s s') : s.st.2 = a := h.1

/-- No move off the site. -/
theorem TakeK.not_of_pc {a : Int64} {rS : Scc.Sem.Range} {s : State} (h : s.st.2 ≠ a) : ∀ s', ¬ TakeK a rS s s' :=
  fun _ hk => h hk.1

/-- The state after a take, at a `nop` cell: the memory `takeMem`, the pc
past the cell. -/
theorem TakeK.eq {a : Int64} {rS : Scc.Sem.Range} {s s' : State} (h : TakeK a rS s s')
    (hc : CellAt s (.instr ⟨.W64, .NOP⟩) 4) :
    ∃ pm, s' = { s with st := (takeMem pm rS s.st.1, s.st.2 + Int64.ofNat 4) } := by
  obtain ⟨-, pm, rfl⟩ := h
  refine ⟨pm, ?_⟩
  have := Scc.Sem.A64.nextPc_of_cellAt hc
  show { s with st := (takeMem pm rS s.st.1, Scc.Sem.A64.nextPc { s with st := (takeMem pm rS s.st.1, s.st.2) }) } = _
  rw [show Scc.Sem.A64.nextPc { s with st := (takeMem pm rS s.st.1, s.st.2) } = Scc.Sem.A64.nextPc s from rfl, this]

/-- A word off `rS` reads the same after the take. -/
theorem loadInt_takeMem {pm : _root_.Mem 64} {rS : Scc.Sem.Range} {m : MachineData} {a : BitVec 64}
    (h : ∀ i < 8, a + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS) :
    Mem.loadInt (takeMem pm rS m).dmem a 8 = Mem.loadInt m.dmem a 8 := by
  unfold Mem.loadInt
  congr 1
  refine Mem.loadBytes_congr fun i hi => ?_
  show (Scc.Sem.Kernel.copyRange pm m.dmem rS)[a + BitVec.ofNat 64 i]? = m.dmem[a + BitVec.ofNat 64 i]?
  unfold Scc.Sem.Kernel.copyRange
  rw [Scc.Sem.Kernel.get_foldl_insert]; simp only [h i hi, ↓reduceIte]

/-- **The stack range is in private memory**: every aligned word of `rS`
reads (`Owned`'s second half, of the machine data). -/
def StackM (rS : Scc.Sem.Range) (m : MachineData) : Prop :=
  ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) → (Mem.loadInt m.dmem (BitVec.ofNat 64 a) 8).isSome

/-- **After the take the range is in private memory**, for any pool. -/
theorem stackM_takeMem {pm : _root_.Mem 64} {rS : Scc.Sem.Range} {m : MachineData} :
    StackM rS (takeMem pm rS m) := by
  intro a _ ha ha7
  unfold Mem.loadInt
  rw [Option.isSome_map]
  unfold Mem.loadBytes
  rw [List.allSome_isSome_iff]
  intro o ho
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ho
  have hi8 := List.mem_range.mp hi
  show ((Scc.Sem.Kernel.copyRange pm m.dmem rS)[BitVec.ofNat 64 a + BitVec.ofNat 64 i]?).isSome
  unfold Scc.Sem.Kernel.copyRange
  rw [Scc.Sem.Kernel.get_foldl_insert, ite_eq_left_of_eq_true _ _ (eq_true ?_)]
  · rfl
  · unfold Scc.Sem.Kernel.addrs
    refine List.mem_map.mpr ⟨a + i - rS.lo, List.mem_range.mpr ?_, ?_⟩
    · simp only [Scc.Sem.Range.contains] at ha ha7; omega
    · simp only [Scc.Sem.Range.contains] at ha ha7
      rw [← BitVec.ofNat_add, show rS.lo + (a + i - rS.lo) = a + i by omega]

/-- **No write inside a region off `rS` breaks `StackM`**: every aligned
word of `rS` lies outside the region `R`. -/
theorem stackM_stable {rS : Scc.Sem.Range} {R : Region} (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a) :
    FStable R (StackM rS) := by
  intro m m' hm hd a h8 ha ha7
  have hlt : a < 2 ^ 64 := by simp only [Scc.Sem.Range.contains] at ha7; omega
  have hn : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [hd (BitVec.ofNat 64 a) (by rw [hn]; simp only [Scc.Sem.Range.contains] at ha7; omega)
    (by rw [hn]; exact hout a h8 ha ha7)]
  exact hm a h8 ha ha7

/-- The machine data after a take is that of `takeMem`. -/
theorem TakeK.mem {a : Int64} {rS : Scc.Sem.Range} {s s' : State} (h : TakeK a rS s s') :
    ∃ pm, s'.st.1 = takeMem pm rS s.st.1 := by
  obtain ⟨-, pm, rfl⟩ := h
  exact ⟨pm, rfl⟩

/-- **A frame condition every `takeMem` keeps no take breaks.** -/
theorem TakeK.kstable {a : Int64} {rS : Scc.Sem.Range} {F : MachineData → Prop}
    (h : ∀ m pm, F m → F (takeMem pm rS m)) : KStable (TakeK a rS) F := fun _ _ hk hm => by
  obtain ⟨pm, he⟩ := hk.mem
  rw [he]; exact h _ pm hm

/-- **A frame condition no take breaks is kept by every `takeMem`** (the
take of a state at the site with that memory). -/
theorem takeMem_of_kstable {a : Int64} {rS : Scc.Sem.Range} {F : MachineData → Prop}
    (h : KStable (TakeK a rS) F) (exe : _root_.Executable) (endPc : Int64) :
    ∀ m pm, F m → F (takeMem pm rS m) :=
  fun m pm hm => h { exe := exe, endPc := endPc, st := (m, a) } _ ⟨rfl, pm, rfl⟩ hm

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64}

/-- **The take node**: at the site's `nop` (pc `a`), from every pair of the
node, every take lands at node `n'` past the `nop`, with the region related
to the same abstract state (`hA`: the take keeps the region's cells and
gives the new frame condition `F'`) and a local run of the source to `n'`'s
invariant (`hedge`). No pair of the node is left unmoved, so no `Out` row is
asked. -/
theorem take_ndW {W : Frag isaLSE2} {a : Int64} {rS : Scc.Sem.Range} {R R' : Region} {F F' : MachineData → Prop}
    {n n' : ND} (hpc : n.pc = a)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [.instr ⟨.W64, .NOP⟩])
    (hW : ∀ s c, At exe endPc R F n s c → W s c)
    (hA : ∀ m σ pm, Abs R n.o m σ → F m → Abs R' n'.o (takeMem pm rS m) σ ∧ F' (takeMem pm rS m))
    (hedge : ∀ σ c, n.J σ c → n'.pc = n.pc + Int64.ofNat 4 ∧ ∃ c', LocalRun p c c' ∧ n'.J σ c') :
    SegW W (TakeK a rS) p lbl ms (At exe endPc R F n) (At exe endPc R' F' n') := by
  refine SegW.stepK hW fun s c ⟨he, hn, hdc, hpc', σ, hAb, hD, hJ⟩ => ⟨fun hk => ?_, fun s' hk => ?_⟩
  · exact (hk _ ⟨hpc'.trans hpc, ∅, rfl⟩).elim
  · have hc : CellAt s (.instr ⟨.W64, .NOP⟩) 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc']; simp)
    obtain ⟨pm, rfl⟩ := hk.eq hc
    obtain ⟨hpc'', c', hr, hJ'⟩ := hedge σ c hJ
    obtain ⟨hA', hF'⟩ := hA _ σ pm hAb hD
    exact ⟨c', hr, he, hn, hdc, by rw [hpc', hpc''], σ, hA', hF', hJ'⟩

end TakeNode

/-! ## `scc_rt_stack_take` -/

/-- **The ghosts of a call of `scc_rt_stack_take`**: `sp`, `x29`, `x30` at
entry, the own word `scc_rt_stack_next`'s value `k0` on entry, the source
control. -/
structure TakeG where
  g : StackTake.G
  k0 : BitVec 64
  c0 : Ctl

/-- `scc_rt_stack_take`'s internal nodes on its feasible path. -/
inductive TK where
  | e | entry | cls | j1 | d0 | d2 | d7 | d9 | d14 | d16 | sp0 | swp | sp3 | lk0 | ldn | lk2
  | b0 | b2 | unl | b6 | b8 | nxt | b12 | b21 | ok0 | ok2 | tk | site | ret

section Take

variable (lab : Label → Int64) (q : TakeG)

/-- `scc_rt_stack_lock`'s address. -/
abbrev lockA : BitVec 64 := (lab "scc_rt_stack_lock").toBitVec
/-- `scc_rt_stack_free_n`'s address (the first class's count). -/
abbrev freeNA : BitVec 64 := (lab "scc_rt_stack_free_n").toBitVec
/-- `scc_rt_stack_next`'s address. -/
abbrev nextA : BitVec 64 := (lab "scc_rt_stack_next").toBitVec
/-- `scc_rt_stacks`' address. -/
abbrev stacksA : BitVec 64 := (lab "scc_rt_stacks").toBitVec

open StackTake in
/-- **The nodes.** -/
def takeN : TK → ND
  | .e => ⟨lab fnL, oE, fun σ c => c = q.c0 ∧ Pre q.g q.k0 σ⟩
  | .entry => ⟨lab entryL, oI, fun σ c => c = q.c0 ∧ Fr0 q.g σ⟩
  | .cls => ⟨lab clsL, oI, fun σ c => c = q.c0 ∧ Fr1 q.g σ⟩
  | .j1 => ⟨lab clsL + Int64.ofNat (4 * 4), oI, fun σ c => c = q.c0 ∧ Fr1 q.g σ⟩
  | .d0 => ⟨lab doneL + Int64.ofNat (4 * 0), oI, fun σ c => c = q.c0 ∧ Fr1 q.g σ⟩
  | .d2 => ⟨lab doneL + Int64.ofNat (4 * 2), oI, fun σ c => c = q.c0 ∧ Fr1 q.g σ ∧
      σ.regs.X9.toBitVec = freeNA lab⟩
  | .d7 => ⟨lab doneL + Int64.ofNat (4 * 7), oI, fun σ c => c = q.c0 ∧ Fr2 q.g (freeNA lab) σ⟩
  | .d9 => ⟨lab doneL + Int64.ofNat (4 * 9), oI, fun σ c => c = q.c0 ∧ Fr2 q.g (freeNA lab) σ⟩
  | .d14 => ⟨lab doneL + Int64.ofNat (4 * 14), oI, fun σ c => c = q.c0 ∧ Fr2 q.g (freeNA lab) σ⟩
  | .d16 => ⟨lab doneL + Int64.ofNat (4 * 16), oI, fun σ c => c = q.c0 ∧ Fr2 q.g (freeNA lab) σ ∧
      σ.regs.X9.toBitVec = lockA lab⟩
  | .sp0 => ⟨lab spinL, oI, fun σ c => c = q.c0 ∧ Fr3 q.g (freeNA lab) (lockA lab) σ⟩
  | .swp => ⟨swpPc lab, oI, fun σ c => c = q.c0 ∧ Fr3 q.g (freeNA lab) (lockA lab) σ ∧
      σ.regs.X9.toBitVec = 1#64 ∧ σ.regs.X10.toBitVec = lockA lab⟩
  | .sp3 => ⟨lab spinL + Int64.ofNat (4 * 3), oI, fun σ c => c = q.c0 ∧ Fr3 q.g (freeNA lab) (lockA lab) σ ∧
      σ.regs.X11.toBitVec = 0#64⟩
  | .lk0 => ⟨lab lockedL, oI, fun σ c => c = q.c0 ∧ Fr3 q.g (freeNA lab) (lockA lab) σ⟩
  | .ldn => ⟨freeNPc lab, oI, fun σ c => c = q.c0 ∧ Fr3 q.g (freeNA lab) (lockA lab) σ ∧
      σ.regs.X10.toBitVec = freeNA lab⟩
  | .lk2 => ⟨lab lockedL + Int64.ofNat (4 * 2), oI, fun σ c => c = q.c0 ∧
      Fr3 q.g (freeNA lab) (lockA lab) σ ∧ σ.regs.X9.toBitVec = 0#64⟩
  | .b0 => ⟨lab bumpL + Int64.ofNat (4 * 0), oI, fun σ c => c = q.c0 ∧ Fr0 q.g σ⟩
  | .b2 => ⟨lab bumpL + Int64.ofNat (4 * 2), oI, fun σ c => c = q.c0 ∧ Fr0 q.g σ ∧
      σ.regs.X9.toBitVec = lockA lab⟩
  | .unl => ⟨unlPc lab, oI, fun σ c => c = q.c0 ∧ Fr0 q.g σ ∧ σ.regs.X9.toBitVec = 0#64 ∧
      σ.regs.X10.toBitVec = lockA lab⟩
  | .b6 => ⟨lab bumpL + Int64.ofNat (4 * 6), oI, fun σ c => c = q.c0 ∧ Fr0 q.g σ⟩
  | .b8 => ⟨lab bumpL + Int64.ofNat (4 * 8), oI, fun σ c => c = q.c0 ∧ Fr0 q.g σ ∧
      σ.regs.X9.toBitVec = nextA lab⟩
  | .nxt => ⟨nextPc lab, oI, fun σ c => c = q.c0 ∧ Fr0 q.g σ ∧ σ.regs.X9.toBitVec = size0 ∧
      σ.regs.X10.toBitVec = nextA lab⟩
  | .b12 => ⟨lab bumpL + Int64.ofNat (4 * 12), oI, fun σ c => c = q.c0 ∧ Fr0 q.g σ ∧
      σ.regs.X11.toBitVec = q.k0⟩
  | .b21 => ⟨lab bumpL + Int64.ofNat (4 * 21), oI, fun σ c => c = q.c0 ∧ Fr4 q.g q.k0 σ⟩
  | .ok0 => ⟨lab StackTake.okL + Int64.ofNat (4 * 0), oI, fun σ c => c = q.c0 ∧ Fr4 q.g q.k0 σ⟩
  | .ok2 => ⟨lab StackTake.okL + Int64.ofNat (4 * 2), oI, fun σ c => c = q.c0 ∧ Fr4 q.g q.k0 σ ∧
      σ.regs.X9.toBitVec = stacksA lab⟩
  | .tk => ⟨lab takenL, oI, fun σ c => c = q.c0 ∧ Fr5 q.g q.k0 (stacksA lab) σ⟩
  | .site => ⟨lab siteL, oI, fun σ c => c = q.c0 ∧ Fr5 q.g q.k0 (stacksA lab) σ ∧
      σ.regs.X0.toBitVec = stacksA lab + q.k0 ∧ σ.regs.X1.toBitVec = size0⟩
  | .ret => ⟨lab siteL + Int64.ofNat (4 * 1), oI, fun σ c => c = q.c0 ∧ Fr5 q.g q.k0 (stacksA lab) σ⟩

/-- **The exit**: at the return address, `Post`. -/
def takeX : Unit → ND
  | () => ⟨Int64.ofBitVec q.g.ra, StackTake.oE, fun σ c => c = q.c0 ∧ StackTake.Post q.g q.k0 (stacksA lab) σ⟩

open StackTake in
/-- **The nodes, before or after the take** (`b`): `takeN`, the node past
the site holding only after it (`b = true`). -/
def takeNG (b : Bool) : TK → ND
  | .e => ⟨lab fnL, oE, fun σ c => c = q.c0 ∧ Pre q.g q.k0 σ⟩
  | .entry => ⟨lab entryL, oI, fun σ c => c = q.c0 ∧ Fr0 q.g σ⟩
  | .cls => ⟨lab clsL, oI, fun σ c => c = q.c0 ∧ Fr1 q.g σ⟩
  | .j1 => ⟨lab clsL + Int64.ofNat (4 * 4), oI, fun σ c => c = q.c0 ∧ Fr1 q.g σ⟩
  | .d0 => ⟨lab doneL + Int64.ofNat (4 * 0), oI, fun σ c => c = q.c0 ∧ Fr1 q.g σ⟩
  | .d2 => ⟨lab doneL + Int64.ofNat (4 * 2), oI, fun σ c => c = q.c0 ∧ Fr1 q.g σ ∧
      σ.regs.X9.toBitVec = freeNA lab⟩
  | .d7 => ⟨lab doneL + Int64.ofNat (4 * 7), oI, fun σ c => c = q.c0 ∧ Fr2 q.g (freeNA lab) σ⟩
  | .d9 => ⟨lab doneL + Int64.ofNat (4 * 9), oI, fun σ c => c = q.c0 ∧ Fr2 q.g (freeNA lab) σ⟩
  | .d14 => ⟨lab doneL + Int64.ofNat (4 * 14), oI, fun σ c => c = q.c0 ∧ Fr2 q.g (freeNA lab) σ⟩
  | .d16 => ⟨lab doneL + Int64.ofNat (4 * 16), oI, fun σ c => c = q.c0 ∧ Fr2 q.g (freeNA lab) σ ∧
      σ.regs.X9.toBitVec = lockA lab⟩
  | .sp0 => ⟨lab spinL, oI, fun σ c => c = q.c0 ∧ Fr3 q.g (freeNA lab) (lockA lab) σ⟩
  | .swp => ⟨swpPc lab, oI, fun σ c => c = q.c0 ∧ Fr3 q.g (freeNA lab) (lockA lab) σ ∧
      σ.regs.X9.toBitVec = 1#64 ∧ σ.regs.X10.toBitVec = lockA lab⟩
  | .sp3 => ⟨lab spinL + Int64.ofNat (4 * 3), oI, fun σ c => c = q.c0 ∧ Fr3 q.g (freeNA lab) (lockA lab) σ ∧
      σ.regs.X11.toBitVec = 0#64⟩
  | .lk0 => ⟨lab lockedL, oI, fun σ c => c = q.c0 ∧ Fr3 q.g (freeNA lab) (lockA lab) σ⟩
  | .ldn => ⟨freeNPc lab, oI, fun σ c => c = q.c0 ∧ Fr3 q.g (freeNA lab) (lockA lab) σ ∧
      σ.regs.X10.toBitVec = freeNA lab⟩
  | .lk2 => ⟨lab lockedL + Int64.ofNat (4 * 2), oI, fun σ c => c = q.c0 ∧
      Fr3 q.g (freeNA lab) (lockA lab) σ ∧ σ.regs.X9.toBitVec = 0#64⟩
  | .b0 => ⟨lab bumpL + Int64.ofNat (4 * 0), oI, fun σ c => c = q.c0 ∧ Fr0 q.g σ⟩
  | .b2 => ⟨lab bumpL + Int64.ofNat (4 * 2), oI, fun σ c => c = q.c0 ∧ Fr0 q.g σ ∧
      σ.regs.X9.toBitVec = lockA lab⟩
  | .unl => ⟨unlPc lab, oI, fun σ c => c = q.c0 ∧ Fr0 q.g σ ∧ σ.regs.X9.toBitVec = 0#64 ∧
      σ.regs.X10.toBitVec = lockA lab⟩
  | .b6 => ⟨lab bumpL + Int64.ofNat (4 * 6), oI, fun σ c => c = q.c0 ∧ Fr0 q.g σ⟩
  | .b8 => ⟨lab bumpL + Int64.ofNat (4 * 8), oI, fun σ c => c = q.c0 ∧ Fr0 q.g σ ∧
      σ.regs.X9.toBitVec = nextA lab⟩
  | .nxt => ⟨nextPc lab, oI, fun σ c => c = q.c0 ∧ Fr0 q.g σ ∧ σ.regs.X9.toBitVec = size0 ∧
      σ.regs.X10.toBitVec = nextA lab⟩
  | .b12 => ⟨lab bumpL + Int64.ofNat (4 * 12), oI, fun σ c => c = q.c0 ∧ Fr0 q.g σ ∧
      σ.regs.X11.toBitVec = q.k0⟩
  | .b21 => ⟨lab bumpL + Int64.ofNat (4 * 21), oI, fun σ c => c = q.c0 ∧ Fr4 q.g q.k0 σ⟩
  | .ok0 => ⟨lab StackTake.okL + Int64.ofNat (4 * 0), oI, fun σ c => c = q.c0 ∧ Fr4 q.g q.k0 σ⟩
  | .ok2 => ⟨lab StackTake.okL + Int64.ofNat (4 * 2), oI, fun σ c => c = q.c0 ∧ Fr4 q.g q.k0 σ ∧
      σ.regs.X9.toBitVec = stacksA lab⟩
  | .tk => ⟨lab takenL, oI, fun σ c => c = q.c0 ∧ Fr5 q.g q.k0 (stacksA lab) σ⟩
  | .site => ⟨lab siteL, oI, fun σ c => c = q.c0 ∧ Fr5 q.g q.k0 (stacksA lab) σ ∧
      σ.regs.X0.toBitVec = stacksA lab + q.k0 ∧ σ.regs.X1.toBitVec = size0⟩
  | .ret => ⟨lab siteL + Int64.ofNat (4 * 1), oI, fun σ c => b = true ∧ c = q.c0 ∧ Fr5 q.g q.k0 (stacksA lab) σ⟩

/-- **The exit, after the take**: at the return address, `Post`. -/
def takeXG (b : Bool) : Unit → ND
  | () => ⟨Int64.ofBitVec q.g.ra, StackTake.oE, fun σ c => b = true ∧ c = q.c0 ∧ StackTake.Post q.g q.k0 (stacksA lab) σ⟩

/-- **The nodes with the take's ghost, the rest after the take empty**:
`takeNG`, after the take (`b = true`) only the node past the site. -/
def takeNP (b : Bool) (i : TK) : ND :=
  match b with
  | false => takeNG lab q false i
  | true => match i with
    | .ret => takeNG lab q true .ret
    | i => ⟨(takeNG lab q true i).pc, (takeNG lab q true i).o, fun _ _ => False⟩

end Take

/-- **The take's accesses to its own words** (`ownSwp_nd`, `ownLdr_nd`,
`ownStlr_nd`, `ownLdop_nd`): the lock's swap `0 → 1`, the free count's load
(`0`), the lock's release (`0`) and the next offset's add `k0 → k0 + size0`.
The memory-side facts of each word, and its value at the access (`own…`,
named hypotheses until `ms.own` is wired). -/
structure TakeOk (ms : MemSide isaLSE2) (F : MachineData → Prop) (exe : _root_.Executable) (endPc : Int64)
    (k0 : BitVec 64) : Prop where
  lock1 : StOk ms F exe endPc (lockA (_root_.Executable.labels exe).label) 1#64
  freeN : LdOk ms F exe endPc (freeNA (_root_.Executable.labels exe).label)
  lock0 : StOk ms F exe endPc (lockA (_root_.Executable.labels exe).label) 0#64
  next : StOk ms F exe endPc (nextA (_root_.Executable.labels exe).label) (k0 + StackTake.size0)
  ownLock : OwnAt ms exe endPc (StackTake.swpPc (_root_.Executable.labels exe).label) (lockA (_root_.Executable.labels exe).label) 0#64
  ownFreeN : OwnAt ms exe endPc (StackTake.freeNPc (_root_.Executable.labels exe).label) (freeNA (_root_.Executable.labels exe).label) 0#64
  ownNext : OwnAt ms exe endPc (StackTake.nextPc (_root_.Executable.labels exe).label) (nextA (_root_.Executable.labels exe).label) k0

theorem TakeOk.mono {ms : MemSide isaLSE2} {F F' : MachineData → Prop} {exe : _root_.Executable} {endPc : Int64}
    {k0 : BitVec 64} (h : TakeOk ms F exe endPc k0) (hFF : ∀ m, F' m → F m) : TakeOk ms F' exe endPc k0 :=
  ⟨h.lock1.mono hFF, h.freeN.mono hFF, h.lock0.mono hFF, h.next.mono hFF, h.ownLock, h.ownFreeN, h.ownNext⟩

section TakeProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F F0 : MachineData → Prop}

set_option hygiene false in
/-- A block node of `scc_rt_stack_take`: the block, its `okBlk`, its code; the edge is left. -/
local macro "knode " b:ident ok:ident l:term:max k:term:max : tactic =>
  `(tactic| refine seg_nd (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (code_of hp hend (by simp only [StackTake.stackTakeIn, Bool.and_eq_true] at hin; simp only [hin])
      (l := $l) (k := $k) (by first | rfl | exact ofNat4_zero _)) fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- **`scc_rt_stack_take` is one segment** in any valid layout of
`ret0Prog`, from its entry to its return, for any region holding its frame
of 208 and any frame condition implying `F0`, given room for the stack below
`2^29` (`hk`) and the facts of the four accesses to its own words
(`htk`). -/
theorem stack_take_seg (hp : Lays exe SccCode.ret0Prog) (hend : endPc = endOf exe SccCode.ret0Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -208) (hhi : 0 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TakeG) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (htk : TakeOk ms F0 exe endPc q.k0) :
    Seg p lbl ms (At exe endPc R F (takeN (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x, At exe endPc R F (takeX (_root_.Executable.labels exe).label q x) s c) := by
  have hin := StackTake.ret0_stackTakeIn
  have hin' := hin
  simp only [StackTake.stackTakeIn, Bool.and_eq_true] at hin'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hGap, -⟩, -⟩, -⟩, -⟩, hLfn⟩, -⟩, hLfr⟩, -⟩, hLlk⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hLlk2⟩, -⟩, -⟩, hLnx⟩, -⟩, -⟩, -⟩, -⟩, hLst⟩, -⟩, -⟩, hGap2⟩, hNop⟩, -⟩ := hin'
  have eEntry := label_labelGap hp hGap
  have eSite := label_labelGap hp hGap2
  have hC := hin
  simp only [StackTake.stackTakeIn, Bool.and_eq_true] at hC
  let lab := (_root_.Executable.labels exe).label
  have hst : ∀ L σ, (AllocTcb.labStep (_root_.Executable.labels exe).label L σ).slot = σ.slot ∧
      (AllocTcb.labStep (_root_.Executable.labels exe).label L σ).regs.SP = σ.regs.SP :=
    fun L σ => ⟨(AllocTcb.labStep_spec _ L σ).2.1, (AllocTcb.labStep_spec _ L σ).2.2.1⟩
  refine fn_seg (N := takeN _ q) (E := takeX _ q) (fun i => ?_) TK.e
  cases i
  case e =>
    knode StackTake.stPro StackTake.stPro_ok StackTake.fnL 0
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stPro_walk lab _ hJ
    exact .inl ⟨TK.entry, by rw [h1, ← eEntry]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    knode StackTake.stInit StackTake.stInit_ok StackTake.entryL 0
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stInit_walk lab _ hJ
    exact .inl ⟨TK.cls, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case cls =>
    knode StackTake.stCls StackTake.stCls_ok StackTake.clsL 0
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stCls_walk lab _ hJ
    exact .inl ⟨TK.j1, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case j1 =>
    knode StackTake.stJ1 StackTake.stJ1_ok StackTake.clsL 4
    dsimp only [takeN] at hJ ⊢
    rw [StackTake.stJ1_run]
    exact .inl ⟨TK.d0, by dsimp only [takeN]; rw [ofNat4_zero], rfl, hJ⟩
  case d0 =>
    refine seg_given TK.d2 (labPair_seg hp hend hLfn hF rfl rfl fun σ c ⟨h0, h⟩ => ⟨h0, ?_, ?_⟩)
    · obtain ⟨h1, h2⟩ := hst "scc_rt_stack_free_n" σ
      simpa [StackTake.Fr1, StackTake.Fr0, h1, h2] using h
    · exact (AllocTcb.labStep_spec lab _ σ).1
  case d2 =>
    knode StackTake.stFreeN StackTake.stFreeN_ok StackTake.doneL 2
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stFreeN_walk lab _ hJ h9
    exact .inl ⟨TK.d7, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case d7 =>
    refine seg_given TK.d9 (labPair_seg hp hend hLfr hF rfl rfl fun σ c ⟨h0, h⟩ => ⟨h0, ?_⟩)
    obtain ⟨h1, h2⟩ := hst "scc_rt_stack_free" σ
    simpa [StackTake.Fr2, StackTake.Fr1, StackTake.Fr0, h1, h2] using h
  case d9 =>
    knode StackTake.stFree StackTake.stFree_ok StackTake.doneL 9
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stFree_walk lab _ hJ
    exact .inl ⟨TK.d14, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case d14 =>
    refine seg_given TK.d16 (labPair_seg hp hend hLlk hF rfl rfl fun σ c ⟨h0, h⟩ => ⟨h0, ?_, ?_⟩)
    · obtain ⟨h1, h2⟩ := hst "scc_rt_stack_lock" σ
      simpa [StackTake.Fr2, StackTake.Fr1, StackTake.Fr0, h1, h2] using h
    · exact (AllocTcb.labStep_spec lab _ σ).1
  case d16 =>
    knode StackTake.stLock StackTake.stLock_ok StackTake.doneL 16
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stLock_walk lab _ hJ h9
    exact .inl ⟨TK.sp0, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case sp0 =>
    knode StackTake.stSwp StackTake.stSwp_ok StackTake.spinL 0
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stSwp_walk lab _ hJ
    exact .inl ⟨TK.swp, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case swp =>
    refine ownSwp_nd hF (code_of hp hend hC.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 rfl) htk.ownLock fun _ σ c _ _ hJ => ?_
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    refine ⟨h10, ?_, .inl ⟨TK.sp3, (ofNat4_succ' _ 2).symm, rfl, rfl, ?_, ?_⟩⟩
    · rw [getRegOrZr_x9, h9]; exact htk.lock1.mono hFF
    · simpa [ldStep, StackTake.Fr3, StackTake.Fr2, StackTake.Fr1, StackTake.Fr0] using hJ
    · simp [ldStep]
  case sp3 =>
    knode StackTake.stSpin StackTake.stSpin_ok StackTake.spinL 3
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ, h11⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stSpin_walk lab _ hJ h11
    exact .inl ⟨TK.lk0, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case lk0 =>
    knode StackTake.stLdN StackTake.stLdN_ok StackTake.lockedL 0
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4⟩ := StackTake.stLdN_walk lab _ hJ
    exact .inl ⟨TK.ldn, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3, h4⟩
  case ldn =>
    refine ownLdr_nd hF (code_of hp hend hC.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 rfl) htk.ownFreeN fun _ σ c _ _ hJ => ?_
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ, h10⟩ := hJ
    refine ⟨by rw [rAddr_x10 h10]; simp, htk.freeN.mono hFF,
      .inl ⟨TK.lk2, (ofNat4_succ' _ 1).symm, rfl, rfl, ?_, ?_⟩⟩
    · simpa [ldStep, StackTake.Fr3, StackTake.Fr2, StackTake.Fr1, StackTake.Fr0] using hJ
    · simp [ldStep]
  case lk2 =>
    knode StackTake.stEmpty StackTake.stEmpty_ok StackTake.lockedL 2
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stEmpty_walk lab _ hJ h9
    exact .inl ⟨TK.b0, by rw [h1]; dsimp only [takeN]; rw [ofNat4_zero], by rw [h2]; rfl, rfl, h3.fr0⟩
  case b0 =>
    refine seg_given TK.b2 (labPair_seg hp hend hLlk2 hF rfl rfl fun σ c ⟨h0, h⟩ => ⟨h0, ?_, ?_⟩)
    · obtain ⟨h1, h2⟩ := hst "scc_rt_stack_lock" σ
      simpa [StackTake.Fr0, h1, h2] using h
    · exact (AllocTcb.labStep_spec lab _ σ).1
  case b2 =>
    knode StackTake.stUnl StackTake.stUnl_ok StackTake.bumpL 2
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stUnl_walk lab _ hJ h9
    exact .inl ⟨TK.unl, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case unl =>
    refine ownStlr_nd (A := lockA lab) (code_of hp hend hC.1.1.1.1.1.1.1.1.1.1.1.2 rfl) fun _ σ c _ _ hJ => ?_
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    refine ⟨h10, ?_, .inl ⟨TK.b6, (ofNat4_succ' _ 5).symm, rfl, rfl, hJ⟩⟩
    rw [getRegOrZr_x9, h9]; exact htk.lock0.mono hFF
  case b6 =>
    refine seg_given TK.b8 (labPair_seg hp hend hLnx hF rfl rfl fun σ c ⟨h0, h⟩ => ⟨h0, ?_, ?_⟩)
    · obtain ⟨h1, h2⟩ := hst "scc_rt_stack_next" σ
      simpa [StackTake.Fr0, h1, h2] using h
    · exact (AllocTcb.labStep_spec lab _ σ).1
  case b8 =>
    knode StackTake.stAdd StackTake.stAdd_ok StackTake.bumpL 8
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stAdd_walk lab _ hJ h9
    exact .inl ⟨TK.nxt, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case nxt =>
    refine ownLdop_nd hF (code_of hp hend hC.1.1.1.1.1.1.1.1.2 rfl) htk.ownNext fun _ σ c _ _ hJ => ?_
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    refine ⟨h10, ?_, .inl ⟨TK.b12, (ofNat4_succ' _ 11).symm, rfl, rfl, ?_, ?_⟩⟩
    · rw [add_apply, getRegOrZr_x9, h9]; exact htk.next.mono hFF
    · simpa [ldStep, StackTake.Fr0] using hJ
    · simp [ldStep]
  case b12 =>
    knode StackTake.stBnd StackTake.stBnd_ok StackTake.bumpL 12
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ, h11⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stBnd_walk lab _ hJ h11 hk
    exact .inl ⟨TK.b21, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case b21 =>
    knode StackTake.stJ2 StackTake.stJ2_ok StackTake.bumpL 21
    dsimp only [takeN] at hJ ⊢
    rw [StackTake.stJ2_run]
    exact .inl ⟨TK.ok0, by dsimp only [takeN]; rw [ofNat4_zero], rfl, hJ⟩
  case ok0 =>
    refine seg_given TK.ok2 (labPair_seg hp hend hLst hF rfl rfl fun σ c ⟨h0, h⟩ => ⟨h0, ?_, ?_⟩)
    · obtain ⟨h1, h2⟩ := hst "scc_rt_stacks" σ
      simpa [StackTake.Fr4, StackTake.Fr0, h1, h2] using h
    · exact (AllocTcb.labStep_spec lab _ σ).1
  case ok2 =>
    knode StackTake.stOk StackTake.stOk_ok StackTake.okL 2
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stOk_walk lab _ hJ h9
    exact .inl ⟨TK.tk, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case tk =>
    knode StackTake.stSite StackTake.stSite_ok StackTake.takenL 0
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stSite_walk lab _ hJ
    exact .inl ⟨TK.site, by rw [h1]; exact eSite, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case site =>
    refine si_nd (si := .nop) hF (code_of hp hend hNop
      (ofNat4_zero _)) fun σ c hJ => ⟨c, .refl c, .inl ⟨TK.ret, rfl, rfl, hJ.1, hJ.2.1⟩⟩
  case ret =>
    knode StackTake.stRet StackTake.stRet_ok StackTake.siteL 1
    dsimp only [takeN, takeX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stRet_walk lab _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, h3⟩

set_option hygiene false in
/-- A block node of `scc_rt_stack_take` inside `W`: the block, its `okBlk`,
its code, its obligation; the edge is left. -/
local macro "knodeW " b:ident ok:ident l:term:max k:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hFb hR hal hlo hhi
    (code_of hp hend (by simp only [StackTake.stackTakeIn, Bool.and_eq_true] at hin; simp only [hin])
      (l := $l) (k := $k) (by first | rfl | exact ofNat4_zero _)) $w fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- A frame condition, and after the take (`b`) the stack range in private
memory. -/
def takeF (F : MachineData → Prop) (rS : Scc.Sem.Range) (b : Bool) (m : MachineData) : Prop :=
  F m ∧ (b = true → StackM rS m)

/-- **`scc_rt_stack_take`'s node obligations** inside `W`, not moved by `K`
(`NodeW`, `BlkW`; both nodes of a label pair; the take site's in `W`). The
block past the site is after the take, its frame condition also `M` (the
stack range in private memory, `StackM`, at the use). The take site's frame
condition is also `P` (a segment-local fact of the caller's memory, kept to
the site; `True` by default). -/
def TakeW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F M : MachineData → Prop) (q : TakeG) (i : TK) (P : MachineData → Prop := fun _ => True) : Prop :=
  match i with
  | .e => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .e) StackTake.stPro
  | .entry => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .entry) StackTake.stInit
  | .cls => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .cls) StackTake.stCls
  | .j1 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .j1) StackTake.stJ1
  | .d0 => NodeW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .d0) ∧
      NodeW W K exe endPc R F (labMid (_root_.Executable.labels exe).label StackTake.doneL "scc_rt_stack_free_n" 0
        StackTake.oI.sp (takeNG (_root_.Executable.labels exe).label q true .d0).J)
  | .d2 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .d2) StackTake.stFreeN
  | .d7 => NodeW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .d7) ∧
      NodeW W K exe endPc R F (labMid (_root_.Executable.labels exe).label StackTake.doneL "scc_rt_stack_free" 7
        StackTake.oI.sp (takeNG (_root_.Executable.labels exe).label q true .d7).J)
  | .d9 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .d9) StackTake.stFree
  | .d14 => NodeW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .d14) ∧
      NodeW W K exe endPc R F (labMid (_root_.Executable.labels exe).label StackTake.doneL "scc_rt_stack_lock" 14
        StackTake.oI.sp (takeNG (_root_.Executable.labels exe).label q true .d14).J)
  | .d16 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .d16) StackTake.stLock
  | .sp0 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .sp0) StackTake.stSwp
  | .swp => NodeW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .swp)
  | .sp3 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .sp3) StackTake.stSpin
  | .lk0 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .lk0) StackTake.stLdN
  | .ldn => NodeW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .ldn)
  | .lk2 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .lk2) StackTake.stEmpty
  | .b0 => NodeW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .b0) ∧
      NodeW W K exe endPc R F (labMid (_root_.Executable.labels exe).label StackTake.bumpL "scc_rt_stack_lock" 0
        StackTake.oI.sp (takeNG (_root_.Executable.labels exe).label q true .b0).J)
  | .b2 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .b2) StackTake.stUnl
  | .unl => NodeW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .unl)
  | .b6 => NodeW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .b6) ∧
      NodeW W K exe endPc R F (labMid (_root_.Executable.labels exe).label StackTake.bumpL "scc_rt_stack_next" 6
        StackTake.oI.sp (takeNG (_root_.Executable.labels exe).label q true .b6).J)
  | .b8 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .b8) StackTake.stAdd
  | .nxt => NodeW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .nxt)
  | .b12 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .b12) StackTake.stBnd
  | .b21 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .b21) StackTake.stJ2
  | .ok0 => NodeW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .ok0) ∧
      NodeW W K exe endPc R F (labMid (_root_.Executable.labels exe).label StackTake.okL "scc_rt_stacks" 0
        StackTake.oI.sp (takeNG (_root_.Executable.labels exe).label q true .ok0).J)
  | .ok2 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .ok2) StackTake.stOk
  | .tk => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .tk) StackTake.stSite
  | .site => ∀ s c, At exe endPc R (fun m => F m ∧ P m) (takeNG (_root_.Executable.labels exe).label q true .site) s c →
      W s c
  | .ret => BlkW W K exe endPc R (fun m => F m ∧ M m) (takeNG (_root_.Executable.labels exe).label q true .ret)
      StackTake.stRet

omit [Kraken.Executable.ValidLayout exe] in
/-- A node obligation under a weaker frame condition holds under a stronger one. -/
theorem nodeW_mono {W : Frag isaLSE2} {K : State → State → Prop} {F' : MachineData → Prop} {n : ND}
    (h : NodeW W K exe endPc R F n) (hFF : ∀ m, F' m → F m) : NodeW W K exe endPc R F' n :=
  fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h s c ⟨he, hn, hdc, hpc, σ, hA, hFF _ hD, hJ⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- A block obligation under a weaker frame condition holds under a stronger one. -/
theorem blkW_mono {W : Frag isaLSE2} {K : State → State → Prop} {F' : MachineData → Prop} {n : ND}
    {blk : List Directive} (h : BlkW W K exe endPc R F n blk) (hFF : ∀ m, F' m → F m) :
    BlkW W K exe endPc R F' n blk :=
  fun s σ c he hn hdc hpc hA hD hJ => h s σ c he hn hdc hpc hA (hFF _ hD) hJ

omit [Kraken.Executable.ValidLayout exe] in
theorem TakeW.mono {W : Frag isaLSE2} {K : State → State → Prop} {F' M P : MachineData → Prop} {q : TakeG}
    {i : TK} (h : TakeW W K exe endPc R F M q i P) (hFF : ∀ m, F' m → F m) : TakeW W K exe endPc R F' M q i P := by
  cases i <;> dsimp only [TakeW] at h ⊢
  all_goals first
    | exact blkW_mono h hFF
    | exact blkW_mono h fun m h => ⟨hFF m h.1, h.2⟩
    | exact nodeW_mono h hFF
    | exact ⟨nodeW_mono h.1 hFF, nodeW_mono h.2 hFF⟩
    | exact fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h s c ⟨he, hn, hdc, hpc, σ, hA, ⟨hFF _ hD.1, hD.2⟩, hJ⟩

/-- **`scc_rt_stack_take` is one segment inside `W`, the take its outside
move**: `stack_take_seg` with the take site the kernel's take of `rS`
(`TakeK`, `take_ndW`) instead of a `nop`, so at the return `rS` is in
private memory (`StackM`). Given the node obligations (`hW`), the region's
cells off `rS` (`hRS`), every aligned word of `rS` off the region (`hout`),
and the frame condition kept by the take (`hFt`). -/
theorem stack_take_segW {W : Frag isaLSE2} {rS : Scc.Sem.Range} (hp : Lays exe SccCode.ret0Prog)
    (hend : endPc = endOf exe SccCode.ret0Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -208) (hhi : 0 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TakeG) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (htk : TakeOk ms F0 exe endPc q.k0) {P : MachineData → Prop} (hP : FStable R P)
    (hW : ∀ i, TakeW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F (StackM rS) q i P)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (fun s c => At exe endPc R F (takeNG (_root_.Executable.labels exe).label q false .e) s c ∧ P s.st.1)
      (fun s c => ∃ x, At exe endPc R (fun m => F m ∧ StackM rS m)
        (takeXG (_root_.Executable.labels exe).label q true x) s c) := by
  have hin := StackTake.ret0_stackTakeIn
  have hin' := hin
  simp only [StackTake.stackTakeIn, Bool.and_eq_true] at hin'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hGap, -⟩, -⟩, -⟩, -⟩, hLfn⟩, -⟩, hLfr⟩, -⟩, hLlk⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hLlk2⟩, -⟩, -⟩, hLnx⟩, -⟩, -⟩, -⟩, -⟩, hLst⟩, -⟩, -⟩, hGap2⟩, hNop⟩, -⟩ := hin'
  have eEntry := label_labelGap hp hGap
  have eSite := label_labelGap hp hGap2
  have hC := hin
  simp only [StackTake.stackTakeIn, Bool.and_eq_true] at hC
  let lab := (_root_.Executable.labels exe).label
  have hst : ∀ L σ, (AllocTcb.labStep (_root_.Executable.labels exe).label L σ).slot = σ.slot ∧
      (AllocTcb.labStep (_root_.Executable.labels exe).label L σ).regs.SP = σ.regs.SP :=
    fun L σ => ⟨(AllocTcb.labStep_spec _ L σ).2.1, (AllocTcb.labStep_spec _ L σ).2.2.1⟩
  have hAbs : ∀ {m : MachineData} {σ : AS} {pm : _root_.Mem 64}, Abs R StackTake.oI m σ →
      Abs R StackTake.oI (takeMem pm rS m) σ := fun hA =>
    ⟨hA.regs, hA.status, hA.so, fun k hk => by rw [loadInt_takeMem (hRS k hk)]; exact hA.slot k hk⟩
  have hSM := stackM_stable hfit hout
  -- `P` held until the take (`b = false`); after it only the node past the site (`takeNP`)
  refine ((fn_seg_gW (exe := exe) (endPc := endPc) (Rg := fun _ => R)
      (Fg := fun b m => takeF F rS b m ∧ (b = false → P m)) (N := takeNP lab q) (E := takeXG lab q)
    (fun b i => ?_) false TK.e).mono_pre fun s c h => ?_).mono_post fun s c h => ?_
  rotate_left
  · obtain ⟨⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hPs⟩ := h
    exact ⟨he, hn, hdc, hpc, σ, hA, ⟨⟨hD, nofun⟩, fun _ => hPs⟩, hJ⟩
  · obtain ⟨g, x, he, hn, hdc, hpc, σ, hA, ⟨⟨hD, hM⟩, -⟩, hb, hJ⟩ := h
    subst hb
    exact ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM rfl⟩, rfl, hJ⟩
  have hFb : FStable R (fun m => takeF F rS b m ∧ (b = false → P m)) := fun m m' ⟨⟨hD, hM⟩, hPm⟩ hd =>
    ⟨⟨hF m m' hD hd, fun hb => hSM m m' (hM hb) hd⟩, fun hb => hP m m' (hPm hb) hd⟩
  have hFFb : ∀ m, takeF F rS b m ∧ (b = false → P m) → F0 m := fun m h => hFF m h.1.1
  have hWb : ∀ i, TakeW W (TakeK (lab StackTake.siteL) rS) exe endPc R
      (fun m => takeF F rS b m ∧ (b = false → P m)) (StackM rS) q i P :=
    fun i => (hW i).mono fun m h => h.1.1
  cases b
  case true =>
    cases i
    case ret =>
      refine seg_fixW true ?_
      knodeW StackTake.stRet StackTake.stRet_ok StackTake.siteL 1 (blkW_mono (F := fun m => F m ∧ StackM rS m)
        (F' := fun m => takeF F rS true m ∧ (true = false → P m)) (hW TK.ret) fun m h => ⟨h.1.1, h.1.2 rfl⟩)
      dsimp only [takeNP, takeNG, takeXG] at hJ ⊢
      obtain ⟨-, rfl, hJ⟩ := hJ
      obtain ⟨h1, h2, h3⟩ := StackTake.stRet_walk lab _ hJ
      exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, rfl, h3⟩
    all_goals exact seg_falseW.mono_pre fun _ _ ⟨_, _, _, _, _, _, _, h⟩ => h
  let b := false  -- before the take
  cases i <;> dsimp only [takeNP]
  case e =>
    refine seg_fixW b ?_
    knodeW StackTake.stPro StackTake.stPro_ok StackTake.fnL 0 (hWb TK.e)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stPro_walk lab _ hJ
    exact .inl ⟨TK.entry, by rw [h1, ← eEntry]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    refine seg_fixW b ?_
    knodeW StackTake.stInit StackTake.stInit_ok StackTake.entryL 0 (hWb TK.entry)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stInit_walk lab _ hJ
    exact .inl ⟨TK.cls, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case cls =>
    refine seg_fixW b ?_
    knodeW StackTake.stCls StackTake.stCls_ok StackTake.clsL 0 (hWb TK.cls)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stCls_walk lab _ hJ
    exact .inl ⟨TK.j1, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case j1 =>
    refine seg_fixW b ?_
    knodeW StackTake.stJ1 StackTake.stJ1_ok StackTake.clsL 4 (hWb TK.j1)
    dsimp only [takeNG] at hJ ⊢
    rw [StackTake.stJ1_run]
    exact .inl ⟨TK.d0, by dsimp only [takeNP, takeNG]; rw [ofNat4_zero], rfl, hJ⟩
  case d0 =>
    refine seg_fixW b ?_
    refine seg_givenW TK.d2
      (labPair_segW hp hend hLfn hFb rfl rfl (hWb TK.d0).1 (hWb TK.d0).2 fun σ c ⟨h0, h⟩ => ⟨h0, ?_, ?_⟩)
    · obtain ⟨h1, h2⟩ := hst "scc_rt_stack_free_n" σ
      simpa [StackTake.Fr1, StackTake.Fr0, h1, h2] using h
    · exact (AllocTcb.labStep_spec lab _ σ).1
  case d2 =>
    refine seg_fixW b ?_
    knodeW StackTake.stFreeN StackTake.stFreeN_ok StackTake.doneL 2 (hWb TK.d2)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stFreeN_walk lab _ hJ h9
    exact .inl ⟨TK.d7, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case d7 =>
    refine seg_fixW b ?_
    refine seg_givenW TK.d9
      (labPair_segW hp hend hLfr hFb rfl rfl (hWb TK.d7).1 (hWb TK.d7).2 fun σ c ⟨h0, h⟩ => ⟨h0, ?_⟩)
    obtain ⟨h1, h2⟩ := hst "scc_rt_stack_free" σ
    simpa [StackTake.Fr2, StackTake.Fr1, StackTake.Fr0, h1, h2] using h
  case d9 =>
    refine seg_fixW b ?_
    knodeW StackTake.stFree StackTake.stFree_ok StackTake.doneL 9 (hWb TK.d9)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stFree_walk lab _ hJ
    exact .inl ⟨TK.d14, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case d14 =>
    refine seg_fixW b ?_
    refine seg_givenW TK.d16
      (labPair_segW hp hend hLlk hFb rfl rfl (hWb TK.d14).1 (hWb TK.d14).2 fun σ c ⟨h0, h⟩ => ⟨h0, ?_, ?_⟩)
    · obtain ⟨h1, h2⟩ := hst "scc_rt_stack_lock" σ
      simpa [StackTake.Fr2, StackTake.Fr1, StackTake.Fr0, h1, h2] using h
    · exact (AllocTcb.labStep_spec lab _ σ).1
  case d16 =>
    refine seg_fixW b ?_
    knodeW StackTake.stLock StackTake.stLock_ok StackTake.doneL 16 (hWb TK.d16)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stLock_walk lab _ hJ h9
    exact .inl ⟨TK.sp0, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case sp0 =>
    refine seg_fixW b ?_
    knodeW StackTake.stSwp StackTake.stSwp_ok StackTake.spinL 0 (hWb TK.sp0)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stSwp_walk lab _ hJ
    exact .inl ⟨TK.swp, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case swp =>
    refine seg_fixW b ?_
    refine ownSwp_ndW hFb (code_of hp hend hC.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 rfl) htk.ownLock
      (hWb TK.swp) fun _ σ c _ _ hJ => ?_
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    refine ⟨h10, ?_, .inl ⟨TK.sp3, (ofNat4_succ' _ 2).symm, rfl, rfl, ?_, ?_⟩⟩
    · rw [getRegOrZr_x9, h9]; exact htk.lock1.mono hFFb
    · simpa [ldStep, StackTake.Fr3, StackTake.Fr2, StackTake.Fr1, StackTake.Fr0] using hJ
    · simp [ldStep]
  case sp3 =>
    refine seg_fixW b ?_
    knodeW StackTake.stSpin StackTake.stSpin_ok StackTake.spinL 3 (hWb TK.sp3)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h11⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stSpin_walk lab _ hJ h11
    exact .inl ⟨TK.lk0, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case lk0 =>
    refine seg_fixW b ?_
    knodeW StackTake.stLdN StackTake.stLdN_ok StackTake.lockedL 0 (hWb TK.lk0)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4⟩ := StackTake.stLdN_walk lab _ hJ
    exact .inl ⟨TK.ldn, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3, h4⟩
  case ldn =>
    refine seg_fixW b ?_
    refine ownLdr_ndW hFb (code_of hp hend hC.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 rfl) htk.ownFreeN
      (hWb TK.ldn) fun _ σ c _ _ hJ => ?_
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h10⟩ := hJ
    refine ⟨by rw [rAddr_x10 h10]; simp [lab], htk.freeN.mono hFFb,
      .inl ⟨TK.lk2, (ofNat4_succ' _ 1).symm, rfl, rfl, ?_, ?_⟩⟩
    · simpa [ldStep, StackTake.Fr3, StackTake.Fr2, StackTake.Fr1, StackTake.Fr0] using hJ
    · simp [ldStep]
  case lk2 =>
    refine seg_fixW b ?_
    knodeW StackTake.stEmpty StackTake.stEmpty_ok StackTake.lockedL 2 (hWb TK.lk2)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stEmpty_walk lab _ hJ h9
    exact .inl ⟨TK.b0, by rw [h1]; dsimp only [takeNP, takeNG]; rw [ofNat4_zero], by rw [h2]; rfl, rfl, h3.fr0⟩
  case b0 =>
    refine seg_fixW b ?_
    refine seg_givenW TK.b2
      (labPair_segW hp hend hLlk2 hFb rfl rfl (hWb TK.b0).1 (hWb TK.b0).2 fun σ c ⟨h0, h⟩ => ⟨h0, ?_, ?_⟩)
    · obtain ⟨h1, h2⟩ := hst "scc_rt_stack_lock" σ
      simpa [StackTake.Fr0, h1, h2] using h
    · exact (AllocTcb.labStep_spec lab _ σ).1
  case b2 =>
    refine seg_fixW b ?_
    knodeW StackTake.stUnl StackTake.stUnl_ok StackTake.bumpL 2 (hWb TK.b2)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stUnl_walk lab _ hJ h9
    exact .inl ⟨TK.unl, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case unl =>
    refine seg_fixW b ?_
    refine ownStlr_ndW (A := lockA lab) (code_of hp hend hC.1.1.1.1.1.1.1.1.1.1.1.2 rfl)
      (hWb TK.unl) fun _ σ c _ _ hJ => ?_
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    refine ⟨h10, ?_, .inl ⟨TK.b6, (ofNat4_succ' _ 5).symm, rfl, rfl, hJ⟩⟩
    rw [getRegOrZr_x9, h9]; exact htk.lock0.mono hFFb
  case b6 =>
    refine seg_fixW b ?_
    refine seg_givenW TK.b8
      (labPair_segW hp hend hLnx hFb rfl rfl (hWb TK.b6).1 (hWb TK.b6).2 fun σ c ⟨h0, h⟩ => ⟨h0, ?_, ?_⟩)
    · obtain ⟨h1, h2⟩ := hst "scc_rt_stack_next" σ
      simpa [StackTake.Fr0, h1, h2] using h
    · exact (AllocTcb.labStep_spec lab _ σ).1
  case b8 =>
    refine seg_fixW b ?_
    knodeW StackTake.stAdd StackTake.stAdd_ok StackTake.bumpL 8 (hWb TK.b8)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stAdd_walk lab _ hJ h9
    exact .inl ⟨TK.nxt, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case nxt =>
    refine seg_fixW b ?_
    refine ownLdop_ndW hFb (code_of hp hend hC.1.1.1.1.1.1.1.1.2 rfl) htk.ownNext (hWb TK.nxt) fun _ σ c _ _ hJ => ?_
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    refine ⟨h10, ?_, .inl ⟨TK.b12, (ofNat4_succ' _ 11).symm, rfl, rfl, ?_, ?_⟩⟩
    · rw [add_apply, getRegOrZr_x9, h9]; exact htk.next.mono hFFb
    · simpa [ldStep, StackTake.Fr0] using hJ
    · simp [ldStep]
  case b12 =>
    refine seg_fixW b ?_
    knodeW StackTake.stBnd StackTake.stBnd_ok StackTake.bumpL 12 (hWb TK.b12)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h11⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stBnd_walk lab _ hJ h11 hk
    exact .inl ⟨TK.b21, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case b21 =>
    refine seg_fixW b ?_
    knodeW StackTake.stJ2 StackTake.stJ2_ok StackTake.bumpL 21 (hWb TK.b21)
    dsimp only [takeNG] at hJ ⊢
    rw [StackTake.stJ2_run]
    exact .inl ⟨TK.ok0, by dsimp only [takeNP, takeNG]; rw [ofNat4_zero], rfl, hJ⟩
  case ok0 =>
    refine seg_fixW b ?_
    refine seg_givenW TK.ok2
      (labPair_segW hp hend hLst hFb rfl rfl (hWb TK.ok0).1 (hWb TK.ok0).2 fun σ c ⟨h0, h⟩ => ⟨h0, ?_, ?_⟩)
    · obtain ⟨h1, h2⟩ := hst "scc_rt_stacks" σ
      simpa [StackTake.Fr4, StackTake.Fr0, h1, h2] using h
    · exact (AllocTcb.labStep_spec lab _ σ).1
  case ok2 =>
    refine seg_fixW b ?_
    knodeW StackTake.stOk StackTake.stOk_ok StackTake.okL 2 (hWb TK.ok2)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stOk_walk lab _ hJ h9
    exact .inl ⟨TK.tk, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case tk =>
    refine seg_fixW b ?_
    knodeW StackTake.stSite StackTake.stSite_ok StackTake.takenL 0 (hWb TK.tk)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stSite_walk lab _ hJ
    exact .inl ⟨TK.site, by rw [h1]; exact eSite, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case site =>
    refine seg_movedW (j := TK.ret) ((take_ndW (n := takeNG lab q false TK.site) (n' := takeNG lab q true TK.ret) rfl
      (fun s he hn => code_of hp hend hNop
        (ofNat4_zero _) s he hn) (fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => hW TK.site s c
          ⟨he, hn, hdc, hpc, σ, hA, ⟨hD.1.1, hD.2 rfl⟩, hJ⟩)
        (fun m σ pm hA hD => ⟨hAbs hA, ⟨hFt m pm hD.1.1, fun _ => stackM_takeMem⟩, nofun⟩)
      fun σ c hJ => ⟨rfl, c, .refl c, rfl, hJ.1, hJ.2.1⟩).mono_post fun _ _ h => ⟨true, h⟩)
  case ret =>
    exact seg_falseW.mono_pre fun _ _ ⟨_, _, _, _, _, _, _, h, _⟩ => Bool.false_ne_true h

end TakeProof

/-! ## `scc_rt_thread_init` -/

/-- **The ghosts of a call of `scc_rt_thread_init`**: `sp`, `x29`, `x30` at
entry, the TCB's address, `scc_rt_stack_next`'s value `k0` on entry, the
source control. -/
structure TiG where
  g : ThreadInit.G
  tcb : BitVec 64
  k0 : BitVec 64
  c0 : Ctl

/-- `scc_rt_thread_init`'s internal nodes. -/
inductive TI where
  | e | entry | call | sp | st0 | f1 | st1 | f2 | st2 | f3 | st3 | f4 | st4 | f5 | st5 | ret

/-- The label after `scc_rt_thread_init`'s call, two instructions after `.0_entry`. -/
def tiSpIn (prog : List Directive) : Bool := labelGap prog ThreadInit.entryL ThreadInit.spL 2

theorem ret0_tiSpIn : tiSpIn SccCode.ret0Prog = true := by decide +kernel

section Ti

variable (lab : Label → Int64) (q : TiG)

/-- The stack's base `scc_rt_stacks + k0`. -/
abbrev tiBase : BitVec 64 := stacksA lab + q.k0

open ThreadInit in
/-- **The nodes.** -/
def tiN : TI → ND
  | .e => ⟨lab fnL, oE, fun σ c => c = q.c0 ∧ Pre q.g q.tcb σ⟩
  | .entry => ⟨lab entryL, oI, fun σ c => c = q.c0 ∧ Fr0 q.g q.tcb σ⟩
  | .call => ⟨lab StackTake.fnL, oI, fun σ c => (c = q.c0 ∧ Fr0 q.g q.tcb σ ∧
      σ.regs.X0.toBitVec = StackTake.size0) ∧ σ.regs.X30.toBitVec = (lab spL).toBitVec⟩
  | .sp => ⟨lab spL, oI, fun σ c => c = q.c0 ∧ Fr0 q.g q.tcb σ ∧ σ.regs.X0.toBitVec = tiBase lab q⟩
  | .st0 => ⟨storePc lab 0, oI, fun σ c => c = q.c0 ∧ Fr1 q.g q.tcb (tiBase lab q) σ ∧
      σ.regs.X9.toBitVec = q.tcb ∧ σ.regs.X10.toBitVec = q.tcb⟩
  | .f1 => ⟨lab spL + Int64.ofNat (4 * 12), oI, fun σ c => c = q.c0 ∧ Fr1 q.g q.tcb (tiBase lab q) σ⟩
  | .st1 => ⟨storePc lab 1, oI, fun σ c => c = q.c0 ∧ Fr1 q.g q.tcb (tiBase lab q) σ ∧
      σ.regs.X9.toBitVec = tiBase lab q + 4096#64 ∧ σ.regs.X10.toBitVec = q.tcb⟩
  | .f2 => ⟨lab spL + Int64.ofNat (4 * 15), oI, fun σ c => c = q.c0 ∧ Fr1 q.g q.tcb (tiBase lab q) σ⟩
  | .st2 => ⟨storePc lab 2, oI, fun σ c => c = q.c0 ∧ Fr1 q.g q.tcb (tiBase lab q) σ ∧
      σ.regs.X9.toBitVec = 0#64 ∧ σ.regs.X10.toBitVec = q.tcb⟩
  | .f3 => ⟨lab spL + Int64.ofNat (4 * 18), oI, fun σ c => c = q.c0 ∧ Fr1 q.g q.tcb (tiBase lab q) σ⟩
  | .st3 => ⟨storePc lab 3, oI, fun σ c => c = q.c0 ∧ Fr1 q.g q.tcb (tiBase lab q) σ ∧
      σ.regs.X9.toBitVec = 0#64 ∧ σ.regs.X10.toBitVec = q.tcb⟩
  | .f4 => ⟨lab spL + Int64.ofNat (4 * 21), oI, fun σ c => c = q.c0 ∧ Fr1 q.g q.tcb (tiBase lab q) σ⟩
  | .st4 => ⟨storePc lab 4, oI, fun σ c => c = q.c0 ∧ Fr1 q.g q.tcb (tiBase lab q) σ ∧
      σ.regs.X9.toBitVec = tiBase lab q ∧ σ.regs.X10.toBitVec = q.tcb⟩
  | .f5 => ⟨lab spL + Int64.ofNat (4 * 24), oI, fun σ c => c = q.c0 ∧ Fr1 q.g q.tcb (tiBase lab q) σ⟩
  | .st5 => ⟨storePc lab 5, oI, fun σ c => c = q.c0 ∧ Fr1 q.g q.tcb (tiBase lab q) σ ∧
      σ.regs.X9.toBitVec = tiBase lab q + 16384#64 ∧ σ.regs.X10.toBitVec = q.tcb⟩
  | .ret => ⟨lab spL + Int64.ofNat (4 * 27), oI, fun σ c => c = q.c0 ∧ Fr1 q.g q.tcb (tiBase lab q) σ⟩

/-- **The exit**: at the return address, `Post`. -/
def tiX : Unit → ND
  | () => ⟨Int64.ofBitVec q.g.ra, ThreadInit.oE, fun σ c => c = q.c0 ∧ ThreadInit.Post q.g (tiBase lab q) σ⟩

/-- The take's ghosts at a call from `scc_rt_thread_init`. -/
abbrev tiTake (g : StackTake.G) : TakeG := ⟨g, q.k0, q.c0⟩

end Ti

section TiProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F F0 : MachineData → Prop}

set_option hygiene false in
/-- A block node of `scc_rt_thread_init`. -/
local macro "inode " b:ident ok:ident l:term:max k:term:max : tactic =>
  `(tactic| refine seg_nd (by simp [$b:ident]) $ok hF hR hal (by omega) hhi
    (code_of hp hend (by simp only [ThreadInit.threadInitIn, Bool.and_eq_true] at hin; simp only [hin])
      (l := $l) (k := $k) (by first | rfl | exact ofNat4_zero _)) fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- **`scc_rt_thread_init` is one segment** in any valid layout of
`ret0Prog`, from its entry to its return, for any region holding its frame
of 48 and `scc_rt_stack_take`'s of 208 below, and any frame condition
implying `F0`: the TCB's six fields' stores (`hfld`, their `StOk`), the
take's room (`hk`) and the facts of its four own-word accesses (`htk`). -/
theorem thread_init_seg (hp : Lays exe SccCode.ret0Prog) (hend : endPc = endOf exe SccCode.ret0Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -256) (hhi : 0 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TiG) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields q.tcb (tiBase (_root_.Executable.labels exe).label q),
      StOk ms F0 exe endPc (q.tcb + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F0 exe endPc q.k0) :
    Seg p lbl ms (At exe endPc R F (tiN (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x, At exe endPc R F (tiX (_root_.Executable.labels exe).label q x) s c) := by
  have hin := ThreadInit.ret0_threadInitIn
  have hin' := hin
  simp only [ThreadInit.threadInitIn, Bool.and_eq_true] at hin'
  have eEntry := label_labelGap hp hin'.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
  have eSp := label_labelGap hp ret0_tiSpIn
  let lab := (_root_.Executable.labels exe).label
  refine fn_seg (N := tiN _ q) (E := tiX _ q) (fun i => ?_) TI.e
  cases i
  case e =>
    inode ThreadInit.tiPro ThreadInit.tiPro_ok ThreadInit.fnL 0
    dsimp only [tiN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := ThreadInit.tiPro_walk lab _ hJ
    exact .inl ⟨TI.entry, by rw [h1, ← eEntry]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    inode ThreadInit.tiCall ThreadInit.tiCall_ok ThreadInit.entryL 0
    dsimp only [tiN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := ThreadInit.tiCall_walk lab _ hJ
    refine .inl ⟨TI.call, h1.symm, ?_, ⟨rfl, h2, h3⟩, ?_⟩
    · rw [ThreadInit.tiCall_run]; rfl
    · rw [ThreadInit.tiCall_run]
      simp only [ofInt_bmod]
      rw [eSp, show Int64.ofNat (4 * 2) = 8 from rfl, Int64.toBitVec_add,
        show ∀ y : Int, y + 4 + 4 = y + 8 from fun y => by omega, BitVec.ofInt_add,
        Spike.Lib.int64_ofInt_toInt]; rfl
  case call =>
    refine call_nd_F (lo' := -208) (hi' := 0) (Ne := fun g => takeN lab (tiTake q g) .e)
      (Ex := fun g => takeX lab (tiTake q g))
      hR hal hF (by show R.lo ≤ -48 + -208; omega) (by decide) (by show (-48 : Int) < R.hi; omega) (by decide)
      (by show (-48 : Int) % 16 = 0; decide) (by decide) (by decide)
      (fun R' F' hR' hal' hlo' hhi' hF' hFF' g' =>
        stack_take_seg hp hend hF' hR' hal' hlo' hhi' (fun m h => hFF m (hFF' m h)) (tiTake q g') hk
          htk)
      (fun _ => rfl) ?_ ?_
    · rintro σC c ⟨⟨rfl, -, h0⟩, -⟩
      exact ⟨⟨σC.regs.SP.toBitVec, σC.regs.X29.toBitVec, σC.regs.X30.toBitVec⟩, rfl, rfl, rfl, rfl, rfl, h0⟩
    · rintro g x σC c σx c' σR ⟨⟨-, hfr, -⟩, h30⟩ ⟨-, hsp', -, h30', -⟩ ⟨rfl, hPost⟩ hregs - hslot
      obtain ⟨hsp, h16, h8, h48⟩ := hfr
      have hk' : ∀ k : Int, k % 8 = 0 → -48 ≤ k → k ≤ -8 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
        hslot k ⟨h1, by omega, by omega⟩ fun h => by simp only [Region.Off, Region.callee] at h; dsimp only [tiN] at h; omega
      refine .inl ⟨TI.sp, ?_, rfl, rfl, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · show lab ThreadInit.spL = Int64.ofBitVec g.ra
        rw [← h30']
        show lab _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [h30, int64_ofBitVec_toBitVec]
      · show σR.regs.SP.toBitVec = _
        rw [hregs, hPost.1, ← hsp']; exact hsp
      · rw [hk' (-16) (by decide) (by decide) (by decide)]; exact h16
      · rw [hk' (-8) (by decide) (by decide) (by decide)]; exact h8
      · rw [hk' (-48) (by decide) (by decide) (by decide)]; exact h48
      · show σR.regs.X0.toBitVec = _
        rw [hregs]; exact hPost.2.2.2
  case sp =>
    inode ThreadInit.tiSp ThreadInit.tiSp_ok ThreadInit.spL 0
    dsimp only [tiN] at hJ ⊢
    obtain ⟨rfl, hJ, h0⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiSp_walk lab _ hJ h0
    exact .inl ⟨TI.st0, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case st0 =>
    have hc : blockAt SccCode.ret0Prog ThreadInit.spL (11 + 3 * 0) [strDir .X9 .X10 0] = true :=
      (show parseAArch64("str x9, [x10]") = [strDir .X9 .X10 0] by decide) ▸ hin'.1.1.1.1.1.1.1.1.1.1.1.2
    refine rtst_nd (code_of hp hend hc rfl) fun m σ c _ hD hJ => ?_
    dsimp only [tiN] at hJ
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    have hfi := hfld (8 * 0, q.tcb) (by simp [ThreadInit.fields])
    rw [rAddr_x10 h10, show BitVec.ofInt 64 (Int64.toInt 0) = BitVec.ofNat 64 (8 * 0) by decide,
      getRegOrZr_x9, h9]
    exact ⟨hfi.rt, hfi.mp, hfi.G, hfi.unmapped m (hFF m hD), q.c0, .refl q.c0,
      .inl ⟨TI.f1, (ofNat4_succ' _ _).symm, rfl, rfl, hJ⟩⟩
  case f1 =>
    inode ThreadInit.tiF1 ThreadInit.tiF1_ok ThreadInit.spL 12
    dsimp only [tiN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF1_walk lab _ hJ
    exact .inl ⟨TI.st1, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case st1 =>
    have hc : blockAt SccCode.ret0Prog ThreadInit.spL (11 + 3 * 1) [strDir .X9 .X10 8] = true :=
      (show parseAArch64("str x9, [x10, #8]") = [strDir .X9 .X10 8] by decide) ▸ hin'.1.1.1.1.1.1.1.1.1.2
    refine rtst_nd (code_of hp hend hc rfl) fun m σ c _ hD hJ => ?_
    dsimp only [tiN] at hJ
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    have hfi := hfld (8 * 1, tiBase (_root_.Executable.labels exe).label q + 4096#64) (by simp [ThreadInit.fields])
    rw [rAddr_x10 h10, show BitVec.ofInt 64 (Int64.toInt 8) = BitVec.ofNat 64 (8 * 1) by decide,
      getRegOrZr_x9, h9]
    exact ⟨hfi.rt, hfi.mp, hfi.G, hfi.unmapped m (hFF m hD), q.c0, .refl q.c0,
      .inl ⟨TI.f2, (ofNat4_succ' _ _).symm, rfl, rfl, hJ⟩⟩
  case f2 =>
    inode ThreadInit.tiF2 ThreadInit.tiF2_ok ThreadInit.spL 15
    dsimp only [tiN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF2_walk lab _ hJ
    exact .inl ⟨TI.st2, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case st2 =>
    have hc : blockAt SccCode.ret0Prog ThreadInit.spL (11 + 3 * 2) [strDir .X9 .X10 16] = true :=
      (show parseAArch64("str x9, [x10, #16]") = [strDir .X9 .X10 16] by decide) ▸ hin'.1.1.1.1.1.1.1.2
    refine rtst_nd (code_of hp hend hc rfl) fun m σ c _ hD hJ => ?_
    dsimp only [tiN] at hJ
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    have hfi := hfld (8 * 2, 0#64) (by simp [ThreadInit.fields])
    rw [rAddr_x10 h10, show BitVec.ofInt 64 (Int64.toInt 16) = BitVec.ofNat 64 (8 * 2) by decide,
      getRegOrZr_x9, h9]
    exact ⟨hfi.rt, hfi.mp, hfi.G, hfi.unmapped m (hFF m hD), q.c0, .refl q.c0,
      .inl ⟨TI.f3, (ofNat4_succ' _ _).symm, rfl, rfl, hJ⟩⟩
  case f3 =>
    inode ThreadInit.tiF3 ThreadInit.tiF3_ok ThreadInit.spL 18
    dsimp only [tiN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF3_walk lab _ hJ
    exact .inl ⟨TI.st3, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case st3 =>
    have hc : blockAt SccCode.ret0Prog ThreadInit.spL (11 + 3 * 3) [strDir .X9 .X10 24] = true :=
      (show parseAArch64("str x9, [x10, #24]") = [strDir .X9 .X10 24] by decide) ▸ hin'.1.1.1.1.1.2
    refine rtst_nd (code_of hp hend hc rfl) fun m σ c _ hD hJ => ?_
    dsimp only [tiN] at hJ
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    have hfi := hfld (8 * 3, 0#64) (by simp [ThreadInit.fields])
    rw [rAddr_x10 h10, show BitVec.ofInt 64 (Int64.toInt 24) = BitVec.ofNat 64 (8 * 3) by decide,
      getRegOrZr_x9, h9]
    exact ⟨hfi.rt, hfi.mp, hfi.G, hfi.unmapped m (hFF m hD), q.c0, .refl q.c0,
      .inl ⟨TI.f4, (ofNat4_succ' _ _).symm, rfl, rfl, hJ⟩⟩
  case f4 =>
    inode ThreadInit.tiF4 ThreadInit.tiF4_ok ThreadInit.spL 21
    dsimp only [tiN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF4_walk lab _ hJ
    exact .inl ⟨TI.st4, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case st4 =>
    have hc : blockAt SccCode.ret0Prog ThreadInit.spL (11 + 3 * 4) [strDir .X9 .X10 32] = true :=
      (show parseAArch64("str x9, [x10, #32]") = [strDir .X9 .X10 32] by decide) ▸ hin'.1.1.1.2
    refine rtst_nd (code_of hp hend hc rfl) fun m σ c _ hD hJ => ?_
    dsimp only [tiN] at hJ
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    have hfi := hfld (8 * 4, tiBase (_root_.Executable.labels exe).label q) (by simp [ThreadInit.fields])
    rw [rAddr_x10 h10, show BitVec.ofInt 64 (Int64.toInt 32) = BitVec.ofNat 64 (8 * 4) by decide,
      getRegOrZr_x9, h9]
    exact ⟨hfi.rt, hfi.mp, hfi.G, hfi.unmapped m (hFF m hD), q.c0, .refl q.c0,
      .inl ⟨TI.f5, (ofNat4_succ' _ _).symm, rfl, rfl, hJ⟩⟩
  case f5 =>
    inode ThreadInit.tiF5 ThreadInit.tiF5_ok ThreadInit.spL 24
    dsimp only [tiN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF5_walk lab _ hJ
    exact .inl ⟨TI.st5, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case st5 =>
    have hc : blockAt SccCode.ret0Prog ThreadInit.spL (11 + 3 * 5) [strDir .X9 .X10 40] = true :=
      (show parseAArch64("str x9, [x10, #40]") = [strDir .X9 .X10 40] by decide) ▸ hin'.1.2
    refine rtst_nd (code_of hp hend hc rfl) fun m σ c _ hD hJ => ?_
    dsimp only [tiN] at hJ
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    have hfi := hfld (8 * 5, tiBase (_root_.Executable.labels exe).label q + 16384#64) (by simp [ThreadInit.fields])
    rw [rAddr_x10 h10, show BitVec.ofInt 64 (Int64.toInt 40) = BitVec.ofNat 64 (8 * 5) by decide,
      getRegOrZr_x9, h9]
    exact ⟨hfi.rt, hfi.mp, hfi.G, hfi.unmapped m (hFF m hD), q.c0, .refl q.c0,
      .inl ⟨TI.ret, (ofNat4_succ' _ _).symm, rfl, rfl, hJ⟩⟩
  case ret =>
    inode ThreadInit.tiRet ThreadInit.tiRet_ok ThreadInit.spL 27
    dsimp only [tiN, tiX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := ThreadInit.tiRet_walk lab _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, h3⟩

end TiProof

/-! ### `scc_rt_thread_init` inside `W`, the take its outside move -/

section TiG

variable (lab : Label → Int64) (q : TiG)

/-- A node after the take's call: its invariant, with the take done (`b`). -/
def tiA (b : Bool) (n : ND) : ND := ⟨n.pc, n.o, fun σ c => b = true ∧ n.J σ c⟩

/-- **The nodes with the take's ghost** `b`: `tiN`, the nodes after the call
of `scc_rt_stack_take` only once the take is done. -/
def tiNG (b : Bool) : TI → ND
  | .e => tiN lab q .e
  | .entry => tiN lab q .entry
  | .call => tiN lab q .call
  | .sp => tiA b (tiN lab q .sp)
  | .st0 => tiA b (tiN lab q .st0)
  | .f1 => tiA b (tiN lab q .f1)
  | .st1 => tiA b (tiN lab q .st1)
  | .f2 => tiA b (tiN lab q .f2)
  | .st2 => tiA b (tiN lab q .st2)
  | .f3 => tiA b (tiN lab q .f3)
  | .st3 => tiA b (tiN lab q .st3)
  | .f4 => tiA b (tiN lab q .f4)
  | .st4 => tiA b (tiN lab q .st4)
  | .f5 => tiA b (tiN lab q .f5)
  | .st5 => tiA b (tiN lab q .st5)
  | .ret => tiA b (tiN lab q .ret)

/-- The exit with the take's ghost. -/
def tiXG (b : Bool) (x : Unit) : ND := tiA b (tiX lab q x)

/-- A node before the take's call: its invariant, with the take not done (`b`). -/
def tiB (b : Bool) (n : ND) : ND := ⟨n.pc, n.o, fun σ c => b = false ∧ n.J σ c⟩

/-- **The nodes with the take's ghost, both sides gated**: `tiNG`, the nodes
up to the call of `scc_rt_stack_take` only before the take is done. -/
def tiNP (b : Bool) : TI → ND
  | .e => tiB b (tiN lab q .e)
  | .entry => tiB b (tiN lab q .entry)
  | .call => tiB b (tiN lab q .call)
  | .sp => tiNG lab q b .sp
  | .st0 => tiNG lab q b .st0
  | .f1 => tiNG lab q b .f1
  | .st1 => tiNG lab q b .st1
  | .f2 => tiNG lab q b .f2
  | .st2 => tiNG lab q b .st2
  | .f3 => tiNG lab q b .f3
  | .st3 => tiNG lab q b .st3
  | .f4 => tiNG lab q b .f4
  | .st4 => tiNG lab q b .st4
  | .f5 => tiNG lab q b .f5
  | .st5 => tiNG lab q b .st5
  | .ret => tiNG lab q b .ret

end TiG

/-- The caller's cells outside a callee's region (at `kc`, from `lo'` to
`hi'`) hold values. -/
def CallerCells (R : Region) (kc lo' hi' : Int) (m : MachineData) : Prop :=
  ∀ k, R.Off k → ¬ (R.callee kc lo' hi').Off (k - kc) → (Mem.loadInt m.dmem (R.addr k) 8).isSome

/-- **`scc_rt_thread_init`'s node obligations inside `W`**: the block
nodes' states (`BlkW`), the stores' (`NodeW`), and at the call those of
`scc_rt_stack_take` in the callee's region (`TakeW`, for every ghost,
the caller's cells outside it holding values). -/
def TiW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F M : MachineData → Prop) (q : TiG) (i : TI) (P : MachineData → Prop := fun _ => True) : Prop :=
  match i with
  | .e => BlkW W K exe endPc R F (tiN (_root_.Executable.labels exe).label q .e) ThreadInit.tiPro
  | .entry => BlkW W K exe endPc R F (tiN (_root_.Executable.labels exe).label q .entry) ThreadInit.tiCall
  | .call => ∀ g, g.ra = ((_root_.Executable.labels exe).label ThreadInit.spL).toBitVec → ∀ i,
      TakeW W K exe endPc (R.callee ThreadInit.oI.sp (-208) 0)
        (fun m => F m ∧ CallerCells R ThreadInit.oI.sp (-208) 0 m) M (tiTake q g) i P
  | .sp => BlkW W K exe endPc R (fun m => F m ∧ M m) (tiN (_root_.Executable.labels exe).label q .sp)
      ThreadInit.tiSp
  | .st0 => NodeW W K exe endPc R (fun m => F m ∧ M m) (tiN (_root_.Executable.labels exe).label q .st0)
  | .f1 => BlkW W K exe endPc R (fun m => F m ∧ M m) (tiN (_root_.Executable.labels exe).label q .f1)
      ThreadInit.tiF1
  | .st1 => NodeW W K exe endPc R (fun m => F m ∧ M m) (tiN (_root_.Executable.labels exe).label q .st1)
  | .f2 => BlkW W K exe endPc R (fun m => F m ∧ M m) (tiN (_root_.Executable.labels exe).label q .f2)
      ThreadInit.tiF2
  | .st2 => NodeW W K exe endPc R (fun m => F m ∧ M m) (tiN (_root_.Executable.labels exe).label q .st2)
  | .f3 => BlkW W K exe endPc R (fun m => F m ∧ M m) (tiN (_root_.Executable.labels exe).label q .f3)
      ThreadInit.tiF3
  | .st3 => NodeW W K exe endPc R (fun m => F m ∧ M m) (tiN (_root_.Executable.labels exe).label q .st3)
  | .f4 => BlkW W K exe endPc R (fun m => F m ∧ M m) (tiN (_root_.Executable.labels exe).label q .f4)
      ThreadInit.tiF4
  | .st4 => NodeW W K exe endPc R (fun m => F m ∧ M m) (tiN (_root_.Executable.labels exe).label q .st4)
  | .f5 => BlkW W K exe endPc R (fun m => F m ∧ M m) (tiN (_root_.Executable.labels exe).label q .f5)
      ThreadInit.tiF5
  | .st5 => NodeW W K exe endPc R (fun m => F m ∧ M m) (tiN (_root_.Executable.labels exe).label q .st5)
  | .ret => BlkW W K exe endPc R (fun m => F m ∧ M m) (tiN (_root_.Executable.labels exe).label q .ret)
      ThreadInit.tiRet

section TiWProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F F0 : MachineData → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- A block obligation holds at the node with the take done, under a
stronger frame condition. -/
theorem blkW_tiA {W : Frag isaLSE2} {K : State → State → Prop} {F' : MachineData → Prop} {n : ND}
    {blk : List Directive} {b : Bool} (h : BlkW W K exe endPc R F n blk) (hFF : ∀ m, F' m → F m) :
    BlkW W K exe endPc R F' (tiA b n) blk :=
  fun s σ c he hn hdc hpc hA hD hJ => h s σ c he hn hdc hpc hA (hFF _ hD) hJ.2

omit [Kraken.Executable.ValidLayout exe] in
/-- A node obligation holds at the node with the take done, under a
stronger frame condition. -/
theorem nodeW_tiA {W : Frag isaLSE2} {K : State → State → Prop} {F' : MachineData → Prop} {n : ND} {b : Bool}
    (h : NodeW W K exe endPc R F n) (hFF : ∀ m, F' m → F m) : NodeW W K exe endPc R F' (tiA b n) :=
  fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h s c ⟨he, hn, hdc, hpc, σ, hA, hFF _ hD, hJ.2⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- A block obligation after the take, with the stack range in private
memory, holds at the node with the take done (`b`, so `takeF` gives the
range). -/
theorem blkW_tiS {W : Frag isaLSE2} {K : State → State → Prop} {rS : Scc.Sem.Range} {n : ND}
    {blk : List Directive} {b : Bool} (h : BlkW W K exe endPc R (fun m => F m ∧ StackM rS m) n blk) :
    BlkW W K exe endPc R (takeF F rS b) (tiA b n) blk :=
  fun s σ c he hn hdc hpc hA hD hJ => h s σ c he hn hdc hpc hA ⟨hD.1, hD.2 hJ.1⟩ hJ.2

omit [Kraken.Executable.ValidLayout exe] in
/-- A node obligation after the take, with the stack range in private
memory, holds at the node with the take done. -/
theorem nodeW_tiS {W : Frag isaLSE2} {K : State → State → Prop} {rS : Scc.Sem.Range} {n : ND} {b : Bool}
    (h : NodeW W K exe endPc R (fun m => F m ∧ StackM rS m) n) : NodeW W K exe endPc R (takeF F rS b) (tiA b n) :=
  fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h s c ⟨he, hn, hdc, hpc, σ, hA, ⟨hD.1, hD.2 hJ.1⟩, hJ.2⟩

set_option hygiene false in
/-- A block node of `scc_rt_thread_init` inside `W`. -/
local macro "inodeW " b:ident ok:ident l:term:max k:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hFb hR hal (by omega) hhi
    (code_of hp hend (by simp only [ThreadInit.threadInitIn, Bool.and_eq_true] at hin; simp only [hin])
      (l := $l) (k := $k) (by first | rfl | exact ofNat4_zero _)) $w fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- **`scc_rt_thread_init` is one segment inside `W`, the take its outside
move**: `thread_init_seg` with `stack_take_segW` at the call, so at the
return the stack range `rS` is in private memory (`StackM`). Given the node
obligations (`hW`), the region's cells off `rS` (`hRS`), every aligned word
of `rS` off the region (`hout`), and the frame condition kept by the take
(`hFt`). -/
theorem thread_init_segW {W : Frag isaLSE2} {rS : Scc.Sem.Range} (hp : Lays exe SccCode.ret0Prog)
    (hend : endPc = endOf exe SccCode.ret0Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -256) (hhi : 0 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TiG) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields q.tcb (tiBase (_root_.Executable.labels exe).label q),
      StOk ms F0 exe endPc (q.tcb + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F0 exe endPc q.k0) {P : MachineData → Prop} (hP : FStable R P)
    (hW : ∀ i, TiW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F (StackM rS) q i P)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (fun s c => At exe endPc R F (tiN (_root_.Executable.labels exe).label q .e) s c ∧ P s.st.1)
      (fun s c => ∃ x,
        At exe endPc R (fun m => F m ∧ StackM rS m) (tiX (_root_.Executable.labels exe).label q x) s c) := by
  have hin := ThreadInit.ret0_threadInitIn
  have hin' := hin
  simp only [ThreadInit.threadInitIn, Bool.and_eq_true] at hin'
  have eEntry := label_labelGap hp hin'.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
  have eSp := label_labelGap hp ret0_tiSpIn
  let lab := (_root_.Executable.labels exe).label
  have hSM := stackM_stable hfit hout
  -- the take's callee region, and `rS` off it
  have hb' := Region.callee_base (hi' := 0) hR (show R.lo ≤ -48 + -208 by omega) (by decide)
    (show (-48 : Int) < R.hi by omega)
  have hRS' : ∀ k, (R.callee (-48) (-208) 0).Off k → ∀ i < 8,
      (R.callee (-48) (-208) 0).addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS := fun k hk i hi => by
    rw [Region.callee_addr]
    exact hRS _ (Region.callee_off (show R.lo ≤ -48 + -208 by omega) (show (-48 : Int) + 0 ≤ R.hi by omega)
      (by decide) hk) i hi
  have hout' : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ (R.callee (-48) (-208) 0).base.toNat + (R.callee (-48) (-208) 0).lo ∨
        ((R.callee (-48) (-208) 0).base.toNat : Int) + (R.callee (-48) (-208) 0).hi ≤ a := fun a h8 ha ha7 => by
    show (a : Int) + 8 ≤ ((R.callee (-48) (-208) 0).base.toNat : Int) + -208 ∨
      ((R.callee (-48) (-208) 0).base.toNat : Int) + 0 ≤ a
    rcases hout a h8 ha ha7 with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)
  -- `P` held until the take's call (`b = false`); the nodes up to it gated by `b = false` (`tiNP`)
  refine ((fn_seg_gW (exe := exe) (endPc := endPc) (Rg := fun _ => R)
      (Fg := fun b m => takeF F rS b m ∧ (b = false → P m))
      (N := tiNP (_root_.Executable.labels exe).label q) (E := tiXG (_root_.Executable.labels exe).label q)
      (fun b i => ?_) false TI.e).mono_pre fun s c h => ?_).mono_post
    fun s c h => ?_
  rotate_left
  · obtain ⟨⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hPs⟩ := h
    exact ⟨he, hn, hdc, hpc, σ, hA, ⟨⟨hD, nofun⟩, fun _ => hPs⟩, rfl, hJ⟩
  · obtain ⟨g, x, he, hn, hdc, hpc, σ, hA, ⟨⟨hD, hM⟩, -⟩, hb, hJ⟩ := h
    subst hb
    exact ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM rfl⟩, hJ⟩
  have hFt0 : FStable R (takeF F rS b) := fun m m' ⟨hD, hM⟩ hd => ⟨hF m m' hD hd, fun hb => hSM m m' (hM hb) hd⟩
  have hFb : FStable R (fun m => takeF F rS b m ∧ (b = false → P m)) := fun m m' ⟨hD, hPm⟩ hd =>
    ⟨hFt0 m m' hD hd, fun hb => hP m m' (hPm hb) hd⟩
  have hFFb : ∀ m, takeF F rS b m ∧ (b = false → P m) → F0 m := fun m h => hFF m h.1.1
  cases i <;> dsimp only [tiNP]
  case e =>
    cases b
    case true => exact seg_falseW.mono_pre fun _ _ ⟨_, _, _, _, _, _, _, h, _⟩ => absurd h (by decide)
    refine seg_fixW false ?_
    inodeW ThreadInit.tiPro ThreadInit.tiPro_ok ThreadInit.fnL 0
      (fun s σ c he hn hdc hpc hA hD hJ => hW TI.e s σ c he hn hdc hpc hA hD.1.1 hJ.2)
    dsimp only [tiNP, tiB, tiN] at hJ ⊢
    obtain ⟨-, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := ThreadInit.tiPro_walk lab _ hJ
    exact .inl ⟨TI.entry, by rw [h1, ← eEntry]; rfl, by rw [h2]; rfl, rfl, rfl, h3⟩
  case entry =>
    cases b
    case true => exact seg_falseW.mono_pre fun _ _ ⟨_, _, _, _, _, _, _, h, _⟩ => absurd h (by decide)
    refine seg_fixW false ?_
    inodeW ThreadInit.tiCall ThreadInit.tiCall_ok ThreadInit.entryL 0
      (fun s σ c he hn hdc hpc hA hD hJ => hW TI.entry s σ c he hn hdc hpc hA hD.1.1 hJ.2)
    dsimp only [tiNP, tiB, tiN] at hJ ⊢
    obtain ⟨-, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := ThreadInit.tiCall_walk lab _ hJ
    refine .inl ⟨TI.call, h1.symm, ?_, rfl, ⟨rfl, h2, h3⟩, ?_⟩
    · rw [ThreadInit.tiCall_run]; rfl
    · rw [ThreadInit.tiCall_run]
      simp only [ofInt_bmod]
      rw [eSp, show Int64.ofNat (4 * 2) = 8 from rfl, Int64.toBitVec_add,
        show ∀ y : Int, y + 4 + 4 = y + 8 from fun y => by omega, BitVec.ofInt_add,
        Spike.Lib.int64_ofInt_toInt]; rfl
  case call =>
    cases b
    case true => exact seg_falseW.mono_pre fun _ _ ⟨_, _, _, _, _, _, _, h, _⟩ => absurd h (by decide)
    refine seg_fixW true ((call_nd_FWP (KC := True) (nC := tiN lab q .call) (lo' := -208) (hi' := 0) (M := StackM rS)
      (P := P) (Ne := fun g => takeNG lab (tiTake q g) false .e)
      (Ex := fun g => takeXG lab (tiTake q g) true)
      hR hal hFt0 (by show R.lo ≤ -48 + -208; omega) (by decide) (by show (-48 : Int) < R.hi; omega) (by decide)
      (by show (-48 : Int) % 16 = 0; decide) (by decide) (by decide)
      (fun _ => TakeK.kstable fun m pm ⟨hD, _⟩ => ⟨hFt m pm hD, fun _ => stackM_takeMem⟩)
      (fun _ s s' hk _ k hk' _ => by obtain ⟨pm, he⟩ := hk.mem; rw [he]; exact loadInt_takeMem (hRS k hk'))
      (fun m h hM => ⟨⟨h.1, fun _ => hM⟩, nofun⟩)
      (fun R' F' hR' hal' hlo' hhi' hF' hK' hFF' hR'e hCC g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, h30⟩, ⟨-, -, -, h30', -⟩⟩ := hg'
        exact (stack_take_segW hp hend hF' hR' hal' hlo' hhi' (fun m h => hFF m (hFF' m h).1) (tiTake q g') hk htk
          (P := P) (FStable.callee hR (show R.lo ≤ -48 + -208 by omega) (by decide) (show (-48 : Int) < R.hi by omega)
            (show (-48 : Int) + 0 ≤ R.hi by omega) hP)
          (fun i => (hW TI.call g' (h30'.symm.trans h30) i).mono fun m h => ⟨(hFF' m h).1, hCC m h⟩) hRS' hfit hout'
          (takeMem_of_kstable (hK' trivial) exe endPc)).mono_post
          fun s c ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM⟩, hJ⟩ => ⟨x, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hM⟩)
      (fun _ => rfl) ?_ ?_).mono_pre
        fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ⟨he, hn, hdc, hpc, σ, hA, ⟨hD.1, hD.2 rfl⟩, hJ.2⟩)
    · rintro σC c ⟨⟨rfl, -, h0⟩, -⟩
      exact ⟨⟨σC.regs.SP.toBitVec, σC.regs.X29.toBitVec, σC.regs.X30.toBitVec⟩, rfl, rfl, rfl, rfl, rfl, h0⟩
    · rintro g x σC c σx c' σR ⟨⟨-, hfr, -⟩, h30⟩ ⟨-, hsp', -, h30', -⟩ ⟨-, rfl, hPost⟩ hregs - hslot
      obtain ⟨hsp, h16, h8, h48⟩ := hfr
      have hk' : ∀ k : Int, k % 8 = 0 → -48 ≤ k → k ≤ -8 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
        hslot k ⟨h1, by omega, by omega⟩ fun h => by
          simp only [Region.Off, Region.callee] at h; dsimp only [tiNG, tiN] at h; omega
      refine .inl ⟨TI.sp, ?_, rfl, rfl, rfl, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · show lab ThreadInit.spL = Int64.ofBitVec g.ra
        rw [← h30']
        show lab _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [h30, int64_ofBitVec_toBitVec]
      · show σR.regs.SP.toBitVec = _
        rw [hregs, hPost.1, ← hsp']; exact hsp
      · rw [hk' (-16) (by decide) (by decide) (by decide)]; exact h16
      · rw [hk' (-8) (by decide) (by decide) (by decide)]; exact h8
      · rw [hk' (-48) (by decide) (by decide) (by decide)]; exact h48
      · show σR.regs.X0.toBitVec = _
        rw [hregs]; exact hPost.2.2.2
  case sp =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiSp ThreadInit.tiSp_ok ThreadInit.spL 0 (fun s σ c he hn hdc hpc hA hD hJ => blkW_tiS (hW TI.sp) s σ c he hn hdc hpc hA hD.1 hJ)
    dsimp only [tiNG, tiA, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ, h0⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiSp_walk lab _ hJ h0
    exact .inl ⟨TI.st0, by rw [h1]; rfl, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st0 =>
    refine seg_fixW b ?_
    have hc : blockAt SccCode.ret0Prog ThreadInit.spL (11 + 3 * 0) [strDir .X9 .X10 0] = true :=
      (show parseAArch64("str x9, [x10]") = [strDir .X9 .X10 0] by decide) ▸ hin'.1.1.1.1.1.1.1.1.1.1.1.2
    refine rtst_ndW (code_of hp hend hc rfl) (nodeW_mono (F := takeF F rS b) (nodeW_tiS (hW TI.st0)) fun m h => h.1) fun m σ c _ hD hJ => ?_
    dsimp only [tiNG, tiA, tiN] at hJ
    obtain ⟨rfl, rfl, hJ, h9, h10⟩ := hJ
    have hfi := hfld (8 * 0, q.tcb) (by simp [ThreadInit.fields])
    rw [rAddr_x10 h10, show BitVec.ofInt 64 (Int64.toInt 0) = BitVec.ofNat 64 (8 * 0) by decide,
      getRegOrZr_x9, h9]
    exact ⟨hfi.rt, hfi.mp, hfi.G, hfi.unmapped m (hFFb m hD), q.c0, .refl q.c0,
      .inl ⟨TI.f1, (ofNat4_succ' _ _).symm, rfl, rfl, rfl, hJ⟩⟩
  case f1 =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiF1 ThreadInit.tiF1_ok ThreadInit.spL 12 (fun s σ c he hn hdc hpc hA hD hJ => blkW_tiS (hW TI.f1) s σ c he hn hdc hpc hA hD.1 hJ)
    dsimp only [tiNG, tiA, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF1_walk lab _ hJ
    exact .inl ⟨TI.st1, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st1 =>
    refine seg_fixW b ?_
    have hc : blockAt SccCode.ret0Prog ThreadInit.spL (11 + 3 * 1) [strDir .X9 .X10 8] = true :=
      (show parseAArch64("str x9, [x10, #8]") = [strDir .X9 .X10 8] by decide) ▸ hin'.1.1.1.1.1.1.1.1.1.2
    refine rtst_ndW (code_of hp hend hc rfl) (nodeW_mono (F := takeF F rS b) (nodeW_tiS (hW TI.st1)) fun m h => h.1) fun m σ c _ hD hJ => ?_
    dsimp only [tiNG, tiA, tiN] at hJ
    obtain ⟨rfl, rfl, hJ, h9, h10⟩ := hJ
    have hfi := hfld (8 * 1, tiBase (_root_.Executable.labels exe).label q + 4096#64) (by simp [ThreadInit.fields])
    rw [rAddr_x10 h10, show BitVec.ofInt 64 (Int64.toInt 8) = BitVec.ofNat 64 (8 * 1) by decide,
      getRegOrZr_x9, h9]
    exact ⟨hfi.rt, hfi.mp, hfi.G, hfi.unmapped m (hFFb m hD), q.c0, .refl q.c0,
      .inl ⟨TI.f2, (ofNat4_succ' _ _).symm, rfl, rfl, rfl, hJ⟩⟩
  case f2 =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiF2 ThreadInit.tiF2_ok ThreadInit.spL 15 (fun s σ c he hn hdc hpc hA hD hJ => blkW_tiS (hW TI.f2) s σ c he hn hdc hpc hA hD.1 hJ)
    dsimp only [tiNG, tiA, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF2_walk lab _ hJ
    exact .inl ⟨TI.st2, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st2 =>
    refine seg_fixW b ?_
    have hc : blockAt SccCode.ret0Prog ThreadInit.spL (11 + 3 * 2) [strDir .X9 .X10 16] = true :=
      (show parseAArch64("str x9, [x10, #16]") = [strDir .X9 .X10 16] by decide) ▸ hin'.1.1.1.1.1.1.1.2
    refine rtst_ndW (code_of hp hend hc rfl) (nodeW_mono (F := takeF F rS b) (nodeW_tiS (hW TI.st2)) fun m h => h.1) fun m σ c _ hD hJ => ?_
    dsimp only [tiNG, tiA, tiN] at hJ
    obtain ⟨rfl, rfl, hJ, h9, h10⟩ := hJ
    have hfi := hfld (8 * 2, 0#64) (by simp [ThreadInit.fields])
    rw [rAddr_x10 h10, show BitVec.ofInt 64 (Int64.toInt 16) = BitVec.ofNat 64 (8 * 2) by decide,
      getRegOrZr_x9, h9]
    exact ⟨hfi.rt, hfi.mp, hfi.G, hfi.unmapped m (hFFb m hD), q.c0, .refl q.c0,
      .inl ⟨TI.f3, (ofNat4_succ' _ _).symm, rfl, rfl, rfl, hJ⟩⟩
  case f3 =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiF3 ThreadInit.tiF3_ok ThreadInit.spL 18 (fun s σ c he hn hdc hpc hA hD hJ => blkW_tiS (hW TI.f3) s σ c he hn hdc hpc hA hD.1 hJ)
    dsimp only [tiNG, tiA, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF3_walk lab _ hJ
    exact .inl ⟨TI.st3, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st3 =>
    refine seg_fixW b ?_
    have hc : blockAt SccCode.ret0Prog ThreadInit.spL (11 + 3 * 3) [strDir .X9 .X10 24] = true :=
      (show parseAArch64("str x9, [x10, #24]") = [strDir .X9 .X10 24] by decide) ▸ hin'.1.1.1.1.1.2
    refine rtst_ndW (code_of hp hend hc rfl) (nodeW_mono (F := takeF F rS b) (nodeW_tiS (hW TI.st3)) fun m h => h.1) fun m σ c _ hD hJ => ?_
    dsimp only [tiNG, tiA, tiN] at hJ
    obtain ⟨rfl, rfl, hJ, h9, h10⟩ := hJ
    have hfi := hfld (8 * 3, 0#64) (by simp [ThreadInit.fields])
    rw [rAddr_x10 h10, show BitVec.ofInt 64 (Int64.toInt 24) = BitVec.ofNat 64 (8 * 3) by decide,
      getRegOrZr_x9, h9]
    exact ⟨hfi.rt, hfi.mp, hfi.G, hfi.unmapped m (hFFb m hD), q.c0, .refl q.c0,
      .inl ⟨TI.f4, (ofNat4_succ' _ _).symm, rfl, rfl, rfl, hJ⟩⟩
  case f4 =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiF4 ThreadInit.tiF4_ok ThreadInit.spL 21 (fun s σ c he hn hdc hpc hA hD hJ => blkW_tiS (hW TI.f4) s σ c he hn hdc hpc hA hD.1 hJ)
    dsimp only [tiNG, tiA, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF4_walk lab _ hJ
    exact .inl ⟨TI.st4, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st4 =>
    refine seg_fixW b ?_
    have hc : blockAt SccCode.ret0Prog ThreadInit.spL (11 + 3 * 4) [strDir .X9 .X10 32] = true :=
      (show parseAArch64("str x9, [x10, #32]") = [strDir .X9 .X10 32] by decide) ▸ hin'.1.1.1.2
    refine rtst_ndW (code_of hp hend hc rfl) (nodeW_mono (F := takeF F rS b) (nodeW_tiS (hW TI.st4)) fun m h => h.1) fun m σ c _ hD hJ => ?_
    dsimp only [tiNG, tiA, tiN] at hJ
    obtain ⟨rfl, rfl, hJ, h9, h10⟩ := hJ
    have hfi := hfld (8 * 4, tiBase (_root_.Executable.labels exe).label q) (by simp [ThreadInit.fields])
    rw [rAddr_x10 h10, show BitVec.ofInt 64 (Int64.toInt 32) = BitVec.ofNat 64 (8 * 4) by decide,
      getRegOrZr_x9, h9]
    exact ⟨hfi.rt, hfi.mp, hfi.G, hfi.unmapped m (hFFb m hD), q.c0, .refl q.c0,
      .inl ⟨TI.f5, (ofNat4_succ' _ _).symm, rfl, rfl, rfl, hJ⟩⟩
  case f5 =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiF5 ThreadInit.tiF5_ok ThreadInit.spL 24 (fun s σ c he hn hdc hpc hA hD hJ => blkW_tiS (hW TI.f5) s σ c he hn hdc hpc hA hD.1 hJ)
    dsimp only [tiNG, tiA, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF5_walk lab _ hJ
    exact .inl ⟨TI.st5, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st5 =>
    refine seg_fixW b ?_
    have hc : blockAt SccCode.ret0Prog ThreadInit.spL (11 + 3 * 5) [strDir .X9 .X10 40] = true :=
      (show parseAArch64("str x9, [x10, #40]") = [strDir .X9 .X10 40] by decide) ▸ hin'.1.2
    refine rtst_ndW (code_of hp hend hc rfl) (nodeW_mono (F := takeF F rS b) (nodeW_tiS (hW TI.st5)) fun m h => h.1) fun m σ c _ hD hJ => ?_
    dsimp only [tiNG, tiA, tiN] at hJ
    obtain ⟨rfl, rfl, hJ, h9, h10⟩ := hJ
    have hfi := hfld (8 * 5, tiBase (_root_.Executable.labels exe).label q + 16384#64) (by simp [ThreadInit.fields])
    rw [rAddr_x10 h10, show BitVec.ofInt 64 (Int64.toInt 40) = BitVec.ofNat 64 (8 * 5) by decide,
      getRegOrZr_x9, h9]
    exact ⟨hfi.rt, hfi.mp, hfi.G, hfi.unmapped m (hFFb m hD), q.c0, .refl q.c0,
      .inl ⟨TI.ret, (ofNat4_succ' _ _).symm, rfl, rfl, rfl, hJ⟩⟩
  case ret =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiRet ThreadInit.tiRet_ok ThreadInit.spL 27 (fun s σ c he hn hdc hpc hA hD hJ => blkW_tiS (hW TI.ret) s σ c he hn hdc hpc hA hD.1 hJ)
    dsimp only [tiNG, tiA, tiN, tiXG, tiX] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := ThreadInit.tiRet_walk lab _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, rfl, h3⟩

end TiWProof

/-! ## `scc_rt_start` from `.sp2` on: `scc_rt_thread_init` and the stack switch -/

/-- `.sp2`'s block: the TCB saved at `[sp, #16]`, the call of `scc_rt_thread_init`. -/
def startCall2 : List Directive := parseAArch64("str x0, [sp, #16]
ldr x0, [sp, #16]
bl scc_rt_thread_init")

/-- `.sp3`'s block: the top saved at `[sp, #24]`, `x9` the top, `x10` and `x0` the TCB. -/
def startSw0 : List Directive := parseAArch64("str x0, [sp, #24]
ldr x9, [sp, #24]
ldr x10, [sp, #16]
ldr x0, [sp, #16]")

/-- After the switch: `x29 = 0`, the call of `scc_rt_main`. -/
def startMain : List Directive := parseAArch64("movz x29, #0
bl scc_rt_main")

block_spec startCall2 (-48) 0 Abort.oI startCall2
block_spec startSw0 (-48) 0 Abort.oI startSw0
block_spec startMain (-80) 0 SO.entry startMain

/-- `.sp2`'s label. -/
abbrev sp2L : Label := ".L0_scc_rt_start.sp2"
/-- `.sp3`'s label. -/
abbrev sp3L : Label := ".L0_scc_rt_start.sp3"

/-- **`scc_rt_start`'s tail in `prog`**: `.sp2`'s block, `.sp3` right after
it, `.sp3`'s block, `msr tpidr_el0, x10`, the switch `add sp, x9, #0` and the
call of `scc_rt_main`. -/
def startTailIn (prog : List Directive) : Bool :=
  blockAt prog sp2L 0 startCall2 && labelGap prog sp2L sp3L 3 && blockAt prog sp3L 0 startSw0 &&
  blockAt prog sp3L 4 [(SI.msr .X10).toDir] && blockAt prog sp3L 5 [swDir .X9] && blockAt prog sp3L 6 startMain

theorem ret0_startTailIn : startTailIn SccCode.ret0Prog = true := by decide +kernel

/-- **The switch's step**: `sp` takes `x9`; `x0` and the thread pointer are kept. -/
theorem swStep (o : SO) (fall : Int64) (σ : AS) :
    (AI.step o fall (.reg .W64 (.ADD_e (.low .SP .W64) (.low (.reg .X9) .W64) (.imm ⟨.int64 0, .S0⟩))) σ).regs.SP.toBitVec =
      σ.regs.X9.toBitVec ∧
    (AI.step o fall (.reg .W64 (.ADD_e (.low .SP .W64) (.low (.reg .X9) .W64) (.imm ⟨.int64 0, .S0⟩))) σ).regs.X0 =
      σ.regs.X0 ∧
    (AI.step o fall (.reg .W64 (.ADD_e (.low .SP .W64) (.low (.reg .X9) .W64) (.imm ⟨.int64 0, .S0⟩))) σ).regs.TPIDR_EL0 =
      σ.regs.TPIDR_EL0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  simp [AI.step, regRes, Operation.interp, RegOnly, MachineData.setRegOrSp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64,
    Reg64s.getRegOrSp, Reg64s.getRegOrSp64, ExtOrImmReg.interp, ConstExpr.interp, RegOrSp.base, Reg64s.getXReg]

/-- **The frame condition after the switch** to the region based at `v`:
`v` is the new stack's top and the limit word `a` is not thread-private
memory. -/
def swF (top a v : BitVec 64) (m : MachineData) : Prop := v = top ∧ Mem.loadInt m.dmem a 8 = none

/-- No write inside the new region breaks it, when the limit word lies
outside the region below `top`. -/
theorem swF_stable {top a v : BitVec 64} (hfit : a.toNat + 8 ≤ 2 ^ 64)
    (hout : (a.toNat : Int) + 8 ≤ top.toNat + -80 ∨ (top.toNat : Int) + 0 ≤ a.toNat) :
    FStable (swR v (-80) 0) (swF top a v) := by
  rintro m m' ⟨rfl, h⟩ hd
  exact ⟨rfl, (hd a hfit hout).trans h⟩

section Tail

variable (lab : Label → Int64)

/-- **The call node of `scc_rt_thread_init`**: `x0` and `[sp, #16]` the
TCB, the return address `.sp3`. -/
def startNC2 (tcb : BitVec 64) (c0 : Ctl) : ND := ⟨lab ThreadInit.fnL, Abort.oI, fun σ c =>
  (c = c0 ∧ σ.regs.X0.toBitVec = tcb ∧ σ.slot (-32) = tcb) ∧ σ.regs.X30.toBitVec = (lab sp3L).toBitVec⟩

/-- **Back at `.sp3`**: `x0` the stack's top, `[sp, #16]` the TCB. -/
def startN3 (tcb top : BitVec 64) (c0 : Ctl) : ND := ⟨lab sp3L, Abort.oI, fun σ c =>
  c = c0 ∧ σ.regs.X0.toBitVec = top ∧ σ.slot (-32) = tcb⟩

/-- At `msr tpidr_el0, x10`; `x0` the TCB too (`scc_rt_main`'s argument). -/
def startN4 (tcb top : BitVec 64) (c0 : Ctl) : ND := ⟨lab sp3L + Int64.ofNat (4 * 4), Abort.oI, fun σ c =>
  c = c0 ∧ σ.regs.X9.toBitVec = top ∧ σ.regs.X10.toBitVec = tcb ∧ σ.regs.X0.toBitVec = tcb⟩

/-- At the switch `add sp, x9, #0`. -/
def startN5 (tcb top : BitVec 64) (c0 : Ctl) : ND := ⟨lab sp3L + Int64.ofNat (4 * 5), Abort.oI, fun σ c =>
  c = c0 ∧ σ.regs.X9.toBitVec = top ∧ σ.regs.TPIDR_EL0 = UInt64.ofBitVec tcb ∧ σ.regs.X0.toBitVec = tcb⟩

/-- **After the switch**: `sp` the new stack's top, at offset 0 of the new region. -/
def startN6 (tcb top : BitVec 64) (c0 : Ctl) : ND := ⟨lab sp3L + Int64.ofNat (4 * 6), SO.entry, fun σ c =>
  c = c0 ∧ σ.regs.SP.toBitVec = top ∧ σ.regs.TPIDR_EL0 = UInt64.ofBitVec tcb ∧ σ.regs.X0.toBitVec = tcb⟩

end Tail

section TailProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **From the switch on**: `add sp, x9, #0` moves to the region based at
the new stack's top `top`, `movz x29, #0; bl scc_rt_main`, then `main_seg`.
A segment to any fragment, given: `top` 16-aligned and its region of 80
bytes not wrapping, the new stack's cells holding a slot file in the
memory at the switch (`hmap`: the stack is the thread's private memory
by then), the limit word `[tcb, #8]` outside the new region (`hfit`,
`hout`) and its facts for both frames (`hlimM`, `hlimW`), and that the
final `exit_group(42)` off an abort site is `main`'s exit (`hexit`). -/
theorem start_switch_seg (hp : Lays exe SccCode.ret0Prog) (hend : endPc = endOf exe SccCode.ret0Prog)
    (hK : ms.K = some Scc.Sem.A64.abi) (tcb top : BitVec 64) (c0 : Ctl)
    (h16 : top.toNat % 16 = 0) (hok : (swR top (-80) 0).OK)
    (hmap : ∀ m, F m → ∃ sl : Int → BitVec 64, ∀ k, (swR top (-80) 0).Off k →
      ∃ j, Mem.loadInt m.dmem ((swR top (-80) 0).addr k) 8 = some j ∧ BitVec.ofInt 64 j = sl k)
    (hfit : (limA (UInt64.ofBitVec tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec tcb)).toNat : Int) + 8 ≤ top.toNat + -80 ∨
      (top.toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec tcb)).toNat)
    (hlimM : LimOk ms F exe endPc (limA (UInt64.ofBitVec tcb)) (top - (48 : Int64).toBitVec))
    (hlimW : LimOk ms F exe endPc (limA (UInt64.ofBitVec tcb)) (top - (48 : Int64).toBitVec - (32 : Int64).toBitVec))
    (hexit : ∀ R' F' s, At exe endPc R' F' (mainNX (_root_.Executable.labels exe).label) s c0 → ¬ ms.abortAt s →
      MainExit p ms s c0 42)
    {Q : Frag isaLSE2} :
    Seg p lbl ms (At exe endPc R F (startN5 (_root_.Executable.labels exe).label tcb top c0)) Q := by
  let lab := (_root_.Executable.labels exe).label
  have hin := ret0_startTailIn
  simp only [startTailIn, Bool.and_eq_true] at hin
  let a := limA (UInt64.ofBitVec tcb)
  refine sw_seq (lo := -80) (hi := 0) (F' := swF top a) (n' := startN6 lab tcb top c0)
    (sw_nd rfl (code_of hp hend hin.1.2 rfl) (ofNat4_succ' _ 5).symm rfl fun m σ c _ hD hJ => ?_) fun v hv hR => ?_
  · obtain ⟨rfl, h9, htp, hx0⟩ := hJ
    obtain ⟨hsp, hx, htp'⟩ := swStep (startN5 lab tcb top c).o ((startN5 lab tcb top c).pc + Int64.ofNat 4) σ
    rw [hsp, h9]
    obtain ⟨sl, hsl⟩ := hmap m hD
    exact ⟨h16, hok, ⟨rfl, hlimM.unmapped m hD⟩, sl, hsl, c, .refl c, rfl, hsp.trans h9, htp'.trans htp,
      (congrArg _ hx).trans hx0⟩
  · let g : MainG := ⟨top, UInt64.ofBitVec tcb, c0⟩
    have hF2 : FStable (swR v (-80) 0) (swF top a v) := swF_stable hfit hout
    refine Seg.seq (Q := At exe endPc (swR v (-80) 0) (swF top a v) (mainN0 lab g))
      (seg_one (seg_nd (by simp [startMain]) startMain_ok hF2 hR hv (Int.le_refl _) (Int.le_refl _)
        (code_of hp hend hin.2 rfl) fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩))
      (main_seg hp hend hK hF2 hR hv (Int.le_refl _) (Int.le_refl _) g
        ⟨hlimM.rt, hlimM.mp, fun _ h => h.2, hlimM.room⟩
        ⟨hlimW.rt, hlimW.mp, fun _ h => h.2, hlimW.room⟩ fun s hAt => hexit _ _ s hAt)
    · dsimp only [startN6, mainN0]; rw [startMain_run]
    · dsimp only [startN6, mainN0]; rw [startMain_run]; rfl
    · dsimp only [startN6, mainN0] at hJ ⊢; rw [startMain_run]
      obtain ⟨rfl, hsp, htp, -⟩ := hJ
      refine ⟨rfl, ?_, ?_⟩ <;> simp_all [setXReg_TPIDR, Reg64s.setXReg_SP] <;> rfl

/-- **`scc_rt_start` from `.sp2` to the switch**: `.sp2`'s block, the call
of `scc_rt_thread_init` through `call_nd_F` with `thread_init_seg` (the TCB
at `[sp, #16]` kept across it), `.sp3`'s block and `msr tpidr_el0, x10`. The
TCB is `scc_rt_pinned + n0 + 8`, the stack's top `scc_rt_stacks + k0 +
16384`; the callee's premises are `thread_init_seg`'s at those values. -/
theorem start_sp2_sw_seg (hp : Lays exe SccCode.ret0Prog) (hend : endPc = endOf exe SccCode.ret0Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi)
    (n0 k0 : BitVec 64) (c0 : Ctl) (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F exe endPc (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0) :
    Seg p lbl ms (At exe endPc R F (startN2 (_root_.Executable.labels exe).label n0 c0))
      (At exe endPc R F (startN5 (_root_.Executable.labels exe).label
        (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0)) := by
  let lab := (_root_.Executable.labels exe).label
  let tcb := pinA lab + n0 + 8#64
  let top := stacksA lab + k0 + 16384#64
  have hin := ret0_startTailIn
  simp only [startTailIn, Bool.and_eq_true] at hin
  have esp3 := label_labelGap hp hin.1.1.1.1.2
  have hlo48 : R.lo ≤ -48 := by omega
  refine Seg.seq (Q := At exe endPc R F (startNC2 lab tcb c0)) ?_
    (Seg.seq (Q := At exe endPc R F (startN3 lab tcb top c0)) ?_
      (Seg.seq (Q := At exe endPc R F (startN4 lab tcb top c0)) ?_ ?_))
  · -- `.sp2`'s block
    refine seg_one (seg_nd (by simp [startCall2]) startCall2_ok hF hR hal hlo48 hhi
      (code_of hp hend hin.1.1.1.1.1 (ofNat4_zero _)) fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
    · dsimp only [startN2, startNC2]; rw [startCall2_run]
    · dsimp only [startN2, startNC2]; rw [startCall2_run]; rfl
    · dsimp only [startN2, startNC2] at hJ ⊢; rw [startCall2_run]
      obtain ⟨rfl, h0⟩ := hJ
      refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
      · simp [Spike.Lib.upd_apply, h0, Spike.Lib.int64_ofInt_toInt]; try rfl
      · simp [Spike.Lib.upd_apply, h0]; try rfl
      · simp only [ofInt_bmod]
        rw [show lab sp3L = _ from esp3, show Int64.ofNat (4 * 3) = 12 from rfl, Int64.toBitVec_add,
          show ∀ y : Int, y + 4 + 4 + 4 = y + 12 from fun y => by omega, BitVec.ofInt_add,
          Spike.Lib.int64_ofInt_toInt]; rfl
  · -- `scc_rt_thread_init`
    refine seg_one (call_nd_F (lo' := -256) (hi' := 0) (Ne := fun g => tiN lab ⟨g, tcb, k0, c0⟩ .e)
      (Ex := fun g => tiX lab ⟨g, tcb, k0, c0⟩)
      hR hal hF (by show R.lo ≤ -48 + -256; omega) (by decide) (by show (-48 : Int) < R.hi; omega) (by decide)
      (by show (-48 : Int) % 16 = 0; decide) (by decide) (by decide)
      (fun R' F' hR' hal' hlo' hhi' hF' hFF g' =>
        thread_init_seg hp hend hF' hR' hal' hlo' hhi' hFF ⟨g', tcb, k0, c0⟩ hk hfld htk)
      (fun _ => rfl) ?_ ?_)
    · rintro σC c ⟨⟨rfl, h0, -⟩, -⟩
      exact ⟨⟨σC.regs.SP.toBitVec, σC.regs.X29.toBitVec, σC.regs.X30.toBitVec⟩, rfl, rfl, rfl, rfl, rfl, h0⟩
    · rintro g x σC c σx c' σR ⟨⟨-, -, h32⟩, h30⟩ ⟨-, -, -, h30', -⟩ ⟨rfl, hPost⟩ hregs - hslot
      refine .inl ⟨(), ?_, rfl, rfl, ?_, ?_⟩
      · show lab sp3L = Int64.ofBitVec g.ra
        rw [← h30']
        show lab _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [h30, int64_ofBitVec_toBitVec]
      · show σR.regs.X0.toBitVec = _
        rw [hregs]; exact hPost.2.2.2
      · rw [hslot (-32) ⟨by decide, by omega, by omega⟩ fun h => by
          simp only [Region.Off, Region.callee] at h; dsimp only [startNC2] at h; omega]
        exact h32
  · -- `.sp3`'s block
    refine seg_one (seg_nd (by simp [startSw0]) startSw0_ok hF hR hal hlo48 hhi
      (code_of hp hend hin.1.1.1.2 (ofNat4_zero _)) fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
    · dsimp only [startN3, startN4]; rw [startSw0_run]; simp only [Int64.add_assoc]; rfl
    · dsimp only [startN3, startN4]; rw [startSw0_run]; rfl
    · dsimp only [startN3, startN4] at hJ ⊢; rw [startSw0_run]
      obtain ⟨rfl, h0, h32⟩ := hJ
      refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp [Spike.Lib.upd_apply, h0, h32]
  · -- `msr tpidr_el0, x10`
    refine seg_one (si_nd (si := .msr .X10) hF (code_of hp hend hin.1.1.2 rfl) fun σ c hJ =>
      ⟨c, .refl c, .inl ⟨(), (ofNat4_succ' _ 4).symm, rfl, ?_⟩⟩)
    obtain ⟨rfl, h9, h10, hx0⟩ := hJ
    refine ⟨rfl, h9, ?_, hx0⟩
    show UInt64.ofBitVec (σ.regs.getRegOrZr (.low (.reg .X10) .W64)) = _
    rw [Spike.Lib.A64.Alloc.getRegOrZr_x]; exact congrArg UInt64.ofBitVec h10

/-- **`scc_rt_start` never returns**: in any valid layout of `ret0Prog`,
from its entry, a segment to any fragment. The chain is S1, the call of
`scc_rt_alloc_tcb`, the call of `scc_rt_thread_init` (with
`scc_rt_stack_take` nested), the switch to the new stack and `scc_rt_main`.
The own words on entry are `scc_rt_pinned_next = n0` and
`scc_rt_stack_next = k0`. The premises are those of the parts: the
memory-side facts (`hhdr`, `hfld`, `hmap`, `hlimM`, `hlimW`), `main`'s
exit (`hexit`), the arithmetic ones (`hn`, `hk`, `h16`, `hok`, `hfit`, `hout`) and the
own-word accesses' (`htcb`, `htk`; their `own…` fields are named until
`ms.own` is wired). -/
theorem start_seg (hp : Lays exe SccCode.ret0Prog) (hend : endPc = endOf exe SccCode.ret0Prog)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (n0 k0 : BitVec 64) (c0 : Ctl)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F exe endPc (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F exe endPc n0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F exe endPc (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0)
    (h16 : (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat % 16 = 0)
    (hok : (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).OK)
    (hmap : ∀ m, F m → ∃ sl : Int → BitVec 64,
      ∀ k, (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).Off k →
        ∃ j, Mem.loadInt m.dmem ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).addr k)
          8 = some j ∧ BitVec.ofInt 64 j = sl k)
    (hfit : (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat + -80 ∨
      ((stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat : Int) + 0 ≤
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat)
    (hlimM : LimOk ms F exe endPc (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - (48 : Int64).toBitVec))
    (hlimW : LimOk ms F exe endPc (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - (48 : Int64).toBitVec - (32 : Int64).toBitVec))
    (hexit : ∀ R' F' s, At exe endPc R' F' (mainNX (_root_.Executable.labels exe).label) s c0 → ¬ ms.abortAt s →
      MainExit p ms s c0 42)
    {Q : Frag isaLSE2} :
    Seg p lbl ms (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0)) Q :=
  (start_sp2_seg hp hend hK hF hR hal (by omega) hhi n0 c0 hn hhdr htcb).seq
    ((start_sp2_sw_seg hp hend hF hR hal hlo hhi n0 k0 c0 hk hfld htk).seq
      (start_switch_seg hp hend hK _ _ c0 h16 hok hmap hfit hout hlimM hlimW hexit))

end TailProof

/-! ## `wc_main` and `scc_rt_main` inside `W` -/

/-- `wc_main`'s entry registers: `wcN0` without the limit word's facts. -/
def wcJ0 (g : WcG) (σ : AS) (c : Ctl) : Prop :=
  c = g.c0 ∧ σ.regs.X29.toBitVec = g.fp ∧ σ.regs.X30.toBitVec = g.ra ∧ σ.regs.SP.toBitVec = g.sp ∧
    σ.regs.TPIDR_EL0 = g.tp

/-- **`wc_main`'s states inside `W`**, none moved by `K`: its prologue's and
its body's. -/
structure WcW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isaLSE2) (g : WcG) : Prop where
  pro : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "wc_main") 32 8 ".L18_wc_main.stack_grow" []
    (wcJ0 g)
  body : WcBodyW W K exe endPc R F (wcN1 (_root_.Executable.labels exe).label g).J

/-- **`scc_rt_main`'s states inside `W`**, none moved by `K`: its prologue's,
the call block's, `wc_main`'s in the callee's region (for every ghost with
the caller's source control and thread pointer, the caller's cells outside
it holding values) and the `exit_group` tail's. -/
structure MainW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isaLSE2) (g : MainG) : Prop where
  pro : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_main") 48 8
    ".L1_scc_rt_main.stack_grow" [(.X0, 0)] (mainN0 (_root_.Executable.labels exe).label g).J
  call : BlkW W K exe endPc R F (mainN1 (_root_.Executable.labels exe).label g) mainCall
  wc : ∀ g', g'.ra = ((_root_.Executable.labels exe).label ".L1_scc_rt_main.0_entry" + 4).toBitVec →
    g'.c0 = g.c0 → g'.tp = g.tp →
      WcW W K exe endPc (R.callee (-48) (-32) 0) (fun m => F m ∧ CallerCells R (-48) (-32) 0 m) ms g'
  exit : ExitW W K exe endPc R F (mainNR (_root_.Executable.labels exe).label g) 8

section MainWProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F F0 : MachineData → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- A prologue's obligations under a weaker frame condition hold under a stronger one. -/
theorem proW_mono {W : Frag isaLSE2} {K : State → State → Prop} {F' : MachineData → Prop} {ms' : MemSide isaLSE2}
    {pc0 Z lim : Int64} {L : Label} {ps : List (XReg × Int64)} {J : AS → Ctl → Prop}
    (h : ProW W K exe endPc R F ms' pc0 Z lim L ps J) (hFF : ∀ m, F' m → F m) :
    ProW W K exe endPc R F' ms' pc0 Z lim L ps J :=
  ⟨blkW_mono h.w0 hFF, nodeW_mono h.w1 hFF, blkW_mono h.w2 hFF, blkW_mono h.w3 hFF⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- `wc_main`'s obligations under a weaker frame condition hold under a stronger one. -/
theorem WcW.mono {W : Frag isaLSE2} {K : State → State → Prop} {F' : MachineData → Prop} {g : WcG}
    (h : WcW W K exe endPc R F ms g) (hFF : ∀ m, F' m → F m) : WcW W K exe endPc R F' ms g :=
  ⟨proW_mono h.pro hFF, ⟨blkW_mono h.body.w0 hFF, blkW_mono h.body.w1 hFF⟩⟩

/-- **`wc_main` is one segment inside `W`** (`wc_seg`, its states' obligations
`hW`). -/
theorem wc_segW {W : Frag isaLSE2} {K : State → State → Prop} (hp : Lays exe SccCode.ret0Prog)
    (hend : endPc = endOf exe SccCode.ret0Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -32) (hhi : 0 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (g : WcG) (hW : WcW W K exe endPc R F ms g) :
    SegW W K p lbl ms (At exe endPc R F (wcN0 ms F0 exe endPc (_root_.Executable.labels exe).label g))
      (At exe endPc R F (wcNx g)) := by
  let lab := (_root_.Executable.labels exe).label
  refine SegW.of_imp (P := At exe endPc R F ⟨lab "wc_main", ⟨0, []⟩, wcJ0 g⟩)
      (L := LimOk ms F0 exe endPc (limA g.tp) (g.sp - (32 : Int64).toBitVec))
      (fun hlim0 => ?_) |>.mono_pre ?_
  · have hlim := hlim0.mono hFF
    refine SegW.seq (ret0_wc_prologue_segW hp hend (nb := wcN1 lab g) hF hR hal hlo hhi rfl wcBody_le hW.pro ?_)
      (ret0_wc_body_segW hp hend hF hR hal hlo hhi rfl hW.body ?_ ?_)
    · rintro σ c ⟨rfl, h29, h30, hsp, htp⟩
      rw [tcbA_limA htp]
      refine ⟨hlim.rt, hlim.mp, hlim.unmapped, fun v hv => ⟨?_, fun σ' _ hs => ⟨rfl, ?_, ?_⟩⟩⟩
      · rw [hsp]; exact hlim.room v hv
      · rw [hs]; simp [stSlots, frSlot, Spike.Lib.upd_apply, h29]
      · rw [hs]; simp [stSlots, frSlot, Spike.Lib.upd_apply, h30]
    · rintro σ c ⟨-, -, h8⟩
      simp [wcNx, h8]
    · rintro σ c ⟨rfl, h16, h8⟩ σ' - h0 h29 h30
      exact ⟨rfl, h0, h29.trans h16, h30.trans h8⟩
  · rintro s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ, hL⟩
    exact ⟨⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hL⟩

/-- **`scc_rt_main` does not return, inside `W`** (`main_seg`, its states'
obligations `hW`). The call of `wc_main` asks no closure under `K` of it
(`call_nd_FWK` with `KC := False`): no outside move is in it. -/
theorem main_segW {W : Frag isaLSE2} {K : State → State → Prop} (hp : Lays exe SccCode.ret0Prog)
    (hend : endPc = endOf exe SccCode.ret0Prog)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) (g : MainG)
    (hlimM : LimOk ms F exe endPc (limA g.tp) (g.sp0 - (48 : Int64).toBitVec))
    (hlimW : LimOk ms F exe endPc (limA g.tp) (g.sp0 - (48 : Int64).toBitVec - (32 : Int64).toBitVec))
    (hexit : ∀ s, At exe endPc R F (mainNX (_root_.Executable.labels exe).label) s g.c0 → ¬ ms.abortAt s →
      MainExit p ms s g.c0 42)
    (hW : MainW W K exe endPc R F ms g)
    {Q : Frag isaLSE2} :
    SegW W K p lbl ms (At exe endPc R F (mainN0 (_root_.Executable.labels exe).label g)) Q := by
  let lab := (_root_.Executable.labels exe).label
  have hin := ret0_mainIn
  simp only [mainIn, Bool.and_eq_true] at hin
  have esp0 := label_labelGap hp hin.2
  have hlo48 : R.lo ≤ -48 := by omega
  refine SegW.seq (ret0_main_prologue_segW hp hend (nb := mainN1 lab g) hF hR hal hlo48 hhi rfl
    (by show SO.le ⟨-48, []⟩ (oFr 48) = true; decide) hW.pro ?_)
    (SegW.seq (Q := At exe endPc R F (mainNC lab g)) ?_
      (SegW.seq (Q := At exe endPc R F (mainNR lab g)) ?_
        (ret0_main_exit_segW hp hend rfl rfl hK hF hR hal hlo48 hhi hW.exit fun s c σ0 hJ hAt => ?_)))
  · -- the prologue
    rintro σ c ⟨rfl, hsp, htp⟩
    rw [tcbA_limA htp]
    refine ⟨hlimM.rt, hlimM.mp, hlimM.unmapped, fun v hv => ⟨?_, fun σ' hr _ => ⟨rfl, ?_, ?_⟩⟩⟩
    · rw [hsp]; exact hlimM.room v hv
    · rw [hr]; simp [frRegs, ldStep, chkRegs, hsp]
    · rw [hr]; simp [frRegs, ldStep, chkRegs, setXReg_TPIDR, htp]
  · -- `bl wc_main`
    refine seg_oneW (seg_ndW (by simp [mainCall]) mainCall_ok hF hR hal hlo48 hhi
      (code_of hp hend hin.1 (ofNat4_zero _)) hW.call fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
    · dsimp only [mainN1, mainNC]; rw [mainCall_run]
    · dsimp only [mainN1, mainNC]; rw [mainCall_run]; rfl
    · dsimp only [mainN1, mainNC] at hJ ⊢; rw [mainCall_run]
      obtain ⟨rfl, hsp, htp⟩ := hJ
      refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩ <;> simp_all [Spike.Lib.int64_ofInt_toInt]
      rw [ofInt_bmod, BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt]; rfl
  · -- the call
    refine seg_oneW (call_nd_FWK (KC := False) (lo' := -32) (hi' := 0) (M := fun _ => True)
      (Ne := wcN0 ms F exe endPc lab) (Ex := fun g _ => wcNx g)
      hR hal hF (by show R.lo ≤ -48 + -32; omega) (by decide) (by show (-48 : Int) < R.hi; omega) (by decide)
      (by show (-48 : Int) % 16 = 0; decide) (by decide) (by decide) (fun h => h.elim) (fun h => h.elim)
      (fun _ h _ => h)
      (fun R' F' hR' hal' hlo' hhi' hF' _ hFF hR'e hcc g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨⟨hc, -, htp⟩, h30⟩, ⟨⟨hc', -, h30', -, htp'⟩, -⟩⟩ := hg'
        exact (wc_segW hp hend hF' hR' hal' hlo' hhi' hFF g'
          ((hW.wc g' (h30'.symm.trans h30) (hc'.symm.trans hc) (htp'.symm.trans htp)).mono
            fun m h => ⟨hFF m h, hcc m h⟩)).mono_post
          fun _ _ h => ⟨(), h, trivial⟩)
      (fun _ => rfl) ?_ ?_)
    · rintro σC c ⟨⟨rfl, hsp, htp⟩, h30⟩
      refine ⟨⟨σC.regs.X29.toBitVec, σC.regs.X30.toBitVec, σC.regs.SP.toBitVec, g.tp, g.c0⟩, rfl,
        ⟨rfl, rfl, rfl, rfl, htp⟩, ?_⟩
      show LimOk ms F exe endPc (limA g.tp) (σC.regs.SP.toBitVec - (32 : Int64).toBitVec)
      rw [hsp]; exact hlimW
    · rintro g' x σC c σx c' σR ⟨⟨rfl, -, -⟩, h30⟩ ⟨⟨hc, -, h30', -⟩, -⟩ ⟨hc', h42, -, -⟩ hreg - -
      refine .inl ⟨(), ?_, rfl, ⟨hc'.trans hc.symm, ?_⟩⟩
      · show lab ".L1_scc_rt_main.sp0" = Int64.ofBitVec g'.ra
        rw [← h30']
        show lab _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [h30, int64_ofBitVec_toBitVec]; exact esp0
      · show σR.regs.X0.toBitVec = 42#64
        rw [hreg]; exact h42
  · -- the exit: `exit_group(42)`
    obtain ⟨rfl, h42⟩ := hJ
    have h : σ0.regs.X0.toNat = 42 := by
      rw [show σ0.regs.X0.toNat = σ0.regs.X0.toBitVec.toNat from rfl, h42]; rfl
    rw [h]
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩ := hAt
    exact SysOk.exitGroup_main
      (hexit s ⟨he, hn, hdc, hpc, σ, hA, hD, by show σ.regs.X0.toBitVec = _; rw [hx]; exact h42⟩)

end MainWProof

/-! ## `scc_rt_start`'s tail inside `W`, the take its outside move -/

/-- **The stack range off a region is in private memory**: every aligned
word of `rS` outside `R` reads (`StackM` but for `R`'s cells, which `Abs`
gives). -/
def StackOff (rS : Scc.Sem.Range) (R : Region) (m : MachineData) : Prop :=
  ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
    ((a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a) →
    (Mem.loadInt m.dmem (BitVec.ofNat 64 a) 8).isSome

theorem StackM.off {rS : Scc.Sem.Range} {R : Region} {m : MachineData} (h : StackM rS m) : StackOff rS R m :=
  fun a h8 ha ha7 _ => h a h8 ha ha7

/-- No write inside `R` breaks `StackOff rS R`. -/
theorem stackOff_stable {rS : Scc.Sem.Range} {R : Region} (hfit : rS.lo + rS.size ≤ 2 ^ 64) :
    FStable R (StackOff rS R) := by
  intro m m' hm hd a h8 ha ha7 hoff
  have hlt : a < 2 ^ 64 := by simp only [Scc.Sem.Range.contains] at ha7; omega
  have hn : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [hd (BitVec.ofNat 64 a) (by rw [hn]; simp only [Scc.Sem.Range.contains] at ha7; omega) (by rw [hn]; exact hoff)]
  exact hm a h8 ha ha7 hoff

/-- **The frame condition after the switch**: `swF`, and the stack range
off the new region in private memory. -/
def swFS (rS : Scc.Sem.Range) (top a v : BitVec 64) (m : MachineData) : Prop :=
  swF top a v m ∧ StackOff rS (swR v (-80) 0) m

/-- **The switch's and `scc_rt_main`'s states inside `W`**, none moved by
`K`: the switch, the block after it and `scc_rt_main`'s, in the new region
(for every value of the new `sp`). -/
structure SwW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isaLSE2) (rS : Scc.Sem.Range) (tcb top : BitVec 64)
    (c0 : Ctl) : Prop where
  sw : NodeW W K exe endPc R F (startN5 (_root_.Executable.labels exe).label tcb top c0)
  blk : ∀ v, BlkW W K exe endPc (swR v (-80) 0) (swFS rS top (limA (UInt64.ofBitVec tcb)) v)
    (startN6 (_root_.Executable.labels exe).label tcb top c0) startMain
  main : ∀ v, MainW W K exe endPc (swR v (-80) 0) (swFS rS top (limA (UInt64.ofBitVec tcb)) v) ms
    ⟨top, UInt64.ofBitVec tcb, c0⟩

/-- **`scc_rt_start` from `.sp2` to the switch: its states inside `W`**,
none moved by `K`: `.sp2`'s block, `scc_rt_thread_init`'s in the callee's
region (for every ghost), `.sp3`'s block and the `msr`, the last two with
the stack range in private memory; `scc_rt_thread_init`'s take site at
frame condition `P` too (`True` by default). -/
structure Sp2W (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (rS : Scc.Sem.Range) (n0 k0 : BitVec 64) (c0 : Ctl)
    (P : MachineData → Prop := fun _ => True) : Prop where
  b2 : BlkW W K exe endPc R F (startN2 (_root_.Executable.labels exe).label n0 c0) startCall2
  ti : ∀ g, g.ra = ((_root_.Executable.labels exe).label sp3L).toBitVec → ∀ i,
    TiW W K exe endPc (R.callee Abort.oI.sp (-256) 0) F (StackM rS)
    ⟨g, pinA (_root_.Executable.labels exe).label + n0 + 8#64, k0, c0⟩ i P
  b3 : BlkW W K exe endPc R (fun m => F m ∧ StackM rS m)
    (startN3 (_root_.Executable.labels exe).label (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0) startSw0
  msr : NodeW W K exe endPc R (fun m => F m ∧ StackM rS m)
    (startN4 (_root_.Executable.labels exe).label (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0)

/-- **`scc_rt_start` up to `.sp2`: its states inside `W`**, none moved by
`K`: S1's, the call block's and `scc_rt_alloc_tcb`'s in the callee's region
(for every ghost). -/
structure Sp0W (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (n0 : BitVec 64) (c0 : Ctl) : Prop where
  start : StartW W K exe endPc R F (startN0 (_root_.Executable.labels exe).label c0).J
  blk : BlkW W K exe endPc R F (startN1 (_root_.Executable.labels exe).label c0) startCall
  tcb : ∀ g, g.ra = ((_root_.Executable.labels exe).label ".L0_scc_rt_start.sp2").toBitVec → ∀ i,
    TcbW W K exe endPc (R.callee Abort.oI.sp (-192) 0) F ⟨g, n0, c0⟩ i

/-- **`scc_rt_start`'s states inside `W`**, none moved by `K`: up to `.sp2`,
from `.sp2` to the switch, and from the switch on (with the stack range in
private memory). -/
structure StartAllW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isaLSE2) (rS : Scc.Sem.Range) (n0 k0 : BitVec 64)
    (c0 : Ctl) : Prop where
  s1 : Sp0W W K exe endPc R F n0 c0
  s2 : Sp2W W K exe endPc R F rS n0 k0 c0
  s3 : SwW W K exe endPc R (fun m => F m ∧ StackM rS m) ms rS
    (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
    (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0

section TailWProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

omit [Kraken.Executable.ValidLayout exe] in
theorem TiW.mono {W : Frag isaLSE2} {K : State → State → Prop} {F' M P : MachineData → Prop} {q : TiG} {i : TI}
    (h : TiW W K exe endPc R F M q i P) (hFF : ∀ m, F' m → F m) : TiW W K exe endPc R F' M q i P := by
  cases i <;> dsimp only [TiW] at h ⊢
  all_goals first
    | exact blkW_mono h hFF
    | exact nodeW_mono h hFF
    | exact blkW_mono h fun m h => ⟨hFF m h.1, h.2⟩
    | exact nodeW_mono h fun m h => ⟨hFF m h.1, h.2⟩
    | exact fun g hg i => (h g hg i).mono fun m h => ⟨hFF m h.1, h.2⟩

/-- **From the switch on, inside `W`** (`start_switch_seg`, its states'
obligations `hW`). The new stack's cells hold values at the switch since
the stack range is in private memory then (`hFS`) and the new region lies
in it (`hsub`), so `hmap` is not asked; after the switch the frame keeps the
range off the new region (`swFS`). -/
theorem start_switch_segW {W : Frag isaLSE2} {K : State → State → Prop} {rS : Scc.Sem.Range}
    (hp : Lays exe SccCode.ret0Prog) (hend : endPc = endOf exe SccCode.ret0Prog)
    (hK : ms.K = some Scc.Sem.A64.abi) (tcb top : BitVec 64) (c0 : Ctl)
    (h16 : top.toNat % 16 = 0) (hok : (swR top (-80) 0).OK)
    (hFS : ∀ m, F m → StackM rS m) (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (hsub : ∀ k, (swR top (-80) 0).Off k → ((swR top (-80) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR top (-80) 0).addr k).toNat ∧ rS.contains (((swR top (-80) 0).addr k).toNat + 7))
    (hfit : (limA (UInt64.ofBitVec tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec tcb)).toNat : Int) + 8 ≤ top.toNat + -80 ∨
      (top.toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec tcb)).toNat)
    (hlimM : LimOk ms F exe endPc (limA (UInt64.ofBitVec tcb)) (top - (48 : Int64).toBitVec))
    (hlimW : LimOk ms F exe endPc (limA (UInt64.ofBitVec tcb)) (top - (48 : Int64).toBitVec - (32 : Int64).toBitVec))
    (hexit : ∀ R' F' s, At exe endPc R' F' (mainNX (_root_.Executable.labels exe).label) s c0 → ¬ ms.abortAt s →
      MainExit p ms s c0 42)
    (hW : SwW W K exe endPc R F ms rS tcb top c0)
    {Q : Frag isaLSE2} :
    SegW W K p lbl ms (At exe endPc R F (startN5 (_root_.Executable.labels exe).label tcb top c0)) Q := by
  let lab := (_root_.Executable.labels exe).label
  have hin := ret0_startTailIn
  simp only [startTailIn, Bool.and_eq_true] at hin
  let a := limA (UInt64.ofBitVec tcb)
  have hmap : ∀ m, F m → ∃ sl : Int → BitVec 64, ∀ k, (swR top (-80) 0).Off k →
      ∃ j, Mem.loadInt m.dmem ((swR top (-80) 0).addr k) 8 = some j ∧ BitVec.ofInt 64 j = sl k := by
    intro m hD
    refine ⟨fun k => BitVec.ofInt 64 ((Mem.loadInt m.dmem ((swR top (-80) 0).addr k) 8).getD 0), fun k hk => ?_⟩
    obtain ⟨h8, ha, ha7⟩ := hsub k hk
    have h := hFS m hD _ h8 ha ha7
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp h
    exact ⟨j, hj, by simp only [hj, Option.getD_some]⟩
  refine sw_seqW (lo := -80) (hi := 0) (F' := swFS rS top a) (n' := startN6 lab tcb top c0)
    (sw_ndW rfl (code_of hp hend hin.1.2 rfl) (ofNat4_succ' _ 5).symm rfl hW.sw fun m σ c _ hD hJ => ?_)
    fun v hv hR => ?_
  · obtain ⟨rfl, h9, htp, hx0⟩ := hJ
    obtain ⟨hsp, hx, htp'⟩ := swStep (startN5 lab tcb top c).o ((startN5 lab tcb top c).pc + Int64.ofNat 4) σ
    rw [hsp, h9]
    obtain ⟨sl, hsl⟩ := hmap m hD
    exact ⟨h16, hok, ⟨⟨rfl, hlimM.unmapped m hD⟩, (hFS m hD).off⟩, sl, hsl, c, .refl c, rfl, hsp.trans h9,
      htp'.trans htp, (congrArg _ hx).trans hx0⟩
  · let g : MainG := ⟨top, UInt64.ofBitVec tcb, c0⟩
    have hF2 : FStable (swR v (-80) 0) (swFS rS top a v) := fun m m' h hd =>
      ⟨swF_stable hfit hout m m' h.1 hd, stackOff_stable hfitS m m' h.2 hd⟩
    refine SegW.seq (Q := At exe endPc (swR v (-80) 0) (swFS rS top a v) (mainN0 lab g))
      (seg_oneW (seg_ndW (by simp [startMain]) startMain_ok hF2 hR hv (Int.le_refl _) (Int.le_refl _)
        (code_of hp hend hin.2 rfl) (hW.blk v) fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩))
      (main_segW hp hend hK hF2 hR hv (Int.le_refl _) (Int.le_refl _) g
        ⟨hlimM.rt, hlimM.mp, fun _ h => h.1.2, hlimM.room⟩
        ⟨hlimW.rt, hlimW.mp, fun _ h => h.1.2, hlimW.room⟩ (fun s hAt => hexit _ _ s hAt)
        (hW.main v))
    · dsimp only [startN6, mainN0]; rw [startMain_run]
    · dsimp only [startN6, mainN0]; rw [startMain_run]; rfl
    · dsimp only [startN6, mainN0] at hJ ⊢; rw [startMain_run]
      obtain ⟨rfl, hsp, htp, -⟩ := hJ
      refine ⟨rfl, ?_, ?_⟩ <;> simp_all [setXReg_TPIDR, Reg64s.setXReg_SP] <;> rfl

/-- **`scc_rt_start` from `.sp2` to the switch, inside `W`, the take its
outside move** (`start_sp2_sw_seg`, its states' obligations `hW`, with
`thread_init_segW` at the call): at the switch the stack range `rS` is in
private memory (`StackM`). Given the take's facts at the region (`hRS`,
`hfit`, `hout`, `hFt`). -/
theorem start_sp2_sw_segW {W : Frag isaLSE2} {rS : Scc.Sem.Range} (hp : Lays exe SccCode.ret0Prog)
    (hend : endPc = endOf exe SccCode.ret0Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi)
    (n0 k0 : BitVec 64) (c0 : Ctl) (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F exe endPc (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0)
    (hW : Sp2W W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F rS n0 k0 c0)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (startN2 (_root_.Executable.labels exe).label n0 c0))
      (At exe endPc R (fun m => F m ∧ StackM rS m) (startN5 (_root_.Executable.labels exe).label
        (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0)) := by
  let lab := (_root_.Executable.labels exe).label
  let tcb := pinA lab + n0 + 8#64
  let top := stacksA lab + k0 + 16384#64
  have hin := ret0_startTailIn
  simp only [startTailIn, Bool.and_eq_true] at hin
  have esp3 := label_labelGap hp hin.1.1.1.1.2
  have hlo48 : R.lo ≤ -48 := by omega
  have hSM := stackM_stable hfit hout
  have hF2 : FStable R (fun m => F m ∧ StackM rS m) := fun m m' h hd => ⟨hF m m' h.1 hd, hSM m m' h.2 hd⟩
  -- `scc_rt_thread_init`'s region, and `rS` off it
  have hb' := Region.callee_base (hi' := 0) hR (show R.lo ≤ -48 + -256 by omega) (by decide)
    (show (-48 : Int) < R.hi by omega)
  have hRS' : ∀ k, (R.callee (-48) (-256) 0).Off k → ∀ i < 8,
      (R.callee (-48) (-256) 0).addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS := fun k hk i hi => by
    rw [Region.callee_addr]
    exact hRS _ (Region.callee_off (show R.lo ≤ -48 + -256 by omega) (show (-48 : Int) + 0 ≤ R.hi by omega)
      (by decide) hk) i hi
  have hout' : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ (R.callee (-48) (-256) 0).base.toNat + (R.callee (-48) (-256) 0).lo ∨
        ((R.callee (-48) (-256) 0).base.toNat : Int) + (R.callee (-48) (-256) 0).hi ≤ a := fun a h8 ha ha7 => by
    show (a : Int) + 8 ≤ ((R.callee (-48) (-256) 0).base.toNat : Int) + -256 ∨
      ((R.callee (-48) (-256) 0).base.toNat : Int) + 0 ≤ a
    rcases hout a h8 ha ha7 with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)
  refine SegW.seq (Q := At exe endPc R F (startNC2 lab tcb c0)) ?_
    (SegW.seq (Q := At exe endPc R (fun m => F m ∧ StackM rS m) (startN3 lab tcb top c0)) ?_
      (SegW.seq (Q := At exe endPc R (fun m => F m ∧ StackM rS m) (startN4 lab tcb top c0)) ?_ ?_))
  · -- `.sp2`'s block
    refine seg_oneW (seg_ndW (by simp [startCall2]) startCall2_ok hF hR hal hlo48 hhi
      (code_of hp hend hin.1.1.1.1.1 (ofNat4_zero _)) hW.b2 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
    · dsimp only [startN2, startNC2]; rw [startCall2_run]
    · dsimp only [startN2, startNC2]; rw [startCall2_run]; rfl
    · dsimp only [startN2, startNC2] at hJ ⊢; rw [startCall2_run]
      obtain ⟨rfl, h0⟩ := hJ
      refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
      · simp [Spike.Lib.upd_apply, h0, Spike.Lib.int64_ofInt_toInt]; try rfl
      · simp [Spike.Lib.upd_apply, h0]; try rfl
      · simp only [ofInt_bmod]
        rw [show lab sp3L = _ from esp3, show Int64.ofNat (4 * 3) = 12 from rfl, Int64.toBitVec_add,
          show ∀ y : Int, y + 4 + 4 + 4 = y + 12 from fun y => by omega, BitVec.ofInt_add,
          Spike.Lib.int64_ofInt_toInt]; rfl
  · -- `scc_rt_thread_init`
    refine seg_oneW (call_nd_FW (lo' := -256) (hi' := 0) (M := StackM rS)
      (Ne := fun g => tiN lab ⟨g, tcb, k0, c0⟩ .e) (Ex := fun g => tiX lab ⟨g, tcb, k0, c0⟩)
      hR hal hF (by show R.lo ≤ -48 + -256; omega) (by decide) (by show (-48 : Int) < R.hi; omega) (by decide)
      (by show (-48 : Int) % 16 = 0; decide) (by decide) (by decide)
      (TakeK.kstable hFt)
      (fun s s' hk _ k hk' _ => by obtain ⟨pm, he⟩ := hk.mem; rw [he]; exact loadInt_takeMem (hRS k hk'))
      (fun m h hM => ⟨h, hM⟩)
      (fun R' F' hR' hal' hlo' hhi' hF' hK' hFF' hR'e _ g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, h30⟩, ⟨-, -, -, h30', -⟩⟩ := hg'
        exact ((thread_init_segW hp hend hF' hR' hal' hlo' hhi' hFF' ⟨g', tcb, k0, c0⟩ hk hfld htk
          (P := fun _ => True) (fun _ _ h _ => h)
          (fun i => (hW.ti g' (h30'.symm.trans h30) i).mono hFF') hRS' hfit hout'
          (takeMem_of_kstable hK' exe endPc)).mono_pre fun _ _ h => ⟨h, trivial⟩).mono_post
          fun s c ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM⟩, hJ⟩ => ⟨x, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hM⟩)
      (fun _ => rfl) ?_ ?_)
    · rintro σC c ⟨⟨rfl, h0, -⟩, -⟩
      exact ⟨⟨σC.regs.SP.toBitVec, σC.regs.X29.toBitVec, σC.regs.X30.toBitVec⟩, rfl, rfl, rfl, rfl, rfl, h0⟩
    · rintro g x σC c σx c' σR ⟨⟨-, -, h32⟩, h30⟩ ⟨-, -, -, h30', -⟩ ⟨rfl, hPost⟩ hregs - hslot
      refine .inl ⟨(), ?_, rfl, rfl, ?_, ?_⟩
      · show lab sp3L = Int64.ofBitVec g.ra
        rw [← h30']
        show lab _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [h30, int64_ofBitVec_toBitVec]
      · show σR.regs.X0.toBitVec = _
        rw [hregs]; exact hPost.2.2.2
      · rw [hslot (-32) ⟨by decide, by omega, by omega⟩ fun h => by
          simp only [Region.Off, Region.callee] at h; dsimp only [startNC2] at h; omega]
        exact h32
  · -- `.sp3`'s block
    refine seg_oneW (seg_ndW (by simp [startSw0]) startSw0_ok hF2 hR hal hlo48 hhi
      (code_of hp hend hin.1.1.1.2 (ofNat4_zero _)) hW.b3 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
    · dsimp only [startN3, startN4]; rw [startSw0_run]; simp only [Int64.add_assoc]; rfl
    · dsimp only [startN3, startN4]; rw [startSw0_run]; rfl
    · dsimp only [startN3, startN4] at hJ ⊢; rw [startSw0_run]
      obtain ⟨rfl, h0, h32⟩ := hJ
      refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp [Spike.Lib.upd_apply, h0, h32]
  · -- `msr tpidr_el0, x10`
    refine seg_oneW (si_ndW (si := .msr .X10) hF2 (code_of hp hend hin.1.1.2 rfl) hW.msr fun σ c hJ =>
      ⟨c, .refl c, .inl ⟨(), (ofNat4_succ' _ 4).symm, rfl, ?_⟩⟩)
    obtain ⟨rfl, h9, h10, hx0⟩ := hJ
    refine ⟨rfl, h9, ?_, hx0⟩
    show UInt64.ofBitVec (σ.regs.getRegOrZr (.low (.reg .X10) .W64)) = _
    rw [Spike.Lib.A64.Alloc.getRegOrZr_x]; exact congrArg UInt64.ofBitVec h10

omit [Kraken.Executable.ValidLayout exe] in
theorem TcbW.mono {W : Frag isaLSE2} {K : State → State → Prop} {F' : MachineData → Prop} {q : TcbG} {i : TN}
    (h : TcbW W K exe endPc R F q i) (hFF : ∀ m, F' m → F m) : TcbW W K exe endPc R F' q i := by
  cases i <;> dsimp only [TcbW] at h ⊢
  all_goals first
    | exact blkW_mono h hFF
    | exact nodeW_mono h hFF

/-- **`scc_rt_start` up to `.sp2` inside `W`** (`start_sp2_seg`, its states'
obligations `hW`). The call of `scc_rt_alloc_tcb` asks no closure under `K`
of it (`call_nd_FWK` with `KC := False`): no outside move is in it. -/
theorem start_sp2_segW {W : Frag isaLSE2} {K : State → State → Prop} (hp : Lays exe SccCode.ret0Prog)
    (hend : endPc = endOf exe SccCode.ret0Prog)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -240) (hhi : 0 ≤ R.hi) (n0 : BitVec 64) (c0 : Ctl) (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F exe endPc (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F exe endPc n0) (hW : Sp0W W K exe endPc R F n0 c0) :
    SegW W K p lbl ms (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0))
      (At exe endPc R F (startN2 (_root_.Executable.labels exe).label n0 c0)) := by
  let lab := (_root_.Executable.labels exe).label
  have hin := ret0_startCallIn
  simp only [startCallIn, Bool.and_eq_true] at hin
  have esp2 := label_labelGap hp hin.2
  have hlo48 : R.lo ≤ -48 := by omega
  refine SegW.seq (ret0_start_segW hp hend hK hF hR hal hlo48 hhi (nC := startN1 lab c0) rfl rfl hW.start
      fun _ _ h => h)
    (SegW.seq (Q := At exe endPc R F (startNC lab c0)) ?_ ?_)
  · -- the call's block
    refine seg_oneW (seg_ndW (by simp [startCall]) startCall_ok hF hR hal hlo48 hhi
      (code_of hp hend hin.1 rfl) hW.blk fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
    · dsimp only [startN1, startNC]; rw [startCall_run]
    · dsimp only [startN1, startNC]; rw [startCall_run]; rfl
    · dsimp only [startN1, startNC] at hJ ⊢; rw [startCall_run]
      refine ⟨hJ, rfl, rfl, ?_⟩
      simp only [ofInt_bmod]
      rw [show lab ".L0_scc_rt_start.sp2" = _ from esp2,
        show Int64.ofNat (4 * 13) = Int64.ofNat (4 * 9) + 16 from rfl, ← Int64.add_assoc, Int64.toBitVec_add,
        show ∀ y : Int, y + 4 + 4 + 4 + 4 = y + 16 from fun y => by omega, BitVec.ofInt_add,
        Spike.Lib.int64_ofInt_toInt]; rfl
  · -- `scc_rt_alloc_tcb`
    refine seg_oneW (call_nd_FWK (KC := False) (lo' := -192) (hi' := 0) (M := fun _ => True)
      (Ne := fun g => tcbN lab ⟨g, n0, c0⟩ .e) (Ex := fun g => tcbX lab ⟨g, n0, c0⟩)
      hR hal hF (by show R.lo ≤ -48 + -192; omega) (by decide) (by show (-48 : Int) < R.hi; omega) (by decide)
      (by show (-48 : Int) % 16 = 0; decide) (by decide) (by decide) (fun h => h.elim) (fun h => h.elim)
      (fun _ h _ => h)
      (fun R' F' hR' hal' hlo' hhi' hF' _ hFF hR'e _ g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, -, -, h30⟩, ⟨-, -, -, h30', -⟩⟩ := hg'
        exact (alloc_tcb_segW hp hend hF' hR' hal' hlo' hhi' hFF ⟨g', n0, c0⟩ hn hhdr htcb
          fun i => (hW.tcb g' (h30'.symm.trans h30) i).mono hFF).mono_post fun _ _ ⟨x, h⟩ => ⟨x, h, trivial⟩)
      (fun _ => rfl) ?_ ?_)
    · rintro σC c ⟨rfl, h0, h1, -⟩
      exact ⟨⟨σC.regs.SP.toBitVec, σC.regs.X29.toBitVec, σC.regs.X30.toBitVec⟩, rfl,
        rfl, rfl, rfl, rfl, h0, h1⟩
    · rintro g x σC c σx c' σR ⟨-, -, -, h30⟩ ⟨-, -, -, h30', -⟩ ⟨rfl, hPost⟩ hregs - -
      refine .inl ⟨(), ?_, rfl, rfl, ?_⟩
      · show lab ".L0_scc_rt_start.sp2" = Int64.ofBitVec g.ra
        rw [← h30']
        show lab _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [h30, int64_ofBitVec_toBitVec]
      · show σR.regs.X0.toBitVec = _
        rw [hregs]; exact hPost.2.2.2

/-- **`scc_rt_start` never returns, inside `W`, the take its outside move**
(`start_seg`, its states' obligations `hW`): `start_sp2_segW`, then
`start_sp2_sw_segW` (the take nested, so at the switch the stack range `rS`
is in private memory), then `start_switch_segW`. `start_seg`'s `hmap` is
not asked: it follows from the take and the new region lying in `rS`
(`hsub`). The take's facts at the region: `hRS`, `hfitS`, `houtS`, `hFt`. -/
theorem start_segW {W : Frag isaLSE2} {rS : Scc.Sem.Range} (hp : Lays exe SccCode.ret0Prog)
    (hend : endPc = endOf exe SccCode.ret0Prog)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (n0 k0 : BitVec 64) (c0 : Ctl)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F exe endPc (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F exe endPc n0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F exe endPc (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0)
    (h16 : (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat % 16 = 0)
    (hok : (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).OK)
    (hsub : ∀ k, (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).Off k →
      ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).addr k).toNat + 7))
    (hfit : (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat + -80 ∨
      ((stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat : Int) + 0 ≤
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat)
    (hlimM : LimOk ms F exe endPc (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - (48 : Int64).toBitVec))
    (hlimW : LimOk ms F exe endPc (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - (48 : Int64).toBitVec - (32 : Int64).toBitVec))
    (hexit : ∀ R' F' s, At exe endPc R' F' (mainNX (_root_.Executable.labels exe).label) s c0 → ¬ ms.abortAt s →
      MainExit p ms s c0 42)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hW : StartAllW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F ms rS n0 k0 c0)
    {Q : Frag isaLSE2} :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0)) Q :=
  (start_sp2_segW hp hend hK hF hR hal (by omega) hhi n0 c0 hn hhdr htcb hW.s1).seq
    ((start_sp2_sw_segW hp hend hF hR hal hlo hhi n0 k0 c0 hk hfld htk hW.s2 hRS hfitS houtS hFt).seq
      (start_switch_segW hp hend hK _ _ c0 h16 hok (fun _ h => h.2) hfitS hsub hfit hout
        (hlimM.mono fun _ h => h.1) (hlimW.mono fun _ h => h.1) hexit hW.s3))

end TailWProof

/-! ## `_start` -/

/-- `_start`: the branch to `scc_rt_start`. -/
def entryB : List Directive := parseAArch64("b scc_rt_start")

block_spec entryB (0 : Int) (0 : Int) Abort.oE entryB

theorem ret0_entryIn : blockAt SccCode.ret0Prog "_start" 0 entryB = true := by decide +kernel

/-- `_start`'s node: the loaded thread's entry, the source control `c0`. -/
def entryN (lab : Label → Int64) (c0 : Ctl) : ND := ⟨lab "_start", Abort.oE, fun _ c => c = c0⟩

section EntryWProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`_start` inside `W`**: its branch, from the loaded thread's entry to
`scc_rt_start`'s, the block's states inside `W` and not moved by `K`
(`hW`). -/
theorem entry_segW {W : Frag isaLSE2} {K : State → State → Prop} (hp : Lays exe SccCode.ret0Prog)
    (hend : endPc = endOf exe SccCode.ret0Prog) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ 0) (hhi : 0 ≤ R.hi) (c0 : Ctl)
    (hW : BlkW W K exe endPc R F (entryN (_root_.Executable.labels exe).label c0) entryB) :
    SegW W K p lbl ms (At exe endPc R F (entryN (_root_.Executable.labels exe).label c0))
      (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0)) :=
  seg_oneW (seg_ndW (by simp [entryB]) entryB_ok hF hR hal hlo hhi
    (code_of hp hend ret0_entryIn (ofNat4_zero _)) hW fun σ c hJ => ⟨c, .refl c, .inl ⟨(), by
      dsimp only [entryN, startN0]; rw [entryB_run], by
      dsimp only [entryN, startN0]; rw [entryB_run]; exact (by decide : Abort.oE.le Abort.oE = true), by
      dsimp only [entryN, startN0] at hJ ⊢; exact hJ⟩⟩)

end EntryWProof

/-! ## Own words by pc

The own map the reshaped consumer interface will take is a function of the
pc only. That is sound for `ret0.w` because the main path visits each of its
pcs in a single phase: every function on it runs once. A pc off the main path
may map to anything, since the invariant only holds main-path states. -/

/-- **`pc` is one of the `n` instructions from label `L`.** -/
def PcIn (lab : Label → Int64) (L : Label) (n : Nat) (pc : Int64) : Prop :=
  ∃ k < n, pc = lab L + Int64.ofNat (4 * k)

/-- **The main path's pcs before the counter's add** (`AllocTcb.rmwPc`
included): `scc_rt_start` up to its call, and `scc_rt_alloc_tcb` up to and
including the add. -/
def PreRmw (lab : Label → Int64) (pc : Int64) : Prop :=
  PcIn lab "scc_rt_start" 4 pc ∨ PcIn lab startE 13 pc ∨ PcIn lab AllocTcb.fnL 6 pc ∨
    PcIn lab AllocTcb.entryL 5 pc ∨ PcIn lab AllocTcb.lenL 38 pc

open Classical in
/-- **`scc_rt_pinned_next`'s value by pc**: `n0` up to and including the
counter's add, `n0 + tcbLen` after it. -/
noncomputable def pnextOwn (lab : Label → Int64) (n0 : BitVec 64) (pc : Int64) : BitVec 64 :=
  if PreRmw lab pc then n0 else n0 + AllocTcb.tcbLen

/-! ## TODO: open premises

`start_seg` covers the whole main path. These premises stay open. They are
named hypotheses, never theorems:

- **The own words' values at their accesses** (`OwnAt`): `TcbOk.own`
  (`scc_rt_pinned_next = n0` at `rmwPc`) and `TakeOk.ownLock`,
  `ownFreeN`, `ownNext` (the lock `0` at `swpPc`, the free count `0` at
  `freeNPc`, `scc_rt_stack_next = k0` at `nextPc`). They are discharged
  once `ms.own` is the own map below.
- **The own map** for the stack words, besides `pnextOwn`:
  `scc_rt_stack_lock` (1 after `swpPc` up to and including `unlPc`, 0
  otherwise: at an access's pc the map gives the value before it), the
  class's `scc_rt_stack_free_n` (0), and `scc_rt_stack_next` (`k0` up to and
  including `nextPc`, `k0 + 16384` after it).
- **The new stack as private memory** (`hmap` of `start_switch_seg`): the
  whole-program proof gives the take site's move of the stack into the
  thread's private memory.
-/

/-- info: 'Spike.Lib.A64.Flow.Ret0.stack_take_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Ret0.stack_take_segW
/-- info: 'Spike.Lib.A64.Flow.Ret0.thread_init_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Ret0.thread_init_segW

end Spike.Lib.A64.Flow.Ret0
