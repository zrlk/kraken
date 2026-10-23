/-
**`ret0.w` on x64: the instance glue**, the x64 twin of
`Spike/Lib/A64Ret0.lean` (`Scc/DESIGN.md` §6, *Per-program instance glue*).
This file composes the runtime and program segments that exist
(`Spike/Lib/X64Ret0Segs.lean`, the S2–S4 specifications in
`Spike/Lib/X64Ret0AllocTcb.lean`, `Spike/Lib/X64Ret0StackTake.lean` and
`Spike/Lib/X64Ret0ThreadInit.lean`) into the whole functions of the main
path. It is hand-written and laid out as the
AArch64 file is: one section per function, one node per block or single
instruction, the same names.

The main path is `_start → scc_rt_start → {alloc_tcb, thread_init
(→ stack_take)} → arch_prctl → scc_rt_main → wc_main → exit_group`; this
file covers all of it (`start_seg`).

- **Calls** go through `call_nd_F` (`Spike/Lib/X64Call.lean`): the `call`
  pushes the return address (the callee's entry offsets are `⟨0, []⟩`, its
  return lands at `⟨8, []⟩`), and the callee may use the caller's frame
  condition. The return lands at offsets that know `%rsp` alone, so the node
  there fixes `%rbp` relative to `%rsp` and `At.rbp`
  (`Spike/Lib/X64RtNodes.lean`) puts its offset back.
- **The stack limit** (`limA`, `LimOk`): the facts a stack-checked prologue
  needs about `%fs:8`. The declarations agree at every address: a node's
  states have none (`At`).
- **`wc_main`** (`wc_seg`), **`scc_rt_main`** (`main_seg`), as on AArch64;
  `main_seg` takes `main`'s exit at its final `exit_group(42)` (`hexit`).
- **`scc_rt_alloc_tcb`** (`alloc_tcb_seg`): one callee segment over its
  nodes `tcbN`, one per block or single instruction. The header's store goes
  through `rtst_nd` and `StOk`; the counter's `lock xadd` through
  `ownXadd_nd` (`TcbOk`: the own word's value at the add, `OwnAt`, is a
  named hypothesis until `ms.own` is wired).
- **`scc_rt_start`** (`start_x0_seg`, `start_x0_x1_seg`, `start_x1_seg`,
  `start_x1_sw_seg`, `start_switch_seg`, `start_seg`): from its entry to
  `.x0` through the call of `scc_rt_alloc_tcb`, then to `.x1` through the
  call of `scc_rt_thread_init`, then `arch_prctl(ARCH_SET_FS, tcb)`
  (`archSetFs_nd`), the switch to the new stack (`sw_nd`, `sw_seq`,
  `Spike/Lib/X64Switch.lean`) and the call of `scc_rt_main`, which never
  returns (`call_nd_F` with no exits).
- **`scc_rt_stack_take`** (`stack_take_seg`): the lock's `xchg`
  (`ownXchg_nd`), the free count's load (`ownLd_nd`), the lock's release
  (`rtst_nd`) and the next offset's `lock xadd` (`ownXadd_nd`), their facts
  bundled in `TakeOk`. Inside `W` (`stack_take_segW`), the take site is the
  kernel's take of the stack range (`TakeK`, `take_ndW`), so at the return
  the range is in private memory (`StackM`).
- **`scc_rt_thread_init`** (`thread_init_seg`, the take nested through
  `call_nd_F`): the six TCB stores go through `rtst_nd` and `StOk`.
  Inside `W` (`thread_init_segW`), `stack_take_segW` nests through
  `call_nd_FW`, and the nodes after the call hold once the take is done
  (`tiNG`).
-/
import Spike.Lib.X64Ret0Segs
import Spike.Lib.X64Call
import Spike.Lib.X64RtNodes
import Spike.Lib.X64Ret0ThreadInit
import Spike.Lib.X64Flags
import Spike.Lib.SegCommon
import Spike.Lib.X64Switch

namespace Spike.Lib.X64.Flow.Ret0

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-- A node's invariant weakened. -/
theorem At.imp {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {n : ND}
    {J : AS → Ctl → Prop} {s : State} {c : Ctl} (h : At exe endPc R F n s c) (hJ : ∀ σ c, n.J σ c → J σ c) :
    At exe endPc R F ⟨n.pc, n.o, J⟩ s c :=
  let ⟨he, hn, hdc, hpc, σ, hA, hD, hJ'⟩ := h
  ⟨he, hn, hdc, hpc, σ, hA, hD, hJ σ c hJ'⟩

/-- **`%rbp` from its offset**: at a node whose offsets put `%rbp` at `k`,
the invariant may claim `%rbp` at `k - sp` bytes above `%rsp`. -/
theorem At.rbp_get {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {n : ND}
    {k : Int} {s : State} {c : Ctl} (hk : n.o.get .rbp = some k) (h : At exe endPc R F n s c) :
    At exe endPc R F ⟨n.pc, n.o, fun σ c =>
      n.J σ c ∧ σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (k - n.o.sp)⟩ s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
  refine ⟨he, hn, hdc, hpc, σ, hA, hD, hJ, ?_⟩
  rw [hA.so .rbp k hk, hA.so .rsp n.o.sp (SO.get_rsp _), ← Region.addr_add]; congr 1; omega

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} in
/-- A segment to the single node of `Next`. -/
theorem seg_one {P : Frag isa} {n : ND}
    (h : Seg p lbl ms P (Next exe endPc R F (fun _ : Unit => n) (fun e : Empty => e.elim))) :
    Seg p lbl ms P (At exe endPc R F n) :=
  h.mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} in
/-- A segment to the single node of `Next`, inside `W`. -/
theorem seg_oneW {W : Frag isa} {K : State → State → Prop} {P : Frag isa} {n : ND}
    (h : SegW W K p lbl ms P (Next exe endPc R F (fun _ : Unit => n) (fun e : Empty => e.elim))) :
    SegW W K p lbl ms P (At exe endPc R F n) :=
  h.mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim

/-! ## The stack limit -/

/-- **The stack-limit word** `%fs:8` for the thread pointer `tp`
(`Scc.IR.Tcb.stackLimit`). -/
def limA (tp : UInt64) : BitVec 64 := tp.toBitVec + (8 : Int64).toBitVec

/-- **What a stack-checked prologue needs of the limit word `a`** (the
memory-side facts, kept together): it is the runtime's, mapped for reading,
not thread-private memory under `F`, and every value runtime memory may hold
there is at most `Z`, the new frame's `%rsp`. -/
structure LimOk (ms : MemSide isa) (F : MachineData → Prop) (a Z : BitVec 64) : Prop where
  rt : ms.rt a.toNat
  mp : ms.mp ⟨a, 8⟩ false
  unmapped : ∀ m, F m → Mem.loadInt m.dmem a 8 = none
  room : ∀ v : Val, ms.G ⟨a, 8⟩ v → (v.setWidth 64).toNat ≤ Z.toNat

theorem LimOk.mono {ms : MemSide isa} {F F' : MachineData → Prop} {a Z : BitVec 64} (h : LimOk ms F a Z)
    (hFF : ∀ m, F' m → F m) : LimOk ms F' a Z :=
  ⟨h.rt, h.mp, fun m hm => h.unmapped m (hFF m hm), h.room⟩

/-! ## `wc_main` -/

/-- **The ghosts of a call of `wc_main`**: the caller's `%rbp`, the return
address, `%rsp` and the thread pointer at the call, the source control. -/
structure WcG where
  fp : BitVec 64
  ra : BitVec 64
  sp : BitVec 64
  tp : UInt64
  c0 : Ctl

section Wc

variable (ms : MemSide isa) (F : MachineData → Prop) (lab : Label → Int64)

/-- **`wc_main`'s entry**: the ghosts' registers and return address, and the
limit word's facts for its frame of 16 (`F` the caller's frame condition). -/
def wcN0 (g : WcG) : ND := ⟨lab "wc_main", ⟨0, []⟩, fun σ c =>
  (c = g.c0 ∧ σ.regs.rbp.toBitVec = g.fp ∧ σ.slot 0 = g.ra ∧ σ.regs.rsp.toBitVec = g.sp ∧
    σ.regs.fsBase = g.tp) ∧ LimOk ms F (limA g.tp) (g.sp - 8#64 - (16 : Int64).toBitVec)⟩

/-- `wc_main`'s body entry: the saved `%rbp` and the return address. -/
def wcN1 (g : WcG) : ND := ⟨lab ".Lwc_main.entry", oB, fun σ c =>
  c = g.c0 ∧ σ.slot (-8) = g.fp ∧ σ.slot 0 = g.ra ∧ σ.regs.rbp.toBitVec = g.sp - 8#64⟩

/-- **`wc_main`'s return**: at the return address, `%rax = 42`, `%rbp`
restored, `%rsp` past the return address. -/
def wcNx (g : WcG) : ND := ⟨Int64.ofBitVec g.ra, ⟨8, []⟩, fun σ c =>
  c = g.c0 ∧ σ.regs.rax.toBitVec = 42#64 ∧ σ.regs.rbp.toBitVec = g.fp ∧ σ.regs.rsp.toBitVec = g.sp + 8#64⟩

end Wc

section WcProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F F0 : MachineData → Prop}

/-- **`wc_main` is one segment** in any valid layout of `ret0Cells`, for any
region holding its frame of 16 and its return address, and any frame
condition implying the one the limit word's facts are stated under. -/
theorem wc_seg (hp : Lays exe SccCode.ret0Cells) (hend : endPc = endOf exe SccCode.ret0Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (g : WcG) :
    Seg p lbl ms (At exe endPc R F (wcN0 ms F0 (_root_.Executable.labels exe).label g))
      (At exe endPc R F (wcNx g)) := by
  let lab := (_root_.Executable.labels exe).label
  refine Seg.of_imp (P := At exe endPc R F ⟨lab "wc_main", ⟨0, []⟩, fun σ c => c = g.c0 ∧
      σ.regs.rbp.toBitVec = g.fp ∧ σ.slot 0 = g.ra ∧ σ.regs.rsp.toBitVec = g.sp ∧ σ.regs.fsBase = g.tp⟩)
      (L := LimOk ms F0 (limA g.tp) (g.sp - 8#64 - (16 : Int64).toBitVec)) (fun hlim0 => ?_) |>.mono_pre ?_
  · have hlim := hlim0.mono hFF
    refine Seg.seq (ret0_wc_prologue_seg hp hend (nb := wcN1 lab g) hF hR hlo (by omega) rfl wcBody_le ?_)
      (ret0_wc_body_seg hp hend hF hR hlo hhi (by show SO.le ⟨8, []⟩ ⟨8, []⟩ = true; decide) ?_ ?_)
    · rintro σ c ⟨rfl, hfp, hra, hsp, htp⟩
      have ha : σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec = limA g.tp := by rw [limA, htp]
      rw [ha]
      refine ⟨hlim.rt, hlim.mp, hlim.unmapped, fun v hv => ⟨?_, fun σ' hr hs => ⟨rfl, ?_, ?_, ?_⟩⟩⟩
      · rw [hsp]; exact hlim.room v hv
      · rw [hs]; simp [xStSlots, xS1, upd_apply, hfp]
      · rw [hs]; simp [xStSlots, xS1, upd_apply, hra]
      · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, hsp]
    · rintro σ c ⟨-, -, h0, -⟩
      simp [wcNx, h0]
    · rintro σ c ⟨rfl, h8, -, hb⟩ σ' - h42 hb' hsp'
      refine ⟨rfl, h42, hb'.trans h8, ?_⟩
      rw [hsp', hb]; bv_omega
  · rintro s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ, hL⟩
    exact ⟨⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hL⟩

end WcProof

/-! ## `scc_rt_main` -/

/-- `scc_rt_main`'s body: the call of `wc_main`. -/
def mainCall : List (Directive × Nat) := (parse("call wc_main")).zip [5]

/-- `scc_rt_main`'s body offsets: `%rsp` at the frame's base, `%rbp` at the
saved `%rbp`. -/
abbrev oM : SO := ⟨-40, [(.rbp, -8)]⟩

block_spec mainCall (-48) 0 oM mainCall

/-- **`scc_rt_main`'s call in `cells`**: `call wc_main` at `.entry`, `.x2`
right after it. -/
def mainIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells ".Lscc_rt_main.entry" 0 mainCall && labelGapB cells ".Lscc_rt_main.entry" ".Lscc_rt_main.x2" 5

theorem ret0_mainIn : mainIn SccCode.ret0Cells = true := by decide +kernel

/-- **The ghosts of `scc_rt_main`'s run**: `%rsp` and the thread pointer at
its entry, the source control. -/
structure MainG where
  sp0 : BitVec 64
  tp : UInt64
  c0 : Ctl

section Main

variable (lab : Label → Int64)

/-- `scc_rt_main`'s entry. -/
def mainN0 (g : MainG) : ND := ⟨lab "scc_rt_main", ⟨0, []⟩, fun σ c =>
  c = g.c0 ∧ σ.regs.rsp.toBitVec = g.sp0 ∧ σ.regs.fsBase = g.tp⟩

/-- `scc_rt_main`'s body entry, the frame of 32 set up. -/
def mainN1 (g : MainG) : ND := ⟨lab ".Lscc_rt_main.entry", oM, fun σ c =>
  c = g.c0 ∧ σ.regs.rsp.toBitVec = g.sp0 - 8#64 - (32 : Int64).toBitVec ∧ σ.regs.fsBase = g.tp⟩

/-- The call node: at `wc_main`'s label, the return address `.x2` pushed. -/
def mainNC (g : MainG) : ND := ⟨lab "wc_main", ⟨-48, []⟩, fun σ c =>
  (c = g.c0 ∧ σ.regs.rsp.toBitVec = g.sp0 - 8#64 - (32 : Int64).toBitVec - 8#64 ∧ σ.regs.fsBase = g.tp) ∧
    σ.slot (-48) = (lab ".Lscc_rt_main.x2").toBitVec ∧
    σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (-8 - -48)⟩

/-- Back from `wc_main`, at `.x2`: `%rbp` at the saved `%rbp`, `%rax = 42`. -/
def mainNR (g : MainG) : ND := ⟨lab ".Lscc_rt_main.x2", ⟨-40, []⟩, fun σ c =>
  c = g.c0 ∧ σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (-8 - -40) ∧ σ.regs.rax.toBitVec = 42#64⟩

/-- The `exit_group` call of `scc_rt_main`'s tail (after its block of
three): `main`'s result `42` in `%rdi`, the status. -/
def mainNX : ND := ⟨lab ".Lscc_rt_main.x2" + Int64.ofNat 4 + Int64.ofNat 4 + Int64.ofNat 5, ⟨-40, [(.rbp, -8)]⟩,
  fun σ _ => σ.regs.rdi.toBitVec = 42#64⟩

end Main

section MainProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` does not return**: in any valid layout of `ret0Cells`,
from its entry (`%rsp` at offset 0 of a region holding its frame of 32, the
return address it pushes and `wc_main`'s frame) a segment to any fragment,
given the limit word's facts for both frames and that the final
`exit_group(42)` off an abort site is `main`'s exit (`hexit`). -/
theorem main_seg (hp : Lays exe SccCode.ret0Cells) (hend : endPc = endOf exe SccCode.ret0Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -72) (hhi : 0 ≤ R.hi) (g : MainG)
    (hlimM : LimOk ms F (limA g.tp) (g.sp0 - 8#64 - (32 : Int64).toBitVec))
    (hlimW : LimOk ms F (limA g.tp) (g.sp0 - 8#64 - (32 : Int64).toBitVec - 8#64 - 8#64 - (16 : Int64).toBitVec))
    (hexit : ∀ s, At exe endPc R F (mainNX (_root_.Executable.labels exe).label) s g.c0 → ¬ ms.abortAt s →
      MainExit p ms s g.c0 42)
    {Q : Frag isa} :
    Seg p lbl ms (At exe endPc R F (mainN0 (_root_.Executable.labels exe).label g)) Q := by
  let lab := (_root_.Executable.labels exe).label
  have hin := ret0_mainIn
  simp only [mainIn, Bool.and_eq_true] at hin
  have ex2 := label_labelGapB hp hin.2
  have hlo40 : R.lo ≤ -40 := by omega
  refine Seg.seq (ret0_main_prologue_seg hp hend (nb := mainN1 lab g) hF hR hlo40 hhi rfl
    (by show SO.le oM (oF 32) = true; decide) ?_)
    (Seg.seq (Q := At exe endPc R F (mainNC lab g)) ?_
      (Seg.seq (Q := At exe endPc R F (mainNR lab g)) ?_
        ((ret0_main_exit_seg hp hend (n := ⟨lab ".Lscc_rt_main.x2", ⟨-40, [(.rbp, -8)]⟩, (mainNR lab g).J⟩)
            rfl rfl hK hF hR hlo40 hhi fun s c σ0 hJ0 hs => ?_).mono_pre
          fun _ _ h => At.rbp h fun _ _ h => h.2.1)))
  · -- the prologue
    rintro σ c ⟨rfl, hsp, htp⟩
    have ha : σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec = limA g.tp := by rw [limA, htp]
    rw [ha]
    refine ⟨hlimM.rt, hlimM.mp, hlimM.unmapped, fun v hv => ⟨?_, fun σ' hr _ => ⟨rfl, ?_, ?_⟩⟩⟩
    · rw [hsp]; exact hlimM.room v hv
    · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, hsp]
    · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, htp]
  · -- `call wc_main`
    refine (seg_one (seg_nd (by simp [mainCall]) mainCall_ok hF hR (by omega) hhi
      (code_field hp hend hin.1 (ofNat_zero' _)) fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)).mono_pre
      fun _ _ h => At.rbp_get rfl h
    · dsimp only [mainN1, mainNC]; rw [mainCall_run]
    · dsimp only [mainN1, mainNC]; rw [mainCall_run]; rfl
    · dsimp only [mainN1, mainNC] at hJ ⊢; rw [mainCall_run]
      obtain ⟨⟨rfl, hsp, htp⟩, hb⟩ := hJ
      refine ⟨⟨rfl, ?_, ?_⟩, ?_, ?_⟩
      · simp [Reg64s.set64, hsp]
      · simp [Reg64s.set64, htp]
      · simp only [upd_apply, ↓reduceIte]
        rw [show lab ".Lscc_rt_main.x2" = _ from ex2]; rfl
      · simp only [Reg64s.get64, Reg64s.set64] at hb ⊢; rw [hb]; bv_omega
  · -- the call
    refine seg_one (call_nd_F (e0 := 0) (lo' := -24) (hi' := 8) (Ne := wcN0 ms F lab) (Ex := fun g _ => wcNx g)
      hR hF (by show R.lo ≤ -48 - 0 + -24; omega) (by decide) (by show (-48 : Int) - 0 < R.hi; omega)
      (by show (-48 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-48 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide)
      (fun R' F' hR' hlo' hhi' hF' hFF g' =>
        (wc_seg hp hend hF' hR' hlo' hhi' hFF g').mono_post fun _ _ h => ⟨(), h⟩)
      (fun _ => rfl) ?_ ?_)
    · rintro σC c ⟨⟨rfl, hsp, htp⟩, -, -⟩
      refine ⟨⟨σC.regs.rbp.toBitVec, σC.slot (-48 - 0 + 0), σC.regs.rsp.toBitVec, g.tp, g.c0⟩, rfl,
        ⟨rfl, rfl, rfl, rfl, htp⟩, ?_⟩
      show LimOk ms F (limA g.tp) (σC.regs.rsp.toBitVec - 8#64 - (16 : Int64).toBitVec)
      rw [hsp]; exact hlimW
    · rintro g' x σC c σx c' σR ⟨⟨rfl, -, -⟩, h48, hb⟩ ⟨⟨hc, hfp, hra, hsp, -⟩, -⟩ ⟨hc', h42, hb', hsp'⟩ hregs
        - - -
      refine .inl ⟨(), ?_, by show SO.le ⟨-40, []⟩ ⟨-48 - 0 + 8, []⟩ = true; decide, hc'.trans hc.symm, ?_,
        by rw [hregs]; exact h42⟩
      · show lab ".Lscc_rt_main.x2" = Int64.ofBitVec g'.ra
        rw [← hra]
        show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
        rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
      · show σR.regs.get64 .rbp = σR.regs.get64 .rsp + BitVec.ofInt 64 (-8 - -40)
        rw [hregs]
        simp only [Reg64s.get64] at hb ⊢
        rw [hb', hsp', ← hfp, ← hsp]
        show σC.regs.rbp.toBitVec = σC.regs.rsp.toBitVec + 8#64 + BitVec.ofInt 64 (-8 - -40)
        rw [hb]; bv_omega
  · -- the `exit_group(42)`
    obtain ⟨rfl, -, h42⟩ := hJ0
    have e : σ0.regs.rax.toNat = 42 := by
      show σ0.regs.rax.toBitVec.toNat = 42; rw [h42]; rfl
    rw [e]
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩ := hs
    exact SysOk.exitGroup_main
      (hexit s ⟨he, hn, hdc, hpc, σ, hA, hD, by show σ.regs.rdi.toBitVec = _; rw [hx]; exact h42⟩)

end MainProof

/-! ## `scc_rt_alloc_tcb` -/

/-- **The ghosts of a call of `scc_rt_alloc_tcb`**: `%rsp`, `%rbp` and the
return address at entry, the own word `scc_rt_pinned_next`'s value `n0` on
entry, the source control. -/
structure TcbG where
  g : AllocTcb.G
  n0 : BitVec 64
  c0 : Ctl

/-- **What a runtime store needs of its word `a`** (the memory-side facts,
kept together as `LimOk` is for loads): it is the runtime's, mapped for
writing, its memory may hold `v` there, and it is not thread-private memory
under `F`. -/
structure StOk (ms : MemSide isa) (F : MachineData → Prop) (a v : BitVec 64) : Prop where
  rt : ms.rt a.toNat
  mp : ms.mp ⟨a, 8⟩ true
  G : ms.G ⟨a, 8⟩ (v.setWidth 128)
  unmapped : ∀ m, F m → Mem.loadInt m.dmem a 8 = none

theorem StOk.mono {ms : MemSide isa} {F F' : MachineData → Prop} {a v : BitVec 64} (h : StOk ms F a v)
    (hFF : ∀ m, F' m → F m) : StOk ms F' a v :=
  ⟨h.rt, h.mp, h.G, fun m hm => h.unmapped m (hFF m hm)⟩

/-- **What a runtime load needs of its word `a`**: it is the runtime's,
mapped for a read (`MemSide.mp`), not thread-private memory under `F`
(`LimOk` without the room). -/
structure LdOk (ms : MemSide isa) (F : MachineData → Prop) (a : BitVec 64) : Prop where
  rt : ms.rt a.toNat
  mp : ms.mp ⟨a, 8⟩ false
  unmapped : ∀ m, F m → Mem.loadInt m.dmem a 8 = none

theorem LdOk.mono {ms : MemSide isa} {F F' : MachineData → Prop} {a : BitVec 64} (h : LdOk ms F a)
    (hFF : ∀ m, F' m → F m) : LdOk ms F' a :=
  ⟨h.rt, h.mp, fun m hm => h.unmapped m (hFF m hm)⟩

/-- `scc_rt_alloc_tcb`'s internal nodes: one per block or single
instruction of its feasible path. -/
inductive TN where
  | e | entry | j1 | len | shr1 | l1 | and1 | l2 | shr2 | l3 | and2 | l4 | imul1 | l5 | shl1 | l6 | lea1 | arg
  | rmw | bnd | j2 | ok | o1 | imul2 | o2 | shl2 | o3 | shl3 | o4 | or1 | o5 | hdr | ret

section Tcb

open AllocTcb (oI Fr s0 sA s1 s2 s3 s4 s5 hdr0 tcbLen lenL okL)

variable (lab : Label → Int64) (q : TcbG)

/-- `scc_rt_pinned`'s address. -/
abbrev pinA : BitVec 64 := (lab "scc_rt_pinned").toBitVec
/-- `scc_rt_pinned_next`'s address. -/
abbrev pnA : BitVec 64 := (lab "scc_rt_pinned_next").toBitVec

/-- **The nodes**: the frame (`Fr`) and the registers the next node reads. -/
def tcbN : TN → ND
  | .e => ⟨lab AllocTcb.fnL, AllocTcb.oE, fun σ c => c = q.c0 ∧ AllocTcb.Pre q.g q.n0 σ⟩
  | .entry => ⟨lab AllocTcb.entryL, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g) σ⟩
  | .j1 => ⟨lab AllocTcb.entryL + Int64.ofNat 20, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g) σ⟩
  | .len => ⟨lab lenL, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g) σ⟩
  | .shr1 => ⟨lab lenL + Int64.ofNat 11, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g) σ ∧
      σ.regs.rax.toBitVec = hdr0 ∧ σ.regs.rcx.toBitVec = 8#64⟩
  | .l1 => ⟨lab lenL + Int64.ofNat 14, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g) σ ∧ σ.regs.rax.toBitVec = 9#64⟩
  | .and1 => ⟨lab lenL + Int64.ofNat 29, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g) σ ∧
      σ.regs.rax.toBitVec = 9#64 ∧ σ.regs.rcx.toBitVec = 16383#64⟩
  | .l2 => ⟨lab lenL + Int64.ofNat 32, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g) σ ∧ σ.regs.rax.toBitVec = 9#64⟩
  | .shr2 => ⟨lab lenL + Int64.ofNat 47, oI, fun σ c => c = q.c0 ∧ Fr q.g (sA q.g) σ ∧
      σ.regs.rax.toBitVec = hdr0 ∧ σ.regs.rcx.toBitVec = 22#64⟩
  | .l3 => ⟨lab lenL + Int64.ofNat 50, oI, fun σ c => c = q.c0 ∧ Fr q.g (sA q.g) σ ∧ σ.regs.rax.toBitVec = 0#64⟩
  | .and2 => ⟨lab lenL + Int64.ofNat 65, oI, fun σ c => c = q.c0 ∧ Fr q.g (sA q.g) σ ∧
      σ.regs.rax.toBitVec = 0#64 ∧ σ.regs.rcx.toBitVec = 16383#64⟩
  | .l4 => ⟨lab lenL + Int64.ofNat 68, oI, fun σ c => c = q.c0 ∧ Fr q.g (sA q.g) σ ∧ σ.regs.rax.toBitVec = 0#64⟩
  | .imul1 => ⟨lab lenL + Int64.ofNat 95, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g) σ ∧
      σ.regs.rax.toBitVec = 1#64 ∧ σ.regs.rcx.toBitVec = 9#64⟩
  | .l5 => ⟨lab lenL + Int64.ofNat 99, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g) σ ∧ σ.regs.rax.toBitVec = 9#64⟩
  | .shl1 => ⟨lab lenL + Int64.ofNat 132, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g) σ ∧
      σ.regs.rax.toBitVec = 10#64 ∧ σ.regs.rcx.toBitVec = 3#64⟩
  | .l6 => ⟨lab lenL + Int64.ofNat 135, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g) σ ∧
      σ.regs.rax.toBitVec = tcbLen⟩
  | .lea1 => ⟨lab lenL + Int64.ofNat 139, oI, fun σ c => c = q.c0 ∧ Fr q.g (s2 q.g) σ⟩
  | .arg => ⟨lab lenL + Int64.ofNat 146, oI, fun σ c => c = q.c0 ∧ Fr q.g (s2 q.g) σ ∧
      σ.regs.rax.toBitVec = pnA lab⟩
  | .rmw => ⟨AllocTcb.rmwPc lab, oI, fun σ c => c = q.c0 ∧ Fr q.g (s2 q.g) σ ∧
      σ.regs.rax.toBitVec = tcbLen ∧ σ.regs.rcx.toBitVec = pnA lab⟩
  | .bnd => ⟨lab lenL + Int64.ofNat 163, oI, fun σ c => c = q.c0 ∧ Fr q.g (s2 q.g) σ ∧
      σ.regs.rax.toBitVec = q.n0⟩
  | .j2 => ⟨lab lenL + Int64.ofNat 198, oI, fun σ c => c = q.c0 ∧ Fr q.g (s3 q.g q.n0) σ⟩
  | .ok => ⟨lab okL, oI, fun σ c => c = q.c0 ∧ Fr q.g (s3 q.g q.n0) σ⟩
  | .o1 => ⟨lab okL + Int64.ofNat 7, oI, fun σ c => c = q.c0 ∧ Fr q.g (s3 q.g q.n0) σ ∧
      σ.regs.rax.toBitVec = pinA lab⟩
  | .imul2 => ⟨lab okL + Int64.ofNat 34, oI, fun σ c => c = q.c0 ∧ Fr q.g (s4 q.g q.n0 (pinA lab)) σ ∧
      σ.regs.rax.toBitVec = 1#64 ∧ σ.regs.rcx.toBitVec = 0#64⟩
  | .o2 => ⟨lab okL + Int64.ofNat 38, oI, fun σ c => c = q.c0 ∧ Fr q.g (s4 q.g q.n0 (pinA lab)) σ ∧
      σ.regs.rax.toBitVec = 0#64⟩
  | .shl2 => ⟨lab okL + Int64.ofNat 53, oI, fun σ c => c = q.c0 ∧ Fr q.g (s4 q.g q.n0 (pinA lab)) σ ∧
      σ.regs.rax.toBitVec = 0#64 ∧ σ.regs.rcx.toBitVec = 3#64⟩
  | .o3 => ⟨lab okL + Int64.ofNat 56, oI, fun σ c => c = q.c0 ∧ Fr q.g (s4 q.g q.n0 (pinA lab)) σ ∧
      σ.regs.rax.toBitVec = 0#64⟩
  | .shl3 => ⟨lab okL + Int64.ofNat 74, oI, fun σ c => c = q.c0 ∧ Fr q.g (s5 q.g q.n0 (pinA lab)) σ ∧
      σ.regs.rax.toBitVec = 1#64 ∧ σ.regs.rcx.toBitVec = 36#64⟩
  | .o4 => ⟨lab okL + Int64.ofNat 77, oI, fun σ c => c = q.c0 ∧ Fr q.g (s5 q.g q.n0 (pinA lab)) σ ∧
      σ.regs.rax.toBitVec = 1#64 <<< 36⟩
  | .or1 => ⟨lab okL + Int64.ofNat 95, oI, fun σ c => c = q.c0 ∧ Fr q.g (s5 q.g q.n0 (pinA lab)) σ ∧
      σ.regs.rax.toBitVec = hdr0 ∧ σ.regs.rcx.toBitVec = 1#64 <<< 36⟩
  | .o5 => ⟨lab okL + Int64.ofNat 98, oI, fun σ c => c = q.c0 ∧ Fr q.g (s5 q.g q.n0 (pinA lab)) σ ∧
      σ.regs.rax.toBitVec = hdr0 ||| 1#64 <<< 36⟩
  | .hdr => ⟨AllocTcb.hdrPc lab, oI, fun σ c => c = q.c0 ∧ Fr q.g (s5 q.g q.n0 (pinA lab)) σ ∧
      σ.regs.rax.toBitVec = hdr0 ||| 1#64 <<< 36 ∧ σ.regs.rcx.toBitVec = pinA lab + q.n0⟩
  | .ret => ⟨lab okL + Int64.ofNat 143, oI, fun σ c => c = q.c0 ∧ Fr q.g (s5 q.g q.n0 (pinA lab)) σ⟩

/-- **The exit**: at the return address, `Post`. -/
def tcbX : Unit → ND
  | () => ⟨Int64.ofBitVec q.g.ra, AllocTcb.oR, fun σ c => c = q.c0 ∧ AllocTcb.Post q.g q.n0 (pinA lab) σ⟩

end Tcb

/-- The header's store is `stDir`. -/
theorem hdrBlk_eq : AllocTcb.hdrBlk = [(stDir .rcx 0 .rax, 3)] := by decide

/-- The counter's add is `xaddDir`. -/
theorem rmwBlk_eq : AllocTcb.rmwBlk = [(xaddDir .rcx 0 .rax, 5)] := by decide

/-- **The counter's add** `lock xadd` on `scc_rt_pinned_next`
(`ownXadd_nd`): the word holds `n0` at the add (`own`, a named hypothesis
until `ms.own` is wired) and runtime memory may hold `n0 + tcbLen` there
(`next`). -/
structure TcbOk (ms : MemSide isa) (F : MachineData → Prop) (exe : _root_.Executable) (endPc : Int64)
    (n0 : BitVec 64) : Prop where
  next : StOk ms F (pnA (_root_.Executable.labels exe).label) (n0 + AllocTcb.tcbLen)
  own : OwnAt ms exe endPc (AllocTcb.rmwPc (_root_.Executable.labels exe).label)
    (pnA (_root_.Executable.labels exe).label) n0

theorem TcbOk.mono {ms : MemSide isa} {F F' : MachineData → Prop} {exe : _root_.Executable} {endPc : Int64}
    {n0 : BitVec 64} (h : TcbOk ms F exe endPc n0) (hFF : ∀ m, F' m → F m) : TcbOk ms F' exe endPc n0 :=
  ⟨h.next.mono hFF, h.own⟩

/-- **`scc_rt_alloc_tcb`'s node obligations inside `W`**: the block nodes'
states (`BlkW`) and the single instructions' (`NodeW`). -/
def TcbW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (q : TcbG) : TN → Prop
  | .e => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .e) AllocTcb.atPro
  | .entry => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .entry) AllocTcb.atChk
  | .j1 => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .j1) AllocTcb.atJ1
  | .len => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .len) AllocTcb.atL0
  | .shr1 => NodeW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .shr1)
  | .l1 => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .l1) AllocTcb.atL1
  | .and1 => NodeW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .and1)
  | .l2 => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .l2) AllocTcb.atL2
  | .shr2 => NodeW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .shr2)
  | .l3 => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .l3) AllocTcb.atL3
  | .and2 => NodeW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .and2)
  | .l4 => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .l4) AllocTcb.atL4
  | .imul1 => NodeW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .imul1)
  | .l5 => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .l5) AllocTcb.atL5
  | .shl1 => NodeW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .shl1)
  | .l6 => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .l6) AllocTcb.atL6
  | .lea1 => NodeW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .lea1)
  | .arg => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .arg) AllocTcb.atArg
  | .rmw => NodeW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .rmw)
  | .bnd => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .bnd) AllocTcb.atBnd
  | .j2 => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .j2) AllocTcb.atJ2
  | .ok => NodeW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .ok)
  | .o1 => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .o1) AllocTcb.atO1
  | .imul2 => NodeW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .imul2)
  | .o2 => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .o2) AllocTcb.atO2
  | .shl2 => NodeW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .shl2)
  | .o3 => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .o3) AllocTcb.atO3
  | .shl3 => NodeW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .shl3)
  | .o4 => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .o4) AllocTcb.atO4
  | .or1 => NodeW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .or1)
  | .o5 => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .o5) AllocTcb.atO5
  | .hdr => NodeW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .hdr)
  | .ret => BlkW W K exe endPc R F (tcbN (_root_.Executable.labels exe).label q .ret) AllocTcb.atRet

section TcbProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F F0 : MachineData → Prop}

set_option hygiene false in
/-- A block node of `scc_rt_alloc_tcb`: the block, its `okBlk`, its code; the edge is left. -/
local macro "tnode " b:ident ok:ident l:term:max k:term:max : tactic =>
  `(tactic| refine seg_nd (by simp [$b:ident]) $ok hF hR hlo hhi
    (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) (by first | rfl | exact ofNat_zero' _))
      fun σ c hJ => ⟨c, .refl c, ?_⟩)

set_option hygiene false in
/-- A node at an instruction with undefined flags writing `%rax`, at `l + k`
(`z` bytes), to node `j`; the invariant's facts are left. -/
local macro "fnode " fi:term:max l:term:max k:term:max z:term:max j:term:max : tactic =>
  `(tactic| refine flag_nd (fi := $fi) rfl hF
    (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) rfl)
      fun σ c hJ fl => ⟨c, .refl c, .inl ⟨$j, ofNat_add' _ $k $z, rfl, ?_⟩⟩)

/-- **`scc_rt_alloc_tcb` is one segment** in any valid layout of
`ret0Cells`, from its entry to its return, for any region holding its frame
of 176, the saved `%rbp` and the return address, and any frame condition
implying `F0`, given: room for the TCB below `2^17` (`hn`), the header
word's facts (`hhdr`), and the counter's add's (`htcb`). -/
theorem alloc_tcb_seg (hp : Lays exe SccCode.ret0Cells) (hend : endPc = endOf exe SccCode.ret0Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -184) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TcbG) (hn : q.n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F0 (pinA (_root_.Executable.labels exe).label + q.n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F0 exe endPc q.n0) :
    Seg p lbl ms (At exe endPc R F (tcbN (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x, At exe endPc R F (tcbX (_root_.Executable.labels exe).label q x) s c) := by
  have hin' := AllocTcb.ret0_allocTcbIn
  simp only [AllocTcb.allocTcbIn, AllocTcb.fiAt, AllocTcb.siAt, hdrBlk_eq, rmwBlk_eq, Bool.and_eq_true] at hin'
  have eEntry := label_labelGapB (a := AllocTcb.fnL) (b := AllocTcb.entryL) (off := 19) hp (by simp only [hin'])
  have pv := AllocTcb.path_vals
  refine fn_seg (N := tcbN _ q) (E := tcbX _ q) (fun i => ?_) TN.e
  cases i
  case e =>
    tnode AllocTcb.atPro AllocTcb.atPro_ok AllocTcb.fnL 0
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atPro_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.entry, by rw [h1]; exact eEntry, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    tnode AllocTcb.atChk AllocTcb.atChk_ok AllocTcb.entryL 0
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atChk_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.j1, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case j1 =>
    tnode AllocTcb.atJ1 AllocTcb.atJ1_ok AllocTcb.entryL 20
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atJ1_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.len, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case len =>
    tnode AllocTcb.atL0 AllocTcb.atL0_ok AllocTcb.lenL 0
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL0_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.shr1, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shr1 =>
    fnode (.shr_cl .rax) AllocTcb.lenL 11 3 TN.l1
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shr_rax ha hc fl).trans pv.1⟩
  case l1 =>
    tnode AllocTcb.atL1 AllocTcb.atL1_ok AllocTcb.lenL 14
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL1_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.and1, by rw [h1]; exact ofNat_add' _ 14 15, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case and1 =>
    fnode (.and_rr .rax .rcx) AllocTcb.lenL 29 3 TN.l2
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.and_rax ha hc fl).trans pv.2.1⟩
  case l2 =>
    tnode AllocTcb.atL2 AllocTcb.atL2_ok AllocTcb.lenL 32
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL2_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.shr2, by rw [h1]; exact ofNat_add' _ 32 15, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shr2 =>
    fnode (.shr_cl .rax) AllocTcb.lenL 47 3 TN.l3
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shr_rax ha hc fl).trans pv.2.2.1⟩
  case l3 =>
    tnode AllocTcb.atL3 AllocTcb.atL3_ok AllocTcb.lenL 50
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL3_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.and2, by rw [h1]; exact ofNat_add' _ 50 15, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case and2 =>
    fnode (.and_rr .rax .rcx) AllocTcb.lenL 65 3 TN.l4
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.and_rax ha hc fl).trans pv.2.2.2.1⟩
  case l4 =>
    tnode AllocTcb.atL4 AllocTcb.atL4_ok AllocTcb.lenL 68
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL4_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.imul1, by rw [h1]; exact ofNat_add' _ 68 27, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case imul1 =>
    fnode (.imul_rr .rax .rcx) AllocTcb.lenL 95 4 TN.l5
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.imul_rax ha hc fl).trans pv.2.2.2.2.1⟩
  case l5 =>
    tnode AllocTcb.atL5 AllocTcb.atL5_ok AllocTcb.lenL 99
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL5_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.shl1, by rw [h1]; exact ofNat_add' _ 99 33, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shl1 =>
    fnode (.shl_cl .rax) AllocTcb.lenL 132 3 TN.l6
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shl_rax ha hc fl).trans pv.2.2.2.2.2.1⟩
  case l6 =>
    tnode AllocTcb.atL6 AllocTcb.atL6_ok AllocTcb.lenL 135
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atL6_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.lea1, by rw [h1]; exact ofNat_add' _ 135 4, by rw [h2]; rfl, rfl, h3⟩
  case lea1 =>
    refine si_nd (si := .leaRip .rax "scc_rt_pinned_next") (z := 7) rfl hF
      (code_field hp hend (by simp only [hin']) (l := AllocTcb.lenL) (off := 139) rfl)
      fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.arg, ofNat_add' _ 139 7, rfl, ?_⟩⟩
    obtain ⟨rfl, hJ⟩ := hJ
    exact ⟨rfl, AllocTcb.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case arg =>
    tnode AllocTcb.atArg AllocTcb.atArg_ok AllocTcb.lenL 146
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atArg_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.rmw, by rw [h1]; exact ofNat_add' _ 146 12, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case rmw =>
    refine ownXadd_nd (b := .rcx) (k := 0) (r := .rax) (z := 5) (by decide) hF
      (code_field hp hend (by simp only [hin']) (l := AllocTcb.lenL) (off := 158) rfl) htcb.own
      fun m σ c _ hD hJ => ?_
    dsimp only [tcbN] at hJ ⊢
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = pnA (_root_.Executable.labels exe).label := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hv : σ.regs.get64 .rax = AllocTcb.tcbLen := by rw [← ha]; rfl
    rw [hb, hv]
    exact ⟨rfl, htcb.next.rt, htcb.next.mp, htcb.next.G, htcb.next.unmapped m (hFF m hD),
      q.c0, .refl q.c0, fun fl =>
        .inl ⟨TN.bnd, ofNat_add' _ 158 5, rfl, rfl, by simpa [ownStep, AllocTcb.Fr, Reg64s.set64] using hJ,
          by simp [ownStep, Reg64s.set64]⟩⟩
  case bnd =>
    tnode AllocTcb.atBnd AllocTcb.atBnd_ok AllocTcb.lenL 163
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atBnd_walk (_root_.Executable.labels exe).label _ hJ ha hn
    exact .inl ⟨TN.j2, by rw [h1]; exact ofNat_add' _ 163 35, by rw [h2]; rfl, rfl, h3⟩
  case j2 =>
    tnode AllocTcb.atJ2 AllocTcb.atJ2_ok AllocTcb.lenL 198
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atJ2_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.ok, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case ok =>
    refine si_nd (si := .leaRip .rax "scc_rt_pinned") (z := 7) rfl hF
      (code_field hp hend (by simp only [hin']) (l := AllocTcb.okL) (off := 0) (ofNat_zero' _))
      fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.o1, ?_, rfl, ?_⟩⟩
    · show _ + Int64.ofNat 7 = _ + Int64.ofNat 7; rfl
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, AllocTcb.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case o1 =>
    tnode AllocTcb.atO1 AllocTcb.atO1_ok AllocTcb.okL 7
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO1_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.imul2, by rw [h1]; exact ofNat_add' _ 7 27, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case imul2 =>
    fnode (.imul_rr .rax .rcx) AllocTcb.okL 34 4 TN.o2
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.imul_rax ha hc fl).trans pv.2.2.2.2.2.2.1⟩
  case o2 =>
    tnode AllocTcb.atO2 AllocTcb.atO2_ok AllocTcb.okL 38
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO2_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.shl2, by rw [h1]; exact ofNat_add' _ 38 15, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shl2 =>
    fnode (.shl_cl .rax) AllocTcb.okL 53 3 TN.o3
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shl_rax ha hc fl).trans pv.2.2.2.2.2.2.2.1⟩
  case o3 =>
    tnode AllocTcb.atO3 AllocTcb.atO3_ok AllocTcb.okL 56
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO3_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.shl3, by rw [h1]; exact ofNat_add' _ 56 18, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shl3 =>
    fnode (.shl_cl .rax) AllocTcb.okL 74 3 TN.o4
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shl_rax ha hc fl).trans pv.2.2.2.2.2.2.2.2⟩
  case o4 =>
    tnode AllocTcb.atO4 AllocTcb.atO4_ok AllocTcb.okL 77
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO4_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.or1, by rw [h1]; exact ofNat_add' _ 77 18, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case or1 =>
    fnode (.or_rr .rax .rcx) AllocTcb.okL 95 3 TN.o5
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, AllocTcb.or_rax ha hc fl⟩
  case o5 =>
    tnode AllocTcb.atO5 AllocTcb.atO5_ok AllocTcb.okL 98
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO5_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.hdr, by rw [h1]; exact ofNat_add' _ 98 42, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case hdr =>
    refine rtst_nd (b := .rcx) (k := 0) (r := .rax) (z := 3)
      (code_field hp hend (by simp only [hin']) (l := AllocTcb.okL) (off := 140) rfl)
      fun m σ c _ hD hJ => ?_
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = pinA (_root_.Executable.labels exe).label + q.n0 := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hv : σ.regs.get64 .rax = AllocTcb.hdr0 ||| 1#64 <<< 36 := by rw [← ha]; rfl
    rw [hb, hv]
    exact ⟨hhdr.rt, hhdr.mp, hhdr.G, hhdr.unmapped m (hFF m hD), q.c0,
      .refl q.c0, .inl ⟨TN.ret, ofNat_add' _ 140 3, rfl, rfl, hJ⟩⟩
  case ret =>
    tnode AllocTcb.atRet AllocTcb.atRet_ok AllocTcb.okL 143
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atRet_walk (_root_.Executable.labels exe).label _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, h3⟩


set_option hygiene false in
/-- A block node of `scc_rt_alloc_tcb` inside `W`: the block, its `okBlk`, its code, its
obligation; the edge is left. -/
local macro "tnodeW " b:ident ok:ident l:term:max k:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hlo hhi
    (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) (by first | rfl | exact ofNat_zero' _)) $w
      fun σ c hJ => ⟨c, .refl c, ?_⟩)

set_option hygiene false in
/-- A node at an instruction with undefined flags writing `%rax` inside `W`, at `l + k`
(`z` bytes), to node `j`, its obligation `w`; the invariant's facts are left. -/
local macro "fnodeW " fi:term:max l:term:max k:term:max z:term:max j:term:max w:term:max : tactic =>
  `(tactic| refine flag_ndW (fi := $fi) rfl hF
    (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) rfl) $w
      fun σ c hJ fl => ⟨c, .refl c, .inl ⟨$j, ofNat_add' _ $k $z, rfl, ?_⟩⟩)

/-- **`scc_rt_alloc_tcb` is one segment inside `W`** (`alloc_tcb_seg`, its
states' obligations `hW`): in any valid layout of `ret0Cells`, from its
entry to its return, for any region holding its frame of 176, the saved
`%rbp` and the return address, and any frame condition implying `F0`,
given: room for the TCB below `2^17` (`hn`), the header word's facts
(`hhdr`), and the counter's add's (`htcb`). -/
theorem alloc_tcb_segW {W : Frag isa} {K : State → State → Prop} (hp : Lays exe SccCode.ret0Cells)
    (hend : endPc = endOf exe SccCode.ret0Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -184) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TcbG) (hn : q.n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F0 (pinA (_root_.Executable.labels exe).label + q.n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F0 exe endPc q.n0) (hW : ∀ i, TcbW W K exe endPc R F q i) :
    SegW W K p lbl ms (At exe endPc R F (tcbN (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x, At exe endPc R F (tcbX (_root_.Executable.labels exe).label q x) s c) := by
  have hin' := AllocTcb.ret0_allocTcbIn
  simp only [AllocTcb.allocTcbIn, AllocTcb.fiAt, AllocTcb.siAt, hdrBlk_eq, rmwBlk_eq, Bool.and_eq_true] at hin'
  have eEntry := label_labelGapB (a := AllocTcb.fnL) (b := AllocTcb.entryL) (off := 19) hp (by simp only [hin'])
  have pv := AllocTcb.path_vals
  refine fn_segW (N := tcbN _ q) (E := tcbX _ q) (fun i => ?_) TN.e
  cases i
  case e =>
    tnodeW AllocTcb.atPro AllocTcb.atPro_ok AllocTcb.fnL 0 (hW TN.e)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atPro_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.entry, by rw [h1]; exact eEntry, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    tnodeW AllocTcb.atChk AllocTcb.atChk_ok AllocTcb.entryL 0 (hW TN.entry)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atChk_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.j1, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case j1 =>
    tnodeW AllocTcb.atJ1 AllocTcb.atJ1_ok AllocTcb.entryL 20 (hW TN.j1)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atJ1_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.len, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case len =>
    tnodeW AllocTcb.atL0 AllocTcb.atL0_ok AllocTcb.lenL 0 (hW TN.len)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL0_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.shr1, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shr1 =>
    fnodeW (.shr_cl .rax) AllocTcb.lenL 11 3 TN.l1 (hW TN.shr1)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shr_rax ha hc fl).trans pv.1⟩
  case l1 =>
    tnodeW AllocTcb.atL1 AllocTcb.atL1_ok AllocTcb.lenL 14 (hW TN.l1)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL1_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.and1, by rw [h1]; exact ofNat_add' _ 14 15, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case and1 =>
    fnodeW (.and_rr .rax .rcx) AllocTcb.lenL 29 3 TN.l2 (hW TN.and1)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.and_rax ha hc fl).trans pv.2.1⟩
  case l2 =>
    tnodeW AllocTcb.atL2 AllocTcb.atL2_ok AllocTcb.lenL 32 (hW TN.l2)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL2_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.shr2, by rw [h1]; exact ofNat_add' _ 32 15, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shr2 =>
    fnodeW (.shr_cl .rax) AllocTcb.lenL 47 3 TN.l3 (hW TN.shr2)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shr_rax ha hc fl).trans pv.2.2.1⟩
  case l3 =>
    tnodeW AllocTcb.atL3 AllocTcb.atL3_ok AllocTcb.lenL 50 (hW TN.l3)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL3_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.and2, by rw [h1]; exact ofNat_add' _ 50 15, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case and2 =>
    fnodeW (.and_rr .rax .rcx) AllocTcb.lenL 65 3 TN.l4 (hW TN.and2)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.and_rax ha hc fl).trans pv.2.2.2.1⟩
  case l4 =>
    tnodeW AllocTcb.atL4 AllocTcb.atL4_ok AllocTcb.lenL 68 (hW TN.l4)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL4_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.imul1, by rw [h1]; exact ofNat_add' _ 68 27, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case imul1 =>
    fnodeW (.imul_rr .rax .rcx) AllocTcb.lenL 95 4 TN.l5 (hW TN.imul1)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.imul_rax ha hc fl).trans pv.2.2.2.2.1⟩
  case l5 =>
    tnodeW AllocTcb.atL5 AllocTcb.atL5_ok AllocTcb.lenL 99 (hW TN.l5)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL5_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.shl1, by rw [h1]; exact ofNat_add' _ 99 33, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shl1 =>
    fnodeW (.shl_cl .rax) AllocTcb.lenL 132 3 TN.l6 (hW TN.shl1)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shl_rax ha hc fl).trans pv.2.2.2.2.2.1⟩
  case l6 =>
    tnodeW AllocTcb.atL6 AllocTcb.atL6_ok AllocTcb.lenL 135 (hW TN.l6)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atL6_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.lea1, by rw [h1]; exact ofNat_add' _ 135 4, by rw [h2]; rfl, rfl, h3⟩
  case lea1 =>
    refine si_ndW (si := .leaRip .rax "scc_rt_pinned_next") (z := 7) rfl hF
      (code_field hp hend (by simp only [hin']) (l := AllocTcb.lenL) (off := 139) rfl) (hW TN.lea1)
      fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.arg, ofNat_add' _ 139 7, rfl, ?_⟩⟩
    obtain ⟨rfl, hJ⟩ := hJ
    exact ⟨rfl, AllocTcb.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case arg =>
    tnodeW AllocTcb.atArg AllocTcb.atArg_ok AllocTcb.lenL 146 (hW TN.arg)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atArg_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.rmw, by rw [h1]; exact ofNat_add' _ 146 12, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case rmw =>
    refine ownXadd_ndW (b := .rcx) (k := 0) (r := .rax) (z := 5) (by decide) hF
      (code_field hp hend (by simp only [hin']) (l := AllocTcb.lenL) (off := 158) rfl) htcb.own (hW TN.rmw)
      fun m σ c _ hD hJ => ?_
    dsimp only [tcbN] at hJ ⊢
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = pnA (_root_.Executable.labels exe).label := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hv : σ.regs.get64 .rax = AllocTcb.tcbLen := by rw [← ha]; rfl
    rw [hb, hv]
    exact ⟨rfl, htcb.next.rt, htcb.next.mp, htcb.next.G, htcb.next.unmapped m (hFF m hD),
      q.c0, .refl q.c0, fun fl =>
        .inl ⟨TN.bnd, ofNat_add' _ 158 5, rfl, rfl, by simpa [ownStep, AllocTcb.Fr, Reg64s.set64] using hJ,
          by simp [ownStep, Reg64s.set64]⟩⟩
  case bnd =>
    tnodeW AllocTcb.atBnd AllocTcb.atBnd_ok AllocTcb.lenL 163 (hW TN.bnd)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atBnd_walk (_root_.Executable.labels exe).label _ hJ ha hn
    exact .inl ⟨TN.j2, by rw [h1]; exact ofNat_add' _ 163 35, by rw [h2]; rfl, rfl, h3⟩
  case j2 =>
    tnodeW AllocTcb.atJ2 AllocTcb.atJ2_ok AllocTcb.lenL 198 (hW TN.j2)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atJ2_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.ok, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case ok =>
    refine si_ndW (si := .leaRip .rax "scc_rt_pinned") (z := 7) rfl hF
      (code_field hp hend (by simp only [hin']) (l := AllocTcb.okL) (off := 0) (ofNat_zero' _)) (hW TN.ok)
      fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.o1, ?_, rfl, ?_⟩⟩
    · show _ + Int64.ofNat 7 = _ + Int64.ofNat 7; rfl
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, AllocTcb.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case o1 =>
    tnodeW AllocTcb.atO1 AllocTcb.atO1_ok AllocTcb.okL 7 (hW TN.o1)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO1_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.imul2, by rw [h1]; exact ofNat_add' _ 7 27, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case imul2 =>
    fnodeW (.imul_rr .rax .rcx) AllocTcb.okL 34 4 TN.o2 (hW TN.imul2)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.imul_rax ha hc fl).trans pv.2.2.2.2.2.2.1⟩
  case o2 =>
    tnodeW AllocTcb.atO2 AllocTcb.atO2_ok AllocTcb.okL 38 (hW TN.o2)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO2_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.shl2, by rw [h1]; exact ofNat_add' _ 38 15, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shl2 =>
    fnodeW (.shl_cl .rax) AllocTcb.okL 53 3 TN.o3 (hW TN.shl2)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shl_rax ha hc fl).trans pv.2.2.2.2.2.2.2.1⟩
  case o3 =>
    tnodeW AllocTcb.atO3 AllocTcb.atO3_ok AllocTcb.okL 56 (hW TN.o3)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO3_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.shl3, by rw [h1]; exact ofNat_add' _ 56 18, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shl3 =>
    fnodeW (.shl_cl .rax) AllocTcb.okL 74 3 TN.o4 (hW TN.shl3)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shl_rax ha hc fl).trans pv.2.2.2.2.2.2.2.2⟩
  case o4 =>
    tnodeW AllocTcb.atO4 AllocTcb.atO4_ok AllocTcb.okL 77 (hW TN.o4)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO4_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.or1, by rw [h1]; exact ofNat_add' _ 77 18, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case or1 =>
    fnodeW (.or_rr .rax .rcx) AllocTcb.okL 95 3 TN.o5 (hW TN.or1)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, AllocTcb.or_rax ha hc fl⟩
  case o5 =>
    tnodeW AllocTcb.atO5 AllocTcb.atO5_ok AllocTcb.okL 98 (hW TN.o5)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO5_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.hdr, by rw [h1]; exact ofNat_add' _ 98 42, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case hdr =>
    refine rtst_ndW (b := .rcx) (k := 0) (r := .rax) (z := 3)
      (code_field hp hend (by simp only [hin']) (l := AllocTcb.okL) (off := 140) rfl) (hW TN.hdr)
      fun m σ c _ hD hJ => ?_
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = pinA (_root_.Executable.labels exe).label + q.n0 := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hv : σ.regs.get64 .rax = AllocTcb.hdr0 ||| 1#64 <<< 36 := by rw [← ha]; rfl
    rw [hb, hv]
    exact ⟨hhdr.rt, hhdr.mp, hhdr.G, hhdr.unmapped m (hFF m hD), q.c0,
      .refl q.c0, .inl ⟨TN.ret, ofNat_add' _ 140 3, rfl, rfl, hJ⟩⟩
  case ret =>
    tnodeW AllocTcb.atRet AllocTcb.atRet_ok AllocTcb.okL 143 (hW TN.ret)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atRet_walk (_root_.Executable.labels exe).label _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, h3⟩

end TcbProof

/-! ## `scc_rt_start` up to `.x0` -/

/-- `scc_rt_start`'s call of `scc_rt_alloc_tcb` with the header and `k = 1`. -/
def startCall : List (Directive × Nat) := (parse("movq %rax, -16(%rbp)
movq $2307, %rdi
movq $1, %rsi
call scc_rt_alloc_tcb")).zip [4, 7, 7, 5]

block_spec startCall (-48) 0 oS startCall

/-- `.Lscc_rt_start.x0`, the return address of the call. -/
abbrev x0L : Label := ".Lscc_rt_start.x0"

/-- **The call's code in `cells`**: the block after the system call, `.x0`
right after it. -/
def startCallIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells startE 43 startCall && labelGapB cells startE x0L 66

theorem ret0_startCallIn : startCallIn SccCode.ret0Cells = true := by decide +kernel

section Start

variable (lab : Label → Int64)

/-- `scc_rt_start`'s entry, the source control `c0`. -/
def startN0 (c0 : Ctl) : ND := ⟨lab "scc_rt_start", ⟨0, []⟩, fun _ c => c = c0⟩

/-- After `rt_sigaction`, at the call's block. -/
def startN1 (c0 : Ctl) : ND := ⟨lab startE + Int64.ofNat 43, oS, fun _ c => c = c0⟩

/-- **The call node**: at `scc_rt_alloc_tcb`'s label, its arguments, the
return address `.x0` pushed, `%rbp` 40 bytes above `%rsp`. -/
def startNC (c0 : Ctl) : ND := ⟨lab AllocTcb.fnL, ⟨-48, []⟩, fun σ c =>
  (c = c0 ∧ σ.regs.rdi.toBitVec = AllocTcb.hdr0 ∧ σ.regs.rsi.toBitVec = 1#64) ∧
    σ.slot (-48) = (lab x0L).toBitVec ∧ σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (-8 - -48)⟩

/-- **Back at `.x0`**: `%rax` the TCB, one word past its header at
`scc_rt_pinned + n0`; `%rbp` at the saved `%rbp`. -/
def startN2 (n0 : BitVec 64) (c0 : Ctl) : ND := ⟨lab x0L, oS, fun σ c =>
  (c = c0 ∧ σ.regs.rax.toBitVec = pinA lab + n0 + 8#64) ∧
    σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (-8 - -40)⟩

end Start

section StartProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_start` from its entry to `.x0`** in any valid layout of
`ret0Cells`: S1, the call's block, and `scc_rt_alloc_tcb` through
`call_nd_F`, with `scc_rt_pinned_next` holding `n0` (room below `2^17`,
`hn`), the header word's facts (`hhdr`) and the counter's add at every
call's ghosts (`htcb`). -/
theorem start_x0_seg (hp : Lays exe SccCode.ret0Cells) (hend : endPc = endOf exe SccCode.ret0Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -232) (hhi : 0 ≤ R.hi) (n0 : BitVec 64) (c0 : Ctl) (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F exe endPc n0) :
    Seg p lbl ms (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0))
      (At exe endPc R F (startN2 (_root_.Executable.labels exe).label n0 c0)) := by
  let lab := (_root_.Executable.labels exe).label
  have hin := ret0_startCallIn
  simp only [startCallIn, Bool.and_eq_true] at hin
  have ex0 := label_labelGapB hp hin.2
  have hlo48 : R.lo ≤ -48 := by omega
  refine Seg.seq (ret0_start_seg hp hend hK hF hR (by omega) (by omega) (nC := startN1 lab c0)
      (by show lab startE + Int64.ofNat 43 = lab startE + 7 + 34 + 2; rw [Int64.add_assoc, Int64.add_assoc]; rfl)
      (by show SO.le oS oS = true; decide) fun _ _ h => h)
    (Seg.seq (Q := At exe endPc R F (startNC lab c0)) ?_
      ((seg_one (n := ⟨lab x0L, ⟨-40, []⟩, (startN2 lab n0 c0).J⟩) ?_).mono_post
        fun _ _ h => At.rbp h fun _ _ h => h.2))
  · -- the call's block
    refine (seg_one (seg_nd (by simp [startCall]) startCall_ok hF hR hlo48 hhi
      (code_field hp hend hin.1 rfl) fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)).mono_pre
      fun _ _ h => At.rbp_get rfl h
    · dsimp only [startN1, startNC]; rw [startCall_run]
    · dsimp only [startN1, startNC]; rw [startCall_run]; rfl
    · dsimp only [startN1, startNC] at hJ ⊢; rw [startCall_run]
      obtain ⟨rfl, hb⟩ := hJ
      refine ⟨⟨rfl, ?_, ?_⟩, ?_, ?_⟩
      · simp [Reg64s.set64]
      · simp [Reg64s.set64]
      · simp only [upd_apply, ↓reduceIte]
        rw [show lab x0L = _ from ex0, Int64.toBitVec_add, Int64.toBitVec_add, BitVec.add_assoc]; rfl
      · simp only [Reg64s.get64, Reg64s.set64] at hb ⊢; rw [hb]; bv_omega
  · -- `scc_rt_alloc_tcb`
    refine call_nd_F (e0 := 0) (lo' := -184) (hi' := 8) (Ne := fun g => tcbN lab ⟨g, n0, c0⟩ .e)
      (Ex := fun g => tcbX lab ⟨g, n0, c0⟩)
      hR hF (by show R.lo ≤ -48 - 0 + -184; omega) (by decide) (by show (-48 : Int) - 0 < R.hi; omega)
      (by show (-48 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-48 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide)
      (fun R' F' hR' hlo' hhi' hF' hFF g' =>
        alloc_tcb_seg hp hend hF' hR' hlo' hhi' hFF ⟨g', n0, c0⟩ hn hhdr htcb)
      (fun _ => rfl) ?_ ?_
    · rintro σC c ⟨⟨rfl, h0, h1⟩, -, -⟩
      exact ⟨⟨σC.regs.rsp.toBitVec, σC.regs.rbp.toBitVec, σC.slot (-48 - 0 + 0)⟩, rfl, rfl, rfl, rfl, rfl, h0, h1⟩
    · rintro g x σC c σx c' σR ⟨-, h48, hb⟩ ⟨-, hsp, hfp, hra, -⟩ ⟨rfl, hsp', hb', hrax⟩ hregs - - -
      refine .inl ⟨(), ?_, by show SO.le ⟨-40, []⟩ ⟨-48 - 0 + 8, []⟩ = true; decide, ⟨rfl, ?_⟩, ?_⟩
      · show lab x0L = Int64.ofBitVec g.ra
        rw [← hra]
        show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
        rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
      · rw [hregs]; exact hrax
      · show σR.regs.get64 .rbp = σR.regs.get64 .rsp + BitVec.ofInt 64 (-8 - -40)
        rw [hregs]
        simp only [Reg64s.get64] at hb ⊢
        rw [hb', hsp', ← hfp, ← hsp]
        show σC.regs.rbp.toBitVec = σC.regs.rsp.toBitVec + 8#64 + BitVec.ofInt 64 (-8 - -40)
        rw [hb]; bv_omega

end StartProof

/-! ## `scc_rt_stack_take` -/

/-- **The ghosts of a call of `scc_rt_stack_take`**: `%rsp`, `%rbp` and the
return address at entry, the own word `scc_rt_stack_next`'s value `k0` on
entry, the source control. -/
structure TakeG where
  g : AllocTcb.G
  k0 : BitVec 64
  c0 : Ctl

/-- `scc_rt_stack_take`'s internal nodes on its feasible path. -/
inductive TK where
  | e | entry | cls | j1 | d0 | d7 | d26 | d33 | d52 | d59 | sp0 | swp | sp14 | lk0 | ldn | lk7
  | b0 | b7 | unl | b31 | b38 | nxt | b61 | b108 | ok0 | ok7 | tk | site | ret

/-- The take site's `nop`. -/
def nopBlk : List (Directive × Nat) := (parse("nop")).zip [1]

block_spec nopBlk (-200) 8 StackTake.oI nopBlk

/-- The unlock is `stDir`. -/
theorem unlBlk_eq : ((parse("movq %rax, (%rcx)")).zip [3] : List (Directive × Nat)) = [(stDir .rcx 0 .rax, 3)] :=
  hdrBlk_eq

/-! ## The take

At the take site the kernel takes the thread's step: the stack range `rS`
named by `%rdi`/`%rsi` moves into the thread's private memory with whatever
bytes the pool holds there, and the thread moves past the site's `nop`
(`Kernel.step_at_take`). In a segment this is an outside move (`SegW`'s
`K`): `TakeK a rS`, at the site's pc `a`. A pair at the site is moved by it
for every pool, so no `Out` row is asked there; every other pair is not. -/

section TakeNode

/-- **The take of the range `rS` at the pc `a`**: the pool's bytes `pm`
copied onto `rS` in private memory, the pc past the `nop`
(`Scc.Sem.X64.abi`'s `skip` and `setDmem`). -/
def TakeK (a : Int64) (rS : Scc.Sem.Range) (s s' : State) : Prop :=
  s.st.2 = a ∧ ∃ pm : _root_.Mem 64,
    s' = Scc.Sem.X64.abi.skip (Scc.Sem.X64.abi.setDmem s (Scc.Sem.Kernel.copyRange pm (Scc.Sem.X64.abi.dmem s) rS))

/-- The machine data after a take of `rS` from the pool `pm`. -/
def takeMem (pm : _root_.Mem 64) (rS : Scc.Sem.Range) (m : MachineData) : MachineData :=
  { m with dmem := Scc.Sem.Kernel.copyRange pm m.dmem rS }

/-- Only a state at `a` is moved. -/
theorem TakeK.pc {a : Int64} {rS : Scc.Sem.Range} {s s' : State} (h : TakeK a rS s s') : s.st.2 = a := h.1

/-- No move off the site. -/
theorem TakeK.not_of_pc {a : Int64} {rS : Scc.Sem.Range} {s : State} (h : s.st.2 ≠ a) : ∀ s', ¬ TakeK a rS s s' :=
  fun _ hk => h hk.1

/-- The state after a take, at a cell of size `z` (the site's `nop`): the
memory `takeMem`, the pc past the cell. -/
theorem TakeK.eq {a : Int64} {rS : Scc.Sem.Range} {s s' : State} {d : Directive} {z : Nat} (h : TakeK a rS s s')
    (hc : CellAt s d z) :
    ∃ pm, s' = { s with st := (takeMem pm rS s.st.1, s.st.2 + Int64.ofNat z) } := by
  obtain ⟨-, pm, rfl⟩ := h
  refine ⟨pm, ?_⟩
  have := Scc.Sem.X64.nextPc_of_cellAt hc
  show { s with st := (takeMem pm rS s.st.1, Scc.Sem.X64.nextPc { s with st := (takeMem pm rS s.st.1, s.st.2) }) } = _
  rw [show Scc.Sem.X64.nextPc { s with st := (takeMem pm rS s.st.1, s.st.2) } = Scc.Sem.X64.nextPc s from rfl, this]

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

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64}

/-- **The take node**: at the site's `nop` (pc `a`), from every pair of the
node, every take lands at node `n'` past the `nop`, with the region related
to the same abstract state (`hA`: the take keeps the region's cells and
gives the new frame condition `F'`) and a local run of the source to `n'`'s
invariant (`hedge`). No pair of the node is left unmoved, so no `Out` row is
asked. -/
theorem take_ndW {W : Frag isa} {a : Int64} {rS : Scc.Sem.Range} {R R' : Region} {F F' : MachineData → Prop}
    {n n' : ND} (hpc : n.pc = a)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc nopBlk)
    (hW : ∀ s c, At exe endPc R F n s c → W s c)
    (hA : ∀ m σ pm, Abs R n.o m σ → F m → Abs R' n'.o (takeMem pm rS m) σ ∧ F' (takeMem pm rS m))
    (hedge : ∀ σ c, n.J σ c → n'.pc = n.pc + Int64.ofNat 1 ∧ ∃ c', LocalRun p c c' ∧ n'.J σ c') :
    SegW W (TakeK a rS) p lbl ms (At exe endPc R F n) (At exe endPc R' F' n') := by
  refine SegW.stepK hW fun s c ⟨he, hn, hdc, hpc', σ, hAb, hD, hJ⟩ => ⟨fun hk => ?_, fun s' hk => ?_⟩
  · exact (hk _ ⟨hpc'.trans hpc, ∅, rfl⟩).elim
  · have hc : CellAt s (.instr (.regular .W64 .W64 (.nop 1))) 1 :=
      (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc']; simp [cellOff])
    obtain ⟨pm, rfl⟩ := hk.eq hc
    obtain ⟨hpc'', c', hr, hJ'⟩ := hedge σ c hJ
    obtain ⟨hA', hF'⟩ := hA _ σ pm hAb hD
    exact ⟨c', hr, he, hn, hdc, by rw [hpc', hpc''], σ, hA', hF', hJ'⟩

end TakeNode

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
  | .entry => ⟨lab entryL, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g) σ⟩
  | .cls => ⟨lab clsL, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g) σ⟩
  | .j1 => ⟨lab clsL + Int64.ofNat 13, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g) σ⟩
  | .d0 => ⟨lab doneL, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g) σ⟩
  | .d7 => ⟨lab doneL + Int64.ofNat 7, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g) σ ∧
      σ.regs.rax.toBitVec = freeNA lab⟩
  | .d26 => ⟨lab doneL + Int64.ofNat 26, oI, fun σ c => c = q.c0 ∧ Fr q.g (s2 q.g (freeNA lab)) σ⟩
  | .d33 => ⟨lab doneL + Int64.ofNat 33, oI, fun σ c => c = q.c0 ∧ Fr q.g (s2 q.g (freeNA lab)) σ⟩
  | .d52 => ⟨lab doneL + Int64.ofNat 52, oI, fun σ c => c = q.c0 ∧ Fr q.g (s2 q.g (freeNA lab)) σ⟩
  | .d59 => ⟨lab doneL + Int64.ofNat 59, oI, fun σ c => c = q.c0 ∧ Fr q.g (s2 q.g (freeNA lab)) σ ∧
      σ.regs.rax.toBitVec = lockA lab⟩
  | .sp0 => ⟨lab spinL, oI, fun σ c => c = q.c0 ∧ Fr q.g (s3 q.g (freeNA lab) (lockA lab)) σ⟩
  | .swp => ⟨swpPc lab, oI, fun σ c => c = q.c0 ∧ Fr q.g (s3 q.g (freeNA lab) (lockA lab)) σ ∧
      σ.regs.rcx.toBitVec = lockA lab ∧ σ.regs.rax.toBitVec = 1#64⟩
  | .sp14 => ⟨lab spinL + Int64.ofNat 14, oI, fun σ c => c = q.c0 ∧ Fr q.g (s3 q.g (freeNA lab) (lockA lab)) σ ∧
      σ.regs.rax.toBitVec = 0#64⟩
  | .lk0 => ⟨lab lockedL, oI, fun σ c => c = q.c0 ∧ Fr q.g (s3 q.g (freeNA lab) (lockA lab)) σ⟩
  | .ldn => ⟨freeNPc lab, oI, fun σ c => c = q.c0 ∧ Fr q.g (s3 q.g (freeNA lab) (lockA lab)) σ ∧
      σ.regs.rcx.toBitVec = freeNA lab⟩
  | .lk7 => ⟨lab lockedL + Int64.ofNat 7, oI, fun σ c => c = q.c0 ∧ Fr q.g (s3 q.g (freeNA lab) (lockA lab)) σ ∧
      σ.regs.rax.toBitVec = 0#64⟩
  | .b0 => ⟨lab bumpL, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g) σ⟩
  | .b7 => ⟨lab bumpL + Int64.ofNat 7, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g) σ ∧
      σ.regs.rax.toBitVec = lockA lab⟩
  | .unl => ⟨unlPc lab, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g) σ ∧ σ.regs.rcx.toBitVec = lockA lab ∧
      σ.regs.rax.toBitVec = 0#64⟩
  | .b31 => ⟨lab bumpL + Int64.ofNat 31, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g) σ⟩
  | .b38 => ⟨lab bumpL + Int64.ofNat 38, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g) σ ∧
      σ.regs.rax.toBitVec = nextA lab⟩
  | .nxt => ⟨nextPc lab, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g) σ ∧ σ.regs.rcx.toBitVec = nextA lab ∧
      σ.regs.rax.toBitVec = size0⟩
  | .b61 => ⟨lab bumpL + Int64.ofNat 61, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g) σ ∧
      σ.regs.rax.toBitVec = q.k0⟩
  | .b108 => ⟨lab bumpL + Int64.ofNat 108, oI, fun σ c => c = q.c0 ∧ Fr q.g (s4 q.g q.k0) σ⟩
  | .ok0 => ⟨lab StackTake.okL, oI, fun σ c => c = q.c0 ∧ Fr q.g (s4 q.g q.k0) σ⟩
  | .ok7 => ⟨lab StackTake.okL + Int64.ofNat 7, oI, fun σ c => c = q.c0 ∧ Fr q.g (s4 q.g q.k0) σ ∧
      σ.regs.rax.toBitVec = stacksA lab⟩
  | .tk => ⟨lab takenL, oI, fun σ c => c = q.c0 ∧ Fr q.g (s5 q.g q.k0 (stacksA lab)) σ⟩
  | .site => ⟨lab siteL, oI, fun σ c => c = q.c0 ∧ Fr q.g (s5 q.g q.k0 (stacksA lab)) σ ∧
      σ.regs.rdi.toBitVec = stacksA lab + q.k0 ∧ σ.regs.rsi.toBitVec = size0⟩
  | .ret => ⟨lab siteL + Int64.ofNat 1, oI, fun σ c => c = q.c0 ∧ Fr q.g (s5 q.g q.k0 (stacksA lab)) σ⟩

/-- **The exit**: at the return address, `Post`. -/
def takeX : Unit → ND
  | () => ⟨Int64.ofBitVec q.g.ra, StackTake.oR, fun σ c => c = q.c0 ∧ StackTake.Post q.g q.k0 (stacksA lab) σ⟩

open StackTake in
/-- **The nodes, before or after the take** (`b`): `takeN`, the node past
the site holding only after it (`b = true`). -/
def takeNG (b : Bool) : TK → ND
  | .e => ⟨lab fnL, oE, fun σ c => c = q.c0 ∧ Pre q.g q.k0 σ⟩
  | .entry => ⟨lab entryL, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g) σ⟩
  | .cls => ⟨lab clsL, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g) σ⟩
  | .j1 => ⟨lab clsL + Int64.ofNat 13, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g) σ⟩
  | .d0 => ⟨lab doneL, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g) σ⟩
  | .d7 => ⟨lab doneL + Int64.ofNat 7, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g) σ ∧
      σ.regs.rax.toBitVec = freeNA lab⟩
  | .d26 => ⟨lab doneL + Int64.ofNat 26, oI, fun σ c => c = q.c0 ∧ Fr q.g (s2 q.g (freeNA lab)) σ⟩
  | .d33 => ⟨lab doneL + Int64.ofNat 33, oI, fun σ c => c = q.c0 ∧ Fr q.g (s2 q.g (freeNA lab)) σ⟩
  | .d52 => ⟨lab doneL + Int64.ofNat 52, oI, fun σ c => c = q.c0 ∧ Fr q.g (s2 q.g (freeNA lab)) σ⟩
  | .d59 => ⟨lab doneL + Int64.ofNat 59, oI, fun σ c => c = q.c0 ∧ Fr q.g (s2 q.g (freeNA lab)) σ ∧
      σ.regs.rax.toBitVec = lockA lab⟩
  | .sp0 => ⟨lab spinL, oI, fun σ c => c = q.c0 ∧ Fr q.g (s3 q.g (freeNA lab) (lockA lab)) σ⟩
  | .swp => ⟨swpPc lab, oI, fun σ c => c = q.c0 ∧ Fr q.g (s3 q.g (freeNA lab) (lockA lab)) σ ∧
      σ.regs.rcx.toBitVec = lockA lab ∧ σ.regs.rax.toBitVec = 1#64⟩
  | .sp14 => ⟨lab spinL + Int64.ofNat 14, oI, fun σ c => c = q.c0 ∧ Fr q.g (s3 q.g (freeNA lab) (lockA lab)) σ ∧
      σ.regs.rax.toBitVec = 0#64⟩
  | .lk0 => ⟨lab lockedL, oI, fun σ c => c = q.c0 ∧ Fr q.g (s3 q.g (freeNA lab) (lockA lab)) σ⟩
  | .ldn => ⟨freeNPc lab, oI, fun σ c => c = q.c0 ∧ Fr q.g (s3 q.g (freeNA lab) (lockA lab)) σ ∧
      σ.regs.rcx.toBitVec = freeNA lab⟩
  | .lk7 => ⟨lab lockedL + Int64.ofNat 7, oI, fun σ c => c = q.c0 ∧ Fr q.g (s3 q.g (freeNA lab) (lockA lab)) σ ∧
      σ.regs.rax.toBitVec = 0#64⟩
  | .b0 => ⟨lab bumpL, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g) σ⟩
  | .b7 => ⟨lab bumpL + Int64.ofNat 7, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g) σ ∧
      σ.regs.rax.toBitVec = lockA lab⟩
  | .unl => ⟨unlPc lab, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g) σ ∧ σ.regs.rcx.toBitVec = lockA lab ∧
      σ.regs.rax.toBitVec = 0#64⟩
  | .b31 => ⟨lab bumpL + Int64.ofNat 31, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g) σ⟩
  | .b38 => ⟨lab bumpL + Int64.ofNat 38, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g) σ ∧
      σ.regs.rax.toBitVec = nextA lab⟩
  | .nxt => ⟨nextPc lab, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g) σ ∧ σ.regs.rcx.toBitVec = nextA lab ∧
      σ.regs.rax.toBitVec = size0⟩
  | .b61 => ⟨lab bumpL + Int64.ofNat 61, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g) σ ∧
      σ.regs.rax.toBitVec = q.k0⟩
  | .b108 => ⟨lab bumpL + Int64.ofNat 108, oI, fun σ c => c = q.c0 ∧ Fr q.g (s4 q.g q.k0) σ⟩
  | .ok0 => ⟨lab StackTake.okL, oI, fun σ c => c = q.c0 ∧ Fr q.g (s4 q.g q.k0) σ⟩
  | .ok7 => ⟨lab StackTake.okL + Int64.ofNat 7, oI, fun σ c => c = q.c0 ∧ Fr q.g (s4 q.g q.k0) σ ∧
      σ.regs.rax.toBitVec = stacksA lab⟩
  | .tk => ⟨lab takenL, oI, fun σ c => c = q.c0 ∧ Fr q.g (s5 q.g q.k0 (stacksA lab)) σ⟩
  | .site => ⟨lab siteL, oI, fun σ c => c = q.c0 ∧ Fr q.g (s5 q.g q.k0 (stacksA lab)) σ ∧
      σ.regs.rdi.toBitVec = stacksA lab + q.k0 ∧ σ.regs.rsi.toBitVec = size0⟩
  | .ret => ⟨lab siteL + Int64.ofNat 1, oI, fun σ c => b = true ∧ c = q.c0 ∧ Fr q.g (s5 q.g q.k0 (stacksA lab)) σ⟩

/-- **The exit, after the take**: at the return address, `Post`. -/
def takeXG (b : Bool) : Unit → ND
  | () => ⟨Int64.ofBitVec q.g.ra, StackTake.oR, fun σ c => b = true ∧ c = q.c0 ∧
      StackTake.Post q.g q.k0 (stacksA lab) σ⟩

end Take

/-- The lock's swap is `xchgDir`, the free count's load `ldDir`, the next
offset's add `xaddDir`. -/
theorem swpBlk_eq : ((parse("xchgq %rax, (%rcx)")).zip [3] : List (Directive × Nat)) = [(xchgDir .rcx 0 .rax, 3)] := by
  decide
theorem ldnBlk_eq : ((parse("movq (%rcx), %rax")).zip [3] : List (Directive × Nat)) = [(ldDir .rcx 0 .rax, 3)] := by
  decide
theorem nxtBlk_eq : ((parse("lock xaddq %rax, (%rcx)")).zip [5] : List (Directive × Nat)) =
    [(xaddDir .rcx 0 .rax, 5)] := by
  decide

/-- **The take's accesses to its own words**: the lock's swap `0 → 1`
(`lock1`, `ownLock`, `ownXchg_nd`), the free count's load of `0` (`freeN`,
`ownFreeN`, `ownLd_nd`), the lock's release (`lock0`, `rtst_nd`) and the
next offset's add `k0 → k0 + size0` (`next`, `ownNext`, `ownXadd_nd`). The
`own*` fields are named hypotheses until `ms.own` is wired; each gives the
word's value before the access at its pc. -/
structure TakeOk (ms : MemSide isa) (F : MachineData → Prop) (exe : _root_.Executable) (endPc : Int64)
    (k0 : BitVec 64) : Prop where
  lock1 : StOk ms F (lockA (_root_.Executable.labels exe).label) 1#64
  freeN : LdOk ms F (freeNA (_root_.Executable.labels exe).label)
  lock0 : StOk ms F (lockA (_root_.Executable.labels exe).label) 0#64
  next : StOk ms F (nextA (_root_.Executable.labels exe).label) (k0 + StackTake.size0)
  ownLock : OwnAt ms exe endPc (StackTake.swpPc (_root_.Executable.labels exe).label)
    (lockA (_root_.Executable.labels exe).label) 0#64
  ownFreeN : OwnAt ms exe endPc (StackTake.freeNPc (_root_.Executable.labels exe).label)
    (freeNA (_root_.Executable.labels exe).label) 0#64
  ownNext : OwnAt ms exe endPc (StackTake.nextPc (_root_.Executable.labels exe).label)
    (nextA (_root_.Executable.labels exe).label) k0

theorem TakeOk.mono {ms : MemSide isa} {F F' : MachineData → Prop} {exe : _root_.Executable} {endPc : Int64}
    {k0 : BitVec 64} (h : TakeOk ms F exe endPc k0) (hFF : ∀ m, F' m → F m) : TakeOk ms F' exe endPc k0 :=
  ⟨h.lock1.mono hFF, h.freeN.mono hFF, h.lock0.mono hFF, h.next.mono hFF, h.ownLock, h.ownFreeN, h.ownNext⟩

section TakeProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F F0 : MachineData → Prop}

set_option hygiene false in
/-- A block node of `scc_rt_stack_take`: the block, its `okBlk`, its code; the edge is left. -/
local macro "knode " b:ident ok:ident l:term:max k:term:max : tactic =>
  `(tactic| refine seg_nd (by simp [$b:ident]) $ok hF hR hlo hhi
    (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) (by first | rfl | exact ofNat_zero' _))
      fun σ c hJ => ⟨c, .refl c, ?_⟩)

set_option hygiene false in
/-- A node at a label's address into `%rax` at `l + k`, to node `j`; the
invariant's facts are left. -/
local macro "lnode " L:term:max l:term:max k:term:max j:term:max : tactic =>
  `(tactic| refine si_nd (si := .leaRip .rax $L) (z := 7) rfl hF
    (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) (by first | rfl | exact ofNat_zero' _))
      fun σ c hJ => ⟨c, .refl c, .inl ⟨$j, ?_, rfl, ?_⟩⟩)

/-- **`scc_rt_stack_take` is one segment** in any valid layout of
`ret0Cells`, from its entry to its return, for any region holding its frame
of 192, the saved `%rbp` and the return address, and any frame condition
implying `F0`, given room for the stack below `2^29` (`hk`) and its
accesses to its own words (`htk`). -/
theorem stack_take_seg (hp : Lays exe SccCode.ret0Cells) (hend : endPc = endOf exe SccCode.ret0Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -200) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TakeG) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (htk : TakeOk ms F0 exe endPc q.k0) :
    Seg p lbl ms (At exe endPc R F (takeN (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x, At exe endPc R F (takeX (_root_.Executable.labels exe).label q x) s c) := by
  have hin' := StackTake.ret0_stackTakeIn
  simp only [StackTake.stackTakeIn, AllocTcb.siAt, unlBlk_eq, swpBlk_eq, ldnBlk_eq, nxtBlk_eq,
    Bool.and_eq_true] at hin'
  have eEntry := label_labelGapB (a := StackTake.fnL) (b := StackTake.entryL) (off := 15) hp (by simp only [hin'])
  have eSite := label_labelGapB (a := StackTake.takenL) (b := StackTake.siteL) (off := 11) hp (by simp only [hin'])
  let lab := (_root_.Executable.labels exe).label
  refine fn_seg (N := takeN _ q) (E := takeX _ q) (fun i => ?_) TK.e
  cases i
  case e =>
    knode StackTake.stPro StackTake.stPro_ok StackTake.fnL 0
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stPro_walk lab _ hJ
    exact .inl ⟨TK.entry, by rw [h1]; exact eEntry, by rw [h2]; rfl, rfl, h3⟩
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
    knode StackTake.stJ1 StackTake.stJ1_ok StackTake.clsL 13
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stJ1_walk lab _ hJ
    exact .inl ⟨TK.d0, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case d0 =>
    lnode "scc_rt_stack_free_n" StackTake.doneL 0 TK.d7
    · show _ + Int64.ofNat 7 = _ + Int64.ofNat 7; rfl
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case d7 =>
    knode StackTake.stFreeN StackTake.stFreeN_ok StackTake.doneL 7
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stFreeN_walk lab _ hJ ha
    exact .inl ⟨TK.d26, by rw [h1]; exact ofNat_add' _ 7 19, by rw [h2]; rfl, rfl, h3⟩
  case d26 =>
    lnode "scc_rt_stack_free" StackTake.doneL 26 TK.d33
    · exact ofNat_add' _ 26 7
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ⟩
  case d33 =>
    knode StackTake.stFree StackTake.stFree_ok StackTake.doneL 33
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stFree_walk lab _ hJ
    exact .inl ⟨TK.d52, by rw [h1]; exact ofNat_add' _ 33 19, by rw [h2]; rfl, rfl, h3⟩
  case d52 =>
    lnode "scc_rt_stack_lock" StackTake.doneL 52 TK.d59
    · exact ofNat_add' _ 52 7
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case d59 =>
    knode StackTake.stLock StackTake.stLock_ok StackTake.doneL 59
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stLock_walk lab _ hJ ha
    exact .inl ⟨TK.sp0, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case sp0 =>
    knode StackTake.stSwp StackTake.stSwp_ok StackTake.spinL 0
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stSwp_walk lab _ hJ
    exact .inl ⟨TK.swp, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case swp =>
    refine ownXchg_nd (b := .rcx) (k := 0) (r := .rax) (z := 3) (by decide) hF
      (code_field hp hend (by simp only [hin']) (l := StackTake.spinL) (off := 11) rfl) htk.ownLock
      fun m σ c _ hD hJ => ?_
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ, hc, ha⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = lockA (_root_.Executable.labels exe).label := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hv : σ.regs.get64 .rax = 1#64 := by rw [← ha]; rfl
    rw [hb, hv]
    exact ⟨rfl, htk.lock1.rt, htk.lock1.mp, htk.lock1.G, htk.lock1.unmapped m (hFF m hD),
      q.c0, .refl q.c0,
        .inl ⟨TK.sp14, ofNat_add' _ 11 3, rfl, rfl, by simpa [ownStep, StackTake.Fr, Reg64s.set64] using hJ,
          by simp [ownStep, Reg64s.set64]⟩⟩
  case sp14 =>
    knode StackTake.stSpin StackTake.stSpin_ok StackTake.spinL 14
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stSpin_walk lab _ hJ ha
    exact .inl ⟨TK.lk0, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case lk0 =>
    knode StackTake.stLdN StackTake.stLdN_ok StackTake.lockedL 0
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4⟩ := StackTake.stLdN_walk lab _ hJ
    exact .inl ⟨TK.ldn, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3, h4⟩
  case ldn =>
    refine ownLd_nd (b := .rcx) (k := 0) (r := .rax) (z := 3) (by decide) hF
      (code_field hp hend (by simp only [hin']) (l := StackTake.lockedL) (off := 4) rfl) htk.ownFreeN
      fun m σ c _ hD hJ => ?_
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ, hc⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = freeNA (_root_.Executable.labels exe).label := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    rw [hb]
    exact ⟨rfl, htk.freeN.rt, htk.freeN.mp, htk.freeN.unmapped m (hFF m hD),
      q.c0, .refl q.c0,
        .inl ⟨TK.lk7, ofNat_add' _ 4 3, rfl, rfl, by simpa [ownStep, StackTake.Fr, Reg64s.set64] using hJ,
          by simp [ownStep, Reg64s.set64]⟩⟩
  case lk7 =>
    knode StackTake.stEmpty StackTake.stEmpty_ok StackTake.lockedL 7
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stEmpty_walk lab _ hJ ha
    exact .inl ⟨TK.b0, h1.symm, by rw [h2]; rfl, rfl, h3.mono (StackTake.s3_s0 _ _ _)⟩
  case b0 =>
    lnode "scc_rt_stack_lock" StackTake.bumpL 0 TK.b7
    · show _ + Int64.ofNat 7 = _ + Int64.ofNat 7; rfl
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case b7 =>
    knode StackTake.stUnl StackTake.stUnl_ok StackTake.bumpL 7
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stUnl_walk lab _ hJ ha
    exact .inl ⟨TK.unl, by rw [h1]; exact ofNat_add' _ 7 21, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case unl =>
    refine rtst_nd (b := .rcx) (k := 0) (r := .rax) (z := 3)
      (code_field hp hend (by simp only [hin']) (l := StackTake.bumpL) (off := 28) rfl)
      fun m σ c _ hD hJ => ?_
    obtain ⟨rfl, hJ, hc, ha⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = lockA (_root_.Executable.labels exe).label := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hv : σ.regs.get64 .rax = 0#64 := by rw [← ha]; rfl
    rw [hb, hv]
    exact ⟨htk.lock0.rt, htk.lock0.mp, htk.lock0.G, htk.lock0.unmapped m (hFF m hD),
      q.c0,
      .refl q.c0, .inl ⟨TK.b31, ofNat_add' _ 28 3, rfl, rfl, hJ⟩⟩
  case b31 =>
    lnode "scc_rt_stack_next" StackTake.bumpL 31 TK.b38
    · exact ofNat_add' _ 31 7
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case b38 =>
    knode StackTake.stAdd StackTake.stAdd_ok StackTake.bumpL 38
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stAdd_walk lab _ hJ ha
    exact .inl ⟨TK.nxt, by rw [h1]; exact ofNat_add' _ 38 18, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case nxt =>
    refine ownXadd_nd (b := .rcx) (k := 0) (r := .rax) (z := 5) (by decide) hF
      (code_field hp hend (by simp only [hin']) (l := StackTake.bumpL) (off := 56) rfl) htk.ownNext
      fun m σ c _ hD hJ => ?_
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ, hc, ha⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = nextA (_root_.Executable.labels exe).label := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hv : σ.regs.get64 .rax = StackTake.size0 := by rw [← ha]; rfl
    rw [hb, hv]
    exact ⟨rfl, htk.next.rt, htk.next.mp, htk.next.G, htk.next.unmapped m (hFF m hD),
      q.c0, .refl q.c0, fun fl =>
        .inl ⟨TK.b61, ofNat_add' _ 56 5, rfl, rfl, by simpa [ownStep, StackTake.Fr, Reg64s.set64] using hJ,
          by simp [ownStep, Reg64s.set64]⟩⟩
  case b61 =>
    knode StackTake.stBnd StackTake.stBnd_ok StackTake.bumpL 61
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stBnd_walk lab _ hJ ha hk
    exact .inl ⟨TK.b108, by rw [h1]; exact ofNat_add' _ 61 47, by rw [h2]; rfl, rfl, h3⟩
  case b108 =>
    knode StackTake.stJ2 StackTake.stJ2_ok StackTake.bumpL 108
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stJ2_walk lab _ hJ
    exact .inl ⟨TK.ok0, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case ok0 =>
    lnode "scc_rt_stacks" StackTake.okL 0 TK.ok7
    · show _ + Int64.ofNat 7 = _ + Int64.ofNat 7; rfl
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case ok7 =>
    knode StackTake.stOk StackTake.stOk_ok StackTake.okL 7
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stOk_walk lab _ hJ ha
    exact .inl ⟨TK.tk, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case tk =>
    knode StackTake.stSite StackTake.stSite_ok StackTake.takenL 0
    dsimp only [takeN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stSite_walk lab _ hJ
    exact .inl ⟨TK.site, by rw [h1]; exact eSite, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case site =>
    refine seg_nd (by simp [nopBlk]) nopBlk_ok hF hR hlo hhi
      (code_field hp hend (by simp only [nopBlk, hin']) (l := StackTake.siteL) (off := 0) (ofNat_zero' _))
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    dsimp only [takeN] at hJ ⊢
    rw [nopBlk_run]
    exact .inl ⟨TK.ret, rfl, rfl, hJ.1, hJ.2.1⟩
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
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hFb hR hlo hhi
    (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) (by first | rfl | exact ofNat_zero' _))
      $w fun σ c hJ => ⟨c, .refl c, ?_⟩)

set_option hygiene false in
/-- A node at a label's address into `%rax` at `l + k`, to node `j`, inside
`W`; the invariant's facts are left. -/
local macro "lnodeW " L:term:max l:term:max k:term:max j:term:max w:term:max : tactic =>
  `(tactic| refine si_ndW (si := .leaRip .rax $L) (z := 7) rfl hFb
    (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) (by first | rfl | exact ofNat_zero' _))
      $w fun σ c hJ => ⟨c, .refl c, .inl ⟨$j, ?_, rfl, ?_⟩⟩)

/-- A frame condition, and after the take (`b`) the stack range in private
memory. -/
def takeF (F : MachineData → Prop) (rS : Scc.Sem.Range) (b : Bool) (m : MachineData) : Prop :=
  F m ∧ (b = true → StackM rS m)

/-- **`scc_rt_stack_take`'s node obligations** inside `W`, not moved by `K`
(`NodeW`, `BlkW`; the take site's in `W`). The block past the site is after
the take, its frame condition also `M` (the stack range in private memory,
`StackM`, at the use). -/
def TakeW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F M : MachineData → Prop) (q : TakeG) : TK → Prop
  | .e => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .e)
      StackTake.stPro
  | .entry => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .entry)
      StackTake.stInit
  | .cls => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .cls)
      StackTake.stCls
  | .j1 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .j1)
      StackTake.stJ1
  | .d0 => NodeW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .d0)
  | .d7 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .d7)
      StackTake.stFreeN
  | .d26 => NodeW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .d26)
  | .d33 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .d33)
      StackTake.stFree
  | .d52 => NodeW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .d52)
  | .d59 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .d59)
      StackTake.stLock
  | .sp0 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .sp0)
      StackTake.stSwp
  | .swp => NodeW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .swp)
  | .sp14 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .sp14)
      StackTake.stSpin
  | .lk0 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .lk0)
      StackTake.stLdN
  | .ldn => NodeW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .ldn)
  | .lk7 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .lk7)
      StackTake.stEmpty
  | .b0 => NodeW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .b0)
  | .b7 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .b7)
      StackTake.stUnl
  | .unl => NodeW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .unl)
  | .b31 => NodeW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .b31)
  | .b38 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .b38)
      StackTake.stAdd
  | .nxt => NodeW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .nxt)
  | .b61 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .b61)
      StackTake.stBnd
  | .b108 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .b108)
      StackTake.stJ2
  | .ok0 => NodeW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .ok0)
  | .ok7 => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .ok7)
      StackTake.stOk
  | .tk => BlkW W K exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .tk)
      StackTake.stSite
  | .site => ∀ s c, At exe endPc R F (takeNG (_root_.Executable.labels exe).label q true .site) s c → W s c
  | .ret => BlkW W K exe endPc R (fun m => F m ∧ M m) (takeNG (_root_.Executable.labels exe).label q true .ret)
      StackTake.stRet

omit [Executable.ValidLayout exe] in
/-- A node obligation under a weaker frame condition holds under a stronger one. -/
theorem nodeW_mono {W : Frag isa} {K : State → State → Prop} {F' : MachineData → Prop} {n : ND}
    (h : NodeW W K exe endPc R F n) (hFF : ∀ m, F' m → F m) : NodeW W K exe endPc R F' n :=
  fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h s c ⟨he, hn, hdc, hpc, σ, hA, hFF _ hD, hJ⟩

omit [Executable.ValidLayout exe] in
/-- A block obligation under a weaker frame condition holds under a stronger one. -/
theorem blkW_mono {W : Frag isa} {K : State → State → Prop} {F' : MachineData → Prop} {n : ND}
    {blk : List (Directive × Nat)} (h : BlkW W K exe endPc R F n blk) (hFF : ∀ m, F' m → F m) :
    BlkW W K exe endPc R F' n blk :=
  fun s σ c he hn hdc hpc hA hD hJ => h s σ c he hn hdc hpc hA (hFF _ hD) hJ

omit [Executable.ValidLayout exe] in
theorem TakeW.mono {W : Frag isa} {K : State → State → Prop} {F' M : MachineData → Prop} {q : TakeG}
    {i : TK} (h : TakeW W K exe endPc R F M q i) (hFF : ∀ m, F' m → F m) : TakeW W K exe endPc R F' M q i := by
  cases i <;> dsimp only [TakeW] at h ⊢
  all_goals first
    | exact blkW_mono h hFF
    | exact blkW_mono h fun m h => ⟨hFF m h.1, h.2⟩
    | exact nodeW_mono h hFF
    | exact fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h s c ⟨he, hn, hdc, hpc, σ, hA, hFF _ hD, hJ⟩

/-- **`scc_rt_stack_take` is one segment inside `W`, the take its outside
move**: `stack_take_seg` with the take site the kernel's take of `rS`
(`TakeK`, `take_ndW`) instead of a `nop`, so at the return `rS` is in
private memory (`StackM`). Given the node obligations (`hW`), the region's
cells off `rS` (`hRS`), every aligned word of `rS` off the region (`hout`),
and the frame condition kept by the take (`hFt`). -/
theorem stack_take_segW {W : Frag isa} {rS : Scc.Sem.Range} (hp : Lays exe SccCode.ret0Cells)
    (hend : endPc = endOf exe SccCode.ret0Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -200) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TakeG) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (htk : TakeOk ms F0 exe endPc q.k0)
    (hW : ∀ i, TakeW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F (StackM rS)
      q i)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (takeNG (_root_.Executable.labels exe).label q false .e))
      (fun s c => ∃ x, At exe endPc R (fun m => F m ∧ StackM rS m)
        (takeXG (_root_.Executable.labels exe).label q true x) s c) := by
  have hin' := StackTake.ret0_stackTakeIn
  simp only [StackTake.stackTakeIn, AllocTcb.siAt, unlBlk_eq, swpBlk_eq, ldnBlk_eq, nxtBlk_eq,
    Bool.and_eq_true] at hin'
  have eEntry := label_labelGapB (a := StackTake.fnL) (b := StackTake.entryL) (off := 15) hp (by simp only [hin'])
  have eSite := label_labelGapB (a := StackTake.takenL) (b := StackTake.siteL) (off := 11) hp (by simp only [hin'])
  let lab := (_root_.Executable.labels exe).label
  have hAbs : ∀ {m : MachineData} {σ : AS} {pm : _root_.Mem 64}, Abs R StackTake.oI m σ →
      Abs R StackTake.oI (takeMem pm rS m) σ := fun hA =>
    ⟨hA.regs, hA.zmms, hA.status, hA.so, fun k hk => by rw [loadInt_takeMem (hRS k hk)]; exact hA.slot k hk⟩
  have hSM := stackM_stable hfit hout
  refine ((fn_seg_gW (exe := exe) (endPc := endPc) (Rg := fun _ => R) (Fg := takeF F rS)
      (N := takeNG lab q) (E := takeXG lab q)
    (fun b i => ?_) false TK.e).mono_pre fun s c h => ?_).mono_post fun s c h => ?_
  rotate_left
  · obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
    exact ⟨he, hn, hdc, hpc, σ, hA, ⟨hD, nofun⟩, hJ⟩
  · obtain ⟨g, x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM⟩, hb, hJ⟩ := h
    subst hb
    exact ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM rfl⟩, rfl, hJ⟩
  have hFb : FStable R (takeF F rS b) := fun m m' ⟨hD, hM⟩ hd => ⟨hF m m' hD hd, fun hb => hSM m m' (hM hb) hd⟩
  have hFFb : ∀ m, takeF F rS b m → F0 m := fun m h => hFF m h.1
  have hWb : ∀ i, TakeW W (TakeK (lab StackTake.siteL) rS) exe endPc R (takeF F rS b) (StackM rS) q i :=
    fun i => (hW i).mono fun m h => h.1
  cases i
  case e =>
    refine seg_fixW b ?_
    knodeW StackTake.stPro StackTake.stPro_ok StackTake.fnL 0 (hWb TK.e)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stPro_walk lab _ hJ
    exact .inl ⟨TK.entry, by rw [h1]; exact eEntry, by rw [h2]; rfl, rfl, h3⟩
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
    knodeW StackTake.stJ1 StackTake.stJ1_ok StackTake.clsL 13 (hWb TK.j1)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stJ1_walk lab _ hJ
    exact .inl ⟨TK.d0, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case d0 =>
    refine seg_fixW b ?_
    lnodeW "scc_rt_stack_free_n" StackTake.doneL 0 TK.d7 (hWb TK.d0)
    · show _ + Int64.ofNat 7 = _ + Int64.ofNat 7; rfl
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case d7 =>
    refine seg_fixW b ?_
    knodeW StackTake.stFreeN StackTake.stFreeN_ok StackTake.doneL 7 (hWb TK.d7)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stFreeN_walk lab _ hJ ha
    exact .inl ⟨TK.d26, by rw [h1]; exact ofNat_add' _ 7 19, by rw [h2]; rfl, rfl, h3⟩
  case d26 =>
    refine seg_fixW b ?_
    lnodeW "scc_rt_stack_free" StackTake.doneL 26 TK.d33 (hWb TK.d26)
    · exact ofNat_add' _ 26 7
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ⟩
  case d33 =>
    refine seg_fixW b ?_
    knodeW StackTake.stFree StackTake.stFree_ok StackTake.doneL 33 (hWb TK.d33)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stFree_walk lab _ hJ
    exact .inl ⟨TK.d52, by rw [h1]; exact ofNat_add' _ 33 19, by rw [h2]; rfl, rfl, h3⟩
  case d52 =>
    refine seg_fixW b ?_
    lnodeW "scc_rt_stack_lock" StackTake.doneL 52 TK.d59 (hWb TK.d52)
    · exact ofNat_add' _ 52 7
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case d59 =>
    refine seg_fixW b ?_
    knodeW StackTake.stLock StackTake.stLock_ok StackTake.doneL 59 (hWb TK.d59)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stLock_walk lab _ hJ ha
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
    refine ownXchg_ndW (b := .rcx) (k := 0) (r := .rax) (z := 3) (by decide) hFb
      (code_field hp hend (by simp only [hin']) (l := StackTake.spinL) (off := 11) rfl) htk.ownLock
      (hWb TK.swp) fun m σ c _ hD hJ => ?_
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, hc, ha⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = lockA (_root_.Executable.labels exe).label := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hv : σ.regs.get64 .rax = 1#64 := by rw [← ha]; rfl
    rw [hb, hv]
    exact ⟨rfl, htk.lock1.rt, htk.lock1.mp, htk.lock1.G, htk.lock1.unmapped m (hFFb m hD),
      q.c0, .refl q.c0,
        .inl ⟨TK.sp14, ofNat_add' _ 11 3, rfl, rfl, by simpa [ownStep, StackTake.Fr, Reg64s.set64] using hJ,
          by simp [ownStep, Reg64s.set64]⟩⟩
  case sp14 =>
    refine seg_fixW b ?_
    knodeW StackTake.stSpin StackTake.stSpin_ok StackTake.spinL 14 (hWb TK.sp14)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stSpin_walk lab _ hJ ha
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
    refine ownLd_ndW (b := .rcx) (k := 0) (r := .rax) (z := 3) (by decide) hFb
      (code_field hp hend (by simp only [hin']) (l := StackTake.lockedL) (off := 4) rfl) htk.ownFreeN
      (hWb TK.ldn) fun m σ c _ hD hJ => ?_
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, hc⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = freeNA (_root_.Executable.labels exe).label := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    rw [hb]
    exact ⟨rfl, htk.freeN.rt, htk.freeN.mp, htk.freeN.unmapped m (hFFb m hD),
      q.c0, .refl q.c0,
        .inl ⟨TK.lk7, ofNat_add' _ 4 3, rfl, rfl, by simpa [ownStep, StackTake.Fr, Reg64s.set64] using hJ,
          by simp [ownStep, Reg64s.set64]⟩⟩
  case lk7 =>
    refine seg_fixW b ?_
    knodeW StackTake.stEmpty StackTake.stEmpty_ok StackTake.lockedL 7 (hWb TK.lk7)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stEmpty_walk lab _ hJ ha
    exact .inl ⟨TK.b0, h1.symm, by rw [h2]; rfl, rfl, h3.mono (StackTake.s3_s0 _ _ _)⟩
  case b0 =>
    refine seg_fixW b ?_
    lnodeW "scc_rt_stack_lock" StackTake.bumpL 0 TK.b7 (hWb TK.b0)
    · show _ + Int64.ofNat 7 = _ + Int64.ofNat 7; rfl
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case b7 =>
    refine seg_fixW b ?_
    knodeW StackTake.stUnl StackTake.stUnl_ok StackTake.bumpL 7 (hWb TK.b7)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stUnl_walk lab _ hJ ha
    exact .inl ⟨TK.unl, by rw [h1]; exact ofNat_add' _ 7 21, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case unl =>
    refine seg_fixW b ?_
    refine rtst_ndW (b := .rcx) (k := 0) (r := .rax) (z := 3)
      (code_field hp hend (by simp only [hin']) (l := StackTake.bumpL) (off := 28) rfl)
      (hWb TK.unl) fun m σ c _ hD hJ => ?_
    obtain ⟨rfl, hJ, hc, ha⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = lockA (_root_.Executable.labels exe).label := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hv : σ.regs.get64 .rax = 0#64 := by rw [← ha]; rfl
    rw [hb, hv]
    exact ⟨htk.lock0.rt, htk.lock0.mp, htk.lock0.G, htk.lock0.unmapped m (hFFb m hD),
      q.c0,
      .refl q.c0, .inl ⟨TK.b31, ofNat_add' _ 28 3, rfl, rfl, hJ⟩⟩
  case b31 =>
    refine seg_fixW b ?_
    lnodeW "scc_rt_stack_next" StackTake.bumpL 31 TK.b38 (hWb TK.b31)
    · exact ofNat_add' _ 31 7
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case b38 =>
    refine seg_fixW b ?_
    knodeW StackTake.stAdd StackTake.stAdd_ok StackTake.bumpL 38 (hWb TK.b38)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stAdd_walk lab _ hJ ha
    exact .inl ⟨TK.nxt, by rw [h1]; exact ofNat_add' _ 38 18, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case nxt =>
    refine seg_fixW b ?_
    refine ownXadd_ndW (b := .rcx) (k := 0) (r := .rax) (z := 5) (by decide) hFb
      (code_field hp hend (by simp only [hin']) (l := StackTake.bumpL) (off := 56) rfl) htk.ownNext
      (hWb TK.nxt) fun m σ c _ hD hJ => ?_
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, hc, ha⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = nextA (_root_.Executable.labels exe).label := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hv : σ.regs.get64 .rax = StackTake.size0 := by rw [← ha]; rfl
    rw [hb, hv]
    exact ⟨rfl, htk.next.rt, htk.next.mp, htk.next.G, htk.next.unmapped m (hFFb m hD),
      q.c0, .refl q.c0, fun fl =>
        .inl ⟨TK.b61, ofNat_add' _ 56 5, rfl, rfl, by simpa [ownStep, StackTake.Fr, Reg64s.set64] using hJ,
          by simp [ownStep, Reg64s.set64]⟩⟩
  case b61 =>
    refine seg_fixW b ?_
    knodeW StackTake.stBnd StackTake.stBnd_ok StackTake.bumpL 61 (hWb TK.b61)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stBnd_walk lab _ hJ ha hk
    exact .inl ⟨TK.b108, by rw [h1]; exact ofNat_add' _ 61 47, by rw [h2]; rfl, rfl, h3⟩
  case b108 =>
    refine seg_fixW b ?_
    knodeW StackTake.stJ2 StackTake.stJ2_ok StackTake.bumpL 108 (hWb TK.b108)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stJ2_walk lab _ hJ
    exact .inl ⟨TK.ok0, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case ok0 =>
    refine seg_fixW b ?_
    lnodeW "scc_rt_stacks" StackTake.okL 0 TK.ok7 (hWb TK.ok0)
    · show _ + Int64.ofNat 7 = _ + Int64.ofNat 7; rfl
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case ok7 =>
    refine seg_fixW b ?_
    knodeW StackTake.stOk StackTake.stOk_ok StackTake.okL 7 (hWb TK.ok7)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stOk_walk lab _ hJ ha
    exact .inl ⟨TK.tk, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case tk =>
    refine seg_fixW b ?_
    knodeW StackTake.stSite StackTake.stSite_ok StackTake.takenL 0 (hWb TK.tk)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stSite_walk lab _ hJ
    exact .inl ⟨TK.site, by rw [h1]; exact eSite, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case site =>
    refine seg_movedW (j := TK.ret) ((take_ndW (n' := takeNG lab q true TK.ret) rfl
      (code_field hp hend (by simp only [nopBlk, hin']) (l := StackTake.siteL) (off := 0) (ofNat_zero' _))
      (hWb TK.site) (fun m σ pm hA hD => ⟨hAbs hA, hFt m pm hD.1, fun _ => stackM_takeMem⟩)
      fun σ c hJ => ⟨rfl, c, .refl c, rfl, hJ.1, hJ.2.1⟩).mono_post fun _ _ h => ⟨true, h⟩)
  case ret =>
    cases b
    · exact seg_falseW.mono_pre fun _ _ ⟨_, _, _, _, _, _, _, h, _⟩ => Bool.false_ne_true h
    refine seg_fixW true ?_
    knodeW StackTake.stRet StackTake.stRet_ok StackTake.siteL 1 (blkW_mono (F := fun m => F m ∧ StackM rS m)
      (F' := takeF F rS true) (hW TK.ret) fun m h => ⟨h.1, h.2 rfl⟩)
    dsimp only [takeNG, takeXG] at hJ ⊢
    obtain ⟨-, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stRet_walk lab _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, rfl, h3⟩

end TakeProof

/-! ## `scc_rt_thread_init` -/

/-- **The ghosts of a call of `scc_rt_thread_init`**: `%rsp`, `%rbp` and the
return address at entry, the TCB's address, `scc_rt_stack_next`'s value
`k0` on entry, the source control. -/
structure TiG where
  g : AllocTcb.G
  tcb : BitVec 64
  k0 : BitVec 64
  c0 : Ctl

/-- `scc_rt_thread_init`'s internal nodes. -/
inductive TI where
  | e | entry | c7 | call | x7 | st0 | f1 | st1 | f2 | st2 | f3 | st3 | f4 | st4 | f5 | st5 | ret

/-- The call `call scc_rt_stack_take` (`ThreadInit.callBlk`). -/
def tiCall : List (Directive × Nat) := (parse("call scc_rt_stack_take")).zip [5]

block_spec tiCall (-48) 8 ThreadInit.oI tiCall

/-- The field stores are `stDir`. -/
theorem storeBlks_eq : ThreadInit.storeBlks = [[(stDir .rcx 0 .rax, 3)], [(stDir .rcx 8 .rax, 4)],
    [(stDir .rcx 16 .rax, 4)], [(stDir .rcx 24 .rax, 4)], [(stDir .rcx 32 .rax, 4)], [(stDir .rcx 40 .rax, 4)]] := by
  decide

section Ti

variable (lab : Label → Int64) (q : TiG)

/-- The stack's base `scc_rt_stacks + k0`. -/
abbrev tiBase : BitVec 64 := stacksA lab + q.k0

open ThreadInit in
/-- **The nodes.** Back from the take (`x7`) only `%rsp`'s offset is
known; the frame fixes `%rbp`'s. -/
def tiN : TI → ND
  | .e => ⟨lab fnL, oE, fun σ c => c = q.c0 ∧ Pre q.g q.tcb σ⟩
  | .entry => ⟨lab entryL, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g q.tcb) σ⟩
  | .c7 => ⟨lab entryL + Int64.ofNat 7, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g q.tcb) σ ∧
      σ.regs.rdi.toBitVec = StackTake.size0⟩
  | .call => ⟨lab StackTake.fnL, ⟨-48, []⟩, fun σ c => (c = q.c0 ∧ (∀ p ∈ s0 q.g q.tcb, σ.slot p.1 = p.2) ∧
      σ.regs.rsp.toBitVec = q.g.sp - 48#64 ∧ σ.regs.rbp.toBitVec = q.g.sp - 8#64 ∧
      σ.regs.rdi.toBitVec = StackTake.size0) ∧ σ.slot (-48) = (lab x7L).toBitVec⟩
  | .x7 => ⟨lab x7L, ⟨-40, []⟩, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g q.tcb) σ ∧
      σ.regs.rax.toBitVec = tiBase lab q⟩
  | .st0 => ⟨lab x7L + Int64.ofNat 48, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ ∧
      σ.regs.rax.toBitVec = q.tcb ∧ σ.regs.rcx.toBitVec = q.tcb⟩
  | .f1 => ⟨lab x7L + Int64.ofNat 51, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ⟩
  | .st1 => ⟨lab x7L + Int64.ofNat 59, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ ∧
      σ.regs.rax.toBitVec = tiBase lab q + 4096#64 ∧ σ.regs.rcx.toBitVec = q.tcb⟩
  | .f2 => ⟨lab x7L + Int64.ofNat 63, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ⟩
  | .st2 => ⟨lab x7L + Int64.ofNat 74, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ ∧
      σ.regs.rax.toBitVec = 0#64 ∧ σ.regs.rcx.toBitVec = q.tcb⟩
  | .f3 => ⟨lab x7L + Int64.ofNat 78, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ⟩
  | .st3 => ⟨lab x7L + Int64.ofNat 89, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ ∧
      σ.regs.rax.toBitVec = 0#64 ∧ σ.regs.rcx.toBitVec = q.tcb⟩
  | .f4 => ⟨lab x7L + Int64.ofNat 93, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ⟩
  | .st4 => ⟨lab x7L + Int64.ofNat 101, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ ∧
      σ.regs.rax.toBitVec = tiBase lab q ∧ σ.regs.rcx.toBitVec = q.tcb⟩
  | .f5 => ⟨lab x7L + Int64.ofNat 105, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ⟩
  | .st5 => ⟨lab x7L + Int64.ofNat 113, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ ∧
      σ.regs.rax.toBitVec = tiBase lab q + 16384#64 ∧ σ.regs.rcx.toBitVec = q.tcb⟩
  | .ret => ⟨lab x7L + Int64.ofNat 117, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ⟩

/-- **The exit**: at the return address, `Post`. -/
def tiX : Unit → ND
  | () => ⟨Int64.ofBitVec q.g.ra, ThreadInit.oR, fun σ c => c = q.c0 ∧ ThreadInit.Post q.g (tiBase lab q) σ⟩

/-- The take's ghosts at a call from `scc_rt_thread_init`. -/
abbrev tiTake (g : AllocTcb.G) : TakeG := ⟨g, q.k0, q.c0⟩

end Ti

/-- A store's address `k(%rcx)` with `%rcx = t`. -/
theorem bAddr_rcx {r : Reg64s} {t : BitVec 64} (h : r.rcx.toBitVec = t) (k : Int64) :
    bAddr r .rcx k = t + BitVec.ofInt 64 k.toInt := by
  rw [← h]; rfl

section TiProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F F0 : MachineData → Prop}

set_option hygiene false in
/-- A block node of `scc_rt_thread_init`. -/
local macro "inode " b:ident ok:ident l:term:max k:term:max : tactic =>
  `(tactic| refine seg_nd (by simp [$b:ident]) $ok hF hR (by omega) hhi
    (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) (by first | rfl | exact ofNat_zero' _))
      fun σ c hJ => ⟨c, .refl c, ?_⟩)

set_option hygiene false in
/-- A node at the store of field `i` (`8·i(%rcx)`, `z` bytes) at `.x7 + k`,
to node `j`. -/
local macro "snode " i:term:max d:term:max k:term:max z:term:max v:term:max j:term:max : tactic =>
  `(tactic| (
    refine rtst_nd (b := .rcx) (k := $d) (r := .rax) (z := $z)
      (code_field hp hend (by simp only [hin']) (l := ThreadInit.x7L) (off := $k) rfl) fun m σ c _ hD hJ => ?_
    dsimp only [tiN] at hJ
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    have hfi := hfld (8 * $i, $v) (by simp [ThreadInit.fields])
    rw [bAddr_rcx hc, show BitVec.ofInt 64 (Int64.toInt $d) = BitVec.ofNat 64 (8 * $i) by decide,
      show σ.regs.get64 .rax = σ.regs.rax.toBitVec from rfl, ha]
    exact ⟨hfi.rt, hfi.mp, hfi.G, hfi.unmapped m (hFF m hD), q.c0,
      .refl q.c0, .inl ⟨$j, ofNat_add' _ $k $z, rfl, rfl, hJ⟩⟩))

/-- **`scc_rt_thread_init` is one segment** in any valid layout of
`ret0Cells`, from its entry to its return, for any region holding its frame
of 32, the saved `%rbp`, the return address and `scc_rt_stack_take`'s frame
below, and any frame condition implying `F0`: the TCB's six fields' stores
(`hfld`, their `StOk`), the take's room (`hk`) and its own-word accesses
(`htk`). -/
theorem thread_init_seg (hp : Lays exe SccCode.ret0Cells) (hend : endPc = endOf exe SccCode.ret0Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TiG) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields q.tcb (tiBase (_root_.Executable.labels exe).label q),
      StOk ms F0 (q.tcb + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F0 exe endPc q.k0) :
    Seg p lbl ms (At exe endPc R F (tiN (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x, At exe endPc R F (tiX (_root_.Executable.labels exe).label q x) s c) := by
  have hin' := ThreadInit.ret0_threadInitIn
  simp only [ThreadInit.threadInitIn, ThreadInit.storeOff, storeBlks_eq, List.zip_cons_cons, List.zip_nil_left,
    List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hin'
  have eEntry := label_labelGapB (a := ThreadInit.fnL) (b := ThreadInit.entryL) (off := 12) hp (by simp only [hin'])
  have eX7 := label_labelGapB (a := ThreadInit.entryL) (b := ThreadInit.x7L) (off := 12) hp (by simp only [hin'])
  have hcall : blockAtB SccCode.ret0Cells ThreadInit.entryL 7 tiCall = true :=
    (by simp only [hin'] : blockAtB SccCode.ret0Cells ThreadInit.entryL 7 ThreadInit.callBlk = true)
  let lab := (_root_.Executable.labels exe).label
  refine fn_seg (N := tiN _ q) (E := tiX _ q) (fun i => ?_) TI.e
  cases i
  case e =>
    inode ThreadInit.tiPro ThreadInit.tiPro_ok ThreadInit.fnL 0
    dsimp only [tiN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := ThreadInit.tiPro_walk lab _ hJ
    exact .inl ⟨TI.entry, by rw [h1]; exact eEntry, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    inode ThreadInit.tiArg ThreadInit.tiArg_ok ThreadInit.entryL 0
    dsimp only [tiN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4⟩ := ThreadInit.tiArg_walk lab _ hJ
    exact .inl ⟨TI.c7, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3, h4⟩
  case c7 =>
    refine seg_nd (by simp [tiCall]) tiCall_ok hF hR (by omega) hhi
      (code_field hp hend hcall rfl) fun σ c hJ => ⟨c, .refl c, ?_⟩
    dsimp only [tiN] at hJ ⊢
    obtain ⟨rfl, ⟨hsp, hfp, hs⟩, hdi⟩ := hJ
    rw [tiCall_run]
    refine .inl ⟨TI.call, rfl, rfl, ⟨rfl, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro p hp'
      have hp48 : p.1 ≠ -48 := by
        simp only [ThreadInit.s0, List.mem_cons, List.mem_nil_iff, or_false] at hp'
        rcases hp' with rfl | rfl | rfl <;> simp
      simp only [upd_apply, hp48, ↓reduceIte]
      exact hs p hp'
    · simp [Reg64s.set64, hsp]; bv_omega
    · simp [Reg64s.set64, hfp]
    · simp [Reg64s.set64, hdi]
    · simp only [upd_apply, ↓reduceIte]
      rw [eX7, Int64.toBitVec_add, Int64.toBitVec_add, BitVec.add_assoc]; rfl
  case call =>
    refine call_nd_F (e0 := 0) (lo' := -200) (hi' := 8) (Ne := fun g => takeN lab (tiTake q g) .e)
      (Ex := fun g => takeX lab (tiTake q g))
      hR hF (by show R.lo ≤ -48 - 0 + -200; omega) (by decide) (by show (-48 : Int) - 0 < R.hi; omega)
      (by show (-48 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-48 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide)
      (fun R' F' hR' hlo' hhi' hF' hFF' g' =>
        stack_take_seg hp hend hF' hR' hlo' hhi' (fun m h => hFF m (hFF' m h)) (tiTake q g') hk
          htk)
      (fun _ => rfl) ?_ ?_
    · rintro σC c ⟨⟨rfl, -, -, -, h0⟩, -⟩
      exact ⟨⟨σC.regs.rsp.toBitVec, σC.regs.rbp.toBitVec, σC.slot (-48 - 0 + 0)⟩, rfl, rfl, rfl, rfl, rfl, h0⟩
    · rintro g x σC c σx c' σR ⟨⟨-, hs, hsp, hfp, -⟩, h48⟩ ⟨-, hsp', hfp', hra', -⟩ ⟨rfl, hPost⟩ hregs - - hslot
      have hk' : ∀ k : Int, k % 8 = 0 → R.lo ≤ k → k + 8 ≤ R.hi → -48 < k → σR.slot k = σC.slot k :=
        fun k h1 h2 h3 h4 => hslot k ⟨h1, h2, h3⟩ fun h => by
          simp only [Region.Off, Region.callee] at h; dsimp only [tiN] at h; omega
      refine .inl ⟨TI.x7, ?_, by show SO.le ⟨-40, []⟩ ⟨-48 - 0 + 8, []⟩ = true; decide, rfl, ⟨?_, ?_, ?_⟩, ?_⟩
      · show lab ThreadInit.x7L = Int64.ofBitVec g.ra
        rw [← hra']
        show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
        rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
      · show σR.regs.rsp.toBitVec = _
        rw [hregs, hPost.1, ← hsp']
        show σC.regs.rsp.toBitVec + 8#64 = _
        rw [hsp]; bv_omega
      · show σR.regs.rbp.toBitVec = _
        rw [hregs, hPost.2.1, ← hfp']
        exact hfp
      · intro p hp'
        simp only [ThreadInit.s0, List.mem_cons, List.mem_nil_iff, or_false] at hp'
        rcases hp' with rfl | rfl | rfl
        · rw [hk' 0 (by decide) (by omega) (by omega) (by decide)]; exact hs (0, q.g.ra) (by simp)
        · rw [hk' (-8) (by decide) (by omega) (by omega) (by decide)]; exact hs (-8, q.g.fp) (by simp)
        · rw [hk' (-16) (by decide) (by omega) (by omega) (by decide)]; exact hs (-16, q.tcb) (by simp)
      · show σR.regs.rax.toBitVec = _
        rw [hregs]; exact hPost.2.2
  case x7 =>
    refine Seg.mono_pre (P := At exe endPc R F ⟨lab ThreadInit.x7L, ThreadInit.oI, (tiN lab q .x7).J⟩) ?_
      fun _ _ h => At.rbp h fun σ c ⟨_, ⟨hsp, hfp, _⟩, _⟩ => by
        simp only [Reg64s.get64]; rw [hsp, hfp]; bv_omega
    refine seg_nd (by simp [ThreadInit.tiSp]) ThreadInit.tiSp_ok hF hR (by omega) hhi
      (code_field hp hend (by simp only [hin']) (l := ThreadInit.x7L) (off := 0) (ofNat_zero' _))
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    dsimp only [tiN] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiSp_walk lab _ hJ ha
    exact .inl ⟨TI.st0, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case st0 => snode 0 0 48 3 q.tcb TI.f1
  case f1 =>
    inode ThreadInit.tiF1 ThreadInit.tiF1_ok ThreadInit.x7L 51
    dsimp only [tiN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF1_walk lab _ hJ
    exact .inl ⟨TI.st1, by rw [h1]; exact ofNat_add' _ 51 8, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case st1 => snode 1 8 59 4 (tiBase (_root_.Executable.labels exe).label q + 4096#64) TI.f2
  case f2 =>
    inode ThreadInit.tiZ ThreadInit.tiZ_ok ThreadInit.x7L 63
    dsimp only [tiN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiZ_walk lab _ hJ
    exact .inl ⟨TI.st2, by rw [h1]; exact ofNat_add' _ 63 11, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case st2 => snode 2 16 74 4 (0#64) TI.f3
  case f3 =>
    inode ThreadInit.tiZ ThreadInit.tiZ_ok ThreadInit.x7L 78
    dsimp only [tiN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiZ_walk lab _ hJ
    exact .inl ⟨TI.st3, by rw [h1]; exact ofNat_add' _ 78 11, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case st3 => snode 3 24 89 4 (0#64) TI.f4
  case f4 =>
    inode ThreadInit.tiF4 ThreadInit.tiF4_ok ThreadInit.x7L 93
    dsimp only [tiN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF4_walk lab _ hJ
    exact .inl ⟨TI.st4, by rw [h1]; exact ofNat_add' _ 93 8, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case st4 => snode 4 32 101 4 (tiBase (_root_.Executable.labels exe).label q) TI.f5
  case f5 =>
    inode ThreadInit.tiF5 ThreadInit.tiF5_ok ThreadInit.x7L 105
    dsimp only [tiN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF5_walk lab _ hJ
    exact .inl ⟨TI.st5, by rw [h1]; exact ofNat_add' _ 105 8, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case st5 => snode 5 40 113 4 (tiBase (_root_.Executable.labels exe).label q + 16384#64) TI.ret
  case ret =>
    inode ThreadInit.tiRet ThreadInit.tiRet_ok ThreadInit.x7L 117
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
  | .c7 => tiN lab q .c7
  | .call => tiN lab q .call
  | .x7 => tiA b (tiN lab q .x7)
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

/-- `.x7` with the frame's `%rbp` offset fixed (`At.rbp`): the node whose
block `ThreadInit.tiSp` runs. -/
def tiX7 : ND := ⟨lab ThreadInit.x7L, ThreadInit.oI, (tiN lab q .x7).J⟩

end TiG

/-- **`scc_rt_thread_init`'s node obligations inside `W`**: the block
nodes' states (`BlkW`; at `.x7` of `tiX7`), the stores' (`NodeW`), and at
the call those of `scc_rt_stack_take` in the callee's region (`TakeW`, for
every ghost). The nodes after the call are after the take, their frame
condition also `M` (the stack range in private memory, `StackM`, at the
use). -/
def TiW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F M : MachineData → Prop) (q : TiG) : TI → Prop
  | .e => BlkW W K exe endPc R F (tiN (_root_.Executable.labels exe).label q .e) ThreadInit.tiPro
  | .entry => BlkW W K exe endPc R F (tiN (_root_.Executable.labels exe).label q .entry) ThreadInit.tiArg
  | .c7 => BlkW W K exe endPc R F (tiN (_root_.Executable.labels exe).label q .c7) tiCall
  | .call => ∀ g, g.ra = ((_root_.Executable.labels exe).label ThreadInit.x7L).toBitVec → ∀ i,
      TakeW W K exe endPc (R.callee (-48 - 0) (-200) 8) F M (tiTake q g) i
  | .x7 => BlkW W K exe endPc R (fun m => F m ∧ M m)
      (tiX7 (_root_.Executable.labels exe).label q) ThreadInit.tiSp
  | .st0 => NodeW W K exe endPc R (fun m => F m ∧ M m)
      (tiN (_root_.Executable.labels exe).label q .st0)
  | .f1 => BlkW W K exe endPc R (fun m => F m ∧ M m)
      (tiN (_root_.Executable.labels exe).label q .f1) ThreadInit.tiF1
  | .st1 => NodeW W K exe endPc R (fun m => F m ∧ M m)
      (tiN (_root_.Executable.labels exe).label q .st1)
  | .f2 => BlkW W K exe endPc R (fun m => F m ∧ M m)
      (tiN (_root_.Executable.labels exe).label q .f2) ThreadInit.tiZ
  | .st2 => NodeW W K exe endPc R (fun m => F m ∧ M m)
      (tiN (_root_.Executable.labels exe).label q .st2)
  | .f3 => BlkW W K exe endPc R (fun m => F m ∧ M m)
      (tiN (_root_.Executable.labels exe).label q .f3) ThreadInit.tiZ
  | .st3 => NodeW W K exe endPc R (fun m => F m ∧ M m)
      (tiN (_root_.Executable.labels exe).label q .st3)
  | .f4 => BlkW W K exe endPc R (fun m => F m ∧ M m)
      (tiN (_root_.Executable.labels exe).label q .f4) ThreadInit.tiF4
  | .st4 => NodeW W K exe endPc R (fun m => F m ∧ M m)
      (tiN (_root_.Executable.labels exe).label q .st4)
  | .f5 => BlkW W K exe endPc R (fun m => F m ∧ M m)
      (tiN (_root_.Executable.labels exe).label q .f5) ThreadInit.tiF5
  | .st5 => NodeW W K exe endPc R (fun m => F m ∧ M m)
      (tiN (_root_.Executable.labels exe).label q .st5)
  | .ret => BlkW W K exe endPc R (fun m => F m ∧ M m)
      (tiN (_root_.Executable.labels exe).label q .ret) ThreadInit.tiRet

section TiWProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F F0 : MachineData → Prop}

omit [Executable.ValidLayout exe] in
/-- A block obligation holds at the node with the take done, under a
stronger frame condition. -/
theorem blkW_tiA {W : Frag isa} {K : State → State → Prop} {F' : MachineData → Prop} {n : ND}
    {blk : List (Directive × Nat)} {b : Bool} (h : BlkW W K exe endPc R F n blk) (hFF : ∀ m, F' m → F m) :
    BlkW W K exe endPc R F' (tiA b n) blk :=
  fun s σ c he hn hdc hpc hA hD hJ => h s σ c he hn hdc hpc hA (hFF _ hD) hJ.2

omit [Executable.ValidLayout exe] in
/-- A node obligation holds at the node with the take done, under a
stronger frame condition. -/
theorem nodeW_tiA {W : Frag isa} {K : State → State → Prop} {F' : MachineData → Prop} {n : ND} {b : Bool}
    (h : NodeW W K exe endPc R F n) (hFF : ∀ m, F' m → F m) : NodeW W K exe endPc R F' (tiA b n) :=
  fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h s c ⟨he, hn, hdc, hpc, σ, hA, hFF _ hD, hJ.2⟩

omit [Executable.ValidLayout exe] in
/-- A block obligation after the take, with the stack range in private
memory, holds at the node with the take done (`b`, so `takeF` gives the
range). -/
theorem blkW_tiS {W : Frag isa} {K : State → State → Prop} {rS : Scc.Sem.Range} {n : ND}
    {blk : List (Directive × Nat)} {b : Bool} (h : BlkW W K exe endPc R (fun m => F m ∧ StackM rS m) n blk) :
    BlkW W K exe endPc R (takeF F rS b) (tiA b n) blk :=
  fun s σ c he hn hdc hpc hA hD hJ => h s σ c he hn hdc hpc hA ⟨hD.1, hD.2 hJ.1⟩ hJ.2

omit [Executable.ValidLayout exe] in
/-- A node obligation after the take, with the stack range in private
memory, holds at the node with the take done. -/
theorem nodeW_tiS {W : Frag isa} {K : State → State → Prop} {rS : Scc.Sem.Range} {n : ND} {b : Bool}
    (h : NodeW W K exe endPc R (fun m => F m ∧ StackM rS m) n) : NodeW W K exe endPc R (takeF F rS b) (tiA b n) :=
  fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h s c ⟨he, hn, hdc, hpc, σ, hA, ⟨hD.1, hD.2 hJ.1⟩, hJ.2⟩

set_option hygiene false in
/-- A block node of `scc_rt_thread_init` inside `W`. -/
local macro "inodeW " b:ident ok:ident l:term:max k:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hFb hR (by omega) hhi
    (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) (by first | rfl | exact ofNat_zero' _))
      $w fun σ c hJ => ⟨c, .refl c, ?_⟩)

set_option hygiene false in
/-- A node at the store of field `i` (`8·i(%rcx)`, `z` bytes) at `.x7 + k`,
to node `j`, inside `W`, after the take. -/
local macro "snodeW " i:term:max d:term:max k:term:max z:term:max v:term:max j:term:max w:term:max : tactic =>
  `(tactic| (
    refine rtst_ndW (b := .rcx) (k := $d) (r := .rax) (z := $z)
      (code_field hp hend (by simp only [hin']) (l := ThreadInit.x7L) (off := $k) rfl) $w
      fun m σ c _ hD hJ => ?_
    dsimp only [tiNG, tiA, tiN] at hJ
    obtain ⟨rfl, rfl, hJ, ha, hc⟩ := hJ
    have hfi := hfld (8 * $i, $v) (by simp [ThreadInit.fields])
    rw [bAddr_rcx hc, show BitVec.ofInt 64 (Int64.toInt $d) = BitVec.ofNat 64 (8 * $i) by decide,
      show σ.regs.get64 .rax = σ.regs.rax.toBitVec from rfl, ha]
    exact ⟨hfi.rt, hfi.mp, hfi.G, hfi.unmapped m (hFFb m hD), q.c0,
      .refl q.c0, .inl ⟨$j, ofNat_add' _ $k $z, rfl, rfl, rfl, hJ⟩⟩))

/-- **`scc_rt_thread_init` is one segment inside `W`, the take its outside
move**: `thread_init_seg` with `stack_take_segW` at the call, so at the
return the stack range `rS` is in private memory (`StackM`). Given the node
obligations (`hW`), the region's cells off `rS` (`hRS`), every aligned word
of `rS` off the region (`hout`), and the frame condition kept by the take
(`hFt`). -/
theorem thread_init_segW {W : Frag isa} {rS : Scc.Sem.Range} (hp : Lays exe SccCode.ret0Cells)
    (hend : endPc = endOf exe SccCode.ret0Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TiG) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields q.tcb (tiBase (_root_.Executable.labels exe).label q),
      StOk ms F0 (q.tcb + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F0 exe endPc q.k0)
    (hW : ∀ i, TiW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F (StackM rS) q
      i)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (tiN (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x,
        At exe endPc R (fun m => F m ∧ StackM rS m) (tiX (_root_.Executable.labels exe).label q x) s c) := by
  have hin' := ThreadInit.ret0_threadInitIn
  simp only [ThreadInit.threadInitIn, ThreadInit.storeOff, storeBlks_eq, List.zip_cons_cons, List.zip_nil_left,
    List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hin'
  have eEntry := label_labelGapB (a := ThreadInit.fnL) (b := ThreadInit.entryL) (off := 12) hp (by simp only [hin'])
  have eX7 := label_labelGapB (a := ThreadInit.entryL) (b := ThreadInit.x7L) (off := 12) hp (by simp only [hin'])
  have hcall : blockAtB SccCode.ret0Cells ThreadInit.entryL 7 tiCall = true :=
    (by simp only [hin'] : blockAtB SccCode.ret0Cells ThreadInit.entryL 7 ThreadInit.callBlk = true)
  let lab := (_root_.Executable.labels exe).label
  have hSM := stackM_stable hfit hout
  -- the take's callee region, and `rS` off it
  have hb' := Region.callee_base (hi' := 8) hR (show R.lo ≤ (-48 - 0) + -200 by omega) (by decide)
    (show (-48 - 0 : Int) < R.hi by omega)
  have hRS' : ∀ k, (R.callee (-48 - 0) (-200) 8).Off k → ∀ i < 8,
      (R.callee (-48 - 0) (-200) 8).addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS := fun k hk i hi => by
    rw [Region.callee_addr]
    exact hRS _ (Region.callee_off (show R.lo ≤ (-48 - 0) + -200 by omega) (show (-48 - 0 : Int) + 8 ≤ R.hi by omega)
      (by decide) hk) i hi
  have hout' : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ (R.callee (-48 - 0) (-200) 8).base.toNat + (R.callee (-48 - 0) (-200) 8).lo ∨
        ((R.callee (-48 - 0) (-200) 8).base.toNat : Int) + (R.callee (-48 - 0) (-200) 8).hi ≤ a :=
    fun a h8 ha ha7 => by
      show (a : Int) + 8 ≤ ((R.callee (-48 - 0) (-200) 8).base.toNat : Int) + -200 ∨
        ((R.callee (-48 - 0) (-200) 8).base.toNat : Int) + 8 ≤ a
      rcases hout a h8 ha ha7 with h | h
      · exact .inl (by omega)
      · exact .inr (by omega)
  refine ((fn_seg_gW (exe := exe) (endPc := endPc) (Rg := fun _ => R) (Fg := takeF F rS)
      (N := tiNG (_root_.Executable.labels exe).label q) (E := tiXG (_root_.Executable.labels exe).label q)
      (fun b i => ?_) false TI.e).mono_pre fun s c h => ?_).mono_post
    fun s c h => ?_
  rotate_left
  · obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
    exact ⟨he, hn, hdc, hpc, σ, hA, ⟨hD, nofun⟩, hJ⟩
  · obtain ⟨g, x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM⟩, hb, hJ⟩ := h
    subst hb
    exact ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM rfl⟩, hJ⟩
  have hFb : FStable R (takeF F rS b) := fun m m' ⟨hD, hM⟩ hd => ⟨hF m m' hD hd, fun hb => hSM m m' (hM hb) hd⟩
  have hFFb : ∀ m, takeF F rS b m → F0 m := fun m h => hFF m h.1
  cases i
  case e =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiPro ThreadInit.tiPro_ok ThreadInit.fnL 0 (blkW_mono (hW TI.e) fun m h => h.1)
    dsimp only [tiNG, tiN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := ThreadInit.tiPro_walk lab _ hJ
    exact .inl ⟨TI.entry, by rw [h1]; exact eEntry, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiArg ThreadInit.tiArg_ok ThreadInit.entryL 0 (blkW_mono (hW TI.entry) fun m h => h.1)
    dsimp only [tiNG, tiN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4⟩ := ThreadInit.tiArg_walk lab _ hJ
    exact .inl ⟨TI.c7, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3, h4⟩
  case c7 =>
    refine seg_fixW b ?_
    refine seg_ndW (by simp [tiCall]) tiCall_ok hFb hR (by omega) hhi
      (code_field hp hend hcall rfl) (blkW_mono (hW TI.c7) fun m h => h.1) fun σ c hJ => ⟨c, .refl c, ?_⟩
    dsimp only [tiNG, tiN] at hJ ⊢
    obtain ⟨rfl, ⟨hsp, hfp, hs⟩, hdi⟩ := hJ
    rw [tiCall_run]
    refine .inl ⟨TI.call, rfl, rfl, ⟨rfl, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro p hp'
      have hp48 : p.1 ≠ -48 := by
        simp only [ThreadInit.s0, List.mem_cons, List.mem_nil_iff, or_false] at hp'
        rcases hp' with rfl | rfl | rfl <;> simp
      simp only [upd_apply, hp48, ↓reduceIte]
      exact hs p hp'
    · simp [Reg64s.set64, hsp]; bv_omega
    · simp [Reg64s.set64, hfp]
    · simp [Reg64s.set64, hdi]
    · simp only [upd_apply, ↓reduceIte]
      rw [eX7, Int64.toBitVec_add, Int64.toBitVec_add, BitVec.add_assoc]; rfl
  case call =>
    refine seg_fixW true ?_
    refine call_nd_FW (e0 := 0) (lo' := -200) (hi' := 8) (M := StackM rS)
      (Ne := fun g => takeNG lab (tiTake q g) false .e) (Ex := fun g => takeXG lab (tiTake q g) true)
      hR hFb (by show R.lo ≤ -48 - 0 + -200; omega) (by decide) (by show (-48 : Int) - 0 < R.hi; omega)
      (by show (-48 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-48 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide)
      (TakeK.kstable fun m pm ⟨hD, _⟩ => ⟨hFt m pm hD, fun _ => stackM_takeMem⟩)
      (fun s s' hk _ k hk' _ => by obtain ⟨pm, he⟩ := hk.mem; rw [he]; exact loadInt_takeMem (hRS k hk'))
      (fun m h hM => ⟨h.1, fun _ => hM⟩)
      (fun R' F' hR' hlo' hhi' hF' hK' hFF' hR'e _ g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, h48⟩, ⟨-, -, -, hra, -⟩⟩ := hg'
        have hr : g'.ra = (lab ThreadInit.x7L).toBitVec := by
          have e : lab ThreadInit.x7L = Int64.ofBitVec g'.ra := by
            rw [← hra]
            show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
            rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
          rw [e]; rfl
        exact (stack_take_segW hp hend hF' hR' hlo' hhi' (fun m h => hFF m (hFF' m h).1) (tiTake q g') hk htk
          (fun i => (hW TI.call g' hr i).mono fun m h => (hFF' m h).1) hRS' hfit hout'
          (takeMem_of_kstable hK' exe endPc)).mono_post
          fun s c ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM⟩, hJ⟩ => ⟨x, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hM⟩)
      (fun _ => rfl) ?_ ?_
    · rintro σC c ⟨⟨rfl, -, -, -, h0⟩, -⟩
      exact ⟨⟨σC.regs.rsp.toBitVec, σC.regs.rbp.toBitVec, σC.slot (-48 - 0 + 0)⟩, rfl, rfl, rfl, rfl, rfl, h0⟩
    · rintro g x σC c σx c' σR ⟨⟨-, hs, hsp, hfp, -⟩, h48⟩ ⟨-, hsp', hfp', hra', -⟩ ⟨-, rfl, hPost⟩ hregs - - hslot
      have hk' : ∀ k : Int, k % 8 = 0 → R.lo ≤ k → k + 8 ≤ R.hi → -48 < k → σR.slot k = σC.slot k :=
        fun k h1 h2 h3 h4 => hslot k ⟨h1, h2, h3⟩ fun h => by
          simp only [Region.Off, Region.callee] at h; dsimp only [tiNG, tiN] at h; omega
      refine .inl ⟨TI.x7, ?_, by show SO.le ⟨-40, []⟩ ⟨-48 - 0 + 8, []⟩ = true; decide, rfl, rfl, ⟨?_, ?_, ?_⟩,
        ?_⟩
      · show lab ThreadInit.x7L = Int64.ofBitVec g.ra
        rw [← hra']
        show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
        rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
      · show σR.regs.rsp.toBitVec = _
        rw [hregs, hPost.1, ← hsp']
        show σC.regs.rsp.toBitVec + 8#64 = _
        rw [hsp]; bv_omega
      · show σR.regs.rbp.toBitVec = _
        rw [hregs, hPost.2.1, ← hfp']
        exact hfp
      · intro p hp'
        simp only [ThreadInit.s0, List.mem_cons, List.mem_nil_iff, or_false] at hp'
        rcases hp' with rfl | rfl | rfl
        · rw [hk' 0 (by decide) (by omega) (by omega) (by decide)]; exact hs (0, q.g.ra) (by simp)
        · rw [hk' (-8) (by decide) (by omega) (by omega) (by decide)]; exact hs (-8, q.g.fp) (by simp)
        · rw [hk' (-16) (by decide) (by omega) (by omega) (by decide)]; exact hs (-16, q.tcb) (by simp)
      · show σR.regs.rax.toBitVec = _
        rw [hregs]; exact hPost.2.2
  case x7 =>
    refine seg_fixW b ?_
    refine SegW.mono_pre (P := At exe endPc R (takeF F rS b) (tiA b (tiX7 lab q))) ?_
      fun _ _ h => At.rbp h fun σ c ⟨_, _, ⟨hsp, hfp, _⟩, _⟩ => by
        simp only [Reg64s.get64]; rw [hsp, hfp]; bv_omega
    refine seg_ndW (by simp [ThreadInit.tiSp]) ThreadInit.tiSp_ok hFb hR (by omega) hhi
      (code_field hp hend (by simp only [hin']) (l := ThreadInit.x7L) (off := 0) (ofNat_zero' _))
      (blkW_tiS (hW TI.x7)) fun σ c hJ => ⟨c, .refl c, ?_⟩
    dsimp only [tiNG, tiA, tiX7, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiSp_walk lab _ hJ ha
    exact .inl ⟨TI.st0, by rw [h1]; rfl, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st0 =>
    refine seg_fixW b ?_
    snodeW 0 0 48 3 q.tcb TI.f1 (nodeW_tiS (hW TI.st0))
  case f1 =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiF1 ThreadInit.tiF1_ok ThreadInit.x7L 51 (blkW_tiS (hW TI.f1))
    dsimp only [tiNG, tiA, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF1_walk lab _ hJ
    exact .inl ⟨TI.st1, by rw [h1]; exact ofNat_add' _ 51 8, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st1 =>
    refine seg_fixW b ?_
    snodeW 1 8 59 4 (tiBase (_root_.Executable.labels exe).label q + 4096#64) TI.f2
      (nodeW_tiS (hW TI.st1))
  case f2 =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiZ ThreadInit.tiZ_ok ThreadInit.x7L 63 (blkW_tiS (hW TI.f2))
    dsimp only [tiNG, tiA, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiZ_walk lab _ hJ
    exact .inl ⟨TI.st2, by rw [h1]; exact ofNat_add' _ 63 11, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st2 =>
    refine seg_fixW b ?_
    snodeW 2 16 74 4 (0#64) TI.f3 (nodeW_tiS (hW TI.st2))
  case f3 =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiZ ThreadInit.tiZ_ok ThreadInit.x7L 78 (blkW_tiS (hW TI.f3))
    dsimp only [tiNG, tiA, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiZ_walk lab _ hJ
    exact .inl ⟨TI.st3, by rw [h1]; exact ofNat_add' _ 78 11, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st3 =>
    refine seg_fixW b ?_
    snodeW 3 24 89 4 (0#64) TI.f4 (nodeW_tiS (hW TI.st3))
  case f4 =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiF4 ThreadInit.tiF4_ok ThreadInit.x7L 93 (blkW_tiS (hW TI.f4))
    dsimp only [tiNG, tiA, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF4_walk lab _ hJ
    exact .inl ⟨TI.st4, by rw [h1]; exact ofNat_add' _ 93 8, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st4 =>
    refine seg_fixW b ?_
    snodeW 4 32 101 4 (tiBase (_root_.Executable.labels exe).label q) TI.f5
      (nodeW_tiS (hW TI.st4))
  case f5 =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiF5 ThreadInit.tiF5_ok ThreadInit.x7L 105 (blkW_tiS (hW TI.f5))
    dsimp only [tiNG, tiA, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF5_walk lab _ hJ
    exact .inl ⟨TI.st5, by rw [h1]; exact ofNat_add' _ 105 8, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st5 =>
    refine seg_fixW b ?_
    snodeW 5 40 113 4 (tiBase (_root_.Executable.labels exe).label q + 16384#64) TI.ret
      (nodeW_tiS (hW TI.st5))
  case ret =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiRet ThreadInit.tiRet_ok ThreadInit.x7L 117 (blkW_tiS (hW TI.ret))
    dsimp only [tiNG, tiA, tiN, tiXG, tiX] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := ThreadInit.tiRet_walk lab _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, rfl, h3⟩

end TiWProof

/-! ## `scc_rt_start` from `.x0` to `.x1`: `scc_rt_thread_init` -/

/-- `scc_rt_start`'s call of `scc_rt_thread_init` with the TCB. -/
def startCall2 : List (Directive × Nat) := (parse("movq %rax, -24(%rbp)
movq -24(%rbp), %rdi
call scc_rt_thread_init")).zip [4, 4, 5]

block_spec startCall2 (-48) 0 oS startCall2

/-- `.Lscc_rt_start.x1`, the return address of the call. -/
abbrev x1L : Label := ".Lscc_rt_start.x1"

/-- **The call's code in `cells`**: the block at `.x0`, `.x1` right after it. -/
def startCall2In (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells x0L 0 startCall2 && labelGapB cells x0L x1L 13

theorem ret0_startCall2In : startCall2In SccCode.ret0Cells = true := by decide +kernel

section Start2

variable (lab : Label → Int64)

/-- **The call node**: at `scc_rt_thread_init`'s label, the TCB in `%rdi`
and at `-24(%rbp)`, the return address `.x1` pushed, `%rbp` 40 bytes above
`%rsp`. -/
def startNC2 (tcb : BitVec 64) (c0 : Ctl) : ND := ⟨lab ThreadInit.fnL, ⟨-48, []⟩, fun σ c =>
  (c = c0 ∧ σ.regs.rdi.toBitVec = tcb ∧ σ.slot (-32) = tcb) ∧ σ.slot (-48) = (lab x1L).toBitVec ∧
    σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (-8 - -48)⟩

/-- **Back at `.x1`**: `%rax` the new stack's top `scc_rt_stacks + k0 +
16384`, the TCB `scc_rt_pinned + n0 + 8` at `-24(%rbp)`; `%rbp` at the
saved `%rbp`. -/
def startN3 (n0 k0 : BitVec 64) (c0 : Ctl) : ND := ⟨lab x1L, oS, fun σ c =>
  (c = c0 ∧ σ.regs.rax.toBitVec = stacksA lab + k0 + 16384#64 ∧ σ.slot (-32) = pinA lab + n0 + 8#64) ∧
    σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (-8 - -40)⟩

end Start2

section Start2Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_start` from `.x0` to `.x1`** in any valid layout of
`ret0Cells`: the call's block and `scc_rt_thread_init` through `call_nd_F`,
with `scc_rt_stack_next` holding `k0` (room below `2^29`, `hk`), the TCB's
fields' facts (`hfld`) and the take's own-word accesses (`htk`). -/
theorem start_x0_x1_seg (hp : Lays exe SccCode.ret0Cells) (hend : endPc = endOf exe SccCode.ret0Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi)
    (n0 k0 : BitVec 64) (c0 : Ctl) (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0) :
    Seg p lbl ms (At exe endPc R F (startN2 (_root_.Executable.labels exe).label n0 c0))
      (At exe endPc R F (startN3 (_root_.Executable.labels exe).label n0 k0 c0)) := by
  let lab := (_root_.Executable.labels exe).label
  let tcb := pinA lab + n0 + 8#64
  have hin := ret0_startCall2In
  simp only [startCall2In, Bool.and_eq_true] at hin
  have ex1 := label_labelGapB hp hin.2
  refine Seg.seq (Q := At exe endPc R F (startNC2 lab tcb c0)) ?_
    ((seg_one (n := ⟨lab x1L, ⟨-40, []⟩, (startN3 lab n0 k0 c0).J⟩) ?_).mono_post
      fun _ _ h => At.rbp h fun _ _ h => h.2)
  · -- the call's block
    refine (seg_one (seg_nd (by simp [startCall2]) startCall2_ok hF hR (by omega) (by omega)
      (code_field hp hend hin.1 (ofNat_zero' _)) fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)).mono_pre
      fun _ _ h => At.rbp_get rfl h
    · dsimp only [startN2, startNC2]; rw [startCall2_run]
    · dsimp only [startN2, startNC2]; rw [startCall2_run]; rfl
    · dsimp only [startN2, startNC2] at hJ ⊢; rw [startCall2_run]
      obtain ⟨⟨⟨rfl, hax⟩, -⟩, hb⟩ := hJ
      refine ⟨⟨rfl, ?_, ?_⟩, ?_, ?_⟩
      · simp [Reg64s.set64, Reg64s.get64, upd_apply, hax]; rfl
      · simp [Reg64s.set64, Reg64s.get64, upd_apply, hax]; rfl
      · simp only [upd_apply, ↓reduceIte]
        rw [show lab x1L = _ from ex1, Int64.toBitVec_add]; rfl
      · simp only [Reg64s.get64, Reg64s.set64] at hb ⊢; rw [hb]; bv_omega
  · -- `scc_rt_thread_init`
    refine call_nd_F (e0 := 0) (lo' := -248) (hi' := 8) (Ne := fun g => tiN lab ⟨g, tcb, k0, c0⟩ .e)
      (Ex := fun g => tiX lab ⟨g, tcb, k0, c0⟩)
      hR hF (by show R.lo ≤ -48 - 0 + -248; omega) (by decide) (by show (-48 : Int) - 0 < R.hi; omega)
      (by show (-48 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-48 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide)
      (fun R' F' hR' hlo' hhi' hF' hFF g' =>
        thread_init_seg hp hend hF' hR' hlo' hhi' hFF ⟨g', tcb, k0, c0⟩ hk hfld htk)
      (fun _ => rfl) ?_ ?_
    · rintro σC c ⟨⟨rfl, h0, -⟩, -, -⟩
      exact ⟨⟨σC.regs.rsp.toBitVec, σC.regs.rbp.toBitVec, σC.slot (-48 - 0 + 0)⟩, rfl, rfl, rfl, rfl, rfl, h0⟩
    · rintro g x σC c σx c' σR ⟨⟨-, -, h32⟩, h48, hb⟩ ⟨-, hsp, hfp, hra, -⟩ ⟨rfl, hsp', hb', hrax⟩ hregs - - hslot
      refine .inl ⟨(), ?_, by show SO.le ⟨-40, []⟩ ⟨-48 - 0 + 8, []⟩ = true; decide, ⟨rfl, ?_, ?_⟩, ?_⟩
      · show lab x1L = Int64.ofBitVec g.ra
        rw [← hra]
        show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
        rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
      · rw [hregs]; exact hrax
      · rw [hslot (-32) ⟨by decide, by omega, by omega⟩ fun h => by
          simp only [Region.Off, Region.callee] at h; dsimp only [startNC2] at h; omega]
        exact h32
      · show σR.regs.get64 .rbp = σR.regs.get64 .rsp + BitVec.ofInt 64 (-8 - -40)
        rw [hregs]
        simp only [Reg64s.get64] at hb ⊢
        rw [hb', hsp', ← hfp, ← hsp]
        show σC.regs.rbp.toBitVec = σC.regs.rsp.toBitVec + 8#64 + BitVec.ofInt 64 (-8 - -40)
        rw [hb]; bv_omega

/-- **`scc_rt_start` from its entry to `.x1`**: `start_x0_seg` then
`start_x0_x1_seg`, the TCB at `scc_rt_pinned + n0 + 8`. -/
theorem start_x1_seg (hp : Lays exe SccCode.ret0Cells) (hend : endPc = endOf exe SccCode.ret0Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi) (n0 k0 : BitVec 64) (c0 : Ctl) (hn : n0.toNat + 80 ≤ 131072)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hhdr : StOk ms F (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F exe endPc n0)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0) :
    Seg p lbl ms (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0))
      (At exe endPc R F (startN3 (_root_.Executable.labels exe).label n0 k0 c0)) :=
  (start_x0_seg hp hend hK hF hR (by omega) (by omega) n0 c0 hn hhdr htcb).seq
    (start_x0_x1_seg hp hend hF hR hlo hhi n0 k0 c0 hk hfld htk)

end Start2Proof

/-! ## `scc_rt_start` from `.x1` on: `arch_prctl`, the stack switch, `scc_rt_main` -/

/-- `.x1`'s block: the top saved at `-32(%rbp)`, `arch_prctl(ARCH_SET_FS,
tcb)`'s arguments. -/
def startFs : List (Directive × Nat) := (parse("movq %rax, -32(%rbp)
movq -24(%rbp), %rsi
movl $4098, %edi
movl $158, %eax")).zip [4, 4, 5, 5]

/-- After `arch_prctl`: `%rax` the top, `%rdi` the TCB. -/
def startSw : List (Directive × Nat) := (parse("movq -32(%rbp), %rax
movq -24(%rbp), %rdi")).zip [4, 4]

/-- After the switch and `xorl %ebp, %ebp`: the call of `scc_rt_main`. -/
def startMain : List (Directive × Nat) := (parse("call scc_rt_main")).zip [5]

block_spec startFs (-48) 0 oS startFs
block_spec startSw (-48) 0 oS startSw
block_spec startMain (-80) 0 SO.entry startMain

/-- **`scc_rt_start`'s tail in `cells`**: `.x1`'s block, the system call,
the block after it, the switch `movq %rax, %rsp` and the call of
`scc_rt_main` after `xorl %ebp, %ebp`. -/
def startTailIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells x1L 0 startFs && blockAtB cells x1L 18 [(op64 .syscall, 2)] && blockAtB cells x1L 20 startSw &&
  blockAtB cells x1L 28 [(swDir .rax, 3)] && blockAtB cells x1L 31 [(FI.toDir (.xor_rr32_self .rbp), 2)] &&
  blockAtB cells x1L 33 startMain

theorem ret0_startTailIn : startTailIn SccCode.ret0Cells = true := by decide +kernel

/-- **The switch's step**: `%rsp` takes `%rax`; the thread pointer is kept. -/
theorem swStep (o : SO) (fall : Int64) (σ : AS) :
    (AI.step o fall (.reg .W64 (.mov (.reg (.low .rsp .W64)) (.regOrMem (.reg (.low .rax .W64))))) σ).regs.rsp =
      σ.regs.rax ∧
    (AI.step o fall (.reg .W64 (.mov (.reg (.low .rsp .W64)) (.regOrMem (.reg (.low .rax .W64))))) σ).regs.fsBase =
      σ.regs.fsBase := by
  constructor <;> simp [AI.step, regRes, Operation.interp, Operand.interp, RegOrMem.interp, MachineData.set,
    MachineData.setReg, Reg64s.set, Reg64s.set64, Reg64s.get_low64]

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

/-- The thread pointer `arch_prctl` sets: the TCB. -/
abbrev tpOf (tcb : BitVec 64) : UInt64 := UInt64.ofNat tcb.toNat

section Tail

variable (lab : Label → Int64)

/-- **At `arch_prctl`**: its arguments, the top at `-32(%rbp)`, the TCB at
`-24(%rbp)`. -/
def startN4 (tcb top : BitVec 64) (c0 : Ctl) : ND := ⟨lab x1L + Int64.ofNat 18, oS, fun σ c =>
  c = c0 ∧ σ.regs.rax.toNat = 158 ∧ σ.regs.rdi.toNat = 4098 ∧ σ.regs.rsi.toBitVec = tcb ∧
    σ.slot (-40) = top ∧ σ.slot (-32) = tcb⟩

/-- **After `arch_prctl`**: the thread pointer the TCB. -/
def startN5 (tcb top : BitVec 64) (c0 : Ctl) : ND := ⟨lab x1L + Int64.ofNat 20, oS, fun σ c =>
  c = c0 ∧ σ.regs.fsBase = tpOf tcb ∧ σ.slot (-40) = top ∧ σ.slot (-32) = tcb⟩

/-- **At the switch** `movq %rax, %rsp`: `%rax` the top. -/
def startN6 (tcb top : BitVec 64) (c0 : Ctl) : ND := ⟨lab x1L + Int64.ofNat 28, oS, fun σ c =>
  c = c0 ∧ σ.regs.rax.toBitVec = top ∧ σ.regs.fsBase = tpOf tcb⟩

/-- **After the switch**: `%rsp` the new stack's top, at offset 0 of the new region. -/
def startN7 (tcb top : BitVec 64) (c0 : Ctl) : ND := ⟨lab x1L + Int64.ofNat 31, SO.entry, fun σ c =>
  c = c0 ∧ σ.regs.rsp.toBitVec = top ∧ σ.regs.fsBase = tpOf tcb⟩

/-- **At the call of `scc_rt_main`**, after `xorl %ebp, %ebp`. -/
def startN8 (tcb top : BitVec 64) (c0 : Ctl) : ND := ⟨lab x1L + Int64.ofNat 33, SO.entry, fun σ c =>
  c = c0 ∧ σ.regs.rsp.toBitVec = top ∧ σ.regs.fsBase = tpOf tcb⟩

/-- **The call node of `scc_rt_main`**: the return address pushed below the top. -/
def startNM (tcb top : BitVec 64) (c0 : Ctl) : ND := ⟨lab "scc_rt_main", ⟨-8, []⟩, fun σ c =>
  c = c0 ∧ σ.regs.rsp.toBitVec = top - 8#64 ∧ σ.regs.fsBase = tpOf tcb⟩

end Tail

section TailProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **From the switch on**: `movq %rax, %rsp` moves to the region based at
the new stack's top `top`, `xorl %ebp, %ebp; call scc_rt_main`, then
`main_seg` through `call_nd_F` (the call never returns). A segment to any
fragment, given: the region of 80 bytes below `top` not wrapping (`hok`),
the new stack's cells holding a slot file in the memory at the switch
(`hmap`: the stack is the thread's private memory by then), the limit word
`%fs:8` outside the new region (`hfit`, `hout`) and its facts for both
frames of `scc_rt_main` (`hlimM`, `hlimW`), and that the final
`exit_group(42)` off an abort site is `main`'s exit (`hexit`). -/
theorem start_switch_seg (hp : Lays exe SccCode.ret0Cells) (hend : endPc = endOf exe SccCode.ret0Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (tcb top : BitVec 64) (c0 : Ctl)
    (hok : (swR top (-80) 0).OK)
    (hmap : ∀ m, F m → ∃ sl : Int → BitVec 64, ∀ k, (swR top (-80) 0).Off k →
      ∃ j, Mem.loadInt m.dmem ((swR top (-80) 0).addr k) 8 = some j ∧ BitVec.ofInt 64 j = sl k)
    (hfit : (limA (tpOf tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf tcb)).toNat : Int) + 8 ≤ top.toNat + -80 ∨ (top.toNat : Int) + 0 ≤ (limA (tpOf tcb)).toNat)
    (hlimM : LimOk ms F (limA (tpOf tcb)) (top - 8#64 - 8#64 - (32 : Int64).toBitVec))
    (hlimW : LimOk ms F (limA (tpOf tcb))
      (top - 8#64 - 8#64 - (32 : Int64).toBitVec - 8#64 - 8#64 - (16 : Int64).toBitVec))
    (hexit : ∀ R' F' s, At exe endPc R' F' (mainNX (_root_.Executable.labels exe).label) s c0 → ¬ ms.abortAt s →
      MainExit p ms s c0 42)
    {Q : Frag isa} :
    Seg p lbl ms (At exe endPc R F (startN6 (_root_.Executable.labels exe).label tcb top c0)) Q := by
  let lab := (_root_.Executable.labels exe).label
  have hin := ret0_startTailIn
  simp only [startTailIn, Bool.and_eq_true] at hin
  let a := limA (tpOf tcb)
  refine sw_seq (lo := -80) (hi := 0) (F' := swF top a) (n' := startN7 lab tcb top c0)
    (sw_nd rfl (code_field hp hend hin.1.1.2 rfl) (ofNat_add' _ 28 3) rfl fun m σ c _ hD hJ => ?_) fun v hv => ?_
  · obtain ⟨rfl, hax, htp⟩ := hJ
    obtain ⟨hsp, htp'⟩ := swStep (startN6 lab tcb top c).o ((startN6 lab tcb top c).pc + Int64.ofNat 3) σ
    have hsp2 : (AI.step (startN6 lab tcb top c).o ((startN6 lab tcb top c).pc + Int64.ofNat 3)
        (.reg .W64 (.mov (.reg (.low .rsp .W64)) (.regOrMem (.reg (.low .rax .W64))))) σ).regs.get64 .rsp = top := by
      show (UInt64.toBitVec _) = _; rw [hsp]; exact hax
    rw [hsp2]
    obtain ⟨sl, hsl⟩ := hmap m hD
    exact ⟨hok, ⟨rfl, hlimM.unmapped m hD⟩, sl, hsl, c, .refl c, rfl, by rw [hsp]; exact hax, htp'.trans htp⟩
  · have hF2 : FStable (swR v (-80) 0) (swF top a v) := swF_stable hfit hout
    refine (Seg.seq (Q := At exe endPc (swR v (-80) 0) (swF top a v) (startN8 lab tcb top c0))
      (seg_one (flag_nd (n := startN7 lab tcb top c0) (fi := .xor_rr32_self .rbp) rfl hF2
        (code_field hp hend hin.1.2 rfl)
        fun σ c hJ fl => ⟨c, .refl c, .inl ⟨(),
          show lab x1L + Int64.ofNat 33 = lab x1L + Int64.ofNat 31 + Int64.ofNat 2 from ofNat_add' _ 31 2,
          by show SO.le SO.entry ((FI.xor_rr32_self .rbp).so SO.entry) = true; decide, ?_⟩⟩))
      (Seg.seq (Q := At exe endPc (swR v (-80) 0) (swF top a v) (startNM lab tcb top c0))
      (seg_one (seg_nd (by simp [startMain]) startMain_ok hF2 hv (Int.le_refl _) (Int.le_refl _)
        (code_field hp hend hin.2 rfl) fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩))
      (call_nd_F (N := fun e : Empty => e.elim) (E := fun e : Empty => e.elim) (e0 := 0) (lo' := -72) (hi' := 8)
        (Ne := fun _ : Unit => mainN0 lab ⟨top - 8#64, tpOf tcb, c0⟩) (Ex := fun _ (e : Empty) => e.elim)
        hv hF2 (by show (-80 : Int) ≤ -8 - 0 + -72; decide) (by decide) (by show (-8 : Int) - 0 < 0; decide)
        (by show (-8 : Int) - 0 + 8 ≤ 0; decide) (by show ((-8 : Int) - 0) % 8 = 0; decide) (by decide) (by decide)
        (fun R' F' hR' hlo' hhi' hF' hFF _ => main_seg hp hend hK hF' hR' hlo' (by omega)
          ⟨top - 8#64, tpOf tcb, c0⟩
          ⟨hlimM.rt, hlimM.mp, fun _ h => (hFF _ h).2, hlimM.room⟩
          ⟨hlimW.rt, hlimW.mp, fun _ h => (hFF _ h).2, hlimW.room⟩ fun s hAt => hexit _ _ s hAt)
        (fun _ => rfl) (fun σC c hJ => ⟨(), rfl, hJ⟩) fun _ x => x.elim))).mono_post
      fun _ _ h => h.elim (fun ⟨e, _⟩ => e.elim) fun ⟨e, _⟩ => e.elim
    · dsimp only [startN7, startN8] at hJ ⊢
      obtain ⟨rfl, hsp, htp⟩ := hJ
      exact ⟨rfl, hsp, htp⟩
    · dsimp only [startN8, startNM]; rw [startMain_run]
    · dsimp only [startN8, startNM]; rw [startMain_run]; rfl
    · dsimp only [startN8, startNM] at hJ ⊢; rw [startMain_run]
      obtain ⟨rfl, hsp, htp⟩ := hJ
      refine ⟨rfl, ?_, ?_⟩
      · simp [Reg64s.set64, Reg64s.get64, hsp]
      · simp [Reg64s.set64, htp]

/-- **`scc_rt_start` from `.x1` to the switch**: `.x1`'s block,
`arch_prctl(ARCH_SET_FS, tcb)` (`archSetFs_nd`) and the block after it. -/
theorem start_x1_sw_seg (hp : Lays exe SccCode.ret0Cells) (hend : endPc = endOf exe SccCode.ret0Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (n0 k0 : BitVec 64) (c0 : Ctl) :
    Seg p lbl ms (At exe endPc R F (startN3 (_root_.Executable.labels exe).label n0 k0 c0))
      (At exe endPc R F (startN6 (_root_.Executable.labels exe).label
        (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0)) := by
  let lab := (_root_.Executable.labels exe).label
  let tcb := pinA lab + n0 + 8#64
  let top := stacksA lab + k0 + 16384#64
  have hin := ret0_startTailIn
  simp only [startTailIn, Bool.and_eq_true] at hin
  refine Seg.seq (Q := At exe endPc R F (startN4 lab tcb top c0)) ?_
    (Seg.seq (Q := At exe endPc R F (startN5 lab tcb top c0)) ?_ ?_)
  · -- `.x1`'s block
    refine seg_one (seg_nd (by simp [startFs]) startFs_ok hF hR hlo hhi
      (code_field hp hend hin.1.1.1.1.1 (ofNat_zero' _)) fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
    · dsimp only [startN3, startN4]; rw [startFs_run]; rfl
    · dsimp only [startN3, startN4]; rw [startFs_run]; rfl
    · dsimp only [startN3, startN4] at hJ ⊢; rw [startFs_run]
      obtain ⟨⟨rfl, hax, h32⟩, -⟩ := hJ
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first
        | (simp [Reg64s.set64, Reg64s.get64, upd_apply, hax, h32]; done)
        | (simp [Reg64s.set64, Reg64s.get64, upd_apply, hax, h32]; rfl)
  · -- `arch_prctl(ARCH_SET_FS, tcb)`
    refine seg_one (archSetFs_nd hK hF (code_field hp hend hin.1.1.1.1.2 rfl) fun σ c hJ => ?_)
    obtain ⟨rfl, hax, hdi, hsi, h40, h32⟩ := hJ
    refine ⟨_, syscallCall_archSetFs hax hdi, c, .refl c, .inl ⟨(), ofNat_add' _ 18 2,
      by show SO.le oS (syscallSO oS) = true; decide, rfl, ?_, h40, h32⟩⟩
    show UInt64.ofNat σ.regs.rsi.toNat = _
    rw [← hsi]; rfl
  · -- the block after it
    refine seg_one (seg_nd (by simp [startSw]) startSw_ok hF hR hlo hhi
      (code_field hp hend hin.1.1.1.2 rfl) fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
    · dsimp only [startN5, startN6]; rw [startSw_run]; exact ofNat_add' _ 20 8
    · dsimp only [startN5, startN6]; rw [startSw_run]; rfl
    · dsimp only [startN5, startN6] at hJ ⊢; rw [startSw_run]
      obtain ⟨rfl, htp, h40, h32⟩ := hJ
      refine ⟨rfl, ?_, ?_⟩
      · simp [Reg64s.set64, Reg64s.get64, upd_apply, h40]; rfl
      · simp only [Reg64s.set64]; exact htp

/-- **`scc_rt_start` never returns**: in any valid layout of `ret0Cells`,
from its entry, a segment to any fragment. The chain is S1, the call of
`scc_rt_alloc_tcb`, the call of `scc_rt_thread_init` (with
`scc_rt_stack_take` nested), `arch_prctl(ARCH_SET_FS, tcb)`, the switch to
the new stack and `scc_rt_main`. The own words on entry are
`scc_rt_pinned_next = n0` and `scc_rt_stack_next = k0`. The premises are
those of the parts: the memory-side facts (`hhdr`, `hfld`, `hmap`,
`hlimM`, `hlimW`), `main`'s exit (`hexit`), the arithmetic ones (`hn`,
`hk`, `hok`, `hfit`, `hout`) and the own-word accesses (`htcb`, `htk`,
whose `OwnAt` values are named until `ms.own` is wired). -/
theorem start_seg (hp : Lays exe SccCode.ret0Cells) (hend : endPc = endOf exe SccCode.ret0Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi) (n0 k0 : BitVec 64) (c0 : Ctl) (hn : n0.toNat + 80 ≤ 131072)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hhdr : StOk ms F (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F exe endPc n0)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0)
    (hok : (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).OK)
    (hmap : ∀ m, F m → ∃ sl : Int → BitVec 64,
      ∀ k, (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).Off k →
        ∃ j, Mem.loadInt m.dmem ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).addr k)
          8 = some j ∧ BitVec.ofInt 64 j = sl k)
    (hfit : (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat + -80 ∨
      ((stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat : Int) + 0 ≤
        (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat)
    (hlimM : LimOk ms F (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - (32 : Int64).toBitVec))
    (hlimW : LimOk ms F (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - (32 : Int64).toBitVec -
        8#64 - 8#64 - (16 : Int64).toBitVec))
    (hexit : ∀ R' F' s, At exe endPc R' F' (mainNX (_root_.Executable.labels exe).label) s c0 → ¬ ms.abortAt s →
      MainExit p ms s c0 42)
    {Q : Frag isa} :
    Seg p lbl ms (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0)) Q :=
  (start_x1_seg hp hend hK hF hR hlo hhi n0 k0 c0 hn hk hhdr htcb hfld htk).seq
    ((start_x1_sw_seg hp hend hK hF hR (by omega) (by omega) n0 k0 c0).seq
      (start_switch_seg hp hend hK _ _ c0 hok hmap hfit hout hlimM hlimW hexit))

end TailProof

/-! ## `wc_main` and `scc_rt_main` inside `W` -/

/-- `wc_main`'s entry registers: `wcN0` without the limit word's facts. -/
def wcJ0 (g : WcG) (σ : AS) (c : Ctl) : Prop :=
  c = g.c0 ∧ σ.regs.rbp.toBitVec = g.fp ∧ σ.slot 0 = g.ra ∧ σ.regs.rsp.toBitVec = g.sp ∧ σ.regs.fsBase = g.tp

/-- **`wc_main`'s states inside `W`**, none moved by `K`: its prologue's and
its body's. -/
structure WcW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isa) (g : WcG) : Prop where
  pro : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "wc_main") 16 8 ".Lwc_main.stk"
    5 9 3 2 4 [] (wcJ0 g)
  body : WcBodyW W K exe endPc R F (wcN1 (_root_.Executable.labels exe).label g).J

/-- The caller's cells outside a callee's region (at `kc`, from `lo'` to
`hi'`) hold values. -/
def CallerCells (R : Region) (kc lo' hi' : Int) (m : MachineData) : Prop :=
  ∀ k, R.Off k → ¬ (R.callee kc lo' hi').Off (k - kc) → (Mem.loadInt m.dmem (R.addr k) 8).isSome

/-- `scc_rt_main`'s body entry with `%rbp` claimed from its offset
(`At.rbp_get`): the node the call block runs from. -/
def mainN1R (lab : Label → Int64) (g : MainG) : ND := ⟨lab ".Lscc_rt_main.entry", oM, fun σ c =>
  (mainN1 lab g).J σ c ∧ σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (-8 - oM.sp)⟩

/-- Back from `wc_main` with `%rbp`'s offset fixed (`At.rbp`): the node the
`exit_group` tail runs from. -/
def mainNRR (lab : Label → Int64) (g : MainG) : ND :=
  ⟨lab ".Lscc_rt_main.x2", ⟨-40, [(.rbp, -8)]⟩, (mainNR lab g).J⟩

/-- **`scc_rt_main`'s states inside `W`**, none moved by `K`: its prologue's,
the call block's, `wc_main`'s in the callee's region (for every ghost with
the caller's source control and thread pointer, the caller's cells outside
it holding values) and the `exit_group` tail's. -/
structure MainW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isa) (g : MainG) : Prop where
  pro : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_main") 32 8 ".Lscc_rt_main.stk"
    5 9 3 2 4 [(.rdi, -8, 4)] (mainN0 (_root_.Executable.labels exe).label g).J
  call : BlkW W K exe endPc R F (mainN1R (_root_.Executable.labels exe).label g) mainCall
  wc : ∀ g', g'.ra = ((_root_.Executable.labels exe).label ".Lscc_rt_main.x2").toBitVec →
    g'.c0 = g.c0 → g'.tp = g.tp →
      WcW W K exe endPc (R.callee (-48 - 0) (-24) 8) (fun m => F m ∧ CallerCells R (-48 - 0) (-24) 8 m) ms g'
  exit : XExitW W K exe endPc R F (mainNRR (_root_.Executable.labels exe).label g) (-40) (-8) (-16) 4 4 5

section MainWProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F F0 : MachineData → Prop}

omit [Executable.ValidLayout exe] in
/-- A prologue's obligations under a weaker frame condition hold under a stronger one. -/
theorem proW_mono {W : Frag isa} {K : State → State → Prop} {F' : MachineData → Prop} {ms' : MemSide isa}
    {pc0 Z lim : Int64} {L : String} {zl zf z1 z2 zs : Nat} {ps : List (Reg64 × Int64 × Nat)}
    {J : AS → Ctl → Prop} (h : XProW W K exe endPc R F ms' pc0 Z lim L zl zf z1 z2 zs ps J)
    (hFF : ∀ m, F' m → F m) : XProW W K exe endPc R F' ms' pc0 Z lim L zl zf z1 z2 zs ps J :=
  ⟨blkW_mono h.w0 hFF, blkW_mono h.w1 hFF, nodeW_mono h.w2 hFF, blkW_mono h.w3 hFF, blkW_mono h.w4 hFF⟩

omit [Executable.ValidLayout exe] in
/-- `wc_main`'s obligations under a weaker frame condition hold under a stronger one. -/
theorem WcW.mono {W : Frag isa} {K : State → State → Prop} {F' : MachineData → Prop} {g : WcG}
    (h : WcW W K exe endPc R F ms g) (hFF : ∀ m, F' m → F m) : WcW W K exe endPc R F' ms g :=
  ⟨proW_mono h.pro hFF, ⟨blkW_mono h.body.w0 hFF, blkW_mono h.body.w1 hFF⟩⟩

/-- **`wc_main` is one segment inside `W`** (`wc_seg`, its states'
obligations `hW`). -/
theorem wc_segW {W : Frag isa} {K : State → State → Prop} (hp : Lays exe SccCode.ret0Cells)
    (hend : endPc = endOf exe SccCode.ret0Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (g : WcG) (hW : WcW W K exe endPc R F ms g) :
    SegW W K p lbl ms (At exe endPc R F (wcN0 ms F0 (_root_.Executable.labels exe).label g))
      (At exe endPc R F (wcNx g)) := by
  let lab := (_root_.Executable.labels exe).label
  refine SegW.of_imp (P := At exe endPc R F ⟨lab "wc_main", ⟨0, []⟩, wcJ0 g⟩)
      (L := LimOk ms F0 (limA g.tp) (g.sp - 8#64 - (16 : Int64).toBitVec)) (fun hlim0 => ?_) |>.mono_pre ?_
  · have hlim := hlim0.mono hFF
    refine SegW.seq (ret0_wc_prologue_segW hp hend (nb := wcN1 lab g) hF hR hlo (by omega) rfl wcBody_le
        hW.pro ?_)
      (ret0_wc_body_segW hp hend hF hR hlo hhi (by show SO.le ⟨8, []⟩ ⟨8, []⟩ = true; decide) hW.body ?_ ?_)
    · rintro σ c ⟨rfl, hfp, hra, hsp, htp⟩
      have ha : σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec = limA g.tp := by rw [limA, htp]
      rw [ha]
      refine ⟨hlim.rt, hlim.mp, hlim.unmapped, fun v hv => ⟨?_, fun σ' hr hs => ⟨rfl, ?_, ?_, ?_⟩⟩⟩
      · rw [hsp]; exact hlim.room v hv
      · rw [hs]; simp [xStSlots, xS1, upd_apply, hfp]
      · rw [hs]; simp [xStSlots, xS1, upd_apply, hra]
      · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, hsp]
    · rintro σ c ⟨-, -, h0, -⟩
      simp [wcNx, h0]
    · rintro σ c ⟨rfl, h8, -, hb⟩ σ' - h42 hb' hsp'
      refine ⟨rfl, h42, hb'.trans h8, ?_⟩
      rw [hsp', hb]; bv_omega
  · rintro s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ, hL⟩
    exact ⟨⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hL⟩

/-- **`scc_rt_main` does not return, inside `W`** (`main_seg`, its states'
obligations `hW`). The call of `wc_main` asks no closure under `K` of it
(`call_nd_FWK` with `KC := False`): no outside move is in it. -/
theorem main_segW {W : Frag isa} {K : State → State → Prop} (hp : Lays exe SccCode.ret0Cells)
    (hend : endPc = endOf exe SccCode.ret0Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -72) (hhi : 0 ≤ R.hi) (g : MainG)
    (hlimM : LimOk ms F (limA g.tp) (g.sp0 - 8#64 - (32 : Int64).toBitVec))
    (hlimW : LimOk ms F (limA g.tp) (g.sp0 - 8#64 - (32 : Int64).toBitVec - 8#64 - 8#64 - (16 : Int64).toBitVec))
    (hexit : ∀ s, At exe endPc R F (mainNX (_root_.Executable.labels exe).label) s g.c0 → ¬ ms.abortAt s →
      MainExit p ms s g.c0 42)
    (hW : MainW W K exe endPc R F ms g)
    {Q : Frag isa} :
    SegW W K p lbl ms (At exe endPc R F (mainN0 (_root_.Executable.labels exe).label g)) Q := by
  let lab := (_root_.Executable.labels exe).label
  have hin := ret0_mainIn
  simp only [mainIn, Bool.and_eq_true] at hin
  have ex2 := label_labelGapB hp hin.2
  have hlo40 : R.lo ≤ -40 := by omega
  refine SegW.seq (ret0_main_prologue_segW hp hend (nb := mainN1 lab g) hF hR hlo40 hhi rfl
    (by show SO.le oM (oF 32) = true; decide) hW.pro ?_)
    (SegW.seq (Q := At exe endPc R F (mainNC lab g)) ?_
      (SegW.seq (Q := At exe endPc R F (mainNR lab g)) ?_
        ((ret0_main_exit_segW hp hend (n := mainNRR lab g)
            rfl rfl hK hF hR hlo40 hhi hW.exit fun s c σ0 hJ0 hs => ?_).mono_pre
          fun _ _ h => At.rbp h fun _ _ h => h.2.1)))
  · -- the prologue
    rintro σ c ⟨rfl, hsp, htp⟩
    have ha : σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec = limA g.tp := by rw [limA, htp]
    rw [ha]
    refine ⟨hlimM.rt, hlimM.mp, hlimM.unmapped, fun v hv => ⟨?_, fun σ' hr _ => ⟨rfl, ?_, ?_⟩⟩⟩
    · rw [hsp]; exact hlimM.room v hv
    · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, hsp]
    · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, htp]
  · -- `call wc_main`
    refine (seg_oneW (seg_ndW (n := mainN1R lab g) (by simp [mainCall]) mainCall_ok hF hR (by omega) hhi
      (code_field hp hend hin.1 (ofNat_zero' _)) hW.call
        fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)).mono_pre
      fun _ _ h => At.rbp_get rfl h
    · dsimp only [mainN1R, mainNC]; rw [mainCall_run]
    · dsimp only [mainN1R, mainNC]; rw [mainCall_run]; rfl
    · dsimp only [mainN1R, mainN1, mainNC] at hJ ⊢; rw [mainCall_run]
      obtain ⟨⟨rfl, hsp, htp⟩, hb⟩ := hJ
      refine ⟨⟨rfl, ?_, ?_⟩, ?_, ?_⟩
      · simp [Reg64s.set64, hsp]
      · simp [Reg64s.set64, htp]
      · simp only [upd_apply, ↓reduceIte]
        rw [show lab ".Lscc_rt_main.x2" = _ from ex2]; rfl
      · simp only [Reg64s.get64, Reg64s.set64] at hb ⊢; rw [hb]; bv_omega
  · -- the call
    refine seg_oneW (call_nd_FWK (KC := False) (e0 := 0) (lo' := -24) (hi' := 8) (M := fun _ => True)
      (Ne := wcN0 ms F lab) (Ex := fun g _ => wcNx g)
      hR hF (by show R.lo ≤ -48 - 0 + -24; omega) (by decide) (by show (-48 : Int) - 0 < R.hi; omega)
      (by show (-48 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-48 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide) (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' hlo' hhi' hF' _ hFF hR'e hcc g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨⟨hc, -, htp⟩, h48, -⟩, ⟨⟨hc', -, hra, -, htp'⟩, -⟩⟩ := hg'
        have hr : g'.ra = (lab ".Lscc_rt_main.x2").toBitVec := by
          have e : lab ".Lscc_rt_main.x2" = Int64.ofBitVec g'.ra := by
            rw [← hra]
            show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
            rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
          rw [e]; rfl
        exact (wc_segW hp hend hF' hR' hlo' hhi' hFF g'
          ((hW.wc g' hr (hc'.symm.trans hc) (htp'.symm.trans htp)).mono fun m h => ⟨hFF m h, hcc m h⟩)).mono_post
            fun _ _ h => ⟨(), h, trivial⟩)
      (fun _ => rfl) ?_ ?_)
    · rintro σC c ⟨⟨rfl, hsp, htp⟩, -, -⟩
      refine ⟨⟨σC.regs.rbp.toBitVec, σC.slot (-48 - 0 + 0), σC.regs.rsp.toBitVec, g.tp, g.c0⟩, rfl,
        ⟨rfl, rfl, rfl, rfl, htp⟩, ?_⟩
      show LimOk ms F (limA g.tp) (σC.regs.rsp.toBitVec - 8#64 - (16 : Int64).toBitVec)
      rw [hsp]; exact hlimW
    · rintro g' x σC c σx c' σR ⟨⟨rfl, -, -⟩, h48, hb⟩ ⟨⟨hc, hfp, hra, hsp, -⟩, -⟩ ⟨hc', h42, hb', hsp'⟩ hregs
        - - -
      refine .inl ⟨(), ?_, by show SO.le ⟨-40, []⟩ ⟨-48 - 0 + 8, []⟩ = true; decide, hc'.trans hc.symm, ?_,
        by rw [hregs]; exact h42⟩
      · show lab ".Lscc_rt_main.x2" = Int64.ofBitVec g'.ra
        rw [← hra]
        show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
        rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
      · show σR.regs.get64 .rbp = σR.regs.get64 .rsp + BitVec.ofInt 64 (-8 - -40)
        rw [hregs]
        simp only [Reg64s.get64] at hb ⊢
        rw [hb', hsp', ← hfp, ← hsp]
        show σC.regs.rbp.toBitVec = σC.regs.rsp.toBitVec + 8#64 + BitVec.ofInt 64 (-8 - -40)
        rw [hb]; bv_omega
  · -- the `exit_group(42)`
    obtain ⟨rfl, -, h42⟩ := hJ0
    have e : σ0.regs.rax.toNat = 42 := by
      show σ0.regs.rax.toBitVec.toNat = 42; rw [h42]; rfl
    rw [e]
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩ := hs
    exact SysOk.exitGroup_main
      (hexit s ⟨he, hn, hdc, hpc, σ, hA, hD, by show σ.regs.rdi.toBitVec = _; rw [hx]; exact h42⟩)

end MainWProof

/-! ## `scc_rt_start` inside `W`, the take its outside move -/

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

/-- After S1, at the call's block, with `%rbp` claimed from its offset
(`At.rbp_get`): the node the block runs from. -/
def startN1R (lab : Label → Int64) (c0 : Ctl) : ND := ⟨lab startE + Int64.ofNat 43, oS, fun σ c =>
  (startN1 lab c0).J σ c ∧ σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (-8 - oS.sp)⟩

/-- Back at `.x0` with `%rbp` claimed from its offset (`At.rbp_get`): the
node the call block of `scc_rt_thread_init` runs from. -/
def startN2R (lab : Label → Int64) (n0 : BitVec 64) (c0 : Ctl) : ND := ⟨lab x0L, oS, fun σ c =>
  (startN2 lab n0 c0).J σ c ∧ σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (-8 - oS.sp)⟩

/-- **The switch's and `scc_rt_main`'s states inside `W`**, none moved by
`K`: the switch; `xorl %ebp, %ebp`, the call block and `scc_rt_main`'s
(in the callee's region, the caller's cells outside it holding values), in
the new region (for every value of the new `%rsp`). -/
structure SwW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isa) (rS : Scc.Sem.Range) (tcb top : BitVec 64)
    (c0 : Ctl) : Prop where
  sw : NodeW W K exe endPc R F (startN6 (_root_.Executable.labels exe).label tcb top c0)
  xor : ∀ v, NodeW W K exe endPc (swR v (-80) 0) (swFS rS top (limA (tpOf tcb)) v)
    (startN7 (_root_.Executable.labels exe).label tcb top c0)
  blk : ∀ v, BlkW W K exe endPc (swR v (-80) 0) (swFS rS top (limA (tpOf tcb)) v)
    (startN8 (_root_.Executable.labels exe).label tcb top c0) startMain
  main : ∀ v, MainW W K exe endPc ((swR v (-80) 0).callee (-8 - 0) (-72) 8)
    (fun m => swFS rS top (limA (tpOf tcb)) v m ∧ CallerCells (swR v (-80) 0) (-8 - 0) (-72) 8 m) ms
    ⟨top - 8#64, tpOf tcb, c0⟩

/-- **`scc_rt_start` from `.x0` to the switch: its states inside `W`**,
none moved by `K`: `.x0`'s block, `scc_rt_thread_init`'s in the callee's
region (for every ghost), then `.x1`'s block, `arch_prctl` and the block
after it, the last three with the stack range in private memory. -/
structure X0W (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (rS : Scc.Sem.Range) (n0 k0 : BitVec 64) (c0 : Ctl) : Prop where
  b0 : BlkW W K exe endPc R F (startN2R (_root_.Executable.labels exe).label n0 c0) startCall2
  ti : ∀ g, g.ra = ((_root_.Executable.labels exe).label x1L).toBitVec → ∀ i,
    TiW W K exe endPc (R.callee (-48 - 0) (-248) 8) F (StackM rS)
    ⟨g, pinA (_root_.Executable.labels exe).label + n0 + 8#64, k0, c0⟩ i
  fs : BlkW W K exe endPc R (fun m => F m ∧ StackM rS m) (startN3 (_root_.Executable.labels exe).label n0 k0 c0)
    startFs
  sys : NodeW W K exe endPc R (fun m => F m ∧ StackM rS m)
    (startN4 (_root_.Executable.labels exe).label (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0)
  sw : BlkW W K exe endPc R (fun m => F m ∧ StackM rS m)
    (startN5 (_root_.Executable.labels exe).label (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0) startSw

/-- **`scc_rt_start` up to `.x0`: its states inside `W`**, none moved by
`K`: S1's, the call block's and `scc_rt_alloc_tcb`'s in the callee's region
(for every ghost). -/
structure St0W (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (n0 : BitVec 64) (c0 : Ctl) : Prop where
  start : XStartW W K exe endPc R F (startN0 (_root_.Executable.labels exe).label c0).J
  blk : BlkW W K exe endPc R F (startN1R (_root_.Executable.labels exe).label c0) startCall
  tcb : ∀ g, g.ra = ((_root_.Executable.labels exe).label x0L).toBitVec → ∀ i,
    TcbW W K exe endPc (R.callee (-48 - 0) (-184) 8) F ⟨g, n0, c0⟩ i

/-- **`scc_rt_start`'s states inside `W`**, none moved by `K`: up to `.x0`,
from `.x0` to the switch, and from the switch on (with the stack range in
private memory). -/
structure StartAllW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isa) (rS : Scc.Sem.Range) (n0 k0 : BitVec 64)
    (c0 : Ctl) : Prop where
  s1 : St0W W K exe endPc R F n0 c0
  s2 : X0W W K exe endPc R F rS n0 k0 c0
  s3 : SwW W K exe endPc R (fun m => F m ∧ StackM rS m) ms rS
    (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
    (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0

section StartWProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

omit [Executable.ValidLayout exe] in
theorem TiW.mono {W : Frag isa} {K : State → State → Prop} {F' M : MachineData → Prop} {q : TiG} {i : TI}
    (h : TiW W K exe endPc R F M q i) (hFF : ∀ m, F' m → F m) : TiW W K exe endPc R F' M q i := by
  cases i <;> dsimp only [TiW] at h ⊢
  all_goals first
    | exact blkW_mono h hFF
    | exact nodeW_mono h hFF
    | exact blkW_mono h fun m h => ⟨hFF m h.1, h.2⟩
    | exact nodeW_mono h fun m h => ⟨hFF m h.1, h.2⟩
    | exact fun g hg i => (h g hg i).mono hFF

omit [Executable.ValidLayout exe] in
theorem TcbW.mono {W : Frag isa} {K : State → State → Prop} {F' : MachineData → Prop} {q : TcbG} {i : TN}
    (h : TcbW W K exe endPc R F q i) (hFF : ∀ m, F' m → F m) : TcbW W K exe endPc R F' q i := by
  cases i <;> dsimp only [TcbW] at h ⊢
  all_goals first
    | exact blkW_mono h hFF
    | exact nodeW_mono h hFF

omit [Executable.ValidLayout exe] in
/-- `scc_rt_main`'s obligations under a weaker frame condition hold under a stronger one. -/
theorem MainW.mono {W : Frag isa} {K : State → State → Prop} {F' : MachineData → Prop} {g : MainG}
    (h : MainW W K exe endPc R F ms g) (hFF : ∀ m, F' m → F m) : MainW W K exe endPc R F' ms g :=
  ⟨proW_mono h.pro hFF, blkW_mono h.call hFF, fun g' hg hc ht => (h.wc g' hg hc ht).mono fun m h => ⟨hFF m h.1, h.2⟩,
    ⟨blkW_mono h.exit.w0 hFF, nodeW_mono h.exit.w1 hFF⟩⟩

/-- **From the switch on, inside `W`** (`start_switch_seg`, its states'
obligations `hW`). The new stack's cells hold values at the switch since
the stack range is in private memory then (`hFS`) and the new region lies
in it (`hsub`), so `hmap` is not asked; after the switch the frame keeps the
range off the new region (`swFS`). The call of `scc_rt_main` asks no
closure under `K` of it (`call_nd_FWK` with `KC := False`). -/
theorem start_switch_segW {W : Frag isa} {K : State → State → Prop} {rS : Scc.Sem.Range}
    (hp : Lays exe SccCode.ret0Cells) (hend : endPc = endOf exe SccCode.ret0Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (tcb top : BitVec 64) (c0 : Ctl)
    (hok : (swR top (-80) 0).OK)
    (hFS : ∀ m, F m → StackM rS m) (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (hsub : ∀ k, (swR top (-80) 0).Off k → ((swR top (-80) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR top (-80) 0).addr k).toNat ∧ rS.contains (((swR top (-80) 0).addr k).toNat + 7))
    (hfit : (limA (tpOf tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf tcb)).toNat : Int) + 8 ≤ top.toNat + -80 ∨ (top.toNat : Int) + 0 ≤ (limA (tpOf tcb)).toNat)
    (hlimM : LimOk ms F (limA (tpOf tcb)) (top - 8#64 - 8#64 - (32 : Int64).toBitVec))
    (hlimW : LimOk ms F (limA (tpOf tcb))
      (top - 8#64 - 8#64 - (32 : Int64).toBitVec - 8#64 - 8#64 - (16 : Int64).toBitVec))
    (hexit : ∀ R' F' s, At exe endPc R' F' (mainNX (_root_.Executable.labels exe).label) s c0 → ¬ ms.abortAt s →
      MainExit p ms s c0 42)
    (hW : SwW W K exe endPc R F ms rS tcb top c0)
    {Q : Frag isa} :
    SegW W K p lbl ms (At exe endPc R F (startN6 (_root_.Executable.labels exe).label tcb top c0)) Q := by
  let lab := (_root_.Executable.labels exe).label
  have hin := ret0_startTailIn
  simp only [startTailIn, Bool.and_eq_true] at hin
  let a := limA (tpOf tcb)
  have hmap : ∀ m, F m → ∃ sl : Int → BitVec 64, ∀ k, (swR top (-80) 0).Off k →
      ∃ j, Mem.loadInt m.dmem ((swR top (-80) 0).addr k) 8 = some j ∧ BitVec.ofInt 64 j = sl k := by
    intro m hD
    refine ⟨fun k => BitVec.ofInt 64 ((Mem.loadInt m.dmem ((swR top (-80) 0).addr k) 8).getD 0), fun k hk => ?_⟩
    obtain ⟨h8, ha, ha7⟩ := hsub k hk
    have h := hFS m hD _ h8 ha ha7
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp h
    exact ⟨j, hj, by simp only [hj, Option.getD_some]⟩
  refine sw_seqW (lo := -80) (hi := 0) (F' := swFS rS top a) (n' := startN7 lab tcb top c0)
    (sw_ndW rfl (code_field hp hend hin.1.1.2 rfl) (ofNat_add' _ 28 3) rfl hW.sw fun m σ c _ hD hJ => ?_)
    fun v hv => ?_
  · obtain ⟨rfl, hax, htp⟩ := hJ
    obtain ⟨hsp, htp'⟩ := swStep (startN6 lab tcb top c).o ((startN6 lab tcb top c).pc + Int64.ofNat 3) σ
    have hsp2 : (AI.step (startN6 lab tcb top c).o ((startN6 lab tcb top c).pc + Int64.ofNat 3)
        (.reg .W64 (.mov (.reg (.low .rsp .W64)) (.regOrMem (.reg (.low .rax .W64))))) σ).regs.get64 .rsp = top := by
      show (UInt64.toBitVec _) = _; rw [hsp]; exact hax
    rw [hsp2]
    obtain ⟨sl, hsl⟩ := hmap m hD
    exact ⟨hok, ⟨⟨rfl, hlimM.unmapped m hD⟩, (hFS m hD).off⟩, sl, hsl, c, .refl c, rfl, by rw [hsp]; exact hax,
      htp'.trans htp⟩
  · have hF2 : FStable (swR v (-80) 0) (swFS rS top a v) := fun m m' h hd =>
      ⟨swF_stable hfit hout m m' h.1 hd, stackOff_stable hfitS m m' h.2 hd⟩
    refine (SegW.seq (Q := At exe endPc (swR v (-80) 0) (swFS rS top a v) (startN8 lab tcb top c0))
      (seg_oneW (flag_ndW (n := startN7 lab tcb top c0) (fi := .xor_rr32_self .rbp) rfl hF2
        (code_field hp hend hin.1.2 rfl) (hW.xor v)
        fun σ c hJ fl => ⟨c, .refl c, .inl ⟨(),
          show lab x1L + Int64.ofNat 33 = lab x1L + Int64.ofNat 31 + Int64.ofNat 2 from ofNat_add' _ 31 2,
          by show SO.le SO.entry ((FI.xor_rr32_self .rbp).so SO.entry) = true; decide, ?_⟩⟩))
      (SegW.seq (Q := At exe endPc (swR v (-80) 0) (swFS rS top a v) (startNM lab tcb top c0))
      (seg_oneW (seg_ndW (by simp [startMain]) startMain_ok hF2 hv (Int.le_refl _) (Int.le_refl _)
        (code_field hp hend hin.2 rfl) (hW.blk v) fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩))
      (call_nd_FWK (KC := False) (N := fun e : Empty => e.elim) (E := fun e : Empty => e.elim) (e0 := 0)
        (lo' := -72) (hi' := 8) (M := fun _ => True)
        (Ne := fun _ : Unit => mainN0 lab ⟨top - 8#64, tpOf tcb, c0⟩) (Ex := fun _ (e : Empty) => e.elim)
        hv hF2 (by show (-80 : Int) ≤ -8 - 0 + -72; decide) (by decide) (by show (-8 : Int) - 0 < 0; decide)
        (by show (-8 : Int) - 0 + 8 ≤ 0; decide) (by show ((-8 : Int) - 0) % 8 = 0; decide) (by decide) (by decide)
        (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
        (fun R' F' hR' hlo' hhi' hF' _ hFF hR'e hcc _ _ _ => by
          subst hR'e
          exact main_segW hp hend hK hF' hR' hlo' (by omega) ⟨top - 8#64, tpOf tcb, c0⟩
            ⟨hlimM.rt, hlimM.mp, fun _ h => (hFF _ h).1.2, hlimM.room⟩
            ⟨hlimW.rt, hlimW.mp, fun _ h => (hFF _ h).1.2, hlimW.room⟩ (fun s hAt => hexit _ _ s hAt)
            ((hW.main v).mono fun m h => ⟨hFF m h, hcc m h⟩))
        (fun _ => rfl) (fun σC c hJ => ⟨(), rfl, hJ⟩) fun _ x => x.elim))).mono_post
      fun _ _ h => h.elim (fun ⟨e, _⟩ => e.elim) fun ⟨e, _⟩ => e.elim
    · dsimp only [startN7, startN8] at hJ ⊢
      obtain ⟨rfl, hsp, htp⟩ := hJ
      exact ⟨rfl, hsp, htp⟩
    · dsimp only [startN8, startNM]; rw [startMain_run]
    · dsimp only [startN8, startNM]; rw [startMain_run]; rfl
    · dsimp only [startN8, startNM] at hJ ⊢; rw [startMain_run]
      obtain ⟨rfl, hsp, htp⟩ := hJ
      refine ⟨rfl, ?_, ?_⟩
      · simp [Reg64s.set64, Reg64s.get64, hsp]
      · simp [Reg64s.set64, htp]

/-- **`scc_rt_start` from `.x1` to the switch, inside `W`**
(`start_x1_sw_seg`, its states' obligations `hfs`, `hsys`, `hsw`). -/
theorem start_x1_sw_segW {W : Frag isa} {K : State → State → Prop} (hp : Lays exe SccCode.ret0Cells)
    (hend : endPc = endOf exe SccCode.ret0Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (n0 k0 : BitVec 64) (c0 : Ctl)
    (hfs : BlkW W K exe endPc R F (startN3 (_root_.Executable.labels exe).label n0 k0 c0) startFs)
    (hsys : NodeW W K exe endPc R F
      (startN4 (_root_.Executable.labels exe).label (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0))
    (hsw : BlkW W K exe endPc R F
      (startN5 (_root_.Executable.labels exe).label (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0) startSw) :
    SegW W K p lbl ms (At exe endPc R F (startN3 (_root_.Executable.labels exe).label n0 k0 c0))
      (At exe endPc R F (startN6 (_root_.Executable.labels exe).label
        (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0)) := by
  let lab := (_root_.Executable.labels exe).label
  let tcb := pinA lab + n0 + 8#64
  let top := stacksA lab + k0 + 16384#64
  have hin := ret0_startTailIn
  simp only [startTailIn, Bool.and_eq_true] at hin
  refine SegW.seq (Q := At exe endPc R F (startN4 lab tcb top c0)) ?_
    (SegW.seq (Q := At exe endPc R F (startN5 lab tcb top c0)) ?_ ?_)
  · -- `.x1`'s block
    refine seg_oneW (seg_ndW (by simp [startFs]) startFs_ok hF hR hlo hhi
      (code_field hp hend hin.1.1.1.1.1 (ofNat_zero' _)) hfs fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
    · dsimp only [startN3, startN4]; rw [startFs_run]; rfl
    · dsimp only [startN3, startN4]; rw [startFs_run]; rfl
    · dsimp only [startN3, startN4] at hJ ⊢; rw [startFs_run]
      obtain ⟨⟨rfl, hax, h32⟩, -⟩ := hJ
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first
        | (simp [Reg64s.set64, Reg64s.get64, upd_apply, hax, h32]; done)
        | (simp [Reg64s.set64, Reg64s.get64, upd_apply, hax, h32]; rfl)
  · -- `arch_prctl(ARCH_SET_FS, tcb)`
    refine seg_oneW (archSetFs_ndW hK hF (code_field hp hend hin.1.1.1.1.2 rfl) hsys fun σ c hJ => ?_)
    obtain ⟨rfl, hax, hdi, hsi, h40, h32⟩ := hJ
    refine ⟨_, syscallCall_archSetFs hax hdi, c, .refl c, .inl ⟨(), ofNat_add' _ 18 2,
      by show SO.le oS (syscallSO oS) = true; decide, rfl, ?_, h40, h32⟩⟩
    show UInt64.ofNat σ.regs.rsi.toNat = _
    rw [← hsi]; rfl
  · -- the block after it
    refine seg_oneW (seg_ndW (by simp [startSw]) startSw_ok hF hR hlo hhi
      (code_field hp hend hin.1.1.1.2 rfl) hsw fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
    · dsimp only [startN5, startN6]; rw [startSw_run]; exact ofNat_add' _ 20 8
    · dsimp only [startN5, startN6]; rw [startSw_run]; rfl
    · dsimp only [startN5, startN6] at hJ ⊢; rw [startSw_run]
      obtain ⟨rfl, htp, h40, h32⟩ := hJ
      refine ⟨rfl, ?_, ?_⟩
      · simp [Reg64s.set64, Reg64s.get64, upd_apply, h40]; rfl
      · simp only [Reg64s.set64]; exact htp

/-- **`scc_rt_start` from `.x0` to the switch, inside `W`, the take its
outside move** (`start_x0_x1_seg` then `start_x1_sw_seg`, their states'
obligations `hW`, with `thread_init_segW` at the call): from `.x1` on the
stack range `rS` is in private memory (`StackM`). Given the take's facts at
the region (`hRS`, `hfit`, `hout`, `hFt`). -/
theorem start_x0_sw_segW {W : Frag isa} {rS : Scc.Sem.Range} (hp : Lays exe SccCode.ret0Cells)
    (hend : endPc = endOf exe SccCode.ret0Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi)
    (n0 k0 : BitVec 64) (c0 : Ctl) (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0)
    (hW : X0W W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F rS n0 k0 c0)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (startN2 (_root_.Executable.labels exe).label n0 c0))
      (At exe endPc R (fun m => F m ∧ StackM rS m) (startN6 (_root_.Executable.labels exe).label
        (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0)) := by
  let lab := (_root_.Executable.labels exe).label
  let tcb := pinA lab + n0 + 8#64
  have hin := ret0_startCall2In
  simp only [startCall2In, Bool.and_eq_true] at hin
  have ex1 := label_labelGapB hp hin.2
  have hSM := stackM_stable hfit hout
  have hF2 : FStable R (fun m => F m ∧ StackM rS m) := fun m m' h hd => ⟨hF m m' h.1 hd, hSM m m' h.2 hd⟩
  -- `scc_rt_thread_init`'s region, and `rS` off it
  have hb' := Region.callee_base (hi' := 8) hR (show R.lo ≤ (-48 - 0) + -248 by omega) (by decide)
    (show (-48 - 0 : Int) < R.hi by omega)
  have hRS' : ∀ k, (R.callee (-48 - 0) (-248) 8).Off k → ∀ i < 8,
      (R.callee (-48 - 0) (-248) 8).addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS := fun k hk i hi => by
    rw [Region.callee_addr]
    exact hRS _ (Region.callee_off (show R.lo ≤ (-48 - 0) + -248 by omega) (show (-48 - 0 : Int) + 8 ≤ R.hi by omega)
      (by decide) hk) i hi
  have hout' : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ (R.callee (-48 - 0) (-248) 8).base.toNat + (R.callee (-48 - 0) (-248) 8).lo ∨
        ((R.callee (-48 - 0) (-248) 8).base.toNat : Int) + (R.callee (-48 - 0) (-248) 8).hi ≤ a :=
    fun a h8 ha ha7 => by
      show (a : Int) + 8 ≤ ((R.callee (-48 - 0) (-248) 8).base.toNat : Int) + -248 ∨
        ((R.callee (-48 - 0) (-248) 8).base.toNat : Int) + 8 ≤ a
      rcases hout a h8 ha ha7 with h | h
      · exact .inl (by omega)
      · exact .inr (by omega)
  refine SegW.seq (Q := At exe endPc R F (startNC2 lab tcb c0)) ?_
    (SegW.seq (Q := At exe endPc R (fun m => F m ∧ StackM rS m) (startN3 lab n0 k0 c0))
      ((seg_oneW (n := ⟨lab x1L, ⟨-40, []⟩, (startN3 lab n0 k0 c0).J⟩) ?_).mono_post
        fun _ _ h => At.rbp h fun _ _ h => h.2)
      (start_x1_sw_segW hp hend hK hF2 hR (by omega) (by omega) n0 k0 c0 hW.fs hW.sys hW.sw))
  · -- the call's block
    refine (seg_oneW (seg_ndW (n := startN2R lab n0 c0) (by simp [startCall2]) startCall2_ok hF hR (by omega)
      (by omega) (code_field hp hend hin.1 (ofNat_zero' _)) hW.b0
        fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)).mono_pre
      fun _ _ h => At.rbp_get rfl h
    · dsimp only [startN2R, startN2, startNC2]; rw [startCall2_run]
    · dsimp only [startN2R, startN2, startNC2]; rw [startCall2_run]; rfl
    · dsimp only [startN2R, startN2, startNC2] at hJ ⊢; rw [startCall2_run]
      obtain ⟨⟨⟨rfl, hax⟩, -⟩, hb⟩ := hJ
      refine ⟨⟨rfl, ?_, ?_⟩, ?_, ?_⟩
      · simp [Reg64s.set64, Reg64s.get64, upd_apply, hax]; rfl
      · simp [Reg64s.set64, Reg64s.get64, upd_apply, hax]; rfl
      · simp only [upd_apply, ↓reduceIte]
        rw [show lab x1L = _ from ex1, Int64.toBitVec_add]; rfl
      · simp only [Reg64s.get64, Reg64s.set64] at hb ⊢; rw [hb]; bv_omega
  · -- `scc_rt_thread_init`
    refine call_nd_FW (e0 := 0) (lo' := -248) (hi' := 8) (M := StackM rS)
      (Ne := fun g => tiN lab ⟨g, tcb, k0, c0⟩ .e) (Ex := fun g => tiX lab ⟨g, tcb, k0, c0⟩)
      hR hF (by show R.lo ≤ -48 - 0 + -248; omega) (by decide) (by show (-48 : Int) - 0 < R.hi; omega)
      (by show (-48 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-48 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide)
      (TakeK.kstable hFt)
      (fun s s' hk _ k hk' _ => by obtain ⟨pm, he⟩ := hk.mem; rw [he]; exact loadInt_takeMem (hRS k hk'))
      (fun m h hM => ⟨h, hM⟩)
      (fun R' F' hR' hlo' hhi' hF' hK' hFF' hR'e _ g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, h48, -⟩, ⟨-, -, -, hra, -⟩⟩ := hg'
        have hr : g'.ra = (lab x1L).toBitVec := by
          have e : lab x1L = Int64.ofBitVec g'.ra := by
            rw [← hra]
            show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
            rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
          rw [e]; rfl
        exact (thread_init_segW hp hend hF' hR' hlo' hhi' hFF' ⟨g', tcb, k0, c0⟩ hk hfld htk
          (fun i => (hW.ti g' hr i).mono hFF') hRS' hfit hout' (takeMem_of_kstable hK' exe endPc)).mono_post
          fun s c ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM⟩, hJ⟩ => ⟨x, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hM⟩)
      (fun _ => rfl) ?_ ?_
    · rintro σC c ⟨⟨rfl, h0, -⟩, -, -⟩
      exact ⟨⟨σC.regs.rsp.toBitVec, σC.regs.rbp.toBitVec, σC.slot (-48 - 0 + 0)⟩, rfl, rfl, rfl, rfl, rfl, h0⟩
    · rintro g x σC c σx c' σR ⟨⟨-, -, h32⟩, h48, hb⟩ ⟨-, hsp, hfp, hra, -⟩ ⟨rfl, hsp', hb', hrax⟩ hregs - - hslot
      refine .inl ⟨(), ?_, by show SO.le ⟨-40, []⟩ ⟨-48 - 0 + 8, []⟩ = true; decide, ⟨rfl, ?_, ?_⟩, ?_⟩
      · show lab x1L = Int64.ofBitVec g.ra
        rw [← hra]
        show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
        rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
      · rw [hregs]; exact hrax
      · rw [hslot (-32) ⟨by decide, by omega, by omega⟩ fun h => by
          simp only [Region.Off, Region.callee] at h; dsimp only [startNC2] at h; omega]
        exact h32
      · show σR.regs.get64 .rbp = σR.regs.get64 .rsp + BitVec.ofInt 64 (-8 - -40)
        rw [hregs]
        simp only [Reg64s.get64] at hb ⊢
        rw [hb', hsp', ← hfp, ← hsp]
        show σC.regs.rbp.toBitVec = σC.regs.rsp.toBitVec + 8#64 + BitVec.ofInt 64 (-8 - -40)
        rw [hb]; bv_omega

/-- **`scc_rt_start` up to `.x0` inside `W`** (`start_x0_seg`, its states'
obligations `hW`). The call of `scc_rt_alloc_tcb` asks no closure under `K`
of it (`call_nd_FWK` with `KC := False`): no outside move is in it. -/
theorem start_x0_segW {W : Frag isa} {K : State → State → Prop} (hp : Lays exe SccCode.ret0Cells)
    (hend : endPc = endOf exe SccCode.ret0Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -232) (hhi : 0 ≤ R.hi) (n0 : BitVec 64) (c0 : Ctl) (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F exe endPc n0) (hW : St0W W K exe endPc R F n0 c0) :
    SegW W K p lbl ms (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0))
      (At exe endPc R F (startN2 (_root_.Executable.labels exe).label n0 c0)) := by
  let lab := (_root_.Executable.labels exe).label
  have hin := ret0_startCallIn
  simp only [startCallIn, Bool.and_eq_true] at hin
  have ex0 := label_labelGapB hp hin.2
  have hlo48 : R.lo ≤ -48 := by omega
  refine SegW.seq (ret0_start_segW hp hend hK hF hR (by omega) (by omega) (nC := startN1 lab c0)
      (by show lab startE + Int64.ofNat 43 = lab startE + 7 + 34 + 2; rw [Int64.add_assoc, Int64.add_assoc]; rfl)
      (by show SO.le oS oS = true; decide) hW.start fun _ _ h => h)
    (SegW.seq (Q := At exe endPc R F (startNC lab c0)) ?_
      ((seg_oneW (n := ⟨lab x0L, ⟨-40, []⟩, (startN2 lab n0 c0).J⟩) ?_).mono_post
        fun _ _ h => At.rbp h fun _ _ h => h.2))
  · -- the call's block
    refine (seg_oneW (seg_ndW (n := startN1R lab c0) (by simp [startCall]) startCall_ok hF hR hlo48 hhi
      (code_field hp hend hin.1 rfl) hW.blk fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)).mono_pre
      fun _ _ h => At.rbp_get rfl h
    · dsimp only [startN1R, startN1, startNC]; rw [startCall_run]
    · dsimp only [startN1R, startN1, startNC]; rw [startCall_run]; rfl
    · dsimp only [startN1R, startN1, startNC] at hJ ⊢; rw [startCall_run]
      obtain ⟨rfl, hb⟩ := hJ
      refine ⟨⟨rfl, ?_, ?_⟩, ?_, ?_⟩
      · simp [Reg64s.set64]
      · simp [Reg64s.set64]
      · simp only [upd_apply, ↓reduceIte]
        rw [show lab x0L = _ from ex0, Int64.toBitVec_add, Int64.toBitVec_add, BitVec.add_assoc]; rfl
      · simp only [Reg64s.get64, Reg64s.set64] at hb ⊢; rw [hb]; bv_omega
  · -- `scc_rt_alloc_tcb`
    refine call_nd_FWK (KC := False) (e0 := 0) (lo' := -184) (hi' := 8) (M := fun _ => True)
      (Ne := fun g => tcbN lab ⟨g, n0, c0⟩ .e) (Ex := fun g => tcbX lab ⟨g, n0, c0⟩)
      hR hF (by show R.lo ≤ -48 - 0 + -184; omega) (by decide) (by show (-48 : Int) - 0 < R.hi; omega)
      (by show (-48 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-48 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide) (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' hlo' hhi' hF' _ hFF hR'e _ g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, h48, -⟩, ⟨-, -, -, hra, -⟩⟩ := hg'
        have hr : g'.ra = (lab x0L).toBitVec := by
          have e : lab x0L = Int64.ofBitVec g'.ra := by
            rw [← hra]
            show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
            rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
          rw [e]; rfl
        exact (alloc_tcb_segW hp hend hF' hR' hlo' hhi' hFF ⟨g', n0, c0⟩ hn hhdr htcb
          fun i => (hW.tcb g' hr i).mono hFF).mono_post fun _ _ ⟨x, h⟩ => ⟨x, h, trivial⟩)
      (fun _ => rfl) ?_ ?_
    · rintro σC c ⟨⟨rfl, h0, h1⟩, -, -⟩
      exact ⟨⟨σC.regs.rsp.toBitVec, σC.regs.rbp.toBitVec, σC.slot (-48 - 0 + 0)⟩, rfl, rfl, rfl, rfl, rfl, h0, h1⟩
    · rintro g x σC c σx c' σR ⟨-, h48, hb⟩ ⟨-, hsp, hfp, hra, -⟩ ⟨rfl, hsp', hb', hrax⟩ hregs - - -
      refine .inl ⟨(), ?_, by show SO.le ⟨-40, []⟩ ⟨-48 - 0 + 8, []⟩ = true; decide, ⟨rfl, ?_⟩, ?_⟩
      · show lab x0L = Int64.ofBitVec g.ra
        rw [← hra]
        show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
        rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
      · rw [hregs]; exact hrax
      · show σR.regs.get64 .rbp = σR.regs.get64 .rsp + BitVec.ofInt 64 (-8 - -40)
        rw [hregs]
        simp only [Reg64s.get64] at hb ⊢
        rw [hb', hsp', ← hfp, ← hsp]
        show σC.regs.rbp.toBitVec = σC.regs.rsp.toBitVec + 8#64 + BitVec.ofInt 64 (-8 - -40)
        rw [hb]; bv_omega

/-- **`scc_rt_start` never returns, inside `W`, the take its outside move**
(`start_seg`, its states' obligations `hW`): `start_x0_segW`, then
`start_x0_sw_segW` (the take nested, so at the switch the stack range `rS`
is in private memory), then `start_switch_segW`. `start_seg`'s `hmap` is
not asked: it follows from the take and the new region lying in `rS`
(`hsub`). The take's facts at the region: `hRS`, `hfitS`, `houtS`, `hFt`. -/
theorem start_segW {W : Frag isa} {rS : Scc.Sem.Range} (hp : Lays exe SccCode.ret0Cells)
    (hend : endPc = endOf exe SccCode.ret0Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi) (n0 k0 : BitVec 64) (c0 : Ctl) (hn : n0.toNat + 80 ≤ 131072)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hhdr : StOk ms F (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F exe endPc n0)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0)
    (hok : (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).OK)
    (hsub : ∀ k, (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).Off k →
      ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-80) 0).addr k).toNat + 7))
    (hfit : (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat + -80 ∨
      ((stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat : Int) + 0 ≤
        (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat)
    (hlimM : LimOk ms F (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - (32 : Int64).toBitVec))
    (hlimW : LimOk ms F (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - (32 : Int64).toBitVec -
        8#64 - 8#64 - (16 : Int64).toBitVec))
    (hexit : ∀ R' F' s, At exe endPc R' F' (mainNX (_root_.Executable.labels exe).label) s c0 → ¬ ms.abortAt s →
      MainExit p ms s c0 42)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hW : StartAllW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F ms rS n0 k0 c0)
    {Q : Frag isa} :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0)) Q :=
  (start_x0_segW hp hend hK hF hR (by omega) (by omega) n0 c0 hn hhdr htcb hW.s1).seq
    ((start_x0_sw_segW hp hend hK hF hR hlo hhi n0 k0 c0 hk hfld htk hW.s2 hRS hfitS houtS hFt).seq
      (start_switch_segW hp hend hK _ _ c0 hok (fun _ h => h.2) hfitS hsub hfit hout
        (hlimM.mono fun _ h => h.1) (hlimW.mono fun _ h => h.1) hexit hW.s3))

end StartWProof

end Spike.Lib.X64.Flow.Ret0
