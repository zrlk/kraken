/-
**hello.w's `wc_main` from `.x23` to `.x25`** (x86-64; the twin of `Spike/Lib/A64HelloWcSp3.lean`), inside `W`,
in any valid layout of `helloCells`, in `wc_main`'s frame of 128 (`oWH`): wake's `X64WakeTcb2Call`,
`X64WakeWcSp3Seg`, `X64WakeWcSp4` and `X64WakeWcSp4Seg` (up to the call's return) at hello's listing:

    .Lwc_main.x1:                      -- %rax = the reserve's id 1
      movq %rax, -56(%rbp)
      movq $12587011, %rdi              -- %rdi = hdrH (n = 16, m = 3)
      movq $1, %rsi
      call scc_rt_alloc_tcb             -- (tcb2CallH), .x24 pushed at -136; the callee (allocTcbG_segWA)
    .Lwc_main.x2:                      -- %rax = the TCB t = pinA + 144
      movq %rax, -64(%rbp); movq -64(%rbp), %rcx; movq -56(%rbp), %rax   (sp4AH)
      movq %rax, 56(%rcx)               -- row: the TCB's tid word (rtst_ndW)
      movq -64(%rbp), %rdi; call scc_rt_thread_init                     (initCallH), the callee `hti`
    .Lwc_main.x3:                      -- `wcN6H` (X64HelloWcSp6) at the stack top `kOf lab`

The frame's words `FrWH sl me cA fr` (the five spills, the cell at `-48`, the caller's `%rbp` and return address
at `0`, `8`) survive both calls (above the callees' regions). The call's ghost record is
`tcb2QH g c0 := ⟨g, hdrH, 112, c0⟩`: the counter's old value `112` is `scc_rt_start`'s first TCB, so the TCB is
`pinA + 144` (`tcb2QH_tcbOf`). `scc_rt_thread_init` at the second take returns wake's `kOf lab`.

- `oCH`, `tcb2CallH`, `sp4AH`, `initCallH` (`block_spec`); `x23L`, `x24L`; `wcSp3InH`, `hello_wcSp3InH`,
  `hello_allocTcbIn`: the blocks, the row and the labels' gaps in `helloCells`.
- `tcb2CallH_rdi`, `tcb2CallH_rsi`, `tcb2CallH_pc`, `tcb2CallH_keep`, `tcb2CallH_ra`: the call block's run.
- `hdrH`, `mOf_hdrH`, `tcb2QH`, `tcb2QH_hdrA`, `tcb2QH_tcbOf`, `tH`: the header, the ghost record, the TCB.
- `j3H`, `wcN3H`, `wcNCH`, `wcNCRH`, `n24I`, `j3H_self`: `.x23`'s node (`%rax = 1`, the frame's words), the call
  node (and with `%rbp` from its offsets), the landing at `.x24`; any state with `%rax = 1` is at `j3H` of its
  own slots.
- `aNH`, `wcNIH`, `wcNIRH`, `n25I`: `.x24`'s nodes (`.n20`, `.n20s`, `.n20p`) and the call node of
  `scc_rt_thread_init`; `sp4AH_edge`, `initCallH_edge`: the blocks' edges.
- `TcbCtxH`, `WcSp3WH`, `hello_wc_sp3_segW`: `.x23` to `.x24` (`aNH .n20` at `tH`).
- `WcSp4WH`, `hello_wc_sp4_pre_segW`, `hello_wc_sp4_call_segW`: `.x24` to the call, the call to `.x25` (`wcN6H`).

## Differences from the AArch64 version

- The return address is the word the `call` pushes at `-136` (`tcb2CallH_ra`, `initCallH_edge`; A64's `x30`), so
  the call nodes are at `oCH = ⟨-136, [(.rbp, 0)]⟩`; the callees' regions are `R.callee (-136) (-184) 8` and
  `R.callee (-136) (-248) 8` (A64's `R.callee (-144) (-192) 0`, `(-256) 0`); back from a callee only `%rsp`'s
  offset is known, so the calls land at `n24I`, `n25I` and `At.rbp` restores `oWH`, as in wake's x86-64
  segments; no `hal`.
- The id is spilled at `-56`, the TCB at `-64` (A64's `[sp, #48]`, `[sp, #56]`, i.e. `-96`, `-88`); the tid
  store goes through `%rcx`/`%rax` (A64's `x10`/`x9`). The nodes before the call are wake x86-64's `XA`
  (`.n20`, `.n20s`, `.n20p` for A64's `.n4`, `.n4s`, `.n5`); `WcSp4WH`'s fields keep A64's names.
- The edges are `Hit`s (x86-64's form); A64's `hit_of_edgeH` has no counterpart. A64's `hello_wc_sp4_segW` and
  `hello_wc_sp3_sp6_segW` are dead and not twinned.
-/
import Spike.Lib.X64HelloWcSp6
import Spike.Lib.X64WakeWcSp3Seg

namespace Spike.Lib.X64.Flow.HelloWc

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (CallerCells StOk TiG tiN tiX)
open Spike.Lib.X64.Flow.Ret0.AllocTcb (mOf)
open Spike.Lib.X64.HelloPh.WcSp6 (oWH x25L FrWH wcN6H)
open Spike.Lib.X64.WakePh.WcSp4 (tidSt)
open Spike.Lib.X64.Flow.WakeWc (tcbWG_mono tidSt_eq kOf tiQ XA)
open Spike.Lib.X64.Rt (TcbGG TcbWG TcbOkGA tcbNG tcbXG hdrA tcbOf allocTcbG_segWA)
open Scc.Cert.Rt.X64 (Lays endOf blockAt labelGap codeAt_blockAt_lays label_labelGap_lays)
open SccCode (helloCells)

set_option linter.unusedSimpArgs false

/-! ## The blocks, the row and the checks -/

/-- The offsets after a `call` in `wc_main` (the return address at `-136`). -/
abbrev oCH : SO := ⟨-136, [(.rbp, 0)]⟩

/-- The label of `.x23`. -/
abbrev x23L : Label := ".Lwc_main.x1"

/-- The label of `.x24`. -/
abbrev x24L : Label := ".Lwc_main.x2"

/-- **The second call's block** at `.x23`. -/
def tcb2CallH : List (Directive × Nat) := (parse("movq %rax, -56(%rbp)
movq $12587011, %rdi
movq $1, %rsi
call scc_rt_alloc_tcb")).zip [4, 7, 7, 5]

/-- `.x24`'s first block: the TCB to `-64` and `%rcx`, the reserve's id to `%rax`. -/
def sp4AH : List (Directive × Nat) := (parse("movq %rax, -64(%rbp)
movq -64(%rbp), %rcx
movq -56(%rbp), %rax")).zip [4, 4, 4]

/-- The call of `scc_rt_thread_init` on the TCB. -/
def initCallH : List (Directive × Nat) := (parse("movq -64(%rbp), %rdi
call scc_rt_thread_init")).zip [4, 5]

block_spec tcb2CallH (-136) 16 oWH tcb2CallH
block_spec sp4AH (-128) 16 oWH sp4AH
block_spec initCallH (-136) 16 oWH initCallH

/-- **The blocks and the row in `cells`**: the call block at `.x23`, `.x24` 23 bytes after; at `.x24` the blocks
and the tid store (indices `0`, `3`, `4`, byte offsets `0`, `12`, `16`), `.x25` six instructions and 25 bytes
after. -/
def wcSp3InH (cells : List (Directive × Nat)) : Bool :=
  blockAt cells x23L 0 0 tcb2CallH && labelGap cells x23L x24L 4 23 && blockAt cells x24L 0 0 sp4AH &&
    blockAt cells x24L 3 12 tidSt && blockAt cells x24L 4 16 initCallH && labelGap cells x24L x25L 6 25

theorem hello_wcSp3InH : wcSp3InH helloCells = true := by decide +kernel

theorem hello_allocTcbIn : Ret0.AllocTcb.allocTcbIn helloCells = true := by decide +kernel

/-! ## The call block's run -/

section Run

variable (lab : Label → Int64) (pc : Int64) (σ : AS)

/-- The run's `%rdi` is the header `12587011`. -/
theorem tcb2CallH_rdi : (arun lab tcb2CallH ⟨pc, oWH, σ⟩).σ.regs.rdi.toBitVec = 12587011#64 := by
  rw [tcb2CallH_run]; rfl

/-- The run's `%rsi` is `1`. -/
theorem tcb2CallH_rsi : (arun lab tcb2CallH ⟨pc, oWH, σ⟩).σ.regs.rsi.toBitVec = 1#64 := by
  rw [tcb2CallH_run]; rfl

/-- The run ends at the callee's label, `%rsp` past the return address. -/
theorem tcb2CallH_pc : (arun lab tcb2CallH ⟨pc, oWH, σ⟩).pc = lab "scc_rt_alloc_tcb" ∧
    (arun lab tcb2CallH ⟨pc, oWH, σ⟩).so = oCH := by
  rw [tcb2CallH_run]; exact ⟨rfl, rfl⟩

/-- The run moves `%rsp` 8 down, keeps `%rbp`, and writes the frame's `-56` (the reserve's result) and `-136`
(the return address `pc + 23`). -/
theorem tcb2CallH_keep :
    (arun lab tcb2CallH ⟨pc, oWH, σ⟩).σ.regs.rsp.toBitVec = σ.regs.rsp.toBitVec - 8#64 ∧
    (arun lab tcb2CallH ⟨pc, oWH, σ⟩).σ.regs.rbp = σ.regs.rbp ∧
    (arun lab tcb2CallH ⟨pc, oWH, σ⟩).σ.slot =
      upd (upd σ.slot (-56) σ.regs.rax.toBitVec) (-136) (pc.toBitVec + 23#64) := by
  rw [tcb2CallH_run]; exact ⟨rfl, rfl, rfl⟩

end Run

/-- **The return address is `.x24`** in any layout of `helloCells`, from `.x23`. -/
theorem tcb2CallH_ra {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
    (hp : Lays exe helloCells kp) (σ : AS) :
    (arun (_root_.Executable.labels exe).label tcb2CallH
        ⟨(_root_.Executable.labels exe).label x23L, oWH, σ⟩).σ.slot (-136) =
      ((_root_.Executable.labels exe).label x24L).toBitVec := by
  have hin := hello_wcSp3InH
  simp only [wcSp3InH, Bool.and_eq_true] at hin
  rw [label_labelGap_lays hp hin.1.1.1.1.2, (tcb2CallH_keep _ _ _).2.2, Int64.toBitVec_add]
  simp only [upd_apply, ↓reduceIte]; rfl

/-! ## The header, the ghost record, the TCB -/

/-- **The second TCB's header** (`n = 12`, `m = 3`; `X64HelloOwn2.hdr2H`). -/
abbrev hdrH : BitVec 64 := 12587011#64

theorem mOf_hdrH : mOf hdrH <<< 3 = 24#64 := by decide

/-- **The second call's ghost record**: the header `hdrH`, the counter's old value `112` (the first TCB's 112
bytes). -/
def tcb2QH (g : Ret0.AllocTcb.G) (c0 : Ctl) : TcbGG := ⟨g, hdrH, 112#64, c0⟩

/-- `tcb2QH`'s header word: `pinned + 136`. -/
theorem tcb2QH_hdrA (lab : Label → Int64) (g : Ret0.AllocTcb.G) (c0 : Ctl) :
    hdrA lab (tcb2QH g c0) = Ret0.pinA lab + 136#64 := by
  show Ret0.pinA lab + 112#64 + mOf hdrH <<< 3 = _
  rw [mOf_hdrH, BitVec.add_assoc]; rfl

/-- The second TCB: `pinA + 144`. -/
abbrev tH (lab : Label → Int64) : BitVec 64 := Ret0.pinA lab + 144#64

/-- **`tcb2QH`'s TCB**: `pinned + 144`. -/
theorem tcb2QH_tcbOf (lab : Label → Int64) (g : Ret0.AllocTcb.G) (c0 : Ctl) :
    tcbOf lab (tcb2QH g c0) = tH lab := by
  show hdrA lab (tcb2QH g c0) + 8#64 = _
  rw [tcb2QH_hdrA, BitVec.add_assoc]; rfl

/-! ## The nodes -/

section Nodes

variable (lab : Label → Int64) (c0 : Ctl) (t : BitVec 64) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)
  (me cA : BitVec 64) (fr : BitVec 64 × BitVec 64)

/-- **`.x23`'s invariant**: the reserve's id `1` in `%rax`, the frame's words. -/
def j3H (σ : AS) : Prop := σ.regs.rax.toBitVec = 1#64 ∧ FrWH sl me cA fr σ

/-- **At `.x23`**: the source at `c0`, `j3H`. -/
def wcN3H : ND := ⟨lab x23L, oWH, fun σ c => c = c0 ∧ j3H sl me cA fr σ⟩

/-- **The call node**: at `scc_rt_alloc_tcb`, its arguments `hdrH` and `1`, `.x24` pushed at `-136`; the
frame's words and the id at `-56`. -/
def wcNCH : ND := ⟨lab Ret0.AllocTcb.fnL, oCH, fun σ c => c = c0 ∧
  σ.regs.rdi.toBitVec = hdrH ∧ σ.regs.rsi.toBitVec = 1#64 ∧ σ.slot (-136) = (lab x24L).toBitVec ∧
  FrWH sl me cA fr σ ∧ σ.slot (-56) = 1#64⟩

/-- **The call node with `%rbp` from its offsets** (`Ret0.At.rbp_get`): `%rbp` `136` bytes above `%rsp`. -/
def wcNCRH : ND := ⟨(wcNCH lab c0 sl me cA fr).pc, oCH, fun σ c => (wcNCH lab c0 sl me cA fr).J σ c ∧
  σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (0 - -136)⟩

/-- **`.x24`'s nodes before the call**: `.x24` (`%rax` the TCB `t`), the tid store (`%rcx` and `-64` the TCB,
`%rax` the id `-56`), past it; the id `1` at `-56` up to the tid store. -/
def aNH : XA → ND
  | .n20 => ⟨lab x24L, oWH, fun σ c => c = c0 ∧ σ.regs.get64 .rax = t ∧ FrWH sl me cA fr σ ∧
      σ.slot (-56) = 1#64⟩
  | .n20s => ⟨lab x24L + 12, oWH, fun σ c => c = c0 ∧ σ.regs.get64 .rcx = t ∧
      σ.regs.get64 .rax = σ.slot (-56) ∧ σ.slot (-64) = t ∧ FrWH sl me cA fr σ ∧ σ.slot (-56) = 1#64⟩
  | .n20p => ⟨lab x24L + 16, oWH, fun σ c => c = c0 ∧ σ.slot (-64) = t ∧ FrWH sl me cA fr σ⟩

/-- **Back at `.x24`** with only `%rsp`'s offset known: `aNH .n20`'s facts at `tH`, `%rbp` `128` bytes above
`%rsp` (`At.rbp` makes it `aNH .n20`). -/
def n24I : ND := ⟨lab x24L, ⟨-128, []⟩, fun σ c => (aNH lab c0 (tH lab) sl me cA fr .n20).J σ c ∧
  σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (0 - -128)⟩

/-- **The call node of `scc_rt_thread_init`**: `%rdi` the TCB, `.x25` pushed at `-136`. -/
def wcNIH : ND := ⟨lab Ret0.ThreadInit.fnL, oCH, fun σ c => c = c0 ∧ σ.regs.get64 .rdi = t ∧
  σ.slot (-136) = (lab x25L).toBitVec ∧ σ.slot (-64) = t ∧ FrWH sl me cA fr σ⟩

/-- **The call node with `%rbp` from its offsets**. -/
def wcNIRH : ND := ⟨(wcNIH lab c0 t sl me cA fr).pc, oCH, fun σ c => (wcNIH lab c0 t sl me cA fr).J σ c ∧
  σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (0 - -136)⟩

/-- **Back at `.x25`** with only `%rsp`'s offset known: `wcN6H`'s facts at the stack top `kOf lab`. -/
def n25I : ND := ⟨lab x25L, ⟨-128, []⟩, fun σ c => (wcN6H lab c0 t (kOf lab) sl me cA fr).J σ c ∧
  σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (0 - -128)⟩

end Nodes

/-- **Any state with `%rax = 1`** is at `j3H` of its own frame's words. -/
theorem j3H_self {σ : AS} (h : σ.regs.rax.toBitVec = 1#64) :
    j3H (σ.slot (-8), σ.slot (-16), σ.slot (-24), σ.slot (-32)) (σ.slot (-40)) (σ.slot (-48))
      (σ.slot 0, σ.slot 8) σ :=
  ⟨h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The edges -/

section Edges

variable {lab : Label → Int64} {c0 : Ctl} {t : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
  {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64} {σ : AS} {c : Ctl}

/-- `sp4AH` from `.x24` to the tid store. -/
theorem sp4AH_edge (hJ : (aNH lab c0 t sl me cA fr .n20).J σ c) :
    Hit (aNH lab c0 t sl me cA fr .n20s) (arun lab sp4AH ⟨(aNH lab c0 t sl me cA fr .n20).pc, oWH, σ⟩) c := by
  obtain ⟨h0, ht, ⟨h8, h16, h24, h32, h40, h48, hf1, hf2⟩, h56⟩ := hJ
  rw [sp4AH_run]
  refine ⟨by simp only [aNH], rfl, h0, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [Reg64s.get64] at ht ⊢; exact ht
  · simp [upd, Reg64s.get64]
  · simp [Reg64s.get64] at ht ⊢; exact ht
  all_goals simp [upd, h8, h16, h24, h32, h40, h48, hf1, hf2, h56]

/-- `initCallH` from past the tid store to `scc_rt_thread_init`, `.x25` pushed, in any layout of
`helloCells`. -/
theorem initCallH_edge {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
    (hp : Lays exe helloCells kp) (hJ : (aNH (_root_.Executable.labels exe).label c0 t sl me cA fr .n20p).J σ c) :
    Hit (wcNIH (_root_.Executable.labels exe).label c0 t sl me cA fr)
      (arun (_root_.Executable.labels exe).label initCallH
        ⟨(aNH (_root_.Executable.labels exe).label c0 t sl me cA fr .n20p).pc, oWH, σ⟩) c := by
  obtain ⟨h0, h64, h8, h16, h24, h32, h40, h48, hf1, hf2⟩ := hJ
  have hin := hello_wcSp3InH
  simp only [wcSp3InH, Bool.and_eq_true] at hin
  have hg := label_labelGap_lays hp hin.2
  rw [initCallH_run]
  refine ⟨rfl, rfl, h0, ?_, ?_, ?_, ?_⟩
  · simp [Reg64s.get64, h64]
  · simp only [upd_apply, ↓reduceIte, aNH, hg, Int64.toBitVec_add, BitVec.add_assoc]; rfl
  · simp [upd, h64]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [upd, h8, h16, h24, h32, h40, h48, hf1, hf2]

end Edges

/-! ## `.x23` to `.x24` -/

/-- **The second TCB call's context in `wc_main`'s region `R`** at the memory `mm`, for the ghost `g`: a caller's
state at the call node `Jc` (`(wcNCRH lab c0 sl me cA fr).J`), the callee's entry, the caller's cells kept. -/
def TcbCtxH (lab : Label → Int64) (R : Region) (Jc : AS → Ctl → Prop) (c0 : Ctl) (g : Ret0.AllocTcb.G)
    (mm : MachineData) : Prop :=
  ∃ mC σC c, Abs R oCH mC σC ∧ Jc σC c ∧ (tcbNG lab (tcb2QH g c0) .e).J (enter (-136) σC) c ∧
    CKept R (-136) (-184) 8 mC mm

/-- **`.x23`'s states to `.x24` inside `W`**: the call block's and the callee's (in its region, for any return
to `.x24`). -/
structure WcSp3WH (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (c0 : Ctl) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)
    (me cA : BitVec 64) (fr : BitVec 64 × BitVec 64) : Prop where
  blk : BlkW W K exe endPc R F (wcN3H (_root_.Executable.labels exe).label c0 sl me cA fr) tcb2CallH
  tcb : ∀ g : Ret0.AllocTcb.G, g.ra = ((_root_.Executable.labels exe).label x24L).toBitVec →
    ∀ i, TcbWG W K exe endPc (R.callee (-136) (-184) 8)
      (fun mm => F mm ∧ CallerCells R (-136) (-184) 8 mm ∧
        TcbCtxH (_root_.Executable.labels exe).label R (wcNCRH (_root_.Executable.labels exe).label c0 sl me cA fr).J
          c0 g mm)
      (tcb2QH g c0) i

/-- From `.x23` to `.x24` inside the trivial predicate, with no outside moves. -/
theorem WcSp3WH.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {c0 : Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} :
    WcSp3WH (fun _ _ => True) (fun _ _ => False) exe endPc R F c0 sl me cA fr := by
  refine ⟨BlkW.triv, fun _ _ i => ?_⟩
  cases i <;> dsimp only [TcbWG] <;> first | exact BlkW.triv | exact NodeW.triv

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` from `.x23` to `.x24` is one segment inside `W`** in any valid layout of `helloCells`: from `.x23`
(the reserve's id `1` in `%rax`, the frame's words, the source at `c0`) to `aNH .n20` at the second TCB `tH`.
`scc_rt_alloc_tcb` at `tcb2QH g c0` writes the header word (`hhdr`) and adds to the counter (`htcb`), moving only
memory `K` keeps off the caller's cells (`hFK`, `hKR`). Its states lie in `W` (`hW`). -/
theorem hello_wc_sp3_segW {W : Frag isa} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe helloCells kp) (hend : endPc = endOf exe helloCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -320) (hhi : 16 ≤ R.hi)
    {c0 : Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (hW : WcSp3WH W K exe endPc R F c0 sl me cA fr)
    (hhdr : ∀ g, StOk ms F (hdrA (_root_.Executable.labels exe).label (tcb2QH g c0))
      ((tcb2QH g c0).h ||| 1#64 <<< 36))
    (htcb : ∀ g, TcbOkGA ms F exe endPc (R.callee (-136) (-184) 8) F (tcb2QH g c0))
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-136) (-184) 8).Off (k - -136) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8) :
    SegW W K p lbl ms (At exe endPc R F (wcN3H (_root_.Executable.labels exe).label c0 sl me cA fr))
      (At exe endPc R F (aNH (_root_.Executable.labels exe).label c0 (tH (_root_.Executable.labels exe).label)
        sl me cA fr .n20)) := by
  let lab := (_root_.Executable.labels exe).label
  have hin := hello_wcSp3InH
  simp only [wcSp3InH, Bool.and_eq_true] at hin
  -- the call block
  have hA : SegW W K p lbl ms (At exe endPc R F (wcN3H lab c0 sl me cA fr))
      (At exe endPc R F (wcNCH lab c0 sl me cA fr)) := by
    refine Ret0.seg_oneW (seg_ndW (by simp [tcb2CallH]) tcb2CallH_ok hF hR (by omega) hhi
      (fun s he hn => (by simpa using codeAt_blockAt_lays hp he (hn.trans hend) hin.1.1.1.1.1 :
        CodeAt s (lab x23L) tcb2CallH)) hW.blk fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_⟩⟩)
    obtain ⟨-, -, hsl⟩ := tcb2CallH_keep lab (lab x23L) σ
    obtain ⟨hc, hax, h8, h16, h24, h32, h40, h48, hf1, hf2⟩ := hJ
    refine ⟨(tcb2CallH_pc lab _ σ).1.symm, ?_, hc, tcb2CallH_rdi lab _ σ, tcb2CallH_rsi lab _ σ,
      tcb2CallH_ra hp σ, ?_, ?_⟩
    · show SO.le oCH (arun lab tcb2CallH ⟨lab x23L, oWH, σ⟩).so = true
      rw [(tcb2CallH_pc lab (lab x23L) σ).2]; decide
    · show FrWH sl me cA fr (arun lab tcb2CallH ⟨lab x23L, oWH, σ⟩).σ
      simp only [FrWH, hsl, upd_apply]
      exact ⟨h8, h16, h24, h32, h40, h48, hf1, hf2⟩
    · show (arun lab tcb2CallH ⟨lab x23L, oWH, σ⟩).σ.slot (-56) = 1#64
      simp only [hsl, upd_apply]
      exact hax
  -- the call
  have hC : SegW W K p lbl ms (At exe endPc R F (wcNCRH lab c0 sl me cA fr))
      (At exe endPc R F (n24I lab c0 sl me cA fr)) := by
    refine Ret0.seg_oneW (call_nd_FWK (KC := True) (e0 := 0) (lo' := -184) (hi' := 8) (M := fun _ => True)
      (nC := wcNCRH lab c0 sl me cA fr) (N := fun _ : Unit => n24I lab c0 sl me cA fr)
      (E := fun e : Empty => e.elim)
      (Ne := fun g : Ret0.AllocTcb.G => tcbNG lab (tcb2QH g c0) .e)
      (Ex := fun g : Ret0.AllocTcb.G => tcbXG lab (tcb2QH g c0))
      hR hF (by show R.lo ≤ -136 - 0 + -184; omega) (by decide) (by show (-136 : Int) - 0 < R.hi; omega)
      (by show (-136 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-136 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide) (fun _ => hFK) (fun _ => hKR) (fun _ h _ => h)
      (fun R' F' hR' hlo' hhi' hF' _ hFF hR'e hcc g hg hkeep => by
        subst hR'e
        obtain ⟨σC, c, ⟨⟨-, -, -, h136, -⟩, -⟩, ⟨-, -, -, hra, -, -⟩⟩ := hg
        have hr : g.ra = (lab x24L).toBitVec := by
          change (tcb2QH g c0).g.ra = _
          rw [← hra, ← h136]; rfl
        exact (allocTcbG_segWA hp hend hello_allocTcbIn hF' hR' hlo' hhi' hFF (tcb2QH g c0)
          (by show (112#64 : BitVec 64).toNat + (Ret0.AllocTcb.lenOf hdrH).toNat ≤ 131072; decide)
          (hhdr g) ((htcb g).mono hFF)
          fun i => tcbWG_mono (hW.tcb g hr i) fun m h => ⟨hFF m h, hcc m h, hkeep m h⟩).mono_post
          fun _ _ ⟨x, h⟩ => ⟨x, h, trivial⟩)
      (fun _ => rfl) ?_ ?_)
    · rintro σC c ⟨⟨hc, hdi, hsi, -⟩, -⟩
      exact ⟨⟨σC.regs.rsp.toBitVec, σC.regs.rbp.toBitVec, σC.slot (-136 - 0 + 0)⟩, rfl, hc, rfl, rfl, rfl, hdi, hsi⟩
    · rintro g ⟨⟩ σC c σx c' σR ⟨⟨-, -, -, h136, ⟨h8, h16, h24, h32, h40, h48, hf1, hf2⟩, h56⟩, hb⟩
        ⟨-, hsp, hfp, hra, -, -⟩ ⟨hc', hpost⟩ hreg - - hsl
      have hkeep : ∀ k : Int, -128 ≤ k → k + 8 ≤ 16 → k % 8 = 0 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
        hsl k ⟨h3, by omega, by omega⟩ fun h => by simp only [Region.Off, Region.callee, wcNCRH, oCH] at h; omega
      refine .inl ⟨(), ?_, by show SO.le ⟨-128, []⟩ ⟨-136 - 0 + 8, []⟩ = true; decide,
        ⟨⟨hc', ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩⟩
      · show lab x24L = Int64.ofBitVec (tcb2QH g c0).g.ra
        rw [← hra]
        show _ = Int64.ofBitVec (σC.slot (-136 - 0 + 0))
        rw [show (-136 : Int) - 0 + 0 = -136 by decide, h136, int64_ofBitVec_toBitVec]
      · show σR.regs.rax.toBitVec = tH lab
        rw [hreg, Rt.postG_tcbOf lab (tcb2QH g c0) hpost, tcb2QH_tcbOf]
      · rw [hkeep (-8) (by omega) (by omega) (by omega), h8]
      · rw [hkeep (-16) (by omega) (by omega) (by omega), h16]
      · rw [hkeep (-24) (by omega) (by omega) (by omega), h24]
      · rw [hkeep (-32) (by omega) (by omega) (by omega), h32]
      · rw [hkeep (-40) (by omega) (by omega) (by omega), h40]
      · rw [hkeep (-48) (by omega) (by omega) (by omega), h48]
      · rw [hkeep 0 (by omega) (by omega) (by omega), hf1]
      · rw [hkeep 8 (by omega) (by omega) (by omega), hf2]
      · rw [hkeep (-56) (by omega) (by omega) (by omega), h56]
      · show σR.regs.get64 .rbp = σR.regs.get64 .rsp + BitVec.ofInt 64 (0 - -128)
        rw [hreg]
        simp only [Reg64s.get64] at hb ⊢
        rw [hpost.2.1, hpost.1, ← hfp, ← hsp]
        show σC.regs.rbp.toBitVec = σC.regs.rsp.toBitVec + 8#64 + BitVec.ofInt 64 (0 - -128)
        rw [hb]; bv_omega
  exact (hA.mono_post fun _ _ h => Ret0.At.rbp_get rfl h).seq
    (hC.mono_post fun _ _ h => Ret0.At.imp (At.rbp h fun _ _ h => h.2) fun _ _ h => h.1)

end Seg

/-! ## `.x24` to `.x25` -/

/-- **`.x24`'s states to the call of `scc_rt_thread_init` inside `W`**, none moved by `K`: the blocks' and the
row's. -/
structure WcSp4WH (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (c0 : Ctl) (t : BitVec 64)
    (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (me cA : BitVec 64) (fr : BitVec 64 × BitVec 64) :
    Prop where
  n4 : BlkW W K exe endPc R F (aNH (_root_.Executable.labels exe).label c0 t sl me cA fr .n20) sp4AH
  n4s : NodeW W K exe endPc R F (aNH (_root_.Executable.labels exe).label c0 t sl me cA fr .n20s)
  n5 : BlkW W K exe endPc R F (aNH (_root_.Executable.labels exe).label c0 t sl me cA fr .n20p) initCallH

/-- From `.x24` to the call inside the trivial predicate, with no outside moves. -/
theorem WcSp4WH.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {c0 : Ctl} {t : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} :
    WcSp4WH (fun _ _ => True) (fun _ _ => False) exe endPc R F c0 t sl me cA fr :=
  ⟨BlkW.triv, NodeW.triv, BlkW.triv⟩

section Seg4

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` from `.x24` to the call of `scc_rt_thread_init`** (`wcNIH`): the TCB to `-64`, the id `1` to the
TCB's tid word `t + 56` (a runtime word the store may write: `htid`). -/
theorem hello_wc_sp4_pre_segW {W : Frag isa} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe helloCells kp) (hend : endPc = endOf exe helloCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -136) (hhi : 16 ≤ R.hi)
    {c0 : Ctl} {t : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64}
    (hW : WcSp4WH W K exe endPc R F c0 t sl me cA fr)
    (htid : ms.rt (t + 56#64).toNat ∧ ms.mp ⟨t + 56#64, 8⟩ true ∧ ms.G ⟨t + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none) :
    SegW W K p lbl ms (At exe endPc R F (aNH (_root_.Executable.labels exe).label c0 t sl me cA fr .n20))
      (At exe endPc R F (wcNIH (_root_.Executable.labels exe).label c0 t sl me cA fr)) := by
  have hin := hello_wcSp3InH
  simp only [wcSp3InH, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨-, b0⟩, bs⟩, bp⟩, -⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have code : ∀ {k off : Nat} {b : List (Directive × Nat)}, blockAt helloCells x24L k off b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (lab x24L + Int64.ofNat off) b :=
    fun h s he hn => codeAt_blockAt_lays hp he (hn.trans hend) h
  have hA : SegW W K p lbl ms (At exe endPc R F (aNH lab c0 t sl me cA fr .n20))
      (fun s c => ∃ x : Unit, At exe endPc R F ((fun _ => wcNIH lab c0 t sl me cA fr) x) s c) := by
    refine fn_segW (N := aNH lab c0 t sl me cA fr) (fun i => ?_) XA.n20
    cases i
    case n20 =>
      exact seg_ndW (by simp [sp4AH]) sp4AH_ok hF hR (by omega) hhi
        (fun s he hn => (by simpa using code b0 s he hn : CodeAt s (lab x24L) sp4AH)) hW.n4
        fun σ c hJ => ⟨c, .refl c, .inl ⟨XA.n20s, sp4AH_edge hJ⟩⟩
    case n20s =>
      refine rtst_ndW (b := .rcx) (k := 56) (r := .rax) (z := 4)
        (fun s he hn => tidSt_eq ▸ code bs s he hn) hW.n4s fun m' σ c _ hD hJ => ?_
      obtain ⟨h0, hcx, hax, h64, hFr, h56⟩ := hJ
      have ha : bAddr σ.regs .rcx 56 = t + 56#64 := by rw [bAddr, hcx]; rfl
      have hv : σ.regs.get64 .rax = 1#64 := hax.trans h56
      obtain ⟨hrt, hmp, hG, hun⟩ := htid
      refine ⟨ha ▸ hrt, ha ▸ hmp, by rw [ha, hv]; exact hG, ha ▸ hun m' hD, c, .refl c,
        .inl ⟨XA.n20p, ?_, rfl, h0, h64, hFr⟩⟩
      show lab x24L + 16 = lab x24L + 12 + Int64.ofNat 4
      rw [Int64.add_assoc]; rfl
    case n20p =>
      exact seg_ndW (by simp [initCallH]) initCallH_ok hF hR hlo hhi (fun s he hn => code bp s he hn) hW.n5
        fun σ c hJ => ⟨c, .refl c, .inr ⟨(), initCallH_edge hp hJ⟩⟩
  exact hA.mono_post fun _ _ ⟨_, h⟩ => h

omit [Kraken.Executable.ValidLayout exe] in
/-- **The call of `scc_rt_thread_init` to `.x25`** (`wcN6H` at the stack top `kOf lab`): from the call node
(`wcNIH`, the caller at `F ∧ P`) through the callee (`hti`, promised `P` at its entry, `call_nd_FWP`), `%rbp`
from the callee's postcondition (`At.rbp`), the frame condition `F₂` from `.x25` on. -/
theorem hello_wc_sp4_call_segW {W : Frag isa} {K : State → State → Prop} {M F₂ P : MachineData → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -384) (hhi : 16 ≤ R.hi) (hF₂ : ∀ m, F m → M m → F₂ m)
    {c0 : Ctl} {t : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64}
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-136) (-248) 8).Off (k - -136) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hti : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -248 → 8 ≤ R'.hi →
      FStable R' F' → KStable K F' → (∀ m, F' m → F m) → R' = R.callee (-136) (-248) 8 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -136) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.AllocTcb.G,
        (∃ σC c, (wcNIH (_root_.Executable.labels exe).label c0 t sl me cA fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-136) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oCH mC σC ∧
          (wcNIH (_root_.Executable.labels exe).label c0 t sl me cA fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-136) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -136) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW W K p lbl ms
          (fun s c => At exe endPc R' F' (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e) s c ∧ P s.st.1)
          (fun s c => ∃ x, At exe endPc R' F' (tiX (_root_.Executable.labels exe).label (tiQ t c0 g) x) s c ∧
            M s.st.1)) :
    SegW W K p lbl ms (At exe endPc R (fun m => F m ∧ P m) (wcNIH (_root_.Executable.labels exe).label c0 t sl me cA fr))
      (At exe endPc R F₂ (wcN6H (_root_.Executable.labels exe).label c0 t
        (kOf (_root_.Executable.labels exe).label) sl me cA fr)) := by
  let lab := (_root_.Executable.labels exe).label
  refine ((Ret0.seg_oneW (n := n25I lab c0 t sl me cA fr)
    (call_nd_FWP (KC := True) (P := P) (e0 := 0) (lo' := -248) (hi' := 8) (M := M)
      (nC := wcNIRH lab c0 t sl me cA fr)
      (Ne := fun g : Ret0.AllocTcb.G => tiN lab (tiQ t c0 g) .e)
      (Ex := fun g : Ret0.AllocTcb.G => tiX lab (tiQ t c0 g))
      hR hF (by show R.lo ≤ -136 - 0 + -248; omega) (by decide) (by show (-136 : Int) - 0 < R.hi; omega)
      (by show (-136 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-136 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide) (fun _ => hFK) (fun _ => hKR) hF₂
      (fun R' F' hR' hlo' hhi' hF' hK' hFF hR'e hcc g hg hkeep =>
        hti R' F' hR' hlo' hhi' hF' (hK' trivial) hFF hR'e hcc g
          (let ⟨σC, c, h1, h2⟩ := hg; ⟨σC, c, h1.1, h2⟩)
          fun m' hm => let ⟨mC, σC, c, hA, hJ, hE, hk⟩ := hkeep m' hm; ⟨mC, σC, c, hA, hJ.1, hE, hk⟩)
      (fun _ => rfl) ?_ ?_)).mono_pre fun _ _ h => Ret0.At.rbp_get rfl h).mono_post
    fun _ _ h => Ret0.At.imp (At.rbp h fun _ _ h => h.2) fun _ _ h => h.1
  · rintro σC c ⟨⟨h0, hdi, -, -⟩, -⟩
    exact ⟨⟨σC.regs.rsp.toBitVec, σC.regs.rbp.toBitVec, σC.slot (-136 - 0 + 0)⟩, rfl, h0, rfl, rfl, rfl, hdi⟩
  · rintro g ⟨⟩ σC c σx c' σR ⟨⟨-, -, h136, h64, h8, h16, h24, h32, h40, h48, hf1, hf2⟩, hb⟩
      ⟨-, hsp, hfp, hra, -⟩ ⟨hc', hsp', hfp', hrax⟩ hreg - - hsl
    have hkeep : ∀ k : Int, -128 ≤ k → k + 8 ≤ 16 → k % 8 = 0 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
      hsl k ⟨h3, by omega, by omega⟩ fun h => by simp only [Region.Off, Region.callee, wcNIRH, oCH] at h; omega
    refine .inl ⟨(), ?_, by show SO.le ⟨-128, []⟩ ⟨-136 - 0 + 8, []⟩ = true; decide,
      ⟨hc', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · show lab x25L = Int64.ofBitVec g.ra
      rw [← hra]
      show _ = Int64.ofBitVec (σC.slot (-136 - 0 + 0))
      rw [show (-136 : Int) - 0 + 0 = -136 by decide, h136, int64_ofBitVec_toBitVec]
    · rw [hreg]; exact hrax
    · rw [hkeep (-64) (by omega) (by omega) (by omega), h64]
    · rw [hkeep (-8) (by omega) (by omega) (by omega), h8]
    · rw [hkeep (-16) (by omega) (by omega) (by omega), h16]
    · rw [hkeep (-24) (by omega) (by omega) (by omega), h24]
    · rw [hkeep (-32) (by omega) (by omega) (by omega), h32]
    · rw [hkeep (-40) (by omega) (by omega) (by omega), h40]
    · rw [hkeep (-48) (by omega) (by omega) (by omega), h48]
    · rw [hkeep 0 (by omega) (by omega) (by omega), hf1]
    · rw [hkeep 8 (by omega) (by omega) (by omega), hf2]
    · show σR.regs.get64 .rbp = σR.regs.get64 .rsp + BitVec.ofInt 64 (0 - -128)
      rw [hreg]
      simp only [Reg64s.get64] at hb ⊢
      rw [hfp', hsp', ← hfp, ← hsp]
      show σC.regs.rbp.toBitVec = σC.regs.rsp.toBitVec + 8#64 + BitVec.ofInt 64 (0 - -128)
      rw [hb]; bv_omega

end Seg4

/-- info: 'Spike.Lib.X64.Flow.HelloWc.hello_wcSp3InH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hello_wcSp3InH

/-- info: 'Spike.Lib.X64.Flow.HelloWc.hello_allocTcbIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hello_allocTcbIn

/-- info: 'Spike.Lib.X64.Flow.HelloWc.tcb2QH_tcbOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms tcb2QH_tcbOf

/-- info: 'Spike.Lib.X64.Flow.HelloWc.hello_wc_sp3_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello_wc_sp3_segW

/--
info: 'Spike.Lib.X64.Flow.HelloWc.hello_wc_sp4_pre_segW' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms hello_wc_sp4_pre_segW

/--
info: 'Spike.Lib.X64.Flow.HelloWc.hello_wc_sp4_call_segW' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms hello_wc_sp4_call_segW

end Spike.Lib.X64.Flow.HelloWc
