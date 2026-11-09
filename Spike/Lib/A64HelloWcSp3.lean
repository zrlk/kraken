/-
**hello.w's `wc_main` from `.sp3` to `.sp6`** (AArch64), inside `W`, in any valid layout of
`helloProg`, in `wc_main`'s 144-byte frame (`oWH`): the twin of wake's `A64WakeTcb2Call`, `A64WakeWcSp3Seg`,
`A64WakeWcSp4` (`.sp4` part) and `A64WakeWcSp4Seg` (up to the call's return) at hello's listing:

    .L22_wc_main.sp3:                   -- x0 = the reserve's id 1
      str x0, [sp, #48]
      movz x0, #4099
      movk x0, #192, lsl #16            -- x0 = hdrH = 12587011 (n = 16, m = 3)
      movz x1, #1
      bl scc_rt_alloc_tcb               -- (tcb2CallH), x30 = .sp4; the callee (allocTcbG_segWA, its frame of 192)
    .L22_wc_main.sp4:                   -- x0 = the TCB t = pinA + 144
      str x0, [sp, #56]; ldr x9, [sp, #48]; ldr x10, [sp, #56]  (sp4AH)
      str x9, [x10, #56]                -- row: the TCB's tid word (rtst_ndW)
      ldr x0, [sp, #56]; bl scc_rt_thread_init                  (initCallH), the callee `hti` (its frame of 256)
    .L22_wc_main.sp6:                   -- `wcN6H` (A64HelloWcSp6) at the stack top `kOf lab`

The frame's words `FrWH sl me cA fr` (the five spills, the cell at `[sp, #40]`, the caller's `x29`, `x30`) survive
both calls (outside the callees' regions). The call's ghost record is `tcb2QH g c0 := ⟨g, hdrH, 112, c0⟩`: the
counter's old value `112` is `scc_rt_start`'s first TCB (header `3331`, as in wake), so the TCB is `pinA + 144`
(`tcb2QH_tcbOf`). `scc_rt_thread_init` at the second take returns wake's `kOf lab` (`k0 = 16384`).

- `tcb2CallH`, `sp4AH`, `initCallH` (`block_spec`); `wcSp3InH`, `hello_wcSp3InH`, `hello_allocTcbIn`: the blocks,
  the row and the labels' gaps in `helloProg`.
- `hdrH`, `mOf_hdrH`, `tcb2QH`, `tcb2QH_hdrA`, `tcb2QH_tcbOf`, `tH`: the header, the ghost record, the TCB.
- `j3H`, `wcN3H`, `wcNCH`, `j3H_self`: `.sp3`'s node (`x0 = 1`, the frame's words), the call node; any state with
  `x0 = 1` (e.g. `rXH`'s) is at `j3H` of its own slots.
- `aNH`, `wcNIH`: `.sp4`'s nodes (`.n4`, `.n4s`, `.n5`) and the call node of `scc_rt_thread_init`; `sp4AH_edge`,
  `initCallH_edge`: the blocks' edges.
- `TcbCtxH`, `WcSp3WH`, `hello_wc_sp3_segW`: `.sp3` to `.sp4` (`aNH .n4` at `tH`).
- `WcSp4WH`, `hello_wc_sp4_pre_segW`, `hello_wc_sp4_call_segW`, `hello_wc_sp4_segW`: `.sp4` to `.sp6` (`wcN6H`).
- `hello_wc_sp3_sp6_segW`: the two composed.
-/
import Spike.Lib.A64HelloWcSp0
import Spike.Lib.A64HelloWcSp6
import Spike.Lib.A64WakeWcSp3Seg

namespace Spike.Lib.A64.Flow.HelloWc

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (CallerCells TiG tiN tiX)
open Spike.Lib.A64.Flow.Ret0.AllocTcb (mOf)
open Spike.Lib.A64.HelloPh.WcSp6 (oWH FrWH wcN6H EdgeH)
open Spike.Lib.A64.WakePh.WcSp4 (tidSt)
open Spike.Lib.A64.Flow.WakeWc (tcbWG_mono tidSt_eq kOf tiQ XA)
open Spike.Lib.A64.Rt (TcbGG TcbWG TcbOkGA tcbNG tcbXG hdrA tcbOf allocTcbG_segWA)
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)

set_option linter.unusedSimpArgs false

/-! ## The blocks, the row and the checks -/

/-- **The second call's block** at `.sp3`. -/
def tcb2CallH : List Directive := parseAArch64("str x0, [sp, #48]
movz x0, #4099
movk x0, #192, lsl #16
movz x1, #1
bl scc_rt_alloc_tcb")

/-- `.sp4`'s first block: the TCB to `[sp, #56]`, the reserve's id and the TCB. -/
def sp4AH : List Directive := parseAArch64("str x0, [sp, #56]
ldr x9, [sp, #48]
ldr x10, [sp, #56]")

/-- The call of `scc_rt_thread_init` on the TCB. -/
def initCallH : List Directive := parseAArch64("ldr x0, [sp, #56]
bl scc_rt_thread_init")

block_spec tcb2CallH (-144) 0 oWH tcb2CallH
block_spec sp4AH (-144) 0 oWH sp4AH
block_spec initCallH (-144) 0 oWH initCallH

/-- **The blocks and the row in `prog`**: the call block at `.sp3`, `.sp4` right after; at `.sp4` the blocks and
the tid store (`0`, `3`, `4`), `.sp6` six instructions after `.sp4`. -/
def wcSp3InH (prog : List Directive) : Bool :=
  blockAt prog ".L22_wc_main.sp3" 0 tcb2CallH && labelGap prog ".L22_wc_main.sp3" ".L22_wc_main.sp4" 5 &&
    blockAt prog ".L22_wc_main.sp4" 0 sp4AH && blockAt prog ".L22_wc_main.sp4" 3 tidSt &&
    blockAt prog ".L22_wc_main.sp4" 4 initCallH && labelGap prog ".L22_wc_main.sp4" ".L22_wc_main.sp6" 6

theorem hello_wcSp3InH : wcSp3InH SccCode.helloProg = true := by decide +kernel

theorem hello_allocTcbIn : Ret0.AllocTcb.allocTcbIn SccCode.helloProg = true := by decide +kernel

/-! ## The header, the ghost record, the TCB -/

/-- **The second TCB's header** (`n = 12`, `m = 3`). -/
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

/-- **`.sp3`'s invariant**: the reserve's id `1` in `x0`, the frame's words. -/
def j3H (σ : AS) : Prop := σ.regs.X0.toBitVec = 1#64 ∧ FrWH sl me cA fr σ

/-- **At `.sp3`**: the source at `c0`, `j3H`. -/
def wcN3H : ND := ⟨lab ".L22_wc_main.sp3", oWH, fun σ c => c = c0 ∧ j3H sl me cA fr σ⟩

/-- **The call node**: at `scc_rt_alloc_tcb`, its arguments `hdrH` and `1`, the return address `.sp4`; the frame's
words and the id at `[sp, #48]`. -/
def wcNCH : ND := ⟨lab Ret0.AllocTcb.fnL, oWH, fun σ c => c = c0 ∧
  σ.regs.X0.toBitVec = hdrH ∧ σ.regs.X1.toBitVec = 1#64 ∧
  σ.regs.X30.toBitVec = (lab ".L22_wc_main.sp4").toBitVec ∧ FrWH sl me cA fr σ ∧ σ.slot (-96) = 1#64⟩

/-- **`.sp4`'s nodes before the call**: `.sp4` (`x0` the TCB `t`), the tid store (`x9` the id `[sp, #48]`, `x10`
and `[sp, #56]` the TCB), past it; the id `1` at `[sp, #48]` up to the tid store. -/
def aNH : XA → ND
  | .n4 => ⟨lab ".L22_wc_main.sp4", oWH, fun σ c => c = c0 ∧ σ.regs.X0.toBitVec = t ∧ FrWH sl me cA fr σ ∧
      σ.slot (-96) = 1#64⟩
  | .n4s => ⟨lab ".L22_wc_main.sp4" + Int64.ofNat (4 * 3), oWH, fun σ c => c = c0 ∧
      σ.regs.X9.toBitVec = σ.slot (-96) ∧ σ.regs.X10.toBitVec = t ∧ σ.slot (-88) = t ∧ FrWH sl me cA fr σ ∧
      σ.slot (-96) = 1#64⟩
  | .n5 => ⟨lab ".L22_wc_main.sp4" + Int64.ofNat (4 * 4), oWH, fun σ c => c = c0 ∧ σ.slot (-88) = t ∧
      FrWH sl me cA fr σ⟩

/-- **The call node of `scc_rt_thread_init`**: `x0` the TCB, the return address `.sp6`. -/
def wcNIH : ND := ⟨lab Ret0.ThreadInit.fnL, oWH, fun σ c => c = c0 ∧ σ.regs.X0.toBitVec = t ∧
  σ.regs.X30.toBitVec = (lab ".L22_wc_main.sp6").toBitVec ∧ σ.slot (-88) = t ∧ FrWH sl me cA fr σ⟩

end Nodes

/-- **Any state with `x0 = 1`** (`rXH`'s at `.sp3`) is at `j3H` of its own frame's words. -/
theorem j3H_self {σ : AS} (h : σ.regs.X0.toBitVec = 1#64) :
    j3H (σ.slot (-144), σ.slot (-136), σ.slot (-128), σ.slot (-120)) (σ.slot (-112)) (σ.slot (-104))
      (σ.slot (-16), σ.slot (-8)) σ :=
  ⟨h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The runs and the edges -/

section Run

variable (lab : Label → Int64) (pc : Int64) (σ : AS)

/-- The call block's `x0` is the header `hdrH`. -/
theorem tcb2CallH_x0 : (arun lab tcb2CallH ⟨pc, oWH, σ⟩).σ.regs.X0.toBitVec = hdrH := by
  rw [tcb2CallH_run]; rfl

/-- The call block's `x1` is `1`. -/
theorem tcb2CallH_x1 : (arun lab tcb2CallH ⟨pc, oWH, σ⟩).σ.regs.X1.toBitVec = 1#64 := by
  rw [tcb2CallH_run]; rfl

/-- The call block ends at the callee's label, the offsets unchanged. -/
theorem tcb2CallH_pc : (arun lab tcb2CallH ⟨pc, oWH, σ⟩).pc = lab "scc_rt_alloc_tcb" ∧
    (arun lab tcb2CallH ⟨pc, oWH, σ⟩).so = oWH := by
  rw [tcb2CallH_run]; exact ⟨rfl, rfl⟩

/-- The call block keeps the frame's slots but `-96` (`[sp, #48]`), which gets `x0`. -/
theorem tcb2CallH_slot : (arun lab tcb2CallH ⟨pc, oWH, σ⟩).σ.slot = Spike.Lib.upd σ.slot (-96) σ.regs.X0.toBitVec := by
  rw [tcb2CallH_run]

end Run

/-- **The call block's return address is `.sp4`** in any layout of `helloProg`, from `.sp3`. -/
theorem tcb2CallH_x30 {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
    (hp : Lays exe SccCode.helloProg kp) (σ : AS) :
    (arun (_root_.Executable.labels exe).label tcb2CallH
        ⟨(_root_.Executable.labels exe).label ".L22_wc_main.sp3", oWH, σ⟩).σ.regs.X30.toBitVec =
      ((_root_.Executable.labels exe).label ".L22_wc_main.sp4").toBitVec := by
  have hin := hello_wcSp3InH
  simp only [wcSp3InH, Bool.and_eq_true] at hin
  rw [label_labelGap hp hin.1.1.1.1.2, tcb2CallH_run]
  simp only [Spike.Lib.A64.Flow.Ret0.ofInt_bmod]
  rw [show Int64.ofNat (4 * 5) = 20 from rfl, Int64.toBitVec_add,
    show ∀ y : Int, y + 4 + 4 + 4 + 4 + 4 = y + 20 from fun y => by omega, BitVec.ofInt_add,
    Spike.Lib.int64_ofInt_toInt]; rfl

section Edges

variable {lab : Label → Int64} {c0 : Ctl} {t : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
  {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64} {σ : AS} {c : Ctl}

/-- A block's edge in hello's frame is a hit at the target node. -/
theorem hit_of_edgeH {blk : List Directive} {n n' : ND} (h : EdgeH lab blk n n' σ c) (ho : n'.o = oWH) :
    Hit n' (arun lab blk ⟨n.pc, oWH, σ⟩) c :=
  ⟨h.1.symm, by rw [h.2.1, ho]; rfl, h.2.2⟩

/-- `sp4AH` from `.sp4` to the tid store. -/
theorem sp4AH_edge (hJ : (aNH lab c0 t sl me cA fr .n4).J σ c) :
    EdgeH lab sp4AH (aNH lab c0 t sl me cA fr .n4) (aNH lab c0 t sl me cA fr .n4s) σ c := by
  obtain ⟨h0, hx, ⟨h144, h136, h128, h120, h112, h104, h16, h8⟩, h96⟩ := hJ
  refine ⟨?_, ?_, ?_⟩
  · simp only [aNH, sp4AH_run]
    rw [show Int64.ofNat (4 * 3) = 4 + 4 + 4 from rfl]; simp only [Int64.add_assoc]
  · simp only [aNH, sp4AH_run]
  · simp only [aNH, sp4AH_run, FrWH, Spike.Lib.upd]
    simp_all

/-- `initCallH` from past the tid store to `scc_rt_thread_init`, in any layout of `helloProg`. -/
theorem initCallH_edge {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
    (hp : Lays exe SccCode.helloProg kp) (hJ : (aNH (_root_.Executable.labels exe).label c0 t sl me cA fr .n5).J σ c) :
    EdgeH (_root_.Executable.labels exe).label initCallH (aNH (_root_.Executable.labels exe).label c0 t sl me cA fr .n5)
      (wcNIH (_root_.Executable.labels exe).label c0 t sl me cA fr) σ c := by
  obtain ⟨h0, h88, hF⟩ := hJ
  have hin := hello_wcSp3InH
  simp only [wcSp3InH, Bool.and_eq_true] at hin
  refine ⟨by simp only [initCallH_run]; rfl, by simp only [initCallH_run]; rfl, h0,
    by simp only [initCallH_run, aNH]; exact h88, ?_, by simp only [initCallH_run]; exact h88,
    by simp only [initCallH_run]; exact hF⟩
  simp only [aNH, initCallH_run, Spike.Lib.A64.Flow.Ret0.ofInt_bmod]
  rw [label_labelGap hp hin.2, show Int64.ofNat (4 * 4) = 16 from rfl, show Int64.ofNat (4 * 6) = 24 from rfl,
    Int64.toBitVec_add, show ∀ y : Int, y + 4 + 4 = y + 8 from fun y => by omega, BitVec.ofInt_add,
    Spike.Lib.int64_ofInt_toInt, Int64.toBitVec_add, BitVec.add_assoc]
  rfl

end Edges

/-! ## `.sp3` to `.sp4` -/

/-- **The second TCB call's context in `wc_main`'s region `R`** at the memory `mm`, for the ghost `g`: a caller's
state at the call node `Jc`, the callee's entry, the caller's cells kept. -/
def TcbCtxH (lab : Label → Int64) (R : Region) (Jc : AS → Ctl → Prop) (c0 : Ctl) (g : Ret0.AllocTcb.G)
    (mm : MachineData) : Prop :=
  ∃ mC σC c, Abs R oWH mC σC ∧ Jc σC c ∧ (tcbNG lab (tcb2QH g c0) .e).J (enter (-144) σC) c ∧
    CKept R (-144) (-192) 0 mC mm

/-- **`.sp3`'s states to `.sp4` inside `W`**: the call block's and the callee's (in its region, for any return to
`.sp4`). -/
structure WcSp3WH (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (c0 : Ctl) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)
    (me cA : BitVec 64) (fr : BitVec 64 × BitVec 64) : Prop where
  blk : BlkW W K exe endPc R F (wcN3H (_root_.Executable.labels exe).label c0 sl me cA fr) tcb2CallH
  tcb : ∀ g : Ret0.AllocTcb.G, g.ra = ((_root_.Executable.labels exe).label ".L22_wc_main.sp4").toBitVec →
    ∀ i, TcbWG W K exe endPc (R.callee (-144) (-192) 0)
      (fun mm => F mm ∧ CallerCells R (-144) (-192) 0 mm ∧
        TcbCtxH (_root_.Executable.labels exe).label R (wcNCH (_root_.Executable.labels exe).label c0 sl me cA fr).J
          c0 g mm)
      (tcb2QH g c0) i

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` from `.sp3` to `.sp4` is one segment inside `W`** in any valid layout of `helloProg`: from `.sp3`
(the reserve's id `1` in `x0`, the frame's words, the source at `c0`) to `aNH .n4` at the second TCB `tH`.
`scc_rt_alloc_tcb` at `tcb2QH g c0` writes the header word (`hhdr`) and adds to the counter (`htcb`), moving only
memory `K` keeps off the caller's cells (`hFK`, `hKR`). Its states lie in `W` (`hW`). -/
theorem hello_wc_sp3_segW {W : Frag isaLSE2} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -336) (hhi : 0 ≤ R.hi)
    {c0 : Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (hW : WcSp3WH W K exe endPc R F c0 sl me cA fr)
    (hhdr : ∀ g, Ret0.StOk ms F exe endPc (hdrA (_root_.Executable.labels exe).label (tcb2QH g c0))
      ((tcb2QH g c0).h ||| 1#64 <<< 36))
    (htcb : ∀ g, TcbOkGA ms F exe endPc (R.callee (-144) (-192) 0) F (tcb2QH g c0))
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-144) (-192) 0).Off (k - -144) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8) :
    SegW W K p lbl ms (At exe endPc R F (wcN3H (_root_.Executable.labels exe).label c0 sl me cA fr))
      (At exe endPc R F (aNH (_root_.Executable.labels exe).label c0 (tH (_root_.Executable.labels exe).label)
        sl me cA fr .n4)) := by
  let lab := (_root_.Executable.labels exe).label
  have hin := hello_wcSp3InH
  simp only [wcSp3InH, Bool.and_eq_true] at hin
  -- the call block
  have hA : SegW W K p lbl ms (At exe endPc R F (wcN3H lab c0 sl me cA fr))
      (At exe endPc R F (wcNCH lab c0 sl me cA fr)) := by
    refine Ret0.seg_oneW (seg_ndW (by simp [tcb2CallH]) tcb2CallH_ok hF hR hal (by omega) hhi
      (code_of hp hend hin.1.1.1.1.1 (ofNat4_zero _)) hW.blk fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_⟩⟩)
    obtain ⟨hc, hx0, h144, h136, h128, h120, h112, h104, h16, h8⟩ := hJ
    have hsl := tcb2CallH_slot lab (lab ".L22_wc_main.sp3") σ
    refine ⟨(tcb2CallH_pc lab _ σ).1.symm, ?_, hc, tcb2CallH_x0 lab _ σ, tcb2CallH_x1 lab _ σ,
      tcb2CallH_x30 hp σ, ?_⟩
    · show SO.le oWH (arun lab tcb2CallH ⟨lab ".L22_wc_main.sp3", oWH, σ⟩).so = true
      rw [(tcb2CallH_pc lab (lab ".L22_wc_main.sp3") σ).2]; rfl
    · show FrWH sl me cA fr (arun lab tcb2CallH ⟨lab ".L22_wc_main.sp3", oWH, σ⟩).σ ∧
        (arun lab tcb2CallH ⟨lab ".L22_wc_main.sp3", oWH, σ⟩).σ.slot (-96) = 1#64
      simp only [FrWH]; rw [hsl]; simp [Spike.Lib.upd, h144, h136, h128, h120, h112, h104, h16, h8, hx0]
  -- the call
  have hC : SegW W K p lbl ms (At exe endPc R F (wcNCH lab c0 sl me cA fr))
      (At exe endPc R F (aNH lab c0 (tH lab) sl me cA fr .n4)) := by
    refine Ret0.seg_oneW (call_nd_FWK (KC := True) (lo' := -192) (hi' := 0) (M := fun _ => True)
      (nC := wcNCH lab c0 sl me cA fr) (N := fun _ : Unit => aNH lab c0 (tH lab) sl me cA fr .n4)
      (E := fun e : Empty => e.elim)
      (Ne := fun g : Ret0.AllocTcb.G => tcbNG lab (tcb2QH g c0) .e)
      (Ex := fun g : Ret0.AllocTcb.G => tcbXG lab (tcb2QH g c0))
      hR hal hF (by show R.lo ≤ -144 + -192; omega) (by decide) (by show (-144 : Int) < R.hi; omega) (by decide)
      (by show (-144 : Int) % 16 = 0; decide) (by decide) (by decide) (fun _ => hFK) (fun _ => hKR)
      (fun _ h _ => h)
      (fun R' F' hR' hal' hlo' hhi' hF' _ hFF hR'e hcc g hg hkeep => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, -, -, h30, -⟩, ⟨-, -, -, h30', -, -⟩⟩ := hg
        exact (allocTcbG_segWA hp hend hello_allocTcbIn hF' hR' hal' hlo' hhi' hFF (tcb2QH g c0)
          (by show (112#64).toNat + (Ret0.AllocTcb.lenOf hdrH).toNat ≤ 131072; decide)
          (hhdr g) ((htcb g).mono hFF)
          fun i => tcbWG_mono (hW.tcb g (h30'.symm.trans h30) i) fun m h => ⟨hFF m h, hcc m h, hkeep m h⟩).mono_post
          fun _ _ ⟨x, h⟩ => ⟨x, h, trivial⟩)
      (fun _ => rfl) ?_ ?_)
    · rintro σC c ⟨rfl, h0, h1, -⟩
      exact ⟨⟨σC.regs.SP.toBitVec, σC.regs.X29.toBitVec, σC.regs.X30.toBitVec⟩, rfl,
        rfl, rfl, rfl, rfl, h0, h1⟩
    · rintro g ⟨⟩ σC c σx c' σR ⟨-, -, -, h30, ⟨h144, h136, h128, h120, h112, h104, h16, h8⟩, h96⟩
        ⟨-, -, -, h30', -, -⟩ ⟨hc', hpost⟩ hreg - hsl
      have hkeep : ∀ k : Int, -144 ≤ k → k < 0 → k % 8 = 0 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
        hsl k ⟨h3, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, wcNCH]; omega)
      refine .inl ⟨(), ?_, rfl, hc', ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · show lab ".L22_wc_main.sp4" = Int64.ofBitVec (tcb2QH g c0).g.ra
        rw [← h30']
        show _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [h30, int64_ofBitVec_toBitVec]
      · show σR.regs.X0.toBitVec = tH lab
        rw [hreg, Spike.Lib.A64.Rt.postG_tcbOf lab (tcb2QH g c0) hpost, tcb2QH_tcbOf]
      · rw [hkeep (-144) (by omega) (by omega) (by omega), h144]
      · rw [hkeep (-136) (by omega) (by omega) (by omega), h136]
      · rw [hkeep (-128) (by omega) (by omega) (by omega), h128]
      · rw [hkeep (-120) (by omega) (by omega) (by omega), h120]
      · rw [hkeep (-112) (by omega) (by omega) (by omega), h112]
      · rw [hkeep (-104) (by omega) (by omega) (by omega), h104]
      · rw [hkeep (-16) (by omega) (by omega) (by omega), h16]
      · rw [hkeep (-8) (by omega) (by omega) (by omega), h8]
      · rw [hkeep (-96) (by omega) (by omega) (by omega), h96]
  exact hA.seq hC

end Seg

/-! ## `.sp4` to `.sp6` -/

/-- **`.sp4`'s states to the call of `scc_rt_thread_init` inside `W`**, none moved by `K`: the blocks' and the
row's. -/
structure WcSp4WH (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (c0 : Ctl) (t : BitVec 64)
    (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (me cA : BitVec 64) (fr : BitVec 64 × BitVec 64) :
    Prop where
  n4 : BlkW W K exe endPc R F (aNH (_root_.Executable.labels exe).label c0 t sl me cA fr .n4) sp4AH
  n4s : NodeW W K exe endPc R F (aNH (_root_.Executable.labels exe).label c0 t sl me cA fr .n4s)
  n5 : BlkW W K exe endPc R F (aNH (_root_.Executable.labels exe).label c0 t sl me cA fr .n5) initCallH

/-- From `.sp4` to the call inside the trivial predicate, with no outside moves. -/
theorem WcSp4WH.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {c0 : Ctl} {t : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} :
    WcSp4WH (fun _ _ => True) (fun _ _ => False) exe endPc R F c0 t sl me cA fr :=
  ⟨BlkW.triv, fun _ _ _ => ⟨trivial, fun _ h => h⟩, BlkW.triv⟩

section Seg4

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` from `.sp4` to the call of `scc_rt_thread_init`** (`wcNIH`): the TCB to `[sp, #56]`, the id `1`
to the TCB's tid word `t + 56` (a runtime word the store may write: `htid`). -/
theorem hello_wc_sp4_pre_segW {W : Frag isaLSE2} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    {c0 : Ctl} {t : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64}
    (hW : WcSp4WH W K exe endPc R F c0 t sl me cA fr)
    (htid : ms.rt (t + 56#64).toNat ∧ ms.mp ⟨t + 56#64, 8⟩ true ∧ ms.G ⟨t + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none) :
    SegW W K p lbl ms (At exe endPc R F (aNH (_root_.Executable.labels exe).label c0 t sl me cA fr .n4))
      (At exe endPc R F (wcNIH (_root_.Executable.labels exe).label c0 t sl me cA fr)) := by
  have hin := hello_wcSp3InH
  simp only [wcSp3InH, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨-, -⟩, b4⟩, b4s⟩, b5⟩, -⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have hA : SegW W K p lbl ms (At exe endPc R F (aNH lab c0 t sl me cA fr .n4))
      (fun s c => ∃ x : Unit, At exe endPc R F ((fun _ => wcNIH lab c0 t sl me cA fr) x) s c) := by
    refine fn_segW (N := aNH lab c0 t sl me cA fr) (fun i => ?_) XA.n4
    cases i
    case n4 =>
      refine seg_ndW (by simp [sp4AH]) sp4AH_ok hF hR hal (by omega) hhi (code_of hp hend b4 (ofNat4_zero _)) hW.n4
        fun σ c hJ => ⟨c, .refl c, .inl ⟨XA.n4s, hit_of_edgeH (sp4AH_edge hJ) rfl⟩⟩
    case n4s =>
      refine rtst_ndW (t := .X9) (b := .X10) (i := 56) (code_of hp hend (tidSt_eq ▸ b4s) rfl) hW.n4s
        fun m' σ c _ hD hJ => ?_
      obtain ⟨h0, h9, h10, h88, hFr, h96⟩ := hJ
      have ha : rAddr σ.regs .X10 56 = t + 56#64 := by rw [Ret0.rAddr_x10 h10]; rfl
      have hv : σ.regs.getRegOrZr (.low (.reg .X9) .W64) = 1#64 := by rw [Ret0.getRegOrZr_x9, h9, h96]
      obtain ⟨hrt, hmp, hG, hun⟩ := htid
      refine ⟨ha ▸ hrt, ha ▸ hmp, by rw [ha, hv]; exact hG, ha ▸ hun m' hD, c, .refl c,
        .inl ⟨XA.n5, ?_, rfl, h0, h88, hFr⟩⟩
      show lab ".L22_wc_main.sp4" + Int64.ofNat (4 * 4) = lab ".L22_wc_main.sp4" + Int64.ofNat (4 * 3) + Int64.ofNat 4
      rw [Int64.add_assoc]; rfl
    case n5 =>
      refine seg_ndW (by simp [initCallH]) initCallH_ok hF hR hal (by omega) hhi (code_of hp hend b5 rfl) hW.n5
        fun σ c hJ => ⟨c, .refl c, .inr ⟨(), hit_of_edgeH (initCallH_edge hp hJ) rfl⟩⟩
  exact hA.mono_post fun _ _ ⟨_, h⟩ => h

omit [Kraken.Executable.ValidLayout exe] in
/-- **The call of `scc_rt_thread_init` to `.sp6`** (`wcN6H` at the stack top `kOf lab`): the callee promised `P`
of the memory at its entry (`call_nd_FWP`; the caller at `F ∧ P`), returning with `M` (the frame condition from
`.sp6` on is `F₂`). -/
theorem hello_wc_sp4_call_segW {W : Frag isaLSE2} {K : State → State → Prop} {M F₂ P : MachineData → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -400) (hhi : 0 ≤ R.hi)
    (hF₂ : ∀ m, F m → M m → F₂ m)
    {c0 : Ctl} {t : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64}
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-144) (-256) 0).Off (k - -144) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hti : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -256 →
      0 ≤ R'.hi → FStable R' F' → KStable K F' → (∀ m, F' m → F m) → R' = R.callee (-144) (-256) 0 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -144) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.ThreadInit.G,
        (∃ σC c, (wcNIH (_root_.Executable.labels exe).label c0 t sl me cA fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-144) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oWH mC σC ∧
          (wcNIH (_root_.Executable.labels exe).label c0 t sl me cA fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-144) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -144) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW W K p lbl ms
          (fun s c => At exe endPc R' F' (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e) s c ∧ P s.st.1)
          (fun s c => ∃ x, At exe endPc R' F' (tiX (_root_.Executable.labels exe).label (tiQ t c0 g) x) s c ∧
            M s.st.1)) :
    SegW W K p lbl ms
      (At exe endPc R (fun m => F m ∧ P m) (wcNIH (_root_.Executable.labels exe).label c0 t sl me cA fr))
      (At exe endPc R F₂
        (wcN6H (_root_.Executable.labels exe).label c0 t (kOf (_root_.Executable.labels exe).label) sl me cA fr)) := by
  let lab := (_root_.Executable.labels exe).label
  refine (call_nd_FWP (KC := True) (P := P) (lo' := -256) (hi' := 0) (M := M) (nC := wcNIH lab c0 t sl me cA fr)
    (N := fun x : Empty => x.elim)
    (E := fun _ : Unit => wcN6H lab c0 t (kOf lab) sl me cA fr)
    (Ne := fun g : Ret0.ThreadInit.G => tiN lab (tiQ t c0 g) .e)
    (Ex := fun g : Ret0.ThreadInit.G => tiX lab (tiQ t c0 g))
    hR hal hF (by show R.lo ≤ -144 + -256; omega) (by decide) (by show (-144 : Int) < R.hi; omega) (by decide)
    (by show (-144 : Int) % 16 = 0; decide) (by decide) (by decide) (fun _ => hFK) (fun _ => hKR) hF₂
    (fun R' F' hR' hal' hlo' hhi' hF' hK' hFF hR'e hcc g hg hkeep =>
      hti R' F' hR' hal' hlo' hhi' hF' (hK' trivial) hFF hR'e hcc g hg hkeep)
    (fun _ => rfl) ?_ ?_).mono_post fun _ _ h => ?_
  · rintro σC c ⟨h0, hx0, -, -, -⟩
    exact ⟨⟨σC.regs.SP.toBitVec, σC.regs.X29.toBitVec, σC.regs.X30.toBitVec⟩, rfl, h0, rfl, rfl, rfl, hx0⟩
  · rintro g ⟨⟩ σC c σx c' σR ⟨h0, -, h30, h88, h144, h136, h128, h120, h112, h104, h16, h8⟩ ⟨hc, -, -, h30', -⟩
      ⟨hc', hpost⟩ hreg - hsl
    have hkeep : ∀ k : Int, -144 ≤ k → k < 0 → k % 8 = 0 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
      hsl k ⟨h3, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, wcNIH]; omega)
    refine .inr ⟨(), ?_, rfl, hc'.trans hc.symm |>.trans h0, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · show lab ".L22_wc_main.sp6" = Int64.ofBitVec g.ra
      rw [← h30']
      show _ = Int64.ofBitVec σC.regs.X30.toBitVec
      rw [h30, int64_ofBitVec_toBitVec]
    · rw [hreg, hpost.2.2.2]
    · rw [hkeep (-88) (by omega) (by omega) (by omega), h88]
    · rw [hkeep (-144) (by omega) (by omega) (by omega), h144]
    · rw [hkeep (-136) (by omega) (by omega) (by omega), h136]
    · rw [hkeep (-128) (by omega) (by omega) (by omega), h128]
    · rw [hkeep (-120) (by omega) (by omega) (by omega), h120]
    · rw [hkeep (-112) (by omega) (by omega) (by omega), h112]
    · rw [hkeep (-104) (by omega) (by omega) (by omega), h104]
    · rw [hkeep (-16) (by omega) (by omega) (by omega), h16]
    · rw [hkeep (-8) (by omega) (by omega) (by omega), h8]
  · rcases h with ⟨j, _⟩ | ⟨_, h⟩
    · exact j.elim
    · exact h

/-- **`wc_main` from `.sp4` to `.sp6` is one segment inside `W`** in any valid layout of `helloProg`: from `.sp4`
(the second TCB `t` in `x0`, the reserve's id `1` at `[sp, #48]`, the frame's words, the source at `c0`) to
`wcN6H` (`x0` the child's stack top `kOf lab`, `t` at `[sp, #56]`). The tid word `t + 56` is a runtime word the
store of `1` may write (`htid`); `scc_rt_thread_init` on `t` at the second take is the callee premise `hti`
(`call_nd_FWK`'s, its frame of 256, moving only memory `K` keeps off the caller's cells: `hFK`, `hKR`), returning
`kOf lab` with `M` (the frame condition at `.sp6` is `F₂`, `hF₂`). Its states lie in `W` (`hW`). -/
theorem hello_wc_sp4_segW {W : Frag isaLSE2} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -400) (hhi : 0 ≤ R.hi)
    (hF₂ : ∀ m, F m → M m → F₂ m)
    {c0 : Ctl} {t : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64}
    (hW : WcSp4WH W K exe endPc R F c0 t sl me cA fr)
    (htid : ms.rt (t + 56#64).toNat ∧ ms.mp ⟨t + 56#64, 8⟩ true ∧ ms.G ⟨t + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none)
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-144) (-256) 0).Off (k - -144) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hti : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -256 →
      0 ≤ R'.hi → FStable R' F' → KStable K F' → (∀ m, F' m → F m) → R' = R.callee (-144) (-256) 0 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -144) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.ThreadInit.G,
        (∃ σC c, (wcNIH (_root_.Executable.labels exe).label c0 t sl me cA fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-144) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oWH mC σC ∧
          (wcNIH (_root_.Executable.labels exe).label c0 t sl me cA fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-144) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -144) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW W K p lbl ms (At exe endPc R' F' (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e))
          (fun s c => ∃ x, At exe endPc R' F' (tiX (_root_.Executable.labels exe).label (tiQ t c0 g) x) s c ∧
            M s.st.1)) :
    SegW W K p lbl ms (At exe endPc R F (aNH (_root_.Executable.labels exe).label c0 t sl me cA fr .n4))
      (At exe endPc R F₂
        (wcN6H (_root_.Executable.labels exe).label c0 t (kOf (_root_.Executable.labels exe).label) sl me cA fr)) :=
  (hello_wc_sp4_pre_segW hp hend hF hR hal (by omega) hhi hW htid).seq
    ((hello_wc_sp4_call_segW (P := fun _ => True) hF hR hal hlo hhi hF₂ hFK hKR
      fun R' F' hR' hal' hlo' hhi' hF' hK' hFF hR'e hcc g hg hkeep =>
        (hti R' F' hR' hal' hlo' hhi' hF' hK' hFF hR'e hcc g hg hkeep).mono_pre fun _ _ h => h.1).mono_pre
      fun _ _ ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ⟨he, hn, hdc, hpc, σ, hA, ⟨hD, trivial⟩, hJ⟩)

/-- **`wc_main` from `.sp3` to `.sp6` is one segment inside `W`** in any valid layout of `helloProg`:
`hello_wc_sp3_segW` then `hello_wc_sp4_segW` at the second TCB `tH lab`. -/
theorem hello_wc_sp3_sp6_segW {W : Frag isaLSE2} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -400) (hhi : 0 ≤ R.hi)
    (hF₂ : ∀ m, F m → M m → F₂ m)
    {c0 : Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (hW3 : WcSp3WH W K exe endPc R F c0 sl me cA fr)
    (hW4 : WcSp4WH W K exe endPc R F c0 (tH (_root_.Executable.labels exe).label) sl me cA fr)
    (hhdr : ∀ g, Ret0.StOk ms F exe endPc (hdrA (_root_.Executable.labels exe).label (tcb2QH g c0))
      ((tcb2QH g c0).h ||| 1#64 <<< 36))
    (htcb : ∀ g, TcbOkGA ms F exe endPc (R.callee (-144) (-192) 0) F (tcb2QH g c0))
    (htid : let t := tH (_root_.Executable.labels exe).label
      ms.rt (t + 56#64).toNat ∧ ms.mp ⟨t + 56#64, 8⟩ true ∧ ms.G ⟨t + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none)
    (hFK : KStable K F)
    (hKR3 : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-144) (-192) 0).Off (k - -144) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hKR4 : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-144) (-256) 0).Off (k - -144) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hti : let t := tH (_root_.Executable.labels exe).label
      ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -256 →
      0 ≤ R'.hi → FStable R' F' → KStable K F' → (∀ m, F' m → F m) → R' = R.callee (-144) (-256) 0 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -144) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.ThreadInit.G,
        (∃ σC c, (wcNIH (_root_.Executable.labels exe).label c0 t sl me cA fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-144) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oWH mC σC ∧
          (wcNIH (_root_.Executable.labels exe).label c0 t sl me cA fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-144) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -144) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW W K p lbl ms (At exe endPc R' F' (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e))
          (fun s c => ∃ x, At exe endPc R' F' (tiX (_root_.Executable.labels exe).label (tiQ t c0 g) x) s c ∧
            M s.st.1)) :
    SegW W K p lbl ms (At exe endPc R F (wcN3H (_root_.Executable.labels exe).label c0 sl me cA fr))
      (At exe endPc R F₂ (wcN6H (_root_.Executable.labels exe).label c0 (tH (_root_.Executable.labels exe).label)
        (kOf (_root_.Executable.labels exe).label) sl me cA fr)) :=
  (hello_wc_sp3_segW hp hend hF hR hal (by omega) hhi hW3 hhdr htcb hFK hKR3).seq
    (hello_wc_sp4_segW hp hend hF hR hal hlo hhi hF₂ hW4 htid hFK hKR4 hti)

end Seg4

end Spike.Lib.A64.Flow.HelloWc

/-- info: 'Spike.Lib.A64.Flow.HelloWc.hello_wcSp3InH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.hello_wcSp3InH

/-- info: 'Spike.Lib.A64.Flow.HelloWc.hello_allocTcbIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.hello_allocTcbIn

/-- info: 'Spike.Lib.A64.Flow.HelloWc.tcb2QH_tcbOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.tcb2QH_tcbOf

/-- info: 'Spike.Lib.A64.Flow.HelloWc.hello_wc_sp3_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.hello_wc_sp3_segW

/-- info: 'Spike.Lib.A64.Flow.HelloWc.hello_wc_sp4_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.hello_wc_sp4_segW

/--
info: 'Spike.Lib.A64.Flow.HelloWc.hello_wc_sp3_sp6_segW' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.hello_wc_sp3_sp6_segW
