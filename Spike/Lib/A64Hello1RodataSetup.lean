/-
**`wc_rodata` on AArch64 from its call to its return**: the prologue, the
allocation of the two-cell buffer (or the heap abort when the arena is
full), the two lane stores and the epilogue, with `TPIDR_EL0` kept across
every segment, ending at the caller's return address in the shape of a
setup call's post state.

- `callOK_tp`, `callOK_untp`, `limOk_tp`, `proW_tp`, `allocW_tp`,
  `rdPreW_tp`: the memory side's facts moved to a thread pointer
  (`tpXa`);
- `rdQ`, `rdQ_facts`: `wc_rodata`'s allocation call and what its
  obligations fix;
- `rAddr_x0_0`, `rAddr_x0_8`: the two lane addresses;
- `sJ0`, `sJ1`, `RdF`, `sJp`, `sJp'`, `sJh1`, `sJ2`, `sJ2'`, `sJh2`,
  `sJ4`: the source controls at each node;
- `rdPostS`, `sX`, `sXf`: the return node and its post state (the buffer
  at `x0`, `x1 = 0`, `x2 = 2`, `x3 = 13`, the caller's `fp`, `lr`, `sp` and
  thread pointer);
- `sp0_sJp`: the frame at the allocation's landing;
- `hello1_rodata_setupW`: from the setup entry `uN0 .. "wc_rodata" 48 g`
  to `sXf`, given the region reaches `256` bytes below the entry `sp`
  (the frame, the allocator and the heap abort).
-/
import Spike.Lib.A64Hello1RodataTP
import Spike.Lib.A64AbortHeapW
import Spike.Lib.Hello1RodataSrc
import Spike.Lib.Rt.A64Main

namespace Spike.Lib.A64.Flow

namespace Hello1

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.A64.Flow.Ret0 (CallerCells LimOk WcG limA tcbA_limA)
open Spike.Lib.A64.Alloc (Call AllocW Ea Jfull mOf)
open Spike.Lib.Hello1RodataSrc (rdC0 rdCN rdCA rdC1 rdC2 rdC3 rdC4 rdRet eW0 τ8 rdK1 rdK2 rdC0_run rdCN_newBuf
  rdCA_store rdC2_store rdC1_next rdC3_next rdC4_run)

set_option linter.unusedSimpArgs false

/-! ## The memory side with the allocation's landing at a thread pointer -/

section Tp

variable {ms : MemSide isaLSE2} {t : UInt64}

theorem callOK_tp {lab : Label → Int64} {q : Call} (h : q.OK ms lab) : q.OK (tpXa ms t) lab :=
  ⟨h.term, h.ev, h.num, h.hold, h.n_lt, h.ctr, h.heap, h.room, h.cells, h.units, h.off, h.accs, h.rt, h.mp,
    h.grow, h.hdr⟩

theorem callOK_untp {lab : Label → Int64} {q : Call} (h : q.OK (tpXa ms t) lab) : q.OK ms lab :=
  ⟨h.term, h.ev, h.num, h.hold, h.n_lt, h.ctr, h.heap, h.room, h.cells, h.units, h.off, h.accs, h.rt, h.mp,
    h.grow, h.hdr⟩

theorem limOk_tp {F : MachineData → Prop} {exe : _root_.Executable} {endPc : Int64} {a Z : BitVec 64}
    (h : LimOk ms F exe endPc a Z) : LimOk (tpXa ms t) F exe endPc a Z :=
  ⟨h.rt, h.mp, h.unmapped, h.room⟩

variable {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop}

theorem proW_tp {pc0 Z lim : Int64} {L : Label} {ps : List (XReg × Int64)} {J : AS → Ctl → Prop}
    (h : ProW W K exe endPc R F ms pc0 Z lim L ps J) : ProW W K exe endPc R F (tpXa ms t) pc0 Z lim L ps J :=
  ⟨h.w0, h.w1, h.w2, h.w3⟩

theorem allocW_tp {q : Call} (h : AllocW ms q W K exe endPc R F) : AllocW (tpXa ms t) q W K exe endPc R F :=
  ⟨h.e, h.entry, h.n2, h.cnt, h.cnt1, h.cnt2, h.rmw, h.n4, h.n5, h.slow, h.n7, h.full, h.ok, h.ok1, h.ok2,
    h.n12, h.hdr, h.n13, h.ret⟩

theorem rdPreW_tp {J0 Jc : AS → Ctl → Prop} (h : RdPreW W K exe endPc R F ms J0 Jc) :
    RdPreW W K exe endPc R F (tpXa ms t) J0 Jc :=
  ⟨proW_tp h.pro, h.e, fun q hok hq => allocW_tp (h.alloc q (callOK_untp hok) hq)⟩

end Tp

/-! ## The source's allocation -/

/-- **`rodata`'s allocation as the allocator's call**: at `rdCN`, `b` bound
to a buffer of `m = 2` lane words, header `257`. -/
def rdQ : Call :=
  ⟨rdCN, "b", .var "m", τ8, eW0, .intS (.lit 2), [TermRun.cst (.num 2)], 2, 257#64, 0#64, 0#64⟩

/-- **A call at `rdCN` is `rodata`'s allocation**: its binder, element
type, continuation and count. -/
theorem rdQ_facts {ms : MemSide isaLSE2} {lab : Label → Int64} {q : Call} (h : q.OK ms lab)
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

/-! ## Addresses off the buffer's base -/

theorem rAddr_x0_0 (r : Reg64s) : rAddr r .X0 0 = r.X0.toBitVec := by
  simp [rAddr, Reg64s.getXReg]

theorem rAddr_x0_8 (r : Reg64s) : rAddr r .X0 8 = r.X0.toBitVec + 8#64 := by
  simp [rAddr, Reg64s.getXReg, BitVec.ofInt_add]

/-! ## `wc_rodata`'s invariants -/

section Inv

variable (lab : Label → Int64) (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide isaLSE2)
  (F0 : MachineData → Prop) (exe : _root_.Executable) (endPc : Int64) (g : WcG)

/-- **The entry's invariant**: `scc_rt_main`'s call of the setup block
(`uN0`, a frame of 48 checked). -/
abbrev sJ0 : AS → Ctl → Prop := (Spike.Lib.A64.Rt.uN0 lab ms F0 exe endPc "wc_rodata" 48 g).J

/-- At the allocation: an entry state, the source at `rdCN`. -/
def sJ1 (J0 : AS → Ctl → Prop) (σ : AS) (c : Ctl) : Prop := (∃ c0, J0 σ c0) ∧ c = rdCN

/-- **`.sp0`'s facts** for label `l`: `x0` its base `A`, in the arena's
cells, and the frame record the caller's. -/
def RdF (σ0 : AS) (l : WeakMem.AllocLabel) : Prop :=
  ∃ A old : Nat, lbl l = some A ∧ σ0.regs.X0.toNat = A ∧ A = ms.heap + 16 * old + ms.off 2 τ8 ∧
    old + ms.units 2 τ8 ≤ ms.cells ∧ σ0.slot (-16) = g.fp ∧ σ0.slot (-8) = g.ra

/-- At `.sp0`: the source past the allocation. -/
def sJp (σ0 : AS) (c : Ctl) : Prop := ∃ l ini, RdF lbl ms g σ0 l ∧ c = rdCA l ini

/-- Before the first exchange's load. -/
def sJp' (σ0 : AS) (c : Ctl) : Prop := ∃ l ini, RdF lbl ms g σ0 l ∧ c = rdC1 l ini

/-- The first word held. -/
def sJh1 (σ0 : AS) (c : Ctl) : Prop := ∃ l ini w, RdF lbl ms g σ0 l ∧
  c = { rdC1 l ini with hold := some ((rAddr σ0.regs .X0 0).toNat, w) }

/-- After the first exchange. -/
def sJ2 (σ0 : AS) (c : Ctl) : Prop := ∃ l ini wo0, RdF lbl ms g σ0 l ∧ c = rdC2 l ini wo0

/-- Before the second exchange's load. -/
def sJ2' (σ0 : AS) (c : Ctl) : Prop := ∃ l ini wo0, RdF lbl ms g σ0 l ∧ c = rdC3 l ini wo0

/-- The second word held. -/
def sJh2 (σ0 : AS) (c : Ctl) : Prop := ∃ l ini wo0 w, RdF lbl ms g σ0 l ∧
  c = { rdC3 l ini wo0 with hold := some ((rAddr σ0.regs .X0 8).toNat, w) }

/-- After the second exchange. -/
def sJ4 (σ0 : AS) (c : Ctl) : Prop := ∃ l ini wo0 wo1, RdF lbl ms g σ0 l ∧ c = rdC4 l ini wo0 wo1

/-- **The setup block's post** (`PostS` of `scc_rt_main`'s interface): the
source at `ret sl` for a buffer at label `l`, base `A` in the arena's cells,
in `x0`, and `x1`–`x3` the slice's other words as the code leaves them. -/
def rdPostS (c : Ctl) (r : Reg64s) : Prop :=
  ∃ (l : WeakMem.AllocLabel) (ini : Nat) (wo0 wo1 : TermRun.Word) (A old : Nat), c = rdRet l ini wo0 wo1 ∧ lbl l = some A ∧ r.X0.toNat = A ∧
    A = ms.heap + 16 * old + ms.off 2 τ8 ∧ old + ms.units 2 τ8 ≤ ms.cells ∧
    r.X1.toBitVec = 0#64 ∧ r.X2.toBitVec = 2#64 ∧ r.X3.toBitVec = 13#64

/-- The return, the frame record restored. -/
def sX : ND := ⟨Int64.ofBitVec g.ra, ⟨0, []⟩, fun σ c =>
  rdPostS lbl ms c σ.regs ∧ σ.regs.X29.toBitVec = g.fp ∧ σ.regs.X30.toBitVec = g.ra⟩

/-- **The return as `scc_rt_main`'s interface has it** (`uNxS`): with `sp`
and the thread pointer as at the call. -/
def sXf : ND := ⟨Int64.ofBitVec g.ra, ⟨0, []⟩, fun σ c =>
  rdPostS lbl ms c σ.regs ∧ σ.regs.X29.toBitVec = g.fp ∧ σ.regs.X30.toBitVec = g.ra ∧
    σ.regs.SP.toBitVec = g.sp ∧ σ.regs.TPIDR_EL0 = g.tp⟩

end Inv

/-! ## The setup block as one segment -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- **The allocator's return at `.sp0` is `sJp`'s**: the label already
placed, its base in `x0`, the source past the allocation. -/
theorem sp0_sJp {F0 : MachineData → Prop} {g : WcG} {t : UInt64} {σ : AS} {c : Ctl}
    (h : (rX (tpXa ms t) (_root_.Executable.labels exe).label lbl
      (sJ1 (sJ0 (_root_.Executable.labels exe).label ms F0 exe endPc g)) .sp0).J σ c) :
    sJp lbl ms g σ c := by
  obtain ⟨q, ⟨σe, ⟨⟨c0, ⟨⟨-, h29, h30, -, -⟩, -⟩⟩, hc⟩, h16, h8⟩, l, ini, old, hv, hcl, hx0, hold, -, -⟩ := h
  obtain ⟨hx, hτ, he, hn⟩ := rdQ_facts (callOK_untp q.2) hc
  obtain ⟨-, x, hw, hxv⟩ := hv
  simp only [Scc.Sem.wordAddr, Option.map_eq_some_iff] at hw
  obtain ⟨A, hl, rfl⟩ := hw
  have hx0' : σ.regs.X0.toNat = ms.heap + 16 * old + ms.off 2 τ8 := by rw [← hn, ← hτ]; exact hx0
  have hold' : old + ms.units 2 τ8 ≤ ms.cells := by rw [← hn, ← hτ]; exact hold
  refine ⟨l, ini, ⟨A, old, hl, by omega, by omega, hold', h16.trans h29, h8.trans h30⟩, ?_⟩
  rw [hc, hx, hτ, he, hn] at hcl
  exact hcl

/-- **`wc_rodata` as `scc_rt_main`'s setup block is one segment inside
`W`** in any valid layout of `hello1Prog`, in a region of depth 256 (its
frame of 48, the allocator's 160 and the heap abort's 48 below that, the
last two in the headroom): from the call's entry (`uN0`, the source at
`rodata`'s body, `hc0`) to the return with `rdPostS`, the frame record,
`sp` and the thread pointer as at the call (`sXf`). The allocation is
`rdQ`, whose premises hold (`hQ`, `hu`); the counter, the headers (`hmem`)
and the buffer's words (`hbuf`) are unmapped in private memory under `F`.
An allocation of a fresh label lands in `ms.xa` at the call's thread
pointer (`hxa`). The heap abort's path is given per caller's state and
source control (`hstub`). The states lie in `W`, none moved by `K`
(`hWpre`, `hWpost`). -/
theorem hello1_rodata_setupW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -256) (hhi : 0 ≤ R.hi) {F0 : MachineData → Prop} (hFF : ∀ m, F m → F0 m)
    (g : WcG) (hc0 : g.c0 = rdC0)
    (hQ : rdQ.OK ms (_root_.Executable.labels exe).label) (hu : ms.units 2 τ8 = 3)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hbuf : ∀ old : Nat, old + ms.units 2 τ8 ≤ ms.cells → ∀ i : Nat, (i = 0 ∨ i = 8) → ∀ m, F m →
      Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * old + ms.off 2 τ8 + i)) 8 = none)
    (hxa : ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop, (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-48, []⟩ mC σC ∧
        (rNL (_root_.Executable.labels exe).label (sJ0 (_root_.Executable.labels exe).label ms F0 exe endPc g)
          (sJ1 (sJ0 (_root_.Executable.labels exe).label ms F0 exe endPc g)) .call).J σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σC) c ∧ CKept R (-48) (-160) 0 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR R) F' (Ea ms q.1 l b w) s c → TP g.tp s → ms.xa l b w s c)
    (hWpre : RdPreW W K exe endPc R F ms (sJ0 (_root_.Executable.labels exe).label ms F0 exe endPc g)
      (sJ1 (sJ0 (_root_.Executable.labels exe).label ms F0 exe endPc g)))
    (hWpost : RdPostLW W K exe endPc R F (sJp lbl ms g) (sJp' lbl ms g) (sJh1 lbl ms g) (sJ2 lbl ms g)
      (sJ2' lbl ms g) (sJh2 lbl ms g) (sJ4 lbl ms g))
    (hstub : ∀ m0 σC c0, σC.regs.X0 = 2 →
      (∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = rdCN ∧ Jfull ms q c0) →
      Abort.Disp.StubHW W K p lbl ms exe endPc (R.callee (-208) (-48) 0)
        (fun m => F m ∧ CKept R (-208) (-48) 0 m0 m ∧ Abs R ⟨-208, []⟩ m0 σC) c0) :
    SegW W K p lbl ms
      (At exe endPc R F (Spike.Lib.A64.Rt.uN0 (_root_.Executable.labels exe).label ms F0 exe endPc "wc_rodata" 48 g))
      (At exe endPc R F (sXf lbl ms g)) := by
  let lab := (_root_.Executable.labels exe).label
  let J0 := sJ0 lab ms F0 exe endPc g
  let J1 := sJ1 J0
  let ms' := tpXa ms g.tp
  -- the bounds of the buffer's words
  have hoff : ms.off 2 τ8 = 8 := by
    have h := hQ.off
    simp only [rdQ] at h
    rw [h]; decide
  have hcells := hQ.cells
  have hroom := hQ.room
  have hA8 : ∀ σ0 l, RdF lbl ms g σ0 l → (σ0.regs.X0.toBitVec + 8#64).toNat = σ0.regs.X0.toNat + 8 := by
    rintro σ0 l ⟨A, old, -, hx0, hA, hold, -, -⟩
    rw [BitVec.toNat_add, show σ0.regs.X0.toBitVec.toNat = σ0.regs.X0.toNat from rfl, hx0]
    simp only [BitVec.toNat_ofNat]
    omega
  -- the first segment: up to the allocator's return
  have hpre : SegW (NoMsrW W K) K p lbl ms' (At exe endPc R F ⟨lab "wc_rodata", ⟨0, []⟩, J0⟩)
      (fun s c => ∃ y, At exe endPc R F (rX ms' lab lbl J1 y) s c) :=
    hello1_rodata_pre_runW hp hend hF hR hal (by omega) hhi (rdPreW_tp (RdPreW.noMsr hp hend hWpre))
      (fun σ c ⟨⟨_, _, _, hsp, htp⟩, hl⟩ => by
        rw [tcbA_limA htp, hsp]; exact limOk_tp (hl.mono hFF))
      (fun σ c hJ => ⟨rdCN, by rw [hJ.1.1, hc0]; exact rdC0_run, ⟨c, hJ⟩, rfl⟩)
      (by
        rintro σ c ⟨-, rfl⟩
        refine ⟨rdQ, callOK_tp hQ, rfl, rfl, rfl, ?_⟩
        show BitVec.ofNat 64 (ms.units 2 τ8) = 3#64
        rw [hu])
      (fun q hq a ha m hm => hmem q (callOK_untp hq) a ha m hm)
      (fun q F' h1 h2 l b w s c hl hAt htp => hxa ⟨q.1, callOK_untp q.2⟩ F' h1 h2 l b w s c hl hAt htp)
  -- the second segment: from `.sp0` to the return
  have hpost : SegW (NoMsrW W K) K p lbl ms'
      (At exe endPc R F (pN lab (sJp lbl ms g) (sJh1 lbl ms g) (sJ2 lbl ms g) (sJh2 lbl ms g) (sJ4 lbl ms g) .s0))
      (At exe endPc R F (sX lbl ms g)) := by
    refine hello1_rodata_post_runW hp hend hF hR hal (by omega) hhi rfl (RdPostLW.noMsr hp hend hWpost)
      ?hra ?hmem ?hr0 ?h1 ?h2 ?hr2 ?h3 ?h4 ?hedge
    case hra =>
      rintro σ0 c ⟨l, ini, ⟨A, old, -, -, -, -, -, h8⟩, -⟩
      show Int64.ofBitVec g.ra = _
      rw [h8]
    case hmem =>
      rintro σ0 c ⟨l, ini, ⟨A, old, -, hx0, hA, hold, -, -⟩, -⟩ i hi m hm
      rcases hi with rfl | rfl
      · have := hbuf old hold 0 (.inl rfl) m hm
        rw [rAddr_x0_0]
        rw [show σ0.regs.X0.toBitVec = BitVec.ofNat 64 (ms.heap + 16 * old + ms.off 2 τ8 + 0) by
          apply BitVec.eq_of_toNat_eq
          rw [show σ0.regs.X0.toBitVec.toNat = σ0.regs.X0.toNat from rfl, hx0, BitVec.toNat_ofNat]
          omega]
        exact this
      · have := hbuf old hold 8 (.inr rfl) m hm
        rw [rAddr_x0_8]
        rw [show σ0.regs.X0.toBitVec + 8#64 = BitVec.ofNat 64 (ms.heap + 16 * old + ms.off 2 τ8 + 8) by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, show σ0.regs.X0.toBitVec.toNat = σ0.regs.X0.toNat from rfl, hx0,
            BitVec.toNat_ofNat, BitVec.toNat_ofNat]
          omega]
        exact this
    case hr0 =>
      rintro σ0 c ⟨l, ini, hRF, rfl⟩
      obtain ⟨A, old, hl, -⟩ := id hRF
      exact ⟨rdC1 l ini, .single (rdCA_store (p := p) (ini := ini) hl).1, l, ini, hRF, rfl⟩
    case h1 =>
      rintro σ0 c ⟨l, ini, hRF, rfl⟩
      obtain ⟨A, old, hl, hx0, -⟩ := id hRF
      obtain ⟨-, hx, hv, hh, -, -⟩ := rdCA_store (p := p) (ini := ini) hl
      refine ⟨_, _, _, _, _, hx, ?_, hh, fun r w' _ _ => ⟨l, ini, w', hRF, rfl⟩⟩
      rw [rAddr_x0_0, show σ0.regs.X0.toBitVec.toNat = A + 8 * 0 by
        rw [show σ0.regs.X0.toBitVec.toNat = σ0.regs.X0.toNat from rfl, hx0]; omega]
      exact hv
    case h2 =>
      rintro σ0 c ⟨l, ini, w', hRF, rfl⟩
      obtain ⟨A, old, hl, hx0, -⟩ := id hRF
      obtain ⟨-, hx, hv, -, hev, hk⟩ := rdCA_store (p := p) (ini := ini) hl
      refine ⟨_, _, _, _, _, _, _, w', hx, ?_, rfl, hev, ?_, l, ini, w', hRF, (rdC1_next l ini w').symm⟩
      · rw [rAddr_x0_0, show σ0.regs.X0.toBitVec.toNat = A + 8 * 0 by
          rw [show σ0.regs.X0.toBitVec.toNat = σ0.regs.X0.toNat from rfl, hx0]; omega]
        exact hv
      · rw [show (rpK1.setWidth 128).toNat = rdK1 by decide]; exact hk
    case hr2 =>
      rintro σ0 c ⟨l, ini, wo0, hRF, rfl⟩
      obtain ⟨A, old, hl, -⟩ := id hRF
      exact ⟨rdC3 l ini wo0, .single (rdC2_store (p := p) (ini := ini) (wo0 := wo0) hl).1, l, ini, wo0, hRF, rfl⟩
    case h3 =>
      rintro σ0 c ⟨l, ini, wo0, hRF, rfl⟩
      have h8 := hA8 σ0 l hRF
      obtain ⟨A, old, hl, hx0, -⟩ := id hRF
      obtain ⟨-, hx, hv, hh, -, -⟩ := rdC2_store (p := p) (ini := ini) (wo0 := wo0) hl
      refine ⟨_, _, _, _, _, hx, ?_, hh, fun r w' _ _ => ⟨l, ini, wo0, w', hRF, rfl⟩⟩
      rw [rAddr_x0_8, h8, hx0]
      exact hv
    case h4 =>
      rintro σ0 c ⟨l, ini, wo0, w', hRF, rfl⟩
      have h8 := hA8 σ0 l hRF
      obtain ⟨A, old, hl, hx0, -⟩ := id hRF
      obtain ⟨-, hx, hv, -, hev, hk⟩ := rdC2_store (p := p) (ini := ini) (wo0 := wo0) hl
      refine ⟨_, _, _, _, _, _, _, w', hx, ?_, rfl, hev, ?_, l, ini, wo0, w', hRF, (rdC3_next l ini wo0 w').symm⟩
      · rw [rAddr_x0_8, h8, hx0]
        exact hv
      · rw [show (rpK2.setWidth 128).toNat = rdK2 by decide]; exact hk
    case hedge =>
      rintro σ0 c ⟨l, ini, wo0, wo1, ⟨A, old, hl, hx0, hA, hold, h16, h8⟩, rfl⟩ σ' h0 h1 h2 h3 h29 h30
      refine ⟨rdRet l ini wo0 wo1, rdC4_run l ini wo0 wo1, ⟨l, ini, wo0, wo1, A, old, rfl, hl, ?_, hA, hold, h1, h2, h3⟩,
        h29.trans h16, h30.trans h8⟩
      show σ'.regs.X0.toBitVec.toNat = A
      rw [h0]; exact hx0
  -- composed, under the thread pointer's memory side
  have hA : SegW (NoMsrW W K) K p lbl ms' (At exe endPc R F ⟨lab "wc_rodata", ⟨0, []⟩, J0⟩)
      (fun s c => At exe endPc R F (sX lbl ms g) s c ∨ At exe endPc R F (rX ms' lab lbl J1 .abort) s c) := by
    refine SegW.seq_left (hpre.mono_post fun s c ⟨y, h⟩ => ?_) hpost
    cases y
    · obtain ⟨he, hn, hdc, hpc, σ, hAb, hD, hJ⟩ := h
      exact .inl ⟨he, hn, hdc, hpc, σ, hAb, hD, sp0_sJp hJ⟩
    · exact .inr h
  have hB := SegW.keepTPN (t := g.tp) hK hA
  -- the heap abort
  have hAb : SegW W K p lbl ms (At exe endPc R F (rX ms' lab lbl J1 .abort)) (fun _ _ => False) := by
    refine Abort.Disp.seg_jabort2W rfl ?_ hF hR hal (by show R.lo ≤ -208 - 48; omega)
      (by show (-208 : Int) < R.hi; omega) (by show (-208 : Int) % 16 = 0; decide) hK ?_
    · rintro σ c ⟨h2, -⟩
      show σ.regs.X0.toNat = 2
      rw [h2]; rfl
    · rintro m0 σC c0 ⟨h2, q, hf, σe, -, hc⟩
      exact hstub m0 σC c0 h2 ⟨q.1, callOK_untp q.2, hc, hf⟩
  have hC := SegW.seq_left (hB.mono_post (Q' := fun s c => At exe endPc R F (rX ms' lab lbl J1 .abort) s c ∨
    (At exe endPc R F (sX lbl ms g) s c ∧ TP g.tp s)) fun s c ⟨h, ht⟩ =>
    h.elim (fun h => .inr ⟨h, ht⟩) fun h => .inl h) hAb
  refine (SegW.of_imp (L := R.addr 0 = g.sp) fun hL => (hC.mono_post fun s c h => ?_)).mono_pre
    fun s c h => ?_
  · rcases h with h | ⟨⟨he, hn, hdc, hpc, σ, hAb, hD, hJ, h29, h30⟩, ht⟩
    · exact h.elim
    refine ⟨he, hn, hdc, hpc, σ, hAb, hD, hJ, h29, h30, ?_, ?_⟩
    · have := hAb.so .SP 0 rfl
      rw [← hL]; exact this
    · rw [← hAb.regs]; exact ht
  · obtain ⟨he, hn, hdc, hpc, σ, hAb, hD, ⟨hc, h29, h30, hsp, htp⟩, hl⟩ := id h
    refine ⟨⟨h, ?_⟩, ?_⟩
    · show s.st.1.regs.TPIDR_EL0 = g.tp
      rw [hAb.regs]; exact htp
    · rw [← hsp]; exact (hAb.so .SP 0 rfl).symm

end Proof

end Hello1

end Spike.Lib.A64.Flow
