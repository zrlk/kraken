/-
**The allocator's memory instructions as nodes of a function** (AArch64).

`scc_rt_alloc` (`Scc/Lower/Runtime.lean`, `allocF`; `Scc/Sem/HeapCtr.lean`)
has three instructions the block lemma (`Spike/Lib/A64Flow.lean`) does not
cover, besides its label addresses (`si_nd`, `Spike/Lib/A64Nodes.lean`):

- **the heap counter's add** `ldaddal Xs, Xt, [Xn]` (`ctr_nd`, through
  `Out.ctrRmw`): `Xn` holds the counter's address (`ms.ctr`, owned by the
  runtime, mapped, outside the thread's private memory), `Xs` the buffer's
  units;
  for every old value the runtime memory may hold there within the arena's
  cells, the state after it (`Xt` the old value, its offset forgotten)
  lands at a node with the control holding the counter and the old count;
- **the header store** `str Xt, [Xn, #i]` (`rtst_nd`, through
  `Out.rtStore`): a store to an address the runtime owns, of a value its
  memory may hold there, outside the thread's private memory; the abstract
  state is unchanged;
- **a runtime load** `ldr Xt, [Xn, #i]` (`rtld_nd`, through `Out.rtLoad`;
  not the allocator's, but the same shape, e.g. a thread-control-block word
  read through `mrs Xn, tpidr_el0`): a load from an address the runtime
  owns, outside the thread's private memory; every value its memory may
  hold there lands, in `Xt`, at a node;
- **an exchange's load and store** `ldr Xt, [Xn, #i]` / `str Xt, [Xn, #i]`
  (`holdLd_nd`, `xchgSt_nd`, through `Out.holdLoad` / `Out.xchgStore`; not
  the allocator's, but the same shapes, e.g. scc's `xchg` on a buffer
  element): the load holds the word the source may read, the store takes
  the source's exchange step and ends the hold;
- **the allocation's last instruction** (`alloc_nd`, through `Out.alloc`):
  a covered instruction (the `ret`) at which the source takes its `newBuf`
  step, binding the buffer at the base the code computed; for a fresh
  label the state after it is one the allocation continues in (`ms.xa`).

Kraken's rows: `exec_ldop`, `exec_ldr` and `exec_str` (`Kraken/Promising/Lower/
EventsA64.lean`), resolved by `access_agrees` where the declarations agree.
-/
import Spike.Lib.A64Nodes

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (ValRep)

/-! ## The instructions -/

/-- `ld<op><k> Xs, Xt, [Xn]`, 64-bit. -/
def ldopDir (op : AtomicOp) (k : RmwKind) (rs rt b : XReg) : Directive :=
  .instr ⟨.W64, .LDOP op k .W64 (.low (.reg rs) .W64) (.low (.reg rt) .W64) (.low (.reg b) .W64)⟩

/-- `str Xt, [Xn, #i]`, 64-bit. -/
def strDir (t b : XReg) (i : Int64) : Directive :=
  .instr ⟨.W64, .STR (.low (.reg t) .W64) ⟨.low (.reg b) .W64, .imm ⟨.int64 i, none⟩⟩⟩

/-- `ldr Xt, [Xn, #i]`, 64-bit. -/
def ldrDir (t b : XReg) (i : Int64) : Directive :=
  .instr ⟨.W64, .LDR (.low (.reg t) .W64) (.addr ⟨.low (.reg b) .W64, .imm ⟨.int64 i, none⟩⟩)⟩

/-- The address `[Xn, #i]` reads in the registers `r`. -/
def rAddr (r : Reg64s) (b : XReg) (i : Int64) : BitVec 64 :=
  BitVec.ofInt 64 ((r.getXReg b).toBitVec.toInt + i.toInt)

/-- The abstract state after a load of `v` into `Xt`. -/
def ldStep (t : XReg) (v : BitVec 64) (σ : AS) : AS :=
  { σ with regs := σ.regs.setRegOrZr (.low (.reg t) .W64) v }

/-- The heap counter's location. -/
abbrev ctrLoc {I : ISA} (ms : MemSide I) : Loc := ⟨BitVec.ofNat 64 ms.ctr, 8⟩

/-- The control after the counter's add returned `old`: it holds the
counter's address and the old count. -/
def holdCtr {I : ISA} (ms : MemSide I) (c : Ctl) (old : BitVec 64) : Ctl :=
  { c with hold := some (ms.ctr, TermRun.cst (.num old.toNat)) }

/-- The control after a buffer allocation `let x = newBuf a τ in e` of `k`
elements at label `l`, `ini` of them initialised. -/
def allocCtl (c : Ctl) (x : String) (τ : Ty) (e : Expr) (k : Nat) (l : WeakMem.AllocLabel) (ini : Nat) : Ctl :=
  ⟨e, (x, .refine (.loc .own (.array (.lit k) (TermRun.close [] τ))) (.ini (.lit ini)),
    [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: c.env, none⟩

/-- `AtomicOp.ADD` adds. -/
theorem add_apply (a b : BitVec 64) : AtomicOp.ADD.apply a b = a + b := rfl

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-! ## The heap counter's add -/

/-- **`ctr_ndW` at any allocation site** (`AllocSite`: a buffer allocation,
or, where the memory side allows it, `ms.newOk`, a box `new` of one
object): the same node, the source's site given as `AllocSite`. -/
theorem ctr_ndWS {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {k : RmwKind} {rs rt b : XReg}
    (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [ldopDir .ADD k rs rt b])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = BitVec.ofNat 64 ms.ctr ∧ ms.rt (BitVec.ofNat 64 ms.ctr).toNat ∧
      ms.mp (ctrLoc ms) true ∧ Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none ∧
      ∃ (x : String) (τ : Ty) (e : Expr) (nn : Nat), AllocSite ms.newOk c x nn τ e ∧ c.hold = none ∧
        σ.regs.getRegOrZr (.low (.reg rs) .W64) = BitVec.ofNat 64 (ms.units nn τ) ∧
        ∀ old : Val, ms.G (ctrLoc ms) old → (old.setWidth 64).toNat ≤ ms.cells → ms.lo (old.setWidth 64).toNat →
          ms.G (ctrLoc ms) ((old.setWidth 64 + BitVec.ofNat 64 (ms.units nn τ)).setWidth 128) ∧
          Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill rt, ldStep rt (old.setWidth 64) σ⟩
            (holdCtr ms c (old.setWidth 64))) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (ldopDir .ADD k rs rt b) 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨hb, hrt, hmp, hdm, x, τ, e, nn, hs, hh, hrs, hX⟩ := hedge _ σ c hA hD hJ
  have hb' : (s.st.1.regs.getXReg b).toBitVec = BitVec.ofNat 64 ms.ctr := by rw [hA.regs]; exact hb
  have hex := exec_ldop hc (by rw [hb']; exact hdm)
  rw [hb', access_agrees (agrees_of_decls hdc _ _)] at hex
  refine .ctrRmw k _ _ x τ e nn hex hrt hmp hs hh (fun old => ?_) fun old hG _ hle hlo => ?_
  · rw [hA.regs, hrs, add_apply]
  obtain ⟨hG', hL⟩ := hX old hG hle hlo
  refine ⟨hG', ?_⟩
  have hA' : Abs R (n.o.kill rt)
      { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg rt) .W64) (old.setWidth 64) }
      (ldStep rt (old.setWidth 64) σ) := by
    refine ⟨by simp only [ldStep, hA.regs], hA.status, ?_, hA.slot⟩
    exact hA.so.killZ (.low (.reg rt) .W64) (old.setWidth 64)
  have hD' : F { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg rt) .W64) (old.setWidth 64) } :=
    hF _ _ hD fun _ _ _ => rfl
  have hs1 : after s 4 { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg rt) .W64) (old.setWidth 64) } =
      { s with st := ({ s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg rt) .W64) (old.setWidth 64) },
        n.pc + Int64.ofNat 4) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA' hD'⟩
  · exact .inr ⟨y, hy.at he hn hdc hA' hD'⟩

/-- **A node at the heap counter's add** `ld<add><k> Xs, Xt, [Xn]`: from
every state of the invariant `Xn` holds the counter's address, owned by
the runtime and mapped for writing (`ms.mp`), outside the thread's private memory;
the source is at a buffer allocation of `nn`
elements, no hold pending, and `Xs` holds the buffer's units; for every
old value the runtime memory may hold at the counter within the arena's
cells and above the counter floor (`ms.lo`), the new value may be held there
too, and the state after it (`Xt`
the old value) lands at a node with the control holding the old count. Its states lie in `W`, and no outside
move `K` moves them (`hW`). -/
theorem ctr_ndW {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {k : RmwKind} {rs rt b : XReg} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [ldopDir .ADD k rs rt b])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = BitVec.ofNat 64 ms.ctr ∧ ms.rt (BitVec.ofNat 64 ms.ctr).toNat ∧
      ms.mp (ctrLoc ms) true ∧ Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none ∧
      ∃ (x : String) (a : CoreTerm.At) (τ : Ty) (e : Expr) (ta : Ty) (ws : List TermRun.Word) (nn : Nat),
        c.term = .let_ x (.newBuf a τ) e ∧ TermRun.evalAt c.env a = some (ta, ws) ∧ TermRun.numOf ws = some nn ∧
        c.hold = none ∧ σ.regs.getRegOrZr (.low (.reg rs) .W64) = BitVec.ofNat 64 (ms.units nn τ) ∧
        ∀ old : Val, ms.G (ctrLoc ms) old → (old.setWidth 64).toNat ≤ ms.cells → ms.lo (old.setWidth 64).toNat →
          ms.G (ctrLoc ms) ((old.setWidth 64 + BitVec.ofNat 64 (ms.units nn τ)).setWidth 128) ∧
          Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill rt, ldStep rt (old.setWidth 64) σ⟩
            (holdCtr ms c (old.setWidth 64))) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  ctr_ndWS hF hcode hW fun m σ c hA hD hJ =>
    let ⟨hb, hrt, hmp, hdm, x, a, τ, e, ta, ws, nn, ht, hev, hnn, hh, hrs, hX⟩ := hedge m σ c hA hD hJ
    ⟨hb, hrt, hmp, hdm, x, τ, e, nn, .inl ⟨a, ta, ws, ht, hev, hnn⟩, hh, hrs, hX⟩

/-- **`ctr_ndW` inside the trivial predicate**, with no outside moves. -/
theorem ctr_nd {n : ND} {k : RmwKind} {rs rt b : XReg} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [ldopDir .ADD k rs rt b])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = BitVec.ofNat 64 ms.ctr ∧ ms.rt (BitVec.ofNat 64 ms.ctr).toNat ∧
      ms.mp (ctrLoc ms) true ∧ Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none ∧
      ∃ (x : String) (a : CoreTerm.At) (τ : Ty) (e : Expr) (ta : Ty) (ws : List TermRun.Word) (nn : Nat),
        c.term = .let_ x (.newBuf a τ) e ∧ TermRun.evalAt c.env a = some (ta, ws) ∧ TermRun.numOf ws = some nn ∧
        c.hold = none ∧ σ.regs.getRegOrZr (.low (.reg rs) .W64) = BitVec.ofNat 64 (ms.units nn τ) ∧
        ∀ old : Val, ms.G (ctrLoc ms) old → (old.setWidth 64).toNat ≤ ms.cells → ms.lo (old.setWidth 64).toNat →
          ms.G (ctrLoc ms) ((old.setWidth 64 + BitVec.ofNat 64 (ms.units nn τ)).setWidth 128) ∧
          Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill rt, ldStep rt (old.setWidth 64) σ⟩
            (holdCtr ms c (old.setWidth 64))) :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (ctr_ndW (W := fun _ _ => True) (K := fun _ _ => False) (hW := fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    hF hcode hedge).toSeg

/-! ## A runtime store -/

/-- **A node at a runtime store** `str Xt, [Xn, #i]`: from every state of
the invariant the address is owned by the runtime and mapped for writing
(`ms.mp`), outside the thread's private memory, and the value is one the runtime memory may hold there; the
abstract state is unchanged and lands at a node after a local run of the
source. Its states lie in `W`, and no outside
move `K` moves them (`hW`). -/
theorem rtst_ndW {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {t b : XReg} {i : Int64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [strDir t b i])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      ms.rt (rAddr σ.regs b i).toNat ∧ ms.mp ⟨rAddr σ.regs b i, 8⟩ true ∧
      ms.G ⟨rAddr σ.regs b i, 8⟩ ((σ.regs.getRegOrZr (.low (.reg t) .W64)).setWidth 128) ∧
      Mem.loadInt m.dmem (rAddr σ.regs b i) 8 = none ∧
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat 4, n.o, σ⟩ c') :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (strDir t b i) 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨hrt, hmp, hG, hdm, c', hr, hL⟩ := hedge _ σ c hA hD hJ
  have ha : rAddr s.st.1.regs b i = rAddr σ.regs b i := by rw [hA.regs]
  have hex := exec_str_agrees hc ha (by exact hdm) (agrees_of_decls hdc _ _)
  rw [hA.regs] at hex
  refine .rtStore _ _ _ _ c' hex hrt hmp hG hr ?_
  have hs1 : after s 4 s.st.1 = { s with st := (s.st.1, n.pc + Int64.ofNat 4) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA hD⟩
  · exact .inr ⟨y, hy.at he hn hdc hA hD⟩

/-- **`rtst_ndW` inside the trivial predicate**, with no outside moves. -/
theorem rtst_nd {n : ND} {t b : XReg} {i : Int64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [strDir t b i])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      ms.rt (rAddr σ.regs b i).toNat ∧ ms.mp ⟨rAddr σ.regs b i, 8⟩ true ∧
      ms.G ⟨rAddr σ.regs b i, 8⟩ ((σ.regs.getRegOrZr (.low (.reg t) .W64)).setWidth 128) ∧
      Mem.loadInt m.dmem (rAddr σ.regs b i) 8 = none ∧
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat 4, n.o, σ⟩ c') :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (rtst_ndW (W := fun _ _ => True) (K := fun _ _ => False) (hW := fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    hcode hedge).toSeg

/-! ## A runtime load -/

/-- **A node at a runtime load** `ldr Xt, [Xn, #i]`: from every state of the
invariant the address is owned by the runtime and mapped for reading
(`ms.mp`), outside the thread's private memory; after a local run of the source, for every value the runtime
memory may hold there, the state after the load (`Xt` the value, its offset
forgotten) lands at a node. Its states lie in `W`, and no outside
move `K` moves them (`hW`). -/
theorem rtld_ndW {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {t b : XReg} {i : Int64} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [ldrDir t b i])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      ms.rt (rAddr σ.regs b i).toNat ∧ ms.mp ⟨rAddr σ.regs b i, 8⟩ false ∧
      Mem.loadInt m.dmem (rAddr σ.regs b i) 8 = none ∧
      ∃ c', LocalRun p c c' ∧ ∀ v : Val, ms.G ⟨rAddr σ.regs b i, 8⟩ v →
        Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill t, ldStep t (v.setWidth 64) σ⟩ c') :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (ldrDir t b i) 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨hrt, hmp, hdm, c', hr, hL⟩ := hedge _ σ c hA hD hJ
  have ha : rAddr s.st.1.regs b i = rAddr σ.regs b i := by rw [hA.regs]
  have hex := exec_ldr_agrees hc ha (by exact hdm) (agrees_of_decls hdc _ _)
  refine .rtLoad _ _ _ c' hex hrt hmp hr fun v hG _ => ?_
  have hA' : Abs R (n.o.kill t)
      { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) (v.setWidth 64) }
      (ldStep t (v.setWidth 64) σ) := by
    refine ⟨by simp only [ldStep, hA.regs], hA.status, ?_, hA.slot⟩
    exact hA.so.killZ (.low (.reg t) .W64) (v.setWidth 64)
  have hD' : F { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) (v.setWidth 64) } :=
    hF _ _ hD fun _ _ _ => rfl
  have hs1 : after s 4 { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) (v.setWidth 64) } =
      { s with st := ({ s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) (v.setWidth 64) },
        n.pc + Int64.ofNat 4) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL v hG with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA' hD'⟩
  · exact .inr ⟨y, hy.at he hn hdc hA' hD'⟩

/-- **`rtld_ndW` inside the trivial predicate**, with no outside moves. -/
theorem rtld_nd {n : ND} {t b : XReg} {i : Int64} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [ldrDir t b i])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      ms.rt (rAddr σ.regs b i).toNat ∧ ms.mp ⟨rAddr σ.regs b i, 8⟩ false ∧
      Mem.loadInt m.dmem (rAddr σ.regs b i) 8 = none ∧
      ∃ c', LocalRun p c c' ∧ ∀ v : Val, ms.G ⟨rAddr σ.regs b i, 8⟩ v →
        Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill t, ldStep t (v.setWidth 64) σ⟩ c') :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (rtld_ndW (W := fun _ _ => True) (K := fun _ _ => False) (hW := fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    hF hcode hedge).toSeg

/-! ## An exchange's load -/

/-- **A node at an exchange's plain load** `ldr Xt, [Xn, #i]`: from every
state in `W` the address is unmapped in `dmem` (`hdm`); the source is at an exchange site
(`XchgSite`) of the word at `sa`, which the address represents, no hold
pending; for every value read and every word the source may read that
represents it, the state after the load (`Xt` the value, its offset
forgotten) lands at a node with the control holding the address and the
word. Its states lie in `W`, and no outside move `K` moves them (`hW`). -/
theorem holdLd_ndWS {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {t b : XReg} {i : Int64}
    (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [ldrDir t b i])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hdm : ∀ s c σ, W s c → Abs R n.o s.st.1 σ → F s.st.1 → n.J σ c →
      Mem.loadInt s.st.1.dmem (rAddr σ.regs b i) 8 = none)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
        XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) (rAddr σ.regs b i).toNat ∧ c.hold = none ∧
        ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → ValRep lbl w'.val (r.setWidth 64).toNat →
          Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill t, ldStep t (r.setWidth 64) σ⟩
            { c with hold := some ((rAddr σ.regs b i).toNat, w') }) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c hAt => ?_
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := hAt
  have hdm' := hdm s c σ (hW s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩).1 hA hD hJ
  have hc : CellAt s (ldrDir t b i) 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨x, sa, u, v, e, hx, hv, hh, hL⟩ := hedge _ σ c hA hD hJ
  have ha : rAddr s.st.1.regs b i = rAddr σ.regs b i := by rw [hA.regs]
  have hex := exec_ldr_agrees hc ha (by exact hdm') (agrees_of_decls hdc _ _)
  refine .holdLoad _ _ _ x sa u v e hex hx hv hh fun r w' hr hrep => ?_
  have hA' : Abs R (n.o.kill t)
      { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) (r.setWidth 64) }
      (ldStep t (r.setWidth 64) σ) := by
    refine ⟨by simp only [ldStep, hA.regs], hA.status, ?_, hA.slot⟩
    exact hA.so.killZ (.low (.reg t) .W64) (r.setWidth 64)
  have hD' : F { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) (r.setWidth 64) } :=
    hF _ _ hD fun _ _ _ => rfl
  have hs1 : after s 4 { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) (r.setWidth 64) } =
      { s with st := ({ s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) (r.setWidth 64) },
        n.pc + Int64.ofNat 4) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL r w' hr hrep with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA' hD'⟩
  · exact .inr ⟨y, hy.at he hn hdc hA' hD'⟩

/-- **A node at an exchange's plain load** `ldr Xt, [Xn, #i]`: from every
state of the invariant the address is unmapped in `dmem`; the source is at an exchange site
(`XchgSite`) of the word at `sa`, which the address represents, no hold
pending; for every value read and every word the source may read that
represents it, the state after the load (`Xt` the value, its offset
forgotten) lands at a node with the control holding the address and the
word. Its states lie in `W`, and no outside move `K` moves them (`hW`). -/
theorem holdLd_ndW {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {t b : XReg} {i : Int64}
    (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [ldrDir t b i])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      Mem.loadInt m.dmem (rAddr σ.regs b i) 8 = none ∧
      ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
        XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) (rAddr σ.regs b i).toNat ∧ c.hold = none ∧
        ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → ValRep lbl w'.val (r.setWidth 64).toNat →
          Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill t, ldStep t (r.setWidth 64) σ⟩
            { c with hold := some ((rAddr σ.regs b i).toNat, w') }) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  holdLd_ndWS hF hcode hW (fun _ _ σ _ hA hD hJ => (hedge _ σ _ hA hD hJ).1)
    fun m σ c hA hD hJ => (hedge m σ c hA hD hJ).2

/-- **`holdLd_ndW` inside the trivial predicate**, with no outside moves. -/
theorem holdLd_nd {n : ND} {t b : XReg} {i : Int64} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [ldrDir t b i])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      Mem.loadInt m.dmem (rAddr σ.regs b i) 8 = none ∧
      ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
        XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) (rAddr σ.regs b i).toNat ∧ c.hold = none ∧
        ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → ValRep lbl w'.val (r.setWidth 64).toNat →
          Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill t, ldStep t (r.setWidth 64) σ⟩
            { c with hold := some ((rAddr σ.regs b i).toNat, w') }) :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (holdLd_ndW (W := fun _ _ => True) (K := fun _ _ => False) (hW := fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    hF hcode hedge).toSeg

/-! ## An exchange's store -/

/-- **A node at an exchange's plain store** `str Xt, [Xn, #i]`: from every
state in `W` the address is unmapped in `dmem` (`hdm`); the source is at an exchange site
(`XchgSite`) of the word at `sa`, which the address represents, holding
the address and the word `wold`, and `Xt` represents the exchanged value's
word; the abstract state is unchanged and lands at a node with `x` bound to
`wold` and the hold ended. Its states lie in `W`, and no outside move `K`
moves them (`hW`). -/
theorem xchgSt_ndWS {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {t b : XReg} {i : Int64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [strDir t b i])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hdm : ∀ s c σ, W s c → Abs R n.o s.st.1 σ → F s.st.1 → n.J σ c →
      Mem.loadInt s.st.1.dmem (rAddr σ.regs b i) 8 = none)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
        (wv wold : TermRun.Word),
        XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) (rAddr σ.regs b i).toNat ∧
        c.hold = some ((rAddr σ.regs b i).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
        ValRep lbl wv.val ((σ.regs.getRegOrZr (.low (.reg t) .W64)).setWidth 128).toNat ∧
        Lands N E ⟨n.pc + Int64.ofNat 4, n.o, σ⟩ ⟨e, (x, u, [wold]) :: c.env, none⟩) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c hAt => ?_
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := hAt
  have hdm' := hdm s c σ (hW s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩).1 hA hD hJ
  have hc : CellAt s (strDir t b i) 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨x, sa, u, v, e, tv, wv, wold, hx, hrep, hh, hev, hV, hL⟩ := hedge _ σ c hA hD hJ
  have ha : rAddr s.st.1.regs b i = rAddr σ.regs b i := by rw [hA.regs]
  have hex := exec_str_agrees hc ha (by exact hdm') (agrees_of_decls hdc _ _)
  rw [hA.regs] at hex
  refine .xchgStore _ _ _ _ x sa u v e tv wv wold hex hx hrep hh hev hV ?_
  have hs1 : after s 4 s.st.1 = { s with st := (s.st.1, n.pc + Int64.ofNat 4) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA hD⟩
  · exact .inr ⟨y, hy.at he hn hdc hA hD⟩

/-- **A node at an exchange's plain store** `str Xt, [Xn, #i]`: from every
state of the invariant the address is unmapped in `dmem`; the source is at an exchange site
(`XchgSite`) of the word at `sa`, which the address represents, holding
the address and the word `wold`, and `Xt` represents the exchanged value's
word; the abstract state is unchanged and lands at a node with `x` bound to
`wold` and the hold ended. Its states lie in `W`, and no outside move `K`
moves them (`hW`). -/
theorem xchgSt_ndW {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {t b : XReg} {i : Int64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [strDir t b i])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      Mem.loadInt m.dmem (rAddr σ.regs b i) 8 = none ∧
      ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
        (wv wold : TermRun.Word),
        XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) (rAddr σ.regs b i).toNat ∧
        c.hold = some ((rAddr σ.regs b i).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
        ValRep lbl wv.val ((σ.regs.getRegOrZr (.low (.reg t) .W64)).setWidth 128).toNat ∧
        Lands N E ⟨n.pc + Int64.ofNat 4, n.o, σ⟩ ⟨e, (x, u, [wold]) :: c.env, none⟩) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  xchgSt_ndWS hcode hW (fun _ _ σ _ hA hD hJ => (hedge _ σ _ hA hD hJ).1)
    fun m σ c hA hD hJ => (hedge m σ c hA hD hJ).2

/-- **`xchgSt_ndW` inside the trivial predicate**, with no outside moves. -/
theorem xchgSt_nd {n : ND} {t b : XReg} {i : Int64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [strDir t b i])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      Mem.loadInt m.dmem (rAddr σ.regs b i) 8 = none ∧
      ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
        (wv wold : TermRun.Word),
        XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) (rAddr σ.regs b i).toNat ∧
        c.hold = some ((rAddr σ.regs b i).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
        ValRep lbl wv.val ((σ.regs.getRegOrZr (.low (.reg t) .W64)).setWidth 128).toNat ∧
        Lands N E ⟨n.pc + Int64.ofNat 4, n.o, σ⟩ ⟨e, (x, u, [wold]) :: c.env, none⟩) :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (xchgSt_ndW (W := fun _ _ => True) (K := fun _ _ => False) (hW := fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    hcode hedge).toSeg

/-! ## The allocation's last instruction -/

/-- **A node at a buffer allocation's last instruction**, a covered
instruction `a` (inside the region `[lo, hi)`): from every state of the
invariant the source is at `let x = newBuf a' τ in e` of `kk` elements,
holding the counter's old count `old` (`ctr_nd`), and the code computed the
base `A = ms.heap + 16·old + ms.off kk τ` with the object within the
cells (`old + ms.units kk τ ≤ ms.cells`); for every fresh label `l`
(`lbl l = none`), the state after `a` hits the node `Ea l A (kk·w)` (`w`
the element type's words) with `x` bound to `l`'s locative (`allocCtl`),
and every state at that node is one the allocation continues in
(`hxa`, `ms.xa`). The node lands nowhere in `Next`: the allocation's
continuation is `ms.xa` (see `Out.alloc`). Its states lie in `W`, and no
outside move `K` moves them (`hW`). -/
theorem alloc_ndW {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {lo hi : Int} {a : AI}
    (Ea : WeakMem.AllocLabel → Nat → Nat → ND)
    (hok : a.ok lo hi n.o = true)
    (hreg : ∀ w op, a = .reg w op → RegOnly op = true) (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [a.toDir])
    (hxa : ∀ l b w s c, lbl l = none → At exe endPc R F (Ea l b w) s c → ms.xa l b w s c)
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ σ c, n.J σ c →
      ∃ (A : BitVec 64) (x : String) (a' : CoreTerm.At) (τ : Ty) (e : Expr) (ta : Ty) (ws : List TermRun.Word)
        (kk : Nat) (wold : TermRun.Word) (old : Nat) (us : List TermRun.Acc),
        c.term = .let_ x (.newBuf a' τ) e ∧ TermRun.evalAt c.env a' = some (ta, ws) ∧
        TermRun.numOf ws = some kk ∧ c.hold = some (ms.ctr, wold) ∧ TermRun.numOf [wold] = some old ∧
        A.toNat = ms.heap + 16 * old + ms.off kk τ ∧ old + ms.units kk τ ≤ ms.cells ∧
        TermRun.accs (TermRun.close [] τ) = some us ∧
        ∀ (l : WeakMem.AllocLabel) (ini : Nat), lbl l = none →
          Hit (Ea l A.toNat (kk * TermRun.nWords us))
            ⟨a.tgt (_root_.Executable.labels exe).label (n.pc + Int64.ofNat 4) σ, a.so n.o,
              a.step n.o (n.pc + Int64.ofNat 4) σ⟩ (allocCtl c x τ e kk l ini)) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s a.toDir 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨m', hex, hA', hD'⟩ := exec_ai hok hR hal hlo hhi hc hreg hA
  have hl : labA s = (_root_.Executable.labels exe).label := by
    funext L; show (_root_.Executable.labels s.exe).label L = _; rw [he]
  rw [hl, hpc] at hex
  rw [hpc] at hA'
  obtain ⟨A, x, a', τ, e, ta, ws, kk, wold, old, us, ht, hev, hkk, hh, hold, hAeq, hcl, hus, hX⟩ := hedge σ c hJ
  refine .alloc _ A x a' τ e ta ws kk wold old us hex ht hev hkk hh hold hAeq hcl hus fun l ini hl => ?_
  exact hxa _ _ _ _ _ hl ((hX l ini hl).at he hn hdc hA' (hF _ _ hD hD'))

/-- **`alloc_ndW` inside the trivial predicate**, with no outside moves. -/
theorem alloc_nd {n : ND} {lo hi : Int} {a : AI} (Ea : WeakMem.AllocLabel → Nat → Nat → ND)
    (hok : a.ok lo hi n.o = true)
    (hreg : ∀ w op, a = .reg w op → RegOnly op = true) (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [a.toDir])
    (hxa : ∀ l b w s c, lbl l = none → At exe endPc R F (Ea l b w) s c → ms.xa l b w s c)
    (hedge : ∀ σ c, n.J σ c →
      ∃ (A : BitVec 64) (x : String) (a' : CoreTerm.At) (τ : Ty) (e : Expr) (ta : Ty) (ws : List TermRun.Word)
        (kk : Nat) (wold : TermRun.Word) (old : Nat) (us : List TermRun.Acc),
        c.term = .let_ x (.newBuf a' τ) e ∧ TermRun.evalAt c.env a' = some (ta, ws) ∧
        TermRun.numOf ws = some kk ∧ c.hold = some (ms.ctr, wold) ∧ TermRun.numOf [wold] = some old ∧
        A.toNat = ms.heap + 16 * old + ms.off kk τ ∧ old + ms.units kk τ ≤ ms.cells ∧
        TermRun.accs (TermRun.close [] τ) = some us ∧
        ∀ (l : WeakMem.AllocLabel) (ini : Nat), lbl l = none →
          Hit (Ea l A.toNat (kk * TermRun.nWords us))
            ⟨a.tgt (_root_.Executable.labels exe).label (n.pc + Int64.ofNat 4) σ, a.so n.o,
              a.step n.o (n.pc + Int64.ofNat 4) σ⟩ (allocCtl c x τ e kk l ini)) :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (alloc_ndW (W := fun _ _ => True) (K := fun _ _ => False) (hW := fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    Ea hok hreg hF hR hal hlo hhi hcode hxa hedge).toSeg

/-- **A node at a single silent instruction** `a` (a register move, a
frame access, a branch, a `ret`): from every state of the invariant the
source takes a local run and the abstract step lands at a node (the
allocator's `ret` at a box allocation, where the hold is kept for the box's
store). Its states lie in `W`, and no outside move `K` moves them
(`hW`). -/
theorem ai_ndW {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {lo hi : Int} {a : AI}
    (hok : a.ok lo hi n.o = true)
    (hreg : ∀ w op, a = .reg w op → RegOnly op = true) (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [a.toDir])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ σ c, n.J σ c → ∃ c', LocalRun p c c' ∧
      Lands N E ⟨a.tgt (_root_.Executable.labels exe).label (n.pc + Int64.ofNat 4) σ, a.so n.o,
        a.step n.o (n.pc + Int64.ofNat 4) σ⟩ c') :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s a.toDir 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨m', hex, hA', hD'⟩ := exec_ai hok hR hal hlo hhi hc hreg hA
  have hl : labA s = (_root_.Executable.labels exe).label := by
    funext L; show (_root_.Executable.labels s.exe).label L = _; rw [he]
  rw [hl, hpc] at hex
  rw [hpc] at hA'
  obtain ⟨c', hr, hL⟩ := hedge σ c hJ
  refine .silent _ c' hex hr ?_
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA' (hF _ _ hD hD')⟩
  · exact .inr ⟨y, hy.at he hn hdc hA' (hF _ _ hD hD')⟩

end Fn

/-! ## The parser's forms -/

section Parse

open Kraken.AArch64.Parser

/-- `ldopDir` and `strDir` are what Kraken's parser makes of scc's text. -/
example : parseAArch64("ldaddal x9, x11, [x10]
str x9, [x10]") = [ldopDir .ADD .acqRel .X9 .X11 .X10, strDir .X9 .X10 0] := by
  decide

end Parse

end Spike.Lib.A64.Flow
