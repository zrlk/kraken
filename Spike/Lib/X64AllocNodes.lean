/-
**The allocator's memory instructions as nodes of a function** (x64): the
x64 twin of `Spike/Lib/A64AllocNodes.lean`, so far its exchange nodes.

- **an exchange's load and store** `movq k(%b), %r` / `movq %r, k(%b)`
  (`holdLd_nd`, `xchgSt_nd`, through `Out.holdLoad` / `Out.xchgStore`; not
  the allocator's, but the same shapes, e.g. scc's `xchg` on a buffer
  element, `.Lwc_rodata.x13` in hello1): the load holds the word the source
  may read, the store takes the source's exchange step and ends the hold.

- **the heap counter's add** `lock xaddq %r, k(%b)` (`ctr_nd`, through
  `Out.ctrRmw`): `k(%b)` is the counter's address (`ms.ctr`, owned by the
  runtime, mapped, outside the thread's private memory), `%r` the buffer's
  units; for every old value the runtime memory may hold there within the
  arena's cells, the state after it (`%r` the old value, its offset
  forgotten, the flags any value) lands at a node with the control holding
  the counter and the old count;
- **the allocation's last instruction** (`alloc_nd`, through `Out.alloc`):
  a covered instruction (the `ret`) at which the source takes its `newBuf`
  step, binding the buffer at the base the code computed; for a fresh
  label the state after it is one the allocation continues in (`ms.xa`).

The header store is `rtst_nd` (`Spike/Lib/X64RtNodes.lean`). `ctrLoc`,
`holdCtr` and `allocCtl` are `Spike/Lib/A64AllocNodes.lean`'s, for x64.

Kraken's rows: `exec_load_agrees`, `exec_store_agrees`
(`Kraken/Promising/Lower/EventsX64.lean`) and `exec_xaddG_agrees`
(`Kraken/Promising/Lower/EventsX64W.lean`).
-/
import Spike.Lib.X64RtNodes

namespace Spike.Lib.X64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem (ValRep)

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

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-! ## An exchange's load -/

/-- **A node at an exchange's plain load** `movq k(%b), %r`: from every
state of the invariant the address is unmapped in `dmem`; the source is at an exchange site
(`XchgSite`) of the word at `sa`, which the address represents, no hold
pending; for every value read and every word the source may read that
represents it, the state after the load (`%r` the value, its offset
forgotten) lands at a node with the control holding the address and the
word. Its states lie in `W`, and no outside move `K` moves them (`hW`). -/
theorem holdLd_ndW {W : Frag isa} {K : State → State → Prop} {n : ND} {b r : Reg64} {k : Int64} {z : Nat}
    (hr : r ≠ .rsp) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(ldDir b k r, z)])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none ∧
      ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
        XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) (bAddr σ.regs b k).toNat ∧ c.hold = none ∧
        ∀ (w : Val) (w' : TermRun.Word), ms.rd w' → ValRep lbl w'.val (w.setWidth 64).toNat →
          Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill r, ownStep r (w.setWidth 64) σ⟩
            { c with hold := some ((bAddr σ.regs b k).toNat, w') }) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (ldDir b k r) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨hdm, x, sa, u, v, e, hx, hv, hh, hL⟩ := hedge _ σ c hA hD hJ
  have ha' : eaddr s z (mB b k) = bAddr σ.regs b k := (eaddr_mB s z b k).trans (by rw [hA.regs]; rfl)
  have hex := exec_load_agrees hc ha' hdm (agrees_of_decls hdc _ _)
  refine .holdLoad _ _ _ x sa u v e hex hx hv hh fun w w' hw hrep => ?_
  exact land_own (flm := s.st.1.status) (fla := σ.status) hA.status hr hF he hn hdc hpc hA hD (hL w w' hw hrep)

/-- **`holdLd_ndW` inside the trivial predicate**, with no outside moves. -/
theorem holdLd_nd {n : ND} {b r : Reg64} {k : Int64} {z : Nat} (hr : r ≠ .rsp) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(ldDir b k r, z)])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none ∧
      ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
        XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) (bAddr σ.regs b k).toNat ∧ c.hold = none ∧
        ∀ (w : Val) (w' : TermRun.Word), ms.rd w' → ValRep lbl w'.val (w.setWidth 64).toNat →
          Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill r, ownStep r (w.setWidth 64) σ⟩
            { c with hold := some ((bAddr σ.regs b k).toNat, w') }) :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (holdLd_ndW (W := fun _ _ => True) (K := fun _ _ => False) (hW := fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    hr hF hcode hedge).toSeg

/-! ## An exchange's store -/

/-- **A node at an exchange's plain store** `movq %r, k(%b)`: from every
state of the invariant the address is unmapped in `dmem`; the source is at an exchange site
(`XchgSite`) of the word at `sa`, which the address represents, holding
the address and the word `wold`, and `%r` represents the exchanged value's
word; the abstract state is unchanged and lands at a node with `x` bound to
`wold` and the hold ended. Its states lie in `W`, and no outside move `K`
moves them (`hW`). -/
theorem xchgSt_ndW {W : Frag isa} {K : State → State → Prop} {n : ND} {b r : Reg64} {k : Int64} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(stDir b k r, z)])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none ∧
      ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
        (wv wold : TermRun.Word),
        XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) (bAddr σ.regs b k).toNat ∧
        c.hold = some ((bAddr σ.regs b k).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
        ValRep lbl wv.val ((σ.regs.get64 r).setWidth 128).toNat ∧
        Lands N E ⟨n.pc + Int64.ofNat z, n.o, σ⟩ ⟨e, (x, u, [wold]) :: c.env, none⟩) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (stDir b k r) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨hdm, x, sa, u, v, e, tv, wv, wold, hx, hrep, hh, hev, hV, hL⟩ := hedge _ σ c hA hD hJ
  have ha : eaddr s z (mB b k) = bAddr σ.regs b k := (eaddr_mB s z b k).trans (by rw [hA.regs]; rfl)
  have hex := exec_store_agrees hc ha (by exact hdm) (agrees_of_decls hdc _ _)
  rw [Reg64s.get_low64, hA.regs] at hex
  refine .xchgStore _ _ _ _ x sa u v e tv wv wold hex hx hrep hh hev hV ?_
  have hs1 : after s z s.st.1 = { s with st := (s.st.1, n.pc + Int64.ofNat z) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA hD⟩
  · exact .inr ⟨y, hy.at he hn hdc hA hD⟩

/-- **`xchgSt_ndW` inside the trivial predicate**, with no outside moves. -/
theorem xchgSt_nd {n : ND} {b r : Reg64} {k : Int64} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(stDir b k r, z)])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none ∧
      ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
        (wv wold : TermRun.Word),
        XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) (bAddr σ.regs b k).toNat ∧
        c.hold = some ((bAddr σ.regs b k).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
        ValRep lbl wv.val ((σ.regs.get64 r).setWidth 128).toNat ∧
        Lands N E ⟨n.pc + Int64.ofNat z, n.o, σ⟩ ⟨e, (x, u, [wold]) :: c.env, none⟩) :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (xchgSt_ndW (W := fun _ _ => True) (K := fun _ _ => False) (hW := fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    hcode hedge).toSeg

/-! ## The heap counter's add -/

/-- **A node at the heap counter's add** `lock xaddq %r, k(%b)`: from every
state of the invariant `k(%b)` is the counter's address, owned by the
runtime and mapped for writing (`ms.mp`), outside the thread's private
memory; the source is at a buffer allocation of `nn` elements, no hold
pending, and `%r` holds the buffer's units; for every old value the runtime
memory may hold at the counter within the arena's cells, the new value may
be held there too, and the state after it (`%r` the old value, the flags any
value) lands at a node with the control holding the old count. Its states
lie in `W`, and no outside move `K` moves them (`hW`). -/
theorem ctr_ndW {W : Frag isa} {K : State → State → Prop} {n : ND} {b r : Reg64} {k : Int64} {z : Nat}
    (hr : r ≠ .rsp) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(xaddDir b k r, z)])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      bAddr σ.regs b k = BitVec.ofNat 64 ms.ctr ∧ ms.rt (BitVec.ofNat 64 ms.ctr).toNat ∧
      ms.mp (ctrLoc ms) true ∧ Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none ∧
      ∃ (x : String) (a : CoreTerm.At) (τ : Ty) (e : Expr) (ta : Ty) (ws : List TermRun.Word) (nn : Nat),
        c.term = .let_ x (.newBuf a τ) e ∧ TermRun.evalAt c.env a = some (ta, ws) ∧ TermRun.numOf ws = some nn ∧
        c.hold = none ∧ σ.regs.get64 r = BitVec.ofNat 64 (ms.units nn τ) ∧
        ∀ old : Val, ms.G (ctrLoc ms) old → (old.setWidth 64).toNat ≤ ms.cells →
          ms.G (ctrLoc ms) ((old.setWidth 64 + BitVec.ofNat 64 (ms.units nn τ)).setWidth 128) ∧
          ∀ fl, Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill r, { ownStep r (old.setWidth 64) σ with status := fl }⟩
            (holdCtr ms c (old.setWidth 64))) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (xaddDir b k r) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨ha, hrt, hmp, hdm, x, a, τ, e, ta, ws, nn, ht, hev, hnn, hh, hru, hX⟩ := hedge _ σ c hA hD hJ
  have ha' : eaddr s z (mB b k) = BitVec.ofNat 64 ms.ctr :=
    (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha)
  have hex := exec_xaddG_agrees (w := .W64) hc ha' hdm (agrees_of_decls hdc _ _)
  rw [Reg64s.get_low64] at hex
  refine .ctrRmw .acqRel _ _ x a τ e ta ws nn hex hrt hmp ht hev hnn hh (fun old => ?_) fun old hG _ hle => ?_
  · simp only [hA.regs, hru]
  obtain ⟨hG', hL⟩ := hX old hG hle
  exact ⟨hG', land_own rfl hr hF he hn hdc hpc hA hD (hL _)⟩

/-- **`ctr_ndW` inside the trivial predicate**, with no outside moves. -/
theorem ctr_nd {n : ND} {b r : Reg64} {k : Int64} {z : Nat} (hr : r ≠ .rsp) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(xaddDir b k r, z)])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      bAddr σ.regs b k = BitVec.ofNat 64 ms.ctr ∧ ms.rt (BitVec.ofNat 64 ms.ctr).toNat ∧
      ms.mp (ctrLoc ms) true ∧ Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none ∧
      ∃ (x : String) (a : CoreTerm.At) (τ : Ty) (e : Expr) (ta : Ty) (ws : List TermRun.Word) (nn : Nat),
        c.term = .let_ x (.newBuf a τ) e ∧ TermRun.evalAt c.env a = some (ta, ws) ∧ TermRun.numOf ws = some nn ∧
        c.hold = none ∧ σ.regs.get64 r = BitVec.ofNat 64 (ms.units nn τ) ∧
        ∀ old : Val, ms.G (ctrLoc ms) old → (old.setWidth 64).toNat ≤ ms.cells →
          ms.G (ctrLoc ms) ((old.setWidth 64 + BitVec.ofNat 64 (ms.units nn τ)).setWidth 128) ∧
          ∀ fl, Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill r, { ownStep r (old.setWidth 64) σ with status := fl }⟩
            (holdCtr ms c (old.setWidth 64))) :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (ctr_ndW (W := fun _ _ => True) (K := fun _ _ => False) (hW := fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    hr hF hcode hedge).toSeg

/-! ## The allocation's last instruction -/

/-- **A node at a buffer allocation's last instruction**, a covered
instruction `a` of `z` bytes (inside the region `[lo, hi)`): from every
state of the invariant the source is at `let x = newBuf a' τ in e` of `kk`
elements, holding the counter's old count `old` (`ctr_nd`), and the code
computed the base `A = ms.heap + 16·old + ms.off kk τ`; for every fresh
label `l` (`lbl l = none`), the state after `a` hits the node
`Ea l A (kk·w)` (`w` the element type's words) with `x` bound to `l`'s
locative (`allocCtl`), and every state at that node is one the allocation
continues in (`hxa`, `ms.xa`). The node lands nowhere in `Next`: the
allocation's continuation is `ms.xa` (see `Out.alloc`). Its states lie in
`W`, and no outside move `K` moves them (`hW`). -/
theorem alloc_ndW {W : Frag isa} {K : State → State → Prop} {n : ND} {lo hi : Int} {a : AI} {z : Nat}
    (Ea : WeakMem.AllocLabel → Nat → Nat → ND)
    (hok : a.ok lo hi n.o = true)
    (hreg : ∀ w op, a = .reg w op → RegOnly op = true) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(a.toDir, z)])
    (hxa : ∀ l b w s c, lbl l = none → At exe endPc R F (Ea l b w) s c → ms.xa l b w s c)
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ σ c, n.J σ c →
      ∃ (A : BitVec 64) (x : String) (a' : CoreTerm.At) (τ : Ty) (e : Expr) (ta : Ty) (ws : List TermRun.Word)
        (kk : Nat) (wold : TermRun.Word) (old : Nat) (us : List TermRun.Acc),
        c.term = .let_ x (.newBuf a' τ) e ∧ TermRun.evalAt c.env a' = some (ta, ws) ∧
        TermRun.numOf ws = some kk ∧ c.hold = some (ms.ctr, wold) ∧ TermRun.numOf [wold] = some old ∧
        A.toNat = ms.heap + 16 * old + ms.off kk τ ∧ TermRun.accs (TermRun.close [] τ) = some us ∧
        ∀ (l : WeakMem.AllocLabel) (ini : Nat), lbl l = none →
          Hit (Ea l A.toNat (kk * TermRun.nWords us))
            ⟨a.tgt (_root_.Executable.labels exe).label n.o (n.pc + Int64.ofNat z) σ, a.so n.o,
              a.step n.o (n.pc + Int64.ofNat z) σ⟩ (allocCtl c x τ e kk l ini)) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s a.toDir z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨m', hex, hA', hD'⟩ := exec_ai hok hR hlo hhi hc hreg hA
  have hl : labelAddr s = (_root_.Executable.labels exe).label := by
    funext L; show (_root_.Executable.labels s.exe).label L = _; rw [he]
  rw [hl, hpc] at hex
  rw [hpc] at hA'
  obtain ⟨A, x, a', τ, e, ta, ws, kk, wold, old, us, ht, hev, hkk, hh, hold, hAeq, hus, hX⟩ := hedge σ c hJ
  refine .alloc _ A x a' τ e ta ws kk wold old us hex ht hev hkk hh hold hAeq hus fun l ini hl => ?_
  exact hxa _ _ _ _ _ hl ((hX l ini hl).at he hn hdc hA' (hF _ _ hD hD'))

/-- **`alloc_ndW` inside the trivial predicate**, with no outside moves. -/
theorem alloc_nd {n : ND} {lo hi : Int} {a : AI} {z : Nat} (Ea : WeakMem.AllocLabel → Nat → Nat → ND)
    (hok : a.ok lo hi n.o = true)
    (hreg : ∀ w op, a = .reg w op → RegOnly op = true) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(a.toDir, z)])
    (hxa : ∀ l b w s c, lbl l = none → At exe endPc R F (Ea l b w) s c → ms.xa l b w s c)
    (hedge : ∀ σ c, n.J σ c →
      ∃ (A : BitVec 64) (x : String) (a' : CoreTerm.At) (τ : Ty) (e : Expr) (ta : Ty) (ws : List TermRun.Word)
        (kk : Nat) (wold : TermRun.Word) (old : Nat) (us : List TermRun.Acc),
        c.term = .let_ x (.newBuf a' τ) e ∧ TermRun.evalAt c.env a' = some (ta, ws) ∧
        TermRun.numOf ws = some kk ∧ c.hold = some (ms.ctr, wold) ∧ TermRun.numOf [wold] = some old ∧
        A.toNat = ms.heap + 16 * old + ms.off kk τ ∧ TermRun.accs (TermRun.close [] τ) = some us ∧
        ∀ (l : WeakMem.AllocLabel) (ini : Nat), lbl l = none →
          Hit (Ea l A.toNat (kk * TermRun.nWords us))
            ⟨a.tgt (_root_.Executable.labels exe).label n.o (n.pc + Int64.ofNat z) σ, a.so n.o,
              a.step n.o (n.pc + Int64.ofNat z) σ⟩ (allocCtl c x τ e kk l ini)) :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (alloc_ndW (W := fun _ _ => True) (K := fun _ _ => False) Ea hok hreg hF hR hlo hhi hcode hxa
    (fun _ _ _ => ⟨trivial, fun _ h => h⟩) hedge).toSeg

end Fn

/-! ## The parser's forms -/

section Parse

open Kraken.X64.Parser

/-- The counter's add and the `ret` are what Kraken's parser makes of scc's text. -/
example : parse("lock xaddq %rax, (%rcx)
ret") = [xaddDir .rcx 0 .rax, AI.ret.toDir] := by
  decide

end Parse

end Spike.Lib.X64
