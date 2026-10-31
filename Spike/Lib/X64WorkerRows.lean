/-
**The worker's thread rows on x86-64** (the x64 twin of
`Spike/Lib/A64WorkerRows.lean`): the target side of the worker's `store rel
c 1`, `unpark j` and the thread's exit, over the thread rows of
`Spike/Lib/SegThr.lean` (`OutT`, `SegT`), and `scc_rt_unpark` as one
segment. The listing is wake.w's (`SccCode.wakeText`,
`Spike/Lib/X64WakeCode.lean`); `scc_rt_unpark` is runtime code, the same
in every program.

- `fn_segT`: `fn_seg` over `SegT`.
- `relStore_nd`: **the node at the source's release store** `movq %r,
  k(%b)` (`Out.store`; under TSO a plain store is a release store):
  `k(%b)` is the address `A` of the source's word, `%r` a value
  representing the stored word.
- `unpkXchg_nd`: **the node at the worker's exchange on the named thread's
  permit word** (`OutT.unpk`): the source takes its `unpark` here, at the
  worker's own `xchgq`, and nowhere else.
- `syscallCall_exit`, `syscallCall_futexWake`: the decoded calls.
- `texit_nd`: **the node at the thread's `exit`** (`OutT.texit`), the
  source at `ret a`.
- `call_ndT`: `call_nd` over `SegT` (a callee with the thread rows), the
  callee's specification asked only for frame conditions giving the
  caller's.
- `Unpark.seg_unpark`: `scc_rt_unpark` as one `SegT` segment.

`wc_worker`'s and `scc_rt_thr_worker`'s rows (A64's `WkTail`, `ThrTail`,
there on hello.w's listing) are on wake.w's listing in
`Spike/Lib/X64WakeWorker.lean`.

**Unlike AArch64** (forced by the x64 shape): the instructions are
byte-sized cells (`(Directive × Nat)` blocks, byte offsets after labels);
the frames are `%rbp` frames whose regions end at `8` (the return address
at offset `0` of the entry `%rsp`, `Spike/Lib/X64WakeFrame.lean`); there is
no alignment (`hal`) premise; the store is a plain `movq` (TSO: no
`stlr`), the exchange `xchgq` (A64 `swpal`); the system call is `syscall`
with the number in `%rax` (`exit` 60, `futex` 202); a callee's entry
offsets are `⟨0, []⟩` and its return pops the return address (offsets
`⟨8, []⟩`), so `call_ndT` is `X64Call.call_nd`'s (`e0`, `hi'`, the vector
registers) over `SegT`.
-/
import Spike.Lib.X64Park
import Spike.Lib.X64Dead
import Spike.Lib.X64Call
import Spike.Lib.X64RtNodes
import Spike.Lib.SegThr

namespace Spike.Lib.X64.Flow.Worker

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Scc.Sem (ValRep)
open Spike.Lib.X64.Flow.Ret0 (StOk LdOk)

set_option linter.unusedSimpArgs false

/-! ## Nodes with the thread rows -/

section Nodes

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A whole function with the thread rows**: `fn_seg` over `SegT`. -/
theorem fn_segT (h : ∀ i, SegT p lbl ms (At exe endPc R F (N i)) (Next exe endPc R F N E)) (i0 : ι) :
    SegT p lbl ms (At exe endPc R F (N i0)) (fun s c => ∃ x, At exe endPc R F (E x) s c) :=
  (SegT.cfg (fun i => At exe endPc R F (N i)) h).mono_pre fun _ _ h => ⟨i0, h⟩

/-- **A node at the source's release store** `movq %r, k(%b)`: `k(%b)` is
`A`, the address of the source's word at its `let x = store rel a b in e`
(`ValRep`, an untagged locative), `A` not private memory under `F`
(`hdm`), `%r` a value representing `b`'s word; the abstract state is
unchanged and the source takes its store. -/
theorem relStore_nd {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {A : BitVec 64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(stDir b k r, z)])
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      bAddr σ.regs b k = A ∧
      ∃ x a bb e ty tb w wb, c.term = .let_ x (.store true a bb none) e ∧
        TermRun.evalAt c.env a = some (ty, [w]) ∧ ValRep lbl w.val A.toNat ∧ (∃ sa, w.val = .loc sa 0) ∧
        TermRun.evalAt c.env bb = some (tb, [wb]) ∧ ValRep lbl wb.val (σ.regs.get64 r).toNat ∧
        Lands N E ⟨n.pc + Int64.ofNat z, n.o, σ⟩ ⟨e, (x, .unit, []) :: c.env, none⟩) :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine Seg.step fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (stDir b k r) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨ha, x, a, bb, e, ty, tb, w, wb, ht, hev, hv, htag, hevb, hvb, hL⟩ := hedge _ σ c hA hD hJ
  have ha' : eaddr s z (mB b k) = A := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha)
  have hex := exec_store_agrees hc ha' (hdm _ hD) (agrees_of_decls hdc _ _)
  rw [Reg64s.get_low64, hA.regs] at hex
  refine .store .plain A _ _ x a bb e ty tb w wb hex ht hev hv hevb
    (by rw [toNat_setWidth128]; exact hvb) ?_ htag
  have hs1 : after s z s.st.1 = { s with st := (s.st.1, n.pc + Int64.ofNat z) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA hD⟩
  · exact .inr ⟨y, hy.at he hn hdc hA hD⟩

/-- `(1 : BitVec 64)` widened is the RMW's value `1`. -/
theorem one_setWidth : ((1#64).setWidth 128 : BitVec 128) = 1 := by decide

/-- **The node at the worker's exchange on the named thread's permit
word** `xchgq %r, k(%b)`: `k(%b)` is `A = B + 16`, the permit word of the
thread whose tid word `jw` (representing `B`) the source's `let x = unpark a
in e` names, no hold pending; `%r` holds `1`, a value runtime memory may
hold there (`StOk`); for every old value the state after it (`%r := old`)
lands at a node with the source's `unpark` taken (`x` bound to `()`). The
row is `OutT.unpk`. -/
theorem unpkXchg_nd {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {A B : BitVec 64} (hr : r ≠ .rsp)
    (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(xchgDir b k r, z)])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      bAddr σ.regs b k = A ∧ σ.regs.get64 r = 1#64 ∧ StOk ms F A 1#64 ∧ A = B + 16#64 ∧
      ∃ x a e ty jw, c.term = .let_ x (.ext .unpark a) e ∧ c.hold = none ∧
        TermRun.evalAt c.env a = some (ty, [jw]) ∧ ValRep lbl jw.val B.toNat ∧
        ∀ v : BitVec 64, Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill r, ownStep r v σ⟩
          ⟨e, (x, ExtName.unpark.sig.2, []) :: c.env, none⟩) :
    SegT p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegT.step fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (xchgDir b k r) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨ha, h1, hS, hAB, x, a, e, ty, jw, ht, hh, hev, hv, hL⟩ := hedge _ σ c hA hD hJ
  have ha' : eaddr s z (mB b k) = A := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha)
  have hex := exec_xchgG_agrees (w := .W64) hc ha' (hS.unmapped _ hD) (agrees_of_decls hdc _ _)
  rw [Reg64s.get_low64] at hex
  refine .unpk .acqRel A B _ _ x a e ty jw hex hS.rt hS.mp (fun _ => by rw [hA.regs, h1, one_setWidth])
    ht hh hev hv hAB fun old _ _ => ⟨?_, ?_⟩
  · have := hS.G
    rwa [one_setWidth] at this
  · exact land_own (flm := s.st.1.status) (fla := σ.status) hA.status hr hF he hn hdc hpc hA hD (hL _)

/-- **`%rax = 60` decodes to the thread's `exit`.** -/
theorem syscallCall_exit {r : Reg64s} (h : r.rax.toNat = 60) : syscallCall r = some .exit := by
  simp [syscallCall, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.x64, h]

/-- **The futex wake the kernel model decodes**: `%rax = 202`, `%rsi =
FUTEX_WAKE_PRIVATE`, a 4-aligned address in `%rdi`, waking `%rdx` threads. -/
theorem syscallCall_futexWake {r : Reg64s} (ha : r.rax.toNat = 202) (h1 : r.rsi.toNat = 129)
    (h0 : r.rdi.toNat % 4 = 0) : syscallCall r = some (.futexWake r.rdx.toNat) := by
  simp [syscallCall, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.x64, Scc.Sem.Kernel.futexWaitPrivate,
    Scc.Sem.Kernel.futexWakePrivate, ha, h1, h0]

/-- **A node at the thread's `exit`**: `syscall` with `%rax = 60` in every
state of the invariant, the source at `ret a`, under the kernel model, is a
segment with the thread rows to any exit (`OutT.texit`: the thread ends). -/
theorem texit_nd {n : ND} {Q : Frag isa} {z : Nat} (hK : ms.K = some Scc.Sem.X64.abi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(op64 .syscall, z)])
    (hx : ∀ σ c, n.J σ c → σ.regs.rax.toNat = 60 ∧ ∃ a, c.term = .ret a) :
    SegT p lbl ms (At exe endPc R F n) Q := by
  refine SegT.step fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (op64 .syscall) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨hax, a, ht⟩ := hx σ c hJ
  have hd : Scc.Sem.Kernel.decode Scc.Sem.Kernel.Nrs.x64 (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) =
      some .exit := by
    rw [← syscallCall_exit hax, syscallCall, ← hA.regs]; rfl
  exact .texit _ a hK (Scc.Sem.X64.atSyscall_of_cellAt hc) hd ht

/-- **A call node with the thread rows** (`call_nd` over `SegT`): the
callee's specification, a `SegT` segment for every region holding its frame
`[lo', hi')` (entry offsets `⟨e0, []⟩`) and every frame condition giving the
caller's `F`, is a given node of the caller from the call node `nC` (the
return address pushed) to the caller's nodes. The proof is `call_nd`'s. -/
theorem call_ndT {nC : ND} {γ : Type _} {κ' : Sort _} {e0 lo' hi' : Int} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hR : R.OK) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp - e0 + lo') (hlo0 : lo' ≤ 0) (hkb : nC.o.sp - e0 < R.hi)
    (hhi : nC.o.sp - e0 + hi' ≤ R.hi) (hk8 : (nC.o.sp - e0) % 8 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ lo' → hi' ≤ R'.hi → FStable R' F' →
      (∀ m, F' m → F m) → ∀ g,
        SegT p lbl ms (At exe endPc R' F' (Ne g)) (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c))
    (hNe : ∀ g, (Ne g).o = ⟨e0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g, (Ne g).pc = nC.pc ∧ (Ne g).J (enter (nC.o.sp - e0) σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), nC.J σC c → (Ne g).J (enter (nC.o.sp - e0) σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.zmms = σx.zmms → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp - e0 + (Ex g x).o.sp, []⟩, σR⟩ c') :
    SegT p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) := by
  -- the callee's region and its ghost-indexed frame condition
  let kb := nC.o.sp - e0
  let R' := R.callee kb lo' hi'
  have hR' : R'.OK := Region.callee_ok hR hlo hlo0 hkb hhi
  have hFR' : FStable R' F := FStable.callee hR hlo hlo0 hkb hhi hF
  -- the ghost: the machine data and abstract state at the call, the caller's control, the callee's
  -- parameters; the facts about it ride in the frame condition (constant, so stable)
  let F' : MachineData × AS × Ctl × γ → MachineData → Prop := fun G m =>
    F m ∧ DFrame R' G.1 m ∧ Abs R nC.o G.1 G.2.1 ∧ nC.J G.2.1 G.2.2.1 ∧ (Ne G.2.2.2).J (enter kb G.2.1) G.2.2.1
  have hF' : ∀ G, FStable R' (F' G) := fun G m m' hm hd =>
    ⟨hFR' m m' hm.1 hd, hm.2.1.trans hd, hm.2.2⟩
  refine SegT.mono_pre (P := fun s c => ∃ G, At exe endPc R' (F' G) (Ne G.2.2.2) s c)
    (SegT.exists_pre fun G => ?_) ?_
  · -- the callee's segment, its exits landing at the caller's nodes
    refine (hcallee R' (F' G) hR' (Int.le_refl _) (Int.le_refl _) (hF' G) (fun _ h => h.1) G.2.2.2).mono_post ?_
    rintro s c ⟨x, he, hn, hdc, hpc, σx, hAx, ⟨hD, hDF, hAC, hJC, hJE⟩, hJx⟩
    obtain ⟨mC, σC, cC, g⟩ := G
    simp only at hDF hAC hJC hJE hJx hAx hpc
    have hAR : Abs R ⟨kb + (Ex g x).o.sp, []⟩ s.st.1 (leave R' kb σC σx) := by
      refine ⟨hAx.regs, hAx.zmms, hAx.status, ?_, fun k hk => ?_⟩
      · intro r k' hr
        obtain ⟨rfl, rfl⟩ := SO.get_sp_only hr
        have := hAx.so .rsp (Ex g x).o.sp (by simp [SO.get])
        simp only [leave] at this ⊢
        rw [this, Region.callee_addr]
      · by_cases hin : R'.Off (k - kb)
        · obtain ⟨j, hj, hv⟩ := hAx.slot _ hin
          refine ⟨j, ?_, ?_⟩
          · rw [Region.callee_addr, show kb + (k - kb) = k by omega] at hj; exact hj
          · simp only [leave]; rw [ite_eq_left hin]; exact hv
        · obtain ⟨j, hj, hv⟩ := hAC.slot k hk
          refine ⟨j, ?_, ?_⟩
          · rw [hDF _ (R.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkb hk8 hl8 hh8 hk hin)]
            exact hj
          · simp only [leave]; rw [ite_eq_right hin]; exact hv
    have hL := hret g x σC cC σx c (leave R' kb σC σx) hJC hJE hJx rfl rfl rfl
      (fun k _ hn => by simp only [leave]; exact ite_eq_right hn)
    have hs : s = { s with st := (s.st.1, (Ex g x).pc) } := by rw [← hpc]; rfl
    rw [hs]
    rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
    · exact .inl ⟨j, hj.at he hn hdc hAR hD⟩
    · exact .inr ⟨y, hy.at he hn hdc hAR hD⟩
  · -- the caller's state at the call, seen from the callee
    rintro s c ⟨he, hn, hdc, hpc, σC, hA, hD, hJ⟩
    obtain ⟨g, hgpc, hgJ⟩ := hent σC c hJ
    refine ⟨(s.st.1, σC, c, g), he, hn, hdc, by rw [hpc, hgpc], enter kb σC, ?_,
      ⟨hD, DFrame.refl _ _, hA, hJ, hgJ⟩, hgJ⟩
    rw [hNe]
    refine ⟨hA.regs, hA.zmms, hA.status, ?_, fun k hk => ?_⟩
    · intro r k' hr
      obtain ⟨rfl, rfl⟩ := SO.get_sp_only hr
      have := hA.so .rsp nC.o.sp (by simp [SO.get])
      simp only [enter] at this ⊢
      rw [this, Region.callee_addr]; congr 1; omega
    · obtain ⟨j, hj, hv⟩ := hA.slot _ (Region.callee_off hlo hhi hk8 hk)
      exact ⟨j, by rw [Region.callee_addr]; exact hj, hv⟩

end Nodes

/-! ## `scc_rt_unpark`

    scc_rt_unpark(j = %rdi):
      prologue (push %rbp; frame of 32; j at -8(%rbp))
      .entry: old = xchg(1, [j + 16])             -- set j's permit: the source's unpark
              if old = 0 goto .wake else goto .done
      .wake:  futex(j + 16, FUTEX_WAKE_PRIVATE, 1)  -- syscall, %rax = 202
              epilogue; ret
      .done:  epilogue; ret

The region is the frame, offsets `[-40, 8)` from the `%rsp` at entry (the
return address at `0`, the saved `%rbp` at `-8`, `j` at `-16`;
`Spike/Lib/X64WakeFrame.lean`'s `unparkD`). Ghosts: the source controls
`c0` (at `let x = unpark a in e`, `a`'s word representing the tid `B`) and
`c1` (past it), the caller's `%rbp` `rbp0`, the return address `ra`, the
thread pointer `tp`. Entry (`.e`): `%rdi = B`, the source at `c0`. Return
(exit `.ret`, offsets `⟨8, []⟩`): the source at `c1`. The source takes its
`unpark` at the `xchgq` (`unpkXchg_nd`) and stutters elsewhere; the permit
word's facts for `1` (`hS`) and its alignment (`htp4`) are hypotheses. -/

namespace Unpark

/-! ### The blocks (generated) -/

def b0 : List (Directive × Nat) := (parse("pushq %rbp
movq %rsp, %rbp
subq $32, %rsp
movq %rdi, -8(%rbp)")).zip [1, 3, 4, 4]
def b1 : List (Directive × Nat) := (parse("movq -8(%rbp), %rcx
movq $1, %rax")).zip [4, 7]
def b2 : List (Directive × Nat) := (parse("movq %rax, -16(%rbp)
movq -16(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
je .Lscc_rt_unpark.wake")).zip [4, 4, 7, 3, 2]
def b3 : List (Directive × Nat) := (parse("jmp .Lscc_rt_unpark.done")).zip [2]
def b4 : List (Directive × Nat) := (parse("movq -8(%rbp), %rax
movq $16, %rcx
addq %rcx, %rax
movq %rax, -24(%rbp)
movq -24(%rbp), %rdi
movq $129, %rsi
movq $1, %rdx
movq $0, %r10
movq $0, %r8
movq $0, %r9
movl $202, %eax")).zip [4, 7, 3, 4, 4, 7, 7, 7, 7, 7, 5]
def b5 : List (Directive × Nat) := (parse("movq %rax, -32(%rbp)
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 3, 1, 1]
def b6 : List (Directive × Nat) := (parse("movq %rbp, %rsp
popq %rbp
ret")).zip [3, 1, 1]

/-- The function's offsets inside the frame: `%rsp` at the frame's base,
`%rbp` at the saved `%rbp`. -/
abbrev oI : SO := ⟨-40, [(.rbp, -8)]⟩
/-- The offsets at entry. -/
abbrev oE : SO := ⟨0, []⟩
/-- The offsets after the return. -/
abbrev oR : SO := ⟨8, []⟩

block_spec b0 (-40) 8 oE b0
block_spec b1 (-40) 8 oI b1
block_spec b2 (-40) 8 oI b2
block_spec b3 (-40) 8 oI b3
block_spec b4 (-40) 8 oI b4
block_spec b5 (-40) 8 oI b5
block_spec b6 (-40) 8 oI b6

/-! ### The graph -/

/-- The internal nodes: one per block, the exchange and the system call. -/
inductive PN where
  | e | n1 | xchg | n2 | n3 | wake | sys | n5 | done

/-- The exits. -/
inductive PX where
  | ret

section Spec

variable (lab : Label → Int64) (c0 c1 : Ctl) (B rbp0 ra tp : BitVec 64)

/-- Inside the frame, the source at `c'`: the caller's `%rbp`, the return
address and `B` in their cells, the thread pointer `tp`. -/
def JI (c' : Ctl) (σ : AS) (c : Ctl) : Prop :=
  c = c' ∧ σ.slot (-8) = rbp0 ∧ σ.slot 0 = ra ∧ σ.slot (-16) = B ∧ σ.regs.fsBase.toBitVec = tp

/-- At the exchange: `%rcx` the tid `B` (the permit at `16(%rcx)`), `%rax`
the new value `1`. -/
def JS (σ : AS) (c : Ctl) : Prop :=
  JI B rbp0 ra tp c0 σ c ∧ σ.regs.get64 .rcx = B ∧ σ.regs.get64 .rax = 1#64

/-- At entry. -/
def JE (σ : AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.regs.get64 .rdi = B ∧ σ.regs.rbp.toBitVec = rbp0 ∧ σ.slot 0 = ra ∧ σ.regs.fsBase.toBitVec = tp

/-- At the return. -/
def JR (σ : AS) (c : Ctl) : Prop :=
  c = c1 ∧ σ.regs.get64 .rbp = rbp0 ∧ σ.regs.fsBase.toBitVec = tp

/-- The pc of the futex wake's `syscall`. -/
abbrev pcSys : Int64 := lab ".Lscc_rt_unpark.wake" + 62

/-- **The nodes.** -/
def N : PN → ND
  | .e => ⟨lab "scc_rt_unpark", oE, JE c0 B rbp0 ra tp⟩
  | .n1 => ⟨lab ".Lscc_rt_unpark.entry", oI, JI B rbp0 ra tp c0⟩
  | .xchg => ⟨lab ".Lscc_rt_unpark.entry" + 11, oI, JS c0 B rbp0 ra tp⟩
  | .n2 => ⟨lab ".Lscc_rt_unpark.entry" + 15, oI, JI B rbp0 ra tp c1⟩
  | .n3 => ⟨lab ".Lscc_rt_unpark.entry" + 35, oI, JI B rbp0 ra tp c1⟩
  | .wake => ⟨lab ".Lscc_rt_unpark.wake", oI, JI B rbp0 ra tp c1⟩
  | .sys => ⟨pcSys lab, oI, fun σ c => JI B rbp0 ra tp c1 σ c ∧ σ.regs.get64 .rdi = B + 16#64 ∧
      σ.regs.get64 .rsi = 129#64 ∧ σ.regs.get64 .rdx = 1#64 ∧ σ.regs.get64 .rax = 202#64⟩
  | .n5 => ⟨lab ".Lscc_rt_unpark.wake" + 64, oI, JI B rbp0 ra tp c1⟩
  | .done => ⟨lab ".Lscc_rt_unpark.done", oI, JI B rbp0 ra tp c1⟩

/-- **The exit**: the return to `ra` with `%rsp` past the return address,
`%rbp` and the thread pointer as at entry, the source past its `unpark`. -/
def E : PX → ND
  | .ret => ⟨Int64.ofBitVec ra, oR, JR c1 rbp0 tp⟩

/-- **The code**: every block and single instruction at its node's pc. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  e : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 B rbp0 ra tp .e).pc b0
  n1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 B rbp0 ra tp .n1).pc b1
  xchg : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 B rbp0 ra tp .xchg).pc [(xchgDir .rcx 16 .rax, 4)]
  n2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 B rbp0 ra tp .n2).pc b2
  n3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 B rbp0 ra tp .n3).pc b3
  wake : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 B rbp0 ra tp .wake).pc b4
  sys : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 B rbp0 ra tp .sys).pc [(op64 .syscall, 2)]
  n5 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 B rbp0 ra tp .n5).pc b5
  done : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 B rbp0 ra tp .done).pc b6

/-- `scc_rt_unpark`'s code does not depend on its ghosts (its nodes' pcs
do not). -/
theorem Code.ghost {exe : _root_.Executable} {endPc : Int64} {c0 c1 c0' c1' : Ctl}
    {B rbp0 ra tp B' rbp0' ra' tp' : BitVec 64} (h : Code c0 c1 B rbp0 ra tp exe endPc) :
    Code c0' c1' B' rbp0' ra' tp' exe endPc :=
  ⟨h.e, h.n1, h.xchg, h.n2, h.n3, h.wake, h.sys, h.n5, h.done⟩

end Spec

/-! ### The proof -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 c1 : Ctl}
  {B rbp0 ra tp : BitVec 64}

set_option hygiene false in
/-- A block node: the block, its `okBlk`, its code; the edge is left. -/
local macro "node " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine (seg_nd (by simp [$b:ident]) $ok hF hR hlo hhi
    (fun s he hn => hcode.$f s he hn) fun σ c hJ => ⟨c, .refl c, ?_⟩).toT)

/-- Hitting node `j`. -/
local macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;>
    simp_all [N, JI, JS, JE, JR, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self,
      Reg64s.get64_set64_ne, KeepTP.set64_tp, ownStep, syscallStep, syscallRegs]))

/-- Hitting exit `x`. -/
local macro "exit " x:term : tactic =>
  `(tactic| (refine .inr ⟨$x, ?_, rfl, ?_⟩ <;>
    simp_all [N, E, JI, JS, JE, JR, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self,
      Reg64s.get64_set64_ne, KeepTP.set64_tp]))

/-- **`scc_rt_unpark` is one segment with the thread rows** from its entry
to its return: the source takes its `unpark` at the `xchgq` setting the
permit word `B + 16` to `1` (`OutT.unpk`, for any old value) and stutters
elsewhere; the futex wake returns `0` or `1`. -/
theorem seg_unpark (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hS : StOk ms F (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {jw : TermRun.Word}
    (ht : c0.term = .let_ x (.ext .unpark a) e) (hh : c0.hold = none)
    (hev : TermRun.evalAt c0.env a = some (ty, [jw])) (hv : ValRep lbl jw.val B.toNat)
    (hc1 : c1 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c0.env, none⟩)
    (hcode : Code c0 c1 B rbp0 ra tp exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".Lscc_rt_unpark.entry" =
      (_root_.Executable.labels exe).label "scc_rt_unpark" + 12) :
    SegT p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 B rbp0 ra tp .e))
      (fun s c => ∃ x, At exe endPc R F (E c1 rbp0 ra tp x) s c) := by
  refine fn_segT (N := N _ c0 c1 B rbp0 ra tp) (E := E c1 rbp0 ra tp) (fun i => ?_) PN.e
  cases i
  case e => node b0 b0_ok e; rw [N, b0_run]; hit PN.n1
  case n1 => node b1 b1_ok n1; rw [N, b1_run]; hit PN.xchg
  case xchg =>
    refine unpkXchg_nd (A := B + 16#64) (B := B) (by decide) hF (fun s he hn => hcode.xchg s he hn)
      fun m σ c _ _ hJ => ?_
    obtain ⟨⟨rfl, hJ⟩, hc, ha⟩ := hJ
    refine ⟨by rw [bAddr, hc]; rfl, ha, hS, rfl, x, a, e, ty, jw, ht, hh, hev, hv, fun v => ?_⟩
    rw [← hc1]
    hit PN.n2
  case n2 =>
    node b2 b2_ok n2; rw [N, b2_run]
    split
    · hit PN.wake
    · hit PN.n3
  case n3 => node b3 b3_ok n3; rw [N, b3_run]; hit PN.done
  case wake =>
    node b4 b4_ok wake; rw [N, b4_run]
    have hc : (16#64 : BitVec 64) + B = B + 16#64 := BitVec.add_comm _ _
    hit PN.sys
  case sys =>
    have hcall : ∀ σ c, (N (_root_.Executable.labels exe).label c0 c1 B rbp0 ra tp .sys).J σ c →
        syscallCall σ.regs = some (.futexWake 1) := by
      rintro σ c ⟨-, h0, h1, h2, h8⟩
      have hw := syscallCall_futexWake (r := σ.regs) ?_ ?_ ?_
      · rw [hw]
        have := congrArg BitVec.toNat h2; simp [Reg64s.get64] at this; rw [this]
      · have := congrArg BitVec.toNat h8; simpa [Reg64s.get64] using this
      · have := congrArg BitVec.toNat h1; simpa [Reg64s.get64] using this
      · have := congrArg BitVec.toNat h0; rw [← htp4, ← this]; simp [Reg64s.get64]
    refine (syscall_nd hK hF (fun s he hn => hcode.sys s he hn) (fun σ c hJ => ?_) ?_).toT
    · refine ⟨.futexWake 1, hcall σ c hJ, nofun, fun v _ => ⟨c, .refl c, ?_⟩⟩
      obtain ⟨hT, -⟩ := hJ
      hit PN.n5
    · rintro s c σ call - hJ hc
      rw [hcall σ c hJ] at hc
      cases hc
      exact ⟨nofun, nofun, nofun, nofun⟩
  case n5 => node b5 b5_ok n5; rw [N, b5_run]; exit PX.ret
  case done => node b6 b6_ok done; rw [N, b6_run]; exit PX.ret

end Proof

/-- info: 'Spike.Lib.X64.Flow.Worker.Unpark.seg_unpark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_unpark

end Unpark

/-- info: 'Spike.Lib.X64.Flow.Worker.fn_segT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fn_segT

/-- info: 'Spike.Lib.X64.Flow.Worker.relStore_nd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms relStore_nd

/-- info: 'Spike.Lib.X64.Flow.Worker.unpkXchg_nd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unpkXchg_nd

/-- info: 'Spike.Lib.X64.Flow.Worker.texit_nd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms texit_nd

/-- info: 'Spike.Lib.X64.Flow.Worker.call_ndT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms call_ndT

/-! ## The parser's forms -/

/-- The worker's store and the `exited` release are plain `movq`s to memory. -/
example : parse("movq %rax, (%rcx)") = [stDir .rcx 0 .rax] := by decide
example : parse("movq %rax, 24(%rcx)") = [stDir .rcx 24 .rax] := by decide
/-- The permit exchange. -/
example : parse("xchgq %rax, 16(%rcx)") = [xchgDir .rcx 16 .rax] := by decide

end Spike.Lib.X64.Flow.Worker
