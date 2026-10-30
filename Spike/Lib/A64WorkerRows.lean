/-
**The worker's thread rows on AArch64** (the worker's
half): the target side of the worker's `store rel c 1`, `unpark j` and the
thread's exit, over the thread rows of `Spike/Lib/SegThr.lean` (`OutT`,
`SegT`). The listing is `hello.w`'s (`scc --arch arm -o - Scc/Test/hello.w`).

- `fn_segT`: `fn_seg` over `SegT`.
- `relStore_nd`: **the node at the source's release store** `stlr Xt, [Xn]`
  (`Out.store`): `Xn` holds the address `A` of the source's word, `Xt` a
  value representing the stored word.
- `unpkSwp_nd`: **the node at the worker's exchange on the named thread's
  permit word** (`OutT.unpk`): the source takes its `unpark` here, at the
  worker's own `swpal`, and nowhere else (main's park is no commit point).
- `svcCall_exit`, `svcCall_futexWake`: the decoded calls.
- `texit_nd`: **the node at the thread's `exit`** (`OutT.texit`), the source
  at `ret a`.
- `Unpark.seg_unpark`: `scc_rt_unpark` as one `SegT` segment.
- `call_ndT`: `call_nd` over `SegT` (a callee with the thread rows).
- `WkTail.seg_wkTail`: `wc_worker`'s tail (from `.sp4`: the store, the call
  of `scc_rt_unpark` as a given node, the return); `WkTail.seg_unparkCall`
  discharges the call with `Unpark.seg_unpark` (`WkTail.seg_wkTailU`).
- `ThrTail.seg_thrTail`: `scc_rt_thr_worker`'s tail (from `.sp0`: the
  `exited` release, the `exit`).

The obligations these rows leave to the whole-program proof (1.6,
`WakeObligations`) are `unpark_src` (an `unpk` row is a source
step of the worker taking its `unpark`) and `worker_done` (a `texit` row:
the worker has finished).
-/
import Spike.Lib.A64Park
import Spike.Lib.A64Dead
import Spike.Lib.SegThr
import Kraken.AArch64.Parser

namespace Spike.Lib.A64.Flow.Worker

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (ValRep)
open Spike.Lib.A64.Flow.Ret0 (StOk land_ldStep)
open Spike.Lib.A64.Flow.Park (swpDir)

/-! ## Nodes with the thread rows -/

section Nodes

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A whole function with the thread rows**: `fn_seg` over `SegT`. -/
theorem fn_segT (h : ∀ i, SegT p lbl ms (At exe endPc R F (N i)) (Next exe endPc R F N E)) (i0 : ι) :
    SegT p lbl ms (At exe endPc R F (N i0)) (fun s c => ∃ x, At exe endPc R F (E x) s c) :=
  (SegT.cfg (fun i => At exe endPc R F (N i)) h).mono_pre fun _ _ h => ⟨i0, h⟩

/-- **A node at the source's release store** `stlr Xt, [Xn]`: `Xn` holds
`A`, the address of the source's word at its `let x = store rel a b in e`
(`ValRep`, an untagged locative), `A` not private memory under `F`
(`hdm`), `Xt` a value representing `b`'s word; the abstract state is
unchanged and the source takes its store. -/
theorem relStore_nd {n : ND} {t b : XReg} {A : BitVec 64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s n.pc [.instr ⟨.W64, .STLR .W64 (.low (.reg t) .W64) (.low (.reg b) .W64)⟩])
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = A ∧
      ∃ x a bb e ty tb w wb, c.term = .let_ x (.store true a bb none) e ∧
        TermRun.evalAt c.env a = some (ty, [w]) ∧ ValRep lbl w.val A.toNat ∧ (∃ sa, w.val = .loc sa 0) ∧
        TermRun.evalAt c.env bb = some (tb, [wb]) ∧
        ValRep lbl wb.val (σ.regs.getRegOrZr (.low (.reg t) .W64)).toNat ∧
        Lands N E ⟨n.pc + Int64.ofNat 4, n.o, σ⟩ ⟨e, (x, .unit, []) :: c.env, none⟩) :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine Seg.step fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : Lower.A64.CellAt s (.instr ⟨.W64, .STLR .W64 (.low (.reg t) .W64) (.low (.reg b) .W64)⟩) 4 :=
    (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨hb, x, a, bb, e, ty, tb, w, wb, ht, hev, hv, htag, hevb, hvb, hL⟩ := hedge _ σ c hA hD hJ
  have hb' : (s.st.1.regs.getXReg b).toBitVec = A := by rw [hA.regs]; exact hb
  have hex := Lower.A64.exec_stlr_agrees hc (by rw [hb']; exact hdm _ hD)
    (by rw [hb']; exact agrees_of_decls hdc _ _)
  rw [hb'] at hex
  refine .store .rel A _ _ x a bb e ty tb w wb hex ht hev hv hevb
    (by rw [Spike.Lib.A64.toNat_setWidth128, hA.regs]; exact hvb) ?_ htag
  have hs1 : after s 4 s.st.1 = { s with st := (s.st.1, n.pc + Int64.ofNat 4) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA hD⟩
  · exact .inr ⟨y, hy.at he hn hdc hA hD⟩

/-- `(1 : BitVec 64)` widened is the RMW's value `1`. -/
theorem one_setWidth : ((1#64).setWidth 128 : BitVec 128) = 1 := by decide

/-- **The node at the worker's exchange on the named thread's permit
word** `swp<k> Xs, Xt, [Xn]`: `Xn` holds `A = B + 16`, the permit word of
the thread whose tid word `jw` (representing `B`) the source's `let x =
unpark a in e` names, no hold pending; `Xs` holds `1`, a value runtime
memory may hold there (`StOk`); for every old value the state after it
(`Xt := old`) lands at a node with the source's `unpark` taken (`x` bound
to ``). The row is `OutT.unpk`. -/
theorem unpkSwp_nd {n : ND} {k : RmwKind} {rs rt b : XReg} {A B : BitVec 64} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [swpDir k rs rt b])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = A ∧ σ.regs.getRegOrZr (.low (.reg rs) .W64) = 1#64 ∧
      StOk ms F exe endPc A 1#64 ∧ A = B + 16#64 ∧
      ∃ x a e ty jw, c.term = .let_ x (.ext .unpark a) e ∧ c.hold = none ∧
        TermRun.evalAt c.env a = some (ty, [jw]) ∧ ValRep lbl jw.val B.toNat ∧
        ∀ v : BitVec 64, Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill rt, ldStep rt v σ⟩
          ⟨e, (x, ExtName.unpark.sig.2, []) :: c.env, none⟩) :
    SegT p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegT.step fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : Lower.A64.CellAt s (swpDir k rs rt b) 4 :=
    (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨hb, h1, hS, hAB, x, a, e, ty, jw, ht, hh, hev, hv, hL⟩ := hedge _ σ c hA hD hJ
  have hb' : (s.st.1.regs.getXReg b).toBitVec = A := by rw [hA.regs]; exact hb
  have hex := Lower.A64.exec_swp hc (by rw [hb']; exact hS.unmapped _ hD)
  rw [hb', Lower.A64.access_agrees (agrees_of_decls hdc _ _)] at hex
  have hz : (RegOrZr.low (.reg rt) .W64).isZr = false := rfl
  rw [hz] at hex
  refine .unpk k A B _ _ x a e ty jw hex hS.rt hS.mp (fun _ => by rw [hA.regs, h1, one_setWidth]) ht hh hev hv
    hAB fun old _ _ => ⟨?_, land_ldStep hF he hn hdc hpc hA hD (hL _)⟩
  have := hS.G
  rwa [one_setWidth] at this

/-- **A node at a fence** `dmb <opt>`: the abstract state and the
source's control are unchanged (`OutT.fnc`, the source stutters), landing
at `pc + 4`. -/
theorem dmb_nd {n : ND} {k : FenceKind}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [.instr ⟨.W64, .DMB k⟩])
    (hedge : ∀ σ c, n.J σ c → Lands N E ⟨n.pc + Int64.ofNat 4, n.o, σ⟩ c) :
    SegT p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegT.step fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : Lower.A64.CellAt s (.instr ⟨.W64, .DMB k⟩) 4 :=
    (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  refine .fnc k _ c (Lower.A64.exec_dmb hc) (.refl c) ?_
  have hs1 : after s 4 s.st.1 = { s with st := (s.st.1, n.pc + Int64.ofNat 4) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hedge σ c hJ with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA hD⟩
  · exact .inr ⟨y, hy.at he hn hdc hA hD⟩

/-- `dmb ish` parses to the full fence. -/
example : parseAArch64("dmb ish") = [.instr ⟨.W64, .DMB .sy⟩] := by decide

/-- **`x8 = 93` decodes to the thread's `exit`.** -/
theorem svcCall_exit {r : Reg64s} (h : r.X8.toNat = 93) : svcCall r = some .exit := by
  simp [svcCall, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.a64, h]

/-- **The futex wake the kernel model decodes**: `x8 = 98`, `x1 =
FUTEX_WAKE_PRIVATE`, a 4-aligned address in `x0`, waking `x2` threads. -/
theorem svcCall_futexWake {r : Reg64s} (h8 : r.X8.toNat = 98) (h1 : r.X1.toNat = 129) (h0 : r.X0.toNat % 4 = 0) :
    svcCall r = some (.futexWake r.X2.toNat) := by
  simp [svcCall, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.a64, Scc.Sem.A64.xRegs, Scc.Sem.Kernel.futexWaitPrivate,
    Scc.Sem.Kernel.futexWakePrivate, h8, h1, h0]

/-- **A node at the thread's `exit`**: `svc #0` with `x8 = 93` in every
state of the invariant, the source at `ret a`, under the kernel model, is
a segment with the thread rows to any exit (`OutT.texit`: the thread
ends). -/
theorem texit_nd {n : ND} {Q : Frag isaLSE2} (hK : ms.K = some Scc.Sem.A64.abi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [svcDir])
    (hx : ∀ σ c, n.J σ c → σ.regs.X8.toNat = 93 ∧ ∃ a, c.term = .ret a) :
    SegT p lbl ms (At exe endPc R F n) Q := by
  refine SegT.step fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : Lower.A64.CellAt s svcDir 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨h8, a, ht⟩ := hx σ c hJ
  have hd : Scc.Sem.Kernel.decode Scc.Sem.Kernel.Nrs.a64 (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
      some .exit := by
    rw [← svcCall_exit h8, svcCall, ← hA.regs]; rfl
  exact .texit _ a hK (Scc.Sem.A64.atSvc_of_cellAt hc) hd ht

/-- **A call node with the thread rows** (`call_nd_F` over `SegT`): the
callee's specification, a `SegT` segment for every region holding its frame
and every frame condition giving the caller's `F`, is a given node of the
caller from the call node `nC` to the caller's nodes. The proof is
`call_nd`'s. -/
theorem call_ndT {nC : ND} {γ : Type _} {κ' : Sort _} {lo' hi' : Int} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp + lo') (hlo0 : lo' ≤ 0) (hkc : nC.o.sp < R.hi) (hhi0 : hi' ≤ 0)
    (hk16 : nC.o.sp % 16 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ lo' →
      hi' ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ g,
        SegT p lbl ms (At exe endPc R' F' (Ne g)) (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c))
    (hNe : ∀ g, (Ne g).o = ⟨0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g, (Ne g).pc = nC.pc ∧ (Ne g).J (enter nC.o.sp σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), nC.J σC c → (Ne g).J (enter nC.o.sp σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee nC.o.sp lo' hi').Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp + (Ex g x).o.sp, []⟩, σR⟩ c') :
    SegT p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) := by
  -- the callee's region and its ghost-indexed frame condition
  let kc := nC.o.sp
  let R' := R.callee kc lo' hi'
  have hR' : R'.OK := Region.callee_ok hR hlo hlo0 hkc (by omega)
  have hb' := Region.callee_base (hi' := hi') hR hlo hlo0 hkc
  have hal' : R'.base.toNat % 16 = 0 := by
    have : ((R'.base.toNat : Int)) % 16 = 0 := by rw [hb']; omega
    omega
  have hFR' : FStable R' F := FStable.callee hR hlo hlo0 hkc (by omega) hF
  -- the ghost: the machine data and abstract state at the call, the caller's control, the callee's
  -- parameters; the facts about it ride in the frame condition (constant, so stable)
  let F' : MachineData × AS × Ctl × γ → MachineData → Prop := fun G m =>
    F m ∧ DFrame R' G.1 m ∧ Abs R nC.o G.1 G.2.1 ∧ nC.J G.2.1 G.2.2.1 ∧ (Ne G.2.2.2).J (enter kc G.2.1) G.2.2.1
  have hF' : ∀ G, FStable R' (F' G) := fun G m m' hm hd =>
    ⟨hFR' m m' hm.1 hd, hm.2.1.trans hd, hm.2.2⟩
  refine SegT.mono_pre (P := fun s c => ∃ G, At exe endPc R' (F' G) (Ne G.2.2.2) s c)
    (SegT.exists_pre fun G => ?_) ?_
  · -- the callee's segment, its exits landing at the caller's nodes
    refine (hcallee R' (F' G) hR' hal' (Int.le_refl _) (Int.le_refl _) (hF' G) (fun _ h => h.1) G.2.2.2).mono_post ?_
    rintro s c ⟨x, he, hn, hdc, hpc, σx, hAx, ⟨hD, hDF, hAC, hJC, hJE⟩, hJx⟩
    obtain ⟨mC, σC, cC, g⟩ := G
    simp only at hDF hAC hJC hJE hJx hAx hpc
    have hAR : Abs R ⟨kc + (Ex g x).o.sp, []⟩ s.st.1 (leave R' kc σC σx) := by
      refine ⟨hAx.regs, hAx.status, ?_, fun k hk => ?_⟩
      · intro r k' hr
        rcases r with y | _
        · cases hr
        · simp only [SO.get, Option.some.injEq] at hr
          subst hr
          have := hAx.so .SP _ rfl
          simp only [leave] at this ⊢
          rw [this, Region.callee_addr]
      · by_cases hin : R'.Off (k - kc)
        · obtain ⟨j, hj, hv⟩ := hAx.slot _ hin
          refine ⟨j, ?_, ?_⟩
          · rw [Region.callee_addr, show kc + (k - kc) = k by omega] at hj; exact hj
          · simp only [leave]; rw [ite_eq_left hin]; exact hv
        · obtain ⟨j, hj, hv⟩ := hAC.slot k hk
          refine ⟨j, ?_, ?_⟩
          · rw [hDF _ (R.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkc (by omega) hl8 hh8 hk hin)]
            exact hj
          · simp only [leave]; rw [ite_eq_right hin]; exact hv
    have hL := hret g x σC cC σx c (leave R' kc σC σx) hJC hJE hJx rfl rfl
      (fun k _ hn => by simp only [leave]; exact ite_eq_right hn)
    have hs : s = { s with st := (s.st.1, (Ex g x).pc) } := by rw [← hpc]; rfl
    rw [hs]
    rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
    · exact .inl ⟨j, hj.at he hn hdc hAR hD⟩
    · exact .inr ⟨y, hy.at he hn hdc hAR hD⟩
  · -- the caller's state at the call, seen from the callee
    rintro s c ⟨he, hn, hdc, hpc, σC, hA, hD, hJ⟩
    obtain ⟨g, hgpc, hgJ⟩ := hent σC c hJ
    refine ⟨(s.st.1, σC, c, g), he, hn, hdc, by rw [hpc, hgpc], enter kc σC, ?_,
      ⟨hD, DFrame.refl _ _, hA, hJ, hgJ⟩, hgJ⟩
    rw [hNe]
    refine ⟨hA.regs, hA.status, ?_, fun k hk => ?_⟩
    · intro r k' hr
      rcases r with y | _
      · cases hr
      · simp only [SO.get, Option.some.injEq] at hr
        subst hr
        have := hA.so .SP _ rfl
        simp only [enter] at this ⊢
        rw [this, Region.callee_addr, Int.add_zero]
    · obtain ⟨j, hj, hv⟩ := hA.slot _ (Region.callee_off hlo (by omega) (by omega) hk)
      exact ⟨j, by rw [Region.callee_addr]; exact hj, hv⟩

end Nodes

/-! ## `scc_rt_unpark`

    scc_rt_unpark(j = x0):
      prologue (frame of 48 bytes, x29/x30 saved at 32/40, j at 0)
      entry: old = swpal(1, [j + 16])             -- set j's permit: the source's unpark
             if old = 0 goto wake else goto done
      wake:  futex(j + 16, FUTEX_WAKE_PRIVATE, 1)  -- svc #0, x8 = 98
             epilogue; ret
      done:  epilogue; ret

The region is the frame, offsets `[-48, 0)`. Ghosts: the source controls
`c0` (at `let x = unpark a in e`, `a`'s word representing the tid `B`) and
`c1` (past it), the caller's `x29`, the return address `ra`, the thread
pointer `tp`. Entry (`.e`): `x0 = B`, the source at `c0`. Return (exit
`.ret`): the source at `c1`. The source takes its `unpark` at the `swpal`
(`unpkSwp_nd`) and stutters elsewhere; the permit word's facts for `1`
(`hS`) and its alignment (`htp4`) are hypotheses. -/

namespace Unpark

def b0 : List Directive := parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32
str x0, [sp]")
def b1 : List Directive := parseAArch64("movz x9, #1
ldr x10, [sp]
add x10, x10, #16")
def b2 : List Directive := parseAArch64("str x11, [sp, #8]
ldr x9, [sp, #8]
movz x10, #0
subs xzr, x9, x10
b.eq .L11_scc_rt_unpark.1_wake")
def b3 : List Directive := parseAArch64("b .L11_scc_rt_unpark.2_done")
def b4 : List Directive := parseAArch64("ldr x9, [sp]
movz x10, #16
add x9, x9, x10
str x9, [sp, #16]
ldr x0, [sp, #16]
movz x1, #129
movz x2, #1
movz x3, #0
movz x4, #0
movz x5, #0
movz x8, #98")
def b5 : List Directive := parseAArch64("str x0, [sp, #24]
ldr x29, [sp, #32]
ldr x30, [sp, #40]
add sp, sp, #48
ret")
def b6 : List Directive := parseAArch64("ldr x29, [sp, #32]
ldr x30, [sp, #40]
add sp, sp, #48
ret")

/-- The function's offsets inside the frame. -/
abbrev oI : SO := ⟨-48, []⟩
/-- The offsets at entry and return. -/
abbrev oE : SO := ⟨0, []⟩

block_spec b0 (-48) 0 oE b0
block_spec b1 (-48) 0 oI b1
block_spec b2 (-48) 0 oI b2
block_spec b3 (-48) 0 oI b3
block_spec b4 (-48) 0 oI b4
block_spec b5 (-48) 0 oI b5
block_spec b6 (-48) 0 oI b6

/-- The internal nodes: one per block, the exchange and the system call. -/
inductive PN where
  | e | n1 | swp | n2 | n3 | wake | svc | n5 | done

/-- The exits. -/
inductive PX where
  | ret

section Spec

variable (lab : Label → Int64) (c0 c1 : Ctl) (B x29 ra tp : BitVec 64)

/-- Inside the frame, the source at `c`: the caller's `x29`, the return
address and `B` in their cells, the thread pointer `tp`. -/
def JI (c' : Ctl) (σ : AS) (c : Ctl) : Prop :=
  c = c' ∧ σ.slot (-16) = x29 ∧ σ.slot (-8) = ra ∧ σ.slot (-48) = B ∧ σ.regs.TPIDR_EL0.toBitVec = tp

/-- At the exchange: `x10` the permit's address, `x9` the new value `1`. -/
def JS (σ : AS) (c : Ctl) : Prop :=
  JI B x29 ra tp c0 σ c ∧ σ.regs.X10.toBitVec = B + 16#64 ∧ σ.regs.X9.toBitVec = 1#64

/-- At entry. -/
def JE (σ : AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.regs.X0.toBitVec = B ∧ σ.regs.X29.toBitVec = x29 ∧ σ.regs.X30.toBitVec = ra ∧
    σ.regs.TPIDR_EL0.toBitVec = tp

/-- At return. -/
def JX (σ : AS) (c : Ctl) : Prop :=
  c = c1 ∧ σ.regs.X29.toBitVec = x29 ∧ σ.regs.X30.toBitVec = ra ∧ σ.regs.TPIDR_EL0.toBitVec = tp

/-- The pc of the futex wake's `svc`. -/
abbrev pcSvc : Int64 := lab ".L11_scc_rt_unpark.1_wake" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4

/-- **The nodes.** -/
def N : PN → ND
  | .e => ⟨lab "scc_rt_unpark", oE, JE c0 B x29 ra tp⟩
  | .n1 => ⟨lab ".L11_scc_rt_unpark.0_entry", oI, JI B x29 ra tp c0⟩
  | .swp => ⟨lab ".L11_scc_rt_unpark.0_entry" + 4 + 4 + 4, oI, JS c0 B x29 ra tp⟩
  | .n2 => ⟨lab ".L11_scc_rt_unpark.0_entry" + 4 + 4 + 4 + 4, oI, JI B x29 ra tp c1⟩
  | .n3 => ⟨lab ".L11_scc_rt_unpark.0_entry" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, JI B x29 ra tp c1⟩
  | .wake => ⟨lab ".L11_scc_rt_unpark.1_wake", oI, JI B x29 ra tp c1⟩
  | .svc => ⟨pcSvc lab, oI, fun σ c => JI B x29 ra tp c1 σ c ∧ σ.regs.X0.toBitVec = B + 16#64 ∧
      σ.regs.X1 = 129 ∧ σ.regs.X2 = 1 ∧ σ.regs.X8 = 98⟩
  | .n5 => ⟨pcSvc lab + 4, oI, JI B x29 ra tp c1⟩
  | .done => ⟨lab ".L11_scc_rt_unpark.2_done", oI, JI B x29 ra tp c1⟩

/-- **The exit**: the return to `ra`, the source past its `unpark`. -/
def E : PX → ND
  | .ret => ⟨Int64.ofBitVec ra, oE, JX c1 x29 ra tp⟩

/-- **The code**: every block at its node's pc. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  e : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 B x29 ra tp .e).pc b0
  n1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 B x29 ra tp .n1).pc b1
  swp : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 B x29 ra tp .swp).pc [swpDir .acqRel .X9 .X11 .X10]
  n2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 B x29 ra tp .n2).pc b2
  n3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 B x29 ra tp .n3).pc b3
  wake : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 B x29 ra tp .wake).pc b4
  svc : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 B x29 ra tp .svc).pc [svcDir]
  n5 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 B x29 ra tp .n5).pc b5
  done : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 B x29 ra tp .done).pc b6

/-- `scc_rt_unpark`'s code does not depend on its ghosts (its nodes' pcs
do not). -/
theorem Code.ghost {exe : _root_.Executable} {endPc : Int64} {c0 c1 c0' c1' : Ctl}
    {B x29 ra tp B' x29' ra' tp' : BitVec 64} (h : Code c0 c1 B x29 ra tp exe endPc) :
    Code c0' c1' B' x29' ra' tp' exe endPc :=
  ⟨h.e, h.n1, h.swp, h.n2, h.n3, h.wake, h.svc, h.n5, h.done⟩

end Spec

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 c1 : Ctl}
  {B x29 ra tp : BitVec 64}

set_option hygiene false in
/-- A block node: the block, its `okBlk`, its code; the edge is left. -/
macro "node " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine (seg_nd (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (fun s he hn => hcode.$f s he hn) fun σ c hJ => ⟨c, .refl c, ?_⟩).toT)

/-- Hitting node `j`. -/
macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> simp_all [N, JI, JS, JE, JX, Spike.Lib.upd_apply, Reg64s.getSysReg, svcStep, ldStep, KeepTP.setRegOrZr_tp, KeepTP.setXReg_tp]))

/-- Hitting exit `x`. -/
macro "exit " x:term : tactic =>
  `(tactic| (refine .inr ⟨$x, ?_, rfl, ?_⟩ <;> simp_all [N, E, JI, JS, JE, JX, Spike.Lib.upd_apply, Reg64s.getSysReg, svcStep, ldStep, KeepTP.setRegOrZr_tp, KeepTP.setXReg_tp]))

/-- **`scc_rt_unpark` is one segment with the thread rows** from its entry
to its return: the source takes its `unpark` at the `swpal` setting the
permit word `B + 16` to `1` (`OutT.unpk`, for any old value) and stutters
elsewhere; the futex wake returns `0` or `1`. -/
theorem seg_unpark (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48)
    (hhi : 0 ≤ R.hi) (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {jw : TermRun.Word}
    (ht : c0.term = .let_ x (.ext .unpark a) e) (hh : c0.hold = none)
    (hev : TermRun.evalAt c0.env a = some (ty, [jw])) (hv : ValRep lbl jw.val B.toNat)
    (hc1 : c1 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c0.env, none⟩)
    (hcode : Code c0 c1 B x29 ra tp exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L11_scc_rt_unpark.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_unpark" + 4 + 4 + 4 + 4 + 4) :
    SegT p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 B x29 ra tp .e))
      (fun s c => ∃ x, At exe endPc R F (E c1 x29 ra tp x) s c) := by
  refine fn_segT (N := N _ c0 c1 B x29 ra tp) (E := E c1 x29 ra tp) (fun i => ?_) PN.e
  cases i
  case e => node b0 b0_ok e; rw [N, b0_run]; hit PN.n1
  case n1 => node b1 b1_ok n1; rw [N, b1_run]; hit PN.swp
  case swp =>
    refine unpkSwp_nd (A := B + 16#64) (B := B) hF (fun s he hn => hcode.swp s he hn) fun m σ c _ _ hJ => ?_
    obtain ⟨⟨rfl, hJ⟩, h10, h9⟩ := hJ
    refine ⟨h10, by rw [Spike.Lib.A64.Flow.Ret0.getRegOrZr_x9, h9], hS, rfl, x, a, e, ty, jw, ht, hh, hev, hv,
      fun v => ?_⟩
    rw [← hc1]
    hit PN.n2
  case n2 =>
    node b2 b2_ok n2; rw [N, b2_run]
    split
    · hit PN.wake
    · hit PN.n3
  case n3 => node b3 b3_ok n3; rw [N, b3_run]; hit PN.done
  case wake => node b4 b4_ok wake; rw [N, b4_run]; hit PN.svc
  case svc =>
    refine (svc_nd hK hF (fun s he hn => hcode.svc s he hn) (fun σ c hJ => ?_) ?_).toT
    · obtain ⟨hT, h0, h1, h2, h8⟩ := hJ
      refine ⟨_, svcCall_futexWake (by rw [h8]; rfl) (by rw [h1]; rfl) (by rw [← htp4, ← h0]; rfl),
        fun v _ => ⟨c, .refl c, ?_⟩⟩
      hit PN.n5
    · rintro s c σ call - ⟨-, h0, h1, h2, h8⟩ hcall
      rw [svcCall_futexWake (by rw [h8]; rfl) (by rw [h1]; rfl) (by rw [← htp4, ← h0]; rfl)] at hcall
      cases hcall
      exact ⟨nofun, nofun, nofun, nofun⟩
  case n5 => node b5 b5_ok n5; rw [N, b5_run]; exit PX.ret
  case done => node b6 b6_ok done; rw [N, b6_run]; exit PX.ret

end Proof

end Unpark

/-! ## `wc_worker`'s tail

    .sp4:  x9 = 1; x10 = c (cell 32)
           stlr x9, [x10]                 -- the source's `store rel c 1`
           x0 = j (cell 40)
           bl scc_rt_unpark               -- the source's `unpark j` (inside)
    .sp6:  epilogue (x29/x30 at 80/88, frame of 96); ret

The region is the frame, offsets `[-96, 0)`. Ghosts: the source controls
`c0` (at `let d = store rel a b in e1`), `c1` (past the store), `c2`
(past the `unpark`), the address `A` of `c` and the tid `B` of `j` in their
cells, the caller's `x29`, the return address `ra`, the thread pointer
`tp`. The source facts of the store (`a`'s word an untagged locative
representing `A`, `b`'s word representing `1`) and that `A` is not private
memory (`hdm`) are hypotheses; so is the call of `scc_rt_unpark` (`hunpk`,
from its entry with the return address in `x30` back to `.sp6`; its
segment is `Unpark.seg_unpark` in the callee's region). -/

namespace WkTail

def b0 : List Directive := parseAArch64("movz x9, #1
ldr x10, [sp, #32]")
def b1 : List Directive := parseAArch64("ldr x0, [sp, #40]")
def b2 : List Directive := parseAArch64("bl scc_rt_unpark")
def b3 : List Directive := parseAArch64("ldr x29, [sp, #80]
ldr x30, [sp, #88]
add sp, sp, #96
ret")

/-- The function's offsets inside the frame. -/
abbrev oI : SO := ⟨-96, []⟩
/-- The offsets at return. -/
abbrev oE : SO := ⟨0, []⟩

block_spec b0 (-96) 0 oI b0
block_spec b1 (-96) 0 oI b1
block_spec b2 (-96) 0 oI b2
block_spec b3 (-96) 0 oI b3

/-- The internal nodes. -/
inductive PN where
  | sp4 | st | n3 | bl | unpk | sp6

/-- The exits. -/
inductive PX where
  | ret

section Spec

variable (lab : Label → Int64) (c0 c1 c2 : Ctl) (A B x29 ra tp : BitVec 64)

/-- Inside the frame, the source at `c'`: the caller's `x29`, the return
address, `A` and `B` in their cells, the thread pointer `tp`. -/
def JI (c' : Ctl) (σ : AS) (c : Ctl) : Prop :=
  c = c' ∧ σ.slot (-16) = x29 ∧ σ.slot (-8) = ra ∧ σ.slot (-64) = A ∧ σ.slot (-56) = B ∧
    σ.regs.TPIDR_EL0.toBitVec = tp

/-- The pc of the `bl`. -/
abbrev pcBl : Int64 := lab ".L23_wc_worker.sp4" + 4 + 4 + 4 + 4

/-- **The nodes.** -/
def N : PN → ND
  | .sp4 => ⟨lab ".L23_wc_worker.sp4", oI, JI A B x29 ra tp c0⟩
  | .st => ⟨lab ".L23_wc_worker.sp4" + 4 + 4, oI, fun σ c => JI A B x29 ra tp c0 σ c ∧
      σ.regs.X10.toBitVec = A ∧ σ.regs.X9.toBitVec = 1#64⟩
  | .n3 => ⟨lab ".L23_wc_worker.sp4" + 4 + 4 + 4, oI, JI A B x29 ra tp c1⟩
  | .bl => ⟨pcBl lab, oI, fun σ c => JI A B x29 ra tp c1 σ c ∧ σ.regs.X0.toBitVec = B⟩
  | .unpk => ⟨lab "scc_rt_unpark", oI, fun σ c => JI A B x29 ra tp c1 σ c ∧ σ.regs.X0.toBitVec = B ∧
      σ.regs.X30.toBitVec = BitVec.ofInt 64 (((pcBl lab).toInt + 4).bmod 18446744073709551616)⟩
  | .sp6 => ⟨lab ".L23_wc_worker.sp6", oI, JI A B x29 ra tp c2⟩

/-- **The exit**: the return to `ra`, the source past its `unpark`. -/
def E : PX → ND
  | .ret => ⟨Int64.ofBitVec ra, oE, fun σ c => c = c2 ∧ σ.regs.X29.toBitVec = x29 ∧ σ.regs.X30.toBitVec = ra ∧
      σ.regs.TPIDR_EL0.toBitVec = tp⟩

/-- **The code**: every block at its node's pc. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  sp4 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp4).pc b0
  st : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .st).pc
      [.instr ⟨.W64, .STLR .W64 (.low (.reg .X9) .W64) (.low (.reg .X10) .W64)⟩]
  n3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .n3).pc b1
  bl : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .bl).pc b2
  sp6 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp6).pc b3

end Spec

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 c1 c2 : Ctl}
  {A B x29 ra tp : BitVec 64}

set_option hygiene false in
/-- A block node: the block, its `okBlk`, its code; the edge is left. -/
macro "node " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine (seg_nd (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (fun s he hn => hcode.$f s he hn) fun σ c hJ => ⟨c, .refl c, ?_⟩).toT)

/-- Hitting node `j`. -/
macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> simp_all [N, JI, Spike.Lib.upd_apply, Reg64s.getSysReg, KeepTP.setRegOrZr_tp, KeepTP.setXReg_tp]))

/-- **`wc_worker`'s tail is one segment with the thread rows** from `.sp4`
to its return: the `stlr` is the source's `store rel c 1` (`Out.store`),
the call of `scc_rt_unpark` the given node `hunpk` (where the source takes
its `unpark`), the rest stutters. -/
theorem seg_wkTail (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -96)
    (hhi : 0 ≤ R.hi) (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c0.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c0.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: c0.env, none⟩)
    (hcode : Code c0 c1 c2 A B x29 ra tp exe endPc)
    (hunpk : SegT p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .unpk))
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp6))) :
    SegT p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp4))
      (fun s c => ∃ x, At exe endPc R F (E c2 x29 ra tp x) s c) := by
  refine fn_segT (N := N _ c0 c1 c2 A B x29 ra tp) (E := E c2 x29 ra tp) (fun i => ?_) PN.sp4
  cases i
  case sp4 => node b0 b0_ok sp4; rw [N, b0_run]; hit PN.st
  case st =>
    refine (relStore_nd (A := A) (fun s he hn => hcode.st s he hn) hdm fun m σ c _ _ hJ => ?_).toT
    obtain ⟨⟨rfl, hJ⟩, h10, h9⟩ := hJ
    refine ⟨h10, d, a, b, e1, ty, tb, w, wb, ht, hev, hv, htag, hevb,
      by rw [Spike.Lib.A64.Flow.Ret0.getRegOrZr_x9, h9]; exact hvb, ?_⟩
    rw [← hc1]
    hit PN.n3
  case n3 => node b1 b1_ok n3; rw [N, b1_run]; hit PN.bl
  case bl => node b2 b2_ok bl; rw [N, b2_run]; hit PN.unpk
  case unpk => exact hunpk.mono_post fun s c h => .inl ⟨PN.sp6, h⟩
  case sp6 =>
    node b3 b3_ok sp6; rw [N, b3_run]
    refine .inr ⟨PX.ret, ?_, rfl, ?_⟩ <;> simp_all [N, E, JI]


/-- **The call of `scc_rt_unpark`** (`call_ndT` with `Unpark.seg_unpark`,
frame `[-48, 0)` from the call's `sp`, which is at offset `-96`): from
`.unpk` back to `.sp6`, the frame unmoved, the source from `c1` (at its
`let x = unpark a in e`, `a`'s word representing `B`) to `c2` (past it).
The ghosts of `seg_unpark` are `x29` and `x30` at the call. The facts it
needs are hypotheses: the kernel model (`hK`), the permit word's (`hS`,
`htp4`), the routine's code (`hpcode`, any ghosts: `Unpark.Code.ghost`)
and prologue fall-through (`hpentry`), and the return label `.sp6` after
the `bl` (`hsp6`). -/
theorem seg_unparkCall (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144)
    (hhi : 0 ≤ R.hi) (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {jw : TermRun.Word}
    (ht : c1.term = .let_ x (.ext .unpark a) e) (hh : c1.hold = none)
    (hev : TermRun.evalAt c1.env a = some (ty, [jw])) (hv : ValRep lbl jw.val B.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩)
    {c0' c1' : Ctl} {B' x29' ra' tp' : BitVec 64} (hpcode : Unpark.Code c0' c1' B' x29' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".L11_scc_rt_unpark.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_unpark" + 4 + 4 + 4 + 4 + 4)
    (hsp6 : (_root_.Executable.labels exe).label ".L23_wc_worker.sp6" = pcBl (_root_.Executable.labels exe).label + 4) :
    SegT p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .unpk))
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp6)) := by
  refine (call_ndT (lo' := -48) (hi' := 0)
    (N := fun _ : Unit => N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp6)
    (E := fun e : Empty => e.elim)
    (Ne := fun g : BitVec 64 × BitVec 64 => Unpark.N (_root_.Executable.labels exe).label c1 c2 B g.1 g.2 tp .e)
    (Ex := fun g y => Unpark.E c2 g.1 g.2 tp y)
    hR hal hF (by show R.lo ≤ -96 + -48; omega) (by decide) (by show (-96 : Int) < R.hi; omega) (by decide)
    (by show (-96 : Int) % 16 = 0; decide) (by decide) (by decide)
    (fun R' F' hR' hal' hlo' hhi' hF' hFF g =>
      Unpark.seg_unpark hF' hR' hal' hlo' hhi' hK (hS.mono hFF) htp4 ht hh hev hv hc2 hpcode.ghost hpentry)
    (fun _ => rfl) ?_ ?_).mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
  · rintro σC c ⟨⟨rfl, -, -, -, -, htp⟩, h0, -⟩
    exact ⟨(σC.regs.X29.toBitVec, σC.regs.X30.toBitVec), rfl, rfl, h0, rfl, rfl, htp⟩
  · rintro ⟨x29', ra'⟩ ⟨⟩ σC c σx c' σR ⟨⟨rfl, h16, h8, h64, h56, -⟩, -, h30⟩ ⟨-, -, -, hra, -⟩ ⟨hc', -, -, htp'⟩ hreg -
      hslot
    have hout : ∀ k : Int, -96 ≤ k → k % 8 = 0 → k + 8 ≤ 0 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
      hslot k ⟨h2, by omega, by omega⟩ fun ⟨_, _, h⟩ => by
        simp only [Region.callee, N] at h; omega
    refine .inl ⟨(), ?_, rfl, hc', ?_, ?_, ?_, ?_, ?_⟩
    · subst hra
      show (_root_.Executable.labels exe).label ".L23_wc_worker.sp6" = Int64.ofBitVec σC.regs.X30.toBitVec
      rw [h30, hsp6, Ret0.ofInt_bmod, BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt]; rfl
    · rw [hout (-16) (by decide) (by decide) (by decide)]; exact h16
    · rw [hout (-8) (by decide) (by decide) (by decide)]; exact h8
    · rw [hout (-64) (by decide) (by decide) (by decide)]; exact h64
    · rw [hout (-56) (by decide) (by decide) (by decide)]; exact h56
    · show σR.regs.TPIDR_EL0.toBitVec = tp
      rw [hreg]; exact htp'

/-- **`wc_worker`'s tail with its `unpark` call discharged** (`seg_wkTail`
with `hunpk` from `seg_unparkCall`): the region holds `scc_rt_unpark`'s
frame below the tail's (`hlo`, `-96 - 48`). -/
theorem seg_wkTailU (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144)
    (hhi : 0 ≤ R.hi) (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c0.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c0.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: c0.env, none⟩)
    (hcode : Code c0 c1 c2 A B x29 ra tp exe endPc)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {au : CoreTerm.At} {e : Expr} {tu : Ty} {jw : TermRun.Word}
    (htu : c1.term = .let_ x (.ext .unpark au) e) (hhu : c1.hold = none)
    (hevu : TermRun.evalAt c1.env au = some (tu, [jw])) (hvu : ValRep lbl jw.val B.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩)
    {c0' c1' : Ctl} {B' x29' ra' tp' : BitVec 64} (hpcode : Unpark.Code c0' c1' B' x29' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".L11_scc_rt_unpark.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_unpark" + 4 + 4 + 4 + 4 + 4)
    (hsp6 : (_root_.Executable.labels exe).label ".L23_wc_worker.sp6" = pcBl (_root_.Executable.labels exe).label + 4) :
    SegT p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp4))
      (fun s c => ∃ x, At exe endPc R F (E c2 x29 ra tp x) s c) :=
  seg_wkTail hF hR hal (Int.le_trans hlo (by decide)) hhi hdm ht hev hv htag hevb hvb hc1 hcode
    (seg_unparkCall hF hR hal hlo hhi hK hS htp4 htu hhu hevu hvu hc2 hpcode hpentry hsp6)

end Proof

end WkTail

/-! ## `scc_rt_thr_worker`'s tail

    .sp0:  x9 = tpidr_el0 (spilled at 48); x10 = x9 + 24
           stlr 1, [x10]                  -- the thread's `exited` word
           x0 = 0; x8 = 93
           svc #0                         -- exit: the thread ends
           (dead: str x0, [sp, #56]; halt: b halt)

The region is the frame, offsets `[-80, 0)`. Ghosts: the source control
`c0` (the worker returned: at `ret a`), the thread pointer `tp`. The
`exited` word's facts for `1` (`hS`, `StOk`) are a hypothesis. The `exit`
is `OutT.texit`; nothing follows it, so the tail is a segment to any
fragment. -/

namespace ThrTail

def b0 : List Directive := parseAArch64("mrs x9, tpidr_el0
str x9, [sp, #48]
movz x9, #1
ldr x10, [sp, #48]
add x10, x10, #24")
def b1 : List Directive := parseAArch64("movz x0, #0
movz x8, #93")

/-- The function's offsets inside the frame. -/
abbrev oI : SO := ⟨-80, []⟩

block_spec b0 (-80) 0 oI b0
block_spec b1 (-80) 0 oI b1

/-- The internal nodes. -/
inductive PN where
  | sp0 | ex | n2 | svc

section Spec

variable (lab : Label → Int64) (c0 : Ctl) (tp : BitVec 64)

/-- **The nodes.** -/
def N : PN → ND
  | .sp0 => ⟨lab ".L18_scc_rt_thr_worker.sp0", oI, fun σ c => c = c0 ∧ σ.regs.TPIDR_EL0.toBitVec = tp⟩
  | .ex => ⟨lab ".L18_scc_rt_thr_worker.sp0" + 4 + 4 + 4 + 4 + 4, oI, fun σ c => c = c0 ∧
      σ.regs.X10.toBitVec = tp + 24#64 ∧ σ.regs.X9.toBitVec = 1#64⟩
  | .n2 => ⟨lab ".L18_scc_rt_thr_worker.sp0" + 4 + 4 + 4 + 4 + 4 + 4, oI, fun _ c => c = c0⟩
  | .svc => ⟨lab ".L18_scc_rt_thr_worker.sp0" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, fun σ c => c = c0 ∧
      σ.regs.X8 = 93⟩

/-- **The code**: every block at its node's pc. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  sp0 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 tp .sp0).pc b0
  ex : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 tp .ex).pc
      [.instr ⟨.W64, .STLR .W64 (.low (.reg .X9) .W64) (.low (.reg .X10) .W64)⟩]
  n2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 tp .n2).pc b1
  svc : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 tp .svc).pc [svcDir]

end Spec

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {tp : BitVec 64}

set_option hygiene false in
/-- A block node: the block, its `okBlk`, its code; the edge is left. -/
macro "node " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine (seg_nd (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (fun s he hn => hcode.$f s he hn) fun σ c hJ => ⟨c, .refl c, ?_⟩).toT)

/-- Hitting node `j`. -/
macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> simp_all [N, Spike.Lib.upd_apply, Reg64s.getSysReg, KeepTP.setRegOrZr_tp, KeepTP.setXReg_tp]))

/-- **`scc_rt_thr_worker`'s tail is one segment with the thread rows** from
`.sp0` to any fragment: the release of the thread's `exited` word (at
`tp + 24`, `StOk`), then the `exit` with the source at `ret a`
(`OutT.texit`); the source stutters until then. -/
theorem seg_thrTail {Q : Frag isaLSE2} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (tp + 24#64) 1#64) {a : CoreTerm.At} (ht : c0.term = .ret a)
    (hcode : Code c0 tp exe endPc) :
    SegT p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 tp .sp0)) Q := by
  refine (fn_segT (N := N _ c0 tp) (E := (nofun : Empty → ND)) (fun i => ?_) PN.sp0).mono_post
    fun _ _ ⟨x, _⟩ => x.elim
  cases i
  case sp0 => node b0 b0_ok sp0; rw [N, b0_run]; hit PN.ex
  case ex =>
    refine (Spike.Lib.A64.Flow.Ret0.ownStlr_nd (A := tp + 24#64) (fun s he hn => hcode.ex s he hn) fun m σ c _ _ hJ => ?_).toT
    obtain ⟨rfl, h10, h9⟩ := hJ
    refine ⟨h10, by rw [Spike.Lib.A64.Flow.Ret0.getRegOrZr_x9, h9]; exact hS, ?_⟩
    hit PN.n2
  case n2 => node b1 b1_ok n2; rw [N, b1_run]; hit PN.svc
  case svc =>
    refine texit_nd hK (fun s he hn => hcode.svc s he hn) fun σ c ⟨hc, h8⟩ => ⟨by rw [h8]; rfl, a, ?_⟩
    rw [hc]; exact ht

end Proof

end ThrTail

/-! ## The parser's forms -/

/-- The `stlr` of the store and the `exited` release is what Kraken's
parser makes of scc's text. -/
example : parseAArch64("stlr x9, [x10]") =
    [.instr ⟨.W64, .STLR .W64 (.low (.reg .X9) .W64) (.low (.reg .X10) .W64)⟩] := by
  decide

end Spike.Lib.A64.Flow.Worker
