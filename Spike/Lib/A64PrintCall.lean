/-
**A call of `print` from any caller node** (AArch64): `call_nd_FWK`
(`Spike/Lib/A64Call.lean`) with the callee `seg_printA_ofW`
(`Spike/Lib/A64PrintA.lean`), for any call node `nC` of any caller, not
just `wc_main`'s.

The ghost is the caller's abstract state at the call `σC`; `print`'s
arguments are its registers (`x29`, `x30`, the buffer `x0`, the count
`x1`), its source predicates are `Pc σC`/`Qc σC`. The caller gives:

- at the call node: `Pc σC 0` (the source at `print`'s loop top), the
  count below `2^63`;
- `print`'s blocks inside `W` in the callee's region at the call
  (`PrintAW`), and its write system call (`hsvc`);
- where the return lands (`hret`: `x29`, `x30` restored, `Pc σC x1`, the
  caller's cells outside the callee's region as at the call) and where the
  abort lands (`habort`).

`print_callW` is that, for any `Pc`/`Qc`. `print_call_segW` takes
`Pc = Qc = PrintC …` (`Spike/Lib/PrintSrc.lean`, the source's loop) on
arguments the caller gives as functions of `σC`, and discharges `hsvc` by
the output row (`hsvc_of_emit`, `Spike/Lib/A64PrintEmit.lean`): its byte
steps from the row's load-and-emit (`hlb`) and the source's loop, given
the byte step's closure under local runs (`LocalClosed`). The call-site
facts it asks are register facts only: `x1 = printN n m` with `8·m < 2^63`
(`printSite_x1`, from the lowering's `min(n, m·8)`).

Generic helpers: `enter_inj`/`enter_slot` (any `kc`) and
`PrintA.PrintAW.mono`.
-/
import Spike.Lib.A64PrintEmit
import Spike.Lib.A64Ret0
import Spike.Lib.PrintSrc

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib
open Spike.Lib.A64.Flow.Ret0 (CallerCells blkW_mono)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.PrintSrc (PrintC loadC nextC printN printLD printBody print_entry_run printC_entry
  printC_load printC_next)

/-! ## Generic helpers -/

/-- Equal entered states have equal slots. -/
theorem enter_slot {kc : Int} {σ σ' : AS} (h : enter kc σ = enter kc σ') (k : Int) : σ.slot k = σ'.slot k := by
  have hk := congrArg (fun σ : AS => σ.slot (k - kc)) h
  simp only [enter] at hk
  rwa [show kc + (k - kc) = k by omega] at hk

/-- Entering at `kc` is injective. -/
theorem enter_inj {kc : Int} {σ σ' : AS} (h : enter kc σ = enter kc σ') : σ = σ' := by
  have hr := congrArg AS.regs h
  have hs := congrArg AS.status h
  obtain ⟨r, st, sl⟩ := σ
  obtain ⟨r', st', sl'⟩ := σ'
  simp only [enter] at hr hs
  subst hr hs
  have : sl = sl' := funext fun k => enter_slot h k
  subst this
  rfl

/-- `PrintAW` under a weaker frame condition holds under a stronger one. -/
theorem _root_.Spike.Lib.A64.PrintA.PrintAW.mono {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {F F' : MachineData → Prop} {x29 ra buf0 : BitVec 64} {len0 : Nat}
    {P Q : Nat → Ctl → Prop}
    (h : PrintA.PrintAW x29 ra buf0 len0 P Q W K exe endPc R F) (hFF : ∀ m, F' m → F m) :
    PrintA.PrintAW x29 ra buf0 len0 P Q W K exe endPc R F' :=
  ⟨blkW_mono h.e hFF, blkW_mono h.n1 hFF, blkW_mono h.loop hFF, blkW_mono h.n3 hFF, blkW_mono h.write hFF,
    blkW_mono h.n5 hFF, blkW_mono h.n6 hFF, blkW_mono h.n7 hFF, blkW_mono h.chk2 hFF, blkW_mono h.n9 hFF,
    blkW_mono h.n10 hFF, blkW_mono h.chk3 hFF, blkW_mono h.n12 hFF, blkW_mono h.adv hFF, blkW_mono h.fail hFF,
    blkW_mono h.done hFF⟩

/-- **A byte step closed under local runs**: a local run of the source
before the step, and local runs after it into `Ψ` from wherever it lands,
keep it a byte step (into `Ψ`). -/
def LocalClosed (p : Prog) (BO : State → Nat → Ctl → (Ctl → Prop) → Prop) : Prop :=
  ∀ s a c c' (Φ Ψ : Ctl → Prop), LocalRun p c c' → BO s a c' Φ →
    (∀ c1, Φ c1 → ∃ c2, LocalRun p c1 c2 ∧ Ψ c2) → BO s a c Ψ

/-! ## The call site's register facts -/

/-- **The count at a `print` call**: the lowering passes `min(n, m·8)` in
`x1`; it is `printN n m`, below `2^63` when `8·m` is. -/
theorem printSite_x1 {x1 : BitVec 64} {n m : Nat} (h : x1.toNat = min n (m * 8)) (hm : 8 * m < 2 ^ 63) :
    x1.toNat = printN n m ∧ x1.toNat < 2 ^ 63 := by
  unfold printN; omega

/-- **The source's entry to `print`**: from a local run to `print`'s body
on a nonempty slice, a local run to `print`'s loop top (`PrintC … 0`). -/
theorem printC_of_entry {p : Prog} (hd : p.find? (·.name == "printL") = some printLD) {c : Ctl}
    {pw wm wn : TermRun.Word} {n m : Nat}
    (h : ∃ c1, LocalRun p c c1 ∧ c1 = ⟨printBody, [("a", Hello1Src.sliceTy, [pw, wm, wn])], none⟩ ∧
      wm.val = .num m ∧ m ≠ 0 ∧ wn.val = .num n) :
    ∃ c', LocalRun p c c' ∧ PrintC pw wn n m 0 c' := by
  obtain ⟨c1, r, rfl, hwm, hm0, hwn⟩ := h
  exact ⟨_, r.trans (print_entry_run hd hwm hm0).toLocalRun, printC_entry hwn hm0⟩

/-! ## The call -/

namespace PrintCall

variable (lab : Label → Int64) (Pc Qc : AS → Nat → Ctl → Prop) (kc : Int)

/-- `print`'s nodes for the call state `σC`. -/
abbrev pN (σC : AS) : Print.PN → ND :=
  PrintA.N lab σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec σC.regs.X1.toBitVec.toNat
    (Pc σC) (Qc σC)

/-- `print`'s exits for the call state `σC`. -/
abbrev pE (σC : AS) : Print.PX → ND :=
  PrintA.E lab σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X1.toBitVec.toNat (Pc σC) (Qc σC)

/-- `print`'s entry, pinned to the call state `σC` entered at `kc`. -/
def pNe (σC : AS) : ND :=
  ⟨(pN lab Pc Qc σC .e).pc, (pN lab Pc Qc σC .e).o, fun σ c => (pN lab Pc Qc σC .e).J σ c ∧ σ = enter kc σC⟩

/-- `print`'s region in the caller's region `R`, called at `kc`. -/
abbrev pR (R : Region) : Region := R.callee kc (-48) 0

/-- `print`'s frame condition: the caller's, with the caller's cells
outside `print`'s region holding values. -/
abbrev pF (R : Region) (F : MachineData → Prop) : MachineData → Prop := fun m => F m ∧ CallerCells R kc (-48) 0 m

/-- **`print`'s source predicate** at the call state `σC`: the source at the
top of `printL` with `k` bytes out (`PrintC`), on the arguments the caller
gives for `σC`. -/
def pcS (pw wn : AS → TermRun.Word) (n m : AS → Nat) (σC : AS) (k : Nat) (c : Ctl) : Prop :=
  PrintC (pw σC) (wn σC) (n σC) (m σC) k c

/-- **A frame condition of `print` that knows the call**: kept by writes
inside `print`'s region, and every state under `F'` is under `pF` and has a
caller's state `mC`, `σC` at the call node `nC` (`Abs`, `nC.J`) whose cells
outside `print`'s region it keeps (`CKept`). `call_nd_FWK` gives it to the
callee; `print_callW'` passes it on. -/
def pFJ (R : Region) (F : MachineData → Prop) (nC : ND) (σC : AS) (F' : MachineData → Prop) : Prop :=
  FStable (pR nC.o.sp R) F' ∧
    ∀ m, F' m → pF nC.o.sp R F m ∧ ∃ mC c, Abs R nC.o mC σC ∧ nC.J σC c ∧ CKept R nC.o.sp (-48) 0 mC m

end PrintCall

open PrintCall

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND} {E : κ → ND}

/-- **A call of `print` is one segment inside `W`**, from any call node
`nC` (pc `scc_rt_print`, `sp` offset `nC.o.sp` 16-aligned with `print`'s
48 bytes inside `R`) to the caller's nodes `N` and exits `E`: `call_nd_FWK`
with `seg_printA_ofW`, for any source predicates `Pc`/`Qc` of the call
state (see the module docstring). `print`'s blocks (`hW`) and system call
(`hsvc`) are asked only under frame conditions that know the call
(`pFJ`: a caller's state at `nC` whose cells outside `print`'s region the
state keeps), as `call_nd_FWK` gives them. -/
theorem print_callW' {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    {nC : ND} {Pc Qc : AS → Nat → Ctl → Prop}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ nC.o.sp + -48) (hhi : nC.o.sp < R.hi) (hk16 : nC.o.sp % 16 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    (hP0 : ∀ σ c, nC.J σ c → Pc σ 0 c)
    (hlen : ∀ σ c, nC.J σ c → σ.regs.X1.toBitVec.toNat < 2 ^ 63)
    (hW : ∀ σC c, nC.J σC c → ∀ F' : MachineData → Prop, pFJ R F nC σC F' →
      PrintA.PrintAW σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec
      σC.regs.X1.toBitVec.toNat (Pc σC) (Qc σC) W K exe endPc (pR nC.o.sp R) F')
    (hsvc : ∀ F' : MachineData → Prop, ∀ σC c, nC.J σC c → pFJ R F nC σC F' →
      SegW W K p lbl ms (At exe endPc (pR nC.o.sp R) F' (pN (_root_.Executable.labels exe).label Pc Qc σC .svc))
        (At exe endPc (pR nC.o.sp R) F' (pN (_root_.Executable.labels exe).label Pc Qc σC .n5)))
    (hret : ∀ σC c σR c', nC.J σC c →
      σR.regs.X29.toBitVec = σC.regs.X29.toBitVec → σR.regs.X30.toBitVec = σC.regs.X30.toBitVec →
      Pc σC σC.regs.X1.toBitVec.toNat c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec σC.regs.X30.toBitVec, ⟨nC.o.sp, []⟩, σR⟩ c')
    (habort : ∀ σC c σR c' k, nC.J σC c → σR.regs.X0 = 4 → Qc σC k c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨(_root_.Executable.labels exe).label "scc_rt_abort", ⟨nC.o.sp + -48, []⟩, σR⟩ c') :
    SegW W K p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) := by
  let lab := (_root_.Executable.labels exe).label
  refine call_nd_FWK (KC := False) (lo' := -48) (hi' := 0) (M := fun _ => True)
    (Ne := pNe lab Pc Qc nC.o.sp) (Ex := pE lab Pc Qc)
    hR hal hF hlo (by decide) hhi (by decide) hk16 (by decide) (by decide) (fun h => h.elim) (fun h => h.elim)
    (fun _ h _ => h)
    (fun R' F' hR' hal' hlo' hhi' hF' _ hFF hR'e hcc g hg hS => by
      subst hR'e
      obtain ⟨σC, c, hJ, ⟨-, he⟩⟩ := hg
      have hσ : σC = g := enter_inj he
      subst hσ
      have hJF : pFJ R F nC σC F' := ⟨hF', fun m h => by
        obtain ⟨mC, σ', c', hA, hJ', ⟨-, he'⟩, hk⟩ := hS m h
        obtain rfl : σ' = σC := enter_inj he'
        exact ⟨⟨hFF m h, hcc m h⟩, mC, c', hA, hJ', hk⟩⟩
      refine ((PrintA.seg_printA_ofW hp hend hprog hF' hR' hal' hlo' hhi' (hlen σC c hJ)
        (hW σC c hJ F' hJF) (hsvc F' σC c hJ hJF)).mono_pre ?_).mono_post
          fun _ _ ⟨y, h⟩ => ⟨y, h, trivial⟩
      rintro s c ⟨a, b, d, e, σ, hA, hD, hJ', -⟩
      exact ⟨a, b, d, e, σ, hA, hD, hJ'⟩)
    (fun _ => rfl) ?_ ?_
  · intro σC c hJ
    exact ⟨σC, hpc.symm, ⟨hP0 σC c hJ, rfl, rfl, rfl, by simp [enter]⟩, rfl⟩
  · rintro g y σC c σx c' σR hJ ⟨-, he⟩ hx hreg - hsl
    have hσ : σC = g := enter_inj he
    subst hσ
    cases y
    · obtain ⟨h29, h30, hP⟩ := hx
      have h := hret σC c σR c' hJ (by rw [hreg]; exact h29) (by rw [hreg]; exact h30) hP hsl
      simpa [pE, PrintA.E, Print.oE] using h
    · obtain ⟨h4, k, hQ⟩ := hx
      exact habort σC c σR c' k hJ (by rw [hreg]; exact h4) hQ hsl

/-- **A call of `print` is one segment inside `W`**, with `print`'s blocks
and system call at the caller's frame condition `pF`: `print_callW'`. -/
theorem print_callW {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    {nC : ND} {Pc Qc : AS → Nat → Ctl → Prop}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ nC.o.sp + -48) (hhi : nC.o.sp < R.hi) (hk16 : nC.o.sp % 16 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    (hP0 : ∀ σ c, nC.J σ c → Pc σ 0 c)
    (hlen : ∀ σ c, nC.J σ c → σ.regs.X1.toBitVec.toNat < 2 ^ 63)
    (hW : ∀ σC c, nC.J σC c → PrintA.PrintAW σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec
      σC.regs.X1.toBitVec.toNat (Pc σC) (Qc σC) W K exe endPc (pR nC.o.sp R) (pF nC.o.sp R F))
    (hsvc : ∀ F' : MachineData → Prop, FStable (pR nC.o.sp R) F' → (∀ m, F' m → pF nC.o.sp R F m) →
      ∀ σC c, nC.J σC c →
      SegW W K p lbl ms (At exe endPc (pR nC.o.sp R) F' (pN (_root_.Executable.labels exe).label Pc Qc σC .svc))
        (At exe endPc (pR nC.o.sp R) F' (pN (_root_.Executable.labels exe).label Pc Qc σC .n5)))
    (hret : ∀ σC c σR c', nC.J σC c →
      σR.regs.X29.toBitVec = σC.regs.X29.toBitVec → σR.regs.X30.toBitVec = σC.regs.X30.toBitVec →
      Pc σC σC.regs.X1.toBitVec.toNat c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec σC.regs.X30.toBitVec, ⟨nC.o.sp, []⟩, σR⟩ c')
    (habort : ∀ σC c σR c' k, nC.J σC c → σR.regs.X0 = 4 → Qc σC k c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨(_root_.Executable.labels exe).label "scc_rt_abort", ⟨nC.o.sp + -48, []⟩, σR⟩ c') :
    SegW W K p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) :=
  print_callW' hp hend hprog hF hR hal hlo hhi hk16 hpc hP0 hlen
    (fun σC c hJ _ hJF => (hW σC c hJ).mono fun m h => (hJF.2 m h).1)
    (fun F' σC c hJ hJF => hsvc F' hJF.1 (fun m h => (hJF.2 m h).1) σC c hJ) hret habort

/-- **A call of `print` against the source's loop is one segment inside
`W`**, with `print`'s blocks and the system call's premises asked only
under frame conditions that know the call (`pFJ`): `print_callW'` as
`print_call_segW` is `print_callW`. -/
theorem print_call_segW' {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    {nC : ND} {BO : State → Nat → Ctl → (Ctl → Prop) → Prop} {WE : State → Ctl → Prop}
    {pw wn : AS → TermRun.Word} {n m : AS → Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ nC.o.sp + -48) (hhi : nC.o.sp < R.hi) (hk16 : nC.o.sp % 16 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    -- the call site
    (hP0 : ∀ σ c, nC.J σ c → PrintC (pw σ) (wn σ) (n σ) (m σ) 0 c)
    (hN : ∀ σ c, nC.J σ c → σ.regs.X1.toBitVec.toNat = printN (n σ) (m σ))
    (hm : ∀ σ c, nC.J σ c → 8 * m σ < 2 ^ 63)
    (hW : ∀ σC c, nC.J σC c → ∀ F' : MachineData → Prop, pFJ R F nC σC F' →
      PrintA.PrintAW σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec
      σC.regs.X1.toBitVec.toNat (pcS pw wn n m σC) (pcS pw wn n m σC) W K exe endPc (pR nC.o.sp R) F')
    -- the source's `print`
    (hd : p.find? (·.name == "printL") = some printLD)
    -- the output row, assumed
    (hE : PrintA.EmitW W K p lbl ms BO WE) (hK : ms.K = some Scc.Sem.A64.abi) (hcl : LocalClosed p BO)
    (hWs : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), pFJ R F nC σC F' → ∀ s c',
      At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) σC .svc) s c' →
      W s c' ∧ ∀ s', ¬ K s s')
    (hlb : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), pFJ R F nC σC F' → ∀ s c',
      At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) σC .svc) s c' →
      ∀ k j, k + j < printN (n σC) (m σC) →
      BO s ((σC.regs.X0.toBitVec + BitVec.ofNat 64 k).toNat + j) (loadC (pw σC) (wn σC) (m σC) (k + j))
        (fun c => ∃ mw b, c = nextC (pw σC) (wn σC) (m σC) (k + j) mw b))
    (hwe : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), pFJ R F nC σC F' → ∀ s c',
      At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) σC .svc) s c' →
      ∀ k c1, PrintC (pw σC) (wn σC) (n σC) (m σC) k c1 → WE s c1)
    -- where the return and the abort land
    (hret : ∀ σC c σR c', nC.J σC c →
      σR.regs.X29.toBitVec = σC.regs.X29.toBitVec → σR.regs.X30.toBitVec = σC.regs.X30.toBitVec →
      PrintC (pw σC) (wn σC) (n σC) (m σC) (printN (n σC) (m σC)) c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec σC.regs.X30.toBitVec, ⟨nC.o.sp, []⟩, σR⟩ c')
    (habort : ∀ σC c σR c' k, nC.J σC c → σR.regs.X0 = 4 → PrintC (pw σC) (wn σC) (n σC) (m σC) k c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨(_root_.Executable.labels exe).label "scc_rt_abort", ⟨nC.o.sp + -48, []⟩, σR⟩ c') :
    SegW W K p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) := by
  have hlen : ∀ σ c, nC.J σ c → σ.regs.X1.toBitVec.toNat < 2 ^ 63 := fun σ c hJ => by
    have := hN σ c hJ; have := hm σ c hJ; unfold printN at *; omega
  refine print_callW' hp hend hprog hF hR hal hlo hhi hk16 hpc hP0 hlen hW ?_
    (fun σC c σR c' hJ h29 h30 hP hsl => hret σC c σR c' hJ h29 h30 (hN σC c hJ ▸ hP) hsl) habort
  intro F' σC c hJ hFF
  have hF' := hFF.1
  have hpr := hprog
  simp only [Scc.Cert.Rt.A64.Print.printIn, Bool.and_eq_true, and_assoc] at hpr
  refine PrintA.hsvc_of_emit hE hK hF' (fun _ _ _ => hlen σC c hJ) ?_ (hWs σC c hJ F' hFF) (fun _ _ h => h) ?_
    (hwe σC c hJ F' hFF)
  · exact Scc.Cert.Rt.A64.Print.code_field hp hend hpr.2.2.2.2.2.1
      (by simp only [PrintA.N, PrintA.pcSvc, Scc.Cert.Rt.A64.Print.add4, Scc.Cert.Rt.A64.Print.add0])
  · intro s c' hAt k j c1 hlt hP
    have hk : k + j < printN (n σC) (m σC) := by rw [← hN σC c hJ]; exact hlt
    obtain ⟨_, _, -, -, -, -, -, -, hwn⟩ := id hP
    refine hcl _ _ _ _ _ _ (printC_load hd hP hk).toLocalRun (hlb σC c hJ F' hFF s c' hAt k j hk) ?_
    rintro _ ⟨mw, b, rfl⟩
    obtain ⟨c2, r, hc2⟩ := printC_next (mw := mw) (b := b) hd hwn hk
    exact ⟨c2, r.toLocalRun, hc2⟩

/-- **A call of `print` against the source's loop is one segment inside
`W`**: `print_callW` with `Pc = Qc = pcS …` and its write system call from
the output row (`hE`, its byte step `BO` closed under local runs, `hcl`),
the byte steps from the row's load-and-emit at the source's element load
(`hlb`) and the source's loop (`printC_load`, `printC_next`). The call
site gives register facts only: `x1 = printN n m` (`hN`) and `8·m < 2^63`
(`hm`); see `printSite_x1`. -/
theorem print_call_segW {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    {nC : ND} {BO : State → Nat → Ctl → (Ctl → Prop) → Prop} {WE : State → Ctl → Prop}
    {pw wn : AS → TermRun.Word} {n m : AS → Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ nC.o.sp + -48) (hhi : nC.o.sp < R.hi) (hk16 : nC.o.sp % 16 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    -- the call site
    (hP0 : ∀ σ c, nC.J σ c → PrintC (pw σ) (wn σ) (n σ) (m σ) 0 c)
    (hN : ∀ σ c, nC.J σ c → σ.regs.X1.toBitVec.toNat = printN (n σ) (m σ))
    (hm : ∀ σ c, nC.J σ c → 8 * m σ < 2 ^ 63)
    (hW : ∀ σC c, nC.J σC c → PrintA.PrintAW σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec
      σC.regs.X1.toBitVec.toNat (pcS pw wn n m σC) (pcS pw wn n m σC) W K exe endPc (pR nC.o.sp R)
      (pF nC.o.sp R F))
    -- the source's `print`
    (hd : p.find? (·.name == "printL") = some printLD)
    -- the output row, assumed
    (hE : PrintA.EmitW W K p lbl ms BO WE) (hK : ms.K = some Scc.Sem.A64.abi) (hcl : LocalClosed p BO)
    (hWs : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), (∀ m, F' m → pF nC.o.sp R F m) → ∀ s c',
      At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) σC .svc) s c' →
      W s c' ∧ ∀ s', ¬ K s s')
    (hlb : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), (∀ m, F' m → pF nC.o.sp R F m) → ∀ s c',
      At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) σC .svc) s c' →
      ∀ k j, k + j < printN (n σC) (m σC) →
      BO s ((σC.regs.X0.toBitVec + BitVec.ofNat 64 k).toNat + j) (loadC (pw σC) (wn σC) (m σC) (k + j))
        (fun c => ∃ mw b, c = nextC (pw σC) (wn σC) (m σC) (k + j) mw b))
    (hwe : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), (∀ m, F' m → pF nC.o.sp R F m) → ∀ s c',
      At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) σC .svc) s c' →
      ∀ k c1, PrintC (pw σC) (wn σC) (n σC) (m σC) k c1 → WE s c1)
    -- where the return and the abort land
    (hret : ∀ σC c σR c', nC.J σC c →
      σR.regs.X29.toBitVec = σC.regs.X29.toBitVec → σR.regs.X30.toBitVec = σC.regs.X30.toBitVec →
      PrintC (pw σC) (wn σC) (n σC) (m σC) (printN (n σC) (m σC)) c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec σC.regs.X30.toBitVec, ⟨nC.o.sp, []⟩, σR⟩ c')
    (habort : ∀ σC c σR c' k, nC.J σC c → σR.regs.X0 = 4 → PrintC (pw σC) (wn σC) (n σC) (m σC) k c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨(_root_.Executable.labels exe).label "scc_rt_abort", ⟨nC.o.sp + -48, []⟩, σR⟩ c') :
    SegW W K p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) :=
  print_call_segW' hp hend hprog hF hR hal hlo hhi hk16 hpc hP0 hN hm
    (fun σC c hJ _ hJF => (hW σC c hJ).mono fun m h => (hJF.2 m h).1) hd hE hK hcl
    (fun σC c hJ F' hJF => hWs σC c hJ F' fun m h => (hJF.2 m h).1)
    (fun σC c hJ F' hJF => hlb σC c hJ F' fun m h => (hJF.2 m h).1)
    (fun σC c hJ F' hJF => hwe σC c hJ F' fun m h => (hJF.2 m h).1) hret habort

end Fn

end Spike.Lib.A64.Flow
