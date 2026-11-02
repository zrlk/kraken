/-
**The flag on hello.w's source worker from `print`'s call on** (both landings,
AArch64): `FlagZ.FlagF cS` (every control a frame run reaches accesses no untagged locative but
`cS`, `WakeMappedRow.LabPtr`) at the worker's controls from the call of `print` (`wcP`) on, given the
packet's flag word is `cS`'s locative (`hcS : w3.val = .loc cS 0`).

A frame run from `print`'s call stays among three kinds of pair (`Inv`): the call itself on no frame; a
term of `print`'s or `printL`'s body (`PTermP`) on the call's frame `uFrame`; and, after `print`'s
return, the worker's store `workerRestH` on no frame (`wcRE`), which takes no step. None of `print`'s
and `printL`'s terms binds a load, store or exchange (`noLabB`, decided on the terms), nor calls
(`noCallB`); the store's only `LabPtr` is to its pointer `c ↦ w3`, i.e. `cS`.

- `PTermP`, `pTermP_step`: `print`'s and `printL`'s terms (`HelloEmitPh.PTermE`'s set), closed under a
  local step (`HelloW1.localStepS_shapeH`).
- `noLabB`, `noCallB`, `pTermP_noLab`, `pTermP_noCall`, `noPtr_pTermP`: no `LabPtr`, no call there.
- `wcRE ws`: the control after `print`'s return; `wcRE_noStep`: it takes no local step.
- `Inv`, `inv_step`, `inv_run`, `ptr_inv`: the invariant along frame runs, and `LabPtr` under it.
- `flagF_wcP`, `flagF_pTerm`, `flagF_wcRE`: `FlagF cS` at the call, inside `print`, at the store.
- `flagF_cS2` (source half): `FlagF cS` at `SegR.cS2` (`ret ()` after `unpark`) on no
  frame, for every `cS`.
-/
import Spike.Lib.A64HelloFlagZ
import Spike.Lib.A64HelloWorkerSegR
import Spike.Lib.HelloW1Print
import Spike.Lib.HelloEmitSrc
import Spike.Lib.WakeLabMapped

namespace Spike.Lib.A64.Flow.Worker.Hello.FlagSrc

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.WorkerSrc
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSplit (envP wcP workerRestH workerCallH)
open Spike.Lib.HelloW1 (uFrame)
open Spike.Lib.WakeMappedRow (LabPtr)
open Spike.Lib.WakeLabMapped (ptr_of_store)
open Spike.Lib.A64.Flow.Worker.Hello.FlagZ (FlagF)

/-! ## `print`'s terms -/

/-- **`print`'s and `printL`'s terms** (`HelloEmitPh.PTermE`'s set). -/
def PTermP (e : Expr) : Prop :=
  e ∈ PrintSvc.printTerms PrintSrc.printBody ∨ e ∈ PrintSvc.printTerms HelloPrintSrcPub.printLBodyP

/-- **`print`'s terms are closed under a local step** (`HelloW1.pTermT_step`'s last two cases). -/
theorem pTermP_step {c c' : Ctl} (h : LocalStepS helloSrc c c') (ht : PTermP c.term) : PTermP c'.term := by
  rcases ht with ht | ht
  · rcases HelloW1.localStepS_shapeH h (HelloW1.printShape_printBody.mem ht) with h' | h'
    · exact .inl (PrintSvc.printTerms_trans ht h')
    · exact .inr (by rw [h']; exact PrintSvc.self_mem_printTerms _)
  · rcases HelloW1.localStepS_shapeH h (HelloW1.printShape_printLBodyP.mem ht) with h' | h'
    · exact .inr (PrintSvc.printTerms_trans ht h')
    · exact .inr (by rw [h']; exact PrintSvc.self_mem_printTerms _)

/-- A term binding none of the accesses `LabPtr` counts: no acquire load, no release store, no
exchange (`printL`'s element load is plain). -/
def noLabB : Expr → Bool
  | .let_ _ (.load true _) _ => false
  | .let_ _ (.store true _ _ _) _ => false
  | .let_ _ (.xchg ..) _ => false
  | .let_ _ (.xchgAt ..) _ => false
  | _ => true

/-- A term binding no call. -/
def noCallB : Expr → Bool
  | .let_ _ (.call ..) _ => false
  | _ => true

theorem pTermP_noLab {e : Expr} (h : PTermP e) : noLabB e = true := by
  have h1 : (PrintSvc.printTerms PrintSrc.printBody).all noLabB = true := by decide
  have h2 : (PrintSvc.printTerms HelloPrintSrcPub.printLBodyP).all noLabB = true := by decide
  rcases h with h | h
  · exact List.all_eq_true.1 h1 e h
  · exact List.all_eq_true.1 h2 e h

theorem pTermP_noCall {e : Expr} (h : PTermP e) : noCallB e = true := by
  have h1 : (PrintSvc.printTerms PrintSrc.printBody).all noCallB = true := by decide
  have h2 : (PrintSvc.printTerms HelloPrintSrcPub.printLBodyP).all noCallB = true := by decide
  rcases h with h | h
  · exact List.all_eq_true.1 h1 e h
  · exact List.all_eq_true.1 h2 e h

/-- **No `LabPtr` at a control whose term binds no load, store or exchange.** -/
theorem noPtr_noLab {c : Ctl} (h : noLabB c.term = true) : ∀ sa, ¬ LabPtr c sa := by
  rintro sa (⟨x, a, e, -, -, (ht | ⟨b, ht⟩), -⟩ | ⟨x, u, v, e, -, (⟨a, -, -, -, ht, -⟩ |
      ⟨b, i, -, -, -, -, -, -, -, ht, -⟩)⟩) <;> rw [ht] at h <;> simp [noLabB] at h

/-- **No `LabPtr` inside `print`.** -/
theorem noPtr_pTermP {c : Ctl} (h : PTermP c.term) : ∀ sa, ¬ LabPtr c sa :=
  noPtr_noLab (pTermP_noLab h)

/-! ## The store after `print`'s return -/

/-- **The worker after `print`'s return** with result words `ws`: at its store, `u` bound. -/
def wcRE (w0 w1 w2 w3 w4 : TermRun.Word) (ws : List TermRun.Word) : Ctl :=
  ⟨workerRestH, ("u", .unit, ws) :: envP w0 w1 w2 w3 w4, none⟩

theorem wcRE_c (w0 w1 w2 w3 w4 : TermRun.Word) (ws : List TermRun.Word) :
    TermRun.evalAt (wcRE w0 w1 w2 w3 w4 ws).env (.var "c") = some (.ptr .pub .int, [w3]) := by
  simp [wcRE, envP, TermRun.evalAt, TermRun.lookupE]

/-- **The store takes no local step** (it pushes a message; `HelloW1.wkStore_noStep`'s argument, with
only `c` bound). -/
theorem wcRE_noStep {cS : WeakMem.Address} {w0 w1 w2 w3 w4 : TermRun.Word} (hcS : w3.val = .loc cS 0)
    {ws : List TermRun.Word} {c₁ : Ctl} (h : LocalStepS helloSrc (wcRE w0 w1 w2 w3 w4 ws) c₁) : False := by
  let g : TermRun.G := { p := helloSrc, k := Promises.Knobs.all, arch := .arm, n := 2, i := 1, lbase := 0 }
  let th : TermRun.TTh := { term := (wcRE w0 w1 w2 w3 w4 ws).term, env := (wcRE w0 w1 w2 w3 w4 ws).env }
  have hA : AtStore w3 cS th := ⟨rfl, rfl, rfl, ⟨.ptr .pub .int, .pub, .int, wcRE_c w0 w1 w2 w3 w4 ws, rfl, rfl⟩, hcS⟩
  obtain ⟨th1, hs, -⟩ := stepStore_append_mem g.k g.arch #[] (TermRun.mth (TermRun.stOf #[] [] th) w3 one one) cS
    (TermRun.dataE 1 one) [0] true
  have hm := atStore_tstep (g := g) (pairs := []) hA hs
  rw [h.2 g #[] [] th rfl rfl rfl rfl] at hm
  simp only [List.mem_singleton, Prod.mk.injEq] at hm
  have := congrArg Array.size hm.1
  simp at this

/-- **At the store, every `LabPtr` is to the flag.** -/
theorem ptr_wcRE {cS : WeakMem.Address} {w0 w1 w2 w3 w4 : TermRun.Word} (hcS : w3.val = .loc cS 0)
    (ws : List TermRun.Word) : ∀ sa, LabPtr (wcRE w0 w1 w2 w3 w4 ws) sa → sa = cS :=
  ptr_of_store rfl (wcRE_c w0 w1 w2 w3 w4 ws) hcS

/-! ## The invariant along frame runs -/

/-- **The worker's pairs from `print`'s call on**: the call on no frame; inside `print` on the call's
frame; at the store after `print`'s return on no frame. -/
def Inv (w0 w1 w2 w3 w4 : TermRun.Word) (q : Ctl × List TermRun.Frame) : Prop :=
  q = (wcP w0 w1 w2 w3 w4, []) ∨ (PTermP q.1.term ∧ q.2 = [uFrame w0 w1 w2 w3 w4]) ∨
    ∃ ws, q = (wcRE w0 w1 w2 w3 w4 ws, [])

/-- **`Inv` is kept by a frame step.** -/
theorem inv_step {cS : WeakMem.Address} {w0 w1 w2 w3 w4 : TermRun.Word} (hcS : w3.val = .loc cS 0)
    {q q₁ : Ctl × List TermRun.Frame} (hs : FrameStep helloSrc q q₁) (hq : Inv w0 w1 w2 w3 w4 q) :
    Inv w0 w1 w2 w3 w4 q₁ := by
  rcases hq with rfl | ⟨ht, hfs⟩ | ⟨ws, rfl⟩
  · cases hs with
    | loc hl => exact (HelloEmitSrc.wcP_noStep hl).elim
    | call hc hd _ =>
      simp only [wcP, workerCallH, Expr.let_.injEq, Op.call.injEq] at hc
      obtain ⟨rfl, ⟨rfl, -, -, -⟩, rfl⟩ := hc
      rw [HelloPrintSrcPub.printPD_find] at hd
      cases hd
      exact .inr (.inl ⟨.inl (PrintSvc.self_mem_printTerms _), rfl⟩)
  · obtain ⟨c, fs⟩ := q
    simp only at ht hfs
    subst hfs
    cases hs with
    | loc hl => exact .inr (.inl ⟨pTermP_step hl ht, rfl⟩)
    | call hc =>
      have h := pTermP_noCall ht
      rw [hc] at h
      simp [noCallB] at h
    | ret => exact .inr (.inr ⟨_, rfl⟩)
  · cases hs with
    | loc hl => exact (wcRE_noStep hcS hl).elim
    | call hc => simp [wcRE, workerRestH] at hc

/-- **`Inv` is kept by a frame run.** -/
theorem inv_run {cS : WeakMem.Address} {w0 w1 w2 w3 w4 : TermRun.Word} (hcS : w3.val = .loc cS 0)
    {q q' : Ctl × List TermRun.Frame} (hr : FrameRun helloSrc q q') (hq : Inv w0 w1 w2 w3 w4 q) :
    Inv w0 w1 w2 w3 w4 q' := by
  induction hr with
  | refl => exact hq
  | step hs _ ih => exact ih (inv_step hcS hs hq)

/-- **Under `Inv`, every `LabPtr` is to the flag.** -/
theorem ptr_inv {cS : WeakMem.Address} {w0 w1 w2 w3 w4 : TermRun.Word} (hcS : w3.val = .loc cS 0)
    {q : Ctl × List TermRun.Frame} (hq : Inv w0 w1 w2 w3 w4 q) : ∀ sa, LabPtr q.1 sa → sa = cS := by
  rcases hq with rfl | ⟨ht, -⟩ | ⟨ws, rfl⟩
  · exact fun sa h => (noPtr_noLab (c := wcP w0 w1 w2 w3 w4) rfl sa h).elim
  · exact fun sa h => (noPtr_pTermP ht sa h).elim
  · exact ptr_wcRE hcS ws

/-- **`FlagF` from `Inv`.** -/
theorem flagF_inv {cS : WeakMem.Address} {w0 w1 w2 w3 w4 : TermRun.Word} (hcS : w3.val = .loc cS 0)
    {c : Ctl} {fs : List TermRun.Frame} (hq : Inv w0 w1 w2 w3 w4 (c, fs)) (s : State) : FlagF cS s c fs :=
  fun _ _ hr => ptr_inv hcS (inv_run hcS hr hq)

/-! ## The flag at the worker's controls -/

/-- **The flag at `print`'s call.** -/
theorem flagF_wcP {cS : WeakMem.Address} {w0 w1 w2 w3 w4 : TermRun.Word} (hcS : w3.val = .loc cS 0)
    (s : State) : FlagF cS s (wcP w0 w1 w2 w3 w4) [] :=
  flagF_inv hcS (.inl rfl) s

/-- **The flag inside `print`**, on the call's frame. -/
theorem flagF_pTerm {cS : WeakMem.Address} {w0 w1 w2 w3 w4 : TermRun.Word} (hcS : w3.val = .loc cS 0)
    {c : Ctl} (ht : PTermP c.term) (s : State) : FlagF cS s c [uFrame w0 w1 w2 w3 w4] :=
  flagF_inv hcS (.inr (.inl ⟨ht, rfl⟩)) s

/-- **The flag at the store** after `print`'s return. -/
theorem flagF_wcRE {cS : WeakMem.Address} {w0 w1 w2 w3 w4 : TermRun.Word} (hcS : w3.val = .loc cS 0)
    (ws : List TermRun.Word) (s : State) : FlagF cS s (wcRE w0 w1 w2 w3 w4 ws) [] :=
  flagF_inv hcS (.inr (.inr ⟨ws, rfl⟩)) s

/-- **The flag at `ret ()` after `unpark`, on no frame** (source half): the only frame
run is empty (`ret` takes no local step, and there is no frame to return into), and `ret` accesses
nothing. Any `cS`. -/
theorem flagF_cS2 (cS : WeakMem.Address) (w0 w1 w2 w3 w4 : TermRun.Word) (s : State) :
    FlagF cS s (SegR.cS2 w0 w1 w2 w3 w4) [] := by
  intro c₁ fs₁ hr sa h
  cases hr with
  | refl => exact (noPtr_noLab (c := SegR.cS2 w0 w1 w2 w3 w4) rfl sa h).elim
  | step hs _ =>
    cases hs with
    | loc hl => exact (hl.not_ret _ rfl).elim
    | call hc => simp [SegR.cS2] at hc

end Spike.Lib.A64.Flow.Worker.Hello.FlagSrc

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.FlagSrc.flagF_wcP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.FlagSrc.flagF_wcP

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.FlagSrc.flagF_pTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.FlagSrc.flagF_pTerm

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.FlagSrc.flagF_cS2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.FlagSrc.flagF_cS2
