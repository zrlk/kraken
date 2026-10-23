/-
**The overflow abort path's site premises from the placement check**
(AArch64): the premises of `userCallW_main` (`Spike/Lib/LowerA64/AbortCall.lean`)
about the abort code and the overflow stub's exit call, at the runtime's
layout of an output passing `placeOK` (`RuntimeLayout.ofPlaceOK`) and its
phase record (`Spike/Lib/A64PhRec.lean`).

- `sites7`: A6's seven site labels resolve, at distinct addresses.
- `lab_toNat`: a resolved code label's address is its `codeOf` address.
- `hprog_ofPlaceOK`: the abort code (A7, `abortIn_of_placeOKAt`).
- `hrel_ofPlaceOK`, `htk_ofPlaceOK`: the exit call is off the release and
  take sites.
- `hk_ofPlaceOK`: no other abort kind's site is the exit call.
- `hKex_ofPlaceOK`: no outside move (the take) at the exit call.
- `hms_ofPlaceOK`: the placement's memory side (`msOf`) aborts at the exit
  call (its kernel is the ABI by `rfl`).
- `userCallW_main_ofPlaceOK`: `userCallW_main` at the record, these premises
  discharged (with `abortPhOk_ofPlaceOK`, A7).
-/
import Spike.Lib.LowerA64.AbortCall
import Spike.Lib.A64PhRec

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Link.A64 (linkOf codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.PhRec (μ K)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)
include h

/-- **A6's sites resolve at distinct addresses**: the take and release sites
and the five abort kinds' exit calls. -/
theorem sites7 : ∃ t r ov he st wr th : Nat,
    codeOf Λ.code.lo o.prog "scc_rt_take_site" = some t ∧
    codeOf Λ.code.lo o.prog "scc_rt_release_site" = some r ∧
    codeOf Λ.code.lo o.prog "scc_rt_abort_overflow_exit" = some ov ∧
    codeOf Λ.code.lo o.prog "scc_rt_abort_heap_exit" = some he ∧
    codeOf Λ.code.lo o.prog "scc_rt_abort_stack_exit" = some st ∧
    codeOf Λ.code.lo o.prog "scc_rt_abort_write_exit" = some wr ∧
    codeOf Λ.code.lo o.prog "scc_rt_abort_threads_exit" = some th ∧
    [t, r, ov, he, st, wr, th].Nodup := by
  obtain ⟨ss, hs, hnd⟩ := Scc.Cert.Rt.A64.sites_nodup_of_phasesOk (phasesOk_of_placeOKAt h)
  have hl : Λ.abortLbl = Scc.Cert.Link.abortName := abortLbl_of_placeOKAt h
  simp only [Scc.Cert.Rt.A64.sitesOf, Scc.Cert.Rt.A64.sitesBy, Scc.Cert.Rt.A64.siteLabels, hl, List.map_cons,
    List.map_nil, Scc.Cert.Link.abortName, List.cons_append, List.nil_append, List.mapM_cons, List.mapM_nil,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hs
  obtain ⟨t, ht, _, ⟨r, hr, _, ⟨ov, hov, _, ⟨he, hhe, _, ⟨st, hst, _, ⟨wr, hwr, _, ⟨th, hth, _, rfl, rfl⟩, rfl⟩,
    rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hs
  exact ⟨t, r, ov, he, st, wr, th, ht, hr, hov, hhe, hst, hwr, hth, hnd⟩

/-- **An abort kind's site is its exit call's `codeOf` address**: the
record's abort labels are `Link.abortName`'s (`abortLbl_of_placeOKAt`). -/
theorem abortAt_eq (k : Scc.Sem.AbortKind) :
    (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = codeOf Λ.code.lo o.prog (Scc.Cert.Link.abortName k) := by
  show codeOf Λ.code.lo o.prog (Λ.abortLbl k) = _
  rw [abortLbl_of_placeOKAt h]

/-- **A resolved code label's address** in the loaded thread is its
`codeOf` address (below `2 ^ 64`, `codeEnd_lt`). -/
theorem lab_toNat {l : String} {a : Nat} (ha : codeOf Λ.code.lo o.prog l = some a) :
    ((RuntimeLayout.ofPlaceOK h i).lab l).toBitVec.toNat = a := by
  have hlab := Scc.Cert.Rt.A64.label_threadAt_of_codeOf (E := Scc.Sem.Entry.linux)
    (syms := Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)
    (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK_above h i) ha
  have hlt : a < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Spike.Lib.A64.PhRec.le_codeEnd_of_codeOf ha) (Spike.Lib.A64.PhRec.codeEnd_lt h i)
  have hlab' : (RuntimeLayout.ofPlaceOK h i).lab l = Int64.ofNat a := hlab
  rw [hlab']
  simp [Nat.mod_eq_of_lt hlt]

/-- The overflow exit call's address is its `codeOf` address. -/
theorem ovf_toNat {a : Nat}
    (ha : codeOf Λ.code.lo o.prog "scc_rt_abort_overflow_exit" = some a) :
    ((RuntimeLayout.ofPlaceOK h i).lab A64.Abort.overflow.exit).toBitVec.toNat = a :=
  lab_toNat h i ha

/-- **`hprog`**: the abort code (A7). -/
theorem hprog_ofPlaceOK : Scc.Cert.Rt.A64.Abort.abortIn (RuntimeLayout.ofPlaceOK h i).prog = true :=
  abortIn_of_placeOKAt h

/-- **`hrel`**: the overflow exit call is off the release site. -/
theorem hrel_ofPlaceOK : ∀ a, (μ (RuntimeLayout.ofPlaceOK h i)).site .release = some a →
    ((RuntimeLayout.ofPlaceOK h i).lab A64.Abort.overflow.exit).toBitVec.toNat ≠ a := by
  obtain ⟨t, r, ov, he, st, wr, th, -, hr, hov, -, -, -, -, hnd⟩ := sites7 h
  intro a ha
  change codeOf Λ.code.lo o.prog "scc_rt_release_site" = some a at ha
  rw [hr] at ha
  cases ha
  rw [ovf_toNat h i hov]
  rintro rfl
  simp at hnd

/-- **`htk`**: the overflow exit call is off the take site. -/
theorem htk_ofPlaceOK : ∀ a, (μ (RuntimeLayout.ofPlaceOK h i)).site .take = some a →
    ((RuntimeLayout.ofPlaceOK h i).lab A64.Abort.overflow.exit).toBitVec.toNat ≠ a := by
  obtain ⟨t, r, ov, he, st, wr, th, ht, -, hov, -, -, -, -, hnd⟩ := sites7 h
  intro a ha
  change codeOf Λ.code.lo o.prog "scc_rt_take_site" = some a at ha
  rw [ht] at ha
  cases ha
  rw [ovf_toNat h i hov]
  rintro rfl
  simp at hnd

/-- **`hk`**: the overflow exit call is no other abort kind's site. -/
theorem hk_ofPlaceOK : ∀ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a →
    ((RuntimeLayout.ofPlaceOK h i).lab A64.Abort.overflow.exit).toBitVec.toNat = a → k = .overflow := by
  obtain ⟨t, r, ov, he, st, wr, th, -, -, hov, hhe, hst, hwr, hth, hnd⟩ := sites7 h
  intro k a ha hx
  rw [ovf_toNat h i hov] at hx
  subst hx
  cases k with
  | overflow => rfl
  | heap =>
    rw [abortAt_eq h i] at ha
    change codeOf Λ.code.lo o.prog "scc_rt_abort_heap_exit" = some ov at ha
    rw [hhe] at ha; cases ha; simp at hnd
  | stack =>
    rw [abortAt_eq h i] at ha
    change codeOf Λ.code.lo o.prog "scc_rt_abort_stack_exit" = some ov at ha
    rw [hst] at ha; cases ha; simp at hnd
  | threads =>
    rw [abortAt_eq h i] at ha
    change codeOf Λ.code.lo o.prog "scc_rt_abort_threads_exit" = some ov at ha
    rw [hth] at ha; cases ha; simp at hnd
  | writeErr =>
    rw [abortAt_eq h i] at ha
    change codeOf Λ.code.lo o.prog "scc_rt_abort_write_exit" = some ov at ha
    rw [hwr] at ha; cases ha; simp at hnd

/-- **`hKex`**: no outside move (the take, at the take site) at the overflow
exit call. -/
theorem hKex_ofPlaceOK {rS : Scc.Sem.Range} : ∀ s s', Scc.Sem.A64.pcOf s =
    ((RuntimeLayout.ofPlaceOK h i).lab A64.Abort.overflow.exit).toBitVec.toNat →
    ¬ K (RuntimeLayout.ofPlaceOK h i) rS s s' := by
  obtain ⟨t, r, ov, he, st, wr, th, ht, -, hov, -, -, -, -, hnd⟩ := sites7 h
  intro s s' hpc hK
  rw [Scc.Sem.A64.pcOf, Spike.Lib.A64.Flow.Ret0.TakeK.pc hK, lab_toNat h i (l := "scc_rt_take_site") ht,
    ovf_toNat h i hov] at hpc
  subst hpc
  simp at hnd

/-- **`hms`**: the placement's memory side aborts at the overflow exit call
(its overflow abort site). -/
theorem hms_ofPlaceOK {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : Spike.Lib.A64Consumer.Own}
    {lbl : Spike.Lib.A64Consumer.Lbl} {lsize : Spike.Lib.A64Consumer.Lsize} :
    ∀ s : State, s.exe = (RuntimeLayout.ofPlaceOK h i).exe →
      s.st.2 = (RuntimeLayout.ofPlaceOK h i).lab A64.Abort.overflow.exit →
      (Spike.Lib.A64Consumer.msOf (RuntimeLayout.ofPlaceOK h i).Λ (μ (RuntimeLayout.ofPlaceOK h i)) rd G own lbl
        lsize).abortAt s := by
  obtain ⟨t, r, ov, he, st, wr, th, -, -, hov, -, -, -, -, -⟩ := sites7 h
  intro s _ hs
  refine ⟨.overflow, ov, (abortAt_eq h i _).trans hov, ?_⟩
  rw [Scc.Sem.A64.pcOf, hs, ovf_toNat h i hov]

open Scc.Lower.InvA64 Scc.Emit.A64 in
/-- **`userCallW_main` at the record of an output passing `placeOK`**: the
instance's facts (`instOk_ofPlaceOK`), the abort code, the abort path's
phase check (`abortPhOk_ofPlaceOK`, A7) and the overflow exit call's site
premises discharged, under the placement's memory side
(`msOf`). The lowered function's code and phases, the immediates, the
frame condition, the limit word and the write tail stay premises. -/
theorem userCallW_main_ofPlaceOK {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true) {cx : FnCtx}
    {r : Scc.Lower.Inv.Res} {fn entry : Label} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hpro : proInC o.prog cx fn entry = true) (hr : Scc.Lower.Inv.lower0 [(d.arg, .unit, [])] 0 d.body = some r)
    (hbody : bodyIn o.prog cx entry 0 r.insts r.ret = true) {rS : Scc.Sem.Range} {Dt : State → Prop}
    {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {lbl : Spike.Lib.A64Consumer.Lbl}
    {lsize : Spike.Lib.A64Consumer.Lsize} {R : Region} {F : MachineData → Prop} {Z : Int64} {D : Int}
    {tp : UInt64} {ra : BitVec 64} (hD : (cx.frame : Int) + 48 ≤ D) (hD8 : D % 8 = 0)
    (hphB : bodyPhOk (Spike.Lib.A64.PhRec.okPc (RuntimeLayout.ofPlaceOK h i))
      (Spike.Lib.A64.PhRec.ph (RuntimeLayout.ofPlaceOK h i)) (fun _ => false) (RuntimeLayout.ofPlaceOK h i).lab cx
      entry r.insts r.ret (Int64.ofBitVec ra) = true)
    (hphP : ProPh (Spike.Lib.A64.PhRec.okPc (RuntimeLayout.ofPlaceOK h i))
      (Spike.Lib.A64.PhRec.ph (RuntimeLayout.ofPlaceOK h i)) (RuntimeLayout.ofPlaceOK h i).lab
      (cx.local "stack_check") (Int64.ofInt cx.frame) (proL cx) [])
    (hC0 : Spike.Lib.A64Consumer.CFacts (RuntimeLayout.ofPlaceOK h i).Λ lbl Spike.Lib.A64Consumer.c0)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (RuntimeLayout.ofPlaceOK h i).Λ) false
      ⟨Spike.Lib.A64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.Ret0.limA tp) 8 = none)
    (hsub : rS.Sub (RuntimeLayout.ofPlaceOK h i).Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → Spike.Lib.A64.Flow.Ret0.CallerCells R (-Z.toInt) (-D) 0 m →
      Spike.Lib.A64.Flow.Ret0.StackOff rS (R.callee (-Z.toInt) (-D) 0) m)
    (hab : r.insts ≠ [] → Scc.Cert.Rt.A64.blockAt o.prog (cx.local "abort_overflow") 0 ovfBlk = true ∧
      Spike.Lib.A64Consumer.blkPh (Spike.Lib.A64.PhRec.okPc (RuntimeLayout.ofPlaceOK h i))
        (Spike.Lib.A64.PhRec.ph (RuntimeLayout.ofPlaceOK h i)) (fun _ => false) (RuntimeLayout.ofPlaceOK h i).lab
        ((RuntimeLayout.ofPlaceOK h i).lab (cx.local "abort_overflow") + Int64.ofNat (4 * 0)) 0
        A64.Abort.Local.lb = true)
    (himm : i = Spike.Lib.LowerNode.immsOf d)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop), R'.base.toNat % 16 = 0 → R'.lo ≤ -48 → 0 ≤ R'.hi →
      ∀ c s c', At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R' F'
        (A64.Abort.N (RuntimeLayout.ofPlaceOK h i).lab A64.Abort.overflow c .svc) s c' → Dt s) :
    Spike.Lib.A64.Rt.UserCallW (fun s c => Spike.Lib.A64Consumer.SFacts (RuntimeLayout.ofPlaceOK h i).Λ
        (μ (RuntimeLayout.ofPlaceOK h i)) (Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.A64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) lbl s c Dt)
      (K (RuntimeLayout.ofPlaceOK h i) rS) [d] lbl
      (Spike.Lib.A64Consumer.msOf (RuntimeLayout.ofPlaceOK h i).Λ (μ (RuntimeLayout.ofPlaceOK h i)) rd G
        (Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) lbl lsize)
      (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R F fn Z D
      (Int64.ofInt cx.frame) (UPost [d] lbl Spike.Lib.A64Consumer.c0) ra Spike.Lib.A64Consumer.c0 tp :=
  userCallW_main hd hf h1 h16 hpro hr hbody (Spike.Lib.A64.PhRec.instOk_ofPlaceOK h i) hD hD8 hphB hphP hC0 hmr
    hun hsub hfit hFO hab (hprog_ofPlaceOK h i) (Spike.Lib.A64.PhRec.abortPhOk_ofPlaceOK h i) himm
    (hrel_ofPlaceOK h i) (htk_ofPlaceOK h i)
    (hk_ofPlaceOK h i) (hKex_ofPlaceOK h i) (hms_ofPlaceOK h i) rfl hwr

end Place

end Spike.Lib.LowerA64
