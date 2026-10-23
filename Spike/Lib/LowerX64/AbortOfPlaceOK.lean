/-
**The overflow abort path's premises from the placement check** (x86-64):
the premises of `userCallW_main` (`Spike/Lib/LowerX64/AbortCall.lean`)
about the abort code and the overflow stub's exit call, at the runtime's
layout of an output passing `placeOK` (`RuntimeLayout.ofPlaceOK`) and its
phase record (`Spike/Lib/X64PhRec.lean`). The twin of
`Spike/Lib/LowerA64/AbortOfPlaceOK.lean`.

- `lab_toNat`: a resolved code label's address is its `codeLabel` address.
- `ovf_codeLabel`: the overflow exit call's label resolves (A3, `abortsIn`).
- `hprog_ofPlaceOK`: the abort code (A7, `abortIn_of_placeOKAt`).
- `hsysIn_ofPlaceOK`: the overflow stub's `write` call (A7's `stubIn`).
- `sites7`: A6's seven site labels resolve, at distinct addresses
  (`sites_nodup_of_placeOKAt`).
- `hrel_ofPlaceOK`, `htk_ofPlaceOK`: the exit call is off the release and
  take sites.
- `hk_ofPlaceOK`: no other abort kind's site is the exit call.
- `hKex_ofPlaceOK`: no outside move (the take) at the exit call.
- `hms_ofPlaceOK`: the placement's memory side (`msOf`) aborts at the exit
  call (its kernel is the ABI by `rfl`).
- `userCallW_main_ofPlaceOK`: `userCallW_main` at the record, these premises
  and the abort path's phase check (`abortPhOk_ofPlaceOK`, A7) discharged.

**Unlike AArch64**: the stub's `write` call is discharged here (AArch64
reads it off the abort code inside the stub's proof).
-/
import Spike.Lib.LowerX64.AbortCall
import Spike.Lib.X64PhRec

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Lower.InvX64
open Scc.Emit.X64 (labelOf)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Cert.Link.X64 (linkOf)
open Scc.Sem.X64 (codeLabel)
open Scc.Lower.Inv (lower0 Res)
open Spike.Lib.X64Consumer (CFacts SFacts Lbl Lsize Own K0 blkPh msOf)
open Spike.Lib.X64.Rt (RuntimeLayout UserCallW)
open Spike.Lib.X64.Flow.Ret0 (StackOff CallerCells limA)
open Spike.Lib.X64.PhRec (μ K)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)
include h

/-- **A resolved code label's address** in the loaded thread is its
`codeLabel` address (below `2 ^ 64`, `codeEnd_lt`). -/
theorem lab_toNat {l : String} {a : Nat} (ha : codeLabel (Λ).code.lo o.prog l = some a) :
    ((RuntimeLayout.ofPlaceOK h i).lab l).toBitVec.toNat = a := by
  haveI : Kraken.Executable.ValidLayout (Scc.Sem.X64.threadAt Scc.Sem.Entry.linux (Λ).code.lo
      o.prog (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)).exe :=
    (RuntimeLayout.ofPlaceOK h i).valid
  have hlab := Scc.Cert.Rt.X64.label_threadAt_of_codeLabel (E := Scc.Sem.Entry.linux)
    (syms := Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)
        (by exact Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK_above h i) ha
  have hlt : a < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Spike.Lib.X64.PhRec.le_codeEnd_of_codeLabel ha) (Spike.Lib.X64.PhRec.codeEnd_lt h i)
  have hlab' : (RuntimeLayout.ofPlaceOK h i).lab l = Int64.ofNat a := hlab
  rw [hlab']
  simp [Nat.mod_eq_of_lt hlt]

/-- **The overflow exit call's label resolves** (A3: every abort label is
a code label). -/
theorem ovf_codeLabel : ∃ a, codeLabel (Λ).code.lo o.prog Abort.overflow.exit = some a := by
  have ha := abortsIn_of_placeOKAt h
  simp only [Scc.Cert.Link.X64.abortsIn, List.all_eq_true] at ha
  have ho := ha .overflow (by simp [Scc.Cert.Link.kinds])
  rw [abortLbl_of_placeOKAt h] at ho
  exact Option.isSome_iff_exists.mp ho

/-- **The record's abort sites are the abort names' code labels** (A2's
`abortLbl`, `abortLbl_of_placeOKAt`). -/
theorem abortAt_eq (k : Scc.Sem.AbortKind) :
    (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = codeLabel (Λ).code.lo o.prog (Scc.Cert.Link.abortName k) := by
  show codeLabel (Λ).code.lo o.prog (Λ.abortLbl k) = _
  rw [abortLbl_of_placeOKAt h]

/-- **`hprog`**: the abort code (A7). -/
theorem hprog_ofPlaceOK : Scc.Cert.Rt.X64.Abort.abortIn (RuntimeLayout.ofPlaceOK h i).prog = true :=
  abortIn_of_placeOKAt h

/-- **`hsysIn`**: the overflow stub's `write` call, 34 bytes after its
entry (A7's `stubIn`). -/
theorem hsysIn_ofPlaceOK :
    Scc.Cert.Rt.X64.blockAtB (RuntimeLayout.ofPlaceOK h i).prog Abort.overflow.entry 34 [(op64 .syscall, 2)] =
      true := by
  have hp := hprog_ofPlaceOK h i
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Scc.Cert.Rt.X64.Abort.stubIn, Bool.and_eq_true] at hp
  exact hp.1.1.1.1.1.1.1.1.1.2

/-- **The sites resolve at distinct addresses**: the take and release sites
and the five abort kinds' exit calls. -/
theorem sites7 : ∃ t r ov he st wr th : Nat,
    codeLabel (Λ).code.lo o.prog "scc_rt_take_site" = some t ∧
    codeLabel (Λ).code.lo o.prog "scc_rt_release_site" = some r ∧
    codeLabel (Λ).code.lo o.prog "scc_rt_abort_overflow_exit" = some ov ∧
    codeLabel (Λ).code.lo o.prog "scc_rt_abort_heap_exit" = some he ∧
    codeLabel (Λ).code.lo o.prog "scc_rt_abort_stack_exit" = some st ∧
    codeLabel (Λ).code.lo o.prog "scc_rt_abort_write_exit" = some wr ∧
    codeLabel (Λ).code.lo o.prog "scc_rt_abort_threads_exit" = some th ∧
    [t, r, ov, he, st, wr, th].Nodup := by
  obtain ⟨ss, hs, hnd⟩ := sites_nodup_of_placeOKAt h
  have hl : (Λ).abortLbl = Scc.Cert.Link.abortName := abortLbl_of_placeOKAt h
  simp only [Scc.Cert.Rt.X64.sitesOf, Scc.Cert.Rt.X64.sitesBy, Scc.Cert.Rt.X64.siteLabels, hl, List.map_cons,
    List.map_nil, Scc.Cert.Link.abortName, List.cons_append, List.nil_append, List.mapM_cons, List.mapM_nil,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hs
  obtain ⟨t, ht, _, ⟨r, hr, _, ⟨ov, hov, _, ⟨he, hhe, _, ⟨st, hst, _, ⟨wr, hwr, _, ⟨th, hth, _, rfl, rfl⟩, rfl⟩,
    rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hs
  exact ⟨t, r, ov, he, st, wr, th, ht, hr, hov, hhe, hst, hwr, hth, hnd⟩

/-- The overflow exit call's address is its `codeLabel` address. -/
theorem ovf_toNat {a : Nat}
    (ha : codeLabel (Λ).code.lo o.prog "scc_rt_abort_overflow_exit" = some a) :
    ((RuntimeLayout.ofPlaceOK h i).lab Abort.overflow.exit).toBitVec.toNat = a :=
  lab_toNat h i ha

/-- **`hrel`**: the overflow exit call is off the release site. -/
theorem hrel_ofPlaceOK : ∀ a, (μ (RuntimeLayout.ofPlaceOK h i)).site .release = some a →
    ((RuntimeLayout.ofPlaceOK h i).lab Abort.overflow.exit).toBitVec.toNat ≠ a := by
  obtain ⟨t, r, ov, he, st, wr, th, -, hr, hov, -, -, -, -, hnd⟩ := sites7 h
  intro a ha
  change codeLabel (Λ).code.lo o.prog "scc_rt_release_site" = some a at ha
  rw [hr] at ha
  cases ha
  rw [ovf_toNat h i hov]
  rintro rfl
  simp at hnd

/-- **`htk`**: the overflow exit call is off the take site. -/
theorem htk_ofPlaceOK : ∀ a, (μ (RuntimeLayout.ofPlaceOK h i)).site .take = some a →
    ((RuntimeLayout.ofPlaceOK h i).lab Abort.overflow.exit).toBitVec.toNat ≠ a := by
  obtain ⟨t, r, ov, he, st, wr, th, ht, -, hov, -, -, -, -, hnd⟩ := sites7 h
  intro a ha
  change codeLabel (Λ).code.lo o.prog "scc_rt_take_site" = some a at ha
  rw [ht] at ha
  cases ha
  rw [ovf_toNat h i hov]
  rintro rfl
  simp at hnd

/-- **`hk`**: the overflow exit call is no other abort kind's site. -/
theorem hk_ofPlaceOK : ∀ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a →
    ((RuntimeLayout.ofPlaceOK h i).lab Abort.overflow.exit).toBitVec.toNat = a → k = .overflow := by
  obtain ⟨t, r, ov, he, st, wr, th, -, -, hov, hhe, hst, hwr, hth, hnd⟩ := sites7 h
  intro k a ha hx
  rw [ovf_toNat h i hov] at hx
  subst hx
  cases k with
  | overflow => rfl
  | heap =>
    rw [abortAt_eq h i] at ha
    change codeLabel (Λ).code.lo o.prog "scc_rt_abort_heap_exit" = some ov at ha
    rw [hhe] at ha; cases ha; simp at hnd
  | stack =>
    rw [abortAt_eq h i] at ha
    change codeLabel (Λ).code.lo o.prog "scc_rt_abort_stack_exit" = some ov at ha
    rw [hst] at ha; cases ha; simp at hnd
  | threads =>
    rw [abortAt_eq h i] at ha
    change codeLabel (Λ).code.lo o.prog "scc_rt_abort_threads_exit" = some ov at ha
    rw [hth] at ha; cases ha; simp at hnd
  | writeErr =>
    rw [abortAt_eq h i] at ha
    change codeLabel (Λ).code.lo o.prog "scc_rt_abort_write_exit" = some ov at ha
    rw [hwr] at ha; cases ha; simp at hnd

/-- **`hKex`**: no outside move (the take, at the take site) at the overflow
exit call. -/
theorem hKex_ofPlaceOK {rS : Scc.Sem.Range} : ∀ s s', Scc.Sem.X64.pcOf s =
    ((RuntimeLayout.ofPlaceOK h i).lab Abort.overflow.exit).toBitVec.toNat →
    ¬ K (RuntimeLayout.ofPlaceOK h i) rS s s' := by
  obtain ⟨t, r, ov, he, st, wr, th, ht, -, hov, -, -, -, -, hnd⟩ := sites7 h
  intro s s' hpc hK
  rw [Scc.Sem.X64.pcOf, Spike.Lib.X64.Flow.Ret0.TakeK.pc hK, lab_toNat h i (l := "scc_rt_take_site") ht,
    ovf_toNat h i hov] at hpc
  subst hpc
  simp at hnd

/-- **`hms`**: the placement's memory side aborts at the overflow exit call
(its overflow abort site). -/
theorem hms_ofPlaceOK {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : Own} {lbl : Lbl}
    {lsize : Lsize} :
    ∀ s : State, s.exe = (RuntimeLayout.ofPlaceOK h i).exe →
      s.st.2 = (RuntimeLayout.ofPlaceOK h i).lab Abort.overflow.exit →
      (msOf (RuntimeLayout.ofPlaceOK h i).Λ (μ (RuntimeLayout.ofPlaceOK h i)) rd G own lbl lsize).abortAt s := by
  obtain ⟨a, ha⟩ := ovf_codeLabel h
  intro s _ hs
  refine ⟨.overflow, a, (abortAt_eq h i _).trans ha, ?_⟩
  rw [Scc.Sem.X64.pcOf, hs, lab_toNat h i ha]

/-- **`userCallW_main` at the record of an output passing `placeOK`**: the
instance's facts (`instOk_ofPlaceOK`), the abort code and the stub's
`write` call, the abort path's phase check (`abortPhOk_ofPlaceOK`, A7) and
the memory side's abort site discharged, under the placement's memory side
(`msOf`). The lowered function's code and phases, the immediates, the
frame condition, the limit word and the write tail stay premises; the
exit call's site premises are discharged (`hrel_ofPlaceOK`, `htk_ofPlaceOK`,
`hk_ofPlaceOK`, `hKex_ofPlaceOK`). -/
theorem userCallW_main_ofPlaceOK {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true) {fr : Scc.Emit.X64.Frame}
    {r : Res} {fn entry : Label} {zl zf z1 z2 zs : Nat} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hpro : proInC o.prog fr fn entry zl zf z1 z2 zs = true) (hr : lower0 [(d.arg, .unit, [])] 0 d.body = some r)
    (hbody : bodyIn o.prog fr entry 0 r.insts r.ret = true) {rS : Scc.Sem.Range} {Dt : State → Prop}
    {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {lbl : Lbl} {lsize : Lsize} {R : Region}
    {F : MachineData → Prop} {Z : Int64} {D : Int} {tp : UInt64} {ra : BitVec 64}
    (hR8 : R.base.toNat % 8 = 0) (hZ8 : Z.toInt % 8 = 0) (hD : (fr.size : Int) + 48 ≤ D) (hD8 : D % 8 = 0)
    (hphB : bodyPhOk (Spike.Lib.X64.PhRec.okPc (RuntimeLayout.ofPlaceOK h i))
      (Spike.Lib.X64.PhRec.ph (RuntimeLayout.ofPlaceOK h i)) (fun _ => false) (RuntimeLayout.ofPlaceOK h i).lab
      o.prog fr entry r.insts r.ret (Int64.ofBitVec ra) = true)
    (hphP : ProPh (Spike.Lib.X64.PhRec.okPc (RuntimeLayout.ofPlaceOK h i))
      (Spike.Lib.X64.PhRec.ph (RuntimeLayout.ofPlaceOK h i)) (RuntimeLayout.ofPlaceOK h i).lab fn
      (labelOf fr.fn "chk") (Int64.ofInt fr.size) (proL fr) zl zf z1 z2 zs [])
    (hC0 : CFacts (RuntimeLayout.ofPlaceOK h i).Λ lbl Spike.Lib.X64Consumer.c0)
    (hmr : Scc.Sem.Kernel.mapped (K0 (RuntimeLayout.ofPlaceOK h i).Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub (RuntimeLayout.ofPlaceOK h i).Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m →
      StackOff rS (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) m)
    (hab : r.insts ≠ [] → Scc.Cert.Rt.X64.blockAtB o.prog (ovfL fr) 0 ovfBlk = true ∧
      blkPh (Spike.Lib.X64.PhRec.okPc (RuntimeLayout.ofPlaceOK h i))
        (Spike.Lib.X64.PhRec.ph (RuntimeLayout.ofPlaceOK h i)) (fun _ => false) (RuntimeLayout.ofPlaceOK h i).lab
        ((RuntimeLayout.ofPlaceOK h i).lab (ovfL fr) + Int64.ofNat 0) 0 Abort.Local.lb = true)
    (himm : i = Spike.Lib.LowerNode.immsOf d)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop), R'.lo ≤ -24 → 16 ≤ R'.hi →
      ∀ c s c', At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R' F'
        (Abort.N (RuntimeLayout.ofPlaceOK h i).lab Abort.overflow c .sys) s c' → Dt s) :
    UserCallW (fun s c => SFacts (RuntimeLayout.ofPlaceOK h i).Λ (μ (RuntimeLayout.ofPlaceOK h i))
        (Spike.Lib.X64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.X64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) lbl s c Dt)
      (K (RuntimeLayout.ofPlaceOK h i) rS) [d] lbl
      (msOf (RuntimeLayout.ofPlaceOK h i).Λ (μ (RuntimeLayout.ofPlaceOK h i)) rd G
        (Spike.Lib.X64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) lbl lsize)
      (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R F fn Z D
      (Int64.ofInt fr.size) (UPost [d] lbl Spike.Lib.X64Consumer.c0) ra Spike.Lib.X64Consumer.c0 tp :=
  userCallW_main hd hf h1 hpro hr hbody (Spike.Lib.X64.PhRec.instOk_ofPlaceOK h i) hR8 hZ8 hD hD8 hphB hphP
    hC0 hmr hun hsub hfit hFO hab (hprog_ofPlaceOK h i) (hsysIn_ofPlaceOK h i)
    (Spike.Lib.X64.PhRec.abortPhOk_ofPlaceOK h i) himm (hrel_ofPlaceOK h i) (htk_ofPlaceOK h i)
    (hk_ofPlaceOK h i) (hKex_ofPlaceOK h i) (hms_ofPlaceOK h i) rfl hwr

end Place

end Spike.Lib.LowerX64
