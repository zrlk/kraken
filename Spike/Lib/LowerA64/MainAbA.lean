/-
**`main`'s aborts never end, at the record of an output passing `placeOK`**
(AArch64): the write exit call's site premises at the record (from A6's
sites), and the abort fragment of a user function's body (`MainAb`: the
overflow label, an abort of `print`) as a segment to the empty fragment
inside `W2` at the write abort's phase, at any layout `Λw`. The twin of
`Spike/Lib/LowerX64/MainAbX.lean`.

- `write_toNat`, `hrelW_ofPlaceOK`, `htkW_ofPlaceOK`, `hkW_ofPlaceOK`,
  `hKexW_ofPlaceOK`, `hmsW_ofPlaceOK`: the write exit call's site premises
  (the twins of the heap's in `Spike/Lib/LowerA64/AbortW2Ab.lean`);
- `stubWN_w2_ofPlaceOK`: `stubWN_w2` at the record, at any layout;
- `stubON_w2_ofPlaceOKw`, `stubHN_w2_ofPlaceOKw`: `stubON_w2Ab`, `stubHN_w2Ab`
  at the record, at any layout;
- `ovfAb_seg`: the overflow label of a user function's body never ends;
- `printAb_seg`: an abort of `print` never ends;
- `MainAb`, `mainAb_seg`: the body's aborts, never ending;
- `abortN2_slotRepAt`, `abortN2_slotRepAt_me`: `ovfAb_seg`'s `hJp` from
  `AbJ2` (the abort label's table agreeing with the layout's at the walk's
  terms; at `imms2Me` for a compiled block's walk `TailAt2 p j`).
-/
import Spike.Lib.LowerA64.AbortW2Ab
import Spike.Lib.LowerA64.PrintAbW2
import Spike.Lib.Src.ImmsMeTail

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region FrameRun OvfReady EnvSmall)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At okBlk FStable KStable)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Ret0 (StackOff TakeK takeMem)
open Spike.Lib.LowerNode (FrOk2 ZBad SlotRepAt)
open Spike.Lib.A64.StubW (abortPhWriteOk RefCtl)
open Scc.Emit.A64 (FnCtx)
open Scc.Lower.InvA64 (FrameOk)
open Scc.Cert.Rt.A64 (blockAt)

section Place

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.PhRec (μ K)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)
include h

/-- The write exit call's address is its `codeOf` address. -/
theorem write_toNat {a : Nat}
    (ha : codeOf Λ.code.lo o.prog "scc_rt_abort_write_exit" = some a) :
    ((RuntimeLayout.ofPlaceOK h i).lab A64.Abort.write.exit).toBitVec.toNat = a :=
  lab_toNat h i ha

/-- **`hrel`** (write): the write exit call is off the release site. -/
theorem hrelW_ofPlaceOK : ∀ a, (μ (RuntimeLayout.ofPlaceOK h i)).site .release = some a →
    ((RuntimeLayout.ofPlaceOK h i).lab A64.Abort.write.exit).toBitVec.toNat ≠ a := by
  obtain ⟨t, r, ov, he, st, wr, th, -, hr, -, -, -, hwr, -, hnd⟩ := sites7 h
  intro a ha
  change codeOf Λ.code.lo o.prog "scc_rt_release_site" = some a at ha
  rw [hr] at ha
  cases ha
  rw [write_toNat h i hwr]
  rintro rfl
  simp at hnd

/-- **`htk`** (write): the write exit call is off the take site. -/
theorem htkW_ofPlaceOK : ∀ a, (μ (RuntimeLayout.ofPlaceOK h i)).site .take = some a →
    ((RuntimeLayout.ofPlaceOK h i).lab A64.Abort.write.exit).toBitVec.toNat ≠ a := by
  obtain ⟨t, r, ov, he, st, wr, th, ht, -, -, -, -, hwr, -, hnd⟩ := sites7 h
  intro a ha
  change codeOf Λ.code.lo o.prog "scc_rt_take_site" = some a at ha
  rw [ht] at ha
  cases ha
  rw [write_toNat h i hwr]
  rintro rfl
  simp at hnd

/-- **`hk`** (write): the write exit call is no other abort kind's site. -/
theorem hkW_ofPlaceOK : ∀ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a →
    ((RuntimeLayout.ofPlaceOK h i).lab A64.Abort.write.exit).toBitVec.toNat = a → k = .writeErr := by
  obtain ⟨t, r, ov, he, st, wr, th, -, -, hov, hhe, hst, hwr, hth, hnd⟩ := sites7 h
  intro k a ha hx
  rw [write_toNat h i hwr] at hx
  subst hx
  cases k with
  | writeErr => rfl
  | overflow =>
    rw [abortAt_eq h i] at ha
    change codeOf Λ.code.lo o.prog "scc_rt_abort_overflow_exit" = some wr at ha
    rw [hov] at ha; cases ha; simp at hnd
  | heap =>
    rw [abortAt_eq h i] at ha
    change codeOf Λ.code.lo o.prog "scc_rt_abort_heap_exit" = some wr at ha
    rw [hhe] at ha; cases ha; simp at hnd
  | stack =>
    rw [abortAt_eq h i] at ha
    change codeOf Λ.code.lo o.prog "scc_rt_abort_stack_exit" = some wr at ha
    rw [hst] at ha; cases ha; simp at hnd
  | threads =>
    rw [abortAt_eq h i] at ha
    change codeOf Λ.code.lo o.prog "scc_rt_abort_threads_exit" = some wr at ha
    rw [hth] at ha; cases ha; simp at hnd

/-- **`hKex`** (write): no outside move (the take, at the take site) at
the write exit call. -/
theorem hKexW_ofPlaceOK {rS : Scc.Sem.Range} : ∀ s s', Scc.Sem.A64.pcOf s =
    ((RuntimeLayout.ofPlaceOK h i).lab A64.Abort.write.exit).toBitVec.toNat →
    ¬ K (RuntimeLayout.ofPlaceOK h i) rS s s' := by
  obtain ⟨t, r, ov, he, st, wr, th, ht, -, -, -, -, hwr, -, hnd⟩ := sites7 h
  intro s s' hpc hK
  rw [Scc.Sem.A64.pcOf, Spike.Lib.A64.Flow.Ret0.TakeK.pc hK, lab_toNat h i (l := "scc_rt_take_site") ht,
    write_toNat h i hwr] at hpc
  subst hpc
  simp at hnd

/-- **`hms`** (write): a memory side aborting at every abort site of the
record aborts at the write exit call. -/
theorem hmsW_ofPlaceOK {ms : MemSide isaLSE2}
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      ms.abortAt s) :
    ∀ s : State, s.exe = (RuntimeLayout.ofPlaceOK h i).exe →
      s.st.2 = (RuntimeLayout.ofPlaceOK h i).lab A64.Abort.write.exit → ms.abortAt s := by
  obtain ⟨t, r, ov, he, st, wr, th, -, -, -, -, -, hwr, -, -⟩ := sites7 h
  intro s _ hs
  refine hma s ⟨.writeErr, wr, (abortAt_eq h i _).trans hwr, ?_⟩
  rw [Scc.Sem.A64.pcOf, hs, write_toNat h i hwr]

variable {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}
  {c0 : Ctl} {rS : Range} {Λw : Scc.Sem.Layout}

/-- **`stubWN_w2` at the record of an output passing `placeOK`**, inside
`W2` at any layout `Λw`: the instance, the abort code, the write path's
phase check (`abortPhWriteOk_ofPlaceOK`) and the exit call's site premises
discharged; the memory side any aborting at the record's abort sites with
the ABI's kernel. -/
theorem stubWN_w2_ofPlaceOK
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m)
    (hc : RefCtl Λw p (fun s _ => Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i) s) lbl F c0 fs)
    {ms : MemSide isaLSE2}
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      ms.abortAt s)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hwr : ∀ s c, At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R F
      (A64.Abort.N (RuntimeLayout.ofPlaceOK h i).lab A64.Abort.write c0 .svc) s c → Dt s) :
    StubWN (fun s c => W2 Λw (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.A64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.A64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
      (K (RuntimeLayout.ofPlaceOK h i) rS) ms (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R F c0 :=
  haveI := (RuntimeLayout.ofPlaceOK h i).valid
  stubWN_w2 (Spike.Lib.A64.PhRec.instOk_ofPlaceOK h i) (hprog_ofPlaceOK h i)
    (Spike.Lib.A64.Rt.abortPhWriteOk_ofPlaceOK h i) hR hal hlo hhi hl hh hF hsub hfit hFO hc
    (hrelW_ofPlaceOK h i) (htkW_ofPlaceOK h i) (hkW_ofPlaceOK h i) (hKexW_ofPlaceOK h i)
    (hmsW_ofPlaceOK h i hma) hK hwr

/-- **`stubON_w2Ab` at the record of an output passing `placeOK`**, inside
`W2` at any layout `Λw` (`stubON_w2_ofPlaceOK` at `Λ`). -/
theorem stubON_w2_ofPlaceOKw (hp : ProgNoS ZBad p)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hc : OvfReady c0) (hsm : EnvSmall c0.env)
    (hpl : ∀ s : State, F s.st.1 → Placed Λw lbl s c0)
    {ms : MemSide isaLSE2}
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      ms.abortAt s)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hwr : ∀ s c, At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R F
      (A64.Abort.N (RuntimeLayout.ofPlaceOK h i).lab A64.Abort.overflow c0 .svc) s c → Dt s)
    (hfp : ∀ s : State, F s.st.1 → FramesPlaced Λw lbl s fs) (hcw : CtlW2 c0 fs) :
    StubON (fun s c => W2 Λw (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.A64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.A64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
      (K (RuntimeLayout.ofPlaceOK h i) rS) ms (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R F c0 :=
  haveI := (RuntimeLayout.ofPlaceOK h i).valid
  stubON_w2Ab (Spike.Lib.A64.PhRec.instOk_ofPlaceOK h i) hp (printIn_of_placeOKAt h) (hprog_ofPlaceOK h i)
    (Spike.Lib.A64.PhRec.abortPhOk_ofPlaceOK h i) hR hal hlo hhi hl hh hF hsub hfit hFO
    hc hsm hpl (hrel_ofPlaceOK h i) (htk_ofPlaceOK h i) (hk_ofPlaceOK h i) (hKex_ofPlaceOK h i)
    (hmsO_ofPlaceOK h i hma) hK hwr hfp hcw

/-- **`stubHN_w2Ab` at the record of an output passing `placeOK`**, inside
`W2` at any layout `Λw` (`stubHN_w2_ofPlaceOK` at `Λ`). -/
theorem stubHN_w2_ofPlaceOKw
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m)
    (hc : Spike.Lib.A64.StubW.NbCtl Λw p (fun s _ => Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i) s)
      lbl F c0 fs)
    (hobl : HeapAbortObl ar.cells ar.ctr c0)
    {ms : MemSide isaLSE2}
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      ms.abortAt s)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hwr : ∀ s c, At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R F
      (A64.Abort.N (RuntimeLayout.ofPlaceOK h i).lab A64.Abort.heap c0 .svc) s c → Dt s) :
    StubHN (fun s c => W2 Λw (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.A64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.A64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
      (K (RuntimeLayout.ofPlaceOK h i) rS) ms (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R F c0 :=
  haveI := (RuntimeLayout.ofPlaceOK h i).valid
  stubHN_w2Ab (Spike.Lib.A64.PhRec.instOk_ofPlaceOK h i) (printIn_of_placeOKAt h) (hprog_ofPlaceOK h i)
    (Spike.Lib.A64.Rt.abortPhHeapOk_ofPlaceOK h i)
    hR hal hlo hhi hl hh hF hsub hfit hFO hc hobl (hrelH_ofPlaceOK h i) (htkH_ofPlaceOK h i)
    (hkH_ofPlaceOK h i) (hKexH_ofPlaceOK h i) (hmsH_ofPlaceOK h i hma) hK hwr

/-- **The overflow abort label of a user function's body never ends** (a
segment to any `Q` inside `W2` at the write abort's phase, at no suspended
frame; `ovfSeg2` with `ovf_hW_w2_fi` and `stubON_w2_ofPlaceOKw` at the
record): the function's `.abort_overflow` block and its phase check when
the walk `T` reaches a `+` (`hab`; else no state is at the label), a valid
16-aligned frame of a function other than the runtime's (`hf`, `h16`,
`hfi`), its source controls placed in the slot file (`hJp`) and `c0` free
of `ZBad` (`hz0`), the take keeping the frame condition and the region off
the stack `rS` (`hFt`, `hRS`); the write tail at the stub's `write`
(`hwr`); in a 16-aligned region holding the frame and the abort call's 48
bytes below it. -/
theorem ovfAb_seg {ia : Expr → String → Nat → Option Nat} {T : Expr → Prop} {cx : FnCtx} {fp ra : BitVec 64}
    (hf : FrameOk cx) (h16 : cx.frame % 16 = 0) (hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16)
    (hab : (∃ x a b e, T (.let_ x (.add a b) e)) →
      blockAt (RuntimeLayout.ofPlaceOK h i).prog (cx.local "abort_overflow") 0 ovfBlk = true ∧
      blkPh (Spike.Lib.A64.PhRec.okPc (RuntimeLayout.ofPlaceOK h i))
        (Spike.Lib.A64.PhRec.ph (RuntimeLayout.ofPlaceOK h i)) (fun _ => false) (RuntimeLayout.ofPlaceOK h i).lab
        ((RuntimeLayout.ofPlaceOK h i).lab (cx.local "abort_overflow") + Int64.ofNat (4 * 0)) 0
        A64.Abort.Local.lb = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λw.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hRS : ∀ k, R.Off k → ∀ j < 8, R.addr k + BitVec.ofNat 64 j ∉ Scc.Sem.Kernel.addrs rS)
    (hJp : ∀ σ c, (abortN2 ia T p lbl cx (RuntimeLayout.ofPlaceOK h i).lab fp ra c0).J σ c →
      SlotRepAt Λw.imms lbl (rsOf cx) σ.slot c)
    (hz0 : NoS ZBad c0.term)
    {ms : List TermRun.Frame → MemSide isaLSE2}
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      (ms []).abortAt s)
    (hK : (ms []).K = some Scc.Sem.A64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R' F'
        (A64.Abort.N (RuntimeLayout.ofPlaceOK h i).lab A64.Abort.overflow c .svc) s c' → Dt s)
    (Q : FragS isaLSE2) :
    SegWS (fun s c fs => W2 Λw (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.A64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.A64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
      (K (RuntimeLayout.ofPlaceOK h i) rS) p lbl ms
      ((At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R F
        (abortN2 ia T p lbl cx (_root_.Executable.labels (RuntimeLayout.ofPlaceOK h i).exe).label fp ra c0)).at [])
      Q := by
  haveI := (RuntimeLayout.ofPlaceOK h i).valid
  by_cases hT : ∃ x a b e, T (.let_ x (.add a b) e)
  case neg =>
    refine SegWS.empty ?_
    rintro s c fs ⟨⟨-, -, -, -, σ, -, -, ⟨⟨⟨sv, lits, hAb, -, -, -, hTc⟩, -⟩, -⟩⟩, -⟩
    obtain ⟨x, a, b, e, -, -, -, -, -, -, he, -⟩ := hAb.1
    exact hT ⟨x, a, b, e, he ▸ hTc⟩
  obtain ⟨hblk, hphA⟩ := hab hT
  rw [Spike.Lib.A64.Flow.ofNat4_zero] at hphA
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK (rS := rS) h i
  have hge := frame_ge16 hf
  have hR8 : R.base.toNat % 8 = 0 := by omega
  have hJc : ∀ σ c, (abortN2 ia T p lbl cx (RuntimeLayout.ofPlaceOK h i).lab fp ra c0).J σ c →
      CtlW2 c [] := by
    rintro σ c ⟨⟨⟨sv, lits, hAb, -⟩, -⟩, hr⟩
    obtain ⟨x, a, b, e, -, -, -, -, -, -, he, -⟩ := hAb.1
    refine ⟨fun _ a' h' => ?_, FrOk2.run hp (FrameRun.ofLocal hr []) ⟨hz0, fun _ h => ?_⟩, fun _ h => ?_⟩
    · rw [he] at h'; cases h'
    · simp at h
    · simp at h
  have hrs : ∀ r k, rsOf cx r = some k → R.Off k := fun r k hr => by
    obtain ⟨h1, h2, h3⟩ := rsOf_bounds hf h16 hr
    exact ⟨h2, by omega, by omega⟩
  have hW := ovf_hW_w2_fi (rd := rd) (G := G) (ar := ar) (J := J) (Dt := Dt) (lsize := lsize) hI
    (printIn_of_placeOKAt h) (hprog_ofPlaceOK h i) hblk hfi hR hal hl hh hsub hfit hFO hF hp hphA hJp hrs
    (fun _ _ => ⟨_, FramesPlacedInI.nil (fun _ => False)⟩) fun σ c hj => ⟨(hJc σ c hj).1, (hJc σ c hj).2.1⟩
  refine ovfSeg2 hI.lays hI.endOk (hprog_ofPlaceOK h i) hblk hF hR hal hlo hhi (by omega) (by omega) hK hW
    (Spike.Lib.A64.Flow.Ret0.TakeK.kstable hFt) (ovf_hKR_take hRS) ?_ Q
  intro R' F' hR' hal' hlo' hhi' hF' hFK' hFF' hR'e c1 ⟨σ0, hJ0⟩ hmem
  subst hR'e
  have hk8 : (-(cx.frame : Int)) % 8 = 0 := by omega
  obtain ⟨⟨⟨sv0, lits0, hAb0, hsm0, -⟩, -⟩, -⟩ := id hJ0
  refine stubON_w2_ofPlaceOKw h i hp hR' hal' hlo' hhi'
    (by show (-48 : Int) % 8 = 0; decide) (by show (0 : Int) % 8 = 0; decide) hF' hsub hfit ?_
    hAb0.1 hsm0 ?_ hma hK (hwr _ _ c1)
    (fun _ _ => (FramesPlacedIn.nil (fun _ => False)).toFramesPlaced) (hJc σ0 c1 hJ0)
  · intro m hm
    refine Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hR hR8 hl hh (by omega) (by decide) (by omega) hk8
      (hFO m (hFF' m hm)) ?_
    intro k hk hn
    obtain ⟨mC, σC, σ1, hA, -, -, he⟩ := hmem m hm
    rw [he k hk hn]
    obtain ⟨j, hj, -⟩ := hA.slot k hk
    rw [hj]; rfl
  · intro s hs
    obtain ⟨mC, σC, σ1, hA, hsl, hJ1, he⟩ := hmem s.st.1 hs
    refine placed_of_slotRep (pf := fun k => .slot (R.addr k).toNat) (hJp σ1 c1 hJ1) fun r k hr => ?_
    obtain ⟨h1, h2, h3⟩ := rsOf_bounds hf h16 hr
    have hk : R.Off k := hrs r k hr
    have hn : ¬ (R.callee (-(cx.frame : Int)) (-48) 0).Off (k - -(cx.frame : Int)) := by
      rintro ⟨-, -, h4⟩
      simp only [Region.callee] at h4
      omega
    obtain ⟨j, hj, hjs⟩ := hA.slot k hk
    show (Scc.Sem.A64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, ← hsl]
    simp only [Scc.Sem.A64.privLoad, he k hk hn, hj, Option.map_some, hjs]

/-- **An abort of `print` never ends** (a segment to any `Q` inside `W2`
at the write abort's phase, at the frames `fs`; `printAbSeg2` with
`stubWN_w2_ofPlaceOK` in the dispatcher's region): the reference facts of
each landing's source control under the caller's frame condition (`hrc`),
the write tail at the stub's `write` (`hwr`); in a 16-aligned region with
the frame and `print`'s 96 bytes below it. -/
theorem printAb_seg {cx : FnCtx} (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 96)
    (hkc : -(cx.frame : Int) - 48 < R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hF : FStable R F)
    (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hrc : ∀ σ c, (printNA (RuntimeLayout.ofPlaceOK h i).lab cx).J σ c →
      RefCtl Λw p (fun s _ => Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i) s) lbl F c fs)
    {ms : List TermRun.Frame → MemSide isaLSE2}
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      (ms fs).abortAt s)
    (hK : (ms fs).K = some Scc.Sem.A64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R' F'
        (A64.Abort.N (RuntimeLayout.ofPlaceOK h i).lab A64.Abort.write c .svc) s c' → Dt s)
    (Q : FragS isaLSE2) :
    SegWS (fun s c fs => W2 Λw (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.A64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.A64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
      (K (RuntimeLayout.ofPlaceOK h i) rS) p lbl ms
      ((At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R F
        (printNA (_root_.Executable.labels (RuntimeLayout.ofPlaceOK h i).exe).label cx)).at fs) Q := by
  haveI := (RuntimeLayout.ofPlaceOK h i).valid
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK (rS := rS) h i
  have hR8 : R.base.toNat % 8 = 0 := by omega
  have hk8 : (-(cx.frame : Int) + -48) % 8 = 0 := by omega
  refine printAbSeg2 hI.lays hI.endOk (hprog_ofPlaceOK h i) hF hR hal hlo hkc (by omega) hK
    (fun m0 σC c0 hJ => ?_) Q
  have hc := hrc σC c0 hJ
  have hcf := Spike.Lib.A64.Flow.Ret0.Inst.callee_facts (kc := -(cx.frame : Int) + -48) (lo' := -48) hR hal
    (by omega) (by decide) (by omega) (by omega)
  refine stubWN_w2_ofPlaceOK h i hcf.1 hcf.2
    (by show (-48 : Int) ≤ -48; omega) (by show (0 : Int) ≤ 0; omega)
    (by show (-48 : Int) % 8 = 0; decide) (by show (0 : Int) % 8 = 0; decide)
    (Spike.Lib.A64.Flow.fstable_enter (kc := -(cx.frame : Int) + -48) hR hF (by omega) (by decide) (by omega)
      (by decide)
      hk8 (by decide) (by decide)) hsub hfit ?_ { hc with place := fun s hs => hc.place s hs.1 }
    hma hK (hwr _ _ c0)
  intro m hm
  refine Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hR hR8 hl hh (by omega) (by decide) (by omega) hk8
    (hFO m hm.1) ?_
  intro k hk hn
  rw [hm.2.1 k hk hn]
  obtain ⟨j, hj, -⟩ := hm.2.2.slot k hk
  rw [hj]; rfl

end Place

/-- **The aborts of a user function's body**, in its region `R` at no
suspended frame: the overflow label at a context control (`G0`), or an
abort of `print` with `print`'s frame suspended. -/
def MainAb (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (ia : Expr → String → Nat → Option Nat) (T : Expr → Prop) (p : Prog) (lbl : Lbl) (cx : FnCtx)
    (fp ra : BitVec 64) (G0 : Ctl → Prop) : FragS isaLSE2 :=
  fun s c fs => (∃ c0, G0 c0 ∧
      (At exe endPc R F (abortN2 ia T p lbl cx (_root_.Executable.labels exe).label fp ra c0)).at [] s c fs) ∨
    ∃ x e c1, (At exe endPc R F (printNA (_root_.Executable.labels exe).label cx)).at
      [Spike.Lib.LowerNode.printFrame x e c1] s c fs

/-- **The overflow label's source controls are placed in the slot file**
(`ovfAb_seg`'s `hJp`): `AbJ2`'s source with its register bases and
immediates, the abort label's table `ia` the layout's at the walk's terms
(`himm`). -/
theorem abortN2_slotRepAt {ia : Expr → String → Nat → Option Nat} {T : Expr → Prop} {p : Prog} {lbl : Lbl}
    {cx : FnCtx} {lab : Label → Int64} {fp ra : BitVec 64} {c0 : Ctl} {Λw : Scc.Sem.Layout}
    (himm : ∀ t, T t → ∀ x k, ia t x k = Λw.imms t x k) :
    ∀ σ c, (abortN2 ia T p lbl cx lab fp ra c0).J σ c → SlotRepAt Λw.imms lbl (rsOf cx) σ.slot c :=
  fun _ _ ⟨⟨⟨s, _, hA, _, hi, hb, hT⟩, _⟩, _⟩ =>
    ⟨s, hA.2.2.1, hA.2.2.2, hb, Spike.Lib.LowerNode.immIn_congr hi (himm _ hT)⟩

/-- **`abortN2_slotRepAt` at a compiled block's walk**: the abort label at
`imms2Of p` and the walk `TailAt2 p j` of an `Accepted2` program's `j`th
compiled block, the layout's immediates `imms2Me` (`imms2Me_tailAt2`). -/
theorem abortN2_slotRepAt_me {p : Prog} (hacc : Scc.Lower.Accepted2 p = true) {j : Nat} {d : Decl}
    (hd : (Spike.Lib.LowerNode.compiled2 p)[j]? = some d) {lbl : Lbl} {cx : FnCtx} {lab : Label → Int64}
    {fp ra : BitVec 64}
    {c0 : Ctl} {Λw Λ0 : Scc.Sem.Layout} (hme : Λw.imms = Spike.Lib.LowerNode.imms2Me Λ0 p) :
    ∀ σ c, (abortN2 (Scc.Lower.imms2Of p) (Spike.Lib.LowerNode.TailAt2 p j) p lbl cx lab fp ra c0).J σ c →
      SlotRepAt Λw.imms lbl (rsOf cx) σ.slot c :=
  abortN2_slotRepAt fun _ ht x k => by
    rw [hme]; exact (Spike.Lib.LowerNode.imms2Me_tailAt2 hacc hd ht x k).symm

section Place2

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.PhRec (μ K)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)
include h

variable {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {rS : Range} {Λw : Scc.Sem.Layout}

/-- **A user function's aborts never end** (`MainAb` a segment to the
empty fragment inside `W2` at the write abort's phase; `ovfAb_seg` at each
context control, `printAb_seg` at each suspended `print` frame): their
premises, in a 16-aligned region with the frame and `print`'s 96 bytes
below it. -/
theorem mainAb_seg {ia : Expr → String → Nat → Option Nat} {T : Expr → Prop} {cx : FnCtx} {fp ra : BitVec 64}
    {G0 : Ctl → Prop} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0) (hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16)
    (hab : (∃ x a b e, T (.let_ x (.add a b) e)) →
      blockAt (RuntimeLayout.ofPlaceOK h i).prog (cx.local "abort_overflow") 0 ovfBlk = true ∧
      blkPh (Spike.Lib.A64.PhRec.okPc (RuntimeLayout.ofPlaceOK h i))
        (Spike.Lib.A64.PhRec.ph (RuntimeLayout.ofPlaceOK h i)) (fun _ => false) (RuntimeLayout.ofPlaceOK h i).lab
        ((RuntimeLayout.ofPlaceOK h i).lab (cx.local "abort_overflow") + Int64.ofNat (4 * 0)) 0
        A64.Abort.Local.lb = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 96) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λw.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hRS : ∀ k, R.Off k → ∀ j < 8, R.addr k + BitVec.ofNat 64 j ∉ Scc.Sem.Kernel.addrs rS)
    (hJp : ∀ c0, G0 c0 → ∀ σ c, (abortN2 ia T p lbl cx (RuntimeLayout.ofPlaceOK h i).lab fp ra c0).J σ c →
      SlotRepAt Λw.imms lbl (rsOf cx) σ.slot c)
    (hz0 : ∀ c0, G0 c0 → NoS ZBad c0.term)
    (hrc : ∀ x e c1 σ c, (printNA (RuntimeLayout.ofPlaceOK h i).lab cx).J σ c →
      RefCtl Λw p (fun s _ => Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i) s) lbl F c
        [Spike.Lib.LowerNode.printFrame x e c1])
    {ms : List TermRun.Frame → MemSide isaLSE2}
    (hma : ∀ fs (s : State), (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      (ms fs).abortAt s)
    (hK : ∀ fs, (ms fs).K = some Scc.Sem.A64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R' F'
        (A64.Abort.N (RuntimeLayout.ofPlaceOK h i).lab A64.Abort.overflow c .svc) s c' → Dt s)
    (hwrW : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R' F'
        (A64.Abort.N (RuntimeLayout.ofPlaceOK h i).lab A64.Abort.write c .svc) s c' → Dt s) :
    SegWS (fun s c fs => W2 Λw (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.A64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.A64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
      (K (RuntimeLayout.ofPlaceOK h i) rS) p lbl ms
      (MainAb (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R F ia T p lbl cx fp ra G0)
      (fun _ _ _ => False) := by
  have hge := frame_ge16 hf
  refine SegWS.or_pre (SegWS.exists_pre fun c0 => ?_) (SegWS.exists_pre fun x => SegWS.exists_pre fun e =>
    SegWS.exists_pre fun c1 => ?_)
  · by_cases hg : G0 c0
    · exact (ovfAb_seg (c0 := c0) h i hf h16 hfi hab hR hal (by omega) hhi hl hh hF hsub hfit hFO hp hFt hRS
        (hJp c0 hg) (hz0 c0 hg) (hma []) (hK []) hwr _).mono_pre fun _ _ _ h => h.2
    · exact SegWS.empty fun _ _ _ h => hg h.1
  · exact printAb_seg h i h16 hR hal hlo (by omega) hl hh hF hsub hfit hFO (hrc x e c1) (hma _) (hK _)
      hwrW _

end Place2

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hkW_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hkW_ofPlaceOK

/-- info: 'Spike.Lib.LowerA64.stubWN_w2_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubWN_w2_ofPlaceOK

/-- info: 'Spike.Lib.LowerA64.stubON_w2_ofPlaceOKw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubON_w2_ofPlaceOKw

/-- info: 'Spike.Lib.LowerA64.stubHN_w2_ofPlaceOKw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubHN_w2_ofPlaceOKw

/-- info: 'Spike.Lib.LowerA64.ovfAb_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ovfAb_seg

/-- info: 'Spike.Lib.LowerA64.printAb_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printAb_seg

/-- info: 'Spike.Lib.LowerA64.abortN2_slotRepAt_me' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms abortN2_slotRepAt_me

/-- info: 'Spike.Lib.LowerA64.mainAb_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainAb_seg

end Spike.Lib.LowerA64
