/-
**`main`'s aborts never end, at the record of an output passing `placeOK`**
(x86-64): the write abort path's premises at the record (its phase check
from A7's `tailOffC`, its exit call's site premises from A6's sites), and
the abort fragment of `main`'s body (`MainAb`: the overflow label, an
abort of `print`) as a segment to the empty fragment inside `W2` at the
write abort's phase.

- `abortPhWriteOk_ofPlaceOK`: the write abort path's phase check;
- `write_codeLabel`, `write_toNat`, `hrelW_ofPlaceOK`, `htkW_ofPlaceOK`,
  `hkW_ofPlaceOK`, `hKexW_ofPlaceOK`, `hmsW_ofPlaceOK`: the write exit
  call's site premises (the twins of the heap's in
  `Spike/Lib/LowerX64/AbortW2Ab.lean`);
- `stubWN_w2_ofPlaceOK`: `stubWN_w2` at the record;
- `stubON_w2_ofPlaceOKw`: `stubON_w2Ab` at the record, at any layout;
- `ovfAb_seg`: the overflow label of `main`'s body never ends;
- `printAb_seg`: an abort of `print` never ends;
- `MainAb`, `mainAb_seg`: `main`'s aborts, never ending;
- `abortN2_slotRepAt`, `mainAb_seg'`: `mainAb_seg` with `hJp` from `AbJ2`.
-/
import Spike.Lib.LowerX64.AbortW2Ab
import Spike.Lib.LowerX64.PrintAbW2
import Spike.Lib.LowerX64.AbortSeg2
import Spike.Lib.LowerX64.UserLabs

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region FrameRun OvfReady EnvSmall)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At okBlk FStable KStable)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff TakeK takeMem)
open Spike.Lib.LowerNode (FrOk2 ZBad SlotRepAt)
open Spike.Lib.X64.StubW (abortPhWriteOk RefCtl)
open A9NoSpawn (NoS)
open Spike.Lib.X64

section Place

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Sem.X64 (codeLabel)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.PhRec (μ K)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)
include h

/-- **The write abort path's phase check** at the record's `okPc`/`ph`
and labels (A7's `tailOffC`, as `abortPhHeapOk_ofPlaceOK`). -/
theorem abortPhWriteOk_ofPlaceOK :
    abortPhWriteOk (Spike.Lib.X64.PhRec.okPc (RuntimeLayout.ofPlaceOK h i))
      (Spike.Lib.X64.PhRec.ph (RuntimeLayout.ofPlaceOK h i)) (RuntimeLayout.ofPlaceOK h i).lab = true := by
  haveI : Kraken.Executable.ValidLayout (Scc.Sem.X64.threadAt Scc.Sem.Entry.linux (Λ).code.lo
      o.prog (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)).exe :=
    (RuntimeLayout.ofPlaceOK h i).valid
  have ht := Spike.Lib.X64.StubW.tailPhOk_of_tailOffC (tailOff_of_placeOKAt h)
    (lab := (RuntimeLayout.ofPlaceOK h i).lab) fun _ _ ha =>
    Scc.Cert.Rt.X64.label_threadAt_of_codeLabel_below (E := Scc.Sem.Entry.linux)
      (syms := Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)
          (by exact Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK_below h i ha) ha
  simp only [Spike.Lib.X64.StubW.tailPhOk, Bool.and_eq_true] at ht
  exact ht.1.1.1.2

/-- The write exit call's label resolves (A6's sites). -/
theorem write_codeLabel : ∃ a, codeLabel (Λ).code.lo o.prog Abort.write.exit = some a := by
  obtain ⟨-, -, -, -, -, wr, -, -, -, -, -, -, hwr, -, -⟩ := sites7 h
  exact ⟨wr, hwr⟩

/-- The write exit call's address is its `codeLabel` address. -/
theorem write_toNat {a : Nat}
    (ha : codeLabel (Λ).code.lo o.prog "scc_rt_abort_write_exit" = some a) :
    ((RuntimeLayout.ofPlaceOK h i).lab Abort.write.exit).toBitVec.toNat = a :=
  lab_toNat h i ha

/-- **`hrel`** (write): the write exit call is off the release site. -/
theorem hrelW_ofPlaceOK : ∀ a, (μ (RuntimeLayout.ofPlaceOK h i)).site .release = some a →
    ((RuntimeLayout.ofPlaceOK h i).lab Abort.write.exit).toBitVec.toNat ≠ a := by
  obtain ⟨t, r, ov, he, st, wr, th, -, hr, -, -, -, hwr, -, hnd⟩ := sites7 h
  intro a ha
  change codeLabel (Λ).code.lo o.prog "scc_rt_release_site" = some a at ha
  rw [hr] at ha
  cases ha
  rw [write_toNat h i hwr]
  rintro rfl
  simp at hnd

/-- **`htk`** (write): the write exit call is off the take site. -/
theorem htkW_ofPlaceOK : ∀ a, (μ (RuntimeLayout.ofPlaceOK h i)).site .take = some a →
    ((RuntimeLayout.ofPlaceOK h i).lab Abort.write.exit).toBitVec.toNat ≠ a := by
  obtain ⟨t, r, ov, he, st, wr, th, ht, -, -, -, -, hwr, -, hnd⟩ := sites7 h
  intro a ha
  change codeLabel (Λ).code.lo o.prog "scc_rt_take_site" = some a at ha
  rw [ht] at ha
  cases ha
  rw [write_toNat h i hwr]
  rintro rfl
  simp at hnd

/-- **`hk`** (write): the write exit call is no other abort kind's site. -/
theorem hkW_ofPlaceOK : ∀ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a →
    ((RuntimeLayout.ofPlaceOK h i).lab Abort.write.exit).toBitVec.toNat = a → k = .writeErr := by
  obtain ⟨t, r, ov, he, st, wr, th, -, -, hov, hhe, hst, hwr, hth, hnd⟩ := sites7 h
  intro k a ha hx
  rw [write_toNat h i hwr] at hx
  subst hx
  cases k with
  | writeErr => rfl
  | overflow =>
    rw [abortAt_eq h i] at ha
    change codeLabel (Λ).code.lo o.prog "scc_rt_abort_overflow_exit" = some wr at ha
    rw [hov] at ha; cases ha; simp at hnd
  | heap =>
    rw [abortAt_eq h i] at ha
    change codeLabel (Λ).code.lo o.prog "scc_rt_abort_heap_exit" = some wr at ha
    rw [hhe] at ha; cases ha; simp at hnd
  | stack =>
    rw [abortAt_eq h i] at ha
    change codeLabel (Λ).code.lo o.prog "scc_rt_abort_stack_exit" = some wr at ha
    rw [hst] at ha; cases ha; simp at hnd
  | threads =>
    rw [abortAt_eq h i] at ha
    change codeLabel (Λ).code.lo o.prog "scc_rt_abort_threads_exit" = some wr at ha
    rw [hth] at ha; cases ha; simp at hnd

/-- **`hKex`** (write): no outside move (the take, at the take site) at
the write exit call. -/
theorem hKexW_ofPlaceOK {rS : Scc.Sem.Range} : ∀ s s', Scc.Sem.X64.pcOf s =
    ((RuntimeLayout.ofPlaceOK h i).lab Abort.write.exit).toBitVec.toNat →
    ¬ K (RuntimeLayout.ofPlaceOK h i) rS s s' := by
  obtain ⟨t, r, ov, he, st, wr, th, ht, -, -, -, -, hwr, -, hnd⟩ := sites7 h
  intro s s' hpc hK
  rw [Scc.Sem.X64.pcOf, Spike.Lib.X64.Flow.Ret0.TakeK.pc hK, lab_toNat h i (l := "scc_rt_take_site") ht,
    write_toNat h i hwr] at hpc
  subst hpc
  simp at hnd

/-- **`hms`** (write): a memory side aborting at every abort site of the
record aborts at the write exit call. -/
theorem hmsW_ofPlaceOK {ms : MemSide isa}
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      ms.abortAt s) :
    ∀ s : State, s.exe = (RuntimeLayout.ofPlaceOK h i).exe →
      s.st.2 = (RuntimeLayout.ofPlaceOK h i).lab Abort.write.exit → ms.abortAt s := by
  obtain ⟨a, ha⟩ := write_codeLabel h
  intro s _ hs
  refine hma s ⟨.writeErr, a, (abortAt_eq h i _).trans ha, ?_⟩
  rw [Scc.Sem.X64.pcOf, hs, lab_toNat h i ha]

variable {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}
  {c0 : Ctl} {rS : Range} {Λw : Scc.Sem.Layout}

/-- **`stubWN_w2` at the record of an output passing `placeOK`**: the
instance, the abort code, the write path's phase check and the exit call's
site premises discharged; the memory side any aborting at the record's
abort sites with the ABI's kernel. -/
theorem stubWN_w2_ofPlaceOK
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m)
    (hc : RefCtl Λw p (fun s _ => Spike.Lib.X64.PhRec.own (RuntimeLayout.ofPlaceOK h i) s) lbl F c0 fs)
    {ms : MemSide isa}
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      ms.abortAt s)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hwr : ∀ s c, At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R F
      (Abort.N (RuntimeLayout.ofPlaceOK h i).lab Abort.write c0 .sys) s c → Dt s) :
    StubWN (fun s c => W2 Λw (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.X64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.X64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.X64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
      (K (RuntimeLayout.ofPlaceOK h i) rS) ms (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R F c0 :=
  haveI := (RuntimeLayout.ofPlaceOK h i).valid
  stubWN_w2 (Spike.Lib.X64.PhRec.instOk_ofPlaceOK h i) (hprog_ofPlaceOK h i) (abortPhWriteOk_ofPlaceOK h i)
    hR hR8 hlo hhi hl hh hF hsub hfit hFO hc (hrelW_ofPlaceOK h i) (htkW_ofPlaceOK h i) (hkW_ofPlaceOK h i)
    (hKexW_ofPlaceOK h i) (hmsW_ofPlaceOK h i hma) hK hwr

/-- **`stubON_w2Ab` at the record of an output passing `placeOK`**, inside
`W2` at any layout `Λw` (`stubON_w2_ofPlaceOK` at `Λ`). -/
theorem stubON_w2_ofPlaceOKw (hp : ProgNoS ZBad p)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hc : OvfReady c0) (hsm : EnvSmall c0.env)
    (hpl : ∀ s : State, F s.st.1 → Placed Λw lbl s c0)
    {ms : MemSide isa}
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      ms.abortAt s)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hwr : ∀ s c, At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R F
      (Abort.N (RuntimeLayout.ofPlaceOK h i).lab Abort.overflow c0 .sys) s c → Dt s)
    (hfp : ∀ s : State, F s.st.1 → FramesPlaced Λw lbl s fs) (hcw : CtlW2 c0 fs) :
    StubON (fun s c => W2 Λw (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.X64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.X64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.X64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
      (K (RuntimeLayout.ofPlaceOK h i) rS) ms (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R F c0 :=
  haveI := (RuntimeLayout.ofPlaceOK h i).valid
  stubON_w2Ab (Spike.Lib.X64.PhRec.instOk_ofPlaceOK h i) hp (printIn_of_placeOKAt h) (hprog_ofPlaceOK h i)
    (hsysIn_ofPlaceOK h i) (Spike.Lib.X64.PhRec.abortPhOk_ofPlaceOK h i) hR hR8 hlo hhi hl hh hF hsub hfit hFO
    hc hsm hpl (hrel_ofPlaceOK h i) (htk_ofPlaceOK h i) (hk_ofPlaceOK h i) (hKex_ofPlaceOK h i)
    (hmsO_ofPlaceOK h i hma) hK hwr hfp hcw

/-- **The overflow abort label of `main`'s body never ends** (a segment to
any `Q` inside `W2` at the write abort's phase, at no suspended frame;
`ovfSeg2` with `ovf_hW_w2` and `stubON_w2_ofPlaceOKw` at the record): the
function's `.ovf` block and its phase check when the walk `T` reaches a
`+` (`hab`; else no state is at the label), a valid frame of a user
function (`hf`, `hfn`), its source controls placed in the slot file
(`hJp`) and `c0` free of `ZBad` (`hz0`), the take keeping the frame
condition and the region off the stack `rS` (`hFt`, `hRS`); the write tail
at the stub's `write` (`hwr`); in an 8-aligned region holding the frame,
the abort call's 40 bytes below it and the frame record. -/
theorem ovfAb_seg {T : Expr → Prop} {fr : Scc.Emit.X64.Frame} {fp ra : BitVec 64} {f : String}
    (hf : FrameOk fr) (hfn : fr.fn = Scc.Lower.Names.user f)
    (hab : (∃ x a b e, T (.let_ x (.add a b) e)) →
      Scc.Cert.Rt.X64.blockAtB (RuntimeLayout.ofPlaceOK h i).prog (ovfL fr) 0 ovfBlk = true ∧
      blkPh (Spike.Lib.X64.PhRec.okPc (RuntimeLayout.ofPlaceOK h i))
        (Spike.Lib.X64.PhRec.ph (RuntimeLayout.ofPlaceOK h i)) (fun _ => false) (RuntimeLayout.ofPlaceOK h i).lab
        ((RuntimeLayout.ofPlaceOK h i).lab (ovfL fr) + Int64.ofNat 0) 0 Abort.Local.lb = true)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 40) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λw.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hRS : ∀ k, R.Off k → ∀ j < 8, R.addr k + BitVec.ofNat 64 j ∉ Scc.Sem.Kernel.addrs rS)
    (hJp : ∀ σ c, (abortN2 i T p lbl fr (RuntimeLayout.ofPlaceOK h i).lab fp ra c0).J σ c →
      SlotRepAt Λw.imms lbl (rsOf fr) σ.slot c)
    (hz0 : NoS ZBad c0.term)
    {ms : List TermRun.Frame → MemSide isa}
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      (ms []).abortAt s)
    (hK : (ms []).K = some Scc.Sem.X64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R' F' (Abort.N (RuntimeLayout.ofPlaceOK h i).lab Abort.overflow c .sys)
        s c' → Dt s)
    (Q : FragS isa) :
    SegWS (fun s c fs => W2 Λw (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.X64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.X64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.X64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
      (K (RuntimeLayout.ofPlaceOK h i) rS) p lbl ms
      ((At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R F
        (abortN2 i T p lbl fr (_root_.Executable.labels (RuntimeLayout.ofPlaceOK h i).exe).label fp ra c0)).at [])
      Q := by
  haveI := (RuntimeLayout.ofPlaceOK h i).valid
  by_cases hT : ∃ x a b e, T (.let_ x (.add a b) e)
  case neg =>
    refine SegWS.empty ?_
    rintro s c fs ⟨⟨-, -, -, -, σ, -, -, ⟨⟨sv, lits, hAb, -, -, -, hTc⟩, -⟩, -⟩, -⟩
    obtain ⟨x, a, b, e, -, -, -, -, -, -, he, -⟩ := hAb.1
    exact hT ⟨x, a, b, e, he ▸ hTc⟩
  obtain ⟨hblk, hphA⟩ := hab hT
  rw [Spike.Lib.X64.Flow.ofNat_zero'] at hphA
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK (rS := rS) h i
  have h8 : (fr.size : Int) % 8 = 0 := by have := frame_mod8 hf; omega
  have hJc : ∀ σ c, (abortN2 i T p lbl fr (RuntimeLayout.ofPlaceOK h i).lab fp ra c0).J σ c →
      CtlW2 c [] := by
    rintro σ c ⟨⟨⟨sv, lits, hAb, -, -, -⟩, -⟩, hr⟩
    obtain ⟨x, a, b, e, -, -, -, -, -, -, he, -⟩ := hAb.1
    refine ⟨fun _ a' h' => ?_, FrOk2.run hp (FrameRun.ofLocal hr []) ⟨hz0, fun _ h => ?_⟩, fun _ h => ?_⟩
    · rw [he] at h'; cases h'
    · simp at h
    · simp at h
  have hrs : ∀ r k, rsOf fr r = some k → R.Off k := fun r k hr => by
    obtain ⟨h1, h2, h3⟩ := rsOf_bounds hf hr
    exact ⟨h2, by omega, by omega⟩
  have hW := ovf_hW_w2 (rd := rd) (G := G) (ar := ar) (J := J) (Dt := Dt) (lsize := lsize) hI
    (printIn_of_placeOKAt h) (hprog_ofPlaceOK h i) hblk (by rw [ovfL, hfn]; exact labelOf_user_not_abLabs f "ovf")
    hR hR8
    (by omega) (by omega) hl hh h8 hsub hfit hFO hF hp hphA hJp hrs
    (fun _ _ => ⟨_, FramesPlacedInI.nil (fun _ => False)⟩) fun σ c hj => ⟨(hJc σ c hj).1, (hJc σ c hj).2.1⟩
  refine ovfSeg2 hI.lays hI.endOk (hprog_ofPlaceOK h i) hblk hF hR hlo (by omega) h8 hK hW
    (TakeK.kstable hFt) (ovf_hKR_take hRS) ?_ Q
  intro R' F' hR' hlo' hhi' hF' hFK' hFF' hR'e c1 ⟨σ0, hJ0⟩ hmem
  subst hR'e
  have hkc8 : (-(fr.size : Int) - 8 - 8) % 8 = 0 := by omega
  refine stubON_w2_ofPlaceOKw h i hp hR' (addr_toNat_mod8 R hR8 hkc8) hlo' hhi'
    (by show (-24 : Int) % 8 = 0; decide) (by show (16 : Int) % 8 = 0; decide) hF' hsub hfit ?_
    hJ0.1.1.choose_spec.choose_spec.1.1 hJ0.1.1.choose_spec.choose_spec.2.1 ?_ hma hK (hwr _ _ c1)
    (fun _ _ => Spike.Lib.X64.Flow.Hello1.SFactsN.framesPlaced_nil) (hJc σ0 c1 hJ0)
  · intro m hm
    refine Spike.Lib.X64.Rt.stackOff_callee hR hR8 hl hh (by omega) (by decide) (by omega) hkc8
      (hFO m (hFF' m hm)) ?_
    intro k hk hn
    obtain ⟨mC, σC, σ1, hA, -, -, he⟩ := hmem m hm
    rw [he k hk hn]
    obtain ⟨j, hj, -⟩ := hA.slot k hk
    rw [hj]; rfl
  · intro s hs
    obtain ⟨mC, σC, σ1, hA, hsl, hJ1, he⟩ := hmem s.st.1 hs
    refine placed_of_slotRep (pf := fun k => .slot (R.addr k).toNat) (hJp σ1 c1 hJ1) fun r k hr => ?_
    obtain ⟨h1, h2, h3⟩ := rsOf_bounds hf hr
    have hk : R.Off k := hrs r k hr
    have hn : ¬ (R.callee (-(fr.size : Int) - 8 - 8) (-24) 16).Off (k - (-(fr.size : Int) - 8 - 8)) := by
      rintro ⟨-, -, h4⟩
      simp only [Region.callee] at h4
      omega
    obtain ⟨j, hj, hjs⟩ := hA.slot k hk
    show (Scc.Sem.X64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    show ((s.st.1.dmem.loadInt (R.addr k) 8).map (BitVec.ofInt 64)).map (·.toNat) = _
    rw [he k hk hn, hj, Option.map_some, hjs, hsl k (by omega)]; rfl

/-- **An abort of `print` never ends** (a segment to any `Q` inside `W2`
at the write abort's phase, at the frames `fs`; `printAbSeg2` with
`stubWN_w2_ofPlaceOK` in the dispatcher's region): the reference facts of
each landing's source control under the caller's frame condition (`hrc`),
the write tail at the stub's `write` (`hwr`); in an 8-aligned region with
the frame and `print`'s 88 bytes below it. -/
theorem printAb_seg {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 88)
    (hhi : -(fr.size : Int) - 48 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hF : FStable R F)
    (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hrc : ∀ σ c, (printNA (RuntimeLayout.ofPlaceOK h i).lab fr).J σ c →
      RefCtl Λw p (fun s _ => Spike.Lib.X64.PhRec.own (RuntimeLayout.ofPlaceOK h i) s) lbl F c fs)
    {ms : List TermRun.Frame → MemSide isa}
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      (ms fs).abortAt s)
    (hK : (ms fs).K = some Scc.Sem.X64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R' F' (Abort.N (RuntimeLayout.ofPlaceOK h i).lab Abort.write c .sys)
        s c' → Dt s)
    (Q : FragS isa) :
    SegWS (fun s c fs => W2 Λw (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.X64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.X64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.X64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
      (K (RuntimeLayout.ofPlaceOK h i) rS) p lbl ms
      ((At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R F
        (printNA (_root_.Executable.labels (RuntimeLayout.ofPlaceOK h i).exe).label fr)).at fs) Q := by
  haveI := (RuntimeLayout.ofPlaceOK h i).valid
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK (rS := rS) h i
  have h8 : (fr.size : Int) % 8 = 0 := by have := frame_mod8 hf; omega
  have hkc8 : (-(fr.size : Int) - 56 - 8) % 8 = 0 := by omega
  refine printAbSeg2 hI.lays hI.endOk (hprog_ofPlaceOK h i) hF hR hlo hhi h8 hK (fun m0 σC c0 hJ => ?_) Q
  have hc := hrc σC c0 hJ
  refine stubWN_w2_ofPlaceOK h i
    (Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)) (addr_toNat_mod8 R hR8 hkc8)
    (by show (-24 : Int) ≤ -24; omega) (by show (16 : Int) ≤ 16; omega)
    (by show (-24 : Int) % 8 = 0; decide) (by show (16 : Int) % 8 = 0; decide)
    (fstable_enter (kb := -(fr.size : Int) - 56 - 8) hR hF (by omega) (by decide) (by omega) (by omega)
      (by omega) (by decide) (by decide)) hsub hfit ?_ { hc with place := fun s hs => hc.place s hs.1 }
    hma hK (hwr _ _ c0)
  intro m hm
  refine Spike.Lib.X64.Rt.stackOff_callee hR hR8 hl hh (by omega) (by decide) (by omega) hkc8 (hFO m hm.1) ?_
  intro k hk hn
  rw [hm.2.1 k hk hn]
  obtain ⟨j, hj, -⟩ := hm.2.2.slot k hk
  rw [hj]; rfl

/-- **The aborts of `main`'s body**, in its region `R` at no suspended
frame: the overflow label at a context control (`G0`), or an abort of
`print` with `print`'s frame suspended. -/
def MainAb (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (i : Expr → String → Nat → Option Nat) (T : Expr → Prop) (p : Prog) (lbl : Lbl) (fr : Scc.Emit.X64.Frame)
    (fp ra : BitVec 64) (G0 : Ctl → Prop) : FragS isa :=
  fun s c fs => (∃ c0, G0 c0 ∧
      (At exe endPc R F (abortN2 i T p lbl fr (_root_.Executable.labels exe).label fp ra c0)).at [] s c fs) ∨
    ∃ x e c1, (At exe endPc R F (printNA (_root_.Executable.labels exe).label fr)).at
      [Spike.Lib.LowerNode.printFrame x e c1] s c fs

/-- **`main`'s aborts never end** (`MainAb` a segment to the empty
fragment inside `W2` at the write abort's phase; `ovfAb_seg` at each
context control, `printAb_seg` at each suspended `print` frame): their
premises, in an 8-aligned region with the frame and `print`'s 88 bytes
below it and the frame record. -/
theorem mainAb_seg {T : Expr → Prop} {fr : Scc.Emit.X64.Frame} {fp ra : BitVec 64} {f : String}
    {G0 : Ctl → Prop} (hf : FrameOk fr) (hfn : fr.fn = Scc.Lower.Names.user f)
    (hab : (∃ x a b e, T (.let_ x (.add a b) e)) →
      Scc.Cert.Rt.X64.blockAtB (RuntimeLayout.ofPlaceOK h i).prog (ovfL fr) 0 ovfBlk = true ∧
      blkPh (Spike.Lib.X64.PhRec.okPc (RuntimeLayout.ofPlaceOK h i))
        (Spike.Lib.X64.PhRec.ph (RuntimeLayout.ofPlaceOK h i)) (fun _ => false) (RuntimeLayout.ofPlaceOK h i).lab
        ((RuntimeLayout.ofPlaceOK h i).lab (ovfL fr) + Int64.ofNat 0) 0 Abort.Local.lb = true)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 88) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λw.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hRS : ∀ k, R.Off k → ∀ j < 8, R.addr k + BitVec.ofNat 64 j ∉ Scc.Sem.Kernel.addrs rS)
    (hJp : ∀ c0, G0 c0 → ∀ σ c, (abortN2 i T p lbl fr (RuntimeLayout.ofPlaceOK h i).lab fp ra c0).J σ c →
      SlotRepAt Λw.imms lbl (rsOf fr) σ.slot c)
    (hz0 : ∀ c0, G0 c0 → NoS ZBad c0.term)
    (hrc : ∀ x e c1 σ c, (printNA (RuntimeLayout.ofPlaceOK h i).lab fr).J σ c →
      RefCtl Λw p (fun s _ => Spike.Lib.X64.PhRec.own (RuntimeLayout.ofPlaceOK h i) s) lbl F c
        [Spike.Lib.LowerNode.printFrame x e c1])
    {ms : List TermRun.Frame → MemSide isa}
    (hma : ∀ fs (s : State), (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      (ms fs).abortAt s)
    (hK : ∀ fs, (ms fs).K = some Scc.Sem.X64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R' F' (Abort.N (RuntimeLayout.ofPlaceOK h i).lab Abort.overflow c .sys)
        s c' → Dt s)
    (hwrW : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R' F' (Abort.N (RuntimeLayout.ofPlaceOK h i).lab Abort.write c .sys)
        s c' → Dt s) :
    SegWS (fun s c fs => W2 Λw (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.X64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.X64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.X64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
      (K (RuntimeLayout.ofPlaceOK h i) rS) p lbl ms
      (MainAb (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R F i T p lbl fr fp ra G0)
      (fun _ _ _ => False) := by
  refine SegWS.or_pre (SegWS.exists_pre fun c0 => ?_) (SegWS.exists_pre fun x => SegWS.exists_pre fun e =>
    SegWS.exists_pre fun c1 => ?_)
  · by_cases hg : G0 c0
    · exact (ovfAb_seg (c0 := c0) h i hf hfn hab hR hR8 (by omega) hhi hl hh hF hsub hfit hFO hp hFt hRS
        (hJp c0 hg) (hz0 c0 hg) (hma []) (hK []) hwr _).mono_pre fun _ _ _ h => h.2
    · exact SegWS.empty fun _ _ _ h => hg h.1
  · exact printAb_seg h i hf hR hR8 (by omega) (by omega) hl hh hF hsub hfit hFO (hrc x e c1) (hma _) (hK _)
      hwrW _


/-- **The overflow label's source controls are placed in the slot file**
(`ovfAb_seg`'s `hJp`): `AbJ2`'s source with its register bases and
immediates, the layout's immediates the table `i` (`himm`). -/
theorem abortN2_slotRepAt {T : Expr → Prop} {fr : Scc.Emit.X64.Frame} {lab : String → Int64} {fp ra : BitVec 64}
    (himm : Λw.imms = i) :
    ∀ σ c, (abortN2 i T p lbl fr lab fp ra c0).J σ c → SlotRepAt Λw.imms lbl (rsOf fr) σ.slot c :=
  fun _ _ ⟨⟨⟨s, _, hA, _, hi, hb, _⟩, _⟩, _⟩ => ⟨s, hA.2.2.1, hA.2.2.2, hb, himm ▸ hi⟩

/-- **`main`'s aborts never end**, the overflow label's slot placement
discharged (`mainAb_seg` with `abortN2_slotRepAt`): the layout's
immediates the table `i` (`himm`) for `hJp`. -/
theorem mainAb_seg' {T : Expr → Prop} {fr : Scc.Emit.X64.Frame} {fp ra : BitVec 64} {f : String}
    {G0 : Ctl → Prop} (hf : FrameOk fr) (hfn : fr.fn = Scc.Lower.Names.user f)
    (hab : (∃ x a b e, T (.let_ x (.add a b) e)) →
      Scc.Cert.Rt.X64.blockAtB (RuntimeLayout.ofPlaceOK h i).prog (ovfL fr) 0 ovfBlk = true ∧
      blkPh (Spike.Lib.X64.PhRec.okPc (RuntimeLayout.ofPlaceOK h i))
        (Spike.Lib.X64.PhRec.ph (RuntimeLayout.ofPlaceOK h i)) (fun _ => false) (RuntimeLayout.ofPlaceOK h i).lab
        ((RuntimeLayout.ofPlaceOK h i).lab (ovfL fr) + Int64.ofNat 0) 0 Abort.Local.lb = true)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 88) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λw.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hRS : ∀ k, R.Off k → ∀ j < 8, R.addr k + BitVec.ofNat 64 j ∉ Scc.Sem.Kernel.addrs rS)
    (himm : Λw.imms = i)
    (hz0 : ∀ c0, G0 c0 → NoS ZBad c0.term)
    (hrc : ∀ x e c1 σ c, (printNA (RuntimeLayout.ofPlaceOK h i).lab fr).J σ c →
      RefCtl Λw p (fun s _ => Spike.Lib.X64.PhRec.own (RuntimeLayout.ofPlaceOK h i) s) lbl F c
        [Spike.Lib.LowerNode.printFrame x e c1])
    {ms : List TermRun.Frame → MemSide isa}
    (hma : ∀ fs (s : State), (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      (ms fs).abortAt s)
    (hK : ∀ fs, (ms fs).K = some Scc.Sem.X64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R' F' (Abort.N (RuntimeLayout.ofPlaceOK h i).lab Abort.overflow c .sys)
        s c' → Dt s)
    (hwrW : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R' F' (Abort.N (RuntimeLayout.ofPlaceOK h i).lab Abort.write c .sys)
        s c' → Dt s) :
    SegWS (fun s c fs => W2 Λw (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.X64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.X64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.X64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
      (K (RuntimeLayout.ofPlaceOK h i) rS) p lbl ms
      (MainAb (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R F i T p lbl fr fp ra G0)
      (fun _ _ _ => False) :=
  mainAb_seg h i hf hfn hab hR hR8 hlo hhi hl hh hF hsub hfit hFO hp hFt hRS
    (fun _ _ => abortN2_slotRepAt h i himm) hz0 hrc hma hK hwr hwrW

end Place

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hkW_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hkW_ofPlaceOK

/-- info: 'Spike.Lib.LowerX64.stubWN_w2_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.stubWN_w2_ofPlaceOK

/-- info: 'Spike.Lib.LowerX64.mainAb_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainAb_seg

/-- info: 'Spike.Lib.LowerX64.mainAb_seg'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainAb_seg'
