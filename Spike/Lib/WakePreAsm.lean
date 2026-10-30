/-
**wake.w on AArch64, the pre-spawn obligations from a one-thread consumer**: `Spike.Lib.WakePreTi.Pre1T` at the relation
`R1 := RSAH Λ P wakeSrc G own I H μ ar` (`Spike/Lib/A64ConsumerA.lean`),
from the consumer's node obligations over a held predicate `H` and a
`clone` path `Cl` (`pre1T_of`).

- `rsah_size`: `RSAH` has one thread and one slot;
- `writeNoPromAH_of`: no promise at a `write` (`WriteNoPromAH`), from the
  certification at the call (`Kernel.prom_nil_of_write`);
- `promSharedAH_of`: `PromSharedAH` with no `write(1, …)` in the fragment
  (`hnw`; the certification has no step at a `write`) and the `clone`
  calls `Cl` from `hC.svc` (`promSharedAXCH`);
- `pre1T_of`: the obligations. `step` from `pre_stepAXCH` (no thread steps
  after the exit); `progress` from `pre_progressACH` (off `AtClone`, so off
  `Cl`: `hC.svc`, `cl_atClone`) and `r_memInAH`; `progressClone` at a
  `clone` from `Spike.Lib.CloneOne.clone_progress_up` (no promise at the
  `clone`, `Spike.Lib.Handover.prom_nil_of_clone`) and after the exit from
  `progress_up`; `abort` from `r_abortACH`; `wit` from `r_componentsAH`;
  `held` from `HeldPathS.own` (`Pre1.held_of`); `tiStep` from `ti_stepACH`.
  The load's relation `hinit` and `TIC` there `hti0`
  (`Spike.Lib.WakePreTi.ti0_of`) are the instance's.
- `init_of_loadAH`, `wake_init`: `hinit` at a one-thread start by
  `pre_loadAH`, and at wake.w's (`tidStartT 2`, heap use `hbox0` a
  hypothesis);
- `pre1T_of_seg`: `pre1T_of` from the segments (`inst_of_segWA2CH2`), at
  `I2 …` and `HeldOk2 Λ r0 r1`, `hnw` from the write tail `Dt` off fd 1.

wake.w's main writes nothing to fd 1 before its `clone` (`hnw`); the
aborts write to fd 2.
-/
import Spike.Lib.WakePreTi
import Spike.Lib.WriteDead
import Spike.Lib.A64SFactsACH

namespace Spike.Lib.WakePreAsm

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib.TwoSlot Spike.Lib.A64TwoSlot Spike.Lib.WakeT1 Spike.Lib.WakeA64 Spike.Lib.WakePre
open Spike.Lib.WakePreTi
open Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : InvS} {μ : Marks} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {H : State → List (Nat × Range) → Prop}

/-- **`RSAH` has one thread and one slot.** -/
theorem rsah_size {t : T.M.Cfg} {s : TermRun.Cfg} (h : RSAH Λ P p G own I H μ ar t s) :
    t.1.threads.size = t.2.slots.size := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, hth, ⟨E, hk⟩, _⟩ | ⟨_, _, _, _, _, _, _, _, _, hth, ⟨E, hk⟩, _⟩ <;>
    rw [hth, hk] <;> rfl

/-- **No promise at a `write`** over `H` (`writeNoPromA_b` over `PreSAH`):
the thread is certified at the call. -/
theorem writeNoPromAH_of {ab : Option (State → Prop)} {Cl : State → Prop} (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hT : HeldPathS Λ p μ I H) : WriteNoPromAH Λ P p G own I H μ ar := by
  intro t s th hpre hth hs ⟨fd, b, n, hc⟩
  obtain ⟨th', th0, j, lbl, lsize, ts, hl, pm, hd, hth', -, -, -, -, hcert, -, -, -, hI, -⟩ := hpre
  obtain rfl : th' = th := by
    have h := congrArg (fun a : Array _ => a[0]?) (hth'.symm.trans hth); exact Option.some.inj h
  exact Kernel.prom_nil_of_write (siteAt_noneA hN hI (hT.toTakeSiteS.off_sys hI hs)) hs hc hcert

/-- **`PromSharedAH` with no output `write` in the fragment** (`hnw`) and
the `clone` calls `Cl` (`hC.svc`): `promSharedAXCH`, the certification
having no step at a `write`. -/
theorem promSharedAH_of {Cl : State → Prop} (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I none Cl)
    (hsafe : SrcSafeS P p I) (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    (hT : HeldPathS Λ p μ I H)
    (hClc : ∀ s, Cl s → ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl)) :
    PromSharedAH Λ P p G own I H μ ar :=
  promSharedAXCH hP hN hsafe hrd hwf hGpl hok hT hClc fun _ _ _ _ _ _ _ hsi hs ⟨_, _, hd⟩ hso ho =>
    (Spike.Lib.WriteDead.certStep_write_none hsi hs hd hso ho).elim

/-- `RSAH`'s held ranges are the main thread's (`HeldPathS.own`), and it
has one thread. -/
theorem rsah_held (hT : HeldPathS Λ p μ I H) {t : T.M.Cfg} {s : TermRun.Cfg} (h : RSAH Λ P p G own I H μ ar t s) :
    t.1.threads.size = 1 ∧ ∀ x ∈ t.2.held, x.1 = 0 := by
  rcases h with ⟨_, _, _, _, _, _, hl, _, _, hth, ⟨E, hk⟩, -, hh, _⟩ |
    ⟨_, _, _, _, _, _, hl, _, _, hth, ⟨E, hk⟩, -, hh, _⟩ <;>
  · refine ⟨by rw [hth]; rfl, fun x hx => ?_⟩
    have e : t.2.held = hl := by rw [hk]; rfl
    rw [e] at hx
    exact (hT.own _ _ hh x hx).1

/-- **`RSAH` is explicit** (`r_componentsAH` for rows with a `clone` path). -/
theorem rsah_components {ab : Option (State → Prop)} {Cl : State → Prop} (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hwf : Λ.WF) (hT : HeldPathS Λ p μ I H) {t : T.M.Cfg} {s : TermRun.Cfg} (h : RSAH Λ P p G own I H μ ar t s) :
    ∃ w : Witness T.M, Components T.M Λ w t ((SrcSem.source P p).core s) := by
  rcases h with ⟨th, th0, j, lbl, lsize, ts, hl, pm, _, hth, ⟨E, hk⟩, -, hh, -, -, hs0, -, -, hI, -, -, -, hinv,
      hown, hmi, -⟩ |
    ⟨th, th0, j, lbl, lsize, ts, hl, pm, o, hth, ⟨E, hk⟩, -, hh, hs0, -, -, hpl, hinv, hown, hmi, -⟩
  · exact (components_oneSXH hwf hth (by rw [hk]; rfl) (hT.own _ _ hh) hmi hs0
      (by have hpl := hN.place _ _ _ _ _ hI; exact hpl) hinv hown).imp fun _ h => h.1
  · exact (components_oneSXH hwf hth (by rw [hk]; rfl) (hT.own _ _ hh) hmi hs0 hpl hinv hown).imp fun _ h => h.1

open Scc.Cert.Link in
/-- **The relation at the target's load over `H`** (`init_of_loadA` at a
start `s₀` with one thread `th₀`, by `pre_loadAH`): `pre1T_of`'s `hinit`
shape, the load given by its parse (`load_of_parsed`). -/
theorem init_of_loadAH {E : Entry} {prog : Program} {secs : DataSecs} {code : String → Option Nat} {lsize : Lsize}
    {name : WeakMem.AllocLabel → String} {s₀ : TermRun.Cfg} {th₀ : TermRun.TTh} (hwf : Λ.WF)
    (himg : imageOk Λ secs code = true) (hss : StaticSyms Λ secs code lsize name) (hw : wideIn prog = true)
    (hinit : P.init s₀) (hs0 : s₀.ths = #[th₀]) (hσ : th₀.σs = []) (hp : th₀.promises = [])
    (hsm : s₀.mem = #[]) (hhu : heapUse s₀ = 0)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) ⟨th₀.term, th₀.env, none⟩
      th₀.stack)
    (hfr0 : AllocInv.FreshInv Λ.static s₀.lbase s₀.n 0 th₀.nalloc)
    (hH0 : H (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) [])
    {t0 : T.M.Cfg} (hown0 : OwnInit (own (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) th₀.stack) t0.1.mem)
    (hg : MemInv G t0.1.mem) (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0)
    (hz0 : ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a → t0.1.mem.initVal (wordLoc a) = 0)
    (hc0 : t0.1.mem.initVal (wordLoc ar.ctr) = 0) (h : loadParsed (kernel 1) E Λ prog secs = some t0) :
    ∃ s, (SrcSem.source P p).init s ∧ RSAH Λ P p G own I H μ ar t0 s := by
  simp only [loadParsed] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    cases h
    refine ⟨s₀, hinit, .inl (pre_loadAH himg hss hw hinit hs0 hσ hp hsm hhu hst hfr0
      (loadMem_in hwf hc.1.1.1.1) ?_ hH0 hown0 hg hstat hsub hal hz0 hc0)⟩
    rw [imageMem, wordsMem, wordsMem, ← List.map_append]
    exact initFits_words fun q hq => (List.mem_append.mp hq).elim (image_fit hwf q) (rodataWords_fit _ _ _ q)
  · cases h

/-- `wake_init`'s thread: `main` entered on its own `ThreadId`. -/
abbrev wakeTh0 : TermRun.TTh := (tidStartT 2).ths[0]'(by decide)

open Scc.Cert.Link in
/-- **wake.w's load is related** (`pre1T_of`'s `hinit`, by `init_of_loadAH`
at the start `tidStartT 2`): the source start is `wake_start`'s, its heap
use `hbox0` (the main thread's `ThreadId` box) a hypothesis until the heap
box lands. -/
theorem wake_init {arch : WeakMem.Arch} {E : Entry} {asm : String} {prog : Program} {secs : DataSecs}
    {code : String → Option Nat} {lsize : Lsize} {name : WeakMem.AllocLabel → String}
    (hpa : textProgram asm = .ok prog) (hd : dataSections asm = some secs) (hwf : Λ.WF)
    (himg : imageOk Λ secs code = true) (hss : StaticSyms Λ secs code lsize name) (hw : wideIn prog = true)
    (hbox0 : heapUse (tidStartT 2) = 0)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata))
      ⟨wakeTh0.term, wakeTh0.env, none⟩ wakeTh0.stack)
    (hfr0 : AllocInv.FreshInv Λ.static (tidStartT 2).lbase (tidStartT 2).n 0 wakeTh0.nalloc)
    (hH0 : H (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) [])
    (hown0 : ∀ t0 : T.M.Cfg, loadParsed (kernel 1) E Λ prog secs = some t0 →
      OwnInit (own (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) wakeTh0.stack) t0.1.mem ∧
      MemInv G t0.1.mem ∧ (∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a → t0.1.mem.initVal (wordLoc a) = 0) ∧
      t0.1.mem.initVal (wordLoc ar.ctr) = 0)
    (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0) :
    ∀ d : Cfg, (target (kernel 1) E).load asm Λ = some d →
      ∃ s0, (wakeS arch).init s0 ∧ RSAH Λ (srcPo 2 arch wakeSrc) wakeSrc G own I H μ ar d s0 := by
  intro d h
  have hl : loadParsed (kernel 1) E Λ prog secs = some d := (load_of_parsed (kernel 1) E Λ hpa hd).symm.trans h
  obtain ⟨ho, hg, hz0, hc0⟩ := hown0 d hl
  exact init_of_loadAH (P := srcPo 2 arch wakeSrc) (th₀ := wakeTh0) hwf himg hss hw
    (show progInitT wakeSrc 2 (tidStartT 2) by rw [wake_start]) rfl rfl rfl rfl hbox0 hst hfr0 hH0 ho hg hstat
    hsub hal hz0 hc0 hl

/-- **The pre-spawn obligations of wake.w from the consumer's** at
`R1 := RSAH` over `H`, with the `clone` path `Cl`: the node obligations
`hN` (rows at the loaded program's marks), the `clone` path `hC` (its
calls `hClc`), the held path `hT`, the abort path `hA` (budget `hB`), no
output `write` before the `clone` (`hnw`), the load's relation `hinit` and
its `TIC` (`hti0`). -/
theorem pre1T_of {arch : WeakMem.Arch} {B : Budget} {asm : String} {E : Entry} {Cl Ab Ac : State → Prop}
    (hμ : μ = (target (kernel 2) E).marks asm Λ)
    (hP : HookOK (srcPo 2 arch wakeSrc) wakeSrc) (hN : NodesA Λ wakeSrc μ rd G own ar I none Cl)
    (hC : ClonePathS wakeSrc I Cl)
    (hClc : ∀ s, Cl s → ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hsafe : SrcSafeS (srcPo 2 arch wakeSrc) wakeSrc I) (hT : HeldPathS Λ wakeSrc μ I H)
    (hrd : SrcRd (srcPo 2 arch wakeSrc) wakeSrc rd) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    (hA : AbortPathSC μ I Cl Ab Ac ar.cells ar.ctr) (hB : B.cells = ar.cells)
    (hnw : ∀ lbl lsize s c fs, I lbl lsize s c fs → abi.atSys s = true →
      ∀ buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 buf n))
    (hinit : ∀ d : Cfg, (target (kernel 1) E).load asm Λ = some d →
      ∃ s0, (wakeS arch).init s0 ∧ RSAH Λ (srcPo 2 arch wakeSrc) wakeSrc G own I H μ ar d s0)
    (hti0 : ∀ d : Cfg, (target (kernel 1) E).load asm Λ = some d → TIC Ab Ac [] d) :
    Pre1T arch Λ B asm E (RSAH Λ (srcPo 2 arch wakeSrc) wakeSrc G own I H μ ar) Ab Ac := by
  subst hμ
  have hps := promSharedAH_of (own := own) hP hN hsafe hrd hwf hGpl hok hT hClc
  have hsvc : WriteNoPromAH Λ (srcPo 2 arch wakeSrc) wakeSrc G own I H _ ar := writeNoPromAH_of hN hT
  refine ⟨hinit, ?step, ?progress, ?progressClone, ?abort, ?wit, ?held, hti0, ?tiStep⟩
  case step =>
    intro tid d es d' s h _ hs
    rcases h with h | ⟨_, _, _, _, _, _, _, _, o, _, ⟨_, hk⟩, _⟩
    · obtain ⟨s', hr, h'⟩ := pre_stepAXCH hP hN hC hsafe hT hps hrd hwf hGpl hok h
        (fun th buf n hth hsys hc => by
          obtain ⟨th', _, _, lbl, lsize, _, _, _, _, hth', _, _, _, _, _, _, _, _, hI, _⟩ := h
          rw [hth] at hth'
          cases (Array.mk.injEq _ _).mp hth' |> List.cons.inj |>.1
          exact hnw _ _ _ _ _ hI hsys buf n hc) hs
      exact ⟨s', hr, h', rsah_size h'⟩
    · exact (Kernel.exited_no_step abi (o := o) (by rw [hk]) hs).elim
  case progress =>
    intro d s h _ hnc
    refine ⟨?_, inLayout_of_memIn (r_memInAH h)⟩
    rcases h with h | h
    · refine pre_progressACH hN hA hT hwf hsvc h fun th hth hcl => hnc ?_
      obtain ⟨th', _, _, lbl, lsize, _, _, _, _, hth', ⟨E', hk⟩, _, _, _, _, _, _, _, hI, _⟩ := h
      rw [hth] at hth'
      cases (Array.mk.injEq _ _).mp hth' |> List.cons.inj |>.1
      obtain ⟨hsys, st, tl, hd⟩ := hC.svc _ _ _ _ _ hI hcl
      exact ⟨0, th, st, tl, by rw [hth]; rfl, hsys, by rw [hk]; rfl, hd⟩
    · exact post_progressSAH h
  case progressClone =>
    intro d u s h hu hpl hn hc
    rcases h with h | h
    · refine Pre1.progressClone_of (Λ := Λ) (R1 := fun d s => PreSAH Λ (srcPo 2 arch wakeSrc) wakeSrc G own I H
        ((target (kernel 2) E).marks asm Λ) ar d s) ?_ d u s h hu hpl hn hc
      intro d s h _ hc
      obtain ⟨th, _, _, lbl, lsize, _, _, _, _, hth, ⟨E', hk⟩, _, _, _, hcert, _, _, _, hI, _, _, _, _, _, hmi, _⟩ :=
        h
      obtain ⟨tid, th', st, tl, ht, ha, -, hcall⟩ := hc
      obtain ⟨rfl, rfl⟩ := get_one hth ht
      obtain ⟨imm, sz, hcell⟩ := hN.svc _ _ _ _ _ hI ha
      refine ⟨th, hth, by rw [hk]; rfl, by rw [hk]; rfl, ?_, ?_, inLayout_of_memIn hmi⟩
      · simp [Thread.halted, Kraken.Promising.Lower.A64.exec_svc hcell]
      · exact Spike.Lib.Handover.prom_nil_of_clone (siteAt_noneA hN hI (hT.toTakeSiteS.off_sys hI ha)) ha hcall
          hcert
    · exact ⟨progress_up hn hu (post_progressSAH h), inLayout_up.mpr (inLayout_of_memIn
        (r_memInAH (G := G) (own := own) (I := I) (ar := ar) (μ := (target (kernel 2) E).marks asm Λ) (.inr h)))⟩
  case abort =>
    intro tr d s tid es d' k _ h _ hti hs hk
    exact r_abortACH hN hsafe hwf hA hB hT h hti hs hk
  case wit =>
    intro d s h _
    exact rsah_components hN hwf hT h
  case held =>
    exact Pre1.held_of fun d s h _ => rsah_held hT h
  case tiStep =>
    intro tid d es d' s pre h _ hs hti
    exact ti_stepACH hN hC hA hT h hs hti

/-! ## From the segments -/

open Spike.Lib.HeapLand (AllocLand) in
/-- **The pre-spawn obligations from the consumer's segments**
(`pre1T_of` after `inst_of_segWA2CH2`): main's code as a segment `h0`
before the allocation and `h1` after it, every state with `SFactsACH`
(`hW0`, `hW1`), the take at `a` naming `r0` then `r1` (`hsplit`), the write
tail `Dt` off fd 1 (`hdt`); `I` is `I2 ar L0 ls0 inv0 inv1` and `H` is
`HeldOk2 Λ r0 r1`. -/
theorem pre1T_of_seg {arch : WeakMem.Arch} {B : Budget} {asm : String} {E : Entry} {Cl Ab Ac Dt : State → Prop}
    {L0 : Lbl} {ls0 : Lsize} {a : Int64}
    {W0 inv0 : FragS isaLSE2} {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {r0 r1 : Range}
    (hμ : μ = (target (kernel 2) E).marks asm Λ)
    (h1 : ∀ l b n, L0 l = none → AllocLand ar.heap ar.cells b n →
      SegInvS (W1 l b n) (TakeCKS a Cl) wakeSrc (A64ConsumerA.upd L0 l b)
        (msOfA Λ μ rd G own ar (fun _ _ _ _ _ => False) (A64ConsumerA.upd L0 l b) (A64ConsumerA.updN ls0 l n))
        (inv1 l b n))
    (h0 : SegInvS W0 (TakeCKS a Cl) wakeSrc L0 (msOfA Λ μ rd G own ar (I2 ar L0 ls0 inv0 inv1) L0 ls0) inv0)
    (ha : μ.site .take = some a.toBitVec.toNat)
    (hW0 : ∀ s c fs, inv0 s c fs → W0 s c fs →
      SFactsACH Λ μ wakeSrc rd G own ar (I2 ar L0 ls0 inv0 inv1) L0 ls0 s c fs Dt Ab Cl Ac)
    (hW1 : ∀ l b n s c fs, L0 l = none → AllocLand ar.heap ar.cells b n → W1 l b n s c fs →
      SFactsACH Λ μ wakeSrc rd G own ar (I2 ar L0 ls0 inv0 inv1) (A64ConsumerA.upd L0 l b)
        (A64ConsumerA.updN ls0 l n) s c fs Dt Ab Cl Ac)
    (hsplit : ∀ lbl lsize s c fs hl, I2 ar L0 ls0 inv0 inv1 lbl lsize s c fs → HeldOk2 Λ r0 r1 s hl →
      ∀ a, μ.site .take = some a → pcOf s = a →
        (hl = [] ∧ Kernel.siteRange abi s = r0) ∨ (hl = [(0, r0)] ∧ Kernel.siteRange abi s = r1))
    (hs0 : r0.Sub Λ.stackPool) (hs1 : r1.Sub Λ.stackPool) (hz0 : 0 < r0.size) (hz1 : 0 < r1.size)
    (hro : Λ.rodata.Disjoint Λ.stackPool) (hd : r1.Disjoint r0)
    (hw0 : r0.lo + r0.size ≤ 2 ^ 64) (hw1 : r1.lo + r1.size ≤ 2 ^ 64)
    (hP : HookOK (srcPo 2 arch wakeSrc) wakeSrc)
    (hClc : ∀ s, Cl s → ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hsafe : SrcSafeS (srcPo 2 arch wakeSrc) wakeSrc (I2 ar L0 ls0 inv0 inv1))
    (hrd : SrcRd (srcPo 2 arch wakeSrc) wakeSrc rd) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    (hB : B.cells = ar.cells)
    (hdt : ∀ s buf n, Dt s → Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 buf n))
    (hinit : ∀ d : Cfg, (target (kernel 1) E).load asm Λ = some d →
      ∃ s0, (wakeS arch).init s0 ∧
        RSAH Λ (srcPo 2 arch wakeSrc) wakeSrc G own (I2 ar L0 ls0 inv0 inv1) (HeldOk2 Λ r0 r1) μ ar d s0)
    (hti0 : ∀ d : Cfg, (target (kernel 1) E).load asm Λ = some d → TIC Ab Ac [] d) :
    Pre1T arch Λ B asm E
      (RSAH Λ (srcPo 2 arch wakeSrc) wakeSrc G own (I2 ar L0 ls0 inv0 inv1) (HeldOk2 Λ r0 r1) μ ar) Ab Ac := by
  obtain ⟨hN, hT, hA, hWr, hC⟩ := inst_of_segWA2CH2 h1 h0 ha hW0 hW1 hsplit hs0 hs1 hz0 hz1 hro hd hw0 hw1
  exact pre1T_of hμ hP hN hC hClc hsafe hT hrd hwf hGpl hok hA hB
    (fun _ _ _ _ _ hI hsys buf n hc => hdt _ buf n (hWr _ _ _ _ _ hI hsys 1 buf n hc) hc) hinit hti0

/-- info: 'Spike.Lib.WakePreAsm.init_of_loadAH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms init_of_loadAH

/-- info: 'Spike.Lib.WakePreAsm.wake_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wake_init

/-- info: 'Spike.Lib.WakePreAsm.pre1T_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pre1T_of

/-- info: 'Spike.Lib.WakePreAsm.promSharedAH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms promSharedAH_of

/-- info: 'Spike.Lib.WakePreAsm.writeNoPromAH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms writeNoPromAH_of

/-- info: 'Spike.Lib.WakePreAsm.rsah_components' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rsah_components

/-- info: 'Spike.Lib.WakePreAsm.pre1T_of_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pre1T_of_seg

end Spike.Lib.WakePreAsm
