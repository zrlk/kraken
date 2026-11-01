/-
**hello.w on AArch64, the pre-spawn obligations from a one-thread consumer**
(B5 check-in 2): `Spike.Lib.WakePreAsm`'s `pre1T_of` / `pre1T_of_seg` /
`wake_init` at `helloSrc`, over the two-allocation invariant `I3`
(`Spike.Lib.A64SegInstA3`).

- `pre1T_ofG`: `WakePreAsm.pre1T_of` for any program `p` (the proof copied;
  `pre1T_of`'s helpers `promSharedAH_of`, `writeNoPromAH_of`, `rsah_size`,
  `rsah_held`, `rsah_components` are generic and reused), result
  `Pre1T … (p := p)`;
- `pre1T_of_seg3`: `pre1T_ofG` at `helloSrc` from the segments
  (`inst_of_segWA3CH2`), at `I3 …` and `HeldOk2 Λ r0 r1`, `hnw` from the
  write tail `Dt` off fd 1;
- `helloTh0`, `hello_init`: the load's relation at hello.w's start
  (`HelloSrc.hello_start`, `setupStartT 2`) by `WakePreAsm.init_of_loadAH`,
  the start's heap use `0` by `decide` (`hbox0H`; as wake's root discharges
  `wake_init`'s `hbox0`, `WakeOHinit.hinit_W`).

`WakePreAsm` is in wake's import closure and is not edited.
-/
import Spike.Lib.WakePreAsm
import Spike.Lib.A64SegInstA3
import Spike.Lib.HelloSrc

namespace Spike.Lib.HelloPreAsm

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib.TwoSlot Spike.Lib.A64TwoSlot Spike.Lib.WakeT1 Spike.Lib.WakeA64 Spike.Lib.WakePre
open Spike.Lib.WakePreTi Spike.Lib.WakePreAsm
open Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.HelloSrc (helloSrc hello_start)

variable {p : Prog} {Λ : Scc.Sem.Layout} {I : InvS} {μ : Marks} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {H : State → List (Nat × Range) → Prop}

/-- **The pre-spawn obligations of program `p` from the consumer's**
(`WakePreAsm.pre1T_of` with `wakeSrc` generalised to `p`; the proof is
`pre1T_of`'s). -/
theorem pre1T_ofG {arch : WeakMem.Arch} {B : Budget} {asm : String} {E : Entry} {Cl Ab Ac : State → Prop}
    (hμ : μ = (target (kernel 2) E).marks asm Λ)
    (hP : HookOK (srcPo 2 arch p) p) (hN : NodesA Λ p μ rd G own ar I none Cl)
    (hC : ClonePathS p I Cl)
    (hClc : ∀ s, Cl s → ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hsafe : SrcSafeS (srcPo 2 arch p) p I) (hT : HeldPathS Λ p μ I H)
    (hrd : SrcRd (srcPo 2 arch p) p rd) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    (hA : AbortPathSC μ I Cl Ab Ac ar.cells ar.ctr) (hB : B.cells = ar.cells)
    (hnw : ∀ lbl lsize s c fs, I lbl lsize s c fs → abi.atSys s = true →
      ∀ buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 buf n))
    (hinit : ∀ d : Cfg, (target (kernel 1) E).load asm Λ = some d →
      ∃ s0, (srcS p arch).init s0 ∧ RSAH Λ (srcPo 2 arch p) p G own I H μ ar d s0)
    (hti0 : ∀ d : Cfg, (target (kernel 1) E).load asm Λ = some d → TIC Ab Ac [] d) :
    Pre1T arch Λ B asm E (RSAH Λ (srcPo 2 arch p) p G own I H μ ar) Ab Ac p := by
  subst hμ
  have hps := promSharedAH_of (own := own) hP hN hsafe hrd hwf hGpl hok hT hClc
  have hsvc : WriteNoPromAH Λ (srcPo 2 arch p) p G own I H _ ar := writeNoPromAH_of hN hT
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
    · refine Pre1.progressClone_of (Λ := Λ) (R1 := fun d s => PreSAH Λ (srcPo 2 arch p) p G own I H
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
/-- **hello.w's pre-spawn obligations from the consumer's segments**
(`pre1T_ofG` after `inst_of_segWA3CH2`; `WakePreAsm.pre1T_of_seg` at
`I3`): main's code as `h0` before the first allocation (rodata's buffer),
`h1` between the two, `h2` after the second (the box) up to the `clone`,
every state with `SFactsACH` (`hW0`, `hW1`, `hW2`), the take at `a` naming
`r0` then `r1` (`hsplit`), the write tail `Dt` off fd 1 (`hdt`). -/
theorem pre1T_of_seg3 {arch : WeakMem.Arch} {B : Budget} {asm : String} {E : Entry} {Cl Ab Ac Dt : State → Prop}
    {L0 : Lbl} {ls0 : Lsize} {a : Int64} {W0 inv0 : FragS isaLSE2}
    {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {r0 r1 : Range}
    (hμ : μ = (target (kernel 2) E).marks asm Λ)
    (h2 : ∀ l b n l' b' n', L0 l = none → AllocLand ar.heap ar.cells b n → A64ConsumerA.upd L0 l b l' = none →
      AllocLand ar.heap ar.cells b' n' →
      SegInvS (W2 l b n l' b' n') (TakeCKS a Cl) helloSrc (A64ConsumerA.upd (A64ConsumerA.upd L0 l b) l' b')
        (msOfA Λ μ rd G own ar (fun _ _ _ _ _ => False) (A64ConsumerA.upd (A64ConsumerA.upd L0 l b) l' b')
          (A64ConsumerA.updN (A64ConsumerA.updN ls0 l n) l' n'))
        (inv2 l b n l' b' n'))
    (h1 : ∀ l b n, L0 l = none → AllocLand ar.heap ar.cells b n →
      SegInvS (W1 l b n) (TakeCKS a Cl) helloSrc (A64ConsumerA.upd L0 l b)
        (msOfA Λ μ rd G own ar (I3 ar L0 ls0 inv0 inv1 inv2) (A64ConsumerA.upd L0 l b)
          (A64ConsumerA.updN ls0 l n)) (inv1 l b n))
    (h0 : SegInvS W0 (TakeCKS a Cl) helloSrc L0 (msOfA Λ μ rd G own ar (I3 ar L0 ls0 inv0 inv1 inv2) L0 ls0) inv0)
    (ha : μ.site .take = some a.toBitVec.toNat)
    (hW0 : ∀ s c fs, inv0 s c fs → W0 s c fs →
      SFactsACH Λ μ helloSrc rd G own ar (I3 ar L0 ls0 inv0 inv1 inv2) L0 ls0 s c fs Dt Ab Cl Ac)
    (hW1 : ∀ l b n s c fs, L0 l = none → AllocLand ar.heap ar.cells b n → W1 l b n s c fs →
      SFactsACH Λ μ helloSrc rd G own ar (I3 ar L0 ls0 inv0 inv1 inv2) (A64ConsumerA.upd L0 l b)
        (A64ConsumerA.updN ls0 l n) s c fs Dt Ab Cl Ac)
    (hW2 : ∀ l b n l' b' n' s c fs, L0 l = none → AllocLand ar.heap ar.cells b n →
      A64ConsumerA.upd L0 l b l' = none → AllocLand ar.heap ar.cells b' n' → W2 l b n l' b' n' s c fs →
      SFactsACH Λ μ helloSrc rd G own ar (I3 ar L0 ls0 inv0 inv1 inv2)
        (A64ConsumerA.upd (A64ConsumerA.upd L0 l b) l' b')
        (A64ConsumerA.updN (A64ConsumerA.updN ls0 l n) l' n') s c fs Dt Ab Cl Ac)
    (hsplit : ∀ lbl lsize s c fs hl, I3 ar L0 ls0 inv0 inv1 inv2 lbl lsize s c fs → HeldOk2 Λ r0 r1 s hl →
      ∀ a, μ.site .take = some a → pcOf s = a →
        (hl = [] ∧ Kernel.siteRange abi s = r0) ∨ (hl = [(0, r0)] ∧ Kernel.siteRange abi s = r1))
    (hs0 : r0.Sub Λ.stackPool) (hs1 : r1.Sub Λ.stackPool) (hz0 : 0 < r0.size) (hz1 : 0 < r1.size)
    (hro : Λ.rodata.Disjoint Λ.stackPool) (hd : r1.Disjoint r0)
    (hw0 : r0.lo + r0.size ≤ 2 ^ 64) (hw1 : r1.lo + r1.size ≤ 2 ^ 64)
    (hP : HookOK (srcPo 2 arch helloSrc) helloSrc)
    (hClc : ∀ s, Cl s → ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hsafe : SrcSafeS (srcPo 2 arch helloSrc) helloSrc (I3 ar L0 ls0 inv0 inv1 inv2))
    (hrd : SrcRd (srcPo 2 arch helloSrc) helloSrc rd) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    (hB : B.cells = ar.cells)
    (hdt : ∀ s buf n, Dt s → Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 buf n))
    (hinit : ∀ d : Cfg, (target (kernel 1) E).load asm Λ = some d →
      ∃ s0, (srcS helloSrc arch).init s0 ∧
        RSAH Λ (srcPo 2 arch helloSrc) helloSrc G own (I3 ar L0 ls0 inv0 inv1 inv2) (HeldOk2 Λ r0 r1) μ ar d s0)
    (hti0 : ∀ d : Cfg, (target (kernel 1) E).load asm Λ = some d → TIC Ab Ac [] d) :
    Pre1T arch Λ B asm E
      (RSAH Λ (srcPo 2 arch helloSrc) helloSrc G own (I3 ar L0 ls0 inv0 inv1 inv2) (HeldOk2 Λ r0 r1) μ ar) Ab Ac
      helloSrc := by
  obtain ⟨hN, hT, hA, hWr, hC⟩ :=
    inst_of_segWA3CH2 h2 h1 h0 ha hW0 hW1 hW2 hsplit hs0 hs1 hz0 hz1 hro hd hw0 hw1
  exact pre1T_ofG hμ hP hN hC hClc hsafe hT hrd hwf hGpl hok hA hB
    (fun _ _ _ _ _ hI hsys buf n hc => hdt _ buf n (hWr _ _ _ _ _ hI hsys 1 buf n hc) hc) hinit hti0

/-! ## The load -/

/-- `hello_init`'s thread: before the setup block on its own `ThreadId`. -/
abbrev helloTh0 : TermRun.TTh := (setupStartT 2).ths[0]'(by decide)

/-- hello.w's start has no heap use (`decide`, as wake's root discharges
`WakePreAsm.wake_init`'s `hbox0` at `tidStartT 2`). -/
theorem hbox0H : heapUse (setupStartT 2) = 0 := by decide

open Scc.Cert.Link in
/-- **hello.w's load is related** (`pre1T_of_seg3`'s `hinit`, by
`WakePreAsm.init_of_loadAH` at the start `setupStartT 2`, `hello_start`,
heap use `hbox0H`). -/
theorem hello_init {arch : WeakMem.Arch} {E : Entry} {asm : String} {prog : Program} {secs : DataSecs}
    {code : String → Option Nat} {lsize : Lsize} {name : WeakMem.AllocLabel → String}
    (hpa : textProgram asm = .ok prog) (hd : dataSections asm = some secs) (hwf : Λ.WF)
    (himg : imageOk Λ secs code = true) (hss : StaticSyms Λ secs code lsize name) (hw : wideIn prog = true)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata))
      ⟨helloTh0.term, helloTh0.env, none⟩ helloTh0.stack)
    (hfr0 : AllocInv.FreshInv Λ.static (setupStartT 2).lbase (setupStartT 2).n 0 helloTh0.nalloc)
    (hH0 : H (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) [])
    (hown0 : ∀ t0 : T.M.Cfg, loadParsed (kernel 1) E Λ prog secs = some t0 →
      OwnInit (own (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) helloTh0.stack) t0.1.mem ∧
      MemInv G t0.1.mem ∧ (∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a → t0.1.mem.initVal (wordLoc a) = 0) ∧
      t0.1.mem.initVal (wordLoc ar.ctr) = 0)
    (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0) :
    ∀ d : Cfg, (target (kernel 1) E).load asm Λ = some d →
      ∃ s0, (srcS helloSrc arch).init s0 ∧ RSAH Λ (srcPo 2 arch helloSrc) helloSrc G own I H μ ar d s0 := by
  intro d h
  have hl : loadParsed (kernel 1) E Λ prog secs = some d := (load_of_parsed (kernel 1) E Λ hpa hd).symm.trans h
  obtain ⟨ho, hg, hz0, hc0⟩ := hown0 d hl
  exact init_of_loadAH (P := srcPo 2 arch helloSrc) (th₀ := helloTh0) hwf himg hss hw
    (show progInitT helloSrc 2 (setupStartT 2) by rw [hello_start]) rfl rfl rfl rfl hbox0H hst hfr0 hH0 ho hg hstat
    hsub hal hz0 hc0 hl

end Spike.Lib.HelloPreAsm

/-- info: 'Spike.Lib.HelloPreAsm.pre1T_ofG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPreAsm.pre1T_ofG

/-- info: 'Spike.Lib.HelloPreAsm.pre1T_of_seg3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPreAsm.pre1T_of_seg3

/-- info: 'Spike.Lib.HelloPreAsm.hello_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPreAsm.hello_init
