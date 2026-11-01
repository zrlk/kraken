/-
**hello.w's load is related at the root** (AArch64, the root's loader facts; the twin of
`WakeLoadT.wake_initT` / `WakeOHinit.hinit_W` at hello's start `setupStartT 2` and global map `ownGH`).

The start's labels are `L0T` (main's `ThreadId` box at `tcb0`, as at wake: hello's start is `setupStartT 2`,
whose thread holds that box), its sizes `ls0T`.

- `freshH`: `setupStartT 2`'s labels past the box are unplaced at `L0T` (`WakeLoadT.freshT`'s twin).
- `hello_initT`: the load's relation `RSAH` at `L0T`/`ls0T` from the start in `I` (`wake_initT`'s twin, by
  `WakeLoadT.init_of_loadAHT` at `helloTh0`, `hello_start`, `hbox0H`).
- `hinit_H`: `HelloO.OPremH.hinit`'s shape at the root's choices (`gWH … cTW`, `ownGH … ntA`, `arW`, `r0W`/`r1W`;
  `WakeOHinit.hinit_W`'s twin, `hown0` by `HelloOInit.hown0_H`). Open: the start in `inv0` (`hst`; at the root
  `RootH0.hstH`).
-/
import Spike.Lib.WakeOHinit
import Spike.Lib.WakeLoadT
import Spike.Lib.HelloPreAsm
import Spike.Lib.HelloOInit
import Spike.Lib.WakeHG
import Spike.Lib.HelloGOf2H

namespace Spike.Lib.HelloOHinit

variable {asm : String}

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.WakeT1 Spike.Lib.WakeA64 Spike.Lib.WakePre Spike.Lib.WakePreTi Spike.Lib.WakePreAsm
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.WakeLoadT (L0T ls0T l0T_some init_of_loadAHT)
open Spike.Lib.HelloSrc (helloSrc hello_start)
open Spike.Lib.HelloPreAsm (helloTh0 hbox0H)

variable {Λ : Scc.Sem.Layout}

/-- **`setupStartT 2`'s labels past the box are unplaced** at `L0T` (`WakeLoadT.freshT`'s twin). -/
theorem freshH (hstat : Λ.static = fun _ => none) :
    AllocInv.FreshInv (L0T Λ) (setupStartT 2).lbase (setupStartT 2).n 0 helloTh0.nalloc := by
  intro k hk
  cases h : L0T Λ (TermRun.freshLabel (setupStartT 2).lbase (setupStartT 2).n 0 k) with
  | none => rfl
  | some b =>
    obtain ⟨he, -⟩ := l0T_some hstat h
    have hn : (setupStartT 2).n = 2 := by decide
    have hl : (setupStartT 2).lbase = 0 := rfl
    have hna : helloTh0.nalloc = 1 := rfl
    rw [hn, hl] at he
    rw [hna] at hk
    have hm : mainTidLbl 2 = 0 := rfl
    rw [hm] at he
    simp only [TermRun.freshLabel] at he
    exfalso
    simp at he
    rcases k with _ | k
    · exact absurd hk (by decide)
    · exact absurd he (by simp [Nat.mul_succ])

section Load

variable {I : InvS} {μ : Marks} {G : Loc → Val → Prop} {own : OwnS} {ar : Arena}
  {H : State → List (Nat × Range) → Prop}

open Scc.Cert.Link in
/-- **hello.w's load is related** at `L0T`/`ls0T` (`WakeLoadT.wake_initT`'s twin at `setupStartT 2`). -/
theorem hello_initT {arch : WeakMem.Arch} {E : Entry} {asm : String} {prog : Program} {secs : DataSecs}
    {lsize : Lsize}
    (hpa : textProgram asm = .ok prog) (hd : dataSections asm = some secs) (hwf : Λ.WF)
    (hpz : 8 ≤ Λ.pinned.size) (hw : wideIn prog = true)
    (hst : I (L0T Λ) (ls0T lsize) (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata))
      ⟨helloTh0.term, helloTh0.env, none⟩ helloTh0.stack)
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
  exact init_of_loadAHT (P := srcPo 2 arch helloSrc) (th₀ := helloTh0) hwf hpz hw
    (show progInitT helloSrc 2 (setupStartT 2) by rw [hello_start]) rfl rfl rfl rfl hbox0H hst (freshH hstat) hH0
    ho hg hstat hsub hal hz0 hc0 hl

end Load

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- **`OPremH.hinit` at the root's choices** (see the module doc): the start in `I` at `L0T`/`ls0T` (`hst`) makes
the load related at `gWH … cTW`, `ownGH … ntA`, `arW`, `HeldOk2 … r0W r1W`. -/
theorem hinit_H (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg) (hd : dataSections asm = some o.secs)
    /- instance facts -/
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hsub1 : (Spike.Lib.WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hnz : Spike.Lib.WakeOInit.NtZ Λ0 o = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (arch : WeakMem.Arch) {E : Entry} (hE : E.clear (Ly).Λ = true) (μ : Marks)
    (I : InvS) (ls : Lsize)
    /- open: the start in `I` (at the root `RootH0.hstH`) -/
    (hst : I (L0T (Ly).Λ) (ls0T ls) (threadAt E (Ly).Λ.code.lo o.prog (loadSyms (Ly).Λ o.secs.rodata))
      ⟨helloTh0.term, helloTh0.env, none⟩ helloTh0.stack) :
    ∀ d : Cfg, (target (kernel 1) E).load asm (Ly).Λ = some d →
      ∃ s0, (srcS helloSrc arch).init s0 ∧
        RSAH (Ly).Λ (srcPo 2 arch helloSrc) helloSrc (Spike.Lib.HelloGOf2H.gWH hp i (Spike.Lib.WakeHG.cTW hp i))
          (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) I
          (HeldOk2 (Ly).Λ (Spike.Lib.WakeOSide.r0W hp i) (Spike.Lib.WakeOSide.r1W hp i)) μ
          (Spike.Lib.WakeOD.arW hp i) d s0 := by
  have hpz : 8 ≤ (Ly).Λ.pinned.size := by
    have := PlaceW.pinA_toNat_ofPlaceW hp i; omega
  refine hello_initT (lsize := ls) hpa hd (Spike.Lib.WakeOSide.hwf_W hp i) hpz
    (PlaceW.wideIn_of_placeW hp) hst
    (Spike.Lib.WakeOHinit.hH0_W hp i hE hsub1) (fun t0 hl => ⟨Spike.Lib.HelloOInit.hown0_H hp i hpa hhp hlo
      (Spike.Lib.WakeOInit.hnt_of hp i hnz) E t0 hl, ?_, ?_, ?_⟩) hstat
    (Spike.Lib.A64.Rt.ArenaW.arOf_sub (PlaceW.link i hp)) (Spike.Lib.A64.Rt.ArenaW.arOf_al (PlaceW.link i hp))
  all_goals
    have he : Scc.Sem.A64.loadParsed (Scc.Sem.A64.kernel 1) E (Ly).Λ o.prog o.secs = _ :=
      Scc.Cert.Link.A64.loadParsed_of_loadOk (H := Scc.Sem.A64.kernel 1) (PlaceW.loadOk_link_of_placeW i hp) hE
    rw [he] at hl
    cases hl
  · exact Spike.Lib.WakeG.memInv_wakeG (Scc.Sem.memInv_fixG_load rfl rfl)
  · exact fun a ha => Spike.Lib.A64.Rt.ArenaW.arOf_z0 (PlaceW.link i hp) hc rfl ha
  · exact Spike.Lib.A64.Rt.ArenaW.arOf_c0 (PlaceW.link i hp) hc rfl

end Place

end Spike.Lib.HelloOHinit

/-- info: 'Spike.Lib.HelloOHinit.hello_initT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloOHinit.hello_initT

/-- info: 'Spike.Lib.HelloOHinit.hinit_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloOHinit.hinit_H
