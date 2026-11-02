/-
**hello.w on x86-64: the load is related at the root** (the root's loader facts; the twin of
`X64WakeLoadT.wake_initT` / `X64WakeOHinit.hinit_W` at hello's start `setupStartT 2` and global map `ownGH`).

The start's labels are `L0T` (main's `ThreadId` box at `tcb0`, as at wake: hello's start is `setupStartT 2`,
whose thread holds that box), its sizes `ls0T`.

- `freshH`: `setupStartT 2`'s labels past the box are unplaced at `L0T` (`X64WakeLoadT.freshT`'s twin).
- `hello_initT`: the load's relation `RSAH` at `L0T`/`ls0T` from the start in `I` (`wake_initT`'s twin, by
  `X64WakeLoadT.init_of_loadAHT` at `helloTh0`, `hello_start`, `hbox0H`).
- `hinit_Hg`: `X64HelloO.OPremH.hinit`'s shape at the root's choices (`gWH … cTW`, `arW`, `r0W`/`r1W`;
  `X64WakeOHinit.hinit_W`'s twin) at any owned words `own`. Hypotheses: `own` initially owned at the load (`hown0`)
  and the start in `inv0` (`hst`; at the root `RootH0.hstH`).
- `hinit_H`: `hinit_Hg` at `ownGH … ntA`, `hown0` by `X64HelloOInit.hown0_H`.

x86-64 twin of `Spike/Lib/HelloOHinit.lean` (same names, namespaces with the `X64` prefix).
Unlike AArch64, the program is `cellsOf asm` (placed cells, not `textProgram`), the data
sections are `dataSections asm.text`, `loadParsed` takes the label offsets (`hoffs : asm.labelOffs =
o.labelOffs` in `hinit_H`), and the link lemma is `Scc.Cert.Link.X64.loadParsed_of_loadOk`.
-/
import Spike.Lib.X64WakeOHinit
import Spike.Lib.X64WakeLoadT
import Spike.Lib.X64HelloPreAsm
import Spike.Lib.X64HelloOInit
import Spike.Lib.X64WakeHG
import Spike.Lib.X64HelloGOf2H

namespace Spike.Lib.X64HelloOHinit

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.X64WakeT1 Spike.Lib.X64WakeA64 Spike.Lib.X64WakePre Spike.Lib.X64WakePreTi Spike.Lib.X64WakePreAsm
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64WakeLoadT (L0T ls0T l0T_some init_of_loadAHT)
open Spike.Lib.X64HelloSrc (helloSrc hello_start)
open Spike.Lib.X64HelloPreAsm (helloTh0 hbox0H)

variable {Λ : Scc.Sem.Layout}

/-- **`setupStartT 2`'s labels past the box are unplaced** at `L0T` (`X64WakeLoadT.freshT`'s twin). -/
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
/-- **hello.w's load is related** at `L0T`/`ls0T` (`X64WakeLoadT.wake_initT`'s twin at `setupStartT 2`). -/
theorem hello_initT {arch : WeakMem.Arch} {E : Entry} {asm : Asm} {prog : List (Directive × Nat)}
    {secs : DataSecs} {lsize : Lsize}
    (hpa : cellsOf asm = some prog) (hd : dataSections asm.text = some secs) (hwf : Λ.WF)
    (hpz : 8 ≤ Λ.pinned.size) (hw : wideIn (prog.map (·.1)) = true)
    (hst : I (L0T Λ) (ls0T lsize) (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata))
      ⟨helloTh0.term, helloTh0.env, none⟩ helloTh0.stack)
    (hH0 : H (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) [])
    (hown0 : ∀ t0 : T.M.Cfg, loadParsed (kernel 1) E Λ prog secs asm.labelOffs = some t0 →
      OwnInit (own (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) helloTh0.stack) t0.1.mem ∧
      MemInv G t0.1.mem ∧ (∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a → t0.1.mem.initVal (wordLoc a) = 0) ∧
      t0.1.mem.initVal (wordLoc ar.ctr) = 0)
    (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0) :
    ∀ d : Cfg, (target (kernel 1) E).load asm Λ = some d →
      ∃ s0, (srcS helloSrc arch).init s0 ∧ RSAH Λ (srcPo 2 arch helloSrc) helloSrc G own I H μ ar d s0 := by
  intro d h
  have hl : loadParsed (kernel 1) E Λ prog secs asm.labelOffs = some d :=
    (load_of_parsed (kernel 1) E Λ hpa hd).symm.trans h
  obtain ⟨ho, hg, hz0, hc0⟩ := hown0 d hl
  exact init_of_loadAHT (P := srcPo 2 arch helloSrc) (th₀ := helloTh0) hwf hpz hw
    (show progInitT helloSrc 2 (setupStartT 2) by rw [hello_start]) rfl rfl rfl rfl hbox0H hst (freshH hstat) hH0
    ho hg hstat hsub hal hz0 hc0 hl

end Load

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **`OPremH.hinit` at the root's choices at any owned words `own`** (see the module doc): the start in `I` at
`L0T`/`ls0T` (`hst`) and `own` initially owned at the load (`hown0`, `X64HelloOInit.hown0_H`'s shape) make the load
related at `gWH … cTW`, `own`, `arW`, `HeldOk2 … r0W r1W`. -/
theorem hinit_Hg {own : Spike.Lib.X64Consumer.Own} (hpa : cellsOf asm = some o.prog)
    (hd : dataSections asm.text = some o.secs)
    (hoffs : asm.labelOffs = o.labelOffs)
    /- instance facts -/
    (hstat : Λ0.static = fun _ => none)
    (hsub1 : (Spike.Lib.X64WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (arch : WeakMem.Arch) {E : Entry} (hE : E.clear (Ly).Λ = true) (μ : Marks)
    (I : InvS) (ls : Lsize)
    /- `own` initially owned at the load (at `ownGH`: `X64HelloOInit.hown0_H`) -/
    (hown0 : ∀ t0, Scc.Sem.X64.loadParsed (Scc.Sem.X64.kernel 1) E (Ly).Λ o.prog o.secs o.labelOffs = some t0 →
      Spike.Lib.Consumer1.OwnInit
        (own (Scc.Sem.X64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata))) t0.1.mem)
    /- the start in `I` (at the root `RootH0.hstH`) -/
    (hst : I (L0T (Ly).Λ) (ls0T ls) (threadAt E (Ly).Λ.code.lo o.prog (loadSyms (Ly).Λ o.secs.rodata))
      ⟨helloTh0.term, helloTh0.env, none⟩ helloTh0.stack) :
    ∀ d : Cfg, (target (kernel 1) E).load asm (Ly).Λ = some d →
      ∃ s0, (srcS helloSrc arch).init s0 ∧
        RSAH (Ly).Λ (srcPo 2 arch helloSrc) helloSrc (Spike.Lib.X64HelloGOf2H.gWH hp i (Spike.Lib.X64WakeHG.cTW hp i))
          (fun s _ => own s) I
          (HeldOk2 (Ly).Λ (Spike.Lib.X64WakeOSide.r0W hp i) (Spike.Lib.X64WakeOSide.r1W hp i)) μ
          (Spike.Lib.X64.WakeOD.arW hp i) d s0 := by
  have hpz : 8 ≤ (Ly).Λ.pinned.size := by
    have := PlaceWX.pinA_toNat_ofPlaceWX hp i; omega
  refine hello_initT (lsize := ls) hpa hd (Spike.Lib.X64WakeOSide.hwf_W hp i) hpz
    (PlaceWX.wideIn_of_placeWX hp) hst
    (Spike.Lib.X64WakeOHinit.hH0_W hp i hE hsub1) (fun t0 hl => ⟨hown0 t0 (hoffs ▸ hl), ?_, ?_, ?_⟩) hstat
    (Spike.Lib.X64.Rt.ArenaW.arOf_sub (PlaceWX.link i hp)) (Spike.Lib.X64.Rt.ArenaW.arOf_al (PlaceWX.link i hp))
  all_goals
    rw [hoffs] at hl
    have he : Scc.Sem.X64.loadParsed (Scc.Sem.X64.kernel 1) E (Ly).Λ o.prog o.secs o.labelOffs = _ :=
      Scc.Cert.Link.X64.loadParsed_of_loadOk (H := Scc.Sem.X64.kernel 1) (PlaceWX.loadOk_link_of_placeWX i hp) hE
    rw [he] at hl
    cases hl
  · exact Spike.Lib.WakeG.memInv_wakeG (Scc.Sem.memInv_fixG_load rfl rfl)
  · exact fun a ha => Spike.Lib.X64.Rt.ArenaW.arOf_z0 (PlaceWX.link i hp) hc rfl ha
  · exact Spike.Lib.X64.Rt.ArenaW.arOf_c0 (PlaceWX.link i hp) hc rfl


/-- **`OPremH.hinit` at the root's choices** (see the module doc): `hinit_Hg` at `ownGH … ntA`, `hown0` by
`X64HelloOInit.hown0_H`. -/
theorem hinit_H (hpa : cellsOf asm = some o.prog)
    (hhp : cellsOf asm = some SccCode.helloCells) (hd : dataSections asm.text = some o.secs)
    (hoffs : asm.labelOffs = o.labelOffs)
    /- instance facts -/
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hsub1 : (Spike.Lib.X64WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hnz : Spike.Lib.X64WakeOInit.NtZ Λ0 o = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (arch : WeakMem.Arch) {E : Entry} (hE : E.clear (Ly).Λ = true) (μ : Marks)
    (I : InvS) (ls : Lsize)
    /- the start in `I` (at the root `RootH0.hstH`) -/
    (hst : I (L0T (Ly).Λ) (ls0T ls) (threadAt E (Ly).Λ.code.lo o.prog (loadSyms (Ly).Λ o.secs.rodata))
      ⟨helloTh0.term, helloTh0.env, none⟩ helloTh0.stack) :
    ∀ d : Cfg, (target (kernel 1) E).load asm (Ly).Λ = some d →
      ∃ s0, (srcS helloSrc arch).init s0 ∧
        RSAH (Ly).Λ (srcPo 2 arch helloSrc) helloSrc (Spike.Lib.X64HelloGOf2H.gWH hp i (Spike.Lib.X64WakeHG.cTW hp i))
          (fun s _ => Spike.Lib.X64.HelloPh.ownGH (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s) I
          (HeldOk2 (Ly).Λ (Spike.Lib.X64WakeOSide.r0W hp i) (Spike.Lib.X64WakeOSide.r1W hp i)) μ
          (Spike.Lib.X64.WakeOD.arW hp i) d s0 :=
  hinit_Hg hp i hpa hd hoffs hstat hsub1 hc hpin2 arch hE μ I ls
    (Spike.Lib.X64HelloOInit.hown0_H hp i hpa hhp hlo (Spike.Lib.X64WakeOInit.hnt_of hp i hnz) E) hst

end Place

end Spike.Lib.X64HelloOHinit

/-- info: 'Spike.Lib.X64HelloOHinit.freshH' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOHinit.freshH


/-- info: 'Spike.Lib.X64HelloOHinit.hello_initT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOHinit.hello_initT

/-- info: 'Spike.Lib.X64HelloOHinit.hinit_Hg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOHinit.hinit_Hg

/-- info: 'Spike.Lib.X64HelloOHinit.hinit_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOHinit.hinit_H
