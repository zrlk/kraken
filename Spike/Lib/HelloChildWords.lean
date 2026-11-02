/-
**hello.w's child words at the clone** (ChildPrem rows
`hv`, `htag`, `hvu` of `Hello.SegR.ChildPrem`): at main's
`clone` (`HelloSpawnR.PreRH`), the worker's pointer word (`D.cw w`, a
locative to `cS w = ⟨l, 0⟩`) is represented by main's `x13` (`ClonePreH`'s
`cA`), and main's id `mainTidW` by its `x14` (`meW`), at the spawn's label
placement `lbl` (the record's, `lbl_clone`).

- `lbl_clone`: the record's placement is the clone's `lbl`.
- `words_clone`: `hv`, `htag`, `hvu` at the clone's thread's `x13`, `x14`.
- `sl_clone`: main's `x11`, `x12` at the clone are the slice's `2`, `13`
  (`SlRep`); `hx1_clone`: at `wc_worker`'s body on the
  clone's words, `print`'s count `x1` is `printN 13 2`.
-/
import Spike.Lib.HelloSpawnR
import Spike.Lib.A64HelloWorkerSegP

namespace Spike.Lib.HelloSpawnR

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.HelloQ (helloQ)
open Spike.Lib.WakeW1 (mainTidW)

section Inst

variable {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isaLSE2}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : WakeM0.MSide ι} {D : WSideH ι} {r0 r1 : ι → Range}
  {Λ : Scc.Sem.Layout} {w : ι} {d : Cfg} {th : Thread isaLSE2} {stack : Nat} {s s' : TermRun.Cfg}
  {s0 s1 : TermRun.TTh} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ts : Nat → Option Nat} {j : Nat} {own₀ : List (Loc × Val)} {l : WeakMem.AllocLabel}

/-- **The record's placement is the clone's.** -/
theorem lbl_clone
    (hR : PreRH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l) :
    (SR w).lbl = lbl :=
  congrArg SpawnRec.lbl hR.pre.SR

/-- **The child's words at the clone** (`ChildPrem`'s `hv`, `htag`, `hvu`;
see the module doc). -/
theorem words_clone
    (hR : PreRH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l)
    (hcw : (D.cw w).val = .loc (cS w) 0) :
    ValRep lbl (D.cw w).val th.st.st.1.regs.X13.toBitVec.toNat ∧ (∃ sa, (D.cw w).val = .loc sa 0) ∧
      ∀ w4 : TermRun.Word, w4.val = mainTidW → ValRep lbl w4.val th.st.st.1.regs.X14.toBitVec.toNat := by
  obtain ⟨th0', ws', hs', hc', -⟩ := hR.hsp
  obtain ⟨X, th', th0, hd, tls, cA, meW, sl0, sl1, sl2, sl3, l', ws, hth', hs, -, -, -, -, -, -, -, -, -, -,
    h13, h14, -, -, -, -, -, -, -, -, -, ⟨-, -, hcl, -⟩, -, -, hvc, hvm, -⟩ := hR.clone
  have hth : th = th' := by
    rw [hR.pre.threads] at hth'
    exact List.singleton_inj.mp (congrArg Array.toList hth')
  have h00 : th0' = th0 := by
    rw [hs'] at hs
    exact List.singleton_inj.mp (congrArg Array.toList hs)
  subst hth h00
  have hl : l' = l := by
    have := hc'.symm.trans hcl
    simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at this
    cases this.2
    rfl
  subst hl
  refine ⟨?_, ⟨_, hcw⟩, fun w4 h4 => ?_⟩
  · rw [hcw, hR.hcS]
    exact (show th.st.st.1.regs.X13.toBitVec.toNat = cA from h13) ▸ hvc
  · rw [h4]
    exact (show th.st.st.1.regs.X14.toBitVec.toNat = meW from h14) ▸ hvm

end Inst

end Spike.Lib.HelloSpawnR

namespace Spike.Lib.HelloPreA

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Spike.Lib.WakeA64
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words)
open Spike.Lib.A64.Flow.Worker.Hello.Wk (wkJ)

variable {pfx : String} {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop}
  {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg}

/-- **main's `x11`, `x12` at the clone are the slice's `2`, `13`** (`SlRep`). -/
theorem sl_clone (h : ClonePreH pfx Λ r0 r1 X lbl t s) {th : Thread isaLSE2} (hth : t.1.threads = #[th]) :
    th.st.st.1.regs.X11.toBitVec.toNat = 2 ∧ th.st.st.1.regs.X12.toBitVec.toNat = 13 := by
  obtain ⟨th', _, _, _, _, _, _, _, sl2, sl3, _, _, hth', -, -, -, -, -, -, -, -, -, h11, h12,
    -, -, -, -, -, -, -, -, -, -, -, -, -, hsl, -, -, -⟩ := h
  obtain rfl : th = th' := by
    rw [hth] at hth'
    exact List.singleton_inj.mp (congrArg Array.toList hth')
  obtain ⟨-, -, -, -, rfl, rfl⟩ := hsl
  exact ⟨h11, h12⟩

/-- **`ChildPrem.hx1` at the clone's words**: at
`wc_worker`'s body (`wkJ`) on main's `x9 .. x14`, `print`'s count is
`printN 13 2` (`Body.wkC_x1`: `min (x12, 8 · x11)`). -/
theorem hx1_clone (h : ClonePreH pfx Λ r0 r1 X lbl t s) {th : Thread isaLSE2} (hth : t.1.threads = #[th])
    (lab : Label → Int64) (c0 : Ctl) (tp : BitVec 64) :
    ∀ x29 ra σ, wkJ c0 ⟨th.st.st.1.regs.X9.toBitVec, th.st.st.1.regs.X10.toBitVec, th.st.st.1.regs.X11.toBitVec,
        th.st.st.1.regs.X12.toBitVec, th.st.st.1.regs.X13.toBitVec, th.st.st.1.regs.X14.toBitVec⟩ x29 ra tp σ c0 →
      (Spike.Lib.A64.Flow.Worker.Body.wkC lab σ).regs.X1.toBitVec.toNat = Spike.Lib.PrintSrc.printN 13 2 := by
  intro x29 ra σ hJ
  obtain ⟨-, -, -, h80, h72, -⟩ := hJ
  obtain ⟨h11, h12⟩ := sl_clone h hth
  rw [Spike.Lib.A64.Flow.Worker.Body.wkC_x1, h80, h72, h12, BitVec.toNat_mul, h11]
  decide

end Spike.Lib.HelloPreA

/-- info: 'Spike.Lib.HelloSpawnR.words_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloSpawnR.words_clone

/-- info: 'Spike.Lib.HelloPreA.hx1_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPreA.hx1_clone
