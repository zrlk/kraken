/-
**hello.w's child words at the clone** (x86-64; the twin of `Spike/Lib/HelloChildWords.lean`, same names): at main's
`clone` (`X64HelloSpawnR.PreRH`), the worker's pointer word (`D.cw w`, a locative to `cS w = ⟨l, 0⟩`) is represented
by main's `%r15` (`ClonePreH`'s `cA`), and main's id `mainTidW` by its `%r9` (`meW`), at the spawn's label placement
`lbl` (the record's, `lbl_clone`). These are `Hello.SegR.ChildPrem`'s `hv`, `htag`, `hvu`.

- `lbl_clone`: the record's placement is the clone's `lbl`.
- `words_clone`: `hv`, `htag`, `hvu` at the clone's thread's `%r15`, `%r9`.
- `sl_clone`: main's `%r13`, `%r14` at the clone are the slice's `2`, `13` (`SlRep`).

**Unlike AArch64**, the worker's words are `%r12, %rbx, %r13, %r14, %r15, %r9` (AArch64: `x9 .. x14`), so the cell is
`%r15` (`x13`), main's id `%r9` (`x14`) and the slice's counts `%r13`, `%r14` (`x11`, `x12`); the facts are read
through `ClonePreH.src` (AArch64 destructures `ClonePreH` by position), and `ClonePreH` has no label prefix.

Not twinned (unreachable from the AArch64 root `hello_linkedA`, so twins only live constants): `hx1_clone` (and so
the import of `A64HelloWorkerSegP`, which only it reads).
-/
import Spike.Lib.X64HelloSpawnR

namespace Spike.Lib.X64HelloSpawnR

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64WakeW1 (mainTidW)

section Inst

variable {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isa}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : X64WakeM0.MSide ι} {D : WSideH ι} {r0 r1 : ι → Range}
  {Λ : Scc.Sem.Layout} {w : ι} {d : Cfg} {th : Thread isa} {stack : Nat} {s s' : TermRun.Cfg}
  {s0 s1 : TermRun.TTh} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ts : Nat → Option Nat} {j : Nat} {own₀ : List (Loc × Val)} {l : WeakMem.AllocLabel}

/-- **The record's placement is the clone's.** -/
theorem lbl_clone
    (hR : PreRH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l) :
    (SR w).lbl = lbl :=
  congrArg SpawnRec.lbl hR.pre.SR

/-- **The child's words at the clone** (`ChildPrem`'s `hv`, `htag`, `hvu`; see the module doc). -/
theorem words_clone
    (hR : PreRH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l)
    (hcw : (D.cw w).val = .loc (cS w) 0) :
    ValRep lbl (D.cw w).val (th.st.st.1.regs.get64 .r15).toNat ∧ (∃ sa, (D.cw w).val = .loc sa 0) ∧
      ∀ w4 : TermRun.Word, w4.val = mainTidW → ValRep lbl w4.val (th.st.st.1.regs.get64 .r9).toNat := by
  obtain ⟨th0', ws', hs', hc', -⟩ := hR.hsp
  obtain ⟨X, hX⟩ := hR.clone
  obtain ⟨th', th0, hd, l', ws, hth', hs, ⟨-, -, hcl, -⟩, -, -, hvc, hvm⟩ := hX.src
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
    exact hvc
  · rw [h4]
    exact hvm

end Inst

end Spike.Lib.X64HelloSpawnR

namespace Spike.Lib.X64HelloPreA

open Kraken.Promising Kraken.Promising.X64 Scc.Sem Spike.Lib.X64WakeA64

variable {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop}
  {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg}

/-- **main's `%r13`, `%r14` at the clone are the slice's `2`, `13`** (`SlRep`). -/
theorem sl_clone (h : ClonePreH Λ r0 r1 X lbl t s) {th : Thread isa} (hth : t.1.threads = #[th]) :
    (th.st.st.1.regs.get64 .r13).toNat = 2 ∧ (th.st.st.1.regs.get64 .r14).toNat = 13 := by
  obtain ⟨th', _, _, _, _, hth', -, -, -, hsl, -, -⟩ := h.src
  obtain rfl : th = th' := by
    rw [hth] at hth'
    exact List.singleton_inj.mp (congrArg Array.toList hth')
  obtain ⟨-, -, -, -, h2, h3⟩ := hsl
  exact ⟨h2, h3⟩

end Spike.Lib.X64HelloPreA

/-- info: 'Spike.Lib.X64HelloSpawnR.lbl_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSpawnR.lbl_clone

/-- info: 'Spike.Lib.X64HelloSpawnR.words_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSpawnR.words_clone

/-- info: 'Spike.Lib.X64HelloPreA.sl_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPreA.sl_clone
