import Kraken.AArch64.Examples.EnvLSE2
import Kraken.Promising.Lower.Lowerable16

/-!
# The lowering's 16-byte pair forms, one thread, on the Promising machine

`pairRelAcq` is the AArch64 lowering of a WeakCore release pair store followed
by an acquire pair load of one 16-byte location: `dmb ish; stp` (release:
Kraken has no `STILP`) and `ldp; dmb ishld` (acquire: no `LDIAPP`). It is
lowerable with 16-byte units (`pairRelAcq_wcLowerable16`) but not under
`Program.WCLowerable` (`pairRelAcq_not_wcLowerable`), whose clause 1 rejects
every 64-bit pair.

`pairRelAcq_correctEnv` proves it in the FEAT_LSE2 environment logic (one
`vcgen` call: the barriers by `dmb_shared`, the pairs as one 16-byte access
each), and `pairRelAcq_promising` carries it through `env_link_halt_lse2` to
the `isaLSE2` runs whose thread declares the location: the registers receive
the halves stored, and the location's last write holds both halves. This is
the one-thread route; the multi-thread lowering kit for 16-byte units is
not built (`Kraken/Promising/Lower/README.md`).
-/

open Std.WP
open Kraken
open Kraken.Promising
open Kraken.Promising.AArch64
open MachineWP

namespace MachineWP

set_option mvcgen.warning false
set_option experimental.vcgen true

open Kraken.AArch64.Parser

/-- The release pair store then the acquire pair load, as lowered. -/
def pairRelAcq : Program := parseAArch64("
    dmb ish
    stp x1, x2, [x0]
    ldp x3, x4, [x0]
    dmb ishld
")

theorem pairRelAcq_wcLowerable16 : pairRelAcq.WCLowerable16 := by decide

theorem pairRelAcq_not_wcLowerable : ¬ pairRelAcq.WCLowerable := by decide

section pairRelAcq

variable [layout : _root_.Layout]

local instance pairRelAcq.env : CodeEnv := ⟨layout pairRelAcq⟩

local instance (a : BitVec 64) : (SharedEnv.lastWrite (pairL a)).LSE2Disc (pairL a) :=
  SharedEnv.lastWrite_lse2Disc (by simp)

theorem pairRelAcq_correctEnv (a v₁ v₂ : BitVec 64) :
    TripleEnvLSE2 (pairL a) (SharedEnv.lastWrite (pairL a))
      (fun s _ => s.regs.X0.toBitVec = a ∧ a % 16 = 0 ∧ s.regs.X1.toBitVec = v₁ ∧ s.regs.X2.toBitVec = v₂ ∧
        Mem.loadInt s.dmem a 8 = none ∧ Mem.loadInt s.dmem (a + 8) 8 = none)
      pairRelAcq
      (fun s g => s.regs.X3.toBitVec = v₁ ∧ s.regs.X4.toBitVec = v₂ ∧
        (g a).setWidth 64 = v₁ ∧ ((g a) >>> 64).setWidth 64 = v₂)
      (fun _ _ _ => False) := by
  apply TripleEnvLSE2.of_triple
  unfold pairRelAcq
  vcgen
  all_goals simp_all [SharedEnv.lastWrite, SharedEnv.upd]

variable [Executable.ValidLayout (layout pairRelAcq)]

/-- **The lowered pair forms on the Promising machine, under FEAT_LSE2.** A
promise-free one-thread `isaLSE2` run from `d`, the thread declaring the
16-byte location at `[x0]` (`declsOf (pairL a)`), `a` 16-byte aligned and
neither half in `dmem`: at the end of the text `x3:x4` is `x1:x2`, and the
location's last write holds `x1` in its low and `x2` in its high half. -/
theorem pairRelAcq_promising (A : Arch) (fuel : Nat) (showPc : Int64 → String) (d : MachineData)
    (mem : Memory) (hm : mem.msgs = #[]) (halign : d.regs.X0.toBitVec % 16 = 0)
    (hfree₁ : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = none)
    (hfree₂ : Mem.loadInt d.dmem (d.regs.X0.toBitVec + 8) 8 = none)
    (c : Config isaLSE2)
    (hc : ReachablePF A fuel ⟨#[Thread.init ({
      exe := layout pairRelAcq
      endPc := (layout pairRelAcq).addrOf pairRelAcq.length
      st := (d, Kraken.Layout.start Directive)
      showPc
      decls := declsOf (pairL d.regs.X0.toBitVec) } : State)], mem⟩ c)
    (t' : Thread isaLSE2) (ht : c.threads = #[t'])
    (hend : t'.st.st.2 = (layout pairRelAcq).addrOf pairRelAcq.length) :
    t'.st.st.1.regs.X3.toBitVec = d.regs.X1.toBitVec ∧ t'.st.st.1.regs.X4.toBitVec = d.regs.X2.toBitVec ∧
      (c.mem.finalVal (sharedLoc d.regs.X0.toBitVec 16)).setWidth 64 = d.regs.X1.toBitVec ∧
      ((c.mem.finalVal (sharedLoc d.regs.X0.toBitVec 16)) >>> 64).setWidth 64 = d.regs.X2.toBitVec := by
  have henv : envRel (pairL d.regs.X0.toBitVec) (fun _ => mem.finalVal (sharedLoc d.regs.X0.toBitVec 16))
      mem := by
    intro b m hb
    simp only [pairL, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hb
    obtain ⟨rfl, rfl⟩ := hb
    rfl
  have hev := Program.instrStepEnvLSE2_of_tripleEnvLSE2
    (pairRelAcq_correctEnv d.regs.X0.toBitVec d.regs.X1.toBitVec d.regs.X2.toBitVec) (s := d)
    (g := fun _ => mem.finalVal (sharedLoc d.regs.X0.toBitVec 16))
    ⟨rfl, halign, rfl, rfl, hfree₁, hfree₂⟩
  obtain ⟨g', hrel', hP⟩ := env_link_halt_lse2 _ (layout pairRelAcq) (pairL_wf _) A fuel _ showPc d _ mem _ _
    hm henv (fun x hx => hx.elim And.left False.elim) (not_instrStepEnvLSE2_of_end _ _) hev c hc t' ht hend
  obtain ⟨-, hx3, hx4, hlo, hhi⟩ := hP.resolve_right id
  have h : c.mem.finalVal (sharedLoc d.regs.X0.toBitVec 16) = g' d.regs.X0.toBitVec := by
    simpa using (hrel' d.regs.X0.toBitVec 16 (by simp)).symm
  exact ⟨hx3, hx4, by rw [h]; exact hlo, by rw [h]; exact hhi⟩

end pairRelAcq

end MachineWP
