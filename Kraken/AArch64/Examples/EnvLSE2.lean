import Kraken.AArch64.EnvLSE2
import Kraken.AArch64.Parser
import Kraken.Promising.EnvLSE2AArch64

/-!
# A 16-byte publish under FEAT_LSE2, carried to the Promising machine

`publish16` stores `x1:x2` to the 16-byte location at `[x0]` (`stp`) and
loads it back into `x3:x4` (`ldp`). With the location declared 16 bytes wide
(`pairL a = [(a, 16)]`) and `a` 16-byte aligned, the FEAT_LSE2 environment
logic (`Kraken/AArch64/EnvLSE2.lean`) reads each as one 16-byte access
(`stp_lse2_shared_spec`, `ldp_lse2_shared_spec`): `publish16_correctEnv`, one
`vcgen` call. `publish16_promising` carries it through `env_link_halt_lse2` to
`isaLSE2` runs whose thread declares `pairL a` (`declsOf`): the registers
receive the halves stored, and the location's last write holds both halves.
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

/-- The 16-byte location. -/
abbrev pairL (a : BitVec 64) : SharedEnv.Layout := [(a, 16)]

def publish16 : Program := parseAArch64("
    stp x1, x2, [x0]
    ldp x3, x4, [x0]
")

section publish16

variable [layout : _root_.Layout]

local instance publish16.env : CodeEnv := ⟨layout publish16⟩

local instance (a : BitVec 64) : (SharedEnv.lastWrite (pairL a)).LSE2Disc (pairL a) :=
  SharedEnv.lastWrite_lse2Disc (by simp)

theorem publish16_correctEnv (a v₁ v₂ : BitVec 64) :
    TripleEnvLSE2 (pairL a) (SharedEnv.lastWrite (pairL a))
      (fun s _ => s.regs.X0.toBitVec = a ∧ a % 16 = 0 ∧ s.regs.X1.toBitVec = v₁ ∧ s.regs.X2.toBitVec = v₂ ∧
        Mem.loadInt s.dmem a 8 = none ∧ Mem.loadInt s.dmem (a + 8) 8 = none)
      publish16
      (fun s g => s.regs.X3.toBitVec = v₁ ∧ s.regs.X4.toBitVec = v₂ ∧
        (g a).setWidth 64 = v₁ ∧ ((g a) >>> 64).setWidth 64 = v₂)
      (fun _ _ _ => False) := by
  apply TripleEnvLSE2.of_triple
  unfold publish16
  vcgen
  all_goals simp_all [SharedEnv.lastWrite, SharedEnv.upd]

omit layout in
/-- The one-location layout is well formed. -/
theorem pairL_wf (a : BitVec 64) : SharedLayout.WF (pairL a) where
  pos _ _ h := by
    simp only [pairL, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨-, rfl⟩; decide
  le16 _ _ h := by
    simp only [pairL, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨-, rfl⟩; decide
  disj _ _ _ _ k ha hb h1 h2 := by
    simp only [pairL, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at ha hb
    rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

variable [Executable.ValidLayout (layout publish16)]

/-- **`publish16` on the Promising machine, under FEAT_LSE2.** A promise-free
one-thread `isaLSE2` run from `d`, the thread declaring the 16-byte location
at `[x0]` (`declsOf (pairL a)`), `a` 16-byte aligned and neither half in
`dmem`: when the thread has reached the end of the text, `x3:x4` is `x1:x2`
and the location's last write holds `x1` in its low and `x2` in its high
half. `publish16_correctEnv` through `env_link_halt_lse2`. -/
theorem publish16_promising (A : Arch) (fuel : Nat) (showPc : Int64 → String) (d : MachineData)
    (mem : Memory) (hm : mem.msgs = #[]) (halign : d.regs.X0.toBitVec % 16 = 0)
    (hfree₁ : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = none)
    (hfree₂ : Mem.loadInt d.dmem (d.regs.X0.toBitVec + 8) 8 = none)
    (c : Config isaLSE2)
    (hc : ReachablePF A fuel ⟨#[Thread.init ({
      exe := layout publish16
      endPc := (layout publish16).addrOf publish16.length
      st := (d, Kraken.Layout.start Directive)
      showPc
      decls := declsOf (pairL d.regs.X0.toBitVec) } : State)], mem⟩ c)
    (t' : Thread isaLSE2) (ht : c.threads = #[t'])
    (hend : t'.st.st.2 = (layout publish16).addrOf publish16.length) :
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
    (publish16_correctEnv d.regs.X0.toBitVec d.regs.X1.toBitVec d.regs.X2.toBitVec) (s := d)
    (g := fun _ => mem.finalVal (sharedLoc d.regs.X0.toBitVec 16))
    ⟨rfl, halign, rfl, rfl, hfree₁, hfree₂⟩
  obtain ⟨g', hrel', hP⟩ := env_link_halt_lse2 _ (layout publish16) (pairL_wf _) A fuel _ showPc d _ mem _ _
    hm henv (fun x hx => hx.elim And.left False.elim) (not_instrStepEnvLSE2_of_end _ _) hev c hc t' ht hend
  obtain ⟨-, hx3, hx4, hlo, hhi⟩ := hP.resolve_right id
  have h : c.mem.finalVal (sharedLoc d.regs.X0.toBitVec 16) = g' d.regs.X0.toBitVec := by
    simpa using (hrel' d.regs.X0.toBitVec 16 (by simp)).symm
  exact ⟨hx3, hx4, by rw [h]; exact hlo, by rw [h]; exact hhi⟩

end publish16

end MachineWP
