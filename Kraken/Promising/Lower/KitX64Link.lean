/-
**The register-link call-site rule of the x64 register-link pilot, as general
x64 kit helpers.** ISA: x64
(`Kraken.X64.EnvCallsPartial`); statements about `Safely` runs of laid-out
code in a shared environment, no machine.

The x64 register-link pilot proved the call-site rule of its stackless register-link convention
in section `LinkCall` of `Lower/PilotXRMain.lean` (global names
`MachineWP.FunSpecPartialEnv.jcall`, `Safely.blockAt`, left where they are).
They are restated here, with the same statements, under **new names** (so a
file importing both sees no clash; dot notation `hf.jcallLink` and
`Safely.blockAtLabel` still works):

- **`MachineWP.FunSpecPartialEnv.jcallLink`**: the jump `jmp f` to a callee
  with a `FunSpecPartialEnv` at its entry, with the link register holding the
  return address `ra` in `Pre`, continues at `ra` from every `Post` state.
- **`Safely.blockAtLabel`**: a block of a placed text (`Program.PlacedIn`),
  run from its label's address by a `MachineWP` triple of its body (no shared
  access, lifted through the fence order of a `SharedEnv.FenceMonoX`
  environment), its exits continuing at every environment state above the
  start.

Use, for a call site `leaq ret_k(%rip), %r11; jmp f; ret_k:`: `blockAtLabel`
on the block ending in `jmp f` (it exits at `f`'s label with `r11` the
address of `ret_k`), `jcallLink` at `ra := label ret_k`, then `blockAtLabel`
on the block at `ret_k`. Unlike `MachineWP.PartialWpEnv.call` there is no
stack side condition (no slot, no `dmem`). The return lands at a *label*, so
the composition is over blocks at their labels (`Program.PlacedIn`), not over
fragments placed anywhere (`PartialWpEnv`).
-/
import Kraken.Promising.Lower.KitX64Wp

open Std.WP Kraken MachineWP

namespace Kraken.Promising.Lower.KitX

/-- Sequencing of `Safely` (a local copy: the x64 one in
`X64/EnvCallsPartial.lean` and the x64 register-link pilot's `safely_bindXR` are private). -/
private theorem safely_bindLink {State : Type} {trans : State → (State → Prop) → Prop}
    {P Q : State → Prop} {x : State} (h : Safely trans P x) (hk : ∀ y, P y → Safely trans Q y) :
    Safely trans Q x := by
  obtain ⟨Inv, hx, hInv⟩ := h
  refine ⟨fun z => Inv z ∨ Safely trans Q z, .inl hx, ?_⟩
  rintro z (hz | hz)
  · rcases hInv z hz with hp | ⟨R, hT, hR⟩
    · rcases (hk z hp).unfold with hq | ⟨R, hT, hR⟩
      · exact .inl hq
      · exact .inr ⟨R, hT, fun w hw => .inr (hR w hw)⟩
    · exact .inr ⟨R, hT, fun w hw => .inl (hR w hw)⟩
  · rcases hz.unfold with hq | ⟨R, hT, hR⟩
    · exact .inl hq
    · exact .inr ⟨R, hT, fun w hw => .inr (hR w hw)⟩

end Kraken.Promising.Lower.KitX

open Kraken.Promising.Lower.KitX (safely_bindLink)

section LinkCallX

variable [CodeEnv] {env : SharedEnv}

/-- **A jump to a link-register callee** (the x64 register-link pilot's
`FunSpecPartialEnv.jcall`): from the callee's entry with `Pre` at the return
address `ra` (the link register's value, in `Pre`), the run continues at
`ra` from every `Post` state. -/
theorem MachineWP.FunSpecPartialEnv.jcallLink {entry ra : Int64}
    {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (hf : FunSpecPartialEnv env entry Pre Post) {t : MachineData} {g : env.State} (hpre : Pre ra t g)
    {Q : MachineState × env.State → Prop}
    (hk : ∀ s' g', Post ra t g s' g' → Safely (cenv.instrStepEnv env) Q ((s', ra), g')) :
    Safely (cenv.instrStepEnv env) Q ((t, entry), g) :=
  safely_bindLink (hf ra t g hpre) fun ⟨⟨s', a⟩, g'⟩ ⟨ha, hp⟩ => by
    dsimp only at ha hp
    subst ha
    exact hk s' g' hp

/-- **A block at its label** (the x64 register-link pilot's `Safely.blockAt`): the block `blk`
of the placed text `p` at `l`, by a `MachineWP` triple of its body from the
exact state `s` that never falls through (it ends in a jump), its exits `X`
continuing at every environment state above `g` in the fence order. -/
theorem Safely.blockAtLabel [env.FenceMonoX] {p : Program} {l : Label} {blk : Program.Block}
    (hpl : Program.PlacedIn p) (hb : Program.blockAt p l = some blk) {s : MachineData} {g : env.State}
    {X : Int64 → MachineData → Prop} {Q : MachineState × env.State → Prop}
    (h : ⦃ fun s' => s' = s ⦄ blk.body ⦃ fun _ _ => False; X ⦄)
    (hk : ∀ a s' g', X a s' → SharedEnv.FenceMonoX.le g g' →
      Safely (cenv.instrStepEnv env) Q ((s', a), g')) :
    Safely (cenv.instrStepEnv env) Q ((s, (_root_.Executable.labels cenv).label l), g) := by
  have hI : env.FenceInv (SharedEnv.FenceMonoX.le g) := fun k g' h =>
    SharedEnv.FenceMonoX.fenceInv g k g' h
  have hw : cenv.wp blk.body (fun _ => False) X s := h.le_wp s rfl
  refine Safely.of_eventually_safely
    (Executable.wpEnv_of_wp hI hw g (SharedEnv.FenceMonoX.refl g) _ (hpl.block l blk hb)) ?_
  rintro ⟨⟨s', a⟩, g'⟩ (⟨-, hF, -⟩ | ⟨hx, hle⟩)
  · exact hF.elim
  · exact hk a s' g' hx hle

end LinkCallX

#print axioms MachineWP.FunSpecPartialEnv.jcallLink
#print axioms Safely.blockAtLabel
