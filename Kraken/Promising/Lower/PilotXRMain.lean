/-
**Part 3: `main` from the two function
specifications under the register-link convention, x64.**

**The call-site rule for the convention** (section `LinkCall`, generic: a
hoist candidate, the register-link analogue of `PartialWpEnv.call`):

- `Safely.blockAt`: a block of a placed text (`Program.PlacedIn`), run from
  its label's address by a `MachineWP` triple of its body (no shared access,
  lifted through the fence order of a `FenceMonoX` environment), its exits
  continuing at every environment state above the start. `Safely.blockAtT`:
  the same for an environment permitting every fence (`FenceInv` of `True`).
- `FunSpecPartialEnv.jcall`: the jump `jmp f` to a callee with a
  `FunSpecPartialEnv` at its entry, the link register holding the return
  label's address `ra` in `Pre`, continues at `ra` from every `Post` state.

A call site `leaq ret_k(%rip), %r11; jmp f; ret_k:` is then `blockAt` (the
block ending in `jmp f` exits at `f`'s label with `r11` the address of
`ret_k`), `jcall` at `ra := label ret_k`, and `blockAt` of the block at
`ret_k`. Unlike `PartialWpEnv.call` there is no stack side condition (no
slot, no `dmem`), and the return lands at a *label*, so the composition is
over blocks at their labels (`Program.PlacedIn`), not over fragments placed
anywhere (`PartialWpEnv`).

`main` (`Lower/PilotXRProg.lean`) is three blocks: `main` (link into `rbp`,
the node from the bump allocator, `ja oom` not taken, `rdi := &top`,
`r11 := ret_push`, `jmp push`), `ret_push` (`rdi := &top`, `r11 := ret_pop`,
`jmp pop`), `ret_pop` (`r12 := rax`, `jmp *%rbp`). Proved by `blockAt` on
each block (one `vcgen` each) and `jcall` at `push_specXR`/`pop_specXR`.
-/
import Kraken.Promising.Lower.PilotXRSpecs
import Kraken.Promising.Lower.KitX64Wp

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG

/-! ## Link-register calls (generic) -/

section LinkCall

/-- Sequencing of `Safely` (the first lowering pilot's `Safely.bind`, local copy: the x64 one
in `X64/EnvCallsPartial.lean` is private). -/
private theorem safely_bindXR {State : Type} {trans : State → (State → Prop) → Prop} {P Q : State → Prop}
    {x : State} (h : Safely trans P x) (hk : ∀ y, P y → Safely trans Q y) : Safely trans Q x := by
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

variable [CodeEnv] {env : SharedEnv}


/-- **A jump to a link-register callee**: from the callee's entry with `Pre`
at the return address `ra` (the link register's value, in `Pre`), the run
continues at `ra` from every `Post` state. -/
theorem MachineWP.FunSpecPartialEnv.jcall {entry ra : Int64} {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (hf : FunSpecPartialEnv env entry Pre Post) {t : MachineData} {g : env.State} (hpre : Pre ra t g)
    {Q : MachineState × env.State → Prop}
    (hk : ∀ s' g', Post ra t g s' g' → Safely (cenv.instrStepEnv env) Q ((s', ra), g')) :
    Safely (cenv.instrStepEnv env) Q ((t, entry), g) :=
  safely_bindXR (hf ra t g hpre) fun ⟨⟨s', a⟩, g'⟩ ⟨ha, hp⟩ => by
    dsimp only at ha hp
    subst ha
    exact hk s' g' hp

/-- **A block at its label**: the block `blk` of the placed text `p` at `l`,
by a `MachineWP` triple of its body from the exact state `s` that never falls
through (it ends in a jump), its exits `X` continuing at every environment
state above `g` in the fence order. -/
theorem Safely.blockAt [env.FenceMonoX] {p : Program} {l : Label} {blk : Program.Block}
    (hpl : Program.PlacedIn p) (hb : Program.blockAt p l = some blk) {s : MachineData} {g : env.State}
    {X : Int64 → MachineData → Prop} {Q : MachineState × env.State → Prop}
    (h : ⦃ fun s' => s' = s ⦄ blk.body ⦃ fun _ _ => False; X ⦄)
    (hk : ∀ a s' g', X a s' → SharedEnv.FenceMonoX.le g g' → Safely (cenv.instrStepEnv env) Q ((s', a), g')) :
    Safely (cenv.instrStepEnv env) Q ((s, (_root_.Executable.labels cenv).label l), g) := by
  have hI : env.FenceInv (SharedEnv.FenceMonoX.le g) := fun k g' h => SharedEnv.FenceMonoX.fenceInv g k g' h
  have hw : cenv.wp blk.body (fun _ => False) X s := h.le_wp s rfl
  refine Safely.of_eventually_safely
    (Executable.wpEnv_of_wp hI hw g (SharedEnv.FenceMonoX.refl g) _ (hpl.block l blk hb)) ?_
  rintro ⟨⟨s', a⟩, g'⟩ (⟨-, hF, -⟩ | ⟨hx, hle⟩)
  · exact hF.elim
  · exact hk a s' g' hx hle

/-- **A block at its label** (`Safely.blockAt` without `FenceMonoX`): for an
environment whose fences are always permitted (`FenceInv` of `True`), its
exits `X` continuing at every environment state. -/
theorem Safely.blockAtT (hI : env.FenceInv fun _ => True) {p : Program} {l : Label} {blk : Program.Block}
    (hpl : Program.PlacedIn p) (hb : Program.blockAt p l = some blk) {s : MachineData}
    {g : env.State} {X : Int64 → MachineData → Prop} {Q : MachineState × env.State → Prop}
    (h : ⦃ fun s' => s' = s ⦄ blk.body ⦃ fun _ _ => False; X ⦄)
    (hk : ∀ a s' g', X a s' → Safely (cenv.instrStepEnv env) Q ((s', a), g')) :
    Safely (cenv.instrStepEnv env) Q ((s, (_root_.Executable.labels cenv).label l), g) := by
  have hw : cenv.wp blk.body (fun _ => False) X s := h.le_wp s rfl
  refine Safely.of_eventually_safely (Executable.wpEnv_of_wp hI hw g trivial _ (hpl.block l blk hb)) ?_
  rintro ⟨⟨s', a⟩, g'⟩ (⟨-, hF, -⟩ | ⟨hx, -⟩)
  · exact hF.elim
  · exact hk a s' g' hx

end LinkCall

namespace Kraken.Promising.Lower.PilotXR

open Kraken.Promising.X64.EnvG.Treiber2X
open Kraken.Promising.X64.EnvG.TreiberX (sAll)
open Kraken.Promising.Lower.PilotX (Saved)
open Kraken.X64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## `main`'s blocks -/

/-- The body of the block `main`. -/
def mainBodyXR : Program := parse("
    movq %r11, %rbp
    movq %r14, %rsi
    addq $16, %r14
    cmpq %r15, %r14
    ja oom
    movq %rbx, %rdi
    leaq ret_push(%rip), %r11
    jmp push
")

/-- The body of the block `ret_push`. -/
def retPushBodyXR : Program := parse("
    movq %rbx, %rdi
    leaq ret_pop(%rip), %r11
    jmp pop
")

/-- The body of the block `ret_pop`. -/
def retPopBodyXR : Program := parse("
    movq %rax, %r12
    jmp *%rbp
")

theorem blockAt_main : Program.blockAt pilotXR "main" = some ⟨"main", mainBodyXR, some "ret_push"⟩ := by
  decide

theorem blockAt_retPush : Program.blockAt pilotXR "ret_push" = some ⟨"ret_push", retPushBodyXR, some "ret_pop"⟩ := by
  decide

theorem blockAt_retPop : Program.blockAt pilotXR "ret_pop" = some ⟨"ret_pop", retPopBodyXR, some "oom"⟩ := by
  decide

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilotXR)]

local instance pilotXR.env' : CodeEnv := ⟨layout pilotXR⟩

/-- A label's address in the laid-out `pilotXR`. -/
abbrev labXR (x : Label) : Int64 := (_root_.Executable.labels (layout pilotXR)).label x

/-! ## `main` -/

/-- `main`'s precondition at its entry: its link `r11 = raM`, `rbx = &top`,
`r14` the free node (with `r14 + 16 ≤ r15`), `dmem` empty, before the push. -/
def MainPreR (P : Params) (w : Nat) (raM : Int64) (s : MachineData) (σ : (SharedEnv.counted (EWX P w)).State) :
    Prop :=
  s.regs.get64 .r11 = raM.toBitVec ∧ s.regs.get64 .rbx = P.t ∧ s.regs.get64 .r14 = P.n w ∧
    s.regs.get64 .r14 + 16 ≤ s.regs.get64 .r15 ∧ D8 s.dmem ∧ Pu P w σ.1

/-- **`main`'s run** (counted `EWX`, partial): from `MainPreR` at `main`,
every run that stops is at `raM` with the popped node in `r12` (`Dn`). -/
theorem main_specXR (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (raM : Int64) :
    ∀ s g, MainPreR P w raM s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EWX P w)))
        (fun x => x.1.2 = raM ∧ Dn P w (x.1.1.regs.get64 .r12) x.2.1) ((s, labXR "main"), g) := by
  have hpl : Program.PlacedIn pilotXR := pilotXR_placed.toPlacedIn
  rintro s g ⟨h11, hbx, h14, h15, hd8, hPu⟩
  refine Safely.blockAt hpl blockAt_main (X := fun a s₁ => a = labXR "push" ∧
      s₁.regs.get64 .r11 = (labXR "ret_push").toBitVec ∧ s₁.regs.get64 .rdi = P.t ∧
      s₁.regs.get64 .rsi = P.n w ∧ s₁.regs.get64 .rbp = raM.toBitVec ∧ s₁.regs.get64 .rbx = P.t ∧
      s₁.dmem = s.dmem) ?_ ?_
  · simp only [mainBodyXR]
    vcgen
    case vc1 hs hz =>
      exfalso
      subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at hz
      have e16 : BitVec.setWidth 64 (Int64.toBitVec 16) = 16 := by decide
      rw [e16, BitVec.add_comm, ja_not_taken h15] at hz
      exact Bool.false_ne_true hz
    case vc2 hs _ =>
      subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hbx, h14, h11, and_true]
  rintro a s₁ g₁ ⟨rfl, h1r11, h1di, h1si, h1bp, h1bx, h1dm⟩ hle₁
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₁
  refine (push_specXR P w hL hw).jcall (ra := labXR "ret_push")
    ⟨h1r11, h1di, h1si, h1dm ▸ hd8, Pu.fence hPu hle₁.1⟩ fun s₂ g₂ ⟨⟨h2bx, h2bp, _, _, _, _, h2dm⟩, hPo⟩ => ?_
  refine Safely.blockAt hpl blockAt_retPush (X := fun a s₃ => a = labXR "pop" ∧
      s₃.regs.get64 .r11 = (labXR "ret_pop").toBitVec ∧ s₃.regs.get64 .rdi = P.t ∧
      s₃.regs.get64 .rbp = s₂.regs.get64 .rbp ∧ s₃.dmem = s₂.dmem) ?_ ?_
  · simp only [retPushBodyXR]
    vcgen
    case vc1 s' hs =>
      subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h2bx, h1bx, and_true]
  rintro a s₃ g₃ ⟨rfl, h3r11, h3di, h3bp, h3dm⟩ hle₃
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₃
  refine (pop_specXR P w hw).jcall (ra := labXR "ret_pop")
    ⟨h3r11, h3di, by rw [h3dm, h2dm, h1dm]; exact hd8, Po.fence hPo hle₃.1⟩
    fun s₄ g₄ ⟨⟨_, h4bp, _, _, _, _, _⟩, hDn⟩ => ?_
  refine Safely.blockAt hpl blockAt_retPop (X := fun a s₅ => a = Int64.ofBitVec (s₄.regs.get64 .rbp) ∧
      s₅.regs.get64 .r12 = s₄.regs.get64 .rax) ?_ ?_
  · simp only [retPopBodyXR]
    vcgen
    case vc1 s' hs =>
      subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, and_true]
  rintro a s₅ g₅ ⟨rfl, h5⟩ hle₅
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₅
  refine Safely.fold (.inl ⟨ofBitVec_reg (by rw [h4bp, h3bp, h2bp, h1bp]), ?_⟩)
  rw [h5]
  exact hDn.fence hle₅.1

end Kraken.Promising.Lower.PilotXR
