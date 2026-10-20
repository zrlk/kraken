/-
**The relPure twins of `msqXR`'s two threads**
(the kit's `LowerCoreX.pure`: counted `EnvRT sAll`).
With `dmem` empty and every `lock cmpxchgq` a release under `Arch.tso`, a
twin needs only where the links point (`twinT`). Each is one
`cfgEnv_partial_fun` over the thread's part of the text (`fragE`/`fragD`; one
text, two entries), exiting at `done`. Every back edge leaves a block that
made a shared access, so the count went up: no rank.
-/
import Kraken.Promising.Lower.MsqXRMain

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG

namespace Kraken.Promising.Lower.MsqXR

open Kraken.Promising.X64.EnvG.MsQueueX
open Kraken.Promising.X64.EnvG.TreiberX (sAll mem_sAll8 EnvRT)
open Kraken.Promising.X64.EnvG.Treiber2X (ldN stN)
open Kraken.Promising.Lower.PilotXR (D8 ofBitVec_reg)
open Kraken.X64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- **A twin's table**: `dmem` empty and where the links point (`m` the
`main`, `r1`/`r2` its return labels; `rM` the link of `main`, `b1`/`b2` the
addresses of `r1`/`r2`). -/
def twinT (m r1 r2 : Label) (rM b1 b2 : BitVec 64) (lb : Label) (s : MachineData) : Prop :=
  D8 s.dmem ∧
    if lb = m then s.regs.get64 .r11 = rM
    else if lb = r1 ∨ lb = r2 then s.regs.get64 .rbp = rM
    else (s.regs.get64 .r11 = b1 ∨ s.regs.get64 .r11 = b2) ∧ s.regs.get64 .rbp = rM

set_option hygiene false in
/-- Land on a table label (the links `hT`; a back edge's count up), or exit. -/
local macro "twin_land" : tactic => `(tactic| (
  first
    | exact .inr (ofBitVec_reg hT)
    | exact .inr (ofBitVec_reg hT.2)
    | (refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, ?_⟩, ?_⟩)
       · have hT' := hT; simp only [Reg64s.get64] at hT'
         simp (config := { decide := true }) [twinT, hT, hT']
       · first | exact .inl (by decide) | exact .inr fun ⟨_, hg⟩ => by subst hg; cnt_all; omega)))

set_option hygiene false in
/-- **Every VC of a twin**: the accesses admitted (`dmem` empty, RMWs release),
the landings (`twin_land`; a return `jmp *%r11` on each of its two links). -/
local macro "twin_cases" : tactic => `(tactic| (
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals have hx : twinT _ _ _ _ _ _ _ _ ∧ _ = _ ∧ _ = _ := (by with_reducible assumption)
  all_goals obtain ⟨⟨hd8, hT⟩, rfl, rfl⟩ := hx
  all_goals simp only [↓reduceIte, String.reduceEq, or_false, false_or, or_self] at hT
  all_goals first
    | exact hd8 _
    | (refine ⟨⟨?_, mem_sAll8 _⟩, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]; done)
    | (refine ⟨?_, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]; done)
    | (refine ⟨?_, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]
       first | rfl | trivial | exact fun h => absurd rfl h | exact fun h => h rfl)
    | (try dsimp only
       try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
       first
         | twin_land
         | (rcases hT.1 with h | h <;> rw [ofBitVec_reg h] <;> twin_land))
    | skip))

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msqXR)]

local instance msqXR.envP : CodeEnv := ⟨layout msqXR⟩

set_option hygiene false in
/-- A twin's proof: the fragment `f`, the `main` `m` with returns `r1`, `r2`. -/
local macro "twin_run" f:ident m:str r1:str r2:str "[" ids:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
  rintro s g ⟨hd8, h11⟩
  refine cfgEnv_partial_fun (p := $f) (env := SharedEnv.counted (EnvRT sAll)) (E := fun a _ _ => a = labX "done")
    (fun lb s _ => twinT $m $r1 $r2 (labX "done").toBitVec (labX $r1).toBitVec (labX $r2).toBitVec lb s) ?_ rfl
    (by decide) (Program.PlacedIn.of_placedE msqXR_placed (by decide)) s g ⟨hd8, by simpa [twinT] using h11⟩
  cfg_cases_env [$ids,*]
  twin_cases))

/-- **The enqueuer's twin**: from `main_e` with `dmem` empty and the link at
`done`, every run that stops is at `done`. -/
theorem msqXR_pureE :
    ∀ s g, D8 s.dmem ∧ s.regs.get64 .r11 = (labX "done").toBitVec →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EnvRT sAll))) (fun x => x.1.2 = labX "done")
        ((s, labX "main_e"), g) := by
  twin_run fragE "main_e" "ret_e1" "ret_e2" [fragE, mainETxt, enqFrag, mainEBody, retE1Body, retE2Body]

/-- **The dequeuer's twin**, from `main_d`. -/
theorem msqXR_pureD :
    ∀ s g, D8 s.dmem ∧ s.regs.get64 .r11 = (labX "done").toBitVec →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EnvRT sAll))) (fun x => x.1.2 = labX "done")
        ((s, labX "main_d"), g) := by
  twin_run fragD "main_d" "ret_d1" "ret_d2" [fragD, mainDTxt, deqFrag, mainDBody, retD1Body, retD2Body]

end Kraken.Promising.Lower.MsqXR
