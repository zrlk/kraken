/-
**The marshalling block's states placed after the setup call** (AArch64,
option (b)): the `hPlS` premise of the `h0` wrappers with a setup block
(`Spike/Lib/LowerA64/RtMainXR.lean`) from the setup call's post `SPostC`
(`Spike/Lib/LowerA64/PlacedSPostC.lean`). At each state of the marshalling
block from `mainS0`, the continuation of the setup call is placed: the
stores and loads move the words `x0`…`x(sw-1)` through the frame and back
into the same registers, so before each instruction those registers hold
the result registers' words (`marshal_take`); `me`'s word is in the frame's
base cell (the TCB) throughout. The twin of
`Spike/Lib/LowerX64/HPlSOfSPostC.lean`, simpler: x86-64 returns the words in
other registers than it passes them in.

- `argX_eq_argRegs`: the marshalling block's registers are the result
  registers;
- `placeVal_slot`: a frame slot's place value is its cell's;
- `hPlS_ofSPostC`: `Placed` and `PlacedS` at every state of the
  marshalling block, from `SPostC` at the result type `ty` with its words
  as many as the block's (`valWords ty = some sw`), and `me`'s word
  represented by the TCB;
- `hPl_setupArgs`: `PlacedS` at `main`'s entry, at every state agreeing
  with the entry registers on `x0`…`x7`, from `SetupArgs` at `SPostC` (the
  words in `x0`…`x(sw-1)`, `me`'s in `x(sw)`).
-/
import Spike.Lib.LowerA64.PlacedSPostC
import Spike.Lib.Rt.A64MarshalTake

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (WordPlace WordPlaceRep Place placeVal ValRep)
open Scc.Sem.A64 (machine kernel)
open Spike.Lib (Region)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Rt (SetupCode argX mshSt marshal marshal_take mainS0 SetupArgs)
open Spike.Lib.A64.Flow.Ret0 (MainG)
open Spike.Lib.A64Consumer

/-- The marshalling block's registers below the ninth are the result
registers. -/
theorem argX_eq_argRegs : ∀ j (hj : j < Scc.Emit.A64.argRegs.length), argX j = Scc.Emit.A64.argRegs[j] := by
  decide

/-- A target place's value at a frame slot: its cell (`Abs.slot`). -/
theorem placeVal_slot {R : Region} {o : SO} {m : MachineData} {σ : AS} (hA : Abs R o m σ) {k : Int} (hk : R.Off k)
    (s : State) (hs : s.st.1 = m) :
    placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some (σ.slot k).toNat := by
  obtain ⟨j, hj, hjv⟩ := hA.slot k hk
  show (Scc.Sem.A64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, Scc.Sem.A64.privLoad, hs, hj]
  simp [hjv]

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **The marshalling block's states are placed** (`hPlS`): from
`mainS0` at the setup call's post `SPostC` at the result type `ty`, whose
words are as many as the block's (`hw`, `hs`), with the frame's base cell
in the region (`hOff`) and every word of the caller's environment
represented by the TCB `x0` (`hme`), every state of the marshalling block
has the continuation placed, with no suspended frame. -/
theorem hPlS_ofSPostC {Λ : Scc.Sem.Layout} {lbl : Lbl} {p : Prog} {ty : Ty} (lab : Label → Int64)
    {sc : SetupCode} {g : MainG} {x0 : BitVec 64} (hsw : sc.sw ≤ 7) (hs : Scc.Lower.simpleTy ty = true)
    (hw : Scc.Obj.valWords ty = some sc.sw) (hOff : R.Off (-sc.Z.toInt))
    (hme : ∀ y t ws, TermRun.lookupE g.c0.env y = some (t, ws) → ∀ k (hk : k < ws.length),
      ValRep lbl ws[k].val x0.toNat) :
    BlkW (fun s c => Placed Λ lbl s c ∧ Spike.Lib.A64ConsumerS.PlacedS Λ lbl s c []) (fun _ _ => False)
      exe endPc R F (mainS0 lab sc (SPostC p lbl ty g.c0) g x0) (marshal sc.sw sc.fn) := by
  intro s σ c _ _ _ _ _ _ hJ k hk m hAk _
  obtain ⟨hPost, -, -, hx0⟩ := hJ
  obtain ⟨ops, -, hcnt, hP⟩ := hPost.placed
  have hlen : ops.length = sc.sw := hcnt hs _ hw
  obtain ⟨hso, hrg, hsl⟩ := marshal_take (_root_.Executable.labels exe).label hsw sc.fn
    (mainS0 lab sc (SPostC p lbl ty g.c0) g x0).pc (-sc.Z.toInt) σ hk
  have hAk' := hAk
  rw [show (mainS0 lab sc (SPostC p lbl ty g.c0) g x0).o = ⟨-sc.Z.toInt, []⟩ from rfl, hso] at hAk'
  let s' : State := { s with st := (m, (mainS0 lab sc (SPostC p lbl ty g.c0) g x0).pc + Int64.ofNat (4 * k)) }
  have hme' : ∀ y t ws, TermRun.lookupE g.c0.env y = some (t, ws) → ∀ k (hk : k < ws.length),
      ∃ wp, OffImm lbl s' ws[k] wp := by
    unfold OffImm
    intro y t ws hl i hi
    refine ⟨.one (.slot (R.addr (-sc.Z.toInt)).toNat), ⟨fun n h => (by cases h), ?_⟩⟩
    show ∃ v, placeVal (machine (kernel 1)) s' (.slot (R.addr (-sc.Z.toInt)).toNat) = some v ∧
      ValRep lbl ws[i].val v
    exact ⟨x0.toNat, by rw [placeVal_slot hAk' hOff s' rfl, hsl, hx0], hme y t ws hl i hi⟩
  have hρ : ∀ j (_hj : j < ops.length) (hr : j < Scc.Emit.A64.argRegs.length),
      s'.st.1.regs.getXReg (argX j) = σ.regs.getXReg Scc.Emit.A64.argRegs[j] := by
    intro j hj hr
    show m.regs.getXReg _ = _
    rw [hAk'.regs, hrg j (hlen ▸ hj), argX_eq_argRegs j hr]
  have hPl := hP Λ s' argX hρ hme'
  exact ⟨⟨hPl, Spike.Lib.A64ConsumerS.PlacedS.ofNil hPl⟩, fun _ h => h⟩

/-- **The continuation placed at `main`'s entry** (`hpro_main`'s `hPl`):
at registers `regs` with `SetupArgs` at the setup call's post `SPostC` at
the result type `ty` of `sw ≤ 7` words (`hs`, `hw`), every state agreeing
with `regs` on `x0`…`x7` has the continuation placed with no suspended
frame: the words in `x0`…`x(sw-1)` (`SPostC.placed` at `argX`), every word
of the caller's environment represented by the TCB `x0` (`hme`) in
`x(sw)`. -/
theorem hPl_setupArgs {p : Prog} {lbl : Lbl} {ty : Ty} {c0 : Ctl} {sw : Nat} {x0 : BitVec 64}
    (hs : Scc.Lower.simpleTy ty = true) (hw : Scc.Obj.valWords ty = some sw) (hsw : sw ≤ 7)
    (hme : ∀ y t ws, TermRun.lookupE c0.env y = some (t, ws) → ∀ k (hk : k < ws.length),
      ValRep lbl ws[k].val x0.toNat)
    (Λ : Scc.Sem.Layout) :
    ∀ c (regs : Reg64s), SetupArgs (SPostC p lbl ty c0) sw x0 c regs → ∀ s : State,
      (∀ i < 8, s.st.1.regs.getXReg (argX i) = regs.getXReg (argX i)) →
      Spike.Lib.A64ConsumerS.PlacedS Λ lbl s c [] := by
  rintro c regs ⟨rs, hP, hrs, hx⟩ s hag
  obtain ⟨ops, -, hcnt, hPl⟩ := hP.placed
  have hlen : ops.length = sw := hcnt hs _ hw
  have h8 : Scc.Emit.A64.argRegs.length = 8 := rfl
  have hpl := hPl Λ s argX (fun j hj hr => by
      rw [hag j (h8 ▸ hr), hrs j (hlen ▸ hj), argX_eq_argRegs j hr])
    (fun y t ws hl k hk => ⟨.one (.reg (.x (argX sw).idx)), ⟨fun n h => (by cases h),
      ⟨x0.toNat, by
        show some (Scc.Sem.A64.regVal s (.x (argX sw).idx)).toNat = _
        rw [regVal_idx, hag sw (by omega), hx], hme y t ws hl k hk⟩⟩⟩)
  exact Spike.Lib.A64ConsumerS.PlacedS.ofNil hpl

/-- info: 'Spike.Lib.LowerA64.argX_eq_argRegs' depends on axioms: [propext] -/
#guard_msgs in #print axioms argX_eq_argRegs

/-- info: 'Spike.Lib.LowerA64.hPlS_ofSPostC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hPlS_ofSPostC

/-- info: 'Spike.Lib.LowerA64.hPl_setupArgs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hPl_setupArgs

end Spike.Lib.LowerA64
