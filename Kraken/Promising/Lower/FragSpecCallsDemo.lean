/-
**Demo: a non-leaf call, a tail call and an
indirect call to `push`, from the one-spec-per-fragment layer's one `push`
spec.** ISA: AArch64; machine: the executable machine's per-thread
environment semantics (`Executable.instrStepEnv`), partial correctness,
as `FragSpecEnvL` (`Lower/FragSpecCalls.lean`).

`push`'s `FragSpecEnv` is `Uni.pushFrag_specU` (`Lower/FragSpecUni.lean`),
used as is (never re-proved). Three callers, each a fragment of its own:

- `pushw` (**non-leaf**, frameless): `mov x19, x30; bl push; mov x30, x19;
  ret`. The ABI frame composes as *callee-saved minus the register holding
  the return address*: `push` keeps `Saved2` (`x19`–`x28`, `dmem`, `sp`), so
  `x19` survives the call; `pushw` clobbers `x19` itself, so its post is
  `SavedX19` (`Saved2` without `x19`).
- `pusht` (**tail call**): `mov x1, x9; b push`. `push` returns straight to
  `pusht`'s caller; the post is `push`'s (`Saved2`).
- `pushi` (**indirect call**): `mov x19, x30; adr x16, push; blr x16;
  mov x30, x19; ret`, as `pushw`.

Each is placed by `[callerFrag, pushFrag]` and transported to the laid-out
program `callsDemo` by `FragSpecEnvL.toFrag` + `FragSpecEnv.of_layout` (one
line each).
-/
import Kraken.Promising.Lower.FragSpecCalls
import Kraken.Promising.Lower.FragSpecUni

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.Calls

open Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.Promising.Lower.Uni
open Kraken.Promising.Lower.Pilot (CalleeSaved pushFrag)
open Kraken.Promising.Lower.Pilot2 (Saved2)
open Kraken.AArch64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The frame -/

/-- **`Saved2` without `x19`**: the frame of a frameless non-leaf function
that keeps its return address in `x19`. -/
def SavedX19 (t s : MachineData) : Prop :=
  s.regs.X20 = t.regs.X20 ∧ s.regs.X21 = t.regs.X21 ∧ s.regs.X22 = t.regs.X22 ∧
    s.regs.X23 = t.regs.X23 ∧ s.regs.X24 = t.regs.X24 ∧ s.regs.X25 = t.regs.X25 ∧
    s.regs.X26 = t.regs.X26 ∧ s.regs.X27 = t.regs.X27 ∧ s.regs.X28 = t.regs.X28 ∧
    s.dmem = t.dmem ∧ s.regs.SP = t.regs.SP

theorem Saved2.savedX19 {t s : MachineData} (h : Saved2 t s) : SavedX19 t s := by
  obtain ⟨⟨-, h20, h21, h22, h23, h24, h25, h26, h27, h28, hd⟩, hsp⟩ := h
  exact ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28, hd, hsp⟩

theorem SavedX19.trans {t s u : MachineData} (h1 : SavedX19 t s) (h2 : SavedX19 s u) : SavedX19 t u := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := h2
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7,
    b8.trans a8, b9.trans a9, b10.trans a10, b11.trans a11⟩

/-! ## The protocol facts under the environment's fence steps

`vcgen` over `EnvGCAdj` lifts every cell over a `FenceMono.le` step of the
environment state; the protocol facts are monotone under it. -/

theorem pu_le {P : Params} {w : Nat} {G : Loc → Val → Prop} {σ σ' : (SharedEnv.counted (EWG P w G)).State}
    (h : SharedEnv.FenceMono.le σ σ') (hp : Pu P w σ.1) : Pu P w σ'.1 := by
  simp only [fenceMono_le_counted, Pilot2.fenceMono_le_valsEnv, fenceMono_le_envGCAdj] at h
  exact hp.fence h.1

theorem po_le {P : Params} {w : Nat} {G : Loc → Val → Prop} {σ σ' : (SharedEnv.counted (EWG P w G)).State}
    (h : SharedEnv.FenceMono.le σ σ') (hp : Po P w σ.1) : Po P w σ'.1 := by
  simp only [fenceMono_le_counted, Pilot2.fenceMono_le_valsEnv, fenceMono_le_envGCAdj] at h
  exact hp.fence h.1

/-! ## `pushw`: a non-leaf call -/

/-- The prefix: save the return address in `x19`. -/
def pushwA : Program := parseAArch64("
    mov x19, x30
")

/-- The suffix: restore it, return. -/
def pushwB : Program := parseAArch64("
    mov x30, x19
    ret
")

/-- `pushw`'s text: `push` through `bl`, frameless. -/
def pushwFrag : Program := parseAArch64("
pushw:
    mov x19, x30
    bl push
    mov x30, x19
    ret
")

theorem pushw_block : Program.blockAt pushwFrag "pushw" =
    some ⟨"pushw", pushwA ++ Directive.instr ⟨.W64, .BL (.label "push")⟩ :: pushwB, none⟩ := by decide

/-- A frameless wrapper's post: `SavedX19`, the frame `F`, pushed. -/
def PushwPost (P : Params) (w : Nat) (G : Loc → Val → Prop) (F : Mem 64 → Prop) (_ : Int64) (t : MachineData)
    (_ : (SharedEnv.counted (EWG P w G)).State) (t' : MachineData) (σ' : (SharedEnv.counted (EWG P w G)).State) :
    Prop :=
  SavedX19 t t' ∧ F t'.dmem ∧ Po P w σ'.1

/-- At `bl push`: `push`'s arguments, the return address in `x19`, the frame. -/
def PushwMid1 (P : Params) (w : Nat) (G : Loc → Val → Prop) (ra : Int64) (t : MachineData)
    (_ : (SharedEnv.counted (EWG P w G)).State) (s : MachineData) (σ : (SharedEnv.counted (EWG P w G)).State) :
    Prop :=
  Int64.ofBitVec s.regs.X19.toBitVec = ra ∧ s.regs.X0.toBitVec = P.t ∧ s.regs.X1.toBitVec = P.n w ∧
    SavedX19 t s ∧ Pu P w σ.1

/-- Behind `bl push`: the return address still in `x19`, the frame, pushed. -/
def PushwMid2 (P : Params) (w : Nat) (G : Loc → Val → Prop) (ra : Int64) (t : MachineData)
    (_ : (SharedEnv.counted (EWG P w G)).State) (s : MachineData) (σ : (SharedEnv.counted (EWG P w G)).State) :
    Prop :=
  Int64.ofBitVec s.regs.X19.toBitVec = ra ∧ SavedX19 t s ∧ Po P w σ.1

/-- **`pushw`'s spec**, from `push`'s, by `FragSpecEnvL.call`. -/
theorem pushw_spec (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (G : Loc → Val → Prop)
    (F : Mem 64 → Prop) (hF : TFrameOK P w G F) :
    FragSpecEnvL (SharedEnv.counted (EWG P w G)) [pushwFrag, pushFrag] "pushw" (PushPreU P w G F)
      (PushwPost P w G F) := by
  refine FragSpecEnvL.call (PushwMid1 P w G) (PushwMid2 P w G) (pushFrag_specU P w hL hw G F hF).toL
    pushw_block rfl ?_ ?_ ?_
  · intro _ ra t g
    unfold pushwA
    vcgen
    obtain ⟨⟨hlr, hx0, hx1, -, hPu⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
    simp only [MachineData.lr] at hlr
    simp_all [PushwMid1, SavedX19]
    first | exact pu_le ‹_› hPu | exact pu_le ‹_› (pu_le ‹_› hPu)
  · rintro ra t g s σ ⟨-, -, -, hF0, -⟩ ⟨h19, hx0, hx1, hfr, hPu⟩ ra'
    refine ⟨⟨by simp [MachineData.lr, MachineData.setLr], by simpa [MachineData.setLr] using hx0,
      by simpa [MachineData.setLr] using hx1, by simpa [MachineData.setLr, hfr.2.2.2.2.2.2.2.2.2.1] using hF0,
      hPu⟩, ?_⟩
    rintro s' σ' ⟨hs, -, hPo⟩
    refine ⟨?_, hfr.trans ?_, hPo⟩
    · rw [hs.1.1]; simpa [MachineData.setLr] using h19
    · simpa [SavedX19, MachineData.setLr, Reg64s.setXReg] using Saved2.savedX19 hs
  · intro _ ra t g s₀ g₀
    unfold pushwB
    vcgen
    obtain ⟨⟨-, -, -, hF0, -⟩, ⟨h19, hfr, hPo⟩, rfl, rfl⟩ := ‹_ ∧ _ ∧ _ = _ ∧ _ = _›
    simp_all [PushwPost, SavedX19]
    first | exact po_le ‹_› hPo | exact po_le ‹_› (po_le ‹_› hPo)

/-! ## `pusht`: a tail call -/

/-- `pusht`'s body. -/
def pushtBody : Program := parseAArch64("
    mov x1, x9
    b push
")

/-- `pusht`'s text: the node in `x9`, then a tail call to `push`. -/
def pushtFrag : Program := parseAArch64("
pusht:
    mov x1, x9
    b push
")

/-- `pusht`'s precondition: `push`'s, with the node in `x9`. -/
def PushtPre (P : Params) (w : Nat) (G : Loc → Val → Prop) (F : Mem 64 → Prop) (ra : Int64) (t : MachineData)
    (σ : (SharedEnv.counted (EWG P w G)).State) : Prop :=
  t.lr = ra ∧ t.regs.X0.toBitVec = P.t ∧ t.regs.X9.toBitVec = P.n w ∧ F t.dmem ∧ Pu P w σ.1

/-- **`pusht`'s spec**, from `push`'s, by `FragSpecEnvL.tail`: `push`'s post. -/
theorem pusht_spec (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (G : Loc → Val → Prop)
    (F : Mem 64 → Prop) (hF : TFrameOK P w G F) :
    FragSpecEnvL (SharedEnv.counted (EWG P w G)) [pushtFrag, pushFrag] "pusht" (PushtPre P w G F)
      (PushPostU P w G F) := by
  refine FragSpecEnvL.tail (pushFrag_specU P w hL hw G F hF).toL (blk := ⟨"pusht", pushtBody, none⟩) (by decide) ?_
  intro _ ra t g
  unfold pushtBody
  dsimp only
  vcgen
  obtain ⟨⟨hlr, hx0, hx9, hF0, hPu⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  refine .inl ⟨rfl, ⟨by simpa [MachineData.lr] using hlr, by simpa using hx0, by simpa using hx9,
    by simpa using hF0, pu_le ‹_› (pu_le ‹_› hPu)⟩, ?_⟩
  rintro s' σ' ⟨hs, hF', hPo⟩
  exact ⟨by simpa [Saved2, CalleeSaved] using hs, hF', hPo⟩

/-! ## `pushi`: an indirect call -/

/-- The prefix: save the return address, `push`'s address into `x16`. -/
def pushiA : Program := parseAArch64("
    mov x19, x30
    adr x16, push
")

/-- `pushi`'s text: `push` through `blr x16`, frameless. -/
def pushiFrag : Program := parseAArch64("
pushi:
    mov x19, x30
    adr x16, push
    blr x16
    mov x30, x19
    ret
")

theorem pushi_block : Program.blockAt pushiFrag "pushi" =
    some ⟨"pushi", pushiA ++ Directive.instr ⟨.W64, .BLR (.X16)⟩ :: pushwB, none⟩ := by decide

/-- **`pushi`'s spec**, from `push`'s, by `FragSpecEnvL.callr`. -/
theorem pushi_spec (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (G : Loc → Val → Prop)
    (F : Mem 64 → Prop) (hF : TFrameOK P w G F) :
    FragSpecEnvL (SharedEnv.counted (EWG P w G)) [pushiFrag, pushFrag] "pushi" (PushPreU P w G F)
      (PushwPost P w G F) := by
  refine FragSpecEnvL.callr (PushwMid1 P w G) (PushwMid2 P w G) (pushFrag_specU P w hL hw G F hF).toL
    pushi_block rfl ?_ ?_ ?_
  · intro _ ra t g
    unfold pushiA
    vcgen
    obtain ⟨⟨hlr, hx0, hx1, -, hPu⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
    simp only [MachineData.lr] at hlr
    simp_all [PushwMid1, SavedX19]
    first | exact pu_le ‹_› hPu | exact pu_le ‹_› (pu_le ‹_› hPu)
  · rintro ra t g s σ ⟨-, -, -, hF0, -⟩ ⟨h19, hx0, hx1, hfr, hPu⟩ ra'
    refine ⟨⟨by simp [MachineData.lr, MachineData.setLr], by simpa [MachineData.setLr] using hx0,
      by simpa [MachineData.setLr] using hx1, by simpa [MachineData.setLr, hfr.2.2.2.2.2.2.2.2.2.1] using hF0,
      hPu⟩, ?_⟩
    rintro s' σ' ⟨hs, -, hPo⟩
    refine ⟨?_, hfr.trans ?_, hPo⟩
    · rw [hs.1.1]; simpa [MachineData.setLr] using h19
    · simpa [SavedX19, MachineData.setLr, Reg64s.setXReg] using Saved2.savedX19 hs
  · intro _ ra t g s₀ g₀
    unfold pushwB
    vcgen
    obtain ⟨⟨-, -, -, hF0, -⟩, ⟨h19, hfr, hPo⟩, rfl, rfl⟩ := ‹_ ∧ _ ∧ _ = _ ∧ _ = _›
    simp_all [PushwPost, SavedX19]
    first | exact po_le ‹_› hPo | exact po_le ‹_› (po_le ‹_› hPo)


/-! ## `pushww`: a non-leaf call to a non-leaf function

Composition is transitive: `pushw`'s `FragSpecEnvL` (itself from `push`'s)
is the callee's spec; the result is placed by all three fragments. `pushww`
keeps its return address in `x20`, which `pushw` keeps (`SavedX19`). -/

/-- `SavedX19` without `x20`. -/
def SavedX1920 (t s : MachineData) : Prop :=
  s.regs.X21 = t.regs.X21 ∧ s.regs.X22 = t.regs.X22 ∧ s.regs.X23 = t.regs.X23 ∧ s.regs.X24 = t.regs.X24 ∧
    s.regs.X25 = t.regs.X25 ∧ s.regs.X26 = t.regs.X26 ∧ s.regs.X27 = t.regs.X27 ∧ s.regs.X28 = t.regs.X28 ∧
    s.dmem = t.dmem ∧ s.regs.SP = t.regs.SP

def pushwwA : Program := parseAArch64("
    mov x20, x30
")

def pushwwB : Program := parseAArch64("
    mov x30, x20
    ret
")

def pushwwFrag : Program := parseAArch64("
pushww:
    mov x20, x30
    bl pushw
    mov x30, x20
    ret
")

theorem pushww_block : Program.blockAt pushwwFrag "pushww" =
    some ⟨"pushww", pushwwA ++ Directive.instr ⟨.W64, .BL (.label "pushw")⟩ :: pushwwB, none⟩ := by decide

/-- At `bl pushw`: the return address in `x20`. -/
def PushwwMid1 (P : Params) (w : Nat) (G : Loc → Val → Prop) (ra : Int64) (t : MachineData)
    (_ : (SharedEnv.counted (EWG P w G)).State) (s : MachineData) (σ : (SharedEnv.counted (EWG P w G)).State) :
    Prop :=
  Int64.ofBitVec s.regs.X20.toBitVec = ra ∧ s.regs.X0.toBitVec = P.t ∧ s.regs.X1.toBitVec = P.n w ∧
    SavedX1920 t s ∧ Pu P w σ.1

/-- Behind `bl pushw`. -/
def PushwwMid2 (P : Params) (w : Nat) (G : Loc → Val → Prop) (ra : Int64) (t : MachineData)
    (_ : (SharedEnv.counted (EWG P w G)).State) (s : MachineData) (σ : (SharedEnv.counted (EWG P w G)).State) :
    Prop :=
  Int64.ofBitVec s.regs.X20.toBitVec = ra ∧ SavedX1920 t s ∧ Po P w σ.1

/-- **`pushww`'s spec**, from `pushw`'s, by `FragSpecEnvL.call`. -/
theorem pushww_spec (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (G : Loc → Val → Prop)
    (F : Mem 64 → Prop) (hF : TFrameOK P w G F) :
    FragSpecEnvL (SharedEnv.counted (EWG P w G)) [pushwwFrag, pushwFrag, pushFrag] "pushww" (PushPreU P w G F)
      (fun _ t _ t' σ' => SavedX1920 t t' ∧ F t'.dmem ∧ Po P w σ'.1) := by
  refine FragSpecEnvL.call (PushwwMid1 P w G) (PushwwMid2 P w G) (pushw_spec P w hL hw G F hF) pushww_block rfl ?_ ?_ ?_
  · intro _ ra t g
    unfold pushwwA
    vcgen
    obtain ⟨⟨hlr, hx0, hx1, -, hPu⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
    simp only [MachineData.lr] at hlr
    simp_all [PushwwMid1, SavedX1920]
    first | exact pu_le ‹_› hPu | exact pu_le ‹_› (pu_le ‹_› hPu)
  · rintro ra t g s σ ⟨-, -, -, hF0, -⟩ ⟨h20, hx0, hx1, hfr, hPu⟩ ra'
    refine ⟨⟨by simp [MachineData.lr, MachineData.setLr], by simpa [MachineData.setLr] using hx0,
      by simpa [MachineData.setLr] using hx1, by simpa [MachineData.setLr, hfr.2.2.2.2.2.2.2.2.1] using hF0,
      hPu⟩, ?_⟩
    rintro s' σ' ⟨hs, -, hPo⟩
    obtain ⟨b20, b21, b22, b23, b24, b25, b26, b27, b28, bd, bsp⟩ := hs
    obtain ⟨a21, a22, a23, a24, a25, a26, a27, a28, ad, asp⟩ := hfr
    simp only [MachineData.setLr, Reg64s.setXReg] at b20 b21 b22 b23 b24 b25 b26 b27 b28 bd bsp
    exact ⟨by rw [b20]; exact h20, ⟨b21.trans a21, b22.trans a22, b23.trans a23, b24.trans a24,
      b25.trans a25, b26.trans a26, b27.trans a27, b28.trans a28, bd.trans ad, bsp.trans asp⟩, hPo⟩
  · intro _ ra t g s₀ g₀
    unfold pushwwB
    vcgen
    obtain ⟨⟨-, -, -, hF0, -⟩, ⟨h20, hfr, hPo⟩, rfl, rfl⟩ := ‹_ ∧ _ ∧ _ = _ ∧ _ = _›
    simp_all [SavedX1920]
    first | exact po_le ‹_› hPo | exact po_le ‹_› (po_le ‹_› hPo)

/-! ## Instantiation at a program -/

/-- The three callers and `push`, laid out in one text (any order: each
spec is placed by its own fragments). -/
def callsDemo : Program := pushwFrag ++ pushtFrag ++ pushiFrag ++ pushFrag ++ pushwwFrag

section Prog

variable [layout : _root_.Layout] [Executable.ValidLayout (layout callsDemo)]

local instance callsDemo.env : CodeEnv := ⟨layout callsDemo⟩

omit layout [Executable.ValidLayout (layout callsDemo)] in
theorem callsDemo_wf : Program.WF callsDemo := by decide

/-- Where `callsDemo`'s blocks sit. -/
theorem callsDemo_placed : Program.Placed callsDemo "pushw" :=
  Program.placed_of_layout callsDemo_wf rfl (by decide)

theorem pushw_spec_at (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (G : Loc → Val → Prop)
    (F : Mem 64 → Prop) (hF : TFrameOK P w G F) :
    FunSpecPartialEnv (SharedEnv.counted (EWG P w G)) ((_root_.Executable.labels cenv).label "pushw")
      (PushPreU P w G F) (PushwPost P w G F) :=
  (pushw_spec P w hL hw G F hF).of_placed callsDemo_placed (by decide)

theorem pusht_spec_at (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (G : Loc → Val → Prop)
    (F : Mem 64 → Prop) (hF : TFrameOK P w G F) :
    FunSpecPartialEnv (SharedEnv.counted (EWG P w G)) ((_root_.Executable.labels cenv).label "pusht")
      (PushtPre P w G F) (PushPostU P w G F) :=
  (pusht_spec P w hL hw G F hF).of_placed callsDemo_placed (by decide)

theorem pushi_spec_at (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (G : Loc → Val → Prop)
    (F : Mem 64 → Prop) (hF : TFrameOK P w G F) :
    FunSpecPartialEnv (SharedEnv.counted (EWG P w G)) ((_root_.Executable.labels cenv).label "pushi")
      (PushPreU P w G F) (PushwPost P w G F) :=
  (pushi_spec P w hL hw G F hF).of_placed callsDemo_placed (by decide)

theorem pushww_spec_at (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (G : Loc → Val → Prop)
    (F : Mem 64 → Prop) (hF : TFrameOK P w G F) :
    FunSpecPartialEnv (SharedEnv.counted (EWG P w G)) ((_root_.Executable.labels cenv).label "pushww")
      (PushPreU P w G F) (fun _ t _ t' σ' => SavedX1920 t t' ∧ F t'.dmem ∧ Po P w σ'.1) :=
  (pushww_spec P w hL hw G F hF).of_placed callsDemo_placed (by decide)

end Prog

end Kraken.Promising.Lower.Calls
