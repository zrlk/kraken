/-
**The setup call's open premises for any `Accepted2` program with a setup
block** (AArch64): `OpenSG` (`Spike/Lib/LowerA64/G1SetupHS.lean`) at the
generic base context `CxG2` (`Spike/Lib/LowerA64/G1FnSpec.lean`), so the
setup call's `hS` (`HSBVFA`) for any such program.

At each choice of the bounds and the setup block `rodata`:

- the setup function's segment: `FnSpecC2At` at the setup frame's bottom
  keys (the program-wide function segment, a premise `HF`);
- the base context at the setup frame: `CxG2` with the aborts' fragment
  `AbG2` itself, its core by `cxCore2_setup`
  (`Spike/Lib/LowerA64/G1SetupCx.lean`; the allocator's `W2` instance from
  `OpenAHA`, a premise `HA`), the abort node's states the first kind of
  `AbG2`'s, and `AbG2` never ending by `abG2_seg`
  (`Spike/Lib/LowerA64/G1AbG2.lean`; the room `Room2OwnStmt` and the abort
  stubs' write tails premises);
- the construct blocks' targets off the write abort: `hTg_of_tgOkB` at the
  branch-target check `tgOkB`.

- `openSG_of_accepted2`: `OpenSG` from these;
- `hSBVFA_of_accepted2`: `HSBVFA` from them (`hSBVFA_ofOpenSG`);
- `hSBVFA_of_accepted2H`: `HSBVFA` at the landings `ElH` and the write tail
  `fun _ => True`, `OpenAHA` by `openAHA_of_accepted2` (`hobj`).
-/
import Spike.Lib.LowerA64.G1SetupCx
import Spike.Lib.LowerA64.G1AbG2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.LowerNode (compiled2 imms2Me)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

/-- **`OpenSG` for any `Accepted2` program with a setup block** at the
contexts `CxG2` (see the module docstring): the program-wide function
segment at every family and bottom keys (`HF`), the allocator's `W2`
instance (`HA`), the room covering each block's frame and slack
(`hRo`), the branch-target check (`hTgB`), the configuration's need check
(`hcfg`) and the abort stubs' write tails (`hDtO`, `hDtW`, `hDtH`). -/
theorem openSG_of_accepted2 (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hcfg : CfgNeedOkA pcfg = true)
    (hTgB : tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))) = true)
    (hRo : Room2OwnStmt h hp) {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {Dt : State → Prop} (HF : ∀ J Bot, FnSpecC2At h hp Dt J Bot) (HA : OpenAHA h hp E El Dt)
    (hDtO : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F'
      (A64.Abort.N (Ly).lab A64.Abort.overflow c .svc) s c' → Dt s)
    (hDtW : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F'
      (A64.Abort.N (Ly).lab A64.Abort.write c .svc) s c' → Dt s)
    (hDtH : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F'
      (A64.Abort.N (Ly).lab A64.Abort.heap c .svc) s c' → Dt s) :
    OpenSG h hp E El Dt := by
  intro L D1 D2 lS lM fS nS fM nM hB J hJ v j d hd hn
  refine ⟨CxG2 h hp Dt J, { hs := HF J _ j d hd, hcx := ?_, hTg := ?_ }⟩
  · intro F' g fr hP hSB
    have hC := cxCore2_setup h hp hty hcfg hB J v hd hn (HA L D1 D2 lS lM fS nS fM nM hB J hJ v j d hd hn) hP hSB
    exact ⟨AbG2 h hp Dt J, ⟨⟨hC, fun _ _ _ h' => h'⟩, List.cons_ne_nil _ _⟩,
      fun _ _ _ hA => ⟨j, d, hd, _, F', [fr], g.fp, g.ra, _, _, hC, .inl hA⟩,
      abG2_seg h hp hRo J hDtO hDtW hDtH⟩
  · exact hTg_of_tgOkB hTgB (fnCode2OfPMe hp h Λ j d hd).hf (fnCode2OfPMe hp h Λ j d hd).h1
      (fnCode2OfPMe hp h Λ j d hd).h16 (fun _ _ h' => h') (Ly).lab

/-- **The setup call's `hS` for any `Accepted2` program with a setup
block** (`hSBVFA_ofOpenSG` at `openSG_of_accepted2`). -/
theorem hSBVFA_of_accepted2 (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hcfg : CfgNeedOkA pcfg = true)
    (hTgB : tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))) = true)
    (hRo : Room2OwnStmt h hp) {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {Dt : State → Prop} (HF : ∀ J Bot, FnSpecC2At h hp Dt J Bot) (HA : OpenAHA h hp E El Dt)
    (hDtO : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F'
      (A64.Abort.N (Ly).lab A64.Abort.overflow c .svc) s c' → Dt s)
    (hDtW : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F'
      (A64.Abort.N (Ly).lab A64.Abort.write c .svc) s c' → Dt s)
    (hDtH : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F'
      (A64.Abort.N (Ly).lab A64.Abort.heap c .svc) s c' → Dt s) :
    HSBVFA h ty E El Dt :=
  hSBVFA_ofOpenSG h hp hty (openSG_of_accepted2 h hp hty hcfg hTgB hRo HF HA hDtO hDtW hDtH)

/-- **`HSBVFA` at the landings `ElH` and the write tail `fun _ => True`**
for any `Accepted2` program with a setup block whose object layout starts
the header's scalar count below bit 22 (`hobj`): `OpenAHA` by
`openAHA_of_accepted2`, the write tails trivial. -/
theorem hSBVFA_of_accepted2H (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hobj : Scc.Obj.nShift cfg.layout.obj < 22) (hcfg : CfgNeedOkA pcfg = true)
    (hTgB : tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))) = true)
    (hRo : Room2OwnStmt h hp) (E : Entry) (HF : ∀ J Bot, FnSpecC2At h hp (fun _ => True) J Bot) :
    HSBVFA h ty E (ElH h hp) (fun _ => True) :=
  hSBVFA_of_accepted2 h hp hty hcfg hTgB hRo HF (openAHA_of_accepted2 h hp hty hobj E)
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)

end Assembled

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.openSG_of_accepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.openSG_of_accepted2

/-- info: 'Spike.Lib.LowerA64.hSBVFA_of_accepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hSBVFA_of_accepted2

/-- info: 'Spike.Lib.LowerA64.hSBVFA_of_accepted2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hSBVFA_of_accepted2H
